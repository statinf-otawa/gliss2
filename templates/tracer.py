#!/usr/bin/python3
import shutil
import subprocess
import sys
import time

VERBOSE = False
program = "sum.elf"
qemu = "qemu-arm"
gdb = "arm-none-eabi-gdb"
port = 1234
target_location = "localhost:%d" % port
REGISTERS = [b"r%d" % i for i in range(0, 13)] + [b"sp", b"lr", b"pc", b"cpsr"]

IS_ERROR = 1
IS_WARNING = 2
IS_HANDLED_ELSEWHERE = 3

def verbose(f):
	if VERBOSE:
		f()

def fatal(msg):
	sys.stderr.write("ERROR: %s\n" % msg)
	exit(1)

def warn(msg):
	sys.stderr.write("WARNING: %s\n" % msg)

class QEmuDriver:
	
	def __init__(self, qemu, program, port):
		self.qemu = qemu
		self.program = program
		self.port = port

	def start(self):
		path = shutil.which(self.qemu)
		#cmd = "%s -singlestep -g %d %s" % (path, self.port, self.program)
		cmd = [path, "-singlestep", "-g", str(self.port), self.program]
		verbose(lambda: print("QEMU: ", " ".join(cmd)))
		self.proc = subprocess.Popen(cmd)
		#time.sleep(1)

	def stop(self):
		self.proc.kill()


class GDBFormatError(BaseException):
	
	def __init__(self, txt, i):
		BaseException.__init__(self, "%d: %s" % (i, txt))


def decode(txt, i):
	try:
		if i >= len(txt):
			return (i, None)
		
		elif txt[i:i+1] == b"[":
			l = []
			i += 1
			if txt[i:i+1] == b']':
				return (i+1, l)
			while True:
				(i, v) = decode(txt, i)
				l.append(v)
				if txt[i:i+1] == b"]":
					return (i+1, l)
				elif txt[i:i+1] != b",":
					raise GDBFormatError(txt, i)
				i += 1
		
		elif txt[i:i+1] == b"{":
			m = { }
			i += 1
			if txt[i:i+1] == b"}":
				return (i+1, m)
			while True:
				p = txt.index(b"=", i)
				k = txt[i:p]
				(i, v) = decode(txt, p+1)
				m[k] = v
				if txt[i:i+1] == b"}":
					return (i+1, m)
				elif txt[i:i+1] != b",":
					raise GDBFormatError(txt, i)
				i += 1		
				
		elif txt[i:i+1] == b'"':
			p = txt.index(b'"', i+1)
			return (p+1, txt[i+1:p].replace(b"\\t", b" "))
		
		else:
			raise GDBFormatError(txt, i)
	except ValueError:
		raise GDBFormatError(txt, i)

def decode_gdb(txt):
	_, v = decode(txt, 0)
	return v


class GDBDriver:

	def __init__(self, gdb, program, remote, regs):
		self.gdb = gdb
		self.program = program
		self.remote = remote
		self.regs = regs
	
	def start(self):
		
		# starting the command
		cmd = "%s --interpreter mi --quiet %s" % (gdb, program)
		verbose(lambda: print("GDB: %s" % cmd))
		self.proc = subprocess.Popen(
			cmd,
			stdin = subprocess.PIPE,
			stdout = subprocess.PIPE,
			#stderr = subprocess.PIPE,
			shell = True)

		# dumping initial messages
		r = self.proc.stdout.readline()
		while r[0:5] != b"(gdb)":
			verbose(lambda: print("GDB: initial: ", r))
			r = self.proc.stdout.readline()

		# connect to remote
		r = self.command(b"-target-select remote tcp:%s\n" % bytes(self.remote, "utf-8"))
		self.match_output(r, b"^connected", IS_ERROR, "when connecting to target.")

		# find start
		self.pc = self.read_pc()
		self._start = self.pc
		verbose(lambda: print("GDB: PC = 0x%x" % self._start))

		# find exit
		self._exit = self.get_label(b"_exit")
		verbose(lambda: print("GDB: _exit = 0x%x" % self._exit))

		# find register numbers
		self.get_registers()

	def stop(self):
		pass

	def step(self):
		r = self.command(b"-exec-step-instruction\n")
		self.match_output(r, b"^running", IS_ERROR, "cannot step instruction")
		r = self.wait_answer()
		self.match_output(r, b"*stopped,reason=\"end-stepping-range\"", IS_ERROR, "step not ended?")
		self.pc = self.read_pc()

	def get_inst(self):
		r = self.command(b"-data-disassemble -s 0x%08X -e 0x%08X -- 0\n" %(self.pc, self.pc + 4))
		r = self.match_output(r, b"^done,asm_insns=", IS_ERROR, "error in getting disassembly")
		return decode_gdb(r[16:-1])[0][b"inst"]

	def get_values(self):
		r = self.command(b"-data-list-register-values r %s\n" % self.nums)
		r = self.match_output(r, b"^done,register-values=[", IS_WARNING, "bad formatted values")
		if r == None:
			return []
		r = r[23:-2].split(b",")
		vs = []
		for v in r:
			if v.startswith(b"value=\""):
				vs.append(int(v[9:-2], 16))
		verbose(lambda: print("GDB: values=", vs))
		return vs

	def get_registers(self):
		r = self.command(b"-data-list-register-names\n")
		r = self.match_output(r, b"^done,register-names=[", IS_ERROR, "cannot get register names")
		names = [x[1:-1] for x in r[22:-1].split(b",")]
		indexes = []
		for r in self.regs:
			i = names.index(r)
			assert i >= 0
			indexes.append(i)
		self.nums = b" ".join([bytes(str(i), "utf-8") for i in indexes])

	def get_label(self, label):
		r = self.command(b"-data-evaluate-expression %s\n" % label)
		r = self.match_output(r, b"^done,value=", IS_ERROR, "no exit symbol!")
		return self.read_addr(r)		

	def get_pc(self):
		return self.pc
		
	def read_pc(self):
		r = self.command(b"-data-evaluate-expression $pc\n")
		r = self.match_output(r, b"^done,value=", IS_WARNING, "cannot get PC?")
		if r == None:
			return None
		else:
			return self.read_addr(r)

	def read_addr(self, l):
		v = l[13:-2]
		if v[0:1] == b"{":
			p = v.index(b"}")
			v = v[p+2:]
		p = v.index(b" ", 1)
		if p >= 0:
			v = v[2:p]
		return int(v, 16)

	def command(self, cmd):
		verbose(lambda : print("GDB: command=%s" % cmd))
		self.proc.stdin.write(cmd)
		self.proc.stdin.flush()
		return self.wait_answer()

	def wait_answer(self):
		rs = []
		while True:
			verbose(lambda: print("GDB: waiting GDB"))
			r = self.proc.stdout.readline()
			verbose(lambda: print("GDB: got %s" % r))
			if r[0:5] == b"(gdb)":
				return rs
			else:
				rs.append(r)

	def match_output(self, rep, pat, lvl, label):
		for r in rep:
			if r == b"^error":
				break
			elif pat in r:
				return r
		if lvl == IS_ERROR:
			fatal(label)
		elif lvl == IS_WARNING:
			warn(label)
		return None



qdriver = QEmuDriver(qemu, program, port)
qdriver.start()

driver = GDBDriver(gdb, program, target_location, REGISTERS)	
driver.start()

#print(driver.get_registers())
#r = driver.command("-data-list-register-names")
#print(r)

print(driver.get_values())
while driver.get_pc() != driver._exit:
	driver.step()
	print(driver.get_pc(), " ", driver.get_values())

driver.stop()
qdriver.stop()


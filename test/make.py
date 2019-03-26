#!/usr/bin/python
# maat can downloaded from https://github.com/hcasse/maat
from maat import *
from maat import test
from maat import ocaml

# configuration
IRG = "../irg/"
PRINT_IRG = IRG + "print_irg"
GEP = "../gep/gep"
MKIRG = "../irg/mkirg"
GLISS_ATTR = "../gep/gliss-attr"

out = directory("out")

# useful function
def print_irg(nml, opts = ""):
	return "%s %s %s" % (PRINT_IRG, nml, opts)

def output(case, name, cmd):
	test.output(case, name, cmd, out="out/%s.out" % name, out_ref="ref/%s.out" % name)


# simple test case
simple = test.case("simple", deps = out)

for t in ["alone.nmp", "for.nml", "irregular.nmp", "qvm.nml"]:
	test.command(simple, t + "-test",	"../"+GEP+" ../"+t, dir = "out")


# failing test case
failing = test.case("failing")

for t in ["image_param", "double_param", "bad_named_param"]:
	test.failing_command(failing, t, "%s %s.nml out/%s.irg" % (MKIRG, t, t), deps = "out")


# attribute test case
attr = test.case("attr", deps = "out")
for (t, f) in [("cst", ""), ("fun", "-f")]:
		test.command(attr, t, GLISS_ATTR+" qvm.nml -e attr/kind_%s.nml -o out/%s.c -a kind -d 0 -t attr/kind_%s.c %s" % (t, t, t, f))

# complete test case
complete = test.case("complete")

test.command(complete, "alias-test", "cd alias-test; make clean all")


# decode test case
ocaml.program("out/decode", "decode/decode.ml",
	OCAMLCFLAGS = "-I ../irg/ -I ../gep",
	LIBS = ["str", "../irg/irg", "../gep/libgep"])
decode = test.case("decode")
test.command(decode, "decode-test", "./out/decode")


# definition argument tests
defarg = test.case("defarg-test")
tests = [
	("arg-bad-type",	"-D N=3"),
	("arg-bad-arg",		"-D N=x")
]
for (t, a) in tests:
	test.failing_command(defarg, "%s-test" % t,  "%s %s.nml %s" % (PRINT_IRG, t, a), err = "out/%s.err" % t)
tests = [
	("arg-none", ""),
	("arg-int", "-D N=1"),
	("arg-str", "-D N=YYY")
]
for (t, a) in tests:
	test.output(defarg, "%s-test" % t, "%s %s.nml %s" % (PRINT_IRG, t, a),
		out = "out/%s.out", out_ref = "ref/%s.out" % t)


# top-if test
top_if = test.case("topif-test")
output(top_if, "if-simple", print_irg("if-simple.nml", ""))
output(top_if, "if-simple2", print_irg("if-simple.nml", "-D N=1"))
test.failing_command(top_if, "if-dyn", print_irg("if-dyn.nml"))
output(top_if, "if-multi00", print_irg("if-multi.nml", "-D N=0 -D K=0"))
output(top_if, "if-multi01", print_irg("if-multi.nml", "-D N=0 -D K=1"))
output(top_if, "if-multi10", print_irg("if-multi.nml", "-D N=1 -D K=0"))
output(top_if, "if-multi11", print_irg("if-multi.nml", "-D N=1 -D K=1"))


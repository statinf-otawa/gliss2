#!/usr/bin/python
from maat import *
from maat import test
from maat import ocaml

# configuration
GEP = "../gep/gep"
MKIRG = "../irg/mkirg"
GLISS_ATTR = "../gep/gliss-attr"

out = directory("out")

# simple test case
simple = test.case("simple", deps = out)

for t in ["alone.nmp", "for.nmp", "irregular.nmp", "qvm.nml"]:
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



#!/usr/bin/python
# maat can downloaded from https://github.com/hcasse/maat

from maat import test

IRG = "../irg/"
PRINT_IRG = IRG + "print_irg"

all = test.case("all")

# failing test
tests = [
	("image_param", 	""),
	("double_param", 	""),
	("bad_named_param",	""),
	("arg-bad-type",	"-D N=3"),
	("arg-bad-arg",		"-D N=x")
]
for (t, a) in tests:
	test.failing_command(all, t,  "%s %s.nml %s" % (PRINT_IRG, t, a),
		err = "out/%s.err" % t)

# success test
tests = [
	("for", 		"")
]
for (t, a) in tests:
	test.command(all, t,  "%s %s.nml %s" % (PRINT_IRG, t, a),
		out = "out/%s.out" % t)


# output tests
tests = [
	("arg-none", ""),
	("arg-int", "-D N=1"),
	("arg-str", "-D N=YYY")
]
for (t, a) in tests:
	test.output(all, t, "%s %s.nml %s" % (PRINT_IRG, t, a),
		out = "out/%s.out", out_ref = "ref/%s.out" % t)

#!/usr/bin/python
# test to call before making publicly available a new version of GLISS
# test all known instruction sets for backward compatibility
# maat can downloaded from https://github.com/hcasse/maat

from maat import *
from maat import std
from maat import test

test.before(
	remove("public", ignore_error = True),
	makedir("public")
)

def home(a):
	return (a, "hg clone http://anon:anon@www.irit.fr/hg/TRACES/%s/trunk %s" % (a, a))

def git(a, addr):
	return (a, "git clone %s %s" % (addr, a))

for (a, f) in [
	home("sparc"),
	git("riscv", "git@github.com:hcasse/riscv.git"),
	home("tricore"),
	home("ppc2"),
	home("armv5t"),
	home("armv7t")
]:
	test.before("cd public; %s" % f)
	test.command(test.case(a), "%s-build" % a, "cd public/%s; make GLISS_PREFIX=../../.." % a)


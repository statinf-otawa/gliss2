
CFLAGS=-I../include -I../src -g -O3
LIBADD += $$(shell bash ../src/$(proc)-config --libs)
EXEC=$(proc)-disasm

all: $$(EXEC)

$$(EXEC): $(proc)-disasm.o ../src/lib$(proc).a
	$$(CC) $$(CFLAGS) -o $$@ $$< $$(LIBADD)

clean:
	rm -rf $(proc)-disasm.o

distclean: clean
	rm -rf $$(EXEC)

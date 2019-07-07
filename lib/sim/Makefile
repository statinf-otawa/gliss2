CFLAGS=-I../include -I../src -g -O3
LIBADD =  $$(shell bash ../src/$(proc)-config --libs)
EXEC=$(proc)-sim

all: $$(EXEC)

$$(EXEC): $(proc)-sim.o  ../src/lib$(proc).a
	$$(CC) $$(CFLAGS) -o $$@ $$< $$(LIBADD)

clean:
	rm -f $(proc)-sim.o

distclean: clean
	rm -f $$(EXEC)

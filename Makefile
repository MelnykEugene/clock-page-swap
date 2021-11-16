CC          = gcc
DEBUG_FLAGS = -ggdb -Wall
CFLAGS      = -std=gnu99 -fPIC $(DEBUG_FLAGS)

all: libvmsim iterative-walk random-hop

libvmsim: vmsim.o mmu.o bs.o
	$(CC) $(CFLAGS) -shared -o libvmsim.so vmsim.o mmu.o bs.o

vmsim.o: vmsim.h mmu.h vmsim.c
	$(CC) $(CFLAGS) -c vmsim.c

mmu.o: mmu.h vmsim.h mmu.c
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) -c mmu.c

bs.o: bs.h bs.c vmsim.h
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) -c bs.c

iterative-walk: iterative-walk.c vmsim.h
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) -L. -o iterative-walk iterative-walk.c -lvmsim

random-hop: random-hop.c vmsim.h
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) -L. -o random-hop random-hop.c -lvmsim

docs:
	doxygen

clean:
	rm -rf *.o *.so iterative-walk

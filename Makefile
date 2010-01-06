#Makefile

CC=gcc
LDFLAGS=-lpcap -lm
CFLAGS=-O3
DCFLAGS=-g
PCFLAGS='-g -pg'
ifneq (${DEBUG},)
CFLAGS = -g -DDEBUG
endif

OBJECTS = edd.o


all: edd

edd: $(OBJECTS)
	$(CC) $(OCFLAGS) -o $@ $(OBJECTS) $(LDFLAGS)

debug:
	 ${MAKE} DEBUG=y

profile:
	${MAKE} CFLAGS+=${PCFLAGS}

clean:
	-rm -v $(OBJECTS)
	-rm edd

indent:
	find -type f -name '*.[ch]' | xargs indent -kr -i4 -cdb -sc -sob -ss -ncs -ts8 -nut

# oldschool header file dependency checking.
deps:
	-rm -f deps.d
	for i in *.c; do gcc -MM $$i >> deps.d; done

ifneq ($(wildcard deps.d),)
include deps.d
endif


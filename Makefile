all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

Makefile.rocq:
	rocq makefile -f _RocqProject -o Makefile.rocq

install: Makefile.rocq
	+@make -f Makefile.rocq install

.PHONY: all clean install

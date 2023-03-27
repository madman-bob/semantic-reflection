.PHONY: all install semantic-reflection test retest clean

all: semantic-reflection

install:
	idris2 --install semantic-reflection.ipkg

semantic-reflection:
	idris2 --build semantic-reflection.ipkg

test:
	make -C tests test

retest:
	make -C tests retest

clean:
	make -C tests clean
	$(RM) -r build

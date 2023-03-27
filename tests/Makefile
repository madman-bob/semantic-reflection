.PHONY: test retest clean

INTERACTIVE ?= --interactive
threads ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

TEST_SCRIPTS := $(wildcard */run) $(wildcard */*/run)
DEPENDS := $(TEST_SCRIPTS:run=depends)

test: build/exec/semantic-reflection-tests $(DEPENDS)
	./build/exec/semantic-reflection-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only $(only)

retest: build/exec/semantic-reflection-tests $(DEPENDS)
	./build/exec/semantic-reflection-tests idris2 $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only $(only)

build/exec/semantic-reflection-tests: semantic-reflection-tests.ipkg SemanticReflectionTests.idr
	idris2 --build semantic-reflection-tests.ipkg

%/depends:
	@mkdir "$@"
	@ln -s "$(CURDIR)/../build/ttc" "$@/semantic-reflection-0"

clean:
	$(RM) failures
	$(RM) -r build
	@find . -depth -name 'depends' -type d -exec rm -rf {} \;
	@find . -type f -name 'output' -exec rm -rf {} \;

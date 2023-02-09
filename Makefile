DY_HOME 	?= .
FSTAR_HOME 	?= $(dir $(shell which fstar.exe))/..
Z3 		?= $(shell which z3)
COMPARSE_HOME 	?= $(DY_HOME)/../comparse

include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

SOURCE_DIR = src

INCLUDE_DIRS = $(SOURCE_DIR) $(COMPARSE_HOME)/src
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

FSTAR_EXTRACT = --extract '-* +DY'
FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '+241@247+285' --cache_dir cache --odir obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	dune clean
	rm -rf hints obj cache ml/lib/src ml/tests/src

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIR))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIR)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

# Verification

hints:
	mkdir $@

cache:
	mkdir $@

obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | hints cache obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction
ALL_LIB_ML_FILES = $(filter-out obj/Comparse_Tests_%.ml,$(ALL_ML_FILES))
ALL_TEST_ML_FILES = $(filter obj/Comparse_Tests_%.ml,$(ALL_ML_FILES))

.PRECIOUS: obj/%.ml
obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib

extract_lib: $(ALL_LIB_ML_FILES)

copy_lib: extract_lib
	mkdir -p ml/lib/src
	cp $(ALL_LIB_ML_FILES) ml/lib/src

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include obj

# Compilation

.PHONY: extract_tests copy_tests check

extract_tests: $(ALL_TEST_ML_FILES)

copy_tests: extract_tests
	mkdir -p ml/tests/src
	cp $(ALL_TEST_ML_FILES) ml/tests/src

check: copy_lib copy_tests
	OCAMLPATH=$(FSTAR_HOME)/bin:$(OCAMLPATH) dune runtest --no-buffer --profile=release

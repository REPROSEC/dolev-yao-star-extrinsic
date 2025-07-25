DY_HOME 	?= .
FSTAR_EXE 	?= $(shell which fstar.exe)
Z3 		?= $(shell which z3)
COMPARSE_HOME 	?= $(DY_HOME)/../comparse

INNER_SOURCE_DIRS = core lib lib/comparse lib/crypto lib/event lib/hpke lib/label lib/state lib/utils lib/communication
SOURCE_DIRS = $(addprefix $(DY_HOME)/src/, $(INNER_SOURCE_DIRS))
INNER_EXAMPLE_DIRS = nsl_pk iso_dh
EXAMPLE_DIRS ?= $(addprefix $(DY_HOME)/examples/, $(INNER_EXAMPLE_DIRS))
INNER_TEST_DIRS = core
TEST_DIRS = $(addprefix $(DY_HOME)/test/, $(INNER_TEST_DIRS))

INCLUDE_DIRS = $(SOURCE_DIRS) $(TEST_DIRS) $(EXAMPLE_DIRS) $(COMPARSE_HOME)/src
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +DY +Comparse'

# Allowed warnings:
# - (Warning 242) Definitions of inner let-rec ... and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types
# - (Warning 335) Interface ... is admitted without an implementation 

FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '@0..1000' --warn_error '+242-335' --record_hints --hint_dir $(DY_HOME)/hints --cache_dir $(DY_HOME)/cache --odir $(DY_HOME)/obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	#dune clean
	rm -rf $(DY_HOME)/hints $(DY_HOME)/obj $(DY_HOME)/cache $(DY_HOME)/ml/lib/src $(DY_HOME)/ml/tests/src

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fsti,$(TEST_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(TEST_DIRS))) \
  $(wildcard $(addsuffix /*.fsti,$(EXAMPLE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(EXAMPLE_DIRS)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
$(DY_HOME)/.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include $(DY_HOME)/.depend

# Verification

$(DY_HOME)/hints:
	mkdir $@

$(DY_HOME)/cache:
	mkdir $@

$(DY_HOME)/obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | $(DY_HOME)/hints $(DY_HOME)/cache $(DY_HOME)/obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction
.PRECIOUS: $(DY_HOME)/obj/%.ml
$(DY_HOME)/obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib

extract_lib: $(ALL_ML_FILES)

copy_lib: extract_lib
	mkdir -p $(DY_HOME)/ml/lib/src
	cp $(ALL_ML_FILES) $(DY_HOME)/ml/lib/src

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include $(DY_HOME)/obj

# Compilation

.PHONY: check

check:

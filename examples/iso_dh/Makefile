DY_HOME ?= ../..
include $(DY_HOME)/Makefile

test:
	cd $(DY_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_DH_Debug.native
	$(DY_HOME)/obj/DY_Example_DH_Debug.native

include ../../Makefile

test:
	cd $(DY_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_NSL_Debug.native
	$(DY_HOME)/obj/DY_Example_NSL_Debug.native

SOURCES = expander.ml my_compile.ml main.ml
PACKS = compiler-libs.common compiler-libs.bytecomp
RESULT = expander
OCAMLMAKEFILE = /Users/YukiIshii/lab/expander/OCamlMakefile
include $(OCAMLMAKEFILE)

go :
	./expander -c test.ml

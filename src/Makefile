OCAMLBUILD_FLAGS := \
  -classic-display \

OCAMLBUILD_TARGETS := \
  pairInsertionSort.native \
  pairInsertionSort_funs.native

.PHONY: all clean

all:
	@ ocamlbuild $(OCAMLBUILD_FLAGS) $(OCAMLBUILD_TARGETS)

clean:
	@ ocamlbuild $(OCAMLBUILD_FLAGS) -clean
	@ rm -f *~

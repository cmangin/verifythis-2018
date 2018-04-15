OCAMLBUILD_FLAGS := \
  -classic-display \

OCAMLBUILD_TARGETS := \
  pairInsertionSort.native \
  pairInsertionSort_funs.native \
	challenge1.native \
	challenge2.native \
	challenge3.native \

.PHONY: all clean

all:
	@ ocamlbuild $(OCAMLBUILD_FLAGS) $(OCAMLBUILD_TARGETS)

clean:
	@ ocamlbuild $(OCAMLBUILD_FLAGS) -clean
	@ rm -f *~
	@ rm -f $(OCAMLBUILD_TARGETS)

.PHONY: all clean

all:
	@ $(MAKE) -C proofs $@

clean:
	@ $(MAKE) -C src $@
	@ $(MAKE) -C proofs $@

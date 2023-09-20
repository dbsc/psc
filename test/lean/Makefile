.PHONY: all

all: charon aeneas

lake-packages:
	lake update

build:
	lake update
	lake build

aeneas:
	aeneas.exe psc.llbc -backend lean

charon:
	# charon --opaque=main --dest=./test/lean
	$(MAKE) -C ../.. charon

clean:
	rm -rf *.llbc

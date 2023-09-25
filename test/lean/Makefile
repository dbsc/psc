.PHONY: all build aeneas charon clean

all: charon aeneas

build:
	lake update
	lake build

aeneas:
	aeneas.exe psc.llbc -backend lean

charon:
	charon --opaque=main --dest=./test/lean

clean:
	rm -rf *.llbc

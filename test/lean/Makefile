.PHONY: all build aeneas charon clean

all: charon aeneas build

build:
	lake build

aeneas:
	aeneas.exe psc.llbc -backend lean -no-gen-lib-entry

charon:
	charon --opaque=main --dest=./test/lean

clean:
	rm -rf *.llbc

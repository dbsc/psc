.PHONY: all build aeneas charon clean

all: charon aeneas build

build:
	lake build

aeneas:
	aeneas.exe test.llbc -backend lean -no-gen-lib-entry

charon:
	charon --opaque=main --dest=./test/lean --crate test

clean:
	rm -rf *.llbc

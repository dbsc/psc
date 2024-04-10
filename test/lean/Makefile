.PHONY: all build aeneas charon clean

all: charon aeneas build

build:
	lake build

aeneas:
	aeneas test.llbc -backend lean -split-files -ext-name-pats

charon:
	charon --opaque=main --dest=./test/lean --crate test

clean:
	rm -rf *.llbc
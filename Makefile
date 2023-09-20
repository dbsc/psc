.PHONY: charon aeneas clean

all: charon aeneas

lake:
	lake build

charon:
	charon --opaque=main --dest=./test/lean --crate test

clean:
	rm -rf *.llbc

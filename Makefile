.PHONY: charon aeneas clean

all: charon aeneas

lake:
	lake build

charon:
	charon --opaque=main

aeneas:
	aeneas.exe psc.llbc -backend lean

clean:
	rm -rf *.llbc

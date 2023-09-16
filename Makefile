.PHONY: charon aeneas

all: charon aeneas

charon:
	charon --opaque=main

aeneas:
	aeneas.exe psc.llbc -backend lean

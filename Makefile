.PHONY: clean test

all:
	cargo build

test:
	$(MAKE) -C test/lean all

clean:

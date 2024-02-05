# psc

## Description
The goal of the project is to verify cryptographic primitives of [arkworks](https://github.com/arkworks-rs) library used in [Substrate](https://github.com/paritytech/polkadot-sdk) framework and Polkadot node code. 

Verification is performed through translation of code from Rust to Lean4 with the help of [Charon](https://github.com/AeneasVerif/charon) + [Aeneas](https://github.com/AeneasVerif/aeneas). After that, properties and proofs for them are formulated.

The translation of functions and structures can be found in [Funs.lean](test/lean/Test/Funs.lean) and [Types.lean](test/lean/Test/Types.lean). These files are automatically generated

Manually formulated properties and proofs can be found in [Proofs.lean](test/lean/Proofs.lean)

Work is currently in progress on the [BigInt](https://github.com/arkworks-rs/algebra/blob/fc3f6614b4b1aa4303a0204daece19679bea04c5/ff/src/biginteger/mod.rs) primitive of large numbers.

## Dependencies
The main dependencies are [charon](https://github.com/AeneasVerif/charon) and [aeneas](https://github.com/AeneasVerif/aeneas). To get everything up and running without issues you can use the Dockerfile in the root of the repository.

### Docker setup
```bash
docker build -t psc .
docker run -it -v $(pwd):/workspace psc bash
```

On VSCode, you can also install the Dev Containers extension and open this project in a container.

## Build
To build, simply run `make`.

## Tests
The tests can be run with `make test`.

For code that is reached from the `main.rs` entry point, `charon` and `aeneas` generate provable code in the `test/lean/Test` folder. Proofs should be written in `test/lean/Proofs.lean`. You can find a nice tutorial on aeneas proofs [here](https://github.com/AeneasVerif/aeneas/blob/main/tests/lean/Tutorial.lean).

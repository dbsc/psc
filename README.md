# psc

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

For code that is reached from the `main.rs` entry point, `charon` and `aeneas` generate provable code in the `test/lean/Test` folder. Proofs should be written in `test/lean/Proofs.lean`.

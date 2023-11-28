FROM fedora:latest

# Update packages
RUN dnf -y update
RUN dnf install -y git rsync dune

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=/root/.cargo/bin:$PATH

# Install and setup OCaml
RUN dnf -y install ocaml opam gmp-devel
RUN opam init -y
RUN opam switch create 4.13.1+options
RUN opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc unionFind ocamlgraph

# Setup charon and aeneas
RUN git clone https://github.com/AeneasVerif/charon.git && cd charon && git checkout 1b96962ee7b1fb1b7fcd03a68f7a5a95d59e71a1 && cd ..
RUN git clone https://github.com/AeneasVerif/aeneas.git && cd aeneas && git checkout 7fc7c82aa61d782b335e7cf37231fd9998cd0d89 && cd ..
RUN eval $(opam env) && cd charon && make && cd ..
RUN opam install -y ./charon/charon-ml
RUN eval $(opam env) && cd aeneas && make && cd ..
ENV PATH="/charon/bin:${PATH}"
ENV PATH="/aeneas/bin:${PATH}"

# Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:$PATH"
RUN elan toolchain install leanprover/lean4:stable
RUN cd aeneas/backends/lean && lake build && cd ..

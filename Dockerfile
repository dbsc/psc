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
RUN git clone https://github.com/AeneasVerif/charon.git
RUN git clone https://github.com/AeneasVerif/aeneas.git
RUN eval $(opam env) && cd charon && make && cd ..
RUN opam install -y ./charon/charon-ml
RUN eval $(opam env) && cd aeneas && make && cd ..
ENV PATH="/charon/bin:${PATH}"
ENV PATH="/aeneas/bin:${PATH}"

FROM fedora:latest

# Update packages
RUN dnf -y update

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Install and setup OCaml
RUN dnf -y install ocaml opam gmp-devel
RUN opam init -y
RUN opam switch create 4.13.1+options
RUN opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc

# Setup charon and aeneas
RUN dnf -y install git
RUN git clone https://github.com/AeneasVerif/charon.git
RUN git clone https://github.com/AeneasVerif/aeneas.git

# Install curl and procps (for 'ps' command)
RUN dnf -y install curl procps

# Install Rustup and Cargo
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=/root/.cargo/bin:$PATH

RUN dnf -y install dune

RUN eval $(opam env) && cd charon && make && cd ..
RUN opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc unionFind ocamlgraph
RUN dnf install -y rsync
RUN opam install -y ./charon/charon-ml
RUN eval $(opam env) && cd aeneas && make && cd ..

ENV PATH="/charon/bin:${PATH}"
ENV PATH="/aeneas/bin:${PATH}"
RUN echo $PATH

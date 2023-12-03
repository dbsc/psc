FROM fedora:latest

# Update packages
RUN dnf -y update
RUN dnf install -y git rsync dune ocaml opam gmp-devel

# Add psc user and switch to it
RUN useradd -ms /bin/bash psc
USER psc

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Install and setup OCaml
RUN opam init -y
RUN opam switch create 4.13.1+options
RUN opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc unionFind ocamlgraph menhir
RUN echo 'eval $(opam env)' >> ~/.bashrc

# Setup charon
WORKDIR /home/psc
ENV PATH="/home/psc/.cargo/bin:${PATH}"
RUN git clone https://github.com/AeneasVerif/charon.git
RUN . ~/.bashrc && cd charon && make # && opam install -y name_matcher_parser ./charon-ml
RUN . ~/.bashrc && opam install -y ./charon/charon-ml || true
RUN . ~/.bashrc && opam install -y ./charon/charon-ml
RUN echo 'export PATH="$PATH:$HOME/charon/bin"' >> ~/.bashrc
ENV PATH="/charon/bin:${PATH}"
# RUN opam install -y --deps-only ./charon/charon-ml
# RUN eval $(opam env) && cd charon && make && cd ..
# RUN opam install -y ./charon/charon-ml

# # Setup Aeneas
RUN git clone https://github.com/AeneasVerif/aeneas.git
# RUN opam install -y --deps-only ./aeneas/compiler
RUN . ~/.bashrc && cd aeneas && make
RUN echo 'export PATH="$PATH:$HOME/aeneas/bin"' >> ~/.bashrc
ENV PATH="/aeneas/bin:${PATH}"

# # Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
RUN echo 'export PATH="$PATH:$HOME/.elan/bin"' >> ~/.bashrc
# ENV PATH="/root/.elan/bin:$PATH"
RUN . ~/.bashrc && elan toolchain install leanprover/lean4:stable
RUN . ~/.bashrc && cd aeneas/backends/lean && lake build

FROM ubuntu:focal

# Update packages
<<<<<<< HEAD
RUN apt-get -y update
RUN apt-get install -y git rsync dune make build-essential

# hadolint ignore=DL3008
RUN apt-get update && apt-get install --no-install-recommends -y  locales curl xz-utils vim  ca-certificates && apt-get clean && rm -rf /var/lib/apt/lists/* \
      && mkdir -m 0755 /nix && groupadd -r nixbld && chown root /nix \
      && for n in $(seq 1 10); do useradd -c "Nix build user $n" -d /var/empty -g nixbld -G nixbld -M -N -r -s "$(command -v nologin)" "nixbld$n"; done
SHELL ["/bin/bash", "-o", "pipefail", "-c"]
RUN set -o pipefail && curl -L https://nixos.org/nix/install | bash

# Fixes locale-related issues: https://gitlab.haskell.org/ghc/ghc/-/issues/8118
RUN locale-gen en_US.UTF-8
ENV LANG='en_US.UTF-8' LANGUAGE='en_US:en' LC_ALL='en_US.UTF-8'
ENV USER=root
RUN echo "source $HOME/.nix-profile/etc/profile.d/nix.sh" >> "$HOME/.bashrc"

# Build charon and aeneas
RUN git clone https://github.com/AeneasVerif/charon.git 
RUN . "$HOME/.nix-profile/etc/profile.d/nix.sh" && cd charon && nix build .#charon -o nix-build --extra-experimental-features nix-command --extra-experimental-features flakes && cd ..
RUN git clone https://github.com/AeneasVerif/aeneas.git 
RUN . "$HOME/.nix-profile/etc/profile.d/nix.sh" && cd aeneas && nix build .#aeneas -o nix-build --extra-experimental-features nix-command --extra-experimental-features flakes && cd ..

# Setup charon and aeneas
ENV PATH="/charon/bin:${PATH}"
ENV PATH="/aeneas/nix-build/bin:${PATH}"

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=/root/.cargo/bin:$PATH
=======
RUN dnf -y update
RUN dnf install -y git rsync dune ocaml opam gmp-devel

# Add psc user and switch to it
RUN useradd -ms /bin/bash psc
USER psc
WORKDIR /home/psc

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Install and setup OCaml
RUN opam init -y
RUN opam switch create 4.13.1+options
RUN opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix odoc unionFind ocamlgraph menhir
RUN echo 'eval $(opam env)' >> ~/.bashrc

# Setup charon
RUN git clone https://github.com/AeneasVerif/charon.git
RUN . ~/.bashrc && cd charon && make
RUN . ~/.bashrc && cd charon/charon-ml && opam install -y . || opam install -y .
RUN echo 'export PATH="$PATH:$HOME/charon/bin"' >> ~/.bashrc

# # Setup Aeneas
RUN git clone https://github.com/AeneasVerif/aeneas.git
RUN . ~/.bashrc && cd aeneas && make
RUN echo 'export PATH="$PATH:$HOME/aeneas/bin"' >> ~/.bashrc
>>>>>>> 67bb35abc0df4af92e13bfba207480819a67a898

# # Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
<<<<<<< HEAD
ENV PATH="/root/.elan/bin:$PATH"
RUN elan toolchain install leanprover/lean4:stable
RUN cd aeneas/backends/lean && lake build && cd ..
=======
RUN echo 'export PATH="$PATH:$HOME/.elan/bin"' >> ~/.bashrc
RUN . ~/.bashrc && elan toolchain install leanprover/lean4:stable
RUN . ~/.bashrc && cd aeneas/backends/lean && lake build
>>>>>>> 67bb35abc0df4af92e13bfba207480819a67a898

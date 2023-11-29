FROM ubuntu:focal

# Update packages
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
RUN . "$HOME/.nix-profile/etc/profile.d/nix.sh" && cd charon && nix build .#charon -o nix-build --extra-experimental-features nix-command --extra-experimental-features flakes && make build-charon-rust && cd ..
RUN git clone https://github.com/AeneasVerif/aeneas.git 
RUN . "$HOME/.nix-profile/etc/profile.d/nix.sh" && cd aeneas && nix build .#aeneas -o nix-build --extra-experimental-features nix-command --extra-experimental-features flakes && cd ..

# Setup charon and aeneas
ENV PATH="/charon//bin:${PATH}"
ENV PATH="/aeneas/nix-build/bin:${PATH}"

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH=/root/.cargo/bin:$PATH

# Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:$PATH"
RUN elan toolchain install leanprover/lean4:stable
RUN cd aeneas/backends/lean && lake build && cd ..

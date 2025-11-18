FROM ubuntu:22.04

WORKDIR /workspace

COPY scripts/setup-aeneas.sh .

RUN apt-get update

RUN apt-get install -y git

RUN apt-get install -y opam

RUN apt-get install -y curl

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | bash -s -- -y

ENV PATH="/root/.cargo/bin:${PATH}"

RUN opam init --disable-sandboxing

RUN apt-get install -y libgmp-dev pkg-config

RUN ./setup-aeneas.sh

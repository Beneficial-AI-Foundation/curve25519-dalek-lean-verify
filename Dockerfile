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

COPY scripts/extract_items.py .

COPY scripts/run_extraction_experiment.py .

RUN cp aeneas/bin/aeneas /usr/local/bin

RUN cp aeneas/charon/bin/charon /usr/local/bin

RUN cp aeneas/charon/bin/charon-driver /usr/local/bin

RUN apt-get install -y protobuf-compiler

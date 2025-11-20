FROM ubuntu:24.04
RUN apt-get update && apt-get install -y curl git
WORKDIR /workspace
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf > install.sh
RUN chmod +x install.sh
RUN ./install.sh -y


ENV PATH="$PATH:/opt/inspect_tool_support/bin"
RUN apt-get install -y python3 python3-pip python3-venv
RUN python3 -m venv /opt/inspect_tool_support && \
    /opt/inspect_tool_support/bin/pip install inspect-tool-support && \
    /opt/inspect_tool_support/bin/inspect-tool-support post-install
# TODO Maybe instead start with aisiuk/inspect-tool-support image?

ENV PATH="$PATH:/root/.elan/bin/"
RUN echo "Needs repo after [2025-11-20 Thu 17:11]" # NOTE: Update this to invalidate next line's cache
RUN git clone https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
WORKDIR /workspace/curve25519-dalek-lean-verify
# NOTE: When you change this commit, please bump the date in DOCKER_IMAGE_TAG
RUN git checkout cc05d152e97b2232a3e0b974d42afc4665579b6b
COPY src/dalek_lean_ai/remove_proofs.py /tmp/remove_proofs.py
RUN find Curve25519Dalek/ -name '*.lean' -exec python3 /tmp/remove_proofs.py -i {} +
RUN lake exe cache get
RUN lake build
# Prevent cheating
RUN rm -rf .git

WORKDIR /workspace
RUN git clone https://github.com/AeneasVerif/aeneas
WORKDIR /workspace/aeneas
RUN git checkout 7c9a204277d5ef043a758e2fa26485ca5bb735b6

WORKDIR /workspace/curve25519-dalek-lean-verify

RUN apt-get install ripgrep

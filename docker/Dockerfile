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
RUN git clone https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
WORKDIR /workspace/curve25519-dalek-lean-verify
RUN git checkout afa6a3e50af21887c0f133cec190f6d73b7d51b1
RUN lake exe cache get
RUN lake build

WORKDIR /workspace
RUN git clone https://github.com/AeneasVerif/aeneas
WORKDIR /workspace/aeneas
RUN git checkout 7c9a204277d5ef043a758e2fa26485ca5bb735b6

WORKDIR /workspace/curve25519-dalek-lean-verify

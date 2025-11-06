FROM ubuntu:24.04
RUN apt-get update && apt-get install -y curl git
WORKDIR /workspace
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf > install.sh
RUN chmod +x install.sh
RUN ./install.sh -y
ENV PATH="$PATH:/root/.elan/bin/"
RUN git clone https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
WORKDIR /workspace/curve25519-dalek-lean-verify
RUN git checkout dfccbc9927d779cbd75bc0d2027a52315dca3d98
RUN lake exe cache get
RUN lake build

ENV PATH="$PATH:/opt/inspect_tool_support/bin"
RUN apt-get install -y python3 python3-pip python3-venv
RUN python3 -m venv /opt/inspect_tool_support && \
    /opt/inspect_tool_support/bin/pip install inspect-tool-support && \
    /opt/inspect_tool_support/bin/inspect-tool-support post-install
# TODO Maybe instead start with aisiuk/inspect-tool-support image?

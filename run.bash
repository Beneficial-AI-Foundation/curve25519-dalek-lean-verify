#!/usr/bin/env bash
set -euo pipefail

# Read the tag from DOCKER_TAG file
TAG=$(cat DOCKER_TAG)

# Run the docker image with bash
echo "Running curve25519-dalek-verify:$TAG"
docker run -it curve25519-dalek-verify:$TAG /bin/bash

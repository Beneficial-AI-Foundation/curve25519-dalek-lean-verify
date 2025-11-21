#!/usr/bin/env bash
set -euo pipefail

# Read the tag from DOCKER_TAG file
TAG=$(cat DOCKER_TAG)

# Build the docker image
echo "Building Docker image with tag: $TAG"
docker build -t curve25519-dalek-verify:$TAG .

echo "Successfully built:"
echo "  - curve25519-dalek-verify:$TAG"

#!/usr/bin/env bash
set -euo pipefail

# Check if directory argument is provided
if [ $# -ne 1 ]; then
    echo "Usage: $0 <directory>" >&2
    exit 1
fi

# Get the real path of the directory
DIR=$(realpath "$1")

if [ ! -d "$DIR" ]; then
    echo "Error: $DIR is not a directory" >&2
    exit 1
fi

# Read the tag from DOCKER_TAG file
TAG=$(cat DOCKER_TAG)

# Run the docker image with bash, mounting the directory and limiting RAM to 20GB
echo "Running curve25519-dalek-verify:$TAG"
echo "Mounting $DIR to /workspace/$(basename $DIR)"
docker run -it \
    --memory=20g \
    -v "$DIR:/workspace/$(basename $DIR)" \
    curve25519-dalek-verify:$TAG /bin/bash

#!/usr/bin/env bash
DOCKER_TAG=$(cat "$(dirname "$0")/DOCKER_IMAGE_TAG")
docker build -t "$DOCKER_TAG" .

#!/usr/bin/env bash
DOCKER_TAG=$(cat "$(dirname "$0")/DOCKER_IMAGE_TAG")
cd docker/
docker build -t "$DOCKER_TAG" .

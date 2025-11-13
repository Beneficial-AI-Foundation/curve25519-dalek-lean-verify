# lean_agent

This repository uses [inspect](https://inspect.aisi.org.uk) to see how many
of the functions from
https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
can be verified by an LLM.


## Installation

1. Install [uv](https://github.com/astral-sh/uv) with `curl -LsSf https://astral.sh/uv/install.sh | sh`
1. The LLM agent runs in a Docker sandbox.
   To prepare the Docker image, run `./build_docker_image.bash`.
   This will take ~10 minutes and use up ~10 GB of disk space---it's
   downloading a cached version of [mathlib4](https://github.com/leanprover-community/mathlib4).
1. `uv sync` will handle the necessary Python dependencies.

## Configuration

Put this in `.env`:

```sh
OPENROUTER_API_KEY=<secret key here>
```

(i.e. `.env` should match `.env.example`, but with values filled in)

If you want to use a different provider, adjust the environment variables
as described [here](https://inspect.aisi.org.uk/#getting-started),
and hence update the Python dependencies (e.g. `uv add openai`).

## Running the eval

`uv run inspect eval src/dalek_lean_ai/run_eval.py --model openrouter/openai/gpt-5-mini --time-limit 1800`

You can restrict to only a few samples using `--limit`
(see [here](https://inspect.aisi.org.uk/options.html) for the full list of options).

## Viewing results

`uv run inspect view`

## How to run on NixOS

Install uv as normal, and put `programs.nix-ld.enable = true;` in your configuration.nix.

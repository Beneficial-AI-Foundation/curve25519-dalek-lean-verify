<p align="center">
<img
 alt="dalek-cryptography logo: a dalek with edwards curves as sparkles coming out of its radar-schnozzley blaster thingies"
 width="200px"
 src="https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png"/>
</p>

# Verify Dalek elliptic curve cryptography using Lean

A project to formally verify [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek), a Rust implementation of elliptic curve cryptography.
The formal verification uses [Lean](https://lean-lang.org) and relies on the Lean representation of the Rust code produced by [Aeneas](https://github.com/AeneasVerif/aeneas).

Maintainers: Oliver Butterley & [The Beneficial AI Foundation](https://www.beneficialaifoundation.org/)

## Contributing

See [`CONTRIBUTING.md`](./CONTRIBUTING.md).

## Project status

See [`status.md`](./status.md) and the [Project Site](https://beneficial-ai-foundation.github.io/curve25519-dalek-lean-verify/) for full details.

## Project workflow, verification trust model and repo structure

See [`details.md`](./site/details.md).

## Code of Conduct

We follow the [Rust Code of Conduct](http://www.rust-lang.org/conduct.html),
with the following additional clause:

* We respect the rights to privacy and anonymity for contributors and people in
  the community.  If someone wishes to contribute under a pseudonym different to
  their primary identity, that wish is to be respected by all contributors.

## License

The verification code (the Lean project in this repo) is licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)).

The code under [`curve25519-dalek/`](curve25519-dalek/) is vendored (with minimal modifications) from the upstream [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek) project and is licensed under the BSD-3-Clause license; see [`curve25519-dalek/LICENSE`](curve25519-dalek/LICENSE).



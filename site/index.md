---
# https://vitepress.dev/reference/default-theme-home-page
layout: home

hero:
  name: "Formally verifying"
  text: "Dalek elliptic curve cryptography"
  tagline: Project to formally verify the Rust code of curve25519-dalek using Lean
  image:
    src: https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png
    alt: dalek-cryptography logo
  actions:
    - theme: brand
      text: View Stats
      link: /stats
    - theme: alt
      text: Function Status
      link: /status
---

This project aims to formally verify the [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek) Rust library using the [Lean theorem prover](https://lean-lang.org). We use [Aeneas](https://github.com/AeneasVerif/aeneas) to automatically extract Rust code into Lean, then we write formal specifications and proofs to ensure the cryptographic implementations are mathematically correct and free from bugs.

We aim to:
- Demonstrate the viability of verifying Rust cryptographic code using Lean
- Develop techniques to make Rust-to-Lean verification more accessible
- Create a resource for learning verification of real-world Rust code

See the [project repo](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) or [project description](details.md) for further details.

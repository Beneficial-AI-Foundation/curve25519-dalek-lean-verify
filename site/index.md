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
  # actions:
  #   - theme: brand
  #     text: Markdown Examples
  #     link: /markdown-examples
  #   - theme: alt
  #     text: API Examples
  #     link: /api-examples

features:
  - title: Trust model
    details: What does we need to trust in order to trust these proofs.
    link: trust
  - title: Project progress
    details: Check out the latest status and track our progress through the codebase.
    link: /status
  - title: Project details
    details: Read more about how, what and where.
    link: /details
---

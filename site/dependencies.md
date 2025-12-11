---
title: Dependency Graph
---

<script setup>
import { data } from './.vitepress/data/deps.data'
import DependencyGraph from './.vitepress/components/DependencyGraph.vue'
</script>

# Function Dependency Graph

This interactive graph visualizes the dependencies between functions in the curve25519-dalek verification project.

<DependencyGraph :functions="data.functions" />

## Understanding the Graph

- **Nodes** represent functions from the curve25519-dalek crate
- **Arrows** point from a function to its dependencies (the functions it calls)
- **Colors** indicate the verification status:
  - **Blue**: Fully verified (function and all its dependencies are verified)
  - **Green**: Verified (function's spec theorem has no `sorry`)
  - **Orange**: Specified (has a spec theorem, but contains `sorry`)
  - **Gray**: Not specified (no spec theorem exists)

## Verification Status

The CLI tool (`lake exe deps`) analyzes each function to determine:

1. **specified**: Whether a theorem `{function_name}_spec` exists
2. **verified**: Whether the spec theorem's proof contains no `sorry`
3. **fully_verified**: Whether the function is verified AND all its transitive dependencies are also verified

A function is only **fully verified** when we have complete confidence in its correctness - both its own proof is complete and every function it depends on is also fully verified.

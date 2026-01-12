---
title: Functions
layout: home
---

<script setup lang="ts">
import { defineAsyncComponent } from 'vue'
import { data as depsData } from './.vitepress/data/deps.data'

const FunctionsTable = defineAsyncComponent(() =>
  import('./.vitepress/components/FunctionsTable.vue')
)
</script>

## Functions

Browse and filter all extracted functions from `functions.json`. This data is generated directly from the Lean codebase analysis.

<FunctionsTable :functions="depsData.functions" />

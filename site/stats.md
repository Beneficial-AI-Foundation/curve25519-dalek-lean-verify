---
title: Stats
layout: home
---

<script setup>
import { data } from './.vitepress/data/deps.data'
import DependencyGraph3D from './.vitepress/components/DependencyGraph3D.vue'
</script>

<DependencyGraph3D :functions="data.functions" />

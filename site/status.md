---
title: Status
layout: home
---

<script setup lang="ts">
import { data } from './.vitepress/data/status.data'
import { data as githubData } from './.vitepress/data/github.data'
import StatusTable from './.vitepress/components/StatusTable.vue'
import { useGitHubMatching } from './.vitepress/composables/useGitHubMatching'

const { entries } = data
const { findItemsForFunction } = useGitHubMatching()
</script>

## Function Status

This table shows the verification status of all functions in the project. Click on a function to see more details.

<StatusTable
  :data="{ functions: entries }"
  :issues="githubData"
  :findIssuesForFunction="findItemsForFunction"
/>

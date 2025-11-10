<template>
  <a
    :href="item.url"
    target="_blank"
    rel="noopener"
    :class="['item-link', `item-${item.type}`, `item-${item.state}`]"
    :title="`${item.type === 'pr' ? 'PR' : 'Issue'} #${item.number}: ${item.title}`"
  >
    <span class="item-badge">
      <span class="item-type-icon">{{ item.type === 'pr' ? '⎇' : '●' }}</span>
      <span class="item-number">#{{ item.number }}</span>
      <span v-if="item.isDraft" class="item-state-icon" title="Draft PR">✏️</span>
    </span>
    <span class="item-title">{{ item.title }}</span>
    <span class="item-avatars" v-if="item.type === 'pr' || item.assignees.length > 0">
      <img
        v-if="item.type === 'pr'"
        :src="item.author.avatar_url"
        :alt="item.author.login"
        :title="`@${item.author.login}`"
        class="avatar"
      />
      <img
        v-for="assignee in item.assignees.slice(0, 3)"
        v-else
        :key="assignee.login"
        :src="assignee.avatar_url"
        :alt="assignee.login"
        :title="`@${assignee.login}`"
        class="avatar"
      />
    </span>
  </a>
</template>

<script setup lang="ts">
import type { GitHubItem } from '../data/github.data'

defineProps<{
  item: GitHubItem
}>()
</script>

<style scoped>
.item-link {
  color: var(--vp-c-brand-1);
  text-decoration: none;
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.25rem 0.5rem;
  border-radius: 4px;
  transition: background-color 0.2s;
}

.item-link:hover {
  background: var(--vp-c-bg-soft);
  text-decoration: none;
}

.item-badge {
  display: flex;
  align-items: center;
  gap: 0.35rem;
  font-weight: 600;
  white-space: nowrap;
  flex-shrink: 0;
}

.item-type-icon {
  font-size: 1em;
  line-height: 1;
}

.item-number {
  font-size: 0.9em;
}

.item-state-icon {
  font-size: 0.85em;
  margin-left: 0.1rem;
}

/* Styling based on item type and state */
.item-link.item-pr {
  border-left: 3px solid var(--vp-c-purple-1);
}

.item-link.item-pr .item-type-icon {
  color: var(--vp-c-purple-1);
  font-weight: bold;
}

.item-link.item-issue {
  border-left: 3px solid var(--vp-c-green-1);
}

.item-link.item-issue .item-type-icon {
  color: var(--vp-c-green-1);
}

.item-state-icon {
  color: var(--vp-c-yellow-1);
}

.item-title {
  color: var(--vp-c-text-2);
  font-weight: 400;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  font-size: 0.9em;
  flex: 1;
  min-width: 0;
}

.item-avatars {
  display: flex;
  align-items: center;
  gap: 0.25rem;
  margin-left: 0.5rem;
  flex-shrink: 0;
}

.avatar {
  width: 20px;
  height: 20px;
  border-radius: 50%;
  border: 1px solid var(--vp-c-divider);
  transition: transform 0.2s;
}

.avatar:hover {
  transform: scale(1.2);
  z-index: 1;
}
</style>

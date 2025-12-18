<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue'
import { getShortLabel, getMediumLabel } from '../utils/labelUtils'
import type { FunctionDep } from '../types'

const props = defineProps<{
  functions: FunctionDep[]
  placeholder?: string
}>()

const emit = defineEmits<{
  select: [leanName: string]
}>()

const searchQuery = ref('')
const showDropdown = ref(false)
const containerRef = ref<HTMLElement | null>(null)

const filteredFunctions = computed(() => {
  if (!searchQuery.value.trim()) return []
  const query = searchQuery.value.toLowerCase()
  return props.functions
    .filter(f => {
      const shortLabel = getShortLabel(f.lean_name).toLowerCase()
      const mediumLabel = getMediumLabel(f.lean_name).toLowerCase()
      return shortLabel.includes(query) || mediumLabel.includes(query)
    })
    .slice(0, 10)
})

function handleInput() {
  showDropdown.value = searchQuery.value.trim().length > 0
}

function handleSelect(leanName: string) {
  emit('select', leanName)
  searchQuery.value = ''
  showDropdown.value = false
}

function handleClickOutside(event: MouseEvent) {
  const target = event.target as HTMLElement
  if (containerRef.value && !containerRef.value.contains(target)) {
    showDropdown.value = false
  }
}

onMounted(() => {
  document.addEventListener('click', handleClickOutside)
})

onUnmounted(() => {
  document.removeEventListener('click', handleClickOutside)
})
</script>

<template>
  <div ref="containerRef" class="search-container">
    <div class="search-input-wrapper">
      <svg class="search-icon" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
        <circle cx="11" cy="11" r="8"/>
        <path d="m21 21-4.3-4.3"/>
      </svg>
      <input
        v-model="searchQuery"
        @input="handleInput"
        type="text"
        :placeholder="placeholder || 'Search functions...'"
        class="search-input"
      />
    </div>
    <div v-if="showDropdown && filteredFunctions.length > 0" class="search-dropdown">
      <button
        v-for="func in filteredFunctions"
        :key="func.lean_name"
        @click="handleSelect(func.lean_name)"
        class="search-result"
      >
        <span class="search-result-label">{{ getShortLabel(func.lean_name) }}</span>
        <span class="search-result-path">{{ getMediumLabel(func.lean_name) }}</span>
      </button>
    </div>
    <div v-else-if="showDropdown && searchQuery.trim()" class="search-dropdown">
      <div class="search-no-results">No functions found</div>
    </div>
  </div>
</template>

<style scoped>
.search-container {
  position: relative;
  flex: 1;
  max-width: 250px;
  min-width: 150px;
}

.search-input-wrapper {
  position: relative;
  display: flex;
  align-items: center;
}

.search-icon {
  position: absolute;
  left: 0.5rem;
  color: var(--vp-c-text-3);
  pointer-events: none;
}

.search-input {
  width: 100%;
  padding: 0.4rem 0.5rem 0.4rem 1.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  font-size: 0.8rem;
  font-family: monospace;
  outline: none;
  transition: border-color 0.2s;
}

.search-input:focus {
  border-color: var(--vp-c-brand-1);
}

.search-input::placeholder {
  color: var(--vp-c-text-3);
}

.search-dropdown {
  position: absolute;
  bottom: 100%;
  left: 0;
  right: 0;
  margin-bottom: 0.25rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  box-shadow: 0 -4px 12px rgba(0, 0, 0, 0.15);
  max-height: 300px;
  overflow-y: auto;
  z-index: 100;
}

.search-result {
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  width: 100%;
  padding: 0.5rem 0.75rem;
  border: none;
  background: none;
  cursor: pointer;
  text-align: left;
  transition: background-color 0.15s;
}

.search-result:hover {
  background: var(--vp-c-bg-soft);
}

.search-result:not(:last-child) {
  border-bottom: 1px solid var(--vp-c-divider);
}

.search-result-label {
  font-size: 0.875rem;
  font-weight: 600;
  color: var(--vp-c-text-1);
  font-family: monospace;
}

.search-result-path {
  font-size: 0.7rem;
  color: var(--vp-c-text-3);
  font-family: monospace;
  margin-top: 0.1rem;
}

.search-no-results {
  padding: 0.75rem;
  text-align: center;
  color: var(--vp-c-text-3);
  font-size: 0.8rem;
}
</style>

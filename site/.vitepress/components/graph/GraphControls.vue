<script setup lang="ts">
import { ref, computed, watch, type PropType } from 'vue'
import type { FileStats, SubgraphMode, GraphNode } from '../../types/graph'

const props = defineProps({
  sourceFiles: {
    type: Array as PropType<string[]>,
    required: true
  },
  enabledSourceFiles: {
    type: Object as PropType<Set<string>>,
    required: true
  },
  fileStats: {
    type: Array as PropType<FileStats[]>,
    required: true
  },
  focusedFunction: {
    type: String as PropType<string | null>,
    default: null
  },
  subgraphMode: {
    type: String as PropType<SubgraphMode>,
    default: 'all'
  },
  showGroups: {
    type: Boolean,
    default: false
  },
  showStats: {
    type: Boolean,
    default: true
  },
  summaryText: {
    type: String,
    default: ''
  },
  isFullscreen: {
    type: Boolean,
    default: false
  },
  allNodes: {
    type: Array as PropType<GraphNode[]>,
    default: () => []
  }
})

const emit = defineEmits<{
  (e: 'toggleSourceFile', file: string): void
  (e: 'enableAllSourceFiles'): void
  (e: 'soloSourceFile', file: string): void
  (e: 'setSubgraphMode', mode: SubgraphMode): void
  (e: 'clearFocus'): void
  (e: 'toggleShowGroups'): void
  (e: 'toggleShowStats'): void
  (e: 'fitToView'): void
  (e: 'recenter'): void
  (e: 'reset'): void
  (e: 'toggleFullscreen'): void
  (e: 'focusOnFunction', nodeId: string): void
}>()

const showFileDropdown = ref(false)
const showViewOptions = ref(false)
const searchQuery = ref('')
const showSearchDropdown = ref(false)

// Search results - filter nodes by search query
const searchResults = computed(() => {
  const query = searchQuery.value.toLowerCase().trim()
  if (query.length < 2) return []

  return props.allNodes
    .filter(node => {
      const label = node.label.toLowerCase()
      const fullLabel = node.fullLabel.toLowerCase()
      const id = node.id.toLowerCase()
      return label.includes(query) || fullLabel.includes(query) || id.includes(query)
    })
    .slice(0, 10) // Limit to 10 results
})

// Get short display name for a node
function getNodeDisplayName(node: GraphNode): string {
  return node.label
}

// Select a search result
function selectSearchResult(node: GraphNode) {
  emit('focusOnFunction', node.id)
  searchQuery.value = ''
  showSearchDropdown.value = false
}

// Close search dropdown when clicking outside
function handleSearchBlur() {
  // Delay to allow click on dropdown item
  setTimeout(() => {
    showSearchDropdown.value = false
  }, 200)
}

// Get display name for source file
function getFileName(sourceFile: string): string {
  if (sourceFile === 'unknown') return 'Unknown'
  const parts = sourceFile.split('/')
  return parts[parts.length - 1]
}

// Check if a file is enabled
function isFileEnabled(file: string): boolean {
  return props.enabledSourceFiles.has(file)
}

// Count of enabled files
const enabledCount = computed(() => props.enabledSourceFiles.size)

// File stats lookup
function getFileStatsFor(file: string): FileStats | undefined {
  return props.fileStats.find(s => s.sourceFile === file)
}

// Subgraph mode options
const subgraphModes: { value: SubgraphMode; label: string }[] = [
  { value: 'both', label: 'Dependencies & Dependents' },
  { value: 'dependencies', label: 'Dependencies Only' },
  { value: 'dependents', label: 'Dependents Only' }
]
</script>

<template>
  <div class="graph-controls">
    <!-- File filter dropdown -->
    <div class="control-group">
      <button
        class="control-btn dropdown-trigger"
        @click="showFileDropdown = !showFileDropdown"
        :class="{ active: showFileDropdown }"
      >
        <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M22 19a2 2 0 0 1-2 2H4a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h5l2 3h9a2 2 0 0 1 2 2z"/>
        </svg>
        <span>Files ({{ enabledCount }}/{{ sourceFiles.length }})</span>
        <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <polyline points="6 9 12 15 18 9"/>
        </svg>
      </button>

      <div v-if="showFileDropdown" class="dropdown-menu file-dropdown">
        <div class="dropdown-header">
          <button class="link-btn" @click="emit('enableAllSourceFiles')">Select All</button>
        </div>
        <div class="dropdown-items">
          <label
            v-for="file in sourceFiles"
            :key="file"
            class="file-item"
          >
            <input
              type="checkbox"
              :checked="isFileEnabled(file)"
              @change="emit('toggleSourceFile', file)"
            />
            <span class="file-name">{{ getFileName(file) }}</span>
            <span class="file-stats" v-if="getFileStatsFor(file)">
              {{ getFileStatsFor(file)!.verified }}/{{ getFileStatsFor(file)!.total }}
            </span>
            <button
              class="solo-btn"
              @click.prevent.stop="emit('soloSourceFile', file)"
              title="Show only this file"
            >
              solo
            </button>
          </label>
        </div>
      </div>
    </div>

    <!-- Function search -->
    <div class="control-group search-group">
      <div class="search-wrapper">
        <svg class="search-icon" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="11" cy="11" r="8"/>
          <line x1="21" y1="21" x2="16.65" y2="16.65"/>
        </svg>
        <input
          type="text"
          v-model="searchQuery"
          placeholder="Search functions..."
          class="search-input"
          @focus="showSearchDropdown = true"
          @blur="handleSearchBlur"
        />
      </div>
      <div v-if="showSearchDropdown && searchResults.length > 0" class="dropdown-menu search-dropdown">
        <div
          v-for="node in searchResults"
          :key="node.id"
          class="search-result"
          @mousedown.prevent="selectSearchResult(node)"
        >
          <span class="result-name">{{ getNodeDisplayName(node) }}</span>
          <span class="result-full">{{ node.fullLabel }}</span>
        </div>
      </div>
      <div v-if="showSearchDropdown && searchQuery.length >= 2 && searchResults.length === 0" class="dropdown-menu search-dropdown">
        <div class="no-results">No functions found</div>
      </div>
    </div>

    <!-- Focus mode indicator -->
    <div v-if="focusedFunction" class="control-group">
      <div class="control-btn focus-btn">
        <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="11" cy="11" r="8"/>
          <line x1="21" y1="21" x2="16.65" y2="16.65"/>
        </svg>
        <span class="focus-name">{{ focusedFunction.split('.').pop() }}</span>
        <select
          class="mode-select"
          :value="subgraphMode"
          @change="emit('setSubgraphMode', ($event.target as HTMLSelectElement).value as SubgraphMode)"
          @click.stop
        >
          <option v-for="mode in subgraphModes" :key="mode.value" :value="mode.value">
            {{ mode.label }}
          </option>
        </select>
        <button class="clear-focus-btn" @click.stop="emit('clearFocus')" title="Clear focus">
          <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <line x1="18" y1="6" x2="6" y2="18"/>
            <line x1="6" y1="6" x2="18" y2="18"/>
          </svg>
        </button>
      </div>
    </div>

    <!-- View options -->
    <div class="control-group">
      <button
        class="control-btn"
        @click="showViewOptions = !showViewOptions"
        :class="{ active: showViewOptions }"
      >
        <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="12" cy="12" r="3"/>
          <path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z"/>
        </svg>
        <span>View</span>
      </button>

      <div v-if="showViewOptions" class="dropdown-menu view-dropdown">
        <label class="toggle-item">
          <input
            type="checkbox"
            :checked="showGroups"
            @change="emit('toggleShowGroups')"
          />
          <span>Group by file</span>
        </label>
        <label class="toggle-item">
          <input
            type="checkbox"
            :checked="showStats"
            @change="emit('toggleShowStats')"
          />
          <span>Show stats on groups</span>
        </label>
      </div>
    </div>

    <!-- View actions -->
    <div class="control-group actions">
      <button class="control-btn icon-only" @click="emit('reset')" title="Reset all filters">
        <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"/>
          <path d="M3 3v5h5"/>
        </svg>
      </button>
      <button class="control-btn icon-only" @click="emit('recenter')" title="Recenter graph">
        <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="12" cy="12" r="3"/>
          <path d="M12 2v4m0 12v4M2 12h4m12 0h4"/>
        </svg>
      </button>
      <button class="control-btn icon-only" @click="emit('toggleFullscreen')" :title="isFullscreen ? 'Exit fullscreen' : 'Enter fullscreen'">
        <svg v-if="!isFullscreen" xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M8 3H5a2 2 0 0 0-2 2v3m18 0V5a2 2 0 0 0-2-2h-3m0 18h3a2 2 0 0 0 2-2v-3M3 16v3a2 2 0 0 0 2 2h3"/>
        </svg>
        <svg v-else xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M8 3v3a2 2 0 0 1-2 2H3m18 0h-3a2 2 0 0 1-2-2V3m0 18v-3a2 2 0 0 1 2-2h3M3 16h3a2 2 0 0 1 2 2v3"/>
        </svg>
      </button>
    </div>

    <!-- Stats summary -->
    <div v-if="summaryText" class="stats-summary">
      {{ summaryText }}
    </div>
  </div>
</template>

<style scoped>
.graph-controls {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.5rem;
  background: var(--vp-c-bg-soft);
  border-bottom: 1px solid var(--vp-c-divider);
  flex-wrap: wrap;
}

.control-group {
  position: relative;
  display: flex;
  align-items: center;
  gap: 0.25rem;
}

.control-btn {
  display: flex;
  align-items: center;
  gap: 0.375rem;
  padding: 0.375rem 0.625rem;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  font-size: 0.8125rem;
  color: var(--vp-c-text-2);
  cursor: pointer;
  transition: all 0.15s;
}

.control-btn:hover {
  background: var(--vp-c-bg-elv);
  color: var(--vp-c-text-1);
  border-color: var(--vp-c-brand-1);
}

.control-btn.active {
  background: var(--vp-c-bg-elv);
  border-color: var(--vp-c-brand-1);
}

.control-btn.icon-only {
  padding: 0.375rem;
}

.dropdown-menu {
  position: absolute;
  top: 100%;
  left: 0;
  margin-top: 0.25rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.15);
  z-index: 100;
  min-width: 200px;
}

.file-dropdown {
  max-height: 400px;
  overflow-y: auto;
}

.dropdown-header {
  padding: 0.5rem 0.75rem;
  border-bottom: 1px solid var(--vp-c-divider);
  font-size: 0.75rem;
}

.link-btn {
  background: none;
  border: none;
  color: var(--vp-c-brand-1);
  cursor: pointer;
  padding: 0;
  font-size: inherit;
}

.link-btn:hover {
  text-decoration: underline;
}

.dropdown-items {
  padding: 0.25rem 0;
}

.file-item {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.375rem 0.75rem;
  cursor: pointer;
  font-size: 0.8125rem;
}

.file-item:hover {
  background: var(--vp-c-bg-soft);
}

.file-item input[type="checkbox"] {
  margin: 0;
}

.file-name {
  flex: 1;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.file-stats {
  font-size: 0.75rem;
  color: var(--vp-c-text-3);
}

.solo-btn {
  font-size: 0.625rem;
  padding: 0.125rem 0.375rem;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  color: var(--vp-c-text-3);
  cursor: pointer;
  opacity: 0;
  transition: opacity 0.15s;
}

.file-item:hover .solo-btn {
  opacity: 1;
}

.solo-btn:hover {
  background: var(--vp-c-brand-soft);
  border-color: var(--vp-c-brand-1);
  color: var(--vp-c-brand-1);
}

.view-dropdown {
  padding: 0.5rem;
}

.toggle-item {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.375rem 0.5rem;
  cursor: pointer;
  font-size: 0.8125rem;
  border-radius: 4px;
}

.toggle-item:hover {
  background: var(--vp-c-bg-soft);
}

.toggle-item input[type="checkbox"] {
  margin: 0;
}

.focus-btn {
  background: var(--vp-c-brand-soft);
  border-color: var(--vp-c-brand-1);
}

.focus-name {
  font-weight: 600;
  color: var(--vp-c-brand-1);
  max-width: 120px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.mode-select {
  padding: 0.25rem 0.375rem;
  font-size: 0.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
}

.clear-focus-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0.125rem;
  background: none;
  border: none;
  color: var(--vp-c-text-2);
  cursor: pointer;
  border-radius: 3px;
  margin-left: 0.125rem;
}

.clear-focus-btn:hover {
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.actions {
  margin-left: auto;
}

.stats-summary {
  font-size: 0.75rem;
  color: var(--vp-c-text-2);
  padding: 0.25rem 0.5rem;
  background: var(--vp-c-bg);
  border-radius: 4px;
}

/* Search styles */
.search-group {
  position: relative;
}

.search-wrapper {
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
  padding: 0.375rem 0.625rem 0.375rem 1.75rem;
  font-size: 0.8125rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  width: 180px;
  transition: all 0.15s;
}

.search-input:focus {
  outline: none;
  border-color: var(--vp-c-brand-1);
  width: 220px;
}

.search-input::placeholder {
  color: var(--vp-c-text-3);
}

.search-dropdown {
  min-width: 280px;
  max-height: 300px;
  overflow-y: auto;
}

.search-result {
  display: flex;
  flex-direction: column;
  padding: 0.5rem 0.75rem;
  cursor: pointer;
  border-bottom: 1px solid var(--vp-c-divider);
}

.search-result:last-child {
  border-bottom: none;
}

.search-result:hover {
  background: var(--vp-c-bg-soft);
}

.result-name {
  font-weight: 600;
  font-size: 0.8125rem;
  color: var(--vp-c-text-1);
}

.result-full {
  font-size: 0.6875rem;
  color: var(--vp-c-text-3);
  font-family: monospace;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.no-results {
  padding: 0.75rem;
  text-align: center;
  color: var(--vp-c-text-3);
  font-size: 0.8125rem;
}

@media (max-width: 768px) {
  .stats-summary {
    width: 100%;
    text-align: center;
  }
}
</style>

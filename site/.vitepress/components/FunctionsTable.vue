<script setup lang="ts">
import { ref, computed, watch } from 'vue'
import type { FunctionRecord } from '../data/deps.data'
import { useStatusFormatting } from '../composables/useStatusFormatting'
import { useCodeHighlight } from '../composables/useCodeHighlight'
import { getShortLabel, shortenSourcePath } from '../utils/labelUtils'

const { getVerifiedStatus } = useStatusFormatting()
const { highlightedCode: highlightedSpec, highlight: highlightSpec } = useCodeHighlight()
const { highlightedCode: highlightedDocstring, highlight: highlightDocstring } = useCodeHighlight()

const props = defineProps<{
  functions: FunctionRecord[]
}>()

// Filtering state
const searchQuery = ref('')
const showHidden = ref(false)
const showArtifacts = ref(false)
const showIgnored = ref(true)
const statusFilter = ref<'all' | 'verified' | 'externally-verified' | 'specified' | 'unspecified'>('all')

// Sorting state
const sortKey = ref<'lean_name' | 'rust_name' | 'source' | 'verified'>('lean_name')
const sortDirection = ref<'asc' | 'desc'>('asc')

// Pagination state
const currentPage = ref(1)
const pageSize = ref(300)

// Modal state
const selectedFunction = ref<FunctionRecord | null>(null)

// Copy state
const copySuccess = ref(false)

// Filtered and sorted data
const filteredFunctions = computed(() => {
  let result = props.functions.filter(fn => fn.is_relevant)

  // Hide hidden functions unless explicitly shown
  if (!showHidden.value) {
    result = result.filter(fn => !fn.is_hidden)
  }

  // Hide extraction artifacts unless explicitly shown
  if (!showArtifacts.value) {
    result = result.filter(fn => !fn.is_extraction_artifact)
  }

  // Hide ignored functions unless explicitly shown
  if (!showIgnored.value) {
    result = result.filter(fn => !fn.is_ignored)
  }

  // Status filter
  if (statusFilter.value === 'verified') {
    result = result.filter(fn => fn.verified)
  } else if (statusFilter.value === 'externally-verified') {
    result = result.filter(fn => fn.externally_verified && !fn.verified)
  } else if (statusFilter.value === 'specified') {
    result = result.filter(fn => fn.specified && !fn.verified && !fn.externally_verified)
  } else if (statusFilter.value === 'unspecified') {
    result = result.filter(fn => !fn.specified)
  }

  // Search filter
  if (searchQuery.value) {
    const query = searchQuery.value.toLowerCase()
    result = result.filter(fn =>
      fn.lean_name.toLowerCase().includes(query) ||
      (fn.rust_name?.toLowerCase().includes(query) ?? false) ||
      (fn.source?.toLowerCase().includes(query) ?? false)
    )
  }

  // Sort
  result = [...result].sort((a, b) => {
    let aVal: string | boolean = ''
    let bVal: string | boolean = ''

    switch (sortKey.value) {
      case 'lean_name':
        aVal = a.lean_name
        bVal = b.lean_name
        break
      case 'rust_name':
        aVal = a.rust_name ?? ''
        bVal = b.rust_name ?? ''
        break
      case 'source':
        aVal = a.source ?? ''
        bVal = b.source ?? ''
        break
      case 'verified':
        aVal = a.fully_verified ? 'a' : a.verified ? 'b' : a.externally_verified ? 'c' : a.specified ? 'd' : 'e'
        bVal = b.fully_verified ? 'a' : b.verified ? 'b' : b.externally_verified ? 'c' : b.specified ? 'd' : 'e'
        break
    }

    if (typeof aVal === 'string' && typeof bVal === 'string') {
      const cmp = aVal.localeCompare(bVal)
      return sortDirection.value === 'asc' ? cmp : -cmp
    }
    return 0
  })

  return result
})

// Paginated data
const paginatedFunctions = computed(() => {
  const start = (currentPage.value - 1) * pageSize.value
  return filteredFunctions.value.slice(start, start + pageSize.value)
})

const totalPages = computed(() => Math.ceil(filteredFunctions.value.length / pageSize.value))

// Stats
const stats = computed(() => {
  const relevant = props.functions.filter(fn => fn.is_relevant && !fn.is_hidden && !fn.is_extraction_artifact)
  const ignored = relevant.filter(fn => fn.is_ignored && !fn.specified && !fn.verified && !fn.externally_verified).length
  return {
    total: relevant.length,
    ignored,
    verified: relevant.filter(fn => fn.verified).length,
    fullyVerified: relevant.filter(fn => fn.fully_verified).length,
    externallyVerified: relevant.filter(fn => fn.externally_verified && !fn.verified).length,
    specified: relevant.filter(fn => fn.specified).length,
    unspecified: relevant.filter(fn => !fn.specified).length
  }
})

// Methods
function toggleSort(key: typeof sortKey.value) {
  if (sortKey.value === key) {
    sortDirection.value = sortDirection.value === 'asc' ? 'desc' : 'asc'
  } else {
    sortKey.value = key
    sortDirection.value = 'asc'
  }
}

function getSortIndicator(key: typeof sortKey.value) {
  if (sortKey.value !== key) return ''
  return sortDirection.value === 'asc' ? ' ▲' : ' ▼'
}

// Map FunctionRecord status to the format expected by useStatusFormatting
function getStatusString(fn: FunctionRecord): string {
  if (fn.verified) return 'verified'
  if (fn.externally_verified) return 'externally verified'
  if (fn.specified) return 'specified'
  return ''
}

function formatSource(fn: FunctionRecord) {
  if (!fn.source) return '-'
  const shortened = shortenSourcePath(fn.source)
  return fn.lines ? `${shortened}:${fn.lines}` : shortened
}

function openDetails(fn: FunctionRecord) {
  selectedFunction.value = fn
}

function closeModal() {
  selectedFunction.value = null
}

// Copy rust name to clipboard
async function copyRustName() {
  if (!selectedFunction.value?.rust_name) return
  try {
    await navigator.clipboard.writeText(selectedFunction.value.rust_name)
    copySuccess.value = true
    setTimeout(() => {
      copySuccess.value = false
    }, 2000)
  } catch (err) {
    console.error('Failed to copy:', err)
  }
}

// Highlight spec statement and docstring when modal opens
watch(selectedFunction, async (fn) => {
  if (fn?.spec_statement) {
    await highlightSpec(fn.spec_statement, 'lean4')
  }
  if (fn?.spec_docstring) {
    await highlightDocstring(fn.spec_docstring, 'lean4')
  }
})
</script>

<template>
  <div class="functions-table-container">
    <!-- Stats Summary -->
    <div class="stats-summary">
      <span><strong>{{ stats.total }}</strong> functions</span>
      <span class="stat-sep">|</span>
      <span class="stat-verified"><strong>{{ stats.verified }}</strong> verified</span>
      <span class="stat-sep">|</span>
      <span class="stat-ext-verified"><strong>{{ stats.externallyVerified }}</strong> ext. verified</span>
      <span class="stat-sep">|</span>
      <span class="stat-specified"><strong>{{ stats.specified - stats.verified - stats.externallyVerified }}</strong> specified only</span>
      <span class="stat-sep">|</span>
      <span class="stat-unspecified"><strong>{{ stats.unspecified }}</strong> unspecified</span>
      <span v-if="stats.ignored > 0" class="stat-sep">|</span>
      <span v-if="stats.ignored > 0" class="stat-ignored"><strong>{{ stats.ignored }}</strong> ignored</span>
    </div>

    <!-- Filters -->
    <div class="filters">
      <input
        v-model="searchQuery"
        type="text"
        placeholder="Search functions..."
        class="search-input"
      />
      <select v-model="statusFilter" class="filter-select">
        <option value="all">All Status</option>
        <option value="verified">Verified</option>
        <option value="externally-verified">Ext. Verified</option>
        <option value="specified">Specified (not verified)</option>
        <option value="unspecified">Unspecified</option>
      </select>
      <label class="checkbox-label">
        <input type="checkbox" v-model="showIgnored" />
        Show ignored
      </label>
      <label class="checkbox-label">
        <input type="checkbox" v-model="showHidden" />
        Show hidden
      </label>
      <label class="checkbox-label">
        <input type="checkbox" v-model="showArtifacts" />
        Show artifacts
      </label>
    </div>

    <!-- Results count -->
    <div class="results-count">
      Showing {{ paginatedFunctions.length }} of {{ filteredFunctions.length }} functions
    </div>

    <!-- Table -->
    <div class="table-wrapper">
      <table class="functions-table">
        <thead>
          <tr>
            <th @click="toggleSort('lean_name')" class="sortable">
              Function{{ getSortIndicator('lean_name') }}
            </th>
            <th @click="toggleSort('source')" class="sortable">
              Source{{ getSortIndicator('source') }}
            </th>
            <th @click="toggleSort('verified')" class="sortable status-col">
              Status{{ getSortIndicator('verified') }}
            </th>
            <th>Deps</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="fn in paginatedFunctions" :key="fn.lean_name" :class="{ 'row-hidden': fn.is_hidden, 'row-artifact': fn.is_extraction_artifact }">
            <td class="cell-name">
              <button @click="openDetails(fn)" class="function-button" :title="fn.lean_name">
                <code>{{ getShortLabel(fn.lean_name) }}</code>
              </button>
              <span v-if="fn.is_hidden" class="tag tag-hidden">hidden</span>
              <span v-if="fn.is_extraction_artifact" class="tag tag-artifact">artifact</span>
              <span v-if="fn.is_ignored" class="tag tag-ignored">ignored</span>
            </td>
            <td class="cell-source">
              <span class="source-link" :title="fn.source ?? ''">{{ formatSource(fn) }}</span>
            </td>
            <td class="cell-status status-col">
              <span :class="['status-icon', getVerifiedStatus(getStatusString(fn)).cssClass]">
                {{ getVerifiedStatus(getStatusString(fn)).icon }}
              </span>
            </td>
            <td class="cell-deps">
              {{ fn.dependencies.length }}
            </td>
          </tr>
        </tbody>
      </table>
    </div>

    <!-- Pagination -->
    <div class="pagination">
      <div class="pagination-controls" v-if="totalPages > 1">
        <button @click="currentPage = 1" :disabled="currentPage === 1">First</button>
        <button @click="currentPage--" :disabled="currentPage === 1">Prev</button>
        <span class="page-info">Page {{ currentPage }} of {{ totalPages }}</span>
        <button @click="currentPage++" :disabled="currentPage === totalPages">Next</button>
        <button @click="currentPage = totalPages" :disabled="currentPage === totalPages">Last</button>
      </div>
      <div class="page-size-selector">
        <label>Per page:</label>
        <select v-model.number="pageSize" @change="currentPage = 1">
          <option :value="50">50</option>
          <option :value="100">100</option>
          <option :value="200">200</option>
          <option :value="300">300</option>
          <option :value="500">500</option>
        </select>
      </div>
    </div>

    <!-- Details Modal -->
    <div v-if="selectedFunction" class="modal-overlay" @click.self="closeModal">
      <div class="modal-content">
        <button class="modal-close" @click="closeModal">&times;</button>
        <h3>{{ selectedFunction.lean_name }}</h3>

        <div class="detail-section" v-if="selectedFunction.rust_name">
          <h4>Rust Name</h4>
          <div class="code-block-wrapper">
            <code class="full-name">{{ selectedFunction.rust_name }}</code>
            <button
              @click="copyRustName"
              class="copy-icon-button"
              :class="{ copied: copySuccess }"
              :title="copySuccess ? 'Copied!' : 'Copy to clipboard'"
            >
              <span v-if="copySuccess">✓</span>
              <span v-else>
                <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                  <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                  <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                </svg>
              </span>
            </button>
          </div>
        </div>

        <div class="detail-section">
          <h4>Source Location</h4>
          <p class="detail-value">{{ selectedFunction.source ?? '-' }} {{ selectedFunction.lines ?? '' }}</p>
        </div>

        <div class="detail-section">
          <h4>Verification Status</h4>
          <p>
            <span :class="['status-icon', getVerifiedStatus(getStatusString(selectedFunction)).cssClass]">
              {{ getVerifiedStatus(getStatusString(selectedFunction)).icon }}
            </span>
            <span class="status-label">{{ getVerifiedStatus(getStatusString(selectedFunction)).label }}</span>
          </p>
        </div>

        <div class="detail-section" v-if="selectedFunction.spec_statement">
          <h4>Spec Statement</h4>
          <div class="spec-code-wrapper" v-html="highlightedSpec || `<pre><code>${selectedFunction.spec_statement}</code></pre>`"></div>
        </div>

        <div class="detail-section" v-if="selectedFunction.spec_docstring">
          <h4>Spec Docstring</h4>
          <div class="spec-code-wrapper" v-html="highlightedDocstring || `<pre><code>${selectedFunction.spec_docstring}</code></pre>`"></div>
        </div>

        <div class="detail-section" v-if="selectedFunction.dependencies.length > 0">
          <h4>Dependencies ({{ selectedFunction.dependencies.length }})</h4>
          <ul class="deps-list">
            <li v-for="dep in selectedFunction.dependencies" :key="dep">{{ getShortLabel(dep) }}</li>
          </ul>
        </div>

        <div class="detail-section" v-if="selectedFunction.dependents.length > 0">
          <h4>Dependents ({{ selectedFunction.dependents.length }})</h4>
          <ul class="deps-list">
            <li v-for="dep in selectedFunction.dependents" :key="dep">{{ getShortLabel(dep) }}</li>
          </ul>
        </div>

        <div class="detail-section" v-if="selectedFunction.nested_children.length > 0">
          <h4>Nested Children</h4>
          <ul class="deps-list">
            <li v-for="child in selectedFunction.nested_children" :key="child">{{ getShortLabel(child) }}</li>
          </ul>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.functions-table-container {
  margin: 1rem 0;
}

.stats-summary {
  margin-bottom: 1rem;
  padding: 0.75rem 1rem;
  background: var(--vp-c-bg-soft);
  border-radius: 6px;
  font-size: 0.9rem;
}

.stat-sep {
  color: var(--vp-c-text-3);
  margin: 0 0.5rem;
}

.stat-verified { color: var(--vp-c-green-1); }
.stat-ext-verified { color: #6ee7b7; }
.stat-specified { color: var(--vp-c-yellow-1); }
.stat-unspecified { color: var(--vp-c-text-2); }
.stat-ignored { color: var(--vp-c-text-3); }

.filters {
  display: flex;
  flex-wrap: wrap;
  gap: 0.75rem;
  margin-bottom: 1rem;
  align-items: center;
}

.search-input {
  flex: 1;
  min-width: 200px;
  padding: 0.5rem 0.75rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.filter-select {
  padding: 0.5rem 0.75rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 0.35rem;
  font-size: 0.9rem;
  cursor: pointer;
}

.results-count {
  font-size: 0.85rem;
  color: var(--vp-c-text-2);
  margin-bottom: 0.5rem;
}

.table-wrapper {
  overflow-x: auto;
}

.functions-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.9rem;
}

.functions-table th,
.functions-table td {
  padding: 0.6rem 0.75rem;
  text-align: left;
  border-bottom: 1px solid var(--vp-c-border);
}

.functions-table th {
  background: var(--vp-c-bg-soft);
  font-weight: 600;
}

.functions-table th.sortable {
  cursor: pointer;
  user-select: none;
}

.functions-table th.sortable:hover {
  background: var(--vp-c-bg-mute);
}

.row-hidden {
  opacity: 0.7;
}

.row-artifact {
  font-style: italic;
}

.cell-name {
  max-width: 300px;
}

.function-button {
  display: block;
  width: 100%;
  text-align: left;
  background: none;
  border: none;
  padding: 0;
  cursor: pointer;
  color: inherit;
}

.function-button:hover {
  opacity: 0.8;
}

.function-button code {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  background: transparent;
  padding: 0;
  font-size: 0.85rem;
  color: var(--vp-c-brand-1);
  cursor: pointer;
}

.function-button:hover code {
  text-decoration: underline;
}

.tag {
  display: inline-block;
  font-size: 0.7rem;
  padding: 0.1rem 0.3rem;
  border-radius: 3px;
  margin-left: 0.4rem;
  vertical-align: middle;
}

.tag-hidden {
  background: var(--vp-c-yellow-soft);
  color: var(--vp-c-yellow-darker);
}

.tag-artifact {
  background: var(--vp-c-gray-soft);
  color: var(--vp-c-text-2);
}

.tag-ignored {
  background: var(--vp-c-gray-soft);
  color: var(--vp-c-text-3);
}

.cell-source {
  max-width: 220px;
}

.source-link {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  direction: rtl;
  text-align: left;
  font-family: var(--vp-font-family-mono);
  font-size: 0.8rem;
  color: var(--vp-c-text-2);
}

.cell-status {
  white-space: nowrap;
}

.status-col {
  text-align: center;
  width: 80px;
}

/* Status icon colors - matches StatusTable */
.status-icon {
  font-size: 1.2rem;
}

.status-icon.checked,
.status-icon.verified {
  color: #10b981;
}

.status-icon.externally-verified {
  color: #6ee7b7;
}

.status-icon.specified {
  color: #3b82f6;
}

.status-icon.draft {
  color: #f59e0b;
}

.status-icon.unchecked {
  color: var(--vp-c-text-3);
}

.status-label {
  margin-left: 0.5rem;
}

.cell-deps {
  text-align: center;
  color: var(--vp-c-text-2);
}

.pagination {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 1rem;
  margin-top: 1rem;
  flex-wrap: wrap;
}

.pagination-controls {
  display: flex;
  align-items: center;
  gap: 0.5rem;
}

.pagination-controls button {
  padding: 0.4rem 0.75rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 4px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
}

.pagination-controls button:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.pagination-controls button:not(:disabled):hover {
  background: var(--vp-c-bg-soft);
}

.page-info {
  padding: 0 0.5rem;
  font-size: 0.9rem;
  color: var(--vp-c-text-2);
}

.page-size-selector {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  font-size: 0.9rem;
  color: var(--vp-c-text-2);
}

.page-size-selector select {
  padding: 0.4rem 0.5rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 4px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
}

/* Modal styles */
.modal-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 100;
}

.modal-content {
  background: var(--vp-c-bg);
  border-radius: 8px;
  padding: 1.5rem;
  max-width: 700px;
  width: 90%;
  max-height: 80vh;
  overflow-y: auto;
  position: relative;
}

.modal-close {
  position: absolute;
  top: 0.75rem;
  right: 0.75rem;
  font-size: 1.5rem;
  background: none;
  border: none;
  cursor: pointer;
  color: var(--vp-c-text-2);
}

.modal-close:hover {
  color: var(--vp-c-text-1);
}

.modal-content h3 {
  font-family: var(--vp-font-family-mono);
  font-size: 0.95rem;
  word-break: break-all;
  margin-bottom: 1rem;
  padding-right: 2rem;
}

.detail-section {
  margin-bottom: 1rem;
}

.detail-section h4 {
  font-size: 0.85rem;
  color: var(--vp-c-text-2);
  margin-bottom: 0.25rem;
}

.detail-value {
  font-family: var(--vp-font-family-mono);
  font-size: 0.85rem;
  word-break: break-all;
}

.code-block-wrapper {
  position: relative;
}

.full-name {
  display: block;
  padding: 0.75rem;
  padding-right: 3rem;
  background: var(--vp-c-bg-soft);
  border-radius: 6px;
  word-break: break-all;
  font-size: 0.9rem;
  line-height: 1.6;
  user-select: all;
}

.copy-icon-button {
  position: absolute;
  top: 0.5rem;
  right: 0.5rem;
  width: 2rem;
  height: 2rem;
  padding: 0;
  background: transparent;
  border: none;
  cursor: pointer;
  color: var(--vp-c-text-2);
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 4px;
  transition: all 0.2s;
}

.copy-icon-button:hover {
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.copy-icon-button.copied {
  color: #10b981;
}

.copy-icon-button svg {
  width: 16px;
  height: 16px;
}

/* Shiki syntax highlighting wrapper */
.spec-code-wrapper {
  border-radius: 6px;
  overflow: hidden;
}

.spec-code-wrapper :deep(pre) {
  margin: 0;
  padding: 0.75rem;
  border-radius: 6px;
  font-size: 0.8rem;
  overflow-x: auto;
  white-space: pre-wrap;
  word-break: break-all;
}

.spec-code-wrapper :deep(code) {
  font-family: var(--vp-font-family-mono);
}

/* Shiki dual theme support - use light theme colors by default */
.spec-code-wrapper :deep(.shiki),
.spec-code-wrapper :deep(.shiki span) {
  color: var(--shiki-light);
  background-color: var(--shiki-light-bg);
}

/* Fallback styling when Shiki hasn't loaded yet */
.spec-code-wrapper > pre {
  background: var(--vp-c-bg-soft);
  margin: 0;
  padding: 0.75rem;
  border-radius: 6px;
  font-size: 0.8rem;
}

.deps-list {
  font-family: var(--vp-font-family-mono);
  font-size: 0.8rem;
  padding-left: 1.25rem;
  max-height: 150px;
  overflow-y: auto;
}

.deps-list li {
  margin-bottom: 0.25rem;
}
</style>

<style>
/* Global styles for Shiki dark mode support (must be non-scoped to access html.dark) */
html.dark .spec-code-wrapper .shiki,
html.dark .spec-code-wrapper .shiki span {
  color: var(--shiki-dark) !important;
  background-color: var(--shiki-dark-bg) !important;
}
</style>

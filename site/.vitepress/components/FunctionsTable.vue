<script setup lang="ts">
import { ref, computed } from 'vue'
import type { FunctionRecord } from '../data/deps.data'

const props = defineProps<{
  functions: FunctionRecord[]
}>()

// Filtering state
const searchQuery = ref('')
const showHidden = ref(false)
const showArtifacts = ref(false)
const statusFilter = ref<'all' | 'verified' | 'specified' | 'unspecified'>('all')

// Sorting state
const sortKey = ref<'lean_name' | 'rust_name' | 'source' | 'verified'>('lean_name')
const sortDirection = ref<'asc' | 'desc'>('asc')

// Pagination state
const currentPage = ref(1)
const pageSize = ref(50)

// Modal state
const selectedFunction = ref<FunctionRecord | null>(null)

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

  // Status filter
  if (statusFilter.value === 'verified') {
    result = result.filter(fn => fn.verified)
  } else if (statusFilter.value === 'specified') {
    result = result.filter(fn => fn.specified && !fn.verified)
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
        aVal = a.fully_verified ? 'a' : a.verified ? 'b' : a.specified ? 'c' : 'd'
        bVal = b.fully_verified ? 'a' : b.verified ? 'b' : b.specified ? 'c' : 'd'
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
  return {
    total: relevant.length,
    verified: relevant.filter(fn => fn.verified).length,
    fullyVerified: relevant.filter(fn => fn.fully_verified).length,
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

function getStatusBadge(fn: FunctionRecord) {
  if (fn.fully_verified) return { class: 'badge-fully-verified', text: 'Fully Verified' }
  if (fn.verified) return { class: 'badge-verified', text: 'Verified' }
  if (fn.specified) return { class: 'badge-specified', text: 'Specified' }
  return { class: 'badge-none', text: 'Unspecified' }
}

// Helper function to extract function name from full path (matches StatusTable)
function getFunctionName(fullPath: string) {
  const parts = fullPath.split('.')
  return parts[parts.length - 1]
}

// Helper function to shorten source path (matches StatusTable)
function shortenSourcePath(source: string | null) {
  if (!source) return '-'
  return source.replace('curve25519-dalek/src/', '')
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
</script>

<template>
  <div class="functions-table-container">
    <!-- Stats Summary -->
    <div class="stats-summary">
      <span><strong>{{ stats.total }}</strong> functions</span>
      <span class="stat-sep">|</span>
      <span class="stat-verified"><strong>{{ stats.verified }}</strong> verified</span>
      <span class="stat-sep">|</span>
      <span class="stat-specified"><strong>{{ stats.specified - stats.verified }}</strong> specified only</span>
      <span class="stat-sep">|</span>
      <span class="stat-unspecified"><strong>{{ stats.unspecified }}</strong> unspecified</span>
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
        <option value="specified">Specified (not verified)</option>
        <option value="unspecified">Unspecified</option>
      </select>
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
            <th @click="toggleSort('verified')" class="sortable">
              Status{{ getSortIndicator('verified') }}
            </th>
            <th>Deps</th>
            <th>Actions</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="fn in paginatedFunctions" :key="fn.lean_name" :class="{ 'row-hidden': fn.is_hidden, 'row-artifact': fn.is_extraction_artifact }">
            <td class="cell-name">
              <span class="name-short" :title="fn.lean_name">{{ getFunctionName(fn.lean_name) }}</span>
              <span v-if="fn.is_hidden" class="tag tag-hidden">hidden</span>
              <span v-if="fn.is_extraction_artifact" class="tag tag-artifact">artifact</span>
            </td>
            <td class="cell-source">
              <span :title="fn.source ?? ''">{{ formatSource(fn) }}</span>
            </td>
            <td class="cell-status">
              <span :class="['badge', getStatusBadge(fn).class]">
                {{ getStatusBadge(fn).text }}
              </span>
            </td>
            <td class="cell-deps">
              {{ fn.dependencies.length }}
            </td>
            <td class="cell-actions">
              <button @click="openDetails(fn)" class="btn-details">Details</button>
            </td>
          </tr>
        </tbody>
      </table>
    </div>

    <!-- Pagination -->
    <div class="pagination" v-if="totalPages > 1">
      <button @click="currentPage = 1" :disabled="currentPage === 1">First</button>
      <button @click="currentPage--" :disabled="currentPage === 1">Prev</button>
      <span class="page-info">Page {{ currentPage }} of {{ totalPages }}</span>
      <button @click="currentPage++" :disabled="currentPage === totalPages">Next</button>
      <button @click="currentPage = totalPages" :disabled="currentPage === totalPages">Last</button>
    </div>

    <!-- Details Modal -->
    <div v-if="selectedFunction" class="modal-overlay" @click.self="closeModal">
      <div class="modal-content">
        <button class="modal-close" @click="closeModal">&times;</button>
        <h3>{{ selectedFunction.lean_name }}</h3>

        <div class="detail-section">
          <h4>Rust Name</h4>
          <p class="detail-value">{{ selectedFunction.rust_name ?? '-' }}</p>
        </div>

        <div class="detail-section">
          <h4>Source Location</h4>
          <p class="detail-value">{{ selectedFunction.source ?? '-' }} {{ selectedFunction.lines ?? '' }}</p>
        </div>

        <div class="detail-section">
          <h4>Verification Status</h4>
          <p>
            <span :class="['badge', getStatusBadge(selectedFunction).class]">
              {{ getStatusBadge(selectedFunction).text }}
            </span>
          </p>
        </div>

        <div class="detail-section" v-if="selectedFunction.spec_statement">
          <h4>Spec Statement</h4>
          <pre class="spec-code">{{ selectedFunction.spec_statement }}</pre>
        </div>

        <div class="detail-section" v-if="selectedFunction.spec_docstring">
          <h4>Spec Docstring</h4>
          <p class="detail-value">{{ selectedFunction.spec_docstring }}</p>
        </div>

        <div class="detail-section" v-if="selectedFunction.dependencies.length > 0">
          <h4>Dependencies ({{ selectedFunction.dependencies.length }})</h4>
          <ul class="deps-list">
            <li v-for="dep in selectedFunction.dependencies" :key="dep">{{ dep }}</li>
          </ul>
        </div>

        <div class="detail-section" v-if="selectedFunction.nested_children.length > 0">
          <h4>Nested Children</h4>
          <ul class="deps-list">
            <li v-for="child in selectedFunction.nested_children" :key="child">{{ child }}</li>
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
.stat-specified { color: var(--vp-c-yellow-1); }
.stat-unspecified { color: var(--vp-c-text-2); }

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

.name-short {
  font-family: var(--vp-font-family-mono);
  font-size: 0.85rem;
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

.cell-source {
  max-width: 200px;
  font-family: var(--vp-font-family-mono);
  font-size: 0.8rem;
  color: var(--vp-c-text-2);
}

.cell-status {
  white-space: nowrap;
}

.badge {
  display: inline-block;
  padding: 0.2rem 0.5rem;
  border-radius: 4px;
  font-size: 0.75rem;
  font-weight: 500;
}

.badge-fully-verified {
  background: var(--vp-c-green-soft);
  color: var(--vp-c-green-darker);
}

.badge-verified {
  background: var(--vp-c-green-soft);
  color: var(--vp-c-green-1);
}

.badge-specified {
  background: var(--vp-c-yellow-soft);
  color: var(--vp-c-yellow-darker);
}

.badge-none {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-2);
}

.cell-deps {
  text-align: center;
  color: var(--vp-c-text-2);
}

.cell-actions {
  white-space: nowrap;
}

.btn-details {
  padding: 0.25rem 0.5rem;
  font-size: 0.8rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 4px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
}

.btn-details:hover {
  background: var(--vp-c-bg-soft);
}

.pagination {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 0.5rem;
  margin-top: 1rem;
}

.pagination button {
  padding: 0.4rem 0.75rem;
  border: 1px solid var(--vp-c-border);
  border-radius: 4px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
}

.pagination button:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.pagination button:not(:disabled):hover {
  background: var(--vp-c-bg-soft);
}

.page-info {
  padding: 0 0.5rem;
  font-size: 0.9rem;
  color: var(--vp-c-text-2);
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

.spec-code {
  background: var(--vp-c-bg-soft);
  padding: 0.75rem;
  border-radius: 4px;
  font-size: 0.8rem;
  overflow-x: auto;
  white-space: pre-wrap;
  word-break: break-all;
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

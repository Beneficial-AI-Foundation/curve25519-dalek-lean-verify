<script setup>
import { ref, computed } from 'vue'
import FunctionDetailModal from './FunctionDetailModal.vue'
import GitHubItemLink from './GitHubItemLink.vue'
import { useStatusFormatting } from '../composables/useStatusFormatting'
import { useGitHubLinks } from '../composables/useGitHubLinks'

const { getExtractedStatus, getVerifiedStatus } = useStatusFormatting()
const { getSourceLink, getSpecLink } = useGitHubLinks()

const props = defineProps({
  data: {
    type: Object,
    required: true
  },
  issues: {
    type: Array,
    default: () => []
  },
  findIssuesForFunction: {
    type: Function,
    default: null
  }
})

// Helper function to find related issues/PRs for a function
// Returns an array of matching items
function findRelatedItems(functionName) {
  if (!props.issues || props.issues.length === 0) return []
  if (!props.findIssuesForFunction) return []

  return props.findIssuesForFunction(functionName, props.issues)
}

// Helper function to extract function name from full path
function getFunctionName(fullPath) {
  const parts = fullPath.split('::')
  return parts[parts.length - 1]
}

// Helper function to shorten source path
function shortenSourcePath(source) {
  return source.replace('curve25519-dalek/src/', '')
}

// Filter state
const filters = ref({
  function: '',
  extracted: '',
  verified: ''
})

// Sort state
const sortColumn = ref('function')
const sortDirection = ref('asc')

// Pagination state
const currentPage = ref(1)
const perPage = ref(100)

// Modal state
const isModalOpen = ref(false)
const selectedFunction = ref(null)

// Open modal with function details
function openFunctionDetail(func) {
  selectedFunction.value = func
  isModalOpen.value = true
}

// Close modal
function closeModal() {
  isModalOpen.value = false
  selectedFunction.value = null
}

// Column visibility state
const visibleColumns = ref({
  function: true,
  source: true,
  extracted: true,
  verified: true,
  issue: true,
  notes: true  // Shown by default
})

// Computed: Filter data
const filteredData = computed(() => {
  return props.data.functions.filter(func => {
    const matchesFunction = !filters.value.function ||
      func.function.toLowerCase().includes(filters.value.function.toLowerCase())

    const matchesExtracted = !filters.value.extracted ||
      (filters.value.extracted === 'not-extracted' ? func.extracted !== 'extracted' : func.extracted === filters.value.extracted)

    const matchesVerified = !filters.value.verified ||
      (filters.value.verified === 'no-status' ? !func.verified || func.verified === '' : func.verified === filters.value.verified)

    return matchesFunction && matchesExtracted && matchesVerified
  })
})

// Computed: Sort filtered data
const sortedData = computed(() => {
  const data = [...filteredData.value]

  data.sort((a, b) => {
    let aVal = a[sortColumn.value] || ''
    let bVal = b[sortColumn.value] || ''

    if (sortDirection.value === 'asc') {
      return aVal.toString().localeCompare(bVal.toString())
    } else {
      return bVal.toString().localeCompare(aVal.toString())
    }
  })

  return data
})

// Computed: Paginate sorted data
const paginatedData = computed(() => {
  const start = (currentPage.value - 1) * perPage.value
  const end = start + perPage.value
  return sortedData.value.slice(start, end)
})

// Computed: Total pages
const totalPages = computed(() => {
  return Math.ceil(sortedData.value.length / perPage.value)
})

// Computed: Page numbers to show
const pageNumbers = computed(() => {
  const pages = []
  const total = totalPages.value
  const current = currentPage.value

  // Always show first page
  pages.push(1)

  // Show pages around current page
  for (let i = Math.max(2, current - 1); i <= Math.min(total - 1, current + 1); i++) {
    if (!pages.includes(i)) pages.push(i)
  }

  // Always show last page
  if (total > 1 && !pages.includes(total)) {
    pages.push(total)
  }

  return pages
})

// Method: Toggle sort
function toggleSort(column) {
  if (sortColumn.value === column) {
    sortDirection.value = sortDirection.value === 'asc' ? 'desc' : 'asc'
  } else {
    sortColumn.value = column
    sortDirection.value = 'asc'
  }
  currentPage.value = 1
}

// Method: Change page
function goToPage(page) {
  if (page >= 1 && page <= totalPages.value) {
    currentPage.value = page
  }
}

// Stats
const stats = computed(() => ({
  total: props.data.functions.length,
  extracted: props.data.functions.filter(f => f.extracted === 'extracted').length,
  verified: props.data.functions.filter(f => f.verified === 'verified').length,
  specified: props.data.functions.filter(f => f.verified === 'specified').length,
  ai_proveable: props.data.functions.filter(f => f['ai-proveable'] && f['ai-proveable'].trim() !== '').length,
  filtered: sortedData.value.length
}))
</script>

<template>
  <div class="status-table-wrapper">
    <!-- Stats Bar -->
    <div class="stats-bar">
      <div class="stat">
        <span class="stat-label">Total:</span>
        <span class="stat-value">{{ stats.total }}</span>
      </div>
      <div class="stat">
        <span class="stat-label">Extracted:</span>
        <span class="stat-value stat-extracted">{{ stats.extracted }}</span>
      </div>
      <div class="stat">
        <span class="stat-label">Verified:</span>
        <span class="stat-value stat-verified">{{ stats.verified }}</span>
      </div>
      <div class="stat">
        <span class="stat-label">Spec only:</span>
        <span class="stat-value stat-specified">{{ stats.specified }}</span>
      </div>
      <div class="stat">
        <span class="stat-label">AI Proveable:</span>
        <span class="stat-value stat-ai-proveable">{{ stats.ai_proveable }}</span>
      </div>
      <div class="stat" v-if="stats.filtered !== stats.total">
        <span class="stat-label">Filtered:</span>
        <span class="stat-value stat-filtered">{{ stats.filtered }}</span>
      </div>
    </div>

    <!-- Filters -->
    <div class="filters">
      <input
        v-model="filters.function"
        type="text"
        placeholder="Filter by function name..."
        class="filter-input"
        @input="currentPage = 1"
      />

      <select v-model="filters.extracted" class="filter-select" @change="currentPage = 1">
        <option value="">All (Extracted)</option>
        <option value="extracted">Extracted</option>
        <option value="not-extracted">Not Extracted</option>
      </select>

      <select v-model="filters.verified" class="filter-select" @change="currentPage = 1">
        <option value="">All (Status)</option>
        <option value="verified">Verified</option>
        <option value="specified">Specified</option>
        <option value="draft spec">Draft Spec</option>
        <option value="no-status">No Status</option>
      </select>
    </div>

    <!-- Table -->
    <div class="table-container">
      <table class="status-table">
        <thead>
          <tr>
            <th v-if="visibleColumns.function" @click="toggleSort('function')" class="sortable">
              Function
              <span class="sort-indicator">
                <span v-if="sortColumn === 'function'">
                  {{ sortDirection === 'asc' ? '▲' : '▼' }}
                </span>
              </span>
            </th>
            <th v-if="visibleColumns.source" @click="toggleSort('source')" class="sortable">
              Rust Source
              <span class="sort-indicator">
                <span v-if="sortColumn === 'source'">
                  {{ sortDirection === 'asc' ? '▲' : '▼' }}
                </span>
              </span>
            </th>
            <th v-if="visibleColumns.extracted" class="status-col">
              Extracted
            </th>
            <th v-if="visibleColumns.verified" class="status-col">
              Verified
            </th>
            <th v-if="visibleColumns.issue" class="issue-col">
              Issue
            </th>
            <th v-if="visibleColumns.notes">Notes</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="func in paginatedData" :key="func.function">
            <td v-if="visibleColumns.function" class="function-col">
              <button
                @click="openFunctionDetail(func)"
                class="function-button"
                :title="func.function"
              >
                <code>{{ getFunctionName(func.function) }}</code>
              </button>
            </td>
            <td v-if="visibleColumns.source" class="source-col">
              <a
                :href="getSourceLink(func.source, func.lines)"
                target="_blank"
                rel="noopener"
                class="source-link"
                :title="func.source"
              >
                {{ shortenSourcePath(func.source) }}
              </a>
            </td>
            <td v-if="visibleColumns.extracted" class="status-col">
              <span :class="['status-icon', getExtractedStatus(func.extracted).cssClass]">
                {{ getExtractedStatus(func.extracted).icon }}
              </span>
            </td>
            <td v-if="visibleColumns.verified" class="status-col">
              <a v-if="func.spec_theorem && func.verified"
                 :href="getSpecLink(func.spec_theorem)"
                 target="_blank"
                 rel="noopener"
                 class="status-link"
                 :title="`View spec: ${func.spec_theorem}`">
                <span :class="['status-icon', getVerifiedStatus(func.verified).cssClass]">
                  {{ getVerifiedStatus(func.verified).icon }}
                </span>
              </a>
              <span v-else :class="['status-icon', getVerifiedStatus(func.verified).cssClass]">
                {{ getVerifiedStatus(func.verified).icon }}
              </span>
            </td>
            <td v-if="visibleColumns.issue" class="issue-col">
              <div v-if="findRelatedItems(func.function).length > 0" class="related-items">
                <GitHubItemLink
                  v-for="item in findRelatedItems(func.function)"
                  :key="item.number"
                  :item="item"
                />
              </div>
              <span v-else class="no-issue">—</span>
            </td>
            <td v-if="visibleColumns.notes" class="notes-col">{{ func.notes }}</td>
          </tr>
        </tbody>
      </table>
    </div>

    <!-- Column Controls -->
    <div class="column-controls">
      <span class="column-controls-label">Show columns:</span>
      <label class="column-toggle">
        <input type="checkbox" v-model="visibleColumns.source" />
        <span>Source</span>
      </label>
      <label class="column-toggle">
        <input type="checkbox" v-model="visibleColumns.extracted" />
        <span>Extracted</span>
      </label>
      <label class="column-toggle">
        <input type="checkbox" v-model="visibleColumns.verified" />
        <span>Verified</span>
      </label>
      <label class="column-toggle">
        <input type="checkbox" v-model="visibleColumns.issue" />
        <span>Issue</span>
      </label>
      <label class="column-toggle">
        <input type="checkbox" v-model="visibleColumns.notes" />
        <span>Notes</span>
      </label>
    </div>

    <!-- Pagination -->
    <div class="pagination">
      <div class="pagination-info">
        Showing {{ ((currentPage - 1) * perPage) + 1 }}–{{ Math.min(currentPage * perPage, stats.filtered) }}
        of {{ stats.filtered }} functions
      </div>

      <div class="pagination-controls">
        <button
          @click="goToPage(currentPage - 1)"
          :disabled="currentPage === 1"
          class="pagination-btn"
          aria-label="Previous page"
        >
          ← Previous
        </button>

        <template v-for="page in pageNumbers" :key="page">
          <span v-if="page - (pageNumbers[pageNumbers.indexOf(page) - 1] || 0) > 1" class="pagination-ellipsis">
            ...
          </span>
          <button
            @click="goToPage(page)"
            :class="['pagination-btn', { active: page === currentPage }]"
            :aria-label="`Go to page ${page}`"
            :aria-current="page === currentPage ? 'page' : undefined"
          >
            {{ page }}
          </button>
        </template>

        <button
          @click="goToPage(currentPage + 1)"
          :disabled="currentPage === totalPages"
          class="pagination-btn"
          aria-label="Next page"
        >
          Next →
        </button>
      </div>

      <select v-model.number="perPage" class="per-page-select" @change="currentPage = 1">
        <option :value="10">10 per page</option>
        <option :value="25">25 per page</option>
        <option :value="50">50 per page</option>
        <option :value="100">100 per page</option>
      </select>
    </div>

    <!-- Legend -->
    <div class="legend">
      <div class="legend-section">
        <h4>Extracted</h4>
        <div class="legend-item">
          <span class="status-icon checked">✓</span>
          <span>Rust code has been extracted to Lean</span>
        </div>
        <div class="legend-item">
          <span class="status-icon unchecked">☐</span>
          <span>Extraction pending</span>
        </div>
      </div>

      <div class="legend-section">
        <h4>Verified</h4>
        <div class="legend-item">
          <span class="status-icon verified">✓</span>
          <span>Function has been formally verified</span>
        </div>
        <div class="legend-item">
          <span class="status-icon specified">📋</span>
          <span>Formal specifications but no proofs</span>
        </div>
        <div class="legend-item">
          <span class="status-icon draft">✏️</span>
          <span>Natural language specifications</span>
        </div>
        <div class="legend-item">
          <span class="status-icon unchecked">☐</span>
          <span>No verification work completed yet</span>
        </div>
      </div>
    </div>

    <!-- Function Detail Modal -->
    <FunctionDetailModal
      :isOpen="isModalOpen"
      :func="selectedFunction"
      @close="closeModal"
    />
  </div>
</template>

<style scoped>
.status-table-wrapper {
  margin: 2rem 0;
}

.stats-bar {
  display: flex;
  gap: 2rem;
  margin-bottom: 1.5rem;
  padding: 1rem 1.5rem;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
  flex-wrap: wrap;
}

.stat {
  display: flex;
  gap: 0.5rem;
  align-items: baseline;
}

.stat-value {
  font-weight: 700;
}

.stat-extracted {
  color: var(--vp-c-green-1);
}

.stat-verified {
  color: var(--vp-c-brand-1);
}

.stat-specified {
  color: var(--vp-c-purple-1);
}

.stat-ai-proveable {
  color: #8b5cf6;
}

.stat-filtered {
  color: var(--vp-c-yellow-1);
}

.filters {
  display: flex;
  gap: 0.75rem;
  margin-bottom: 1.5rem;
  flex-wrap: wrap;
}

.column-controls {
  display: flex;
  gap: 1rem;
  align-items: center;
  flex-wrap: wrap;
  padding: 0.75rem 1rem;
  background: var(--vp-c-bg-soft);
  border-radius: 6px;
  margin-top: 1rem;
  margin-bottom: 1rem;
}

.column-toggle {
  display: flex;
  align-items: center;
  gap: 0.4rem;
  cursor: pointer;
  user-select: none;
}

.filter-input,
.filter-select {
  padding: 0.5rem 0.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  background: var(--vp-c-bg);
}

.filter-input {
  min-width: 250px;
  flex: 1;
}

.table-container {
  overflow-x: auto;
  margin-bottom: 1.5rem;
}

.status-table {
  width: 100%;
  border-collapse: collapse;
}

.status-table thead {
  background: var(--vp-c-bg-soft);
}

.status-table th {
  padding: 0.5rem 0.75rem;
  text-align: left;
  font-weight: 600;
  border-bottom: 2px solid var(--vp-c-divider);
  white-space: nowrap;
  vertical-align: middle;
}

.status-table th.sortable {
  cursor: pointer;
  user-select: none;
}

.status-table td {
  padding: 0.4rem 0.75rem;
  border-bottom: 1px solid var(--vp-c-divider);
  vertical-align: top;
}

.status-table tbody tr:hover {
  background: var(--vp-c-bg-soft);
}

.sort-indicator {
  display: inline-block;
  margin-left: 0.25rem;
  color: var(--vp-c-brand-1);
  font-size: 0.8em;
  vertical-align: middle;
  width: 14px;
}

/* Column width constraints */
.function-col {
  max-width: 220px;
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
  font-size: inherit;
  color: var(--vp-c-brand-1);
  cursor: pointer;
}

.function-button:hover code {
  text-decoration: underline;
}

.source-col {
  max-width: 220px;
}

.source-link {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  direction: rtl;
  text-align: left;
}

.status-col {
  text-align: center;
  width: 80px;
}

.status-link {
  text-decoration: none;
}

/* Status icon colors */
.status-icon {
  font-size: 1.2rem;
}

.status-icon.checked,
.status-icon.verified {
  color: #10b981;
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

.issue-col {
  max-width: 400px;
}

.related-items {
  display: flex;
  flex-direction: column;
  gap: 0.4rem;
}

.no-issue {
  color: var(--vp-c-text-3);
}

.notes-col {
  max-width: 300px;
}

.legend {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
  gap: 2rem;
  margin-top: 2rem;
  padding: 1.5rem;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
}

.legend-section h4 {
  margin: 0 0 1rem 0;
}

.legend-item {
  display: flex;
  align-items: center;
  gap: 0.75rem;
  margin-bottom: 0.75rem;
}

.legend-item .status-icon {
  min-width: 1.5rem;
}

.pagination {
  display: flex;
  justify-content: space-between;
  align-items: center;
  flex-wrap: wrap;
  gap: 1rem;
}

.pagination-controls {
  display: flex;
  gap: 0.5rem;
  align-items: center;
}

.pagination-btn {
  padding: 0.4rem 0.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  background: var(--vp-c-bg);
  cursor: pointer;
  min-width: 38px;
}

.pagination-btn:hover:not(:disabled) {
  border-color: var(--vp-c-brand-1);
}

.pagination-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.pagination-btn.active {
  background: var(--vp-c-brand-1);
  color: white;
}

.per-page-select {
  padding: 0.4rem 0.6rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  background: var(--vp-c-bg);
  cursor: pointer;
}

/* Responsive */
@media (max-width: 768px) {
  .stats-bar {
    gap: 1rem;
  }

  .filters {
    flex-direction: column;
  }

  .filter-input {
    width: 100%;
  }

  .function-col {
    max-width: 180px;
  }

  .source-col {
    max-width: 180px;
  }

  .status-col {
    width: 60px;
  }

  .notes-col {
    max-width: 200px;
  }

  .pagination {
    flex-direction: column;
    align-items: stretch;
  }

  .pagination-controls {
    justify-content: center;
  }

  .per-page-select {
    width: 100%;
  }

  .column-controls {
    flex-direction: column;
    align-items: flex-start;
  }
}
</style>

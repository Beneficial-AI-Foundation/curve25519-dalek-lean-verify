<script setup>
import { ref, computed } from 'vue'

const props = defineProps({
  data: {
    type: Object,
    required: true
  }
})

// Helper function to extract function name from full path
function getFunctionName(fullPath) {
  const parts = fullPath.split('::')
  return parts[parts.length - 1]
}

// Helper function to shorten source path
function shortenSourcePath(source) {
  return source.replace('curve25519-dalek/src/', '')
}

// Helper function to create GitHub link for Rust source
function getSourceLink(source, lines) {
  const baseUrl = 'https://github.com/dalek-cryptography/curve25519-dalek/blob/main'
  const lineMatch = lines.match(/L(\d+)(?:-L(\d+))?/)
  if (lineMatch) {
    const start = lineMatch[1]
    const end = lineMatch[2]
    const lineFragment = end ? `#L${start}-L${end}` : `#L${start}`
    return `${baseUrl}/${source}${lineFragment}`
  }
  return `${baseUrl}/${source}`
}

// Helper function to create GitHub link for Lean spec file
function getSpecLink(specPath) {
  if (!specPath) return null
  const baseUrl = 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master'
  return `${baseUrl}/${specPath}`
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
const perPage = ref(25)

// Column visibility state
const visibleColumns = ref({
  function: true,
  source: true,
  extracted: true,
  verified: true,
  notes: false  // Hidden by default
})

// Computed: Filter data
const filteredData = computed(() => {
  return props.data.functions.filter(func => {
    const matchesFunction = !filters.value.function ||
      func.function.toLowerCase().includes(filters.value.function.toLowerCase())

    const matchesExtracted = !filters.value.extracted ||
      func.extracted === filters.value.extracted

    const matchesVerified = !filters.value.verified ||
      func.verified === filters.value.verified

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
      </select>

      <select v-model="filters.verified" class="filter-select" @change="currentPage = 1">
        <option value="">All (Status)</option>
        <option value="verified">Verified</option>
        <option value="specified">Specified</option>
        <option value="draft spec">Draft Spec</option>
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
            <th v-if="visibleColumns.extracted" @click="toggleSort('extracted')" class="sortable status-col">
              Extracted
              <span class="sort-indicator">
                <span v-if="sortColumn === 'extracted'">
                  {{ sortDirection === 'asc' ? '▲' : '▼' }}
                </span>
              </span>
            </th>
            <th v-if="visibleColumns.verified" @click="toggleSort('verified')" class="sortable status-col">
              Verified
              <span class="sort-indicator">
                <span v-if="sortColumn === 'verified'">
                  {{ sortDirection === 'asc' ? '▲' : '▼' }}
                </span>
              </span>
            </th>
            <th v-if="visibleColumns.notes">Notes</th>
          </tr>
        </thead>
        <tbody>
          <tr v-for="func in paginatedData" :key="func.function">
            <td v-if="visibleColumns.function" class="function-col">
              <code :title="func.function">{{ getFunctionName(func.function) }}</code>
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
              <span :class="['status-icon', func.extracted === 'extracted' ? 'checked' : 'unchecked']">
                {{ func.extracted === 'extracted' ? '✓' : '☐' }}
              </span>
            </td>
            <td v-if="visibleColumns.verified" class="status-col">
              <a v-if="func.spec_theorem && func.verified"
                 :href="getSpecLink(func.spec_theorem)"
                 target="_blank"
                 rel="noopener"
                 class="status-link"
                 :title="`View spec: ${func.spec_theorem}`">
                <span :class="['status-icon',
                  func.verified === 'verified' ? 'verified' :
                  func.verified === 'specified' ? 'specified' :
                  func.verified === 'draft spec' ? 'draft' : 'unchecked']">
                  {{ func.verified === 'verified' ? '✓' :
                     func.verified === 'specified' ? '📋' :
                     func.verified === 'draft spec' ? '✏️' : '☐' }}
                </span>
              </a>
              <span v-else :class="['status-icon',
                func.verified === 'verified' ? 'verified' :
                func.verified === 'specified' ? 'specified' :
                func.verified === 'draft spec' ? 'draft' : 'unchecked']">
                {{ func.verified === 'verified' ? '✓' :
                   func.verified === 'specified' ? '📋' :
                   func.verified === 'draft spec' ? '✏️' : '☐' }}
              </span>
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
  border: 1px solid var(--vp-c-divider);
  flex-wrap: wrap;
}

.stat {
  display: flex;
  gap: 0.5rem;
  align-items: baseline;
}

.stat-label {
  font-weight: 500;
  color: var(--vp-c-text-2);
  font-size: 0.9em;
}

.stat-value {
  font-weight: 700;
  font-size: 1.1em;
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
  border: 1px solid var(--vp-c-divider);
  margin-top: 1rem;
  margin-bottom: 1rem;
}

.column-controls-label {
  font-weight: 600;
  color: var(--vp-c-text-2);
  font-size: 0.9em;
}

.column-toggle {
  display: flex;
  align-items: center;
  gap: 0.4rem;
  cursor: pointer;
  font-size: 0.9em;
  color: var(--vp-c-text-1);
  user-select: none;
}

.column-toggle input[type="checkbox"] {
  cursor: pointer;
}

.column-toggle input[type="checkbox"]:disabled {
  cursor: not-allowed;
  opacity: 0.5;
}

.column-toggle:hover span {
  color: var(--vp-c-brand-1);
}

.filter-input,
.filter-select {
  padding: 0.5rem 0.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  font-size: 0.9rem;
  transition: border-color 0.2s;
}

.filter-input {
  min-width: 250px;
  flex: 1;
}

.filter-select {
  min-width: 150px;
}

.filter-input:focus,
.filter-select:focus {
  outline: none;
  border-color: var(--vp-c-brand-1);
}

.table-container {
  overflow-x: auto;
  border: 1px solid var(--vp-c-divider);
  border-radius: 8px;
  margin-bottom: 1.5rem;
}

.status-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 0.9rem;
}

.status-table thead {
  background: var(--vp-c-bg-soft);
}

.status-table th {
  padding: 0.75rem 1rem;
  text-align: left;
  font-weight: 600;
  border-bottom: 2px solid var(--vp-c-divider);
  white-space: nowrap;
}

.status-table th.sortable {
  cursor: pointer;
  user-select: none;
  transition: background-color 0.2s;
}

.status-table th.sortable:hover {
  background: var(--vp-c-bg-elv);
}

.sort-indicator {
  display: inline-block;
  margin-left: 0.25rem;
  width: 14px;
  color: var(--vp-c-brand-1);
}

.status-table td {
  padding: 0.75rem 1rem;
  border-bottom: 1px solid var(--vp-c-divider);
  vertical-align: top;
}

.status-table tbody tr:hover {
  background: var(--vp-c-bg-soft);
}

.function-col {
  max-width: 200px;
}

.function-col code {
  display: block;
  font-family: var(--vp-font-family-mono);
  font-size: 0.85em;
  color: var(--vp-c-text-1);
  background: transparent;
  padding: 0;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  cursor: help;
}

.source-col {
  font-size: 0.85em;
  max-width: 200px;
}

.source-link {
  display: block;
  color: var(--vp-c-brand-1);
  text-decoration: none;
  transition: color 0.2s;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  direction: rtl;
  text-align: left;
}

.source-link:hover {
  color: var(--vp-c-brand-2);
  text-decoration: underline;
}

.status-col {
  text-align: center;
  width: 50px;
}

.status-link {
  text-decoration: none;
  display: inline-block;
  transition: opacity 0.2s;
}

.status-link:hover {
  opacity: 0.8;
}

.status-icon {
  font-size: 1.2rem;
  font-weight: bold;
}

.status-icon.checked {
  color: #10b981;
}

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

.notes-col {
  color: var(--vp-c-text-2);
  font-size: 0.85em;
  max-width: 300px;
}

.pagination {
  display: flex;
  justify-content: space-between;
  align-items: center;
  flex-wrap: wrap;
  gap: 1rem;
}

.pagination-info {
  color: var(--vp-c-text-2);
  font-size: 0.9em;
}

.pagination-controls {
  display: flex;
  gap: 0.5rem;
  align-items: center;
}

.pagination-btn {
  padding: 0.4rem 0.75rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  cursor: pointer;
  font-size: 0.85rem;
  transition: all 0.2s;
  min-width: 38px;
}

.pagination-btn:hover:not(:disabled) {
  background: var(--vp-c-bg-soft);
  border-color: var(--vp-c-brand-1);
}

.pagination-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.pagination-btn.active {
  background: var(--vp-c-brand-1);
  color: white;
  border-color: var(--vp-c-brand-1);
}

.pagination-ellipsis {
  color: var(--vp-c-text-3);
  padding: 0 0.25rem;
}

.per-page-select {
  padding: 0.4rem 0.6rem;
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
  font-size: 0.85rem;
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
}
</style>

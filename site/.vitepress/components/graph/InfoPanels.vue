<script setup lang="ts">
import { ref, watch, type PropType } from 'vue'
import type { GraphNode } from '../../types/graph'
import { useGitHubLinks } from '../../composables/useGitHubLinks'
import { highlightCode } from '../../composables/useCodeHighlight'

const props = defineProps({
  selectedNodes: {
    type: Array as PropType<GraphNode[]>,
    required: true
  }
})

const emit = defineEmits<{
  (e: 'deselect', nodeId: string): void
  (e: 'focusOn', nodeId: string): void
  (e: 'close'): void
  (e: 'panelHover', nodeId: string | null): void
}>()

const { getSourceLink } = useGitHubLinks()

// Cache of highlighted code per node
const highlightedSpecs = ref<Map<string, string>>(new Map())

// Highlight spec statements for selected nodes
watch(() => props.selectedNodes, async (nodes) => {
  for (const node of nodes) {
    if (node.specStatement && !highlightedSpecs.value.has(node.id)) {
      const html = await highlightCode(node.specStatement, 'lean4')
      highlightedSpecs.value.set(node.id, html)
    }
  }
}, { immediate: true, deep: true })

function getHighlightedSpec(nodeId: string): string | undefined {
  return highlightedSpecs.value.get(nodeId)
}

// Track which panels are expanded (showing full details)
const expandedPanels = ref<Set<string>>(new Set())

function toggleExpanded(nodeId: string) {
  if (expandedPanels.value.has(nodeId)) {
    expandedPanels.value.delete(nodeId)
  } else {
    expandedPanels.value.add(nodeId)
  }
}

function isExpanded(nodeId: string): boolean {
  return expandedPanels.value.has(nodeId)
}

// Get status color
function getStatusColor(node: GraphNode): string {
  switch (node.status) {
    case 'fully_verified':
    case 'verified':
      return '#22c55e'
    case 'specified':
      return '#f59e0b'
    default:
      return '#9ca3af'
  }
}

// Get status label
function getStatusLabel(node: GraphNode): string {
  switch (node.status) {
    case 'fully_verified':
      return 'Fully Verified'
    case 'verified':
      return 'Verified'
    case 'specified':
      return 'Specified'
    default:
      return 'Not Specified'
  }
}

// Copy to clipboard
async function copyToClipboard(text: string) {
  try {
    await navigator.clipboard.writeText(text)
  } catch (err) {
    console.error('Failed to copy:', err)
  }
}
</script>

<template>
  <div class="info-panels" v-if="selectedNodes.length > 0">
    <div class="panels-header">
      <span class="panels-title">Selected ({{ selectedNodes.length }})</span>
      <button class="close-all-btn" @click="emit('close')" title="Close all">
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <line x1="18" y1="6" x2="6" y2="18"/>
          <line x1="6" y1="6" x2="18" y2="18"/>
        </svg>
      </button>
    </div>

    <div class="panels-container" @mouseleave="emit('panelHover', null)">
      <div
        v-for="node in selectedNodes"
        :key="node.id"
        class="info-panel"
        :class="{ expanded: isExpanded(node.id) }"
        @mouseenter="emit('panelHover', node.id)"
      >
        <!-- Minimal header with name and status -->
        <div class="panel-header" @click="toggleExpanded(node.id)">
          <div class="panel-title-row">
            <span class="status-dot" :style="{ backgroundColor: getStatusColor(node) }"></span>
            <span class="panel-title" :title="node.id">{{ node.label }}</span>
          </div>
          <div class="panel-actions" @click.stop>
            <button
              class="panel-btn"
              @click="emit('focusOn', node.id)"
              title="Focus in graph"
            >
              <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                <circle cx="11" cy="11" r="8"/>
                <line x1="21" y1="21" x2="16.65" y2="16.65"/>
              </svg>
            </button>
            <button
              class="panel-btn close"
              @click="emit('deselect', node.id)"
              title="Close"
            >
              <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                <line x1="18" y1="6" x2="6" y2="18"/>
                <line x1="6" y1="6" x2="18" y2="18"/>
              </svg>
            </button>
          </div>
        </div>

        <!-- Spec statement (always visible when present) -->
        <div v-if="node.specStatement" class="spec-section">
          <div
            v-if="getHighlightedSpec(node.id)"
            class="spec-code-highlighted"
            v-html="getHighlightedSpec(node.id)"
          ></div>
          <pre v-else class="spec-code">{{ node.specStatement }}</pre>
        </div>
        <div v-else class="no-spec">
          <span class="no-spec-text">{{ getStatusLabel(node) }}</span>
        </div>

        <!-- Expanded details (tap to show) -->
        <div v-if="isExpanded(node.id)" class="panel-details">
          <!-- Full name -->
          <div class="info-row">
            <span class="info-label">Name:</span>
            <code class="info-value name-value" @click="copyToClipboard(node.id)" title="Click to copy">
              {{ node.fullLabel }}
            </code>
          </div>

          <!-- Source file -->
          <div v-if="node.sourceFile" class="info-row">
            <span class="info-label">Source:</span>
            <a
              :href="getSourceLink(node.sourceFile, node.lines || '')"
              target="_blank"
              class="info-link"
            >
              {{ node.sourceFile.split('/').pop() }}
              <span v-if="node.lines" class="lines-badge">{{ node.lines }}</span>
            </a>
          </div>

          <!-- Dependencies/Dependents -->
          <div class="info-row">
            <span class="info-label">Deps:</span>
            <span class="info-value">{{ node.dependencies.length }} in / {{ node.dependents.length }} out</span>
          </div>

          <!-- Spec docstring -->
          <div v-if="node.specDocstring" class="docstring-section">
            <p class="docstring">{{ node.specDocstring }}</p>
          </div>
        </div>

        <!-- Expand hint -->
        <div class="expand-hint" @click="toggleExpanded(node.id)">
          <span v-if="!isExpanded(node.id)">Details</span>
          <span v-else>Hide details</span>
          <svg
            xmlns="http://www.w3.org/2000/svg"
            width="10"
            height="10"
            viewBox="0 0 24 24"
            fill="none"
            stroke="currentColor"
            stroke-width="2"
            :class="{ rotated: isExpanded(node.id) }"
          >
            <polyline points="6 9 12 15 18 9"/>
          </svg>
        </div>
      </div>
    </div>
  </div>
</template>

<style scoped>
.info-panels {
  position: absolute;
  right: 1rem;
  top: 4rem;
  bottom: 1rem;
  width: 420px;
  max-width: calc(100vw - 2rem);
  display: flex;
  flex-direction: column;
  gap: 0.5rem;
  z-index: 50;
  pointer-events: none;
}

.panels-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 0.375rem 0.625rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  pointer-events: auto;
}

.panels-title {
  font-size: 0.75rem;
  font-weight: 600;
  color: var(--vp-c-text-1);
}

.close-all-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0.25rem;
  background: none;
  border: none;
  color: var(--vp-c-text-2);
  cursor: pointer;
  border-radius: 4px;
}

.close-all-btn:hover {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-1);
}

.panels-container {
  flex: 1;
  overflow-y: auto;
  display: flex;
  flex-direction: column;
  gap: 0.375rem;
}

.info-panel {
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  overflow: hidden;
  pointer-events: auto;
  box-shadow: 0 2px 6px rgba(0, 0, 0, 0.08);
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 0.375rem 0.5rem;
  background: var(--vp-c-bg-soft);
  cursor: pointer;
}

.panel-header:hover {
  background: var(--vp-c-bg);
}

.panel-title-row {
  display: flex;
  align-items: center;
  gap: 0.375rem;
  flex: 1;
  min-width: 0;
}

.status-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
  flex-shrink: 0;
}

.panel-title {
  font-size: 0.8125rem;
  font-weight: 600;
  color: var(--vp-c-text-1);
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.panel-actions {
  display: flex;
  align-items: center;
  gap: 0.125rem;
}

.panel-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0.1875rem;
  background: none;
  border: none;
  color: var(--vp-c-text-3);
  cursor: pointer;
  border-radius: 3px;
}

.panel-btn:hover {
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.panel-btn.close:hover {
  color: #ef4444;
}

/* Spec section - always visible */
.spec-section {
  padding: 0.5rem;
}

.spec-code {
  font-family: 'JetBrains Mono', 'Fira Code', monospace;
  font-size: 0.6875rem;
  line-height: 1.4;
  padding: 0.5rem;
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  overflow-x: auto;
  max-height: 150px;
  margin: 0;
  white-space: pre;
  color: var(--vp-c-text-1);
}

/* Shiki highlighted code container */
.spec-code-highlighted {
  font-size: 0.6875rem;
  line-height: 1.4;
  overflow-x: auto;
  max-height: 150px;
  border-radius: 4px;
  border: 1px solid var(--vp-c-divider);
}

.spec-code-highlighted :deep(pre) {
  margin: 0;
  padding: 0.5rem;
  background: var(--vp-c-bg) !important;
  font-family: 'JetBrains Mono', 'Fira Code', monospace;
  font-size: inherit;
  line-height: inherit;
}

.spec-code-highlighted :deep(code) {
  font-family: inherit;
  white-space: pre;
}

/* Handle Shiki dual theme - default to light */
.spec-code-highlighted :deep(.shiki) {
  background: var(--vp-c-bg) !important;
}

.spec-code-highlighted :deep(.shiki span) {
  color: var(--shiki-light);
}

.no-spec {
  padding: 0.5rem;
  text-align: center;
}

.no-spec-text {
  font-size: 0.6875rem;
  color: var(--vp-c-text-3);
  font-style: italic;
}

/* Expanded details */
.panel-details {
  padding: 0.5rem;
  border-top: 1px solid var(--vp-c-divider);
  background: var(--vp-c-bg-soft);
}

.info-row {
  display: flex;
  align-items: baseline;
  gap: 0.375rem;
  margin-bottom: 0.375rem;
  font-size: 0.75rem;
}

.info-row:last-child {
  margin-bottom: 0;
}

.info-label {
  color: var(--vp-c-text-3);
  flex-shrink: 0;
  font-size: 0.6875rem;
}

.info-value {
  color: var(--vp-c-text-1);
}

.name-value {
  font-family: monospace;
  font-size: 0.625rem;
  cursor: pointer;
  padding: 0.125rem 0.25rem;
  background: var(--vp-c-bg);
  border-radius: 3px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  max-width: 180px;
}

.name-value:hover {
  background: var(--vp-c-bg-elv);
}

.info-link {
  color: var(--vp-c-brand-1);
  text-decoration: none;
  display: flex;
  align-items: center;
  gap: 0.25rem;
  font-size: 0.6875rem;
}

.info-link:hover {
  text-decoration: underline;
}

.lines-badge {
  font-size: 0.5625rem;
  padding: 0.0625rem 0.1875rem;
  background: var(--vp-c-bg);
  border-radius: 2px;
  color: var(--vp-c-text-2);
}

.docstring-section {
  margin-top: 0.375rem;
  padding-top: 0.375rem;
  border-top: 1px dashed var(--vp-c-divider);
}

.docstring {
  font-size: 0.6875rem;
  color: var(--vp-c-text-2);
  line-height: 1.4;
  margin: 0;
  font-style: italic;
}

/* Expand hint */
.expand-hint {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 0.25rem;
  padding: 0.25rem;
  font-size: 0.625rem;
  color: var(--vp-c-text-3);
  cursor: pointer;
  border-top: 1px solid var(--vp-c-divider);
}

.expand-hint:hover {
  color: var(--vp-c-text-2);
  background: var(--vp-c-bg-soft);
}

.expand-hint svg {
  transition: transform 0.2s ease;
}

.expand-hint svg.rotated {
  transform: rotate(180deg);
}
</style>

<!-- Unscoped styles for dark mode syntax highlighting -->
<style>
html.dark .spec-code-highlighted .shiki span {
  color: var(--shiki-dark) !important;
}
</style>

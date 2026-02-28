<script setup lang="ts">
import { ref, computed, watch, nextTick, onMounted, type PropType } from 'vue'
import { useDraggable } from '@vueuse/core'
import type { GraphNode } from '../../types/graph'
import { useGitHubLinks } from '../../composables/useGitHubLinks'
import { highlightCode } from '../../composables/useCodeHighlight'

const props = defineProps({
  node: {
    type: Object as PropType<GraphNode>,
    required: true
  },
  initialPosition: {
    type: Object as PropType<{ x: number; y: number }>,
    required: true
  },
  containerRef: {
    type: Object as PropType<HTMLElement | null>,
    default: null
  },
  width: {
    type: Number,
    required: true
  }
})

const emit = defineEmits<{
  (e: 'deselect'): void
  (e: 'focusOn'): void
  (e: 'positionUpdate', rect: { x: number; y: number; width: number; height: number }): void
}>()

const { getSourceLink } = useGitHubLinks()

const PANEL_MIN_HEIGHT = 100
const PANEL_MARGIN = 10

// Element refs
const panelEl = ref<HTMLElement | null>(null)
const handleEl = ref<HTMLElement | null>(null)

// Draggable
const { x, y } = useDraggable(panelEl, {
  initialValue: props.initialPosition,
  handle: handleEl,
  containerElement: props.containerRef ?? undefined,
  onMove() {
    emitPosition()
  }
})

// Expanded state
const expanded = ref(false)

// Highlighted code cache
const highlightedSpec = ref<string>('')
const highlightedRust = ref<string>('')

// Highlight on mount
onMounted(async () => {
  if (props.node.specStatement) {
    highlightedSpec.value = await highlightCode(props.node.specStatement, 'lean4')
  }
  if (props.node.rustSource) {
    highlightedRust.value = await highlightCode(props.node.rustSource, 'rust')
  }
  nextTick(emitPosition)
})

// Re-emit position when expanded changes
watch(expanded, () => nextTick(emitPosition))

function emitPosition() {
  if (!panelEl.value) return
  emit('positionUpdate', {
    x: x.value,
    y: y.value,
    width: panelEl.value.offsetWidth || props.width,
    height: panelEl.value.offsetHeight || PANEL_MIN_HEIGHT
  })
}

const panelStyle = computed(() => {
  const style: Record<string, string> = {
    left: `${x.value}px`,
    top: `${y.value}px`,
    width: `${props.width}px`
  }
  // Clamp max-height so the panel never extends below the container
  if (props.containerRef) {
    const available = props.containerRef.clientHeight - y.value - PANEL_MARGIN
    if (available > PANEL_MIN_HEIGHT) {
      style.maxHeight = `${available}px`
    }
  }
  return style
})

function getStatusColor(node: GraphNode): string {
  switch (node.status) {
    case 'verified': return '#22c55e'
    case 'externally_verified': return '#6ee7b7'
    case 'specified': return '#f59e0b'
    default: return '#9ca3af'
  }
}

function getStatusLabel(node: GraphNode): string {
  switch (node.status) {
    case 'verified': return 'Verified'
    case 'externally_verified': return 'Ext. Verified'
    case 'specified': return 'Specified'
    default: return 'Not Specified'
  }
}

function formatDocstring(raw: string): string {
  let text = raw.trim()
  if (text.startsWith('/--')) text = text.slice(3)
  if (text.endsWith('-/')) text = text.slice(0, -2)
  text = text.trim()
  text = text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
  text = text.replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>')
  text = text.replace(/`([^`]+)`/g, '<code>$1</code>')
  const lines = text.split('\n')
  let html = ''
  let inList = false
  for (const line of lines) {
    const trimmed = line.trim()
    if (trimmed.startsWith('- ')) {
      if (!inList) { html += '<ul>'; inList = true }
      html += `<li>${trimmed.slice(2)}</li>`
    } else {
      if (inList) { html += '</ul>'; inList = false }
      if (trimmed) html += `<p>${trimmed}</p>`
    }
  }
  if (inList) html += '</ul>'
  return html
}

async function copyToClipboard(text: string) {
  try {
    await navigator.clipboard.writeText(text)
  } catch (err) {
    console.error('Failed to copy:', err)
  }
}
</script>

<template>
  <div
    ref="panelEl"
    class="info-panel draggable"
    :class="{ expanded }"
    :style="panelStyle"
  >
    <!-- Drag handle header -->
    <div ref="handleEl" class="panel-header drag-handle">
      <div class="panel-title-row">
        <span class="status-dot" :style="{ backgroundColor: getStatusColor(node) }"></span>
        <span class="panel-title" :title="node.id">{{ node.label }}</span>
      </div>
      <div class="panel-actions" @pointerdown.stop>
        <button
          class="panel-btn"
          @click="emit('focusOn')"
          title="Focus in graph"
        >
          <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <circle cx="11" cy="11" r="8"/>
            <line x1="21" y1="21" x2="16.65" y2="16.65"/>
          </svg>
        </button>
        <button
          class="panel-btn close"
          @click="emit('deselect')"
          title="Close"
        >
          <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <line x1="18" y1="6" x2="6" y2="18"/>
            <line x1="6" y1="6" x2="18" y2="18"/>
          </svg>
        </button>
      </div>
    </div>

    <!-- Scrollable panel body -->
    <div class="panel-body">
      <!-- Spec statement -->
      <div v-if="node.specStatement" class="spec-section">
        <div
          v-if="highlightedSpec"
          class="spec-code-highlighted"
          v-html="highlightedSpec"
        ></div>
        <pre v-else class="spec-code">{{ node.specStatement }}</pre>
      </div>
      <div v-else class="no-spec">
        <span class="no-spec-text">{{ getStatusLabel(node) }}</span>
      </div>

      <!-- Expanded details -->
      <div v-if="expanded" class="panel-details">
        <div class="info-row">
          <span class="info-label">Name:</span>
          <code class="info-value name-value" @click="copyToClipboard(node.id)" title="Click to copy">
            {{ node.fullLabel }}
          </code>
        </div>

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

        <div v-if="node.rustSource" class="rust-source-section">
          <div class="section-label">Rust source</div>
          <div
            v-if="highlightedRust"
            class="spec-code-highlighted"
            v-html="highlightedRust"
          ></div>
          <pre v-else class="spec-code">{{ node.rustSource }}</pre>
        </div>

        <div v-if="node.specDocstring" class="docstring-section">
          <div class="docstring" v-html="formatDocstring(node.specDocstring)"></div>
        </div>
      </div>

      <!-- Expand hint -->
      <div class="expand-hint" @click="expanded = !expanded; nextTick(emitPosition)">
        <span v-if="!expanded">Details</span>
        <span v-else>Hide details</span>
        <svg
          xmlns="http://www.w3.org/2000/svg"
          width="10"
          height="10"
          viewBox="0 0 24 24"
          fill="none"
          stroke="currentColor"
          stroke-width="2"
          :class="{ rotated: expanded }"
        >
          <polyline points="6 9 12 15 18 9"/>
        </svg>
      </div>
    </div>
  </div>
</template>

<style scoped>
.info-panel.draggable {
  position: absolute;
  max-width: calc(100vw - 2rem);
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  overflow: hidden;
  pointer-events: auto;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.12);
  display: flex;
  flex-direction: column;
  resize: both;
  min-width: 280px;
  min-height: 100px;
}

.panel-body {
  flex: 1;
  overflow: auto;
  min-height: 0;
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 0.375rem 0.5rem;
  background: var(--vp-c-bg-soft);
  cursor: grab;
  user-select: none;
  touch-action: none;
  flex-shrink: 0;
}

.panel-header:active {
  cursor: grabbing;
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

/* Spec section */
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
  margin: 0;
  white-space: pre;
  color: var(--vp-c-text-1);
}

/* Shiki highlighted code container */
.spec-code-highlighted {
  font-size: 0.6875rem;
  line-height: 1.4;
  overflow-x: auto;
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

/* Rust source section in details */
.rust-source-section {
  margin-bottom: 0.5rem;
}

.section-label {
  font-size: 0.6875rem;
  color: var(--vp-c-text-3);
  margin-bottom: 0.25rem;
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
  line-height: 1.5;
}

.docstring :deep(p) {
  margin: 0 0 0.25rem;
}

.docstring :deep(p:last-child) {
  margin-bottom: 0;
}

.docstring :deep(ul) {
  margin: 0.25rem 0;
  padding-left: 1.25rem;
}

.docstring :deep(li) {
  margin-bottom: 0.125rem;
}

.docstring :deep(code) {
  font-family: 'JetBrains Mono', 'Fira Code', monospace;
  font-size: 0.625rem;
  padding: 0.0625rem 0.25rem;
  background: var(--vp-c-bg);
  border-radius: 2px;
}

.docstring :deep(strong) {
  color: var(--vp-c-text-1);
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

<script setup lang="ts">
import { ref, reactive, watch, onMounted, nextTick, type PropType } from 'vue'
import type { GraphNode } from '../../types/graph'
import { useGitHubLinks } from '../../composables/useGitHubLinks'
import { highlightCode } from '../../composables/useCodeHighlight'

const props = defineProps({
  selectedNodes: {
    type: Array as PropType<GraphNode[]>,
    required: true
  },
  containerRef: {
    type: Object as PropType<HTMLElement | null>,
    default: null
  },
  getNodeScreenPosition: {
    type: Function as PropType<(nodeId: string) => { x: number; y: number } | null>,
    default: null
  }
})

const emit = defineEmits<{
  (e: 'deselect', nodeId: string): void
  (e: 'focusOn', nodeId: string): void
  (e: 'close'): void
  (e: 'panelPositions', positions: Map<string, { x: number; y: number; width: number; height: number }>): void
}>()

const { getSourceLink } = useGitHubLinks()

// Panel sizing
const PANEL_MIN_WIDTH = 320
const PANEL_MAX_WIDTH = 700 // ~100 monospace chars at 0.6875rem
const PANEL_MIN_HEIGHT = 100
const PANEL_MARGIN = 10

// Compute panel width from longest line in spec statement
function getPanelWidth(node: GraphNode): number {
  if (!node.specStatement) return PANEL_MIN_WIDTH
  const maxLen = Math.max(...node.specStatement.split('\n').map(line => line.length))
  // ~6.6px per char at 0.6875rem monospace + ~34px horizontal padding
  const needed = maxLen * 6.6 + 34
  return Math.max(PANEL_MIN_WIDTH, Math.min(Math.ceil(needed), PANEL_MAX_WIDTH))
}

// Store panel refs and positions
const panelRefs = ref<Map<string, HTMLElement>>(new Map())
const panelPositions = reactive<Map<string, { x: number; y: number }>>(new Map())

// Drag state
const dragState = ref<{
  nodeId: string | null
  startX: number
  startY: number
  startPosX: number
  startPosY: number
} | null>(null)

// Cache of highlighted code per node
const highlightedSpecs = ref<Map<string, string>>(new Map())

// Track which panels are expanded (showing full details)
const expandedPanels = ref<Set<string>>(new Set())

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

function toggleExpanded(nodeId: string) {
  if (expandedPanels.value.has(nodeId)) {
    expandedPanels.value.delete(nodeId)
  } else {
    expandedPanels.value.add(nodeId)
  }
  // Re-emit positions after height change
  nextTick(emitPanelPositions)
}

function isExpanded(nodeId: string): boolean {
  return expandedPanels.value.has(nodeId)
}

// Get status color
function getStatusColor(node: GraphNode): string {
  switch (node.status) {
    case 'verified':
      return '#22c55e'
    case 'externally_verified':
      return '#6ee7b7'
    case 'specified':
      return '#f59e0b'
    default:
      return '#9ca3af'
  }
}

// Get status label
function getStatusLabel(node: GraphNode): string {
  switch (node.status) {
    case 'verified':
      return 'Verified'
    case 'externally_verified':
      return 'Ext. Verified'
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

// Calculate initial position for a new panel
function calculateInitialPosition(nodeId: string, existingPanels: string[]): { x: number; y: number } {
  if (!props.containerRef || !props.getNodeScreenPosition) {
    return { x: 20, y: 60 + existingPanels.length * (PANEL_MIN_HEIGHT + PANEL_MARGIN) }
  }

  const containerRect = props.containerRef.getBoundingClientRect()
  const nodePos = props.getNodeScreenPosition(nodeId)

  if (!nodePos) {
    return { x: 20, y: 60 + existingPanels.length * (PANEL_MIN_HEIGHT + PANEL_MARGIN) }
  }

  // Convert node position to container-relative coordinates
  const nodeX = nodePos.x - containerRect.left
  const nodeY = nodePos.y - containerRect.top

  // Determine which edge is closest to the node
  const distToLeft = nodeX
  const distToRight = containerRect.width - nodeX

  let x: number
  if (distToRight < distToLeft) {
    // Place on right edge
    x = containerRect.width - PANEL_MAX_WIDTH - PANEL_MARGIN
  } else {
    // Place on left edge
    x = PANEL_MARGIN
  }

  // Start with y position near the node
  let y = Math.max(PANEL_MARGIN, Math.min(nodeY - 50, containerRect.height - PANEL_MIN_HEIGHT - PANEL_MARGIN))

  // Avoid overlapping with existing panels
  const occupiedRanges: { top: number; bottom: number }[] = []
  for (const existingId of existingPanels) {
    const existingPos = panelPositions.get(existingId)
    const existingEl = panelRefs.value.get(existingId)
    if (existingPos && existingEl) {
      // Only check for overlap if on the same side
      const existingOnRight = existingPos.x > containerRect.width / 2
      const newOnRight = x > containerRect.width / 2
      if (existingOnRight === newOnRight) {
        const height = existingEl.offsetHeight || PANEL_MIN_HEIGHT
        occupiedRanges.push({ top: existingPos.y, bottom: existingPos.y + height })
      }
    }
  }

  // Sort ranges by top position
  occupiedRanges.sort((a, b) => a.top - b.top)

  // Find a non-overlapping position
  for (const range of occupiedRanges) {
    if (y < range.bottom && y + PANEL_MIN_HEIGHT > range.top) {
      // Overlap detected, move below this panel
      y = range.bottom + PANEL_MARGIN
    }
  }

  // Clamp to container bounds
  y = Math.max(PANEL_MARGIN, Math.min(y, containerRect.height - PANEL_MIN_HEIGHT - PANEL_MARGIN))

  return { x, y }
}

// Watch for new panels being added
watch(() => props.selectedNodes, (newNodes, oldNodes) => {
  const oldIds = new Set((oldNodes || []).map(n => n.id))
  const newIds = newNodes.map(n => n.id)

  // Remove positions for deselected nodes
  let removedAny = false
  for (const [id] of panelPositions) {
    if (!newIds.includes(id)) {
      panelPositions.delete(id)
      panelRefs.value.delete(id)
      removedAny = true
    }
  }

  // Notify parent when panels are removed (so connector lines get cleared)
  if (removedAny) {
    nextTick(emitPanelPositions)
  }

  // Add positions for new nodes
  const existingIds = newIds.filter(id => oldIds.has(id))
  for (const node of newNodes) {
    if (!oldIds.has(node.id) && !panelPositions.has(node.id)) {
      nextTick(() => {
        const pos = calculateInitialPosition(node.id, existingIds)
        panelPositions.set(node.id, pos)
        existingIds.push(node.id)
        nextTick(emitPanelPositions)
      })
    }
  }
}, { immediate: true })

// Store panel ref
function setPanelRef(nodeId: string, el: HTMLElement | null) {
  if (el) {
    panelRefs.value.set(nodeId, el)
    nextTick(emitPanelPositions)
  }
}

// Get position for a panel
function getPanelPosition(nodeId: string): { x: number; y: number } {
  return panelPositions.get(nodeId) || { x: 20, y: 60 }
}

// Drag handlers
function startDrag(nodeId: string, event: PointerEvent) {
  const pos = panelPositions.get(nodeId)
  if (!pos) return

  dragState.value = {
    nodeId,
    startX: event.clientX,
    startY: event.clientY,
    startPosX: pos.x,
    startPosY: pos.y
  }

  // Capture pointer for touch support
  ;(event.target as HTMLElement).setPointerCapture(event.pointerId)
}

function onDrag(event: PointerEvent) {
  if (!dragState.value) return

  const dx = event.clientX - dragState.value.startX
  const dy = event.clientY - dragState.value.startY

  let newX = dragState.value.startPosX + dx
  let newY = dragState.value.startPosY + dy

  // Clamp to container bounds
  if (props.containerRef) {
    const containerRect = props.containerRef.getBoundingClientRect()
    const dragNodeId = dragState.value.nodeId!
    const el = panelRefs.value.get(dragNodeId)
    const panelW = el?.offsetWidth || PANEL_MAX_WIDTH
    newX = Math.max(0, Math.min(newX, containerRect.width - panelW))
    newY = Math.max(0, Math.min(newY, containerRect.height - PANEL_MIN_HEIGHT))
  }

  panelPositions.set(dragState.value.nodeId!, { x: newX, y: newY })
  emitPanelPositions()
}

function endDrag(event: PointerEvent) {
  if (dragState.value) {
    ;(event.target as HTMLElement).releasePointerCapture(event.pointerId)
    dragState.value = null
  }
}

// Emit panel positions for connector lines
function emitPanelPositions() {
  const positions = new Map<string, { x: number; y: number; width: number; height: number }>()
  for (const [nodeId, pos] of panelPositions) {
    const el = panelRefs.value.get(nodeId)
    if (el) {
      positions.set(nodeId, {
        x: pos.x,
        y: pos.y,
        width: el.offsetWidth || PANEL_MIN_WIDTH,
        height: el.offsetHeight || PANEL_MIN_HEIGHT
      })
    }
  }
  emit('panelPositions', positions)
}

// Emit positions when panels mount
onMounted(() => {
  nextTick(emitPanelPositions)
})
</script>

<template>
  <div class="info-panels-container" v-if="selectedNodes.length > 0">
    <!-- Close all button (floating) -->
    <div class="close-all-floating">
      <span class="panels-count">{{ selectedNodes.length }} selected</span>
      <button class="close-all-btn" @click="emit('close')" title="Close all">
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <line x1="18" y1="6" x2="6" y2="18"/>
          <line x1="6" y1="6" x2="18" y2="18"/>
        </svg>
      </button>
    </div>

    <!-- Individual draggable panels -->
    <div
      v-for="node in selectedNodes"
      :key="node.id"
      :ref="(el) => setPanelRef(node.id, el as HTMLElement)"
      class="info-panel draggable"
      :class="{ expanded: isExpanded(node.id) }"
      :style="{ left: getPanelPosition(node.id).x + 'px', top: getPanelPosition(node.id).y + 'px', width: getPanelWidth(node) + 'px' }"
    >
      <!-- Drag handle header -->
      <div
        class="panel-header drag-handle"
        @pointerdown="(e) => startDrag(node.id, e)"
        @pointermove="onDrag"
        @pointerup="endDrag"
        @pointercancel="endDrag"
      >
        <div class="panel-title-row">
          <span class="status-dot" :style="{ backgroundColor: getStatusColor(node) }"></span>
          <span class="panel-title" :title="node.id">{{ node.label }}</span>
        </div>
        <div class="panel-actions" @pointerdown.stop>
          <a
            v-if="node.sourceFile"
            class="panel-btn source-link"
            :href="getSourceLink(node.sourceFile, node.lines || '')"
            target="_blank"
            :title="node.sourceFile.split('/').pop() + (node.lines ? ' ' + node.lines : '')"
          >
            <svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
              <path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/>
              <polyline points="15 3 21 3 21 9"/>
              <line x1="10" y1="14" x2="21" y2="3"/>
            </svg>
          </a>
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

      <!-- Expanded details -->
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
</template>

<style scoped>
.info-panels-container {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 50;
}

.close-all-floating {
  position: absolute;
  right: 1rem;
  top: 0.5rem;
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.25rem 0.5rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  pointer-events: auto;
  z-index: 60;
}

.panels-count {
  font-size: 0.75rem;
  color: var(--vp-c-text-2);
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

.info-panel.draggable {
  position: absolute;
  max-width: calc(100vw - 2rem);
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  overflow: hidden;
  pointer-events: auto;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.12);
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

.panel-btn.source-link {
  text-decoration: none;
}

.panel-btn.source-link:hover {
  color: var(--vp-c-brand-1);
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

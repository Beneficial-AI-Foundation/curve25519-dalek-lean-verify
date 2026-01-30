<template>
  <div class="extraction-diagram">
    <svg viewBox="0 0 500 320" class="diagram-svg">
      <defs>
        <!-- Arrow marker -->
        <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
          <polygon points="0 0, 10 3.5, 0 7" :fill="colors.arrow" />
        </marker>
        <!-- Dashed line marker -->
        <marker id="arrowhead-dashed" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
          <polygon points="0 0, 10 3.5, 0 7" :fill="colors.dashedArrow" />
        </marker>
      </defs>

      <!-- Extraction subgraph (dashed border) -->
      <rect
        x="20" y="20" width="200" height="200" rx="8"
        :fill="colors.subgraphBg"
        :stroke="colors.subgraphBorder"
        stroke-width="2"
        stroke-dasharray="8 4"
      />

      <!-- Rust crate (cylinder) -->
      <g transform="translate(70, 45)">
        <ellipse cx="50" cy="8" rx="40" ry="8" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <rect x="10" y="8" width="80" height="35" :fill="colors.nodeBg" :stroke="colors.nodeBg" stroke-width="0"/>
        <line x1="10" y1="8" x2="10" y2="43" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <line x1="90" y1="8" x2="90" y2="43" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <ellipse cx="50" cy="43" rx="40" ry="8" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="50" y="30" text-anchor="middle" :fill="colors.text" class="node-text">Rust crate</text>
      </g>

      <!-- Aeneas extraction (stadium/pill shape) -->
      <g transform="translate(55, 115)">
        <rect x="0" y="0" width="130" height="32" rx="16" :fill="colors.aeneasBg" :stroke="colors.aeneasBorder" stroke-width="1.5"/>
        <text x="65" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Aeneas extraction</text>
      </g>

      <!-- Funs box -->
      <g transform="translate(40, 170)">
        <rect x="0" y="0" width="70" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="35" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Funs</text>
      </g>

      <!-- Types box -->
      <g transform="translate(130, 170)">
        <rect x="0" y="0" width="70" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="35" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Types</text>
      </g>

      <!-- Dashed arrows within extraction subgraph -->
      <line x1="120" y1="98" x2="120" y2="112" :stroke="colors.dashedArrow" stroke-width="1.5" stroke-dasharray="4 3"/>
      <line x1="90" y1="150" x2="80" y2="167" :stroke="colors.dashedArrow" stroke-width="1.5" stroke-dasharray="4 3"/>
      <line x1="150" y1="150" x2="160" y2="167" :stroke="colors.dashedArrow" stroke-width="1.5" stroke-dasharray="4 3"/>

      <!-- External boxes on the right -->
      <!-- FunsExternal -->
      <g transform="translate(280, 70)">
        <rect x="0" y="0" width="100" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="50" y="21" text-anchor="middle" :fill="colors.text" class="node-text">FunsExternal</text>
      </g>

      <!-- TypesExternal -->
      <g transform="translate(280, 120)">
        <rect x="0" y="0" width="110" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="55" y="21" text-anchor="middle" :fill="colors.text" class="node-text">TypesExternal</text>
      </g>

      <!-- Defs -->
      <g transform="translate(280, 170)">
        <rect x="0" y="0" width="70" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="35" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Defs</text>
      </g>

      <!-- Aux -->
      <g transform="translate(280, 220)">
        <rect x="0" y="0" width="70" height="32" rx="4" :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="35" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Aux</text>
      </g>

      <!-- Specs (document shape) -->
      <g transform="translate(280, 270)">
        <path d="M0,4 L0,28 Q0,32 4,32 L66,32 Q70,32 70,28 L70,10 L60,0 L4,0 Q0,0 0,4 Z"
              :fill="colors.nodeBg" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <path d="M60,0 L60,10 L70,10" :fill="none" :stroke="colors.nodeBorder" stroke-width="1.5"/>
        <text x="35" y="21" text-anchor="middle" :fill="colors.text" class="node-text">Specs</text>
      </g>

      <!-- Solid arrows from Funs/Types to External -->
      <line x1="113" y1="186" x2="277" y2="90" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>
      <line x1="203" y1="186" x2="277" y2="140" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>

      <!-- Arrows from Specs to other nodes -->
      <path d="M280,286 Q240,286 160,205" :fill="none" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>
      <path d="M280,286 Q230,260 203,205" :fill="none" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>
      <line x1="315" y1="267" x2="315" y2="255" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>
      <line x1="315" y1="218" x2="315" y2="205" :stroke="colors.arrow" stroke-width="1.5" marker-end="url(#arrowhead)"/>
    </svg>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue'
import { useData } from 'vitepress'

const { isDark } = useData()

const colors = computed(() => ({
  // Node colors
  nodeBg: isDark.value ? '#1e293b' : '#ffffff',
  nodeBorder: isDark.value ? '#475569' : '#374151',
  text: isDark.value ? '#e2e8f0' : '#1f2937',

  // Aeneas node (slightly different)
  aeneasBg: isDark.value ? '#1e293b' : '#f5f5f5',
  aeneasBorder: isDark.value ? '#64748b' : '#999999',

  // Subgraph
  subgraphBg: isDark.value ? 'rgba(30, 41, 59, 0.3)' : '#f9f9f9',
  subgraphBorder: isDark.value ? '#475569' : '#999999',

  // Arrows
  arrow: isDark.value ? '#94a3b8' : '#374151',
  dashedArrow: isDark.value ? '#64748b' : '#9ca3af'
}))
</script>

<style scoped>
.extraction-diagram {
  margin: 2rem 0;
  display: flex;
  justify-content: center;
  overflow-x: auto;
}

.diagram-svg {
  max-width: 100%;
  height: auto;
  min-width: 400px;
}

.node-text {
  font-family: ui-sans-serif, system-ui, sans-serif;
  font-size: 12px;
  font-weight: 500;
}
</style>

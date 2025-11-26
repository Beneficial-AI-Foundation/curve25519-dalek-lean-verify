<template>
  <div ref="mermaidContainer" class="mermaid-container"></div>
</template>

<script setup lang="ts">
import { ref, onMounted, watch } from 'vue'
import mermaid from 'mermaid'

const props = defineProps<{
  graph: string
}>()

const mermaidContainer = ref<HTMLElement | null>(null)

const renderDiagram = async () => {
  if (!mermaidContainer.value) return

  try {
    mermaidContainer.value.innerHTML = ''
    const { svg } = await mermaid.render('mermaid-' + Math.random().toString(36).substr(2, 9), props.graph)
    mermaidContainer.value.innerHTML = svg
  } catch (error) {
    console.error('Mermaid rendering error:', error)
    mermaidContainer.value.innerHTML = '<pre>Error rendering diagram</pre>'
  }
}

onMounted(async () => {
  mermaid.initialize({
    startOnLoad: false,
    theme: 'base',
    look: 'handDrawn'
  })

  await renderDiagram()
})

watch(() => props.graph, renderDiagram)
</script>

<style scoped>
.mermaid-container {
  margin: 2rem 0;
  text-align: center;
  overflow-x: auto;
}

.mermaid-container :deep(svg) {
  max-width: 100%;
  height: auto;
}
</style>

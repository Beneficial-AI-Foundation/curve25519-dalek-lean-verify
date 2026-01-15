import { ref, watch } from 'vue'
import { createHighlighter, type Highlighter } from 'shiki'

// Singleton highlighter instance
let highlighterPromise: Promise<Highlighter> | null = null

async function getHighlighter(): Promise<Highlighter> {
  if (!highlighterPromise) {
    highlighterPromise = createHighlighter({
      themes: ['github-dark', 'github-light'],
      langs: ['lean4']
    })
  }
  return highlighterPromise
}

export function useCodeHighlight() {
  const highlightedCode = ref<string>('')
  const isLoading = ref(false)

  async function highlight(code: string, lang: string = 'lean4') {
    if (!code) {
      highlightedCode.value = ''
      return
    }

    isLoading.value = true
    try {
      const highlighter = await getHighlighter()
      highlightedCode.value = highlighter.codeToHtml(code, {
        lang,
        themes: {
          light: 'github-light',
          dark: 'github-dark'
        }
      })
    } catch (err) {
      console.error('Failed to highlight code:', err)
      // Fallback to plain text
      highlightedCode.value = `<pre><code>${escapeHtml(code)}</code></pre>`
    } finally {
      isLoading.value = false
    }
  }

  return {
    highlightedCode,
    isLoading,
    highlight
  }
}

function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;')
}

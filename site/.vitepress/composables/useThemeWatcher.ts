import { onMounted, onUnmounted } from 'vue'

export function isDarkMode(): boolean {
  if (typeof document === 'undefined') return false
  return document.documentElement.classList.contains('dark')
}

export function useThemeWatcher(onChange: () => void) {
  let observer: MutationObserver | null = null

  onMounted(() => {
    observer = new MutationObserver((mutations) => {
      for (const mutation of mutations) {
        if (mutation.attributeName === 'class') {
          onChange()
          break
        }
      }
    })
    observer.observe(document.documentElement, { attributes: true })
  })

  onUnmounted(() => {
    if (observer) {
      observer.disconnect()
      observer = null
    }
  })

  return {
    isDarkMode
  }
}

import { ref, onMounted, onUnmounted, type Ref } from 'vue'

export function useFullscreen(elementRef: Ref<HTMLElement | null>) {
  const isFullscreen = ref(false)

  function toggle() {
    if (!elementRef.value) return

    if (!document.fullscreenElement) {
      elementRef.value.requestFullscreen().catch(err => {
        console.error('Error attempting to enable fullscreen:', err)
      })
    } else {
      document.exitFullscreen()
    }
  }

  function handleFullscreenChange() {
    isFullscreen.value = !!document.fullscreenElement
  }

  onMounted(() => {
    document.addEventListener('fullscreenchange', handleFullscreenChange)
  })

  onUnmounted(() => {
    document.removeEventListener('fullscreenchange', handleFullscreenChange)
  })

  return {
    isFullscreen,
    toggle
  }
}

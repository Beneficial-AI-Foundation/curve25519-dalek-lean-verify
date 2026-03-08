import DefaultTheme from 'vitepress/theme'
import { onMounted, watch } from 'vue'
import { useRoute } from 'vitepress'
import './custom.css'
import { scheduleGraphPreload, preloadGraphNow } from '../utils/preloadGraph'

export default {
  extends: DefaultTheme,
  setup() {
    // Only run on client
    if (typeof window === 'undefined') return

    const route = useRoute()

    onMounted(() => {
      // Start preloading graph deps after page settles (3s delay)
      // Skip if we're already on the deps page
      if (route.path !== '/deps' && route.path !== '/deps.html') {
        scheduleGraphPreload(3000)
      }

      // Add hover listener to Deps nav link for immediate preload
      setupNavHoverPreload()
    })

    // Re-setup hover listener after route changes (SPA navigation)
    watch(() => route.path, () => {
      setupNavHoverPreload()
    })
  }
}

/**
 * Find the "Deps" nav link and add hover-to-preload.
 */
function setupNavHoverPreload(): void {
  // Use setTimeout to ensure DOM is ready after navigation
  setTimeout(() => {
    const navLinks = document.querySelectorAll('.VPNavBarMenuLink, .VPNavScreenMenuLink')
    navLinks.forEach(link => {
      const href = link.getAttribute('href')
      if (href?.includes('/deps')) {
        // Remove existing listener to avoid duplicates
        link.removeEventListener('mouseenter', preloadGraphNow)
        link.addEventListener('mouseenter', preloadGraphNow, { once: true })
      }
    })
  }, 100)
}
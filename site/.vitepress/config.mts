import { defineConfig } from 'vitepress'

// https://vitepress.dev/reference/site-config
export default defineConfig({
  title: "Verify curve25519-dalek",
  description: "A project to formally verify curve25519-dalek",
  base: '/curve25519-dalek-lean-verify/',
  lastUpdated: true,
  themeConfig: {
    // https://vitepress.dev/reference/default-theme-config
    nav: [
      { text: 'Home', link: '/' },
      { text: 'Project', link: '/details' },
      { text: 'Status', link: '/status' },
      { text: 'Repository', link: '/repo-structure' },
      { text: 'Trust', link: '/trust' }
    ],

    sidebar: [
      { text: 'Project Details', link: '/details' },
      { text: 'Verification Status', link: '/status' },
      { text: 'Repository Structure', link: '/repo-structure' },
      { text: 'Trust Model', link: '/trust' }
    ],

    socialLinks: [
      { icon: 'github', link: 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify' }
    ]
  }
})

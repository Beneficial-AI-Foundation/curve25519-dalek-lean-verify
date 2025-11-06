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
      { text: 'Rust API', link: '/doc/curve25519_dalek/index.html', target: '_blank' }
    ],

    socialLinks: [
      { icon: 'github', link: 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify' }
    ],

    editLink: {
      pattern: 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/edit/master/site/:path',
      text: 'Edit this page on GitHub'
    }
  }
})

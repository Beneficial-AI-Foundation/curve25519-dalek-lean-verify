import VersoManual
import VersoBlueprint.PreviewManifest
import Curve25519DalekDocs

open Verso Doc
open Verso.Genre Manual


def bpCss : CSS := CSS.mk
r#"
/* Lean syntax highlighting colors (github-light theme) */
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}
.hl.lean .keyword { color: #D73A49; }
.hl.lean .var { color: #24292E; }
.hl.lean .const { color: #6F42C1; }
.hl.lean .sort { color: #005CC5; }
.hl.lean .literal { color: #005CC5; }
.hl.lean .string { color: #032F62; }
.hl.lean .unknown { color: #24292E; }
.hl.lean .inter-text { color: #24292E; }

/* Rendered docstrings inside code blocks */
.bp_external_decl_body .docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  font-size: 0.95em;
  line-height: 1.5;
  white-space: normal;
  padding: 0.6rem 0.8rem;
  margin: 0.4rem 0 0 0;
  background: #f8fafc;
  border-left: 3px solid #6F42C1;
  border-radius: 0 4px 4px 0;
}
.bp_external_decl_body .docstring code {
  background: #eef2f7;
  padding: 0.1em 0.3em;
  border-radius: 3px;
  font-size: 0.9em;
}
.bp_external_decl_body .docstring p {
  margin: 0.3em 0;
}

/* Proof source card */
.proof-source-card {
  margin: 0.8rem 0;
  border: none;
  border-left: none;
  background: transparent;
  overflow: hidden;
}
.proof-source-card.bp_code_panel {
  border-left: none !important;
}
.proof-source-code {
  margin: 0;
  padding: 0.8rem 1rem;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.6;
  white-space: pre;
  overflow-x: auto;
  color: #24292E;
  background: var(--bp-color-surface-muted, #f8fafc);
  border-left: 3px solid #6F42C1;
  border-radius: 0 4px 4px 0;
}


/* Hide "Code for ..." cards — L∃∀N links already show declarations */
.bp_code_panel_wrapper {
  display: none !important;
}

/* Blueprint heading: "Definition 1.1 (name)" pattern */
.bp_name {
  font-weight: bold;
  font-style: italic;
  white-space: nowrap;
}
.bp_heading_title_row_statement {
  display: inline-flex !important;
  align-items: baseline;
  gap: 0.35rem;
  white-space: nowrap;
}
"#

def bpJs : JS := JS.mk
r#"
(function() {
  function onReady(fn) {
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', fn);
    } else {
      fn();
    }
  }

  /* Insert blueprint label names: "Definition 1.1" -> "Definition 1.1 (decl_name)" */
  onReady(function() {
    document.querySelectorAll('.bp_heading_title_row_statement').forEach(function(row) {
      if (row.querySelector('.bp_name')) return;
      var caption = row.querySelector('.bp_caption[title]');
      if (!caption) return;
      var name = caption.getAttribute('title');
      if (!name || name.length === 0) return;
      var nameSpan = document.createElement('span');
      nameSpan.className = 'bp_name';
      nameSpan.textContent = '(' + name + ')';
      row.appendChild(nameSpan);
    });
  });

  /* Render markdown in docstrings (requires marked.js, optional) */
  onReady(function() {
    if (typeof marked !== 'undefined') {
      document.querySelectorAll('pre.docstring, code.docstring').forEach(function(el) {
        if (el.dataset.rendered) return;
        if (el.closest('.hover-info')) return;
        el.dataset.rendered = '1';
        var text = el.innerText;
        if (!text || !text.trim()) return;
        var html = marked.parse(text);
        var rendered = document.createElement('div');
        rendered.className = 'docstring';
        rendered.innerHTML = html;
        el.parentNode.replaceChild(rendered, el);
      });
    }
  });

  /* Set modern style by default */
  onReady(function() {
    document.documentElement.setAttribute('data-bp-style', 'modern');
  });

  /* Enhance proof cards: rename captions, extract source, add L∃∀N preview */
  onReady(function() {
    var markerText = '-- PROOF-SOURCE';
    var proofSourcesByTitle = {};
    /* Extract and highlight proof source blocks */
    var allPres = document.querySelectorAll('pre');
    for (var i = allPres.length - 1; i >= 0; i--) {
      var el = allPres[i];
      var text = el.textContent || '';
      if (text.trimStart().indexOf(markerText) !== 0) continue;
      var idx = text.indexOf(markerText);
      var rest = text.substring(idx + markerText.length);
      var nlIdx = rest.indexOf('\n');
      var code = nlIdx >= 0 ? rest.substring(nlIdx + 1) : rest;
      var html = code.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
      html = html.replace(/(--[^\n]*)/g, '<span style="color:#6A737D">$1</span>');
      html = html.replace(/\b(by|cases|simp|exact|subst|rw|rewrite|apply|intro|intros|have|show|suffices|induction|constructor|refine|calc|ring|omega|norm_num|linarith|aesop|trivial|contradiction|exfalso|congr|ext|funext|sorry|with|match|fun|let|do|if|then|else|for|in|return|pure|try|catch|throw|unless|where|only|guard|logInfo|throwError)\b/g, '<span style="color:#D73A49">$1</span>');
      html = html.replace(/\b(none|some|true|false)\b/g, '<span style="color:#005CC5">$1</span>');
      html = html.replace(/(\|) /g, '<span style="color:#D73A49">$1</span> ');
      var prev = el.previousElementSibling;
      while (prev) {
        if (prev.classList && prev.classList.contains('bp_kind_proof_wrapper')) {
          proofSourcesByTitle[prev.getAttribute('title') || ''] = html;
          break;
        }
        prev = prev.previousElementSibling;
      }
      el.parentNode.removeChild(el);
    }
    /* Enhance proof blocks */
    document.querySelectorAll('.bp_kind_proof_wrapper').forEach(function(proofEl) {
      var prev = proofEl.previousElementSibling;
      var theoremLabel = '';
      while (prev) {
        if (prev.classList && (prev.classList.contains('bp_kind_theorem_wrapper') ||
            prev.classList.contains('bp_kind_definition_wrapper') ||
            prev.classList.contains('bp_kind_lemma_wrapper'))) {
          var cap = prev.querySelector('.bp_caption');
          var lab = prev.querySelector('.bp_label');
          if (cap && lab) theoremLabel = cap.textContent.trim() + ' ' + lab.textContent.trim();
          break;
        }
        if (prev.classList && (prev.classList.contains('bp_kind_proof_wrapper') ||
            prev.classList.contains('bp_code_panel_wrapper'))) {
          prev = prev.previousElementSibling; continue;
        }
        prev = prev.previousElementSibling;
      }
      if (theoremLabel) {
        var proofCaption = proofEl.querySelector('.bp_kind_proof_caption');
        if (proofCaption) proofCaption.textContent = 'Proof for ' + theoremLabel;
      }
      var sourceHtml = proofSourcesByTitle[proofEl.getAttribute('title') || ''];
      if (!sourceHtml) return;
      var heading = proofEl.querySelector('.bp_kind_proof_heading');
      if (!heading) return;
      var proofId = 'bp-proof-source-' + (proofEl.getAttribute('title') || 'unknown');
      var extras = document.createElement('div');
      extras.className = 'bp_extras thm_header_extras';
      var slot = document.createElement('span');
      slot.className = 'bp_extra_slot bp_extra_slot_code';
      var root = document.createElement('span');
      root.className = 'bp_code_summary_preview_root';
      var wrap = document.createElement('span');
      wrap.className = 'bp_code_summary_preview_wrap bp_code_summary_preview_wrap_active';
      wrap.setAttribute('data-bp-preview-id', proofId);
      wrap.setAttribute('data-bp-preview-title', theoremLabel ? 'Proof for ' + theoremLabel : 'Proof');
      wrap.setAttribute('tabindex', '0');
      wrap.setAttribute('role', 'button');
      wrap.setAttribute('aria-label', 'Proof source');
      wrap.innerHTML = '<span class="bp_code_link bp_code_link_status bp_code_link_status_proved" title="Proof source"><span class="bp_code_status_symbol">✓</span><span class="bp_code_link_label">L∃∀N</span></span>';
      var tpl = document.createElement('template');
      tpl.className = 'bp_code_summary_preview_tpl';
      tpl.setAttribute('data-bp-preview-id', proofId);
      tpl.innerHTML = '<div class="bp_code_summary_preview_content"><pre class="proof-source-code" style="margin:0">' + sourceHtml + '</pre></div>';
      var aside = document.createElement('aside');
      aside.className = 'bp_code_summary_preview_panel bp_preview_panel';
      aside.setAttribute('data-bp-preview-mode', 'hover');
      aside.setAttribute('data-bp-preview-placement', 'anchored');
      aside.setAttribute('hidden', '');
      aside.innerHTML = '<div class="bp_code_summary_preview_header bp_preview_panel_header"><div class="bp_code_summary_preview_title bp_preview_panel_title"></div><button type="button" class="bp_code_summary_preview_close bp_preview_panel_close" aria-label="Close">Close</button></div><div class="bp_code_summary_preview_body bp_preview_panel_body"></div>';
      root.appendChild(wrap);
      root.appendChild(tpl);
      root.appendChild(aside);
      slot.appendChild(root);
      extras.appendChild(slot);
      heading.appendChild(extras);
    });
    /* Re-run blueprint's preview binding on newly created elements */
    document.querySelectorAll('.bp_code_summary_preview_root').forEach(function(root) {
      if (root.getAttribute('data-bp-code-summary-preview-bound') === '1') return;
      if (window.bpPreviewUtils && typeof window.bpPreviewUtils.bindTemplatePreview === 'function') {
        var panel = root.querySelector('.bp_code_summary_preview_panel');
        if (!panel) return;
        root.setAttribute('data-bp-code-summary-preview-bound', '1');
        window.bpPreviewUtils.bindTemplatePreview({
          root: root,
          previewRoot: root,
          triggerRoot: root,
          panel: panel,
          templateSelector: 'template.bp_code_summary_preview_tpl[data-bp-preview-id]',
          triggerSelector: '.bp_code_summary_preview_wrap_active[data-bp-preview-id]',
          keyAttr: 'data-bp-preview-id',
          titleAttr: 'data-bp-preview-title',
          titleSelector: '.bp_code_summary_preview_title',
          bodySelector: '.bp_code_summary_preview_body',
          closeSelector: '.bp_code_summary_preview_close',
          triggerBoundAttr: 'data-bp-code-summary-trigger-bound',
          defaults: { mode: 'hover', placement: 'anchored' }
        });
      }
    });
  });

  /* Suppress empty Tippy tooltips */
  onReady(function() {
    document.querySelectorAll('.hover-info').forEach(function(el) {
      var text = el.textContent.trim();
      if (!text) el.remove();
    });
  });
})();
"#


def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc Curve25519DalekDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlConfig := {
        extraCss := [bpCss]
        extraJs := [bpJs]
      }
    })

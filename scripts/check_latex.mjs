#!/usr/bin/env node
// Docstring mathematics is LaTeX: every `$...$` and `$$...$$` span in a declaration docstring
// (/-- ... -/) or module docstring (/-! ... -/) of NLAlib/ and NLAlibScaffold/ parses and renders
// under KaTeX (the renderer used by the doc site), and no docstring has an unclosed `$`.
// Backtick code spans, fenced code blocks and `\$` are not math. A line inside a `$$` display may
// not start with Markdown block syntax (`- `, `+ `, `* `, `#`, `>`, `1. `), which doc-gen4 would
// read as a list, heading or quote and so split the formula. This checks syntax, not meaning:
// a formula that renders can still be the wrong formula.
//
// Usage: node scripts/check_latex.mjs [root]    (root defaults to the repository root)
// Needs `katex` resolvable from Node (CI: npm install --no-save --no-package-lock katex@0.16.22).
// KaTeX runs with strict 'error' except for unicodeTextInMathMode (Unicode such as `ε` in math
// is accepted; KaTeX renders it fine). Exit 1 if any problem is found.
import katex from 'katex';
import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(process.argv[2] ?? join(dirname(fileURLToPath(import.meta.url)), '..'));
const strict = (code) => (code === 'unicodeTextInMathMode' ? 'ignore' : 'error');

function* leanFiles(dir) {
  let entries;
  try { entries = readdirSync(dir, { withFileTypes: true }); } catch { return; }
  entries.sort((a, b) => (a.name < b.name ? -1 : 1));
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) yield* leanFiles(p);
    else if (e.name.endsWith('.lean')) yield p;
  }
}

// Docstrings of a Lean source: [{start, end}] offsets of the body (after `/--` or `/-!`, before `-/`).
// Ordinary (possibly nested) block comments `/- ... -/` are skipped as a whole.
function docstrings(src) {
  const out = [];
  let i = 0;
  while (i < src.length) {
    if (src.startsWith('/-', i)) {
      const doc = src[i + 2] === '-' || src[i + 2] === '!';
      if (doc) {
        const end = src.indexOf('-/', i + 3);
        const stop = end < 0 ? src.length : end;
        out.push({ start: i + 3, end: stop });
        i = stop + 2;
      } else {
        let depth = 1;
        i += 2;
        while (i < src.length && depth > 0) {
          if (src.startsWith('/-', i)) { depth++; i += 2; }
          else if (src.startsWith('-/', i)) { depth--; i += 2; }
          else i++;
        }
      }
    } else if (src.startsWith('--', i)) {
      const nl = src.indexOf('\n', i);
      i = nl < 0 ? src.length : nl;
    } else i++;
  }
  return out;
}

// Math spans of a docstring body: [{offset, tex, display}] and unclosed [{offset}].
function mathSpans(s) {
  const spans = [], unclosed = [];
  let i = 0, lineStart = true, fence = false;
  while (i < s.length) {
    if (lineStart && /^[ \t]*(```|~~~)/.test(s.slice(i, i + 80))) {
      fence = !fence;
      const nl = s.indexOf('\n', i);
      i = nl < 0 ? s.length : nl + 1;
      continue;
    }
    if (fence) {
      const nl = s.indexOf('\n', i);
      i = nl < 0 ? s.length : nl + 1;
      continue;
    }
    const c = s[i];
    lineStart = c === '\n';
    if (c === '\\') { i += 2; continue; }
    if (c === '`') {
      let n = 0;
      while (s[i + n] === '`') n++;
      let j = i + n, close = -1;
      while (j < s.length) {
        if (s[j] === '`') {
          let m = 0;
          while (s[j + m] === '`') m++;
          if (m === n) { close = j; break; }
          j += m;
        } else j++;
      }
      i = close < 0 ? i + n : close + n;
      continue;
    }
    if (c === '$') {
      const display = s[i + 1] === '$';
      const open = display ? 2 : 1;
      let j = i + open, close = -1;
      while (j < s.length) {
        if (s[j] === '\\') { j += 2; continue; }
        if (s[j] === '$' && (!display || s[j + 1] === '$')) { close = j; break; }
        j++;
      }
      if (close < 0) { unclosed.push({ offset: i }); break; }
      spans.push({ offset: i, tex: s.slice(i + open, close), display });
      i = close + open;
      continue;
    }
    i++;
  }
  return { spans, unclosed };
}

const excerpt = (t) => {
  const one = t.replace(/\s+/g, ' ').trim();
  return one.length > 60 ? one.slice(0, 57) + '...' : one;
};

let ndoc = 0, nmath = 0, bad = 0;
for (const lib of ['NLAlib', 'NLAlibScaffold']) {
  for (const file of leanFiles(join(root, lib))) {
    const src = readFileSync(file, 'utf8');
    const rel = file.startsWith(root + '/') ? file.slice(root.length + 1) : file;
    const lineOf = (off) => src.slice(0, off).split('\n').length;
    for (const { start, end } of docstrings(src)) {
      ndoc++;
      const { spans, unclosed } = mathSpans(src.slice(start, end));
      for (const u of unclosed) {
        const rest = src.slice(start + u.offset, end);
        console.log(`${rel}:${lineOf(start + u.offset)}: unclosed '$' in docstring (${excerpt(rest)})`);
        bad++;
      }
      for (const sp of spans) {
        nmath++;
        // a line of a display must not start like a Markdown block (list item, heading, quote,
        // numbered item), or doc-gen4 splits the formula before KaTeX sees it
        if (sp.display) {
          const lines = sp.tex.split('\n').slice(1);
          lines.forEach((line, k) => {
            if (/^\s*([-+*]\s|#|>|\d+[.)]\s)/.test(line)) {
              const at = start + sp.offset + 2 + sp.tex.split('\n').slice(0, k + 1).join('\n').length;
              console.log(`${rel}:${lineOf(at + 1)}: display line starts with Markdown syntax (${excerpt(line)})`);
              bad++;
            }
          });
        }
        try {
          katex.renderToString(sp.tex, { throwOnError: true, strict, displayMode: sp.display });
        } catch (e) {
          const msg = String(e.message ?? e).split('\n')[0];
          console.log(`${rel}:${lineOf(start + sp.offset)}: ${msg} (${excerpt(sp.tex)})`);
          bad++;
        }
      }
    }
  }
}
console.log(`${ndoc} docstrings, ${nmath} math spans checked; ${bad} problems`);
process.exit(bad ? 1 : 0);

#!/usr/bin/env node
// Full-CLI regressions: shared Lean lexical fixtures must expose real math and hide fake docs.
// Run after installing the checker's KaTeX dependency: node --test scripts/test_check_latex.mjs.
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const scripts = dirname(fileURLToPath(import.meta.url));
const fixtures = JSON.parse(readFileSync(join(scripts, 'fixtures', 'lean_docstrings.json'), 'utf8'));

function check(source) {
  const root = mkdtempSync(join(tmpdir(), 'nlalib-latex-'));
  try {
    mkdirSync(join(root, 'NLAlib'));
    writeFileSync(join(root, 'NLAlib', 'Example.lean'), source, 'utf8');
    const result = spawnSync(process.execPath, [join(scripts, 'check_latex.mjs'), root], {
      encoding: 'utf8', timeout: 20_000,
    });
    assert.ifError(result.error);
    assert.equal(result.signal, null);
    return result;
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

for (const fixture of fixtures) {
  test(fixture.name, () => {
    const good = check(fixture.source);
    assert.equal(good.status, 0, good.stdout + good.stderr);
    assert.match(good.stdout, new RegExp(
      `${fixture.docs.length} docstrings, ${fixture.math_spans} math spans checked; 0 problems`));

    const bad = check(fixture.source.replaceAll('$x$', '$\\notARealMacro$'));
    assert.equal(bad.status, 1, bad.stdout + bad.stderr);
    assert.match(bad.stdout, /Undefined control sequence: \\notARealMacro/);
    assert.match(bad.stdout, new RegExp(
      `${fixture.docs.length} docstrings, ${fixture.math_spans} math spans checked; ` +
      `${fixture.math_spans} problems`));
  });
}

test('unclosed math after a nested comment is rejected', () => {
  const result = check('/-- After `/- inner -/`, an unclosed $x. -/\ndef x := 1\n');
  assert.equal(result.status, 1, result.stdout + result.stderr);
  assert.match(result.stdout, /unclosed '\$' in docstring/);
});

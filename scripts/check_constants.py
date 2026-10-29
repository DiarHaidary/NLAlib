#!/usr/bin/env python3
"""Named bounds show their current value in every docstring that uses them (CONTRIBUTING §5.2).

The registry `docs/constants.toml` has one `[[constant]]` entry per named constant, tail function
or sample size of the library: its Lean `name`, `kind`, `file`, explicit `args` (Lean order),
`latex` (a template of its value with positional placeholders `#1`, `#2`, ... for the arguments),
optionally `display` (the same value with `\\frac`, for `$$…$$` displays), `lean_body` (the
definition's text from its name to its end, whitespace-normalised) and `body_hash` (sha256 of
`lean_body`, 16 hex digits).

In a docstring (`/-- … -/` or `/-! … -/`) of NLAlib/ or NLAlibScaffold/ the value is written inline,
inside the equation, in place of the constant, and the math span is annotated by a value marker
placed immediately before it:

    <!-- value gaussianPinvSpecNormBound k \\ell -->
    $$\\|\\mathbf{A} - \\mathsf{rsvd}(\\mathbf{A}, \\mathbf{X})\\|_2 \\le … +
    \\frac{e}{\\ell - k}\\sqrt{(\\ell + k - 1)/2}\\,\\|\\mathbf{A} - …\\|_{\\mathsf{F}}$$

The marker holds the constant's name (with or without `NLAlib.`), then one LaTeX argument per Lean
argument, separated by spaces. An argument containing a space is wrapped in braces,
`{\\lvert r \\rvert}`, which are dropped on substitution; arguments are substituted verbatim
otherwise, so write `(\\varepsilon/2)` where precedence needs parentheses. Arguments contain no `$`,
backtick or `--`. Only whitespace (at most one line break) separates the marker from its span
(`$…$` on one line, or `$$…$$`); several markers may precede one span, one per constant in it. There
is no closing marker, and a marker never begins a line: Markdown reads a line that starts with
`<!--` as an HTML block, which ends the paragraph, so the marker follows the text before it on its
line ("… and $t > 0$, <!-- value … -->" then the display). The markers are HTML comments:
doc-gen4's Markdown hides them, the explorer's build strips them and scripts/check_latex.mjs skips
them.

The annotated span must contain the filled template: `latex` with `#i` replaced by the i-th
argument, or, in a `$$…$$` display, also `display` filled. The comparison ignores whitespace (a
display may break the value across lines, and `\\log 2` matches `\\log2`) and requires a token
boundary at both ends (the value `2` does not match inside `12`). Around it the docstring may add
grouping, `\\bigl(…\\bigr)` or `{…}`, where the surrounding expression needs it.

The check fails if
  * a definition's `lean_body` or `body_hash` differs from the source (the body changed: update
    `latex`, then run `--update NAME`), or its explicit arguments differ from `args`;
  * an annotated span does not contain its filled template, a marker has the wrong number of
    arguments, names an unregistered constant, or is not followed by a math span;
  * an entry still has `previous_latex`/`previous_display` (an update is pending);
  * a docstring names a registered constant in backticks without a value marker of it (unless it
    carries the opt-out `<!-- mention NAME -->`, for a name mentioned only in passing; keep rare);
  * a definition's own docstring has no value marker of it;
  * a marker begins a line (after indentation and a list bullet);
  * a marker line or a line of an annotated span exceeds 100 characters.

Changing a value. Edit the Lean body; in the registry move the old `latex` (and `display`) to
`previous_latex` (and `previous_display`) and write the new ones; run `--update NAME`. In every span
annotated for NAME it replaces the previous filled value by the new one, in the same form (inline
by `latex`, display by `display` or `latex`), at every occurrence in the span; a short previous
value (under 5 non-blank characters, such as `2` or `1/64`) only when it occurs exactly once per
marker of it on the span, so that an unrelated `2` is never rewritten. Only the characters that
differ are replaced, so the line breaks of a display survive. It then records the new `lean_body`
and `body_hash` and removes the `previous_*` fields once every span is rewritten. A span where the
previous value is missing or ambiguous is reported and left for a hand edit (rerun after fixing:
spans already holding the new value are skipped). The previous template lives in the registry
rather than being recovered from git, so that the update works on any copy, before or after a
commit.

Usage:
  python3 scripts/check_constants.py              check; one summary line on success
  python3 scripts/check_constants.py --update NAME [NAME ...]
                                                  rewrite NAME's values in the annotated spans
                                                  from `previous_*`, record its current
                                                  `lean_body` and `body_hash`
  --root DIR                                      run on another copy of the repository
Exit status 1 on any problem.
"""
import argparse
import hashlib
import re
import sys
import tomllib
from pathlib import Path

LIBS = ("NLAlib", "NLAlibScaffold")
MAX_LINE = 100
MARK = re.compile(r"<!-- value (?P<name>[^\s>]+)(?P<args>(?: [^\n]*?)?) -->")
MARK_ANY = re.compile(r"<!--\s*/?\s*value\b")
OPT_OUT = re.compile(r"<!-- mention (\S+) -->")
PLACEHOLDER = re.compile(r"#([1-9])")
CODE = re.compile(r"(`+)(.+?)\1", re.S)
GAP = re.compile(r"[ \t]*\n?[ \t]*")
SHORT = 5   # a shorter previous value is replaced only once per marker of it on the span
LINE_START = re.compile(r"[ \t]*(?:(?:[*+-]|\d+[.)])[ \t]+)?")
RAW_STRING = re.compile(r"(?<![\w'!?.»\u2070-\u209f\u2100-\u214f])r(#*)\"")
CHAR_LITERAL = re.compile(
    r"(?<![\w'!?.»\u2070-\u209f\u2100-\u214f])"
    r"'(?:[^'\\\n]|\\(?:[nrt\\\"']|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'")


def short(name):
    return name[len("NLAlib."):] if name.startswith("NLAlib.") else name


def docstrings(src, *, regions=None):
    """(start, end) offsets of every docstring body, as in scripts/check_latex.mjs: after `/--` or
    `/-!`, before its matching `-/`. Both kinds of block comment nest, even inside Markdown
    code spans. Outside comments, skip quoted identifiers and regular/raw strings so their
    comment markers are not mistaken for Lean comments. Optionally collect opaque regions as
    (start, end, kind), for definition-boundary detection. This bounded lexer does not parse
    arbitrary syntax extensions or interpolated terms."""
    out, i, n = [], 0, len(src)
    while i < n:
        region_start, kind = i, None
        if src.startswith("/-", i):
            kind = "comment"
            doc = i + 2 < n and src[i + 2] in "-!"
            start = i + 3
            depth, i = 1, i + (3 if doc else 2)
            while i < n and depth:
                if src.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if doc:
                out.append((start, i - 2 if depth == 0 else n))
        elif src.startswith("--", i):
            kind = "comment"
            nl = src.find("\n", i)
            i = n if nl < 0 else nl
        elif src[i] == "«":
            kind = "literal"
            end = src.find("»", i + 1)
            i = n if end < 0 else end + 1
        elif src[i] == "r" and (raw := RAW_STRING.match(src, i)):
            kind = "literal"
            close = '"' + raw.group(1)
            end = src.find(close, raw.end())
            i = n if end < 0 else end + len(close)
        elif src[i] == '"':
            kind = "literal"
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                elif src[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif src[i] == "'" and (char := CHAR_LITERAL.match(src, i)):
            kind = "literal"
            i = char.end()
        else:
            i += 1
        if regions is not None and kind:
            regions.append((region_start, min(i, n), kind))
    return out


def split_args(s):
    out, cur, depth = [], "", 0
    for ch in s.strip():
        if ch.isspace() and depth == 0:
            if cur:
                out.append(cur)
                cur = ""
            continue
        depth += (ch == "{") - (ch == "}")
        cur += ch
    if cur:
        out.append(cur)
    return [a[1:-1] if a.startswith("{") and a.endswith("}") and balanced(a[1:-1]) else a
            for a in out]


def balanced(s):
    depth = 0
    for ch in s:
        depth += (ch == "{") - (ch == "}")
        if depth < 0:
            return False
    return depth == 0


GREEK = {"ε": r"\varepsilon", "δ": r"\delta", "ℓ": r"\ell", "λ": r"\lambda", "σ": r"\sigma"}


def fill(template, args):
    return PLACEHOLDER.sub(lambda m: args[int(m.group(1)) - 1], template)


def forms(c, args, display, prefix=""):
    """[(kind, filled value)] a span may hold: `latex` always, `display` in a display."""
    out = [("latex", fill(c[prefix + "latex"], args))] if (prefix + "latex") in c else []
    if display and (prefix + "display") in c:
        out.append(("display", fill(c[prefix + "display"], args)))
    return out


def example(name, c):
    """A value marker of `name` with the definition's argument letters, for messages."""
    args = [GREEK.get(a, a) for a in c["args"]]
    return (f"`<!-- value {' '.join([name] + args)} -->` before the equation, which shows "
            f"`{fill(c['latex'], args)}` in place of the constant")


def value_regex(value):
    """Regex for `value` ignoring whitespace, with a token boundary at each end."""
    chars = [ch for ch in value if not ch.isspace()]
    body = r"\s*".join(re.escape(ch) for ch in chars)
    head = r"(?<![0-9.])" if chars[0].isdigit() else ""
    if chars[-1].isdigit():
        tail = r"(?![0-9.])"
    elif re.search(r"\\[A-Za-z]+$", "".join(chars)):
        tail = r"(?![A-Za-z])"
    else:
        tail = ""
    return re.compile(head + body + tail)


def occurrences(span, value):
    """Matches of `value` in `span` (whitespace-insensitive), dropping those that start inside a
    control word (`e` of `\\ell`) or right after a letter when the value starts with a digit."""
    out = []
    for m in value_regex(value).finditer(span):
        k = m.start()
        if value.lstrip()[:1].isalpha():
            j = k
            while j > 0 and span[j - 1].isalpha():
                j -= 1
            if j > 0 and span[j - 1] == "\\":
                continue
        out.append(m)
    return out


def minimal_edit(text, start, end, new):
    """(start, end, replacement) turning `text[start:end]`, a whitespace-insensitive occurrence of
    the previous value, into `new`, replacing only the part between the longest common prefix and
    suffix of non-whitespace characters, so that the line breaks of a display survive."""
    pos = [k for k in range(start, end) if not text[k].isspace()]
    old = [text[k] for k in pos]
    npos = [k for k, ch in enumerate(new) if not ch.isspace()]
    nchr = [new[k] for k in npos]
    p = 0
    while p < min(len(old), len(nchr)) and old[p] == nchr[p]:
        p += 1
    s = 0
    while s < min(len(old), len(nchr)) - p and old[-1 - s] == nchr[-1 - s]:
        s += 1
    a = pos[p] if p < len(old) - s else (pos[p - 1] + 1 if p else start)
    b = pos[len(old) - s - 1] + 1 if p < len(old) - s else a
    na = npos[p] if p < len(nchr) - s else (npos[p - 1] + 1 if p else 0)
    nb = npos[len(nchr) - s - 1] + 1 if p < len(nchr) - s else na
    return a, b, new[na:nb]


def math_span(doc, pos):
    """(start, end, display) of the math span starting at `pos`, or None."""
    if doc.startswith("$$", pos):
        j = pos + 2
        while j < len(doc):
            if doc[j] == "\\":
                j += 2
                continue
            if doc.startswith("$$", j):
                return pos, j + 2, True
            j += 1
        return None
    if doc.startswith("$", pos):
        j = pos + 1
        while j < len(doc) and doc[j] != "\n":
            if doc[j] == "\\":
                j += 2
                continue
            if doc[j] == "$":
                return pos, j + 1, False
            j += 1
    return None


def annotated(doc):
    """[(marker match, span or None)]: each value marker and the math span it annotates."""
    out, marks = [], list(MARK.finditer(doc))
    for k, m in enumerate(marks):
        pos = m.end()
        while True:
            g = GAP.match(doc, pos)
            pos = g.end()
            nxt = MARK.match(doc, pos)
            if nxt:
                pos = nxt.end()
                continue
            break
        out.append((m, math_span(doc, pos)))
    return out


def find_definition(src, name):
    """(offset, normalised text from the name to the end) of `def`/`irreducible_def NAME`: its first
    line and its indented body, including blank lines and declaration continuations. Comments
    and literal contents cannot end the body or supply a fake definition. Like the library's
    source format, other commands begin at no greater indentation; this is not a Lean parser."""
    regions = []
    docstrings(src, regions=regions)
    masked = list(src)
    for start, end, kind in regions:
        for i in range(start, end):
            if src[i] not in "\r\n":
                masked[i] = " "
        if kind == "literal":
            masked[start] = "_"  # a literal is code; a comment is whitespace
    code = "".join(masked)
    m = re.search(rf"^(?:[\w@\[\] ]*?)(?:irreducible_def|def|abbrev) ({re.escape(name)})(?![\w'])",
                  code, re.M)
    if not m:
        return None, None
    indent = len(m.group()) - len(m.group().lstrip())
    first_end = src.find("\n", m.end())
    if first_end < 0:
        first_end = len(src)
    end, offset = first_end, first_end + 1
    continuations = re.compile(r"(?:where\b|termination_by\b|decreasing_by\b|\|)")
    for line in code[offset:].splitlines(keepends=True):
        line_end = offset + len(line)
        # A multiline string or quoted identifier may contain outdented lines.
        in_literal = any(kind == "literal" and a < offset < b for a, b, kind in regions)
        offset = line_end
        if in_literal:
            end = line_end
            continue
        if not line.strip():
            continue
        if (len(line) - len(line.lstrip()) <= indent and
                not continuations.match(line.lstrip())):
            break
        end = line_end
    return m.start(), " ".join(src[m.start(1):end].split())


def explicit_args(lean_body):
    header = lean_body.split(":=")[0]
    names = []
    for group in re.findall(r"\(([^():]+):", header):
        names += group.split()
    return names


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def line_of(src, off):
    return src.count("\n", 0, off) + 1


def run(root, update_names):
    registry_path = root / "docs" / "constants.toml"
    registry = tomllib.loads(registry_path.read_text())["constant"]
    by_name = {short(c["name"]): c for c in registry}
    problems = []

    # 1. the registry against the definitions
    def_docs = {}   # (file, docstring start) -> short name, for the definition's own docstring
    current = {}    # short name -> (lean_body, hash) in the source
    for name, c in by_name.items():
        if name not in update_names:
            for f in ("previous_latex", "previous_display"):
                if f in c:
                    problems.append(f"docs/constants.toml: {c['name']} has `{f}`: an update is "
                                    f"pending; run `python3 scripts/check_constants.py --update "
                                    f"{name}`")
        path = root / c["file"]
        src = path.read_text() if path.exists() else ""
        # a constant in a sub-namespace (`NLAlib.Computation.roundingFactor`) is defined by its
        # last component inside `namespace NLAlib.Computation`
        off, body = find_definition(src, name.rsplit(".", 1)[-1])
        if body is None:
            problems.append(f"{c['file']}: definition of {c['name']} not found (docs/constants.toml)")
            continue
        current[name] = (body, digest(body))
        own = [d for d in docstrings(src) if d[1] < off and not src[d[1] + 2:off].strip()]
        if own:
            def_docs[(c["file"], own[-1][0])] = name
        else:
            problems.append(f"{c['file']}:{line_of(src, off)}: {c['name']} has no docstring")
        if name not in update_names and (body != c["lean_body"] or digest(body) != c["body_hash"]):
            problems.append(
                f"{c['file']}:{line_of(src, off)}: the body of {c['name']} changed.\n"
                f"  registry: {c['lean_body']}\n  source:   {body}\n"
                f"  In docs/constants.toml move `latex` to `previous_latex` (and `display` to "
                f"`previous_display`), write the new value, then run "
                f"`python3 scripts/check_constants.py --update {name}`.")
        if explicit_args(body) != c["args"]:
            problems.append(f"{c['file']}: explicit arguments of {c['name']} are "
                            f"{explicit_args(body)}, registry has {c['args']}")
        for field in ("latex", "display"):
            if field not in c:
                continue
            for m in PLACEHOLDER.finditer(c[field]):
                if int(m.group(1)) > len(c["args"]):
                    problems.append(f"docs/constants.toml: {c['name']}: placeholder #{m.group(1)} "
                                    f"beyond its {len(c['args'])} arguments")
            if re.search(r"#[1-9][A-Za-z]", c[field]):
                problems.append(f"docs/constants.toml: {c['name']}: a placeholder is followed by "
                                "a letter; an argument like `\\ell` would merge with it")
    unknown = set(update_names) - set(by_name)
    if unknown:
        problems.append(f"--update: not in the registry: {', '.join(sorted(unknown))}")
        update_names = [n for n in update_names if n in by_name]
    pending = {n for n in update_names
               if "previous_latex" in by_name[n] or "previous_display" in by_name[n]}
    unfinished = set()  # names with a span the update could not rewrite

    # 2. the docstrings
    mention = {n: re.compile(rf"(?<![\w'.])(?:NLAlib\.)?{re.escape(n)}(?![\w'!?])") for n in by_name}
    ndoc = nmark = nspan = nrewritten = 0
    for lib in LIBS:
        for path in sorted((root / lib).rglob("*.lean")):
            src = path.read_text()
            rel = path.relative_to(root).as_posix()
            out, last, changed = [], 0, False
            span_lines = set()
            for start, end in docstrings(src):
                doc = src[start:end]
                ndoc += 1
                edits = []   # (start, end, replacement) in doc
                spans_seen = set()
                updated = set()   # (span, name, args) already rewritten
                for m, sp in annotated(doc):
                    nmark += 1
                    at = f"{rel}:{line_of(src, start + m.start())}"
                    span_lines.add(line_of(src, start + m.start()))
                    name, args = short(m.group("name")), split_args(m.group("args"))
                    bol = doc.rfind("\n", 0, m.start()) + 1
                    if LINE_START.fullmatch(doc[bol:m.start()]):
                        problems.append(f"{at}: the value marker of {name} begins a line; "
                                        "Markdown reads such a line as an HTML block, which ends "
                                        "the paragraph: put the marker after the text before it")
                    c = by_name.get(name)
                    if c is None:
                        problems.append(f"{at}: value marker of unregistered constant {name}")
                        continue
                    if len(args) != len(c["args"]):
                        problems.append(f"{at}: {name} takes {len(c['args'])} arguments "
                                        f"({' '.join(c['args'])}), marker has {len(args)}")
                        continue
                    if re.search(r"--|\$|`", m.group("args")):
                        problems.append(f"{at}: marker arguments may not contain `--`, `$` or "
                                        "a backtick")
                        continue
                    if sp is None:
                        problems.append(f"{at}: the value marker of {name} is not followed by a "
                                        "math span (`$…$` on one line, or `$$…$$`), with only "
                                        "whitespace and other value markers between")
                        continue
                    s0, s1, display = sp
                    if (s0, s1) not in spans_seen:
                        spans_seen.add((s0, s1))
                        nspan += 1
                        span_lines.update(range(line_of(src, start + s0),
                                                line_of(src, start + s1) + 1))
                    inner0, inner1 = s0 + (2 if display else 1), s1 - (2 if display else 1)
                    tex = doc[inner0:inner1]
                    want = forms(c, args, display)
                    if any(occurrences(tex, v) for _, v in want):
                        continue
                    if name in pending:
                        key = (s0, name, tuple(args))
                        if key in updated:
                            continue
                        updated.add(key)
                        old = forms(c, args, display, "previous_")
                        hits = [(kind, h) for kind, v in old for h in occurrences(tex, v)]
                        hits = [x for k, x in enumerate(hits)
                                if not any(y[1].start() < x[1].end() and x[1].start() < y[1].end()
                                           for y in hits[:k])]
                        nmarks = sum(1 for m2, sp2 in annotated(doc) if sp2 == sp and
                                     short(m2.group("name")) == name and
                                     split_args(m2.group("args")) == args)
                        shortval = min(len("".join(v.split())) for _, v in old) < SHORT
                        if hits and (len(hits) == nmarks or not shortval):
                            for kind, h in hits:
                                new = dict(want).get(kind, want[0][1])
                                e0, e1, rep = minimal_edit(tex, h.start(), h.end(), new)
                                edits.append((inner0 + e0, inner0 + e1, rep))
                                nrewritten += 1
                            continue
                        unfinished.add(name)
                        problems.append(f"{at}: the span annotated for {name} holds the previous "
                                        f"value {len(hits)} times for {nmarks} marker(s); rewrite "
                                        f"it by hand to {want[0][1]!r}, then rerun --update {name}")
                        continue
                    alt = f" or {want[1][1]!r}" if len(want) > 1 else ""
                    problems.append(f"{at}: the span annotated for {name} does not contain its "
                                    f"value {want[0][1]!r}{alt} (whitespace ignored)")
                if len(MARK_ANY.findall(doc)) != len(MARK.findall(doc)):
                    problems.append(f"{rel}:{line_of(src, start)}: malformed value marker (syntax: "
                                    "`<!-- value NAME ARGS -->` before a math span; there is no "
                                    "closing marker)")
                marked = {short(m.group("name")) for m in MARK.finditer(doc)}
                opted = {short(n) for n in OPT_OUT.findall(doc)}
                own = def_docs.get((rel, start))
                if own and own not in marked:
                    problems.append(f"{rel}:{line_of(src, start)}: the docstring of {own} must show "
                                    f"its value: {example(own, by_name[own])}")
                named = set()
                for cm in CODE.finditer(doc):
                    for n, rx in mention.items():
                        if rx.search(cm.group(2)):
                            named.add(n)
                for n in sorted(named - marked - opted - {own}):
                    first = next(cm for cm in CODE.finditer(doc) if mention[n].search(cm.group(2)))
                    problems.append(f"{rel}:{line_of(src, start + first.start())}: docstring names "
                                    f"`{n}` without its value; put {example(n, by_name[n])} "
                                    "(arguments as this docstring names them)")
                new = doc
                for e0, e1, rep in sorted(edits, reverse=True):
                    new = new[:e0] + rep + new[e1:]
                if new != doc:
                    changed = True
                out.append(src[last:start] + new)
                last = end
            out.append(src[last:])
            text = "".join(out)
            if changed:
                path.write_text(text)
                span_lines = {k for k, line in enumerate(text.split("\n"), 1)
                              if k in span_lines or "<!-- value" in line}
            lines = text.split("\n")
            for k in sorted(span_lines):
                if k <= len(lines) and len(lines[k - 1]) > MAX_LINE:
                    problems.append(f"{rel}:{k}: line of {len(lines[k - 1])} characters in an "
                                    f"annotated value (limit {MAX_LINE}); rewrap it")

    if update_names:
        text = registry_path.read_text()
        for name in update_names:
            if name not in current:
                continue
            body, h = current[name]
            text = rewrite_entry(text, by_name[name]["name"], body, h,
                                 drop_previous=name not in unfinished)
        registry_path.write_text(text)
        print(f"docs/constants.toml: recorded the current body of {', '.join(update_names)}")
    for p in problems:
        print(p)
    verb = f"{nrewritten} values rewritten" if update_names else "checked"
    print(f"{len(by_name)} constants, {ndoc} docstrings, {nmark} value markers on {nspan} spans "
          f"{verb}; {len(problems)} problems")
    return 1 if problems else 0


def toml_str(s):
    if "'" not in s and "\n" not in s:
        return f"'{s}'"
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def rewrite_entry(text, full_name, body, h, drop_previous):
    """Replace `lean_body` and `body_hash` in the `[[constant]]` block of `full_name`, and drop its
    `previous_*` fields."""
    blocks = re.split(r"(?m)^(?=\[\[constant\]\])", text)
    for k, b in enumerate(blocks):
        if re.search(rf'(?m)^name = "{re.escape(full_name)}"$', b):
            b = re.sub(r"(?m)^lean_body = .*$", lambda _: f"lean_body = {toml_str(body)}", b)
            b = re.sub(r"(?m)^body_hash = .*$", lambda _: f'body_hash = "{h}"', b)
            if drop_previous:
                b = re.sub(r"(?m)^previous_(?:latex|display) = .*\n", "", b)
            blocks[k] = b
    return "".join(blocks)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--update", nargs="+", metavar="NAME", default=[],
                    help="rewrite NAME's values from previous_* and record its body and hash")
    a = ap.parse_args()
    sys.exit(run(a.root.resolve(), [short(n) for n in a.update]))


if __name__ == "__main__":
    main()

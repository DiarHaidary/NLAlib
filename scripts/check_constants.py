#!/usr/bin/env python3
"""Named bounds show their current value in every docstring that uses them (CONTRIBUTING §5.2).

The registry `docs/constants.toml` has one `[[constant]]` entry per named constant, tail function
or sample size of the library: its Lean `name`, `kind`, `file`, explicit `args` (Lean order),
`latex` (a template of its value with positional placeholders `#1`, `#2`, ... for the arguments),
`lean_body` (the definition's text from its name to its end, whitespace-normalised) and
`body_hash` (sha256 of `lean_body`, 16 hex digits).

In a docstring (`/-- … -/` or `/-! … -/`) of NLAlib/ or NLAlibScaffold/ the value is written as

    <!-- value gaussianPinvSpecNormBound k \\ell -->$…$<!-- /value -->

the constant's name (with or without `NLAlib.`), then one LaTeX argument per Lean argument,
separated by spaces. An argument containing a space is wrapped in braces, `{\\lvert r \\rvert}`,
which are dropped on substitution; arguments are substituted verbatim otherwise, so write
`(\\varepsilon/2)` where precedence needs parentheses. The value is `$` + the template with `#i`
replaced by the i-th argument + `$`; `--fill` writes it. The opening marker and the value are on
one line, or the opening marker ends a line and the value starts the next; the closing marker
follows the value's `$` directly. Arguments contain no `$`, backtick or `--`, and the closing
marker keeps its spaces (`<!--/value-->` would contain `-/`, which ends a Lean docstring). The
markers are HTML comments: doc-gen4's Markdown hides them, the explorer's build strips them and
scripts/check_latex.mjs skips them.

The check fails if
  * a definition's `lean_body` or `body_hash` differs from the source (the body changed: update
    `latex`, then run `--update NAME`), or its explicit arguments differ from `args`;
  * a marked value differs from its filled template, has the wrong number of arguments, or names
    an unregistered constant;
  * a docstring names a registered constant in backticks without a marked value of it (unless it
    carries the opt-out `<!-- mention NAME -->`, for a name mentioned only in passing; keep rare);
  * a definition's own docstring has no marked value of it;
  * a line with a marker exceeds 100 characters.

Usage:
  python3 scripts/check_constants.py              check; one summary line on success
  python3 scripts/check_constants.py --fill       rewrite every marked value from the registry
  python3 scripts/check_constants.py --update NAME [NAME ...]
                                                  record NAME's current `lean_body` and
                                                  `body_hash`, then --fill
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
MARK = re.compile(r"<!-- value (?P<name>\S+?)(?P<args>(?: [^\n]*?)?) -->[ \t]*\n?[ \t]*"
                  r"(?P<val>[^\n]*?)<!-- /value -->")
MARK_OPEN = re.compile(r"<!-- value\b")
MARK_CLOSE = re.compile(r"<!-- /value -->")
OPT_OUT = re.compile(r"<!-- mention (\S+) -->")
PLACEHOLDER = re.compile(r"#([1-9])")
CODE = re.compile(r"(`+)(.+?)\1", re.S)


def short(name):
    return name[len("NLAlib."):] if name.startswith("NLAlib.") else name


def docstrings(src):
    """(start, end) offsets of every docstring body, as in scripts/check_latex.mjs: after `/--` or
    `/-!`, before `-/`; ordinary nested block comments and line comments are skipped."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            if i + 2 < n and src[i + 2] in "-!":
                end = src.find("-/", i + 3)
                stop = n if end < 0 else end
                out.append((i + 3, stop))
                i = stop + 2
            else:
                depth, i = 1, i + 2
                while i < n and depth:
                    if src.startswith("/-", i):
                        depth, i = depth + 1, i + 2
                    elif src.startswith("-/", i):
                        depth, i = depth - 1, i + 2
                    else:
                        i += 1
        elif src.startswith("--", i):
            nl = src.find("\n", i)
            i = n if nl < 0 else nl
        else:
            i += 1
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


def example(name, c):
    """The marked value of `name` with the definition's argument letters, for messages."""
    args = [GREEK.get(a, a) for a in c["args"]]
    return f"<!-- value {' '.join([name] + args)} -->{fill(c['latex'], args)}<!-- /value -->"


def fill(template, args):
    return "$" + PLACEHOLDER.sub(lambda m: args[int(m.group(1)) - 1], template) + "$"


def find_definition(src, name):
    """(offset, normalised text from the name to the end) of `def`/`irreducible_def NAME`: its first
    line and the indented lines that follow it."""
    m = re.search(rf"^(?:[\w@\[\] ]*?)(?:irreducible_def|def|abbrev) ({re.escape(name)})(?![\w'])",
                  src, re.M)
    if not m:
        return None, None
    lines = src[m.start(1):].split("\n")
    body = [lines[0]]
    for line in lines[1:]:
        if not line.strip() or not line[0].isspace():
            break
        body.append(line)
    return m.start(), " ".join(" ".join(body).split())


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


def run(root, mode, update_names):
    registry_path = root / "docs" / "constants.toml"
    registry = tomllib.loads(registry_path.read_text())["constant"]
    by_name = {short(c["name"]): c for c in registry}
    problems = []

    # 1. the registry against the definitions
    def_docs = {}   # (file, docstring start) -> short name, for the definition's own docstring
    current = {}    # short name -> (lean_body, hash) in the source
    for name, c in by_name.items():
        path = root / c["file"]
        src = path.read_text() if path.exists() else ""
        off, body = find_definition(src, name)
        if body is None:
            problems.append(f"{c['file']}: definition of {c['name']} not found (docs/constants.toml)")
            continue
        current[name] = (body, digest(body))
        own = [d for d in docstrings(src) if d[1] < off and not src[d[1] + 2:off].strip()]
        if own:
            def_docs[(c["file"], own[-1][0])] = name
        else:
            problems.append(f"{c['file']}:{line_of(src, off)}: {c['name']} has no docstring")
        if name in update_names:
            continue
        if body != c["lean_body"] or digest(body) != c["body_hash"]:
            problems.append(
                f"{c['file']}:{line_of(src, off)}: the body of {c['name']} changed.\n"
                f"  registry: {c['lean_body']}\n  source:   {body}\n"
                f"  Update its `latex` in docs/constants.toml to the new value, then run "
                f"`python3 scripts/check_constants.py --update {name}`.")
        if explicit_args(body) != c["args"]:
            problems.append(f"{c['file']}: explicit arguments of {c['name']} are "
                            f"{explicit_args(body)}, registry has {c['args']}")
        for m in PLACEHOLDER.finditer(c["latex"]):
            if int(m.group(1)) > len(c["args"]):
                problems.append(f"docs/constants.toml: {c['name']}: placeholder #{m.group(1)} "
                                f"beyond its {len(c['args'])} arguments")
        if re.search(r"#[1-9][A-Za-z]", c["latex"]):
            problems.append(f"docs/constants.toml: {c['name']}: a placeholder is followed by a "
                            "letter; an argument like `\\ell` would merge with it")
    unknown = set(update_names) - set(by_name)
    if unknown:
        problems.append(f"--update: not in the registry: {', '.join(sorted(unknown))}")
        update_names = [n for n in update_names if n in by_name]

    if update_names:
        text = registry_path.read_text()
        for name in update_names:
            if name not in current:
                continue
            body, h = current[name]
            text = rewrite_entry(text, by_name[name]["name"], body, h)
        registry_path.write_text(text)
        print(f"docs/constants.toml: recorded the current body of {', '.join(update_names)}")

    mention = {n: re.compile(rf"(?<![\w'.])(?:NLAlib\.)?{re.escape(n)}(?![\w'!?])") for n in by_name}
    ndoc = nmark = nfilled = 0
    for lib in LIBS:
        for path in sorted((root / lib).rglob("*.lean")):
            src = path.read_text()
            rel = path.relative_to(root).as_posix()
            out, last, changed = [], 0, False
            for start, end in docstrings(src):
                doc = src[start:end]
                ndoc += 1

                def sub(m):
                    nonlocal nmark, nfilled
                    nmark += 1
                    at = f"{rel}:{line_of(src, start + m.start())}"
                    name, args = short(m.group("name")), split_args(m.group("args"))
                    c = by_name.get(name)
                    if c is None:
                        problems.append(f"{at}: marked value of unregistered constant {name}")
                        return m.group(0)
                    if len(args) != len(c["args"]):
                        problems.append(f"{at}: {name} takes {len(c['args'])} arguments "
                                        f"({' '.join(c['args'])}), marker has {len(args)}")
                        return m.group(0)
                    if re.search(r"--|\$|`", m.group("args")):
                        problems.append(f"{at}: marker arguments may not contain `--`, `$` or "
                                        "a backtick")
                        return m.group(0)
                    want = fill(c["latex"], args)
                    if m.group("val") == want:
                        return m.group(0)
                    if mode == "check":
                        problems.append(f"{at}: stale value of {name}: {m.group('val')!r}, "
                                        f"expected {want!r} (run --fill)")
                        return m.group(0)
                    nfilled += 1
                    return m.group(0)[:m.start("val") - m.start()] + want + "<!-- /value -->"

                new = MARK.sub(sub, doc)
                if len(MARK_OPEN.findall(doc)) != len(MARK.findall(doc)) or \
                        len(MARK_CLOSE.findall(doc)) != len(MARK.findall(doc)):
                    problems.append(f"{rel}:{line_of(src, start)}: malformed value marker "
                                    "(syntax: `<!-- value NAME ARGS -->$…$<!-- /value -->`, one line)")
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
                    c = by_name[n]
                    problems.append(f"{rel}:{line_of(src, start + first.start())}: docstring names "
                                    f"`{n}` without its value; add {example(n, c)} "
                                    "(arguments as this docstring names them)")
                if new != doc:
                    changed = True
                out.append(src[last:start] + new)
                last = end
            out.append(src[last:])
            text = "".join(out)
            if changed and mode != "check":
                path.write_text(text)
            for k, line in enumerate(text.split("\n"), 1):
                if ("<!-- value" in line or "<!-- /value -->" in line) and len(line) > MAX_LINE:
                    problems.append(f"{rel}:{k}: line of {len(line)} characters with a marked value "
                                    f"(limit {MAX_LINE}); rewrap the sentence around it")
    for p in problems:
        print(p)
    verb = f"{nfilled} rewritten" if mode != "check" else "checked"
    print(f"{len(by_name)} constants, {ndoc} docstrings, {nmark} marked values {verb}; "
          f"{len(problems)} problems")
    return 1 if problems else 0


def toml_str(s):
    if "'" not in s and "\n" not in s:
        return f"'{s}'"
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def rewrite_entry(text, full_name, body, h):
    """Replace `lean_body` and `body_hash` in the `[[constant]]` block of `full_name`."""
    blocks = re.split(r"(?m)^(?=\[\[constant\]\])", text)
    for k, b in enumerate(blocks):
        if re.search(rf'(?m)^name = "{re.escape(full_name)}"$', b):
            b = re.sub(r"(?m)^lean_body = .*$", lambda _: f"lean_body = {toml_str(body)}", b)
            b = re.sub(r"(?m)^body_hash = .*$", lambda _: f'body_hash = "{h}"', b)
            blocks[k] = b
    return "".join(blocks)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--fill", action="store_true", help="rewrite every marked value")
    ap.add_argument("--update", nargs="+", metavar="NAME", default=[],
                    help="record the current body and hash of NAME, then --fill")
    a = ap.parse_args()
    mode = "fill" if a.fill or a.update else "check"
    sys.exit(run(a.root.resolve(), mode, [short(n) for n in a.update]))


if __name__ == "__main__":
    main()

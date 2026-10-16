#!/usr/bin/env python3
"""Every `[Key]` or `[Key, label]` citation in a docstring names an entry of docs/references.bib,
every `Result: id` line is a well-formed slug, and every asymptotic form (CONTRIBUTING §5.2,
rule 3) is tagged consistently. Exit 1 on any failure.

Asymptotic forms. A docstring line `Asymptotic: NAME` (or `Asymptotic:` alone with `NAME` on the
next line, when the two do not fit in 100 characters) marks its declaration as the asymptotic form
of the explicit theorem `NAME`. The check, textual like `scripts/ledger_check.py`, requires that the
tagged declaration is an `exists_forall_` theorem, that the tag is the docstring's last line before
any `Result:` line, that `NAME` (a full name) is declared in the same file, and that the two are
related both ways (the explorer's "Related"): the asymptotic form's docstring names `NAME` in
backticks in a sentence besides the tag, and `NAME`'s docstring names the asymptotic form in
backticks (full name or `NLAlib`-relative). A docstring
saying "Asymptotic form: `X`" must name a declaration whose `Asymptotic:` tag points back."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
bib = (ROOT / "docs" / "references.bib").read_text()
keys = set(re.findall(r"^@\w+\{([^,\s]+),", bib, re.M))

cite = re.compile(r"\[([A-Z][A-Za-z]+\d{4}[a-z]?)(?:,[^\]]*)?\]")
result = re.compile(r"^\s*Result:\s*(.+?)\s*(?:-/)?\s*$", re.M)
slug = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

DECL = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public)\s+)*"
    r"(theorem|lemma|def|irreducible_def|structure|abbrev|instance|class|inductive|alias)"
    r"(?:\s+([^\s:({\[]+)|\s*$)")
SKIP = re.compile(r"\s*(?:omit\b.*\bin\s*$|include\b.*\bin\s*$|variable\b.*\bin\s*$|@\[[^\]]*\]\s*$)")
ASYM = re.compile(r"^\s*Asymptotic:[ \t]*(\S*)[ \t]*(?:-/)?[ \t]*$", re.M)
ASYM_FORM = re.compile(r"Asymptotic form:\s*`([^`]+)`")


def declarations(path):
    """(full name, short name, docstring or None) for each declaration of the file."""
    out, namespaces, doc, pending, buf = [], [], None, None, None
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if buf is not None:  # inside a `/--` docstring
            buf.append(line)
            if "-/" in line:
                pending, buf = "\n".join(buf), None
            i += 1
            continue
        if re.match(r"\s*/--", line):
            buf = [line]
            if "-/" in line[line.index("/--") + 3:]:
                pending, buf = line, None
            i += 1
            continue
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m:
            namespaces.append(m.group(1))
            pending = None
        elif (m := re.match(r"\s*end\s+(\S+)\s*$", line)) and namespaces and \
                namespaces[-1] == m.group(1):
            namespaces.pop()
            pending = None
        elif m := DECL.match(line):
            name = m.group(2)
            if name is None and i + 1 < len(lines):  # long name on its own line
                name = re.match(r"\s*([^\s:({\[]+)", lines[i + 1]).group(1)
            if name:
                full = name[7:] if name.startswith("_root_.") else ".".join(namespaces + [name])
                out.append((full, name.split(".")[-1], pending))
            pending = None
        elif line.strip() and not SKIP.match(line):
            pending = None
        i += 1
    return out


def asymptotic_problems(paths):
    bad, decls = [], {}
    for path in paths:
        for full, short, doc in declarations(path):
            decls[full] = (path, short, doc)
    tagged = 0
    for full, (path, short, doc) in decls.items():
        if not doc:
            continue
        body = doc.rsplit("-/", 1)[0]
        for m in ASYM.finditer(body):
            tagged += 1
            target = m.group(1)
            rest = body[m.end():]
            if not target:  # name on the next line
                n = re.match(r"\s*\n\s*(\S+)[ \t]*(?:\n|$)", rest)
                target = n.group(1) if n else ""
                rest = rest[n.end():] if n else rest
            where = f"{path.relative_to(ROOT)}: {full}"
            if not short.startswith("exists_forall_"):
                bad.append(f"{where}: an `Asymptotic:` tag on a declaration not named exists_forall_")
            if any(l.strip() and not l.strip().startswith("Result:") for l in rest.splitlines()):
                bad.append(f"{where}: the `Asymptotic:` line is not the docstring's last line "
                           "(before `Result:`)")
            if target not in decls:
                bad.append(f"{where}: `Asymptotic: {target}` names no declaration of the library")
                continue
            trel = target[7:] if target.startswith("NLAlib.") else target
            if not re.search(rf"`(?:NLAlib\.)?{re.escape(trel)}`", body[:m.start()]):
                bad.append(f"{where}: its docstring does not name {target} in a sentence")
            tpath, _, tdoc = decls[target]
            if tpath != path:
                bad.append(f"{where}: its explicit theorem {target} is in another file")
            rel = full[7:] if full.startswith("NLAlib.") else full
            if not tdoc or not re.search(rf"`(?:NLAlib\.)?{re.escape(rel)}`", tdoc):
                bad.append(f"{where}: the docstring of {target} does not name this asymptotic form")
    for full, (path, short, doc) in decls.items():
        for m in ASYM_FORM.finditer(doc or ""):
            name = m.group(1)
            name = name if name in decls else f"NLAlib.{name}"
            adoc = decls.get(name, (None, None, None))[2] or ""
            if not re.search(rf"^\s*Asymptotic:\s*(?:-/)?\s*\n?\s*{re.escape(full)}\b", adoc, re.M):
                bad.append(f"{path.relative_to(ROOT)}: {full}: `Asymptotic form:` names {m.group(1)}, "
                           "which is not tagged as its asymptotic form")
    return tagged, bad


bad = 0
paths = []
for lib in ("NLAlib", "NLAlibScaffold"):
    for path in sorted((ROOT / lib).rglob("*.lean")):
        paths.append(path)
        text = path.read_text()
        for m in cite.finditer(text):
            if m.group(1) not in keys:
                print(f"{path}: unknown reference key [{m.group(1)}]")
                bad += 1
        for m in result.finditer(text):
            for rid in m.group(1).split(","):
                if not slug.match(rid.strip()):
                    print(f"{path}: malformed result id {rid.strip()!r}")
                    bad += 1
tagged, problems = asymptotic_problems(paths)
for p in problems:
    print(p)
bad += len(problems)
print(f"{len(keys)} bibliography keys; {tagged} asymptotic forms; {bad} problems")
sys.exit(1 if bad else 0)

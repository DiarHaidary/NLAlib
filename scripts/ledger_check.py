#!/usr/bin/env python3
"""Check that every new name in docs/port/ledger.json is declared in the library (rule G2,
CONTRIBUTING §9).

Usage: python3 scripts/ledger_check.py
Declarations and structure fields are found textually (namespace tracking, `_root_.` prefixes,
docstrings skipped), so generated names (`Foo.mk`, `Foo.rec`) are reported as missing although they
exist; anything else reported is a ledger entry pointing at a renamed or deleted declaration.
Exit status 1 if any target is missing. `scripts/check_rules.py` runs the same check as G2.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public)\s+)*"
    r"(?:theorem|lemma|def|irreducible_def|structure|abbrev|instance|class|inductive|alias)\s+([^\s:({\[]+)")


def declared_names(root=ROOT):
    names = set()
    for lib in ("NLAlib", "NLAlibScaffold"):
        for f in (root / lib).rglob("*.lean"):
            namespaces = []
            structure = None
            in_doc = False
            for line in f.read_text().splitlines():
                if in_doc:  # a docstring continuation line is not a column-0 command
                    in_doc = "-/" not in line
                    continue
                if "/--" in line and "-/" not in line[line.index("/--") + 3:]:
                    in_doc = True
                    continue
                m = re.match(r"\s*namespace\s+(\S+)", line)
                if m:
                    namespaces.append(m.group(1))
                    continue
                m = re.match(r"\s*end\s+(\S+)\s*$", line)
                if m and namespaces and namespaces[-1] == m.group(1):
                    namespaces.pop()
                    continue
                m = DECL.match(line)
                if m:
                    n = m.group(1)
                    full = n[7:] if n.startswith("_root_.") else ".".join(namespaces + [n])
                    names.add(full)
                    structure = full if re.search(r"\b(structure|class)\s", line) else None
                    continue
                m = re.match(r"\s+([^\s:({\[]+)\s*:", line)
                if structure and m:
                    names.add(f"{structure}.{m.group(1)}")
                elif line and not line[0].isspace():
                    structure = None
    return names


def missing(root=ROOT):
    """(old name, ledger target, stage) for each ledger target that is not declared."""
    names = declared_names(root)
    ledger = json.loads((root / "docs" / "port" / "ledger.json").read_text())
    return names, [(old, e["new"], e.get("stage")) for old, e in sorted(ledger.items())
                   if e.get("new") and e["new"] not in names]


def main():
    names, miss = missing()
    print(f"{len(names)} declarations found; {len(miss)} ledger targets missing")
    for old, new, stage in miss:
        print(f"G2 docs/port/ledger.json:0 {old}: ledger target {new} (stage {stage}) is not declared;"
              " point the entry at the current name")
    return 1 if miss else 0


if __name__ == "__main__":
    sys.exit(main())

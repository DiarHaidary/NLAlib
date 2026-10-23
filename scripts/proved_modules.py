#!/usr/bin/env python3
"""List the NLAlib modules that are fully proved, for checks on a library still under way.

Usage: python3 scripts/proved_modules.py [bad] [--imports]
A module is listed if neither it nor any NLAlib module it imports, directly or not, contains
`sorry` outside comments. With `bad`, the complement is listed. With `--imports`, each line is
printed as `import <module>`: prefix that list to `scripts/Audit.lean` or `scripts/Lint.lean`
minus their first line to audit or lint the proved part only, as `scripts/stage_check.sh` does.
"""
import re
import sys
from pathlib import Path

# The import forms of `scripts/leansrc.py`: `public`, `meta` and `import all` included.
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def nlalib_imports(text):
    """The NLAlib modules a Lean source imports, in every import form."""
    return [m for m in IMPORT_RE.findall(text) if m.startswith("NLAlib.")]


def has_sorry(text):
    """Whether a Lean source contains `sorry` outside comments."""
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    return bool(re.search(r"\bsorry\b", code))


def main(args):
    root = Path(__file__).resolve().parent.parent
    mods = {}
    for f in sorted((root / "NLAlib").rglob("*.lean")):
        name = ".".join(f.relative_to(root).with_suffix("").parts)
        text = f.read_text()
        mods[name] = (nlalib_imports(text), has_sorry(text))
    bad = {m for m, (_, sorry) in mods.items() if sorry}
    changed = True
    while changed:
        changed = False
        for m, (imports, _) in mods.items():
            if m not in bad and any(i in bad for i in imports):
                bad.add(m)
                changed = True
    chosen = sorted(bad) if "bad" in args else sorted(m for m in mods if m not in bad)
    prefix = "import " if "--imports" in args else ""
    print("\n".join(prefix + m for m in chosen))


if __name__ == "__main__":
    main(sys.argv[1:])

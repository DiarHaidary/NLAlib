#!/usr/bin/env python3
"""Add presentation roles and source fingerprints to freshly extracted explorer data.

Run through explore_data.sh after building NLAlib. Hashes let the explorer safely use a
source checkout or a release archive, including a local preview of uncommitted doc edits.
Named bounds are supporting API by default; their constants.toml entry may explicitly set
explorer_role = "concept" when the definition itself is a headline mathematical concept.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib


def enrich(data, root):
    root = Path(root).resolve()
    registry = tomllib.loads((root / "docs/constants.toml").read_text())
    roles = {}
    for entry in registry.get("constant", []):
        role = entry.get("explorer_role", "support")
        if role not in {"support", "concept"}:
            raise ValueError(f"invalid explorer_role for {entry['name']}: {role!r}")
        roles[entry["name"]] = role
    names = {d["name"] for d in data["decls"]}
    missing = roles.keys() - names
    if missing:
        raise ValueError(f"registered bounds missing from extraction: {sorted(missing)}")
    for decl in data["decls"]:
        if decl["name"] in roles:
            decl["explorerRole"] = roles[decl["name"]]
    hashes = {}
    for module in data["modules"]:
        relative = Path(module["path"])
        source = (root / relative).resolve()
        if relative.is_absolute() or ".." in relative.parts or not source.is_relative_to(root):
            raise ValueError(f"unsafe module path: {relative}")
        hashes[relative.as_posix()] = hashlib.sha256(source.read_bytes()).hexdigest()
    data["sourceHashes"] = hashes
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    data = enrich(json.loads(args.data.read_text()), root)
    def git(*argv):
        return subprocess.check_output(["git", "-C", str(root), *argv], text=True).strip()
    data["commit"] = git("rev-parse", "HEAD")
    data["date"] = git("show", "-s", "--format=%cI", "HEAD")
    args.data.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(f"{args.data}: {len(data['modules'])} modules, {len(data['decls'])} declarations, "
          f"{data['commit'][:10]}")


if __name__ == "__main__":
    main()

#!/usr/bin/env bash
# Data for the explore website (nla-lib.org/explore): runs scripts/Explore.lean, then stamps the
# git commit, date, presentation roles and source fingerprints into the JSON.
#
# Usage: scripts/explore_data.sh [OUT]   (default explore-data.json; run from the repository root
# after `lake build NLAlib`). Never while another build is running (CONTRIBUTING §10).
set -euo pipefail
out="${1:-explore-data.json}"
EXPLORE_OUT="$out" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" \
  lake env lean -M 8000 scripts/Explore.lean
python3 scripts/explore_metadata.py "$out"

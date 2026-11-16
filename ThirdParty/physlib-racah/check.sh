#!/usr/bin/env bash
# Apply the vendored Racah stack to a clean Physlib checkout at the base commit and build it.
# Usage: ThirdParty/physlib-racah/check.sh /path/to/physlib-checkout   (a clone with a built Mathlib/Physlib is much faster)
set -euo pipefail
BASE=3d9ca099e0c842e746bef6f10289a6f965bc8f08
here="$(cd "$(dirname "$0")" && pwd)"
repo="${1:?path to a Physlib checkout}"
cd "$repo"
git diff --quiet && git diff --cached --quiet || { echo "checkout not clean"; exit 1; }
git cat-file -e "$BASE^{commit}" || { echo "base commit $BASE not present; fetch upstream"; exit 1; }
git switch -c racah-check "$BASE"
git am "$here"/patches/*.patch
lake build PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJRacahAll
lake build PhyslibAlpha.Mathematics.SpecialFunctions.Hypergeometric.Sears
echo "OK: sixJ_eq_ite_racah6j builds on top of $BASE"

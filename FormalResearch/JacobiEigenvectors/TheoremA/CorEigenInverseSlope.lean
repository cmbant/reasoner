module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvCoeffs
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeEdgeS0

/-!
# Paper J, Layer 2: cor:eigen (b) from the slope input (L2.E)

Source: Paper J `thmA.tex`, `cor:eigen` (b).

## Proved here

* **`corEigenInverse_of_slope`**: `InvS0 F K S ∧ InvLevel F K M S delta ∧ InvCoeffs F K M S` for the `S` of `ThmAi` with the slope input `BandSlope` (`M >= 1`, `0 < delta`): `InvS0` is `BandSlope` together with
  `invS0_edges` (the soft-edge values), `InvLevel` is `invLevel_of_slope`, `InvCoeffs` is `invCoeffs_of_slope`.

## Differences from the paper

The premise `0 < delta` is now part of the frozen `CorEigenInverse` (finding F-BB-1); `BandSlope` is *not* (F-BB-2): `corEigen_proved` (`Assembly/CorEigen.lean`) supplies it from the windows.

## Not formalised

`BandSlope` itself (from the windows: `CorEigenWindows.bandSlope_of_windows`, `bandSlope_of_layer4`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn : ℝ}

/-- **cor:eigen (b)** from the slope input: `InvS0` (the uniform slope is `BandSlope`, the edge values are `invS0_edges`), `InvLevel` (`invLevel_of_slope`) and `InvCoeffs` (`invCoeffs_of_slope`). -/
theorem corEigenInverse_of_slope (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K M) (hM : 1 ≤ M)
    (hδ : 0 < δ) (hS : SmoothExt F K M S δ Cn) {hM' C : ℝ} (hR : EigenRule F K M S hM' C) (hA : ActionFormula F K S)
    (hsl : BandSlope F K S) : InvS0 F K S ∧ InvLevel F K M S δ ∧ InvCoeffs F K M S := by
  have hD0 := dm_zero_of_dm F K M hK hD
  obtain ⟨e1, e2⟩ := invS0_edges F K hH hD0 hδ hS hA
  exact ⟨⟨hsl, e1, e2⟩, invLevel_of_slope hK hH hD hM hδ hS hR hA hsl, invCoeffs_of_slope hK hH hD hM hδ hS hR hA hsl⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenInverse_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenInverse_of_slope

end FormalResearch.JacobiEigenvectors.TheoremA

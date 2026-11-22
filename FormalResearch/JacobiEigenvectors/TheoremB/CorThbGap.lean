module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStable
public import FormalResearch.JacobiEigenvectors.Assembly.CorEigen

/-!
# Paper J, Theorem B, L3.D/L3.Dm: the gap bound `EigGapBound` from the Layer-4 chart inputs

Source: Paper J `thmA.tex`, `cor:eigen` (c) (`CorEigenGap1`, `c h ≤ X_k - X_{k+1}`), as used in `thmB.tex`, `cor:thb-stable` and `cor:thb-Dm`.

Claim class: **proved under explicit hypotheses** (the Layer-4 chart inputs `Layer4Inputs G K 1`).

## Proved here (axiom-pinned)

* `eigGapBound_of_layer4 : Layer4Inputs G K 1 → IsCompact K → HypOn G K → DM G K 1 → EigGapBound G K`: the gap bound of `cor:eigen (c)` for the family `G`, from the chart and phase inputs of order `1`
  (`Layer4Inputs G K 1`, the premises of `thmAi_assembled`) and the standing hypotheses `(H1)`--`(H3)`, `(D_1)` of `cor:eigen (c)`.  The proof assembles what is already proved:
  `thmAi_assembled` gives the smooth coefficients `S` of `thm:A (i)` (`ThmAi G K 1`), `bandSlope_of_layer4` the slope `-S_0' ≥ 2 c_0` on the band, `BandSlope.surj` an inverse `x_0` of `S_0`
  on `[0, π L]`, and `corEigenGap1_of_slope` the first part of `cor:eigen (c)`; `EigGapBound` is its lower bound `c_1 h ≤ X_i - X_{i+1}`.

## Differences from the paper

None; the paper's `cor:eigen (c)` first part is read off with the constant `c_1` of `corEigenGap1_of_slope` (the admissible `S` is the one produced by `thm:A (i)`, any other has the same `S_0` on the band).

## Not formalised

The Layer-4 inputs themselves (`CI`, `PI`, `SIu`, `SIl`; see `Assembly/CorEigen.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA

variable {Par : Type*} [TopologicalSpace Par]

/-- **The gap bound of `cor:eigen (c)` from the Layer-4 inputs of order `1`** (see the module docstring): `EigGapBound G K`. -/
theorem eigGapBound_of_layer4 {G : SymbolFamily Par} {K : Set Par} (L : Layer4Inputs G K 1) (hK : IsCompact K) (hH : HypOn G K)
    (hD : DM G K 1) : EigGapBound G K := by
  obtain ⟨δ, Cn, C, hM, S, hδ, hS, hA, hR⟩ :=
    thmAi_assembled G K 1 L.Kidx L.t0 L.U L.V L.cPC L.CPC L.CI L.PI L.ht0 L.SIu L.SIl L.hw L.hlt L.hJhi L.hJlo L.hwb L.hKidx hK hH hD
  have hsl : BandSlope G K S := bandSlope_of_layer4 L hK hH hD hδ hS hA
  have hlt := bandLo_lt_bandHi G K 1 hH hD
  have hD0 : DM G K 0 := dm_zero_of_dm G K 1 hK hD
  have hex : ∀ μ ∈ K, ∀ y ∈ Icc (0 : ℝ) (Real.pi * G.L), ∃ X ∈ Icc (G.bandLo μ) (G.bandHi μ), S 0 μ X = y :=
    fun μ hμ y hy => BandSlope.surj hS hδ hA hH hD0 hμ (hlt μ hμ) hy
  choose! x0 hx0 using hex
  obtain ⟨C1, c1, C2, h0, hh0, hc1, H⟩ := corEigenGap1_of_slope hK hH hD hδ hS hR hA hsl (fun μ y => x0 μ y)
    (fun μ hμ y hy => hx0 μ hμ y hy)
  exact ⟨c1, h0, hc1, hh0, fun μ hμ N hN X Um hE i j hij => (H μ hμ N hN X Um hE i j hij).2.1⟩

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigGapBound_of_layer4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigGapBound_of_layer4

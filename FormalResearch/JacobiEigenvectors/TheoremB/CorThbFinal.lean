module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbFinal
public import FormalResearch.JacobiEigenvectors.TheoremB.CorThbDm

/-!
# Paper J, Theorem B, L3.D and L3.Dm: `cor:thb-stable` and `cor:thb-Dm` with `thmB_proved`

Source: Paper J `thmB.tex`, `cor:thb-stable`, `cor:thb-Dm`.  Claim class: **proved under explicit hypotheses**.

## Proved here (axiom-pinned)

* `corThbStable_proved`: `corThbStable` (`ThbStable.lean`) with `ThmB CP spl` supplied by `thmB_proved CP TB spl` (so the only
  inputs are the transfer bundle `TB` of the charts, as for `thmB_proved`, and the gap bound `EigGapBound F K` of
  `cor:eigen (c)`).
* `corThbDm_proved`: the frozen `CorThbDm CP spl` for the chart pair `CP` of `truncFamily F m`, with `ThmB` for `CP` supplied by
  `thmB_proved CP TB spl`; extra premises: the transfer bundle `TB` and `EigGapBound (truncFamily F m) K`.  The hypothesis of `ThmB` for the truncated family is `StdDM (truncFamily F m) K Kidx` (the
  consequences of `(D_{2 Kidx+1})` that the proof uses), which `stdDM_trunc` derives from `DM F K m` (finding F-DD1: `DM (truncFamily F m) K (2 Kidx + 1)` itself does not follow).
* `hypOn_truncFamily`: `HypOn F K` gives `HypOn (truncFamily F m) K` (same principal symbols).

## Differences from the paper

The `ThmB` hypothesis is `StdDM` (`(D_1)` and the regularity and remainder of the frozen matrices, the paper's `(E_Kbar)` with budget `r(m) >= r(max(2 Kbar - 1, 0))`), as in the paper's proof; the frozen
`ThmB` is stated with `StdDM` in place of `(D_{q_m+1})` (it implies the paper's: `stdDM_of_dm`).

## Not formalised

The transfer bundle `TB` and the gap bound.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA

variable {Par : Type*} [TopologicalSpace Par]

theorem hypOn_truncFamily {F : SymbolFamily Par} {K : Set Par} (m : ℕ) (h : HypOn F K) :
    HypOn (truncFamily F m) K := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun μ hμ => ?_⟩
  have e1 : (truncFamily F m).G 0 μ = F.G 0 μ := by funext s; simp [truncFamily]
  have e2 : (truncFamily F m).B 0 μ = F.B 0 μ := by funext s; simp [truncFamily]
  rw [e1, e2]
  exact hg μ hμ

section Final

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`cor:thb-stable`** with `ThmB` from `thmB_proved`. -/
theorem corThbStable_proved
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ)
    (h1m : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hq : q = 2 * Kidx) (hcpt : IsCompact K) (hH : HypOn F K)
    (hD : StdDM F K Kidx) (hspl : CP.SplicesInWindow spl) (hgap : EigGapBound F K)
    (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C hm Cs h' : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ 0 ≤ Cs ∧ 0 < h' ∧ h' ≤ hm ∧
      ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h' → F.step N ≤ t0 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
          IsEigenSystem (F.jacobiMat μ N) Xs Um →
            ThbStableAt (F.jacobiMat μ N) (compMatrix CP.CI0 spl μ N Xs) (K0 * F.step N ^ (m + 1))
              ((C + Cs * K0) * F.step N ^ m) :=
  corThbStable CP spl (thmB_proved CP TB spl) h1m hK hq hcpt hH hD hspl hgap K0 hK0

/-- **`cor:thb-Dm`** (`CorThbDm`) with `ThmB` for the truncated chart pair from `thmB_proved`, given the gap bound of the truncated family. -/
theorem corThbDm_proved
    (CP : ChartPair (F := truncFamily F m) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (hgap : EigGapBound (truncFamily F m) K) :
    CorThbDm CP spl := by
  intro h1m hK hq hcpt hH hD hspl
  exact corThbDm_of_thmB CP spl
    (thmBConcl_of_thmB CP spl (thmB_proved CP TB spl) h1m hK hq hcpt (hypOn_truncFamily m hH) (stdDM_trunc h1m hK hcpt hD) hspl)
    hgap h1m hK hq hcpt hH hD hspl

end Final

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.corThbStable_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.corThbStable_proved

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.corThbDm_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.corThbDm_proved

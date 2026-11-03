module

public import FormalResearch.FourQubitEntropy.QVEqualityBell

/-!
# Equality classification in (QK), `thm:fqe-quadratic-variance`

Paper E, `quadratic_variance_certificate.tex` and `sup_renyi.tex` (`sec:sup-qk`).  Conditional on (QV)
(`RenyiFull.SharpQuadraticVarianceBound`, proved unconditionally in `QVCheck/Unconditional.lean`; the
unconditional corollaries are in `QVEqualityMain.lean`):

for a unit pure four-qubit state `ψ`, `F² + (9/2)(P-1) = 6 V_P` holds iff the three cut spectra are, up to
the ordering of the cuts and of the eigenvalues,

* HS spectra `(1/2, 1/6, 1/6, 1/6)` (`IsHsTriple`; then `ψ` is in the local-unitary orbit of `M₄` or `conj M₄`,
  `hs_triple_LU`), or
* cluster spectra `((1/2, 1/2, 0, 0), (1/4)⁴, (1/4)⁴)` (`IsClusterTriple`), or
* the spectra of a product of two Bell pairs `((1,0,0,0), (1/4)⁴, (1/4)⁴)` (`IsBellTriple`, equivalently
  `IsBellProduct ψ`, `isBellTriple_iff_bellProduct`).

The proof follows the paper: equality forces `P ∈ {1, 3/2}` ((QV) strictly gives `1 < P < 3/2` a positive defect
`3(P-1)(3/2-P)`, the purity box makes `P > 3/2` strict, `qk_strict_scalar`); at `P = 3/2` the box forces `F = 0`
and purities `(1, 1/4, 1/4)` up to order (`eq_three_two`), i.e. the Bell spectral triple; at `P = 1` the critical
profile (RF) of `prop:fqe-critical-variance` (`critical_qk_equality`) leaves HS or cluster spectra.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

theorem purity_cuts_sum (ψ : Psi) : purity ψ = cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ :=
  purity_eq_cutPurities ψ

/-- **Equality classification in (QK)** (`thm:fqe-quadratic-variance`), conditional on (QV). -/
theorem qk_equality_iff (hQV : SharpQuadraticVarianceBound) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    6 * VP ψ = sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1) ↔
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsBellTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  constructor
  · intro heq
    have p2 : IsProb4 (cutSpec₂ ψ) := isProb4_spec4 (isProb12 hψ)
    have p3 : IsProb4 (cutSpec₃ ψ) := isProb4_spec4 (isProb13 hψ)
    have p4 : IsProb4 (cutSpec₄ ψ) := isProb4_spec4 (isProb14 hψ)
    have ha := pur_ge_quarter p2
    have hb := pur_ge_quarter p3
    have hc := pur_ge_quarter p4
    have ha' := pur_le_one p2
    have hb' := pur_le_one p3
    have hc' := pur_le_one p4
    rw [pur_cutSpec₂] at ha ha'
    rw [pur_cutSpec₃] at hb hb'
    rw [pur_cutSpec₄] at hc hc'
    have hP := purity_cuts_sum ψ
    have hP1 := purity_ge ψ
    rw [hψ] at hP1
    have hQ := hQV ψ hψ
    have heq' := heq
    unfold VP at heq' hQ
    rw [hP] at heq' hQ hP1
    rcases lt_trichotomy (cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ) (3 / 2) with hlt | heq32 | hgt
    · rcases eq_or_lt_of_le (show 1 ≤ cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ by nlinarith) with h1 | h1
      · -- P = 1
        have hP1' : purity ψ = 1 := by rw [hP]; exact h1.symm
        have := critical_qk_equality ψ hψ hP1' (by rw [hP1'] at heq; linarith)
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exfalso
        nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 hlt)]
    · right; right
      obtain ⟨-, h⟩ := eq_three_two ha ha' hb hb' hc hc' heq32 heq'
      exact bellTriple_of_purities hψ h
    · exfalso
      have := qk_strict_scalar ha ha' hb hb' hc hc' hgt (F := sexticF ψ)
      linarith
  · intro h
    have key : 6 * RenyiFull.Vm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) =
        RenyiFull.Fm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ^ 2 +
          9 / 2 * (RenyiFull.Pm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) - 1) := by
      rcases h with h | h | h
      · exact hs_triple_eq h
      · exact cluster_triple_eq h
      · exact bell_triple_eq h
    rw [← VP_eq_Vm, Fm_cutSpec ψ hψ, Pm_cutSpec] at key
    exact key

end FormalResearch.FourQubitEntropy.QVEquality

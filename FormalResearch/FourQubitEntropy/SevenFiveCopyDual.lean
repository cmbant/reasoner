module

public import FormalResearch.FourQubitEntropy.SevenQubitConseqPurity

/-!
# Layer 0 of the sharp seven-qubit purity bound: from a five-copy dual identity to `SevenPurityBound`

`cor:seven-global-from-fivecopy` (`QI/multiqubit_entanglement/seven_qubit_entanglement/moment_orbit_rigidity.tex`)
rests on `thm:fivecopy-sharp-certificate` (FP5-1): rational positive-definite `C_b` on twelve physical
faces with `q(G) = ∑_b tr[C_b W_bᵀ Γ_b(G) Wᵦ]`.  On a pure state, `W_bᵀ Γ_b(X₅⁺(ψ)) W_b` is a Gram matrix of
covariants of `ψ`, so the right-hand side is `∑_b Φ_b(ψ)^† C_b Φ_b(ψ)` with `Φ_b` polynomial maps of bidegree
`(5, 5)` in total.

This file states exactly that polynomial identity, abstractly (the faces `ι`, their ranks `k b`, the covariant
maps `Φ b` and the weights `C b` are *arguments*, not data), and proves the inequality part of the corollary:

* `FiveCopyDualIdentity`: for every `ψ : BitString → ℂ` (homogenised with `N = ‖ψ‖²`),
  `π₃(ψ) N³ − (121/917) N⁵ = ∑_b Re (Φ_b ψ)^† C_b (Φ_b ψ)`;
* `sevenPurityBound_of_dual`: the identity with every `C_b` positive semidefinite gives `SevenPurityBound`;
* `purity_gap_ge_of_dual`: the quantitative form `π₃ − 121/917 ≥ c ∑_b ‖Φ_b ψ‖²` for unit `ψ`, when
  `C_b − c·1` is positive semidefinite for all `b` (`c` the least eigenvalue of the `C_b`).

Nothing here is a certificate: the *content* of FP5-1 is the construction of `Φ_b`, `C_b` and a proof of
`FiveCopyDualIdentity`; this file isolates the interface the later layers must meet.
-/

@[expose] public section


open scoped Matrix ComplexConjugate ComplexOrder
open Finset

namespace FormalResearch.FourQubitEntropy.SevenFiveCopy

open FormalResearch.FourQubitEntropy.SevenQubitIco FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- The squared norm `N(ψ) = ∑_z |ψ z|²` (so `UnitVec ψ ↔ N ψ = 1`). -/
noncomputable def nrm (ψ : BitString → ℂ) : ℝ := ∑ z, Complex.normSq (ψ z)

theorem unitVec_iff (ψ : BitString → ℂ) : UnitVec ψ ↔ nrm ψ = 1 := Iff.rfl

section
variable {ι : Type*} [Fintype ι] {k : ι → ℕ}

/-- The face form `Re Φ^† C Φ` of a covariant vector `Φ` with Hermitian weight `C`. -/
noncomputable def faceForm (C : ∀ b, Matrix (Fin (k b)) (Fin (k b)) ℂ)
    (Φ : ∀ b, (BitString → ℂ) → Fin (k b) → ℂ) (ψ : BitString → ℂ) (b : ι) : ℝ :=
  (star (Φ b ψ) ⬝ᵥ (C b *ᵥ Φ b ψ)).re

/-- **The five-copy dual identity** (the polynomial identity of `thm:fivecopy-sharp-certificate`, written on
vectors): `π₃ N³ − (121/917) N⁵ = ∑_b Re Φ_b^† C_b Φ_b` for every `ψ`. -/
def FiveCopyDualIdentity (C : ∀ b, Matrix (Fin (k b)) (Fin (k b)) ℂ)
    (Φ : ∀ b, (BitString → ℂ) → Fin (k b) → ℂ) : Prop :=
  ∀ ψ : BitString → ℂ,
    meanPurity3 ψ * nrm ψ ^ 3 - 121 / 917 * nrm ψ ^ 5 = ∑ b, faceForm C Φ ψ b

theorem re_star_dot_self {m : ℕ} (v : Fin m → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

omit [Fintype ι] in
/-- A positive semidefinite weight gives a nonnegative face form. -/
theorem faceForm_nonneg {C : ∀ b, Matrix (Fin (k b)) (Fin (k b)) ℂ}
    (hC : ∀ b, (C b).PosSemidef) (Φ : ∀ b, (BitString → ℂ) → Fin (k b) → ℂ)
    (ψ : BitString → ℂ) (b : ι) : 0 ≤ faceForm C Φ ψ b := by
  have h := (hC b).dotProduct_mulVec_nonneg (Φ b ψ)
  unfold faceForm
  exact Complex.nonneg_iff.mp h |>.1

/-- **Layer 0.**  The five-copy dual identity with positive semidefinite weights gives the sharp
seven-qubit purity bound `π₃ ≥ 121/917` (the inequality half of `cor:seven-global-from-fivecopy`). -/
theorem sevenPurityBound_of_dual {C : ∀ b, Matrix (Fin (k b)) (Fin (k b)) ℂ}
    {Φ : ∀ b, (BitString → ℂ) → Fin (k b) → ℂ}
    (hC : ∀ b, (C b).PosSemidef) (hid : FiveCopyDualIdentity C Φ) : SevenPurityBound := by
  intro ψ hψ
  have h1 : nrm ψ = 1 := hψ
  have h := hid ψ
  rw [h1] at h
  have : 0 ≤ ∑ b, faceForm C Φ ψ b := Finset.sum_nonneg fun b _ => faceForm_nonneg hC Φ ψ b
  linarith

/-- **Quantitative form** (`cor:seven-global-from-fivecopy`, last display): if every `C_b − c·1` is positive
semidefinite then `π₃(ψ) − 121/917 ≥ c ∑_b ‖Φ_b ψ‖²` for unit `ψ`. -/
theorem purity_gap_ge_of_dual {C : ∀ b, Matrix (Fin (k b)) (Fin (k b)) ℂ}
    {Φ : ∀ b, (BitString → ℂ) → Fin (k b) → ℂ} {c : ℝ}
    (hC : ∀ b, (C b - (c : ℂ) • (1 : Matrix (Fin (k b)) (Fin (k b)) ℂ)).PosSemidef)
    (hid : FiveCopyDualIdentity C Φ) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    c * ∑ b, ∑ i, Complex.normSq (Φ b ψ i) ≤ meanPurity3 ψ - 121 / 917 := by
  have h1 : nrm ψ = 1 := hψ
  have h := hid ψ
  rw [h1] at h
  have key : ∀ b, c * ∑ i, Complex.normSq (Φ b ψ i) ≤ faceForm C Φ ψ b := by
    intro b
    have h2 := (hC b).dotProduct_mulVec_nonneg (Φ b ψ)
    have h3 : (star (Φ b ψ) ⬝ᵥ ((C b - (c : ℂ) • 1) *ᵥ Φ b ψ)).re =
        faceForm C Φ ψ b - c * ∑ i, Complex.normSq (Φ b ψ i) := by
      simp only [faceForm, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rw [re_star_dot_self]
    have := (Complex.nonneg_iff.mp h2).1
    linarith
  have hs : c * ∑ b, ∑ i, Complex.normSq (Φ b ψ i) ≤ ∑ b, faceForm C Φ ψ b := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun b _ => key b
  linarith

end

end FormalResearch.FourQubitEntropy.SevenFiveCopy

#print axioms FormalResearch.FourQubitEntropy.SevenFiveCopy.sevenPurityBound_of_dual
#print axioms FormalResearch.FourQubitEntropy.SevenFiveCopy.purity_gap_ge_of_dual

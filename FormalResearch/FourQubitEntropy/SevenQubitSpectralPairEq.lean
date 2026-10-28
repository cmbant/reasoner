import FormalResearch.FourQubitEntropy.SevenQubitSpectralPairCore

/-!
# The equality family `ρ_r = (1-r) I/8 + r |g⟩⟨g|` of the spin-flip spectral pairing

For a unit vector `g` of three qubits and `r ∈ [0,1]` the state `rhoR r g` attains equality in
`b(ρ) ≥ 4 v(ρ)` (`prop:seven-spinflip-spectral-pair`):
`e(ρ_r) = 7 r²`, `b(ρ_r) = 3 r²`, `v(ρ_r) = 3 r²/4`.  All three are proved here
(`rhoR_e3`, `rhoR_b3`, `rhoR_v3`), hence `rhoR_equality`.

The independence of `b(|g⟩⟨g|) = 3` of `g` is proved through the spin-flip Pauli identity
`8 tr(ρ ρ̃) = 1 - e + 2b` of `SevenQubitSpectralPairCore` together with `tr(|g⟩⟨g| ρ̃) = 0`
(`ρ̃ = Y^{⊗3} ρᵀ Y^{⊗3}`; `Y^{⊗3}` is antisymmetric for an odd number of qubits).
-/

open scoped ComplexConjugate Matrix ComplexOrder
open Finset
open FormalResearch.FourQubitEntropy.SevenQubitConseq

namespace FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

/-- A unit vector of three qubits. -/
def IsUnit3 (g : Cfg3 → ℂ) : Prop := ∑ a, Complex.normSq (g a) = 1

/-- The projector `|g⟩⟨g|`. -/
def projP (g : Cfg3 → ℂ) : Mat3 := Matrix.of fun a b => g a * conj (g b)

/-- `ρ_r = (1-r) I/8 + r |g⟩⟨g|`. -/
noncomputable def rhoR (r : ℝ) (g : Cfg3 → ℂ) : Mat3 :=
  (((1 - r) / 8 : ℝ) : ℂ) • (1 : Mat3) + (r : ℂ) • projP g

section Algebra

variable {g : Cfg3 → ℂ}

theorem sum_conj_mul (hg : IsUnit3 g) : ∑ x, conj (g x) * g x = 1 := by
  have h : ((∑ x, Complex.normSq (g x) : ℝ) : ℂ) = 1 := by rw [hg]; simp
  rw [← h]
  push_cast
  exact Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_conj_mul_self).symm

theorem projP_mul (hg : IsUnit3 g) : projP g * projP g = projP g := by
  ext a b
  simp only [Matrix.mul_apply, projP, Matrix.of_apply]
  calc ∑ x, g a * conj (g x) * (g x * conj (g b)) = g a * conj (g b) * ∑ x, conj (g x) * g x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    _ = g a * conj (g b) := by rw [sum_conj_mul hg, mul_one]

theorem projP_trace (hg : IsUnit3 g) : (projP g).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, projP, Matrix.of_apply]
  rw [← sum_conj_mul hg]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem projP_herm : (projP g).IsHermitian := by
  ext a b
  simp [projP, Matrix.conjTranspose_apply, mul_comm]

theorem rhoR_herm (r : ℝ) : (rhoR r g).IsHermitian := by
  ext a b
  simp only [rhoR, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    projP, Matrix.of_apply, star_add, star_mul', Complex.star_def, Complex.conj_ofReal, map_mul,
    Complex.conj_conj, smul_eq_mul]
  by_cases h : a = b
  · subst h; simp [mul_comm]
  · have h' : b ≠ a := Ne.symm h
    simp [h, h', mul_comm]

theorem rhoR_trace (hg : IsUnit3 g) (r : ℝ) : (rhoR r g).trace = 1 := by
  simp only [rhoR, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, projP_trace hg, card_cfg3]
  simp only [smul_eq_mul]
  push_cast
  ring

theorem rhoR_sq (hg : IsUnit3 g) (r : ℝ) :
    rhoR r g * rhoR r g = ((((1 - r) / 8 : ℝ) : ℂ) * (((1 - r) / 8 : ℝ) : ℂ)) • (1 : Mat3) +
      (2 * (((1 - r) / 8 : ℝ) : ℂ) * (r : ℂ) + (r : ℂ) * (r : ℂ)) • projP g := by
  unfold rhoR
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    projP_mul hg]
  module

theorem rhoR_sq_trace (hg : IsUnit3 g) (r : ℝ) :
    (rhoR r g * rhoR r g).trace = (((1 + 7 * r ^ 2) / 8 : ℝ) : ℂ) := by
  rw [rhoR_sq hg]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, projP_trace hg, card_cfg3,
    smul_eq_mul]
  push_cast
  ring

theorem rhoR_e3 (hg : IsUnit3 g) (r : ℝ) : e3 (rhoR r g) = 7 * r ^ 2 := by
  unfold e3
  rw [rhoR_sq_trace hg, Complex.ofReal_re]
  ring

end Algebra

section Flip

variable {g : Cfg3 → ℂ}

theorem trace_mul_flip (M : Mat3) :
    (M * spinFlip3 M).trace = ∑ a, ∑ b, ∑ x, ∑ y, M a b * (Y3 b x * M y x * Y3 y a) := by
  simp only [Matrix.trace, Matrix.diag, spinFlip3, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem Y3_antisymm (a b : Cfg3) : Y3 b a = - Y3 a b := by
  rw [Y3_apply, Y3_apply, epsV_swap]; ring

theorem trace_spinFlip (M : Mat3) : (spinFlip3 M).trace = M.trace := by
  unfold spinFlip3
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Y3_mul_Y3, Matrix.one_mul,
    Matrix.trace_transpose]

/-- `tr(|g⟩⟨g| ρ̃)` vanishes for `ρ = |g⟩⟨g|`: `g^T Y^{⊗3} g = 0` by antisymmetry. -/
theorem projP_flip_trace (g : Cfg3 → ℂ) : (projP g * spinFlip3 (projP g)).trace = 0 := by
  rw [trace_mul_flip]
  set F : Cfg3 → Cfg3 → Cfg3 → Cfg3 → ℂ :=
    fun a b x y => projP g a b * (Y3 b x * projP g y x * Y3 y a) with hF
  set H : Cfg3 → Cfg3 → ℂ := fun a y => ∑ b, ∑ x, F a b x y with hH
  have h1 : ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ y, H a y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ b, ∑ x, ∑ y, F a b x y = ∑ b, ∑ y, ∑ x, F a b x y :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_comm
  have h2 : ∀ a y b x, F y b x a = - F a b x y := by
    intro a y b x
    simp only [hF, projP, Matrix.of_apply]
    rw [show Y3 a y = - Y3 y a from Y3_antisymm y a]
    ring
  have h3 : ∀ a y, H y a = - H a y := by
    intro a y
    simp only [hH]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => h2 a y b x
  have hT : ∑ a, ∑ y, H a y = - ∑ a, ∑ y, H a y := by
    calc ∑ a, ∑ y, H a y = ∑ y, ∑ a, H a y := Finset.sum_comm
      _ = ∑ a, ∑ y, H y a := rfl
      _ = ∑ a, ∑ y, - H a y := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => h3 a y
      _ = - ∑ a, ∑ y, H a y := by simp [Finset.sum_neg_distrib]
  rw [h1]
  linear_combination (1 / 2 : ℂ) * hT

theorem spinFlip_rhoR (r : ℝ) :
    spinFlip3 (rhoR r g) = (((1 - r) / 8 : ℝ) : ℂ) • (1 : Mat3) + (r : ℂ) • spinFlip3 (projP g) := by
  unfold rhoR spinFlip3
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, mul_add, add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Y3_mul_Y3]

theorem rhoR_flip_trace (hg : IsUnit3 g) (r : ℝ) :
    (rhoR r g * spinFlip3 (rhoR r g)).trace = (((1 - r ^ 2) / 8 : ℝ) : ℂ) := by
  rw [spinFlip_rhoR]
  have hexp : rhoR r g * ((((1 - r) / 8 : ℝ) : ℂ) • (1 : Mat3) + (r : ℂ) • spinFlip3 (projP g)) =
      ((((1 - r) / 8 : ℝ) : ℂ) * (((1 - r) / 8 : ℝ) : ℂ)) • (1 : Mat3) +
        ((((1 - r) / 8 : ℝ) : ℂ) * (r : ℂ)) • spinFlip3 (projP g) +
        (((r : ℂ) * (((1 - r) / 8 : ℝ) : ℂ)) • projP g +
          ((r : ℂ) * (r : ℂ)) • (projP g * spinFlip3 (projP g))) := by
    unfold rhoR
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  rw [hexp]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, card_cfg3, trace_spinFlip,
    projP_trace hg, projP_flip_trace, smul_eq_mul]
  push_cast
  ring

theorem rhoR_b3 (hg : IsUnit3 g) (r : ℝ) : b3 (rhoR r g) = 3 * r ^ 2 := by
  have h := flip_formula (rhoR r g) (rhoR_herm r) (rhoR_trace hg r)
  rw [rhoR_flip_trace hg, Complex.ofReal_re, rhoR_e3 hg] at h
  linarith

end Flip

end FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

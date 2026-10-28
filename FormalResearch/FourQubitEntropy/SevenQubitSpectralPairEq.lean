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

section Spectrum

variable {g : Cfg3 → ℂ}

/-- Every eigenvalue of `ρ_r` is `(1-r)/8` or `(1+7r)/8`, since `(ρ_r - c)(ρ_r - c - r) = 0`. -/
theorem rhoR_eig (hg : IsUnit3 g) (r : ℝ) (hρ : (rhoR r g).IsHermitian) (j : Cfg3) :
    hρ.eigenvalues j = (1 - r) / 8 ∨ hρ.eigenvalues j = (1 - r) / 8 + r := by
  set c : ℝ := (1 - r) / 8 with hc
  have hid : (rhoR r g - (c : ℂ) • (1 : Mat3)) * (rhoR r g - ((c : ℂ) + (r : ℂ)) • (1 : Mat3)) = 0 := by
    unfold rhoR
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, projP_mul hg, hc]
    module
  set u : Cfg3 → ℂ := ⇑(hρ.eigenvectorBasis j) with hu
  have hune : u ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hρ.eigenvectorBasis.orthonormal.ne_zero j
  have hev : rhoR r g *ᵥ u = ((hρ.eigenvalues j : ℝ) : ℂ) • u := by
    have := hρ.mulVec_eigenvectorBasis j
    rwa [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
  set l : ℂ := ((hρ.eigenvalues j : ℝ) : ℂ) with hl
  have h1 : (rhoR r g - ((c : ℂ) + (r : ℂ)) • (1 : Mat3)) *ᵥ u = (l - ((c : ℂ) + (r : ℂ))) • u := by
    rw [Matrix.sub_mulVec, hev, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have h2 : (rhoR r g - (c : ℂ) • (1 : Mat3)) *ᵥ ((l - ((c : ℂ) + (r : ℂ))) • u) =
      ((l - ((c : ℂ) + (r : ℂ))) * (l - (c : ℂ))) • u := by
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hev, Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul,
      smul_smul]
  have h3 : ((l - ((c : ℂ) + (r : ℂ))) * (l - (c : ℂ))) • u = 0 := by
    rw [← h2, ← h1, Matrix.mulVec_mulVec, hid, Matrix.zero_mulVec]
  have h4 : (l - ((c : ℂ) + (r : ℂ))) * (l - (c : ℂ)) = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hune
  have h5 : (hρ.eigenvalues j - (c + r)) * (hρ.eigenvalues j - c) = 0 := by
    have : (((hρ.eigenvalues j - (c + r)) * (hρ.eigenvalues j - c) : ℝ) : ℂ) = 0 := by
      push_cast; exact h4
    exact_mod_cast this
  rcases mul_eq_zero.mp h5 with h | h
  · right; linarith
  · left; linarith

/-- Shape of a one-spike sorted spectrum. -/
theorem spike_shape (l : Fin 8 → ℝ) (c r : ℝ) (hr : 0 < r) (hanti : Antitone l)
    (hmem : ∀ i, l i = c ∨ l i = c + r) (hsum : ∑ i, l i = 8 * c + r) :
    l 0 = c + r ∧ ∀ i, i ≠ 0 → l i = c := by
  have hlow : ∀ i, c ≤ l i := fun i => by rcases hmem i with h | h <;> linarith
  have h0 : l 0 = c + r := by
    rcases hmem 0 with h | h
    · exfalso
      have hall : ∀ i, l i = c := fun i => by
        have := hanti (Fin.zero_le i)
        rcases hmem i with h' | h'
        · exact h'
        · linarith
      have : ∑ i, l i = 8 * c := by
        simp [hall]
      linarith
    · exact h
  refine ⟨h0, fun i hi => ?_⟩
  rcases hmem i with h | h
  · exact h
  · exfalso
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => l j - c)
      (Finset.subset_univ {0, i}) (fun j _ _ => sub_nonneg.2 (hlow j))
    rw [Finset.sum_pair (Ne.symm hi)] at hpair
    have htot : ∑ j, (l j - c) = r := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    linarith

theorem vSpec_spike (l : Fin 8 → ℝ) (c r : ℝ) (h0 : l 0 = c + r) (h : ∀ i, i ≠ 0 → l i = c)
    (hl : ∑ i, l i = 1) : vSpec l = (2 * c + r) ^ 2 + 12 * c ^ 2 - 1 / 4 := by
  rw [vSpec_eq l hl]
  have r0 : Fin.rev (0 : Fin 8) = 7 := by decide
  have r1 : Fin.rev (1 : Fin 8) = 6 := by decide
  have r2 : Fin.rev (2 : Fin 8) = 5 := by decide
  have r3 : Fin.rev (3 : Fin 8) = 4 := by decide
  have r4 : Fin.rev (4 : Fin 8) = 3 := by decide
  have r5 : Fin.rev (5 : Fin 8) = 2 := by decide
  have r6 : Fin.rev (6 : Fin 8) = 1 := by decide
  have r7 : Fin.rev (7 : Fin 8) = 0 := by decide
  simp only [Fin.sum_univ_eight, r0, r1, r2, r3, r4, r5, r6, r7, h0, h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]
  ring

/-- `v(ρ_r) = 3 r² / 4`. -/
theorem rhoR_v3 (hg : IsUnit3 g) (r : ℝ) (hr : 0 ≤ r) :
    v3 (rhoR r g) (rhoR_herm r) = 3 * r ^ 2 / 4 := by
  set hρ := rhoR_herm (g := g) r with hρdef
  set c : ℝ := (1 - r) / 8 with hc
  have hsum : ∑ i, lam3 (rhoR r g) hρ i = 1 := by
    have := (spectral_pairing_data 8 card_cfg3 (rhoR r g) hρ 1 (by simp) (by simp)).1
    rw [rhoR_trace hg r] at this
    exact this.trans Complex.one_re
  have hmem : ∀ i, lam3 (rhoR r g) hρ i = c ∨ lam3 (rhoR r g) hρ i = c + r := by
    intro i
    have h := rhoR_eig hg r hρ (Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.cast card_cfg3.symm i))
    have e : hρ.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.cast card_cfg3.symm i)) =
        lam3 (rhoR r g) hρ i := by
      simp only [lam3, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    rw [e] at h
    exact h
  have hanti : Antitone (lam3 (rhoR r g) hρ) := fun i j hij =>
    hρ.eigenvalues₀_antitone (Fin.le_def.2 (by simpa [Fin.coe_cast] using Fin.le_def.1 hij))
  have hshape : lam3 (rhoR r g) hρ 0 = c + r ∧ ∀ i, i ≠ 0 → lam3 (rhoR r g) hρ i = c := by
    rcases hr.eq_or_lt with h | h
    · subst h
      exact ⟨by rcases hmem 0 with h' | h' <;> linarith,
        fun i _ => by rcases hmem i with h' | h' <;> linarith⟩
    · exact spike_shape _ c r h hanti hmem (by rw [hsum, hc]; ring)
  unfold v3
  rw [vSpec_spike _ c r hshape.1 hshape.2 hsum, hc]
  ring

/-- **Equality family of `prop:seven-spinflip-spectral-pair`.** For every unit `g` and `r ≥ 0`
(`r ∈ [0,1]` for density matrices), `ρ_r` satisfies `e = 7r²`, `b = 3r²`, `v = 3r²/4` and
`b = 4v`. -/
theorem rhoR_equality (hg : IsUnit3 g) (r : ℝ) (hr : 0 ≤ r) :
    e3 (rhoR r g) = 7 * r ^ 2 ∧ b3 (rhoR r g) = 3 * r ^ 2 ∧
      v3 (rhoR r g) (rhoR_herm r) = 3 * r ^ 2 / 4 ∧
      b3 (rhoR r g) = 4 * v3 (rhoR r g) (rhoR_herm r) := by
  have hv := rhoR_v3 hg r hr
  refine ⟨rhoR_e3 hg r, rhoR_b3 hg r, hv, ?_⟩
  rw [rhoR_b3 hg r, hv]; ring

end Spectrum

end FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

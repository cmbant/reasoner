import Mathlib
import FormalResearch.FrameFree.FilteredGateReal

/-!
# Filtered-gate law: rank-two Cauchy--Schwarz for a Hermitian-form hypothesis

`rk2H`: for `R : ι × ι` complex, `q_R(e) = ‖Rᵀ e‖²`, and `N = x₁⊗y₁ + x₂⊗y₂` of rank at most two,
`|Σ x₁ᵀ R y₁ + Σ x₂ᵀ R y₂|² ≤ D ‖N‖²_F` provided `q_R(e₁) + q_R(e₂) ≤ D` for every orthonormal pair
`e₁, e₂`.  (Includes the flat case `R Rᴴ = κ I`, `D = 2κ`.)  Proof: Gram--Schmidt
on `x₁, x₂`, then Cauchy--Schwarz term by term (`rk2H_orth`).
-/

open scoped Matrix ComplexConjugate BigOperators
open Finset

namespace FormalResearch.FrameFree.FTG

section RK2H

variable {ι : Type*} [Fintype ι]

/-- `‖x‖²`. -/
noncomputable def nrm2 (x : ι → ℂ) : ℝ := ∑ a, Complex.normSq (x a)

/-- `q_R(e) = ‖Rᵀ e‖²`. -/
noncomputable def qg (R : Matrix ι ι ℂ) (e : ι → ℂ) : ℝ := nrm2 (fun j => ∑ i, e i * R i j)

theorem nrm2_nonneg (x : ι → ℂ) : 0 ≤ nrm2 x := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem nrm2_smul (c : ℂ) (x : ι → ℂ) : nrm2 (fun i => c * x i) = Complex.normSq c * nrm2 x := by
  simp only [nrm2, Complex.normSq_mul, Finset.mul_sum]

theorem qg_smul (R : Matrix ι ι ℂ) (c : ℂ) (x : ι → ℂ) :
    qg R (fun i => c * x i) = Complex.normSq c * qg R x := by
  unfold qg
  have : (fun j => ∑ i, c * x i * R i j) = fun j => c * ∑ i, x i * R i j := by
    funext j; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, nrm2_smul]

theorem nrm2_eq_zero {x : ι → ℂ} (h : nrm2 x = 0) : ∀ i, x i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (x i))).1 h i
    (Finset.mem_univ i)
  simpa using this

/-- Cauchy--Schwarz for the bilinear pairing. -/
theorem normSq_dot_le (x y : ι → ℂ) :
    Complex.normSq (∑ a, x a * y a) ≤ nrm2 x * nrm2 y := by
  have h1 : ‖∑ a, x a * y a‖ ≤ ∑ a, ‖x a‖ * ‖y a‖ := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖x a‖) (fun a => ‖y a‖)
  rw [Complex.normSq_eq_norm_sq]
  have h0 : 0 ≤ ‖∑ a, x a * y a‖ := norm_nonneg _
  calc ‖∑ a, x a * y a‖ ^ 2 ≤ (∑ a, ‖x a‖ * ‖y a‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2
    _ = _ := by simp [nrm2, Complex.normSq_eq_norm_sq]

/-- A bilinear pairing: `|xᵀ R y|² ≤ q_R(x) ‖y‖²`. -/
theorem normSq_bilin_qg (R : Matrix ι ι ℂ) (x y : ι → ℂ) :
    Complex.normSq (∑ i, ∑ j, x i * R i j * y j) ≤ qg R x * nrm2 y := by
  have e : ∑ i, ∑ j, x i * R i j * y j = ∑ j, (∑ i, x i * R i j) * y j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
  rw [e]
  exact normSq_dot_le (fun j => ∑ i, x i * R i j) y

/-- A unit vector orthogonal to a given one (needs `dim ≥ 2`). -/
theorem exists_partner (hι : 1 < Fintype.card ι) (e : ι → ℂ) :
    ∃ e' : ι → ℂ, nrm2 e' = 1 ∧ ∑ i, conj (e i) * e' i = 0 := by
  let f : (ι → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun z => ∑ i, conj (e i) * z i
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a v; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring }
  have hk : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hι)
  obtain ⟨z, hz, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hz' : ∑ i, conj (e i) * z i = 0 := hz
  have hpos : 0 < nrm2 z := by
    rcases (nrm2_nonneg z).eq_or_lt with h | h
    · exact absurd (funext (nrm2_eq_zero h.symm)) hne
    · exact h
  refine ⟨fun i => ((1 / Real.sqrt (nrm2 z) : ℝ) : ℂ) * z i, ?_, ?_⟩
  · rw [nrm2_smul, Complex.normSq_ofReal]
    have hs := Real.sqrt_pos.mpr hpos
    have h := Real.mul_self_sqrt hpos.le
    field_simp
    linarith [h]
  · calc ∑ i, conj (e i) * (((1 / Real.sqrt (nrm2 z) : ℝ) : ℂ) * z i)
        = ((1 / Real.sqrt (nrm2 z) : ℝ) : ℂ) * ∑ i, conj (e i) * z i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hz', mul_zero]

/-- normalisation -/
noncomputable def hat (x : ι → ℂ) : ι → ℂ := fun i => ((1 / Real.sqrt (nrm2 x) : ℝ) : ℂ) * x i

theorem hat_nrm2 (x : ι → ℂ) (hx : nrm2 x ≠ 0) : nrm2 (hat x) = 1 := by
  have hpos : 0 < nrm2 x := lt_of_le_of_ne (nrm2_nonneg x) (Ne.symm hx)
  unfold hat
  rw [nrm2_smul, Complex.normSq_ofReal]
  have hs := Real.sqrt_pos.mpr hpos
  have h := Real.mul_self_sqrt hpos.le
  field_simp
  linarith [h]

theorem hat_qg (R : Matrix ι ι ℂ) (x : ι → ℂ) (hx : nrm2 x ≠ 0) :
    qg R (hat x) = qg R x / nrm2 x := by
  have hpos : 0 < nrm2 x := lt_of_le_of_ne (nrm2_nonneg x) (Ne.symm hx)
  unfold hat
  rw [qg_smul, Complex.normSq_ofReal]
  have hs := Real.sqrt_pos.mpr hpos
  have h := Real.mul_self_sqrt hpos.le
  field_simp
  rw [sq, h]; ring

theorem hat_orth (x₁ x₂ : ι → ℂ) (ho : ∑ i, conj (x₁ i) * x₂ i = 0) :
    ∑ i, conj (hat x₁ i) * hat x₂ i = 0 := by
  unfold hat
  have : ∑ i, conj (((1 / Real.sqrt (nrm2 x₁) : ℝ) : ℂ) * x₁ i) * (((1 / Real.sqrt (nrm2 x₂) : ℝ) : ℂ) * x₂ i)
      = (((1 / Real.sqrt (nrm2 x₁) : ℝ) : ℂ) * ((1 / Real.sqrt (nrm2 x₂) : ℝ) : ℂ)) *
        ∑ i, conj (x₁ i) * x₂ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, Complex.conj_ofReal]; ring
  rw [this, ho, mul_zero]

/-- the per-vector coefficient -/
noncomputable def tcoef (R : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ :=
  if nrm2 x = 0 then 0 else qg R x / nrm2 x

theorem tcoef_nonneg (R : Matrix ι ι ℂ) (x : ι → ℂ) : 0 ≤ tcoef R x := by
  unfold tcoef
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (nrm2_nonneg _) (nrm2_nonneg _)

theorem single_le (R : Matrix ι ι ℂ) (x y : ι → ℂ) :
    Complex.normSq (∑ i, ∑ j, x i * R i j * y j) ≤ tcoef R x * (nrm2 x * nrm2 y) := by
  unfold tcoef
  split_ifs with h
  · have hx := nrm2_eq_zero h
    have : ∑ i, ∑ j, x i * R i j * y j = 0 := by simp [hx]
    rw [this]; simp
  · have hpos : 0 < nrm2 x := lt_of_le_of_ne (nrm2_nonneg x) (Ne.symm h)
    have := normSq_bilin_qg R x y
    calc _ ≤ qg R x * nrm2 y := this
      _ = _ := by field_simp

theorem tcoef_pair (R : Matrix ι ι ℂ) (D : ℝ) (hD0 : 0 ≤ D)
    (hD1 : ∀ e : ι → ℂ, nrm2 e = 1 → qg R e ≤ D)
    (hD2 : ∀ e₁ e₂ : ι → ℂ, nrm2 e₁ = 1 → nrm2 e₂ = 1 → ∑ i, conj (e₁ i) * e₂ i = 0 →
      qg R e₁ + qg R e₂ ≤ D)
    (x₁ x₂ : ι → ℂ) (ho : ∑ i, conj (x₁ i) * x₂ i = 0) :
    tcoef R x₁ + tcoef R x₂ ≤ D := by
  by_cases h1 : nrm2 x₁ = 0
  · by_cases h2 : nrm2 x₂ = 0
    · simp [tcoef, h1, h2, hD0]
    · have : tcoef R x₂ = qg R (hat x₂) := by rw [hat_qg R x₂ h2]; simp [tcoef, h2]
      simp only [tcoef, h1, ite_true, zero_add]
      rw [← tcoef.eq_1, this]
      exact hD1 _ (hat_nrm2 x₂ h2)
  · by_cases h2 : nrm2 x₂ = 0
    · have : tcoef R x₁ = qg R (hat x₁) := by rw [hat_qg R x₁ h1]; simp [tcoef, h1]
      simp only [tcoef, h2, ite_true, add_zero]
      rw [← tcoef.eq_1, this]
      exact hD1 _ (hat_nrm2 x₁ h1)
    · have e1 : tcoef R x₁ = qg R (hat x₁) := by rw [hat_qg R x₁ h1]; simp [tcoef, h1]
      have e2 : tcoef R x₂ = qg R (hat x₂) := by rw [hat_qg R x₂ h2]; simp [tcoef, h2]
      rw [e1, e2]
      exact hD2 _ _ (hat_nrm2 x₁ h1) (hat_nrm2 x₂ h2) (hat_orth x₁ x₂ ho)

theorem rk2H_orth (R : Matrix ι ι ℂ) (D : ℝ) (hD0 : 0 ≤ D)
    (hD1 : ∀ e : ι → ℂ, nrm2 e = 1 → qg R e ≤ D)
    (hD2 : ∀ e₁ e₂ : ι → ℂ, nrm2 e₁ = 1 → nrm2 e₂ = 1 → ∑ i, conj (e₁ i) * e₂ i = 0 →
      qg R e₁ + qg R e₂ ≤ D)
    (x₁ x₂ y₁ y₂ : ι → ℂ) (ho : ∑ i, conj (x₁ i) * x₂ i = 0) :
    Complex.normSq (∑ i, ∑ j, x₁ i * R i j * y₁ j + ∑ i, ∑ j, x₂ i * R i j * y₂ j) ≤
      D * (nrm2 x₁ * nrm2 y₁ + nrm2 x₂ * nrm2 y₂) := by
  set z₁ := ∑ i, ∑ j, x₁ i * R i j * y₁ j with hz₁
  set z₂ := ∑ i, ∑ j, x₂ i * R i j * y₂ j with hz₂
  have a₁ := single_le R x₁ y₁
  have a₂ := single_le R x₂ y₂
  have hb := tcoef_pair R D hD0 hD1 hD2 x₁ x₂ ho
  have c₁ := tcoef_nonneg R x₁
  have c₂ := tcoef_nonneg R x₂
  have n1 := nrm2_nonneg x₁
  have n2 := nrm2_nonneg x₂
  have m1 := nrm2_nonneg y₁
  have m2 := nrm2_nonneg y₂
  have hB₁ : ‖z₁‖ ^ 2 ≤ tcoef R x₁ * (nrm2 x₁ * nrm2 y₁) := by
    rw [← Complex.normSq_eq_norm_sq]; exact a₁
  have hB₂ : ‖z₂‖ ^ 2 ≤ tcoef R x₂ * (nrm2 x₂ * nrm2 y₂) := by
    rw [← Complex.normSq_eq_norm_sq]; exact a₂
  have hcs := cs_two ‖z₁‖ ‖z₂‖ (tcoef R x₁) (tcoef R x₂) (nrm2 x₁ * nrm2 y₁) (nrm2 x₂ * nrm2 y₂) c₁ c₂
    (mul_nonneg n1 m1) (mul_nonneg n2 m2) hB₁ hB₂
  have htri : ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
  rw [Complex.normSq_eq_norm_sq]
  calc ‖z₁ + z₂‖ ^ 2 ≤ (‖z₁‖ + ‖z₂‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (tcoef R x₁ + tcoef R x₂) * (nrm2 x₁ * nrm2 y₁ + nrm2 x₂ * nrm2 y₂) := hcs
    _ ≤ D * (nrm2 x₁ * nrm2 y₁ + nrm2 x₂ * nrm2 y₂) :=
        mul_le_mul_of_nonneg_right hb (add_nonneg (mul_nonneg n1 m1) (mul_nonneg n2 m2))

theorem norm_orth (x₁ x₂ y₁ y₂ : ι → ℂ) (ho : ∑ i, conj (x₁ i) * x₂ i = 0) :
    ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) =
      nrm2 x₁ * nrm2 y₁ + nrm2 x₂ * nrm2 y₂ := by
  have hc : ∑ i, ∑ j, conj (x₁ i * y₁ j) * (x₂ i * y₂ j) = 0 := by
    have : ∑ i, ∑ j, conj (x₁ i * y₁ j) * (x₂ i * y₂ j) =
        (∑ i, conj (x₁ i) * x₂ i) * ∑ j, conj (y₁ j) * y₂ j := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]; ring
    rw [this, ho, zero_mul]
  have h2 : ∀ i j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) =
      Complex.normSq (x₁ i) * Complex.normSq (y₁ j) + Complex.normSq (x₂ i) * Complex.normSq (y₂ j)
      + 2 * (conj (x₁ i * y₁ j) * (x₂ i * y₂ j)).re := by
    intro i j
    have h2' : ∀ z w : ℂ, Complex.normSq (z + w) =
        Complex.normSq z + Complex.normSq w + 2 * (conj z * w).re := by
      intro z w
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    rw [h2', Complex.normSq_mul, Complex.normSq_mul]
  simp_rw [h2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, nrm2]
  have : ∑ i, ∑ j, (conj (x₁ i * y₁ j) * (x₂ i * y₂ j)).re = 0 := by
    have := congrArg Complex.re hc
    simpa [Complex.re_sum] using this
  rw [this]
  simp

/-- **Rank-two Cauchy--Schwarz with a Hermitian-form hypothesis.**  If every orthonormal pair has
`q_R(e₁) + q_R(e₂) ≤ D` (and `dim ≥ 2`), then `|Σ x₁ᵀ R y₁ + Σ x₂ᵀ R y₂|² ≤ D ‖x₁⊗y₁ + x₂⊗y₂‖²`. -/
theorem rk2H (R : Matrix ι ι ℂ) (D : ℝ) (hι : 1 < Fintype.card ι) (hD0 : 0 ≤ D)
    (hD2 : ∀ e₁ e₂ : ι → ℂ, nrm2 e₁ = 1 → nrm2 e₂ = 1 → ∑ i, conj (e₁ i) * e₂ i = 0 →
      qg R e₁ + qg R e₂ ≤ D)
    (x₁ x₂ y₁ y₂ : ι → ℂ) :
    Complex.normSq (∑ i, ∑ j, x₁ i * R i j * y₁ j + ∑ i, ∑ j, x₂ i * R i j * y₂ j) ≤
      D * ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) := by
  have hD1 : ∀ e : ι → ℂ, nrm2 e = 1 → qg R e ≤ D := by
    intro e he
    obtain ⟨e', he', ho⟩ := exists_partner hι e
    have := hD2 e e' he he' ho
    have : 0 ≤ qg R e' := nrm2_nonneg _
    linarith
  set c : ℂ := (∑ i, conj (x₁ i) * x₂ i) / (nrm2 x₁ : ℂ) with hc
  have ho : ∑ i, conj (x₁ i) * (x₂ i - c * x₁ i) = 0 := by
    by_cases hn : nrm2 x₁ = 0
    · have h0 := nrm2_eq_zero hn
      simp [h0]
    · have hn' : (nrm2 x₁ : ℂ) ≠ 0 := by exact_mod_cast hn
      have hn2 : ((nrm2 x₁ : ℝ) : ℂ) = ∑ i, conj (x₁ i) * x₁ i := by
        unfold nrm2; push_cast; simp [Complex.normSq_eq_conj_mul_self]
      have : ∑ i, conj (x₁ i) * (x₂ i - c * x₁ i) =
          ∑ i, conj (x₁ i) * x₂ i - c * (nrm2 x₁ : ℂ) := by
        rw [hn2, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this, hc, div_mul_cancel₀ _ hn', sub_self]
  have key := rk2H_orth R D hD0 hD1 hD2 x₁ (fun i => x₂ i - c * x₁ i) (fun j => y₁ j + c * y₂ j) y₂ ho
  have hnorm := norm_orth x₁ (fun i => x₂ i - c * x₁ i) (fun j => y₁ j + c * y₂ j) y₂ ho
  have e1 : ∀ i j, x₁ i * (y₁ j + c * y₂ j) + (x₂ i - c * x₁ i) * y₂ j = x₁ i * y₁ j + x₂ i * y₂ j :=
    fun i j => by ring
  have e2 : ∑ i, ∑ j, x₁ i * R i j * (y₁ j + c * y₂ j) +
      ∑ i, ∑ j, (x₂ i - c * x₁ i) * R i j * y₂ j =
      ∑ i, ∑ j, x₁ i * R i j * y₁ j + ∑ i, ∑ j, x₂ i * R i j * y₂ j := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [e1] at hnorm
  rw [e2] at key
  rw [hnorm]
  exact key

end RK2H

end FormalResearch.FrameFree.FTG

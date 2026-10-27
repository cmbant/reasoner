import Mathlib

/-!
# Rank-two Cauchy--Schwarz for flat bilinear forms

If `W Wᴴ = κ I` (a *flat* matrix: all singular values equal `√κ`) and `N_{ij} = x₁ᵢ y₁ⱼ + x₂ᵢ y₂ⱼ` has
rank at most two, then `|Σ_{ij} W_{ij} N_{ij}|² ≤ 2 κ ‖N‖²_F` (`rk2`).  This is the elementary step
behind the Kramers bound `F_C(ψ₊) ≤ 1/2` (`PsiPlusKramersCore`): the nuclear norm of a rank-two matrix is
at most `√2` times its Frobenius norm.  Proof by Gram--Schmidt on `x₁, x₂` (`rk2_orth`), no SVD.
-/

open scoped Matrix ComplexConjugate BigOperators
open Finset

namespace FormalResearch.FrameFree.PsiPlusKramers

section RK2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖x‖²`. -/
noncomputable def nrm2 (x : ι → ℂ) : ℝ := ∑ a, Complex.normSq (x a)

omit [DecidableEq ι] in
theorem nrm2_nonneg (x : ι → ℂ) : 0 ≤ nrm2 x := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

omit [DecidableEq ι] in
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

/-- A "flat" bilinear form: `W Wᴴ = κ I` scales norms of `xᵀ W` by `κ`. -/
theorem nrm2_vecMul (W : Matrix ι ι ℂ) (κ : ℝ) (hW : W * Wᴴ = (κ : ℂ) • (1 : Matrix ι ι ℂ))
    (x : ι → ℂ) : nrm2 (fun b => ∑ a, x a * W a b) = κ * nrm2 x := by
  have hentry : ∀ a a' : ι, ∑ b, conj (W a b) * W a' b = if a' = a then (κ : ℂ) else 0 := by
    intro a a'
    have := congrFun (congrFun hW a') a
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm] using this
  have h : ∀ b, (Complex.normSq (∑ a, x a * W a b) : ℂ) =
      ∑ a, ∑ a', conj (x a) * x a' * (conj (W a b) * W a' b) := by
    intro b
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    simp only [map_mul]; ring
  have key : ((nrm2 (fun b => ∑ a, x a * W a b) : ℝ) : ℂ) = ((κ * nrm2 x : ℝ) : ℂ) := by
    unfold nrm2
    push_cast
    simp_rw [h]
    have e1 : ∑ b, ∑ a, ∑ a', conj (x a) * x a' * (conj (W a b) * W a' b) =
        ∑ a, ∑ a', conj (x a) * x a' * ∑ b, conj (W a b) * W a' b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
    rw [e1]
    simp_rw [hentry]
    simp [Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  exact_mod_cast key

/-- `|xᵀ W y|² ≤ κ ‖x‖² ‖y‖²` for a flat `W`. -/
theorem normSq_bilin_le (W : Matrix ι ι ℂ) (κ : ℝ) (hW : W * Wᴴ = (κ : ℂ) • (1 : Matrix ι ι ℂ))
    (x y : ι → ℂ) :
    Complex.normSq (∑ a, ∑ b, x a * W a b * y b) ≤ κ * nrm2 x * nrm2 y := by
  have e : ∑ a, ∑ b, x a * W a b * y b = ∑ b, (∑ a, x a * W a b) * y b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  rw [e]
  refine (normSq_dot_le _ y).trans ?_
  rw [nrm2_vecMul W κ hW x]

/-- Rank-two Cauchy--Schwarz, orthogonal case. -/
theorem rk2_orth (W : Matrix ι ι ℂ) (κ : ℝ) (hW : W * Wᴴ = (κ : ℂ) • (1 : Matrix ι ι ℂ))
    (x₁ x₂ y₁ y₂ : ι → ℂ) (ho : ∑ i, conj (x₁ i) * x₂ i = 0) :
    Complex.normSq (∑ i, ∑ j, x₁ i * W i j * y₁ j + ∑ i, ∑ j, x₂ i * W i j * y₂ j) ≤
      2 * κ * ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) := by
  have hnorm : ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) =
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
  rw [hnorm]
  have h1 := normSq_bilin_le W κ hW x₁ y₁
  have h2 := normSq_bilin_le W κ hW x₂ y₂
  have h3 : ∀ z w : ℂ, Complex.normSq (z + w) ≤ 2 * (Complex.normSq z + Complex.normSq w) := by
    intro z w
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]
  refine (h3 _ _).trans ?_
  nlinarith

/-- **Rank-two Cauchy--Schwarz.**  For a flat `W` (`W Wᴴ = κ I`) and a matrix of rank at most two,
`N_{ij} = x₁ᵢ y₁ⱼ + x₂ᵢ y₂ⱼ`: `|Σ W_{ij} N_{ij}|² ≤ 2 κ ‖N‖²`. -/
theorem rk2 (W : Matrix ι ι ℂ) (κ : ℝ) (hW : W * Wᴴ = (κ : ℂ) • (1 : Matrix ι ι ℂ))
    (x₁ x₂ y₁ y₂ : ι → ℂ) :
    Complex.normSq (∑ i, ∑ j, x₁ i * W i j * y₁ j + ∑ i, ∑ j, x₂ i * W i j * y₂ j) ≤
      2 * κ * ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) := by
  set c : ℂ := (∑ i, conj (x₁ i) * x₂ i) / (nrm2 x₁ : ℂ) with hc
  have ho : ∑ i, conj (x₁ i) * (x₂ i - c * x₁ i) = 0 := by
    by_cases hn : nrm2 x₁ = 0
    · have h0 : ∀ i, x₁ i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (x₁ i))).1 hn i
          (Finset.mem_univ i)
        simpa using this
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
  have key := rk2_orth W κ hW x₁ (fun i => x₂ i - c * x₁ i) (fun j => y₁ j + c * y₂ j) y₂ ho
  have e1 : ∀ i j, x₁ i * (y₁ j + c * y₂ j) + (x₂ i - c * x₁ i) * y₂ j = x₁ i * y₁ j + x₂ i * y₂ j :=
    fun i j => by ring
  have e2 : ∑ i, ∑ j, x₁ i * W i j * (y₁ j + c * y₂ j) +
      ∑ i, ∑ j, (x₂ i - c * x₁ i) * W i j * y₂ j =
      ∑ i, ∑ j, x₁ i * W i j * y₁ j + ∑ i, ∑ j, x₂ i * W i j * y₂ j := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [e1] at key
  rwa [e2] at key

end RK2

end FormalResearch.FrameFree.PsiPlusKramers

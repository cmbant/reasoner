import FormalResearch.FourQubitEntropy.PurityLPShadow

/-!
# `S(x,y)` is the homogeneous polynomial with coefficients `S_i`

`shadowCoeff` of `PurityLPShadow.lean` is defined as a coefficient of the dehomogenised polynomial `S(1,y)`.
`shadow_homogeneous` shows this is the same as the paper's definition: for all real `x, y`,
`Σ_j A_j ((x+3y)/2)^{n-j} ((y-x)/2)^j = Σ_{i ≤ n} S_i x^{n-i} y^i`.
-/

open scoped BigOperators
open FormalResearch.FrameFree.NQubit
open Polynomial

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

theorem natDegree_shadowPoly_le (ψ : Ψ n) : (shadowPoly ψ).natDegree ≤ n := by
  unfold shadowPoly
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hp : (C (1 / 2 : ℝ) * (1 + 3 * X) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hq : (C (1 / 2 : ℝ) * (X - 1) : ℝ[X]).natDegree ≤ 1 := by compute_degree
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_mul_le.trans ?_
  have h1 : ((C (1 / 2 : ℝ) * (1 + 3 * X)) ^ (n - j)).natDegree ≤ (n - j) * 1 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ hp)
  have h2 : ((C (1 / 2 : ℝ) * (X - 1)) ^ j).natDegree ≤ j * 1 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ hq)
  omega

theorem shadow_homogeneous_ne (ψ : Ψ n) (x y : ℝ) (hx : x ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), A ψ j * (((x + 3 * y) / 2) ^ (n - j) * ((y - x) / 2) ^ j)
      = ∑ i ∈ Finset.range (n + 1), shadowCoeff ψ i * x ^ (n - i) * y ^ i := by
  set t := y / x with ht
  have hy : y = x * t := by rw [ht]; field_simp
  have h1 := eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_shadowPoly_le ψ)) t
  have h2 : (shadowPoly ψ).eval t = ∑ j ∈ Finset.range (n + 1),
      A ψ j * (((1 + 3 * t) / 2) ^ (n - j) * ((t - 1) / 2) ^ j) := by
    unfold shadowPoly
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one, eval_sub,
      eval_ofNat]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∑ j ∈ Finset.range (n + 1), A ψ j * (((1 + 3 * t) / 2) ^ (n - j) * ((t - 1) / 2) ^ j)
      = ∑ i ∈ Finset.range (n + 1), shadowCoeff ψ i * t ^ i := by
    rw [← h2, h1]; rfl
  have h4 : ∀ j ∈ Finset.range (n + 1), A ψ j * (((x + 3 * y) / 2) ^ (n - j) * ((y - x) / 2) ^ j)
      = x ^ n * (A ψ j * (((1 + 3 * t) / 2) ^ (n - j) * ((t - 1) / 2) ^ j)) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e1 : (x + 3 * y) / 2 = x * ((1 + 3 * t) / 2) := by rw [hy]; ring
    have e2 : (y - x) / 2 = x * ((t - 1) / 2) := by rw [hy]; ring
    rw [e1, e2, mul_pow, mul_pow]
    have : x ^ n = x ^ (n - j) * x ^ j := by rw [← pow_add, Nat.sub_add_cancel hj']
    rw [this]; ring
  have h5 : ∀ i ∈ Finset.range (n + 1), shadowCoeff ψ i * x ^ (n - i) * y ^ i
      = x ^ n * (shadowCoeff ψ i * t ^ i) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : x ^ n = x ^ (n - i) * x ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
    rw [this, hy, mul_pow]; ring
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, h3, Finset.sum_congr rfl h5, ← Finset.mul_sum]

/-- **`S(x,y)` has the coefficients `S_i`**: `Σ_j A_j ((x+3y)/2)^{n-j} ((y-x)/2)^j = Σ_i S_i x^{n-i} y^i`. -/
theorem shadow_homogeneous (ψ : Ψ n) (x y : ℝ) :
    ∑ j ∈ Finset.range (n + 1), A ψ j * (((x + 3 * y) / 2) ^ (n - j) * ((y - x) / 2) ^ j)
      = ∑ i ∈ Finset.range (n + 1), shadowCoeff ψ i * x ^ (n - i) * y ^ i := by
  have hc : Continuous (fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      A ψ j * (((x + 3 * y) / 2) ^ (n - j) * ((y - x) / 2) ^ j)) := by fun_prop
  have hc' : Continuous (fun x : ℝ => ∑ i ∈ Finset.range (n + 1),
      shadowCoeff ψ i * x ^ (n - i) * y ^ i) := by fun_prop
  have := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc hc'
    (fun x hx => shadow_homogeneous_ne ψ x y hx)
  exact congrFun this x

end FormalResearch.FourQubitEntropy.PurityLP

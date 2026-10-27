import FormalResearch.FrameFree.SupportRate
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators InnerProductSpace

/-!
# Zariski-closure cone, polynomial form

Namespace `FormalResearch.FrameFree.SupportRate`.  Linear-algebra translation between the two descriptions of the
Zariski-closure cone of a set `O ⊆ ℂ^N`:

* **tensor form** `z^{⊗k} ∈ W_k = span{w^{⊗k} : w ∈ O}` for all `k` (used by `eventually_proj_sq_le`);
* **polynomial form** every polynomial vanishing on the cone `ℂ·O` vanishes at `z`.

`eval_homogeneousComponent_eq_zero_of_pw_mem`: if `z^{⊗k} ∈ W_k` and the degree-`k` component of `p` vanishes on `O`,
then it vanishes at `z` (a degree-`k` form is a linear functional of the `k`-th tensor power).
`homogeneousComponent_eval_zero_of_smul`: if `p(c x) = 0` for all `c ∈ ℂ`, every homogeneous component of `p`
vanishes at `x`.  Together (`eval_eq_zero_of_pw_mem`): if `z^{⊗k} ∈ W_k` for all `k` and `p` vanishes on `ℂ·O`
then `p(z) = 0`.  No hypothesis.
-/

namespace FormalResearch.FrameFree.SupportRate

open MvPolynomial

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Every monomial is the product of the entries of a list of variables. -/
theorem exists_list_monomial (d : N →₀ ℕ) :
    ∃ l : List N, l.length = d.degree ∧
      ∀ w : N → ℂ, (l.map w).prod = d.prod fun x e => w x ^ e := by
  induction d using Finsupp.induction_linear with
  | zero => exact ⟨[], by simp, fun w => by simp⟩
  | add f g hf hg =>
    obtain ⟨l1, h1, e1⟩ := hf
    obtain ⟨l2, h2, e2⟩ := hg
    refine ⟨l1 ++ l2, by simp [h1, h2, map_add], fun w => ?_⟩
    rw [List.map_append, List.prod_append, e1, e2,
      Finsupp.prod_add_index' (fun x => pow_zero _) (fun x a b => pow_add _ _ _)]
  | single a b =>
    refine ⟨List.replicate b a, by simp [Finsupp.degree_single], fun w => ?_⟩
    rw [List.map_replicate, List.prod_replicate]
    exact (Finsupp.prod_single_index (h := fun x e => w x ^ e) (pow_zero _)).symm

/-- The degree-`k` component of a polynomial is a linear functional of the `k`-th tensor power. -/
theorem exists_functional (k : ℕ) (p : MvPolynomial N ℂ) :
    ∃ c : (Fin k → N) → ℂ, ∀ w : N → ℂ,
      eval w (homogeneousComponent k p) = ∑ β, c β * ∏ j, w (β j) := by
  classical
  set S : Finset (N →₀ ℕ) := p.support.filter fun d => d.degree = k with hS
  have hβ : ∀ d : S, ∃ β : Fin k → N, ∀ w : N → ℂ,
      ∏ j, w (β j) = d.1.prod fun x e => w x ^ e := by
    intro d
    have hd : d.1.degree = k := (Finset.mem_filter.1 d.2).2
    obtain ⟨l, hl, e⟩ := exists_list_monomial d.1
    have hl' : l.length = k := hl.trans hd
    refine ⟨fun j => l.get (Fin.cast hl'.symm j), fun w => ?_⟩
    rw [← e w]
    have : List.ofFn (fun j : Fin k => w (l.get (Fin.cast hl'.symm j))) = l.map w := by
      subst hl'
      simp
    rw [← this, List.prod_ofFn]
  choose β hβ using hβ
  refine ⟨fun b => ∑ d : S, p.coeff d.1 * if b = β d then 1 else 0, fun w => ?_⟩
  rw [homogeneousComponent_apply, map_sum, ← hS, ← Finset.sum_coe_sort S]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [eval_monomial, ← hβ d w]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']

/-- If `z^{⊗k} ∈ W_k` and the degree-`k` component of `p` vanishes on `O`, it vanishes at `z`. -/
theorem eval_homogeneousComponent_eq_zero_of_pw_mem (O : Set (V N)) (z : V N) (k : ℕ)
    (hz : pw z k ∈ W O k) (p : MvPolynomial N ℂ)
    (hO : ∀ w ∈ O, eval (WithLp.ofLp w) (homogeneousComponent k p) = 0) :
    eval (WithLp.ofLp z) (homogeneousComponent k p) = 0 := by
  obtain ⟨c, hc⟩ := exists_functional k p
  have key : ∀ T ∈ W O k, ∑ β, c β * T β = 0 := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨w, hw, rfl⟩ := hT
      have := hO w hw
      rw [hc] at this
      simpa [pw] using this
    | zero => simp
    | add T T' _ _ h h' => simp [mul_add, Finset.sum_add_distrib, h, h']
    | smul a T _ h =>
      simp only [PiLp.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [← Finset.mul_sum, h, mul_zero]
  rw [hc]
  simpa [pw] using key _ hz

/-- If `p(c x) = 0` for all `c ∈ ℂ`, every homogeneous component of `p` vanishes at `x`. -/
theorem homogeneousComponent_eval_zero_of_smul (p : MvPolynomial N ℂ) (x : N → ℂ)
    (h : ∀ c : ℂ, eval (c • x) p = 0) (k : ℕ) : eval x (homogeneousComponent k p) = 0 := by
  have hsm : ∀ (i : ℕ) (c : ℂ), eval (c • x) (homogeneousComponent i p) =
      c ^ i * eval x (homogeneousComponent i p) := by
    intro i c
    rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg : d.degree = i := (Finset.mem_filter.1 hd).2
    simp only [eval_monomial, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finsupp.prod_mul, Finsupp.prod_pow]
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, hdeg]
    ring
  set D := p.totalDegree
  set Q : Polynomial ℂ := ∑ i ∈ Finset.range (D + 1),
    Polynomial.C (eval x (homogeneousComponent i p)) * Polynomial.X ^ i with hQ
  have hQe : ∀ c : ℂ, Q.eval c = 0 := by
    intro c
    have := h c
    rw [← sum_homogeneousComponent p, map_sum] at this
    rw [hQ, Polynomial.eval_finset_sum]
    simp only [hsm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hQ0 : Q = 0 := Polynomial.funext fun c => by simp [hQe c]
  have hk := congrArg (fun q : Polynomial ℂ => q.coeff k) hQ0
  simp only [hQ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hk
  by_cases hkD : k ∈ Finset.range (D + 1)
  · simpa [hkD] using hk
  · have : D < k := by simpa [Finset.mem_range, not_lt, Nat.lt_succ_iff] using hkD
    rw [homogeneousComponent_eq_zero k p this]
    simp

/-- **Tensor form ⟹ polynomial form of the Zariski-closure cone.**  If `z^{⊗k} ∈ W_k` for all `k`, every
polynomial vanishing on the cone `ℂ·O` vanishes at `z`. -/
theorem eval_eq_zero_of_pw_mem (O : Set (V N)) (z : V N) (hz : ∀ k, pw z k ∈ W O k)
    (p : MvPolynomial N ℂ) (hO : ∀ w ∈ O, ∀ c : ℂ, eval (c • WithLp.ofLp w) p = 0) :
    eval (WithLp.ofLp z) p = 0 := by
  rw [← sum_homogeneousComponent p, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  exact eval_homogeneousComponent_eq_zero_of_pw_mem O z k (hz k) p fun w hw =>
    homogeneousComponent_eval_zero_of_smul p _ (hO w hw) k

end FormalResearch.FrameFree.SupportRate

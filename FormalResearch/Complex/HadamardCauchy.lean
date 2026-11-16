module

public import Mathlib

/-!
# Analytic utilities for the Hadamard factorization (Cauchy estimates, logarithms, polynomials)

All **proved**; generic statements used by `HadamardBlaschke` and `HadamardFactorization`.

* `Hadamard.norm_iteratedDeriv_le_ball`: Cauchy estimate `‖h^{(n)}(z)‖ ≤ n! A (4/R)^n` for `‖z‖ < R/4`
  if `‖h‖ ≤ A` on `‖w‖ < R/2` (from Mathlib's `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`).
* `Hadamard.exists_log_ball`: a zero-free holomorphic function on a disc has a holomorphic logarithm whose real part is
  `log ‖g‖` and whose value at the centre is `log ‖g 0‖` (primitive of `g'/g`, `DifferentiableOn.isExactOn_ball`).
* `Hadamard.iteratedDeriv_poly_zero`, `Hadamard.exists_poly_of_iteratedDeriv_eq_zero`: `p`-th derivative zero on a
  connected open set iff polynomial of degree `< p`.
* `Hadamard.tendstoLocallyUniformlyOn_iteratedDeriv`: iterated derivatives of locally uniformly convergent
  holomorphic sequences converge locally uniformly.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators

namespace FormalResearch.Hadamard

/-- Cauchy's estimate for the `n`-th derivative on `‖z‖ < R/4` from a bound on `‖w‖ < R/2`. -/
lemma norm_iteratedDeriv_le_ball {h : ℂ → ℂ} {R A : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (ball 0 R)) (hA : ∀ w ∈ ball (0 : ℂ) (R / 2), ‖h w‖ ≤ A)
    {z : ℂ} (hz : ‖z‖ < R / 4) (n : ℕ) :
    ‖iteratedDeriv n h z‖ ≤ n.factorial * A * (4 / R) ^ n := by
  have hr : 0 < R / 4 := by positivity
  have hsub : closedBall z (R / 4) ⊆ ball (0 : ℂ) (R / 2) := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [mem_ball_zero_iff]
    have : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
    linarith
  have hsub2 : closedBall z (R / 4) ⊆ ball (0 : ℂ) R := hsub.trans (ball_subset_ball (by linarith))
  have hdc : DiffContOnCl ℂ h (ball z (R / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hr.ne']
    exact hd.mono hsub2
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdc
    (C := A) (fun w hw => hA w (hsub (sphere_subset_closedBall hw)))
  refine this.trans (le_of_eq ?_)
  have e : (4 / R) ^ n = ((R / 4) ^ n)⁻¹ := by rw [← inv_pow, inv_div]
  rw [e, div_eq_mul_inv]

/-- A zero-free holomorphic function on a disc has a holomorphic logarithm (up to a constant phase) with
`Re H = log ‖g‖` and `H 0 = log ‖g 0‖`. -/
lemma exists_log_ball {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 R) ∧
      (∀ w ∈ ball (0 : ℂ) R, deriv H w = deriv g w / g w) ∧
      H 0 = (Real.log ‖g 0‖ : ℂ) ∧ ∀ w ∈ ball (0 : ℂ) R, (H w).re = Real.log ‖g w‖ := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hq : DifferentiableOn ℂ (fun w => deriv g w / g w) (ball 0 R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨H, hH0, hH⟩ := (hq.isExactOn_ball).with_val_at 0 (Real.log ‖g 0‖ : ℂ)
  have hHd : DifferentiableOn ℂ H (ball 0 R) := fun w hw => (hH w hw).differentiableAt.differentiableWithinAt
  refine ⟨H, hHd, fun w hw => (hH w hw).deriv, hH0, ?_⟩
  -- exp H / g is constant
  have hu : DifferentiableOn ℂ (fun w => cexp (H w) / g w) (ball 0 R) :=
    hHd.cexp.div hg hne
  have hderiv : (ball (0 : ℂ) R).EqOn (deriv (fun w => cexp (H w) / g w)) 0 := by
    intro w hw
    have h1 : HasDerivAt H (deriv g w / g w) w := hH w hw
    have h2 : HasDerivAt g (deriv g w) w :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h3 := (h1.cexp).div h2 (hne w hw)
    have h4 : deriv (fun w => cexp (H w) / g w) w = _ := h3.deriv
    rw [h4]
    have := hne w hw
    simp only [Pi.zero_apply]
    field_simp
    ring
  intro w hw
  have hw' := (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) R)).is_const_of_deriv_eq_zero
    (convex_ball _ _).isPreconnected hu hderiv hw h0
  simp only [hH0] at hw'
  have hg0 : g 0 ≠ 0 := hne 0 h0
  have hgw : g w ≠ 0 := hne w hw
  have hnorm : ‖cexp (H w)‖ = ‖g w‖ := by
    have h4 : ‖cexp (H w) / g w‖ = ‖cexp (↑(Real.log ‖g 0‖)) / g 0‖ := by rw [hw']
    rw [norm_div, norm_div, Complex.norm_exp, Complex.norm_exp] at h4
    simp only [Complex.ofReal_re] at h4
    rw [Real.exp_log (norm_pos_iff.mpr hg0)] at h4
    have hn0 : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
    have hnw : 0 < ‖g w‖ := norm_pos_iff.mpr hgw
    rw [Complex.norm_exp]
    field_simp at h4
    nlinarith [h4]
  rw [Complex.norm_exp] at hnorm
  rw [← Real.log_exp (H w).re, hnorm]

/-- `p`-th derivative of a polynomial of degree `< p` vanishes. -/
lemma iteratedDeriv_poly_zero (p : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    iteratedDeriv p (fun w : ℂ => ∑ k ∈ range p, c k * w ^ k) z = 0 := by
  rw [iteratedDeriv_fun_sum (fun k _ => by fun_prop)]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  have : k.descFactorial p = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hk)
  simp [this]

/-- Iterated derivatives of locally uniformly convergent holomorphic sequences converge locally uniformly. -/
lemma tendstoLocallyUniformlyOn_iteratedDeriv {κ : Type*} {φ : Filter κ} [φ.NeBot]
    {U : Set ℂ} (hU : IsOpen U) :
    ∀ (k : ℕ) (F : κ → ℂ → ℂ) (f : ℂ → ℂ), (∀ n, DifferentiableOn ℂ (F n) U) →
      TendstoLocallyUniformlyOn F f φ U →
      TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) φ U := by
  intro k
  induction k with
  | zero => intro F f _ h; simpa using h
  | succ k ih =>
    intro F f hF hlim
    have h1 := hlim.deriv (Eventually.of_forall hF) hU
    have := ih (fun n => deriv (F n)) (deriv f) (fun n => (hF n).deriv hU) h1
    simpa [iteratedDeriv_succ'] using this

/-- A holomorphic function on a connected open set with vanishing `p`-th derivative is a polynomial of
degree `< p` there. -/
lemma exists_poly_of_iteratedDeriv_eq_zero {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) :
    ∀ (p : ℕ) (G : ℂ → ℂ), DifferentiableOn ℂ G U → (∀ z ∈ U, iteratedDeriv p G z = 0) →
      ∃ c : ℕ → ℂ, ∀ z ∈ U, G z = ∑ k ∈ range p, c k * z ^ k := by
  intro p
  induction p with
  | zero => intro G _ h; exact ⟨fun _ => 0, fun z hz => by simpa using h z hz⟩
  | succ p ih =>
    intro G hG h
    have hdG : DifferentiableOn ℂ (deriv G) U := hG.deriv hU
    obtain ⟨c, hc⟩ := ih (deriv G) hdG (fun z hz => by
      rw [← iteratedDeriv_succ']; exact h z hz)
    set Q : ℂ → ℂ := fun z => ∑ k ∈ range p, (c k / ((k : ℂ) + 1)) * z ^ (k + 1) with hQ
    have hQd : ∀ z, HasDerivAt Q (∑ k ∈ range p, c k * z ^ k) z := by
      intro z
      refine HasDerivAt.fun_sum (fun k _ => ?_)
      have h1 := (hasDerivAt_pow (k + 1) z).const_mul (c k / ((k : ℂ) + 1))
      convert h1 using 1
      have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      field_simp
    have hQdiff : DifferentiableOn ℂ Q U := fun z _ => (hQd z).differentiableAt.differentiableWithinAt
    obtain ⟨a, ha⟩ := hU.exists_eq_add_of_deriv_eq hUc hG hQdiff (fun z hz => by
      rw [(hQd z).deriv]; exact hc z hz)
    refine ⟨fun k => if k = 0 then a else c (k - 1) / (k : ℂ), fun z hz => ?_⟩
    rw [ha hz, Finset.sum_range_succ']
    simp only [hQ, ite_true, pow_zero, mul_one, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    push_cast
    rfl

end FormalResearch.Hadamard

module

public import FormalResearch.Complex.HadamardBlaschke

/-!
# The core estimate of the Hadamard factorization (milestone H3')

Statement formalised (the "derivative form" of Hadamard's argument, cf. Boas, *Entire functions*, Ch. 2, and the
Poisson–Jensen proof in Conway, VII.5): for `f` entire, `f 0 ≠ 0`, `R > 0` with no zero of `f` on `‖z‖ = R` and
`‖f‖ ≤ M` (`M ≥ 1`) on `‖z‖ = R`, writing `T = {i | ‖a_i‖ < R}`, for every `z` with `‖z‖ < R/4`, `f z ≠ 0`,

`‖ (d/dz)^p ( f'/f(w) - Σ_{i ∈ T} (w/a_i)^p/(w - a_i) ) |_{w = z} ‖`
`    ≤ ( (p+1)! (5 log M + 2 + 3|log ‖f 0‖|) 4^{p+1} + #T · p! · (4/3)^{p+1} ) / R^{p+1}`.

(`Hadamard.core_estimate`.)  The point is that the sum `Σ (w/a_i)^p/(w - a_i)` is the logarithmic derivative of the
genus-`p` canonical product; no lower bound for canonical products (Cartan / minimum modulus) is needed.
Proof: finite Blaschke decomposition (`HadamardBlaschke`), Borel–Carathéodory + Cauchy for the zero-free part, and
explicit `p`-th derivatives of `1/(c w + d)`.  **Proved.**
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical Nat

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- Per-zero polynomial identity: `1/(w-a) - (w/a)^p/(w-a) = - Σ_{k<p} a^{-(k+1)} w^k`. -/
lemma sub_pow_div_eq (p : ℕ) {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ a) :
    1 / (w - a) - (w / a) ^ p / (w - a) = -∑ k ∈ range p, ((a ^ (k + 1))⁻¹) * w ^ k := by
  have hwa : w - a ≠ 0 := sub_ne_zero.mpr hw
  have hgeo := geom_sum_mul_neg (w / a) p
  have h1 : 1 / (w - a) - (w / a) ^ p / (w - a) = (1 - (w / a) ^ p) / (w - a) := by ring
  rw [h1, ← hgeo]
  have h2 : (1 - w / a) = -(w - a) / a := by field_simp; ring
  rw [h2]
  have h3 : ∀ k ∈ range p, (w / a) ^ k = (a ^ k)⁻¹ * w ^ k := fun k _ => by
    rw [div_pow]; ring
  rw [Finset.sum_congr rfl h3]
  have h4 : ∑ k ∈ range p, ((a ^ (k + 1))⁻¹) * w ^ k =
      (∑ k ∈ range p, (a ^ k)⁻¹ * w ^ k) / a := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ]; field_simp
  rw [h4]
  field_simp

/-- The `p`-th derivative of a Blaschke term. -/
lemma norm_iteratedDeriv_blaschke_term {R : ℝ} (hR : 0 < R) {u z : ℂ} (hu : ‖u‖ < R)
    (hz : ‖z‖ < R / 4) (p : ℕ) :
    ‖iteratedDeriv p (fun w : ℂ => conj u / ((R : ℂ) ^ 2 - conj u * w)) z‖ ≤
      p.factorial * (4 / (3 * R)) ^ (p + 1) := by
  have hfun : (fun w : ℂ => conj u / ((R : ℂ) ^ 2 - conj u * w)) =
      fun w => conj u * ((-conj u) * w + (R : ℂ) ^ 2)⁻¹ := by
    funext w; rw [div_eq_mul_inv]; congr 2; ring
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  have hD : 3 * R ^ 2 / 4 ≤ ‖(-conj u) * z + (R : ℂ) ^ 2‖ := by
    have e : (-conj u) * z + (R : ℂ) ^ 2 = (R : ℂ) ^ 2 - conj u * z := by ring
    rw [e]
    have h1 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj u * z)
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_mul,
      Complex.norm_conj] at h1
    have h2 : ‖u‖ * ‖z‖ ≤ R * (R / 4) := by
      apply mul_le_mul hu.le hz.le (norm_nonneg _) hR.le
    nlinarith
  have hnorm : ∀ x : ℂ, ‖(-conj x)‖ = ‖x‖ := fun x => by rw [norm_neg, Complex.norm_conj]
  simp only [norm_mul, norm_pow, hnorm, Complex.norm_conj, norm_zpow, norm_natCast, norm_one,
    one_pow, one_mul, norm_neg]
  set D := ‖(-conj u) * z + (R : ℂ) ^ 2‖ with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hexp : (-1 - (p : ℤ)) = -((p + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hexp, zpow_neg, zpow_natCast]
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hpow1 : (D ^ (p + 1))⁻¹ ≤ ((3 * R ^ 2 / 4) ^ (p + 1))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hD _)
  have hpow2 : ‖u‖ ^ (p + 1) ≤ R ^ (p + 1) := pow_le_pow_left₀ hu0 hu.le _
  calc ‖u‖ * (↑p ! * ‖u‖ ^ p * (D ^ (p + 1))⁻¹) = (p ! : ℝ) * (‖u‖ ^ (p + 1) * (D ^ (p + 1))⁻¹) := by
        ring
    _ ≤ (p ! : ℝ) * (R ^ (p + 1) * ((3 * R ^ 2 / 4) ^ (p + 1))⁻¹) := by
        gcongr
    _ = (p ! : ℝ) * (4 / (3 * R)) ^ (p + 1) := by
        congr 1
        rw [← inv_pow, ← mul_pow]
        congr 1
        field_simp

section core

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {R : ℝ} (hR : 0 < R) (hsph : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0)
  (hT : {i | a i ∈ ball (0 : ℂ) R}.Finite)
  {M : ℝ} (hM1 : 1 ≤ M) (hM : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M)
include hf h0 L hR hsph hT hM1 hM

/-- **Core estimate.** -/
theorem core_estimate (p : ℕ) {z : ℂ} (hz : ‖z‖ < R / 4) (hfz : f z ≠ 0) :
    ‖iteratedDeriv p (fun w => logDeriv f w -
        ∑ i ∈ hT.toFinset, (w / a i) ^ p / (w - a i)) z‖ ≤
      ((p + 1).factorial * (5 * Real.log M + 2 + 3 * |Real.log ‖f 0‖|) * 4 ^ (p + 1) +
        hT.toFinset.card * p.factorial * (4 / 3) ^ (p + 1)) / R ^ (p + 1) := by
  obtain ⟨g, hgan, hgne, hgdec⟩ := exists_blaschke hf h0 L hR hsph hT
  obtain ⟨H, hHd, hHder, hHb⟩ := exists_log_bound h0 L hR hsph hT hgan hgne hgdec hM hM1
  set T := hT.toFinset with hTdef
  set c : ℕ → ℂ := fun k => ∑ i ∈ T, ((a i) ^ (k + 1))⁻¹ with hc
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hHdiff : AnalyticOnNhd ℂ H (ball 0 R) := hHd.analyticOnNhd isOpen_ball
  have hdHan : AnalyticAt ℂ (deriv H) z := (hHdiff.deriv) z hzR
  have hBt : ∀ i ∈ T, ‖a i‖ < R := fun i hi => by simpa using hT.mem_toFinset.mp hi
  have hBan : ∀ i ∈ T, AnalyticAt ℂ (fun w : ℂ => conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) z := by
    intro i hi
    refine analyticAt_const.div (by fun_prop) ?_
    intro h
    have h1 : conj (a i) * z = (R : ℂ) ^ 2 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le] at h2
    have h3 : ‖a i‖ * ‖z‖ ≤ R * (R / 4) :=
      mul_le_mul (hBt i hi).le hz.le (norm_nonneg _) hR.le
    nlinarith
  have hev : (fun w => logDeriv f w - ∑ i ∈ T, (w / a i) ^ p / (w - a i)) =ᶠ[𝓝 z]
      fun w => (deriv H w + ∑ i ∈ T, conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w))
        - ∑ k ∈ range p, c k * w ^ k := by
    have h1 : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) R := isOpen_ball.mem_nhds hzR
    have h2 : ∀ᶠ w in 𝓝 z, f w ≠ 0 := hf.continuous.continuousAt.eventually_ne hfz
    filter_upwards [h1, h2] with w hw1 hw2
    have hw : ‖w‖ < R := by simpa using hw1
    rw [logDeriv_eq_blaschke hf h0 L hR hT hgdec hw hw2, ← hHder w hw1]
    have hwa : ∀ i, w ≠ a i := fun i h => hw2 (h ▸ L.f_a hf h0 i)
    have key : ∑ i ∈ T, (1 / (w - a i) - (w / a i) ^ p / (w - a i)) =
        -∑ k ∈ range p, c k * w ^ k := by
      have : ∀ i ∈ T, (1 / (w - a i) - (w / a i) ^ p / (w - a i)) =
          -∑ k ∈ range p, ((a i ^ (k + 1))⁻¹) * w ^ k := fun i _ =>
        sub_pow_div_eq p (L.ne_zero i) (hwa i)
      rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hc]; simp only [Finset.sum_mul]
    have e1 : ∑ i ∈ T, (1 / (w - a i) + conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w))
        = ∑ i ∈ T, (1 / (w - a i)) + ∑ i ∈ T, conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w) :=
      Finset.sum_add_distrib
    have e2 : ∑ i ∈ T, (1 / (w - a i) - (w / a i) ^ p / (w - a i)) =
        ∑ i ∈ T, (1 / (w - a i)) - ∑ i ∈ T, (w / a i) ^ p / (w - a i) := Finset.sum_sub_distrib _ _
    rw [e1]
    linear_combination key - e2
  rw [hev.iteratedDeriv_eq]
  have hcd1 : ContDiffAt ℂ p (deriv H) z := hdHan.contDiffAt
  have hcd2 : ∀ i ∈ T, ContDiffAt ℂ p
      (fun w : ℂ => conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) z := fun i hi =>
    (hBan i hi).contDiffAt
  have hcd3 : ContDiffAt ℂ p
      (fun w : ℂ => ∑ i ∈ T, conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) z :=
    ContDiffAt.sum hcd2
  have hcd4 : ContDiffAt ℂ p (fun w : ℂ => ∑ k ∈ range p, c k * w ^ k) z := by fun_prop
  rw [iteratedDeriv_fun_sub (hcd1.add hcd3) hcd4, iteratedDeriv_fun_add hcd1 hcd3,
    iteratedDeriv_fun_sum hcd2, iteratedDeriv_poly_zero, sub_zero]
  have hA : ∀ w ∈ ball (0 : ℂ) (R / 2), ‖H w‖ ≤ 5 * Real.log M + 2 + 3 * |Real.log ‖f 0‖| :=
    fun w hw => hHb w (by simpa using hw)
  have hb1 : ‖iteratedDeriv p (deriv H) z‖ ≤ (p + 1).factorial *
      (5 * Real.log M + 2 + 3 * |Real.log ‖f 0‖|) * (4 / R) ^ (p + 1) := by
    rw [← iteratedDeriv_succ']
    exact norm_iteratedDeriv_le_ball hR hHd hA hz (p + 1)
  have hb2 : ‖∑ i ∈ T, iteratedDeriv p
      (fun w : ℂ => conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) z‖ ≤
      T.card * (p.factorial * (4 / (3 * R)) ^ (p + 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ T, ‖iteratedDeriv p
          (fun w : ℂ => conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) z‖
        ≤ ∑ i ∈ T, (p.factorial * (4 / (3 * R)) ^ (p + 1)) :=
          Finset.sum_le_sum fun i hi => norm_iteratedDeriv_blaschke_term hR (hBt i hi) hz p
      _ = T.card * (p.factorial * (4 / (3 * R)) ^ (p + 1)) := by simp
  refine (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans (le_of_eq ?_))
  have hRp : (R ^ (p + 1)) ≠ 0 := by positivity
  simp only [div_pow, mul_pow]
  field_simp

end core

end FormalResearch.Hadamard

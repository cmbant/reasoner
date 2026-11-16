module

public import FormalResearch.Complex.HadamardListing
public import FormalResearch.Complex.HadamardCauchy

/-!
# Finite Blaschke decomposition of an entire function on a disc (Hadamard factorization, milestone H3')

Statement formalised: for `f` entire, `f 0 ≠ 0`, and a radius `R > 0` with no zero of `f` on `‖z‖ = R`, write
`B_R(z) = ∏_{‖a_i‖<R} canonicalFactor R (a_i) z` (Mathlib's Blaschke-type factors
`(R² - conj a z)/(R (z - a))`, of modulus one on `‖z‖ = R`, so that `f = g_R / B_R`).  Then:

* `Hadamard.exists_blaschke`: there is `g` holomorphic and zero-free near `‖z‖ ≤ R` with `g = B_R f` there
  (Mathlib's extended canonical decomposition `MeromorphicOn.exists_ecanonicalDecomp`, repackaged along a `Listing`);
* `Hadamard.logDeriv_eq_blaschke`: for `‖w‖ < R`, `f w ≠ 0`:
  `f'/f (w) = Σ_{‖a_i‖<R} (1/(w - a_i) + conj a_i/(R² - conj a_i w)) + h'(w)`, where `h` is a holomorphic logarithm of `g`
  on the disc with `Re h = log ‖g‖`, `h 0 = log ‖g 0‖`;
* `Hadamard.norm_g_le`, `Hadamard.norm_h_le`: `‖g‖ ≤ M` on the disc if `‖f‖ ≤ M` on the circle, and (Borel–Carathéodory,
  Mathlib's `Complex.borelCaratheodory`) `‖h‖ ≤ 5 log M + 2 + 3 |log ‖f 0‖|` on `‖z‖ < R/2`.

All **proved**.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical

namespace FormalResearch.Hadamard

variable {ι : Type*}

section decomp

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {R : ℝ} (hR : 0 < R) (hsph : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0)
  (hT : {i | a i ∈ ball (0 : ℂ) R}.Finite)
include hf h0 L hR hsph

/-- The finite Blaschke decomposition `g = (∏_{‖a_i‖<R} canonicalFactor R (a i)) · f` with `g` holomorphic and
zero-free on the closed disc. -/
lemma exists_blaschke :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧ (∀ w ∈ closedBall (0 : ℂ) R, g w ≠ 0) ∧
      ∀ w ∈ closedBall (0 : ℂ) R, f w ≠ 0 →
        g w = (∏ i ∈ hT.toFinset, canonicalFactor R (a i) w) * f w := by
  have hmer : MeromorphicOn f (closedBall 0 R) := fun w _ => (hf.analyticAt w).meromorphicAt
  have hord : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf.analyticAt u).meromorphicOrderAt_eq]
    have := order_ne_top hf h0 u
    simpa using this
  obtain ⟨g, D⟩ := hmer.exists_ecanonicalDecomp hord
  refine ⟨g, D.analyticOnNhd, D.ne_zero, fun w hw hfw => ?_⟩
  have hord0 : meromorphicOrderAt f w = 0 := by
    rw [(hf.analyticAt w).meromorphicOrderAt_eq]
    have : analyticOrderAt f w = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hfw
    simp [this]
  rw [D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt hw hord0 hR,
    (hf.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hfw]
  have hsphere : ∀ u : ℂ, MeromorphicOn.divisor f (sphere (0 : ℂ) R) u = 0 := by
    intro u
    rw [divisor_apply_entire hf h0]
    by_cases hu : u ∈ sphere (0 : ℂ) R
    · simp only [hu, ↓reduceIte]
      have hfu : f u ≠ 0 := hsph u (by simpa using hu)
      have : analyticOrderNatAt f u = 0 := by
        by_contra hne
        exact hfu ((ordNat_pos_iff hf h0 u).mp (Nat.pos_of_ne_zero hne))
      simp [this]
    · simp only [hu, ↓reduceIte]
  have h1 : (∏ᶠ i : ℂ, (w - i) ^ ((-MeromorphicOn.divisor f (sphere (0 : ℂ) R)) i)) = 1 := by
    simp [hsphere]
  have h2 : (∏ᶠ u : ℂ, canonicalFactor R u w ^ (MeromorphicOn.divisor f (ball (0 : ℂ) R) u))
      = ∏ i ∈ hT.toFinset, canonicalFactor R (a i) w := by
    have := Listing.prod_idx hf h0 L (ball (0 : ℂ) R) hT (fun u => canonicalFactor R u w)
    rw [this]
    refine finprod_congr fun u => ?_
    rw [divisor_apply_entire hf h0]
    by_cases hu : u ∈ ball (0 : ℂ) R <;> simp [hu, zpow_natCast]
  rw [h1, h2, mul_one, smul_eq_mul]

end decomp

/-- Logarithmic derivative of a canonical factor. -/
lemma logDeriv_canonicalFactor {R : ℝ} (hR : R ≠ 0) {u w : ℂ} (hwu : w ≠ u)
    (hne : (R : ℂ) ^ 2 - conj u * w ≠ 0) :
    logDeriv (canonicalFactor R u) w = -(conj u / ((R : ℂ) ^ 2 - conj u * w)) - 1 / (w - u) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hwu' : w - u ≠ 0 := sub_ne_zero.mpr hwu
  have hN : HasDerivAt (fun z : ℂ => (R : ℂ) ^ 2 - conj u * z) (-conj u) w := by
    simpa using ((hasDerivAt_id w).const_mul (conj u)).const_sub ((R : ℂ) ^ 2)
  have hD : HasDerivAt (fun z : ℂ => (R : ℂ) * (z - u)) R w := by
    simpa using ((hasDerivAt_id w).sub_const u).const_mul (R : ℂ)
  have hq := hN.div hD (mul_ne_zero hR' hwu')
  have h2 : deriv (canonicalFactor R u) w = _ := hq.deriv
  rw [logDeriv_apply, h2, canonicalFactor_apply]
  field_simp

section logderiv

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {R : ℝ} (hR : 0 < R) (hT : {i | a i ∈ ball (0 : ℂ) R}.Finite)
  {g : ℂ → ℂ}
  (hgdec : ∀ w ∈ closedBall (0 : ℂ) R, f w ≠ 0 →
    g w = (∏ i ∈ hT.toFinset, canonicalFactor R (a i) w) * f w)
include hf h0 L hR hgdec

/-- Logarithmic derivative of `f` inside the disc: Blaschke terms plus `g'/g`. -/
lemma logDeriv_eq_blaschke {w : ℂ} (hw : ‖w‖ < R) (hfw : f w ≠ 0) :
    logDeriv f w = logDeriv g w + ∑ i ∈ hT.toFinset,
      (1 / (w - a i) + conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) := by
  have hwb : w ∈ ball (0 : ℂ) R := by simpa using hw
  have hwc : w ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hwb
  have hai : ∀ i ∈ hT.toFinset, a i ∈ ball (0 : ℂ) R := fun i hi => by
    simpa using hT.mem_toFinset.mp hi
  have hwa : ∀ i, w ≠ a i := fun i h => hfw (h ▸ L.f_a hf h0 i)
  have hcf_ne : ∀ i ∈ hT.toFinset, canonicalFactor R (a i) w ≠ 0 := fun i hi =>
    canonicalFactor_ne_zero (hai i hi) hwc (hwa i)
  have hcf_diff : ∀ i ∈ hT.toFinset, DifferentiableAt ℂ (canonicalFactor R (a i)) w := fun i _ =>
    ((analyticOnNhd_canonicalFactor R (a i)) w (hwa i)).differentiableAt
  set P : ℂ → ℂ := fun z => ∏ i ∈ hT.toFinset, canonicalFactor R (a i) z with hP
  have hPne : P w ≠ 0 := Finset.prod_ne_zero_iff.mpr hcf_ne
  have hPd : DifferentiableAt ℂ P w := DifferentiableAt.fun_finsetProd hcf_diff
  have hfd : DifferentiableAt ℂ f w := hf w
  have hev : g =ᶠ[𝓝 w] fun z => P z * f z := by
    have h1 : ∀ᶠ z in 𝓝 w, z ∈ ball (0 : ℂ) R := isOpen_ball.mem_nhds hwb
    have h2 : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hfw
    filter_upwards [h1, h2] with z hz1 hz2
    exact hgdec z (ball_subset_closedBall hz1) hz2
  have hlg : logDeriv g w = logDeriv P w + logDeriv f w := by
    have : logDeriv g w = logDeriv (fun z => P z * f z) w := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
    rw [this, logDeriv_fun_mul w hPne hfw hPd hfd]
  have hlP : logDeriv P w = ∑ i ∈ hT.toFinset, logDeriv (canonicalFactor R (a i)) w :=
    logDeriv_fun_prod hcf_ne hcf_diff
  have hterm : ∀ i ∈ hT.toFinset, logDeriv (canonicalFactor R (a i)) w =
      -(1 / (w - a i) + conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w)) := by
    intro i hi
    have hnum : (R : ℂ) ^ 2 - conj (a i) * w ≠ 0 := by
      intro h
      apply hcf_ne i hi
      rw [canonicalFactor_apply, h]; simp
    rw [logDeriv_canonicalFactor hR.ne' (hwa i) hnum]
    ring
  rw [hlP, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hlg
  linear_combination -hlg

end logderiv

section bounds

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {R : ℝ} (hR : 0 < R) (hsph : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0)
  (hT : {i | a i ∈ ball (0 : ℂ) R}.Finite)
  {g : ℂ → ℂ} (hgan : AnalyticOnNhd ℂ g (closedBall 0 R))
  (hgne : ∀ w ∈ closedBall (0 : ℂ) R, g w ≠ 0)
  (hgdec : ∀ w ∈ closedBall (0 : ℂ) R, f w ≠ 0 →
    g w = (∏ i ∈ hT.toFinset, canonicalFactor R (a i) w) * f w)
  {M : ℝ} (hM : ∀ w : ℂ, ‖w‖ = R → ‖f w‖ ≤ M)
include hf h0 L hR hsph hgan hgne hgdec hM

omit hf h0 L hgne in
/-- Maximum principle: `‖g‖ ≤ M` on the closed disc. -/
lemma norm_g_le : ∀ w ∈ closedBall (0 : ℂ) R, ‖g w‖ ≤ M := by
  intro w hw
  have hdc : DiffContOnCl ℂ g (ball 0 R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    exact hgan.differentiableOn
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc ?_
    (by rw [closure_ball _ hR.ne']; exact hw)
  intro z hz
  rw [frontier_ball _ hR.ne'] at hz
  have hz' : ‖z‖ = R := by simpa using hz
  rw [hgdec z (sphere_subset_closedBall hz) (hsph z hz'), norm_mul, norm_prod]
  have : ∏ i ∈ hT.toFinset, ‖canonicalFactor R (a i) z‖ = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    exact norm_canonicalFactor_eval_circle_eq_one (by simpa using hT.mem_toFinset.mp hi) hz
  rw [this, one_mul]
  exact hM z hz'

omit hf hsph hgan hgne hM in
/-- `‖f 0‖ ≤ ‖g 0‖` (the Blaschke product has modulus `≤ 1` at the origin). -/
lemma norm_f_zero_le_g : ‖f 0‖ ≤ ‖g 0‖ := by
  rw [hgdec 0 (by simp [hR.le]) h0, norm_mul, norm_prod]
  have : 1 ≤ ∏ i ∈ hT.toFinset, ‖canonicalFactor R (a i) 0‖ := by
    refine one_le_prod₀ fun i hi => ?_
    have hai : ‖a i‖ < R := by simpa using hT.mem_toFinset.mp hi
    have hpos : 0 < ‖a i‖ := norm_pos_iff.mpr (L.ne_zero i)
    rw [canonicalFactor_apply, norm_div]
    simp only [mul_zero, zero_sub, sub_zero, norm_mul, norm_neg]
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ (by positivity)]
    nlinarith
  nlinarith [norm_nonneg (f 0)]

omit hf in
/-- A holomorphic logarithm `H` of `g` on the disc, bounded on `‖z‖ < R/2` by Borel–Carathéodory:
`‖H z‖ ≤ 5 log M + 2 + 3 |log ‖f 0‖|`. -/
lemma exists_log_bound (hM1 : 1 ≤ M) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 R) ∧
      (∀ w ∈ ball (0 : ℂ) R, deriv H w = logDeriv g w) ∧
      ∀ z : ℂ, ‖z‖ < R / 2 → ‖H z‖ ≤ 5 * Real.log M + 2 + 3 * |Real.log ‖f 0‖| := by
  have hgd : DifferentiableOn ℂ g (ball 0 R) := hgan.differentiableOn.mono ball_subset_closedBall
  have hne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0 := fun w hw => hgne w (ball_subset_closedBall hw)
  obtain ⟨H, hHd, hHder, hH0, hHre⟩ := exists_log_ball hR hgd hne
  refine ⟨H, hHd, fun w hw => by rw [hHder w hw, logDeriv_apply], fun z hz => ?_⟩
  have hgle := norm_g_le hR hsph hT hgan hgdec hM
  have hg0le : ‖g 0‖ ≤ M := hgle 0 (by simp [hR.le])
  have hfg0 := norm_f_zero_le_g h0 L hR hT hgdec
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hMpos : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hg0log_le : Real.log ‖g 0‖ ≤ Real.log M := Real.log_le_log (by linarith) hg0le
  have hg0log_ge : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := Real.log_le_log hf0pos hfg0
  have hH0n : ‖H 0‖ ≤ Real.log M + |Real.log ‖f 0‖| := by
    rw [hH0, Complex.norm_real, Real.norm_eq_abs]
    have h1 := neg_abs_le (Real.log ‖f 0‖)
    have h2 := le_abs_self (Real.log ‖f 0‖)
    rw [abs_le]; constructor <;> linarith [abs_nonneg (Real.log ‖f 0‖)]
  have hmaps : Set.MapsTo H (ball 0 R) {w : ℂ | w.re ≤ Real.log M + 1} := by
    intro w hw
    have hw' := hHre w hw
    have : Real.log ‖g w‖ ≤ Real.log M :=
      Real.log_le_log (norm_pos_iff.mpr (hne w hw)) (hgle w (ball_subset_closedBall hw))
    show (H w).re ≤ Real.log M + 1
    linarith
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hBC := Complex.borelCaratheodory (by linarith : 0 < Real.log M + 1) hHd hmaps hR hzR
  have hz0 : ‖z‖ < R / 2 := hz
  have hden : 0 < R - ‖z‖ := by linarith
  have e1 : 2 * (Real.log M + 1) * ‖z‖ / (R - ‖z‖) ≤ 2 * (Real.log M + 1) := by
    rw [div_le_iff₀ hden]; nlinarith
  have e2 : ‖H 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖H 0‖ := by
    rw [div_le_iff₀ hden]; nlinarith [norm_nonneg (H 0)]
  have := hBC.trans (add_le_add e1 e2)
  linarith [abs_nonneg (Real.log ‖f 0‖)]

end bounds

end FormalResearch.Hadamard

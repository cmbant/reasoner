module

public import FormalResearch.ModularBootstrap.Upper.Comb.Factors
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reference Blaschke Comb I: Zero Law and Quantiles (Lemma K0) and $B^{(f)}$ (Lemma K1(a))

Formalizes Lemma K0 (`cmb:K0`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`, together with
the index-$f$ reference Blaschke comb $B^{(f)}$ and the $B^{(f)}$ instantiation of Lemma K1(a)
(`cmb:K1`):

* `arccoshR`: real $\operatorname{arccosh}(x) = \log(x + \sqrt{x^2 - 1})$ for $x \ge 1$.
* `rhoU`: zero-law density $\rho_U(y) = \frac{4}{3\pi}\operatorname{arccosh}(\sinh(\pi y))$ ($y \ge \xi_*$).
* `cumulN`: cumulative count $N(y) = \frac{1}{2}\int_{\xi_*}^y \rho_U(t)\,dt$.
* `chiQuantile`, `chiDeriv`, `chiSecond`, `siteGap` ($\ell_k$), `siteRadius` ($r_a$),
  `lambdaComb` ($\lambda$), `phiQuantile` ($\Phi_a$).
* **K0(a)**: `rhoU_strictMonoOn`, `rhoU_strictConcaveOn`, `rhoUDeriv_ge`, `rhoU_sq_bounds`,
  `rhoU_ge_max`, `logDeriv_rhoU_bounds`.
* **K0(b)**: `hasDerivAt_chiQuantile`, `hasDerivAt_chiDeriv`, `siteGap_strictAnti`,
  `chiDeriv_le_div`, `abs_logDeriv_chiDeriv_le`.
* **K0(c)**: `cumulN_bounds`, `siteRadius_bounds`, `siteRadius_le_one_bounds`,
  `siteGap_eventually_le`.
* `refComb`: the index-$f$ reference comb $B^{(f)}$ and its K1(a) properties
  `refComb_hasProdLocallyUniformlyOn`, `refComb_norm_le_one`, `refComb_norm_eq_one`,
  `refComb_half_I`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Real `arccosh` and the zero-law density `rhoU` -/

/-- Real inverse hyperbolic cosine $\operatorname{arccosh}(x) = \log(x + \sqrt{x^2 - 1})$ for $x \ge 1$. -/
noncomputable def arccoshR (x : ℝ) : ℝ := Real.log (x + √(x ^ 2 - 1))

lemma arccoshR_one : arccoshR 1 = 0 := by simp [arccoshR]

lemma arccoshR_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arccoshR x := by
  unfold arccoshR
  apply Real.log_nonneg
  have : 0 ≤ √(x ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

lemma arccoshR_pos {x : ℝ} (hx : 1 < x) : 0 < arccoshR x := by
  unfold arccoshR
  apply Real.log_pos
  have : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  linarith

lemma cosh_arccoshR {x : ℝ} (hx : 1 ≤ x) : Real.cosh (arccoshR x) = x := by
  unfold arccoshR
  have hpos : 0 < x + √(x ^ 2 - 1) := by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  have hmul : (x + √(x ^ 2 - 1)) * (x - √(x ^ 2 - 1)) = 1 := by
    have hsq : √(x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    nlinarith
  have hinv : x - √(x ^ 2 - 1) = (x + √(x ^ 2 - 1))⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [Real.cosh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos, ← hinv]
  ring

lemma sinh_arccoshR {x : ℝ} (hx : 1 ≤ x) : Real.sinh (arccoshR x) = √(x ^ 2 - 1) := by
  unfold arccoshR
  have hpos : 0 < x + √(x ^ 2 - 1) := by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  have hmul : (x + √(x ^ 2 - 1)) * (x - √(x ^ 2 - 1)) = 1 := by
    have hsq : √(x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    nlinarith
  have hinv : x - √(x ^ 2 - 1) = (x + √(x ^ 2 - 1))⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [Real.sinh_eq, Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos, ← hinv]
  ring

lemma arccoshR_cosh {u : ℝ} (hu : 0 ≤ u) : arccoshR (Real.cosh u) = u := by
  unfold arccoshR
  have hsq : Real.cosh u ^ 2 - 1 = Real.sinh u ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq u]
  rw [hsq, Real.sqrt_sq (Real.sinh_nonneg_iff.mpr hu), Real.cosh_add_sinh, Real.log_exp]

lemma hasDerivAt_arccoshR {x : ℝ} (hx : 1 < x) :
    HasDerivAt arccoshR (1 / √(x ^ 2 - 1)) x := by
  have hx2 : 0 < x ^ 2 - 1 := by nlinarith
  have hsqrt : HasDerivAt (fun t => √(t ^ 2 - 1)) (2 * x / (2 * √(x ^ 2 - 1))) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
      simpa using ((hasDerivAt_id x).pow 2).sub_const 1
    exact h1.sqrt hx2.ne'
  have hsum : HasDerivAt (fun t => t + √(t ^ 2 - 1)) (1 + 2 * x / (2 * √(x ^ 2 - 1))) x :=
    (hasDerivAt_id x).add hsqrt
  have hpos : 0 < x + √(x ^ 2 - 1) := by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  have hs_ne : √(x ^ 2 - 1) ≠ 0 := (Real.sqrt_pos.mpr hx2).ne'
  refine (hsum.log hpos.ne').congr_deriv ?_
  field_simp [hpos.ne', hs_ne]
  ring

lemma continuousOn_arccoshR : ContinuousOn arccoshR (Ici 1) := by
  unfold arccoshR
  refine ContinuousOn.log (continuousOn_id.add ?_) fun x hx => ?_
  · exact (continuous_id.pow 2 |>.sub continuous_const).sqrt.continuousOn
  · have : 1 ≤ x := hx
    have : 0 ≤ √(x ^ 2 - 1) := Real.sqrt_nonneg _
    linarith

lemma strictMonoOn_arccoshR : StrictMonoOn arccoshR (Ici 1) := by
  intro x hx y hy hxy
  unfold arccoshR
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hpos_x : 0 < x + √(x ^ 2 - 1) := by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith
  apply Real.log_lt_log hpos_x
  have hsq : x ^ 2 - 1 < y ^ 2 - 1 := by nlinarith
  have hsqrt : √(x ^ 2 - 1) < √(y ^ 2 - 1) := Real.sqrt_lt_sqrt (by nlinarith) hsq
  linarith

/-- The zero-law density $\rho_U(y) = \frac{4}{3\pi}\operatorname{arccosh}(\sinh(\pi y))$ for $y \ge \xi_*$
(and $0$ for $y \le \xi_*$). -/
noncomputable def rhoU (y : ℝ) : ℝ :=
  if y ≤ xiStar then 0 else (4 / (3 * π)) * arccoshR (Real.sinh (π * y))

/-- Derivative $\rho_U'(y) = \frac{4}{3}\frac{\cosh(\pi y)}{\sqrt{\sinh^2(\pi y) - 1}}$ for $y > \xi_*$. -/
noncomputable def rhoUDeriv (y : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1))

lemma rhoU_eq_of_ge {y : ℝ} (hy : xiStar ≤ y) :
    rhoU y = (4 / (3 * π)) * arccoshR (Real.sinh (π * y)) := by
  unfold rhoU
  split_ifs with h
  · have heq : y = xiStar := le_antisymm h hy
    subst heq; rw [sinh_pi_mul_xiStar, arccoshR_one, mul_zero]
  · rfl

lemma rhoU_xiStar : rhoU xiStar = 0 := by simp [rhoU]

lemma rhoU_nonneg (y : ℝ) : 0 ≤ rhoU y := by
  unfold rhoU
  split_ifs with h
  · exact le_rfl
  · have hpi := Real.pi_pos
    have hgt : xiStar < y := lt_of_not_ge h
    have hs : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
    exact mul_nonneg (by positivity) (arccoshR_nonneg hs.le)

lemma rhoU_pos {y : ℝ} (hy : xiStar < y) : 0 < rhoU y := by
  rw [rhoU_eq_of_ge hy.le]
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  exact mul_pos (by positivity) (arccoshR_pos hs)

lemma continuousOn_rhoU : ContinuousOn rhoU (Ici xiStar) := by
  have hpi := Real.pi_pos
  have heq : EqOn rhoU (fun y => (4 / (3 * π)) * arccoshR (Real.sinh (π * y))) (Ici xiStar) :=
    fun _ hy => rhoU_eq_of_ge hy
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_const.mul (continuousOn_arccoshR.comp
    ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn) ?_)
  intro y hy
  change 1 ≤ Real.sinh (π * y)
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hy hpi.le)

lemma hasDerivAt_rhoU {y : ℝ} (hy : xiStar < y) :
    HasDerivAt rhoU (rhoUDeriv y) y := by
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have h_in : HasDerivAt (fun t => Real.sinh (π * t)) (Real.cosh (π * y) * π) y :=
    (Real.hasDerivAt_sinh (π * y)).comp y (by simpa using (hasDerivAt_id y).const_mul π)
  have h_ar := (hasDerivAt_arccoshR hs).comp y h_in
  have h_mul := h_ar.const_mul (4 / (3 * π))
  have h_ev : rhoU =ᶠ[𝓝 y] fun t => (4 / (3 * π)) * arccoshR (Real.sinh (π * t)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact rhoU_eq_of_ge ht.le
  refine (h_mul.congr_of_eventuallyEq h_ev).congr_deriv ?_
  unfold rhoUDeriv
  field_simp [hpi.ne']

lemma rhoUDeriv_ge {y : ℝ} (hy : xiStar < y) : 4 / 3 < rhoUDeriv y := by
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have hden : 0 < √(Real.sinh (π * y) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hlt : √(Real.sinh (π * y) ^ 2 - 1) < Real.cosh (π * y) := by
    have hch : Real.cosh (π * y) ^ 2 = Real.sinh (π * y) ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * y)]
    rw [← Real.sqrt_sq (Real.cosh_pos _).le]
    exact Real.sqrt_lt_sqrt (by nlinarith) (by linarith)
  have hquot : 1 < Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1) := (one_lt_div hden).mpr hlt
  unfold rhoUDeriv; linarith

lemma rhoUDeriv_strictAntiOn : StrictAntiOn rhoUDeriv (Ioi xiStar) := by
  intro y₁ hy₁ y₂ hy₂ hy
  have hpi := Real.pi_pos
  have hsq : ∀ y : ℝ, xiStar < y →
      (Real.cosh (π * y) / √(Real.sinh (π * y) ^ 2 - 1)) ^ 2 =
        1 + 2 / (Real.sinh (π * y) ^ 2 - 1) := by
    intro y hy'
    have hs : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
    have hpos : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
    rw [div_pow, Real.sq_sqrt hpos.le]
    have hch : Real.cosh (π * y) ^ 2 = Real.sinh (π * y) ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq (π * y)]
    rw [hch]; field_simp [hpos.ne']; ring
  have hs1 : 1 < Real.sinh (π * y₁) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith [hy₁.out])
  have hs2 : Real.sinh (π * y₁) < Real.sinh (π * y₂) :=
    Real.sinh_lt_sinh.mpr (by nlinarith)
  have hlt_sq : (Real.cosh (π * y₂) / √(Real.sinh (π * y₂) ^ 2 - 1)) ^ 2 <
      (Real.cosh (π * y₁) / √(Real.sinh (π * y₁) ^ 2 - 1)) ^ 2 := by
    rw [hsq y₁ hy₁, hsq y₂ hy₂]
    have h1 : 0 < Real.sinh (π * y₁) ^ 2 - 1 := by nlinarith
    have h2 : Real.sinh (π * y₁) ^ 2 - 1 < Real.sinh (π * y₂) ^ 2 - 1 := by nlinarith
    gcongr
  have hpos1 : 0 < Real.cosh (π * y₁) / √(Real.sinh (π * y₁) ^ 2 - 1) := by
    have : 0 < √(Real.sinh (π * y₁) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
    exact div_pos (Real.cosh_pos _) this
  have hpos2 : 0 < Real.cosh (π * y₂) / √(Real.sinh (π * y₂) ^ 2 - 1) := by
    have : 0 < √(Real.sinh (π * y₂) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
    exact div_pos (Real.cosh_pos _) this
  have hlt : Real.cosh (π * y₂) / √(Real.sinh (π * y₂) ^ 2 - 1) <
      Real.cosh (π * y₁) / √(Real.sinh (π * y₁) ^ 2 - 1) := by
    nlinarith
  unfold rhoUDeriv; linarith

/-- **K0(a), monotonicity**: $\rho_U$ is strictly increasing on $[\xi_*, \infty)$. -/
theorem rhoU_strictMonoOn : StrictMonoOn rhoU (Ici xiStar) := by
  intro y₁ hy₁ y₂ hy₂ hy
  have hpi := Real.pi_pos
  rw [rhoU_eq_of_ge hy₁, rhoU_eq_of_ge hy₂]
  have hs1 : 1 ≤ Real.sinh (π * y₁) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hy₁ hpi.le)
  have hs2 : 1 ≤ Real.sinh (π * y₂) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hy₂ hpi.le)
  have hs_lt : Real.sinh (π * y₁) < Real.sinh (π * y₂) := Real.sinh_lt_sinh.mpr (by nlinarith)
  exact mul_lt_mul_of_pos_left (strictMonoOn_arccoshR hs1 hs2 hs_lt) (by positivity)

/-- **K0(a), concavity**: $\rho_U$ is strictly concave on $[\xi_*, \infty)$. -/
theorem rhoU_strictConcaveOn : StrictConcaveOn ℝ (Ici xiStar) rhoU := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici xiStar) continuousOn_rhoU ?_
  intro y₁ hy₁ y₂ hy₂ hy
  rw [interior_Ici] at hy₁ hy₂
  rw [(hasDerivAt_rhoU hy₁).deriv, (hasDerivAt_rhoU hy₂).deriv]
  exact rhoUDeriv_strictAntiOn hy₁ hy₂ hy

/-! ### Section 2: Second derivative of `Φ(r) = ρ_U(ξ_* + r)^2` and tip bounds -/

/-- $\Phi(r) := \rho_U(\xi_* + r)^2$ for $r \ge 0$. -/
noncomputable def rhoUSq (r : ℝ) : ℝ := rhoU (xiStar + r) ^ 2

/-- $A(r) := \operatorname{arccosh}(\sinh(\pi(\xi_* + r)))$ for $r \ge 0$. -/
noncomputable def tipArgA (r : ℝ) : ℝ := arccoshR (Real.sinh (π * (xiStar + r)))

/-- $\Phi'(r) = 2 \rho_U(\xi_* + r) \rho_U'(\xi_* + r)$ for $r > 0$. -/
noncomputable def rhoUSqDeriv (r : ℝ) : ℝ :=
  (32 / (9 * π)) * (tipArgA r * Real.cosh (π * (xiStar + r)) / Real.sinh (tipArgA r))

/-- $\Phi''(r) = \frac{32}{9}\frac{(1 + \cosh^2 A)\sinh A - 2 A\cosh A}{\sinh^3 A}$ for $r > 0$. -/
noncomputable def rhoUSqSecond (r : ℝ) : ℝ :=
  (32 / 9 : ℝ) *
    (((1 + Real.cosh (tipArgA r) ^ 2) * Real.sinh (tipArgA r) -
        2 * tipArgA r * Real.cosh (tipArgA r)) /
      Real.sinh (tipArgA r) ^ 3)

lemma nine_mul_kTip_sq : 9 * kTip ^ 2 = 32 * √2 / (9 * π) := by
  unfold kTip
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hsqp : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have h2 : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = 2 * √2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul (by norm_num),
      show (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 by push_cast; norm_num, Real.rpow_add two_pos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  calc 9 * (4 * (2 : ℝ) ^ (3 / 4 : ℝ) / (9 * √π)) ^ 2
      = 9 * (16 * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (81 * √π ^ 2)) := by ring
    _ = 9 * (16 * (2 * √2) / (81 * π)) := by rw [h2, hsqp]
    _ = 32 * √2 / (9 * π) := by ring

lemma tipArgA_pos {r : ℝ} (hr : 0 < r) : 0 < tipArgA r := by
  unfold tipArgA
  apply arccoshR_pos
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_lt_sinh.mpr (by nlinarith [Real.pi_pos])

lemma cosh_tipArgA {r : ℝ} (hr : 0 ≤ r) :
    Real.cosh (tipArgA r) = Real.sinh (π * (xiStar + r)) := by
  unfold tipArgA
  apply cosh_arccoshR
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])

lemma sinh_tipArgA {r : ℝ} (hr : 0 ≤ r) :
    Real.sinh (tipArgA r) = √(Real.sinh (π * (xiStar + r)) ^ 2 - 1) := by
  unfold tipArgA
  apply sinh_arccoshR
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])

lemma hasDerivAt_tipArgA {r : ℝ} (hr : 0 < r) :
    HasDerivAt tipArgA (π * Real.cosh (π * (xiStar + r)) / Real.sinh (tipArgA r)) r := by
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * (xiStar + r)) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have h_in : HasDerivAt (fun t => Real.sinh (π * (xiStar + t)))
      (Real.cosh (π * (xiStar + r)) * π) r := by
    have hl : HasDerivAt (fun t => π * (xiStar + t)) π r := by
      simpa using ((hasDerivAt_id r).const_add xiStar).const_mul π
    exact (Real.hasDerivAt_sinh _).comp r hl
  have h_ar := (hasDerivAt_arccoshR hs).comp r h_in
  refine h_ar.congr_deriv ?_
  rw [sinh_tipArgA hr.le]; ring

lemma hasDerivAt_rhoUSq {r : ℝ} (hr : 0 < r) :
    HasDerivAt rhoUSq (rhoUSqDeriv r) r := by
  have hpi := Real.pi_pos
  have hr_xi : xiStar < xiStar + r := by linarith
  have h_rho : HasDerivAt (fun t => rhoU (xiStar + t)) (rhoUDeriv (xiStar + r)) r := by
    have h1 := hasDerivAt_rhoU hr_xi
    have hl : HasDerivAt (fun t => xiStar + t) 1 r := (hasDerivAt_id r).const_add xiStar
    have hc := h1.comp r hl
    simp only [Function.comp_def, mul_one] at hc
    exact hc
  have h_sq := h_rho.pow 2
  refine h_sq.congr_deriv ?_
  unfold rhoUSqDeriv rhoUDeriv tipArgA
  rw [rhoU_eq_of_ge hr_xi.le, ← sinh_arccoshR (by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos, hr.le]))]
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]; ring

lemma hasDerivAt_rhoUSqDeriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt rhoUSqDeriv (rhoUSqSecond r) r := by
  have hpi := Real.pi_pos
  have hA_pos : 0 < tipArgA r := tipArgA_pos hr
  have hsh_pos : 0 < Real.sinh (tipArgA r) := Real.sinh_pos_iff.mpr hA_pos
  have hA_deriv := hasDerivAt_tipArgA hr
  have hch_deriv : HasDerivAt (fun t => Real.cosh (π * (xiStar + t)))
      (Real.sinh (π * (xiStar + r)) * π) r := by
    have hl : HasDerivAt (fun t => π * (xiStar + t)) π r := by
      simpa using ((hasDerivAt_id r).const_add xiStar).const_mul π
    exact (Real.hasDerivAt_cosh _).comp r hl
  have hshA_deriv : HasDerivAt (fun t => Real.sinh (tipArgA t))
      (Real.cosh (tipArgA r) * (π * Real.cosh (π * (xiStar + r)) / Real.sinh (tipArgA r))) r :=
    (Real.hasDerivAt_sinh _).comp r hA_deriv
  have hquot_deriv := (hA_deriv.mul hch_deriv).div hshA_deriv hsh_pos.ne'
  have htot := hquot_deriv.const_mul (32 / (9 * π))
  refine htot.congr_deriv ?_
  unfold rhoUSqSecond
  dsimp only [Pi.mul_apply]
  set A := tipArgA r
  set shA := Real.sinh A
  set chA := Real.cosh A
  set c := Real.cosh (π * (xiStar + r))
  have hch_eq : chA = Real.sinh (π * (xiStar + r)) := cosh_tipArgA hr.le
  have hc2 : c ^ 2 = 1 + chA ^ 2 := by
    dsimp [c]; rw [hch_eq]; linarith [Real.cosh_sq_sub_sinh_sq (π * (xiStar + r))]
  have hch2 : chA ^ 2 = shA ^ 2 + 1 := by
    dsimp [chA, shA]; linarith [Real.cosh_sq_sub_sinh_sq A]
  have hsh_ne : shA ≠ 0 := hsh_pos.ne'
  have h1 : (π * c / shA * c + A * (Real.sinh (π * (xiStar + r)) * π)) * shA -
      A * c * (chA * (π * c / shA)) =
      π * ((1 + chA ^ 2) * shA - 2 * A * chA) / shA := by
    rw [← hch_eq, eq_div_iff hsh_ne]
    calc ((π * c / shA * c + A * (chA * π)) * shA - A * c * (chA * (π * c / shA))) * shA
        = π * (c / shA * shA) * c * shA + π * A * chA * shA ^ 2 -
            π * A * chA * c * (c / shA * shA) := by ring
      _ = π * c ^ 2 * shA + π * A * chA * shA ^ 2 - π * A * chA * c ^ 2 := by
          rw [div_mul_cancel₀ c hsh_ne]; ring
      _ = π * (1 + chA ^ 2) * shA + π * A * chA * (shA ^ 2 - (1 + chA ^ 2)) := by
          rw [hc2]; ring
      _ = π * ((1 + chA ^ 2) * shA - 2 * A * chA) := by
          rw [hch2]; ring
  rw [h1]
  field_simp [hpi.ne', hsh_ne]

private lemma real_continuous_tanh : Continuous Real.tanh :=
  (Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne').congr
    fun x => by simp [Real.tanh_eq_sinh_div_cosh]

private lemma real_differentiable_tanh : Differentiable ℝ Real.tanh :=
  fun x => (Real.differentiableAt_sinh.div Real.differentiableAt_cosh (Real.cosh_pos x).ne').congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simp [Real.tanh_eq_sinh_div_cosh])

private lemma real_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hne
  have hd' : HasDerivAt (fun t => Real.sinh t / Real.cosh t) (1 / Real.cosh x ^ 2) x := by
    refine hd.congr_deriv ?_
    have hcs := Real.cosh_sq_sub_sinh_sq x
    field_simp [hne]
    linarith
  exact hd'.congr_of_eventuallyEq (Eventually.of_forall fun t => Real.tanh_eq_sinh_div_cosh t)

/-- Positivity and upper bound `0 ≤ Φ''(r) ≤ 32/9` for all `r > 0` (`A_tip`, `K0`). -/
theorem rhoUSqSecond_bounds {r : ℝ} (hr : 0 < r) :
    0 ≤ rhoUSqSecond r ∧ rhoUSqSecond r ≤ 32 / 9 := by
  have hA_pos : 0 < tipArgA r := tipArgA_pos hr
  have hsh_pos : 0 < Real.sinh (tipArgA r) := Real.sinh_pos_iff.mpr hA_pos
  have h_le : ∀ A : ℝ, 0 ≤ A → Real.tanh A ≤ A := by
    intro A hA
    let g : ℝ → ℝ := fun x => x - Real.tanh x
    have hc : ContinuousOn g (Icc 0 A) := (continuous_id.sub real_continuous_tanh).continuousOn
    have hdiff : DifferentiableOn ℝ g (interior (Icc 0 A)) :=
      (differentiable_id.sub real_differentiable_tanh).differentiableOn.mono interior_subset
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 A) hc hdiff
      (fun t _ => by
        have ht : HasDerivAt g (1 - 1 / Real.cosh t ^ 2) t :=
          (hasDerivAt_id t).sub (real_hasDerivAt_tanh t)
        rw [ht.deriv]
        have hch : 1 ≤ Real.cosh t := Real.one_le_cosh t
        have hinv : 1 / Real.cosh t ^ 2 ≤ 1 := div_le_one_of_le₀ (by nlinarith) (sq_nonneg _)
        linarith)
    have h0 := hm (left_mem_Icc.mpr hA) (right_mem_Icc.mpr hA) hA
    dsimp [g] at h0
    simp only [Real.tanh_zero, sub_self] at h0
    linarith
  have h_nonneg : ∀ A : ℝ, 0 ≤ A →
      0 ≤ (1 + Real.cosh A ^ 2) * Real.sinh A - 2 * A * Real.cosh A := by
    intro A hA
    have hg : 0 ≤ (1 + Real.cosh A ^ 2) * Real.tanh A - 2 * A := by
      let g : ℝ → ℝ := fun x => (1 + Real.cosh x ^ 2) * Real.tanh x - 2 * x
      have hc : ContinuousOn g (Icc 0 A) :=
        (((continuous_const.add (Real.continuous_cosh.pow 2)).mul real_continuous_tanh).sub
          (continuous_const.mul continuous_id)).continuousOn
      have hdiff : DifferentiableOn ℝ g (interior (Icc 0 A)) :=
        ((((differentiable_const _).add (Real.differentiable_cosh.pow 2)).mul
          real_differentiable_tanh).sub ((differentiable_const _).mul differentiable_id)).differentiableOn.mono
          interior_subset
      have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 A) hc hdiff
        (fun t _ => by
          have hd : HasDerivAt g
              ((2 * Real.cosh t * Real.sinh t) * Real.tanh t +
                (1 + Real.cosh t ^ 2) * (1 / Real.cosh t ^ 2) - 2) t := by
            have h1 := (hasDerivAt_const t (1 : ℝ)).add ((Real.hasDerivAt_cosh t).pow 2)
            have h2 := real_hasDerivAt_tanh t
            have h3 := (hasDerivAt_id t).const_mul 2
            exact ((h1.mul h2).sub h3).congr_deriv
              (by simp only [Nat.reduceSub, pow_one, zero_add, Nat.cast_ofNat,
                Pi.add_apply, Pi.pow_apply]; ring)
          rw [hd.deriv]
          have hch_ne : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
          have hcs : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
          have h_eq : (2 * Real.cosh t * Real.sinh t) * Real.tanh t +
              (1 + Real.cosh t ^ 2) * (1 / Real.cosh t ^ 2) - 2 =
              Real.sinh t ^ 2 * (2 - 1 / Real.cosh t ^ 2) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            field_simp [hch_ne]
            linear_combination -hcs
          rw [h_eq]
          have hch1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
          have hsech : 1 / Real.cosh t ^ 2 ≤ 1 := div_le_one_of_le₀ (by nlinarith) (sq_nonneg _)
          exact mul_nonneg (sq_nonneg _) (by linarith))
      have h0 := hm (left_mem_Icc.mpr hA) (right_mem_Icc.mpr hA) hA
      dsimp [g] at h0
      simp only [Real.cosh_zero, one_pow, Real.tanh_zero, mul_zero, sub_self] at h0
      exact h0
    have hch : 0 < Real.cosh A := Real.cosh_pos A
    have hmul := mul_nonneg hg hch.le
    have hid : ((1 + Real.cosh A ^ 2) * Real.tanh A - 2 * A) * Real.cosh A =
        (1 + Real.cosh A ^ 2) * Real.sinh A - 2 * A * Real.cosh A := by
      rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hch.ne']
    linarith
  set A := tipArgA r
  have hnum0 := h_nonneg A hA_pos.le
  have hnum1 : (1 + Real.cosh A ^ 2) * Real.sinh A - 2 * A * Real.cosh A ≤ Real.sinh A ^ 3 := by
    have h1 := h_le A hA_pos.le
    have hch : 0 < Real.cosh A := Real.cosh_pos A
    have h2 : Real.sinh A ≤ A * Real.cosh A := by
      have := mul_le_mul_of_nonneg_right h1 hch.le
      rwa [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ hch.ne'] at this
    have hcs : Real.cosh A ^ 2 - Real.sinh A ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq A
    nlinarith
  unfold rhoUSqSecond
  constructor
  · exact mul_nonneg (by norm_num) (div_nonneg hnum0 (pow_nonneg hsh_pos.le 3))
  · calc (32 / 9 : ℝ) * (((1 + Real.cosh A ^ 2) * Real.sinh A - 2 * A * Real.cosh A) / Real.sinh A ^ 3)
        ≤ (32 / 9 : ℝ) * (Real.sinh A ^ 3 / Real.sinh A ^ 3) := by gcongr
      _ = 32 / 9 := by rw [div_self (pow_ne_zero 3 hsh_pos.ne'), mul_one]

lemma tendsto_rhoUSqDeriv_zero :
    Tendsto rhoUSqDeriv (𝓝[>] 0) (𝓝 (9 * kTip ^ 2)) := by
  have hlim_eq : (32 / (9 * π)) * (1 * √2) = 9 * kTip ^ 2 := by
    rw [nine_mul_kTip_sq]; ring
  rw [← hlim_eq]
  have hA_cont : ContinuousWithinAt tipArgA (Ici 0) 0 := by
    unfold tipArgA
    have hc1 : ContinuousWithinAt (fun r => Real.sinh (π * (xiStar + r))) (Ici 0) 0 :=
      (Real.continuous_sinh.comp (continuous_const.mul
        (continuous_const.add continuous_id))).continuousWithinAt
    have hc2 : ContinuousWithinAt arccoshR (Ici 1) (Real.sinh (π * (xiStar + 0))) :=
      continuousOn_arccoshR.continuousWithinAt (by
        rw [add_zero, sinh_pi_mul_xiStar]; exact le_rfl)
    exact ContinuousWithinAt.comp (g := arccoshR) (f := fun r => Real.sinh (π * (xiStar + r)))
      hc2 hc1 fun r hr => by
      change 1 ≤ Real.sinh (π * (xiStar + r))
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos, show (0 : ℝ) ≤ r from hr])
  have hA0 : tipArgA 0 = 0 := by unfold tipArgA; rw [add_zero, sinh_pi_mul_xiStar, arccoshR_one]
  have hA_tend : Tendsto tipArgA (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [hA0] using hA_cont.tendsto.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact tipArgA_pos hr
  have h_u_sinh : Tendsto (fun u : ℝ => u / Real.sinh u) (𝓝[>] 0) (𝓝 1) := by
    have hd : Tendsto (fun t : ℝ => t⁻¹ * (Real.sinh (0 + t) - Real.sinh 0)) (𝓝[≠] 0) (𝓝 (Real.cosh 0)) :=
      (Real.hasDerivAt_sinh 0).tendsto_slope_zero
    simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero] at hd
    have hd' : Tendsto (fun u : ℝ => Real.sinh u / u) (𝓝[>] 0) (𝓝 1) :=
      (hd.mono_left (nhdsWithin_mono 0 fun _ hx => ne_of_gt hx)).congr'
        (Eventually.of_forall fun u => by dsimp only; rw [div_eq_mul_inv, mul_comm])
    have hinv := hd'.inv₀ one_ne_zero
    rw [inv_one] at hinv
    exact hinv.congr' (Eventually.of_forall fun u => by rw [inv_div])
  have h_ratio : Tendsto (fun r : ℝ => tipArgA r / Real.sinh (tipArgA r)) (𝓝[>] 0) (𝓝 1) :=
    h_u_sinh.comp hA_tend
  have h_cosh : Tendsto (fun r : ℝ => Real.cosh (π * (xiStar + r))) (𝓝[>] 0) (𝓝 √2) := by
    have hc : Continuous (fun r : ℝ => Real.cosh (π * (xiStar + r))) := by fun_prop
    have hlim : Real.cosh (π * (xiStar + 0)) = √2 := by
      rw [add_zero]
      have hsq : Real.cosh (π * xiStar) ^ 2 = 2 := by
        have h1 := Real.cosh_sq_sub_sinh_sq (π * xiStar)
        rw [sinh_pi_mul_xiStar, one_pow] at h1
        linarith
      rw [← hsq, Real.sqrt_sq (Real.cosh_pos _).le]
    rw [← hlim]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htot := ((h_ratio.mul h_cosh).const_mul (32 / (9 * π)))
  exact htot.congr' (Eventually.of_forall fun r => by unfold rhoUSqDeriv; ring)

lemma rhoUSqDeriv_bounds {r : ℝ} (hr : 0 < r) :
    9 * kTip ^ 2 ≤ rhoUSqDeriv r ∧ rhoUSqDeriv r ≤ 9 * kTip ^ 2 + (32 / 9) * r := by
  have h_lb : Tendsto (fun δ : ℝ => rhoUSqDeriv r - rhoUSqDeriv δ) (𝓝[>] 0)
      (𝓝 (rhoUSqDeriv r - 9 * kTip ^ 2)) :=
    tendsto_const_nhds.sub tendsto_rhoUSqDeriv_zero
  have h_mono : ∀ δ : ℝ, 0 < δ → δ ≤ r →
      0 ≤ rhoUSqDeriv r - rhoUSqDeriv δ ∧ rhoUSqDeriv r - rhoUSqDeriv δ ≤ (32 / 9) * (r - δ) := by
    intro δ hδ hδr
    let g2 : ℝ → ℝ := fun t => (32 / 9 : ℝ) * t - rhoUSqDeriv t
    have hd1 : ContinuousOn rhoUSqDeriv (Icc δ r) := fun t ht =>
      (hasDerivAt_rhoUSqDeriv (lt_of_lt_of_le hδ ht.1)).continuousAt.continuousWithinAt
    have hd2 : ContinuousOn g2 (Icc δ r) :=
      (continuousOn_const.mul continuousOn_id).sub hd1
    have hm1 := monotoneOn_of_deriv_nonneg (convex_Icc δ r) hd1
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (hasDerivAt_rhoUSqDeriv (lt_of_lt_of_le hδ ht.1.le)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hasDerivAt_rhoUSqDeriv (lt_of_lt_of_le hδ ht.1.le)).deriv]
        exact (rhoUSqSecond_bounds (lt_of_lt_of_le hδ ht.1.le)).1)
    have hm2 := monotoneOn_of_deriv_nonneg (convex_Icc δ r) hd2
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (((hasDerivAt_id t).const_mul (32 / 9)).sub
          (hasDerivAt_rhoUSqDeriv (lt_of_lt_of_le hδ ht.1.le))).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        have hpt := lt_of_lt_of_le hδ ht.1.le
        have hderiv : HasDerivAt g2 (32 / 9 - rhoUSqSecond t) t :=
          (((hasDerivAt_id t).const_mul (32 / 9)).sub (hasDerivAt_rhoUSqDeriv hpt)).congr_of_eventuallyEq
            (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by ring)
        rw [hderiv.deriv]
        linarith [(rhoUSqSecond_bounds hpt).2])
    have h1 := hm1 (left_mem_Icc.mpr hδr) (right_mem_Icc.mpr hδr) hδr
    have h2 := hm2 (left_mem_Icc.mpr hδr) (right_mem_Icc.mpr hδr) hδr
    dsimp [g2] at h2
    exact ⟨by linarith, by linarith⟩
  have h1 : 0 ≤ rhoUSqDeriv r - 9 * kTip ^ 2 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h_lb ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    exact (h_mono δ hδ.1 hδ.2.le).1
  have h2 : rhoUSqDeriv r - 9 * kTip ^ 2 ≤ (32 / 9) * r := by
    have h_rhs : Tendsto (fun δ : ℝ => (32 / 9 : ℝ) * (r - δ)) (𝓝[>] 0) (𝓝 ((32 / 9) * r)) := by
      have hc : Continuous (fun δ : ℝ => (32 / 9 : ℝ) * (r - δ)) := by fun_prop
      simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    refine le_of_tendsto_of_tendsto h_lb h_rhs ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with δ hδ
    exact (h_mono δ hδ.1 hδ.2.le).2
  exact ⟨by linarith, by linarith⟩

/-- **K0(a), tip density square bounds**:
$9 k_{\mathrm{tip}}^2 r \le \rho_U(\xi_* + r)^2 \le 9 k_{\mathrm{tip}}^2 r + \frac{16}{9} r^2$ for all $r \ge 0$. -/
theorem rhoU_sq_bounds {r : ℝ} (hr : 0 ≤ r) :
    9 * kTip ^ 2 * r ≤ rhoU (xiStar + r) ^ 2 ∧
      rhoU (xiStar + r) ^ 2 ≤ 9 * kTip ^ 2 * r + (16 / 9) * r ^ 2 := by
  change 9 * kTip ^ 2 * r ≤ rhoUSq r ∧ rhoUSq r ≤ 9 * kTip ^ 2 * r + (16 / 9) * r ^ 2
  have h0 : rhoUSq 0 = 0 := by unfold rhoUSq; rw [add_zero, rhoU_xiStar]; norm_num
  have hcont : ContinuousOn rhoUSq (Icc 0 r) := by
    unfold rhoUSq
    have hc : ContinuousOn (fun t => rhoU (xiStar + t)) (Icc 0 r) :=
      continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn fun t ht => by
        change xiStar ≤ xiStar + t; linarith [ht.1]
    exact hc.pow 2
  let g1 : ℝ → ℝ := fun t => rhoUSq t - 9 * kTip ^ 2 * t
  let g2 : ℝ → ℝ := fun t => 9 * kTip ^ 2 * t + (16 / 9) * t ^ 2 - rhoUSq t
  have hc1 : ContinuousOn g1 (Icc 0 r) := hcont.sub (continuousOn_const.mul continuousOn_id)
  have hc2 : ContinuousOn g2 (Icc 0 r) :=
    ((continuousOn_const.mul continuousOn_id).add
      (continuousOn_const.mul (continuousOn_id.pow 2))).sub hcont
  have hm1 := monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hc1
    (fun t ht => by
      rw [interior_Icc] at ht
      exact ((hasDerivAt_rhoUSq ht.1).sub ((hasDerivAt_id t).const_mul (9 * kTip ^ 2))).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      have hd : HasDerivAt g1 (rhoUSqDeriv t - 9 * kTip ^ 2) t :=
        ((hasDerivAt_rhoUSq ht.1).sub ((hasDerivAt_id t).const_mul (9 * kTip ^ 2))).congr_of_eventuallyEq
          (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by ring)
      rw [hd.deriv]
      linarith [(rhoUSqDeriv_bounds ht.1).1])
  have hm2 := monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hc2
    (fun t ht => by
      rw [interior_Icc] at ht
      have hd1 : HasDerivAt (fun x => 9 * kTip ^ 2 * x + (16 / 9) * x ^ 2)
          (9 * kTip ^ 2 + (32 / 9) * t) t := by
        have h := ((hasDerivAt_id t).const_mul (9 * kTip ^ 2)).add
          (((hasDerivAt_pow 2 t)).const_mul (16 / 9))
        refine h.congr_deriv ?_; simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
      exact (hd1.sub (hasDerivAt_rhoUSq ht.1)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      have hd1 : HasDerivAt (fun x => 9 * kTip ^ 2 * x + (16 / 9) * x ^ 2)
          (9 * kTip ^ 2 + (32 / 9) * t) t := by
        have h := ((hasDerivAt_id t).const_mul (9 * kTip ^ 2)).add
          (((hasDerivAt_pow 2 t)).const_mul (16 / 9))
        refine h.congr_deriv ?_; simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
      have hd : HasDerivAt g2 (9 * kTip ^ 2 + (32 / 9) * t - rhoUSqDeriv t) t :=
        hd1.sub (hasDerivAt_rhoUSq ht.1)
      rw [hd.deriv]
      have h2 := (rhoUSqDeriv_bounds ht.1).2
      linarith)
  have h1 := hm1 (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have h2 := hm2 (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  dsimp [g1, g2] at h1 h2
  simp only [h0, mul_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **K0(a), linear and square-root lower bounds**:
$\rho_U(\xi_* + r) \ge \max(3 k_{\mathrm{tip}} r^{1/2}, \frac{4}{3} r)$ for $r \ge 0$. -/
theorem rhoU_ge_max {r : ℝ} (hr : 0 ≤ r) :
    max (3 * kTip * √r) ((4 / 3) * r) ≤ rhoU (xiStar + r) := by
  have hnn : 0 ≤ rhoU (xiStar + r) := rhoU_nonneg _
  refine max_le ?_ ?_
  · have h1 := (rhoU_sq_bounds hr).1
    have hsq : (3 * kTip * √r) ^ 2 = 9 * kTip ^ 2 * r := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hr]; ring
    have hk : 0 ≤ 3 * kTip * √r := by have := kTip_pos; positivity
    nlinarith [sq_nonneg (rhoU (xiStar + r) - 3 * kTip * √r)]
  · let g : ℝ → ℝ := fun t => rhoU (xiStar + t) - (4 / 3) * t
    have hcont : ContinuousOn g (Icc 0 r) :=
      (continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn
        fun t ht => by change xiStar ≤ xiStar + t; linarith [ht.1]).sub
        (continuousOn_const.mul continuousOn_id)
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont
      (fun t ht => by
        rw [interior_Icc] at ht
        have h1 := (hasDerivAt_rhoU (by linarith [ht.1] : xiStar < xiStar + t)).comp t
          ((hasDerivAt_id t).const_add xiStar)
        exact (h1.sub ((hasDerivAt_id t).const_mul (4 / 3))).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        have h1 : HasDerivAt (fun x => rhoU (xiStar + x)) (rhoUDeriv (xiStar + t)) t := by
          have h := (hasDerivAt_rhoU (by linarith [ht.1] : xiStar < xiStar + t)).comp t
            ((hasDerivAt_id t).const_add xiStar)
          simpa only [Function.comp_def, mul_one] using h
        have h2 : HasDerivAt g (rhoUDeriv (xiStar + t) - 4 / 3) t :=
          (h1.sub ((hasDerivAt_id t).const_mul (4 / 3))).congr_of_eventuallyEq
            (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by ring)
        rw [h2.deriv]
        have hge := rhoUDeriv_ge (by linarith [ht.1] : xiStar < xiStar + t)
        linarith)
    have h0 := hm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
    dsimp [g] at h0
    simp only [add_zero, rhoU_xiStar, mul_zero, sub_self] at h0
    linarith

/-- **K0(a), log-derivative bound**: $0 < (\log \rho_U)'(\xi_* + r) \le 1/r$ for $r > 0$. -/
theorem logDeriv_rhoU_bounds {r : ℝ} (hr : 0 < r) :
    0 < rhoUDeriv (xiStar + r) / rhoU (xiStar + r) ∧
      rhoUDeriv (xiStar + r) / rhoU (xiStar + r) ≤ 1 / r := by
  have hrho_pos : 0 < rhoU (xiStar + r) := rhoU_pos (by linarith)
  have hderiv_pos : 0 < rhoUDeriv (xiStar + r) := by
    linarith [rhoUDeriv_ge (by linarith : xiStar < xiStar + r)]
  refine ⟨div_pos hderiv_pos hrho_pos, ?_⟩
  rw [div_le_div_iff₀ hrho_pos hr, one_mul]
  let g : ℝ → ℝ := fun t => rhoU (xiStar + t) - t * rhoUDeriv (xiStar + r)
  have hcont : ContinuousOn g (Icc 0 r) :=
    (continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn
      fun t ht => by change xiStar ≤ xiStar + t; linarith [ht.1]).sub
      (continuousOn_id.mul continuousOn_const)
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont
    (fun t ht => by
      rw [interior_Icc] at ht
      have h1 := (hasDerivAt_rhoU (by linarith [ht.1] : xiStar < xiStar + t)).comp t
        ((hasDerivAt_id t).const_add xiStar)
      exact (h1.sub ((hasDerivAt_id t).mul_const _)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      have h1 := (hasDerivAt_rhoU (by linarith [ht.1] : xiStar < xiStar + t)).comp t
        ((hasDerivAt_id t).const_add xiStar)
      have h2 : HasDerivAt g (rhoUDeriv (xiStar + t) - rhoUDeriv (xiStar + r)) t := by
        refine (h1.sub ((hasDerivAt_id t).mul_const _)).congr_deriv ?_; ring
      rw [h2.deriv]
      have hanti := rhoUDeriv_strictAntiOn (by change xiStar < xiStar + t; linarith [ht.1])
        (by change xiStar < xiStar + r; linarith) (by linarith [ht.2])
      linarith)
  have h0 := hm (left_mem_Icc.mpr hr.le) (right_mem_Icc.mpr hr.le) hr.le
  dsimp [g] at h0
  simp only [add_zero, rhoU_xiStar, zero_mul, sub_self] at h0
  linarith

/-! ### Section 3: Cumulative count `N(y)`, quantiles `χ_a`, and Lemmas K0(b), K0(c) -/

/-- Cumulative zero count $N(y) = \frac{1}{2}\int_{\xi_*}^y \rho_U(t)\,dt$. -/
noncomputable def cumulN (y : ℝ) : ℝ := (1 / 2 : ℝ) * ∫ t in xiStar..y, rhoU t

lemma cumulN_xiStar : cumulN xiStar = 0 := by simp [cumulN]

lemma intervalIntegrable_rhoU {a b : ℝ} (ha : xiStar ≤ a) (hb : xiStar ≤ b) :
    IntervalIntegrable rhoU volume a b :=
  (continuousOn_rhoU.mono (fun _ ht => by
    simp only [Set.mem_uIcc, Set.mem_Ici] at ht ⊢
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)).intervalIntegrable

lemma continuousOn_cumulN : ContinuousOn cumulN (Ici xiStar) := by
  unfold cumulN
  refine continuousOn_const.mul ?_
  intro y hy
  have h1 : IntervalIntegrable rhoU volume xiStar (y + 1) :=
    intervalIntegrable_rhoU le_rfl (by linarith [hy.out])
  have hcont : ContinuousOn (fun u => ∫ t in xiStar..u, rhoU t) (Icc xiStar (y + 1)) :=
    (Set.uIcc_of_le (by linarith [hy.out] : xiStar ≤ y + 1)) ▸
      intervalIntegral.continuousOn_primitive_interval' h1
        (by rw [Set.uIcc_of_le (by linarith [hy.out])]; exact ⟨le_rfl, by linarith [hy.out]⟩)
  exact (hcont.continuousWithinAt ⟨hy, by linarith⟩).mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (inter_mem_nhdsWithin (Ici xiStar) (Iio_mem_nhds (by linarith : y < y + 1)))
      fun _ hx => ⟨hx.1, hx.2.le⟩)

lemma hasDerivAt_cumulN {y : ℝ} (hy : xiStar < y) :
    HasDerivAt cumulN (rhoU y / 2) y := by
  have hc_nhds : ContinuousAt rhoU y :=
    continuousOn_rhoU.continuousAt (Ici_mem_nhds hy)
  have hint : IntervalIntegrable rhoU volume xiStar y := intervalIntegrable_rhoU le_rfl hy.le
  have hmeas : StronglyMeasurableAtFilter rhoU (𝓝 y) :=
    (continuousOn_rhoU.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi y hy
  have hftc := intervalIntegral.integral_hasDerivAt_right hint hmeas hc_nhds
  exact ((hftc.const_mul (1 / 2 : ℝ)).congr_deriv (by ring))

lemma cumulN_strictMonoOn : StrictMonoOn cumulN (Ici xiStar) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici xiStar) continuousOn_cumulN fun y hy => ?_
  rw [interior_Ici] at hy
  rw [(hasDerivAt_cumulN hy).deriv]
  exact div_pos (rhoU_pos hy) two_pos

lemma cumulN_ge_sq_div_three {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 / 3 ≤ cumulN (xiStar + r) := by
  unfold cumulN
  have hsub : ∫ t in xiStar..(xiStar + r), rhoU t = ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) := by
    simpa [add_comm] using intervalIntegral.integral_comp_add_left rhoU xiStar (a := 0) (b := r)
  rw [hsub]
  have hint1 : IntervalIntegrable (fun s : ℝ => (4 / 3) * s) volume 0 r :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 r
  have hint2 : IntervalIntegrable (fun s : ℝ => rhoU (xiStar + s)) volume 0 r := by
    refine (continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable_of_Icc hr
    intro s hs; change xiStar ≤ xiStar + s; linarith [hs.1]
  have hmono := intervalIntegral.integral_mono_on hr hint1 hint2 fun s hs =>
    (le_max_right _ _).trans (rhoU_ge_max hs.1)
  have hval : ∫ s in (0 : ℝ)..r, (4 / 3 : ℝ) * s = (2 / 3) * r ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    simp; ring
  rw [hval] at hmono
  linarith

lemma tendsto_cumulN_atTop : Tendsto cumulN atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  refine ⟨xiStar + √(3 * max M 0), fun y hy => ?_⟩
  have hsq_nn : 0 ≤ √(3 * max M 0) := Real.sqrt_nonneg _
  have hy_sub : √(3 * max M 0) ≤ y - xiStar := by linarith
  have h1 := cumulN_ge_sq_div_three (hsq_nn.trans hy_sub)
  rw [add_sub_cancel] at h1
  have h2 : 3 * max M 0 ≤ (y - xiStar) ^ 2 := by
    calc 3 * max M 0 = √(3 * max M 0) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ (y - xiStar) ^ 2 := sq_le_sq' (by linarith) hy_sub
  calc M ≤ max M 0 := le_max_left _ _
    _ = (3 * max M 0) / 3 := by ring
    _ ≤ (y - xiStar) ^ 2 / 3 := by gcongr
    _ ≤ cumulN y := h1

lemma existsUnique_chiQuantile {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    ∃! y ∈ Ici xiStar, c' * cumulN y = a - 1 / 4 := by
  have hu : 0 ≤ (a - 1 / 4) / c' := div_nonneg (sub_nonneg.mpr ha) hc'.le
  have him : (a - 1 / 4) / c' ∈ Ici (cumulN xiStar) := by
    rw [cumulN_xiStar]; exact hu
  obtain ⟨y, hy_mem, hy_eq⟩ := intermediate_value_Ici continuousOn_cumulN tendsto_cumulN_atTop him
  refine ⟨y, ⟨hy_mem, ?_⟩, fun z ⟨hz_mem, hz_eq⟩ => ?_⟩
  · field_simp [hc'.ne'] at hy_eq ⊢; linarith
  · apply cumulN_strictMonoOn.injOn hz_mem hy_mem
    have h1 : c' * cumulN z = c' * cumulN y := by
      rw [hz_eq]; field_simp [hc'.ne'] at hy_eq ⊢; linarith
    exact mul_left_cancel₀ hc'.ne' h1

/-- Quantile site $\chi_a$ solving $c' N(\chi_a) = a - 1/4$ for $a \ge 1/4$ and $c' > 0$. -/
noncomputable def chiQuantile (c' a : ℝ) : ℝ :=
  if h : 0 < c' ∧ 1 / 4 ≤ a then
    Classical.choose (existsUnique_chiQuantile h.1 h.2).exists
  else xiStar

/-- Tip scale $\lambda = (k_{\mathrm{tip}} c')^{-2/3}$. -/
noncomputable def lambdaComb (c' : ℝ) : ℝ := (kTip * c') ^ (-(2 / 3 : ℝ))

/-- Quantile exponent $\Phi_a = (a - 1/4)^{2/3}$. -/
noncomputable def phiQuantile (a : ℝ) : ℝ := (a - 1 / 4) ^ (2 / 3 : ℝ)

/-- Tip offset $r_a = \chi_a - \xi_*$. -/
noncomputable def siteRadius (c' a : ℝ) : ℝ := chiQuantile c' a - xiStar

/-- Cell spacing $\ell_k = \chi_{k+1} - \chi_k$. -/
noncomputable def siteGap (c' : ℝ) (k : ℕ) : ℝ :=
  chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ)

/-- First derivative $\chi'_a = 2 / (c' \rho_U(\chi_a))$ for $a > 1/4$. -/
noncomputable def chiDeriv (c' a : ℝ) : ℝ := 2 / (c' * rhoU (chiQuantile c' a))

/-- Second derivative $\chi''_a = -(\chi'_a)^2 (\log \rho_U)'(\chi_a)$ for $a > 1/4$. -/
noncomputable def chiSecond (c' a : ℝ) : ℝ :=
  -(chiDeriv c' a) ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))

lemma chiQuantile_spec {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    xiStar ≤ chiQuantile c' a ∧ c' * cumulN (chiQuantile c' a) = a - 1 / 4 := by
  unfold chiQuantile
  rw [dif_pos ⟨hc', ha⟩]
  exact Classical.choose_spec (existsUnique_chiQuantile hc' ha).exists

lemma chiQuantile_eq_of_cumulN {c' a y : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a)
    (hy : xiStar ≤ y) (heq : c' * cumulN y = a - 1 / 4) :
    chiQuantile c' a = y :=
  (existsUnique_chiQuantile hc' ha).unique (chiQuantile_spec hc' ha) ⟨hy, heq⟩

lemma chiQuantile_quarter (c' : ℝ) (hc' : 0 < c') : chiQuantile c' (1 / 4) = xiStar :=
  chiQuantile_eq_of_cumulN hc' le_rfl le_rfl (by rw [cumulN_xiStar, mul_zero, sub_self])

lemma xiStar_lt_chiQuantile {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    xiStar < chiQuantile c' a := by
  have ⟨hle, heq⟩ := chiQuantile_spec hc' ha.le
  refine lt_of_le_of_ne hle ?_
  intro h
  rw [← h, cumulN_xiStar, mul_zero] at heq
  linarith

lemma chiQuantile_strictMonoOn {c' : ℝ} (hc' : 0 < c') :
    StrictMonoOn (chiQuantile c') (Ici (1 / 4)) := by
  intro a ha b hb hab
  have ha_spec := chiQuantile_spec hc' ha
  have hb_spec := chiQuantile_spec hc' hb
  by_contra hle
  push Not at hle
  have hcum : cumulN (chiQuantile c' b) ≤ cumulN (chiQuantile c' a) :=
    cumulN_strictMonoOn.monotoneOn hb_spec.1 ha_spec.1 hle
  have hmul : c' * cumulN (chiQuantile c' b) ≤ c' * cumulN (chiQuantile c' a) :=
    mul_le_mul_of_nonneg_left hcum hc'.le
  linarith

lemma continuousAt_chiQuantile {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    ContinuousAt (chiQuantile c') a := by
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  rw [Metric.continuousAt_iff]
  intro ε hε
  set ε' := min ε ((chiQuantile c' a - xiStar) / 2)
  have hε' : 0 < ε' := lt_min hε (by linarith)
  set y_neg := chiQuantile c' a - ε'
  set y_pos := chiQuantile c' a + ε'
  have hy_neg_xi : xiStar < y_neg := by
    dsimp [y_neg, ε']; linarith [min_le_right ε ((chiQuantile c' a - xiStar) / 2)]
  have hy_pos_gt : xiStar < y_pos := by
    dsimp [y_pos]; linarith
  have h_lt1 : c' * cumulN y_neg < a - 1 / 4 := by
    rw [← (chiQuantile_spec hc' ha.le).2]
    exact mul_lt_mul_of_pos_left
      (cumulN_strictMonoOn hy_neg_xi.le (chiQuantile_spec hc' ha.le).1 (by dsimp [y_neg]; linarith)) hc'
  have h_lt2 : a - 1 / 4 < c' * cumulN y_pos := by
    rw [← (chiQuantile_spec hc' ha.le).2]
    exact mul_lt_mul_of_pos_left
      (cumulN_strictMonoOn (chiQuantile_spec hc' ha.le).1 hy_pos_gt.le
        (by dsimp [y_pos]; linarith)) hc'
  set δ := min (min ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4))) ((a - 1 / 4) / 2)
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hb_dist : |b - a| < δ := by simpa [Real.dist_eq] using hb
  have hb_gt : 1 / 4 ≤ b := by
    have := (abs_lt.mp hb_dist).1
    linarith [min_le_right (min ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4))) ((a - 1 / 4) / 2)]
  have hb_spec := chiQuantile_spec hc' hb_gt
  have h1 : cumulN y_neg < cumulN (chiQuantile c' b) := by
    have : c' * cumulN y_neg < c' * cumulN (chiQuantile c' b) := by
      rw [hb_spec.2]
      linarith [(abs_lt.mp hb_dist).1,
        min_le_left ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4)),
        min_le_left (min ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4))) ((a - 1 / 4) / 2)]
    exact lt_of_mul_lt_mul_left this hc'.le
  have h2 : cumulN (chiQuantile c' b) < cumulN y_pos := by
    have : c' * cumulN (chiQuantile c' b) < c' * cumulN y_pos := by
      rw [hb_spec.2]
      linarith [(abs_lt.mp hb_dist).2,
        min_le_right ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4)),
        min_le_left (min ((a - 1 / 4) - c' * cumulN y_neg) (c' * cumulN y_pos - (a - 1 / 4))) ((a - 1 / 4) / 2)]
    exact lt_of_mul_lt_mul_left this hc'.le
  have hy1 : y_neg < chiQuantile c' b :=
    cumulN_strictMonoOn.lt_iff_lt hy_neg_xi.le hb_spec.1 |>.mp h1
  have hy2 : chiQuantile c' b < y_pos :=
    cumulN_strictMonoOn.lt_iff_lt hb_spec.1 hy_pos_gt.le |>.mp h2
  rw [Real.dist_eq, abs_lt]
  have hε'_le : ε' ≤ ε := min_le_left _ _
  constructor <;> linarith

/-- **K0(b), first and second derivatives of $\chi_a$**:
$\chi'_a = 2/(c'\rho_U(\chi_a))$ and $\chi''_a = -\chi_a'^2 (\log\rho_U)'(\chi_a) < 0$. -/
theorem hasDerivAt_chiQuantile {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    HasDerivAt (chiQuantile c') (chiDeriv c' a) a ∧
      HasDerivAt (chiDeriv c') (chiSecond c' a) a := by
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  have hrho_pos : 0 < rhoU (chiQuantile c' a) := rhoU_pos hχ_gt
  have h_cumul : HasDerivAt (fun y => c' * cumulN y + 1 / 4)
      (c' * rhoU (chiQuantile c' a) / 2) (chiQuantile c' a) := by
    have h1 := ((hasDerivAt_cumulN hχ_gt).const_mul c').add_const (1 / 4 : ℝ)
    refine h1.congr_deriv ?_; ring
  have h_ne : c' * rhoU (chiQuantile c' a) / 2 ≠ 0 := by positivity
  have h_inv_ev : ∀ᶠ b in 𝓝 a, c' * cumulN (chiQuantile c' b) + 1 / 4 = b := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    rw [(chiQuantile_spec hc' hb.out.le).2]; ring
  have h_d1 : HasDerivAt (chiQuantile c') (chiDeriv c' a) a := by
    have hd := HasDerivAt.of_local_left_inverse (continuousAt_chiQuantile hc' ha) h_cumul h_ne h_inv_ev
    refine hd.congr_deriv ?_
    unfold chiDeriv
    field_simp [hc'.ne', hrho_pos.ne']
  have h_rho_comp : HasDerivAt (fun b => rhoU (chiQuantile c' b))
      (rhoUDeriv (chiQuantile c' a) * chiDeriv c' a) a :=
    (hasDerivAt_rhoU hχ_gt).comp a h_d1
  have h_den : HasDerivAt (fun b => c' * rhoU (chiQuantile c' b))
      (c' * (rhoUDeriv (chiQuantile c' a) * chiDeriv c' a)) a :=
    h_rho_comp.const_mul c'
  have h_d2 := (hasDerivAt_const a (2 : ℝ)).div h_den (by positivity)
  refine ⟨h_d1, h_d2.congr_deriv ?_⟩
  unfold chiSecond chiDeriv
  field_simp [hc'.ne', hrho_pos.ne']
  ring

theorem chiSecond_neg {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    chiSecond c' a < 0 := by
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  have hr_pos : 0 < chiQuantile c' a - xiStar := sub_pos.mpr hχ_gt
  have hld := (logDeriv_rhoU_bounds hr_pos).1
  rw [add_sub_cancel] at hld
  have hcd : 0 < chiDeriv c' a := by
    unfold chiDeriv; exact div_pos two_pos (mul_pos hc' (rhoU_pos hχ_gt))
  unfold chiSecond
  have : 0 < (chiDeriv c' a) ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) :=
    mul_pos (sq_pos_of_pos hcd) hld
  linarith

theorem chiDeriv_strictAntiOn {c' : ℝ} (hc' : 0 < c') :
    StrictAntiOn (chiDeriv c') (Ioi (1 / 4)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (1 / 4))
    (fun a ha => (hasDerivAt_chiQuantile hc' ha).2.continuousAt.continuousWithinAt)
    fun a ha => ?_
  rw [interior_Ioi] at ha
  rw [(hasDerivAt_chiQuantile hc' ha).2.deriv]
  exact chiSecond_neg hc' ha

lemma continuousOn_chiQuantile {c' : ℝ} (hc' : 0 < c') :
    ContinuousOn (chiQuantile c') (Ici (1 / 4)) := by
  intro a ha
  rcases eq_or_lt_of_le (ha : 1 / 4 ≤ a) with rfl | ha_gt
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcum_pos : 0 < c' * cumulN (xiStar + ε) :=
      mul_pos hc' (lt_of_lt_of_le (by positivity) (cumulN_ge_sq_div_three hε.le))
    refine ⟨c' * cumulN (xiStar + ε), hcum_pos, fun b hb hdist => ?_⟩
    have hb_spec := chiQuantile_spec hc' hb
    have h_lt : c' * cumulN (chiQuantile c' b) < c' * cumulN (xiStar + ε) := by
      rw [hb_spec.2]
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb)] at hdist
      linarith
    have h_chi_lt : chiQuantile c' b < xiStar + ε :=
      cumulN_strictMonoOn.lt_iff_lt hb_spec.1 (show xiStar + ε ∈ Ici xiStar from le_add_of_nonneg_right hε.le) |>.mp
        (lt_of_mul_lt_mul_left h_lt hc'.le)
    rw [chiQuantile_quarter c' hc', Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb_spec.1)]
    linarith
  · exact (continuousAt_chiQuantile hc' ha_gt).continuousWithinAt

theorem chiQuantile_strictConcaveOn {c' : ℝ} (hc' : 0 < c') :
    StrictConcaveOn ℝ (Ici (1 / 4)) (chiQuantile c') := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici (1 / 4)) (continuousOn_chiQuantile hc') ?_
  intro a ha b hb hab
  rw [interior_Ici] at ha hb
  rw [(hasDerivAt_chiQuantile hc' ha).1.deriv, (hasDerivAt_chiQuantile hc' hb).1.deriv]
  exact chiDeriv_strictAntiOn hc' ha hb hab

/-- **K0(b), decreasing cell widths**: $\ell_k$ strictly decreases in $k \ge 1$. -/
theorem siteGap_strictAnti {c' : ℝ} (hc' : 0 < c') :
    StrictAnti (fun k : ℕ => siteGap c' (k + 1)) := by
  intro j k hjk
  have hgap : ∀ m : ℕ, 1 ≤ m → siteGap c' m = ∫ t in (m : ℝ)..((m : ℝ) + 1), chiDeriv c' t := by
    intro m hm
    have hm14 : 1 / 4 < (m : ℝ) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hcont : ContinuousOn (chiDeriv c') (Icc (m : ℝ) ((m : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hm14 ht.1)).2.continuousAt.continuousWithinAt
    have hint : IntervalIntegrable (chiDeriv c') volume (m : ℝ) ((m : ℝ) + 1) :=
      hcont.intervalIntegrable_of_Icc (by linarith)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (m : ℝ)) (b := (m : ℝ) + 1)
      (fun t ht => (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hm14
        ((Set.uIcc_of_le (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)) ▸ ht).1)).1) hint
    unfold siteGap; exact hftc.symm
  have hgj := hgap (j + 1) (by omega)
  have hgk := hgap (k + 1) (by omega)
  change siteGap c' (k + 1) < siteGap c' (j + 1)
  rw [hgj, hgk]
  have hj14 : 1 / 4 < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hk14 : 1 / 4 < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hsub : ∫ t in ((k + 1 : ℕ) : ℝ)..(((k + 1 : ℕ) : ℝ) + 1), chiDeriv c' t =
      ∫ t in ((j + 1 : ℕ) : ℝ)..(((j + 1 : ℕ) : ℝ) + 1), chiDeriv c' (t + ((k - j : ℕ) : ℝ)) := by
    have h_eq := intervalIntegral.integral_comp_add_right (chiDeriv c') ((k - j : ℕ) : ℝ)
      (a := ((j + 1 : ℕ) : ℝ)) (b := ((j + 1 : ℕ) : ℝ) + 1)
    have ha1 : ((j + 1 : ℕ) : ℝ) + ((k - j : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
      have : j + 1 + (k - j) = k + 1 := by omega
      exact_mod_cast this
    have ha2 : (((j + 1 : ℕ) : ℝ) + 1) + ((k - j : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by
      linarith
    rw [ha1, ha2] at h_eq
    exact h_eq.symm
  rw [hsub]
  have hkj_nn : (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkj_pos : (0 : ℝ) < ((k - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hjk
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
    (fun t ht => by
      have ht_kj : 1 / 4 < t + ((k - j : ℕ) : ℝ) := by
        have ht_ge : ((j + 1 : ℕ) : ℝ) ≤ t := ht.1
        linarith
      exact (ContinuousAt.comp (g := chiDeriv c') (f := fun x => x + ((k - j : ℕ) : ℝ))
        (hasDerivAt_chiQuantile hc' ht_kj).2.continuousAt
        (continuousAt_id.add continuousAt_const)).continuousWithinAt)
    (fun t ht => (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hj14 ht.1)).2.continuousAt.continuousWithinAt)
    (fun t ht => by
      have ht_gt : ((j + 1 : ℕ) : ℝ) < t := ht.1
      have ht14 : 1 / 4 < t := by linarith
      have htkj14 : 1 / 4 < t + ((k - j : ℕ) : ℝ) := by linarith
      exact (chiDeriv_strictAntiOn hc' ht14 htkj14 (by linarith)).le)
    ⟨((j + 1 : ℕ) : ℝ) + 1 / 2, ⟨by linarith, by linarith⟩, by
      have hmid14 : 1 / 4 < ((j + 1 : ℕ) : ℝ) + 1 / 2 := by linarith
      have hmidkj : 1 / 4 < ((j + 1 : ℕ) : ℝ) + 1 / 2 + ((k - j : ℕ) : ℝ) := by linarith
      exact chiDeriv_strictAntiOn hc' hmid14 hmidkj (by linarith)⟩

/-- **K0(b), derivative bound**: $\chi'_a \le r_a / (a - 1/4)$ for $a > 1/4$. -/
theorem chiDeriv_le_div {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    chiDeriv c' a ≤ siteRadius c' a / (a - 1 / 4) := by
  have h_num : (a - 1 / 4) * chiDeriv c' a ≤ siteRadius c' a := by
    let g : ℝ → ℝ := fun t => chiQuantile c' t - chiQuantile c' (1 / 4) - (t - 1 / 4) * chiDeriv c' a
    have hcont : ContinuousOn g (Icc (1 / 4) a) := by
      refine ((continuousOn_chiQuantile hc').mono
        (Icc_subset_Ici_self)).sub continuousOn_const |>.sub ?_
      exact (continuousOn_id.sub continuousOn_const).mul continuousOn_const
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (1 / 4) a) hcont
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (((hasDerivAt_chiQuantile hc' ht.1).1.sub_const _).sub
          (((hasDerivAt_id t).sub_const _).mul_const _)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        have hd : HasDerivAt g (chiDeriv c' t - chiDeriv c' a) t := by
          refine (((hasDerivAt_chiQuantile hc' ht.1).1.sub_const _).sub
            (((hasDerivAt_id t).sub_const _).mul_const _)).congr_deriv ?_; ring
        rw [hd.deriv]
        have hanti := (chiDeriv_strictAntiOn hc' ht.1 ha ht.2).le
        linarith)
    have h0 := hm (left_mem_Icc.mpr ha.le) (right_mem_Icc.mpr ha.le) ha.le
    dsimp [g] at h0
    rw [chiQuantile_quarter c' hc'] at h0
    simp only [sub_self, zero_mul] at h0
    unfold siteRadius; linarith
  exact (le_div_iff₀ (sub_pos.mpr ha)).mpr (by linarith)

/-- **K0(b), log-derivative bound**: $|(\log \chi')'(a)| \le 1 / (a - 1/4)$ for $a > 1/4$. -/
theorem abs_logDeriv_chiDeriv_le {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) :
    |chiSecond c' a / chiDeriv c' a| ≤ 1 / (a - 1 / 4) := by
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  have hcd_pos : 0 < chiDeriv c' a := by
    unfold chiDeriv; exact div_pos two_pos (mul_pos hc' (rhoU_pos hχ_gt))
  have hr_pos : 0 < siteRadius c' a := sub_pos.mpr hχ_gt
  have hld := (logDeriv_rhoU_bounds hr_pos).2
  have h_eq_y : xiStar + siteRadius c' a = chiQuantile c' a := by unfold siteRadius; ring
  rw [h_eq_y] at hld
  have hld_pos : 0 < rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a) := by
    have := (logDeriv_rhoU_bounds hr_pos).1
    rwa [h_eq_y] at this
  have hquot : chiSecond c' a / chiDeriv c' a =
      -chiDeriv c' a * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) := by
    unfold chiSecond; field_simp [hcd_pos.ne']
  rw [hquot, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hcd_pos.le hld_pos.le)]
  calc chiDeriv c' a * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))
      ≤ (siteRadius c' a / (a - 1 / 4)) * (1 / siteRadius c' a) :=
        mul_le_mul (chiDeriv_le_div hc' ha) hld hld_pos.le (div_nonneg hr_pos.le (sub_pos.mpr ha).le)
    _ = 1 / (a - 1 / 4) := by field_simp [hr_pos.ne']

/-- Constant $C_1 = 3\pi / (20\sqrt{2})$ in Lemma K0(c). -/
noncomputable def c1K0 : ℝ := 3 * π / (20 * √2)

lemma c1K0_pos : 0 < c1K0 := by unfold c1K0; positivity

/-- **K0(c), cumulative count bounds**:
$k_{\mathrm{tip}} r^{3/2} \le N(\xi_* + r) \le k_{\mathrm{tip}} r^{3/2}(1 + C_1 r)$ for all $r \ge 0$. -/
theorem cumulN_bounds {r : ℝ} (hr : 0 ≤ r) :
    kTip * r ^ (3 / 2 : ℝ) ≤ cumulN (xiStar + r) ∧
      cumulN (xiStar + r) ≤ kTip * r ^ (3 / 2 : ℝ) * (1 + c1K0 * r) := by
  unfold cumulN
  have hsub : ∫ t in xiStar..(xiStar + r), rhoU t = ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) := by
    simpa [add_comm] using intervalIntegral.integral_comp_add_left rhoU xiStar (a := 0) (b := r)
  rw [hsub]
  have hpi := Real.pi_pos
  have hk_pos : 0 < kTip := kTip_pos
  have hint_rho : IntervalIntegrable (fun s : ℝ => rhoU (xiStar + s)) volume 0 r := by
    refine (continuousOn_rhoU.comp (continuous_const.add continuous_id).continuousOn ?_).intervalIntegrable_of_Icc hr
    intro s hs; change xiStar ≤ xiStar + s; linarith [hs.1]
  have h_lb : kTip * r ^ (3 / 2 : ℝ) ≤ (1 / 2) * ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) := by
    have hint1 : IntervalIntegrable (fun s : ℝ => 3 * kTip * s ^ (1 / 2 : ℝ)) volume 0 r :=
      ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn).intervalIntegrable_of_Icc hr
    have hmono := intervalIntegral.integral_mono_on hr hint1 hint_rho fun s hs => by
      rw [← Real.sqrt_eq_rpow]
      exact (le_max_left _ _).trans (rhoU_ge_max hs.1)
    have hval : ∫ s in (0 : ℝ)..r, 3 * kTip * s ^ (1 / 2 : ℝ) =
        2 * kTip * r ^ (3 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
      rw [Real.zero_rpow (by norm_num), sub_zero]
      ring_nf
    rw [hval] at hmono
    linarith
  have h_ub : (1 / 2) * ∫ s in (0 : ℝ)..r, rhoU (xiStar + s) ≤
      kTip * r ^ (3 / 2 : ℝ) * (1 + c1K0 * r) := by
    have h_pt : ∀ s ∈ Icc (0 : ℝ) r,
        rhoU (xiStar + s) ≤ 3 * kTip * s ^ (1 / 2 : ℝ) +
          3 * kTip * (π / (4 * √2)) * s ^ (3 / 2 : ℝ) := by
      intro s hs
      have hsq := (rhoU_sq_bounds hs.1).2
      have h16 : (16 / 9 : ℝ) / (9 * kTip ^ 2) = π / (2 * √2) := by
        rw [nine_mul_kTip_sq]
        have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        field_simp [hpi.ne']
        nlinarith [hsq2]
      have hsq' : rhoU (xiStar + s) ^ 2 ≤
          9 * kTip ^ 2 * s * (1 + (π / (2 * √2)) * s) := by
        calc rhoU (xiStar + s) ^ 2 ≤ 9 * kTip ^ 2 * s + (16 / 9) * s ^ 2 := hsq
          _ = 9 * kTip ^ 2 * s * (1 + ((16 / 9) / (9 * kTip ^ 2)) * s) := by
              have hk9 : 9 * kTip ^ 2 ≠ 0 := by positivity
              field_simp [hk9]
          _ = 9 * kTip ^ 2 * s * (1 + (π / (2 * √2)) * s) := by rw [h16]
      have h_lin : 9 * kTip ^ 2 * s * (1 + (π / (2 * √2)) * s) ≤
          (3 * kTip * √s * (1 + (π / (4 * √2)) * s)) ^ 2 := by
        have h1 : 1 + (π / (2 * √2)) * s ≤ (1 + (π / (4 * √2)) * s) ^ 2 := by
          have hexp : (1 + (π / (4 * √2)) * s) ^ 2 =
              1 + (π / (2 * √2)) * s + ((π / (4 * √2)) * s) ^ 2 := by ring
          have hsqn : 0 ≤ ((π / (4 * √2)) * s) ^ 2 := sq_nonneg _
          linarith
        have hsq_s : √s ^ 2 = s := Real.sq_sqrt hs.1
        have hk_pos : 0 < kTip := kTip_pos
        have hs0 : 0 ≤ s := hs.1
        calc 9 * kTip ^ 2 * s * (1 + (π / (2 * √2)) * s)
            ≤ 9 * kTip ^ 2 * √s ^ 2 * (1 + (π / (4 * √2)) * s) ^ 2 := by
              rw [hsq_s]
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (3 * kTip * √s * (1 + (π / (4 * √2)) * s)) ^ 2 := by ring
      have hrhs_nn : 0 ≤ 3 * kTip * √s * (1 + (π / (4 * √2)) * s) := by
        have := hs.1; positivity
      have hle_sqrt : rhoU (xiStar + s) ≤ 3 * kTip * √s * (1 + (π / (4 * √2)) * s) := by
        nlinarith [rhoU_nonneg (xiStar + s), hsq'.trans h_lin]
      refine hle_sqrt.trans_eq ?_
      rw [Real.sqrt_eq_rpow]
      have hs_rpow : s ^ (1 / 2 : ℝ) * s = s ^ (3 / 2 : ℝ) := by
        rcases eq_or_lt_of_le hs.1 with rfl | hsp
        · simp [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
        · conv_lhs => arg 2; rw [← Real.rpow_one s]
          rw [← Real.rpow_add hsp]; norm_num
      calc 3 * kTip * s ^ (1 / 2 : ℝ) * (1 + π / (4 * √2) * s)
          = 3 * kTip * s ^ (1 / 2 : ℝ) + 3 * kTip * (π / (4 * √2)) * (s ^ (1 / 2 : ℝ) * s) := by ring
        _ = 3 * kTip * s ^ (1 / 2 : ℝ) + 3 * kTip * (π / (4 * √2)) * s ^ (3 / 2 : ℝ) := by rw [hs_rpow]
    have hint2 : IntervalIntegrable (fun s : ℝ => 3 * kTip * s ^ (1 / 2 : ℝ) +
        3 * kTip * (π / (4 * √2)) * s ^ (3 / 2 : ℝ)) volume 0 r := by
      refine IntervalIntegrable.add ?_ ?_
      · exact ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn).intervalIntegrable_of_Icc hr
      · exact ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn).intervalIntegrable_of_Icc hr
    have hmono := intervalIntegral.integral_mono_on hr hint_rho hint2 h_pt
    have hval : ∫ s in (0 : ℝ)..r, (3 * kTip * s ^ (1 / 2 : ℝ) +
        3 * kTip * (π / (4 * √2)) * s ^ (3 / 2 : ℝ)) =
        2 * kTip * r ^ (3 / 2 : ℝ) * (1 + c1K0 * r) := by
      have i1 : IntervalIntegrable (fun s : ℝ => 3 * kTip * s ^ (1 / 2 : ℝ)) volume 0 r :=
        ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn).intervalIntegrable_of_Icc hr
      have i2 : IntervalIntegrable (fun s : ℝ => 3 * kTip * (π / (4 * √2)) * s ^ (3 / 2 : ℝ)) volume 0 r :=
        ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).continuousOn).intervalIntegrable_of_Icc hr
      rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2)),
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 3 / 2)),
        Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), sub_zero, sub_zero]
      have hr_pow : r ^ (3 / 2 : ℝ) * r = r ^ (5 / 2 : ℝ) := by
        rcases eq_or_lt_of_le hr with rfl | hrp
        · simp [Real.zero_rpow (by norm_num : (5 / 2 : ℝ) ≠ 0)]
        · conv_lhs => arg 2; rw [← Real.rpow_one r]
          rw [← Real.rpow_add hrp]; norm_num
      rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, ← hr_pow]
      unfold c1K0; ring
    rw [hval] at hmono
    linarith
  exact ⟨h_lb, h_ub⟩

/-- **K0(c), global quantile bounds**:
$\lambda \Phi_a (1 - \frac{2 C_1}{3} \lambda \Phi_a) \le r_a \le \lambda \Phi_a$ for $c' > 0, a \ge 1/4$. -/
theorem siteRadius_bounds {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    lambdaComb c' * phiQuantile a * (1 - (2 * c1K0 / 3) * (lambdaComb c' * phiQuantile a)) ≤
        siteRadius c' a ∧
      siteRadius c' a ≤ lambdaComb c' * phiQuantile a := by
  have hk_pos : 0 < kTip := kTip_pos
  have hr_nn : 0 ≤ siteRadius c' a := sub_nonneg.mpr (chiQuantile_spec hc' ha).1
  have h_eq : c' * cumulN (xiStar + siteRadius c' a) = a - 1 / 4 := by
    have hspec := (chiQuantile_spec hc' ha).2
    unfold siteRadius
    simpa [add_sub_cancel] using hspec
  have h_rpow_id : c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) = a - 1 / 4 := by
    rcases eq_or_lt_of_le ha with rfl | ha_gt
    · unfold phiQuantile; simp [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    · have hl_nn : 0 ≤ lambdaComb c' := by unfold lambdaComb; positivity
      have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
      rw [Real.mul_rpow hl_nn hp_nn]
      have hl32 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
        unfold lambdaComb
        rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
      have hp32 : phiQuantile a ^ (3 / 2 : ℝ) = a - 1 / 4 := by
        unfold phiQuantile
        rw [← Real.rpow_mul (sub_nonneg.mpr ha), show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
          Real.rpow_one]
      rw [hl32, hp32]
      field_simp [hc'.ne', hk_pos.ne']
  have hN := cumulN_bounds hr_nn
  have h_ub : siteRadius c' a ≤ lambdaComb c' * phiQuantile a := by
    have hpow : siteRadius c' a ^ (3 / 2 : ℝ) ≤ (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) := by
      have h1 : c' * kTip * siteRadius c' a ^ (3 / 2 : ℝ) ≤
          c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) := by
        rw [h_rpow_id, ← h_eq]
        have := mul_le_mul_of_nonneg_left hN.1 hc'.le
        linarith
      exact le_of_mul_le_mul_left h1 (mul_pos hc' hk_pos)
    have hr32 := Real.rpow_le_rpow (by positivity) hpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hl_nn : 0 ≤ lambdaComb c' := by unfold lambdaComb; positivity
    have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
    rw [← Real.rpow_mul hr_nn, ← Real.rpow_mul (mul_nonneg hl_nn hp_nn),
      show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hr32
    exact hr32
  have h_lb : lambdaComb c' * phiQuantile a * (1 - (2 * c1K0 / 3) * (lambdaComb c' * phiQuantile a)) ≤
      siteRadius c' a := by
    set L := lambdaComb c' * phiQuantile a
    have hL_nn : 0 ≤ L := by dsimp [L]; unfold lambdaComb phiQuantile; positivity
    have hpow : L ^ (3 / 2 : ℝ) ≤ siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * L) := by
      have h1 : c' * kTip * L ^ (3 / 2 : ℝ) ≤
          c' * kTip * (siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * L)) := by
        rw [h_rpow_id, ← h_eq]
        have h2 : cumulN (xiStar + siteRadius c' a) ≤
            kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * L) :=
          hN.2.trans (by gcongr; exact c1K0_pos.le)
        linarith [mul_le_mul_of_nonneg_left h2 hc'.le]
      exact le_of_mul_le_mul_left h1 (mul_pos hc' hk_pos)
    have h_div : L ^ (3 / 2 : ℝ) * (1 + c1K0 * L)⁻¹ ≤ siteRadius c' a ^ (3 / 2 : ℝ) := by
      have hpos : 0 < 1 + c1K0 * L := by have := c1K0_pos; positivity
      rwa [mul_inv_le_iff₀ hpos]
    have hr_ge : L * (1 + c1K0 * L) ^ (-(2 / 3 : ℝ)) ≤ siteRadius c' a := by
      have hpos : 0 < 1 + c1K0 * L := by have := c1K0_pos; positivity
      have hr23 := Real.rpow_le_rpow (by positivity) h_div (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hL_nn,
        ← Real.rpow_mul hr_nn, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one,
        Real.rpow_one, ← Real.rpow_neg_one, ← Real.rpow_mul hpos.le,
        show (-1 : ℝ) * (2 / 3) = -(2 / 3) by norm_num] at hr23
      exact hr23
    have h_bern : ∀ u : ℝ, 0 ≤ u → 1 - (2 / 3 : ℝ) * u ≤ (1 + u) ^ (-(2 / 3 : ℝ)) := by
      intro u hu
      let g : ℝ → ℝ := fun x => (1 + x) ^ (-(2 / 3 : ℝ)) - (1 - (2 / 3 : ℝ) * x)
      have hc : ContinuousOn g (Icc 0 u) :=
        (((continuousOn_const.add continuousOn_id).rpow_const (fun t ht =>
          Or.inl (by change (1 : ℝ) + t ≠ 0; linarith [ht.1]))).sub
          (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
      have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hc
        (fun t ht => by
          rw [interior_Icc] at ht
          have ht1 : 0 < 1 + t := by linarith [ht.1]
          have hd1 : HasDerivAt (fun x => (1 + x) ^ (-(2 / 3 : ℝ)))
              (-(2 / 3) * (1 + t) ^ (-(2 / 3 : ℝ) - 1)) t :=
            (((hasDerivAt_id t).const_add (1 : ℝ)).rpow_const (p := -(2 / 3 : ℝ))
              (Or.inl ht1.ne')).congr_deriv (by simp only [id_eq]; ring)
          have hd2 : HasDerivAt (fun x => 1 - (2 / 3 : ℝ) * x) (-(2 / 3)) t := by
            have h := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul (2 / 3))
            exact (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
          exact (hd1.sub hd2).differentiableAt.differentiableWithinAt)
        (fun t ht => by
          rw [interior_Icc] at ht
          have ht1 : 0 < 1 + t := by linarith [ht.1]
          have hd1 : HasDerivAt (fun x => (1 + x) ^ (-(2 / 3 : ℝ)))
              (-(2 / 3) * (1 + t) ^ (-(2 / 3 : ℝ) - 1)) t :=
            (((hasDerivAt_id t).const_add (1 : ℝ)).rpow_const (p := -(2 / 3 : ℝ))
              (Or.inl ht1.ne')).congr_deriv (by simp only [id_eq]; ring)
          have hd2 : HasDerivAt (fun x => 1 - (2 / 3 : ℝ) * x) (-(2 / 3)) t := by
            have h := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul (2 / 3))
            exact (h.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
          have hd : HasDerivAt g (-(2 / 3) * (1 + t) ^ (-(2 / 3 : ℝ) - 1) - -(2 / 3)) t :=
            (hd1.sub hd2).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
          rw [hd.deriv]
          have hpow1 : (1 + t) ^ (-(2 / 3 : ℝ) - 1) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by norm_num)
          linarith)
      have h0 := hm (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
      dsimp [g] at h0
      simp only [add_zero, Real.one_rpow, mul_zero, sub_zero, sub_self] at h0
      linarith
    have h_u : 1 - (2 * c1K0 / 3) * L ≤ (1 + c1K0 * L) ^ (-(2 / 3 : ℝ)) := by
      have := h_bern (c1K0 * L) (mul_nonneg c1K0_pos.le hL_nn)
      linarith
    exact (mul_le_mul_of_nonneg_left h_u hL_nn).trans hr_ge
  exact ⟨h_lb, h_ub⟩

/-- **K0(c), when $r_a \le 1$**:
$r_a \ge (1 + C_1)^{-2/3} \lambda \Phi_a$ and $\chi'_a \le \frac{2}{3}(1 + C_1)^{1/3}\lambda(a - 1/4)^{-1/3}$. -/
theorem siteRadius_le_one_bounds {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a)
    (hr1 : siteRadius c' a ≤ 1) :
    (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile a) ≤ siteRadius c' a ∧
      chiDeriv c' a ≤ (2 / 3) * (1 + c1K0) ^ (1 / 3 : ℝ) * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
  have hk_pos : 0 < kTip := kTip_pos
  have hc1_pos : 0 < 1 + c1K0 := by have := c1K0_pos; positivity
  have hr_pos : 0 < siteRadius c' a := sub_pos.mpr (xiStar_lt_chiQuantile hc' ha)
  have h_eq : c' * cumulN (xiStar + siteRadius c' a) = a - 1 / 4 := by
    have hspec := (chiQuantile_spec hc' ha.le).2
    unfold siteRadius; simpa [add_sub_cancel] using hspec
  have h_rpow_id : c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) = a - 1 / 4 := by
    have hl_nn : 0 ≤ lambdaComb c' := by unfold lambdaComb; positivity
    have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
    rw [Real.mul_rpow hl_nn hp_nn]
    have hl32 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
      unfold lambdaComb
      rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
        Real.rpow_neg_one]
    have hp32 : phiQuantile a ^ (3 / 2 : ℝ) = a - 1 / 4 := by
      unfold phiQuantile
      rw [← Real.rpow_mul (sub_nonneg.mpr ha.le), show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
        Real.rpow_one]
    rw [hl32, hp32]; field_simp [hc'.ne', hk_pos.ne']
  have hN := (cumulN_bounds hr_pos.le).2
  have h_le : (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) ≤
      siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0) := by
    have h1 : c' * kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) ≤
        c' * kTip * (siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0)) := by
      rw [h_rpow_id, ← h_eq]
      have h2 : cumulN (xiStar + siteRadius c' a) ≤ kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0) :=
        calc cumulN (xiStar + siteRadius c' a)
            ≤ 1 * kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * siteRadius c' a) := by
              simpa [one_mul] using hN
          _ ≤ 1 * kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0 * 1) := by
              have hc1nn : 0 ≤ c1K0 := c1K0_pos.le
              gcongr
          _ = kTip * siteRadius c' a ^ (3 / 2 : ℝ) * (1 + c1K0) := by ring
      linarith [mul_le_mul_of_nonneg_left h2 hc'.le]
    exact le_of_mul_le_mul_left h1 (mul_pos hc' hk_pos)
  have h_div : (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) * (1 + c1K0)⁻¹ ≤
      siteRadius c' a ^ (3 / 2 : ℝ) := by
    rwa [mul_inv_le_iff₀ hc1_pos]
  have hl_nn : 0 ≤ lambdaComb c' := by unfold lambdaComb; positivity
  have hp_nn : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
  have hr_lb : (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile a) ≤ siteRadius c' a := by
    have hr23 := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (mul_nonneg hl_nn hp_nn) _)
      (inv_nonneg.mpr hc1_pos.le)) h_div (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hl_nn hp_nn) _) (inv_nonneg.mpr hc1_pos.le),
      ← Real.rpow_mul (mul_nonneg hl_nn hp_nn),
      ← Real.rpow_mul hr_pos.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one,
      Real.rpow_one, ← Real.rpow_neg_one, ← Real.rpow_mul hc1_pos.le,
      show (-1 : ℝ) * (2 / 3) = -(2 / 3) by norm_num, mul_comm] at hr23
    exact hr23
  refine ⟨hr_lb, ?_⟩
  have h_rho_lb : 3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ) ≤ rhoU (chiQuantile c' a) := by
    have h1 := (le_max_left _ _).trans (rhoU_ge_max hr_pos.le)
    unfold siteRadius at h1 ⊢
    rw [add_sub_cancel] at h1
    rwa [Real.sqrt_eq_rpow] at h1
  have hcd_le : chiDeriv c' a ≤ 2 / (3 * c' * kTip * siteRadius c' a ^ (1 / 2 : ℝ)) := by
    unfold chiDeriv
    have hpos : 0 < 3 * c' * kTip * siteRadius c' a ^ (1 / 2 : ℝ) := by positivity
    calc 2 / (c' * rhoU (chiQuantile c' a))
        ≤ 2 / (c' * (3 * kTip * siteRadius c' a ^ (1 / 2 : ℝ))) := by gcongr
      _ = 2 / (3 * c' * kTip * siteRadius c' a ^ (1 / 2 : ℝ)) := by ring
  have h_c_lam : (c' * kTip)⁻¹ = lambdaComb c' ^ (3 / 2 : ℝ) := by
    unfold lambdaComb
    rw [← Real.rpow_mul (by positivity), show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
      Real.rpow_neg_one, mul_comm]
  have hr_sqrt_lb : ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile a)) ^ (1 / 2 : ℝ) ≤
      siteRadius c' a ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hc1_pos.le _) (mul_nonneg hl_nn hp_nn)) hr_lb (by norm_num)
  have hr_sqrt_eq : ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile a)) ^ (1 / 2 : ℝ) =
      (1 + c1K0) ^ (-(1 / 3 : ℝ)) * lambdaComb c' ^ (1 / 2 : ℝ) * (a - 1 / 4) ^ (1 / 3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hc1_pos.le _) (mul_nonneg hl_nn hp_nn), Real.mul_rpow hl_nn hp_nn,
      ← Real.rpow_mul hc1_pos.le, show -(2 / 3 : ℝ) * (1 / 2) = -(1 / 3) by norm_num]
    unfold phiQuantile
    rw [← Real.rpow_mul (sub_nonneg.mpr ha.le), show (2 / 3 : ℝ) * (1 / 2) = 1 / 3 by norm_num,
      mul_assoc]
  rw [hr_sqrt_eq] at hr_sqrt_lb
  have h_rhs_eq : 2 / (3 * c' * kTip * ((1 + c1K0) ^ (-(1 / 3 : ℝ)) * lambdaComb c' ^ (1 / 2 : ℝ) *
      (a - 1 / 4) ^ (1 / 3 : ℝ))) =
      (2 / 3) * (1 + c1K0) ^ (1 / 3 : ℝ) * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
    have ha_pos : 0 < a - 1 / 4 := sub_pos.mpr ha
    have hl_pos : 0 < lambdaComb c' := by unfold lambdaComb; positivity
    have h_l_split : lambdaComb c' ^ (3 / 2 : ℝ) / lambdaComb c' ^ (1 / 2 : ℝ) = lambdaComb c' := by
      rw [← Real.rpow_sub hl_pos, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, Real.rpow_one]
    have h1_neg : ((1 + c1K0) ^ (-(1 / 3 : ℝ)))⁻¹ = (1 + c1K0) ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_neg hc1_pos.le, neg_neg]
    have ha_neg : ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ = (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_neg ha_pos.le]
    calc 2 / (3 * c' * kTip * ((1 + c1K0) ^ (-(1 / 3 : ℝ)) * lambdaComb c' ^ (1 / 2 : ℝ) *
            (a - 1 / 4) ^ (1 / 3 : ℝ)))
        = (2 / 3) * (c' * kTip)⁻¹ * ((1 + c1K0) ^ (-(1 / 3 : ℝ)))⁻¹ *
            (lambdaComb c' ^ (1 / 2 : ℝ))⁻¹ * ((a - 1 / 4) ^ (1 / 3 : ℝ))⁻¹ := by ring
      _ = (2 / 3) * lambdaComb c' ^ (3 / 2 : ℝ) * (1 + c1K0) ^ (1 / 3 : ℝ) *
            (lambdaComb c' ^ (1 / 2 : ℝ))⁻¹ * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
          rw [h_c_lam, h1_neg, ha_neg]
      _ = (2 / 3) * (1 + c1K0) ^ (1 / 3 : ℝ) * (lambdaComb c' ^ (3 / 2 : ℝ) /
            lambdaComb c' ^ (1 / 2 : ℝ)) * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by ring
      _ = (2 / 3) * (1 + c1K0) ^ (1 / 3 : ℝ) * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
          rw [h_l_split]
  refine hcd_le.trans ?_
  rw [← h_rhs_eq]
  have hden_pos : 0 < 3 * c' * kTip * ((1 + c1K0) ^ (-(1 / 3 : ℝ)) * lambdaComb c' ^ (1 / 2 : ℝ) *
      (a - 1 / 4) ^ (1 / 3 : ℝ)) := by
    have : 0 < a - 1 / 4 := sub_pos.mpr ha
    have : 0 < lambdaComb c' := by unfold lambdaComb; positivity
    positivity
  gcongr

lemma tendsto_lambdaComb_atTop : Tendsto lambdaComb atTop (𝓝 0) := by
  unfold lambdaComb
  have h1 : Tendsto (fun c' : ℝ => kTip * c') atTop atTop :=
    Tendsto.const_mul_atTop kTip_pos tendsto_id
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h1

/-- **K0(c), eventual uniform bound on $\ell_k \le \ell_1 \le \chi'_1 \le C \lambda$**:
for $c'$ large, every $\ell_k \le \ell_1 \le \chi'_1 \le C \lambda$ and $\ell_1 \le 1/2$. -/
theorem siteGap_eventually_le :
    ∃ C > 0, ∀ᶠ c' in atTop,
      (∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1) ∧
      siteGap c' 1 ≤ chiDeriv c' 1 ∧
      chiDeriv c' 1 ≤ C * lambdaComb c' ∧
      siteGap c' 1 ≤ 1 / 2 := by
  set C := (2 / 3 : ℝ) * (1 + c1K0) ^ (1 / 3 : ℝ) * (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ))
  refine ⟨C, by have := c1K0_pos; positivity, ?_⟩
  have h_ev1 : ∀ᶠ c' : ℝ in atTop, 0 < c' := eventually_gt_atTop 0
  have h_ev2 : ∀ᶠ c' in atTop, lambdaComb c' * phiQuantile 1 ≤ 1 := by
    have ht := (tendsto_lambdaComb_atTop.mul_const (phiQuantile 1))
    simp only [zero_mul] at ht
    exact ht.eventually_le_const zero_lt_one
  have h_ev3 : ∀ᶠ c' in atTop, C * lambdaComb c' ≤ 1 / 2 := by
    have ht := tendsto_lambdaComb_atTop.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_le_const (by norm_num)
  filter_upwards [h_ev1, h_ev2, h_ev3] with c' hc' hr1_bd hC_bd
  have hgap_le : siteGap c' 1 ≤ chiDeriv c' 1 := by
    let g : ℝ → ℝ := fun t => chiQuantile c' t - chiQuantile c' 1 - (t - 1) * chiDeriv c' 1
    have hcont : ContinuousOn g (Icc 1 2) := by
      refine ((continuousOn_chiQuantile hc').mono
        (fun t ht => by change 1 / 4 ≤ t; linarith [ht.1])).sub continuousOn_const |>.sub ?_
      exact (continuousOn_id.sub continuousOn_const).mul continuousOn_const
    have hm := antitoneOn_of_deriv_nonpos (convex_Icc (1 : ℝ) 2) hcont
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (((hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1.sub_const _).sub
          (((hasDerivAt_id t).sub_const _).mul_const _)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        have ht1 : (1 : ℝ) < t := ht.1
        have ht14 : (1 / 4 : ℝ) < t := by linarith
        have hd : HasDerivAt g (chiDeriv c' t - chiDeriv c' 1) t := by
          refine (((hasDerivAt_chiQuantile hc' ht14).1.sub_const _).sub
            (((hasDerivAt_id t).sub_const _).mul_const _)).congr_deriv ?_; ring
        rw [hd.deriv]
        have hanti := (chiDeriv_strictAntiOn hc' (by norm_num : (1 / 4 : ℝ) < 1) ht14 ht1).le
        linarith)
    have h12 := hm (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num)) (by norm_num)
    dsimp [g] at h12
    simp only [sub_self, zero_mul, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] at h12
    unfold siteGap; push_cast; norm_num; linarith
  have hr1 : siteRadius c' 1 ≤ 1 := (siteRadius_bounds hc' (by norm_num)).2.trans hr1_bd
  have hbd : chiDeriv c' 1 ≤ C * lambdaComb c' := by
    have h0 := (siteRadius_le_one_bounds hc' (by norm_num) hr1).2
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by ring] at h0
    exact h0.trans_eq (by dsimp [C]; ring)
  refine ⟨?_, hgap_le, hbd, hgap_le.trans (hbd.trans hC_bd)⟩
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hk_gt
  · exact le_rfl
  · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
    have heq : (k - 1) + 1 = k := by omega
    simpa [heq] using hanti

/-! ### Section 4: The index-$f$ reference comb $B^{(f)}$ and Lemma K1(a) -/

/-- The index-$f$ reference Blaschke comb ($f \ge 1$, $\eta_0 \in [0, 1/4]$):
$B^{(f)}(b) = T_{\chi_f}(b) \prod_{k \ge f + 1} T_{\chi_k + i\varepsilon_k}(b) T_{\chi_k - i\varepsilon_k}(b)$,
where $\varepsilon_k = \eta_0 \ell_k$. -/
noncomputable def refComb (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  blaschkeT (chiQuantile c' f : ℂ) b *
    ∏' m : ℕ, (blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b *
      blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b)

lemma summable_exp_neg_pi_chiQuantile {c' : ℝ} (hc' : 0 < c') (f : ℕ) :
    Summable fun m : ℕ => Real.exp (-π * chiQuantile c' (f + 1 + m : ℕ)) := by
  have hpi := Real.pi_pos
  have harccosh_le : ∀ x : ℝ, 1 ≤ x → arccoshR x ≤ Real.log (2 * x) := by
    intro x hx
    unfold arccoshR
    apply Real.log_le_log (by have := Real.sqrt_nonneg (x ^ 2 - 1); linarith)
    have hsqrt : √(x ^ 2 - 1) ≤ x := by rw [Real.sqrt_le_left (by positivity)]; linarith
    linarith
  have hrho_le : ∀ y : ℝ, xiStar ≤ y → rhoU y ≤ (4 / 3 : ℝ) * y + 4 / (3 * π) := by
    intro y hy
    rw [rhoU_eq_of_ge hy]
    have hy_nn : 0 ≤ y := xiStar_pos.le.trans hy
    have hs1 : 1 ≤ Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
    have hsh_le : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
      rw [Real.sinh_eq]; linarith [Real.exp_pos (-(π * y))]
    have hlog_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
      refine (harccosh_le _ hs1).trans ?_
      calc Real.log (2 * Real.sinh (π * y)) ≤ Real.log (Real.exp (π * y)) :=
            Real.log_le_log (by positivity) hsh_le
        _ = π * y := Real.log_exp _
    calc (4 / (3 * π)) * arccoshR (Real.sinh (π * y))
        ≤ (4 / (3 * π)) * (π * y) := by gcongr
      _ = (4 / 3) * y := by field_simp [hpi.ne']
      _ ≤ (4 / 3) * y + 4 / (3 * π) := le_add_of_nonneg_right (by positivity)
  have hN_le : ∀ y : ℝ, xiStar ≤ y → cumulN y ≤ y ^ 2 + y := by
    intro y hy
    unfold cumulN
    have hy0 : 0 ≤ xiStar := xiStar_pos.le
    have hy_nn : 0 ≤ y := hy0.trans hy
    have h1 : IntervalIntegrable rhoU volume xiStar y := intervalIntegrable_rhoU le_rfl hy
    have h2 : IntervalIntegrable (fun t => (4 / 3 : ℝ) * t + 4 / (3 * π)) volume xiStar y :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on hy h1 h2 fun t ht => hrho_le t ht.1
    have hval : ∫ t in xiStar..y, ((4 / 3 : ℝ) * t + 4 / (3 * π)) ≤
        (2 / 3 : ℝ) * y ^ 2 + (4 / (3 * π)) * y := by
      have hi1 : IntervalIntegrable (fun t : ℝ => (4 / 3 : ℝ) * t) volume xiStar y :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun _ : ℝ => (4 / (3 * π))) volume xiStar y :=
        intervalIntegrable_const
      rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      have hsub1 : (4 / 3 : ℝ) * ((y ^ 2 - xiStar ^ 2) / 2) ≤ (2 / 3 : ℝ) * y ^ 2 := by nlinarith [sq_nonneg xiStar]
      have h43pi_nn : 0 ≤ 4 / (3 * π) := by positivity
      have hsub2 : (y - xiStar) * (4 / (3 * π)) ≤ (4 / (3 * π)) * y :=
        calc (y - xiStar) * (4 / (3 * π)) = (4 / (3 * π)) * y - (4 / (3 * π)) * xiStar := by ring
          _ ≤ (4 / (3 * π)) * y := sub_le_self _ (mul_nonneg h43pi_nn hy0)
      linarith
    have h3 : (1 / 2 : ℝ) * ((2 / 3 : ℝ) * y ^ 2 + (4 / (3 * π)) * y) ≤ y ^ 2 + y := by
      have hpi3 : 4 / (3 * π) ≤ 2 := by
        calc 4 / (3 * π) ≤ 4 / (3 * 3) := by gcongr; exact Real.pi_gt_three.le
          _ ≤ 2 := by norm_num
      have hmul : (4 / (3 * π)) * y ≤ 2 * y := mul_le_mul_of_nonneg_right hpi3 hy_nn
      nlinarith [sq_nonneg y]
    linarith
  have hexp_sqrt : Summable fun m : ℕ => Real.exp (-π * √((m : ℝ) / c')) := by
    have hg : Summable fun m : ℕ => (24 * c' ^ 2 / π ^ 4) / ((m + 1 : ℕ) : ℝ) ^ 2 :=
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))).mul_left _
    have hle : ∀ m : ℕ, Real.exp (-π * √(((m + 1 : ℕ) : ℝ) / c')) ≤
        (24 * c' ^ 2 / π ^ 4) / ((m + 1 : ℕ) : ℝ) ^ 2 := by
      intro m
      set u := π * √(((m + 1 : ℕ) : ℝ) / c')
      have hu : 0 ≤ u := by positivity
      have h4 : u ^ 4 / 24 ≤ Real.exp u := by
        have hs := Real.sum_le_exp_of_nonneg hu 5
        have hterm : u ^ 4 / 24 ≤ ∑ i ∈ Finset.range 5, u ^ i / (i.factorial : ℝ) := by
          simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
          norm_num [Nat.factorial]
          linarith [pow_nonneg hu 0, pow_nonneg hu 1, pow_nonneg hu 2, pow_nonneg hu 3]
        exact hterm.trans hs
      have hu4 : u ^ 4 = π ^ 4 * (((m + 1 : ℕ) : ℝ) ^ 2 / c' ^ 2) := by
        dsimp [u]
        rw [mul_pow, show √(((m + 1 : ℕ) : ℝ) / c') ^ 4 =
          (√(((m + 1 : ℕ) : ℝ) / c') ^ 2) ^ 2 by ring,
          Real.sq_sqrt (by positivity), div_pow]
      rw [hu4] at h4
      rw [show (-π * √(((m + 1 : ℕ) : ℝ) / c')) = -u by ring, Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos u) (by positivity)]
      calc ((24 * c' ^ 2 / π ^ 4) / ((m + 1 : ℕ) : ℝ) ^ 2)⁻¹
          = π ^ 4 * (((m + 1 : ℕ) : ℝ) ^ 2 / c' ^ 2) / 24 := by
              rw [inv_div]; field_simp [hc'.ne', hpi.ne']
        _ ≤ Real.exp u := h4
    exact (summable_nat_add_iff 1).mp (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hg)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    (hexp_sqrt.mul_left (Real.exp π))
  have ha : (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := by
    have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    linarith
  have hspec := chiQuantile_spec hc' ha
  have hχ_nn : 0 ≤ chiQuantile c' (f + 1 + m : ℕ) := xiStar_pos.le.trans hspec.1
  have hm_le : ((m : ℝ) / c') ≤ (chiQuantile c' (f + 1 + m : ℕ) + 1) ^ 2 := by
    have h1 : (m : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) - 1 / 4 := by
      have : (m : ℝ) + 1 ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ f + 1 + m)
      linarith
    have h2 := hN_le (chiQuantile c' (f + 1 + m : ℕ)) hspec.1
    have h3 : (m : ℝ) ≤ c' * (chiQuantile c' (f + 1 + m : ℕ) + 1) ^ 2 := by
      have hsq : chiQuantile c' (f + 1 + m : ℕ) ^ 2 + chiQuantile c' (f + 1 + m : ℕ) ≤
          (chiQuantile c' (f + 1 + m : ℕ) + 1) ^ 2 := by nlinarith
      calc (m : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) - 1 / 4 := h1
        _ = c' * cumulN (chiQuantile c' (f + 1 + m : ℕ)) := hspec.2.symm
        _ ≤ c' * (chiQuantile c' (f + 1 + m : ℕ) ^ 2 + chiQuantile c' (f + 1 + m : ℕ)) := by
            gcongr
        _ ≤ c' * (chiQuantile c' (f + 1 + m : ℕ) + 1) ^ 2 := by gcongr
    rwa [div_le_iff₀ hc', mul_comm]
  have hsqrt_le : √((m : ℝ) / c') ≤ chiQuantile c' (f + 1 + m : ℕ) + 1 :=
    (Real.sqrt_le_sqrt hm_le).trans_eq (Real.sqrt_sq (by linarith))
  rw [mul_comm (Real.exp π), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **K1(a) for $B^{(f)}$**: for $c'$ large, $f \ge 1$, $\eta_0 \in [0, 1/4]$,
$B^{(f)}$ is holomorphic on $\{|\operatorname{Im} b| < 7/8\} \setminus \{\pm \chi_f\}$
(in fact the pair product converges locally uniformly on $\{|\operatorname{Im} b| < 7/8\}$),
satisfies $|B^{(f)}(b)| \le 1$ on $|\operatorname{Im} b| \le 1/2$, $|B^{(f)}(b)| = 1$ on $|\operatorname{Im} b| = 1/2$,
and $B^{(f)}(i/2) = -1$. -/
theorem refComb_K1a (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop,
      (∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖refComb c' f η₀ b‖ ≤ 1) ∧
      (∀ {b : ℂ}, |b.im| = 1 / 2 → ‖refComb c' f η₀ b‖ = 1) ∧
      refComb c' f η₀ (Complex.I / 2) = -1 ∧
      DifferentiableOn ℂ (refComb c' f η₀) {b : ℂ | |b.im| < 7 / 8} := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' ⟨hgap_k, _, _, hgap_1⟩
  set χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  set ε := fun m : ℕ => η₀ * siteGap c' (f + 1 + m)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have ha : (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := by
      have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
      linarith
    exact xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
    have hgap_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      have ha1 : (1 / 4 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
        linarith
      have ha2 : ((f + 1 + m : ℕ) : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) + 1 := by linarith
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn ha1 (ha1.trans ha2) ha2)
    have hε_nn : 0 ≤ ε m := mul_nonneg hη₀0 hgap_nn
    rw [abs_of_nonneg hε_nn]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) := mul_le_mul hη₀1 hgk hgap_nn (by norm_num)
      _ = 1 / 8 := by norm_num
  have hsum := summable_exp_neg_pi_chiQuantile hc' f
  have h_le1 := fun {b : ℂ} (hb : |b.im| ≤ 1 / 2) => comb_pairProd_norm_le_one χ ε hχ_nn hε_bd hsum hb
  have h_eq1 := fun {b : ℂ} (hb : |b.im| = 1 / 2) => comb_pairProd_norm_eq_one χ ε hχ_nn hε_bd hsum hb
  have h_half := comb_pairProd_half_I χ ε hε_bd
  have h_diff := comb_pairProd_differentiableOn χ ε hχ_nn hε_bd hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    unfold refComb
    rw [norm_mul]
    calc ‖blaschkeT (chiQuantile c' f : ℂ) b‖ *
          ‖∏' m : ℕ, _‖
        ≤ 1 * ‖∏' m : ℕ, _‖ := by gcongr; exact norm_blaschkeT_real_le_one _ hb
      _ = ‖∏' m : ℕ, _‖ := one_mul _
      _ ≤ 1 := h_le1 hb
  · intro b hb
    unfold refComb
    rw [norm_mul, norm_blaschkeT_real_eq_one _ hb, h_eq1 hb, mul_one]
  · unfold refComb
    have hT : blaschkeT (chiQuantile c' f : ℂ) (Complex.I / 2) = -1 :=
      blaschkeT_half_I (by simp)
    rw [hT, h_half, mul_one]
  · intro b hb
    have hd1 : DifferentiableAt ℂ (blaschkeT (chiQuantile c' f : ℂ)) b :=
      differentiableAt_blaschkeT (by simp; exact lt_trans hb (by norm_num))
    exact (hd1.differentiableWithinAt.mul (h_diff b hb))

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.rhoU_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.rhoU_strictMonoOn

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.rhoU_strictConcaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.rhoU_strictConcaveOn

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.rhoU_sq_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.rhoU_sq_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.logDeriv_rhoU_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.logDeriv_rhoU_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.hasDerivAt_chiQuantile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.hasDerivAt_chiQuantile

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.siteGap_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.siteGap_strictAnti

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.cumulN_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.cumulN_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.siteRadius_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.siteRadius_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.siteGap_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.siteGap_eventually_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.refComb_K1a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.refComb_K1a

end FormalResearch.ModularBootstrap.Upper.Comb
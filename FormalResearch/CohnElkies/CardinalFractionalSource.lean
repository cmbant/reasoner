module

public import FormalResearch.CohnElkies.TwoSaddleContraction
public import FormalResearch.CohnElkies.CardinalTruncation
public import FormalResearch.Special.AiryZeroSpacing
public import FormalResearch.Special.AiryCftSignUncertainty
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Fractional Stieltjes-resolvent cardinal source (`ce_o1_route.tex` Lemma O.11h)

Formalizes Lemma `O.11h` (`ceo:O11h`, `(ceo:O11h.1)`–`(ceo:O11h.9)`) of
`CFT/sign_uncertainty/paper/ce_o1_route.tex` (latest `origin/claude/nice-dirac-7zai6p`, commit `f5d5f213a`),
following the 0-indexed conventions of `ClosedResolvent.lean` and `TwoSaddleContraction.lean`
(`n : ℕ` corresponds to `airyZero (n + 1)`, so `n = 0` is `a₁ = airyZero 1` and `n + 1` is `a_{n+2}`).

* **Part 1 (`(ceo:O11h.1)`):** `fracJ2`, integrability/positivity (`p > 1/2`), IBP / `y = x^p` reduction,
  and Beta/reflection evaluation `fracJ2 p = 2 * α_p * (1 + α_p) / Real.sin (π * α_p)` (`α_p = 1/(2p)`).
* **Part 2 (`(ceo:O11h.2)`–`(ceo:O11h.3)` and Part (1)):** `cardinalTailSqSum`, `cardinalB`, `cardinalH`,
  `cardinalHC`, `cardinalP`, `cardinalQ`; `∑' n, b_n² = M`; pointwise and locally uniform convergence on
  `ℂ` and `ℝ`; `L²(ℝ)` `HasSum` and `airyPW` membership; `AiryClassG` membership for `P_h, Q_h` (`H_h ∈ airyPW`
  with `e(z)^{1/2}` decay matching `f5d5f213a`, whereas `H_h ∈ 𝒢` in the later live `.tex` fails since
  `-H_h(x) ≥ |b₀| L₀(x)` on `x > 0`); and `∫ P_h = M`, `∫ Q_h = 0`.
* **Part 3 (`(ceo:O11h.8)`):** `airyZero_counting_law`, `cohnE_counting_law`, Stieltjes IBP identity for
  `cardinalDh`, and `cardinalDh_asymptotic` / `cardinalDh_littleO`.
* **Part 4 (`(ceo:O11h.9)`):** `cardinalH_eq_untuned_sub`, `cardinalEtaHat_bounds`, `cardinalEtaHat_sqrt_bound`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexInnerProductSpace

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1: Exact integral `J_{2,p}` (`(ceo:O11h.1)`) -/

/-- The fractional cutoff deficiency integral `J_{2,p} = (1 / π) ∫_0^∞ (1 - φ_p(x)²) x^{-3/2} dx` (`(ceo:O11h.1)`). -/
noncomputable def fracJ2 (p : ℝ) : ℝ :=
  (1 / π) * ∫ x in Ioi (0 : ℝ), (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ))

private lemma ceVarphiP_pos (p : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 < ceVarphiP p x := by
  unfold ceVarphiP; exact inv_pos.mpr (by linarith [Real.rpow_nonneg hx p])

private lemma ceVarphiP_le_one (p : ℝ) {x : ℝ} (hx : 0 ≤ x) : ceVarphiP p x ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [Real.rpow_nonneg hx p])

private lemma one_sub_ceVarphiP_sq_nonneg (p : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - ceVarphiP p x ^ 2 := by
  have := (ceVarphiP_pos p hx).le; have := ceVarphiP_le_one p hx; nlinarith

private lemma one_sub_ceVarphiP_sq_pos (p : ℝ) {x : ℝ} (hx : 0 < x) : 0 < 1 - ceVarphiP p x ^ 2 := by
  have := (ceVarphiP_pos p hx.le).le
  have h1 : ceVarphiP p x < 1 := by unfold ceVarphiP; rw [inv_lt_one_iff₀]; right; linarith [Real.rpow_pos_of_pos hx p]
  nlinarith

private lemma one_sub_ceVarphiP_sq_le_one (p : ℝ) {x : ℝ} (_hx : 0 ≤ x) : 1 - ceVarphiP p x ^ 2 ≤ 1 := by
  linarith [sq_nonneg (ceVarphiP p x)]

private lemma one_sub_ceVarphiP_sq_le_two_rpow (p : ℝ) {x : ℝ} (hx : 0 ≤ x) : 1 - ceVarphiP p x ^ 2 ≤ 2 * x ^ p := by
  have := (ceVarphiP_pos p hx).le; have := ceVarphiP_le_one p hx
  have hden : 0 < 1 + x ^ p := by linarith [Real.rpow_nonneg hx p]
  have hsub : 1 - ceVarphiP p x ≤ x ^ p := by
    rw [show 1 - ceVarphiP p x = x ^ p / (1 + x ^ p) by unfold ceVarphiP; field_simp; ring]
    exact div_le_self (Real.rpow_nonneg hx p) (by linarith [Real.rpow_nonneg hx p])
  calc 1 - ceVarphiP p x ^ 2 = (1 - ceVarphiP p x) * (1 + ceVarphiP p x) := by ring
    _ ≤ x ^ p * 2 := mul_le_mul hsub (by linarith) (by linarith) (Real.rpow_nonneg hx p)
    _ = 2 * x ^ p := by ring

private lemma one_sub_ceVarphiP_sq_mul_le (p : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    1 - ceVarphiP p (h * x) ^ 2 ≤ 2 * h ^ p * x ^ p :=
  (one_sub_ceVarphiP_sq_le_two_rpow p (mul_nonneg hh hx)).trans_eq (by rw [Real.mul_rpow hh hx]; ring)

private lemma continuousOn_ceVarphiP_mul (p : ℝ) {h : ℝ} (hh : 0 < h) :
    ContinuousOn (fun t : ℝ => ceVarphiP p (h * t)) (Ioi 0) := fun t ht => by
  have hden : 1 + (h * t) ^ p ≠ 0 := by linarith [Real.rpow_pos_of_pos (mul_pos hh ht) p]
  exact ((continuousAt_const.add ((continuousAt_const.mul continuousAt_id).rpow_const
    (Or.inl (mul_pos hh ht).ne'))).inv₀ hden).continuousWithinAt

private lemma continuousOn_rpow_add (c r : ℝ) (hc : 0 < c) : ContinuousOn (fun t : ℝ => (t + c) ^ r) (Ioi 0) :=
  (continuousOn_id.add continuousOn_const).rpow_const fun t (ht : 0 < t) => Or.inl (by change t + c ≠ 0; linarith)

private lemma hasDerivAt_one_sub_ceVarphiP_sq_mul (p : ℝ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => 1 - ceVarphiP p (h * t) ^ 2)
      (2 * p * h ^ p * x ^ (p - 1) / (1 + (h * x) ^ p) ^ 3) x := by
  have hden : 1 + (h * x) ^ p ≠ 0 := by linarith [Real.rpow_pos_of_pos (mul_pos hh hx) p]
  have hr : HasDerivAt (fun t : ℝ => 1 + (h * t) ^ p) (p * (h * x) ^ (p - 1) * h) x := by
    simpa [mul_assoc] using ((Real.hasDerivAt_rpow_const (p := p) (Or.inl (mul_pos hh hx).ne')).comp x
      ((hasDerivAt_id' x).const_mul h)).const_add (1 : ℝ)
  refine (((hr.inv hden).pow 2).const_sub (1 : ℝ)).congr_deriv ?_
  have hpow : (h * x) ^ (p - 1) * h = h ^ p * x ^ (p - 1) := by
    rw [Real.mul_rpow hh.le hx.le, mul_right_comm, ← Real.rpow_add_one hh.ne']; ring_nf
  simp only [Pi.inv_apply]; norm_num
  rw [show 2 * p * h ^ p * x ^ (p - 1) = 2 * p * ((h * x) ^ (p - 1) * h) by rw [hpow]; ring]
  field_simp [hden]

private lemma tendsto_const_mul_rpow_nhdsGT_zero {c q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => c * x ^ q) (𝓝[>] 0) (𝓝 0) := by
  have h0 : c * (0 : ℝ) ^ q = 0 := by rw [Real.zero_rpow hq.ne']; ring
  conv_rhs => rw [← h0]
  exact ((continuous_const.mul (Real.continuous_rpow_const hq.le)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds

private lemma integrableOn_Ioc_rpow_of_lt {a c : ℝ} (ha : -1 < a) (hc : 0 ≤ c) :
    IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 c) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).mp (intervalIntegral.intervalIntegrable_rpow' ha)

/-- **Lemma O.11h (`(ceo:O11h.1)`), integrability:**
`x ↦ (1 - φ_p(x)²) x^{-3/2}` is integrable on `(0, ∞)` for `p > 1/2`. -/
theorem fracJ2_integrable {p : ℝ} (hp : 1 / 2 < p) :
    IntegrableOn (fun x : ℝ => (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
  have hce : ContinuousOn (ceVarphiP p) (Ioi 0) := fun x hx => by simpa [one_mul] using continuousOn_ceVarphiP_mul p one_pos x hx
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0)) :=
    ((continuousOn_const.sub (hce.pow 2)).mul
      (fun x (hx : 0 < x) => (continuousAt_id.rpow_const (Or.inl hx.ne')).continuousWithinAt)).aestronglyMeasurable measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine ((integrableOn_Ioc_rpow_of_lt (by linarith : -1 < p - 3 / 2) zero_le_one).const_mul 2).mono'
      (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    rw [Real.norm_of_nonneg (mul_nonneg (one_sub_ceVarphiP_sq_nonneg p hx0.le) (Real.rpow_nonneg hx0.le _))]
    calc (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)) ≤ (2 * x ^ p) * x ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (one_sub_ceVarphiP_sq_le_two_rpow p hx0.le) (Real.rpow_nonneg hx0.le _)
      _ = 2 * x ^ (p - 3 / 2) := by rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf
  · refine (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).mono'
      (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [Real.norm_of_nonneg (mul_nonneg (one_sub_ceVarphiP_sq_nonneg p hx0.le) (Real.rpow_nonneg hx0.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (one_sub_ceVarphiP_sq_le_one p hx0.le)

/-- **Lemma O.11h (`(ceo:O11h.1)`), positivity:** `0 < J_{2,p}` for `p > 1/2`. -/
theorem fracJ2_pos {p : ℝ} (hp : 1 / 2 < p) : 0 < fracJ2 p := by
  unfold fracJ2; refine mul_pos (div_pos one_pos Real.pi_pos) ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (fracJ2_integrable hp)]
  · have hsupp : Function.support (fun x : ℝ => (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ))) ∩ Ioi 0 = Ioi 0 := by
      ext x; simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro hx; exact (mul_pos (one_sub_ceVarphiP_sq_pos p hx) (Real.rpow_pos_of_pos hx _)).ne'
    rw [hsupp, Real.volume_Ioi]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (one_sub_ceVarphiP_sq_nonneg p hx.le) (Real.rpow_nonneg hx.le _)

private lemma integrableOn_ibp_j2 {p : ℝ} (hp : 1 / 2 < p) :
    IntegrableOn (fun x : ℝ => p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3)) (Ioi (0 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hmeas : AEStronglyMeasurable (fun x : ℝ => p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3))
      (volume.restrict (Ioi 0)) := ContinuousOn.aestronglyMeasurable (fun x (hx : 0 < x) => by
    have hden : (1 + x ^ p) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith [Real.rpow_pos_of_pos hx p])
    exact ((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hx.ne'))).mul
      ((continuousAt_id.rpow_const (Or.inl hx.ne')).div
        ((continuousAt_const.add (continuousAt_id.rpow_const (Or.inl hx.ne'))).pow 3) hden)).continuousWithinAt) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine ((integrableOn_Ioc_rpow_of_lt (by linarith : -1 < p - 3 / 2) zero_le_one).const_mul p).mono'
      (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1; have hden : 1 ≤ (1 + x ^ p) ^ 3 := one_le_pow₀ (by linarith [Real.rpow_pos_of_pos hx0 p])
    rw [Real.norm_of_nonneg (by positivity)]
    calc p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3) ≤ p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / 1) := by gcongr
      _ = p * x ^ (p - 3 / 2) := by rw [div_one, mul_assoc, ← Real.rpow_add hx0]; ring_nf
  · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -2 * p - 3 / 2 < -1) zero_lt_one).const_mul p).mono'
      (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hden : x ^ (3 * p) ≤ (1 + x ^ p) ^ 3 := by
      have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le p) (by linarith : x ^ p ≤ 1 + x ^ p) 3
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, show p * (3 : ℕ) = 3 * p by norm_cast; ring] at h1
    rw [Real.norm_of_nonneg (by positivity)]
    calc p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3) ≤ p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / x ^ (3 * p)) := by gcongr
      _ = p * x ^ (-2 * p - 3 / 2) := by rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, mul_assoc, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf

/-- **Lemma O.11h (`(ceo:O11h.1)`), IBP / `y = x^p` identity:**
`J_{2,p} = (4 / π) * ∫ y in Ioi 0, y ^ (-α_p) / (1 + y) ^ 3` with `α_p = 1 / (2 * p)`. -/
theorem fracJ2_eq_ibp_integral {p : ℝ} (hp : 1 / 2 < p) :
    fracJ2 p = (4 / π) * ∫ y in Ioi (0 : ℝ), y ^ (-(1 / (2 * p))) / (1 + y) ^ 3 := by
  have hp0 : 0 < p := by linarith
  let u : ℝ → ℝ := fun x => 1 - ceVarphiP p x ^ 2; let u' : ℝ → ℝ := fun x => 2 * p * x ^ (p - 1) / (1 + x ^ p) ^ 3
  let v : ℝ → ℝ := fun x => -2 * x ^ (-(1 / 2 : ℝ)); let v' : ℝ → ℝ := fun x => x ^ (-(3 / 2 : ℝ))
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := fun x hx => by simpa [u, u', one_mul] using hasDerivAt_one_sub_ceVarphiP_sq_mul p one_pos hx
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := fun x hx =>
    ((Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hx.ne')).const_mul (-2)).congr_deriv (by norm_num [v']; ring)
  have hu'v_eq : ∀ x, u' x * v x = -4 * (p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3)) := fun x => by dsimp [u', v]; ring
  have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) :=
    ((integrableOn_ibp_j2 hp).const_mul (-4)).congr (ae_of_all _ fun x => (hu'v_eq x).symm)
  have h_zero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_rpow_nhdsGT_zero (c := 4) (by linarith : 0 < p - 1 / 2))
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    have hu_bd : |u x| ≤ 2 * x ^ p := (abs_of_nonneg (one_sub_ceVarphiP_sq_nonneg p hx.le)).symm ▸ one_sub_ceVarphiP_sq_le_two_rpow p hx.le
    have hv_bd : |v x| = 2 * x ^ (-(1 / 2 : ℝ)) := by dsimp [v]; rw [abs_mul, abs_neg, abs_two, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
    calc |u x| * |v x| ≤ (2 * x ^ p) * (2 * x ^ (-(1 / 2 : ℝ))) := mul_le_mul hu_bd hv_bd.le (abs_nonneg _) (by positivity)
      _ = 4 * x ^ (p - 1 / 2) := by rw [show (2 * x ^ p) * (2 * x ^ (-(1 / 2 : ℝ))) = 4 * (x ^ p * x ^ (-(1 / 2 : ℝ))) by ring, ← Real.rpow_add hx]; ring_nf
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      conv_rhs => rw [show (0 : ℝ) = 2 * 0 by ring]
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x (hx : 0 < x)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    have hu_bd : |u x| ≤ 1 := (abs_of_nonneg (one_sub_ceVarphiP_sq_nonneg p hx.le)).symm ▸ one_sub_ceVarphiP_sq_le_one p hx.le
    have hv_bd : |v x| = 2 * x ^ (-(1 / 2 : ℝ)) := by dsimp [v]; rw [abs_mul, abs_neg, abs_two, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
    exact (mul_le_mul hu_bd hv_bd.le (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv (fracJ2_integrable hp) hu'v h_zero h_infty
  simp only [sub_zero, zero_sub] at hibp
  have hibp' : ∫ x in Ioi (0 : ℝ), (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)) =
      4 * ∫ x in Ioi (0 : ℝ), p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3) := by
    change ∫ x in Ioi (0 : ℝ), u x * v' x = _; simp_rw [hu'v_eq] at hibp; rw [hibp, integral_const_mul]; ring
  have hsub := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (-(1 / (2 * p))) / (1 + y) ^ 3) hp0
  have hsub_eq : ∫ x in Ioi (0 : ℝ), p * x ^ (p - 1) * (x ^ (-(1 / 2 : ℝ)) / (1 + x ^ p) ^ 3) =
      ∫ y in Ioi (0 : ℝ), y ^ (-(1 / (2 * p))) / (1 + y) ^ 3 := by
    rw [← hsub]; refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
    have hpow : (x ^ p) ^ (-(1 / (2 * p))) = x ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_mul hx.le]; congr 1; field_simp [hp0.ne']
    simp only [smul_eq_mul, hpow]
  unfold fracJ2; rw [hibp', hsub_eq]; ring

private lemma real_beta_integral_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (b : ℂ) (by simpa using ha) (by simpa using hb)
  unfold Complex.betaIntegral at h
  have e : ∀ u ∈ uIcc (0 : ℝ) 1, ((u : ℂ) ^ ((a : ℂ) - 1) * (1 - (u : ℂ)) ^ ((b : ℂ) - 1)) =
      ((u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := fun u hu => by
    rw [uIcc_of_le zero_le_one] at hu; push_cast
    rw [Complex.ofReal_cpow hu.1, Complex.ofReal_cpow (by linarith [hu.2])]; push_cast; rfl
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  exact_mod_cast h

/-- **Lemma O.11h (`(ceo:O11h.1)`), exact closed form:**
for `p > 1/2` (in particular `p ∈ (1/2, 1)`), with `α_p = 1 / (2 * p)`,
`J_{2,p} = 2 * α_p * (1 + α_p) / Real.sin (π * α_p)`. -/
theorem fracJ2_eq {p : ℝ} (hp : 1 / 2 < p) :
    let α := 1 / (2 * p)
    fracJ2 p = 2 * α * (1 + α) / Real.sin (π * α) := by
  intro α; have hp0 : 0 < p := by linarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α < 1 := by dsimp [α]; rw [div_lt_one (by linarith)]; linarith
  let φ : ℝ → ℝ := fun u => u / (1 - u)
  have hφ_img : φ '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
    ext y; simp only [mem_image, mem_Ioo, mem_Ioi, φ]
    exact ⟨by rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩; exact div_pos hu0 (by linarith),
      fun hy => ⟨y / (1 + y), ⟨div_pos hy (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩,
        by field_simp [show 1 + y ≠ 0 by linarith]; ring⟩⟩
  have hφ_deriv : ∀ u ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (((1 - u) ^ 2)⁻¹) (Ioo 0 1) u := fun u hu => by
    have h1u : 1 - u ≠ 0 := by linarith [hu.2]
    exact ((hasDerivAt_id' u).div ((hasDerivAt_id' u).const_sub 1) h1u |>.congr_deriv (by field_simp [h1u]; ring)).hasDerivWithinAt
  have hφ_inj : InjOn φ (Ioo (0 : ℝ) 1) := fun u hu v hv h => by
    dsimp [φ] at h; rw [div_eq_div_iff (by linarith [hu.2]) (by linarith [hv.2])] at h; linarith
  have hcov : ∫ u in Ioo (0 : ℝ) 1, |((1 - u) ^ 2)⁻¹| • ((φ u) ^ (-α) / (1 + φ u) ^ 3) =
      ∫ y in Ioi (0 : ℝ), y ^ (-α) / (1 + y) ^ 3 := by
    rw [← hφ_img]
    exact (integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφ_deriv hφ_inj (fun y : ℝ => y ^ (-α) / (1 + y) ^ 3)).symm
  have h_Ioo : ∫ y in Ioi (0 : ℝ), y ^ (-α) / (1 + y) ^ 3 = ∫ u in (0 : ℝ)..1, u ^ ((1 - α) - 1) * (1 - u) ^ ((2 + α) - 1) := by
    rw [← hcov, intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu0 : 0 < u := hu.1; have hu1 : 0 < 1 - u := by linarith [hu.2]
    have h1add : 1 + φ u = (1 - u)⁻¹ := by dsimp [φ]; field_simp [hu1.ne']; ring
    have hrpow_div : (φ u) ^ (-α) = u ^ (-α) * (1 - u) ^ α := by
      dsimp [φ]; rw [Real.div_rpow hu0.le hu1.le, div_eq_mul_inv, ← Real.rpow_neg hu1.le, neg_neg]
    have hjac : ((1 - u) ^ 2)⁻¹ = (1 - u) ^ (-2 : ℝ) := by rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hu1.le, Real.rpow_natCast]
    have hcub : ((1 - u)⁻¹) ^ 3 = (1 - u) ^ (-3 : ℝ) := by rw [← Real.rpow_natCast, Real.inv_rpow hu1.le, ← Real.rpow_neg hu1.le]; norm_cast
    simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu1))]
    rw [h1add, hrpow_div, hjac, hcub, div_eq_mul_inv, ← Real.rpow_neg hu1.le, neg_neg]
    have hcomb : (1 - u) ^ (-2 : ℝ) * (1 - u) ^ α * (1 - u) ^ (3 : ℝ) = (1 - u) ^ ((2 + α) - 1) := by
      rw [← Real.rpow_add hu1, ← Real.rpow_add hu1]; congr 1; ring
    calc (1 - u) ^ (-2 : ℝ) * (u ^ (-α) * (1 - u) ^ α * (1 - u) ^ (3 : ℝ))
        = u ^ (-α) * ((1 - u) ^ (-2 : ℝ) * (1 - u) ^ α * (1 - u) ^ (3 : ℝ)) := by ring
      _ = u ^ ((1 - α) - 1) * (1 - u) ^ ((2 + α) - 1) := by rw [hcomb, sub_sub_cancel_left]
  have hG3 : Real.Gamma 3 = 2 := by rw [show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  have hG2 : Real.Gamma (2 + α) = (1 + α) * α * Real.Gamma α := by
    rw [show (2 : ℝ) + α = (1 + α) + 1 by ring, Real.Gamma_add_one (by linarith), show 1 + α = α + 1 by ring, Real.Gamma_add_one hα0.ne']; ring
  have hsin_ne : Real.sin (π * α) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hα0) (by nlinarith [Real.pi_pos])).ne'
  rw [fracJ2_eq_ibp_integral hp, show 1 / (2 * p) = α from rfl, h_Ioo, real_beta_integral_of_pos (by linarith) (by linarith),
    show (1 - α) + (2 + α) = 3 by ring, hG3, hG2, show Real.Gamma (1 - α) * ((1 + α) * α * Real.Gamma α) =
      (1 + α) * α * (Real.Gamma α * Real.Gamma (1 - α)) by ring, Real.Gamma_mul_Gamma_one_sub α]
  field_simp [Real.pi_ne_zero, hsin_ne]; ring

/-! ### Part 2: Generic square-summable cardinal series and Part (1) of Lemma O.11h -/

private lemma cohnE_nonneg (n : ℕ) : 0 ≤ cohnE n := by
  unfold cohnE; linarith [airyZero_anti le_rfl (Nat.le_add_left 1 n)]

/-- `L_n` is entire on `ℂ`. -/
lemma differentiable_cohnLC (n : ℕ) : Differentiable ℂ (cohnLC n) := fun z =>
  ((Complex.differentiableOn_dslope (s := univ) (f := airyAiC) (c := (airyZero (n + 1) : ℂ))
    Filter.univ_mem).2 differentiable_airyAiC.differentiableOn z (mem_univ z)).differentiableAt Filter.univ_mem

/-- The entire representative of `cohnLL2 n ∈ airyPW` is `cohnLC n`. -/
lemma airyPWFun_cohnLL2 (n : ℕ) (z : ℂ) : airyPWFun (cohnLL2 n) z = cohnLC n z := by
  have hae : (fun u : ℝ => airyPWFun (cohnLL2 n) (u : ℂ)) =ᵐ[volume] fun u : ℝ => cohnLC n (u : ℂ) := by
    filter_upwards [airyPWFun_ae (cohnLL2_mem_airyPW n), cohnLL2_ae n] with u hu1 hu2; rw [← hu1, hu2, cohnLC_ofReal]
  have hreal : ∀ u : ℝ, airyPWFun (cohnLL2 n) (u : ℂ) = cohnLC n (u : ℂ) :=
    congrFun (((differentiable_airyPWFun _).continuous.comp Complex.continuous_ofReal).ae_eq_iff_eq volume
      ((differentiable_cohnLC n).continuous.comp Complex.continuous_ofReal) |>.mp hae)
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), airyPWFun (cohnLL2 n) w - cohnLC n w = 0 :=
    (tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall (s := ({0}ᶜ : Set ℝ)) (fun (u : ℝ) (hu : u ≠ 0) => Complex.ofReal_ne_zero.mpr hu)⟩).frequently
      (Eventually.frequently (Eventually.of_forall fun u => by rw [hreal u, sub_self]))
  exact sub_eq_zero.mp (AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun w _ => ((differentiable_airyPWFun _).sub (differentiable_cohnLC n)).analyticAt w)
    isPreconnected_univ (mem_univ (0 : ℂ)) hfreq (mem_univ z))

private lemma inner_airyKerCL2_cohnLL2 (z : ℂ) (n : ℕ) : inner ℂ (airyKerCL2 z) (cohnLL2 n) = cohnLC n z := by
  rw [← airyPW_eval_inner (cohnLL2_mem_airyPW n) z, airyPWFun_cohnLL2]

/-- Generic `L²`, `airyPW`, pointwise `HasSum`, and growth bound for any square-summable real sequence `b`. -/
lemma cardinal_series_of_sq_hasSum {b : ℕ → ℝ} {S : ℝ} (hb : HasSum (fun n : ℕ => b n ^ 2) S) :
    let F : AiryL2 := ∑' n : ℕ, (b n : ℂ) • cohnLL2 n
    F ∈ airyPW ∧ ‖F‖ ^ 2 = S ∧ HasSum (fun n : ℕ => (b n : ℂ) • cohnLL2 n) F ∧
    (∀ z : ℂ, HasSum (fun n : ℕ => (b n : ℂ) * cohnLC n z) (airyPWFun F z)) ∧
    (∀ u : ℝ, HasSum (fun n : ℕ => b n * cohnL n u) (airyPWFun F (u : ℂ)).re ∧
      (airyPWFun F (u : ℂ)) = ((airyPWFun F (u : ℂ)).re : ℂ)) ∧
    (∃ hmem : MemLp (fun u : ℝ => (airyPWFun F (u : ℂ))) 2 volume, hmem.toLp _ = F) ∧
    (∀ z : ℂ, ‖airyPWFun F z‖ ^ 2 ≤ 23 * S * (1 + ‖z‖) * airyEnv z) := by
  intro F
  have hHasSum : HasSum (fun n : ℕ => (b n : ℂ) • cohnLL2 n) F :=
    ((cohnLL2_orthonormal.orthogonalFamily.summable_iff_norm_sq_summable (fun n => (b n : ℂ))).mpr
      (hb.summable.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])).hasSum
  have hPW : F ∈ airyPW := isClosed_airyPW.mem_of_tendsto hHasSum.tendsto_sum_nat
    (Eventually.of_forall fun _ => Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (cohnLL2_mem_airyPW n))
  have hnorm_sq : ‖F‖ ^ 2 = S := by
    have h_partial : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, (b n : ℂ) • cohnLL2 n‖ ^ 2 = ∑ n ∈ Finset.range N, b n ^ 2 := fun N => by
      have ho := cohnLL2_orthonormal.orthogonalFamily.norm_sum (fun n => (b n : ℂ)) (Finset.range N)
      change ‖∑ n ∈ Finset.range N, (b n : ℂ) • cohnLL2 n‖ ^ 2 = _ at ho
      exact ho.trans (Finset.sum_congr rfl fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
    exact tendsto_nhds_unique ((hHasSum.tendsto_sum_nat.norm.pow 2).congr h_partial) hb.tendsto_sum_nat
  have hptC : ∀ z : ℂ, HasSum (fun n : ℕ => (b n : ℂ) * cohnLC n z) (airyPWFun F z) := fun z => by
    rw [airyPW_eval_inner hPW z]
    exact (hHasSum.mapL (innerSL ℂ (airyKerCL2 z))).congr_fun fun n => by rw [innerSL_apply_apply, inner_smul_right, inner_airyKerCL2_cohnLL2]
  have hptR : ∀ u : ℝ, HasSum (fun n : ℕ => b n * cohnL n u) (airyPWFun F (u : ℂ)).re ∧
      airyPWFun F (u : ℂ) = ((airyPWFun F (u : ℂ)).re : ℂ) := fun u => by
    have hc := hptC (u : ℂ)
    have him : (airyPWFun F (u : ℂ)).im = 0 := by
      have hmap := hc.mapL Complex.imCLM
      rw [show (fun n : ℕ => Complex.imCLM ((b n : ℂ) * cohnLC n (u : ℂ))) = 0 from
        funext fun n => by simp [Complex.imCLM_apply, cohnLC_ofReal]] at hmap
      change (airyPWFun F (u : ℂ)).im = 0; exact (hasSum_zero.unique hmap).symm
    exact ⟨(hc.mapL Complex.reCLM).congr_fun fun n => by simp [cohnLC_ofReal], Complex.ext rfl (by simpa using him)⟩
  have hmem : MemLp (fun u : ℝ => airyPWFun F (u : ℂ)) 2 volume := (Lp.memLp F).ae_eq (airyPWFun_ae hPW)
  exact ⟨hPW, hnorm_sq, hHasSum, hptC, hptR, ⟨hmem, Lp.ext (hmem.coeFn_toLp.trans (airyPWFun_ae hPW).symm)⟩,
    fun z => hnorm_sq ▸ norm_airyPWFun_sq_le F z⟩

/-- Generic locally uniform convergence on `ℂ` for any cardinal series dominated by `|cohnC a n|`. -/
lemma cardinal_series_tendstoLocallyUniformlyC {b : ℕ → ℝ} {a : ℝ} {f : ℂ → ℂ}
    (hbd : ∀ᶠ n in atTop, |b n| ≤ |cohnC a n|) (hf : ∀ z : ℂ, HasSum (fun n : ℕ => (b n : ℂ) * cohnLC n z) (f z)) :
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N, (b n : ℂ) * cohnLC n z) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]; intro K hK
  rcases K.eq_empty_or_nonempty with rfl | ⟨z0, hz0⟩; · simp [tendstoUniformlyOn_empty]
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn differentiable_airyAiC.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z0 hz0)
  rw [show f = fun z => ∑' n : ℕ, (b n : ℂ) * cohnLC n z from funext fun z => (hf z).tsum_eq.symm]
  refine tendstoUniformlyOn_tsum_nat_eventually (airyCft_summable_inv_sq.mul_left (4 * M)) ?_
  filter_upwards [airyCft_eventually_ge (2 * (R + |a| + 1)), hbd] with n hn hbn z hz
  have hz_le : ‖z‖ ≤ R := hR z hz; have hpos : 0 < -airyZero (n + 1) / 2 := by linarith [airyZero_neg (n + 1)]
  have hza_ge : -airyZero (n + 1) / 2 ≤ ‖z - (airyZero (n + 1) : ℂ)‖ := by
    have hnorm := norm_sub_norm_le (airyZero (n + 1) : ℂ) z
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg (n + 1))] at hnorm; linarith [abs_nonneg a]
  have hca_ge : -airyZero (n + 1) / 2 ≤ |airyZero (n + 1) - a| := by
    have h1 := abs_sub_abs_le_abs_sub (airyZero (n + 1)) a; rw [abs_of_neg (airyZero_neg (n + 1))] at h1; linarith [norm_nonneg z, abs_nonneg a]
  have hzne : z ≠ (airyZero (n + 1) : ℂ) := fun h => by rw [h, sub_self, norm_zero] at hza_ge; linarith
  have hb_le : |b n| ≤ (-airyZero (n + 1) / 2)⁻¹ := hbn.trans (by rw [cohnC, abs_inv]; exact inv_anti₀ hpos hca_ge)
  have hL_le : ‖cohnLC n z‖ ≤ M / (-airyZero (n + 1) / 2) := by
    rw [cohnLC, dslope_of_ne _ hzne, slope_def_field, airyAiC_ofReal, airyAi_airyZero, Complex.ofReal_zero, sub_zero, norm_div]
    exact div_le_div₀ hM0 (hM z hz) hpos hza_ge
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |b n| * ‖cohnLC n z‖ ≤ (-airyZero (n + 1) / 2)⁻¹ * (M / (-airyZero (n + 1) / 2)) := mul_le_mul hb_le hL_le (norm_nonneg _) (inv_pos.mpr hpos).le
    _ = 4 * M * ((airyZero (n + 1)) ^ 2)⁻¹ := by have hne := (airyZero_neg (n + 1)).ne; field_simp; ring

/-- Generic locally uniform convergence on `ℝ` deduced from `ℂ`. -/
lemma cardinal_series_tendstoLocallyUniformlyR {b : ℕ → ℝ} {fC : ℂ → ℂ} {fR : ℝ → ℝ}
    (hC : TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N, (b n : ℂ) * cohnLC n z) fC atTop)
    (hreal : ∀ u : ℝ, fC (u : ℂ) = (fR u : ℂ)) :
    TendstoLocallyUniformly (fun N u => ∑ n ∈ Finset.range N, b n * cohnL n u) fR atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]; intro K hK
  have hCu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hC) (Complex.ofReal '' K) (hK.image Complex.continuous_ofReal)
  rw [Metric.tendstoUniformlyOn_iff] at hCu ⊢; intro ε hε
  filter_upwards [hCu ε hε] with N hN u hu
  have h := hN (u : ℂ) ⟨u, hu, rfl⟩
  have hsum : (∑ n ∈ Finset.range N, (b n : ℂ) * cohnLC n (u : ℂ)) = ((∑ n ∈ Finset.range N, b n * cohnL n u : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun n _ => by rw [cohnLC_ofReal]
  rw [dist_eq_norm, hreal u, hsum, ← Complex.ofReal_sub, Complex.norm_real] at h; simpa [Real.dist_eq] using h

private def cardinalSeriesProps (b : ℕ → ℝ) (S : ℝ) (fC : ℂ → ℂ) (fR : ℝ → ℝ) : Prop :=
  let F : AiryL2 := ∑' n : ℕ, (b n : ℂ) • cohnLL2 n
  F ∈ airyPW ∧ ‖F‖ ^ 2 = S ∧ HasSum (fun n : ℕ => (b n : ℂ) • cohnLL2 n) F ∧
  (∀ z : ℂ, fC z = airyPWFun F z ∧ HasSum (fun n : ℕ => (b n : ℂ) * cohnLC n z) (fC z)) ∧
  (∀ u : ℝ, fR u = (airyPWFun F (u : ℂ)).re ∧ HasSum (fun n : ℕ => b n * cohnL n u) (fR u) ∧ fC (u : ℂ) = (fR u : ℂ)) ∧
  TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N, (b n : ℂ) * cohnLC n z) fC atTop ∧
  TendstoLocallyUniformly (fun N u => ∑ n ∈ Finset.range N, b n * cohnL n u) fR atTop ∧
  (∃ hmem : MemLp (fun u : ℝ => (fR u : ℂ)) 2 volume, hmem.toLp _ = F) ∧
  (∀ z : ℂ, ‖fC z‖ ^ 2 ≤ 23 * S * (1 + ‖z‖) * airyEnv z)

private lemma cardinal_series_pack {b : ℕ → ℝ} {S a : ℝ} {fC : ℂ → ℂ} {fR : ℝ → ℝ}
    (hb : HasSum (fun n : ℕ => b n ^ 2) S) (hfC : ∀ z, fC z = ∑' n : ℕ, (b n : ℂ) * cohnLC n z)
    (hfR : ∀ u, fR u = ∑' n : ℕ, b n * cohnL n u) (hbd : ∀ᶠ n in atTop, |b n| ≤ |cohnC a n|) :
    cardinalSeriesProps b S fC fR := by
  obtain ⟨hPW, hnorm, hHasSum, hptC, hptR, ⟨hmemC, htoLpC⟩, hbdPW⟩ := cardinal_series_of_sq_hasSum hb
  have hCeq : ∀ z, fC z = airyPWFun (∑' n : ℕ, (b n : ℂ) • cohnLL2 n) z := fun z => (hfC z).trans (hptC z).tsum_eq
  have hReq : ∀ u, fR u = (airyPWFun (∑' n : ℕ, (b n : ℂ) • cohnLL2 n) (u : ℂ)).re := fun u => (hfR u).trans (hptR u).1.tsum_eq
  have hLUC := cardinal_series_tendstoLocallyUniformlyC hbd (fun z => (hCeq z).symm ▸ hptC z)
  have hLUR := cardinal_series_tendstoLocallyUniformlyR (fR := fR) hLUC (fun u => by rw [hCeq u, (hptR u).2, ← hReq u])
  have hmemR : MemLp (fun u : ℝ => (fR u : ℂ)) 2 volume := hmemC.ae_eq (Eventually.of_forall fun u => by rw [(hptR u).2, ← hReq u])
  have haeR : (fun u : ℝ => (fR u : ℂ)) =ᵐ[volume] fun u : ℝ => airyPWFun (∑' n : ℕ, (b n : ℂ) • cohnLL2 n) (u : ℂ) :=
    Eventually.of_forall fun u => by dsimp only; rw [hReq u, ← (hptR u).2]
  exact ⟨hPW, hnorm, hHasSum, fun z => ⟨hCeq z, (hCeq z).symm ▸ hptC z⟩,
    fun u => ⟨hReq u, (hReq u).symm ▸ (hptR u).1, by rw [hCeq u, (hptR u).2, ← hReq u]⟩, hLUC, hLUR,
    ⟨hmemR, (Lp.ext (hmemR.coeFn_toLp.trans (haeR.trans hmemC.coeFn_toLp.symm))).trans htoLpC⟩, fun z => by rw [hCeq z]; exact hbdPW z⟩

/-- `∑_{n ≥ 2} b_n²` (0-indexed tail starting at `n + 1 ↔ a_{n+2}`) from `(ceo:O11h.2)`. -/
noncomputable def cardinalTailSqSum (p h σ : ℝ) : ℝ :=
  ∑' n : ℕ, (σ * cohnC airyDerivFirstZero (n + 1) * ceVarphiP p (h * cohnE (n + 1))) ^ 2

/-- Soft infinite-cardinal coefficients `b_n` (`0 ↦ b₁`, `n + 1 ↦ b_{n+2}`) from `(ceo:O11h.2)`. -/
noncomputable def cardinalB (p h σ : ℝ) : ℕ → ℝ
  | 0 => -Real.sqrt (-airyDerivFirstZero - cardinalTailSqSum p h σ)
  | n + 1 => σ * cohnC airyDerivFirstZero (n + 1) * ceVarphiP p (h * cohnE (n + 1))

/-- Real cardinal source `H_h(u) = ∑' n, b_n L_n(u)` (`(ceo:O11h.2)`). -/
noncomputable def cardinalH (p h σ u : ℝ) : ℝ := ∑' n : ℕ, cardinalB p h σ n * cohnL n u

/-- Entire complex extension `H_h(z) = ∑' n, b_n L_n(z)` (`(ceo:O11h.2)`). -/
noncomputable def cardinalHC (p h σ : ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, (cardinalB p h σ n : ℂ) * cohnLC n z

/-- Real seed `f₁(u) = Ai(u)² / (u - a₁)` extended smoothly at `a₁` (`ce_o1_route.tex`). -/
noncomputable def ceF1 (u : ℝ) : ℝ := airyAi u * dslope airyAi (airyZero 1) u

/-- Complex entire seed `f₁(z) = -airyExtremal z` (`ce_o1_route.tex`). -/
noncomputable def ceF1C (z : ℂ) : ℂ := -airyExtremal z

/-- Coherent square `P_h = H_h²` (`(ceo:O11h.3)`). -/
noncomputable def cardinalP (p h σ u : ℝ) : ℝ := cardinalH p h σ u ^ 2

/-- Complex extension `P_h(z) = H_h(z)²` (`(ceo:O11h.3)`). -/
noncomputable def cardinalPC (p h σ : ℝ) (z : ℂ) : ℂ := cardinalHC p h σ z ^ 2

/-- Complement `Q_h = -f₁ + g₁' - P_h` (`(ceo:O11h.3)`). -/
noncomputable def cardinalQ (p h σ u : ℝ) : ℝ := -ceF1 u + ceG1Deriv airyDerivFirstZero u - cardinalP p h σ u

/-- Complex extension `Q_h(z) = -f₁(z) + H_*(z)² - P_h(z)` (`(ceo:O11h.3)`). -/
noncomputable def cardinalQC (p h σ : ℝ) (z : ℂ) : ℂ := -ceF1C z + cardinalHstarC airyDerivFirstZero z ^ 2 - cardinalPC p h σ z

private lemma cohnC_sq_hasSum_M : HasSum (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) (-airyDerivFirstZero) := by
  have h := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
  have hma : cohnM airyDerivFirstZero = 0 := by simp [cohnM, airyDerivFirstZero_spec.2.2]
  rw [hma, zero_pow two_ne_zero, zero_sub] at h; exact h.congr_fun fun n => by rw [cohnC, inv_pow]; ring_nf

private lemma cohnC_tail_sq_hasSum :
    HasSum (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2) (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) := by
  simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr cohnC_sq_hasSum_M

/-- **Lemma O.11h(1), well-definedness of `b₁`:** for `p > 0`, `h ≥ 0`, `σ ∈ (0, 1]`,
`c₀² ≤ M - ∑_{n ≥ 1} b_n²`, `0 < M - ∑_{n ≥ 1} b_n²`, and `∑_{n ≥ 0} b_n² = M`. -/
theorem cardinalB0_well_defined {p h σ : ℝ} (_hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    cohnC airyDerivFirstZero 0 ^ 2 ≤ -airyDerivFirstZero - cardinalTailSqSum p h σ ∧
      0 < -airyDerivFirstZero - cardinalTailSqSum p h σ ∧
      HasSum (fun n : ℕ => cardinalB p h σ n ^ 2) (-airyDerivFirstZero) ∧
      ∑' n : ℕ, cardinalB p h σ n ^ 2 = -airyDerivFirstZero := by
  have hterm_le : ∀ n : ℕ, (σ * cohnC airyDerivFirstZero (n + 1) * ceVarphiP p (h * cohnE (n + 1))) ^ 2 ≤
      cohnC airyDerivFirstZero (n + 1) ^ 2 := fun n => by
    have := (ceVarphiP_pos p (mul_nonneg hh (cohnE_nonneg (n + 1)))).le; have := ceVarphiP_le_one p (mul_nonneg hh (cohnE_nonneg (n + 1)))
    calc (σ * cohnC airyDerivFirstZero (n + 1) * ceVarphiP p (h * cohnE (n + 1))) ^ 2
        = (σ ^ 2 * ceVarphiP p (h * cohnE (n + 1)) ^ 2) * cohnC airyDerivFirstZero (n + 1) ^ 2 := by ring
      _ ≤ (1 ^ 2 * 1 ^ 2) * cohnC airyDerivFirstZero (n + 1) ^ 2 := by gcongr
      _ = cohnC airyDerivFirstZero (n + 1) ^ 2 := by ring
  have htail_sum := cohnC_tail_sq_hasSum.summable.of_nonneg_of_le (fun _ => sq_nonneg _) hterm_le
  have htail_le : cardinalTailSqSum p h σ ≤ -airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2 :=
    (htail_sum.tsum_le_tsum hterm_le cohnC_tail_sq_hasSum.summable).trans_eq cohnC_tail_sq_hasSum.tsum_eq
  have hc0_pos : 0 < cohnC airyDerivFirstZero 0 ^ 2 := by rw [cohnC, zero_add]; exact sq_pos_of_ne_zero (inv_ne_zero (by linarith [airyDerivFirstZero_spec.1]))
  have hdiff_le : cohnC airyDerivFirstZero 0 ^ 2 ≤ -airyDerivFirstZero - cardinalTailSqSum p h σ := by linarith
  have hdiff_pos : 0 < -airyDerivFirstZero - cardinalTailSqSum p h σ := lt_of_lt_of_le hc0_pos hdiff_le
  have hb0_sq : cardinalB p h σ 0 ^ 2 = -airyDerivFirstZero - cardinalTailSqSum p h σ := by simp only [cardinalB, neg_sq]; exact Real.sq_sqrt hdiff_pos.le
  have hfull : HasSum (fun n : ℕ => cardinalB p h σ n ^ 2) (-airyDerivFirstZero) := by
    rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one, show -airyDerivFirstZero - cardinalB p h σ 0 ^ 2 = cardinalTailSqSum p h σ by linarith]
    exact htail_sum.hasSum
  exact ⟨hdiff_le, hdiff_pos, hfull, hfull.tsum_eq⟩

private lemma cardinalH_pack {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    cardinalSeriesProps (cardinalB p h σ) (-airyDerivFirstZero) (cardinalHC p h σ) (cardinalH p h σ) :=
  cardinal_series_pack (a := airyDerivFirstZero) (cardinalB0_well_defined hp hh hσ0 hσ1).2.2.1 (fun _ => rfl) (fun _ => rfl) (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hφ0 := (ceVarphiP_pos p (mul_nonneg hh (cohnE_nonneg (m + 1)))).le; have hφ1 := ceVarphiP_le_one p (mul_nonneg hh (cohnE_nonneg (m + 1)))
    change |σ * cohnC airyDerivFirstZero (m + 1) * ceVarphiP p (h * cohnE (m + 1))| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg hσ0, abs_of_nonneg hφ0]
    calc σ * |cohnC airyDerivFirstZero (m + 1)| * ceVarphiP p (h * cohnE (m + 1)) ≤ 1 * |cohnC airyDerivFirstZero (m + 1)| * 1 := by gcongr
      _ = |cohnC airyDerivFirstZero (m + 1)| := by ring)

/-- **Lemma O.11h(1), pointwise `HasSum` on `ℂ` and `ℝ`:**
`H_h(z) = ∑_{n ≥ 1} b_n L_n(z)` and `H_h(u) = ∑_{n ≥ 1} b_n L_n(u)` everywhere. -/
theorem cardinalH_hasSum {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (∀ z : ℂ, HasSum (fun n : ℕ => (cardinalB p h σ n : ℂ) * cohnLC n z) (cardinalHC p h σ z)) ∧
    (∀ u : ℝ, HasSum (fun n : ℕ => cardinalB p h σ n * cohnL n u) (cardinalH p h σ u)) :=
  let hs := cardinalH_pack hp hh hσ0 hσ1; ⟨fun z => (hs.2.2.2.1 z).2, fun u => (hs.2.2.2.2.1 u).2.1⟩

/-- **Lemma O.11h(1), locally uniform convergence on `ℂ` and `ℝ`** of `H_h = ∑ b_n L_n`. -/
theorem cardinalH_tendstoLocallyUniformly {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N, (cardinalB p h σ n : ℂ) * cohnLC n z) (cardinalHC p h σ) atTop ∧
    TendstoLocallyUniformly (fun N u => ∑ n ∈ Finset.range N, cardinalB p h σ n * cohnL n u) (cardinalH p h σ) atTop :=
  let hs := cardinalH_pack hp hh hσ0 hσ1; ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1⟩

/-- **Lemma O.11h(1), `L²(ℝ)` convergence and `airyPW` membership** of `H_h`. -/
theorem cardinalH_memLp_and_L2_hasSum {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ hmem : MemLp (fun u : ℝ => (cardinalH p h σ u : ℂ)) 2 volume,
      HasSum (fun n : ℕ => (cardinalB p h σ n : ℂ) • cohnLL2 n) (hmem.toLp _) ∧ (hmem.toLp _) ∈ airyPW :=
  let hs := cardinalH_pack hp hh hσ0 hσ1; let ⟨hmem, htoLp⟩ := hs.2.2.2.2.2.2.2.1; ⟨hmem, htoLp.symm ▸ hs.2.2.1, htoLp.symm ▸ hs.1⟩

/-- Pointwise Airy-kernel growth bound `‖H_h(z)‖² ≤ 23 M (1 + ‖z‖) e(z)` (`ceo:O11h`). -/
theorem cardinalHC_norm_sq_le {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (z : ℂ) :
    ‖cardinalHC p h σ z‖ ^ 2 ≤ 23 * (-airyDerivFirstZero) * (1 + ‖z‖) * airyEnv z :=
  (cardinalH_pack hp hh hσ0 hσ1).2.2.2.2.2.2.2.2 z

private lemma airyClassG_sq_of_airyPW {F : AiryL2} (hF : F ∈ airyPW) : AiryClassG (fun z => airyPWFun F z ^ 2) := by
  have hdiff : Differentiable ℂ (fun z => airyPWFun F z ^ 2) := (differentiable_airyPWFun F).pow 2
  have hint : Integrable (fun u : ℝ => airyPWFun F (u : ℂ) ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)).mono'
      (hdiff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable (by
        filter_upwards [airyPWFun_ae hF] with u hu
        exact le_of_eq (by rw [norm_pow, ← hu]))
  exact ⟨hdiff, hint, ⟨23 * ‖F‖ ^ 2, 1, by positivity, fun z => by rw [norm_pow, pow_one]; exact (norm_airyPWFun_sq_le F z).trans_eq (by ring)⟩⟩

/-- **Lemma O.11h(1), `P_h, Q_h ∈ 𝒢` (`AiryClassG`):** `cardinalPC p h σ ∈ AiryClassG` and `cardinalQC p h σ ∈ AiryClassG`. -/
theorem cardinalPQ_mem_airyClassG {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    AiryClassG (cardinalPC p h σ) ∧ AiryClassG (cardinalQC p h σ) := by
  have hs := cardinalH_pack hp hh hσ0 hσ1
  have hP : AiryClassG (cardinalPC p h σ) := by
    rw [show cardinalPC p h σ = fun z => airyPWFun (∑' n : ℕ, (cardinalB p h σ n : ℂ) • cohnLL2 n) z ^ 2
      from funext fun z => by rw [cardinalPC, (hs.2.2.2.1 z).1]]
    exact airyClassG_sq_of_airyPW hs.1
  have hExt : AiryClassG airyExtremal := by
    obtain ⟨C, hC, hb⟩ := airyExtremal_bound; exact ⟨differentiable_airyExtremal, airyExtremal_integrable, ⟨C, 0, hC, fun z => by simpa using hb z⟩⟩
  have hHstar : AiryClassG (fun z : ℂ => cardinalHstarC airyDerivFirstZero z ^ 2) := by
    have hsG := cardinal_series_of_sq_hasSum cohnC_sq_hasSum_M
    rw [show (fun z : ℂ => cardinalHstarC airyDerivFirstZero z ^ 2) = fun z => airyPWFun (∑' n : ℕ, (cohnC airyDerivFirstZero n : ℂ) • cohnLL2 n) z ^ 2
      from funext fun z => by rw [← (cardinal_HstarC_hasSum airyDerivFirstZero_spec.2.2 z).tsum_eq, (hsG.2.2.2.1 z).tsum_eq]]
    exact airyClassG_sq_of_airyPW hsG.1
  have hsum : AiryClassG (fun z => airyExtremal z + cardinalHstarC airyDerivFirstZero z ^ 2) := by
    obtain ⟨C, N, hC, hb⟩ := hHstar.bound
    simpa [sub_neg_eq_add] using airyClassG_sub hExt ⟨hHstar.differentiable.neg, hHstar.integrable.neg, ⟨C, N, hC, fun z => by simpa using hb z⟩⟩
  exact ⟨hP, by rw [show cardinalQC p h σ = fun z => (airyExtremal z + cardinalHstarC airyDerivFirstZero z ^ 2) - cardinalPC p h σ z
    from funext fun z => by simp [cardinalQC, ceF1C]]; exact airyClassG_sub hsum hP⟩

/-- `∫_ℝ f₁ = 0` (`ce_o1_route.tex` Lemma O.11h(1)). -/
theorem ceF1_integral_eq_zero : Integrable ceF1 ∧ ∫ u : ℝ, ceF1 u = 0 := by
  have heq : ceF1 = fun u : ℝ => -(airyExtremal (u : ℂ)).re := funext fun u => by
    rw [airyExtremal_re, ceF1]
    by_cases hu : u = airyZero 1
    · subst hu; simp [airyAi_airyZero]
    · rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero]; ring
  refine ⟨heq ▸ airyExtremal_integrable.re.neg, ?_⟩
  rw [heq, integral_neg, ← RCLike.re_eq_complex_re, integral_re airyExtremal_integrable, RCLike.re_eq_complex_re, airyExtremal_integral]; simp

/-- `∫_ℝ g₁' = -a₁' = M` (`ce_o1_route.tex` Lemma O.11h(1)). -/
theorem ceG1Deriv_integral_eq_M : Integrable (ceG1Deriv airyDerivFirstZero) ∧ ∫ u : ℝ, ceG1Deriv airyDerivFirstZero u = -airyDerivFirstZero := by
  obtain ⟨hmem, -, -, hint⟩ := cardinal_Hstar_memLp_and_L2_hasSum airyDerivFirstZero_spec.2.2
  exact ⟨((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem).congr (Eventually.of_forall fun u => by simp [ceG1Deriv, cardinalHstar, sq_abs]), hint⟩

/-- **Lemma O.11h(1), exact masses:** `∫_ℝ P_h = M` and `∫_ℝ Q_h = 0`. -/
theorem cardinalPQ_integrals {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    Integrable (cardinalP p h σ) ∧ ∫ u : ℝ, cardinalP p h σ u = -airyDerivFirstZero ∧
    Integrable (cardinalQ p h σ) ∧ ∫ u : ℝ, cardinalQ p h σ u = 0 := by
  have hs := cardinalH_pack hp hh hσ0 hσ1; set F : AiryL2 := ∑' n : ℕ, (cardinalB p h σ n : ℂ) • cohnLL2 n
  have hae : (fun u : ℝ => cardinalP p h σ u) =ᵐ[volume] fun u : ℝ => ‖F u‖ ^ 2 := by
    filter_upwards [airyPWFun_ae hs.1] with u hu
    rw [hu, ← (hs.2.2.2.1 (u : ℂ)).1, (hs.2.2.2.2.1 u).2.2, Complex.norm_real, Real.norm_eq_abs, sq_abs, cardinalP]
  have hintP : Integrable (cardinalP p h σ) := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)).congr hae.symm
  have hIntP : ∫ u : ℝ, cardinalP p h σ u = -airyDerivFirstZero := by
    have hnorm_eq : (∫ u : ℝ, ‖F u‖ ^ 2) = ‖F‖ ^ 2 := by
      have hin := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
      have h1 : inner ℂ F F = ((‖F‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F]; simp
      have h2 : ∀ a : ℝ, inner ℂ (F a) (F a) = ((‖F a‖ ^ 2 : ℝ) : ℂ) := fun a => by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (F a)]; simp
      simp_rw [h2] at hin; rw [integral_complex_ofReal, h1] at hin; exact_mod_cast hin.symm
    rw [integral_congr_ae hae, hnorm_eq, hs.2.1]
  have hintF := ceF1_integral_eq_zero.1; have hintG := ceG1Deriv_integral_eq_M.1
  have hIntQ : ∫ u : ℝ, cardinalQ p h σ u = 0 := by
    have h1 : ∫ u : ℝ, cardinalQ p h σ u = (∫ u : ℝ, (-ceF1 + ceG1Deriv airyDerivFirstZero) u) - ∫ u : ℝ, cardinalP p h σ u :=
      integral_sub (hintF.neg.add hintG) hintP
    have h2 : ∫ u : ℝ, (-ceF1 + ceG1Deriv airyDerivFirstZero) u = (∫ u : ℝ, (-ceF1) u) + ∫ u : ℝ, ceG1Deriv airyDerivFirstZero u :=
      integral_add hintF.neg hintG
    have h3 : ∫ u : ℝ, (-ceF1) u = -∫ u : ℝ, ceF1 u := integral_neg ceF1
    rw [h1, h2, h3, ceF1_integral_eq_zero.2, ceG1Deriv_integral_eq_M.2, hIntP]; ring
  exact ⟨hintP, hIntP, (hintF.neg.add hintG).sub hintP, hIntQ⟩

/-! ### Part 3: Airy-zero counting law & Stieltjes asymptotic `(ceo:O11h.8)` -/

/-- Fractional cutoff deficiency `D_h = ∑_{n ≥ 2} c_n² [1 - φ_p(h E_n)²]` (0-indexed from `n + 1`). -/
noncomputable def cardinalDh (p h : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (n + 1)) ^ 2)

/-- Number of Airy zeros `-a_n ≤ X` (`n ≥ 1`, indexed as `n : ℕ` via `airyZero (n + 1)`). -/
noncomputable def airyZeroLeCount (X : ℝ) : ℕ := ({ n : ℕ | -airyZero (n + 1) ≤ X }).ncard

/-- Shifted counting function `Ñ(E) = #{n ≥ 2 : E_n ≤ E}` (`E_n = a_1 - a_n = cohnE (n + 1)`). -/
noncomputable def cohnELeCount (E : ℝ) : ℕ := ({ n : ℕ | cohnE (n + 1) ≤ E }).ncard

private lemma airyZeroRoot_cube_eq_rpow {n : ℕ} : airyZeroRoot n ^ 3 = (-airyZero n) ^ (3 / 2 : ℝ) := by
  rw [airyZeroRoot]; exact sqrt_cube_eq_rpow (neg_pos.mpr (airyZero_neg n))

private lemma airyZeroLeSet_sub_range {X : ℝ} :
    { n : ℕ | -airyZero (n + 1) ≤ X } ⊆ Finset.range (Nat.floor (2 / (3 * π) * X ^ (3 / 2 : ℝ)) + 1) := by
  let T : ℝ := 2 / (3 * π) * X ^ (3 / 2 : ℝ)
  have hTpi : 2 / 3 * X ^ (3 / 2 : ℝ) = T * π := by dsimp [T]; field_simp [Real.pi_ne_zero]
  intro n hn; simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range] at hn ⊢
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Nat.succ_pos _
  · have hph := (abs_le.mp (airyZero_phase_weak (by omega : 2 ≤ n + 1))).1
    have hle : airyZeroRoot (n + 1) ^ 3 ≤ X ^ (3 / 2 : ℝ) :=
      airyZeroRoot_cube_eq_rpow ▸ Real.rpow_le_rpow (neg_nonneg.mpr (airyZero_nonpos _)) hn (by norm_num)
    have hpi : 3 < π := Real.pi_gt_three
    have hmul : (n : ℝ) * π < T * π := by
      have hcast : (((n + 1 : ℕ) : ℝ) - 1 / 4) = (n : ℝ) + 3 / 4 := by push_cast; ring
      nlinarith
    by_contra hcon; push Not at hcon
    exact absurd (lt_of_lt_of_le (Nat.lt_floor_add_one T) (by exact_mod_cast hcon)) (lt_of_mul_lt_mul_right hmul Real.pi_pos.le).not_gt

private lemma airyZeroLeSet_finite (X : ℝ) : { n : ℕ | -airyZero (n + 1) ≤ X }.Finite :=
  (Finset.finite_toSet _).subset airyZeroLeSet_sub_range

/-- **Airy-zero counting law:** for all `X ≥ 0`, `|(airyZeroLeCount X : ℝ) - (2 / (3 * π)) * X ^ (3 / 2 : ℝ)| ≤ 1`. -/
theorem airyZero_counting_law {X : ℝ} (hX : 0 ≤ X) :
    |(airyZeroLeCount X : ℝ) - 2 / (3 * π) * X ^ (3 / 2 : ℝ)| ≤ 1 := by
  let T : ℝ := 2 / (3 * π) * X ^ (3 / 2 : ℝ); have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTpi : 2 / 3 * X ^ (3 / 2 : ℝ) = T * π := by dsimp [T]; field_simp [Real.pi_ne_zero]
  have hpi : 3 < π := Real.pi_gt_three
  by_cases hXa : X < -airyZero 1
  · have hempty : { n : ℕ | -airyZero (n + 1) ≤ X } = ∅ := by
      ext n; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]; linarith [airyZero_le_of_le le_rfl (by omega : 1 ≤ n + 1)]
    have hX235 : X < 2.35 := by linarith [airyZero_one.1]
    have hX32 : X ^ (3 / 2 : ℝ) < 3.65 := by
      have h1 : (X ^ (3 / 2 : ℝ)) ^ 2 = X ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
      have hcube : X ^ 3 < 3.65 ^ 2 := by have := pow_le_pow_left₀ hX hX235.le 3; norm_num at this ⊢; linarith
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (h1 ▸ hcube)
    unfold airyZeroLeCount; rw [hempty, Set.ncard_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hT0]
    exact (lt_of_mul_lt_mul_right (by nlinarith : T * π < 1 * π) Real.pi_pos.le).le
  · push Not at hXa
    have hsub2 : (Finset.range (Nat.floor T) : Set ℕ) ⊆ { n : ℕ | -airyZero (n + 1) ≤ X } := by
      intro n hn; simp only [Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq] at hn ⊢
      rcases eq_or_ne n 0 with rfl | hn0
      · exact hXa
      · have hn_le : (n : ℝ) + 1 ≤ T := (show (n + 1 : ℝ) ≤ (Nat.floor T : ℝ) by exact_mod_cast hn).trans (Nat.floor_le hT0)
        have hph := (abs_le.mp (airyZero_phase_weak (by omega : 2 ≤ n + 1))).2
        rw [show (((n + 1 : ℕ) : ℝ) - 1 / 4) = (n : ℝ) + 3 / 4 by push_cast; ring] at hph
        have hTle : ((n : ℝ) + 1) * π ≤ T * π := mul_le_mul_of_nonneg_right hn_le Real.pi_pos.le
        have hlt : (-airyZero (n + 1)) ^ (3 / 2 : ℝ) < X ^ (3 / 2 : ℝ) := by
          rw [← airyZeroRoot_cube_eq_rpow]
          have hmul : 2 / 3 * airyZeroRoot (n + 1) ^ 3 < 2 / 3 * X ^ (3 / 2 : ℝ) := by nlinarith
          linarith
        by_contra hcon; push Not at hcon
        exact absurd (Real.rpow_le_rpow hX hcon.le (by norm_num : (0 : ℝ) ≤ 3 / 2)) hlt.not_ge
    have hcard_ub : airyZeroLeCount X ≤ Nat.floor T + 1 :=
      (Set.ncard_le_ncard airyZeroLeSet_sub_range (Finset.finite_toSet _)).trans_eq ((Set.ncard_coe_finset (Finset.range (Nat.floor T + 1))).trans (Finset.card_range _))
    have hcard_lb : Nat.floor T ≤ airyZeroLeCount X :=
      ((Set.ncard_coe_finset (Finset.range (Nat.floor T))).trans (Finset.card_range _)).symm.trans_le (Set.ncard_le_ncard hsub2 (airyZeroLeSet_finite X))
    have hub' : (airyZeroLeCount X : ℝ) ≤ (Nat.floor T : ℝ) + 1 := by exact_mod_cast hcard_ub
    have hlb' : (Nat.floor T : ℝ) ≤ (airyZeroLeCount X : ℝ) := by exact_mod_cast hcard_lb
    rw [abs_le]; constructor <;> linarith [Nat.floor_le hT0, Nat.lt_floor_add_one T]

private lemma rpow_three_halves_shift_le {E c : ℝ} (hE : 0 ≤ E) (hc : 0 < c) :
    0 ≤ (E + c) ^ (3 / 2 : ℝ) - E ^ (3 / 2 : ℝ) ∧ (E + c) ^ (3 / 2 : ℝ) - E ^ (3 / 2 : ℝ) ≤ c * (2 * √E + √c) := by
  set u : ℝ := √(E + c); set v : ℝ := √E
  have hu3 : (E + c) ^ (3 / 2 : ℝ) = u ^ 3 := (sqrt_cube_eq_rpow (by linarith)).symm
  have hv3 : E ^ (3 / 2 : ℝ) = v ^ 3 := by dsimp [v]; rw [Real.sqrt_eq_rpow E, ← Real.rpow_natCast, ← Real.rpow_mul hE]; norm_num
  have h1 : (u - v) * (u + v) = c := by dsimp [u, v]; nlinarith [Real.sq_sqrt (by linarith : 0 ≤ E + c), Real.sq_sqrt hE]
  have huv_pos : 0 < u + v := by positivity
  have hfactor : u ^ 3 - v ^ 3 = c * ((u ^ 2 + u * v + v ^ 2) / (u + v)) := by
    field_simp [huv_pos.ne']; linear_combination (u ^ 2 + u * v + v ^ 2) * h1
  have hu_le : u ≤ v + √c := by dsimp [u, v]; exact Real.sqrt_le_iff.mpr ⟨by positivity, by
    rw [add_sq, Real.sq_sqrt hE, Real.sq_sqrt hc.le]; nlinarith [Real.sqrt_nonneg E, Real.sqrt_nonneg c]⟩
  have hle_sum : (u ^ 2 + u * v + v ^ 2) / (u + v) ≤ u + v :=
    (div_le_iff₀ huv_pos).mpr (by nlinarith [mul_nonneg (Real.sqrt_nonneg (E + c)) (Real.sqrt_nonneg E)])
  rw [hu3, hv3, hfactor]; exact ⟨by positivity, (mul_le_mul_of_nonneg_left hle_sum hc.le).trans (mul_le_mul_of_nonneg_left (by linarith) hc.le)⟩

/-- **Shifted Airy-zero counting law:** `Ñ(E) = (2 / (3 * π)) E^{3/2} + r(E)` with `|r(E)| ≤ C * (1 + √E)` for all `E ≥ 0`. -/
theorem cohnE_counting_law :
    ∃ C > 0, ∀ E : ℝ, 0 ≤ E → |(cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| ≤ C * (1 + √E) := by
  let c : ℝ := -airyZero 1; have hc : 0 < c := neg_pos.mpr (airyZero_neg 1)
  let C : ℝ := 2 + (2 / (3 * π)) * (c * max (2 : ℝ) (√c)); refine ⟨C, by positivity, fun E hE => ?_⟩
  have hXc : 0 ≤ E + c := by linarith
  have heq_set : (fun n : ℕ => n + 1) '' { n : ℕ | cohnE (n + 1) ≤ E } = { m : ℕ | -airyZero (m + 1) ≤ E + c } \ {0} := by
    ext m; simp only [mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq, cohnE, c]
    exact ⟨by rintro ⟨n, hn, rfl⟩; exact ⟨by linarith, Nat.succ_ne_zero n⟩,
      by rintro ⟨hm, hm0⟩; obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0; exact ⟨n, by linarith, rfl⟩⟩
  have hcard : ({ m : ℕ | -airyZero (m + 1) ≤ E + c } \ {0}).ncard + 1 = airyZeroLeCount (E + c) :=
    Set.ncard_sdiff_singleton_add_one (show (0 : ℕ) ∈ { m : ℕ | -airyZero (m + 1) ≤ E + c } by change -airyZero 1 ≤ E + c; linarith)
      (airyZeroLeSet_finite (E + c))
  have hcard_img : cohnELeCount E = ({ m : ℕ | -airyZero (m + 1) ≤ E + c } \ {0}).ncard := by
    unfold cohnELeCount; rw [← heq_set, Set.ncard_image_of_injective _ Nat.succ_injective]
  have hN_eq : (cohnELeCount E : ℝ) = (airyZeroLeCount (E + c) : ℝ) - 1 := by
    have : (cohnELeCount E : ℝ) + 1 = (airyZeroLeCount (E + c) : ℝ) := by exact_mod_cast hcard_img ▸ hcard
    linarith
  have h1 := airyZero_counting_law hXc; have h2 := rpow_three_halves_shift_le hE hc
  have hdiff_E : |2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| ≤ 2 / (3 * π) * (c * (2 * √E + √c)) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / (3 * π)), abs_of_nonneg h2.1]; exact mul_le_mul_of_nonneg_left h2.2 (by positivity)
  have h2sqrt : c * (2 * √E + √c) ≤ c * max (2 : ℝ) (√c) * (1 + √E) := calc
    c * (2 * √E + √c) ≤ c * (max (2 : ℝ) (√c) * √E + max (2 : ℝ) (√c)) := by
          gcongr
          · exact le_max_left (2 : ℝ) (√c)
          · exact le_max_right (2 : ℝ) (√c)
    _ = c * max (2 : ℝ) (√c) * (1 + √E) := by ring
  have h_tri : |(cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| ≤
      |(airyZeroLeCount (E + c) : ℝ) - 2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ)| + 1 + |2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| := by
    rw [show (cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ) = ((airyZeroLeCount (E + c) : ℝ) - 2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 1) +
      (2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) by rw [hN_eq]; ring]
    have t := abs_add_le ((airyZeroLeCount (E + c) : ℝ) - 2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 1) (2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ))
    have t2 := abs_sub ((airyZeroLeCount (E + c) : ℝ) - 2 / (3 * π) * (E + c) ^ (3 / 2 : ℝ)) (1 : ℝ); rw [abs_one] at t2; linarith
  calc |(cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| ≤ 2 + 2 / (3 * π) * (c * (2 * √E + √c)) := by linarith
    _ ≤ 2 * (1 + √E) + 2 / (3 * π) * (c * max (2 : ℝ) (√c) * (1 + √E)) := add_le_add (by linarith [Real.sqrt_nonneg E]) (mul_le_mul_of_nonneg_left h2sqrt (by positivity))
    _ = C * (1 + √E) := by dsimp [C]; ring

/-! #### Stieltjes summation-by-parts and error estimates for `D_h` (`(ceo:O11h.8)`) -/

private lemma cohnE_succ_pos (n : ℕ) : 0 < cohnE (n + 1) := by unfold cohnE; linarith [airyZero_lt_of_lt (n := 1) (m := n + 2) le_rfl (by omega)]
private lemma cohnE_succ_strictMono : StrictMono (fun n : ℕ => cohnE (n + 1)) := fun n m hnm => by
  unfold cohnE; linarith [airyZero_lt_of_lt (n := n + 2) (m := m + 2) (by omega) (by omega)]

private lemma cohnE_succ_tendsto_atTop : Tendsto (fun n : ℕ => cohnE (n + 1)) atTop atTop :=
  tendsto_atTop_mono (fun n => by
    have h := (airyZero_abs_bounds (n := n + 2) (by omega)).1
    unfold cohnE; change 2.5 * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ) + airyZero 1 ≤ airyZero 1 - airyZero (n + 2); linarith)
    ((Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2.5) ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)))).atTop_add tendsto_const_nhds)

private lemma cohnELeCount_eq_zero {E : ℝ} (hE : E < cohnE 1) : cohnELeCount E = 0 := by
  unfold cohnELeCount
  rw [show { n : ℕ | cohnE (n + 1) ≤ E } = ∅ from by
    ext n; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]; exact hE.trans_le (cohnE_succ_strictMono.monotone (Nat.zero_le n)), Set.ncard_empty]

private lemma cohnELeCount_eq_succ {k : ℕ} {E : ℝ} (h1 : cohnE (k + 1) ≤ E) (h2 : E < cohnE (k + 2)) : cohnELeCount E = k + 1 := by
  unfold cohnELeCount
  rw [show { n : ℕ | cohnE (n + 1) ≤ E } = (Finset.range (k + 1) : Set ℕ) from by
    ext n; simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range]
    exact ⟨fun hn => not_le.mp fun hcon => (h2.trans_le (cohnE_succ_strictMono.monotone (by omega : k + 1 ≤ n))).not_ge hn,
      fun hn => (cohnE_succ_strictMono.monotone (by omega : n ≤ k)).trans h1⟩, Set.ncard_coe_finset, Finset.card_range]

private noncomputable def stieltjesG (p h E : ℝ) : ℝ := (E + (airyDerivFirstZero - airyZero 1)) ^ (-2 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2)
private noncomputable def stieltjesG' (p h E : ℝ) : ℝ :=
  -2 * (E + (airyDerivFirstZero - airyZero 1)) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) +
    (E + (airyDerivFirstZero - airyZero 1)) ^ (-2 : ℝ) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3)

private lemma stieltjesG_nonneg {p h E : ℝ} (hh : 0 < h) (hE : 0 < E) : 0 ≤ stieltjesG p h E :=
  mul_nonneg (Real.rpow_nonneg (by linarith [sub_pos.mpr airyDerivFirstZero_spec.1]) _) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le)

private lemma stieltjesG_le_rpow {p h E : ℝ} (hh : 0 < h) (hE : 0 < E) :
    stieltjesG p h E ≤ (E + (airyDerivFirstZero - airyZero 1)) ^ (-2 : ℝ) :=
  mul_le_of_le_one_right (Real.rpow_nonneg (by linarith [sub_pos.mpr airyDerivFirstZero_spec.1]) _) (one_sub_ceVarphiP_sq_le_one p (mul_pos hh hE).le)

private lemma stieltjesG_hasDerivAt {p h E : ℝ} (hh : 0 < h) (hE : 0 < E) : HasDerivAt (stieltjesG p h) (stieltjesG' p h E) E := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have hr := (Real.hasDerivAt_rpow_const (p := (-2 : ℝ)) (Or.inl (by linarith : E + ell ≠ 0))).comp E ((hasDerivAt_id' E).add_const ell)
  refine (hr.mul (hasDerivAt_one_sub_ceVarphiP_sq_mul p hh hE)).congr_deriv ?_
  dsimp [stieltjesG']; rw [show (-2 : ℝ) - 1 = -3 by norm_num]; ring

private lemma stieltjesG'_continuousOn {p h : ℝ} (hh : 0 < h) : ContinuousOn (stieltjesG' p h) (Ioi 0) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  intro E (hE : 0 < E)
  have hden : (1 + (h * E) ^ p) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith [Real.rpow_pos_of_pos (mul_pos hh hE) p])
  exact ((continuousWithinAt_const.mul (continuousOn_rpow_add ell (-3) hell E hE)).mul
    (continuousWithinAt_const.sub ((continuousOn_ceVarphiP_mul p hh E hE).pow 2))).add
    ((continuousOn_rpow_add ell (-2) hell E hE).mul (((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hE.ne'))).div
      ((continuousAt_const.add ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inl (mul_pos hh hE).ne'))).pow 3) hden).continuousWithinAt))

private lemma stieltjesG_eq_term (p h : ℝ) (n : ℕ) :
    stieltjesG p h (cohnE (n + 1)) = cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (n + 1)) ^ 2) := by
  have hpos : 0 < cohnE (n + 1) + (airyDerivFirstZero - airyZero 1) := add_pos (cohnE_succ_pos n) (sub_pos.mpr airyDerivFirstZero_spec.1)
  have hdiff : cohnE (n + 1) + (airyDerivFirstZero - airyZero 1) = -(airyZero (n + 2) - airyDerivFirstZero) := by unfold cohnE; ring
  rw [stieltjesG, show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast, hdiff, neg_sq, cohnC, inv_pow]

private lemma integrableOn_rpow_ell {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun E : ℝ => (E + (airyDerivFirstZero - airyZero 1)) ^ a) (Ioi (0 : ℝ)) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have himg : (fun E : ℝ => E + ell) '' Ioi (0 : ℝ) = Ioi ell := by
    ext t; simp only [mem_image, mem_Ioi]; exact ⟨fun ⟨_, hE, h⟩ => h ▸ by linarith, fun ht => ⟨t - ell, by linarith, by ring⟩⟩
  simpa using (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi (f := fun E : ℝ => E + ell) (f' := fun _ => 1)
    (fun E _ => ((hasDerivAt_id' E).add_const ell).hasDerivWithinAt) (fun _ _ _ _ h => by linarith) (fun t : ℝ => t ^ a)).mp
    (himg ▸ integrableOn_Ioi_rpow_of_lt ha hell)

private lemma integrableOn_rpow_ell_mul_cutoff {p h q : ℝ} (hh : 0 < h) (hq : 1 < q) :
    IntegrableOn (fun E : ℝ => (E + (airyDerivFirstZero - airyZero 1)) ^ (-q) * (1 - ceVarphiP p (h * E) ^ 2)) (Ioi (0 : ℝ)) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have hmeas : AEStronglyMeasurable (fun E : ℝ => (E + ell) ^ (-q) * (1 - ceVarphiP p (h * E) ^ 2)) (volume.restrict (Ioi 0)) :=
    ((continuousOn_rpow_add ell (-q) hell).mul (continuousOn_const.sub ((continuousOn_ceVarphiP_mul p hh).pow 2))).aestronglyMeasurable measurableSet_Ioi
  refine (integrableOn_rpow_ell (by linarith : -q < -1)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le))]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (by linarith) _) (one_sub_ceVarphiP_sq_le_one p (mul_pos hh hE).le)

private lemma integrableOn_rpow_ell_deriv_cutoff {p h q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 1 / 2 ≤ q) :
    IntegrableOn (fun E : ℝ => (E + (airyDerivFirstZero - airyZero 1)) ^ (-q) *
        (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3)) (Ioi (0 : ℝ)) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have hmeas : AEStronglyMeasurable (fun E : ℝ => (E + ell) ^ (-q) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3))
      (volume.restrict (Ioi 0)) := by
    refine ((continuousOn_rpow_add ell (-q) hell).mul fun E (hE : 0 < E) => ?_).aestronglyMeasurable measurableSet_Ioi
    have hden : (1 + (h * E) ^ p) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith [Real.rpow_pos_of_pos (mul_pos hh hE) p])
    exact ((continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hE.ne'))).div
      ((continuousAt_const.add ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inl (mul_pos hh hE).ne'))).pow 3) hden).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]; refine IntegrableOn.union ?_ ?_
  · refine ((integrableOn_Ioc_rpow_of_lt (by linarith : -1 < p - 1) zero_le_one).const_mul (ell ^ (-q) * (2 * p * h ^ p))).mono'
      (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with E hE
    have hE0 : 0 < E := hE.1; have hM0 : (E + ell) ^ (-q) ≤ ell ^ (-q) := Real.rpow_le_rpow_of_nonpos hell (by linarith) (by linarith)
    have hden1 : 1 ≤ (1 + (h * E) ^ p) ^ 3 := one_le_pow₀ (by linarith [Real.rpow_pos_of_pos (mul_pos hh hE0) p])
    rw [Real.norm_of_nonneg (by positivity)]
    calc (E + ell) ^ (-q) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) ≤ ell ^ (-q) * (2 * p * h ^ p * E ^ (p - 1) / 1) := by gcongr
      _ = ell ^ (-q) * (2 * p * h ^ p) * E ^ (p - 1) := by ring
  · refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -2 * p - 3 / 2 < -1) zero_lt_one).const_mul (2 * p * h ^ (-2 * p))).mono'
      (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 1 < E)
    have hE0 : 0 < E := by linarith
    have h_ell_le : (E + ell) ^ (-q) ≤ E ^ (-(1 / 2 : ℝ)) :=
      (Real.rpow_le_rpow_of_nonpos hE0 (by linarith) (by linarith)).trans (Real.rpow_le_rpow_of_exponent_le hE.le (by linarith))
    have h_den_ge : h ^ (3 * p) * E ^ (3 * p) ≤ (1 + (h * E) ^ p) ^ 3 := by
      have h2 := pow_le_pow_left₀ (Real.rpow_nonneg (mul_pos hh hE0).le p) (by linarith : (h * E) ^ p ≤ 1 + (h * E) ^ p) 3
      have h3 : ((h * E) ^ p) ^ 3 = h ^ (3 * p) * E ^ (3 * p) := by
        rw [Real.mul_rpow hh.le hE0.le, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul hh.le, ← Real.rpow_mul hE0.le]
        simp only [Nat.cast_ofNat]; ring_nf
      rwa [← h3]
    rw [Real.norm_of_nonneg (by positivity)]
    calc (E + ell) ^ (-q) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) ≤
          E ^ (-(1 / 2 : ℝ)) * (2 * p * h ^ p * E ^ (p - 1) / (h ^ (3 * p) * E ^ (3 * p))) := by gcongr
      _ = 2 * p * h ^ (-2 * p) * E ^ (-2 * p - 3 / 2) := by
          rw [div_eq_mul_inv _ (h ^ (3 * p) * E ^ (3 * p)), mul_inv_rev, ← Real.rpow_neg hh.le, ← Real.rpow_neg hE0.le]
          have hhh : h ^ p * h ^ (-(3 * p)) = h ^ (-2 * p) := by rw [← Real.rpow_add hh]; ring_nf
          have hEE : E ^ (-(1 / 2 : ℝ)) * E ^ (p - 1) * E ^ (-(3 * p)) = E ^ (-2 * p - 3 / 2) := by rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; ring_nf
          linear_combination 2 * p * E ^ (-(1 / 2 : ℝ)) * E ^ (p - 1) * E ^ (-(3 * p)) * hhh + 2 * p * h ^ (-2 * p) * hEE

private lemma stieltjesG'_abs_le {p h E : ℝ} (hp : 0 < p) (hh : 0 < h) (hE : 0 < E) :
    |stieltjesG' p h E| ≤ 2 * (E + (airyDerivFirstZero - airyZero 1)) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) +
      (E + (airyDerivFirstZero - airyZero 1)) ^ (-2 : ℝ) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) := by
  have hell := sub_pos.mpr airyDerivFirstZero_spec.1
  have h1 : 0 ≤ 2 * (E + (airyDerivFirstZero - airyZero 1)) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) :=
    mul_nonneg (by positivity) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le)
  have h2 : 0 ≤ (E + (airyDerivFirstZero - airyZero 1)) ^ (-2 : ℝ) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) := by positivity
  unfold stieltjesG'; refine (abs_add_le _ _).trans (add_le_add ?_ (abs_of_nonneg h2).le)
  rw [show -2 * (E + (airyDerivFirstZero - airyZero 1)) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) =
    -(2 * (E + (airyDerivFirstZero - airyZero 1)) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2)) by ring, abs_neg, abs_of_nonneg h1]

private lemma integrableOn_rpow_ell_mul_stieltjesG' {p h r : ℝ} (hp : 0 < p) (hh : 0 < h) (hr : r ≤ 3 / 2) :
    IntegrableOn (fun E : ℝ => (E + (airyDerivFirstZero - airyZero 1)) ^ r * |stieltjesG' p h E|) (Ioi (0 : ℝ)) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have hmeas : AEStronglyMeasurable (fun E : ℝ => (E + ell) ^ r * |stieltjesG' p h E|) (volume.restrict (Ioi 0)) :=
    ((continuousOn_rpow_add ell r hell).mul (stieltjesG'_continuousOn hh).norm).aestronglyMeasurable measurableSet_Ioi
  refine (((integrableOn_rpow_ell_mul_cutoff (p := p) (q := 3 - r) hh (by linarith)).const_mul 2).add
    (integrableOn_rpow_ell_deriv_cutoff (p := p) (q := 2 - r) hp hh (by linarith))).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
  have hEell : 0 < E + ell := by linarith
  have ha1 : (E + ell) ^ r * (E + ell) ^ (-3 : ℝ) = (E + ell) ^ (-(3 - r)) := by rw [← Real.rpow_add hEell]; ring_nf
  have ha2 : (E + ell) ^ r * (E + ell) ^ (-2 : ℝ) = (E + ell) ^ (-(2 - r)) := by rw [← Real.rpow_add hEell]; ring_nf
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hEell.le r) (abs_nonneg _))]
  calc (E + ell) ^ r * |stieltjesG' p h E| ≤ (E + ell) ^ r * (2 * (E + ell) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) +
          (E + ell) ^ (-2 : ℝ) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3)) :=
        mul_le_mul_of_nonneg_left (stieltjesG'_abs_le hp hh hE) (Real.rpow_nonneg hEell.le r)
    _ = 2 * ((E + ell) ^ (-(3 - r)) * (1 - ceVarphiP p (h * E) ^ 2)) +
          (E + ell) ^ (-(2 - r)) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) := by
        linear_combination 2 * (1 - ceVarphiP p (h * E) ^ 2) * ha1 + (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) * ha2

private lemma cohnELeCount_le_ell_rpow :
    ∃ C_N > 0, ∀ E : ℝ, 0 ≤ E → (cohnELeCount E : ℝ) ≤ C_N * (E + (airyDerivFirstZero - airyZero 1)) ^ (3 / 2 : ℝ) := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  obtain ⟨Cr, hCr, hcount⟩ := cohnE_counting_law
  refine ⟨2 / (3 * π) + Cr * (2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ)))), by positivity, fun E hE => ?_⟩
  have hc := (abs_le.mp (hcount E hE)).2
  have hE_le : E ^ (3 / 2 : ℝ) ≤ (E + ell) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hE (by linarith) (by norm_num)
  have hsqrt : 1 + √E ≤ 2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ))) * (E + ell) ^ (3 / 2 : ℝ) := by
    have hpow_nn : 0 ≤ (E + ell) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    rcases le_or_gt (E + ell) 1 with hle | hgt
    · have hs1 : √E ≤ 1 := Real.sqrt_one ▸ Real.sqrt_le_sqrt (by linarith)
      have hpow : 1 ≤ ell ^ (-(3 / 2 : ℝ)) * (E + ell) ^ (3 / 2 : ℝ) := by
        have h1 := Real.rpow_le_rpow hell.le (by linarith : ell ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 3 / 2)
        calc (1 : ℝ) = ell ^ (-(3 / 2 : ℝ)) * ell ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hell]; norm_num
          _ ≤ ell ^ (-(3 / 2 : ℝ)) * (E + ell) ^ (3 / 2 : ℝ) := by gcongr
      calc 1 + √E ≤ 2 * (ell ^ (-(3 / 2 : ℝ)) * (E + ell) ^ (3 / 2 : ℝ)) := by linarith
        _ ≤ 2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ))) * (E + ell) ^ (3 / 2 : ℝ) := by rw [mul_assoc]; gcongr; exact le_max_right _ _
    · have h1 : 1 ≤ (E + ell) ^ (3 / 2 : ℝ) := Real.one_le_rpow hgt.le (by norm_num)
      have h2 : √E ≤ (E + ell) ^ (3 / 2 : ℝ) := (Real.sqrt_le_sqrt (by linarith : E ≤ E + ell)).trans
        (by rw [Real.sqrt_eq_rpow (E + ell)]; exact Real.rpow_le_rpow_of_exponent_le hgt.le (by norm_num))
      calc 1 + √E ≤ 2 * (1 * (E + ell) ^ (3 / 2 : ℝ)) := by linarith
        _ ≤ 2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ))) * (E + ell) ^ (3 / 2 : ℝ) := by rw [mul_assoc]; gcongr; exact le_max_left _ _
  calc (cohnELeCount E : ℝ) ≤ 2 / (3 * π) * E ^ (3 / 2 : ℝ) + Cr * (1 + √E) := by linarith
    _ ≤ 2 / (3 * π) * (E + ell) ^ (3 / 2 : ℝ) + Cr * (2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ))) * (E + ell) ^ (3 / 2 : ℝ)) := by gcongr
    _ = (2 / (3 * π) + Cr * (2 * max (1 : ℝ) (ell ^ (-(3 / 2 : ℝ))))) * (E + ell) ^ (3 / 2 : ℝ) := by ring

private lemma cardinalDh_eq_integral {p h : ℝ} (hp : 0 < p) (hh : 0 < h) :
    IntegrableOn (fun E : ℝ => (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) (Ioi (0 : ℝ)) ∧
      HasSum (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (n + 1)) ^ 2))
        (∫ E in Ioi (0 : ℝ), (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) := by
  let ell := airyDerivFirstZero - airyZero 1; obtain ⟨C_N, _, hN_le⟩ := cohnELeCount_le_ell_rpow
  have hfin : ∀ b : ℝ, { n : ℕ | cohnE (n + 1) ≤ b }.Finite := fun b => by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (cohnE_succ_tendsto_atTop (eventually_ge_atTop (b + 1)))
    exact (Finset.range N).finite_toSet.subset fun n hn => by
      rw [Set.mem_ofPred_eq] at hn; simp only [Finset.mem_coe, Finset.mem_range]; by_contra hcon
      have hNb := hN n (not_lt.mp hcon); rw [Set.mem_ofPred_eq] at hNb; linarith
  have hmono : Monotone (fun E : ℝ => (cohnELeCount E : ℝ)) := fun _ b hab => Nat.cast_le.mpr (Set.ncard_le_ncard (fun _ hn => hn.trans hab) (hfin b))
  have hint : IntegrableOn (fun E : ℝ => (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) (Ioi (0 : ℝ)) := by
    refine ((integrableOn_rpow_ell_mul_stieltjesG' (p := p) (r := 3 / 2) hp hh le_rfl).const_mul C_N).mono'
      (hmono.measurable.aestronglyMeasurable.mul ((stieltjesG'_continuousOn hh).neg.aestronglyMeasurable measurableSet_Ioi)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
    rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), norm_neg, Real.norm_eq_abs]
    calc (cohnELeCount E : ℝ) * |stieltjesG' p h E| ≤ (C_N * (E + ell) ^ (3 / 2 : ℝ)) * |stieltjesG' p h E| := mul_le_mul_of_nonneg_right (hN_le E hE.le) (abs_nonneg _)
      _ = C_N * ((E + ell) ^ (3 / 2 : ℝ) * |stieltjesG' p h E|) := by ring
  refine ⟨hint, ?_⟩
  let g : ℕ → ℝ := fun n => stieltjesG p h (cohnE (n + 1))
  have htel : ∀ K : ℕ, ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * (g k - g (k + 1)) = (∑ k ∈ Finset.range K, g k) - (K : ℝ) * g K :=
    fun K => by induction K with | zero => simp | succ K ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; push_cast; ring
  have h_part : ∀ K : ℕ, ∫ E in (0 : ℝ)..cohnE (K + 1), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) = (∑ k ∈ Finset.range K, g k) - (K : ℝ) * g K := fun K => by
    have hint_0 : IntervalIntegrable (fun E => (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) volume 0 (cohnE 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (cohnE_succ_pos 0).le).2 (hint.mono_set Ioc_subset_Ioi_self)
    have hint_k : ∀ k : ℕ, IntervalIntegrable (fun E => (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) volume (cohnE (k + 1)) (cohnE (k + 2)) := fun k =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (cohnE_succ_strictMono.monotone (Nat.le_succ k))).2
        (hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (cohnE_succ_pos k).le)))
    have hint_1K : IntervalIntegrable (fun E => (cohnELeCount E : ℝ) * (-stieltjesG' p h E)) volume (cohnE 1) (cohnE (K + 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (cohnE_succ_strictMono.monotone (Nat.zero_le K))).2
        (hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (cohnE_succ_pos 0).le)))
    have h_adj : ∑ k ∈ Finset.range K, ∫ E in cohnE (k + 1)..cohnE (k + 2), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) =
        ∫ E in cohnE 1..cohnE (K + 1), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) := by
      simpa [add_assoc] using intervalIntegral.sum_integral_adjacent_intervals (f := fun E => (cohnELeCount E : ℝ) * (-stieltjesG' p h E))
        (a := fun k => cohnE (k + 1)) (n := K) (fun k _ => hint_k k)
    have hfirst : ∫ E in (0 : ℝ)..cohnE 1, (cohnELeCount E : ℝ) * (-stieltjesG' p h E) = 0 := by
      rw [intervalIntegral.integral_of_le (cohnE_succ_pos 0).le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact setIntegral_eq_zero_of_forall_eq_zero fun E hE => by rw [cohnELeCount_eq_zero hE.2, Nat.cast_zero, zero_mul]
    have hstep : ∀ k : ℕ, ∫ E in cohnE (k + 1)..cohnE (k + 2), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) = ((k : ℝ) + 1) * (g k - g (k + 1)) := fun k => by
      have hle := cohnE_succ_strictMono.monotone (Nat.le_succ k)
      have hconst : ∫ E in cohnE (k + 1)..cohnE (k + 2), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) =
          ∫ E in cohnE (k + 1)..cohnE (k + 2), ((k : ℝ) + 1) * (-stieltjesG' p h E) := by
        rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        exact setIntegral_congr_fun measurableSet_Ioo fun E hE => by rw [cohnELeCount_eq_succ hE.1.le hE.2]; push_cast; rfl
      have hder : ∀ E ∈ uIcc (cohnE (k + 1)) (cohnE (k + 2)), HasDerivAt (fun t => -stieltjesG p h t) (-stieltjesG' p h E) E :=
        fun E hE => by rw [uIcc_of_le hle] at hE; exact (stieltjesG_hasDerivAt hh (lt_of_lt_of_le (cohnE_succ_pos k) hE.1)).neg
      have hint_g' : IntervalIntegrable (fun E => -stieltjesG' p h E) volume (cohnE (k + 1)) (cohnE (k + 2)) :=
        ((stieltjesG'_continuousOn hh).neg.mono fun E hE => by rw [uIcc_of_le hle] at hE; exact lt_of_lt_of_le (cohnE_succ_pos k) hE.1).intervalIntegrable
      rw [hconst, intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint_g']; dsimp [g]; ring
    rw [(intervalIntegral.integral_add_adjacent_intervals hint_0 hint_1K).symm, hfirst, zero_add, ← h_adj, Finset.sum_congr rfl fun k _ => hstep k, htel]
  have hI := (intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hint tendsto_id).comp cohnE_succ_tendsto_atTop
  have hg_nn : ∀ n : ℕ, 0 ≤ g n := fun n => stieltjesG_nonneg hh (cohnE_succ_pos n)
  have hK_rem : Tendsto (fun K : ℕ => (K : ℝ) * g K) atTop (𝓝 0) := by
    have hlim : Tendsto (fun K : ℕ => C_N * (cohnE (K + 1) + ell) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp (cohnE_succ_tendsto_atTop.atTop_add tendsto_const_nhds)).const_mul C_N
    refine squeeze_zero (fun K => mul_nonneg (Nat.cast_nonneg K) (hg_nn K)) (fun K => ?_) hlim
    have hEell : 0 < cohnE (K + 1) + ell := add_pos (cohnE_succ_pos K) (sub_pos.mpr airyDerivFirstZero_spec.1)
    have h1 : (K + 1 : ℕ) = cohnELeCount (cohnE (K + 1)) := (cohnELeCount_eq_succ le_rfl (cohnE_succ_strictMono (Nat.lt_succ_self K))).symm
    have hKE : (K : ℝ) ≤ C_N * (cohnE (K + 1) + ell) ^ (3 / 2 : ℝ) :=
      (show (K : ℝ) ≤ (cohnELeCount (cohnE (K + 1)) : ℝ) by rw [← h1]; exact_mod_cast Nat.le_succ K).trans (hN_le _ (cohnE_succ_pos K).le)
    calc (K : ℝ) * g K ≤ (C_N * (cohnE (K + 1) + ell) ^ (3 / 2 : ℝ)) * (cohnE (K + 1) + ell) ^ (-2 : ℝ) :=
          mul_le_mul hKE (stieltjesG_le_rpow hh (cohnE_succ_pos K)) (hg_nn K) (by positivity)
      _ = C_N * (cohnE (K + 1) + ell) ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hEell]; norm_num
  have hsum_lim : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, g k) atTop (𝓝 (∫ E in Ioi (0 : ℝ), (cohnELeCount E : ℝ) * (-stieltjesG' p h E))) := by
    have hadd := hI.add hK_rem; rw [add_zero] at hadd
    exact hadd.congr fun K => by dsimp only [Function.comp_apply, id_eq]; rw [h_part K]; ring
  have hg_summable : Summable g := cohnC_tail_sq_hasSum.summable.of_nonneg_of_le hg_nn fun n => by
    dsimp [g]; rw [stieltjesG_eq_term p h n]; exact mul_le_of_le_one_right (sq_nonneg _) (one_sub_ceVarphiP_sq_le_one p (mul_nonneg hh.le (cohnE_nonneg (n + 1))))
  have h1 := hg_summable.hasSum; rw [tendsto_nhds_unique h1.tendsto_sum_nat hsum_lim] at h1
  exact h1.congr_fun fun n => by dsimp only [g]; exact (stieltjesG_eq_term p h n).symm

private lemma ibp_main_stieltjes {p h : ℝ} (hp : 1 / 2 < p) (hh : 0 < h) :
    ∫ E in Ioi (0 : ℝ), (2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E) =
      (1 / π) * ∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E := by
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  let u : ℝ → ℝ := fun E => 2 / (3 * π) * E ^ (3 / 2 : ℝ); let u' : ℝ → ℝ := fun E => 1 / π * E ^ (1 / 2 : ℝ)
  let v : ℝ → ℝ := fun E => -stieltjesG p h E; let v' : ℝ → ℝ := fun E => -stieltjesG' p h E
  have hu : ∀ E ∈ Ioi (0 : ℝ), HasDerivAt u (u' E) E := fun E hE =>
    ((Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl hE.ne')).const_mul (2 / (3 * π))).congr_deriv (by norm_num [u']; ring)
  have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable (u * v') (volume.restrict (Ioi 0)) :=
      (((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).continuousOn).mul (stieltjesG'_continuousOn hh).neg).aestronglyMeasurable measurableSet_Ioi
    refine ((integrableOn_rpow_ell_mul_stieltjesG' (p := p) (r := 3 / 2) (by linarith) hh le_rfl).const_mul (2 / (3 * π))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
    have hEle := Real.rpow_le_rpow hE.le (by linarith : E ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    simp only [Pi.mul_apply, u, v', norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / (3 * π)), abs_of_nonneg (Real.rpow_nonneg hE.le _)]
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEle (abs_nonneg _)) (by positivity)
  have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable (u' * v) (volume.restrict (Ioi 0)) :=
      (((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).continuousOn).mul
        (((continuousOn_rpow_add ell (-2) hell).mul (continuousOn_const.sub ((continuousOn_ceVarphiP_mul p hh).pow 2))).neg)).aestronglyMeasurable measurableSet_Ioi
    refine ((integrableOn_rpow_ell (a := -(3 / 2 : ℝ)) (by norm_num)).const_mul (1 / π)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
    have hEell : 0 < E + ell := by linarith
    have hEle := Real.rpow_le_rpow hE.le (by linarith : E ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hst : |stieltjesG p h E| ≤ (E + ell) ^ (-2 : ℝ) := (abs_of_nonneg (stieltjesG_nonneg hh hE)).symm ▸ stieltjesG_le_rpow hh hE
    simp only [Pi.mul_apply, u', v, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / π), abs_of_nonneg (Real.rpow_nonneg hE.le _)]
    calc 1 / π * E ^ (1 / 2 : ℝ) * |stieltjesG p h E| ≤ 1 / π * (E + ell) ^ (1 / 2 : ℝ) * (E + ell) ^ (-2 : ℝ) := by gcongr
      _ = 1 / π * (E + ell) ^ (-(3 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hEell]; ring_nf
  have h_zero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_rpow_nhdsGT_zero (c := 2 / (3 * π) * ell ^ (-2 : ℝ)) (q := 3 / 2) (by norm_num))
    filter_upwards [self_mem_nhdsWithin] with E (hE : 0 < E)
    have hst : |stieltjesG p h E| ≤ ell ^ (-2 : ℝ) := (abs_of_nonneg (stieltjesG_nonneg hh hE)).symm ▸ (stieltjesG_le_rpow hh hE).trans (Real.rpow_le_rpow_of_nonpos hell (by linarith) (by norm_num))
    simp only [Pi.mul_apply, u, v, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / (3 * π)), abs_of_nonneg (Real.rpow_nonneg hE.le _)]
    calc 2 / (3 * π) * E ^ (3 / 2 : ℝ) * |stieltjesG p h E| ≤ 2 / (3 * π) * E ^ (3 / 2 : ℝ) * ell ^ (-2 : ℝ) := by gcongr
      _ = 2 / (3 * π) * ell ^ (-2 : ℝ) * E ^ (3 / 2 : ℝ) := by ring
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun E : ℝ => 2 / (3 * π) * E ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      conv_rhs => rw [show (0 : ℝ) = 2 / (3 * π) * 0 by ring]
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 / (3 * π))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with E (hE : 0 < E)
    have hst : |stieltjesG p h E| ≤ E ^ (-2 : ℝ) := (abs_of_nonneg (stieltjesG_nonneg hh hE)).symm ▸ (stieltjesG_le_rpow hh hE).trans (Real.rpow_le_rpow_of_nonpos hE (by linarith) (by norm_num))
    simp only [Pi.mul_apply, u, v, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / (3 * π)), abs_of_nonneg (Real.rpow_nonneg hE.le _)]
    calc 2 / (3 * π) * E ^ (3 / 2 : ℝ) * |stieltjesG p h E| ≤ 2 / (3 * π) * E ^ (3 / 2 : ℝ) * E ^ (-2 : ℝ) := by gcongr
      _ = 2 / (3 * π) * E ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hE]; norm_num
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu (fun _ hE => (stieltjesG_hasDerivAt hh hE).neg) huv' hu'v h_zero h_infty
  simp only [sub_zero, zero_sub] at hibp
  calc ∫ E in Ioi (0 : ℝ), u E * v' E = -∫ E in Ioi (0 : ℝ), u' E * v E := hibp
    _ = -∫ E in Ioi (0 : ℝ), -(1 / π) * (E ^ (1 / 2 : ℝ) * stieltjesG p h E) := by congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun E _ => by dsimp [u', v]; ring
    _ = (1 / π) * ∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E := by rw [integral_const_mul]; ring

private lemma ibp_rem_stieltjes {p h : ℝ} (hp : 0 < p) (hh : 0 < h) :
    let ell := airyDerivFirstZero - airyZero 1
    ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(3 / 2 : ℝ)) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) =
      (3 / 2 : ℝ) * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) := by
  intro ell; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  let u : ℝ → ℝ := fun E => (E + ell) ^ (-(3 / 2 : ℝ)); let u' : ℝ → ℝ := fun E => -(3 / 2 : ℝ) * (E + ell) ^ (-(5 / 2 : ℝ))
  let v : ℝ → ℝ := fun E => 1 - ceVarphiP p (h * E) ^ 2; let v' : ℝ → ℝ := fun E => 2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3
  have hu : ∀ E ∈ Ioi (0 : ℝ), HasDerivAt u (u' E) E := fun E (hE : 0 < E) => by
    have hc := (Real.hasDerivAt_rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (by linarith : E + ell ≠ 0))).comp E ((hasDerivAt_id' E).add_const ell)
    refine hc.congr_deriv ?_
    dsimp [u']; rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num]; ring
  have h_zero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_rpow_nhdsGT_zero (c := 2 * ell ^ (-(3 / 2 : ℝ)) * h ^ p) hp)
    filter_upwards [self_mem_nhdsWithin] with E (hE : 0 < E)
    have hEell : 0 < E + ell := by linarith
    simp only [Pi.mul_apply, u, v, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hEell.le _), abs_of_nonneg (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le)]
    calc (E + ell) ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) ≤ ell ^ (-(3 / 2 : ℝ)) * (2 * h ^ p * E ^ p) :=
          mul_le_mul (Real.rpow_le_rpow_of_nonpos hell (by linarith) (by norm_num)) (one_sub_ceVarphiP_sq_mul_le p hh.le hE.le) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le) (by positivity)
      _ = 2 * ell ^ (-(3 / 2 : ℝ)) * h ^ p * E ^ p := by ring
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun E : ℝ => (E + ell) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) from
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp (tendsto_id.atTop_add (tendsto_const_nhds (x := ell))))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with E (hE : 0 < E)
    have hEell : 0 < E + ell := by linarith
    simp only [Pi.mul_apply, u, v, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hEell.le _), abs_of_nonneg (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hEell.le _) (one_sub_ceVarphiP_sq_le_one p (mul_pos hh hE).le)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu (fun _ hE => hasDerivAt_one_sub_ceVarphiP_sq_mul p hh hE)
    (integrableOn_rpow_ell_deriv_cutoff (p := p) (q := 3 / 2) hp hh (by norm_num))
    (((integrableOn_rpow_ell_mul_cutoff (p := p) (q := 5 / 2) hh (by norm_num)).const_mul (-(3 / 2 : ℝ))).congr (ae_of_all _ fun E => by dsimp [u', v]; ring))
    h_zero h_infty
  simp only [sub_zero, zero_sub] at hibp
  calc ∫ E in Ioi (0 : ℝ), u E * v' E = -∫ E in Ioi (0 : ℝ), u' E * v E := hibp
    _ = -∫ E in Ioi (0 : ℝ), (-(3 / 2 : ℝ)) * ((E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)) := by
        congr 1; exact setIntegral_congr_fun measurableSet_Ioi fun E _ => by dsimp [u', v]; ring
    _ = (3 / 2 : ℝ) * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) := by rw [integral_const_mul]; ring

private lemma fracJ2_mul_sqrt_eq {p h : ℝ} (hp : 1 / 2 < p) (hh : 0 < h) :
    (1 / π) * ∫ E in Ioi (0 : ℝ), E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) = fracJ2 p * √h ∧
      IntegrableOn (fun E : ℝ => E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)) (Ioi (0 : ℝ)) := by
  have himg1 : (fun E : ℝ => h * E) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x; simp only [mem_image, mem_Ioi]; exact ⟨by rintro ⟨_, hE, rfl⟩; exact mul_pos hh hE, fun hx => ⟨x / h, div_pos hx hh, mul_div_cancel₀ x hh.ne'⟩⟩
  have himg2 : (fun x : ℝ => h⁻¹ * x) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext E; simp only [mem_image, mem_Ioi]; exact ⟨by rintro ⟨_, hx, rfl⟩; exact mul_pos (inv_pos.mpr hh) hx, fun hE => ⟨h * E, mul_pos hh hE, by field_simp [hh.ne']⟩⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi (f := fun E : ℝ => h * E) (f' := fun _ => h)
    (fun E _ => ((hasDerivAt_id' E).const_mul h).hasDerivWithinAt.congr_deriv (mul_one h))
    (fun _ _ _ _ heq => mul_left_cancel₀ hh.ne' heq) (fun x : ℝ => (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)))
  rw [himg1] at hcov
  have heq_int : ∫ x in Ioi (0 : ℝ), (1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)) =
      h ^ (-(1 / 2 : ℝ)) * ∫ E in Ioi (0 : ℝ), E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) := by
    rw [hcov, ← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Ioi fun E (hE : 0 < E) => ?_
    simp only [smul_eq_mul, abs_of_pos hh]
    have hcomb : h * h ^ (-(3 / 2 : ℝ)) = h ^ (-(1 / 2 : ℝ)) := by nth_rw 1 [← Real.rpow_one h]; rw [← Real.rpow_add hh]; norm_num
    rw [Real.mul_rpow hh.le hE.le, ← hcomb]; ring
  have h1 : h ^ (-(1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ) = 1 := by rw [← Real.rpow_add hh]; norm_num
  have hint0 : IntegrableOn (fun x : ℝ => h⁻¹ * (h⁻¹) ^ (-(3 / 2 : ℝ)) * ((1 - ceVarphiP p x ^ 2) * x ^ (-(3 / 2 : ℝ)))) (Ioi (0 : ℝ)) :=
    (fracJ2_integrable hp).const_mul (h⁻¹ * (h⁻¹) ^ (-(3 / 2 : ℝ)))
  have hint2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi (f := fun x : ℝ => h⁻¹ * x) (f' := fun _ => h⁻¹)
    (fun x _ => ((hasDerivAt_id' x).const_mul h⁻¹).hasDerivWithinAt.congr_deriv (mul_one h⁻¹))
    (fun _ _ _ _ heq => mul_left_cancel₀ (inv_ne_zero hh.ne') heq) (fun E : ℝ => E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2))).mpr
    (hint0.congr_fun (fun x (hx : 0 < x) => by
      simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hh), Real.mul_rpow (inv_pos.mpr hh).le hx.le, mul_inv_cancel_left₀ hh.ne']; ring) measurableSet_Ioi)
  rw [himg2] at hint2; refine ⟨?_, hint2⟩; unfold fracJ2; rw [heq_int, Real.sqrt_eq_rpow]
  calc (1 / π) * ∫ E in Ioi (0 : ℝ), E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)
      = (1 / π) * ((h ^ (-(1 / 2 : ℝ)) * h ^ (1 / 2 : ℝ)) * ∫ E in Ioi (0 : ℝ), E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)) := by rw [h1, one_mul]
    _ = _ := by ring

/-- **Lemma O.11h(2), Stieltjes asymptotic `(ceo:O11h.8)`:** for `p ∈ (1/2, 1)`, `|D_h - J_{2,p} √h| ≤ C h^p` for all `h > 0`. -/
theorem cardinalDh_asymptotic_pos {p : ℝ} (hp : p ∈ Ioo (1 / 2) 1) :
    ∃ C > 0, ∀ {h : ℝ}, 0 < h → |cardinalDh p h - fracJ2 p * √h| ≤ C * h ^ p := by
  have hp_lo := hp.1; have hp_hi := hp.2; have hp0 : 0 < p := by linarith
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  obtain ⟨Cr, hCr, hcount⟩ := cohnE_counting_law; let Cr' : ℝ := Cr * (ell ^ (-(1 / 2 : ℝ)) + 1)
  let I₁ : ℝ := 2 / π * (∫ E in Ioc 0 ell, E ^ (p - 3 / 2)) + 6 * ell / π * (∫ E in Ioi ell, E ^ (p - 5 / 2))
  let I₂ : ℝ := 7 * Cr' * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (p - 5 / 2)
  have hI_nn : 0 ≤ I₁ + I₂ := add_nonneg
    (add_nonneg (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioc fun E hE => Real.rpow_nonneg hE.1.le _))
      (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun E hE => Real.rpow_nonneg (hell.trans hE).le _)))
    (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun E (hE : 0 < E) => Real.rpow_nonneg (add_pos hE hell).le _))
  refine ⟨I₁ + I₂ + 1, by linarith, fun {h} hh => ?_⟩
  have hcount_ell : ∀ E : ℝ, 0 ≤ E → |(cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| ≤ Cr' * (E + ell) ^ (1 / 2 : ℝ) := fun E hE => by
    have h1 : 1 ≤ ell ^ (-(1 / 2 : ℝ)) * (E + ell) ^ (1 / 2 : ℝ) := by
      have := Real.rpow_le_rpow hell.le (by linarith : ell ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      calc (1 : ℝ) = ell ^ (-(1 / 2 : ℝ)) * ell ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hell]; norm_num
        _ ≤ ell ^ (-(1 / 2 : ℝ)) * (E + ell) ^ (1 / 2 : ℝ) := by gcongr
    have h2 : √E ≤ (E + ell) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (E + ell) ▸ Real.sqrt_le_sqrt (by linarith)
    exact (hcount E hE).trans (by calc Cr * (1 + √E) ≤ Cr * (ell ^ (-(1 / 2 : ℝ)) * (E + ell) ^ (1 / 2 : ℝ) + (E + ell) ^ (1 / 2 : ℝ)) := by gcongr
      _ = Cr' * (E + ell) ^ (1 / 2 : ℝ) := by dsimp [Cr']; ring)
  obtain ⟨hint_Dh, hhas_Dh⟩ := cardinalDh_eq_integral (p := p) hp0 hh
  have hint_lead : IntegrableOn (fun E : ℝ => (2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun E : ℝ => (2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) (volume.restrict (Ioi 0)) :=
      (((continuous_const.mul (Real.continuous_rpow_const (by norm_num))).continuousOn).mul (stieltjesG'_continuousOn hh).neg).aestronglyMeasurable measurableSet_Ioi
    refine ((integrableOn_rpow_ell_mul_stieltjesG' (p := p) (r := 3 / 2) hp0 hh le_rfl).const_mul (2 / (3 * π))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
    have hEle := Real.rpow_le_rpow hE.le (by linarith : E ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hE.le _)), Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEle (abs_nonneg _)) (by positivity)
  have hint_rem : IntegrableOn (fun E : ℝ => ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) (Ioi (0 : ℝ)) :=
    (hint_Dh.sub hint_lead).congr_fun (fun E _ => by simp [Pi.sub_apply]; ring) measurableSet_Ioi
  have hDh_split : cardinalDh p h = (1 / π) * (∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E) +
      (∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) := by
    calc cardinalDh p h = ∫ E in Ioi (0 : ℝ), (cohnELeCount E : ℝ) * (-stieltjesG' p h E) := by unfold cardinalDh; exact hhas_Dh.tsum_eq
      _ = (∫ E in Ioi (0 : ℝ), (2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) +
            (∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) := by
          rw [← integral_add hint_lead hint_rem]; exact setIntegral_congr_fun measurableSet_Ioi fun E _ => by ring
      _ = (1 / π) * (∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E) +
            (∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)) := by
          rw [ibp_main_stieltjes hp_lo hh]
  obtain ⟨hJ2_eq, hint_main2⟩ := fracJ2_mul_sqrt_eq hp_lo hh
  have hint_main1 : IntegrableOn (fun E : ℝ => E ^ (1 / 2 : ℝ) * stieltjesG p h E) (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun E : ℝ => E ^ (1 / 2 : ℝ) * stieltjesG p h E) (volume.restrict (Ioi 0)) :=
      ((Real.continuous_rpow_const (by norm_num)).continuousOn.mul
        ((continuousOn_rpow_add ell (-2) hell).mul (continuousOn_const.sub ((continuousOn_ceVarphiP_mul p hh).pow 2)))).aestronglyMeasurable measurableSet_Ioi
    refine (integrableOn_rpow_ell (a := -(3 / 2 : ℝ)) (by norm_num)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with E (hE : 0 < E)
    have hEell : 0 < E + ell := by linarith
    have hEle := Real.rpow_le_rpow hE.le (by linarith : E ≤ E + ell) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hE.le _) (stieltjesG_nonneg hh hE))]
    calc E ^ (1 / 2 : ℝ) * stieltjesG p h E ≤ (E + ell) ^ (1 / 2 : ℝ) * (E + ell) ^ (-2 : ℝ) :=
          mul_le_mul hEle (stieltjesG_le_rpow hh hE) (stieltjesG_nonneg hh hE) (Real.rpow_nonneg hEell.le _)
      _ = (E + ell) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hEell]; ring_nf
  have h_main_diff : |(1 / π) * (∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E) - fracJ2 p * √h| ≤ I₁ * h ^ p := by
    let gdiff : ℝ → ℝ := fun E => E ^ (1 / 2 : ℝ) * (E ^ (-2 : ℝ) - (E + ell) ^ (-2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)
    have h_diff_eq : ∀ E ∈ Ioi (0 : ℝ), E ^ (-(3 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) - E ^ (1 / 2 : ℝ) * stieltjesG p h E = gdiff E := fun E (hE : 0 < E) => by
      have hpow : E ^ (-(3 / 2 : ℝ)) = E ^ (1 / 2 : ℝ) * E ^ (-2 : ℝ) := by rw [← Real.rpow_add hE]; norm_num
      dsimp [stieltjesG, gdiff]; rw [hpow]; ring
    have hint_diff : IntegrableOn gdiff (Ioi (0 : ℝ)) := (hint_main2.sub hint_main1).congr_fun h_diff_eq measurableSet_Ioi
    have h_int_nn : 0 ≤ ∫ E in Ioi (0 : ℝ), gdiff E := setIntegral_nonneg measurableSet_Ioi fun E (hE : 0 < E) =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hE.le _) (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hE (by linarith) (by norm_num)))) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE).le)
    rw [← hJ2_eq, abs_sub_comm ((1 / π) * ∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E), ← mul_sub, ← integral_sub hint_main2 hint_main1,
      setIntegral_congr_fun measurableSet_Ioi h_diff_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π), abs_of_nonneg h_int_nn, ← Ioc_union_Ioi_eq_Ioi hell.le]
    rw [← Ioc_union_Ioi_eq_Ioi hell.le] at hint_diff
    rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hint_diff.mono_set subset_union_left) (hint_diff.mono_set subset_union_right)]
    have hb1 : ∫ E in Ioc 0 ell, gdiff E ≤ 2 * h ^ p * ∫ E in Ioc 0 ell, E ^ (p - 3 / 2) := by
      rw [← integral_const_mul]; refine setIntegral_mono_on (hint_diff.mono_set subset_union_left)
        ((integrableOn_Ioc_rpow_of_lt (by linarith : -1 < p - 3 / 2) hell.le).const_mul _) measurableSet_Ioc fun E hE => ?_
      have hE0 : 0 < E := hE.1; have hsub : E ^ (-2 : ℝ) - (E + ell) ^ (-2 : ℝ) ≤ E ^ (-2 : ℝ) := by linarith [Real.rpow_nonneg (by linarith : 0 ≤ E + ell) (-2 : ℝ)]
      calc gdiff E ≤ E ^ (1 / 2 : ℝ) * E ^ (-2 : ℝ) * (2 * h ^ p * E ^ p) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsub (Real.rpow_nonneg hE0.le _)) (one_sub_ceVarphiP_sq_mul_le p hh.le hE0.le) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE0).le) (by positivity)
        _ = 2 * h ^ p * E ^ (p - 3 / 2) := by
            have ha : E ^ (1 / 2 : ℝ) * E ^ (-2 : ℝ) * E ^ p = E ^ (p - 3 / 2) := by rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; ring_nf
            linear_combination 2 * h ^ p * ha
    have hb2 : ∫ E in Ioi ell, gdiff E ≤ 6 * ell * h ^ p * ∫ E in Ioi ell, E ^ (p - 5 / 2) := by
      rw [← integral_const_mul]; refine setIntegral_mono_on (hint_diff.mono_set subset_union_right)
        ((integrableOn_Ioi_rpow_of_lt (by linarith : p - 5 / 2 < -1) hell).const_mul _) measurableSet_Ioi fun E (hE : ell < E) => ?_
      have hE0 : 0 < E := hell.trans hE; have hEell : 0 < E + ell := by linarith
      have hsub : E ^ (-2 : ℝ) - (E + ell) ^ (-2 : ℝ) ≤ 3 * ell * E ^ (-3 : ℝ) := by
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hE0.le, Real.rpow_neg hEell.le, Real.rpow_natCast, Real.rpow_natCast,
          show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg hE0.le, Real.rpow_natCast, inv_sub_inv (pow_ne_zero 2 hE0.ne') (pow_ne_zero 2 hEell.ne')]
        calc ((E + ell) ^ 2 - E ^ 2) / (E ^ 2 * (E + ell) ^ 2) ≤ (3 * ell * E) / E ^ 4 :=
          div_le_div₀ (by positivity) (by nlinarith [hE.le]) (by positivity) (by rw [show E ^ 4 = E ^ 2 * E ^ 2 by ring]; gcongr; linarith)
          _ = 3 * ell * (E ^ 3)⁻¹ := by field_simp [hE0.ne']
      calc gdiff E ≤ E ^ (1 / 2 : ℝ) * (3 * ell * E ^ (-3 : ℝ)) * (2 * h ^ p * E ^ p) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsub (Real.rpow_nonneg hE0.le _)) (one_sub_ceVarphiP_sq_mul_le p hh.le hE0.le) (one_sub_ceVarphiP_sq_nonneg p (mul_pos hh hE0).le) (by positivity)
        _ = 6 * ell * h ^ p * E ^ (p - 5 / 2) := by
            have ha : E ^ (1 / 2 : ℝ) * E ^ (-3 : ℝ) * E ^ p = E ^ (p - 5 / 2) := by rw [← Real.rpow_add hE0, ← Real.rpow_add hE0]; ring_nf
            linear_combination 6 * ell * h ^ p * ha
    calc 1 / π * ((∫ E in Ioc 0 ell, gdiff E) + (∫ E in Ioi ell, gdiff E)) ≤
          1 / π * (2 * h ^ p * (∫ E in Ioc 0 ell, E ^ (p - 3 / 2)) + 6 * ell * h ^ p * (∫ E in Ioi ell, E ^ (p - 5 / 2))) := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)
      _ = I₁ * h ^ p := by dsimp [I₁]; ring
  have hint_err_dom1 := (integrableOn_rpow_ell_mul_cutoff (p := p) (q := 5 / 2) hh (by norm_num)).const_mul (2 * Cr')
  have hint_err_dom2 := (integrableOn_rpow_ell_deriv_cutoff (p := p) (q := 3 / 2) hp0 hh (by norm_num)).const_mul Cr'
  have h_rem_bd : |∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)| ≤ I₂ * h ^ p := by
    have h_mono1 : ∫ E in Ioi (0 : ℝ), ‖((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)‖ ≤
        ∫ E in Ioi (0 : ℝ), (2 * Cr' * ((E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)) +
          Cr' * ((E + ell) ^ (-(3 / 2 : ℝ)) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3))) := by
      refine setIntegral_mono_on hint_rem.norm (hint_err_dom1.add hint_err_dom2) measurableSet_Ioi fun E (hE : 0 < E) => ?_
      have hEell : 0 < E + ell := by linarith
      have hr1 : (E + ell) ^ (1 / 2 : ℝ) * (E + ell) ^ (-3 : ℝ) = (E + ell) ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hEell]; ring_nf
      have hr2 : (E + ell) ^ (1 / 2 : ℝ) * (E + ell) ^ (-2 : ℝ) = (E + ell) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hEell]; ring_nf
      rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |(cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)| * |stieltjesG' p h E|
          ≤ (Cr' * (E + ell) ^ (1 / 2 : ℝ)) * (2 * (E + ell) ^ (-3 : ℝ) * (1 - ceVarphiP p (h * E) ^ 2) +
              (E + ell) ^ (-2 : ℝ) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3)) :=
            mul_le_mul (hcount_ell E hE.le) (stieltjesG'_abs_le hp0 hh hE) (abs_nonneg _) (by positivity)
        _ = _ := by linear_combination 2 * Cr' * (1 - ceVarphiP p (h * E) ^ 2) * hr1 + Cr' * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3) * hr2
    have h_eval : ∫ E in Ioi (0 : ℝ), (2 * Cr' * ((E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2)) +
          Cr' * ((E + ell) ^ (-(3 / 2 : ℝ)) * (2 * p * h ^ p * E ^ (p - 1) / (1 + (h * E) ^ p) ^ 3))) =
        (7 / 2 : ℝ) * Cr' * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) := by
      rw [integral_add hint_err_dom1 hint_err_dom2, integral_const_mul, integral_const_mul, ibp_rem_stieltjes hp0 hh]; ring
    have h_pow_bd : ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) ≤ 2 * h ^ p * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (p - 5 / 2) := by
      rw [← integral_const_mul]; refine setIntegral_mono_on (integrableOn_rpow_ell_mul_cutoff (p := p) (q := 5 / 2) hh (by norm_num))
        ((integrableOn_rpow_ell (by linarith : p - 5 / 2 < -1)).const_mul _) measurableSet_Ioi fun E (hE : 0 < E) => ?_
      have hEell : 0 < E + ell := by linarith
      have hEp : E ^ p ≤ (E + ell) ^ p := Real.rpow_le_rpow hE.le (by linarith) hp0.le
      calc (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) ≤ (E + ell) ^ (-(5 / 2 : ℝ)) * (2 * h ^ p * (E + ell) ^ p) := by
            gcongr; exact (one_sub_ceVarphiP_sq_mul_le p hh.le hE.le).trans (mul_le_mul_of_nonneg_left hEp (by positivity))
        _ = 2 * h ^ p * (E + ell) ^ (p - 5 / 2) := by rw [mul_left_comm, ← Real.rpow_add hEell]; ring_nf
    calc |∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E)|
        ≤ (7 / 2 : ℝ) * Cr' * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (-(5 / 2 : ℝ)) * (1 - ceVarphiP p (h * E) ^ 2) :=
          (norm_integral_le_integral_norm _).trans (h_mono1.trans_eq h_eval)
      _ ≤ (7 / 2 : ℝ) * Cr' * (2 * h ^ p * ∫ E in Ioi (0 : ℝ), (E + ell) ^ (p - 5 / 2)) := mul_le_mul_of_nonneg_left h_pow_bd (by positivity)
      _ = I₂ * h ^ p := by dsimp [I₂]; ring
  calc |cardinalDh p h - fracJ2 p * √h|
      = |((1 / π) * (∫ E in Ioi (0 : ℝ), E ^ (1 / 2 : ℝ) * stieltjesG p h E) - fracJ2 p * √h) +
          (∫ E in Ioi (0 : ℝ), ((cohnELeCount E : ℝ) - 2 / (3 * π) * E ^ (3 / 2 : ℝ)) * (-stieltjesG' p h E))| := by rw [hDh_split, add_sub_right_comm]
    _ ≤ I₁ * h ^ p + I₂ * h ^ p := (abs_add_le _ _).trans (add_le_add h_main_diff h_rem_bd)
    _ ≤ (I₁ + I₂ + 1) * h ^ p := by linarith [Real.rpow_nonneg hh.le p]

/-- **Lemma O.11h(2) (`(ceo:O11h.8)`):** for `p ∈ (1/2, 1)`, `|D_h - J_{2,p} √h| ≤ C h^p` on `h ∈ (0, 1]`. -/
theorem cardinalDh_asymptotic {p : ℝ} (hp : p ∈ Ioo (1 / 2) 1) :
    ∃ C > 0, ∀ h ∈ Ioc (0 : ℝ) 1, |cardinalDh p h - fracJ2 p * √h| ≤ C * h ^ p :=
  let ⟨C, hC, hbd⟩ := cardinalDh_asymptotic_pos hp; ⟨C, hC, fun _ hh => hbd hh.1⟩

/-- Little-`o` form of `(ceo:O11h.8)`: `D_h = J_{2,p} √h + o(√h)` as `h → 0⁺`. -/
theorem cardinalDh_littleO {p : ℝ} (hp : p ∈ Ioo (1 / 2) 1) :
    Tendsto (fun h : ℝ => (cardinalDh p h - fracJ2 p * √h) / √h) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hbd⟩ := cardinalDh_asymptotic_pos hp
  refine squeeze_zero_norm' ?_ (tendsto_const_mul_rpow_nhdsGT_zero (c := C) (by linarith [hp.1] : 0 < p - 1 / 2))
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hh), div_le_iff₀ (Real.sqrt_pos.mpr hh)]
  calc |cardinalDh p h - fracJ2 p * √h| ≤ C * h ^ p := hbd hh
    _ = C * h ^ (p - 1 / 2) * √h := by rw [Real.sqrt_eq_rpow h, mul_assoc, ← Real.rpow_add hh]; ring_nf

/-! ### Part 4: Untuned decomposition and `η̂_h` bound (`(ceo:O11h.9)`) -/

/-- The untuned sum `H_h^{(0)}(u) = ∑_{n ≥ 1} c_n φ_p(h E_n) L_n(u)` (`(ceo:O11h.9)`). -/
noncomputable def cardinalH_untuned (p h u : ℝ) : ℝ := ∑' n : ℕ, (cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n)) * cohnL n u

/-- Complex entire extension `H_h^{(0)}(z)` (`(ceo:O11h.9)`). -/
noncomputable def cardinalHC_untuned (p h : ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, ((cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n) : ℝ) : ℂ) * cohnLC n z

/-- First-coefficient discrepancy `η̂_h := σ c₁ - b₁` (`(ceo:O11h.9)`). -/
noncomputable def cardinalEtaHat (p h σ : ℝ) : ℝ := σ * cohnC airyDerivFirstZero 0 - cardinalB p h σ 0

/-- Convergence of the untuned sum `H_h^{(0)}` (pointwise, locally uniformly on `ℂ` and `ℝ`, and in `L²`). -/
theorem cardinalH_untuned_converges {p h : ℝ} (hh : 0 ≤ h) :
    (∀ z : ℂ, HasSum (fun n : ℕ => ((cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n) : ℝ) : ℂ) * cohnLC n z) (cardinalHC_untuned p h z)) ∧
    (∀ u : ℝ, HasSum (fun n : ℕ => (cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n)) * cohnL n u) (cardinalH_untuned p h u)) ∧
    TendstoLocallyUniformly (fun N z => ∑ n ∈ Finset.range N, ((cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n) : ℝ) : ℂ) * cohnLC n z)
      (cardinalHC_untuned p h) atTop ∧
    TendstoLocallyUniformly (fun N u => ∑ n ∈ Finset.range N, (cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n)) * cohnL n u)
      (cardinalH_untuned p h) atTop ∧
    (∃ hmem : MemLp (fun u : ℝ => (cardinalH_untuned p h u : ℂ)) 2 volume,
      HasSum (fun n : ℕ => ((cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n) : ℝ) : ℂ) • cohnLL2 n) (hmem.toLp _) ∧ (hmem.toLp _) ∈ airyPW) := by
  have hs_sq : Summable (fun n : ℕ => (cohnC airyDerivFirstZero n * ceVarphiP p (h * cohnE n)) ^ 2) :=
    cohnC_sq_hasSum_M.summable.of_nonneg_of_le (fun _ => sq_nonneg _) fun n => by
      have := (ceVarphiP_pos p (mul_nonneg hh (cohnE_nonneg n))).le; have := ceVarphiP_le_one p (mul_nonneg hh (cohnE_nonneg n))
      rw [mul_pow]; exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)
  have hpk := cardinal_series_pack (a := airyDerivFirstZero) hs_sq.hasSum (fun _ => rfl) (fun _ => rfl)
    (Eventually.of_forall fun n => by
      rw [abs_mul, abs_of_nonneg (ceVarphiP_pos p (mul_nonneg hh (cohnE_nonneg n))).le]
      exact mul_le_of_le_one_right (abs_nonneg _) (ceVarphiP_le_one p (mul_nonneg hh (cohnE_nonneg n))))
  obtain ⟨hmem, htoLp⟩ := hpk.2.2.2.2.2.2.2.1
  exact ⟨fun z => (hpk.2.2.2.1 z).2, fun u => (hpk.2.2.2.2.1 u).2.1, hpk.2.2.2.2.2.1, hpk.2.2.2.2.2.2.1, ⟨hmem, htoLp.symm ▸ hpk.2.2.1, htoLp.symm ▸ hpk.1⟩⟩

/-- **Lemma O.11h(3), untuned decomposition (`(ceo:O11h.9)`):** `H_h(u) = σ H_h^{(0)}(u) - η̂_h L_1(u)` (and on `ℂ`). -/
theorem cardinalH_eq_untuned_sub {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (∀ u : ℝ, cardinalH p h σ u = σ * cardinalH_untuned p h u - cardinalEtaHat p h σ * cohnL 0 u) ∧
    (∀ z : ℂ, cardinalHC p h σ z = (σ : ℂ) * cardinalHC_untuned p h z - (cardinalEtaHat p h σ : ℂ) * cohnLC 0 z) := by
  have hφ0 : ceVarphiP p (h * cohnE 0) = 1 := by rw [show cohnE 0 = 0 by unfold cohnE; ring, mul_zero]; unfold ceVarphiP; rw [Real.zero_rpow hp.ne']; norm_num
  have hH_sum := cardinalH_hasSum hp hh hσ0 hσ1; have hU_conv := cardinalH_untuned_converges (p := p) hh
  constructor
  · intro u
    have hsH := (hasSum_nat_add_iff' 1).mpr (hH_sum.2 u); have hsU := (hasSum_nat_add_iff' 1).mpr ((hU_conv.2.1 u).mul_left σ)
    simp only [Finset.sum_range_one] at hsH hsU
    have heq_sum := (hsH.congr_fun fun n => by simp only [cardinalB]; ring).unique hsU; rw [hφ0, mul_one] at heq_sum; unfold cardinalEtaHat; linarith
  · intro z
    have hsH := (hasSum_nat_add_iff' 1).mpr (hH_sum.1 z); have hsU := (hasSum_nat_add_iff' 1).mpr ((hU_conv.1 z).mul_left (σ : ℂ))
    simp only [Finset.sum_range_one] at hsH hsU
    have heq_sum := (hsH.congr_fun fun n => by simp only [cardinalB]; push_cast; ring).unique hsU; rw [hφ0, mul_one] at heq_sum; unfold cardinalEtaHat; push_cast; linear_combination heq_sum

/-- **Lemma O.11h(3), exact identity and `η̂_h` bound (`(ceo:O11h.9)`):**
`η̂_h = σ c₁ - b₁ = √(M - σ² A_h) - σ / ℓ` satisfies `0 ≤ η̂_h ≤ ℓ (D_h + (1 - σ²) M)`. -/
theorem cardinalEtaHat_bounds {p h σ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    let ell := airyDerivFirstZero - airyZero 1; let M := -airyDerivFirstZero
    cardinalEtaHat p h σ = Real.sqrt (M - cardinalTailSqSum p h σ) - σ / ell ∧
      0 ≤ cardinalEtaHat p h σ ∧ cardinalEtaHat p h σ ≤ ell * (cardinalDh p h + (1 - σ ^ 2) * M) := by
  intro ell M; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  have hc0_eq : cohnC airyDerivFirstZero 0 = -ell⁻¹ := by rw [cohnC, zero_add]; dsimp [ell]; rw [← neg_sub, inv_neg]
  have hη_eq : cardinalEtaHat p h σ = Real.sqrt (M - cardinalTailSqSum p h σ) - σ / ell := by unfold cardinalEtaHat cardinalB; rw [hc0_eq, div_eq_mul_inv]; ring
  have hB0 := cardinalB0_well_defined hp hh hσ0 hσ1
  let A_h : ℝ := ∑' n : ℕ, cohnC airyDerivFirstZero (n + 1) ^ 2 * ceVarphiP p (h * cohnE (n + 1)) ^ 2
  have hA_sum : Summable (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2 * ceVarphiP p (h * cohnE (n + 1)) ^ 2) :=
    cohnC_tail_sq_hasSum.summable.of_nonneg_of_le (fun _ => by positivity) fun n => by
      have := (ceVarphiP_pos p (mul_nonneg hh (cohnE_nonneg (n + 1)))).le; have := ceVarphiP_le_one p (mul_nonneg hh (cohnE_nonneg (n + 1)))
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)
  have htail_eq : cardinalTailSqSum p h σ = σ ^ 2 * A_h := by unfold cardinalTailSqSum; rw [← hA_sum.tsum_mul_left]; exact tsum_congr fun n => by ring
  have hDh_sum : Summable (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (n + 1)) ^ 2)) :=
    cohnC_tail_sq_hasSum.summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (one_sub_ceVarphiP_sq_nonneg p (mul_nonneg hh (cohnE_nonneg (n + 1)))))
      (fun n => mul_le_of_le_one_right (sq_nonneg _) (one_sub_ceVarphiP_sq_le_one p (mul_nonneg hh (cohnE_nonneg (n + 1)))))
  have hDh_eq : cardinalDh p h = (M - cohnC airyDerivFirstZero 0 ^ 2) - A_h := by
    have hadd := hA_sum.tsum_add hDh_sum
    rw [show (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2 * ceVarphiP p (h * cohnE (n + 1)) ^ 2 +
        cohnC airyDerivFirstZero (n + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (n + 1)) ^ 2)) = fun n => cohnC airyDerivFirstZero (n + 1) ^ 2 from funext fun _ => by ring,
      cohnC_tail_sq_hasSum.tsum_eq] at hadd
    change M - cohnC airyDerivFirstZero 0 ^ 2 = A_h + cardinalDh p h at hadd; linarith
  have hDh_nn : 0 ≤ cardinalDh p h := tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (one_sub_ceVarphiP_sq_nonneg p (mul_nonneg hh (cohnE_nonneg (n + 1))))
  have hc0_sq : cohnC airyDerivFirstZero 0 ^ 2 = (ell⁻¹) ^ 2 := by rw [hc0_eq, neg_sq]
  have h_lb_sq : (σ / ell) ^ 2 ≤ M - cardinalTailSqSum p h σ := by
    rw [htail_eq, div_pow, div_eq_mul_inv, ← inv_pow, ← hc0_sq]
    have h1 : σ ^ 2 * (A_h + cohnC airyDerivFirstZero 0 ^ 2) ≤ 1 * M := mul_le_mul (by nlinarith) (by linarith [show 0 ≤ A_h from tsum_nonneg fun _ => by positivity]) (by positivity) zero_le_one
    linarith
  have hη_nn : 0 ≤ cardinalEtaHat p h σ := by rw [hη_eq, sub_nonneg, ← Real.sqrt_sq (div_nonneg hσ0 hell.le)]; exact Real.sqrt_le_sqrt h_lb_sq
  have hden_ge : ell⁻¹ ≤ Real.sqrt (M - cardinalTailSqSum p h σ) + σ / ell := by
    have hsqrt_ge : ell⁻¹ ≤ Real.sqrt (M - cardinalTailSqSum p h σ) := by rw [← Real.sqrt_sq (inv_nonneg.mpr hell.le), ← hc0_sq]; exact Real.sqrt_le_sqrt hB0.1
    linarith [div_nonneg hσ0 hell.le]
  have h_num_eq : (Real.sqrt (M - cardinalTailSqSum p h σ) - σ / ell) * (Real.sqrt (M - cardinalTailSqSum p h σ) + σ / ell) =
      cardinalDh p h + (1 - σ ^ 2) * (A_h + cohnC airyDerivFirstZero 0 ^ 2) := by
    have hsq : Real.sqrt (M - cardinalTailSqSum p h σ) ^ 2 = M - σ ^ 2 * A_h := htail_eq ▸ Real.sq_sqrt hB0.2.1.le
    calc (Real.sqrt (M - cardinalTailSqSum p h σ) - σ / ell) * (Real.sqrt (M - cardinalTailSqSum p h σ) + σ / ell)
        = Real.sqrt (M - cardinalTailSqSum p h σ) ^ 2 - (σ / ell) ^ 2 := by ring
      _ = (M - σ ^ 2 * A_h) - σ ^ 2 * cohnC airyDerivFirstZero 0 ^ 2 := by rw [hsq, div_pow, div_eq_mul_inv, ← inv_pow, ← hc0_sq]
      _ = _ := by rw [hDh_eq]; ring
  have h_num_le : cardinalDh p h + (1 - σ ^ 2) * (A_h + cohnC airyDerivFirstZero 0 ^ 2) ≤ cardinalDh p h + (1 - σ ^ 2) * M := by
    have h1σ : 0 ≤ 1 - σ ^ 2 := by nlinarith
    have hle : A_h + cohnC airyDerivFirstZero 0 ^ 2 ≤ M := by linarith
    gcongr
  have hη_ub : cardinalEtaHat p h σ ≤ ell * (cardinalDh p h + (1 - σ ^ 2) * M) := by
    rw [hη_eq]
    calc Real.sqrt (M - cardinalTailSqSum p h σ) - σ / ell
        = (cardinalDh p h + (1 - σ ^ 2) * (A_h + cohnC airyDerivFirstZero 0 ^ 2)) / (Real.sqrt (M - cardinalTailSqSum p h σ) + σ / ell) := by
          rw [← h_num_eq, mul_div_cancel_right₀ _ (lt_of_lt_of_le (inv_pos.mpr hell) hden_ge).ne']
      _ ≤ (cardinalDh p h + (1 - σ ^ 2) * M) / ell⁻¹ :=
          div_le_div₀ (add_nonneg hDh_nn (mul_nonneg (by nlinarith) (neg_nonneg.mpr airyDerivFirstZero_spec.2.1.le))) h_num_le (inv_pos.mpr hell) hden_ge
      _ = ell * (cardinalDh p h + (1 - σ ^ 2) * M) := by rw [div_inv_eq_mul, mul_comm]
  exact ⟨hη_eq, hη_nn, hη_ub⟩

/-- `O(√h)` bound on `η̂_h` whenever `1 - σ² ≤ R₀ √h` (`(ceo:O11h.9)`). -/
theorem cardinalEtaHat_sqrt_bound {p R₀ : ℝ} (hp : p ∈ Ioo (1 / 2) 1) (hR₀ : 0 ≤ R₀) :
    ∃ C > 0, ∀ {h σ : ℝ}, h ∈ Ioc (0 : ℝ) 1 → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h → cardinalEtaHat p h σ ≤ C * √h := by
  obtain ⟨Cd, hCd, hDbd⟩ := cardinalDh_asymptotic hp
  let ell := airyDerivFirstZero - airyZero 1; have hell : 0 < ell := sub_pos.mpr airyDerivFirstZero_spec.1
  let M := -airyDerivFirstZero; have hM : 0 < M := neg_pos.mpr airyDerivFirstZero_spec.2.1
  have hJ : 0 ≤ fracJ2 p := (fracJ2_pos hp.1).le
  refine ⟨ell * (fracJ2 p + Cd + R₀ * M) + 1, by positivity, fun {h σ} hh hσ0 hσ1 hsig => ?_⟩
  have hDh_le : cardinalDh p h ≤ (fracJ2 p + Cd) * √h := by
    have h1 := (abs_le.mp (hDbd h hh)).2
    have hcd := mul_le_mul_of_nonneg_left (Real.sqrt_eq_rpow h ▸ Real.rpow_le_rpow_of_exponent_ge hh.1 hh.2 hp.1.le) hCd.le
    linarith
  calc cardinalEtaHat p h σ ≤ ell * (cardinalDh p h + (1 - σ ^ 2) * M) := (cardinalEtaHat_bounds (by linarith [hp.1]) hh.1.le hσ0 hσ1).2.2
    _ ≤ ell * ((fracJ2 p + Cd) * √h + (R₀ * √h) * M) := by gcongr
    _ ≤ (ell * (fracJ2 p + Cd + R₀ * M) + 1) * √h := by
        linarith [Real.sqrt_nonneg h, show ell * ((fracJ2 p + Cd) * √h + R₀ * √h * M) = ell * (fracJ2 p + Cd + R₀ * M) * √h by ring]

/-! ### Part 5: Axiom checks -/

/-- info: 'FormalResearch.CohnElkies.fracJ2_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.fracJ2_integrable
/-- info: 'FormalResearch.CohnElkies.fracJ2_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.fracJ2_pos
/-- info: 'FormalResearch.CohnElkies.fracJ2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.fracJ2_eq
/-- info: 'FormalResearch.CohnElkies.cardinalB0_well_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalB0_well_defined
/-- info: 'FormalResearch.CohnElkies.cardinalH_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalH_hasSum
/-- info: 'FormalResearch.CohnElkies.cardinalH_tendstoLocallyUniformly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalH_tendstoLocallyUniformly
/-- info: 'FormalResearch.CohnElkies.cardinalH_memLp_and_L2_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalH_memLp_and_L2_hasSum
/-- info: 'FormalResearch.CohnElkies.cardinalPQ_mem_airyClassG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalPQ_mem_airyClassG
/-- info: 'FormalResearch.CohnElkies.cardinalPQ_integrals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalPQ_integrals
/-- info: 'FormalResearch.CohnElkies.airyZero_counting_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyZero_counting_law
/-- info: 'FormalResearch.CohnElkies.cohnE_counting_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnE_counting_law
/-- info: 'FormalResearch.CohnElkies.cardinalDh_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalDh_asymptotic
/-- info: 'FormalResearch.CohnElkies.cardinalDh_littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalDh_littleO
/-- info: 'FormalResearch.CohnElkies.cardinalH_untuned_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalH_untuned_converges
/-- info: 'FormalResearch.CohnElkies.cardinalH_eq_untuned_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalH_eq_untuned_sub
/-- info: 'FormalResearch.CohnElkies.cardinalEtaHat_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalEtaHat_bounds
/-- info: 'FormalResearch.CohnElkies.cardinalEtaHat_sqrt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinalEtaHat_sqrt_bound

end FormalResearch.CohnElkies

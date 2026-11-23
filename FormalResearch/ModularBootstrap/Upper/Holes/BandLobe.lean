module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit

@[expose] public section

/-!
# Band and lobe upper bounds (`cmb:K6`)

This module formalizes **Lemma K6** from `comb_estimates.tex` (`\label{cmb:K6}`,
lines 241–284) for the reference comb `refComb c' f η₀`:

* **K6(a) (`band_upper_K6a_mul`, `band_upper_K6a`)**: Uniform upper bound on the band
  `x ∈ [χ_n, χ_{n+1})` for all `n ≥ f + 2`, proved unconditionally in multiplicative form and
  logarithmically away from `(η₀ = 0 ∧ x = χ_n)`, together with the fixed-distance bound on
  `[ξ_* + r₀, ∞)` (`band_upper_K6a_r0`) and global boundedness on `[0, ∞)` (`band_upper_K6a_bdd`).
* **K6(b) (`lobe_upper_K6b`, `lobe_upper_K6b_blaschke`)**: Uniform upper bound on the lobe
  `x ∈ [0, ξ_*]` with an absolute constant `C_minus > 0`, and the resulting
  `|T_{ξ_*}(x)|^{-2 n_1}` majorization for `0 ≤ x < ξ_*`.
-/

namespace FormalResearch.ModularBootstrap.Upper.Holes

open Complex Real MeasureTheory Filter Topology Set
open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Elementary helper bounds for K6 -/

private lemma tanh_strictMono : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos fun x => ?_
  have hd : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    rw [show Real.tanh = fun t => Real.sinh t / Real.cosh t from funext Real.tanh_eq_sinh_div_cosh]
    refine ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne').congr_deriv ?_
    field_simp [(Real.cosh_pos x).ne']
    linarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hd.deriv]
  exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos x))

private lemma tanh_mono {a b : ℝ} (h : a ≤ b) : Real.tanh a ≤ Real.tanh b :=
  tanh_strictMono.monotone h

private lemma tanh_ne_zero {x : ℝ} (hx : x ≠ 0) : Real.tanh x ≠ 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_ne_zero (Real.sinh_ne_zero.mpr hx) (Real.cosh_pos x).ne'

private lemma realLogT_eq_log_tanh {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) :
    realLogT x y = Real.log (Real.tanh (π * |x - y| / 2) * Real.tanh (π * (x + y) / 2)) := by
  rw [realLogT_eq_combH hx hy hxy]
  unfold combH
  have ht1 : 0 < Real.tanh (π * |x - y| / 2) :=
    tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (abs_pos.mpr (sub_ne_zero.mpr hxy.symm))) two_pos)
  have ht2 : 0 < Real.tanh (π * (x + y) / 2) := by
    have hsum : 0 < x + y := by
      rcases eq_or_lt_of_le hx with rfl | hxp
      · linarith [lt_of_le_of_ne hy hxy.symm]
      · linarith
    exact tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos hsum) two_pos)
  rw [Real.log_mul ht1.ne' ht2.ne']

private lemma tendsto_lambdaComb_zero : Tendsto lambdaComb atTop (𝓝 0) := by
  unfold lambdaComb
  have h_mul : Tendsto (fun c' : ℝ => kTip * c') atTop atTop :=
    tendsto_atTop_atTop.mpr fun M => ⟨M / kTip, fun x hx => by
      rw [div_le_iff₀ kTip_pos] at hx; linarith⟩
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h_mul

private lemma chiDeriv_antitone {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) (hab : a ≤ b) :
    chiDeriv c' b ≤ chiDeriv c' a := by
  have hanti : StrictAntiOn (chiDeriv c') (Set.Ioi (1 / 4 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ioi _)
      (fun t ht => (hasDerivAt_chiQuantile hc' ht).2.continuousAt.continuousWithinAt)
      fun t ht => by
        rw [interior_Ioi] at ht
        rw [(hasDerivAt_chiQuantile hc' ht).2.deriv]
        exact chiSecond_neg hc' ht
  exact hanti.antitoneOn ha (ha.trans_le hab) hab

private lemma chiQuantile_sub_ge_mul {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) (hab : a ≤ b) :
    (b - a) * chiDeriv c' b ≤ chiQuantile c' b - chiQuantile c' a := by
  have hcont : ContinuousOn (chiDeriv c') (Icc a b) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (ha.trans_le ht.1)).2.continuousAt.continuousWithinAt
  have hint : ∫ t in a..b, chiDeriv c' t = chiQuantile c' b - chiQuantile c' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        rw [Set.uIcc_of_le hab] at ht
        exact (hasDerivAt_chiQuantile hc' (ha.trans_le ht.1)).1)
      (hcont.intervalIntegrable_of_Icc hab)
  rw [← hint]
  have hconst : (b - a) * chiDeriv c' b = ∫ _t in a..b, chiDeriv c' b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst]
  exact intervalIntegral.integral_mono_on hab
    intervalIntegrable_const (hcont.intervalIntegrable_of_Icc hab)
    fun t ht => chiDeriv_antitone hc' (ha.trans_le ht.1) ht.2

private lemma chiQuantile_sub_le_mul {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) (hab : a ≤ b) :
    chiQuantile c' b - chiQuantile c' a ≤ (b - a) * chiDeriv c' a := by
  have hcont : ContinuousOn (chiDeriv c') (Icc a b) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (ha.trans_le ht.1)).2.continuousAt.continuousWithinAt
  have hint : ∫ t in a..b, chiDeriv c' t = chiQuantile c' b - chiQuantile c' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        rw [Set.uIcc_of_le hab] at ht
        exact (hasDerivAt_chiQuantile hc' (ha.trans_le ht.1)).1)
      (hcont.intervalIntegrable_of_Icc hab)
  rw [← hint]
  have hconst : (b - a) * chiDeriv c' a = ∫ _t in a..b, chiDeriv c' a := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst]
  exact intervalIntegral.integral_mono_on hab
    (hcont.intervalIntegrable_of_Icc hab) intervalIntegrable_const
    fun t ht => chiDeriv_antitone hc' ha ht.1

private lemma siteGap_ge_chiDeriv {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    chiDeriv c' ((k : ℝ) + 1) ≤ siteGap c' k := by
  have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h := chiQuantile_sub_ge_mul hc' hk14 (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
  have heq : (k : ℝ) + 1 - (k : ℝ) = 1 := by ring
  rw [heq, one_mul] at h
  unfold siteGap
  push_cast
  exact h

private lemma siteGap_le_chiDeriv {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    siteGap c' k ≤ chiDeriv c' (k : ℝ) := by
  have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h := chiQuantile_sub_le_mul hc' hk14 (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
  have heq : (k : ℝ) + 1 - (k : ℝ) = 1 := by ring
  rw [heq, one_mul] at h
  unfold siteGap
  push_cast
  exact h

private lemma cosh_one_lt_two : Real.cosh 1 < 2 := by
  have he1 : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hem1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [Real.cosh_eq]
  linarith

private lemma abs_sinh_le_two_mul {t : ℝ} (ht : |t| ≤ 1) : |Real.sinh t| ≤ 2 * |t| := by
  have h_nn : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → Real.sinh u ≤ 2 * u := by
    intro u hu0 hu1
    have hanti : AntitoneOn (fun s => Real.sinh s - 2 * s) (Icc 0 1) :=
      antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
        (Real.continuous_sinh.sub (continuous_const.mul continuous_id)).continuousOn
        (fun s _ => ((Real.hasDerivAt_sinh s).sub
          ((hasDerivAt_id s).const_mul 2)).differentiableAt.differentiableWithinAt)
        fun s hs => by
          rw [interior_Icc] at hs
          have hd : HasDerivAt (fun r => Real.sinh r - 2 * r) (Real.cosh s - 2) s := by
            refine ((Real.hasDerivAt_sinh s).sub ((hasDerivAt_id s).const_mul 2)).congr_deriv ?_
            simp
          rw [hd.deriv]
          have hch : Real.cosh s ≤ Real.cosh 1 := by
            rw [Real.cosh_le_cosh, abs_of_nonneg hs.1.le, abs_one]
            exact hs.2.le
          linarith [cosh_one_lt_two]
    have h0 := hanti ⟨le_rfl, zero_le_one⟩ ⟨hu0, hu1⟩ hu0
    simp only [Real.sinh_zero, mul_zero, sub_zero] at h0
    linarith
  rcases le_total 0 t with ht0 | ht0
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht0), abs_of_nonneg ht0]
    exact h_nn t ht0 ((abs_of_nonneg ht0).symm ▸ ht)
  · have ht' : 0 ≤ -t := neg_nonneg.mpr ht0
    have h_abs : |-t| ≤ 1 := by simpa [abs_neg] using ht
    rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr ht0), abs_of_nonpos ht0, ← Real.sinh_neg]
    exact h_nn (-t) ht' ((abs_of_nonneg ht').symm ▸ h_abs)

private lemma tanh_ge_half_self {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : y / 2 ≤ Real.tanh y := by
  have hsh : y ≤ Real.sinh y := by
    have hmono : MonotoneOn (fun s => Real.sinh s - s) (Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (Real.continuous_sinh.sub continuous_id).continuousOn
        (fun s _ => ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)).differentiableAt.differentiableWithinAt)
        fun s _ => by
          have hd : HasDerivAt (fun r => Real.sinh r - r) (Real.cosh s - 1) s :=
            (Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)
          rw [hd.deriv]
          linarith [Real.one_le_cosh s]
    have h0 := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy0) hy0
    simp only [Real.sinh_zero, sub_zero] at h0
    linarith
  have hch : Real.cosh y < 2 := by
    have h1 : Real.cosh y ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hy0, abs_one]
      exact hy1
    exact h1.trans_lt cosh_one_lt_two
  rw [Real.tanh_eq_sinh_div_cosh]
  have hch_pos : 0 < Real.cosh y := Real.cosh_pos y
  rw [div_le_div_iff₀ two_pos hch_pos]
  nlinarith

private lemma integral_log_zero_le_bound {c : ℝ} (hc0 : 0 ≤ c) :
    -1 ≤ ∫ t in (0 : ℝ)..c, Real.log t := by
  rcases eq_or_lt_of_le hc0 with rfl | hc_pos
  · simp
  rw [integral_log]
  simp only [zero_mul, Real.log_zero, sub_zero, add_zero]
  have h_min : ∀ y : ℝ, 0 < y → -1 ≤ y * Real.log y - y := by
    intro y hy
    rcases le_total y 1 with hy1 | hy1
    · have hanti : AntitoneOn (fun t => t * Real.log t - t) (Icc y 1) :=
        antitoneOn_of_deriv_nonpos (convex_Icc y 1)
          ((continuousOn_id.mul (Real.continuousOn_log.mono fun t ht =>
            (lt_of_lt_of_le hy ht.1).ne')).sub continuousOn_id)
          (fun t ht => by
            rw [interior_Icc] at ht
            have ht0 : t ≠ 0 := (lt_trans hy ht.1).ne'
            exact (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).sub
              (hasDerivAt_id t)).differentiableAt.differentiableWithinAt)
          fun t ht => by
            rw [interior_Icc] at ht
            have ht0 : t ≠ 0 := (lt_trans hy ht.1).ne'
            have hd : HasDerivAt (fun s => s * Real.log s - s) (Real.log t) t := by
              refine (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).sub
                (hasDerivAt_id t)).congr_deriv ?_
              simp [ht0]
            rw [hd.deriv]
            exact Real.log_nonpos (lt_trans hy ht.1).le ht.2.le
      have hval := hanti ⟨le_rfl, hy1⟩ ⟨hy1, le_rfl⟩ hy1
      simp only [Real.log_one, mul_zero, zero_sub] at hval
      exact hval
    · have hmono : MonotoneOn (fun t => t * Real.log t - t) (Icc 1 y) :=
        monotoneOn_of_deriv_nonneg (convex_Icc 1 y)
          ((continuousOn_id.mul (Real.continuousOn_log.mono fun t ht =>
            (lt_of_lt_of_le zero_lt_one ht.1).ne')).sub continuousOn_id)
          (fun t ht => by
            rw [interior_Icc] at ht
            have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht.1).ne'
            exact (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).sub
              (hasDerivAt_id t)).differentiableAt.differentiableWithinAt)
          fun t ht => by
            rw [interior_Icc] at ht
            have ht0 : t ≠ 0 := (lt_trans zero_lt_one ht.1).ne'
            have hd : HasDerivAt (fun s => s * Real.log s - s) (Real.log t) t := by
              refine (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).sub
                (hasDerivAt_id t)).congr_deriv ?_
              simp [ht0]
            rw [hd.deriv]
            exact Real.log_nonneg ht.1.le
      have hval := hmono ⟨le_rfl, hy1⟩ ⟨hy1, le_rfl⟩ hy1
      simp only [Real.log_one, mul_zero, zero_sub] at hval
      exact hval
  exact h_min c hc_pos

private lemma integral_log_abs_sub_ge {aStar A B : ℝ} (haA : A ≤ aStar) (haB : aStar ≤ B) :
    -2 ≤ ∫ a in A..B, Real.log |aStar - a| := by
  have hi1 : IntervalIntegrable (fun a => Real.log |aStar - a|) volume A aStar := by
    have hlin : IntervalIntegrable (fun s : ℝ => Real.log s) volume 0 (aStar - A) :=
      intervalIntegral.intervalIntegrable_log'
    have hcomp : IntervalIntegrable (fun a => Real.log (aStar - a)) volume A aStar := by
      have h := (hlin.comp_sub_left aStar).symm
      simpa [sub_sub_cancel] using h
    refine hcomp.congr fun a ha => ?_
    rw [Set.uIoc_of_le haA] at ha
    rcases eq_or_lt_of_le ha.2 with rfl | hlt
    · simp
    · rw [abs_of_pos (sub_pos.mpr hlt)]
  have hi2 : IntervalIntegrable (fun a => Real.log |aStar - a|) volume aStar B := by
    have hlin : IntervalIntegrable (fun s : ℝ => Real.log s) volume 0 (B - aStar) :=
      intervalIntegral.intervalIntegrable_log'
    have hcomp : IntervalIntegrable (fun a => Real.log (a - aStar)) volume aStar B := by
      have h := hlin.comp_sub_right aStar
      simpa using h
    refine hcomp.congr fun a ha => ?_
    rw [Set.uIoc_of_le haB] at ha
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr ha.1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h_ae_ne : ∀ᵐ a ∂volume, a ≠ aStar := by rw [ae_iff]; simp
  have heq1 : ∫ a in A..aStar, Real.log |aStar - a| = ∫ s in (0 : ℝ)..(aStar - A), Real.log s := by
    have h1 : ∫ a in A..aStar, Real.log |aStar - a| = ∫ a in A..aStar, Real.log (aStar - a) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [h_ae_ne] with a hane ha
      rw [Set.uIoc_of_le haA] at ha
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_ne ha.2 hane))]
    rw [h1, intervalIntegral.integral_comp_sub_left (fun s => Real.log s) aStar, sub_self]
  have heq2 : ∫ a in aStar..B, Real.log |aStar - a| = ∫ s in (0 : ℝ)..(B - aStar), Real.log s := by
    have h1 : ∫ a in aStar..B, Real.log |aStar - a| = ∫ a in aStar..B, Real.log (a - aStar) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [h_ae_ne] with a hane ha
      rw [Set.uIoc_of_le haB] at ha
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr ha.1)]
    rw [h1, intervalIntegral.integral_comp_sub_right (fun s => Real.log s) aStar, sub_self]
  rw [heq1, heq2]
  linarith [integral_log_zero_le_bound (sub_nonneg.mpr haA),
    integral_log_zero_le_bound (sub_nonneg.mpr haB)]

private lemma refComb_eq_zero_of_zero_at_site {c' : ℝ} (hc' : 0 < c')
    {f n : ℕ} (hf : 1 ≤ f) (hn : f + 1 ≤ n) :
    refComb c' f 0 (chiQuantile c' n : ℂ) = 0 := by
  let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  let ε := fun _ : ℕ => (0 : ℝ)
  let P : ℕ → ℂ := fun m =>
    blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (chiQuantile c' n : ℂ) *
      blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (chiQuantile c' n : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun _ => by simp [ε]
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd
    (summable_exp_neg_pi_chiQuantile hc' f)).hasProd
    (by simp : (chiQuantile c' n : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  let m₀ : ℕ := n - (f + 1)
  have hm₀_eq : f + 1 + m₀ = n := by omega
  have hPm₀ : P m₀ = 0 := by
    have hχm : χ m₀ = chiQuantile c' n := by dsimp [χ]; rw [hm₀_eq]
    have hεm : ε m₀ = 0 := rfl
    have hself : blaschkeT (chiQuantile c' n : ℂ) (chiQuantile c' n : ℂ) = 0 := by
      unfold blaschkeT; simp
    simp only [P, hχm, hεm, Complex.ofReal_zero, zero_mul, add_zero, hself, zero_mul]
  have htprod0 : (∏' m : ℕ, P m) = 0 := by
    refine tendsto_nhds_unique hhasProd ?_
    refine Tendsto.congr' ?_ tendsto_const_nhds
    change ∀ᶠ s : Finset ℕ in atTop, (0 : ℂ) = ∏ b ∈ s, P b
    rw [Filter.eventually_atTop]
    refine ⟨{m₀}, fun s hs => ?_⟩
    exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self m₀)) hPm₀).symm
  have h_unfold : refComb c' f 0 (chiQuantile c' n : ℂ) =
      blaschkeT (chiQuantile c' f : ℂ) (chiQuantile c' n : ℂ) * ∏' m : ℕ, P m := by
    unfold refComb; simp [χ, ε, P]
  rw [h_unfold, htprod0, mul_zero]

private lemma refComb_norm_pos_of_ne_site {c' η₀ x : ℝ} (hc' : 0 < c') (hx0 : 0 ≤ x)
    {f : ℕ} (hf : 1 ≤ f) (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (hf_ne : chiQuantile c' f ≠ x)
    (hq_all : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m)) :
    0 < ‖refComb c' f η₀ (x : ℂ)‖ := by
  have hsum_q := (refComb_norm_log_eq_tsum hc' hx0 hf hη₀0 hη₀1 hgap hf_ne hq_all).1
  have h_prod_exp : HasProd (fun m : ℕ => pairModQ c' η₀ x (f + 1 + m))
      (Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)))) := by
    refine (Real.continuous_exp.continuousAt.tendsto.comp hsum_q.hasSum).congr fun s => ?_
    dsimp [Function.comp_def]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun m _ => Real.exp_log (hq_all m)
  let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  let ε := fun m : ℕ => η₀ * siteGap c' (f + 1 + m)
  let P : ℕ → ℂ := fun m =>
    blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (x : ℂ) *
      blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
    dsimp [ε]
    have hgk : siteGap c' (f + 1 + m) ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ f + 1 + m - 1 by omega)
      convert hanti using 2
      omega
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    have hgk_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      push_cast
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgk_nn)]; nlinarith [hη₀1, hgap, hgk]
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd
    (summable_exp_neg_pi_chiQuantile hc' f)).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hnorm_prod : HasProd (fun m : ℕ => ‖P m‖) ‖∏' m : ℕ, P m‖ := by
    refine (continuous_norm.continuousAt.tendsto.comp hhasProd).congr fun s => ?_
    dsimp [Function.comp_def]
    induction s using Finset.induction with
    | empty => simp
    | @insert a s has ih => rw [Finset.prod_insert has, Finset.prod_insert has, norm_mul, ih]
  have h_norm_eq : (fun m : ℕ => ‖P m‖) = fun m : ℕ => pairModQ c' η₀ x (f + 1 + m) := by
    ext m; rfl
  rw [h_norm_eq] at hnorm_prod
  have h_tprod_pos : 0 < ‖∏' m : ℕ, P m‖ := by
    rw [tendsto_nhds_unique hnorm_prod h_prod_exp]
    exact Real.exp_pos _
  have hχf_pos : 0 < chiQuantile c' f := by
    have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
    exact xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
  have hT_pos : 0 < ‖blaschkeT (chiQuantile c' f : ℂ) (x : ℂ)‖ := by
    have h_eq := realLogT_eq_log_tanh hx0 hχf_pos.le hf_ne
    have hlog : Real.log ‖blaschkeT (chiQuantile c' f : ℂ) (x : ℂ)‖ = realLogT x (chiQuantile c' f) := rfl
    by_contra h0
    have hnorm0 : ‖blaschkeT (chiQuantile c' f : ℂ) (x : ℂ)‖ = 0 :=
      le_antisymm (not_lt.mp h0) (norm_nonneg _)
    have hl0 : realLogT x (chiQuantile c' f) = 0 := by rw [← hlog, hnorm0, Real.log_zero]
    have ht1 : 0 < Real.tanh (π * |x - chiQuantile c' f| / 2) :=
      tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (abs_pos.mpr (sub_ne_zero.mpr hf_ne.symm))) two_pos)
    have ht2 : 0 < Real.tanh (π * (x + chiQuantile c' f) / 2) :=
      tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (by linarith)) two_pos)
    have hprod_lt1 : Real.tanh (π * |x - chiQuantile c' f| / 2) *
        Real.tanh (π * (x + chiQuantile c' f) / 2) < 1 := by
      have ht1_lt := Real.tanh_lt_one (π * |x - chiQuantile c' f| / 2)
      have ht2_lt := Real.tanh_lt_one (π * (x + chiQuantile c' f) / 2)
      nlinarith
    have hlog_neg : realLogT x (chiQuantile c' f) < 0 := by
      rw [h_eq]; exact Real.log_neg (mul_pos ht1 ht2) hprod_lt1
    linarith
  have h_unfold : refComb c' f η₀ (x : ℂ) =
      blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) * ∏' m : ℕ, P m := by
    unfold refComb; simp [χ, ε, P]
  rw [h_unfold, norm_mul]
  exact mul_pos hT_pos h_tprod_pos

/-! ### Section 2: K6(a) Band upper bound (`cmb:K6`, `comb_estimates.tex`, lines 244–248) -/

private lemma holeH_one_le_K6a {c' η₀ x : ℝ} {n : ℕ}
    (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hn3 : 3 ≤ n) (hx : inCell c' n x) (hgap_small : siteGap c' 1 ≤ 1 / (16 * π))
    (hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n) :
    holeH c' η₀ n 1 x ≤
      2 * Real.log 64 - 4 * Real.log (Real.tanh (π * xiStar)) - 4 * Real.log (π / 8) + 8 := by
  let ℓ := siteGap c' n
  have hn_r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn14 : (1 / 4 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hℓ_le1 : ℓ ≤ siteGap c' 1 := by
    have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ n - 1 by omega)
    dsimp [ℓ]
    convert hanti using 2
    omega
  have hℓ_small : ℓ ≤ 1 / (16 * π) := hℓ_le1.trans hgap_small
  have hℓ_pos : 0 < ℓ := by
    unfold ℓ siteGap
    push_cast
    exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have h_deriv_ratio : chiDeriv c' ((n : ℝ) - 1 / 2) ≤ 2 * chiDeriv c' ((n : ℝ) + 3 / 2) := by
    have hdiv := chiDeriv_div_le hc' hn14 (by linarith : (n : ℝ) - 1 / 2 ≤ (n : ℝ) + 3 / 2)
    have hden_pos : 0 < chiDeriv c' ((n : ℝ) + 3 / 2) := chiDeriv_pos hc' (by linarith)
    have hfrac : ((n : ℝ) + 3 / 2 - 1 / 4) / ((n : ℝ) - 1 / 2 - 1 / 4) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    exact (div_le_iff₀ hden_pos).mp (hdiv.trans hfrac)
  have h_deriv_bounds : ∀ t ∈ Icc ((n : ℝ) - 1 / 2) ((n : ℝ) + 3 / 2),
      (1 / 2 : ℝ) * ℓ ≤ chiDeriv c' t ∧ chiDeriv c' t ≤ 2 * ℓ := by
    have hl_ge : chiDeriv c' ((n : ℝ) + 3 / 2) ≤ ℓ := by
      have hsub := chiQuantile_sub_ge_mul hc' (by linarith : (1 / 4 : ℝ) < (n : ℝ))
        (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      have h1 : chiDeriv c' ((n : ℝ) + 3 / 2) ≤ chiDeriv c' ((n : ℝ) + 1) :=
        chiDeriv_antitone hc' (by linarith) (by linarith)
      unfold ℓ siteGap; push_cast
      linarith [hsub, h1]
    have hl_le : ℓ ≤ chiDeriv c' ((n : ℝ) - 1 / 2) := by
      have hsub := chiQuantile_sub_le_mul hc' (by linarith : (1 / 4 : ℝ) < (n : ℝ))
        (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      have h1 : chiDeriv c' (n : ℝ) ≤ chiDeriv c' ((n : ℝ) - 1 / 2) :=
        chiDeriv_antitone hc' hn14 (by linarith)
      unfold ℓ siteGap; push_cast
      linarith [hsub, h1]
    intro t ht
    have h_lo : chiDeriv c' ((n : ℝ) + 3 / 2) ≤ chiDeriv c' t :=
      chiDeriv_antitone hc' (hn14.trans_le ht.1) ht.2
    have h_hi : chiDeriv c' t ≤ chiDeriv c' ((n : ℝ) - 1 / 2) :=
      chiDeriv_antitone hc' hn14 ht.1
    constructor <;> linarith
  have h_site_log : ∀ m ∈ ({n, n + 1} : Finset ℕ),
      Real.log (pairModQ c' η₀ x m) ≤ 2 * Real.log ℓ + Real.log 64 := by
    intro m hm
    have hm_r : m = n ∨ m = n + 1 := by simpa using hm
    have hm_ge3 : 3 ≤ m := by rcases hm_r with rfl | rfl <;> omega
    have hm14 : (1 / 4 : ℝ) < (m : ℝ) := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge3
      linarith
    have hxm_bd : |x - chiQuantile c' m| ≤ ℓ := by
      rcases hm_r with rfl | rfl
      · rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
        unfold ℓ siteGap; push_cast
        have h2 := hx.2; push_cast at h2; linarith
      · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hx.2)]
        unfold ℓ siteGap; push_cast
        have h1 := hx.1; linarith
    have hℓm_le : siteGap c' m ≤ ℓ := by
      rcases hm_r with rfl | rfl
      · exact le_rfl
      · have hanti := (siteGap_strictAnti hc').antitone (show n - 1 ≤ n by omega)
        dsimp [ℓ]; convert hanti using 2; omega
    have hℓm_nn : 0 ≤ siteGap c' m := by
      unfold siteGap; push_cast
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr hm14.le) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    let α := π * (x - chiQuantile c' m) / 2
    let β := π * (η₀ * siteGap c' m) / 2
    let γ := π * (x + chiQuantile c' m) / 2
    have hpi := Real.pi_pos
    have hα_bd : |α| ≤ π * ℓ / 2 := by
      dsimp [α]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxm_bd hpi.le) two_pos.le
    have hα_le1 : |α| ≤ 1 := by
      have h1 : π * (1 / (16 * π)) / 2 = 1 / 32 := by field_simp [hpi.ne']; ring
      calc |α| ≤ π * ℓ / 2 := hα_bd
        _ ≤ π * (1 / (16 * π)) / 2 := by gcongr
        _ = 1 / 32 := h1
        _ ≤ 1 := by norm_num
    have hβ_nn : 0 ≤ β := div_nonneg (mul_nonneg hpi.le (mul_nonneg hη₀0 hℓm_nn)) two_pos.le
    have hβ_bd : β ≤ π * ℓ / 8 := by
      dsimp [β]
      have h1 : η₀ * siteGap c' m ≤ (1 / 4 : ℝ) * ℓ := mul_le_mul hη₀1 hℓm_le hℓm_nn (by norm_num)
      calc π * (η₀ * siteGap c' m) / 2 ≤ π * ((1 / 4 : ℝ) * ℓ) / 2 := by gcongr
        _ = π * ℓ / 8 := by ring
    have hβ_le14 : β ≤ 1 / 4 := by
      have h1 : π * (1 / (16 * π)) / 8 = 1 / 128 := by field_simp [hpi.ne']; ring
      calc β ≤ π * ℓ / 8 := hβ_bd
        _ ≤ π * (1 / (16 * π)) / 8 := by gcongr
        _ = 1 / 128 := h1
        _ ≤ 1 / 4 := by norm_num
    have h_sin_le : |Real.sin β| ≤ β := Real.abs_sin_le_abs.trans (abs_of_nonneg hβ_nn).le
    have h_sin2_le : Real.sin β ^ 2 ≤ 1 / 2 := by
      have hab : |Real.sin β| ≤ 1 / 4 := h_sin_le.trans hβ_le14
      have hsq : Real.sin β ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
      linarith
    have hχm_pos : 0 < chiQuantile c' m := xiStar_pos.trans (xiStar_lt_chiQuantile hc' hm14)
    have hχn_pos : 0 < chiQuantile c' n := xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
    have hx_pos : 0 < x := hχn_pos.trans_le hx.1
    have hγ_pos : 0 < γ := div_pos (mul_pos hpi (add_pos hx_pos hχm_pos)) two_pos
    have hq_pos : 0 < pairModQ c' η₀ x m := by
      unfold pairModQ
      rw [blaschkePairQ_eq]
      have hden1 : 0 < Real.cosh α ^ 2 - Real.sin β ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh α)]
      have hden2 : 0 < Real.cosh γ ^ 2 - Real.sin β ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh γ)]
      have hnum2 : 0 < Real.sinh γ ^ 2 + Real.sin β ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos (Real.sinh_pos_iff.mpr hγ_pos) 2) (sq_nonneg _)
      have hnum1 : 0 < Real.sinh α ^ 2 + Real.sin β ^ 2 := by
        rcases hnz with hη | hne
        · rcases hm_r with rfl | rfl
          · have hb_p : 0 < β := div_pos (mul_pos hpi (mul_pos hη hℓ_pos)) two_pos
            have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hb_p (by linarith [Real.pi_gt_three])
            positivity
          · have hα_ne : α ≠ 0 := by
              dsimp [α]
              exact div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hx.2.ne)) two_ne_zero
            have hsh_ne : Real.sinh α ≠ 0 := Real.sinh_ne_zero.mpr hα_ne
            positivity
        · have hα_ne : α ≠ 0 := by
            dsimp [α]
            rcases hm_r with rfl | rfl
            · exact div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hne)) two_ne_zero
            · exact div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hx.2.ne)) two_ne_zero
          have hsh_ne : Real.sinh α ≠ 0 := Real.sinh_ne_zero.mpr hα_ne
          positivity
      exact mul_pos (div_pos hnum1 hden1) (div_pos hnum2 hden2)
    have hq_le : pairModQ c' η₀ x m ≤ 64 * ℓ ^ 2 := by
      unfold pairModQ
      rw [blaschkePairQ_eq]
      have hden1 : 1 / 2 ≤ Real.cosh α ^ 2 - Real.sin β ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh α)]
      have hden2 : 0 < Real.cosh γ ^ 2 - Real.sin β ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh γ)]
      have hf2_le1 : (Real.sinh γ ^ 2 + Real.sin β ^ 2) / (Real.cosh γ ^ 2 - Real.sin β ^ 2) ≤ 1 := by
        rw [div_le_one hden2]
        have hch_sh : Real.cosh γ ^ 2 - Real.sinh γ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq γ
        linarith
      have hsh_le : Real.sinh α ^ 2 ≤ 4 * α ^ 2 := by
        have h1 := abs_sinh_le_two_mul hα_le1
        calc Real.sinh α ^ 2 = |Real.sinh α| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * |α|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = 4 * α ^ 2 := by rw [mul_pow, sq_abs]; norm_num
      have hsin_le : Real.sin β ^ 2 ≤ β ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h_sin_le 2
      have hnum1_le : Real.sinh α ^ 2 + Real.sin β ^ 2 ≤ 32 * ℓ ^ 2 := by
        have hα2 : α ^ 2 ≤ (π * ℓ / 2) ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hα_bd 2
        have hβ2 : β ^ 2 ≤ (π * ℓ / 8) ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ hβ_nn hβ_bd 2
        have hpi4 : π ^ 2 ≤ 16 := by
          have : π ≤ 4 := by linarith [Real.pi_lt_d4]
          nlinarith [hpi]
        calc Real.sinh α ^ 2 + Real.sin β ^ 2
            ≤ 4 * α ^ 2 + β ^ 2 := add_le_add hsh_le hsin_le
          _ ≤ 4 * (π * ℓ / 2) ^ 2 + (π * ℓ / 8) ^ 2 := by gcongr
          _ = π ^ 2 * (1 + 1 / 64) * ℓ ^ 2 := by ring
          _ ≤ 16 * 2 * ℓ ^ 2 := by gcongr; norm_num
          _ = 32 * ℓ ^ 2 := by ring
      have hf1_le : (Real.sinh α ^ 2 + Real.sin β ^ 2) / (Real.cosh α ^ 2 - Real.sin β ^ 2) ≤ 64 * ℓ ^ 2 := by
        calc (Real.sinh α ^ 2 + Real.sin β ^ 2) / (Real.cosh α ^ 2 - Real.sin β ^ 2)
            ≤ (32 * ℓ ^ 2) / (1 / 2 : ℝ) :=
              div_le_div₀ (by positivity) hnum1_le (by norm_num) hden1
          _ = 64 * ℓ ^ 2 := by ring
      have hf2_nn : 0 ≤ (Real.sinh γ ^ 2 + Real.sin β ^ 2) / (Real.cosh γ ^ 2 - Real.sin β ^ 2) := by
        positivity
      calc ((Real.sinh α ^ 2 + Real.sin β ^ 2) / (Real.cosh α ^ 2 - Real.sin β ^ 2)) *
            ((Real.sinh γ ^ 2 + Real.sin β ^ 2) / (Real.cosh γ ^ 2 - Real.sin β ^ 2))
          ≤ (64 * ℓ ^ 2) * 1 := mul_le_mul hf1_le hf2_le1 hf2_nn (by positivity)
        _ = 64 * ℓ ^ 2 := mul_one _
    calc Real.log (pairModQ c' η₀ x m)
        ≤ Real.log (64 * ℓ ^ 2) := Real.log_le_log hq_pos hq_le
      _ = 2 * Real.log ℓ + Real.log 64 := by
          rw [Real.log_mul (by norm_num) (sq_pos_of_pos hℓ_pos).ne', Real.log_pow]
          push_cast; ring
  have haStar_ex : ∃ aStar ∈ Ico (n : ℝ) ((n : ℝ) + 1), chiQuantile c' aStar = x := by
    have hcont : ContinuousOn (chiQuantile c') (Icc (n : ℝ) ((n : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [hn14, ht.1])).1.continuousAt.continuousWithinAt
    have hcast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' ((n : ℝ) + 1) := by push_cast; rfl
    have hmem : x ∈ Icc (chiQuantile c' (n : ℝ)) (chiQuantile c' ((n : ℝ) + 1)) :=
      ⟨hx.1, hcast ▸ hx.2.le⟩
    obtain ⟨aStar, haI, haEq⟩ := intermediate_value_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) hcont hmem
    have ha_lt : aStar < (n : ℝ) + 1 := by
      rcases eq_or_lt_of_le haI.2 with rfl | hlt
      · exfalso; have hx2 := hx.2; rw [hcast] at hx2; linarith
      · exact hlt
    exact ⟨aStar, ⟨haI.1, ha_lt⟩, haEq⟩
  rcases haStar_ex with ⟨aStar, haStar_Ico, haStar_eq⟩
  let A : ℝ := (n : ℝ) - 1 / 2
  let B : ℝ := (n : ℝ) + 3 / 2
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hA_a : A ≤ aStar := by dsimp [A]; linarith [haStar_Ico.1]
  have ha_B : aStar ≤ B := by dsimp [B]; linarith [haStar_Ico.2]
  have h_pt_lb : ∀ a ∈ Icc A B, a ≠ aStar →
      Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8) ≤
        phiVar c' x a := by
    intro a ha hane
    dsimp [A, B] at ha
    have ha14 : (1 / 4 : ℝ) < a := hn14.trans_le ha.1
    have haStar14 : (1 / 4 : ℝ) < aStar := by linarith [hn14, haStar_Ico.1]
    have hx_ne_a : chiQuantile c' a ≠ x := by
      intro heq
      rw [← haStar_eq] at heq
      exact hane ((chiQuantile_strictMonoOn hc').injOn (Set.mem_Ici.mpr ha14.le)
        (Set.mem_Ici.mpr haStar14.le) heq)
    have h_dist_lb : (1 / 2 : ℝ) * ℓ * |aStar - a| ≤ |x - chiQuantile c' a| := by
      have h_min14 : (1 / 4 : ℝ) < min a aStar := lt_min ha14 haStar14
      have hcon : ContinuousOn (chiDeriv c') (Icc (min a aStar) (max a aStar)) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (h_min14.trans_le ht.1)).2.continuousAt.continuousWithinAt
      have hint_diff : chiQuantile c' (max a aStar) - chiQuantile c' (min a aStar) =
          ∫ t in (min a aStar)..(max a aStar), chiDeriv c' t :=
        (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => by
            rw [Set.uIcc_of_le min_le_max] at ht
            exact (hasDerivAt_chiQuantile hc' (h_min14.trans_le ht.1)).1)
          (hcon.intervalIntegrable_of_Icc min_le_max)).symm
      have h_int_lb : (max a aStar - min a aStar) * ((1 / 2 : ℝ) * ℓ) ≤
          ∫ t in (min a aStar)..(max a aStar), chiDeriv c' t := by
        have hc_eq : (max a aStar - min a aStar) * ((1 / 2 : ℝ) * ℓ) =
            ∫ _t in (min a aStar)..(max a aStar), (1 / 2 : ℝ) * ℓ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [hc_eq]
        exact intervalIntegral.integral_mono_on min_le_max intervalIntegrable_const
          (hcon.intervalIntegrable_of_Icc min_le_max) fun t ht =>
            (h_deriv_bounds t ⟨(le_min ha.1 (by linarith [haStar_Ico.1])).trans ht.1,
              ht.2.trans (max_le ha.2 (by linarith [haStar_Ico.2]))⟩).1
      rcases le_total a aStar with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hint_diff h_int_lb
        rw [abs_of_nonneg (sub_nonneg.mpr hle), ← haStar_eq,
          abs_of_nonneg (sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr ha14.le) (Set.mem_Ici.mpr haStar14.le) hle))]
        linarith
      · rw [min_eq_right hle, max_eq_left hle] at hint_diff h_int_lb
        rw [abs_sub_comm aStar a, abs_of_nonneg (sub_nonneg.mpr hle), abs_sub_comm x _, ← haStar_eq,
          abs_of_nonneg (sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr haStar14.le) (Set.mem_Ici.mpr ha14.le) hle))]
        linarith
    have h_dist_ub : |x - chiQuantile c' a| ≤ 2 * ℓ * |aStar - a| := by
      have h_min14 : (1 / 4 : ℝ) < min a aStar := lt_min ha14 haStar14
      have hcon : ContinuousOn (chiDeriv c') (Icc (min a aStar) (max a aStar)) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (h_min14.trans_le ht.1)).2.continuousAt.continuousWithinAt
      have hint_diff : chiQuantile c' (max a aStar) - chiQuantile c' (min a aStar) =
          ∫ t in (min a aStar)..(max a aStar), chiDeriv c' t :=
        (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => by
            rw [Set.uIcc_of_le min_le_max] at ht
            exact (hasDerivAt_chiQuantile hc' (h_min14.trans_le ht.1)).1)
          (hcon.intervalIntegrable_of_Icc min_le_max)).symm
      have h_int_ub : ∫ t in (min a aStar)..(max a aStar), chiDeriv c' t ≤
          (max a aStar - min a aStar) * (2 * ℓ) := by
        have hc_eq : (max a aStar - min a aStar) * (2 * ℓ) =
            ∫ _t in (min a aStar)..(max a aStar), 2 * ℓ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [hc_eq]
        exact intervalIntegral.integral_mono_on min_le_max
          (hcon.intervalIntegrable_of_Icc min_le_max) intervalIntegrable_const fun t ht =>
            (h_deriv_bounds t ⟨(le_min ha.1 (by linarith [haStar_Ico.1])).trans ht.1,
              ht.2.trans (max_le ha.2 (by linarith [haStar_Ico.2]))⟩).2
      rcases le_total a aStar with hle | hle
      · rw [min_eq_left hle, max_eq_right hle] at hint_diff h_int_ub
        rw [abs_of_nonneg (sub_nonneg.mpr hle), ← haStar_eq,
          abs_of_nonneg (sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr ha14.le) (Set.mem_Ici.mpr haStar14.le) hle))]
        linarith
      · rw [min_eq_right hle, max_eq_left hle] at hint_diff h_int_ub
        rw [abs_sub_comm aStar a, abs_of_nonneg (sub_nonneg.mpr hle), abs_sub_comm x _, ← haStar_eq,
          abs_of_nonneg (sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr haStar14.le) (Set.mem_Ici.mpr ha14.le) hle))]
        linarith
    have ha_len : |aStar - a| ≤ 2 := abs_le.mpr ⟨by linarith [ha.2, haStar_Ico.1], by linarith [ha.1, haStar_Ico.2]⟩
    have h_diff_pos : 0 < |x - chiQuantile c' a| := abs_pos.mpr (sub_ne_zero.mpr hx_ne_a.symm)
    have h_y1_pos : 0 < π * |x - chiQuantile c' a| / 2 := div_pos (mul_pos Real.pi_pos h_diff_pos) two_pos
    have h_y1_le1 : π * |x - chiQuantile c' a| / 2 ≤ 1 := by
      have h1 : |x - chiQuantile c' a| ≤ 4 * ℓ := by
        calc |x - chiQuantile c' a| ≤ 2 * ℓ * |aStar - a| := h_dist_ub
          _ ≤ 2 * ℓ * 2 := mul_le_mul_of_nonneg_left ha_len (by positivity)
          _ = 4 * ℓ := by ring
      have hpi := Real.pi_pos
      have h3 : π * (4 * (1 / (16 * π))) / 2 = 1 / 8 := by field_simp [hpi.ne']; ring
      calc π * |x - chiQuantile c' a| / 2 ≤ π * (4 * ℓ) / 2 := by gcongr
        _ ≤ π * (4 * (1 / (16 * π))) / 2 := by gcongr
        _ = 1 / 8 := h3
        _ ≤ 1 := by norm_num
    have h_t1_ge : π * |x - chiQuantile c' a| / 4 ≤ Real.tanh (π * |x - chiQuantile c' a| / 2) := by
      linarith [tanh_ge_half_self h_y1_pos.le h_y1_le1]
    have h_lb1 : Real.log ℓ + Real.log |aStar - a| + Real.log (π / 8) ≤
        Real.log (Real.tanh (π * |x - chiQuantile c' a| / 2)) := by
      have hane_abs : 0 < |aStar - a| := abs_pos.mpr (sub_ne_zero.mpr hane.symm)
      have hpi8_pos : 0 < π / 8 := div_pos Real.pi_pos (by norm_num)
      have h_lin_pos : 0 < ℓ * |aStar - a| * (π / 8) := mul_pos (mul_pos hℓ_pos hane_abs) hpi8_pos
      have h_le : ℓ * |aStar - a| * (π / 8) ≤ Real.tanh (π * |x - chiQuantile c' a| / 2) := by
        have h1 : ℓ * |aStar - a| * (π / 8) = π * ((1 / 2 : ℝ) * ℓ * |aStar - a|) / 4 := by ring
        rw [h1]
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_dist_lb Real.pi_pos.le)
          (by norm_num)).trans h_t1_ge
      calc Real.log ℓ + Real.log |aStar - a| + Real.log (π / 8)
          = Real.log (ℓ * |aStar - a| * (π / 8)) := by
              rw [Real.log_mul (mul_pos hℓ_pos hane_abs).ne' hpi8_pos.ne',
                Real.log_mul hℓ_pos.ne' hane_abs.ne']
        _ ≤ Real.log (Real.tanh (π * |x - chiQuantile c' a| / 2)) := Real.log_le_log h_lin_pos h_le
    have hχa_xi : xiStar ≤ chiQuantile c' a := (chiQuantile_spec hc' ha14.le).1
    have hχn_xi : xiStar ≤ chiQuantile c' n := (chiQuantile_spec hc' (by linarith [hn14])).1
    have hx_xi : xiStar ≤ x := hχn_xi.trans hx.1
    have h_y2_ge : π * xiStar ≤ π * (x + chiQuantile c' a) / 2 := by
      have h1 : xiStar ≤ (x + chiQuantile c' a) / 2 := by linarith
      calc π * xiStar ≤ π * ((x + chiQuantile c' a) / 2) :=
          mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
        _ = π * (x + chiQuantile c' a) / 2 := by ring
    have hth_xi_pos : 0 < Real.tanh (π * xiStar) := tanh_pos_of_pos (mul_pos Real.pi_pos xiStar_pos)
    have h_lb2 : Real.log (Real.tanh (π * xiStar)) ≤ Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) :=
      Real.log_le_log hth_xi_pos (tanh_mono h_y2_ge)
    have hχa_nn : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans hχa_xi
    have hx_nn : 0 ≤ x := xiStar_pos.le.trans hx_xi
    have h_eq := realLogT_eq_log_tanh hx_nn hχa_nn hx_ne_a
    have ht1_p : 0 < Real.tanh (π * |x - chiQuantile c' a| / 2) := tanh_pos_of_pos h_y1_pos
    have ht2_p : 0 < Real.tanh (π * (x + chiQuantile c' a) / 2) := hth_xi_pos.trans_le (tanh_mono h_y2_ge)
    change _ ≤ realLogT x (chiQuantile c' a)
    rw [h_eq, Real.log_mul ht1_p.ne' ht2_p.ne']
    linarith
  have hint_phi : IntervalIntegrable (phiVar c' x) volume A B := by
    have hA14 : (1 / 4 : ℝ) < A := hn14
    have h_ioi := (riesz_real_identities hc' (xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith)).1.trans hx.1))
      1 le_rfl).2.1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mpr
      (h_ioi.mono (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (by linarith [hA14]))) le_rfl)
  have hint_log : IntervalIntegrable (fun a => Real.log |aStar - a|) volume A B := by
    have hi1 : IntervalIntegrable (fun a => Real.log |aStar - a|) volume A aStar := by
      have hlin : IntervalIntegrable (fun s : ℝ => Real.log s) volume 0 (aStar - A) :=
        intervalIntegral.intervalIntegrable_log'
      have hcomp : IntervalIntegrable (fun a => Real.log (aStar - a)) volume A aStar := by
        have h := (hlin.comp_sub_left aStar).symm
        simpa [sub_sub_cancel] using h
      refine hcomp.congr fun a ha => ?_
      rw [Set.uIoc_of_le hA_a] at ha
      rcases eq_or_lt_of_le ha.2 with rfl | hlt
      · simp
      · rw [abs_of_pos (sub_pos.mpr hlt)]
    have hi2 : IntervalIntegrable (fun a => Real.log |aStar - a|) volume aStar B := by
      have hlin : IntervalIntegrable (fun s : ℝ => Real.log s) volume 0 (B - aStar) :=
        intervalIntegral.intervalIntegrable_log'
      have hcomp : IntervalIntegrable (fun a => Real.log (a - aStar)) volume aStar B := by
        have h := hlin.comp_sub_right aStar
        simpa using h
      refine hcomp.congr fun a ha => ?_
      rw [Set.uIoc_of_le ha_B] at ha
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr ha.1)]
    exact hi1.trans hi2
  have hint_lb : IntervalIntegrable (fun a =>
      Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) volume A B :=
    ((intervalIntegrable_const.add hint_log).add intervalIntegrable_const).add intervalIntegrable_const
  have h_int_lb : ∫ a in A..B, (Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) ≤
      ∫ a in A..B, phiVar c' x a := by
    rw [intervalIntegral.integral_of_le hAB, intervalIntegral.integral_of_le hAB]
    refine MeasureTheory.setIntegral_mono_ae_restrict
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mp hint_lb)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mp hint_phi) ?_
    change ∀ᵐ a ∂volume.restrict (Ioc A B),
        Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8) ≤
          phiVar c' x a
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    have h_ae_ne : ∀ᵐ a ∂volume, a ≠ aStar := by rw [ae_iff]; simp
    filter_upwards [h_ae_ne] with a hane ha
    exact h_pt_lb a ⟨ha.1.le, ha.2⟩ hane
  have h_eval_lb : ∫ a in A..B, (Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) =
      2 * (Real.log ℓ + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) +
        ∫ a in A..B, Real.log |aStar - a| := by
    have heq_f : (fun a : ℝ => Real.log ℓ + Real.log |aStar - a| + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) =
        fun a : ℝ => (Real.log ℓ + Real.log (Real.tanh (π * xiStar)) + Real.log (π / 8)) + Real.log |aStar - a| := by
      ext a; ring
    rw [heq_f, intervalIntegral.integral_add intervalIntegrable_const hint_log,
      intervalIntegral.integral_const, smul_eq_mul]
    have hBA : B - A = 2 := by dsimp [A, B]; ring
    rw [hBA]
  have h_log_abs_ge : -2 ≤ ∫ a in A..B, Real.log |aStar - a| :=
    integral_log_abs_sub_ge hA_a ha_B
  have h_int2 : 4 * Real.log ℓ + 4 * Real.log (Real.tanh (π * xiStar)) + 4 * Real.log (π / 8) - 4 ≤
      2 * ∫ a in A..B, phiVar c' x a := by
    linarith [h_int_lb, h_eval_lb, h_log_abs_ge]
  unfold holeH
  have hsum_eq : ∑ m ∈ Finset.Icc (n - 1 + 1) (n + 1), Real.log (pairModQ c' η₀ x m) =
      Real.log (pairModQ c' η₀ x n) + Real.log (pairModQ c' η₀ x (n + 1)) := by
    have hset : Finset.Icc (n - 1 + 1) (n + 1) = {n, n + 1} := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hset, Finset.sum_pair (by omega)]
  have hAl : ((n : ℝ) - (1 : ℕ) + 1 / 2) = A := by dsimp [A]; push_cast; ring
  have hBr : ((n : ℝ) + (1 : ℕ) + 1 / 2) = B := by dsimp [B]; push_cast; ring
  rw [hsum_eq, hAl, hBr]
  have hqn := h_site_log n (Finset.mem_insert_self _ _)
  have hqn1 := h_site_log (n + 1) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  linarith

/-- **K6(a), band upper bound in multiplicative form (`cmb:K6`, `comb_estimates.tex`, line 246)**:
unconditional for all $\eta_0 \in [0, \frac14]$ and all $x$ in a cell $n \ge f + 2$,
with an absolute constant $C_+ > 0$. -/
theorem band_upper_K6a_mul :
    ∃ C_plus > 0, ∀ᶠ c' in atTop, ∀ (f n : ℕ) (η₀ x : ℝ),
      1 ≤ f → f + 2 ≤ n → 0 ≤ η₀ → η₀ ≤ 1 / 4 → inCell c' n x →
        ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
          Real.exp (c' * combPf c' f x + C_plus) := by
  obtain ⟨C_U, hCU_pos, hK4_ev⟩ := hole_upper_K4
  obtain ⟨C_gap, _, hgap_ev⟩ := siteGap_eventually_le
  let C_H : ℝ := 2 * Real.log 64 - 4 * Real.log (Real.tanh (π * xiStar)) - 4 * Real.log (π / 8) + 8
  let C_plus : ℝ := |C_H| + 11 / 6 + C_U + 1
  have hCp_pos : 0 < C_plus := by dsimp [C_plus]; positivity
  refine ⟨C_plus, hCp_pos, ?_⟩
  have h_gap_small_ev : ∀ᶠ c' in atTop, C_gap * lambdaComb c' ≤ 1 / (16 * π) := by
    have hmul := tendsto_lambdaComb_zero.const_mul C_gap
    rw [mul_zero] at hmul
    exact hmul.eventually (eventually_le_nhds (div_pos one_pos (mul_pos (by norm_num) Real.pi_pos)))
  filter_upwards [hK4_ev, hgap_ev, h_gap_small_ev, eventually_gt_atTop (0 : ℝ)] with
    c' hK4 hgap_c hsmall hc'
  have hgap16 : siteGap c' 1 ≤ 1 / (16 * π) := hgap_c.2.1.trans (hgap_c.2.2.1.trans hsmall)
  intro f n η₀ x hf hfn2 hη₀0 hη₀1 hx
  by_cases hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n
  · have hn_max : max (f + 1) (2 * 1 + 1) ≤ n := by omega
    have hK4_bnd := hK4 f n 1 η₀ x hf le_rfl hn_max hη₀0 hη₀1 hx
    have hj_bd : jEndComb c' x f ≤ 11 / 6 := by
      have hf_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
      have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
      have hfn2_r : (f : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hfn2
      have hχ_f2_gt : chiQuantile c' ((f : ℝ) + 1 / 2) < x :=
        (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr (by linarith)) (by linarith)).trans_le hx.1
      have hj := (jEndComb_bounds hc' hf hχ_f2_gt).2
      have h_x_gap : siteGap c' (f + 1) ≤ x - chiQuantile c' ((f : ℝ) + 1 / 2) := by
        have hfn2_nat : ((f + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfn2
        have hf2_le : chiQuantile c' ((f + 2 : ℕ) : ℝ) ≤ x :=
          ((chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr (by push_cast; linarith))
            (Set.mem_Ici.mpr (by linarith)) hfn2_nat).trans hx.1
        have h_f12_le : chiQuantile c' ((f : ℝ) + 1 / 2) ≤ chiQuantile c' ((f + 1 : ℕ) : ℝ) :=
          (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr (by linarith))
            (Set.mem_Ici.mpr (by push_cast; linarith)) (by push_cast; linarith)
        unfold siteGap
        have h_eq1 : chiQuantile c' (((f + 1 : ℕ) : ℝ) + 1) = chiQuantile c' ((f + 2 : ℕ) : ℝ) := by
          congr 1; push_cast; ring
        rw [h_eq1]
        linarith
      have h_gf_le : siteGap c' f ≤ (11 / 3 : ℝ) * siteGap c' (f + 1) := by
        have h_gf : siteGap c' f ≤ chiDeriv c' (f : ℝ) := siteGap_le_chiDeriv hc' hf
        have h_gf1 : chiDeriv c' ((f : ℝ) + 2) ≤ siteGap c' (f + 1) := by
          have h := siteGap_ge_chiDeriv hc' (show 1 ≤ f + 1 by omega)
          convert h using 2; push_cast; ring
        have h_div := chiDeriv_div_le hc' hf14 (by linarith : (f : ℝ) ≤ (f : ℝ) + 2)
        have h_frac : ((f : ℝ) + 2 - 1 / 4) / ((f : ℝ) - 1 / 4) ≤ 11 / 3 := by
          rw [div_le_iff₀ (by linarith)]; linarith [hf_r]
        have hden : 0 < chiDeriv c' ((f : ℝ) + 2) := chiDeriv_pos hc' (by linarith)
        have h_cd : chiDeriv c' (f : ℝ) ≤ (11 / 3 : ℝ) * chiDeriv c' ((f : ℝ) + 2) :=
          (div_le_iff₀ hden).mp (h_div.trans h_frac)
        calc siteGap c' f ≤ chiDeriv c' (f : ℝ) := h_gf
          _ ≤ (11 / 3 : ℝ) * chiDeriv c' ((f : ℝ) + 2) := h_cd
          _ ≤ (11 / 3 : ℝ) * siteGap c' (f + 1) := mul_le_mul_of_nonneg_left h_gf1 (by norm_num)
      have h_gf1_pos : 0 < siteGap c' (f + 1) := by
        have h := siteGap_ge_chiDeriv hc' (show 1 ≤ f + 1 by omega)
        exact (chiDeriv_pos hc' (by push_cast; linarith)).trans_le h
      calc jEndComb c' x f
          ≤ 1 / 2 * siteGap c' f / (x - chiQuantile c' ((f : ℝ) + 1 / 2)) := hj
        _ ≤ 1 / 2 * ((11 / 3 : ℝ) * siteGap c' (f + 1)) / siteGap c' (f + 1) :=
            div_le_div₀ (by positivity) (by gcongr) h_gf1_pos h_x_gap
        _ = 11 / 6 := by field_simp [h_gf1_pos.ne']; ring
    have hh_bd : holeH c' η₀ n 1 x ≤ C_H :=
      holeH_one_le_K6a hc' hη₀0 hη₀1 (by omega) hx hgap16 hnz
    have h_exp_le : c' * combPf c' f x + holeH c' η₀ n 1 x + jEndComb c' x f + C_U ≤
        c' * combPf c' f x + C_plus := by
      have hch : C_H ≤ |C_H| := le_abs_self _
      dsimp [C_plus]; linarith
    exact hK4_bnd.trans (Real.exp_le_exp.mpr h_exp_le)
  · have h_eq : η₀ = 0 ∧ x = chiQuantile c' n := by
      push Not at hnz
      exact ⟨le_antisymm hnz.1 hη₀0, hnz.2⟩
    rw [h_eq.1, h_eq.2, refComb_eq_zero_of_zero_at_site hc' hf (by omega), norm_zero, zero_mul]
    exact (Real.exp_pos _).le

/-- **K6(a), logarithmic band upper bound (`cmb:K6`, `comb_estimates.tex`, line 246)**:
away from `(η₀ = 0 ∧ x = χ_n)`,
$\log|B^{(f)}(x)| + c' L(x) \le c' P^{(f)}(x) + C_+$. -/
theorem band_upper_K6a :
    ∃ C_plus > 0, ∀ᶠ c' in atTop, ∀ (f n : ℕ) (η₀ x : ℝ),
      1 ≤ f → f + 2 ≤ n → 0 ≤ η₀ → η₀ ≤ 1 / 4 → inCell c' n x →
        (0 < η₀ ∨ x ≠ chiQuantile c' n) →
          Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x ≤
            c' * combPf c' f x + C_plus := by
  obtain ⟨C_plus, hCp_pos, h_mul_ev⟩ := band_upper_K6a_mul
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨C_plus, hCp_pos, ?_⟩
  filter_upwards [h_mul_ev, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' h_mul hgap_c hc'
  have hgap1 : siteGap c' 1 ≤ 1 / 2 := hgap_c.2.2.2
  intro f n η₀ x hf hfn2 hη₀0 hη₀1 hx hnz
  have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hf1_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hχn_nn : 0 ≤ chiQuantile c' n :=
    xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hx0 : 0 ≤ x := hχn_nn.trans hx.1
  have hf_ne : chiQuantile c' f ≠ x := by
    have hfn_r : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
    have hlt : chiQuantile c' f < chiQuantile c' n :=
      chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hfn_r
    exact (hlt.trans_le hx.1).ne
  have hq_all : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m) := fun m => by
    by_cases hkn : f + 1 + m = n
    · rw [hkn]; exact pairModQ_pos hc' hη₀0 hη₀1 hgap1 (by omega) hx hnz
    · have hk1 : 1 ≤ f + 1 + m := by omega
      have hk14 : (1 / 4 : ℝ) < ((f + 1 + m : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast hk1
        linarith
      have hx_ne_k : x ≠ chiQuantile c' (f + 1 + m : ℕ) := by
        rcases lt_or_gt_of_ne hkn with hlt | hgt
        · have h_mono : chiQuantile c' (f + 1 + m : ℕ) < chiQuantile c' n :=
            chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hk14.le)
              (Set.mem_Ici.mpr (by linarith)) (by exact_mod_cast hlt)
          exact (h_mono.trans_le hx.1).ne'
        · have hn1_le : n + 1 ≤ f + 1 + m := by omega
          have h_mono : chiQuantile c' (n + 1 : ℕ) ≤ chiQuantile c' (f + 1 + m : ℕ) :=
            (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr (by push_cast; linarith))
              (Set.mem_Ici.mpr hk14.le) (by exact_mod_cast hn1_le)
          exact (hx.2.trans_le h_mono).ne
      unfold pairModQ
      rw [blaschkePairQ_eq]
      have hgk_nn : 0 ≤ siteGap c' (f + 1 + m) := by
        unfold siteGap
        exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
          (Set.mem_Ici.mpr hk14.le) (Set.mem_Ici.mpr (by push_cast; linarith))
          (by push_cast; linarith))
      have hgk_le : siteGap c' (f + 1 + m) ≤ siteGap c' 1 := by
        have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ f + 1 + m - 1 by omega)
        convert hanti using 2; omega
      have hβ_le : π * (η₀ * siteGap c' (f + 1 + m)) / 2 ≤ π / 16 := by
        have h1 : η₀ * siteGap c' (f + 1 + m) ≤ 1 / 8 := by nlinarith [hη₀1, hgap1, hgk_le]
        linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le) two_pos.le]
      have h_S_le : Real.sin (π * (η₀ * siteGap c' (f + 1 + m)) / 2) ^ 2 ≤ 1 / 2 := by
        have hβ_nn : 0 ≤ π * (η₀ * siteGap c' (f + 1 + m)) / 2 :=
          div_nonneg (mul_nonneg Real.pi_pos.le (mul_nonneg hη₀0 hgk_nn)) two_pos.le
        have hab : |Real.sin (π * (η₀ * siteGap c' (f + 1 + m)) / 2)| ≤ π / 16 :=
          Real.abs_sin_le_abs.trans ((abs_of_nonneg hβ_nn).le.trans hβ_le)
        have hpi4 : π / 16 ≤ 1 / 4 := by linarith [Real.pi_lt_d4]
        have hsq : Real.sin (π * (η₀ * siteGap c' (f + 1 + m)) / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hab.trans hpi4) 2
        linarith
      have hχk_pos : 0 < chiQuantile c' (f + 1 + m : ℕ) :=
        xiStar_pos.trans (xiStar_lt_chiQuantile hc' hk14)
      have hsh1 : Real.sinh (π * (x - chiQuantile c' (f + 1 + m : ℕ)) / 2) ≠ 0 :=
        Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hx_ne_k)) two_ne_zero)
      have hsh2 : Real.sinh (π * (x + chiQuantile c' (f + 1 + m : ℕ)) / 2) ≠ 0 :=
        Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith)) two_ne_zero)
      have hden1 : 0 < Real.cosh (π * (x - chiQuantile c' (f + 1 + m : ℕ)) / 2) ^ 2 -
          Real.sin (π * (η₀ * siteGap c' (f + 1 + m)) / 2) ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x - chiQuantile c' (f + 1 + m : ℕ)) / 2))]
      have hden2 : 0 < Real.cosh (π * (x + chiQuantile c' (f + 1 + m : ℕ)) / 2) ^ 2 -
          Real.sin (π * (η₀ * siteGap c' (f + 1 + m)) / 2) ^ 2 := by
        linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x + chiQuantile c' (f + 1 + m : ℕ)) / 2))]
      exact mul_pos (div_pos (by positivity) hden1) (div_pos (by positivity) hden2)
  have href_pos := refComb_norm_pos_of_ne_site hc' hx0 hf hη₀0 hη₀1 hgap1 hf_ne hq_all
  have hmul := h_mul f n η₀ x hf hfn2 hη₀0 hη₀1 hx
  have hlog := Real.log_le_log (mul_pos href_pos (Real.exp_pos _)) hmul
  rw [Real.log_mul href_pos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hlog
  exact hlog

private lemma exists_inCell_of_ge {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : chiQuantile c' (k : ℝ) ≤ x) :
    ∃ n : ℕ, k ≤ n ∧ inCell c' n x := by
  have htend : Tendsto (fun m : ℕ => chiQuantile c' (m : ℝ)) atTop atTop :=
    (tendsto_chiQuantile_atTop hc').comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := (tendsto_atTop_atTop.mp htend) (x + 1)
  have hhi : x < chiQuantile c' ((max k M : ℕ) : ℝ) := by linarith [hM (max k M) (le_max_right _ _)]
  have hex : ∃ m : ℕ, k ≤ m ∧ x < chiQuantile c' (m : ℝ) := ⟨max k M, le_max_left _ _, hhi⟩
  classical
  let m₀ := Nat.find hex
  have hm₀_spec := Nat.find_spec hex
  have hk_lt_m₀ : k < m₀ := by
    rcases eq_or_lt_of_le hm₀_spec.1 with heq | hlt
    · exfalso; rw [← heq] at hm₀_spec; linarith [hm₀_spec.2, hx]
    · exact hlt
  let n := m₀ - 1
  have hn_k : k ≤ n := by omega
  have hm₀_eq : m₀ = n + 1 := by omega
  have hxn : chiQuantile c' (n : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have hn_lt : n < m₀ := by omega
    exact absurd ⟨hn_k, hlt⟩ (Nat.find_min hex hn_lt)
  refine ⟨n, hn_k, hxn, ?_⟩
  have hcast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' (m₀ : ℝ) := by rw [hm₀_eq]
  rw [hcast]
  exact hm₀_spec.2

private lemma neg_realLogT_antitoneOn {z : ℝ} (hz : 0 ≤ z) :
    AntitoneOn (fun y => -realLogT y z) (Ioi z) := by
  have heq : ∀ y ∈ Ioi z, -realLogT y z = -realLogT z y := fun y hy => by
    have hy0 : 0 ≤ y := hz.trans hy.le
    rw [realLogT_eq_log_tanh hy0 hz hy.ne, realLogT_eq_log_tanh hz hy0 hy.ne']
    rw [abs_sub_comm y z, add_comm y z]
  have hanti : AntitoneOn (fun y => -realLogT z y) (Ioi z) :=
    antitoneOn_of_deriv_nonpos (convex_Ioi z)
      (fun y hy => ((realLogT_hasDerivAt hz (hz.trans_lt hy).le hy.ne').1.neg.continuousAt.continuousWithinAt))
      (fun y hy => by
        rw [interior_Ioi] at hy
        exact (realLogT_hasDerivAt hz (hz.trans_lt hy).le hy.ne').1.neg.differentiableAt.differentiableWithinAt)
      fun y hy => by
        rw [interior_Ioi] at hy
        have hd : HasDerivAt (fun t => -realLogT z t) (-realLogTDeriv z y) y :=
          (realLogT_hasDerivAt hz (hz.trans_lt hy).le hy.ne').1.neg
        rw [hd.deriv]
        have hpos := ((realLogT_deriv_bounds hz (hz.trans_lt hy).le hy.ne').2.2 hy).1
        linarith
  intro a ha b hb hab
  dsimp only
  rw [heq a ha, heq b hb]
  exact hanti ha hb hab

/-- **K6(a), first consequence (`cmb:K6`, `comb_estimates.tex`, line 248)**:
for fixed `f ≥ 1`, `η₀ ∈ [0, 1/4]`, and `r₀ > 0`, for large `c'` one has
$|B^{(f)}(x)| e^{c' L(x)} \le C(f, r_0)$ uniformly on $x \ge \xi_* + r_0$. -/
theorem band_upper_K6a_r0 {f : ℕ} (hf : 1 ≤ f) {η₀ r₀ : ℝ}
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hr₀ : 0 < r₀) :
    ∃ C_r > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤ C_r := by
  obtain ⟨C_plus, hCp_pos, h_mul_ev⟩ := band_upper_K6a_mul
  have ht1 : 0 < Real.tanh (π * (r₀ / 2) / 2) :=
    tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (half_pos hr₀)) two_pos)
  have ht2 : 0 < Real.tanh (π * (2 * xiStar + r₀) / 2) :=
    tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (by linarith [xiStar_pos, hr₀])) two_pos)
  let M_T : ℝ := -(Real.log (Real.tanh (π * (r₀ / 2) / 2)) + Real.log (Real.tanh (π * (2 * xiStar + r₀) / 2)))
  let C_r : ℝ := Real.exp (2 * n1Comb f * max M_T 0 + C_plus)
  refine ⟨C_r, Real.exp_pos _, ?_⟩
  have hχ_ev : ∀ᶠ c' in atTop, chiQuantile c' ((f + 2 : ℕ) : ℝ) ≤ xiStar + r₀ / 2 := by
    have hmul := tendsto_lambdaComb_zero.const_mul (phiQuantile ((f + 2 : ℕ) : ℝ))
    rw [mul_zero] at hmul
    have hev := hmul.eventually (eventually_le_nhds (half_pos hr₀))
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with c' hlc hc'
    have hf2_ge : (1 / 4 : ℝ) ≤ ((f + 2 : ℕ) : ℝ) := by
      have : (3 : ℝ) ≤ ((f + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ f + 2)
      linarith
    have hsr := (siteRadius_bounds hc' hf2_ge).2
    unfold siteRadius at hsr
    linarith [hlc]
  filter_upwards [h_mul_ev, hχ_ev, eventually_gt_atTop (0 : ℝ)] with c' h_mul hχ2 hc'
  intro x hx
  have h_le_x : chiQuantile c' ((f + 2 : ℕ) : ℝ) ≤ x := by linarith
  obtain ⟨n, hfn2, hx_cell⟩ := exists_inCell_of_ge hc' (show 1 ≤ f + 2 by omega) h_le_x
  have h_k6 := h_mul f n η₀ x hf hfn2 hη₀0 hη₀1 hx_cell
  have hf_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
  have hχf_le : chiQuantile c' (f : ℝ) ≤ chiQuantile c' ((f + 2 : ℕ) : ℝ) :=
    (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr hf14.le)
      (Set.mem_Ici.mpr (by push_cast; linarith)) (by push_cast; linarith)
  have hχf_lt : chiQuantile c' (f : ℝ) < x := by linarith [hχf_le, hχ2, hr₀]
  have hpf := (combPf_bounds_K4 hc' hf hχf_lt).2.1
  have hχf_xi : xiStar ≤ chiQuantile c' (f : ℝ) := (chiQuantile_spec hc' hf14.le).1
  have hx_nn : 0 ≤ x := xiStar_pos.le.trans (by linarith)
  have h_logT_bd : -realLogT x (chiQuantile c' (f : ℝ)) ≤ M_T := by
    have h_eq := realLogT_eq_log_tanh hx_nn (xiStar_pos.le.trans hχf_xi) hχf_lt.ne
    have hdx : r₀ / 2 ≤ |x - chiQuantile c' (f : ℝ)| := by
      rw [abs_of_pos (sub_pos.mpr hχf_lt)]; linarith [hχf_le, hχ2]
    have hsx : 2 * xiStar + r₀ ≤ x + chiQuantile c' (f : ℝ) := by linarith [hχf_xi, hx]
    have hth1_le : Real.tanh (π * (r₀ / 2) / 2) ≤ Real.tanh (π * |x - chiQuantile c' (f : ℝ)| / 2) :=
      tanh_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdx Real.pi_pos.le) two_pos.le)
    have hth2_le : Real.tanh (π * (2 * xiStar + r₀) / 2) ≤ Real.tanh (π * (x + chiQuantile c' (f : ℝ)) / 2) :=
      tanh_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsx Real.pi_pos.le) two_pos.le)
    have ht1_p : 0 < Real.tanh (π * |x - chiQuantile c' (f : ℝ)| / 2) := ht1.trans_le hth1_le
    have ht2_p : 0 < Real.tanh (π * (x + chiQuantile c' (f : ℝ)) / 2) := ht2.trans_le hth2_le
    rw [h_eq, Real.log_mul ht1_p.ne' ht2_p.ne']
    have hl1 : Real.log (Real.tanh (π * (r₀ / 2) / 2)) ≤ Real.log (Real.tanh (π * |x - chiQuantile c' (f : ℝ)| / 2)) :=
      Real.log_le_log ht1 hth1_le
    have hl2 : Real.log (Real.tanh (π * (2 * xiStar + r₀) / 2)) ≤ Real.log (Real.tanh (π * (x + chiQuantile c' (f : ℝ)) / 2)) :=
      Real.log_le_log ht2 hth2_le
    dsimp [M_T]; linarith
  have hn1_nn : 0 ≤ 2 * n1Comb f := by
    unfold n1Comb; linarith
  have hpf_le : c' * combPf c' f x + C_plus ≤ 2 * n1Comb f * max M_T 0 + C_plus :=
    add_le_add (hpf.trans (mul_le_mul_of_nonneg_left (h_logT_bd.trans (le_max_left _ _)) hn1_nn)) le_rfl
  exact h_k6.trans (Real.exp_le_exp.mpr hpf_le)

/-- **K6(a), second consequence (`cmb:K6`, `comb_estimates.tex`, line 248)**:
for fixed `f ≥ 1`, `η₀ ∈ [0, 1/4]`, and fixed large `c'`,
$\sup_{x \ge 0} |B^{(f)}(x)| e^{c' L(x)} < \infty$. -/
theorem band_upper_K6a_bdd {f : ℕ} (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∃ M > 0, ∀ x : ℝ, 0 ≤ x →
      ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤ M := by
  obtain ⟨C_plus, _, h_mul_ev⟩ := band_upper_K6a_mul
  have hk1a := refComb_K1a f hf hη₀0 hη₀1
  filter_upwards [h_mul_ev, hk1a, eventually_gt_atTop (0 : ℝ)] with c' h_mul hk1a_c hc'
  let χ₂ : ℝ := chiQuantile c' ((f + 2 : ℕ) : ℝ)
  have hf_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
  have hχf_lt_χ2 : chiQuantile c' (f : ℝ) < χ₂ :=
    chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hf14.le)
      (Set.mem_Ici.mpr (by push_cast; linarith)) (by push_cast; linarith)
  have hχf_nn : 0 ≤ chiQuantile c' (f : ℝ) := xiStar_pos.le.trans (chiQuantile_spec hc' hf14.le).1
  let M : ℝ := max (Real.exp (c' * slitL χ₂))
    (Real.exp (2 * n1Comb f * (-realLogT χ₂ (chiQuantile c' (f : ℝ))) + C_plus))
  refine ⟨M, lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _), fun x hx0 => ?_⟩
  rcases le_or_gt x χ₂ with hx_le | hx_gt
  · have href1 : ‖refComb c' f η₀ (x : ℂ)‖ ≤ 1 := hk1a_c.1 (by simp)
    have hL_le : slitL x ≤ slitL χ₂ := by
      unfold slitL
      have hχ2_nn : 0 ≤ χ₂ := hχf_nn.trans hχf_lt_χ2.le
      rw [abs_of_nonneg hx0, abs_of_nonneg hχ2_nn]
      gcongr
    have hexp_le : Real.exp (c' * slitL x) ≤ Real.exp (c' * slitL χ₂) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL_le hc'.le)
    calc ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x)
        ≤ 1 * Real.exp (c' * slitL χ₂) := mul_le_mul href1 hexp_le (Real.exp_pos _).le zero_le_one
      _ = Real.exp (c' * slitL χ₂) := one_mul _
      _ ≤ M := le_max_left _ _
  · obtain ⟨n, hfn2, hx_cell⟩ := exists_inCell_of_ge hc' (show 1 ≤ f + 2 by omega) hx_gt.le
    have h_k6 := h_mul f n η₀ x hf hfn2 hη₀0 hη₀1 hx_cell
    have hχf_lt_x : chiQuantile c' (f : ℝ) < x := hχf_lt_χ2.trans hx_gt
    have hpf := (combPf_bounds_K4 hc' hf hχf_lt_x).2.1
    have h_anti := neg_realLogT_antitoneOn hχf_nn
      (Set.mem_Ioi.mpr hχf_lt_χ2) (Set.mem_Ioi.mpr hχf_lt_x) hx_gt.le
    have hn1_nn : 0 ≤ 2 * n1Comb f := by
      unfold n1Comb; linarith
    have h_arg : c' * combPf c' f x + C_plus ≤
        2 * n1Comb f * (-realLogT χ₂ (chiQuantile c' (f : ℝ))) + C_plus :=
      add_le_add (hpf.trans (mul_le_mul_of_nonneg_left h_anti hn1_nn)) le_rfl
    exact h_k6.trans ((Real.exp_le_exp.mpr h_arg).trans (le_max_right _ _))

/-! ### Section 3: K6(b) Lobe upper bound (`cmb:K6`, `comb_estimates.tex`, lines 250–257) -/

private lemma log_pairModQ_eq_phiVar_add_detune {c' η₀ x : ℝ} (hc' : 0 < c') (hx0 : 0 ≤ x)
    {k : ℕ} (hk : 1 ≤ k) (hne : x ≠ chiQuantile c' k)
    (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2) :
    Real.log (pairModQ c' η₀ x k) =
      2 * phiVar c' x k + deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x := by
  have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by linarith
  have hχk_pos : 0 < chiQuantile c' k := xiStar_pos.trans (xiStar_lt_chiQuantile hc' hk14)
  have hth1_ne : Real.tanh (π * (x - chiQuantile c' k) / 2) ≠ 0 :=
    tanh_ne_zero (div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hne)) two_ne_zero)
  have hth2_pos : 0 < Real.tanh (π * (x + chiQuantile c' k) / 2) :=
    tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (by linarith)) two_pos)
  have hden_pos' : 0 < (Real.tanh (π * (x - chiQuantile c' k) / 2) *
      Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2 :=
    sq_pos_iff.mpr (mul_ne_zero hth1_ne hth2_pos.ne')
  have hq_pos : 0 < pairModQ c' η₀ x k := by
    unfold pairModQ
    rw [blaschkePairQ_eq]
    have hgk_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr hk14.le) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      convert hanti using 2; omega
    have hβ_le : π * (η₀ * siteGap c' k) / 2 ≤ π / 16 := by
      have h1 : η₀ * siteGap c' k ≤ 1 / 8 := by nlinarith [hη₀1, hgap, hgk_le]
      linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le) two_pos.le]
    have h_S_le : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ 1 / 2 := by
      have hβ_nn : 0 ≤ π * (η₀ * siteGap c' k) / 2 :=
        div_nonneg (mul_nonneg Real.pi_pos.le (mul_nonneg hη₀0 hgk_nn)) two_pos.le
      have hab : |Real.sin (π * (η₀ * siteGap c' k) / 2)| ≤ π / 16 :=
        Real.abs_sin_le_abs.trans ((abs_of_nonneg hβ_nn).le.trans hβ_le)
      have hpi4 : π / 16 ≤ 1 / 4 := by linarith [Real.pi_lt_d4]
      have hsq : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hab.trans hpi4) 2
      linarith
    have hsh1 : Real.sinh (π * (x - chiQuantile c' k) / 2) ≠ 0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hne)) two_ne_zero)
    have hsh2 : Real.sinh (π * (x + chiQuantile c' k) / 2) ≠ 0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith)) two_ne_zero)
    have hden1 : 0 < Real.cosh (π * (x - chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x - chiQuantile c' k) / 2))]
    have hden2 : 0 < Real.cosh (π * (x + chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x + chiQuantile c' k) / 2))]
    exact mul_pos (div_pos (by positivity) hden1) (div_pos (by positivity) hden2)
  have hphi_eq : phiVar c' x k = Real.log (|Real.tanh (π * (x - chiQuantile c' k) / 2)| *
      Real.tanh (π * (x + chiQuantile c' k) / 2)) := by
    change realLogT x (chiQuantile c' k) = _
    rw [realLogT_eq_log_tanh hx0 hχk_pos.le hne.symm]
    congr 2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt),
        show π * (x - chiQuantile c' k) / 2 = -(π * (chiQuantile c' k - x) / 2) by ring,
        Real.tanh_neg, abs_neg,
        abs_of_pos (tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (sub_pos.mpr hlt)) two_pos))]
    · rw [abs_of_pos (sub_pos.mpr hgt),
        abs_of_pos (tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (sub_pos.mpr hgt)) two_pos))]
  have hsq_eq : (|Real.tanh (π * (x - chiQuantile c' k) / 2)| *
      Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2 =
      (Real.tanh (π * (x - chiQuantile c' k) / 2) *
        Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  unfold deltaDetune pairModQ at hq_pos ⊢
  rw [Real.log_div hq_pos.ne' hden_pos'.ne', hphi_eq, ← hsq_eq, Real.log_pow]
  push_cast; ring

private lemma inv_k_sub_quarter_sq_Icc_le (K : ℕ) (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / (((k : ℝ) - 1 / 4) ^ 2) ≤ 1 := by
  calc ∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / (((k : ℝ) - 1 / 4) ^ 2)
      ≤ ∑ k ∈ Finset.Icc 2 K, ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        have h1 : (0 : ℝ) < ((k : ℝ) - 1) * (k : ℝ) := mul_pos (by linarith) (by linarith)
        have h2 : ((k : ℝ) - 1) * (k : ℝ) ≤ ((k : ℝ) - 1 / 4) ^ 2 := by nlinarith
        have h_eq : (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) = (1 : ℝ) / (((k : ℝ) - 1) * (k : ℝ)) := by
          field_simp [(by linarith : (k : ℝ) - 1 ≠ 0), (by linarith : (k : ℝ) ≠ 0)]; ring
        rw [h_eq]
        exact div_le_div_of_nonneg_left zero_le_one h1 h2
    _ = (1 : ℝ) - 1 / (K : ℝ) := by
        induction K, hK using Nat.le_induction with
        | base => simp; norm_num
        | succ m hm ih =>
          have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
            ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
          push_cast; ring
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
        linarith

private lemma exp_neg_pi_siteRadius_sum_le {c' : ℝ} (hc' : 0 < c') (K : ℕ) (hK : 2 ≤ K) :
    ∑ k ∈ Finset.Icc 2 K, chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) ≤ 1 / π := by
  have h1K : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hcont_g' : ContinuousOn (fun t => chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)))
      (Icc (1 : ℝ) (K : ℝ)) := fun t ht =>
    ((hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.mul
      (Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul ((hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1.continuousAt.sub
          continuousAt_const)))).continuousWithinAt
  have h_term : ∀ k ∈ Finset.Icc 2 K,
      chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) ≤
        ∫ t in ((k : ℝ) - 1)..(k : ℝ),
          chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkKr : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
    have hlen1 : chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) =
        ∫ _t in ((k : ℝ) - 1)..(k : ℝ),
          chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel, one_mul]
    rw [hlen1]
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((hcont_g'.mono (Icc_subset_Icc (by linarith) hkKr)).intervalIntegrable_of_Icc
        (by linarith)) fun t ht => ?_
    have ht14 : (1 / 4 : ℝ) < t := by linarith [ht.1]
    have hcd : chiDeriv c' (k : ℝ) ≤ chiDeriv c' t := chiDeriv_antitone hc' ht14 ht.2
    have hχ : chiQuantile c' t ≤ chiQuantile c' (k : ℝ) :=
      (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr ht14.le)
        (Set.mem_Ici.mpr (by linarith)) ht.2
    have hexp : Real.exp (-π * siteRadius c' (k : ℝ)) ≤ Real.exp (-π * (chiQuantile c' t - xiStar)) := by
      unfold siteRadius
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr Real.pi_pos.le))
    exact mul_le_mul hcd hexp (Real.exp_pos _).le (chiDeriv_pos hc' ht14).le
  have h_sum_int :
      ∑ k ∈ Finset.Icc 2 K,
          ∫ t in ((k : ℝ) - 1)..(k : ℝ),
            chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)) =
        ∫ t in (1 : ℝ)..(K : ℝ),
          chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)) := by
    clear h1K hcont_g' h_term
    induction K, hK using Nat.le_induction with
    | base =>
      simp only [Nat.cast_ofNat, Finset.Icc_self, Finset.sum_singleton]
      rw [show (2 : ℝ) - 1 = 1 by norm_num]
    | succ m hm ih =>
      have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
      have hcont_succ : ContinuousOn (fun t => chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)))
          (Icc (1 : ℝ) ((m + 1 : ℕ) : ℝ)) := fun t ht =>
        ((hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.mul
          (Real.continuous_exp.continuousAt.comp
            (continuousAt_const.mul ((hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1.continuousAt.sub
              continuousAt_const)))).continuousWithinAt
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have hi1 : IntervalIntegrable (fun t => chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)))
          volume 1 (m : ℝ) :=
        (hcont_succ.mono (Icc_subset_Icc_right (by push_cast; linarith))).intervalIntegrable_of_Icc hm1
      have hi2 : IntervalIntegrable (fun t => chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)))
          volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
        (hcont_succ.mono (Icc_subset_Icc_left hm1)).intervalIntegrable_of_Icc (by push_cast; linarith)
      have heq_m : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by push_cast; ring
      rw [add_comm, heq_m]
      exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h_eval : ∫ t in (1 : ℝ)..(K : ℝ),
      chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)) =
      (-(1 / π)) * Real.exp (-π * (chiQuantile c' (K : ℝ) - xiStar)) -
        ((-(1 / π)) * Real.exp (-π * (chiQuantile c' (1 : ℝ) - xiStar))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => (-(1 / π)) * Real.exp (-π * (chiQuantile c' s - xiStar)))
      (fun t ht => ?_) (hcont_g'.intervalIntegrable_of_Icc h1K)
    rw [Set.uIcc_of_le h1K] at ht
    have ht14 : (1 / 4 : ℝ) < t := by linarith [ht.1]
    have hd_chi := (hasDerivAt_chiQuantile hc' ht14).1
    have hd_arg : HasDerivAt (fun s => -π * (chiQuantile c' s - xiStar)) (-π * chiDeriv c' t) t := by
      simpa using (hd_chi.sub_const xiStar).const_mul (-π)
    have hd_exp : HasDerivAt (fun s => (-(1 / π)) * Real.exp (-π * (chiQuantile c' s - xiStar)))
        ((-(1 / π)) * (Real.exp (-π * (chiQuantile c' t - xiStar)) * (-π * chiDeriv c' t))) t :=
      (hd_arg.exp).const_mul (-(1 / π))
    refine hd_exp.congr_deriv ?_
    field_simp [Real.pi_ne_zero]
  calc ∑ k ∈ Finset.Icc 2 K, chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))
      ≤ ∑ k ∈ Finset.Icc 2 K,
          ∫ t in ((k : ℝ) - 1)..(k : ℝ),
            chiDeriv c' t * Real.exp (-π * (chiQuantile c' t - xiStar)) :=
        Finset.sum_le_sum h_term
    _ = -(1 / π) * Real.exp (-π * (chiQuantile c' (K : ℝ) - xiStar)) +
          (1 / π) * Real.exp (-π * (chiQuantile c' (1 : ℝ) - xiStar)) := by
        rw [h_sum_int, h_eval]; ring
    _ ≤ 0 + (1 / π) * 1 := by
        refine add_le_add ?_ ?_
        · have : 0 ≤ (1 / π) * Real.exp (-π * (chiQuantile c' (K : ℝ) - xiStar)) := by
            positivity [Real.pi_pos]
          linarith
        · have h1_xi : 0 ≤ chiQuantile c' (1 : ℝ) - xiStar :=
            sub_nonneg.mpr (chiQuantile_spec hc' (by norm_num)).1
          have hexp1 : Real.exp (-π * (chiQuantile c' (1 : ℝ) - xiStar)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) h1_xi)
          exact mul_le_mul_of_nonneg_left hexp1 (by positivity [Real.pi_pos])
    _ = 1 / π := by ring

/-- **K6(b), lobe upper bound (`cmb:K6`, `comb_estimates.tex`, line 252)**:
for all `f ≥ 1`, `η₀ ∈ [0, 1/4]`, and real `x ∈ [0, ξ_*]`,
$\log |B^{(f)}(x)| + c' L(x) \le c' P^{(f)}(x) + c' (U + L)(x) + C_-$,
with an absolute constant $C_- > 0$. -/
theorem lobe_upper_K6b :
    ∃ C_minus > 0, ∀ᶠ c' in atTop, ∀ (f : ℕ) (η₀ x : ℝ),
      1 ≤ f → 0 ≤ η₀ → η₀ ≤ 1 / 4 → x ∈ Icc 0 xiStar →
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x ≤
          c' * combPf c' f x + c' * (majorantReal x + slitL x) + C_minus := by
  obtain ⟨C_δ, hCδ_pos, h_det⟩ := deltaDetune_le_of_xiStar_le
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  let C_minus : ℝ := 1 / 16 + C_δ / (32 * π) + 1
  have hCm_pos : 0 < C_minus := by dsimp [C_minus]; positivity [Real.pi_pos]
  refine ⟨C_minus, hCm_pos, ?_⟩
  filter_upwards [hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' hgap_c hc'
  have hgap1 : siteGap c' 1 ≤ 1 / 2 := hgap_c.2.2.2
  intro f η₀ x hf hη₀0 hη₀1 hx
  have hf_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
  have h_gt_all : ∀ a : ℝ, (f : ℝ) ≤ a → x < chiQuantile c' a := fun a ha =>
    hx.2.trans_lt (xiStar_lt_chiQuantile hc' (hf14.trans_le ha))
  have hf_ne : chiQuantile c' f ≠ x := (h_gt_all f le_rfl).ne'
  have h_q_pos : ∀ k : ℕ, 1 ≤ k → 0 < pairModQ c' η₀ x k := fun k hk => by
    have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by linarith
    have hχk_gt : x < chiQuantile c' k := hx.2.trans_lt (xiStar_lt_chiQuantile hc' hk14)
    have hχk_pos : 0 < chiQuantile c' k := xiStar_pos.trans (xiStar_lt_chiQuantile hc' hk14)
    have hgk_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr hk14.le) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      convert hanti using 2; omega
    have hβ_le : π * (η₀ * siteGap c' k) / 2 ≤ π / 16 := by
      have h1 : η₀ * siteGap c' k ≤ 1 / 8 := by nlinarith [hη₀1, hgap1, hgk_le]
      linarith [div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le) two_pos.le]
    have h_S_le : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ 1 / 2 := by
      have hβ_nn : 0 ≤ π * (η₀ * siteGap c' k) / 2 :=
        div_nonneg (mul_nonneg Real.pi_pos.le (mul_nonneg hη₀0 hgk_nn)) two_pos.le
      have hab : |Real.sin (π * (η₀ * siteGap c' k) / 2)| ≤ π / 16 :=
        Real.abs_sin_le_abs.trans ((abs_of_nonneg hβ_nn).le.trans hβ_le)
      have hpi4 : π / 16 ≤ 1 / 4 := by linarith [Real.pi_lt_d4]
      have hsq : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hab.trans hpi4) 2
      linarith
    have hsh1 : Real.sinh (π * (x - chiQuantile c' k) / 2) ≠ 0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hχk_gt.ne)) two_ne_zero)
    have hsh2 : Real.sinh (π * (x + chiQuantile c' k) / 2) ≠ 0 :=
      Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith [hx.1])) two_ne_zero)
    unfold pairModQ
    rw [blaschkePairQ_eq]
    have hden1 : 0 < Real.cosh (π * (x - chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x - chiQuantile c' k) / 2))]
    have hden2 : 0 < Real.cosh (π * (x + chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      linarith [one_le_pow₀ (n := 2) (Real.one_le_cosh (π * (x + chiQuantile c' k) / 2))]
    exact mul_pos (div_pos (by positivity) hden1) (div_pos (by positivity) hden2)
  have h_log_tsum := refComb_norm_log_eq_tsum hc' hx.1 hf hη₀0 hη₀1 hgap1 hf_ne
    fun m => h_q_pos (f + 1 + m) (by omega)
  have h_riesz := (riesz_real_identities hc' hx.1 f hf).2
  have h_int_eq : 2 * ∫ a in Set.Ioi (f : ℝ), phiVar c' x a = c' * majorantReal x + c' * combPf c' f x :=
    h_riesz.2.2.1
  have h_int_ioi : IntegrableOn (phiVar c' x) (Set.Ioi (f : ℝ)) volume :=
    h_riesz.1.mono (Set.Ioi_subset_Ioi hf14.le) le_rfl
  let S : ℕ → ℝ := fun K =>
    phiVar c' x f + ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k) -
      2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a
  have hS_le : ∀ K : ℕ, f + 1 ≤ K → S K ≤ C_minus := by
    intro K hKf
    have h_det_rw : ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k) =
        2 * ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k +
          ∑ k ∈ Finset.Icc (f + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkf1 : f + 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk1 : 1 ≤ k := by omega
      have hfk_r : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : f ≤ k)
      have hkne : x ≠ chiQuantile c' k := (h_gt_all k hfk_r).ne
      exact log_pairModQ_eq_phiVar_add_detune hc' hx.1 hk1 hkne hη₀0 hη₀1 hgap1
    have h_int_split : ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a =
        (∑ k ∈ Finset.Icc f (K - 1), ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a) +
          ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a := by
      have hcont : ContinuousOn (phiVar c' x) (Icc (f : ℝ) ((K : ℝ) + 1 / 2)) := fun a ha =>
        (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le ha.1) (h_gt_all a ha.1).ne').1.continuousAt.continuousWithinAt
      have h_ind : ∀ m : ℕ, f ≤ m → m ≤ K →
          ∫ a in (f : ℝ)..(m : ℝ), phiVar c' x a =
            ∑ k ∈ Finset.Icc f (m - 1), ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a := by
        intro m hfm hmK
        induction m, hfm using Nat.le_induction with
        | base =>
          have hmt : Finset.Icc f (f - 1) = ∅ := Finset.Icc_eq_empty (by omega)
          simp [hmt]
        | succ m hm ih =>
          have hmK_r : ((m + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
          have hm_r : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
          have hfm_r : (f : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          have hi1 : IntervalIntegrable (phiVar c' x) volume (f : ℝ) (m : ℝ) :=
            (hcont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc hfm_r
          have hi2 : IntervalIntegrable (phiVar c' x) volume (m : ℝ) ((m + 1 : ℕ) : ℝ) :=
            (hcont.mono (Icc_subset_Icc hfm_r (by linarith))).intervalIntegrable_of_Icc hm_r
          rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, ih (by omega)]
          have hIcc : Finset.Icc f (m + 1 - 1) = insert m (Finset.Icc f (m - 1)) := by
            ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
          have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          rw [hcast]
      have h1 := h_ind K (by omega) le_rfl
      have hfK_r : (f : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : f ≤ K)
      have hi_1 : IntervalIntegrable (phiVar c' x) volume (f : ℝ) (K : ℝ) :=
        (hcont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc hfK_r
      have hi_2 : IntervalIntegrable (phiVar c' x) volume (K : ℝ) ((K : ℝ) + 1 / 2) :=
        (hcont.mono (Icc_subset_Icc_left hfK_r)).intervalIntegrable_of_Icc (by linarith)
      rw [← intervalIntegral.integral_add_adjacent_intervals hi_1 hi_2, h1]
    have h_trap_sum :
        phiVar c' x f + 2 * ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k -
          2 * ((∑ k ∈ Finset.Icc f (K - 1), ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a) +
            ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a) ≤ 0 := by
      have h_id : phiVar c' x f + 2 * ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k =
          ∑ k ∈ Finset.Icc f (K - 1), (phiVar c' x k + phiVar c' x ((k : ℝ) + 1)) + phiVar c' x K := by
        have hI1 : Finset.Icc f (K - 1) = insert f (Finset.Icc (f + 1) (K - 1)) := by
          ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hI2 : Finset.Icc (f + 1) K = insert K (Finset.Icc (f + 1) (K - 1)) := by
          ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have h_shift : ∑ k ∈ Finset.Icc f (K - 1), phiVar c' x ((k : ℝ) + 1) =
            ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k := by
          refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
          · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
          · intro a _ b _ h; omega
          · intro m hm; simp only [Finset.mem_Icc] at hm; exact ⟨m - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k _; push_cast; rfl
        have h_eq0 : ∑ k ∈ Finset.Icc f (K - 1), phiVar c' x k =
            phiVar c' x f + ∑ k ∈ Finset.Icc (f + 1) (K - 1), phiVar c' x k := by
          rw [hI1, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
        have h_eq1 : ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k =
            ∑ k ∈ Finset.Icc (f + 1) (K - 1), phiVar c' x k + phiVar c' x K := by
          rw [hI2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
        rw [Finset.sum_add_distrib, h_shift, h_eq0, h_eq1]
        ring
      have h_telesc : phiVar c' x f + 2 * ∑ k ∈ Finset.Icc (f + 1) K, phiVar c' x k -
          2 * ((∑ k ∈ Finset.Icc f (K - 1), ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a) +
            ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a) =
          ∑ k ∈ Finset.Icc f (K - 1),
            (phiVar c' x k + phiVar c' x ((k : ℝ) + 1) -
              2 * ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a) +
          (phiVar c' x K - 2 * ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a) := by
        rw [h_id, mul_add (2 : ℝ), Finset.mul_sum]
        have heq_sub : ∑ k ∈ Finset.Icc f (K - 1), (phiVar c' x k + phiVar c' x ((k : ℝ) + 1) -
            2 * ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a) =
          (∑ k ∈ Finset.Icc f (K - 1), (phiVar c' x k + phiVar c' x ((k : ℝ) + 1))) -
            ∑ k ∈ Finset.Icc f (K - 1), 2 * ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a :=
          Finset.sum_sub_distrib _ _
        rw [heq_sub]; ring
      rw [h_telesc]
      have h_each_T : ∀ k ∈ Finset.Icc f (K - 1),
          phiVar c' x k + phiVar c' x ((k : ℝ) + 1) -
            2 * ∫ a in (k : ℝ)..((k : ℝ) + 1), phiVar c' x a ≤ 0 := by
        intro k hk
        have hkf : (f : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
        refine trapezoid_nonpos_of_second_nonpos
          (fun t ht => (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le (hkf.trans ht.1))
            (h_gt_all t (hkf.trans ht.1)).ne').1)
          (fun t ht => (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le (hkf.trans ht.1))
            (h_gt_all t (hkf.trans ht.1)).ne').2)
          (continuousOn_phiVarSecond hc' hx.1 (hf14.trans_le hkf)
            (by linarith) fun t ht => (h_gt_all t (hkf.trans ht.1)).ne')
          fun t ht => (phiVar_deriv_sign_of_gt hc' hx.1 (hf14.trans_le (hkf.trans ht.1))
            (h_gt_all t (hkf.trans ht.1))).2.le
      have h_tail : phiVar c' x K - 2 * ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a ≤ 0 := by
        have hfK_r : (f : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : f ≤ K)
        have hcontK : ContinuousOn (phiVar c' x) (Icc (K : ℝ) ((K : ℝ) + 1 / 2)) := fun t ht =>
          (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le (hfK_r.trans ht.1))
            (h_gt_all t (hfK_r.trans ht.1)).ne').1.continuousAt.continuousWithinAt
        have h_mono : ∫ _a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x K ≤
            ∫ a in (K : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a := by
          refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
            (hcontK.intervalIntegrable_of_Icc (by linarith)) fun a ha => ?_
          have h_m : MonotoneOn (phiVar c' x) (Icc (K : ℝ) ((K : ℝ) + 1 / 2)) :=
            monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcontK
              (fun t ht => by
                rw [interior_Icc] at ht
                exact (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le (hfK_r.trans ht.1.le))
                  (h_gt_all t (hfK_r.trans ht.1.le)).ne').1.differentiableAt.differentiableWithinAt)
              fun t ht => by
                rw [interior_Icc] at ht
                have hd := (phiVar_hasDerivAt hc' hx.1 (hf14.trans_le (hfK_r.trans ht.1.le))
                  (h_gt_all t (hfK_r.trans ht.1.le)).ne').1
                rw [hd.deriv]
                exact (phiVar_deriv_sign_of_gt hc' hx.1 (hf14.trans_le (hfK_r.trans ht.1.le))
                  (h_gt_all t (hfK_r.trans ht.1.le))).1.le
          exact h_m ⟨le_rfl, by linarith⟩ ha ha.1
        rw [intervalIntegral.integral_const, smul_eq_mul] at h_mono
        have heq : ((K : ℝ) + 1 / 2 - (K : ℝ)) * phiVar c' x K = (1 / 2 : ℝ) * phiVar c' x K := by ring
        rw [heq] at h_mono
        linarith
      exact add_nonpos (Finset.sum_nonpos h_each_T) h_tail
    have h_det_sum : ∑ k ∈ Finset.Icc (f + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x ≤
        C_minus := by
      have h_each_d : ∀ k ∈ Finset.Icc (f + 1) K,
          deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x ≤
            (1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2 +
              (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))) := by
        intro k hk
        have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
        have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by linarith
        have hχk_xi : xiStar ≤ chiQuantile c' (k : ℝ) := (chiQuantile_spec hc' hk14.le).1
        have hχk_ne : x ≠ chiQuantile c' (k : ℝ) := (hx.2.trans_lt (xiStar_lt_chiQuantile hc' hk14)).ne
        have hgk_nn : 0 ≤ siteGap c' k := by
          unfold siteGap
          exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr hk14.le) (Set.mem_Ici.mpr (by linarith)) (by linarith))
        have hgk_le1 : siteGap c' k ≤ siteGap c' 1 := by
          have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
          convert hanti using 2; omega
        have hε_nn : 0 ≤ η₀ * siteGap c' k := mul_nonneg hη₀0 hgk_nn
        have hε_le18 : η₀ * siteGap c' k ≤ 1 / 8 := by nlinarith [hη₀1, hgap1, hgk_le1]
        have hd_raw := h_det hχk_xi hx.1 hχk_ne hε_nn hε_le18
        have h_dist_ge : siteRadius c' (k : ℝ) ≤ |x - chiQuantile c' (k : ℝ)| := by
          have hlt := hx.2.trans_lt (xiStar_lt_chiQuantile hc' hk14)
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
          unfold siteRadius; linarith [hx.2]
        have h_rad_ge : ((k : ℝ) - 1 / 4) * chiDeriv c' (k : ℝ) ≤ siteRadius c' (k : ℝ) := by
          have h_any : ∀ a₀ ∈ Ioo (1 / 4 : ℝ) (k : ℝ),
              ((k : ℝ) - a₀) * chiDeriv c' (k : ℝ) ≤ siteRadius c' (k : ℝ) := by
            intro a₀ ha₀
            have h1 := chiQuantile_sub_ge_mul hc' ha₀.1 ha₀.2.le
            have ha₀_xi : xiStar ≤ chiQuantile c' a₀ := (chiQuantile_spec hc' ha₀.1.le).1
            unfold siteRadius; linarith
          by_contra hlt
          push Not at hlt
          let δ := ((k : ℝ) - 1 / 4) * chiDeriv c' (k : ℝ) - siteRadius c' (k : ℝ)
          have hδ_pos : 0 < δ := by dsimp [δ]; linarith
          have hcd_pos : 0 < chiDeriv c' (k : ℝ) := chiDeriv_pos hc' hk14
          let a₀ := 1 / 4 + min (((k : ℝ) - 1 / 4) / 2) (δ / (2 * chiDeriv c' (k : ℝ)))
          have ha₀_mem : a₀ ∈ Ioo (1 / 4 : ℝ) (k : ℝ) := by
            have hm_pos : 0 < min (((k : ℝ) - 1 / 4) / 2) (δ / (2 * chiDeriv c' (k : ℝ))) :=
              lt_min (by linarith) (div_pos hδ_pos (mul_pos two_pos hcd_pos))
            have hm_le : min (((k : ℝ) - 1 / 4) / 2) (δ / (2 * chiDeriv c' (k : ℝ))) ≤ ((k : ℝ) - 1 / 4) / 2 :=
              min_le_left _ _
            dsimp [a₀]
            exact ⟨by linarith, by linarith⟩
          have h_bd := h_any a₀ ha₀_mem
          have hm_le2 : a₀ - 1 / 4 ≤ δ / (2 * chiDeriv c' (k : ℝ)) := by
            dsimp [a₀]; linarith [min_le_right (((k : ℝ) - 1 / 4) / 2) (δ / (2 * chiDeriv c' (k : ℝ)))]
          have h_mul : (a₀ - 1 / 4) * chiDeriv c' (k : ℝ) ≤ δ / 2 := by
            have := mul_le_mul_of_nonneg_right hm_le2 hcd_pos.le
            have heq : δ / (2 * chiDeriv c' (k : ℝ)) * chiDeriv c' (k : ℝ) = δ / 2 := by
              field_simp [hcd_pos.ne']
            linarith
          have h_calc : ((k : ℝ) - 1 / 4) * chiDeriv c' (k : ℝ) - (a₀ - 1 / 4) * chiDeriv c' (k : ℝ) =
              ((k : ℝ) - a₀) * chiDeriv c' (k : ℝ) := by ring
          dsimp [δ] at h_mul hδ_pos
          linarith
        have h_gk_cd : siteGap c' k ≤ chiDeriv c' (k : ℝ) := siteGap_le_chiDeriv hc' (by omega)
        have h_rad_pos : 0 < siteRadius c' (k : ℝ) := by
          unfold siteRadius; exact sub_pos.mpr (xiStar_lt_chiQuantile hc' hk14)
        have h_t1 : (η₀ * siteGap c' k) ^ 2 / (x - chiQuantile c' (k : ℝ)) ^ 2 ≤
            (1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2 := by
          have hε_cd : η₀ * siteGap c' k ≤ (1 / 4 : ℝ) * chiDeriv c' (k : ℝ) :=
            mul_le_mul hη₀1 h_gk_cd hgk_nn (by norm_num)
          have h_prod : η₀ * siteGap c' k * ((k : ℝ) - 1 / 4) ≤ (1 / 4 : ℝ) * |x - chiQuantile c' (k : ℝ)| := by
            calc η₀ * siteGap c' k * ((k : ℝ) - 1 / 4)
                ≤ (1 / 4 : ℝ) * chiDeriv c' (k : ℝ) * ((k : ℝ) - 1 / 4) :=
                  mul_le_mul_of_nonneg_right hε_cd (by linarith)
              _ = (1 / 4 : ℝ) * (((k : ℝ) - 1 / 4) * chiDeriv c' (k : ℝ)) := by ring
              _ ≤ (1 / 4 : ℝ) * siteRadius c' (k : ℝ) :=
                  mul_le_mul_of_nonneg_left h_rad_ge (by norm_num)
              _ ≤ (1 / 4 : ℝ) * |x - chiQuantile c' (k : ℝ)| :=
                  mul_le_mul_of_nonneg_left h_dist_ge (by norm_num)
          have h_div : (η₀ * siteGap c' k) / |x - chiQuantile c' (k : ℝ)| ≤ (1 / 4 : ℝ) / ((k : ℝ) - 1 / 4) := by
            rw [div_le_div_iff₀ (h_rad_pos.trans_le h_dist_ge) (by linarith)]
            exact h_prod
          have h_sq := pow_le_pow_left₀ (div_nonneg hε_nn (abs_nonneg _)) h_div 2
          rw [div_pow, div_pow, sq_abs] at h_sq
          linarith [show ((1 / 4 : ℝ) ^ 2) / ((k : ℝ) - 1 / 4) ^ 2 = (1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2 by ring]
        have h_t2 : C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * |x - chiQuantile c' (k : ℝ)|) ≤
            (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))) := by
          have hexp_le : Real.exp (-π * |x - chiQuantile c' (k : ℝ)|) ≤ Real.exp (-π * siteRadius c' (k : ℝ)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h_dist_ge (neg_nonpos.mpr Real.pi_pos.le))
          have hε2_le : (η₀ * siteGap c' k) ^ 2 ≤ (1 / 32 : ℝ) * chiDeriv c' (k : ℝ) := by
            calc (η₀ * siteGap c' k) ^ 2 = (η₀ * siteGap c' k) * (η₀ * siteGap c' k) := by ring
              _ ≤ (1 / 8 : ℝ) * ((1 / 4 : ℝ) * chiDeriv c' (k : ℝ)) :=
                  mul_le_mul hε_le18 (mul_le_mul hη₀1 h_gk_cd hgk_nn (by norm_num))
                    hε_nn (by norm_num)
              _ = (1 / 32 : ℝ) * chiDeriv c' (k : ℝ) := by ring
          calc C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * |x - chiQuantile c' (k : ℝ)|)
              ≤ C_δ * ((1 / 32 : ℝ) * chiDeriv c' (k : ℝ)) * Real.exp (-π * siteRadius c' (k : ℝ)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hε2_le hCδ_pos.le) hexp_le
                  (Real.exp_pos _).le (mul_nonneg hCδ_pos.le (by positivity [chiDeriv_pos hc' hk14]))
            _ = (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))) := by ring
        exact hd_raw.trans (add_le_add h_t1 h_t2)
      have h_sub_Icc : Finset.Icc (f + 1) K ⊆ Finset.Icc 2 K := fun k hk =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hk).1; omega, (Finset.mem_Icc.mp hk).2⟩
      have h_sum1 : ∑ k ∈ Finset.Icc (f + 1) K, ((1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2) ≤ 1 / 16 := by
        have h_eq : ∑ k ∈ Finset.Icc (f + 1) K, ((1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2) =
            (1 / 16 : ℝ) * ∑ k ∈ Finset.Icc (f + 1) K, (1 : ℝ) / (((k : ℝ) - 1 / 4) ^ 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [h_eq]
        have hs1 := (Finset.sum_le_sum_of_subset_of_nonneg h_sub_Icc fun _ _ _ => by positivity).trans
          (inv_k_sub_quarter_sq_Icc_le K (by omega))
        linarith
      have h_sum2 : ∑ k ∈ Finset.Icc (f + 1) K,
          (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))) ≤ C_δ / (32 * π) := by
        rw [← Finset.mul_sum]
        have h_sub : ∑ k ∈ Finset.Icc (f + 1) K, chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) ≤
            ∑ k ∈ Finset.Icc 2 K, chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg h_sub_Icc fun k hk _ => ?_
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 1 ≤ k)
          have hk14 : (1 / 4 : ℝ) < (k : ℝ) := by linarith
          exact mul_nonneg (chiDeriv_pos hc' hk14).le (Real.exp_pos _).le
        have h_exp := h_sub.trans (exp_neg_pi_siteRadius_sum_le hc' K (by omega))
        calc (C_δ / 32) * ∑ k ∈ Finset.Icc (f + 1) K, chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ))
            ≤ (C_δ / 32) * (1 / π) := mul_le_mul_of_nonneg_left h_exp (by positivity)
          _ = C_δ / (32 * π) := by ring
      calc ∑ k ∈ Finset.Icc (f + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x
          ≤ ∑ k ∈ Finset.Icc (f + 1) K,
              ((1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2 +
                (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)))) :=
            Finset.sum_le_sum h_each_d
        _ = (∑ k ∈ Finset.Icc (f + 1) K, ((1 / 16 : ℝ) / ((k : ℝ) - 1 / 4) ^ 2)) +
              (∑ k ∈ Finset.Icc (f + 1) K,
                (C_δ / 32) * (chiDeriv c' (k : ℝ) * Real.exp (-π * siteRadius c' (k : ℝ)))) :=
            Finset.sum_add_distrib
        _ ≤ 1 / 16 + C_δ / (32 * π) := add_le_add h_sum1 h_sum2
        _ ≤ C_minus := by dsimp [C_minus]; linarith
    dsimp [S]
    rw [h_det_rw, h_int_split]
    linarith [h_trap_sum, h_det_sum]
  have hS_tend : Tendsto S atTop (𝓝 (Real.log ‖refComb c' f η₀ (x : ℂ)‖ -
      (c' * majorantReal x + c' * combPf c' f x))) := by
    have h_tsum_tend : Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k))
        atTop (𝓝 (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)))) := by
      have h_part := h_log_tsum.1.hasSum.tendsto_sum_nat
      have h_shift : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range (K - f), Real.log (pairModQ c' η₀ x (f + 1 + m)))
          atTop (𝓝 (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)))) :=
        h_part.comp (tendsto_atTop_atTop.mpr fun N => ⟨N + f, fun K hK => by omega⟩)
      refine h_shift.congr' ?_
      rw [EventuallyEq, Filter.eventually_atTop]
      refine ⟨f + 1, fun K hK => ?_⟩
      refine Finset.sum_bij (fun m _ => f + 1 + m) ?_ ?_ ?_ ?_
      · intro m hm; rw [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; exact ⟨k - (f + 1), Finset.mem_range.mpr (by omega), by omega⟩
      · intro m _; rfl
    have h_int_tend : Tendsto (fun K : ℕ => ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)
        atTop (𝓝 (∫ a in Set.Ioi (f : ℝ), phiVar c' x a)) :=
      intervalIntegral_tendsto_integral_Ioi (f : ℝ) h_int_ioi
        (tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop)
    have h_eq_lim : phiVar c' x f + ∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) -
          2 * ∫ a in Set.Ioi (f : ℝ), phiVar c' x a =
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ - (c' * majorantReal x + c' * combPf c' f x) := by
      rw [← h_log_tsum.2, h_int_eq]
    rw [← h_eq_lim]
    exact (tendsto_const_nhds.add h_tsum_tend).sub (h_int_tend.const_mul 2)
  have h_lim_le : Real.log ‖refComb c' f η₀ (x : ℂ)‖ - (c' * majorantReal x + c' * combPf c' f x) ≤ C_minus :=
    le_of_tendsto hS_tend (Filter.eventually_atTop.mpr ⟨f + 1, hS_le⟩)
  linarith

/-- **K6(b), lobe Blaschke majorization (`cmb:K6`, `comb_estimates.tex`, line 256)**:
for $0 \le x < \xi_*$,
$|B^{(f)}(x)| e^{c' L(x)} \le C e^{c' P^{(f)}(x) + c' (U + L)(x)} \le C |T_{\xi_*}(x)|^{-2 n_1} e^{c' (U + L)(x)}$. -/
theorem lobe_upper_K6b_blaschke :
    ∃ C > 0, ∀ᶠ c' in atTop, ∀ (f : ℕ) (η₀ x : ℝ),
      1 ≤ f → 0 ≤ η₀ → η₀ ≤ 1 / 4 → x ∈ Ico 0 xiStar →
        ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
            C * Real.exp (c' * combPf c' f x + c' * (majorantReal x + slitL x)) ∧
          C * Real.exp (c' * combPf c' f x + c' * (majorantReal x + slitL x)) ≤
            C * ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(2 * n1Comb f)) *
              Real.exp (c' * (majorantReal x + slitL x)) := by
  obtain ⟨C_minus, hCm_pos, h_log_ev⟩ := lobe_upper_K6b
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  let C : ℝ := Real.exp C_minus
  refine ⟨C, Real.exp_pos _, ?_⟩
  filter_upwards [h_log_ev, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' h_log hgap_c hc'
  intro f η₀ x hf hη₀0 hη₀1 hx
  have hf_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
  have hx_Icc : x ∈ Icc 0 xiStar := ⟨hx.1, hx.2.le⟩
  have h_log_le := h_log f η₀ x hf hη₀0 hη₀1 hx_Icc
  have href_nn : 0 ≤ ‖refComb c' f η₀ (x : ℂ)‖ := norm_nonneg _
  have h_first : ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
      C * Real.exp (c' * combPf c' f x + c' * (majorantReal x + slitL x)) := by
    rcases eq_or_lt_of_le href_nn with h0 | href_pos
    · rw [← h0, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · have hexp := Real.exp_le_exp.mpr h_log_le
      rw [Real.exp_add, Real.exp_log href_pos, Real.exp_add] at hexp
      dsimp [C]; linarith
  have hχf_gt : xiStar < chiQuantile c' (f : ℝ) := xiStar_lt_chiQuantile hc' hf14
  have hpf_le : c' * combPf c' f x ≤ 2 * n1Comb f * (-realLogT x xiStar) := by
    have hcont : ContinuousOn (fun y => rhoU y * (-realLogT x y)) (Icc xiStar (chiQuantile c' (f : ℝ))) := by
      refine (continuousOn_rhoU.mono Set.Icc_subset_Ici_self).mul ?_
      intro y hy
      exact ((realLogT_hasDerivAt hx.1 (xiStar_pos.le.trans hy.1) (hx.2.trans_le hy.1).ne').1.neg.continuousAt.continuousWithinAt)
    have h_mono : ∀ y ∈ Icc xiStar (chiQuantile c' (f : ℝ)), -realLogT x y ≤ -realLogT x xiStar := by
      intro y hy
      have h_inc : MonotoneOn (realLogT x) (Ici xiStar) :=
        monotoneOn_of_deriv_nonneg (convex_Ici xiStar)
          (fun t ht => (realLogT_hasDerivAt hx.1 (xiStar_pos.le.trans ht) (hx.2.trans_le ht).ne').1.continuousAt.continuousWithinAt)
          (fun t ht => by
            rw [interior_Ici] at ht
            exact (realLogT_hasDerivAt hx.1 (xiStar_pos.le.trans ht.le) (hx.2.trans ht).ne').1.differentiableAt.differentiableWithinAt)
          fun t ht => by
            rw [interior_Ici] at ht
            rw [(realLogT_hasDerivAt hx.1 (xiStar_pos.le.trans ht.le) (hx.2.trans ht).ne').1.deriv]
            exact ((realLogT_deriv_bounds hx.1 (xiStar_pos.le.trans ht.le) (hx.2.trans ht).ne').2.2 (hx.2.trans ht)).1.le
      have hle := h_inc (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.1) hy.1
      linarith
    have h_int_le : ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y * (-realLogT x y) ≤
        ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y * (-realLogT x xiStar) :=
      intervalIntegral.integral_mono_on hχf_gt.le
        (hcont.intervalIntegrable_of_Icc hχf_gt.le)
        (((continuousOn_rhoU.mono Set.Icc_subset_Ici_self).mul continuousOn_const).intervalIntegrable_of_Icc hχf_gt.le)
        fun y hy => mul_le_mul_of_nonneg_left (h_mono y hy) (rhoU_nonneg y)
    have h_cum : c' * ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y = 2 * n1Comb f := by
      have hs := (chiQuantile_spec hc' hf14.le).2
      unfold cumulN at hs
      unfold n1Comb
      linarith
    have h_pf_eq : combPf c' f x = ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y * (-realLogT x y) := by
      unfold combPf
      rw [← intervalIntegral.integral_neg]
      congr 1; ext y; ring
    rw [h_pf_eq]
    calc c' * ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y * (-realLogT x y)
        ≤ c' * ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y * (-realLogT x xiStar) :=
          mul_le_mul_of_nonneg_left h_int_le hc'.le
      _ = (c' * ∫ y in xiStar..(chiQuantile c' (f : ℝ)), rhoU y) * (-realLogT x xiStar) := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ = 2 * n1Comb f * (-realLogT x xiStar) := by rw [h_cum]
  have hT_pos : 0 < ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ := by
    have h_eq := realLogT_eq_log_tanh hx.1 xiStar_pos.le hx.2.ne'
    have ht1 : 0 < Real.tanh (π * |x - xiStar| / 2) :=
      tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (abs_pos.mpr (sub_ne_zero.mpr hx.2.ne))) two_pos)
    have ht2 : 0 < Real.tanh (π * (x + xiStar) / 2) :=
      tanh_pos_of_pos (div_pos (mul_pos Real.pi_pos (by linarith [hx.1, xiStar_pos])) two_pos)
    have h_log_val : Real.log ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ = realLogT x xiStar := rfl
    by_contra h0
    have hnorm0 : ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    have hl0 : realLogT x xiStar = 0 := by rw [← h_log_val, hnorm0, Real.log_zero]
    have hprod_lt1 : Real.tanh (π * |x - xiStar| / 2) * Real.tanh (π * (x + xiStar) / 2) < 1 := by
      have ht1_lt := Real.tanh_lt_one (π * |x - xiStar| / 2)
      have ht2_lt := Real.tanh_lt_one (π * (x + xiStar) / 2)
      nlinarith
    have hlog_neg : realLogT x xiStar < 0 := by
      rw [h_eq]; exact Real.log_neg (mul_pos ht1 ht2) hprod_lt1
    linarith
  have hrpow_eq : Real.exp (2 * n1Comb f * (-realLogT x xiStar)) =
      ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(2 * n1Comb f)) := by
    have h_log_val : Real.log ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ = realLogT x xiStar := rfl
    rw [Real.rpow_def_of_pos hT_pos, h_log_val]
    congr 1; ring
  have h_second : C * Real.exp (c' * combPf c' f x + c' * (majorantReal x + slitL x)) ≤
      C * ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(2 * n1Comb f)) *
        Real.exp (c' * (majorantReal x + slitL x)) := by
    rw [Real.exp_add, ← hrpow_eq]
    have hexp := Real.exp_le_exp.mpr hpf_le
    calc C * (Real.exp (c' * combPf c' f x) * Real.exp (c' * (majorantReal x + slitL x)))
        ≤ C * (Real.exp (2 * n1Comb f * (-realLogT x xiStar)) * Real.exp (c' * (majorantReal x + slitL x))) := by
          gcongr
      _ = C * Real.exp (2 * n1Comb f * (-realLogT x xiStar)) * Real.exp (c' * (majorantReal x + slitL x)) := by
          ring
  exact ⟨h_first, h_second⟩

/-! ### Axiom verification guards -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_mul

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_r0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_r0

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.band_upper_K6a_bdd

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.lobe_upper_K6b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.lobe_upper_K6b

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.lobe_upper_K6b_blaschke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.lobe_upper_K6b_blaschke

end FormalResearch.ModularBootstrap.Upper.Holes

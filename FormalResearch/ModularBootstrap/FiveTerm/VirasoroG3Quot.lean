module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroSlopeIBP

/-!
# The quotient amplitude `b = (a - a(0))/sinh²(πt)` (FIVE-0, `ctu:jets`, `g₃`, step 1)

For an admissible amplitude `a` (`Amp a`: even, real-analytic, of exponential growth) the quotient
`b(t) = (a(t) - a(0))/sinh²(πt)` (value `b(0)` by continuity) is again admissible: the singularity at `t = 0` is
removable because `a - a(0)` has a double zero there (`a` is even).  This is the amplitude through which the third odd jet
of `h̄_a` is expressed as a first-order slope (`VirasoroG3Poisson`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma sinh_eq_re_im (w : ℂ) : Complex.sinh w = ((Real.sinh w.re * Real.cos w.im : ℝ) : ℂ) +
    ((Real.cosh w.re * Real.sin w.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast; ring

lemma re_sinh' (w : ℂ) : (Complex.sinh w).re = Real.sinh w.re * Real.cos w.im := by
  rw [sinh_eq_re_im]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]

lemma im_sinh' (w : ℂ) : (Complex.sinh w).im = Real.cosh w.re * Real.sin w.im := by
  rw [sinh_eq_re_im]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, zero_add, mul_one, add_zero]

lemma sinh_pi_ofReal (t : ℝ) : Complex.sinh ((π : ℂ) * (t : ℂ)) = ((Real.sinh (π * t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sinh]; push_cast; rfl

lemma sinh_pi_ne_zero_of_re_ne {ζ : ℂ} (h : ζ.re ≠ 0) : Complex.sinh ((π : ℂ) * ζ) ≠ 0 := by
  intro h0
  have hpi := Real.pi_pos
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  rw [re_sinh'] at hre
  rw [im_sinh'] at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero, Complex.zero_re, Complex.zero_im] at hre him
  have hsin : Real.sin (π * ζ.im) = 0 := by
    have := Real.cosh_pos (π * ζ.re)
    rcases mul_eq_zero.mp him with h1 | h1
    · exact absurd h1 this.ne'
    · exact h1
  have hcos : Real.cos (π * ζ.im) ≠ 0 := by
    intro hc
    have := Real.sin_sq_add_cos_sq (π * ζ.im)
    rw [hsin, hc] at this; norm_num at this
  have : Real.sinh (π * ζ.re) = 0 := by
    rcases mul_eq_zero.mp hre with h1 | h1
    · exact h1
    · exact absurd h1 hcos
  have := Real.sinh_eq_zero.mp this
  apply h
  nlinarith

lemma sinh_pi_ne_zero_of_ball {ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ‖ζ‖ < 1) : Complex.sinh ((π : ℂ) * ζ) ≠ 0 := by
  by_cases hr : ζ.re = 0
  · intro h
    have hpi := Real.pi_pos
    have him := congrArg Complex.im h
    rw [im_sinh'] at him
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      add_zero, Complex.zero_im, hr, mul_zero, Real.cosh_zero, one_mul] at him
    have hy : |ζ.im| < 1 := by
      have := Complex.abs_im_le_norm ζ
      linarith
    have hy0 : ζ.im ≠ 0 := by
      intro hy0; apply h0; apply Complex.ext <;> simp [hr, hy0]
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (x := π * ζ.im) (by nlinarith [abs_lt.mp hy])
      (by nlinarith [abs_lt.mp hy])).mp him
    apply hy0
    nlinarith
  · exact sinh_pi_ne_zero_of_re_ne hr

/-- The quotient amplitude: `Amp` is preserved by `a ↦ (a - a(0))/sinh²(πt)` (with the continuous value at `0`). -/
theorem amp_quot {a : ℝ → ℝ} (ha : Amp a) :
    ∃ b : ℝ → ℝ, Amp b ∧ ∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2 := by
  have hpi := Real.pi_pos
  -- the chart at 0
  obtain ⟨R, hR, v, hvd, hva⟩ := ha.loc 0
  have hv0 : v 0 = (a 0 : ℂ) := by
    have := hva 0 (by simpa using hR); simpa using this
  have hvball : DifferentiableOn ℂ v (ball (0 : ℂ) R) := by simpa using hvd
  -- v'(0) = 0 by evenness
  have hder0 : deriv v 0 = 0 := by
    have hHd : HasDerivAt v (deriv v 0) 0 :=
      (hvball.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
    obtain ⟨K, r, hr, hK⟩ := amp_sq_bound ha
    -- along the reals, (v t - v 0)/t → deriv v 0, and |a t - a 0|/|t| ≤ K |t| → 0
    have hsl := hasDerivAt_iff_tendsto_slope.mp hHd
    have hmap : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
          simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simpa using (ne_of_gt hε)
    have h1 := hsl.comp hmap
    have h2 : Tendsto (fun ε : ℝ => slope v 0 (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (show Tendsto (fun x : ℝ => |K| * x) (𝓝[>] 0) (𝓝 0) by
          have : Tendsto (fun x : ℝ => |K| * x) (𝓝 0) (𝓝 (|K| * 0)) :=
            (continuous_const.mul continuous_id).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r R by positivity)] with x hx
      have hx0 : 0 < x := hx.1
      have hxr : x < r := lt_of_lt_of_le hx.2 (min_le_left _ _)
      have hxR : x < R := lt_of_lt_of_le hx.2 (min_le_right _ _)
      have hvx : v (x : ℂ) = (a x : ℂ) := hva x (by rw [sub_zero, abs_of_pos hx0]; exact hxR)
      have hb := hK x (by rw [abs_of_pos hx0]; exact hxr)
      rw [slope_def_field, hvx, hv0, sub_zero]
      have : ((a x : ℂ) - (a 0 : ℂ)) / (x : ℂ) = (((a x - a 0) / x : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
      calc |a x - a 0| ≤ K * x ^ 2 := hb
        _ ≤ |K| * x * x := by
          have := le_abs_self K; nlinarith [mul_nonneg hx0.le hx0.le]
    exact tendsto_nhds_unique h1 h2
  -- the double zero: v ζ - v 0 = ζ² W ζ
  set W : ℂ → ℂ := dslope (dslope v 0) 0 with hW
  have hWd : DifferentiableOn ℂ W (ball (0 : ℂ) R) := by
    have h1 : DifferentiableOn ℂ (dslope v 0) (ball (0 : ℂ) R) :=
      (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr hvball
    exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr h1
  have hWeq : ∀ ζ : ℂ, v ζ - v 0 = ζ ^ 2 * W ζ := by
    intro ζ
    have e1 : (ζ - 0) • dslope v 0 ζ = v ζ - v 0 := sub_smul_dslope v 0 ζ
    have e2 : (ζ - 0) • dslope (dslope v 0) 0 ζ = dslope v 0 ζ - dslope v 0 0 := sub_smul_dslope (dslope v 0) 0 ζ
    have e3 : dslope v 0 0 = 0 := by rw [dslope_same, hder0]
    simp only [smul_eq_mul, sub_zero] at e1 e2
    rw [e3, sub_zero] at e2
    rw [← e1, hW, ← e2]; ring
  -- sinh(πζ) = ζ · Sh ζ
  set Sh : ℂ → ℂ := dslope (fun z : ℂ => Complex.sinh ((π : ℂ) * z)) 0 with hSh
  have hShd : Differentiable ℂ Sh := by
    have hd : Differentiable ℂ (fun z : ℂ => Complex.sinh ((π : ℂ) * z)) := by fun_prop
    intro z
    exact ((Complex.differentiableOn_dslope (s := univ) Filter.univ_mem).mpr hd.differentiableOn z (mem_univ z)).differentiableAt
      Filter.univ_mem
  have hSheq : ∀ ζ : ℂ, Complex.sinh ((π : ℂ) * ζ) = ζ * Sh ζ := by
    intro ζ
    have e1 := sub_smul_dslope (fun z : ℂ => Complex.sinh ((π : ℂ) * z)) 0 ζ
    simp only [smul_eq_mul, sub_zero, mul_zero, Complex.sinh_zero] at e1
    rw [← hSh] at e1
    exact e1.symm
  have hShne : ∀ ζ : ℂ, ‖ζ‖ < 1 → Sh ζ ≠ 0 := by
    intro ζ hζ
    by_cases hz : ζ = 0
    · subst hz
      have : HasDerivAt (fun z : ℂ => Complex.sinh ((π : ℂ) * z)) ((π : ℂ) * Complex.cosh ((π : ℂ) * 0)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).csinh
      rw [hSh, dslope_same, this.deriv]
      simp
    · intro h0
      apply sinh_pi_ne_zero_of_ball hz hζ
      rw [hSheq, h0, mul_zero]
  set ρ : ℝ := min R 1 with hρ
  have hρpos : 0 < ρ := lt_min hR one_pos
  set vt : ℂ → ℂ := fun ζ => W ζ / Sh ζ ^ 2 with hvt
  have hvtd : DifferentiableOn ℂ vt (ball (0 : ℂ) ρ) := by
    intro ζ hζ
    have hζR : ζ ∈ ball (0 : ℂ) R := ball_subset_ball (min_le_left _ _) hζ
    have hζ1 : ‖ζ‖ < 1 := by
      have := mem_ball_zero_iff.mp hζ
      exact lt_of_lt_of_le this (min_le_right _ _)
    exact ((hWd ζ hζR).mono (ball_subset_ball (min_le_left _ _))).div
      ((hShd ζ).differentiableWithinAt.pow 2) (pow_ne_zero 2 (hShne ζ hζ1))
  -- vt agrees with the quotient on the reals
  have hvtq : ∀ t : ℝ, t ≠ 0 → |t| < ρ →
      vt (t : ℂ) = (((a t - a 0) / Real.sinh (π * t) ^ 2 : ℝ) : ℂ) := by
    intro t ht htρ
    have htR : |t - 0| < R := by rw [sub_zero]; exact lt_of_lt_of_le htρ (min_le_left _ _)
    have h1 := hWeq (t : ℂ)
    rw [hva t htR, hv0] at h1
    have h2 := hSheq (t : ℂ)
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hsh : Real.sinh (π * t) ^ 2 ≠ 0 := by
      have : Real.sinh (π * t) ≠ 0 := by
        intro h; have := Real.sinh_eq_zero.mp h
        apply ht; nlinarith
      positivity
    have h3 : (Complex.sinh ((π : ℂ) * (t : ℂ))) = ((Real.sinh (π * t) : ℝ) : ℂ) := sinh_pi_ofReal t
    have hSht : Sh (t : ℂ) ≠ 0 := hShne _ (by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le htρ (min_le_right _ _))
    simp only [hvt]
    have hshc : ((Real.sinh (π * t) : ℝ) : ℂ) ≠ 0 := by
      have : Real.sinh (π * t) ≠ 0 := by
        intro h; have := Real.sinh_eq_zero.mp h
        apply ht; nlinarith
      exact_mod_cast this
    push_cast
    rw [h2, h1]
    field_simp
  -- the limit value b0
  set b0 : ℝ := (vt 0).re with hb0
  have hvt0 : vt 0 = (b0 : ℂ) := by
    apply Complex.ext
    · simp [hb0]
    · -- imaginary part vanishes: vt is continuous and real on the punctured real line
      have hc : ContinuousAt vt 0 :=
        (hvtd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρpos))).continuousAt
      have himc : ContinuousAt (fun ζ : ℂ => (vt ζ).im) 0 := Complex.continuous_im.continuousAt.comp hc
      have h2 : Tendsto (fun ε : ℝ => (vt (ε : ℂ)).im) (𝓝[>] 0) (𝓝 (vt 0).im) := by
        have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
            simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
          exact this.mono_left nhdsWithin_le_nhds
        exact himc.tendsto.comp h0
      have h3 : Tendsto (fun ε : ℝ => (vt (ε : ℂ)).im) (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hρpos] with ε hε
        rw [hvtq ε hε.1.ne' (by rw [abs_of_pos hε.1]; exact hε.2), Complex.ofReal_im]
      simpa using tendsto_nhds_unique h2 h3
  -- the function b
  let b : ℝ → ℝ := fun t => if t = 0 then b0 else (a t - a 0) / Real.sinh (π * t) ^ 2
  have hbq : ∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2 := fun t ht => by simp [b, ht]
  have hbvt : ∀ t : ℝ, |t| < ρ → vt (t : ℂ) = ((b t : ℝ) : ℂ) := by
    intro t htρ
    by_cases ht : t = 0
    · subst ht; simp [b, hvt0]
    · rw [hvtq t ht htρ, hbq t ht]
  have hbcont : Continuous b := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t = 0
    · subst ht
      have hc : ContinuousAt vt 0 :=
        (hvtd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρpos))).continuousAt
      have h1 : ContinuousAt (fun s : ℝ => vt (s : ℂ)) 0 := by
        have : ContinuousAt vt ((0 : ℝ) : ℂ) := by simpa using hc
        exact this.comp (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt
      have h2 : ContinuousAt (fun s : ℝ => (vt (s : ℂ)).re) 0 :=
        Complex.continuous_re.continuousAt.comp h1
      refine h2.congr ?_
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < ρ by exact hρpos), Ioi_mem_nhds (show -ρ < (0 : ℝ) by linarith)]
        with s hs1 hs2
      rw [hbvt s (by rw [abs_lt]; exact ⟨hs2, hs1⟩)]; simp
    · have hsh : Real.sinh (π * t) ^ 2 ≠ 0 := by
        have : Real.sinh (π * t) ≠ 0 := by
          intro h; have := Real.sinh_eq_zero.mp h
          apply ht; nlinarith
        positivity
      have hc : ContinuousAt (fun s : ℝ => (a s - a 0) / Real.sinh (π * s) ^ 2) t :=
        ((ha.cont.continuousAt.sub continuousAt_const).div
          ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).continuousAt hsh)
      refine hc.congr ?_
      filter_upwards [isOpen_ne.mem_nhds ht] with s hs
      rw [hbq s hs]
  have hbev : ∀ t, b (-t) = b t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hbq t ht, hbq (-t) (neg_ne_zero.mpr ht), ha.even, mul_neg, Real.sinh_neg, neg_sq]
  have hbbdd : ExpBdd b := by
    obtain ⟨M, hM⟩ := ha.bdd
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hbcont.continuousOn
    have hsinh1 : 0 < Real.sinh π := Real.sinh_pos_iff.mpr hpi
    refine ⟨max |K| ((|M| + |a 0|) / Real.sinh π ^ 2), fun t => ?_⟩
    have hexp1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
    by_cases ht : |t| ≤ 1
    · have := hK t ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩
      rw [Real.norm_eq_abs] at this
      calc |b t| ≤ |K| := this.trans (le_abs_self K)
        _ ≤ max |K| ((|M| + |a 0|) / Real.sinh π ^ 2) * 1 := by rw [mul_one]; exact le_max_left _ _
        _ ≤ _ := by gcongr
    · push Not at ht
      have ht0 : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
      rw [hbq t ht0, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sinh (π * t) ^ 2)]
      have hs1 : Real.sinh π ≤ Real.sinh (π * |t|) := by
        rw [Real.sinh_le_sinh]; nlinarith
      have hsabs : Real.sinh (π * t) ^ 2 = Real.sinh (π * |t|) ^ 2 := by
        rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h, mul_neg, Real.sinh_neg, neg_sq]
      rw [hsabs]
      have hsq : Real.sinh π ^ 2 ≤ Real.sinh (π * |t|) ^ 2 := pow_le_pow_left₀ hsinh1.le hs1 2
      have hnum : |a t - a 0| ≤ (|M| + |a 0|) * Real.exp |t| := by
        have h1 := hM t
        have h2 : M * Real.exp |t| ≤ |M| * Real.exp |t| :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
        calc |a t - a 0| ≤ |a t| + |a 0| := abs_sub _ _
          _ ≤ |M| * Real.exp |t| + |a 0| * Real.exp |t| := by
            nlinarith [abs_nonneg (a 0)]
          _ = _ := by ring
      calc |a t - a 0| / Real.sinh (π * |t|) ^ 2 ≤ ((|M| + |a 0|) * Real.exp |t|) / Real.sinh π ^ 2 :=
            div_le_div₀ (by positivity) hnum (by positivity) hsq
        _ = ((|M| + |a 0|) / Real.sinh π ^ 2) * Real.exp |t| := by ring
        _ ≤ _ := by gcongr; exact le_max_right _ _
  refine ⟨b, ⟨hbcont, hbev, hbbdd, fun y₀ => ?_⟩, hbq⟩
  by_cases hy : y₀ = 0
  · subst hy
    refine ⟨ρ, hρpos, vt, ?_, fun t ht => ?_⟩
    · simpa using hvtd
    · rw [sub_zero] at ht; exact hbvt t ht
  · obtain ⟨R', hR', v', hv'd, hv'a⟩ := ha.loc y₀
    set R'' : ℝ := min R' |y₀| with hR''
    have hR''pos : 0 < R'' := lt_min hR' (abs_pos.mpr hy)
    refine ⟨R'', hR''pos, fun ζ => (v' ζ - (a 0 : ℂ)) / Complex.sinh ((π : ℂ) * ζ) ^ 2, ?_, fun t ht => ?_⟩
    · intro ζ hζ
      have hζ' : ζ ∈ ball (y₀ : ℂ) R' := ball_subset_ball (min_le_left _ _) hζ
      have hre : ζ.re ≠ 0 := by
        intro h0
        have h1 : ‖ζ - (y₀ : ℂ)‖ < |y₀| := lt_of_lt_of_le (mem_ball_iff_norm.mp hζ) (min_le_right _ _)
        have h2 : |(ζ - (y₀ : ℂ)).re| ≤ ‖ζ - (y₀ : ℂ)‖ := Complex.abs_re_le_norm _
        simp [h0] at h2
        linarith
      have hne := sinh_pi_ne_zero_of_re_ne hre
      refine DifferentiableWithinAt.div (((hv'd ζ hζ').mono (ball_subset_ball (min_le_left _ _))).sub_const _) ?_
        (pow_ne_zero 2 hne)
      exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.sinh ((π : ℂ) * z) ^ 2)).differentiableAt.differentiableWithinAt
    · have htR : |t - y₀| < R' := lt_of_lt_of_le ht (min_le_left _ _)
      have ht0 : t ≠ 0 := by
        intro h0; rw [h0] at ht
        have := lt_of_lt_of_le ht (min_le_right _ _)
        simp at this
      simp only
      rw [hv'a t htR, hbq t ht0]
      rw [sinh_pi_ofReal t]; push_cast; rfl

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.amp_quot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.amp_quot

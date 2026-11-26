module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroJet
public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterPoisson
public import FormalResearch.ModularBootstrap.FiveTerm.StripCauchy

/-!
# The slope of the strip Schwarz integral at the edge point `0` (FIVE-0, `ctu:jets`, step 2)

For an even amplitude `a` (`Amp a`) the real Poisson representation `Re h̄_a(ε) = ∫ a(t) P_ε(t) dt`, with
`P_ε(t) = sin(πε) cosh(πt)/(sinh²(πt) + sin²(πε))` of total mass `1`, gives
`(Re h̄_a(ε) - a(0))/ε → π ∫ (a(t) - a(0)) cosh(πt)/sinh²(πt) dt` as `ε → 0⁺`
(dominated convergence; `a(t) - a(0) = O(t²)` by evenness and local holomorphy).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `a(t) - a(0) = O(t²)` for an even locally holomorphic amplitude. -/
lemma amp_sq_bound {a : ℝ → ℝ} (ha : Amp a) :
    ∃ K r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → |a t - a 0| ≤ K * t ^ 2 := by
  obtain ⟨R, hR, v, hv, hva⟩ := ha.loc 0
  obtain ⟨C, r0, hr0, hjet⟩ := jet_ball hR (by simpa using hv)
  refine ⟨C, min r0 R, lt_min hr0 hR, fun t ht => ?_⟩
  have htr : |t| < r0 := lt_of_lt_of_le ht (min_le_left _ _)
  have htR : |t| < R := lt_of_lt_of_le ht (min_le_right _ _)
  have h0 : v 0 = (a 0 : ℂ) := by
    have := hva 0 (by simpa using hR); simpa using this
  have hvt : v (t : ℂ) = (a t : ℂ) := hva t (by simpa using htR)
  have hvt' : v ((-t : ℝ) : ℂ) = (a t : ℂ) := by
    rw [hva (-t) (by simpa using htR), ha.even]
  have n1 := hjet (t : ℂ) (by simpa using htr)
  have n2 := hjet ((-t : ℝ) : ℂ) (by simpa using htr)
  rw [hvt, h0] at n1
  rw [hvt', h0] at n2
  rw [Complex.norm_real, Real.norm_eq_abs] at n1 n2
  set d := deriv v 0
  have e : ((a t - a 0 : ℝ) : ℂ) = ((a t : ℂ) - (a 0 : ℂ) - d * (t : ℂ)) / 2 +
      ((a t : ℂ) - (a 0 : ℂ) - d * ((-t : ℝ) : ℂ)) / 2 := by push_cast; ring
  have h3 : ‖((a t - a 0 : ℝ) : ℂ)‖ ≤ C * t ^ 2 := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div]
    simp only [Complex.norm_ofNat] at *
    rw [abs_neg, sq_abs] at n2
    rw [sq_abs] at n1
    linarith
  rwa [Complex.norm_real, Real.norm_eq_abs] at h3

/-- `cosh(πt)/sinh²(πt)`, the Hilbert-type kernel of the slope. -/
noncomputable def kern (t : ℝ) : ℝ := Real.cosh (π * t) / Real.sinh (π * t) ^ 2

lemma kern_nonneg (t : ℝ) : 0 ≤ kern t := by
  unfold kern; exact div_nonneg (Real.cosh_pos _).le (sq_nonneg _)

lemma kern_abs (t : ℝ) : kern t = Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2 := by
  unfold kern
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, mul_neg, Real.cosh_neg, Real.sinh_neg]; ring

lemma kern_le_exp {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, s ≤ |t| → kern t ≤ C * Real.exp (-(π * |t|)) := by
  have hpi := Real.pi_pos
  set κ : ℝ := (1 - Real.exp (-(2 * π * s))) / 2 with hκ
  have hκpos : 0 < κ := by
    have : Real.exp (-(2 * π * s)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith)
    rw [hκ]; linarith
  refine ⟨κ⁻¹ ^ 2, by positivity, fun t ht => ?_⟩
  rw [kern_abs]
  set x : ℝ := π * |t| with hx
  have hxs : π * s ≤ x := by rw [hx]; exact mul_le_mul_of_nonneg_left ht hpi.le
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxs
  have hch : Real.cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsh : κ * Real.exp x ≤ Real.sinh x := by
    rw [Real.sinh_eq, hκ]
    have h1 : Real.exp (-x) ≤ Real.exp (-(2 * π * s)) * Real.exp x := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  have hshpos : 0 < κ * Real.exp x := by positivity
  have hsq : (κ * Real.exp x) ^ 2 ≤ Real.sinh x ^ 2 := by
    exact pow_le_pow_left₀ hshpos.le hsh 2
  have hex : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hsq), hex]
  calc Real.cosh x ≤ Real.exp x := hch
    _ = κ⁻¹ ^ 2 * (Real.exp x)⁻¹ * (κ * Real.exp x) ^ 2 := by
      field_simp
    _ ≤ κ⁻¹ ^ 2 * (Real.exp x)⁻¹ * Real.sinh x ^ 2 := by gcongr

lemma kern_le_small {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) :
    kern t ≤ Real.cosh π / (π ^ 2 * t ^ 2) := by
  have hpi := Real.pi_pos
  rw [kern_abs]
  have ha : 0 < |t| := abs_pos.mpr ht0
  have hsh : π * |t| ≤ Real.sinh (π * |t|) := Real.self_le_sinh_iff.mpr (by positivity)
  have hch : Real.cosh (π * |t|) ≤ Real.cosh π := by
    rw [Real.cosh_le_cosh, abs_of_pos (by positivity), abs_of_pos hpi]
    nlinarith
  have hsq : (π * |t|) ^ 2 ≤ Real.sinh (π * |t|) ^ 2 := pow_le_pow_left₀ (by positivity) hsh 2
  have h2 : π ^ 2 * t ^ 2 = (π * |t|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [h2]
  have hpos : 0 < (π * |t|) ^ 2 := by positivity
  calc Real.cosh (π * |t|) / Real.sinh (π * |t|) ^ 2 ≤ Real.cosh (π * |t|) / (π * |t|) ^ 2 :=
        div_le_div_of_nonneg_left (Real.cosh_pos _).le hpos hsq
    _ ≤ Real.cosh π / (π * |t|) ^ 2 := by gcongr

lemma slope_bound {a : ℝ → ℝ} (ha : Amp a) :
    ∃ Cb : ℝ, ∀ t : ℝ, t ≠ 0 → |a t - a 0| * (π * kern t) ≤ Cb * Real.exp (-(1 * |t|)) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  obtain ⟨K, r, hr, hK⟩ := amp_sq_bound ha
  obtain ⟨M, hM⟩ := ha.bdd
  have hs : 0 < min r 1 := lt_min hr one_pos
  obtain ⟨Cs, hCs, hk⟩ := kern_le_exp hs
  refine ⟨|K| * Real.cosh π / π * Real.exp 1 + (|M| + |a 0|) * π * Cs, fun t ht0 => ?_⟩
  have hc1 : 0 ≤ |K| * Real.cosh π / π * Real.exp 1 := by
    have := Real.cosh_pos π; positivity
  have hc2 : 0 ≤ (|M| + |a 0|) * π * Cs := by positivity
  have hexp : 0 < Real.exp (-(1 * |t|)) := Real.exp_pos _
  have ht : 0 < |t| := abs_pos.mpr ht0
  by_cases hts : |t| < min r 1
  · have h1 : |a t - a 0| ≤ |K| * t ^ 2 :=
      (hK t (lt_of_lt_of_le hts (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg t))
    have h2 := kern_le_small ht0 (lt_of_lt_of_le hts (min_le_right _ _)).le
    have ht2 : 0 < t ^ 2 := by positivity
    have hk0 := kern_nonneg t
    have h3 : |a t - a 0| * (π * kern t) ≤ |K| * t ^ 2 * (π * (Real.cosh π / (π ^ 2 * t ^ 2))) := by
      gcongr
    have h4 : |K| * t ^ 2 * (π * (Real.cosh π / (π ^ 2 * t ^ 2))) = |K| * Real.cosh π / π := by
      field_simp
    have h5 : 1 ≤ Real.exp 1 * Real.exp (-(1 * |t|)) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have := lt_of_lt_of_le hts (min_le_right _ _); linarith
    have h6 : |K| * Real.cosh π / π ≤ |K| * Real.cosh π / π * Real.exp 1 * Real.exp (-(1 * |t|)) := by
      have : 0 ≤ |K| * Real.cosh π / π := by have := Real.cosh_pos π; positivity
      calc |K| * Real.cosh π / π = |K| * Real.cosh π / π * 1 := by ring
        _ ≤ |K| * Real.cosh π / π * (Real.exp 1 * Real.exp (-(1 * |t|))) :=
          mul_le_mul_of_nonneg_left h5 this
        _ = _ := by ring
    calc |a t - a 0| * (π * kern t) ≤ _ := h3
      _ = _ := h4
      _ ≤ _ := h6
      _ ≤ (|K| * Real.cosh π / π * Real.exp 1 + (|M| + |a 0|) * π * Cs) * Real.exp (-(1 * |t|)) := by
        nlinarith [mul_nonneg hc2 hexp.le]
  · have hts' : min r 1 ≤ |t| := not_lt.mp hts
    have hk1 := hk t hts'
    have hex1 : 1 ≤ Real.exp |t| := Real.one_le_exp ht.le
    have h1 : |a t - a 0| ≤ (|M| + |a 0|) * Real.exp |t| := by
      have := hM t
      have h2 : M * Real.exp |t| ≤ |M| * Real.exp |t| :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      calc |a t - a 0| ≤ |a t| + |a 0| := abs_sub _ _
        _ ≤ |M| * Real.exp |t| + |a 0| * 1 := by linarith
        _ ≤ |M| * Real.exp |t| + |a 0| * Real.exp |t| := by
          nlinarith [abs_nonneg (a 0)]
        _ = _ := by ring
    have hk0 := kern_nonneg t
    have h3 : |a t - a 0| * (π * kern t) ≤
        (|M| + |a 0|) * Real.exp |t| * (π * (Cs * Real.exp (-(π * |t|)))) := by
      gcongr
    have h4 : (|M| + |a 0|) * Real.exp |t| * (π * (Cs * Real.exp (-(π * |t|)))) =
        (|M| + |a 0|) * π * Cs * Real.exp (|t| + -(π * |t|)) := by
      rw [Real.exp_add]; ring
    have h5 : Real.exp (|t| + -(π * |t|)) ≤ Real.exp (-(1 * |t|)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc |a t - a 0| * (π * kern t) ≤ _ := h3
      _ = _ := h4
      _ ≤ (|M| + |a 0|) * π * Cs * Real.exp (-(1 * |t|)) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hc1 hexp.le]

lemma tendsto_sin_pi_div : Tendsto (fun ε : ℝ => Real.sin (π * ε) / ε) (𝓝[>] 0) (𝓝 π) := by
  have h : HasDerivAt (fun ε : ℝ => Real.sin (π * ε)) π 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul π).sin
    simpa using this
  have := (hasDerivAt_iff_tendsto_slope_zero.mp h).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  refine this.congr (fun ε => ?_)
  simp [div_eq_inv_mul]

/-- **The slope of `Re h̄_a` at the edge point `0`.** -/
theorem hbarA_slope {a : ℝ → ℝ} (ha : Amp a) :
    Tendsto (fun ε : ℝ => ((hbarA a (ε : ℂ)).re - a 0) / ε) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, (a t - a 0) * (π * kern t))) := by
  have hpi := Real.pi_pos
  set F : ℝ → ℝ → ℝ := fun ε t => (a t - a 0) * poissonK ε t / ε with hF
  have hstrip : ∀ ε : ℝ, 0 < ε → ε < 1 → (ε : ℂ) ∈ strip := fun ε h0 h1 =>
    ⟨by simpa using h0, by simpa using h1⟩
  have hint : ∀ ε : ℝ, 0 < ε → ε < 1 → Integrable (fun t : ℝ => a t * poissonK ε t) := by
    intro ε h0 h1
    have := integrable_re_genH ha (hstrip ε h0 h1)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub]
    rw [poissonK_even]
  have hP : ∀ ε : ℝ, 0 < ε → ε < 1 → Integrable (poissonK ε) := fun ε h0 h1 => integrable_poissonK h0 h1
  have hFint : ∀ ε : ℝ, 0 < ε → ε < 1 → Integrable (F ε) := by
    intro ε h0 h1
    have : Integrable (fun t : ℝ => (a t * poissonK ε t - a 0 * poissonK ε t) / ε) :=
      ((hint ε h0 h1).sub ((hP ε h0 h1).const_mul (a 0))).div_const ε
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [hF]; ring
  -- representation of the quotient
  have hrep : ∀ᶠ ε : ℝ in 𝓝[>] 0, ((hbarA a (ε : ℂ)).re - a 0) / ε = ∫ t : ℝ, F ε t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    have hst := hstrip ε hε.1 hε.2
    rw [hbarA_of_mem_strip ha hst, re_genH ha hst]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_sub]
    simp only [poissonK_even]
    simp only [hF]
    rw [integral_div]
    congr 1
    have h1 : ∫ t : ℝ, (a t - a 0) * poissonK ε t =
        (∫ t : ℝ, a t * poissonK ε t) - a 0 * ∫ t : ℝ, poissonK ε t := by
      have : (fun t : ℝ => (a t - a 0) * poissonK ε t) =
          fun t => a t * poissonK ε t - a 0 * poissonK ε t := by funext t; ring
      rw [this, integral_sub (hint ε hε.1 hε.2) ((hP ε hε.1 hε.2).const_mul _), integral_const_mul]
    rw [h1, integral_poissonK hε.1 hε.2]; ring
  obtain ⟨Cb, hCb⟩ := slope_bound ha
  have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    simpa using this
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := F) (f := fun t => (a t - a 0) * (π * kern t))
    (fun t => Cb * Real.exp (-(1 * |t|)))
    (by filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        exact (hFint ε hε.1 hε.2).aestronglyMeasurable)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      filter_upwards [hae] with t ht
      have hε0 := hε.1
      have hsin : 0 < Real.sin (π * ε) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [hε.2])
      have hsin_le : Real.sin (π * ε) ≤ π * ε := Real.sin_le (by positivity)
      have hsh : 0 < Real.sinh (π * t) ^ 2 := by
        have : Real.sinh (π * t) ≠ 0 := by
          intro h; have := Real.sinh_eq_zero.mp h
          exact ht (by nlinarith)
        positivity
      have hPK : poissonK ε t / ε ≤ π * kern t := by
        rw [poissonK_eq hε.1 hε.2, kern, div_le_iff₀ hε0]
        have hc := Real.cosh_pos (π * t)
        calc Real.sin (π * ε) * Real.cosh (π * t) / (Real.sinh (π * t) ^ 2 + Real.sin (π * ε) ^ 2)
            ≤ Real.sin (π * ε) * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) hsh (by nlinarith [sq_nonneg (Real.sin (π * ε))])
          _ ≤ (π * ε) * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 := by gcongr
          _ = π * (Real.cosh (π * t) / Real.sinh (π * t) ^ 2) * ε := by ring
      have hPk0 : 0 ≤ poissonK ε t / ε := div_nonneg (poissonK_pos hε.1 hε.2 t).le hε0.le
      simp only [hF, Real.norm_eq_abs]
      rw [mul_div_assoc, abs_mul, abs_of_nonneg hPk0]
      calc |a t - a 0| * (poissonK ε t / ε) ≤ |a t - a 0| * (π * kern t) :=
            mul_le_mul_of_nonneg_left hPK (abs_nonneg _)
        _ ≤ Cb * Real.exp (-(1 * |t|)) := hCb t ht)
    ((integrable_exp_neg_mul_abs one_pos).const_mul Cb)
    (by
      filter_upwards [hae] with t ht
      have hsh : Real.sinh (π * t) ^ 2 ≠ 0 := by
        intro h
        have := pow_eq_zero_iff (two_ne_zero) |>.mp h
        have := Real.sinh_eq_zero.mp this
        exact ht (by nlinarith)
      have h1 : Tendsto (fun ε : ℝ => Real.sin (π * ε) / ε) (𝓝[>] 0) (𝓝 π) := tendsto_sin_pi_div
      have h2 : Tendsto (fun ε : ℝ => Real.cosh (π * t) / (Real.sinh (π * t) ^ 2 + Real.sin (π * ε) ^ 2))
          (𝓝[>] 0) (𝓝 (Real.cosh (π * t) / (Real.sinh (π * t) ^ 2 + Real.sin (π * 0) ^ 2))) := by
        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        refine (tendsto_const_nhds).div ?_ (by simpa using hsh)
        exact (continuous_const.add ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)).tendsto 0
      have h3 := ((h1.mul h2).const_mul (a t - a 0))
      have hk : (a t - a 0) * (π * (Real.cosh (π * t) / (Real.sinh (π * t) ^ 2 + Real.sin (π * 0) ^ 2))) =
          (a t - a 0) * (π * kern t) := by simp [kern]
      rw [hk] at h3
      refine h3.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      simp only [hF]
      rw [poissonK_eq hε.1 hε.2]
      field_simp)
  exact hlim.congr' (hrep.mono fun ε h => h.symm)

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.hbarA_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.hbarA_slope

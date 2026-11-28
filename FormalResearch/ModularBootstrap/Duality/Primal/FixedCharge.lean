module

public import FormalResearch.ModularBootstrap.WeightAxioms.HankelContinuation
public import FormalResearch.ModularBootstrap.WeightAxioms.ComplexAsymptotics

/-!
# Fixed-charge strip bound (`dsl:strip-fixed`(a), `dual_spectrum_limit.tex`)

Proves `dsl:strip-fixed`(a) at **every** fixed charge `c̃ > 0` with `12 S ≤ c̃`
(`prob : FixedWeightProblem`), removing the large-charge restriction `c̃ ≥ c₀(w, Q)` and the
hypothesis structure `FixedChargeStrip`:

* `kernelK_div_tendsto_zero`: for `0 ≤ a' < a`, `K_{a'}^{(w)}(t) / K_a^{(w)}(t) → 0` as `t → ∞`;
* `cardyV_div_kernelK_tendsto_one`: `V(t) / K_{c̃/12}^{(w)}(t) → 1` as `t → ∞`;
* `kernelK_le_mul_cardyV_fixed`: `K_{c̃/12}^{(w)}(t) ≤ C_K V(t)` on `[4/c̃, ∞)`;
* `testClass_integral_kernelK_le_fixed`, `hankelContinuationW_strip_bound_fixed`,
  `continuousOn_hankelContinuationW_fixed`, `differentiableOn_hankelContinuationW_fixed`,
  `tail_of_fixed`, and the bundled `dsl_strip_fixed_a`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing Bessel WeightAxioms

/-! ### Section 1: Fixed-charge asymptotics `K_{a'}/K_a → 0`, `V/K_a → 1`, and `K_a ≤ C V` -/

/-- `K_a^{(w)}(t) ≥ (2π t)^{w-1} · 4π² a t / w!` for `a, t ≥ 0`. -/
lemma kernelK_ge_linear (w : ℕ) (hw : 1 ≤ w) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (2 * π * t) ^ (w - 1) * (4 * π ^ 2 * a * t / (w.factorial : ℝ)) ≤ kernelK w a t := by
  unfold kernelK
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hnn : ∀ k, 0 ≤ kernelKTerm w a t k := fun k => by unfold kernelKTerm; positivity
  have h1 := (summable_kernelKTerm w a t).le_tsum 1 (fun k _ => hnn k)
  refine le_trans (le_of_eq ?_) h1
  unfold kernelKTerm
  have : (1 + w - 1) = w := by omega
  simp [this]

private lemma kernelK_zero_eq (w : ℕ) (_hw : 1 ≤ w) (t : ℝ) :
    kernelK w 0 t = (2 * π * t) ^ (w - 1) / ((w - 1).factorial : ℝ) := by
  unfold kernelK
  have heq : (∑' k : ℕ, kernelKTerm w 0 t k) = 1 / ((w - 1).factorial : ℝ) := by
    have hfn : kernelKTerm w 0 t = fun k => if k = 0 then 1 / ((w - 1).factorial : ℝ) else 0 := by
      ext k
      rcases k with _ | k
      · simp [kernelKTerm]
      · simp [kernelKTerm]
    rw [hfn, tsum_ite_eq]
  rw [heq, mul_one_div]

private lemma tendsto_sqrt_mul_exp_neg_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.sqrt (Real.sqrt t) * Real.exp (-c * Real.sqrt t)) atTop (𝓝 0) := by
  have hbd : ∀ᶠ t : ℝ in atTop,
      0 ≤ Real.sqrt (Real.sqrt t) * Real.exp (-c * Real.sqrt t) ∧
      Real.sqrt (Real.sqrt t) * Real.exp (-c * Real.sqrt t) ≤ 2 * (1 + Real.sqrt t) / (c ^ 2 * (Real.sqrt t) ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hst_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
    have hst_ge1 : 1 ≤ Real.sqrt t := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ht
    refine ⟨by positivity, ?_⟩
    have hsqrt_le : Real.sqrt (Real.sqrt t) ≤ 1 + Real.sqrt t := by
      nlinarith [sq_nonneg (Real.sqrt (Real.sqrt t) - 1), Real.sq_sqrt hst_pos.le]
    have hexp_ge : (c * Real.sqrt t) ^ 2 / 2 ≤ Real.exp (c * Real.sqrt t) := by
      have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ c * Real.sqrt t) 3
      have hsub : (∑ i ∈ Finset.range 3, (c * Real.sqrt t) ^ i / i.factorial) =
          1 + c * Real.sqrt t + (c * Real.sqrt t) ^ 2 / 2 := by
        simp [Finset.sum_range_succ, Nat.factorial]
      nlinarith [hst_pos]
    have hexp_neg : Real.exp (-c * Real.sqrt t) ≤ 2 / (c ^ 2 * (Real.sqrt t) ^ 2) := by
      rw [show -c * Real.sqrt t = -(c * Real.sqrt t) by ring, Real.exp_neg,
        inv_le_iff_one_le_mul₀ (by positivity)]
      have hsq : (c * Real.sqrt t) ^ 2 / 2 * (2 / (c ^ 2 * (Real.sqrt t) ^ 2)) = 1 := by
        field_simp [hc.ne', hst_pos.ne']
      calc (1 : ℝ)
          = (2 / (c ^ 2 * (Real.sqrt t) ^ 2)) * ((c * Real.sqrt t) ^ 2 / 2) := by linarith
        _ ≤ (2 / (c ^ 2 * (Real.sqrt t) ^ 2)) * Real.exp (c * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hexp_ge (by positivity)
    calc Real.sqrt (Real.sqrt t) * Real.exp (-c * Real.sqrt t)
        ≤ (1 + Real.sqrt t) * (2 / (c ^ 2 * (Real.sqrt t) ^ 2)) :=
          mul_le_mul hsqrt_le hexp_neg (by positivity) (by positivity)
      _ = 2 * (1 + Real.sqrt t) / (c ^ 2 * (Real.sqrt t) ^ 2) := by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (hbd.mono fun _ h => h.1) (hbd.mono fun _ h => h.2)
  have hrewrite : (fun t : ℝ => 2 * (1 + Real.sqrt t) / (c ^ 2 * (Real.sqrt t) ^ 2)) =ᶠ[atTop]
      fun t : ℝ => (2 / c ^ 2) * ((Real.sqrt t)⁻¹ ^ 2 + (Real.sqrt t)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp [hc.ne', hst]
  refine Tendsto.congr' hrewrite.symm ?_
  have hsqrt_atTop : Tendsto Real.sqrt atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun B => eventually_atTop.mpr ⟨max 0 B ^ 2, fun t ht => ?_⟩
    exact (le_max_right 0 B).trans ((Real.sqrt_sq (le_max_left 0 B)).symm.le.trans (Real.sqrt_le_sqrt ht))
  have hinv : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt_atTop
  have h0 := ((hinv.pow 2).add hinv).const_mul (2 / c ^ 2)
  simpa using h0

/-- For `1 ≤ w` and `0 ≤ a' < a`, `K_{a'}^{(w)}(t) / K_a^{(w)}(t) → 0` as `t → ∞`. -/
theorem kernelK_div_tendsto_zero (w : ℕ) (hw : 1 ≤ w) {a' a : ℝ} (ha' : 0 ≤ a') (ha : a' < a) :
    Tendsto (fun t : ℝ => kernelK w a' t / kernelK w a t) atTop (𝓝 0) := by
  have ha_pos : 0 < a := lt_of_le_of_lt ha' ha
  rcases eq_or_lt_of_le ha' with rfl | ha'_pos
  · have hbd : ∀ᶠ t : ℝ in atTop,
        0 ≤ kernelK w 0 t / kernelK w a t ∧
        kernelK w 0 t / kernelK w a t ≤ (w : ℝ) / (4 * π ^ 2 * a * t) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hK0_nn : 0 ≤ kernelK w 0 t := kernelK_nonneg le_rfl ht.le
      have hKa_lb := kernelK_ge_linear w hw ha_pos.le ht.le
      have hpow_pos : 0 < (2 * π * t) ^ (w - 1) := by positivity
      have hKa_pos : 0 < kernelK w a t := lt_of_lt_of_le (by positivity) hKa_lb
      refine ⟨div_nonneg hK0_nn hKa_pos.le, ?_⟩
      rw [kernelK_zero_eq w hw t, div_le_div_iff₀ hKa_pos (by positivity)]
      have hfac_eq : (w.factorial : ℝ) = (w : ℝ) * ((w - 1).factorial : ℝ) := by
        have hw1 : w = (w - 1) + 1 := by omega
        conv_lhs => rw [hw1, Nat.factorial_succ, Nat.cast_mul]
        rw [← hw1]
      have hfac_ne : ((w - 1).factorial : ℝ) ≠ 0 := by positivity
      have hw_ne : (w : ℝ) ≠ 0 := by positivity
      calc (2 * π * t) ^ (w - 1) / ((w - 1).factorial : ℝ) * (4 * π ^ 2 * a * t)
          = (w : ℝ) * ((2 * π * t) ^ (w - 1) * (4 * π ^ 2 * a * t / (w.factorial : ℝ))) := by
            rw [hfac_eq]; field_simp [hfac_ne, hw_ne]
        _ ≤ (w : ℝ) * kernelK w a t := mul_le_mul_of_nonneg_left hKa_lb (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (hbd.mono fun _ h => h.1) (hbd.mono fun _ h => h.2)
    have h0 : Tendsto (fun t : ℝ => (w : ℝ) / (4 * π ^ 2 * a) * t⁻¹) atTop (𝓝 0) := by
      convert tendsto_inv_atTop_zero.const_mul ((w : ℝ) / (4 * π ^ 2 * a)) using 2; ring
    exact h0.congr fun t => by ring
  · obtain ⟨C_I, hCI_nn, hI_bd⟩ := besselI_asymptotic_real (w - 1)
    let Z₀ : ℝ := max 1 (2 * C_I)
    have hZ₀_pos : 0 < Z₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let T₀ : ℝ := max 1 ((Z₀ / (4 * π)) ^ 2 / a)
    let c_diff : ℝ := 4 * π * (Real.sqrt a - Real.sqrt a')
    have hcdiff_pos : 0 < c_diff := mul_pos (by positivity) (sub_pos.mpr (Real.sqrt_lt_sqrt ha'_pos.le ha))
    let C_pre : ℝ := 2 * Real.sqrt (a / a') ^ (w - 1) * Real.sqrt (8 * π ^ 2 * Real.sqrt a)
    have hbd : ∀ᶠ t : ℝ in atTop,
        0 ≤ kernelK w a' t / kernelK w a t ∧
        kernelK w a' t / kernelK w a t ≤ C_pre * (Real.sqrt (Real.sqrt t) * Real.exp (-c_diff * Real.sqrt t)) := by
      filter_upwards [eventually_ge_atTop T₀] with t ht
      have ht_ge1 : 1 ≤ t := (le_max_left _ _).trans ht
      have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge1
      have ht_Z : (Z₀ / (4 * π)) ^ 2 / a ≤ t := (le_max_right _ _).trans ht
      let z : ℝ := 4 * π * Real.sqrt (a * t)
      have hz_pos : 0 < z := by dsimp [z]; positivity
      have hz_ge : Z₀ ≤ z := by
        dsimp [z]
        have h1 : (Z₀ / (4 * π)) ^ 2 ≤ a * t := (div_le_iff₀' ha_pos).mp ht_Z
        have h2 := Real.sqrt_le_sqrt h1
        rw [Real.sqrt_sq (by positivity)] at h2
        exact (div_le_iff₀' (by positivity : 0 < 4 * π)).mp h2
      have hCI_le : C_I / z ≤ 1 / 2 := by
        have h1 : 2 * C_I ≤ z := (le_max_right _ _).trans hz_ge
        rw [div_le_iff₀ hz_pos]; linarith
      have hAs_pos : 0 < besselAs z := besselAs_pos hz_pos
      have hI_lb : (1 / 2) * besselAs z ≤ besselI (w - 1) z := by
        have hsub : 1 / 2 ≤ besselI (w - 1) z / besselAs z := by linarith [(abs_le.mp (hI_bd hz_pos)).1]
        exact (le_div_iff₀ hAs_pos).mp hsub
      have hKa_eq := Crossing.kernelK_eq_besselI hw ha_pos ht_pos
      have hKa'_ub := kernelK_le_pow_mul_exp hw ha'_pos ht_pos.le
      have hKa_pos : 0 < kernelK w a t := by
        rw [hKa_eq]; exact mul_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) (lt_of_lt_of_le (by positivity) hI_lb)
      refine ⟨div_nonneg (kernelK_nonneg ha'_pos.le ht_pos.le) hKa_pos.le, ?_⟩
      have hratio_pow : Real.sqrt (t / a') ^ (w - 1) / Real.sqrt (t / a) ^ (w - 1) =
          Real.sqrt (a / a') ^ (w - 1) := by
        rw [← div_pow]
        congr 1
        rw [← Real.sqrt_div (by positivity)]
        congr 1
        field_simp [ha_pos.ne', ha'_pos.ne', ht_pos.ne']
      have hKa_lb : (1 / 2) * Real.sqrt (t / a) ^ (w - 1) * besselAs z ≤ kernelK w a t := by
        rw [hKa_eq]
        nlinarith [pow_nonneg (Real.sqrt_nonneg (t / a)) (w - 1)]
      have hsqrt_z : Real.sqrt (2 * π * z) = Real.sqrt (8 * π ^ 2 * Real.sqrt a) * Real.sqrt (Real.sqrt t) := by
        have h1 : 2 * π * z = (8 * π ^ 2 * Real.sqrt a) * Real.sqrt t := by
          dsimp [z]; rw [Real.sqrt_mul ha_pos.le]; ring
        rw [h1, Real.sqrt_mul (by positivity)]
      have hexp_ratio : Real.exp (4 * π * Real.sqrt (a' * t)) / besselAs z =
          Real.sqrt (8 * π ^ 2 * Real.sqrt a) * (Real.sqrt (Real.sqrt t) * Real.exp (-c_diff * Real.sqrt t)) := by
        unfold besselAs
        have harg : 4 * π * Real.sqrt (a' * t) - z = -c_diff * Real.sqrt t := by
          dsimp [z, c_diff]
          rw [Real.sqrt_mul ha'_pos.le, Real.sqrt_mul ha_pos.le]
          ring
        calc Real.exp (4 * π * Real.sqrt (a' * t)) / (Real.exp z / Real.sqrt (2 * π * z))
            = Real.sqrt (2 * π * z) * (Real.exp (4 * π * Real.sqrt (a' * t)) / Real.exp z) := by
              field_simp [(Real.exp_pos z).ne', (Real.sqrt_pos.mpr (by positivity : 0 < 2 * π * z)).ne']
          _ = (Real.sqrt (8 * π ^ 2 * Real.sqrt a) * Real.sqrt (Real.sqrt t)) *
                Real.exp (4 * π * Real.sqrt (a' * t) - z) := by rw [hsqrt_z, ← Real.exp_sub]
          _ = Real.sqrt (8 * π ^ 2 * Real.sqrt a) * (Real.sqrt (Real.sqrt t) * Real.exp (-c_diff * Real.sqrt t)) := by
                rw [harg]; ring
      calc kernelK w a' t / kernelK w a t
          ≤ (Real.sqrt (t / a') ^ (w - 1) * Real.exp (4 * π * Real.sqrt (a' * t))) /
              ((1 / 2) * Real.sqrt (t / a) ^ (w - 1) * besselAs z) :=
            div_le_div₀ (by positivity) hKa'_ub (by positivity) hKa_lb
        _ = 2 * (Real.sqrt (t / a') ^ (w - 1) / Real.sqrt (t / a) ^ (w - 1)) *
              (Real.exp (4 * π * Real.sqrt (a' * t)) / besselAs z) := by ring
        _ = C_pre * (Real.sqrt (Real.sqrt t) * Real.exp (-c_diff * Real.sqrt t)) := by
            rw [hratio_pow, hexp_ratio]; dsimp [C_pre]; ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (hbd.mono fun _ h => h.1) (hbd.mono fun _ h => h.2)
    simpa using (tendsto_sqrt_mul_exp_neg_atTop hcdiff_pos).const_mul C_pre

/-- At every fixed charge `c̃ > 0` with `12 S ≤ c̃`, `V(t) / K_{c̃/12}^{(w)}(t) → 1` as `t → ∞`. -/
theorem cardyV_div_kernelK_tendsto_one (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    Tendsto (fun t : ℝ => prob.cardyV (cTilde / 12) t / kernelK prob.w (cTilde / 12) t) atTop (𝓝 1) := by
  let a : ℝ := cTilde / 12
  have ha_pos : 0 < a := by positivity
  have hsh : prob.totalShift ≤ a := by dsimp [a]; linarith
  have hrew : (fun t : ℝ => prob.cardyV a t / kernelK prob.w a t) =ᶠ[atTop]
      fun t : ℝ => ∑ s : Finset (Fin prob.m),
        (-1 : ℝ) ^ s.card * (kernelK prob.w (a - prob.shiftSum s) t / kernelK prob.w a t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    unfold FixedWeightProblem.cardyV
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  refine Tendsto.congr' hrew.symm ?_
  have hterm : ∀ s : Finset (Fin prob.m),
      Tendsto (fun t : ℝ => (-1 : ℝ) ^ s.card * (kernelK prob.w (a - prob.shiftSum s) t / kernelK prob.w a t))
        atTop (𝓝 (if s = ∅ then (1 : ℝ) else 0)) := by
    intro s
    by_cases hs : s = ∅
    · subst hs
      simp only [Finset.card_empty, pow_zero, one_mul, ↓reduceIte, FixedWeightProblem.shiftSum,
        Finset.sum_empty, sub_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hK_pos : 0 < kernelK prob.w a t :=
        lt_of_lt_of_le (by positivity) (kernelK_ge_linear prob.w prob.hw ha_pos.le ht.le)
      exact (div_self hK_pos.ne').symm
    · simp only [hs, ↓reduceIte]
      have hs_ne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      obtain ⟨l₀, hl₀⟩ := hs_ne
      have hs_pos : 0 < prob.shiftSum s :=
        Finset.sum_pos' (fun l _ => (prob.hμ l).le) ⟨l₀, hl₀, prob.hμ l₀⟩
      have ha'_nn : 0 ≤ a - prob.shiftSum s :=
        sub_nonneg.mpr ((prob.shiftSum_le_totalShift s).trans hsh)
      have ha'_lt : a - prob.shiftSum s < a := sub_lt_self a hs_pos
      simpa using (kernelK_div_tendsto_zero prob.w prob.hw ha'_nn ha'_lt).const_mul ((-1 : ℝ) ^ s.card)
  have hsum : ∀ F : Finset (Finset (Fin prob.m)),
      Tendsto (fun t : ℝ => ∑ s ∈ F,
        (-1 : ℝ) ^ s.card * (kernelK prob.w (a - prob.shiftSum s) t / kernelK prob.w a t))
        atTop (𝓝 (∑ s ∈ F, if s = ∅ then (1 : ℝ) else 0)) := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp
    | insert s F hs ih => simpa [Finset.sum_insert hs] using (hterm s).add ih
  simpa using hsum Finset.univ

/-- **Fixed-charge kernel comparison** (`dsl:strip-fixed`(a)): for every `c̃ > 0` with `12 S ≤ c̃`,
there exists `C_K > 0` (depending on `prob` and `c̃`) such that `K_{c̃/12}^{(w)}(t) ≤ C_K V(t)` for all
`t ≥ 4 / c̃`. -/
theorem kernelK_le_mul_cardyV_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {t : ℝ}, 4 / cTilde ≤ t →
      kernelK prob.w (cTilde / 12) t ≤ C_K * prob.cardyV (cTilde / 12) t := by
  have ha_sh : prob.totalShift ≤ cTilde / 12 := by linarith
  have hlim := cardyV_div_kernelK_tendsto_one prob hc_pos hc
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  let R₁ : ℝ := max (4 / cTilde) R₀
  have h4_pos : 0 < 4 / cTilde := by positivity
  have hR₁_pos : 0 < R₁ := lt_of_lt_of_le h4_pos (le_max_left _ _)
  have hcont_K : Continuous (kernelK prob.w (cTilde / 12)) := continuous_kernelK prob.hw (cTilde / 12)
  have hcont_V : Continuous (prob.cardyV (cTilde / 12)) := continuous_cardyV prob (cTilde / 12)
  have hcont_ratio : ContinuousOn (fun t : ℝ => kernelK prob.w (cTilde / 12) t / prob.cardyV (cTilde / 12) t)
      (Icc (4 / cTilde) R₁) :=
    hcont_K.continuousOn.div hcont_V.continuousOn fun t ht =>
      (prob.cardyV_pos ha_sh (lt_of_lt_of_le h4_pos ht.1)).ne'
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_ratio
  refine ⟨max 2 M₀, by positivity, fun {t} ht => ?_⟩
  by_cases htop : R₁ ≤ t
  · have htR₀ : R₀ ≤ t := (le_max_right _ _).trans htop
    have ht_pos : 0 < t := lt_of_lt_of_le h4_pos ht
    have hK_pos : 0 < kernelK prob.w (cTilde / 12) t :=
      lt_of_lt_of_le (by positivity) (kernelK_ge_linear prob.w prob.hw (by positivity) ht_pos.le)
    have hdiv := hR₀ t htR₀
    rw [lt_div_iff₀ hK_pos] at hdiv
    have h2 : kernelK prob.w (cTilde / 12) t ≤ 2 * prob.cardyV (cTilde / 12) t := by linarith
    have hV_nn : 0 ≤ prob.cardyV (cTilde / 12) t := prob.cardyV_nonneg ha_sh ht_pos.le
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hV_nn)
  · push Not at htop
    have ht_mem : t ∈ Icc (4 / cTilde) R₁ := ⟨ht, htop.le⟩
    have ht_pos : 0 < t := lt_of_lt_of_le h4_pos ht
    have hV_pos : 0 < prob.cardyV (cTilde / 12) t := prob.cardyV_pos ha_sh ht_pos
    have hbd := hM₀ t ht_mem
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (kernelK_nonneg (by positivity) ht_pos.le) hV_pos.le),
      div_le_iff₀ hV_pos] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hV_pos.le)

/-! ### Section 2: Fixed-charge `L¹` kernel bound, strip bound, continuity, holomorphy, and tail -/

/-- **Fixed-charge `L¹` kernel bound** (`dsl:strip-fixed`(a)): for every `c̃ > 0` with `12 S ≤ c̃`,
there exists `C > 0` such that `∫₀^∞ |g(t)| K_{c̃/12}^{(w)}(t) dt ≤ C M[g]` for all `g ∈ Ā_w`. -/
theorem testClass_integral_kernelK_le_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    ∃ C_Kint : ℝ, 0 < C_Kint ∧ ∀ {g : ℝ → ℝ}, TestClass prob (cTilde / 12) g →
      IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (cTilde / 12) t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t ≤
        C_Kint * prob.cardyNorm (cTilde / 12) g := by
  have hw := prob.hw
  have ha_ge : prob.totalShift ≤ cTilde / 12 := by linarith
  obtain ⟨C_int, _, hCint_pos, _, hwin⟩ := testClass_window_bounds prob
  obtain ⟨C_K, hCK_pos, hK_bd⟩ := kernelK_le_mul_cardyV_fixed prob hc_pos hc
  let C_ker : ℝ := (2 * π) ^ (prob.w - 1) * Real.exp (4 * π / Real.sqrt 3)
  let C_head : ℝ := C_ker * C_int
  refine ⟨C_head + C_K, by positivity, fun {g} hg => ?_⟩
  have h4_pos : 0 < 4 / cTilde := div_pos (by norm_num) hc_pos
  have haesm : AEStronglyMeasurable (fun t : ℝ => |g t| * kernelK prob.w (cTilde / 12) t)
      (volume.restrict (Ioi 0)) :=
    (((hg.cont.abs.mono Ioi_subset_Ici_self).mul
      (continuous_kernelK hw (cTilde / 12)).continuousOn)).aestronglyMeasurable
      measurableSet_Ioi
  have hwin_bd := hwin ha_ge hg
  have hA_int : IntegrableOn (fun t : ℝ => |g t| * t ^ (prob.w - 1)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ‖t ^ (prob.w - 1) * g t‖) (Ioi 0) :=
      ((integrable_radialLift_iff hw g).1 hg.int_lift).norm
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le _), mul_comm]
  have hhead_dom : ∀ t ∈ Ioc (0 : ℝ) (4 / cTilde),
      ‖|g t| * kernelK prob.w (cTilde / 12) t‖ ≤ C_ker * (|g t| * t ^ (prob.w - 1)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have hK_nn : 0 ≤ kernelK prob.w (cTilde / 12) t := kernelK_nonneg (by positivity) ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hK_nn)]
    have hK_ub : kernelK prob.w (cTilde / 12) t ≤ C_ker * t ^ (prob.w - 1) := by
      unfold kernelK
      have hs_eq : (∑' j : ℕ, kernelKTerm prob.w (cTilde / 12) t j) =
          besselS (prob.w - 1) (4 * π ^ 2 * (cTilde / 12) * t) := by
        unfold besselS besselTerm kernelKTerm
        refine tsum_congr fun j => ?_
        rw [show j + prob.w - 1 = j + (prob.w - 1) by omega]
      rw [hs_eq]
      have hs_exp : besselS (prob.w - 1) (4 * π ^ 2 * (cTilde / 12) * t) ≤
          Real.exp (4 * π / Real.sqrt 3) := by
        have h1 := besselS_sq_div_four_le_exp (prob.w - 1)
          (u := 2 * Real.sqrt (4 * π ^ 2 * (cTilde / 12) * t)) (by positivity)
        have harg : (2 * Real.sqrt (4 * π ^ 2 * (cTilde / 12) * t)) ^ 2 / 4 =
            4 * π ^ 2 * (cTilde / 12) * t := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
        rw [harg] at h1
        have h1' : besselS (prob.w - 1) (4 * π ^ 2 * (cTilde / 12) * t) ≤
            Real.exp (2 * Real.sqrt (4 * π ^ 2 * (cTilde / 12) * t)) :=
          h1.trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast Nat.factorial_pos (prob.w - 1)))
        have hsqrt_le : 2 * Real.sqrt (4 * π ^ 2 * (cTilde / 12) * t) ≤ 4 * π / Real.sqrt 3 := by
          have h13 : (cTilde / 12) * t ≤ 1 / 3 := by
            calc (cTilde / 12) * t ≤ (cTilde / 12) * (4 / cTilde) := by gcongr; exact ht.2
              _ = 1 / 3 := by field_simp [hc_pos.ne']; norm_num
          have harg_le : 4 * π ^ 2 * (cTilde / 12) * t ≤ (2 * π / Real.sqrt 3) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num)]
            calc 4 * π ^ 2 * (cTilde / 12) * t = 4 * π ^ 2 * ((cTilde / 12) * t) := by ring
              _ ≤ 4 * π ^ 2 * (1 / 3) := by gcongr
              _ = (2 * π) ^ 2 / 3 := by ring
          have hsq := Real.sqrt_le_sqrt harg_le
          rw [Real.sqrt_sq (by positivity)] at hsq
          calc 2 * Real.sqrt (4 * π ^ 2 * (cTilde / 12) * t)
              ≤ 2 * (2 * π / Real.sqrt 3) := by gcongr
            _ = 4 * π / Real.sqrt 3 := by ring
        exact h1'.trans (Real.exp_le_exp.mpr hsqrt_le)
      calc (2 * π * t) ^ (prob.w - 1) * besselS (prob.w - 1) (4 * π ^ 2 * (cTilde / 12) * t)
          ≤ (2 * π * t) ^ (prob.w - 1) * Real.exp (4 * π / Real.sqrt 3) := by gcongr
        _ = C_ker * t ^ (prob.w - 1) := by dsimp [C_ker]; rw [mul_pow]; ring
    calc |g t| * kernelK prob.w (cTilde / 12) t ≤ |g t| * (C_ker * t ^ (prob.w - 1)) := by gcongr
      _ = C_ker * (|g t| * t ^ (prob.w - 1)) := by ring
  have hint_head : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (cTilde / 12) t) (Ioc 0 (4 / cTilde)) :=
    ((hA_int.mono_set Ioc_subset_Ioi_self).const_mul C_ker).mono' (haesm.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hhead_dom))
  have htail_dom : ∀ t ∈ Ioi (4 / cTilde),
      ‖|g t| * kernelK prob.w (cTilde / 12) t‖ ≤ C_K * (|g t| * prob.cardyV (cTilde / 12) t) := by
    intro t ht
    have ht0 : 0 ≤ t := (h4_pos.trans ht).le
    have hK_nn : 0 ≤ kernelK prob.w (cTilde / 12) t := kernelK_nonneg (by positivity) ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hK_nn)]
    have hbd := hK_bd (mem_Ioi.mp ht).le
    calc |g t| * kernelK prob.w (cTilde / 12) t
        ≤ |g t| * (C_K * prob.cardyV (cTilde / 12) t) := by gcongr
      _ = C_K * (|g t| * prob.cardyV (cTilde / 12) t) := by ring
  have hint_tail : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (cTilde / 12) t) (Ioi (4 / cTilde)) :=
    ((hg.int_cardy.mono_set (Ioi_subset_Ioi h4_pos.le)).const_mul C_K).mono'
      (haesm.mono_set (Ioi_subset_Ioi h4_pos.le))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall htail_dom))
  have hint_all : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (cTilde / 12) t) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi h4_pos.le]
    exact hint_head.union hint_tail
  refine ⟨hint_all, ?_⟩
  have hsplit : ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t =
      (∫ t in Ioc 0 (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t) +
      (∫ t in Ioi (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_head hint_tail,
      Ioc_union_Ioi_eq_Ioi h4_pos.le]
  have hhead_le : ∫ t in Ioc 0 (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t ≤
      C_head * prob.cardyNorm (cTilde / 12) g := by
    have h1 : ∫ t in Ioc 0 (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t ≤
        ∫ t in Ioc 0 (4 / cTilde), C_ker * (|g t| * t ^ (prob.w - 1)) := by
      refine setIntegral_mono_on hint_head ((hA_int.mono_set Ioc_subset_Ioi_self).const_mul C_ker)
        measurableSet_Ioc fun t ht => ?_
      have := hhead_dom t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (kernelK_nonneg (by positivity) ht.1.le))] at this
    have h2 : ∫ t in Ioc 0 (4 / cTilde), C_ker * (|g t| * t ^ (prob.w - 1)) ≤
        C_ker * ∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine setIntegral_mono_set hA_int ?_ Ioc_subset_Ioi_self.eventuallySubset
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (pow_nonneg (mem_Ioi.mp ht).le _))
    calc ∫ t in Ioc 0 (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t
        ≤ C_ker * ∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) := h1.trans h2
      _ ≤ C_ker * (C_int * prob.cardyNorm (cTilde / 12) g) :=
          mul_le_mul_of_nonneg_left hwin_bd.1 (by positivity)
      _ = C_head * prob.cardyNorm (cTilde / 12) g := by dsimp [C_head]; ring
  have htail_le : ∫ t in Ioi (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t ≤
      C_K * prob.cardyNorm (cTilde / 12) g := by
    have h1 : ∫ t in Ioi (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t ≤
        ∫ t in Ioi (4 / cTilde), C_K * (|g t| * prob.cardyV (cTilde / 12) t) := by
      refine setIntegral_mono_on hint_tail
        ((hg.int_cardy.mono_set (Ioi_subset_Ioi h4_pos.le)).const_mul C_K)
        measurableSet_Ioi fun t ht => ?_
      have := htail_dom t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (kernelK_nonneg (by positivity) (h4_pos.trans ht).le))] at this
    have h2 : ∫ t in Ioi (4 / cTilde), C_K * (|g t| * prob.cardyV (cTilde / 12) t) ≤
        C_K * prob.cardyNorm (cTilde / 12) g := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold FixedWeightProblem.cardyNorm
      refine setIntegral_mono_set hg.int_cardy ?_ (Ioi_subset_Ioi h4_pos.le).eventuallySubset
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha_ge (mem_Ioi.mp ht).le))
    exact h1.trans h2
  calc ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t
      = (∫ t in Ioc 0 (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t) +
          (∫ t in Ioi (4 / cTilde), |g t| * kernelK prob.w (cTilde / 12) t) := hsplit
    _ ≤ C_head * prob.cardyNorm (cTilde / 12) g + C_K * prob.cardyNorm (cTilde / 12) g :=
        add_le_add hhead_le htail_le
    _ = (C_head + C_K) * prob.cardyNorm (cTilde / 12) g := by ring

/-- Fixed-charge strip bound (`dsl:strip-fixed`(a)): `‖G(b)‖ ≤ 2π C M[g]` on `|Im b| ≤ 1/2`. -/
theorem hankelContinuationW_strip_bound_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    ∃ C_Kint : ℝ, 0 < C_Kint ∧ ∀ {g : ℝ → ℝ}, TestClass prob (cTilde / 12) g →
      ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
        ‖hankelContinuationW prob.w cTilde g b‖ ≤ 2 * π * C_Kint * prob.cardyNorm (cTilde / 12) g := by
  obtain ⟨C_Kint, hCK_pos, hK⟩ := testClass_integral_kernelK_le_fixed prob hc_pos hc
  refine ⟨C_Kint, hCK_pos, fun {g} hg {b} hb => ?_⟩
  obtain ⟨hint, hbd⟩ := hK hg
  have hnorm_int : ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)‖ ≤
      ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t := by
    calc ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖(g t : ℂ) * kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t := by
          refine setIntegral_mono_on ?_ hint measurableSet_Ioi fun t ht => ?_
          · have hintc : IntegrableOn (fun t : ℝ => (g t : ℂ) *
                kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)) (Ioi 0) := by
              refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
              · exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
                  ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
                  measurableSet_Ioi
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                exact mul_le_mul_of_nonneg_left
                  (norm_kernelKC_strip_le prob.w prob.hw hc_pos (mem_Ioi.mp hs).le hb) (abs_nonneg _)
            exact hintc.norm
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left
              (norm_kernelKC_strip_le prob.w prob.hw hc_pos (mem_Ioi.mp ht).le hb) (abs_nonneg _)
  unfold hankelContinuationW
  rw [norm_mul, show (-2 * (π : ℂ) : ℂ) = ((-(2 * π) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  calc 2 * π * ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)‖
      ≤ 2 * π * ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t := by gcongr
    _ ≤ 2 * π * (C_Kint * prob.cardyNorm (cTilde / 12) g) := by gcongr
    _ = 2 * π * C_Kint * prob.cardyNorm (cTilde / 12) g := by ring

/-- Fixed-charge closed-strip continuity (`dsl:strip-fixed`(a)). -/
theorem continuousOn_hankelContinuationW_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {g : ℝ → ℝ} (hg : TestClass prob (cTilde / 12) g) :
    ContinuousOn (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| ≤ 1 / 2} := by
  obtain ⟨_, _, hK⟩ := testClass_integral_kernelK_le_fixed prob hc_pos hc
  have hint := (hK hg).1
  intro b₀ hb₀
  unfold hankelContinuationW
  refine ContinuousWithinAt.mul continuousWithinAt_const ?_
  refine continuousWithinAt_of_dominated (bound := fun t => |g t| * kernelK prob.w (cTilde / 12) t) ?_ ?_ hint ?_
  · refine Eventually.of_forall fun b => ?_
    exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
      ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  · rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall fun b hb => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_kernelKC_strip_le prob.w prob.hw hc_pos (mem_Ioi.mp ht).le hb) (abs_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : Continuous fun b : ℂ => kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ) :=
      (kernelKC_entire_alpha prob.w (t : ℂ)).continuous.comp (by fun_prop)
    exact (continuous_const.mul h1).continuousAt

private lemma one_add_mul_besselS_le' (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ {u : ℝ}, 0 ≤ u → (u + 1) * besselS n (q * u) ≤ M * besselS n u := by
  have htend : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * q ^ k) atTop (𝓝 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
    have h0 : Tendsto (fun j : ℕ => ((j + 1 + n : ℕ) : ℝ) ^ 2 * q ^ j) atTop (𝓝 0) := by
      have hshift : Tendsto (fun j : ℕ => ((j + (1 + n) : ℕ) : ℝ) ^ 2 * q ^ (j + (1 + n))) atTop (𝓝 0) :=
        h2.comp (tendsto_add_atTop_nat (1 + n))
      by_cases hq0' : q = 0
      · subst hq0'
        refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun j hj => ?_)
        simp [Nat.ne_of_gt hj]
      · have hpow_ne : q ^ (1 + n) ≠ 0 := pow_ne_zero _ hq0'
        have hdiv := hshift.div_const (q ^ (1 + n))
        rw [zero_div] at hdiv
        refine hdiv.congr fun j => ?_
        rw [pow_add q j (1 + n), ← mul_assoc, mul_div_cancel_right₀ _ hpow_ne, add_assoc]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun j => by positivity) (fun j => ?_)
    have hle : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 + n : ℕ) : ℝ) := by push_cast; linarith
    calc ((j + 1 : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j
        ≤ ((j + 1 + n : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j := by gcongr
      _ = ((j + 1 + n : ℕ) : ℝ) ^ 2 * q ^ j := by ring
  obtain ⟨M₀, hM₀⟩ := htend.bddAbove_range
  let M₁ : ℝ := max 1 M₀
  have hM₁_pos : 0 < M₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨M₁ + 1, by positivity, fun {u} hu => ?_⟩
  have hj_bd : ∀ j : ℕ, ((j + 1 : ℝ) * (j + 1 + n : ℝ) * q ^ j) ≤ M₁ := fun j => by
    have h1 := hM₀ ⟨j, rfl⟩
    push_cast at h1
    exact h1.trans (le_max_right _ _)
  have hS0 : Summable fun j : ℕ => u * besselTerm n (q * u) j :=
    (summable_besselTerm n (mul_nonneg hq0 hu)).mul_left u
  have hSn_shift : Summable fun j : ℕ => M₁ * besselTerm n u (j + 1) :=
    ((summable_nat_add_iff 1).mpr (summable_besselTerm n hu)).mul_left M₁
  have hterm : ∀ j : ℕ, u * besselTerm n (q * u) j ≤ M₁ * besselTerm n u (j + 1) := by
    intro j
    unfold besselTerm
    have hj_ne : ((j + 1)! : ℝ) ≠ 0 := by positivity
    have hjn_ne : ((j + 1 + n)! : ℝ) ≠ 0 := by positivity
    have hid : u * ((q * u) ^ j / ((j ! : ℝ) * ((j + n)! : ℝ))) =
        ((j + 1 : ℝ) * (j + 1 + n : ℝ) * q ^ j) *
          (u ^ (j + 1) / (((j + 1)! : ℝ) * ((j + 1 + n)! : ℝ))) := by
      have hjf : ((j + 1)! : ℝ) = (j + 1 : ℝ) * (j ! : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      have hjnf : ((j + 1 + n)! : ℝ) = (j + 1 + n : ℝ) * ((j + n)! : ℝ) := by
        rw [show j + 1 + n = (j + n) + 1 by ring, Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      rw [mul_pow, pow_succ u j]
      field_simp [hj_ne, hjn_ne]
      rw [hjf, hjnf]; ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (hj_bd j) (by positivity)
  have hle_sum : u * besselS n (q * u) ≤ M₁ * ∑' j : ℕ, besselTerm n u (j + 1) := by
    unfold besselS; rw [← tsum_mul_left, ← tsum_mul_left]; exact hS0.tsum_le_tsum hterm hSn_shift
  have htail : ∑' j : ℕ, besselTerm n u (j + 1) ≤ besselS n u := by
    unfold besselS
    have hsp := (summable_besselTerm n hu).sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hsp
    have h0_nn : 0 ≤ besselTerm n u 0 := by unfold besselTerm; positivity
    linarith
  have hu_le : u * besselS n (q * u) ≤ M₁ * besselS n u :=
    hle_sum.trans (mul_le_mul_of_nonneg_left htail hM₁_pos.le)
  have h1_le : besselS n (q * u) ≤ besselS n u :=
    besselS_mono n (mul_nonneg hq0 hu) (mul_le_of_le_one_left hu hq1.le)
  linarith

private lemma continuous_besselSCSqDeriv' (n : ℕ) : Continuous (besselSCSqDeriv n) := by
  unfold besselSCSqDeriv
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z θ => (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ)) *
      ((Real.sin θ ^ (2 * n) : ℝ) : ℂ))
    (by fun_prop) 0 π

/-- Fixed-charge open-strip holomorphy (`dsl:strip-fixed`(a)). -/
theorem differentiableOn_hankelContinuationW_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {g : ℝ → ℝ} (hg : TestClass prob (cTilde / 12) g) :
    DifferentiableOn ℂ (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| < 1 / 2} := by
  have hw := prob.hw
  obtain ⟨_, _, hK⟩ := testClass_integral_kernelK_le_fixed prob hc_pos hc
  have hint := (hK hg).1
  intro b₀ hb₀
  let r : ℝ := (|b₀.im| + 1 / 2) / 2
  have hr_gt : |b₀.im| < r := by dsimp [r]; linarith [show |b₀.im| < 1 / 2 from hb₀]
  have hr_lt : r < 1 / 2 := by dsimp [r]; linarith [show |b₀.im| < 1 / 2 from hb₀]
  have hr_nn : 0 ≤ r := le_trans (abs_nonneg _) hr_gt.le
  let q : ℝ := 4 * r ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by dsimp [q]; nlinarith [hr_nn, hr_lt]
  obtain ⟨M_b, _, hMb⟩ := one_add_mul_besselS_le' (prob.w - 1) hq0 hq1
  let δ : ℝ := min (r - |b₀.im|) 1
  have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hr_gt) zero_lt_one
  let C_dom : ℝ := 2 * M_b
  let F : ℂ → ℝ → ℂ := fun b t => (g t : ℂ) * kernelKC prob.w (-(cTilde : ℂ) * b ^ 2 / 3) (t : ℂ)
  let zFun : ℂ → ℝ → ℂ := fun b t => 4 * (π : ℂ) * Complex.I * b * (Real.sqrt (cTilde * t / 3) : ℝ)
  let F' : ℂ → ℝ → ℂ := fun b t =>
    (g t : ℂ) * ((2 * (π : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
      (besselSCSqDeriv (prob.w - 1) (zFun b t) *
        (4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ))))
  have hball_bd : ∀ b ∈ Metric.ball b₀ δ, |b.im| ≤ r := fun b hb => by
    have hdist : ‖b - b₀‖ < δ := dist_eq_norm b b₀ ▸ Metric.mem_ball.mp hb
    have him : |b.im - b₀.im| ≤ ‖b - b₀‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - b₀)
    calc |b.im| = |(b.im - b₀.im) + b₀.im| := by ring_nf
      _ ≤ |b.im - b₀.im| + |b₀.im| := abs_add_le _ _
      _ ≤ δ + |b₀.im| := by linarith
      _ ≤ (r - |b₀.im|) + |b₀.im| := by gcongr; exact min_le_left _ _
      _ = r := by ring
  have hF_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun b =>
      ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
        ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
  have hF_int : Integrable (F b₀) (volume.restrict (Ioi 0)) := by
    refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    · exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
        ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · dsimp [F]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelKC_strip_le prob.w prob.hw hc_pos (mem_Ioi.mp ht).le (le_trans hr_gt.le hr_lt.le))
        (abs_nonneg _)
  have hF'_meas : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi 0)) := by
    have hcont_sq : Continuous fun t : ℝ => besselSCSqDeriv (prob.w - 1) (zFun b₀ t) :=
      (continuous_besselSCSqDeriv' (prob.w - 1)).comp (by fun_prop)
    have hcont_rest : ContinuousOn (fun t : ℝ =>
        (2 * (π : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
          (besselSCSqDeriv (prob.w - 1) (zFun b₀ t) *
            (4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)))) (Ioi 0) :=
      (((continuous_const.mul Complex.continuous_ofReal).pow (prob.w - 1)).mul
        (hcont_sq.mul (continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))))).continuousOn
    exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul hcont_rest).aestronglyMeasurable
      measurableSet_Ioi
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δ,
      ‖F' b t‖ ≤ C_dom * (|g t| * kernelK prob.w (cTilde / 12) t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht b hb => ?_)
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hbim := hball_bd b hb
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow,
      show 2 * (π : ℂ) * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * π * t), norm_mul]
    have hz_re : (zFun b t).re = -(4 * π * b.im * Real.sqrt (cTilde * t / 3)) := by
      dsimp [zFun]; simp [Complex.mul_re, Complex.mul_im]
    have hre_le : (zFun b t).re ^ 2 / 4 ≤ q * (4 * π ^ 2 * (cTilde / 12) * t) := by
      rw [hz_re]
      have hsq : Real.sqrt (cTilde * t / 3) ^ 2 = cTilde * t / 3 := Real.sq_sqrt (by positivity)
      have hb_sq : b.im ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs b.im]; exact pow_le_pow_left₀ (abs_nonneg _) hbim 2
      calc (-(4 * π * b.im * Real.sqrt (cTilde * t / 3))) ^ 2 / 4
          = 4 * π ^ 2 * (Real.sqrt (cTilde * t / 3)) ^ 2 * b.im ^ 2 := by ring
        _ = 4 * π ^ 2 * (cTilde * t / 3) * b.im ^ 2 := by rw [hsq]
        _ ≤ 4 * π ^ 2 * (cTilde * t / 3) * r ^ 2 := by gcongr
        _ = q * (4 * π ^ 2 * (cTilde / 12) * t) := by dsimp [q]; ring
    let u : ℝ := 4 * π ^ 2 * (cTilde / 12) * t
    have hu_nn : 0 ≤ u := by dsimp [u]; positivity
    have hderiv_sq : ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ ≤ besselS (prob.w - 1) (q * u) :=
      (besselSCSqDeriv_norm_le (prob.w - 1) (zFun b t)).trans (besselS_mono (prob.w - 1) (by positivity) hre_le)
    have hc_n : ‖4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)‖ ≤ 2 * (u + 1) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hsq_u : (2 * π * Real.sqrt (cTilde * t / 3)) ^ 2 = 4 * u := by
        dsimp [u]; rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
      have hsqrt_le : 2 * π * Real.sqrt (cTilde * t / 3) ≤ u + 1 := by
        nlinarith [sq_nonneg (2 * π * Real.sqrt (cTilde * t / 3) - 2), hsq_u]
      linarith
    have hK_eq : kernelK prob.w (cTilde / 12) t = (2 * π * t) ^ (prob.w - 1) * besselS (prob.w - 1) u := by
      unfold kernelK besselS besselTerm kernelKTerm
      congr 1; refine tsum_congr fun j => ?_; rw [show j + prob.w - 1 = j + (prob.w - 1) by omega]
    have hb_nn : 0 ≤ besselS (prob.w - 1) (q * u) := by
      unfold besselS; exact tsum_nonneg fun _ => by unfold besselTerm; positivity
    have hprod_le : ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
          ‖4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)‖ ≤
        M_b * (2 * besselS (prob.w - 1) u) := by
      calc ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
            ‖4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)‖
          ≤ besselS (prob.w - 1) (q * u) * (2 * (u + 1)) :=
            mul_le_mul hderiv_sq hc_n (norm_nonneg _) hb_nn
        _ = 2 * ((u + 1) * besselS (prob.w - 1) (q * u)) := by ring
        _ ≤ 2 * (M_b * besselS (prob.w - 1) u) := mul_le_mul_of_nonneg_left (hMb hu_nn) (by norm_num)
        _ = M_b * (2 * besselS (prob.w - 1) u) := by ring
    have hpow_nn : 0 ≤ (2 * π * t) ^ (prob.w - 1) := pow_nonneg (by positivity) _
    calc |g t| * ((2 * π * t) ^ (prob.w - 1) *
            (‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
              ‖4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)‖))
        ≤ |g t| * ((2 * π * t) ^ (prob.w - 1) * (M_b * (2 * besselS (prob.w - 1) u))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod_le hpow_nn) (abs_nonneg _)
      _ = C_dom * (|g t| * ((2 * π * t) ^ (prob.w - 1) * besselS (prob.w - 1) u)) := by
          dsimp [C_dom]; ring
      _ = C_dom * (|g t| * kernelK prob.w (cTilde / 12) t) := by rw [← hK_eq]
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δ,
      HasDerivAt (fun b => F b t) (F' b t) b := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht b _ => ?_)
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hz_deriv : HasDerivAt (fun b : ℂ => zFun b t)
        (4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)) b := by
      have hid : (fun b : ℂ => zFun b t) = fun b : ℂ =>
          b * (4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ)) := by
        ext w; dsimp [zFun]; ring
      rw [hid]; simpa using (hasDerivAt_id b).mul_const _
    have hS_deriv : HasDerivAt ((fun z : ℂ => besselSC (prob.w - 1) (z ^ 2 / 4)) ∘ fun b : ℂ => zFun b t)
        (besselSCSqDeriv (prob.w - 1) (zFun b t) *
          (4 * (π : ℂ) * Complex.I * (Real.sqrt (cTilde * t / 3) : ℝ))) b :=
      (hasDerivAt_besselSC_sq_div_four (prob.w - 1) (zFun b t)).comp b hz_deriv
    have hS_eq : (fun b : ℂ => besselSC (prob.w - 1) (4 * (π : ℂ) ^ 2 * (-(cTilde : ℂ) * b ^ 2 / 3) * (t : ℂ))) =
        fun b : ℂ => besselSC (prob.w - 1) ((zFun b t) ^ 2 / 4) := by
      ext w; congr 1; dsimp [zFun]
      have hsq : ((Real.sqrt (cTilde * t / 3) : ℝ) : ℂ) ^ 2 = ((cTilde * t / 3 : ℝ) : ℂ) := by
        exact_mod_cast Real.sq_sqrt (by positivity)
      calc 4 * (π : ℂ) ^ 2 * (-(cTilde : ℂ) * w ^ 2 / 3) * (t : ℂ)
          = (4 * (π : ℂ) * Complex.I * w) ^ 2 * ((cTilde * t / 3 : ℝ) : ℂ) / 4 := by
            rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]; push_cast; ring
        _ = (4 * (π : ℂ) * Complex.I * w) ^ 2 * ((Real.sqrt (cTilde * t / 3) : ℝ) : ℂ) ^ 2 / 4 := by
            rw [hsq]
        _ = _ := by ring
    have hK_eq_fn : (fun b : ℂ => F b t) = fun b : ℂ =>
        (g t : ℂ) * ((2 * (π : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
          besselSC (prob.w - 1) ((zFun b t) ^ 2 / 4)) := by
      ext w; dsimp [F, kernelKC]
      exact congrArg (fun x => (g t : ℂ) * ((2 * (π : ℂ) * (t : ℂ)) ^ (prob.w - 1) * x))
        (congrFun hS_eq w)
    rw [hK_eq_fn]
    dsimp [F']
    exact (hS_deriv.const_mul _).const_mul (g t : ℂ)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hδ_pos)
    hF_meas hF_int hF'_meas h_bound (hint.const_mul C_dom) h_diff).2
  unfold hankelContinuationW
  exact (hd.const_mul (-2 * (π : ℂ))).differentiableAt.differentiableWithinAt

/-- `t^{w-1} / V(t) → 0` at every fixed charge (`c̃ > 0`, `12 S ≤ c̃`). -/
theorem tail_of_fixed (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (prob.w - 1) ≤ ε * prob.cardyV (cTilde / 12) t := by
  obtain ⟨C_K, hCK, hK⟩ := kernelK_le_mul_cardyV_fixed prob hc_pos hc
  have ha : 0 < cTilde / 12 := by positivity
  have hw := prob.hw
  have hfac : (0 : ℝ) < (prob.w.factorial : ℝ) := by positivity
  intro ε hε
  set R₁ : ℝ := (prob.w.factorial : ℝ) * C_K /
    (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12)))) with hR₁
  refine ⟨max (4 / cTilde) R₁, fun t ht => ?_⟩
  have ht4 : 4 / cTilde ≤ t := (le_max_left _ _).trans ht
  have htR : R₁ ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht4
  have hVK := hK ht4
  have hKlin := kernelK_ge_linear prob.w hw ha.le ht0.le
  have hpow : 0 < (2 * π) ^ (prob.w - 1) := by positivity
  have htw : 0 < t ^ (prob.w - 1) := pow_pos ht0 _
  have hcoef : 0 < ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12))) := by positivity
  have h1 : (prob.w.factorial : ℝ) * C_K ≤ t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12)))) := by
    have := (div_le_iff₀ hcoef).1 htR
    linarith
  have h2 : (2 * π * t) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12) * t / (prob.w.factorial : ℝ)) ≤
      C_K * prob.cardyV (cTilde / 12) t := hKlin.trans hVK
  rw [mul_pow] at h2
  have h3 : t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * C_K) ≤
      t ^ (prob.w - 1) * (t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12))))) :=
    mul_le_mul_of_nonneg_left h1 htw.le
  have h4 : (prob.w.factorial : ℝ) * (C_K * prob.cardyV (cTilde / 12) t) ≥
      (2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12) * t) := by
    have := mul_le_mul_of_nonneg_left h2 hfac.le
    calc (prob.w.factorial : ℝ) * (C_K * prob.cardyV (cTilde / 12) t)
        ≥ (prob.w.factorial : ℝ) * ((2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) *
            (4 * π ^ 2 * (cTilde / 12) * t / (prob.w.factorial : ℝ))) := this
      _ = (2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12) * t) := by
          field_simp
  have h5 : t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * C_K) ≤
      (prob.w.factorial : ℝ) * (C_K * (ε * prob.cardyV (cTilde / 12) t)) := by
    calc t ^ (prob.w - 1) * ((prob.w.factorial : ℝ) * C_K)
        ≤ t ^ (prob.w - 1) * (t * (ε * ((2 * π) ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12))))) := h3
      _ = ε * ((2 * π) ^ (prob.w - 1) * t ^ (prob.w - 1) * (4 * π ^ 2 * (cTilde / 12) * t)) := by ring
      _ ≤ ε * ((prob.w.factorial : ℝ) * (C_K * prob.cardyV (cTilde / 12) t)) :=
          mul_le_mul_of_nonneg_left h4 hε.le
      _ = (prob.w.factorial : ℝ) * (C_K * (ε * prob.cardyV (cTilde / 12) t)) := by ring
  exact le_of_mul_le_mul_left (by linarith : (prob.w.factorial : ℝ) * C_K * t ^ (prob.w - 1) ≤
      (prob.w.factorial : ℝ) * C_K * (ε * prob.cardyV (cTilde / 12) t)) (mul_pos hfac hCK)

/-- **Lemma E'-S(a)** (`dsl:strip-fixed`(a), `dual_spectrum_limit.tex`) at every fixed charge
`c̃ > 0` with `12 S ≤ c̃`:
* uniform sup bound `‖g‖_∞ ≤ C₀ M[g]` with `C₀` independent of `c̃`;
* at every fixed `c̃`, `∫ |g| K_{c̃/12}^{(w)} dt ≤ C M[g]`, closed-strip continuity, open-strip
  holomorphy, and `sup_{|Im b| ≤ 1/2} |G(b)| ≤ 2π C M[g]`. -/
theorem dsl_strip_fixed_a (prob : FixedWeightProblem) :
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {cTilde : ℝ} {g : ℝ → ℝ}, 12 * prob.totalShift ≤ cTilde →
      TestClass prob (cTilde / 12) g → ∀ {t : ℝ}, 0 ≤ t →
        |g t| ≤ C₀ * prob.cardyNorm (cTilde / 12) g) ∧
    ∀ {cTilde : ℝ}, 0 < cTilde → 12 * prob.totalShift ≤ cTilde →
      ∃ C : ℝ, 0 < C ∧ ∀ {g : ℝ → ℝ}, TestClass prob (cTilde / 12) g →
        (∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (cTilde / 12) t ≤
          C * prob.cardyNorm (cTilde / 12) g) ∧
        ContinuousOn (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| ≤ 1 / 2} ∧
        DifferentiableOn ℂ (hankelContinuationW prob.w cTilde g) {b : ℂ | |b.im| < 1 / 2} ∧
        (∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
          ‖hankelContinuationW prob.w cTilde g b‖ ≤ 2 * π * C * prob.cardyNorm (cTilde / 12) g) := by
  refine ⟨?_, fun {cTilde} hc_pos hc => ?_⟩
  · obtain ⟨_, C₀, _, hC0, hwin⟩ := testClass_window_bounds prob
    exact ⟨C₀, hC0, fun {cTilde g} hc hg {t} ht => (hwin (by linarith) hg).2 ht⟩
  · obtain ⟨C, hC, hbd⟩ := hankelContinuationW_strip_bound_fixed prob hc_pos hc
    obtain ⟨C', _, hK⟩ := testClass_integral_kernelK_le_fixed prob hc_pos hc
    refine ⟨max C C', by positivity, fun {g} hg => ⟨?_,
      continuousOn_hankelContinuationW_fixed prob hc_pos hc hg,
      differentiableOn_hankelContinuationW_fixed prob hc_pos hc hg, fun {b} hb => ?_⟩⟩
    · have hM_nn : 0 ≤ prob.cardyNorm (cTilde / 12) g := prob.cardyNorm_nonneg (by linarith) g
      exact (hK hg).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM_nn)
    · have hM_nn : 0 ≤ prob.cardyNorm (cTilde / 12) g := prob.cardyNorm_nonneg (by linarith) g
      exact (hbd hg hb).trans (by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left C C') (by positivity : 0 ≤ 2 * π)) hM_nn
        linarith)

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.kernelK_le_mul_cardyV_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.kernelK_le_mul_cardyV_fixed

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.dsl_strip_fixed_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.dsl_strip_fixed_a

end FormalResearch.ModularBootstrap.FixedWeight

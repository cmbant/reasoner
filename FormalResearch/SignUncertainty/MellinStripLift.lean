module

public import FormalResearch.SignUncertainty.StripAdmissOrigin

/-!
# Lemma T.7 (`mat:T7`): Mellin-strip lift — inversion, vertical representation, and Hankel reflection

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.7 (`mat:T7`), parts (a), (b), (c).

Fix a real `c ≥ 2` and a strip multiplier `W : ℂ → ℂ` satisfying:
* `(W1)` (`StripW1 η W`, `η > 0`): holomorphic on `S = {0 < Re ζ < 1}`, continuous on `S̄ = {0 ≤ Re ζ ≤ 1}`,
  real-symmetric (`W(ζ̄) = conj W(ζ)`), and `‖W(σ + iτ)‖ ≤ C (1 + |τ|)^{-1/2 - η}` on `S̄`;
* `(W2)` (`StripW2 α W`, `0 < α ≤ 1`): endpoint `α`-Hölder continuity at `ζ = 0` and `ζ = 1`.

Main results:
* `mat_T7_a` (`mat:T7` (a)): `f_W` does not depend on `x₀ ∈ (0, c)`, is real, and extends continuously to `[0, ∞)`
  with `f_W(0) = W(1)` (real).
* `mat_T7_b` (`mat:T7` (b)): for `ξ > 0` and `0 ≤ σ < 1`, `(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W(σ + iτ) dτ`,
  with the integral converging absolutely.
* `mat_T7_c` (`mat:T7` (c)): if in addition `f_W ∈ L¹((0, ∞), ρ₀ dΔ)`, then `|f_W(Δ)| Δ^{x-1} ∈ L¹(0, ∞)` for
  every `x ∈ (0, c]`; the Mellin transform of `f_W` is `G(z) W(1 - z/c)` (equivalently normalized Mellin transform
  `e^{c ℋ(1 - z/c)} W(1 - z/c)`) on `0 < Re z ≤ c`; `W(1 - ·)` again satisfies `(W1)`–`(W2)`; the radial Hankel
  transform satisfies `𝓗_c f_W = f_{W(1 - ·)}` on `[0, ∞)` with `𝓗_c f_W(0) = W(0)` (real); and if
  `W(1 - ζ) = σ W(ζ)` (`σ ∈ ℝ`, in particular `σ = ±1`), then `𝓗_c f_W = σ f_W` and `f_W ∈ 𝒜_c^σ`.
* `mat_T7`: full Lemma T.7 combining (a), (b), (c).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- Hypothesis (W2) of `mat:T7` (Lemma T.7): endpoint `α`-Hölder continuity at `ζ = 0` and `ζ = 1`
(`0 < α ≤ 1` is a separate hypothesis). -/
structure StripW2 (α : ℝ) (W : ℂ → ℂ) : Prop where
  holder0 : ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ 1 / 2 → ‖W ζ - W 0‖ ≤ C * ‖ζ‖ ^ α
  holder1 : ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ C * ‖1 - ζ‖ ^ α

/-- Reflection `ζ ↦ 1 - ζ` preserves `(W2)`. -/
lemma StripW2.reflect {α : ℝ} {W : ℂ → ℂ} (hW : StripW2 α W) :
    StripW2 α (fun ζ => W (1 - ζ)) where
  holder0 := by
    obtain ⟨C, hC⟩ := hW.holder1
    refine ⟨C, fun ζ h0 h1 hn => ?_⟩
    have h := hC (1 - ζ) (by simp [h1]) (by simp [h0]) (by simpa using hn)
    simpa using h
  holder1 := by
    obtain ⟨C, hC⟩ := hW.holder0
    refine ⟨C, fun ζ h0 h1 hn => ?_⟩
    have h := hC (1 - ζ) (by simp [h1]) (by simp [h0]) (by simpa using hn)
    simpa using h

lemma W_one_im_of_W1 {η : ℝ} {W : ℂ → ℂ} (hW : StripW1 η W) : (W 1).im = 0 := by
  have := W_one_conj_of_W1 hW
  have h2 := congrArg Complex.im this
  simp only [Complex.conj_im] at h2
  linarith

lemma W_zero_im_of_W1 {η : ℝ} {W : ℂ → ℂ} (hW : StripW1 η W) : (W 0).im = 0 := by
  have h := hW.real 0 (by simp) (by simp)
  have h2 := congrArg Complex.im h
  simp only [map_zero, Complex.conj_im] at h2
  linarith

/-- **`mat:T7` (a), continuity:** `admissF c W` is continuous on `[0, ∞)` under `(W1)` (`η > 0`) and `(W2)` at `1` (`0 < α ≤ 1`). -/
theorem admissF_continuousOn_of_W1 {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hW : StripW1 η W)
    (hH1 : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    ContinuousOn (admissF c W) (Ici 0) := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 hc1 hη hW
  have hcont : ContinuousOn (admissLift c W) (Ioi 0) :=
    continuousOn_liftFun hΦ (x₀ := c / 2) (by linarith) (by linarith)
  have hev : ∀ Δ : ℝ, 0 < Δ → admissF c W =ᶠ[𝓝 Δ] admissLift c W := fun Δ hΔ => by
    filter_upwards [Ioi_mem_nhds hΔ] with x hx
    simp [admissF, ne_of_gt hx]
  intro Δ hΔ
  rcases (mem_Ici.mp hΔ).eq_or_lt with h0 | hpos
  · subst h0
    refine continuousWithinAt_Ioi_iff_Ici.mp ?_
    have hlim := admiss_lift_tendsto_of_W1 hc hη hα0 hα1 hW hH1
    have h0 : admissF c W 0 = (W 1).re := by simp [admissF]
    unfold ContinuousWithinAt
    rw [h0]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [admissF, ne_of_gt (show 0 < x from hx)]
  · exact ((hcont.continuousAt (Ioi_mem_nhds hpos)).congr (hev Δ hpos).symm).continuousWithinAt

/-! ### Integrability and continuity of `mellinRaw` from continuity on `[0, ∞)` and `L¹(ρ₀)` -/

/-- Any function continuous on `[0, ∞)` with `f ρ₀ ∈ L¹(0, ∞)` satisfies `|f(Δ)| Δ^{x-1} ∈ L¹(0, ∞)`
for every `0 < x ≤ c`. -/
theorem integrableOn_abs_mul_rpow_of_cont_int {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ici 0)) (hint : IntegrableOn (fun Δ : ℝ => f Δ * hankelRho0 c Δ) (Ioi 0))
    {x : ℝ} (hx0 : 0 < x) (hxc : x ≤ c) :
    IntegrableOn (fun Δ : ℝ => |f Δ| * Δ ^ (x - 1)) (Ioi 0) := by
  have hmeas : ∀ t : Set ℝ, MeasurableSet t → t ⊆ Ioi 0 →
      AEStronglyMeasurable (fun Δ : ℝ => |f Δ| * Δ ^ (x - 1)) (volume.restrict t) :=
    fun t ht hts => ContinuousOn.aestronglyMeasurable
      ((continuous_abs.comp_continuousOn (hcont.mono fun Δ hΔ => le_of_lt (hts hΔ))).mul
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (ne_of_gt (hts hw)))) ht
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (f := f) (hcont.mono fun Δ hΔ => hΔ.1)
    have hI : IntegrableOn (fun Δ : ℝ => K * Δ ^ (x - 1)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < x - 1))).const_mul K
    refine Integrable.mono' hI (hmeas _ measurableSet_Ioc fun Δ hΔ => hΔ.1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hΔ.1.le _)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hK Δ ⟨hΔ.1.le, hΔ.2⟩)
      (Real.rpow_nonneg hΔ.1.le _)
  · have hρ := abs_mul_rho0_integrableOn hc hint
    have hI : IntegrableOn (fun Δ : ℝ => (Real.Gamma c / (2 * π) ^ c) *
        (|f Δ| * hankelRho0 c Δ)) (Ioi 1) := (hρ.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    refine Integrable.mono' hI (hmeas _ measurableSet_Ioi fun Δ hΔ => lt_trans zero_lt_one hΔ) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
    have hΔ0 : 0 < Δ := lt_trans zero_lt_one hΔ
    have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
    have hp : 0 < (2 * π) ^ c := Real.rpow_pos_of_pos (by positivity) c
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hΔ0.le _)]
    have hle : Δ ^ (x - 1) ≤ Δ ^ (c - 1) :=
      Real.rpow_le_rpow_of_exponent_le hΔ.le (by linarith)
    have e : (Real.Gamma c / (2 * π) ^ c) * (|f Δ| * hankelRho0 c Δ) = |f Δ| * Δ ^ (c - 1) := by
      unfold hankelRho0; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- Continuity of `mellinRaw f` on `0 < Re z ≤ c` from continuity of `f` on `[0, ∞)` and `f ρ₀ ∈ L¹(0, ∞)`. -/
theorem continuousOn_mellinRaw_of_cont_int {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ici 0)) (hint : IntegrableOn (fun Δ : ℝ => f Δ * hankelRho0 c Δ) (Ioi 0)) :
    ContinuousOn (mellinRaw f) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  have hfc : ContinuousOn f (Ioi 0) := hcont.mono Ioi_subset_Ici_self
  have haesm : ∀ z : ℂ, AEStronglyMeasurable (fun Δ : ℝ => (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1)) (volume.restrict (Ioi 0)) :=
    fun z => ContinuousOn.aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_continuousOn hfc).mul
        (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
          fun w hw => Or.inl (by simpa using (mem_Ioi.mp hw)))) measurableSet_Ioi
  have key : ∀ x0 : ℝ, 0 < x0 → x0 ≤ c →
      ContinuousOn (mellinRaw f) {z : ℂ | x0 ≤ z.re ∧ z.re ≤ c} := by
    intro x0 hx0 hx0c
    have hb : IntegrableOn (fun Δ : ℝ => |f Δ| * Δ ^ (x0 - 1) + |f Δ| * Δ ^ (c - 1)) (Ioi 0) :=
      (integrableOn_abs_mul_rpow_of_cont_int hc hcont hint hx0 hx0c).add
        (integrableOn_abs_mul_rpow_of_cont_int hc hcont hint hc le_rfl)
    refine continuousOn_of_dominated (bound := fun Δ => |f Δ| * Δ ^ (x0 - 1) + |f Δ| * Δ ^ (c - 1))
      (fun z _ => haesm z) ?_ hb ?_
    · intro z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
      have hΔ0 : 0 < Δ := hΔ
      rw [norm_mul, norm_cpow_sub_one hΔ0, Complex.norm_real, Real.norm_eq_abs]
      have hnn0 : 0 ≤ |f Δ| * Δ ^ (x0 - 1) := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hΔ0.le _)
      have hnn1 : 0 ≤ |f Δ| * Δ ^ (c - 1) := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hΔ0.le _)
      rcases le_total Δ 1 with h1 | h1
      · have : Δ ^ (z.re - 1) ≤ Δ ^ (x0 - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ0 h1 (by linarith [hz.1])
        nlinarith [abs_nonneg (f Δ)]
      · have : Δ ^ (z.re - 1) ≤ Δ ^ (c - 1) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hz.2])
        nlinarith [abs_nonneg (f Δ)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
      have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mem_Ioi.mp hΔ))
      exact (continuous_const.mul
        (Continuous.const_cpow (continuous_id.sub continuous_const) (Or.inl hΔ0))).continuousOn
  intro z hz
  have h := (key (z.re / 2) (by linarith [hz.1]) (by linarith [hz.1, hz.2])).continuousWithinAt
    (show z ∈ {w : ℂ | z.re / 2 ≤ w.re ∧ w.re ≤ c} from ⟨by linarith [hz.1], hz.2⟩)
  have hnhds : {w : ℂ | z.re / 2 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; linarith [hz.1])
  rw [← continuousWithinAt_inter hnhds]
  refine h.mono ?_
  rintro w ⟨hw, hw'⟩
  exact ⟨le_of_lt hw', hw.2⟩

/-! ### Mellin transform on `0 < Re z ≤ c` and Hankel reflection (`mat:T7` (c)) -/

/-- **`mat:T7` (c), Mellin transform on `0 < Re z ≤ c`:** if `f_W ∈ L¹(ρ₀)`, then
`mellinRaw (admissF c W) z = admissPhi c W z` (`= G(z) W(1 - z/c)`) for all `0 < Re z ≤ c`. -/
theorem mellinRaw_admissF_eq_of_W1 {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hW1 : StripW1 η W) (hW2 : StripW2 α W)
    (hint : IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0))
    {z : ℂ} (hz0 : 0 < z.re) (hzc : z.re ≤ c) :
    mellinRaw (admissF c W) z = admissPhi c W z := by
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 (c := c) (by linarith) hη hW1
  have hopen : ∀ w : ℂ, 0 < w.re → w.re < c → mellinRaw (admissF c W) w = admissPhi c W w := by
    intro w hw0 hwc
    have heq : mellinRaw (admissF c W) w = mellinRaw (admissLift c W) w := by
      unfold mellinRaw
      refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
      simp [admissF, ne_of_gt (show 0 < Δ from hΔ)]
    rw [heq]
    exact mellinRaw_liftFun hΦ (x₀ := c / 2) (by linarith) (by linarith) hw0 hwc
  rcases hzc.eq_or_lt with hzceq | hzclt
  · have hFcont := admissF_continuousOn_of_W1 hc hη hα0 hα1 hW1 hW2.holder1
    have hMcont := continuousOn_mellinRaw_of_cont_int hc0 hFcont hint
    have hPcont := admissPhi_continuousOn_edge_of_W1 hc0 hW1
    set γ : ℝ → ℂ := fun x => (x : ℂ) + (z.im : ℂ) * Complex.I with hγ
    have hγc : γ c = z := by
      apply Complex.ext <;> simp [hγ, hzceq]
    have hγ_tendsto : Tendsto γ (𝓝[<] c) (𝓝[{w : ℂ | 0 < w.re ∧ w.re ≤ c}] z) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous γ := by simp only [hγ]; fun_prop
        rw [← hγc]
        exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT hc0] with x hx
        exact ⟨by simp [hγ]; exact hx.1, by simp [hγ]; exact hx.2.le⟩
    have hL : Tendsto (fun x : ℝ => mellinRaw (admissF c W) (γ x)) (𝓝[<] c) (𝓝 (mellinRaw (admissF c W) z)) :=
      (hMcont z ⟨hz0, hzc⟩).tendsto.comp hγ_tendsto
    have hR : Tendsto (fun x : ℝ => admissPhi c W (γ x)) (𝓝[<] c) (𝓝 (admissPhi c W z)) :=
      (hPcont z ⟨hz0, hzc⟩).tendsto.comp hγ_tendsto
    have hev : (fun x : ℝ => mellinRaw (admissF c W) (γ x)) =ᶠ[𝓝[<] c] (fun x : ℝ => admissPhi c W (γ x)) := by
      filter_upwards [Ioo_mem_nhdsLT hc0] with x hx
      exact hopen (γ x) (by simp [hγ]; exact hx.1) (by simp [hγ]; exact hx.2)
    exact tendsto_nhds_unique hL (hR.congr' hev.symm)
  · exact hopen z hz0 hzclt

/-- **`mat:T7` (c), normalized Mellin transform on `0 < Re z ≤ c`:**
`mellinStrip (admissF c W) z = e^{c ℋ(1 - z/c)} W(1 - z/c)`. -/
theorem mellinStrip_admissF_eq_of_W1 {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hW1 : StripW1 η W) (hW2 : StripW2 α W)
    (hint : IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0))
    {z : ℂ} (hz0 : 0 < z.re) (hzc : z.re ≤ c) :
    mellinStrip (admissF c W) z = Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c) := by
  unfold mellinStrip
  rw [mellinRaw_admissF_eq_of_W1 hc hη hα0 hα1 hW1 hW2 hint hz0 hzc]
  unfold admissPhi admissG
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hpow : ((2 * Real.pi : ℝ) : ℂ) ^ z * ((2 * Real.pi : ℝ) : ℂ) ^ (-z) = 1 := by
    rw [← Complex.cpow_add _ _ hpi, add_neg_cancel, Complex.cpow_zero]
  calc ((2 * Real.pi : ℝ) : ℂ) ^ z / Complex.Gamma z *
        (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c))
      = (((2 * Real.pi : ℝ) : ℂ) ^ z * ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) * (Complex.Gamma z / Complex.Gamma z) *
          (Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c)) := by ring
    _ = _ := by rw [hpow, div_self hGz]; ring

/-- Reflection identity for the normalized multiplier `mellinMult (admissPhi c W)` (`ℋ(1 - ζ) = ℋ(ζ)`). -/
lemma mellinMult_admissPhi_reflect {c : ℝ} (hc : 0 < c) (W : ℂ → ℂ) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    mellinMult (admissPhi c W) ((c : ℂ) - z) = mellinMult (admissPhi c (fun ζ => W (1 - ζ))) z := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpow : ∀ w : ℂ, ((2 * Real.pi : ℝ) : ℂ) ^ w * ((2 * Real.pi : ℝ) : ℂ) ^ (-w) = 1 := fun w => by
    rw [← Complex.cpow_add _ _ hpi, add_neg_cancel, Complex.cpow_zero]
  have hre0 : 0 < (z / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hre1 : (z / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; exact (div_lt_one hc).mpr hz1
  have harg : 1 - ((c : ℂ) - z) / c = z / c := by field_simp; ring
  have harg2 : 1 - (1 - z / (c : ℂ)) = z / c := by ring
  have hH : stripH (1 - z / c) = stripH (z / c) := stripH_one_sub hre0 hre1
  unfold mellinMult admissPhi admissG
  have hL : ((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) - z) / Complex.Gamma ((c : ℂ) - z) *
      (((2 * Real.pi : ℝ) : ℂ) ^ (-((c : ℂ) - z)) * Complex.Gamma ((c : ℂ) - z) *
        Complex.exp ((c : ℂ) * stripH (1 - ((c : ℂ) - z) / c)) * W (1 - ((c : ℂ) - z) / c)) =
      Complex.exp ((c : ℂ) * stripH (z / c)) * W (z / c) := by
    rw [harg]
    calc _ = (((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) - z) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((c : ℂ) - z))) *
          (Complex.Gamma ((c : ℂ) - z) / Complex.Gamma ((c : ℂ) - z)) *
          (Complex.exp ((c : ℂ) * stripH (z / c)) * W (z / c)) := by ring
      _ = _ := by rw [hpow, div_self hGc]; ring
  have hR : ((2 * Real.pi : ℝ) : ℂ) ^ z / Complex.Gamma z *
      (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z *
        Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - (1 - z / c))) =
      Complex.exp ((c : ℂ) * stripH (z / c)) * W (z / c) := by
    rw [harg2, hH]
    calc _ = (((2 * Real.pi : ℝ) : ℂ) ^ z * ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) *
          (Complex.Gamma z / Complex.Gamma z) *
          (Complex.exp ((c : ℂ) * stripH (z / c)) * W (z / c)) := by ring
      _ = _ := by rw [hpow, div_self hGz]; ring
  rw [hL, hR]

/-- **`mat:T7` (c), Hankel reflection on `[0, ∞)`:**
`besselHankelTransform c (admissF c W) Δ = admissF c (fun ζ => W (1 - ζ)) Δ` for all `Δ ≥ 0`. -/
theorem besselHankelTransform_admissF_of_W1 {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hW1 : StripW1 η W) (hW2 : StripW2 α W)
    (hint : IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0)) :
    ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c (admissF c W) Δ = admissF c (fun ζ => W (1 - ζ)) Δ := by
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 (c := c) (by linarith) hη hW1
  have hΨ := admissPhi_mellinLiftData_of_W1 (c := c) (by linarith) hη hW1.reflect
  have hintL : IntegrableOn (fun Δ : ℝ => liftFun (admissPhi c W) (c / 2) Δ * hankelRho0 c Δ) (Ioi 0) :=
    hint.congr_fun (fun Δ hΔ => by simp [admissF, admissLift, ne_of_gt (show 0 < Δ from hΔ)]) measurableSet_Ioi
  have hpos : ∀ Δ : ℝ, 0 < Δ → besselHankelTransform c (admissF c W) Δ = admissF c (fun ζ => W (1 - ζ)) Δ := by
    intro Δ hΔ
    have hEq : besselHankelTransform c (admissF c W) Δ = besselHankelTransform c (admissLift c W) Δ := by
      unfold besselHankelTransform
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      simp [admissF, ne_of_gt (show 0 < s from hs)]
    rw [hEq]
    have hpair := besselHankelTransform_liftFun_pair hΦ hΨ hc32 (x₀ := c / 2) (y₀ := c / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun z hz0 hz1 => mellinMult_admissPhi_reflect hc0 W hz0 hz1) hintL hΔ
    simpa [admissF, admissLift, ne_of_gt hΔ] using hpair
  intro Δ hΔ
  rcases (mem_Ici.mp hΔ).eq_or_lt with rfl | hΔpos
  · have hHcont : Continuous (besselHankelTransform c (admissF c W)) :=
      besselHankelTransform_continuous (by linarith) hint
    have hRcont : ContinuousOn (admissF c (fun ζ => W (1 - ζ))) (Ici 0) :=
      admissF_continuousOn_of_W1 hc hη hα0 hα1 hW1.reflect hW2.reflect.holder1
    have hL : Tendsto (besselHankelTransform c (admissF c W)) (𝓝[>] (0 : ℝ))
        (𝓝 (besselHankelTransform c (admissF c W) 0)) :=
      hHcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hR : Tendsto (admissF c (fun ζ => W (1 - ζ))) (𝓝[>] (0 : ℝ))
        (𝓝 (admissF c (fun ζ => W (1 - ζ)) 0)) :=
      (continuousWithinAt_Ioi_iff_Ici.mpr (hRcont 0 le_rfl)).tendsto
    have hev : besselHankelTransform c (admissF c W) =ᶠ[𝓝[>] (0 : ℝ)] admissF c (fun ζ => W (1 - ζ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hpos x hx
    exact tendsto_nhds_unique hL (hR.congr' hev.symm)
  · exact hpos Δ hΔpos

/-- Pointwise scaling on the strip `0 ≤ Re ζ ≤ 1` scales `admissF c W` on `[0, ∞)`. -/
lemma admissF_eq_const_mul {c σ : ℝ} {W W' : ℂ → ℂ} (hc : 0 < c)
    (heq : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W' ζ = (σ : ℂ) * W ζ) :
    ∀ Δ ∈ Ici (0 : ℝ), admissF c W' Δ = σ * admissF c W Δ := by
  intro Δ hΔ
  rcases (mem_Ici.mp hΔ).eq_or_lt with rfl | hΔpos
  · simp only [admissF, ite_true]
    have h1 := heq 1 (by simp) (by simp)
    rw [h1]
    simp
  · simp only [admissF, ne_of_gt hΔpos, ite_false, admissLift, liftFun, mellinInv]
    have hint : (∫ y : ℝ, (Δ : ℂ) ^ (-(((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) •
          admissPhi c W' (((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
        (σ : ℂ) * ∫ y : ℝ, (Δ : ℂ) ^ (-(((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) •
          admissPhi c W (((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      have hre : (1 - (((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ)).re = 1 / 2 := by
        rw [re_one_sub_div hc]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        field_simp; ring
      have hw := heq (1 - (((c / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) / (c : ℂ))
        (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      dsimp only
      unfold admissPhi
      rw [hw, smul_eq_mul, smul_eq_mul]
      ring
    rw [hint, Complex.real_smul, Complex.real_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

/-! ### Headline statements for Lemma T.7 (`mat:T7`) -/

/-- **Lemma T.7 (`mat:T7`), part (a)** (Mellin-strip lift: line independence, reality, continuity up to `0`).

Fix `c ≥ 2`, `η > 0`, `α ∈ (0, 1]` and `W : ℂ → ℂ` satisfying `(W1)` (`StripW1 η W`) and `(W2)` (`StripW2 α W`).
Then the inverse Mellin lift `f_W` does not depend on `x₀ ∈ (0, c)`, is real-valued, and its extension
`admissF c W` is continuous on `[0, ∞)` with `admissF c W 0 = (W 1).re` and `(W 1).im = 0`.

Scope and limitations: matches `mat:T7` (a) of `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`
with no extra hypotheses (in fact only `(W2)` at `ζ = 1` is used). -/
theorem mat_T7_a {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW1 : StripW1 η W) (hW2 : StripW2 α W) :
    (∀ x₀ x₁ : ℝ, 0 < x₀ → x₀ < c → 0 < x₁ → x₁ < c → ∀ Δ : ℝ, 0 < Δ →
      liftFun (admissPhi c W) x₀ Δ = liftFun (admissPhi c W) x₁ Δ) ∧
    (∀ x₀ : ℝ, 0 < x₀ → x₀ < c → ∀ Δ : ℝ, 0 < Δ → (mellinInv x₀ (admissPhi c W) Δ).im = 0) ∧
    ContinuousOn (admissF c W) (Ici 0) ∧ admissF c W 0 = (W 1).re ∧ (W 1).im = 0 := by
  have hΦ := admissPhi_mellinLiftData_of_W1 (c := c) (by linarith) hη hW1
  refine ⟨fun x₀ x₁ hx0 hx1 hy0 hy1 Δ hΔ => ?_, fun x₀ hx0 hx1 Δ hΔ => hΦ.im_mellinInv hx0 hx1 hΔ,
    admissF_continuousOn_of_W1 hc hη hα0 hα1 hW1 hW2.holder1, by simp [admissF], W_one_im_of_W1 hW1⟩
  unfold liftFun
  rw [hΦ.mellinInv_indep hx0 hx1 hy0 hy1 hΔ]

/-- **Lemma T.7 (`mat:T7`), part (b)** (vertical-line representation and absolute convergence).

Fix `c ≥ 2`, `η > 0` and `W : ℂ → ℂ` satisfying `(W1)` (`StripW1 η W`). Then for every `ξ > 0` and
`σ ∈ [0, 1)`, the integral `∫ K₀(σ + iτ, ξ) W(σ + iτ) dτ` converges absolutely and
`(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W(σ + iτ) dτ`.

Scope and limitations: matches `mat:T7` (b) of `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`
with no extra hypotheses (in fact `c ≥ 1` suffices and `(W2)` is not needed). -/
theorem mat_T7_b {c η : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η) (hW1 : StripW1 η W) :
    ∀ ξ : ℝ, 0 < ξ → ∀ σ : ℝ, 0 ≤ σ → σ < 1 →
      Integrable (fun τ : ℝ => mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)) ∧
      (((hankelRho0 c (c * ξ) * admissF c W (c * ξ) : ℝ)) : ℂ) =
        ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
          ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
  intro ξ hξ σ hσ0 hσ1
  have hc1 : 1 ≤ c := by linarith
  have hcξ : 0 < c * ξ := by positivity
  refine ⟨admiss_vert_integrable_of_W1 hc1 hη hW1 hσ0 hσ1 hξ, ?_⟩
  simp only [admissF, ne_of_gt hcξ, ite_false]
  exact admiss_vert_rep_of_W1 hc1 hη hW1 hσ0 hσ1 hξ

/-- **Lemma T.7 (`mat:T7`), part (c)** (Mellin transform and Hankel reflection for a general lift).

Fix `c ≥ 2`, `η > 0`, `α ∈ (0, 1]` and `W : ℂ → ℂ` satisfying `(W1)` (`StripW1 η W`) and `(W2)` (`StripW2 α W`).
Assume in addition `f_W ∈ L¹((0, ∞), ρ₀ dΔ)`. Then:
1. `|f_W(Δ)| Δ^{x - 1} ∈ L¹(0, ∞)` for every `x ∈ (0, c]`;
2. on `0 < Re z ≤ c`, `mellinRaw f_W z = G(z) W(1 - z/c)` and `mellinStrip f_W z = e^{c ℋ(1 - z/c)} W(1 - z/c)`;
3. `W(1 - ·)` again satisfies `(W1)`–`(W2)`;
4. `𝓗_c f_W = f_{W(1 - ·)}` on `[0, ∞)`, with `𝓗_c f_W(0) = (W 0).re` and `(W 0).im = 0`;
5. if `W(1 - ζ) = σ W(ζ)` on `0 ≤ Re ζ ≤ 1` (for any real `σ`, in particular `σ = ±1`), then
   `𝓗_c f_W = σ f_W` on `[0, ∞)` and `f_W ∈ 𝒜_c^σ` (`IsHankelEigenfn c σ (admissF c W)`).

Scope and limitations: matches `mat:T7` (c) of `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`
with no extra hypotheses. -/
theorem mat_T7_c {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW1 : StripW1 η W) (hW2 : StripW2 α W)
    (hint : IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0)) :
    (∀ x : ℝ, 0 < x → x ≤ c → IntegrableOn (fun Δ : ℝ => |admissF c W Δ| * Δ ^ (x - 1)) (Ioi 0)) ∧
    (∀ z : ℂ, 0 < z.re → z.re ≤ c → mellinRaw (admissF c W) z = admissPhi c W z) ∧
    (∀ z : ℂ, 0 < z.re → z.re ≤ c →
      mellinStrip (admissF c W) z = Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c)) ∧
    (StripW1 η (fun ζ => W (1 - ζ)) ∧ StripW2 α (fun ζ => W (1 - ζ))) ∧
    (∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c (admissF c W) Δ = admissF c (fun ζ => W (1 - ζ)) Δ) ∧
    (besselHankelTransform c (admissF c W) 0 = (W 0).re ∧ (W 0).im = 0) ∧
    (∀ σ : ℝ, (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (1 - ζ) = (σ : ℂ) * W ζ) →
      IsHankelEigenfn c σ (admissF c W)) := by
  have hc0 : 0 < c := by linarith
  have hcont := admissF_continuousOn_of_W1 hc hη hα0 hα1 hW1 hW2.holder1
  have hrefl := besselHankelTransform_admissF_of_W1 hc hη hα0 hα1 hW1 hW2 hint
  refine ⟨fun x hx0 hxc => integrableOn_abs_mul_rpow_of_cont_int hc0 hcont hint hx0 hxc,
    fun z hz0 hzc => mellinRaw_admissF_eq_of_W1 hc hη hα0 hα1 hW1 hW2 hint hz0 hzc,
    fun z hz0 hzc => mellinStrip_admissF_eq_of_W1 hc hη hα0 hα1 hW1 hW2 hint hz0 hzc,
    ⟨hW1.reflect, hW2.reflect⟩, hrefl, ?_, ?_⟩
  · refine ⟨?_, W_zero_im_of_W1 hW1⟩
    rw [hrefl 0 le_rfl]
    simp [admissF]
  · intro σ hsym
    refine ⟨hcont, hint, fun Δ hΔ => ?_⟩
    rw [hrefl Δ hΔ]
    exact admissF_eq_const_mul hc0 hsym Δ hΔ

/-- **Lemma T.7 (`mat:T7`), full statement (parts (a), (b), (c))** (Mellin-strip lift: inversion and reflection).

Combines `mat_T7_a`, `mat_T7_b`, and `mat_T7_c` under the exact hypotheses `(W1)`–`(W2)` of
`CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.7 (`mat:T7`). -/
theorem mat_T7 {c η α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hη : 0 < η) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hW1 : StripW1 η W) (hW2 : StripW2 α W) :
    -- (a)
    ((∀ x₀ x₁ : ℝ, 0 < x₀ → x₀ < c → 0 < x₁ → x₁ < c → ∀ Δ : ℝ, 0 < Δ →
        liftFun (admissPhi c W) x₀ Δ = liftFun (admissPhi c W) x₁ Δ) ∧
      (∀ x₀ : ℝ, 0 < x₀ → x₀ < c → ∀ Δ : ℝ, 0 < Δ → (mellinInv x₀ (admissPhi c W) Δ).im = 0) ∧
      ContinuousOn (admissF c W) (Ici 0) ∧ admissF c W 0 = (W 1).re ∧ (W 1).im = 0) ∧
    -- (b)
    (∀ ξ : ℝ, 0 < ξ → ∀ σ : ℝ, 0 ≤ σ → σ < 1 →
      Integrable (fun τ : ℝ => mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)) ∧
      (((hankelRho0 c (c * ξ) * admissF c W (c * ξ) : ℝ)) : ℂ) =
        ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
          ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)) ∧
    -- (c)
    (IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0) →
      (∀ x : ℝ, 0 < x → x ≤ c → IntegrableOn (fun Δ : ℝ => |admissF c W Δ| * Δ ^ (x - 1)) (Ioi 0)) ∧
      (∀ z : ℂ, 0 < z.re → z.re ≤ c → mellinRaw (admissF c W) z = admissPhi c W z) ∧
      (∀ z : ℂ, 0 < z.re → z.re ≤ c →
        mellinStrip (admissF c W) z = Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c)) ∧
      (StripW1 η (fun ζ => W (1 - ζ)) ∧ StripW2 α (fun ζ => W (1 - ζ))) ∧
      (∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c (admissF c W) Δ = admissF c (fun ζ => W (1 - ζ)) Δ) ∧
      (besselHankelTransform c (admissF c W) 0 = (W 0).re ∧ (W 0).im = 0) ∧
      (∀ σ : ℝ, (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (1 - ζ) = (σ : ℂ) * W ζ) →
        IsHankelEigenfn c σ (admissF c W))) :=
  ⟨mat_T7_a hc hη hα0 hα1 hW1 hW2, mat_T7_b hc hη hW1, fun hint => mat_T7_c hc hη hα0 hα1 hW1 hW2 hint⟩

/-- info: 'FormalResearch.SignUncertainty.mat_T7_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mat_T7_a

/-- info: 'FormalResearch.SignUncertainty.mat_T7_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mat_T7_b

/-- info: 'FormalResearch.SignUncertainty.mat_T7_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mat_T7_c

/-- info: 'FormalResearch.SignUncertainty.mat_T7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mat_T7

end FormalResearch.SignUncertainty

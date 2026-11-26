module

public import FormalResearch.SignUncertainty.MellinStrip

/-!
# Continuity and holomorphy of the Mellin integral of a Hankel eigenfunction (`gt:7.4(1)`)

For `f ∈ 𝒜_c^ε`, `z ↦ ∫_0^∞ f(Δ) Δ^{z-1} dΔ` is continuous on `0 < Re z ≤ c`
(`continuousOn_mellinRaw`) and holomorphic on `0 < Re z < c` (`differentiableOn_mellinRaw`), by
dominated convergence with the integrability `integrableOn_abs_mul_rpow_eigen`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

private lemma aesm_mellin_integrand {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) (z : ℂ) :
    AEStronglyMeasurable (fun Δ : ℝ => (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1)) (volume.restrict (Ioi 0)) :=
  ContinuousOn.aestronglyMeasurable
    ((Complex.continuous_ofReal.comp_continuousOn hf).mul
      (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
        fun w hw => Or.inl (by simpa using (mem_Ioi.mp hw)))) measurableSet_Ioi

/-- Continuity of the Mellin integral on `0 < Re z ≤ c`. -/
theorem continuousOn_mellinRaw {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (mellinRaw f) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  have hfc : ContinuousOn f (Ioi 0) := hf.cont.mono Ioi_subset_Ici_self
  -- on `x0 ≤ Re z ≤ c`
  have key : ∀ x0 : ℝ, 0 < x0 → x0 ≤ c →
      ContinuousOn (mellinRaw f) {z : ℂ | x0 ≤ z.re ∧ z.re ≤ c} := by
    intro x0 hx0 hx0c
    have hb : IntegrableOn (fun Δ : ℝ => |f Δ| * Δ ^ (x0 - 1) + |f Δ| * Δ ^ (c - 1)) (Ioi 0) :=
      (integrableOn_abs_mul_rpow_eigen hc hf hx0 hx0c).add
        (integrableOn_abs_mul_rpow_eigen hc hf hc le_rfl)
    refine continuousOn_of_dominated (bound := fun Δ => |f Δ| * Δ ^ (x0 - 1) + |f Δ| * Δ ^ (c - 1))
      (fun z _ => aesm_mellin_integrand hfc z) ?_ hb ?_
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


/-- The complex Mellin integrand is integrable for `0 < Re z ≤ c`. -/
theorem integrableOn_mellin_integrand {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {z : ℂ} (hz0 : 0 < z.re) (hzc : z.re ≤ c) :
    IntegrableOn (fun Δ : ℝ => (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1)) (Ioi 0) := by
  refine (integrableOn_abs_mul_rpow_eigen hc hf hz0 hzc).mono'
    (aesm_mellin_integrand (hf.cont.mono Ioi_subset_Ici_self) z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
  rw [norm_mul, norm_cpow_sub_one hΔ, Complex.norm_real, Real.norm_eq_abs]

private lemma abs_log_le_of_le_one {Δ δ : ℝ} (h0 : 0 < Δ) (h1 : Δ ≤ 1) (hδ : 0 < δ) :
    |Real.log Δ| ≤ Δ ^ (-δ) / δ := by
  have hlog : Real.log Δ ≤ 0 := Real.log_nonpos h0.le h1
  rw [abs_of_nonpos hlog, ← Real.log_inv]
  have := Real.log_le_rpow_div (inv_nonneg.mpr h0.le) hδ
  rwa [Real.inv_rpow h0.le, ← Real.rpow_neg h0.le] at this

private lemma abs_log_le_of_one_le {Δ δ : ℝ} (h1 : 1 ≤ Δ) (hδ : 0 < δ) :
    |Real.log Δ| ≤ Δ ^ δ / δ := by
  have h0 : 0 < Δ := lt_of_lt_of_le zero_lt_one h1
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  exact Real.log_le_rpow_div h0.le hδ

/-- Holomorphy of the Mellin integral on `0 < Re z < c`. -/
theorem differentiableOn_mellinRaw {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (mellinRaw f) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  have hfc : ContinuousOn f (Ioi 0) := hf.cont.mono Ioi_subset_Ici_self
  intro z0 hz0
  refine DifferentiableAt.differentiableWithinAt ?_
  set x0 : ℝ := z0.re / 2 with hx0d
  set x1 : ℝ := (z0.re + c) / 2 with hx1d
  have hx0 : 0 < x0 := by rw [hx0d]; linarith [hz0.1]
  have hx1 : x1 < c := by rw [hx1d]; linarith [hz0.2]
  have hx01 : x0 < z0.re := by rw [hx0d]; linarith [hz0.1]
  have hx11 : z0.re < x1 := by rw [hx1d]; linarith [hz0.2]
  set δ : ℝ := min (x0 / 2) (c - x1) with hδd
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ0 : δ ≤ x0 / 2 := min_le_left _ _
  have hδ1 : δ ≤ c - x1 := min_le_right _ _
  let s : Set ℂ := {z : ℂ | x0 < z.re ∧ z.re < x1}
  have hs : s ∈ 𝓝 z0 := by
    have : IsOpen s := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    exact this.mem_nhds ⟨hx01, hx11⟩
  let F : ℂ → ℝ → ℂ := fun z Δ => (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1)
  let F' : ℂ → ℝ → ℂ := fun z Δ => (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1) * ((Real.log Δ : ℝ) : ℂ)
  let bound : ℝ → ℝ := fun Δ => (|f Δ| * Δ ^ (x0 / 2 - 1) + |f Δ| * Δ ^ (c - 1)) / δ
  have hbound : Integrable bound (volume.restrict (Ioi 0)) :=
    ((integrableOn_abs_mul_rpow_eigen hc hf (by linarith : 0 < x0 / 2) (by linarith)).add
      (integrableOn_abs_mul_rpow_eigen hc hf hc le_rfl)).div_const δ
  have hmeasF' : AEStronglyMeasurable (F' z0) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((Complex.continuous_ofReal.comp_continuousOn hfc).mul
      (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
        fun w hw => Or.inl (by simpa using (mem_Ioi.mp hw)))).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun w hw => ne_of_gt (mem_Ioi.mp hw)))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := z0) hs
    (Eventually.of_forall fun z => aesm_mellin_integrand hfc z)
    (integrableOn_mellin_integrand hc hf (by linarith) (by linarith [hz0.2]))
    hmeasF' (bound := bound) ?_ hbound ?_
  · exact h.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ z hz
    have hΔ0 : 0 < Δ := hΔ
    simp only [F']
    rw [norm_mul, norm_mul, norm_cpow_sub_one hΔ0, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hnn : 0 ≤ |f Δ| := abs_nonneg _
    rcases le_total Δ 1 with h1 | h1
    · have hp : Δ ^ (z.re - 1) ≤ Δ ^ (x0 - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ0 h1 (by linarith [hz.1])
      have hl := abs_log_le_of_le_one hΔ0 h1 hδ
      have hq : Δ ^ (x0 - 1) * Δ ^ (-δ) ≤ Δ ^ (x0 / 2 - 1) := by
        rw [← Real.rpow_add hΔ0]
        exact Real.rpow_le_rpow_of_exponent_ge hΔ0 h1 (by linarith)
      have hc2 : 0 ≤ |f Δ| * Δ ^ (c - 1) := mul_nonneg hnn (Real.rpow_nonneg hΔ0.le _)
      calc |f Δ| * Δ ^ (z.re - 1) * |Real.log Δ|
          ≤ |f Δ| * Δ ^ (x0 - 1) * (Δ ^ (-δ) / δ) := by
            gcongr
        _ = |f Δ| * (Δ ^ (x0 - 1) * Δ ^ (-δ)) / δ := by ring
        _ ≤ |f Δ| * Δ ^ (x0 / 2 - 1) / δ := by gcongr
        _ ≤ bound Δ := by
            simp only [bound]
            gcongr
            linarith
    · have hp : Δ ^ (z.re - 1) ≤ Δ ^ (x1 - 1) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hz.2])
      have hl := abs_log_le_of_one_le h1 hδ
      have hq : Δ ^ (x1 - 1) * Δ ^ δ ≤ Δ ^ (c - 1) := by
        rw [← Real.rpow_add hΔ0]
        exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      have hc2 : 0 ≤ |f Δ| * Δ ^ (x0 / 2 - 1) := mul_nonneg hnn (Real.rpow_nonneg hΔ0.le _)
      calc |f Δ| * Δ ^ (z.re - 1) * |Real.log Δ|
          ≤ |f Δ| * Δ ^ (x1 - 1) * (Δ ^ δ / δ) := by gcongr
        _ = |f Δ| * (Δ ^ (x1 - 1) * Δ ^ δ) / δ := by ring
        _ ≤ |f Δ| * Δ ^ (c - 1) / δ := by gcongr
        _ ≤ bound Δ := by
            simp only [bound]
            gcongr
            linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ z hz
    have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mem_Ioi.mp hΔ))
    have h1 : HasDerivAt (fun z : ℂ => z - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have h2 := (h1.const_cpow (c := (Δ : ℂ)) (Or.inl hΔ0)).const_mul (f Δ : ℂ)
    refine h2.congr_deriv ?_
    simp only [F']
    rw [Complex.ofReal_log (le_of_lt (mem_Ioi.mp hΔ))]
    ring


/-- `M̃_f` is holomorphic on `0 < Re z < c` (`gt:7.4(1)`). -/
theorem differentiableOn_mellinStrip {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (mellinStrip f) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  intro z hz
  have hz' : (z : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < c} := hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hnm : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => by
    have := hz.1
    rw [h] at this; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hGd : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hnm
  have hG0 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz.1
  have hr : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => ((2 * π : ℝ) : ℂ) ^ w) z :=
    (differentiableAt_id.const_cpow (Or.inl hr))
  have hM : DifferentiableAt ℂ (mellinRaw f) z :=
    ((differentiableOn_mellinRaw hc hf) z hz').differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const) |>.mem_nhds hz')
  exact (hpow.div hGd hG0).mul hM

/-- **`gt:7.4(1)`, reflection on the whole strip**: for `c > 3/2`, `f ∈ 𝒜_c^ε`, `ε = ±1`, and
`0 < Re z < c`: `M̃_f(c - z) = ε M̃_f(z)`. -/
theorem mellinStrip_reflection {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {z : ℂ} (hz0 : 0 < z.re) (hzc : z.re < c) :
    mellinStrip f ((c : ℂ) - z) = (ε : ℂ) * mellinStrip f z := by
  have hc0 : 0 < c := by linarith
  set S : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < c} with hS
  have hSo : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hdA : DifferentiableOn ℂ (fun z => mellinStrip f ((c : ℂ) - z)) S := by
    refine (differentiableOn_mellinStrip hc0 hf).comp (differentiableOn_const _ |>.sub differentiableOn_id) ?_
    intro w hw
    refine ⟨?_, ?_⟩ <;> simp [hw.1, hw.2]
  have hdB : DifferentiableOn ℂ (fun z => (ε : ℂ) * mellinStrip f z) S :=
    (differentiableOn_const _).mul (differentiableOn_mellinStrip hc0 hf)
  have hconv : Convex ℝ S := by
    have h1 : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
    have h2 : Convex ℝ {z : ℂ | z.re < c} := convex_halfSpace_re_lt c
    exact h1.inter h2
  have hz₀ : ((c / 4 : ℝ) : ℂ) ∈ S := by simp [hS]; constructor <;> linarith
  have hev : (fun z => mellinStrip f ((c : ℂ) - z)) =ᶠ[𝓝 ((c / 4 : ℝ) : ℂ)]
      fun z => (ε : ℂ) * mellinStrip f z := by
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < c / 2 - 1 / 4} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show ((c / 4 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < c / 2 - 1 / 4} by
      simp; constructor <;> linarith)] with w hw
    exact mellinStrip_reflection_of_re_lt hc hf hw.1 hw.2
  exact (hdA.analyticOnNhd hSo).eqOn_of_preconnected_of_eventuallyEq (hdB.analyticOnNhd hSo)
    hconv.isPreconnected hz₀ hev ⟨hz0, hzc⟩

/-- **Edge bound** (`gt:7.4(1)`): on `Re z = c`, `|M̃_f(c + i y)| ≤ Γ(c) M[f] / |Γ(c + i y)|`. -/
theorem norm_mellinStrip_edge_le {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (_hf : IsHankelEigenfn c ε f)
    (y : ℝ) :
    ‖mellinStrip f ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.Gamma c * hankelMass c f / ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * Complex.I)‖ := by
  set z : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = c := by simp [hz]
  have hr : (0 : ℝ) < 2 * π := by positivity
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hp : 0 < (2 * π) ^ c := Real.rpow_pos_of_pos hr c
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hzre]; exact hc)
  have hGn : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.mpr hGz
  have hmass : hankelMass c f = (2 * π) ^ c / Real.Gamma c * ∫ Δ in Ioi (0 : ℝ), |f Δ| * Δ ^ (c - 1) := by
    unfold hankelMass hankelRho0
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ _ => ?_
    ring
  have hM : ‖mellinRaw f z‖ ≤ ∫ Δ in Ioi (0 : ℝ), |f Δ| * Δ ^ (c - 1) := by
    unfold mellinRaw
    refine (norm_integral_le_integral_norm _).trans ?_
    refine le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_)
    rw [norm_mul, norm_cpow_sub_one hΔ, Complex.norm_real, Real.norm_eq_abs, hzre]
  have hpn : ‖((2 * π : ℝ) : ℂ) ^ z‖ = (2 * π) ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, hzre]
  unfold mellinStrip
  rw [norm_mul, norm_div, hpn, le_div_iff₀ hGn]
  have hI : ∫ Δ in Ioi (0 : ℝ), |f Δ| * Δ ^ (c - 1) = hankelMass c f * Real.Gamma c / (2 * π) ^ c := by
    rw [hmass]; field_simp
  calc (2 * π) ^ c / ‖Complex.Gamma z‖ * ‖mellinRaw f z‖ * ‖Complex.Gamma z‖
      = (2 * π) ^ c * ‖mellinRaw f z‖ := by field_simp
    _ ≤ (2 * π) ^ c * (hankelMass c f * Real.Gamma c / (2 * π) ^ c) :=
        mul_le_mul_of_nonneg_left (hM.trans (le_of_eq hI)) hp.le
    _ = Real.Gamma c * hankelMass c f := by field_simp

/-- info: 'FormalResearch.SignUncertainty.differentiableOn_mellinRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_mellinRaw

/-- info: 'FormalResearch.SignUncertainty.continuousOn_mellinRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_mellinRaw

/-- info: 'FormalResearch.SignUncertainty.mellinStrip_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinStrip_reflection

/-- info: 'FormalResearch.SignUncertainty.norm_mellinStrip_edge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinStrip_edge_le

end FormalResearch.SignUncertainty

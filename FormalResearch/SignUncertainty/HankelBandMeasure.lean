module

public import FormalResearch.SignUncertainty.HankelEdgeRep

/-!
# The signed measure `dm = c (f ρ₀)(cξ) dξ` and its positive and negative parts (`teb:MS2`, M5-S5)

For `c > 0` and `f ∈ 𝒜_c^ε`, `hankelDmPos c f` and `hankelDmNeg c f` are the measures on `ℝ` with densities
`max (g₀ ξ) 0` and `max (-g₀ ξ) 0` with respect to Lebesgue measure on `(0, ∞)`, where
`g₀(ξ) = c f(cξ) ρ₀(cξ)`.  They are finite, live on `(0, ∞)`, have total variation `M[f]`
(`hankelDm_tv`), and `dm_neg` vanishes above `T` when `f ≥ 0` on `[cT, ∞)`.  For a bounded measurable
kernel `K`, `∫ K d dmPos - ∫ K d dmNeg = ∫_0^∞ K g₀` (`hankelDm_integral_sub`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology ENNReal
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The density `g₀(ξ) = c f(cξ) ρ₀(cξ)` of `dm`. -/
noncomputable def hankelDmDens (c : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  c * (f (c * ξ) * hankelRho0 c (c * ξ))

/-- The positive part of `dm`. -/
noncomputable def hankelDmPos (c : ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun ξ => ENNReal.ofReal (hankelDmDens c f ξ))

/-- The negative part of `dm`. -/
noncomputable def hankelDmNeg (c : ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun ξ => ENNReal.ofReal (-hankelDmDens c f ξ))

theorem hankelDmDens_continuousOn {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (hankelDmDens c f) (Ioi 0) := by
  have hmaps : MapsTo (fun ξ : ℝ => c * ξ) (Ioi 0) (Ioi 0) := fun ξ hξ => mul_pos hc hξ
  have h1 : ContinuousOn (fun ξ : ℝ => f (c * ξ)) (Ioi 0) :=
    hf.cont.comp (by fun_prop) (hmaps.mono_right Ioi_subset_Ici_self)
  have h2 : ContinuousOn (fun ξ : ℝ => hankelRho0 c (c * ξ)) (Ioi 0) :=
    (continuousOn_hankelRho0 c).comp (by fun_prop) hmaps
  exact continuousOn_const.mul (h1.mul h2)

theorem hankelDmDens_integrableOn {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IntegrableOn (hankelDmDens c f) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (fun Δ => f Δ * hankelRho0 c Δ) 0 hc).mpr
    (by simpa using hf.int)
  exact h.const_mul c

theorem hankelDmDens_aemeasurable {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    AEMeasurable (hankelDmDens c f) (volume.restrict (Ioi (0 : ℝ))) :=
  (hankelDmDens_continuousOn hc hf).aemeasurable measurableSet_Ioi

theorem hankelDmPos_apply {c : ℝ} {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    hankelDmPos c f s = ∫⁻ ξ in s ∩ Ioi 0, ENNReal.ofReal (hankelDmDens c f ξ) := by
  unfold hankelDmPos
  rw [withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem hankelDmNeg_apply {c : ℝ} {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    hankelDmNeg c f s = ∫⁻ ξ in s ∩ Ioi 0, ENNReal.ofReal (-hankelDmDens c f ξ) := by
  unfold hankelDmNeg
  rw [withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem hankelDmPos_Iic (c : ℝ) (f : ℝ → ℝ) : hankelDmPos c f (Iic 0) = 0 := by
  rw [hankelDmPos_apply measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1, h.2]
  rw [this]; simp

theorem hankelDmNeg_Iic (c : ℝ) (f : ℝ → ℝ) : hankelDmNeg c f (Iic 0) = 0 := by
  rw [hankelDmNeg_apply measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1, h.2]
  rw [this]; simp

theorem isFiniteMeasure_hankelDmPos {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IsFiniteMeasure (hankelDmPos c f) := by
  refine ⟨?_⟩
  rw [hankelDmPos_apply MeasurableSet.univ, univ_inter]
  exact (hankelDmDens_integrableOn hc hf).lintegral_lt_top

theorem isFiniteMeasure_hankelDmNeg {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IsFiniteMeasure (hankelDmNeg c f) := by
  refine ⟨?_⟩
  rw [hankelDmNeg_apply MeasurableSet.univ, univ_inter]
  exact (hankelDmDens_integrableOn hc hf).neg.lintegral_lt_top

/-- Bochner integrals against `dm_±`. -/
theorem hankelDmPos_integral {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : ℝ → E) :
    ∫ ξ, h ξ ∂hankelDmPos c f = ∫ ξ in Ioi (0 : ℝ), max (hankelDmDens c f ξ) 0 • h ξ := by
  unfold hankelDmPos
  rw [integral_withDensity_eq_integral_toReal_smul₀ (hankelDmDens_aemeasurable hc hf).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', max_comm]

theorem hankelDmNeg_integral {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : ℝ → E) :
    ∫ ξ, h ξ ∂hankelDmNeg c f = ∫ ξ in Ioi (0 : ℝ), max (-hankelDmDens c f ξ) 0 • h ξ := by
  unfold hankelDmNeg
  have hm : AEMeasurable (fun ξ => ENNReal.ofReal (-hankelDmDens c f ξ))
      (volume.restrict (Ioi (0 : ℝ))) := (hankelDmDens_aemeasurable hc hf).neg.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', max_comm]

/-- Total variation of `dm` equals `M[f]`. -/
theorem hankelDm_tv {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    (hankelDmPos c f univ).toReal + (hankelDmNeg c f univ).toReal = hankelMass c f := by
  have hP := hankelDmPos_integral hc hf (fun _ => (1 : ℝ))
  have hN := hankelDmNeg_integral hc hf (fun _ => (1 : ℝ))
  have hfP := isFiniteMeasure_hankelDmPos hc hf
  have hfN := isFiniteMeasure_hankelDmNeg hc hf
  simp only [integral_const, smul_eq_mul, mul_one] at hP hN
  have e1 : (hankelDmPos c f).real univ = (hankelDmPos c f univ).toReal := rfl
  have e2 : (hankelDmNeg c f).real univ = (hankelDmNeg c f univ).toReal := rfl
  have hint := hankelDmDens_integrableOn hc hf
  have hsum : ∫ ξ in Ioi (0 : ℝ), (max (hankelDmDens c f ξ) 0 + max (-hankelDmDens c f ξ) 0) =
      ∫ ξ in Ioi (0 : ℝ), |hankelDmDens c f ξ| := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rcases le_total (hankelDmDens c f ξ) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
  have hposI : IntegrableOn (fun ξ => max (hankelDmDens c f ξ) 0) (Ioi 0) := hint.pos_part
  have hnegI : IntegrableOn (fun ξ => max (-hankelDmDens c f ξ) 0) (Ioi 0) := hint.neg_part
  rw [← e1, ← e2, hP, hN, ← integral_add hposI hnegI, hsum]
  unfold hankelMass
  have hcongr : ∫ ξ in Ioi (0 : ℝ), |hankelDmDens c f ξ| =
      ∫ ξ in Ioi (0 : ℝ), c * ((fun Δ => |f Δ| * hankelRho0 c Δ) (c * ξ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    have hρ := hankelRho0_nonneg hc (mul_pos hc hξ).le
    simp only [hankelDmDens]
    rw [abs_mul, abs_of_pos hc, abs_mul, abs_of_nonneg hρ]
  rw [hcongr, integral_const_mul,
    integral_comp_mul_left_Ioi (fun Δ => |f Δ| * hankelRho0 c Δ) 0 hc, mul_zero, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- `dm_-` has no mass above `T` when `f ≥ 0` on `[cT, ∞)`. -/
theorem hankelDmNeg_tail {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {T : ℝ} (hT : ∀ Δ : ℝ, c * T ≤ Δ → 0 ≤ f Δ) :
    hankelDmNeg c f (Ici T) = 0 := by
  rw [hankelDmNeg_apply measurableSet_Ici]
  rw [setLIntegral_congr_fun (measurableSet_Ici.inter measurableSet_Ioi) (g := fun _ => (0 : ℝ≥0∞))]
  · simp
  · intro ξ hξ
    have hf0 := hT (c * ξ) (mul_le_mul_of_nonneg_left hξ.1 hc.le)
    have hρ := hankelRho0_nonneg hc (mul_pos hc hξ.2).le
    have : 0 ≤ hankelDmDens c f ξ := mul_nonneg hc.le (mul_nonneg hf0 hρ)
    exact ENNReal.ofReal_of_nonpos (by linarith)

/-- `∫ K d dm_+ - ∫ K d dm_- = ∫_0^∞ K g₀` for a bounded measurable kernel. -/
theorem hankelDm_integral_sub {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {K : ℝ → ℂ} {B : ℝ} (hKm : AEStronglyMeasurable K (volume.restrict (Ioi (0 : ℝ))))
    (hKb : ∀ ξ ∈ Ioi (0 : ℝ), ‖K ξ‖ ≤ B) :
    (∫ ξ, K ξ ∂hankelDmPos c f) - ∫ ξ, K ξ ∂hankelDmNeg c f =
      ∫ ξ in Ioi (0 : ℝ), K ξ * (hankelDmDens c f ξ : ℂ) := by
  rw [hankelDmPos_integral hc hf, hankelDmNeg_integral hc hf]
  have hint := hankelDmDens_integrableOn hc hf
  have hmeas : AEStronglyMeasurable (hankelDmDens c f) (volume.restrict (Ioi (0 : ℝ))) :=
    hint.aestronglyMeasurable
  have hI : ∀ g : ℝ → ℝ, IntegrableOn g (Ioi 0) → (∀ ξ, |g ξ| ≤ |hankelDmDens c f ξ|) →
      IntegrableOn (fun ξ => g ξ • K ξ) (Ioi 0) := by
    intro g hg hgb
    refine Integrable.mono' (hint.norm.mul_const (|B|)) (hg.aestronglyMeasurable.smul hKm) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun ξ hξ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hgb ξ) ((hKb ξ hξ).trans (le_abs_self B)) (norm_nonneg _) (abs_nonneg _)
  have h1 := hI _ hint.pos_part (fun ξ => by
    rcases le_total (hankelDmDens c f ξ) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h])
  have h2 := hI _ hint.neg_part (fun ξ => by
    rcases le_total (hankelDmDens c f ξ) 0 with h | h
    · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos h]
    · rw [max_eq_right (by linarith)]; simp)
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
  simp only [Complex.real_smul]
  have : ((max (hankelDmDens c f ξ) 0 : ℝ) : ℂ) - ((max (-hankelDmDens c f ξ) 0 : ℝ) : ℂ) =
      (hankelDmDens c f ξ : ℂ) := by
    rcases le_total (hankelDmDens c f ξ) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; push_cast; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; push_cast; ring
  calc _ = (((max (hankelDmDens c f ξ) 0 : ℝ) : ℂ) - ((max (-hankelDmDens c f ξ) 0 : ℝ) : ℂ)) * K ξ := by ring
    _ = _ := by rw [this]; ring

/-- info: 'FormalResearch.SignUncertainty.hankelDm_tv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelDm_tv

/-- info: 'FormalResearch.SignUncertainty.hankelDm_integral_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelDm_integral_sub

/-- info: 'FormalResearch.SignUncertainty.hankelDmNeg_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelDmNeg_tail

/-- info: 'FormalResearch.SignUncertainty.hankelDmPos_Iic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelDmPos_Iic

/-- info: 'FormalResearch.SignUncertainty.isFiniteMeasure_hankelDmPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFiniteMeasure_hankelDmPos

end FormalResearch.SignUncertainty

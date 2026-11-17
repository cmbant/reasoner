module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Multiplication operators and reflection on `L²(ℝ; ℂ)`

Plumbing for the Airy transform (`AiryTransformDef`): multiplication by a measurable function of
modulus `1` is a unitary operator `AiryL2 ≃ₗᵢ[ℂ] AiryL2` (`airyMulEquiv`), multiplication by the indicator of a
measurable set is an orthogonal projection (`airyIndProj`), and the reflection `(R f)(t) = f(-t)` is a
unitary involution (`airyReflect`).  Everything is stated on `Lp ℂ 2` for Lebesgue measure on `ℝ`.

The multiplication is Mathlib's Hölder pairing `Lp ℂ ∞ × Lp ℂ 2 → Lp ℂ 2`
(`MeasureTheory.Lp.coeFn_lpSMul`), the reflection is `Lp.compMeasurePreservingₗᵢ` for `neg`.

**Not formalised:** nothing beyond these elementary statements is claimed here.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal ComplexInnerProductSpace

namespace FormalResearch.Special

/-- `L²(ℝ; ℂ)`. -/
abbrev AiryL2 : Type := Lp (α := ℝ) ℂ 2

section Mul

variable {m : ℝ → ℂ}

lemma airyMul_memLp (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) : MemLp m ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall hb)

/-- Multiplication of `L²(ℝ)` by a measurable function bounded by `1`. -/
noncomputable def airyMulL2 (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) (f : AiryL2) : AiryL2 :=
  (((airyMul_memLp hm hb).toLp m : Lp (α := ℝ) ℂ ∞) • f : AiryL2)

lemma airyMulL2_coeFn (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) (f : AiryL2) :
    airyMulL2 hm hb f =ᵐ[volume] fun x => m x * f x := by
  have h1 := Lp.coeFn_lpSMul (r := 2) ((airyMul_memLp hm hb).toLp m : Lp (α := ℝ) ℂ ∞) f
  have h2 := (airyMul_memLp hm hb).coeFn_toLp
  filter_upwards [h1, h2] with x hx1 hx2
  unfold airyMulL2
  rw [hx1]
  simp [Pi.smul_apply', hx2]

lemma airyMulL2_comp (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) {n : ℝ → ℂ} (hn : Measurable n)
    (hbn : ∀ x, ‖n x‖ ≤ 1) (f : AiryL2) (hmn : ∀ x, n x * m x = 1) :
    airyMulL2 hn hbn (airyMulL2 hm hb f) = f := by
  refine Lp.ext ?_
  filter_upwards [airyMulL2_coeFn hn hbn (airyMulL2 hm hb f), airyMulL2_coeFn hm hb f] with x h1 h2
  rw [h1, h2, ← mul_assoc, hmn x, one_mul]

lemma norm_airyMulL2 (hm : Measurable m) (h1 : ∀ x, ‖m x‖ = 1) (f : AiryL2) :
    ‖airyMulL2 hm (fun x => (h1 x).le) f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def (f := f)]
  congr 1
  rw [eLpNorm_congr_ae (airyMulL2_coeFn hm (fun x => (h1 x).le) f)]
  exact eLpNorm_congr_norm_ae (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f) (Eventually.of_forall fun x => by simp [h1 x])

/-- Multiplication by a measurable function of modulus one is a unitary operator on `L²(ℝ)`. -/
noncomputable def airyMulEquiv (hm : Measurable m) (h1 : ∀ x, ‖m x‖ = 1) : AiryL2 ≃ₗᵢ[ℂ] AiryL2 where
  toFun := airyMulL2 hm (fun x => (h1 x).le)
  invFun := airyMulL2 (m := fun x => starRingEnd ℂ (m x)) (by fun_prop) (fun x => by simp [h1 x])
  map_add' f g := Lp.add_smul _ f g
  map_smul' c f := (Lp.smul_comm c _ f).symm
  left_inv f := airyMulL2_comp _ _ _ _ f (fun x => by
    rw [mul_comm]; simpa [Complex.normSq_eq_norm_sq, h1 x] using Complex.mul_conj' (m x))
  right_inv f := airyMulL2_comp _ _ _ _ f (fun x => by
    simpa [Complex.normSq_eq_norm_sq, h1 x] using Complex.mul_conj' (m x))
  norm_map' := norm_airyMulL2 hm h1

lemma airyMulEquiv_coeFn (hm : Measurable m) (h1 : ∀ x, ‖m x‖ = 1) (f : AiryL2) :
    airyMulEquiv hm h1 f =ᵐ[volume] fun x => m x * f x :=
  airyMulL2_coeFn hm (fun x => (h1 x).le) f

lemma norm_airyMulL2_le (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) (f : AiryL2) :
    ‖airyMulL2 hm hb f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def (f := f)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  rw [eLpNorm_congr_ae (airyMulL2_coeFn hm hb f)]
  refine eLpNorm_mono_ae (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

/-- Multiplication by a measurable function bounded by `1`, as a continuous linear map. -/
noncomputable def airyMulCLM (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) : AiryL2 →L[ℂ] AiryL2 :=
  LinearMap.mkContinuous
    { toFun := airyMulL2 hm hb
      map_add' := fun f g => Lp.add_smul _ f g
      map_smul' := fun c f => (Lp.smul_comm c _ f).symm } 1
    (fun f => by
      show ‖airyMulL2 hm hb f‖ ≤ 1 * ‖f‖
      rw [one_mul]; exact norm_airyMulL2_le hm hb f)

lemma airyMulCLM_apply (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) (f : AiryL2) :
    airyMulCLM hm hb f = airyMulL2 hm hb f := rfl

end Mul

/-! ### Indicator projections -/

section Ind

variable {s : Set ℝ}

lemma airyInd_measurable (hs : MeasurableSet s) : Measurable (s.indicator (fun _ : ℝ => (1 : ℂ))) :=
  measurable_const.indicator hs

lemma airyInd_bound (s : Set ℝ) (x : ℝ) : ‖s.indicator (fun _ : ℝ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- Multiplication by the indicator of a measurable set `s`: the orthogonal projection of `L²(ℝ)` onto
`L²(s)`. -/
noncomputable def airyIndProj (hs : MeasurableSet s) : AiryL2 →L[ℂ] AiryL2 :=
  airyMulCLM (airyInd_measurable hs) (airyInd_bound s)

lemma airyIndProj_coeFn (hs : MeasurableSet s) (f : AiryL2) :
    airyIndProj hs f =ᵐ[volume] s.indicator (f : ℝ → ℂ) := by
  filter_upwards [airyMulL2_coeFn (airyInd_measurable hs) (airyInd_bound s) f] with x hx
  rw [airyIndProj, airyMulCLM_apply, hx]
  by_cases h : x ∈ s <;> simp [h]

lemma airyIndProj_idem (hs : MeasurableSet s) (f : AiryL2) :
    airyIndProj hs (airyIndProj hs f) = airyIndProj hs f := by
  refine Lp.ext ?_
  filter_upwards [airyIndProj_coeFn hs (airyIndProj hs f), airyIndProj_coeFn hs f] with x h1 h2
  rw [h1]
  by_cases h : x ∈ s
  · simp [h, h2]
  · simp [h, h2]

lemma airyIndProj_inner (hs : MeasurableSet s) (f g : AiryL2) :
    inner ℂ (airyIndProj hs f) g = inner ℂ f (airyIndProj hs g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [airyIndProj_coeFn hs f, airyIndProj_coeFn hs g] with x h1 h2
  rw [h1, h2]
  by_cases h : x ∈ s <;> simp [h]

lemma airyIndProj_eq_self_iff (hs : MeasurableSet s) (f : AiryL2) :
    airyIndProj hs f = f ↔ ∀ᵐ x ∂volume, x ∉ s → f x = 0 := by
  constructor
  · intro h
    filter_upwards [airyIndProj_coeFn hs f, Lp.ext_iff.mp h] with x h1 h2 hx
    rw [← h2, h1]; simp [hx]
  · intro h
    refine Lp.ext ?_
    filter_upwards [airyIndProj_coeFn hs f, h] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ s
    · simp [hx]
    · simp [hx, h2 hx]

end Ind

/-! ### Reflection -/

/-- The reflection `f ↦ f(-·)` on `L²(ℝ)` as a linear isometry. -/
noncomputable def airyReflectLI : AiryL2 →ₗᵢ[ℂ] AiryL2 :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma airyReflectLI_coeFn (f : AiryL2) :
    airyReflectLI f =ᵐ[volume] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))

lemma airyReflectLI_involutive (f : AiryL2) : airyReflectLI (airyReflectLI f) = f := by
  refine Lp.ext ?_
  have h1 := airyReflectLI_coeFn (airyReflectLI f)
  have h2 := airyReflectLI_coeFn f
  have h3 : (fun x : ℝ => (airyReflectLI f) (-x)) =ᵐ[volume] fun x => f (-(-x)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3] with x hx1 hx3
  rw [hx1, hx3]; simp

/-- The reflection `(R f)(t) = f(-t)` is a unitary involution of `L²(ℝ)`. -/
noncomputable def airyReflect : AiryL2 ≃ₗᵢ[ℂ] AiryL2 where
  toFun := airyReflectLI
  invFun := airyReflectLI
  map_add' := airyReflectLI.map_add
  map_smul' := airyReflectLI.map_smul
  left_inv := airyReflectLI_involutive
  right_inv := airyReflectLI_involutive
  norm_map' := airyReflectLI.norm_map

lemma airyReflect_coeFn (f : AiryL2) : airyReflect f =ᵐ[volume] fun x => f (-x) :=
  airyReflectLI_coeFn f

lemma airyReflect_airyReflect (f : AiryL2) : airyReflect (airyReflect f) = f :=
  airyReflectLI_involutive f

lemma airyReflect_symm : airyReflect.symm = airyReflect := rfl

end FormalResearch.Special

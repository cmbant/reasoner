module

public import FormalResearch.Special.AiryTransformMul
public import FormalResearch.Special.AiryBound

/-!
# The Airy transform on `L²(ℝ)`: unitarity and the involution `A = 𝒜 R`

Mathlib normalisation: `𝓕 f (ξ) = ∫ e^{-2πi x ξ} f(x) dx` (`Lp.fourierTransformₗᵢ`, unitary on `L²(ℝ; ℂ)`).
With the unimodular symbol `m(ξ) = exp(i (2πξ)³/3)` (`airyMult`; `m(ξ) = e^{iω³/3}` at the angular frequency
`ω = 2πξ`) put
`𝒜 = 𝓕⁻¹ ∘ M_m ∘ 𝓕` (`airyTransform`, the Fourier multiplier of `Ai`'s transform `∫ Ai(x)e^{-iωx}dx = e^{iω³/3}`).

* `airyTransform : AiryL2 ≃ₗᵢ[ℂ] AiryL2`: **`𝒜` is unitary** (composition of unitaries; Plancherel is Mathlib's);
* `airyF_airyF`: `𝓕 (𝓕 f) = R f` (reflection `R f(t) = f(-t)`), proved by density of Schwartz functions;
* `airyTransform_symm_eq`: `𝒜⁻¹ = 𝒜* = R 𝒜 R` (the multiplier `m` satisfies `m(-ξ) = conj m(ξ)`);
* `airyA := 𝒜 ∘ R`: **`A⁻¹ = A`** (`airyA_symm`), hence `A` is a self-adjoint unitary involution
  (`airyA_airyA`, `airyA_inner_left`).

In `AiryTransformKernel` and `AiryTransformWeak` it is shown that `(A φ)(u) = ∫ φ(t) Ai(u+t) dt`, i.e. `A` is the
"Airy transform with kernel `Ai(u+t)`" of the CFT notes (`LOCAL_AIRY_MODEL` Lemma Q2: unitary involution on `L²(ℝ)`).
Note that `𝒜 = ` convolution with `Ai` is unitary but **not** an involution; the involution is the reflected
operator `A = 𝒜 R` (checked numerically, see `AiryTransformKernel`: `𝓕⁻¹ m 𝓕 f (u) = ∫ f(t) Ai(u-t) dt`, 25 digits).

**Not formalised** here: the kernel identification (next modules).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set SchwartzMap
open scoped ENNReal ComplexInnerProductSpace FourierTransform Real

namespace FormalResearch.Special

/-- The symbol `m(ξ) = exp(i (2πξ)³/3)` of the Airy transform in Mathlib's `2π`-normalisation. -/
noncomputable def airyMult (ξ : ℝ) : ℂ := cexp (I * (((2 * π * ξ) ^ 3 / 3 : ℝ) : ℂ))

lemma norm_airyMult (ξ : ℝ) : ‖airyMult ξ‖ = 1 := by
  rw [airyMult]; exact Complex.norm_exp_I_mul_ofReal _

lemma continuous_airyMult : Continuous airyMult := by
  unfold airyMult; fun_prop

lemma measurable_airyMult : Measurable airyMult := continuous_airyMult.measurable

lemma airyMult_neg (ξ : ℝ) : airyMult (-ξ) = starRingEnd ℂ (airyMult ξ) := by
  unfold airyMult
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

/-- The Plancherel–Fourier transform of `L²(ℝ; ℂ)`. -/
noncomputable abbrev airyF : AiryL2 ≃ₗᵢ[ℂ] AiryL2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-- Multiplication by the Airy symbol. -/
noncomputable def airyM : AiryL2 ≃ₗᵢ[ℂ] AiryL2 := airyMulEquiv measurable_airyMult norm_airyMult

lemma airyM_coeFn (f : AiryL2) : airyM f =ᵐ[volume] fun ξ => airyMult ξ * f ξ :=
  airyMulEquiv_coeFn measurable_airyMult norm_airyMult f

/-- **The Airy transform** `𝒜 = 𝓕⁻¹ M_m 𝓕` on `L²(ℝ)`; unitary. -/
noncomputable def airyTransform : AiryL2 ≃ₗᵢ[ℂ] AiryL2 := (airyF.trans airyM).trans airyF.symm

lemma airyTransform_apply (f : AiryL2) : airyTransform f = airyF.symm (airyM (airyF f)) := rfl

theorem airyTransform_norm (f : AiryL2) : ‖airyTransform f‖ = ‖f‖ := airyTransform.norm_map f

theorem airyTransform_inner (f g : AiryL2) :
    inner ℂ (airyTransform f) (airyTransform g) = inner ℂ f g := airyTransform.inner_map_map f g

/-! ### `𝓕 𝓕 = R` -/

lemma airyFinv_eq_reflect (f : AiryL2) : airyF.symm f = airyReflect (airyF f) := by
  set p := fun f : AiryL2 => airyF.symm f = airyReflect (airyF f) with hp
  refine DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f ?_ ?_
  · exact isClosed_eq (airyF.symm.continuous) (airyReflect.continuous.comp airyF.continuous)
  · intro φ
    show airyF.symm (φ.toLp 2) = airyReflect (airyF (φ.toLp 2))
    have h1 : airyF.symm (φ.toLp 2) = (𝓕⁻ φ).toLp 2 := SchwartzMap.toLp_fourierInv_eq φ
    have h2 : airyF (φ.toLp 2) = (𝓕 φ).toLp 2 := SchwartzMap.toLp_fourier_eq φ
    rw [h1, h2]
    refine Lp.ext ?_
    have e1 := SchwartzMap.coeFn_toLp (𝓕⁻ φ) 2 (volume : Measure ℝ)
    have e2 := SchwartzMap.coeFn_toLp (𝓕 φ) 2 (volume : Measure ℝ)
    have e3 := airyReflect_coeFn ((𝓕 φ).toLp 2)
    have e4 : (fun x : ℝ => ((𝓕 φ).toLp 2 : AiryL2) (-x)) =ᵐ[volume] fun x => (𝓕 φ) (-x) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp e2
    filter_upwards [e1, e3, e4] with x h1 h3 h4
    rw [h1, h3, h4]
    have := congrArg (fun g : 𝓢(ℝ, ℂ) => g x) (SchwartzMap.fourierInv_apply_eq φ)
    simpa using this

lemma airyF_airyF (f : AiryL2) : airyF (airyF f) = airyReflect f := by
  have h := airyFinv_eq_reflect (airyF f)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  have := congrArg airyReflect h
  rw [airyReflect_airyReflect] at this
  exact this.symm

lemma airyReflect_airyF (f : AiryL2) : airyReflect (airyF f) = airyF (airyReflect f) := by
  have h1 := airyF_airyF (airyF f)
  have h2 := congrArg airyF (airyF_airyF f)
  rw [h1] at h2
  exact h2

lemma airyM_symm_coeFn (f : AiryL2) : airyM.symm f =ᵐ[volume] fun ξ => starRingEnd ℂ (airyMult ξ) * f ξ :=
  airyMulL2_coeFn (m := fun x => starRingEnd ℂ (airyMult x)) (by have := measurable_airyMult; fun_prop)
    (fun x => by simp [norm_airyMult]) f

lemma airyReflect_airyM_airyReflect (f : AiryL2) :
    airyReflect (airyM (airyReflect f)) = airyM.symm f := by
  refine Lp.ext ?_
  have e1 := airyReflect_coeFn (airyM (airyReflect f))
  have e2 : (fun x : ℝ => (airyM (airyReflect f)) (-x)) =ᵐ[volume]
      fun x => airyMult (-x) * (airyReflect f) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (airyM_coeFn (airyReflect f))
  have e3 : (fun x : ℝ => (airyReflect f) (-x)) =ᵐ[volume] fun x => f (-(-x)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (airyReflect_coeFn f)
  have e4 := airyM_symm_coeFn f
  have e5 : (fun x : ℝ => airyMult (-x) * (airyReflect f) (-x)) =ᵐ[volume]
      fun x => airyMult (-x) * f (-(-x)) := by
    filter_upwards [e3] with x hx
    simp only [hx]
  filter_upwards [e1, e2, e4, e5] with x h1 h2 h4 h5
  rw [h1, h2, h5, h4, airyMult_neg]
  simp

lemma airyTransform_symm_apply (f : AiryL2) :
    airyTransform.symm f = airyF.symm (airyM.symm (airyF f)) := rfl

/-- **Adjoint of `𝒜`:** `𝒜⁻¹ = 𝒜* = R 𝒜 R`. -/
theorem airyTransform_symm_eq (f : AiryL2) :
    airyTransform.symm f = airyReflect (airyTransform (airyReflect f)) := by
  set h := airyF f with hh
  have e1 : airyM (airyReflect h) = airyReflect (airyM.symm h) := by
    rw [← airyReflect_airyM_airyReflect h, airyReflect_airyReflect]
  have e2 : airyReflect (airyTransform (airyReflect f)) = airyF (airyM (airyReflect h)) := by
    rw [airyTransform_apply, airyFinv_eq_reflect, airyReflect_airyReflect, airyReflect_airyF]
  rw [e2, e1, airyTransform_symm_apply, airyFinv_eq_reflect, ← airyReflect_airyF]

/-- The involutive Airy transform `A = 𝒜 ∘ R`, `A φ (u) = ∫ φ(t) Ai(u+t) dt`. -/
noncomputable def airyA : AiryL2 ≃ₗᵢ[ℂ] AiryL2 := airyReflect.trans airyTransform

lemma airyA_apply (f : AiryL2) : airyA f = airyTransform (airyReflect f) := rfl

/-- **`A⁻¹ = A`**. -/
theorem airyA_symm : airyA.symm = airyA := by
  refine LinearIsometryEquiv.ext fun f => ?_
  show airyReflect (airyTransform.symm f) = airyTransform (airyReflect f)
  rw [airyTransform_symm_eq, airyReflect_airyReflect]

/-- **`A` is an involution**: `A (A f) = f`. -/
theorem airyA_airyA (f : AiryL2) : airyA (airyA f) = f := by
  have := airyA.symm_apply_apply f
  rw [airyA_symm] at this
  exact this

/-- **`A` is self-adjoint**: `⟨A f, g⟩ = ⟨f, A g⟩`. -/
theorem airyA_inner_left (f g : AiryL2) : inner ℂ (airyA f) g = inner ℂ f (airyA g) := by
  rw [airyA.inner_map_eq_flip, airyA_symm]

/-- **Parseval for `A`**: `⟨A f, A g⟩ = ⟨f, g⟩`. -/
theorem airyA_inner (f g : AiryL2) : inner ℂ (airyA f) (airyA g) = inner ℂ f g :=
  airyA.inner_map_map f g

theorem airyA_norm (f : AiryL2) : ‖airyA f‖ = ‖f‖ := airyA.norm_map f

/-- info: 'FormalResearch.Special.airyTransform_symm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTransform_symm_eq

/-- info: 'FormalResearch.Special.airyA_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_symm

/-- info: 'FormalResearch.Special.airyA_airyA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_airyA

/-- info: 'FormalResearch.Special.airyA_inner_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_inner_left

/-- info: 'FormalResearch.Special.airyF_airyF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyF_airyF

/-- info: 'FormalResearch.Special.airyTransform_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTransform_norm

/-- info: 'FormalResearch.Special.airyTransform_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyTransform_inner

/-- info: 'FormalResearch.Special.airyA_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_inner

/-- info: 'FormalResearch.Special.airyA_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyA_norm

end FormalResearch.Special

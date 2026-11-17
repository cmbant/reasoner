module

public import FormalResearch.Special.AiryTransformWeak

/-!
# The Airy projector `K_Ai = A P A`, the Paley–Wiener space `PW = A L²(0,∞)` and `K_u = A_u A_u^*`

With `A` the Airy transform (`AiryTransformDef`), `P` the orthogonal projection of `L²(ℝ)` onto `L²(0,∞)`
(`airyIndProj`), set `K_Ai := A P A` (`airyKAi`).  Proved (all on `AiryL2 = L²(ℝ; ℂ)`):

* `isStarProjection_airyKAi`: **`K_Ai` is an orthogonal projection** (`K_Ai² = K_Ai`, `K_Ai* = K_Ai`), with
  `⟨K_Ai f, f⟩ = ‖P A f‖² ≥ 0` (`inner_airyKAi_self`) and `‖K_Ai f‖ ≤ ‖f‖`;
* its range `PW` (`airyPW`, the closed subspace `{F : K_Ai F = F} = A L²(0,∞)`, `mem_airyPW_iff`);
* **the integral kernel** (`airyKAi_ae`): for **every** `f ∈ L²(ℝ)`,
  `(K_Ai f)(u) = ∫ K(u,v) f(v) dv` for a.e. `u`, the integral being absolutely convergent for every `u`
  because `K(u,·) = A(1_{t>0} Ai(u+·)) ∈ L²` with `‖K(u,·)‖² = K(u,u)` (`airyKerL2`, `airyKerL2_ae`);
  in particular `PW` has the reproducing property `F(u) = ∫ K(u,v) F(v) dv` (`airyPW_reproducing`);
* **`K_u = A_u A_u^*`** (`airyKu_eq`), `A_u = 1_{(u,∞)} A 1_{(0,∞)}`, `K_u = 1_{(u,∞)} K_Ai 1_{(u,∞)}`, hence
  `K_u` is positive (`inner_airyKu_self`), and its kernel is `K(x,y)` on `(u,∞)²` (`airyKu_ae`).

This is the content of `LOCAL_AIRY_MODEL` Lemma Q2 / `STRUCTURAL_LINKS` (`K_Ai` is the projector on `PW`) and of the
operator statement `K_u = A_u A_u^*` of W1 `edge.tex`.

**Not formalised:** trace class / Hilbert–Schmidt norms of `K_u` as `Lp` operators (the function-level HS bound
is `AiryKernelOpL2`), eigenvalues, Fredholm determinants.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set SchwartzMap
open scoped ContDiff ComplexInnerProductSpace FourierTransform Real

namespace FormalResearch.Special

/-- `A` as a continuous linear map. -/
noncomputable def airyAL : AiryL2 →L[ℂ] AiryL2 := airyA.toContinuousLinearEquiv.toContinuousLinearMap

lemma airyAL_apply (f : AiryL2) : airyAL f = airyA f := rfl

/-- The projection onto `L²(0,∞)`. -/
noncomputable def airyPL : AiryL2 →L[ℂ] AiryL2 := airyIndProj (measurableSet_Ioi (a := (0 : ℝ)))

lemma airyPL_apply (f : AiryL2) : airyPL f = airyIndProj (measurableSet_Ioi (a := (0 : ℝ))) f := rfl

/-- **The Airy projector** `K_Ai = A P A`. -/
noncomputable def airyKAi : AiryL2 →L[ℂ] AiryL2 := airyAL ∘L airyPL ∘L airyAL

lemma airyKAi_apply (f : AiryL2) : airyKAi f = airyA (airyPL (airyA f)) := rfl

lemma airyPL_idem (f : AiryL2) : airyPL (airyPL f) = airyPL f := airyIndProj_idem _ f

lemma airyPL_inner (f g : AiryL2) : inner ℂ (airyPL f) g = inner ℂ f (airyPL g) :=
  airyIndProj_inner _ f g

theorem airyKAi_inner (f g : AiryL2) : inner ℂ (airyKAi f) g = inner ℂ f (airyKAi g) := by
  rw [airyKAi_apply, airyKAi_apply, airyA_inner_left, airyPL_inner, airyA_inner_left]

theorem airyKAi_idem (f : AiryL2) : airyKAi (airyKAi f) = airyKAi f := by
  rw [airyKAi_apply, airyKAi_apply, airyA_airyA, airyPL_idem]

theorem isStarProjection_airyKAi : IsStarProjection airyKAi := by
  refine ⟨?_, ?_⟩
  · refine ContinuousLinearMap.ext fun f => ?_
    exact airyKAi_idem f
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro f g
    exact airyKAi_inner f g

lemma airyPL_inner_self (x : AiryL2) : inner ℂ (airyPL x) x = inner ℂ (airyPL x) (airyPL x) := by
  conv_lhs => rw [← airyPL_idem x]
  rw [airyPL_inner]

/-- `⟨K_Ai f, f⟩ = ‖P A f‖²`. -/
theorem inner_airyKAi_self (f : AiryL2) :
    inner ℂ (airyKAi f) f = ((‖airyPL (airyA f)‖ ^ 2 : ℝ) : ℂ) := by
  rw [airyKAi_apply, airyA_inner_left, airyPL_inner_self, inner_self_eq_norm_sq_to_K]
  simp

lemma norm_airyPL_le (x : AiryL2) : ‖airyPL x‖ ≤ ‖x‖ :=
  norm_airyMulL2_le (airyInd_measurable measurableSet_Ioi) (airyInd_bound (Ioi (0 : ℝ))) x

theorem norm_airyKAi_le (f : AiryL2) : ‖airyKAi f‖ ≤ ‖f‖ := by
  rw [airyKAi_apply, airyA_norm, ← airyA_norm f]
  exact norm_airyPL_le _

/-! ### The space `PW = A L²(0,∞)` -/

/-- The Airy Paley–Wiener space `PW = {F : K_Ai F = F} = A L²(0,∞)`, a closed subspace of `L²(ℝ)`. -/
noncomputable def airyPW : Submodule ℂ AiryL2 :=
  LinearMap.ker ((airyKAi - ContinuousLinearMap.id ℂ AiryL2 : AiryL2 →L[ℂ] AiryL2) : AiryL2 →ₗ[ℂ] AiryL2)

lemma mem_airyPW_iff (F : AiryL2) : F ∈ airyPW ↔ airyKAi F = F := by
  simp [airyPW, sub_eq_zero]

lemma isClosed_airyPW : IsClosed (airyPW : Set AiryL2) :=
  ContinuousLinearMap.isClosed_ker (airyKAi - ContinuousLinearMap.id ℂ AiryL2)

/-- `PW = A L²(0,∞)`: `F ∈ PW` iff `F = A φ` with `φ ∈ L²(0,∞)`. -/
theorem mem_airyPW_iff_exists (F : AiryL2) :
    F ∈ airyPW ↔ ∃ φ : AiryL2, airyPL φ = φ ∧ airyA φ = F := by
  rw [mem_airyPW_iff]
  constructor
  · intro h
    exact ⟨airyPL (airyA F), airyPL_idem _, by rw [← airyKAi_apply]; exact h⟩
  · rintro ⟨φ, hφ, rfl⟩
    rw [airyKAi_apply, airyA_airyA, hφ]

theorem airyKAi_mem_airyPW (f : AiryL2) : airyKAi f ∈ airyPW := by
  rw [mem_airyPW_iff]; exact airyKAi_idem f

/-! ### The integral kernel -/

/-- `K(u, ·) = A(1_{t>0} Ai(u+·)) ∈ L²(ℝ)`. -/
noncomputable def airyKerL2 (u : ℝ) : AiryL2 := airyA (airyHalf u)

lemma airyPL_airyHalf (u : ℝ) : airyPL (airyHalf u) = airyHalf u := by
  rw [airyPL_apply, airyIndProj_eq_self_iff]
  filter_upwards [airyHalf_coeFn u] with t ht htn
  rw [ht]; simp [htn]

/-- `K(u,·)` as an `L²` function is the Airy kernel `v ↦ K(u,v)`. -/
theorem airyKerL2_ae (u : ℝ) : airyKerL2 u =ᵐ[volume] fun v => (airyKer u v : ℂ) := by
  have h := airyA_indProj_ae (airyHalf u)
  rw [← airyPL_apply, airyPL_airyHalf] at h
  unfold airyKerL2
  refine h.trans (Eventually.of_forall fun v => ?_)
  show airyPsi (airyHalf u) v = _
  unfold airyPsi
  show _ = (airyKer u v : ℂ)
  rw [airyKer_eq_integral, ← integral_complex_ofReal]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [airyHalf_coeFn u] with t ht htm
  rw [ht]
  simp [htm]

theorem norm_airyKerL2_sq (u : ℝ) : ‖airyKerL2 u‖ ^ 2 = airyKer u u := by
  unfold airyKerL2; rw [airyA_norm, norm_airyHalf_sq]

lemma airyPsi_airyA (f : AiryL2) (u : ℝ) : airyPsi (airyA f) u = inner ℂ (airyKerL2 u) f := by
  rw [airyPsi_eq_inner, airyKerL2, airyA_inner_left]

lemma inner_airyKerL2 (u : ℝ) (f : AiryL2) :
    inner ℂ (airyKerL2 u) f = ∫ v, (airyKer u v : ℂ) * f v := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [airyKerL2_ae u] with v hv
  rw [hv, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

lemma integrable_airyKer_mul (u : ℝ) (f : AiryL2) :
    Integrable (fun v => (airyKer u v : ℂ) * f v) volume := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (airyKerL2 u) f
  refine h.congr ?_
  filter_upwards [airyKerL2_ae u] with v hv
  rw [hv, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- **`K_Ai` is the integral operator with kernel `K(u,v)`**: for every `f ∈ L²(ℝ)`,
`(K_Ai f)(u) = ∫ K(u,v) f(v) dv` for a.e. `u` (the integral converges absolutely for every `u`). -/
theorem airyKAi_ae (f : AiryL2) :
    airyKAi f =ᵐ[volume] fun u => ∫ v, (airyKer u v : ℂ) * f v := by
  have h := airyA_indProj_ae (airyA f)
  rw [← airyPL_apply] at h
  refine h.trans (Eventually.of_forall fun u => ?_)
  show airyPsi (airyA f) u = _
  rw [airyPsi_airyA, inner_airyKerL2]

/-- **Reproducing property of `PW`**: `F(u) = ∫ K(u,v) F(v) dv` a.e., for `F ∈ PW`. -/
theorem airyPW_reproducing {F : AiryL2} (hF : F ∈ airyPW) :
    F =ᵐ[volume] fun u => ∫ v, (airyKer u v : ℂ) * F v := by
  have h := airyKAi_ae F
  rwa [(mem_airyPW_iff F).mp hF] at h

/-! ### `K_u = A_u A_u^*` -/

/-- The projection onto `L²(u, ∞)`. -/
noncomputable def airyPu (u : ℝ) : AiryL2 →L[ℂ] AiryL2 := airyIndProj (measurableSet_Ioi (a := u))

lemma airyPu_idem (u : ℝ) (f : AiryL2) : airyPu u (airyPu u f) = airyPu u f := airyIndProj_idem _ f

lemma airyPu_inner (u : ℝ) (f g : AiryL2) : inner ℂ (airyPu u f) g = inner ℂ f (airyPu u g) :=
  airyIndProj_inner _ f g

/-- `A_u = 1_{(u,∞)} A 1_{(0,∞)} : L²(0,∞) → L²(u,∞)`. -/
noncomputable def airyAu (u : ℝ) : AiryL2 →L[ℂ] AiryL2 := airyPu u ∘L airyAL ∘L airyPL

/-- `A_u^* = 1_{(0,∞)} A 1_{(u,∞)}`. -/
noncomputable def airyAuStar (u : ℝ) : AiryL2 →L[ℂ] AiryL2 := airyPL ∘L airyAL ∘L airyPu u

/-- `K_u = 1_{(u,∞)} K_Ai 1_{(u,∞)}`. -/
noncomputable def airyKu (u : ℝ) : AiryL2 →L[ℂ] AiryL2 := airyPu u ∘L airyKAi ∘L airyPu u

theorem airyAuStar_inner (u : ℝ) (g f : AiryL2) :
    inner ℂ (airyAuStar u g) f = inner ℂ g (airyAu u f) := by
  simp only [airyAuStar, airyAu, ContinuousLinearMap.comp_apply, airyAL_apply]
  rw [airyPL_inner, airyA_inner_left, airyPu_inner]

/-- `A_u^*` is the Hilbert-space adjoint of `A_u`. -/
theorem airyAu_adjoint (u : ℝ) : ContinuousLinearMap.adjoint (airyAu u) = airyAuStar u :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => airyAuStar_inner u x y).symm

/-- **`K_u = A_u A_u^*`.** -/
theorem airyKu_eq (u : ℝ) : airyKu u = airyAu u ∘L airyAuStar u := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [airyKu, airyAu, airyAuStar, ContinuousLinearMap.comp_apply, airyAL_apply, airyKAi_apply,
    airyPL_idem]

theorem airyKu_eq_adjoint (u : ℝ) :
    airyKu u = airyAu u ∘L ContinuousLinearMap.adjoint (airyAu u) := by
  rw [airyAu_adjoint, airyKu_eq]

/-- `K_u` is positive: `⟨K_u f, f⟩ = ‖A_u^* f‖²`. -/
theorem inner_airyKu_self (u : ℝ) (f : AiryL2) :
    inner ℂ (airyKu u f) f = ((‖airyAuStar u f‖ ^ 2 : ℝ) : ℂ) := by
  rw [airyKu_eq, ContinuousLinearMap.comp_apply, ← inner_conj_symm, ← airyAuStar_inner u,
    inner_self_eq_norm_sq_to_K]
  simp

theorem airyKu_inner (u : ℝ) (f g : AiryL2) : inner ℂ (airyKu u f) g = inner ℂ f (airyKu u g) := by
  simp only [airyKu, ContinuousLinearMap.comp_apply]
  rw [airyPu_inner, airyKAi_inner, airyPu_inner]

/-- The kernel of `K_u`: `(K_u f)(x) = 1_{x>u} ∫_{y>u} K(x,y) f(y) dy` a.e. -/
theorem airyKu_ae (u : ℝ) (f : AiryL2) :
    airyKu u f =ᵐ[volume] fun x => (Ioi u).indicator (fun x => ∫ y in Ioi u, (airyKer x y : ℂ) * f y) x := by
  have h1 : airyPu u f =ᵐ[volume] (Ioi u).indicator (f : ℝ → ℂ) := airyIndProj_coeFn _ f
  have h2 := airyKAi_ae (airyPu u f)
  have h3 : airyPu u (airyKAi (airyPu u f)) =ᵐ[volume]
      (Ioi u).indicator (airyKAi (airyPu u f) : ℝ → ℂ) := airyIndProj_coeFn _ _
  filter_upwards [h3, h2] with x hx3 hx2
  show airyPu u (airyKAi (airyPu u f)) x = _
  rw [hx3]
  by_cases hx : x ∈ Ioi u
  · simp only [Set.indicator_of_mem hx]
    rw [hx2, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae ?_
    filter_upwards [h1] with y hy
    rw [hy]
    by_cases hy' : y ∈ Ioi u <;> simp [hy']
  · simp [hx]

/-- info: 'FormalResearch.Special.isStarProjection_airyKAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.isStarProjection_airyKAi

/-- info: 'FormalResearch.Special.inner_airyKAi_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.inner_airyKAi_self

/-- info: 'FormalResearch.Special.mem_airyPW_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mem_airyPW_iff_exists

/-- info: 'FormalResearch.Special.airyKerL2_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerL2_ae

/-- info: 'FormalResearch.Special.airyKAi_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKAi_ae

/-- info: 'FormalResearch.Special.airyPW_reproducing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_reproducing

/-- info: 'FormalResearch.Special.airyKu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKu_eq

/-- info: 'FormalResearch.Special.inner_airyKu_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.inner_airyKu_self

/-- info: 'FormalResearch.Special.airyKu_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKu_ae

end FormalResearch.Special

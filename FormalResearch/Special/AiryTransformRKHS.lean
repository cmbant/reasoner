module

public import FormalResearch.Special.AiryTransformHilbert

/-!
# `PW` as a reproducing-kernel space of entire functions; the function-level `K_u` is the Hilbert-space `K_u`

**Entire model.**  For `F ∈ L²(ℝ)` put `airyPWFun F (z) = Ψ(P A F)(z)` (`AiryTransformEval`).  For `F ∈ PW`:

* `airyPWFun_ae`: `F(u) = airyPWFun F (u)` for a.e. real `u` (so `airyPWFun F` is the entire representative of `F`);
* `differentiable_airyPWFun`, `norm_airyPWFun_sq_le`: it is entire with `‖F(z)‖² ≤ 23 ‖F‖² (1+|z|) e(z)`;
* `airyPW_eval_inner`: **reproducing kernel**: `F(z) = ⟨k_z, F⟩`, `k_z = A(1_{t>0} Ai(z̄+·)) ∈ PW`
  (`airyKerCL2`), with `⟨k_z, k_w⟩ = K(z, w̄)` the complex Airy kernel `airyKerC` (`inner_airyKerCL2`), so that
  `|F(z)| ≤ ‖F‖ K(z̄, z)^{1/2}` (`K(z̄, z) = κ(z̄)`).

**`K_u` bridge** (`airyKu_airyKerOp`): for real measurable `f` with `∫_u^∞ f² < ∞`, the Hilbert-space operator
`K_u = A_u A_u^*` (`AiryTransformProj`) applied to `1_{(u,∞)} f` is, a.e., `1_{(u,∞)}` times the function-level
operator `airyKerOp u f (x) = ∫_u^∞ K(x,y) f(y) dy` of `AiryKernelOpL2`.  So the function-level bounded/self-adjoint/
positive statements there and the operator statements here are two views of one operator.

**Not formalised:** the converse direction (a Paley–Wiener-type characterisation of `PW` as the space of entire
`F` with the above growth and `F|_ℝ ∈ L²`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

/-- `k_z = A(1_{t>0} Ai(z̄ + ·)) ∈ PW`: the reproducing kernel of `PW` at `z ∈ ℂ`. -/
noncomputable def airyKerCL2 (z : ℂ) : AiryL2 := airyA (airyHalfC ((starRingEnd ℂ) z))

lemma airyPL_airyHalfC (w : ℂ) : airyPL (airyHalfC w) = airyHalfC w := by
  rw [airyPL_apply, airyIndProj_eq_self_iff]
  filter_upwards [airyHalfC_coeFn w] with t ht htn
  rw [ht]; simp [htn]

lemma airyKerCL2_mem (z : ℂ) : airyKerCL2 z ∈ airyPW :=
  (mem_airyPW_iff_exists _).mpr ⟨airyHalfC ((starRingEnd ℂ) z), airyPL_airyHalfC _, rfl⟩

lemma airyKerCL2_ofReal (x : ℝ) : airyKerCL2 (x : ℂ) = airyKerL2 x := by
  simp [airyKerCL2, airyKerL2, Complex.conj_ofReal, airyHalfC_ofReal]

/-- `Ψφ(z) = ⟨k_z, Aφ⟩`. -/
theorem airyPsiC_eq_inner_airyKerCL2 (φ : AiryL2) (z : ℂ) :
    airyPsiC φ z = inner ℂ (airyKerCL2 z) (airyA φ) := by
  rw [airyKerCL2, airyA_inner, airyPsiC_eq_inner]

/-- `⟨k_z, k_w⟩ = K(z, w̄)`, the complex Airy kernel. -/
theorem inner_airyKerCL2 (z w : ℂ) :
    inner ℂ (airyKerCL2 z) (airyKerCL2 w) = airyKerC z ((starRingEnd ℂ) w) := by
  unfold airyKerCL2
  rw [airyA_inner, MeasureTheory.L2.inner_def, airyKerC_eq_integral, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [airyHalfC_coeFn ((starRingEnd ℂ) z), airyHalfC_coeFn ((starRingEnd ℂ) w)] with t h1 h2
  rw [h1, h2, RCLike.inner_apply]
  by_cases hh : t ∈ Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem hh]
    have e : (starRingEnd ℂ) (airyAiC ((starRingEnd ℂ) z + (t : ℂ))) = airyAiC (z + (t : ℂ)) := by
      rw [conj_airyAiC]; simp
    rw [e]; ring
  · simp [hh]

/-- The entire representative `F(z) = Ψ(P A F)(z)` of `F ∈ PW`. -/
noncomputable def airyPWFun (F : AiryL2) (z : ℂ) : ℂ := airyPsiC (airyPL (airyA F)) z

theorem differentiable_airyPWFun (F : AiryL2) : Differentiable ℂ (airyPWFun F) :=
  differentiable_airyPsiC _

theorem norm_airyPWFun_sq_le (F : AiryL2) (z : ℂ) :
    ‖airyPWFun F z‖ ^ 2 ≤ 23 * ‖F‖ ^ 2 * (1 + ‖z‖) * airyEnv z := by
  have h := norm_airyPsiC_sq_le (airyPL (airyA F)) z
  have h2 : ‖airyPL (airyA F)‖ ≤ ‖F‖ := (norm_airyPL_le _).trans (airyA_norm F).le
  have h3 : ‖airyPL (airyA F)‖ ^ 2 ≤ ‖F‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : 0 ≤ (1 + ‖z‖) * airyEnv z := by have := airyEnv_pos z; positivity
  calc ‖airyPWFun F z‖ ^ 2 ≤ 23 * ‖airyPL (airyA F)‖ ^ 2 * (1 + ‖z‖) * airyEnv z := h
    _ = 23 * ‖airyPL (airyA F)‖ ^ 2 * ((1 + ‖z‖) * airyEnv z) := by ring
    _ ≤ 23 * ‖F‖ ^ 2 * ((1 + ‖z‖) * airyEnv z) := by gcongr
    _ = _ := by ring

/-- **`F ∈ PW` equals its entire representative on `ℝ`** (a.e.). -/
theorem airyPWFun_ae {F : AiryL2} (hF : F ∈ airyPW) :
    F =ᵐ[volume] fun u : ℝ => airyPWFun F (u : ℂ) := by
  have h1 := airyA_indProj_ae (airyA F)
  rw [← airyPL_apply, ← airyKAi_apply, (mem_airyPW_iff F).mp hF] at h1
  refine h1.trans (Eventually.of_forall fun u => ?_)
  show airyPsi (airyA F) u = _
  show airyPsi (airyA F) u = airyPsiC (airyPL (airyA F)) (u : ℂ)
  rw [airyPsiC_ofReal, airyPL_apply, airyPsi_indProj]

/-- **Reproducing property** at every `z ∈ ℂ`: `F(z) = ⟨k_z, F⟩`. -/
theorem airyPW_eval_inner {F : AiryL2} (hF : F ∈ airyPW) (z : ℂ) :
    airyPWFun F z = inner ℂ (airyKerCL2 z) F := by
  obtain ⟨φ, hφ, rfl⟩ := (mem_airyPW_iff_exists F).mp hF
  unfold airyPWFun
  rw [airyA_airyA, hφ, airyPsiC_eq_inner_airyKerCL2]

/-! ### The bridge to `airyKerOp` -/

lemma memLp_airyKuInput (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    MemLp (fun y : ℝ => (((Ioi u).indicator f y : ℝ) : ℂ)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y : ℝ => (((Ioi u).indicator f y : ℝ) : ℂ)) volume :=
    (Complex.measurable_ofReal.comp (hf.indicator measurableSet_Ioi)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf2
  refine hf2.congr (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Ioi u <;> simp [hy]

/-- `1_{(u,∞)} f` as an element of `L²(ℝ)`. -/
noncomputable def airyKuInput (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) : AiryL2 := (memLp_airyKuInput u hf hf2).toLp _

/-- **`K_u` (Hilbert-space operator `A_u A_u^*`) = `airyKerOp` (function-level operator)**. -/
theorem airyKu_airyKerOp (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    airyKu u (airyKuInput u hf hf2) =ᵐ[volume]
      fun x => (((Ioi u).indicator (airyKerOp u f) x : ℝ) : ℂ) := by
  have h1 := airyKu_ae u (airyKuInput u hf hf2)
  have h2 : airyKuInput u hf hf2 =ᵐ[volume] fun y : ℝ => (((Ioi u).indicator f y : ℝ) : ℂ) :=
    (memLp_airyKuInput u hf hf2).coeFn_toLp
  filter_upwards [h1] with x hx
  rw [hx]
  by_cases hxu : x ∈ Ioi u
  · simp only [Set.indicator_of_mem hxu]
    unfold airyKerOp
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [h2] with y hy hyu
    rw [hy]
    simp [hyu]
  · simp [hxu]

/-- **Parseval in function form**: for `F, G ∈ PW` with entire representatives `airyPWFun`,
`⟨G, F⟩ = ∫ \overline{G} F = Σ_{n ≥ 1} F(a_n) \overline{G(a_n)} / Ai'(a_n)²`. -/
theorem airyPW_parseval_fun {F G : AiryL2} (hF : F ∈ airyPW) (hG : G ∈ airyPW) :
    HasSum (fun n : ℕ => airyPWFun F (airyZ n : ℂ) * (starRingEnd ℂ) (airyPWFun G (airyZ n : ℂ)) /
        (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ)) (inner ℂ G F) := by
  have h := airyPW_parseval_of_basis hF hG
  have hfun : (fun n : ℕ => inner ℂ (airyBasisVec n) F * (starRingEnd ℂ) (inner ℂ (airyBasisVec n) G)) =
      fun n : ℕ => airyPWFun F (airyZ n : ℂ) * (starRingEnd ℂ) (airyPWFun G (airyZ n : ℂ)) /
        (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ) := by
    funext n
    rw [airyPW_eval_inner hF, airyPW_eval_inner hG, airyKerCL2_ofReal]
    unfold airyBasisVec
    rw [inner_smul_left, inner_smul_left, Complex.conj_ofReal, map_mul, Complex.conj_ofReal]
    have hn := airyAi'_airyZ_ne_zero n
    have h1 : ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) =
        1 / (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div]
      congr 1
      have := sq_abs (airyAi' (airyZ n))
      field_simp
      rw [this]
    calc _ = (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) *
          (inner ℂ (airyKerL2 (airyZ n)) F * (starRingEnd ℂ) (inner ℂ (airyKerL2 (airyZ n)) G)) := by ring
      _ = _ := by rw [h1]; ring
  rw [hfun] at h
  exact h

/-- `‖K_u f‖ ≤ ‖f‖` (`K_u` is a contraction, dominated by the projection `K_Ai`). -/
theorem norm_airyKu_le (u : ℝ) (f : AiryL2) : ‖airyKu u f‖ ≤ ‖f‖ := by
  have h1 : ∀ g : AiryL2, ‖airyPu u g‖ ≤ ‖g‖ := fun g =>
    norm_airyMulL2_le (airyInd_measurable measurableSet_Ioi) (airyInd_bound (Ioi u)) g
  simp only [airyKu, ContinuousLinearMap.comp_apply]
  exact (h1 _).trans ((norm_airyKAi_le _).trans (h1 _))

/-- info: 'FormalResearch.Special.airyPW_parseval_fun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_parseval_fun

/-- info: 'FormalResearch.Special.airyPW_eval_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_eval_inner

/-- info: 'FormalResearch.Special.airyPWFun_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPWFun_ae

/-- info: 'FormalResearch.Special.inner_airyKerCL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.inner_airyKerCL2

/-- info: 'FormalResearch.Special.airyKu_airyKerOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKu_airyKerOp

/-- info: 'FormalResearch.Special.differentiable_airyPWFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.differentiable_airyPWFun

/-- info: 'FormalResearch.Special.norm_airyPWFun_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyPWFun_sq_le

/-- info: 'FormalResearch.Special.norm_airyKu_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyKu_le

end FormalResearch.Special

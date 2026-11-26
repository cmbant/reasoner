module

public import FormalResearch.SignUncertainty.OneProfileEnvelope
public import FormalResearch.Special.AiryTransformRKHS
public import FormalResearch.Special.AiryPwsPW
public import FormalResearch.Special.AiryCftQUnc
public import FormalResearch.Special.AiryCftMittagLeffler
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Airy cardinal system (`ce_airy_lp_proofs.tex`, Lemma `lem:al-kernel`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`, Lemma `lem:al-kernel` and `(eq:al-kernel)`.

With `airyZ n = airyZero (n + 1)` (`n : ℕ`, `0`-indexed so `airyZ 0 = a_1 > airyZ 1 = a_2 > …`
matches `airyPW_hilbertBasis`, `airyQ_hasSum_unc`, `airyCft_summable_inv_sq`, and
`lp (fun _ : ℕ => ℝ) 2`), the Airy cardinal functions are
`airyCardinal n z := dslope airyAiC (airyZ n : ℂ) z`, i.e. `Ai(z) / (z - a_{n+1})` for `z ≠ a_{n+1}`
and `Ai'(a_{n+1})` at `z = a_{n+1}`.

Main declarations:
* `airyCardinal`, `airyCardinalR`: entire complex and real-axis Airy cardinal functions `k_n`, with
  `airyCardinal_airyZ` (`k_m(a_n) = δ_{mn} Ai'(a_n)`), `differentiable_airyCardinal`, positive-axis
  `O(u^{-5/4} e^{-(2/3) u^{3/2}})` and negative-axis `O(|u|^{-5/4})` decay
  (`airyCardinalR_pos_decay`, `airyCardinalR_neg_decay`), exclusion `k_n ∉ 𝒢`
  (`not_inAiryClass_airyCardinal`), and pairwise product membership `k_m k_n ∈ 𝒢`
  (`airyCardinal_mul_inAiryClass`).
* `airyCardinalL2`, `airyCardinalPW`, `airyCardinalBasis`: signed bridge `k_n = K(·, a_n) / Ai'(a_n)`
  to `airyBasisVec` (`AiryTransformBasis`) and `airyPW_hilbertBasis` (`AiryTransformHilbert`),
  entire representative `airyPWFun (airyCardinalL2 n) = airyCardinal n`, and `L²(ℝ)` orthonormality
  (`integral_airyCardinalR_mul`).
* `airyCardinal_ker_hasSum`, `airyCardinal_ker_summable_norm`,
  `airyCardinal_ker_tendstoLocallyUniformly`: the reproducing kernel expansion `(eq:al-kernel)`,
  `∑_n k_n(z) k_n(w) = K(z, w) = airyKerC z w`, absolutely and locally uniformly on `ℂ × ℂ`.
* `airyCardinalSeries`, `airyCardinalSeriesR`, `airyCardinalSeriesC`: cardinal series `q_c = ∑_n c_n k_n`
  for `c ∈ ℓ²` (real and complex), locally uniform convergence, entireness, `q_c(a_n) = c_n Ai'(a_n)`,
  `∫ q_c² = ∑_n c_n²` (`∫ |q_c|² = ∑_n |c_n|²`), and `q_c₁ q_c₂, q_c² ∈ 𝒢` via `airyClassG_PW_mul`.
* `airyEvalVec`: the `ℓ²` evaluation vector `(k_n(x))_n` with `‖airyEvalVec x‖² = K(x, x)` and
  `q_c(x) = ⟪airyEvalVec x, c⟫`.
* `lem_al_kernel`: bundled statement of Lemma `lem:al-kernel`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped ENNReal ComplexInnerProductSpace RealInnerProductSpace Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Zeros `airyZ n = a_{n+1}`: basic negativity and spacing helpers -/

lemma airyZ_neg (n : ℕ) : airyZ n < 0 := airyZero_neg (n + 1)

lemma airyZ_lt_neg_two (n : ℕ) : airyZ n < -2 := by
  have h1 : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti le_rfl (Nat.le_add_left 1 n)
  obtain ⟨_, ha1⟩ := airyZero_one
  unfold airyZ
  linarith only [h1, ha1]

lemma two_lt_abs_airyZ (n : ℕ) : 2 < |airyZ n| := by
  rw [abs_of_neg (airyZ_neg n)]
  linarith only [airyZ_lt_neg_two n]

lemma airyZ_strictAnti : StrictAnti airyZ := by
  intro m n hmn
  exact airyZero_lt_of_lt (Nat.succ_le_succ (Nat.zero_le m)) (Nat.succ_lt_succ hmn)

lemma airyZ_anti {m n : ℕ} (h : m ≤ n) : airyZ n ≤ airyZ m :=
  airyZ_strictAnti.antitone h

lemma summable_airyZ_inv_sq : Summable (fun n : ℕ => ((airyZ n) ^ 2)⁻¹) :=
  airyCft_summable_inv_sq

lemma eventually_le_neg_airyZ (C : ℝ) : ∀ᶠ n : ℕ in atTop, C ≤ -airyZ n :=
  airyCft_eventually_ge C

lemma airyAiC_airyZ (n : ℕ) : airyAiC (airyZ n : ℂ) = 0 := by
  rw [airyAiC_ofReal, airyAi_airyZ, Complex.ofReal_zero]

/-! ### The Airy cardinal functions `k_n(z) = Ai(z) / (z - a_{n+1})` -/

/-- The `n`-th Airy cardinal function `k_n(z) = Ai(z) / (z - a_{n+1})`, defined globally via
`dslope` so `k_n(a_{n+1}) = Ai'(a_{n+1})`. -/
noncomputable def airyCardinal (n : ℕ) (z : ℂ) : ℂ :=
  dslope airyAiC (airyZ n : ℂ) z

/-- Real-axis Airy cardinal function `k_n(u)` for `u : ℝ`. -/
noncomputable def airyCardinalR (n : ℕ) (u : ℝ) : ℝ :=
  (airyCardinal n (u : ℂ)).re

lemma airyCardinal_of_ne (n : ℕ) {z : ℂ} (hz : z ≠ (airyZ n : ℂ)) :
    airyCardinal n z = airyAiC z / (z - (airyZ n : ℂ)) := by
  rw [airyCardinal, dslope_of_ne _ hz, slope_def_field, airyAiC_airyZ, sub_zero]

lemma airyCardinal_same (n : ℕ) :
    airyCardinal n (airyZ n : ℂ) = deriv airyAiC (airyZ n : ℂ) :=
  dslope_same airyAiC (airyZ n : ℂ)

lemma airyCardinal_same_eq_airyAi' (n : ℕ) :
    airyCardinal n (airyZ n : ℂ) = (airyAi' (airyZ n) : ℂ) := by
  rw [airyCardinal_same, deriv_airyAiC_ofReal]

/-- Node values: `k_m(a_n) = δ_{mn} Ai'(a_n)`. -/
theorem airyCardinal_airyZ (m n : ℕ) :
    airyCardinal m (airyZ n : ℂ) = if m = n then (airyAi' (airyZ n) : ℂ) else 0 := by
  by_cases h : m = n
  · subst h
    simp [airyCardinal_same_eq_airyAi']
  · have hne : (airyZ n : ℂ) ≠ (airyZ m : ℂ) := by
      intro heq
      exact h (airyZ_injective (Complex.ofReal_injective heq)).symm
    rw [airyCardinal_of_ne m hne, airyAiC_airyZ, zero_div]
    simp [h]

/-- Algebraic identity `(z - a_n) k_n(z) = Ai(z)` for every `z ∈ ℂ` (including `z = a_n`). -/
theorem mul_airyCardinal (n : ℕ) (z : ℂ) :
    (z - (airyZ n : ℂ)) * airyCardinal n z = airyAiC z := by
  by_cases hz : z = (airyZ n : ℂ)
  · subst hz
    rw [sub_self, zero_mul, airyAiC_airyZ]
  · rw [airyCardinal_of_ne n hz, mul_div_cancel₀ _ (sub_ne_zero.mpr hz)]

/-- Every Airy cardinal function `k_n` is entire. -/
theorem differentiable_airyCardinal (n : ℕ) : Differentiable ℂ (airyCardinal n) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr differentiable_airyAiC.differentiableOn

lemma airyCardinal_conj (n : ℕ) (z : ℂ) :
    airyCardinal n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (airyCardinal n z) := by
  by_cases hz : z = (airyZ n : ℂ)
  · subst hz
    rw [Complex.conj_ofReal, airyCardinal_same_eq_airyAi', Complex.conj_ofReal]
  · have hzc : (starRingEnd ℂ) z ≠ (airyZ n : ℂ) := by
      intro h
      apply hz
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    rw [airyCardinal_of_ne n hzc, airyCardinal_of_ne n hz, map_div₀, map_sub,
      Complex.conj_ofReal, conj_airyAiC]

lemma airyCardinal_ofReal_im (n : ℕ) (u : ℝ) : (airyCardinal n (u : ℂ)).im = 0 := by
  have h := airyCardinal_conj n (u : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma ofReal_airyCardinalR (n : ℕ) (u : ℝ) :
    (airyCardinalR n u : ℂ) = airyCardinal n (u : ℂ) :=
  Complex.ext rfl (airyCardinal_ofReal_im n u).symm

lemma continuous_airyCardinalR (n : ℕ) : Continuous (airyCardinalR n) :=
  Complex.continuous_re.comp ((differentiable_airyCardinal n).continuous.comp Complex.continuous_ofReal)

lemma airyCardinalR_of_ne (n : ℕ) {u : ℝ} (hu : u ≠ airyZ n) :
    airyCardinalR n u = airyAi u / (u - airyZ n) := by
  have huc : (u : ℂ) ≠ (airyZ n : ℂ) := fun h => hu (Complex.ofReal_injective h)
  have h := airyCardinal_of_ne n huc
  rw [airyAiC_ofReal, ← Complex.ofReal_sub, ← Complex.ofReal_div] at h
  unfold airyCardinalR
  rw [h, Complex.ofReal_re]

lemma airyCardinalR_airyZ (m n : ℕ) :
    airyCardinalR m (airyZ n) = if m = n then airyAi' (airyZ n) else 0 := by
  unfold airyCardinalR
  rw [airyCardinal_airyZ]
  split_ifs <;> simp

/-! ### Bridge to `AiryTransformBasis` / `AiryTransformHilbert` / `AiryTransformRKHS` -/

/-- Signed basis vector `k_n = K(·, a_n) / Ai'(a_n) ∈ L²(ℝ)`. -/
noncomputable def airyCardinalL2 (n : ℕ) : AiryL2 :=
  (((1 / airyAi' (airyZ n) : ℝ) : ℂ)) • airyKerL2 (airyZ n)

lemma airyCardinalL2_mem (n : ℕ) : airyCardinalL2 n ∈ airyPW :=
  Submodule.smul_mem _ _ (airyKerL2_mem _)

/-- Bridge to `airyBasisVec`: `airyCardinalL2 n` differs from `airyBasisVec n` by the unit sign
`|Ai'(a_n)| / Ai'(a_n) ∈ {-1, 1}`. -/
lemma airyCardinalL2_eq_sign_smul (n : ℕ) :
    airyCardinalL2 n = (((|airyAi' (airyZ n)| / airyAi' (airyZ n) : ℝ) : ℂ)) • airyBasisVec n := by
  unfold airyCardinalL2 airyBasisVec
  rw [smul_smul]
  congr 1
  have hne : airyAi' (airyZ n) ≠ 0 := airyAi'_airyZ_ne_zero n
  have habs : |airyAi' (airyZ n)| ≠ 0 := abs_ne_zero.mpr hne
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

lemma airyKerC_airyZ_right (n : ℕ) (z : ℂ) :
    airyKerC z (airyZ n : ℂ) = (airyAi' (airyZ n) : ℂ) * airyCardinal n z := by
  by_cases hz : z = (airyZ n : ℂ)
  · subst hz
    rw [airyKerC_self, airyAiC_airyZ, deriv_airyAiC_ofReal, airyCardinal_same_eq_airyAi']
    ring
  · rw [airyKerC_of_ne hz, airyKernelXY, airyAiC_airyZ, deriv_airyAiC_ofReal, airyCardinal_of_ne n hz]
    ring

/-- The entire representative of `airyCardinalL2 n ∈ PW` is `airyCardinal n`. -/
theorem airyPWFun_airyCardinalL2 (n : ℕ) (z : ℂ) :
    airyPWFun (airyCardinalL2 n) z = airyCardinal n z := by
  rw [airyPW_eval_inner (airyCardinalL2_mem n) z]
  unfold airyCardinalL2
  rw [inner_smul_right, ← airyKerCL2_ofReal, inner_airyKerCL2, Complex.conj_ofReal,
    airyKerC_airyZ_right]
  have hne : (airyAi' (airyZ n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (airyAi'_airyZ_ne_zero n)
  push_cast
  field_simp

theorem inner_airyKerCL2_airyCardinalL2 (n : ℕ) (z : ℂ) :
    inner ℂ (airyKerCL2 z) (airyCardinalL2 n) = airyCardinal n z := by
  rw [← airyPW_eval_inner (airyCardinalL2_mem n) z, airyPWFun_airyCardinalL2]

theorem airyCardinalL2_ae (n : ℕ) :
    airyCardinalL2 n =ᵐ[volume] fun u : ℝ => airyCardinal n (u : ℂ) := by
  filter_upwards [airyPWFun_ae (airyCardinalL2_mem n)] with u hu
  rw [hu, airyPWFun_airyCardinalL2]

theorem memLp_airyCardinal (n : ℕ) :
    MemLp (fun u : ℝ => airyCardinal n (u : ℂ)) 2 volume :=
  (Lp.memLp (airyCardinalL2 n)).ae_eq (airyCardinalL2_ae n)

theorem memLp_airyCardinalR (n : ℕ) :
    MemLp (airyCardinalR n) 2 volume := by
  have hm : AEStronglyMeasurable (airyCardinalR n) volume :=
    (continuous_airyCardinalR n).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h := (memLp_two_iff_integrable_sq_norm
    ((differentiable_airyCardinal n).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable).mp
    (memLp_airyCardinal n)
  refine h.congr (Eventually.of_forall fun u => ?_)
  dsimp only [Function.comp_apply]
  rw [← ofReal_airyCardinalR, Complex.norm_real]

/-- Orthonormality of `airyCardinalL2` in `L²(ℝ; ℂ)`. -/
theorem airyCardinalL2_orthonormal : Orthonormal ℂ airyCardinalL2 := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [airyCardinalL2_eq_sign_smul m, airyCardinalL2_eq_sign_smul n,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    (orthonormal_iff_ite.mp airyBasisVec_orthonormal) m n]
  by_cases h : m = n
  · subst h
    simp only [↓reduceIte, mul_one, ← Complex.ofReal_mul]
    have hne : airyAi' (airyZ m) ≠ 0 := airyAi'_airyZ_ne_zero m
    have hsq : (|airyAi' (airyZ m)| / airyAi' (airyZ m)) *
        (|airyAi' (airyZ m)| / airyAi' (airyZ m)) = 1 := by
      rw [div_mul_div_comm, ← sq, ← sq, sq_abs]
      exact div_self (pow_ne_zero 2 hne)
    rw [hsq, Complex.ofReal_one]
  · simp [h]

/-- `airyCardinalL2 n` as an element of the Hilbert space `airyPW`. -/
noncomputable def airyCardinalPW (n : ℕ) : airyPW :=
  ⟨airyCardinalL2 n, airyCardinalL2_mem n⟩

theorem airyCardinalPW_orthonormal : Orthonormal ℂ airyCardinalPW := by
  rw [orthonormal_iff_ite]
  intro m n
  have h := (orthonormal_iff_ite.mp airyCardinalL2_orthonormal) m n
  simpa [airyCardinalPW, Submodule.coe_inner] using h

/-- `{k_n}_{n : ℕ}` is a Hilbert basis of the Airy Paley–Wiener space `airyPW`. -/
noncomputable def airyCardinalBasis : HilbertBasis ℕ ℂ airyPW :=
  HilbertBasis.mkOfOrthogonalEqBot airyCardinalPW_orthonormal (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : ∀ n, inner ℂ (airyBasisVec n) (x : AiryL2) = 0 := by
      intro n
      have hc : inner ℂ (airyCardinalL2 n) (x : AiryL2) = 0 := by
        have h0 := (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨n, rfl⟩)
        simpa [airyCardinalPW, Submodule.coe_inner] using h0
      rw [airyCardinalL2_eq_sign_smul, inner_smul_left, Complex.conj_ofReal] at hc
      have hs : ((|airyAi' (airyZ n)| / airyAi' (airyZ n) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        exact div_ne_zero (abs_ne_zero.mpr (airyAi'_airyZ_ne_zero n)) (airyAi'_airyZ_ne_zero n)
      exact (mul_eq_zero.mp hc).resolve_left hs
    exact Subtype.ext (airyPW_eq_zero_of_inner_liouville x.2 hx'))

theorem coe_airyCardinalBasis : ⇑airyCardinalBasis = airyCardinalPW :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- Function-level `L²(ℝ)` orthonormality: `∫ k_m(u) k_n(u) du = δ_{mn}`. -/
theorem integrable_airyCardinalR_mul (m n : ℕ) :
    Integrable (fun u : ℝ => airyCardinalR m u * airyCardinalR n u) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (airyCardinalL2 m) (airyCardinalL2 n)
  have hae : (fun u : ℝ => inner ℂ (airyCardinalL2 m u) (airyCardinalL2 n u)) =ᵐ[volume]
      fun u : ℝ => ((airyCardinalR m u * airyCardinalR n u : ℝ) : ℂ) := by
    filter_upwards [airyCardinalL2_ae m, airyCardinalL2_ae n] with u hm hn
    rw [hm, hn, ← ofReal_airyCardinalR, ← ofReal_airyCardinalR, RCLike.inner_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
  exact (h.congr hae).re.congr (Eventually.of_forall fun _ => rfl)

theorem integral_airyCardinalR_mul (m n : ℕ) :
    (∫ u : ℝ, airyCardinalR m u * airyCardinalR n u) = if m = n then 1 else 0 := by
  have horth := (orthonormal_iff_ite.mp airyCardinalL2_orthonormal) m n
  rw [MeasureTheory.L2.inner_def] at horth
  have hae : (fun u : ℝ => inner ℂ (airyCardinalL2 m u) (airyCardinalL2 n u)) =ᵐ[volume]
      fun u : ℝ => ((airyCardinalR m u * airyCardinalR n u : ℝ) : ℂ) := by
    filter_upwards [airyCardinalL2_ae m, airyCardinalL2_ae n] with u hm hn
    rw [hm, hn, ← ofReal_airyCardinalR, ← ofReal_airyCardinalR, RCLike.inner_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
  rw [integral_congr_ae hae, integral_complex_ofReal] at horth
  by_cases h : m = n
  · subst h
    simp only [↓reduceIte] at horth ⊢
    exact Complex.ofReal_injective horth
  · simp only [h, ↓reduceIte] at horth ⊢
    exact Complex.ofReal_injective (by simpa using horth)

/-! ### Real-axis asymptotics, exclusion `k_n ∉ 𝒢`, and pairwise products `k_m k_n ∈ 𝒢` -/

/-- Positive-axis decay: `|k_n(u)| ≤ (1 / (2√π)) u^{-5/4} exp(-(2/3) u^{3/2})` for `u ≥ 1`. -/
theorem airyCardinalR_pos_decay (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |airyCardinalR n u| ≤
      (1 / (2 * √π)) * u ^ (-(5 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have han : airyZ n < 0 := airyZ_neg n
  have hne : u ≠ airyZ n := by linarith only [hu0, han]
  have hden : u < u - airyZ n := by linarith only [han]
  have hden_abs : |u - airyZ n| = u - airyZ n := abs_of_pos (by linarith only [hu0, hden])
  rw [airyCardinalR_of_ne n hne, abs_div, hden_abs]
  have hAi := airyAi_abs_le hu0
  have h1 : |airyAi u| / (u - airyZ n) ≤ |airyAi u| / u :=
    div_le_div_of_nonneg_left (abs_nonneg _) hu0 hden.le
  refine h1.trans ?_
  calc |airyAi u| / u
      ≤ ((1 / (2 * √π)) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ))) / u :=
        div_le_div_of_nonneg_right hAi hu0.le
    _ = (1 / (2 * √π)) * (u ^ (-(1 / 4 : ℝ)) * u ^ (-1 : ℝ)) *
          Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := by
        rw [Real.rpow_neg_one]; ring
    _ = (1 / (2 * √π)) * u ^ (-(5 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hu0]; norm_num

/-- Negative-axis decay: `|k_n(u)| ≤ 6 |u|^{-5/4}` for `u ≤ 2 a_n - 1`. -/
theorem airyCardinalR_neg_decay (n : ℕ) {u : ℝ} (hu : u ≤ 2 * airyZ n - 1) :
    |airyCardinalR n u| ≤ 6 * |u| ^ (-(5 / 4 : ℝ)) := by
  have han : airyZ n < 0 := airyZ_neg n
  have hu_neg : u < 0 := by linarith only [hu, han]
  have hne : u ≠ airyZ n := by linarith only [hu, han]
  have habs_u : |u| = -u := abs_of_neg hu_neg
  have hu_pos : 0 < |u| := by rw [habs_u]; linarith only [hu_neg]
  have hden : |u| / 2 ≤ |u - airyZ n| := by
    have hlt : u - airyZ n < 0 := by linarith only [hu, han]
    rw [abs_of_neg hlt, habs_u]
    linarith only [hu]
  have hAi : |airyAi u| ≤ 3 * |u| ^ (-(1 / 4 : ℝ)) := by
    have henv := airyAiC_envelope (u : ℂ)
    rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs] at henv
    have hre0 : (((u : ℂ) ^ (3 / 2 : ℂ)).re) = 0 := by
      have h := airyEnv_ofReal_neg hu_neg
      unfold airyEnv at h
      have := Real.exp_injective (h.trans Real.exp_zero.symm)
      linarith only [this]
    rw [hre0, mul_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs] at henv
    have hmono : (1 + |u|) ^ (-(1 / 4 : ℝ)) ≤ |u| ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hu_pos (by linarith only [hu_pos]) (by norm_num)
    exact henv.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  rw [airyCardinalR_of_ne n hne, abs_div]
  calc |airyAi u| / |u - airyZ n|
      ≤ (3 * |u| ^ (-(1 / 4 : ℝ))) / (|u| / 2) :=
        div_le_div₀ (by positivity) hAi (by positivity) hden
    _ = 6 * (|u| ^ (-(1 / 4 : ℝ)) * |u| ^ (-1 : ℝ)) := by
        rw [Real.rpow_neg_one]; field_simp; ring
    _ = 6 * |u| ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add hu_pos]; norm_num

/-- Positive-axis decay excludes `k_n` from `AiryClassG` (and hence from `InAiryClass`). -/
theorem not_airyClassG_airyCardinal (n : ℕ) : ¬ AiryClassG (airyCardinal n) := by
  rintro ⟨_, _, C, N, hC, hb⟩
  have han : airyZ n < 0 := airyZ_neg n
  -- Compare at large positive real `u = t^2`: `k_n(t^2) ≳ t^{-5/2} e^{-(2/3) t^3}` vs `e^{-(4/3) t^3}`.
  have hlim : Tendsto (fun t : ℝ => (t ^ (2 * N + 6)) * Real.exp (-(2 / 3) * t)) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * N + 6)
    have h2 : Tendsto (fun t : ℝ => (2 / 3 : ℝ) * t) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_id
    have h3 := (h1.comp h2).const_mul (((2 / 3 : ℝ) ^ (2 * N + 6))⁻¹)
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t _
    simp only [Function.comp_apply, mul_pow]
    field_simp
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (8 * √π * (C + 1) * (2 ^ N) * (1 - airyZ n)) by
    have := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < 1 - airyZ n := by linarith only [han]
    positivity))
  obtain ⟨t, ht1, htsmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and hsmall).exists
  set u := t ^ 2
  have hu1 : 1 ≤ u := by nlinarith only [ht1]
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hbu := hb (u : ℂ)
  rw [← ofReal_airyCardinalR, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ u), airyEnv_ofReal_nonneg hu0.le] at hbu
  have hlow := airyAi_lower_bound hu0
  have hu32 : u ^ (3 / 2 : ℝ) = t ^ 3 := by
    have hsq : √u = t := Real.sqrt_sq (by linarith only [ht1])
    rw [← sqrt_cube_eq_rpow hu0, hsq]
  have hu14 : u ^ (-(1 / 4 : ℝ)) = (√t)⁻¹ := by
    have hsq : √u = t := Real.sqrt_sq (by linarith only [ht1])
    rw [Real.rpow_neg hu0.le, ← sqrt_sqrt_eq_rpow hu0, hsq]
  have hfac : 1 / 2 ≤ 1 - 5 / 48 / u ^ (3 / 2 : ℝ) := by
    have hc : 1 ≤ u ^ (3 / 2 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
    have : 5 / 48 / u ^ (3 / 2 : ℝ) ≤ 5 / 48 := div_le_self (by norm_num) hc
    linarith only [this]
  have hAi_lb : (1 / (4 * √π)) * t⁻¹ * Real.exp (-(2 / 3) * t ^ 3) ≤ airyAi u := by
    have ht_sqrt : t⁻¹ ≤ (√t)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (by linarith only [ht1]))
        (Real.sqrt_le_iff.mpr ⟨by linarith only [ht1], by nlinarith only [ht1]⟩)
    calc (1 / (4 * √π)) * t⁻¹ * Real.exp (-(2 / 3) * t ^ 3)
        ≤ (1 / (4 * √π)) * (√t)⁻¹ * Real.exp (-(2 / 3) * t ^ 3) := by
          gcongr
      _ = (1 / (2 * √π)) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) * (1 / 2) := by
          rw [hu32, hu14]; ring
      _ ≤ (1 / (2 * √π)) * u ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3) * u ^ (3 / 2 : ℝ)) *
            (1 - 5 / 48 / u ^ (3 / 2 : ℝ)) := by
          gcongr
      _ ≤ airyAi u := hlow
  have hden_ub : u - airyZ n ≤ (1 - airyZ n) * t ^ 2 := by
    dsimp [u]
    nlinarith only [hu1, han]
  have hcard_lb : (1 / (4 * √π * (1 - airyZ n))) * (t ^ 3)⁻¹ * Real.exp (-(2 / 3) * t ^ 3) ≤
      |airyCardinalR n u| := by
    have hne : u ≠ airyZ n := by linarith only [hu0, han]
    rw [airyCardinalR_of_ne n hne, abs_div, abs_of_pos (airyAi_pos hu0.le),
      abs_of_pos (by linarith only [hu0, han])]
    calc (1 / (4 * √π * (1 - airyZ n))) * (t ^ 3)⁻¹ * Real.exp (-(2 / 3) * t ^ 3)
        = ((1 / (4 * √π)) * t⁻¹ * Real.exp (-(2 / 3) * t ^ 3)) / ((1 - airyZ n) * t ^ 2) := by
          field_simp
      _ ≤ airyAi u / (u - airyZ n) :=
          div_le_div₀ (airyAi_pos hu0.le).le hAi_lb (by linarith only [hu0, han]) hden_ub
  have hcard_ub : C * (1 + u) ^ N * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) ≤
      (C + 1) * (2 ^ N) * t ^ (2 * N) * Real.exp (-(4 / 3) * t ^ 3) := by
    rw [hu32]
    have h1u : 1 + u ≤ 2 * t ^ 2 := by dsimp [u]; linarith only [hu1]
    have hpow : (1 + u) ^ N ≤ (2 * t ^ 2) ^ N := pow_le_pow_left₀ (by positivity) h1u N
    have hpow_eq : (2 * t ^ 2) ^ N = 2 ^ N * t ^ (2 * N) := by rw [mul_pow, ← pow_mul, mul_comm 2 N]
    rw [hpow_eq] at hpow
    calc C * (1 + u) ^ N * Real.exp (-(4 / 3) * t ^ 3)
        ≤ (C + 1) * (2 ^ N * t ^ (2 * N)) * Real.exp (-(4 / 3) * t ^ 3) := by
          gcongr; linarith only [hC]
      _ = (C + 1) * (2 ^ N) * t ^ (2 * N) * Real.exp (-(4 / 3) * t ^ 3) := by ring
  have hcomb := hcard_lb.trans (hbu.trans hcard_ub)
  -- Multiply both sides by `t ^ 3 * exp((4/3) t^3)` and use `t ≤ t^3` for `t ≥ 1`.
  have ht3 : t ≤ t ^ 3 := by nlinarith only [ht1, sq_nonneg (t - 1)]
  have hexp_le : Real.exp (-(2 / 3) * t ^ 3) ≤ Real.exp (-(2 / 3) * t) :=
    Real.exp_le_exp.mpr (by linarith only [ht3])
  have hexp_split : Real.exp (-(2 / 3) * t ^ 3) =
      Real.exp ((2 / 3) * t ^ 3) * Real.exp (-(4 / 3) * t ^ 3) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp_split] at hcomb
  have hEpos : 0 < Real.exp (-(4 / 3) * t ^ 3) := Real.exp_pos _
  have hcomb2 : (1 / (4 * √π * (1 - airyZ n))) * (t ^ 3)⁻¹ * Real.exp ((2 / 3) * t ^ 3) ≤
      (C + 1) * 2 ^ N * t ^ (2 * N) :=
    le_of_mul_le_mul_right (by simpa only [mul_assoc] using hcomb) hEpos
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hcomb3 : 1 / (4 * √π * (1 - airyZ n)) ≤
      (C + 1) * 2 ^ N * t ^ (2 * N + 3) * Real.exp (-(2 / 3) * t ^ 3) := by
    have hmul := mul_le_mul_of_nonneg_right hcomb2
      (mul_nonneg (pow_nonneg ht_pos.le 3) (Real.exp_pos (-(2 / 3) * t ^ 3)).le)
    have hlhs : (1 / (4 * √π * (1 - airyZ n))) * (t ^ 3)⁻¹ * Real.exp ((2 / 3) * t ^ 3) *
        (t ^ 3 * Real.exp (-(2 / 3) * t ^ 3)) = 1 / (4 * √π * (1 - airyZ n)) := by
      have hexp1 : Real.exp ((2 / 3) * t ^ 3) * Real.exp (-(2 / 3) * t ^ 3) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ = (1 / (4 * √π * (1 - airyZ n))) * ((t ^ 3)⁻¹ * t ^ 3) *
            (Real.exp ((2 / 3) * t ^ 3) * Real.exp (-(2 / 3) * t ^ 3)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero 3 ht_pos.ne'), hexp1, mul_one, mul_one]
    have hrhs : (C + 1) * 2 ^ N * t ^ (2 * N) * (t ^ 3 * Real.exp (-(2 / 3) * t ^ 3)) =
        (C + 1) * 2 ^ N * t ^ (2 * N + 3) * Real.exp (-(2 / 3) * t ^ 3) := by
      rw [pow_add]; ring
    rwa [hlhs, hrhs] at hmul
  have hpow_le : t ^ (2 * N + 3) ≤ t ^ (2 * N + 6) :=
    pow_le_pow_right₀ ht1 (by omega)
  have hcomb4 : 1 / (4 * √π * (1 - airyZ n)) ≤
      (C + 1) * 2 ^ N * (t ^ (2 * N + 6) * Real.exp (-(2 / 3) * t)) := by
    calc 1 / (4 * √π * (1 - airyZ n))
        ≤ (C + 1) * 2 ^ N * t ^ (2 * N + 3) * Real.exp (-(2 / 3) * t ^ 3) := hcomb3
      _ ≤ (C + 1) * 2 ^ N * t ^ (2 * N + 6) * Real.exp (-(2 / 3) * t) := by
          have : 0 ≤ (C + 1) * (2 : ℝ) ^ N := by positivity
          gcongr
      _ = (C + 1) * 2 ^ N * (t ^ (2 * N + 6) * Real.exp (-(2 / 3) * t)) := by ring
  have hpos_den : 0 < (C + 1) * (2 : ℝ) ^ N := by positivity
  have hlt := mul_lt_mul_of_pos_left htsmall hpos_den
  have hrhs_simp : (C + 1) * (2 : ℝ) ^ N *
      (1 / (8 * √π * (C + 1) * 2 ^ N * (1 - airyZ n))) =
      1 / (8 * √π * (1 - airyZ n)) := by
    have := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < 1 - airyZ n := by linarith only [han]
    field_simp
  rw [hrhs_simp] at hlt
  have hpos_lhs : 0 < 1 / (8 * √π * (1 - airyZ n)) := by
    have := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < 1 - airyZ n := by linarith only [han]
    positivity
  have htwo : 1 / (4 * √π * (1 - airyZ n)) = 2 * (1 / (8 * √π * (1 - airyZ n))) := by
    have := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < 1 - airyZ n := by linarith only [han]
    field_simp
    ring
  linarith only [hcomb4, hlt, hpos_lhs, htwo]

theorem not_inAiryClass_airyCardinal (n : ℕ) : ¬ InAiryClass (airyCardinal n) := by
  intro h
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, _⟩ := h
  refine not_airyClassG_airyCardinal n ⟨hd, hi, C, ⌈max ν 0⌉₊, hC, fun z => (hb z).trans ?_⟩
  have hp : (1 + ‖z‖) ^ ν ≤ (1 + ‖z‖) ^ (⌈max ν 0⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [norm_nonneg z])
      ((le_max_left ν 0).trans (Nat.le_ceil _))
  rw [Real.rpow_natCast] at hp
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (airyEnv_pos z).le

lemma inAiryClass_of_airyClassG {f : ℂ → ℂ} (hf : AiryClassG f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) : InAiryClass f := by
  obtain ⟨C, N, hC, hb⟩ := hf.bound
  refine ⟨hf.differentiable, hf.integrable, ⟨C, (N : ℝ), hC, fun z => ?_⟩, hreal⟩
  rw [Real.rpow_natCast]
  exact hb z

/-- Pairwise products `k_m k_n` lie in `AiryClassG` (`PW · PW ⊂ 𝒢`). -/
theorem airyCardinal_mul_mem_airyClassG (m n : ℕ) :
    AiryClassG (fun z => airyCardinal m z * airyCardinal n z) := by
  have h := airyClassG_PW_mul (airyCardinalL2_mem m) (airyCardinalL2_mem n)
  simpa only [airyPWFun_airyCardinalL2] using h

/-- Pairwise products `k_m k_n` lie in `InAiryClass` (`𝒢`). -/
theorem airyCardinal_mul_inAiryClass (m n : ℕ) :
    InAiryClass (fun z => airyCardinal m z * airyCardinal n z) := by
  refine inAiryClass_of_airyClassG (airyCardinal_mul_mem_airyClassG m n) fun x => ?_
  rw [← ofReal_airyCardinalR, ← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_im]

/-! ### Compact-set tail bounds and the reproducing kernel expansion `(eq:al-kernel)` -/

/-- Uniform bound on `‖k_n(z)‖` for `‖z‖ ≤ R` and `-airyZ n ≥ 2 R + 1`. -/
lemma norm_airyCardinal_le_on_ball {R : ℝ} (_hR : 0 ≤ R) {n : ℕ}
    (hn : 2 * R + 1 ≤ -airyZ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖airyCardinal n z‖ ≤ (6 * Real.exp ((2 / 3) * R ^ (3 / 2 : ℝ))) / (-airyZ n) := by
  have han : airyZ n < 0 := airyZ_neg n
  have hna : ‖(airyZ n : ℂ)‖ = -airyZ n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg han]
  have hden : (-airyZ n) / 2 ≤ ‖z - (airyZ n : ℂ)‖ := by
    have h1 := norm_sub_norm_le (airyZ n : ℂ) z
    rw [norm_sub_rev, hna] at h1
    linarith only [h1, hz, hn]
  have hne : z ≠ (airyZ n : ℂ) := by
    intro heq
    rw [heq, sub_self, norm_zero] at hden
    linarith only [hden, han]
  have hAi : ‖airyAiC z‖ ≤ 3 * Real.exp ((2 / 3) * R ^ (3 / 2 : ℝ)) := by
    refine (airyAiC_norm_le_exp_rpow z).trans ?_
    gcongr
  rw [airyCardinal_of_ne n hne, norm_div]
  calc ‖airyAiC z‖ / ‖z - (airyZ n : ℂ)‖
      ≤ (3 * Real.exp ((2 / 3) * R ^ (3 / 2 : ℝ))) / ((-airyZ n) / 2) :=
        div_le_div₀ (by positivity) hAi (by linarith only [han]) hden
    _ = (6 * Real.exp ((2 / 3) * R ^ (3 / 2 : ℝ))) / (-airyZ n) := by ring

/-- Global majorant sequence `u_R n ≥ ‖k_n(z)‖` on `closedBall 0 R`, with `∑_n (u_R n)² < ∞`. -/
lemma exists_airyCardinal_ball_majorant (R : ℝ) :
    ∃ u : ℕ → ℝ, (∀ n, 0 ≤ u n) ∧ Summable (fun n => (u n) ^ 2) ∧
      ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R, ‖airyCardinal n z‖ ≤ u n := by
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hev := eventually_le_neg_airyZ (2 * R' + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  -- On `n < N₀`, each continuous `z ↦ ‖airyCardinal n z‖` is bounded on `closedBall 0 R'`.
  have hfin : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ closedBall (0 : ℂ) R', ‖airyCardinal n z‖ ≤ B := by
    intro n
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
      (differentiable_airyCardinal n).continuous.continuousOn
    refine ⟨max B 0, le_max_right B 0, fun z hz => ?_⟩
    exact (hB z hz).trans (le_max_left B 0)
  choose B hB0 hB using hfin
  set M := 6 * Real.exp ((2 / 3) * R' ^ (3 / 2 : ℝ))
  let u : ℕ → ℝ := fun n => if n < N₀ then B n else M / (-airyZ n)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    dsimp [u]
    split_ifs with h
    · exact hB0 n
    · have : 0 < -airyZ n := neg_pos.mpr (airyZ_neg n)
      positivity
  · have hsum_tail : Summable (fun n : ℕ => (M / (-airyZ n)) ^ 2) := by
      have heq : (fun n : ℕ => (M / (-airyZ n)) ^ 2) = fun n => M ^ 2 * ((airyZ n) ^ 2)⁻¹ := by
        ext n
        have : airyZ n ≠ 0 := (airyZ_neg n).ne
        field_simp
      rw [heq]
      exact summable_airyZ_inv_sq.mul_left (M ^ 2)
    refine hsum_tail.congr_cofinite ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N₀] with n hn
    dsimp [u]
    have hnot : ¬ n < N₀ := not_lt.mpr hn
    simp [hnot]
  · intro n z hz
    have hz' : z ∈ closedBall (0 : ℂ) R' :=
      closedBall_subset_closedBall (le_max_left R 0) hz
    dsimp [u]
    split_ifs with h
    · exact hB n z hz'
    · exact norm_airyCardinal_le_on_ball hR' (hN₀ n (not_lt.mp h)) (mem_closedBall_zero_iff.mp hz')

/-- **`(eq:al-kernel)`**: `∑_n k_n(z) k_n(w) = K(z, w)` (`HasSum`) for all `z, w ∈ ℂ`. -/
theorem airyCardinal_ker_hasSum (z w : ℂ) :
    HasSum (fun n : ℕ => airyCardinal n z * airyCardinal n w) (airyKerC z w) := by
  let G : airyPW := ⟨airyKerCL2 z, airyKerCL2_mem z⟩
  let F : airyPW := ⟨airyKerCL2 ((starRingEnd ℂ) w), airyKerCL2_mem _⟩
  have h := airyCardinalBasis.hasSum_inner_mul_inner G F
  rw [coe_airyCardinalBasis] at h
  have hinner : inner ℂ G F = airyKerC z w := by
    change inner ℂ (airyKerCL2 z) (airyKerCL2 ((starRingEnd ℂ) w)) = airyKerC z w
    rw [inner_airyKerCL2, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [hinner] at h
  refine h.congr_fun fun n => ?_
  have h1 : inner ℂ G (airyCardinalPW n) = airyCardinal n z :=
    inner_airyKerCL2_airyCardinalL2 n z
  have h2 : inner ℂ (airyCardinalPW n) F = airyCardinal n w := by
    change inner ℂ (airyCardinalL2 n) (airyKerCL2 ((starRingEnd ℂ) w)) = airyCardinal n w
    rw [← inner_conj_symm, inner_airyKerCL2_airyCardinalL2, airyCardinal_conj,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [h1, h2]

/-- Absolute convergence of `∑_n k_n(z) k_n(w)` for all `z, w ∈ ℂ`. -/
theorem airyCardinal_ker_summable_norm (z w : ℂ) :
    Summable (fun n : ℕ => ‖airyCardinal n z * airyCardinal n w‖) := by
  set R := max ‖z‖ ‖w‖
  obtain ⟨u, hu0, husum, hub⟩ := exists_airyCardinal_ball_majorant R
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) husum
  rw [norm_mul]
  have hz : z ∈ closedBall (0 : ℂ) R := by simp [R]
  have hw : w ∈ closedBall (0 : ℂ) R := by simp [R]
  calc ‖airyCardinal n z‖ * ‖airyCardinal n w‖
      ≤ u n * u n := mul_le_mul (hub n z hz) (hub n w hw) (norm_nonneg _) (hu0 n)
    _ = (u n) ^ 2 := (sq (u n)).symm

/-- Locally uniform convergence of `∑_{n < N} k_n(z) k_n(w)` to `K(z, w)` on `ℂ × ℂ`. -/
theorem airyCardinal_ker_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun (N : ℕ) (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, airyCardinal n p.1 * airyCardinal n p.2)
      (fun p => airyKerC p.1 p.2) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨u, hu0, husum, hub⟩ := exists_airyCardinal_ball_majorant R
  have hunif : TendstoUniformlyOn
      (fun (s : Finset ℕ) (p : ℂ × ℂ) => ∑ n ∈ s, airyCardinal n p.1 * airyCardinal n p.2)
      (fun p : ℂ × ℂ => ∑' n : ℕ, airyCardinal n p.1 * airyCardinal n p.2) atTop K := by
    refine tendstoUniformlyOn_tsum husum fun n p hp => ?_
    have hnorm := hR p hp
    rw [Prod.norm_def] at hnorm
    have hz : p.1 ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff]; exact (le_max_left _ _).trans hnorm
    have hw : p.2 ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff]; exact (le_max_right _ _).trans hnorm
    rw [norm_mul]
    calc ‖airyCardinal n p.1‖ * ‖airyCardinal n p.2‖
        ≤ u n * u n := mul_le_mul (hub n p.1 hz) (hub n p.2 hw) (norm_nonneg _) (hu0 n)
      _ = (u n) ^ 2 := (sq (u n)).symm
  have hcomp : TendstoUniformlyOn
      (fun (N : ℕ) (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, airyCardinal n p.1 * airyCardinal n p.2)
      (fun p : ℂ × ℂ => ∑' n : ℕ, airyCardinal n p.1 * airyCardinal n p.2) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    exact fun ε hε => tendsto_finset_range.eventually (hunif ε hε)
  refine hcomp.congr_right fun p _ => ?_
  exact (airyCardinal_ker_hasSum p.1 p.2).tsum_eq

/-! ### Cardinal series `q_c = ∑_n c_n k_n` for `c ∈ ℓ²` (complex and real) -/

/-- Complex `ℓ²` cardinal series `q_c(z) = ∑_n c_n k_n(z)`. -/
noncomputable def airyCardinalSeriesC (c : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) : ℂ :=
  ∑' n : ℕ, c n * airyCardinal n z

lemma memℓp_complex_ofReal (c : lp (fun _ : ℕ => ℝ) 2) :
    Memℓp (fun n : ℕ => (c n : ℂ)) 2 := by
  refine memℓp_gen ?_
  have hc : Summable (fun n : ℕ => ‖c n‖ ^ (2 : ℝ≥0∞).toReal) :=
    Memℓp.summable (by norm_num) (lp.memℓp c)
  simpa only [Complex.norm_real] using hc

/-- Real `ℓ²` embedding into complex `ℓ²`. -/
noncomputable def lpComplexOfReal (c : lp (fun _ : ℕ => ℝ) 2) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => (c n : ℂ), memℓp_complex_ofReal c⟩

@[simp]
lemma lpComplexOfReal_apply (c : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    lpComplexOfReal c n = (c n : ℂ) := rfl

lemma norm_lpComplexOfReal (c : lp (fun _ : ℕ => ℝ) 2) :
    ‖lpComplexOfReal c‖ = ‖c‖ := by
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) (lpComplexOfReal c)
  have h2 := lp.hasSum_norm (p := 2) (by norm_num) c
  simp only [ENNReal.toReal_ofNat, lpComplexOfReal_apply, Complex.norm_real] at h1 h2
  have hsq : ‖lpComplexOfReal c‖ ^ (2 : ℝ) = ‖c‖ ^ (2 : ℝ) := h1.unique h2
  simp only [Real.rpow_two] at hsq
  nlinarith only [hsq, norm_nonneg (lpComplexOfReal c), norm_nonneg c]

/-- Real `ℓ²` cardinal series `q_c(z) = ∑_n c_n k_n(z)` on `ℂ`. -/
noncomputable def airyCardinalSeries (c : lp (fun _ : ℕ => ℝ) 2) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (c n : ℂ) * airyCardinal n z

/-- Real-axis values of `q_c` for `c : lp (fun _ : ℕ => ℝ) 2`. -/
noncomputable def airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) (u : ℝ) : ℝ :=
  (airyCardinalSeries c (u : ℂ)).re

lemma airyCardinalSeries_eq_seriesC (c : lp (fun _ : ℕ => ℝ) 2) (z : ℂ) :
    airyCardinalSeries c z = airyCardinalSeriesC (lpComplexOfReal c) z := rfl

/-- Pointwise `HasSum` identifying `q_c(z)` with the entire representative of
`airyCardinalBasis.repr.symm c ∈ airyPW`. -/
theorem airyCardinalSeriesC_hasSum (c : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) :
    HasSum (fun n : ℕ => c n * airyCardinal n z)
      (airyPWFun ((airyCardinalBasis.repr.symm c : airyPW) : AiryL2) z) := by
  set F : airyPW := airyCardinalBasis.repr.symm c
  let G : airyPW := ⟨airyKerCL2 z, airyKerCL2_mem z⟩
  have h := airyCardinalBasis.hasSum_inner_mul_inner G F
  rw [coe_airyCardinalBasis] at h
  have hGF : inner ℂ G F = airyPWFun (F : AiryL2) z :=
    (airyPW_eval_inner F.2 z).symm
  rw [hGF] at h
  refine h.congr_fun fun n => ?_
  have h1 : inner ℂ G (airyCardinalPW n) = airyCardinal n z :=
    inner_airyKerCL2_airyCardinalL2 n z
  have h2 : inner ℂ (airyCardinalPW n) F = c n := by
    have hr : airyCardinalBasis.repr F n = c n := by
      simp [F]
    rw [HilbertBasis.repr_apply_apply, coe_airyCardinalBasis] at hr
    exact hr
  rw [h1, h2, mul_comm]

theorem airyCardinalSeriesC_eq_airyPWFun (c : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) :
    airyCardinalSeriesC c z =
      airyPWFun ((airyCardinalBasis.repr.symm c : airyPW) : AiryL2) z :=
  (airyCardinalSeriesC_hasSum c z).tsum_eq

theorem airyCardinalSeries_hasSum (c : lp (fun _ : ℕ => ℝ) 2) (z : ℂ) :
    HasSum (fun n : ℕ => (c n : ℂ) * airyCardinal n z) (airyCardinalSeries c z) := by
  rw [airyCardinalSeries_eq_seriesC, airyCardinalSeriesC_eq_airyPWFun]
  exact airyCardinalSeriesC_hasSum (lpComplexOfReal c) z

/-- Absolute summability of `∑_n c_n k_n(z)`. -/
theorem airyCardinalSeriesC_summable_norm (c : lp (fun _ : ℕ => ℂ) 2) (z : ℂ) :
    Summable (fun n : ℕ => ‖c n * airyCardinal n z‖) := by
  obtain ⟨u, hu0, husum, hub⟩ := exists_airyCardinal_ball_majorant ‖z‖
  have hcsum : Summable (fun n : ℕ => ‖c n‖ ^ 2) := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num) c).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((hcsum.add husum).mul_left (1 / 2 : ℝ))
  rw [norm_mul]
  have hz : z ∈ closedBall (0 : ℂ) ‖z‖ := by simp
  have hkn := hub n z hz
  have hprod : ‖c n‖ * ‖airyCardinal n z‖ ≤ ‖c n‖ * u n :=
    mul_le_mul_of_nonneg_left hkn (norm_nonneg _)
  nlinarith only [hprod, sq_nonneg (‖c n‖ - u n)]

/-- Locally uniform convergence of `∑_{n < N} c_n k_n(z)` to `q_c(z)` on `ℂ`. -/
theorem airyCardinalSeriesC_tendstoLocallyUniformly (c : lp (fun _ : ℕ => ℂ) 2) :
    TendstoLocallyUniformly
      (fun (N : ℕ) (z : ℂ) => ∑ n ∈ Finset.range N, c n * airyCardinal n z)
      (airyCardinalSeriesC c) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨u, hu0, husum, hub⟩ := exists_airyCardinal_ball_majorant R
  have hcsum : Summable (fun n : ℕ => ‖c n‖ ^ 2) := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num) c).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hunif : TendstoUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) => ∑ n ∈ s, c n * airyCardinal n z)
      (airyCardinalSeriesC c) atTop K := by
    refine tendstoUniformlyOn_tsum ((hcsum.add husum).mul_left (1 / 2 : ℝ)) fun n z hz => ?_
    have hzR : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (hR z hz)
    have hkn := hub n z hzR
    rw [norm_mul]
    have hprod : ‖c n‖ * ‖airyCardinal n z‖ ≤ ‖c n‖ * u n :=
      mul_le_mul_of_nonneg_left hkn (norm_nonneg _)
    nlinarith only [hprod, sq_nonneg (‖c n‖ - u n)]
  rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
  exact fun ε hε => tendsto_finset_range.eventually (hunif ε hε)

theorem airyCardinalSeries_tendstoLocallyUniformly (c : lp (fun _ : ℕ => ℝ) 2) :
    TendstoLocallyUniformly
      (fun (N : ℕ) (z : ℂ) => ∑ n ∈ Finset.range N, (c n : ℂ) * airyCardinal n z)
      (airyCardinalSeries c) atTop :=
  airyCardinalSeriesC_tendstoLocallyUniformly (lpComplexOfReal c)

/-- `q_c` is entire for every `c ∈ ℓ²`. -/
theorem differentiable_airyCardinalSeriesC (c : lp (fun _ : ℕ => ℂ) 2) :
    Differentiable ℂ (airyCardinalSeriesC c) := by
  have heq : airyCardinalSeriesC c =
      airyPWFun ((airyCardinalBasis.repr.symm c : airyPW) : AiryL2) :=
    funext (airyCardinalSeriesC_eq_airyPWFun c)
  rw [heq]
  exact differentiable_airyPWFun _

theorem differentiable_airyCardinalSeries (c : lp (fun _ : ℕ => ℝ) 2) :
    Differentiable ℂ (airyCardinalSeries c) :=
  differentiable_airyCardinalSeriesC (lpComplexOfReal c)

lemma airyCardinalSeries_conj (c : lp (fun _ : ℕ => ℝ) 2) (z : ℂ) :
    airyCardinalSeries c ((starRingEnd ℂ) z) = (starRingEnd ℂ) (airyCardinalSeries c z) := by
  have h1 := (airyCardinalSeries_hasSum c z).map (starRingEnd ℂ).toAddMonoidHom
    Complex.continuous_conj
  have h2 := airyCardinalSeries_hasSum c ((starRingEnd ℂ) z)
  have hcongr : (fun n : ℕ => (c n : ℂ) * airyCardinal n ((starRingEnd ℂ) z)) =
      fun n : ℕ => (starRingEnd ℂ) ((c n : ℂ) * airyCardinal n z) := by
    ext n
    rw [map_mul, Complex.conj_ofReal, airyCardinal_conj]
  rw [hcongr] at h2
  exact h2.unique h1

theorem airyCardinalSeries_ofReal_im (c : lp (fun _ : ℕ => ℝ) 2) (u : ℝ) :
    (airyCardinalSeries c (u : ℂ)).im = 0 := by
  have h := airyCardinalSeries_conj c (u : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma ofReal_airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) (u : ℝ) :
    (airyCardinalSeriesR c u : ℂ) = airyCardinalSeries c (u : ℂ) :=
  Complex.ext rfl (airyCardinalSeries_ofReal_im c u).symm

lemma continuous_airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) :
    Continuous (airyCardinalSeriesR c) :=
  Complex.continuous_re.comp ((differentiable_airyCardinalSeries c).continuous.comp Complex.continuous_ofReal)

theorem airyCardinalSeriesR_hasSum (c : lp (fun _ : ℕ => ℝ) 2) (u : ℝ) :
    HasSum (fun n : ℕ => c n * airyCardinalR n u) (airyCardinalSeriesR c u) := by
  have h := (airyCardinalSeries_hasSum c (u : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  refine h.congr_fun fun n => ?_
  dsimp only [Function.comp_apply]
  change c n * airyCardinalR n u = ((c n : ℂ) * airyCardinal n (u : ℂ)).re
  rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Node evaluation: `q_c(a_n) = c_n Ai'(a_n)` (complex `c`). -/
theorem airyCardinalSeriesC_airyZ (c : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    airyCardinalSeriesC c (airyZ n : ℂ) = c n * (airyAi' (airyZ n) : ℂ) := by
  have h := airyCardinalSeriesC_hasSum c (airyZ n : ℂ)
  rw [← airyCardinalSeriesC_eq_airyPWFun] at h
  have hsingle : HasSum (fun m : ℕ => c m * airyCardinal m (airyZ n : ℂ))
      (c n * (airyAi' (airyZ n) : ℂ)) := by
    refine hasSum_ite_eq n (c n * (airyAi' (airyZ n) : ℂ)) |>.congr_fun fun m => ?_
    rw [airyCardinal_airyZ]
    by_cases hm : m = n
    · subst hm; simp
    · simp [hm]
  exact h.unique hsingle

/-- Node evaluation: `q_c(a_n) = c_n Ai'(a_n)` (real `c`). -/
theorem airyCardinalSeries_airyZ (c : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    airyCardinalSeries c (airyZ n : ℂ) = ((c n * airyAi' (airyZ n) : ℝ) : ℂ) := by
  rw [airyCardinalSeries_eq_seriesC, airyCardinalSeriesC_airyZ, lpComplexOfReal_apply,
    Complex.ofReal_mul]

theorem airyCardinalSeriesR_airyZ (c : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    airyCardinalSeriesR c (airyZ n) = c n * airyAi' (airyZ n) := by
  unfold airyCardinalSeriesR
  rw [airyCardinalSeries_airyZ, Complex.ofReal_re]

/-- Parseval identity for complex `c ∈ ℓ²`: `∫ |q_c(u)|² du = ∑_n |c_n|² = ‖c‖²`. -/
theorem integrable_norm_sq_airyCardinalSeriesC (c : lp (fun _ : ℕ => ℂ) 2) :
    Integrable (fun u : ℝ => ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2) := by
  have heq : (fun u : ℝ => ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2) =
      fun u : ℝ => ‖airyPWFun ((airyCardinalBasis.repr.symm c : airyPW) : AiryL2) (u : ℂ)‖ ^ 2 := by
    ext u; rw [airyCardinalSeriesC_eq_airyPWFun]
  rw [heq]
  exact integrable_norm_sq_airyPWFun (airyCardinalBasis.repr.symm c).2

theorem integral_norm_sq_airyCardinalSeriesC (c : lp (fun _ : ℕ => ℂ) 2) :
    (∫ u : ℝ, ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2) = ‖c‖ ^ 2 := by
  set F : airyPW := airyCardinalBasis.repr.symm c
  have heq : (fun u : ℝ => ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2) =
      fun u : ℝ => ‖airyPWFun (F : AiryL2) (u : ℂ)‖ ^ 2 := by
    ext u; rw [airyCardinalSeriesC_eq_airyPWFun]
  rw [heq, integral_norm_sq_airyPWFun F.2]
  change ‖F‖ ^ 2 = ‖c‖ ^ 2
  rw [LinearIsometryEquiv.norm_map]

theorem hasSum_norm_sq_airyCardinalSeriesC (c : lp (fun _ : ℕ => ℂ) 2) :
    HasSum (fun n : ℕ => ‖c n‖ ^ 2) (∫ u : ℝ, ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2) := by
  rw [integral_norm_sq_airyCardinalSeriesC]
  have h := lp.hasSum_norm (p := 2) (by norm_num) c
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- Parseval identity for real `c ∈ ℓ²`: `∫ q_c(u)² du = ∑_n c_n² = ‖c‖²`. -/
theorem integrable_sq_airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) :
    Integrable (fun u : ℝ => airyCardinalSeriesR c u ^ 2) := by
  have h := integrable_norm_sq_airyCardinalSeriesC (lpComplexOfReal c)
  refine h.congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [← airyCardinalSeries_eq_seriesC, ← ofReal_airyCardinalSeriesR, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem integral_sq_airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) :
    (∫ u : ℝ, airyCardinalSeriesR c u ^ 2) = ‖c‖ ^ 2 := by
  have h := integral_norm_sq_airyCardinalSeriesC (lpComplexOfReal c)
  rw [norm_lpComplexOfReal] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [← airyCardinalSeries_eq_seriesC, ← ofReal_airyCardinalSeriesR, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem hasSum_sq_airyCardinalSeriesR (c : lp (fun _ : ℕ => ℝ) 2) :
    HasSum (fun n : ℕ => (c n) ^ 2) (∫ u : ℝ, airyCardinalSeriesR c u ^ 2) := by
  rw [integral_sq_airyCardinalSeriesR]
  have h := lp.hasSum_norm (p := 2) (by norm_num) c
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

/-- Products `q_{c₁} q_{c₂}` and squares `q_c²` lie in `AiryClassG` / `InAiryClass` via
`airyClassG_PW_mul`. -/
theorem airyCardinalSeriesC_mul_mem_airyClassG (c₁ c₂ : lp (fun _ : ℕ => ℂ) 2) :
    AiryClassG (fun z => airyCardinalSeriesC c₁ z * airyCardinalSeriesC c₂ z) := by
  have h := airyClassG_PW_mul (airyCardinalBasis.repr.symm c₁).2 (airyCardinalBasis.repr.symm c₂).2
  simpa only [airyCardinalSeriesC_eq_airyPWFun] using h

theorem airyCardinalSeries_mul_inAiryClass (c₁ c₂ : lp (fun _ : ℕ => ℝ) 2) :
    InAiryClass (fun z => airyCardinalSeries c₁ z * airyCardinalSeries c₂ z) := by
  refine inAiryClass_of_airyClassG
    (airyCardinalSeriesC_mul_mem_airyClassG (lpComplexOfReal c₁) (lpComplexOfReal c₂)) fun x => ?_
  rw [← ofReal_airyCardinalSeriesR, ← ofReal_airyCardinalSeriesR, ← Complex.ofReal_mul,
    Complex.ofReal_im]

theorem airyCardinalSeries_sq_inAiryClass (c : lp (fun _ : ℕ => ℝ) 2) :
    InAiryClass (fun z => airyCardinalSeries c z ^ 2) := by
  simpa only [sq] using airyCardinalSeries_mul_inAiryClass c c

/-! ### The `ℓ²` evaluation vector `(k_n(x))_n` -/

lemma memℓp_airyCardinalR_eval (x : ℝ) : Memℓp (fun n : ℕ => airyCardinalR n x) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have h := (airyCardinal_ker_hasSum (x : ℂ) (x : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  refine h.summable.congr fun n => ?_
  dsimp only [Function.comp_apply]
  change (airyCardinal n (x : ℂ) * airyCardinal n (x : ℂ)).re = airyCardinalR n x ^ 2
  rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re, sq]

/-- Evaluation vector `(k_n(x))_{n : ℕ} ∈ ℓ²(ℕ; ℝ)`. -/
noncomputable def airyEvalVec (x : ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun n => airyCardinalR n x, memℓp_airyCardinalR_eval x⟩

@[simp]
lemma airyEvalVec_apply (x : ℝ) (n : ℕ) : airyEvalVec x n = airyCardinalR n x := rfl

theorem norm_sq_airyEvalVec (x : ℝ) : ‖airyEvalVec x‖ ^ 2 = airyKer x x := by
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) (airyEvalVec x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, airyEvalVec_apply, Real.norm_eq_abs, sq_abs] at h1
  have h2 := (airyCardinal_ker_hasSum (x : ℂ) (x : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  rw [airyKerC_ofReal] at h2
  have h2' : HasSum (fun n : ℕ => airyCardinalR n x ^ 2) (airyKer x x) := by
    refine (by simpa using h2 : HasSum _ (airyKer x x)).congr_fun fun n => ?_
    dsimp only [Function.comp_apply]
    rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  exact h1.unique h2'

theorem inner_airyEvalVec (x : ℝ) (c : lp (fun _ : ℕ => ℝ) 2) :
    inner ℝ (airyEvalVec x) c = airyCardinalSeriesR c x := by
  have h1 := lp.hasSum_inner (𝕜 := ℝ) (airyEvalVec x) c
  have h2 := airyCardinalSeriesR_hasSum c x
  refine (h1.congr_fun fun n => ?_).unique h2
  simp [airyEvalVec_apply, mul_comm]

theorem norm_sub_airyEvalVec_sq (x y : ℝ) :
    ‖airyEvalVec x - airyEvalVec y‖ ^ 2 = airyKer x x - 2 * airyKer x y + airyKer y y := by
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) (airyEvalVec x - airyEvalVec y)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply,
    airyEvalVec_apply, Real.norm_eq_abs, sq_abs] at h1
  have hxx := (airyCardinal_ker_hasSum (x : ℂ) (x : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  have hxy := (airyCardinal_ker_hasSum (x : ℂ) (y : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  have hyy := (airyCardinal_ker_hasSum (y : ℂ) (y : ℂ)).map Complex.reCLM.toAddMonoidHom
    Complex.continuous_re
  rw [airyKerC_ofReal] at hxx hxy hyy
  have hxx' : HasSum (fun n : ℕ => airyCardinalR n x ^ 2) (airyKer x x) := by
    refine (by simpa using hxx : HasSum _ (airyKer x x)).congr_fun fun n => ?_
    dsimp only [Function.comp_apply]
    rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have hxy' : HasSum (fun n : ℕ => airyCardinalR n x * airyCardinalR n y) (airyKer x y) := by
    refine (by simpa using hxy : HasSum _ (airyKer x y)).congr_fun fun n => ?_
    dsimp only [Function.comp_apply]
    rw [← ofReal_airyCardinalR, ← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hyy' : HasSum (fun n : ℕ => airyCardinalR n y ^ 2) (airyKer y y) := by
    refine (by simpa using hyy : HasSum _ (airyKer y y)).congr_fun fun n => ?_
    dsimp only [Function.comp_apply]
    rw [← ofReal_airyCardinalR, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have hcomb := (hxx'.sub (hxy'.mul_left 2)).add hyy'
  have hcongr : (fun n : ℕ => airyCardinalR n x ^ 2 -
      2 * (airyCardinalR n x * airyCardinalR n y) + airyCardinalR n y ^ 2) =
      fun n : ℕ => (airyCardinalR n x - airyCardinalR n y) ^ 2 := by
    ext n; ring
  rw [hcongr] at hcomb
  exact h1.unique hcomb

/-! ### Headline statement of Lemma `lem:al-kernel` -/

/-- **Lemma `lem:al-kernel` (The Airy cardinal system, `ce_airy_lp_proofs.tex`).**
1. Each `k_n = Ai / (u - a_{n+1})` (`airyCardinal n`) is entire, square integrable on `ℝ`,
   excluded from `𝒢`, with pairwise products `k_m k_n ∈ 𝒢`, orthonormal in `L²(ℝ)`, and satisfies
   `k_m(a_{n+1}) = δ_{mn} Ai'(a_{n+1})`.
2. For real `c ∈ ℓ²`, `q_c = ∑_n c_n k_n` (`airyCardinalSeries c`) converges locally uniformly on
   `ℂ`, is entire, lies in `√𝒢` (`q_c² ∈ 𝒢`), and satisfies `q_c(a_{n+1}) = c_n Ai'(a_{n+1})` and
   `∫ q_c² = ∑_n c_n²` (for complex `c ∈ ℓ²`, `∫ |q_c|² = ∑_n |c_n|²`).
3. `(eq:al-kernel)`: `∑_n k_n(z) k_n(w) = K(z, w)` (`airyKerC z w`) for all `z, w ∈ ℂ`, with
   absolute convergence locally uniformly on `ℂ × ℂ`. -/
theorem lem_al_kernel :
    (∀ n : ℕ, Differentiable ℂ (airyCardinal n) ∧
      MemLp (airyCardinalR n) 2 volume ∧
      ¬ InAiryClass (airyCardinal n)) ∧
    (∀ m n : ℕ, InAiryClass (fun z => airyCardinal m z * airyCardinal n z) ∧
      (∫ u : ℝ, airyCardinalR m u * airyCardinalR n u) = (if m = n then 1 else 0) ∧
      airyCardinal m (airyZ n : ℂ) = (if m = n then (airyAi' (airyZ n) : ℂ) else 0)) ∧
    (∀ c : lp (fun _ : ℕ => ℝ) 2,
      TendstoLocallyUniformly
        (fun (N : ℕ) (z : ℂ) => ∑ n ∈ Finset.range N, (c n : ℂ) * airyCardinal n z)
        (airyCardinalSeries c) atTop ∧
      Differentiable ℂ (airyCardinalSeries c) ∧
      InAiryClass (fun z => airyCardinalSeries c z ^ 2) ∧
      (∀ n : ℕ, airyCardinalSeriesR c (airyZ n) = c n * airyAi' (airyZ n)) ∧
      HasSum (fun n : ℕ => (c n) ^ 2) (∫ u : ℝ, airyCardinalSeriesR c u ^ 2)) ∧
    (∀ c : lp (fun _ : ℕ => ℂ) 2,
      HasSum (fun n : ℕ => ‖c n‖ ^ 2) (∫ u : ℝ, ‖airyCardinalSeriesC c (u : ℂ)‖ ^ 2)) ∧
    (∀ z w : ℂ, Summable (fun n : ℕ => ‖airyCardinal n z * airyCardinal n w‖) ∧
      HasSum (fun n : ℕ => airyCardinal n z * airyCardinal n w) (airyKerC z w)) ∧
    TendstoLocallyUniformly
      (fun (N : ℕ) (p : ℂ × ℂ) => ∑ n ∈ Finset.range N, airyCardinal n p.1 * airyCardinal n p.2)
      (fun p => airyKerC p.1 p.2) atTop :=
  ⟨fun n => ⟨differentiable_airyCardinal n, memLp_airyCardinalR n, not_inAiryClass_airyCardinal n⟩,
   fun m n => ⟨airyCardinal_mul_inAiryClass m n, integral_airyCardinalR_mul m n,
     airyCardinal_airyZ m n⟩,
   fun c => ⟨airyCardinalSeries_tendstoLocallyUniformly c, differentiable_airyCardinalSeries c,
     airyCardinalSeries_sq_inAiryClass c, airyCardinalSeriesR_airyZ c,
     hasSum_sq_airyCardinalSeriesR c⟩,
   hasSum_norm_sq_airyCardinalSeriesC,
   fun z w => ⟨airyCardinal_ker_summable_norm z w, airyCardinal_ker_hasSum z w⟩,
   airyCardinal_ker_tendstoLocallyUniformly⟩

/-- info: 'FormalResearch.SignUncertainty.airyCardinalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyCardinalBasis

/-- info: 'FormalResearch.SignUncertainty.airyCardinal_ker_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyCardinal_ker_hasSum

/-- info: 'FormalResearch.SignUncertainty.airyCardinalSeries_sq_inAiryClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airyCardinalSeries_sq_inAiryClass

/-- info: 'FormalResearch.SignUncertainty.lem_al_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_kernel

end FormalResearch.SignUncertainty

module

public import FormalResearch.Special.AiryPwsMain

/-!
# Consequences of the `H^∞` bound: decay transfer and `PW·PW ⊂ G`

* `pl_halfPlane_decay`: a function `F` holomorphic on `Im ζ > 0`, continuous on `Im ζ ≥ 0`, polynomially bounded there, with
  boundary decay `|F(ξ)| (1+|ξ|)^m ≤ D` (`m ≥ 0` real) satisfies `|F(ζ)| (1+|ζ|)^m ≤ 2^{m/2} D` on all of `Im ζ ≥ 0`
  (apply `pl_halfPlane` to `F(ζ)(ζ+i)^m`).  This is the "Phragmén–Lindelöf as in Lemma U.2" step of CE_O1_ROUTE O.11n,
  where `m = 5/2`.
* `airyClassG_PW_mul`: for `F₁, F₂ ∈ PW` (Airy Paley–Wiener space, `AiryTransform*`) with entire representatives
  `H_j = airyPWFun F_j`, the product `H₁ H₂` lies in `G` (`‖H₁H₂‖ ≤ 23‖F₁‖‖F₂‖(1+|z|)e(z)`, `H₁H₂ ∈ L¹` by Cauchy–Schwarz):
  this is the formalised part of `LOCAL_AIRY_MODEL` Lemma Q2, third bullet (with the exponent `(1+|z|)` in place of `(1+|z|)^{1/2}`).
* `airyFtilde_PW_sq_le`, `airyFtilde_PW_mul_le`: the **uniform `H^∞` bound** of CE_O1_ROUTE O.11n for `P = H²`:
  `|F̃_{H²}(ζ)| ≤ k ‖F‖₂²` for `Im ζ ≥ 0`; for products `|F̃_{H₁H₂}| ≤ k (‖F₁‖² + ‖F₂‖²)/2`
  (the sharp `k‖F₁‖‖F₂‖` follows by scaling `H₁ ↦ tH₁`, `H₂ ↦ H₂/t`, not done here).

**Not formalised:** the sharp exponent `(1+|z|)^{1/2}` in `G`, and the scaled sharp product bound.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real ComplexInnerProductSpace

namespace FormalResearch.Special

/-- `Phragmén–Lindelöf` with a boundary decay rate `m ≥ 0` (real). -/
theorem pl_halfPlane_decay {F : ℂ → ℂ} {A D m : ℝ} {M : ℕ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hd : DiffContOnCl ℂ F {ζ : ℂ | 0 < ζ.im})
    (hpoly : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖F ζ‖ ≤ A * (1 + ‖ζ‖) ^ M)
    (hbd : ∀ ξ : ℝ, ‖F (ξ : ℂ)‖ * (1 + |ξ|) ^ m ≤ D) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖F ζ‖ * (1 + ‖ζ‖) ^ m ≤ (2 : ℝ) ^ (m / 2) * D := by
  set g : ℂ → ℂ := fun ζ => F ζ * (ζ + I) ^ (m : ℂ) with hg
  have hmem : ∀ ζ : ℂ, 0 ≤ ζ.im → ζ + I ∈ slitPlane := fun ζ hζ => by
    rw [mem_slitPlane_iff]; right; simp; linarith
  have hnorm : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖(ζ + I) ^ (m : ℂ)‖ = ‖ζ + I‖ ^ m := fun ζ hζ => by
    have hne : ζ + I ≠ 0 := slitPlane_ne_zero (hmem ζ hζ)
    rw [Complex.norm_cpow_of_ne_zero hne]
    simp
  have hdc : DiffContOnCl ℂ g {ζ : ℂ | 0 < ζ.im} := by
    have hdiffp : ∀ ζ : ℂ, 0 ≤ ζ.im → DifferentiableAt ℂ (fun ζ : ℂ => (ζ + I) ^ (m : ℂ)) ζ :=
      fun ζ hζ => (differentiableAt_id.add_const I).cpow_const (hmem ζ hζ)
    refine ⟨hd.differentiableOn.mul (fun ζ hζ => (hdiffp ζ (le_of_lt hζ)).differentiableWithinAt), ?_⟩
    rw [closure_setOfPred_lt_im]
    have hc1 : ContinuousOn F {ζ : ℂ | 0 ≤ ζ.im} := by
      simpa [closure_setOfPred_lt_im] using hd.continuousOn
    have hc2 : ContinuousOn (fun ζ : ℂ => (ζ + I) ^ (m : ℂ)) {ζ : ℂ | 0 ≤ ζ.im} :=
      fun ζ hζ => (hdiffp ζ hζ).continuousAt.continuousWithinAt
    exact hc1.mul hc2
  have hbound : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖g ζ‖ ≤ A * (1 + ‖ζ‖) ^ (M + ⌈m⌉₊) := by
    intro ζ hζ
    rw [hg]; simp only [norm_mul]
    rw [hnorm ζ hζ]
    have h1 : ‖ζ + I‖ ≤ 1 + ‖ζ‖ := by
      calc ‖ζ + I‖ ≤ ‖ζ‖ + ‖I‖ := norm_add_le _ _
        _ = 1 + ‖ζ‖ := by simp [add_comm]
    have h2 : ‖ζ + I‖ ^ m ≤ (1 + ‖ζ‖) ^ m := Real.rpow_le_rpow (norm_nonneg _) h1 hm
    have hr1 : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
    have h3 : (1 + ‖ζ‖) ^ m ≤ (1 + ‖ζ‖) ^ (⌈m⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (Nat.le_ceil m)
    rw [Real.rpow_natCast] at h3
    have h4 := hpoly ζ hζ
    calc ‖F ζ‖ * ‖ζ + I‖ ^ m ≤ (A * (1 + ‖ζ‖) ^ M) * (1 + ‖ζ‖) ^ ⌈m⌉₊ :=
          mul_le_mul h4 (h2.trans h3) (by positivity) (by positivity)
      _ = _ := by ring
  have hbdr : ∀ ξ : ℝ, ‖g (ξ : ℂ)‖ ≤ D := by
    intro ξ
    rw [hg]; simp only [norm_mul]
    rw [hnorm (ξ : ℂ) (by simp)]
    have h1 : ‖(ξ : ℂ) + I‖ ≤ 1 + |ξ| := by
      calc ‖(ξ : ℂ) + I‖ ≤ ‖(ξ : ℂ)‖ + ‖I‖ := norm_add_le _ _
        _ = 1 + |ξ| := by simp [add_comm]
    have h2 : ‖(ξ : ℂ) + I‖ ^ m ≤ (1 + |ξ|) ^ m := Real.rpow_le_rpow (norm_nonneg _) h1 hm
    exact (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (hbd ξ)
  have hD : ‖g ζ‖ ≤ D := pl_halfPlane hA hdc hbound hbdr hζ
  -- lower bound of `‖ζ + I‖`
  have hlow : 1 + ‖ζ‖ ≤ Real.sqrt 2 * ‖ζ + I‖ := by
    have h0 := norm_nonneg ζ
    have hsq : ‖ζ + I‖ ^ 2 = ζ.re ^ 2 + (ζ.im + 1) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hz2 : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h5 : (1 + ‖ζ‖) ^ 2 ≤ 2 * ‖ζ + I‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (‖ζ‖ - 1)]
    have h6 : 0 ≤ Real.sqrt 2 * ‖ζ + I‖ := by positivity
    have h7 : (Real.sqrt 2 * ‖ζ + I‖) ^ 2 = 2 * ‖ζ + I‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact le_of_sq_le_sq (by rw [h7]; exact h5) h6
  have hr1 : (0 : ℝ) ≤ 1 + ‖ζ‖ := by positivity
  have hpow : (1 + ‖ζ‖) ^ m ≤ (Real.sqrt 2 * ‖ζ + I‖) ^ m := Real.rpow_le_rpow hr1 hlow hm
  have hs2 : (Real.sqrt 2) ^ m = (2 : ℝ) ^ (m / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _), hs2] at hpow
  have hD' : ‖F ζ‖ * ‖ζ + I‖ ^ m ≤ D := by
    have := hD
    rw [hg] at this; simp only [norm_mul] at this
    rwa [hnorm ζ hζ] at this
  calc ‖F ζ‖ * (1 + ‖ζ‖) ^ m ≤ ‖F ζ‖ * ((2 : ℝ) ^ (m / 2) * ‖ζ + I‖ ^ m) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = (2 : ℝ) ^ (m / 2) * (‖F ζ‖ * ‖ζ + I‖ ^ m) := by ring
    _ ≤ (2 : ℝ) ^ (m / 2) * D := mul_le_mul_of_nonneg_left hD' (by positivity)

/-! ### `PW · PW ⊂ G` and the uniform `H^∞` bound for `P = H²` -/

lemma airy_norm_sq_eq_integral (F : AiryL2) : ‖F‖ ^ 2 = ∫ u : ℝ, ‖F u‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
  have h1 : inner ℂ F F = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F]; simp
  have h2 : ∀ a : ℝ, inner ℂ (F a) (F a) = (((‖F a‖ ^ 2 : ℝ)) : ℂ) := fun a => by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (F a)]; simp
  simp_rw [h2] at h
  rw [integral_complex_ofReal, h1] at h
  exact_mod_cast h

lemma integral_norm_sq_airyPWFun {F : AiryL2} (hF : F ∈ airyPW) :
    ∫ u : ℝ, ‖airyPWFun F (u : ℂ)‖ ^ 2 = ‖F‖ ^ 2 := by
  rw [airy_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [airyPWFun_ae hF] with u hu
  rw [hu]

lemma integrable_norm_sq_airyPWFun {F : AiryL2} (hF : F ∈ airyPW) :
    Integrable (fun u : ℝ => ‖airyPWFun F (u : ℂ)‖ ^ 2) := by
  have h : Integrable (fun u : ℝ => ‖F u‖ ^ 2) := integrable_norm_sq_lp F
  refine h.congr ?_
  filter_upwards [airyPWFun_ae hF] with u hu
  rw [hu]

lemma continuous_airyPWFun_ofReal (F : AiryL2) : Continuous fun u : ℝ => airyPWFun F (u : ℂ) :=
  (differentiable_airyPWFun F).continuous.comp Complex.continuous_ofReal

/-- **`PW · PW ⊂ G`**: the product of two elements of the Airy Paley–Wiener space (entire representatives) is in `G`. -/
theorem airyClassG_PW_mul {F₁ F₂ : AiryL2} (h₁ : F₁ ∈ airyPW) (h₂ : F₂ ∈ airyPW) :
    AiryClassG (fun z => airyPWFun F₁ z * airyPWFun F₂ z) := by
  refine ⟨(differentiable_airyPWFun F₁).mul (differentiable_airyPWFun F₂), ?_, ?_⟩
  · have hb : Integrable (fun u : ℝ => (1 / 2 : ℝ) * (‖airyPWFun F₁ (u : ℂ)‖ ^ 2 + ‖airyPWFun F₂ (u : ℂ)‖ ^ 2)) :=
      ((integrable_norm_sq_airyPWFun h₁).add (integrable_norm_sq_airyPWFun h₂)).const_mul _
    refine hb.mono' ?_ (Eventually.of_forall fun u => ?_)
    · exact ((continuous_airyPWFun_ofReal F₁).mul (continuous_airyPWFun_ofReal F₂)).aestronglyMeasurable
    · rw [norm_mul]
      nlinarith [sq_nonneg (‖airyPWFun F₁ (u : ℂ)‖ - ‖airyPWFun F₂ (u : ℂ)‖), norm_nonneg (airyPWFun F₁ (u : ℂ)),
        norm_nonneg (airyPWFun F₂ (u : ℂ))]
  · refine ⟨23 * ‖F₁‖ * ‖F₂‖, 1, by positivity, fun z => ?_⟩
    have a1 := norm_airyPWFun_sq_le F₁ z
    have a2 := norm_airyPWFun_sq_le F₂ z
    have he := airyEnv_pos z
    have hX : 0 ≤ 23 * ‖F₁‖ * ‖F₂‖ * (1 + ‖z‖) ^ 1 * airyEnv z := by positivity
    have hsq : ‖airyPWFun F₁ z * airyPWFun F₂ z‖ ^ 2 ≤ (23 * ‖F₁‖ * ‖F₂‖ * (1 + ‖z‖) ^ 1 * airyEnv z) ^ 2 := by
      rw [norm_mul, mul_pow]
      calc ‖airyPWFun F₁ z‖ ^ 2 * ‖airyPWFun F₂ z‖ ^ 2
          ≤ (23 * ‖F₁‖ ^ 2 * (1 + ‖z‖) * airyEnv z) * (23 * ‖F₂‖ ^ 2 * (1 + ‖z‖) * airyEnv z) :=
            mul_le_mul a1 a2 (sq_nonneg _) (by positivity)
        _ = _ := by ring
    exact abs_le_of_sq_le_sq' hsq hX |>.2 |> fun h => by simpa using h

/-- **Uniform `H^∞` bound for `P = H²`** (CE_O1_ROUTE O.11n): for `F ∈ PW` with entire representative `H`,
`|F̃_{H²}(ζ)| ≤ k ‖F‖₂²` on `Im ζ ≥ 0`. -/
theorem airyFtilde_PW_sq_le {F : AiryL2} (hF : F ∈ airyPW) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖airyFtilde (fun z => airyPWFun F z * airyPWFun F z) ζ‖ ≤ airyPhiK * ‖F‖ ^ 2 := by
  have h := airyFtilde_norm_le (airyClassG_PW_mul hF hF) hζ
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [← integral_norm_sq_airyPWFun hF]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, sq]

/-- Polarised form: `|F̃_{H₁H₂}(ζ)| ≤ k (‖F₁‖² + ‖F₂‖²)/2`. -/
theorem airyFtilde_PW_mul_le {F₁ F₂ : AiryL2} (h₁ : F₁ ∈ airyPW) (h₂ : F₂ ∈ airyPW) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖airyFtilde (fun z => airyPWFun F₁ z * airyPWFun F₂ z) ζ‖ ≤ airyPhiK * ((‖F₁‖ ^ 2 + ‖F₂‖ ^ 2) / 2) := by
  have h := airyFtilde_norm_le (airyClassG_PW_mul h₁ h₂) hζ
  refine h.trans (mul_le_mul_of_nonneg_left ?_ airyPhiK_pos.le)
  have hi : Integrable (fun u : ℝ => (1 / 2 : ℝ) * (‖airyPWFun F₁ (u : ℂ)‖ ^ 2 + ‖airyPWFun F₂ (u : ℂ)‖ ^ 2)) :=
    ((integrable_norm_sq_airyPWFun h₁).add (integrable_norm_sq_airyPWFun h₂)).const_mul _
  calc ∫ u : ℝ, ‖airyPWFun F₁ (u : ℂ) * airyPWFun F₂ (u : ℂ)‖
      ≤ ∫ u : ℝ, (1 / 2 : ℝ) * (‖airyPWFun F₁ (u : ℂ)‖ ^ 2 + ‖airyPWFun F₂ (u : ℂ)‖ ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hi
          (Eventually.of_forall fun u => ?_)
        simp only [norm_mul]
        nlinarith [sq_nonneg (‖airyPWFun F₁ (u : ℂ)‖ - ‖airyPWFun F₂ (u : ℂ)‖)]
    _ = (‖F₁‖ ^ 2 + ‖F₂‖ ^ 2) / 2 := by
        rw [integral_const_mul, integral_add (integrable_norm_sq_airyPWFun h₁) (integrable_norm_sq_airyPWFun h₂),
          integral_norm_sq_airyPWFun h₁, integral_norm_sq_airyPWFun h₂]
        ring

/-- info: 'FormalResearch.Special.pl_halfPlane_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.pl_halfPlane_decay

/-- info: 'FormalResearch.Special.airyFtilde_PW_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFtilde_PW_sq_le

/-- info: 'FormalResearch.Special.airyClassG_PW_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClassG_PW_mul

/-- info: 'FormalResearch.Special.airyFtilde_PW_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFtilde_PW_mul_le

end FormalResearch.Special

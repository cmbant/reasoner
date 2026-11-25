module

public import FormalResearch.SignUncertainty.CtOuterBlaschke

/-!
# `ct:outer` (1): the outer function `G_ε`, analyticity, parity and boundary modulus

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Proposition `ct:outer` (1) with eq. `ct:Gdef`
and `ct:Gmod`.  **Proved.**

On `S = {0 < Re ζ < 1}` put `h(ζ) = ∫ u_r(t)/sin(π(ζ - it)) dt` (`outerH`), `G_- = ζ^{1/2}(1-ζ)^{1/2}e^{h}` and
`G_+ = b_{1/2} G_-` (`outerG`, `ε = ±1`).  `outerGbar` is the same expression with the boundary extension `outerHbar`
of `h`; it is the continuous extension of `G_ε` to the closed strip.

* `outerG_differentiableOn`: `G_ε` is holomorphic on `S`;
* `outerGbar_continuousOn`: `G_ε` is continuous on `closure S = closedStrip`, with `outerGbar = outerG` on `S`;
* `outerGbar_conj`: real symmetry; `outerGbar_oneSub`: the parity `G_ε(1 - ζ) = -ε G_ε(ζ)`;
* `norm_outerGbar_left`, `norm_outerGbar_right`: the boundary modulus
  `|G_ε(iτ)| = |G_ε(1 + iτ)| = √((6/π²) m'(|τ|)/√(1+τ²))` (`ct:Gmod`);
* `outerGbar_bound`: `|G_ε(σ + iτ)| ≤ C (1 + |τ|)⁻¹` on `closedStrip`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `G_-` built from a function `h`: `ζ^{1/2} (1 - ζ)^{1/2} e^{h(ζ)}` (principal square roots). -/
noncomputable def outerGm (h : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  ζ ^ (1 / 2 : ℂ) * (1 - ζ) ^ (1 / 2 : ℂ) * Complex.exp (h ζ)

/-- The outer function `G_ε` on `S`: `G_- = ζ^{1/2}(1-ζ)^{1/2}e^h`, `G_+ = b_{1/2} G_-` (`ε = ±1`). -/
noncomputable def outerG (ε : ℝ) (ζ : ℂ) : ℂ := (if ε = 1 then bHalf ζ else 1) * outerGm outerH ζ

/-- The continuous extension of `G_ε` to the closed strip. -/
noncomputable def outerGbar (ε : ℝ) (ζ : ℂ) : ℂ := (if ε = 1 then bHalf ζ else 1) * outerGm outerHbar ζ

lemma arg_ne_pi_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) : z.arg ≠ π := by
  intro h'
  rw [Complex.arg_eq_pi_iff] at h'
  linarith [h'.1]

lemma conj_cpow_half {z : ℂ} (h : 0 ≤ z.re) :
    (starRingEnd ℂ z) ^ (1 / 2 : ℂ) = starRingEnd ℂ (z ^ (1 / 2 : ℂ)) := by
  rw [Complex.conj_cpow z _ (arg_ne_pi_of_re_nonneg h)]
  congr 2
  simp [map_ofNat]

lemma norm_cpow_half (z : ℂ) : ‖z ^ (1 / 2 : ℂ)‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
  have := Complex.norm_cpow_real z (1 / 2 : ℝ)
  simpa using this

lemma outerGm_oneSub {h : ℂ → ℂ} (hs : ∀ ζ, h (1 - ζ) = h ζ) (ζ : ℂ) :
    outerGm h (1 - ζ) = outerGm h ζ := by
  unfold outerGm
  rw [hs, sub_sub_cancel]
  ring

lemma outerGm_conj {h : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ closedStrip) (hc : h (starRingEnd ℂ ζ) = starRingEnd ℂ (h ζ)) :
    outerGm h (starRingEnd ℂ ζ) = starRingEnd ℂ (outerGm h ζ) := by
  unfold outerGm
  have h1 : 1 - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) := by simp
  have h2 : 0 ≤ (1 - ζ).re := by simp; exact hζ.2
  rw [h1, conj_cpow_half hζ.1, conj_cpow_half h2, hc, map_mul, map_mul, Complex.exp_conj]

lemma outerH_oneSub_all (ζ : ℂ) : outerH (1 - ζ) = outerH ζ := outerH_one_sub ζ

lemma outerHbar_oneSub_closed {ζ : ℂ} (hζ : ζ ∈ closedStrip) : outerHbar (1 - ζ) = outerHbar ζ :=
  outerHbar_oneSub hζ

/-- **`ct:outer` (1), parity.** `G_ε(1 - ζ) = -ε G_ε(ζ)` on the closed strip. -/
theorem outerGbar_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    outerGbar ε (1 - ζ) = -ε * outerGbar ε ζ := by
  have hm : (1 - ζ) ∈ closedStrip := ⟨by simp; exact hζ.2, by simp; exact hζ.1⟩
  -- `outerGm outerHbar` is symmetric on the closed strip
  have key : outerGm outerHbar (1 - ζ) = outerGm outerHbar ζ := by
    unfold outerGm
    rw [outerHbar_oneSub hζ, sub_sub_cancel]
    ring
  unfold outerGbar
  rcases hε with rfl | rfl
  · simp [bHalf_oneSub, key]
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp [hne, key]

/-- **`ct:outer` (1), real symmetry.** -/
theorem outerGbar_conj {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    outerGbar ε (starRingEnd ℂ ζ) = starRingEnd ℂ (outerGbar ε ζ) := by
  have hc := outerHbar_conj hζ
  have key := outerGm_conj (h := outerHbar) hζ hc
  unfold outerGbar
  rcases hε with rfl | rfl
  · simp [bHalf_conj, key]
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp [hne, key]

lemma mem_slitPlane_of_mem_strip {ζ : ℂ} (hζ : ζ ∈ strip) : ζ ∈ slitPlane := Or.inl hζ.1

lemma one_sub_mem_slitPlane_of_mem_strip {ζ : ℂ} (hζ : ζ ∈ strip) : (1 - ζ) ∈ slitPlane :=
  Or.inl (by simp; exact hζ.2)

lemma outerGm_differentiableOn : DifferentiableOn ℂ (outerGm outerH) strip := by
  intro ζ hζ
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ (1 / 2 : ℂ)) ζ :=
    differentiableAt_id.cpow_const (mem_slitPlane_of_mem_strip hζ)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) ζ :=
    (differentiableAt_const _ |>.sub differentiableAt_id).cpow_const (one_sub_mem_slitPlane_of_mem_strip hζ)
  have h3 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (outerH z)) ζ :=
    (differentiableOn_outerH.differentiableAt (isOpen_strip.mem_nhds hζ)).cexp
  exact (h1.mul h2 |>.mul h3).differentiableWithinAt

/-- **`ct:outer` (1), holomorphy.** `G_ε` is holomorphic on `S`. -/
theorem outerG_differentiableOn (ε : ℝ) : DifferentiableOn ℂ (outerG ε) strip := by
  unfold outerG
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]; exact differentiableOn_bHalf.mul outerGm_differentiableOn
  · simp only [h, ↓reduceIte, one_mul]; exact outerGm_differentiableOn

lemma outerGm_continuousOn : ContinuousOn (outerGm outerHbar) closedStrip := by
  intro ζ hζ
  have h1 : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ζ :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hζ.1) (by norm_num)
  have h2 : ContinuousAt (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) ζ := by
    have := Complex.continuousAt_cpow_const_of_re_pos (z := 1 - ζ) (w := 1 / 2) (Or.inl (by simp; exact hζ.2))
      (by norm_num)
    exact this.comp (by fun_prop : Continuous fun z : ℂ => 1 - z).continuousAt
  have h3 : ContinuousWithinAt (fun z : ℂ => Complex.exp (outerHbar z)) closedStrip ζ :=
    (continuousOn_outerHbar ζ hζ).cexp
  exact ((h1.mul h2).continuousWithinAt).mul h3

/-- **`ct:outer` (1), continuity on the closed strip.** -/
theorem outerGbar_continuousOn (ε : ℝ) : ContinuousOn (outerGbar ε) closedStrip := by
  unfold outerGbar
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]; exact continuousOn_bHalf.mul outerGm_continuousOn
  · simp only [h, ↓reduceIte, one_mul]; exact outerGm_continuousOn

theorem outerGbar_eq_outerG (ε : ℝ) {ζ : ℂ} (hζ : ζ ∈ strip) : outerGbar ε ζ = outerG ε ζ := by
  unfold outerGbar outerG outerGm
  rw [outerHbar_of_mem_strip hζ]

lemma norm_I_mul_real (τ : ℝ) : ‖Complex.I * (τ : ℂ)‖ = |τ| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_one_sub_I_mul (τ : ℝ) : ‖1 - Complex.I * (τ : ℂ)‖ = Real.sqrt (1 + τ ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp; ring

lemma uR_abs (τ : ℝ) : uR |τ| = uR τ := by
  rcases abs_cases τ with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, uR_neg]

/-- **`ct:outer` (1), boundary modulus on the left edge** (`ct:Gmod`). -/
theorem norm_outerGm_left (τ : ℝ) :
    ‖outerGm outerHbar (Complex.I * (τ : ℂ))‖ =
      Real.sqrt (6 / π ^ 2 * mPrime |τ| / Real.sqrt (1 + τ ^ 2)) := by
  unfold outerGm
  rw [norm_mul, norm_mul, norm_cpow_half, norm_cpow_half, norm_I_mul_real, norm_one_sub_I_mul,
    Complex.norm_exp, re_outerHbar_left]
  by_cases hτ : τ = 0
  · subst hτ
    simp [mPrime]
  · have ha : 0 < |τ| := abs_pos.mpr hτ
    set a : ℝ := |τ| with hadef
    have hs : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (1 + τ ^ 2) ^ 2 = 1 + a ^ 2 := by
      rw [Real.sq_sqrt (by positivity), hadef, sq_abs]
    have hF := Freal_pos ha.ne'
    have hexp : Real.exp (uR τ) = Real.sqrt (Freal a) := by
      rw [← uR_abs, ← hadef, uR_eq ha.ne', Real.sqrt_eq_rpow, Real.rpow_def_of_pos hF]
      congr 1; ring
    rw [hexp, ← Real.sqrt_eq_rpow a]
    have h1 : Real.sqrt (1 + τ ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (Real.sqrt (1 + τ ^ 2)) := by
      rw [Real.sqrt_eq_rpow (Real.sqrt (1 + τ ^ 2))]
    rw [h1, ← Real.sqrt_mul ha.le, ← Real.sqrt_mul (by positivity)]
    congr 1
    unfold Freal
    have ha1 : (0 : ℝ) < 1 + a ^ 2 := by positivity
    field_simp
    rw [hs2]
    ring

lemma norm_outerGbar_eq_Gm {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : ζ.re = 0 ∨ ζ.re = 1) :
    ‖outerGbar ε ζ‖ = ‖outerGm outerHbar ζ‖ := by
  unfold outerGbar
  rcases hε with rfl | rfl
  · simp [norm_bHalf_edge hζ]
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp [hne]

/-- **`ct:outer` (1), boundary modulus (`ct:Gmod`), left edge.** -/
theorem norm_outerGbar_left {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (τ : ℝ) :
    ‖outerGbar ε (Complex.I * (τ : ℂ))‖ = Real.sqrt (6 / π ^ 2 * mPrime |τ| / Real.sqrt (1 + τ ^ 2)) := by
  rw [norm_outerGbar_eq_Gm hε (Or.inl (by simp)), norm_outerGm_left]

/-- **`ct:outer` (1), boundary modulus (`ct:Gmod`), right edge.** -/
theorem norm_outerGbar_right {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (τ : ℝ) :
    ‖outerGbar ε (1 + Complex.I * (τ : ℂ))‖ = Real.sqrt (6 / π ^ 2 * mPrime |τ| / Real.sqrt (1 + τ ^ 2)) := by
  have hcl : (1 + Complex.I * (τ : ℂ)) ∈ closedStrip := ⟨by simp, by simp⟩
  have h1 := outerGbar_oneSub hε hcl
  have e : 1 - (1 + Complex.I * (τ : ℂ)) = starRingEnd ℂ (Complex.I * (τ : ℂ)) := by simp
  have hcl2 : Complex.I * (τ : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  rw [e, outerGbar_conj hε hcl2] at h1
  have h2 := congrArg norm h1
  rw [Complex.norm_conj, norm_mul] at h2
  have hnorm : ‖(-(ε : ℂ))‖ = 1 := by
    rcases hε with rfl | rfl <;> simp
  rw [hnorm, one_mul] at h2
  rw [← h2, norm_outerGbar_left hε]

/-- **`ct:outer` (1), decay.** `|G_ε(σ + iτ)| ≤ C (1 + |τ|)⁻¹` on the closed strip. -/
theorem outerGbar_bound {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, ∀ ζ ∈ closedStrip, ‖outerGbar ε ζ‖ ≤ C / (1 + |ζ.im|) := by
  obtain ⟨C₁, hC₁⟩ := re_outerHbar_bound
  refine ⟨Real.exp C₁, fun ζ hζ => ?_⟩
  set t : ℝ := |ζ.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hf : ‖(if ε = 1 then bHalf ζ else 1)‖ ≤ 1 := by
    split_ifs
    · exact norm_bHalf_le_one hζ
    · simp
  have hn1 : ‖ζ‖ ≤ 1 + t := by
    calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
      _ ≤ 1 + t := by
        have : |ζ.re| ≤ 1 := by rw [abs_of_nonneg hζ.1]; exact hζ.2
        linarith
  have hn2 : ‖1 - ζ‖ ≤ 1 + t := by
    calc ‖1 - ζ‖ ≤ |(1 - ζ).re| + |(1 - ζ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + t := by
        have : |(1 - ζ).re| ≤ 1 := by
          rw [abs_of_nonneg (by simp; exact hζ.2)]; simp; exact hζ.1
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
        linarith
  have hp : ‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖ ≤ 1 + t := by
    rw [norm_cpow_half, norm_cpow_half]
    have a1 : ‖ζ‖ ^ (1 / 2 : ℝ) ≤ (1 + t) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hn1 (by norm_num)
    have a2 : ‖1 - ζ‖ ^ (1 / 2 : ℝ) ≤ (1 + t) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hn2 (by norm_num)
    calc ‖ζ‖ ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) ≤ (1 + t) ^ (1 / 2 : ℝ) * (1 + t) ^ (1 / 2 : ℝ) :=
          mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = 1 + t := by
          rw [← Real.rpow_add (by linarith)]; norm_num
  have hexp : ‖Complex.exp (outerHbar ζ)‖ ≤ Real.exp C₁ / (1 + t) ^ 2 := by
    rw [Complex.norm_exp]
    have h1 := hC₁ ζ hζ
    calc Real.exp (outerHbar ζ).re ≤ Real.exp (-2 * Real.log (1 + t) + C₁) := Real.exp_le_exp.mpr h1
      _ = Real.exp C₁ / (1 + t) ^ 2 := by
          have : Real.exp (-2 * Real.log (1 + t)) = ((1 + t) ^ 2)⁻¹ := by
            rw [show -2 * Real.log (1 + t) = -(Real.log ((1 + t) ^ 2)) by
              rw [Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
          rw [Real.exp_add, this]
          ring
  have e0 : 0 < 1 + t := by linarith
  unfold outerGbar outerGm
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(if ε = 1 then bHalf ζ else 1)‖ * (‖ζ ^ (1 / 2 : ℂ)‖ * ‖(1 - ζ) ^ (1 / 2 : ℂ)‖ * ‖Complex.exp (outerHbar ζ)‖)
      ≤ 1 * ((1 + t) * (Real.exp C₁ / (1 + t) ^ 2)) := by
        gcongr
    _ = Real.exp C₁ / (1 + t) := by field_simp


end FormalResearch.SignUncertainty.CtOuter

module

public import FormalResearch.Special.AiryCftWeights

/-!
# Corollary D1: the Airy quadrature `∫ f = Σ f(a_n)/Ai'(a_n)²` for `f ∈ 𝒢_N`, `N < -1`

Statement formalised (CFT/PR240 `AIRY_POISSON.md` Corollary D1, the case `N < -1` of Theorem Q; `LOCAL_AIRY_MODEL.md`
property (Q)): for `f` entire with `|f(u)| ≤ C (1+|u|)^ν e(u)`, `e(u) = exp(-(4/3) Re u^{3/2})`, and `ν < -1`,

`∫_ℝ f(x) dx = Σ_{n ≥ 1} f(a_n)/Ai'(a_n)²`   (`airy_quadrature`; the series converges absolutely).

`f ∈ L¹(ℝ)` is automatic: `e ≤ 1` on `ℝ` (`airyEnv_ofReal_le_one`) and `(1+|x|)^ν` is integrable for `ν < -1`.

Proof: the defect bound of `AiryCftDefect` (Theorem D) on the good circles `|u| = r_k` of `AiryGoodCircles` with the
ratio bounds `|R_±| e ≤ 30√π` of `AiryRatioBounds` gives
`|Σ_{n ≤ N_k} f(a_n)/Ai'(a_n)² - ∫_{-r_k}^{r_k} f| ≤ 30 π √π C r_k (1+r_k)^ν ≤ 30 π √π C (1+r_k)^{ν+1} → 0`
(this is where `ν < -1` is used, besides the summability of `AiryCftWeights`).

Numerical evidence only (mpmath, 20 digits; not a proof ingredient): `f(u) = ∫_0^1 m(τ) Ai(2^{2/3}(u+τ)) dτ` with
`m(τ) = τ²(1-τ)²` (so `∫ f = 2^{-2/3}/30 = 0.020999`, the Airy-Poisson identity) has partial sums
`Σ_{n ≤ 25, 50, 100, 200, 400} = 0.00937, 0.01030, 0.01497, 0.01606, 0.01779`, closing the gap to `0.020999` like the predicted
tail `n^{-1/6}` (the exponent `(2/3)(ν - 1/2)` with `ν = -5/4`); the finite identity itself is checked to `10⁻⁵⁰` in `AiryCftDefect`.

The range `ν ≥ -1` is treated in `AiryCftQQuad` and `AiryCftQNonneg` (this file's absolute-convergence theorems are not superseded): the
Fejér–Riesz/Hardy arc bound (`FormalResearch.Complex.HardyArcDecay`) gives Theorem Q (1) for any real `ν` with `f ∈ L¹(ℝ)` (the limit of the partial sums over
good circles, `airyQ_tendsto`; `HasSum` if the series is summable or its terms are nonnegative), and Theorem Q (3), the sampling bound
`Σ|f(a_n)|/Ai'(a_n)² ≤ C‖f‖_b` (`airyQ_sampling`, `AiryCftQSample`), makes the `HasSum` unconditional for every real `ν` with `f ∈ L¹(ℝ)`
(`airyQ_hasSum_unc`, `AiryCftQUnc`).  The sharp pointwise bound of
Theorem Q (2) (`‖G(z)‖ ≤ ‖g‖₁/(4π Im z)`, `airyQ_pointwise_sharp`) is `AiryCftQSharp` (weak forms: `AiryCftQSamplePt`); not formalised: the Poisson representation of `G` (Lemma H).  The case where `f` is holomorphic only near the closed disc is `AiryCft2Ball` (`airy_defect_ball`); the
`P·Ai + Q·Ai'` quadrature, the Clark summation for `ν < -1` and the first zero of `Ai'` are in `AiryCft2Combo*`,
`AiryCft2Clark`, `AiryCft2FirstDerivZero`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- Good circles with data and the two Hermite-Biehler ratio bounds. -/
lemma airyCft_circles_ratio :
    ∃ (r : ℕ → ℝ) (N : ℕ → ℕ), (∀ k : ℕ, (k : ℝ) + 10 ≤ r k) ∧
      (∀ k n, 1 ≤ n → (n ≤ N k ↔ -airyZero n < r k)) ∧
      (∀ k, CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 (N k)) (r k)) ∧
      (∀ k (u : ℂ), ‖u‖ = r k → 0 ≤ u.im →
        ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) ∧
      (∀ k (u : ℂ), ‖u‖ = r k → u.im ≤ 0 →
        ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) := by
  have h : ∀ k : ℕ, ∃ r : ℝ, (k : ℝ) + 10 ≤ r ∧ ∃ N : ℕ,
      (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < r)) ∧
      CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) r ∧
      (∀ u : ℂ, ‖u‖ = r → 0 ≤ u.im →
        ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) ∧
      (∀ u : ℂ, ‖u‖ = r → u.im ≤ 0 →
        ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π) := by
    intro k
    obtain ⟨r, h1, h2, h⟩ := good_circle_exists (k + 10) (by omega)
    have hk' : ((k + 10 : ℕ) : ℝ) ≤ r := h1
    push_cast at hk'
    have hr : 0 < r := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hgood : ∀ u : ℂ, ‖u‖ = r → airyAiC u ≠ 0 := by
      intro u hu h0
      have := h u hu
      rw [h0, norm_zero] at this
      have : 0 < 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u := by
        have := airyEnv_pos u
        have : 0 < (1 + r) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
        positivity
      linarith
    obtain ⟨N, hN, hD⟩ := airy_circleData hr hgood
    refine ⟨r, hk', N, hN, hD, fun u hu hi => ?_, fun u hu hi => ?_⟩
    · exact airy_Rplus_bound hi (hu ▸ h u hu)
    · exact airy_Rminus_bound hi (hu ▸ h u hu)
  choose r h1 N h3 h4 h5 h6 using h
  exact ⟨r, N, h1, h3, h4, h5, h6⟩

/-- `f ∈ 𝒢_ν` is integrable on `ℝ` for `ν < -1`. -/
lemma airy_integrable_real {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C ν : ℝ} (hC : 0 ≤ C) (hν : ν < -1)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    Integrable (fun x : ℝ => f (x : ℂ)) := by
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(-ν)) ) :=
    integrable_one_add_norm (E := ℝ) (r := -ν) (by rw [Module.finrank_self]; push_cast; linarith)
  simp only [neg_neg] at hint
  refine Integrable.mono' (hint.const_mul C) (hf.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h1 := hb (x : ℂ)
  rw [Complex.norm_real] at h1
  have h2 := airyEnv_ofReal_le_one x
  have h3 : 0 ≤ C * (1 + ‖x‖) ^ ν := by positivity
  calc ‖f (x : ℂ)‖ ≤ C * (1 + ‖x‖) ^ ν * airyEnv (x : ℂ) := h1
    _ ≤ C * (1 + ‖x‖) ^ ν * 1 := by gcongr
    _ = _ := by ring

/-- **Corollary D1 (Airy quadrature).** For `f` entire with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `ν < -1`:
`∫_ℝ f = Σ_{n ≥ 1} f(a_n)/Ai'(a_n)²` (absolutely convergent), and `f ∈ L¹(ℝ)`. -/
theorem airy_quadrature {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C ν : ℝ} (hC : 0 ≤ C) (hν : ν < -1)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, f (x : ℂ)) := by
  obtain ⟨r, N, h1, h3, h4, h5, h6⟩ := airyCft_circles_ratio
  have hfi := airy_integrable_real hf hC hν hb
  have hu := airy_summable_weighted hC hν hb
  set L : ℂ := ∫ x : ℝ, f (x : ℂ) with hL
  have hr0 : ∀ k, 0 < r k := fun k => by linarith [h1 k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- the defect bound on each circle
  have hdef : ∀ k, ‖(∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ ≤ π * r k * (C * (1 + r k) ^ ν * (30 * √π)) := by
    intro k
    have hpos : 0 ≤ C * (1 + r k) ^ ν := by
      have : 0 < (1 + r k) ^ ν := Real.rpow_pos_of_pos (by linarith [hr0 k]) _
      positivity
    refine airy_defect_bound (h4 k) hf (fun w hw him => ?_) (fun w hw him => ?_)
    · have hfw := hb w
      rw [hw] at hfw
      rw [norm_mul]
      have h7 := h5 k w hw him
      have he := airyEnv_pos w
      calc ‖f w‖ * ‖(airyBiC w - I * airyAiC w) / airyAiC w‖
          ≤ (C * (1 + r k) ^ ν * airyEnv w) * ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ := by gcongr
        _ = C * (1 + r k) ^ ν * (‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w) := by ring
        _ ≤ C * (1 + r k) ^ ν * (30 * √π) := by gcongr
    · have hfw := hb w
      rw [hw] at hfw
      rw [norm_mul]
      have h7 := h6 k w hw him
      have he := airyEnv_pos w
      calc ‖f w‖ * ‖(airyBiC w + I * airyAiC w) / airyAiC w‖
          ≤ (C * (1 + r k) ^ ν * airyEnv w) * ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ := by gcongr
        _ = C * (1 + r k) ^ ν * (‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w) := by ring
        _ ≤ C * (1 + r k) ^ ν * (30 * √π) := by gcongr
  -- the error sequence
  have hrt : Tendsto r atTop atTop :=
    tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ) + 10) (fun k => h1 k)
      (tendsto_atTop_add_const_right _ (10 : ℝ) tendsto_natCast_atTop_atTop)
  have hrt' : Tendsto (fun k => -r k) atTop atBot := tendsto_neg_atTop_atBot.comp hrt
  have hI : Tendsto (fun k => ∫ x in (-(r k))..(r k), f (x : ℂ)) atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral hfi hrt' hrt
  have hI' : Tendsto (fun k => ‖L - ∫ x in (-(r k))..(r k), f (x : ℂ)‖) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := L)).sub hI
    rw [sub_self] at this
    simpa using this.norm
  have hB : Tendsto (fun k : ℕ => 30 * π * √π * C * (((k : ℝ) + 1) ^ (ν + 1))) atTop (𝓝 0) := by
    have h0 := tendsto_rpow_neg_atTop (show 0 < -(ν + 1) by linarith)
    simp only [neg_neg] at h0
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa using (h0.comp h2).const_mul (30 * π * √π * C)
  have hE : Tendsto (fun k => ‖L - ∫ x in (-(r k))..(r k), f (x : ℂ)‖ + 30 * π * √π * C * (((k : ℝ) + 1) ^ (ν + 1)))
      atTop (𝓝 0) := by
    simpa using hI'.add hB
  refine airyCft_hasSum_of_partial hu hE (airyCft_N_tendsto h1 h3) (Eventually.of_forall fun k => ?_)
  rw [← airyCft_sum_Icc (fun n : ℕ => f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)]
  have hk := hdef k
  have hrk : r k * (1 + r k) ^ ν ≤ ((k : ℝ) + 1) ^ (ν + 1) := by
    have hp1 : (0 : ℝ) < 1 + r k := by linarith [hr0 k]
    have e1 : (1 + r k) ^ (ν + 1) = (1 + r k) ^ ν * (1 + r k) := Real.rpow_add_one hp1.ne' ν
    have h2 : (1 + r k) ^ (ν + 1) ≤ ((k : ℝ) + 1) ^ (ν + 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [h1 k]) (by linarith)
    have h3 : 0 < (1 + r k) ^ ν := Real.rpow_pos_of_pos hp1 _
    nlinarith
  calc ‖L - ∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2‖
      ≤ ‖L - ∫ x in (-(r k))..(r k), f (x : ℂ)‖ +
        ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) -
          ∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2‖ := by
        have := norm_add_le (L - ∫ x in (-(r k))..(r k), f (x : ℂ))
          ((∫ x in (-(r k))..(r k), f (x : ℂ)) -
            ∑ n ∈ Finset.Icc 1 (N k), f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2)
        rwa [sub_add_sub_cancel] at this
    _ ≤ _ := by
        gcongr
        rw [norm_sub_rev]
        refine hk.trans ?_
        have h4 : 0 ≤ C := hC
        have : π * r k * (C * (1 + r k) ^ ν * (30 * √π)) = 30 * π * √π * C * (r k * (1 + r k) ^ ν) := by ring
        rw [this]
        gcongr

/-- info: 'FormalResearch.Special.airy_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_quadrature

end FormalResearch.Special

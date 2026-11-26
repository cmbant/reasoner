module

public import FormalResearch.SignUncertainty.CtOuterBandFinal
public import FormalResearch.Analysis.VanDerCorput

/-!
# Uniform bound for the outer-band integral at bounded `μ₀` (`ct:dual-id` (2), `ct:cfu` (2))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (2) (the uniform bound `|K_ε| ≤ C√c`) and
Lemma `ct:cfu` (2) (the range `1 ≤ μ₀ < M₀`).  **Proved.**  For `μ₀ = c·min(1,τ₀³) ∈ [1, M₀)` the improper integral `I = ∫₀^∞ A e^{icφ}` (`φ' = m - m(τ₀)`) exists and
`√c ‖I‖ ≤ C (1 + √(c·min(1,τ₀³)))`: `τ₀ ≤ 1` by the crude bound on `[0,2τ₀]` plus the tail (`bdd_small_final`); `τ₀ ≥ 1` by the crude bound
on `[0,1]`, double integration by parts on `[1,τ₀/2]` (`mid_ibp`), second-derivative van der Corput on `[τ₀/2,2τ₀]` (`vdc_mid`) and the tail
(`tail_bdd`), giving `‖I‖ ≤ C` (`bdd_large`).  `ct_cfu_outer_bdd` is the form for `K_ε`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtOsc

open CtOuter

/-- The tail `∫_a^∞ A e^{icϕ}` exists and is bounded by the boundary terms and the double-IBP remainder. -/
theorem tail_est {C0 CA γ c L a : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hγ : 0 < γ) (hc : 0 < c) (ha : 0 < a)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) (hp : ∀ τ : ℝ, a ≤ τ → γ * sg τ ≤ |m τ - L|) :
    ∃ V : ℂ, Tendsto (fun b : ℝ => ∫ τ in a..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 V) ∧
      ‖V‖ ≤ (1 / c) * (CA * a ^ (1 / 2 : ℝ) / (1 + a) / |m a - L|) +
        (1 / c) ^ 2 * (CA * (1 + C0 / γ) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / |m a - L| / |m a - L|) +
        (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
          ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ))) := by
  obtain ⟨J, hV, hJ⟩ := piece3_gen hM hγ hA.CA0 hc ha hϕ hA.d1 hA.d2 hA.c2 hA.b0 hA.b1 hA.b2 hp
  refine ⟨_, hV, ?_⟩
  have hsg : 0 < sg a := by unfold sg; positivity
  have hpa : γ * sg a ≤ |m a - L| := hp a le_rfl
  have hpp : 0 < |m a - L| := lt_of_lt_of_le (by positivity) hpa
  have hn1 : ‖(1 / (Complex.I * (c : ℂ)))‖ = 1 / c := norm_inv_I_mul hc
  have hexp : ‖Complex.exp (Complex.I * c * (ϕ a : ℂ))‖ = 1 := by
    rw [show Complex.I * (c : ℂ) * (ϕ a : ℂ) = ((c * ϕ a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hnr : ‖((m a - L : ℝ) : ℂ)‖ = |m a - L| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hH := H_pt (τ := a) (p := |m a - L|) (γ := γ) (C0 := C0) (KB := CA) ha hpp hγ hM.C0nn hA.CA0 hpa
    (ϕ1 := fun τ => m τ - L) (ϕ2 := m1) (B := A) (B1 := A1) le_rfl (hM.abs_m1 ha) (hA.b0 a ha) (hA.b1 a ha)
  have e1 : ‖(1 / (Complex.I * (c : ℂ))) * (A a / ((m a - L : ℝ) : ℂ) * Complex.exp (Complex.I * c * (ϕ a : ℂ)))‖ ≤
      (1 / c) * (CA * a ^ (1 / 2 : ℝ) / (1 + a) / |m a - L|) := by
    rw [norm_mul, hn1, norm_mul, norm_div, hnr, hexp, mul_one]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hA.b0 a ha) hpp.le) (by positivity)
  have e2 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2 * (ibpH A A1 (fun τ => m τ - L) m1 a / ((m a - L : ℝ) : ℂ) *
      Complex.exp (Complex.I * c * (ϕ a : ℂ)))‖ ≤
      (1 / c) ^ 2 * (CA * (1 + C0 / γ) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / |m a - L| / |m a - L|) := by
    rw [norm_mul, norm_pow, hn1, norm_mul, norm_div, hnr, hexp, mul_one]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hH hpp.le) (by positivity)
  have e3 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2 * (J : ℂ)‖ ≤ (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
          ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ))) := by
    rw [norm_mul, norm_pow, hn1]
    exact mul_le_mul_of_nonneg_left hJ (by positivity)
  refine le_trans (norm_add₃_le) ?_
  rw [norm_neg]
  linarith only [e1, e2, e3]

lemma hp_two {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ} (hM : MData C0 m m1 m2 m3) {τ0 τ : ℝ} (hτ0 : 0 < τ0) (hτ : 2 * τ0 ≤ τ) :
    (1 / 4 : ℝ) * sg τ ≤ |m τ - m τ0| := by
  have hτp : 0 < τ := by linarith
  have h1 := hM.step (κ := 1 / 2) (by norm_num) (by norm_num) hτp
  have h2 : m τ0 ≤ m (1 / 2 * τ) :=
    hM.strictMonoOn.monotoneOn (show τ0 ∈ Ioi (0 : ℝ) from hτ0) (show 1 / 2 * τ ∈ Ioi (0 : ℝ) by
      simp only [mem_Ioi]; positivity) (by linarith)
  have h3 : (1 / 4 : ℝ) * sg τ ≤ m τ - m τ0 := by
    have : (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 := by norm_num
    rw [this] at h1; linarith
  exact h3.trans (le_abs_self _)

/-- `‖∫_0^a A e^{icϕ}‖ ≤ (2/3) C_A a^{3/2}`. -/
lemma crude_left {CA c a : ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} (hA : AmpBd CA A A1 A2) (ha : 0 ≤ a)
    (hϕc : ContinuousOn ϕ (Ioi 0)) :
    ‖∫ τ in (0 : ℝ)..a, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ (2 / 3) * CA * a ^ (3 / 2 : ℝ) := by
  have hint : IntervalIntegrable (fun τ => A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) volume 0 a :=
    intInt_BE ha hA.CA0 (fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt) hϕc hA.b0
  have hg : IntervalIntegrable (fun τ : ℝ => CA * τ ^ (1 / 2 : ℝ)) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := 1 / 2) (by norm_num)).const_mul CA
  have hb : ∀ τ ∈ Ioc (0 : ℝ) a, ‖A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ CA * τ ^ (1 / 2 : ℝ) := by
    intro τ hτ
    have hτp : 0 < τ := hτ.1
    rw [norm_mul]
    simp only [norm_cexp_phase, mul_one]
    refine (hA.b0 τ hτp).trans ?_
    exact div_le_self (by have := hA.CA0; positivity) (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le ha
    (Eventually.of_forall fun τ (hτ : τ ∈ Ioc (0 : ℝ) a) => hb τ hτ) hg
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  have : ((1 : ℝ) / 2 + 1) = 3 / 2 := by norm_num
  rw [this, Real.zero_rpow (by norm_num)]; ring

/-- The improper integral exists and is bounded by the crude left piece on `[0,a]` plus the tail from `a`, whenever
`(1/4) sg ≤ |m - L|` on `[a, ∞)`. -/
theorem bdd_a {C0 CA c a L : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 0 < c) (ha : 0 < a)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) (hp : ∀ τ : ℝ, a ≤ τ → (1 / 4 : ℝ) * sg τ ≤ |m τ - L|) :
    ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
      ‖I‖ ≤ (2 / 3) * CA * a ^ (3 / 2 : ℝ) +
        ((1 / c) * (CA * a ^ (1 / 2 : ℝ) / (1 + a) / |m a - L|) +
        (1 / c) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / |m a - L| /
          |m a - L|) +
        (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
          ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ)))) := by
  have hϕc : ContinuousOn ϕ (Ioi 0) := fun τ hτ => (hϕ τ hτ).continuousAt.continuousWithinAt
  obtain ⟨V, hV, hVb⟩ := tail_est (γ := 1 / 4) hM hA (by norm_num) hc ha hϕ hp
  have hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun τ => A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) volume 0 b :=
    fun b hb => intInt_BE hb hA.CA0 (fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt) hϕc hA.b0
  refine ⟨(∫ τ in (0 : ℝ)..a, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) + V, ?_, ?_⟩
  · refine (hV.const_add _).congr' ?_
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (intervalIntegral_split ha.le hb (hint b (by linarith))).symm
  · refine (norm_add_le _ _).trans ?_
    have := crude_left (c := c) hA ha.le hϕc
    linarith only [this, hVb]

/-- **Small `τ₀`.** For `0 < τ₀`, the improper integral exists and is bounded by the crude left piece plus the tail. -/
theorem bdd_small {C0 CA c τ0 : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 0 < c) (hτ0 : 0 < τ0)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) :
    ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
      ‖I‖ ≤ (2 / 3) * CA * (2 * τ0) ^ (3 / 2 : ℝ) +
        ((1 / c) * (CA * (2 * τ0) ^ (1 / 2 : ℝ) / (1 + 2 * τ0) / |m (2 * τ0) - m τ0|) +
        (1 / c) ^ 2 * (CA * (1 + C0 / (1 / 4)) * ((2 * τ0) ^ (-1 / 2 : ℝ) / (1 + 2 * τ0)) / |m (2 * τ0) - m τ0| /
          |m (2 * τ0) - m τ0|) +
        (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
          ((2 / 9) * (2 * τ0) ^ (-9 / 2 : ℝ) + (2 / 3) * (2 * τ0) ^ (-3 / 2 : ℝ)))) :=
  bdd_a hM hA hc (by positivity) hϕ (fun τ hτ => hp_two hM hτ0 hτ)

lemma rp_all {a : ℝ} (ha : 0 < a) : a ^ (1 / 2 : ℝ) = Real.sqrt a ∧ a ^ (-1 / 2 : ℝ) = (Real.sqrt a)⁻¹ ∧
    a ^ (-3 / 2 : ℝ) = ((Real.sqrt a) ^ 3)⁻¹ ∧ a ^ (-9 / 2 : ℝ) = ((Real.sqrt a) ^ 9)⁻¹ ∧
    a ^ (3 / 2 : ℝ) = (Real.sqrt a) ^ 3 := by
  have h : ∀ q : ℝ, a ^ q = ((Real.sqrt a) ^ (2 : ℕ)) ^ q := fun q => by rw [Real.sq_sqrt ha.le]
  have hw : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have key : ∀ n : ℕ, ((Real.sqrt a) ^ (2 : ℕ)) ^ ((n : ℝ) / 2) = (Real.sqrt a) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    rw [show ((2 : ℕ) : ℝ) * ((n : ℝ) / 2) = n by push_cast; ring, Real.rpow_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := key 1; simpa [h] using this
  · rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha.le, Real.sqrt_eq_rpow]
  · rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg ha.le, h (3 / 2)]
    have := key 3; norm_num at this; rw [this]
  · rw [show (-9 / 2 : ℝ) = -(9 / 2) by norm_num, Real.rpow_neg ha.le, h (9 / 2)]
    have := key 9; norm_num at this; rw [this]
  · rw [h (3 / 2)]; have := key 3; norm_num at this; rw [this]

/-- The pure-real estimate behind the small-`τ₀` bound. -/
lemma small_arith {CA C0 r w p : ℝ} (hCA : 0 ≤ CA) (hC0 : 0 ≤ C0) (hr : 0 < r) (hw : 0 < w) (hw2 : w ^ 2 ≤ 2)
    (hX : 2 ≤ r * w ^ 3) (hp0 : w ^ 4 / 20 ≤ p) :
    r * ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p) +
      (1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p) +
      (1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) ≤
      10 * CA + 50 * (CA * (1 + 4 * C0)) + 4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 := by
  have hp : 0 < p := lt_of_lt_of_le (by positivity) hp0
  set X := r * w ^ 3 with hXdef
  have hX0 : 0 < X := by positivity
  have h1p : 1 / p ≤ 20 / w ^ 4 := by
    rw [div_le_div_iff₀ hp (by positivity)]; nlinarith
  -- first term
  have t1 : r * ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p)) ≤ 10 * CA := by
    have e1 : CA * w / (1 + w ^ 2) / p ≤ CA * w * (20 / w ^ 4) := by
      calc CA * w / (1 + w ^ 2) / p ≤ CA * w / p := by
            apply div_le_div_of_nonneg_right _ hp.le
            exact div_le_self (by positivity) (by nlinarith)
        _ = CA * w * (1 / p) := by ring
        _ ≤ CA * w * (20 / w ^ 4) := mul_le_mul_of_nonneg_left h1p (by positivity)
    have e2 : r * ((1 / r ^ 2) * (CA * w * (20 / w ^ 4))) = 20 * CA / X := by
      rw [hXdef]; field_simp
    calc r * ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p)) ≤ r * ((1 / r ^ 2) * (CA * w * (20 / w ^ 4))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (by positivity)) hr.le
      _ = 20 * CA / X := e2
      _ ≤ 10 * CA := by rw [div_le_iff₀ hX0]; nlinarith
  -- second term
  have t2 : r * ((1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p)) ≤ 50 * (CA * (1 + 4 * C0)) := by
    have h2p : 1 / p / p ≤ (20 / w ^ 4) * (20 / w ^ 4) := by
      rw [div_div, show (20 / w ^ 4) * (20 / w ^ 4) = 1 / ((w ^ 4 / 20) * (w ^ 4 / 20)) by field_simp]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hp0 hp0 (by positivity) hp.le)
    have e1 : CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p ≤
        CA * (1 + 4 * C0) * (w⁻¹ * ((20 / w ^ 4) * (20 / w ^ 4))) := by
      have : CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p =
          CA * (1 + 4 * C0) * (w⁻¹ / (1 + w ^ 2)) * (1 / p / p) := by field_simp
      rw [this]
      have h3 : w⁻¹ / (1 + w ^ 2) ≤ w⁻¹ := div_le_self (by positivity) (by nlinarith)
      have h4 : 0 ≤ CA * (1 + 4 * C0) := by positivity
      calc CA * (1 + 4 * C0) * (w⁻¹ / (1 + w ^ 2)) * (1 / p / p) ≤ CA * (1 + 4 * C0) * w⁻¹ * ((20 / w ^ 4) * (20 / w ^ 4)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h3 h4) h2p (by positivity) (by positivity)
        _ = _ := by ring
    have e2 : r * ((1 / r ^ 2) ^ 2 * (CA * (1 + 4 * C0) * (w⁻¹ * ((20 / w ^ 4) * (20 / w ^ 4))))) =
        400 * (CA * (1 + 4 * C0)) / X ^ 3 := by rw [hXdef]; field_simp; ring
    have e3 : 400 * (CA * (1 + 4 * C0)) / X ^ 3 ≤ 50 * (CA * (1 + 4 * C0)) := by
      have h8 : 8 ≤ X ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hX 3]
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ CA * (1 + 4 * C0) := by positivity
      nlinarith
    calc _ ≤ r * ((1 / r ^ 2) ^ 2 * (CA * (1 + 4 * C0) * (w⁻¹ * ((20 / w ^ 4) * (20 / w ^ 4))))) := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : CA * (1 + C0 / (1 / 4)) = CA * (1 + 4 * C0) := by ring
          rw [this] at e1 ⊢; exact e1
      _ = _ := e2
      _ ≤ _ := e3
  -- third term
  have t3 : r * ((1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) ≤ 4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 := by
    have hK : (4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) =
        4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 := by ring
    rw [hK]
    set K3 := 4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 with hK3
    have hK30 : 0 ≤ K3 := by positivity
    have hrw : X / 2 ≤ r * w := by
      rw [hXdef]
      have : w ^ 3 ≤ 2 * w := by nlinarith
      nlinarith
    have h8 : 8 ≤ X ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hX 3]
    have e1 : r * (1 / r ^ 2) ^ 2 * ((w ^ 9)⁻¹) = 1 / X ^ 3 := by rw [hXdef]; field_simp
    have e2 : r * (1 / r ^ 2) ^ 2 * ((w ^ 3)⁻¹) = 1 / (r * w) ^ 3 := by field_simp
    have e3 : 1 / (r * w) ^ 3 ≤ 8 / X ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (X / 2) ^ 3 ≤ (r * w) ^ 3 := pow_le_pow_left₀ (by positivity) hrw 3
      nlinarith
    have e4 : (2 / 9) * (1 / X ^ 3) + (2 / 3) * (8 / X ^ 3) ≤ 1 := by
      have : (2 / 9) * (1 / X ^ 3) + (2 / 3) * (8 / X ^ 3) = (2 / 9 + 16 / 3) / X ^ 3 := by ring
      rw [this, div_le_one (by positivity)]; linarith
    calc r * ((1 / r ^ 2) ^ 2 * (K3 * ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) =
        K3 * ((2 / 9) * (r * (1 / r ^ 2) ^ 2 * ((w ^ 9)⁻¹)) + (2 / 3) * (r * (1 / r ^ 2) ^ 2 * ((w ^ 3)⁻¹))) := by ring
      _ ≤ K3 * ((2 / 9) * (1 / X ^ 3) + (2 / 3) * (8 / X ^ 3)) := by
          rw [e1, e2]
          apply mul_le_mul_of_nonneg_left _ hK30
          have := mul_le_mul_of_nonneg_left e3 (by norm_num : (0 : ℝ) ≤ 2 / 3)
          linarith
      _ ≤ K3 * 1 := mul_le_mul_of_nonneg_left e4 hK30
      _ = K3 := mul_one _
  calc _ = r * ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p)) +
      r * ((1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p)) +
      r * ((1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) := by ring
    _ ≤ _ := by linarith only [t1, t2, t3]

/-- **Bounded `μ₀`, small `τ₀`.** For `τ₀ ≤ 1` and `c τ₀³ ≥ 1`: `√c ‖I‖ ≤ C (1 + √(c τ₀³))`. -/
theorem bdd_small_final (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {c τ0 : ℝ},
      MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 0 < c → 0 < τ0 → τ0 ≤ 1 → 1 ≤ c * τ0 ^ 3 →
      (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) →
      ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
        Real.sqrt c * ‖I‖ ≤ Cs * (1 + Real.sqrt (c * τ0 ^ 3)) := by
  set K3 : ℝ := 4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 with hK3
  have hK30 : 0 ≤ K3 := by rw [hK3]; positivity
  refine ⟨2 * CA + 10 * CA + 50 * (CA * (1 + 4 * C0)) + K3, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ c τ0 hM hA hc hτ0 hτ1 hμ hϕ
  obtain ⟨I, hI, hb⟩ := bdd_small hM hA hc hτ0 hϕ
  refine ⟨I, hI, ?_⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ c = r ^ 2 := ⟨Real.sqrt c, Real.sqrt_pos.2 hc, (Real.sq_sqrt hc.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  have ha : 0 < 2 * τ0 := by positivity
  obtain ⟨e1, e2, e3, e4, e5⟩ := rp_all ha
  set w := Real.sqrt (2 * τ0) with hwdef
  have hw : 0 < w := Real.sqrt_pos.2 ha
  have hw2 : w ^ 2 = 2 * τ0 := Real.sq_sqrt ha.le
  have hp := hp_two hM hτ0 (le_refl (2 * τ0))
  set p := |m (2 * τ0) - m τ0| with hpdef
  rw [e1, e2, e3, e4, e5, ← hw2] at hb
  have hsg : (1 / 4 : ℝ) * sg (2 * τ0) ≤ p := hp
  have hw4 : w ^ 4 / 20 ≤ p := by
    refine le_trans ?_ hsg
    unfold sg
    rw [← hw2, show (w ^ 2) ^ 2 = w ^ 4 by ring]
    have h2 : w ^ 4 ≤ 4 := by nlinarith
    rw [show (1 / 4 : ℝ) * (w ^ 4 / (1 + w ^ 4)) = w ^ 4 / (4 * (1 + w ^ 4)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hw 4]
  have hw22 : w ^ 2 ≤ 2 := by rw [hw2]; linarith
  have hX2 : (r * w ^ 3) ^ 2 = 8 * (r ^ 2 * τ0 ^ 3) := by
    have : w ^ 6 = 8 * τ0 ^ 3 := by
      have : w ^ 6 = (w ^ 2) ^ 3 := by ring
      rw [this, hw2]; ring
    calc (r * w ^ 3) ^ 2 = r ^ 2 * w ^ 6 := by ring
      _ = _ := by rw [this]; ring
  have hX : 2 ≤ r * w ^ 3 := by
    have h1 : 4 ≤ (r * w ^ 3) ^ 2 := by rw [hX2]; nlinarith
    have h0 : 0 ≤ r * w ^ 3 := by positivity
    nlinarith
  have hXs : r * w ^ 3 ≤ 3 * Real.sqrt (r ^ 2 * τ0 ^ 3) := by
    have hq : (Real.sqrt (r ^ 2 * τ0 ^ 3)) ^ 2 = r ^ 2 * τ0 ^ 3 := Real.sq_sqrt (by positivity)
    have : (r * w ^ 3) ^ 2 ≤ (3 * Real.sqrt (r ^ 2 * τ0 ^ 3)) ^ 2 := by
      rw [hX2, mul_pow, hq]; nlinarith [mul_nonneg (sq_nonneg r) (pow_pos hτ0 3).le]
    exact (abs_le_of_sq_le_sq' this (by positivity)).2
  have hsm := small_arith hCA hC0.le hr hw hw22 hX hw4
  have hcr : r * ((2 / 3) * CA * w ^ 3) ≤ 2 * CA * Real.sqrt (r ^ 2 * τ0 ^ 3) := by
    have : r * ((2 / 3) * CA * w ^ 3) = (2 / 3) * CA * (r * w ^ 3) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hXs (by positivity : 0 ≤ (2 / 3) * CA)
    linarith only [this]
  have hsq0 := Real.sqrt_nonneg (r ^ 2 * τ0 ^ 3)
  have hb2 : ‖I‖ ≤ (2 / 3) * CA * w ^ 3 + ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p) +
      (1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p) +
      (1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) := hb
  generalize hTt : ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p) +
      (1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p) +
      (1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) = Tt at hb2 hsm
  have h0 : r * ‖I‖ ≤ r * ((2 / 3) * CA * w ^ 3) + r * Tt := by
    have := mul_le_mul_of_nonneg_left hb2 hr.le
    linarith only [this]
  have h1 := add_le_add hcr hsm
  have h3 : 0 ≤ CA * (1 + 4 * C0) := by positivity
  have h2 : 2 * CA * Real.sqrt (r ^ 2 * τ0 ^ 3) ≤ (2 * CA + 10 * CA + 50 * (CA * (1 + 4 * C0)) + K3) *
      Real.sqrt (r ^ 2 * τ0 ^ 3) :=
    mul_le_mul_of_nonneg_right (by linarith only [h3, hCA, hK30]) hsq0
  linarith only [h0, h1, h2, hCA, hK30, h3]

/-- **Tiny `μ₀`** (`c ≥ 2`, `λ = c^{-1/3}`, `(1/4) sg ≤ |m - L|` on `[2λ, ∞)`): `√c ‖I‖ ≤ C`. -/
theorem bdd_tiny (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {c lam L : ℝ},
      MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 2 ≤ c → 0 < lam → c * lam ^ 3 = 1 →
      (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) → (∀ τ : ℝ, 2 * lam ≤ τ → (1 / 4 : ℝ) * sg τ ≤ |m τ - L|) →
      ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
        Real.sqrt c * ‖I‖ ≤ Ct := by
  set K3 : ℝ := 4 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 16 with hK3
  have hK30 : 0 ≤ K3 := by rw [hK3]; positivity
  refine ⟨2 * CA + 10 * CA + 50 * (CA * (1 + 4 * C0)) + K3, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ c lam L hM hA hc hlam hcl hϕ hp
  have hc0 : 0 < c := by linarith
  have ha : 0 < 2 * lam := by positivity
  obtain ⟨I, hI, hb⟩ := bdd_a hM hA hc0 ha hϕ hp
  refine ⟨I, hI, ?_⟩
  have hl1 : lam < 1 := by
    by_contra h
    push_neg at h
    have : 1 ≤ lam ^ 3 := one_le_pow₀ h
    nlinarith
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ c = r ^ 2 := ⟨Real.sqrt c, Real.sqrt_pos.2 hc0, (Real.sq_sqrt hc0.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  obtain ⟨e1, e2, e3, e4, e5⟩ := rp_all ha
  set w := Real.sqrt (2 * lam) with hwdef
  have hw : 0 < w := Real.sqrt_pos.2 ha
  have hw2 : w ^ 2 = 2 * lam := Real.sq_sqrt ha.le
  have hpa := hp (2 * lam) le_rfl
  set p := |m (2 * lam) - L| with hpdef
  rw [e1, e2, e3, e4, e5, ← hw2] at hb
  have hw22 : w ^ 2 ≤ 2 := by rw [hw2]; linarith
  have hw4 : w ^ 4 / 20 ≤ p := by
    refine le_trans ?_ hpa
    unfold sg
    rw [← hw2, show (w ^ 2) ^ 2 = w ^ 4 by ring]
    have h2 : w ^ 4 ≤ 4 := by nlinarith
    rw [show (1 / 4 : ℝ) * (w ^ 4 / (1 + w ^ 4)) = w ^ 4 / (4 * (1 + w ^ 4)) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hw 4]
  have hX2 : (r * w ^ 3) ^ 2 = 8 := by
    have : w ^ 6 = 8 * lam ^ 3 := by
      have : w ^ 6 = (w ^ 2) ^ 3 := by ring
      rw [this, hw2]; ring
    calc (r * w ^ 3) ^ 2 = r ^ 2 * w ^ 6 := by ring
      _ = 8 * (r ^ 2 * lam ^ 3) := by rw [this]; ring
      _ = 8 := by rw [hcl]; ring
  have hX : 2 ≤ r * w ^ 3 := by
    have h1 : 4 ≤ (r * w ^ 3) ^ 2 := by rw [hX2]; norm_num
    have h0 : 0 ≤ r * w ^ 3 := by positivity
    nlinarith
  have hX3 : r * w ^ 3 ≤ 3 := by
    have h0 : 0 ≤ r * w ^ 3 := by positivity
    nlinarith
  have hsm := small_arith hCA hC0.le hr hw hw22 hX hw4
  have hcr : r * ((2 / 3) * CA * w ^ 3) ≤ 2 * CA := by
    have : r * ((2 / 3) * CA * w ^ 3) = (2 / 3) * CA * (r * w ^ 3) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hX3 (by positivity : 0 ≤ (2 / 3) * CA)
    linarith only [this]
  have hb2 : ‖I‖ ≤ (2 / 3) * CA * w ^ 3 + ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p) +
      (1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p) +
      (1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) := hb
  generalize hTt : ((1 / r ^ 2) * (CA * w / (1 + w ^ 2) / p) +
      (1 / r ^ 2) ^ 2 * (CA * (1 + C0 / (1 / 4)) * (w⁻¹ / (1 + w ^ 2)) / p / p) +
      (1 / r ^ 2) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4) + 3 * C0 ^ 2 / (1 / 4) ^ 2) / (1 / 4) ^ 2) *
        ((2 / 9) * ((w ^ 9)⁻¹) + (2 / 3) * ((w ^ 3)⁻¹)))) = Tt at hb2 hsm
  have h0 : r * ‖I‖ ≤ r * ((2 / 3) * CA * w ^ 3) + r * Tt := by
    have := mul_le_mul_of_nonneg_left hb2 hr.le
    linarith only [this]
  have h3 : 0 ≤ CA * (1 + 4 * C0) := by positivity
  linarith only [h0, hcr, hsm]


/-- Bounded variation of the amplitude on `[a, b]` from a derivative bound. -/
lemma A_bv {CA Lc a b : ℝ} {A A1 A2 : ℝ → ℂ} (hA : AmpBd CA A A1 A2) (ha : 0 < a) (hab : a ≤ b) (hLc : 0 ≤ Lc)
    (hb : ∀ τ ∈ Icc a b, ‖A1 τ‖ ≤ Lc) :
    BoundedVariationOn A (Icc a b) ∧ (eVariationOn A (Icc a b)).toReal ≤ Lc * (b - a) := by
  have hlip : LipschitzOnWith (Real.toNNReal Lc) A (Icc a b) := by
    refine Convex.lipschitzOnWith_of_nnNorm_hasDerivWithin_le (f' := A1) (convex_Icc a b) ?_ ?_
    · exact fun x hx => (hA.d1 x (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
    · intro x hx
      have := hb x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hLc]; exact this
  have hmaps : MapsTo (id : ℝ → ℝ) (Icc a b) (Icc a b) := fun x hx => hx
  have hle := hlip.comp_eVariationOn_le hmaps
  have hid : eVariationOn (id : ℝ → ℝ) (Icc a b) = ENNReal.ofReal (b - a) := by
    have := (monotoneOn_id (s := (Set.univ : Set ℝ))).eVariationOn_eq (a := a) (b := b) (Set.mem_univ _) (Set.mem_univ _)
    simpa using this
  rw [Function.comp_id, hid] at hle
  have hfin : eVariationOn A (Icc a b) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  refine ⟨hfin, ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hle
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by linarith), Real.coe_toNNReal _ hLc] at this
  exact this

/-- **Middle window `[τ₀/2, 2τ₀]`** (second-derivative van der Corput): `‖∫‖ ≤ 144 C_A / √c` for `τ₀ ≥ 1`. -/
theorem vdc_mid {C0 CA c τ0 : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 0 < c) (hτ0 : 1 ≤ τ0)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) :
    ‖∫ τ in (τ0 / 2)..(2 * τ0), A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ 144 * CA / Real.sqrt c := by
  have hτp : 0 < τ0 := by linarith
  have hab : τ0 / 2 ≤ 2 * τ0 := by linarith
  have hap : 0 < τ0 / 2 := by positivity
  set y := Real.sqrt (τ0 / 2) with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 hap
  have hy2 : y ^ 2 = τ0 / 2 := Real.sq_sqrt hap.le
  have hCA := hA.CA0
  -- amplitude bounds on the window
  have hM0 : ∀ τ ∈ Icc (τ0 / 2) (2 * τ0), ‖A τ‖ ≤ CA / y := by
    intro τ hτ
    have hτ' : 0 < τ := lt_of_lt_of_le hap hτ.1
    have h1 := hA.b0 τ hτ'
    have h2 : τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) := by
      refine le_trans (div_le_div_of_nonneg_left (by positivity) hτ' (by linarith)) (le_of_eq (rpow_half_div hτ'))
    have h3 : τ ^ (-1 / 2 : ℝ) ≤ (τ0 / 2) ^ (-1 / 2 : ℝ) := Real.rpow_le_rpow_of_nonpos hap hτ.1 (by norm_num)
    rw [(rp_all hap).2.1] at h3
    calc ‖A τ‖ ≤ CA * τ ^ (1 / 2 : ℝ) / (1 + τ) := h1
      _ = CA * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by ring
      _ ≤ CA * y⁻¹ := mul_le_mul_of_nonneg_left (h2.trans h3) hCA
      _ = CA / y := by ring
  have hL0 : ∀ τ ∈ Icc (τ0 / 2) (2 * τ0), ‖A1 τ‖ ≤ CA / y ^ 3 := by
    intro τ hτ
    have hτ' : 0 < τ := lt_of_lt_of_le hap hτ.1
    have h1 := hA.b1 τ hτ'
    have h2 : τ ^ (-1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-3 / 2 : ℝ) := by
      refine le_trans (div_le_div_of_nonneg_left (by positivity) hτ' (by linarith)) (le_of_eq (rpow_neg_half_div hτ'))
    have h3 : τ ^ (-3 / 2 : ℝ) ≤ (τ0 / 2) ^ (-3 / 2 : ℝ) := Real.rpow_le_rpow_of_nonpos hap hτ.1 (by norm_num)
    rw [(rp_all hap).2.2.1] at h3
    calc ‖A1 τ‖ ≤ CA * τ ^ (-1 / 2 : ℝ) / (1 + τ) := h1
      _ = CA * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by ring
      _ ≤ CA * ((y ^ 3)⁻¹) := mul_le_mul_of_nonneg_left (h2.trans h3) hCA
      _ = CA / y ^ 3 := by ring
  obtain ⟨hbv, hTV⟩ := A_bv hA hap hab (by positivity) hL0
  have hcont : ContinuousOn A (Icc (τ0 / 2) (2 * τ0)) := fun τ hτ =>
    (hA.d1 τ (lt_of_lt_of_le hap hτ.1)).continuousAt.continuousWithinAt
  -- phase data
  have hlam : (0 : ℝ) < 1 / (20 * y ^ 2) := by positivity
  have hvdc := FormalResearch.Analysis.van_der_corput_second (a := τ0 / 2) (b := 2 * τ0) (c := c)
    (lam := 1 / (20 * y ^ 2)) (M := CA / y) hab hc hlam (φ := ϕ) (φ' := fun τ => m τ - m τ0) (φ'' := m1)
    (fun τ hτ => hϕ τ (lt_of_lt_of_le hap hτ.1))
    (fun τ hτ => (hM.d0 τ (lt_of_lt_of_le hap hτ.1)).sub_const _)
    (Or.inl (fun x hx y' hy' hxy => by
      have := hM.strictMonoOn.monotoneOn (show x ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hap hx.1)
        (show y' ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hap hy'.1) hxy
      simp only; linarith))
    (fun τ hτ => by
      have hτ' : 0 < τ := lt_of_lt_of_le hap hτ.1
      rw [abs_of_pos (hM.m1_pos hτ')]
      refine le_trans ?_ (hM.lo τ hτ')
      have h2 : 1 / 2 ≤ τ := by linarith [hτ.1]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : y ^ 2 = τ0 / 2 := hy2
      nlinarith [hτ.2, hτ.1, sq_nonneg τ])
    hcont hbv hM0
  refine hvdc.trans ?_
  have hTV' : (eVariationOn A (Icc (τ0 / 2) (2 * τ0))).toReal ≤ 3 * CA / y := by
    refine hTV.trans ?_
    have : CA / y ^ 3 * (2 * τ0 - τ0 / 2) = 3 * CA / y := by
      have : 2 * τ0 - τ0 / 2 = 3 * y ^ 2 := by rw [hy2]; ring
      rw [this]; field_simp
    exact this.le
  have hsq : Real.sqrt (c * (1 / (20 * y ^ 2))) = Real.sqrt c / (Real.sqrt 20 * y) := by
    rw [show c * (1 / (20 * y ^ 2)) = c / (Real.sqrt 20 * y) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)]; field_simp, Real.sqrt_div hc.le,
      Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hy0.le)]
  rw [hsq]
  have hs20 : Real.sqrt 20 ≤ 9 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 := Real.sqrt_pos.2 hc
  calc 8 * (CA / y + (eVariationOn A (Icc (τ0 / 2) (2 * τ0))).toReal) / (Real.sqrt c / (Real.sqrt 20 * y)) ≤
      8 * (CA / y + 3 * CA / y) / (Real.sqrt c / (Real.sqrt 20 * y)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
    _ = 32 * Real.sqrt 20 * CA / Real.sqrt c := by field_simp; ring
    _ ≤ 144 * CA / Real.sqrt c := by
        apply div_le_div_of_nonneg_right _ hs0.le
        nlinarith

lemma integral_wt_le {b : ℝ} (hb : 1 ≤ b) : ∫ τ in (1 : ℝ)..b, wt τ ≤ 2 := by
  have hwi : IntervalIntegrable wt volume 1 b := (continuousOn_wt (a := 1) (b := b) one_pos).intervalIntegrable_of_Icc hb
  have hgi : IntervalIntegrable (fun τ : ℝ => τ ^ (-3 / 2 : ℝ)) volume 1 b :=
    (ContinuousOn.intervalIntegrable_of_Icc hb (fun τ hτ =>
      (Real.continuousAt_rpow_const τ (-3 / 2 : ℝ) (Or.inl (by linarith [hτ.1]))).continuousWithinAt))
  have h1 : ∫ τ in (1 : ℝ)..b, wt τ ≤ ∫ τ in (1 : ℝ)..b, τ ^ (-3 / 2 : ℝ) := by
    refine intervalIntegral.integral_mono_on hb hwi hgi (fun τ hτ => ?_)
    have hτ' : 0 < τ := by linarith [hτ.1]
    unfold wt
    exact div_le_self (by positivity) (by linarith)
  refine h1.trans ?_
  rw [integral_rpow (Or.inr ⟨by norm_num, by
    rw [Set.mem_uIcc]; intro h; rcases h with h | h <;> linarith [h.1]⟩)]
  have : b ^ (-3 / 2 + 1 : ℝ) ≥ 0 := by positivity
  rw [show (-3 / 2 + 1 : ℝ) = -1 / 2 by norm_num, Real.one_rpow] at *
  nlinarith [this]

lemma ibpH_norm_le {B1 B : ℂ} {d e CA C0 : ℝ} (hCA : 0 ≤ CA) (hC0 : 0 ≤ C0) (hd : 1 / 5 ≤ |d|)
    (h1 : ‖B1‖ ≤ CA) (h0 : ‖B‖ ≤ CA) (he : |e| ≤ C0) :
    ‖(B1 * (d : ℂ) - B * (e : ℂ)) / (d : ℂ) ^ 2‖ ≤ 5 * CA + 25 * CA * C0 := by
  have hu : 0 < |d| := by linarith
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by positivity)]
  have h2 : ‖B1 * (d : ℂ) - B * (e : ℂ)‖ ≤ CA * |d| + CA * C0 := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h0 he (abs_nonneg _) hCA
  refine h2.trans ?_
  have e1 : CA * |d| ≤ 5 * CA * |d| ^ 2 := by
    have : 0 ≤ CA * |d| * (5 * |d| - 1) := mul_nonneg (mul_nonneg hCA hu.le) (by linarith)
    nlinarith
  have e2 : CA * C0 ≤ 25 * CA * C0 * |d| ^ 2 := by
    have h5 : (1 : ℝ) ≤ 25 * |d| ^ 2 := by nlinarith
    have := mul_nonneg hCA hC0
    nlinarith
  linarith

lemma amp_le_CA {CA x : ℝ} (hCA : 0 ≤ CA) (hx : 1 ≤ x) :
    CA * x ^ (1 / 2 : ℝ) / (1 + x) ≤ CA ∧ CA * x ^ (-1 / 2 : ℝ) / (1 + x) ≤ CA := by
  have hx0 : 0 < x := by linarith
  obtain ⟨r1, r2, -, -, -⟩ := rp_all hx0
  have hs1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hs2 : Real.sqrt x ≤ x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  rw [r1, r2]
  constructor
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · have : (Real.sqrt x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left this hCA
    nlinarith

/-- **IBP window `[1, τ₀/2]`** for `τ₀ ≥ 2`: one-sided phase derivative `m τ₀ - m τ ≥ 1/5`. -/
theorem mid_ibp {C0 CA c τ0 : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 2 ≤ c) (hτ0 : 2 ≤ τ0)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) :
    ‖∫ τ in (1 : ℝ)..(τ0 / 2), A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤
      CA * (110 + 1250 * C0 + 3750 * C0 ^ 2) / c := by
  have hC0 := hM.C0nn
  have hCA := hA.CA0
  have hc0 : 0 < c := by linarith
  have hb1 : 1 ≤ τ0 / 2 := by linarith
  -- the phase derivative gap
  have hgap : ∀ τ ∈ Icc (1 : ℝ) (τ0 / 2), (1 / 5 : ℝ) ≤ |m τ - m τ0| := by
    intro τ hτ
    have hτ' : 0 < τ := by linarith [hτ.1]
    have h1 := hM.step (κ := 1 / 2) (by norm_num) (by norm_num) (show 0 < τ0 by linarith)
    have h2 : m τ ≤ m (1 / 2 * τ0) := hM.strictMonoOn.monotoneOn (show τ ∈ Ioi (0 : ℝ) from hτ')
      (show 1 / 2 * τ0 ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith) (by linarith [hτ.2])
    have h3 : (1 / 5 : ℝ) ≤ (1 / 2 : ℝ) * (1 - 1 / 2) * sg τ0 := by
      unfold sg
      rw [show (1 / 2 : ℝ) * (1 - 1 / 2) * (τ0 ^ 2 / (1 + τ0 ^ 2)) = τ0 ^ 2 / (4 * (1 + τ0 ^ 2)) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have : (1 / 5 : ℝ) ≤ m τ0 - m τ := by linarith
    calc (1 / 5 : ℝ) ≤ m τ0 - m τ := this
      _ ≤ |m τ - m τ0| := by rw [abs_sub_comm]; exact le_abs_self _
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 1 / 5 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; norm_num
  have hrb := region_bound hM (γ := γ) (KB := CA) (lam := c) (L := m τ0) (a := 1) (b := τ0 / 2) hγ0 hCA hc0 one_pos hb1
    hϕ (B := A) (B1 := A1) (B2 := A2) (fun τ hτ => hA.d1 τ (by linarith [hτ.1])) (fun τ hτ => hA.d2 τ (by linarith [hτ.1]))
    (hA.c2.mono (fun τ hτ => by simp only [mem_Ioi]; linarith [hτ.1]))
    (fun τ hτ => hA.b0 τ (by linarith [hτ.1])) (fun τ hτ => hA.b1 τ (by linarith [hτ.1]))
    (fun τ hτ => hA.b2 τ (by linarith [hτ.1])) (p := fun _ => (1 / 5 : ℝ)) continuousOn_const
    (fun τ hτ => ⟨by norm_num, hgap τ hτ, by
      have := sg_le_one τ
      have h0 := sg_nonneg τ
      rw [hγ]; nlinarith⟩)
  refine hrb.trans ?_
  have hmem1 : (1 : ℝ) ∈ Icc (1 : ℝ) (τ0 / 2) := ⟨le_rfl, hb1⟩
  have hmem2 : τ0 / 2 ∈ Icc (1 : ℝ) (τ0 / 2) := ⟨hb1, le_rfl⟩
  -- pointwise bounds at an endpoint
  have hA0 : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2), ‖A x‖ ≤ CA := fun x hx =>
    (hA.b0 x (by linarith [hx.1])).trans (amp_le_CA hCA hx.1).1
  have hA1 : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2), ‖A1 x‖ ≤ CA := fun x hx =>
    (hA.b1 x (by linarith [hx.1])).trans (amp_le_CA hCA hx.1).2
  have hm1b : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2), |m1 x| ≤ C0 := fun x hx => by
    have hx0 : 0 < x := by linarith [hx.1]
    refine (hM.abs_m1 hx0).trans ?_
    have : sg x / x ≤ 1 := by
      rw [sg_div x hx0, div_le_one (by positivity)]; nlinarith [sq_nonneg (x - 1)]
    nlinarith
  have hH : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2),
      ‖ibpH A A1 (fun τ => m τ - m τ0) m1 x‖ ≤ 5 * CA + 25 * CA * C0 := fun x hx =>
    ibpH_norm_le hCA hC0 (hgap x hx) (hA1 x hx) (hA0 x hx) (hm1b x hx)
  have hB : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2), ‖A x‖ / |m x - m τ0| ≤ 5 * CA := fun x hx => by
    have hd := hgap x hx
    have hd0 : 0 < |m x - m τ0| := by linarith
    rw [div_le_iff₀ hd0]
    have h5 : 1 ≤ 5 * |m x - m τ0| := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hCA, hA0 x hx, norm_nonneg (A x)]
  have hHd : ∀ x ∈ Icc (1 : ℝ) (τ0 / 2),
      ‖ibpH A A1 (fun τ => m τ - m τ0) m1 x‖ / |m x - m τ0| ≤ 5 * (5 * CA + 25 * CA * C0) := fun x hx => by
    have hd := hgap x hx
    have hd0 : 0 < |m x - m τ0| := by linarith
    rw [div_le_iff₀ hd0]
    have := hH x hx
    have hn := norm_nonneg (ibpH A A1 (fun τ => m τ - m τ0) m1 x)
    have hp : 0 ≤ 5 * CA + 25 * CA * C0 := by positivity
    have h5 : 1 ≤ 5 * |m x - m τ0| := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hp]
  have hint : (∫ τ in (1 : ℝ)..(τ0 / 2), CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / (1 / 5 : ℝ) ^ 2) ≤
      CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * 25 * 2 := by
    have : ∀ τ : ℝ, CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / (1 / 5 : ℝ) ^ 2 =
        (CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * 25) * wt τ := fun τ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]
    have hk : 0 ≤ CA * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * 25 := by positivity
    exact (mul_le_mul_of_nonneg_left (integral_wt_le hb1) hk).trans_eq (by ring)
  have t1 := hB (τ0 / 2) hmem2
  have t1' := hB 1 hmem1
  have t2 := hHd (τ0 / 2) hmem2
  have t2' := hHd 1 hmem1
  refine le_trans (add_le_add (add_le_add (div_le_div_of_nonneg_right (add_le_add t1 t1') hc0.le)
    (div_le_div_of_nonneg_right (add_le_add t2 t2') (by positivity)))
    (div_le_div_of_nonneg_right hint (by positivity))) ?_
  have key : ∀ X : ℝ, 0 ≤ X → X / c ^ 2 ≤ X / c := fun X hX => by
    rw [div_le_div_iff₀ (by positivity) hc0]
    nlinarith [mul_nonneg (mul_nonneg hX hc0.le) (sub_nonneg.2 (by linarith : (1:ℝ) ≤ c))]
  have hγ' : 4 * C0 / γ = 20 * C0 := by rw [hγ]; ring
  have hγ'' : 3 * C0 ^ 2 / γ ^ 2 = 75 * C0 ^ 2 := by rw [hγ]; ring
  rw [hγ', hγ'']
  have kx : (5 * (5 * CA + 25 * CA * C0) + 5 * (5 * CA + 25 * CA * C0)) / c ^ 2 +
      CA * (1 + 20 * C0 + 75 * C0 ^ 2) * 25 * 2 / c ^ 2 ≤
      (100 * CA + 1250 * CA * C0 + 3750 * CA * C0 ^ 2) / c := by
    rw [← add_div]
    refine (key _ (by positivity)).trans (le_of_eq (by congr 1; ring))
  have e : CA * (110 + 1250 * C0 + 3750 * C0 ^ 2) / c =
      (5 * CA + 5 * CA) / c + (100 * CA + 1250 * CA * C0 + 3750 * CA * C0 ^ 2) / c := by ring
  linarith

/-- Tail from `a ≥ 2`: bounded by an absolute constant when `c ≥ 1`. -/
theorem tail_bdd {C0 CA c a L : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 1 ≤ c) (ha : 2 ≤ a)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) (hp : ∀ τ : ℝ, a ≤ τ → (1 / 4 : ℝ) * sg τ ≤ |m τ - L|) :
    ∃ V : ℂ, Tendsto (fun b : ℝ => ∫ τ in a..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 V) ∧
      ‖V‖ ≤ 5 * CA + 25 * (CA * (1 + 4 * C0)) + 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by
  have hC0 := hM.C0nn
  have hCA := hA.CA0
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨V, hV, hb⟩ := tail_est (γ := 1 / 4) hM hA (by norm_num) hc0 ha0 hϕ hp
  refine ⟨V, hV, hb.trans ?_⟩
  have hd : (1 / 5 : ℝ) ≤ |m a - L| := by
    refine le_trans ?_ (hp a le_rfl)
    unfold sg
    rw [show (1 / 4 : ℝ) * (a ^ 2 / (1 + a ^ 2)) = a ^ 2 / (4 * (1 + a ^ 2)) by field_simp]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hd0 : 0 < |m a - L| := by linarith
  set d := |m a - L| with hddef
  have hc1 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  have hc10 : 0 ≤ 1 / c := by positivity
  have hc2 : (1 / c) ^ 2 ≤ 1 := by nlinarith
  obtain ⟨-, -, r3, r9, -⟩ := rp_all ha0
  have hs1 : 1 ≤ Real.sqrt a := by rw [Real.one_le_sqrt]; linarith
  have hr3 : a ^ (-3 / 2 : ℝ) ≤ 1 := by rw [r3]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hs1)
  have hr9 : a ^ (-9 / 2 : ℝ) ≤ 1 := by rw [r9]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hs1)
  have hr30 : 0 ≤ a ^ (-3 / 2 : ℝ) := by positivity
  have hr90 : 0 ≤ a ^ (-9 / 2 : ℝ) := by positivity
  have hw : (2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ) ≤ 1 := by linarith
  have hw0 : 0 ≤ (2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ) := by positivity
  have hu1 := (amp_le_CA hCA (show 1 ≤ a by linarith)).1
  have hu2 := (amp_le_CA (show (0 : ℝ) ≤ 1 by norm_num) (show 1 ≤ a by linarith)).2
  have hu20 : 0 ≤ a ^ (-1 / 2 : ℝ) / (1 + a) := by positivity
  have hu10 : 0 ≤ CA * a ^ (1 / 2 : ℝ) / (1 + a) := by positivity
  rw [one_mul] at hu2
  -- term 1
  have T1 : (1 / c) * (CA * a ^ (1 / 2 : ℝ) / (1 + a) / d) ≤ 5 * CA := by
    have : CA * a ^ (1 / 2 : ℝ) / (1 + a) / d ≤ 5 * CA := by
      rw [div_le_iff₀ hd0]; nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ 5 * d by linarith) hCA]
    calc _ ≤ 1 * (5 * CA) := mul_le_mul hc1 this (by positivity) zero_le_one
      _ = 5 * CA := one_mul _
  -- term 2
  have e2 : C0 / (1 / 4 : ℝ) = 4 * C0 := by ring
  have T2 : (1 / c) ^ 2 * (CA * (1 + C0 / (1 / 4 : ℝ)) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / d / d) ≤
      25 * (CA * (1 + 4 * C0)) := by
    rw [e2]
    have hX : 0 ≤ CA * (1 + 4 * C0) := by positivity
    have : CA * (1 + 4 * C0) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / d / d ≤ 25 * (CA * (1 + 4 * C0)) := by
      rw [div_div, div_le_iff₀ (mul_pos hd0 hd0)]
      have h1 : CA * (1 + 4 * C0) * (a ^ (-1 / 2 : ℝ) / (1 + a)) ≤ CA * (1 + 4 * C0) :=
        mul_le_of_le_one_right hX hu2
      have h2 : (1 : ℝ) ≤ 25 * (d * d) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hX]
    calc _ ≤ 1 * (25 * (CA * (1 + 4 * C0))) := mul_le_mul hc2 this (by positivity) zero_le_one
      _ = _ := one_mul _
  -- term 3
  have e3 : 4 * CA * (1 + 4 * C0 / (1 / 4 : ℝ) + 3 * C0 ^ 2 / (1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ) ^ 2 =
      64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by ring
  have T3 : (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4 : ℝ) + 3 * C0 ^ 2 / (1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ) ^ 2) *
      ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ))) ≤ 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by
    rw [e3]
    have hX : 0 ≤ 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by positivity
    calc _ ≤ 1 * (64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * 1) :=
          mul_le_mul hc2 (mul_le_mul_of_nonneg_left hw hX) (by positivity) zero_le_one
      _ = _ := by ring
  linarith only [T1, T2, T3]

/-- Tail from `a ≥ 2`, with decay: `‖V‖ ≤ K_t / √a` (`c ≥ 1`). -/
theorem tail_small {C0 CA c a L : ℝ} {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ}
    (hM : MData C0 m m1 m2 m3) (hA : AmpBd CA A A1 A2) (hc : 1 ≤ c) (ha : 2 ≤ a)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) (hp : ∀ τ : ℝ, a ≤ τ → (1 / 4 : ℝ) * sg τ ≤ |m τ - L|) :
    ∃ V : ℂ, Tendsto (fun b : ℝ => ∫ τ in a..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 V) ∧
      ‖V‖ ≤ (5 * CA + 25 * (CA * (1 + 4 * C0)) + 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2)) / Real.sqrt a := by
  have hC0 := hM.C0nn
  have hCA := hA.CA0
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨V, hV, hb⟩ := tail_est (γ := 1 / 4) hM hA (by norm_num) hc0 ha0 hϕ hp
  refine ⟨V, hV, hb.trans ?_⟩
  have hd : (1 / 5 : ℝ) ≤ |m a - L| := by
    refine le_trans ?_ (hp a le_rfl)
    unfold sg
    rw [show (1 / 4 : ℝ) * (a ^ 2 / (1 + a ^ 2)) = a ^ 2 / (4 * (1 + a ^ 2)) by field_simp]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hd0 : 0 < |m a - L| := by linarith
  set d := |m a - L| with hddef
  have hc1 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  have hc10 : 0 ≤ 1 / c := by positivity
  have hc2 : (1 / c) ^ 2 ≤ 1 := by nlinarith
  obtain ⟨r1, r2, r3, r9, -⟩ := rp_all ha0
  have hs1 : 1 ≤ Real.sqrt a := by rw [Real.one_le_sqrt]; linarith
  have hs0 : 0 < Real.sqrt a := by linarith
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  set q := (Real.sqrt a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 hs0
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hr3 : a ^ (-3 / 2 : ℝ) ≤ q := by
    rw [r3]
    have h3 : (Real.sqrt a) ≤ (Real.sqrt a) ^ 3 := by
      calc Real.sqrt a = Real.sqrt a * 1 := by ring
        _ ≤ Real.sqrt a * (Real.sqrt a) ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hs1) hs0.le
        _ = (Real.sqrt a) ^ 3 := by ring
    exact inv_anti₀ hs0 h3
  have hr9 : a ^ (-9 / 2 : ℝ) ≤ q := by
    rw [r9]
    have h9 : (Real.sqrt a) ≤ (Real.sqrt a) ^ 9 := by
      calc Real.sqrt a = Real.sqrt a * 1 := by ring
        _ ≤ Real.sqrt a * (Real.sqrt a) ^ 8 := mul_le_mul_of_nonneg_left (one_le_pow₀ hs1) hs0.le
        _ = (Real.sqrt a) ^ 9 := by ring
    exact inv_anti₀ hs0 h9
  have hr30 : 0 ≤ a ^ (-3 / 2 : ℝ) := by positivity
  have hr90 : 0 ≤ a ^ (-9 / 2 : ℝ) := by positivity
  have hw : (2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ) ≤ q := by linarith
  have hw0 : 0 ≤ (2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ) := by positivity
  have hu1 : CA * a ^ (1 / 2 : ℝ) / (1 + a) ≤ CA * q := by
    rw [r1, div_le_iff₀ (by linarith)]
    have : Real.sqrt a ≤ q * (1 + a) := by
      rw [hq]
      rw [← div_eq_inv_mul, le_div_iff₀ hs0]
      nlinarith
    nlinarith only [mul_le_mul_of_nonneg_left this hCA]
  have hu2 : a ^ (-1 / 2 : ℝ) / (1 + a) ≤ q := by
    rw [r2]; exact div_le_self hq0.le (by linarith)
  have hu20 : 0 ≤ a ^ (-1 / 2 : ℝ) / (1 + a) := by positivity
  have hu10 : 0 ≤ CA * a ^ (1 / 2 : ℝ) / (1 + a) := by positivity
  have T1 : (1 / c) * (CA * a ^ (1 / 2 : ℝ) / (1 + a) / d) ≤ 5 * CA * q := by
    have : CA * a ^ (1 / 2 : ℝ) / (1 + a) / d ≤ 5 * CA * q := by
      rw [div_le_iff₀ hd0]
      have hCq : 0 ≤ CA * q := by positivity
      have h5 := mul_le_mul_of_nonneg_left (show 1 ≤ 5 * d by linarith only [hd]) hCq
      linarith only [hu1, h5]
    calc _ ≤ 1 * (5 * CA * q) := mul_le_mul hc1 this (by positivity) zero_le_one
      _ = 5 * CA * q := one_mul _
  have e2 : C0 / (1 / 4 : ℝ) = 4 * C0 := by ring
  have T2 : (1 / c) ^ 2 * (CA * (1 + C0 / (1 / 4 : ℝ)) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / d / d) ≤
      25 * (CA * (1 + 4 * C0)) * q := by
    rw [e2]
    have hX : 0 ≤ CA * (1 + 4 * C0) := by positivity
    have : CA * (1 + 4 * C0) * (a ^ (-1 / 2 : ℝ) / (1 + a)) / d / d ≤ 25 * (CA * (1 + 4 * C0)) * q := by
      rw [div_div, div_le_iff₀ (mul_pos hd0 hd0)]
      have h1 : CA * (1 + 4 * C0) * (a ^ (-1 / 2 : ℝ) / (1 + a)) ≤ CA * (1 + 4 * C0) * q :=
        mul_le_mul_of_nonneg_left hu2 hX
      have h2 : (1 : ℝ) ≤ 25 * (d * d) := by nlinarith only [hd]
      have hXq : 0 ≤ CA * (1 + 4 * C0) * q := by positivity
      calc _ ≤ CA * (1 + 4 * C0) * q := h1
        _ = (CA * (1 + 4 * C0) * q) * 1 := (mul_one _).symm
        _ ≤ (CA * (1 + 4 * C0) * q) * (25 * (d * d)) := mul_le_mul_of_nonneg_left h2 hXq
        _ = 25 * (CA * (1 + 4 * C0)) * q * (d * d) := by ring
    calc _ ≤ 1 * (25 * (CA * (1 + 4 * C0)) * q) := mul_le_mul hc2 this (by positivity) zero_le_one
      _ = _ := one_mul _
  have e3 : 4 * CA * (1 + 4 * C0 / (1 / 4 : ℝ) + 3 * C0 ^ 2 / (1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ) ^ 2 =
      64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by ring
  have T3 : (1 / c) ^ 2 * ((4 * CA * (1 + 4 * C0 / (1 / 4 : ℝ) + 3 * C0 ^ 2 / (1 / 4 : ℝ) ^ 2) / (1 / 4 : ℝ) ^ 2) *
      ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ))) ≤ 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * q := by
    rw [e3]
    have hX : 0 ≤ 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) := by positivity
    calc _ ≤ 1 * (64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) * q) :=
          mul_le_mul hc2 (mul_le_mul_of_nonneg_left hw hX) (by positivity) zero_le_one
      _ = _ := one_mul _
  have hfin : (5 * CA + 25 * (CA * (1 + 4 * C0)) + 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2)) / Real.sqrt a =
      (5 * CA + 25 * (CA * (1 + 4 * C0)) + 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2)) * q := by
    rw [hq, div_eq_mul_inv]
  rw [hfin]
  linarith only [T1, T2, T3]

lemma assemble_split {F : ℝ → ℂ} {e f g : ℝ} {V : ℂ} (he : 0 ≤ e) (hef : e ≤ f) (hfg : f ≤ g)
    (hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable F volume 0 b)
    (hV : Tendsto (fun b : ℝ => ∫ τ in g..b, F τ) atTop (𝓝 V)) :
    Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, F τ) atTop
      (𝓝 ((∫ τ in (0 : ℝ)..e, F τ) + (∫ τ in e..f, F τ) + (∫ τ in f..g, F τ) + V)) := by
  have hg0 : 0 ≤ g := he.trans (hef.trans hfg)
  have hig := hint g hg0
  have hs1 := intervalIntegral_split he (hef.trans hfg) hig
  have hs2 := intervalIntegral_split (a := e) hef hfg
    (hig.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨he, hef.trans hfg⟩)) Set.right_mem_uIcc))
  have hs2' : ∫ τ in e..g, F τ = (∫ τ in e..f, F τ) + ∫ τ in f..g, F τ := hs2
  have htot : (∫ τ in (0 : ℝ)..e, F τ) + (∫ τ in e..f, F τ) + (∫ τ in f..g, F τ) + V =
      (∫ τ in (0 : ℝ)..g, F τ) + V := by
    rw [hs1, hs2']; ring
  rw [htot]
  refine (hV.const_add _).congr' ?_
  filter_upwards [eventually_ge_atTop g] with b hb
  exact (intervalIntegral_split hg0 hb (hint b (hg0.trans hb))).symm

/-- **Bounded `μ₀`, large `τ₀`.** For `τ₀ ≥ 1`, `c ≥ 2`: the improper integral exists and is bounded by an absolute constant. -/
theorem bdd_large (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {c τ0 : ℝ},
      MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 2 ≤ c → 1 ≤ τ0 →
      (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) →
      ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
        ‖I‖ ≤ Cl := by
  set KI : ℝ := CA * (110 + 1250 * C0 + 3750 * C0 ^ 2) with hKI
  set Kt : ℝ := 5 * CA + 25 * (CA * (1 + 4 * C0)) + 64 * CA * (1 + 16 * C0 + 48 * C0 ^ 2) with hKt
  have hKI0 : 0 ≤ KI := by rw [hKI]; positivity
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  refine ⟨2 / 3 * CA + KI + 144 * CA + Kt, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ c τ0 hM hA hc hτ0 hϕ
  have hc0 : 0 < c := by linarith
  have hτp : 0 < τ0 := by linarith
  have hϕc : ContinuousOn ϕ (Ioi 0) := fun τ hτ => (hϕ τ hτ).continuousAt.continuousWithinAt
  have hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun τ => A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) volume 0 b :=
    fun b hb => intInt_BE hb hA.CA0 (fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt) hϕc hA.b0
  obtain ⟨V, hV, hVb⟩ := tail_bdd (c := c) (a := 2 * τ0) hM hA (by linarith) (by linarith) hϕ
    (fun τ hτ => hp_two hM hτp hτ)
  -- the starting point `e ≤ 1` and the IBP window
  obtain ⟨e, he0, he1, hef, hibp⟩ : ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 ∧ e ≤ τ0 / 2 ∧
      ‖∫ τ in e..(τ0 / 2), A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ KI := by
    by_cases h2 : τ0 < 2
    · refine ⟨τ0 / 2, by linarith, by linarith, le_rfl, ?_⟩
      rw [intervalIntegral.integral_same, norm_zero]; exact hKI0
    · push_neg at h2
      refine ⟨1, zero_le_one, le_rfl, by linarith, ?_⟩
      have := mid_ibp hM hA hc h2 hϕ
      refine this.trans ?_
      rw [hKI, div_le_iff₀ hc0]
      have : 0 ≤ CA * (110 + 1250 * C0 + 3750 * C0 ^ 2) := by positivity
      nlinarith
  refine ⟨_, assemble_split he0 hef (show τ0 / 2 ≤ 2 * τ0 by linarith) hint hV, ?_⟩
  have hcr := crude_left (c := c) hA he0 hϕc
  have hcr' : ‖∫ τ in (0 : ℝ)..e, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ 2 / 3 * CA := by
    refine hcr.trans ?_
    have : e ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one he0 he1 (by norm_num)
    nlinarith [mul_nonneg hCA (show (0 : ℝ) ≤ 2 / 3 by norm_num)]
  have hmid := vdc_mid (c := c) hM hA hc0 hτ0 hϕ
  have hmid' : ‖∫ τ in (τ0 / 2)..(2 * τ0), A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤ 144 * CA := by
    refine hmid.trans ?_
    have hs : 1 ≤ Real.sqrt c := by rw [Real.one_le_sqrt]; linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hCA (show (0 : ℝ) ≤ 144 by norm_num)]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hcr' hibp)) hmid')) hVb)

/-- **`ct:cfu` (2), bounded range `1 ≤ μ₀ < M₀`** (`μ₀ = c · min(1, τ₀³)`): for every `M₀` there is `K_b` such that for `c ≥ 2` the
improper integral `I = ∫₀^∞ A_ε e^{-icΦ}` exists and `|K_ε| = √(πc/12) |Re I| ≤ K_b`.  Together with `ct_cfu_outer_tau` this
covers `μ₀ ≥ 1`. -/
theorem ct_cfu_outer_bdd {ε : ℝ} (hε : ε = -1 ∨ ε = 1) (M0 : ℝ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ {c τ0 : ℝ}, 2 ≤ c → 0 < τ0 → 1 ≤ c * min 1 (τ0 ^ 3) → c * min 1 (τ0 ^ 3) < M0 →
      ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
          outerAmp ε c τ * Complex.exp (Complex.I * c * (phaseP τ0 τ : ℂ))) atTop (𝓝 I) ∧
        Real.sqrt (π * c / 12) * |I.re| ≤ Kb := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨CA, hCA, hAmp⟩ := outerAmp_ampBd hε
  obtain ⟨Cs, hCs, Hs⟩ := bdd_small_final C0 CA hC0 hCA
  obtain ⟨Cl, hCl, Hl⟩ := bdd_large C0 CA hC0 hCA
  have hpi := Real.pi_pos
  have hM0 : 0 ≤ Real.sqrt M0 := Real.sqrt_nonneg _
  refine ⟨Real.sqrt (π / 12) * (Cs * (1 + Real.sqrt M0) + Real.sqrt M0 * Cl), by positivity, ?_⟩
  intro c τ0 hc2 hτ0 hμ1 hμ2
  have hc : 0 < c := by linarith
  obtain ⟨A1, A2, hA⟩ := hAmp c hc2
  have hsc : Real.sqrt (π * c / 12) = Real.sqrt (π / 12) * Real.sqrt c := by
    rw [show π * c / 12 = π / 12 * c by ring, Real.sqrt_mul (by positivity)]
  have hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt (phaseP τ0) (hankelEdgeM τ - hankelEdgeM τ0) τ :=
    fun τ hτ => hasDerivAt_phaseP τ0 hτ
  -- reduce to `√c ‖I‖ ≤ K'`
  have red : ∀ (I : ℂ) (K' : ℝ), Real.sqrt c * ‖I‖ ≤ K' →
      Real.sqrt (π * c / 12) * |I.re| ≤ Real.sqrt (π / 12) * K' := by
    intro I K' h
    rw [hsc]
    have h1 : |I.re| ≤ ‖I‖ := Complex.abs_re_le_norm I
    have h2 : Real.sqrt c * |I.re| ≤ K' :=
      (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)).trans h
    calc Real.sqrt (π / 12) * Real.sqrt c * |I.re| = Real.sqrt (π / 12) * (Real.sqrt c * |I.re|) := by ring
      _ ≤ Real.sqrt (π / 12) * K' := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
  have hmono : ∀ K' : ℝ, K' ≤ Cs * (1 + Real.sqrt M0) + Real.sqrt M0 * Cl →
      Real.sqrt (π / 12) * K' ≤ Real.sqrt (π / 12) * (Cs * (1 + Real.sqrt M0) + Real.sqrt M0 * Cl) :=
    fun K' h => mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
  by_cases h1 : τ0 ≤ 1
  · have hmin : min 1 (τ0 ^ 3) = τ0 ^ 3 := min_eq_right (pow_le_one₀ hτ0.le h1)
    rw [hmin] at hμ1 hμ2
    obtain ⟨I, hI, hb⟩ := Hs hMd hA hc hτ0 h1 hμ1 hϕ
    refine ⟨I, hI, (red I _ hb).trans (hmono _ ?_)⟩
    have hsq : Real.sqrt (c * τ0 ^ 3) ≤ Real.sqrt M0 := Real.sqrt_le_sqrt hμ2.le
    nlinarith [mul_nonneg hM0 hCl]
  · push_neg at h1
    have hmin : min 1 (τ0 ^ 3) = 1 := min_eq_left (one_le_pow₀ h1.le)
    rw [hmin, mul_one] at hμ2
    obtain ⟨I, hI, hb⟩ := Hl hMd hA hc2 h1.le hϕ
    refine ⟨I, hI, (red I _ (show Real.sqrt c * ‖I‖ ≤ Real.sqrt M0 * Cl from
      mul_le_mul (Real.sqrt_le_sqrt hμ2.le) hb (norm_nonneg _) hM0)).trans (hmono _ ?_)⟩
    nlinarith [mul_nonneg hCs (Real.sqrt_nonneg M0), mul_nonneg hM0 hCl]

/-- info: 'FormalResearch.SignUncertainty.CtOsc.mid_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mid_ibp

/-- info: 'FormalResearch.SignUncertainty.CtOsc.bdd_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bdd_large

/-- info: 'FormalResearch.SignUncertainty.CtOsc.bdd_small_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bdd_small_final

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ct_cfu_outer_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_cfu_outer_bdd

/-- info: 'FormalResearch.SignUncertainty.CtOsc.bdd_tiny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bdd_tiny

/-- info: 'FormalResearch.SignUncertainty.CtOsc.tail_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_small

end FormalResearch.SignUncertainty.CtOsc

module

public import FormalResearch.SignUncertainty.CtOscChart
public import FormalResearch.SignUncertainty.CtOscInv
public import FormalResearch.SignUncertainty.CtMorseExpansion
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Stationary phase with a variable phase

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 1 (stationary-phase core: Morse
coordinate, pulled-back amplitude `B(s) = Ã(t(s)) t'(s)`, `ct:morse-expansion` with `r = 1`).  **Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace FormalResearch.SignUncertainty.CtOsc

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open scoped Real

noncomputable def KG (Ks m0 : ℝ) : ℝ := m0⁻¹ + Ks * m0⁻¹ ^ 2 + 2 * (Ks ^ 2 * m0⁻¹ ^ 3)
noncomputable def Kt (Ks m0 : ℝ) : ℝ := 1 + KG Ks m0 + KG Ks m0 * KG Ks m0
/-- Constant of the pulled-back amplitude: `‖B‖_{C²} ≤ KBc · ‖A‖_{C²}`. -/
noncomputable def KBc (Ks m0 : ℝ) : ℝ := 4 * KG Ks m0 * (Kt Ks m0 * Kt Ks m0 + 2 * Kt Ks m0 + 1)

section
variable {s sd sd1 sd2 : ℝ → ℝ} {Ks m0 : ℝ}

/-- The pulled-back amplitude `B = (Ã/s') ∘ s⁻¹` is `D2` on `(-m₀, m₀)`. -/
lemma Chart.D2_B (h : Chart s sd sd1 sd2 Ks m0) {A A1 A2 : ℝ → ℂ} {KA : ℝ}
    (hA : D2 (Ioo (-1 : ℝ) 1) A A1 A2 KA) :
    ∃ tinv : ℝ → ℝ, (∀ X ∈ Ioo (-m0) m0, tinv X ∈ Ioo (-1 : ℝ) 1 ∧ s (tinv X) = X) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, s t ∈ Ioo (-m0) m0 → tinv (s t) = t) ∧
      ∃ B B1 B2 : ℝ → ℂ, D2 (Ioo (-m0) m0) B B1 B2 (KBc Ks m0 * KA) ∧
        ∀ X ∈ Ioo (-m0) m0, B X = ((sd (tinv X))⁻¹ : ℝ) • A (tinv X) := by
  obtain ⟨tinv, h1, h2, h3⟩ := h.exists_inv
  have hG : D2 (Ioo (-1 : ℝ) 1) (fun y => (sd y)⁻¹) (fun y => -sd1 y * ((sd y)⁻¹) ^ 2)
      (fun y => -sd2 y * ((sd y)⁻¹) ^ 2 + 2 * (sd1 y) ^ 2 * ((sd y)⁻¹) ^ 3) (KG Ks m0) :=
    h.D.inv h.m0pos h.lo
  have hKG : 0 ≤ KG Ks m0 := hG.K0
  have hF := hG.smul hA
  have hcont_t : ContinuousOn tinv (Ioo (-m0) m0) := fun X hX => (h3 X hX).continuousAt.continuousWithinAt
  have hmaps : ∀ X ∈ Ioo (-m0) m0, tinv X ∈ Ioo (-1 : ℝ) 1 := fun X hX => (h1 X hX).1
  have ht : D2 (Ioo (-m0) m0) tinv (fun X => (sd (tinv X))⁻¹)
      (fun X => (sd (tinv X))⁻¹ * (-sd1 (tinv X) * ((sd (tinv X))⁻¹) ^ 2)) (Kt Ks m0) := {
    d1 X hX := h3 X hX
    d2 X hX := by
      have := (hG.d1 (tinv X) (hmaps X hX)).scomp X (h3 X hX)
      simpa only [smul_eq_mul, Function.comp_def] using this
    c2 := by
      have a1 : ContinuousOn (fun X => (sd (tinv X))⁻¹) (Ioo (-m0) m0) := hG.cont0.comp hcont_t hmaps
      have a2 : ContinuousOn (fun X => -sd1 (tinv X) * ((sd (tinv X))⁻¹) ^ 2) (Ioo (-m0) m0) :=
        hG.cont1.comp hcont_t hmaps
      exact a1.mul a2
    K0 := by have := hKG; unfold Kt; positivity
    b0 X hX := by
      have := (h1 X hX).1
      rw [Real.norm_eq_abs]
      have : |tinv X| ≤ 1 := (abs_lt.mpr ⟨(h1 X hX).1.1, (h1 X hX).1.2⟩).le
      unfold Kt; nlinarith [mul_nonneg hKG hKG]
    b1 X hX := by
      have := hG.b0 (tinv X) (hmaps X hX)
      unfold Kt; simp only [Real.norm_eq_abs] at this ⊢
      nlinarith [mul_nonneg hKG hKG]
    b2 X hX := by
      have e1 := hG.b0 (tinv X) (hmaps X hX)
      have e2 := hG.b1 (tinv X) (hmaps X hX)
      simp only [Real.norm_eq_abs] at e1 e2 ⊢
      rw [abs_mul]
      have := mul_le_mul e1 e2 (abs_nonneg _) hKG
      unfold Kt; nlinarith [mul_nonneg hKG hKG] }
  have hB := hF.comp ht hmaps
  refine ⟨tinv, h1, h2, _, _, _, hB.mono (le_of_eq ?_), fun X hX => rfl⟩
  unfold KBc
  ring

lemma exists_cutoff {a : ℝ} (ha : 0 < a) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞' χ ∧ tsupport χ ⊆ Ioo (-a) a ∧ (∀ x, |x| ≤ a / 2 → χ x = 1) ∧
      ∀ x, a ≤ |x| → χ x = 0 := by
  let f : ContDiffBump (0 : ℝ) := ⟨a / 2, 3 * a / 4, by positivity, by linarith⟩
  refine ⟨⇑f, f.contDiff, ?_, ?_, ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have : |x| ≤ 3 * a / 4 := hx
    exact abs_lt.mp (by linarith)
  · intro x hx
    exact f.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)
  · intro x hx
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero]
    intro h
    have : |x| ≤ 3 * a / 4 := h
    linarith

/-- Support facts for the substitution `x = s(t)`. -/
lemma Chart.subst (h : Chart s sd sd1 sd2 Ks m0) {tinv : ℝ → ℝ}
    (h1 : ∀ X ∈ Ioo (-m0) m0, tinv X ∈ Ioo (-1 : ℝ) 1 ∧ s (tinv X) = X) (g : ℝ → ℂ) :
    ∫ X in Ioo (-m0) m0, g X =
      ∫ t in Ioo (-1 : ℝ) 1 ∩ s ⁻¹' Ioo (-m0) m0, |sd t| • g (s t) := by
  have hS : MeasurableSet (Ioo (-1 : ℝ) 1 ∩ s ⁻¹' Ioo (-m0) m0) :=
    (h.cont_s.isOpen_inter_preimage isOpen_Ioo isOpen_Ioo).measurableSet
  have himg : s '' (Ioo (-1 : ℝ) 1 ∩ s ⁻¹' Ioo (-m0) m0) = Ioo (-m0) m0 := by
    ext X
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht.2
    · intro hX
      exact ⟨tinv X, ⟨(h1 X hX).1, by rw [mem_preimage, (h1 X hX).2]; exact hX⟩, (h1 X hX).2⟩
  have := integral_image_eq_integral_abs_deriv_smul hS (fun t ht => (h.hs t ht.1).hasDerivWithinAt)
    (h.strictMonoOn.injOn.mono inter_subset_left) g
  rwa [himg] at this

lemma KBc_nonneg (hm0 : 0 < m0) (hKs : 0 ≤ Ks) : 0 ≤ KBc Ks m0 := by
  have : 0 < m0⁻¹ := inv_pos.mpr hm0
  unfold KBc Kt KG
  positivity

/-- Stationary phase for the Morse chart: `∫ A e^{iλ s²/2} = e^{iπ/4} √(2π/λ) A(0)/s'(0) + O(‖A‖_{C²} λ^{-3/2})`. -/
theorem stat_chart (m0 Ks : ℝ) (hm0 : 0 < m0) (hKs : 0 ≤ Ks) :
    ∃ θ K : ℝ, 0 < θ ∧ θ < 1 ∧ 0 ≤ K ∧
      ∀ {s sd sd1 sd2 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {KA lam : ℝ},
        Chart s sd sd1 sd2 Ks m0 → D2 (Ioo (-1 : ℝ) 1) A A1 A2 KA → (∀ t, θ ≤ |t| → A t = 0) → 1 ≤ lam →
        ‖(∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((s t : ℝ) : ℂ) ^ 2 / 2)) -
            Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / lam) : ℝ) : ℂ) *
              (((sd 0)⁻¹ : ℝ) • A 0)‖ ≤ K * KA / (lam * Real.sqrt lam) := by
  obtain ⟨χ, hχ, hχs, hχ1, hχ0⟩ := exists_cutoff hm0
  have hχn : ∀ᶠ x in 𝓝 (0 : ℝ), χ x = 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < m0 / 2)] with x hx
    exact hχ1 x (by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx; exact hx.le)
  obtain ⟨C, hC⟩ := CtMorse.morse_expansion hm0 hχ hχs hχn (r := 1) le_rfl
  have hKB := KBc_nonneg hm0 hKs
  have hθ0 : 0 < min (1 / 2 : ℝ) (m0 / (4 * (Ks + 1))) := lt_min (by norm_num) (by positivity)
  refine ⟨min (1 / 2) (m0 / (4 * (Ks + 1))), Real.sqrt (2 * π) * |C| * KBc Ks m0, hθ0,
    lt_of_le_of_lt (min_le_left _ _) (by norm_num), by positivity, ?_⟩
  intro s sd sd1 sd2 A A1 A2 KA lam hch hA hAsupp hlam
  set θ := min (1 / 2 : ℝ) (m0 / (4 * (Ks + 1))) with hθdef
  have hθ1 : θ * (4 * (Ks + 1)) ≤ m0 := by
    have := min_le_right (1 / 2 : ℝ) (m0 / (4 * (Ks + 1)))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hKθ : Ks * θ ≤ m0 / 4 := by nlinarith
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hKA : 0 ≤ KA := hA.K0
  obtain ⟨tinv, h1, h2, B, B1, B2, hD, hBeq⟩ := hch.D2_B hA
  have hcd : ContDiffOn ℝ ((2 * 1 : ℕ) : WithTop ℕ∞) B (Ioo (-m0) m0) := by
    simpa using hD.contDiffOn isOpen_Ioo
  have hbd : ∀ j ≤ 2 * 1, ∀ x ∈ Ioo (-m0) m0, ‖iteratedDeriv j B x‖ ≤ KBc Ks m0 * KA :=
    fun j hj x hx => hD.iteratedDeriv_le isOpen_Ioo hx j (by omega)
  obtain ⟨R, hR1, hR2⟩ := hC (σ := 1) (μ := lam) (B := fun x => B x) (M := KBc Ks m0 * KA) (Or.inl rfl) hlam hcd hbd
  -- the substitution
  have hclaim : ∫ x : ℝ, (χ x : ℂ) * B x * Complex.exp (Complex.I * ((1 * lam : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2) =
      ∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((s t : ℝ) : ℂ) ^ 2 / 2) := by
    set g : ℝ → ℂ := fun x => (χ x : ℂ) * B x * Complex.exp (Complex.I * ((1 * lam : ℝ) : ℂ) * (x : ℂ) ^ 2 / 2) with hg
    have e1 : ∫ x in Ioo (-m0) m0, g x = ∫ x, g x := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : m0 ≤ |x| := by
        by_contra hc
        exact hx (abs_lt.mp (not_le.mp hc) |> fun h => ⟨h.1, h.2⟩)
      simp [hg, hχ0 x this]
    rw [← e1, hch.subst h1 g]
    have hS : MeasurableSet (Ioo (-1 : ℝ) 1 ∩ s ⁻¹' Ioo (-m0) m0) :=
      (hch.cont_s.isOpen_inter_preimage isOpen_Ioo isOpen_Ioo).measurableSet
    have hpt : ∀ t ∈ Ioo (-1 : ℝ) 1 ∩ s ⁻¹' Ioo (-m0) m0,
        |sd t| • g (s t) = A t * Complex.exp (Complex.I * (lam : ℂ) * ((s t : ℝ) : ℂ) ^ 2 / 2) := by
      intro t ht
      have hsdpos : 0 < sd t := lt_of_lt_of_le hch.m0pos (hch.lo t ht.1)
      have hBt : B (s t) = ((sd t)⁻¹ : ℝ) • A t := by
        rw [hBeq (s t) ht.2, h2 t ht.1 ht.2]
      by_cases hA0 : A t = 0
      · simp [hg, hBt, hA0]
      · have hθt : |t| < θ := by
          by_contra hc
          exact hA0 (hAsupp t (not_lt.mp hc))
        have hst : |s t| ≤ m0 / 4 := by
          refine (hch.abs_s_le ht.1).trans ?_
          nlinarith [abs_nonneg t, hKs]
        have hχst : χ (s t) = 1 := hχ1 _ (by linarith)
        have hne : ((sd t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsdpos.ne'
        simp only [hg, hBt, hχst, Complex.real_smul, abs_of_pos hsdpos]
        push_cast
        field_simp
    rw [setIntegral_congr_fun hS hpt]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    have : θ ≤ |t| := by
      by_contra hc
      have hlt : |t| < θ := not_le.mp hc
      have htI : t ∈ Ioo (-1 : ℝ) 1 := by
        have : |t| < 1 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (by norm_num))
        exact abs_lt.mp this
      refine ht ⟨htI, ?_⟩
      have := (hch.abs_s_le htI)
      have h3 : |s t| < m0 := by nlinarith [abs_nonneg t, hKs]
      exact abs_lt.mp h3
    simp [hAsupp t this]
  have h0 : tinv 0 = 0 := by
    have := h2 0 (by norm_num) (by rw [hch.s0]; exact ⟨by linarith, hm0⟩)
    simpa [hch.s0] using this
  have hB0 : B 0 = ((sd 0)⁻¹ : ℝ) • A 0 := by
    rw [hBeq 0 ⟨by linarith, hm0⟩, h0]
  rw [← hclaim, hR1]
  simp only [Finset.sum_range_one, mul_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_zero, mul_one, Complex.ofReal_one, one_mul, hB0]
  have e : ∀ E S X : ℂ, E * S * (X + R) - E * S * X = E * S * R := fun E S X => by ring
  rw [e, norm_mul, norm_mul]
  have hE : ‖Complex.exp ((π : ℂ) / 4 * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hS : ‖((Real.sqrt (2 * π / lam) : ℝ) : ℂ)‖ = Real.sqrt (2 * π) / Real.sqrt lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (by positivity)]
  have hRb : ‖R‖ ≤ |C| * (KBc Ks m0 * KA) / lam := by
    have := hR2
    rw [pow_one] at this
    refine this.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hKB hKA)) hlam0.le
  rw [hE, hS, one_mul]
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  calc Real.sqrt (2 * π) / Real.sqrt lam * ‖R‖
      ≤ Real.sqrt (2 * π) / Real.sqrt lam * (|C| * (KBc Ks m0 * KA) / lam) :=
        mul_le_mul_of_nonneg_left hRb (by positivity)
    _ = Real.sqrt (2 * π) * |C| * KBc Ks m0 * KA / (lam * Real.sqrt lam) := by
        field_simp

end

section Final

/-- Stationary phase for a phase with `φ(0) = φ'(0) = 0`, `φ'' ≥ c₁`, and `φ'', φ''', φ⁗` bounded by `C` on `(-1,1)`
(**Proved**).  For amplitudes `A` supported in `|t| < θ` with `‖A‖_{C²} ≤ KA`:
`∫ A e^{iλφ} = e^{iπ/4} √(2π/(λφ''(0))) A(0) + O(KA λ^{-3/2})`, `θ, K` depending only on `(c₁, C)`. -/
theorem stat_phase (c1 C : ℝ) (hc1 : 0 < c1) :
    ∃ θ K : ℝ, 0 < θ ∧ θ < 1 ∧ 0 ≤ K ∧
      ∀ {φ φ1 f f1 f2 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {KA lam : ℝ},
        Phase c1 C φ φ1 f f1 f2 → D2 (Ioo (-1 : ℝ) 1) A A1 A2 KA → (∀ t, θ ≤ |t| → A t = 0) → 1 ≤ lam →
        ‖(∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((φ t : ℝ) : ℂ))) -
            Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (lam * f 0)) : ℝ) : ℂ) * A 0‖
          ≤ K * KA / (lam * Real.sqrt lam) := by
  by_cases hC : 0 < C
  · have hKq : 0 < Kq' C := by unfold Kq'; positivity
    have hm0 : 0 < c1 / Real.sqrt (Kq' C) := div_pos hc1 (Real.sqrt_pos.mpr hKq)
    have hKs : 0 ≤ Ksd c1 C := by
      have : 0 < Real.sqrt c1 := Real.sqrt_pos.mpr hc1
      unfold Ksd Kw Ku Kq'
      positivity
    obtain ⟨θ, K, hθ0, hθ1, hK0, H⟩ := stat_chart (c1 / Real.sqrt (Kq' C)) (Ksd c1 C) hm0 hKs
    refine ⟨θ, K, hθ0, hθ1, hK0, ?_⟩
    intro φ φ1 f f1 f2 A A1 A2 KA lam hph hA hsupp hlam
    obtain ⟨sd, sd1, sd2, hD, hsd⟩ := hph.D2_sd hc1
    have hch : Chart (sfun f) sd sd1 sd2 (Ksd c1 C) (c1 / Real.sqrt (Kq' C)) :=
      { D := hD
        hs := fun y hy => by rw [hsd]; exact hph.hasDerivAt_s hc1 hy
        m0pos := hm0
        lo := fun y hy => by rw [hsd]; exact hph.sd_ge hc1 hy
        s0 := Phase.s_zero f }
    have key := H hch hA hsupp hlam
    have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
    have hf0 : 0 < f 0 := lt_of_lt_of_le hc1 (hph.lo 0 (by norm_num))
    have hint : (∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((sfun f t : ℝ) : ℂ) ^ 2 / 2)) =
        ∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((φ t : ℝ) : ℂ)) := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      by_cases ht : t ∈ Ioo (-1 : ℝ) 1
      · simp only
        have := hph.s_sq hc1 ht
        have h2 : ((sfun f t : ℝ) : ℂ) ^ 2 / 2 = ((φ t : ℝ) : ℂ) := by
          rw [← this]; push_cast; ring
        have e : Complex.I * (lam : ℂ) * ((sfun f t : ℝ) : ℂ) ^ 2 / 2 = Complex.I * (lam : ℂ) * ((φ t : ℝ) : ℂ) := by
          rw [← h2]; ring
        rw [e]
      · have : θ ≤ |t| := by
          by_contra hc
          have hlt : |t| < θ := not_le.mp hc
          exact ht (abs_lt.mp (hlt.trans hθ1))
        simp [hsupp t this]
    rw [hint] at key
    have hsd0 : sd 0 = Real.sqrt (f 0) := by rw [hsd]; exact hph.sd_zero hc1
    have hsq : Real.sqrt (2 * π / lam) * (Real.sqrt (f 0))⁻¹ = Real.sqrt (2 * π / (lam * f 0)) := by
      rw [← div_div, Real.sqrt_div' _ hf0.le]
      exact (div_eq_mul_inv _ _).symm
    have e : Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / lam) : ℝ) : ℂ) * ((sd 0)⁻¹ • A 0) =
        Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (lam * f 0)) : ℝ) : ℂ) * A 0 := by
      rw [hsd0, Complex.real_smul, ← hsq]
      push_cast
      ring
    rw [e] at key
    exact key
  · refine ⟨1 / 2, 0, by norm_num, by norm_num, le_rfl, ?_⟩
    intro φ φ1 f f1 f2 A A1 A2 KA lam hph
    exact absurd (lt_of_lt_of_le hc1 (le_trans (hph.lo 0 (by norm_num)) ((le_abs_self _).trans (hph.b0 0 (by norm_num))))) hC

end Final

/-- info: 'FormalResearch.SignUncertainty.CtOsc.stat_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stat_phase

/-- info: 'FormalResearch.SignUncertainty.CtOsc.stat_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stat_chart

end FormalResearch.SignUncertainty.CtOsc

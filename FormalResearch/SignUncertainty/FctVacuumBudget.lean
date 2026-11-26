/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumPaired
public import FormalResearch.SignUncertainty.FctPhysicalBudget

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

/-! ### Generic power-law integrals -/

/-- `∫_b^∞ u^{-r} = b^{1-r}/(r-1)` for `r > 1`, `b > 0`. -/
lemma integral_Ioi_rpow_neg {b r : ℝ} (hb : 0 < b) (hr : 1 < r) :
    IntegrableOn (fun u : ℝ => u ^ (-r)) (Ioi b) ∧ ∫ u in Ioi b, u ^ (-r) = b ^ (1 - r) / (r - 1) := by
  refine ⟨integrableOn_Ioi_rpow_of_lt (by linarith) hb, ?_⟩
  rw [integral_Ioi_rpow_of_lt (by linarith) hb]
  rw [show -r + 1 = 1 - r by ring, show (1 - r) = -(r - 1) by ring, neg_div, div_neg]
  simp

/-- A measurable function with `|f| ≤ M u^{-r}` on `(b, ∞)` is integrable there with `∫ |f| ≤ M b^{1-r}/(r-1)`. -/
lemma integrableOn_Ioi_of_abs_le {b r M : ℝ} (hb : 0 < b) (hr : 1 < r) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi b))) (h : ∀ u ∈ Ioi b, |f u| ≤ M * u ^ (-r)) :
    IntegrableOn f (Ioi b) ∧ ∫ u in Ioi b, |f u| ≤ M * (b ^ (1 - r) / (r - 1)) := by
  obtain ⟨hi, hv⟩ := integral_Ioi_rpow_neg hb hr
  have hg : IntegrableOn (fun u : ℝ => M * u ^ (-r)) (Ioi b) := hi.const_mul M
  have hint : IntegrableOn f (Ioi b) := by
    refine Integrable.mono' hg hf ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa [Real.norm_eq_abs] using h u hu
  refine ⟨hint, ?_⟩
  calc ∫ u in Ioi b, |f u| ≤ ∫ u in Ioi b, M * u ^ (-r) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hg
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using h u hu)
    _ = M * (b ^ (1 - r) / (r - 1)) := by rw [integral_const_mul, hv]


/-! ### The data of the vacuum integral at one `(ε, c)` -/

/-- `D_*(u) = I_osc^{DH₀}(u)(1 + Δ_curv(τ₀(u))) - I_fl(u) = P(u) - I_fl(u)` (`fct:comp-D` (2)). -/
noncomputable def vacD (P : ℝ → ℝ) (u : ℝ) : ℝ := P u - uctIfl u

/-- The hypotheses of the vacuum integral at one `(ε, c)`, with `a = c^{-1/12}` (so `τ₁ = a³`, `c^{-1} = a^{12}`, `δ_L ≍ a⁶`,
`|L₁| ≲ a⁸`, `|s| = |θ₁^ε|/c ≲ a^{12}`, `|α| ≲ a⁸`, `κ = (5π²/96) c^{-2} ≤ a^{24}`), one constant `K` dominating all of them.
`Φ(u) = φ_kill(i τ₀(u); a)`.  Every field is a named display of `fct:comp-D` / `fct:phikill`, or a size fact, as annotated. -/
structure VacHyp (K a0 a1 a δ s L1 α κ Cfl I0 : ℝ) (P : ℝ → ℝ) (Φ : ℝ → ℂ) : Prop where
  -- constants
  hK : 1 ≤ K
  ha0 : 0 < a0
  hKa0 : a0⁻¹ ≤ K
  hKa1 : a1 ≤ K
  hKf : |uctAlphaFl| ≤ K
  -- scales (`fct:physical-budget` size facts)
  ha : 0 < a
  ha1 : a ≤ 1
  hδ0 : a0 * a ^ 6 ≤ δ
  hδ1 : δ ≤ a1 * a ^ 6
  hs : |s| ≤ K * a ^ 12
  hL1 : |L1| ≤ K * a ^ 8
  hα : |α| ≤ K * a ^ 8
  hκ0 : 0 ≤ κ
  hκa : κ ≤ a ^ 24
  -- smallness for large `c`
  hA : |L1 - s| ≤ δ / 4
  hs10 : |s| ≤ δ / 10
  hL1K : |L1| * K ≤ δ / 2
  h31 : 31 / 10 * δ ≤ 1
  hκδ : κ * (δ ^ 3)⁻¹ ≤ 1
  -- regularity and positivity of the datum
  hPm : Measurable P
  hΦm : Measurable Φ
  hP0 : ∀ u, 0 < u → 0 ≤ P u
  -- `fct:phikill` (1): `|φ_kill(it; a)| ≤ C min((t/a)^8, 1)`, `|Im φ_kill(it; a)| ≤ C min((t/a)^9, 1)`, `τ₀(u)² ≲ u`
  hΦre : ∀ u, 0 < u → |(Φ u).re| ≤ K * min 1 ((u / a ^ 2) ^ 4)
  hΦim : ∀ u, 0 < u → (Φ u).im ^ 2 ≤ K * min 1 ((u / a ^ 2) ^ 4)
  -- `(fct:Dstar-inner)` and the pointwise bounds of `fct:physical-budget` (a), (d)
  hDin : ∀ u ∈ Icc δ (31 / 10 * δ), |vacD P u| ≤ K * Real.sqrt u
  hDmid : ∀ u ∈ Icc (3 * δ) (144 * δ), |vacD P u| ≤ K * a ^ 6 * u ^ (-(3 / 2 : ℝ))
  hDfar : ∀ u, 144 * δ ≤ u → |vacD P u| ≤ K * u ^ (-(1 / 2 : ℝ))
  -- `(fct:cos-pen)` and `∫_0^{3δ} D_*`
  hDint : IntegrableOn (vacD P) (Ioi 0)
  hCfl : Cfl ≤ 0
  hcos : |(∫ u in Ioi 0, vacD P u) - Cfl| ≤ K * a ^ 9
  hin : |∫ u in Ioc 0 (3 * δ), vacD P u| ≤ K * (a ^ 9 + |α| * a ^ 3)
  -- `(fct:bump-1L)`, `(fct:bump-2L)`
  hI0 : |I0| ≤ K
  hb1 : |(∫ u in Ioi (3 * δ), vacD P u / u) - I0| ≤ K * (a ^ 3 + |α| * (a⁻¹) ^ 3)
  hb2 : |∫ u in Ioi (3 * δ), vacD P u / u ^ 2| ≤ K * ((a⁻¹) ^ 3 + |α| * (a⁻¹) ^ 9)
  -- `(fct:bump-1L)` with `fct:phikill` (3): the finite-part cancellation of `fct:physical-budget` (c)
  hcancel : |(∫ u in Ioi (3 * δ), vacD P u / u) - ∫ u in Ioi (3 * δ), (Φ u).re * P u / u| ≤
    K * (a ^ 3 + |α| * (a⁻¹) ^ 3 + a ^ 8)

namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

lemma hδpos (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) : 0 < δ :=
  lt_of_lt_of_le (mul_pos V.ha0 (pow_pos V.ha 6)) V.hδ0

/-- `u - A ≥ 3u/4` for `u ≥ δ`, `A = L₁ - s`. -/
lemma sub_A (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) : 3 * u / 4 ≤ u - (L1 - s) := by
  have h := (abs_le.mp V.hA).2
  linarith

/-- `u - L₁ Re Φ ≥ u/2` for `u ≥ δ`. -/
lemma sub_phi (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) : u / 2 ≤ u - L1 * (Φ u).re := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  have h1 : |(Φ u).re| ≤ K := by
    refine (V.hΦre u hu0).trans ?_
    calc K * min 1 ((u / a ^ 2) ^ 4) ≤ K * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [V.hK])
      _ = K := mul_one K
  have h2 : |L1 * (Φ u).re| ≤ δ / 2 := by
    rw [abs_mul]
    calc |L1| * |(Φ u).re| ≤ |L1| * K := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ δ / 2 := V.hL1K
  have := (abs_le.mp h2).2
  linarith

/-- `0 ≤ γ ≤ 1` for `u ≥ δ`, `γ = 1 - κ u^{-3}`. -/
lemma gamma_range (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) :
    0 ≤ 1 - κ * (u ^ 3)⁻¹ ∧ 1 - κ * (u ^ 3)⁻¹ ≤ 1 := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  have h1 : (u ^ 3)⁻¹ ≤ (δ ^ 3)⁻¹ :=
    inv_anti₀ (pow_pos V.hδpos 3) (pow_le_pow_left₀ V.hδpos.le hu 3)
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h1 V.hκ0
    linarith [V.hκδ]
  · have : 0 ≤ κ * (u ^ 3)⁻¹ := mul_nonneg V.hκ0 (inv_nonneg.mpr (pow_pos hu0 3).le)
    linarith

end VacHyp


/-! ### Pointwise bounds -/

/-- Transition region `[δ, 3.1δ]`: the sum `Y = |D| + |L₁||ρ|P/u + L₁²ι²P/u²` of the three pieces of the paired bound is `≤ 8K⁴a³`
(`r = √u ≤ 2Ka³`, `|ρ|, ι² ≤ K (u/a²)⁴`, `P ≤ 2K u^{-3/2}`). -/
lemma regionII_Y {r a K L1 ρ ι2 P D : ℝ} (hr0 : 0 < r) (ha : 0 < a) (hK : 1 ≤ K) (hra : r ≤ 2 * K * a ^ 3) (hr1 : r ≤ 1)
    (hD : |D| ≤ K * r) (hP : P ≤ 2 * K * (r ^ 3)⁻¹) (hP0 : 0 ≤ P) (hρ : |ρ| ≤ K * ((r ^ 2 / a ^ 2) ^ 4))
    (hι : ι2 ≤ K * ((r ^ 2 / a ^ 2) ^ 4)) (hι0 : 0 ≤ ι2) (hL1 : |L1| ≤ K * a ^ 8) (ha1 : a ≤ 1) :
    |D| + |L1| * |ρ| * P / r ^ 2 + L1 ^ 2 * ι2 * P / (r ^ 2) ^ 2 ≤ 8 * K ^ 4 * a ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hr2 : 0 < r ^ 2 := by positivity
  have e1 : |D| ≤ 2 * K ^ 2 * a ^ 3 := by
    calc |D| ≤ K * r := hD
      _ ≤ K * (2 * K * a ^ 3) := mul_le_mul_of_nonneg_left hra hK0
      _ = 2 * K ^ 2 * a ^ 3 := by ring
  -- the second term
  have e2 : |L1| * |ρ| * P / r ^ 2 ≤ 4 * K ^ 4 * a ^ 3 := by
    have h1 : |L1| * |ρ| * P / r ^ 2 ≤ (K * a ^ 8) * (K * ((r ^ 2 / a ^ 2) ^ 4)) * (2 * K * (r ^ 3)⁻¹) / r ^ 2 := by
      gcongr
    have h2 : (K * a ^ 8) * (K * ((r ^ 2 / a ^ 2) ^ 4)) * (2 * K * (r ^ 3)⁻¹) / r ^ 2 = 2 * K ^ 3 * r ^ 3 := by
      field_simp
    have h3 : 2 * K ^ 3 * r ^ 3 ≤ 2 * K ^ 3 * r := by
      have : r ^ 3 ≤ r := by
        calc r ^ 3 = r * r ^ 2 := by ring
          _ ≤ r * 1 := by gcongr; nlinarith
          _ = r := mul_one r
      gcongr
    have h4 : 2 * K ^ 3 * r ≤ 2 * K ^ 3 * (2 * K * a ^ 3) := by gcongr
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ ≤ _ := h4
      _ = 4 * K ^ 4 * a ^ 3 := by ring
  have e3 : L1 ^ 2 * ι2 * P / (r ^ 2) ^ 2 ≤ 2 * K ^ 4 * a ^ 3 := by
    have hL2 : L1 ^ 2 ≤ (K * a ^ 8) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg L1, hL1, neg_abs_le L1] : -(K * a ^ 8) ≤ L1) ((le_abs_self L1).trans hL1)
      exact this
    have h1 : L1 ^ 2 * ι2 * P / (r ^ 2) ^ 2 ≤ (K * a ^ 8) ^ 2 * (K * ((r ^ 2 / a ^ 2) ^ 4)) * (2 * K * (r ^ 3)⁻¹) / (r ^ 2) ^ 2 := by
      gcongr
    have h2 : (K * a ^ 8) ^ 2 * (K * ((r ^ 2 / a ^ 2) ^ 4)) * (2 * K * (r ^ 3)⁻¹) / (r ^ 2) ^ 2 = 2 * K ^ 4 * a ^ 8 * r := by
      field_simp
    have h3 : 2 * K ^ 4 * a ^ 8 * r ≤ 2 * K ^ 4 * a ^ 3 := by
      have : a ^ 8 * r ≤ a ^ 3 := by
        calc a ^ 8 * r ≤ a ^ 3 * 1 := by
              have : a ^ 8 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
              exact mul_le_mul this hr1 hr0.le (by positivity)
          _ = a ^ 3 := mul_one _
      nlinarith [pow_nonneg hK0 4]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  have hK24 : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have : 2 * K ^ 2 * a ^ 3 ≤ 2 * K ^ 4 * a ^ 3 := by gcongr
  linarith


/-- The exact algebraic form of the split of `γ Q` (with `γ = 1 - κ u^{-3}` and `Q = (u D - L₁ρP + X)/(u - A)`) into the main part
`D(1 + A/u + A²/u²) - L₁ρP/u` and the remainder (`(fct:vac-paired)`, parts (b)-(d)). -/
lemma vac_split {u A κ D L1 ρ P X : ℝ} (hu : u ≠ 0) (hA : u - A ≠ 0) :
    (1 - κ * (u ^ 3)⁻¹) * ((u * D - L1 * ρ * P + X) / (u - A)) =
      (D * (1 + A / u + A ^ 2 / u ^ 2) - L1 * ρ * P / u) +
        (D * ((A ^ 3 - κ) / (u ^ 2 * (u - A))) - L1 * ρ * P * ((A - κ * (u ^ 2)⁻¹) / (u * (u - A))) +
          (1 - κ * (u ^ 3)⁻¹) * X / (u - A)) := by
  field_simp
  ring

/-- Remainder bound R1: `|D · E₁| ≤ 2K(8K³ + 1)(a^{30}t⁹ + a^{24}t⁷)`, `t = u^{-1/2}`, `E₁ = (A³ - κ)/(u²(u - A))`. -/
lemma remR1 {u t a K A κ D : ℝ} (hu : 0 < u) (ht : 0 < t) (htu : t ^ 2 * u = 1) (hA : |A| ≤ 2 * K * a ^ 8) (hκ0 : 0 ≤ κ)
    (hκa : κ ≤ a ^ 24) (hAu : 3 * u / 4 ≤ u - A) (hD : |D| ≤ K * (a ^ 6 * t ^ 3 + t)) (hK : 1 ≤ K) (ha : 0 < a) :
    |D * ((A ^ 3 - κ) / (u ^ 2 * (u - A)))| ≤ 2 * K * (8 * K ^ 3 + 1) * (a ^ 30 * t ^ 9 + a ^ 24 * t ^ 7) := by
  have hK0 : 0 ≤ K := by linarith
  have hu3 : 0 < u ^ 3 := by positivity
  have hAp : 0 < u - A := by linarith
  have hnum : |A ^ 3 - κ| ≤ (8 * K ^ 3 + 1) * a ^ 24 := by
    have h1 : |A ^ 3| ≤ (2 * K * a ^ 8) ^ 3 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hA 3
    have h2 : (2 * K * a ^ 8) ^ 3 = 8 * K ^ 3 * a ^ 24 := by ring
    calc |A ^ 3 - κ| ≤ |A ^ 3| + |κ| := abs_sub _ _
      _ ≤ 8 * K ^ 3 * a ^ 24 + a ^ 24 := by rw [abs_of_nonneg hκ0]; linarith
      _ = (8 * K ^ 3 + 1) * a ^ 24 := by ring
  have hE : |(A ^ 3 - κ) / (u ^ 2 * (u - A))| ≤ 2 * ((8 * K ^ 3 + 1) * a ^ 24) * t ^ 6 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < u ^ 2 * (u - A))]
    have h1 : u ^ 2 * (3 * u / 4) ≤ u ^ 2 * (u - A) := by gcongr
    have h2 : |A ^ 3 - κ| / (u ^ 2 * (u - A)) ≤ ((8 * K ^ 3 + 1) * a ^ 24) / (u ^ 2 * (3 * u / 4)) := by
      apply div_le_div₀ (by positivity) hnum (by positivity) h1
    have h3 : ((8 * K ^ 3 + 1) * a ^ 24) / (u ^ 2 * (3 * u / 4)) = (4 / 3) * ((8 * K ^ 3 + 1) * a ^ 24) * t ^ 6 := by
      have : t ^ 6 = (t ^ 2) ^ 3 := by ring
      have hu' : u = (t ^ 2)⁻¹ := by field_simp; linarith
      rw [this, hu']
      field_simp
    have h4 : (4 / 3) * ((8 * K ^ 3 + 1) * a ^ 24) * t ^ 6 ≤ 2 * ((8 * K ^ 3 + 1) * a ^ 24) * t ^ 6 := by gcongr; norm_num
    linarith
  have hDb : |D| ≤ K * (a ^ 6 * t ^ 3 + t) := hD
  rw [abs_mul]
  calc |D| * |(A ^ 3 - κ) / (u ^ 2 * (u - A))| ≤ (K * (a ^ 6 * t ^ 3 + t)) * (2 * ((8 * K ^ 3 + 1) * a ^ 24) * t ^ 6) :=
        mul_le_mul hDb hE (abs_nonneg _) (by positivity)
    _ = 2 * K * (8 * K ^ 3 + 1) * (a ^ 30 * t ^ 9 + a ^ 24 * t ^ 7) := by ring


/-- Remainder bound R2: `|L₁ ρ P E₂| ≤ 16 K⁵ a^{12} t³`, `E₂ = (A - κ u^{-2})/(u(u - A))`. -/
lemma remR2 {u t a K A κ L1 ρ P : ℝ} (hu : 0 < u) (ht : 0 < t) (htu : t ^ 2 * u = 1) (hA : |A| ≤ 2 * K * a ^ 8)
    (hκ0 : 0 ≤ κ) (hκu : κ * (u ^ 2)⁻¹ ≤ K ^ 2 * a ^ 8) (hAu : 3 * u / 4 ≤ u - A) (hL1 : |L1| ≤ K * a ^ 8)
    (hρP : |ρ| * P ≤ 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹) (hP0 : 0 ≤ P) (hK : 1 ≤ K) (ha : 0 < a) :
    |L1 * ρ * P * ((A - κ * (u ^ 2)⁻¹) / (u * (u - A)))| ≤ 16 * K ^ 5 * a ^ 12 * t ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hAp : 0 < u - A := by linarith
  have hnum : |A - κ * (u ^ 2)⁻¹| ≤ 3 * K ^ 2 * a ^ 8 := by
    have h1 : |κ * (u ^ 2)⁻¹| ≤ K ^ 2 * a ^ 8 := by
      rw [abs_of_nonneg (mul_nonneg hκ0 (inv_nonneg.mpr (by positivity)))]; exact hκu
    have hK2 : K ≤ K ^ 2 := by nlinarith
    calc |A - κ * (u ^ 2)⁻¹| ≤ |A| + |κ * (u ^ 2)⁻¹| := abs_sub _ _
      _ ≤ 2 * K * a ^ 8 + K ^ 2 * a ^ 8 := add_le_add hA h1
      _ ≤ 3 * K ^ 2 * a ^ 8 := by nlinarith [pow_pos ha 8]
  have hE : |(A - κ * (u ^ 2)⁻¹) / (u * (u - A))| ≤ 4 * K ^ 2 * a ^ 8 * t ^ 4 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < u * (u - A))]
    have h1 : u * (3 * u / 4) ≤ u * (u - A) := by gcongr
    have h2 : |A - κ * (u ^ 2)⁻¹| / (u * (u - A)) ≤ (3 * K ^ 2 * a ^ 8) / (u * (3 * u / 4)) :=
      div_le_div₀ (by positivity) hnum (by positivity) h1
    have h3 : (3 * K ^ 2 * a ^ 8) / (u * (3 * u / 4)) = 4 * K ^ 2 * a ^ 8 * t ^ 4 := by
      have hu' : u = (t ^ 2)⁻¹ := by field_simp; linarith
      rw [hu']
      field_simp
    linarith
  have hL1' : 0 ≤ |L1| := abs_nonneg _
  have step : |L1 * ρ * P * ((A - κ * (u ^ 2)⁻¹) / (u * (u - A)))| =
      |L1| * (|ρ| * P) * |(A - κ * (u ^ 2)⁻¹) / (u * (u - A))| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hP0]; ring
  rw [step]
  calc |L1| * (|ρ| * P) * |(A - κ * (u ^ 2)⁻¹) / (u * (u - A))|
      ≤ (K * a ^ 8) * (4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹) * (4 * K ^ 2 * a ^ 8 * t ^ 4) := by
        gcongr
    _ = 16 * K ^ 5 * a ^ 12 * t ^ 3 := by
        field_simp
        norm_num

/-- Remainder bound R3: `γ X/(u - A) ≤ 8K⁴ a^{12} t³`, `X = P (L₁ι)²/(2(u - L₁ρ))`. -/
lemma remR3 {u t a K A γ L1 ι2 P a' : ℝ} (hu : 0 < u) (ht : 0 < t) (htu : t ^ 2 * u = 1) (hAu : 3 * u / 4 ≤ u - A)
    (hγ1 : γ ≤ 1) (ha' : u / 2 ≤ a') (hL1 : |L1| ≤ K * a ^ 8) (hι0 : 0 ≤ ι2)
    (hιP : ι2 * P ≤ 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹) (hP0 : 0 ≤ P) (hK : 1 ≤ K) (ha : 0 < a) :
    γ * (P * (L1 ^ 2 * ι2) / (2 * a')) / (u - A) ≤ 8 * K ^ 4 * a ^ 12 * t ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hAp : 0 < u - A := by linarith
  have ha'p : 0 < a' := by linarith
  have hL2 : L1 ^ 2 ≤ (K * a ^ 8) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg L1, hL1, neg_abs_le L1] : -(K * a ^ 8) ≤ L1) ((le_abs_self L1).trans hL1)
    exact this
  have hX : 0 ≤ P * (L1 ^ 2 * ι2) / (2 * a') := by positivity
  have h1 : γ * (P * (L1 ^ 2 * ι2) / (2 * a')) / (u - A) ≤ (P * (L1 ^ 2 * ι2) / (2 * a')) / (u - A) := by
    gcongr
    nlinarith
  have h2 : (P * (L1 ^ 2 * ι2) / (2 * a')) / (u - A) ≤ (P * (L1 ^ 2 * ι2) / (2 * (u / 2))) / (3 * u / 4) := by
    gcongr
  have h3 : (P * (L1 ^ 2 * ι2) / (2 * (u / 2))) / (3 * u / 4) ≤
      (P * ((K * a ^ 8) ^ 2 * ι2) / (2 * (u / 2))) / (3 * u / 4) := by
    gcongr
  have h4 : (P * ((K * a ^ 8) ^ 2 * ι2) / (2 * (u / 2))) / (3 * u / 4) = (4 / 3) * (K ^ 2 * a ^ 16) * (ι2 * P) * t ^ 4 := by
    have hu' : u = (t ^ 2)⁻¹ := by field_simp; linarith
    rw [hu']
    field_simp
  have h5 : (4 / 3) * (K ^ 2 * a ^ 16) * (ι2 * P) * t ^ 4 ≤ (4 / 3) * (K ^ 2 * a ^ 16) * (4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹) * t ^ 4 := by
    gcongr
  have h6 : (4 / 3) * (K ^ 2 * a ^ 16) * (4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹) * t ^ 4 = (16 / 3) * K ^ 4 * a ^ 12 * t ^ 3 := by
    field_simp
    norm_num
  have h7 : (16 / 3) * K ^ 4 * a ^ 12 * t ^ 3 ≤ 8 * K ^ 4 * a ^ 12 * t ^ 3 := by
    have : 0 ≤ K ^ 4 * a ^ 12 * t ^ 3 := by positivity
    nlinarith
  linarith


lemma min_one_pow_le_sq {x : ℝ} (hx : 0 ≤ x) : min 1 (x ^ 4) ≤ x ^ 2 := by
  by_cases h : x ≤ 1
  · exact (min_le_right _ _).trans (by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 - x)])
  · exact (min_le_left _ _).trans (by nlinarith)

lemma min_one_pow_le {x : ℝ} (hx : 0 ≤ x) : min 1 (x ^ 4) ≤ x := by
  by_cases h : x ≤ 1
  · exact (min_le_right _ _).trans (by nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x), pow_nonneg hx 3])
  · exact (min_le_left _ _).trans (by linarith [not_le.mp h])

/-- `m P ≤ 4K²a^{-4}t^{-1}` for `m ≤ K min(1, (u/a²)⁴)` and `P ≤ 2K(t³ + t)`, `t = u^{-1/2}` (so `t²u = 1`). -/
lemma mP_bound {u t a K m P : ℝ} (hu : 0 < u) (ht : 0 < t) (htu : t ^ 2 * u = 1) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K)
    (hm : m ≤ K * min 1 ((u / a ^ 2) ^ 4)) (hP : P ≤ 2 * K * (t ^ 3 + t)) (hP0 : 0 ≤ P) :
    m * P ≤ 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹ := by
  have hK0 : 0 ≤ K := by linarith
  have hx : 0 ≤ u / a ^ 2 := by positivity
  have h1 : m * P ≤ (K * min 1 ((u / a ^ 2) ^ 4)) * (2 * K * (t ^ 3 + t)) :=
    mul_le_mul hm hP hP0 (by positivity)
  have h2 : (K * min 1 ((u / a ^ 2) ^ 4)) * (2 * K * (t ^ 3 + t)) ≤
      2 * K ^ 2 * ((u / a ^ 2) ^ 2 * t ^ 3 + (u / a ^ 2) * t) := by
    have e : (K * min 1 ((u / a ^ 2) ^ 4)) * (2 * K * (t ^ 3 + t)) =
        2 * K ^ 2 * (min 1 ((u / a ^ 2) ^ 4) * t ^ 3 + min 1 ((u / a ^ 2) ^ 4) * t) := by ring
    rw [e]
    have := min_one_pow_le_sq hx
    have := min_one_pow_le hx
    have h3 : min 1 ((u / a ^ 2) ^ 4) * t ^ 3 ≤ (u / a ^ 2) ^ 2 * t ^ 3 := by gcongr
    have h4 : min 1 ((u / a ^ 2) ^ 4) * t ≤ (u / a ^ 2) * t := by gcongr
    have : 0 ≤ 2 * K ^ 2 := by positivity
    nlinarith
  have hu' : u = (t ^ 2)⁻¹ := by field_simp; linarith
  have h5 : (u / a ^ 2) ^ 2 * t ^ 3 + (u / a ^ 2) * t = (a ^ 4)⁻¹ * t⁻¹ + (a ^ 2)⁻¹ * t⁻¹ := by
    rw [hu']; field_simp
  have h6 : (a ^ 2)⁻¹ ≤ (a ^ 4)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_of_le_one ha.le ha1 (by norm_num))
  have h7 : (a ^ 4)⁻¹ * t⁻¹ + (a ^ 2)⁻¹ * t⁻¹ ≤ 2 * ((a ^ 4)⁻¹ * t⁻¹) := by
    have : (a ^ 2)⁻¹ * t⁻¹ ≤ (a ^ 4)⁻¹ * t⁻¹ := by gcongr
    linarith
  calc m * P ≤ _ := h1
    _ ≤ _ := h2
    _ = 2 * K ^ 2 * ((a ^ 4)⁻¹ * t⁻¹ + (a ^ 2)⁻¹ * t⁻¹) := by rw [h5]
    _ ≤ 2 * K ^ 2 * (2 * ((a ^ 4)⁻¹ * t⁻¹)) := by gcongr
    _ = 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹ := by ring


/-! ### Region III (`u > 3.1δ`): the cutoff is `1`, `O - F ≤ γ Q = M₀ + remainder` -/

/-- The integrand of the vacuum integral in the variable `u = L - s`. -/
noncomputable def vacG (χ : ℝ → ℝ) (c δ s L1 : ℝ) (P : ℝ → ℝ) (Φ : ℝ → ℂ) (u : ℝ) : ℝ :=
  χ ((u + s) / (3 * δ)) * physGamma c s (u + s) * (physOsc P Φ s L1 (u + s) - physF s L1 (u + s))

/-- The main part `D(1 + A/u + A²/u²) - L₁ Re Φ P/u` of `(fct:vac-paired)`, `A = L₁ - s`. -/
noncomputable def vacM0 (P : ℝ → ℝ) (Φ : ℝ → ℂ) (L1 s u : ℝ) : ℝ :=
  vacD P u * (1 + (L1 - s) / u + (L1 - s) ^ 2 / u ^ 2) - L1 * (Φ u).re * P u / u

/-- The power-law majorant of the remainder on `u > 3.1δ`. -/
noncomputable def vacBR (K a u : ℝ) : ℝ :=
  2 * K * (8 * K ^ 3 + 1) * (a ^ 30 * (u ^ (-(1 / 2 : ℝ))) ^ 9 + a ^ 24 * (u ^ (-(1 / 2 : ℝ))) ^ 7) +
    (16 * K ^ 5 + 8 * K ^ 4) * a ^ 12 * (u ^ (-(1 / 2 : ℝ))) ^ 3

lemma rpow_neg_half_sq {u : ℝ} (hu : 0 < u) : (u ^ (-(1 / 2 : ℝ))) ^ 2 * u = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

lemma rpow_neg_three_half {u : ℝ} (hu : 0 < u) : u ^ (-(3 / 2 : ℝ)) = (u ^ (-(1 / 2 : ℝ))) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num

lemma rpow_neg_three {u : ℝ} (hu : 0 < u) : u ^ (-(3 : ℝ)) = (u ^ 3)⁻¹ := by
  rw [Real.rpow_neg hu.le]
  norm_cast

lemma vacG_eq {χ : ℝ → ℝ} {c δ s L1 κ : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ} (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) {u : ℝ}
    (hu : 0 < u) :
    vacG χ c δ s L1 P Φ u = χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) *
      (P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s)) - u / (u - (L1 - s)) * uctIfl u) := by
  unfold vacG physGamma physOsc physF
  simp only [add_sub_cancel_right, rpow_neg_three hu, hκ]
  have e : u + s - L1 = u - (L1 - s) := by ring
  rw [e]


/-- The one-sided paired bound `Q` (`(fct:vac-paired)`) in the variable `u`. -/
noncomputable def vacQ (P : ℝ → ℝ) (Φ : ℝ → ℂ) (L1 s u : ℝ) : ℝ :=
  (u * vacD P u - L1 * (Φ u).re * P u + P u * (L1 * (Φ u).im) ^ 2 / (2 * (u - L1 * (Φ u).re))) / (u - (L1 - s))

lemma vacG_le_Q {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K a0 a1 a δ s L1 α κ Cfl I0 c : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}
    (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) {u : ℝ} (hu : δ ≤ u) :
    vacG χ c δ s L1 P Φ u ≤ χ ((u + s) / (3 * δ)) * ((1 - κ * (u ^ 3)⁻¹) * vacQ P Φ L1 s u) := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  rw [vacG_eq hκ hu0]
  have hq := physOsc_sub_physF_le (P := P) (Φ := Φ) (s := s) (L1 := L1) (x := u + s)
    (by simpa only [add_sub_cancel_right] using V.hP0 u hu0)
    (by have := V.sub_A hu; have e : u + s - L1 = u - (L1 - s) := by ring
        rw [e]; linarith)
    (by simp only [add_sub_cancel_right]; have := V.sub_phi hu; linarith)
  simp only [physOsc, physF, add_sub_cancel_right] at hq
  have e : u + s - L1 = u - (L1 - s) := by ring
  rw [e] at hq
  have hg := V.gamma_range hu
  have hχ0 := (hχ.mem ((u + s) / (3 * δ))).1
  have hc : 0 ≤ χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) := mul_nonneg hχ0 hg.1
  have : P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s)) - u / (u - (L1 - s)) * uctIfl u ≤ vacQ P Φ L1 s u := by
    unfold vacQ vacD; exact hq
  calc _ ≤ χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) * vacQ P Φ L1 s u := mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring


namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

/-- `|D_*| ≤ K (a⁶ u^{-3/2} + u^{-1/2})` for `u ≥ 3δ` (`(fct:Dstar-inner)`-regimes of `fct:physical-budget` (d)). -/
lemma D_bound_R (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : 3 * δ ≤ u) :
    |vacD P u| ≤ K * (a ^ 6 * (u ^ (-(1 / 2 : ℝ))) ^ 3 + u ^ (-(1 / 2 : ℝ))) := by
  have hu0 : 0 < u := by have := V.hδpos; linarith
  have ht : 0 < u ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have hK0 : 0 ≤ K := by linarith [V.hK]
  by_cases h : u ≤ 144 * δ
  · have := V.hDmid u ⟨hu, h⟩
    rw [rpow_neg_three_half hu0] at this
    calc _ ≤ _ := this
      _ ≤ K * (a ^ 6 * (u ^ (-(1 / 2 : ℝ))) ^ 3 + u ^ (-(1 / 2 : ℝ))) := by
        rw [mul_assoc]; gcongr; linarith
  · have := V.hDfar u (not_le.mp h).le
    calc _ ≤ _ := this
      _ ≤ K * (a ^ 6 * (u ^ (-(1 / 2 : ℝ))) ^ 3 + u ^ (-(1 / 2 : ℝ))) := by
        gcongr; have : 0 ≤ a ^ 6 * (u ^ (-(1 / 2 : ℝ))) ^ 3 := by positivity
        linarith

/-- `P ≤ 2K (u^{-3/2} + u^{-1/2})` for `u ≥ 3δ`. -/
lemma P_bound_R (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : 3 * δ ≤ u) :
    P u ≤ 2 * K * ((u ^ (-(1 / 2 : ℝ))) ^ 3 + u ^ (-(1 / 2 : ℝ))) := by
  have hu0 : 0 < u := by have := V.hδpos; linarith
  have ht : 0 < u ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have hK0 : 0 ≤ K := by linarith [V.hK]
  have hD := (le_abs_self _).trans (V.D_bound_R hu)
  have hfl : uctIfl u ≤ K * (u ^ (-(1 / 2 : ℝ))) ^ 3 := by
    unfold uctIfl
    rw [rpow_neg_three_half hu0]
    calc uctAlphaFl * (u ^ (-(1 / 2 : ℝ))) ^ 3 ≤ |uctAlphaFl| * (u ^ (-(1 / 2 : ℝ))) ^ 3 := by gcongr; exact le_abs_self _
      _ ≤ K * (u ^ (-(1 / 2 : ℝ))) ^ 3 := by gcongr; exact V.hKf
  have ha6 : a ^ 6 ≤ 1 := pow_le_one₀ V.ha.le V.ha1
  have h3 : 0 ≤ (u ^ (-(1 / 2 : ℝ))) ^ 3 := by positivity
  have : P u = vacD P u + uctIfl u := by unfold vacD; ring
  rw [this]
  have h4 : K * (a ^ 6 * (u ^ (-(1 / 2 : ℝ))) ^ 3) ≤ K * (u ^ (-(1 / 2 : ℝ))) ^ 3 := by
    gcongr; nlinarith
  nlinarith

end VacHyp


/-- **Region III** (`u > 3.1δ`, where `χ = 1`): `vacG ≤ M₀ + (power-law remainder)` (parts (b)-(d) of `fct:physical-budget`,
via `(fct:vac-paired)` and the exact `1/u` expansions). -/
lemma vacG_le_III {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K a0 a1 a δ s L1 α κ Cfl I0 c : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}
    (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) {u : ℝ} (hu : 31 / 10 * δ < u) :
    vacG χ c δ s L1 P Φ u ≤ vacM0 P Φ L1 s u + vacBR K a u := by
  have hδ := V.hδpos
  have hu0 : 0 < u := by linarith
  have hδu : δ ≤ u := by linarith
  have h3 : 3 * δ ≤ u := by linarith
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  have ha := V.ha
  have hχ1 : χ ((u + s) / (3 * δ)) = 1 := by
    apply hχ.one
    rw [le_div_iff₀ (by positivity)]
    have := (abs_le.mp V.hs10).1
    linarith
  have h1 := vacG_le_Q hχ V hκ hδu
  rw [hχ1, one_mul] at h1
  set t := u ^ (-(1 / 2 : ℝ)) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hu0 _
  have htu : t ^ 2 * u = 1 := rpow_neg_half_sq hu0
  have hAu := V.sub_A hδu
  have hAp : 0 < u - (L1 - s) := by linarith
  have hsub := V.sub_phi hδu
  have hA : |L1 - s| ≤ 2 * K * a ^ 8 := by
    have h12 : a ^ 12 ≤ a ^ 8 := pow_le_pow_of_le_one ha.le V.ha1 (by norm_num)
    calc |L1 - s| ≤ |L1| + |s| := abs_sub _ _
      _ ≤ K * a ^ 8 + K * a ^ 12 := add_le_add V.hL1 V.hs
      _ ≤ K * a ^ 8 + K * a ^ 8 := by gcongr
      _ = 2 * K * a ^ 8 := by ring
  have hκu : κ * (u ^ 2)⁻¹ ≤ K ^ 2 * a ^ 8 := by
    have hua : a0 * a ^ 6 ≤ u := by linarith [V.hδ0]
    have h1 : (u ^ 2)⁻¹ ≤ ((a0 * a ^ 6) ^ 2)⁻¹ :=
      inv_anti₀ (by have := V.ha0; positivity) (pow_le_pow_left₀ (by have := V.ha0; positivity) hua 2)
    have h2 : ((a0 * a ^ 6) ^ 2)⁻¹ = (a0⁻¹) ^ 2 * (a ^ 12)⁻¹ := by
      field_simp
    have h3 : (a0⁻¹) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr V.ha0.le) V.hKa0 2
    have h12 : a ^ 12 ≤ a ^ 8 := pow_le_pow_of_le_one ha.le V.ha1 (by norm_num)
    calc κ * (u ^ 2)⁻¹ ≤ a ^ 24 * ((a0⁻¹) ^ 2 * (a ^ 12)⁻¹) := by
          rw [← h2]; exact mul_le_mul V.hκa h1 (inv_nonneg.mpr (by positivity)) (by positivity)
      _ ≤ a ^ 24 * (K ^ 2 * (a ^ 12)⁻¹) := by gcongr
      _ = K ^ 2 * a ^ 12 := by field_simp
      _ ≤ K ^ 2 * a ^ 8 := by gcongr
  have hD := V.D_bound_R h3
  have hP := V.P_bound_R h3
  have hP0 := V.hP0 u hu0
  have hρP : |(Φ u).re| * P u ≤ 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹ :=
    mP_bound hu0 ht htu ha V.ha1 hK (V.hΦre u hu0) hP hP0
  have hιP : (Φ u).im ^ 2 * P u ≤ 4 * K ^ 2 * (a ^ 4)⁻¹ * t⁻¹ :=
    mP_bound hu0 ht htu ha V.ha1 hK (V.hΦim u hu0) hP hP0
  have hg := V.gamma_range hδu
  -- the split
  have hsplit := vac_split (u := u) (A := L1 - s) (κ := κ) (D := vacD P u) (L1 := L1) (ρ := (Φ u).re) (P := P u)
    (X := P u * (L1 * (Φ u).im) ^ 2 / (2 * (u - L1 * (Φ u).re))) hu0.ne' hAp.ne'
  have hQ : vacQ P Φ L1 s u = (u * vacD P u - L1 * (Φ u).re * P u +
      P u * (L1 * (Φ u).im) ^ 2 / (2 * (u - L1 * (Φ u).re))) / (u - (L1 - s)) := rfl
  rw [hQ, hsplit] at h1
  have r1 := remR1 hu0 ht htu hA V.hκ0 V.hκa hAu hD hK ha
  have r2 := remR2 hu0 ht htu hA V.hκ0 hκu hAu V.hL1 hρP hP0 hK ha
  have r3 := remR3 hu0 ht htu hAu hg.2 hsub V.hL1 (sq_nonneg _) hιP hP0 hK ha
  have hX : P u * (L1 * (Φ u).im) ^ 2 = P u * (L1 ^ 2 * (Φ u).im ^ 2) := by ring
  rw [hX] at h1
  have e : vacM0 P Φ L1 s u = vacD P u * (1 + (L1 - s) / u + (L1 - s) ^ 2 / u ^ 2) - L1 * (Φ u).re * P u / u := rfl
  have e1 := le_abs_self (vacD P u * (((L1 - s) ^ 3 - κ) / (u ^ 2 * (u - (L1 - s)))))
  have e2 := neg_abs_le (L1 * (Φ u).re * P u * (((L1 - s) - κ * (u ^ 2)⁻¹) / (u * (u - (L1 - s)))))
  have hvb : vacBR K a u = 2 * K * (8 * K ^ 3 + 1) * (a ^ 30 * t ^ 9 + a ^ 24 * t ^ 7) +
      (16 * K ^ 5 + 8 * K ^ 4) * a ^ 12 * t ^ 3 := rfl
  rw [e, hvb]
  linarith


/-! ### Region II (`δ ≤ u ≤ 3.1δ`): crude absolute bounds -/

/-- `Y = |D| + |L₁||Re Φ|P/u + L₁²(Im Φ)²P/u²`. -/
noncomputable def vacY (P : ℝ → ℝ) (Φ : ℝ → ℂ) (L1 u : ℝ) : ℝ :=
  |vacD P u| + |L1| * |(Φ u).re| * P u / u + L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2

namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

lemma Q_abs_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) :
    |vacQ P Φ L1 s u| ≤ 4 / 3 * vacY P Φ L1 u := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  have hAu := V.sub_A hu
  have hsub := V.sub_phi hu
  have hP0 := V.hP0 u hu0
  have hAp : 0 < u - (L1 - s) := by linarith
  unfold vacQ vacY
  rw [abs_div, abs_of_pos hAp]
  set X := P u * (L1 * (Φ u).im) ^ 2 / (2 * (u - L1 * (Φ u).re)) with hX
  have hX0 : 0 ≤ X := div_nonneg (mul_nonneg hP0 (sq_nonneg _)) (by linarith)
  have hX1 : X ≤ L1 ^ 2 * (Φ u).im ^ 2 * P u / u := by
    rw [hX, div_le_div_iff₀ (by linarith) hu0]
    have : 0 ≤ P u * (L1 * (Φ u).im) ^ 2 := by positivity
    nlinarith
  have hnum : |u * vacD P u - L1 * (Φ u).re * P u + X| ≤ u * (|vacD P u| + |L1| * |(Φ u).re| * P u / u +
      L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2) := by
    have e : u * (|vacD P u| + |L1| * |(Φ u).re| * P u / u + L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2) =
        u * |vacD P u| + |L1| * |(Φ u).re| * P u + L1 ^ 2 * (Φ u).im ^ 2 * P u / u := by
      field_simp
    rw [e]
    calc |u * vacD P u - L1 * (Φ u).re * P u + X| ≤ |u * vacD P u| + |L1 * (Φ u).re * P u| + |X| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos hu0, abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hX0]
          linarith
  calc |u * vacD P u - L1 * (Φ u).re * P u + X| / (u - (L1 - s)) ≤
        (u * (|vacD P u| + |L1| * |(Φ u).re| * P u / u + L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2)) / (3 * u / 4) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hAu
    _ = _ := by field_simp

lemma M0_abs_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) :
    |vacM0 P Φ L1 s u| ≤ 2 * vacY P Φ L1 u := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  have hP0 := V.hP0 u hu0
  have hA : |L1 - s| ≤ u / 4 := (V.hA).trans (by linarith)
  have hw : |1 + (L1 - s) / u + (L1 - s) ^ 2 / u ^ 2| ≤ 2 := by
    have h1 : |(L1 - s) / u| ≤ 1 / 4 := by
      rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]; linarith
    have h2 : (L1 - s) ^ 2 / u ^ 2 ≤ 1 / 16 := by
      have : (L1 - s) ^ 2 / u ^ 2 = ((L1 - s) / u) ^ 2 := by ring
      rw [this]
      have := abs_le.mp h1
      nlinarith
    have h3 : 0 ≤ (L1 - s) ^ 2 / u ^ 2 := by positivity
    have := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith
  unfold vacM0 vacY
  calc |vacD P u * (1 + (L1 - s) / u + (L1 - s) ^ 2 / u ^ 2) - L1 * (Φ u).re * P u / u|
      ≤ |vacD P u * (1 + (L1 - s) / u + (L1 - s) ^ 2 / u ^ 2)| + |L1 * (Φ u).re * P u / u| := abs_sub _ _
    _ ≤ |vacD P u| * 2 + |L1| * |(Φ u).re| * P u / u := by
        rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_pos hu0]
        gcongr
    _ ≤ 2 * (|vacD P u| + |L1| * |(Φ u).re| * P u / u + L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2) := by
        have : 0 ≤ L1 ^ 2 * (Φ u).im ^ 2 * P u / u ^ 2 := by positivity
        have : 0 ≤ |L1| * |(Φ u).re| * P u / u := by positivity
        nlinarith [abs_nonneg (vacD P u)]

/-- `Y ≤ 8K⁴a³` on `[δ, 3.1δ]` (`(fct:Dstar-inner)`, `fct:phikill` (1)). -/
lemma Y_le_II (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : δ ≤ u) (hu2 : u ≤ 31 / 10 * δ) :
    vacY P Φ L1 u ≤ 8 * K ^ 4 * a ^ 3 := by
  have hu0 : 0 < u := lt_of_lt_of_le V.hδpos hu
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  have ha := V.ha
  have hP0 := V.hP0 u hu0
  set r := Real.sqrt u with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hu0
  have hrsq : r ^ 2 = u := Real.sq_sqrt hu0.le
  have hu1 : u ≤ 1 := by linarith [V.h31]
  have hr1 : r ≤ 1 := by
    rw [hr]; calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hu1
      _ = 1 := Real.sqrt_one
  have hua : u ≤ (2 * K * a ^ 3) ^ 2 := by
    have h1 : u ≤ 31 / 10 * (a1 * a ^ 6) := by have := V.hδ1; linarith
    have h2 : 31 / 10 * (a1 * a ^ 6) ≤ 4 * K ^ 2 * a ^ 6 := by
      have : a1 ≤ K := V.hKa1
      have : K ≤ K ^ 2 := by nlinarith
      have h6 : 0 ≤ a ^ 6 := by positivity
      nlinarith
    calc u ≤ 4 * K ^ 2 * a ^ 6 := h1.trans h2
      _ = (2 * K * a ^ 3) ^ 2 := by ring
  have hra : r ≤ 2 * K * a ^ 3 := by
    rw [hr]; exact Real.sqrt_le_iff.mpr ⟨by positivity, hua⟩
  have hD : |vacD P u| ≤ K * r := V.hDin u ⟨hu, hu2⟩
  have hfl : uctIfl u ≤ K * (r ^ 3)⁻¹ := by
    unfold uctIfl
    have : u ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by
      rw [rpow_neg_three_half hu0, Real.rpow_neg hu0.le, hr, Real.sqrt_eq_rpow]; simp
    rw [this]
    calc uctAlphaFl * (r ^ 3)⁻¹ ≤ |uctAlphaFl| * (r ^ 3)⁻¹ := by gcongr; exact le_abs_self _
      _ ≤ K * (r ^ 3)⁻¹ := by gcongr; exact V.hKf
  have hKr : K * r ≤ K * (r ^ 3)⁻¹ := by
    gcongr
    rw [← one_div, le_div_iff₀ (by positivity)]
    have : r * r ^ 3 = r ^ 4 := by ring
    rw [this]
    exact pow_le_one₀ hr0.le hr1
  have hP : P u ≤ 2 * K * (r ^ 3)⁻¹ := by
    have : P u = vacD P u + uctIfl u := by unfold vacD; ring
    rw [this]
    have := (le_abs_self (vacD P u)).trans hD
    linarith
  have hmin : ∀ m : ℝ, m ≤ K * min 1 ((u / a ^ 2) ^ 4) → m ≤ K * ((r ^ 2 / a ^ 2) ^ 4) := by
    intro m hm
    rw [hrsq]
    exact hm.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK0)
  have key := regionII_Y hr0 ha hK hra hr1 hD hP hP0
    (hmin _ (V.hΦre u hu0)) (hmin _ (V.hΦim u hu0)) (sq_nonneg _) V.hL1 V.ha1
  rw [hrsq] at key
  exact key

end VacHyp

end FormalResearch.SignUncertainty.FctSym

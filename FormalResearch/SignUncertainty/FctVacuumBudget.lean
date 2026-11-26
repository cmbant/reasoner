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

/-- The named inputs of the vacuum integral at one `(ε, c)`, with `a = c^{-1/12}` (so `τ₁ = c^{-1/4} = a³`, `c^{-1} = a^{12}`,
`δ_L ≍ a⁶`, `|L₁| ≲ a⁸`, `|s| = |θ₁^ε|/c ≲ a^{12}`, `|α| ≲ a⁸`), one constant `K` dominating all of them; `P = I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)`,
`Φ(u) = φ_kill(i τ₀(u); a)`.  Each field is a display of `fct:comp-D` / `fct:phikill` or a size fact of the datum, as annotated. -/
structure VacDisp (K a0 a1 a δ s L1 α Cfl I0 : ℝ) (P : ℝ → ℝ) (Φ : ℝ → ℂ) : Prop where
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
  -- regularity and positivity of the datum (`P ≥ 0`: `I_osc^{DH₀} ≥ 0`, `1 + Δ_curv > 0`)
  hPm : Measurable P
  hP0 : ∀ u, 0 < u → 0 ≤ P u
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

/-- `VacDisp` together with the facts that are proved (not assumed) in the uniform statement: measurability and the size bounds of
`Φ = φ_kill(i τ₀(·); a)` (`fct:phikill` (1)), `κ = (5π²/96) c^{-2} ≤ a^{24}`, and the smallness of `a` (`c` large). -/
structure VacHyp (K a0 a1 a δ s L1 α κ Cfl I0 : ℝ) (P : ℝ → ℝ) (Φ : ℝ → ℂ) : Prop extends
    VacDisp K a0 a1 a δ s L1 α Cfl I0 P Φ where
  hκ0 : 0 ≤ κ
  hκa : κ ≤ a ^ 24
  -- smallness for large `c`
  hA : |L1 - s| ≤ δ / 4
  hs10 : |s| ≤ δ / 10
  hL1K : |L1| * K ≤ δ / 2
  h31 : 31 / 10 * δ ≤ 1
  hκδ : κ * (δ ^ 3)⁻¹ ≤ 1
  -- `fct:phikill` (1): `|φ_kill(it; a)| ≤ C min((t/a)^8, 1)` and `τ₀(u)² ≲ u`
  hΦm : Measurable Φ
  hΦre : ∀ u, 0 < u → |(Φ u).re| ≤ K * min 1 ((u / a ^ 2) ^ 4)
  hΦim : ∀ u, 0 < u → (Φ u).im ^ 2 ≤ K * min 1 ((u / a ^ 2) ^ 4)

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


/-! ### The main part `M₀` on `(3δ, ∞)` -/

lemma integrableOn_div_pow {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hf : IntegrableOn f (Ioi b)) (k : ℕ) :
    IntegrableOn (fun u => f u / u ^ k) (Ioi b) := by
  have hm : AEStronglyMeasurable (fun u : ℝ => f u / u ^ k) (volume.restrict (Ioi b)) := by
    simp only [div_eq_mul_inv]
    exact hf.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
  refine Integrable.mono' (hf.norm.const_mul (b ^ k)⁻¹) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans hb hu
  rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0]
  rw [div_eq_inv_mul]
  gcongr
  exact le_of_lt hu

namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

lemma vacD_meas (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) : Measurable (vacD P) := by
  unfold vacD uctIfl
  have := V.hPm
  fun_prop

/-- `∫_{3δ}^∞ ρ P/u` is finite: `|ρ P/u| ≤ 2K²(u^{-5/2} + u^{-3/2})`. -/
lemma rhoP_integrableOn (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) :
    IntegrableOn (fun u => (Φ u).re * P u / u) (Ioi (3 * δ)) := by
  have hδ := V.hδpos
  have hK := V.hK
  have hm : AEStronglyMeasurable (fun u => (Φ u).re * P u / u) (volume.restrict (Ioi (3 * δ))) := by
    have := V.hPm; have := V.hΦm
    exact (by fun_prop : Measurable (fun u => (Φ u).re * P u / u)).aestronglyMeasurable
  have i1 := (integral_Ioi_rpow_neg (b := 3 * δ) (r := 5 / 2) (by positivity) (by norm_num)).1
  have i2 := (integral_Ioi_rpow_neg (b := 3 * δ) (r := 3 / 2) (by positivity) (by norm_num)).1
  refine Integrable.mono' ((i1.const_mul (2 * K ^ 2)).add (i2.const_mul (2 * K ^ 2))) hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have h3 : 3 * δ ≤ u := le_of_lt hu
  have hu0 : 0 < u := by linarith
  have hP0 := V.hP0 u hu0
  have hP := V.P_bound_R h3
  have hρ : |(Φ u).re| ≤ K := by
    refine (V.hΦre u hu0).trans ?_
    calc K * min 1 ((u / a ^ 2) ^ 4) ≤ K * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
      _ = K := mul_one K
  have ht : 0 < u ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
  have htu := rpow_neg_half_sq hu0
  set t := u ^ (-(1 / 2 : ℝ)) with ht_def
  have e1 : u ^ (-(5 / 2 : ℝ)) = t ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have e2 : u ^ (-(3 / 2 : ℝ)) = t ^ 3 := rpow_neg_three_half hu0
  have hinv : u⁻¹ = t ^ 2 := by field_simp; linarith
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hP0, abs_of_pos hu0]
  simp only [Pi.add_apply, e1, e2]
  rw [div_eq_mul_inv, hinv]
  calc |(Φ u).re| * P u * t ^ 2 ≤ K * (2 * K * (t ^ 3 + t)) * t ^ 2 := by gcongr
    _ = 2 * K ^ 2 * t ^ 5 + 2 * K ^ 2 * t ^ 3 := by ring

end VacHyp


namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

/-- The constant of `M0_integral_le`. -/
noncomputable def AM (K : ℝ) : ℝ := (2 * K + K ^ 2) + 2 * (K ^ 2 * (2 + K)) + 4 * K ^ 3 * (1 + K)

/-- **Parts (b), (c), (d) combined** (`fct:physical-budget`): the main part `M₀` is integrable on `(3δ, ∞)` and
`∫_{3δ}^∞ M₀ ≤ AM a⁹`.  Inputs: `(fct:cos-pen)`, `∫_0^{3δ}D_*`, `(fct:bump-1L)`, `(fct:bump-2L)` and the finite-part cancellation. -/
lemma M0_integral_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) :
    IntegrableOn (vacM0 P Φ L1 s) (Ioi (3 * δ)) ∧ ∫ u in Ioi (3 * δ), vacM0 P Φ L1 s u ≤ AM K * a ^ 9 := by
  have hδ := V.hδpos
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  have ha := V.ha
  have ha1 := V.ha1
  have hb : 0 < 3 * δ := by positivity
  have h9 : ∀ n : ℕ, 9 ≤ n → a ^ n ≤ a ^ 9 := fun n hn => pow_le_pow_of_le_one ha.le ha1 hn
  have hD1 : IntegrableOn (vacD P) (Ioi (3 * δ)) := V.hDint.mono_set (Ioi_subset_Ioi hb.le)
  have hD2 : IntegrableOn (fun u => vacD P u / u) (Ioi (3 * δ)) := by
    simpa using integrableOn_div_pow hb hD1 1
  have hD3 : IntegrableOn (fun u => vacD P u / u ^ 2) (Ioi (3 * δ)) := integrableOn_div_pow hb hD1 2
  have hR := V.rhoP_integrableOn
  set A := L1 - s with hA
  have hpt : ∀ u : ℝ, vacM0 P Φ L1 s u =
      vacD P u + A * (vacD P u / u) + A ^ 2 * (vacD P u / u ^ 2) - L1 * ((Φ u).re * P u / u) := by
    intro u; unfold vacM0; ring
  have hfun : vacM0 P Φ L1 s = fun u => vacD P u + A * (vacD P u / u) + A ^ 2 * (vacD P u / u ^ 2) -
      L1 * ((Φ u).re * P u / u) := funext hpt
  have i12 : IntegrableOn (fun u => vacD P u + A * (vacD P u / u)) (Ioi (3 * δ)) := hD1.add (hD2.const_mul A)
  have i123 : IntegrableOn (fun u => vacD P u + A * (vacD P u / u) + A ^ 2 * (vacD P u / u ^ 2)) (Ioi (3 * δ)) :=
    i12.add (hD3.const_mul (A ^ 2))
  have i4 : IntegrableOn (fun u => L1 * ((Φ u).re * P u / u)) (Ioi (3 * δ)) := hR.const_mul L1
  have hint : IntegrableOn (vacM0 P Φ L1 s) (Ioi (3 * δ)) := by
    rw [hfun]
    exact i123.sub i4
  refine ⟨hint, ?_⟩
  have hsplit : ∫ u in Ioi (3 * δ), vacM0 P Φ L1 s u =
      (∫ u in Ioi (3 * δ), vacD P u) + A * (∫ u in Ioi (3 * δ), vacD P u / u) +
        A ^ 2 * (∫ u in Ioi (3 * δ), vacD P u / u ^ 2) - L1 * (∫ u in Ioi (3 * δ), (Φ u).re * P u / u) := by
    have e1 := integral_sub i123 i4
    have e2 := integral_add i12 (hD3.const_mul (A ^ 2))
    have e3 := integral_add hD1 (hD2.const_mul A)
    simp only [integral_const_mul] at e1 e2 e3
    rw [hfun]
    simp only [e1, e2, e3]
  rw [hsplit]
  set ID := ∫ u in Ioi (3 * δ), vacD P u with hID
  set I1 := ∫ u in Ioi (3 * δ), vacD P u / u with hI1
  set I2 := ∫ u in Ioi (3 * δ), vacD P u / u ^ 2 with hI2
  set Iρ := ∫ u in Ioi (3 * δ), (Φ u).re * P u / u with hIρ
  have hα := V.hα
  have hαK : |α| * a ^ 3 ≤ K * a ^ 9 := by
    calc |α| * a ^ 3 ≤ (K * a ^ 8) * a ^ 3 := by gcongr
      _ = K * a ^ 11 := by ring
      _ ≤ K * a ^ 9 := mul_le_mul_of_nonneg_left (h9 11 (by norm_num)) hK0
  have hαinv : |α| * (a⁻¹) ^ 3 ≤ K * a ^ 5 := by
    calc |α| * (a⁻¹) ^ 3 ≤ (K * a ^ 8) * (a⁻¹) ^ 3 := by gcongr
      _ = K * a ^ 5 := by field_simp
  have hαinv9 : |α| * (a⁻¹) ^ 9 ≤ K * a⁻¹ := by
    calc |α| * (a⁻¹) ^ 9 ≤ (K * a ^ 8) * (a⁻¹) ^ 9 := by gcongr
      _ = K * a⁻¹ := by field_simp
  have ha5 : a ^ 5 ≤ 1 := pow_le_one₀ ha.le ha1
  have ha3 : a ^ 3 ≤ 1 := pow_le_one₀ ha.le ha1
  -- the integral of D over (3δ, ∞)
  have hID : ID ≤ (2 * K + K ^ 2) * a ^ 9 := by
    have hu : Ioc 0 (3 * δ) ∪ Ioi (3 * δ) = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hb.le
    have hI : IntegrableOn (vacD P) (Ioc 0 (3 * δ)) := V.hDint.mono_set Ioc_subset_Ioi_self
    have hsum : (∫ u in Ioi (0 : ℝ), vacD P u) = (∫ u in Ioc 0 (3 * δ), vacD P u) + ID := by
      rw [← hu, setIntegral_union (Set.disjoint_left.mpr fun x (hx : x ∈ Ioc (0 : ℝ) (3 * δ)) (hx' : x ∈ Ioi (3 * δ)) => not_lt.mpr hx.2 hx') measurableSet_Ioi hI hD1]
    have h1 := (abs_le.mp V.hcos).2
    have h2 := (abs_le.mp V.hin).1
    have : ID = (∫ u in Ioi (0 : ℝ), vacD P u) - ∫ u in Ioc 0 (3 * δ), vacD P u := by linarith
    nlinarith [V.hCfl, hαK, mul_le_mul_of_nonneg_left hαK hK0]
  have hI1b : |I1| ≤ K * (2 + K) := by
    have h := V.hb1
    have : |I1| ≤ |I0| + |I1 - I0| := by
      have := abs_add_le I0 (I1 - I0); rwa [add_sub_cancel] at this
    have h3 : K * (a ^ 3 + |α| * (a⁻¹) ^ 3) ≤ K * (1 + K) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      have : K * a ^ 5 ≤ K := by nlinarith
      linarith
    nlinarith [V.hI0]
  have hI2b : |I2| ≤ K * ((a⁻¹) ^ 3 + K * a⁻¹) := by
    refine V.hb2.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    linarith
  have ha53 : a ^ 5 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have ha83 : a ^ 8 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have hDiff : |I1 - Iρ| ≤ K * (2 + K) * a ^ 3 := by
    refine V.hcancel.trans ?_
    have : a ^ 3 + |α| * (a⁻¹) ^ 3 + a ^ 8 ≤ (2 + K) * a ^ 3 := by
      have : K * a ^ 5 ≤ K * a ^ 3 := mul_le_mul_of_nonneg_left ha53 hK0
      nlinarith
    calc K * (a ^ 3 + |α| * (a⁻¹) ^ 3 + a ^ 8) ≤ K * ((2 + K) * a ^ 3) := mul_le_mul_of_nonneg_left this hK0
      _ = K * (2 + K) * a ^ 3 := by ring
  have hT2 : L1 * (I1 - Iρ) ≤ K ^ 2 * (2 + K) * a ^ 9 := by
    calc L1 * (I1 - Iρ) ≤ |L1 * (I1 - Iρ)| := le_abs_self _
      _ = |L1| * |I1 - Iρ| := abs_mul _ _
      _ ≤ (K * a ^ 8) * (K * (2 + K) * a ^ 3) := mul_le_mul V.hL1 hDiff (abs_nonneg _) (by positivity)
      _ = K ^ 2 * (2 + K) * a ^ 11 := by ring
      _ ≤ K ^ 2 * (2 + K) * a ^ 9 := mul_le_mul_of_nonneg_left (h9 11 (by norm_num)) (by positivity)
  have hT3 : -(s * I1) ≤ K ^ 2 * (2 + K) * a ^ 9 := by
    calc -(s * I1) ≤ |s * I1| := neg_le_abs _
      _ = |s| * |I1| := abs_mul _ _
      _ ≤ (K * a ^ 12) * (K * (2 + K)) := mul_le_mul V.hs hI1b (abs_nonneg _) (by positivity)
      _ = K ^ 2 * (2 + K) * a ^ 12 := by ring
      _ ≤ K ^ 2 * (2 + K) * a ^ 9 := mul_le_mul_of_nonneg_left (h9 12 (by norm_num)) (by positivity)
  have hA2 : |A| ≤ 2 * K * a ^ 8 := by
    have h12 : a ^ 12 ≤ a ^ 8 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
    calc |A| ≤ |L1| + |s| := abs_sub _ _
      _ ≤ K * a ^ 8 + K * a ^ 12 := add_le_add V.hL1 V.hs
      _ ≤ K * a ^ 8 + K * a ^ 8 := by gcongr
      _ = 2 * K * a ^ 8 := by ring
  have hT4 : A ^ 2 * I2 ≤ 4 * K ^ 3 * (1 + K) * a ^ 9 := by
    have h1 : A ^ 2 ≤ (2 * K * a ^ 8) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg A, neg_abs_le A] : -(2 * K * a ^ 8) ≤ A) ((le_abs_self A).trans hA2)
      exact this
    have h2 : (2 * K * a ^ 8) ^ 2 * (K * ((a⁻¹) ^ 3 + K * a⁻¹)) = 4 * K ^ 3 * (a ^ 13 + K * a ^ 15) := by
      field_simp
      norm_num
    calc A ^ 2 * I2 ≤ |A ^ 2 * I2| := le_abs_self _
      _ = A ^ 2 * |I2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg A)]
      _ ≤ (2 * K * a ^ 8) ^ 2 * (K * ((a⁻¹) ^ 3 + K * a⁻¹)) := mul_le_mul h1 hI2b (abs_nonneg _) (by positivity)
      _ = 4 * K ^ 3 * (a ^ 13 + K * a ^ 15) := h2
      _ ≤ 4 * K ^ 3 * ((1 + K) * a ^ 9) := by
          have h13 := h9 13 (by norm_num)
          have h15 := h9 15 (by norm_num)
          have : K * a ^ 15 ≤ K * a ^ 9 := mul_le_mul_of_nonneg_left h15 hK0
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith
      _ = 4 * K ^ 3 * (1 + K) * a ^ 9 := by ring
  have hA' : A * I1 = L1 * I1 - s * I1 := by rw [hA]; ring
  have hfinal : ID + A * I1 + A ^ 2 * I2 - L1 * Iρ = ID + L1 * (I1 - Iρ) + (-(s * I1)) + A ^ 2 * I2 := by
    rw [hA']; ring
  rw [hfinal]
  unfold AM
  nlinarith [hID, hT2, hT3, hT4]

end VacHyp


/-! ### The pointwise majorant and the integral of `vacG` -/

namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

lemma vacG_le_II {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ)
    (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) {u : ℝ} (hu : δ ≤ u) (hu2 : u ≤ 31 / 10 * δ) :
    vacG χ c δ s L1 P Φ u ≤ 11 * K ^ 4 * a ^ 3 ∧ -vacM0 P Φ L1 s u ≤ 16 * K ^ 4 * a ^ 3 := by
  have hY := V.Y_le_II hu hu2
  have hK4 : 0 ≤ K ^ 4 * a ^ 3 := by have := V.hK; have := V.ha; positivity
  have h1 := vacG_le_Q hχ V hκ hu
  have hg := V.gamma_range hu
  have hχ0 := hχ.mem ((u + s) / (3 * δ))
  have hc0 : 0 ≤ χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) := mul_nonneg hχ0.1 hg.1
  have hc1 : χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hχ0.2 hg.2 hg.1 zero_le_one
      _ = 1 := one_mul 1
  have hQ := V.Q_abs_le hu
  have hQ' : χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) * vacQ P Φ L1 s u ≤ |vacQ P Φ L1 s u| := by
    calc _ ≤ |χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) * vacQ P Φ L1 s u| := le_abs_self _
      _ = (χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹)) * |vacQ P Φ L1 s u| := by rw [abs_mul, abs_of_nonneg hc0]
      _ ≤ 1 * |vacQ P Φ L1 s u| := by gcongr
      _ = _ := one_mul _
  refine ⟨?_, ?_⟩
  · calc vacG χ c δ s L1 P Φ u ≤ _ := h1
      _ = χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) * vacQ P Φ L1 s u := by ring
      _ ≤ |vacQ P Φ L1 s u| := hQ'
      _ ≤ 4 / 3 * vacY P Φ L1 u := hQ
      _ ≤ 4 / 3 * (8 * K ^ 4 * a ^ 3) := by gcongr
      _ ≤ 11 * K ^ 4 * a ^ 3 := by nlinarith
  · have := V.M0_abs_le hu
    calc -vacM0 P Φ L1 s u ≤ |vacM0 P Φ L1 s u| := neg_le_abs _
      _ ≤ 2 * vacY P Φ L1 u := this
      _ ≤ 2 * (8 * K ^ 4 * a ^ 3) := by gcongr
      _ = 16 * K ^ 4 * a ^ 3 := by ring

lemma vacG_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {u : ℝ} (hu : u < δ) :
    vacG χ c δ s L1 P Φ u = 0 := by
  have hδ := V.hδpos
  unfold vacG
  rw [hχ.zero, zero_mul, zero_mul]
  rw [div_le_iff₀ (by positivity)]
  have := (abs_le.mp V.hs10).2
  linarith

end VacHyp

/-- The pointwise majorant of `vacG`. -/
noncomputable def vacMaj (K a δ L1 s : ℝ) (P : ℝ → ℝ) (Φ : ℝ → ℂ) (u : ℝ) : ℝ :=
  (Ioi (3 * δ)).indicator (vacM0 P Φ L1 s) u + (Icc δ (31 / 10 * δ)).indicator (fun _ => 27 * K ^ 4 * a ^ 3) u +
    (Ioi (31 / 10 * δ)).indicator (vacBR K a) u

lemma vacG_le_maj {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K a0 a1 a δ s L1 α κ Cfl I0 c : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}
    (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) (u : ℝ) :
    vacG χ c δ s L1 P Φ u ≤ vacMaj K a δ L1 s P Φ u := by
  have hδ := V.hδpos
  have hK4 : 0 ≤ K ^ 4 * a ^ 3 := by have := V.hK; have := V.ha; positivity
  unfold vacMaj
  by_cases h1 : u < δ
  · rw [V.vacG_zero hχ h1]
    have a1' : u ∉ Ioi (3 * δ) := by simp only [mem_Ioi, not_lt]; linarith
    have a2' : u ∉ Icc δ (31 / 10 * δ) := by simp only [mem_Icc, not_and, not_le]; intro h; linarith
    have a3' : u ∉ Ioi (31 / 10 * δ) := by simp only [mem_Ioi, not_lt]; linarith
    simp [Set.indicator_of_notMem, a1', a2', a3']
  by_cases h2 : u ≤ 31 / 10 * δ
  · obtain ⟨hG, hM⟩ := V.vacG_le_II hχ hκ (not_lt.mp h1) h2
    have a3' : u ∉ Ioi (31 / 10 * δ) := by simp only [mem_Ioi, not_lt]; exact h2
    have a2' : u ∈ Icc δ (31 / 10 * δ) := ⟨not_lt.mp h1, h2⟩
    rw [Set.indicator_of_notMem a3', Set.indicator_of_mem a2']
    by_cases h3 : u ∈ Ioi (3 * δ)
    · rw [Set.indicator_of_mem h3]; linarith
    · rw [Set.indicator_of_notMem h3]; linarith
  · have h2' := not_le.mp h2
    have a3 : u ∈ Ioi (31 / 10 * δ) := h2'
    have a1 : u ∈ Ioi (3 * δ) := by simp only [mem_Ioi]; linarith
    have a2 : u ∉ Icc δ (31 / 10 * δ) := by simp only [mem_Icc, not_and, not_le]; intro _; exact h2'
    rw [Set.indicator_of_mem a3, Set.indicator_of_mem a1, Set.indicator_of_notMem a2]
    linarith [vacG_le_III hχ V hκ h2']


lemma vacBR_eq {K a u : ℝ} (hu : 0 < u) :
    vacBR K a u = 2 * K * (8 * K ^ 3 + 1) * (a ^ 30 * u ^ (-(9 / 2 : ℝ)) + a ^ 24 * u ^ (-(7 / 2 : ℝ))) +
      (16 * K ^ 5 + 8 * K ^ 4) * a ^ 12 * u ^ (-(3 / 2 : ℝ)) := by
  unfold vacBR
  have e9 : (u ^ (-(1 / 2 : ℝ))) ^ 9 = u ^ (-(9 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have e7 : (u ^ (-(1 / 2 : ℝ))) ^ 7 = u ^ (-(7 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  rw [e9, e7, ← rpow_neg_three_half hu]

/-- The constant of `BR_integral_le`. -/
noncomputable def ABR (K : ℝ) : ℝ := 2 * K * (8 * K ^ 3 + 1) * (K ^ 7 + K ^ 5) + 2 * (16 * K ^ 5 + 8 * K ^ 4) * K

namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

/-- `b^{-1/2} ≤ K a^{-3}` for `b ≥ δ`. -/
lemma rpow_neg_half_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) {b : ℝ} (hb : δ ≤ b) :
    b ^ (-(1 / 2 : ℝ)) ≤ K * (a⁻¹) ^ 3 := by
  have hb0 : 0 < b := lt_of_lt_of_le V.hδpos hb
  have hK := V.hK
  have ha := V.ha
  have hKpos : 0 < K := by linarith
  have hT0 : 0 ≤ b ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hb0 _).le
  have hTsq := rpow_neg_half_sq hb0
  have hKa : K⁻¹ ≤ a0 := (inv_le_comm₀ V.ha0 hKpos).mp V.hKa0
  have hba : K⁻¹ * a ^ 6 ≤ b := by
    calc K⁻¹ * a ^ 6 ≤ a0 * a ^ 6 := by gcongr
      _ ≤ δ := V.hδ0
      _ ≤ b := hb
  have h1 : (b ^ (-(1 / 2 : ℝ))) ^ 2 ≤ (K * (a⁻¹) ^ 3) ^ 2 := by
    have h2 : (b ^ (-(1 / 2 : ℝ))) ^ 2 = b⁻¹ := by
      have : (b ^ (-(1 / 2 : ℝ))) ^ 2 * b = 1 := hTsq
      field_simp; linarith
    rw [h2]
    have h3 : b⁻¹ ≤ (K⁻¹ * a ^ 6)⁻¹ := inv_anti₀ (by positivity) hba
    have h4 : (K⁻¹ * a ^ 6)⁻¹ = K * (a ^ 6)⁻¹ := by field_simp
    have h5 : (K * (a⁻¹) ^ 3) ^ 2 = K ^ 2 * (a ^ 6)⁻¹ := by field_simp
    rw [h5]
    calc b⁻¹ ≤ K * (a ^ 6)⁻¹ := h3.trans h4.le
      _ ≤ K ^ 2 * (a ^ 6)⁻¹ := by
        have : K ≤ K ^ 2 := by nlinarith
        gcongr
  exact (pow_le_pow_iff_left₀ hT0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp h1

lemma BR_integral_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) :
    IntegrableOn (vacBR K a) (Ioi (31 / 10 * δ)) ∧ ∫ u in Ioi (31 / 10 * δ), vacBR K a u ≤ ABR K * a ^ 9 := by
  have hδ := V.hδpos
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  have ha := V.ha
  set b := 31 / 10 * δ with hbdef
  have hb : 0 < b := by positivity
  have hδb : δ ≤ b := by rw [hbdef]; linarith
  have TB := V.rpow_neg_half_le hδb
  set T := b ^ (-(1 / 2 : ℝ)) with hT
  have hT0 : 0 ≤ T := (Real.rpow_pos_of_pos hb _).le
  obtain ⟨i9, v9⟩ := integral_Ioi_rpow_neg (b := b) (r := 9 / 2) hb (by norm_num)
  obtain ⟨i7, v7⟩ := integral_Ioi_rpow_neg (b := b) (r := 7 / 2) hb (by norm_num)
  obtain ⟨i3, v3⟩ := integral_Ioi_rpow_neg (b := b) (r := 3 / 2) hb (by norm_num)
  have p9 : b ^ (1 - (9 / 2 : ℝ)) = T ^ 7 := by rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
  have p7 : b ^ (1 - (7 / 2 : ℝ)) = T ^ 5 := by rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
  have p3 : b ^ (1 - (3 / 2 : ℝ)) = T := by rw [hT]; norm_num
  rw [p9] at v9; rw [p7] at v7; rw [p3] at v3
  set C1 := 2 * K * (8 * K ^ 3 + 1) with hC1
  set C2 := 16 * K ^ 5 + 8 * K ^ 4 with hC2
  have hfun : ∀ u ∈ Ioi b, vacBR K a u =
      C1 * (a ^ 30 * u ^ (-(9 / 2 : ℝ)) + a ^ 24 * u ^ (-(7 / 2 : ℝ))) + C2 * a ^ 12 * u ^ (-(3 / 2 : ℝ)) :=
    fun u hu => vacBR_eq (lt_trans hb hu)
  have j9 : IntegrableOn (fun u : ℝ => a ^ 30 * u ^ (-(9 / 2 : ℝ))) (Ioi b) := i9.const_mul _
  have j7 : IntegrableOn (fun u : ℝ => a ^ 24 * u ^ (-(7 / 2 : ℝ))) (Ioi b) := i7.const_mul _
  have j97 : IntegrableOn (fun u : ℝ => a ^ 30 * u ^ (-(9 / 2 : ℝ)) + a ^ 24 * u ^ (-(7 / 2 : ℝ))) (Ioi b) := j9.add j7
  have jA : IntegrableOn (fun u : ℝ => C1 * (a ^ 30 * u ^ (-(9 / 2 : ℝ)) + a ^ 24 * u ^ (-(7 / 2 : ℝ)))) (Ioi b) :=
    j97.const_mul C1
  have jB : IntegrableOn (fun u : ℝ => C2 * a ^ 12 * u ^ (-(3 / 2 : ℝ))) (Ioi b) := i3.const_mul _
  have hI : IntegrableOn (fun u : ℝ => C1 * (a ^ 30 * u ^ (-(9 / 2 : ℝ)) + a ^ 24 * u ^ (-(7 / 2 : ℝ))) +
      C2 * a ^ 12 * u ^ (-(3 / 2 : ℝ))) (Ioi b) := jA.add jB
  refine ⟨hI.congr_fun (fun u hu => (hfun u hu).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hfun u hu)]
  have e1 := integral_add jA jB
  have e2 := integral_add j9 j7
  simp only [integral_const_mul] at e1 e2
  rw [e1, e2, v9, v7, v3]
  have hTK : T ≤ K * (a⁻¹) ^ 3 := TB
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  have t7 : T ^ 7 ≤ K ^ 7 * (a⁻¹) ^ 21 := by
    calc T ^ 7 ≤ (K * (a⁻¹) ^ 3) ^ 7 := pow_le_pow_left₀ hT0 hTK 7
      _ = K ^ 7 * (a⁻¹) ^ 21 := by ring
  have t5 : T ^ 5 ≤ K ^ 5 * (a⁻¹) ^ 15 := by
    calc T ^ 5 ≤ (K * (a⁻¹) ^ 3) ^ 5 := pow_le_pow_left₀ hT0 hTK 5
      _ = K ^ 5 * (a⁻¹) ^ 15 := by ring
  have q9 : a ^ 30 * (T ^ 7 / (9 / 2 - 1)) ≤ K ^ 7 * a ^ 9 := by
    calc a ^ 30 * (T ^ 7 / (9 / 2 - 1)) ≤ a ^ 30 * (T ^ 7) :=
          mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg hT0 7) (by norm_num)) (by positivity)
      _ ≤ a ^ 30 * (K ^ 7 * (a⁻¹) ^ 21) := by gcongr
      _ = K ^ 7 * a ^ 9 := by field_simp
  have q7 : a ^ 24 * (T ^ 5 / (7 / 2 - 1)) ≤ K ^ 5 * a ^ 9 := by
    calc a ^ 24 * (T ^ 5 / (7 / 2 - 1)) ≤ a ^ 24 * (T ^ 5) :=
          mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg hT0 5) (by norm_num)) (by positivity)
      _ ≤ a ^ 24 * (K ^ 5 * (a⁻¹) ^ 15) := by gcongr
      _ = K ^ 5 * a ^ 9 := by field_simp
  have q3 : (C2 * a ^ 12) * (T / (3 / 2 - 1)) ≤ 2 * C2 * K * a ^ 9 := by
    calc (C2 * a ^ 12) * (T / (3 / 2 - 1)) = 2 * C2 * a ^ 12 * T := by ring
      _ ≤ 2 * C2 * a ^ 12 * (K * (a⁻¹) ^ 3) := by gcongr
      _ = 2 * C2 * K * a ^ 9 := by field_simp
  unfold ABR
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add q9 q7) hC10]

end VacHyp


namespace VacHyp

variable {K a0 a1 a δ s L1 α κ Cfl I0 : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}

lemma vacG_meas {χ : ℝ → ℝ} (hχ : IsCutoff χ) (c : ℝ) (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) :
    Measurable (vacG χ c δ s L1 P Φ) := by
  have h1 : Measurable χ := hχ.smooth.continuous.measurable
  have h2 := V.hPm
  have h3 := V.hΦm
  unfold vacG physGamma physOsc physF uctIfl
  fun_prop

/-- The majorant is integrable, with `∫ vacMaj ≤ (AM + 57 K⁵ + ABR) a⁹`. -/
lemma maj_integral_le (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) :
    Integrable (vacMaj K a δ L1 s P Φ) ∧ ∫ u, vacMaj K a δ L1 s P Φ u ≤ (AM K + 57 * K ^ 5 + ABR K) * a ^ 9 := by
  have hδ := V.hδpos
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  have ha := V.ha
  obtain ⟨h1i, h1v⟩ := V.M0_integral_le
  obtain ⟨h3i, h3v⟩ := V.BR_integral_le
  have h2i : IntegrableOn (fun _ : ℝ => 27 * K ^ 4 * a ^ 3) (Icc δ (31 / 10 * δ)) := integrableOn_const (by simp)
  have e1 : Integrable ((Ioi (3 * δ)).indicator (vacM0 P Φ L1 s)) := (integrable_indicator_iff measurableSet_Ioi).mpr h1i
  have e2 : Integrable ((Icc δ (31 / 10 * δ)).indicator (fun _ : ℝ => 27 * K ^ 4 * a ^ 3)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr h2i
  have e3 : Integrable ((Ioi (31 / 10 * δ)).indicator (vacBR K a)) := (integrable_indicator_iff measurableSet_Ioi).mpr h3i
  have hmaj : vacMaj K a δ L1 s P Φ = fun u => (Ioi (3 * δ)).indicator (vacM0 P Φ L1 s) u +
      (Icc δ (31 / 10 * δ)).indicator (fun _ => 27 * K ^ 4 * a ^ 3) u +
      (Ioi (31 / 10 * δ)).indicator (vacBR K a) u := rfl
  refine ⟨by rw [hmaj]; exact (e1.add e2).add e3, ?_⟩
  have e12 : Integrable (fun u => (Ioi (3 * δ)).indicator (vacM0 P Φ L1 s) u +
      (Icc δ (31 / 10 * δ)).indicator (fun _ => 27 * K ^ 4 * a ^ 3) u) := e1.add e2
  rw [hmaj, integral_add e12 e3, integral_add e1 e2, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioi, setIntegral_const]
  have hvol : volume.real (Icc δ (31 / 10 * δ)) = 21 / 10 * δ := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  rw [hvol]
  simp only [smul_eq_mul]
  have h57 : 21 / 10 * δ * (27 * K ^ 4 * a ^ 3) ≤ 57 * K ^ 5 * a ^ 9 := by
    have hd : δ ≤ K * a ^ 6 := V.hδ1.trans (mul_le_mul_of_nonneg_right V.hKa1 (by positivity))
    calc 21 / 10 * δ * (27 * K ^ 4 * a ^ 3) ≤ 21 / 10 * (K * a ^ 6) * (27 * K ^ 4 * a ^ 3) := by gcongr
      _ = 56.7 * K ^ 5 * a ^ 9 := by ring
      _ ≤ 57 * K ^ 5 * a ^ 9 := by
        have : 0 ≤ K ^ 5 * a ^ 9 := by positivity
        nlinarith
  linarith

/-- `vacG` is integrable. -/
lemma vacG_integrable {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ)
    (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) : Integrable (vacG χ c δ s L1 P Φ) := by
  have hδ := V.hδpos
  have hK := V.hK
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨hmi, -⟩ := V.maj_integral_le
  have i3 := (integral_Ioi_rpow_neg (b := δ) (r := 3 / 2) hδ (by norm_num)).1
  have i3' : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ici δ) := (integrableOn_Ici_iff_integrableOn_Ioi).mpr i3
  have e3 : Integrable ((Ici δ).indicator (fun u : ℝ => 4 / 3 * K * u ^ (-(3 / 2 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ici).mpr (i3'.const_mul (4 / 3 * K))
  have h4 : ∀ u : ℝ, 0 ≤ (Ici δ).indicator (fun u : ℝ => 4 / 3 * K * u ^ (-(3 / 2 : ℝ))) u := by
    intro u
    apply Set.indicator_nonneg; intro x hx; have : 0 < x := lt_of_lt_of_le hδ hx; positivity
  refine Integrable.mono' (hmi.norm.add e3) (V.vacG_meas hχ c).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  by_cases hu : u < δ
  · rw [V.vacG_zero hχ hu, abs_zero]; exact add_nonneg (norm_nonneg _) (h4 u)
  have hu' : δ ≤ u := not_lt.mp hu
  have hu0 : 0 < u := lt_of_lt_of_le hδ hu'
  by_cases hneg : 0 ≤ vacG χ c δ s L1 P Φ u
  · rw [abs_of_nonneg hneg]
    have := vacG_le_maj hχ V hκ u
    have h5 : vacMaj K a δ L1 s P Φ u ≤ ‖vacMaj K a δ L1 s P Φ u‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    linarith [h4 u]
  · -- lower bound: `O ≥ 0`
    rw [abs_of_neg (not_le.mp hneg)]
    have hAu := V.sub_A hu'
    have hAp : 0 < u - (L1 - s) := by linarith
    have hg := V.gamma_range hu'
    have hχ0 := hχ.mem ((u + s) / (3 * δ))
    have hc0 : 0 ≤ χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) := mul_nonneg hχ0.1 hg.1
    have hc1 : χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hχ0.2 hg.2 hg.1 zero_le_one
        _ = 1 := one_mul 1
    have hP0 := V.hP0 u hu0
    have hO : 0 ≤ P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s)) := by positivity
    have hIfl : |uctIfl u| ≤ K * u ^ (-(3 / 2 : ℝ)) := by
      unfold uctIfl
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      exact mul_le_mul_of_nonneg_right V.hKf (Real.rpow_nonneg hu0.le _)
    have hFv : |u / (u - (L1 - s)) * uctIfl u| ≤ 4 / 3 * (K * u ^ (-(3 / 2 : ℝ))) := by
      rw [abs_mul, abs_of_pos (div_pos hu0 hAp)]
      have : u / (u - (L1 - s)) ≤ 4 / 3 := by
        rw [div_le_iff₀ hAp]; linarith
      exact mul_le_mul this hIfl (abs_nonneg _) (by norm_num)
    have heq := vacG_eq (χ := χ) (c := c) (δ := δ) (s := s) (L1 := L1) (P := P) (Φ := Φ) hκ hu0
    rw [heq]
    have hind : (Ici δ).indicator (fun u : ℝ => 4 / 3 * K * u ^ (-(3 / 2 : ℝ))) u = 4 / 3 * K * u ^ (-(3 / 2 : ℝ)) :=
      Set.indicator_of_mem (show u ∈ Ici δ from hu') _
    rw [hind]
    have hn : ‖vacMaj K a δ L1 s P Φ u‖ ≥ 0 := norm_nonneg _
    set c0 := χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) with hc0def
    have e : -(χ ((u + s) / (3 * δ)) * (1 - κ * (u ^ 3)⁻¹) * (P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s)) -
        u / (u - (L1 - s)) * uctIfl u)) = c0 * (u / (u - (L1 - s)) * uctIfl u - P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s))) := by
      rw [hc0def]; ring
    rw [e]
    have h6 : u / (u - (L1 - s)) * uctIfl u - P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s)) ≤ 4 / 3 * (K * u ^ (-(3 / 2 : ℝ))) :=
      by linarith [le_abs_self (u / (u - (L1 - s)) * uctIfl u)]
    have h7 : 0 ≤ 4 / 3 * (K * u ^ (-(3 / 2 : ℝ))) := by positivity
    calc c0 * (u / (u - (L1 - s)) * uctIfl u - P u * ‖(u : ℂ) - (L1 : ℂ) * Φ u‖ / (u - (L1 - s))) ≤ c0 * (4 / 3 * (K * u ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h6 hc0
      _ ≤ 1 * (4 / 3 * (K * u ^ (-(3 / 2 : ℝ)))) := mul_le_mul_of_nonneg_right hc1 h7
      _ = 4 / 3 * K * u ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ ‖vacMaj K a δ L1 s P Φ u‖ + 4 / 3 * K * u ^ (-(3 / 2 : ℝ)) := by linarith

end VacHyp


/-- **The vacuum integral at one `(ε, c)`**: under `VacHyp`, `∫ χ(L/3δ) γ(L̃)(O − F) dL ≤ (AM + 57K⁵ + ABR) a⁹`, `a⁹ = c^{-3/4}`. -/
theorem vac_core {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K a0 a1 a δ s L1 α κ Cfl I0 c : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}
    (V : VacHyp K a0 a1 a δ s L1 α κ Cfl I0 P Φ) (hκ : κ = (5 * π ^ 2 / 96) * c⁻¹ ^ 2) :
    (∫ x, χ (x / (3 * δ)) * physGamma c s x * (physOsc P Φ s L1 x - physF s L1 x)) ≤
      (VacHyp.AM K + 57 * K ^ 5 + ABR K) * a ^ 9 := by
  have hshift : (∫ x, χ (x / (3 * δ)) * physGamma c s x * (physOsc P Φ s L1 x - physF s L1 x)) =
      ∫ u, vacG χ c δ s L1 P Φ u :=
    (integral_add_right_eq_self (fun x => χ (x / (3 * δ)) * physGamma c s x * (physOsc P Φ s L1 x - physF s L1 x)) s).symm
  rw [hshift]
  obtain ⟨hmi, hmv⟩ := V.maj_integral_le
  calc ∫ u, vacG χ c δ s L1 P Φ u ≤ ∫ u, vacMaj K a δ L1 s P Φ u :=
        integral_mono (V.vacG_integrable hχ hκ) hmi (vacG_le_maj hχ V hκ)
    _ ≤ _ := hmv

/-- The smallness and `κ`-facts of `VacHyp` from the displays, for `a = c^{-1/12}` small (`10 K³ a² ≤ 1`) and `c⁻¹ = a^{12}`. -/
lemma VacHyp.of_disp {K a0 a1 a δ s L1 α Cfl I0 c : ℝ} {P : ℝ → ℝ} {Φ : ℝ → ℂ}
    (D : VacDisp K a0 a1 a δ s L1 α Cfl I0 P Φ) (hc : c⁻¹ = a ^ 12) (hsm : 10 * K ^ 3 * a ^ 2 ≤ 1)
    (hΦm : Measurable Φ) (hΦre : ∀ u, 0 < u → |(Φ u).re| ≤ K * min 1 ((u / a ^ 2) ^ 4))
    (hΦim : ∀ u, 0 < u → (Φ u).im ^ 2 ≤ K * min 1 ((u / a ^ 2) ^ 4)) :
    VacHyp K a0 a1 a δ s L1 α ((5 * π ^ 2 / 96) * c⁻¹ ^ 2) Cfl I0 P Φ := by
  have hK := D.hK
  have ha := D.ha
  have ha1 := D.ha1
  have hK0 : 0 < K := by linarith
  have hKa : K⁻¹ ≤ a0 := (inv_le_comm₀ D.ha0 hK0).mp D.hKa0
  have hδK : a ^ 6 / K ≤ δ := by
    calc a ^ 6 / K = K⁻¹ * a ^ 6 := by ring
      _ ≤ a0 * a ^ 6 := by gcongr
      _ ≤ δ := D.hδ0
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδK
  have ha2 : a ^ 2 ≤ 1 / (10 * K ^ 3) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hK3 : K ^ 2 ≤ K ^ 3 := by nlinarith
  have ha68 : a ^ 8 ≤ a ^ 6 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have ha126 : a ^ 12 ≤ a ^ 6 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have ha62 : a ^ 6 ≤ a ^ 2 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have hpi : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hκe : (5 * π ^ 2 / 96) * c⁻¹ ^ 2 = (5 * π ^ 2 / 96) * a ^ 24 := by rw [hc]; ring
  have hs := D.hs
  have hL1 := D.hL1
  -- δ/4 ≥ a⁶/(4K)
  have key : ∀ m : ℝ, 0 < m → m * K ≤ a ^ 6 → m ≤ δ := by
    intro m hm h
    have : m ≤ a ^ 6 / K := by rw [le_div_iff₀ hK0]; exact h
    exact this.trans hδK
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hΦm, hΦre, hΦim⟩
  · positivity
  · rw [hκe]
    have : 5 * π ^ 2 / 96 ≤ 1 := by nlinarith
    calc (5 * π ^ 2 / 96) * a ^ 24 ≤ 1 * a ^ 24 := by gcongr
      _ = a ^ 24 := one_mul _
  · -- `|L₁ - s| ≤ δ/4`
    have h1 : |L1 - s| ≤ 2 * K * a ^ 8 := by
      calc |L1 - s| ≤ |L1| + |s| := abs_sub _ _
        _ ≤ K * a ^ 8 + K * a ^ 12 := add_le_add hL1 hs
        _ ≤ K * a ^ 8 + K * a ^ 8 := add_le_add_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ha.le ha1 (show 8 ≤ 12 by norm_num)) hK0.le) _
        _ = 2 * K * a ^ 8 := by ring
    have h2 : 4 * (2 * K * a ^ 8) ≤ δ := by
      refine key _ (by positivity) ?_
      have : 4 * (2 * K * a ^ 8) * K = 8 * K ^ 2 * a ^ 2 * a ^ 6 := by ring
      rw [this]
      have : 8 * K ^ 2 * a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, pow_pos ha 2]
      nlinarith [pow_pos ha 6]
    linarith
  · have h2 : 10 * (K * a ^ 12) ≤ δ := by
      refine key _ (by positivity) ?_
      have : 10 * (K * a ^ 12) * K = 10 * K ^ 2 * a ^ 6 * a ^ 6 := by ring
      rw [this]
      have : 10 * K ^ 2 * a ^ 6 ≤ 1 := by nlinarith [pow_pos ha 6, pow_pos ha 2]
      nlinarith [pow_pos ha 6]
    linarith [hs]
  · have h2 : 2 * (K * a ^ 8 * K) ≤ δ := by
      refine key _ (by positivity) ?_
      have : 2 * (K * a ^ 8 * K) * K = 2 * K ^ 3 * a ^ 2 * a ^ 6 := by ring
      rw [this]
      have : 2 * K ^ 3 * a ^ 2 ≤ 1 := by nlinarith [pow_pos ha 2]
      nlinarith [pow_pos ha 6]
    calc |L1| * K ≤ K * a ^ 8 * K := by gcongr
      _ ≤ δ / 2 := by linarith
  · have h2 : 31 / 10 * δ ≤ 1 := by
      have : δ ≤ K * a ^ 6 := D.hδ1.trans (mul_le_mul_of_nonneg_right D.hKa1 (by positivity))
      have h3 : K * a ^ 6 ≤ K * a ^ 2 := by gcongr
      have h4 : K * a ^ 2 ≤ 1 / 10 := by nlinarith [pow_pos ha 2]
      linarith
    exact h2
  · rw [hκe]
    have hδ3 : (a ^ 6 / K) ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (by positivity) hδK 3
    have h1 : (δ ^ 3)⁻¹ ≤ ((a ^ 6 / K) ^ 3)⁻¹ := inv_anti₀ (by positivity) hδ3
    have h2 : ((a ^ 6 / K) ^ 3)⁻¹ = K ^ 3 * (a ^ 18)⁻¹ := by field_simp
    have hpi' : (5 * π ^ 2 / 96) ≤ 1 := by nlinarith
    have h3 : (5 * π ^ 2 / 96) * a ^ 24 * (δ ^ 3)⁻¹ ≤ 1 * a ^ 24 * (K ^ 3 * (a ^ 18)⁻¹) := by
      rw [← h2]; gcongr
    have h4 : 1 * a ^ 24 * (K ^ 3 * (a ^ 18)⁻¹) = K ^ 3 * a ^ 6 := by field_simp
    have h5 : K ^ 3 * a ^ 6 ≤ 1 := by nlinarith [pow_pos ha 2, pow_pos ha 6]
    linarith

/-- info: 'FormalResearch.SignUncertainty.FctSym.vac_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vac_core

end FormalResearch.SignUncertainty.FctSym

module

public import FormalResearch.SignUncertainty.MellinLiftTail

/-!
# The Hankel eigenfunction lift of a general `U.2` seed (M6)

`exists_hankelEigenfn_lift_general`: for a seed `X` with the `U.2` package (`HasU2 X`), a width `δ₀ ≥ 0`, `m`, `c > 3/2` and `σ = ±1`, if the edge
integrals decay like `|I_main[X] + σ I_dual[X]|(ξ) ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for large `ξ` (the hypothesis `htail'`, which for the one-level seeds is
`iMain_add_iDual_tail`), then the Mellin lift of `X` is a Hankel eigenfunction `f ∈ 𝒜_c^σ` with the edge representation, `f(0) = σ ∫ f ρ₀` and
`f(0) = W(c^{1/3}) + σ W(0)`, `W = liftSymbol X δ₀ m`.  The proof is that of `exists_hankelEigenfn_lift` with the one-level tail estimate replaced by `htail'`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

theorem exists_hankelEigenfn_lift_general {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ}
    (hc : 3 / 2 < c) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (htail' : ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain X δ₀ m c ξ + (σ : ℂ) * iDual X δ₀ m c ξ‖ ≤ C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) :
    ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain X δ₀ m c ξ + (σ : ℂ) * iDual X δ₀ m c ξ) ∧
      f 0 = σ * ∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ ∧
      ((f 0 : ℝ) : ℂ) = liftSymbol X δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) + (σ : ℂ) * liftSymbol X δ₀ m 0 := by
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := hc
  have hWd := liftSymbolData_of_hasU2 hX hδ m
  set Φ := liftPhi (liftSymbol (X) δ₀ m) c σ with hΦdef
  have hΦ : MellinLiftData c Φ := liftPhi_mellinLiftData hWd hc32 σ hσ
  obtain ⟨C, hC0, ξ₀, hξ₀, htail⟩ := htail'
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_liftFun_le hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  set ξ₁ : ℝ := max ξ₀ (Real.exp 1 / Real.pi ^ 2) with hξ₁
  have hξ₁0 : 0 < ξ₁ := lt_max_of_lt_left hξ₀
  have hmass : IntegrableOn (fun Δ => liftFun Φ (c / 2) Δ * hankelRho0 c Δ) (Ioi 0) := by
    refine integrableOn_mass_of_bounds (C := c ^ (-(1 / 3 : ℝ)) * C * c) hc0 (continuousOn_liftFun hΦ (by linarith) (by linarith))
      hC₀ (Δ₁ := c * ξ₁) (k := Real.pi ^ 2 / c) (by positivity) (by positivity) ?_ ?_
    · have : Real.pi ^ 2 / c * (c * ξ₁) = Real.pi ^ 2 * ξ₁ := by field_simp
      rw [this]
      have : Real.exp 1 ≤ Real.pi ^ 2 * ξ₁ := by
        have := le_max_right ξ₀ (Real.exp 1 / Real.pi ^ 2)
        rw [← hξ₁] at this
        rw [div_le_iff₀ (by positivity)] at this
        linarith
      exact Real.log_pos (by have := Real.exp_one_gt_d9; linarith)
    · intro Δ hΔ
      have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
      set ξ := Δ / c with hξdef
      have hξpos : 0 < ξ := div_pos hΔ0 hc0
      have hξge : ξ₀ ≤ ξ := by
        have : ξ₁ ≤ ξ := by rw [hξdef, le_div_iff₀ hc0]; linarith
        exact (le_max_left _ _).trans this
      have hcξ : c * ξ = Δ := by rw [hξdef]; field_simp
      have hrepr := lift_edge_repr hX hδ m hc32 hσ hξpos
      rw [hcξ] at hrepr
      have hnorm := htail ξ hξge
      rw [← hrepr, Complex.norm_real, Real.norm_eq_abs] at hnorm
      have hlog : Real.log (Real.pi ^ 2 / c * Δ) = Real.log (Real.pi ^ 2 * ξ) := by
        congr 1; rw [hξdef]; ring
      rw [hlog]
      have hc13 : 0 < c ^ (1 / 3 : ℝ) := by positivity
      have e : |c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * liftFun Φ (c / 2) Δ| = c ^ (1 / 3 : ℝ) * |liftFun Φ (c / 2) Δ * hankelRho0 c Δ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc13, abs_of_nonneg (hankelRho0_nonneg hc0 hΔ0.le)]
        ring
      rw [e] at hnorm
      have hΔξ : ξ⁻¹ = c * Δ⁻¹ := by rw [hξdef]; field_simp
      rw [hΔξ] at hnorm
      have h13 : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; simp
      have := mul_le_mul_of_nonneg_left hnorm (le_of_lt (Real.rpow_pos_of_pos hc0 (-(1 / 3 : ℝ))))
      calc |liftFun Φ (c / 2) Δ * hankelRho0 c Δ|
          = c ^ (-(1 / 3 : ℝ)) * (c ^ (1 / 3 : ℝ) * |liftFun Φ (c / 2) Δ * hankelRho0 c Δ|) := by
            rw [← mul_assoc, h13, one_mul]
        _ ≤ _ := this
        _ = _ := by ring
  obtain ⟨f, hf, hfeq, hf0⟩ := exists_isHankelEigenfn_of_lift hΦ hc32 hσ (x₀ := c / 2) (by linarith) (by linarith)
    (fun z hz0 hz1 => mellinMult_liftPhi_reflect hσ hc0 hz0 hz1) hmass
  have hint : (∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ) = ∫ Δ in Ioi (0 : ℝ), liftFun Φ (c / 2) Δ * hankelRho0 c Δ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    rw [hfeq Δ hΔ]
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro ξ hξ
    have h := lift_edge_repr hX hδ m hc32 hσ hξ
    rw [← h, hfeq (c * ξ) (by positivity)]
  · rw [hf0, hint]
  · have hlim : Tendsto (fun x : ℝ => Φ (x : ℂ)) (𝓝[<] c) (𝓝 (Φ (c : ℂ))) := by
      have hcn := liftPhi_continuousOn_edge hWd hc0 σ
      have hmap : Set.MapsTo (fun x : ℝ => (x : ℂ)) (Ioc 0 c) {z : ℂ | 0 < z.re ∧ z.re ≤ c} :=
        fun x hx => ⟨by simpa using hx.1, by simpa using hx.2⟩
      have h1 : ContinuousWithinAt (fun x : ℝ => Φ (x : ℂ)) (Ioc 0 c) c :=
        (hcn.comp Complex.continuous_ofReal.continuousOn hmap) c ⟨hc0, le_refl c⟩
      exact h1.tendsto.mono_left (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ioc_mem_nhdsLT hc0)))
    have hmv := liftFun_mass_value hΦ hc0 (x₀ := c / 2) (by linarith) (by linarith) hlim hmass
    have hv := liftPhi_edge_value (liftSymbol (X) δ₀ m) hc0 σ
    have hf0' : ((f 0 : ℝ) : ℂ) = (σ : ℂ) * ((∫ Δ in Ioi (0 : ℝ), liftFun Φ (c / 2) Δ * hankelRho0 c Δ : ℝ) : ℂ) := by
      rw [hf0, Complex.ofReal_mul]
    have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc0
    have hone : (((2 * Real.pi) ^ c / Real.Gamma c : ℝ) : ℂ) * ((((2 * Real.pi) ^ (-c) * Real.Gamma c : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have : (2 * Real.pi) ^ c / Real.Gamma c * ((2 * Real.pi) ^ (-c) * Real.Gamma c) = 1 := by
        rw [Real.rpow_neg (by positivity)]
        have : (0 : ℝ) < (2 * Real.pi) ^ c := Real.rpow_pos_of_pos (by positivity) c
        field_simp
      rw [this]; simp
    have hσσ : (σ : ℂ) * σ = 1 := by
      rcases hσ with rfl | rfl <;> simp
    rw [hf0', hmv, hΦdef, hv]
    calc (σ : ℂ) * ((((2 * Real.pi) ^ c / Real.Gamma c : ℝ) : ℂ) * (((((2 * Real.pi) ^ (-c) * Real.Gamma c : ℝ)) : ℂ) *
          (liftSymbol (X) δ₀ m 0 +
            (σ : ℂ) * liftSymbol (X) δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ))))
        = (σ : ℂ) * (((((2 * Real.pi) ^ c / Real.Gamma c : ℝ) : ℂ) * ((((2 * Real.pi) ^ (-c) * Real.Gamma c : ℝ)) : ℂ)) *
          (liftSymbol (X) δ₀ m 0 +
            (σ : ℂ) * liftSymbol (X) δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ))) := by ring
      _ = _ := by rw [hone]; linear_combination (liftSymbol (X) δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)) * hσσ


/-- info: 'FormalResearch.SignUncertainty.exists_hankelEigenfn_lift_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelEigenfn_lift_general

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.HankelBandAssembly
public import FormalResearch.SignUncertainty.HankelBootData

/-!
# The window bound for `W̃_c` from the band reduction (`teb:mellin` (2); M5-S6b)

`hankel_window_Wt_bound`: for `ζ = σ + iτ₀` in the annulus `0.9 ρ_R ≤ ‖ζ‖ ≤ 1.1 ρ_R` with
`σ ≥ 1.1 c^{-1/12} ‖ζ‖`, every point `σ + iy` of the window `|y - τ₀| ≤ h ≤ ‖ζ‖/10` obeys
`‖W̃_c(σ + iy)‖ ≤ C_Y c^{-5/6} (c^{1/3}(B₁ + B₂) + c^{-1/6}) · 1.1 ‖ζ‖/σ`, from `hankel_band_reduction`
(`cos ψ = σ/‖σ + iy‖ ≥ σ/(1.1 ‖ζ‖)`).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

lemma norm_window_diff (σ τ0 y : ℝ) :
    ‖((σ : ℂ) + (y : ℂ) * Complex.I) - ((σ : ℂ) + (τ0 : ℂ) * Complex.I)‖ = |y - τ0| := by
  have : ((σ : ℂ) + (y : ℂ) * Complex.I) - ((σ : ℂ) + (τ0 : ℂ) * Complex.I) =
      ((y - τ0 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]

theorem hankel_window_Wt_bound {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c)
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hB12 : 0 ≤ hankelBootB1 c f R u_T + hankelBootB2 c f R)
    {σ τ0 h : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hρlo : 9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖)
    (hρhi : ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R)
    (hh : h ≤ 1 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖)
    (hcz : 11 / 10 * c ^ (-(1 / 12 : ℝ)) * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ σ)
    {y : ℝ} (hy : |y - τ0| ≤ h) :
    ‖hankelWt c f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      tebBandConst hankelBandParams * c ^ (-(5 / 6 : ℝ)) *
        (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + c ^ (-(1 / 6 : ℝ))) *
        (11 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ / σ) := by
  have hc0 : 0 < c := by linarith
  set ζ : ℂ := (σ : ℂ) + (τ0 : ℂ) * Complex.I with hζ
  set ζ0 : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I with hζ0
  have hρ0 : 0 ≤ rhoR hankelBandParams c R := by
    unfold rhoR
    have := hankelBandParams.hκ_ζ
    positivity
  have hdiff : ‖ζ0 - ζ‖ = |y - τ0| := norm_window_diff σ τ0 y
  have hd1 := norm_sub_norm_le ζ0 ζ
  have hd2 := norm_sub_norm_le ζ ζ0
  rw [norm_sub_rev] at hd2
  rw [hdiff] at hd1 hd2
  have hζ0lo : 9 / 10 * ‖ζ‖ ≤ ‖ζ0‖ := by linarith
  have hζ0hi : ‖ζ0‖ ≤ 11 / 10 * ‖ζ‖ := by linarith
  have hζn : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hζ0pos : 0 < ‖ζ0‖ := by
    have : σ ≤ ‖ζ0‖ := by
      have := Complex.re_le_norm ζ0
      simpa [hζ0] using this
    linarith
  have hre : ζ0.re = σ := by simp [hζ0]
  have hlo : rhoR hankelBandParams c R / 3 ≤ ‖ζ0‖ := by nlinarith
  have hhi : ‖ζ0‖ ≤ 2 * rhoR hankelBandParams c R := by nlinarith
  have hq : σ / ‖ζ0‖ ≤ 1 := by
    rw [div_le_one hζ0pos]
    have := Complex.re_le_norm ζ0
    rwa [hre] at this
  have hcos_eq : ζ0.re = ‖ζ0‖ * Real.cos (Real.arccos (σ / ‖ζ0‖)) := by
    rw [Real.cos_arccos (by have : 0 ≤ σ / ‖ζ0‖ := by positivity
                            linarith) hq, hre]
    field_simp
  set ψ := Real.arccos (σ / ‖ζ0‖) with hψ
  have hcosψ : Real.cos ψ = σ / ‖ζ0‖ := by
    rw [hψ, Real.cos_arccos (by have : 0 ≤ σ / ‖ζ0‖ := by positivity
                                linarith) hq]
  have hcos : c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by
    rw [hcosψ, le_div_iff₀ hζ0pos]
    nlinarith [Real.rpow_pos_of_pos hc0 (-(1 / 12 : ℝ))]
  have hRlb' := hRlb
  have hbr := hankel_band_reduction hc hε hf.toIsHankelEigenfn hM hu0 hu3 hRlb hRub
    (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ)) hlo hhi hcos_eq hcos
  rw [hankelWtS_eq (by linarith) hf.toIsHankelEigenfn (by rw [hre]; exact hσ0.le)
    (by rw [hre]; exact hσ1)] at hbr
  have hB1 := hankelBoot_bandB1_eq hc hf hε hM hT hu0 hu3 hRlb hRub
  have hB2 := hankelBoot_bandB2_eq hc hf hε hM hT hu0 hu3 hRlb hRub
  rw [hB1, hB2] at hbr
  refine hbr.trans ?_
  set Q := tebBandConst hankelBandParams * c ^ (-(5 / 6 : ℝ)) *
        (c ^ (1 / 3 : ℝ) * (hankelBootB1 c f R u_T + hankelBootB2 c f R) + c ^ (-(1 / 6 : ℝ))) with hQ
  have hQ0 : 0 ≤ Q := by
    have := tebBandConst_pos hankelBandParams
    have h1 : 0 ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
    have h2 : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    have h3 : 0 ≤ c ^ (-(1 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
    rw [hQ]; positivity
  rw [hcosψ]
  have hr : ‖ζ0‖ / σ ≤ 11 / 10 * ‖ζ‖ / σ := by
    apply div_le_div_of_nonneg_right _ hσ0.le; exact hζ0hi
  calc Q / (σ / ‖ζ0‖) = Q * (‖ζ0‖ / σ) := by field_simp
    _ ≤ Q * (11 / 10 * ‖ζ‖ / σ) := by gcongr

/-- info: 'FormalResearch.SignUncertainty.hankel_window_Wt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_window_Wt_bound

end FormalResearch.SignUncertainty

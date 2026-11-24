module

public import FormalResearch.SignUncertainty.HankelWindowGeom
public import FormalResearch.SignUncertainty.HankelWindowAux
public import FormalResearch.SignUncertainty.HankelLocalEnvelope

/-!
# Saddle geometry of the window lemma (M5-S6b)

`hankel_window_saddle`: for a Langer point `ũ` with `R - 1 ≤ ‖ũ‖ ≤ R + 1`, `2 c^{-1/12} √‖ũ‖ ≤ Re ũ^{1/2}` and its
saddle `ζ₊ = σ + iτ₀`, the window `|y - τ₀| ≤ h`, `h² = 5 log c/(cσ)`, lies in the annulus of the band reduction
with `σ ≥ 1.1 c^{-1/12} ‖ζ₊‖` (all numerical, `c ≥ 10¹⁴`).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

set_option maxHeartbeats 4000000 in
theorem hankel_window_saddle {c R : ℝ} {u q : ℂ} (hc : 1e14 ≤ c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hlo : R - 1 ≤ ‖u‖) (hhi : ‖u‖ ≤ R + 1)
    (hX : 2 * c ^ (-(1 / 12 : ℝ)) * √‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re)
    (hq : q ∈ slitPlane) (hqn : ‖q‖ ≤ 0.035 ^ 2) (hqu : langerUtilde etaC c q = u) :
    ∃ σ τ0 h : ℝ, saddleRoot q = (σ : ℂ) + (τ0 : ℂ) * Complex.I ∧ 0 < σ ∧ σ ≤ 0.035 ∧ |τ0| ≤ 0.035 ∧
      0 ≤ h ∧ h ^ 2 = 5 * Real.log c / (c * σ) ∧
      9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ∧
      ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R ∧
      h ≤ 1 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ∧
      11 / 10 * c ^ (-(1 / 12 : ℝ)) * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ σ ∧
      ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ / σ ≤ 1.002 * ‖u‖ ^ (1 / 2 : ℝ) / (u ^ (1 / 2 : ℂ)).re ∧
      (u ^ (1 / 2 : ℂ)).re ≤ c ^ (1 / 3 : ℝ) * σ ∧ c ^ (1 / 3 : ℝ) ≤ 0.035 * c * σ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht14, hct, hk4, hK8, hτi, hc56, hlog⟩ := hankel_window_cnum hc
  have ht0 : 0 < t := by linarith
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  -- numerics of the radius
  have ht8 : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
  have ht8' : (1.4e9 : ℝ) ≤ t ^ 8 := by norm_num at ht8; linarith
  have hRlb8 : (1 / 100 : ℝ) ^ 2 * t ^ 8 ≤ R := by rw [← hK8]; exact hRlb
  have hRub8 : R ≤ (1 / 100 : ℝ) ^ 2 * t ^ 8 + 1 := by rw [← hK8]; exact hRub
  have hR1 : 1e5 ≤ R := by nlinarith
  have hRc : R + 1 ≤ t ^ 8 := by nlinarith
  have hkap := hankelLangerKappa_bounds
  have hRdisc : R + 1 ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [hK8]; nlinarith
  have hRA : R ≤ langerRadius c := by
    have : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    rw [this]; linarith
  -- the point u
  set N : ℝ := ‖u‖ with hNdef
  have hN1 : 9e4 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hNdef; linarith
  set s : ℝ := N ^ (1 / 2 : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hN0 _
  have hsqrtN : Real.sqrt N = s := by rw [hsdef, Real.sqrt_eq_rpow]
  set X : ℝ := (u ^ (1 / 2 : ℂ)).re with hXdef
  rw [hτi, hsqrtN] at hX
  have hτi0 : 0 < t⁻¹ := inv_pos.2 ht0
  have hX0 : 0 < X := by
    have : 0 < 2 * t⁻¹ * s := by positivity
    linarith
  have hgeom := hankel_saddle_geom hc0 hq hqn hqu
  set ζ := saddleRoot q with hζdef
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hqn
  have hσpos : 0 < ζ.re := re_saddleRoot_pos hq
  obtain ⟨σ, τ0, hζeq⟩ : ∃ σ τ0 : ℝ, ζ = (σ : ℂ) + (τ0 : ℂ) * Complex.I :=
    ⟨ζ.re, ζ.im, by apply Complex.ext <;> simp⟩
  have hσre : ζ.re = σ := by rw [hζeq]; simp
  have hτ0im : ζ.im = τ0 := by rw [hζeq]; simp
  rw [hσre] at hσpos hgeom
  have hσle : σ ≤ 0.035 := hσre ▸ ((Complex.re_le_norm ζ).trans hζn)
  have hτ0 : |τ0| ≤ 0.035 := hτ0im ▸ ((Complex.abs_im_le_norm ζ).trans hζn)
  have hσ1 : σ < 1 := by linarith
  obtain ⟨g1, g2, g3, g4⟩ := hgeom
  have hμ := langerMu_lt
  have hμ0 := langerMu_pos
  set M : ℝ := k * langerMu with hMdef
  have g1 : 0.9991 * M * ‖ζ‖ ≤ s := g1
  have g2 : s ≤ 1.0009 * M * ‖ζ‖ := g2
  have g3 : 0.9991 * M * σ ≤ X := g3
  have g4 : X ≤ 1.0009 * M * σ := g4
  have hM0 : 0 < M := mul_pos hk0 hμ0
  have hMle : M ≤ 3 / 4 * t ^ 4 := by
    rw [hMdef, hk4]; nlinarith [pow_pos ht0 4]
  have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  -- `σ ≳ ‖ζ‖ / t`
  have hσt : 1.99 * ‖ζ‖ ≤ t * σ := by
    have h1 : 2 * t⁻¹ * (0.9991 * M * ‖ζ‖) ≤ 2 * t⁻¹ * s := by
      have := mul_le_mul_of_nonneg_left g1 (by positivity : (0 : ℝ) ≤ 2 * t⁻¹)
      linarith
    have h2 : M * (1.9982 * t⁻¹ * ‖ζ‖) ≤ M * (1.0009 * σ) := by nlinarith
    have h3 : 1.9982 * t⁻¹ * ‖ζ‖ ≤ 1.0009 * σ := le_of_mul_le_mul_left h2 hM0
    have h4 : t * (1.9982 * t⁻¹ * ‖ζ‖) ≤ t * (1.0009 * σ) := mul_le_mul_of_nonneg_left h3 ht0.le
    have e : t * (1.9982 * t⁻¹ * ‖ζ‖) = 1.9982 * ‖ζ‖ := by field_simp
    nlinarith
  -- annulus
  set R' := Real.sqrt R with hR'
  have hR'0 : 0 < R' := Real.sqrt_pos.2 (by linarith)
  have hR'sq : R' ^ 2 = R := Real.sq_sqrt (by linarith)
  have hsR1 : 0.99 * R' ≤ s := by
    have : (0.99 * R') ^ 2 ≤ s ^ 2 := by
      have : s ^ 2 = N := by rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      rw [this]; nlinarith
    exact abs_le_of_sq_le_sq' this hs0.le |>.2
  have hsR2 : s ≤ 1.01 * R' := by
    have : s ^ 2 ≤ (1.01 * R') ^ 2 := by
      have : s ^ 2 = N := by rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      rw [this]; nlinarith
    exact abs_le_of_sq_le_sq' this (by positivity) |>.2
  have hρ : rhoR hankelBandParams c R = R' / M := rhoR_hankel_eq hc0
  have hζlo : 9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ := by
    rw [← hζeq, hρ, mul_div_assoc', div_le_iff₀ hM0]
    nlinarith
  have hζhi : ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R := by
    rw [← hζeq, hρ, mul_div_assoc', le_div_iff₀ hM0]
    nlinarith
  -- absolute lower bound for `‖ζ‖`
  have hR't : 0.01 * t ^ 4 ≤ R' := by
    rw [hR']
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hζabs : 0.012 ≤ ‖ζ‖ := by
    have h1 : 0.009 * t ^ 4 ≤ M * ‖ζ‖ := by
      have : 0.9 * R' ≤ M * ‖ζ‖ := by
        have := hζlo
        rw [← hζeq, hρ, mul_div_assoc', div_le_iff₀ hM0] at this
        linarith
      nlinarith
    have h2 : M * ‖ζ‖ ≤ 3 / 4 * t ^ 4 * ‖ζ‖ := mul_le_mul_of_nonneg_right hMle hζ0
    have h3 : 0 < t ^ 4 := pow_pos ht0 4
    by_contra hlt
    push Not at hlt
    nlinarith
  -- size of `cσ` and the window width `h`
  have ht11 : (14 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht14 7
  have ht10 : (14 : ℝ) ^ 10 ≤ t ^ 10 := pow_le_pow_left₀ (by norm_num) ht14 10
  have hσ' : 0.0238 * t ^ 11 ≤ c * σ := by
    have : c * σ = t ^ 11 * (t * σ) := by rw [hct]; ring
    rw [this]
    have h11 : 0 < t ^ 11 := pow_pos ht0 11
    nlinarith
  have hcσ0 : 0 < c * σ := by positivity
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set h : ℝ := Real.sqrt (5 * Real.log c / (c * σ)) with hhdef
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhsq : h ^ 2 = 5 * Real.log c / (c * σ) := Real.sq_sqrt (by positivity)
  have hhle : h ≤ 1 / 10 * ‖ζ‖ := by
    rw [hhdef]
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    rw [div_le_iff₀ hcσ0]
    have h1 : (1.44e-6 : ℝ) ≤ (1 / 10 * ‖ζ‖) ^ 2 := by nlinarith
    have h2 : (60 : ℝ) * t ≤ 3.4e-8 * t ^ 11 := by
      have : t ^ 11 = t * t ^ 10 := by ring
      rw [this]; nlinarith
    have h3 : 3.4e-8 * t ^ 11 ≤ (1.44e-6 : ℝ) * (0.0238 * t ^ 11) := by nlinarith [pow_pos ht0 11]
    have h4 : (1.44e-6 : ℝ) * (0.0238 * t ^ 11) ≤ (1 / 10 * ‖ζ‖) ^ 2 * (c * σ) := by
      have := mul_le_mul h1 hσ' (by positivity) (by positivity)
      linarith
    nlinarith
  have hcz : 11 / 10 * c ^ (-(1 / 12 : ℝ)) * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ σ := by
    rw [← hζeq, hτi]
    have h3 : 1.99 * t⁻¹ * ‖ζ‖ ≤ σ := by
      have := mul_le_mul_of_nonneg_left hσt hτi0.le
      have e : t⁻¹ * (t * σ) = σ := by field_simp
      nlinarith
    nlinarith
  refine ⟨σ, τ0, h, hζeq, hσpos, hσle, hτ0, hh0, hhsq, hζlo, hζhi, (by rw [← hζeq]; exact hhle), hcz, ?_, ?_, ?_⟩
  · rw [← hζeq]
    rw [div_le_div_iff₀ hσpos hX0]
    have h1 := mul_le_mul_of_nonneg_left g4 hζ0
    have h2 := mul_le_mul_of_nonneg_right g1 hσpos.le
    nlinarith
  · have h1 : X ≤ 1.0009 * M * σ := g4
    have h2 : M ≤ 3 / 4 * k := by rw [hMdef]; nlinarith
    nlinarith [mul_pos hk0 hσpos]
  · have h2 : 0.035 * c * σ ≥ 0.035 * (0.0238 * t ^ 11) := by nlinarith
    have h3 : t ^ 11 = t ^ 4 * t ^ 7 := by ring
    rw [hk4]
    have h4 : (14 : ℝ) ^ 7 ≤ t ^ 7 := ht11
    have h5 : 0 < t ^ 4 := pow_pos ht0 4
    nlinarith

end FormalResearch.SignUncertainty

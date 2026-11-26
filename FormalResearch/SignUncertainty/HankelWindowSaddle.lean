module

public import FormalResearch.SignUncertainty.HankelWindowGeom
public import FormalResearch.SignUncertainty.HankelWindowAux
public import FormalResearch.SignUncertainty.HankelLocalEnvelope

/-!
# Saddle geometry of the window lemma (M5-S6b)

`hankel_window_saddle`: for a Langer point `ũ` with `R - 1 ≤ ‖ũ‖ ≤ R + 1`, `θ √‖ũ‖ ≤ Re ũ^{1/2}` (`θ √c ≥ 10⁵`, i.e. `sin φ ≥ θ`
with `θ ≥ 10⁵ c^{-1/2}`; this covers the angular range `sin φ ≥ C₂ R^{-3/4} (log c)^{1/2}` of `(ct:cov)`) and its saddle
`ζ₊ = σ + iτ₀`, the window `|y - τ₀| ≤ h`, `h² = 5 log c/(cσ)`, lies in the annulus of the band reduction
with `cσ ≥ 1190 c^{1/2}` (all numerical, `c ≥ 10¹⁴`).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

set_option maxHeartbeats 4000000 in
/-- **Window geometry** (numerical, `c ≥ 10¹⁴`): for `ũ = ũ(q)` (`q` off the cut, `‖q‖ ≤ 0.035²`) on the annulus `R - 1 ≤ ‖ũ‖ ≤ R + 1`
with `θ √‖ũ‖ ≤ Re ũ^{1/2}`, `10⁵ ≤ θ √c` and saddle `ζ₊ = q^{1/2} = σ + iτ₀`, the window half-width `h = √(5 log c/(cσ))` satisfies
`h ≤ ‖ζ₊‖/10`, `‖ζ₊‖ ∈ [0.9, 1.1] ρ_R` (so the window lies in the band-reduction annulus); also
`‖ζ₊‖/σ ≤ 1.002 ‖ũ‖^{1/2}/Re ũ^{1/2}`, `Re ũ^{1/2} ≤ c^{1/3} σ` and `c^{1/3} ≤ 0.035 c σ`.  The radius `R` is the free window
radius `[b² c^{2/3}, b² c^{2/3} + 1]` (`b = 1/100`); inside the proof `R + 1 ≤ langerRadius c`, so the annulus lies in the Langer disc.
(The earlier form assumed `θ = 2 c^{-1/12}` and also concluded `σ ≥ 1.1 c^{-1/12} ‖ζ₊‖`; that conclusion is not used by the window lemma.) -/
theorem hankel_window_saddle {c R : ℝ} {u q : ℂ} (hc : 1e14 ≤ c)
    (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hlo : R - 1 ≤ ‖u‖) (hhi : ‖u‖ ≤ R + 1)
    {θ : ℝ} (hθ : 1e5 ≤ θ * √c) (hX : θ * √‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re)
    (hq : q ∈ slitPlane) (hqn : ‖q‖ ≤ 0.035 ^ 2) (hqu : langerUtilde etaC c q = u) :
    ∃ σ τ0 h : ℝ, saddleRoot q = (σ : ℂ) + (τ0 : ℂ) * Complex.I ∧ 0 < σ ∧ σ ≤ 0.035 ∧ |τ0| ≤ 0.035 ∧
      0 ≤ h ∧ h ^ 2 = 5 * Real.log c / (c * σ) ∧
      9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ∧
      ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R ∧
      h ≤ 1 / 10 * ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ∧
      ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ / σ ≤ 1.002 * ‖u‖ ^ (1 / 2 : ℝ) / (u ^ (1 / 2 : ℂ)).re ∧
      (u ^ (1 / 2 : ℂ)).re ≤ c ^ (1 / 3 : ℝ) * σ ∧ c ^ (1 / 3 : ℝ) ≤ 0.035 * c * σ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht14, hct, hk4, hK8, -, hc56, hlog⟩ := hankel_window_cnum hc
  have ht0 : 0 < t := by linarith
  set k : ℝ := c ^ (1 / 3 : ℝ) with hkdef
  have hk0 : 0 < k := Real.rpow_pos_of_pos hc0 _
  -- numerics of the radius
  have ht8 : (14 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht14 8
  have ht8' : (1.4e9 : ℝ) ≤ t ^ 8 := by norm_num at ht8; linarith
  have hRlb8 : (1 / 100 : ℝ) ^ 2 * t ^ 8 ≤ R := by rw [← hK8]; exact hRlb
  have hRub8 : R ≤ (1 / 100 : ℝ) ^ 2 * t ^ 8 + 1 := by rw [← hK8]; exact hRub
  have hR1 : 1e5 ≤ R := by nlinarith only [hRlb8, ht8']
  have hRc : R + 1 ≤ t ^ 8 := by nlinarith only [hRub8, ht8']
  obtain ⟨hκ1, hκ2⟩ := hankelLangerKappa_bounds
  have hRdisc : R + 1 ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [hK8]; nlinarith only [hRub8, ht8', mul_nonneg (sub_nonneg.2 hκ1) (pow_pos ht0 8).le]
  have hRA : R ≤ langerRadius c := by
    have : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
    rw [this]; linarith only [hRdisc]
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
  rw [hsqrtN] at hX
  have hsqc : √c = t ^ 6 := by
    rw [hct, show t ^ 12 = (t ^ 6) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hθt : 1e5 ≤ θ * t ^ 6 := by rwa [hsqc] at hθ
  have hθ0 : 0 < θ := by
    by_contra hneg
    push Not at hneg
    nlinarith only [hθt, hneg, pow_pos ht0 6]
  have hX0 : 0 < X := by
    have : 0 < θ * s := by positivity
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
    rw [hMdef, hk4]; nlinarith only [mul_nonneg (sub_nonneg.2 hμ.le) (pow_pos ht0 4).le]
  have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  -- annulus
  set R' := Real.sqrt R with hR'
  have hR'0 : 0 < R' := Real.sqrt_pos.2 (by linarith)
  have hR'sq : R' ^ 2 = R := Real.sq_sqrt (by linarith)
  have hsR1 : 0.99 * R' ≤ s := by
    have : (0.99 * R') ^ 2 ≤ s ^ 2 := by
      have : s ^ 2 = N := by rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      rw [this]; nlinarith only [hR'sq, hlo, hR1]
    exact abs_le_of_sq_le_sq' this hs0.le |>.2
  have hsR2 : s ≤ 1.01 * R' := by
    have : s ^ 2 ≤ (1.01 * R') ^ 2 := by
      have : s ^ 2 = N := by rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      rw [this]; nlinarith only [hR'sq, hhi, hR1]
    exact abs_le_of_sq_le_sq' this (by positivity) |>.2
  have hρ : rhoR hankelBandParams c R = R' / M := rhoR_hankel_eq hc0
  have hζlo : 9 / 10 * rhoR hankelBandParams c R ≤ ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ := by
    rw [← hζeq, hρ, mul_div_assoc', div_le_iff₀ hM0]
    linarith only [g2, hsR1, hR'0]
  have hζhi : ‖(σ : ℂ) + (τ0 : ℂ) * Complex.I‖ ≤ 11 / 10 * rhoR hankelBandParams c R := by
    rw [← hζeq, hρ, mul_div_assoc', le_div_iff₀ hM0]
    linarith only [g1, hsR2, hR'0]
  -- absolute lower bound for `‖ζ‖`
  have hR't : 0.01 * t ^ 4 ≤ R' := by
    rw [hR']
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hRlb8]
  have hζabs : 0.012 ≤ ‖ζ‖ := by
    have h1 : 0.009 * t ^ 4 ≤ M * ‖ζ‖ := by
      have : 0.9 * R' ≤ M * ‖ζ‖ := by
        have := hζlo
        rw [← hζeq, hρ, mul_div_assoc', div_le_iff₀ hM0] at this
        linarith only [this]
      linarith only [this, hR't]
    have h2 : M * ‖ζ‖ ≤ 3 / 4 * t ^ 4 * ‖ζ‖ := mul_le_mul_of_nonneg_right hMle hζ0
    have h3 : 0 < t ^ 4 := pow_pos ht0 4
    by_contra hlt
    push Not at hlt
    nlinarith only [h1, h2, h3, mul_pos (sub_pos.2 hlt) h3]
  -- size of `cσ` and the window width `h`
  have ht11 : (14 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht14 7
  have ht10 : (14 : ℝ) ^ 10 ≤ t ^ 10 := pow_le_pow_left₀ (by norm_num) ht14 10
  have hσθ : 0.998 * θ * ‖ζ‖ ≤ σ := by
    have h1 : θ * (0.9991 * M * ‖ζ‖) ≤ θ * s := mul_le_mul_of_nonneg_left g1 hθ0.le
    have h2 : M * (0.9991 * θ * ‖ζ‖) ≤ M * (1.0009 * σ) := by nlinarith only [h1, hX, g4]
    have h3 : 0.9991 * θ * ‖ζ‖ ≤ 1.0009 * σ := le_of_mul_le_mul_left h2 hM0
    nlinarith only [h3, mul_nonneg hθ0.le hζ0]
  have hσ' : 1190 * t ^ 6 ≤ c * σ := by
    have : c * σ = t ^ 6 * (t ^ 6 * σ) := by rw [hct]; ring
    rw [this]
    have h1 : t ^ 6 * (0.998 * θ * ‖ζ‖) ≤ t ^ 6 * σ := mul_le_mul_of_nonneg_left hσθ (by positivity)
    have h2 : 1e5 * ‖ζ‖ ≤ (θ * t ^ 6) * ‖ζ‖ := mul_le_mul_of_nonneg_right hθt hζ0
    have h3 : 1190 ≤ t ^ 6 * σ := by nlinarith only [h1, h2, hζabs]
    nlinarith only [mul_le_mul_of_nonneg_left h3 (pow_pos ht0 6).le]
  have hcσ0 : 0 < c * σ := by positivity
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  set h : ℝ := Real.sqrt (5 * Real.log c / (c * σ)) with hhdef
  have hh0 : 0 ≤ h := Real.sqrt_nonneg _
  have hhsq : h ^ 2 = 5 * Real.log c / (c * σ) := Real.sq_sqrt (by positivity)
  have hhle : h ≤ 1 / 10 * ‖ζ‖ := by
    rw [hhdef]
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    rw [div_le_iff₀ hcσ0]
    have h1 : (1.44e-6 : ℝ) ≤ (1 / 10 * ‖ζ‖) ^ 2 := by nlinarith only [hζabs, mul_nonneg (sub_nonneg.2 hζabs) (sub_nonneg.2 hζabs)]
    have h2 : (60 : ℝ) * t ≤ 1.7e-3 * t ^ 6 := by
      have h5 : (14 : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by norm_num) ht14 5
      have : t ^ 6 = t * t ^ 5 := by ring
      rw [this]; nlinarith only [mul_le_mul_of_nonneg_left h5 ht0.le, ht0]
    have h3 : 1.7e-3 * t ^ 6 ≤ (1.44e-6 : ℝ) * (1190 * t ^ 6) := by nlinarith only [pow_pos ht0 6]
    have h4 : (1.44e-6 : ℝ) * (1190 * t ^ 6) ≤ (1 / 10 * ‖ζ‖) ^ 2 * (c * σ) := by
      have := mul_le_mul h1 hσ' (by positivity) (by positivity)
      linarith only [this]
    linarith only [hlog, h2, h3, h4]
  refine ⟨σ, τ0, h, hζeq, hσpos, hσle, hτ0, hh0, hhsq, hζlo, hζhi, (by rw [← hζeq]; exact hhle), ?_, ?_, ?_⟩
  · rw [← hζeq]
    rw [div_le_div_iff₀ hσpos hX0]
    have h1 := mul_le_mul_of_nonneg_left g4 hζ0
    have h2 := mul_le_mul_of_nonneg_right g1 hσpos.le
    nlinarith only [h1, h2, mul_pos hs0 hσpos]
  · have h1 : X ≤ 1.0009 * M * σ := g4
    have h2 : M ≤ 3 / 4 * k := by rw [hMdef]; nlinarith only [mul_nonneg (sub_nonneg.2 hμ.le) hk0.le]
    nlinarith only [h1, mul_nonneg hσpos.le (sub_nonneg.2 h2), mul_pos hk0 hσpos]
  · have h2 : 0.035 * c * σ ≥ 0.035 * (1190 * t ^ 6) := by linarith only [hσ']
    rw [hk4]
    have h5 : 0 < t ^ 4 := pow_pos ht0 4
    have h6 : t ^ 6 = t ^ 4 * t ^ 2 := by ring
    have h7 : (196 : ℝ) ≤ t ^ 2 := by nlinarith only [ht14]
    nlinarith only [h2, h6, h5, mul_le_mul_of_nonneg_left h7 h5.le]

/-- info: 'FormalResearch.SignUncertainty.hankel_window_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_window_saddle

end FormalResearch.SignUncertainty

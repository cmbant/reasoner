module

public import FormalResearch.ModularBootstrap.StripBand.BandReduction
public import FormalResearch.SignUncertainty.HankelBandChart
public import FormalResearch.SignUncertainty.HankelEdgePhase
public import FormalResearch.SignUncertainty.HankelEdgeAmp

/-!
# Constants of the Hankel band reduction (`teb:mellin`, M5-S5)

`hankelBandParams` is the fixed `BandReductionParams` for the Hankel strip data:
`M = 1/2`, `b = 1/100`, `κ_ζ = 2κ` (`κ = langerKappa = 1/c_s`, so `κ_ζ = 2/c_s`), `A_0 = √(32/κ)`, `C_W = 2`,
`C_a = 4`, `c_1 = 3/16`, `c_2 = 1/2`, `C_ν = 1`, `κ_sub = 1`, `C_τ = 11/κ`.  The constant `b = 1/100` is
smaller than the paper's `0.012880`.  Both values keep `R = b² c^{2/3}` inside the Lean Langer disc
(radius `κ·4.94·10⁻⁴ c^{2/3}`, `κ ≥ 1/2`), but the paper's `b` leaves almost no room in `2ρ_R = 4κ b < 0.035`
(`4κ·0.01288 = 0.0346` for the true `κ = 0.6724`), and Lean only has the crude bound `κ ≤ 7/10`
(`hankelLangerKappa_bounds`); with `b = 1/100` one gets `2ρ_R = 4κ b ≤ 0.028 < 0.035`.  The other constants
(`C_W`, `C_a`, `C_ν`, `κ_sub`, `A_0`, `C_τ`) are not fixed by the paper; they are chosen so that the hypotheses of
`BandReductionInstance` hold for the Hankel data (`A_0² c^{-2/3} = 32/K`, `K = c^{2/3}κ`, `C_τ = 11/κ`,
from `τ₀² ≤ (16/3) m(τ₀)` for `m(τ₀) < 3/16`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

lemma hankelLangerKappa_cube : langerKappa ^ 3 = 3 / Real.pi ^ 2 := by
  unfold langerKappa
  have h := langerMu_cube
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  calc (12 * langerMu ^ 2 / Real.pi ^ 2) ^ 3
      = 1728 * (langerMu ^ 3) ^ 2 / (Real.pi ^ 2) ^ 3 := by ring
    _ = 3 / Real.pi ^ 2 := by rw [h]; field_simp; ring

lemma hankelLangerKappa_bounds : 1 / 2 ≤ langerKappa ∧ langerKappa ≤ 7 / 10 := by
  have hk := langerKappa_pos
  have hc := hankelLangerKappa_cube
  have hp1 : Real.pi < 3.15 := Real.pi_lt_d2
  have hp2 : 3.14 < Real.pi := Real.pi_gt_d2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · by_contra h
    push Not at h
    have : langerKappa ^ 3 < (1 / 2) ^ 3 := pow_lt_pow_left₀ h hk.le (by norm_num)
    rw [hc] at this
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith
  · by_contra h
    push Not at h
    have : (7 / 10 : ℝ) ^ 3 < langerKappa ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hc] at this
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith

/-- The fixed constants of the Hankel band reduction. -/
noncomputable def hankelBandParams : BandReductionParams where
  M := 1 / 2
  b := 1 / 100
  κ_ζ := 2 * langerKappa
  A_0 := Real.sqrt (32 / langerKappa)
  C_W := 2
  C_a := 4
  c_1 := 3 / 16
  c_2 := 1 / 2
  C_ν := 1
  κ_sub := 1
  C_τ := 11 / langerKappa
  hM := by norm_num
  hb := by norm_num
  hκ_ζ := by have := langerKappa_pos; positivity
  hA_0 := Real.sqrt_pos.mpr (by have := langerKappa_pos; positivity)
  hC_W := by norm_num
  hC_a := by norm_num
  hc_1 := by norm_num
  hc_2 := by norm_num
  hC_ν := by norm_num
  hκ_sub := by norm_num
  hC_τ := by have := langerKappa_pos; positivity

/-- `c ≥ 3·10⁶` gives `c^{2/3} ≥ 2·10⁴`. -/
lemma hankel_rpow23_ge {c : ℝ} (hc : 3e6 ≤ c) : 2e4 ≤ c ^ (2 / 3 : ℝ) := by
  have hc0 : 0 < c := by linarith
  have h3 : (c ^ (2 / 3 : ℝ)) ^ 3 = c ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  by_contra h
  push Not at h
  have hp : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
  have : (c ^ (2 / 3 : ℝ)) ^ 3 < (2e4 : ℝ) ^ 3 := pow_lt_pow_left₀ h hp (by norm_num)
  rw [h3] at this
  nlinarith

/-- The Langer disc contains `|u| ≤ 3` and `R = b² c^{2/3}` for `c ≥ 3·10⁶`. -/
lemma hankel_radius_ge {c : ℝ} (hc : 3e6 ≤ c) :
    3 ≤ langerRadius c ∧ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ langerRadius c := by
  have h1 := hankel_rpow23_ge hc
  have hk := hankelLangerKappa_bounds
  have hr : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
  have hp : 0 ≤ c ^ (2 / 3 : ℝ) := by linarith
  rw [hr]
  constructor
  · nlinarith [mul_le_mul h1 hk.1 (by norm_num) hp]
  · nlinarith [mul_le_mul_of_nonneg_left hk.1 hp]

/-- info: 'FormalResearch.SignUncertainty.hankelLangerKappa_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelLangerKappa_bounds

/-- info: 'FormalResearch.SignUncertainty.hankel_radius_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_radius_ge

end FormalResearch.SignUncertainty

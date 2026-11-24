module

public import FormalResearch.SignUncertainty.HankelBandAssembly
public import FormalResearch.SignUncertainty.HankelLangerPsi

/-!
# Saddle geometry for the window lemma (`teb:mellin` (2)--(3); M5-S6b)

At the saddle `ζ₊ = q^{1/2}` of a Langer point `ũ = ũ(q)` one has `√ũ = c^{1/3} μ 𝗆(ζ₊)`, `𝗆(ζ) = ζ + O(10⁻³ ‖ζ‖)`:

* `norm_mMap_sub_le`: `‖𝗆(ζ) - ζ‖ ≤ 9·10⁻⁴ ‖ζ‖` for `‖ζ‖ ≤ 0.035`;
* `hankel_saddle_geom`: `‖ũ‖^{1/2}` and `Re ũ^{1/2}` against `c^{1/3} μ ‖ζ₊‖` and `c^{1/3} μ Re ζ₊` (factors `1 ± 10⁻³`);
* `rhoR_hankel_eq`: the band-reduction annulus scale is `ρ_R = √R / (c^{1/3} μ)` (`2κμ = 1`).
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand

lemma mMap_zero (η : ℕ → ℝ) : mMap η 0 = 0 := by
  unfold mMap powMap; simp

/-- `‖𝗆(ζ) - ζ‖ ≤ 9·10⁻⁴ ‖ζ‖` for `‖ζ‖ ≤ 0.035`. -/
lemma norm_mMap_sub_le (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    ‖mMap η ζ - ζ‖ ≤ 9e-4 * ‖ζ‖ := by
  have hd : ∀ z ∈ closedBall (0 : ℂ) 0.035,
      HasDerivAt (fun z => mMap η z - z) (powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) z - 1) z := by
    intro z hz
    exact (hasDerivAt_mMap h (by simpa using mem_closedBall_zero_iff.1 hz)).sub (hasDerivAt_id z)
  have hbd : ∀ z ∈ closedBall (0 : ℂ) 0.035,
      ‖powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) z - 1‖ ≤ 9e-4 := fun z hz =>
    norm_mMapD_sub_one_le h (by simpa using mem_closedBall_zero_iff.1 hz)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun z => mMap η z - z)
    (s := closedBall (0 : ℂ) 0.035) (x := 0) (y := ζ) (fun z hz => (hd z hz).hasDerivWithinAt) hbd
    (convex_closedBall _ _) (mem_closedBall_zero_iff.2 (by norm_num)) (mem_closedBall_zero_iff.2 hζ)
  simpa [mMap_zero] using hmv

lemma langerKappa_mul_mu : 2 * langerKappa * langerMu = 1 := by
  unfold langerKappa
  have h := langerMu_cube
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : 2 * (12 * langerMu ^ 2 / Real.pi ^ 2) * langerMu = 24 * langerMu ^ 3 / Real.pi ^ 2 := by ring
  rw [this, h]; field_simp

/-- The band-reduction annulus scale is `ρ_R = √R / (c^{1/3} μ)`. -/
lemma rhoR_hankel_eq {c R : ℝ} (hc : 0 < c) :
    rhoR hankelBandParams c R = Real.sqrt R / (c ^ (1 / 3 : ℝ) * langerMu) := by
  have hk : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hm := langerMu_pos
  have hneg : c ^ (-(1 / 3 : ℝ)) = (c ^ (1 / 3 : ℝ))⁻¹ := Real.rpow_neg hc.le _
  show 2 * langerKappa * c ^ (-(1 / 3 : ℝ)) * Real.sqrt R = _
  rw [hneg]
  have h2 := langerKappa_mul_mu
  field_simp
  linear_combination (Real.sqrt R) * h2

/-- Saddle geometry (`kμ = c^{1/3} μ`): `0.9991 kμ ‖ζ₊‖ ≤ ‖ũ‖^{1/2} ≤ 1.0009 kμ ‖ζ₊‖` and
`0.9991 kμ Re ζ₊ ≤ Re ũ^{1/2} ≤ 1.0009 kμ Re ζ₊` for `ζ₊ = q^{1/2}`, `ũ = ũ(q)`. -/
theorem hankel_saddle_geom {c : ℝ} (hc : 0 < c) {q u : ℂ} (hq : q ∈ slitPlane) (hqn : ‖q‖ ≤ 0.035 ^ 2)
    (hqu : langerUtilde etaC c q = u) :
    (0.9991 * (c ^ (1 / 3 : ℝ) * langerMu)) * ‖saddleRoot q‖ ≤ ‖u‖ ^ (1 / 2 : ℝ) ∧
    ‖u‖ ^ (1 / 2 : ℝ) ≤ (1.0009 * (c ^ (1 / 3 : ℝ) * langerMu)) * ‖saddleRoot q‖ ∧
    (0.9991 * (c ^ (1 / 3 : ℝ) * langerMu)) * (saddleRoot q).re ≤ (u ^ (1 / 2 : ℂ)).re ∧
    (u ^ (1 / 2 : ℂ)).re ≤ (1.0009 * (c ^ (1 / 3 : ℝ) * langerMu)) * (saddleRoot q).re := by
  set ζ := saddleRoot q with hζ
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hqn
  have hre : 0 < ζ.re := re_saddleRoot_pos hq
  have hζeq : (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I = ζ := by apply Complex.ext <;> simp
  have hm := re_mMap_bounds langerEta_etaC (σ := ζ.re) (τ := ζ.im) hre.le (by rw [hζeq]; exact hζn)
  rw [hζeq] at hm
  have hmn := norm_mMap_sub_le langerEta_etaC hζn
  have hmn' : 0.9991 * ‖ζ‖ ≤ ‖mMap etaC ζ‖ ∧ ‖mMap etaC ζ‖ ≤ 1.0009 * ‖ζ‖ := by
    have h1 := norm_sub_norm_le (mMap etaC ζ) ζ
    have h2 := norm_sub_norm_le ζ (mMap etaC ζ)
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  have hk : 0 < c ^ (1 / 3 : ℝ) * langerMu := mul_pos (Real.rpow_pos_of_pos hc _) langerMu_pos
  have hsq : u ^ (1 / 2 : ℂ) = ((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ) * mMap etaC ζ := by
    rw [← hqu]; exact langerUtilde_sqrt langerEta_etaC hc hq hqn
  have hnu : ‖u‖ ^ (1 / 2 : ℝ) = (c ^ (1 / 3 : ℝ) * langerMu) * ‖mMap etaC ζ‖ := by
    rw [← norm_saddleRoot]
    show ‖u ^ (1 / 2 : ℂ)‖ = _
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  have hru : (u ^ (1 / 2 : ℂ)).re = (c ^ (1 / 3 : ℝ) * langerMu) * (mMap etaC ζ).re := by
    rw [hsq, Complex.re_ofReal_mul]
  rw [hnu, hru]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hmn'.1, hmn'.2, hm.1, hm.2, hre, norm_nonneg ζ]

/-- The prefactor of `Ψ̃`: `k / (2πκ) ≤ 0.27 k`. -/
lemma hankel_pref_le {k : ℝ} (hk : 0 ≤ k) : k / (2 * π * langerKappa) ≤ k * 0.27 := by
  have hmu := langerMu_sq_ge
  have : 1 / (2 * π * langerKappa) ≤ 0.27 := by
    unfold langerKappa
    have hpi := Real.pi_pos
    have e : 1 / (2 * π * (12 * langerMu ^ 2 / π ^ 2)) = π / (24 * langerMu ^ 2) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2]
  calc k / (2 * π * langerKappa) = k * (1 / (2 * π * langerKappa)) := by ring
    _ ≤ _ := by gcongr

/-- info: 'FormalResearch.SignUncertainty.norm_mMap_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mMap_sub_le

/-- info: 'FormalResearch.SignUncertainty.rhoR_hankel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoR_hankel_eq

/-- info: 'FormalResearch.SignUncertainty.hankel_saddle_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_saddle_geom

/-- info: 'FormalResearch.SignUncertainty.langerKappa_mul_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerKappa_mul_mu

/-- info: 'FormalResearch.SignUncertainty.hankel_pref_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_pref_le

end FormalResearch.SignUncertainty

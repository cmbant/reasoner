module

public import FormalResearch.ModularBootstrap.Upper.Design.PhaseComb
public import FormalResearch.ModularBootstrap.Upper.Design.CombTransformP
public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound

/-!
# Lemma `Φ` for an abstract comb with a phase decomposition (`ut:Phi`, `ut:T2`)

The proof of `designProfile_sdvHypotheses_of_decomp` and `lemma_Phi_transform_of_decomp`
(`Design.CombTransform`) uses a finite modification `B_D` only through the following facts about the
pair `(B, Φ₁)`: `|B| ≤ 1` on `|Im b| ≤ 1/2`, `B = exp (c' Φ₀ + Φ₁)` on `𝒩`, `Φ₁` holomorphic on a
neighbourhood of `𝒩` with first two derivatives bounded by `M_φ` on `𝒩`, `B(-b̄) = conj B(b)` on `E₊`.
This module states the two results for such a pair.  The design combs, and the combs `T_{χ(p)} B_D` of
`ut:T2`, are instances.

* `sdvHypotheses_of_phase`: `SDVHypotheses Φ₀ x c' (1/8) (𝒜₀ + M_φ) (𝒜₀' + M_φ) sech² Φ₁ H₀¹ ε_H` for
  `x ≥ ξ_*`, `c' ≥ 6/(π ξ_*)`.
* `edgeHankel_eq_sdvIntegral_of_eq`: the Hankel transform of `sech² B` is the integral `SD_V` of `Φ₁`.
* `lemma_Phi_transform_of_phase`: `|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`; the case
  `p = 0` of `lemma_Phi_transform_of_phase_P` (`CombTransformP`, every order `p`, via `FW-SD`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle

/-- **The hypotheses of Lemma `SD_V` for `h₀ = sech² B`, from a phase decomposition** (the abstract form
of `designProfile_sdvHypotheses_of_decomp`). -/
theorem sdvHypotheses_of_phase {c' Mφ : ℝ} {B Φ₁ : ℂ → ℂ} (hc : 6 / (π * xiStar) ≤ c')
    (hP : PhaseComb c' Mφ B Φ₁) {x : ℝ} (hx : xiStar ≤ x) :
    SDVHypotheses edgePhi0Blaschke x c' (1 / 8) (ampM0 + Mφ) (ampM0' + Mφ)
      sechSqProfile Φ₁ hankel0 hankelEps := by
  have hc'pos : 0 < c' := lt_of_lt_of_le (by have := xiStar_pos; positivity) hc
  have hk8 : 8 ≤ sdvWave c' x := by
    unfold sdvWave
    have hxi := xiStar_pos
    have h1 : 6 / (π * xiStar) * (π * xiStar) = 6 := by field_simp
    nlinarith [mul_le_mul hc hx hxi.le hc'pos.le, Real.pi_pos]
  have hkpos : 0 < sdvWave c' x := by linarith
  have hstrip : edgeStrip (1 / 8) ⊆ combN := fun b hb => by
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    exact le_trans hb' (by norm_num)
  obtain ⟨hAn, hNz, hL1, hL2⟩ := sdvAmplitude_fields (x := x) (n := c') hk8 hP.diff
    (fun b hb => (hP.deriv_bound b (hstrip hb)).1) (fun b hb => (hP.deriv_bound b (hstrip hb)).2)
  refine ⟨hAn, hNz, ?_, hL1, hL2, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    have him : 0 < ((sdvWave c' x : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul]
      exact mul_pos hkpos (by linarith [(abs_le.mp hb').1])
    rw [hankel0_eq_leading_mul him]
    rfl
  · exact phase_h_decay hP
  · refine ⟨1, fun b hb => ?_⟩
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    have him : 0 < ((sdvWave c' x : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul]
      exact mul_pos hkpos (by linarith [(abs_le.mp hb').1])
    exact norm_one_add_hankelEps_le him
  · intro v
    dsimp only
    have hb_im : (((v : ℂ) + Complex.I / 2)).im = 1 / 2 := by simp
    have hbm_im : (((-v : ℂ) + Complex.I / 2)).im = 1 / 2 := by simp
    have hbc : (v : ℂ) + Complex.I / 2 ∈ combN := by
      change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
      rw [hb_im]; norm_num
    have hbmc : (-v : ℂ) + Complex.I / 2 ∈ combN := by
      change |((-v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
      rw [hbm_im]; norm_num
    have hneg : (-v : ℂ) + Complex.I / 2 = -(starRingEnd ℂ ((v : ℂ) + Complex.I / 2)) := by
      rw [map_add, Complex.conj_ofReal, map_div₀, Complex.conj_I, map_ofNat]; ring
    have hk : ((sdvWave c' x : ℂ) * ((-v : ℂ) + Complex.I / 2)) =
        -(starRingEnd ℂ ((sdvWave c' x : ℂ) * ((v : ℂ) + Complex.I / 2))) := by
      rw [hneg, map_mul, Complex.conj_ofReal]; ring
    have hh : ∀ z : ℂ, z ∈ combN → sechSqProfile z *
        Complex.exp ((c' : ℂ) * edgePhi0Blaschke z + Φ₁ z) = sechSqProfile z * B z :=
      fun z hz => by rw [hP.eq z hz]
    rw [hh _ hbmc, hh _ hbc, hk, hankel0_reflection]
    have hsym : sechSqProfile (-(starRingEnd ℂ ((v : ℂ) + Complex.I / 2))) *
        B (-(starRingEnd ℂ ((v : ℂ) + Complex.I / 2))) =
        starRingEnd ℂ (sechSqProfile ((v : ℂ) + Complex.I / 2) * B ((v : ℂ) + Complex.I / 2)) := by
      rw [sechSqProfile_neg_conj, hP.symm_edge _ hb_im, map_mul]
    rw [← hneg] at hsym
    rw [hsym, hneg]
    simp only [map_mul]
    ring

/-- `(SD.1)`: the Hankel transform of `h₀ = sech² B` is the edge integral of `SD_V`, for `B = exp (c' Φ₀ + Φ₁)`
on `𝒩` (the abstract form of `edgeHankel_designProfile_eq_sdvIntegral`). -/
lemma edgeHankel_eq_sdvIntegral_of_eq {c' : ℝ} {B Φ₁ : ℂ → ℂ}
    (heq : ∀ b ∈ combN, Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) = B b)
    (hh : EdgeHankelHyp (fun b => sechSqProfile b * B b) π 8) {x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' (fun b => sechSqProfile b * B b) (c' * x ^ 2 / 3) =
      ((sdvIntegral edgePhi0Blaschke c' x sechSqProfile Φ₁ hankel0 : ℂ)) := by
  rw [edge_hankel_representation Real.pi_pos hh hc hx]
  unfold sdvIntegral sdvWave
  have hpref : (2 * (π : ℂ) * (c' : ℂ) / 3) = ((2 * π * c' / 3 : ℝ) : ℂ) := by push_cast; ring
  rw [hpref]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hbc : (v : ℂ) + Complex.I / 2 ∈ combN := by
    change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ 1 / 4
    simp
  have := heq _ hbc
  simp only
  rw [this]

/-- **Lemma `Φ`, "Consequently", for an abstract phase decomposition** (the abstract form of
`lemma_Phi_transform_of_decomp`): for `M_φ ≥ 0` and `0 < θ < 2/3` there is `C ≥ 0` such that for `c'`
large, every comb `B` with a `PhaseComb c' M_φ B Φ₁` and `EdgeHankelHyp (sech² B) π 8`, and every
`x ≥ ξ_* + c'^{-θ}`, `|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})`. -/
theorem lemma_Phi_transform_of_phase {Mφ : ℝ} (hM : 0 ≤ Mφ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ (B Φ₁ : ℂ → ℂ), PhaseComb c' Mφ B Φ₁ →
      EdgeHankelHyp (fun b => sechSqProfile b * B b) π 8 →
      ∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
        ‖edgeHankel c' (fun b => sechSqProfile b * B b) (c' * x ^ 2 / 3)‖ ≤
          combAmplitude c' x * (1 + C * c' ^ (-1 + 3 * θ / 2)) := by
  obtain ⟨C, hC, h⟩ := lemma_Phi_transform_of_phase_P 0 hM hθ0 hθ1
  refine ⟨C, hC, h.mono fun c' hc' B Φ₁ hP hh x hx => ?_⟩
  have := hc' B Φ₁ hP hh x hx
  simpa [edgeHankelP_zero, fwsdRatio] using this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.sdvHypotheses_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sdvHypotheses_of_phase

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_transform_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_transform_of_phase

end FormalResearch.ModularBootstrap.Upper.Design

module

public import FormalResearch.ModularBootstrap.Upper.Design.AmplitudeLogDeriv
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
* `lemma_Phi_transform_of_phase`: `|ĥ₀(c'x²/3)| ≤ 𝒜_x (1 + C c'^{-1+3θ/2})` for `x ≥ ξ_* + c'^{-θ}`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle

/-- The comb-independent amplitude `𝒜_x = 2 e^{-2πnx/3} |ℰ(b_x)| |1 + ε_H(k b_x)|
(|b_x|/(x F'(v_x)))^{1/2}` of `(SD.4)` for `ℰ = sech²(π b/2)` (the factor `e^{Re Φ₁(b_x)}` is `1`
for the combs of Lemma `Φ`, see `designPhi1_re_edge`). -/
noncomputable def combAmplitude (n x : ℝ) : ℝ :=
  sdvPrefactor n x sechSqProfile (fun _ => 0) hankelEps

lemma sechSqProfile_neg_conj (b : ℂ) :
    sechSqProfile (-(starRingEnd ℂ b)) = starRingEnd ℂ (sechSqProfile b) := by
  unfold sechSqProfile
  have h1 : (π : ℂ) * -(starRingEnd ℂ b) / 2 = -(starRingEnd ℂ ((π : ℂ) * b / 2)) := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]; ring
  rw [h1, Complex.cosh_neg, Complex.cosh_conj]
  simp

/-- The data of a comb with a phase decomposition: the facts about `(B, Φ₁)` used for Lemmas `SD_V`,
`SD_G` and `Φ`.  `|B| ≤ 1` on `|Im b| ≤ 1/2`, `B = exp (c' Φ₀ + Φ₁)` on `𝒩`, `Φ₁` differentiable on
`combNMid` with `‖Φ₁'‖, ‖Φ₁''‖ ≤ M_φ` on `𝒩`, `Re Φ₁ = 0` and `B(-b̄) = conj B(b)` on `E₊`. -/
structure PhaseComb (c' Mφ : ℝ) (B Φ₁ : ℂ → ℂ) : Prop where
  bound : ∀ b : ℂ, |b.im| ≤ 1 / 2 → ‖B b‖ ≤ 1
  eq : ∀ b ∈ combN, Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) = B b
  diff : DifferentiableOn ℂ Φ₁ combNMid
  deriv_bound : ∀ b ∈ combN, ‖deriv Φ₁ b‖ ≤ Mφ ∧ ‖deriv (deriv Φ₁) b‖ ≤ Mφ
  re_edge : ∀ b : ℂ, b.im = 1 / 2 → (Φ₁ b).re = 0
  symm_edge : ∀ b : ℂ, b.im = 1 / 2 → B (-(starRingEnd ℂ b)) = starRingEnd ℂ (B b)

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
  · refine ⟨8, π, by norm_num, Real.pi_pos, fun v t ht0 ht1 => ?_⟩
    have hbim : (((v : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    have hbre : (((v : ℂ) + (t : ℂ) * Complex.I)).re = v := by simp
    have hbc : (v : ℂ) + (t : ℂ) * Complex.I ∈ combN := by
      change |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ 1 / 4
      rw [hbim, abs_le]; constructor <;> linarith
    rw [norm_mul, hP.eq _ hbc]
    have h2 := edgeHankelHyp_sech.decay ((v : ℂ) + (t : ℂ) * Complex.I) (by rw [hbim]; linarith)
      (by rw [hbim]; exact ht1)
    rw [hbre] at h2
    have h3 : ‖B ((v : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 :=
      hP.bound _ (by rw [hbim, abs_of_nonneg (by linarith)]; exact ht1)
    calc _ ≤ (8 * Real.exp (-π * |v|)) * 1 := mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
      _ = 8 * Real.exp (-π * |v|) := mul_one _
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
  have hc1' := cosC_pos
  have hM₁ : 0 ≤ ampM0 + Mφ := by unfold ampM0; positivity
  have hM₂ : 0 ≤ ampM0' + Mφ := by unfold ampM0'; positivity
  obtain ⟨C₃, C₄, hΦ⟩ := edgePhaseData_blaschke
  have hEP := hΦ (1 / 8) (by norm_num) (by norm_num)
  have hC₃ : 0 ≤ C₃ := (norm_nonneg _).trans (hEP.deriv3_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  have hC₄ : 0 ≤ C₄ := (norm_nonneg _).trans (hEP.deriv4_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  obtain ⟨N₀, CSD, hN₀, hCSD, hSD⟩ := lemma_SD_V (δ := 1 / 8) (C₃ := C₃) (C₄ := C₄) (M := ampM0 + Mφ)
    (M' := ampM0' + Mφ) (by norm_num) (by norm_num) hC₃ hC₄ hM₁ hM₂
  obtain ⟨cm, hcm, hmx⟩ := sdv_uniform_mX_cubed
  have hexp : 0 < 1 - 3 * θ / 2 := by linarith
  refine ⟨CSD / cm, by positivity, ?_⟩
  filter_upwards [(tendsto_rpow_atTop hexp).eventually_ge_atTop (N₀ / cm), eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (6 / (π * xiStar))]
    with c' hbig hc1 hc6 B Φ₁ hP hh x hx
  have hc'pos : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hxpos : 0 < c' ^ (-θ) := Real.rpow_pos_of_pos hc'pos _
  have hxξ : xiStar < x := by linarith
  have hxpos' : 0 < x := lt_trans xiStar_pos hxξ
  have hEq := edgeHankel_eq_sdvIntegral_of_eq hP.eq hh hc'pos hxpos'
  set P : ℝ := c' ^ (1 - 3 * θ / 2) with hP'
  have hPpos : 0 < P := Real.rpow_pos_of_pos hc'pos _
  have hq : c' ^ (-(3 * θ / 2)) ≤ (x - xiStar) ^ (3 / 2 : ℝ) := by
    have h1 : (c' ^ (-θ)) ^ (3 / 2 : ℝ) ≤ (x - xiStar) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hxpos.le (by linarith) (by norm_num)
    have h2 : (c' ^ (-θ)) ^ (3 / 2 : ℝ) = c' ^ (-(3 * θ / 2)) := by
      rw [← Real.rpow_mul hc'pos.le]; congr 1; ring
    rwa [h2] at h1
  have hq1 : c' ^ (-(3 * θ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc1 (by linarith)
  have hmX : cm * c' ^ (-(3 * θ / 2)) ≤ mX x ^ 3 :=
    (mul_le_mul_of_nonneg_left (le_min hq1 hq) hcm.le).trans (hmx x hxξ)
  have hPeq : P = c' * c' ^ (-(3 * θ / 2)) := by
    rw [hP', ← Real.rpow_one_add' hc'pos.le (by linarith)]; congr 1
  have hcm_mX : cm * P ≤ c' * mX x ^ 3 := by
    rw [hPeq]
    calc cm * (c' * c' ^ (-(3 * θ / 2))) = c' * (cm * c' ^ (-(3 * θ / 2))) := by ring
      _ ≤ c' * mX x ^ 3 := mul_le_mul_of_nonneg_left hmX hc'pos.le
  have hN : N₀ ≤ c' * mX x ^ 3 := by
    have := (div_le_iff₀ hcm).1 hbig
    linarith
  obtain ⟨err, herr, hint⟩ := hSD hxξ hc'pos hN hEP (sdvHypotheses_of_phase hc6 hP (by linarith))
  have hre : (Φ₁ (bX x)).re = 0 := hP.re_edge _ (by simp [bX])
  have hpref : sdvPrefactor c' x sechSqProfile Φ₁ hankelEps = combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor
    simp [hre]
  have hA0 : 0 ≤ combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor
    positivity
  have herr' : |err| ≤ CSD / cm * c' ^ (-1 + 3 * θ / 2) := by
    have h1 : c' ^ (-1 + 3 * θ / 2) = P⁻¹ := by
      rw [hP', ← Real.rpow_neg hc'pos.le]; congr 1; ring
    rw [h1]
    refine herr.trans ?_
    have hpos : 0 < c' * mX x ^ 3 := lt_of_lt_of_le (mul_pos hcm hPpos) hcm_mX
    calc CSD / (c' * mX x ^ 3) ≤ CSD / (cm * P) :=
          div_le_div_of_nonneg_left hCSD (mul_pos hcm hPpos) hcm_mX
      _ = CSD / cm * P⁻¹ := by field_simp
  rw [hEq, hint, Complex.norm_real, Real.norm_eq_abs, hpref, abs_mul, abs_of_nonneg hA0]
  refine mul_le_mul_of_nonneg_left ?_ hA0
  calc |Real.cos (sdvPhase edgePhi0Blaschke c' x sechSqProfile Φ₁ hankelEps) + err|
      ≤ |Real.cos _| + |err| := abs_add_le _ _
    _ ≤ 1 + |err| := by gcongr; exact Real.abs_cos_le_one _
    _ ≤ _ := by linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.sdvHypotheses_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sdvHypotheses_of_phase

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_transform_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_transform_of_phase

end FormalResearch.ModularBootstrap.Upper.Design

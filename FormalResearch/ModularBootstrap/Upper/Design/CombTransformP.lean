module

public import FormalResearch.ModularBootstrap.Upper.Design.PhaseComb
public import FormalResearch.ModularBootstrap.Upper.Saddle.FWSD
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderPFields
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderPSymm
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBoundP

/-!
# Lemma `Φ` at every order `p`: `FW-SD` for a comb with a phase decomposition (`fw:SDp`, `ut:Phi`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `FW-SD` (`fw:SDp`, `fw:e1.3`, `fw:e1.4`) and its
proof, step (2): the comb hypotheses of `FW-SD` follow from a phase decomposition `PhaseComb` (`Φ₁` bounded in
`C²` on `𝒩`), exactly as those of `SD_V` do at order `0` (`CombTransformAbs`).

* `phase_h_decay`: strip decay of `h₀ = sech² e^{c'Φ₀ + Φ₁}` on `1/2 - 1/8 ≤ Im b ≤ 1/2` (shared with the
  `SD_V` instance).
* `fwsdHypotheses_of_phase`: `FWSDHypotheses p Φ₀ x c' (1/8) (𝒜₀ + M_φ) (𝒜₀' + M_φ) C_ε sech² Φ₁ H_p¹ ε_p` for
  every `x > ξ_*` with `k = 4π c' x/3 ≥ K₀(p)` (the amplitude fields `circAmplitude_fields`, the Hankel fields
  `exists_hankelEpsOrd_fwsd_fields`, the edge reflection `hankelOrd_reflection`).
* `edgeHankelP_eq_fwsdIntegral_of_eq`: the order-`p` transform of `sech² B` is the integral of `FW-SD`
  (`fw:e1.2a`).
* `lemma_Phi_transform_of_phase_P`: for `x ≥ ξ_* + c'^{-θ}`, `0 < θ < 2/3`,
  `‖(𝓗_{p+1} h₀)(c' x²/3)‖ ≤ 𝒜_x R_p(x) (1 + C c'^{-1+3θ/2})`, `R_p(x) = (|b_x|/x)^p` (`fw:e1.4`, `fw:e1.5`).
  At `p = 0` this is `lemma_Phi_transform_of_phase` (`CombTransformAbs`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle

/-- Strip decay of `h₀ = sech²(πb/2) e^{c'Φ₀ + Φ₁}` on `1/2 - 1/8 ≤ Im b ≤ 1/2` for a comb with a phase
decomposition (`|B| ≤ 1` there). -/
lemma phase_h_decay {c' Mφ : ℝ} {B Φ₁ : ℂ → ℂ} (hP : PhaseComb c' Mφ B Φ₁) :
    ∃ C_h a_h : ℝ, 0 ≤ C_h ∧ 0 < a_h ∧ ∀ v t : ℝ, 1 / 2 - 1 / 8 ≤ t → t ≤ 1 / 2 →
      ‖sechSqProfile ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((c' : ℂ) * edgePhi0Blaschke ((v : ℂ) + (t : ℂ) * Complex.I) +
          Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C_h * Real.exp (-a_h * |v|) := by
  refine ⟨8, π, by norm_num, Real.pi_pos, fun v t ht0 ht1 => ?_⟩
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

/-- **The hypotheses of Lemma `FW-SD` (order `p`) for `h₀ = sech² B`, from a phase decomposition.**
For every `p` there are `C_ε ≥ 0` and `K₀ > 0`, depending on `p` only, such that for every comb `B` with
`PhaseComb c' M_φ B Φ₁`, every `x > ξ_*` and `k = 4π c' x/3 ≥ K₀`:
`FWSDHypotheses p Φ₀ x c' (1/8) (𝒜₀ + M_φ) (𝒜₀' + M_φ) C_ε sech² Φ₁ H_p¹ ε_p`
(`Φ₀ = edgePhi0Blaschke`, `δ = 1/8`). -/
theorem fwsdHypotheses_of_phase (p : ℕ) :
    ∃ Cε K₀ : ℝ, 0 ≤ Cε ∧ 0 < K₀ ∧ ∀ {c' Mφ : ℝ} {B Φ₁ : ℂ → ℂ} {x : ℝ},
      PhaseComb c' Mφ B Φ₁ → xiStar < x → K₀ ≤ sdvWave c' x →
      FWSDHypotheses p edgePhi0Blaschke x c' (1 / 8) (ampM0 + Mφ) (ampM0' + Mφ) Cε
        sechSqProfile Φ₁ (hankelOrd p) (hankelEpsOrd p) := by
  obtain ⟨Ce, K0, hCe, hK0, hf⟩ := exists_hankelEpsOrd_fwsd_fields p
  have hξ := xiStar_pos
  have hpi := Real.pi_pos
  refine ⟨3 * Ce / (4 * π * xiStar), K0, by positivity, hK0, ?_⟩
  intro c' Mφ B Φ₁ x hP hx hk
  have hx0 : 0 < x := lt_trans hξ hx
  have hk0 : 0 < sdvWave c' x := lt_of_lt_of_le hK0 hk
  have hc' : 0 < c' := by
    unfold sdvWave at hk0
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_nonneg (mul_nonneg hpi.le (neg_nonneg.mpr h)) hx0.le]
  have hstrip : edgeStrip (1 / 8) ⊆ combN := fun b hb => by
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    exact le_trans hb' (by norm_num)
  have him : ∀ b ∈ edgeStrip (1 / 8), 3 / 8 ≤ b.im := fun b hb => by
    have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
    linarith [(abs_le.mp hb').1]
  obtain ⟨hAn, hNz, hL1, hL2⟩ := circAmplitude_fields hP.diff
    (fun b hb => (hP.deriv_bound b (hstrip hb)).1) (fun b hb => (hP.deriv_bound b (hstrip hb)).2)
  refine ⟨hAn, hNz, hL1, hL2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, phase_h_decay hP, ?_⟩
  · intro b hb
    have hz : 0 < ((sdvWave c' x : ℂ) * b).im := by
      rw [Complex.im_ofReal_mul]; exact mul_pos hk0 (by linarith [him b hb])
    exact hankelOrd_expansion p hz
  · exact (analyticOnNhd_one_add_hankelEpsOrd p hk0).mono (fun b hb => by
      have := him b hb
      show 0 < b.im
      linarith)
  · intro b hb; exact (hf _ hk b (by linarith [him b hb])).2.2.1
  · intro b hb; exact (hf _ hk b (by linarith [him b hb])).2.2.2.1
  · intro b hb; exact (hf _ hk b (by linarith [him b hb])).2.2.2.2
  · exact ⟨2, fun b hb => (hf _ hk b (by linarith [him b hb])).2.1⟩
  · have h1 := (hf _ hk (bX x) (by simp [bX]; norm_num)).1
    refine h1.trans ?_
    have hm := mX_pos hx
    have hm3 : 0 < mX x ^ 3 := pow_pos hm 3
    have hm31 : mX x ^ 3 ≤ 1 := pow_le_one₀ hm.le (mX_le_one x)
    have e1 : Ce / sdvWave c' x ≤ (3 * Ce / (4 * π * xiStar)) / c' := by
      have hk' : sdvWave c' x = 4 * π * c' * x / 3 := rfl
      have e2 : Ce / (4 * π * c' * x / 3) = (3 * Ce / (4 * π * c')) / x := by field_simp
      have e3 : (3 * Ce / (4 * π * xiStar)) / c' = (3 * Ce / (4 * π * c')) / xiStar := by
        field_simp
      rw [hk', e2, e3]
      exact div_le_div_of_nonneg_left (by positivity) hξ hx.le
    refine e1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [hc'])
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
    have hk' : ((sdvWave c' x : ℂ) * ((-v : ℂ) + Complex.I / 2)) =
        -(starRingEnd ℂ ((sdvWave c' x : ℂ) * ((v : ℂ) + Complex.I / 2))) := by
      rw [hneg, map_mul, Complex.conj_ofReal]; ring
    have hh : ∀ z : ℂ, z ∈ combN → sechSqProfile z *
        Complex.exp ((c' : ℂ) * edgePhi0Blaschke z + Φ₁ z) = sechSqProfile z * B z :=
      fun z hz => by rw [hP.eq z hz]
    rw [hh _ hbmc, hh _ hbc, hk', hankelOrd_reflection]
    have hsym : sechSqProfile (-(starRingEnd ℂ ((v : ℂ) + Complex.I / 2))) *
        B (-(starRingEnd ℂ ((v : ℂ) + Complex.I / 2))) =
        starRingEnd ℂ (sechSqProfile ((v : ℂ) + Complex.I / 2) * B ((v : ℂ) + Complex.I / 2)) := by
      rw [sechSqProfile_neg_conj, hP.symm_edge _ hb_im, map_mul]
    rw [← hneg] at hsym
    rw [hsym, hneg]
    have hs : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by rw [← mul_pow]; simp
    simp only [map_mul, map_pow, map_div₀, Complex.conj_ofReal]
    rw [neg_div, neg_pow, pow_succ]
    generalize (starRingEnd ℂ) (sechSqProfile ((v : ℂ) + Complex.I / 2)) = S
    generalize (starRingEnd ℂ) (B ((v : ℂ) + Complex.I / 2)) = Bc
    generalize (starRingEnd ℂ) ((v : ℂ) + Complex.I / 2) = bc
    generalize (starRingEnd ℂ) (hankelOrd p ((sdvWave c' x : ℂ) * ((v : ℂ) + Complex.I / 2))) = H
    generalize (-1 : ℂ) ^ p = s at hs ⊢
    linear_combination (S * Bc * (bc / (x : ℂ)) ^ p * H * bc) * hs

/-- `(SD.1)` at order `p`: the order-`p` transform of `h₀ = sech² B` is the edge integral of `FW-SD`, for
`B = exp (c' Φ₀ + Φ₁)` on `𝒩` (`fw:e1.2a`). -/
lemma edgeHankelP_eq_fwsdIntegral_of_eq (p : ℕ) {c' : ℝ} {B Φ₁ : ℂ → ℂ}
    (heq : ∀ b ∈ combN, Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) = B b)
    (hh : EdgeHankelHyp (fun b => sechSqProfile b * B b) π 8) {x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankelP p c' (fun b => sechSqProfile b * B b) (c' * x ^ 2 / 3) =
      fwsdIntegral p edgePhi0Blaschke c' x sechSqProfile Φ₁ (hankelOrd p) := by
  rw [edge_hankel_representation_P Real.pi_pos hh p hc hx]
  unfold edgeIntegralP edgeIntegrandP fwsdIntegral sdvWave
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

/-- The order-zero prefactor `𝒜_x^∘` of `FW-SD` (without the factor `|1 + ε_H(k b_x)|`) is at most
`(1 + 1/k) 𝒜_x`, `k = 4π c' x/3 ≥ 1`, when `Re Φ₁(b_x) = 0` (`|ε_H(k b_x)| ≤ 1/(2k)`). -/
lemma fwsdPrefactor0_le_combAmplitude {c' x : ℝ} {Φ₁ : ℂ → ℂ} (hk1' : 1 ≤ sdvWave c' x)
    (hre : (Φ₁ (bX x)).re = 0) :
    fwsdPrefactor0 c' x sechSqProfile Φ₁ ≤ combAmplitude c' x * (1 + 1 / sdvWave c' x) := by
  have hkpos : 0 < sdvWave c' x := by linarith
  have hpref0 : 0 ≤ fwsdPrefactor0 c' x sechSqProfile Φ₁ := by
    unfold fwsdPrefactor0; positivity
  have hrel : combAmplitude c' x =
      fwsdPrefactor0 c' x sechSqProfile Φ₁ * ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ := by
    unfold combAmplitude sdvPrefactor fwsdPrefactor0
    simp [hre]
    ring
  have hlow : 1 - 1 / (2 * sdvWave c' x) ≤ ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ := by
    have hzim : 0 < ((sdvWave c' x : ℂ) * bX x).im := by
      unfold bX
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.div_ofNat_im, Complex.I_im, Complex.add_re, Complex.div_ofNat_re, Complex.I_re,
        zero_mul, zero_add, add_zero]
      positivity
    have hε := norm_hankelEps_le hzim
    have hbn : (1 / 2 : ℝ) ≤ ‖bX x‖ := by
      have := Complex.abs_im_le_norm (bX x)
      have him : (bX x).im = 1 / 2 := by unfold bX; simp
      rw [him] at this
      simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this
    have hzn : sdvWave c' x / 2 ≤ ‖(sdvWave c' x : ℂ) * bX x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hkpos.le]
      nlinarith
    have hzpos : 0 < ‖(sdvWave c' x : ℂ) * bX x‖ := by linarith
    have h1 : ‖hankelEps ((sdvWave c' x : ℂ) * bX x)‖ ≤ 1 / (2 * sdvWave c' x) := by
      refine hε.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    have := norm_sub_norm_le (1 : ℂ) (-hankelEps ((sdvWave c' x : ℂ) * bX x))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  set k := sdvWave c' x with hkdef
  set a := ‖1 + hankelEps ((k : ℂ) * bX x)‖ with hadef
  have hk' : 1 / k ≤ 1 := by rw [div_le_one hkpos]; exact hk1'
  have h2 : 1 ≤ (1 + 1 / k) * (1 - 1 / (2 * k)) := by
    have e : (1 + 1 / k) * (1 - 1 / (2 * k)) = 1 + (1 / (2 * k)) * (1 - 1 / k) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ 1 / (2 * k) * (1 - 1 / k) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have h3 : a ≥ 1 - 1 / (2 * k) := hlow
  calc fwsdPrefactor0 c' x sechSqProfile Φ₁
      ≤ fwsdPrefactor0 c' x sechSqProfile Φ₁ * ((1 + 1 / k) * (1 - 1 / (2 * k))) :=
        le_mul_of_one_le_right hpref0 h2
    _ ≤ fwsdPrefactor0 c' x sechSqProfile Φ₁ * ((1 + 1 / k) * a) := by
        gcongr
    _ = combAmplitude c' x * (1 + 1 / k) := by rw [hrel]; ring

/-- **Lemma `Φ`, "Consequently", at order `p`** (`fw:SDp` (2), `fw:e1.4`, for a phase decomposition): for
`M_φ ≥ 0` and `0 < θ < 2/3` there is `C ≥ 0` such that for `c'` large, every comb `B` with
`PhaseComb c' M_φ B Φ₁` and `EdgeHankelHyp (sech² B) π 8`, and every `x ≥ ξ_* + c'^{-θ}`,
`‖(𝓗_{p+1} h₀)(c' x²/3)‖ ≤ 𝒜_x R_p(x) (1 + C c'^{-1+3θ/2})`, where `R_p(x) = (|b_x|/x)^p`
(`fwsdRatio`) and `𝒜_x = combAmplitude c' x` is the order-zero amplitude of `(SD.4)`.  The constant `C`
depends on `p`, `M_φ`, `θ` only. -/
theorem lemma_Phi_transform_of_phase_P (p : ℕ) {Mφ : ℝ} (hM : 0 ≤ Mφ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ (B Φ₁ : ℂ → ℂ), PhaseComb c' Mφ B Φ₁ →
      EdgeHankelHyp (fun b => sechSqProfile b * B b) π 8 →
      ∀ x : ℝ, xiStar + c' ^ (-θ) ≤ x →
        ‖edgeHankelP p c' (fun b => sechSqProfile b * B b) (c' * x ^ 2 / 3)‖ ≤
          combAmplitude c' x * fwsdRatio p x * (1 + C * c' ^ (-1 + 3 * θ / 2)) := by
  have hc1' := cosC_pos
  have hξ := xiStar_pos
  have hpi := Real.pi_pos
  have hM₁ : 0 ≤ ampM0 + Mφ := by unfold ampM0; positivity
  have hM₂ : 0 ≤ ampM0' + Mφ := by unfold ampM0'; positivity
  obtain ⟨Cε, K₀, hCε, hK₀, hfw⟩ := fwsdHypotheses_of_phase p
  obtain ⟨C₃, C₄, hΦ⟩ := edgePhaseData_blaschke
  have hEP := hΦ (1 / 8) (by norm_num) (by norm_num)
  have hC₃ : 0 ≤ C₃ := (norm_nonneg _).trans (hEP.deriv3_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  have hC₄ : 0 ≤ C₄ := (norm_nonneg _).trans (hEP.deriv4_bound (Complex.I / 2) (by
    change |(Complex.I / 2 : ℂ).im - 1 / 2| ≤ 1 / 8
    simp))
  obtain ⟨N₀, Cp, hN₀, hCp, hSD⟩ := lemma_FW_SD_part2 p (δ := 1 / 8) (by norm_num) (by norm_num)
    hC₃ hC₄ hM₁ hM₂ hCε
  obtain ⟨cm, hcm, hmx⟩ := sdv_uniform_mX_cubed
  have hexp : 0 < 1 - 3 * θ / 2 := by linarith
  refine ⟨3 / (4 * π * xiStar) + 2 * (Cp / cm), by positivity, ?_⟩
  filter_upwards [(tendsto_rpow_atTop hexp).eventually_ge_atTop (N₀ / cm),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (3 * (K₀ + 1) / (4 * π * xiStar))]
    with c' hbig hc1 hcK B Φ₁ hP hh x hx
  have hc'pos : 0 < c' := lt_of_lt_of_le one_pos hc1
  have hxpos : 0 < c' ^ (-θ) := Real.rpow_pos_of_pos hc'pos _
  have hxξ : xiStar < x := by linarith
  have hxpos' : 0 < x := lt_trans hξ hxξ
  have hEq := edgeHankelP_eq_fwsdIntegral_of_eq p hP.eq hh hc'pos hxpos'
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
  have hmpos : 0 < c' * mX x ^ 3 := lt_of_lt_of_le (mul_pos hcm hPpos) hcm_mX
  -- the wave number
  have hk_ge : 3 * (K₀ + 1) / (4 * π * xiStar) * (4 * π * xiStar / 3) ≤ c' * (4 * π * xiStar / 3) :=
    mul_le_mul_of_nonneg_right hcK (by positivity)
  have hk1 : K₀ + 1 ≤ sdvWave c' x := by
    unfold sdvWave
    have e : 3 * (K₀ + 1) / (4 * π * xiStar) * (4 * π * xiStar / 3) = K₀ + 1 := by field_simp
    rw [e] at hk_ge
    nlinarith [mul_le_mul_of_nonneg_left hxξ.le (mul_pos hpi hc'pos).le]
  have hkx : K₀ ≤ sdvWave c' x := by linarith
  have hk1' : 1 ≤ sdvWave c' x := by linarith
  have hkpos : 0 < sdvWave c' x := by linarith
  obtain ⟨err, herr, hint⟩ := hSD hxξ hc'pos hN hEP (hfw hP hxξ hkx)
  have hre : (Φ₁ (bX x)).re = 0 := hP.re_edge _ (by simp [bX])
  have hpref0 : 0 ≤ fwsdPrefactor0 c' x sechSqProfile Φ₁ := by
    unfold fwsdPrefactor0; positivity
  have hA0 : 0 ≤ combAmplitude c' x := by
    unfold combAmplitude sdvPrefactor; positivity
  have hpref_le := fwsdPrefactor0_le_combAmplitude (c' := c') (x := x) hk1' hre
  -- the ratio bound
  have hr0 : 0 ≤ fwsdRatio p x := by unfold fwsdRatio; positivity
  have hnorm_main : ‖(-Complex.I * (bX x / (x : ℂ))) ^ p *
      Complex.exp (Complex.I * (fwsdPhase0 edgePhi0Blaschke c' x sechSqProfile Φ₁ : ℂ))‖ =
      fwsdRatio p x := by
    rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hxpos'.le, Complex.norm_exp_I_mul_ofReal, mul_one]
    rfl
  have hre_le : |((-Complex.I * (bX x / (x : ℂ))) ^ p *
      Complex.exp (Complex.I * (fwsdPhase0 edgePhi0Blaschke c' x sechSqProfile Φ₁ : ℂ))).re| ≤
      fwsdRatio p x := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq hnorm_main)
  rw [hEq, hint, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpref0]
  have hbr : |(((-Complex.I * (bX x / (x : ℂ))) ^ p *
      Complex.exp (Complex.I * (fwsdPhase0 edgePhi0Blaschke c' x sechSqProfile Φ₁ : ℂ))).re + err)| ≤
      fwsdRatio p x * (1 + Cp / (c' * mX x ^ 3)) := by
    refine (abs_add_le _ _).trans ?_
    have herr' : |err| ≤ Cp * fwsdRatio p x / (c' * mX x ^ 3) := herr
    calc _ ≤ fwsdRatio p x + Cp * fwsdRatio p x / (c' * mX x ^ 3) := add_le_add hre_le herr'
      _ = fwsdRatio p x * (1 + Cp / (c' * mX x ^ 3)) := by ring
  -- the error factor
  have hP1 : c' ^ (-1 + 3 * θ / 2) = P⁻¹ := by
    rw [hP', ← Real.rpow_neg hc'pos.le]; congr 1; ring
  have hPle : P ≤ c' := by
    rw [hP']
    calc c' ^ (1 - 3 * θ / 2) ≤ c' ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = c' := Real.rpow_one c'
  have ha : 1 / sdvWave c' x ≤ 3 / (4 * π * xiStar) * P⁻¹ := by
    have e1 : 1 / sdvWave c' x ≤ 3 / (4 * π * xiStar) * c'⁻¹ := by
      have hk' : sdvWave c' x = 4 * π * c' * x / 3 := rfl
      have e2 : 1 / (4 * π * c' * x / 3) = (3 / (4 * π * c')) / x := by field_simp
      have e3 : 3 / (4 * π * xiStar) * c'⁻¹ = (3 / (4 * π * c')) / xiStar := by field_simp
      rw [hk', e2, e3]
      exact div_le_div_of_nonneg_left (by positivity) hξ hxξ.le
    exact e1.trans (mul_le_mul_of_nonneg_left (inv_anti₀ hPpos hPle) (by positivity))
  have hb : Cp / (c' * mX x ^ 3) ≤ (Cp / cm) * P⁻¹ := by
    refine (div_le_div_of_nonneg_left hCp (mul_pos hcm hPpos) hcm_mX).trans (le_of_eq ?_)
    field_simp
  have hb0 : 0 ≤ Cp / (c' * mX x ^ 3) := div_nonneg hCp hmpos.le
  have ha1 : 1 / sdvWave c' x ≤ 1 := by rw [div_le_one hkpos]; exact hk1'
  have ha0 : 0 ≤ 1 / sdvWave c' x := by positivity
  calc fwsdPrefactor0 c' x sechSqProfile Φ₁ * |(((-Complex.I * (bX x / (x : ℂ))) ^ p *
        Complex.exp (Complex.I * (fwsdPhase0 edgePhi0Blaschke c' x sechSqProfile Φ₁ : ℂ))).re + err)|
      ≤ combAmplitude c' x * (1 + 1 / sdvWave c' x) *
        (fwsdRatio p x * (1 + Cp / (c' * mX x ^ 3))) :=
        mul_le_mul hpref_le hbr (abs_nonneg _) (by positivity)
    _ = combAmplitude c' x * fwsdRatio p x *
        ((1 + 1 / sdvWave c' x) * (1 + Cp / (c' * mX x ^ 3))) := by ring
    _ ≤ combAmplitude c' x * fwsdRatio p x *
        (1 + (3 / (4 * π * xiStar) + 2 * (Cp / cm)) * c' ^ (-1 + 3 * θ / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA0 hr0)
        rw [hP1]
        nlinarith [mul_le_mul_of_nonneg_right ha1 hb0]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.fwsdHypotheses_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwsdHypotheses_of_phase

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_Phi_transform_of_phase_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Phi_transform_of_phase_P

end FormalResearch.ModularBootstrap.Upper.Design

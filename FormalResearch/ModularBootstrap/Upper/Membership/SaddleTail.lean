module

public import FormalResearch.ModularBootstrap.Upper.Membership.CombDecay
public import FormalResearch.ModularBootstrap.Upper.Saddle.SDV
public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelAsym

/-!
# Lemma `K7` tail: from the `SD_V` amplitude hypotheses to `SaddleTailBound`

For `x ≥ x_I = ξ_* + c'^{-3/5}`, Lemma `SD_V` (`lemma_SD_V`) applied to `ℰ = sech²(πb/2)`, the phase
`Φ₀ = edgePhi0Blaschke` (`edgePhaseData_blaschke`) and the data `Φ₁` of hypothesis (ii) gives
`ĥ₀(c' x²/3) = 𝒜_x (cos Θ_x + err)` with `|err| ≤ C/(c' m_x³)` and `m_x³ ≥ c c'^{-9/10}`
(`sdv_uniform_mX_cubed`).  Here `𝒜_x e^{c' L} ≤ C(c) e^{-πx}` is derived from
`‖sech²(π b_x/2)‖ ≤ 8 e^{-π v_x}`, `v_x ≥ x - π⁻¹ log 3` (`F(v) ≤ v + π⁻¹ log 3`), `e^{Re Φ₁(b_x)} = 1`
on `E_+`, `‖1 + ε_H‖ ≤ 2` and `|b_x|/(x F'(v_x)) ≤ C(c)` on `x ≥ x_I` (`F'` increasing).

The remaining named hypothesis is `SDVAmplitudeInput`: the amplitude hypotheses `SDVHypotheses` of
`lemma_SD_V` for the comb data (analyticity and non-vanishing of `A_x`, the Hankel expansion with
`ε_H = hankelEps`, the log-derivative bounds `M, M'` of `A_x`, strip decay, and edge reflection
symmetry), at every `x ≥ x_I`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Hankel
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Saddle-point bookkeeping -/

lemma edgeF_le_add {v : ℝ} (hv : 0 ≤ v) : edgeF v ≤ v + Real.log 3 / π := by
  unfold edgeF
  have hpi := Real.pi_pos
  have hc : Real.cosh (π * v) ≤ Real.exp (π * v) := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.mpr (by nlinarith : -(π * v) ≤ π * v)
    linarith
  have h1 : 1 ≤ Real.exp (π * v) := Real.one_le_exp (by positivity)
  have hcpos := Real.cosh_pos (π * v)
  have hs : √(1 + Real.cosh (π * v) ^ 2) ≤ 1 + Real.cosh (π * v) := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have harg : Real.arsinh (Real.cosh (π * v)) ≤ π * v + Real.log 3 := by
    unfold Real.arsinh
    calc Real.log (Real.cosh (π * v) + √(1 + Real.cosh (π * v) ^ 2))
        ≤ Real.log (3 * Real.exp (π * v)) := by
          apply Real.log_le_log (by positivity); nlinarith
      _ = π * v + Real.log 3 := by
          rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring
  rw [div_le_iff₀ hpi]
  calc Real.arsinh (Real.cosh (π * v)) ≤ π * v + Real.log 3 := harg
    _ = (v + Real.log 3 / π) * π := by field_simp

lemma le_edgeF (v : ℝ) : v ≤ edgeF v := by
  unfold edgeF
  have hpi := Real.pi_pos
  rw [le_div_iff₀ hpi]
  calc v * π = Real.arsinh (Real.sinh (π * v)) := by rw [Real.arsinh_sinh]; ring
    _ ≤ Real.arsinh (Real.cosh (π * v)) :=
        Real.arsinh_le_arsinh.mpr (by
          rw [Real.sinh_eq, Real.cosh_eq]
          have := Real.exp_pos (-(π * v))
          linarith)

lemma edgeV_le {x : ℝ} (hx : xiStar < x) : edgeV x ≤ x := by
  have := le_edgeF (edgeV x)
  rwa [edgeF_edgeV hx] at this

lemma sub_le_edgeV {x : ℝ} (hx : xiStar < x) : x - Real.log 3 / π ≤ edgeV x := by
  have := edgeF_le_add (edgeV_pos hx).le
  rw [edgeF_edgeV hx] at this
  linarith

lemma edgeV_mono {x y : ℝ} (hx : xiStar < x) (hxy : x ≤ y) : edgeV x ≤ edgeV y := by
  by_contra h
  have h := not_le.mp h
  have hy : xiStar < y := lt_of_lt_of_le hx hxy
  have := edgeF_strictMonoOn (Set.mem_Ici.mpr (edgeV_pos hy).le) (Set.mem_Ici.mpr (edgeV_pos hx).le) h
  rw [edgeF_edgeV hy, edgeF_edgeV hx] at this
  linarith


/-- Hypothesis (ii) of Lemma `K7`: on `𝒩 = {|Im b - 1/2| ≤ 1/4}`, `log B = c' Φ₀ + Φ₁` with
`Φ₀ = edgePhi0Blaschke` (Lemma `SD_0`), `Re Φ₁ = 0` on `E_+` and `sup_𝒩 |Φ₁^{(i)}| ≤ M`
(`i = 0, 1, 2`); written multiplicatively as `B = exp (c' Φ₀ + Φ₁)`. -/
structure CombPhaseData (c' M : ℝ) (B Φ₁ : ℂ → ℂ) : Prop where
  holo : AnalyticOnNhd ℂ Φ₁ (edgeStrip (1 / 4))
  eq : ∀ b ∈ edgeStrip (1 / 4), B b = Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b)
  re_edge : ∀ v : ℝ, (Φ₁ ((v : ℂ) + Complex.I / 2)).re = 0
  bound : ∀ i : ℕ, i ≤ 2 → ∀ b ∈ edgeStrip (1 / 4), ‖iteratedDeriv i Φ₁ b‖ ≤ M

/-- **Named hypothesis** (amplitude hypotheses of Lemma `SD_V`): `SDVHypotheses` of `lemma_SD_V` for
`ℰ = sech²`, `Φ₀ = edgePhi0Blaschke`, `Φ₁`, `H₀ = hankel0`, `ε_H = hankelEps`, at every `x ≥ x_I`. -/
def SDVAmplitudeInput (c' : ℝ) (Φ₁ : ℂ → ℂ) (δ M M' : ℝ) : Prop :=
  ∀ x : ℝ, xI c' ≤ x →
    SDVHypotheses edgePhi0Blaschke x c' δ M M' sechSqProfile Φ₁ hankel0 hankelEps

/-! ### The prefactor bound -/

lemma sdvPrefactor_le {Φ₁ : ℂ → ℂ} {c' x x₀ : ℝ} (hc' : 0 < c') (hx₀ : xiStar < x₀) (hxx₀ : x₀ ≤ x)
    (hk : 1 / 2 ≤ 4 * π * c' * x / 3) (hre : ∀ v : ℝ, (Φ₁ ((v : ℂ) + Complex.I / 2)).re = 0) :
    sdvPrefactor c' x sechSqProfile Φ₁ hankelEps ≤
      2 * 8 * 3 * 2 * Real.sqrt ((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) *
        Real.exp (-(c' * (2 * π * x / 3)) - π * x) := by
  have hx : xiStar < x := lt_of_lt_of_le hx₀ hxx₀
  have hpi := Real.pi_pos
  have hx0 : 0 < x₀ := lt_trans xiStar_pos hx₀
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hxx₀
  set v := edgeV x with hv
  have hvpos : 0 < v := edgeV_pos hx
  have hφ : 0 < edgeF' (edgeV x₀) := edgeF'_pos (edgeV_pos hx₀)
  have hφle : edgeF' (edgeV x₀) ≤ edgeF' v := edgeF'_strictMono.monotone (edgeV_mono hx₀ hxx₀)
  -- the pieces
  have e1 : Real.exp (-2 * π * c' * x / 3) = Real.exp (-(c' * (2 * π * x / 3))) := by
    congr 1; ring
  have e2 : ‖sechSqProfile (bX x)‖ ≤ 8 * Real.exp (-π * |v|) := by
    unfold bX sechSqProfile; exact sech_sq_le v
  have e2' : Real.exp (-π * |v|) ≤ 3 * Real.exp (-π * x) := by
    rw [abs_of_pos hvpos]
    have h1 := sub_le_edgeV hx
    have h2 : -π * v ≤ -π * x + Real.log 3 := by
      have : π * (x - Real.log 3 / π) ≤ π * v := mul_le_mul_of_nonneg_left h1 hpi.le
      rw [mul_sub, mul_div_cancel₀ _ hpi.ne'] at this
      nlinarith
    calc Real.exp (-π * v) ≤ Real.exp (-π * x + Real.log 3) := Real.exp_le_exp.mpr h2
      _ = 3 * Real.exp (-π * x) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]; ring
  have e3 : Real.exp (Φ₁ (bX x)).re = 1 := by
    have := hre v
    unfold bX; rw [this, Real.exp_zero]
  have e4 : ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ ≤ 2 := by
    have hkpos : 0 < sdvWave c' x := by unfold sdvWave; positivity
    have hzim : 0 < ((sdvWave c' x : ℂ) * bX x).im := by
      unfold bX
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.div_ofNat_im, Complex.I_im, Complex.add_re, Complex.div_ofNat_re, Complex.I_re,
        zero_mul, zero_add, add_zero]
      positivity
    have hznorm : sdvWave c' x / 2 ≤ ‖(sdvWave c' x : ℂ) * bX x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hkpos.le]
      have : (1 / 2 : ℝ) ≤ ‖bX x‖ := by
        have := Complex.abs_im_le_norm (bX x)
        have him : (bX x).im = 1 / 2 := by unfold bX; simp
        rw [him] at this
        simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this
      nlinarith
    have hε := norm_hankelEps_le hzim
    have hk' : 1 / 2 ≤ sdvWave c' x := by unfold sdvWave; linarith
    have hn : 1 / 4 ≤ ‖(sdvWave c' x : ℂ) * bX x‖ := by linarith
    have hn' : 0 < ‖(sdvWave c' x : ℂ) * bX x‖ := by linarith
    have h1 : ‖hankelEps ((sdvWave c' x : ℂ) * bX x)‖ ≤ 1 := by
      refine hε.trans ?_
      rw [div_le_one (by positivity)]; linarith
    calc ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ ≤ ‖(1 : ℂ)‖ + ‖hankelEps _‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
  have e5 : Real.sqrt (‖bX x‖ / (x * edgeF' v)) ≤
      Real.sqrt ((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) := by
    refine Real.sqrt_le_sqrt ?_
    have hb : ‖bX x‖ ≤ x + 1 / 2 := by
      unfold bX
      calc ‖(v : ℂ) + Complex.I / 2‖ ≤ ‖(v : ℂ)‖ + ‖Complex.I / 2‖ := norm_add_le _ _
        _ ≤ x + 1 / 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hvpos.le]
          have := edgeV_le hx
          have h2 : ‖Complex.I / 2‖ = 1 / 2 := by simp
          linarith
    have hFp : 0 < edgeF' v := lt_of_lt_of_le hφ hφle
    rw [div_le_div_iff₀ (by positivity) hφ]
    have h1 : ‖bX x‖ * edgeF' (edgeV x₀) ≤ (x + 1 / 2) * edgeF' v :=
      mul_le_mul hb hφle hφ.le (by positivity)
    have h2 : (1 + 1 / (2 * x₀)) * (x * edgeF' v) ≥ (x + 1 / 2) * edgeF' v := by
      have : (1 + 1 / (2 * x₀)) * x ≥ x + 1 / 2 := by
        have : 1 / (2 * x₀) * x ≥ 1 / 2 := by
          rw [ge_iff_le, ← sub_nonneg]
          have : 1 / (2 * x₀) * x - 1 / 2 = (x - x₀) / (2 * x₀) := by field_simp
          rw [this]; exact div_nonneg (by linarith) (by positivity)
        linarith
      nlinarith [hFp]
    linarith
  -- assemble
  unfold sdvPrefactor
  rw [e1, e3, mul_one]
  have hA := Real.exp_pos (-(c' * (2 * π * x / 3)))
  have hsq : 0 ≤ Real.sqrt (‖bX x‖ / (x * edgeF' v)) := Real.sqrt_nonneg _
  have hε4 : 0 ≤ ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ := norm_nonneg _
  have hE0 : 0 ≤ ‖sechSqProfile (bX x)‖ := norm_nonneg _
  have hE : ‖sechSqProfile (bX x)‖ ≤ 24 * Real.exp (-π * x) :=
    e2.trans (by nlinarith [e2'])
  have hsplit : Real.exp (-(c' * (2 * π * x / 3)) - π * x) =
      Real.exp (-(c' * (2 * π * x / 3))) * Real.exp (-π * x) := by
    rw [sub_eq_add_neg, Real.exp_add]
    congr 2; ring
  rw [hsplit]
  calc 2 * Real.exp (-(c' * (2 * π * x / 3))) * ‖sechSqProfile (bX x)‖ *
        ‖1 + hankelEps ((sdvWave c' x : ℂ) * bX x)‖ * Real.sqrt (‖bX x‖ / (x * edgeF' v))
      ≤ 2 * Real.exp (-(c' * (2 * π * x / 3))) * (24 * Real.exp (-π * x)) * 2 *
          Real.sqrt ((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) := by
        gcongr
    _ = 2 * 8 * 3 * 2 * Real.sqrt ((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) *
          (Real.exp (-(c' * (2 * π * x / 3))) * Real.exp (-π * x)) := by ring

/-! ### The lower bound `c' m_x³ ≥ N` on `x ≥ x_I` -/

lemma large_mX_cubed {cm N : ℝ} (hcm : 0 < cm) (hN : 0 ≤ N)
    (hmX : ∀ x : ℝ, xiStar < x → cm * min 1 ((x - xiStar) ^ (3 / 2 : ℝ)) ≤ mX x ^ 3)
    {c' : ℝ} (hc1 : 1 ≤ c') (hc : (N / cm) ^ 10 ≤ c') {x : ℝ} (hx : xI c' ≤ x) :
    N ≤ c' * mX x ^ 3 := by
  have hc0 : 0 < c' := by linarith
  have hxx : xiStar < x := by
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    unfold xI at hx; linarith
  have h1 := hmX x hxx
  have h2 : c' ^ (-(9 / 10 : ℝ)) ≤ min 1 ((x - xiStar) ^ (3 / 2 : ℝ)) := by
    refine le_min (Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)) ?_
    have h3 : c' ^ (-(3 / 5 : ℝ)) ≤ x - xiStar := by unfold xI at hx; linarith
    calc c' ^ (-(9 / 10 : ℝ)) = (c' ^ (-(3 / 5 : ℝ))) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_mul hc0.le]; norm_num
      _ ≤ (x - xiStar) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hc0.le _) h3 (by norm_num)
  have hs0 : 0 ≤ N / cm := div_nonneg hN hcm.le
  have h4 : N / cm ≤ c' ^ (1 / 10 : ℝ) := by
    calc N / cm = ((N / cm) ^ 10) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]; norm_num
      _ ≤ c' ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by positivity) hc (by norm_num)
  have h5 : c' * c' ^ (-(9 / 10 : ℝ)) = c' ^ (1 / 10 : ℝ) := by
    have := Real.rpow_add hc0 1 (-(9 / 10 : ℝ))
    rw [Real.rpow_one] at this
    rw [← this]; norm_num
  calc N = cm * (N / cm) := by field_simp
    _ ≤ cm * c' ^ (1 / 10 : ℝ) := by gcongr
    _ = c' * (cm * c' ^ (-(9 / 10 : ℝ))) := by rw [← h5]; ring
    _ ≤ c' * (cm * min 1 ((x - xiStar) ^ (3 / 2 : ℝ))) := by gcongr
    _ ≤ c' * mX x ^ 3 := by gcongr

/-! ### Reduction of `SaddleTailBound` to the amplitude hypotheses -/

/-- **Lemma `K7`, `SD_V` tail** (`cmb:K7`, decay of `ĥ₀` for `x ≥ x_I`).  For `0 ≤ M, M'` there is
`c₀ > 0` such that for every `c' ≥ c₀`, every comb `B` with (i), (iii) (`InnerCombHyp`), the phase
decomposition (ii) (`CombPhaseData`) and the amplitude hypotheses of `SD_V` on `x ≥ x_I`
(`SDVAmplitudeInput`, with `δ = 1/8`), the tail bound `SaddleTailBound c' B` holds.  The threshold
`c₀` depends only on `(M, M')` through the constants of `lemma_SD_V` and `sdv_uniform_mX_cubed`;
the constant `C` of `SaddleTailBound` depends on `c'` through `x_I`. -/
theorem saddleTailBound_of_sdv {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {c' : ℝ} {B Φ₁ : ℂ → ℂ} {Mφ : ℝ}, c₀ ≤ c' → InnerCombHyp c' B →
      CombPhaseData c' Mφ B Φ₁ → SDVAmplitudeInput c' Φ₁ (1 / 8) M M' → SaddleTailBound c' B := by
  obtain ⟨C₃, C₄, hΦall⟩ := edgePhaseData_blaschke
  have hΦ := hΦall (1 / 8) (by norm_num) (by norm_num)
  have hC₃ : 0 ≤ C₃ :=
    (norm_nonneg _).trans (hΦ.deriv3_bound _ (mem_edgeStrip_edge (by norm_num) 0))
  have hC₄ : 0 ≤ C₄ :=
    (norm_nonneg _).trans (hΦ.deriv4_bound _ (mem_edgeStrip_edge (by norm_num) 0))
  obtain ⟨N₀, C, hN₀, hC, hSD⟩ :=
    lemma_SD_V (δ := 1 / 8) (C₃ := C₃) (C₄ := C₄) (M := M) (M' := M') (by norm_num) (by norm_num)
      hC₃ hC₄ hM hM'
  obtain ⟨cm, hcm, hmX⟩ := sdv_uniform_mX_cubed
  have hxi := xiStar_pos
  have hpi := Real.pi_pos
  set N : ℝ := max N₀ C with hNdef
  have hN0 : 0 ≤ N := le_max_of_le_left (by linarith)
  refine ⟨max (max 1 ((N / cm) ^ 10)) (3 / (8 * π * xiStar)),
    lt_max_of_lt_left (lt_max_of_lt_left one_pos), ?_⟩
  intro c' B Φ₁ Mφ hc hB hφ hAmp
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc2 : (N / cm) ^ 10 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc3 : 3 / (8 * π * xiStar) ≤ c' := (le_max_right _ _).trans hc
  have hc0 : 0 < c' := by linarith
  have hxI_gt : xiStar < xI c' := by
    unfold xI
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    linarith
  refine ⟨2 * (2 * 8 * 3 * 2 * Real.sqrt ((1 + 1 / (2 * xI c')) / edgeF' (edgeV (xI c')))),
    fun x hx => ?_⟩
  have hxx : xiStar < x := lt_of_lt_of_le hxI_gt hx
  have hxpos : 0 < x := lt_trans hxi hxx
  have hk : 1 / 2 ≤ 4 * π * c' * x / 3 := by
    have h1 : 3 / (8 * π * xiStar) * (8 * π * xiStar) = 3 := by field_simp
    have h2 : 3 ≤ c' * (8 * π * xiStar) := by
      calc (3 : ℝ) = 3 / (8 * π * xiStar) * (8 * π * xiStar) := h1.symm
        _ ≤ c' * (8 * π * xiStar) := by gcongr
    nlinarith [mul_pos hpi hxi, mul_pos hpi hc0, mul_pos (mul_pos hpi hc0) hxi]
  have hnm : N₀ ≤ c' * mX x ^ 3 :=
    (le_max_left _ _).trans (large_mX_cubed hcm hN0 hmX hc1 hc2 hx)
  have herr1 : C ≤ c' * mX x ^ 3 := (le_max_right _ _).trans (large_mX_cubed hcm hN0 hmX hc1 hc2 hx)
  have hmpos : 0 < c' * mX x ^ 3 := lt_of_lt_of_le (by linarith) hnm
  have hAmp' := hAmp x hx
  obtain ⟨err, herr, hint⟩ := hSD hxx hc0 hnm hΦ hAmp'
  have herr' : |err| ≤ 1 := by
    refine herr.trans ?_
    rw [div_le_one hmpos]; exact herr1
  have hrep := edge_hankel_representation Real.pi_pos hB.edgeHankelHyp hc0 hxpos
  have hsd : edgeHankel c' (combH0 B) (c' * x ^ 2 / 3) =
      sdvIntegral edgePhi0Blaschke c' x sechSqProfile Φ₁ hankel0 := by
    rw [hrep]
    unfold sdvIntegral sdvWave
    have hfun : ∀ v : ℝ, combH0 B ((v : ℂ) + Complex.I / 2) =
        sechSqProfile ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((c' : ℂ) * edgePhi0Blaschke ((v : ℂ) + Complex.I / 2) +
            Φ₁ ((v : ℂ) + Complex.I / 2)) := fun v => by
      unfold combH0
      rw [hφ.eq _ (mem_edgeStrip_edge (by norm_num) v)]
    simp only [hfun]
    push_cast
    rfl
  rw [hsd, hint, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hpref0 : 0 ≤ sdvPrefactor c' x sechSqProfile Φ₁ hankelEps := by
    unfold sdvPrefactor; positivity
  have hpref := sdvPrefactor_le (Φ₁ := Φ₁) hc0 hxI_gt hx hk hφ.re_edge
  have hcos1 := Real.abs_cos_le_one (sdvPhase edgePhi0Blaschke c' x sechSqProfile Φ₁ hankelEps)
  have hcos : |Real.cos (sdvPhase edgePhi0Blaschke c' x sechSqProfile Φ₁ hankelEps) + err| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  rw [abs_of_nonneg hpref0]
  calc sdvPrefactor c' x sechSqProfile Φ₁ hankelEps *
        |Real.cos (sdvPhase edgePhi0Blaschke c' x sechSqProfile Φ₁ hankelEps) + err|
      ≤ (2 * 8 * 3 * 2 * Real.sqrt ((1 + 1 / (2 * xI c')) / edgeF' (edgeV (xI c'))) *
          Real.exp (-(c' * (2 * π * x / 3)) - π * x)) * 2 := by gcongr
    _ = _ := by ring

/-- Non-vacuity of `CombPhaseData`: `B = exp (c' Φ₀)`, `Φ₁ = 0`. -/
theorem combPhaseData_nonvacuous (c' : ℝ) :
    CombPhaseData c' 0 (fun b => Complex.exp ((c' : ℂ) * edgePhi0Blaschke b)) (fun _ => 0) where
  holo := analyticOnNhd_const
  eq := fun b _ => by simp
  re_edge := fun v => by simp
  bound := fun i _ b _ => by simp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.saddleTailBound_of_sdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saddleTailBound_of_sdv

/-- **Lemma `K7`** (`cmb:K7`, weight `w = 1`), with the `SD_V` tail derived from the amplitude
hypotheses: for `c' ≥ c₀(M, M')`, `a = c'/12 ≥ S`, a comb with (i), (iii), the phase decomposition (ii)
and `SDVAmplitudeInput`, the decay, the membership `g = ½ (h₀ - ĥ₀) ∈ Ā` and the vacuum identity hold. -/
theorem k7_membership_vacuum_of_sdv {prob : FixedWeightProblem} (hw : prob.w = 1) {M M' : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {c' : ℝ} {B Φ₁ : ℂ → ℂ} {Mφ : ℝ}, c₀ ≤ c' →
      prob.totalShift ≤ c' / 12 → InnerCombHyp c' B → CombPhaseData c' Mφ B Φ₁ →
      SDVAmplitudeInput c' Φ₁ (1 / 8) M M' →
      ∃ C : ℝ, 0 ≤ C ∧ DecayBound c' C (combProfile c' B) ∧
        DecayBound c' C (hankelTransform 1 (combProfile c' B)) ∧
        TestClass prob (c' / 12)
          (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) ∧
        ((prob.gVac (c' / 12)
            (pairOdd (combProfile c' B) (hankelTransform 1 (combProfile c' B))) : ℝ) : ℂ) =
          (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
              combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s)) -
            (π : ℂ) * ((∫ t in Ioi (0 : ℝ), combProfile c' B t * prob.cardyV (c' / 12) t : ℝ) : ℂ) ∧
        ‖(1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
            combH0 B (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2 ^ prob.m := by
  obtain ⟨c₀, hc₀, h⟩ := saddleTailBound_of_sdv hM hM'
  refine ⟨c₀, hc₀, fun {c' B Φ₁ Mφ} hc hS hB hφ hA => ?_⟩
  exact k7_membership_vacuum hw (lt_of_lt_of_le hc₀ hc) hS hB (h hc hB hφ hA)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.k7_membership_vacuum_of_sdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k7_membership_vacuum_of_sdv

end FormalResearch.ModularBootstrap.Upper.Membership

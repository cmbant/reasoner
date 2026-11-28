module

public import FormalResearch.ModularBootstrap.Mixtures.JetsAmp
public import FormalResearch.ModularBootstrap.FiveTerm.CombEquality
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Jet

/-!
# Outer datum, `GA4` properties, and `ctu:common-functional` for `(w, A)`

`constant_term_universality.tex`, Lemma ctu.2 (`ctu:jets`) and Lemma ctu.2a (`ctu:common-functional`);
`positive_mixtures.tex`, Proposition PM.13 (`pmix:jets`):

* `goutWA_modulus`, `goutWA_coupling`, `goutWA_jet`, and `goutWA_outerDatum`:
  for any integer weight `w ≥ 1` and `JetAmplitude A`, `GoutWA w A` satisfies `OuterDatum (WslitWA w A) (KedgeW w) g₁ (GoutWA w A)`.
* `comb_minimum_WA`, `comb_defect_WA`, `comb_equality_iff_WA`, `comb_regularisation_WA`, `fStar_detuning_WA`:
  the exact minimum, defect identity, equality criterion, `ctu:J-quad` regularisation estimate, and detuning ratio
  for `𝒥_{w, A}` via `CombMinimum`, `CombEquality`, `CombRegularisation`.
* `GA4` properties (`ctu:jets` (a)): boundedness above and below away from `{±i}`, real symmetry, `σ`-invariance,
  local holomorphy and non-vanishing across `z = 0` and `z = 1`, and boundary moduli `A(x(y))/A(ξ_*)`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
  FormalResearch.ModularBootstrap.FiveTerm
  FormalResearch.ModularBootstrap.FiveTerm.StripOuter

/-! ### 1. Slit modulus `|GoutWA w A (iy)| = WslitWA w A y` -/

lemma aWA_eq (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) {τ : ℝ} (hτ : 0 ≤ τ) :
    aWA w A τ = Real.log (WslitWA w A (Real.tanh (π * τ / 4))) +
      (3 / 4) * Real.log (1 + Real.tanh (π * τ / 4) ^ 2) +
      ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) *
        Real.log (√(vOf (Real.tanh (π * τ / 4)) ^ 2 + 1 / 4) / xOf (Real.tanh (π * τ / 4))) := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  set y : ℝ := Real.tanh (π * τ / 4) with hy
  have hxT := xT_pos τ
  have hxi := xiStar_pos
  have hlam := lamT_pos τ
  have hb := bT_pos τ
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hAx : 0 < A (xT τ) := lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT τ))
  have hy1 : 1 - y ^ 2 > 0 := by linarith [tanh_sq_lt_one (π * τ / 4)]
  have hq : 0 < √(1 + 6 * y ^ 2 + y ^ 4) := Real.sqrt_pos.mpr (by positivity)
  have hW : 0 < Wslit y := by
    have hlam_eq : (1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar))) = lamT τ := by
      unfold lamT; rw [hy, xOf_tanh]
    unfold Wslit
    rw [hlam_eq, hy, xOf_tanh]
    positivity
  have hWA_eq : WslitWA w A y =
      Wslit y * (xT τ / xiStar) ^ ((w - 1 : ℕ) : ℝ) * (A (xT τ) / A xiStar) * lamT τ ^ (-2 : ℝ) := by
    have hlam_eq : (1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar))) = lamT τ := by
      unfold lamT; rw [hy, xOf_tanh]
    have hxp : (xT τ / xiStar) ^ ((w : ℝ) - 1 / 2) =
        √(xT τ / xiStar) * (xT τ / xiStar) ^ ((w - 1 : ℕ) : ℝ) := by
      have hw' : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by
        rw [Nat.cast_sub hw, Nat.cast_one]
      rw [hw', Real.sqrt_eq_rpow, ← Real.rpow_add (div_pos hxT hxi)]
      congr 1; ring
    have hlam2 : lamT τ ^ 2 * lamT τ ^ (-2 : ℝ) = 1 := by
      rw [← Real.rpow_natCast (lamT τ) 2, ← Real.rpow_add hlam]
      norm_num
    unfold WslitWA Wslit
    rw [hlam_eq, hy, xOf_tanh, hxp]
    calc (√(xT τ / xiStar) * (xT τ / xiStar) ^ ((w - 1 : ℕ) : ℝ)) * (A (xT τ) / A xiStar) /
          ((1 - Real.tanh (π * τ / 4) ^ 2) * √(1 + 6 * Real.tanh (π * τ / 4) ^ 2 + Real.tanh (π * τ / 4) ^ 4))
        = (√(xT τ / xiStar) * (lamT τ ^ 2 * lamT τ ^ (-2 : ℝ))) /
            ((1 - Real.tanh (π * τ / 4) ^ 2) * √(1 + 6 * Real.tanh (π * τ / 4) ^ 2 + Real.tanh (π * τ / 4) ^ 4)) *
            (xT τ / xiStar) ^ ((w - 1 : ℕ) : ℝ) * (A (xT τ) / A xiStar) := by
          rw [hlam2]; ring
      _ = (√(xT τ / xiStar) * lamT τ ^ 2 /
            ((1 - Real.tanh (π * τ / 4) ^ 2) * √(1 + 6 * Real.tanh (π * τ / 4) ^ 2 + Real.tanh (π * τ / 4) ^ 4))) *
            (xT τ / xiStar) ^ ((w - 1 : ℕ) : ℝ) * (A (xT τ) / A xiStar) * lamT τ ^ (-2 : ℝ) := by
          ring
  have hlogWA : Real.log (WslitWA w A y) =
      Real.log (Wslit y) + ((w - 1 : ℕ) : ℝ) * Real.log (xT τ / xiStar) +
        aRel A τ - 2 * Real.log (lamT τ) := by
    rw [hWA_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul hW.ne' (by positivity),
      Real.log_rpow (div_pos hxT hxi), Real.log_rpow hlam]
    unfold aRel
    ring
  have hAmp := aAmp_eq hτ
  rw [← hy] at hAmp
  have hxv : √(vOf y ^ 2 + 1 / 4) / xOf y = bT τ / xT τ := by
    rw [hy, xOf_tanh, vOf_tanh hτ]; rfl
  have haW_eq : aW τ = 2 * Real.log (xT τ / xiStar) + Real.log (bT τ / xT τ) := by
    unfold aW
    rw [Real.log_div hxT.ne' hxi.ne', Real.log_div hb.ne' hxi.ne',
      Real.log_div hb.ne' hxT.ne']
    ring
  unfold aWA
  rw [hAmp, hlogWA, hxv, haW_eq]
  ring

/-- **`ctu:jets` (modulus)**: `|G_outer^{(w,A)}(iy)| = W_slit^{(w,A)}(y)` for `y ∈ (0, 1)`. -/
theorem goutWA_modulus (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖GoutWA w A (Complex.I * (y : ℂ))‖ = WslitWA w A y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  set τ : ℝ := slitTau y with hτ
  have hτ0 : 0 ≤ τ := slitTau_nonneg hy0.le
  have htanh : Real.tanh (π * τ / 4) = y := tanh_slitTau hy'
  have hre : (hbarA (aWA w A) (Complex.I * (τ : ℂ))).re = aWA w A τ :=
    re_hbarA_left (amp_aWA w hA) τ
  have hsI : sInv (Complex.I * (y : ℂ)) = Complex.I * (τ : ℂ) := by
    rw [sInv_slit hy', mul_comm]
  have hAeq := aWA_eq w hw hA hτ0
  rw [htanh] at hAeq
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hx := xOf_pos hy'
  have hxi := xiStar_pos
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hAx : 0 < A (xOf y) := lt_of_lt_of_le hlo (hAlo _ (by
    rw [← htanh, xOf_tanh]; exact xiStar_le_xT τ))
  have hW : 0 < WslitWA w A y := by
    have h1 : 0 < 1 - y ^ 2 := by nlinarith
    have h2 : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
    unfold WslitWA
    positivity
  have hr : 0 < √(vOf y ^ 2 + 1 / 4) / xOf y := by positivity
  have hn1 : ‖(1 : ℂ) - Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
    have : (1 : ℂ) - Complex.I * (y : ℂ) = (1 : ℝ) + ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_add_mul_I]; simp
  have hn2 : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
    have : (1 : ℂ) + Complex.I * (y : ℂ) = (1 : ℝ) + ((y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_add_mul_I]; simp
  have e1 : ‖(1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ)‖ = (1 + y ^ 2) ^ (1 / 4 : ℝ) := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_real, hn1, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  set p : ℝ := (2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 with hpdef
  have e2 : ‖(qBd (Complex.I * (y : ℂ))) ^ (-((p : ℝ) : ℂ))‖ =
      (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-p) := by
    have hpc : -((p : ℝ) : ℂ) = ((-p : ℝ) : ℂ) := by push_cast; rfl
    rw [hpc, Complex.norm_cpow_real, qBd_slit hy', norm_slitVal hy']
  unfold GoutWA
  rw [hsI, norm_mul, norm_div, norm_mul, Complex.norm_exp, hre, e1, e2, norm_pow, hn2,
    Real.sq_sqrt (by positivity)]
  have hexp : Real.exp (aWA w A τ) =
      WslitWA w A y * (1 + y ^ 2) ^ (3 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ p := by
    rw [hAeq, Real.exp_add, Real.exp_add, Real.exp_log hW,
      mul_comm (3 / 4 : ℝ), mul_comm p,
      ← Real.rpow_def_of_pos (by positivity), ← Real.rpow_def_of_pos hr]
  rw [hexp]
  have hp1 : (1 + y ^ 2) ^ (3 / 4 : ℝ) * (1 + y ^ 2) ^ (1 / 4 : ℝ) = 1 + y ^ 2 := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hp2 : (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ p * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-p) = 1 := by
    rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
  have h1y : (0 : ℝ) < 1 + y ^ 2 := by positivity
  calc WslitWA w A y * (1 + y ^ 2) ^ (3 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ p *
        (1 + y ^ 2) ^ (1 / 4 : ℝ) / (1 + y ^ 2) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-p)
      = WslitWA w A y * ((1 + y ^ 2) ^ (3 / 4 : ℝ) * (1 + y ^ 2) ^ (1 / 4 : ℝ)) / (1 + y ^ 2) *
        ((√(vOf y ^ 2 + 1 / 4) / xOf y) ^ p * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-p)) := by ring
    _ = WslitWA w A y := by rw [hp1, hp2]; field_simp

/-! ### 2. Coupling identity `G(iy) K_edge^{(w)}(y) = G(e^{-iψ}) e^{iψ} 2y²/(1+y²)` -/

private lemma slitVal_re_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < (slitVal y).re := by
  rw [slitVal_eq hy]
  have hx := xOf_pos hy
  have : ((1 / 2 : ℂ) - Complex.I * (vOf y : ℂ)) / (xOf y : ℂ) =
      (((1 / 2) / xOf y : ℝ) : ℂ) + ((-vOf y / xOf y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero]
  positivity

private lemma slitVal_cpow_shift {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    (slitVal y) ^ (-(((2 * (n : ℝ) + 1) / 4 : ℝ) : ℂ)) * (slitVal y) ^ n =
      (slitVal y) ^ (-(1 / 4 : ℂ)) * (slitVal y) ^ (((n : ℝ) / 2 : ℝ) : ℂ) ∧
    (slitVal y)⁻¹ ^ (-(((2 * (n : ℝ) + 1) / 4 : ℝ) : ℂ)) =
      (slitVal y)⁻¹ ^ (-(1 / 4 : ℂ)) * (slitVal y) ^ (((n : ℝ) / 2 : ℝ) : ℂ) := by
  have hre : 0 < (slitVal y).re := slitVal_re_pos hy
  have hne : slitVal y ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have harg : |Complex.arg (slitVal y)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have harg' := abs_lt.mp harg
  have hpi := Real.pi_pos
  set a : ℝ := Real.log ‖slitVal y‖
  set b : ℝ := Complex.arg (slitVal y)
  have hex : slitVal y = ex a b := eq_ex_arg hne
  have hex_inv : (slitVal y)⁻¹ = ex (-a) (-b) := by
    conv_lhs => rw [hex, ex_inv]
  have hp : (-(((2 * (n : ℝ) + 1) / 4 : ℝ) : ℂ)) = (((-((2 * (n : ℝ) + 1) / 4) : ℝ) : ℂ)) := by
    push_cast; rfl
  have hq : (-(1 / 4 : ℂ)) = ((-(1 / 4 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  constructor
  · rw [hex, hp, hq, ex_cpow (by linarith) (by linarith), ex_pow, ex_mul,
      ex_cpow (by linarith) (by linarith), ex_cpow (by linarith) (by linarith), ex_mul]
    exact ex_congr (by ring) (by ring)
  · conv_lhs => rw [hex_inv, hp, ex_cpow (by linarith) (by linarith)]
    conv_rhs => rw [hex_inv, hex, hq, ex_cpow (by linarith) (by linarith),
      ex_cpow (by linarith) (by linarith), ex_mul]
    exact ex_congr (by ring) (by ring)

/-- **`ctu:jets` (c), coupling**: `G(iy) K_edge^{(w)}(y) = G(e^{-iψ}) e^{iψ} 2y²/(1+y²)`. -/
theorem goutWA_coupling (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    GoutWA w A (Complex.I * (y : ℂ)) * KedgeW w y =
      GoutWA w A (starRingEnd ℂ (wPt y)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) := by
  have hA1 : hbarA (aWA w A) (1 - (slitTau y : ℂ) * Complex.I) =
      hbarA (aWA w A) ((slitTau y : ℂ) * Complex.I) :=
    hbarA_oneSub (amp_aWA w hA) (slit_mem_closedStrip _)
  obtain ⟨hs1, hs2⟩ := slitVal_cpow_shift hy (w - 1)
  have key := coupling_alg hy
  rw [conj_wPt]
  unfold GoutWA KedgeW
  rw [sInv_slit hy, sInv_sigma_slit hy, hA1, qBd_slit hy, qBd_sigma_slit hy]
  set E := Complex.exp (hbarA (aWA w A) ((slitTau y : ℂ) * Complex.I))
  set S := (slitVal y) ^ ((((w - 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)
  have hLHS : E * (1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 *
        (slitVal y) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) *
        (Kedge y * (slitVal y) ^ (w - 1)) =
      E * S * ((1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 *
        (slitVal y) ^ (-(1 / 4 : ℂ)) * Kedge y) := by
    calc E * (1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 *
          (slitVal y) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) *
          (Kedge y * (slitVal y) ^ (w - 1))
        = E * ((1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 * Kedge y) *
          ((slitVal y) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) * (slitVal y) ^ (w - 1)) := by ring
      _ = E * ((1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 * Kedge y) *
          ((slitVal y) ^ (-(1 / 4 : ℂ)) * S) := by rw [hs1]
      _ = E * S * ((1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) / (1 + Complex.I * (y : ℂ)) ^ 2 *
          (slitVal y) ^ (-(1 / 4 : ℂ)) * Kedge y) := by ring
  have hRHS : E * (1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) /
        (1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ 2 *
        (slitVal y)⁻¹ ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) * wPt y *
        ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) =
      E * S * ((1 - (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) /
        (1 + (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ))) ^ 2 *
        (slitVal y)⁻¹ ^ (-(1 / 4 : ℂ)) * wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ)) := by
    rw [hs2]; ring
  rw [hLHS, hRHS, key]

/-! ### 3. Local holomorphy near `z = 0`, jet, and `OuterDatum` -/

lemma hbarA_zero_of_amp {a : ℝ → ℝ} (ha : Amp a) : hbarA a 0 = ((a 0 : ℝ) : ℂ) := by
  have h1 := re_hbarA_left ha 0
  simp only [Complex.ofReal_zero, mul_zero] at h1
  have h2 := hbarA_conj ha (ζ := 0) ⟨by simp, by simp⟩
  simp only [map_zero] at h2
  have him : (hbarA a 0).im = 0 := by
    have := congrArg Complex.im h2
    simp at this; linarith
  exact Complex.ext (by simpa using h1) (by simpa using him)

/-- `GoutWA w A` is the restriction of a function holomorphic on a disc about the tip `z = 0`. -/
theorem goutWA_local (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ (Gl : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ ρ ≤ 1 / 4 ∧ DifferentiableOn ℂ Gl (ball (0 : ℂ) ρ) ∧
      ∀ z ∈ closure halfDisc, ‖z‖ < ρ → GoutWA w A z = Gl z := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA (amp_aWA w hA) 0
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hH : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  obtain ⟨ρ, hρ, hρ4, hsIball, hTre⟩ := exists_local_radius hδ
  set p : ℂ := -(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ) with hp
  refine ⟨fun z => Complex.exp (H (sInv z)) * (1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2 * (tipExt z) ^ p,
    ρ, hρ, hρ4, ?_, ?_⟩
  · intro z hz
    have hzn : ‖z‖ < ρ := by simpa using hz
    have hz1 : ‖z‖ < 1 := by linarith
    have hHd : DifferentiableAt ℂ H (sInv z) :=
      hH.differentiableAt (isOpen_ball.mem_nhds (hsIball z hzn))
    have hA' : DifferentiableAt ℂ (fun u => H (sInv u)) z :=
      DifferentiableAt.comp (g := H) (f := sInv) z hHd (differentiableAt_sInv_ball hz1)
    have hslit : 1 - z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have := Complex.re_le_norm z
      simp; linarith
    have hP : DifferentiableAt ℂ (fun u : ℂ => (1 - u) ^ (1 / 2 : ℂ)) z :=
      DifferentiableAt.cpow_const (by fun_prop) hslit
    have hD : (1 + z) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro h
      have : z = -1 := eq_neg_of_add_eq_zero_right h
      rw [this] at hz1; simp at hz1
    have hTd : DifferentiableAt ℂ tipExt z :=
      differentiableOn_tipExt.differentiableAt (isOpen_ball.mem_nhds (by simp; linarith))
    have hTs : tipExt z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; exact hTre z hzn
    have hQ : DifferentiableAt ℂ (fun u => (tipExt u) ^ p) z :=
      DifferentiableAt.cpow_const hTd hTs
    exact ((((hA'.cexp).mul hP).div (by fun_prop) hD).mul hQ).differentiableWithinAt
  · intro z hz hzn
    have hz4 : ‖z‖ < 1 / 4 := by linarith
    have hI : z ≠ Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
    have hI' : z ≠ -Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
    have hs : sInv z ∈ closedStrip := sInv_mem_closedStrip hz hI hI'
    have hb : hbarA (aWA w A) (sInv z) = H (sInv z) := by
      refine hbarA_eq_local hH0 heq0 ?_ hs
      rw [hc]; exact hsIball z hzn
    unfold GoutWA
    rw [hb, qBd_eq_tipExt hz hz4]

lemma goutWA_real_pos (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (GoutWA w A (x : ℂ)).im = 0 := by
  have hx : (x : ℂ) ∈ halfDisc := ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
  have h := goutWA_conj w hA hx
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The jet at the tip (`OuterDatum.jet`) for `GoutWA w A`, with real derivative `g₁`. -/
theorem goutWA_jet (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ g1 : ℝ, ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r →
      ‖GoutWA w A z - 1 - g1 * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨Gl, ρ, hρ, hρ4, hdiff, hGl⟩ := goutWA_local w hA
  obtain ⟨C, r0, hr0, hjet⟩ := jet_ball hρ hdiff
  have h0 : Gl 0 = 1 := by
    rw [← hGl 0 zero_mem_closure_halfDisc (by simpa using hρ)]; exact goutWA_zero w hA
  set d : ℂ := deriv Gl 0 with hd
  set r1 : ℝ := min r0 ρ with hr1
  have hr1pos : 0 < r1 := lt_min hr0 hρ
  have hGlx : ∀ x : ℝ, 0 < x → x < r1 → (Gl (x : ℂ)).im = 0 := by
    intro x hx0 hx
    have hxρ : ‖(x : ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact lt_of_lt_of_le hx (min_le_right _ _)
    have hx1 : x < 1 := by
      have := lt_of_lt_of_le hx (min_le_right _ _); linarith
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
    rw [← hGl _ hxc hxρ]
    exact goutWA_real_pos w hA hx0 hx1
  have hdim : d.im = 0 := by
    by_contra hne
    have ha : 0 < |d.im| := abs_pos.mpr hne
    set x : ℝ := min (r1 / 2) (|d.im| / (2 * (|C| + 1))) with hx
    have hx0 : 0 < x := lt_min (by positivity) (by positivity)
    have hxr : x < r1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hb := hjet (x : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact lt_of_lt_of_le hxr (min_le_left _ _))
    rw [h0] at hb
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hb
    have him : |(Gl (x : ℂ) - 1 - d * (x : ℂ)).im| ≤ ‖Gl (x : ℂ) - 1 - d * (x : ℂ)‖ :=
      Complex.abs_im_le_norm _
    have hcalc : (Gl (x : ℂ) - 1 - d * (x : ℂ)).im = -(d.im * x) := by
      simp [hGlx x hx0 hxr]
    rw [hcalc, abs_neg, abs_mul, abs_of_pos hx0] at him
    have h1 : |d.im| * x ≤ C * x ^ 2 := him.trans hb
    have h2 : |d.im| ≤ C * x := by nlinarith [hx0]
    have h3 : x ≤ |d.im| / (2 * (|C| + 1)) := min_le_right _ _
    have h4 : C * x ≤ |C| * x := mul_le_mul_of_nonneg_right (le_abs_self C) hx0.le
    have h5 : |C| * x < |d.im| := by
      have hC1 : 0 < |C| + 1 := by positivity
      calc |C| * x ≤ (|C| + 1) * x := by nlinarith [abs_nonneg C]
        _ ≤ (|C| + 1) * (|d.im| / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h3 hC1.le
        _ = |d.im| / 2 := by field_simp
        _ < |d.im| := by linarith
    linarith
  refine ⟨d.re, C, r1, hr1pos, fun z hz hzr => ?_⟩
  have hdd : d = (d.re : ℂ) := Complex.ext (by simp) (by simpa using hdim)
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzr (min_le_right _ _)
  have hzr0 : ‖z‖ < r0 := lt_of_lt_of_le hzr (min_le_left _ _)
  have := hjet z hzr0
  rw [h0, hdd] at this
  rw [hGl z hz hzρ]
  exact this

/-- **`OuterDatum` for general `(w, A)`** (`ctu:jets`, `ctu:common-functional`, `pmix:jets`):
for any integer weight `w ≥ 1` and `JetAmplitude A`, `GoutWA w A` satisfies every field of
`OuterDatum (WslitWA w A) (KedgeW w) g₁ (GoutWA w A)` for `g₁ = (GoutWA w A)'(0)`. -/
theorem goutWA_outerDatum (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ g1 : ℝ, OuterDatum (WslitWA w A) (KedgeW w) g1 (GoutWA w A) := by
  obtain ⟨g1, C, r, hr, hj⟩ := goutWA_jet w hA
  exact ⟨g1, {
    diff := goutWA_diff w hA
    cont := goutWA_cont w hA
    conj := fun z hz => goutWA_conj w hA hz
    ne_zero := fun z hz => goutWA_ne_zero w hz
    jet := ⟨C, r, hr, hj⟩
    near_one := goutWA_near_one w hA
    near_I := goutWA_near_I w hA
    modulus := fun y hy => goutWA_modulus w hw hA hy
    coupling := fun y hy => goutWA_coupling w hA hy }⟩

/-- The first odd jet `g₁(w, A) = (G_outer^{(w, A)})'(0)`. -/
noncomputable def g1OutWA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) : ℝ :=
  Classical.choose (goutWA_outerDatum w hw hA)

theorem goutWA_outerDatum_g1OutWA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    OuterDatum (WslitWA w A) (KedgeW w) (g1OutWA w hw hA) (GoutWA w A) :=
  Classical.choose_spec (goutWA_outerDatum w hw hA)

/-! ### 4. `ctu:common-functional`: defect identity, minimum, equality criterion, regularisation -/

/-- **`ctu:common-functional` (1), defect identity**: for any `F ∈ HAdm(Ω)`,
`𝒥_{w,A}[F] - α_tip g₁(w,A) = α_C ∫₀¹ [max(|H(iy)|, |B_H(y)|) - Re B_H(y)] dy/y² ≥ 0`
where `H = F · G_outer^{(w,A)}` and the RHS depends only on `H`. -/
theorem comb_defect_WA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {F : ℂ → ℂ} {c1 : ℝ} (hF : HAdm F c1) :
    0 ≤ combJ (WslitWA w A) (KedgeW w) F - alphaTip * g1OutWA w hw hA ∧
      combJ (WslitWA w A) (KedgeW w) F = alphaTip * g1OutWA w hw hA +
        alphaC * ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * GoutWA w A z) y :=
  let hG := goutWA_outerDatum_g1OutWA w hw hA
  ⟨sub_nonneg.mpr (comb_lower_bound hF hG), (comb_defect_identity hF hG).2⟩

/-- **`ctu:common-functional` (2), exact minimum**: `min_{F ∈ H_adm(Ω)} 𝒥_{w,A}[F] = α_tip g₁(w, A)`,
attained at `F_* = (1 + z²)/G_outer^{(w,A)}`. -/
theorem comb_minimum_WA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    IsLeast {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ), HAdm F c1 ∧ combJ (WslitWA w A) (KedgeW w) F = x}
      (alphaTip * g1OutWA w hw hA) :=
  comb_minimum (goutWA_outerDatum_g1OutWA w hw hA)

/-- **`ctu:common-functional` (2), equality criterion**: `𝒥_{w,A}[F] = α_tip g₁(w,A)` iff for all
`y ∈ (0, 1)`, `B_H(y) ∈ [0, ∞)` and `|H(iy)| ≤ B_H(y)` (`H = F · G_outer^{(w,A)}`). -/
theorem comb_equality_iff_WA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {F : ℂ → ℂ} {c1 : ℝ} (hF : HAdm F c1) :
    combJ (WslitWA w A) (KedgeW w) F = alphaTip * g1OutWA w hw hA ↔
      ∀ y ∈ Ioo (0 : ℝ) 1,
        (edgeSum (fun z => F z * GoutWA w A z) y).im = 0 ∧
          0 ≤ (edgeSum (fun z => F z * GoutWA w A z) y).re ∧
          ‖F (Complex.I * (y : ℂ)) * GoutWA w A (Complex.I * (y : ℂ))‖ ≤
            (edgeSum (fun z => F z * GoutWA w A z) y).re :=
  comb_equality_iff hF (goutWA_outerDatum_g1OutWA w hw hA)

/-- **`ctu:common-functional` (3), regularisation (`ctu:J-quad`)**: for `ε ∈ (0, 1)`,
`F_ε = m_ε F_*` is in `H_adm` with `F_ε'(0) = -g₁ - ε/2` and
`α_tip g₁ ≤ 𝒥_{w,A}[F_ε] ≤ α_tip g₁ + 25 α_C ε²` (absolute constant independent of `(w, A)`). -/
theorem comb_regularisation_WA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    HAdm (fun z => mEps ε z * fStar (GoutWA w A) z) (-g1OutWA w hw hA - ε / 2) ∧
      alphaTip * g1OutWA w hw hA ≤ combJ (WslitWA w A) (KedgeW w) (fun z => mEps ε z * fStar (GoutWA w A) z) ∧
      combJ (WslitWA w A) (KedgeW w) (fun z => mEps ε z * fStar (GoutWA w A) z) ≤
        alphaTip * g1OutWA w hw hA + 25 * alphaC * ε ^ 2 :=
  comb_regularisation (goutWA_outerDatum_g1OutWA w hw hA) hε0 hε1

/-- **`ctu:jets` (c), phase-locked detuning ratio**:
`|F_*(iy) + K_edge^{(w)}(y) F_*(e^{-iψ})| / |F_*(iy)| = 1 + 4y²/(1+y²)²` is independent of `(w, A)`. -/
theorem fStar_detuning_WA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖fStar (GoutWA w A) (Complex.I * (y : ℂ)) +
        KedgeW w y * fStar (GoutWA w A) (starRingEnd ℂ (wPt y))‖ =
      (1 + 4 * y ^ 2 / (1 + y ^ 2) ^ 2) * ‖fStar (GoutWA w A) (Complex.I * (y : ℂ))‖ :=
  fStar_detuning (goutWA_outerDatum_g1OutWA w hw hA) hy

/-! ### 5. Properties of `GA4` (`ctu:jets` (a)) -/

lemma aRel_bounds {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ m M : ℝ, ∀ τ : ℝ, m ≤ aRel A τ ∧ aRel A τ ≤ M := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨hi, hAhi⟩ := hA.upper
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  refine ⟨Real.log (lo / A xiStar), Real.log (hi / A xiStar), fun τ => ?_⟩
  have hx := xiStar_le_xT τ
  have hpos : 0 < A (xT τ) := lt_of_lt_of_le hlo (hAlo _ hx)
  exact ⟨Real.log_le_log (div_pos hlo hAξ) (div_le_div_of_nonneg_right (hAlo _ hx) hAξ.le),
    Real.log_le_log (div_pos hpos hAξ) (div_le_div_of_nonneg_right (hAhi _ hx) hAξ.le)⟩

/-- `GA4` is bounded and bounded away from zero on `closure Ω ∖ {±i}` (in particular on `Ω`). -/
theorem GA4_bounded {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ c C : ℝ, 0 < c ∧ ∀ z ∈ closure halfDisc \ {Complex.I, -Complex.I},
      c ≤ ‖GA4 A z‖ ∧ ‖GA4 A z‖ ≤ C := by
  obtain ⟨m, M, hmM⟩ := aRel_bounds hA
  have hamp := amp_aRel hA
  have hle := re_hbarA_le hamp (α := 0) (β := M) le_rfl (fun τ => by
    have := (hmM τ).2; simpa using this)
  obtain ⟨κ, hκ⟩ := hle
  refine ⟨Real.exp m, Real.exp (0 * 0 + M + 0 * κ), Real.exp_pos m, fun z hz => ?_⟩
  have hstrip : sInv z ∈ closedStrip :=
    sInv_mem_closedStrip hz.1 (ne_of_mem_diff hz).1 (ne_of_mem_diff hz).2
  unfold GA4
  rw [Complex.norm_exp]
  refine ⟨Real.exp_le_exp.mpr (re_hbarA_ge hamp (fun τ => (hmM τ).1) hstrip), ?_⟩
  refine Real.exp_le_exp.mpr ?_
  have := hκ (sInv z) hstrip
  simpa using this

/-- `GA4` is real-symmetric: `GA4 A z̄ = conj (GA4 A z)` on `Ω`. -/
theorem GA4_conj {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ} (hz : z ∈ halfDisc) :
    GA4 A (starRingEnd ℂ z) = starRingEnd ℂ (GA4 A z) := by
  unfold GA4
  rw [sInv_conj hz, hbarA_conj (amp_aRel hA) (strip_subset_closedStrip (sInv_mem_strip hz)),
    Complex.exp_conj]

/-- `GA4` is `σ`-invariant: `GA4 A (σ z) = GA4 A z` on `Ω`. -/
theorem GA4_sigma {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ} (hz : z ∈ halfDisc) :
    GA4 A (sigmaHD z) = GA4 A z := by
  unfold GA4
  rw [sInv_sigma hz, hbarA_oneSub (amp_aRel hA) (strip_subset_closedStrip (sInv_mem_strip hz))]

/-- `GA4 A 0 = 1`. -/
theorem GA4_zero {A : ℝ → ℝ} (hA : JetAmplitude A) : GA4 A 0 = 1 := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  unfold GA4
  rw [sInv_zero, hbarA_zero_of_amp (amp_aRel hA), aRel_zero A hlo hAlo, Complex.ofReal_zero,
    Complex.exp_zero]

/-- `GA4` extends holomorphically and without zeros across `z = 0`. -/
theorem GA4_local_zero {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ (G0 : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ DifferentiableOn ℂ G0 (ball (0 : ℂ) ρ) ∧
      (∀ z ∈ ball (0 : ℂ) ρ, G0 z ≠ 0) ∧
      ∀ z ∈ closure halfDisc \ {Complex.I, -Complex.I}, ‖z‖ < ρ → GA4 A z = G0 z := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA (amp_aRel hA) 0
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hH : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  have hsI0 : ContinuousAt sInv 0 := (differentiableAt_sInv_ball (by simp)).continuousAt
  obtain ⟨ρ1, hρ1, hS⟩ := Metric.continuousAt_iff.mp hsI0 δ hδ
  set ρ := min ρ1 (1 / 2) with hρ
  have hρpos : 0 < ρ := lt_min hρ1 (by norm_num)
  refine ⟨fun z => Complex.exp (H (sInv z)), ρ, hρpos, ?_, fun z _ => Complex.exp_ne_zero _, ?_⟩
  · intro z hz
    have hzn : ‖z‖ < ρ := by simpa using hz
    have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzn (min_le_right _ _) |>.trans (by norm_num)
    have hball : sInv z ∈ ball (0 : ℂ) δ := by
      have := hS (x := z) (by rw [dist_zero_right]; exact lt_of_lt_of_le hzn (min_le_left _ _))
      rw [sInv_zero, dist_zero_right] at this
      simpa [mem_ball_zero_iff] using this
    exact ((hH.differentiableAt (isOpen_ball.mem_nhds hball)).comp z
      (differentiableAt_sInv_ball hz1)).cexp.differentiableWithinAt
  · intro z hz hzn
    have hball : sInv z ∈ ball (0 : ℂ) δ := by
      have := hS (x := z) (by rw [dist_zero_right]; exact lt_of_lt_of_le hzn (min_le_left _ _))
      rw [sInv_zero, dist_zero_right] at this
      simpa [mem_ball_zero_iff] using this
    have hs : sInv z ∈ closedStrip :=
      sInv_mem_closedStrip hz.1 (ne_of_mem_diff hz).1 (ne_of_mem_diff hz).2
    unfold GA4
    rw [hbarA_eq_local hH0 heq0 (by rw [hc]; exact hball) hs]

private lemma differentiableAt_sInv_one : DifferentiableAt ℂ sInv 1 := by
  have hq : qArc (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right
    have hI : ((1 : ℂ) + 1 * Complex.I) / ((1 : ℂ) - 1 * Complex.I) = Complex.I := by
      have hne : (1 : ℂ) - Complex.I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
      rw [one_mul, div_eq_iff hne]
      ring_nf; rw [Complex.I_sq]; ring
    unfold qArc
    rw [hI]; simp
  have hd : (1 : ℂ) - (1 : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  unfold sInv Complex.arctan
  have hqd : DifferentiableAt ℂ (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) 1 :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) hd
  exact (hqd.clog hq).const_mul (-Complex.I / 2) |>.const_mul (4 / (π : ℂ))

/-- `GA4` extends holomorphically and without zeros across `z = 1`. -/
theorem GA4_local_one {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ (G1 : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ DifferentiableOn ℂ G1 (ball (1 : ℂ) ρ) ∧
      (∀ z ∈ ball (1 : ℂ) ρ, G1 z ≠ 0) ∧
      ∀ z ∈ closure halfDisc \ {Complex.I, -Complex.I}, ‖z - 1‖ < ρ → GA4 A z = G1 z := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA (amp_aRel hA) 0
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hH : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  have hd_cont : ContinuousAt sInv 1 := differentiableAt_sInv_one.continuousAt
  obtain ⟨ρ1, hρ1, hS⟩ := Metric.continuousAt_iff.mp hd_cont δ hδ
  have hd_nhds : ∀ᶠ z in 𝓝 (1 : ℂ), DifferentiableAt ℂ sInv z := by
    have hq : qArc (1 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      have hI : ((1 : ℂ) + 1 * Complex.I) / ((1 : ℂ) - 1 * Complex.I) = Complex.I := by
        have hne : (1 : ℂ) - Complex.I ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
        rw [one_mul, div_eq_iff hne]
        ring_nf; rw [Complex.I_sq]; ring
      unfold qArc; rw [hI]; simp
    have hq_cont : ContinuousAt qArc 1 := by
      unfold qArc
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      intro h; have := congrArg Complex.re h; simp at this
    have hne : ∀ᶠ z in 𝓝 (1 : ℂ), (1 : ℂ) - z * Complex.I ≠ 0 := by
      have : ContinuousAt (fun z : ℂ => 1 - z * Complex.I) 1 := by fun_prop
      exact this.eventually_ne (by intro h; have := congrArg Complex.re h; simp at this)
    filter_upwards [hq_cont.eventually (Complex.isOpen_slitPlane.mem_nhds hq), hne] with z hqz hnz
    unfold sInv Complex.arctan
    have hqd : DifferentiableAt ℂ (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) z :=
      DifferentiableAt.div (by fun_prop) (by fun_prop) hnz
    exact ((hqd.clog hqz).const_mul (-Complex.I / 2)).const_mul (4 / (π : ℂ))
  obtain ⟨ρ2, hρ2, hdiff_s⟩ := Metric.eventually_nhds_iff_ball.mp hd_nhds
  set ρ := min ρ1 ρ2 with hρ
  have hρpos : 0 < ρ := lt_min hρ1 hρ2
  refine ⟨fun z => Complex.exp (H (1 - sInv z)), ρ, hρpos, ?_, fun z _ => Complex.exp_ne_zero _, ?_⟩
  · intro z hz
    have hz1 : z ∈ ball (1 : ℂ) ρ1 := mem_ball.2 ((mem_ball.1 hz).trans_le (min_le_left _ _))
    have hz2 : z ∈ ball (1 : ℂ) ρ2 := mem_ball.2 ((mem_ball.1 hz).trans_le (min_le_right _ _))
    have hball : 1 - sInv z ∈ ball (0 : ℂ) δ := by
      have := hS hz1
      rwa [dist_eq_norm, sInv_one, norm_sub_rev, ← show ‖1 - sInv z - 0‖ = ‖1 - sInv z‖ by simp,
        ← dist_eq_norm] at this
    have h1s : DifferentiableAt ℂ (fun w => 1 - sInv w) z := (hdiff_s z hz2).const_sub 1
    exact ((hH.differentiableAt (isOpen_ball.mem_nhds hball)).comp z h1s).cexp.differentiableWithinAt
  · intro z hz hzn
    have hz1 : z ∈ ball (1 : ℂ) ρ1 := mem_ball.2 (by rw [dist_eq_norm]; exact hzn.trans_le (min_le_left _ _))
    have hball : 1 - sInv z ∈ ball (0 : ℂ) δ := by
      have := hS hz1
      rwa [dist_eq_norm, sInv_one, norm_sub_rev, ← show ‖1 - sInv z - 0‖ = ‖1 - sInv z‖ by simp,
        ← dist_eq_norm] at this
    have hs : sInv z ∈ closedStrip :=
      sInv_mem_closedStrip hz.1 (ne_of_mem_diff hz).1 (ne_of_mem_diff hz).2
    have h1s : 1 - sInv z ∈ closedStrip := ⟨by simp [hs.2], by simp [hs.1]⟩
    unfold GA4
    rw [← hbarA_oneSub (amp_aRel hA) hs, hbarA_eq_local hH0 heq0 (by rw [hc]; exact hball) h1s]

/-- Boundary modulus of `GA4` on the slit `z = iy` and paired arc `z = e^{-iψ}`. -/
theorem GA4_modulus {A : ℝ → ℝ} (hA : JetAmplitude A) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖GA4 A (Complex.I * (y : ℂ))‖ = A (xOf y) / A xiStar ∧
      ‖GA4 A (starRingEnd ℂ (wPt y))‖ = A (xOf y) / A xiStar := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  set τ : ℝ := slitTau y
  have htanh : Real.tanh (π * τ / 4) = y := tanh_slitTau hy
  have hAx : 0 < A (xOf y) := lt_of_lt_of_le hlo (hAlo _ (by
    rw [← htanh, xOf_tanh]; exact xiStar_le_xT τ))
  have hxτ : xT τ = xOf y := by rw [← htanh, xOf_tanh]
  have ha : aRel A τ = Real.log (A (xOf y) / A xiStar) := by
    unfold aRel; rw [hxτ]
  have hs1 : sInv (Complex.I * (y : ℂ)) = Complex.I * (τ : ℂ) := by
    rw [sInv_slit hy, mul_comm]
  have hs2 : sInv (starRingEnd ℂ (wPt y)) = 1 - Complex.I * (τ : ℂ) := by
    rw [conj_wPt, sInv_sigma_slit hy, mul_comm]
  unfold GA4
  rw [hs1, hs2, Complex.norm_exp, Complex.norm_exp,
    hbarA_oneSub (amp_aRel hA) (by rw [mul_comm]; exact slit_mem_closedStrip _),
    re_hbarA_left (amp_aRel hA) τ, ha, Real.exp_log (div_pos hAx hAξ)]
  exact ⟨rfl, rfl⟩

end FormalResearch.ModularBootstrap.Mixtures

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.goutWA_outerDatum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.goutWA_outerDatum

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.comb_minimum_WA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.comb_minimum_WA

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.comb_regularisation_WA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.comb_regularisation_WA

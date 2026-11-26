module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterBridge

/-!
# FIVE-S, S1 (`H₃`): holomorphy, zero-freeness, normalisation, slit modulus

`H₃(z) = (1 + sin πs) S(u(z))² / (π² ξ_*²)` with `s = sInv z`, `u = uC`, `S = sInt`, on `Ω = halfDisc`.
Inputs: `Re (1 + sin πs) > 0` on the strip, `Re S(u) > 0` for `u ∈ ℂ ∖ (-∞,-1]` (`re_sInt_pos`), `u(Ω) ⊆ sDom`
(`uC_mem_sHatDom`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma re_one_add_sin_pos {s : ℂ} (hs : s ∈ unitStrip) : 0 < (1 + Complex.sin ((π : ℂ) * s)).re := by
  have h := sin_re' ((π : ℂ) * s)
  rw [Complex.add_re, Complex.one_re, h]
  have hpi := Real.pi_pos
  have h1 : 0 < Real.sin (((π : ℂ) * s).re) := by
    have : ((π : ℂ) * s).re = π * s.re := by simp
    rw [this]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have h2 : 0 < Real.cosh (((π : ℂ) * s).im) := Real.cosh_pos _
  nlinarith [mul_pos h1 h2]

lemma one_add_sin_mem_slit {s : ℂ} (hs : s ∈ unitStrip) :
    1 + Complex.sin ((π : ℂ) * s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; exact re_one_add_sin_pos hs

lemma sInt_uC_mem_slit {z : ℂ} (hz : z ∈ halfDisc) : sInt (uC z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; exact re_sInt_pos (uC_mem_sHatDom hz).1

lemma sInt_uC_ne_zero {z : ℂ} (hz : z ∈ halfDisc) : sInt (uC z) ≠ 0 :=
  sInt_ne_zero (uC_mem_sHatDom hz).1

lemma H3_ne_zero {z : ℂ} (hz : z ∈ halfDisc) : H3 z ≠ 0 := by
  unfold H3
  have hs : sInv z ∈ unitStrip := sInv_mem_strip hz
  exact div_ne_zero (mul_ne_zero (Complex.slitPlane_ne_zero (one_add_sin_mem_slit hs))
    (pow_ne_zero 2 (sInt_uC_ne_zero hz))) pi_xi_ne

lemma differentiableOn_H3 : DifferentiableOn ℂ H3 halfDisc := by
  intro z hz
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hcl : z ∈ closure halfDisc := subset_closure hz
  have hsI : DifferentiableAt ℂ sInv z := differentiableAt_sInv hcl h1 h2
  have hS : DifferentiableAt ℂ (fun w => sInt (uC w)) z := by
    have h3 : DifferentiableAt ℂ sInt (uC z) :=
      differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (uC_mem_sHatDom hz).1)
    exact h3.comp z (differentiableOn_uC.differentiableAt (isOpen_halfDisc.mem_nhds hz))
  unfold H3
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div_const (DifferentiableAt.mul ?_ (hS.pow 2)) _
  exact (differentiableAt_const _).add (((differentiableAt_const _).mul hsI).csin)

lemma sInt_one : sInt 1 = ((Real.arsinh 1 : ℝ) : ℂ) := by
  have := sInt_pos_real (c := 1) one_pos
  simpa using this

lemma H3_zero : H3 0 = 1 := by
  unfold H3
  have hu : uC 0 = 1 := by simp [uC]
  rw [hu, sInt_one, sInv_zero]
  simp only [mul_zero, Complex.sin_zero, add_zero, one_mul]
  have hpi := Real.pi_pos
  have hx : (xiStar : ℂ) = ((Real.arsinh 1 / π : ℝ) : ℂ) := rfl
  have h1 : Real.arsinh 1 ≠ 0 := (Real.arsinh_pos_iff.mpr one_pos).ne'
  rw [hx]
  push_cast
  field_simp


lemma real_mem_halfDisc {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : (r : ℂ) ∈ halfDisc := by
  refine ⟨?_, by simpa using hr.1⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]; exact hr.2

lemma sInt_real_pos {c : ℝ} (hc : (c : ℂ) ∈ sDom) : ∃ b : ℝ, 0 < b ∧ sInt (c : ℂ) = (b : ℂ) := by
  have hconj : sInt (starRingEnd ℂ (c : ℂ)) = starRingEnd ℂ (sInt (c : ℂ)) := sInt_conj hc
  rw [Complex.conj_ofReal] at hconj
  have him : (sInt (c : ℂ)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  refine ⟨(sInt (c : ℂ)).re, re_sInt_pos hc, ?_⟩
  apply Complex.ext <;> simp [him]

/-- On `(0,1)`: `1 + sin(π s(r))` and `S(u(r))` are positive reals. -/
lemma real_vals {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 1 + Complex.sin ((π : ℂ) * sInv (r : ℂ)) = (a : ℂ) ∧
      sInt (uC (r : ℂ)) = (b : ℂ) := by
  have hz := real_mem_halfDisc hr
  have hs : sInv (r : ℂ) ∈ unitStrip := sInv_mem_strip hz
  have hconj : sInv (starRingEnd ℂ (r : ℂ)) = starRingEnd ℂ (sInv (r : ℂ)) := sInv_conj hz
  rw [Complex.conj_ofReal] at hconj
  have him : (sInv (r : ℂ)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  have hsr : sInv (r : ℂ) = (((sInv (r : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hpi := Real.pi_pos
  have h1 : 0 < Real.sin (π * (sInv (r : ℂ)).re) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])
  obtain ⟨b, hb, hbS⟩ : ∃ b : ℝ, 0 < b ∧ sInt (uC (r : ℂ)) = (b : ℂ) := by
    have hu : uC (r : ℂ) = (((1 - 6 * r ^ 2 + r ^ 4) / (1 + r ^ 2) ^ 2 : ℝ) : ℂ) := by
      unfold uC; push_cast; ring
    have hmem : (((1 - 6 * r ^ 2 + r ^ 4) / (1 + r ^ 2) ^ 2 : ℝ) : ℂ) ∈ sDom := hu ▸ (uC_mem_sHatDom hz).1
    rw [hu]
    exact sInt_real_pos hmem
  refine ⟨1 + Real.sin (π * (sInv (r : ℂ)).re), b, by linarith, hb, ?_, hbS⟩
  conv_lhs => rw [hsr]
  push_cast
  rfl

lemma H3_real_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < (H3 (r : ℂ)).re ∧ (H3 (r : ℂ)).im = 0 := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := real_vals hr
  have hpi := Real.pi_pos; have hxi := xiStar_pos
  have : H3 (r : ℂ) = ((a * b ^ 2 / (π ^ 2 * xiStar ^ 2) : ℝ) : ℂ) := by
    unfold H3; rw [h1, h2]; push_cast; ring
  rw [this, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by positivity, rfl⟩

lemma uC_slit {y : ℝ} : uC (Complex.I * (y : ℂ)) = ((uSlit y : ℝ) : ℂ) := by
  unfold uC uSlit
  have : (Complex.I * (y : ℂ)) ^ 2 = ((-(y ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have h4 : (Complex.I * (y : ℂ)) ^ 4 = ((y ^ 4 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_pow_four]; push_cast; ring
  rw [this, h4]
  push_cast
  ring_nf

/-- **`OuterS1` (2), slit modulus**: `|H₃(iy)| = (x(y)/ξ_*)²`. -/
lemma norm_H3_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : ‖H3 (Complex.I * (y : ℂ))‖ = (xOf y / xiStar) ^ 2 := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  set τ : ℝ := slitTau y with hτ
  have htanh : Real.tanh (π * τ / 4) = y := tanh_slitTau hy'
  have hu1 : 1 < uSlit y := uSlit_gt_one hy0 hy1
  have hu0 : 0 < uSlit y := by linarith
  have hcosh : Real.cosh (π * τ) = uSlit y := by
    have := uSlit_tanh (π * τ / 4)
    rw [htanh] at this
    rw [this]; congr 1; ring
  have hpi := Real.pi_pos; have hxi := xiStar_pos
  unfold H3
  rw [sInv_slit hy', uC_slit, sInt_pos_real hu0]
  have hsin : Complex.sin ((π : ℂ) * ((τ : ℂ) * Complex.I)) = ((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I := by
    rw [← mul_assoc, show (π : ℂ) * (τ : ℂ) = ((π * τ : ℝ) : ℂ) by push_cast; rfl, Complex.sin_mul_I,
      ← Complex.ofReal_sinh]
  rw [hsin]
  have hn : ‖(1 : ℂ) + ((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I‖ = uSlit y := by
    have : (1 : ℂ) + ((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I =
        (((1 : ℝ)) : ℂ) + ((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_add_mul_I, ← hcosh]
    have := Real.cosh_sq (π * τ)
    rw [show (1 : ℝ) ^ 2 + Real.sinh (π * τ) ^ 2 = Real.cosh (π * τ) ^ 2 by nlinarith]
    exact Real.sqrt_sq (Real.cosh_pos _).le
  rw [norm_div, norm_mul, hn, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hden : ‖((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2)‖ = π ^ 2 * xiStar ^ 2 := by
    rw [show ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2) = ((π ^ 2 * xiStar ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hden]
  have hs : 0 < √(uSlit y) := Real.sqrt_pos.mpr hu0
  have hA : 0 < Real.arsinh (√(uSlit y)) := Real.arsinh_pos_iff.mpr hs
  rw [abs_of_pos (div_pos hA hs)]
  have hxo : xOf y = Real.arsinh (√(uSlit y)) / π := rfl
  rw [hxo, div_pow, div_pow, div_pow, Real.sq_sqrt hu0.le]
  field_simp


/-! ### The fourth root `R4` and `G̃` -/

private lemma cpow_quarter_pow (x : ℂ) : (x ^ (1 / 4 : ℂ)) ^ 4 = x := by
  have := Complex.cpow_nat_inv_pow x (n := 4) (by norm_num)
  rw [show (1 / 4 : ℂ) = ((4 : ℕ) : ℂ)⁻¹ by norm_num]
  exact this

private lemma cpow_half_pow (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  have := Complex.cpow_nat_inv_pow x (n := 2) (by norm_num)
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact this

/-- `κ = √(π ξ_*)`, `κ⁴ = π² ξ_*²`. -/
noncomputable def kap : ℝ := √(π * xiStar)

lemma kap_pos : 0 < kap := Real.sqrt_pos.mpr (mul_pos Real.pi_pos xiStar_pos)

lemma kap_pow4 : kap ^ 4 = π ^ 2 * xiStar ^ 2 := by
  unfold kap
  have h : 0 ≤ π * xiStar := (mul_pos Real.pi_pos xiStar_pos).le
  calc √(π * xiStar) ^ 4 = (√(π * xiStar) ^ 2) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt h]; ring

/-- The explicit fourth root of `H₃`: `R4 = (1 + sin πs)^{1/4} S(u)^{1/2} / κ`. -/
noncomputable def R4c (z : ℂ) : ℂ :=
  (1 + Complex.sin ((π : ℂ) * sInv z)) ^ (1 / 4 : ℂ) * (sInt (uC z)) ^ (1 / 2 : ℂ) / (kap : ℂ)

lemma R4c_pow_four {z : ℂ} : R4c z ^ 4 = H3 z := by
  unfold R4c H3
  have hk : ((kap : ℝ) : ℂ) ^ 4 = (π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2 := by
    exact_mod_cast kap_pow4
  rw [div_pow, mul_pow, cpow_quarter_pow, hk]
  have : ((sInt (uC z)) ^ (1 / 2 : ℂ)) ^ 4 = sInt (uC z) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, cpow_half_pow]
  rw [this]

lemma R4c_ne_zero {z : ℂ} (hz : z ∈ halfDisc) : R4c z ≠ 0 := by
  have hs : sInv z ∈ unitStrip := sInv_mem_strip hz
  unfold R4c
  have hk : ((kap : ℝ) : ℂ) ≠ 0 := by exact_mod_cast kap_pos.ne'
  refine div_ne_zero (mul_ne_zero ?_ ?_) hk
  · rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    intro h; exact absurd h (Complex.slitPlane_ne_zero (one_add_sin_mem_slit hs))
  · rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    intro h; exact absurd h (sInt_uC_ne_zero hz)

lemma differentiableOn_R4c : DifferentiableOn ℂ R4c halfDisc := by
  intro z hz
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hcl : z ∈ closure halfDisc := subset_closure hz
  have hsI : DifferentiableAt ℂ sInv z := differentiableAt_sInv hcl h1 h2
  have hS : DifferentiableAt ℂ (fun w => sInt (uC w)) z := by
    have h3 : DifferentiableAt ℂ sInt (uC z) :=
      differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (uC_mem_sHatDom hz).1)
    exact h3.comp z (differentiableOn_uC.differentiableAt (isOpen_halfDisc.mem_nhds hz))
  have hA : DifferentiableAt ℂ (fun w => 1 + Complex.sin ((π : ℂ) * sInv w)) z :=
    (differentiableAt_const _).add (((differentiableAt_const _).mul hsI).csin)
  have hs : sInv z ∈ unitStrip := sInv_mem_strip hz
  unfold R4c
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((hA.cpow_const (one_add_sin_mem_slit hs)).mul (hS.cpow_const (sInt_uC_mem_slit hz))).div_const _

lemma R4c_real_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < (R4c (r : ℂ)).re ∧ (R4c (r : ℂ)).im = 0 := by
  obtain ⟨a, b, ha, hb, h1, h2⟩ := real_vals hr
  have hk := kap_pos
  have : R4c (r : ℂ) = ((a ^ (1 / 4 : ℝ) * b ^ (1 / 2 : ℝ) / kap : ℝ) : ℂ) := by
    unfold R4c
    rw [h1, h2]
    push_cast
    rw [Complex.ofReal_cpow ha.le, Complex.ofReal_cpow hb.le]
    push_cast
    rfl
  rw [this, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨by positivity, rfl⟩

lemma norm_R4c_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : ‖R4c (Complex.I * (y : ℂ))‖ = √(xOf y / xiStar) := by
  have h4 : ‖R4c (Complex.I * (y : ℂ))‖ ^ 4 = (xOf y / xiStar) ^ 2 := by
    rw [← norm_pow, R4c_pow_four, norm_H3_slit hy]
  have hx := xOf_pos hy
  have hxi := xiStar_pos
  have hq : 0 < xOf y / xiStar := div_pos hx hxi
  have hn := norm_nonneg (R4c (Complex.I * (y : ℂ)))
  have h2 : (‖R4c (Complex.I * (y : ℂ))‖ ^ 2) ^ 2 = (xOf y / xiStar) ^ 2 := by rw [← h4]; ring
  have h3 : ‖R4c (Complex.I * (y : ℂ))‖ ^ 2 = xOf y / xiStar :=
    (pow_left_inj₀ (by positivity : 0 ≤ ‖R4c (Complex.I * (y : ℂ))‖ ^ 2) hq.le two_ne_zero).mp h2
  rw [← h3, Real.sqrt_sq hn]

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

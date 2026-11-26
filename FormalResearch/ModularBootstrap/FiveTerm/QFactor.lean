module

public import FormalResearch.ModularBootstrap.FiveTerm.SchwarzSBoundary
public import FormalResearch.ModularBootstrap.FiveTerm.BoundaryExt

/-!
# The antisymmetric factor `Q = Ŝ(u(z))^{1/2}`: symmetries and the tip (FIVE-0 slice 2c)

`qHat z = Ŝ(u(z)) = S(-u(z))/S(u(z))` (`cts:R-id`: `Q⁴ = (S(-u)/S(u))²`, `Q = Ŝ^{1/2}`).

* `qHat_conj`: `qHat(z̄) = conj(qHat z)` on `Ω`; `qHat_sigma`: `qHat(σ z) = (qHat z)⁻¹` on `Ω`;
* the tip: with `m(z) = 2√2 z/(1+z²)` one has `u = 1 - m²` and, for `Re m > 0`, `|m| < 1`,
  `S(m² - 1) = (π/2 - m S(-m²))/√(1-m²)` (`sInt_sub_one_sq`), so `qHat` extends holomorphically across `z = 0`
  (`tipExt`), with the value `π/(2 S(1))` there.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `Ŝ(u(z)) = S(-u(z))/S(u(z))`. -/
noncomputable def qHat (z : ℂ) : ℂ := sHat (uC z)

lemma uC_conj (z : ℂ) : uC (starRingEnd ℂ z) = starRingEnd ℂ (uC z) := by
  simp [uC, map_ofNat]

lemma sInt_conj {v : ℂ} (hv : v ∈ sDom) : sInt (starRingEnd ℂ v) = starRingEnd ℂ (sInt v) := by
  unfold sInt
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have hslit := one_add_mul_mem_slit hv ht
  have harg := Complex.slitPlane_arg_ne_pi hslit
  have e : 1 + starRingEnd ℂ v * (t : ℂ) ^ 2 = starRingEnd ℂ (1 + v * (t : ℂ) ^ 2) := by simp
  simp only [e]
  rw [Complex.conj_cpow _ _ harg]
  simp [map_ofNat]

lemma neg_conj (u : ℂ) : -(starRingEnd ℂ u) = starRingEnd ℂ (-u) := by simp

lemma sHatDom_conj {u : ℂ} (hu : u ∈ sHatDom) : starRingEnd ℂ u ∈ sHatDom := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, ?_⟩
  · rintro ⟨him, hre⟩; apply h1; simp at him hre; exact ⟨by simpa using him, hre⟩
  · rintro ⟨him, hre⟩; apply h2; simp at him hre
    exact ⟨by simpa using him, by simp only [Complex.neg_re]; linarith⟩

lemma sHat_conj {u : ℂ} (hu : u ∈ sHatDom) : sHat (starRingEnd ℂ u) = starRingEnd ℂ (sHat u) := by
  unfold sHat
  rw [neg_conj, sInt_conj hu.2, sInt_conj hu.1, map_div₀]

lemma halfDisc_conj {z : ℂ} (hz : z ∈ halfDisc) : starRingEnd ℂ z ∈ halfDisc := by
  obtain ⟨h1, h2⟩ := hz
  exact ⟨by simpa using h1, by simpa using h2⟩

lemma qHat_conj {z : ℂ} (hz : z ∈ halfDisc) : qHat (starRingEnd ℂ z) = starRingEnd ℂ (qHat z) := by
  unfold qHat
  rw [uC_conj, sHat_conj (uC_mem_sHatDom hz)]

/-- The involution `σ(z) = (1-z)/(1+z)` maps `Ω` to itself (here: the identity `qHat ∘ σ = (qHat)⁻¹`). -/
lemma qHat_sigma {z : ℂ} (hz : z ∈ halfDisc) : qHat ((1 - z) / (1 + z)) = (qHat z)⁻¹ := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  have hz1 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := eq_neg_of_add_eq_zero_right h
    have h1 := hz.2; rw [this] at h1; norm_num at h1
  unfold qHat
  rw [uC_sigma hne hz1, sHat_neg (uC_mem_sHatDom hz)]

lemma qHat_ne_zero {z : ℂ} (hz : z ∈ halfDisc) : qHat z ≠ 0 := by
  have h := sHat_mem_slit (uC_mem_sHatDom hz)
  exact Complex.slitPlane_ne_zero h

lemma qHat_mem_slit {z : ℂ} (hz : z ∈ halfDisc) : qHat z ∈ Complex.slitPlane :=
  sHat_mem_slit (uC_mem_sHatDom hz)

lemma differentiableOn_qHat : DifferentiableOn ℂ qHat halfDisc := by
  intro z hz
  have h1 : DifferentiableAt ℂ sHat (uC z) :=
    differentiableOn_sHat.differentiableAt (isOpen_sHatDom.mem_nhds (uC_mem_sHatDom hz))
  have h2 : DifferentiableAt ℂ uC z :=
    differentiableOn_uC.differentiableAt (isOpen_halfDisc.mem_nhds hz)
  exact (h1.comp z h2).differentiableWithinAt

/-! ### The tip -/

/-- `m(z) = 2√2 z/(1+z²)`, so that `u = 1 - m²`. -/
noncomputable def mC (z : ℂ) : ℂ := (2 * (√2 : ℂ)) * z / (1 + z ^ 2)

lemma uC_eq_one_sub_mC_sq {z : ℂ} (hz : 1 + z ^ 2 ≠ 0) : uC z = 1 - mC z ^ 2 := by
  have h := one_sub_uC hz
  unfold mC
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  have : (2 * ((√2 : ℝ) : ℂ) * z / (1 + z ^ 2)) ^ 2 = 8 * z ^ 2 / (1 + z ^ 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, h2]; ring
  rw [this, ← h]; ring

/-- `E₁(m) = (π/2 - m S(-m²)) / √(1-m²)`, holomorphic on the unit disc; `E₁(m) = S(m²-1)` for `Re m > 0`. -/
noncomputable def tipE (m : ℂ) : ℂ :=
  ((π : ℂ) / 2 - m * sInt (-(m ^ 2))) / (1 - m ^ 2) ^ (1 / 2 : ℂ)

lemma neg_sq_mem_sDom {m : ℂ} (hm : ‖m‖ < 1) : -(m ^ 2) ∈ sDom := by
  rintro ⟨him, hre⟩
  have h1 : ‖m ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hm (by norm_num)
  have h2 : (m ^ 2).re ≤ ‖m ^ 2‖ := Complex.re_le_norm _
  simp at hre
  linarith

lemma one_sub_sq_mem_slit {m : ℂ} (hm : ‖m‖ < 1) : 1 - m ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have h1 : ‖m ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hm (by norm_num)
  have h2 : (m ^ 2).re ≤ ‖m ^ 2‖ := Complex.re_le_norm _
  simp; linarith

lemma differentiableOn_tipE : DifferentiableOn ℂ tipE (ball (0 : ℂ) 1) := by
  intro m hm
  have hm' : ‖m‖ < 1 := by simpa using hm
  have h1 : DifferentiableAt ℂ (fun m : ℂ => sInt (-(m ^ 2))) m := by
    have h2 : DifferentiableAt ℂ sInt (-(m ^ 2)) :=
      differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (neg_sq_mem_sDom hm'))
    exact DifferentiableAt.comp (g := sInt) (f := fun m : ℂ => -(m ^ 2)) m h2
      (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun m : ℂ => (1 - m ^ 2) ^ (1 / 2 : ℂ)) m :=
    DifferentiableAt.cpow_const (by fun_prop) (one_sub_sq_mem_slit hm')
  have h4 : (1 - m ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact Complex.slitPlane_ne_zero (one_sub_sq_mem_slit hm') h.1
  have hnum : DifferentiableAt ℂ (fun m : ℂ => (π : ℂ) / 2 - m * sInt (-(m ^ 2))) m :=
    (differentiableAt_const _).sub (differentiableAt_id.mul h1)
  exact (hnum.div h3 h4).differentiableWithinAt

/-- `S(-c) = arcsin(√c)/√c` for real `0 < c ≤ 1`. -/
lemma sInt_neg_real {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    sInt (-(c : ℂ)) = ((Real.arcsin (√c) / √c : ℝ) : ℂ) := by
  have hsc : 0 < √c := Real.sqrt_pos.mpr hc
  have hsc1 : √c * 1 ≤ 1 := by
    rw [mul_one, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1
  unfold sInt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have : ∀ t ∈ uIcc (0 : ℝ) 1, (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      ((1 / √(1 - c * t ^ 2) : ℝ) : ℂ) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have : (1 + (-(c : ℂ)) * (t : ℂ) ^ 2) = ((1 - c * t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact cpow_neg_half_ofReal_nonneg (by nlinarith [mul_le_mul_of_nonneg_left h1 hc.le])
  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_ofReal]
  have h := (integral_inv_sqrt_one_sub hc zero_le_one hsc1).1
  rw [h, mul_one]

lemma tip_identity_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    sInt (((x : ℂ)) ^ 2 - 1) = tipE (x : ℂ) := by
  have hc : 0 < 1 - x ^ 2 := by nlinarith
  have hsq : 0 < x ^ 2 := by positivity
  have e1 : ((x : ℂ)) ^ 2 - 1 = -(((1 - x ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  have e2 : -((x : ℂ) ^ 2) = -((x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, sInt_neg_real hc (by nlinarith)]
  unfold tipE
  rw [e2, sInt_neg_real hsq (by nlinarith)]
  have e3 : (1 - (x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((√(1 - x ^ 2) : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow hc.le (1 / 2 : ℝ)
    rw [show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at h
    have e : (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, ← h, ← Real.sqrt_eq_rpow]
  rw [e3]
  have hs : √(x ^ 2) = x := Real.sqrt_sq hx0.le
  have harcsin : Real.arcsin (√(1 - x ^ 2)) = π / 2 - Real.arcsin x := by
    rw [Real.arcsin_eq_arccos (Real.sqrt_nonneg _), Real.sq_sqrt hc.le,
      show 1 - (1 - x ^ 2) = x ^ 2 by ring, hs, Real.arccos_eq_pi_div_two_sub_arcsin]
  have hsp : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr hc
  rw [hs, harcsin]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  push_cast
  field_simp

/-- `S(m² - 1) = (π/2 - m S(-m²))/√(1-m²)` for `|m| < 1`, `Re m > 0`. -/
theorem sInt_sub_one_sq {m : ℂ} (hm : ‖m‖ < 1) (hre : 0 < m.re) : sInt (m ^ 2 - 1) = tipE m := by
  set U : Set ℂ := {m : ℂ | ‖m‖ < 1 ∧ 0 < m.re} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_re)
  have hUc : Convex ℝ U := by
    have h1 : Convex ℝ {m : ℂ | ‖m‖ < 1} := by
      simpa [Metric.ball, dist_eq_norm] using convex_ball (0 : ℂ) 1
    have h2 : Convex ℝ {m : ℂ | 0 < m.re} := convex_halfSpace_re_gt 0
    exact h1.inter h2
  have hmem : ∀ m ∈ U, m ^ 2 - 1 ∈ sDom := by
    rintro m ⟨hm1, hm2⟩ ⟨him, hre'⟩
    have him2 : (m ^ 2).im = 2 * m.re * m.im := by simp [pow_two, Complex.mul_im]; ring
    have hre2 : (m ^ 2).re = m.re ^ 2 - m.im ^ 2 := by simp [pow_two, Complex.mul_re]
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at him
    simp only [Complex.sub_re, Complex.one_re] at hre'
    rw [him2] at him
    have : m.im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · rcases mul_eq_zero.mp h with h | h <;> [norm_num at h; linarith]
      · exact h
    rw [hre2, this] at hre'
    nlinarith [sq_nonneg m.re, sq_pos_of_pos hm2]
  have hf : DifferentiableOn ℂ (fun m : ℂ => sInt (m ^ 2 - 1)) U := by
    intro m hmU
    have h2 : DifferentiableAt ℂ sInt (m ^ 2 - 1) :=
      differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (hmem m hmU))
    exact (DifferentiableAt.comp (g := sInt) (f := fun m : ℂ => m ^ 2 - 1) m h2
      (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ tipE U := differentiableOn_tipE.mono (by
    intro m hm; simpa using hm.1)
  have hfa := hf.analyticOnNhd hUo
  have hga := hg.analyticOnNhd hUo
  have hz0 : ((1 / 2 : ℝ) : ℂ) ∈ U := ⟨by rw [Complex.norm_real]; norm_num, by simp⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 / 2 : ℝ) : ℂ), sInt (z ^ 2 - 1) = tipE z := by
    rw [Filter.frequently_iff]
    intro s hs
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hs
    set δ : ℝ := min (ε / 2) (1 / 4) with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(((1 / 2 : ℝ) + δ : ℝ) : ℂ), hsub ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [Complex.ofReal_add, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδpos]
      have : δ ≤ ε / 2 := min_le_left _ _
      linarith
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have := Complex.ofReal_injective h
      linarith
    · exact tip_identity_real (by have : δ > 0 := hδpos; linarith)
        (by have : δ ≤ 1 / 4 := min_le_right _ _; linarith)
  exact hfa.eqOn_of_preconnected_of_frequently_eq hga hUc.isPreconnected hz0 hfreq ⟨hm, hre⟩

lemma re_mC_pos {z : ℂ} (hz : z ∈ halfDisc) : 0 < (mC z).re := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  have h := re_div_one_add_sq_pos hz.2 hne
  have e : mC z = (2 * (√2 : ℂ)) * (z / (1 + z ^ 2)) := by unfold mC; ring
  rw [e]
  have h2 : (2 * (√2 : ℂ)) = ((2 * √2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.re_ofReal_mul]
  exact mul_pos (by positivity) h

lemma norm_mC_lt_one {z : ℂ} (hz : ‖z‖ < 1 / 4) : ‖mC z‖ < 1 := by
  have hz2 : ‖z ^ 2‖ < 1 / 16 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hden : 15 / 16 ≤ ‖1 + z ^ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(z ^ 2))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have hden0 : 0 < ‖1 + z ^ 2‖ := by linarith
  unfold mC
  rw [norm_div, div_lt_one hden0, norm_mul]
  have h2 : ‖(2 * (√2 : ℂ))‖ = 2 * √2 := by
    rw [norm_mul]; simp
  rw [h2]
  have : √2 < 15 / 8 := by
    rw [show (15 / 8 : ℝ) = √((15 / 8) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith [norm_nonneg z]

lemma uC_mem_sDom_of_small {z : ℂ} (hz : ‖z‖ < 1 / 4) : uC z ∈ sDom := by
  have hz2 : ‖z ^ 2‖ < 1 / 16 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hne : 1 + z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    rw [this] at hz2; norm_num at hz2
  rw [uC_eq_one_sub_mC_sq hne]
  have hm := norm_mC_lt_one hz
  have h1 : ‖mC z ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hm (by norm_num)
  have h2 : (mC z ^ 2).re ≤ ‖mC z ^ 2‖ := Complex.re_le_norm _
  rintro ⟨him, hre⟩
  simp at hre
  linarith

/-- The holomorphic extension of `qHat` across the tip `z = 0`. -/
noncomputable def tipExt (z : ℂ) : ℂ := tipE (mC z) / sInt (uC z)

lemma qHat_eq_tipExt {z : ℂ} (hz : z ∈ halfDisc) (hz4 : ‖z‖ < 1 / 4) : qHat z = tipExt z := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  have hu := uC_eq_one_sub_mC_sq hne
  unfold qHat sHat tipExt
  have : -uC z = mC z ^ 2 - 1 := by rw [hu]; ring
  rw [this, sInt_sub_one_sq (norm_mC_lt_one hz4) (re_mC_pos hz)]

lemma differentiableOn_tipExt : DifferentiableOn ℂ tipExt (ball (0 : ℂ) (1 / 4)) := by
  intro z hz
  have hz4 : ‖z‖ < 1 / 4 := by simpa using hz
  have hz2 : ‖z ^ 2‖ < 1 / 16 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hne : 1 + z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    rw [this] at hz2; norm_num at hz2
  have hm : DifferentiableAt ℂ mC z := by
    unfold mC
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) hne
  have h1 : DifferentiableAt ℂ tipE (mC z) :=
    differentiableOn_tipE.differentiableAt (isOpen_ball.mem_nhds (by simpa using norm_mC_lt_one hz4))
  have hu : DifferentiableAt ℂ uC z := by
    unfold uC
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hne)
  have h2 : DifferentiableAt ℂ sInt (uC z) :=
    differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (uC_mem_sDom_of_small hz4))
  have h3 : DifferentiableAt ℂ (fun z => sInt (uC z)) z :=
    DifferentiableAt.comp (g := sInt) (f := uC) z h2 hu
  have h4 : DifferentiableAt ℂ (fun z => tipE (mC z)) z :=
    DifferentiableAt.comp (g := tipE) (f := mC) z h1 hm
  exact (h4.div h3 (sInt_ne_zero (uC_mem_sDom_of_small hz4))).differentiableWithinAt

lemma uC_zero : uC 0 = 1 := by simp [uC]

lemma mC_zero : mC 0 = 0 := by simp [mC]

lemma tipE_zero : tipE 0 = (π : ℂ) / 2 := by
  simp [tipE]

lemma tipExt_zero : tipExt 0 = ((π / 2 / Real.arsinh 1 : ℝ) : ℂ) := by
  unfold tipExt
  rw [mC_zero, uC_zero, tipE_zero]
  have := sInt_pos_real (c := 1) one_pos
  simp only [Complex.ofReal_one, Real.sqrt_one, div_one] at this
  rw [this]
  push_cast; ring

/-! ### The slit `z = i y` -/

/-- `u(iy) = (1 + 6y² + y⁴)/(1 - y²)²`. -/
noncomputable def uSlit (y : ℝ) : ℝ := (1 + 6 * y ^ 2 + y ^ 4) / (1 - y ^ 2) ^ 2

lemma uSlit_gt_one {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 1 < uSlit y := by
  have hd : 0 < (1 - y ^ 2) ^ 2 := by
    have : 0 < 1 - y ^ 2 := by nlinarith
    positivity
  unfold uSlit
  rw [lt_div_iff₀ hd]
  nlinarith [pow_pos hy0 2]

lemma uC_I_mul (y : ℝ) : uC (Complex.I * (y : ℂ)) = ((uSlit y : ℝ) : ℂ) := by
  unfold uC uSlit
  push_cast
  have : (Complex.I * (y : ℂ)) ^ 2 = -(y : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  have h4 : (Complex.I * (y : ℂ)) ^ 4 = (y : ℂ) ^ 4 := by
    have : (Complex.I * (y : ℂ)) ^ 4 = ((Complex.I * (y : ℂ)) ^ 2) ^ 2 := by ring
    rw [this]; ring_nf; simp
  rw [this, h4]
  ring_nf

lemma im_uC_neg {z : ℂ} (hz : z ∈ halfDisc) (hy : 0 < z.im) : (uC z).im < 0 := by
  have hne := one_add_sq_ne_zero_of_halfDisc hz
  have hr := re_one_sub_sq_div_pos hz.1 hne
  have h1 := one_add_uC hne
  set r := (1 - z ^ 2) / (1 + z ^ 2) with hrdef
  have him : r.im < 0 := by
    have hnpos : 0 < Complex.normSq (1 + z ^ 2) := by
      rw [Complex.normSq_pos]; exact hne
    rw [hrdef, Complex.div_im]
    have e1 : (1 - z ^ 2).im * (1 + z ^ 2).re / Complex.normSq (1 + z ^ 2) -
        (1 - z ^ 2).re * (1 + z ^ 2).im / Complex.normSq (1 + z ^ 2) =
        ((1 - z ^ 2).im * (1 + z ^ 2).re - (1 - z ^ 2).re * (1 + z ^ 2).im) /
          Complex.normSq (1 + z ^ 2) := by ring
    rw [e1]
    apply div_neg_of_neg_of_pos _ hnpos
    simp only [Complex.sub_im, Complex.add_im, Complex.sub_re, Complex.add_re, Complex.one_im,
      Complex.one_re, pow_two, Complex.mul_im, Complex.mul_re]
    nlinarith [mul_pos hz.2 hy]
  have : (uC z).im = 4 * r.re * r.im := by
    have := congrArg Complex.im h1
    rw [Complex.add_im, Complex.one_im, two_mul_im_aux] at this
    simp only [pow_two, Complex.mul_im] at this
    linarith
  rw [this]
  nlinarith [mul_pos hr (neg_pos.mpr him)]

/-- The boundary value of `Ŝ(u(z))` at `z = i y`: `(π/2 - i arsinh √(u₀-1))/arsinh √u₀` (`= (1/2 - i v_x)/x`). -/
noncomputable def slitVal (y : ℝ) : ℂ :=
  ((π : ℂ) / 2 - Complex.I * (Real.arsinh (√(uSlit y - 1)) : ℂ)) / (Real.arsinh (√(uSlit y)) : ℂ)

lemma tendsto_qHat_slit {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Tendsto qHat (𝓝[halfDisc] (Complex.I * (y : ℂ))) (𝓝 (slitVal y)) := by
  set z₀ : ℂ := Complex.I * (y : ℂ) with hz₀
  set u₀ : ℝ := uSlit y with hu₀def
  have hu₀ : 1 < u₀ := uSlit_gt_one hy0 hy1
  have hu₀pos : 0 < u₀ := by linarith
  have hne : 1 + z₀ ^ 2 ≠ 0 := by
    have : 1 + z₀ ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
      rw [hz₀, mul_pow, Complex.I_sq]; push_cast; ring
    rw [this]
    have : 0 < 1 - y ^ 2 := by nlinarith
    exact_mod_cast this.ne'
  set s : Set ℂ := halfDisc ∩ {z : ℂ | 0 < z.im} with hs
  have hsmem : s ∈ 𝓝[halfDisc] z₀ := by
    refine inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds ?_)
    refine (isOpen_lt continuous_const Complex.continuous_im).mem_nhds ?_
    simp [hz₀, hy0]
  have hu_cont : ContinuousAt uC z₀ := by
    unfold uC
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hne)
  have huz₀ : uC z₀ = (u₀ : ℂ) := uC_I_mul y
  have hK : ContinuousWithinAt sInt {v : ℂ | 0 ≤ v.im} (-(u₀ : ℂ)) :=
    continuousWithinAt_sInt_cut (by simp) (by simp; exact hu₀pos)
  have hmap : MapsTo (fun z => -uC z) s {v : ℂ | 0 ≤ v.im} := by
    intro z hz
    have := im_uC_neg hz.1 hz.2
    simp only [Set.mem_ofPred_eq, Complex.neg_im]
    linarith
  have hnum : Tendsto (fun z => sInt (-uC z)) (𝓝[s] z₀) (𝓝 (sInt (-(u₀ : ℂ)))) := by
    have hc : ContinuousWithinAt (fun z => -uC z) s z₀ := hu_cont.neg.continuousWithinAt
    have h : ContinuousWithinAt (fun z => sInt (-uC z)) s z₀ :=
      ContinuousWithinAt.comp (f := fun z => -uC z) (g := sInt) (s := s)
        (t := {v : ℂ | 0 ≤ v.im}) (x := z₀) (by rw [huz₀]; exact hK) hc hmap
    have h2 := h.tendsto
    rw [huz₀] at h2
    exact h2
  have hsd : (u₀ : ℂ) ∈ sDom := by
    rintro ⟨_, h⟩; simp at h; linarith
  have hden : Tendsto (fun z => sInt (uC z)) (𝓝[s] z₀) (𝓝 (sInt (u₀ : ℂ))) := by
    have h1 : ContinuousAt sInt (uC z₀) := by
      rw [huz₀]
      exact differentiableOn_sInt.continuousOn.continuousAt (isOpen_sDom.mem_nhds hsd)
    have h3 : ContinuousAt (fun z => sInt (uC z)) z₀ := h1.comp hu_cont
    have h4 := h3.tendsto.mono_left (nhdsWithin_le_nhds (s := s))
    rw [huz₀] at h4
    exact h4
  have hratio := hnum.div hden (sInt_ne_zero hsd)
  have hval : sInt (-(u₀ : ℂ)) / sInt (u₀ : ℂ) = slitVal y := by
    rw [sInt_oncut hu₀, sInt_pos_real hu₀pos]
    unfold slitVal
    rw [← hu₀def]
    have hb : 0 < Real.arsinh (√u₀) := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr hu₀pos)
    have hsq : 0 < √u₀ := Real.sqrt_pos.mpr hu₀pos
    have hb' : ((Real.arsinh (√u₀) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hsq' : ((√u₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
    push_cast
    field_simp
  rw [hval] at hratio
  exact hratio.mono_left (nhdsWithin_le_of_mem hsmem)

/-! ### Limits of `qHat` at every point of `closure Ω ∖ {±i}` -/

lemma closure_halfDisc_subset {z : ℂ} (hz : z ∈ closure halfDisc) : ‖z‖ ≤ 1 ∧ 0 ≤ z.re := by
  have hcl : IsClosed {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.re} :=
    (isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  exact closure_minimal (s := halfDisc) (t := {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.re})
    (fun w hw => ⟨hw.1.le, hw.2.le⟩) hcl hz

lemma tendsto_qHat_conj {w L : ℂ}
    (h : Tendsto qHat (𝓝[halfDisc] (starRingEnd ℂ w)) (𝓝 L)) :
    Tendsto qHat (𝓝[halfDisc] w) (𝓝 (starRingEnd ℂ L)) := by
  have hc : Tendsto (starRingEnd ℂ) (𝓝[halfDisc] w) (𝓝[halfDisc] (starRingEnd ℂ w)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_conj.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz using halfDisc_conj hz
  have h2 := (Complex.continuous_conj.tendsto L).comp (h.comp hc)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Function.comp]
  rw [qHat_conj hz, Complex.conj_conj]

lemma sigma_sigma_aux {w : ℂ} (h : 1 + w ≠ 0) : (1 - (1 - w) / (1 + w)) / (1 + (1 - w) / (1 + w)) = w := by
  have h2 : (1 + w) + (1 - w) ≠ 0 := by
    have : (1 + w) + (1 - w) = 2 := by ring
    rw [this]; norm_num
  field_simp
  ring

lemma tendsto_qHat_sigma {w L : ℂ} (hw : 1 + w ≠ 0) (hL : L ≠ 0)
    (h : Tendsto qHat (𝓝[halfDisc] w) (𝓝 L)) :
    Tendsto qHat (𝓝[halfDisc] ((1 - w) / (1 + w))) (𝓝 L⁻¹) := by
  set w' : ℂ := (1 - w) / (1 + w) with hw'
  have hw1 : 1 + w' ≠ 0 := by
    have : 1 + w' = 2 / (1 + w) := by rw [hw']; field_simp; ring
    rw [this]; exact div_ne_zero (by norm_num) hw
  have hσw' : (1 - w') / (1 + w') = w := sigma_sigma_aux hw
  have hcont : ContinuousAt (fun z : ℂ => (1 - z) / (1 + z)) w' :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hw1
  have hmap : Tendsto (fun z : ℂ => (1 - z) / (1 + z)) (𝓝[halfDisc] w') (𝓝[halfDisc] w) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := halfDisc))
      rwa [hσw'] at this
    · filter_upwards [self_mem_nhdsWithin] with z hz using sigmaHD_mem hz
  have h2 := (h.comp hmap).inv₀ hL
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Function.comp]
  rw [qHat_sigma hz, inv_inv]

lemma inv_mem_slitPlane' {L : ℂ} (hL : L ∈ Complex.slitPlane) : L⁻¹ ∈ Complex.slitPlane := by
  have hL0 := Complex.slitPlane_ne_zero hL
  have hn : 0 < Complex.normSq L := Complex.normSq_pos.mpr hL0
  rw [Complex.mem_slitPlane_iff] at hL ⊢
  rcases hL with h | h
  · left; rw [Complex.inv_re]; exact div_pos h hn
  · right; rw [Complex.inv_im]
    intro h'
    apply h
    have : -L.im / Complex.normSq L = 0 := h'
    rcases div_eq_zero_iff.mp this with h'' | h''
    · linarith
    · exact absurd h'' hn.ne'

lemma re_slitVal_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : 0 < (slitVal y).re := by
  unfold slitVal
  have hu : 1 < uSlit y := uSlit_gt_one hy0 hy1
  have hb : 0 < Real.arsinh (√(uSlit y)) :=
    Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by linarith))
  rw [Complex.div_ofReal_re]
  have : ((π : ℂ) / 2 - Complex.I * (Real.arsinh (√(uSlit y - 1)) : ℂ)).re = π / 2 := by
    simp
  rw [this]
  positivity

lemma tendsto_qHat_tip : Tendsto qHat (𝓝[halfDisc] 0) (𝓝 (tipExt 0)) := by
  have hcont : ContinuousAt tipExt 0 :=
    differentiableOn_tipExt.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simp))
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := halfDisc))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 4)))] with z hz hz4
  exact (qHat_eq_tipExt hz (by simpa using hz4)).symm

/-- Existence of limits on the slit `Re w = 0`, `|Im w| < 1`. -/
lemma exists_limit_qHat_slit {w : ℂ} (hre : w.re = 0) (him : |w.im| < 1) :
    ∃ L : ℂ, L ∈ Complex.slitPlane ∧ Tendsto qHat (𝓝[halfDisc] w) (𝓝 L) := by
  have hw : w = Complex.I * (w.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · -- lower slit: conjugate
    have hy : 0 < -w.im := by linarith
    have hy1 : -w.im < 1 := by have := abs_lt.mp him; linarith
    have hconj : starRingEnd ℂ w = Complex.I * ((-w.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    refine ⟨starRingEnd ℂ (slitVal (-w.im)), ?_, ?_⟩
    · rw [Complex.mem_slitPlane_iff]; left
      simpa using re_slitVal_pos hy hy1
    · apply tendsto_qHat_conj
      rw [hconj]
      exact tendsto_qHat_slit hy hy1
  · have : w = 0 := by
      rw [hw, hzero]; simp
    refine ⟨tipExt 0, ?_, ?_⟩
    · rw [tipExt_zero, Complex.mem_slitPlane_iff]; left
      simp only [Complex.ofReal_re]
      have : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos
      positivity
    · rw [this]; exact tendsto_qHat_tip
  · have hy1 : w.im < 1 := by have := abs_lt.mp him; linarith
    refine ⟨slitVal w.im, ?_, ?_⟩
    · rw [Complex.mem_slitPlane_iff]; left; exact re_slitVal_pos hpos hy1
    · have h := tendsto_qHat_slit hpos hy1
      have e : (Complex.I * (w.im : ℂ)) = w := hw.symm
      rw [e] at h; exact h

/-- **Limits of `Ŝ(u(z))` at every point of `closure Ω ∖ {±i}`**, with value in the slit plane. -/
lemma exists_limit_qHat {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) :
    ∃ L : ℂ, L ∈ Complex.slitPlane ∧ Tendsto qHat (𝓝[halfDisc] z) (𝓝 L) := by
  obtain ⟨hn, hr⟩ := closure_halfDisc_subset hz
  rcases hr.eq_or_lt with hr0 | hrpos
  · -- the slit
    have him : |z.im| < 1 := by
      have hz' : z = Complex.I * (z.im : ℂ) := by apply Complex.ext <;> simp [← hr0]
      have habs : ‖z‖ = |z.im| := by rw [hz']; simp
      rcases lt_or_eq_of_le (habs ▸ hn : |z.im| ≤ 1) with h | h
      · exact h
      · exfalso
        rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp h with h' | h'
        · apply h1; rw [hz', h']; simp
        · apply h2; rw [hz', h']; simp
    exact exists_limit_qHat_slit (by linarith) him
  · rcases hn.eq_or_lt with hn1 | hn1
    · -- the arc: use `σ`
      have hz1 : 1 + z ≠ 0 := by
        intro h; have : z = -1 := eq_neg_of_add_eq_zero_right h
        rw [this] at hrpos; norm_num at hrpos
      set w : ℂ := (1 - z) / (1 + z) with hw
      have hwre : w.re = 0 := by
        have hden : 0 < Complex.normSq (1 + z) := by
          rw [Complex.normSq_pos]; exact hz1
        rw [hw, Complex.div_re]
        have : (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im = 1 - ‖z‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
            Complex.one_im]
          ring
        rw [← add_div, this, hn1]; simp
      have hwim : |w.im| < 1 := by
        have hnorm : ‖w‖ < 1 := by
          rw [hw, norm_div, div_lt_one (norm_pos_iff.mpr hz1)]
          have : ‖1 - z‖ ^ 2 < ‖1 + z‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
            simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
              Complex.one_im]
            nlinarith
          exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
        have : |w.im| = ‖w‖ := by
          have hw' : w = Complex.I * (w.im : ℂ) := by apply Complex.ext <;> simp [hwre]
          rw [hw']; simp
        rw [this]; exact hnorm
      obtain ⟨L, hLslit, hLt⟩ := exists_limit_qHat_slit hwre hwim
      have hw1 : 1 + w ≠ 0 := by
        have : 1 + w = 2 / (1 + z) := by rw [hw]; field_simp; ring
        rw [this]; exact div_ne_zero (by norm_num) hz1
      have hσ := tendsto_qHat_sigma hw1 (Complex.slitPlane_ne_zero hLslit) hLt
      have hσσ : (1 - w) / (1 + w) = z := sigma_sigma_aux hz1
      rw [hσσ] at hσ
      refine ⟨L⁻¹, ?_, hσ⟩
      exact inv_mem_slitPlane' hLslit
    · -- interior
      have hzU : z ∈ halfDisc := ⟨hn1, hrpos⟩
      refine ⟨qHat z, qHat_mem_slit hzU, ?_⟩
      exact (differentiableOn_qHat.continuousOn.continuousAt (isOpen_halfDisc.mem_nhds hzU)).tendsto.mono_left
        nhdsWithin_le_nhds

end FormalResearch.ModularBootstrap.FiveTerm

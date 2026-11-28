module

public import FormalResearch.ModularBootstrap.Upper.Comb.Riesz
public import FormalResearch.Complex.SchwarzReflection

/-!
# Conformal Phase Coordinate `ζ(b)` for Local Strip Boas Positivity (`cts:boas` Step 1)

Formalizes Step 1 of Lemma C8 (`cts:boas`) in `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`:

* On `lowerBoasRightDom := {b : ℂ | xiStar < b.re ∧ |b.im| < 1 / 2}`, define `zetaRight c' b`
  by `zetaPlus c' b := (c' / (2 * π)) * (majorantHolomorphic b + I * (2 * π / 3) * b)` for `0 < b.im`,
  its Schwarz reflection `-zetaPlus c' b = conj (zetaPlus c' (conj b))` for `b.im < 0`, and
  `c' * cumulN b.re` on `(ξ_*, ∞)`.
* `differentiableOn_zetaRight`: holomorphic on `lowerBoasRightDom`, with `(deriv (zetaRight c') b).re > 0`.
* `zetaRight_im_abs_eq`: `2 * π * |(zetaRight c' b).im| = c' * (majorantUExt b + (2 * π / 3) * b.re)`.
* `zetaRight_injOn` and `zetaStrip_subset_zetaRight_image`: biholomorphism onto a domain containing
  `zetaStrip c' := {ζ : ℂ | 0 < ζ.re ∧ |ζ.im| < (c' / 3) * xiStar}`, with holomorphic inverse
  `bOfZeta c'`.
* `re_zetaRight_sub_cumulN_le` and `abs_zetaRight_im_lower`: geometric comparison bounds for `cts:h-growth`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. Definitions, Domains, and Conjugation Symmetry -/

/-- Upper half-strip conformal phase coordinate `ζ_+(b) = (c' / (2π)) (Φ_U(b) + i (2π/3) b)`. -/
noncomputable def zetaPlus (c' : ℝ) (b : ℂ) : ℂ :=
  ((c' / (2 * π) : ℝ) : ℂ) * (majorantHolomorphic b + Complex.I * ((2 * π / 3 : ℝ) : ℂ) * b)

/-- Extended conformal phase coordinate `ζ` on `{Re b > ξ_*, |Im b| < 1/2}` by Schwarz reflection. -/
noncomputable def zetaRight (c' : ℝ) (b : ℂ) : ℂ :=
  if 0 < b.im then zetaPlus c' b
  else if b.im < 0 then -zetaPlus c' b
  else ((c' * cumulN b.re : ℝ) : ℂ)

/-- Right half-strip `D_right = {b : ℂ | ξ_* < Re b ∧ |Im b| < 1/2}`. -/
def lowerBoasRightDom : Set ℂ := {b : ℂ | xiStar < b.re ∧ |b.im| < 1 / 2}

/-- Target conformal strip `U₀ = {ζ : ℂ | 0 < Re ζ ∧ |Im ζ| < (c'/3) ξ_*}`. -/
def zetaStrip (c' : ℝ) : Set ℂ := {ζ : ℂ | 0 < ζ.re ∧ |ζ.im| < (c' / 3) * xiStar}

lemma isOpen_lowerBoasRightDom : IsOpen lowerBoasRightDom :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

lemma convex_lowerBoasRightDom : Convex ℝ lowerBoasRightDom := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · change xiStar < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.ofReal_re, mul_re, ofReal_im, zero_mul,
      sub_zero]
    have hxi : a * xiStar + b * xiStar = xiStar := by linear_combination xiStar * hab
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; linarith [hy.1]
    · linarith [mul_lt_mul_of_pos_left hx.1 ha', mul_le_mul_of_nonneg_left hy.1.le hb, hxi]
  · change |(a • x + b • y).im| < 1 / 2
    simp only [Complex.add_im, Complex.real_smul, Complex.ofReal_re, mul_im, ofReal_im, zero_mul,
      add_zero]
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < (a + b) * (1 / 2) := by
          rcases eq_or_lt_of_le ha with rfl | ha'
          · have hb1 : b = 1 := by linarith
            subst hb1; linarith [hy.2]
          · nlinarith [hx.2, hy.2, abs_nonneg x.im, abs_nonneg y.im]
      _ = 1 / 2 := by rw [hab, one_mul]

lemma mem_slitStrip_of_im_ne_zero {b : ℂ} (hb : |b.im| < 1 / 2) (him : b.im ≠ 0) :
    b ∈ slitStrip :=
  ⟨hb, fun ⟨h0, _⟩ => him h0⟩

lemma conj_mem_lowerBoasRightDom {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    starRingEnd ℂ b ∈ lowerBoasRightDom :=
  ⟨by simpa using hb.1, by simpa using hb.2⟩

lemma isOpen_zetaStrip (c' : ℝ) : IsOpen (zetaStrip c') :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

lemma conj_mem_zetaStrip {c' : ℝ} {ζ : ℂ} (hζ : ζ ∈ zetaStrip c') :
    starRingEnd ℂ ζ ∈ zetaStrip c' :=
  ⟨by simpa using hζ.1, by simpa using hζ.2⟩

lemma majorantHolomorphic_conj {b : ℂ} (hb : b ∈ slitStrip) :
    majorantHolomorphic (starRingEnd ℂ b) = -starRingEnd ℂ (majorantHolomorphic b) := by
  have hconj_mem : starRingEnd ℂ b ∈ slitStrip := by
    refine ⟨by simpa using hb.1, ?_⟩
    rintro ⟨him, hre⟩
    simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
    exact hb.2 ⟨him, hre⟩
  have hint_cont : ContinuousOn (fun t : ℝ => pMap ((t : ℂ) * b) * b) (Icc 0 1) :=
    (differentiableOn_pMap_slitStrip.continuousOn.comp
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
      (fun t (ht : t ∈ Icc (0 : ℝ) 1) => smul_mem_slitStrip hb ht.1 ht.2)).mul continuousOn_const
  have hint_eq : ∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * starRingEnd ℂ b) * starRingEnd ℂ b =
      -starRingEnd ℂ (∫ t in (0 : ℝ)..1, pMap ((t : ℂ) * b) * b) := by
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
        pMap ((t : ℂ) * starRingEnd ℂ b) * starRingEnd ℂ b =
          -starRingEnd ℂ (pMap ((t : ℂ) * b) * b) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have htb : (t : ℂ) * b ∈ slitStrip := smul_mem_slitStrip hb ht.1 ht.2
      rw [show (t : ℂ) * starRingEnd ℂ b = starRingEnd ℂ ((t : ℂ) * b) by
        rw [map_mul, Complex.conj_ofReal], pMap_conj _ htb, map_mul]
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg]
    exact congrArg Neg.neg (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      (hint_cont.intervalIntegrable_of_Icc zero_le_one))
  unfold majorantHolomorphic
  rw [hint_eq, map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

lemma zetaPlus_conj {c' : ℝ} {b : ℂ} (hb : b ∈ slitStrip) :
    zetaPlus c' (starRingEnd ℂ b) = -starRingEnd ℂ (zetaPlus c' b) := by
  unfold zetaPlus
  rw [majorantHolomorphic_conj hb, map_mul, Complex.conj_ofReal, map_add, map_mul, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  ring

lemma zetaRight_conj {c' : ℝ} {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    zetaRight c' (starRingEnd ℂ b) = starRingEnd ℂ (zetaRight c' b) := by
  unfold zetaRight
  rcases lt_trichotomy b.im 0 with hneg | h0 | hpos
  · have hbs := mem_slitStrip_of_im_ne_zero hb.2 hneg.ne
    have h1 : 0 < (starRingEnd ℂ b).im := by simpa using hneg
    rw [ite_eq_left h1, ite_eq_right (not_lt.mpr hneg.le), ite_eq_left hneg, zetaPlus_conj hbs,
      map_neg]
  · simp only [Complex.conj_im, h0, neg_zero, lt_irrefl, ↓reduceIte, Complex.conj_ofReal,
      Complex.conj_re]
  · have hbs := mem_slitStrip_of_im_ne_zero hb.2 hpos.ne'
    have h1 : ¬0 < (starRingEnd ℂ b).im := by simpa using hpos.le
    have h2 : (starRingEnd ℂ b).im < 0 := by simpa using hpos
    rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left hpos, zetaPlus_conj hbs]
    ring

lemma hasDerivAt_zetaPlus {c' : ℝ} {b : ℂ} (hb : b ∈ slitStrip) :
    HasDerivAt (zetaPlus c') (((2 * c' / 3 : ℝ) : ℂ) * (pMap b + Complex.I / 2)) b := by
  have hm := hasDerivAt_majorantHolomorphic hb
  have hl : HasDerivAt (fun z : ℂ => Complex.I * ((2 * π / 3 : ℝ) : ℂ) * z)
      (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) b := by
    simpa using (hasDerivAt_id b).const_mul (Complex.I * ((2 * π / 3 : ℝ) : ℂ))
  have hs := (hm.add hl).const_mul ((c' / (2 * π) : ℝ) : ℂ)
  refine hs.congr_deriv ?_
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  push_cast
  field_simp [hpi]
  ring

/-! ### 2. Sign and Quantitative Real Part of `pMap` in `{0 < Re b, 0 < Im b < 1/2}` -/

lemma pMap_pos_re_neg_im {b : ℂ} (hb : b ∈ slitStrip) (hre : 0 < b.re) (him : 0 < b.im) :
    0 < (pMap b).re ∧ (pMap b).im < 0 ∧ -(1 / 2 : ℝ) < (pMap b).im := by
  have hpi := Real.pi_pos
  have hbim_lt : b.im < 1 / 2 := (abs_lt.mp hb.1).2
  set w : ℂ := -Complex.I * Complex.sinh ((π : ℂ) * b)
  have hw_dom : w ∈ arsinhDomain := mem_arsinhDomain_of_slitStrip hb
  obtain ⟨hre_f, him_f⟩ := neg_I_mul_sinh_pi_re_im b
  have hw_re : 0 < w.re := by
    change 0 < (-Complex.I * Complex.sinh ((π : ℂ) * b)).re at *
    rw [hre_f]
    exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi him) (by nlinarith))
  have hw_im : w.im < 0 := by
    change (-Complex.I * Complex.sinh ((π : ℂ) * b)).im < 0 at *
    rw [him_f]
    have hs_pos : 0 < Real.sinh (π * b.re) := Real.sinh_pos_iff.mpr (mul_pos hpi hre)
    have hc_pos : 0 < Real.cos (π * b.im) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
    nlinarith
  set s : ℂ := (w ^ 2 + 1) ^ (1 / 2 : ℂ)
  have hs_re : 0 < s.re := cpow_half_re_pos hw_dom
  have hs_sq : s ^ 2 = w ^ 2 + 1 := by
    have hz0 : w ^ 2 + 1 ≠ 0 := slitPlane_ne_zero hw_dom
    dsimp [s]
    rw [Complex.cpow_def_of_ne_zero hz0, sq, ← Complex.exp_add]
    have h : Complex.log (w ^ 2 + 1) * (1 / 2 : ℂ) + Complex.log (w ^ 2 + 1) * (1 / 2 : ℂ) =
        Complex.log (w ^ 2 + 1) := by ring
    rw [h, Complex.exp_log hz0]
  have hs_im : s.im < 0 := by
    have him_sq : (s ^ 2).im = (w ^ 2 + 1).im := congrArg Complex.im hs_sq
    have hs2 : (s ^ 2).im = 2 * s.re * s.im := by simp [sq]; ring
    have hw2 : (w ^ 2 + 1).im = 2 * w.re * w.im := by simp [sq]; ring
    nlinarith
  have hsum_re : 0 < (w + s).re := by simp [Complex.add_re]; linarith
  have hsum_im : (w + s).im < 0 := by simp [Complex.add_im]; linarith
  have hsum_ne0 : w + s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hsum_re; exact lt_irrefl _ hsum_re
  have hprod : (w + s) * (s - w) = 1 := by linear_combination hs_sq
  have hnorm_prod : ‖w + s‖ * ‖s - w‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have hnorm_gt : 1 < ‖w + s‖ := by
    have hdiff_sq : ‖w + s‖ ^ 2 - ‖s - w‖ ^ 2 = 4 * (w.re * s.re + w.im * s.im) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im]
      ring
    have hpos4 : 0 < 4 * (w.re * s.re + w.im * s.im) := by nlinarith
    have hlt_norm : ‖s - w‖ < ‖w + s‖ := by nlinarith [norm_nonneg (w + s), norm_nonneg (s - w)]
    nlinarith [norm_nonneg (w + s), norm_nonneg (s - w)]
  have hp_re : 0 < (pMap b).re := by
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.re_ofReal_mul, Complex.log_re]
    exact mul_pos (inv_pos.mpr hpi) (Real.log_pos hnorm_gt)
  have hsin_lt0 : Real.sin (Complex.arg (w + s)) < 0 := by
    rw [Complex.sin_arg]
    exact div_neg_of_neg_of_pos hsum_im (norm_pos_iff.mpr hsum_ne0)
  have hcos_pos : 0 < Real.cos (Complex.arg (w + s)) := by
    rw [Complex.cos_arg hsum_ne0]
    exact div_pos hsum_re (norm_pos_iff.mpr hsum_ne0)
  have harg_neg : Complex.arg (w + s) < 0 := by
    by_contra h0
    push Not at h0
    exact (Real.sin_nonneg_of_nonneg_of_le_pi h0 (Complex.arg_le_pi _)).not_gt hsin_lt0
  have harg_gt : -(π / 2) < Complex.arg (w + s) := by
    by_contra hle
    push Not at hle
    have hpi_lt := Complex.neg_pi_lt_arg (w + s)
    have hcos_le : Real.cos (Complex.arg (w + s)) ≤ 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    linarith
  have hp_im : (pMap b).im = Complex.arg (w + s) / π := by
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.im_ofReal_mul, Complex.log_im]
    ring
  refine ⟨hp_re, ?_, ?_⟩ <;> rw [hp_im]
  · exact div_neg_of_neg_of_pos harg_neg hpi
  · rw [lt_div_iff₀ hpi]; linarith

/-! ### 3. Boundary Limits and Schwarz Reflection of `zetaRight` -/

private lemma tendsto_pMap_slit_right_re {t : ℝ} (ht : xiStar < t) :
    Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 ((3 / 4 : ℝ) * rhoU t)) := by
  have hpi := Real.pi_pos
  have hlim_z : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
    have h0 : (t : ℂ) = (t : ℂ) + (0 : ℂ) * Complex.I := by simp
    conv_rhs => rw [h0]
    exact tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        tendsto_const_nhds)
  let w : ℂ → ℂ := fun z => -Complex.I * Complex.sinh ((π : ℂ) * z)
  have hw_cont : Continuous w :=
    continuous_const.mul (Complex.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hw_val : w (t : ℂ) = -Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ) := by
    dsimp [w]; rw [show (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]
  have hw_tend : Tendsto (fun y : ℝ => w ((t : ℂ) + (y : ℂ) * Complex.I)) (𝓝[>] 0)
      (𝓝 (-Complex.I * ((Real.sinh (π * t) : ℝ) : ℂ))) := by
    rw [← hw_val]; exact hw_cont.continuousAt.tendsto.comp hlim_z
  have hsinh_gt : 1 < Real.sinh (π * t) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_left ht hpi)
  have hsq_pos : 0 < Real.sinh (π * t) ^ 2 - 1 := by nlinarith
  have hnz_tend : Tendsto (fun y : ℝ => -((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))
      (𝓝[>] 0) (𝓝 ((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)) := by
    have h1 := ((hw_tend.pow 2).add (tendsto_const_nhds (x := (1 : ℂ)))).neg
    convert h1 using 2; rw [mul_pow, neg_sq, Complex.I_sq]; push_cast; ring
  have harg_nz : Tendsto (fun y : ℝ =>
      Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1))) (𝓝[>] 0) (𝓝 0) := by
    have hcmp := (Complex.continuousAt_arg (Complex.ofReal_mem_slitPlane.mpr hsq_pos)).tendsto.comp hnz_tend
    rwa [Complex.arg_ofReal_of_nonneg hsq_pos.le] at hcmp
  have hnorm_tend : Tendsto (fun y : ℝ =>
      ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
      (𝓝 (Real.sinh (π * t) ^ 2 - 1)) := by
    have h1 := (continuous_norm.tendsto _).comp hnz_tend
    have hnl : ‖((Real.sinh (π * t) ^ 2 - 1 : ℝ) : ℂ)‖ = Real.sinh (π * t) ^ 2 - 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hsq_pos.le]
    rw [hnl] at h1; convert h1 using 1; ext y; exact (norm_neg _).symm
  have him_neg_ev : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im < 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    have hri := neg_I_mul_sinh_pi_re_im ((t : ℂ) + (y : ℂ) * Complex.I)
    have hre0 : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by simp
    have him0 : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rw [hre0, him0] at hri
    have hw_re_pos : 0 < (w ((t : ℂ) + (y : ℂ) * Complex.I)).re := by
      dsimp [w]; rw [hri.1]
      exact mul_pos (Real.cosh_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hy.1) (by nlinarith [hy.2]))
    have hw_im_neg : (w ((t : ℂ) + (y : ℂ) * Complex.I)).im < 0 := by
      dsimp [w]; rw [hri.2]
      have hcos_pos : 0 < Real.cos (π * y) := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
      nlinarith
    have him_sq : ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1).im =
        2 * (w ((t : ℂ) + (y : ℂ) * Complex.I)).re * (w ((t : ℂ) + (y : ℂ) * Complex.I)).im := by
      simp [pow_two]; ring
    rw [him_sq]; nlinarith
  have hs_tend : Tendsto (fun y : ℝ =>
      ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (-Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ))) := by
    have hsqrt_tend : Tendsto (fun y : ℝ =>
        Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖) (𝓝[>] 0)
        (𝓝 (Real.sqrt (Real.sinh (π * t) ^ 2 - 1))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnorm_tend
    have hsin_tend : Tendsto (fun y : ℝ =>
        Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 := Real.continuous_sin.continuousAt.tendsto.comp (harg_nz.div_const 2)
      change Tendsto (fun y : ℝ => Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 (Real.sin (0 / 2))) at h1
      simpa [Real.sin_zero] using h1
    have hcos_tend : Tendsto (fun y : ℝ =>
        Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 1) := by
      have h1 := Real.continuous_cos.continuousAt.tendsto.comp (harg_nz.div_const 2)
      change Tendsto (fun y : ℝ => Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2))
        (𝓝[>] 0) (𝓝 (Real.cos (0 / 2))) at h1
      simpa [Real.cos_zero] using h1
    have hcomb : Tendsto (fun y : ℝ =>
        ((Real.sqrt ‖(w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1‖ : ℝ) : ℂ) *
          (((Real.sin (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ) -
            Complex.I * ((Real.cos (Complex.arg (-((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1)) / 2) : ℝ) : ℂ)))
        (𝓝[>] 0)
        (𝓝 (((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
          (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)))) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hsqrt_tend).mul
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp hsin_tend).sub
          ((tendsto_const_nhds (x := Complex.I)).mul
            (Complex.continuous_ofReal.continuousAt.tendsto.comp hcos_tend)))
    rw [show ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) *
        (((0 : ℝ) : ℂ) - Complex.I * ((1 : ℝ) : ℂ)) =
        -Complex.I * ((Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ) by push_cast; ring] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [him_neg_ev] with y hy
    set z := (w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1
    have hz0 : z ≠ 0 := by intro h0; rw [h0, Complex.zero_im] at hy; exact lt_irrefl _ hy
    rw [Complex.cpow_def_of_ne_zero hz0,
      show Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I from
        Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im]),
      show Complex.arg z = Complex.arg (-z) - π by linarith [Complex.arg_neg_eq_arg_add_pi_of_im_neg hy],
      show (Real.log ‖z‖ + (Complex.arg (-z) - π : ℝ) * Complex.I : ℂ) * (1 / 2 : ℂ) =
        ((Real.log ‖z‖ / 2 : ℝ) : ℂ) + (((Complex.arg (-z) / 2 - π / 2 : ℝ) : ℂ) * Complex.I) by
          push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two,
      show Real.exp (Real.log ‖z‖ / 2) = Real.sqrt ‖z‖ by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hz0)]; congr 1; ring]
    push_cast; ring
  have hsum_tend : Tendsto (fun y : ℝ =>
      w ((t : ℂ) + (y : ℂ) * Complex.I) + ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (-Complex.I * ((Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ))) := by
    convert hw_tend.add hs_tend using 2; push_cast; ring
  have hsum_norm : Tendsto (fun y : ℝ =>
      ‖w ((t : ℂ) + (y : ℂ) * Complex.I) + ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)‖)
      (𝓝[>] 0) (𝓝 (Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1))) := by
    have h1 := (continuous_norm.tendsto _).comp hsum_tend
    have hpos : 0 < Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) := by positivity
    rw [show ‖-Complex.I * ((Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) : ℝ) : ℂ)‖ =
        Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]] at h1
    exact h1
  have hpos_sum : Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) ≠ 0 := by positivity
  have hdiv := ((Real.continuousAt_log hpos_sum).tendsto.comp hsum_norm).div_const π
  have h_eq : ∀ y : ℝ, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re =
      Real.log ‖w ((t : ℂ) + (y : ℂ) * Complex.I) +
        ((w ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 + 1) ^ (1 / 2 : ℂ)‖ / π := fun y => by
    unfold pMap complexArsinh
    have hpi_inv : ((π : ℂ)⁻¹) = ((π⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi_inv, Complex.re_ofReal_mul, Complex.log_re]; ring
  simp_rw [h_eq]
  have hlim_rho : Real.log (Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1)) / π =
      (3 / 4 : ℝ) * rhoU t := by
    rw [rhoU_eq_of_ge ht.le]
    unfold arccoshR
    have hsq : Real.sinh (π * t) ^ 2 - 1 = Real.sqrt (Real.sinh (π * t) ^ 2 - 1) ^ 2 :=
      (Real.sq_sqrt hsq_pos.le).symm
    have harg_eq : Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) =
        Real.sinh (π * t) + Real.sqrt ((Real.sinh (π * t) - 1) * (Real.sinh (π * t) + 1)) := by
      congr 2; ring
    rw [harg_eq]
    field_simp [hpi.ne']
  rwa [hlim_rho] at hdiv

private lemma majorantHolomorphic_imag_re_zero {y : ℝ} (hy : |y| < 1 / 2) :
    (majorantHolomorphic ((y : ℂ) * Complex.I)).re = 0 := by
  have hy_mem : (y : ℂ) * Complex.I ∈ slitStrip :=
    ⟨by simpa using hy, fun ⟨_, hre⟩ => by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, abs_zero] at hre
      linarith [xiStar_pos]⟩
  have heq := majorantHolomorphic_conj hy_mem
  have hneg : starRingEnd ℂ ((y : ℂ) * Complex.I) = -((y : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hm_neg : majorantHolomorphic (-((y : ℂ) * Complex.I)) = majorantHolomorphic ((y : ℂ) * Complex.I) := by
    unfold majorantHolomorphic
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
        pMap ((t : ℂ) * (-((y : ℂ) * Complex.I))) * (-((y : ℂ) * Complex.I)) =
          pMap ((t : ℂ) * ((y : ℂ) * Complex.I)) * ((y : ℂ) * Complex.I) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have htb := smul_mem_slitStrip hy_mem ht.1 ht.2
      rw [show (t : ℂ) * (-((y : ℂ) * Complex.I)) = -((t : ℂ) * ((y : ℂ) * Complex.I)) by ring,
        pMap_neg htb]
      ring
    rw [intervalIntegral.integral_congr hcongr]
  rw [hneg, hm_neg] at heq
  have hre := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

private lemma zetaPlus_re_eq_integral {c' x y : ℝ} (hy : 0 < y) (hy2 : y < 1 / 2) :
    (zetaPlus c' ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      -(c' / 3) * y + (2 * c' / 3) * ∫ t in (0 : ℝ)..x, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hmem : ∀ t : ℝ, (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip := fun t =>
    ⟨by simpa [abs_of_pos hy] using hy2, fun ⟨him, _⟩ => by simp at him; exact hy.ne' him⟩
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => (zetaPlus c' ((s : ℂ) + (y : ℂ) * Complex.I)).re)
        ((2 * c' / 3) * (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re) t := by
    intro t _
    have hc : HasDerivAt (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((y : ℂ) * Complex.I)
    have hz : HasDerivAt (zetaPlus c') (((2 * c' / 3 : ℝ) : ℂ) * (pMap ((t : ℂ) + (y : ℂ) * Complex.I) + Complex.I / 2))
        ((t : ℂ) + (y : ℂ) * Complex.I) := hasDerivAt_zetaPlus (hmem t)
    have hcomp := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hc
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
    refine hre.congr_deriv ?_
    simp [Complex.reCLM_apply]
  have hint : IntervalIntegrable (fun t : ℝ => (2 * c' / 3) * (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
      volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
      (Complex.continuous_ofReal.add continuous_const) hmem
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : (zetaPlus c' ((0 : ℂ) + (y : ℂ) * Complex.I)).re = -(c' / 3) * y := by
    unfold zetaPlus
    rw [zero_add]
    have hmr := majorantHolomorphic_imag_re_zero (by rw [abs_of_pos hy]; exact hy2)
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, hmr,
      Complex.I_re, Complex.I_im, zero_mul, sub_zero, mul_zero, zero_add, Complex.mul_im, one_mul,
      zero_sub]
    field_simp [hpi]
    ring
  simp only [Complex.ofReal_zero] at hftc
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith [hftc, h0]

private lemma hasDerivAt_zetaPlus_vert_re {c' x s : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    HasDerivAt (fun t : ℝ => (zetaPlus c' ((x : ℂ) + (t : ℂ) * Complex.I)).re)
      (-(2 * c' / 3) * ((pMap ((x : ℂ) + (s : ℂ) * Complex.I)).im + 1 / 2)) s := by
  have hmem : (x : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
    ⟨by simpa [abs_of_pos hs0] using hs1, fun ⟨him, _⟩ => by simp at him; exact hs0.ne' him⟩
  have hc : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I).const_add (x : ℂ)
  have hz := hasDerivAt_zetaPlus (c' := c') hmem
  have hcomp := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hc
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hcomp
  refine hre.congr_deriv ?_
  simp [Complex.reCLM_apply]

private lemma tendsto_zetaPlus_xiStar_re {c' : ℝ} :
    Tendsto (fun y : ℝ => (zetaPlus c' ((xiStar : ℂ) + (y : ℂ) * Complex.I)).re) (𝓝[>] 0) (𝓝 0) := by
  have h0_eq : ∀ y ∈ Ioo (0 : ℝ) (1 / 2),
      (zetaPlus c' ((xiStar : ℂ) + (y : ℂ) * Complex.I)).re =
        -(c' / 3) * y + (2 * c' / 3) * ∫ t in (0 : ℝ)..xiStar, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re :=
    fun y hy => zetaPlus_re_eq_integral hy.1 hy.2
  have hint_tend : Tendsto (fun y : ℝ =>
      ∫ t in (0 : ℝ)..xiStar, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re) (𝓝[>] 0) (𝓝 0) := by
    conv_rhs => rw [← show ∫ _ in (0 : ℝ)..xiStar, (0 : ℝ) = 0 by simp]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (F := fun y t => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
      (f := fun _ => (0 : ℝ)) (a := 0) (b := xiStar) (l := (𝓝[>] (0 : ℝ)))
      (bound := fun _ => xiStar + 1) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      refine Continuous.aestronglyMeasurable ?_
      exact Complex.continuous_re.comp (differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
        (Complex.continuous_ofReal.add continuous_const) fun t =>
          ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by simp at him; exact hy.1.ne' him⟩)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      filter_upwards with t ht
      rw [uIoc_of_le xiStar_pos.le] at ht
      have hmem : (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by simp at him; exact hy.1.ne' him⟩
      have hbd := pMap_re_abs_le hmem
      have hre0 : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by simp
      rw [hre0, abs_of_pos ht.1] at hbd
      rw [Real.norm_eq_abs]
      linarith [ht.2]
    · have hne : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) xiStar → t < xiStar := by
        filter_upwards [compl_mem_ae_iff.mpr Real.volume_singleton] with t ht htu
        rw [uIoc_of_le xiStar_pos.le] at htu
        exact lt_of_le_of_ne htu.2 ht
      filter_upwards [hne] with t ht htu
      have hlt := ht htu
      rw [uIoc_of_le xiStar_pos.le] at htu
      have hmem : (t : ℂ) ∈ slitStrip := ⟨by simp, fun ⟨_, hre⟩ => by
        have : |(t : ℂ).re| = t := by simpa using abs_of_pos htu.1
        linarith⟩
      have hcont := (Complex.continuous_re.continuousAt.comp
        (differentiableOn_pMap_slitStrip.continuousOn.continuousAt (isOpen_slitStrip.mem_nhds hmem)))
      have hz_lim : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
        have hc : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
        have ht1 : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0)
            (𝓝 ((t : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
          hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        simpa using ht1
      have hp0 : (pMap (t : ℂ)).re = 0 := by
        rw [pMap_ofReal (by rw [abs_of_pos htu.1]; exact hlt.le)]; simp
      have hres := hcont.tendsto.comp hz_lim
      change Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re) (𝓝[>] 0)
        (𝓝 (pMap (t : ℂ)).re) at hres
      rwa [hp0] at hres
  have hlim : Tendsto (fun y : ℝ => -(c' / 3) * y + (2 * c' / 3) *
      ∫ t in (0 : ℝ)..xiStar, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := -(c' / 3))).mul
      (continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
        ((tendsto_const_nhds (x := 2 * c' / 3)).mul hint_tend)
    simpa using h1
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
  exact (h0_eq y hy).symm

lemma zetaPlus_xiStar_re_neg {c' y : ℝ} (hc' : 0 < c') (hy : 0 < y) (hy2 : y < 1 / 2) :
    (zetaPlus c' ((xiStar : ℂ) + (y : ℂ) * Complex.I)).re < 0 := by
  set f : ℝ → ℝ := fun s => (zetaPlus c' ((xiStar : ℂ) + (s : ℂ) * Complex.I)).re
  have hanti : StrictAntiOn f (Ioo 0 (1 / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo 0 (1 / 2)) ?_ ?_
    · intro s hs
      have hm : (xiStar : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos hs.1] using hs.2, fun ⟨him, _⟩ => by simp at him; exact hs.1.ne' him⟩
      have hd := (hasDerivAt_zetaPlus (c' := c') hm).continuousAt
      have hc : Continuous (fun t : ℝ => (xiStar : ℂ) + (t : ℂ) * Complex.I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      exact (Complex.continuous_re.continuousAt.comp (hd.comp_of_eq hc.continuousAt rfl)).continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      have hmem : (xiStar : ℂ) + (s : ℂ) * Complex.I ∈ slitStrip :=
        ⟨by simpa [abs_of_pos hs.1] using hs.2, fun ⟨him, _⟩ => by simp at him; exact hs.1.ne' him⟩
      have hp := pMap_pos_re_neg_im hmem (by simpa using xiStar_pos) (by simpa using hs.1)
      have hd := hasDerivAt_zetaPlus_vert_re (c' := c') (x := xiStar) hs.1 hs.2
      rw [hd.deriv]
      nlinarith [hp.2.2]
  have hf_half : f (y / 2) < 0 → f y < 0 := fun h =>
    (hanti ⟨half_pos hy, by linarith⟩ ⟨hy, hy2⟩ (by linarith)).trans h
  have hf_le0 : f (y / 2) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hev : ∀ᶠ s in 𝓝[>] 0, f (y / 2) ≤ f s := by
      filter_upwards [Ioo_mem_nhdsGT (half_pos hy)] with s hs
      exact (hanti ⟨hs.1, by linarith [hs.2]⟩ ⟨half_pos hy, by linarith⟩ hs.2).le
    have hlim : f (y / 2) ≤ 0 := ge_of_tendsto (f := f) tendsto_zetaPlus_xiStar_re hev
    linarith
  have hev2 : ∀ᶠ s in 𝓝[>] 0, f (y / 4) ≤ f s := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y / 4 by positivity)] with s hs
    exact (hanti ⟨hs.1, by linarith [hs.2]⟩ ⟨by positivity, by linarith⟩ hs.2).le
  have hf_le0' : f (y / 4) ≤ 0 := ge_of_tendsto (f := f) tendsto_zetaPlus_xiStar_re hev2
  exact hf_half ((hanti ⟨by positivity, by linarith⟩ ⟨half_pos hy, by linarith⟩ (by linarith)).trans_le hf_le0')

lemma tendsto_zetaPlus_slit_right {c' x₀ : ℝ} (hx₀ : xiStar < x₀) :
    Tendsto (zetaPlus c') (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝 ((c' * cumulN x₀ : ℝ) : ℂ)) := by
  have hx₀_pos : 0 < x₀ := xiStar_pos.trans hx₀
  have hre : Tendsto (fun b : ℂ => (zetaPlus c' b).re)
      (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝 (c' * cumulN x₀)) := by
    have hvert : Tendsto (fun y : ℝ => (zetaPlus c' ((x₀ : ℂ) + (y : ℂ) * Complex.I)).re)
        (𝓝[>] 0) (𝓝 (c' * cumulN x₀)) := by
      have hint_target : (3 / 2 : ℝ) * cumulN x₀ =
          ∫ t in (0 : ℝ)..x₀, (if t ≤ xiStar then (0 : ℝ) else (3 / 4 : ℝ) * rhoU t) := by
        have hxi_mem : xiStar ∈ uIcc (0 : ℝ) x₀ := Set.mem_uIcc.mpr (Or.inl ⟨xiStar_pos.le, hx₀.le⟩)
        let flim : ℝ → ℝ := fun t => if t ≤ xiStar then 0 else (3 / 4 : ℝ) * rhoU t
        have hint_flim : IntervalIntegrable flim volume 0 x₀ := by
          refine IntervalIntegrable.trans (b := xiStar) ?_ ?_
          · exact (intervalIntegrable_const (c := 0)).congr (fun t ht => by
              rw [uIoc_of_le xiStar_pos.le] at ht
              dsimp [flim]; rw [ite_eq_left ht.2])
          · have hcont_rho : ContinuousOn (fun t : ℝ => (3 / 4 : ℝ) * rhoU t) (Icc xiStar x₀) :=
              (continuousOn_const.mul (continuousOn_rhoU.mono Icc_subset_Ici_self))
            refine (hcont_rho.intervalIntegrable_of_Icc hx₀.le).congr (fun t ht => by
              rw [uIoc_of_le hx₀.le] at ht
              dsimp [flim]; rw [ite_eq_right (not_le.mpr ht.1)])
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hint_flim.mono_set (Set.uIcc_subset_uIcc_left hxi_mem))
          (hint_flim.mono_set (Set.uIcc_subset_uIcc_right hxi_mem))
        have h1 : ∫ t in (0 : ℝ)..xiStar, flim t = 0 := by
          have : ∫ t in (0 : ℝ)..xiStar, flim t = ∫ _ in (0 : ℝ)..xiStar, (0 : ℝ) :=
            intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
              rw [uIoc_of_le xiStar_pos.le] at ht; dsimp [flim]; rw [ite_eq_left ht.2])
          simpa using this
        have h2 : ∫ t in xiStar..x₀, flim t = (3 / 2 : ℝ) * cumulN x₀ := by
          have heq : ∫ t in xiStar..x₀, flim t = ∫ t in xiStar..x₀, (3 / 4 : ℝ) * rhoU t :=
            intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
              rw [uIoc_of_le hx₀.le] at ht; dsimp [flim]; rw [ite_eq_right (not_le.mpr ht.1)])
          rw [heq, intervalIntegral.integral_const_mul, cumulN]
          ring
        linarith
      have hint_tend : Tendsto (fun y : ℝ =>
          ∫ t in (0 : ℝ)..x₀, (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
          (𝓝[>] 0) (𝓝 ((3 / 2 : ℝ) * cumulN x₀)) := by
        rw [hint_target]
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (F := fun y t => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re)
          (f := fun t => if t ≤ xiStar then (0 : ℝ) else (3 / 4 : ℝ) * rhoU t)
          (a := 0) (b := x₀) (l := (𝓝[>] (0 : ℝ))) (bound := fun _ => x₀ + 1) ?_ ?_
          intervalIntegrable_const ?_
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
          exact (Complex.continuous_re.comp (differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
            (Complex.continuous_ofReal.add continuous_const) fun t =>
              ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by
                simp at him; exact hy.1.ne' him⟩)).aestronglyMeasurable
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
          filter_upwards with t ht
          rw [uIoc_of_le hx₀_pos.le] at ht
          have hmem : (t : ℂ) + (y : ℂ) * Complex.I ∈ slitStrip :=
            ⟨by simpa [abs_of_pos hy.1] using hy.2, fun ⟨him, _⟩ => by simp at him; exact hy.1.ne' him⟩
          have hbd := pMap_re_abs_le hmem
          have hre0 : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by simp
          rw [hre0, abs_of_pos ht.1] at hbd
          rw [Real.norm_eq_abs]
          linarith [ht.2]
        · have hne : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) x₀ → t ≠ xiStar := by
            filter_upwards [compl_mem_ae_iff.mpr Real.volume_singleton] with t ht _; exact ht
          filter_upwards [hne] with t ht htu
          have htne := ht htu
          rw [uIoc_of_le hx₀_pos.le] at htu
          rcases lt_or_gt_of_ne htne with hlt | hgt
          · rw [ite_eq_left hlt.le]
            have hmem : (t : ℂ) ∈ slitStrip := ⟨by simp, fun ⟨_, hre⟩ => by
              have : |(t : ℂ).re| = t := by simpa using abs_of_pos htu.1
              linarith⟩
            have hcont := Complex.continuous_re.continuousAt.comp
              (differentiableOn_pMap_slitStrip.continuousOn.continuousAt (isOpen_slitStrip.mem_nhds hmem))
            have hz_lim : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
              have hc : Continuous (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
              have ht1 : Tendsto (fun y : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0)
                  (𝓝 ((t : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
                hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
              simpa using ht1
            have hp0 : (pMap (t : ℂ)).re = 0 := by
              rw [pMap_ofReal (by rw [abs_of_pos htu.1]; exact hlt.le)]; simp
            have hres := hcont.tendsto.comp hz_lim
            change Tendsto (fun y : ℝ => (pMap ((t : ℂ) + (y : ℂ) * Complex.I)).re) (𝓝[>] 0)
              (𝓝 (pMap (t : ℂ)).re) at hres
            rwa [hp0] at hres
          · rw [ite_eq_right (not_le.mpr hgt)]
            exact tendsto_pMap_slit_right_re hgt
      have hid : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
        continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hlim := ((tendsto_const_nhds (x := -(c' / 3))).mul hid).add
        ((tendsto_const_nhds (x := 2 * c' / 3)).mul hint_tend)
      have hlim_eq : -(c' / 3) * 0 + (2 * c' / 3) * ((3 / 2 : ℝ) * cumulN x₀) = c' * cumulN x₀ := by ring
      rw [hlim_eq] at hlim
      refine hlim.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      exact (zetaPlus_re_eq_integral hy.1 hy.2).symm
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hvert (ε / 2) (half_pos hε)
    set L : ℝ := |2 * c' / 3| * (|x₀| + 2) + 1
    have hL_pos : 0 < L := by positivity
    refine ⟨min (min δ₁ (1 / 4)) (min 1 (ε / (2 * L))), by positivity, fun b hb hdist => ?_⟩
    rw [Complex.dist_eq] at hdist
    have hbre_lt : |b.re - x₀| < min 1 (ε / (2 * L)) := by
      have h1 := Complex.abs_re_le_norm (b - (x₀ : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      exact h1.trans_lt (hdist.trans_le (min_le_right _ _))
    have hbim_lt : |b.im| < min δ₁ (1 / 4) := by
      have h1 := Complex.abs_im_le_norm (b - (x₀ : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
      exact h1.trans_lt (hdist.trans_le (min_le_left _ _))
    have hbim_pos : 0 < b.im := hb
    have hbim_half : b.im < 1 / 2 := by linarith [(abs_lt.mp hbim_lt).2, min_le_right δ₁ (1 / 4)]
    have h1 : |(zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re - c' * cumulN x₀| < ε / 2 := by
      have hdist_im : dist b.im 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hbim_pos]
        exact (abs_of_pos hbim_pos ▸ hbim_lt).trans_le (min_le_left _ _)
      exact hδ₁ hbim_pos hdist_im
    have hcont_p : Continuous (fun t : ℝ => (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re) :=
      Complex.continuous_re.comp (differentiableOn_pMap_slitStrip.continuousOn.comp_continuous
        (Complex.continuous_ofReal.add continuous_const) fun t =>
          ⟨by simpa [abs_of_pos hbim_pos] using hbim_half, fun ⟨him, _⟩ => by
            simp at him; exact hbim_pos.ne' him⟩)
    have hdiff_re : (zetaPlus c' b).re - (zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re =
        (2 * c' / 3) * ∫ t in x₀..b.re, (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re := by
      have hb_eq : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b := by apply Complex.ext <;> simp
      have h1' := zetaPlus_re_eq_integral (c' := c') (x := b.re) hbim_pos hbim_half
      have h2' := zetaPlus_re_eq_integral (c' := c') (x := x₀) hbim_pos hbim_half
      rw [hb_eq] at h1'
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hcont_p.intervalIntegrable (μ := volume) 0 x₀)
        (hcont_p.intervalIntegrable (μ := volume) x₀ b.re)
      rw [h1', h2', ← hadd]
      ring
    have h2 : |(zetaPlus c' b).re - (zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re| < ε / 2 := by
      have hpt : ∀ t ∈ uIcc x₀ b.re, |(pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re| ≤ |x₀| + 2 := by
        intro t ht
        have hmem : (t : ℂ) + (b.im : ℂ) * Complex.I ∈ slitStrip :=
          ⟨by simpa [abs_of_pos hbim_pos] using hbim_half, fun ⟨him, _⟩ => by
            simp at him; exact hbim_pos.ne' him⟩
        have hbd := pMap_re_abs_le hmem
        have hre0 : ((t : ℂ) + (b.im : ℂ) * Complex.I).re = t := by simp
        rw [hre0] at hbd
        have htx : |t - x₀| ≤ |b.re - x₀| := by
          rcases le_total x₀ b.re with hxb | hbx
          · rw [uIcc_of_le hxb] at ht
            rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hxb)]
            linarith [ht.2]
          · rw [uIcc_comm, uIcc_of_le hbx] at ht
            rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hbx)]
            linarith [ht.1]
        have htx1 : |t - x₀| ≤ 1 := htx.trans (hbre_lt.le.trans (min_le_left _ _))
        linarith [abs_sub_abs_le_abs_sub t x₀]
      have hint_bd : |∫ t in x₀..b.re, (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re| ≤
          (|x₀| + 2) * |b.re - x₀| := by
        rcases le_total x₀ b.re with hxb | hbx
        · calc |∫ t in x₀..b.re, (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re|
              ≤ ∫ t in x₀..b.re, |(pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re| :=
                intervalIntegral.abs_integral_le_integral_abs hxb
            _ ≤ ∫ _ in x₀..b.re, (|x₀| + 2 : ℝ) :=
                intervalIntegral.integral_mono_on hxb
                  ((hcont_p.abs).intervalIntegrable x₀ b.re)
                  (intervalIntegrable_const : IntervalIntegrable _ volume x₀ b.re) fun t ht =>
                  hpt t (uIcc_of_le hxb ▸ ht)
            _ = (|x₀| + 2) * |b.re - x₀| := by
                rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_nonneg (sub_nonneg.mpr hxb)]
                ring
        · rw [intervalIntegral.integral_symm b.re x₀, abs_neg]
          calc |∫ t in b.re..x₀, (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re|
              ≤ ∫ t in b.re..x₀, |(pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re| :=
                intervalIntegral.abs_integral_le_integral_abs hbx
            _ ≤ ∫ _ in b.re..x₀, (|x₀| + 2 : ℝ) :=
                intervalIntegral.integral_mono_on hbx
                  ((hcont_p.abs).intervalIntegrable b.re x₀)
                  (intervalIntegrable_const : IntervalIntegrable _ volume b.re x₀) fun t ht =>
                  hpt t (by rw [uIcc_comm, uIcc_of_le hbx]; exact ht)
            _ = (|x₀| + 2) * |b.re - x₀| := by
                rw [intervalIntegral.integral_const, smul_eq_mul, abs_sub_comm,
                  abs_of_nonneg (sub_nonneg.mpr hbx)]
                ring
      rw [hdiff_re, abs_mul]
      have hL1 : |2 * c' / 3| * (|x₀| + 2) ≤ L := by dsimp [L]; linarith
      calc |2 * c' / 3| * |∫ t in x₀..b.re, (pMap ((t : ℂ) + (b.im : ℂ) * Complex.I)).re|
          ≤ |2 * c' / 3| * ((|x₀| + 2) * |b.re - x₀|) :=
            mul_le_mul_of_nonneg_left hint_bd (abs_nonneg _)
        _ = (|2 * c' / 3| * (|x₀| + 2)) * |b.re - x₀| := by ring
        _ ≤ L * |b.re - x₀| := mul_le_mul_of_nonneg_right hL1 (abs_nonneg _)
        _ < L * (ε / (2 * L)) :=
            mul_lt_mul_of_pos_left (hbre_lt.trans_le (min_le_right _ _)) hL_pos
        _ = ε / 2 := by field_simp [hL_pos.ne']
    rw [Real.dist_eq]
    calc |(zetaPlus c' b).re - c' * cumulN x₀|
        = |((zetaPlus c' b).re - (zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re) +
            ((zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re - c' * cumulN x₀)| := by ring_nf
      _ ≤ |(zetaPlus c' b).re - (zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re| +
            |(zetaPlus c' ((x₀ : ℂ) + (b.im : ℂ) * Complex.I)).re - c' * cumulN x₀| :=
          abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h1
      _ = ε := add_halves ε
  have him : Tendsto (fun b : ℂ => (zetaPlus c' b).im)
      (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝 0) := by
    have him_eq : ∀ b : ℂ, (zetaPlus c' b).im =
        (c' / (2 * π)) * (majorant2D b + (2 * π / 3) * b.re) := fun b => by
      unfold zetaPlus majorant2D
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.I_im,
        Complex.I_re, mul_zero, zero_mul, add_zero, zero_add, one_mul, Complex.mul_re, sub_zero]
    simp_rw [him_eq]
    have hmem_nhds : Tendsto id (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝[slitStrip] (x₀ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (x₀ : ℂ) (show (0 : ℝ) < 1 / 2 by norm_num))] with
        b hb hball
      have hbim_lt : b.im < 1 / 2 := by
        have h1 := Complex.abs_im_le_norm (b - (x₀ : ℂ))
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        rw [Metric.mem_ball, Complex.dist_eq] at hball
        linarith [(abs_lt.mp (h1.trans_lt hball)).2]
      refine ⟨?_, fun ⟨him, _⟩ => (hb : 0 < b.im).ne' him⟩
      change |b.im| < 1 / 2
      rw [abs_of_pos hb]; exact hbim_lt
    have hm_tend := (tendsto_majorant2D_slit_nonneg hx₀.le).comp hmem_nhds
    have hre_tend : Tendsto (fun b : ℂ => b.re) (𝓝[{b : ℂ | 0 < b.im}] (x₀ : ℂ)) (𝓝 x₀) :=
      Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hcomb := (tendsto_const_nhds (x := c' / (2 * π))).mul
      (hm_tend.add ((tendsto_const_nhds (x := 2 * π / 3)).mul hre_tend))
    have hlim0 : (c' / (2 * π)) * (-slitL x₀ + (2 * π / 3) * x₀) = 0 := by
      unfold slitL; rw [abs_of_pos hx₀_pos]; ring
    simpa [hlim0] using hcomb
  have hcomb := (Complex.continuous_ofReal.continuousAt.tendsto.comp hre).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul (tendsto_const_nhds (x := Complex.I)))
  rw [Complex.ofReal_zero, zero_mul, add_zero] at hcomb
  exact hcomb.congr' (Eventually.of_forall fun b => by apply Complex.ext <;> simp)

/-- Holomorphy of `zetaRight c'` on `lowerBoasRightDom` via Morera across the real axis. -/
theorem differentiableOn_zetaRight (c' : ℝ) :
    DifferentiableOn ℂ (zetaRight c') lowerBoasRightDom := by
  refine Complex.differentiableOn_of_continuousOn_off_horizLine (a := 0)
    isOpen_lowerBoasRightDom ?_ ?_
  · intro b hb
    rcases lt_trichotomy b.im 0 with hneg | h0 | hpos
    · have hev : zetaRight c' =ᶠ[𝓝 b] fun z => -zetaPlus c' z := by
        filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with z hz
        unfold zetaRight
        rw [ite_eq_right (not_lt.mpr hz.le), ite_eq_left hz]
      have hcont : ContinuousAt (fun z => -zetaPlus c' z) b :=
        (hasDerivAt_zetaPlus (mem_slitStrip_of_im_ne_zero hb.2 hneg.ne)).neg.continuousAt
      exact (hcont.congr hev.symm).continuousWithinAt
    · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl h0
      rw [hb_eq]
      have hx₀ : xiStar < b.re := hb.1
      have h_top : Tendsto (zetaRight c') (𝓝[{z : ℂ | 0 < z.im}] (b.re : ℂ))
          (𝓝 ((c' * cumulN b.re : ℝ) : ℂ)) := by
        refine (tendsto_zetaPlus_slit_right hx₀).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        unfold zetaRight; rw [ite_eq_left hz]
      have h_bot : Tendsto (zetaRight c') (𝓝[{z : ℂ | z.im < 0}] (b.re : ℂ))
          (𝓝 ((c' * cumulN b.re : ℝ) : ℂ)) := by
        have hconj_tend : Tendsto (starRingEnd ℂ) (𝓝[{z : ℂ | z.im < 0}] (b.re : ℂ))
            (𝓝[{z : ℂ | 0 < z.im}] (b.re : ℂ)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have hc : Tendsto (starRingEnd ℂ) (𝓝 (b.re : ℂ)) (𝓝 (b.re : ℂ)) := by
              simpa using (Complex.continuous_conj.continuousAt (x := (b.re : ℂ))).tendsto
            exact hc.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with z hz
            simpa using hz
        have hcomp := (Complex.continuous_conj.continuousAt (x := ((c' * cumulN b.re : ℝ) : ℂ))).tendsto.comp
          ((tendsto_zetaPlus_slit_right (c' := c') hx₀).comp hconj_tend)
        have hval : starRingEnd ℂ ((c' * cumulN b.re : ℝ) : ℂ) = ((c' * cumulN b.re : ℝ) : ℂ) := by
          simp
        rw [hval] at hcomp
        refine hcomp.congr' ?_
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_lowerBoasRightDom.mem_nhds (by simpa [← hb_eq] using hb))]
          with z hz hzb
        unfold zetaRight
        dsimp only [Function.comp_def]
        rw [ite_eq_right (not_lt.mpr hz.le), ite_eq_left hz,
          zetaPlus_conj (mem_slitStrip_of_im_ne_zero hzb.2 hz.ne)]
        simp
      have h_mid : Tendsto (zetaRight c') (𝓝[{z : ℂ | z.im = 0}] (b.re : ℂ))
          (𝓝 ((c' * cumulN b.re : ℝ) : ℂ)) := by
        have hcont : ContinuousWithinAt (fun z : ℂ => ((c' * cumulN z.re : ℝ) : ℂ))
            ({z : ℂ | z.im = 0} ∩ {z : ℂ | xiStar < z.re}) (b.re : ℂ) := by
          have hc1 : ContinuousWithinAt (fun x : ℝ => ((c' * cumulN x : ℝ) : ℂ)) (Ici xiStar)
              ((b.re : ℂ).re) :=
            Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
              (continuousOn_const.mul continuousOn_cumulN |>.continuousWithinAt (by simpa using hx₀.le))
          exact hc1.comp (f := fun z : ℂ => z.re) Complex.continuous_re.continuousAt.continuousWithinAt
            (fun z (hz : z ∈ ({z : ℂ | z.im = 0} ∩ {z : ℂ | xiStar < z.re})) => by
              change xiStar ≤ z.re; exact hz.2.le)
        have heq_nhds : 𝓝[{z : ℂ | z.im = 0} ∩ {z : ℂ | xiStar < z.re}] (b.re : ℂ) =
            𝓝[{z : ℂ | z.im = 0}] (b.re : ℂ) := by
          rw [inter_comm]
          exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
            ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hx₀)))
        rw [← heq_nhds]
        refine hcont.tendsto.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z (hz : z.im = 0 ∧ xiStar < z.re)
        unfold zetaRight
        rw [ite_eq_right (not_lt.mpr hz.1.le), ite_eq_right (not_lt.mpr hz.1.ge)]
      have h_top_bot : Tendsto (zetaRight c') (𝓝[{z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0}] (b.re : ℂ))
          (𝓝 ((c' * cumulN b.re : ℝ) : ℂ)) := by
        rw [nhdsWithin_union]; exact h_top.sup h_bot
      have h_all : ({z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0}) ∪ {z : ℂ | z.im = 0} = Set.univ := by
        ext z; simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
        rcases lt_trichotomy z.im 0 with h | h | h <;> simp [h]
      have h_cont_at : Tendsto (zetaRight c') (𝓝 (b.re : ℂ)) (𝓝 ((c' * cumulN b.re : ℝ) : ℂ)) := by
        rw [← nhdsWithin_univ, ← h_all, nhdsWithin_union]
        exact h_top_bot.sup h_mid
      have hval : zetaRight c' (b.re : ℂ) = ((c' * cumulN b.re : ℝ) : ℂ) := by
        unfold zetaRight; simp
      exact (hval ▸ h_cont_at).mono_left nhdsWithin_le_nhds
    · have hev : zetaRight c' =ᶠ[𝓝 b] zetaPlus c' := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with z hz
        unfold zetaRight; rw [ite_eq_left hz]
      have hcont : ContinuousAt (zetaPlus c') b :=
        (hasDerivAt_zetaPlus (mem_slitStrip_of_im_ne_zero hb.2 hpos.ne')).continuousAt
      exact (hcont.congr hev.symm).continuousWithinAt
  · intro b ⟨hb, hnot⟩
    change b.im ≠ 0 at hnot
    rcases lt_or_gt_of_ne hnot with hneg | hpos
    · have hev : zetaRight c' =ᶠ[𝓝 b] fun z => -zetaPlus c' z := by
        filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with z hz
        unfold zetaRight; rw [ite_eq_right (not_lt.mpr hz.le), ite_eq_left hz]
      exact ((hasDerivAt_zetaPlus (mem_slitStrip_of_im_ne_zero hb.2 hneg.ne)).neg.differentiableAt.congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hev : zetaRight c' =ᶠ[𝓝 b] zetaPlus c' := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with z hz
        unfold zetaRight; rw [ite_eq_left hz]
      exact ((hasDerivAt_zetaPlus (mem_slitStrip_of_im_ne_zero hb.2 hpos.ne')).differentiableAt.congr_of_eventuallyEq
        hev).differentiableWithinAt

lemma analyticOnNhd_zetaRight (c' : ℝ) : AnalyticOnNhd ℂ (zetaRight c') lowerBoasRightDom :=
  (differentiableOn_zetaRight c').analyticOnNhd isOpen_lowerBoasRightDom

lemma zetaRight_ofReal {c' x : ℝ} (_hx : xiStar < x) :
    zetaRight c' (x : ℂ) = ((c' * cumulN x : ℝ) : ℂ) := by
  unfold zetaRight; simp

lemma deriv_zetaRight_re_pos {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    0 < (deriv (zetaRight c') b).re := by
  rcases lt_trichotomy b.im 0 with hneg | h0 | hpos
  · have hbs := mem_slitStrip_of_im_ne_zero hb.2 hneg.ne
    have hev : zetaRight c' =ᶠ[𝓝 b] fun z => -zetaPlus c' z := by
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with z hz
      unfold zetaRight; rw [ite_eq_right (not_lt.mpr hz.le), ite_eq_left hz]
    have hd := ((hasDerivAt_zetaPlus (c' := c') hbs).neg).congr_of_eventuallyEq hev
    rw [hd.deriv]
    have hp := pMap_pos_re_neg_im (conj_mem_slitStrip_of_mem hbs) (by simpa using xiStar_pos.trans hb.1)
      (by simpa using hneg)
    have hpc : (pMap b).re = -(pMap (starRingEnd ℂ b)).re := by
      have h1 := congrArg Complex.re (pMap_conj b hbs)
      simp only [Complex.neg_re, Complex.conj_re] at h1
      linarith
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.div_ofNat_re, Complex.I_re, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
      zero_div, add_zero, zero_mul, sub_zero]
    nlinarith [hp.1]
  · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl h0
    have hbr_mem : (b.re : ℂ) ∈ lowerBoasRightDom := hb_eq ▸ hb
    rw [hb_eq]
    have hdC : HasDerivAt (zetaRight c') (deriv (zetaRight c') (b.re : ℂ)) (b.re : ℂ) :=
      ((differentiableOn_zetaRight c') _ hbr_mem).differentiableAt
        (isOpen_lowerBoasRightDom.mem_nhds hbr_mem) |>.hasDerivAt
    have hdR := hdC.comp_ofReal
    have hevR : (fun t : ℝ => zetaRight c' (t : ℂ)) =ᶠ[𝓝 b.re] fun t : ℝ => ((c' * cumulN t : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hb.1] with t ht
      exact zetaRight_ofReal ht
    have hd_real : HasDerivAt (fun t : ℝ => ((c' * cumulN t : ℝ) : ℂ))
        ((deriv (zetaRight c') (b.re : ℂ)) * (1 : ℂ)) b.re := by
      simpa using hdR.congr_of_eventuallyEq hevR.symm
    have hd_re : HasDerivAt (fun t : ℝ => c' * cumulN t) (deriv (zetaRight c') (b.re : ℂ)).re b.re := by
      have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt b.re hd_real
      exact h1.congr_deriv (by simp [Complex.reCLM_apply])
    have hd_cumul : HasDerivAt (fun t : ℝ => c' * cumulN t) (c' * (rhoU b.re / 2)) b.re :=
      (hasDerivAt_cumulN hb.1).const_mul c'
    have hval := hd_cumul.unique hd_re
    rw [← hval]
    exact mul_pos hc' (div_pos (rhoU_pos hb.1) two_pos)
  · have hbs := mem_slitStrip_of_im_ne_zero hb.2 hpos.ne'
    have hev : zetaRight c' =ᶠ[𝓝 b] zetaPlus c' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with z hz
      unfold zetaRight; rw [ite_eq_left hz]
    have hd := (hasDerivAt_zetaPlus (c' := c') hbs).congr_of_eventuallyEq hev
    rw [hd.deriv]
    have hp := pMap_pos_re_neg_im hbs (xiStar_pos.trans hb.1) hpos
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.div_ofNat_re, Complex.I_re, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
      zero_div, add_zero, zero_mul, sub_zero]
    nlinarith [hp.1]
where
  conj_mem_slitStrip_of_mem {z : ℂ} (hz : z ∈ slitStrip) : starRingEnd ℂ z ∈ slitStrip :=
    ⟨by simpa using hz.1, fun ⟨him, hre⟩ => by
      simp only [Complex.conj_im, neg_eq_zero, Complex.conj_re] at him hre
      exact hz.2 ⟨him, hre⟩⟩

lemma hasDerivAt_zetaRight {c' : ℝ} {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    HasDerivAt (zetaRight c') (deriv (zetaRight c') b) b :=
  ((differentiableOn_zetaRight c') b hb).differentiableAt (isOpen_lowerBoasRightDom.mem_nhds hb) |>.hasDerivAt

lemma deriv_zetaRight_ne_zero {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    deriv (zetaRight c') b ≠ 0 := by
  intro h0
  have hp := deriv_zetaRight_re_pos hc' hb
  rw [h0, Complex.zero_re] at hp
  exact lt_irrefl _ hp

/-- `Im ζ` has sign matching `Im b`, and `2π |Im ζ(b)| = c' (majorantUExt b + (2π/3) Re b)`. -/
lemma zetaRight_im_pos_of_im_pos {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom)
    (him : 0 < b.im) : 0 < (zetaRight c' b).im := by
  set g : ℝ → ℝ := fun y => (zetaRight c' ((b.re : ℂ) + (y : ℂ) * Complex.I)).im
  have hg_mono : StrictMonoOn g (Ico 0 (1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico 0 (1 / 2)) ?_ ?_
    · intro y hy
      have hmem : (b.re : ℂ) + (y : ℂ) * Complex.I ∈ lowerBoasRightDom :=
        ⟨by simpa using hb.1, by
          change |((b.re : ℂ) + (y : ℂ) * Complex.I).im| < 1 / 2
          simpa [one_div, abs_of_nonneg hy.1] using hy.2⟩
      have hc := (differentiableOn_zetaRight c').continuousOn.continuousAt
        (isOpen_lowerBoasRightDom.mem_nhds hmem)
      exact (Complex.continuous_im.continuousAt.comp
        (hc.comp_of_eq (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
          rfl)).continuousWithinAt
    · intro y hy
      rw [interior_Ico] at hy
      have hmem : (b.re : ℂ) + (y : ℂ) * Complex.I ∈ lowerBoasRightDom :=
        ⟨by simpa using hb.1, by
          change |((b.re : ℂ) + (y : ℂ) * Complex.I).im| < 1 / 2
          simpa [one_div, abs_of_pos hy.1] using hy.2⟩
      have hc : HasDerivAt (fun s : ℝ => (b.re : ℂ) + (s : ℂ) * Complex.I) Complex.I y := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (b.re : ℂ)
      have hz := ((hasDerivAt_zetaRight (c' := c') hmem).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt y hc
      have him_d : HasDerivAt g (deriv (zetaRight c') ((b.re : ℂ) + (y : ℂ) * Complex.I)).re y := by
        refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hz).congr_deriv ?_
        simp
      rw [him_d.deriv]
      exact deriv_zetaRight_re_pos hc' hmem
  have hg0 : g 0 = 0 := by
    dsimp [g]
    have heq : (b.re : ℂ) + (0 : ℂ) * Complex.I = (b.re : ℂ) := by simp
    rw [heq, zetaRight_ofReal hb.1]
    simp
  have hlt := hg_mono ⟨le_rfl, by norm_num⟩ ⟨him.le, (abs_lt.mp hb.2).2⟩ him
  rw [hg0] at hlt
  have hbe : (b.re : ℂ) + (b.im : ℂ) * Complex.I = b := by apply Complex.ext <;> simp
  simpa [g, hbe] using hlt

theorem zetaRight_im_abs_eq {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : b ∈ lowerBoasRightDom) :
    2 * π * |(zetaRight c' b).im| = c' * (majorantUExt b + (2 * π / 3) * b.re) := by
  have hpi := Real.pi_pos
  have huext : majorantUExt b = if |b.im| = 1 / 2 then 0
      else if b.im = 0 ∧ xiStar ≤ |b.re| then -slitL b.re else majorant2D b := rfl
  rcases lt_trichotomy b.im 0 with hneg | h0 | hpos
  · have hconj : starRingEnd ℂ b ∈ lowerBoasRightDom := conj_mem_lowerBoasRightDom hb
    have him_conj := zetaRight_im_pos_of_im_pos hc' hconj (by simpa using hneg)
    have him_neg : (zetaRight c' b).im < 0 := by
      have hc := congrArg Complex.im (zetaRight_conj hb (c' := c'))
      simp only [Complex.conj_im] at hc
      linarith
    have hval : (zetaRight c' b).im = -(c' / (2 * π)) * (majorant2D b + (2 * π / 3) * b.re) := by
      unfold zetaRight zetaPlus majorant2D
      rw [ite_eq_right (not_lt.mpr hneg.le), ite_eq_left hneg]
      simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_im, Complex.I_im, Complex.I_re, mul_zero, zero_mul, add_zero, zero_add,
        one_mul, Complex.mul_re, sub_zero]
      ring
    rw [abs_of_neg him_neg, hval, huext, ite_eq_right hb.2.ne, ite_eq_right (fun h => hneg.ne h.1)]
    field_simp [hpi.ne']
  · have hb_eq : b = (b.re : ℂ) := Complex.ext rfl h0
    have him0 : (zetaRight c' b).im = 0 := by
      rw [hb_eq, zetaRight_ofReal hb.1]; simp
    have hxpos : 0 < b.re := xiStar_pos.trans hb.1
    rw [him0, abs_zero, mul_zero, huext, ite_eq_right hb.2.ne,
      ite_eq_left ⟨h0, by rw [abs_of_pos hxpos]; exact hb.1.le⟩]
    unfold slitL; rw [abs_of_pos hxpos]; ring
  · have him_pos := zetaRight_im_pos_of_im_pos hc' hb hpos
    have hval : (zetaRight c' b).im = (c' / (2 * π)) * (majorant2D b + (2 * π / 3) * b.re) := by
      unfold zetaRight zetaPlus majorant2D
      rw [ite_eq_left hpos]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.I_im, Complex.I_re, mul_zero, zero_mul, add_zero, zero_add, one_mul,
        Complex.mul_re, sub_zero]
    rw [abs_of_pos him_pos, hval, huext, ite_eq_right hb.2.ne, ite_eq_right (fun h => hpos.ne' h.1)]
    field_simp [hpi.ne']

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_zetaRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.differentiableOn_zetaRight

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.deriv_zetaRight_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.deriv_zetaRight_re_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.zetaRight_im_abs_eq

end FormalResearch.ModularBootstrap.FiveTerm






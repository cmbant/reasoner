module

public import FormalResearch.SignUncertainty.CtOuterStrip
public import FormalResearch.Complex.StripPoisson

/-!
# The even strip Poisson kernel and the real part of `h` (`ct:outer` (1))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:outer` (1): the real part of
`1/sin(π(x + i s))` is the even strip Poisson kernel
`P_x(s) = sin(πx) cosh(πs) / (sinh²(πs) + sin²(πx)) = p(s) + p₁(s)`, which integrates to `1`.  **Proved.**

* `poissonK`, `poissonK_eq`, `poissonK_pos`, `integrable_poissonK`, `integral_poissonK` (uses the exact integrals
  `1 - σ` and `σ` of `Complex/StripPoisson.lean`), `poissonK_le` (decay `8 e^{-π|s|}` for `|s| ≥ 1`);
* `re_inv_sin_arg`: `Re 1/sin(π(ζ - i t)) = P_{Re ζ}(Im ζ - t)`;
* `re_outerH`: `Re h(ζ) = ∫ u_r(t) P_{Re ζ}(Im ζ - t) dt`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory FormalResearch.StripPoisson
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The even strip Poisson kernel `p + p₁`. -/
noncomputable def poissonK (x s : ℝ) : ℝ := stripPoissonP x s + stripPoissonP1 x s

lemma poissonK_eq {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (s : ℝ) :
    poissonK x s = Real.sin (π * x) * Real.cosh (π * s) /
      (Real.sinh (π * s) ^ 2 + Real.sin (π * x) ^ 2) := by
  unfold poissonK stripPoissonP stripPoissonP1
  have hd1 := stripPoissonP_den_pos h0 h1 s
  have hd2 := stripPoissonP1_den_pos h0 h1 s
  have hs : 0 < Real.sin (π * x) := stripPoisson_sin_pos h0 h1
  have hc := Real.cosh_sq (π * s)
  have hsc := Real.sin_sq_add_cos_sq (π * x)
  have hden : Real.sinh (π * s) ^ 2 + Real.sin (π * x) ^ 2 =
      (Real.cosh (π * s) - Real.cos (π * x)) * (Real.cosh (π * s) + Real.cos (π * x)) := by
    nlinarith
  rw [hden]
  field_simp
  ring

lemma poissonK_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (s : ℝ) : 0 < poissonK x s :=
  add_pos (stripPoissonP_pos h0 h1 s) (stripPoissonP1_pos h0 h1 s)

lemma poissonK_even (x s : ℝ) : poissonK x (-s) = poissonK x s := by
  unfold poissonK; rw [stripPoissonP_even, stripPoissonP1_even]

lemma integrable_poissonK {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : Integrable (poissonK x) :=
  (stripPoissonP_integrable h0 h1).add (stripPoissonP1_integrable h0 h1)

lemma integral_poissonK {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : ∫ s : ℝ, poissonK x s = 1 := by
  unfold poissonK
  rw [integral_add (stripPoissonP_integrable h0 h1) (stripPoissonP1_integrable h0 h1),
    stripPoissonP_integral h0 h1, stripPoissonP1_integral h0 h1]
  ring

lemma re_inv_sin_arg {ζ : ℂ} (hζ : ζ ∈ strip) (t : ℝ) :
    (1 / Complex.sin (π * (ζ - Complex.I * t))).re = poissonK ζ.re (ζ.im - t) := by
  have hre : (Complex.sin (π * (ζ - Complex.I * t))).re =
      Real.sin (π * ζ.re) * Real.cosh (π * (ζ.im - t)) := by
    conv_lhs => rw [sin_eq_re_im, re_arg, im_arg]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  rw [poissonK_eq hζ.1 hζ.2, one_div, Complex.inv_re, ← Complex.sq_norm, norm_sin_arg_sq, hre]
  ring

lemma poissonK_le {x : ℝ} (h0 : 0 < x) (h1 : x < 1) {s : ℝ} (hs : 1 ≤ |s|) :
    poissonK x s ≤ 8 * Real.exp (-(π * |s|)) := by
  rw [poissonK_eq h0 h1]
  set a : ℝ := π * |s| with ha
  have ha3 : 3 ≤ a := by nlinarith [Real.pi_gt_three]
  have hc : Real.cosh (π * s) = Real.cosh a := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [ha, h]
    · rw [ha, h, mul_neg, Real.cosh_neg]
  have hsh : Real.sinh (π * s) ^ 2 = Real.sinh a ^ 2 := by
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [ha, h]
    · rw [ha, h, mul_neg, Real.sinh_neg, neg_sq]
  rw [hc, hsh]
  set E : ℝ := Real.exp a with hE
  have hE4 : 4 ≤ E := by
    have := Real.add_one_le_exp a
    linarith
  have hEpos : 0 < E := by linarith
  have hE' : Real.exp (-a) = 1 / E := by rw [Real.exp_neg, hE]; simp
  have hcosh : Real.cosh a ≤ E := by
    rw [Real.cosh_eq, hE']
    have : 1 / E ≤ E := by
      rw [div_le_iff₀ hEpos]; nlinarith
    linarith
  have hsinh : 3 / 8 * E ≤ Real.sinh a := by
    rw [Real.sinh_eq, hE']
    have : E ^ 2 ≥ 4 := by nlinarith
    have h2 : 1 / E ≤ E / 4 := by
      rw [div_le_div_iff₀ hEpos (by norm_num)]; nlinarith
    linarith
  have hsin1 : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
  have hsinpos : 0 < Real.sin (π * x) := stripPoisson_sin_pos h0 h1
  have hcpos : 0 < Real.cosh a := Real.cosh_pos a
  have hsq : (3 / 8 * E) ^ 2 ≤ Real.sinh a ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsinh
  have hden : 0 < Real.sinh a ^ 2 + Real.sin (π * x) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have : Real.sin (π * x) * Real.cosh a ≤ E := by nlinarith
  have e : Real.exp (-a) = 1 / E := hE'
  rw [e]
  have h3 : 8 * (1 / E) * (Real.sinh a ^ 2 + Real.sin (π * x) ^ 2) ≥ E := by
    have : 8 * (1 / E) * (Real.sinh a ^ 2) ≥ 8 * (1 / E) * ((3 / 8 * E) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 8 * (1 / E) * ((3 / 8 * E) ^ 2) = 9 / 8 * E := by field_simp; ring
    have : 0 ≤ 8 * (1 / E) * Real.sin (π * x) ^ 2 := by positivity
    nlinarith
  linarith

lemma re_outerH {ζ : ℂ} (hζ : ζ ∈ strip) :
    (outerH ζ).re = ∫ t : ℝ, uR t * poissonK ζ.re (ζ.im - t) := by
  unfold outerH
  refine (integral_re (integrable_integrand hζ)).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [RCLike.re_to_complex]
  rw [div_eq_mul_inv, ← one_div, Complex.re_ofReal_mul, re_inv_sin_arg hζ]

lemma poissonK_tail_Ioi {x : ℝ} (h0 : 0 < x) (h1 : x < 1) {a : ℝ} (ha : 1 ≤ a) :
    ∫ s in Ioi a, poissonK x s ≤ 8 / π * Real.exp (-(π * a)) := by
  have hint : IntegrableOn (fun s : ℝ => 8 * Real.exp ((-π) * s)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (a := -π) (by linarith [Real.pi_pos]) a).const_mul 8
  have hP : IntegrableOn (poissonK x) (Ioi a) := (integrable_poissonK h0 h1).integrableOn
  calc ∫ s in Ioi a, poissonK x s ≤ ∫ s in Ioi a, 8 * Real.exp ((-π) * s) := by
        refine setIntegral_mono_on hP hint measurableSet_Ioi (fun s hs => ?_)
        have hs1 : 1 ≤ |s| := by rw [abs_of_pos (by linarith [mem_Ioi.mp hs])]; linarith [mem_Ioi.mp hs]
        have := poissonK_le h0 h1 hs1
        rw [abs_of_pos (by linarith [mem_Ioi.mp hs] : (0 : ℝ) < s)] at this
        calc poissonK x s ≤ 8 * Real.exp (-(π * s)) := this
          _ = 8 * Real.exp ((-π) * s) := by rw [neg_mul]
    _ = 8 / π * Real.exp (-(π * a)) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [Real.pi_pos]) a]
        have := Real.pi_pos
        field_simp

lemma poissonK_tail_Iic {x : ℝ} (h0 : 0 < x) (h1 : x < 1) {a : ℝ} (ha : 1 ≤ a) :
    ∫ s in Iic (-a), poissonK x s ≤ 8 / π * Real.exp (-(π * a)) := by
  have hint : IntegrableOn (fun s : ℝ => 8 * Real.exp (π * s)) (Iic (-a)) :=
    (integrableOn_exp_mul_Iic (a := π) Real.pi_pos (-a)).const_mul 8
  have hP : IntegrableOn (poissonK x) (Iic (-a)) := (integrable_poissonK h0 h1).integrableOn
  calc ∫ s in Iic (-a), poissonK x s ≤ ∫ s in Iic (-a), 8 * Real.exp (π * s) := by
        refine setIntegral_mono_on hP hint measurableSet_Iic (fun s hs => ?_)
        have hs' : s ≤ -a := mem_Iic.mp hs
        have hs1 : 1 ≤ |s| := by rw [abs_of_neg (by linarith)]; linarith
        have := poissonK_le h0 h1 hs1
        rw [abs_of_neg (by linarith : s < 0)] at this
        calc poissonK x s ≤ 8 * Real.exp (-(π * -s)) := this
          _ = 8 * Real.exp (π * s) := by rw [mul_neg, neg_neg]
    _ = 8 / π * Real.exp (-(π * a)) := by
        rw [integral_const_mul, integral_exp_mul_Iic Real.pi_pos (-a)]
        have := Real.pi_pos
        field_simp

lemma poissonK_mass_ge {x : ℝ} (h0 : 0 < x) (h1 : x < 1) {a : ℝ} (ha : 1 ≤ a) :
    1 - 16 / π * Real.exp (-(π * a)) ≤ ∫ s in Icc (-a) a, poissonK x s := by
  have hI := integrable_poissonK h0 h1
  have h2 := integral_add_compl (measurableSet_Icc (a := -a) (b := a)) hI
  rw [integral_poissonK h0 h1] at h2
  have hc : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext s
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h
      by_cases h' : -a ≤ s
      · exact Or.inr (not_le.mp (fun h2 => h ⟨h', h2⟩))
      · exact Or.inl (not_le.mp h')
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  rw [hc, setIntegral_union (Set.disjoint_left.mpr fun s h1 h2 => by
      simp only [mem_Iio, mem_Ioi] at h1 h2; linarith) measurableSet_Ioi hI.integrableOn hI.integrableOn] at h2
  have e1 : ∫ s in Iio (-a), poissonK x s = ∫ s in Iic (-a), poissonK x s :=
    setIntegral_congr_set Iio_ae_eq_Iic
  have t1 := poissonK_tail_Iic h0 h1 ha
  have t2 := poissonK_tail_Ioi h0 h1 ha
  rw [e1] at h2
  have : 16 / π * Real.exp (-(π * a)) = 8 / π * Real.exp (-(π * a)) + 8 / π * Real.exp (-(π * a)) := by ring
  linarith

lemma re_outerH_le {ζ : ℂ} (hζ : ζ ∈ strip) :
    (outerH ζ).re ≤ -(Real.log (1 + ζ.im ^ 2 / 4) *
      ∫ s in Icc (-(|ζ.im| / 2)) (|ζ.im| / 2), poissonK ζ.re s) := by
  set y : ℝ := ζ.im with hy
  set x : ℝ := ζ.re with hx
  set a : ℝ := |y| / 2 with ha
  set L : ℝ := Real.log (1 + y ^ 2 / 4) with hL
  set g : ℝ → ℝ := (Icc (-a) a).indicator (poissonK x) with hg
  have hre := re_outerH hζ
  have hPpos : ∀ s, 0 ≤ poissonK x s := fun s => (poissonK_pos hζ.1 hζ.2 s).le
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [sq_nonneg y])
  have hpt : ∀ t : ℝ, uR t * poissonK x (y - t) ≤ -(L * g (y - t)) := by
    intro t
    by_cases h : y - t ∈ Icc (-a) a
    · have hgt : g (y - t) = poissonK x (y - t) := indicator_of_mem h _
      rw [hgt]
      have hmem := h
      rw [mem_Icc] at hmem
      have habs : |y| / 2 ≤ |t| := by
        have : |y| ≤ |t| + |y - t| := by
          calc |y| = |t + (y - t)| := by ring_nf
            _ ≤ |t| + |y - t| := abs_add_le _ _
        have h3 : |y - t| ≤ a := abs_le.mpr hmem
        linarith
      have ht2 : y ^ 2 / 4 ≤ t ^ 2 := by
        have := sq_le_sq' (by linarith [abs_nonneg y, abs_nonneg t] : -|t| ≤ |y| / 2) habs
        nlinarith [sq_abs y, sq_abs t]
      have hLt : L ≤ Real.log (1 + t ^ 2) := by
        apply Real.log_le_log (by positivity); linarith
      have hu : uR t ≤ -L := (uR_le t).trans (by linarith)
      have := hPpos (y - t)
      nlinarith
    · have hgt : g (y - t) = 0 := indicator_of_notMem h _
      rw [hgt]
      have := uR_nonpos t
      have := hPpos (y - t)
      nlinarith
  have hint1 : Integrable fun t : ℝ => uR t * poissonK x (y - t) := by
    refine ((integrable_integrand hζ).re).congr (Eventually.of_forall fun t => ?_)
    simp only [RCLike.re_to_complex]
    rw [div_eq_mul_inv, ← one_div, Complex.re_ofReal_mul, re_inv_sin_arg hζ]
  have hgint : Integrable g := ((integrable_poissonK hζ.1 hζ.2).indicator measurableSet_Icc)
  have hint2 : Integrable fun t : ℝ => -(L * g (y - t)) :=
    ((hgint.comp_sub_left y).const_mul L).neg
  calc (outerH ζ).re = ∫ t : ℝ, uR t * poissonK x (y - t) := hre
    _ ≤ ∫ t : ℝ, -(L * g (y - t)) := integral_mono hint1 hint2 hpt
    _ = -(L * ∫ t : ℝ, g t) := by
        rw [integral_neg, integral_const_mul, integral_sub_left_eq_self g volume y]
    _ = _ := by rw [hg, integral_indicator measurableSet_Icc]

/-- **`ct:outer` (1), decay of the real part.** `Re h(σ + iτ) ≤ -2 log(1 + |τ|) + C`, uniformly on `S`. -/
theorem re_outerH_bound : ∃ C : ℝ, ∀ ζ ∈ strip, (outerH ζ).re ≤ -2 * Real.log (1 + |ζ.im|) + C := by
  refine ⟨2 * Real.log 3 + Real.log 8 + 4, fun ζ hζ => ?_⟩
  have hle := re_outerH_le hζ
  set y : ℝ := |ζ.im| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hy2 : ζ.im ^ 2 = y ^ 2 := (sq_abs _).symm
  rw [hy2] at hle
  set M := ∫ s in Icc (-(y / 2)) (y / 2), poissonK ζ.re s with hM
  set L := Real.log (1 + y ^ 2 / 4) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [sq_nonneg y])
  have hM0 : 0 ≤ M := by
    refine setIntegral_nonneg measurableSet_Icc (fun s _ => (poissonK_pos hζ.1 hζ.2 s).le)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rcases le_or_gt y 2 with hy2' | hy2'
  · have h1 : Real.log (1 + y) ≤ Real.log 3 :=
      Real.log_le_log (by linarith) (by linarith)
    have : -(L * M) ≤ 0 := by nlinarith [mul_nonneg hL0 hM0]
    have h4 : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
    linarith
  · have ha1 : 1 ≤ y / 2 := by linarith
    have hmass := poissonK_mass_ge hζ.1 hζ.2 ha1
    rw [← hM] at hmass
    -- `L ≥ 2 log (1 + y) - log 8`
    have hL1 : 2 * Real.log (1 + y) - Real.log 8 ≤ L := by
      have : Real.log ((1 + y) ^ 2 / 8) ≤ L := by
        apply Real.log_le_log (by positivity); nlinarith [sq_nonneg (y - 1)]
      rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at this
      push_cast at this
      linarith
    -- `L ≤ y`
    have hL2 : L ≤ y := by
      rw [hL, Real.log_le_iff_le_exp (by positivity)]
      have := Real.quadratic_le_exp_of_nonneg hy0
      nlinarith
    have hexp : y * (16 / π * Real.exp (-(π * (y / 2)))) ≤ 32 / π ^ 2 := by
      have hu : (π * y / 2) * Real.exp (-(π * y / 2)) ≤ 1 := by
        have := Real.add_one_le_exp (π * y / 2)
        have h5 : 0 < Real.exp (π * y / 2) := Real.exp_pos _
        rw [Real.exp_neg]
        rw [mul_inv_le_iff₀ h5]
        linarith
      have e : y * (16 / π * Real.exp (-(π * (y / 2)))) =
          32 / π ^ 2 * ((π * y / 2) * Real.exp (-(π * y / 2))) := by
        have := Real.pi_pos
        field_simp
        ring_nf
      rw [e]
      have := Real.pi_pos
      calc 32 / π ^ 2 * ((π * y / 2) * Real.exp (-(π * y / 2))) ≤ 32 / π ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hu (by positivity)
        _ = _ := by ring
    have h32 : 32 / π ^ 2 ≤ 4 := by
      have := Real.pi_gt_three
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hLT : L * (16 / π * Real.exp (-(π * (y / 2)))) ≤ 32 / π ^ 2 :=
      (mul_le_mul_of_nonneg_right hL2 (by positivity)).trans hexp
    have : -(L * M) ≤ -L + L * (16 / π * Real.exp (-(π * (y / 2)))) := by nlinarith
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 1 + y by linarith)
    linarith

end FormalResearch.SignUncertainty.CtOuter

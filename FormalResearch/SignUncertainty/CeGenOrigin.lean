module

public import FormalResearch.SignUncertainty.StripAdmissOrigin
public import FormalResearch.SignUncertainty.HankelWtConj
public import FormalResearch.CohnElkies.OriginMellinAndS0

/-!
# `cel:L3a` (1)-(2) (single-strip Dini form) and the Mellin identity of `cepe:PE3` (D1 / F2b leaves)

Formalizes:
* **General Mellin inversion (`cepe:PE3`, `uct:ce-band` (2)):**
  `integral_Gamma_mul_one_sub_cpow` (`(2π)⁻¹ ∫ Δ^{-iy} Γ(iy)(1 - a^{-iy}) dy = e^{-Δ} - e^{-aΔ}` for `a ≥ 1`, `Δ > 0`),
  re-deriving `integral_Gamma_mul_one_sub_four` (`a = 4`) and giving `pe3_mellin_identity` (`a = e^L`, `Δ ↦ 4Δ`):
  `(2π)⁻¹ ∫ 4^{-iy} Γ(iy)(1 - e^{-iy L}) Δ^{-iy} dy = e^{-4Δ} - e^{-4 e^L Δ} ≥ 0` for `Δ > 0`, `L ≥ 0`.
* **`cel:L3a` (1) (kernel bounds completing `OriginMellinAndS0`):**
  `norm_ceOriginE_imag` (`|E_c(iy)| = e^{c h_B(y/c)}`), `norm_gamma_mul_ceOriginE_le` (`|Γ(iy) E_c(iy)| ≤ √(3π) y^{-1/2} e^{-ψ_c(y)}` for `y ≥ 1`),
  and `ceOrigin_phase_quad_bound` (`|c ℋ(z/c) - z log(π/2)| ≤ C_ℋ |z|² / c` for `|z| ≤ c/2`, `0 ≤ Re z`, with `hInt_sub_linear_bound` on the full disc `|z| ≤ c/2`).
* **`cel:L3a` (2) (origin Mellin shift, single-strip Dini form, `uct:gen-preedge` (2)):**
  `ceOriginG_conj` (`G_c(-iy) = conj G_c(iy)`), `ceOrigin_shift_dini` (integrability, conjugation symmetry, Mellin identity, and `sup_{Δ ≥ 0}` bound
  under `StripM1 W` and a Dini modulus `IsDiniModulus ω δ₀` at `ζ = 1`), re-deriving the Hölder version `ceOrigin_shift`.

Class: proved, unconditional. Not covered: multipliers `J_c` that are not of the form `W̃(1 - z/c)` (such as the two-edge `W_S + W_D` of `PE3OriginData` and `thm:ce-post-edge`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real


namespace FormalResearch.SignUncertainty

/-! ### General Mellin inversion of `Γ(z)(1 - a^{-z})` (`a ≥ 1`) and the `cepe:PE3` identity -/

/-- `e^{-t} - e^{-at}` as a complex-valued function. -/
noncomputable def expDiffA (a t : ℝ) : ℂ := ((Real.exp (-t) - Real.exp (-(a * t)) : ℝ) : ℂ)

/-- `e^{-t} - e^{-4t}` as a complex-valued function. -/
noncomputable def expDiff (t : ℝ) : ℂ := expDiffA 4 t

lemma expDiffA_eq_integral {a t : ℝ} (ha : 1 ≤ a) :
    expDiffA a t = ∫ u in Icc (1 : ℝ) a, ((t * Real.exp (-(u * t)) : ℝ) : ℂ) := by
  have h : ∫ u in Icc (1 : ℝ) a, t * Real.exp (-(u * t)) = Real.exp (-t) - Real.exp (-(a * t)) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => -Real.exp (-(u * t)))
      (f' := fun u : ℝ => t * Real.exp (-(u * t))) (a := 1) (b := a) (fun u _ => by
        have h1 : HasDerivAt (fun u : ℝ => -(u * t)) (-t) u :=
          (((hasDerivAt_id' u).mul_const t).neg).congr_deriv (by ring)
        have := (h1.exp).neg
        convert this using 1; ring)
      (by apply Continuous.intervalIntegrable; fun_prop)
    rw [this]; simp; ring_nf
  rw [integral_complex_ofReal, h]; rfl

lemma expDiff_eq_integral {t : ℝ} :
    expDiff t = ∫ u in Icc (1 : ℝ) 4, ((t * Real.exp (-(u * t)) : ℝ) : ℂ) :=
  expDiffA_eq_integral (by norm_num)

lemma cpow_ofReal_inv_pos {u : ℝ} (hu : 0 < u) (a : ℂ) : (1 / (u : ℂ)) ^ a = (u : ℂ) ^ (-a) := by
  rw [Complex.cpow_neg, one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm)]

/-- The integrand `t^s e^{-ut}` of the Fubini representation. -/
noncomputable def expDiffF (s : ℂ) (t u : ℝ) : ℂ := (t : ℂ) ^ s * ((Real.exp (-(u * t)) : ℝ) : ℂ)

lemma expDiffF_integrable_Icc {a : ℝ} (_ha : 1 ≤ a) {s : ℂ} (hs : -1 < s.re) :
    Integrable (Function.uncurry (expDiffF s)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 : ℝ) a))) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ s.re * Real.exp (-t)) (Ioi 0) := by
    have := Real.GammaIntegral_convergent (s := s.re + 1) (by linarith)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [add_sub_cancel_right]; ring
  have h2 : Integrable (fun p : ℝ × ℝ => (p.1 ^ s.re * Real.exp (-p.1)) * (1 : ℝ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 : ℝ) a))) :=
    Integrable.mul_prod (f := fun t : ℝ => t ^ s.re * Real.exp (-t)) (g := fun _ : ℝ => (1 : ℝ)) h1
      (integrable_const (1 : ℝ))
  refine h2.mono' ?_ ?_
  · have hm : Measurable (Function.uncurry (expDiffF s)) := by
      refine Measurable.mul ?_ ?_
      · exact (Complex.measurable_ofReal.comp measurable_fst).pow_const s
      · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_snd.mul measurable_fst).neg))
    exact hm.aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Icc (a := (1 : ℝ)) (b := a)))] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have ht : 0 < p.1 := hp1
    simp only [Function.uncurry, expDiffF]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos ht, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hp2.1]

lemma expDiffF_integrable {s : ℂ} (hs : -1 < s.re) :
    Integrable (Function.uncurry (expDiffF s)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Icc (1 : ℝ) 4))) :=
  expDiffF_integrable_Icc (by norm_num) hs

lemma expDiffA_mellin_integrand {a : ℝ} (ha : 1 ≤ a) {s : ℂ} {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    (t : ℂ) ^ (s - 1) • expDiffA a t = ∫ u in Icc (1 : ℝ) a, expDiffF s t u := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioi.mp ht).ne'
  have hcp : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
    have := Complex.cpow_add (s - 1) 1 ht0
    rwa [sub_add_cancel, Complex.cpow_one] at this
  rw [expDiffA_eq_integral ha, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [expDiffF]
  rw [hcp]; push_cast; ring

lemma expDiff_mellin_integrand {s : ℂ} {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    (t : ℂ) ^ (s - 1) • expDiff t = ∫ u in Icc (1 : ℝ) 4, expDiffF s t u :=
  expDiffA_mellin_integrand (by norm_num) ht

/-- Mellin transform of `e^{-t} - e^{-at}` on `Re s > -1` (`1 ≤ a`): `Γ(s+1) ∫₁ᵃ u^{-(s+1)} du`. -/
lemma mellin_expDiffA {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -1 < s.re) :
    mellin (expDiffA a) s = Complex.Gamma (s + 1) * ∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(s + 1)) := by
  set F : ℝ → ℝ → ℂ := expDiffF s with hF
  have hstep : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • expDiffA a t = ∫ u in Icc (1 : ℝ) a, F t u :=
    fun t ht => expDiffA_mellin_integrand ha ht
  have hint := expDiffF_integrable_Icc ha hs
  have hinner : ∀ u ∈ Icc (1 : ℝ) a, ∫ t in Ioi (0 : ℝ), F t u = Complex.Gamma (s + 1) * (u : ℂ) ^ (-(s + 1)) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s + 1) (r := u) (by simp; linarith) hu0
    rw [add_sub_cancel_right] at this
    have e : ∀ t : ℝ, F t u = (t : ℂ) ^ s * Complex.exp (-((u : ℂ) * (t : ℂ))) := fun t => by
      simp only [hF, expDiffF]; push_cast; ring_nf
    simp_rw [e]
    rw [this, cpow_ofReal_inv_pos hu0, mul_comm]
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hstep, integral_integral_swap hint,
    setIntegral_congr_fun measurableSet_Icc hinner, integral_const_mul]

/-- Mellin transform of `e^{-t} - e^{-4t}` on `Re s > -1`: `Γ(s+1) ∫₁⁴ u^{-(s+1)} du`. -/
lemma mellin_expDiff {s : ℂ} (hs : -1 < s.re) :
    mellin expDiff s = Complex.Gamma (s + 1) * ∫ u in Icc (1 : ℝ) 4, (u : ℂ) ^ (-(s + 1)) :=
  mellin_expDiffA (by norm_num) hs

lemma mellinConvergent_expDiffA {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -1 < s.re) :
    MellinConvergent (expDiffA a) s := by
  have h := (expDiffF_integrable_Icc ha hs).integral_prod_left
  refine h.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  simp only [Function.uncurry]
  exact (expDiffA_mellin_integrand ha ht).symm

lemma mellinConvergent_expDiff {s : ℂ} (hs : -1 < s.re) : MellinConvergent expDiff s :=
  mellinConvergent_expDiffA (by norm_num) hs

/-- `m_a(y) = Γ(1 + iy) ∫₁ᵃ u^{-(1+iy)} du`, the Mellin transform of `e^{-t} - e^{-at}` on the imaginary axis. -/
noncomputable def expDiffMA (a y : ℝ) : ℂ :=
  Complex.Gamma (1 + (y : ℂ) * Complex.I) * ∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))

/-- `m(y) = Γ(1 + iy) ∫₁⁴ u^{-(1+iy)} du`, the Mellin transform of `e^{-t} - e^{-4t}` on the imaginary axis. -/
noncomputable def expDiffM (y : ℝ) : ℂ := expDiffMA 4 y

lemma expDiffMA_eq {a : ℝ} (ha : 1 ≤ a) (y : ℝ) :
    mellin (expDiffA a) (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = expDiffMA a y := by
  rw [mellin_expDiffA ha (by simp)]
  have e : ((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I + 1 = 1 + (y : ℂ) * Complex.I := by push_cast; ring
  rw [e]; rfl

lemma expDiffMA_eq_Gamma {a : ℝ} (ha : 1 ≤ a) {y : ℝ} (hy : y ≠ 0) :
    expDiffMA a y = Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (a : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
  set z : ℂ := (y : ℂ) * Complex.I with hz
  have hz0 : z ≠ 0 := by
    intro h; apply hy; have := congrArg Complex.im h; simpa [hz] using this
  have h1 : ∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(1 + z)) = (1 - (a : ℂ) ^ (-z)) / z := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    have hr : -(1 + z) ≠ -1 := fun h => hz0 (by linear_combination -h)
    rw [integral_cpow (Or.inr ⟨hr, by
      rw [uIcc_of_le ha]; intro h; linarith [h.1]⟩)]
    have e : -(1 + z) + 1 = -z := by ring
    rw [e, Complex.ofReal_one, Complex.one_cpow]
    have : (-z) ≠ 0 := neg_ne_zero.mpr hz0
    field_simp
    ring
  have h2 : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    rw [add_comm, Complex.Gamma_add_one z hz0]
  simp only [expDiffMA]
  rw [h1, h2]
  field_simp

lemma integrable_expDiffMA {a : ℝ} (ha : 1 ≤ a) : Integrable (expDiffMA a) := by
  obtain ⟨B, hB⟩ := Gamma_decay_strip (a := 1) (b := 1) one_pos le_rfl
  have hmeas : AEStronglyMeasurable (expDiffMA a) volume := by
    have h1 : Measurable fun y : ℝ => Complex.Gamma (1 + (y : ℂ) * Complex.I) := by
      have := continuous_Gamma_line 1 one_pos
      simpa using this.measurable
    have h2 : StronglyMeasurable fun y : ℝ => ∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I)) := by
      have hm : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (-(1 + (p.1 : ℂ) * Complex.I))) := by
        refine Measurable.pow (Complex.measurable_ofReal.comp measurable_snd) ?_
        exact ((measurable_const.add (Complex.measurable_ofReal.comp measurable_fst |>.mul measurable_const))).neg
      exact (hm.stronglyMeasurable).integral_prod_right' (ν := volume.restrict (Icc (1 : ℝ) a))
    exact (h1.stronglyMeasurable.mul h2).aestronglyMeasurable
  have ha1 : 0 ≤ a - 1 := by linarith
  refine (integrable_inv_one_add_sq.const_mul (4 * (|B| * (a - 1)))).mono' hmeas (Eventually.of_forall fun y => ?_)
  have hG := hB (1 + (y : ℂ) * Complex.I) (by simp) (by simp)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at hG
  have hI : ‖∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))‖ ≤ a - 1 := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (1 : ℝ) a) (by simp)
      (f := fun u : ℝ => (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))) (C := 1) (fun u hu => by
        have hu0 : 0 < u := by linarith [hu.1]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, neg_add_rev, neg_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by norm_num))
    simpa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal ha1] using this
  have hw : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + y ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    apply inv_anti₀ (by positivity)
    nlinarith [sq_abs y, abs_nonneg y]
  calc ‖expDiffMA a y‖ = ‖Complex.Gamma (1 + (y : ℂ) * Complex.I)‖ * ‖∫ u in Icc (1 : ℝ) a, (u : ℂ) ^ (-(1 + (y : ℂ) * Complex.I))‖ :=
        norm_mul _ _
    _ ≤ (B * (1 + |y|) ^ (-(2 : ℝ))) * (a - 1) :=
        mul_le_mul hG hI (norm_nonneg _) ((norm_nonneg _).trans hG)
    _ ≤ (|B| * (1 + y ^ 2)⁻¹) * (a - 1) := by
        gcongr
        · exact le_abs_self B
    _ ≤ 4 * (|B| * (a - 1)) * (1 + y ^ 2)⁻¹ := by
        have : 0 ≤ |B| * (a - 1) * (1 + y ^ 2)⁻¹ := by positivity
        nlinarith

/-- `y ↦ Γ(iy)(1 - a^{-iy})` is integrable on `ℝ` for every `a ≥ 1`. -/
theorem integrable_Gamma_mul_one_sub_cpow {a : ℝ} (ha : 1 ≤ a) :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (a : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
  refine (integrable_expDiffMA ha).congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
  exact expDiffMA_eq_Gamma ha hy

/-- **Mellin inversion of `Γ(z)(1 - a^{-z})` on `Re z = 0` (`1 ≤ a`):**
`(2π)⁻¹ ∫ Δ^{-iy} Γ(iy)(1 - a^{-iy}) dy = e^{-Δ} - e^{-aΔ}` for `Δ > 0`. -/
theorem integral_Gamma_mul_one_sub_cpow {a Δ : ℝ} (ha : 1 ≤ a) (hΔ : 0 < Δ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (a : ℂ) ^ (-((y : ℂ) * Complex.I)))) =
      ((Real.exp (-Δ) - Real.exp (-(a * Δ)) : ℝ) : ℂ) := by
  have hvert : Complex.VerticalIntegrable (mellin (expDiffA a)) 0 := by
    unfold Complex.VerticalIntegrable
    refine (integrable_expDiffMA ha).congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [expDiffMA_eq ha]
  have hcont : ContinuousAt (expDiffA a) Δ := by
    unfold expDiffA; fun_prop
  have h := mellinInv_mellin_eq 0 (expDiffA a) hΔ (mellinConvergent_expDiffA ha (by simp)) hvert hcont
  unfold mellinInv at h
  rw [Complex.real_smul] at h
  have e : ∫ y : ℝ, (Δ : ℂ) ^ (-(((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) • mellin (expDiffA a) (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (a : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    rw [expDiffMA_eq ha, expDiffMA_eq_Gamma ha hy, smul_eq_mul]
    simp
  rw [e] at h
  exact h

/-- `y ↦ Γ(iy)(1 - 4^{-iy})` is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_one_sub_four :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
  simpa using integrable_Gamma_mul_one_sub_cpow (a := 4) (by norm_num)

/-- **Mellin inversion of `Γ(z)(1 - 4^{-z})` on `Re z = 0`:**
`(2π)⁻¹ ∫ Δ^{-iy} Γ(iy)(1 - 4^{-iy}) dy = e^{-Δ} - e^{-4Δ}` for `Δ > 0`. -/
theorem integral_Gamma_mul_one_sub_four {Δ : ℝ} (hΔ : 0 < Δ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) =
      ((Real.exp (-Δ) - Real.exp (-(4 * Δ)) : ℝ) : ℂ) := by
  simpa using integral_Gamma_mul_one_sub_cpow (a := 4) (by norm_num) hΔ

/-- `y ↦ 4^{-iy} Γ(iy) (1 - e^{-iy L})` is integrable on `ℝ` for every `L ≥ 0` (`cepe:PE3`). -/
theorem integrable_pe3_mellin_kernel {L : ℝ} (hL : 0 ≤ L) :
    Integrable fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      Complex.Gamma ((y : ℂ) * Complex.I) * (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) := by
  have h1 := integrable_Gamma_mul_one_sub_cpow (a := Real.exp L) (Real.one_le_exp hL)
  have hc : Continuous fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by norm_num))
  have h2 : Integrable fun y : ℝ => (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - ((Real.exp L : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    refine h1.norm.mono' (hc.aestronglyMeasurable.mul h1.1) (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    have : ‖(4 : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := by
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]; simp
    rw [this, one_mul]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  have hexp : ((Real.exp L : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)) = Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
      ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]
    congr 1; ring
  dsimp only; rw [hexp]; ring

/-- **Mellin identity of `cepe:PE3` (`ce_o1_pre_edge.tex`, also used in `uct:ce-band` (2) and `fct:ce-preedge` Step 2):**
for every `Δ > 0` and `L ≥ 0`,
`(2π)⁻¹ ∫ 4^{-iy} Γ(iy) (1 - e^{-iy L}) Δ^{-iy} dy = e^{-4Δ} - e^{-4 e^L Δ} ≥ 0`.
(With `L = c_s X` this is the exact reference inversion of `cepe:PE3`.) -/
theorem pe3_mellin_identity {Δ L : ℝ} (hΔ : 0 < Δ) (hL : 0 ≤ L) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
        Complex.Gamma ((y : ℂ) * Complex.I) * (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) *
        (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
      ((Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) : ℝ) : ℂ) ∧
    0 ≤ Real.exp (-(4 * Δ)) - Real.exp (-(4 * Real.exp L * Δ)) := by
  have heL : 1 ≤ Real.exp L := Real.one_le_exp hL
  refine ⟨?_, sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))⟩
  have h := integral_Gamma_mul_one_sub_cpow (a := Real.exp L) (Δ := 4 * Δ) heL (by positivity)
  have hstep : ∫ y : ℝ, (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      Complex.Gamma ((y : ℂ) * Complex.I) * (1 - Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ))) *
      (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
      ∫ y : ℝ, ((4 * Δ : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)) *
      (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - ((Real.exp L : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hexp : ((Real.exp L : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)) = Complex.exp (-((y : ℂ) * Complex.I) * (L : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
        ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]
      congr 1; ring
    have h4Δ : ((4 * Δ : ℝ) : ℂ) ^ (-((y : ℂ) * Complex.I)) =
        (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΔ.le]
      norm_num
    dsimp only; rw [hexp, h4Δ]; ring
  rw [hstep, h]
  congr 2; congr 1; ring


/-! ### `cel:L3a` (1) kernel bounds and `cel:L3a` (2) single-strip Dini origin shift -/

open FormalResearch.CohnElkies

/-- `E_c(z) = exp(c ℋ(z/c) - z log(π/2))` (Lemma P.2, `cel:L3a`). -/
noncomputable def ceOriginE (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((c : ℂ) * stripH (z / (c : ℂ)) - z * ((Real.log (Real.pi / 2) : ℝ) : ℂ))

/-- `G_c(iy) = 4^{-iy} Γ(iy) [E_c(iy) J_c(iy) - J_c(0)]` with `J_c(z) = W̃(1 - z/c)` (`(cel:4.2)`). -/
noncomputable def ceOriginG (c : ℝ) (W : ℂ → ℂ) (y : ℝ) : ℂ :=
  (4 : ℂ) ^ (-((y : ℂ) * Complex.I)) * Complex.Gamma ((y : ℂ) * Complex.I) *
    (ceOriginE c ((y : ℂ) * Complex.I) * W (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) - W 1)

/-- **`cel:L3a` (1):** `|E_c(iy)| = e^{c h_B(y/c)}` for `c > 0`, `y ∈ ℝ`. -/
theorem norm_ceOriginE_imag {c : ℝ} (_hc : 0 < c) (y : ℝ) :
    ‖ceOriginE c ((y : ℂ) * Complex.I)‖ = Real.exp (c * hB (y / c)) := by
  unfold ceOriginE
  rw [Complex.norm_exp]
  have e1 : ((y : ℂ) * Complex.I) / (c : ℂ) = ((y / c : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1]
  have hre : ((c : ℂ) * stripH (((y / c : ℝ) : ℂ) * Complex.I) -
      (y : ℂ) * Complex.I * ((Real.log (Real.pi / 2) : ℝ) : ℂ)).re =
      c * hB (y / c) := by
    simp only [Complex.sub_re, Complex.re_ofReal_mul, re_stripH_imag]
    have h0 : ((y : ℂ) * Complex.I * ((Real.log (Real.pi / 2) : ℝ) : ℂ)).re = 0 := by
      rw [mul_assoc, Complex.mul_re]; simp
    rw [h0, sub_zero]
    rfl
  rw [hre]

/-- **`cel:L3a` (1):** `|Γ(iy) E_c(iy)| ≤ √(3π) y^{-1/2} e^{-ψ_c(y)}` for `c > 0`, `y ≥ 1`. -/
theorem norm_gamma_mul_ceOriginE_le {c y : ℝ} (hc : 0 < c) (hy : 1 ≤ y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I) * ceOriginE c ((y : ℂ) * Complex.I)‖ ≤
      Real.sqrt (3 * Real.pi) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-originPsi c y) := by
  rw [norm_mul, norm_ceOriginE_imag hc y]
  exact norm_gamma_mul_exp_hB_le hc hy

/-- **`cel:L3a` (1), quadratic phase bound for `hInt`:**
`∃ C_ℋ > 0, ∀ ζ, |ζ| ≤ 1/2 → |ℋ(ζ) - ζ log(π/2)| ≤ C_ℋ |ζ|²`. -/
theorem hInt_sub_linear_bound :
    ∃ C_H : ℝ, 0 < C_H ∧ ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 2 →
      ‖hInt ζ - ζ * ((Real.log (Real.pi / 2) : ℝ) : ℂ)‖ ≤ C_H * ‖ζ‖ ^ 2 := by
  set K : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 2) with hK
  have hK_sub : K ⊆ hStrip := fun w hw => by
    have hn : ‖w‖ ≤ 1 / 2 := by simpa [hK, Metric.mem_closedBall, dist_zero_right] using hw
    have hre : |w.re| ≤ 1 / 2 := (Complex.abs_re_le_norm w).trans hn
    exact ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (continuousOn_hLogDeriv.mono hK_sub)
  have hlip : ∀ w ∈ K, ‖hLog w - hLog 0‖ ≤ |M| * ‖w‖ := by
    intro w hw
    have h0K : (0 : ℂ) ∈ K := Metric.mem_closedBall_self (by norm_num)
    have hconv : Convex ℝ K := convex_closedBall (0 : ℂ) (1 / 2)
    have hd : ∀ z ∈ K, HasDerivWithinAt hLog (hLogDeriv z) K z := fun z hz =>
      (hasDerivAt_hLog (hK_sub hz)).hasDerivWithinAt
    have hbd : ∀ z ∈ K, ‖hLogDeriv z‖ ≤ |M| := fun z hz => (hM z hz).trans (le_abs_self M)
    simpa [sub_zero] using hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd h0K hw
  refine ⟨|M| + 1, by positivity, fun ζ hζ => ?_⟩
  have hζK : ζ ∈ K := by simpa [hK, Metric.mem_closedBall, dist_zero_right] using hζ
  have heq : hInt ζ - ζ * ((Real.log (Real.pi / 2) : ℝ) : ℂ) =
      ∫ s in (0 : ℝ)..1, ζ * (hLog ((s : ℂ) * ζ) - hLog 0) := by
    unfold hInt
    rw [← hLog_zero]
    have h1 : IntervalIntegrable (fun s : ℝ => ζ * hLog ((s : ℂ) * ζ)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_const.mul (continuousOn_hLog.comp
        (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ).continuousOn
        fun s hs => smul_mem_hStrip (hK_sub hζK) hs)
    have h2 : IntervalIntegrable (fun _ : ℝ => ζ * hLog 0) volume 0 1 := intervalIntegrable_const
    rw [show ζ * hLog 0 = ∫ _s in (0 : ℝ)..1, ζ * hLog 0 by simp, ← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun s _ => by ring
  rw [heq]
  have hbd_int : ∀ s ∈ uIoc (0 : ℝ) 1, ‖ζ * (hLog ((s : ℂ) * ζ) - hLog 0)‖ ≤ |M| * ‖ζ‖ ^ 2 := by
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hs1 : s ≤ 1 := hs.2
    have hns : ‖(s : ℂ) * ζ‖ = s * ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
    have hmK : (s : ℂ) * ζ ∈ K := by
      simp only [hK, Metric.mem_closedBall, dist_zero_right, hns]
      calc s * ‖ζ‖ ≤ 1 * (1 / 2) := mul_le_mul hs1 hζ (norm_nonneg _) zero_le_one
        _ = 1 / 2 := one_mul _
    rw [norm_mul]
    calc ‖ζ‖ * ‖hLog ((s : ℂ) * ζ) - hLog 0‖
        ≤ ‖ζ‖ * (|M| * ‖(s : ℂ) * ζ‖) := mul_le_mul_of_nonneg_left (hlip _ hmK) (norm_nonneg _)
      _ = |M| * s * ‖ζ‖ ^ 2 := by rw [hns]; ring
      _ ≤ |M| * 1 * ‖ζ‖ ^ 2 := by gcongr
      _ = |M| * ‖ζ‖ ^ 2 := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbd_int
  simp only [sub_zero, abs_one, mul_one] at hnorm
  calc ‖∫ s in (0 : ℝ)..1, ζ * (hLog ((s : ℂ) * ζ) - hLog 0)‖
      ≤ |M| * ‖ζ‖ ^ 2 := hnorm
    _ ≤ (|M| + 1) * ‖ζ‖ ^ 2 := by nlinarith [sq_nonneg ‖ζ‖]

/-- **`cel:L3a` (1), quadratic phase bound:**
there is an absolute constant `C_ℋ > 0` such that for all `c > 0` and `z ∈ ℂ` with `0 ≤ Re z`, `|z| ≤ c/2`,
`|c ℋ(z/c) - z log(π/2)| ≤ C_ℋ |z|² / c`. -/
theorem ceOrigin_phase_quad_bound :
    ∃ C_H : ℝ, 0 < C_H ∧ ∀ {c : ℝ}, 0 < c → ∀ {z : ℂ}, 0 ≤ z.re → ‖z‖ ≤ c / 2 →
      ‖(c : ℂ) * stripH (z / (c : ℂ)) - z * ((Real.log (Real.pi / 2) : ℝ) : ℂ)‖ ≤ C_H * ‖z‖ ^ 2 / c := by
  obtain ⟨C_H, hCH, hbd⟩ := hInt_sub_linear_bound
  refine ⟨C_H, hCH, fun {c} hc {z} hz0 hzc => ?_⟩
  set ζ : ℂ := z / (c : ℂ) with hζ
  have hζn : ‖ζ‖ = ‖z‖ / c := by
    rw [hζ, norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hζhalf : ‖ζ‖ ≤ 1 / 2 := by
    rw [hζn, div_le_iff₀ hc]; linarith
  have hζre0 : 0 ≤ ζ.re := by rw [hζ, Complex.div_ofReal_re]; exact div_nonneg hz0 hc.le
  have hζre1 : ζ.re < 1 := lt_of_le_of_lt ((Complex.re_le_norm ζ).trans hζhalf) (by norm_num)
  have hstrip : stripH ζ = hInt ζ := (hInt_eq_stripH hζre0 hζre1).symm
  have hc_ne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hfac : (c : ℂ) * stripH ζ - z * ((Real.log (Real.pi / 2) : ℝ) : ℂ) =
      (c : ℂ) * (hInt ζ - ζ * ((Real.log (Real.pi / 2) : ℝ) : ℂ)) := by
    rw [hstrip, hζ]; field_simp
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  calc c * ‖hInt ζ - ζ * ((Real.log (Real.pi / 2) : ℝ) : ℂ)‖
      ≤ c * (C_H * ‖ζ‖ ^ 2) := mul_le_mul_of_nonneg_left (hbd ζ hζhalf) hc.le
    _ = C_H * ‖z‖ ^ 2 / c := by rw [hζn]; field_simp [hc.ne']

lemma four_cpow_mul_ceOriginE {c : ℝ} (hc : 0 < c) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re < c) :
    (4 : ℂ) ^ (-z) * ceOriginE c z = admissEhat c z := by
  have hre0 : 0 ≤ (z / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hre1 : (z / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; exact (div_lt_one hc).mpr hz1
  unfold ceOriginE admissEhat
  rw [← hInt_eq_stripH hre0 hre1]
  have h4 : (4 : ℂ) ^ (-z) = Complex.exp (-z * ((Real.log 4 : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
    ring_nf
  have h2 : ((2 * Real.pi : ℝ) : ℂ) ^ (-z) = Complex.exp (-z * ((Real.log (2 * Real.pi) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)),
      ← Complex.ofReal_log (by positivity)]
    ring_nf
  have hl : Real.log (2 * Real.pi) = Real.log 4 + Real.log (Real.pi / 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  rw [h4, h2, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hl]
  push_cast
  ring

/-- Conjugation symmetry of `E_c` on the imaginary axis: `E_c(-iy) = conj E_c(iy)` (`cel:L3a` (2)). -/
theorem ceOriginE_conj_imag {c : ℝ} (_hc : 0 < c) (y : ℝ) :
    ceOriginE c (((-y : ℝ) : ℂ) * Complex.I) = starRingEnd ℂ (ceOriginE c ((y : ℂ) * Complex.I)) := by
  have hre0 : 0 ≤ (((y : ℂ) * Complex.I) / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; simp
  have hre1 : (((y : ℂ) * Complex.I) / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; simp
  have hre0' : 0 ≤ ((((-y : ℝ) : ℂ) * Complex.I) / (c : ℂ)).re := by rw [Complex.div_ofReal_re]; simp
  have hre1' : ((((-y : ℝ) : ℂ) * Complex.I) / (c : ℂ)).re < 1 := by rw [Complex.div_ofReal_re]; simp
  have hconj_arg : ((((-y : ℝ) : ℂ) * Complex.I) / (c : ℂ)) =
      starRingEnd ℂ (((y : ℂ) * Complex.I) / (c : ℂ)) := by
    simp [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
  unfold ceOriginE
  rw [← hInt_eq_stripH hre0 hre1, ← hInt_eq_stripH hre0' hre1', hconj_arg,
    hankelHInt_conj hre0 hre1, ← Complex.exp_conj]
  congr 1
  simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- Conjugation symmetry of `G_c` on the imaginary axis: `G_c(-iy) = conj G_c(iy)` (`cel:L3a` (2)). -/
theorem ceOriginG_conj {c : ℝ} (hc : 0 < c) {W : ℂ → ℂ} (hW : StripM1 W) (y : ℝ) :
    ceOriginG c W (-y) = starRingEnd ℂ (ceOriginG c W y) := by
  have h4arg : (4 : ℂ).arg ≠ Real.pi := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_ne_zero.symm
  have h4c : (4 : ℂ) ^ (-(((-y : ℝ) : ℂ) * Complex.I)) =
      starRingEnd ℂ ((4 : ℂ) ^ (-((y : ℂ) * Complex.I))) := by
    have h := Complex.cpow_conj (4 : ℂ) (-((y : ℂ) * Complex.I)) h4arg
    rw [map_ofNat] at h
    rw [← h]; congr 1
    simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hGc : Complex.Gamma (((-y : ℝ) : ℂ) * Complex.I) =
      starRingEnd ℂ (Complex.Gamma ((y : ℂ) * Complex.I)) := by
    rw [← Complex.Gamma_conj]; congr 1
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hWc : W (1 - (((-y : ℝ) : ℂ) * Complex.I) / (c : ℂ)) =
      starRingEnd ℂ (W (1 - ((y : ℂ) * Complex.I) / (c : ℂ))) := by
    have hre0 : 0 ≤ (1 - ((y : ℂ) * Complex.I) / (c : ℂ)).re := by rw [re_one_sub_div hc]; simp
    have hre1 : (1 - ((y : ℂ) * Complex.I) / (c : ℂ)).re ≤ 1 := by rw [re_one_sub_div hc]; simp
    have harg : 1 - (((-y : ℝ) : ℂ) * Complex.I) / (c : ℂ) =
        starRingEnd ℂ (1 - ((y : ℂ) * Complex.I) / (c : ℂ)) := by
      simp [map_sub, map_one, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [harg, hW.real _ hre0 hre1]
  unfold ceOriginG
  rw [h4c, hGc, ceOriginE_conj_imag hc y, hWc]
  simp only [map_mul, map_sub, W_one_conj hW]

section
variable {W : ℂ → ℂ}

/-- The pointwise limit `Γ(ε + iy) K(ε + iy) → Γ(iy) K(iy)` as `ε ↓ 0` (`y ≠ 0`). -/
lemma tendsto_Gamma_mul_admissK {c : ℝ} (hc : 0 < c) (hW : StripM1 W) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => Complex.Gamma ((ε : ℂ) + (y : ℂ) * Complex.I) * admissK c W ((ε : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I))) := by
  set z0 : ℂ := (y : ℂ) * Complex.I with hz0
  have hz0re : z0.re = 0 := by simp [hz0]
  have hz0ne : z0 ≠ 0 := by
    intro h; apply hy; have := congrArg Complex.im h; simpa [hz0] using this
  have hGc : ContinuousAt Complex.Gamma z0 := continuousAt_Gamma_of_re_nonneg hz0re.ge hz0ne
  have hKc := admissK_continuousOn hc hW z0 ⟨hz0re.ge, by rw [hz0re]; exact hc.le⟩
  have hcw : ContinuousWithinAt (fun z : ℂ => Complex.Gamma z * admissK c W z)
      {z : ℂ | 0 ≤ z.re ∧ z.re ≤ c} z0 := hGc.continuousWithinAt.mul hKc
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
      (𝓝[{z : ℂ | 0 ≤ z.re ∧ z.re ≤ c}] z0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
        (by fun_prop : Continuous fun ε : ℝ => (ε : ℂ) + (y : ℂ) * Complex.I).continuousAt.tendsto
      simpa [hz0] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
      exact ⟨by simp; exact hε.1.le, by simp; exact hε.2.le⟩
  exact hcw.tendsto.comp hz

/-- `Γ(iy) K(iy)` is integrable under a Dini modulus at `ζ = 1`. -/
theorem integrable_Gamma_mul_admissK_dini {c δ₀ : ℝ} {ω : ℝ → ℝ} (hc : 2 ≤ c) (hW : StripM1 W)
    (hω : IsDiniModulus ω δ₀)
    (hD : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ δ₀ → ‖W ζ - W 1‖ ≤ ω ‖1 - ζ‖) :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨δ₁, A, hδ₁, _, hδ₁_c, _, hA_out, _⟩ := admissRem_line_bound_dini hc hW hω hD
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)) volume := by
    have hf : Continuous fun y : ℝ => (y : ℂ) * Complex.I := by fun_prop
    have hK : Continuous fun y : ℝ => admissK c W ((y : ℂ) * Complex.I) :=
      (admissK_continuousOn hc0 hW).comp_continuous hf (fun y => ⟨by simp, by simp; exact hc0.le⟩)
    have hcont : ContinuousOn (fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)) {y : ℝ | y ≠ 0} := by
      intro y hy
      have hz0ne : ((y : ℂ) * Complex.I) ≠ 0 := by
        intro h; apply hy; have := congrArg Complex.im h; simpa using this
      have hG : ContinuousAt Complex.Gamma ((y : ℂ) * Complex.I) := continuousAt_Gamma_of_re_nonneg (by simp) hz0ne
      exact ((hG.comp_of_eq hf.continuousAt rfl).mul hK.continuousAt).continuousWithinAt
    have := hcont.aestronglyMeasurable (μ := volume) (isOpen_compl_singleton.measurableSet)
    rwa [show {y : ℝ | y ≠ 0} = {(0 : ℝ)}ᶜ from rfl, restrict_compl_singleton] at this
  have hbd : ∀ y : ℝ, y ≠ 0 → ‖Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I)‖ ≤ A * diniOriginMajorant c δ₁ ω y := by
    intro y hy
    have hlim := (tendsto_Gamma_mul_admissK hc0 hW hy).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (abs_pos.mpr hy)), Ioo_mem_nhdsGT hc0] with ε hε hε'
    have hε_half : ε ≤ 1 / 2 := (hε.2.trans_le (min_le_left _ _)).le
    have hεy : ε ≤ |y| := (hε.2.trans_le (min_le_right _ _)).le
    have hre0 : 0 < ((ε : ℂ) + (y : ℂ) * Complex.I).re := by simpa using hε.1
    have hre1 : ((ε : ℂ) + (y : ℂ) * Complex.I).re < c := by simpa using hε'.2
    rw [← admissRem_eq hc0 hre0 hre1]
    exact hA_out ε y hε.1 hε_half hy hεy
  refine ((integrable_diniOriginMajorant hc0 hδ₁ hδ₁_c hω).const_mul A).mono' hmeas ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
  exact hbd y hy

/-- `Γ(iy) K(iy)` is integrable. -/
theorem integrable_Gamma_mul_admissK {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (_hα1 : α < 1) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Integrable fun y : ℝ => Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) := by
  obtain ⟨CH, hCH⟩ := hH
  exact integrable_Gamma_mul_admissK_dini hc hW (IsDiniModulus.holder hα0 (by norm_num : (0 : ℝ) < 1 / 2) CH)
    (fun ζ h0 h1 hn => (hCH ζ h0 h1 hn).trans (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity)))

lemma integrable_cpow_mul {Δ : ℝ} (hΔ : 0 < Δ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable fun y : ℝ => (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) * g y := by
  have hc : Continuous fun y : ℝ => (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))
  refine hg.norm.mono' (hc.aestronglyMeasurable.mul hg.1) (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  have : ‖(Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]; simp
  rw [this, one_mul]

lemma ceOriginG_decomp {c : ℝ} (hc : 0 < c) (W : ℂ → ℂ) (y : ℝ) :
    ceOriginG c W y = Complex.Gamma ((y : ℂ) * Complex.I) * admissK c W ((y : ℂ) * Complex.I) +
      W 1 * (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
  have h := four_cpow_mul_ceOriginE hc (z := (y : ℂ) * Complex.I) (by simp) (by simpa using hc)
  unfold ceOriginG admissK
  rw [← h]
  ring

private lemma integral_norm_even_eq_two_mul_Ioi {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ y, f (-y) = f y) :
    ∫ y : ℝ, f y = 2 * ∫ y in Ioi (0 : ℝ), f y := by
  have hsplit : ∫ y : ℝ, f y = (∫ y in Iic (0 : ℝ), f y) + ∫ y in Ioi (0 : ℝ), f y := by
    rw [← setIntegral_union (Set.disjoint_left.mpr fun x hx1 hx2 => not_lt.mpr hx1 hx2)
      measurableSet_Ioi hf.integrableOn hf.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have hneg : ∫ y in Iic (0 : ℝ), f y = ∫ y in Ioi (0 : ℝ), f y := by
    have h1 := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := f)
    rw [neg_zero] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => heven y
  linarith

/-- **`cel:L3a` (2) / `uct:gen-origin` for the lift of an admissible strip multiplier with a Dini modulus**
(`ce_rate.tex` Lemma P.2 (2), `(cel:4.2)`, `(cel:4.5)`, `(uct:gen-origin)`):
for `c ≥ 2`, `W̃` satisfying `StripM1` and a Dini modulus `|W̃(ζ) - W̃(1)| ≤ ω(|1 - ζ|)` near `ζ = 1`
(with `IsDiniModulus ω δ₀`: nonnegative, nondecreasing, `∫₀^{δ₀} ω(r)/r dr < ∞`),
(a) `G_c(iy) = 4^{-iy} Γ(iy)[E_c(iy) W̃(1 - iy/c) - W̃(1)]` is integrable on `ℝ`;
(b) `G_c(-iy) = conj G_c(iy)`;
(c) for every `Δ > 0`, `f_W(Δ) - W̃(1) e^{-4Δ} = (2π)⁻¹ ∫ G_c(iy) Δ^{-iy} dy`;
(d) for every `Δ > 0`, `|f_W(Δ) - W̃(1).re e^{-4Δ}| ≤ π⁻¹ ∫₀^∞ |G_c(iy)| dy`
(and the same bound holds trivially at `Δ = 0` for the continuous extension `f_W(0) = W̃(1).re`).
Class: proved, unconditional. Scope: single-strip multipliers `J_c(z) = W̃(1 - z/c)` with `StripM1 W̃` and a Dini modulus at `1`. -/
theorem ceOrigin_shift_dini {c δ₀ : ℝ} {ω : ℝ → ℝ} (hc : 2 ≤ c) (hW : StripM1 W) (hω : IsDiniModulus ω δ₀)
    (hD : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ δ₀ → ‖W ζ - W 1‖ ≤ ω ‖1 - ζ‖) :
    Integrable (ceOriginG c W) ∧
      (∀ y : ℝ, ceOriginG c W (-y) = starRingEnd ℂ (ceOriginG c W y)) ∧
      (∀ {Δ : ℝ}, 0 < Δ →
        ((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
          ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) ∧
      (∀ {Δ : ℝ}, 0 < Δ →
        |admissLift c W Δ - (W 1).re * Real.exp (-(4 * Δ))| ≤
          (1 / Real.pi) * ∫ y in Ioi (0 : ℝ), ‖ceOriginG c W y‖) := by
  have hc0 : 0 < c := by linarith
  have hρ := integrable_Gamma_mul_admissK_dini hc hW hω hD
  have hm := integrable_Gamma_mul_one_sub_four
  have hint : Integrable (ceOriginG c W) := by
    have := hρ.add (hm.const_mul (W 1))
    exact this.congr (Eventually.of_forall fun y => (ceOriginG_decomp hc0 W y).symm)
  have hconj : ∀ y : ℝ, ceOriginG c W (-y) = starRingEnd ℂ (ceOriginG c W y) := ceOriginG_conj hc0 hW
  have hshift : ∀ {Δ : ℝ}, 0 < Δ →
      ((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) := by
    intro Δ hΔ
    have h1 := admiss_lift_eq_limit_dini hc hW hω hD hΔ
    have h2 := integral_Gamma_mul_one_sub_four hΔ
    have e : ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) =
        (∫ y : ℝ, originLimit c W Δ y) + W 1 * ∫ y : ℝ, (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) *
          (Complex.Gamma ((y : ℂ) * Complex.I) * (1 - (4 : ℂ) ^ (-((y : ℂ) * Complex.I)))) := by
      rw [← integral_const_mul]
      have hs := integral_add (integrable_cpow_mul hΔ hρ) ((integrable_cpow_mul hΔ hm).const_mul (W 1))
      simp only [originLimit]
      rw [← hs]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [ceOriginG_decomp hc0 W y]
      ring
    rw [e, mul_add, ← mul_assoc, mul_comm ((1 / (2 * Real.pi) : ℝ) : ℂ) (W 1), mul_assoc, h2]
    rw [h1]
    push_cast
    ring_nf
  refine ⟨hint, hconj, hshift, fun {Δ} hΔ => ?_⟩
  have hW1_real : W 1 = ((W 1).re : ℂ) := by
    have h := W_one_conj hW
    exact Complex.ext rfl (by
      have him := congrArg Complex.im h
      simp only [Complex.conj_im, Complex.ofReal_im] at him ⊢
      linarith)
  have hdiff_eq : ((admissLift c W Δ - (W 1).re * Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) := by
    rw [← hshift hΔ, hW1_real]; push_cast; rfl
  have hnorm_lhs : |admissLift c W Δ - (W 1).re * Real.exp (-(4 * Δ))| =
      ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖ := by
    rw [← hdiff_eq, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm_lhs, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint_norm : ‖∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖ ≤ ∫ y : ℝ, ‖ceOriginG c W y‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
    simp
  have heven : ∀ y : ℝ, ‖ceOriginG c W (-y)‖ = ‖ceOriginG c W y‖ := fun y => by
    rw [hconj y, Complex.norm_conj]
  have htwo := integral_norm_even_eq_two_mul_Ioi hint.norm heven
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))‖
      ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, ‖ceOriginG c W y‖ :=
        mul_le_mul_of_nonneg_left hint_norm (by positivity)
    _ = 1 / (2 * Real.pi) * (2 * ∫ y in Ioi (0 : ℝ), ‖ceOriginG c W y‖) := by rw [htwo]
    _ = (1 / Real.pi) * ∫ y in Ioi (0 : ℝ), ‖ceOriginG c W y‖ := by field_simp [Real.pi_ne_zero]

/-- **`cel:L3a` (2) / `uct:gen-origin` for the lift of an admissible strip multiplier** (`(cel:4.2)`, `(cel:4.5)`, `(uct:gen-origin)`):
for `c ≥ 2`, `W̃` with the hypotheses `StripM1` and the Hölder bound `|W̃(ζ) - W̃(1)| ≤ C |1 - ζ|^α` at `ζ = 1` (this is `J_c(z) - J_c(0) = O(|z|^α)`,
`J_c(z) = W̃(1 - z/c)`; `α = 1/2` is the case used by `uct:gen-preedge` (2)), `G_c(iy) = 4^{-iy} Γ(iy)[E_c(iy) J_c(iy) - J_c(0)]` is integrable on `ℝ` and, for every `Δ > 0`,
`f_W(Δ) - W̃(1) e^{-4Δ} = (2π)⁻¹ ∫ G_c(iy) Δ^{-iy} dy`, where `f_W = admissLift c W` is the lift (`ĥ_c`).
Derived directly from the Dini version `ceOrigin_shift_dini`. Class: proved. -/
theorem ceOrigin_shift {c α : ℝ} (hc : 2 ≤ c) (hα0 : 0 < α) (_hα1 : α < 1) {W : ℂ → ℂ} (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Integrable (ceOriginG c W) ∧ ∀ {Δ : ℝ}, 0 < Δ →
      ((admissLift c W Δ : ℝ) : ℂ) - W 1 * ((Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I)) := by
  obtain ⟨CH, hCH⟩ := hH
  have h := ceOrigin_shift_dini hc hW (IsDiniModulus.holder hα0 (by norm_num : (0 : ℝ) < 1 / 2) CH)
    (fun ζ h0 h1 hn => (hCH ζ h0 h1 hn).trans (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity)))
  exact ⟨h.1, h.2.2.1⟩

end


/-- info: 'FormalResearch.SignUncertainty.integral_Gamma_mul_one_sub_cpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Gamma_mul_one_sub_cpow

/-- info: 'FormalResearch.SignUncertainty.integral_Gamma_mul_one_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_Gamma_mul_one_sub_four

/-- info: 'FormalResearch.SignUncertainty.pe3_mellin_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pe3_mellin_identity

/-- info: 'FormalResearch.SignUncertainty.norm_ceOriginE_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_ceOriginE_imag

/-- info: 'FormalResearch.SignUncertainty.norm_gamma_mul_ceOriginE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_gamma_mul_ceOriginE_le

/-- info: 'FormalResearch.SignUncertainty.ceOrigin_phase_quad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceOrigin_phase_quad_bound

/-- info: 'FormalResearch.SignUncertainty.ceOriginG_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceOriginG_conj

/-- info: 'FormalResearch.SignUncertainty.ceOrigin_shift_dini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceOrigin_shift_dini

/-- info: 'FormalResearch.SignUncertainty.ceOrigin_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceOrigin_shift

end FormalResearch.SignUncertainty

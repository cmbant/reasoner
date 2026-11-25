module

public import FormalResearch.ModularBootstrap.WeightAxioms.ComplexAsymptotics
public import FormalResearch.ModularBootstrap.PoissonJensen.HankelInversion
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# General-Weight Hankel Continuation on the Strip `|Im b| ≤ 1/2` (Lemma 4(a), (W1), (P0))

Defines `hankelContinuationW prob.w c' g b` for every weight `w ≥ 1`:
`G(b) = -2π ∫₀^∞ g(t) K_{-c' b² / 3}^{(w)}(t) dt`,
and proves all analytic and real-line properties unconditionally for every `prob : FixedWeightProblem`:

* `hankelContinuationW_one_eq`: coincides with `Integration.hankelContinuation c' g b` at `w = 1`.
* `testClass_kernelK_integrable` and `testClass_integral_kernelK_le`: for `c' ≥ c₀` (`c₀ ≥ max 1 (24 S)`),
  `∫₀^∞ |g(t)| K_{c'/12}^{(w)}(t) dt ≤ C (1 + c'^m) M[g]` (`≤ C' c'^m M[g]`).
* `hankelContinuationW_strip_bound` (**Lemma 4(a)**): `‖G(b)‖ ≤ C_e c'^m M[g]` and
  `‖G(b)‖ ≤ C_e (1 + c'^m) M[g]` on `|Im b| ≤ 1/2`.
* `continuousOn_hankelContinuationW`: `G` is continuous on `{b : ℂ | |b.im| ≤ 1/2}`.
* `differentiableOn_hankelContinuationW`: `G` is holomorphic on `{b : ℂ | |b.im| < 1/2}`.
* `hankelContinuationW_ofReal`: for every `b : ℝ`, `G(b) = (g (c' b^2 / 3) : ℂ)` (valid for all `c' > 0`
  and all `w ≥ 1` simultaneously via spherical reduction to `ℝ × EuclideanSpace ℝ (Fin (2*(w-1)+1))`
  and polar coordinates).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat FourierTransform ENNReal

namespace FormalResearch.ModularBootstrap.WeightAxioms

open Crossing Bessel

/-! ### Section 1: Definition and `w = 1` compatibility -/

/-- General-weight Hankel continuation on the strip `|Im b| ≤ 1/2`:
`G(b) = -2π ∫₀^∞ g(t) K_{-c' b² / 3}^{(w)}(t) dt`. -/
noncomputable def hankelContinuationW (w : ℕ) (c' : ℝ) (g : ℝ → ℝ) (b : ℂ) : ℂ :=
  -2 * (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ),
    (g t : ℂ) * kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)

lemma hankelContinuationW_one_eq {c' : ℝ} (hc' : 0 ≤ c') (g : ℝ → ℝ) (b : ℂ) :
    hankelContinuationW 1 c' g b = Integration.hankelContinuation c' g b := by
  unfold hankelContinuationW Integration.hankelContinuation
  refine congrArg ((-2 * (Real.pi : ℂ)) * ·) ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  refine congrArg ((g t : ℂ) * ·) ?_
  unfold kernelKC Integration.besselI0C
  simp only [Nat.sub_self, pow_zero, one_mul]
  let z : ℂ := 4 * (Real.pi : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)
  have hz_sq : 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ) = z ^ 2 / 4 := by
    dsimp [z]
    have hsq : ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 = ((c' * t / 3 : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (by positivity)
    calc 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ)
        = (4 * (Real.pi : ℂ) * Complex.I * b) ^ 2 * ((c' * t / 3 : ℝ) : ℂ) / 4 := by
          rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]; push_cast; ring
      _ = (4 * (Real.pi : ℂ) * Complex.I * b) ^ 2 *
            ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 / 4 := by
          rw [hsq]
      _ = _ := by ring
  rw [hz_sq, besselSC_eq_sin_integral 0 z, sinEvenIntegral_zero]
  dsimp [z]
  simp

/-! ### Section 2: Strip integrability, strip bound (Lemma 4(a)), and continuity -/

lemma continuous_kernelK {w : ℕ} (hw : 1 ≤ w) (a : ℝ) : Continuous (kernelK w a) := by
  have heq : kernelK w a = fun t : ℝ => (kernelKC w (a : ℂ) (t : ℂ)).re := by
    ext t
    rw [kernelKC_ofReal w hw a t, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp ((kernelKC_entire_t w (a : ℂ)).continuous.comp Complex.continuous_ofReal)

/-- **Lemma 4(a) kernel integrability & `L¹` bound**:
for `c' ≥ c₀` (`c₀ ≥ max 1 (24 S)`), `|g| * K_{c'/12}^{(w)}` is integrable on `Ioi 0` with
`∫₀^∞ |g(t)| K_{c'/12}^{(w)}(t) dt ≤ C_int_K * c'^m * M[g]`. -/
theorem testClass_integral_kernelK_le (prob : FixedWeightProblem) :
    ∃ C_Kint c₀ : ℝ, 0 < C_Kint ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
        IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (c' / 12) t) (Ioi 0) ∧
        ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t ≤
          C_Kint * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g := by
  have hw := prob.hw
  obtain ⟨C_int, _, hCint_pos, _, hwin⟩ := testClass_window_bounds prob
  obtain ⟨C_K, c₀, hCK_pos, hc₀_ge, hK_bd⟩ := kernelK_le_mul_cardyV_gen prob
  let C_head : ℝ := (2 * Real.pi) ^ (prob.w - 1) * Real.exp (4 * Real.pi / Real.sqrt 3) * C_int
  have hChead_pos : 0 < C_head := by positivity
  let C_Kint : ℝ := C_head + C_K
  refine ⟨C_Kint, c₀, by positivity, hc₀_ge, fun {c' g} hc' hg => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hcm
  have hcS : 24 * prob.totalShift ≤ c' := (le_max_right _ _).trans hcm
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc1
  have ha_ge : prob.totalShift ≤ c' / 12 := by linarith [prob.totalShift_nonneg]
  have hc_rpow : (1 : ℝ) ≤ c' ^ (prob.m : ℝ) := by
    rw [Real.rpow_natCast]; exact one_le_pow₀ hc1
  have h4_pos : 0 < 4 / c' := div_pos (by norm_num) hc'_pos
  have haesm : AEStronglyMeasurable (fun t : ℝ => |g t| * kernelK prob.w (c' / 12) t)
      (volume.restrict (Ioi 0)) :=
    (((hg.cont.abs.mono Ioi_subset_Ici_self).mul
      (continuous_kernelK hw (c' / 12)).continuousOn)).aestronglyMeasurable
      measurableSet_Ioi
  have hwin_bd := hwin ha_ge hg
  have hA_int : IntegrableOn (fun t : ℝ => |g t| * t ^ (prob.w - 1)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ‖t ^ (prob.w - 1) * g t‖) (Ioi 0) :=
      ((integrable_radialLift_iff hw g).1 hg.int_lift).norm
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le _), mul_comm]
  let C_ker : ℝ := (2 * Real.pi) ^ (prob.w - 1) * Real.exp (4 * Real.pi / Real.sqrt 3)
  have hhead_dom : ∀ t ∈ Ioc (0 : ℝ) (4 / c'),
      ‖|g t| * kernelK prob.w (c' / 12) t‖ ≤ C_ker * (|g t| * t ^ (prob.w - 1)) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have hK_nn : 0 ≤ kernelK prob.w (c' / 12) t :=
      kernelK_nonneg (by positivity) ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hK_nn)]
    have hK_ub : kernelK prob.w (c' / 12) t ≤ C_ker * t ^ (prob.w - 1) := by
      unfold kernelK
      have hs_eq : (∑' j : ℕ, kernelKTerm prob.w (c' / 12) t j) =
          besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) := by
        unfold besselS besselTerm kernelKTerm
        refine tsum_congr fun j => ?_
        rw [show j + prob.w - 1 = j + (prob.w - 1) by omega]
      rw [hs_eq]
      have hs_exp : besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) ≤
          Real.exp (4 * Real.pi / Real.sqrt 3) := by
        have h1 := besselS_sq_div_four_le_exp (prob.w - 1)
          (u := 2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t)) (by positivity)
        have harg : (2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t)) ^ 2 / 4 =
            4 * Real.pi ^ 2 * (c' / 12) * t := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
        rw [harg] at h1
        have h1' : besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t) ≤
            Real.exp (2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t)) :=
          h1.trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast Nat.factorial_pos (prob.w - 1)))
        have hsqrt_le : 2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t) ≤ 4 * Real.pi / Real.sqrt 3 := by
          have h13 : (c' / 12) * t ≤ 1 / 3 := by
            calc (c' / 12) * t ≤ (c' / 12) * (4 / c') := by gcongr; exact ht.2
              _ = 1 / 3 := by field_simp [hc'_pos.ne']; norm_num
          have harg_le : 4 * Real.pi ^ 2 * (c' / 12) * t ≤ (2 * Real.pi / Real.sqrt 3) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num)]
            calc 4 * Real.pi ^ 2 * (c' / 12) * t = 4 * Real.pi ^ 2 * ((c' / 12) * t) := by ring
              _ ≤ 4 * Real.pi ^ 2 * (1 / 3) := by gcongr
              _ = (2 * Real.pi) ^ 2 / 3 := by ring
          have hsq := Real.sqrt_le_sqrt harg_le
          rw [Real.sqrt_sq (by positivity)] at hsq
          calc 2 * Real.sqrt (4 * Real.pi ^ 2 * (c' / 12) * t)
              ≤ 2 * (2 * Real.pi / Real.sqrt 3) := by gcongr
            _ = 4 * Real.pi / Real.sqrt 3 := by ring
        exact h1'.trans (Real.exp_le_exp.mpr hsqrt_le)
      calc (2 * Real.pi * t) ^ (prob.w - 1) * besselS (prob.w - 1) (4 * Real.pi ^ 2 * (c' / 12) * t)
          ≤ (2 * Real.pi * t) ^ (prob.w - 1) * Real.exp (4 * Real.pi / Real.sqrt 3) := by gcongr
        _ = C_ker * t ^ (prob.w - 1) := by dsimp [C_ker]; rw [mul_pow]; ring
    calc |g t| * kernelK prob.w (c' / 12) t ≤ |g t| * (C_ker * t ^ (prob.w - 1)) := by gcongr
      _ = C_ker * (|g t| * t ^ (prob.w - 1)) := by ring
  have hint_head : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (c' / 12) t) (Ioc 0 (4 / c')) := by
    refine ((hA_int.mono_set Ioc_subset_Ioi_self).const_mul C_ker).mono' (haesm.mono_set Ioc_subset_Ioi_self)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hhead_dom))
  have htail_dom : ∀ t ∈ Ioi (4 / c'),
      ‖|g t| * kernelK prob.w (c' / 12) t‖ ≤
        (C_K * c' ^ (prob.m : ℝ)) * (|g t| * prob.cardyV (c' / 12) t) := by
    intro t ht
    have ht0 : 0 ≤ t := (h4_pos.trans ht).le
    have hK_nn : 0 ≤ kernelK prob.w (c' / 12) t := kernelK_nonneg (by positivity) ht0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hK_nn)]
    have hbd := hK_bd hc' (mem_Ioi.mp ht).le
    calc |g t| * kernelK prob.w (c' / 12) t
        ≤ |g t| * (C_K * c' ^ (prob.m : ℝ) * prob.cardyV (c' / 12) t) := by gcongr
      _ = (C_K * c' ^ (prob.m : ℝ)) * (|g t| * prob.cardyV (c' / 12) t) := by ring
  have hint_tail : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (c' / 12) t) (Ioi (4 / c')) := by
    refine ((hg.int_cardy.mono_set (Ioi_subset_Ioi h4_pos.le)).const_mul (C_K * c' ^ (prob.m : ℝ))).mono'
      (haesm.mono_set (Ioi_subset_Ioi h4_pos.le))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall htail_dom))
  have hint_all : IntegrableOn (fun t : ℝ => |g t| * kernelK prob.w (c' / 12) t) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi h4_pos.le]
    exact hint_head.union hint_tail
  refine ⟨hint_all, ?_⟩
  have hsplit : ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t =
      (∫ t in Ioc 0 (4 / c'), |g t| * kernelK prob.w (c' / 12) t) +
      (∫ t in Ioi (4 / c'), |g t| * kernelK prob.w (c' / 12) t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_head hint_tail,
      Ioc_union_Ioi_eq_Ioi h4_pos.le]
  have hhead_le : ∫ t in Ioc 0 (4 / c'), |g t| * kernelK prob.w (c' / 12) t ≤
      C_head * prob.cardyNorm (c' / 12) g := by
    have h1 : ∫ t in Ioc 0 (4 / c'), |g t| * kernelK prob.w (c' / 12) t ≤
        ∫ t in Ioc 0 (4 / c'), C_ker * (|g t| * t ^ (prob.w - 1)) := by
      refine setIntegral_mono_on hint_head ((hA_int.mono_set Ioc_subset_Ioi_self).const_mul C_ker)
        measurableSet_Ioc fun t ht => ?_
      have := hhead_dom t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (kernelK_nonneg (by positivity) ht.1.le))] at this
    have h2 : ∫ t in Ioc 0 (4 / c'), C_ker * (|g t| * t ^ (prob.w - 1)) ≤
        C_ker * ∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine setIntegral_mono_set hA_int ?_ Ioc_subset_Ioi_self.eventuallySubset
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (pow_nonneg (mem_Ioi.mp ht).le _))
    calc ∫ t in Ioc 0 (4 / c'), |g t| * kernelK prob.w (c' / 12) t
        ≤ C_ker * ∫ t in Ioi (0 : ℝ), |g t| * t ^ (prob.w - 1) := h1.trans h2
      _ ≤ C_ker * (C_int * prob.cardyNorm (c' / 12) g) := by
          exact mul_le_mul_of_nonneg_left hwin_bd.1 (by positivity)
      _ = C_head * prob.cardyNorm (c' / 12) g := by dsimp [C_head]; ring
  have htail_le : ∫ t in Ioi (4 / c'), |g t| * kernelK prob.w (c' / 12) t ≤
      (C_K * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g := by
    have h1 : ∫ t in Ioi (4 / c'), |g t| * kernelK prob.w (c' / 12) t ≤
        ∫ t in Ioi (4 / c'), (C_K * c' ^ (prob.m : ℝ)) * (|g t| * prob.cardyV (c' / 12) t) := by
      refine setIntegral_mono_on hint_tail
        ((hg.int_cardy.mono_set (Ioi_subset_Ioi h4_pos.le)).const_mul _)
        measurableSet_Ioi fun t ht => ?_
      have := htail_dom t ht
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
        (kernelK_nonneg (by positivity) (h4_pos.trans ht).le))] at this
    have h2 : ∫ t in Ioi (4 / c'), (C_K * c' ^ (prob.m : ℝ)) * (|g t| * prob.cardyV (c' / 12) t) ≤
        (C_K * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold FixedWeightProblem.cardyNorm
      refine setIntegral_mono_set hg.int_cardy ?_ (Ioi_subset_Ioi h4_pos.le).eventuallySubset
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha_ge (mem_Ioi.mp ht).le))
    exact h1.trans h2
  have hM_nn : 0 ≤ prob.cardyNorm (c' / 12) g :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha_ge (mem_Ioi.mp ht).le)
  have hC_head_le : C_head * prob.cardyNorm (c' / 12) g ≤
      (C_head * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g := by
    calc C_head * prob.cardyNorm (c' / 12) g
        = (C_head * 1) * prob.cardyNorm (c' / 12) g := by ring
      _ ≤ (C_head * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g := by gcongr
  calc ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t
      = (∫ t in Ioc 0 (4 / c'), |g t| * kernelK prob.w (c' / 12) t) +
          (∫ t in Ioi (4 / c'), |g t| * kernelK prob.w (c' / 12) t) := hsplit
    _ ≤ C_head * prob.cardyNorm (c' / 12) g + (C_K * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g :=
        add_le_add hhead_le htail_le
    _ ≤ (C_head * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g +
          (C_K * c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g :=
        add_le_add hC_head_le le_rfl
    _ = C_Kint * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g := by dsimp [C_Kint]; ring

theorem hankelContinuationW_integrable (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
        ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
          IntegrableOn (fun t : ℝ => (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)) (Ioi 0) := by
  obtain ⟨_, c₀, _, hc₀_ge, hK⟩ := testClass_integral_kernelK_le prob
  refine ⟨c₀, hc₀_ge, fun {c' g} hc' hg {b} hb => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  have hint := (hK hc' hg).1
  refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · have hcont : ContinuousOn (fun t : ℝ => (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)) (Ioi 0) :=
      (Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
        ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_kernelKC_strip_le prob.w prob.hw hc'_pos (mem_Ioi.mp ht).le hb) (abs_nonneg _)

/-- **Lemma 4(a), strip bound (`n1:L4`, `(W1)`, `(P0)`)**:
for `c' ≥ c₀` (`c₀ ≥ max 1 (24 S)`), `g ∈ TestClass prob (c'/12) g`, and `|Im b| ≤ 1/2`,
`‖hankelContinuationW prob.w c' g b‖ ≤ C_e * c'^m * M[g]` and
`‖hankelContinuationW prob.w c' g b‖ ≤ C_e * (1 + c'^m) * M[g]`. -/
theorem hankelContinuationW_strip_bound (prob : FixedWeightProblem) :
    ∃ C_e c₀ : ℝ, 0 < C_e ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
        ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
          ‖hankelContinuationW prob.w c' g b‖ ≤ C_e * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g ∧
          ‖hankelContinuationW prob.w c' g b‖ ≤
            C_e * (1 + c' ^ (prob.m : ℝ)) * prob.cardyNorm (c' / 12) g := by
  obtain ⟨C_Kint, c₀, hCK_pos, hc₀_ge, hK⟩ := testClass_integral_kernelK_le prob
  refine ⟨2 * Real.pi * C_Kint, c₀, by positivity, hc₀_ge, fun {c' g} hc' hg {b} hb => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  obtain ⟨hint, hbd⟩ := hK hc' hg
  have hM_nn : 0 ≤ prob.cardyNorm (c' / 12) g :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg (by linarith [(le_max_right (1 : ℝ) (24 * prob.totalShift)).trans hcm, prob.totalShift_nonneg]) (mem_Ioi.mp ht).le)
  have hnorm_int : ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖ ≤
      ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t := by
    calc ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖(g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t := by
          refine setIntegral_mono_on ?_ hint measurableSet_Ioi fun t ht => ?_
          · have hintc : IntegrableOn (fun t : ℝ => (g t : ℂ) *
                kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)) (Ioi 0) := by
              refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
              · exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
                  ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
                  measurableSet_Ioi
              · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                exact mul_le_mul_of_nonneg_left
                  (norm_kernelKC_strip_le prob.w prob.hw hc'_pos (mem_Ioi.mp hs).le hb) (abs_nonneg _)
            exact hintc.norm
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left
              (norm_kernelKC_strip_le prob.w prob.hw hc'_pos (mem_Ioi.mp ht).le hb) (abs_nonneg _)
  have hmain : ‖hankelContinuationW prob.w c' g b‖ ≤
      (2 * Real.pi * C_Kint) * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g := by
    unfold hankelContinuationW
    rw [norm_mul, show (-2 * (Real.pi : ℂ) : ℂ) = ((-(2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    calc 2 * Real.pi * ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖
        ≤ 2 * Real.pi * ∫ t in Ioi (0 : ℝ), |g t| * kernelK prob.w (c' / 12) t := by gcongr
      _ ≤ 2 * Real.pi * (C_Kint * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g) := by gcongr
      _ = 2 * Real.pi * C_Kint * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g := by ring
  refine ⟨hmain, hmain.trans ?_⟩
  have h1c : c' ^ (prob.m : ℝ) ≤ 1 + c' ^ (prob.m : ℝ) := le_add_of_nonneg_left zero_le_one
  gcongr

theorem continuousOn_hankelContinuationW (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
        ContinuousOn (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| ≤ 1 / 2} := by
  obtain ⟨_, c₀, _, hc₀_ge, hK⟩ := testClass_integral_kernelK_le prob
  refine ⟨c₀, hc₀_ge, fun {c' g} hc' hg b₀ hb₀ => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  have hint := (hK hc' hg).1
  unfold hankelContinuationW
  refine ContinuousWithinAt.mul continuousWithinAt_const ?_
  let F : ℂ → ℝ → ℂ := fun b t => (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)
  refine continuousWithinAt_of_dominated (bound := fun t => |g t| * kernelK prob.w (c' / 12) t) ?_ ?_ hint ?_
  · refine Eventually.of_forall fun b => ?_
    exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
      ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  · rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall fun b hb => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_kernelKC_strip_le prob.w prob.hw hc'_pos (mem_Ioi.mp ht).le hb) (abs_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : Continuous fun b : ℂ => kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ) :=
      (kernelKC_entire_alpha prob.w (t : ℂ)).continuous.comp (by fun_prop)
    exact (continuous_const.mul h1).continuousAt

/-! ### Section 3: Holomorphy on `{b : ℂ | |b.im| < 1/2}` -/

private lemma one_add_mul_besselS_le (n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ {u : ℝ}, 0 ≤ u → (u + 1) * besselS n (q * u) ≤ M * besselS n u := by
  have htend : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * q ^ k) atTop (𝓝 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
    have h0 : Tendsto (fun j : ℕ => ((j + 1 + n : ℕ) : ℝ) ^ 2 * q ^ j) atTop (𝓝 0) := by
      have hshift : Tendsto (fun j : ℕ => ((j + (1 + n) : ℕ) : ℝ) ^ 2 * q ^ (j + (1 + n))) atTop (𝓝 0) :=
        h2.comp (tendsto_add_atTop_nat (1 + n))
      by_cases hq0' : q = 0
      · subst hq0'
        refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun j hj => ?_)
        simp [Nat.ne_of_gt hj]
      · have hpow_ne : q ^ (1 + n) ≠ 0 := pow_ne_zero _ hq0'
        have hdiv := hshift.div_const (q ^ (1 + n))
        rw [zero_div] at hdiv
        refine hdiv.congr fun j => ?_
        rw [pow_add q j (1 + n), ← mul_assoc, mul_div_cancel_right₀ _ hpow_ne, add_assoc]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun j => by positivity) (fun j => ?_)
    have hle : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 + n : ℕ) : ℝ) := by push_cast; linarith
    calc ((j + 1 : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j
        ≤ ((j + 1 + n : ℕ) : ℝ) * ((j + 1 + n : ℕ) : ℝ) * q ^ j := by gcongr
      _ = ((j + 1 + n : ℕ) : ℝ) ^ 2 * q ^ j := by ring
  obtain ⟨M₀, hM₀⟩ := htend.bddAbove_range
  let M₁ : ℝ := max 1 M₀
  have hM₁_pos : 0 < M₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨M₁ + 1, by positivity, fun {u} hu => ?_⟩
  have hj_bd : ∀ j : ℕ, ((j + 1 : ℝ) * (j + 1 + n : ℝ) * q ^ j) ≤ M₁ := fun j => by
    have h1 := hM₀ ⟨j, rfl⟩
    push_cast at h1
    exact h1.trans (le_max_right _ _)
  have hS0 : Summable fun j : ℕ => u * besselTerm n (q * u) j :=
    (summable_besselTerm n (mul_nonneg hq0 hu)).mul_left u
  have hSn_shift : Summable fun j : ℕ => M₁ * besselTerm n u (j + 1) :=
    ((summable_nat_add_iff 1).mpr (summable_besselTerm n hu)).mul_left M₁
  have hterm : ∀ j : ℕ, u * besselTerm n (q * u) j ≤ M₁ * besselTerm n u (j + 1) := by
    intro j
    unfold besselTerm
    have hj_ne : ((j + 1)! : ℝ) ≠ 0 := by positivity
    have hjn_ne : ((j + 1 + n)! : ℝ) ≠ 0 := by positivity
    have hid : u * ((q * u) ^ j / ((j ! : ℝ) * ((j + n)! : ℝ))) =
        ((j + 1 : ℝ) * (j + 1 + n : ℝ) * q ^ j) *
          (u ^ (j + 1) / (((j + 1)! : ℝ) * ((j + 1 + n)! : ℝ))) := by
      have hjf : ((j + 1)! : ℝ) = (j + 1 : ℝ) * (j ! : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      have hjnf : ((j + 1 + n)! : ℝ) = (j + 1 + n : ℝ) * ((j + n)! : ℝ) := by
        rw [show j + 1 + n = (j + n) + 1 by ring, Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
      rw [mul_pow, pow_succ u j]
      field_simp [hj_ne, hjn_ne]
      rw [hjf, hjnf]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right (hj_bd j) (by positivity)
  have hle_sum : u * besselS n (q * u) ≤ M₁ * ∑' j : ℕ, besselTerm n u (j + 1) := by
    unfold besselS
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact hS0.tsum_le_tsum hterm hSn_shift
  have htail : ∑' j : ℕ, besselTerm n u (j + 1) ≤ besselS n u := by
    unfold besselS
    have hsum := summable_besselTerm n hu
    have hsp := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hsp
    have h0_nn : 0 ≤ besselTerm n u 0 := by unfold besselTerm; positivity
    linarith
  have hu_le : u * besselS n (q * u) ≤ M₁ * besselS n u :=
    hle_sum.trans (mul_le_mul_of_nonneg_left htail hM₁_pos.le)
  have h1_le : besselS n (q * u) ≤ besselS n u :=
    besselS_mono n (mul_nonneg hq0 hu) (mul_le_of_le_one_left hu hq1.le)
  linarith

private lemma continuous_besselSCSqDeriv (n : ℕ) : Continuous (besselSCSqDeriv n) := by
  have hdiff : Differentiable ℂ (besselSCSqDeriv n) := fun z₀ => by
    let F : ℂ → ℝ → ℂ := fun z θ =>
      (Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ)) * ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)
    let F' : ℂ → ℝ → ℂ := fun z θ =>
      (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) * Complex.exp (z * (Real.cos θ : ℝ))) *
        ((Real.sin θ ^ (2 * n) : ℝ) : ℂ)
    have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℂ) (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ 1)
      (a := 0) (b := Real.pi) (Metric.ball_mem_nhds z₀ one_pos)
      (Eventually.of_forall fun z => (by fun_prop : Continuous (F z)).aestronglyMeasurable)
      ((by fun_prop : Continuous (F z₀)).intervalIntegrable 0 Real.pi)
      (by fun_prop : Continuous (F' z₀)).aestronglyMeasurable
      (Eventually.of_forall fun θ _ z hz => by
        dsimp [F']
        have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
        have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
        have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
          have hball : ‖z - z₀‖ < 1 := dist_eq_norm z z₀ ▸ Metric.mem_ball.mp hz
          calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
            _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
            _ ≤ 1 + ‖z₀‖ := by linarith
            _ = ‖z₀‖ + 1 := by ring
        have hre : (z * (Real.cos θ : ℝ)).re ≤ ‖z₀‖ + 1 := by
          calc (z * (Real.cos θ : ℝ)).re ≤ ‖z * (Real.cos θ : ℝ)‖ := Complex.re_le_norm _
            _ = ‖z‖ * |Real.cos θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            _ ≤ ‖z₀‖ + 1 := by nlinarith [norm_nonneg z]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_pow]
        have hs1 : |Real.sin θ| ^ (2 * n) ≤ 1 := pow_le_one₀ (abs_nonneg _) hsin
        calc |Real.cos θ| * (|Real.cos θ| * Real.exp (z * (Real.cos θ : ℝ)).re) * |Real.sin θ| ^ (2 * n)
            ≤ 1 * (1 * Real.exp (‖z₀‖ + 1)) * 1 := by gcongr
          _ = Real.exp (‖z₀‖ + 1) := by ring)
      (intervalIntegrable_const (μ := volume))
      (Eventually.of_forall fun θ _ z _ => by
        dsimp [F, F']
        have hd := ((((hasDerivAt_id z).mul_const (Real.cos θ : ℂ)).cexp.const_mul
          (Real.cos θ : ℂ)).mul_const ((Real.sin θ ^ (2 * n) : ℝ) : ℂ))
        refine hd.congr_deriv ?_
        dsimp only [id_eq]; ring)
    exact (hint.2.const_mul ((((n ! : ℝ) * sinEvenIntegral n : ℝ) : ℂ)⁻¹)).differentiableAt
  exact hdiff.continuous

theorem differentiableOn_hankelContinuationW (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
        DifferentiableOn ℂ (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| < 1 / 2} := by
  have hw := prob.hw
  obtain ⟨_, c₀, _, hc₀_ge, hK⟩ := testClass_integral_kernelK_le prob
  refine ⟨c₀, hc₀_ge, fun {c' g} hc' hg b₀ hb₀ => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
  have hint := (hK hc' hg).1
  let r : ℝ := (|b₀.im| + 1 / 2) / 2
  have hr_gt : |b₀.im| < r := by dsimp [r]; linarith [show |b₀.im| < 1 / 2 from hb₀]
  have hr_lt : r < 1 / 2 := by dsimp [r]; linarith [show |b₀.im| < 1 / 2 from hb₀]
  have hr_nn : 0 ≤ r := le_trans (abs_nonneg _) hr_gt.le
  let q : ℝ := 4 * r ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp [q]; nlinarith [hr_nn, hr_lt]
  obtain ⟨M_b, hMb_pos, hMb⟩ := one_add_mul_besselS_le (prob.w - 1) hq0 hq1
  let δ : ℝ := min (r - |b₀.im|) 1
  have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hr_gt) zero_lt_one
  let C_dom : ℝ := 2 * M_b
  let F : ℂ → ℝ → ℂ := fun b t => (g t : ℂ) * kernelKC prob.w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)
  let zFun : ℂ → ℝ → ℂ := fun b t =>
    4 * (Real.pi : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ)
  let F' : ℂ → ℝ → ℂ := fun b t =>
    (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
      (besselSCSqDeriv (prob.w - 1) (zFun b t) *
        (4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ))))
  have hball_bd : ∀ b ∈ Metric.ball b₀ δ, |b.im| ≤ r := fun b hb => by
    have hdist : ‖b - b₀‖ < δ := dist_eq_norm b b₀ ▸ Metric.mem_ball.mp hb
    have him : |b.im - b₀.im| ≤ ‖b - b₀‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - b₀)
    calc |b.im| = |(b.im - b₀.im) + b₀.im| := by ring_nf
      _ ≤ |b.im - b₀.im| + |b₀.im| := abs_add_le _ _
      _ ≤ δ + |b₀.im| := by linarith
      _ ≤ (r - |b₀.im|) + |b₀.im| := by gcongr; exact min_le_left _ _
      _ = r := by ring
  have hF_meas : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable (F b) (volume.restrict (Ioi 0)) := by
    refine Eventually.of_forall fun b => ?_
    exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
      ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  have hF_int : Integrable (F b₀) (volume.restrict (Ioi 0)) := by
    refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    · exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul
        ((kernelKC_entire_t prob.w _).continuous.comp Complex.continuous_ofReal).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · dsimp [F]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelKC_strip_le prob.w prob.hw hc'_pos (mem_Ioi.mp ht).le (le_trans hr_gt.le hr_lt.le))
        (abs_nonneg _)
  have hF'_meas : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi 0)) := by
    have hcont_sq : Continuous fun t : ℝ => besselSCSqDeriv (prob.w - 1) (zFun b₀ t) :=
      (continuous_besselSCSqDeriv (prob.w - 1)).comp (by fun_prop)
    have hcont_rest : ContinuousOn (fun t : ℝ =>
        (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
          (besselSCSqDeriv (prob.w - 1) (zFun b₀ t) *
            (4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)))) (Ioi 0) :=
      (((continuous_const.mul Complex.continuous_ofReal).pow (prob.w - 1)).mul
        (hcont_sq.mul (continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))))).continuousOn
    exact ((Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)).mul hcont_rest).aestronglyMeasurable
      measurableSet_Ioi
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δ,
      ‖F' b t‖ ≤ C_dom * (|g t| * kernelK prob.w (c' / 12) t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht b hb => ?_)
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hbim := hball_bd b hb
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow,
      show 2 * (Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * t), norm_mul]
    have hz_re : (zFun b t).re = -(4 * Real.pi * b.im * Real.sqrt (c' * t / 3)) := by
      dsimp [zFun]; simp [Complex.mul_re, Complex.mul_im]
    have hre_le : (zFun b t).re ^ 2 / 4 ≤ q * (4 * Real.pi ^ 2 * (c' / 12) * t) := by
      rw [hz_re]
      have hsq : Real.sqrt (c' * t / 3) ^ 2 = c' * t / 3 := Real.sq_sqrt (by positivity)
      have hb_sq : b.im ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs b.im]; exact pow_le_pow_left₀ (abs_nonneg _) hbim 2
      calc (-(4 * Real.pi * b.im * Real.sqrt (c' * t / 3))) ^ 2 / 4
          = 4 * Real.pi ^ 2 * (Real.sqrt (c' * t / 3)) ^ 2 * b.im ^ 2 := by ring
        _ = 4 * Real.pi ^ 2 * (c' * t / 3) * b.im ^ 2 := by rw [hsq]
        _ ≤ 4 * Real.pi ^ 2 * (c' * t / 3) * r ^ 2 := by gcongr
        _ = q * (4 * Real.pi ^ 2 * (c' / 12) * t) := by dsimp [q]; ring
    let u : ℝ := 4 * Real.pi ^ 2 * (c' / 12) * t
    have hu_nn : 0 ≤ u := by dsimp [u]; positivity
    have hderiv_sq : ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ ≤ besselS (prob.w - 1) (q * u) :=
      (besselSCSqDeriv_norm_le (prob.w - 1) (zFun b t)).trans (besselS_mono (prob.w - 1) (by positivity) hre_le)
    have hc_n : ‖4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)‖ ≤ 2 * (u + 1) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have hsq_u : (2 * Real.pi * Real.sqrt (c' * t / 3)) ^ 2 = 4 * u := by
        dsimp [u]
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        ring
      have hsqrt_le : 2 * Real.pi * Real.sqrt (c' * t / 3) ≤ u + 1 := by
        nlinarith [sq_nonneg (2 * Real.pi * Real.sqrt (c' * t / 3) - 2), hsq_u]
      linarith
    have hK_eq : kernelK prob.w (c' / 12) t = (2 * Real.pi * t) ^ (prob.w - 1) * besselS (prob.w - 1) u := by
      unfold kernelK besselS besselTerm kernelKTerm
      congr 1; refine tsum_congr fun j => ?_; rw [show j + prob.w - 1 = j + (prob.w - 1) by omega]
    have hb_nn : 0 ≤ besselS (prob.w - 1) (q * u) := by
      unfold besselS; exact tsum_nonneg fun _ => by unfold besselTerm; positivity
    have hprod_le : ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
          ‖4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)‖ ≤
        M_b * (2 * besselS (prob.w - 1) u) := by
      calc ‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
            ‖4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)‖
          ≤ besselS (prob.w - 1) (q * u) * (2 * (u + 1)) :=
            mul_le_mul hderiv_sq hc_n (norm_nonneg _) hb_nn
        _ = 2 * ((u + 1) * besselS (prob.w - 1) (q * u)) := by ring
        _ ≤ 2 * (M_b * besselS (prob.w - 1) u) := mul_le_mul_of_nonneg_left (hMb hu_nn) (by norm_num)
        _ = M_b * (2 * besselS (prob.w - 1) u) := by ring
    calc |g t| * ((2 * Real.pi * t) ^ (prob.w - 1) *
            (‖besselSCSqDeriv (prob.w - 1) (zFun b t)‖ *
              ‖4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)‖))
        ≤ |g t| * ((2 * Real.pi * t) ^ (prob.w - 1) * (M_b * (2 * besselS (prob.w - 1) u))) := by
          gcongr
      _ = C_dom * (|g t| * ((2 * Real.pi * t) ^ (prob.w - 1) * besselS (prob.w - 1) u)) := by
          dsimp [C_dom]; ring
      _ = C_dom * (|g t| * kernelK prob.w (c' / 12) t) := by rw [← hK_eq]
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ Metric.ball b₀ δ,
      HasDerivAt (fun b => F b t) (F' b t) b := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht b _ => ?_)
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hz_deriv : HasDerivAt (fun b : ℂ => zFun b t)
        (4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)) b := by
      have hid : (fun b : ℂ => zFun b t) = fun b : ℂ =>
          b * (4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ)) := by
        ext w; dsimp [zFun]; ring
      rw [hid]
      simpa using (hasDerivAt_id b).mul_const _
    have hS_deriv : HasDerivAt ((fun z : ℂ => besselSC (prob.w - 1) (z ^ 2 / 4)) ∘ fun b : ℂ => zFun b t)
        (besselSCSqDeriv (prob.w - 1) (zFun b t) *
          (4 * (Real.pi : ℂ) * Complex.I * (Real.sqrt (c' * t / 3) : ℝ))) b :=
      (hasDerivAt_besselSC_sq_div_four (prob.w - 1) (zFun b t)).comp b hz_deriv
    have hS_eq : (fun b : ℂ => besselSC (prob.w - 1) (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ))) =
        fun b : ℂ => besselSC (prob.w - 1) ((zFun b t) ^ 2 / 4) := by
      ext w
      congr 1
      dsimp [zFun]
      have hsq : ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 = ((c' * t / 3 : ℝ) : ℂ) := by
        exact_mod_cast Real.sq_sqrt (by positivity)
      calc 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * w ^ 2 / 3) * (t : ℂ)
          = (4 * (Real.pi : ℂ) * Complex.I * w) ^ 2 * ((c' * t / 3 : ℝ) : ℂ) / 4 := by
            rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]; push_cast; ring
        _ = (4 * (Real.pi : ℂ) * Complex.I * w) ^ 2 * ((Real.sqrt (c' * t / 3) : ℝ) : ℂ) ^ 2 / 4 := by
            rw [hsq]
        _ = _ := by ring
    have hK_eq_fn : (fun b : ℂ => F b t) = fun b : ℂ =>
        (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
          besselSC (prob.w - 1) ((zFun b t) ^ 2 / 4)) := by
      ext w; dsimp [F, kernelKC]
      exact congrArg (fun x => (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (prob.w - 1) * x))
        (congrFun hS_eq w)
    rw [hK_eq_fn]
    have hK_deriv : HasDerivAt
        (fun b : ℂ => (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (prob.w - 1) *
          besselSC (prob.w - 1) ((zFun b t) ^ 2 / 4)))
        (F' b t) b := by
      dsimp [F']
      exact (hS_deriv.const_mul _).const_mul (g t : ℂ)
    exact hK_deriv
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hδ_pos)
    hF_meas hF_int hF'_meas h_bound (hint.const_mul C_dom) h_diff).2
  unfold hankelContinuationW
  exact (hd.const_mul (-2 * (Real.pi : ℂ))).differentiableAt.differentiableWithinAt

/-! ### Section 4: Agreement on `ℝ` (`hankelContinuationW_ofReal`) for every `w ≥ 1` -/

private lemma sphere_const_cancel (k : ℕ) :
    (2 * k + 1 : ℝ) * (Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ)) *
      ((k ! : ℝ) * sinEvenIntegral k) = 2 * Real.pi ^ (k + 1) := by
  rw [sinEvenIntegral_eq]
  have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * k)
  rw [Nat.doubleFactorial_two_mul] at hfac
  have hfac_cast : (((2 * k + 1)! : ℕ) : ℝ) = ((2 * k + 1 : ℕ)‼ : ℝ) * ((2 : ℝ) ^ k * (k ! : ℝ)) := by
    exact_mod_cast hfac
  have hfac_succ : (((2 * k + 1)! : ℕ) : ℝ) = (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) = ((2 * k + 1 : ℕ)‼ : ℝ) * ((2 : ℝ) ^ k * (k ! : ℝ)) := by
    linarith [hfac_cast, hfac_succ]
  have hdd_ne : ((2 * k + 1 : ℕ)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * k + 1)).ne'
  have hk_ne : (k ! : ℝ) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
  rw [h4]
  field_simp [hdd_ne, hk_ne]
  calc (2 * (k : ℝ) + 1) * Real.pi ^ k * 2 ^ (k + 1) * Real.pi * ((2 * k)! : ℝ)
      = Real.pi ^ (k + 1) * 2 ^ (k + 1) * ((2 * (k : ℝ) + 1) * ((2 * k)! : ℝ)) := by
          rw [pow_succ Real.pi k]; ring
    _ = Real.pi ^ (k + 1) * 2 ^ (k + 1) * (((2 * k + 1 : ℕ)‼ : ℝ) * (2 ^ k * (k ! : ℝ))) := by
          rw [h1]
    _ = 2 * ((2 * k + 1 : ℕ)‼ : ℝ) * (k ! : ℝ) * (2 ^ k) ^ 2 * Real.pi ^ (k + 1) := by
          rw [pow_succ (2 : ℝ) k]; ring

private noncomputable def splitEuclideanEquiv (w : ℕ) (hw : 1 ≤ w) :
    EuclideanSpace ℝ (Fin (2 * w)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin (2 * (w - 1) + 1)) :=
  let hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
  (MeasurableEquiv.toLp 2 (Fin (2 * w) → ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (finCongr hdim)).trans
      ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.toLp 2 (Fin (2 * (w - 1) + 1) → ℝ)))))

private lemma measurePreserving_splitEuclideanEquiv (w : ℕ) (hw : 1 ≤ w) :
    MeasurePreserving (splitEuclideanEquiv w hw) volume volume := by
  unfold splitEuclideanEquiv
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2 * w))).trans ?_
  refine (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℝ) _).trans ?_
  refine (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (2 * (w - 1) + 1 + 1) => ℝ) 0).trans ?_
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (μ := volume)).prod (PiLp.volume_preserving_toLp (Fin (2 * (w - 1) + 1)))

private lemma splitEuclideanEquiv_symm_apply_eq {w : ℕ} (hw : 1 ≤ w)
    (hdim : 2 * w = (2 * (w - 1) + 1) + 1) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) (j : Fin (2 * w)) :
    ((splitEuclideanEquiv w hw).symm (u, y)) j =
      @Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) (finCongr hdim j) := by
  rfl

private lemma splitEuclideanEquiv_symm_norm_sq {w : ℕ} (hw : 1 ≤ w) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) :
    ‖(splitEuclideanEquiv w hw).symm (u, y)‖ ^ 2 = u ^ 2 + ‖y‖ ^ 2 := by
  let hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
  have hnorm_sum : ∀ (v : EuclideanSpace ℝ (Fin (2 * w))),
      ‖v‖ ^ 2 = ∑ i : Fin (2 * w), (v i) ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm_sum, EuclideanSpace.norm_sq_eq]
  have hmap : ∑ j : Fin (2 * w), (((splitEuclideanEquiv w hw).symm (u, y)) j) ^ 2 =
      ∑ i : Fin (2 * (w - 1) + 1 + 1),
        (@Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) i) ^ 2 := by
    have hpt : ∀ j : Fin (2 * w),
        (((splitEuclideanEquiv w hw).symm (u, y)) j) ^ 2 =
          (@Fin.insertNth (2 * (w - 1) + 1) (fun _ => ℝ) 0 u (fun m => y m) (finCongr hdim j)) ^ 2 :=
      fun j => by rw [splitEuclideanEquiv_symm_apply_eq hw hdim]
    simp_rw [hpt]
    exact Fintype.sum_equiv (finCongr hdim) _ _ fun j => rfl
  rw [hmap, Fin.sum_univ_succ]
  simp only [Fin.insertNth_apply_same, ← Fin.succAbove_zero, Fin.insertNth_apply_succAbove,
    Real.norm_eq_abs, sq_abs]

private lemma splitEuclideanEquiv_symm_inner {w : ℕ} (hw : 1 ≤ w) (u : ℝ)
    (y : EuclideanSpace ℝ (Fin (2 * (w - 1) + 1))) (r : ℝ) :
    let i0 : Fin (2 * w) := ⟨0, by omega⟩
    inner ℝ ((splitEuclideanEquiv w hw).symm (u, y)) (EuclideanSpace.single i0 r) = u * r := by
  intro i0
  rw [EuclideanSpace.inner_single_right]
  have hi0 : ((splitEuclideanEquiv w hw).symm (u, y)) i0 = u := by
    have hdim : 2 * w = (2 * (w - 1) + 1) + 1 := by omega
    rw [splitEuclideanEquiv_symm_apply_eq hw hdim]
    have h0 : finCongr hdim i0 = 0 := Fin.ext rfl
    rw [h0, Fin.insertNth_apply_same]
  simp [hi0, mul_comm]

private lemma setIntegral_polarCoord_Ioi (H : ℝ × ℝ → ℂ)
    (hH : IntegrableOn H ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ))) (hH_cont : Continuous H) :
    (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ s in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi,
        s • H (s * Real.cos θ, s * Real.sin θ) := by
  have h1 : (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ p : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H p :=
    (integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) (f := H)).symm
  rw [h1, ← integral_comp_polarCoord_symm (((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)]
  have hpt : EqOn
      (fun p : ℝ × ℝ => p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator H (polarCoord.symm p))
      (Set.indicator (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi)
        (fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)))
      polarCoord.target := by
    intro p hp
    rcases hp with ⟨hs, hθ⟩
    simp only [polarCoord_symm_apply]
    by_cases hθ0 : p.2 ∈ Ioo (0 : ℝ) Real.pi
    · have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0.2
      have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) :=
        ⟨trivial, mul_pos hs hsin⟩
      have hmem2 : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := ⟨hs, hθ0⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2]
    · have hnot : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
        intro hmem
        have hsin : 0 < Real.sin p.2 := pos_of_mul_pos_right hmem.2 (mem_Ioi.mp hs).le
        have hlt : 0 < p.2 := by
          by_contra hle
          push Not at hle
          have : Real.sin p.2 ≤ 0 := by
            rcases eq_or_lt_of_le hle with h0 | hneg
            · rw [h0]; simp
            · rw [← neg_neg p.2, Real.sin_neg]
              exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hθ.1])).le
          linarith
        exact hθ0 ⟨hlt, hθ.2⟩
      rw [Set.indicator_of_notMem hnot, smul_zero, Set.indicator_of_notMem (fun h : p ∈ (_ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi => hθ0 h.2)]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setIntegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have hsub : polarCoord.target ∩ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) =
      Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := by
    refine inter_eq_right.mpr fun p hp => ⟨hp.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
  rw [hsub]
  have hint_pol : IntegrableOn
      (fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) := by
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun p : ℝ × ℝ => p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2) :=
        continuous_fst.smul (hH_cont.comp (by fun_prop))
      exact hcont.continuousOn.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioo)
    · have h_lin := lintegral_comp_polarCoord_symm
        (fun q => (((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞)) q))
      have h_fin_tar : (∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
            (polarCoord.symm p)) < ⊤ := by
        rw [h_lin]
        calc ∫⁻ q : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞)) q
            = ∫⁻ q in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H q‖₊ : ℝ≥0∞) :=
              lintegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) _
          _ < ⊤ := hH.2
      have h_sub_le : ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            (‖p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) ≤
          ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
              (polarCoord.symm p) := by
        calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
              (‖p.1 • H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞)
            = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal p.1 • ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun z => (‖H z‖₊ : ℝ≥0∞))
                  (polarCoord.symm p) := by
              refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
              have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
              have hmem : polarCoord.symm p ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
                simp only [polarCoord_symm_apply]; exact ⟨trivial, mul_pos hp.1 hsin⟩
              rw [Set.indicator_of_mem hmem]
              simp only [polarCoord_symm_apply, nnNorm_smul, ENNReal.coe_mul,
                smul_eq_mul, Real.nnNorm_of_nonneg hp.1.le, ENNReal.ofReal_eq_coe_nnreal hp.1.le]
          _ ≤ _ := lintegral_mono_set (by rw [← hsub]; exact inter_subset_left)
      exact lt_of_le_of_lt h_sub_le h_fin_tar
  rw [Measure.volume_eq_prod] at hint_pol ⊢
  exact setIntegral_prod _ hint_pol

private lemma setIntegral_sq_div_two_Ioi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Φ : ℝ → F) :
    ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) = ∫ t in Ioi (0 : ℝ), Φ t := by
  have him : (fun s : ℝ => s ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨s, hs, rfl⟩; exact div_pos (sq_pos_of_pos hs) zero_lt_two
    · intro ht
      refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩
      dsimp only
      rw [Real.sq_sqrt (mul_pos zero_lt_two ht).le]; ring
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) s (Ioi 0) s := fun s _ => by
    have h1 := ((hasDerivAt_pow 2 s).div_const 2).hasDerivWithinAt (s := Ioi 0)
    simpa [Nat.cast_ofNat] using h1
  have hinj : InjOn (fun s : ℝ => s ^ 2 / 2) (Ioi 0) := fun x hx y hy hxy => by
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
    have hsq : x ^ 2 = y ^ 2 := by linarith
    nlinarith [sq_nonneg (x - y)]
  symm
  calc ∫ t in Ioi (0 : ℝ), Φ t
      = ∫ t in (fun s : ℝ => s ^ 2 / 2) '' Ioi 0, Φ t := by rw [him]
    _ = ∫ s in Ioi (0 : ℝ), |s| • Φ (s ^ 2 / 2) :=
        integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj Φ
    _ = ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [abs_of_pos hs]

theorem hankelContinuationW_ofReal {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g)) (b : ℝ) :
    hankelContinuationW w c' g (b : ℂ) = (g (c' * b ^ 2 / 3) : ℂ) := by
  let k : ℕ := w - 1
  let d : ℕ := 2 * k + 1
  let i0 : Fin (2 * w) := ⟨0, by omega⟩
  let r : ℝ := b * Real.sqrt (2 * c' / 3)
  let x₀ : EuclideanSpace ℝ (Fin (2 * w)) := EuclideanSpace.single i0 r
  have hx₀_sq : ‖x₀‖ ^ 2 / 2 = c' * b ^ 2 / 3 := by
    have hnorm : ‖x₀‖ = |r| := by simp [x₀]
    rw [hnorm, sq_abs]
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hfx₀ : radialLift w g x₀ = (g (c' * b ^ 2 / 3) : ℂ) := by
    simp only [radialLift, hx₀_sq]
  have hfour_eq : -(g (c' * b ^ 2 / 3) : ℂ) =
      ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) := by
    have hodd := congrFun hg_odd x₀
    simp only [Real.fourier_eq', Pi.neg_apply, smul_eq_mul] at hodd
    have hneg : -(g (c' * b ^ 2 / 3) : ℂ) = -(radialLift w g x₀) := by rw [← hfx₀]
    calc -(g (c' * b ^ 2 / 3) : ℂ) = -(radialLift w g x₀) := hneg
      _ = ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
            Complex.exp (((-2 * Real.pi * inner ℝ v x₀ : ℝ) : ℂ) * Complex.I) * (radialLift w g v) := hodd.symm
      _ = ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
            Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) := by
          refine integral_congr_ae (Eventually.of_forall fun v => ?_)
          dsimp only
          refine congrArg (· * radialLift w g v) (congrArg Complex.exp ?_)
          push_cast; ring
  have he_mp := measurePreserving_splitEuclideanEquiv w hw
  have hint_four : Integrable fun v : EuclideanSpace ℝ (Fin (2 * w)) =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) := by
    have haesm : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin (2 * w)) =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v)) volume := by
      have hlift : Continuous (radialLift w g) :=
        Complex.continuous_ofReal.comp
          (hg_cont.comp_continuous ((continuous_norm.pow 2).div_const 2) fun v =>
            mem_Ici.mpr (by positivity))
      exact ((Complex.continuous_exp.comp (by fun_prop)).mul hlift).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    have hfin := hg_int.hasFiniteIntegral
    refine lt_of_le_of_lt (lintegral_mono fun v => ?_) hfin
    rw [← ofReal_norm, ← ofReal_norm, norm_mul,
      show -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ) =
        ((-2 * Real.pi * inner ℝ v x₀ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hint_prod : Integrable fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) *
        (g ((p.1 ^ 2 + ‖p.2‖ ^ 2) / 2) : ℂ) := by
    refine ((he_mp.symm.integrable_comp_emb (splitEuclideanEquiv w hw).symm.measurableEmbedding).mpr
      hint_four).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Function.comp_apply, radialLift, x₀]
    rw [splitEuclideanEquiv_symm_norm_sq hw p.1 p.2, splitEuclideanEquiv_symm_inner hw p.1 p.2 r]
    push_cast; rfl
  have hstep1 : ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ v x₀ : ℂ)) * (radialLift w g v) =
      ∫ u : ℝ, ∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
          (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ) := by
    rw [← he_mp.symm.integral_comp']
    have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (inner ℝ ((splitEuclideanEquiv w hw).symm p) x₀ : ℂ)) *
          radialLift w g ((splitEuclideanEquiv w hw).symm p)) =
        fun p : ℝ × EuclideanSpace ℝ (Fin (2 * k + 1)) =>
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) *
            (g ((p.1 ^ 2 + ‖p.2‖ ^ 2) / 2) : ℂ) := by
      ext ⟨u, y⟩
      dsimp only [radialLift, x₀]
      rw [splitEuclideanEquiv_symm_norm_sq hw u y, splitEuclideanEquiv_symm_inner hw u y r]
      push_cast; rfl
    rw [heq, Measure.volume_eq_prod, integral_prod _ hint_prod]
  let c_sph : ℝ := (2 * k + 1 : ℝ) * (Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ))
  let H : ℝ × ℝ → ℂ := fun p =>
    (p.2 ^ (2 * k) : ℝ) •
      (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (p.1 * r : ℂ)) * (g ((p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ))
  have hH_cont : Continuous H := by
    dsimp [H]
    exact ((continuous_snd.pow (2 * k)).smul
      ((Complex.continuous_exp.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp
          (hg_cont.comp_continuous (by fun_prop) fun p => mem_Ici.mpr (by positivity)))))
  have hstep2 : (∫ u : ℝ, ∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
          (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ)) =
      c_sph • ∫ u : ℝ, ∫ ρ in Ioi (0 : ℝ), H (u, ρ) := by
    have h_inner : ∀ u : ℝ,
        (∫ y : EuclideanSpace ℝ (Fin (2 * k + 1)),
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) *
            (g ((u ^ 2 + ‖y‖ ^ 2) / 2) : ℂ)) =
        c_sph • ∫ ρ in Ioi (0 : ℝ), H (u, ρ) := by
      intro u
      let ψ : ℝ → ℂ := fun ρ =>
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (u * r : ℂ)) * (g ((u ^ 2 + ρ ^ 2) / 2) : ℂ)
      have hsph := MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2 * k + 1))))) ψ
      have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * k + 1))) = 2 * k + 1 :=
        finrank_euclideanSpace_fin
      have hvol := InnerProductSpace.volume_ball_of_dim_odd (E := EuclideanSpace ℝ (Fin (2 * k + 1)))
        (k := k) hdim 0 1
      have hvol_real : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k + 1))) 1) =
          Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℝ) := by
        rw [Measure.real_def, hvol, ENNReal.ofReal_one, one_pow, one_mul, hdim,
          ENNReal.toReal_ofReal (by positivity)]
      rw [hdim, hvol_real, Nat.add_sub_cancel] at hsph
      simp_rw [nsmul_eq_mul, Complex.real_smul] at hsph
      rw [Complex.real_smul]
      dsimp [c_sph]
      push_cast at hsph ⊢
      have hnorm_fac : ((2 * (k : ℂ) + 1) * ((Real.pi : ℂ) ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℂ))) *
          ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ =
          (2 * (k : ℂ) + 1) * (((Real.pi : ℂ) ^ k * 2 ^ (k + 1) / ((2 * k + 1 : ℕ)‼ : ℂ)) *
            ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ) := by ring
      have heq_rhs : ∫ ρ in Ioi (0 : ℝ), H (u, ρ) = ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (2 * k) * ψ ρ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
        dsimp [H, ψ]; push_cast; rfl
      rw [heq_rhs, hnorm_fac]
      exact hsph
    simp_rw [h_inner]
    rw [integral_smul]
  have ht_int : IntegrableOn (fun t : ℝ => t ^ k * |g t|) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => ‖t ^ k * g t‖) (Ioi 0) :=
      ((integrable_radialLift_iff hw g).1 hg_int).norm
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (mem_Ioi.mp ht).le _)]
  have hH_int : IntegrableOn H ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := by
    have haesm_H : AEStronglyMeasurable H (volume.restrict ((univ : Set ℝ) ×ˢ Ioi 0)) :=
      hH_cont.continuousOn.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioi)
    have hs_int : IntegrableOn (fun s : ℝ => s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|)) (Ioi 0) := by
      have him : (fun s : ℝ => s ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
        ext t; refine ⟨fun ⟨s, hs, h⟩ => h ▸ div_pos (sq_pos_of_pos hs) zero_lt_two,
          fun ht => ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩⟩
        dsimp only; rw [Real.sq_sqrt (mul_pos zero_lt_two ht).le]; ring
      have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) s (Ioi 0) s :=
        fun s _ => by simpa [Nat.cast_ofNat] using ((hasDerivAt_pow 2 s).div_const 2).hasDerivWithinAt
      have hinj : InjOn (fun s : ℝ => s ^ 2 / 2) (Ioi 0) := fun x hx y hy hxy => by
        have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le; have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
        have : x ^ 2 = y ^ 2 := by linarith
        nlinarith [sq_nonneg (x - y)]
      have ht_int_img : IntegrableOn (fun t : ℝ => t ^ k * |g t|) ((fun s : ℝ => s ^ 2 / 2) '' Ioi 0) := by
        rwa [him]
      have hcomp := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
        (f' := fun x => x) (g := fun t => t ^ k * |g t|)).mp ht_int_img
      refine hcomp.congr_fun (fun s hs => ?_) measurableSet_Ioi
      dsimp only
      rw [abs_of_pos hs, smul_eq_mul]
    have hfin : (∫⁻ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H p‖₊ : ℝ≥0∞)) < ⊤ := by
      have hlin := lintegral_comp_polarCoord_symm
        (fun p : ℝ × ℝ => ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) p)
      have h_eq_lhs : (∫⁻ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), (‖H p‖₊ : ℝ≥0∞)) =
          ∫⁻ p : ℝ × ℝ, ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) p :=
        (lintegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi) _).symm
      rw [h_eq_lhs, ← hlin]
      have hsub : polarCoord.target ∩ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi) =
          Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi :=
        inter_eq_right.mpr fun p hp => ⟨hp.1, by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      have h_le_ub : ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 •
              ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) (polarCoord.symm p) ≤
          ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
        calc ∫⁻ p in polarCoord.target,
                ENNReal.ofReal p.1 •
                  ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => (‖H q‖₊ : ℝ≥0∞)) (polarCoord.symm p)
            = ∫⁻ p in polarCoord.target,
                (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi).indicator
                  (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞)) p := by
              refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
              rw [polarCoord_symm_apply]
              by_cases hθ0 : p.2 ∈ Ioo (0 : ℝ) Real.pi
              · have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0.2
                have hmem : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) :=
                  ⟨trivial, mul_pos hp.1 hsin⟩
                have hmem2 : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := ⟨hp.1, hθ0⟩
                rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem2, smul_eq_mul]
              · have hnot : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
                  intro hmem
                  have hsin : 0 < Real.sin p.2 := pos_of_mul_pos_right hmem.2 (mem_Ioi.mp hp.1).le
                  have hlt : 0 < p.2 := by
                    by_contra hle; push Not at hle
                    have : Real.sin p.2 ≤ 0 := by
                      rcases eq_or_lt_of_le hle with h0 | hneg
                      · rw [h0]; simp
                      · rw [← neg_neg p.2, Real.sin_neg]
                        exact neg_nonpos.mpr (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hneg) (by linarith [hp.2.1])).le
                    linarith
                  exact hθ0 ⟨hlt, hp.2.2⟩
                rw [Set.indicator_of_notMem hnot, smul_zero, Set.indicator_of_notMem (fun h : p ∈ (_ : Set ℝ) ×ˢ Ioo (0 : ℝ) Real.pi => hθ0 h.2)]
          _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal p.1 * (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) := by
              rw [setLIntegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo), inter_comm, hsub]
          _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
                ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
              refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
              have hsin_nn : 0 ≤ Real.sin p.2 := (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2).le
              have htrig : ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) / 2 = p.1 ^ 2 / 2 := by
                calc ((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) / 2
                    = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) / 2 := by ring
                  _ = p.1 ^ 2 * 1 / 2 := by rw [Real.cos_sq_add_sin_sq]
                  _ = p.1 ^ 2 / 2 := by ring
              have hval : p.1 * ‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ ≤
                  2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)) := by
                dsimp [H]
                rw [htrig, norm_mul, Complex.norm_real,
                  Real.norm_of_nonneg (pow_nonneg (mul_nonneg hp.1.le hsin_nn) _),
                  norm_mul, show -2 * (Real.pi : ℂ) * Complex.I * ((p.1 * Real.cos p.2 : ℝ) * (r : ℂ)) =
                    ((-2 * Real.pi * (p.1 * Real.cos p.2 * r) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                  Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
                have hsin_le1 : Real.sin p.2 ≤ 1 := Real.sin_le_one p.2
                have hpow : (p.1 * Real.sin p.2) ^ (2 * k) ≤ p.1 ^ (2 * k) := by
                  calc (p.1 * Real.sin p.2) ^ (2 * k) ≤ (p.1 * 1) ^ (2 * k) :=
                        pow_le_pow_left₀ (mul_nonneg hp.1.le hsin_nn)
                          (mul_le_mul_of_nonneg_left hsin_le1 hp.1.le) _
                    _ = p.1 ^ (2 * k) := by rw [mul_one]
                calc p.1 * ((p.1 * Real.sin p.2) ^ (2 * k) * |g (p.1 ^ 2 / 2)|)
                    ≤ p.1 * (p.1 ^ (2 * k) * |g (p.1 ^ 2 / 2)|) := by
                      gcongr
                      exact hp.1.le
                  _ = 2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)) := by
                      have h2ne : (2 : ℝ) ^ k ≠ 0 := by positivity
                      rw [div_pow, show (p.1 ^ 2) ^ k = p.1 ^ (2 * k) from (pow_mul p.1 2 k).symm]
                      field_simp [h2ne]
              rw [show (‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖₊ : ℝ≥0∞) =
                  ENNReal.ofReal ‖H (p.1 * Real.cos p.2, p.1 * Real.sin p.2)‖ from
                  (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm,
                ← ENNReal.ofReal_mul hp.1.le]
              exact ENNReal.ofReal_le_ofReal hval
      have h_prod_lt : (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|)))) < ⊤ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        have hm_f : Measurable fun p : ℝ × ℝ =>
            ENNReal.ofReal (2 ^ k * (p.1 * ((p.1 ^ 2 / 2) ^ k * |g (p.1 ^ 2 / 2)|))) := by
          refine ENNReal.continuous_ofReal.measurable.comp ?_
          exact (continuous_const.mul (continuous_fst.mul
            (((continuous_fst.pow 2).div_const 2 |>.pow k).mul
              (continuous_abs.comp (hg_cont.comp_continuous ((continuous_fst.pow 2).div_const 2) fun p =>
                mem_Ici.mpr (div_nonneg (sq_nonneg _) zero_lt_two.le)))))).measurable
        rw [MeasureTheory.lintegral_prod _ hm_f.aemeasurable]
        have h_eq : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ _θ in Ioo (0 : ℝ) Real.pi,
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|)))) =
            ENNReal.ofReal Real.pi * ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) := by
          simp_rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
          have hm1 : Measurable fun s : ℝ =>
              ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) :=
            ENNReal.continuous_ofReal.measurable.comp
              ((continuous_const.mul (continuous_id.mul (((continuous_pow 2).div_const 2 |>.pow k).mul
                (continuous_abs.comp (hg_cont.comp_continuous ((continuous_pow 2).div_const 2) fun s =>
                  mem_Ici.mpr (div_nonneg (sq_nonneg _) zero_lt_two.le))))))).measurable
          rw [lintegral_mul_const _ hm1, mul_comm]
        rw [h_eq]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        have hlt := (hs_int.const_mul ((2 : ℝ) ^ k)).hasFiniteIntegral
        have h_eq2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))) =
            ∫⁻ s in Ioi (0 : ℝ), (‖(2 : ℝ) ^ k * (s * ((s ^ 2 / 2) ^ k * |g (s ^ 2 / 2)|))‖₊ : ℝ≥0∞) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
          have hs0 : 0 ≤ s := (mem_Ioi.mp hs).le
          rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm, Real.norm_of_nonneg (by positivity)]
        rw [h_eq2]
        exact hlt
      exact lt_of_le_of_lt h_le_ub h_prod_lt
    exact ⟨haesm_H, hfin⟩
  have hstep3 : (∫ u : ℝ, ∫ ρ in Ioi (0 : ℝ), H (u, ρ)) =
      ∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p := by
    rw [Measure.volume_eq_prod] at hH_int ⊢
    have hprod := (setIntegral_prod H hH_int).symm
    simp_rw [setIntegral_univ] at hprod
    exact hprod
  have hstep4 : (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), H p) =
      ∫ s in Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi, s • H (s * Real.cos θ, s * Real.sin θ) :=
    setIntegral_polarCoord_Ioi H hH_int hH_cont
  have hstep5 : ∀ s ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (0 : ℝ) Real.pi, s • H (s * Real.cos θ, s * Real.sin θ)) =
        s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) := by
    intro s hs
    have htrig : ∀ θ : ℝ, ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2 = s ^ 2 / 2 := fun θ => by
      calc ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2
          = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) / 2 := by ring
        _ = s ^ 2 * 1 / 2 := by rw [Real.cos_sq_add_sin_sq]
        _ = s ^ 2 / 2 := by ring
    have heq_θ : ∀ θ : ℝ, s • H (s * Real.cos θ, s * Real.sin θ) =
        (s : ℂ) * (((2 * (s ^ 2 / 2) : ℝ) : ℂ) ^ k * (g (s ^ 2 / 2) : ℂ) *
          (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) *
          ((((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))) := by
      intro θ
      have hfac_ne : (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (by positivity) (sinEvenIntegral_pos k)).ne'
      have hmul : (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ) *
          (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hfac_ne
      dsimp [H]
      rw [htrig θ]
      have hcast :
          (s : ℂ) * ((((s * Real.sin θ) ^ (2 * k) : ℝ) : ℂ) *
            (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * ((s * Real.cos θ : ℝ) * r : ℂ)) *
              (g (s ^ 2 / 2) : ℂ))) =
          (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ)) *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ)) := by
        rw [Complex.ofReal_pow, Complex.ofReal_mul, mul_pow, Complex.ofReal_pow, Complex.ofReal_mul]
        rw [show (-2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (Real.cos θ : ℂ) * (r : ℂ))) =
          (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ) by ring]
        ring
      rw [hcast]
      have hcast2 :
          (s : ℂ) * (((2 * (s ^ 2 / 2) : ℝ) : ℂ) ^ k * (g (s ^ 2 / 2) : ℂ) *
            (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) =
          (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) *
            (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) := by
        push_cast
        rw [show (2 : ℂ) * ((s : ℂ) ^ 2 / 2) = (s : ℂ) ^ 2 by ring, ← pow_mul]
      rw [hcast2]
      calc (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ)) *
            (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
              ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))
          = (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) * 1) *
              (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
                ((Real.sin θ ^ (2 * k) : ℝ) : ℂ)) := by ring
        _ = (s : ℂ) * ((s : ℂ) ^ (2 * k) * (g (s ^ 2 / 2) : ℂ) *
                (((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)) *
              ((((k ! : ℝ) * sinEvenIntegral k : ℝ) : ℂ)⁻¹ *
                (Complex.exp ((-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) * (Real.cos θ : ℂ)) *
                  ((Real.sin θ ^ (2 * k) : ℝ) : ℂ))) := by
            rw [← hmul]; ring
    simp_rw [heq_θ, integral_const_mul]
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    have hbes := besselSC_eq_sin_integral k (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ))
    have hz_sq : (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) ^ 2 / 4 =
        4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ) := by
      have hr_sq : (r : ℂ) ^ 2 = (2 : ℂ) * (c' : ℂ) * (b : ℂ) ^ 2 / 3 := by
        dsimp [r]; push_cast
        rw [mul_pow, show ((Real.sqrt (2 * c' / 3) : ℝ) : ℂ) ^ 2 = ((2 * c' / 3 : ℝ) : ℂ) by
          exact_mod_cast Real.sq_sqrt (by positivity)]
        push_cast; ring
      calc (-2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) * (s : ℂ)) ^ 2 / 4
          = 4 * (Real.pi : ℂ) ^ 2 * (Complex.I ^ 2) * (r : ℂ) ^ 2 * (s : ℂ) ^ 2 / 4 := by ring
        _ = 4 * (Real.pi : ℂ) ^ 2 * (-1) * ((2 : ℂ) * (c' : ℂ) * (b : ℂ) ^ 2 / 3) * (s : ℂ) ^ 2 / 4 := by
            rw [Complex.I_sq, hr_sq]
        _ = _ := by push_cast; ring
    rw [← hbes, hz_sq, Complex.real_smul]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hstep5] at hstep4
  have hstep6 : ∫ s in Ioi (0 : ℝ), s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) *
        ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) =
      ((k ! : ℝ) * sinEvenIntegral k : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)) := by
    let Φ : ℝ → ℂ := fun t => ((2 * t : ℝ) : ℂ) ^ k *
      ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g t : ℂ) *
      besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))
    have h6 : ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) = ∫ t in Ioi (0 : ℝ), Φ t :=
      setIntegral_sq_div_two_Ioi Φ
    have h6l : ∫ s in Ioi (0 : ℝ), s • (((2 * (s ^ 2 / 2)) ^ k : ℂ) *
          ((k ! : ℝ) * sinEvenIntegral k : ℂ) * (g (s ^ 2 / 2) : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * ((s ^ 2 / 2 : ℝ) : ℂ))) =
        ∫ s in Ioi (0 : ℝ), s • Φ (s ^ 2 / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      dsimp [Φ]; push_cast; rfl
    rw [h6l, h6, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp [Φ]; ring
  have hfour_final : -(g (c' * b ^ 2 / 3) : ℂ) =
      c_sph • (((k ! : ℝ) * sinEvenIntegral k : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
          besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))) := by
    rw [hfour_eq, hstep1, hstep2, hstep3, hstep4, hstep6]
  have hconst_c : (c_sph : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ) =
      2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) := by
    calc (c_sph : ℂ) * ((k ! : ℝ) * sinEvenIntegral k : ℂ)
        = ((c_sph * ((k ! : ℝ) * sinEvenIntegral k) : ℝ) : ℂ) := by push_cast; ring
      _ = ((2 * Real.pi ^ (k + 1) : ℝ) : ℂ) := by rw [sphere_const_cancel k]
      _ = 2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) := by push_cast; rw [pow_succ']; ring
  rw [Complex.real_smul, ← mul_assoc, hconst_c] at hfour_final
  have hint_pull : 2 * (Real.pi : ℂ) * ((Real.pi : ℂ) ^ k) *
      ∫ t in Ioi (0 : ℝ), ((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)) =
      2 * (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ),
        (g t : ℂ) * kernelKC w (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) (t : ℂ) := by
    rw [mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold kernelKC
    change (Real.pi : ℂ) ^ k * (((2 * t : ℝ) : ℂ) ^ k * (g t : ℂ) *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ))) =
      (g t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ k *
        besselSC k (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) * (t : ℂ)))
    rw [show (2 * (Real.pi : ℂ) * (t : ℂ)) = (Real.pi : ℂ) * ((2 * t : ℝ) : ℂ) by push_cast; ring, mul_pow]
    ring
  rw [hint_pull] at hfour_final
  unfold hankelContinuationW
  calc -2 * (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ),
        (g t : ℂ) * kernelKC w (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) (t : ℂ)
      = -(2 * (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ),
          (g t : ℂ) * kernelKC w (-(c' : ℂ) * (b : ℂ) ^ 2 / 3) (t : ℂ)) := by ring
    _ = -(-(g (c' * b ^ 2 / 3) : ℂ)) := congrArg Neg.neg hfour_final.symm
    _ = (g (c' * b ^ 2 / 3) : ℂ) := neg_neg _

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.testClass_integral_kernelK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms testClass_integral_kernelK_le

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.hankelContinuationW_strip_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelContinuationW_strip_bound

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.continuousOn_hankelContinuationW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_hankelContinuationW

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.differentiableOn_hankelContinuationW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_hankelContinuationW

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.hankelContinuationW_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelContinuationW_ofReal

end FormalResearch.ModularBootstrap.WeightAxioms

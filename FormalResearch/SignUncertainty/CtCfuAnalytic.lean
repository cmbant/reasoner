module

public import Mathlib
public import FormalResearch.SignUncertainty.CtCfuInv

/-!
# `ct:cfu` Step 2: the germs `n, ñ, d, a ↦ z_A(a)` and `ψ_ε = θ̂(z_A)/d(z_A)` are *real-analytic* at `0`

`constant_terms_lower.tex`, Lemma `ct:cfu` Step 2 (the phase shift `ψ_ε(a) = h_ε(-a, a)` extends analytically across `a = 0`).
**Proved.**  `CtCfuGerm`/`CtCfuInv` prove these germs `C^∞`; here the power-series argument upgrades them to analytic:

* `analyticAt_integral_pow`: for `g` analytic at `0`, `z ↦ ∫₀¹ s^m g(z s^q) ds` is analytic at `0` (termwise integration of the
  power series of `g`);
* `analyticAt_nfun`, `analyticAt_ntil` (`n(z) = ½∫₀¹ k(tz)dt`, `ñ(z) = ∫₀¹ s² n(zs²)ds`), `analyticAt_dF`, `analyticAt_AF`;
* `analyticAt_zA`: the local inverse `z_A` of `A` is analytic (Mathlib's analytic inverse function theorem);
* `analyticAt_psiOf`: `psiOf th` is analytic at `0` when `th` is.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtCfu

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma nnnorm_lt_of_abs_lt {z : ℝ} {s : NNReal} (h : |z| < (s : ℝ)) : (‖z‖₊ : ENNReal) < s := by
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm, Real.norm_eq_abs]; exact h

/-- **Termwise integration of a power series.**  If `g` is analytic at `0`, then `z ↦ ∫₀¹ s^m g(z s^q) ds` is analytic at `0`. -/
theorem analyticAt_integral_pow {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) (m q : ℕ) :
    AnalyticAt ℝ (fun z : ℝ => ∫ s in (0 : ℝ)..1, s ^ m * g (z * s ^ q)) 0 := by
  obtain ⟨p, R, hp⟩ := hg
  obtain ⟨s0, hs0pos, hs0R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hs0 : (0 : ℝ) < s0 := by exact_mod_cast hs0pos
  set a : ℕ → ℝ := fun j => p.coeff j with ha
  have hnorm : ∀ j, ‖p j‖ = |a j| := fun j => by rw [p.norm_apply_eq_norm_coef, Real.norm_eq_abs]
  -- (F1) pointwise sum
  have hF1 : ∀ y : ℝ, |y| < (s0 : ℝ) → HasSum (fun j => a j * y ^ j) (g y) := by
    intro y hy
    have hyb : y ∈ Metric.eball (0 : ℝ) R := by
      rw [Metric.mem_eball, edist_zero_right]
      exact (nnnorm_lt_of_abs_lt hy).trans hs0R
    have := hp.hasSum hyb
    simp only [zero_add] at this
    refine this.congr_fun fun j => ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  -- (F2) summability of the majorant
  have hF2 : ∀ z : ℝ, |z| < (s0 : ℝ) → Summable (fun j => |a j| * |z| ^ j) := by
    intro z hz
    have h := p.summable_norm_mul_pow (r := ‖z‖₊) (by
      exact ((nnnorm_lt_of_abs_lt hz).trans hs0R).trans_le hp.r_le)
    simpa [hnorm, Real.norm_eq_abs] using h
  set c : ℕ → ℝ := fun j => a j / ((m + q * j : ℕ) + 1 : ℝ) with hc
  -- (A) the integral equals the sum
  have hA : ∀ z : ℝ, |z| < (s0 : ℝ) →
      HasSum (fun j => c j * z ^ j) (∫ s in (0 : ℝ)..1, s ^ m * g (z * s ^ q)) := by
    intro z hz
    have hbd : ∀ j : ℕ, ∀ s ∈ Ι (0 : ℝ) 1, ‖s ^ m * (a j * (z * s ^ q) ^ j)‖ ≤ |a j| * |z| ^ j := by
      intro j s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      have hs0' : 0 ≤ s := hs.1.le
      have hs1 : s ≤ 1 := hs.2
      have h1 : |s ^ m| ≤ 1 := by
        rw [abs_pow, abs_of_nonneg hs0']; exact pow_le_one₀ hs0' hs1
      have h2 : |(z * s ^ q) ^ j| ≤ |z| ^ j := by
        rw [abs_pow, abs_mul, abs_pow, abs_of_nonneg hs0']
        have : |z| * s ^ q ≤ |z| := mul_le_of_le_one_right (abs_nonneg z) (pow_le_one₀ hs0' hs1)
        exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (pow_nonneg hs0' _)) this j
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |s ^ m| * (|a j| * |(z * s ^ q) ^ j|) ≤ 1 * (|a j| * |z| ^ j) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by positivity) zero_le_one
        _ = _ := one_mul _
    have hlim : ∀ s ∈ Ι (0 : ℝ) 1, HasSum (fun j => s ^ m * (a j * (z * s ^ q) ^ j)) (s ^ m * g (z * s ^ q)) := by
      intro s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      have hs0' : 0 ≤ s := hs.1.le
      have hs1 : s ≤ 1 := hs.2
      have hy : |z * s ^ q| < (s0 : ℝ) := by
        rw [abs_mul, abs_pow, abs_of_nonneg hs0']
        calc |z| * s ^ q ≤ |z| := mul_le_of_le_one_right (abs_nonneg z) (pow_le_one₀ hs0' hs1)
          _ < s0 := hz
      exact (hF1 _ hy).mul_left (s ^ m)
    have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := 1)
      (F := fun (j : ℕ) (s : ℝ) => s ^ m * (a j * (z * s ^ q) ^ j))
      (f := fun s => s ^ m * g (z * s ^ q))
      (fun j _ => |a j| * |z| ^ j)
      (fun j => (by fun_prop : Continuous fun s : ℝ => s ^ m * (a j * (z * s ^ q) ^ j)).aestronglyMeasurable)
      (fun j => Filter.Eventually.of_forall fun s hs => hbd j s hs)
      (Filter.Eventually.of_forall fun s hs => hF2 z hz)
      (by simp [intervalIntegrable_const])
      (Filter.Eventually.of_forall fun s hs => hlim s hs)
    · refine hdom.congr_fun fun j => ?_
      have e : ∀ s : ℝ, s ^ m * (a j * (z * s ^ q) ^ j) = (a j * z ^ j) * s ^ (m + q * j) := by
        intro s; rw [mul_pow, ← pow_mul, pow_add]; ring
      simp only [e]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [hc]
      push_cast
      field_simp
      simp
  -- (B) the series `∑ c_j z^j` has radius `≥ s0`
  set q' : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c with hq'
  have hrad : (s0 : ENNReal) ≤ q'.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    have htR : (t : ℝ) < s0 := by exact_mod_cast ht
    refine q'.le_radius_of_summable_norm ?_
    have hs := hF2 (t : ℝ) (by rw [abs_of_nonneg (NNReal.coe_nonneg t)]; exact htR)
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
    rw [FormalMultilinearSeries.ofScalars_norm, abs_of_nonneg (NNReal.coe_nonneg t)]
    simp only [hc, Real.norm_eq_abs]
    rw [abs_div]
    have hd : (1 : ℝ) ≤ |((m + q * j : ℕ) + 1 : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]; linarith [(Nat.cast_nonneg (m + q * j) : (0 : ℝ) ≤ _)]
    have : |a j| / |((m + q * j : ℕ) + 1 : ℝ)| ≤ |a j| := div_le_self (abs_nonneg _) hd
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hqpos : 0 < q'.radius := lt_of_lt_of_le (by exact_mod_cast hs0pos) hrad
  have hbq := q'.hasFPowerSeriesOnBall hqpos
  have hqan : AnalyticAt ℝ q'.sum 0 := hbq.analyticAt
  refine hqan.congr ?_
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), |z| < (s0 : ℝ) := by
    have : Metric.ball (0 : ℝ) s0 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hs0
    filter_upwards [this] with z hz
    simpa [Real.dist_eq] using hz
  filter_upwards [hev] with z hz
  have hzb : z ∈ Metric.eball (0 : ℝ) q'.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact (nnnorm_lt_of_abs_lt hz).trans_le hrad
  have h1 := hbq.hasSum (y := z) hzb
  simp only [zero_add] at h1
  have h2 : HasSum (fun j => c j * z ^ j) (q'.sum z) := by
    refine h1.congr_fun fun j => ?_
    rw [hq', FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  exact h2.unique (hA z hz)

lemma analyticAt_kfun : AnalyticAt ℝ kfun 0 := by
  unfold kfun
  have hl : AnalyticAt ℝ (fun y : ℝ => π ^ 2 * y) 0 := analyticAt_const.mul analyticAt_id
  have h3 : AnalyticAt ℝ (fun y : ℝ => Sser 3 (π ^ 2 * y)) 0 :=
    ((analyticOnNhd_Sser 3) (π ^ 2 * 0) (mem_univ _)).comp hl
  have h1 : AnalyticAt ℝ (fun y : ℝ => Sser 1 (π ^ 2 * y)) 0 :=
    ((analyticOnNhd_Sser 1) (π ^ 2 * 0) (mem_univ _)).comp hl
  refine (analyticAt_const.mul h3).div h1 ?_
  simp [Sser_zero]

lemma analyticAt_nfun : AnalyticAt ℝ nfun 0 := by
  have h := (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 / 2 : ℝ)) 0).mul (analyticAt_integral_pow analyticAt_kfun 0 1)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [nfun, pow_zero, one_mul, pow_one]
  show (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..1, kfun (z * s) = 1 / 2 * ∫ (t : ℝ) in (0 : ℝ)..1, kfun (t * z)
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp [mul_comm]

lemma analyticAt_ntil : AnalyticAt ℝ ntil 0 := by
  have h := analyticAt_integral_pow analyticAt_nfun 2 2
  exact h

lemma analyticAt_fF : AnalyticAt ℝ fF 0 := analyticAt_nfun.sub analyticAt_ntil

lemma analyticAt_dF : AnalyticAt ℝ dF 0 := by
  have hpos : 0 < (3 / 2 : ℝ) * fF 0 := by rw [fF_zero]; positivity
  have hf : AnalyticAt ℝ (fun z => (3 / 2 : ℝ) * fF z) 0 := analyticAt_const.mul analyticAt_fF
  have hlog : AnalyticAt ℝ (fun z => Real.log ((3 / 2 : ℝ) * fF z)) 0 :=
    AnalyticAt.comp (g := Real.log) (f := fun z => (3 / 2 : ℝ) * fF z) (x := 0) (analyticAt_log hpos) hf
  have hexp : AnalyticAt ℝ (fun z => Real.exp ((1 / 3 : ℝ) * Real.log ((3 / 2 : ℝ) * fF z))) 0 :=
    AnalyticAt.comp (g := Real.exp) (f := fun z => (1 / 3 : ℝ) * Real.log ((3 / 2 : ℝ) * fF z)) (x := 0)
      analyticAt_rexp (analyticAt_const.mul hlog)
  refine hexp.congr ?_
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < (3 / 2 : ℝ) * fF z :=
    (hf.continuousAt.eventually (lt_mem_nhds hpos))
  filter_upwards [hev] with z hz
  unfold dF
  rw [Real.rpow_def_of_pos hz]
  congr 1; ring

lemma analyticAt_AF : AnalyticAt ℝ AF 0 := by
  unfold AF
  exact (analyticAt_id.neg.mul (analyticAt_dF.pow 2))

lemma analyticAt_zA : AnalyticAt ℝ zA 0 := by
  have hd : deriv AF 0 ≠ 0 := by rw [hasDerivAt_AF_zero.deriv]; exact d0_sq_ne
  have hleft : ∀ᶠ x in 𝓝 (0 : ℝ), zA (AF x) = x :=
    (contDiffAt_AF.hasStrictFDerivAt hasFDerivAt_AF_zero (by simp : (∞' : WithTop ℕ∞) ≠ 0)).eventually_left_inverse
  have hid : AnalyticAt ℝ (zA ∘ AF) 0 :=
    (analyticAt_id).congr (hleft.mono fun x hx => hx.symm)
  have := (analyticAt_comp_iff_of_deriv_ne_zero analyticAt_AF hd (g := zA)).mp hid
  rwa [AF_zero] at this

lemma analyticAt_psiOf {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0) : AnalyticAt ℝ (psiOf th) 0 := by
  unfold psiOf
  have hz : AnalyticAt ℝ zA 0 := analyticAt_zA
  have h1 : AnalyticAt ℝ (fun a => th (zA a)) 0 := by
    have := hth; rw [← zA_zero] at this; exact this.comp hz
  have h2 : AnalyticAt ℝ (fun a => dF (zA a)) 0 := by
    have := analyticAt_dF; rw [← zA_zero] at this; exact this.comp hz
  refine h1.div h2 ?_
  rw [zA_zero, dF_zero]; exact d0_pos.ne'

end FormalResearch.SignUncertainty.CtCfu

module

public import FormalResearch.ModularBootstrap.Spin.SpinS2xS23b
public import Mathlib.Analysis.Complex.Schwarz

/-!
# Lemma S2.4 (`spinnotes:S24`): Sub-bistrip holomorphy, derivative bounds, and double inward telescope

Proves `SpinS24` (`spinning_foundations.tex`, lines 425–496):
1. For `c ≥ 25` (`a = (c - 1) / 12 ≥ 2`) and `0 < θ < 1 / 2`, there exists `C(a, θ) > 0`
   independent of `Φ` such that `I_θ[Φ] ≤ C(a, θ) M_2[Φ]`, `spinGC a Φ` is separately
   holomorphic on `spinStrip (1 / 2)²`, agrees with `spinG a Φ` on `ℝ²`, and satisfies
   `‖spinGC a Φ bL bR‖ ≤ C(a, θ) M_2[Φ]` on `|Im bL|, |Im bR| ≤ θ`.
2. For `c ≥ 40` (`a = (c - 1) / 12`), on `‖bL‖, ‖bR‖ ≤ 1 / 2`,
   `‖spinDaC a Φ bL bR‖ ≤ 64 M_2[Φ] ‖bL‖² ‖bR‖²`, and for all `bL, bR ∈ spinStrip (1 / 2)`,
   `HasSum (fun q : ℕ × ℕ => spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR))
     (spinGC a Φ bL bR - spinGC a Φ bL 0 - spinGC a Φ 0 bR + spinGC a Φ 0 0)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Section 1: Scaling invariance, zero-norm rigidity, and `I_{1/24}[Φ] ≤ C₀ M₂[Φ]` -/

private lemma spinTestClass_const_mul {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (t : ℝ) : SpinTestClass a (fun p => t * Φ p) where
  cont := continuous_const.mul hΦ.cont
  int := hΦ.int.const_mul t
  d4_inv := by
    refine ⟨fun rL rR => ?_, fun rL rR => ?_, fun rL rR => ?_⟩
    · simp only [hΦ.d4_inv.1 rL rR]
    · simp only [hΦ.d4_inv.2.1 rL rR]
    · simp only [hΦ.d4_inv.2.2 rL rR]
  fourier_odd := by
    ext w
    change (∫ v : EuclideanSpace ℝ (Fin 2), 𝐞 (-⟪v, w⟫) • ((t * Φ (v 0, v 1) : ℝ) : ℂ)) =
      -((t * Φ (w 0, w 1) : ℝ) : ℂ)
    have h1 : (fun v : EuclideanSpace ℝ (Fin 2) => 𝐞 (-⟪v, w⟫) • ((t * Φ (v 0, v 1) : ℝ) : ℂ)) =
        fun v => (t : ℂ) * (𝐞 (-⟪v, w⟫) • ((Φ (v 0, v 1) : ℝ) : ℂ)) := by
      ext v
      rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul]
      push_cast; ring
    rw [h1, integral_const_mul]
    have hfo := congrFun hΦ.fourier_odd w
    change (∫ v : EuclideanSpace ℝ (Fin 2), 𝐞 (-⟪v, w⟫) • ((Φ (v 0, v 1) : ℝ) : ℂ)) =
      -((Φ (w 0, w 1) : ℝ) : ℂ) at hfo
    rw [hfo]
    push_cast; ring
  int_M2 := by
    refine (hΦ.int_M2.const_mul |t|).congr (Eventually.of_forall fun p => ?_)
    dsimp only
    rw [abs_mul]
    ring

private lemma spinM2_eq_zero_imp {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (hm : spinM2 a Φ = 0) : ∀ p : ℝ × ℝ, Φ p = 0 := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hcont_V1 : Continuous (spinV1 a) := by
    unfold spinV1; fun_prop
  let f : ℝ × ℝ → ℝ := fun p => |Φ p| * spinV1 a p.1 * spinV1 a p.2
  have hf_cont : Continuous f :=
    (hΦ.cont.abs.mul (hcont_V1.comp continuous_fst)).mul (hcont_V1.comp continuous_snd)
  have hf_nn : 0 ≤ f := fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1))
    (spinV1_nonneg ha p.2)
  have hf_ae : f =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hf_nn hΦ.int_M2).mp hm
  have hf_eq : f = 0 := (hf_cont.ae_eq_iff_eq volume continuous_zero).mp hf_ae
  have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr => by
    have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
    exact lt_of_lt_of_le (by positivity) h1
  have hzero_off : ∀ p : ℝ × ℝ, p.1 ≠ 0 → p.2 ≠ 0 → Φ p = 0 := fun p hp1 hp2 => by
    have hfp := congrFun hf_eq p
    dsimp [f] at hfp
    have hp1' := (hV1_pos p.1 hp1).ne'
    have hp2' := (hV1_pos p.2 hp2).ne'
    rcases mul_eq_zero.mp hfp with h12 | h2
    · rcases mul_eq_zero.mp h12 with h1 | h1
      · exact abs_eq_zero.mp h1
      · exact absurd h1 hp1'
    · exact absurd h2 hp2'
  intro p
  let seq : ℕ → ℝ × ℝ := fun n =>
    (p.1 + (if 0 ≤ p.1 then (1 : ℝ) else -1) / (n + 1 : ℝ),
     p.2 + (if 0 ≤ p.2 then (1 : ℝ) else -1) / (n + 1 : ℝ))
  have hseq_ne : ∀ n : ℕ, (seq n).1 ≠ 0 ∧ (seq n).2 ≠ 0 := fun n => by
    have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hneg : (-1 : ℝ) / (n + 1 : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hn
    constructor
    · dsimp [seq]; split_ifs with h
      · linarith [div_pos one_pos hn]
      · push Not at h; linarith
    · dsimp [seq]; split_ifs with h
      · linarith [div_pos one_pos hn]
      · push Not at h; linarith
  have hseq_lim : Tendsto seq atTop (𝓝 p) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).congr
        (fun n => by simp [Function.comp_def])
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    have h1 : Tendsto (fun n : ℕ => p.1 + (if 0 ≤ p.1 then (1 : ℝ) else -1) / (n + 1 : ℝ))
        atTop (𝓝 p.1) := by
      have h' : Tendsto (fun n : ℕ => p.1 + (if 0 ≤ p.1 then (1 : ℝ) else -1) * (1 / ((n : ℝ) + 1)))
          atTop (𝓝 (p.1 + (if 0 ≤ p.1 then (1 : ℝ) else -1) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
      simpa [div_eq_mul_inv] using h'
    have h2 : Tendsto (fun n : ℕ => p.2 + (if 0 ≤ p.2 then (1 : ℝ) else -1) / (n + 1 : ℝ))
        atTop (𝓝 p.2) := by
      have h' : Tendsto (fun n : ℕ => p.2 + (if 0 ≤ p.2 then (1 : ℝ) else -1) * (1 / ((n : ℝ) + 1)))
          atTop (𝓝 (p.2 + (if 0 ≤ p.2 then (1 : ℝ) else -1) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
      simpa [div_eq_mul_inv] using h'
    exact h1.prodMk_nhds h2
  have hΦ_lim : Tendsto (fun n : ℕ => Φ (seq n)) atTop (𝓝 (Φ p)) :=
    (hΦ.cont.continuousAt.tendsto).comp hseq_lim
  have hΦ_zero : (fun n : ℕ => Φ (seq n)) = fun _ => 0 := by
    ext n; exact hzero_off (seq n) (hseq_ne n).1 (hseq_ne n).2
  rw [hΦ_zero] at hΦ_lim
  exact tendsto_nhds_unique hΦ_lim tendsto_const_nhds

private lemma integrable_g_one24 {a : ℝ} (ha : 2 ≤ a) :
    Integrable (fun r : ℝ =>
      (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r) / spinV1 a r ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ))
      volume := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  let g : ℝ → ℝ := fun r =>
    (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r) / spinV1 a r ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ)
  have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr => by
    have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
    exact lt_of_lt_of_le (by positivity) h1
  let lam0 : ℝ := π * Real.sqrt a * (1 / 5 : ℝ)
  have hlam0 : 0 < lam0 := by positivity
  let C_g : ℝ := (4 * a) ^ (1 / 5 : ℝ)
  have hC_g : 0 < C_g := by positivity
  have hbd_r : ∀ r : ℝ, r ≠ 0 →
      g r ≤ C_g * (min 1 (Real.sqrt a * |r|)) ^ (-2 / 5 : ℝ) * Real.exp (-lam0 * |r|) := fun r hr => by
    have hV1_lb := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hmin_pos : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
    have hcosh_le : Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r) ≤
        Real.exp ((1 / 6 : ℝ) * π * Real.sqrt a * |r|) := by
      rw [← Real.cosh_abs, Real.cosh_eq]
      have harg : |4 * π * Real.sqrt a * (1 / 24 : ℝ) * r| ≤ (1 / 6 : ℝ) * π * Real.sqrt a * |r| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * (1 / 24 : ℝ))]
        linarith
      have h1 := Real.exp_le_exp.mpr harg
      have h2 : Real.exp (-|4 * π * Real.sqrt a * (1 / 24 : ℝ) * r|) ≤
          Real.exp ((1 / 6 : ℝ) * π * Real.sqrt a * |r|) :=
        Real.exp_le_exp.mpr (by
          have hpos : 0 ≤ (1 / 6 : ℝ) * π * Real.sqrt a * |r| := by positivity
          linarith [abs_nonneg (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r)])
      linarith
    have hV1_rpow : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
        min 1 (Real.sqrt a * |r|) ^ 2) ^ (1 / 6 : ℝ) ≤ spinV1 a r ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hV1_lb (by norm_num)
    have hdiv_le : Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r) / spinV1 a r ^ (1 / 6 : ℝ) ≤
        Real.exp ((1 / 6 : ℝ) * π * Real.sqrt a * |r|) /
          ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
            min 1 (Real.sqrt a * |r|) ^ 2) ^ (1 / 6 : ℝ) :=
      div_le_div₀ (by positivity) hcosh_le (by positivity) hV1_rpow
    have hrpow_le := Real.rpow_le_rpow (div_nonneg (Real.cosh_pos _).le
      (Real.rpow_nonneg (spinV1_nonneg ha r) _)) hdiv_le (by norm_num : (0 : ℝ) ≤ 6 / 5)
    have hrhs_eq : (Real.exp ((1 / 6 : ℝ) * π * Real.sqrt a * |r|) /
        ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
          min 1 (Real.sqrt a * |r|) ^ 2) ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ) =
        C_g * (min 1 (Real.sqrt a * |r|)) ^ (-2 / 5 : ℝ) * Real.exp (-lam0 * |r|) := by
      have h4a_pos : 0 < (4 * a) := by positivity
      have hexp_pos : 0 < Real.exp (2 * π * Real.sqrt a * |r|) := Real.exp_pos _
      rw [Real.div_rpow (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (by positivity),
        show (1 / 6 : ℝ) * (6 / 5 : ℝ) = 1 / 5 by norm_num,
        Real.mul_rpow (mul_nonneg (inv_nonneg.mpr h4a_pos.le) hexp_pos.le) (sq_nonneg _),
        Real.mul_rpow (inv_nonneg.mpr h4a_pos.le) hexp_pos.le,
        Real.inv_rpow h4a_pos.le,
        ← Real.exp_mul, ← Real.exp_mul, div_eq_mul_inv, mul_inv, mul_inv,
        inv_inv, ← Real.exp_neg]
      have hneg_rpow : (min 1 (Real.sqrt a * |r|) ^ (2 : ℕ)) ^ (1 / 5 : ℝ) =
          (min 1 (Real.sqrt a * |r|)) ^ (2 / 5 : ℝ) := by
        rw [← Real.rpow_natCast (min 1 (Real.sqrt a * |r|)) 2, ← Real.rpow_mul hmin_pos.le]
        norm_num
      rw [hneg_rpow, ← Real.rpow_neg hmin_pos.le, show -(2 / 5 : ℝ) = -2 / 5 by norm_num]
      have hmul : Real.exp (1 / 6 * π * Real.sqrt a * |r| * (6 / 5 : ℝ)) *
            ((4 * a) ^ (1 / 5 : ℝ) * Real.exp (-(2 * π * Real.sqrt a * |r| * (1 / 5 : ℝ))) *
              min 1 (Real.sqrt a * |r|) ^ (-2 / 5 : ℝ)) =
          (4 * a) ^ (1 / 5 : ℝ) * min 1 (Real.sqrt a * |r|) ^ (-2 / 5 : ℝ) *
            (Real.exp (1 / 6 * π * Real.sqrt a * |r| * (6 / 5 : ℝ)) *
              Real.exp (-(2 * π * Real.sqrt a * |r| * (1 / 5 : ℝ)))) := by ring
      rw [hmul, ← Real.exp_add]
      dsimp [C_g, lam0]
      ring_nf
    exact hrpow_le.trans_eq hrhs_eq
  have hg_cont : ContinuousOn g ({0}ᶜ) := by
    refine ContinuousOn.rpow ?_ continuousOn_const (fun r hr => Or.inl ?_)
    · refine ContinuousOn.div (by fun_prop) ?_ (fun r hr => (Real.rpow_pos_of_pos (hV1_pos r hr) _).ne')
      exact (Continuous.rpow_const (by unfold spinV1; fun_prop) (fun r => Or.inr (by norm_num))).continuousOn
    · exact (div_pos (Real.cosh_pos _) (Real.rpow_pos_of_pos (hV1_pos r hr) _)).ne'
  have hg_meas : AEStronglyMeasurable g volume := by
    have hm : MeasurableSet ({0}ᶜ : Set ℝ) := (isClosed_singleton (x := (0 : ℝ))).isOpen_compl.measurableSet
    have hcomp : ({0}ᶜ : Set ℝ) =ᵐ[volume] (univ : Set ℝ) := by
      rw [ae_eq_set]
      exact ⟨by simp, by simp⟩
    have hae : AEStronglyMeasurable g (volume.restrict ({0}ᶜ)) := hg_cont.aestronglyMeasurable hm
    rwa [Measure.restrict_congr_set hcomp, Measure.restrict_univ] at hae
  let r₁ : ℝ := (Real.sqrt a)⁻¹
  have hr₁ : 0 < r₁ := inv_pos.mpr hsqa
  have hint_core : IntegrableOn g {r : ℝ | |r| < r₁} volume := by
    have hset : {r : ℝ | |r| < r₁} = Set.Ioo (-r₁) 0 ∪ ({0} ∪ Set.Ioo 0 r₁) := by
      ext r; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff, abs_lt]
      constructor
      · intro ⟨h1, h2⟩
        rcases lt_trichotomy r 0 with hr | rfl | hr
        · left; exact ⟨h1, hr⟩
        · right; left; rfl
        · right; right; exact ⟨hr, h2⟩
      · rintro (⟨h1, h2⟩ | rfl | ⟨h1, h2⟩) <;> constructor <;> linarith
    have hint_Ioo : IntegrableOn g (Set.Ioo 0 r₁) volume := by
      have hdom : IntegrableOn (fun r : ℝ => (C_g * Real.sqrt a ^ (-2 / 5 : ℝ)) * r ^ (-2 / 5 : ℝ))
          (Set.Ioo 0 r₁) volume := by
        have hint_rpow : IntervalIntegrable (fun r : ℝ => r ^ (-2 / 5 : ℝ)) volume 0 r₁ :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -2 / 5)
        exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr₁.le).mp hint_rpow).const_mul
          (C_g * Real.sqrt a ^ (-2 / 5 : ℝ))
      refine hdom.mono' hg_meas.restrict ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => ?_
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _)]
      have h1 := hbd_r r hr.1.ne'
      have hmin_eq : min 1 (Real.sqrt a * |r|) = Real.sqrt a * r := by
        rw [abs_of_pos hr.1, min_eq_right]
        calc Real.sqrt a * r ≤ Real.sqrt a * r₁ := mul_le_mul_of_nonneg_left hr.2.le hsqa.le
          _ = 1 := mul_inv_cancel₀ hsqa.ne'
      have hexp1 : Real.exp (-lam0 * |r|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg r])
      have hr0 : 0 ≤ r := hr.1.le
      calc g r ≤ C_g * (min 1 (Real.sqrt a * |r|)) ^ (-2 / 5 : ℝ) * Real.exp (-lam0 * |r|) := h1
        _ ≤ C_g * (Real.sqrt a * r) ^ (-2 / 5 : ℝ) * 1 := by rw [hmin_eq]; gcongr
        _ = (C_g * Real.sqrt a ^ (-2 / 5 : ℝ)) * r ^ (-2 / 5 : ℝ) := by
            rw [mul_one, Real.mul_rpow hsqa.le hr0]; ring
    have hint_Ioo_neg : IntegrableOn g (Set.Ioo (-r₁) 0) volume := by
      have hcomp := hint_Ioo.comp_neg
      change IntegrableOn (fun x => g (-x)) ((fun r : ℝ => -r) ⁻¹' Set.Ioo 0 r₁) volume at hcomp
      have hpre : (fun r : ℝ => -r) ⁻¹' Set.Ioo 0 r₁ = Set.Ioo (-r₁) 0 := by
        ext r; simp only [Set.mem_preimage, Set.mem_Ioo]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [hpre] at hcomp
      refine hcomp.congr_fun (fun r _ => ?_) measurableSet_Ioo
      simp [g, spinV1_even, mul_neg, Real.cosh_neg]
    have h0 : IntegrableOn g ({0} : Set ℝ) volume := by
      rw [IntegrableOn, Measure.restrict_eq_zero.mpr Real.volume_singleton]
      exact integrable_zero_measure
    rw [hset]
    exact hint_Ioo_neg.union (h0.union hint_Ioo)
  have hint_tail : IntegrableOn g {r : ℝ | r₁ ≤ |r|} volume := by
    have hdom := (integrable_exp_neg_mul_abs hlam0).const_mul C_g
    refine hdom.integrableOn.mono' hg_meas.restrict ?_
    refine ae_restrict_of_forall_mem (measurableSet_le measurable_const continuous_abs.measurable) fun r hr => ?_
    have hr0 : r ≠ 0 := by
      intro heq; subst heq; simp only [Set.mem_setOf_eq, abs_zero] at hr; linarith
    have hmin1 : min 1 (Real.sqrt a * |r|) = 1 := min_eq_left (by
      have hr' : (Real.sqrt a)⁻¹ ≤ |r| := hr
      calc 1 = Real.sqrt a * (Real.sqrt a)⁻¹ := (mul_inv_cancel₀ hsqa.ne').symm
        _ ≤ Real.sqrt a * |r| := mul_le_mul_of_nonneg_left hr' hsqa.le)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _)]
    have h1 := hbd_r r hr0
    rw [hmin1, Real.one_rpow, mul_one] at h1
    exact h1
  have huniv : (univ : Set ℝ) = {r : ℝ | |r| < r₁} ∪ {r : ℝ | r₁ ≤ |r|} := by
    ext r; simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]; exact lt_or_ge |r| r₁
  rw [← integrableOn_univ, huniv]
  exact hint_core.union hint_tail

private lemma spinITheta_init_le {a : ℝ} (ha : 2 ≤ a) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
      spinITheta a (1 / 24) Φ ≤ C₀ * spinM2 a Φ := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  let g : ℝ → ℝ := fun r =>
    (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * r) / spinV1 a r ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ)
  have hg_int : Integrable g volume := integrable_g_one24 ha
  have hg_nn : ∀ r : ℝ, 0 ≤ g r := fun r =>
    Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _
  let I_g : ℝ := ∫ r : ℝ, g r
  have hI_g_nn : 0 ≤ I_g := integral_nonneg hg_nn
  have hg_prod_int : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2) volume :=
    hg_int.mul_prod hg_int
  have hg_prod_val : ∫ p : ℝ × ℝ, g p.1 * g p.2 = I_g ^ 2 := by
    rw [Measure.volume_eq_prod, integral_prod_mul]; ring
  let t : ℝ := max 1 (2 * (5 / 6 : ℝ) * I_g ^ 2)
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos (le_max_left _ _)
  let C_L1 : ℝ := (1 / 3 : ℝ) * t ^ 5
  have hC_L1_pos : 0 < C_L1 := by positivity
  let C₀ : ℝ := (1 / 6 : ℝ) + (5 / 6 : ℝ) * C_L1 * I_g ^ 2
  have hC₀_pos : 0 < C₀ := by positivity
  refine ⟨C₀, hC₀_pos, fun {Φ} hΦ => ?_⟩
  have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr => by
    have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
    exact lt_of_lt_of_le (by positivity) h1
  let L1 : ℝ := ∫ p : ℝ × ℝ, |Φ p|
  have hL1_nn : 0 ≤ L1 := integral_nonneg fun _ => abs_nonneg _
  have hM0_pt : ∀ p : ℝ × ℝ, |Φ p| ≤ L1 := fun p => spinTestClass_abs_le_integral_abs hΦ p
  have hL1_bound : L1 ≤ C_L1 * spinM2 a Φ := by
    have hpt : ∀ᵐ p : ℝ × ℝ, |Φ p| ≤
        (1 / 6 : ℝ) * t ^ 5 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) +
          (5 / 6 : ℝ) * t⁻¹ * L1 * (g p.1 * g p.2) := by
      have haxes : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} =ᵐ[volume] (∅ : Set (ℝ × ℝ)) := by
        rw [ae_eq_set]
        refine ⟨?_, by simp⟩
        have hs : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} = ({0} : Set ℝ) ×ˢ univ ∪ univ ×ˢ ({0} : Set ℝ) := by
          ext p; simp
        rw [hs, Measure.volume_eq_prod, Set.sdiff_empty]
        refine measure_union_null ?_ ?_ <;> (rw [Measure.prod_prod]; simp)
      have hne_ae : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
        filter_upwards [compl_mem_ae_iff.mpr (by simpa using haxes)] with p hp
        simpa [not_or] using hp
      filter_upwards [hne_ae] with p ⟨hp1, hp2⟩
      have hV1_1 := hV1_pos p.1 hp1
      have hV1_2 := hV1_pos p.2 hp2
      have hcosh1 : 1 ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) := Real.one_le_cosh _
      have hcosh2 : 1 ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) := Real.one_le_cosh _
      have hpow_g : (g p.1 * g p.2) ^ (5 / 6 : ℝ) =
          (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) / spinV1 a p.1 ^ (1 / 6 : ℝ)) *
          (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) / spinV1 a p.2 ^ (1 / 6 : ℝ)) := by
        dsimp [g]
        rw [Real.mul_rpow (hg_nn p.1) (hg_nn p.2),
          ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)),
          ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _))]
        norm_num
      have h1_le : |Φ p| ≤ (t ^ 5 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) ^ (1 / 6 : ℝ) *
          (t⁻¹ * L1 * (g p.1 * g p.2)) ^ (5 / 6 : ℝ) := by
        have hΦ_pow : |Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) = |Φ p| := by
          by_cases h0 : |Φ p| = 0
          · simp [h0]
          · rw [← Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0))]; norm_num
        have ht_pow : (t ^ 5) ^ (1 / 6 : ℝ) * (t⁻¹) ^ (5 / 6 : ℝ) = 1 := by
          rw [← Real.rpow_natCast t 5, ← Real.rpow_mul ht_pos.le, Real.inv_rpow ht_pos.le,
            ← Real.rpow_neg ht_pos.le, ← Real.rpow_add ht_pos]
          norm_num
        have hpow_M0 : |Φ p| ^ (5 / 6 : ℝ) ≤ L1 ^ (5 / 6 : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) (hM0_pt p) (by norm_num)
        have h1_cosh : 1 ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
            Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) :=
          one_le_mul_of_one_le_of_one_le hcosh1 hcosh2
        have hleft : |Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) *
              (spinV1 a p.1 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) /
                spinV1 a p.1 ^ (1 / 6 : ℝ))) *
              (spinV1 a p.2 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) /
                spinV1 a p.2 ^ (1 / 6 : ℝ))) =
            (t ^ 5) ^ (1 / 6 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) *
              ((t⁻¹) ^ (5 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) * (g p.1 * g p.2) ^ (5 / 6 : ℝ)) := by
          rw [hpow_g, Real.mul_rpow (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le,
            Real.mul_rpow (abs_nonneg _) hV1_1.le]
          have h1 : (t ^ 5) ^ (1 / 6 : ℝ) * (t⁻¹) ^ (5 / 6 : ℝ) *
                (|Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) *
                (spinV1 a p.1 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) /
                  spinV1 a p.1 ^ (1 / 6 : ℝ))) *
                (spinV1 a p.2 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) /
                  spinV1 a p.2 ^ (1 / 6 : ℝ)))) =
              (t ^ 5) ^ (1 / 6 : ℝ) * (|Φ p| ^ (1 / 6 : ℝ) * spinV1 a p.1 ^ (1 / 6 : ℝ) *
                spinV1 a p.2 ^ (1 / 6 : ℝ)) *
                ((t⁻¹) ^ (5 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) *
                  (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) / spinV1 a p.1 ^ (1 / 6 : ℝ) *
                  (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) / spinV1 a p.2 ^ (1 / 6 : ℝ)))) := by
            ring
          rw [ht_pow, one_mul] at h1
          exact h1
        calc |Φ p| ≤ |Φ p| * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
              Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2)) :=
            le_mul_of_one_le_right (abs_nonneg _) h1_cosh
          _ = (|Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ)) *
                (spinV1 a p.1 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) /
                  spinV1 a p.1 ^ (1 / 6 : ℝ))) *
                (spinV1 a p.2 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) /
                  spinV1 a p.2 ^ (1 / 6 : ℝ))) := by
              rw [hΦ_pow]; field_simp [(Real.rpow_pos_of_pos hV1_1 _).ne', (Real.rpow_pos_of_pos hV1_2 _).ne']
          _ = (t ^ 5) ^ (1 / 6 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) *
                ((t⁻¹) ^ (5 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) * (g p.1 * g p.2) ^ (5 / 6 : ℝ)) := hleft
          _ ≤ (t ^ 5 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) ^ (1 / 6 : ℝ) *
                (t⁻¹ * L1 * (g p.1 * g p.2)) ^ (5 / 6 : ℝ) := by
              rw [Real.mul_rpow (by positivity) (mul_nonneg (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le),
                Real.mul_rpow (by positivity) (mul_nonneg (hg_nn p.1) (hg_nn p.2)),
                Real.mul_rpow (by positivity) hL1_nn]
              gcongr
      have hyoung := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 1 / 6)
        (by norm_num : (0 : ℝ) ≤ 5 / 6)
        (show (0 : ℝ) ≤ t ^ 5 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) by
          exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le))
        (show (0 : ℝ) ≤ t⁻¹ * L1 * (g p.1 * g p.2) by
          exact mul_nonneg (mul_nonneg (by positivity) hL1_nn) (mul_nonneg (hg_nn p.1) (hg_nn p.2)))
        (by norm_num)
      exact (h1_le.trans hyoung).trans_eq (by ring)
    have hint_rhs : Integrable (fun p : ℝ × ℝ =>
        (1 / 6 : ℝ) * t ^ 5 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) +
          (5 / 6 : ℝ) * t⁻¹ * L1 * (g p.1 * g p.2)) volume :=
      (hΦ.int_M2.const_mul _).add (hg_prod_int.const_mul _)
    have hint_int := integral_mono_ae hΦ.int.norm hint_rhs hpt
    rw [integral_add (hΦ.int_M2.const_mul _) (hg_prod_int.const_mul _),
      integral_const_mul, integral_const_mul, hg_prod_val] at hint_int
    have hcoeff : (5 / 6 : ℝ) * t⁻¹ * L1 * I_g ^ 2 ≤ (1 / 2 : ℝ) * L1 := by
      have ht_ge : 2 * (5 / 6 : ℝ) * I_g ^ 2 ≤ t := le_max_right _ _
      have h1 : (5 / 6 : ℝ) * I_g ^ 2 * t⁻¹ ≤ 1 / 2 := by
        rw [mul_inv_le_iff₀ ht_pos]
        linarith
      calc (5 / 6 : ℝ) * t⁻¹ * L1 * I_g ^ 2 = ((5 / 6 : ℝ) * I_g ^ 2 * t⁻¹) * L1 := by ring
        _ ≤ (1 / 2 : ℝ) * L1 := by gcongr
    change L1 ≤ (1 / 6 : ℝ) * t ^ 5 * spinM2 a Φ + (5 / 6 : ℝ) * t⁻¹ * L1 * I_g ^ 2 at hint_int
    dsimp [C_L1]
    linarith
  have hpt_theta : ∀ᵐ p : ℝ × ℝ,
      |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
          Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) ≤
        (1 / 6 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) +
          (5 / 6 : ℝ) * L1 * (g p.1 * g p.2) := by
    have haxes : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} =ᵐ[volume] (∅ : Set (ℝ × ℝ)) := by
      rw [ae_eq_set]
      refine ⟨?_, by simp⟩
      have hs : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} = ({0} : Set ℝ) ×ˢ univ ∪ univ ×ˢ ({0} : Set ℝ) := by
        ext p; simp
      rw [hs, Measure.volume_eq_prod, Set.sdiff_empty]
      refine measure_union_null ?_ ?_ <;> (rw [Measure.prod_prod]; simp)
    have hne_ae : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
      filter_upwards [compl_mem_ae_iff.mpr (by simpa using haxes)] with p hp
      simpa [not_or] using hp
    filter_upwards [hne_ae] with p ⟨hp1, hp2⟩
    have hV1_1 := hV1_pos p.1 hp1
    have hV1_2 := hV1_pos p.2 hp2
    have hpow_g : (g p.1 * g p.2) ^ (5 / 6 : ℝ) =
        (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) / spinV1 a p.1 ^ (1 / 6 : ℝ)) *
        (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) / spinV1 a p.2 ^ (1 / 6 : ℝ)) := by
      dsimp [g]
      rw [Real.mul_rpow (hg_nn p.1) (hg_nn p.2),
        ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)),
        ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _))]
      norm_num
    have h1_le : |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
          Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) ≤
        (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) * (L1 * (g p.1 * g p.2)) ^ (5 / 6 : ℝ) := by
      have hΦ_pow : |Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) = |Φ p| := by
        by_cases h0 : |Φ p| = 0
        · simp [h0]
        · rw [← Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0))]; norm_num
      have hpow_M0 : |Φ p| ^ (5 / 6 : ℝ) ≤ L1 ^ (5 / 6 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (hM0_pt p) (by norm_num)
      calc |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
            Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2)
          = (|Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ)) *
              (spinV1 a p.1 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) /
                spinV1 a p.1 ^ (1 / 6 : ℝ))) *
              (spinV1 a p.2 ^ (1 / 6 : ℝ) * (Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) /
                spinV1 a p.2 ^ (1 / 6 : ℝ))) := by
            rw [hΦ_pow]; field_simp [(Real.rpow_pos_of_pos hV1_1 _).ne', (Real.rpow_pos_of_pos hV1_2 _).ne']
        _ = (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) *
              (|Φ p| ^ (5 / 6 : ℝ) * (g p.1 * g p.2) ^ (5 / 6 : ℝ)) := by
            rw [hpow_g, Real.mul_rpow (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le,
              Real.mul_rpow (abs_nonneg _) hV1_1.le]; ring
        _ ≤ (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) *
              (L1 * (g p.1 * g p.2)) ^ (5 / 6 : ℝ) := by
            rw [Real.mul_rpow hL1_nn (mul_nonneg (hg_nn p.1) (hg_nn p.2))]; gcongr
    have hyoung := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (by norm_num : (0 : ℝ) ≤ 5 / 6)
      (show (0 : ℝ) ≤ |Φ p| * spinV1 a p.1 * spinV1 a p.2 by
        exact mul_nonneg (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le)
      (show (0 : ℝ) ≤ L1 * (g p.1 * g p.2) by
        exact mul_nonneg hL1_nn (mul_nonneg (hg_nn p.1) (hg_nn p.2)))
      (by norm_num)
    exact (h1_le.trans hyoung).trans_eq (by ring)
  have hint_init := integrable_spinITheta_init ha hΦ
  have hint_rhs : Integrable (fun p : ℝ × ℝ =>
      (1 / 6 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) +
        (5 / 6 : ℝ) * L1 * (g p.1 * g p.2)) volume :=
    (hΦ.int_M2.const_mul _).add (hg_prod_int.const_mul _)
  have hint_bd := integral_mono_ae hint_init hint_rhs hpt_theta
  rw [integral_add (hΦ.int_M2.const_mul _) (hg_prod_int.const_mul _),
    integral_const_mul, integral_const_mul, hg_prod_val] at hint_bd
  change spinITheta a (1 / 24) Φ ≤ (1 / 6 : ℝ) * spinM2 a Φ + (5 / 6 : ℝ) * L1 * I_g ^ 2 at hint_bd
  calc spinITheta a (1 / 24) Φ
      ≤ (1 / 6 : ℝ) * spinM2 a Φ + (5 / 6 : ℝ) * L1 * I_g ^ 2 := hint_bd
    _ ≤ (1 / 6 : ℝ) * spinM2 a Φ + (5 / 6 : ℝ) * (C_L1 * spinM2 a Φ) * I_g ^ 2 := by
        gcongr
    _ = C₀ * spinM2 a Φ := by dsimp [C₀]; ring

/-! ### Section 2: General `spinITheta a θ Φ ≤ C(a, θ) M₂[Φ]` for `0 < θ < 1 / 2` -/

private lemma spinITheta_le {a : ℝ} (ha : 2 ≤ a) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
      spinITheta a θ Φ ≤ C * spinM2 a Φ := by
  obtain ⟨C₀, hC₀_pos, hinit⟩ := spinITheta_init_le ha
  by_cases hθ_le : θ ≤ 1 / 24
  · refine ⟨C₀, hC₀_pos, fun {Φ} hΦ => ?_⟩
    have hint_124 := integrable_spinITheta_init ha hΦ
    have hint_θ := integrable_spinITheta ha hθ0 hθ1 hΦ
    have hmono : spinITheta a θ Φ ≤ spinITheta a (1 / 24) Φ := by
      refine integral_mono hint_θ hint_124 fun p => ?_
      have hc1 : Real.cosh (4 * π * Real.sqrt a * θ * p.1) ≤
          Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) := by
        rw [Real.cosh_le_cosh]
        have ha1 : |4 * π * Real.sqrt a * θ * p.1| = 4 * π * Real.sqrt a * θ * |p.1| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        have ha2 : |4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1| =
            4 * π * Real.sqrt a * (1 / 24 : ℝ) * |p.1| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        rw [ha1, ha2]
        exact mul_le_mul_of_nonneg_right (by gcongr) (abs_nonneg _)
      have hc2 : Real.cosh (4 * π * Real.sqrt a * θ * p.2) ≤
          Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) := by
        rw [Real.cosh_le_cosh]
        have ha1 : |4 * π * Real.sqrt a * θ * p.2| = 4 * π * Real.sqrt a * θ * |p.2| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        have ha2 : |4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2| =
            4 * π * Real.sqrt a * (1 / 24 : ℝ) * |p.2| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
        rw [ha1, ha2]
        exact mul_le_mul_of_nonneg_right (by gcongr) (abs_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
        (Real.cosh_pos _).le (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
    exact hmono.trans (hinit hΦ)
  · push Not at hθ_le
    have ha0 : 0 < a := by linarith
    have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
    let ρ : ℝ := Real.sqrt a / 48
    have hρ : 0 < ρ := by positivity
    let ε : ℝ := min (1 / 2) ((1 - 2 * θ) / 2)
    have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hε_lt : ε ≤ (1 - 2 * θ) / 2 := min_le_right _ _
    let δ : ℝ := 2 * π * Real.sqrt a * (1 - ε - 2 * θ)
    have hδ : 0 < δ := by
      have : 0 < 1 - ε - 2 * θ := by linarith
      positivity
    let c_tail : ℝ := 4 * a * (min 1 (Real.sqrt a * ρ))⁻¹ ^ 2
    have hc_tail : 0 < c_tail := by positivity
    have htail_bd : ∀ r : ℝ, ρ ≤ |r| →
        Real.exp (2 * π * Real.sqrt a * |r|) ≤ c_tail * spinV1 a r := fun r hr => by
      have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
      have hmin_le : min 1 (Real.sqrt a * ρ) ≤ min 1 (Real.sqrt a * |r|) :=
        min_le_min le_rfl (mul_le_mul_of_nonneg_left hr hsqa.le)
      have hmin_pos : 0 < min 1 (Real.sqrt a * ρ) := lt_min one_pos (mul_pos hsqa hρ)
      have hsq_le : min 1 (Real.sqrt a * ρ) ^ 2 ≤ min 1 (Real.sqrt a * |r|) ^ 2 :=
        pow_le_pow_left₀ hmin_pos.le hmin_le 2
      have h2 : (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * ρ) ^ 2 ≤
          spinV1 a r :=
        (mul_le_mul_of_nonneg_left hsq_le (by positivity)).trans h1
      calc Real.exp (2 * π * Real.sqrt a * |r|)
          = c_tail * ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * ρ) ^ 2) := by
            dsimp [c_tail]; field_simp [ha0.ne', hmin_pos.ne']
        _ ≤ c_tail * spinV1 a r := mul_le_mul_of_nonneg_left h2 hc_tail.le
    let c_core : ℝ := max 4 (4 * a * ρ ^ 2)
    have hc_core : 0 < c_core := by positivity
    have hcore_bd : ∀ y ∈ Set.Icc (-ρ) ρ, y ^ 2 ≤ c_core * spinV1 a y := fun y hy => by
      have hy_abs : |y| ≤ ρ := abs_le.mpr hy
      have h1 := spinV1_ge_inv_four_a_exp_min_sq ha y
      have hexp1 : 1 ≤ Real.exp (2 * π * Real.sqrt a * |y|) :=
        Real.one_le_exp (by positivity)
      by_cases hle : Real.sqrt a * |y| ≤ 1
      · have hmin : min 1 (Real.sqrt a * |y|) = Real.sqrt a * |y| := min_eq_right hle
        have h2 : (4 * a)⁻¹ * 1 * (Real.sqrt a * |y|) ^ 2 ≤ spinV1 a y := by
          calc (4 * a)⁻¹ * 1 * (Real.sqrt a * |y|) ^ 2
              = (4 * a)⁻¹ * 1 * min 1 (Real.sqrt a * |y|) ^ 2 := by rw [hmin]
            _ ≤ (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |y|) * min 1 (Real.sqrt a * |y|) ^ 2 := by
                gcongr
            _ ≤ spinV1 a y := h1
        have hsq_y : (Real.sqrt a * |y|) ^ 2 = a * y ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0.le, sq_abs]
        rw [hsq_y] at h2
        have h3 : y ^ 2 ≤ 4 * spinV1 a y := by
          have : (4 * a)⁻¹ * 1 * (a * y ^ 2) = y ^ 2 / 4 := by field_simp [ha0.ne']
          linarith
        exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (spinV1_nonneg ha y))
      · push Not at hle
        have hmin : min 1 (Real.sqrt a * |y|) = 1 := min_eq_left hle.le
        have h2 : (4 * a)⁻¹ ≤ spinV1 a y := by
          have h3 : (4 * a)⁻¹ * 1 * (min 1 (Real.sqrt a * |y|)) ^ 2 ≤ spinV1 a y :=
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 (by positivity))
              (sq_nonneg _)).trans h1
          rw [hmin] at h3
          linarith
        have hsq_y : y ^ 2 ≤ ρ ^ 2 := by
          rw [← sq_abs y]
          exact pow_le_pow_left₀ (abs_nonneg _) hy_abs 2
        calc y ^ 2 ≤ ρ ^ 2 := hsq_y
          _ = (4 * a * ρ ^ 2) * (4 * a)⁻¹ := by field_simp [ha0.ne']
          _ ≤ (4 * a * ρ ^ 2) * spinV1 a y := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ c_core * spinV1 a y := mul_le_mul_of_nonneg_right (le_max_right _ _) (spinV1_nonneg ha y)
    obtain ⟨C_s, hC_s, hslice_bd⟩ := spin_slice_L1_le_L1_sq ha hε0 hε1
    let C_c : ℝ := Real.cosh (4 * π * Real.sqrt a * θ * ρ)
    have hC_c : 0 ≤ C_c := (Real.cosh_pos _).le
    let I_exp : ℝ := ∫ x : ℝ, Real.exp (-δ * |x|)
    let C_unif : ℝ := C_c ^ 2 * C₀ + c_tail ^ 2 + 2 * C_c * C_s *
      (ε * (C₀ + 1) * I_exp + (1 - ε) * c_tail * c_core) + 1
    have hC_unif_pos : 0 < C_unif := by
      have h1 : 0 ≤ C_c ^ 2 * C₀ := by positivity
      have h2 : 0 ≤ c_tail ^ 2 := by positivity
      have hI : 0 ≤ I_exp := integral_nonneg fun _ => (Real.exp_pos _).le
      have h3 : 0 ≤ 2 * C_c * C_s * (ε * (C₀ + 1) * I_exp + (1 - ε) * c_tail * c_core) := by
        have : 0 ≤ 1 - ε := by linarith
        positivity
      linarith
    refine ⟨C_unif, hC_unif_pos, fun {Φ} hΦ => ?_⟩
    by_cases hm0 : spinM2 a Φ = 0
    · have hzero := spinM2_eq_zero_imp ha hΦ hm0
      have hI0 : spinITheta a θ Φ = 0 := by
        unfold spinITheta
        simp_rw [hzero, abs_zero, zero_mul, integral_zero]
      rw [hI0, hm0, mul_zero]
    · have hm_pos : 0 < spinM2 a Φ := lt_of_le_of_ne (spinM2_nonneg ha Φ) (Ne.symm hm0)
      let t : ℝ := (spinM2 a Φ)⁻¹
      have ht_pos : 0 < t := inv_pos.mpr hm_pos
      let Ψ : ℝ × ℝ → ℝ := fun p => t * Φ p
      have hΨ : SpinTestClass a Ψ := spinTestClass_const_mul hΦ t
      have hmΨ : spinM2 a Ψ = 1 := by
        unfold spinM2
        have h1 : (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) =
            fun p : ℝ × ℝ => t * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
          ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos ht_pos]; ring
        rw [h1, integral_const_mul]
        change t * spinM2 a Φ = 1
        exact inv_mul_cancel₀ hm_pos.ne'
      have hIΨ_scale : spinITheta a θ Φ = spinM2 a Φ * spinITheta a θ Ψ := by
        unfold spinITheta
        have h1 : (fun p : ℝ × ℝ => |Ψ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
            Real.cosh (4 * π * Real.sqrt a * θ * p.2)) =
            fun p : ℝ × ℝ => t * (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θ * p.2)) := by
          ext p; dsimp [Ψ]; rw [abs_mul, abs_of_pos ht_pos]; ring
        rw [h1, integral_const_mul]
        dsimp [t]
        rw [← mul_assoc, mul_inv_cancel₀ hm_pos.ne', one_mul]
      suffices hΨ_bd : spinITheta a θ Ψ ≤ C_unif by
        rw [hIΨ_scale, mul_comm]
        exact mul_le_mul_of_nonneg_right hΨ_bd hm_pos.le
      let f : ℝ × ℝ → ℝ := fun p =>
        |Ψ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
          Real.cosh (4 * π * Real.sqrt a * θ * p.2)
      have hf_int : Integrable f volume := integrable_spinITheta ha hθ0 hθ1 hΨ
      have hf_nn : ∀ p, 0 ≤ f p := fun p => by dsimp [f]; positivity
      let S₁ : Set (ℝ × ℝ) := Set.Icc (-ρ) ρ ×ˢ Set.Icc (-ρ) ρ
      let S₂ : Set (ℝ × ℝ) := {p : ℝ × ℝ | ρ ≤ |p.1| ∧ ρ ≤ |p.2|}
      let S₃ : Set (ℝ × ℝ) := {p : ℝ × ℝ | ρ ≤ |p.1| ∧ |p.2| ≤ ρ}
      let S₄ : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| ≤ ρ ∧ ρ ≤ |p.2|}
      have hS₁_bd : ∫ p in S₁, f p ≤ C_c ^ 2 * C₀ := by
        have h1 : ∫ p in S₁, f p ≤ ∫ p in S₁, C_c ^ 2 *
            (|Ψ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
              Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2)) := by
          refine setIntegral_mono_on hf_int.integrableOn
            ((integrable_spinITheta_init ha hΨ).const_mul _).integrableOn
            (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
          have hp1 : |p.1| ≤ ρ := abs_le.mpr hp.1
          have hp2 : |p.2| ≤ ρ := abs_le.mpr hp.2
          have hc1 : Real.cosh (4 * π * Real.sqrt a * θ * p.1) ≤ C_c := by
            rw [Real.cosh_le_cosh, abs_mul,
              abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ),
              abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ * ρ)]
            exact mul_le_mul_of_nonneg_left hp1 (by positivity)
          have hc2 : Real.cosh (4 * π * Real.sqrt a * θ * p.2) ≤ C_c := by
            rw [Real.cosh_le_cosh, abs_mul,
              abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ),
              abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ * ρ)]
            exact mul_le_mul_of_nonneg_left hp2 (by positivity)
          have h124_1 : 1 ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) := Real.one_le_cosh _
          have h124_2 : 1 ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2) := Real.one_le_cosh _
          calc f p ≤ |Ψ p| * C_c * C_c := by
                dsimp [f]; exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
                  (Real.cosh_pos _).le (mul_nonneg (abs_nonneg _) hC_c)
            _ = C_c ^ 2 * (|Ψ p| * 1 * 1) := by ring
            _ ≤ C_c ^ 2 * (|Ψ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
                  Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2)) := by
                gcongr
        have h2 : ∫ p in S₁, C_c ^ 2 *
            (|Ψ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.1) *
              Real.cosh (4 * π * Real.sqrt a * (1 / 24 : ℝ) * p.2)) ≤
            C_c ^ 2 * spinITheta a (1 / 24) Ψ := by
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact setIntegral_le_integral (integrable_spinITheta_init ha hΨ)
            (Eventually.of_forall fun p => by positivity)
        have h3 := hinit hΨ
        rw [hmΨ, mul_one] at h3
        exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)))
      have hS₂_bd : ∫ p in S₂, f p ≤ c_tail ^ 2 := by
        have hmS2 : MeasurableSet S₂ :=
          (measurableSet_le measurable_const (continuous_abs.comp continuous_fst).measurable).inter
          (measurableSet_le measurable_const (continuous_abs.comp continuous_snd).measurable)
        have hcosh_le : ∀ r : ℝ, Real.cosh (4 * π * Real.sqrt a * θ * r) ≤
            Real.exp (2 * π * Real.sqrt a * |r|) := fun r => by
          rw [← Real.cosh_abs, Real.cosh_eq]
          have harg : |4 * π * Real.sqrt a * θ * r| ≤ 2 * π * Real.sqrt a * |r| := by
            rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
            have h4θ : 4 * θ ≤ 2 := by linarith
            calc 4 * π * Real.sqrt a * θ * |r| = (4 * θ) * (π * Real.sqrt a * |r|) := by ring
              _ ≤ 2 * (π * Real.sqrt a * |r|) := by gcongr
              _ = 2 * π * Real.sqrt a * |r| := by ring
          have h1 := Real.exp_le_exp.mpr harg
          have h2 : Real.exp (-|4 * π * Real.sqrt a * θ * r|) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
            Real.exp_le_exp.mpr (by
              have hpos : 0 ≤ 2 * π * Real.sqrt a * |r| := by positivity
              linarith [abs_nonneg (4 * π * Real.sqrt a * θ * r)])
          linarith
        have h1 : ∫ p in S₂, f p ≤ ∫ p in S₂, c_tail ^ 2 * (|Ψ p| * spinV1 a p.1 * spinV1 a p.2) := by
          refine setIntegral_mono_on hf_int.integrableOn (hΨ.int_M2.const_mul _).integrableOn hmS2
            fun p hp => ?_
          have hc1 := (hcosh_le p.1).trans (htail_bd p.1 hp.1)
          have hc2 := (hcosh_le p.2).trans (htail_bd p.2 hp.2)
          calc f p ≤ |Ψ p| * (c_tail * spinV1 a p.1) * (c_tail * spinV1 a p.2) := by
                dsimp [f]; exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
                  (Real.cosh_pos _).le (mul_nonneg (abs_nonneg _) (mul_nonneg hc_tail.le (spinV1_nonneg ha p.1)))
            _ = c_tail ^ 2 * (|Ψ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
        have h2 : ∫ p in S₂, c_tail ^ 2 * (|Ψ p| * spinV1 a p.1 * spinV1 a p.2) ≤
            c_tail ^ 2 * spinM2 a Ψ := by
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact setIntegral_le_integral hΨ.int_M2
            (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha p.1))
              (spinV1_nonneg ha p.2))
        rw [hmΨ, mul_one] at h2
        exact h1.trans h2
      have hS₃_bd : ∫ p in S₃, f p ≤
          C_c * C_s * (ε * (C₀ + 1) * I_exp + (1 - ε) * c_tail * c_core) := by
        have hmS₃ : MeasurableSet S₃ :=
          (measurableSet_le measurable_const (continuous_abs.comp continuous_fst).measurable).inter
          (measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const)
        let g : ℝ × ℝ → ℝ := S₃.indicator f
        have hg_int : Integrable g volume := hf_int.indicator hmS₃
        have hS₃_eq : ∫ p in S₃, f p = ∫ x : ℝ, ∫ y : ℝ, g (x, y) := by
          rw [← integral_indicator hmS₃]; exact integral_prod g hg_int
        have hM₀_le : spinITheta a (1 / 24) Ψ ≤ C₀ := by
          have h := hinit hΨ; rw [hmΨ, mul_one] at h; exact h
        have hM2_prod : Integrable (fun p : ℝ × ℝ => |Ψ p| * spinV1 a p.1 * spinV1 a p.2) (volume.prod volume) := by
          rw [← Measure.volume_eq_prod]; exact hΨ.int_M2
        have hM2_x : Integrable (fun x : ℝ => ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y) volume :=
          hM2_prod.integral_prod_left
        have hM2_x_val : ∫ x : ℝ, ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y = 1 := by
          rw [← integral_prod _ hM2_prod, ← Measure.volume_eq_prod]; exact hmΨ
        let rhs_x : ℝ → ℝ := fun x =>
          C_c * C_s * (ε * (C₀ + 1) * Real.exp (-δ * |x|) +
            (1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y))
        have hrhs_int : Integrable rhs_x volume := by
          have h1 : Integrable (fun x : ℝ => C_c * C_s * (ε * (C₀ + 1) * Real.exp (-δ * |x|) +
              (1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y))) volume :=
            (((integrable_exp_neg_mul_abs hδ).const_mul (ε * (C₀ + 1))).add
              ((hM2_x.const_mul (c_tail * c_core)).const_mul (1 - ε))).const_mul (C_c * C_s)
          exact h1
        have hpt_x : ∀ᵐ x : ℝ, ∫ y : ℝ, g (x, y) ≤ rhs_x x := by
          filter_upwards [hΨ.int_M2.prod_right_ae, hf_int.prod_right_ae] with x hint_M2y hint_fy
          by_cases hx : ρ ≤ |x|
          · have hgy_eq : ∫ y : ℝ, g (x, y) = ∫ y in Set.Icc (-ρ) ρ, f (x, y) := by
              rw [← integral_indicator measurableSet_Icc]
              congr 1; ext y
              simp only [g, Set.indicator, S₃, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
              split_ifs with h1 h2 h2 <;> simp_all
            have hcont_y : Continuous (fun y : ℝ => |Ψ (x, y)|) :=
              (hΨ.cont.comp (continuous_const.prodMk continuous_id)).abs
            have hfy_le : ∫ y in Set.Icc (-ρ) ρ, f (x, y) ≤
                Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c * ∫ y in Set.Icc (-ρ) ρ, |Ψ (x, y)| := by
              rw [← integral_const_mul]
              refine setIntegral_mono_on hint_fy.integrableOn
                (hcont_y.continuousOn.integrableOn_Icc.const_mul _) measurableSet_Icc fun y hy => ?_
              have hy_abs : |y| ≤ ρ := abs_le.mpr hy
              have hcy : Real.cosh (4 * π * Real.sqrt a * θ * y) ≤ C_c := by
                rw [Real.cosh_le_cosh, abs_mul,
                  abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ),
                  abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ * ρ)]
                exact mul_le_mul_of_nonneg_left hy_abs (by positivity)
              calc f (x, y) ≤ |Ψ (x, y)| * Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c := by
                    dsimp [f]; gcongr
                _ = _ := by ring
            let Q : ℝ := ∫ y in Set.Icc (-ρ) ρ, |Ψ (x, y)| * y ^ 2
            have hQ_nn : 0 ≤ Q := setIntegral_nonneg measurableSet_Icc fun _ _ => by positivity
            have hQ_le_M2 : Real.exp (2 * π * Real.sqrt a * |x|) * Q ≤
                c_tail * c_core * ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y := by
              have hint_q : IntegrableOn (fun y : ℝ => |Ψ (x, y)| * y ^ 2) (Set.Icc (-ρ) ρ) volume :=
                (hcont_y.mul (continuous_pow 2)).continuousOn.integrableOn_Icc
              have h1 : Real.exp (2 * π * Real.sqrt a * |x|) * Q =
                  ∫ y in Set.Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Ψ (x, y)| * y ^ 2) := by
                rw [← integral_const_mul]
              have h2 : ∫ y in Set.Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Ψ (x, y)| * y ^ 2) ≤
                  ∫ y in Set.Icc (-ρ) ρ, c_tail * c_core * (|Ψ (x, y)| * spinV1 a x * spinV1 a y) := by
                refine setIntegral_mono_on (hint_q.const_mul _) (hint_M2y.integrableOn.const_mul _)
                  measurableSet_Icc fun y hy => ?_
                have hx_v := htail_bd x hx
                have hy_v := hcore_bd y hy
                calc Real.exp (2 * π * Real.sqrt a * |x|) * (|Ψ (x, y)| * y ^ 2)
                    ≤ (c_tail * spinV1 a x) * (|Ψ (x, y)| * (c_core * spinV1 a y)) := by
                      refine mul_le_mul hx_v (mul_le_mul_of_nonneg_left hy_v (abs_nonneg _))
                        (by positivity) (mul_nonneg hc_tail.le (spinV1_nonneg ha x))
                  _ = c_tail * c_core * (|Ψ (x, y)| * spinV1 a x * spinV1 a y) := by ring
              have h3 : ∫ y in Set.Icc (-ρ) ρ, |Ψ (x, y)| * spinV1 a x * spinV1 a y ≤
                  ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y :=
                setIntegral_le_integral hint_M2y (Eventually.of_forall fun y =>
                  mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha x)) (spinV1_nonneg ha y))
              rw [h1]
              calc ∫ y in Set.Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Ψ (x, y)| * y ^ 2)
                  ≤ ∫ y in Set.Icc (-ρ) ρ, c_tail * c_core * (|Ψ (x, y)| * spinV1 a x * spinV1 a y) := h2
                _ = c_tail * c_core * ∫ y in Set.Icc (-ρ) ρ, |Ψ (x, y)| * spinV1 a x * spinV1 a y := by
                    rw [integral_const_mul]
                _ ≤ c_tail * c_core * ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y := by gcongr
            have hcosh_split : Real.cosh (4 * π * Real.sqrt a * θ * x) ≤
                Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε) := by
              have h1 : Real.cosh (4 * π * Real.sqrt a * θ * x) ≤
                  Real.exp (4 * π * Real.sqrt a * θ * |x|) := by
                rw [← Real.cosh_abs, Real.cosh_eq]
                have ha1 : |4 * π * Real.sqrt a * θ * x| = 4 * π * Real.sqrt a * θ * |x| := by
                  rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
                rw [ha1]
                have hexp_le : Real.exp (-(4 * π * Real.sqrt a * θ * |x|)) ≤
                    Real.exp (4 * π * Real.sqrt a * θ * |x|) :=
                  Real.exp_le_exp.mpr (by linarith [show 0 ≤ 4 * π * Real.sqrt a * θ * |x| by positivity])
                linarith
              have h2 : Real.exp (4 * π * Real.sqrt a * θ * |x|) =
                  Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε) := by
                rw [← Real.exp_mul, ← Real.exp_add]
                congr 1; dsimp [δ]; ring
              exact h1.trans_eq h2
            have hslice_x := hslice_bd hΨ x
            have hM₀_nn : 0 ≤ spinITheta a (1 / 24) Ψ := by
              unfold spinITheta; exact integral_nonneg fun p => by positivity
            have hyoung : (spinITheta a (1 / 24) Ψ + 1) ^ ε *
                (Real.exp (2 * π * Real.sqrt a * |x|) * Q) ^ (1 - ε) ≤
                ε * (spinITheta a (1 / 24) Ψ + 1) +
                  (1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q) :=
              Real.geom_mean_le_arith_mean2_weighted hε0.le (by linarith) (by linarith [hM₀_nn]) (by positivity)
                (by ring)
            have hexp_le1 : Real.exp (-δ * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
            rw [hgy_eq]
            calc ∫ y in Set.Icc (-ρ) ρ, f (x, y)
                ≤ Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c * ∫ y in Set.Icc (-ρ) ρ, |Ψ (x, y)| := hfy_le
              _ ≤ (Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε)) * C_c *
                    (C_s * (spinITheta a (1 / 24) Ψ + 1) ^ ε * Q ^ (1 - ε)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_right hcosh_split hC_c) hslice_x
                    (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _)
                    (mul_nonneg (by positivity) hC_c)
              _ = C_c * C_s * (Real.exp (-δ * |x|) *
                    ((spinITheta a (1 / 24) Ψ + 1) ^ ε *
                      (Real.exp (2 * π * Real.sqrt a * |x|) * Q) ^ (1 - ε))) := by
                  rw [Real.mul_rpow (Real.exp_pos _).le hQ_nn]; ring
              _ ≤ C_c * C_s * (Real.exp (-δ * |x|) *
                    (ε * (spinITheta a (1 / 24) Ψ + 1) +
                      (1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q))) := by gcongr
              _ = C_c * C_s * (ε * (spinITheta a (1 / 24) Ψ + 1) * Real.exp (-δ * |x|) +
                    Real.exp (-δ * |x|) * ((1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q))) := by ring
              _ ≤ C_c * C_s * (ε * (C₀ + 1) * Real.exp (-δ * |x|) +
                    1 * ((1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y))) := by
                  have h1me : 0 ≤ 1 - ε := by linarith
                  gcongr
              _ = rhs_x x := by dsimp [rhs_x]; ring
          · have hg0 : (fun y : ℝ => g (x, y)) = fun _ => 0 := by
              ext y; simp [g, S₃, hx]
            rw [hg0, integral_zero]
            have h1 : 0 ≤ ε * (C₀ + 1) * Real.exp (-δ * |x|) := by positivity
            have h2 : 0 ≤ ∫ y : ℝ, |Ψ (x, y)| * spinV1 a x * spinV1 a y :=
              integral_nonneg fun y => mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha x))
                (spinV1_nonneg ha y)
            have h3 : 0 ≤ 1 - ε := by linarith
            dsimp [rhs_x]
            positivity
        have hint_g_x : Integrable (fun x : ℝ => ∫ y : ℝ, g (x, y)) volume := hg_int.integral_prod_left
        have hbd := integral_mono_ae hint_g_x hrhs_int hpt_x
        rw [hS₃_eq]
        calc ∫ x : ℝ, ∫ y : ℝ, g (x, y)
            ≤ ∫ x : ℝ, rhs_x x := hbd
          _ = C_c * C_s * (ε * (C₀ + 1) * I_exp + (1 - ε) * c_tail * c_core) := by
              dsimp [rhs_x]
              rw [integral_const_mul, integral_add ((integrable_exp_neg_mul_abs hδ).const_mul _)
                ((hM2_x.const_mul _).const_mul _), integral_const_mul, integral_const_mul,
                integral_const_mul, hM2_x_val]
              dsimp [I_exp]; ring
      have hS₄_bd : ∫ p in S₄, f p ≤
          C_c * C_s * (ε * (C₀ + 1) * I_exp + (1 - ε) * c_tail * c_core) := by
        have hswap_mp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume :=
          Measure.measurePreserving_swap
        have hpre : (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) ⁻¹' S₃ = S₄ := by
          ext p; simp [S₃, S₄, and_comm, MeasurableEquiv.prodComm]
        have heq : ∫ p in S₄, f p = ∫ p in S₃, f p := by
          rw [← hpre, ← hswap_mp.setIntegral_preimage_emb
            (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).measurableEmbedding f S₃]
          refine setIntegral_congr_fun (measurableSet_preimage
            (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).measurable
            ((measurableSet_le measurable_const (continuous_abs.comp continuous_fst).measurable).inter
              (measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const))) fun p _ => ?_
          dsimp [f]
          simp only [MeasurableEquiv.prodComm, MeasurableEquiv.coe_mk, Equiv.prodComm_apply, Prod.swap]
          rw [hΨ.d4_inv.2.2 p.1 p.2]
          ring
        rw [heq]
        exact hS₃_bd
      have huniv : (univ : Set (ℝ × ℝ)) = S₁ ∪ S₂ ∪ S₃ ∪ S₄ := by
        ext p
        simp only [Set.mem_univ, Set.mem_union, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq,
          true_iff, S₁, S₂, S₃, S₄]
        rcases le_or_gt |p.1| ρ with h1 | h1 <;> rcases le_or_gt |p.2| ρ with h2 | h2
        · left; left; left; exact ⟨abs_le.mp h1, abs_le.mp h2⟩
        · right; exact ⟨h1, h2.le⟩
        · left; right; exact ⟨h1.le, h2⟩
        · left; left; right; exact ⟨h1.le, h2.le⟩
      have hsplit : spinITheta a θ Ψ ≤
          (∫ p in S₁, f p) + (∫ p in S₂, f p) + (∫ p in S₃, f p) + (∫ p in S₄, f p) := by
        change ∫ p : ℝ × ℝ, f p ≤ _
        rw [← setIntegral_univ, huniv]
        have hunion_le : ∀ A B : Set (ℝ × ℝ),
            ∫ p in A ∪ B, f p ≤ (∫ p in A, f p) + (∫ p in B, f p) := fun A B => by
          calc ∫ p in A ∪ B, f p
              ≤ ∫ p, f p ∂(volume.restrict A + volume.restrict B) :=
                integral_mono_measure (Measure.restrict_union_le A B)
                  (Eventually.of_forall hf_nn) (hf_int.integrableOn.integrable.add_measure hf_int.integrableOn.integrable)
            _ = (∫ p in A, f p) + (∫ p in B, f p) :=
                integral_add_measure hf_int.integrableOn hf_int.integrableOn
        have h123 : ∫ p in (S₁ ∪ S₂ ∪ S₃), f p ≤
            (∫ p in S₁, f p) + (∫ p in S₂, f p) + (∫ p in S₃, f p) := by
          have h12 := hunion_le S₁ S₂
          have h12_3 := hunion_le (S₁ ∪ S₂) S₃
          linarith
        have h123_4 := hunion_le (S₁ ∪ S₂ ∪ S₃) S₄
        linarith
      dsimp [C_unif]
      linarith

/-! ### Section 3: Separate holomorphy, real agreement, and bounds for `spinGC` -/

private lemma spinGC_ofReal {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (xL xR : ℝ) : spinGC a Φ (xL : ℂ) (xR : ℂ) = ((spinG a Φ xL xR : ℝ) : ℂ) := by
  unfold spinGC spinG
  have heq : -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (xL : ℂ)) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (xR : ℂ))) =
      spinSliceC Φ (2 * Real.sqrt a * xL) (2 * Real.sqrt a * xR) := by
    unfold spinSliceC
    congr 2
    ext p
    congr 1
    · congr 1; push_cast; ring
    · push_cast; ring
  rw [heq]
  simpa using spinSliceC_ofReal hΦ (2 * Real.sqrt a * xL) (2 * Real.sqrt a * xR)

private lemma spinGC_swap (a : ℝ) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (bL bR : ℂ) :
    spinGC a Φ bL bR = spinGC a Φ bR bL := by
  unfold spinGC
  congr 1
  have hswap_mp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have heq := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ)))
    (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
    (fun p : ℝ × ℝ => (Φ p : ℂ) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR))
  rw [hswap_mp.map_eq] at heq
  rw [heq]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [MeasurableEquiv.prodComm, MeasurableEquiv.coe_mk, Equiv.prodComm_apply, Prod.swap]
  rw [hΦ.d4_inv.2.2 p.1 p.2]
  ring

private lemma spinGC_norm_le_spinITheta {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {bL bR : ℂ} (hbL : |bL.im| ≤ θ) (hbR : |bR.im| ≤ θ) :
    ‖spinGC a Φ bL bR‖ ≤ spinITheta a θ Φ := by
  have ha0 : 0 < a := by linarith
  have hint := integrable_spinITheta ha hθ0 hθ1 hΦ
  unfold spinGC spinITheta
  rw [norm_neg]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
    (Eventually.of_forall fun p => ?_)
  have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL).im = 4 * π * Real.sqrt a * p.1 * bL.im := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR).im = 4 * π * Real.sqrt a * p.2 * bR.im := by
    simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL)‖ ≤
      Real.cosh (4 * π * Real.sqrt a * θ * p.1) := by
    calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * bL.im) := by
          rw [← him1]; exact norm_complex_cos_le_cosh _
      _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.1) := cosh_mul_im_le_cosh ha0 hθ0.le hbL
  have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)‖ ≤
      Real.cosh (4 * π * Real.sqrt a * θ * p.2) := by
    calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * bR.im) := by
          rw [← him2]; exact norm_complex_cos_le_cosh _
      _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.2) := cosh_mul_im_le_cosh ha0 hθ0.le hbR
  dsimp only
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
    (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)

private lemma norm_complex_sin_le_cosh_s24 (w : ℂ) : ‖Complex.sin w‖ ≤ Real.cosh w.im := by
  have h1 : Complex.sin w = Complex.cos (w - π / 2) := by rw [Complex.cos_sub_pi_div_two]
  rw [h1]
  have him : (w - (π / 2 : ℂ)).im = w.im := by simp
  simpa [him] using norm_complex_cos_le_cosh (w - π / 2)

private lemma spinGC_differentiableOn_left {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bR : ℂ} (hbR : bR ∈ spinStrip (1 / 2)) :
    DifferentiableOn ℂ (fun bL => spinGC a Φ bL bR) (spinStrip (1 / 2)) := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  intro b₀ hb₀
  have hb₀_im : |b₀.im| < 1 / 2 := hb₀
  have hbR_im : |bR.im| < 1 / 2 := hbR
  let r : ℝ := (1 / 2 - |b₀.im|) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let θ₀ : ℝ := max (1 / 24) (max (|b₀.im| + r) |bR.im|)
  have hθ₀_pos : 0 < θ₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hθ₀_lt : θ₀ < 1 / 2 := by
    refine max_lt (by norm_num) (max_lt ?_ hbR_im)
    dsimp [r]; linarith
  let θ₁ : ℝ := (θ₀ + 1 / 2) / 2
  have hθ₁_pos : 0 < θ₁ := by dsimp [θ₁]; linarith
  have hθ₁_lt : θ₁ < 1 / 2 := by dsimp [θ₁]; linarith
  have hθ_gap : 0 < θ₁ - θ₀ := by dsimp [θ₁]; linarith
  have hδ_pos : 0 < 4 * π * Real.sqrt a * (θ₁ - θ₀) := by positivity
  let F : ℂ → ℝ × ℝ → ℂ := fun w p =>
    (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)
  let F' : ℂ → ℝ × ℝ → ℂ := fun w p =>
    -((Φ p : ℂ) * (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ)) *
      Complex.sin (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR))
  let bound : ℝ × ℝ → ℝ := fun p =>
    (8 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
      (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
        Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2))
  have hint_θ₁ := integrable_spinITheta ha hθ₁_pos hθ₁_lt hΦ
  have hbound_int : Integrable bound volume := hint_θ₁.const_mul _
  have hF_meas : ∀ᶠ w in 𝓝 b₀, AEStronglyMeasurable (F w) volume := by
    refine Eventually.of_forall fun w => ?_
    have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have h2 : Continuous (fun p : ℝ × ℝ =>
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)) := by fun_prop
    exact ((h1.mul h2).congr (fun p => by dsimp [F]; ring)).aestronglyMeasurable
  have hF_int : Integrable (F b₀) volume := by
    refine (integrable_spinITheta ha hθ₀_pos hθ₀_lt hΦ).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ =>
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * b₀) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)) := by fun_prop
      exact ((h1.mul h2).congr (fun p => by dsimp [F]; ring)).aestronglyMeasurable
    · have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * b₀).im = 4 * π * Real.sqrt a * p.1 * b₀.im := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR).im = 4 * π * Real.sqrt a * p.2 * bR.im := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * b₀)‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * b₀.im) := by
              rw [← him1]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) :=
              cosh_mul_im_le_cosh ha0 hθ₀_pos.le ((le_add_of_nonneg_right hr.le).trans
                ((le_max_left _ _).trans (le_max_right _ _)))
      have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ₀ * p.2) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * bR.im) := by
              rw [← him2]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₀ * p.2) :=
              cosh_mul_im_le_cosh ha0 hθ₀_pos.le ((le_max_right _ _).trans (le_max_right _ _))
      dsimp [F]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
        (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hF'_meas : AEStronglyMeasurable (F' b₀) volume := by
    have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have h2 : Continuous (fun p : ℝ × ℝ => -(4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) *
        Complex.sin (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * b₀) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR))) := by fun_prop
    exact ((h1.mul h2).congr (fun p => by dsimp [F']; ring)).aestronglyMeasurable
  have hF_bd : ∀ᵐ p : ℝ × ℝ, ∀ w ∈ Metric.ball b₀ r, ‖F' w p‖ ≤ bound p := by
    refine Eventually.of_forall fun p w hw => ?_
    have hw_im : |w.im| ≤ θ₀ := by
      have h1 : |w.im - b₀.im| < r := by
        calc |w.im - b₀.im| = |(w - b₀).im| := by simp
          _ ≤ ‖w - b₀‖ := Complex.abs_im_le_norm _
          _ = dist w b₀ := (Complex.dist_eq w b₀).symm
          _ < r := Metric.mem_ball.mp hw
      have h2 : |w.im| ≤ |b₀.im| + r := by
        have := abs_add_le (w.im - b₀.im) b₀.im
        simp only [sub_add_cancel] at this
        linarith
      exact h2.trans ((le_max_left _ _).trans (le_max_right _ _))
    have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w).im = 4 * π * Real.sqrt a * p.1 * w.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR).im = 4 * π * Real.sqrt a * p.2 * bR.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hsin_le : ‖Complex.sin (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w)‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) := by
      calc ‖Complex.sin _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * w.im) := by
            rw [← him1]; exact norm_complex_sin_le_cosh_s24 _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) := cosh_mul_im_le_cosh ha0 hθ₀_pos.le hw_im
    have hcos_le : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * bR.im) := by
            rw [← him2]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) :=
            cosh_mul_im_le_cosh ha0 hθ₁_pos.le (((le_max_right _ _).trans (le_max_right _ _)).trans (by linarith))
    have hlin : |p.1| * Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) ≤
        (2 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) := by
      have harg : 4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1| ≤
          Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|) :=
        (Real.add_one_le_exp _).trans' (by linarith)
      have h1 : |p.1| ≤ (1 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
          Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|) := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hδ_pos]
        calc |p.1| * (4 * π * Real.sqrt a * (θ₁ - θ₀)) =
              4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1| := by ring
          _ ≤ Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|) := harg
      have h2 : Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|) *
          Real.cosh (4 * π * Real.sqrt a * θ₀ * |p.1|) ≤
          2 * Real.cosh (4 * π * Real.sqrt a * θ₁ * |p.1|) := by
        rw [Real.cosh_eq, Real.cosh_eq, mul_div_assoc', mul_div_assoc',
          div_le_div_iff_of_pos_right two_pos, mul_add, ← Real.exp_add, ← Real.exp_add]
        have he1 : 4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1| + 4 * π * Real.sqrt a * θ₀ * |p.1| =
            4 * π * Real.sqrt a * θ₁ * |p.1| := by ring
        have he2 : 4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1| + -(4 * π * Real.sqrt a * θ₀ * |p.1|) ≤
            4 * π * Real.sqrt a * θ₁ * |p.1| := by
          have : 0 ≤ 8 * π * Real.sqrt a * θ₀ * |p.1| := by positivity
          linarith
        have hle2 := Real.exp_le_exp.mpr he2
        have hle3 : 0 ≤ 2 * Real.exp (-(4 * π * Real.sqrt a * θ₁ * |p.1|)) := by positivity
        rw [he1]
        linarith
      have hc_abs0 : Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) =
          Real.cosh (4 * π * Real.sqrt a * θ₀ * |p.1|) := by
        rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ₀ * p.1), abs_mul,
          abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ₀)]
      have hc_abs1 : Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) =
          Real.cosh (4 * π * Real.sqrt a * θ₁ * |p.1|) := by
        rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ₁ * p.1), abs_mul,
          abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ₁)]
      calc |p.1| * Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1)
          = |p.1| * Real.cosh (4 * π * Real.sqrt a * θ₀ * |p.1|) := by rw [hc_abs0]
        _ ≤ ((1 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
              Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|)) *
              Real.cosh (4 * π * Real.sqrt a * θ₀ * |p.1|) := by gcongr
        _ = (1 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
              (Real.exp (4 * π * Real.sqrt a * (θ₁ - θ₀) * |p.1|) *
                Real.cosh (4 * π * Real.sqrt a * θ₀ * |p.1|)) := by ring
        _ ≤ (1 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
              (2 * Real.cosh (4 * π * Real.sqrt a * θ₁ * |p.1|)) := by gcongr
        _ = (2 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) *
              Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) := by rw [hc_abs1]; ring
    dsimp [F', bound]
    simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      abs_of_pos Real.pi_pos, abs_of_pos hsqa]
    calc |Φ p| * (4 * π * Real.sqrt a * |p.1|) *
          ‖Complex.sin (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w)‖ *
          ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)‖
        ≤ |Φ p| * (4 * π * Real.sqrt a * |p.1|) *
            Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) *
            Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by gcongr
      _ = (4 * π * Real.sqrt a) * |Φ p| *
            (|p.1| * Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1)) *
            Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by ring
      _ ≤ (4 * π * Real.sqrt a) * |Φ p| *
            ((2 / (4 * π * Real.sqrt a * (θ₁ - θ₀))) * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1)) *
            Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by gcongr
      _ = _ := by ring
  have hF_deriv : ∀ᵐ p : ℝ × ℝ, ∀ w ∈ Metric.ball b₀ r, HasDerivAt (F · p) (F' w p) w := by
    refine Eventually.of_forall fun p w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => 4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w)
        (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ))
    have h2 := (Complex.hasDerivAt_cos _).comp w h1
    have h3 := (h2.const_mul (Φ p : ℂ)).mul_const
      (Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR))
    refine h3.congr_deriv ?_
    dsimp [F']; ring
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hr)
    hF_meas hF_int hF'_meas hF_bd hbound_int hF_deriv
  have hneg : HasDerivAt (fun w => spinGC a Φ w bR) (-(∫ p : ℝ × ℝ, F' b₀ p)) b₀ := by
    have hfun : (fun w => spinGC a Φ w bR) = fun w => -(∫ p : ℝ × ℝ, F w p) := rfl
    rw [hfun]
    exact hderiv.neg
  exact hneg.differentiableAt.differentiableWithinAt

private lemma spinGC_differentiableOn_right {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bL : ℂ} (hbL : bL ∈ spinStrip (1 / 2)) :
    DifferentiableOn ℂ (fun bR => spinGC a Φ bL bR) (spinStrip (1 / 2)) := by
  have hfun : (fun bR => spinGC a Φ bL bR) = fun bR => spinGC a Φ bR bL := by
    ext bR; exact spinGC_swap a hΦ bL bR
  rw [hfun]
  exact spinGC_differentiableOn_left ha hΦ hbL

private lemma spinGC_continuousAt_zero {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    ContinuousAt (fun q : ℂ × ℂ => spinGC a Φ q.1 q.2) (0, 0) := by
  have ha0 : 0 < a := by linarith
  have hθ0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hθ1 : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hint := integrable_spinITheta ha hθ0 hθ1 hΦ
  let F : ℂ × ℂ → ℝ × ℝ → ℂ := fun q p =>
    (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * q.1) *
      Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * q.2)
  have hF_meas : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), AEStronglyMeasurable (F q) volume :=
    Eventually.of_forall fun q => by
      have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ =>
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * q.1) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * q.2)) := by fun_prop
      exact ((h1.mul h2).congr (fun p => by dsimp [F]; ring)).aestronglyMeasurable
  have hF_bd : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), ∀ᵐ p : ℝ × ℝ,
      ‖F q p‖ ≤ |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.1) *
        Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.2) := by
    have hnhds : Metric.ball (0 : ℂ) (1 / 4) ×ˢ Metric.ball (0 : ℂ) (1 / 4) ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Metric.ball_mem_nhds 0 hθ0) (Metric.ball_mem_nhds 0 hθ0)
    filter_upwards [hnhds] with q hq
    refine Eventually.of_forall fun p => ?_
    have hq1 : |q.1.im| ≤ 1 / 4 := by
      calc |q.1.im| ≤ ‖q.1‖ := Complex.abs_im_le_norm _
        _ ≤ 1 / 4 := (mem_ball_zero_iff.mp hq.1).le
    have hq2 : |q.2.im| ≤ 1 / 4 := by
      calc |q.2.im| ≤ ‖q.2‖ := Complex.abs_im_le_norm _
        _ ≤ 1 / 4 := (mem_ball_zero_iff.mp hq.2).le
    have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * q.1).im = 4 * π * Real.sqrt a * p.1 * q.1.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * q.2).im = 4 * π * Real.sqrt a * p.2 * q.2.im := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * q.1)‖ ≤
        Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.1) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * q.1.im) := by
            rw [← him1]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.1) :=
            cosh_mul_im_le_cosh ha0 hθ0.le hq1
    have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * q.2)‖ ≤
        Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.2) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * q.2.im) := by
            rw [← him2]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 4 : ℝ) * p.2) :=
            cosh_mul_im_le_cosh ha0 hθ0.le hq2
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hF_lim : ∀ᵐ p : ℝ × ℝ, Tendsto (fun q : ℂ × ℂ => F q p) (𝓝 (0, 0)) (𝓝 (F (0, 0) p)) := by
    refine Eventually.of_forall fun p => ?_
    have hc : Continuous (fun q : ℂ × ℂ => F q p) := by dsimp [F]; fun_prop
    exact hc.continuousAt.tendsto
  have ht := (tendsto_integral_filter_of_dominated_convergence _ hF_meas hF_bd hint hF_lim).neg
  simpa [ContinuousAt, spinGC, F] using ht

/-! ### Section 4: Schwarz-squared bound `‖spinDaC a Φ bL bR‖ ≤ 64 M₂[Φ] ‖bL‖² ‖bR‖²` -/

private lemma schwarz_sq_of_even_zero {f : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ f (Metric.ball 0 (1 / 2)))
    (heven : ∀ z : ℂ, f (-z) = f z) (hzero : f 0 = 0)
    (hbd : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), ‖f z‖ ≤ M) :
    ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), ‖f z‖ ≤ 4 * M * ‖z‖ ^ 2 := by
  intro z hz
  have hdiff0 : DifferentiableAt ℂ f 0 :=
    hd.differentiableAt (Metric.ball_mem_nhds 0 (by norm_num))
  have hderiv0 : deriv f 0 = 0 := by
    have h1 : HasDerivAt f (deriv f 0) 0 := hdiff0.hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => f (-w)) (-deriv f 0) 0 := by
      have h1' : HasDerivAt f (deriv f 0) (-0) := by simpa [neg_zero] using h1
      have hneg : HasDerivAt (fun w : ℂ => -w) (-1) 0 := (hasDerivAt_id (0 : ℂ)).neg
      exact (h1'.comp 0 hneg).congr_deriv (by ring)
    have hfun : (fun w : ℂ => f (-w)) = f := funext heven
    rw [hfun] at h2
    have heq : -deriv f 0 = deriv f 0 := h2.unique h1
    have h2d : (2 : ℂ) * deriv f 0 = 0 := by
      calc (2 : ℂ) * deriv f 0 = deriv f 0 - (-deriv f 0) := by ring
        _ = 0 := by rw [heq, sub_self]
    exact (mul_eq_zero.mp h2d).resolve_left (by norm_num)
  have h_littleO : (fun w => f w - f 0) =o[𝓝 (0 : ℂ)] (fun w => ‖w - 0‖ ^ 1) := by
    have h1 : HasFDerivAt f (0 : ℂ →L[ℂ] ℂ) 0 := by
      have h' := hdiff0.hasDerivAt
      rw [hderiv0] at h'
      simpa using h'.hasFDerivAt
    simpa [pow_one] using h1.isLittleO.norm_right
  have hmaps : MapsTo f (Metric.ball 0 (1 / 2)) (Metric.closedBall (f 0) M) := fun w hw => by
    rw [Metric.mem_closedBall, dist_eq_norm, hzero, sub_zero]
    exact hbd w hw
  have hsch := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps h_littleO hz
  rw [dist_eq_norm, dist_eq_norm, hzero, sub_zero, sub_zero] at hsch
  calc ‖f z‖ ≤ M * (‖z‖ / (1 / 2)) ^ (1 + 1 : ℕ) := hsch
    _ = 4 * M * ‖z‖ ^ 2 := by ring

private lemma spinDaC_neg_left (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) :
    spinDaC a Φ (-bL) bR = spinDaC a Φ bL bR := by
  unfold spinDaC
  congr 1; refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [mul_neg, Complex.cos_neg]

private lemma spinDaC_neg_right (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) :
    spinDaC a Φ bL (-bR) = spinDaC a Φ bL bR := by
  unfold spinDaC
  congr 1; refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [mul_neg, Complex.cos_neg]

private lemma spinDaC_zero_left (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bR : ℂ) :
    spinDaC a Φ 0 bR = 0 := by
  unfold spinDaC
  simp

private lemma spinDaC_zero_right (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL : ℂ) :
    spinDaC a Φ bL 0 = 0 := by
  unfold spinDaC
  simp

private lemma spinDaC_continuousOn_bistrip {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    ContinuousOn (fun q : ℂ × ℂ => spinDaC a Φ q.1 q.2)
      ({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2}) := by
  have ha0 : 0 < a := by linarith
  intro q₀ hq₀
  have hball_mem : (Metric.ball q₀.1 1 ×ˢ Metric.ball q₀.2 1) ∩
      ({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2}) ∈
      𝓝[({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2})] q₀ := by
    have hmem : Metric.ball q₀.1 1 ×ˢ Metric.ball q₀.2 1 ∈ 𝓝 q₀ := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Metric.ball_mem_nhds q₀.1 one_pos) (Metric.ball_mem_nhds q₀.2 one_pos)
    rw [Set.inter_comm]
    exact inter_mem_nhdsWithin _ hmem
  let R : ℝ := max (‖q₀.1‖ + 1) (‖q₀.2‖ + 1)
  let C_R : ℝ := (1 + 4 * R ^ 2) ^ 2
  have hint_dom : Integrable (fun p : ℝ × ℝ => C_R * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) volume :=
    hΦ.int_M2.const_mul C_R
  let F : ℂ × ℂ → ℝ × ℝ → ℂ := fun q p =>
    (Φ p : ℂ) * spinWa a p.1 q.1 * spinWa a p.2 q.2
  have hF_meas : ∀ᶠ q in 𝓝[({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2})] q₀,
      AEStronglyMeasurable (F q) volume :=
    Eventually.of_forall fun q => by
      have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 q.1 * spinWa a p.2 q.2) := by
        unfold spinWa; fun_prop
      exact ((h1.mul h2).congr (fun p => by dsimp [F]; ring)).aestronglyMeasurable
  have hF_bd : ∀ᶠ q in 𝓝[({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2})] q₀,
      ∀ᵐ p : ℝ × ℝ, ‖F q p‖ ≤ C_R * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    filter_upwards [hball_mem] with q ⟨hq_ball, hq_strip⟩
    refine Eventually.of_forall fun p => ?_
    have hre1 : |q.1.re| ≤ R := by
      have h1 : ‖q.1‖ ≤ ‖q₀.1‖ + 1 := by
        have htri : ‖q.1‖ ≤ ‖q₀.1‖ + ‖q.1 - q₀.1‖ := by
          calc ‖q.1‖ = ‖q₀.1 + (q.1 - q₀.1)‖ := by ring_nf
            _ ≤ ‖q₀.1‖ + ‖q.1 - q₀.1‖ := norm_add_le _ _
        have hd : ‖q.1 - q₀.1‖ < 1 := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hq_ball.1
        linarith
      exact (Complex.abs_re_le_norm q.1).trans (h1.trans (le_max_left _ _))
    have hre2 : |q.2.re| ≤ R := by
      have h1 : ‖q.2‖ ≤ ‖q₀.2‖ + 1 := by
        have htri : ‖q.2‖ ≤ ‖q₀.2‖ + ‖q.2 - q₀.2‖ := by
          calc ‖q.2‖ = ‖q₀.2 + (q.2 - q₀.2)‖ := by ring_nf
            _ ≤ ‖q₀.2‖ + ‖q.2 - q₀.2‖ := norm_add_le _ _
        have hd : ‖q.2 - q₀.2‖ < 1 := by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hq_ball.2
        linarith
      exact (Complex.abs_re_le_norm q.2).trans (h1.trans (le_max_right _ _))
    have hw1 := norm_spinWa_le ha p.1 hq_strip.1
    have hw2 := norm_spinWa_le ha p.2 hq_strip.2
    have h1 : 1 + 4 * q.1.re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : q.1.re ^ 2 ≤ R ^ 2 := by rw [← sq_abs q.1.re]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      linarith
    have h2 : 1 + 4 * q.2.re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : q.2.re ^ 2 ≤ R ^ 2 := by rw [← sq_abs q.2.re]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
      linarith
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Φ p| * ‖spinWa a p.1 q.1‖ * ‖spinWa a p.2 q.2‖
        ≤ |Φ p| * ((1 + 4 * R ^ 2) * spinV1 a p.1) * ((1 + 4 * R ^ 2) * spinV1 a p.2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hw1.trans (mul_le_mul_of_nonneg_right h1 (spinV1_nonneg ha p.1))) (abs_nonneg _))
            (hw2.trans (mul_le_mul_of_nonneg_right h2 (spinV1_nonneg ha p.2))) (norm_nonneg _)
            (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (spinV1_nonneg ha p.1)))
      _ = C_R * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by dsimp [C_R]; ring
  have hF_lim : ∀ᵐ p : ℝ × ℝ, Tendsto (fun q : ℂ × ℂ => F q p)
      (𝓝[({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2})] q₀) (𝓝 (F q₀ p)) := by
    refine Eventually.of_forall fun p => ?_
    have hc : Continuous (fun q : ℂ × ℂ => F q p) := by dsimp [F, spinWa]; fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := (tendsto_integral_filter_of_dominated_convergence _ hF_meas hF_bd hint_dom hF_lim).neg
  simpa [ContinuousWithinAt, spinDaC_eq_spinWa, F] using ht

private lemma norm_spinDaC_le_64 {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bL bR : ℂ} (hbL : ‖bL‖ ≤ 1 / 2) (hbR : ‖bR‖ ≤ 1 / 2) :
    ‖spinDaC a Φ bL bR‖ ≤ 64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 := by
  have hm_nn : 0 ≤ spinM2 a Φ := spinM2_nonneg ha Φ
  have hball_sub : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), z ∈ spinStrip (1 / 2) := fun z hz => by
    calc |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      _ < 1 / 2 := mem_ball_zero_iff.mp hz
  have hstrip_bd : ∀ z₁ z₂ : ℂ, ‖z₁‖ ≤ 1 / 2 → ‖z₂‖ ≤ 1 / 2 →
      ‖spinDaC a Φ z₁ z₂‖ ≤ 4 * spinM2 a Φ := fun z₁ z₂ hz₁ hz₂ => by
    have him1 : |z₁.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z₁).trans hz₁
    have him2 : |z₂.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z₂).trans hz₂
    have hre1 : z₁.re ^ 2 ≤ 1 / 4 := by
      have : |z₁.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z₁).trans hz₁
      rw [← sq_abs z₁.re]; linarith [pow_le_pow_left₀ (abs_nonneg _) this 2]
    have hre2 : z₂.re ^ 2 ≤ 1 / 4 := by
      have : |z₂.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z₂).trans hz₂
      rw [← sq_abs z₂.re]; linarith [pow_le_pow_left₀ (abs_nonneg _) this 2]
    calc ‖spinDaC a Φ z₁ z₂‖
        ≤ (1 + 4 * z₁.re ^ 2) * (1 + 4 * z₂.re ^ 2) * spinM2 a Φ := norm_spinDaC_le ha hΦ him1 him2
      _ ≤ (1 + 4 * (1 / 4)) * (1 + 4 * (1 / 4)) * spinM2 a Φ := by gcongr
      _ = 4 * spinM2 a Φ := by ring
  have hopen_bd : ∀ z₁ ∈ Metric.ball (0 : ℂ) (1 / 2), ∀ z₂ ∈ Metric.ball (0 : ℂ) (1 / 2),
      ‖spinDaC a Φ z₁ z₂‖ ≤ 64 * spinM2 a Φ * ‖z₁‖ ^ 2 * ‖z₂‖ ^ 2 := by
    intro z₁ hz₁ z₂ hz₂
    have h1 : ∀ w₂ ∈ Metric.ball (0 : ℂ) (1 / 2),
        ‖spinDaC a Φ z₁ w₂‖ ≤ 16 * spinM2 a Φ * ‖z₁‖ ^ 2 := fun w₂ hw₂ => by
      have hsch1 := schwarz_sq_of_even_zero (M := 4 * spinM2 a Φ) (by positivity)
        ((differentiableOn_spinDaC_left ha hΦ (hball_sub w₂ hw₂)).mono hball_sub)
        (fun w => spinDaC_neg_left a Φ w w₂) (spinDaC_zero_left a Φ w₂)
        (fun w hw => hstrip_bd w w₂ (mem_ball_zero_iff.mp hw).le (mem_ball_zero_iff.mp hw₂).le)
        z₁ hz₁
      linarith
    have hsch2 := schwarz_sq_of_even_zero (M := 16 * spinM2 a Φ * ‖z₁‖ ^ 2) (by positivity)
        ((differentiableOn_spinDaC_right ha hΦ (hball_sub z₁ hz₁)).mono hball_sub)
        (fun w => spinDaC_neg_right a Φ z₁ w) (spinDaC_zero_right a Φ z₁)
        h1 z₂ hz₂
    linarith
  let seq : ℕ → ℂ × ℂ := fun n =>
    (((1 - 1 / (n + 2 : ℝ) : ℝ) : ℂ) * bL, ((1 - 1 / (n + 2 : ℝ) : ℝ) : ℂ) * bR)
  have hseq_mem : ∀ n : ℕ, (seq n).1 ∈ Metric.ball (0 : ℂ) (1 / 2) ∧
      (seq n).2 ∈ Metric.ball (0 : ℂ) (1 / 2) := fun n => by
    have hn : (0 : ℝ) < 1 - 1 / (n + 2 : ℝ) := by
      have : (1 : ℝ) / (n + 2 : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
      linarith
    have hn_lt : 1 - 1 / (n + 2 : ℝ) < 1 := by
      have : (0 : ℝ) < 1 / (n + 2 : ℝ) := by positivity
      linarith
    constructor <;> simp only [seq, mem_ball_zero_iff, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn]
    · calc (1 - 1 / (n + 2 : ℝ)) * ‖bL‖ ≤ (1 - 1 / (n + 2 : ℝ)) * (1 / 2) := by gcongr
        _ < 1 * (1 / 2) := by gcongr
        _ = 1 / 2 := one_mul _
    · calc (1 - 1 / (n + 2 : ℝ)) * ‖bR‖ ≤ (1 - 1 / (n + 2 : ℝ)) * (1 / 2) := by gcongr
        _ < 1 * (1 / 2) := by gcongr
        _ = 1 / 2 := one_mul _
  have hseq_strip : ∀ n : ℕ, seq n ∈ ({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2}) := fun n =>
    ⟨(Complex.abs_im_le_norm _).trans (mem_ball_zero_iff.mp (hseq_mem n).1).le,
     (Complex.abs_im_le_norm _).trans (mem_ball_zero_iff.mp (hseq_mem n).2).le⟩
  have hq_strip : (bL, bR) ∈ ({b : ℂ | |b.im| ≤ 1 / 2} ×ˢ {b : ℂ | |b.im| ≤ 1 / 2}) :=
    ⟨(Complex.abs_im_le_norm bL).trans hbL, (Complex.abs_im_le_norm bR).trans hbR⟩
  have hseq_lim : Tendsto seq atTop (𝓝 (bL, bR)) := by
    have hcoeff : Tendsto (fun n : ℕ => ((1 - 1 / (n + 2 : ℝ) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).congr
            (fun n => by simp [Function.comp_def]))
      have hr : Tendsto (fun n : ℕ => 1 - 1 / (n + 2 : ℝ)) atTop (𝓝 (1 - 0 : ℝ)) :=
        tendsto_const_nhds.sub hinv
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
      simpa [Function.comp_def] using hc
    have hprod := (hcoeff.mul_const bL).prodMk_nhds (hcoeff.mul_const bR)
    simpa [seq] using hprod
  have hcont_seq : Tendsto (fun n : ℕ => ‖spinDaC a Φ (seq n).1 (seq n).2‖) atTop
      (𝓝 ‖spinDaC a Φ bL bR‖) := by
    have hc := (spinDaC_continuousOn_bistrip ha hΦ (bL, bR) hq_strip).tendsto
    exact (continuous_norm.continuousAt.tendsto.comp hc).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hseq_lim, Eventually.of_forall hseq_strip⟩)
  have hrhs_lim : Tendsto (fun n : ℕ => 64 * spinM2 a Φ * ‖(seq n).1‖ ^ 2 * ‖(seq n).2‖ ^ 2) atTop
      (𝓝 (64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2)) := by
    have h1 : Tendsto (fun n : ℕ => ‖(seq n).1‖) atTop (𝓝 ‖bL‖) :=
      (continuous_norm.comp continuous_fst).continuousAt.tendsto.comp hseq_lim
    have h2 : Tendsto (fun n : ℕ => ‖(seq n).2‖) atTop (𝓝 ‖bR‖) :=
      (continuous_norm.comp continuous_snd).continuousAt.tendsto.comp hseq_lim
    exact (((tendsto_const_nhds.mul (h1.pow 2)).mul (h2.pow 2)).congr (fun n => by ring))
  exact le_of_tendsto_of_tendsto hcont_seq hrhs_lim
    (Eventually.of_forall fun n => hopen_bd (seq n).1 (hseq_mem n).1 (seq n).2 (hseq_mem n).2)

/-! ### Section 5: Double inward telescope and `SpinS24` -/

private lemma spinDaC_eq_spinGC_diff {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {bL bR : ℂ} (hbL : bL ∈ spinStrip (1 / 2))
    (hbR : bR ∈ spinStrip (1 / 2)) :
    spinDaC a Φ bL bR =
      spinGC a Φ bL bR - spinGC a Φ ((spinGamma a : ℂ) * bL) bR -
        spinGC a Φ bL ((spinGamma a : ℂ) * bR) +
        spinGC a Φ ((spinGamma a : ℂ) * bL) ((spinGamma a : ℂ) * bR) := by
  have ha0 : 0 < a := by linarith
  have hgam_nn : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hgam_lt : spinGamma a < 1 := by
    unfold spinGamma
    exact (Real.sqrt_lt' one_pos).mpr (by have : 0 < 2 / a := div_pos two_pos ha0; linarith)
  have hsq_gam : Real.sqrt (a - 2) = Real.sqrt a * spinGamma a := by
    unfold spinGamma
    rw [← Real.sqrt_mul ha0.le]
    congr 1; field_simp [ha0.ne']
  let θ : ℝ := max (1 / 24) (max |bL.im| |bR.im|)
  have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hθ1 : θ < 1 / 2 := max_lt (by norm_num) (max_lt hbL hbR)
  have hint_θ := integrable_spinITheta ha hθ0 hθ1 hΦ
  have hint_term : ∀ w₁ w₂ : ℂ, |w₁.im| ≤ θ → |w₂.im| ≤ θ →
      Integrable (fun p : ℝ × ℝ => (Φ p : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w₁) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * w₂)) volume := by
    intro w₁ w₂ hw₁ hw₂
    refine hint_θ.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ =>
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w₁) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * w₂)) := by fun_prop
      exact ((h1.mul h2).congr (fun p => by dsimp only [Pi.mul_apply]; ring)).aestronglyMeasurable
    · have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w₁).im = 4 * π * Real.sqrt a * p.1 * w₁.im := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * w₂).im = 4 * π * Real.sqrt a * p.2 * w₂.im := by
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * w₁)‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ * p.1) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * w₁.im) := by
              rw [← him1]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.1) := cosh_mul_im_le_cosh ha0 hθ0.le hw₁
      have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * w₂)‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ * p.2) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * w₂.im) := by
              rw [← him2]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.2) := cosh_mul_im_le_cosh ha0 hθ0.le hw₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
        (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  have hbL_le : |bL.im| ≤ θ := (le_max_left _ _).trans (le_max_right _ _)
  have hbR_le : |bR.im| ≤ θ := (le_max_right _ _).trans (le_max_right _ _)
  have hgbL_le : |((spinGamma a : ℂ) * bL).im| ≤ θ := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
      abs_of_nonneg hgam_nn]
    exact (mul_le_of_le_one_left (abs_nonneg _) hgam_lt.le).trans hbL_le
  have hgbR_le : |((spinGamma a : ℂ) * bR).im| ≤ θ := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
      abs_of_nonneg hgam_nn]
    exact (mul_le_of_le_one_left (abs_nonneg _) hgam_lt.le).trans hbR_le
  have h11 := hint_term bL bR hbL_le hbR_le
  have h21 := hint_term ((spinGamma a : ℂ) * bL) bR hgbL_le hbR_le
  have h12 := hint_term bL ((spinGamma a : ℂ) * bR) hbL_le hgbR_le
  have h22 := hint_term ((spinGamma a : ℂ) * bL) ((spinGamma a : ℂ) * bR) hgbL_le hgbR_le
  unfold spinDaC spinGC
  have hpt : ∀ p : ℝ × ℝ,
      (Φ p : ℂ) *
        (Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) -
          Complex.cos (4 * π * (Real.sqrt (a - 2) : ℂ) * (p.1 : ℂ) * bL)) *
        (Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR) -
          Complex.cos (4 * π * (Real.sqrt (a - 2) : ℂ) * (p.2 : ℂ) * bR)) =
      ((Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR) -
      (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a : ℂ) * bL)) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)) -
      ((Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a : ℂ) * bR)) -
      (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a : ℂ) * bL)) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a : ℂ) * bR))) := by
    intro p
    have he1 : 4 * π * (Real.sqrt (a - 2) : ℂ) * (p.1 : ℂ) * bL =
        4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a : ℂ) * bL) := by
      rw [hsq_gam]; push_cast; ring
    have he2 : 4 * π * (Real.sqrt (a - 2) : ℂ) * (p.2 : ℂ) * bR =
        4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a : ℂ) * bR) := by
      rw [hsq_gam]; push_cast; ring
    rw [he1, he2]; ring
  simp_rw [hpt]
  let f11 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)
  let f21 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a : ℂ) * bL)) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * bR)
  let f12 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * bL) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a : ℂ) * bR))
  let f22 : ℝ × ℝ → ℂ := fun p => (Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * ((spinGamma a : ℂ) * bL)) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * ((spinGamma a : ℂ) * bR))
  have hsub1 : Integrable (fun p : ℝ × ℝ => f11 p - f21 p) volume := h11.sub h21
  have hsub2 : Integrable (fun p : ℝ × ℝ => f12 p - f22 p) volume := h12.sub h22
  change -(∫ p : ℝ × ℝ, (f11 p - f21 p) - (f12 p - f22 p)) =
    (-(∫ p : ℝ × ℝ, f11 p)) - (-(∫ p : ℝ × ℝ, f21 p)) - (-(∫ p : ℝ × ℝ, f12 p)) + (-(∫ p : ℝ × ℝ, f22 p))
  rw [integral_sub hsub1 hsub2, integral_sub h11 h21, integral_sub h12 h22]
  ring

private lemma spinDaC_rect_sum {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    {bL bR : ℂ} (hbL : bL ∈ spinStrip (1 / 2)) (hbR : bR ∈ spinStrip (1 / 2)) (M L : ℕ) :
    ∑ q ∈ Finset.range M ×ˢ Finset.range L,
      spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR) =
      spinGC a Φ bL bR - spinGC a Φ ((spinGamma a ^ M : ℝ) * bL) bR -
        spinGC a Φ bL ((spinGamma a ^ L : ℝ) * bR) +
        spinGC a Φ ((spinGamma a ^ M : ℝ) * bL) ((spinGamma a ^ L : ℝ) * bR) := by
  have ha0 : 0 < a := by linarith
  let γ : ℝ := spinGamma a
  have hγ_nn : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ_lt : γ < 1 := by
    dsimp [γ]; unfold spinGamma
    exact (Real.sqrt_lt' one_pos).mpr (by have : 0 < 2 / a := div_pos two_pos ha0; linarith)
  have hγ_pow_strip : ∀ (k : ℕ) {w : ℂ}, w ∈ spinStrip (1 / 2) →
      ((γ ^ k : ℝ) : ℂ) * w ∈ spinStrip (1 / 2) := fun k w hw => by
    have hpow_nn : 0 ≤ γ ^ k := pow_nonneg hγ_nn k
    have hpow_le : γ ^ k ≤ 1 := pow_le_one₀ hγ_nn hγ_lt.le
    change |(((γ ^ k : ℝ) : ℂ) * w).im| < 1 / 2
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
      abs_of_nonneg hpow_nn]
    exact (mul_le_of_le_one_left (abs_nonneg _) hpow_le).trans_lt hw
  let f : ℕ × ℕ → ℂ := fun q =>
    spinDaC a Φ ((γ ^ q.1 : ℝ) * bL) ((γ ^ q.2 : ℝ) * bR)
  change ∑ q ∈ Finset.range M ×ˢ Finset.range L, f q = _
  rw [Finset.sum_product]
  have hinner : ∀ m : ℕ, ∑ l ∈ Finset.range L, f (m, l) =
      (spinGC a Φ ((γ ^ m : ℝ) * bL) bR - spinGC a Φ ((γ ^ (m + 1) : ℝ) * bL) bR) -
      (spinGC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ L : ℝ) * bR) -
        spinGC a Φ ((γ ^ (m + 1) : ℝ) * bL) ((γ ^ L : ℝ) * bR)) := by
    intro m
    have hterm : ∀ l : ℕ, f (m, l) =
        (spinGC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ l : ℝ) * bR) -
          spinGC a Φ ((γ ^ (m + 1) : ℝ) * bL) ((γ ^ l : ℝ) * bR)) -
        (spinGC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ (l + 1) : ℝ) * bR) -
          spinGC a Φ ((γ ^ (m + 1) : ℝ) * bL) ((γ ^ (l + 1) : ℝ) * bR)) := fun l => by
      dsimp [f]
      have heq := spinDaC_eq_spinGC_diff ha hΦ (hγ_pow_strip m hbL) (hγ_pow_strip l hbR)
      have hgm : (γ : ℂ) * (((γ ^ m : ℝ) : ℂ) * bL) = ((γ ^ (m + 1) : ℝ) : ℂ) * bL := by
        push_cast; rw [pow_succ']; ring
      have hgl : (γ : ℂ) * (((γ ^ l : ℝ) : ℂ) * bR) = ((γ ^ (l + 1) : ℝ) : ℂ) * bR := by
        push_cast; rw [pow_succ']; ring
      rw [hgm, hgl] at heq
      rw [heq]; ring
    simp_rw [hterm]
    rw [Finset.sum_range_sub' (fun l =>
      spinGC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ l : ℝ) * bR) -
      spinGC a Φ ((γ ^ (m + 1) : ℝ) * bL) ((γ ^ l : ℝ) * bR)) L]
    simp [pow_zero]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun m => spinGC a Φ ((γ ^ m : ℝ) * bL) bR) M,
    Finset.sum_range_sub' (fun m => spinGC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ L : ℝ) * bR)) M]
  simp [pow_zero]
  ring

private lemma spinDaC_summable {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    {bL bR : ℂ} (hbL : bL ∈ spinStrip (1 / 2)) (hbR : bR ∈ spinStrip (1 / 2)) :
    Summable (fun q : ℕ × ℕ =>
      ‖spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR)‖) := by
  have ha0 : 0 < a := by linarith
  let γ : ℝ := spinGamma a
  have hγ_nn : 0 ≤ γ := Real.sqrt_nonneg _
  have hγ_lt : γ < 1 := by
    dsimp [γ]; unfold spinGamma
    exact (Real.sqrt_lt' one_pos).mpr (by have : 0 < 2 / a := div_pos two_pos ha0; linarith)
  have hγ_pow_strip : ∀ (k : ℕ) {w : ℂ}, w ∈ spinStrip (1 / 2) →
      ((γ ^ k : ℝ) : ℂ) * w ∈ spinStrip (1 / 2) := fun k w hw => by
    have hpow_nn : 0 ≤ γ ^ k := pow_nonneg hγ_nn k
    have hpow_le : γ ^ k ≤ 1 := pow_le_one₀ hγ_nn hγ_lt.le
    change |(((γ ^ k : ℝ) : ℂ) * w).im| < 1 / 2
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
      abs_of_nonneg hpow_nn]
    exact (mul_le_of_le_one_left (abs_nonneg _) hpow_le).trans_lt hw
  let f : ℕ × ℕ → ℂ := fun q =>
    spinDaC a Φ ((γ ^ q.1 : ℝ) * bL) ((γ ^ q.2 : ℝ) * bR)
  change Summable (fun q : ℕ × ℕ => ‖f q‖)
  have hpow_lim : Tendsto (fun k : ℕ => γ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ_nn hγ_lt
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((hpow_lim.mul_const ‖bL‖).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) * ‖bL‖ < 1 / 2)))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    ((hpow_lim.mul_const ‖bR‖).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) * ‖bR‖ < 1 / 2)))
  let N : ℕ := max N₁ N₂
  have hbd_tail : ∀ m l : ℕ, N ≤ m → N ≤ l →
      ‖f (m, l)‖ ≤ 64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ m * (γ ^ 2) ^ l := fun m l hm hl => by
    have hm1 : ‖((γ ^ m : ℝ) : ℂ) * bL‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn m)]
      exact (hN₁ m (le_trans (le_max_left _ _) hm)).le
    have hl1 : ‖((γ ^ l : ℝ) : ℂ) * bR‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn l)]
      exact (hN₂ l (le_trans (le_max_right _ _) hl)).le
    have h64 := norm_spinDaC_le_64 ha hΦ hm1 hl1
    dsimp [f]
    calc ‖spinDaC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ l : ℝ) * bR)‖
        ≤ 64 * spinM2 a Φ * ‖((γ ^ m : ℝ) : ℂ) * bL‖ ^ 2 * ‖((γ ^ l : ℝ) : ℂ) * bR‖ ^ 2 := h64
      _ = 64 * spinM2 a Φ * (γ ^ m * ‖bL‖) ^ 2 * (γ ^ l * ‖bR‖) ^ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn m),
            norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn l)]
      _ = 64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ m * (γ ^ 2) ^ l := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, mul_comm l 2, pow_mul, pow_mul]
          ring
  let R_re : ℝ := max (max ‖bL‖ ‖bR‖) (1 / 2)
  let C_unif : ℝ := (1 + 4 * R_re ^ 2) ^ 2 * spinM2 a Φ
  have hC_unif : 0 ≤ C_unif := by
    have := spinM2_nonneg ha Φ; positivity
  have hball_sub : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2), z ∈ spinStrip (1 / 2) := fun z hz =>
    (Complex.abs_im_le_norm z).trans_lt (mem_ball_zero_iff.mp hz)
  have hbd_all : ∀ m l : ℕ, ‖f (m, l)‖ ≤ C_unif := fun m l => by
    have him1 : |(((γ ^ m : ℝ) : ℂ) * bL).im| ≤ 1 / 2 := (hγ_pow_strip m hbL).le
    have him2 : |(((γ ^ l : ℝ) : ℂ) * bR).im| ≤ 1 / 2 := (hγ_pow_strip l hbR).le
    have hre1 : |(((γ ^ m : ℝ) : ℂ) * bL).re| ≤ R_re := by
      calc |(((γ ^ m : ℝ) : ℂ) * bL).re| ≤ ‖((γ ^ m : ℝ) : ℂ) * bL‖ := Complex.abs_re_le_norm _
        _ = γ ^ m * ‖bL‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn m)]
        _ ≤ 1 * ‖bL‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ hγ_nn hγ_lt.le) (norm_nonneg _)
        _ ≤ R_re := (one_mul _).le.trans ((le_max_left _ _).trans (le_max_left _ _))
    have hre2 : |(((γ ^ l : ℝ) : ℂ) * bR).re| ≤ R_re := by
      calc |(((γ ^ l : ℝ) : ℂ) * bR).re| ≤ ‖((γ ^ l : ℝ) : ℂ) * bR‖ := Complex.abs_re_le_norm _
        _ = γ ^ l * ‖bR‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn l)]
        _ ≤ 1 * ‖bR‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ hγ_nn hγ_lt.le) (norm_nonneg _)
        _ ≤ R_re := (one_mul _).le.trans ((le_max_right _ _).trans (le_max_left _ _))
    have h1 : (((γ ^ m : ℝ) : ℂ) * bL).re ^ 2 ≤ R_re ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
    have h2 : (((γ ^ l : ℝ) : ℂ) * bR).re ^ 2 ≤ R_re ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
    have hm_nn := spinM2_nonneg ha Φ
    calc ‖f (m, l)‖ ≤ (1 + 4 * (((γ ^ m : ℝ) : ℂ) * bL).re ^ 2) *
          (1 + 4 * (((γ ^ l : ℝ) : ℂ) * bR).re ^ 2) * spinM2 a Φ :=
        norm_spinDaC_le ha hΦ him1 him2
      _ ≤ (1 + 4 * R_re ^ 2) * (1 + 4 * R_re ^ 2) * spinM2 a Φ := by gcongr
      _ = C_unif := by dsimp [C_unif]; ring
  have hbd_strip_L : ∀ m l : ℕ, N ≤ m →
      ‖f (m, l)‖ ≤ 4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ m := fun m l hm => by
    have h_bL_ball : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2),
        ‖spinDaC a Φ z ((γ ^ l : ℝ) * bR)‖ ≤ C_unif := fun z hz => by
      have him1 : |z.im| ≤ 1 / 2 := (hball_sub z hz).le
      have him2 : |(((γ ^ l : ℝ) : ℂ) * bR).im| ≤ 1 / 2 := (hγ_pow_strip l hbR).le
      have hre1 : |z.re| ≤ R_re :=
        (Complex.abs_re_le_norm z).trans ((mem_ball_zero_iff.mp hz).le.trans (le_max_right _ _))
      have hre2 : |(((γ ^ l : ℝ) : ℂ) * bR).re| ≤ R_re := by
        calc |(((γ ^ l : ℝ) : ℂ) * bR).re| ≤ ‖((γ ^ l : ℝ) : ℂ) * bR‖ := Complex.abs_re_le_norm _
          _ = γ ^ l * ‖bR‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn l)]
          _ ≤ 1 * ‖bR‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ hγ_nn hγ_lt.le) (norm_nonneg _)
          _ ≤ R_re := (one_mul _).le.trans ((le_max_right _ _).trans (le_max_left _ _))
      have h1 : z.re ^ 2 ≤ R_re ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      have h2 : (((γ ^ l : ℝ) : ℂ) * bR).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
      have hm_nn := spinM2_nonneg ha Φ
      calc ‖spinDaC a Φ z ((γ ^ l : ℝ) * bR)‖
          ≤ (1 + 4 * z.re ^ 2) * (1 + 4 * (((γ ^ l : ℝ) : ℂ) * bR).re ^ 2) * spinM2 a Φ :=
            norm_spinDaC_le ha hΦ him1 him2
        _ ≤ (1 + 4 * R_re ^ 2) * (1 + 4 * R_re ^ 2) * spinM2 a Φ := by gcongr
        _ = C_unif := by dsimp [C_unif]; ring
    have hm1 : ((γ ^ m : ℝ) : ℂ) * bL ∈ Metric.ball (0 : ℂ) (1 / 2) := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hγ_nn m)]
      exact hN₁ m (le_trans (le_max_left _ _) hm)
    have hsch := schwarz_sq_of_even_zero hC_unif
      ((differentiableOn_spinDaC_left ha hΦ (hγ_pow_strip l hbR)).mono hball_sub)
      (fun w => spinDaC_neg_left a Φ w ((γ ^ l : ℝ) * bR))
      (spinDaC_zero_left a Φ ((γ ^ l : ℝ) * bR))
      h_bL_ball ((γ ^ m : ℝ) * bL) hm1
    dsimp [f]
    calc ‖spinDaC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ l : ℝ) * bR)‖
        ≤ 4 * C_unif * ‖((γ ^ m : ℝ) : ℂ) * bL‖ ^ 2 := hsch
      _ = 4 * C_unif * (γ ^ m * ‖bL‖) ^ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn m)]
      _ = 4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ m := by
          rw [mul_pow, ← pow_mul, mul_comm m 2, pow_mul]; ring
  have hbd_strip_R : ∀ m l : ℕ, N ≤ l →
      ‖f (m, l)‖ ≤ 4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ l := fun m l hl => by
    have h_bR_ball : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2),
        ‖spinDaC a Φ ((γ ^ m : ℝ) * bL) z‖ ≤ C_unif := fun z hz => by
      have him1 : |(((γ ^ m : ℝ) : ℂ) * bL).im| ≤ 1 / 2 := (hγ_pow_strip m hbL).le
      have him2 : |z.im| ≤ 1 / 2 := (hball_sub z hz).le
      have hre1 : |(((γ ^ m : ℝ) : ℂ) * bL).re| ≤ R_re := by
        calc |(((γ ^ m : ℝ) : ℂ) * bL).re| ≤ ‖((γ ^ m : ℝ) : ℂ) * bL‖ := Complex.abs_re_le_norm _
          _ = γ ^ m * ‖bL‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn m)]
          _ ≤ 1 * ‖bL‖ := mul_le_mul_of_nonneg_right (pow_le_one₀ hγ_nn hγ_lt.le) (norm_nonneg _)
          _ ≤ R_re := (one_mul _).le.trans ((le_max_left _ _).trans (le_max_left _ _))
      have hre2 : |z.re| ≤ R_re :=
        (Complex.abs_re_le_norm z).trans ((mem_ball_zero_iff.mp hz).le.trans (le_max_right _ _))
      have h1 : (((γ ^ m : ℝ) : ℂ) * bL).re ^ 2 ≤ R_re ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      have h2 : z.re ^ 2 ≤ R_re ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
      have hm_nn := spinM2_nonneg ha Φ
      calc ‖spinDaC a Φ ((γ ^ m : ℝ) * bL) z‖
          ≤ (1 + 4 * (((γ ^ m : ℝ) : ℂ) * bL).re ^ 2) * (1 + 4 * z.re ^ 2) * spinM2 a Φ :=
            norm_spinDaC_le ha hΦ him1 him2
        _ ≤ (1 + 4 * R_re ^ 2) * (1 + 4 * R_re ^ 2) * spinM2 a Φ := by gcongr
        _ = C_unif := by dsimp [C_unif]; ring
    have hl1 : ((γ ^ l : ℝ) : ℂ) * bR ∈ Metric.ball (0 : ℂ) (1 / 2) := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hγ_nn l)]
      exact hN₂ l (le_trans (le_max_right _ _) hl)
    have hsch := schwarz_sq_of_even_zero hC_unif
      ((differentiableOn_spinDaC_right ha hΦ (hγ_pow_strip m hbL)).mono hball_sub)
      (fun w => spinDaC_neg_right a Φ ((γ ^ m : ℝ) * bL) w)
      (spinDaC_zero_right a Φ ((γ ^ m : ℝ) * bL))
      h_bR_ball ((γ ^ l : ℝ) * bR) hl1
    dsimp [f]
    calc ‖spinDaC a Φ ((γ ^ m : ℝ) * bL) ((γ ^ l : ℝ) * bR)‖
        ≤ 4 * C_unif * ‖((γ ^ l : ℝ) : ℂ) * bR‖ ^ 2 := hsch
      _ = 4 * C_unif * (γ ^ l * ‖bR‖) ^ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ_nn l)]
      _ = 4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ l := by
          rw [mul_pow, ← pow_mul, mul_comm l 2, pow_mul]; ring
  have hγ2_nn : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hγ2_lt : γ ^ 2 < 1 := pow_lt_one₀ hγ_nn hγ_lt (by norm_num)
  have hgeom : Summable (fun k : ℕ => (γ ^ 2) ^ k) := summable_geometric_of_lt_one hγ2_nn hγ2_lt
  have hind : Summable (fun k : ℕ => if k < N then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range N) fun k hk => ?_
    simp [Finset.mem_range.not.mp hk]
  have hs1 : Summable (fun q : ℕ × ℕ => (if q.1 < N ∧ q.2 < N then C_unif else 0)) := by
    refine summable_of_ne_finset_zero (s := Finset.range N ×ˢ Finset.range N) fun q hq => ?_
    simp only [Finset.mem_product, Finset.mem_range, not_and] at hq
    split_ifs with h
    · exact absurd h.2 (hq h.1)
    · rfl
  have hs2 : Summable (fun q : ℕ × ℕ =>
      (if q.1 < N then (1 : ℝ) else 0) * (4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.2)) :=
    hind.mul_of_nonneg (hgeom.mul_left _) (fun k => by dsimp; split_ifs <;> norm_num)
      (fun k => by positivity)
  have hs3 : Summable (fun q : ℕ × ℕ =>
      (4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ q.1) * (if q.2 < N then (1 : ℝ) else 0)) :=
    (hgeom.mul_left _).mul_of_nonneg hind (fun k => by positivity)
      (fun k => by dsimp; split_ifs <;> norm_num)
  have hs4 : Summable (fun q : ℕ × ℕ =>
      (64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.1) * (γ ^ 2) ^ q.2) :=
    (hgeom.mul_left _).mul_of_nonneg hgeom (fun k => by
      have := spinM2_nonneg ha Φ; positivity) (fun k => pow_nonneg hγ2_nn k)
  refine (((hs1.add hs2).add hs3).add hs4).of_norm_bounded fun q => ?_
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hm_nn := spinM2_nonneg ha Φ
  have h1_nn : 0 ≤ (if q.1 < N ∧ q.2 < N then C_unif else 0) := by split_ifs <;> linarith
  have h2_nn : 0 ≤ (if q.1 < N then (1 : ℝ) else 0) * (4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.2) := by
    split_ifs <;> positivity
  have h3_nn : 0 ≤ (4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ q.1) * (if q.2 < N then (1 : ℝ) else 0) := by
    split_ifs <;> positivity
  have h4_nn : 0 ≤ (64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.1) * (γ ^ 2) ^ q.2 := by
    positivity
  rcases lt_or_ge q.1 N with hq1 | hq1 <;> rcases lt_or_ge q.2 N with hq2 | hq2
  · exact le_trans (hbd_all q.1 q.2) (by
      have ha1 : (if q.1 < N ∧ q.2 < N then C_unif else 0) = C_unif := if_pos ⟨hq1, hq2⟩
      linarith)
  · exact le_trans (hbd_strip_R q.1 q.2 hq2) (by
      have ha2 : (if q.1 < N then (1 : ℝ) else 0) * (4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.2) =
          4 * C_unif * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.2 := by rw [if_pos hq1, one_mul]
      linarith)
  · exact le_trans (hbd_strip_L q.1 q.2 hq1) (by
      have ha3 : (4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ q.1) * (if q.2 < N then (1 : ℝ) else 0) =
          4 * C_unif * ‖bL‖ ^ 2 * (γ ^ 2) ^ q.1 := by rw [if_pos hq2, mul_one]
      linarith)
  · exact le_trans (hbd_tail q.1 q.2 hq1 hq2) (by
      have ha4 : (64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.1) * (γ ^ 2) ^ q.2 =
          64 * spinM2 a Φ * ‖bL‖ ^ 2 * ‖bR‖ ^ 2 * (γ ^ 2) ^ q.1 * (γ ^ 2) ^ q.2 := by ring
      linarith)

private lemma spinDaC_hasSum {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    {bL bR : ℂ} (hbL : bL ∈ spinStrip (1 / 2)) (hbR : bR ∈ spinStrip (1 / 2)) :
    HasSum (fun q : ℕ × ℕ =>
      spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR))
      (spinGC a Φ bL bR - spinGC a Φ bL 0 - spinGC a Φ 0 bR + spinGC a Φ 0 0) := by
  have ha0 : 0 < a := by linarith
  have hγ_nn : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hγ_lt : spinGamma a < 1 := by
    unfold spinGamma
    exact (Real.sqrt_lt' one_pos).mpr (by have : 0 < 2 / a := div_pos two_pos ha0; linarith)
  have hf_summable := spinDaC_summable ha hΦ hbL hbR
  have hs_tendsto : Tendsto (fun n : ℕ => Finset.range n ×ˢ Finset.range n) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro F
    refine ⟨F.sup (fun q => max q.1 q.2 + 1), fun n hn q hq => ?_⟩
    have hle : max q.1 q.2 + 1 ≤ n := (Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2 + 1) hq).trans hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hrect_lim : Tendsto (fun n : ℕ => ∑ q ∈ Finset.range n ×ˢ Finset.range n,
      spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR)) atTop
      (𝓝 (spinGC a Φ bL bR - spinGC a Φ bL 0 - spinGC a Φ 0 bR + spinGC a Φ 0 0)) := by
    have hpow_lim : Tendsto (fun n : ℕ => ((spinGamma a ^ n : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hγ_nn hγ_lt
      have h2 := Complex.continuous_ofReal.continuousAt.tendsto.comp h1
      simpa [Function.comp_def] using h2
    have hL_lim : Tendsto (fun n : ℕ => ((spinGamma a ^ n : ℝ) : ℂ) * bL) atTop (𝓝 (0 : ℂ)) := by
      simpa using hpow_lim.mul_const bL
    have hR_lim : Tendsto (fun n : ℕ => ((spinGamma a ^ n : ℝ) : ℂ) * bR) atTop (𝓝 (0 : ℂ)) := by
      simpa using hpow_lim.mul_const bR
    have hstrip_open : IsOpen (spinStrip (1 / 2)) := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    have h0_mem : (0 : ℂ) ∈ spinStrip (1 / 2) := by simp [spinStrip]
    have h1 : Tendsto (fun n : ℕ => spinGC a Φ (((spinGamma a ^ n : ℝ) : ℂ) * bL) bR) atTop
        (𝓝 (spinGC a Φ 0 bR)) :=
      ((spinGC_differentiableOn_left ha hΦ hbR).continuousOn.continuousAt
        (hstrip_open.mem_nhds h0_mem)).tendsto.comp hL_lim
    have h2 : Tendsto (fun n : ℕ => spinGC a Φ bL (((spinGamma a ^ n : ℝ) : ℂ) * bR)) atTop
        (𝓝 (spinGC a Φ bL 0)) :=
      ((spinGC_differentiableOn_right ha hΦ hbL).continuousOn.continuousAt
        (hstrip_open.mem_nhds h0_mem)).tendsto.comp hR_lim
    have hLR_lim : Tendsto (fun n : ℕ => (((spinGamma a ^ n : ℝ) : ℂ) * bL, ((spinGamma a ^ n : ℝ) : ℂ) * bR))
        atTop (𝓝 ((0 : ℂ), (0 : ℂ))) := hL_lim.prodMk_nhds hR_lim
    have h3 : Tendsto (fun n : ℕ => spinGC a Φ (((spinGamma a ^ n : ℝ) : ℂ) * bL) (((spinGamma a ^ n : ℝ) : ℂ) * bR))
        atTop (𝓝 (spinGC a Φ 0 0)) := by
      have hc0 := spinGC_continuousAt_zero ha hΦ
      have ht : Tendsto (fun n : ℕ => (fun q : ℂ × ℂ => spinGC a Φ q.1 q.2)
          ((((spinGamma a ^ n : ℝ) : ℂ) * bL, ((spinGamma a ^ n : ℝ) : ℂ) * bR))) atTop (𝓝 (spinGC a Φ 0 0)) :=
        hc0.tendsto.comp hLR_lim
      exact ht
    have hrect_eq : (fun n : ℕ => ∑ q ∈ Finset.range n ×ˢ Finset.range n,
        spinDaC a Φ ((spinGamma a ^ q.1 : ℝ) * bL) ((spinGamma a ^ q.2 : ℝ) * bR)) =
        fun n => spinGC a Φ bL bR - spinGC a Φ (((spinGamma a ^ n : ℝ) : ℂ) * bL) bR -
          spinGC a Φ bL (((spinGamma a ^ n : ℝ) : ℂ) * bR) +
          spinGC a Φ (((spinGamma a ^ n : ℝ) : ℂ) * bL) (((spinGamma a ^ n : ℝ) : ℂ) * bR) :=
      funext fun n => spinDaC_rect_sum ha hΦ hbL hbR n n
    rw [hrect_eq]
    have hcomb := (((tendsto_const_nhds (x := spinGC a Φ bL bR)).sub h1).sub h2).add h3
    rwa [sub_right_comm (spinGC a Φ bL bR) (spinGC a Φ 0 bR) (spinGC a Φ bL 0)] at hcomb
  exact hasSum_of_subseq_of_summable hf_summable hs_tendsto hrect_lim

/-- **Lemma S2.4 (`spinnotes:S24`)**: Sub-bistrip holomorphy, derivative bounds, and double inward telescope. -/
theorem spinS24 : SpinS24 := by
  refine ⟨?_, ?_⟩
  · intro c hc θ hθ0 hθ1
    have ha : 2 ≤ (c - 1) / 12 := by linarith
    obtain ⟨C, hC_pos, hI_bd⟩ := spinITheta_le ha hθ0 hθ1
    refine ⟨C, hC_pos, fun {Φ} hΦ => ?_⟩
    dsimp only
    refine ⟨integrable_spinITheta ha hθ0 hθ1 hΦ, hI_bd hΦ,
      fun bR hbR => spinGC_differentiableOn_left ha hΦ hbR,
      fun bL hbL => spinGC_differentiableOn_right ha hΦ hbL,
      fun xL xR => spinGC_ofReal ha hΦ xL xR,
      fun bL bR hbL hbR => (spinGC_norm_le_spinITheta ha hΦ hθ0 hθ1 hbL hbR).trans (hI_bd hΦ)⟩
  · intro c hc Φ hΦ
    have ha : 2 ≤ (c - 1) / 12 := by linarith
    exact ⟨fun bL bR hbL hbR => norm_spinDaC_le_64 ha hΦ hbL hbR,
      fun bL hbL bR hbR => spinDaC_hasSum ha hΦ hbL hbR⟩

#print axioms FormalResearch.ModularBootstrap.Spin.spinS24

end FormalResearch.ModularBootstrap.Spin

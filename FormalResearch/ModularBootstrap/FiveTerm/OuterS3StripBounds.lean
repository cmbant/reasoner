module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3S1Bounds

/-!
# FIVE-S, S3 (step 4b): interior strip bounds and branch-point lower bound

Proves the two remaining ingredients for the global strip bound in `OuterS3`:

* `abs_re_DeltaPhi_interior_le`: `|(DeltaPhi δ b).re| ≤ C` uniformly for `δ ∈ (0, 1/4)` and
  `0 < b.im ≤ 7/16`, using `|tanh u| ≤ ‖tanh(u + iv)‖ ≤ 1` (`0 ≤ v ≤ π/4`) and `a² b ≤ a³ + b³`.
* `R4c_zetaD_sq_eq`: `R4c (zetaD b) ^ 2 = ((1 + 2 z - z^2)/(1 + z^2)) * (π b / sinh(π b)) / kap^2`
  on `{0 < b.im < 1/2}` by the identity theorem from `R4cStrip_eq_R4c`.
* `norm_Estripped_interior_le`: `‖Estripped δ b‖ ≤ C (1 + |b.re|)^{-1/2} e^{-2π|b.re|}` uniformly
  for `δ ∈ (0, 1/4)` and `0 < b.im ≤ 7/16`.
* `norm_one_sub_one_sub_delta_zetaD_ge`: `c * (min 1 ‖b - I/2‖ + δ) ≤ ‖1 - (1 - δ) * zetaD b‖`
  for `δ ∈ (0, 1/10)`, `7/16 < b.im ≤ 1/2 + etaDelta δ / 2`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

private lemma half_le_sin_of_le_pi_div_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ π / 3) :
    x / 2 ≤ Real.sin x := by
  have hmono : MonotoneOn (fun y : ℝ => Real.sin y - y / 2) (Icc 0 (π / 3)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 3))
      (Real.continuous_sin.sub (continuous_id.div_const 2)).continuousOn
      (fun y _ => ((Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).div_const 2)).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        have hd : HasDerivAt (fun z : ℝ => Real.sin z - z / 2) (Real.cos y - 1 / 2) y :=
          (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).div_const 2)
        rw [hd.deriv]
        have hcos : 1 / 2 ≤ Real.cos y := by
          have hy' := interior_subset hy
          rw [← Real.cos_pi_div_three]
          exact Real.cos_le_cos_of_nonneg_of_le_pi hy'.1 (by linarith [Real.pi_pos]) hy'.2
        linarith)
  have h0 := hmono ⟨le_rfl, by positivity⟩ ⟨hx0, hx1⟩ hx0
  simp only [Real.sin_zero, zero_div, sub_zero] at h0
  linarith

private lemma le_sinh_of_nonneg {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  have hmono : MonotoneOn (fun y : ℝ => Real.sinh y - y) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (Real.continuous_sinh.sub continuous_id).continuousOn
      (fun y _ => ((Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)).differentiableAt.differentiableWithinAt)
      (fun y _ => by
        have hd : HasDerivAt (fun z : ℝ => Real.sinh z - z) (Real.cosh y - 1) y :=
          (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
        rw [hd.deriv]
        linarith [Real.one_le_cosh y])
  have h0 := hmono (by simp) ht ht
  simp only [Real.sinh_zero, sub_zero] at h0
  linarith

/-! ### 1. Interior `DeltaPhi` bound for `0 < Im b ≤ 7/16` -/

private lemma norm_tanh_ge_abs_tanh {u v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ π / 4) :
    |Real.tanh u| ≤ ‖Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)‖ ∧
    ‖Complex.tanh ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ 1 := by
  have hsq := norm_tanh_sq ((u : ℂ) + (v : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add] at hsq
  have hsin_le : Real.sin v ≤ Real.cos v := by
    have h1 : Real.cos v = Real.sin (π / 2 - v) := (Real.sin_pi_div_two_sub v).symm
    rw [h1]
    exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
  have hsin_nonneg : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hcos_pos : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin_sq_le : Real.sin v ^ 2 ≤ Real.cos v ^ 2 := by nlinarith
  have hden_pos : 0 < Real.sinh u ^ 2 + Real.cos v ^ 2 := by positivity
  have hcos_le1 : Real.cos v ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have hcosh_eq : Real.cosh u ^ 2 = Real.sinh u ^ 2 + 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq u]
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
    rw [hsq, sq_abs, Real.tanh_eq_sinh_div_cosh, div_pow, hcosh_eq, div_le_div_iff₀ (by positivity) hden_pos]
    nlinarith [sq_nonneg (Real.sinh u), sq_nonneg (Real.sin v)]
  · apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num)
    rw [hsq, one_pow, div_le_one hden_pos]
    linarith

private lemma log_inv_le_rpow_quarter {t : ℝ} (ht : 0 < t) : Real.log (1 / t) ≤ 4 * t ^ (-(1 / 4 : ℝ)) := by
  have h1 : Real.log (t ^ (-(1 / 4 : ℝ))) ≤ t ^ (-(1 / 4 : ℝ)) := by
    linarith [Real.add_one_le_exp (Real.log (t ^ (-(1 / 4 : ℝ)))), Real.exp_log (Real.rpow_pos_of_pos ht (-(1 / 4 : ℝ)))]
  have h2 : Real.log (1 / t) = 4 * Real.log (t ^ (-(1 / 4 : ℝ))) := by
    rw [Real.log_rpow ht, one_div, Real.log_inv]; ring
  linarith

private lemma abs_tanh_ge_min' (s : ℝ) : (Real.cosh 1)⁻¹ * min |s| 1 ≤ |Real.tanh s| := by
  have hsh_ge := @le_sinh_of_nonneg
  have h_pos : ∀ x : ℝ, 0 ≤ x → (Real.cosh 1)⁻¹ * min x 1 ≤ Real.tanh x := by
    intro x hx
    have hch1 : 0 < Real.cosh 1 := Real.cosh_pos 1
    by_cases hx1 : x ≤ 1
    · rw [min_eq_left hx1, Real.tanh_eq_sinh_div_cosh, inv_mul_eq_div]
      have hch_le : Real.cosh x ≤ Real.cosh 1 :=
        Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hx, abs_of_pos one_pos]; exact hx1)
      exact div_le_div₀ (hx.trans (le_sinh_of_nonneg hx)) (le_sinh_of_nonneg hx) (Real.cosh_pos x) hch_le
    · push Not at hx1
      rw [min_eq_right hx1.le]
      have h1 : Real.tanh 1 ≤ Real.tanh x := by
        rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          div_le_div_iff₀ (Real.cosh_pos 1) (Real.cosh_pos x)]
        have hsub : 0 ≤ Real.sinh (x - 1) := Real.sinh_nonneg_iff.mpr (by linarith)
        rw [Real.sinh_sub] at hsub
        linarith
      have h2 : (Real.cosh 1)⁻¹ ≤ Real.tanh 1 := by
        rw [Real.tanh_eq_sinh_div_cosh, inv_eq_one_div]
        exact div_le_div_of_nonneg_right (le_sinh_of_nonneg zero_le_one) hch1.le
      rw [mul_one]; exact h2.trans h1
  rcases abs_cases s with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hnn : 0 ≤ Real.tanh s := by
      rw [Real.tanh_eq_sinh_div_cosh]; exact div_nonneg (Real.sinh_nonneg_iff.mpr h2) (Real.cosh_pos _).le
    rw [h1, abs_of_nonneg hnn]; exact h_pos s h2
  · have hnp : Real.tanh s ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]; exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr h2.le) (Real.cosh_pos _).le
    rw [h1, abs_of_nonpos hnp, show -Real.tanh s = Real.tanh (-s) by
      simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_neg, Real.cosh_neg, neg_div, neg_neg]]
    exact h_pos (-s) (by linarith)

private lemma integrableOn_abs_rpow_Icc :
    IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (Icc (-1 : ℝ) 1) := by
  have h01 : IntervalIntegrable (fun t : ℝ => t ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h_pos_ioc : IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (Ioc 0 1) :=
    h01.1.congr_fun (fun t ht => by rw [abs_of_pos ht.1]) measurableSet_Ioc
  have h_pos_icc : IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (Icc 0 1) := by
    rwa [integrableOn_Icc_iff_integrableOn_Ioc]
  have h_neg_icc : IntegrableOn (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (Icc (-1 : ℝ) 0) := by
    have hcomp : IntegrableOn (fun t : ℝ => |-t| ^ (-(3 / 4 : ℝ))) ((fun t : ℝ => -t) ⁻¹' Icc 0 1) :=
      h_pos_icc.comp_neg
    have hpre : (fun t : ℝ => -t) ⁻¹' Icc (0 : ℝ) 1 = Icc (-1 : ℝ) 0 := by
      ext t; simp only [mem_Icc, mem_preimage]; constructor <;> intro h <;> constructor <;> linarith
    rw [hpre] at hcomp
    exact hcomp.congr_fun (fun t _ => by dsimp only; rw [abs_neg]) measurableSet_Icc
  have hunion : Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 0 ∪ Icc 0 1 := by
    ext t; simp only [mem_Icc, mem_union]; constructor <;> intro h
    · rcases le_or_gt t 0 with h0 | h0
      · exact Or.inl ⟨h.1, h0⟩
      · exact Or.inr ⟨h0.le, h.2⟩
    · rcases h with h | h <;> constructor <;> linarith
  rw [hunion]
  exact h_neg_icc.union h_pos_icc

private lemma integrable_min_rpow_neg_three_quarters_exp (u : ℝ) :
    IntegrableOn (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) (Ioi xiStar) := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hexp_int : IntegrableOn (fun y => Real.exp (-(π * y))) (Ioi xiStar) := by
    have h := integrableOn_exp_mul_Ioi (show -π < 0 by linarith) xiStar
    exact h.congr_fun (fun y _ => by ring_nf) measurableSet_Ioi
  set A : Set ℝ := Icc (u - 1) (u + 1)
  have hA_meas : MeasurableSet A := measurableSet_Icc
  have h_meas : AEStronglyMeasurable (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)))
      (volume.restrict (Ioi xiStar)) := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  have h1 : IntegrableOn (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)))
      (Ioi xiStar ∩ A) := by
    have h_int_A : IntegrableOn (fun y => |u - y| ^ (-(3 / 4 : ℝ))) A := by
      have h0 := integrableOn_abs_rpow_Icc
      have hmp := measurePreserving_add_right volume (-u)
      have h_comp : IntegrableOn (fun y : ℝ => |y + -u| ^ (-(3 / 4 : ℝ))) ((fun y : ℝ => y + -u) ⁻¹' Icc (-1 : ℝ) 1) :=
        (hmp.integrableOn_comp_preimage (MeasurableEquiv.addRight (-u)).measurableEmbedding).mpr h0
      have h_pre : (fun y : ℝ => y + -u) ⁻¹' Icc (-1 : ℝ) 1 = A := by
        ext y; simp [A, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith
      rw [h_pre] at h_comp
      exact h_comp.congr_fun (fun y _ => by dsimp only; rw [abs_sub_comm]; ring_nf) measurableSet_Icc
    refine (h_int_A.mono_set Set.inter_subset_right).mono' (h_meas.mono_set Set.inter_subset_left) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.inter hA_meas)] with y hy
    have hy_xi : xiStar < y := hy.1
    have hy_A : y ∈ A := hy.2
    have hmin_eq : min |u - y| 1 = |u - y| := min_eq_left (abs_le.mpr ⟨by linarith [hy_A.2], by linarith [hy_A.1]⟩)
    rw [Real.norm_of_nonneg (by positivity), hmin_eq]
    have hexp_le1 : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg _) _) hexp_le1
  have h2 : IntegrableOn (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)))
      (Ioi xiStar \ A) := by
    refine (hexp_int.mono_set Set.sdiff_subset).mono' (h_meas.mono_set Set.sdiff_subset) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff hA_meas)] with y hy
    have hy_nA : ¬ (u - 1 ≤ y ∧ y ≤ u + 1) := hy.2
    have h1_le : 1 ≤ |u - y| := by
      rcases lt_or_ge y (u - 1) with hlt | hge
      · rw [abs_of_pos (by linarith)]; linarith
      · have hgt : u + 1 < y := by by_contra h; exact hy_nA ⟨hge, not_lt.mp h⟩
        rw [abs_of_neg (by linarith)]; linarith
    rw [Real.norm_of_nonneg (by positivity), min_eq_right h1_le, Real.one_rpow, one_mul]
  have hunion : Ioi xiStar = (Ioi xiStar ∩ A) ∪ (Ioi xiStar \ A) := (Set.inter_union_diff _ _).symm
  rw [hunion]
  exact h1.union h2

private lemma setIntegral_min_rpow_exp_le (u : ℝ) :
    ∫ y in Ioi xiStar, (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) ≤
      (∫ t in Icc (-1 : ℝ) 1, |t| ^ (-(3 / 4 : ℝ))) + ∫ y in Ioi xiStar, Real.exp (-(π * y)) := by
  have hpi := Real.pi_pos
  set A : Set ℝ := Icc (u - 1) (u + 1)
  have h_int := integrable_min_rpow_neg_three_quarters_exp u
  have h_int1 : IntegrableOn (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) (Ioi xiStar ∩ A) :=
    h_int.mono_set Set.inter_subset_left
  have h_int2 : IntegrableOn (fun y => (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) (Ioi xiStar \ A) :=
    h_int.mono_set Set.diff_subset
  have hunion : Ioi xiStar = (Ioi xiStar ∩ A) ∪ (Ioi xiStar \ A) := (Set.inter_union_diff _ _).symm
  conv_lhs => rw [hunion]
  rw [setIntegral_union (disjoint_sdiff_self_right.mono_left Set.inter_subset_right) (measurableSet_Ioi.diff measurableSet_Icc) h_int1 h_int2]
  have h1_le : ∫ y in Ioi xiStar ∩ A, (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) ≤
      ∫ t in Icc (-1 : ℝ) 1, |t| ^ (-(3 / 4 : ℝ)) := by
    have h_int_A : IntegrableOn (fun y => |u - y| ^ (-(3 / 4 : ℝ))) A := by
      have h0 := integrableOn_abs_rpow_Icc
      have hmp := measurePreserving_add_right volume (-u)
      have h_comp : IntegrableOn (fun y : ℝ => |y + -u| ^ (-(3 / 4 : ℝ))) ((fun y : ℝ => y + -u) ⁻¹' Icc (-1 : ℝ) 1) :=
        (hmp.integrableOn_comp_preimage (MeasurableEquiv.addRight (-u)).measurableEmbedding).mpr h0
      have h_pre : (fun y : ℝ => y + -u) ⁻¹' Icc (-1 : ℝ) 1 = A := by
        ext y; simp [A, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith
      rw [h_pre] at h_comp
      exact h_comp.congr_fun (fun y _ => by dsimp only; rw [abs_sub_comm]; ring_nf) measurableSet_Icc
    have h_mono1 : ∫ y in Ioi xiStar ∩ A, (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) ≤
        ∫ y in Ioi xiStar ∩ A, |u - y| ^ (-(3 / 4 : ℝ)) := by
      apply setIntegral_mono_on h_int1 (h_int_A.mono_set Set.inter_subset_right) (measurableSet_Ioi.inter measurableSet_Icc)
      intro y hy
      have hy_xi : xiStar < y := hy.1
      have hmin : min |u - y| 1 = |u - y| := min_eq_left (abs_le.mpr ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩)
      rw [hmin]
      exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.exp_le_one_iff.mpr (by nlinarith [xiStar_pos]))
    have h_mono2 : ∫ y in Ioi xiStar ∩ A, |u - y| ^ (-(3 / 4 : ℝ)) ≤ ∫ y in A, |u - y| ^ (-(3 / 4 : ℝ)) :=
      setIntegral_mono_set h_int_A (ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _)
        (Filter.Eventually.of_forall fun _ h => Set.inter_subset_right h)
    have h_eq : ∫ y in A, |u - y| ^ (-(3 / 4 : ℝ)) = ∫ t in Icc (-1 : ℝ) 1, |t| ^ (-(3 / 4 : ℝ)) := by
      have h_shift : ∫ y in A, |u - y| ^ (-(3 / 4 : ℝ)) = ∫ y in A, |y + -u| ^ (-(3 / 4 : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun y _ => ?_)
        rw [abs_sub_comm]; ring_nf
      rw [h_shift]
      have h_pre : A = (fun y : ℝ => y + -u) ⁻¹' Icc (-1 : ℝ) 1 := by
        ext y; simp [A, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith
      rw [h_pre]
      have hmp := measurePreserving_add_right volume (-u)
      exact hmp.setIntegral_preimage_emb (MeasurableEquiv.addRight (-u)).measurableEmbedding
        (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (Icc (-1 : ℝ) 1)
    exact (h_mono1.trans h_mono2).trans_eq h_eq
  have h2_le : ∫ y in Ioi xiStar \ A, (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) ≤
      ∫ y in Ioi xiStar, Real.exp (-(π * y)) := by
    have hexp_int : IntegrableOn (fun y => Real.exp (-(π * y))) (Ioi xiStar) :=
      (integrableOn_exp_mul_Ioi (show -π < 0 by linarith) xiStar).congr_fun (fun y _ => by ring_nf) measurableSet_Ioi
    have h_mono1 : ∫ y in Ioi xiStar \ A, (min |u - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) ≤
        ∫ y in Ioi xiStar \ A, Real.exp (-(π * y)) := by
      apply setIntegral_mono_on h_int2 (hexp_int.mono_set Set.diff_subset) (measurableSet_Ioi.diff measurableSet_Icc)
      intro y hy
      have hy_nA : ¬ (u - 1 ≤ y ∧ y ≤ u + 1) := hy.2
      have h1_le : 1 ≤ |u - y| := by
        rcases lt_or_ge y (u - 1) with hlt | hge
        · rw [abs_of_pos (by linarith)]; linarith
        · have hgt : u + 1 < y := by by_contra h; exact hy_nA ⟨hge, not_lt.mp h⟩
          rw [abs_of_neg (by linarith)]; linarith
      rw [min_eq_right h1_le, Real.one_rpow, one_mul]
    exact h_mono1.trans (setIntegral_mono_set hexp_int (ae_of_all _ fun _ => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall fun _ h => Set.sdiff_subset h))
  exact add_le_add h1_le h2_le

lemma abs_re_DeltaPhi_interior_le :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∀ b : ℂ, 0 < b.im → b.im ≤ 7 / 16 →
      |(DeltaPhi δ b).re| ≤ C := by
  obtain ⟨C0, hC0_pos, hS4a⟩ := outerS4a
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hch1 : 0 < Real.cosh 1 := Real.cosh_pos 1
  set c_t : ℝ := (Real.cosh 1)⁻¹ with hc_t
  have hct_pos : 0 < c_t := inv_pos.mpr hch1
  set K_t : ℝ := 4 * c_t ^ (-(1 / 4 : ℝ)) with hKt
  have hKt_pos : 0 < K_t := by positivity
  have h_tanh_log : ∀ s : ℝ, s ≠ 0 →
      -Real.log |Real.tanh s| ≤ K_t * (min |s| 1) ^ (-(1 / 4 : ℝ)) := by
    intro s hs
    have h1 : 0 < |Real.tanh s| := by
      rw [abs_pos, Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero (Real.sinh_ne_zero.mpr hs) (Real.cosh_pos _).ne'
    have h2 : c_t * min |s| 1 ≤ |Real.tanh s| := abs_tanh_ge_min' s
    have h3 : 0 < min |s| 1 := lt_min (abs_pos.mpr hs) one_pos
    have h4 : 1 / |Real.tanh s| ≤ 1 / (c_t * min |s| 1) :=
      one_div_le_one_div_of_le (by positivity) h2
    have h5 : -Real.log |Real.tanh s| = Real.log (1 / |Real.tanh s|) := by rw [one_div, Real.log_inv]
    rw [h5]
    calc Real.log (1 / |Real.tanh s|)
        ≤ Real.log (1 / (c_t * min |s| 1)) := Real.log_le_log (by positivity) h4
      _ ≤ 4 * (c_t * min |s| 1) ^ (-(1 / 4 : ℝ)) := log_inv_le_rpow_quarter (by positivity)
      _ = K_t * (min |s| 1) ^ (-(1 / 4 : ℝ)) := by
          rw [Real.mul_rpow hct_pos.le h3.le, hKt]; ring
  set M_int : ℝ := (∫ t in Icc (-1 : ℝ) 1, |t| ^ (-(3 / 4 : ℝ))) + ∫ y in Ioi xiStar, Real.exp (-(π * y))
  have hM_int_pos : 0 < M_int := by
    have hexp_pos : 0 < ∫ y in Ioi xiStar, Real.exp (-(π * y)) := by
      have hexp_int : IntegrableOn (fun y => Real.exp (-(π * y))) (Ioi xiStar) :=
        (integrableOn_exp_mul_Ioi (show -π < 0 by linarith) xiStar).congr_fun (fun y _ => by ring_nf) measurableSet_Ioi
      exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le) hexp_int).mpr (by
        have hsupp : Function.support (fun y => Real.exp (-(π * y))) = Set.univ := by
          ext y; simp [(Real.exp_pos _).ne']
        rw [hsupp]; simp)
    have hI_nonneg : 0 ≤ ∫ t in Icc (-1 : ℝ) 1, |t| ^ (-(3 / 4 : ℝ)) :=
      setIntegral_nonneg measurableSet_Icc (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  refine ⟨(1 / π) * (C0 * K_t * (4 * M_int)), by positivity, fun δ hδ0 hδ4 b hbim0 hbim1 => ?_⟩
  have hb_strip : b ∈ imStrip := ⟨hbim0, by linarith⟩
  have h_phiY_bd : ∀ y : ℝ, xiStar < y → y ≠ b.re → y ≠ -b.re →
      |(phiY y b).re| ≤ K_t * ((min |b.re - y| 1) ^ (-(1 / 4 : ℝ)) + (min |b.re + y| 1) ^ (-(1 / 4 : ℝ))) := by
    intro y _ hne1 hne2
    have hb_eq : b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
    rw [phiY_eq hb_strip, Complex.log_re, norm_neg]
    unfold Tcx
    rw [norm_mul]
    set s1 : ℝ := π * (b.re - y) / 2
    set s2 : ℝ := π * (b.re + y) / 2
    set v : ℝ := π * b.im / 2
    have hv0 : 0 ≤ v := by positivity
    have hv1 : v ≤ π / 4 := by dsimp only [v]; nlinarith [hbim1, hpi]
    have hs1_ne : s1 ≠ 0 := by dsimp only [s1]; intro h; apply hne1; have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right (by norm_num)); linarith [this.resolve_left hpi.ne']
    have hs2_ne : s2 ≠ 0 := by dsimp only [s2]; intro h; apply hne2; have := mul_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right (by norm_num)); linarith [this.resolve_left hpi.ne']
    have hw1 : (π : ℂ) * (b - (y : ℂ)) / 2 = (s1 : ℂ) + (v : ℂ) * Complex.I := by
      rw [hb_eq]; apply Complex.ext <;> simp [s1, v] <;> ring
    have hw2 : (π : ℂ) * (b + (y : ℂ)) / 2 = (s2 : ℂ) + (v : ℂ) * Complex.I := by
      rw [hb_eq]; apply Complex.ext <;> simp [s2, v] <;> ring
    rw [hw1, hw2]
    obtain ⟨h1_lo, h1_hi⟩ := norm_tanh_ge_abs_tanh (u := s1) hv0 hv1
    obtain ⟨h2_lo, h2_hi⟩ := norm_tanh_ge_abs_tanh (u := s2) hv0 hv1
    have h1_pos : 0 < |Real.tanh s1| := by
      rw [abs_pos, Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero (Real.sinh_ne_zero.mpr hs1_ne) (Real.cosh_pos _).ne'
    have h2_pos : 0 < |Real.tanh s2| := by
      rw [abs_pos, Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero (Real.sinh_ne_zero.mpr hs2_ne) (Real.cosh_pos _).ne'
    have hprod_pos : 0 < ‖Complex.tanh ((s1 : ℂ) + (v : ℂ) * Complex.I)‖ *
        ‖Complex.tanh ((s2 : ℂ) + (v : ℂ) * Complex.I)‖ := mul_pos (lt_of_lt_of_le h1_pos h1_lo) (lt_of_lt_of_le h2_pos h2_lo)
    have hprod_le1 : ‖Complex.tanh ((s1 : ℂ) + (v : ℂ) * Complex.I)‖ *
        ‖Complex.tanh ((s2 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ 1 := by
      nlinarith [norm_nonneg (Complex.tanh ((s1 : ℂ) + (v : ℂ) * Complex.I)),
        norm_nonneg (Complex.tanh ((s2 : ℂ) + (v : ℂ) * Complex.I))]
    rw [abs_of_nonpos (Real.log_nonpos hprod_pos.le hprod_le1),
      Real.log_mul (lt_of_lt_of_le h1_pos h1_lo).ne' (lt_of_lt_of_le h2_pos h2_lo).ne']
    have hl1 : -Real.log ‖Complex.tanh ((s1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ K_t * (min |b.re - y| 1) ^ (-(1 / 4 : ℝ)) := by
      have hlog : -Real.log ‖Complex.tanh ((s1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ -Real.log |Real.tanh s1| :=
        neg_le_neg (Real.log_le_log h1_pos h1_lo)
      have hmin : min |b.re - y| 1 ≤ min |s1| 1 := by
        refine le_min (min_le_of_left_le ?_) (min_le_right _ _)
        dsimp only [s1]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have : 1 ≤ π / 2 := by linarith [Real.two_le_pi]
        nlinarith [abs_nonneg (b.re - y)]
      have hrp : (min |s1| 1) ^ (-(1 / 4 : ℝ)) ≤ (min |b.re - y| 1) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (lt_min (abs_pos.mpr (sub_ne_zero.mpr hne1.symm)) one_pos) hmin (by norm_num)
      exact hlog.trans ((h_tanh_log s1 hs1_ne).trans (mul_le_mul_of_nonneg_left hrp hKt_pos.le))
    have hl2 : -Real.log ‖Complex.tanh ((s2 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ K_t * (min |b.re + y| 1) ^ (-(1 / 4 : ℝ)) := by
      have hlog : -Real.log ‖Complex.tanh ((s2 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ -Real.log |Real.tanh s2| :=
        neg_le_neg (Real.log_le_log h2_pos h2_lo)
      have hmin : min |b.re + y| 1 ≤ min |s2| 1 := by
        refine le_min (min_le_of_left_le ?_) (min_le_right _ _)
        dsimp only [s2]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have : 1 ≤ π / 2 := by linarith [Real.two_le_pi]
        nlinarith [abs_nonneg (b.re + y)]
      have hrp : (min |s2| 1) ^ (-(1 / 4 : ℝ)) ≤ (min |b.re + y| 1) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (lt_min (abs_pos.mpr (by intro h; apply hne2; linarith)) one_pos) hmin (by norm_num)
      exact hlog.trans ((h_tanh_log s2 hs2_ne).trans (mul_le_mul_of_nonneg_left hrp hKt_pos.le))
    linarith
  have h_cube : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a ^ 2 * c ≤ a ^ 3 + c ^ 3 := by
    intro a c ha hc
    rcases le_total a c with h | h
    · calc a ^ 2 * c ≤ c ^ 2 * c := by gcongr
        _ = c ^ 3 := by ring
        _ ≤ a ^ 3 + c ^ 3 := le_add_of_nonneg_left (pow_nonneg ha 3)
    · calc a ^ 2 * c ≤ a ^ 2 * a := by gcongr
        _ = a ^ 3 := by ring
        _ ≤ a ^ 3 + c ^ 3 := le_add_of_nonneg_right (pow_nonneg hc 3)
  set maj : ℝ → ℝ := fun y =>
    C0 * K_t * (2 * (min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) +
      (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) + (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ))) * Real.exp (-(π * y))
  have hmaj_int : IntegrableOn maj (Ioi xiStar) := by
    have h1 := integrable_min_rpow_neg_three_quarters_exp xiStar
    have h2 := integrable_min_rpow_neg_three_quarters_exp b.re
    have h3 := integrable_min_rpow_neg_three_quarters_exp (-b.re)
    exact IntegrableOn.congr_fun ((((h1.const_mul 2).add h2).add h3).const_mul (C0 * K_t))
      (fun y _ => by dsimp only [maj, Pi.add_apply]; ring) measurableSet_Ioi
  have h_pt_bd : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)),
      |deriv (dphi δ) y * (phiY y b).re| ≤ maj y := by
    have h_ae_mem : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ∈ Ioi xiStar :=
      ae_restrict_mem measurableSet_Ioi
    have h_ae_ne1 : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ≠ b.re :=
      ae_iff.mpr (by simp)
    have h_ae_ne2 : ∀ᵐ y ∂(volume.restrict (Ioi xiStar)), y ≠ -b.re :=
      ae_iff.mpr (by simp)
    filter_upwards [h_ae_mem, h_ae_ne1, h_ae_ne2] with y hy hne1 hne2
    have hd := (hS4a δ hδ0 hδ4 y hy).1
    have hp := h_phiY_bd y hy hne1 hne2
    rw [abs_mul]
    have hmin_xi : min (y - xiStar) 1 = min |xiStar - y| 1 := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hy)]
    have hmin_neg : |b.re + y| = |-b.re - y| := by
      rw [show b.re + y = -(-b.re - y) by ring, abs_neg]
    set X := (min |xiStar - y| 1) ^ (-(1 / 4 : ℝ))
    set Y1 := (min |b.re - y| 1) ^ (-(1 / 4 : ℝ))
    set Y2 := (min |-b.re - y| 1) ^ (-(1 / 4 : ℝ))
    have hX_nn : 0 ≤ X := Real.rpow_nonneg (by positivity) _
    have hY1_nn : 0 ≤ Y1 := Real.rpow_nonneg (by positivity) _
    have hY2_nn : 0 ≤ Y2 := Real.rpow_nonneg (by positivity) _
    have hX2 : X ^ 2 = (min (y - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by
      rw [hmin_xi, ← Real.rpow_natCast X 2]; dsimp only [X]
      rw [← Real.rpow_mul (by positivity)]; norm_num
    have hX3 : X ^ 3 = (min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast X 3]; dsimp only [X]
      rw [← Real.rpow_mul (by positivity)]; norm_num
    have hY1_3 : Y1 ^ 3 = (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast Y1 3]; dsimp only [Y1]
      rw [← Real.rpow_mul (by positivity)]; norm_num
    have hY2_3 : Y2 ^ 3 = (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast Y2 3]; dsimp only [Y2]
      rw [← Real.rpow_mul (by positivity)]; norm_num
    calc |deriv (dphi δ) y| * |(phiY y b).re|
        ≤ (C0 * (min (y - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * y))) *
            (K_t * (Y1 + Y2)) :=
          mul_le_mul hd (by dsimp only [Y1, Y2]; rw [← hmin_neg]; exact hp) (abs_nonneg _)
            (by have : 0 ≤ y - xiStar := sub_nonneg.mpr hy.le; positivity)
      _ = C0 * K_t * (X ^ 2 * Y1 + X ^ 2 * Y2) * Real.exp (-(π * y)) := by
          rw [hX2]; ring_nf
      _ ≤ C0 * K_t * (2 * X ^ 3 + Y1 ^ 3 + Y2 ^ 3) * Real.exp (-(π * y)) := by
          have hsum_le : X ^ 2 * Y1 + X ^ 2 * Y2 ≤ 2 * X ^ 3 + Y1 ^ 3 + Y2 ^ 3 := by
            linarith [h_cube X Y1 hX_nn hY1_nn, h_cube X Y2 hX_nn hY2_nn]
          gcongr
      _ = maj y := by rw [hX3, hY1_3, hY2_3]
  have hg := integrableOn_dphi_deriv hδ0 hδ4
  have hcont_phi := continuous_phiY_y hb_strip
  have h_re_int : IntegrableOn (fun y => deriv (dphi δ) y * (phiY y b).re) (Ioi xiStar) :=
    hmaj_int.mono' (hg.aestronglyMeasurable.mul
      (Complex.continuous_re.comp hcont_phi).aestronglyMeasurable) h_pt_bd
  have h_cx_int : IntegrableOn (fun y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) (Ioi xiStar) := by
    set ε : ℝ := min b.im (1 - b.im) / 2
    have hε0 : 0 < ε := by
      dsimp only [ε]; exact div_pos (lt_min hbim0 (by linarith)) (by norm_num)
    have hε1 : ε < 1 / 2 := by
      dsimp only [ε]; have := min_le_left b.im (1 - b.im); have := min_le_right b.im (1 - b.im); linarith
    have hbε : b ∈ stripEps ε := ⟨by dsimp only [ε]; linarith [min_le_left b.im (1 - b.im)],
      by dsimp only [ε]; linarith [min_le_right b.im (1 - b.im)]⟩
    set K0 := 2 * (-Real.log (Real.sin (π * ε / 2))) + π
    refine (hg.norm.mul_const K0).mono'
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul
        hcont_phi.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_phiY_le_of_stripEps hε0 hε1 hbε) (norm_nonneg _)
  have h_re_eq : (DeltaPhi δ b).re =
      (1 / π) * ∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y b).re := by
    unfold DeltaPhi
    rw [show (1 / (π : ℂ)) = ((1 / π : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    congr 1
    have hcomm := Complex.reCLM.integral_comp_comm h_cx_int
    simpa using hcomm.symm
  rw [h_re_eq, abs_mul, abs_of_pos (by positivity : 0 < 1 / π)]
  have h_int_abs : |∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y b).re| ≤
      ∫ y in Ioi xiStar, maj y := by
    calc |∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y b).re|
        = ‖∫ y in Ioi xiStar, deriv (dphi δ) y * (phiY y b).re‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y in Ioi xiStar, ‖deriv (dphi δ) y * (phiY y b).re‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y in Ioi xiStar, |deriv (dphi δ) y * (phiY y b).re| := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => Real.norm_eq_abs _)
      _ ≤ ∫ y in Ioi xiStar, maj y :=
          integral_mono_ae h_re_int.norm hmaj_int h_pt_bd
  have h_maj_bd : ∫ y in Ioi xiStar, maj y ≤ C0 * K_t * (4 * M_int) := by
    have h1 := integrable_min_rpow_neg_three_quarters_exp xiStar
    have h2 := integrable_min_rpow_neg_three_quarters_exp b.re
    have h3 := integrable_min_rpow_neg_three_quarters_exp (-b.re)
    have h_eq : ∫ y in Ioi xiStar, maj y =
        C0 * K_t * (2 * (∫ y in Ioi xiStar, (min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
          (∫ y in Ioi xiStar, (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
          (∫ y in Ioi xiStar, (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)))) := by
      have hsum : ∫ y in Ioi xiStar,
          (2 * ((min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
            (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) +
            (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) =
          2 * (∫ y in Ioi xiStar, (min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
            (∫ y in Ioi xiStar, (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
            (∫ y in Ioi xiStar, (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) := by
        erw [integral_add ((h1.const_mul 2).add h2) h3, integral_add (h1.const_mul 2) h2, integral_const_mul]
      have hmaj_eq : ∫ y in Ioi xiStar, maj y = C0 * K_t * ∫ y in Ioi xiStar,
          (2 * ((min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
            (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y)) +
            (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_); dsimp only [maj]; ring
      rw [hmaj_eq, hsum]
    rw [h_eq]
    have hb1 := setIntegral_min_rpow_exp_le xiStar
    have hb2 := setIntegral_min_rpow_exp_le b.re
    have hb3 := setIntegral_min_rpow_exp_le (-b.re)
    calc C0 * K_t * (2 * (∫ y in Ioi xiStar, (min |xiStar - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
          (∫ y in Ioi xiStar, (min |b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))) +
          (∫ y in Ioi xiStar, (min |-b.re - y| 1) ^ (-(3 / 4 : ℝ)) * Real.exp (-(π * y))))
        ≤ C0 * K_t * (2 * M_int + M_int + M_int) := by gcongr
      _ = C0 * K_t * (4 * M_int) := by ring
  exact mul_le_mul_of_nonneg_left (h_int_abs.trans h_maj_bd) (by positivity)

/-! ### 2. `R4c (zetaD b)^2` on `{0 < Im b < 1/2}` and interior `Estripped` bound -/

lemma R4c_zetaD_sq_eq {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    R4c (zetaD b) ^ 2 =
      ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) *
        ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) / (kap : ℂ) ^ 2 := by
  set U : Set ℂ := {w : ℂ | 0 < w.im ∧ w.im < 1 / 2}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hU_conv : Convex ℝ U := convex_iff_segment_subset.mpr fun x hx y hy z hz => by
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have him : ((1 - t) • x + t • y).im = (1 - t) * x.im + t * y.im := by simp
    have hmem := convex_Ioo (0 : ℝ) (1 / 2) ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ (sub_nonneg.mpr ht1) ht0 (by ring)
    rw [smul_eq_mul] at hmem
    change 0 < ((1 - t) • x + t • y).im ∧ ((1 - t) • x + t • y).im < 1 / 2
    rw [him]
    exact ⟨hmem.1, hmem.2⟩
  set F : ℂ → ℂ := fun w => R4c (zetaD w) ^ 2
  set G : ℂ → ℂ := fun w =>
    ((1 + 2 * zetaD w - zetaD w ^ 2) / (1 + zetaD w ^ 2)) *
      ((π : ℂ) * w / Complex.sinh ((π : ℂ) * w)) / (kap : ℂ) ^ 2
  have hU_strip : ∀ w ∈ U, w ∈ imStrip := fun _ hw => ⟨hw.1, by linarith [hw.2]⟩
  have hsh_ne_strip : ∀ w ∈ imStrip, Complex.sinh ((π : ℂ) * w) ≠ 0 := fun w hw h =>
    Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hw) (by rw [h, div_zero])
  have hF_diff : DifferentiableOn ℂ F U := by
    intro w hw
    have hzd : DifferentiableAt ℂ zetaD w :=
      differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds (hU_strip w hw))
    have hR : DifferentiableAt ℂ R4c (zetaD w) :=
      differentiableOn_R4c.differentiableAt (isOpen_halfDisc.mem_nhds (zetaD_mem_halfDisc hw.1 hw.2))
    exact ((hR.comp w hzd).pow 2).differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G U := by
    intro w hw
    have hw_s := hU_strip w hw
    have hzd : DifferentiableAt ℂ zetaD w :=
      differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hw_s)
    have hsh_ne : Complex.sinh ((π : ℂ) * w) ≠ 0 := hsh_ne_strip w hw_s
    have hsq_ne : 1 + zetaD w ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hw_s
    have h1 : DifferentiableAt ℂ (fun x => (1 + 2 * zetaD x - zetaD x ^ 2) / (1 + zetaD x ^ 2)) w :=
      (((differentiableAt_const 1).add (hzd.const_mul 2)).sub (hzd.pow 2)).div
        ((differentiableAt_const 1).add (hzd.pow 2)) hsq_ne
    have h2 : DifferentiableAt ℂ (fun x => (π : ℂ) * x / Complex.sinh ((π : ℂ) * x)) w :=
      (differentiableAt_id.const_mul (π : ℂ)).div
        (Complex.differentiableAt_sinh.comp w (differentiableAt_id.const_mul (π : ℂ))) hsh_ne
    exact ((h1.mul h2).div_const ((kap : ℂ) ^ 2)).differentiableWithinAt
  have h_pt : (3 / 8 : ℂ) * Complex.I ∈ U := by simp [U]; norm_num
  have h_ev : F =ᶠ[𝓝 ((3 / 8 : ℂ) * Complex.I)] G := by
    have h_band : ((3 / 8 : ℂ) * Complex.I) ∈ bandUpper (1 / 4) ∩ U := by
      refine ⟨?_, h_pt⟩
      change |((3 / 8 : ℂ) * Complex.I).im - 1 / 2| < 1 / 4; simp; norm_num
    have h_open : IsOpen (bandUpper (1 / 4) ∩ U) := isOpen_band.inter hU_open
    filter_upwards [h_open.mem_nhds h_band] with w ⟨hw_q, hw_U⟩
    have hw_s := hU_strip w hw_U
    have hr1_ne : (1 + 2 * zetaD w - zetaD w ^ 2) / (1 + zetaD w ^ 2) ≠ 0 :=
      Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hw_q)
    have hr2_ne : (π : ℂ) * w / Complex.sinh ((π : ℂ) * w) ≠ 0 :=
      Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hw_s)
    have hcpow_sq : ∀ z : ℂ, z ≠ 0 → (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z hz => by
      rw [Complex.cpow_def_of_ne_zero hz, ← Complex.exp_nat_mul]
      push_cast
      rw [show (2 : ℂ) * (Complex.log z * (1 / 2 : ℂ)) = Complex.log z by ring, Complex.exp_log hz]
    dsimp only [F, G]
    rw [← R4cStrip_eq_R4c hw_q hw_U.2]
    unfold R4cStrip
    rw [div_pow, mul_pow, hcpow_sq _ hr1_ne, hcpow_sq _ hr2_ne]
  exact (hF_diff.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
    (hG_diff.analyticOnNhd hU_open) hU_conv.isPreconnected h_pt h_ev ⟨hb0, hb1⟩

private lemma norm_sinh_le_cosh_pi_mul_norm {b : ℂ} (hb_re : |b.re| ≤ 1) :
    ‖Complex.sinh ((π : ℂ) * b)‖ ≤ Real.cosh π * (π * ‖b‖) := by
  have hpi := Real.pi_pos
  set S : Set ℂ := {z : ℂ | |z.re| ≤ π}
  have hS_conv : Convex ℝ S := convex_iff_segment_subset.mpr fun x hx y hy z hz => by
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    change |((1 - t) • x + t • y).re| ≤ π
    simp only [Complex.add_re, Complex.smul_re]
    calc |(1 - t) * x.re + t * y.re|
        ≤ |(1 - t) * x.re| + |t * y.re| := abs_add_le _ _
      _ = (1 - t) * |x.re| + t * |y.re| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
      _ ≤ (1 - t) * π + t * π := by
          have hx' : |x.re| ≤ π := hx
          have hy' : |y.re| ≤ π := hy
          nlinarith
      _ = π := by ring
  have h0_mem : (0 : ℂ) ∈ S := by simp [S, hpi.le]
  have hb_mem : (π : ℂ) * b ∈ S := by
    change |((π : ℂ) * b).re| ≤ π
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hbound : ∀ z ∈ S, ‖Complex.cosh z‖ ≤ Real.cosh π := by
    intro z hz
    have hcosh_le : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
      rw [norm_cosh_sq]
      have : Real.sinh z.re ^ 2 = Real.cosh z.re ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq z.re]
      nlinarith [Real.cos_sq_le_one z.im]
    refine hcosh_le.trans ?_
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_pos hpi]; exact hz)
  have hmvt := hS_conv.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (Complex.hasDerivAt_sinh z).differentiableAt)
    (fun z hz => by rw [(Complex.hasDerivAt_sinh z).deriv]; exact hbound z hz) h0_mem hb_mem
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi] using hmvt

private lemma norm_ghat_halfDisc_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ halfDisc, c ≤ ‖(1 - z) ^ (-(1 / 2 : ℂ)) * Gtilde R4c z‖ := by
  obtain ⟨c0, _, hc0_pos, hbd⟩ := exp_hbarA_aRest_mul_one_add_sq_bounds
  refine ⟨c0 / 4, by positivity, fun z hz => ?_⟩
  have hs : sInv z ∈ unitStrip := sInv_mem_strip hz
  have hscl : sInv z ∈ unitStripCl := unitStrip_subset_cl hs
  have hstan : sTan (sInv z) = z := sTan_sInv (halfDisc_ne_pm_I hz).1 (halfDisc_ne_pm_I hz).2
  have h4 : Complex.exp ((4 : ℂ) * Hxb (sInv z)) = Kfun (sInv z) := by
    rw [exp_four_Hxb hscl, Kb_of_mem hs]
  have hnorm_Hxb : ‖Complex.exp (Hxb (sInv z))‖ ^ 4 = ‖Kfun (sInv z)‖ := by
    rw [← norm_pow, ← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * Hxb (sInv z) =
      (4 : ℂ) * Hxb (sInv z) by norm_cast, h4]
  have hK_eq : Kfun (sInv z) = qHat z * H3 z := by
    rw [Kfun_eq_qHat hs, hstan]
    unfold H3 gS
    have hu : Complex.cos ((π : ℂ) * sInv z) = uC z :=
      calc Complex.cos ((π : ℂ) * sInv z) = cC (sInv z) := rfl
        _ = uC (sTan (sInv z)) := (uC_sTan hscl).symm
        _ = uC z := by rw [hstan]
    rw [hu]; ring
  have hnorm_K : ‖Kfun (sInv z)‖ = ‖qHat z‖ * ‖R4c z‖ ^ 4 := by
    rw [hK_eq, norm_mul, ← R4c_pow_four (z := z), norm_pow]
  have hR4_pos : 0 < ‖R4c z‖ := norm_pos_iff.mpr (R4c_ne_zero hz)
  have hq_ne : qHat z ≠ 0 := Complex.slitPlane_ne_zero (qHat_mem_slit hz)
  have hq_pos : 0 < ‖qHat z‖ := norm_pos_iff.mpr hq_ne
  have hnorm_Hxb' : ‖Complex.exp (Hxb (sInv z))‖ = ‖qHat z‖ ^ (1 / 4 : ℝ) * ‖R4c z‖ := by
    have hpow_eq : ‖Complex.exp (Hxb (sInv z))‖ ^ 4 = (‖qHat z‖ ^ (1 / 4 : ℝ) * ‖R4c z‖) ^ 4 := by
      rw [hnorm_Hxb, hnorm_K, mul_pow, ← Real.rpow_natCast (‖qHat z‖ ^ (1 / 4 : ℝ)) 4,
        ← Real.rpow_mul hq_pos.le]
      norm_num
    exact le_antisymm
      (le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) hpow_eq.le)
      (le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (norm_nonneg _) hpow_eq.symm.le)
  have hA_split : Complex.exp (hbarA aAmp (sInv z)) =
      Complex.exp (Hxb (sInv z)) * Complex.exp (hbarA aRest (sInv z)) := by
    rw [← Complex.exp_add]; congr 1; unfold Hxb; ring
  have h1sub_ne : 1 - z ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mem_slit (subset_closure hz) (halfDisc_ne_special hz).2.2)
  have h1sub_cancel : ‖(1 - z) ^ (-(1 / 2 : ℂ))‖ * ‖(1 - z) ^ (1 / 2 : ℂ)‖ = 1 := by
    rw [← norm_mul, Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1sub_ne,
      ← Complex.exp_add]
    simp
  have hq_cancel : ‖qHat z‖ ^ (1 / 4 : ℝ) * ‖(qBd z) ^ (-(1 / 4 : ℂ))‖ = 1 := by
    rw [qBd_of_mem hz, Complex.cpow_def_of_ne_zero hq_ne, Complex.norm_exp]
    have hre_q : (Complex.log (qHat z) * (-(1 / 4 : ℂ))).re = -(1 / 4 : ℝ) * Real.log ‖qHat z‖ := by
      simp [Complex.mul_re, Complex.log_re]; ring
    rw [hre_q, Real.rpow_def_of_pos hq_pos, ← Real.exp_add]
    ring_nf; simp
  have hnorm_full : ‖(1 - z) ^ (-(1 / 2 : ℂ)) * Gtilde R4c z‖ =
      ‖Complex.exp (hbarA aRest (sInv z)) * (1 + z ^ 2)‖ / ‖1 + z‖ ^ 2 := by
    unfold Gtilde Gout
    rw [hA_split, norm_mul, norm_div, norm_mul, norm_mul, norm_div, norm_mul, norm_mul,
      norm_pow, hnorm_Hxb', norm_mul (Complex.exp (hbarA aRest (sInv z)))]
    calc ‖(1 - z) ^ (-(1 / 2 : ℂ))‖ *
          (‖1 + z ^ 2‖ *
            (‖qHat z‖ ^ (1 / 4 : ℝ) * ‖R4c z‖ * ‖Complex.exp (hbarA aRest (sInv z))‖ *
              ‖(1 - z) ^ (1 / 2 : ℂ)‖ / ‖1 + z‖ ^ 2 * ‖qBd z ^ (-(1 / 4 : ℂ))‖) /
            ‖R4c z‖)
        = (‖(1 - z) ^ (-(1 / 2 : ℂ))‖ * ‖(1 - z) ^ (1 / 2 : ℂ)‖) *
            (‖qHat z‖ ^ (1 / 4 : ℝ) * ‖qBd z ^ (-(1 / 4 : ℂ))‖) *
            (‖Complex.exp (hbarA aRest (sInv z))‖ * ‖1 + z ^ 2‖ / ‖1 + z‖ ^ 2) := by
          field_simp [hR4_pos.ne']
      _ = _ := by rw [h1sub_cancel, hq_cancel, one_mul, one_mul]
  rw [hnorm_full]
  have hb_lo := (hbd (sInv z) hscl).1
  rw [hstan] at hb_lo
  have hd_pos : 0 < ‖1 + z‖ ^ 2 := by
    have := one_le_norm_one_add (subset_closure hz); positivity
  have hd2 : ‖1 + z‖ ^ 2 ≤ 4 := by
    have := norm_one_add_le (subset_closure hz); nlinarith [norm_nonneg (1 + z)]
  rw [le_div_iff₀ hd_pos]
  nlinarith

lemma norm_Estripped_interior_le :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 40 → ∀ b : ℂ, 0 < b.im → b.im ≤ 7 / 16 →
      ‖Estripped δ b‖ ≤ C * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
  obtain ⟨C_phi, hCphi_pos, hPhi⟩ := abs_re_DeltaPhi_interior_le
  obtain ⟨c_gh, hcgh_pos, hgh⟩ := norm_ghat_halfDisc_ge
  have hpi := Real.pi_pos
  have hkap := kap_pos
  set c_c : ℝ := Real.cos (7 * π / 16)
  have hcc_pos : 0 < c_c := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcc_ge : 1 / 12 < c_c := by
    dsimp only [c_c]
    rw [show 7 * π / 16 = π / 2 - π / 16 by ring, Real.cos_pi_div_two_sub]
    have h1 := half_le_sin_of_le_pi_div_three (by positivity : (0 : ℝ) ≤ π / 16) (by linarith)
    linarith [Real.pi_gt_three]
  -- Bound on ‖√2 + cosh(π b)‖ for 0 < b.im ≤ 7/16
  have hden_bd : ∀ b : ℂ, 0 < b.im → b.im ≤ 7 / 16 →
      c_c * Real.cosh (π * b.re) ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ∧
      ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * Real.cosh (π * b.re) := by
    intro b h0 h7
    have hcos_ge : c_c ≤ Real.cos (π * b.im) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by nlinarith)
    have hre_ge : c_c * Real.cosh (π * b.re) ≤ ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)).re := by
      rw [Complex.add_re, Complex.ofReal_re, re_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have hsq2 : 0 ≤ √2 := Real.sqrt_nonneg _
      have := mul_le_mul_of_nonneg_left hcos_ge (Real.cosh_pos (π * b.re)).le
      linarith
    have hcosh_le : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Real.cosh_pos _).le
      rw [norm_cosh_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
      nlinarith [Real.cos_sq_le_one (π * b.im)]
    have h1c := Real.one_le_cosh (π * b.re)
    have hsq2 : 0 ≤ √2 := Real.sqrt_nonneg _
    refine ⟨hre_ge.trans (Complex.re_le_norm _), ?_⟩
    calc ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
        ≤ ‖(√2 : ℂ)‖ + ‖Complex.cosh ((π : ℂ) * b)‖ := norm_add_le _ _
      _ = √2 + ‖Complex.cosh ((π : ℂ) * b)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq2]
      _ ≤ √2 + Real.cosh (π * b.re) := by linarith
      _ ≤ (√2 + 1) * Real.cosh (π * b.re) := by nlinarith
  -- Lower bound on ‖R4c (zetaD b)‖^2 for 0 < b.im ≤ 7/16
  set c_r2 : ℝ := min (1 / 2) (1 / (2 * Real.cosh π)) * (c_c / (4 * kap ^ 2))
  have hcr2_pos : 0 < c_r2 := by positivity
  have hR4_sq_ge : ∀ b : ℂ, 0 < b.im → b.im ≤ 7 / 16 →
      c_r2 * (1 + |b.re|) ≤ ‖R4c (zetaD b)‖ ^ 2 := by
    intro b h0 h7
    have hb1 : b.im < 1 / 2 := by linarith
    have hb_strip : b ∈ imStrip := ⟨h0, by linarith⟩
    have hz : zetaD b ∈ halfDisc := zetaD_mem_halfDisc h0 hb1
    have hsq_R := R4c_zetaD_sq_eq h0 hb1
    have hnorm_sq : ‖R4c (zetaD b)‖ ^ 2 =
        ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) *
          (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) / kap ^ 2 := by
      rw [← norm_pow, hsq_R, norm_div, norm_mul, norm_div, norm_div, norm_mul, Complex.norm_pow,
        one_add_zetaD_sq_eq hb_strip, norm_div, norm_mul, Complex.norm_ofNat]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkap, abs_of_pos hpi,
        abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
      field_simp
    have h12z_ge : 1 ≤ ‖1 + 2 * zetaD b - zetaD b ^ 2‖ := by
      have hz_re : 0 < (zetaD b).re := hz.2
      have hre_12z : 1 ≤ (1 + 2 * zetaD b - zetaD b ^ 2).re := by
        have hnorm1 : (zetaD b).re ^ 2 ≤ 1 := by
          have hsq := Complex.sq_norm (zetaD b)
          rw [Complex.normSq_apply] at hsq
          have hlt : ‖zetaD b‖ < 1 := hz.1
          have hsq_lt : ‖zetaD b‖ ^ 2 < 1 := by nlinarith [norm_nonneg (zetaD b)]
          nlinarith [sq_nonneg (zetaD b).im]
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
          Complex.im_ofNat, zero_mul, sub_zero, sq]
        nlinarith [sq_nonneg (zetaD b).im]
      exact hre_12z.trans (Complex.re_le_norm _)
    obtain ⟨hden_lo, hden_hi⟩ := hden_bd b h0 h7
    have hch_pos : 0 < Real.cosh (π * b.re) := Real.cosh_pos _
    have hsh_pos : 0 < ‖Complex.sinh ((π : ℂ) * b)‖ := by
      have hsin_pos : 0 < Real.sin (π * b.im) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
      have hsq_pos : 0 < ‖Complex.sinh ((π : ℂ) * b)‖ ^ 2 := by
        rw [norm_sinh_sq]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        positivity
      by_contra h
      have h0 : ‖Complex.sinh ((π : ℂ) * b)‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [h0, zero_pow (by norm_num)] at hsq_pos
      exact lt_irrefl 0 hsq_pos
    have hsh_le : ‖Complex.sinh ((π : ℂ) * b)‖ ≤ Real.cosh (π * b.re) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hch_pos.le
      rw [norm_sinh_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      have : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (π * b.re)]
      nlinarith [Real.sin_sq_le_one (π * b.im)]
    have hsqrt2_lt : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hpart1 : c_c / 4 * Real.cosh (π * b.re) ≤
        ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) := by
      rw [le_div_iff₀ (by positivity)]
      calc c_c / 4 * Real.cosh (π * b.re) * (2 * √2)
          = (√2 / 2) * (c_c * Real.cosh (π * b.re)) := by ring
        _ ≤ 1 * (c_c * Real.cosh (π * b.re)) := by gcongr; linarith
        _ ≤ ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ :=
            mul_le_mul h12z_ge hden_lo (by positivity) (norm_nonneg _)
    have hprod_ge : min (1 / 2) (1 / (2 * Real.cosh π)) * (c_c / 4) * (1 + |b.re|) ≤
        ‖1 + 2 * zetaD b - zetaD b ^ 2‖ * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ / (2 * √2) *
          (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) := by
      rcases le_or_gt |b.re| 1 with hre1 | hre1
      · have hsh_norm := norm_sinh_le_cosh_pi_mul_norm hre1
        have hpart2 : 1 / (2 * Real.cosh π) * (1 + |b.re|) ≤ π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖ := by
          calc 1 / (2 * Real.cosh π) * (1 + |b.re|)
              ≤ 1 / (2 * Real.cosh π) * 2 := by gcongr; linarith
            _ = 1 / Real.cosh π := by ring
            _ ≤ π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖ := by
                rw [le_div_iff₀ hsh_pos]
                calc 1 / Real.cosh π * ‖Complex.sinh ((π : ℂ) * b)‖
                    ≤ 1 / Real.cosh π * (Real.cosh π * (π * ‖b‖)) := by gcongr
                  _ = π * ‖b‖ := by have := Real.cosh_pos π; field_simp
        have h1c : 1 ≤ Real.cosh (π * b.re) := Real.one_le_cosh _
        calc min (1 / 2) (1 / (2 * Real.cosh π)) * (c_c / 4) * (1 + |b.re|)
            ≤ 1 / (2 * Real.cosh π) * (c_c / 4) * (1 + |b.re|) := by
              gcongr; exact min_le_right _ _
          _ = (c_c / 4) * (1 / (2 * Real.cosh π) * (1 + |b.re|)) := by ring
          _ ≤ (c_c / 4 * Real.cosh (π * b.re)) * (π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖) := by
              have h1' : c_c / 4 ≤ c_c / 4 * Real.cosh (π * b.re) := by nlinarith
              exact mul_le_mul h1' hpart2 (by positivity) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hpart1 (by positivity)
      · have hb_ge : (1 / 2 : ℝ) * (1 + |b.re|) ≤ ‖b‖ := by
          have := Complex.abs_re_le_norm b; linarith
        have hpart2 : (1 / 2 : ℝ) * (1 + |b.re|) / Real.cosh (π * b.re) ≤
            π * ‖b‖ / ‖Complex.sinh ((π : ℂ) * b)‖ := by
          rw [div_le_div_iff₀ hch_pos hsh_pos]
          have hpi1 : 1 ≤ π := by linarith [Real.two_le_pi]
          calc (1 / 2 : ℝ) * (1 + |b.re|) * ‖Complex.sinh ((π : ℂ) * b)‖
              ≤ (1 / 2 : ℝ) * (1 + |b.re|) * Real.cosh (π * b.re) := by gcongr
            _ ≤ π * ((1 / 2 : ℝ) * (1 + |b.re|)) * Real.cosh (π * b.re) := by
                have : (1 / 2 : ℝ) * (1 + |b.re|) ≤ π * ((1 / 2 : ℝ) * (1 + |b.re|)) := by nlinarith [abs_nonneg b.re]
                gcongr
            _ ≤ π * ‖b‖ * Real.cosh (π * b.re) := by gcongr
        calc min (1 / 2) (1 / (2 * Real.cosh π)) * (c_c / 4) * (1 + |b.re|)
            ≤ (1 / 2 : ℝ) * (c_c / 4) * (1 + |b.re|) := by
              gcongr; exact min_le_left _ _
          _ = (c_c / 4 * Real.cosh (π * b.re)) * ((1 / 2 : ℝ) * (1 + |b.re|) / Real.cosh (π * b.re)) := by
              field_simp
          _ ≤ _ := mul_le_mul hpart1 hpart2 (by positivity) (by positivity)
    rw [hnorm_sq, le_div_iff₀ (by positivity)]
    calc c_r2 * (1 + |b.re|) * kap ^ 2
        = min (1 / 2) (1 / (2 * Real.cosh π)) * (c_c / 4) * (1 + |b.re|) := by
          dsimp only [c_r2]; field_simp
      _ ≤ _ := hprod_ge
  -- Now assemble the interior bound for Estripped δ b
  set C_est : ℝ := √120 * (32 / c_c ^ 2) * Real.exp C_phi / (√c_r2 * c_gh)
  refine ⟨C_est, by positivity, fun δ hδ0 hδ40 => ?_⟩
  intro b hb0 hb7
  have hb1 : b.im < 1 / 2 := by linarith
  have hb_strip : b ∈ imStrip := ⟨hb0, by linarith⟩
  have hz : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb0 hb1
  have hfac := fDelta_factor hδ0 (by linarith : δ < 1) hz
  have h1sub_ge : (1 / 120 : ℝ) ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
    have h1sq : (1 / 15 : ℝ) ≤ ‖1 - zetaD b ^ 2‖ := by
      have hid : 1 - zetaD b ^ 2 = 2 * Complex.cosh ((π : ℂ) * b) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := by
        rw [zetaD_sq_eq_imStrip hb_strip]
        have hden_ne : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
          intro h; have := (hden_bd b hb0 hb7).1; rw [h, norm_zero] at this
          have hpos := mul_pos hcc_pos (Real.cosh_pos (π * b.re)); linarith
        field_simp [hden_ne]; ring
      rw [hid, norm_div, norm_mul, Complex.norm_ofNat]
      have hcosh_ge : c_c * Real.cosh (π * b.re) ≤ ‖Complex.cosh ((π : ℂ) * b)‖ := by
        have hcos_ge : c_c ≤ Real.cos (π * b.im) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by nlinarith)
        have hre_ge : c_c * Real.cosh (π * b.re) ≤ (Complex.cosh ((π : ℂ) * b)).re := by
          rw [re_cosh']; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.mul_im, add_zero]
          rw [mul_comm (Real.cosh _)]
          exact mul_le_mul_of_nonneg_right hcos_ge (Real.cosh_pos _).le
        exact hre_ge.trans (Complex.re_le_norm _)
      have hden_le := (hden_bd b hb0 hb7).2
      have hden_pos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
        have := (hden_bd b hb0 hb7).1
        have hpos := mul_pos hcc_pos (Real.cosh_pos (π * b.re)); linarith
      rw [le_div_iff₀ hden_pos]
      have hsqrt2_lt : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hch_pos := Real.cosh_pos (π * b.re)
      calc (1 / 15 : ℝ) * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
          ≤ (1 / 15 : ℝ) * ((√2 + 1) * Real.cosh (π * b.re)) := mul_le_mul_of_nonneg_left hden_le (by norm_num)
        _ ≤ 2 * (c_c * Real.cosh (π * b.re)) := by nlinarith
        _ ≤ 2 * ‖Complex.cosh ((π : ℂ) * b)‖ := by gcongr
    have h1m_ge : (1 / 30 : ℝ) ≤ ‖1 - zetaD b‖ := by
      have h2 : ‖1 - zetaD b ^ 2‖ = ‖1 - zetaD b‖ * ‖1 + zetaD b‖ := by
        rw [← norm_mul]; congr 1; ring
      have h1p : ‖1 + zetaD b‖ ≤ 2 := by
        calc ‖1 + zetaD b‖ ≤ ‖(1 : ℂ)‖ + ‖zetaD b‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by rw [norm_one]; linarith [hz.1]
          _ = 2 := by norm_num
      have h1p_pos : 0 < ‖1 + zetaD b‖ := by
        have := one_le_norm_one_add (subset_closure hz); linarith
      nlinarith
    have htri : ‖1 - zetaD b‖ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ + δ * ‖zetaD b‖ := by
      have hid : 1 - zetaD b = (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) - (δ : ℂ) * zetaD b := by
        push_cast; ring
      calc ‖1 - zetaD b‖
          = ‖(1 - ((1 - δ : ℝ) : ℂ) * zetaD b) - (δ : ℂ) * zetaD b‖ := by rw [hid]
        _ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ + ‖(δ : ℂ) * zetaD b‖ := norm_sub_le _ _
        _ = ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ + δ * ‖zetaD b‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have hzd1 : ‖zetaD b‖ ≤ 1 := hz.1.le
    linarith [mul_le_of_le_one_right hδ0.le hzd1]
  have hpow_le : ‖(1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ))‖ ≤ √120 := by
    have hne : 1 - ((1 - δ : ℝ) : ℂ) * zetaD b ≠ 0 := norm_pos_iff.mp (by linarith)
    rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp]
    have hre_p : (Complex.log (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) * (-(1 / 2 : ℂ))).re =
        -(1 / 2 : ℝ) * Real.log ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
      simp [Complex.mul_re, Complex.log_re]; ring
    rw [hre_p, show -(1 / 2 : ℝ) * Real.log ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ =
      Real.log (‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ ^ (-(1 / 2 : ℝ))) by
      rw [Real.log_rpow (by linarith)], Real.exp_log (Real.rpow_pos_of_pos (by linarith) _)]
    rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow, inv_le_comm₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr (by norm_num))]
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1sq_le : ‖(1 + zetaD b ^ 2) ^ 2‖ ≤ (32 / c_c ^ 2) * Real.exp (-(2 * π * |b.re|)) := by
    rw [norm_pow, one_add_zetaD_sq_eq hb_strip, norm_div, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num)),
      div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num only
    have hden_lo := (hden_bd b hb0 hb7).1
    have hc1 := (cosh_pi_re_bounds b.re).1
    have hlo : (c_c / 2) * Real.exp (π * |b.re|) ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
      calc (c_c / 2) * Real.exp (π * |b.re|) = c_c * ((1 / 2 : ℝ) * Real.exp (π * |b.re|)) := by ring
        _ ≤ c_c * Real.cosh (π * b.re) := mul_le_mul_of_nonneg_left hc1 hcc_pos.le
        _ ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := hden_lo
    have hsq : (c_c ^ 2 / 4) * Real.exp (π * |b.re|) ^ 2 ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := by
      calc (c_c ^ 2 / 4) * Real.exp (π * |b.re|) ^ 2 = ((c_c / 2) * Real.exp (π * |b.re|)) ^ 2 := by ring
        _ ≤ ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2 := pow_le_pow_left₀ (by positivity) hlo 2
    have hE : Real.exp (-(2 * π * |b.re|)) = (Real.exp (π * |b.re|) ^ 2)⁻¹ := by
      rw [Real.exp_neg, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [hE]
    calc (8 : ℝ) / ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ^ 2
        ≤ 8 / ((c_c ^ 2 / 4) * Real.exp (π * |b.re|) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      _ = (32 / c_c ^ 2) * (Real.exp (π * |b.re|) ^ 2)⁻¹ := by field_simp; ring
  have hR4_ge : √c_r2 * (1 + |b.re|) ^ (1 / 2 : ℝ) ≤ ‖R4c (zetaD b)‖ := by
    rw [← Real.sqrt_eq_rpow]
    calc √c_r2 * √(1 + |b.re|) = √(c_r2 * (1 + |b.re|)) := (Real.sqrt_mul hcr2_pos.le _).symm
      _ ≤ √(‖R4c (zetaD b)‖ ^ 2) := Real.sqrt_le_sqrt (hR4_sq_ge b hb0 hb7)
      _ = ‖R4c (zetaD b)‖ := Real.sqrt_sq (norm_nonneg _)
  have hgh_ge : c_gh ≤ ‖(1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b)‖ := hgh (zetaD b) hz
  have hexp_phi : ‖Complex.exp (-DeltaPhi δ b)‖ ≤ Real.exp C_phi := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (neg_le.mp (abs_le.mp (hPhi δ hδ0 (by linarith) b hb0 hb7)).1)
  unfold Estripped
  rw [norm_mul, hfac, norm_div, norm_mul, norm_mul]
  have hden_ge : √c_r2 * c_gh * (1 + |b.re|) ^ (1 / 2 : ℝ) ≤
      ‖R4c (zetaD b)‖ * ‖(1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b)‖ := by
    calc √c_r2 * c_gh * (1 + |b.re|) ^ (1 / 2 : ℝ)
        = (√c_r2 * (1 + |b.re|) ^ (1 / 2 : ℝ)) * c_gh := by ring
      _ ≤ ‖R4c (zetaD b)‖ * ‖(1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b)‖ :=
          mul_le_mul hR4_ge hgh_ge hcgh_pos.le (norm_nonneg _)
  have h_rpow_inv : ((1 + |b.re|) ^ (1 / 2 : ℝ))⁻¹ = (1 + |b.re|) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg (by positivity)]; congr 1; ring
  calc ‖(1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ))‖ * ‖(1 + zetaD b ^ 2) ^ 2‖ /
        (‖R4c (zetaD b)‖ * ‖(1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b)‖) *
        ‖Complex.exp (-DeltaPhi δ b)‖
      ≤ (√120 * ((32 / c_c ^ 2) * Real.exp (-(2 * π * |b.re|)))) /
          (√c_r2 * c_gh * (1 + |b.re|) ^ (1 / 2 : ℝ)) * Real.exp C_phi := by
        gcongr
    _ = C_est * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
        rw [← h_rpow_inv]; dsimp only [C_est]; field_simp

/-! ### 3. Branch-point lower bound on `1 - (1 - δ) ζ_D(b)` for `7/16 < Im b ≤ 1/2 + η_δ/2` -/

lemma norm_one_sub_one_sub_delta_zetaD_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 40 → ∀ b : ℂ, 7 / 16 < b.im → b.im ≤ 1 / 2 + etaDelta δ / 2 →
      c * (min 1 ‖b - Complex.I / 2‖ + δ) ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
  have hpi := Real.pi_pos
  have h_eta_lt : ∀ δ : ℝ, 0 < δ → δ < 1 / 40 → etaDelta δ < 1 / 16 := fun δ hδ0 hδ40 => by
    -- sin(π etaDelta δ) = √2 (2δ - δ^2)/(2 - 2δ + δ^2) < 1/12 < sin(π/16)
    have hnum : √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < 1 / 12 := by
      have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hden_ge : 3 / 2 ≤ 2 - 2 * δ + δ ^ 2 := by nlinarith [sq_nonneg δ]
      rw [div_lt_iff₀ (by linarith)]
      have h1 : √2 * (2 * δ - δ ^ 2) ≤ (3 / 2) * (2 * δ) :=
        mul_le_mul hsqrt2.le (by linarith [sq_nonneg δ]) (by nlinarith) (by norm_num)
      linarith only [h1, hden_ge, hδ40]
    have hsin16 : 1 / 12 ≤ Real.sin (π / 16) := by
      have h1 := half_le_sin_of_le_pi_div_three (by positivity : (0 : ℝ) ≤ π / 16) (by linarith)
      linarith [Real.pi_gt_three]
    have harcsin : Real.arcsin (√2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2)) < π / 16 := by
      rw [← Real.arcsin_sin (by linarith : -(π / 2) ≤ π / 16) (by linarith)]
      have hnn : 0 ≤ √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) :=
        div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)) (by nlinarith [sq_nonneg δ])
      exact Real.arcsin_lt_arcsin (by linarith) (hnum.trans_le hsin16) (Real.sin_le_one _)
    unfold etaDelta
    rw [div_lt_iff₀ hpi]; linarith
  have h_sin_eta : ∀ δ : ℝ, 0 < δ → δ < 1 / 40 →
      Real.sin (π * etaDelta δ) = √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) := fun δ hδ0 hδ40 => by
    unfold etaDelta
    rw [mul_div_cancel₀ _ hpi.ne']
    apply Real.sin_arcsin
    · have : 0 ≤ √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) := by
        apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by nlinarith)) (by nlinarith [sq_nonneg δ])
      linarith
    · have : √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < 1 / 8 := by
        have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have h1 : √2 * (2 * δ - δ ^ 2) ≤ (3 / 2) * (2 * δ) :=
          mul_le_mul hsqrt2.le (by linarith [sq_nonneg δ]) (by nlinarith) (by norm_num)
        have hden_ge : 3 / 2 ≤ 2 - 2 * δ + δ ^ 2 := by nlinarith [sq_nonneg δ]
        rw [div_lt_iff₀ (by linarith)]; linarith only [h1, hden_ge, hδ40]
      linarith
  have hcos16 : 1 / 2 ≤ Real.cos (π / 16) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have hcos6 : 3 / 4 ≤ Real.cos (π / 6) := by
    rw [Real.cos_pi_div_six]
    have : (3 / 2 : ℝ) ^ 2 ≤ 3 := by norm_num
    have hsq : 3 / 2 ≤ √3 := Real.le_sqrt_of_sq_le this
    linarith
  have hcosh8 : Real.cosh (π / 8) ≤ 4 / 3 := by
    have hpi_lt := Real.pi_lt_d2
    have h1 : 1 - π / 8 ≤ Real.exp (-(π / 8)) := by linarith [Real.add_one_le_exp (-(π / 8))]
    have h2 : 0 < 1 - π / 8 := by linarith
    have h3 : Real.exp (π / 8) ≤ (1 - π / 8)⁻¹ := by
      rw [← inv_inv (Real.exp (π / 8)), ← Real.exp_neg]
      exact inv_anti₀ h2 h1
    have h4 : (1 - π / 8)⁻¹ ≤ 5 / 3 := by
      rw [inv_le_comm₀ h2 (by norm_num)]; linarith
    have h5 : Real.exp (-(π / 8)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.cosh_eq]
    linarith
  set c_fin : ℝ := 1 / (96 * √2 * (√2 + 1))
  refine ⟨c_fin, by positivity, fun δ hδ0 hδ40 b hb_lo hb_hi => ?_⟩
  have hη_pos : 0 < etaDelta δ := by
    unfold etaDelta
    refine div_pos (Real.arcsin_pos.mpr ?_) hpi
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (by nlinarith)) (by nlinarith [sq_nonneg δ])
  have hη_lt := h_eta_lt δ hδ0 hδ40
  have hb_band : b ∈ bandUpper (3 / 32) := by
    change |b.im - 1 / 2| < 3 / 32
    rw [abs_lt]; constructor <;> linarith
  have hb_strip : b ∈ imStrip := ⟨by linarith, by linarith⟩
  have hz_bd : ‖zetaD b‖ ≤ 3 := (norm_zetaD_bounds_band hb_band).2
  have h1p_le4 : ‖1 + ((1 - δ : ℝ) : ℂ) * zetaD b‖ ≤ 4 := by
    calc ‖1 + ((1 - δ : ℝ) : ℂ) * zetaD b‖
        ≤ ‖(1 : ℂ)‖ + ‖((1 - δ : ℝ) : ℂ) * zetaD b‖ := norm_add_le _ _
      _ = 1 + (1 - δ) * ‖zetaD b‖ := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ 1 + 1 * 3 := by nlinarith [norm_nonneg (zetaD b)]
      _ = 4 := by norm_num
  have h_id : 1 - ((1 - δ : ℝ) : ℂ) ^ 2 * zetaD b ^ 2 =
      ((2 - 2 * δ + δ ^ 2 : ℝ) : ℂ) * (Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)) /
        ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := by
    have hsin_mul : ((2 - 2 * δ + δ ^ 2 : ℝ) : ℂ) * (Real.sin (π * etaDelta δ) : ℂ) =
        ((√2 * (2 * δ - δ ^ 2) : ℝ) : ℂ) := by
      norm_cast
      rw [h_sin_eta δ hδ0 hδ40, mul_div_cancel₀ _ (by nlinarith [sq_nonneg δ])]
    rw [zetaD_sq_eq_imStrip hb_strip]
    have hden_ne : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
      intro h; have := (norm_sqrt2_add_cosh_bounds hb_band).1; rw [h, norm_zero] at this
      linarith [Real.cosh_pos (π * b.re)]
    field_simp [hden_ne]
    calc (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) - ((1 - δ : ℝ) : ℂ) ^ 2 * ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b))
        = ((2 - 2 * δ + δ ^ 2 : ℝ) : ℂ) * Complex.cosh ((π : ℂ) * b) + ((√2 * (2 * δ - δ ^ 2) : ℝ) : ℂ) := by
          push_cast; ring
      _ = ((2 - 2 * δ + δ ^ 2 : ℝ) : ℂ) * (Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)) := by
          rw [mul_add, hsin_mul]
      _ = (((1 - δ) * 2 + δ ^ 2 : ℝ) : ℂ) * (Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)) := by
          push_cast; ring
  have h_fac2 : 1 - ((1 - δ : ℝ) : ℂ) ^ 2 * zetaD b ^ 2 =
      (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) * (1 + ((1 - δ : ℝ) : ℂ) * zetaD b) := by ring
  have h_lower_sq : (1 / 4 : ℝ) * ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
      ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
    have h1 : ‖1 - ((1 - δ : ℝ) : ℂ) ^ 2 * zetaD b ^ 2‖ ≤ 4 * ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
      rw [h_fac2, norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h1p_le4 (norm_nonneg _)
    have h2 : 1 ≤ 2 - 2 * δ + δ ^ 2 := by nlinarith [sq_nonneg δ]
    have h3 : ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
        ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) ^ 2 * zetaD b ^ 2‖ := by
      rw [h_id, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      gcongr
      calc ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖
          = 1 * ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ := (one_mul _).symm
        _ ≤ (2 - 2 * δ + δ ^ 2) * ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ := by gcongr
    calc (1 / 4 : ℝ) * ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
          ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
        = (1 / 4 : ℝ) * (‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
            ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖) := by ring
      _ ≤ (1 / 4 : ℝ) * ‖1 - ((1 - δ : ℝ) : ℂ) ^ 2 * zetaD b ^ 2‖ := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by linarith only [h1]
  -- Now bound ‖cosh(π b) + sin(π η_δ)‖ / ‖√2 + cosh(π b)‖ from below!
  have hden_up := (norm_sqrt2_add_cosh_bounds hb_band).2
  set u : ℝ := b.re
  set y : ℝ := b.im - 1 / 2
  have hy_lo : -(1 / 16 : ℝ) < y := by dsimp only [y]; linarith
  have hy_hi : y ≤ etaDelta δ / 2 := by dsimp only [y]; linarith
  have hb_eq : b = (u : ℂ) + ((1 / 2 + y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [u, y]
  have h_re_im : (Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).re =
      Real.sin (π * etaDelta δ) - Real.cosh (π * u) * Real.sin (π * y) ∧
      (Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).im =
      Real.sinh (π * u) * Real.cos (π * y) := by
    rw [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero,
      re_cosh', im_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    rw [show π * b.im = π * y + π / 2 by dsimp only [y]; ring, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two]
    constructor <;> ring
  have hcos_y : 1 / 2 ≤ Real.cos (π * y) := by
    have hy_abs : |y| ≤ 1 / 16 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : |π * y| ≤ π / 16 := by
      rw [abs_mul, abs_of_pos hpi]
      calc π * |y| ≤ π * (1 / 16) := mul_le_mul_of_nonneg_left hy_abs hpi.le
        _ = π / 16 := by ring
    rw [← Real.cos_abs (π * y)]
    exact hcos16.trans (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h1)
  have hsin_eta_ge : δ ≤ Real.sin (π * etaDelta δ) := by
    rw [h_sin_eta δ hδ0 hδ40, le_div_iff₀ (by nlinarith [sq_nonneg δ])]
    have hsqrt2_gt : 5 / 4 < √2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h1 : (5 / 4 : ℝ) * (2 * δ - δ ^ 2) < √2 * (2 * δ - δ ^ 2) :=
      mul_lt_mul_of_pos_right hsqrt2_gt (by nlinarith only [hδ0, hδ40])
    have h2 : δ ^ 3 ≤ δ ^ 2 := by nlinarith only [hδ0, hδ40, sq_nonneg δ]
    have h3 : 40 * δ ^ 2 ≤ δ := by nlinarith only [hδ0, hδ40]
    have hexp : δ * (2 - 2 * δ + δ ^ 2) = 2 * δ - 2 * δ ^ 2 + δ ^ 3 := by ring
    linarith only [h1, h2, h3, hexp, hδ0, hδ40, sq_nonneg δ]
  rcases le_or_gt (1 / 8 : ℝ) |u| with hu_ge | hu_lt
  · -- Case 1: |u| ≥ 1/8
    have h_sh_ge : (1 / 4 : ℝ) * Real.cosh (π * u) ≤ |Real.sinh (π * u)| := by
      have h_pos_fn : ∀ t : ℝ, π / 8 ≤ t → (1 / 4 : ℝ) * Real.cosh t ≤ Real.sinh t := by
        intro t ht
        have hexp_ge : 5 / 3 ≤ Real.exp (2 * t) := by
          have h1 := Real.add_one_le_exp (2 * t)
          linarith only [h1, ht, Real.pi_gt_three]
        have hexp_mul : 5 * Real.exp (-t) ≤ 3 * Real.exp t := by
          rw [Real.exp_neg]
          have hpos : 0 < Real.exp t := Real.exp_pos t
          rw [mul_inv_le_iff₀ hpos]
          calc (5 : ℝ) ≤ 3 * Real.exp (2 * t) := by linarith only [hexp_ge]
            _ = 3 * Real.exp t * Real.exp t := by rw [show 2 * t = t + t by ring, Real.exp_add]; ring
        rw [Real.cosh_eq, Real.sinh_eq]
        linarith only [hexp_mul]
      rcases le_or_gt 0 u with hu0 | hu0
      · have h1 : π / 8 ≤ π * u := by rw [abs_of_nonneg hu0] at hu_ge; nlinarith only [hu_ge, hpi]
        exact (h_pos_fn (π * u) h1).trans (le_abs_self _)
      · have h1 : π / 8 ≤ π * (-u) := by rw [abs_of_neg hu0] at hu_ge; nlinarith only [hu_ge, hpi]
        have h2 := h_pos_fn (π * (-u)) h1
        rw [mul_neg, Real.cosh_neg, Real.sinh_neg] at h2
        exact h2.trans (neg_le_abs _)
    have h_im_ge : (1 / 8 : ℝ) * Real.cosh (π * u) ≤
        ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ := by
      calc (1 / 8 : ℝ) * Real.cosh (π * u)
          = (1 / 4 : ℝ) * Real.cosh (π * u) * (1 / 2) := by ring
        _ ≤ |Real.sinh (π * u)| * Real.cos (π * y) := by
            gcongr
        _ = |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).im| := by
            rw [h_re_im.2, abs_mul, abs_of_nonneg (show 0 ≤ Real.cos (π * y) by linarith only [hcos_y])]
        _ ≤ ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ := Complex.abs_im_le_norm _
    have hden_pos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
      have := (norm_sqrt2_add_cosh_bounds hb_band).1; linarith [Real.cosh_pos (π * b.re)]
    have h_ratio : 1 / (8 * (√2 + 1)) ≤ ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
        ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
      rw [le_div_iff₀ hden_pos]
      calc 1 / (8 * (√2 + 1)) * ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
          ≤ 1 / (8 * (√2 + 1)) * ((√2 + 1) * Real.cosh (π * u)) := by gcongr
        _ = (1 / 8 : ℝ) * Real.cosh (π * u) := by
            have : 0 < √2 + 1 := by positivity
            field_simp
        _ ≤ _ := h_im_ge
    have h_min_le : min 1 ‖b - Complex.I / 2‖ + δ ≤ 2 := by
      linarith [min_le_left (1 : ℝ) ‖b - Complex.I / 2‖]
    have hc_le : c_fin * 2 ≤ (1 / 4) * (1 / (8 * (√2 + 1))) := by
      dsimp only [c_fin]
      have hsq2 : 1 ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
      have hp1 : 0 < √2 + 1 := by positivity
      calc 1 / (96 * √2 * (√2 + 1)) * 2
          = 1 / (48 * √2 * (√2 + 1)) := by field_simp; ring
        _ ≤ 1 / (32 * 1 * (√2 + 1)) := by gcongr; norm_num
        _ = (1 / 4) * (1 / (8 * (√2 + 1))) := by field_simp; ring
    calc c_fin * (min 1 ‖b - Complex.I / 2‖ + δ)
        ≤ c_fin * 2 := mul_le_mul_of_nonneg_left h_min_le (by positivity)
      _ ≤ (1 / 4) * (1 / (8 * (√2 + 1))) := hc_le
      _ ≤ (1 / 4) * (‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
            ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖) := by gcongr
      _ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
          rw [mul_div_assoc']; exact h_lower_sq
  · -- Case 2: |u| < 1/8
    have hcosh_u_ge : 1 ≤ Real.cosh (π * u) := Real.one_le_cosh _
    have hcosh_u_le : Real.cosh (π * u) ≤ 4 / 3 := by
      have h1 : |(|π * u|)| ≤ |π / 8| := by
        rw [abs_abs, abs_mul, abs_of_pos hpi, abs_of_pos (by positivity : 0 < π / 8)]
        nlinarith only [hu_lt, hpi]
      rw [← Real.cosh_abs (π * u)]
      exact (Real.cosh_le_cosh.mpr h1).trans hcosh8
    have hden_pos : 0 < ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
      have := (norm_sqrt2_add_cosh_bounds hb_band).1; linarith only [this, Real.cosh_pos (π * b.re)]
    have hden_le : ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ ≤ (√2 + 1) * (4 / 3) := by
      calc ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖
          ≤ (√2 + 1) * Real.cosh (π * u) := hden_up
        _ ≤ (√2 + 1) * (4 / 3) := by gcongr
    have h_sh_ge : π * |u| ≤ |Real.sinh (π * u)| := by
      rcases le_or_gt 0 u with hu0 | hu0
      · rw [abs_of_nonneg hu0]
        exact (le_sinh_of_nonneg (mul_nonneg hpi.le hu0)).trans (le_abs_self _)
      · rw [abs_of_neg hu0, show π * -u = -(π * u) by ring]
        have h1 := le_sinh_of_nonneg (show 0 ≤ -(π * u) by nlinarith only [hpi, hu0])
        rw [Real.sinh_neg] at h1
        exact h1.trans (neg_le_abs _)
    have h_im_ge : (1 / 2 : ℝ) * π * |u| ≤
        |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).im| := by
      rw [h_re_im.2, abs_mul, abs_of_nonneg (show 0 ≤ Real.cos (π * y) by linarith only [hcos_y])]
      calc (1 / 2 : ℝ) * π * |u| = π * |u| * (1 / 2) := by ring
        _ ≤ |Real.sinh (π * u)| * Real.cos (π * y) := by gcongr
    have h_re_ge : (1 / 18 : ℝ) * δ + (1 / 6 : ℝ) * |y| ≤
        |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).re| := by
      rw [h_re_im.1]
      rcases le_or_gt y 0 with hy0 | hy0
      · have hsin_neg : (3 / 2 : ℝ) * |y| ≤ -Real.sin (π * y) := by
          have h1 : Real.sin (π * (-y)) = -Real.sin (π * y) := by
            rw [mul_neg, Real.sin_neg]
          rw [← h1, abs_of_nonpos hy0]
          have hpiy_nn : 0 ≤ π * (-y) := mul_nonneg hpi.le (neg_nonneg.mpr hy0)
          have hpiy_le : π * (-y) ≤ π / 3 := by nlinarith only [hy_lo, hpi]
          have h2 := half_le_sin_of_le_pi_div_three hpiy_nn hpiy_le
          have h3 : (3 / 2 : ℝ) * (-y) ≤ π * (-y) / 2 := by nlinarith only [Real.pi_gt_three, hy0]
          linarith only [h2, h3]
        have h_pos_re : δ + (3 / 2 : ℝ) * |y| ≤ Real.sin (π * etaDelta δ) - Real.cosh (π * u) * Real.sin (π * y) := by
          have h1 : (3 / 2 : ℝ) * |y| ≤ Real.cosh (π * u) * (-Real.sin (π * y)) := by
            calc (3 / 2 : ℝ) * |y| = 1 * ((3 / 2 : ℝ) * |y|) := (one_mul _).symm
              _ ≤ Real.cosh (π * u) * (-Real.sin (π * y)) :=
                  mul_le_mul hcosh_u_ge hsin_neg (by positivity) (by positivity)
          have h2 : Real.cosh (π * u) * (-Real.sin (π * y)) = -(Real.cosh (π * u) * Real.sin (π * y)) := by ring
          linarith only [h1, h2, hsin_eta_ge]
        have h_nn : 0 ≤ Real.sin (π * etaDelta δ) - Real.cosh (π * u) * Real.sin (π * y) := by
          linarith only [h_pos_re, hδ0, abs_nonneg y]
        rw [abs_of_nonneg h_nn]
        linarith only [h_pos_re, hδ0, abs_nonneg y]
      · have h_pi_y_le : π * y ≤ π * etaDelta δ / 2 := by nlinarith only [hy_hi, hpi]
        have h_pi_eta_le : π * etaDelta δ ≤ π / 16 := by nlinarith only [hη_lt, hpi]
        have h_pi_eta_half_le : π * etaDelta δ / 2 ≤ π / 6 := by linarith only [h_pi_eta_le, hpi]
        have hsin_half : Real.sin (π * y) ≤ (2 / 3 : ℝ) * Real.sin (π * etaDelta δ) := by
          have h1 : Real.sin (π * y) ≤ Real.sin (π * etaDelta δ / 2) :=
            Real.strictMonoOn_sin.monotoneOn
              ⟨by nlinarith only [hy0, hpi], by linarith only [h_pi_y_le, h_pi_eta_le, hpi]⟩
              ⟨by nlinarith only [hη_pos, hpi], by linarith only [h_pi_eta_le, hpi]⟩ h_pi_y_le
          have h2 : Real.sin (π * etaDelta δ) = 2 * Real.sin (π * etaDelta δ / 2) * Real.cos (π * etaDelta δ / 2) := by
            have := Real.sin_two_mul (π * etaDelta δ / 2)
            rwa [show 2 * (π * etaDelta δ / 2) = π * etaDelta δ by ring] at this
          have hcos_half : 3 / 4 ≤ Real.cos (π * etaDelta δ / 2) :=
            hcos6.trans (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith only [hpi]) h_pi_eta_half_le)
          have hsin_nn : 0 ≤ Real.sin (π * etaDelta δ / 2) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith only [h_pi_eta_le, hpi])
          nlinarith only [h1, h2, hcos_half, hsin_nn]
        have h_diff : (1 / 9 : ℝ) * Real.sin (π * etaDelta δ) ≤
            Real.sin (π * etaDelta δ) - Real.cosh (π * u) * Real.sin (π * y) := by
          have hsin_nn : 0 ≤ Real.sin (π * y) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith only [h_pi_y_le, h_pi_eta_le, hpi])
          have h1 : Real.cosh (π * u) * Real.sin (π * y) ≤ (4 / 3) * ((2 / 3) * Real.sin (π * etaDelta δ)) :=
            mul_le_mul hcosh_u_le hsin_half hsin_nn (by positivity)
          linarith only [h1]
        have hy_le_sin : 3 * |y| ≤ Real.sin (π * etaDelta δ) := by
          rw [abs_of_pos hy0]
          have h1 : (3 / 2 : ℝ) * etaDelta δ ≤ Real.sin (π * etaDelta δ) := by
            have h2 := half_le_sin_of_le_pi_div_three (by positivity : 0 ≤ π * etaDelta δ) (by linarith only [h_pi_eta_le, hpi])
            have h3 : (3 / 2 : ℝ) * etaDelta δ ≤ π * etaDelta δ / 2 := by nlinarith only [Real.pi_gt_three, hη_pos]
            linarith only [h2, h3]
          linarith only [h1, hy_hi]
        have h_nn : 0 ≤ Real.sin (π * etaDelta δ) - Real.cosh (π * u) * Real.sin (π * y) := by
          have hsn := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity : 0 ≤ π * etaDelta δ) (by linarith only [h_pi_eta_le, hpi])
          linarith only [h_diff, hsn]
        rw [abs_of_nonneg h_nn]
        linarith only [h_diff, hy_le_sin, hsin_eta_ge]
    have hnorm_sum : (1 / √2) * (|(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).re| +
          |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).im|) ≤
          ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ := by
      set z := Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
      rw [mul_pow, Real.sq_sqrt (by norm_num), Complex.sq_norm, Complex.normSq_apply]
      nlinarith only [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im]
    have h_b_le : min 1 ‖b - Complex.I / 2‖ ≤ |u| + |y| := by
      refine (min_le_right _ _).trans ?_
      have h1 : b - Complex.I / 2 = (u : ℂ) + (y : ℂ) * Complex.I := by
        rw [hb_eq]; push_cast; ring
      rw [h1]
      calc ‖(u : ℂ) + (y : ℂ) * Complex.I‖
          ≤ ‖(u : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |u| + |y| := by simp [Complex.norm_real]
    have h_pi2 : (1 : ℝ) ≤ (1 / 2 : ℝ) * π := by linarith only [Real.two_le_pi]
    have h_comb : (1 / 18 : ℝ) * (min 1 ‖b - Complex.I / 2‖ + δ) ≤
        |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).re| +
          |(Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)).im| := by
      have h1 : (1 / 18 : ℝ) * (|u| + |y| + δ) ≤ (1 / 18 : ℝ) * δ + (1 / 6 : ℝ) * |y| + (1 / 2 : ℝ) * π * |u| := by
        nlinarith only [h_pi2, abs_nonneg u, abs_nonneg y]
      linarith only [h1, h_b_le, h_re_ge, h_im_ge]
    have h_c_fin : c_fin ≤ (1 / 4 : ℝ) * ((1 / √2) * (1 / 18)) / ((√2 + 1) * (4 / 3)) := by
      dsimp only [c_fin]
      have hne : √2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hp1 : 0 < √2 + 1 := by positivity
      calc 1 / (96 * √2 * (√2 + 1))
          = (1 / 4 : ℝ) * ((1 / √2) * (1 / 18)) / ((√2 + 1) * (4 / 3)) := by field_simp; ring
        _ ≤ (1 / 4 : ℝ) * ((1 / √2) * (1 / 18)) / ((√2 + 1) * (4 / 3)) := le_rfl
    calc c_fin * (min 1 ‖b - Complex.I / 2‖ + δ)
        ≤ ((1 / 4 : ℝ) * ((1 / √2) * (1 / 18)) / ((√2 + 1) * (4 / 3))) * (min 1 ‖b - Complex.I / 2‖ + δ) :=
          mul_le_mul_of_nonneg_right h_c_fin (by positivity)
      _ = (1 / 4 : ℝ) * ((1 / √2) * ((1 / 18 : ℝ) * (min 1 ‖b - Complex.I / 2‖ + δ))) / ((√2 + 1) * (4 / 3)) := by ring
      _ ≤ (1 / 4 : ℝ) * ‖Complex.cosh ((π : ℂ) * b) + (Real.sin (π * etaDelta δ) : ℂ)‖ /
            ‖(√2 : ℂ) + Complex.cosh ((π : ℂ) * b)‖ := by
          apply div_le_div₀ (by positivity)
          · exact mul_le_mul_of_nonneg_left (hnorm_sum.trans' (mul_le_mul_of_nonneg_left h_comb (by positivity))) (by norm_num)
          · exact hden_pos
          · exact hden_le
      _ ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := h_lower_sq

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
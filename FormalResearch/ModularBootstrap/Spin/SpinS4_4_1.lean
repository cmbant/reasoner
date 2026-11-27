/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS22Strip
public import FormalResearch.ModularBootstrap.Spin.SpinS22Outward

/-!
# Section 4.1 (`s4:4.1`): Charge-Uniform Truncated Outward Inverse and Strip Bound

This module proves `SpinS4_4_1` (`spinning_s4.tex`, Lemma 4.1 / `s4:4.1`), establishing:
1. `(s4:eO1.2)` geometric-tail `L^1(W_c)` bound
   `∫_{x_L, x_R ≥ r₀} |G - G^{[N]}| W_c ≤ C_r (N+1) e^{-4π r₀ N}`,
2. `(s4:eO1.3)` uniform `L^1(W_c)` bound `∫_{x_L, x_R ≥ r₀} |G^{[N]}| W_c ≤ C_r`,
3. `(s4:eO1.4)` polynomial strip bound on `spinTruncInvC` on the adaptive slice
   `|d| ≤ V √ε`, `|Im b| ≤ γ_N / 2`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

section Helpers

lemma spinGamma_mul_spinLambda {a : ℝ} (ha : 2 < a) :
    spinGamma a * spinLambda a = 1 := by
  have ha0 : 0 < a := by linarith
  have h12 : 0 < 1 - 2 / a := by rw [sub_pos, div_lt_one ha0]; linarith
  have hγ : 0 < spinGamma a := by unfold spinGamma; exact Real.sqrt_pos.mpr h12
  unfold spinLambda
  exact mul_inv_cancel₀ hγ.ne'

lemma spinLambda_gt_one_s4 {a : ℝ} (ha : 2 < a) : 1 < spinLambda a := by
  have ha0 : 0 < a := by linarith
  have h12 : 0 < 1 - 2 / a := by rw [sub_pos, div_lt_one ha0]; linarith
  have hγ0 : 0 < spinGamma a := by unfold spinGamma; exact Real.sqrt_pos.mpr h12
  have hγ1 : spinGamma a < 1 := by
    unfold spinGamma; exact (Real.sqrt_lt' one_pos).mpr (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) ha0])
  unfold spinLambda
  exact (one_lt_inv₀ hγ0).mpr hγ1

private lemma spin_a_mul_lambda_sub_one_ge_one_s4 {a : ℝ} (ha : 2 < a) :
    1 ≤ a * (spinLambda a - 1) := by
  have ha0 : 0 < a := by linarith
  have h12 : 0 < 1 - 2 / a := by rw [sub_pos, div_lt_one ha0]; linarith
  have hγ_pos : 0 < spinGamma a := by unfold spinGamma; exact Real.sqrt_pos.mpr h12
  have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := by unfold spinGamma; exact Real.sq_sqrt h12.le
  have hγ_lt1 : spinGamma a < 1 := by
    unfold spinGamma; exact (Real.sqrt_lt' one_pos).mpr (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) ha0])
  have hdiff : 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := by linarith [hγ_sq]
  have hlt : 2 / a < (1 - spinGamma a) * 2 := by
    calc 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := hdiff
      _ < (1 - spinGamma a) * 2 := mul_lt_mul_of_pos_left (by linarith) (sub_pos.mpr hγ_lt1)
  have h1γ : 1 / a < 1 - spinGamma a := by
    have : 2 < a * ((1 - spinGamma a) * 2) := by
      calc 2 = a * (2 / a) := by field_simp [ha0.ne']
        _ < a * ((1 - spinGamma a) * 2) := mul_lt_mul_of_pos_left hlt ha0
    have : 1 < a * (1 - spinGamma a) := by linarith
    calc 1 / a = a⁻¹ := one_div a
      _ < a⁻¹ * (a * (1 - spinGamma a)) := by nlinarith [inv_pos.mpr ha0]
      _ = 1 - spinGamma a := by field_simp [ha0.ne']
  have hlam : spinLambda a - 1 = (1 - spinGamma a) / spinGamma a := by
    unfold spinLambda; field_simp [hγ_pos.ne']
  have hlam_gt : 1 - spinGamma a < spinLambda a - 1 := by
    rw [hlam]; exact lt_div_iff₀ hγ_pos |>.mpr (by nlinarith [sub_pos.mpr hγ_lt1])
  have hmul : 1 < a * (spinLambda a - 1) := by
    calc 1 = a * (1 / a) := by field_simp [ha0.ne']
      _ < a * (spinLambda a - 1) := mul_lt_mul_of_pos_left (h1γ.trans hlam_gt) ha0
  exact hmul.le

private lemma one_le_a_mul_pow_sub_one_s4 {a : ℝ} (ha : 2 < a) (m : ℕ) :
    (m : ℝ) ≤ a * (spinLambda a ^ m - 1) := by
  have hlam1 : 1 ≤ spinLambda a := (spinLambda_gt_one_s4 ha).le
  have hbase : (m : ℝ) * (spinLambda a - 1) ≤ spinLambda a ^ m - 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, pow_succ']
      have h1 : 0 ≤ spinLambda a ^ m - 1 := sub_nonneg.mpr (one_le_pow₀ hlam1)
      have h2 : spinLambda a ^ m - 1 ≤ spinLambda a * (spinLambda a ^ m - 1) :=
        le_mul_of_one_le_left h1 hlam1
      calc ((m : ℝ) + 1) * (spinLambda a - 1)
          = (m : ℝ) * (spinLambda a - 1) + (spinLambda a - 1) := by ring
        _ ≤ spinLambda a * (spinLambda a ^ m - 1) + (spinLambda a - 1) := by linarith
        _ = spinLambda a * spinLambda a ^ m - 1 := by ring
  have h1 := le_mul_of_one_le_right (Nat.cast_nonneg m) (spin_a_mul_lambda_sub_one_ge_one_s4 ha)
  calc (m : ℝ) ≤ (m : ℝ) * (a * (spinLambda a - 1)) := h1
    _ = a * ((m : ℝ) * (spinLambda a - 1)) := by ring
    _ ≤ a * (spinLambda a ^ m - 1) := mul_le_mul_of_nonneg_left hbase (by linarith)

lemma spinWc_pow_le_s4 {a r x : ℝ} (ha : 2 < a) (hr : 0 < r) (hx : r ≤ x) (m : ℕ) :
    spinWc a x ≤ Real.exp (-4 * π * r * (m : ℝ)) * spinWc a (spinLambda a ^ m * x) := by
  have hlam1 : 1 ≤ spinLambda a := (spinLambda_gt_one_s4 ha).le
  have hpow1 : 1 ≤ spinLambda a ^ m := one_le_pow₀ hlam1
  have hx0 : 0 ≤ x := hr.le.trans hx
  have hle : x ≤ spinLambda a ^ m * x := le_mul_of_one_le_left hx0 hpow1
  have hmono := spinWc_exp_mono ha.le hx0 hle
  have hexp_arg : -4 * π * a * (spinLambda a ^ m * x - x) ≤ -4 * π * r * (m : ℝ) := by
    have h1 : (m : ℝ) ≤ a * (spinLambda a ^ m - 1) := one_le_a_mul_pow_sub_one_s4 ha m
    have h2 : (m : ℝ) * r ≤ (a * (spinLambda a ^ m - 1)) * x :=
      mul_le_mul h1 hx hr.le (mul_nonneg (by linarith) (sub_nonneg.mpr hpow1))
    nlinarith [Real.pi_pos]
  have hexp : Real.exp (-(4 * π * a * (spinLambda a ^ m * x - x))) ≤
      Real.exp (-4 * π * r * (m : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact hmono.trans (mul_le_mul_of_nonneg_right hexp (spinWc_nonneg ha.le _))

private lemma spinDeltaA_eq_expand_s4 {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) :
    spinDeltaA a Φ xL xR =
      spinG a Φ (spinLambda a * xL) (spinLambda a * xR) -
        spinG a Φ xL (spinLambda a * xR) -
        spinG a Φ (spinLambda a * xL) xR +
        spinG a Φ xL xR := by
  unfold spinDeltaA spinDa
  have hgl := spinGamma_mul_spinLambda ha
  rw [← mul_assoc, ← mul_assoc, hgl, one_mul, one_mul]

/-- Exact telescoping identity for the truncated outward inverse `spinTruncInv`. -/
lemma spinG_sub_spinTruncInv {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) (N : ℕ) :
    spinG a Φ xL xR - spinTruncInv a N Φ xL xR =
      spinG a Φ xL (spinLambda a ^ N * xR) +
        spinG a Φ (spinLambda a ^ N * xL) xR -
        spinG a Φ (spinLambda a ^ N * xL) (spinLambda a ^ N * xR) := by
  let g : ℕ → ℕ → ℝ := fun j k => spinG a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
  have hstep : ∀ j k : ℕ,
      spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR) =
        (g (j + 1) (k + 1) - g (j + 1) k) - (g j (k + 1) - g j k) := by
    intro j k
    rw [spinDeltaA_eq_expand_s4 ha]
    dsimp [g]; simp only [pow_succ', mul_assoc]; ring
  have hsum_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range N, spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)) =
        (g (j + 1) N - g (j + 1) 0) - (g j N - g j 0) := by
    intro j
    calc ∑ k ∈ Finset.range N, spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
        = ∑ k ∈ Finset.range N, ((g (j + 1) (k + 1) - g (j + 1) k) - (g j (k + 1) - g j k)) :=
            Finset.sum_congr rfl fun k _ => hstep j k
      _ = (∑ k ∈ Finset.range N, (g (j + 1) (k + 1) - g (j + 1) k)) -
            (∑ k ∈ Finset.range N, (g j (k + 1) - g j k)) := Finset.sum_sub_distrib _ _
      _ = (g (j + 1) N - g (j + 1) 0) - (g j N - g j 0) := by
            rw [Finset.sum_range_sub (g (j + 1)), Finset.sum_range_sub (g j)]
  have hsum_jk : spinTruncInv a N Φ xL xR = (g N N - g 0 N) - (g N 0 - g 0 0) := by
    unfold spinTruncInv
    let fN : ℕ → ℝ := fun j => g j N
    let f0 : ℕ → ℝ := fun j => g j 0
    calc ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
        = ∑ j ∈ Finset.range N, ((fN (j + 1) - fN j) - (f0 (j + 1) - f0 j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hsum_k j]; dsimp [fN, f0]; ring
      _ = (∑ j ∈ Finset.range N, (fN (j + 1) - fN j)) -
            (∑ j ∈ Finset.range N, (f0 (j + 1) - f0 j)) := Finset.sum_sub_distrib _ _
      _ = (g N N - g 0 N) - (g N 0 - g 0 0) := by
            rw [Finset.sum_range_sub fN, Finset.sum_range_sub f0]
  have hg00 : g 0 0 = spinG a Φ xL xR := by dsimp [g]; rw [pow_zero, one_mul, one_mul]
  have hg0N : g 0 N = spinG a Φ xL (spinLambda a ^ N * xR) := by dsimp [g]; rw [pow_zero, one_mul]
  have hgN0 : g N 0 = spinG a Φ (spinLambda a ^ N * xL) xR := by dsimp [g]; rw [pow_zero, one_mul]
  have hgNN : g N N = spinG a Φ (spinLambda a ^ N * xL) (spinLambda a ^ N * xR) := rfl
  linarith [hsum_jk, hg00, hg0N, hgN0, hgNN]

lemma integrable_dilate_and_bound_s4 {a r : ℝ} (ha : 2 < a) (hr : 0 < r)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (j k : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
        |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2) volume ∧
      (∫ p in {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2},
          |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
            spinWc a p.1 * spinWc a p.2) ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) * spinM2 a Φ := by
  have ha0 : 0 < a := by linarith
  have hG_int : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume :=
    integrable_spinG_wc ha0 hΦ
  have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hlam := spinLambda_gt_one_s4 ha
  have hc1 : 0 < spinLambda a ^ j := pow_pos (lt_trans zero_lt_one hlam) j
  have hc2 : 0 < spinLambda a ^ k := pow_pos (lt_trans zero_lt_one hlam) k
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ (spinLambda a ^ j) hc1.ne').prodCongr
      (MeasurableEquiv.mulLeft₀ (spinLambda a ^ k) hc2.ne')
  have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal ((spinLambda a ^ j)⁻¹ * (spinLambda a ^ k)⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (spinLambda a ^ j * ·) (spinLambda a ^ k * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
      Real.map_volume_mul_left hc1.ne', Real.map_volume_mul_left hc2.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc1), abs_of_pos (inv_pos.mpr hc2),
      ENNReal.ofReal_mul (inv_pos.mpr hc1).le]
  have hdom : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
        spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) volume := by
    have hf_map : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
        (Measure.map e volume) := by
      rw [hmp]
      exact hG_int.smul_measure ENNReal.ofReal_ne_top
    exact (MeasurePreserving.integrable_comp_emb ⟨e.measurable, rfl⟩ e.measurableEmbedding).mpr hf_map
  have hmeas_dil : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume :=
    ((((hG_cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).abs).mul
      (hWc_cont.comp continuous_fst)).mul (hWc_cont.comp continuous_snd)).aestronglyMeasurable
  have hint_dil : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume := by
    refine hdom.mono' hmeas_dil (Eventually.of_forall fun p => ?_)
    have hw1 : spinWc a p.1 ≤ spinWc a (spinLambda a ^ j * p.1) := by
      refine spinWc_mono_abs ha.le ?_
      rw [abs_mul, abs_of_pos hc1]
      exact le_mul_of_one_le_left (abs_nonneg p.1) (one_le_pow₀ hlam.le)
    have hw2 : spinWc a p.2 ≤ spinWc a (spinLambda a ^ k * p.2) := by
      refine spinWc_mono_abs ha.le ?_
      rw [abs_mul, abs_of_pos hc2]
      exact le_mul_of_one_le_left (abs_nonneg p.2) (one_le_pow₀ hlam.le)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le p.1))
      (spinWc_nonneg ha.le p.2))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2
      (spinWc_nonneg ha.le p.2) (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _))
  refine ⟨hint_dil, ?_⟩
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2}
  have hS_meas : MeasurableSet S := by
    have : S = Set.Ici r ×ˢ Set.Ici r := rfl
    rw [this]; exact measurableSet_Ici.prod measurableSet_Ici
  have hpt : ∀ p ∈ S,
      |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (|spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
    intro p ⟨hp1, hp2⟩
    have hw1 := spinWc_pow_le_s4 ha hr hp1 j
    have hw2 := spinWc_pow_le_s4 ha hr hp2 k
    have hexp : Real.exp (-4 * π * r * (j : ℝ)) * Real.exp (-4 * π * r * (k : ℝ)) =
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hrw1 : 0 ≤ Real.exp (-4 * π * r * (j : ℝ)) * spinWc a (spinLambda a ^ j * p.1) :=
      mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha.le _)
    calc |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2
        ≤ |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
            (Real.exp (-4 * π * r * (j : ℝ)) * spinWc a (spinLambda a ^ j * p.1)) *
            (Real.exp (-4 * π * r * (k : ℝ)) * spinWc a (spinLambda a ^ k * p.2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2
            (spinWc_nonneg ha.le _) (mul_nonneg (abs_nonneg _) hrw1)
      _ = Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
            (|spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
              spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
          rw [← hexp]; ring
  have hmono1 :
      (∫ p in S, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2) ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p in S, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hint_dil.integrableOn (hdom.const_mul _).integrableOn hS_meas hpt
  have hmono2 :
      (∫ p in S, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) ≤
        ∫ p : ℝ × ℝ, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2) :=
    setIntegral_le_integral hdom (Eventually.of_forall fun p =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _))
  have hscale :
      (∫ p : ℝ × ℝ, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) =
        (spinLambda a ^ j * spinLambda a ^ k)⁻¹ * spinM2 a Φ := by
    have hs := integral_prod_scale hc1 hc2 (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
    rw [← spinM2_eq_spinWc ha0 Φ] at hs
    have hne : spinLambda a ^ j * spinLambda a ^ k ≠ 0 := (mul_pos hc1 hc2).ne'
    rw [hs]; field_simp [hne]
  have hinv_le : (spinLambda a ^ j * spinLambda a ^ k)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlam.le) (one_le_pow₀ hlam.le))
  have hM2_nn : 0 ≤ spinM2 a Φ := by
    rw [spinM2_eq_spinWc ha0 Φ]
    exact integral_nonneg fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _))
      (spinWc_nonneg ha.le _)
  calc (∫ p in S, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2)
      ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p in S, |spinG a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := hmono1
    _ ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          ((spinLambda a ^ j * spinLambda a ^ k)⁻¹ * spinM2 a Φ) :=
        mul_le_mul_of_nonneg_left (hmono2.trans_eq hscale) (Real.exp_pos _).le
    _ ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) * (1 * spinM2 a Φ) := by
        gcongr
    _ = Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) * spinM2 a Φ := by rw [one_mul]

private lemma spinLambda_pow_le_exp {c : ℝ} (hc : 49 ≤ c) (m : ℕ)
    (hm : m ≤ Nat.ceil (Real.log (c - 1))) :
    spinLambda ((c - 1) / 12) ^ m ≤ Real.exp 24 := by
  let n := c - 1
  let a := n / 12
  have hn48 : 48 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha4 : 4 ≤ a := by dsimp [a]; linarith
  have ha2 : 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hlam_gt1 := spinLambda_gt_one_s4 ha2
  have hlam_eq : spinLambda a = Real.sqrt (1 + 2 / (a - 2)) := by
    have ha2_pos : 0 < a - 2 := by linarith
    unfold spinLambda spinGamma
    rw [show 1 - 2 / a = (a - 2) / a by field_simp [ha0.ne'], ← Real.sqrt_inv, inv_div,
      show a / (a - 2) = 1 + 2 / (a - 2) by field_simp [ha2_pos.ne']; ring]
  have hlam_le_add : spinLambda a ≤ 1 + 1 / (a - 2) := by
    rw [hlam_eq]
    have ha2_pos : 0 < a - 2 := by linarith
    have hrhs : 0 ≤ 1 + 1 / (a - 2) := by positivity
    refine Real.sqrt_le_iff.mpr ⟨hrhs, ?_⟩
    have hsq : (1 + 1 / (a - 2)) ^ 2 = 1 + 2 / (a - 2) + (1 / (a - 2)) ^ 2 := by ring
    linarith [sq_nonneg (1 / (a - 2))]
  have hlam_le_exp : spinLambda a ≤ Real.exp (24 / n) := by
    have h1 : 1 / (a - 2) ≤ 24 / n := by
      have ha2_ge : n / 24 ≤ a - 2 := by dsimp [a]; linarith
      have ha2_pos : 0 < a - 2 := by linarith
      calc 1 / (a - 2) ≤ 1 / (n / 24) := one_div_le_one_div_of_le (by positivity) ha2_ge
        _ = 24 / n := by ring
    exact hlam_le_add.trans (calc 1 + 1 / (a - 2) ≤ 1 + 24 / n := by linarith
      _ = 24 / n + 1 := add_comm _ _
      _ ≤ Real.exp (24 / n) := Real.add_one_le_exp (24 / n))
  have hN_le_n : (Nat.ceil (Real.log n) : ℝ) ≤ n := by
    have hlog_pos : 0 < Real.log n := Real.log_pos (by linarith)
    have hlt := Nat.ceil_lt_add_one hlog_pos.le
    have hlog_sub := Real.log_le_sub_one_of_pos hn_pos
    linarith
  have hm_le_n : (m : ℝ) ≤ n := (Nat.cast_le.mpr hm).trans hN_le_n
  calc spinLambda a ^ m
      ≤ spinLambda a ^ Nat.ceil (Real.log n) := pow_le_pow_right₀ hlam_gt1.le hm
    _ ≤ Real.exp (24 / n) ^ Nat.ceil (Real.log n) :=
        pow_le_pow_left₀ (lt_trans zero_lt_one hlam_gt1).le hlam_le_exp _
    _ = Real.exp ((Nat.ceil (Real.log n) : ℝ) * (24 / n)) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 24 := by
        refine Real.exp_le_exp.mpr ?_
        calc (Nat.ceil (Real.log n) : ℝ) * (24 / n)
            ≤ n * (24 / n) := mul_le_mul_of_nonneg_right hN_le_n (by positivity)
          _ = 24 := by field_simp [hn_pos.ne']

private lemma continuous_sum_range_s4 {α : Type*} [TopologicalSpace α]
    (N : ℕ) (f : ℕ → α → ℝ) (hf : ∀ j < N, Continuous (f j)) :
    Continuous (fun x => ∑ j ∈ Finset.range N, f j x) := by
  induction N with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp_rw [Finset.sum_range_succ]
    exact (ih fun j hj => hf j (Nat.lt_succ_of_lt hj)).add (hf k (Nat.lt_succ_self k))

private lemma continuous_spinTruncInv_s4 {a : ℝ} {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (N : ℕ) : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
  have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hsc : ∀ c1 c2 : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c1 * p.1) (c2 * p.2)) := fun c1 c2 =>
    hG_cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  unfold spinTruncInv
  refine continuous_sum_range_s4 N _ fun j _ => continuous_sum_range_s4 N _ fun ℓ _ => ?_
  simp only [spinDeltaA, spinDa, ← mul_assoc]
  exact (((hsc _ _).sub (hsc _ _)).sub (hsc _ _)).add (hsc _ _)

private lemma spinTruncInvC_fac_bound {lam_j lam_l bre d V E24 : ℝ}
    (hlamj0 : 0 ≤ lam_j) (hlaml0 : 0 ≤ lam_l) (hlamj : lam_j ≤ E24) (hlaml : lam_l ≤ E24)
    (hd : |d| ≤ V) (_hE : 0 ≤ E24) :
    (1 + 4 * (lam_j * (bre + d)) ^ 2) * (1 + 4 * (lam_l * (bre - d)) ^ 2) ≤
      (1 + 8 * E24 ^ 2 * (1 + V ^ 2)) ^ 2 * (1 + |bre| ^ 2) ^ 2 := by
  have hlamj2 : lam_j ^ 2 ≤ E24 ^ 2 := pow_le_pow_left₀ hlamj0 hlamj 2
  have hlaml2 : lam_l ^ 2 ≤ E24 ^ 2 := pow_le_pow_left₀ hlaml0 hlaml 2
  have hd2 : d ^ 2 ≤ V ^ 2 := by rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hsum1 : (bre + d) ^ 2 ≤ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by
    have h1 : (bre + d) ^ 2 ≤ 2 * bre ^ 2 + 2 * d ^ 2 := by nlinarith [sq_nonneg (bre - d)]
    rw [sq_abs]
    nlinarith [sq_nonneg bre, sq_nonneg V]
  have hsum2 : (bre - d) ^ 2 ≤ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by
    have h1 : (bre - d) ^ 2 ≤ 2 * bre ^ 2 + 2 * d ^ 2 := by nlinarith [sq_nonneg (bre + d)]
    rw [sq_abs]
    nlinarith [sq_nonneg bre, sq_nonneg V]
  have hpL : (lam_j * (bre + d)) ^ 2 ≤ 2 * E24 ^ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by
    rw [mul_pow]
    calc lam_j ^ 2 * (bre + d) ^ 2
        ≤ E24 ^ 2 * (2 * (1 + V ^ 2) * (1 + |bre| ^ 2)) :=
          mul_le_mul hlamj2 hsum1 (sq_nonneg _) (sq_nonneg _)
      _ = 2 * E24 ^ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by ring
  have hpR : (lam_l * (bre - d)) ^ 2 ≤ 2 * E24 ^ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by
    rw [mul_pow]
    calc lam_l ^ 2 * (bre - d) ^ 2
        ≤ E24 ^ 2 * (2 * (1 + V ^ 2) * (1 + |bre| ^ 2)) :=
          mul_le_mul hlaml2 hsum2 (sq_nonneg _) (sq_nonneg _)
      _ = 2 * E24 ^ 2 * (1 + V ^ 2) * (1 + |bre| ^ 2) := by ring
  have hfacL : 1 + 4 * (lam_j * (bre + d)) ^ 2 ≤ (1 + 8 * E24 ^ 2 * (1 + V ^ 2)) * (1 + |bre| ^ 2) := by
    nlinarith [sq_nonneg |bre|, sq_nonneg E24, sq_nonneg V]
  have hfacR : 1 + 4 * (lam_l * (bre - d)) ^ 2 ≤ (1 + 8 * E24 ^ 2 * (1 + V ^ 2)) * (1 + |bre| ^ 2) := by
    nlinarith [sq_nonneg |bre|, sq_nonneg E24, sq_nonneg V]
  calc (1 + 4 * (lam_j * (bre + d)) ^ 2) * (1 + 4 * (lam_l * (bre - d)) ^ 2)
      ≤ ((1 + 8 * E24 ^ 2 * (1 + V ^ 2)) * (1 + |bre| ^ 2)) *
          ((1 + 8 * E24 ^ 2 * (1 + V ^ 2)) * (1 + |bre| ^ 2)) :=
        mul_le_mul hfacL hfacR (by positivity) (by positivity)
    _ = (1 + 8 * E24 ^ 2 * (1 + V ^ 2)) ^ 2 * (1 + |bre| ^ 2) ^ 2 := by ring

end Helpers

/-- **`s4:4.1` (`spinning_s4.tex`, Lemma 4.1): charge-uniform truncated outward inverse
and polynomial strip bound.** -/
theorem spinS4_4_1 : SpinS4_4_1 := by
  intro r₀ V hr₀ hV
  let C_r : ℝ := 4
  let C_V : ℝ := (1 + 8 * Real.exp 24 ^ 2 * (1 + V ^ 2)) ^ 2
  let c₀ : ℝ := 49
  refine ⟨C_r, C_V, c₀, by norm_num, by positivity, by norm_num, ?_⟩
  intro c hc n a ε N γN Φ hΦ hM2
  have hc49 : 49 ≤ c := hc
  have hn48 : 48 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha2 : 2 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hlam_gt1 := spinLambda_gt_one_s4 ha2
  let S : Set (ℝ × ℝ) := {q : ℝ × ℝ | r₀ ≤ q.1 ∧ r₀ ≤ q.2}
  have hS_meas : MeasurableSet S := by
    have : S = Set.Ici r₀ ×ˢ Set.Ici r₀ := rfl
    rw [this]; exact measurableSet_Ici.prod measurableSet_Ici
  obtain ⟨h0N_int, h0N_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ 0 N
  obtain ⟨hN0_int, hN0_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ N 0
  obtain ⟨hNN_int, hNN_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr₀ hΦ N N
  have h0N_eq : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by
    ext p; rw [pow_zero, one_mul]
  have hN0_eq : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by
    ext p; rw [pow_zero, one_mul]
  rw [← h0N_eq] at h0N_int h0N_bd
  rw [← hN0_eq] at hN0_int hN0_bd
  have hdiff_int : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume := by
    refine ((h0N_int.add hN0_int).add hNN_int).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
        unfold spinG
        exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
      have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
      have hT_cont := continuous_spinTruncInv_s4 hΦ N
      exact (((hG_cont.sub hT_cont).abs.mul (hWc_cont.comp continuous_fst)).mul
        (hWc_cont.comp continuous_snd)).aestronglyMeasurable
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hw1) hw2),
        spinG_sub_spinTruncInv ha2]
      have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
        (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [sub_zero, zero_sub, abs_neg] at hab2
      have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
          spinG a Φ (spinLambda a ^ N * p.1) p.2 -
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by linarith
      calc |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
              spinG a Φ (spinLambda a ^ N * p.1) p.2 -
              spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2
          ≤ (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
              |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)|) *
              spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by ring
  have htail_bd : ∫ p in S,
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
        3 * Real.exp (-4 * π * r₀ * (N : ℝ)) := by
    have hpt : ∀ p ∈ S,
        |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by
      intro p _
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [spinG_sub_spinTruncInv ha2]
      have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
        (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [sub_zero, zero_sub, abs_neg] at hab2
      have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
          spinG a Φ (spinLambda a ^ N * p.1) p.2 -
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by linarith
      calc |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
              spinG a Φ (spinLambda a ^ N * p.1) p.2 -
              spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2
          ≤ (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
              |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)|) *
              spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by ring
    have h0N_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S) := h0N_int.integrableOn
    have hN0_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S) := hN0_int.integrableOn
    have hNN_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) (volume.restrict S) := hNN_int.integrableOn
    have hmono := setIntegral_mono_on hdiff_int.integrableOn
      ((h0N_S.add hN0_S).add hNN_S) hS_meas hpt
    have hadd1 := integral_add (h0N_S.add hN0_S) hNN_S
    have hadd2 := integral_add h0N_S hN0_S
    have hexp_NN : Real.exp (-4 * π * r₀ * ((N + N : ℕ) : ℝ)) ≤ Real.exp (-4 * π * r₀ * (N : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      push_cast
      have : 0 ≤ 4 * π * r₀ * (N : ℝ) := by positivity
      linarith
    rw [hM2, mul_one] at h0N_bd hN0_bd hNN_bd
    have h0N_bd' : ∫ p in S, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
        Real.exp (-4 * π * r₀ * (N : ℝ)) := by
      simpa using h0N_bd
    have hN0_bd' : ∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 ≤
        Real.exp (-4 * π * r₀ * (N : ℝ)) := by
      simpa using hN0_bd
    have hNN_bd' : ∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2 ≤ Real.exp (-4 * π * r₀ * (N : ℝ)) :=
      hNN_bd.trans hexp_NN
    have hsum_eq : (∫ p in S, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
        (∫ p in S, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) +
        (∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) +
        (∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
          spinWc a p.1 * spinWc a p.2) := by
      calc _ = (∫ p in S, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) +
            (∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
              spinWc a p.1 * spinWc a p.2) := hadd1
        _ = _ := by rw [hadd2]
    calc ∫ p in S, |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
        ≤ ∫ p in S, (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) := hmono
      _ = (∫ p in S, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) +
          (∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) +
          (∫ p in S, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
            spinWc a p.1 * spinWc a p.2) := hsum_eq
      _ ≤ Real.exp (-4 * π * r₀ * (N : ℝ)) + Real.exp (-4 * π * r₀ * (N : ℝ)) +
          Real.exp (-4 * π * r₀ * (N : ℝ)) := add_le_add (add_le_add h0N_bd' hN0_bd') hNN_bd'
      _ = 3 * Real.exp (-4 * π * r₀ * (N : ℝ)) := by ring
  have hclause1 : ∫ p in S,
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
        C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * r₀ * (N : ℝ)) := by
    have h3 : (3 : ℝ) * Real.exp (-4 * π * r₀ * (N : ℝ)) ≤
        C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * r₀ * (N : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      dsimp [C_r]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact htail_bd.trans h3
  have hclause2 : ∫ p in S, |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤ C_r := by
    have hG_int := integrable_spinG_wc ha0 hΦ
    have hT_int : Integrable (fun p : ℝ × ℝ => |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
        volume := by
      refine (hdiff_int.add hG_int).mono' ?_ (Eventually.of_forall fun p => ?_)
      · have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
          unfold spinG
          exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
        have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
        have hT_cont := continuous_spinTruncInv_s4 hΦ N
        exact ((hT_cont.abs.mul (hWc_cont.comp continuous_fst)).mul
          (hWc_cont.comp continuous_snd)).aestronglyMeasurable
      · have hw1 := spinWc_nonneg ha2.le p.1
        have hw2 := spinWc_nonneg ha2.le p.2
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hw1) hw2)]
        have hab : |spinTruncInv a N Φ p.1 p.2| ≤
            |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| + |spinG a Φ p.1 p.2| := by
          have := abs_add_le (-(spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2)) (spinG a Φ p.1 p.2)
          rw [abs_neg] at this
          simpa [sub_eq_add_neg, add_assoc] using this
        calc |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
            ≤ (|spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| + |spinG a Φ p.1 p.2|) *
                spinWc a p.1 * spinWc a p.2 := by gcongr
          _ = |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 +
              |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by ring
    have hpt : ∀ p ∈ S,
        |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
          |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
      intro p _
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have hab : |spinTruncInv a N Φ p.1 p.2| ≤
          |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| + |spinG a Φ p.1 p.2| := by
        have := abs_add_le (-(spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2)) (spinG a Φ p.1 p.2)
        rw [abs_neg] at this
        simpa [sub_eq_add_neg, add_assoc] using this
      calc |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
          ≤ (|spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| + |spinG a Φ p.1 p.2|) *
              spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by ring
    have hdiff_S : Integrable (fun p : ℝ × ℝ =>
        |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S) := hdiff_int.integrableOn
    have hG_S_int : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S) := hG_int.integrableOn
    have hmono := setIntegral_mono_on hT_int.integrableOn (hdiff_S.add hG_S_int) hS_meas hpt
    have hadd := integral_add hdiff_S hG_S_int
    have hG_S : ∫ p in S, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤ 1 := by
      rw [← hM2, spinM2_eq_spinWc ha0 Φ]
      exact setIntegral_le_integral hG_int (Eventually.of_forall fun p =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _))
    have hexp_le1 : Real.exp (-4 * π * r₀ * (N : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ 4 * π * r₀ * (N : ℝ) := by positivity
      linarith
    have hsum_eq : (∫ p in S, |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) =
        (∫ p in S, |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) +
        (∫ p in S, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := hadd
    calc ∫ p in S, |spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
        ≤ ∫ p in S, (|spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := hmono
      _ = (∫ p in S, |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) +
          (∫ p in S, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := hsum_eq
      _ ≤ 3 * Real.exp (-4 * π * r₀ * (N : ℝ)) + 1 := add_le_add htail_bd hG_S
      _ ≤ 3 * 1 + 1 := by gcongr
      _ = C_r := by dsimp [C_r]; norm_num
  refine ⟨hclause1, hclause2, ?_⟩
  intro d b hd hb
  have hN_pos : 1 ≤ N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  have hε_le1 : ε ≤ 1 := by
    dsimp [ε]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hd_le : |d| ≤ V := hd.trans (by
    calc V * Real.sqrt ε ≤ V * Real.sqrt 1 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hε_le1) hV.le
      _ = V := by rw [Real.sqrt_one, mul_one])
  have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_pos).symm
  have hN_pow : spinLambda a ^ N = spinLambda a ^ (N - 1) * spinLambda a := by
    conv_lhs => rw [hN1, pow_succ]
  have hglam : spinLambda a ^ N * γN = 1 := by
    dsimp [γN]; rw [hN_pow]
    calc (spinLambda a ^ (N - 1) * spinLambda a) * (spinGamma a * (spinLambda a ^ (N - 1))⁻¹)
        = (spinGamma a * spinLambda a) * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹) := by ring
      _ = 1 * 1 := by rw [spinGamma_mul_spinLambda ha2, mul_inv_cancel₀ (pow_pos (lt_trans zero_lt_one hlam_gt1) _).ne']
      _ = 1 := one_mul 1
  have hterm : ∀ j ℓ : ℕ, j < N → ℓ < N →
      ‖spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
          ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))‖ ≤
        C_V * (1 + |b.re| ^ 2) ^ 2 := by
    intro j ℓ hj hℓ
    let bL : ℂ := ((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ))
    let bR : ℂ := ((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))
    have hΔ_eq : spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
        ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ))) = spinDaC a Φ bL bR := by
      unfold spinDeltaAC
      congr 1 <;> [simp [bL, pow_succ', mul_assoc]; simp [bR, pow_succ', mul_assoc]]
    have hlam_nn : 0 ≤ spinLambda a := (lt_trans zero_lt_one hlam_gt1).le
    have hbL_im : |bL.im| ≤ 1 / 2 := by
      have him : bL.im = spinLambda a ^ (j + 1) * b.im := by
        dsimp [bL]
        rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero]
      rw [him, abs_mul, abs_of_nonneg (pow_nonneg hlam_nn _)]
      have hpow : spinLambda a ^ (j + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hj
      calc spinLambda a ^ (j + 1) * |b.im|
          ≤ spinLambda a ^ N * (γN / 2) := mul_le_mul hpow hb (abs_nonneg _) (pow_nonneg hlam_nn _)
        _ = (spinLambda a ^ N * γN) / 2 := by ring
        _ = 1 / 2 := by rw [hglam]
    have hbR_im : |bR.im| ≤ 1 / 2 := by
      have him : bR.im = spinLambda a ^ (ℓ + 1) * b.im := by
        dsimp [bR]
        rw [Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im, sub_zero]
      rw [him, abs_mul, abs_of_nonneg (pow_nonneg hlam_nn _)]
      have hpow : spinLambda a ^ (ℓ + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hℓ
      calc spinLambda a ^ (ℓ + 1) * |b.im|
          ≤ spinLambda a ^ N * (γN / 2) := mul_le_mul hpow hb (abs_nonneg _) (pow_nonneg hlam_nn _)
        _ = (spinLambda a ^ N * γN) / 2 := by ring
        _ = 1 / 2 := by rw [hglam]
    have hda := norm_spinDaC_le ha2.le hΦ hbL_im hbR_im
    rw [hΔ_eq]
    rw [hM2, mul_one] at hda
    have hlamj_bd : spinLambda a ^ (j + 1) ≤ Real.exp 24 := spinLambda_pow_le_exp hc49 (j + 1) hj
    have hlaml_bd : spinLambda a ^ (ℓ + 1) ≤ Real.exp 24 := spinLambda_pow_le_exp hc49 (ℓ + 1) hℓ
    have hreL : bL.re = spinLambda a ^ (j + 1) * (b.re + d) := by
      dsimp [bL]
      rw [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
    have hreR : bR.re = spinLambda a ^ (ℓ + 1) * (b.re - d) := by
      dsimp [bR]
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
    have hbd := spinTruncInvC_fac_bound (bre := b.re) (pow_nonneg hlam_nn _)
      (pow_nonneg hlam_nn _) hlamj_bd hlaml_bd hd_le (Real.exp_pos 24).le
    rw [← hreL, ← hreR] at hbd
    exact hda.trans (hbd.trans_eq rfl)
  unfold spinTruncInvC
  calc ‖∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
          spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))‖
      ≤ ∑ j ∈ Finset.range N, ‖∑ ℓ ∈ Finset.range N,
          spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
          ‖spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ∑ _ℓ ∈ Finset.range N, (C_V * (1 + |b.re| ^ 2) ^ 2) :=
        Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun ℓ hℓ => hterm j ℓ (Finset.mem_range.mp hj) (Finset.mem_range.mp hℓ)
    _ = C_V * (N : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2 := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_4_1

end FormalResearch.ModularBootstrap.Spin

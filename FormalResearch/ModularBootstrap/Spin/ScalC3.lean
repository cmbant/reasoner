module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS22Outward
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Lemma `scal:C3`: Double-Difference Inversion and Tail Decay

Proves `ScalC3` (`spinning_calibration.tex`, Lemma `scal:C3`):
for every `r > 0`, there is `C_r > 0` such that for all `c ≥ 40` (`a = (c - 1) / 12`),
`Φ ∈ \overline{\mathcal A}_{\rm spin}`, and `N : ℕ`:
1. `∬_{[r, ∞)²} |\mathcal G(x_L, x_R)| w_c(x_L) w_c(x_R) ≤ (1 - e^{-4π r})^{-2} ∬ |\Delta_a \mathcal G| w_c ⊗ w_c`,
2. `∑_{m + n ≥ N} ∬_{[r, ∞)²} |\Delta_a \mathcal G(λ^m x_L, λ^n x_R)| w_c(x_L) w_c(x_R) ≤ C_r (N + 1) e^{-4π r N} ∬ |\Delta_a \mathcal G| w_c ⊗ w_c`.

Both bounds hold with `C_r = (1 - e^{-4π r})^{-2}` via the finite telescoping identity for
`\Delta_a \mathcal G` and monotonicity of `w_c(x) e^{-4π a x}` (`spinWc_exp_mono`) using
`a (λ - 1) ≥ 1`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

section Helpers

private lemma spin_a_mul_lambda_sub_one_ge_one {a : ℝ} (ha : 2 < a) :
    1 ≤ a * (spinLambda a - 1) := by
  have ha0 : 0 < a := by linarith
  have hγ_pos : 0 < spinGamma a := spinGamma_pos ha
  have hγ_lt : spinGamma a < 1 := spinGamma_lt_one ha
  have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha.le
  have hdiff : 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := by nlinarith
  have h1γ : 1 / a < 1 - spinGamma a := by
    have hadd : 1 + spinGamma a < 2 := by linarith
    have hpos : 0 < 1 - spinGamma a := sub_pos.mpr hγ_lt
    have hlt : 2 / a < (1 - spinGamma a) * 2 := by
      calc 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := hdiff
        _ < (1 - spinGamma a) * 2 := mul_lt_mul_of_pos_left hadd hpos
    have hmul_lt : 2 < a * ((1 - spinGamma a) * 2) := by
      calc 2 = a * (2 / a) := by field_simp [ha0.ne']
        _ < a * ((1 - spinGamma a) * 2) := mul_lt_mul_of_pos_left hlt ha0
    have ha_inv : 1 < a * (1 - spinGamma a) := by linarith
    calc 1 / a = a⁻¹ := one_div a
      _ < a⁻¹ * (a * (1 - spinGamma a)) := by nlinarith [inv_pos.mpr ha0]
      _ = 1 - spinGamma a := by field_simp [ha0.ne']
  have hlam : spinLambda a - 1 = (1 - spinGamma a) / spinGamma a := by
    unfold spinLambda
    field_simp [hγ_pos.ne']
  have hlam_gt : 1 - spinGamma a < spinLambda a - 1 := by
    rw [hlam]
    exact lt_div_iff₀ hγ_pos |>.mpr (by nlinarith)
  have hmul : 1 < a * (spinLambda a - 1) := by
    calc 1 = a * (1 / a) := by field_simp [ha0.ne']
      _ < a * (spinLambda a - 1) := mul_lt_mul_of_pos_left (h1γ.trans hlam_gt) ha0
  exact hmul.le

private lemma one_le_a_mul_pow_sub_one {a : ℝ} (ha : 2 < a) (m : ℕ) :
    (m : ℝ) ≤ a * (spinLambda a ^ m - 1) := by
  have hlam1 : 1 ≤ spinLambda a := (spinLambda_gt_one ha).le
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
  have ha0 : 0 ≤ a := by linarith
  have h1 : (m : ℝ) ≤ (m : ℝ) * (a * (spinLambda a - 1)) :=
    le_mul_of_one_le_right (Nat.cast_nonneg m) (spin_a_mul_lambda_sub_one_ge_one ha)
  calc (m : ℝ) ≤ (m : ℝ) * (a * (spinLambda a - 1)) := h1
    _ = a * ((m : ℝ) * (spinLambda a - 1)) := by ring
    _ ≤ a * (spinLambda a ^ m - 1) := mul_le_mul_of_nonneg_left hbase ha0

private lemma spinWc_pow_le {a r x : ℝ} (ha : 2 < a) (hr : 0 < r) (hx : r ≤ x) (m : ℕ) :
    spinWc a x ≤ Real.exp (-4 * π * r * (m : ℝ)) * spinWc a (spinLambda a ^ m * x) := by
  have hlam1 : 1 ≤ spinLambda a := (spinLambda_gt_one ha).le
  have hpow1 : 1 ≤ spinLambda a ^ m := one_le_pow₀ hlam1
  have hx0 : 0 ≤ x := hr.le.trans hx
  have hle : x ≤ spinLambda a ^ m * x := le_mul_of_one_le_left hx0 hpow1
  have hmono := spinWc_exp_mono ha.le hx0 hle
  have hexp_arg : -4 * π * a * (spinLambda a ^ m * x - x) ≤ -4 * π * r * (m : ℝ) := by
    have h1 : (m : ℝ) ≤ a * (spinLambda a ^ m - 1) := one_le_a_mul_pow_sub_one ha m
    have h2 : (m : ℝ) * r ≤ (a * (spinLambda a ^ m - 1)) * x :=
      mul_le_mul h1 hx hr.le (mul_nonneg (by linarith) (sub_nonneg.mpr hpow1))
    have h4pi : 0 ≤ 4 * π := by positivity
    nlinarith
  have hexp : Real.exp (-(4 * π * a * (spinLambda a ^ m * x - x))) ≤
      Real.exp (-4 * π * r * (m : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  exact hmono.trans (mul_le_mul_of_nonneg_right hexp (spinWc_nonneg ha.le _))

private lemma spinDeltaA_eq_expand {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) :
    spinDeltaA a Φ xL xR =
      spinG a Φ (spinLambda a * xL) (spinLambda a * xR) -
        spinG a Φ xL (spinLambda a * xR) -
        spinG a Φ (spinLambda a * xL) xR +
        spinG a Φ xL xR := by
  unfold spinDeltaA spinDa
  have hγ_pos : 0 < spinGamma a := spinGamma_pos ha
  have hgl : spinGamma a * spinLambda a = 1 := by
    unfold spinLambda
    exact mul_inv_cancel₀ hγ_pos.ne'
  rw [← mul_assoc, ← mul_assoc, hgl, one_mul, one_mul]

private lemma spinG_telescope {a : ℝ} (ha : 2 < a) (Φ : ℝ × ℝ → ℝ) (xL xR : ℝ) (J : ℕ) :
    spinG a Φ xL xR =
      (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
        spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)) -
        spinG a Φ (spinLambda a ^ J * xL) (spinLambda a ^ J * xR) +
        spinG a Φ xL (spinLambda a ^ J * xR) +
        spinG a Φ (spinLambda a ^ J * xL) xR := by
  let g : ℕ → ℕ → ℝ := fun j k => spinG a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
  have hstep : ∀ j k : ℕ,
      spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR) =
        (g (j + 1) (k + 1) - g (j + 1) k) - (g j (k + 1) - g j k) := by
    intro j k
    rw [spinDeltaA_eq_expand ha]
    dsimp [g]
    simp only [pow_succ', mul_assoc]
    ring
  have hsum_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range J, spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)) =
        (g (j + 1) J - g (j + 1) 0) - (g j J - g j 0) := by
    intro j
    calc ∑ k ∈ Finset.range J, spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
        = ∑ k ∈ Finset.range J, ((g (j + 1) (k + 1) - g (j + 1) k) - (g j (k + 1) - g j k)) := by
            refine Finset.sum_congr rfl fun k _ => hstep j k
      _ = (∑ k ∈ Finset.range J, (g (j + 1) (k + 1) - g (j + 1) k)) -
            (∑ k ∈ Finset.range J, (g j (k + 1) - g j k)) := Finset.sum_sub_distrib _ _
      _ = (g (j + 1) J - g (j + 1) 0) - (g j J - g j 0) := by
            rw [Finset.sum_range_sub (g (j + 1)), Finset.sum_range_sub (g j)]
  have hsum_jk :
      (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
        spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)) =
        (g J J - g 0 J) - (g J 0 - g 0 0) := by
    let fJ : ℕ → ℝ := fun j => g j J
    let f0 : ℕ → ℝ := fun j => g j 0
    calc ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
          spinDeltaA a Φ (spinLambda a ^ j * xL) (spinLambda a ^ k * xR)
        = ∑ j ∈ Finset.range J, ((fJ (j + 1) - fJ j) - (f0 (j + 1) - f0 j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hsum_k j]
            dsimp [fJ, f0]; ring
      _ = (∑ j ∈ Finset.range J, (fJ (j + 1) - fJ j)) -
            (∑ j ∈ Finset.range J, (f0 (j + 1) - f0 j)) := Finset.sum_sub_distrib _ _
      _ = (g J J - g 0 J) - (g J 0 - g 0 0) := by
            rw [Finset.sum_range_sub fJ, Finset.sum_range_sub f0]
  have hg00 : g 0 0 = spinG a Φ xL xR := by dsimp [g]; rw [pow_zero, one_mul, one_mul]
  have hg0J : g 0 J = spinG a Φ xL (spinLambda a ^ J * xR) := by dsimp [g]; rw [pow_zero, one_mul]
  have hgJ0 : g J 0 = spinG a Φ (spinLambda a ^ J * xL) xR := by dsimp [g]; rw [pow_zero, one_mul]
  have hgJJ : g J J = spinG a Φ (spinLambda a ^ J * xL) (spinLambda a ^ J * xR) := rfl
  linarith [hsum_jk, hg00, hg0J, hgJ0, hgJJ]

private lemma integrable_dilate_wc {a : ℝ} (ha : 2 < a) {f : ℝ × ℝ → ℝ}
    (hf_int : Integrable (fun p : ℝ × ℝ => |f p| * spinWc a p.1 * spinWc a p.2) volume)
    {j k : ℕ} (hf_dil_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume) :
    Integrable (fun p : ℝ × ℝ => |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume ∧
      Integrable (fun p : ℝ × ℝ => |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) volume := by
  have hc1 : 0 < spinLambda a ^ j := pow_pos (lt_trans zero_lt_one (spinLambda_gt_one ha)) j
  have hc2 : 0 < spinLambda a ^ k := pow_pos (lt_trans zero_lt_one (spinLambda_gt_one ha)) k
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
      |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) volume := by
    have hf_map : Integrable (fun p : ℝ × ℝ => |f p| * spinWc a p.1 * spinWc a p.2)
        (Measure.map e volume) := by
      rw [hmp]
      exact hf_int.smul_measure ENNReal.ofReal_ne_top
    exact (MeasurePreserving.integrable_comp_emb ⟨e.measurable, rfl⟩ e.measurableEmbedding).mpr hf_map
  refine ⟨?_, hdom⟩
  refine hdom.mono' hf_dil_meas (Eventually.of_forall fun p => ?_)
  have hw1 : spinWc a p.1 ≤ spinWc a (spinLambda a ^ j * p.1) := by
    refine spinWc_mono_abs ha.le ?_
    rw [abs_mul, abs_of_pos hc1]
    exact le_mul_of_one_le_left (abs_nonneg p.1) (one_le_pow₀ (spinLambda_gt_one ha).le)
  have hw2 : spinWc a p.2 ≤ spinWc a (spinLambda a ^ k * p.2) := by
    refine spinWc_mono_abs ha.le ?_
    rw [abs_mul, abs_of_pos hc2]
    exact le_mul_of_one_le_left (abs_nonneg p.2) (one_le_pow₀ (spinLambda_gt_one ha).le)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le p.1))
    (spinWc_nonneg ha.le p.2))]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2
    (spinWc_nonneg ha.le p.2) (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _))

private lemma integrable_dilate_and_bound {a r : ℝ} (ha : 2 < a) (hr : 0 < r)
    {f : ℝ × ℝ → ℝ} (hf_cont : Continuous f)
    (hf_int : Integrable (fun p : ℝ × ℝ => |f p| * spinWc a p.1 * spinWc a p.2) volume)
    (j k : ℕ) :
    Integrable (fun p : ℝ × ℝ => |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume ∧
      (∫ p in {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2},
        |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2) ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2) := by
  have hcont_wc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hmeas_dil : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
        spinWc a p.1 * spinWc a p.2) volume :=
    ((((hf_cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).abs).mul
      (hcont_wc.comp continuous_fst)).mul (hcont_wc.comp continuous_snd)).aestronglyMeasurable
  obtain ⟨hint_dil, hint_dom⟩ := integrable_dilate_wc ha hf_int hmeas_dil
  refine ⟨hint_dil, ?_⟩
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2}
  have hS_eq : S = Set.Ici r ×ˢ Set.Ici r := rfl
  have hS_meas : MeasurableSet S := by rw [hS_eq]; exact measurableSet_Ici.prod measurableSet_Ici
  have hpt : ∀ p ∈ S,
      |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (|f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
    intro p ⟨hp1, hp2⟩
    have hw1 := spinWc_pow_le ha hr hp1 j
    have hw2 := spinWc_pow_le ha hr hp2 k
    have hexp : Real.exp (-4 * π * r * (j : ℝ)) * Real.exp (-4 * π * r * (k : ℝ)) =
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hrw1 : 0 ≤ Real.exp (-4 * π * r * (j : ℝ)) * spinWc a (spinLambda a ^ j * p.1) :=
      mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha.le _)
    have hrw2 : 0 ≤ Real.exp (-4 * π * r * (k : ℝ)) * spinWc a (spinLambda a ^ k * p.2) :=
      mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha.le _)
    have hmul : |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2 ≤
        |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          (Real.exp (-4 * π * r * (j : ℝ)) * spinWc a (spinLambda a ^ j * p.1)) *
          (Real.exp (-4 * π * r * (k : ℝ)) * spinWc a (spinLambda a ^ k * p.2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2
        (spinWc_nonneg ha.le p.2) (mul_nonneg (abs_nonneg _) hrw1)
    calc |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| * spinWc a p.1 * spinWc a p.2
        ≤ |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
            (Real.exp (-4 * π * r * (j : ℝ)) * spinWc a (spinLambda a ^ j * p.1)) *
            (Real.exp (-4 * π * r * (k : ℝ)) * spinWc a (spinLambda a ^ k * p.2)) := hmul
      _ = Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
            (|f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
              spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
          rw [← hexp]; ring
  have hmono1 :
      (∫ p in S, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2) ≤
        Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p in S, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hint_dil.integrableOn
      (hint_dom.const_mul _).integrableOn hS_meas (fun p hp => hpt p hp)
  have hmono2 :
      (∫ p in S, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) ≤
        ∫ p : ℝ × ℝ, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2) :=
    setIntegral_le_integral hint_dom (Eventually.of_forall fun p =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _))
  have hc1 : 0 < spinLambda a ^ j := pow_pos (lt_trans zero_lt_one (spinLambda_gt_one ha)) j
  have hc2 : 0 < spinLambda a ^ k := pow_pos (lt_trans zero_lt_one (spinLambda_gt_one ha)) k
  have hscale :
      (∫ p : ℝ × ℝ, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) =
        (spinLambda a ^ j * spinLambda a ^ k)⁻¹ *
          (∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2) := by
    have hs := integral_prod_scale hc1 hc2 (fun p : ℝ × ℝ => |f p| * spinWc a p.1 * spinWc a p.2)
    have hne : spinLambda a ^ j * spinLambda a ^ k ≠ 0 := (mul_pos hc1 hc2).ne'
    rw [hs]
    field_simp [hne]
  have hinv_le : (spinLambda a ^ j * spinLambda a ^ k)⁻¹ ≤ 1 := by
    have hge : 1 ≤ spinLambda a ^ j * spinLambda a ^ k := by
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ spinLambda a ^ j * spinLambda a ^ k :=
            mul_le_mul (one_le_pow₀ (spinLambda_gt_one ha).le)
              (one_le_pow₀ (spinLambda_gt_one ha).le) zero_le_one
              (pow_nonneg (lt_trans zero_lt_one (spinLambda_gt_one ha)).le j)
    exact inv_le_one_of_one_le₀ hge
  have hI_nonneg : 0 ≤ ∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2 :=
    integral_nonneg fun p =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _)
  calc (∫ p in S, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2)
      ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p in S, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) := hmono1
    _ ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p : ℝ × ℝ, |f (spinLambda a ^ j * p.1, spinLambda a ^ k * p.2)| *
            spinWc a (spinLambda a ^ j * p.1) * spinWc a (spinLambda a ^ k * p.2)) :=
        mul_le_mul_of_nonneg_left hmono2 (Real.exp_pos _).le
    _ = Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          ((spinLambda a ^ j * spinLambda a ^ k)⁻¹ *
            (∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2)) := by rw [hscale]
    _ ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (1 * (∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv_le hI_nonneg)
          (Real.exp_pos _).le
    _ = Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) *
          (∫ p : ℝ × ℝ, |f p| * spinWc a p.1 * spinWc a p.2) := by rw [one_mul]

private def tailIndexEquiv (N : ℕ) :
    (ℕ × ℕ) ⊕ (Fin N × ℕ) ≃ {q : ℕ × ℕ // N ≤ q.1 + q.2} where
  toFun
    | Sum.inl (a, b) => ⟨(N + a, b), by omega⟩
    | Sum.inr (j, b) => ⟨(j.1, (N - j.1) + b), by omega⟩
  invFun q :=
    if h : N ≤ q.1.1 then
      Sum.inl (q.1.1 - N, q.1.2)
    else
      Sum.inr (⟨q.1.1, by omega⟩, q.1.2 - (N - q.1.1))
  left_inv x := by
    rcases x with ⟨a, b⟩ | ⟨⟨j, hj⟩, b⟩
    · simp
    · have hnot : ¬ N ≤ j := by omega
      simp [hnot]
  right_inv q := by
    rcases q with ⟨⟨x, y⟩, h⟩
    by_cases hx : N ≤ x
    · simp only [hx, ↓reduceDIte, Subtype.ext_iff, Prod.ext_iff]
      exact ⟨by omega, trivial⟩
    · simp only [hx, ↓reduceDIte, Subtype.ext_iff, Prod.ext_iff]
      exact ⟨trivial, by omega⟩

private lemma tail_geom_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Summable (fun q : {q : ℕ × ℕ // N ≤ q.1 + q.2} => ρ ^ (q.1.1 + q.1.2)) ∧
      (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2}, ρ ^ (q.1.1 + q.1.2)) ≤
        (1 - ρ) ^ (-2 : ℤ) * ((N : ℝ) + 1) * ρ ^ N := by
  let g : ℕ × ℕ → ℝ := fun q => ρ ^ (q.1 + q.2)
  have hs_geom : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρ0.le hρ1
  have hs_geom_norm : Summable (fun n : ℕ => ‖ρ ^ n‖) := by
    simpa [Real.norm_of_nonneg (pow_nonneg hρ0.le _)] using hs_geom
  have hs_g : Summable g := by
    have h := summable_mul_of_summable_norm hs_geom_norm hs_geom_norm
    refine h.congr fun q => ?_
    dsimp [g]; rw [pow_add]
  have hs_sub : Summable (fun q : {q : ℕ × ℕ // N ≤ q.1 + q.2} => ρ ^ (q.1.1 + q.1.2)) :=
    hs_g.subtype _
  refine ⟨hs_sub, ?_⟩
  let Ssub : Set (ℕ × ℕ) := {q | N ≤ q.1 + q.2}
  let S1 : Set (ℕ × ℕ) := {q | N ≤ q.1}
  let S2 : ℕ → Set (ℕ × ℕ) := fun j => {q | q.1 = j ∧ N - j ≤ q.2}
  have hS1_sum : Summable (S1.indicator g) := hs_g.indicator S1
  have hS2_sum : ∀ j : ℕ, Summable ((S2 j).indicator g) := fun j => hs_g.indicator (S2 j)
  have hFin_sum : Summable (fun q : ℕ × ℕ => ∑ j ∈ Finset.range N, (S2 j).indicator g q) := by
    classical
    exact summable_sum fun j _ => hS2_sum j
  have hpt : ∀ q : ℕ × ℕ,
      Ssub.indicator g q ≤ S1.indicator g q + ∑ j ∈ Finset.range N, (S2 j).indicator g q := by
    intro q
    have hnn1 : 0 ≤ S1.indicator g q :=
      Set.indicator_nonneg (fun _ _ => pow_nonneg hρ0.le _) q
    have hnn2 : ∀ j, 0 ≤ (S2 j).indicator g q := fun j =>
      Set.indicator_nonneg (fun _ _ => pow_nonneg hρ0.le _) q
    have hnnS2 : 0 ≤ ∑ j ∈ Finset.range N, (S2 j).indicator g q :=
      Finset.sum_nonneg fun j _ => hnn2 j
    by_cases hq : q ∈ Ssub
    · rw [Set.indicator_of_mem hq]
      by_cases hq1 : q ∈ S1
      · rw [Set.indicator_of_mem hq1]
        linarith
      · have hq1_lt : q.1 < N := Nat.lt_of_not_le hq1
        have hmem_S2 : q ∈ S2 q.1 := ⟨rfl, by dsimp [Ssub] at hq; omega⟩
        have hj_le : (S2 q.1).indicator g q ≤ ∑ j ∈ Finset.range N, (S2 j).indicator g q :=
          Finset.single_le_sum (fun j _ => hnn2 j) (Finset.mem_range.mpr hq1_lt)
        rw [Set.indicator_of_mem hmem_S2] at hj_le
        linarith
    · rw [Set.indicator_of_notMem hq]
      linarith
  have htsum_sub : (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2}, ρ ^ (q.1.1 + q.1.2)) =
      ∑' q : ℕ × ℕ, Ssub.indicator g q :=
    tsum_subtype Ssub g
  have htsum_fin : ∀ M : ℕ,
      (∑' q : ℕ × ℕ, ∑ j ∈ Finset.range M, (S2 j).indicator g q) =
        ∑ j ∈ Finset.range M, ∑' q : ℕ × ℕ, (S2 j).indicator g q := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
      have hk : Summable (fun q : ℕ × ℕ => ∑ j ∈ Finset.range k, (S2 j).indicator g q) := by
        classical
        exact summable_sum fun j _ => hS2_sum j
      simp_rw [Finset.sum_range_succ]
      rw [hk.tsum_add (hS2_sum k), ih]
  have htsum_le : (∑' q : ℕ × ℕ, Ssub.indicator g q) ≤
      (∑' q : ℕ × ℕ, S1.indicator g q) +
        ∑ j ∈ Finset.range N, ∑' q : ℕ × ℕ, (S2 j).indicator g q := by
    have h1 := (hs_g.indicator Ssub).tsum_le_tsum hpt (hS1_sum.add hFin_sum)
    rw [hS1_sum.tsum_add hFin_sum, htsum_fin N] at h1
    exact h1
  let e1 : ℕ × ℕ ≃ S1 :=
    { toFun := fun p => ⟨(N + p.1, p.2), by dsimp [S1]; omega⟩
      invFun := fun q => (q.1.1 - N, q.1.2)
      left_inv := fun ⟨a, b⟩ => by simp
      right_inv := fun ⟨⟨x, y⟩, h⟩ => by
        simp only [Subtype.ext_iff, Prod.ext_iff]
        dsimp [S1] at h
        exact ⟨by omega, trivial⟩ }
  have hS1_eval : (∑' q : ℕ × ℕ, S1.indicator g q) = ρ ^ N * (1 - ρ) ^ (-2 : ℤ) := by
    rw [← tsum_subtype S1 g, ← Equiv.tsum_eq e1]
    have heq : (fun p : ℕ × ℕ => g (e1 p).1) = fun p : ℕ × ℕ => ρ ^ N * (ρ ^ p.1 * ρ ^ p.2) := by
      ext p; dsimp [g, e1]; rw [add_assoc, pow_add, pow_add]
    change ∑' p : ℕ × ℕ, g (e1 p).1 = _
    rw [heq, tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hs_geom_norm hs_geom_norm,
      tsum_geometric_of_lt_one hρ0.le hρ1]
    have h1ρ : (1 - ρ)⁻¹ * (1 - ρ)⁻¹ = (1 - ρ) ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_two, mul_inv]
    rw [h1ρ]
  have hS2_eval : ∀ j ∈ Finset.range N,
      (∑' q : ℕ × ℕ, (S2 j).indicator g q) = ρ ^ N * (1 - ρ)⁻¹ := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    let e2 : ℕ ≃ S2 j :=
      { toFun := fun b => ⟨(j, (N - j) + b), ⟨rfl, by omega⟩⟩
        invFun := fun q => q.1.2 - (N - j)
        left_inv := fun b => by simp
        right_inv := fun ⟨⟨x, y⟩, h⟩ => by
          simp only [Subtype.ext_iff, Prod.ext_iff]
          dsimp [S2] at h
          exact ⟨h.1.symm, by omega⟩ }
    rw [← tsum_subtype (S2 j) g, ← Equiv.tsum_eq e2]
    have heq : (fun b : ℕ => g (e2 b).1) = fun b : ℕ => ρ ^ N * ρ ^ b := by
      ext b
      dsimp [g, e2]
      rw [show j + (N - j + b) = N + b by omega, pow_add]
    change ∑' b : ℕ, g (e2 b).1 = _
    rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1]
  have hfin_eval :
      (∑ j ∈ Finset.range N, ∑' q : ℕ × ℕ, (S2 j).indicator g q) =
        (N : ℝ) * ρ ^ N * (1 - ρ)⁻¹ := by
    rw [Finset.sum_congr rfl hS2_eval, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [htsum_sub]
  refine htsum_le.trans ?_
  rw [hS1_eval, hfin_eval]
  have h1ρ_pos : 0 < 1 - ρ := sub_pos.mpr hρ1
  have h1ρ_le : (1 - ρ)⁻¹ ≤ (1 - ρ) ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_two, mul_inv]
    have hone : 1 ≤ (1 - ρ)⁻¹ := one_le_inv₀ h1ρ_pos |>.mpr (by linarith)
    nlinarith
  have hN_nn : 0 ≤ (N : ℝ) * ρ ^ N := mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hρ0.le N)
  nlinarith

end Helpers

/-- Lemma `scal:C3` (`spinning_calibration.tex`): double-difference inversion and tail decay
for all `c ≥ 40` and `Φ ∈ \overline{\mathcal A}_{\rm spin}`. -/
theorem scalC3 : ScalC3 := by
  intro r hr
  have hpi : 0 < π := Real.pi_pos
  have hρ_pos : 0 < Real.exp (-4 * π * r) := Real.exp_pos _
  have hρ_lt : Real.exp (-4 * π * r) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1ρ_pos : 0 < 1 - Real.exp (-4 * π * r) := sub_pos.mpr hρ_lt
  let C_r : ℝ := (1 - Real.exp (-4 * π * r)) ^ (-2 : ℤ)
  have hCr_pos : 0 < C_r := zpow_pos h1ρ_pos _
  refine ⟨C_r, hCr_pos, ?_⟩
  intro c hc a Φ hΦ
  have ha : 2 < a := by dsimp [a]; linarith
  have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))
  have hD_cont : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) =
        fun p => spinG a Φ (spinLambda a * p.1) (spinLambda a * p.2) -
          spinG a Φ p.1 (spinLambda a * p.2) -
          spinG a Φ (spinLambda a * p.1) p.2 +
          spinG a Φ p.1 p.2 := by
      ext p; exact spinDeltaA_eq_expand ha Φ p.1 p.2
    rw [heq]
    exact (((hG_cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).sub
      (hG_cont.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).sub
      (hG_cont.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).add hG_cont
  have hG_int : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume :=
    integrable_spinG_wc (by linarith) hΦ
  have hD_int : Integrable (fun p : ℝ × ℝ =>
      |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) volume :=
    (integrable_and_integral_spinDeltaA_wc ha hΦ).1
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | r ≤ p.1 ∧ r ≤ p.2}
  have hS_eq : S = Set.Ici r ×ˢ Set.Ici r := rfl
  have hS_meas : MeasurableSet S := by rw [hS_eq]; exact measurableSet_Ici.prod measurableSet_Ici
  let ρ : ℝ := Real.exp (-4 * π * r)
  have hexp_pow : ∀ m : ℕ, Real.exp (-4 * π * r * (m : ℝ)) = ρ ^ m := fun m => by
    dsimp [ρ]
    rw [show -4 * π * r * (m : ℝ) = (m : ℝ) * (-4 * π * r) by ring, Real.exp_nat_mul]
  let M : ℝ := ∫ p : ℝ × ℝ, |spinDeltaA a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
  have hM_nn : 0 ≤ M := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _)
  let M₂ : ℝ := ∫ p : ℝ × ℝ, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
  have hM₂_nn : 0 ≤ M₂ := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _)
  refine ⟨?_, ?_⟩
  · have hbound_J : ∀ J : ℕ,
        (∫ p in S, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) ≤
          C_r * M + 3 * M₂ * ρ ^ J := by
      intro J
      let d_fn : ℕ → ℕ → ℝ × ℝ → ℝ := fun j k p =>
        |spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| *
          spinWc a p.1 * spinWc a p.2
      let S_sum : ℝ × ℝ → ℝ := fun p => ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, d_fn j k p
      let r1 : ℝ × ℝ → ℝ := fun p =>
        |spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2)| *
          spinWc a p.1 * spinWc a p.2
      let r2 : ℝ × ℝ → ℝ := fun p =>
        |spinG a Φ p.1 (spinLambda a ^ J * p.2)| * spinWc a p.1 * spinWc a p.2
      let r3 : ℝ × ℝ → ℝ := fun p =>
        |spinG a Φ (spinLambda a ^ J * p.1) p.2| * spinWc a p.1 * spinWc a p.2
      have h_d : ∀ j k : ℕ, Integrable (d_fn j k) volume ∧
          (∫ p in S, d_fn j k p) ≤ ρ ^ (j + k) * M := by
        intro j k
        have h := integrable_dilate_and_bound ha hr hD_cont hD_int j k
        refine ⟨h.1, ?_⟩
        calc ∫ p in S, d_fn j k p
            ≤ Real.exp (-4 * π * r * ((j + k : ℕ) : ℝ)) * M := h.2
          _ = ρ ^ (j + k) * M := by rw [hexp_pow (j + k)]
      have hr1 := integrable_dilate_and_bound ha hr hG_cont hG_int J J
      have hr2 := integrable_dilate_and_bound ha hr hG_cont hG_int 0 J
      have hr3 := integrable_dilate_and_bound ha hr hG_cont hG_int J 0
      have hpt : ∀ p : ℝ × ℝ,
          |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
            S_sum p + r1 p + r2 p + r3 p := by
        intro p
        have htel := spinG_telescope ha Φ p.1 p.2 J
        have htri : |spinG a Φ p.1 p.2| ≤
            (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              |spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)|) +
              |spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2)| +
              |spinG a Φ p.1 (spinLambda a ^ J * p.2)| +
              |spinG a Φ (spinLambda a ^ J * p.1) p.2| := by
          rw [htel]
          have ha1 := abs_add_le
            ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)) -
              spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2) +
              spinG a Φ p.1 (spinLambda a ^ J * p.2))
            (spinG a Φ (spinLambda a ^ J * p.1) p.2)
          have ha2 := abs_add_le
            ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)) -
              spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2))
            (spinG a Φ p.1 (spinLambda a ^ J * p.2))
          have ha3 := abs_sub
            (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2))
            (spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2))
          have hsum_abs :
              |∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
                spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| ≤
              ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
                |spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
          linarith
        have hw : 0 ≤ spinWc a p.1 * spinWc a p.2 :=
          mul_nonneg (spinWc_nonneg ha.le p.1) (spinWc_nonneg ha.le p.2)
        have hmul := mul_le_mul_of_nonneg_right htri hw
        have hsum_mul :
            (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
              |spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)|) *
                (spinWc a p.1 * spinWc a p.2) = S_sum p := by
          dsimp [S_sum]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp [d_fn]; ring
        have hr1_eq : |spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2)| *
            (spinWc a p.1 * spinWc a p.2) = r1 p := by dsimp [r1]; ring
        have hr2_eq : |spinG a Φ p.1 (spinLambda a ^ J * p.2)| *
            (spinWc a p.1 * spinWc a p.2) = r2 p := by dsimp [r2]; ring
        have hr3_eq : |spinG a Φ (spinLambda a ^ J * p.1) p.2| *
            (spinWc a p.1 * spinWc a p.2) = r3 p := by dsimp [r3]; ring
        calc |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2
            = |spinG a Φ p.1 p.2| * (spinWc a p.1 * spinWc a p.2) := by ring
          _ ≤ ((∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
                |spinDeltaA a Φ (spinLambda a ^ j * p.1) (spinLambda a ^ k * p.2)|) +
                |spinG a Φ (spinLambda a ^ J * p.1) (spinLambda a ^ J * p.2)| +
                |spinG a Φ p.1 (spinLambda a ^ J * p.2)| +
                |spinG a Φ (spinLambda a ^ J * p.1) p.2|) * (spinWc a p.1 * spinWc a p.2) := hmul
          _ = S_sum p + r1 p + r2 p + r3 p := by
              rw [add_mul, add_mul, add_mul, hsum_mul, hr1_eq, hr2_eq, hr3_eq]
      have hsum_int : IntegrableOn S_sum S := by
        have h1 : IntegrableOn (fun p => ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, d_fn j k p) S :=
          integrable_finsetSum _ fun j _ =>
            integrable_finsetSum _ fun k _ => (h_d j k).1.integrableOn
        exact h1
      have hr1' : IntegrableOn r1 S := hr1.1.integrableOn
      have hr2' : IntegrableOn r2 S := by
        simpa [r2, pow_zero, one_mul] using hr2.1.integrableOn
      have hr3' : IntegrableOn r3 S := by
        simpa [r3, pow_zero, one_mul] using hr3.1.integrableOn
      have h_rhs_int : IntegrableOn (fun p => S_sum p + r1 p + r2 p + r3 p) S :=
        ((hsum_int.add hr1').add hr2').add hr3'
      have hmono := setIntegral_mono_on hG_int.integrableOn h_rhs_int hS_meas fun p _ => hpt p
      have hsplit :
          (∫ p in S, S_sum p + r1 p + r2 p + r3 p) =
            (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∫ p in S, d_fn j k p) +
              (∫ p in S, r1 p) + (∫ p in S, r2 p) + (∫ p in S, r3 p) := by
        have ha3 := integral_add ((hsum_int.add hr1').add hr2') hr3'
        have ha2 := integral_add (hsum_int.add hr1') hr2'
        have ha1 := integral_add hsum_int hr1'
        simp only [Pi.add_apply] at ha3 ha2 ha1
        have hS_eval : (∫ p in S, S_sum p) =
            ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∫ p in S, d_fn j k p := by
          change (∫ p in S, ∑ j ∈ Finset.range J, (fun q => ∑ k ∈ Finset.range J, d_fn j k q) p) = _
          rw [integral_finsetSum _ fun j _ =>
            integrable_finsetSum _ fun k _ => (h_d j k).1.integrableOn]
          refine Finset.sum_congr rfl fun j _ =>
            integral_finsetSum _ fun k _ => (h_d j k).1.integrableOn
        rw [ha3, ha2, ha1, hS_eval]
      have hgeom_part :
          (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∫ p in S, d_fn j k p) ≤ C_r * M := by
        have h1 : (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∫ p in S, d_fn j k p) ≤
            ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ρ ^ (j + k) * M :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => (h_d j k).2
        have h2 : (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ρ ^ (j + k) * M) =
            (∑ j ∈ Finset.range J, ρ ^ j) * (∑ k ∈ Finset.range J, ρ ^ k) * M := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_add]
        have hs_geom := summable_geometric_of_lt_one hρ_pos.le hρ_lt
        have hgeom_sum : ∑ j ∈ Finset.range J, ρ ^ j ≤ (1 - ρ)⁻¹ :=
          (hs_geom.sum_le_tsum (Finset.range J) (fun _ _ => pow_nonneg hρ_pos.le _)).trans_eq
            (tsum_geometric_of_lt_one hρ_pos.le hρ_lt)
        have hsum_nn : 0 ≤ ∑ j ∈ Finset.range J, ρ ^ j :=
          Finset.sum_nonneg fun j _ => pow_nonneg hρ_pos.le j
        have hprod_le : (∑ j ∈ Finset.range J, ρ ^ j) * (∑ k ∈ Finset.range J, ρ ^ k) ≤ C_r := by
          have hCr_eq : C_r = (1 - ρ)⁻¹ * (1 - ρ)⁻¹ := by
            dsimp [C_r, ρ]
            rw [zpow_neg, zpow_two, mul_inv]
          rw [hCr_eq]
          exact mul_le_mul hgeom_sum hgeom_sum hsum_nn (inv_nonneg.mpr h1ρ_pos.le)
        exact h1.trans (h2 ▸ mul_le_mul_of_nonneg_right hprod_le hM_nn)
      have hr1_bd : (∫ p in S, r1 p) ≤ ρ ^ J * M₂ := by
        have h := hr1.2
        rw [hexp_pow (J + J)] at h
        have hle : ρ ^ (J + J) ≤ ρ ^ J := pow_le_pow_of_le_one hρ_pos.le hρ_lt.le (by omega)
        exact h.trans (mul_le_mul_of_nonneg_right hle hM₂_nn)
      have hr2_bd : (∫ p in S, r2 p) ≤ ρ ^ J * M₂ := by
        have h := hr2.2
        rw [hexp_pow (0 + J), zero_add] at h
        simpa [r2, S, M₂, pow_zero, one_mul] using h
      have hr3_bd : (∫ p in S, r3 p) ≤ ρ ^ J * M₂ := by
        have h := hr3.2
        rw [hexp_pow (J + 0), add_zero] at h
        simpa [r3, S, M₂, pow_zero, one_mul] using h
      linarith [hmono, hsplit, hgeom_part, hr1_bd, hr2_bd, hr3_bd]
    have htend : Tendsto (fun J : ℕ => C_r * M + 3 * M₂ * ρ ^ J) atTop (𝓝 (C_r * M)) := by
      have h0 : Tendsto (fun J : ℕ => ρ ^ J) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hρ_pos.le hρ_lt
      simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul h0))
    exact ge_of_tendsto htend (Eventually.of_forall hbound_J)
  · intro N
    let f : {q : ℕ × ℕ // N ≤ q.1 + q.2} → ℝ := fun q =>
      ∫ p in S, |spinDeltaA a Φ (spinLambda a ^ q.1.1 * p.1) (spinLambda a ^ q.1.2 * p.2)| *
        spinWc a p.1 * spinWc a p.2
    let g : {q : ℕ × ℕ // N ≤ q.1 + q.2} → ℝ := fun q => ρ ^ (q.1.1 + q.1.2) * M
    have hf_nn : ∀ q, 0 ≤ f q := fun q =>
      setIntegral_nonneg hS_meas fun p _ =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha.le _)) (spinWc_nonneg ha.le _)
    have hfg : ∀ q, f q ≤ g q := by
      intro q
      have h := (integrable_dilate_and_bound ha hr hD_cont hD_int q.1.1 q.1.2).2
      rw [hexp_pow (q.1.1 + q.1.2)] at h
      exact h
    obtain ⟨hg_sum, hg_le⟩ := tail_geom_bound hρ_pos hρ_lt N
    have hg_mul_sum : Summable g := hg_sum.mul_right M
    have hf_sum : Summable f := Summable.of_nonneg_of_le hf_nn hfg hg_mul_sum
    have htsum_le : (∑' q, f q) ≤ ∑' q, g q := hf_sum.tsum_le_tsum hfg hg_mul_sum
    have htsum_g : (∑' q, g q) = (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2}, ρ ^ (q.1.1 + q.1.2)) * M :=
      tsum_mul_right
    calc (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2},
            ∫ p in S, |spinDeltaA a Φ (spinLambda a ^ q.1.1 * p.1) (spinLambda a ^ q.1.2 * p.2)| *
              spinWc a p.1 * spinWc a p.2)
        ≤ (∑' q : {q : ℕ × ℕ // N ≤ q.1 + q.2}, ρ ^ (q.1.1 + q.1.2)) * M := by
          simpa [f, htsum_g] using htsum_le
      _ ≤ (C_r * ((N : ℝ) + 1) * ρ ^ N) * M :=
          mul_le_mul_of_nonneg_right hg_le hM_nn
      _ = C_r * ((N : ℝ) + 1) * Real.exp (-4 * π * r * (N : ℝ)) * M := by
          rw [hexp_pow N]

/-- info: 'FormalResearch.ModularBootstrap.Spin.scalC3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.scalC3

end FormalResearch.ModularBootstrap.Spin

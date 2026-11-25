module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Real-axis Twisted Airy Laplace Asymptotic (`ce_rate.tex` Lemma P.1(1))

Source: `CFT/sign_uncertainty/paper/ce_rate.tex` (PR 240), Lemma `P.1(1)` (`cel:L2a`, `(cel:3.2)`,
`(cel:3.6)`).

## Main definitions
* `ceK`, `ceCs`, `airyTwistedLaplace`: the twisted Airy Laplace transform `X̃(i x̃)`.

## Main results
* `completed_cube_id`: exact completed-cube identity `(cel:3.6)`.
* `airyTwistedLaplace_tendsto`, `airyTwistedLaplace_rescaled_tendsto`: general real-axis Laplace
  asymptotic `(cel:3.2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### Part 1: Real-axis Laplace asymptotic (`ce_rate.tex` Lemma P.1, `cel:L2a`) -/

/-- Scaling constant `k = 2^{2/3}`. -/
noncomputable def ceK : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ)

/-- Scaling constant `c_s = (π² / 3)^{1/3}`. -/
noncomputable def ceCs : ℝ := (π ^ 2 / 3) ^ (1 / 3 : ℝ)

lemma ceK_pos : 0 < ceK := by unfold ceK; positivity

lemma ceCs_pos : 0 < ceCs := by unfold ceCs; positivity

/-- Twisted Airy Laplace transform `X̃(i x̃) = k e^{-x̃³ / 12} ∫_ℝ X(u) e^{x̃ u} du`. -/
noncomputable def airyTwistedLaplace (X : ℝ → ℝ) (xtilde : ℝ) : ℝ :=
  ceK * Real.exp (-(xtilde ^ 3) / 12) * ∫ u : ℝ, X u * Real.exp (xtilde * u)

/-- Exact completed-cube identity `(cel:3.6)`. -/
theorem completed_cube_id (xtilde s : ℝ) :
    -(4 / 3 : ℝ) * s ^ 3 + xtilde * s ^ 2 - xtilde ^ 3 / 12 =
      -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) := by
  ring

private lemma cube_sub_quad_le {xtilde s : ℝ} (hx : 0 ≤ xtilde) (hs : 0 ≤ s) :
    -(4 / 3 : ℝ) * s ^ 3 + xtilde * s ^ 2 ≤ -(s ^ 2) + (xtilde + 1) ^ 3 := by
  rcases le_or_gt s (xtilde + 1) with h | h
  · have h1 : (xtilde + 1) * s ^ 2 ≤ (xtilde + 1) * (xtilde + 1) ^ 2 := by gcongr
    have h2 : (xtilde + 1) * (xtilde + 1) ^ 2 = (xtilde + 1) ^ 3 := by ring
    have h3 : 0 ≤ (4 / 3 : ℝ) * s ^ 3 := by positivity
    linarith
  · have h1 : (xtilde + 1) * s ^ 2 ≤ s * s ^ 2 := by gcongr
    have h2 : s * s ^ 2 = s ^ 3 := by ring
    have h3 : 0 ≤ (xtilde + 1) ^ 3 := by positivity
    have h4 : 0 ≤ (1 / 3 : ℝ) * s ^ 3 := by positivity
    linarith

private lemma tail_coef_bound {R_plus : ℝ → ℝ} (β_plus : ℝ) {C_tl s : ℝ}
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ)) (hs1 : 1 ≤ s) :
    |β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s| ≤ |β_plus| / (2 * π) + C_tl := by
  have hs_pos : 0 < s := by linarith
  have hs2 : s ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hs4 : s ^ (-4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have h1 : |β_plus / (2 * π) * s ^ (-2 : ℝ)| ≤ |β_plus| / (2 * π) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      abs_of_nonneg (Real.rpow_nonneg hs_pos.le _)]
    exact mul_le_of_le_one_right (by positivity) hs2
  exact (abs_add_le _ _).trans (add_le_add h1 ((hR_plus s hs1).trans (mul_le_of_le_one_right hC_tl hs4)))

private lemma tail_integrableOn_Ioi {X R_plus : ℝ → ℝ} {β_plus C_tl xtilde : ℝ}
    (hX_meas : AEStronglyMeasurable X volume)
    (hX_tail : ∀ s ≥ 1, 2 * s * X (s ^ 2) =
      (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) * Real.exp (-(4 / 3 : ℝ) * s ^ 3))
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ))
    (hx : 0 ≤ xtilde) :
    IntegrableOn (fun u => X u * Real.exp (xtilde * u)) (Ioi 1) := by
  set M : ℝ := (|β_plus| / (2 * π) + C_tl) / 2 * Real.exp ((xtilde + 1) ^ 3) with hM
  refine ((integrableOn_exp_neg_Ioi 1).const_mul M).mono' (hX_meas.restrict.mul (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : 0 ≤ u := by linarith
  set s := √u
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hu1.le
  have hs_pos : 0 < s := by linarith
  have hsq : s ^ 2 = u := Real.sq_sqrt hu0
  have htail := hX_tail s hs1
  rw [hsq] at htail
  have hX_eq : X u = (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
      Real.exp (-(4 / 3 : ℝ) * s ^ 3) / (2 * s) := by rw [← htail]; field_simp
  have hcoef := tail_coef_bound β_plus hC_tl hR_plus hs1
  have hexp := cube_sub_quad_le hx hs_pos.le
  rw [hsq] at hexp
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (xtilde * u)), hX_eq, abs_div,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith : 0 < 2 * s)]
  calc |β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s| *
        Real.exp (-(4 / 3 : ℝ) * s ^ 3) / (2 * s) * Real.exp (xtilde * u)
      ≤ (|β_plus| / (2 * π) + C_tl) * Real.exp (-(4 / 3 : ℝ) * s ^ 3) / 2 * Real.exp (xtilde * u) := by
        gcongr; linarith
    _ = ((|β_plus| / (2 * π) + C_tl) / 2) * Real.exp (-(4 / 3 : ℝ) * s ^ 3 + xtilde * u) := by
        rw [Real.exp_add]; ring
    _ ≤ ((|β_plus| / (2 * π) + C_tl) / 2) * Real.exp (-u + (xtilde + 1) ^ 3) := by gcongr
    _ = M * Real.exp (-u) := by rw [hM, Real.exp_add]; ring

lemma tail_integrable {X R_plus : ℝ → ℝ} {β_plus C_tl xtilde : ℝ}
    (hX_int : Integrable X)
    (hX_tail : ∀ s ≥ 1, 2 * s * X (s ^ 2) =
      (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) * Real.exp (-(4 / 3 : ℝ) * s ^ 3))
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ))
    (hx : 0 ≤ xtilde) :
    Integrable (fun u => X u * Real.exp (xtilde * u)) := by
  have hIoi := tail_integrableOn_Ioi hX_int.aestronglyMeasurable hX_tail hC_tl hR_plus hx
  have hIic : IntegrableOn (fun u => X u * Real.exp (xtilde * u)) (Iic 1) := by
    refine (hX_int.integrableOn.norm.const_mul (Real.exp xtilde)).mono'
      (hX_int.aestronglyMeasurable.restrict.mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (xtilde * u))]
    calc |X u| * Real.exp (xtilde * u) ≤ |X u| * Real.exp (xtilde * 1) := by gcongr; exact hu
      _ = Real.exp xtilde * ‖X u‖ := by rw [mul_one, mul_comm, Real.norm_eq_abs]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (1 : ℝ)), integrableOn_union]
  exact ⟨hIic, hIoi⟩

private lemma tendsto_rpow_mul_exp_neg_cube {a : ℝ} (ha : 0 < a) (p : ℝ) :
    Filter.Tendsto (fun x : ℝ => x ^ p * Real.exp (-a * x ^ 3)) Filter.atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx; positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (le_self_pow₀ hx (by norm_num))
        (neg_nonpos.mpr ha.le)))
      (Real.rpow_nonneg (by linarith) _)

lemma sq_image_Ioi_one : (fun s : ℝ => s ^ 2) '' Ioi 1 = Ioi 1 := by
  ext u
  simp only [mem_image, mem_Ioi]
  exact ⟨fun ⟨s, hs, hsq⟩ => by rw [← hsq]; nlinarith,
    fun hu => ⟨√u, Real.lt_sqrt_of_sq_lt (by linarith), Real.sq_sqrt (by linarith)⟩⟩

lemma sq_injOn_Ioi_one : InjOn (fun s : ℝ => s ^ 2) (Ioi 1) := fun _ h1 _ h2 h =>
  (sq_eq_sq₀ (zero_lt_one.trans h1).le (zero_lt_one.trans h2).le).mp h

private lemma main_var_image (xtilde : ℝ) (hx : 8 ≤ xtilde) :
    (fun t : ℝ => xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t) ''
      Ioo (-(xtilde ^ (3 / 2 : ℝ) / 4)) (xtilde ^ (3 / 2 : ℝ) / 4) =
      Ioo (xtilde / 4) (3 * xtilde / 4) := by
  have hx0 : 0 < xtilde := by linarith
  have hpow : xtilde ^ (-(1 / 2 : ℝ)) * xtilde ^ (3 / 2 : ℝ) = xtilde := by
    rw [← Real.rpow_add hx0]; norm_num
  have hmul : xtilde ^ (1 / 2 : ℝ) * xtilde = xtilde ^ (3 / 2 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one xtilde]
    rw [← Real.rpow_add hx0]; norm_num
  have hinv : xtilde ^ (-(1 / 2 : ℝ)) * xtilde ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  have hpos : 0 < xtilde ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hp : 0 < xtilde ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  ext s
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have ha : xtilde ^ (-(1 / 2 : ℝ)) * (-(xtilde ^ (3 / 2 : ℝ) / 4)) = -(xtilde / 4) := by
      rw [mul_neg, mul_div_assoc', hpow]
    have hb : xtilde ^ (-(1 / 2 : ℝ)) * (xtilde ^ (3 / 2 : ℝ) / 4) = xtilde / 4 := by
      rw [mul_div_assoc', hpow]
    constructor <;> nlinarith
  · intro ⟨hs1, hs2⟩
    refine ⟨xtilde ^ (1 / 2 : ℝ) * (s - xtilde / 2), ⟨by nlinarith, by nlinarith⟩, ?_⟩
    calc xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * (xtilde ^ (1 / 2 : ℝ) * (s - xtilde / 2))
        = xtilde / 2 + (xtilde ^ (-(1 / 2 : ℝ)) * xtilde ^ (1 / 2 : ℝ)) * (s - xtilde / 2) := by ring
      _ = s := by rw [hinv]; ring

private lemma laplace_left_tendsto {X : ℝ → ℝ} (hX_int : Integrable X) :
    Filter.Tendsto (fun xtilde => xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) *
      ∫ u in Iic 1, X u * Real.exp (xtilde * u)) Filter.atTop (𝓝 0) := by
  have h_bd : ∀ᶠ xtilde in atTop,
      ‖xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) *
        ∫ u in Iic 1, X u * Real.exp (xtilde * u)‖ ≤
        ceK * (∫ u, |X u|) * (xtilde ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * xtilde ^ 3)) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
    have hx0 : 0 ≤ xtilde := by linarith
    have hint_iic : IntegrableOn (fun u => X u * Real.exp (xtilde * u)) (Iic 1) := by
      refine (hX_int.integrableOn.norm.const_mul (Real.exp xtilde)).mono'
        (hX_int.aestronglyMeasurable.restrict.mul (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |X u| * Real.exp (xtilde * u) ≤ |X u| * Real.exp (xtilde * 1) := by gcongr; exact hu
        _ = Real.exp xtilde * ‖X u‖ := by rw [mul_one, mul_comm, Real.norm_eq_abs]
    have h_int_bd : ‖∫ u in Iic 1, X u * Real.exp (xtilde * u)‖ ≤ (∫ u, |X u|) * Real.exp xtilde := by
      calc ‖∫ u in Iic 1, X u * Real.exp (xtilde * u)‖
          ≤ ∫ u in Iic 1, ‖X u * Real.exp (xtilde * u)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ u in Iic 1, |X u| * Real.exp xtilde := by
            refine setIntegral_mono_on hint_iic.norm (hX_int.integrableOn.abs.mul_const _)
              measurableSet_Iic fun u hu => ?_
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            gcongr; exact le_trans (mul_le_mul_of_nonneg_left hu hx0) (by rw [mul_one])
        _ ≤ ∫ u : ℝ, |X u| * Real.exp xtilde :=
            setIntegral_le_integral (hX_int.abs.mul_const _) (ae_of_all _ fun u => by positivity)
        _ = (∫ u, |X u|) * Real.exp xtilde := integral_mul_const _ _
    have hexp : Real.exp (-(xtilde ^ 3) / 12) * Real.exp xtilde ≤
        Real.exp (-(1 / 24 : ℝ) * xtilde ^ 3) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hx2 : 64 * xtilde ≤ xtilde ^ 3 := by
        calc 64 * xtilde ≤ xtilde ^ 2 * xtilde := by nlinarith
          _ = xtilde ^ 3 := by ring
      linarith
    have hpre_nn : 0 ≤ xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0 _) ceK_pos.le) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hx0 _), abs_of_pos ceK_pos, abs_of_pos (Real.exp_pos _)]
    calc xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) *
          |∫ u in Iic 1, X u * Real.exp (xtilde * u)|
        ≤ xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) *
            ((∫ u, |X u|) * Real.exp xtilde) :=
          mul_le_mul_of_nonneg_left h_int_bd hpre_nn
      _ = ceK * (∫ u, |X u|) *
            (xtilde ^ (5 / 2 : ℝ) * (Real.exp (-(xtilde ^ 3) / 12) * Real.exp xtilde)) := by ring
      _ ≤ ceK * (∫ u, |X u|) *
            (xtilde ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * xtilde ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx0 _))
            (mul_nonneg ceK_pos.le (integral_nonneg fun _ => abs_nonneg _))
  have ht0 := (tendsto_rpow_mul_exp_neg_cube (by norm_num : (0 : ℝ) < 1 / 24) (5 / 2)).const_mul
    (ceK * ∫ u, |X u|)
  rw [mul_zero] at ht0
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
      (Eventually.of_forall fun _ => norm_nonneg _) h_bd)

private lemma laplace_tail1_tendsto {R_plus : ℝ → ℝ} {β_plus C_tl : ℝ}
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ))
    (hg_int_Ioi : ∀ xtilde ≥ 0, IntegrableOn (fun s => (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
      Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))) (Ioi 1)) :
    Filter.Tendsto (fun xtilde => xtilde ^ (5 / 2 : ℝ) * ceK *
      ∫ s in Ioc 1 (xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
        Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4)))
      Filter.atTop (𝓝 0) := by
  let M : ℝ := |β_plus| / (2 * π) + C_tl
  have hM0 : 0 ≤ M := by positivity
  have h_bd : ∀ᶠ xtilde in atTop,
      ‖xtilde ^ (5 / 2 : ℝ) * ceK *
        ∫ s in Ioc 1 (xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
          Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ ≤
        ceK * M * (xtilde ^ (7 / 2 : ℝ) * Real.exp (-(1 / 48 : ℝ) * xtilde ^ 3)) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
    have hx0 : 0 ≤ xtilde := by linarith
    let c := M * Real.exp (-(1 / 48 : ℝ) * xtilde ^ 3)
    have hc0 : 0 ≤ c := mul_nonneg hM0 (Real.exp_pos _).le
    have h_int_bd : ‖∫ s in Ioc 1 (xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
        Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ ≤ c * (xtilde / 4) := by
      calc ‖∫ s in Ioc 1 (xtilde / 4), _‖
          ≤ ∫ s in Ioc 1 (xtilde / 4), ‖(β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
              Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioc 1 (xtilde / 4), c := by
            refine setIntegral_mono_on ((hg_int_Ioi xtilde hx0).mono_set Ioc_subset_Ioi_self).norm
              (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun s hs => ?_
            have hs1 : 1 ≤ s := hs.1.le
            have hs_le : s ≤ xtilde / 4 := hs.2
            have h_exp : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) ≤
                -(1 / 48 : ℝ) * xtilde ^ 3 := by
              have hsq : (xtilde / 4) ^ 2 ≤ (s - xtilde / 2) ^ 2 := by
                have hle : xtilde / 4 ≤ xtilde / 2 - s := by linarith
                nlinarith
              have hlin : xtilde / 4 ≤ s + xtilde / 4 := by linarith
              nlinarith
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul (tail_coef_bound β_plus hC_tl hR_plus hs1)
              (Real.exp_le_exp.mpr h_exp) (Real.exp_pos _).le hM0
        _ = volume.real (Ioc 1 (xtilde / 4)) * c := by rw [setIntegral_const, smul_eq_mul]
        _ ≤ (xtilde / 4) * c := by
            rw [Real.volume_real_Ioc_of_le (by linarith)]
            exact mul_le_mul_of_nonneg_right (by linarith) hc0
        _ = c * (xtilde / 4) := mul_comm _ _
    have hpre_nn : 0 ≤ xtilde ^ (5 / 2 : ℝ) * ceK := mul_nonneg (Real.rpow_nonneg hx0 _) ceK_pos.le
    have hx_pow : xtilde ^ (5 / 2 : ℝ) * xtilde = xtilde ^ (7 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one xtilde]
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0 _), abs_of_pos ceK_pos]
    calc xtilde ^ (5 / 2 : ℝ) * ceK * |∫ s in Ioc 1 (xtilde / 4), _|
        ≤ xtilde ^ (5 / 2 : ℝ) * ceK * (c * (xtilde / 4)) := mul_le_mul_of_nonneg_left h_int_bd hpre_nn
      _ ≤ xtilde ^ (5 / 2 : ℝ) * ceK * (c * xtilde) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hc0) hpre_nn
      _ = ceK * M * (xtilde ^ (7 / 2 : ℝ) * Real.exp (-(1 / 48 : ℝ) * xtilde ^ 3)) := by
          dsimp [c]; rw [← hx_pow]; ring
  have ht0 := (tendsto_rpow_mul_exp_neg_cube (by norm_num : (0 : ℝ) < 1 / 48) (7 / 2)).const_mul (ceK * M)
  rw [mul_zero] at ht0
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
      (Eventually.of_forall fun _ => norm_nonneg _) h_bd)

private lemma laplace_tail2_tendsto {R_plus : ℝ → ℝ} {β_plus C_tl : ℝ}
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ))
    (hg_int_Ioi : ∀ xtilde ≥ 0, IntegrableOn (fun s => (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
      Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))) (Ioi 1)) :
    Filter.Tendsto (fun xtilde => xtilde ^ (5 / 2 : ℝ) * ceK *
      ∫ s in Ici (3 * xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
        Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4)))
      Filter.atTop (𝓝 0) := by
  let M : ℝ := |β_plus| / (2 * π) + C_tl
  have hM0 : 0 ≤ M := by positivity
  have h_bd : ∀ᶠ xtilde in atTop,
      ‖xtilde ^ (5 / 2 : ℝ) * ceK *
        ∫ s in Ici (3 * xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
          Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ ≤
        ceK * M * 14 * (xtilde ^ (5 / 2 : ℝ) * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3)) := by
    filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
    have hx0 : 0 ≤ xtilde := by linarith
    have hint_g := (hg_int_Ioi xtilde hx0).mono_set
      (Ici_subset_Ioi.mpr (by linarith : 1 < 3 * xtilde / 4))
    have hint_exp0 : IntegrableOn (fun s : ℝ => M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) *
        Real.exp (-(1 / 14 : ℝ) * s)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -(1 / 14 : ℝ)) (by norm_num) 0).const_mul _
    have hint_exp := hint_exp0.mono_set
      (Ici_subset_Ioi.mpr (by linarith : 0 < 3 * xtilde / 4))
    have h_le_exp : ∀ s ∈ Ici (3 * xtilde / 4),
        ‖(β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
          Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ ≤
          M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) * Real.exp (-(1 / 14 : ℝ) * s) := by
      intro s hs
      have hs_ge : 3 * xtilde / 4 ≤ s := mem_Ici.mp hs
      have hs1 : 1 ≤ s := by linarith
      have h_exp1 : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) ≤
          -(1 / 48 : ℝ) * xtilde ^ 3 := by
        have hsq : (xtilde / 4) ^ 2 ≤ (s - xtilde / 2) ^ 2 := by nlinarith
        have hlin : xtilde / 4 ≤ s + xtilde / 4 := by linarith
        nlinarith
      have h_exp2 : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) ≤ -(1 / 7 : ℝ) * s := by
        have h1 : s / 3 ≤ s - xtilde / 2 := by linarith
        have h2 : s ≤ s + xtilde / 4 := by linarith
        have h3 : (1 / 7 : ℝ) * s ≤ (4 / 3 : ℝ) * (s / 3) ^ 2 * s := by
          have : 1 ≤ s ^ 2 := by nlinarith
          nlinarith
        have h4 : (4 / 3 : ℝ) * (s / 3) ^ 2 * s ≤
            (4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) := by gcongr
        linarith
      have h_exp : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) ≤
          -(1 / 96 : ℝ) * xtilde ^ 3 + -(1 / 14 : ℝ) * s := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s| *
            Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))
          ≤ M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3 + -(1 / 14 : ℝ) * s) :=
            mul_le_mul (tail_coef_bound β_plus hC_tl hR_plus hs1)
              (Real.exp_le_exp.mpr h_exp) (Real.exp_pos _).le hM0
        _ = M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) * Real.exp (-(1 / 14 : ℝ) * s) := by
            rw [Real.exp_add]; ring
    have h_int_exp0 : ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 14 : ℝ) * s) = 14 := by
      rw [integral_exp_mul_Ioi (by norm_num)]; norm_num
    have h_int_bd : ‖∫ s in Ici (3 * xtilde / 4), (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
        Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ ≤
        M * 14 * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) := by
      calc ‖∫ s in Ici (3 * xtilde / 4), _‖
          ≤ ∫ s in Ici (3 * xtilde / 4), ‖(β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
              Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ s in Ici (3 * xtilde / 4), M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) *
              Real.exp (-(1 / 14 : ℝ) * s) :=
            setIntegral_mono_on hint_g.norm hint_exp measurableSet_Ici h_le_exp
        _ ≤ ∫ s in Ioi (0 : ℝ), M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) *
              Real.exp (-(1 / 14 : ℝ) * s) :=
            setIntegral_mono_set hint_exp0 (ae_of_all _ fun s => by positivity)
              (Ici_subset_Ioi.mpr (by linarith : 0 < 3 * xtilde / 4)).eventuallySubset
        _ = M * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) *
              ∫ s in Ioi (0 : ℝ), Real.exp (-(1 / 14 : ℝ) * s) := integral_const_mul _ _
        _ = M * 14 * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3) := by rw [h_int_exp0]; ring
    have hpre_nn : 0 ≤ xtilde ^ (5 / 2 : ℝ) * ceK := mul_nonneg (Real.rpow_nonneg hx0 _) ceK_pos.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0 _), abs_of_pos ceK_pos]
    calc xtilde ^ (5 / 2 : ℝ) * ceK * |∫ s in Ici (3 * xtilde / 4), _|
        ≤ xtilde ^ (5 / 2 : ℝ) * ceK * (M * 14 * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3)) :=
          mul_le_mul_of_nonneg_left h_int_bd hpre_nn
      _ = ceK * M * 14 * (xtilde ^ (5 / 2 : ℝ) * Real.exp (-(1 / 96 : ℝ) * xtilde ^ 3)) := by ring
  have ht0 := (tendsto_rpow_mul_exp_neg_cube (by norm_num : (0 : ℝ) < 1 / 96) (5 / 2)).const_mul
    (ceK * M * 14)
  rw [mul_zero] at ht0
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
      (Eventually.of_forall fun _ => norm_nonneg _) h_bd)

/-- **Real-axis Laplace asymptotic** (`ce_rate.tex` Lemma P.1(1), `(cel:3.2)`). -/
theorem airyTwistedLaplace_tendsto {X R_plus : ℝ → ℝ} {β_plus C_tl : ℝ}
    (hX_int : Integrable X)
    (hX_tail : ∀ s ≥ 1, 2 * s * X (s ^ 2) =
      (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) * Real.exp (-(4 / 3 : ℝ) * s ^ 3))
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ)) :
    Filter.Tendsto (fun xtilde => xtilde ^ (5 / 2 : ℝ) * airyTwistedLaplace X xtilde)
      Filter.atTop (𝓝 (2 * ceK / √π * β_plus)) := by
  let g_main : ℝ → ℝ → ℝ := fun xtilde s =>
    (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
      Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))
  have hg_eq : ∀ xtilde : ℝ, ∀ s ≥ 1,
      Real.exp (-(xtilde ^ 3) / 12) * (2 * s * (X (s ^ 2) * Real.exp (xtilde * s ^ 2))) =
        g_main xtilde s := by
    intro xtilde s hs1
    dsimp [g_main]
    calc Real.exp (-(xtilde ^ 3) / 12) * (2 * s * (X (s ^ 2) * Real.exp (xtilde * s ^ 2)))
        = Real.exp (-(xtilde ^ 3) / 12) * ((2 * s * X (s ^ 2)) * Real.exp (xtilde * s ^ 2)) := by ring
      _ = (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
            (Real.exp (-(4 / 3 : ℝ) * s ^ 3) * Real.exp (xtilde * s ^ 2) *
              Real.exp (-(xtilde ^ 3) / 12)) := by rw [hX_tail s hs1]; ring
      _ = (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
            Real.exp (-(4 / 3 : ℝ) * s ^ 3 + xtilde * s ^ 2 - xtilde ^ 3 / 12) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ = (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
            Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4)) := by
          rw [completed_cube_id]
  have hg_int_Ioi : ∀ xtilde ≥ 0, IntegrableOn (g_main xtilde) (Ioi 1) := by
    intro xtilde hx
    have hIoi := tail_integrableOn_Ioi hX_int.aestronglyMeasurable hX_tail hC_tl hR_plus hx
    have hch := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s)
      (fun s _ => by simpa using (hasDerivAt_pow 2 s).hasDerivWithinAt) sq_injOn_Ioi_one
      (fun u => X u * Real.exp (xtilde * u))).mp (by rwa [sq_image_Ioi_one])
    refine IntegrableOn.congr_fun (hch.const_mul (Real.exp (-(xtilde ^ 3) / 12)))
      (fun s hs => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, abs_of_pos (by linarith [mem_Ioi.mp hs] : 0 < 2 * s)]
    exact hg_eq xtilde s (mem_Ioi.mp hs).le
  have h_left := laplace_left_tendsto hX_int
  have h_tail1 := laplace_tail1_tendsto hC_tl hR_plus hg_int_Ioi
  have h_tail2 := laplace_tail2_tendsto hC_tl hR_plus hg_int_Ioi
  -- Main saddle region `Ioo (xtilde / 4) (3 * xtilde / 4)`
  let I_mid : ℝ → ℝ := fun xtilde =>
    xtilde ^ (5 / 2 : ℝ) * ceK * ∫ s in Ioo (xtilde / 4) (3 * xtilde / 4), g_main xtilde s
  have h_mid : Filter.Tendsto I_mid Filter.atTop (𝓝 (2 * ceK / √π * β_plus)) := by
    let F : ℝ → ℝ → ℝ := fun xtilde t =>
      if |t| < xtilde ^ (3 / 2 : ℝ) / 4 then
        xtilde ^ 2 * g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)
      else 0
    let F_lim : ℝ → ℝ := fun t => (2 * β_plus / π) * Real.exp (-(t ^ 2))
    let B : ℝ → ℝ := fun t => (16 * |β_plus| / (2 * π) + 256 * C_tl) * Real.exp (-(2 / 3 : ℝ) * t ^ 2)
    have hB_int : Integrable B :=
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
    have h_ch_var : ∀ xtilde : ℝ, 8 ≤ xtilde →
        IntegrableOn (fun t : ℝ => xtilde ^ 2 *
          g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t))
          (Ioo (-(xtilde ^ (3 / 2 : ℝ) / 4)) (xtilde ^ (3 / 2 : ℝ) / 4)) ∧
        I_mid xtilde = ceK * ∫ t : ℝ, F xtilde t := by
      intro xtilde hx
      have hx0 : 0 < xtilde := by linarith
      set a := xtilde ^ (3 / 2 : ℝ) / 4
      have hint_main : IntegrableOn (g_main xtilde) (Ioo (xtilde / 4) (3 * xtilde / 4)) :=
        (hg_int_Ioi xtilde hx0.le).mono_set fun s hs => show 1 < s by linarith [hs.1]
      have hf' : ∀ t ∈ Ioo (-a) a,
          HasDerivWithinAt (fun t : ℝ => xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)
            (xtilde ^ (-(1 / 2 : ℝ))) (Ioo (-a) a) t := fun t _ => by
        simpa [mul_one] using
          (((hasDerivAt_id t).const_mul (xtilde ^ (-(1 / 2 : ℝ)))).const_add (xtilde / 2)).hasDerivWithinAt
      have hinj : InjOn (fun t : ℝ => xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t) (Ioo (-a) a) :=
        fun _ _ _ _ h => mul_left_cancel₀ (Real.rpow_pos_of_pos hx0 _).ne' (by linarith)
      have hch_int := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
        hf' hinj (g_main xtilde)).mp (by rwa [main_var_image xtilde hx])
      have hpow52 : xtilde ^ (5 / 2 : ℝ) * xtilde ^ (-(1 / 2 : ℝ)) = xtilde ^ 2 := by
        rw [← Real.rpow_add hx0]; norm_num
      have hpos_rpow : 0 < xtilde ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have hint2 : IntegrableOn
          (fun t => xtilde ^ 2 * g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t))
          (Ioo (-a) a) := by
        refine IntegrableOn.congr_fun (hch_int.const_mul (xtilde ^ (5 / 2 : ℝ)))
          (fun t _ => ?_) measurableSet_Ioo
        simp only [smul_eq_mul, abs_of_pos hpos_rpow, ← mul_assoc, hpow52]
      refine ⟨hint2, ?_⟩
      have hch := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hf' hinj (g_main xtilde)
      rw [main_var_image xtilde hx] at hch
      have hF_ind : ∀ t : ℝ, F xtilde t = (Ioo (-a) a).indicator
          (fun t => xtilde ^ 2 * g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)) t := by
        intro t; simp only [F, indicator, mem_Ioo, abs_lt, a]
      simp_rw [hF_ind, integral_indicator measurableSet_Ioo]
      dsimp [I_mid]
      rw [hch, ← integral_const_mul, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      rw [smul_eq_mul, abs_of_pos hpos_rpow]
      calc xtilde ^ (5 / 2 : ℝ) * ceK * (xtilde ^ (-(1 / 2 : ℝ)) *
              g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t))
          = ceK * ((xtilde ^ (5 / 2 : ℝ) * xtilde ^ (-(1 / 2 : ℝ))) *
              g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)) := by ring
        _ = ceK * (xtilde ^ 2 * g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)) := by
            rw [hpow52]
    have hF_eq : ∀ᶠ xtilde in atTop, I_mid xtilde = ceK * ∫ t : ℝ, F xtilde t := by
      filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
      exact (h_ch_var xtilde hx).2
    have hF_meas : ∀ᶠ xtilde in atTop, AEStronglyMeasurable (F xtilde) volume := by
      filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
      set a := xtilde ^ (3 / 2 : ℝ) / 4
      have hF_ind : F xtilde = (Ioo (-a) a).indicator
          (fun t => xtilde ^ 2 * g_main xtilde (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)) := by
        ext t; simp [F, indicator, mem_Ioo, abs_lt, a]
      rw [hF_ind]
      exact ((integrable_indicator_iff measurableSet_Ioo).mpr (h_ch_var xtilde hx).1).aestronglyMeasurable
    have h_s_ge : ∀ xtilde t : ℝ, 0 < xtilde → |t| < xtilde ^ (3 / 2 : ℝ) / 4 →
        xtilde / 4 ≤ xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t ∧
        xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t ≤ 3 * xtilde / 4 := by
      intro xtilde t hx0 ht
      have hpos := Real.rpow_pos_of_pos hx0 (-(1 / 2 : ℝ))
      have h1 : xtilde ^ (-(1 / 2 : ℝ)) * |t| < xtilde ^ (-(1 / 2 : ℝ)) * (xtilde ^ (3 / 2 : ℝ) / 4) :=
        mul_lt_mul_of_pos_left ht hpos
      have hpow : xtilde ^ (-(1 / 2 : ℝ)) * xtilde ^ (3 / 2 : ℝ) = xtilde := by
        rw [← Real.rpow_add hx0]; norm_num
      rw [mul_div_assoc', hpow, ← abs_of_pos hpos, ← abs_mul, abs_lt] at h1
      constructor <;> linarith
    have hF_bound : ∀ᶠ xtilde in atTop, ∀ᵐ t : ℝ, ‖F xtilde t‖ ≤ B t := by
      filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
      refine ae_of_all _ fun t => ?_
      have hx0 : 0 < xtilde := by linarith
      dsimp [F, B]
      split_ifs with ht
      · have hs_ge : xtilde / 4 ≤ xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t := (h_s_ge xtilde t hx0 ht).1
        let s := xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t
        have hs1 : 1 ≤ s := by dsimp [s]; linarith
        have hs_pos : 0 < s := by dsimp [s]; linarith
        have h_s2 : xtilde ^ 2 * s ^ (-2 : ℝ) ≤ 16 := by
          rw [Real.rpow_neg hs_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            ← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hs_pos)]
          have hsq4 : (xtilde / 4) ^ 2 ≤ s ^ 2 := by nlinarith [show xtilde / 4 ≤ s from hs_ge]
          linarith
        have h_R : xtilde ^ 2 * |R_plus s| ≤ 256 * C_tl := by
          have hs4 : s ^ (-4 : ℝ) = (s ^ 4)⁻¹ := by rw [Real.rpow_neg hs_pos.le]; norm_cast
          have h1 : xtilde ^ 2 * |R_plus s| ≤ C_tl * (xtilde ^ 2 * (s ^ 4)⁻¹) := by
            have := mul_le_mul_of_nonneg_left (hR_plus s hs1) (sq_nonneg xtilde)
            rw [hs4] at this; linarith
          have hs_p4 : (xtilde / 4) ^ 4 ≤ s ^ 4 :=
            pow_le_pow_left₀ (by linarith) hs_ge 4
          ring_nf at hs_p4
          have hx2_s4 : xtilde ^ 2 * (s ^ 4)⁻¹ ≤ 256 := by
            rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hs_pos 4)]
            have h4 : xtilde ^ 4 ≤ 256 * s ^ 4 := by linarith
            have hx2 : 64 ≤ xtilde ^ 2 := by nlinarith only [hx]
            have h64 : 64 * xtilde ^ 2 ≤ xtilde ^ 4 := by nlinarith only [hx2, sq_nonneg xtilde]
            linarith
          exact h1.trans (mul_le_mul_of_nonneg_left hx2_s4 hC_tl |>.trans_eq (by ring))
        have h_exp : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) ≤
            -(2 / 3 : ℝ) * t ^ 2 := by
          have hs_sub : s - xtilde / 2 = xtilde ^ (-(1 / 2 : ℝ)) * t := by dsimp [s]; ring
          have hsq : (xtilde ^ (-(1 / 2 : ℝ)) * t) ^ 2 = xtilde⁻¹ * t ^ 2 := by
            rw [mul_pow, ← Real.rpow_natCast (xtilde ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hx0.le,
              show (-(1 / 2 : ℝ)) * (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
          have hs_add : (1 / 2 : ℝ) * xtilde ≤ s + xtilde / 4 := by dsimp [s]; linarith
          have hcalc : (4 / 3 : ℝ) * (xtilde⁻¹ * t ^ 2) * ((1 / 2 : ℝ) * xtilde) =
              (2 / 3 : ℝ) * t ^ 2 := by field_simp [hx0.ne']; ring
          have hineq : (2 / 3 : ℝ) * t ^ 2 ≤
              (4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) := by
            rw [← hcalc]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (by rw [hs_sub, hsq]) (by norm_num))
              hs_add (by linarith) (by positivity)
          linarith
        have h_coef : xtilde ^ 2 * |β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s| ≤
            16 * |β_plus| / (2 * π) + 256 * C_tl := by
          calc xtilde ^ 2 * |β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s|
              ≤ xtilde ^ 2 * (|β_plus / (2 * π) * s ^ (-2 : ℝ)| + |R_plus s|) := by
                gcongr; exact abs_add_le _ _
            _ = |β_plus| / (2 * π) * (xtilde ^ 2 * s ^ (-2 : ℝ)) + xtilde ^ 2 * |R_plus s| := by
                rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
                  abs_of_nonneg (Real.rpow_nonneg hs_pos.le _)]; ring
            _ ≤ |β_plus| / (2 * π) * 16 + 256 * C_tl := by gcongr
            _ = 16 * |β_plus| / (2 * π) + 256 * C_tl := by ring
        dsimp [g_main]
        simp only [abs_mul, abs_of_nonneg (sq_nonneg xtilde),
          abs_of_pos (Real.exp_pos _), ← mul_assoc]
        exact mul_le_mul h_coef (Real.exp_le_exp.mpr h_exp) (Real.exp_pos _).le (by positivity)
      · simp only [abs_zero]; positivity
    have hF_lim : ∀ᵐ t : ℝ, Filter.Tendsto (fun xtilde => F xtilde t) atTop (𝓝 (F_lim t)) := by
      refine ae_of_all _ fun t => ?_
      have h_pow_inv : Filter.Tendsto (fun xtilde : ℝ => xtilde ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num)
      have h_ind : ∀ᶠ xtilde in atTop, |t| < xtilde ^ (3 / 2 : ℝ) / 4 :=
        ((tendsto_rpow_atTop (by norm_num)).atTop_div_const (by norm_num)).eventually_gt_atTop |t|
      have h_u : Filter.Tendsto (fun xtilde : ℝ => xtilde ^ (-(3 / 2 : ℝ)) * t) atTop (𝓝 0) := by
        simpa using h_pow_inv.mul_const t
      have h_coef1 : Filter.Tendsto
          (fun xtilde : ℝ => β_plus / (2 * π) * (1 / 2 + xtilde ^ (-(3 / 2 : ℝ)) * t) ^ (-2 : ℝ))
          atTop (𝓝 (2 * β_plus / π)) := by
        have h1 := Filter.Tendsto.rpow_const (p := (-2 : ℝ))
          (by simpa using (tendsto_const_nhds.add h_u))
          (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))
        have h2 : β_plus / (2 * π) * (1 / 2 : ℝ) ^ (-2 : ℝ) = 2 * β_plus / π := by norm_num; ring
        rw [← h2]
        simpa [one_div] using tendsto_const_nhds.mul h1
      have h_coef2 : Filter.Tendsto
          (fun xtilde : ℝ => xtilde ^ 2 * R_plus (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t))
          atTop (𝓝 0) := by
        have h_bd : ∀ᶠ xtilde in atTop,
            ‖xtilde ^ 2 * R_plus (xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t)‖ ≤
              256 * C_tl * xtilde ^ (-2 : ℝ) := by
          filter_upwards [eventually_ge_atTop (8 : ℝ), h_ind] with xtilde hx ht
          have hx0 : 0 < xtilde := by linarith
          have hs_ge := (h_s_ge xtilde t hx0 ht).1
          let s := xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t
          have hs1 : 1 ≤ s := by dsimp [s]; linarith
          have hs_pos : 0 < s := by dsimp [s]; linarith
          have hs4 : s ^ (-4 : ℝ) = (s ^ 4)⁻¹ := by rw [Real.rpow_neg hs_pos.le]; norm_cast
          have hx2_neg : xtilde ^ (-2 : ℝ) = (xtilde ^ 2)⁻¹ := by
            rw [Real.rpow_neg hx0.le]; norm_cast
          have h1 : xtilde ^ 2 * |R_plus s| ≤ C_tl * (xtilde ^ 2 * (s ^ 4)⁻¹) := by
            have := mul_le_mul_of_nonneg_left (hR_plus s hs1) (sq_nonneg xtilde)
            rw [hs4] at this; linarith
          have h_div : xtilde ^ 2 * (s ^ 4)⁻¹ ≤ 256 * (xtilde ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, ← div_eq_mul_inv,
              div_le_div_iff₀ (pow_pos hs_pos 4) (sq_pos_of_pos hx0)]
            have hs_p4 : (xtilde / 4) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (by linarith) hs_ge 4
            ring_nf at hs_p4 ⊢
            linarith
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg xtilde), hx2_neg]
          exact h1.trans (mul_le_mul_of_nonneg_left h_div hC_tl |>.trans_eq (by ring))
        have h0 : Filter.Tendsto (fun xtilde : ℝ => 256 * C_tl * xtilde ^ (-2 : ℝ)) atTop (𝓝 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul (256 * C_tl)
        exact tendsto_zero_iff_norm_tendsto_zero.mpr
          (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
            (Eventually.of_forall fun _ => norm_nonneg _) h_bd)
      have h_exp_lim : Filter.Tendsto
          (fun xtilde : ℝ => Real.exp (-(t ^ 2) * (1 + (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t)))
          atTop (𝓝 (Real.exp (-(t ^ 2)))) := by
        have h0 : Filter.Tendsto (fun xtilde : ℝ => (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t)
            atTop (𝓝 0) := by simpa using (h_pow_inv.const_mul (4 / 3 : ℝ)).mul_const t
        have h1 : Filter.Tendsto
            (fun xtilde : ℝ => -(t ^ 2) * (1 + (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t))
            atTop (𝓝 (-(t ^ 2) * (1 + 0))) :=
          tendsto_const_nhds.mul (tendsto_const_nhds.add h0)
        rw [add_zero, mul_one] at h1
        exact Real.continuous_exp.tendsto _ |>.comp h1
      have h_all := (h_coef1.add h_coef2).mul h_exp_lim
      rw [add_zero] at h_all
      refine h_all.congr' ?_
      filter_upwards [eventually_ge_atTop (8 : ℝ), h_ind] with xtilde hx ht
      have hx0 : 0 < xtilde := by linarith
      set s := xtilde / 2 + xtilde ^ (-(1 / 2 : ℝ)) * t
      have hs_eq : s = xtilde * (1 / 2 + xtilde ^ (-(3 / 2 : ℝ)) * t) := by
        have hpow : xtilde * xtilde ^ (-(3 / 2 : ℝ)) = xtilde ^ (-(1 / 2 : ℝ)) := by
          conv_lhs => lhs; rw [← Real.rpow_one xtilde]
          rw [← Real.rpow_add hx0]; norm_num
        dsimp [s]; rw [← hpow]; ring
      have h_u_pos : 0 < 1 / 2 + xtilde ^ (-(3 / 2 : ℝ)) * t := by
        have hpos := Real.rpow_pos_of_pos hx0 (-(3 / 2 : ℝ))
        have h1 : xtilde ^ (-(3 / 2 : ℝ)) * |t| < 1 / 4 := by
          have hmul := mul_lt_mul_of_pos_left ht hpos
          have hinv : xtilde ^ (-(3 / 2 : ℝ)) * xtilde ^ (3 / 2 : ℝ) = 1 := by
            rw [← Real.rpow_add hx0]; norm_num
          rwa [mul_div_assoc', hinv] at hmul
        rw [← abs_of_pos hpos, ← abs_mul, abs_lt] at h1
        linarith
      have h_rpow_s : xtilde ^ 2 * s ^ (-2 : ℝ) = (1 / 2 + xtilde ^ (-(3 / 2 : ℝ)) * t) ^ (-2 : ℝ) := by
        rw [hs_eq, Real.mul_rpow hx0.le h_u_pos.le]
        have hpow : xtilde ^ 2 * xtilde ^ (-2 : ℝ) = 1 := by
          rw [← Real.rpow_natCast xtilde 2, ← Real.rpow_add hx0]; norm_num
        rw [← mul_assoc, hpow, one_mul]
      have h_exp_eq : -(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4) =
          -(t ^ 2) * (1 + (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t) := by
        have hs_sub : s - xtilde / 2 = xtilde ^ (-(1 / 2 : ℝ)) * t := by dsimp [s]; ring
        have hsq : (xtilde ^ (-(1 / 2 : ℝ)) * t) ^ 2 = xtilde⁻¹ * t ^ 2 := by
          rw [mul_pow, ← Real.rpow_natCast (xtilde ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hx0.le,
            show (-(1 / 2 : ℝ)) * (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
        have hpow : xtilde⁻¹ * xtilde ^ (-(1 / 2 : ℝ)) = xtilde ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_neg_one xtilde, ← Real.rpow_add hx0]; norm_num
        have hs_add : s + xtilde / 4 = 3 / 4 * xtilde + xtilde ^ (-(1 / 2 : ℝ)) * t := by
          dsimp [s]; ring
        rw [hs_sub, hsq, hs_add]
        calc -(4 / 3 : ℝ) * (xtilde⁻¹ * t ^ 2) * (3 / 4 * xtilde + xtilde ^ (-(1 / 2 : ℝ)) * t)
            = -(t ^ 2) * ((xtilde⁻¹ * xtilde) + (4 / 3 : ℝ) * (xtilde⁻¹ * xtilde ^ (-(1 / 2 : ℝ))) * t) := by ring
          _ = -(t ^ 2) * (1 + (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t) := by
              rw [inv_mul_cancel₀ hx0.ne', hpow]
      dsimp [F, g_main]
      simp only [ht, ↓reduceIte]
      calc (β_plus / (2 * π) * (1 / 2 + xtilde ^ (-(3 / 2 : ℝ)) * t) ^ (-2 : ℝ) +
              xtilde ^ 2 * R_plus s) *
            Real.exp (-(t ^ 2) * (1 + (4 / 3 : ℝ) * xtilde ^ (-(3 / 2 : ℝ)) * t))
          = (β_plus / (2 * π) * (xtilde ^ 2 * s ^ (-2 : ℝ)) + xtilde ^ 2 * R_plus s) *
              Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4)) := by
            rw [← h_rpow_s, ← h_exp_eq]
        _ = xtilde ^ 2 * ((β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) *
              Real.exp (-(4 / 3 : ℝ) * (s - xtilde / 2) ^ 2 * (s + xtilde / 4))) := by ring
    have h_dct := tendsto_integral_filter_of_dominated_convergence B hF_meas hF_bound hB_int hF_lim
    have h_gauss : ∫ t : ℝ, F_lim t = 2 * β_plus / √π := by
      dsimp [F_lim]
      rw [integral_const_mul, show ∫ t : ℝ, Real.exp (-(t ^ 2)) = √π by simpa using integral_gaussian (1 : ℝ)]
      have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
      have hsq : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
      calc 2 * β_plus / π * √π = 2 * β_plus / (√π * √π) * √π := by rw [hπ]
        _ = 2 * β_plus / √π := by field_simp
    have h_ceK : Filter.Tendsto (fun xtilde => ceK * ∫ t : ℝ, F xtilde t) atTop
        (𝓝 (2 * ceK / √π * β_plus)) := by
      have h1 := h_dct.const_mul ceK
      rw [h_gauss] at h1
      convert h1 using 2; ring
    exact h_ceK.congr' (EventuallyEq.symm hF_eq)
  have h_sum := h_left.add ((h_tail1.add h_mid).add h_tail2)
  rw [zero_add, zero_add, add_zero] at h_sum
  refine h_sum.congr' ?_
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with xtilde hx
  have hx0 : 0 ≤ xtilde := by linarith
  have h_full_int := tail_integrable hX_int hX_tail hC_tl hR_plus hx0
  have h_split1 : ∫ u : ℝ, X u * Real.exp (xtilde * u) =
      (∫ u in Iic 1, X u * Real.exp (xtilde * u)) +
        ∫ u in Ioi 1, X u * Real.exp (xtilde * u) := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      h_full_int.integrableOn h_full_int.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have h_ch : Real.exp (-(xtilde ^ 3) / 12) * ∫ u in Ioi 1, X u * Real.exp (xtilde * u) =
      ∫ s in Ioi 1, g_main xtilde s := by
    have hch := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s)
      (fun s _ => by simpa using (hasDerivAt_pow 2 s).hasDerivWithinAt) sq_injOn_Ioi_one
      (fun u => X u * Real.exp (xtilde * u))
    rw [sq_image_Ioi_one] at hch
    rw [hch, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [smul_eq_mul, abs_of_pos (by linarith [mem_Ioi.mp hs] : 0 < 2 * s)]
    exact hg_eq xtilde s (mem_Ioi.mp hs).le
  have hIoi := hg_int_Ioi xtilde hx0
  have h1 : 1 < xtilde / 4 := by linarith
  have h2 : xtilde / 4 < 3 * xtilde / 4 := by linarith
  have h_split2 : ∫ s in Ioi 1, g_main xtilde s =
      (∫ s in Ioc 1 (xtilde / 4), g_main xtilde s) +
        (∫ s in Ioo (xtilde / 4) (3 * xtilde / 4), g_main xtilde s) +
          ∫ s in Ici (3 * xtilde / 4), g_main xtilde s := by
    have hu1 : Ioi 1 = Ioc 1 (xtilde / 4) ∪ Ioi (xtilde / 4) := (Ioc_union_Ioi_eq_Ioi h1.le).symm
    have hu2 : Ioi (xtilde / 4) = Ioo (xtilde / 4) (3 * xtilde / 4) ∪ Ici (3 * xtilde / 4) :=
      (Ioo_union_Ici_eq_Ioi h2).symm
    have hi1 : IntegrableOn (g_main xtilde) (Ioc 1 (xtilde / 4)) := hIoi.mono_set Ioc_subset_Ioi_self
    have hi2 : IntegrableOn (g_main xtilde) (Ioi (xtilde / 4)) := hIoi.mono_set (Ioi_subset_Ioi h1.le)
    have hi3 : IntegrableOn (g_main xtilde) (Ioo (xtilde / 4) (3 * xtilde / 4)) :=
      hi2.mono_set Ioo_subset_Ioi_self
    have hi4 : IntegrableOn (g_main xtilde) (Ici (3 * xtilde / 4)) :=
      hi2.mono_set (Ici_subset_Ioi.mpr h2)
    have hu2_int : ∫ s in Ioi (xtilde / 4), g_main xtilde s =
        (∫ s in Ioo (xtilde / 4) (3 * xtilde / 4), g_main xtilde s) +
          ∫ s in Ici (3 * xtilde / 4), g_main xtilde s := by
      rw [hu2]
      exact setIntegral_union
        (Set.disjoint_left.mpr fun _ ha hb => absurd hb (not_le_of_gt ha.2))
        measurableSet_Ici hi3 hi4
    rw [hu1, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi1 hi2, hu2_int, add_assoc]
  dsimp only [I_mid, airyTwistedLaplace]
  symm
  calc xtilde ^ (5 / 2 : ℝ) * (ceK * Real.exp (-(xtilde ^ 3) / 12) *
          ∫ u : ℝ, X u * Real.exp (xtilde * u))
      = xtilde ^ (5 / 2 : ℝ) * ceK * Real.exp (-(xtilde ^ 3) / 12) *
          (∫ u in Iic 1, X u * Real.exp (xtilde * u)) +
        xtilde ^ (5 / 2 : ℝ) * ceK *
          (Real.exp (-(xtilde ^ 3) / 12) * ∫ u in Ioi 1, X u * Real.exp (xtilde * u)) := by
          rw [h_split1]; ring
    _ = _ := by rw [h_ch, h_split2]; ring

/-- Rescaled real-axis Laplace asymptotic `(ce_rate.tex` `(cel:3.2)`). -/
theorem airyTwistedLaplace_rescaled_tendsto {X R_plus : ℝ → ℝ} {β_plus C_tl : ℝ}
    (hX_int : Integrable X)
    (hX_tail : ∀ s ≥ 1, 2 * s * X (s ^ 2) =
      (β_plus / (2 * π) * s ^ (-2 : ℝ) + R_plus s) * Real.exp (-(4 / 3 : ℝ) * s ^ 3))
    (hC_tl : 0 ≤ C_tl) (hR_plus : ∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ)) :
    Filter.Tendsto (fun x => x ^ (5 / 2 : ℝ) * airyTwistedLaplace X (ceCs * x))
      Filter.atTop (𝓝 (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π * β_plus)) := by
  have h1 := (airyTwistedLaplace_tendsto hX_int hX_tail hC_tl hR_plus).comp
    (tendsto_id.const_mul_atTop ceCs_pos)
  have h2 := h1.const_mul (ceCs ^ (-(5 / 2 : ℝ)))
  have h_lim : ceCs ^ (-(5 / 2 : ℝ)) * (2 * ceK / √π * β_plus) =
      2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π * β_plus := by ring
  rw [h_lim] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_def, id_eq]
  rw [Real.mul_rpow ceCs_pos.le hx.le, ← mul_assoc, ← mul_assoc,
    ← Real.rpow_add ceCs_pos, neg_add_cancel, Real.rpow_zero, one_mul]


/-! ### Axiom audit -/

/-- info: 'FormalResearch.CohnElkies.completed_cube_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.completed_cube_id

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplace_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyTwistedLaplace_tendsto

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplace_rescaled_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyTwistedLaplace_rescaled_tendsto

end FormalResearch.CohnElkies

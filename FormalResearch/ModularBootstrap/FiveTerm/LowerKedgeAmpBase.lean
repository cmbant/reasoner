module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualIdLeft
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeWeps
public import FormalResearch.ModularBootstrap.FiveTerm.OuterX
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3a

/-!
# Edge Geometry Order-3 Bounds and `OscAmpBound` Factor Building Blocks

Provides:
* `v_lt_edgeF`, `edgeF'''`, `hasDerivAt_edgeF''`, `edgeF''_bound`, `edgeF'''_bound`, `edgeF'_v_bounds`
* `OscAmpBound`: a uniform `L^∞ ∩ L¹` second-derivative package closed under products (`mul`)
* `theta_oscAmpBound`, `oneSubExp_oscAmpBound`, `sqrtEdgeF'_oscAmpBound`, `auxInv_oscAmpBound`
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-! ### 1. `edgeF` derivatives up to order 3 and exponential decay -/

/-- `edgeF v > v` for all `v : ℝ` (`cosh(πv) > sinh(πv)`). -/
lemma v_lt_edgeF (v : ℝ) : v < edgeF v := by
  have hlt : Real.sinh (π * v) < Real.cosh (π * v) := Real.sinh_lt_cosh (π * v)
  have har : π * v < Real.arsinh (Real.cosh (π * v)) := by
    calc π * v = Real.arsinh (Real.sinh (π * v)) := (Real.arsinh_sinh _).symm
      _ < Real.arsinh (Real.cosh (π * v)) := Real.arsinh_strictMono hlt
  unfold edgeF
  exact (lt_div_iff₀ Real.pi_pos).mpr (by linarith)

/-- Third derivative of `edgeF`:
`2 π² sinh(πv) (1 - 2 cosh(πv)²) / (1 + cosh(πv)²)^{5/2}`. -/
def edgeF''' (v : ℝ) : ℝ :=
  2 * π ^ 2 * Real.sinh (π * v) * (1 - 2 * Real.cosh (π * v) ^ 2) /
    (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ)

lemma hasDerivAt_edgeF'' (v : ℝ) : HasDerivAt edgeF'' (edgeF''' v) v := by
  have hpi : HasDerivAt (fun t : ℝ => π * t) π v := by simpa using (hasDerivAt_id v).const_mul π
  have hc : HasDerivAt (fun t : ℝ => Real.cosh (π * t)) (π * Real.sinh (π * v)) v :=
    ((Real.hasDerivAt_cosh (π * v)).comp v hpi).congr_deriv (by ring)
  have hden_pos : 0 < 1 + Real.cosh (π * v) ^ 2 := by positivity
  have hc2 : HasDerivAt (fun t : ℝ => 1 + Real.cosh (π * t) ^ 2)
      (2 * Real.cosh (π * v) * (π * Real.sinh (π * v))) v :=
    ((hc.pow 2).const_add 1).congr_deriv (by ring)
  have hpow : HasDerivAt (fun t : ℝ => (1 + Real.cosh (π * t) ^ 2) ^ (-(3 / 2 : ℝ)))
      (-(3 / 2 : ℝ) * (1 + Real.cosh (π * v) ^ 2) ^ (-(5 / 2 : ℝ)) *
        (2 * Real.cosh (π * v) * (π * Real.sinh (π * v)))) v := by
    have h : HasDerivAt (fun t : ℝ => (1 + Real.cosh (π * t) ^ 2) ^ (-(3 / 2 : ℝ)))
        (-(2 * Real.cosh (π * v) * (π * Real.sinh (π * v)) * (3 / 2 : ℝ) *
          (1 + Real.cosh (π * v) ^ 2) ^ (-(3 / 2 : ℝ) - 1))) v := by
      simpa [mul_comm, mul_assoc] using hc2.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hden_pos.ne')
    refine h.congr_deriv ?_
    rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num]; ring
  have hnum : HasDerivAt (fun t : ℝ => 2 * π * Real.cosh (π * t))
      (2 * π * (π * Real.sinh (π * v))) v := hc.const_mul (2 * π)
  have heq : edgeF'' = fun t => (2 * π * Real.cosh (π * t)) * (1 + Real.cosh (π * t) ^ 2) ^ (-(3 / 2 : ℝ)) := by
    ext t; unfold edgeF''
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
  rw [heq]
  refine (hnum.mul hpow).congr_deriv ?_
  have hr3 : (1 + Real.cosh (π * v) ^ 2) ^ (-(3 / 2 : ℝ)) =
      (1 + Real.cosh (π * v) ^ 2) * (1 + Real.cosh (π * v) ^ 2) ^ (-(5 / 2 : ℝ)) := by
    have h1 : -(3 / 2 : ℝ) = 1 + -(5 / 2 : ℝ) := by norm_num
    rw [h1, Real.rpow_add hden_pos, Real.rpow_one]
  have h5 : (1 + Real.cosh (π * v) ^ 2) ^ (-(5 / 2 : ℝ)) =
      ((1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg hden_pos.le (5 / 2 : ℝ)
  rw [hr3, h5]
  unfold edgeF'''
  ring

private lemma inv_cosh_sq_le {v : ℝ} (_hv : 0 ≤ v) :
    (Real.cosh (π * v) ^ 2)⁻¹ ≤ 4 * Real.exp (-(2 * π * v)) := by
  have hcosh : (1 / 2 : ℝ) * Real.exp (π * v) ≤ Real.cosh (π * v) := by
    rw [Real.cosh_eq]
    have he : 0 ≤ Real.exp (-(π * v)) := (Real.exp_pos _).le
    linarith
  have hsq : (1 / 4 : ℝ) * Real.exp (2 * π * v) ≤ Real.cosh (π * v) ^ 2 := by
    calc (1 / 4 : ℝ) * Real.exp (2 * π * v)
        = ((1 / 2 : ℝ) * Real.exp (π * v)) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; norm_cast; ring_nf
      _ ≤ Real.cosh (π * v) ^ 2 := pow_le_pow_left₀ (by positivity) hcosh 2
  rw [inv_le_iff_one_le_mul₀ (pow_pos (Real.cosh_pos _) 2)]
  calc (1 : ℝ) = Real.exp (-(2 * π * v)) * Real.exp (2 * π * v) := by
        rw [← Real.exp_add]; simp
    _ = 4 * Real.exp (-(2 * π * v)) * ((1 / 4 : ℝ) * Real.exp (2 * π * v)) := by ring
    _ ≤ 4 * Real.exp (-(2 * π * v)) * Real.cosh (π * v) ^ 2 := by gcongr

lemma edgeF''_bound {v : ℝ} (hv : 0 ≤ v) :
    0 < edgeF'' v ∧ edgeF'' v ≤ 8 * π * Real.exp (-(2 * π * v)) := by
  refine ⟨edgeF''_pos v, ?_⟩
  have hden : Real.cosh (π * v) ^ 3 ≤ (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
    have h1 : Real.cosh (π * v) ^ 3 = (Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (Real.cosh (π * v)), ← Real.rpow_natCast (Real.cosh (π * v)) 2,
        ← Real.rpow_mul (Real.cosh_pos _).le]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) (by linarith [sq_nonneg (Real.cosh (π * v))]) (by norm_num)
  have hle : edgeF'' v ≤ 2 * π / Real.cosh (π * v) ^ 2 := by
    unfold edgeF''
    have h1 : 2 * π * Real.cosh (π * v) / (1 + Real.cosh (π * v) ^ 2) ^ (3 / 2 : ℝ) ≤
        2 * π * Real.cosh (π * v) / Real.cosh (π * v) ^ 3 := by gcongr
    have h2 : 2 * π * Real.cosh (π * v) / Real.cosh (π * v) ^ 3 = 2 * π / Real.cosh (π * v) ^ 2 := by
      have hc0 : Real.cosh (π * v) ≠ 0 := (Real.cosh_pos _).ne'
      field_simp
    linarith
  calc edgeF'' v ≤ 2 * π * (Real.cosh (π * v) ^ 2)⁻¹ := by simpa [div_eq_mul_inv] using hle
    _ ≤ 2 * π * (4 * Real.exp (-(2 * π * v))) := by gcongr; exact inv_cosh_sq_le hv
    _ = 8 * π * Real.exp (-(2 * π * v)) := by ring

lemma edgeF'''_bound {v : ℝ} (hv : 0 ≤ v) :
    |edgeF''' v| ≤ 16 * π ^ 2 * Real.exp (-(2 * π * v)) := by
  have hch : 1 ≤ Real.cosh (π * v) := Real.one_le_cosh _
  have hsh : |Real.sinh (π * v)| ≤ Real.cosh (π * v) := by
    rw [abs_le]; constructor <;>
      linarith [Real.sinh_lt_cosh (π * v), Real.sinh_lt_cosh (-(π * v)), Real.sinh_neg (π * v), Real.cosh_neg (π * v)]
  have hfac : |1 - 2 * Real.cosh (π * v) ^ 2| ≤ 2 * Real.cosh (π * v) ^ 2 := by
    have h1 : 1 ≤ Real.cosh (π * v) ^ 2 := by nlinarith
    rw [abs_of_nonpos (by linarith)]; linarith
  have hden : Real.cosh (π * v) ^ 5 ≤ (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) := by
    have h1 : Real.cosh (π * v) ^ 5 = (Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (Real.cosh (π * v)), ← Real.rpow_natCast (Real.cosh (π * v)) 2,
        ← Real.rpow_mul (Real.cosh_pos _).le]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) (by linarith [sq_nonneg (Real.cosh (π * v))]) (by norm_num)
  have hden_pos : 0 < (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hle : |edgeF''' v| ≤ 4 * π ^ 2 / Real.cosh (π * v) ^ 2 := by
    unfold edgeF'''
    rw [abs_div, abs_of_pos hden_pos, abs_mul, abs_mul, abs_mul,
      abs_of_pos two_pos, abs_of_pos (pow_pos Real.pi_pos 2)]
    calc 2 * π ^ 2 * |Real.sinh (π * v)| * |1 - 2 * Real.cosh (π * v) ^ 2| /
          (1 + Real.cosh (π * v) ^ 2) ^ (5 / 2 : ℝ)
        ≤ 2 * π ^ 2 * Real.cosh (π * v) * (2 * Real.cosh (π * v) ^ 2) / Real.cosh (π * v) ^ 5 := by gcongr
      _ = 4 * π ^ 2 / Real.cosh (π * v) ^ 2 := by
          have hc0 : Real.cosh (π * v) ≠ 0 := (Real.cosh_pos _).ne'
          field_simp; ring
  calc |edgeF''' v| ≤ 4 * π ^ 2 * (Real.cosh (π * v) ^ 2)⁻¹ := by simpa [div_eq_mul_inv] using hle
    _ ≤ 4 * π ^ 2 * (4 * Real.exp (-(2 * π * v))) := by gcongr; exact inv_cosh_sq_le hv
    _ = 16 * π ^ 2 * Real.exp (-(2 * π * v)) := by ring

lemma edgeF'_v_bounds {v₀ v : ℝ} (_hv₀ : 0 < v₀) (hv : v₀ ≤ v) :
    edgeF' v₀ ≤ edgeF' v ∧ edgeF' v < 1 :=
  ⟨edgeF'_strictMono.monotone hv, edgeF'_lt_one v⟩

lemma integrableOn_exp_neg_Ioi (v₀ a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun v => Real.exp (-(a * v))) (Ioi v₀) ∧
      ∫ v in Ioi v₀, Real.exp (-(a * v)) ≤ Real.exp (-(a * v₀)) / a := by
  have hi : IntegrableOn (fun v => Real.exp (-(a * v))) (Ioi v₀) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi v₀ ha
  refine ⟨hi, ?_⟩
  have hd : ∀ v ∈ Ici v₀, HasDerivAt (fun t : ℝ => -Real.exp (-(a * t)) / a) (Real.exp (-(a * v))) v := by
    intro v _
    have h1 := (((hasDerivAt_id v).const_mul a).neg.exp).neg.div_const a
    refine h1.congr_deriv ?_
    simp [ha.ne']
  have ht : Tendsto (fun t : ℝ => -Real.exp (-(a * t)) / a) atTop (𝓝 (-0 / a)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    have hmul : Tendsto (fun t : ℝ => -(a * t)) atTop atBot := by
      have h := (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 ha))
      simpa [neg_mul] using h
    exact Real.tendsto_exp_atBot.comp hmul
  have heq := integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun v _ => (Real.exp_pos _).le) ht
  rw [heq]; ring_nf; exact le_rfl

lemma edgeF_ge_of_ge {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : v₀ ≤ v) :
    xiStar < edgeF v₀ ∧ edgeF v₀ ≤ edgeF v := by
  have h1 : xiStar < edgeF v₀ := by
    rw [← edgeF_zero]
    exact edgeF_strictMonoOn (by simp) hv₀.le hv₀
  have h2 : edgeF v₀ ≤ edgeF v := by
    rcases hv.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (edgeF_strictMonoOn hv₀.le (hv₀.le.trans hv) hlt).le
  exact ⟨h1, h2⟩

/-! ### 2. Uniform `L^∞ ∩ L¹` `C^2`-a.e. amplitude package and product combinator -/

/-- Bounds for `F` (`‖F‖_∞ ≤ K0`) and its two derivatives `F1, F2` (`L^∞ ∩ L¹`) on `[v₀, ∞)`. -/
structure OscAmpBound (v₀ : ℝ) (F F1 F2 : ℝ → ℂ) where
  hd1 : ∀ v ∈ Ici v₀, HasDerivAt F (F1 v) v
  hd2 : ∀ v ∈ Ici v₀, HasDerivAt F1 (F2 v) v
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  L1 : ℝ
  L2 : ℝ
  hK0 : 0 ≤ K0
  hK1 : 0 ≤ K1
  hK2 : 0 ≤ K2
  hL1 : 0 ≤ L1
  hL2 : 0 ≤ L2
  b0 : ∀ v ∈ Ici v₀, ‖F v‖ ≤ K0
  b1 : ∀ v ∈ Ici v₀, ‖F1 v‖ ≤ K1
  b2 : ∀ v ∈ Ici v₀, ‖F2 v‖ ≤ K2
  i1 : IntegrableOn F1 (Ioi v₀)
  int1 : ∫ v in Ioi v₀, ‖F1 v‖ ≤ L1
  i2 : IntegrableOn F2 (Ioi v₀)
  int2 : ∫ v in Ioi v₀, ‖F2 v‖ ≤ L2

def OscAmpBound.HasConsts {v₀ : ℝ} {F F1 F2 : ℝ → ℂ} (h : OscAmpBound v₀ F F1 F2)
    (C0 C1 C2 M1 M2 : ℝ) : Prop :=
  h.K0 ≤ C0 ∧ h.K1 ≤ C1 ∧ h.K2 ≤ C2 ∧ h.L1 ≤ M1 ∧ h.L2 ≤ M2

private lemma integrableOn_Ioi_mul_bdd_left {v₀ C : ℝ} {f g : ℝ → ℂ} (_hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi v₀)))
    (hfb : ∀ v ∈ Ioi v₀, ‖f v‖ ≤ C) (hg : IntegrableOn g (Ioi v₀)) :
    IntegrableOn (fun v => f v * g v) (Ioi v₀) ∧
      ∫ v in Ioi v₀, ‖f v * g v‖ ≤ C * ∫ v in Ioi v₀, ‖g v‖ := by
  have hint : IntegrableOn (fun v => f v * g v) (Ioi v₀) :=
    Integrable.bdd_mul hg hf ((ae_restrict_mem measurableSet_Ioi).mono hfb)
  refine ⟨hint, ?_⟩
  have hle : ∀ᵐ v ∂(volume.restrict (Ioi v₀)), ‖f v * g v‖ ≤ C * ‖g v‖ :=
    (ae_restrict_mem measurableSet_Ioi).mono fun v hv => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hfb v hv) (norm_nonneg _)
  calc ∫ v in Ioi v₀, ‖f v * g v‖ ≤ ∫ v in Ioi v₀, C * ‖g v‖ :=
        integral_mono_ae hint.norm (hg.norm.const_mul C) hle
    _ = C * ∫ v in Ioi v₀, ‖g v‖ := integral_const_mul C _

/-- Helper building `OscAmpBound v₀` from exponential-decay derivative bounds `C_j * exp(-a v)`. -/
def OscAmpBound.ofExpDecay {v₀ : ℝ} (hv₀ : 0 ≤ v₀) {F F1 F2 : ℝ → ℂ}
    (hd1 : ∀ v ∈ Ici v₀, HasDerivAt F (F1 v) v)
    (hd2 : ∀ v ∈ Ici v₀, HasDerivAt F1 (F2 v) v)
    (hm2 : AEStronglyMeasurable F2 (volume.restrict (Ioi v₀)))
    (K0 C1 C2 a : ℝ) (hK0 : 0 ≤ K0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (ha : 0 < a)
    (hb0 : ∀ v ∈ Ici v₀, ‖F v‖ ≤ K0)
    (hb1 : ∀ v ∈ Ici v₀, ‖F1 v‖ ≤ C1 * Real.exp (-(a * v)))
    (hb2 : ∀ v ∈ Ici v₀, ‖F2 v‖ ≤ C2 * Real.exp (-(a * v))) :
    OscAmpBound v₀ F F1 F2 :=
  have hF1_c : ContinuousOn F1 (Ici v₀) := fun v hv => (hd2 v hv).continuousAt.continuousWithinAt
  have hexp_int := integrableOn_exp_neg_Ioi v₀ a ha
  have hexp_le1 : ∀ v ∈ Ici v₀, Real.exp (-(a * v)) ≤ 1 := fun v hv =>
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le (hv₀.trans hv)))
  have hexp_int_bd : ∫ v in Ioi v₀, Real.exp (-(a * v)) ≤ 1 / a :=
    hexp_int.2.trans (div_le_div_of_nonneg_right
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le hv₀))) ha.le)
  have hi1 : IntegrableOn F1 (Ioi v₀) := by
    refine (hexp_int.1.const_mul C1).mono' ((hF1_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hb1 v hv.le
  have hi2 : IntegrableOn F2 (Ioi v₀) := by
    refine (hexp_int.1.const_mul C2).mono' hm2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hb2 v hv.le
  {
    hd1 := hd1
    hd2 := hd2
    K0 := K0
    K1 := C1
    K2 := C2
    L1 := C1 / a
    L2 := C2 / a
    hK0 := hK0
    hK1 := hC1
    hK2 := hC2
    hL1 := div_nonneg hC1 ha.le
    hL2 := div_nonneg hC2 ha.le
    b0 := hb0
    b1 := fun v hv => (hb1 v hv).trans (by nlinarith [hexp_le1 v hv])
    b2 := fun v hv => (hb2 v hv).trans (by nlinarith [hexp_le1 v hv])
    i1 := hi1
    int1 := by
      calc ∫ v in Ioi v₀, ‖F1 v‖ ≤ ∫ v in Ioi v₀, C1 * Real.exp (-(a * v)) :=
            integral_mono_ae hi1.norm (hexp_int.1.const_mul C1)
              ((ae_restrict_mem measurableSet_Ioi).mono fun v hv => hb1 v hv.le)
        _ = C1 * ∫ v in Ioi v₀, Real.exp (-(a * v)) := integral_const_mul C1 _
        _ ≤ C1 * (1 / a) := mul_le_mul_of_nonneg_left hexp_int_bd hC1
        _ = C1 / a := by ring
    i2 := hi2
    int2 := by
      calc ∫ v in Ioi v₀, ‖F2 v‖ ≤ ∫ v in Ioi v₀, C2 * Real.exp (-(a * v)) :=
            integral_mono_ae hi2.norm (hexp_int.1.const_mul C2)
              ((ae_restrict_mem measurableSet_Ioi).mono fun v hv => hb2 v hv.le)
        _ = C2 * ∫ v in Ioi v₀, Real.exp (-(a * v)) := integral_const_mul C2 _
        _ ≤ C2 * (1 / a) := mul_le_mul_of_nonneg_left hexp_int_bd hC2
        _ = C2 / a := by ring
  }

/-- Product combinator for `OscAmpBound` on `[v₀, ∞)`. -/
def OscAmpBound.mul {v₀ : ℝ} {A A1 A2 B B1 B2 : ℝ → ℂ}
    (hA : OscAmpBound v₀ A A1 A2) (hB : OscAmpBound v₀ B B1 B2) :
    OscAmpBound v₀ (fun v => A v * B v) (fun v => A1 v * B v + A v * B1 v)
      (fun v => A2 v * B v + 2 * (A1 v * B1 v) + A v * B2 v) where
  hd1 v hv := (hA.hd1 v hv).mul (hB.hd1 v hv)
  hd2 v hv := by
    have hd := ((hA.hd2 v hv).mul (hB.hd1 v hv)).add ((hA.hd1 v hv).mul (hB.hd2 v hv))
    refine hd.congr_deriv ?_; ring
  K0 := hA.K0 * hB.K0
  K1 := hA.K1 * hB.K0 + hA.K0 * hB.K1
  K2 := hA.K2 * hB.K0 + 2 * (hA.K1 * hB.K1) + hA.K0 * hB.K2
  L1 := hB.K0 * hA.L1 + hA.K0 * hB.L1
  L2 := hB.K0 * hA.L2 + 2 * (hA.K1 * hB.L1) + hA.K0 * hB.L2
  hK0 := mul_nonneg hA.hK0 hB.hK0
  hK1 := add_nonneg (mul_nonneg hA.hK1 hB.hK0) (mul_nonneg hA.hK0 hB.hK1)
  hK2 := add_nonneg (add_nonneg (mul_nonneg hA.hK2 hB.hK0) (by nlinarith [hA.hK1, hB.hK1]))
    (mul_nonneg hA.hK0 hB.hK2)
  hL1 := add_nonneg (mul_nonneg hB.hK0 hA.hL1) (mul_nonneg hA.hK0 hB.hL1)
  hL2 := add_nonneg (add_nonneg (mul_nonneg hB.hK0 hA.hL2) (by nlinarith [hA.hK1, hB.hL1]))
    (mul_nonneg hA.hK0 hB.hL2)
  b0 v hv := by rw [norm_mul]; exact mul_le_mul (hA.b0 v hv) (hB.b0 v hv) (norm_nonneg _) hA.hK0
  b1 v hv := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add
      (mul_le_mul (hA.b1 v hv) (hB.b0 v hv) (norm_nonneg _) hA.hK1)
      (mul_le_mul (hA.b0 v hv) (hB.b1 v hv) (norm_nonneg _) hA.hK0)
  b2 v hv := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul]; exact mul_le_mul (hA.b2 v hv) (hB.b0 v hv) (norm_nonneg _) hA.hK2
    · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hA.b1 v hv) (hB.b1 v hv) (norm_nonneg _) hA.hK1) (by norm_num)
    · rw [norm_mul]; exact mul_le_mul (hA.b0 v hv) (hB.b2 v hv) (norm_nonneg _) hA.hK0
  i1 := by
    have hAc : ContinuousOn A (Ici v₀) := fun v hv => (hA.hd1 v hv).continuousAt.continuousWithinAt
    have hBc : ContinuousOn B (Ici v₀) := fun v hv => (hB.hd1 v hv).continuousAt.continuousWithinAt
    have h1 := (integrableOn_Ioi_mul_bdd_left hB.hK0
      ((hBc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hB.b0 v hv.le) hA.i1).1.congr_fun (fun v _ => mul_comm _ _) measurableSet_Ioi
    have h2 := (integrableOn_Ioi_mul_bdd_left hA.hK0
      ((hAc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b0 v hv.le) hB.i1).1
    exact h1.add h2
  int1 := by
    have hAc : ContinuousOn A (Ici v₀) := fun v hv => (hA.hd1 v hv).continuousAt.continuousWithinAt
    have hBc : ContinuousOn B (Ici v₀) := fun v hv => (hB.hd1 v hv).continuousAt.continuousWithinAt
    have p1 := integrableOn_Ioi_mul_bdd_left hB.hK0
      ((hBc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hB.b0 v hv.le) hA.i1
    have p2 := integrableOn_Ioi_mul_bdd_left hA.hK0
      ((hAc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b0 v hv.le) hB.i1
    have h12 : IntegrableOn (fun v => A1 v * B v + A v * B1 v) (Ioi v₀) :=
      (p1.1.congr_fun (fun v _ => mul_comm _ _) measurableSet_Ioi).add p2.1
    have htri : ∀ v, ‖A1 v * B v + A v * B1 v‖ ≤ ‖B v * A1 v‖ + ‖A v * B1 v‖ := fun v => by
      rw [mul_comm (B v) (A1 v)]; exact norm_add_le _ _
    calc ∫ v in Ioi v₀, ‖A1 v * B v + A v * B1 v‖
        ≤ ∫ v in Ioi v₀, (‖B v * A1 v‖ + ‖A v * B1 v‖) :=
          integral_mono h12.norm (p1.1.norm.add p2.1.norm) htri
      _ = (∫ v in Ioi v₀, ‖B v * A1 v‖) + ∫ v in Ioi v₀, ‖A v * B1 v‖ :=
          integral_add p1.1.norm p2.1.norm
      _ ≤ hB.K0 * hA.L1 + hA.K0 * hB.L1 := add_le_add
          (p1.2.trans (mul_le_mul_of_nonneg_left hA.int1 hB.hK0))
          (p2.2.trans (mul_le_mul_of_nonneg_left hB.int1 hA.hK0))
  i2 := by
    have hAc : ContinuousOn A (Ici v₀) := fun v hv => (hA.hd1 v hv).continuousAt.continuousWithinAt
    have hBc : ContinuousOn B (Ici v₀) := fun v hv => (hB.hd1 v hv).continuousAt.continuousWithinAt
    have hA1c : ContinuousOn A1 (Ici v₀) := fun v hv => (hA.hd2 v hv).continuousAt.continuousWithinAt
    have h1 := (integrableOn_Ioi_mul_bdd_left hB.hK0
      ((hBc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hB.b0 v hv.le) hA.i2).1.congr_fun (fun v _ => mul_comm _ _) measurableSet_Ioi
    have h2 := ((integrableOn_Ioi_mul_bdd_left hA.hK1
      ((hA1c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b1 v hv.le) hB.i1).1).const_mul (2 : ℂ)
    have h3 := (integrableOn_Ioi_mul_bdd_left hA.hK0
      ((hAc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b0 v hv.le) hB.i2).1
    exact (h1.add h2).add h3
  int2 := by
    have hAc : ContinuousOn A (Ici v₀) := fun v hv => (hA.hd1 v hv).continuousAt.continuousWithinAt
    have hBc : ContinuousOn B (Ici v₀) := fun v hv => (hB.hd1 v hv).continuousAt.continuousWithinAt
    have hA1c : ContinuousOn A1 (Ici v₀) := fun v hv => (hA.hd2 v hv).continuousAt.continuousWithinAt
    have p1 := integrableOn_Ioi_mul_bdd_left hB.hK0
      ((hBc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hB.b0 v hv.le) hA.i2
    have p2 := integrableOn_Ioi_mul_bdd_left hA.hK1
      ((hA1c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b1 v hv.le) hB.i1
    have p3 := integrableOn_Ioi_mul_bdd_left hA.hK0
      ((hAc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
      (fun v hv => hA.b0 v hv.le) hB.i2
    have h12 : IntegrableOn (fun v => A2 v * B v + 2 * (A1 v * B1 v) + A v * B2 v) (Ioi v₀) :=
      ((p1.1.congr_fun (fun v _ => mul_comm _ _) measurableSet_Ioi).add (p2.1.const_mul 2)).add p3.1
    have htri : ∀ v, ‖A2 v * B v + 2 * (A1 v * B1 v) + A v * B2 v‖ ≤
        ‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖ + ‖A v * B2 v‖ := fun v => by
      calc ‖A2 v * B v + 2 * (A1 v * B1 v) + A v * B2 v‖
          ≤ ‖A2 v * B v + 2 * (A1 v * B1 v)‖ + ‖A v * B2 v‖ := norm_add_le _ _
        _ ≤ (‖A2 v * B v‖ + ‖2 * (A1 v * B1 v)‖) + ‖A v * B2 v‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖ + ‖A v * B2 v‖ := by
            rw [mul_comm (A2 v) (B v), norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hsum : IntegrableOn (fun v => ‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖ + ‖A v * B2 v‖) (Ioi v₀) :=
      (p1.1.norm.add (p2.1.norm.const_mul 2)).add p3.1.norm
    have hiA : IntegrableOn (fun v => ‖B v * A2 v‖) (Ioi v₀) := p1.1.norm
    have hiB : IntegrableOn (fun v => 2 * ‖A1 v * B1 v‖) (Ioi v₀) := p2.1.norm.const_mul 2
    have hiC : IntegrableOn (fun v => ‖A v * B2 v‖) (Ioi v₀) := p3.1.norm
    have he1 := integral_add (hiA.add hiB) hiC
    have he2 := integral_add hiA hiB
    calc ∫ v in Ioi v₀, ‖A2 v * B v + 2 * (A1 v * B1 v) + A v * B2 v‖
        ≤ ∫ v in Ioi v₀, (‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖ + ‖A v * B2 v‖) :=
          integral_mono h12.norm hsum htri
      _ = (∫ v in Ioi v₀, ‖B v * A2 v‖) + 2 * (∫ v in Ioi v₀, ‖A1 v * B1 v‖) +
            ∫ v in Ioi v₀, ‖A v * B2 v‖ := by
          rw [show (∫ v in Ioi v₀, ‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖ + ‖A v * B2 v‖) =
            (∫ v in Ioi v₀, (‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖)) + ∫ v in Ioi v₀, ‖A v * B2 v‖ from he1,
            show (∫ v in Ioi v₀, ‖B v * A2 v‖ + 2 * ‖A1 v * B1 v‖) =
              (∫ v in Ioi v₀, ‖B v * A2 v‖) + ∫ v in Ioi v₀, 2 * ‖A1 v * B1 v‖ from he2,
            integral_const_mul]
      _ ≤ hB.K0 * hA.L2 + 2 * (hA.K1 * hB.L1) + hA.K0 * hB.L2 := by
          gcongr
          · exact p1.2.trans (mul_le_mul_of_nonneg_left hA.int2 hB.hK0)
          · exact p2.2.trans (mul_le_mul_of_nonneg_left hB.int1 hA.hK1)
          · exact p3.2.trans (mul_le_mul_of_nonneg_left hB.int2 hA.hK0)

/-! ### 3. Outer-phase, geometric, and auxiliary-denominator factors -/

/-- Outer-phase factor `exp(I * thetaOut (lowerY (edgeF v)))` satisfies `OscAmpBound` on `[v₀, ∞)`. -/
lemma theta_oscAmpBound {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ F1 F2 : ℝ → ℂ,
      Nonempty (OscAmpBound v₀ (fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))) F1 F2) := by
  obtain ⟨Cθ, hCθ, _, hdiff, hth1_bd, hth2_bd, _⟩ := outerS2
  let x₀ := edgeF v₀
  have hx₀ : xiStar < x₀ := (edgeF_ge_of_ge hv₀ le_rfl).1
  let m₀ : ℝ := min (x₀ - xiStar) 1
  have hm₀ : 0 < m₀ := lt_min (sub_pos.mpr hx₀) one_pos
  let ph1 : ℝ → ℝ := fun v => deriv thetaOutX (edgeF v) * edgeF' v
  let ph2 : ℝ → ℝ := fun v => deriv (deriv thetaOutX) (edgeF v) * edgeF' v ^ 2 +
    deriv thetaOutX (edgeF v) * edgeF'' v
  let F : ℝ → ℂ := fun v => Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ))
  let F1 : ℝ → ℂ := fun v => Complex.I * (ph1 v : ℂ) * F v
  let F2 : ℝ → ℂ := fun v => (Complex.I * (ph2 v : ℂ) - ((ph1 v ^ 2 : ℝ) : ℂ)) * F v
  have hhd_ph : ∀ v ∈ Ici v₀,
      HasDerivAt (fun t => thetaOut (lowerY (edgeF t))) (ph1 v) v ∧
      HasDerivAt ph1 (ph2 v) v := fun v hv => by
    have hx : xiStar < edgeF v := hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
    have heq : ∀ᶠ t in 𝓝 v, thetaOut (lowerY (edgeF t)) = thetaOutX (edgeF t) := by
      have hF_c : ContinuousAt edgeF v := (hasDerivAt_edgeF v).continuousAt
      filter_upwards [hF_c.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)] with t ht
      exact thetaOut_yOfX ht
    have h1 := ((hdiff (edgeF v) hx).1.hasDerivAt.comp v (hasDerivAt_edgeF v)).congr_of_eventuallyEq heq
    have h2 : HasDerivAt ph1 (ph2 v) v :=
      (((hdiff (edgeF v) hx).2.hasDerivAt.comp v (hasDerivAt_edgeF v)).mul (hasDerivAt_edgeF' v)).congr_deriv
        (by dsimp [ph2]; ring)
    exact ⟨h1, h2⟩
  have hhd1 : ∀ v ∈ Ici v₀, HasDerivAt F (F1 v) v := fun v hv =>
    (((hhd_ph v hv).1.ofReal_comp.const_mul Complex.I).cexp).congr_deriv (by dsimp [F1, F]; ring)
  have hhd2 : ∀ v ∈ Ici v₀, HasDerivAt F1 (F2 v) v := fun v hv => by
    have h := ((hhd_ph v hv).2.ofReal_comp.const_mul Complex.I).mul (hhd1 v hv)
    refine h.congr_deriv ?_
    dsimp [F2, F1]; push_cast
    calc (Complex.I * (ph2 v : ℂ)) * F v + (Complex.I * (ph1 v : ℂ)) * (Complex.I * (ph1 v : ℂ) * F v)
        = (Complex.I * (ph2 v : ℂ) + Complex.I ^ 2 * ((ph1 v : ℂ) ^ 2)) * F v := by ring
      _ = (Complex.I * (ph2 v : ℂ) - ((ph1 v : ℂ) ^ 2)) * F v := by rw [Complex.I_sq]; ring
  let C1 : ℝ := Cθ * m₀ ^ (-(1 / 2 : ℝ))
  let C2 : ℝ := Cθ * m₀ ^ (-(3 / 2 : ℝ)) + 8 * π * C1
  let K2 : ℝ := C2 + C1 ^ 2
  have hmin_rpow : ∀ {v : ℝ} (hv : v ∈ Ici v₀),
      min (edgeF v - xiStar) 1 ^ (-(1 : ℝ) / 2) ≤ m₀ ^ (-(1 / 2 : ℝ)) ∧
      min (edgeF v - xiStar) 1 ^ (-(3 : ℝ) / 2) ≤ m₀ ^ (-(3 / 2 : ℝ)) := fun {v} hv => by
    have hmin_ge : m₀ ≤ min (edgeF v - xiStar) 1 :=
      le_min (le_trans (min_le_left _ _) (by linarith [(edgeF_ge_of_ge hv₀ hv).2])) (min_le_right _ _)
    refine ⟨?_, ?_⟩
    · rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg (lt_of_lt_of_le hm₀ hmin_ge).le, Real.rpow_neg hm₀.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hm₀ _) (Real.rpow_le_rpow hm₀.le hmin_ge (by norm_num))
    · rw [show -(3 : ℝ) / 2 = -(3 / 2 : ℝ) by norm_num,
        Real.rpow_neg (lt_of_lt_of_le hm₀ hmin_ge).le, Real.rpow_neg hm₀.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hm₀ _) (Real.rpow_le_rpow hm₀.le hmin_ge (by norm_num))
  have hbd_ph1 : ∀ v ∈ Ici v₀, |ph1 v| ≤ C1 * Real.exp (-(π * v)) := fun v hv => by
    have hx := hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
    have hexp : Real.exp (-(π * edgeF v)) ≤ Real.exp (-(π * v)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (v_lt_edgeF v).le Real.pi_pos.le))
    have hF' := edgeF'_v_bounds hv₀ hv
    have hm1 := (hmin_rpow hv).1
    dsimp [ph1]
    rw [abs_mul, abs_of_pos (edgeF'_pos (hv₀.trans_le hv))]
    calc |deriv thetaOutX (edgeF v)| * edgeF' v
        ≤ (Cθ * min (edgeF v - xiStar) 1 ^ (-(1 : ℝ) / 2) * Real.exp (-(π * edgeF v))) * 1 :=
          mul_le_mul (hth1_bd (edgeF v) hx) hF'.2.le (edgeF'_pos (hv₀.trans_le hv)).le (by positivity)
      _ ≤ (Cθ * m₀ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π * v))) * 1 := by
          gcongr
      _ = C1 * Real.exp (-(π * v)) := by dsimp [C1]; ring
  have hbd_ph2 : ∀ v ∈ Ici v₀, |ph2 v| ≤ C2 * Real.exp (-(π * v)) := fun v hv => by
    have hx := hx₀.trans_le (edgeF_ge_of_ge hv₀ hv).2
    have hexp : Real.exp (-(π * edgeF v)) ≤ Real.exp (-(π * v)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (v_lt_edgeF v).le Real.pi_pos.le))
    have hF' := edgeF'_v_bounds hv₀ hv
    have hF'' := edgeF''_bound (hv₀.le.trans hv)
    have h8 : edgeF'' v ≤ 8 * π := by
      have hexp1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv₀.le.trans hv])
      nlinarith [hF''.2, Real.pi_pos]
    have hmr := hmin_rpow hv
    dsimp [ph2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (edgeF' v)), abs_mul, abs_of_pos hF''.1]
    have ht1 : |deriv (deriv thetaOutX) (edgeF v)| * edgeF' v ^ 2 ≤
        Cθ * m₀ ^ (-(3 / 2 : ℝ)) * Real.exp (-(π * v)) := by
      have hsq : edgeF' v ^ 2 ≤ 1 := by nlinarith [edgeF'_pos (hv₀.trans_le hv), hF'.2]
      calc |deriv (deriv thetaOutX) (edgeF v)| * edgeF' v ^ 2
          ≤ (Cθ * min (edgeF v - xiStar) 1 ^ (-(3 : ℝ) / 2) * Real.exp (-(π * edgeF v))) * 1 :=
            mul_le_mul (hth2_bd (edgeF v) hx) hsq (sq_nonneg _) (by positivity)
        _ = Cθ * min (edgeF v - xiStar) 1 ^ (-(3 : ℝ) / 2) * Real.exp (-(π * edgeF v)) := mul_one _
        _ ≤ Cθ * m₀ ^ (-(3 / 2 : ℝ)) * Real.exp (-(π * v)) := by
            gcongr
            exact hmr.2
    have ht2 : |deriv thetaOutX (edgeF v)| * edgeF'' v ≤ (8 * π * C1) * Real.exp (-(π * v)) := by
      calc |deriv thetaOutX (edgeF v)| * edgeF'' v
          ≤ (Cθ * min (edgeF v - xiStar) 1 ^ (-(1 : ℝ) / 2) * Real.exp (-(π * edgeF v))) * (8 * π) :=
            mul_le_mul (hth1_bd (edgeF v) hx) h8 hF''.1.le (by positivity)
        _ ≤ (Cθ * m₀ ^ (-(1 / 2 : ℝ)) * Real.exp (-(π * v))) * (8 * π) := by
            gcongr
            exact hmr.1
        _ = (8 * π * C1) * Real.exp (-(π * v)) := by dsimp [C1]; ring
    dsimp [C2]; linarith
  have hFc : ContinuousOn F (Ici v₀) := fun v hv => (hhd1 v hv).continuousAt.continuousWithinAt
  have hF_norm : ∀ v, ‖F v‖ = 1 := fun v => Complex.norm_exp_I_mul_ofReal _
  have hF2_meas : AEStronglyMeasurable F2 (volume.restrict (Ioi v₀)) := by
    have hm_th1 : Measurable (deriv thetaOutX) := measurable_deriv _
    have hm_th2 : Measurable (deriv (deriv thetaOutX)) := measurable_deriv _
    have hm_F : Measurable edgeF := (continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt).measurable
    have hm_F' : Measurable edgeF' := (continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt).measurable
    have hm_F'' : Measurable edgeF'' := (continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt).measurable
    have hm_ph1 : Measurable ph1 := (hm_th1.comp hm_F).mul hm_F'
    have hm_ph2 : Measurable ph2 := ((hm_th2.comp hm_F).mul (hm_F'.pow_const 2)).add ((hm_th1.comp hm_F).mul hm_F'')
    have hF_m : AEStronglyMeasurable F (volume.restrict (Ioi v₀)) :=
      (hFc.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self
    have hm_pre : Measurable (fun v => Complex.I * (ph2 v : ℂ) - ((ph1 v ^ 2 : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.measurable.comp hm_ph2).const_mul Complex.I).sub
        (Complex.continuous_ofReal.measurable.comp (hm_ph1.pow_const 2))
    exact hm_pre.aestronglyMeasurable.mul hF_m
  refine ⟨F1, F2, ⟨OscAmpBound.ofExpDecay hv₀.le hhd1 hhd2 hF2_meas 1 C1 K2 π zero_le_one
    (by positivity) (by positivity) Real.pi_pos
    (fun v _ => (hF_norm v).le)
    (fun v hv => by
      dsimp [F1]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hF_norm, mul_one]
      exact hbd_ph1 v hv)
    (fun v hv => by
      have hexp1 : Real.exp (-(π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv₀.le.trans hv])
      dsimp [F2]
      rw [norm_mul, hF_norm, mul_one]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_sq]
      have hsq : ph1 v ^ 2 ≤ C1 ^ 2 * Real.exp (-(π * v)) := by
        calc ph1 v ^ 2 = |ph1 v| ^ 2 := (sq_abs _).symm
          _ ≤ (C1 * Real.exp (-(π * v))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbd_ph1 v hv) 2
          _ = C1 ^ 2 * Real.exp (-(π * v)) * Real.exp (-(π * v)) := by ring
          _ ≤ C1 ^ 2 * 1 * Real.exp (-(π * v)) := by gcongr
          _ = C1 ^ 2 * Real.exp (-(π * v)) := by ring
      calc |ph2 v| + ph1 v ^ 2 ≤ C2 * Real.exp (-(π * v)) + C1 ^ 2 * Real.exp (-(π * v)) :=
            add_le_add (hbd_ph2 v hv) hsq
        _ = K2 * Real.exp (-(π * v)) := by dsimp [K2]; ring)⟩⟩

/-- `1 - exp(-4π F(v))` satisfies `OscAmpBound` on `[v₀, ∞)`. -/
lemma oneSubExp_oscAmpBound {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ F1 F2 : ℝ → ℂ,
      Nonempty (OscAmpBound v₀ (fun v => ((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)) F1 F2) := by
  let f : ℝ → ℂ := fun v => ((1 - Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)
  let f1 : ℝ → ℂ := fun v => ((4 * π * edgeF' v * Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)
  let f2 : ℝ → ℂ := fun v => ((4 * π * (edgeF'' v - 4 * π * edgeF' v ^ 2) * Real.exp (-(4 * π * edgeF v)) : ℝ) : ℂ)
  have hd1 : ∀ v ∈ Ici v₀, HasDerivAt f (f1 v) v := fun v _ => by
    have h := (hasDerivAt_const v (1 : ℝ)).sub (((hasDerivAt_edgeF v).const_mul (4 * π)).neg.exp)
    exact h.ofReal_comp.congr_deriv (by dsimp [f1]; push_cast; ring)
  have hd2 : ∀ v ∈ Ici v₀, HasDerivAt f1 (f2 v) v := fun v _ => by
    have h1 := ((hasDerivAt_edgeF' v).const_mul (4 * π)).mul (((hasDerivAt_edgeF v).const_mul (4 * π)).neg.exp)
    exact h1.ofReal_comp.congr_deriv (by dsimp [f2]; push_cast; ring)
  let C2 : ℝ := 4 * π * (8 * π + 4 * π)
  have hexp_le : ∀ v ∈ Ici v₀, Real.exp (-(4 * π * edgeF v)) ≤ Real.exp (-(4 * π * v)) := fun v _ =>
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (v_lt_edgeF v).le (by positivity)))
  have hf2_c : ContinuousOn f2 (Ici v₀) := by
    have hF_c : Continuous edgeF := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt
    have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
    have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
    have hc : Continuous f2 := Complex.continuous_ofReal.comp
      (((continuous_const.mul (hF''_c.sub (continuous_const.mul (hF'_c.pow 2))))).mul
        (Real.continuous_exp.comp (continuous_const.mul hF_c).neg))
    exact hc.continuousOn
  refine ⟨f1, f2, ⟨OscAmpBound.ofExpDecay hv₀.le hd1 hd2
    ((hf2_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
    1 (4 * π) C2 (4 * π) zero_le_one (by positivity) (by positivity) (by positivity)
    (fun v hv => by
      have hpos : 0 ≤ 4 * π * edgeF v := by
        have hv_nn : 0 ≤ edgeF v := (hv₀.le.trans hv).trans (v_lt_edgeF v).le
        positivity
      have hex1 : Real.exp (-(4 * π * edgeF v)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpos)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith [Real.exp_pos (-(4 * π * edgeF v))])
    (fun v hv => by
      have hF' := edgeF'_v_bounds hv₀ hv
      have hF'nn : 0 ≤ edgeF' v := (edgeF'_pos (hv₀.trans_le hv)).le
      dsimp [f1]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc 4 * π * edgeF' v * Real.exp (-(4 * π * edgeF v))
          ≤ 4 * π * 1 * Real.exp (-(4 * π * v)) := by gcongr; exact hF'.2.le; exact (v_lt_edgeF v).le
        _ = (4 * π) * Real.exp (-(4 * π * v)) := by ring)
    (fun v hv => by
      have hF' := edgeF'_v_bounds hv₀ hv
      have hF'nn : 0 ≤ edgeF' v := (edgeF'_pos (hv₀.trans_le hv)).le
      have hF'' := edgeF''_bound (hv₀.le.trans hv)
      have h8 : edgeF'' v ≤ 8 * π := by
        have hex1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv₀.le.trans hv])
        nlinarith [hF''.2, Real.pi_pos]
      dsimp [f2]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_pos (by positivity : 0 < 4 * π)]
      have hdiff : |edgeF'' v - 4 * π * edgeF' v ^ 2| ≤ 8 * π + 4 * π := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos hF''.1, abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg (edgeF' v)))]
        have hF'sq : edgeF' v ^ 2 ≤ 1 := by nlinarith [hF'.1, hF'.2, edgeF'_pos (hv₀.trans_le hv)]
        nlinarith [Real.pi_pos]
      calc 4 * π * |edgeF'' v - 4 * π * edgeF' v ^ 2| * Real.exp (-(4 * π * edgeF v))
          ≤ 4 * π * (8 * π + 4 * π) * Real.exp (-(4 * π * v)) := by gcongr; exact (v_lt_edgeF v).le
        _ = C2 * Real.exp (-(4 * π * v)) := rfl)⟩⟩

/-- `√(edgeF' v)` satisfies `OscAmpBound` on `[v₀, ∞)`. -/
lemma sqrtEdgeF'_oscAmpBound {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ F1 F2 : ℝ → ℂ,
      Nonempty (OscAmpBound v₀ (fun v => (√(edgeF' v) : ℂ)) F1 F2) := by
  have hF'₀ : 0 < edgeF' v₀ := edgeF'_pos hv₀
  let s1 : ℝ → ℝ := fun v => edgeF'' v / (2 * √(edgeF' v))
  let s2 : ℝ → ℝ := fun v =>
    (edgeF''' v * (2 * √(edgeF' v)) - edgeF'' v * (2 * s1 v)) / (2 * √(edgeF' v)) ^ 2
  let f1 : ℝ → ℂ := fun v => (s1 v : ℂ)
  let f2 : ℝ → ℂ := fun v => (s2 v : ℂ)
  have hd1 : ∀ v ∈ Ici v₀, HasDerivAt (fun t => (√(edgeF' t) : ℂ)) (f1 v) v := fun v hv => by
    have hpos := hF'₀.trans_le (edgeF'_v_bounds hv₀ hv).1
    exact ((hasDerivAt_edgeF' v).sqrt hpos.ne').ofReal_comp
  have hd2 : ∀ v ∈ Ici v₀, HasDerivAt f1 (f2 v) v := fun v hv => by
    have hpos := hF'₀.trans_le (edgeF'_v_bounds hv₀ hv).1
    have hsf := (hasDerivAt_edgeF' v).sqrt hpos.ne'
    have hden := hsf.const_mul (2 : ℝ)
    have hne : 2 * √(edgeF' v) ≠ 0 := by positivity
    exact ((hasDerivAt_edgeF'' v).div hden hne).ofReal_comp
  let C1 : ℝ := (8 * π) / (2 * √(edgeF' v₀))
  let C2 : ℝ := (16 * π ^ 2 * 2 + (8 * π) ^ 2 / √(edgeF' v₀)) / (4 * edgeF' v₀)
  have hf2_c : ContinuousOn f2 (Ici v₀) := by
    have hF'_c : Continuous edgeF' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF' v).continuousAt
    have hF''_c : Continuous edgeF'' := continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF'' v).continuousAt
    have hF'''_c : Continuous edgeF''' := by
      unfold edgeF'''
      apply Continuous.div
      · continuity
      · exact ((continuous_const.add ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow 2)).rpow_const
          (fun x => Or.inl (by positivity : 1 + Real.cosh (π * x) ^ 2 ≠ 0)))
      · intro t; exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    have hsf_c : ContinuousOn (fun v => √(edgeF' v)) (Ici v₀) := (Real.continuous_sqrt.comp hF'_c).continuousOn
    have hs1_c : ContinuousOn s1 (Ici v₀) := hF''_c.continuousOn.div (continuousOn_const.mul hsf_c)
      (fun v hv => by have := hF'₀.trans_le (edgeF'_v_bounds hv₀ hv).1; positivity)
    have hs2_c : ContinuousOn s2 (Ici v₀) :=
      ((hF'''_c.continuousOn.mul (continuousOn_const.mul hsf_c)).sub
        (hF''_c.continuousOn.mul (continuousOn_const.mul hs1_c))).div
        ((continuousOn_const.mul hsf_c).pow 2) (fun v hv => by
          have := hF'₀.trans_le (edgeF'_v_bounds hv₀ hv).1; positivity)
    exact Complex.continuous_ofReal.comp_continuousOn hs2_c
  refine ⟨f1, f2, ⟨OscAmpBound.ofExpDecay hv₀.le hd1 hd2
    ((hf2_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self)
    1 C1 C2 (2 * π) zero_le_one (by positivity) (by positivity) (by positivity)
    (fun v hv => by
      have hF' := edgeF'_v_bounds hv₀ hv
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr hF'.2.le)
    (fun v hv => by
      have hF' := edgeF'_v_bounds hv₀ hv
      have hpos := hF'₀.trans_le hF'.1
      have hF'' := edgeF''_bound (hv₀.le.trans hv)
      dsimp [f1, s1]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hF''.1.le (by positivity))]
      have hsq : √(edgeF' v₀) ≤ √(edgeF' v) := Real.sqrt_le_sqrt hF'.1
      have hnum : edgeF'' v ≤ 8 * π * Real.exp (-(2 * π * v)) := hF''.2
      calc edgeF'' v / (2 * √(edgeF' v)) ≤ (8 * π * Real.exp (-(2 * π * v))) / (2 * √(edgeF' v₀)) :=
            div_le_div₀ (by positivity) hnum (by positivity) (by gcongr)
        _ = C1 * Real.exp (-(2 * π * v)) := by dsimp [C1]; ring)
    (fun v hv => by
      have hF' := edgeF'_v_bounds hv₀ hv
      have hpos := hF'₀.trans_le hF'.1
      have hF'' := edgeF''_bound (hv₀.le.trans hv)
      have hF''' := edgeF'''_bound (hv₀.le.trans hv)
      have hs_le1 : √(edgeF' v) ≤ 1 := Real.sqrt_le_one.mpr hF'.2.le
      have hs_ge : √(edgeF' v₀) ≤ √(edgeF' v) := Real.sqrt_le_sqrt hF'.1
      have h8 : edgeF'' v ≤ 8 * π := by
        have hex1 : Real.exp (-(2 * π * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hv₀.le.trans hv])
        nlinarith [hF''.2, Real.pi_pos]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
      have hden_eq : |(2 * √(edgeF' v)) ^ 2| = 4 * edgeF' v := by
        rw [abs_of_nonneg (sq_nonneg _), mul_pow, Real.sq_sqrt hpos.le]; ring
      rw [hden_eq]
      have hnum : |edgeF''' v * (2 * √(edgeF' v)) - edgeF'' v * (2 * (edgeF'' v / (2 * √(edgeF' v))))| ≤
          (16 * π ^ 2 * 2 + (8 * π) ^ 2 / √(edgeF' v₀)) * Real.exp (-(2 * π * v)) := by
        refine (abs_sub _ _).trans ?_
        have hn1 : 0 ≤ 2 * √(edgeF' v) := mul_nonneg two_pos.le (Real.sqrt_nonneg _)
        have hn2 : 0 ≤ 2 * (edgeF'' v / (2 * √(edgeF' v))) :=
          mul_nonneg two_pos.le (div_nonneg hF''.1.le hn1)
        rw [abs_mul, abs_of_nonneg hn1, abs_mul, abs_of_pos hF''.1, abs_of_nonneg hn2]
        have ht1 : |edgeF''' v| * (2 * √(edgeF' v)) ≤ 16 * π ^ 2 * Real.exp (-(2 * π * v)) * 2 := by
          gcongr; linarith
        have ht2 : edgeF'' v * (2 * (edgeF'' v / (2 * √(edgeF' v)))) ≤
            ((8 * π) ^ 2 / √(edgeF' v₀)) * Real.exp (-(2 * π * v)) := by
          have hsimpl : 2 * (edgeF'' v / (2 * √(edgeF' v))) = edgeF'' v / √(edgeF' v) := by ring
          rw [hsimpl]
          have hdiv : edgeF'' v / √(edgeF' v) ≤ (8 * π * Real.exp (-(2 * π * v))) / √(edgeF' v₀) :=
            div_le_div₀ (by positivity) hF''.2 (Real.sqrt_pos.mpr hF'₀) hs_ge
          calc edgeF'' v * (edgeF'' v / √(edgeF' v))
              ≤ (8 * π) * ((8 * π * Real.exp (-(2 * π * v))) / √(edgeF' v₀)) :=
                mul_le_mul h8 hdiv (div_nonneg hF''.1.le (Real.sqrt_nonneg _)) (by positivity)
            _ = ((8 * π) ^ 2 / √(edgeF' v₀)) * Real.exp (-(2 * π * v)) := by ring
        linarith
      calc |edgeF''' v * (2 * √(edgeF' v)) - edgeF'' v * (2 * (edgeF'' v / (2 * √(edgeF' v))))| / (4 * edgeF' v)
          ≤ ((16 * π ^ 2 * 2 + (8 * π) ^ 2 / √(edgeF' v₀)) * Real.exp (-(2 * π * v))) / (4 * edgeF' v₀) := by
            gcongr; exact hF'.1
        _ = C2 * Real.exp (-(2 * π * v)) := by dsimp [C2]; ring)⟩⟩

/-- `(1 - 2 I v)⁻¹` satisfies `OscAmpBound` on `[v₀, ∞)` for `v₀ > 0`. -/
lemma auxInv_oscAmpBound {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ F1 F2 : ℝ → ℂ,
      Nonempty (OscAmpBound v₀ (fun v => ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) F1 F2) := by
  let d : ℝ → ℂ := fun v => (1 : ℂ) - 2 * Complex.I * (v : ℂ)
  let r : ℝ → ℂ := fun v => (d v)⁻¹
  let r1 : ℝ → ℂ := fun v => (2 * Complex.I) / d v ^ 2
  let r2 : ℝ → ℂ := fun v => (-8 : ℂ) / d v ^ 3
  have hd_ne : ∀ v : ℝ, d v ≠ 0 := fun v hz => by
    have hre : (d v).re = 1 := by dsimp [d]; simp
    rw [hz, Complex.zero_re] at hre; norm_num at hre
  have hd_norm : ∀ v : ℝ, ‖d v‖ ^ 2 = 1 + 4 * v ^ 2 := fun v => by
    dsimp [d]; rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have hd_ge1 : ∀ v : ℝ, 1 ≤ ‖d v‖ := fun v => by
    have hsq : 1 ≤ ‖d v‖ ^ 2 := by rw [hd_norm v]; linarith [sq_nonneg v]
    nlinarith [norm_nonneg (d v)]
  have hdd : ∀ v : ℝ, HasDerivAt d (-2 * Complex.I) v := fun v =>
    ((hasDerivAt_const v (1 : ℂ)).sub ((hasDerivAt_id v).ofReal_comp.const_mul (2 * Complex.I))).congr_deriv
      (by simp)
  have hr1_d : ∀ v ∈ Ici v₀, HasDerivAt r (r1 v) v := fun v _ =>
    ((hdd v).inv (hd_ne v)).congr_deriv (by dsimp [r1]; ring)
  have hr2_d : ∀ v ∈ Ici v₀, HasDerivAt r1 (r2 v) v := fun v _ => by
    have h := (hasDerivAt_const v (2 * Complex.I)).div ((hdd v).pow 2) (pow_ne_zero 2 (hd_ne v))
    refine h.congr_deriv ?_
    dsimp [r2]
    have hne := hd_ne v
    field_simp [hne]
    norm_num
  have hr1_bd : ∀ v : ℝ, ‖r1 v‖ ≤ 2 / (1 + 4 * v ^ 2) := fun v => by
    dsimp [r1]
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, show ‖(2 : ℂ)‖ = 2 by norm_num, norm_pow, hd_norm v]
  have hr2_bd : ∀ v : ℝ, ‖r2 v‖ ≤ 8 / (1 + 4 * v ^ 2) := fun v => by
    have h1 := hd_ge1 v
    have h3 : ‖d v‖ ^ 2 ≤ ‖d v‖ ^ 3 := by nlinarith
    dsimp [r2]
    rw [norm_div, norm_neg, show ‖(8 : ℂ)‖ = 8 by norm_num, norm_pow]
    calc 8 / ‖d v‖ ^ 3 ≤ 8 / ‖d v‖ ^ 2 := by gcongr
      _ = 8 / (1 + 4 * v ^ 2) := by rw [hd_norm v]
  have hwt_deriv : ∀ v ∈ Ici v₀, HasDerivAt (fun t : ℝ => Real.arctan (2 * t)) (2 / (1 + 4 * v ^ 2)) v := fun v _ => by
    have h := ((hasDerivAt_id v).const_mul 2).arctan
    refine h.congr_deriv ?_
    simp [mul_pow]; ring
  have hwt_tend : Tendsto (fun t : ℝ => Real.arctan (2 * t)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_id.const_mul_atTop zero_lt_two)).mono_right nhdsWithin_le_nhds
  have hwt_i := integrableOn_Ioi_deriv_of_nonneg' hwt_deriv (fun v _ => by positivity) hwt_tend
  have hwt_int := integral_Ioi_of_hasDerivAt_of_nonneg' hwt_deriv (fun v _ => by positivity) hwt_tend
  have hwt_int_bd : ∫ v in Ioi v₀, 2 / (1 + 4 * v ^ 2) ≤ π / 2 := by
    rw [hwt_int]
    have h0 : 0 ≤ Real.arctan (2 * v₀) := Real.arctan_nonneg.mpr (by linarith)
    linarith
  have hr1_c : ContinuousOn r1 (Ici v₀) := fun v hv => (hr2_d v hv).continuousAt.continuousWithinAt
  have hr2_c : ContinuousOn r2 (Ici v₀) := by
    have hd_c : Continuous d := by dsimp [d]; continuity
    exact continuousOn_const.div (hd_c.continuousOn.pow 3) (fun v _ => pow_ne_zero 3 (hd_ne v))
  have hi1 : IntegrableOn r1 (Ioi v₀) := by
    refine hwt_i.mono' ((hr1_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    exact hr1_bd v
  have hi2 : IntegrableOn r2 (Ioi v₀) := by
    refine (hwt_i.const_mul 4).mono' ((hr2_c.aestronglyMeasurable measurableSet_Ici).mono_set Ioi_subset_Ici_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
    calc ‖r2 v‖ ≤ 8 / (1 + 4 * v ^ 2) := hr2_bd v
      _ = 4 * (2 / (1 + 4 * v ^ 2)) := by ring
  refine ⟨r1, r2, ⟨{
    hd1 := hr1_d
    hd2 := hr2_d
    K0 := 1
    K1 := 2
    K2 := 8
    L1 := π / 2
    L2 := 2 * π
    hK0 := zero_le_one
    hK1 := by norm_num
    hK2 := by norm_num
    hL1 := by positivity
    hL2 := by positivity
    b0 := fun v _ => by rw [norm_inv]; exact inv_le_one_of_one_le₀ (hd_ge1 v)
    b1 := fun v _ => (hr1_bd v).trans (div_le_self (by norm_num) (by linarith [sq_nonneg v]))
    b2 := fun v _ => (hr2_bd v).trans (div_le_self (by norm_num) (by linarith [sq_nonneg v]))
    i1 := hi1
    int1 := by
      calc ∫ v in Ioi v₀, ‖r1 v‖ ≤ ∫ v in Ioi v₀, 2 / (1 + 4 * v ^ 2) :=
            integral_mono_ae hi1.norm hwt_i ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => hr1_bd v)
        _ ≤ π / 2 := hwt_int_bd
    i2 := hi2
    int2 := by
      calc ∫ v in Ioi v₀, ‖r2 v‖ ≤ ∫ v in Ioi v₀, 4 * (2 / (1 + 4 * v ^ 2)) :=
            integral_mono_ae hi2.norm (hwt_i.const_mul 4)
              ((ae_restrict_mem measurableSet_Ioi).mono fun v _ =>
                (hr2_bd v).trans (le_of_eq (by ring)))
        _ = 4 * ∫ v in Ioi v₀, 2 / (1 + 4 * v ^ 2) := integral_const_mul 4 _
        _ ≤ 4 * (π / 2) := mul_le_mul_of_nonneg_left hwt_int_bd (by norm_num)
        _ = 2 * π := by ring
  }⟩⟩

end
end FormalResearch.ModularBootstrap.FiveTerm

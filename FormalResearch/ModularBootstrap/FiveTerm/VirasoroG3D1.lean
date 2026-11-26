module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3RegIbp
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Elem2
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3XbCauchy

/-!
# The slope `d₁` of the quotient amplitude `b = (a - a(0))/sinh²(πt)` (FIVE-0b)

`d₁ = ∫_ℝ (b - b(0)) π cosh/sinh² = (2/3)(-73π/128 + 5√2 A/4 + 5√2/64 + √2/(4π²))`, `A = arsinh 1`.
Route: the regularised integration by parts of `VirasoroG3RegIbp`, the decomposition
`a'/sinh³ = E/8 + T/sinh²` into the third-order strip integrand `E` of `VirasoroG3XbCauchy` (zero mean) and
elementary pieces (`VirasoroG3Elem1/2`), and the matching of the `1/sinh(πδ)` pole against `b(0)`.
Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `P = √2 (π²/2 + 4)/π² = -Ψ'(1)/π`. -/
noncomputable def P3 : ℝ := √2 * (π ^ 2 / 2 + 4) / π ^ 2

/-- The third-order strip integrand. -/
noncomputable def Efun (B t : ℝ) : ℝ :=
  (xA t + vA t - 2 * π / Real.cosh (π * t) + √2 / Real.cosh (π * t / 2) + 2 * B * Real.cosh (π * t) -
    P3 * (Real.sinh (π * t) * Real.sinh (π * t / 2))) / Real.sinh (π * t) ^ 2

/-- The elementary part of `a'/sinh³`. -/
noncomputable def Tfun (B t : ℝ) : ℝ :=
  (3 * π / 4) * qA t - (√2 / 8) * qB t - (B / 4) * kern t + (P3 / 16) * qD t + (11 * π / 8) * qE t -
    (2 * π) * qF t + (5 / 8) * qG t

lemma one_add_cosh (t : ℝ) : 1 + Real.cosh (π * t) = 2 * Real.cosh (π * t / 2) ^ 2 := by
  rw [cosh_double t]; ring

lemma aD_decomp (B : ℝ) {t : ℝ} (ht : 0 < t) :
    aD t / Real.sinh (π * t) ^ 3 = Efun B t / 8 + Tfun B t := by
  have hpi := Real.pi_pos
  have h := aD_div ht.ne'
  have hs := sinh_pos_of_pos ht
  have e : aD t / Real.sinh (π * t) ^ 3 = (aD t / Real.sinh (π * t)) / Real.sinh (π * t) ^ 2 := by
    field_simp
  rw [e, h]
  have hsh := sinh2_pos_of_pos ht
  have hch := Real.cosh_pos (π * t / 2)
  have hc := Real.cosh_pos (π * t)
  have h4 := Real.cosh_pos (π * t / 4)
  have hx := xT_pos t
  unfold Efun Tfun qA qB qD qE qF qG kern g4 g5 P3
  rw [sinh_double t, one_add_cosh t]
  have hq : 0 < √(Real.cosh (π * t) * (2 * Real.cosh (π * t / 2) ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  have hs' : 0 < Real.sinh (π * t / 2) * Real.cosh (π * t / 2) := by positivity
  field_simp
  ring

/-- `1/(2√2π)(-√2 + √2/2 - (5/2) arsinh 1)`, the limit of `QF`. -/
noncomputable def Finf : ℝ := (-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π)

/-- The primitive of `Tfun`. -/
noncomputable def PhiT (B t : ℝ) : ℝ :=
  (3 * π / 4) * QA t - (√2 / 8) * QB t - (B / 4) * QC t + (P3 / 16) * QD t + (11 * π / 8) * QE t -
    (2 * π) * QF t + (5 / 8) * QG t

/-- The limit of `PhiT` at `∞`. -/
noncomputable def PhiInf (B : ℝ) : ℝ :=
  (3 * π / 4) * (-1 / 2) - (√2 / 8) * (-3 / 8) - (B / 4) * 0 + (P3 / 16) * 1 +
    (11 * π / 8) * (-2 / (3 * π)) - (2 * π) * Finf + (5 / 8) * (2 / 3 - 5 * π / 16)

lemma hasDerivAt_PhiT (B : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (PhiT B) (Tfun B t) t := by
  have h1 := (hasDerivAt_QA ht).const_mul (3 * π / 4)
  have h2 := (hasDerivAt_QB ht).const_mul (√2 / 8)
  have h3 := (hasDerivAt_QC ht).const_mul (B / 4)
  have h4 := (hasDerivAt_QD t).const_mul (P3 / 16)
  have h5 := (hasDerivAt_QE ht).const_mul (11 * π / 8)
  have h6 := (hasDerivAt_QF ht).const_mul (2 * π)
  have h7 := (hasDerivAt_QG ht).const_mul (5 / 8)
  have h := ((((h1.fun_sub h2).fun_sub h3).fun_add h4).fun_add h5).fun_sub h6
  exact h.fun_add h7

lemma tendsto_PhiT (B : ℝ) : Tendsto (PhiT B) atTop (𝓝 (PhiInf B)) := by
  have h1 := tendsto_QA.const_mul (3 * π / 4)
  have h2 := tendsto_QB.const_mul (√2 / 8)
  have h3 := tendsto_QC.const_mul (B / 4)
  have h4 := tendsto_QD.const_mul (P3 / 16)
  have h5 := tendsto_QE.const_mul (11 * π / 8)
  have h6 := tendsto_QF.const_mul (2 * π)
  have h7 := tendsto_QG.const_mul (5 / 8)
  exact (((((h1.sub h2).sub h3).add h4).add h5).sub h6).add h7

lemma integrableOn_Tfun (B : ℝ) {δ : ℝ} (hδ : 0 < δ) : IntegrableOn (Tfun B) (Ioi δ) := by
  have h1 := (int_qA hδ).1.const_mul (3 * π / 4)
  have h2 := (int_qB hδ).1.const_mul (√2 / 8)
  have h3 := (int_kern hδ).1.const_mul (B / 4)
  have h4 := (int_qD hδ).1.const_mul (P3 / 16)
  have h5 := (int_qE hδ).1.const_mul (11 * π / 8)
  have h6 := (int_qF hδ).1.const_mul (2 * π)
  have h7 := (int_qG hδ).1.const_mul (5 / 8)
  exact (((((h1.sub h2).sub h3).add h4).add h5).sub h6).add h7

lemma int_Tfun (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in Ioi δ, Tfun B t = PhiInf B - PhiT B δ := by
  refine integral_Ioi_of_hasDerivAt_of_tendsto' (fun x hx => hasDerivAt_PhiT B (lt_of_lt_of_le hδ hx))
    (integrableOn_Tfun B hδ) (tendsto_PhiT B)

/-- The coefficient of `1/sinh(πδ)` in `PhiT`. -/
noncomputable def kapT (B : ℝ) : ℝ :=
  (3 * π / 4) * (-1 / π) - (√2 / 8) * (-1 / π) - (B / 4) * (-1 / π) + (11 * π / 8) * (-1 / (2 * π)) -
    (2 * π) * (-1 / (√2 * π)) + (5 / 8) * (-1 / 4)

lemma sing_PhiT (B : ℝ) :
    Tendsto (fun δ : ℝ => PhiT B δ - kapT B * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have h1 := sing_QA.const_mul (3 * π / 4)
  have h2 := sing_QB.const_mul (√2 / 8)
  have h3 := sing_QC.const_mul (B / 4)
  have h4 := tendsto_QD_zero.const_mul (P3 / 16)
  have h5 := sing_QE.const_mul (11 * π / 8)
  have h6 := sing_QF.const_mul (2 * π)
  have h7 := sing_QG.const_mul (5 / 8)
  have h := (((((h1.sub h2).sub h3).add h4).add h5).sub h6).add h7
  have e : (3 * π / 4) * 0 - (√2 / 8) * 0 - (B / 4) * 0 + (P3 / 16) * 0 + (11 * π / 8) * 0 - (2 * π) * 0 +
      (5 / 8) * 0 = 0 := by ring
  rw [e] at h
  refine h.congr (fun δ => ?_)
  unfold PhiT kapT
  ring

lemma kern_neg (t : ℝ) : kern (-t) = kern t := by
  unfold kern; rw [mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]

lemma Efun_even (B t : ℝ) : Efun B (-t) = Efun B t := by
  unfold Efun
  rw [xA_even, vA_even, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq, neg_div, Real.cosh_neg,
    Real.sinh_neg]
  ring

/-- The closed form of the limit. -/
noncomputable def S0 : ℝ := -(73 * π / 128) + 5 * √2 * Real.arsinh 1 / 4 + 5 * √2 / 64 + √2 / (4 * π ^ 2)

lemma PhiInf_eq (B : ℝ) : PhiInf B = S0 := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold PhiInf S0 Finf P3
  field_simp
  ring_nf
  simp only [hs2]
  ring

/-- **The slope of the quotient amplitude.** -/
theorem d1_exists : ∃ b : ℝ → ℝ, Amp b ∧
    (∀ t : ℝ, t ≠ 0 → b t = (aAmp t - aAmp 0) / Real.sinh (π * t) ^ 2) ∧
    ∫ t : ℝ, (b t - b 0) * (π * kern t) = (2 / 3) * S0 := by
  have hpi := Real.pi_pos
  obtain ⟨b, hb, hab⟩ := amp_quot amp_aAmp
  refine ⟨b, hb, hab, ?_⟩
  obtain ⟨B, hEint, hE0⟩ := xb_third
  have hE : Integrable (Efun B) := hEint
  have hE0' : ∫ t : ℝ, Efun B t = 0 := hE0
  have hE0Ioi : ∫ t in Ioi (0 : ℝ), Efun B t = 0 := by
    have := integral_eq_two_Ioi (f := Efun B) (Efun_even B)
    rw [hE0'] at this; linarith
  -- integrability of a'/sinh³
  have hint : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun t => aD t / Real.sinh (π * t) ^ 3) (Ioi δ) := by
    intro δ hδ
    have h : IntegrableOn (fun t => Efun B t / 8 + Tfun B t) (Ioi δ) :=
      ((hE.integrableOn (s := Ioi δ)).div_const 8).add (integrableOn_Tfun B hδ)
    exact h.congr_fun (fun t ht => (aD_decomp B (lt_trans hδ ht)).symm) measurableSet_Ioi
  have hreg := fun (δ : ℝ) (hδ : 0 < δ) =>
    reg_ibp amp_aAmp (fun t _ => hasDerivAt_aAmp t) hab hint hδ
  -- the integral of a'/sinh³
  have hJ : ∀ δ : ℝ, 0 < δ → ∫ t in Ioi δ, aD t / Real.sinh (π * t) ^ 3 =
      (1 / 8) * (∫ t in Ioi δ, Efun B t) + (PhiInf B - PhiT B δ) := by
    intro δ hδ
    have hI1 : IntegrableOn (fun t => Efun B t / 8) (Ioi δ) := (hE.integrableOn (s := Ioi δ)).div_const 8
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => aD_decomp B (lt_trans hδ ht)),
      integral_add hI1 (integrableOn_Tfun B hδ), int_Tfun B hδ, integral_div]
    ring
  -- the three limits
  set f : ℝ → ℝ := fun t => (b t - b 0) * (π * kern t) with hf
  have hfI : Integrable f := integrable_slope_integrand hb
  have hfev : ∀ t, f (-t) = f t := by
    intro t; simp only [hf, hb.even, kern_neg]
  have hΘ := tendsto_setIntegral_Ioi hfI
  have hf2 : ∫ t : ℝ, f t = 2 * ∫ t in Ioi (0 : ℝ), f t := integral_eq_two_Ioi hfev
  have hEf := tendsto_setIntegral_Ioi hE
  rw [hE0Ioi] at hEf
  have hbq := tendsto_amp_quot_div hb
  have hsing := sing_PhiT B
  -- the pole coefficient
  set c : ℝ := -kapT B / 3 - 2 / 3 * b 0 with hc
  set L : ℝ := (∫ t in Ioi (0 : ℝ), f t) - 0 - PhiInf B / 3 + (1 / 3) * 0 - (1 / 3) * 0 with hL
  have hlim : Tendsto (fun δ : ℝ => c * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 L) := by
    have h := ((((hΘ.sub (hEf.const_mul (1 / 24))).sub (tendsto_const_nhds (x := PhiInf B / 3))).add
      (hsing.const_mul (1 / 3))).sub (hbq.const_mul (1 / 3)))
    have e : (∫ t in Ioi (0 : ℝ), f t) - 1 / 24 * 0 - PhiInf B / 3 + 1 / 3 * 0 - 1 / 3 * 0 = L := by
      rw [hL]; ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : 0 < δ := hδ
    have hs := sinh_pos_of_pos hδ0
    have := hreg δ hδ0
    rw [hJ δ hδ0] at this
    simp only [hf, hc]
    rw [this]
    field_simp
    ring
  have hc0 : c = 0 := coeff_zero hlim
  have hL0 : L = 0 := by
    have h0 : Tendsto (fun δ : ℝ => c * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
      simp only [hc0, zero_mul]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim h0
  rw [hf2]
  have : ∫ t in Ioi (0 : ℝ), f t = PhiInf B / 3 := by rw [hL] at hL0; linarith
  rw [this, PhiInf_eq]
  ring

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.d1_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.d1_exists

end FormalResearch.ModularBootstrap.FiveTerm

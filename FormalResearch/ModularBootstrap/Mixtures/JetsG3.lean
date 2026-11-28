module

public import FormalResearch.ModularBootstrap.Mixtures.JetsG1

/-!
# Cubic jet `g₃(w, A)` (`ctu:jets` (a)–(b), `ctu:g13A`)

Computes the regularized third-order quotient slope integrals `d₁(bLam)` and `d₁(bW)` via
`reg_ibp` and the elementary primitives of `FiveTerm/VirasoroG3Elem{1,2}`, defines `g₃(w, A)`
(`g3OutWA`) from the cubic Taylor jet of `log G_outer^{(w,A)}` along `𝓝[>] 0`, proves the exact
formula `g₃(w, A) = (7/3)(2w - 3) - 10/(9π) - 24 I₁(A)/π - 128 I₃(A)/(3π)` (`g3OutWA_eq`),
and records the `Q ≡ 1` specialization (`g3OutWA_one`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.Mixtures

/-! ### 1. Regularized quotient integral `d₁` for `lamLog` -/

lemma d1_lamLog_eq {b : ℝ → ℝ} (hb : Amp b)
    (hab : ∀ t : ℝ, t ≠ 0 → b t = (lamLog t - lamLog 0) / Real.sinh (π * t) ^ 2) :
    ∫ t : ℝ, (b t - b 0) * (π * kern t) =
      (2 / 3) * (-1 / 12 - π / 4 + 5 / (4 * √2) * Real.arsinh 1) := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hlam : Amp lamLog := amp_lamLog
  have hpt : ∀ t : ℝ, t ≠ 0 → (lD t / lamT t) / Real.sinh (π * t) ^ 3 =
      (π / 2) * qA t + (π / 2) * qE t - π * qF t := fun t ht => by
    have hsh : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
    have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
    have hp := piece_lam ht
    unfold qA qE qF
    have hmul : (lD t / lamT t) / Real.sinh (π * t) ^ 3 =
        (2 * (lD t / lamT t) / Real.sinh (π * t)) / (2 * Real.sinh (π * t) ^ 2) := by
      field_simp
    rw [hmul, hp]
    field_simp
  have hint : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun t => (lD t / lamT t) / Real.sinh (π * t) ^ 3)
      (Ioi δ) := fun δ hδ => by
    obtain ⟨hiA, _⟩ := int_qA hδ
    obtain ⟨hiE, _⟩ := int_qE hδ
    obtain ⟨hiF, _⟩ := int_qF hδ
    have hi : IntegrableOn (fun t => (π / 2) * qA t + (π / 2) * qE t - π * qF t) (Ioi δ) :=
      ((hiA.const_mul (π / 2)).add (hiE.const_mul (π / 2))).sub (hiF.const_mul π)
    exact hi.congr_fun (fun t ht => (hpt t (lt_trans hδ ht).ne').symm) measurableSet_Ioi
  let Φinf : ℝ := -1 / 12 - π / 4 + 5 / (4 * √2) * Real.arsinh 1
  let Φ : ℝ → ℝ := fun δ => (π / 2) * QA δ + (π / 2) * QE δ - π * QF δ
  have hΦ_eq : ∀ δ : ℝ, 0 < δ →
      ∫ t in Ioi δ, (lD t / lamT t) / Real.sinh (π * t) ^ 3 = Φinf - Φ δ := fun δ hδ => by
    obtain ⟨hiA, vA⟩ := int_qA hδ
    obtain ⟨hiE, vE⟩ := int_qE hδ
    obtain ⟨hiF, vF⟩ := int_qF hδ
    have hcon : ∫ t in Ioi δ, (lD t / lamT t) / Real.sinh (π * t) ^ 3 =
        ∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t - π * qF t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t (lt_trans hδ ht).ne'
    have hsub1 : ∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t) =
        (π / 2) * (-1 / 2 - QA δ) + (π / 2) * (-2 / (3 * π) - QE δ) := by
      calc ∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t)
          = (∫ t in Ioi δ, (π / 2) * qA t) + ∫ t in Ioi δ, (π / 2) * qE t :=
              integral_add (hiA.const_mul _) (hiE.const_mul _)
        _ = (π / 2) * (-1 / 2 - QA δ) + (π / 2) * (-2 / (3 * π) - QE δ) := by
              rw [integral_const_mul, integral_const_mul, vA, vE]
    have hsub2 : ∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t - π * qF t) =
        ((π / 2) * (-1 / 2 - QA δ) + (π / 2) * (-2 / (3 * π) - QE δ)) -
          π * ((-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π) - QF δ) := by
      calc ∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t - π * qF t)
          = (∫ t in Ioi δ, ((π / 2) * qA t + (π / 2) * qE t)) - ∫ t in Ioi δ, π * qF t :=
              integral_sub ((hiA.const_mul _).add (hiE.const_mul _)) (hiF.const_mul _)
        _ = _ := by rw [hsub1, integral_const_mul, vF]
    rw [hcon, hsub2]
    dsimp only [Φinf, Φ]
    have hmul' : ((π / 2) * (-1 / 2 - QA δ) + (π / 2) * (-2 / (3 * π) - QE δ)) -
          π * ((-√2 + √2 / 2 - 5 / 2 * Real.arsinh 1) / (2 * √2 * π) - QF δ) =
        (-1 / 12 - π / 4 + 5 / (4 * √2) * Real.arsinh 1) -
          ((π / 2) * QA δ + (π / 2) * QE δ - π * QF δ) := by
      field_simp
      ring
    exact hmul'
  have hibp_ev : ∀ δ : ℝ, 0 < δ →
      ∫ t in Ioi δ, (b t - b 0) * (π * kern t) =
        (1 / 3) * (Φinf - Φ δ) + (b δ / 3 - b 0) / Real.sinh (π * δ) := fun δ hδ => by
    rw [reg_ibp hlam (fun t _ => hasDerivAt_lamLog t) hab hint hδ, hΦ_eq δ hδ]
  let f : ℝ → ℝ := fun t => (b t - b 0) * (π * kern t)
  have hf_int : Integrable f := integrable_slope_integrand hb
  have hΘ := tendsto_setIntegral_Ioi hf_int
  have hbq := tendsto_amp_quot_div hb
  let c : ℝ := (1 / 3) * ((π / 2) * (-1 / π) + (π / 2) * (-1 / (2 * π)) - π * (-1 / (√2 * π))) -
      (-(2 / 3) * b 0)
  have hsing : Tendsto (fun δ : ℝ => (Φ δ - ((π / 2) * (-1 / π) + (π / 2) * (-1 / (2 * π)) -
      π * (-1 / (√2 * π))) * (Real.sinh (π * δ))⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((sing_QA.const_mul (π / 2)).add (sing_QE.const_mul (π / 2))).sub (sing_QF.const_mul π)
    have h0 : (π / 2 * (0 : ℝ) + π / 2 * 0 - π * 0) = 0 := by ring
    rw [h0] at h
    refine h.congr (fun δ => ?_)
    dsimp only [Φ]; ring
  set L : ℝ := (∫ t in Ioi (0 : ℝ), f t) - Φinf / 3 with hL
  have hlim : Tendsto (fun δ : ℝ => (-c) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 L) := by
    have h := ((hΘ.sub (tendsto_const_nhds (x := Φinf / 3))).add (hsing.const_mul (1 / 3))).sub
      (hbq.const_mul (1 / 3))
    have e : (∫ t in Ioi (0 : ℝ), f t) - Φinf / 3 + 1 / 3 * 0 - 1 / 3 * 0 = L := by rw [hL]; ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have h1 := hibp_ev δ hδ
    dsimp only [f] at h1 ⊢
    rw [h1]
    dsimp only [c]
    ring
  have hc0 : -c = 0 := coeff_zero hlim
  have hlim0 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 L) :=
    hlim.congr (fun δ => by rw [hc0, zero_mul])
  have hL0 : L = 0 := tendsto_nhds_unique hlim0 tendsto_const_nhds
  have hev : ∀ t : ℝ, f (-t) = f t := fun t => by dsimp only [f]; rw [hb.even, kern_neg]
  rw [show ∫ t : ℝ, (b t - b 0) * (π * kern t) = ∫ t : ℝ, f t from rfl,
    integral_eq_two_Ioi hev]
  have hIoi : ∫ t in Ioi (0 : ℝ), f t = Φinf / 3 := by rw [hL] at hL0; linarith
  rw [hIoi]
  dsimp only [Φinf]
  ring

/-! ### 2. Regularized quotient integral `d₁` for `aW` -/

lemma d1_aW_eq {b : ℝ → ℝ} (hb : Amp b)
    (hab : ∀ t : ℝ, t ≠ 0 → b t = (aW t - aW 0) / Real.sinh (π * t) ^ 2) :
    ∫ t : ℝ, (b t - b 0) * (π * kern t) =
      (2 / 3) * (-π / 2 + 5 * √2 / 16 + √2 / π ^ 2) := by
  have hpi := Real.pi_pos
  obtain ⟨B, hE_int, hE_val⟩ := xb_third
  have hE0Ioi : ∫ t in Ioi (0 : ℝ), (xA t + vA t - 2 * π / Real.cosh (π * t) +
      √2 / Real.cosh (π * t / 2) + 2 * B * Real.cosh (π * t) -
      √2 * (π ^ 2 / 2 + 4) / π ^ 2 * (Real.sinh (π * t) * Real.sinh (π * t / 2))) /
      Real.sinh (π * t) ^ 2 = 0 := by
    have hev : ∀ t : ℝ, Efun B (-t) = Efun B t := Efun_even B
    have htwo := integral_eq_two_Ioi hev
    change ∫ t : ℝ, Efun B t = 0 at hE_val
    rw [hE_val] at htwo
    change ∫ t in Ioi (0 : ℝ), Efun B t = 0
    linarith
  have hE_eq : (fun t : ℝ => Efun B t) = fun t : ℝ =>
      (xA t + vA t - 2 * π / Real.cosh (π * t) + √2 / Real.cosh (π * t / 2) + 2 * B * Real.cosh (π * t) -
        √2 * (π ^ 2 / 2 + 4) / π ^ 2 * (Real.sinh (π * t) * Real.sinh (π * t / 2))) /
        Real.sinh (π * t) ^ 2 := by
    ext t; unfold Efun P3; rfl
  have hE_int' : Integrable (Efun B) := by convert hE_int using 2
  have hE0Ioi' : ∫ t in Ioi (0 : ℝ), Efun B t = 0 := by convert hE0Ioi using 2
  have hpt : ∀ t : ℝ, t ≠ 0 →
      (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3 =
        Efun B t / 2 + π * qA t - (√2 / 2) * qB t - B * kern t + (P3 / 4) * qD t := fun t ht => by
    have hsh : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
    have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
    have hc2 : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
    have hpx := piece_x ht
    have hpb := piece_b ht
    have h1 : (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) = (xA t + vA t) / 2 := by
      linear_combination 4 * hpx + 4 * hpb
    have h2 : (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3 =
        (xA t + vA t) / (2 * Real.sinh (π * t) ^ 2) := by
      have : (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3 =
          ((xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t)) / Real.sinh (π * t) ^ 2 := by
        field_simp
      rw [this, h1]
      ring
    rw [h2]
    unfold Efun qA qB kern qD P3
    have hdbl : Real.sinh (π * t) = 2 * Real.sinh (π * t / 2) * Real.cosh (π * t / 2) := by
      simpa [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using Real.sinh_two_mul (π * t / 2)
    rw [hdbl]
    field_simp
    ring
  have hint : ∀ δ : ℝ, 0 < δ →
      IntegrableOn (fun t => (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3)
        (Ioi δ) := fun δ hδ => by
    obtain ⟨hiA, _⟩ := int_qA hδ
    obtain ⟨hiB, _⟩ := int_qB hδ
    obtain ⟨hiC, _⟩ := int_kern hδ
    obtain ⟨hiD, _⟩ := int_qD hδ
    have hiE : IntegrableOn (fun t => Efun B t / 2) (Ioi δ) := (hE_int'.integrableOn).div_const 2
    have hi : IntegrableOn (fun t => Efun B t / 2 + π * qA t - (√2 / 2) * qB t -
        B * kern t + (P3 / 4) * qD t) (Ioi δ) :=
      (((hiE.add (hiA.const_mul _)).sub (hiB.const_mul _)).sub (hiC.const_mul _)).add
        (hiD.const_mul _)
    exact hi.congr_fun (fun t ht => (hpt t (lt_trans hδ ht).ne').symm) measurableSet_Ioi
  let Φinf : ℝ := -π / 2 + 5 * √2 / 16 + √2 / π ^ 2
  let Φ : ℝ → ℝ := fun δ => π * QA δ - (√2 / 2) * QB δ - B * QC δ + (P3 / 4) * QD δ
  have hΦ_eq : ∀ δ : ℝ, 0 < δ →
      ∫ t in Ioi δ, (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3 =
        (∫ t in Ioi δ, Efun B t) / 2 + (Φinf - Φ δ) := fun δ hδ => by
    obtain ⟨hiA, valA⟩ := int_qA hδ
    obtain ⟨hiB, valB⟩ := int_qB hδ
    obtain ⟨hiC, valC⟩ := int_kern hδ
    obtain ⟨hiD, valD⟩ := int_qD hδ
    have hiE : IntegrableOn (fun t => Efun B t / 2) (Ioi δ) := (hE_int'.integrableOn).div_const 2
    have hcon : ∫ t in Ioi δ,
          (xD t / xT t + (vT t * vD t / bT t) / bT t) / Real.sinh (π * t) ^ 3 =
        ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t -
          B * kern t + (P3 / 4) * qD t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t (lt_trans hδ ht).ne'
    have h1 : ∫ t in Ioi δ, (Efun B t / 2 + π * qA t) =
        (∫ t in Ioi δ, Efun B t) / 2 + π * (-1 / 2 - QA δ) := by
      calc ∫ t in Ioi δ, (Efun B t / 2 + π * qA t)
          = (∫ t in Ioi δ, Efun B t / 2) + ∫ t in Ioi δ, π * qA t :=
              integral_add hiE (hiA.const_mul _)
        _ = _ := by rw [integral_div, integral_const_mul, valA]
    have h2 : ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t) =
        (∫ t in Ioi δ, Efun B t) / 2 + π * (-1 / 2 - QA δ) - (√2 / 2) * (-3 / 8 - QB δ) := by
      calc ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t)
          = (∫ t in Ioi δ, (Efun B t / 2 + π * qA t)) - ∫ t in Ioi δ, (√2 / 2) * qB t :=
              integral_sub (hiE.add (hiA.const_mul _)) (hiB.const_mul _)
        _ = _ := by rw [h1, integral_const_mul, valB]
    have h3 : ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t - B * kern t) =
        (∫ t in Ioi δ, Efun B t) / 2 + π * (-1 / 2 - QA δ) - (√2 / 2) * (-3 / 8 - QB δ) -
          B * (0 - QC δ) := by
      calc ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t - B * kern t)
          = (∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t)) -
              ∫ t in Ioi δ, B * kern t :=
              integral_sub ((hiE.add (hiA.const_mul _)).sub (hiB.const_mul _)) (hiC.const_mul _)
        _ = _ := by rw [h2, integral_const_mul, valC]
    have h4 : ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t -
          B * kern t + (P3 / 4) * qD t) =
        (∫ t in Ioi δ, Efun B t) / 2 + π * (-1 / 2 - QA δ) - (√2 / 2) * (-3 / 8 - QB δ) -
          B * (0 - QC δ) + (P3 / 4) * (1 - QD δ) := by
      calc ∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t -
              B * kern t + (P3 / 4) * qD t)
          = (∫ t in Ioi δ, (Efun B t / 2 + π * qA t - (√2 / 2) * qB t - B * kern t)) +
              ∫ t in Ioi δ, (P3 / 4) * qD t :=
              integral_add (((hiE.add (hiA.const_mul _)).sub (hiB.const_mul _)).sub
                (hiC.const_mul _)) (hiD.const_mul _)
        _ = _ := by rw [h3, integral_const_mul, valD]
    rw [hcon, h4]
    dsimp only [Φinf, Φ]
    unfold P3
    field_simp
    ring
  have hibp_ev : ∀ δ : ℝ, 0 < δ →
      ∫ t in Ioi δ, (b t - b 0) * (π * kern t) =
        (1 / 6) * (∫ t in Ioi δ, Efun B t) + (1 / 3) * (Φinf - Φ δ) +
          (b δ / 3 - b 0) / Real.sinh (π * δ) := fun δ hδ => by
    rw [reg_ibp amp_aW (fun t _ => hasDerivAt_aW t) hab hint hδ, hΦ_eq δ hδ]
    ring
  let f : ℝ → ℝ := fun t => (b t - b 0) * (π * kern t)
  have hf_int : Integrable f := integrable_slope_integrand hb
  have hΘ := tendsto_setIntegral_Ioi hf_int
  have hEf : Tendsto (fun δ => ∫ t in Ioi δ, Efun B t) (𝓝[>] 0) (𝓝 0) := by
    simpa [hE0Ioi'] using tendsto_setIntegral_Ioi hE_int'
  have hbq := tendsto_amp_quot_div hb
  let c₀ : ℝ := π * (-1 / π) - (√2 / 2) * (-1 / π) - B * (-1 / π)
  have hsing : Tendsto (fun δ : ℝ => Φ δ - c₀ * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h := (((sing_QA.const_mul π).sub (sing_QB.const_mul (√2 / 2))).sub
      (sing_QC.const_mul B)).add (tendsto_QD_zero.const_mul (P3 / 4))
    have h0 : (π * (0 : ℝ) - √2 / 2 * 0 - B * 0 + P3 / 4 * 0) = 0 := by ring
    rw [h0] at h
    refine h.congr (fun δ => ?_)
    dsimp only [Φ, c₀]; ring
  let c : ℝ := (1 / 3) * c₀ - (-(2 / 3) * b 0)
  set L : ℝ := (∫ t in Ioi (0 : ℝ), f t) - Φinf / 3 with hL
  have hlim : Tendsto (fun δ : ℝ => (-c) * (Real.sinh (π * δ))⁻¹) (𝓝[>] 0) (𝓝 L) := by
    have h := ((((hΘ.sub (hEf.const_mul (1 / 6))).sub (tendsto_const_nhds (x := Φinf / 3))).add
      (hsing.const_mul (1 / 3))).sub (hbq.const_mul (1 / 3)))
    have e : (∫ t in Ioi (0 : ℝ), f t) - 1 / 6 * 0 - Φinf / 3 + 1 / 3 * 0 - 1 / 3 * 0 = L := by
      rw [hL]; ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have h1 := hibp_ev δ hδ
    dsimp only [f] at h1 ⊢
    rw [h1]
    dsimp only [c, c₀]
    ring
  have hc0 : -c = 0 := coeff_zero hlim
  have hlim0 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 L) :=
    hlim.congr (fun δ => by rw [hc0, zero_mul])
  have hL0 : L = 0 := tendsto_nhds_unique hlim0 tendsto_const_nhds
  have hev : ∀ t : ℝ, f (-t) = f t := fun t => by dsimp only [f]; rw [hb.even, kern_neg]
  rw [show ∫ t : ℝ, (b t - b 0) * (π * kern t) = ∫ t : ℝ, f t from rfl,
    integral_eq_two_Ioi hev]
  have hIoi : ∫ t in Ioi (0 : ℝ), f t = Φinf / 3 := by rw [hL] at hL0; linarith
  rw [hIoi]
  dsimp only [Φinf]
  ring

/-! ### 3. Cubic jet of `log G_outer^{(w,A)}` and `g₃(w, A)` (`ctu:g13A`, `ctu:jets` (b)) -/

/-- Existence of the cubic Taylor jet of `log G_outer^{(w,A)}` along `𝓝[>] 0` with the explicit
first and third coefficients `g₁(w, A)` and `g₃(w, A)`. -/
theorem exists_jet_logGoutWAR {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ c2 : ℝ, Jet (𝓝[>] (0 : ℝ)) (logGoutWAR w A) 0 (g1OutWA w hw hA) c2
      ((7 / 3) * (2 * (w : ℝ) - 3) - 10 / (9 * π) - 24 * I1Amp A / π - 128 * I3Amp A / (3 * π)) := by
  have hpi := Real.pi_pos.ne'
  obtain ⟨bLam, bW, bA, hbLam, habLam, hbW, habW, _, _, c2, hJ⟩ := exists_jet_logGoutWAR_raw hw hA
  rw [d1_lamLog_eq hbLam habLam] at hJ
  rw [d1_aW_eq hbW habW] at hJ
  rw [g1OutWA_eq hw hA]
  refine ⟨c2, hJ.of_eq rfl rfl rfl ?_⟩
  have hw1 : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by simp [Nat.cast_sub hw]
  have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hw1]
  unfold g3Vir xiStar
  field_simp
  ring_nf
  rw [hsq2]
  ring

/-- Existence wrapper matching the quadratic and cubic Taylor coefficients of `log G_outer^{(w,A)}`. -/
lemma exists_jet_logGoutWA_pair {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ c : ℝ × ℝ, Jet (𝓝[>] (0 : ℝ)) (logGoutWAR w A) 0 (g1OutWA w hw hA) c.1 c.2 := by
  obtain ⟨c2, h⟩ := exists_jet_logGoutWAR hw hA
  exact ⟨(c2, _), h⟩

/-- The quadratic Taylor coefficient `g₂(w, A)` of `log G_outer^{(w,A)}` at `0`. -/
noncomputable def g2OutWA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) : ℝ :=
  (Classical.choose (exists_jet_logGoutWA_pair hw hA)).1

/-- The cubic Taylor coefficient `g₃(w, A) = (1/6)(log G_outer^{(w,A)})'''(0)` (`ctu:jets`). -/
noncomputable def g3OutWA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) : ℝ :=
  (Classical.choose (exists_jet_logGoutWA_pair hw hA)).2

/-- `log G_outer^{(w,A)}(x) = g₁ x + g₂ x² + g₃ x³ + o(x³)` along `𝓝[>] 0` (`ctu:jets`). -/
theorem jet_logGoutWAR {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    Jet (𝓝[>] (0 : ℝ)) (logGoutWAR w A) 0
      (g1OutWA w hw hA) (g2OutWA w hw hA) (g3OutWA w hw hA) :=
  Classical.choose_spec (exists_jet_logGoutWA_pair hw hA)

/-- Exact formula for `g₃(w, A)` (`ctu:g13A`, `ctu:jets` (b)):
`g₃(w, A) = (7/3)(2w - 3) - 10/(9π) - 24 I₁(A)/π - 128 I₃(A)/(3π)` for every `w ≥ 1`. -/
theorem g3OutWA_eq {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    g3OutWA w hw hA =
      (7 / 3) * (2 * (w : ℝ) - 3) - 10 / (9 * π) - 24 * I1Amp A / π - 128 * I3Amp A / (3 * π) := by
  obtain ⟨c2, h⟩ := exists_jet_logGoutWAR hw hA
  exact (Jet.unique (jet_logGoutWAR hw hA) h).2.2.2

/-- `Q ≡ 1` specialization (`ctu:jets` (b)): `g₃(w, 1) = (7/3)(2w - 3) - 10/(9π)`. -/
theorem g3OutWA_one {w : ℕ} (hw : 1 ≤ w) :
    g3OutWA w hw jetAmplitude_one = (7 / 3) * (2 * (w : ℝ) - 3) - 10 / (9 * π) := by
  rw [g3OutWA_eq hw jetAmplitude_one, I1Amp_one, I3Amp_one]
  ring

/-- Shifting `w ↦ w + 1` increases `c₀^* = α_tip g₁` by `2 α_tip = ξ_*/(2√2)` (`ctu:jets` (b)). -/
theorem c0Star_WA_succ {w : ℕ} (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    alphaTip * g1OutWA (w + 1) (Nat.le_add_left 1 w) hA - alphaTip * g1OutWA w hw hA =
      xiStar / (2 * √2) := by
  rw [g1OutWA_eq (Nat.le_add_left 1 w) hA, g1OutWA_eq hw hA]
  push_cast
  unfold alphaTip
  ring

end FormalResearch.ModularBootstrap.Mixtures

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.exists_jet_logGoutWAR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.exists_jet_logGoutWAR

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.g3OutWA_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.g3OutWA_eq

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.c0Star_WA_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.c0Star_WA_succ

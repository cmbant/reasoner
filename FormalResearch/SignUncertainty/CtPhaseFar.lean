module

public import Mathlib
public import FormalResearch.SignUncertainty.CtCfuInv
public import FormalResearch.SignUncertainty.UctStripSplit
public import FormalResearch.SignUncertainty.HankelBandAssembly

/-!
# `ct:phase-far-lem`: the outer-band phase at large `Δ`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:phase-far-lem`.  **Proved.**
For `x = Δ/c ≥ 1` and `τ₀ > 0` with `m(τ₀) = log(π² x)`:
`|τ₀ - 2π x| ≤ C x e^{-2π² x}` and `|Φ_Ph(τ₀; L) - (2π x - π/4)| ≤ C x e^{-2π² x}`.
The constant `π/4` comes from `∫_0^∞ y / sinh y dy = π²/4` (`integral_div_sinh`), proved here from
`y / sinh y = 2 ∑ y e^{-(2k+1)y}` and `∑ (2k+1)^{-2} = π²/8`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty.CtPhaseFar

lemma sinh_series {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ => 2 * y * Real.exp (-((2 * k + 1) * y))) (y / Real.sinh y) := by
  have hr0 : 0 ≤ Real.exp (-(2 * y)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(2 * y)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * y * Real.exp (-y))
  convert hg using 1
  · ext k
    rw [← Real.exp_nat_mul, show Real.exp (-((2 * k + 1) * y)) = Real.exp (-y) * Real.exp (k * -(2 * y)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  · have hs : Real.sinh y = (Real.exp y - Real.exp (-y)) / 2 := Real.sinh_eq y
    have hE : 0 < Real.exp (-y) := Real.exp_pos _
    have hlt : Real.exp (-y) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have h2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have hy' : Real.exp y = (Real.exp (-y))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [hs, h2, hy']
    generalize Real.exp (-y) = a at *
    have h1 : 1 - a * a ≠ 0 := by nlinarith
    have h1' : 1 - a ^ 2 ≠ 0 := by nlinarith
    have hne : a⁻¹ - a ≠ 0 := by
      intro h
      have : a⁻¹ = a := by linarith
      have h' : a * a = 1 := by field_simp at this; linarith
      exact h1 (by linarith)
    field_simp

lemma odd_sq_sum : HasSum (fun k : ℕ => 1 / ((2 * (k : ℝ) + 1)) ^ 2) (π ^ 2 / 8) := by
  have hz := hasSum_zeta_two
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hz.summable
  have hev : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
    have := hz.mul_left (1 / 4)
    convert this using 1
    · ext k
      by_cases hk : k = 0
      · simp [hk]
      · push_cast
        field_simp
        norm_num
    · ring
  have hod : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
      simp only [add_left_inj] at h; omega
    exact hs.comp_injective hinj
  have hsum := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) hev.summable hod
  rw [hev.tsum_eq, hz.tsum_eq] at hsum
  have h8 : ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
  have h3 := hod.hasSum
  rw [h8] at h3
  simpa using h3

lemma int_term (k : ℕ) :
    IntegrableOn (fun y : ℝ => 2 * y * Real.exp (-((2 * k + 1) * y))) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), 2 * y * Real.exp (-((2 * k + 1) * y)) = 2 / (2 * (k : ℝ) + 1) ^ 2 := by
  have hr : (0 : ℝ) < 2 * k + 1 := by positivity
  constructor
  · have hI : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(2 * k + 1) * x ^ (1 : ℝ)))
        (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 2 * k + 1)
        (by norm_num) one_pos hr
    refine IntegrableOn.congr_fun (hI.const_mul 2) (fun y _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]; ring_nf
  · have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 2 * k + 1) (by norm_num) hr
    have e : ∀ y : ℝ, 2 * y * Real.exp (-((2 * k + 1) * y)) =
        2 * (y ^ ((2 : ℝ) - 1) * Real.exp (-((2 * k + 1) * y))) := by
      intro y; norm_num [Real.rpow_one]; ring
    simp_rw [e]
    rw [integral_const_mul, h, Real.Gamma_two]
    rw [Real.rpow_two, one_div, inv_pow]
    ring

/-- `∫_0^∞ y / sinh y dy = π²/4`. -/
theorem integral_div_sinh : ∫ y in Ioi (0 : ℝ), y / Real.sinh y = π ^ 2 / 4 := by
  have hint : ∀ k : ℕ, Integrable (fun y : ℝ => 2 * y * Real.exp (-((2 * k + 1) * y)))
      (volume.restrict (Ioi 0)) := fun k => (int_term k).1
  have hnorm : ∀ k : ℕ, ∫ y in Ioi (0 : ℝ), ‖2 * y * Real.exp (-((2 * k + 1) * y))‖ =
      2 / (2 * (k : ℝ) + 1) ^ 2 := by
    intro k
    rw [← (int_term k).2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [Real.norm_of_nonneg]
    have : 0 < y := hy
    positivity
  have hsum : Summable (fun k : ℕ => ∫ y in Ioi (0 : ℝ), ‖2 * y * Real.exp (-((2 * k + 1) * y))‖) := by
    simp_rw [hnorm]
    have := odd_sq_sum.summable.mul_left 2
    convert this using 2 with k
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hT : ∫ y in Ioi (0 : ℝ), ∑' k : ℕ, 2 * y * Real.exp (-((2 * k + 1) * y)) =
      ∫ y in Ioi (0 : ℝ), y / Real.sinh y := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    exact (sinh_series hy).tsum_eq
  rw [hT] at h
  have h2 : HasSum (fun k : ℕ => 2 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 4) := by
    have := odd_sq_sum.mul_left 2
    convert this using 1
    · ext k; ring
    · ring
  refine h.unique ?_
  convert h2 using 1
  ext k
  exact (int_term k).2

/-- `sj y = y / sinh y`. -/
noncomputable def sj (y : ℝ) : ℝ := y / Real.sinh y

lemma sj_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ sj y :=
  div_nonneg hy (Real.sinh_nonneg_iff.mpr hy)

lemma sj_le {y : ℝ} (hy : 0 < y) : sj y ≤ 3 * (1 + y) * Real.exp (-y) := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  unfold sj
  rw [div_le_iff₀ hs]
  have ha : 0 < Real.exp (-y) := Real.exp_pos _
  have hya : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have key : Real.exp (-y) * Real.sinh y = (1 - Real.exp (-y) ^ 2) / 2 := by
    rw [Real.sinh_eq]; linear_combination (1 / 2) * hya
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hm1 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rcases lt_or_ge y 1 with h1 | h1
  · have hb : 1 / 3 ≤ Real.exp (-y) := by
      have : Real.exp (-1) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
      have h3 : 1 / 3 ≤ Real.exp (-1) := by
        rw [hm1]; rw [one_div]; exact inv_anti₀ (by positivity) he2.le
      linarith
    have h3 : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy.le
    calc y = 3 * 1 * (1 / 3) * y := by ring
      _ ≤ 3 * (1 + y) * Real.exp (-y) * Real.sinh y := by gcongr; linarith
  · have hb : Real.exp (-y) ≤ 1 / 2 := by
      have : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h3 : Real.exp (-1) ≤ 1 / 2 := by
        rw [hm1, one_div]; exact inv_anti₀ (by norm_num) he1
      linarith
    have hsq : Real.exp (-y) ^ 2 ≤ 1 / 4 := by nlinarith
    have h4 : 3 / 8 ≤ Real.exp (-y) * Real.sinh y := by rw [key]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 3 * (1 + y))]

lemma hasDerivAt_G (y : ℝ) :
    HasDerivAt (fun y : ℝ => -(3 * ((y + 2) * Real.exp (-y)))) (3 * (1 + y) * Real.exp (-y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y + 2) 1 y := (hasDerivAt_id y).add_const 2
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
    simpa using (hasDerivAt_neg y).exp
  refine (((h1.mul h2).const_mul 3).neg).congr_deriv ?_
  ring

lemma g_tendsto : Tendsto (fun y : ℝ => -(3 * ((y + 2) * Real.exp (-y)))) atTop (𝓝 0) := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
  have := ((h1.add (h2.const_mul 2)).const_mul (-3))
  simp only [pow_one, mul_zero, add_zero] at this
  refine this.congr fun y => ?_
  ring

lemma g_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun y : ℝ => 3 * (1 + y) * Real.exp (-y)) (Ioi T) ∧
    ∫ y in Ioi T, 3 * (1 + y) * Real.exp (-y) = 3 * ((T + 2) * Real.exp (-T)) := by
  have hpos : ∀ x ∈ Ioi T, 0 ≤ 3 * (1 + x) * Real.exp (-x) := fun x hx =>
    by have : T < x := hx; have hx0 : 0 ≤ x := by linarith
       positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_G x) hpos g_tendsto, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hasDerivAt_G x) hpos g_tendsto]
  ring

lemma sj_integrableOn {T : ℝ} (hT : 0 ≤ T) : IntegrableOn sj (Ioi T) := by
  refine Integrable.mono' (g_integrable hT).1 ?_ ?_
  · exact (measurable_id.div Real.continuous_sinh.measurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun y hy => ?_)
    have hy' : 0 < y := lt_of_le_of_lt hT hy
    rw [Real.norm_of_nonneg (sj_nonneg hy'.le)]
    exact sj_le hy'

lemma sj_intervalIntegrable {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable sj volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (sj_integrableOn le_rfl).mono_set Ioc_subset_Ioi_self

/-- The incomplete integral `∫_0^T y/sinh y dy` is within `3(T+2)e^{-T}` of `π²/4`. -/
theorem sj_tail {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ π ^ 2 / 4 - ∫ y in (0 : ℝ)..T, sj y ∧
    π ^ 2 / 4 - ∫ y in (0 : ℝ)..T, sj y ≤ 3 * ((T + 2) * Real.exp (-T)) := by
  have hsplit : ∫ y in Ioi (0 : ℝ), sj y = (∫ y in Ioc (0 : ℝ) T, sj y) + ∫ y in Ioi T, sj y := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((sj_integrableOn le_rfl).mono_set Ioc_subset_Ioi_self) (sj_integrableOn hT),
      Ioc_union_Ioi_eq_Ioi hT]
  have htot : ∫ y in Ioi (0 : ℝ), sj y = π ^ 2 / 4 := integral_div_sinh
  rw [intervalIntegral.integral_of_le hT]
  have htail : π ^ 2 / 4 - ∫ y in Ioc (0 : ℝ) T, sj y = ∫ y in Ioi T, sj y := by linarith
  rw [htail]
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun y hy => sj_nonneg (hT.trans hy.le), ?_⟩
  rw [← (g_integrable hT).2]
  refine setIntegral_mono_on (sj_integrableOn hT) (g_integrable hT).1 measurableSet_Ioi fun y hy => ?_
  exact sj_le (lt_of_le_of_lt hT hy)

lemma edgePhiDeriv_zero_eq {u : ℝ} (hu : 0 < u) : edgePhiDeriv 0 u = -hankelEdgeM u := by
  unfold edgePhiDeriv hankelEdgeM ceEll
  rw [if_neg hu.ne', abs_of_pos hu, zero_add, ← Real.log_inv, inv_div]

lemma mderiv_eq {u : ℝ} (hu : 0 < u) : u * uctMderiv u = 1 - sj (π * u) := by
  unfold uctMderiv uctEllDeriv sj
  have h1 : Real.sinh (2 * (π * u / 2)) = Real.sinh (π * u) := by ring_nf
  rw [h1]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have : 0 < Real.sinh (π * u) := Real.sinh_pos_iff.mpr (by positivity)
  field_simp

/-- `Φ_Ph(τ; m(τ)) = τ - π⁻¹ ∫_0^{πτ} y/sinh y dy`, i.e. `∫_0^τ u m'(u) du`. -/
theorem edgePhi_at_crit {τ : ℝ} (hτ : 0 ≤ τ) :
    edgePhi (hankelEdgeM τ) τ = τ - π⁻¹ * ∫ y in (0 : ℝ)..π * τ, sj y := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set P : ℝ → ℝ := fun u => u * hankelEdgeM u + edgePhi 0 u with hP
  have hEq : edgePhi (hankelEdgeM τ) τ = P τ := by simp only [hP, edgePhi]; ring
  have hP0 : P 0 = 0 := by simp [hP, hankelEdgeM_zero, edgePhi]
  have hint : IntervalIntegrable (fun u => sj (π * u)) volume 0 τ := by
    have := (sj_intervalIntegrable (by positivity : 0 ≤ π * τ)).comp_mul_left (c := π)
    simpa [hpi.ne'] using this
  have hftc : ∫ u in (0 : ℝ)..τ, (1 - sj (π * u)) = P τ - P 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ ?_ ?_ ?_
    · have h1 : ContinuousOn (fun u : ℝ => u * hankelEdgeM u) (Icc 0 τ) :=
        continuousOn_id.mul (hankelEdgeM_continuousOn.mono Icc_subset_Ici_self)
      exact h1.add continuous_edgePhi_zero.continuousOn
    · intro u hu
      have hu0 : 0 < u := hu.1
      have h1 := ((hasDerivAt_id u).mul (hankelEdgeM_hasDerivAt hu0))
      have h1' : HasDerivAt hankelEdgeM (uctMderiv u) u := hasDerivAt_uctM hu0
      have h2 := ((hasDerivAt_id u).mul h1').add (hasDerivAt_edgePhi 0 u)
      refine h2.congr_deriv ?_
      rw [edgePhiDeriv_zero_eq hu0]
      have := mderiv_eq hu0
      simp only [id]
      linarith
    · exact intervalIntegrable_const.sub hint
  have h3 := hftc
  rw [hP0, sub_zero, intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_comp_mul_left (fun y => sj y) hpi.ne'] at h3
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero, sub_zero, one_mul] at h3
  rw [hEq]
  linarith

lemma tanh_eq_exp (s : ℝ) : Real.tanh s = 1 - 2 / (Real.exp (2 * s) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hE : 0 < Real.exp s := Real.exp_pos _
  have h2 : Real.exp (2 * s) = Real.exp s * Real.exp s := by rw [← Real.exp_add]; ring_nf
  rw [Real.exp_neg, h2]
  have : 0 < Real.exp s * Real.exp s + 1 := by positivity
  field_simp
  ring

lemma tanh_ge {s : ℝ} (hs : 0 < s) : s / (s + 1) ≤ Real.tanh s := by
  rw [tanh_eq_exp, div_le_iff₀ (by linarith)]
  have h1 : 2 * s + 1 ≤ Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
  have hu : 0 < Real.exp (2 * s) + 1 := by positivity
  have : 2 / (Real.exp (2 * s) + 1) = 2 * (Real.exp (2 * s) + 1)⁻¹ := by ring
  have h3 : (1 - 2 / (Real.exp (2 * s) + 1)) * (s + 1) = ((Real.exp (2 * s) - 1) * (s + 1)) / (Real.exp (2 * s) + 1) := by
    field_simp; ring
  rw [h3, le_div_iff₀ hu]
  nlinarith

lemma crit_eq {x τ0 : ℝ} (hx : 0 < x) (hτ0 : 0 < τ0) (hm : hankelEdgeM τ0 = Real.log (π ^ 2 * x)) :
    τ0 = 2 * π * x * Real.tanh (π * τ0 / 2) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hs : 0 < π * τ0 / 2 := by positivity
  have ht : 0 < Real.tanh (π * τ0 / 2) := tanh_pos_of_pos hs
  unfold hankelEdgeM ceEll at hm
  have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos hs ht)) (Set.mem_Ioi.mpr (by positivity)) hm
  rw [div_eq_iff ht.ne'] at h
  have : π * (τ0 - 2 * π * x * Real.tanh (π * τ0 / 2)) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hpi.ne'
  · linarith

/-- Constant of `ct_phase_far`. -/
noncomputable def phaseFarK : ℝ := 16 * π * Real.exp 2

/-- **ct:phase-far-lem** (scaled form, `x = Δ/c ≥ 1`). If `τ₀ > 0` solves `m(τ₀) = log(π² x)` then
`|τ₀ - 2πx| ≤ K x e^{-2π²x}` and `|Φ_Ph(τ₀; L) - (2πx - π/4)| ≤ K x e^{-2π²x}`,
where `Φ_Ph(τ₀; L) = edgePhi L τ₀`. -/
theorem ct_phase_far {x : ℝ} (hx : 1 ≤ x) {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hm : hankelEdgeM τ0 = Real.log (π ^ 2 * x)) :
    |τ0 - 2 * π * x| ≤ phaseFarK * x * Real.exp (-(2 * π ^ 2 * x)) ∧
    |edgePhi (Real.log (π ^ 2 * x)) τ0 - (2 * π * x - π / 4)|
      ≤ phaseFarK * x * Real.exp (-(2 * π ^ 2 * x)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hx0 : 0 < x := by linarith
  have h1 := crit_eq hx0 hτ0 hm
  set s := π * τ0 / 2 with hsdef
  have hs : 0 < s := by positivity
  set t := Real.tanh s with htdef
  have ht0 : 0 < t := tanh_pos_of_pos hs
  have hsE : s = π ^ 2 * x * t := by rw [hsdef]; linear_combination (π / 2) * h1
  have hlow : π ^ 2 * x ≤ s + 1 := by
    have hg := tanh_ge hs
    rw [div_le_iff₀ (by linarith)] at hg
    have h2 : π ^ 2 * x * s ≤ (s + 1) * s := by
      calc π ^ 2 * x * s ≤ π ^ 2 * x * (t * (s + 1)) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ = (π ^ 2 * x * t) * (s + 1) := by ring
        _ = s * (s + 1) := by rw [← hsE]
        _ = (s + 1) * s := by ring
    exact le_of_mul_le_mul_right h2 hs
  have ht1 : t ≤ 1 := by
    have := tanh_eq_exp s
    have : 0 ≤ 2 / (Real.exp (2 * s) + 1) := by positivity
    linarith
  set ε := Real.exp (-(2 * π ^ 2 * x)) with hε
  have hε0 : 0 < ε := Real.exp_pos _
  have he2 : 0 < Real.exp 2 := Real.exp_pos _
  have hdiff : 1 - t ≤ 2 * (Real.exp 2 * ε) := by
    have h3 : 1 - t = 2 / (Real.exp (2 * s) + 1) := by rw [htdef, tanh_eq_exp]; ring
    have h4 : 2 / (Real.exp (2 * s) + 1) ≤ 2 / Real.exp (2 * s) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) (by linarith)
    have h5 : 2 / Real.exp (2 * s) = 2 * Real.exp (-(2 * s)) := by rw [Real.exp_neg]; ring
    have h6 : Real.exp (-(2 * s)) ≤ Real.exp 2 * ε := by
      rw [hε, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hτ2 : τ0 - 2 * π * x = -(2 * π * x * (1 - t)) := by rw [h1]; ring
  have hE1 : |τ0 - 2 * π * x| ≤ 4 * π * Real.exp 2 * x * ε := by
    have h1t : 0 ≤ 1 - t := by linarith
    have hnn : 0 ≤ 2 * π * x * (1 - t) := by positivity
    rw [hτ2, abs_neg, abs_of_nonneg hnn]
    calc 2 * π * x * (1 - t) ≤ 2 * π * x * (2 * (Real.exp 2 * ε)) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 4 * π * Real.exp 2 * x * ε := by ring
  have hK : 4 * π * Real.exp 2 * x * ε ≤ phaseFarK * x * ε := by
    unfold phaseFarK
    have : 0 ≤ Real.exp 2 * x * ε * π := by positivity
    nlinarith
  refine ⟨hE1.trans hK, ?_⟩
  -- second claim
  have hcrit := edgePhi_at_crit hτ0.le
  rw [hm] at hcrit
  rw [hcrit]
  obtain ⟨hr0, hr1⟩ := sj_tail (T := π * τ0) (by positivity)
  set R := ∫ y in (0 : ℝ)..π * τ0, sj y with hR
  set r := π ^ 2 / 4 - R with hr
  have hT : π * τ0 = 2 * s := by rw [hsdef]; ring
  have hTle : π * τ0 ≤ 2 * π ^ 2 * x := by
    have : t ≤ 1 := ht1
    have : π ^ 2 * x * t ≤ π ^ 2 * x := by nlinarith [sq_nonneg π, hx0]
    linarith
  have hTge : 2 * π ^ 2 * x - 2 ≤ π * τ0 := by linarith
  have hexpT : Real.exp (-(π * τ0)) ≤ Real.exp 2 * ε := by
    rw [hε, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hπ2 : (9 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hT2 : π * τ0 + 2 ≤ 4 * π ^ 2 * x := by nlinarith
  have hrb : r ≤ 3 * ((4 * π ^ 2 * x) * (Real.exp 2 * ε)) := by
    refine hr1.trans ?_
    gcongr
  have hr' : π⁻¹ * r ≤ 12 * π * Real.exp 2 * x * ε := by
    rw [inv_mul_le_iff₀ hpi]
    nlinarith
  have hr0' : 0 ≤ π⁻¹ * r := mul_nonneg (inv_nonneg.mpr hpi.le) hr0
  have hid : τ0 - π⁻¹ * R - (2 * π * x - π / 4) = (τ0 - 2 * π * x) + π⁻¹ * r := by
    rw [hr]; field_simp; ring
  rw [hid]
  have hE1' := abs_le.mp hE1
  rw [abs_le]
  unfold phaseFarK
  constructor <;> nlinarith [hE1'.1, hE1'.2, hr', hr0']

/-- **ct:phase-far-lem** in the variables of the paper (`Δ ≥ c > 0`, `L = log(π²Δ/c)`):
`|τ₀ - 2πΔ/c| ≤ K (Δ/c) e^{-2π²Δ/c}` and
`|c Φ_Ph(τ₀; L) - (2πΔ - πc/4)| ≤ K Δ e^{-2π²Δ/c}`. -/
theorem ct_phase_far_Delta {c Δ : ℝ} (hc : 0 < c) (hΔ : c ≤ Δ) {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hm : hankelEdgeM τ0 = Real.log (π ^ 2 * (Δ / c))) :
    |τ0 - 2 * π * Δ / c| ≤ phaseFarK * (Δ / c) * Real.exp (-(2 * π ^ 2 * Δ / c)) ∧
    |c * edgePhi (Real.log (π ^ 2 * (Δ / c))) τ0 - (2 * π * Δ - π * c / 4)|
      ≤ phaseFarK * Δ * Real.exp (-(2 * π ^ 2 * Δ / c)) := by
  have hx : 1 ≤ Δ / c := by rw [le_div_iff₀ hc]; linarith
  obtain ⟨h1, h2⟩ := ct_phase_far hx hτ0 hm
  have e : 2 * π ^ 2 * (Δ / c) = 2 * π ^ 2 * Δ / c := by ring
  rw [e] at h1 h2
  refine ⟨by rwa [show 2 * π * (Δ / c) = 2 * π * Δ / c by ring] at h1, ?_⟩
  have : c * edgePhi (Real.log (π ^ 2 * (Δ / c))) τ0 - (2 * π * Δ - π * c / 4) =
      c * (edgePhi (Real.log (π ^ 2 * (Δ / c))) τ0 - (2 * π * (Δ / c) - π / 4)) := by
    field_simp
  rw [this, abs_mul, abs_of_pos hc]
  calc c * |edgePhi (Real.log (π ^ 2 * (Δ / c))) τ0 - (2 * π * (Δ / c) - π / 4)|
      ≤ c * (phaseFarK * (Δ / c) * Real.exp (-(2 * π ^ 2 * Δ / c))) :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ = phaseFarK * Δ * Real.exp (-(2 * π ^ 2 * Δ / c)) := by field_simp

/-- info: 'FormalResearch.SignUncertainty.CtPhaseFar.integral_div_sinh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_div_sinh

/-- info: 'FormalResearch.SignUncertainty.CtPhaseFar.ct_phase_far_Delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_phase_far_Delta

end FormalResearch.SignUncertainty.CtPhaseFar

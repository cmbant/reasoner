module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCEnergyAiry

/-!
# Paper J, Layer 4 (phase B2, E3-link): `env_well` on the Airy zone `[z₁, z₂]`

For `a ≤ -4` (`A = -a ≥ 4`), on the Airy zone `[z₁(a), z₂(a)]`:
* `M_bal(a, z₁)` and `M_bal(a, z)` are comparable within `[2^{-1/2}, 2^{1/2}]` (`Mbal_airy_ratio`),
* `R₀(y, a, z)` and `y(z)^2 + y'(z)^2 / k₂(a, z)` are comparable within `[1/2, 1]` (`R0Airy_vs_k2`),
* `exp(-3) ≤ E_well(a, z) ≤ 1` (`Ewell_airy_bounds`),
* combining `PCEnergyAiry.R0Airy_bounds` with `PCEnergyWell.env_well_on_Icc_U_V` at `z = z₁(a)`
  yields two-sided `env_well` bounds on `[z₁(a), z₂(a)]` for `pcU` and `pcV` with explicit
  absolute constants `exp(-14)` and `exp(14)` (`env_well_on_airy_U_V`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Real

/-! ### Comparing `Mbal` and `R₀` with `k₂` on `[z₁, z₂]` -/

/-- On `[z₁(a), z₂(a)]` with `a ≤ -4`, `Mbal a (z1Well a)` and `Mbal a z` agree up to `sqrt 2`. -/
lemma Mbal_airy_ratio {a z : ℝ} (ha : a ≤ -4) (hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    (Real.sqrt 2)⁻¹ * Mbal a z ≤ Mbal a (z1Well a) ∧
      Mbal a (z1Well a) ≤ Real.sqrt 2 * Mbal a z := by
  have hk_z := k2_airy_bounds ha hz1 hz2
  have hk_z1 := k2_airy_bounds ha le_rfl (z1Well_le_z2Airy ha)
  have hA0 : 0 < -a := by linarith
  have hA13 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hA0 _
  have hkz_pos : 0 < k2 a z := lt_of_lt_of_le hA13 hk_z.1
  have hkz1_pos : 0 < k2 a (z1Well a) := lt_of_lt_of_le hA13 hk_z1.1
  have hsqrt2_ge : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hsqrt2_inv : (Real.sqrt 2)⁻¹ ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg (by norm_num)]
    exact inv_anti₀ (by positivity) hsqrt2_ge
  have hM_z : 0 ≤ Mbal a z := (Mbal_pos a z).le
  constructor
  · have hle : k2 a (z1Well a) ≤ 2 * k2 a z := by linarith [hk_z1.2, hk_z.1]
    have hr : (2 * k2 a z) ^ (-(1 : ℝ) / 4) ≤ (k2 a (z1Well a)) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hkz1_pos hle (by norm_num)
    have hmul : (2 * k2 a z) ^ (-(1 : ℝ) / 4) = (2 : ℝ) ^ (-(1 : ℝ) / 4) * Mbal a z := by
      unfold Mbal
      rw [Real.mul_rpow (by norm_num) hkz_pos.le]
    calc (Real.sqrt 2)⁻¹ * Mbal a z
        ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) * Mbal a z := by gcongr
      _ = (2 * k2 a z) ^ (-(1 : ℝ) / 4) := hmul.symm
      _ ≤ Mbal a (z1Well a) := hr
  · have hle : k2 a z ≤ 2 * k2 a (z1Well a) := by linarith [hk_z.2, hk_z1.1]
    have h2 : k2 a z / 2 ≤ k2 a (z1Well a) := by linarith
    have hr : (k2 a (z1Well a)) ^ (-(1 : ℝ) / 4) ≤ (k2 a z / 2) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num)
    have hmul : (k2 a z / 2) ^ (-(1 : ℝ) / 4) = (2 : ℝ) ^ ((1 : ℝ) / 4) * Mbal a z := by
      unfold Mbal
      rw [div_eq_mul_inv, Real.mul_rpow hkz_pos.le (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      norm_num
      ring
    calc Mbal a (z1Well a)
        ≤ (k2 a z / 2) ^ (-(1 : ℝ) / 4) := hr
      _ = (2 : ℝ) ^ ((1 : ℝ) / 4) * Mbal a z := hmul
      _ ≤ Real.sqrt 2 * Mbal a z := by gcongr

/-- On `[z₁(a), z₂(a)]` with `a ≤ -4`, `y(z)^2 + y'(z)^2 / k₂(a, z)` lies in `[R₀(z)/2, R₀(z)]`. -/
lemma R0Airy_vs_k2 (y : ℝ → ℝ) {a z : ℝ} (ha : a ≤ -4) (hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    1 / 2 * R0Airy y a z ≤ y z ^ 2 + deriv y z ^ 2 / k2 a z ∧
      y z ^ 2 + deriv y z ^ 2 / k2 a z ≤ R0Airy y a z := by
  have hk := k2_airy_bounds ha hz1 hz2
  have hA0 : 0 < -a := by linarith
  have hA13 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hA0 _
  have hkz_pos : 0 < k2 a z := lt_of_lt_of_le hA13 hk.1
  unfold R0Airy
  constructor
  · have hdiv : deriv y z ^ 2 / (2 * (-a) ^ ((1 : ℝ) / 3)) ≤ deriv y z ^ 2 / k2 a z :=
      div_le_div_of_nonneg_left (sq_nonneg _) hkz_pos hk.2
    have hy2 : 1 / 2 * y z ^ 2 ≤ y z ^ 2 := by linarith [sq_nonneg (y z)]
    linarith [show 1 / 2 * (y z ^ 2 + deriv y z ^ 2 / (-a) ^ ((1 : ℝ) / 3)) =
      1 / 2 * y z ^ 2 + deriv y z ^ 2 / (2 * (-a) ^ ((1 : ℝ) / 3)) by ring]
  · have hdiv : deriv y z ^ 2 / k2 a z ≤ deriv y z ^ 2 / (-a) ^ ((1 : ℝ) / 3) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hA13 hk.1
    linarith

/-- Transporting the scaled `k₂`-energy `sqrt((c y)^2 + (c y')^2 / k₂)` across `[z₁(a), z₂(a)]`
for any Weber solution `y` and `c > 0`. -/
lemma env_scale_airy_bounds {a : ℝ} (ha : a ≤ -4) {c : ℝ} (hc : 0 < c) (y : ℝ → ℝ)
    (hy : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), DifferentiableAt ℝ y z)
    (hy' : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), DifferentiableAt ℝ (deriv y) z)
    (hode : ∀ z ∈ Set.Icc (z1Well a) (z2Airy a), deriv (deriv y) z = (z ^ 2 / 4 + a) * y z) :
    ∀ z ∈ Set.Icc (z1Well a) (z2Airy a),
      (Real.sqrt 2)⁻¹ * Real.exp (-9) *
          Real.sqrt ((c * y (z1Well a)) ^ 2 + (c * deriv y (z1Well a)) ^ 2 / k2 a (z1Well a)) ≤
        Real.sqrt ((c * y z) ^ 2 + (c * deriv y z) ^ 2 / k2 a z) ∧
      Real.sqrt ((c * y z) ^ 2 + (c * deriv y z) ^ 2 / k2 a z) ≤
        Real.sqrt 2 * Real.exp 9 *
          Real.sqrt ((c * y (z1Well a)) ^ 2 + (c * deriv y (z1Well a)) ^ 2 / k2 a (z1Well a)) := by
  have hR0 := R0Airy_bounds ha y hy hy' hode
  have hfac : ∀ w, Real.sqrt ((c * y w) ^ 2 + (c * deriv y w) ^ 2 / k2 a w) =
      c * Real.sqrt (y w ^ 2 + deriv y w ^ 2 / k2 a w) := by
    intro w
    have h1 : (c * y w) ^ 2 + (c * deriv y w) ^ 2 / k2 a w =
        c ^ 2 * (y w ^ 2 + deriv y w ^ 2 / k2 a w) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hvs_z1 := R0Airy_vs_k2 y ha le_rfl (z1Well_le_z2Airy ha)
  have hsqrt_z1_lb : (Real.sqrt 2)⁻¹ * Real.sqrt (R0Airy y a (z1Well a)) ≤
      Real.sqrt (y (z1Well a) ^ 2 + deriv y (z1Well a) ^ 2 / k2 a (z1Well a)) := by
    rw [show (Real.sqrt 2)⁻¹ = Real.sqrt (1 / 2) by
      rw [one_div, Real.sqrt_inv]]
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hvs_z1.1
  have hsqrt_z1_ub : Real.sqrt (y (z1Well a) ^ 2 + deriv y (z1Well a) ^ 2 / k2 a (z1Well a)) ≤
      Real.sqrt (R0Airy y a (z1Well a)) := Real.sqrt_le_sqrt hvs_z1.2
  intro z hz
  have hvs_z := R0Airy_vs_k2 y ha hz.1 hz.2
  have hsqrt_z_lb : (Real.sqrt 2)⁻¹ * Real.sqrt (R0Airy y a z) ≤
      Real.sqrt (y z ^ 2 + deriv y z ^ 2 / k2 a z) := by
    rw [show (Real.sqrt 2)⁻¹ = Real.sqrt (1 / 2) by rw [one_div, Real.sqrt_inv]]
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hvs_z.1
  have hsqrt_z_ub : Real.sqrt (y z ^ 2 + deriv y z ^ 2 / k2 a z) ≤
      Real.sqrt (R0Airy y a z) := Real.sqrt_le_sqrt hvs_z.2
  have hR0_sqrt_lb : Real.exp (-9) * Real.sqrt (R0Airy y a (z1Well a)) ≤
      Real.sqrt (R0Airy y a z) := by
    rw [← Real.sqrt_sq (Real.exp_pos (-9)).le, ← Real.sqrt_mul (sq_nonneg _),
      sq, ← Real.exp_add, show (-9 : ℝ) + -9 = -18 by norm_num]
    exact Real.sqrt_le_sqrt (hR0 z hz).1
  have hR0_sqrt_ub : Real.sqrt (R0Airy y a z) ≤
      Real.exp 9 * Real.sqrt (R0Airy y a (z1Well a)) := by
    rw [← Real.sqrt_sq (Real.exp_pos 9).le, ← Real.sqrt_mul (sq_nonneg _),
      sq, ← Real.exp_add, show (9 : ℝ) + 9 = 18 by norm_num]
    exact Real.sqrt_le_sqrt (hR0 z hz).2
  rw [hfac z, hfac (z1Well a)]
  constructor
  · calc (Real.sqrt 2)⁻¹ * Real.exp (-9) *
          (c * Real.sqrt (y (z1Well a) ^ 2 + deriv y (z1Well a) ^ 2 / k2 a (z1Well a)))
        ≤ (Real.sqrt 2)⁻¹ * Real.exp (-9) * (c * Real.sqrt (R0Airy y a (z1Well a))) := by
          gcongr
      _ = c * ((Real.sqrt 2)⁻¹ * (Real.exp (-9) * Real.sqrt (R0Airy y a (z1Well a)))) := by ring
      _ ≤ c * ((Real.sqrt 2)⁻¹ * Real.sqrt (R0Airy y a z)) := by gcongr
      _ ≤ c * Real.sqrt (y z ^ 2 + deriv y z ^ 2 / k2 a z) := by gcongr
  · calc c * Real.sqrt (y z ^ 2 + deriv y z ^ 2 / k2 a z)
        ≤ c * Real.sqrt (R0Airy y a z) := by gcongr
      _ ≤ c * (Real.exp 9 * Real.sqrt (R0Airy y a (z1Well a))) := by gcongr
      _ ≤ c * (Real.exp 9 * (Real.sqrt 2 *
            Real.sqrt (y (z1Well a) ^ 2 + deriv y (z1Well a) ^ 2 / k2 a (z1Well a)))) := by
          gcongr
          rw [← mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))] at hsqrt_z1_lb
          linarith [show (Real.sqrt 2)⁻¹ * Real.sqrt (R0Airy y a (z1Well a)) * Real.sqrt 2 =
            Real.sqrt (R0Airy y a (z1Well a)) by
            field_simp [ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' ]]
      _ = Real.sqrt 2 * Real.exp 9 *
            (c * Real.sqrt (y (z1Well a) ^ 2 + deriv y (z1Well a) ^ 2 / k2 a (z1Well a))) := by ring

/-! ### Bounds on `Ewell` on `[z₁, z₂]` -/

/-- On `[z₁(a), z₂(a)]` with `a ≤ -4`, `exp(-3) ≤ Ewell a z ≤ 1`.
In fact, `Ewell a z ≥ exp(-2 * sqrt 2) > exp(-3)`. -/
lemma Ewell_airy_bounds {a z : ℝ} (ha : a ≤ -4) (_hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    Real.exp (-3) ≤ Ewell a z ∧ Ewell a z ≤ 1 := by
  unfold Ewell
  split_ifs with hlt
  · have hA0 : 0 < -a := by linarith
    have habs : |a| = -a := abs_of_nonpos (by linarith)
    rw [habs] at hlt ⊢
    set zt := 2 * Real.sqrt (-a)
    have hnonneg : 0 ≤ ∫ t in zt..z, Real.sqrt (t ^ 2 / 4 - -a) :=
      intervalIntegral.integral_nonneg hlt.le (fun _ _ => Real.sqrt_nonneg _)
    -- Bound the integrand by `sqrt 2 * (-a)^{1/6}` and the length by `2 * (-a)^{-1/6}`
    have hC_int : ∫ t in zt..z, Real.sqrt (t ^ 2 / 4 - -a) ≤
        (z - zt) * (Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6)) := by
      have hint1 : IntervalIntegrable (fun t => Real.sqrt (t ^ 2 / 4 - -a)) MeasureTheory.volume zt z :=
        Continuous.intervalIntegrable (by fun_prop) zt z
      have hint2 : IntervalIntegrable (fun _ => Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6)) MeasureTheory.volume zt z :=
        intervalIntegrable_const
      have hmono : ∫ t in zt..z, Real.sqrt (t ^ 2 / 4 - -a) ≤
          ∫ _t in zt..z, Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6) := by
        apply intervalIntegral.integral_mono_on hlt.le hint1 hint2
        intro t ht
        have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ zt) ht.1
        have ht_ub : t ^ 2 ≤ (z2Airy a) ^ 2 := by nlinarith [ht.2, hz2]
        have hz2_sq : (z2Airy a) ^ 2 = 4 * (-a + 2 * (-a) ^ ((1 : ℝ) / 3)) := by
          unfold z2Airy
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          ring
        have hsub : t ^ 2 / 4 - -a ≤ 2 * (-a) ^ ((1 : ℝ) / 3) := by linarith
        have hrhs : Real.sqrt (2 * (-a) ^ ((1 : ℝ) / 3)) = Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6) := by
          rw [Real.sqrt_mul (by norm_num)]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA0.le]
          norm_num
        rw [← hrhs]
        exact Real.sqrt_le_sqrt hsub
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      exact hmono
    have hlen : z - zt ≤ 2 * (-a) ^ ((1 : ℝ) / 3) / Real.sqrt (-a) := by
      set s2 := Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3))
      set sA := Real.sqrt (-a)
      have hsA_pos : 0 < sA := Real.sqrt_pos.mpr hA0
      have hs2_ge : sA ≤ s2 := by
        apply Real.sqrt_le_sqrt
        linarith [Real.rpow_pos_of_pos hA0 ((1 : ℝ) / 3)]
      have hsum_pos : 0 < s2 + sA := by linarith
      have hs_diff : s2 ^ 2 - sA ^ 2 = 2 * (-a) ^ ((1 : ℝ) / 3) := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hA0.le]; ring
      have hz2_diff : z2Airy a - zt = 4 * (-a) ^ ((1 : ℝ) / 3) / (s2 + sA) := by
        unfold z2Airy
        change 2 * s2 - 2 * sA = 4 * (-a) ^ ((1 : ℝ) / 3) / (s2 + sA)
        rw [eq_div_iff hsum_pos.ne']
        linarith [hs_diff]
      calc z - zt ≤ z2Airy a - zt := by linarith
        _ = 4 * (-a) ^ ((1 : ℝ) / 3) / (s2 + sA) := hz2_diff
        _ ≤ 4 * (-a) ^ ((1 : ℝ) / 3) / (2 * sA) := by
          gcongr; linarith
        _ = 2 * (-a) ^ ((1 : ℝ) / 3) / Real.sqrt (-a) := by ring
    have hrpow : (-a) ^ ((1 : ℝ) / 3) * (-a) ^ ((1 : ℝ) / 6) = Real.sqrt (-a) := by
      rw [← Real.rpow_add hA0, Real.sqrt_eq_rpow]
      norm_num
    have hsA_ne : Real.sqrt (-a) ≠ 0 := (Real.sqrt_pos.mpr hA0).ne'
    have h2sqrt2 : 2 * Real.sqrt 2 ≤ 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt 2)]
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hint_ub : ∫ t in zt..z, Real.sqrt (t ^ 2 / 4 - -a) ≤ 3 := by
      calc ∫ t in zt..z, Real.sqrt (t ^ 2 / 4 - -a)
          ≤ (z - zt) * (Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6)) := hC_int
        _ ≤ (2 * (-a) ^ ((1 : ℝ) / 3) / Real.sqrt (-a)) * (Real.sqrt 2 * (-a) ^ ((1 : ℝ) / 6)) := by
            gcongr
        _ = 2 * Real.sqrt 2 * ((-a) ^ ((1 : ℝ) / 3) * (-a) ^ ((1 : ℝ) / 6)) / Real.sqrt (-a) := by ring
        _ = 2 * Real.sqrt 2 := by rw [hrpow]; field_simp [hsA_ne]
        _ ≤ 3 := h2sqrt2
    constructor
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact Real.exp_le_one_iff.mpr (by linarith)
  · constructor
    · exact Real.exp_le_one_iff.mpr (by norm_num)
    · exact le_rfl

/-! ### Headline `env_well` bounds on `[z₁, z₂]` for `pcU` and `pcV` -/

/-- **E3-link (`env_well` on `[z₁, z₂]` for `pcU` and `pcV`)**: for `a ≤ -4` and
`z₁(a) ≤ z ≤ z₂(a)`, both the `U`-envelope and `V`-envelope satisfy two-sided `env_well`
bounds with explicit absolute constants `exp(-14)` and `exp(14)`. -/
theorem env_well_on_airy_U_V {a z : ℝ} (ha : a ≤ -4) (hz1 : z1Well a ≤ z) (hz2 : z ≤ z2Airy a) :
    (Real.exp (-14) * (Ewell a z * Mbal a z) ≤
        Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        Real.exp 14 * (Ewell a z * Mbal a z)) ∧
    (Real.exp (-14) * ((Ewell a z)⁻¹ * Mbal a z) ≤
        Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
        Real.exp 14 * ((Ewell a z)⁻¹ * Mbal a z)) := by
  have hz1_0 : 0 ≤ z1Well a := z1Well_nonneg a
  have hUV_z1 := env_well_on_Icc_U_V ha hz1_0 le_rfl
  have hEz1 : Ewell a (z1Well a) = 1 := Ewell_eq_one_on_Icc ha le_rfl
  have hM := Mbal_airy_ratio ha hz1 hz2
  have hE := Ewell_airy_bounds ha hz1 hz2
  have hEpos : 0 < Ewell a z := lt_of_lt_of_le (Real.exp_pos (-3)) hE.1
  have hEinv : 1 ≤ (Ewell a z)⁻¹ ∧ (Ewell a z)⁻¹ ≤ Real.exp 3 := by
    constructor
    · exact one_le_inv₀ hEpos |>.mpr hE.2
    · rw [show Real.exp 3 = (Real.exp (-3))⁻¹ by rw [Real.exp_neg, inv_inv]]
      exact inv_anti₀ (Real.exp_pos (-3)) hE.1
  have hMpos : 0 ≤ Mbal a z := (Mbal_pos a z).le
  have hκ := kappaBal_pos a
  have hcV : 0 < Real.sqrt (π / 2) * (kappaBal a)⁻¹ := by positivity
  have hU_trans := env_scale_airy_bounds ha hκ (pcU a)
    (fun w _ => (hasDerivAt_pcU a w).differentiableAt)
    (fun w _ => by rw [deriv_pcU]; exact (hasDerivAt_pcUD a w).differentiableAt)
    (fun w _ => pcU_ode a w) z ⟨hz1, hz2⟩
  have hV_trans := env_scale_airy_bounds ha hcV (pcV a)
    (fun w _ => (hasDerivAt_pcV a w).differentiableAt)
    (fun w _ => by rw [deriv_pcV]; exact (hasDerivAt_pcVD a w).differentiableAt)
    (fun w _ => pcV_ode a w) z ⟨hz1, hz2⟩
  -- Numerical comparison: 117 / 25 < exp 2 and exp (-2) < 43 / 200
  have hexp1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp2 : (117 : ℝ) / 25 ≤ Real.exp 2 := by
    have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    rw [h2]
    nlinarith
  have hexp_m2 : Real.exp (-2) ≤ (43 : ℝ) / 200 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
    have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    rw [h2]
    nlinarith
  have hsqrt2_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  have hsqrt2_mul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  constructor
  · constructor
    · calc Real.exp (-14) * (Ewell a z * Mbal a z)
          ≤ Real.exp (-11) * (Ewell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by positivity)
        _ = (Real.exp (-2) * Real.exp (-9)) * (Ewell a z * Mbal a z) := by
            rw [← Real.exp_add]; norm_num
        _ ≤ ((43 : ℝ) / 200 * Real.exp (-9)) * (Ewell a z * Mbal a z) := by
            gcongr
        _ ≤ ((43 : ℝ) / 200 * Real.exp (-9)) * (1 * Mbal a z) := by
            gcongr; exact hE.2
        _ = (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * ((Real.sqrt 2)⁻¹ * Mbal a z)) := by
            calc ((43 : ℝ) / 200 * Real.exp (-9)) * (1 * Mbal a z)
                = 43 / 100 * (1 / 2) * Real.exp (-9) * Mbal a z := by ring
              _ = 43 / 100 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * Real.exp (-9) * Mbal a z := by
                  rw [hsqrt2_sq]
              _ = (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * ((Real.sqrt 2)⁻¹ * Mbal a z)) := by ring
        _ ≤ (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * Mbal a (z1Well a)) := by
            gcongr; exact hM.1
        _ ≤ (Real.sqrt 2)⁻¹ * Real.exp (-9) *
              Real.sqrt (ut pcU a (z1Well a) ^ 2 + (kappaBal a * deriv (pcU a) (z1Well a)) ^ 2 / k2 a (z1Well a)) := by
            gcongr
            simpa [hEz1] using hUV_z1.1.1
        _ ≤ Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) := hU_trans.1
    · calc Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
          ≤ Real.sqrt 2 * Real.exp 9 *
              Real.sqrt (ut pcU a (z1Well a) ^ 2 + (kappaBal a * deriv (pcU a) (z1Well a)) ^ 2 / k2 a (z1Well a)) :=
            hU_trans.2
        _ ≤ Real.sqrt 2 * Real.exp 9 * (117 / 50 * Mbal a (z1Well a)) := by
            gcongr; simpa [hEz1] using hUV_z1.1.2
        _ ≤ Real.sqrt 2 * Real.exp 9 * (117 / 50 * (Real.sqrt 2 * Mbal a z)) := by
            gcongr; exact hM.2
        _ = (117 / 25 * Real.exp 9) * Mbal a z := by
            calc Real.sqrt 2 * Real.exp 9 * (117 / 50 * (Real.sqrt 2 * Mbal a z))
                = (Real.sqrt 2 * Real.sqrt 2) * (117 / 50) * Real.exp 9 * Mbal a z := by ring
              _ = 2 * (117 / 50) * Real.exp 9 * Mbal a z := by rw [hsqrt2_mul]
              _ = (117 / 25 * Real.exp 9) * Mbal a z := by ring
        _ ≤ (Real.exp 2 * Real.exp 9) * (Real.exp 3 * Ewell a z * Mbal a z) := by
            gcongr
            have : 1 ≤ Real.exp 3 * Ewell a z := by
              calc (1 : ℝ) = Real.exp 3 * Real.exp (-3) := by rw [← Real.exp_add]; norm_num
                _ ≤ Real.exp 3 * Ewell a z := by gcongr; exact hE.1
            linarith [mul_le_mul_of_nonneg_right this hMpos]
        _ = Real.exp 14 * (Ewell a z * Mbal a z) := by
            rw [show (Real.exp 2 * Real.exp 9) * (Real.exp 3 * Ewell a z * Mbal a z) =
              Real.exp (2 + 9 + 3) * (Ewell a z * Mbal a z) by
              rw [Real.exp_add, Real.exp_add]; ring]
            norm_num
  · constructor
    · calc Real.exp (-14) * ((Ewell a z)⁻¹ * Mbal a z)
          = (Real.exp (-2) * Real.exp (-9) * Real.exp (-3)) * ((Ewell a z)⁻¹ * Mbal a z) := by
            rw [← Real.exp_add, ← Real.exp_add]; norm_num
        _ ≤ ((43 : ℝ) / 200 * Real.exp (-9)) * (Real.exp (-3) * (Ewell a z)⁻¹ * Mbal a z) := by
            have hle : Real.exp (-2) * Real.exp (-9) * Real.exp (-3) * ((Ewell a z)⁻¹ * Mbal a z) ≤
                (43 : ℝ) / 200 * Real.exp (-9) * (Real.exp (-3) * (Ewell a z)⁻¹ * Mbal a z) := by
              have h1 : Real.exp (-2) * Real.exp (-9) * Real.exp (-3) * ((Ewell a z)⁻¹ * Mbal a z) =
                  Real.exp (-2) * (Real.exp (-9) * Real.exp (-3) * ((Ewell a z)⁻¹ * Mbal a z)) := by ring
              have h2 : (43 : ℝ) / 200 * Real.exp (-9) * (Real.exp (-3) * (Ewell a z)⁻¹ * Mbal a z) =
                  (43 : ℝ) / 200 * (Real.exp (-9) * Real.exp (-3) * ((Ewell a z)⁻¹ * Mbal a z)) := by ring
              rw [h1, h2]
              gcongr
            exact hle
        _ ≤ ((43 : ℝ) / 200 * Real.exp (-9)) * (1 * Mbal a z) := by
            gcongr
            calc Real.exp (-3) * (Ewell a z)⁻¹ ≤ Real.exp (-3) * Real.exp 3 := by gcongr; exact hEinv.2
              _ = 1 := by rw [← Real.exp_add]; norm_num
        _ = (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * ((Real.sqrt 2)⁻¹ * Mbal a z)) := by
            calc ((43 : ℝ) / 200 * Real.exp (-9)) * (1 * Mbal a z)
                = 43 / 100 * (1 / 2) * Real.exp (-9) * Mbal a z := by ring
              _ = 43 / 100 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * Real.exp (-9) * Mbal a z := by
                  rw [hsqrt2_sq]
              _ = (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * ((Real.sqrt 2)⁻¹ * Mbal a z)) := by ring
        _ ≤ (Real.sqrt 2)⁻¹ * Real.exp (-9) * (43 / 100 * Mbal a (z1Well a)) := by
            gcongr; exact hM.1
        _ ≤ (Real.sqrt 2)⁻¹ * Real.exp (-9) *
              Real.sqrt (vt pcV a (z1Well a) ^ 2 +
                (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) (z1Well a)) ^ 2 / k2 a (z1Well a)) := by
            gcongr
            simpa [hEz1] using hUV_z1.2.1
        _ ≤ Real.sqrt (vt pcV a z ^ 2 +
              (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) := hV_trans.1
    · calc Real.sqrt (vt pcV a z ^ 2 +
              (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z)
          ≤ Real.sqrt 2 * Real.exp 9 *
              Real.sqrt (vt pcV a (z1Well a) ^ 2 +
                (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) (z1Well a)) ^ 2 / k2 a (z1Well a)) :=
            hV_trans.2
        _ ≤ Real.sqrt 2 * Real.exp 9 * (117 / 50 * Mbal a (z1Well a)) := by
            gcongr; simpa [hEz1] using hUV_z1.2.2
        _ ≤ Real.sqrt 2 * Real.exp 9 * (117 / 50 * (Real.sqrt 2 * Mbal a z)) := by
            gcongr; exact hM.2
        _ = (117 / 25 * Real.exp 9) * Mbal a z := by
            calc Real.sqrt 2 * Real.exp 9 * (117 / 50 * (Real.sqrt 2 * Mbal a z))
                = (Real.sqrt 2 * Real.sqrt 2) * (117 / 50) * Real.exp 9 * Mbal a z := by ring
              _ = 2 * (117 / 50) * Real.exp 9 * Mbal a z := by rw [hsqrt2_mul]
              _ = (117 / 25 * Real.exp 9) * Mbal a z := by ring
        _ ≤ (Real.exp 2 * Real.exp 9) * ((Ewell a z)⁻¹ * Mbal a z) := by
            gcongr
            exact le_mul_of_one_le_left hMpos hEinv.1
        _ = Real.exp 11 * ((Ewell a z)⁻¹ * Mbal a z) := by
            rw [← Real.exp_add]; norm_num
        _ ≤ Real.exp 14 * ((Ewell a z)⁻¹ * Mbal a z) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by positivity)

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.env_well_on_airy_U_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env_well_on_airy_U_V

end FormalResearch.JacobiEigenvectors.Charts

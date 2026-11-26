module

public import FormalResearch.ModularBootstrap.Spin.SpinDLagAdd
public import FormalResearch.ModularBootstrap.Spin.SpinS1c
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian chiral Cardy identity and 2D tensor Cayley expansion (`dsl:tensor-cayley`)

Proves:
- `spin_gaussian_V1`: `∫ r, exp(-π β r²) V_1(r) = β^{-1/2} q(β⁻¹)` for `a ≥ 2`, `β > 0`.
- `spin_gaussian_V1_prod`: 2D product Gaussian integral against `V_1 ⊗ V_1`, giving
  `spinVacT a (fun p => spinThermalX βL βR p.1 p.2) = spinThermalXVac a βL βR`.
- `spin_tensor_cayley_hasSum`: pointwise 2D tensor Cayley expansion (`dsl:tensor-cayley`).
- `spin_tensor_cayley_integral`: termwise integration of `dsl:tensor-cayley` against any positive
  measure `ν` on `E_B` with finite diagonal Laplace transform at `s_θ`, and against the Cardy
  product measure `V_1 ⊗ V_1`.
- `spin_tensor_cayley_iff`: local crossing on `(s_θ, 1/s_θ)²` holds iff all odd two-variable
  Laguerre moments match `-spinVacT`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.LP

/-! ### Section 1: Gaussian chiral Cardy identity -/

private lemma integral_exp_neg_pi_mul_sq_mul_cosh {β c : ℝ} (hβ : 0 < β) :
    Integrable (fun r : ℝ => Real.exp (-π * β * r ^ 2) * Real.cosh (2 * π * c * r)) ∧
    ∫ r : ℝ, Real.exp (-π * β * r ^ 2) * Real.cosh (2 * π * c * r) =
      β ^ (-(1 / 2 : ℝ)) * Real.exp (π * c ^ 2 / β) := by
  have h1 : ∀ s : ℝ,
      Integrable (fun r : ℝ => Real.exp (-π * β * r ^ 2 + 2 * π * s * r)) ∧
      ∫ r : ℝ, Real.exp (-π * β * r ^ 2 + 2 * π * s * r) =
        β ^ (-(1 / 2 : ℝ)) * Real.exp (π * s ^ 2 / β) := by
    intro s
    have hcomp : ∀ r : ℝ,
        Real.exp (-π * β * r ^ 2 + 2 * π * s * r) =
          Real.exp (π * s ^ 2 / β) * Real.exp (-(π * β) * (r - s / β) ^ 2) := by
      intro r
      rw [← Real.exp_add]
      congr 1
      field_simp [hβ.ne']
      ring
    simp_rw [hcomp]
    have hbase : Integrable (fun u : ℝ => Real.exp (-(π * β) * u ^ 2)) :=
      integrable_exp_neg_mul_sq (by positivity)
    have hshift : Integrable (fun r : ℝ => Real.exp (-(π * β) * (r - s / β) ^ 2)) :=
      hbase.comp_sub_right (s / β)
    refine ⟨hshift.const_mul _, ?_⟩
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun u => Real.exp (-(π * β) * u ^ 2)) (s / β),
      integral_gaussian (π * β)]
    have hsqrt : Real.sqrt (π / (π * β)) = β ^ (-(1 / 2 : ℝ)) := by
      rw [div_mul_eq_div_div, div_self Real.pi_pos.ne', one_div, Real.sqrt_inv,
        Real.sqrt_eq_rpow, Real.rpow_neg hβ.le]
    rw [hsqrt, mul_comm]
  have hp := h1 c
  have hm := h1 (-c)
  have hpt : ∀ r : ℝ, Real.exp (-π * β * r ^ 2) * Real.cosh (2 * π * c * r) =
      (1 / 2 : ℝ) * Real.exp (-π * β * r ^ 2 + 2 * π * c * r) +
      (1 / 2 : ℝ) * Real.exp (-π * β * r ^ 2 + 2 * π * (-c) * r) := by
    intro r
    rw [Real.cosh_eq]
    have e1 : Real.exp (-π * β * r ^ 2) * Real.exp (2 * π * c * r) =
        Real.exp (-π * β * r ^ 2 + 2 * π * c * r) := (Real.exp_add _ _).symm
    have e2 : Real.exp (-π * β * r ^ 2) * Real.exp (-(2 * π * c * r)) =
        Real.exp (-π * β * r ^ 2 + 2 * π * (-c) * r) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-π * β * r ^ 2) * ((Real.exp (2 * π * c * r) + Real.exp (-(2 * π * c * r))) / 2)
        = (1 / 2 : ℝ) * (Real.exp (-π * β * r ^ 2) * Real.exp (2 * π * c * r)) +
          (1 / 2 : ℝ) * (Real.exp (-π * β * r ^ 2) * Real.exp (-(2 * π * c * r))) := by ring
      _ = _ := by rw [e1, e2]
  simp_rw [hpt]
  refine ⟨(hp.1.const_mul _).add (hm.1.const_mul _), ?_⟩
  rw [integral_add (hp.1.const_mul _) (hm.1.const_mul _), integral_const_mul, integral_const_mul,
    hp.2, hm.2, neg_sq]
  ring

/-- **Gaussian chiral Cardy identity** (`spinning_dual.tex`, proof of `sd:W`):
`∫_ℝ exp(-π β r²) V_1(r) dr = β^{-1/2} q(β⁻¹)`. -/
theorem spin_gaussian_V1 {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    Integrable (fun r : ℝ => Real.exp (-π * β * r ^ 2) * spinV1 a r) ∧
    ∫ r : ℝ, Real.exp (-π * β * r ^ 2) * spinV1 a r =
      β ^ (-(1 / 2 : ℝ)) * spinVacuumQ a β⁻¹ := by
  have h1 := integral_exp_neg_pi_mul_sq_mul_cosh (c := Real.sqrt a) hβ
  have h2 := integral_exp_neg_pi_mul_sq_mul_cosh (c := Real.sqrt (a - 2)) hβ
  have hpt : ∀ r : ℝ, Real.exp (-π * β * r ^ 2) * spinV1 a r =
      Real.exp (-π * β * r ^ 2) * Real.cosh (2 * π * Real.sqrt a * r) -
      Real.exp (-π * β * r ^ 2) * Real.cosh (2 * π * Real.sqrt (a - 2) * r) := by
    intro r; unfold spinV1; ring
  simp_rw [hpt]
  refine ⟨h1.1.sub h2.1, ?_⟩
  rw [integral_sub h1.1 h2.1, h1.2, h2.2, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  unfold spinVacuumQ
  have hexp : Real.exp (π * a * β⁻¹) * (1 - Real.exp (-2 * π * β⁻¹)) =
      Real.exp (π * a / β) - Real.exp (π * (a - 2) / β) := by
    rw [mul_sub, mul_one, ← Real.exp_add, div_eq_mul_inv, div_eq_mul_inv]
    congr 2; ring
  rw [hexp]
  ring

/-- 2D product Gaussian integral against `V_1 ⊗ V_1`. -/
theorem spin_gaussian_V1_prod {a βL βR : ℝ} (ha : 2 ≤ a) (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) *
      spinV1 a p.1 * spinV1 a p.2) ∧
    ∫ p : ℝ × ℝ, Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) *
      spinV1 a p.1 * spinV1 a p.2 =
      (βL * βR) ^ (-(1 / 2 : ℝ)) * spinVacuumV a βL⁻¹ βR⁻¹ := by
  have hL := spin_gaussian_V1 ha hβL
  have hR := spin_gaussian_V1 ha hβR
  have hpt : ∀ p : ℝ × ℝ,
      Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) * spinV1 a p.1 * spinV1 a p.2 =
        (Real.exp (-π * βL * p.1 ^ 2) * spinV1 a p.1) *
        (Real.exp (-π * βR * p.2 ^ 2) * spinV1 a p.2) := by
    intro p
    have he : Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) =
        Real.exp (-π * βL * p.1 ^ 2) * Real.exp (-π * βR * p.2 ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]; ring
  simp_rw [hpt]
  refine ⟨hL.1.mul_prod hR.1, ?_⟩
  rw [Measure.volume_eq_prod ℝ ℝ,
    integral_prod_mul (f := fun r => Real.exp (-π * βL * r ^ 2) * spinV1 a r)
      (g := fun r => Real.exp (-π * βR * r ^ 2) * spinV1 a r),
    hL.2, hR.2]
  unfold spinVacuumV
  have hpow : βL ^ (-(1 / 2 : ℝ)) * βR ^ (-(1 / 2 : ℝ)) = (βL * βR) ^ (-(1 / 2 : ℝ)) :=
    (Real.mul_rpow hβL.le hβR.le).symm
  rw [← hpow]
  ring

/-- Vacuum value of the two-variable thermal test `X_{β_L, β_R}` equals `X_{β_L, β_R, vac}`. -/
theorem spinVacT_thermalX {a βL βR : ℝ} (ha : 2 ≤ a) (hβL : 0 < βL) (hβR : 0 < βR) :
    spinVacT a (fun p => spinThermalX βL βR p.1 p.2) = spinThermalXVac a βL βR := by
  unfold spinVacT spinPhiVac spinLiftTToR spinThermalX
  have h1 := spin_gaussian_V1_prod ha hβL hβR
  have h2 := spin_gaussian_V1_prod ha (inv_pos.mpr hβL) (inv_pos.mpr hβR)
  have hpt : ∀ p : ℝ × ℝ,
      (Real.exp (-2 * π * (βL * (p.1 ^ 2 / 2) + βR * (p.2 ^ 2 / 2))) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-2 * π * (p.1 ^ 2 / 2 / βL + p.2 ^ 2 / 2 / βR))) *
        spinV1 a p.1 * spinV1 a p.2 =
      Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) * spinV1 a p.1 * spinV1 a p.2 -
      (βL * βR) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (-π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2)) * spinV1 a p.1 * spinV1 a p.2) := by
    intro p
    have e1 : -2 * π * (βL * (p.1 ^ 2 / 2) + βR * (p.2 ^ 2 / 2)) =
        -π * (βL * p.1 ^ 2 + βR * p.2 ^ 2) := by ring
    have e2 : -2 * π * (p.1 ^ 2 / 2 / βL + p.2 ^ 2 / 2 / βR) =
        -π * (βL⁻¹ * p.1 ^ 2 + βR⁻¹ * p.2 ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    rw [e1, e2]; ring
  simp_rw [hpt]
  rw [integral_sub h1.1 (h2.1.const_mul _), integral_const_mul, h1.2, h2.2, inv_inv, inv_inv]
  have hpow : (βL * βR) ^ (-(1 / 2 : ℝ)) * (βL⁻¹ * βR⁻¹) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.mul_rpow (mul_pos hβL hβR).le (mul_pos (inv_pos.mpr hβL) (inv_pos.mpr hβR)).le]
    have hmul : (βL * βR) * (βL⁻¹ * βR⁻¹) = 1 := by field_simp [hβL.ne', hβR.ne']
    rw [hmul, Real.one_rpow]
  unfold spinThermalXVac
  linear_combination spinVacuumV a βL βR * hpow

/-! ### Section 2: Pointwise 2D tensor Cayley expansion (`dsl:tensor-cayley`) -/

private lemma spin_tensor_cayley_single {ϖL ϖR βL βR : ℝ} (hϖL : |ϖL| < 1) (hϖR : |ϖR| < 1)
    (hβL : βL = (1 + ϖL) / (1 - ϖL)) (hβR : βR = (1 + ϖR) / (1 - ϖR)) (tL tR : ℝ) :
    HasSum (fun p : ℕ × ℕ =>
      ϖL ^ p.1 * ϖR ^ p.2 * (lagPsi (1 / 2) p.1 tL * lagPsi (1 / 2) p.2 tR))
      ((1 - ϖL) ^ (-(1 / 2 : ℝ)) * (1 - ϖR) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-2 * π * (βL * tL + βR * tR))) := by
  have h1L : 0 < 1 - ϖL := by linarith [(abs_lt.1 hϖL).2]
  have h1R : 0 < 1 - ϖR := by linarith [(abs_lt.1 hϖR).2]
  have hL := (hasSum_lagL_gen_real (w := 1 / 2) (by norm_num) (4 * π * tL) hϖL).mul_left
    (Real.exp (-2 * π * tL))
  have hR := (hasSum_lagL_gen_real (w := 1 / 2) (by norm_num) (4 * π * tR) hϖR).mul_left
    (Real.exp (-2 * π * tR))
  have heL : Real.exp (-2 * π * tL) * lagGenReal (1 / 2) (4 * π * tL) ϖL =
      (1 - ϖL) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βL * tL) := by
    unfold lagGenReal
    have e : Real.exp (-2 * π * tL) * Real.exp (-(4 * π * tL) * ϖL / (1 - ϖL)) =
        Real.exp (-2 * π * βL * tL) := by
      rw [← Real.exp_add]; congr 1; rw [hβL]; field_simp [h1L.ne']; ring
    rw [← mul_left_comm, e]
  have heR : Real.exp (-2 * π * tR) * lagGenReal (1 / 2) (4 * π * tR) ϖR =
      (1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR) := by
    unfold lagGenReal
    have e : Real.exp (-2 * π * tR) * Real.exp (-(4 * π * tR) * ϖR / (1 - ϖR)) =
        Real.exp (-2 * π * βR * tR) := by
      rw [← Real.exp_add]; congr 1; rw [hβR]; field_simp [h1R.ne']; ring
    rw [← mul_left_comm, e]
  rw [heL] at hL; rw [heR] at hR
  -- Absolute summability of each factor via `spin_abs_lagPsi_le_shifted`
  set θL : ℝ := (|ϖL| + 1) / 2
  set θR : ℝ := (|ϖR| + 1) / 2
  have hθL0 : 0 < θL := by dsimp [θL]; linarith [abs_nonneg ϖL]
  have hθL1 : θL < 1 := by dsimp [θL]; linarith
  have hθR0 : 0 < θR := by dsimp [θR]; linarith [abs_nonneg ϖR]
  have hθR1 : θR < 1 := by dsimp [θR]; linarith
  have ha_norm : Summable (fun m : ℕ => ‖ϖL ^ m * lagPsi (1 / 2) m tL‖) := by
    let BL : ℝ := max 0 (-tL)
    have hBL : 0 ≤ BL := le_max_left _ _
    have htL : -BL ≤ tL := by dsimp [BL]; linarith [le_max_right (0 : ℝ) (-tL)]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one (by positivity : 0 ≤ |ϖL| / θL)
        ((div_lt_one hθL0).mpr (by dsimp [θL]; linarith))).mul_left
        ((1 - θL) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * BL / sTheta θL) *
          Real.exp (-2 * π * sTheta θL * tL)))
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have hbd := spin_abs_lagPsi_le_shifted (w := 1 / 2) (by norm_num) hθL0 hθL1 hBL htL m
    have hr : (|ϖL| / θL) ^ m = |ϖL| ^ m * θL⁻¹ ^ m := by rw [div_eq_mul_inv, mul_pow]
    rw [hr]
    calc |ϖL| ^ m * |lagPsi (1 / 2) m tL|
        ≤ |ϖL| ^ m * ((1 - θL) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * BL / sTheta θL) *
            θL⁻¹ ^ m * Real.exp (-2 * π * sTheta θL * tL)) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = _ := by ring
  have hb_norm : Summable (fun n : ℕ => ‖ϖR ^ n * lagPsi (1 / 2) n tR‖) := by
    let BR : ℝ := max 0 (-tR)
    have hBR : 0 ≤ BR := le_max_left _ _
    have htR : -BR ≤ tR := by dsimp [BR]; linarith [le_max_right (0 : ℝ) (-tR)]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity : 0 ≤ |ϖR| / θR)
        ((div_lt_one hθR0).mpr (by dsimp [θR]; linarith))).mul_left
        ((1 - θR) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * BR / sTheta θR) *
          Real.exp (-2 * π * sTheta θR * tR)))
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have hbd := spin_abs_lagPsi_le_shifted (w := 1 / 2) (by norm_num) hθR0 hθR1 hBR htR n
    have hr : (|ϖR| / θR) ^ n = |ϖR| ^ n * θR⁻¹ ^ n := by rw [div_eq_mul_inv, mul_pow]
    rw [hr]
    calc |ϖR| ^ n * |lagPsi (1 / 2) n tR|
        ≤ |ϖR| ^ n * ((1 - θR) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * BR / sTheta θR) *
            θR⁻¹ ^ n * Real.exp (-2 * π * sTheta θR * tR)) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = _ := by ring
  have hL' : HasSum (fun m : ℕ => ϖL ^ m * lagPsi (1 / 2) m tL)
      ((1 - ϖL) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βL * tL)) := by
    convert hL using 1; ext m; unfold lagPsi; ring
  have hR' : HasSum (fun n : ℕ => ϖR ^ n * lagPsi (1 / 2) n tR)
      ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR)) := by
    convert hR using 1; ext n; unfold lagPsi; ring
  let f : ℕ × ℕ → ℝ := fun p => (ϖL ^ p.1 * lagPsi (1 / 2) p.1 tL) * (ϖR ^ p.2 * lagPsi (1 / 2) p.2 tR)
  have hf_norm : Summable (fun p : ℕ × ℕ => ‖f p‖) := by
    have h1 : Summable (fun p : ℕ × ℕ => ‖ϖL ^ p.1 * lagPsi (1 / 2) p.1 tL‖ *
        ‖ϖR ^ p.2 * lagPsi (1 / 2) p.2 tR‖) :=
      ha_norm.mul_of_nonneg hb_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact h1.congr fun p => (norm_mul _ _).symm
  have hf_sum : Summable f := hf_norm.of_norm
  have hfib : ∀ m : ℕ, HasSum (fun n => f (m, n))
      ((ϖL ^ m * lagPsi (1 / 2) m tL) * ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR))) :=
    fun m => hR'.mul_left _
  have houter : HasSum (fun m => (ϖL ^ m * lagPsi (1 / 2) m tL) *
        ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR)))
      (((1 - ϖL) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βL * tL)) *
        ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR))) := hL'.mul_right _
  have heq : ∑' p, f p = ((1 - ϖL) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βL * tL)) *
      ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR)) :=
    (hf_sum.hasSum.prod_fiberwise hfib).unique houter
  have hhas : HasSum f (((1 - ϖL) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βL * tL)) *
      ((1 - ϖR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * βR * tR))) := by
    rw [← heq]; exact hf_sum.hasSum
  convert hhas using 1
  · ext p; dsimp only [f]; ring
  · have hexp : Real.exp (-2 * π * βL * tL) * Real.exp (-2 * π * βR * tR) =
        Real.exp (-2 * π * (βL * tL + βR * tR)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 - ϖL) ^ (-(1 / 2 : ℝ)) * (1 - ϖR) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-2 * π * (βL * tL + βR * tR))
        = (1 - ϖL) ^ (-(1 / 2 : ℝ)) * (1 - ϖR) ^ (-(1 / 2 : ℝ)) *
            (Real.exp (-2 * π * βL * tL) * Real.exp (-2 * π * βR * tR)) := by rw [hexp]
      _ = _ := by ring

/-- **Pointwise 2D tensor Cayley expansion** (`dsl:tensor-cayley`, `sd:eLag`):
for `|ϖL|, |ϖR| < 1` and `β_i = (1 + ϖ_i) / (1 - ϖ_i)`,
`X_{β_L, β_R}(t_L, t_R) = 2 (1 - ϖ_L)^{1/2} (1 - ϖ_R)^{1/2} ∑_{m+n odd} ϖ_L^m ϖ_R^n ψ_m(t_L) ψ_n(t_R)`. -/
theorem spin_tensor_cayley_hasSum {ϖL ϖR βL βR : ℝ} (hϖL : |ϖL| < 1) (hϖR : |ϖR| < 1)
    (hβL : βL = (1 + ϖL) / (1 - ϖL)) (hβR : βR = (1 + ϖR) / (1 - ϖR)) (tL tR : ℝ) :
    HasSum (fun p : ℕ × ℕ =>
      if Odd (p.1 + p.2) then
        ϖL ^ p.1 * ϖR ^ p.2 * (lagPsi (1 / 2) p.1 tL * lagPsi (1 / 2) p.2 tR)
      else 0)
      (spinThermalX βL βR tL tR / (2 * (1 - ϖL) ^ (1 / 2 : ℝ) * (1 - ϖR) ^ (1 / 2 : ℝ))) := by
  have h1L : 0 < 1 - ϖL := by linarith [(abs_lt.1 hϖL).2]
  have h1R : 0 < 1 - ϖR := by linarith [(abs_lt.1 hϖR).2]
  have h2L : 0 < 1 + ϖL := by linarith [(abs_lt.1 hϖL).1]
  have h2R : 0 < 1 + ϖR := by linarith [(abs_lt.1 hϖR).1]
  have hβL_pos : 0 < βL := by rw [hβL]; positivity
  have hβR_pos : 0 < βR := by rw [hβR]; positivity
  have hA := spin_tensor_cayley_single hϖL hϖR hβL hβR tL tR
  have hβL_inv : βL⁻¹ = (1 + (-ϖL)) / (1 - (-ϖL)) := by rw [hβL, inv_div]; ring_nf
  have hβR_inv : βR⁻¹ = (1 + (-ϖR)) / (1 - (-ϖR)) := by rw [hβR, inv_div]; ring_nf
  have hB := spin_tensor_cayley_single (by rwa [abs_neg]) (by rwa [abs_neg]) hβL_inv hβR_inv tL tR
  have hdiff := (hA.sub hB).div_const 2
  convert hdiff using 1
  · ext p
    have hneg : (-ϖL) ^ p.1 * (-ϖR) ^ p.2 = (-1 : ℝ) ^ (p.1 + p.2) * (ϖL ^ p.1 * ϖR ^ p.2) := by
      rw [neg_eq_neg_one_mul ϖL, neg_eq_neg_one_mul ϖR, mul_pow, mul_pow, pow_add]; ring
    rw [hneg]
    split_ifs with hodd
    · rw [hodd.neg_one_pow]; ring
    · have heven : Even (p.1 + p.2) := Nat.not_odd_iff_even.mp hodd
      rw [heven.neg_one_pow]; ring
  · have h1 : (1 - -ϖL) ^ (-(1 / 2 : ℝ)) = βL ^ (-(1 / 2 : ℝ)) * (1 - ϖL) ^ (-(1 / 2 : ℝ)) := by
      rw [show 1 - -ϖL = 1 + ϖL by ring, hβL, ← Real.mul_rpow (by positivity) h1L.le]
      congr 1; field_simp [h1L.ne']
    have h2 : (1 - -ϖR) ^ (-(1 / 2 : ℝ)) = βR ^ (-(1 / 2 : ℝ)) * (1 - ϖR) ^ (-(1 / 2 : ℝ)) := by
      rw [show 1 - -ϖR = 1 + ϖR by ring, hβR, ← Real.mul_rpow (by positivity) h1R.le]
      congr 1; field_simp [h1R.ne']
    have hpow_prod : βL ^ (-(1 / 2 : ℝ)) * βR ^ (-(1 / 2 : ℝ)) = (βL * βR) ^ (-(1 / 2 : ℝ)) :=
      (Real.mul_rpow hβL_pos.le hβR_pos.le).symm
    have hinvL : (1 - ϖL) ^ (-(1 / 2 : ℝ)) = ((1 - ϖL) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg h1L.le _
    have hinvR : (1 - ϖR) ^ (-(1 / 2 : ℝ)) = ((1 - ϖR) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg h1R.le _
    have hexp : βL⁻¹ * tL + βR⁻¹ * tR = tL / βL + tR / βR := by rw [div_eq_inv_mul, div_eq_inv_mul]
    rw [h1, h2, hexp]
    unfold spinThermalX
    have hneL : (1 - ϖL) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos h1L _).ne'
    have hneR : (1 - ϖR) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos h1R _).ne'
    rw [hinvL, hinvR]
    set eA := Real.exp (-2 * π * (βL * tL + βR * tR))
    set eB := Real.exp (-2 * π * (tL / βL + tR / βR))
    rw [← hpow_prod]
    field_simp [hneL, hneR]

/-! ### Section 3: Termwise integration against a measure on `E_B` and uniqueness -/

/-- Multivariate exponential domination on `E_B` (`sd:eE-B-bound`):
`exp(-2π (β_L t_L + β_R t_R)) ≤ exp(2π B |β_L - β_R|) exp(-2π min(β_L, β_R) (t_L + t_R))`. -/
lemma spin_exp_dom_coneB {B βL βR : ℝ} (_hB : 0 ≤ B) {p : ℝ × ℝ} (hp : p ∈ spinConeB B) :
    Real.exp (-2 * π * (βL * p.1 + βR * p.2)) ≤
      Real.exp (2 * π * B * (βL + βR - 2 * min βL βR)) *
        Real.exp (-2 * π * min βL βR * (p.1 + p.2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 0 ≤ (βL - min βL βR) * (p.1 + B) :=
    mul_nonneg (sub_nonneg.mpr (min_le_left _ _)) (by linarith [hp.1])
  have h2 : 0 ≤ (βR - min βL βR) * (p.2 + B) :=
    mul_nonneg (sub_nonneg.mpr (min_le_right _ _)) (by linarith [hp.2])
  have hpi : 0 < 2 * π := by positivity
  nlinarith

/-- **2D tensor Cayley series against a measure `ν` on `E_B`** (`dsl:tensor-cayley`). -/
theorem spin_tensor_cayley_integral {B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ν : Measure (ℝ × ℝ)} (hν : ν (spinConeB B)ᶜ = 0)
    (hint : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2))) ν)
    {ϖL ϖR βL βR : ℝ} (hϖL : |ϖL| < θ) (hϖR : |ϖR| < θ)
    (hβL : βL = (1 + ϖL) / (1 - ϖL)) (hβR : βR = (1 + ϖR) / (1 - ϖR)) :
    (∀ m n : ℕ, Integrable (fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) ν) ∧
    Integrable (fun q : ℝ × ℝ => spinThermalX βL βR q.1 q.2) ν ∧
    HasSum (fun p : ℕ × ℕ =>
      if Odd (p.1 + p.2) then
        ϖL ^ p.1 * ϖR ^ p.2 * ∫ q : ℝ × ℝ, lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2 ∂ν
      else 0)
      ((∫ q : ℝ × ℝ, spinThermalX βL βR q.1 q.2 ∂ν) /
        (2 * (1 - ϖL) ^ (1 / 2 : ℝ) * (1 - ϖR) ^ (1 / 2 : ℝ))) := by
  have hae : ∀ᵐ q ∂ν, q ∈ spinConeB B := by
    have : ∀ᵐ q ∂ν, q ∉ (spinConeB B)ᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with q hq using not_not.mp hq
  set A : ℝ := (1 - θ) ^ (-(1 / 2 : ℝ)) * Real.exp (2 * π * B / sTheta θ) with hA
  have hA_nn : 0 ≤ A := by positivity
  have hΨ_bd : ∀ (m n : ℕ) (q : ℝ × ℝ), q ∈ spinConeB B →
      |lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2| ≤
        A ^ 2 * θ⁻¹ ^ m * θ⁻¹ ^ n * Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) := by
    intro m n q hq
    have h1 := spin_abs_lagPsi_le_shifted (w := 1 / 2) (by norm_num) hθ0 hθ1 hB hq.1 m
    have h2 := spin_abs_lagPsi_le_shifted (w := 1 / 2) (by norm_num) hθ0 hθ1 hB hq.2 n
    rw [abs_mul]
    have hexp : Real.exp (-2 * π * sTheta θ * q.1) * Real.exp (-2 * π * sTheta θ * q.2) =
        Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |lagPsi (1 / 2) m q.1| * |lagPsi (1 / 2) n q.2|
        ≤ (A * θ⁻¹ ^ m * Real.exp (-2 * π * sTheta θ * q.1)) *
          (A * θ⁻¹ ^ n * Real.exp (-2 * π * sTheta θ * q.2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = A ^ 2 * θ⁻¹ ^ m * θ⁻¹ ^ n *
          (Real.exp (-2 * π * sTheta θ * q.1) * Real.exp (-2 * π * sTheta θ * q.2)) := by ring
      _ = _ := by rw [hexp]
  have hΨ_int : ∀ m n : ℕ, Integrable (fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) ν := by
    intro m n
    refine Integrable.mono' (hint.const_mul (A ^ 2 * θ⁻¹ ^ m * θ⁻¹ ^ n))
      (((continuous_lagPsi (1 / 2) m).comp continuous_fst).mul
        ((continuous_lagPsi (1 / 2) n).comp continuous_snd)).aestronglyMeasurable ?_
    filter_upwards [hae] with q hq
    rw [Real.norm_eq_abs]; exact hΨ_bd m n q hq
  -- Integrability of `spinThermalX βL βR`
  obtain ⟨hbL1, hbL2⟩ := sTheta_lt_beta hθ0 hθ1 hϖL
  obtain ⟨hbR1, hbR2⟩ := sTheta_lt_beta hθ0 hθ1 hϖR
  rw [← hβL] at hbL1; rw [← hβR] at hbR1
  have hβL_pos : 0 < βL := (sTheta_pos hθ0 hθ1).trans hbL1
  have hβR_pos : 0 < βR := (sTheta_pos hθ0 hθ1).trans hbR1
  have hinvL : βL⁻¹ = (1 - ϖL) / (1 + ϖL) := by rw [hβL, inv_div]
  have hinvR : βR⁻¹ = (1 - ϖR) / (1 + ϖR) := by rw [hβR, inv_div]
  rw [← hinvL] at hbL2; rw [← hinvR] at hbR2
  have hmin1 : sTheta θ ≤ min βL βR := le_min hbL1.le hbR1.le
  have hmin2 : sTheta θ ≤ min βL⁻¹ βR⁻¹ := le_min hbL2.le hbR2.le
  have hexp_int : ∀ {γL γR : ℝ}, sTheta θ ≤ min γL γR →
      Integrable (fun q : ℝ × ℝ => Real.exp (-2 * π * (γL * q.1 + γR * q.2))) ν := by
    intro γL γR hmin
    have hC : 0 ≤ Real.exp (2 * π * B * (γL + γR - 2 * min γL γR)) *
        Real.exp (4 * π * B * (min γL γR - sTheta θ)) := by positivity
    refine Integrable.mono' (hint.const_mul (Real.exp (2 * π * B * (γL + γR - 2 * min γL γR)) *
        Real.exp (4 * π * B * (min γL γR - sTheta θ))))
      (by fun_prop : Continuous fun q : ℝ × ℝ => Real.exp (-2 * π * (γL * q.1 + γR * q.2))).aestronglyMeasurable ?_
    filter_upwards [hae] with q hq
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 := spin_exp_dom_coneB (βL := γL) (βR := γR) hB hq
    have h2 : Real.exp (-2 * π * min γL γR * (q.1 + q.2)) ≤
        Real.exp (4 * π * B * (min γL γR - sTheta θ)) *
          Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hqsum : -2 * B ≤ q.1 + q.2 := by linarith [hq.1, hq.2]
      have hprod_nn : 0 ≤ (min γL γR - sTheta θ) * (q.1 + q.2 + 2 * B) :=
        mul_nonneg (sub_nonneg.mpr hmin) (by linarith)
      have hpi : 0 < 2 * π := by positivity
      nlinarith
    calc Real.exp (-2 * π * (γL * q.1 + γR * q.2))
        ≤ Real.exp (2 * π * B * (γL + γR - 2 * min γL γR)) *
            Real.exp (-2 * π * min γL γR * (q.1 + q.2)) := h1
      _ ≤ Real.exp (2 * π * B * (γL + γR - 2 * min γL γR)) *
            (Real.exp (4 * π * B * (min γL γR - sTheta θ)) *
              Real.exp (-2 * π * sTheta θ * (q.1 + q.2))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by ring
  have hX_int : Integrable (fun q : ℝ × ℝ => spinThermalX βL βR q.1 q.2) ν := by
    have he1 := hexp_int hmin1
    have he2 := (hexp_int hmin2).const_mul ((βL * βR) ^ (-(1 / 2 : ℝ)))
    refine (he1.sub he2).congr (Eventually.of_forall fun q => ?_)
    unfold spinThermalX
    simp only [Pi.sub_apply, div_eq_inv_mul]
  -- Dominated convergence for the double series
  let F : ℕ × ℕ → ℝ × ℝ → ℝ := fun p q =>
    if Odd (p.1 + p.2) then
      ϖL ^ p.1 * ϖR ^ p.2 * (lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2)
    else 0
  have hF_int : ∀ p : ℕ × ℕ, Integrable (F p) ν := fun p => by
    dsimp only [F]
    split_ifs
    · exact (hΨ_int p.1 p.2).const_mul _
    · exact integrable_zero _ _ _
  set rL : ℝ := |ϖL| / θ
  set rR : ℝ := |ϖR| / θ
  have hrL1 : rL < 1 := (div_lt_one hθ0).mpr hϖL
  have hrR1 : rR < 1 := (div_lt_one hθ0).mpr hϖR
  set I : ℝ := ∫ q : ℝ × ℝ, Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) ∂ν
  have hI_nn : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  have hF_norm : ∀ p : ℕ × ℕ, ∫ q : ℝ × ℝ, ‖F p q‖ ∂ν ≤ (A ^ 2 * I) * (rL ^ p.1 * rR ^ p.2) := by
    intro p
    dsimp only [F]
    split_ifs
    · have hdom : ∀ᵐ q ∂ν, ‖ϖL ^ p.1 * ϖR ^ p.2 * (lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2)‖ ≤
          (A ^ 2 * (rL ^ p.1 * rR ^ p.2)) * Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) := by
        filter_upwards [hae] with q hq
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
        have h1 := hΨ_bd p.1 p.2 q hq
        have hrrL : rL ^ p.1 = |ϖL| ^ p.1 * θ⁻¹ ^ p.1 := by dsimp only [rL]; rw [div_eq_mul_inv, mul_pow]
        have hrrR : rR ^ p.2 = |ϖR| ^ p.2 * θ⁻¹ ^ p.2 := by dsimp only [rR]; rw [div_eq_mul_inv, mul_pow]
        calc |ϖL| ^ p.1 * |ϖR| ^ p.2 * |lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2|
            ≤ |ϖL| ^ p.1 * |ϖR| ^ p.2 *
                (A ^ 2 * θ⁻¹ ^ p.1 * θ⁻¹ ^ p.2 * Real.exp (-2 * π * sTheta θ * (q.1 + q.2))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (A ^ 2 * ((|ϖL| ^ p.1 * θ⁻¹ ^ p.1) * (|ϖR| ^ p.2 * θ⁻¹ ^ p.2))) *
                Real.exp (-2 * π * sTheta θ * (q.1 + q.2)) := by ring
          _ = _ := by rw [← hrrL, ← hrrR]
      have hint_le := integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (hint.const_mul _) hdom
      rw [integral_const_mul] at hint_le
      calc _ ≤ A ^ 2 * (rL ^ p.1 * rR ^ p.2) * I := hint_le
        _ = (A ^ 2 * I) * (rL ^ p.1 * rR ^ p.2) := by ring
    · simp only [norm_zero, integral_zero]
      positivity
  have hsumm : Summable fun p : ℕ × ℕ => ∫ q : ℝ × ℝ, ‖F p q‖ ∂ν := by
    have hgL : Summable (fun m : ℕ => rL ^ m) := summable_geometric_of_lt_one (by positivity) hrL1
    have hgR : Summable (fun n : ℕ => rR ^ n) := summable_geometric_of_lt_one (by positivity) hrR1
    have hprod : Summable (fun p : ℕ × ℕ => rL ^ p.1 * rR ^ p.2) :=
      hgL.mul_of_nonneg hgR (fun _ => by positivity) (fun _ => by positivity)
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hF_norm
      (hprod.mul_left _)
  have hHas := hasSum_integral_of_summable_integral_norm hF_int hsumm
  have hpt : ∀ q : ℝ × ℝ, ∑' p : ℕ × ℕ, F p q =
      spinThermalX βL βR q.1 q.2 / (2 * (1 - ϖL) ^ (1 / 2 : ℝ) * (1 - ϖR) ^ (1 / 2 : ℝ)) :=
    fun q => (spin_tensor_cayley_hasSum (hϖL.trans hθ1) (hϖR.trans hθ1) hβL hβR q.1 q.2).tsum_eq
  refine ⟨hΨ_int, hX_int, ?_⟩
  have hval : ∫ q : ℝ × ℝ, ∑' p : ℕ × ℕ, F p q ∂ν =
      (∫ q : ℝ × ℝ, spinThermalX βL βR q.1 q.2 ∂ν) /
        (2 * (1 - ϖL) ^ (1 / 2 : ℝ) * (1 - ϖR) ^ (1 / 2 : ℝ)) := by
    simp_rw [hpt]
    rw [integral_div]
  rw [hval] at hHas
  convert hHas using 1
  ext p
  dsimp only [F]
  split_ifs
  · rw [integral_const_mul]
  · simp

/-- **2D power-series uniqueness**: if `∑_{m,n} c(m, n) x^m y^n = 0` on `(-r, r)²` with absolute
summability on `ℕ × ℕ`, then `c(m, n) = 0` for all `m, n`. -/
lemma spin_double_coeff_zero {c : ℕ × ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hsumm : ∀ x y : ℝ, |x| < r → |y| < r → Summable (fun p : ℕ × ℕ => c p * (x ^ p.1 * y ^ p.2)))
    (hzero : ∀ x y : ℝ, |x| < r → |y| < r → HasSum (fun p : ℕ × ℕ => c p * (x ^ p.1 * y ^ p.2)) 0) :
    ∀ m n : ℕ, c (m, n) = 0 := by
  intro m n
  -- Fix `y` with `|y| < r`; sum over `n'` first to get a 1D power series in `x`
  have hrow : ∀ y : ℝ, |y| < r → ∀ m' : ℕ, ∑' n' : ℕ, c (m', n') * y ^ n' = 0 := by
    intro y hy
    have h1d : ∀ x : ℝ, |x| < r → HasSum (fun m' : ℕ => (∑' n' : ℕ, c (m', n') * y ^ n') * x ^ m') 0 := by
      intro x hx
      have hfib : ∀ m' : ℕ, HasSum (fun n' : ℕ => c (m', n') * (x ^ m' * y ^ n'))
          ((∑' n' : ℕ, c (m', n') * y ^ n') * x ^ m') := by
        intro m'
        have hs' : Summable (fun n' : ℕ => c (m', n') * y ^ n') := by
          have hr2 : |r / 2| < r := by rw [abs_of_pos (by linarith)]; linarith
          have hslice := (hsumm (r / 2) y hr2 hy).comp_injective
            (i := fun n' : ℕ => (m', n')) (fun _ _ h => (Prod.mk.inj h).2)
          have hpow_ne : (r / 2) ^ m' ≠ 0 := (pow_pos (by linarith) m').ne'
          refine (hslice.mul_left (((r / 2) ^ m')⁻¹)).congr fun n' => ?_
          dsimp only [Function.comp_apply]
          field_simp [hpow_ne]
        have hmul := hs'.hasSum.mul_right (x ^ m')
        convert hmul using 1
        ext n'; ring
      exact (hzero x y hx hy).prod_fiberwise hfib
    exact coeff_zero_of_hasSum_zero hr h1d
  -- Now for fixed `m`, `y ↦ ∑' n', c (m, n') * y ^ n'` vanishes on `(-r, r)`
  have hcol : ∀ y : ℝ, |y| < r → HasSum (fun n' : ℕ => c (m, n') * y ^ n') 0 := by
    intro y hy
    have hr2 : |r / 2| < r := by rw [abs_of_pos (by linarith)]; linarith
    have hslice := (hsumm (r / 2) y hr2 hy).comp_injective
      (i := fun n' : ℕ => (m, n')) (fun _ _ h => (Prod.mk.inj h).2)
    have hpow_ne : (r / 2) ^ m ≠ 0 := (pow_pos (by linarith) m).ne'
    have hs' : Summable (fun n' : ℕ => c (m, n') * y ^ n') := by
      refine (hslice.mul_left (((r / 2) ^ m)⁻¹)).congr fun n' => ?_
      dsimp only [Function.comp_apply]
      field_simp [hpow_ne]
    rw [← hrow y hy m]
    exact hs'.hasSum
  exact coeff_zero_of_hasSum_zero hr hcol n

/-- Cardy-measure version of `spin_tensor_cayley_integral`: the vacuum functional `-spinVacT a`
satisfies the exact same 2D Cayley series for all `|ϖL|, |ϖR| < θ < 1`. -/
theorem spin_tensor_cayley_vac {a θ : ℝ} (ha : 2 ≤ a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ϖL ϖR βL βR : ℝ} (hϖL : |ϖL| < θ) (hϖR : |ϖR| < θ)
    (hβL : βL = (1 + ϖL) / (1 - ϖL)) (hβR : βR = (1 + ϖR) / (1 - ϖR)) :
    (∀ m n : ℕ, Integrable (fun r : ℝ × ℝ =>
      lagPsi (1 / 2) m (r.1 ^ 2 / 2) * lagPsi (1 / 2) n (r.2 ^ 2 / 2) *
        spinV1 a r.1 * spinV1 a r.2)) ∧
    HasSum (fun p : ℕ × ℕ =>
      if Odd (p.1 + p.2) then
        ϖL ^ p.1 * ϖR ^ p.2 *
          (-spinVacT a (fun q => lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2))
      else 0)
      ((-spinThermalXVac a βL βR) /
        (2 * (1 - ϖL) ^ (1 / 2 : ℝ) * (1 - ϖR) ^ (1 / 2 : ℝ))) := by
  have hs0 : 0 < sTheta θ := sTheta_pos hθ0 hθ1
  have hβL_pos : 0 < βL := hs0.trans (by rw [hβL]; exact (sTheta_lt_beta hθ0 hθ1 hϖL).1)
  have hβR_pos : 0 < βR := hs0.trans (by rw [hβR]; exact (sTheta_lt_beta hθ0 hθ1 hϖR).1)
  -- Push forward the Cardy measure `V_1(r_L) V_1(r_R) dr_L dr_R` by `r ↦ (r_L²/2, r_R²/2)`
  let μV : Measure (ℝ × ℝ) :=
    volume.withDensity (fun r : ℝ × ℝ => ENNReal.ofReal (spinV1 a r.1 * spinV1 a r.2))
  have hV_cont : Continuous (fun r : ℝ × ℝ => spinV1 a r.1 * spinV1 a r.2) := by
    have hV1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact (hV1.comp continuous_fst).mul (hV1.comp continuous_snd)
  have hV_nn : ∀ r : ℝ × ℝ, 0 ≤ spinV1 a r.1 * spinV1 a r.2 := fun r =>
    mul_nonneg (spinV1_nonneg ha r.1) (spinV1_nonneg ha r.2)
  have hV_meas : Measurable (fun r : ℝ × ℝ => ENNReal.ofReal (spinV1 a r.1 * spinV1 a r.2)) :=
    ENNReal.measurable_ofReal.comp hV_cont.measurable
  let sq : ℝ × ℝ → ℝ × ℝ := fun r => (r.1 ^ 2 / 2, r.2 ^ 2 / 2)
  have hsq_meas : Measurable sq := by unfold sq; fun_prop
  let νC : Measure (ℝ × ℝ) := μV.map sq
  have hνC_supp : νC (spinConeB 0)ᶜ = 0 := by
    unfold νC
    rw [Measure.map_apply hsq_meas (isClosed_spinConeB 0).measurableSet.compl]
    have hemp : sq ⁻¹' (spinConeB 0)ᶜ = ∅ := by
      ext r; simp only [Set.mem_preimage, mem_compl_iff, spinConeB, neg_zero, mem_ofPred_eq,
        mem_empty_iff_false, iff_false, not_not, sq]
      exact ⟨by positivity, by positivity⟩
    rw [hemp, measure_empty]
  have hint_νC : Integrable (fun q : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (q.1 + q.2))) νC := by
    unfold νC
    rw [integrable_map_measure (by fun_prop : Continuous fun q : ℝ × ℝ =>
        Real.exp (-2 * π * sTheta θ * (q.1 + q.2))).aestronglyMeasurable hsq_meas.aemeasurable]
    unfold μV
    rw [integrable_withDensity_iff_integrable_smul' hV_meas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine (spin_gaussian_V1_prod ha hs0 hs0).1.congr (Eventually.of_forall fun r => ?_)
    simp only [Function.comp_apply, smul_eq_mul, sq, ENNReal.toReal_ofReal (hV_nn r)]
    have he : -2 * π * sTheta θ * (r.1 ^ 2 / 2 + r.2 ^ 2 / 2) =
        -π * (sTheta θ * r.1 ^ 2 + sTheta θ * r.2 ^ 2) := by ring
    rw [he]; ring
  have htc := spin_tensor_cayley_integral (B := 0) le_rfl hθ0 hθ1 hνC_supp hint_νC hϖL hϖR hβL hβR
  have hμV_int_eq : ∀ (f : ℝ × ℝ → ℝ), Continuous f →
      ∫ q : ℝ × ℝ, f q ∂νC = ∫ r : ℝ × ℝ, f (sq r) * spinV1 a r.1 * spinV1 a r.2 := by
    intro f hf
    unfold νC μV
    rw [integral_map hsq_meas.aemeasurable hf.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hV_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hV_nn r)]
    ring
  refine ⟨fun m n => ?_, ?_⟩
  · have h1 := htc.1 m n
    have hcont_mn : Continuous (fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) :=
      ((continuous_lagPsi (1 / 2) m).comp continuous_fst).mul
        ((continuous_lagPsi (1 / 2) n).comp continuous_snd)
    unfold νC μV at h1
    rw [integrable_map_measure hcont_mn.aestronglyMeasurable hsq_meas.aemeasurable,
      integrable_withDensity_iff_integrable_smul' hV_meas
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Eventually.of_forall fun r => ?_)
    simp only [Function.comp_apply, smul_eq_mul, sq, ENNReal.toReal_ofReal (hV_nn r)]
    ring
  · have hvac_eq : ∫ q : ℝ × ℝ, spinThermalX βL βR q.1 q.2 ∂νC = -spinThermalXVac a βL βR := by
      rw [hμV_int_eq _ (by unfold spinThermalX; fun_prop)]
      have h := spinVacT_thermalX ha hβL_pos hβR_pos
      unfold spinVacT spinPhiVac spinLiftTToR at h
      linarith
    have hterm_eq : ∀ m n : ℕ,
        ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂νC =
          -spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) := by
      intro m n
      have hcont_mn : Continuous (fun q : ℝ × ℝ => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2) :=
        ((continuous_lagPsi (1 / 2) m).comp continuous_fst).mul
          ((continuous_lagPsi (1 / 2) n).comp continuous_snd)
      rw [hμV_int_eq _ hcont_mn]
      unfold spinVacT spinPhiVac spinLiftTToR sq
      ring
    have hhas := htc.2.2
    rw [hvac_eq] at hhas
    convert hhas using 1
    ext p
    split_ifs
    · rw [hterm_eq p.1 p.2]
    · rfl

/-- **2D Cayley equivalence** (`dsl:tensor-cayley`): for `a ≥ 2`, `B ≥ 0`, `0 < θ < 1`, and a
positive measure `ν` on `E_B` with finite diagonal Laplace transform at `s_θ`:
local crossing `∫ X_{β_L, β_R} dν = -X_{β_L, β_R, vac}` on `(s_θ, 1/s_θ)²` holds **iff**
all odd two-variable Laguerre moments match `-spinVacT`. -/
theorem spin_tensor_cayley_iff {a B θ : ℝ} (ha : 2 ≤ a) (hB : 0 ≤ B) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ν : Measure (ℝ × ℝ)} (hν : ν (spinConeB B)ᶜ = 0)
    (hint : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * sTheta θ * (p.1 + p.2))) ν) :
    (∀ βL βR : ℝ, sTheta θ < βL → βL < 1 / sTheta θ → sTheta θ < βR → βR < 1 / sTheta θ →
      ∫ q : ℝ × ℝ, spinThermalX βL βR q.1 q.2 ∂ν = -spinThermalXVac a βL βR) ↔
    (∀ m n : ℕ, Odd (m + n) →
      ∫ q : ℝ × ℝ, lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2 ∂ν =
        -spinVacT a (fun q => lagPsi (1 / 2) m q.1 * lagPsi (1 / 2) n q.2)) := by
  constructor
  · intro hcross m n hmn
    let c : ℕ × ℕ → ℝ := fun p =>
      if Odd (p.1 + p.2) then
        (∫ q : ℝ × ℝ, lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2 ∂ν) -
          (-spinVacT a (fun q => lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2))
      else 0
    have hzero : ∀ ϖL ϖR : ℝ, |ϖL| < θ → |ϖR| < θ →
        HasSum (fun p : ℕ × ℕ => c p * (ϖL ^ p.1 * ϖR ^ p.2)) 0 := by
      intro ϖL ϖR hϖL hϖR
      set βL := (1 + ϖL) / (1 - ϖL)
      set βR := (1 + ϖR) / (1 - ϖR)
      have hbL := beta_of_varpi hθ0 hθ1 hϖL
      have hbR := beta_of_varpi hθ0 hθ1 hϖR
      have h1 := (spin_tensor_cayley_integral hB hθ0 hθ1 hν hint hϖL hϖR rfl rfl).2.2
      have h2 := (spin_tensor_cayley_vac ha hθ0 hθ1 hϖL hϖR rfl rfl).2
      have hsub := h1.sub h2
      rw [hcross βL βR hbL.1 hbL.2 hbR.1 hbR.2, sub_self] at hsub
      convert hsub using 1
      ext p; dsimp only [c]
      split_ifs <;> ring
    have h0 := spin_double_coeff_zero hθ0 (fun x y hx hy => (hzero x y hx hy).summable) hzero m n
    dsimp only [c] at h0
    simp only [hmn, ↓reduceIte] at h0
    linarith
  · intro hmom βL βR hL1 hL2 hR1 hR2
    obtain ⟨hϖL, hβL⟩ := varpi_of_beta hθ0 hθ1 hL1 hL2
    obtain ⟨hϖR, hβR⟩ := varpi_of_beta hθ0 hθ1 hR1 hR2
    have h1 := (spin_tensor_cayley_integral hB hθ0 hθ1 hν hint hϖL hϖR hβL hβR).2.2
    have h2 := (spin_tensor_cayley_vac ha hθ0 hθ1 hϖL hϖR hβL hβR).2
    have hsame : (fun p : ℕ × ℕ =>
        if Odd (p.1 + p.2) then
          ((βL - 1) / (βL + 1)) ^ p.1 * ((βR - 1) / (βR + 1)) ^ p.2 *
            ∫ q : ℝ × ℝ, lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2 ∂ν
        else 0) =
      fun p : ℕ × ℕ =>
        if Odd (p.1 + p.2) then
          ((βL - 1) / (βL + 1)) ^ p.1 * ((βR - 1) / (βR + 1)) ^ p.2 *
            (-spinVacT a (fun q => lagPsi (1 / 2) p.1 q.1 * lagPsi (1 / 2) p.2 q.2))
        else 0 := by
      ext p; split_ifs with hodd
      · rw [hmom p.1 p.2 hodd]
      · rfl
    rw [hsame] at h1
    have heq := h1.unique h2
    have h1L : 0 < 1 - (βL - 1) / (βL + 1) := by linarith [(abs_lt.1 (hϖL.trans hθ1)).2]
    have h1R : 0 < 1 - (βR - 1) / (βR + 1) := by linarith [(abs_lt.1 (hϖR.trans hθ1)).2]
    have hden : 2 * (1 - (βL - 1) / (βL + 1)) ^ (1 / 2 : ℝ) *
        (1 - (βR - 1) / (βR + 1)) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
    exact (div_left_inj₀ hden).mp heq

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_gaussian_V1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_gaussian_V1

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_gaussian_V1_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_gaussian_V1_prod

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacT_thermalX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinVacT_thermalX

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_hasSum

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_integral

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_vac

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_tensor_cayley_iff

end FormalResearch.ModularBootstrap.Spin

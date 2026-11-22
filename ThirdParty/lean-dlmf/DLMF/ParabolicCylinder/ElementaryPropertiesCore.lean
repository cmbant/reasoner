/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
-- PATCH: extracted from upstream `DLMF/ParabolicCylinder/ElementaryProperties.lean` (bjbraams/lean-DLMF,
-- commit 7edc630), lines 103-107, 109-137, 139-144, 146-149, 151-154, 156-160, 162-167, 169-172, 174-178, 180-194,
-- 196-199. The listed declarations are copied verbatim, proofs included.
-- The parameter-entire lemmas `differentiable_parabolicCylinder{Even,Odd}_order` and `parabolicCylinder{U,V}_entire_order`
-- (lines 109-137, 180-194) use `differentiable_regularizedConfluent_comp`, vendored with `DLMF/Confluent/Regularized.lean`.
-- Not extracted: the derivative conjugation lemmas and the rest of the upstream file.
module

public import DLMF.ParabolicCylinder.Basic.Wronskians
public import DLMF.Confluent.Basic.KummerContiguous
public import DLMF.Confluent.Regularized

/-!
# Parabolic cylinder functions: entire dependence in the argument, conjugation and reality

Core of `DLMF.ParabolicCylinder.ElementaryProperties` (DLMF §12.2, §12.4): the parabolic cylinder
functions `U(a,z)` and `V(a,z)` are entire in the argument `z`, they commute with complex conjugation,
and they are real for real `a` and `z` (`parabolicCylinderU_real`, `parabolicCylinderV_real`). The
statements and proofs are those of the upstream file.

Entire dependence on the parameter `a` is proved for each fixed `z` (`differentiable_parabolicCylinder{Even,Odd}_order`,
`parabolicCylinder{U,V}_entire_order`); joint smoothness of `(a, z) ↦ U(a, z)` is not derived here.
-/

public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat ComplexConjugate
namespace DLMF.Confluent

/-- Entire dependence on the argument. -/
theorem parabolicCylinderU_entire (a : ℂ) :
    Differentiable ℂ (parabolicCylinderU a) := by
  intro z
  exact (hasDerivAt_parabolicCylinderU a z).differentiableAt

/-- Powers of two commute with complex conjugation of the exponent. -/
theorem conj_two_cpow (w : ℂ) : conj ((2:ℂ) ^ w) = (2:ℂ) ^ (conj w) := by
  rw [Complex.cpow_conj _ _
      (by rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)];
          exact Real.pi_ne_zero.symm),
    map_ofNat]

/-- The even Kummer basis commutes with complex conjugation. -/
theorem conj_parabolicCylinderEven (a z : ℂ) : conj (parabolicCylinderEven a z) =
    parabolicCylinderEven (conj a) (conj z) := by
  simp [parabolicCylinderEven, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- The odd Kummer basis commutes with complex conjugation. -/
theorem conj_parabolicCylinderOdd (a z : ℂ) : conj (parabolicCylinderOdd a z) =
    parabolicCylinderOdd (conj a) (conj z) := by
  simp [parabolicCylinderOdd, conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]

/-- `U(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderU (a z : ℂ) : conj (parabolicCylinderU a z) =
    parabolicCylinderU (conj a) (conj z) := by
  simp [parabolicCylinderU, conj_parabolicCylinderEven, conj_parabolicCylinderOdd, conj_two_cpow,
      ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- `V(a,z)` commutes with complex conjugation. -/
theorem conj_parabolicCylinderV (a z : ℂ) : conj (parabolicCylinderV a z) =
    parabolicCylinderV (conj a) (conj z) := by
  simp [parabolicCylinderV, parabolicCylinderVZero, parabolicCylinderVDerivZero,
      conj_parabolicCylinderEven, conj_parabolicCylinderOdd, conj_two_cpow,
    ← Complex.Gamma_conj, map_div₀, map_ofNat]

/-- Reality on real parameters and arguments. -/
theorem parabolicCylinderU_real (a x : ℝ) :
    (parabolicCylinderU a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_parabolicCylinderU, Complex.conj_ofReal, Complex.conj_ofReal]

/-- Entire dependence on the argument. -/
theorem parabolicCylinderV_entire (a : ℂ) :
    Differentiable ℂ (parabolicCylinderV a) := by
  intro z
  exact (hasDerivAt_parabolicCylinderV a z).differentiableAt

/-- Reality on real parameters and arguments. -/
theorem parabolicCylinderV_real (a x : ℝ) :
    (parabolicCylinderV a x).im=0 := by
  rw [← Complex.conj_eq_iff_im, conj_parabolicCylinderV, Complex.conj_ofReal, Complex.conj_ofReal]

-- PATCH: extracted from upstream lines 109-137 (verbatim, proofs included)
/-- The even Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_parabolicCylinderEven_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderEven a z) := by
  unfold parabolicCylinderEven
  simp_rw [kummerM_eq_mul_regularizedHGFun Complex.one_div_two_ne_neg_natCast]
  fun_prop

/-- The odd Kummer basis is entire in the cylinder parameter. -/
theorem differentiable_parabolicCylinderOdd_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderOdd a z) := by
  unfold parabolicCylinderOdd
  simp_rw [kummerM_eq_mul_regularizedHGFun Complex.three_div_two_ne_neg_natCast]
  fun_prop

/-- Entire dependence on the parameter. -/
theorem parabolicCylinderU_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderU a z) := by
  have he := differentiable_parabolicCylinderEven_order z
  have ho := differentiable_parabolicCylinderOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold parabolicCylinderU
  fun_prop

-- PATCH: extracted from upstream lines 180-194 (verbatim, proofs included)
/-- Entire dependence on the parameter. -/
theorem parabolicCylinderV_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => parabolicCylinderV a z) := by
  have he := differentiable_parabolicCylinderEven_order z
  have ho := differentiable_parabolicCylinderOdd_order z
  have hG1 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG2 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4+a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG3 : Differentiable ℂ (fun a : ℂ => (Gamma (3/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  have hG4 : Differentiable ℂ (fun a : ℂ => (Gamma (1/4-a/2))⁻¹) :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  unfold parabolicCylinderV parabolicCylinderVZero parabolicCylinderVDerivZero
  fun_prop

end DLMF.Confluent

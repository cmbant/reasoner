import FormalResearch.FrameFree.RealRep3
import FormalResearch.FrameFree.Reversals

/-!
# `Ceilings.RealRep3` discharged

`FrameFree/RealRep3.lean` proves that every three-qubit vector is in the `GL(2,ℂ)³`-orbit of a real vector.
Here that proof discharges the hypothesis `Ceilings.RealRep3` and re-states the conditional theorems of
`Ceilings`, `M4Support`, `Unify` and `Reversals` without it.  Any remaining hypothesis (`h49`, `hle`, `hc`, ...)
is unchanged.  Nothing in `Ceilings.lean` is edited.
-/

open scoped ComplexConjugate Matrix BigOperators
open FormalResearch.FrameFree.NQubit
open FormalResearch.FrameFree

namespace FormalResearch.FrameFree.RealRep3Discharge

open Ceilings

/-- **`RealRep3`** (Dür-Vidal-Cirac), proved: the hypothesis of `Ceilings`. -/
theorem realRep3 : Ceilings.RealRep3 := RealRep3.realRep3_core

theorem FC_three_ge' (φ : Ψ 3) : nsq φ ≤ FC φ (cj φ) := FC_three_ge realRep3 φ

theorem entceiling_contract' {n : ℕ} {ψ : Ψ n} {φ : Ψ 3} (h : Contract ψ φ) : nsq φ ≤ FCΘ ψ :=
  entceiling_contract realRep3 h

theorem ceiling_lmax' (j : Fin 4) (ψ : Ψ 4) : lmax j ψ ≤ FCΘ ψ := ceiling_lmax realRep3 j ψ

theorem ceiling_half' (ψ : Ψ 4) (hψ : nsq ψ = 1) : 1 / 2 ≤ FCΘ ψ := ceiling_half realRep3 ψ hψ

theorem FCΘ_ge_three' (ψ : Ψ 3) : nsq ψ ≤ FCΘ ψ := FCΘ_ge_three realRep3 ψ

theorem FCΘ_ge_pow' (m : ℕ) (ψ : Ψ (m + 3)) : (1 / 2 : ℝ) ^ m * nsq ψ ≤ FCΘ ψ :=
  FCΘ_ge_pow realRep3 m ψ

theorem FCΘ_ge_eight' (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) :
    8 * (1 / 2 : ℝ) ^ (m + 3) ≤ FCΘ ψ := FCΘ_ge_eight realRep3 m ψ hψ

theorem normSq_ip_pv_le_FCΘ' (m : ℕ) (ψ : Ψ (m + 3)) (e : Fin (m + 3) → Fin 2 → ℂ)
    (he : ∀ i, Complex.normSq (e i 0) + Complex.normSq (e i 1) = 1) :
    Complex.normSq (NQubit.ip (pv e) ψ) ≤ FCΘ ψ := normSq_ip_pv_le_FCΘ realRep3 m ψ e he

theorem Lam_le_FCΘ' (m : ℕ) (ψ : Ψ (m + 3)) : Lam ψ ≤ FCΘ ψ := Lam_le_FCΘ realRep3 m ψ

theorem FCΘ_pos' (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) : 0 < FCΘ ψ := FCΘ_pos realRep3 m ψ hψ

theorem negLog_FC_le_EG' (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) : -Real.log (FCΘ ψ) ≤ EG ψ :=
  negLog_FC_le_EG realRep3 m ψ hψ

theorem negLog_FC_le_log2' (m : ℕ) (ψ : Ψ (m + 3)) (hψ : nsq ψ = 1) :
    -Real.log (FCΘ ψ) ≤ m * Real.log 2 := negLog_FC_le_log2 realRep3 m ψ hψ

theorem FCΘ_eq_one_of_le_three' {n : ℕ} (hn : n ≤ 3) (ψ : Ψ n) (hψ : nsq ψ = 1) : FCΘ ψ = 1 :=
  FCΘ_eq_one_of_le_three realRep3 hn ψ hψ

theorem block_FC_ge' {b : ℕ} (hb : 1 ≤ b) (φ : Ψ b) (hφ : nsq φ = 1) :
    (1 / 2 : ℝ) ^ (b - 3) ≤ FCΘ φ := block_FC_ge realRep3 hb φ hφ

theorem block_FC_pos' {b : ℕ} (hb : 1 ≤ b) (φ : Ψ b) (hφ : nsq φ = 1) : 0 < FCΘ φ :=
  block_FC_pos realRep3 hb φ hφ

theorem negLog_FC_le_producible' {m : ℕ} (hm : 3 ≤ m) {n : ℕ} {ψ : Ψ n} (h : Producible m ψ) :
    0 < FCΘ ψ ∧ -Real.log (FCΘ ψ) ≤ n * (1 - 3 / (m : ℝ)) * Real.log 2 :=
  negLog_FC_le_producible realRep3 hm h

theorem half_le_FCΘ_M4' : 1 / 2 ≤ FCΘ M4v := half_le_FCΘ_M4 realRep3

theorem M4_uncalibrated' (h49 : FKΘ M4v = 4 / 9) : FKΘ M4v < FCΘ M4v :=
  M4_uncalibrated realRep3 h49

theorem FCΘ_M4pow_ge' (m : ℕ) : (1 / 2 : ℝ) ^ (m + 1) ≤ FCΘ (M4pow m) := FCΘ_M4pow_ge realRep3 m

theorem FCΘ_M4pow_eq' (hle : FCΘ M4v ≤ 1 / 2) (m : ℕ) : FCΘ (M4pow m) = (1 / 2 : ℝ) ^ (m + 1) :=
  FCΘ_M4pow_eq realRep3 hle m

theorem M4pow_window' (hle : FCΘ M4v ≤ 1 / 2) (h49 : FKΘ M4v = 4 / 9) (m : ℕ) :
    -Real.log (FCΘ (M4pow m)) = (m + 1) * Real.log 2 ∧ (m + 1) * Real.log 2 < CK (M4pow m) :=
  M4pow_window realRep3 hle h49 m

/-! ### `M4Support`, `Unify`, `Reversals` -/

section Downstream

open Real

/-- `thm:m4support` (heavy half proved in `M4Support`): `F_C(M₄) = 1/2`, unconditionally. -/
theorem FCΘ_M4v_eq' : FCΘ M4v = 1 / 2 := M4Support.FCΘ_M4v_eq realRep3

theorem FCΘ_M4pow_eq_half_pow' (m : ℕ) : FCΘ (M4pow m) = (1 / 2 : ℝ) ^ (m + 1) :=
  M4Support.FCΘ_M4pow_eq_half_pow realRep3 m

theorem M4pow_window_of_h49' (h49 : FKΘ M4v = 4 / 9) (m : ℕ) :
    -Real.log (FCΘ (M4pow m)) = (m + 1) * Real.log 2 ∧ (m + 1) * Real.log 2 < CK (M4pow m) :=
  M4Support.M4pow_window_of_h49 realRep3 h49 m

theorem M4_uncalibrated_of_le' (h : FKΘ M4v ≤ 4 / 9) : FKΘ M4v < FCΘ M4v :=
  Unify.M4_uncalibrated_of_le realRep3 h

open Reversals in
theorem Psi8_values' (h49 : FKΘ M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ) :
    FKΘ (Psi8 θ) = 4 / 9 * ((1 + cos (2 * θ)) / 2) ∧
      FCΘ (Psi8 θ) = 1 / 2 * ((1 + cos (2 * θ)) / 2) ∧
      CK (Psi8 θ) = CK8 (cos (2 * θ)) ∧
      -Real.log (FCΘ (Psi8 θ)) = xi8 (cos (2 * θ)) :=
  Reversals.Psi8_values realRep3 h49 h0 h1 hK hC

open Reversals in
theorem eight_qubit_reversal' (h49 : FKΘ M4v ≤ 4 / 9) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) (hK : Sharing.ExchangeIndepBound θ)
    (hC : Sharing.ExchangeIndepBoundC θ) (hK4 : Sharing.ExchangeIndepBound (π / 4))
    (hC4 : Sharing.ExchangeIndepBoundC (π / 4)) (hs0 : 0 < cos (2 * θ)) (hs1 : cos (2 * θ) < 1 / 8) :
    StrictReversal (CK (Psi8 θ)) (-Real.log (FCΘ (Psi8 θ))) (CK Phi8) (-Real.log (FCΘ Phi8)) ∧
      CK (Psi8 θ) = Real.log (9 / (2 * (1 + cos (2 * θ)))) ∧
      -Real.log (FCΘ (Psi8 θ)) = Real.log (4 / (1 + cos (2 * θ))) :=
  Reversals.eight_qubit_reversal realRep3 h49 h0 h1 hK hC hK4 hC4 hs0 hs1

theorem blocks_gap' (h49 : FKΘ M4v ≤ 4 / 9) (m : ℕ) :
    CK (M4pow m) = (m + 1) * Real.log (9 / 4) ∧
      -Real.log (FCΘ (M4pow m)) = (m + 1) * Real.log 2 ∧
      CK (M4pow m) - -Real.log (FCΘ (M4pow m)) = (m + 1) * Real.log (9 / 8) :=
  Reversals.blocks_gap realRep3 h49 m

theorem blocks_exponent' (h49 : FKΘ M4v ≤ 4 / 9) (m : ℕ) (ξ : ℝ)
    (hlo : -Real.log (FCΘ (M4pow m)) ≤ ξ) (hhi : ξ ≤ (m + 1) * Real.log 2) :
    ξ = (m + 1) * Real.log 2 ∧ CK (M4pow m) - ξ = (m + 1) * Real.log (9 / 8) :=
  Reversals.blocks_exponent realRep3 h49 m ξ hlo hhi

theorem m4_exponent' (h49 : FKΘ M4v ≤ 4 / 9) (ξ : ℝ)
    (hlo : -Real.log (FCΘ M4v) ≤ ξ) (hhi : ξ ≤ Real.log 2) :
    ξ = Real.log 2 ∧ CK M4v = Real.log (9 / 4) ∧ ξ < CK M4v ∧
      CK M4v - ξ = Real.log (9 / 8) ∧
      0.1452 < 1 - ξ / CK M4v ∧ 1 - ξ / CK M4v < 0.1453 :=
  Reversals.m4_exponent realRep3 h49 ξ hlo hhi

end Downstream

end FormalResearch.FrameFree.RealRep3Discharge

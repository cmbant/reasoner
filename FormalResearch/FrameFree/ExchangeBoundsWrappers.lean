import FormalResearch.FrameFree.ExchangeBounds

/-!
# Unconditional wrappers: the exchange-law theorems without `ExchangeIndepBound(C)`

`ExchangeBounds.exchangeIndepBound(C)` prove the two independent-frame hypotheses for `0 ≤ θ ≤ π/4`.
Here the downstream theorems of `Sharing`, `Reversals`, `RealRep3Discharge` that took them as hypotheses are
restated without them (primed).  Nothing in those files is edited.  Remaining hypotheses (`h49`,
`hs0`, `hs1`, ...) are unchanged.
-/

open scoped Matrix ComplexConjugate Kronecker Real
open FormalResearch.FrameFree.Sharing FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.ExchangeBounds

section Sharing

variable {β : Type*}

/-- `thm:exchangesharing` (ii), rotation overlap: `F_K^π(ψ_{U_θ}) = cos² θ`, `0 ≤ θ ≤ π/4`. -/
theorem FKΘs_exchange_ii' (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) : FKΘs g (psiEx θ) = Real.cos θ ^ 2 :=
  FKΘs_exchange_ii g h θ (exchangeIndepBound θ h0 h1)

/-- `thm:exchangesharing` (iii), rotation overlap. -/
theorem FKΘs_exchange_iii' (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FKΘs g (psiEx θ) ∧ FKΘs g (psiEx θ) ≤ Real.cos θ ^ 2 :=
  FKΘs_exchange_iii g h θ (exchangeIndepBound θ h0 h1)

/-- `thm:exchangesharing` (ii), chiral distance. -/
theorem CKs_exchange_ii' (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) : CKs g (psiEx θ) = Real.log (2 / (1 + Real.cos (2 * θ))) :=
  CKs_exchange_ii g h θ (exchangeIndepBound θ h0 h1)

/-- `thm:exchangesharing` (iii), chiral distance. -/
theorem CKs_exchange_iii' (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) :
    Real.log (2 / (1 + Real.cos (2 * θ))) ≤ CKs g (psiEx θ) ∧
      CKs g (psiEx θ) ≤ -Real.log (max (Real.sin θ ^ 2) (kappa θ)) :=
  CKs_exchange_iii g h θ (exchangeIndepBound θ h0 h1)

/-- `√SWAP`, every pattern, rotation form (`thm:exchangesharing`, last sentence). -/
theorem CKs_sqrtSwap' (g : Fin 4 → β) :
    ((g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 4) ∧
    (¬ (g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 2) :=
  CKs_sqrtSwap g (exchangeIndepBound _ (by positivity) le_rfl)

/-- `thm:exchangesharing` (ii), filters: `F_C^π(ψ_{U_θ}) = cos² θ`, `0 ≤ θ ≤ π/4`. -/
theorem FCΘs_exchange_ii' (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) : FCΘs g (psiEx θ) = Real.cos θ ^ 2 :=
  FCΘs_exchange_ii g h θ (exchangeIndepBoundC θ h0 h1)

/-- `thm:exchangesharing` (iii), filters. -/
theorem FCΘs_exchange_iii' (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FCΘs g (psiEx θ) ∧ FCΘs g (psiEx θ) ≤ Real.cos θ ^ 2 :=
  FCΘs_exchange_iii g h θ (exchangeIndepBoundC θ h0 h1)

end Sharing

/-- `Reversals.FKΘ_psiEx`: `F_K(ψ_{U_θ}) = cos² θ`. -/
theorem FKΘ_psiEx' {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    FKΘ (psiEx θ) = Real.cos θ ^ 2 :=
  Reversals.FKΘ_psiEx (exchangeIndepBound θ h0 h1)

/-- `Reversals.FCΘ_psiEx`: `F_C(ψ_{U_θ}) = cos² θ` (`Ceilings.FCΘ`). -/
theorem FCΘ_psiEx' {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    Ceilings.FCΘ (psiEx θ) = Real.cos θ ^ 2 :=
  Reversals.FCΘ_psiEx (exchangeIndepBoundC θ h0 h1)

/-- **`thm:heis`** (`Reversals.exchange_law`) without the hypotheses: `F_C = F_K = (1+cos 2θ)/2 = cos² θ`
for `0 ≤ θ ≤ π/4`, the Weyl-side value, and calibration `-log F_C = C_K = log (2/(1+cos 2θ))`. -/
theorem exchange_law' {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    Ceilings.FCΘ (psiEx θ) = (1 + Real.cos (2 * θ)) / 2 ∧
      FKΘ (psiEx θ) = (1 + Real.cos (2 * θ)) / 2 ∧
      FKmag (dgate (fun _ => θ / 2)) = (1 + Real.cos (2 * θ)) / 2 ∧
      -Real.log (Ceilings.FCΘ (psiEx θ)) = Reversals.CKex (Real.cos (2 * θ)) ∧
      CK (psiEx θ) = Reversals.CKex (Real.cos (2 * θ)) :=
  Reversals.exchange_law h0 h1 (exchangeIndepBound θ h0 h1) (exchangeIndepBoundC θ h0 h1)

/-- `Reversals.Psi8_values` (hypothesis `RealRep3` kept) without the exchange hypotheses. -/
theorem Psi8_values' (hR : Ceilings.RealRep3) (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    FKΘ (Reversals.Psi8 θ) = 4 / 9 * ((1 + Real.cos (2 * θ)) / 2) ∧
      Ceilings.FCΘ (Reversals.Psi8 θ) = 1 / 2 * ((1 + Real.cos (2 * θ)) / 2) ∧
      CK (Reversals.Psi8 θ) = CK8 (Real.cos (2 * θ)) ∧
      -Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)) = xi8 (Real.cos (2 * θ)) :=
  Reversals.Psi8_values hR h49 h0 h1 (exchangeIndepBound θ h0 h1) (exchangeIndepBoundC θ h0 h1)

/-- `RealRep3Discharge.Psi8_values'` without the exchange hypotheses: only `h49` remains. -/
theorem Psi8_values'' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    FKΘ (Reversals.Psi8 θ) = 4 / 9 * ((1 + Real.cos (2 * θ)) / 2) ∧
      Ceilings.FCΘ (Reversals.Psi8 θ) = 1 / 2 * ((1 + Real.cos (2 * θ)) / 2) ∧
      CK (Reversals.Psi8 θ) = CK8 (Real.cos (2 * θ)) ∧
      -Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)) = xi8 (Real.cos (2 * θ)) :=
  Psi8_values' RealRep3Discharge.realRep3 h49 h0 h1

/-- `Reversals.eight_qubit_reversal` (`RealRep3` kept) without the exchange hypotheses. -/
theorem eight_qubit_reversal_of_RealRep3' (hR : Ceilings.RealRep3) (h49 : FKΘ Ceilings.M4v ≤ 4 / 9)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) (hs0 : 0 < Real.cos (2 * θ))
    (hs1 : Real.cos (2 * θ) < 1 / 8) :
    Reversals.StrictReversal (CK (Reversals.Psi8 θ)) (-Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)))
        (CK Reversals.Phi8) (-Real.log (Ceilings.FCΘ Reversals.Phi8)) ∧
      CK (Reversals.Psi8 θ) = Real.log (9 / (2 * (1 + Real.cos (2 * θ)))) ∧
      -Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)) = Real.log (4 / (1 + Real.cos (2 * θ))) :=
  Reversals.eight_qubit_reversal hR h49 h0 h1 (exchangeIndepBound θ h0 h1)
    (exchangeIndepBoundC θ h0 h1) (exchangeIndepBound _ (by positivity) le_rfl)
    (exchangeIndepBoundC _ (by positivity) le_rfl) hs0 hs1

/-- **Eight-qubit strict reversal** (`cor:calgeom-spin1extensive` (b)), with every recalled exchange
hypothesis and `RealRep3` discharged: for `0 < cos 2θ < 1/8` and `F_K(M₄) ≤ 4/9`, `(Ψ_θ, Φ)` is a strict
reversal, `C_K(Ψ_θ) = log (9/(2(1+s)))`, `-log F_C(Ψ_θ) = log (4/(1+s))`. -/
theorem eight_qubit_reversal''' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ π / 4) (hs0 : 0 < Real.cos (2 * θ)) (hs1 : Real.cos (2 * θ) < 1 / 8) :
    Reversals.StrictReversal (CK (Reversals.Psi8 θ)) (-Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)))
        (CK Reversals.Phi8) (-Real.log (Ceilings.FCΘ Reversals.Phi8)) ∧
      CK (Reversals.Psi8 θ) = Real.log (9 / (2 * (1 + Real.cos (2 * θ)))) ∧
      -Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)) = Real.log (4 / (1 + Real.cos (2 * θ))) :=
  PsiPlusKramers.eight_qubit_reversal'' h49 h0 h1 (exchangeIndepBound θ h0 h1)
    (exchangeIndepBoundC θ h0 h1) hs0 hs1

end FormalResearch.FrameFree.ExchangeBounds

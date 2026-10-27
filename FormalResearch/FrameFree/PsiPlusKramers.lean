import FormalResearch.FrameFree.Reversals

/-!
# `ψ₊` is calibrated: `F_C(ψ₊) = F_K(ψ₊) = 1/2` (Paper P, `thm:psipluskramers`)

Namespace `FormalResearch.FrameFree.PsiPlusKramers`.  Claim class: **proved**.  `ψ₊` is realised as
`psiPlus = ψ_{U_{π/4}}`, the Choi state of `√SWAP` (`Sharing.psiEx (π/4)`); it is the paper's `ψ₊` after
exchanging spins `2` and `4`, up to a phase.  The values are the `θ = π/4` case of the exchange law
(`Reversals.exchange_pi4`), whose upper bounds are the filtered-gate law at `δ = cos 2θ = 0`
(`ExchangeBounds`).  The rate `ξ_inv(ψ₊) = log 2` is `XiInv.psiplus_xi_inv`.
-/

open scoped Real
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.PsiPlusKramers

/-- `ψ₊`, realised as the Choi probe of `√SWAP`: `ψ_{U_{π/4}}`. -/
noncomputable abbrev psiPlus : Ψ 4 := Sharing.psiEx (π / 4)

/-- **`thm:psipluskramers`, values.**  `F_C(ψ₊) = F_K(ψ₊) = 1/2`. -/
theorem psiplus_kramers : Ceilings.FCΘ psiPlus = 1 / 2 ∧ FKΘ psiPlus = 1 / 2 :=
  Reversals.exchange_pi4

/-- `ψ₊` is calibrated: `F_C(ψ₊) = F_K(ψ₊)`. -/
theorem psiplus_calibrated : Ceilings.FCΘ psiPlus = FKΘ psiPlus := by
  rw [psiplus_kramers.1, psiplus_kramers.2]

/-- `C_K(ψ₊) = -log F_K(ψ₊) = log 2`. -/
theorem psiplus_CK : CK psiPlus = Real.log 2 := by
  unfold CK
  rw [psiplus_kramers.2, Real.log_div (by norm_num) (by norm_num)]
  simp

end FormalResearch.FrameFree.PsiPlusKramers

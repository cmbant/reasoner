module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.BandFacts

/-!
# Paper J, Theorem B: the part of `(D_{q_m+1})` that `thm:B` and `prop:thb-inputs` use (`StdDM`)

Source: Paper J `thmB.tex`, proof of `cor:thb-Dm` ("These are the only consequences of `(D_{q_m+1})` used in the proof of
Proposition `prop:thb-inputs` (Appendix `app:thmB`, *Freezing*)"); finding **F-DD1** of `PLAN.md`.

Claim class: **proved** (definition and the two bridges below).

## What the Theorem B chain uses of `DM F K (2 Kidx + 1)`

Everything below `ThmB` (`PropThaSpliceTwoOrders`, `PropThbInputs`, `ThmB`) takes `DM F K (2 Kidx + 1)` only to feed two lemmas:

* `stdAssump_frozen_all` (the standing assumptions `StdAssump (frozenFamily F Kidx) (paramSet K t) ..` of `sec:tha-standing`), which uses `HypMorse.frozenStandard_of_reg`, i.e. only `FrozenReg F K Kidx r`
  (the paper's `(E_Kbar)` of the frozen matrices with the budget `r >= r(max(2 Kidx - 1, 0))`, and the remainder after the jet `2 Kidx + 1`);
* `spectrumCovered_of_dm1` (the three cases of `def:tha-Psihat` exhaust the spectrum), which uses only `(D_1)`.

`StdDM F K Kidx` is exactly these two inputs.  `stdDM_of_dm`: `DM F K (2 Kidx + 1)` implies it (so the statements `ThmB`, `PropThbInputs`, `PropThaSpliceTwoOrders` with `StdDM` in place of
`DM F K (2 Kidx + 1)` are the paper's, strengthened).  `stdDM_trunc` (`CorThbDm.lean`): `(D_m)`, `1 <= m`, `Kidx = (m+1)/2` give `StdDM (truncFamily F m) K Kidx`, which is **not** true of
`DM (truncFamily F m) K (2 Kidx + 1)` (`regBudget`).

## Differences from the paper

None: the paper states the hypothesis as `(D_{q_m+1})` and notes in the proof of `cor:thb-Dm` that only these consequences are used.
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA

variable {Par : Type*} [TopologicalSpace Par]

/-- **The consequences of `(D_{2 Kidx + 1})` used by `thm:B`** (finding F-DD1): `(D_1)` and the regularity/remainder data `FrozenReg` of the frozen family, i.e. `(E_Kidx)` of the frozen matrices
`J_h^{(t)}` with the budget `r >= r(max(2 Kidx - 1, 0))` (`HypMorse.FrozenReg`, with some `r`). -/
structure StdDM (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) : Prop where
  d1 : DM F K 1
  frozen : ∃ r : ℕ, HypMorse.FrozenReg F K Kidx r

/-- `(D_{2 Kidx + 1})` on a compact set implies `StdDM`. -/
theorem stdDM_of_dm {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} (hK : IsCompact K) (hD : DM F K (2 * Kidx + 1)) :
    StdDM F K Kidx :=
  ⟨dm_mono F K (by omega) hK hD, _, HypMorse.frozenReg_of_dm hD⟩

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.stdDM_of_dm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.stdDM_of_dm

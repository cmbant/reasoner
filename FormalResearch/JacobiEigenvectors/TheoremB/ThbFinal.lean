module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftLo

/-!
# Paper J, Theorem B, L3.5c, part 17: `prop:thb-inputs` and `thm:B`

Source: Paper J `app_thmB.tex`, `prop:thb-inputs` (proof: the blocks, (I1)--(I5)), and `thmB.tex`, `thm:B`.

## Proved here

* **`propThbInputs_proved : PropThbInputs CP TB spl`** (the frozen statement of `Statements.lean`, with its own premises `1 <= m`, `Kidx = (m+1)/2`, `q = 2 Kidx`, `K` compact, `HypOn`, `DM F K (2 Kidx + 1)`, `SplicesInWindow`): from `propThbInputs_of_soft`
  with the bulk blocks (`bulk_block`), the upper soft block (`softBlockUp_proved`) and the lower soft block (`softBlockLo_proved`), for every restriction `t0' <= t0` of the chart data (F-t0).
* **`thmB_proved : ThmB CP spl`** (`thm:B`): `thmB_of_propThbInputs` applied to `propThbInputs_proved`.

## Differences from the paper

`TB : TransferBundle CP` (the transfer inputs of the charts; `TransferInputs` and `TransferInputsDn` of every chart) is a hypothesis, as in the frozen statement.  `N >= N_0` replaces `h <= h_0` (finding F-B3).

## Not formalised

The transfer inputs `TB` themselves (the primitive `C^2` regularity, lower bounds and parity of the transfer coefficients of the charts; the soft-edge part of `lem:tha-collar` (2)).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`prop:thb-inputs`**: `PropThbInputs CP TB spl`. -/
theorem propThbInputs_proved
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : PropThbInputs CP TB spl :=
  propThbInputs_of_soft CP TB spl (fun h => softBlockUp_proved (CP.restrict h) (TB.restrict h) spl) (fun h => softBlockLo_proved (CP.restrict h) (TB.restrict h) spl)

/-- **Theorem B** (`thm:B`): `ThmB CP spl`. -/
theorem thmB_proved
    (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) : ThmB CP spl :=
  thmB_of_propThbInputs CP TB spl (propThbInputs_proved CP TB spl)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThbInputs_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.propThbInputs_proved

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thmB_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thmB_proved

end FormalResearch.JacobiEigenvectors.TheoremB

end

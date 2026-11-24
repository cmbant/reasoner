module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ChartCores
public import FormalResearch.JacobiEigenvectors.Assembly.ThmA
public import FormalResearch.JacobiEigenvectors.TheoremB.CorThbFinal

/-!
# Paper J: the headline theorems from the chart cores

`ChartCores` (`Charts/ChartCores.lean`) is the chart data with every derivable field removed; `ChartInputs.ofCore` builds the chart
inputs.  The headlines keep their statements (on `ChartInputs`, `ChartPair`); the `_of_core` forms below state them for the charts of the
cores.

* `thmAii_of_core`: `ThmAii` (thm:A (ii)) for `ChartInputs.ofCore D`.  No premise beyond the statement's own (`D` carries the core
  data and the standing assumptions `SoftEdgeCore.FamilyInputs` of the soft families).
* `ChartPairCores`, `ChartPair.ofCores`: the order-`m` and order-`(m+1)` cores with the link fields of `ChartPair`.
* `thmB_of_core`, `corFermions_of_core`: `ThmB` (thm:B) and `CorFermions` (cor:fermions) for `ChartPair.ofCores`, given the transfer
  bundle `TB`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA FormalResearch.JacobiEigenvectors.TheoremB

/-- The coordinates of the chart of a core are those of the core. -/
theorem SoftEdgeChart.ofCore_coords {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
    (C : SoftEdgeCore F P m q pcU pcV Lm) (hF : C.FamilyInputs) (N2 : ℕ) (h2 : C.chartN0 hF ≤ N2) :
    (SoftEdgeChart.ofCore C hF N2 h2).uc = C.uc ∧ (SoftEdgeChart.ofCore C hF N2 h2).δ0 = C.δ0 ∧
      (SoftEdgeChart.ofCore C hF N2 h2).η = C.η ∧ (SoftEdgeChart.ofCore C hF N2 h2).zeta = C.zeta ∧
      (SoftEdgeChart.ofCore C hF N2 h2).muS = C.muS := by
  have h := SoftEdgeChart.ofCore_core C hF N2 h2
  have e1 := congrArg SoftEdgeCore.uc h
  have e2 := congrArg SoftEdgeCore.δ0 h
  have e3 := congrArg SoftEdgeCore.η h
  have e4 := congrArg SoftEdgeCore.zeta h
  have e5 := congrArg SoftEdgeCore.muS h
  exact ⟨e1, e2, e3, e4, e5⟩

/-- Two orders of cores with the link fields of `ChartPair` (the same bulk blocks, fold, collar width, window and shifts at order `m` and `m + 1`). -/
structure ChartPairCores {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {cPC CPC : ℝ} where
  D0 : ChartCores F K Kidx t0 m q cPC CPC
  D1 : ChartCores F K Kidx t0 (m + 1) q cPC CPC
  nb_eq : D1.nb = D0.nb
  lo_eq : ∀ ν, D1.lo ν = D0.lo (Fin.cast nb_eq ν)
  hi_eq : ∀ ν, D1.hi ν = D0.hi (Fin.cast nb_eq ν)
  J_eq : D1.Jlo = D0.Jlo ∧ D1.Jhi = D0.Jhi
  soft_up_eq : D1.softUpL.uc = D0.softUpL.uc ∧ D1.softUpL.δ0 = D0.softUpL.δ0 ∧ D1.softUpL.η = D0.softUpL.η ∧
    D1.softUpL.zeta = D0.softUpL.zeta ∧ D1.softUpL.muS = D0.softUpL.muS
  soft_lo_eq : D1.softLoL.uc = D0.softLoL.uc ∧ D1.softLoL.δ0 = D0.softLoL.δ0 ∧ D1.softLoL.η = D0.softLoL.η ∧
    D1.softLoL.zeta = D0.softLoL.zeta ∧ D1.softLoL.muS = D0.softLoL.muS

/-- **The chart pair of a pair of cores.** -/
def ChartPair.ofCores {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {cPC CPC : ℝ} (D : ChartPairCores (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (cPC := cPC) (CPC := CPC)) :
    ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := pcU) (V := pcV) (cPC := cPC) (CPC := CPC) where
  CI0 := ChartInputs.ofCore D.D0
  CI1 := ChartInputs.ofCore D.D1
  nb_eq := D.nb_eq
  lo_eq := D.lo_eq
  hi_eq := D.hi_eq
  J_eq := D.J_eq
  soft_up_eq := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := SoftEdgeChart.ofCore_coords D.D0.softUpL D.D0.fam_upL D.D0.Nup (le_max_left _ _)
    obtain ⟨b1, b2, b3, b4, b5⟩ := SoftEdgeChart.ofCore_coords D.D1.softUpL D.D1.fam_upL D.D1.Nup (le_max_left _ _)
    obtain ⟨c1, c2, c3, c4, c5⟩ := D.soft_up_eq
    exact ⟨(b1.trans c1).trans a1.symm, (b2.trans c2).trans a2.symm, (b3.trans c3).trans a3.symm, (b4.trans c4).trans a4.symm,
      (b5.trans c5).trans a5.symm⟩
  soft_lo_eq := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := SoftEdgeChart.ofCore_coords D.D0.softLoL D.D0.fam_loL D.D0.Nlo (le_max_left _ _)
    obtain ⟨b1, b2, b3, b4, b5⟩ := SoftEdgeChart.ofCore_coords D.D1.softLoL D.D1.fam_loL D.D1.Nlo (le_max_left _ _)
    obtain ⟨c1, c2, c3, c4, c5⟩ := D.soft_lo_eq
    exact ⟨(b1.trans c1).trans a1.symm, (b2.trans c2).trans a2.symm, (b3.trans c3).trans a3.symm, (b4.trans c4).trans a4.symm,
      (b5.trans c5).trans a5.symm⟩

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {cPC CPC : ℝ}

/-- **thm:A (ii) from the chart cores**: `ThmAii` for the charts `ChartInputs.ofCore D`. -/
theorem thmAii_of_core (D : ChartCores F K Kidx t0 m (2 * Kidx) cPC CPC) :
    ThmAii F K m Kidx t0 pcU pcV cPC CPC (ChartInputs.ofCore D) :=
  thmAii_proved (ChartInputs.ofCore D)

/-- **thm:B from the chart cores**: `ThmB` for the chart pair of `D`, given the transfer bundle. -/
theorem thmB_of_core (D : ChartPairCores (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle (ChartPair.ofCores D)) (spl : Fin (ChartPair.ofCores D).CI0.nb → ℝ) :
    ThmB (ChartPair.ofCores D) spl :=
  thmB_proved (ChartPair.ofCores D) TB spl

/-- **cor:fermions from the chart cores**. -/
theorem corFermions_of_core (D : ChartPairCores (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle (ChartPair.ofCores D)) (spl : Fin (ChartPair.ofCores D).CI0.nb → ℝ) :
    CorFermions (ChartPair.ofCores D) spl :=
  corFermions_proved (ChartPair.ofCores D) TB spl

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.ChartInputs.ofCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.ChartInputs.ofCore

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmAii_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmAii_of_core

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.thmB_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.thmB_of_core

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.corFermions_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.corFermions_of_core

end FormalResearch.JacobiEigenvectors.Charts

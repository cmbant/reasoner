module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.ChartRestrict
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.5c, part 3: restriction of a chart pair and of the transfer bundle to `t0' <= t0` (finding F-t0)

The standing assumptions `StdAssump (frozenFamily F Kidx) (paramSet K t) ..` hold only for `t <= t1` (`stdAssump_frozen_all`), while the chart data of `PropThbInputs` live on `paramSet K t0`.  As for `ThmAii`
(`thmAii_of_restrict`) the assembly is done for the restricted data and transported back.

* `TransferInputs.restrict`, `TransferInputsDn.restrict`: every field is `forall mu in P`, so the transfer inputs restrict to `P' <= P` (same data).
* `ChartPair.restrict`, `TransferBundle.restrict`: the chart pair (`ChartInputs.restrict` of both orders) and its transfer bundle on `paramSet K t0'`.
* `compMatrix_restrict` (`rfl`): the comparison matrices of the restricted data are those of the original ones; `ChartPair.restrict_splicesInWindow`.

Differences from the paper: none (the paper restricts silently).  Not formalised: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- Restriction of the transfer inputs of an upward chart to a smaller parameter set. -/
def _root_.FormalResearch.JacobiEigenvectors.Charts.TransferInputs.restrict {F : SymbolFamily Par} {P P' : Set Par} {Jlo Jhi : Par → ℝ} {m : ℕ}
    {chain0 chain1 : Par → ℝ → ℕ → LadderData} {patch : ℕ} {ulo uhi : Par → ℝ}
    (TI : TransferInputs F P Jlo Jhi m chain0 chain1 patch ulo uhi) (h : P' ⊆ P) : TransferInputs F P' Jlo Jhi m chain0 chain1 patch ulo uhi :=
  { TI with
    consts_pos := ⟨fun μ hμ => TI.consts_pos.1 μ (h hμ), TI.consts_pos.2⟩
    same_ladder := fun μ hμ => TI.same_ladder μ (h hμ)
    parity_A := fun μ hμ => TI.parity_A μ (h hμ)
    parity_B := fun μ hμ => TI.parity_B μ (h hμ)
    reg_t11 := fun μ hμ => TI.reg_t11 μ (h hμ)
    reg_t12 := fun μ hμ => TI.reg_t12 μ (h hμ)
    reg_A1 := fun μ hμ => TI.reg_A1 μ (h hμ)
    reg_B1 := fun μ hμ => TI.reg_B1 μ (h hμ)
    reg_κ := fun μ hμ => TI.reg_κ μ (h hμ)
    t12_lb := fun μ hμ => TI.t12_lb μ (h hμ)
    alpha_lb := fun μ hμ => TI.alpha_lb μ (h hμ)
    omega_pos_le := fun μ hμ => TI.omega_pos_le μ (h hμ) }

/-- Restriction of the transfer inputs of a downward chart to a smaller parameter set. -/
def _root_.FormalResearch.JacobiEigenvectors.Charts.TransferInputsDn.restrict {F : SymbolFamily Par} {P P' : Set Par} {Jlo Jhi : Par → ℝ} {m : ℕ}
    {chain0 chain1 : Par → ℝ → ℕ → LadderData} {patch : ℕ} {ulo uhi : Par → ℝ}
    (TI : TransferInputsDn F P Jlo Jhi m chain0 chain1 patch ulo uhi) (h : P' ⊆ P) : TransferInputsDn F P' Jlo Jhi m chain0 chain1 patch ulo uhi :=
  { TI with
    consts_pos := ⟨fun μ hμ => TI.consts_pos.1 μ (h hμ), TI.consts_pos.2⟩
    same_ladder := fun μ hμ => TI.same_ladder μ (h hμ)
    parity_A := fun μ hμ => TI.parity_A μ (h hμ)
    parity_B := fun μ hμ => TI.parity_B μ (h hμ)
    reg_t11 := fun μ hμ => TI.reg_t11 μ (h hμ)
    reg_t12 := fun μ hμ => TI.reg_t12 μ (h hμ)
    reg_A1 := fun μ hμ => TI.reg_A1 μ (h hμ)
    reg_B1 := fun μ hμ => TI.reg_B1 μ (h hμ)
    reg_κ := fun μ hμ => TI.reg_κ μ (h hμ)
    t12_lb := fun μ hμ => TI.t12_lb μ (h hμ)
    alpha_lb := fun μ hμ => TI.alpha_lb μ (h hμ)
    omega_pos_le := fun μ hμ => TI.omega_pos_le μ (h hμ) }

section Pair

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The chart pair restricted to `t0' ≤ t0`.** -/
def ChartPair.restrict (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    {t0' : ℝ} (h : t0' ≤ t0) :
    ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0') (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC) where
  CI0 := CP.CI0.restrict h
  CI1 := CP.CI1.restrict h
  nb_eq := CP.nb_eq
  lo_eq := CP.lo_eq
  hi_eq := CP.hi_eq
  J_eq := CP.J_eq
  soft_up_eq := CP.soft_up_eq
  soft_lo_eq := CP.soft_lo_eq

/-- **The transfer bundle restricted to `t0' ≤ t0`.** -/
def TransferBundle.restrict {CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC)}
    (TB : TransferBundle CP) {t0' : ℝ} (h : t0' ≤ t0) : TransferBundle (CP.restrict h) where
  bulkL := fun ν => (TB.bulkL ν).restrict (paramSet_mono K h)
  bulkR := fun ν => (TB.bulkR ν).restrict (paramSet_mono K h)
  softUpL := TB.softUpL.restrict (paramSet_mono K h)
  softUpR := TB.softUpR.restrict (paramSet_mono K h)
  softLoL := TB.softLoL.restrict (paramSet_mono K h)
  softLoR := TB.softLoR.restrict (paramSet_mono K h)

theorem compMatrix_restrict (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) {t0' : ℝ} (h : t0' ≤ t0) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (X : Fin (N + 1) → ℝ) : compMatrix (CI.restrict h) spl μ N X = compMatrix CI spl μ N X := rfl

theorem ChartPair.restrict_splicesInWindow (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    {t0' : ℝ} (h : t0' ≤ t0) (spl : Fin CP.CI0.nb → ℝ) (hs : CP.SplicesInWindow spl) : (CP.restrict h).SplicesInWindow spl := hs

end Pair

end FormalResearch.JacobiEigenvectors.TheoremB

end

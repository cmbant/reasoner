module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs
public import FormalResearch.JacobiEigenvectors.Charts.SoftEdgeCore
public import FormalResearch.JacobiEigenvectors.Charts.PCActual

/-!
# Paper J, charts: `ChartInputs` from the cores

`ChartCores` is `ChartInputs` for the model pair `pcU, pcV` with every chart replaced by its core (`BulkWeberCore`, `SoftEdgeCore`), the
Layer-4 envelope premise `PCEnvelopeFacts` in place of `ParabolicCylinderFacts`, and the standing assumptions `SoftEdgeCore.FamilyInputs`
of the four soft families.  `ChartInputs.ofCore` builds the `ChartInputs`: each chart is `BulkWeberChart.ofCore` / `SoftEdgeChart.ofCore`,
the soft pairs at a common `N0` (so that `SoftMirror` holds), and the covering, overlap and mirror clauses transfer from the cores
(`ofCore` changes only `N0`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Setting

/-- `SoftMirror` for cores: `u_c^R = L - u_c`, `zeta_R(-x) = -zeta(x)`, the same shifts, `eta`, `delta_0` and `N_0`. -/
def SoftEdgeCore.Mirror {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (CL : SoftEdgeCore F P m q U V Lm) (CR : SoftEdgeCore (mirrorFamily F) P m q U V Lm) : Prop :=
  (∀ p ∈ P, CR.uc p = F.L - CL.uc p) ∧ (∀ p ∈ P, ∀ α x, CR.zeta p α (-x) = -CL.zeta p α x) ∧
    (∀ r, ∀ p ∈ P, ∀ α, CR.muS r p α = CL.muS r p α) ∧ CR.η = CL.η ∧ CR.δ0 = CL.δ0 ∧ CR.N0 = CL.N0

/-- **The chart hypotheses at the level of cores** (see the module docstring); the fields mirror those of `ChartInputs`. -/
structure ChartCores {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) (t0 : ℝ)
    (m q : ℕ) (cPC CPC : ℝ) where
  he : PCEnvelopeFacts pcU pcV cPC CPC
  Jlo : ℝ
  Jhi : ℝ
  nb : ℕ
  lo : Fin nb → ℝ
  hi : Fin nb → ℝ
  bulkL : (ν : Fin nb) → BulkWeberCore (frozenFamily F Kidx) (paramSet K t0) (lo ν) (hi ν) m pcU pcV
  bulkR : (ν : Fin nb) → BulkWeberCore (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) (lo ν) (hi ν) m pcU pcV
  softUpL : SoftEdgeCore (frozenFamily F Kidx) (paramSet K t0) m q pcU pcV (fun _ => 1)
  softUpR : SoftEdgeCore (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) m q pcU pcV (fun _ => 1)
  softLoL : SoftEdgeCore (negFamily (frozenFamily F Kidx)) (paramSet K t0) m q pcU pcV (fun _ => 1)
  softLoR : SoftEdgeCore (mirrorFamily (negFamily (frozenFamily F Kidx))) (paramSet K t0) m q pcU pcV (fun _ => 1)
  fam_upL : softUpL.FamilyInputs
  fam_upR : softUpR.FamilyInputs
  fam_loL : softLoL.FamilyInputs
  fam_loR : softLoR.FamilyInputs
  overlap_match : ∀ ν, (bulkR ν).c = F.L - (bulkL ν).c' ∧ (bulkR ν).c' = F.L - (bulkL ν).c
  mirror_up : softUpL.Mirror softUpR
  mirror_lo : softLoL.Mirror softLoR
  cover_bulk : ∀ X, Jlo ≤ X → X ≤ Jhi → ∃ ν, lo ν ≤ X ∧ X ≤ hi ν ∧ (lo ν < X ∨ lo ν = Jlo) ∧ (X < hi ν ∨ hi ν = Jhi)
  blocks_in_J : ∀ ν, Jlo ≤ lo ν ∧ lo ν ≤ hi ν ∧ hi ν ≤ Jhi
  cover : ∀ p ∈ paramSet K t0,
    (frozenFamily F Kidx).bandLo p < Jlo ∧ Jlo ≤ Jhi ∧ Jhi < (frozenFamily F Kidx).bandHi p ∧
    (frozenFamily F Kidx).bandHi p < Jhi + softUpL.δ0 ∧ Jlo - softLoL.δ0 < (frozenFamily F Kidx).bandLo p

namespace ChartCores

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {cPC CPC : ℝ}
  (D : ChartCores F K Kidx t0 m q cPC CPC)

/-- the common `N0` threshold of the two soft pairs. -/
def Nup : ℕ := max (D.softUpL.chartN0 D.fam_upL) (D.softUpR.chartN0 D.fam_upR)

def Nlo : ℕ := max (D.softLoL.chartN0 D.fam_loL) (D.softLoR.chartN0 D.fam_loR)

end ChartCores

/-- A mirror pair of cores gives a mirror pair of charts, built at a common threshold. -/
theorem SoftEdgeChart.ofCore_mirror {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
    {CL : SoftEdgeCore F P m q pcU pcV Lm} {CR : SoftEdgeCore (mirrorFamily F) P m q pcU pcV Lm}
    (hM : CL.Mirror CR) (hL : CL.FamilyInputs) (hR : CR.FamilyInputs) (N2 : ℕ)
    (h2L : CL.chartN0 hL ≤ N2) (h2R : CR.chartN0 hR ≤ N2) :
    SoftMirror (SoftEdgeChart.ofCore CL hL N2 h2L) (SoftEdgeChart.ofCore CR hR N2 h2R) := by
  have eL := SoftEdgeChart.ofCore_core CL hL N2 h2L
  have eR := SoftEdgeChart.ofCore_core CR hR N2 h2R
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hM
  refine ⟨fun p hp => ?_, fun p hp α x => ?_, fun r p hp α => ?_, ?_, ?_, ?_⟩
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).uc = (CR.raiseN0 N2).uc from congrArg SoftEdgeCore.uc eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).uc = (CL.raiseN0 N2).uc from congrArg SoftEdgeCore.uc eL]
    exact h1 p hp
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).zeta = (CR.raiseN0 N2).zeta from congrArg SoftEdgeCore.zeta eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).zeta = (CL.raiseN0 N2).zeta from congrArg SoftEdgeCore.zeta eL]
    exact h2 p hp α x
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).muS = (CR.raiseN0 N2).muS from congrArg SoftEdgeCore.muS eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).muS = (CL.raiseN0 N2).muS from congrArg SoftEdgeCore.muS eL]
    exact h3 r p hp α
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).η = (CR.raiseN0 N2).η from congrArg SoftEdgeCore.η eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).η = (CL.raiseN0 N2).η from congrArg SoftEdgeCore.η eL]
    exact h4
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).δ0 = (CR.raiseN0 N2).δ0 from congrArg SoftEdgeCore.δ0 eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).δ0 = (CL.raiseN0 N2).δ0 from congrArg SoftEdgeCore.δ0 eL]
    exact h5
  · rw [show (SoftEdgeChart.ofCore CR hR N2 h2R).N0 = (CR.raiseN0 N2).N0 from congrArg SoftEdgeCore.N0 eR,
      show (SoftEdgeChart.ofCore CL hL N2 h2L).N0 = (CL.raiseN0 N2).N0 from congrArg SoftEdgeCore.N0 eL]
    show max CR.N0 N2 = max CL.N0 N2
    rw [h6]

/-- `ofCore` keeps the window half-width. -/
theorem SoftEdgeChart.ofCore_δ0 {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {Lm : ℝ → ℝ}
    (C : SoftEdgeCore F P m q pcU pcV Lm) (hF : C.FamilyInputs) (N2 : ℕ) (h2 : C.chartN0 hF ≤ N2) :
    (SoftEdgeChart.ofCore C hF N2 h2).δ0 = C.δ0 := by
  have h := congrArg SoftEdgeCore.δ0 (SoftEdgeChart.ofCore_core C hF N2 h2)
  exact h

/-- **`ChartInputs` from the cores.** -/
def ChartInputs.ofCore {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ}
    {cPC CPC : ℝ} (D : ChartCores F K Kidx t0 m q cPC CPC) : ChartInputs F K Kidx t0 m q pcU pcV cPC CPC where
  pc := ParabolicCylinderFacts.ofEnvelope D.he
  Jlo := D.Jlo
  Jhi := D.Jhi
  nb := D.nb
  lo := D.lo
  hi := D.hi
  bulkL := fun ν => BulkWeberChart.ofCore (D.bulkL ν)
  bulkR := fun ν => BulkWeberChart.ofCore (D.bulkR ν)
  softUpL := SoftEdgeChart.ofCore D.softUpL D.fam_upL D.Nup (le_max_left _ _)
  softUpR := SoftEdgeChart.ofCore D.softUpR D.fam_upR D.Nup (le_max_right _ _)
  softLoL := SoftEdgeChart.ofCore D.softLoL D.fam_loL D.Nlo (le_max_left _ _)
  softLoR := SoftEdgeChart.ofCore D.softLoR D.fam_loR D.Nlo (le_max_right _ _)
  overlap_match := D.overlap_match
  mirror_up := SoftEdgeChart.ofCore_mirror D.mirror_up _ _ _ _ _
  mirror_lo := SoftEdgeChart.ofCore_mirror D.mirror_lo _ _ _ _ _
  cover_bulk := D.cover_bulk
  blocks_in_J := D.blocks_in_J
  cover := fun p hp => by
    have := D.cover p hp
    have h1 := SoftEdgeChart.ofCore_δ0 D.softUpL D.fam_upL D.Nup (le_max_left _ _)
    have h2 := SoftEdgeChart.ofCore_δ0 D.softLoL D.fam_loL D.Nlo (le_max_left _ _)
    obtain ⟨c1, c2, c3, c4, c5⟩ := this
    exact ⟨c1, c2, c3, by rw [h1]; exact c4, by rw [h2]; exact c5⟩

end FormalResearch.JacobiEigenvectors.Charts

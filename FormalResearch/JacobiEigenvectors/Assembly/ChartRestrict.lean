module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumRestrict
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs

/-!
# Paper J, assembly: restriction of the chart data to a smaller parameter set (`ChartInputs.restrict`, finding F-t0)

The chart hypotheses of `ChartInputs F K Kidx t0` are statements for all `p` in `paramSet K t0 = K x [-t0, t0]`; the standing assumptions `StdAssump (frozenFamily F Kidx) (paramSet K t') Kd r`
(the premise of `PropThaW`, `PropThaW2`) hold only for `t' <= t1` (`frozenStandard`).  Every field is a `forall p in P` statement or data, so the charts restrict to `t0' <= t0`.

* `SoftEdgeChart.restrictSub`: every `P`-dependent field of a soft chart (**a new `P`-dependent field of `SoftEdgeChart` must be added here**).
* `ChartInputs.restrict`: the bulk charts by `BulkWeberChart.restrictSub` (`TheoremA/SpectrumRestrict.lean`), the soft charts by the above, the covering clauses by `paramSet K t0' <= paramSet K t0`.
* `psiHatVec_restrict`, `envVec_restrict`: the comparison vectors and envelopes are unchanged (definitionally), so a statement about them for the restricted charts is one for the original ones.

Differences from the paper: none (the paper restricts silently: "for `t_0` small"). Not formalised: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Setting

/-- Restriction of a soft chart to a smaller parameter set. -/
def SoftEdgeChart.restrictSub {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P P' : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
    (C : SoftEdgeChart F P m q U V Lm) (h : P' ⊆ P) : SoftEdgeChart F P' m q U V Lm :=
  { C with
    uc_spec := fun μ hμ => C.uc_spec μ (h hμ)
    ucη_in := fun μ hμ => C.ucη_in μ (h hμ)
    zeta_deriv := fun μ hμ => C.zeta_deriv μ (h hμ)
    zeta_alpha := fun μ hμ => C.zeta_alpha μ (h hμ)
    muS_bd := fun r hr μ hμ => C.muS_bd r hr μ (h hμ)
    zeta_far := fun μ hμ => C.zeta_far μ (h hμ)
    zeta_far_out := fun μ hμ => C.zeta_far_out μ (h hμ)
    mu0_zero := fun μ hμ => C.mu0_zero μ (h hμ)
    mu0_deriv := fun μ hμ => C.mu0_deriv μ (h hμ)
    mu0_S0 := fun μ hμ => C.mu0_S0 μ (h hμ)
    Y_forb := fun μ hμ => C.Y_forb μ (h hμ)
    matchF_soft := fun μ hμ => C.matchF_soft μ (h hμ)
    shapeW := fun μ hμ => C.shapeW μ (h hμ)
    validW := fun μ hμ => C.validW μ (h hμ)
    A_bondW := fun μ hμ => C.A_bondW μ (h hμ)
    Q_diagW := fun μ hμ => C.Q_diagW μ (h hμ)
    dd_sqrtW := fun μ hμ => C.dd_sqrtW μ (h hμ)
    omega_sqrtW := fun μ hμ => C.omega_sqrtW μ (h hμ)
    wfW_eq := fun μ hμ => C.wfW_eq μ (h hμ)
    theta_leW := fun μ hμ => C.theta_leW μ (h hμ)
    W_defW := fun μ hμ => C.W_defW μ (h hμ)
    M_defW := fun μ hμ => C.M_defW μ (h hμ)
    seed_posW := fun μ hμ => C.seed_posW μ (h hμ)
    patch1_eq := fun μ hμ => C.patch1_eq μ (h hμ)
    shape := fun μ hμ => C.shape μ (h hμ)
    switch_in := fun μ hμ => C.switch_in μ (h hμ)
    valid := fun μ hμ => C.valid μ (h hμ)
    A_bond := fun μ hμ => C.A_bond μ (h hμ)
    Q_diag := fun μ hμ => C.Q_diag μ (h hμ)
    shared_PC := fun μ hμ => C.shared_PC μ (h hμ)
    d2_PC := fun μ hμ => C.d2_PC μ (h hμ)
    wf2_eq := fun μ hμ => C.wf2_eq μ (h hμ)
    wf3_eq := fun μ hμ => C.wf3_eq μ (h hμ)
    W1_def := fun μ hμ => C.W1_def μ (h hμ)
    M1_def := fun μ hμ => C.M1_def μ (h hμ)
    W2_def := fun μ hμ => C.W2_def μ (h hμ)
    W3_def := fun μ hμ => C.W3_def μ (h hμ)
    M2_def := fun μ hμ => C.M2_def μ (h hμ)
    theta_le := fun μ hμ => C.theta_le μ (h hμ)
    bondA_le := fun μ hμ => C.bondA_le μ (h hμ)
    grow_gap := fun μ hμ => C.grow_gap μ (h hμ)
    collar_lbW := fun μ hμ => C.collar_lbW μ (h hμ)
    ratio2 := fun μ hμ => C.ratio2 μ (h hμ)
    ratioM := fun μ hμ => C.ratioM μ (h hμ)
    corr_PC := fun μ hμ => C.corr_PC μ (h hμ)
    zeta_sign_out := fun μ hμ => C.zeta_sign_out μ (h hμ)
    mu0_slope := fun μ hμ => C.mu0_slope μ (h hμ)
    lb_weber := fun μ hμ => C.lb_weber μ (h hμ)
    lb_pc := fun μ hμ => C.lb_pc μ (h hμ)
    lamL_cont := fun μ hμ => C.lamL_cont μ (h hμ)
    grow3 := fun μ hμ => C.grow3 μ (h hμ)
    zeta_T := fun μ hμ => C.zeta_T μ (h hμ)
    Y_le := by
      obtain ⟨CY, hY⟩ := C.Y_le
      exact ⟨CY, fun μ hμ => hY μ (h hμ)⟩
    corr_leadW := by
      obtain ⟨cg, Cg, hcg, g0, hg⟩ := C.corr_leadW
      exact ⟨cg, Cg, hcg, g0, fun μ hμ => hg μ (h hμ)⟩
    AA2_ratio := by
      obtain ⟨CAl, hCAl, hA⟩ := C.AA2_ratio
      exact ⟨CAl, hCAl, fun μ hμ => hA μ (h hμ)⟩ }

lemma paramSet_mono {Par : Type*} (K : Set Par) {t0 t0' : ℝ} (h : t0' ≤ t0) : paramSet K t0' ⊆ paramSet K t0 :=
  Set.prod_mono subset_rfl (Set.Icc_subset_Icc (by linarith) h)

/-- **`ChartInputs.restrict`**: the chart inputs on `paramSet K t0` restrict to `paramSet K t0'` for `t0' <= t0` (same blocks, same constants). -/
def ChartInputs.restrict {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) {t0' : ℝ} (h : t0' ≤ t0) : ChartInputs F K Kidx t0' m q U V cPC CPC where
  pc := CI.pc
  Jlo := CI.Jlo
  Jhi := CI.Jhi
  nb := CI.nb
  lo := CI.lo
  hi := CI.hi
  bulkL := fun ν => (CI.bulkL ν).restrictSub (paramSet_mono K h)
  bulkR := fun ν => (CI.bulkR ν).restrictSub (paramSet_mono K h)
  softUpL := CI.softUpL.restrictSub (paramSet_mono K h)
  softUpR := CI.softUpR.restrictSub (paramSet_mono K h)
  softLoL := CI.softLoL.restrictSub (paramSet_mono K h)
  softLoR := CI.softLoR.restrictSub (paramSet_mono K h)
  overlap_match := CI.overlap_match
  mirror_up := ⟨fun p hp => CI.mirror_up.1 p (paramSet_mono K h hp), fun p hp => CI.mirror_up.2.1 p (paramSet_mono K h hp),
    fun r p hp => CI.mirror_up.2.2.1 r p (paramSet_mono K h hp), CI.mirror_up.2.2.2.1, CI.mirror_up.2.2.2.2.1, CI.mirror_up.2.2.2.2.2⟩
  mirror_lo := ⟨fun p hp => CI.mirror_lo.1 p (paramSet_mono K h hp), fun p hp => CI.mirror_lo.2.1 p (paramSet_mono K h hp),
    fun r p hp => CI.mirror_lo.2.2.1 r p (paramSet_mono K h hp), CI.mirror_lo.2.2.2.1, CI.mirror_lo.2.2.2.2.1, CI.mirror_lo.2.2.2.2.2⟩
  cover_bulk := CI.cover_bulk
  blocks_in_J := CI.blocks_in_J
  cover := fun p hp => CI.cover p (paramSet_mono K h hp)

end FormalResearch.JacobiEigenvectors.Charts

end

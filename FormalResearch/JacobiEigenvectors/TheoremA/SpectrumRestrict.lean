module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssembly
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhase

/-!
# Paper J, Layer 2: shrinking the freezing range `t0` (finding F-t0, for the assembly of `thm:smo-spec`)

Source: `thmA.tex` sec:tha-standing ("there is `t0 > 0` such that the frozen family satisfies `(E_K)`, (H1)--(H3) uniformly in `|t| <= t0`"); `Charts/ChartInputs.lean` (finding F-t0).

The chart data of `ThmSmoSpec` live on `paramSet K t0` with `t0` *given*, while the standing assumptions of the frozen family (`frozenStandard_of_reg`) hold only for `t0` below some `t1`.
Every statement about the chart data is a statement for all parameters of `paramSet K t0` and all `|t| <= t0`, so it restricts to `t0' <= t0`.  This module proves the restrictions that the assembly uses:

* `jetRegJ_restrict`, `sigma_bdd_restrict`: `JetRegJ` and the uniform `C^{2M+1}` norm bound of a phase coefficient on `I x [-t0, t0]` restrict to `I x [-t0', t0']` (`iteratedFDerivWithin_subset`).
* `BulkWeberChart.restrictSub`, `BulkPhaseInputs.restrictSub` (restriction of a bulk chart / its phase inputs to `P' <= P`, `t0' <= t0`).
* `WindowPhase.restrictT0`: a phase window at `t0` is one at `t0' <= t0`.
* `stdAssump_restrict`: `StdAssump F P Kd r` restricts to a smaller compact `P'`.
* `EK_lower_zero_tail`: `(E_K)` gives `(E_{K'})`, `K' <= K`, when the even jets `K' < j <= K` vanish (the truncated family with odd `M`).

## Differences from the paper

None (the paper chooses `t0` small once and for all, at the beginning of the "Setting" paragraphs of `thm:smo-BSr`; here `t0` is given and is shrunk).
`BulkWeberChart.restrictSub` is the same construction as `TheoremB.BulkWeberChart.restrict` (`TheoremB/TwoOrdersBulk.lean`), re-done here so that `TheoremA` does not import `TheoremB`.

## Not formalised

Restriction of the soft-edge charts (not needed: the assembly uses the soft windows only through `WindowPhase`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

/-! ### Phase coefficients -/

lemma jetRegJ_restrict {f : ℝ → ℝ → ℝ} {I : Set ℝ} {t0 t0' : ℝ} {k : ℕ} (h : JetRegJ f I t0 k) (ht : t0' ≤ t0) :
    JetRegJ f I t0' k :=
  h.mono (prod_mono subset_rfl (Icc_subset_Icc (by linarith) ht))

/-- The uniform `C^n` norm bound of a phase coefficient on `[a,b] x [-t0, t0]` holds on `[a,b] x [-t0', t0']`, `t0' <= t0`, with the same constant. -/
lemma sigma_bdd_restrict {f : ℝ → ℝ → ℝ} {a b t0 t0' : ℝ} {k : ℕ} (hab : a < b) (ht0' : 0 < t0') (ht : t0' ≤ t0)
    (hreg : JetRegJ f (Icc a b) t0 k) {C : ℝ} {i : ℕ} (hi : i ≤ k)
    (hC : ∀ p ∈ Icc a b ×ˢ Icc (-t0) t0, ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => f q.1 q.2) (Icc a b ×ˢ Icc (-t0) t0) p‖ ≤ C) :
    ∀ p ∈ Icc a b ×ˢ Icc (-t0') t0', ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => f q.1 q.2) (Icc a b ×ˢ Icc (-t0') t0') p‖ ≤ C := by
  intro p hp
  have hsub : Icc a b ×ˢ Icc (-t0') t0' ⊆ Icc a b ×ˢ Icc (-t0) t0 :=
    prod_mono subset_rfl (Icc_subset_Icc (by linarith) ht)
  have hs : UniqueDiffOn ℝ (Icc a b ×ˢ Icc (-t0') t0') :=
    (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith))
  have ht' : UniqueDiffOn ℝ (Icc a b ×ˢ Icc (-t0) t0) :=
    (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith))
  have hcd : ContDiffOn ℝ (i : WithTop ℕ∞) (fun q : ℝ × ℝ => f q.1 q.2) (Icc a b ×ˢ Icc (-t0) t0) :=
    hreg.of_le (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_subset hsub hs ht' hcd hp]
  exact hC p (hsub hp)

/-! ### Phase windows -/

/-- A phase window at `t0` is a phase window at `t0' <= t0`. -/
def WindowPhase.restrictT0 {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M : ℕ} {a b : Par → ℝ}
    (W : WindowPhase F K t0 M a b) (hab : ∀ μ ∈ K, a μ < b μ) {t0' : ℝ} (ht0' : 0 < t0') (ht : t0' ≤ t0) :
    WindowPhase F K t0' M a b where
  Sigma := W.Sigma
  Sigma_reg := fun μ hμ j hj => jetRegJ_restrict (W.Sigma_reg μ hμ j hj) ht
  Sigma_bdd := by
    obtain ⟨C, hC⟩ := W.Sigma_bdd
    exact ⟨C, fun μ hμ j hj i hi p hp =>
      sigma_bdd_restrict (hab μ hμ) ht0' ht (W.Sigma_reg μ hμ j hj) (by omega : i ≤ 2 * M + 1) (hC μ hμ j hj i hi) p hp⟩
  Sigma_zero := W.Sigma_zero
  slope := W.slope
  rule := W.rule

/-! ### Bulk charts -/

/-- Every field of a bulk Weber chart is a statement for all parameters in `P`: restriction to `P' <= P`. -/
def _root_.FormalResearch.JacobiEigenvectors.Charts.BulkWeberChart.restrictSub {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par}
    {P P' : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart F P Jlo Jhi m U V) (h : P' ⊆ P) :
    BulkWeberChart F P' Jlo Jhi m U V :=
  { C with
    overlap_in_well := fun μ hμ => C.overlap_in_well μ (h hμ)
    turn_eq := fun μ hμ => C.turn_eq μ (h hμ)
    Hz_lb := fun μ hμ => C.Hz_lb μ (h hμ)
    matchF := fun μ hμ => C.matchF μ (h hμ)
    matchO := fun μ hμ => C.matchO μ (h hμ)
    Y_bound := by
      obtain ⟨S, hS⟩ := C.Y_bound
      exact ⟨S, fun μ hμ => hS μ (h hμ)⟩
    shape := fun μ hμ => C.shape μ (h hμ)
    valid := fun μ hμ => C.valid μ (h hμ)
    A_bond := fun μ hμ => C.A_bond μ (h hμ)
    Q_diag := fun μ hμ => C.Q_diag μ (h hμ)
    dd_sqrt := fun μ hμ => C.dd_sqrt μ (h hμ)
    omega_sqrt := fun μ hμ => C.omega_sqrt μ (h hμ)
    wf_eq := fun μ hμ => C.wf_eq μ (h hμ)
    rho_one := fun μ hμ => C.rho_one μ (h hμ)
    theta_le := fun μ hμ => C.theta_le μ (h hμ)
    W_def := fun μ hμ => C.W_def μ (h hμ)
    M_def := fun μ hμ => C.M_def μ (h hμ)
    W_osc := fun μ hμ => C.W_osc μ (h hμ)
    M_osc := fun μ hμ => C.M_osc μ (h hμ)
    seed_pos := fun μ hμ => C.seed_pos μ (h hμ)
    collar_lb := fun μ hμ => C.collar_lb μ (h hμ)
    corr_lead := by
      obtain ⟨cg, Cg, hcg, g0, hg⟩ := C.corr_lead
      exact ⟨cg, Cg, hcg, g0, fun μ hμ => hg μ (h hμ)⟩
    theta_margin := by
      obtain ⟨ε, hε, hε1, hm⟩ := C.theta_margin
      exact ⟨ε, hε, hε1, fun μ hμ => hm μ (h hμ)⟩ }

/-- The restricted chart has the same overlap `[c', c]`, definitionally. -/
lemma restrictSub_c {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par}
    {P P' : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart F P Jlo Jhi m U V) (h : P' ⊆ P) :
    (C.restrictSub h).c = C.c ∧ (C.restrictSub h).c' = C.c' := ⟨rfl, rfl⟩

/-- The chart's rows, restricted: the left/right comparison sequences of the restricted chart are those of the chart. -/
lemma restrictSub_psiHatL {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par}
    {P P' : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart F P Jlo Jhi m U V) (h : P' ⊆ P)
    (μ : Par) (X : ℝ) (N : ℕ) : (C.restrictSub h).psiHatL μ X N = C.psiHatL μ X N := rfl

/-- **Phase inputs of the bulk charts, restricted to `t0' <= t0`** (the charts restricted to `paramSet K t0'`). -/
def _root_.FormalResearch.JacobiEigenvectors.Charts.BulkPhaseInputs.restrictSub {Par : Type*} [TopologicalSpace Par]
    {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ} {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ}
    {CL : BulkWeberChart F P Jlo Jhi (max M 1) U V} {CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V}
    (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) (hJ : K.Nonempty → Jlo < Jhi) {P' : Set (Par × ℝ)} (hP : P' ⊆ P)
    {t0' : ℝ} (ht0' : 0 < t0') (ht : t0' ≤ t0) :
    BulkPhaseInputs F P' K t0' Jlo Jhi M U V (CL.restrictSub hP) (CR.restrictSub hP) where
  Sigma := PI.Sigma
  Sigma_reg := fun μ hμ j hj => jetRegJ_restrict (PI.Sigma_reg μ hμ j hj) ht
  Sigma_zero := fun μ hμ X hX t ht' => PI.Sigma_zero μ hμ X hX t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  Sigma_one := fun μ hμ X hX t ht' => PI.Sigma_one μ hμ X hX t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  casoratian := by
    obtain ⟨Ccas, c0, N0, hc0, h⟩ := PI.casoratian
    exact ⟨Ccas, c0, N0, hc0, fun μ hμ t ht' X hX N hN =>
      h μ hμ t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ X hX N hN⟩
  Sigma_bdd := by
    obtain ⟨C, hC⟩ := PI.Sigma_bdd
    exact ⟨C, fun μ hμ j hj i hi p hp =>
      sigma_bdd_restrict (hJ ⟨μ, hμ⟩) ht0' ht (PI.Sigma_reg μ hμ j hj) (by omega : i ≤ 2 * M + 1) (hC μ hμ j hj i hi) p hp⟩

/-! ### Standing assumptions -/

/-- `StdAssump` restricts to a compact subset of the parameter set (`(E_K)` and `(H1)`--`(H3)` are statements for all parameters). -/
theorem stdAssump_restrict {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P P' : Set Par} {Kd r : ℕ}
    (hs : StdAssump F P Kd r) (hP : P' ⊆ P) (hc : IsCompact P') : StdAssump F P' Kd r := by
  obtain ⟨-, hEK, g, hg⟩ := hs
  refine ⟨hc, ⟨hEK.budget, fun j hj => ?_, ?_⟩, g, fun μ hμ => hg μ (hP hμ)⟩
  · have hj' := hEK.reg j hj
    have mono : ∀ {f : Par → ℝ → ℝ} {n : ℕ}, JetReg f P F.L n → JetReg f P' F.L n :=
      fun {f n} hf => ⟨fun μ hμ => hf.1 μ (hP hμ), fun i hi => (hf.2 i hi).mono (prod_mono hP subset_rfl)⟩
    exact ⟨mono hj'.1, mono hj'.2⟩
  · obtain ⟨C, hC⟩ := hEK.rem
    exact ⟨C, fun μ hμ => hC μ (hP hμ)⟩

/-- **Lowering the index of `(E_K)` when the dropped even jets vanish**: if `G_{2j} = B_{2j} = 0` for `K' < j <= K`, then `(E_K)` with regularity `r` gives `(E_{K'})` with the same `r`
(the remainder after `K'` is that after `K`, and `h^{2K+2} <= Lambda^{2(K - K')} h^{2K'+2}` for `h <= L <= Lambda`).  (The general lowering, for bounded non-vanishing tails, is
`TheoremB.EK_mono_idx`.) -/
theorem EK_lower_zero_tail {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {K K' r : ℕ}
    (h : EK F P K r) (hle : K' ≤ K) (hzero : ∀ j, K' < j → j ≤ K → ∀ μ ∈ P, F.G (2 * j) μ = 0 ∧ F.B (2 * j) μ = 0) :
    EK F P K' r := by
  obtain ⟨C, hC⟩ := h.rem
  refine EK.mk (le_trans ?_ h.budget) (fun j hj => h.reg j (hj.trans hle)) ?_
  · unfold regBudget
    omega
  · obtain ⟨Λ, hΛ⟩ : ∃ x : ℝ, x = max 1 F.L := ⟨_, rfl⟩
    have hΛ1 : 1 ≤ Λ := by rw [hΛ]; exact le_max_left _ _
    have hΛL : F.L ≤ Λ := by rw [hΛ]; exact le_max_right _ _
    refine ⟨|C| * Λ ^ (2 * K - 2 * K'), fun μ hμ N s hs => ?_⟩
    have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hsL : F.step N ≤ Λ := by
      have : F.step N ≤ F.L := by
        unfold SymbolFamily.step FormalResearch.JB.stepSize
        exact div_le_self F.L_pos.le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      exact this.trans hΛL
    have hsplit : ∀ f : ℕ → ℝ, (∀ j, K' < j → j ≤ K → f j = 0) →
        ∑ j ∈ Finset.range (K + 1), F.step N ^ (2 * j) * f j = ∑ j ∈ Finset.range (K' + 1), F.step N ^ (2 * j) * f j := by
      intro f hf
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : K' + 1 ≤ K + 1)]
      have : ∑ j ∈ Finset.Ico (K' + 1) (K + 1), F.step N ^ (2 * j) * f j = 0 := by
        refine Finset.sum_eq_zero (fun j hj => ?_)
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
        rw [hf j (by omega) (by omega), mul_zero]
      rw [this, add_zero]
    have hpow : F.step N ^ (2 * K + 2) ≤ Λ ^ (2 * K - 2 * K') * F.step N ^ (2 * K' + 2) := by
      have e : F.step N ^ (2 * K + 2) = F.step N ^ (2 * K - 2 * K') * F.step N ^ (2 * K' + 2) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hst.le hsL _) (by positivity)
    have hgz : ∀ j, K' < j → j ≤ K → F.G (2 * j) μ s = 0 := fun j h1 h2 => by
      have := (hzero j h1 h2 μ hμ).1; rw [this]; rfl
    have hbz : ∀ j, K' < j → j ≤ K → F.B (2 * j) μ s = 0 := fun j h1 h2 => by
      have := (hzero j h1 h2 μ hμ).2; rw [this]; rfl
    obtain ⟨hG, hB⟩ := hC μ hμ N s hs
    rw [hsplit (fun j => F.G (2 * j) μ s) hgz] at hG
    rw [hsplit (fun j => F.B (2 * j) μ s) hbz] at hB
    have hC' : C * F.step N ^ (2 * K + 2) ≤ |C| * Λ ^ (2 * K - 2 * K') * F.step N ^ (2 * K' + 2) := by
      calc C * F.step N ^ (2 * K + 2) ≤ |C| * F.step N ^ (2 * K + 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C| * (Λ ^ (2 * K - 2 * K') * F.step N ^ (2 * K' + 2)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
        _ = _ := by ring
    exact ⟨hG.trans hC', hB.trans hC'⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.EK_lower_zero_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.EK_lower_zero_tail

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.stdAssump_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.stdAssump_restrict

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.sigma_bdd_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.sigma_bdd_restrict

end FormalResearch.JacobiEigenvectors.TheoremA

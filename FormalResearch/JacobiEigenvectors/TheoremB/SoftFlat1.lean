module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SoftOverlap

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 9: `lem:tha-Mflat` (flat1, corrected sequence) as a single-chart lemma

Source: Paper J `app_thmB.tex`, `lem:tha-Mflat` (flat1).  `propThaMflat_proved` is stated for a pair `(CL, CR)`, but its flat1 conjunct for the corrected sequence uses only `CL`
(`propThaM_of_facts` without its unused `StdAssump` premise, `fold_pair`, `fold_in_window`).  Here it is a lemma for any soft chart `C` (of any family), so that it applies to the mirror chart `CR`
(of `mirrorFamily Fz`, for which no `StdAssump` is available).

* `propThaM_phi_nostd`: the third conjunct of `propThaM_of_facts`, without the premise `StdAssump`.
* `soft_flat1_phi`: for `a <= 1`, `c kappa_bal(a)^{-2} sum_Omega M_bal^2 <= sum_{Omega cap {n <= n_c}} (phi^{(2)}/kappa_bal)^2`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

set_option maxHeartbeats 1000000 in
theorem propThaM_phi_nostd {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (aplus : ℝ) :
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 →
      CL.aOf p X N ≤ aplus → ∀ s : ℝ, |s| ≤ Real.sqrt (max (-CL.aOf p X N) 0) + (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) / 4 →
        c * (kappaBal (CL.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2
            ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ s),
                ((CL.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (CL.aOf p X N)) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  obtain ⟨c1, hc1pos, hc1⟩ := wm_c1 pc aplus
  have hΔ : 0 < wmDelta c1 (winCB CPC aplus ^ 2) CL.dp := wmDelta_pos hc1pos (by positivity) hdp
  obtain ⟨cs, hs0, hcs, hhs, hsm⟩ := wm_small pc CL aplus hc1pos hc1
  obtain ⟨cl, hl0, hcl, hhl, hlg⟩ := wm_large pc CL aplus hΔ
  refine ⟨min cs cl, min hs0 hl0, lt_min hcs hcl, lt_min hhs hhl, ?_⟩
  intro p hp X hX N hN hstep haplus s hs
  have hsmall := (le_min_iff.mp hstep).1
  have hlarge := (le_min_iff.mp hstep).2
  have hclaims : WmClaims CL p X N (min cs cl) := by
    by_cases hA : Fz.step N * max (-CL.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) CL.dp
    · exact (hsm p hp X hX N hN hsmall haplus hA).mono (min_le_left _ _) (wmMass_nonneg CL p X N)
    · push_neg at hA
      exact (hlg p hp X hX N hN hlarge haplus hA).mono (min_le_right _ _) (wmMass_nonneg CL p X N)
  obtain ⟨-, -, h3⟩ := hclaims
  have hκ := wm_kappa_pos' (CL.aOf p X N)
  have hsl := abs_le.mp hs
  have hcutdef : wmCut (CL.aOf p X N) = Real.sqrt (max (-CL.aOf p X N) 0) +
      (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) / 4 := rfl
  rw [← hcutdef] at hsl
  refine wm_unscale3 _ _ _ hκ _ _ (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n) ?_ h3
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, le_trans hn.2 (by linarith [hsl.1])⟩

set_option maxHeartbeats 1000000 in
/-- **flat1 (corrected sequence) of one soft chart**: for `a <= 1`, `c kappa_bal(a)^{-2} sum_Omega M_bal^2 <= sum_{Omega cap {n <= n_c}} (phi^{(2)} / kappa_bal)^2`, `n_c = nearestRow u_c`. -/
theorem soft_flat1_phi {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (C : SoftEdgeChart Fz P m q U V (fun _ => 1)) :
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → C.aOf p X N ≤ 1 →
      c * (kappaBal (C.aOf p X N))⁻¹ ^ 2 * ∑ n ∈ softWindow C p X N, Mbal (C.aOf p X N) (C.Zof p X N n) ^ 2
        ≤ ∑ n ∈ (softWindow C p X N).filter (fun n => n ≤ nearestRow (Fz.step N) (C.uc p)),
            ((C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N)) ^ 2 := by
  have hfold : SoftFoldSmall C := C.delta0_small
  obtain ⟨cM, hM0, hcM, hM0p, HM⟩ := propThaM_phi_nostd pc C 1
  obtain ⟨hw0, hw0p, Hw⟩ := fold_in_window C hfold
  refine ⟨cM, min (min hM0 hw0) (asmH0 C), hcM, lt_min (lt_min hM0p hw0p) (asmH0_pos C), ?_⟩
  intro p hp X hX N hN hstep ha
  have sM : Fz.step N ≤ hM0 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have sw : Fz.step N ≤ hw0 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have sAs : Fz.step N ≤ asmH0 C := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hnc : |uNode (Fz.step N) (nearestRow (Fz.step N) (C.uc p)) - C.uc p| ≤ Fz.step N / 2 := nearestRow_close _ _ hh0
  set nc := nearestRow (Fz.step N) (C.uc p) with hncdef
  obtain ⟨hncW, hncC⟩ := Hw p hp X hX N hN sw ha nc hnc
  have h3 := HM p hp X hX N hN sM ha (C.Zof p X N nc) (by unfold wmCut at hncC; exact hncC)
  have hiff : ∀ n ∈ softWindow C p X N, (n ≤ nc ↔ C.Zof p X N n ≤ C.Zof p X N nc) := by
    intro n hn
    have hc1 := soft_win_loc C hp hX sAs hn
    have hc2 := soft_win_loc C hp hX sAs hncW
    have hη := C.consts_pos.2.1
    have hdm := C.consts_pos.2.2.1
    constructor
    · intro hle
      exact Zof_le C hp hX N hle (by linarith) (by linarith)
    · intro hZ
      by_contra hcon
      push_neg at hcon
      have hinc := Zof_incr C hp hX N hcon.le (by linarith) (by linarith)
      have h1 : (1 : ℝ) ≤ (n : ℝ) - nc := by
        have : nc + 1 ≤ n := hcon
        have : ((nc : ℝ) + 1) ≤ n := by exact_mod_cast this
        linarith
      have hs0 : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
      have : 0 < C.dm * ((n : ℝ) - nc) * Real.sqrt (Fz.step N) := by positivity
      linarith
  have hfil1 : (softWindow C p X N).filter (fun n => n ≤ nc) = (softWindow C p X N).filter (fun n => C.Zof p X N n ≤ C.Zof p X N nc) :=
    Finset.filter_congr fun n hn => hiff n hn
  rw [hfil1]
  exact h3

end FormalResearch.JacobiEigenvectors.TheoremB

end

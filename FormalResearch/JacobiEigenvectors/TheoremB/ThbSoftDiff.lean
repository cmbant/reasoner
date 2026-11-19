module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoft
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftOvP
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbSoftGeom
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersSoft

/-!
# Paper J, Theorem B, L3.5c, part 10: the two sewings agree on the window up to `C h^m` (entries of the modified host)

Source: Paper J `app_thmB.tex`, proof of `prop:tha-splice` (b), eq:tha-spl1 (the matching `|psi-hat^L - hat kappa psi-hat^R| <= C h^m T M_bal` on the window) and the normalisation `c_n T^2 h^{-1/2} <= hat N^2`, `m_Omega <= C_M h^{-1/2}`.

## Proved here

* `soft_entry_diff`: at an eigenvalue column with `a <= 1`, for every row `g` of the window `Omega`, `|hat kappa psi-hat^R_{N-g}/hat N - psi-hat^L_g/hat N| <= C_d h^m`.  (`T M_bal(g) <= sqrt(C_M/c_n) hat N`, since `M_bal(g)^2 <= m_Omega`.)
  This bounds the one-row (or two-row) difference between the host `compMatrix` and the host of the right half chart that also covers the rows `g_0 .. n_c` (see `ThbSoftGeom`).
* `soft_fold_rows`: the rows `n_c` and `g_0` lie in the window (`fold_in_window`).

## Differences from the paper

None (the paper's host of the right chart is the right-sewn column).  **Not formalised**: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem soft_entry_diff (hf : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (hm : 1 ≤ m) (hM : SoftMirror CL CR) :
    ∃ Cd h1 : ℝ, 0 ≤ Cd ∧ 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p (Xs k) N ≤ 1 →
          ∀ g ∈ softWindow CL p (Xs k) N,
            |softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - g) / softNorm CL CR p (Xs k) N -
              CL.psiHatL p (Xs k) N g / softNorm CL CR p (Xs k) N| ≤ Cd * Fz.step N ^ m := by
  have hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ (fun _ : ℝ => (1 : ℝ)) h := fun _ _ _ => le_rfl
  obtain ⟨Cenv, Cm, K, CM, cn, clb, hF0, hCenv, hCm, hK, hCM, hcn, hclb, hF0p, Hf⟩ := soft_splice_facts CL CR hM hf hm hLm
  refine ⟨Cm * Real.sqrt (CM / cn), min (min hF0 (min CL.softH1 CR.softH1)) (min CL.η CR.η),
    by positivity, lt_min (lt_min hF0p (lt_min CL.softH1_pos CR.softH1_pos)) (lt_min CL.consts_pos.2.1 CR.consts_pos.2.1), ?_⟩
  intro p hp N hN hstep Xs Um hE k hX ha g hg
  have hA1 := hstep.trans (min_le_left _ _)
  have hA2 := hstep.trans (min_le_right _ _)
  have sF : Fz.step N ≤ hF0 := hA1.trans (min_le_left _ _)
  have sH1 : Fz.step N ≤ CL.softH1 := hA1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have sH1R : Fz.step N ≤ CR.softH1 := hA1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have sη : Fz.step N ≤ CL.η := hA2.trans (min_le_left _ _)
  have sηR : Fz.step N ≤ CR.η := hA2.trans (min_le_right _ _)
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 sH1 sH1R sη sηR Xs Um hE k hX
  obtain ⟨hT, E1, E2, E3, E4, E5, E7⟩ := Hf p hp N hN sF (Xs k) hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  simp only [mul_one] at E2
  set a := CL.aOf p (Xs k) N with hadef
  set T := |CL.lamL p (Xs k) N| / kappaBal a with hTdef
  have hE0 : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
  have hBpos : 0 < cn * (T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) := by positivity
  have hnn : 0 ≤ softNorm CL CR p (Xs k) N := Real.sqrt_nonneg _
  have hypos : 0 < softNorm CL CR p (Xs k) N := by
    refine lt_of_le_of_ne hnn (fun h => ?_)
    rw [← h] at E5; simp at E5; linarith
  have hMg : Mbal a (CL.Zof p (Xs k) N g) ^ 2 ≤ wmMass CL p (Xs k) N := by
    unfold wmMass
    exact Finset.single_le_sum (f := fun n => Mbal a (CL.Zof p (Xs k) N n) ^ 2) (fun _ _ => sq_nonneg _) hg
  have hM0 : 0 ≤ Mbal a (CL.Zof p (Xs k) N g) := Mbal_nonneg' _ _
  -- (T M)^2 <= (CM/cn) N^2
  have hsq : (T * Mbal a (CL.Zof p (Xs k) N g)) ^ 2 ≤ (CM / cn) * softNorm CL CR p (Xs k) N ^ 2 := by
    have h1 : (T * Mbal a (CL.Zof p (Xs k) N g)) ^ 2 ≤ T ^ 2 * (CM * Fz.step N ^ (-(1 : ℝ) / 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (hMg.trans E4) (sq_nonneg _)
    have h2 : T ^ 2 * (CM * Fz.step N ^ (-(1 : ℝ) / 2)) = (CM / cn) * (cn * (T ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2))) := by
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left E5 (by positivity)
  have hTM : T * Mbal a (CL.Zof p (Xs k) N g) ≤ Real.sqrt (CM / cn) * softNorm CL CR p (Xs k) N := by
    have h0 : 0 ≤ T * Mbal a (CL.Zof p (Xs k) N g) := mul_nonneg hT.le hM0
    have h1 : Real.sqrt ((T * Mbal a (CL.Zof p (Xs k) N g)) ^ 2) ≤ Real.sqrt ((CM / cn) * softNorm CL CR p (Xs k) N ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq h0, Real.sqrt_mul (by positivity), Real.sqrt_sq hnn] at h1
    exact h1
  have hmatch := E2 g hg
  set D := softNorm CL CR p (Xs k) N with hD
  have e : softKappa CL CR p (Xs k) N * CR.psiHatL p (Xs k) N ((N : ℤ) - g) / D - CL.psiHatL p (Xs k) N g / D =
      -(CL.psiHatL p (Xs k) N g - softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N g) / D := by
    unfold softSeqR; ring
  rw [e, abs_div, abs_neg, abs_of_pos hypos, div_le_iff₀ hypos]
  have hp0 : 0 ≤ Fz.step N ^ m := pow_nonneg hh0.le _
  calc |CL.psiHatL p (Xs k) N g - softKappa CL CR p (Xs k) N * softSeqR CR p (Xs k) N g|
      ≤ Cm * Fz.step N ^ m * (T * Mbal a (CL.Zof p (Xs k) N g)) := hmatch
    _ ≤ Cm * Fz.step N ^ m * (Real.sqrt (CM / cn) * D) := mul_le_mul_of_nonneg_left hTM (by positivity)
    _ = _ := by ring

/-- The fold rows `n_c` and `g_0` (within `h/2` of `u_c`) lie in the window. -/
theorem soft_fold_rows (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → CL.aOf p X N ≤ 1 →
      ∀ n0 : ℤ, |uNode (Fz.step N) n0 - CL.uc p| ≤ Fz.step N / 2 → n0 ∈ softWindow CL p X N := by
  obtain ⟨h0, hh0, H⟩ := fold_in_window CL CL.delta0_small
  exact ⟨h0, hh0, fun p hp X hX N hN hs ha n0 hn0 => (H p hp X hX N hN hs ha n0 hn0).1⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_entry_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_entry_diff

end FormalResearch.JacobiEigenvectors.TheoremB

end

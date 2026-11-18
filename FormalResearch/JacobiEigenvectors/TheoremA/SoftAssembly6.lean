module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly5

/-!
# Soft-edge assembly, part F: the window label of an eigenvalue (`PropThaW2` (3), first half, up to the identification label = index)

Source: app_thmA, proof of prop:tha-W2, Steps 4 (b) and 5.

Proved here (all axiom-pinned):
* `eig_exact_data`: at an eigenvalue obeying Step 0, the exact solutions `psi^L`, `psi'` seeded by `psi-hat_0` with `psi^L = kappa psi'(N - .)` exist (`exists_seeded`, `psiL_eq_kappa_psiR`, `bondA_pos_all`).
* `soft_window_label`: every eigenvalue `X_k` with `|X_k - bandHi| <= delta_0` and Step 0 satisfies `a <= 0` and `|mu-tilde(X_k) - (j + 1/2) h| <= C h^{m+1} Lm(h)` for SOME integer `j >= 0`
  (`soft_match` for `hkap`, `soft_quant`, `cos_label`; `mu-tilde` is the frozen sum `mu_0 + sum h^{2r} mu_{2r}`, `a = -mu-tilde/h`).

Differences from the paper: none.  Not formalised: that `j` is the index `k` of the eigenvalue and the existence of an eigenvalue in every window (app_thmA Step 6, `lem:tha-count`: needs the sign chain of Step 6 (ii), (iii)).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Label

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- exact solutions at an eigenvalue. -/
theorem eig_exact_data (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) {N : ℕ} (hN1 : CL.N0 ≤ N) (hN2 : CR.N0 ≤ N)
    (hs1 : Fz.step N ≤ CL.softH1) (hs1R : Fz.step N ≤ CR.softH1) (hsη : Fz.step N ≤ CL.η) (hsηR : Fz.step N ≤ CR.η)
    (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (Fz.jacobiMat p N) Xs Um)
    (k : Fin (N + 1)) (hX : |Xs k - Fz.bandHi p| ≤ CL.δ0) :
    ∃ (ψL ψ' : ℤ → ℝ) (κ : ℝ), JacSol Fz p N (Xs k) (CL.chain p (Xs k) N).NR ψL ∧ ψL 0 = CL.psiHatL p (Xs k) N 0 ∧
      JacSol (mirrorFamily Fz) p N (Xs k) (CR.chain p (Xs k) N).NR ψ' ∧ ψ' 0 = CR.psiHatL p (Xs k) N 0 ∧
      (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) := by
  set X := Xs k with hXk
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN1
  have hpos := bondA_pos_all CL CR hM hp hX hN1 hs1 hs1R
  have hLpos : ∀ n : ℤ, 0 ≤ n → n < N → Fz.bondA p N n ≠ 0 := fun n h0 h1 => (hpos n h0 h1).ne'
  have hRpos : ∀ n : ℤ, 0 ≤ n → n < N → (mirrorFamily Fz).bondA p N n ≠ 0 := by
    intro n h0 h1
    rw [bondA_mirror]
    exact (hpos _ (by omega) (by omega)).ne'
  obtain ⟨ψL, hψL0, hψL⟩ := exists_seeded (Fz.bondA p N) (Fz.diagQ p N X) N hLpos (CL.psiHatL p X N 0)
  obtain ⟨ψ', hψ'0, hψ'⟩ := exists_seeded ((mirrorFamily Fz).bondA p N) ((mirrorFamily Fz).diagQ p N X) N hRpos (CR.psiHatL p X N 0)
  have hJL : JacSol Fz p N X N ψL := hψL
  have hJR : JacSol (mirrorFamily Fz) p N X N ψ' := hψ'
  have hLp : 0 < ψL 0 := by rw [hψL0]; exact psiHatL_zero_pos CL hp hX hN1 hsη
  have hRp : ψ' 0 ≠ 0 := by rw [hψ'0]; exact (psiHatL_zero_pos CR hp hXR hNR hsηR).ne'
  obtain ⟨hrel0, -⟩ := psiL_eq_kappa_psiR Fz p N hpos Xs Um hE k ψL hJL hLp ψ' hJR hRp
  have hNRL : (CL.chain p X N).NR ≤ N := by
    have := row_le_N Fz N (j := (CL.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CL.shape p hp X hX N hN1
      have := (CL.ucη_in p hp).2
      have hη := CL.consts_pos.2.1
      linarith)
    exact_mod_cast this
  have hNRR : (CR.chain p X N).NR ≤ N := by
    have := row_le_N (mirrorFamily Fz) N (j := (CR.chain p X N).NR) (by
      obtain ⟨-, -, -, -, -, -, hNRu, -⟩ := CR.shape p hp X hXR N hNR
      have := (CR.ucη_in p hp).2
      have hη := CR.consts_pos.2.1
      linarith)
    exact_mod_cast this
  exact ⟨ψL, ψ', ψL N / ψ' 0, fun n h0 h1 => hJL n h0 (lt_of_lt_of_le h1 (by exact_mod_cast hNRL)), hψL0,
    fun n h0 h1 => hJR n h0 (lt_of_lt_of_le h1 (by exact_mod_cast hNRR)), hψ'0, hrel0⟩

/-- **the window label**: every eigenvalue in the chart range obeying Step 0 lies in a window `|mu-tilde - (j+1/2) h| <= C h^{m+1} Lm`, `j >= 0`, and has `a <= 0`. -/
theorem soft_window_label (hM : SoftMirror CL CR) {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (Cs0 : ℝ) :
    ∃ Cc h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        (∀ i, Xs i ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2) → ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 →
          CL.aOf p (Xs k) N ≤ 0 ∧ ∃ j : ℕ,
            |(CL.muS 0 p (Fz.bandHi p - Xs k) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs k))
              - ((j : ℝ) + 1 / 2) * Fz.step N| ≤ Cc * Fz.step N ^ (m + 1) * Lm (Fz.step N) := by
  obtain ⟨h0a, h0ap, Ha⟩ := aOf_le_of_step0 CL Cs0
  obtain ⟨Ck, Dk, cn, h0b, h0bp, hCk, hDk, hcn, Hm⟩ := soft_match CL CR hf hm hLm hM (asmAplus CL)
  obtain ⟨Cq, h0c, h0cp, Hq⟩ := soft_quant CL CR hf hm hLm hM Ck
  refine ⟨Cq / 2 + 0, min (min h0a h0b) (min h0c (min CL.softH1 (min CR.softH1 (min CL.η CR.η)))),
    lt_min (lt_min h0ap h0bp) (lt_min h0cp (lt_min CL.softH1_pos (lt_min CR.softH1_pos (lt_min CL.consts_pos.2.1 CR.consts_pos.2.1)))), ?_⟩
  intro p hp N hN hstep Xs Um hE hs0 k hX
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hsa : Fz.step N ≤ h0a := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hsb : Fz.step N ≤ h0b := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsc : Fz.step N ≤ h0c := (hstep.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs1 : Fz.step N ≤ CL.softH1 := ((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs1R : Fz.step N ≤ CR.softH1 := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsη : Fz.step N ≤ CL.η := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsηR : Fz.step N ≤ CR.η := (((hstep.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha := Ha p hp N (hstep.trans ((min_le_left _ _).trans (min_le_left _ _))) (Xs k) hX (hs0 k)
  obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 hs1 hs1R hsη hsηR Xs Um hE k hX
  obtain ⟨hk1, -, -, -, -⟩ := Hm p hp N hN1 hsb (Xs k) hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  obtain ⟨ha0, hcos⟩ := Hq p hp N hN1 hsc (Xs k) hX ψL ψ' κ hJL hsL hJR hsR hrel hk1
  refine ⟨ha0, ?_⟩
  obtain ⟨j, hj⟩ := cos_label ha0 hcos
  refine ⟨j, ?_⟩
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hdef : CL.aOf p (Xs k) N = -(1 / Fz.step N) * (CL.muS 0 p (Fz.bandHi p - Xs k) +
      ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs k)) := rfl
  set S := CL.muS 0 p (Fz.bandHi p - Xs k) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs k) with hS
  rw [hdef] at hj
  have e : S - ((j : ℝ) + 1 / 2) * Fz.step N = -(Fz.step N * (-(1 / Fz.step N) * S + ((j : ℝ) + 1 / 2))) := by
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos hh0]
  calc Fz.step N * |-(1 / Fz.step N) * S + ((j : ℝ) + 1 / 2)| ≤ Fz.step N * (Cq * Fz.step N ^ m * Lm (Fz.step N) / 2) :=
        mul_le_mul_of_nonneg_left hj hh0.le
    _ = (Cq / 2 + 0) * Fz.step N ^ (m + 1) * Lm (Fz.step N) := by ring

end Label

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eig_exact_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eig_exact_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_window_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_window_label

end FormalResearch.JacobiEigenvectors.TheoremA

end

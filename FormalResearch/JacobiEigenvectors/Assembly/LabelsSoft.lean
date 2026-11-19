module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Assembly.SoftLabels

/-!
# Paper J: the soft anchor of the bulk labels (thm:A (i), "Location and labels")

Source: Paper J `thmA.tex`, proof of `thm:A (i)`: "at the top, the eigenvalues within `delta_0` of `X_s^+` are labelled by `Prop.thaW2` (3), `pi mu_0 = S_0` (eq:cha-mu0), so the bulk window of such an eigenvalue has label equal to its index".

## Proved here (axiom-pinned)

* `soft_anchor_window`: for an eigenvalue `X_i` of `J_h(mu)` in `[X_s^+(mu, h) - delta_0, X_s^+(mu, h)]`, `|S_0^{(h)}(X_i) - pi h (i + 1/2)| <= Cs h^2`.  From the labelled soft rule `SoftLabels` (of exponent `>= 2`), the chart field `mu0_S0`
  (`pi mu_0(alpha) = S_0`) and the bound `muS_bd` of the shifts `mu_{2r}` (so the terms `h^{2r} mu_{2r}` are `O(h^2)`).

## Differences from the paper

None.

## Not formalised

Nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

theorem soft_anchor_window {T : SymbolFamily Par} {K : Set Par} {Kidx m : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs T K Kidx t0 m (2 * Kidx) U V cPC CPC) {M' : ℕ} (hM' : 1 ≤ M') (hlab : SoftLabels T Kidx K M' CI.softUpL) :
    ∃ Cs h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, T.step N ≤ h0 → T.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (T.jacobiMat μ N) Xs Um →
        ∀ i : Fin (N + 1), (frozenFamily T Kidx).bandHi (μ, T.step N) - Xs i ≤ CI.softUpL.δ0 →
          Xs i ≤ (frozenFamily T Kidx).bandHi (μ, T.step N) →
          |actionS0 (frozenFamily T Kidx) (μ, T.step N) (Xs i) - Real.pi * T.step N * (((i : ℕ) : ℝ) + 1 / 2)| ≤ Cs * T.step N ^ 2 := by
  obtain ⟨Cc, h0s, hh0s, hrule⟩ := hlab
  obtain ⟨-, hCmu⟩ := CI.softUpL.consts_pos2
  refine ⟨Real.pi * (Kidx * CI.softUpL.Cmu + |Cc|), min h0s 1, lt_min hh0s one_pos, ?_⟩
  intro μ hμ N hN ht Xs Um hE i hi1 hi2
  have hst : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
  have hh0 : T.step N ≤ h0s := hN.trans (min_le_left _ _)
  have hh1 : T.step N ≤ 1 := hN.trans (min_le_right _ _)
  set h := T.step N with hh
  set bh := (frozenFamily T Kidx).bandHi (μ, h) with hbh
  have hp : (μ, h) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, ht⟩⟩
  have hmu0 := CI.softUpL.mu0_S0 (μ, h) hp (Xs i) hi2 hi1
  have hS : actionS0 (frozenFamily T Kidx) (μ, h) (Xs i) = Real.pi * CI.softUpL.muS 0 (μ, h) (bh - Xs i) := by
    rw [hmu0]; rfl
  have hr := hrule μ hμ N hh0 Xs Um hE i (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hq : 2 * Kidx / 2 = Kidx := by omega
  rw [hq] at hr
  -- the shifts are bounded
  have hbd : ∀ s ∈ Finset.Icc 1 Kidx, |h ^ (2 * s) * CI.softUpL.muS s (μ, h) (bh - Xs i)| ≤ CI.softUpL.Cmu * h ^ 2 := by
    intro s hs
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hs2 := (Finset.mem_Icc.mp hs).2
    have hmb := CI.softUpL.muS_bd s (by rw [Finset.mem_Icc]; constructor <;> omega) (μ, h) hp (bh - Xs i)
      (by rw [abs_of_nonneg (by linarith)]; exact hi1)
    rw [abs_mul, abs_of_pos (pow_pos hst _)]
    have : h ^ (2 * s) ≤ h ^ 2 := pow_le_pow_of_le_one hst.le hh1 (by omega)
    calc h ^ (2 * s) * |CI.softUpL.muS s (μ, h) (bh - Xs i)| ≤ h ^ 2 * CI.softUpL.Cmu :=
          mul_le_mul this hmb (abs_nonneg _) (by positivity)
      _ = CI.softUpL.Cmu * h ^ 2 := by ring
  have hsum : |∑ s ∈ Finset.Icc 1 Kidx, h ^ (2 * s) * CI.softUpL.muS s (μ, h) (bh - Xs i)| ≤ Kidx * (CI.softUpL.Cmu * h ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  have hpow : h ^ (M' + 1) ≤ h ^ 2 := pow_le_pow_of_le_one hst.le hh1 (by omega)
  have hrr : |CI.softUpL.muS 0 (μ, h) (bh - Xs i) - (((i : ℕ) : ℝ) + 1 / 2) * h| ≤ Kidx * (CI.softUpL.Cmu * h ^ 2) + |Cc| * h ^ 2 := by
    have h1 : |CI.softUpL.muS 0 (μ, h) (bh - Xs i) + ∑ s ∈ Finset.Icc 1 Kidx, h ^ (2 * s) * CI.softUpL.muS s (μ, h) (bh - Xs i)
        - (((i : ℕ) : ℝ) + 1 / 2) * h| ≤ |Cc| * h ^ 2 :=
      hr.trans ((mul_le_mul_of_nonneg_right (le_abs_self Cc) (pow_nonneg hst.le _)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
    have e : CI.softUpL.muS 0 (μ, h) (bh - Xs i) - (((i : ℕ) : ℝ) + 1 / 2) * h
        = (CI.softUpL.muS 0 (μ, h) (bh - Xs i) + ∑ s ∈ Finset.Icc 1 Kidx, h ^ (2 * s) * CI.softUpL.muS s (μ, h) (bh - Xs i)
            - (((i : ℕ) : ℝ) + 1 / 2) * h) - ∑ s ∈ Finset.Icc 1 Kidx, h ^ (2 * s) * CI.softUpL.muS s (μ, h) (bh - Xs i) := by ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ |Cc| * h ^ 2 + Kidx * (CI.softUpL.Cmu * h ^ 2) := add_le_add h1 hsum
      _ = _ := by ring
  rw [hS]
  have e2 : Real.pi * CI.softUpL.muS 0 (μ, h) (bh - Xs i) - Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2)
      = Real.pi * (CI.softUpL.muS 0 (μ, h) (bh - Xs i) - (((i : ℕ) : ℝ) + 1 / 2) * h) := by ring
  rw [e2, abs_mul, abs_of_pos Real.pi_pos]
  calc Real.pi * |CI.softUpL.muS 0 (μ, h) (bh - Xs i) - (((i : ℕ) : ℝ) + 1 / 2) * h|
      ≤ Real.pi * (Kidx * (CI.softUpL.Cmu * h ^ 2) + |Cc| * h ^ 2) := mul_le_mul_of_nonneg_left hrr Real.pi_pos.le
    _ = Real.pi * (Kidx * CI.softUpL.Cmu + |Cc|) * h ^ 2 := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_anchor_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.soft_anchor_window

end FormalResearch.JacobiEigenvectors.TheoremA

end

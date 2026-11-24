module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremA.BandFacts

/-!
# thm:A (i) with the localisation clause

Source: Paper J `main_results.tex`, `thm:A (i)`: besides the eigenvalue rule (`ThmAi`), for `h <= h_M` every eigenvalue lies in
`[X_s^- - delta, X_s^+ + delta]`, with the same `delta` as the smooth extension of the `S_j`.

* `EigenLoc`: the localisation clause.
* `ThmAiFull`: `thm:A (i)` as stated in the paper, `ThmAi`'s conclusion together with `EigenLoc` for the same `delta` and `h_M`.
* `thmAiFull_of_thmAi`: `ThmAi -> ThmAiFull`. The clause needs no chart input: Step 0 under `(D_0)` (`stepZeroD0`) puts the eigenvalues within
  `C h` of the band, and `h_M` is lowered to `delta / (|C| + 1)` (the rule is monotone in `h_M`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Finset FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-- The localisation clause of `thm:A (i)`: for `h <= h_M` every eigenvalue of `J_h(mu)` lies in `[X_s^- - delta, X_s^+ + delta]`, uniformly in `mu in K`. -/
def EigenLoc (F : SymbolFamily Par) (K : Set Par) (δ hM : ℝ) : Prop :=
  ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hM → ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
    IsEigenSystem (F.jacobiMat μ N) X Um → ∀ k : Fin (N + 1), F.bandLo μ - δ ≤ X k ∧ X k ≤ F.bandHi μ + δ

/-- **Theorem A (i)** as stated in the paper: `ThmAi` together with the localisation of the spectrum in `[X_s^- - delta, X_s^+ + delta]` for `h <= h_M`. -/
def ThmAiFull (F : SymbolFamily Par) (K : Set Par) (M : ℕ) : Prop :=
  IsCompact K → HypOn F K → DM F K M →
    ∃ (δ Cn C hM : ℝ) (S : ℕ → Par → ℝ → ℝ), 0 < δ ∧ SmoothExt F K M S δ Cn ∧ ActionFormula F K S ∧ EigenRule F K M S hM C ∧
      EigenLoc F K δ hM

/-- `ThmAi` gives `ThmAiFull`: the localisation clause follows from Step 0 under `(D_0)` after lowering `h_M`. -/
theorem thmAiFull_of_thmAi {F : SymbolFamily Par} {K : Set Par} {M : ℕ} (h : ThmAi F K M) : ThmAiFull F K M := by
  intro hK hH hD
  obtain ⟨δ, Cn, C, hM, S, hδ, hSm, hAct, hRule⟩ := h hK hH hD
  obtain ⟨C0, h0, hh0, hloc⟩ := stepZeroD0 F K hK hH (dm_zero_of_dm F K M hK hD)
  have hC : 0 < |C0| + 1 := by positivity
  set hM' := min hM (min h0 (δ / (|C0| + 1))) with hM'def
  have hM'pos : 0 < hM' := lt_min hRule.1 (lt_min hh0 (div_pos hδ hC))
  refine ⟨δ, Cn, C, hM', S, hδ, hSm, hAct, ⟨hM'pos, fun μ hμ N hN => hRule.2 μ hμ N (hN.trans (min_le_left _ _))⟩, ?_⟩
  intro μ hμ N hN X Um hE k
  have hN0 : F.step N ≤ h0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNd : F.step N ≤ δ / (|C0| + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs := (step_pos F N).le
  have hCh : C0 * F.step N ≤ δ := by
    have h1 : C0 * F.step N ≤ (|C0| + 1) * F.step N := mul_le_mul_of_nonneg_right (by linarith [le_abs_self C0]) hs
    have h2 : (|C0| + 1) * F.step N ≤ δ := by rw [le_div_iff₀ hC] at hNd; linarith
    linarith
  obtain ⟨hlo, hhi⟩ := hloc μ hμ N hN0 X Um hE k
  constructor <;> linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAiFull_of_thmAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thmAiFull_of_thmAi

end FormalResearch.JacobiEigenvectors.TheoremA

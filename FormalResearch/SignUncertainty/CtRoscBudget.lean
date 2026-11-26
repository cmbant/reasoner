module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscRealChart
public import FormalResearch.SignUncertainty.CtNodeLower

/-!
# `ct:dyadic` (3)-(4), `(ct:rosc)`: the budget `tsum` is the finite node sum (piece `T1` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (4), definition of `P_R(H)`.  `ctBudget R ε c f = Σ_{|a_n|<R} H(a_n)/Ai'(a_n)² - ε f(0)` is built from the *real*
inverse chart `ctPhi = invFunOn û` (window domain `ctPhiDom`), while `ctRoscAiry` uses the complex chart `φ_c = ctPhiC ctChartC1`.  On the window
`ctPhi` and the real restriction `ctPhiR` of `φ_c` agree near every point `y ∈ (-R_max, -1)` (`ctPhi_eventuallyEq`), so `ctFc = ctFr` at the Airy nodes
(`ctFc_eq_ctFr`), and the `tsum` (finitely many nonzero terms, `N` = number of nodes in `|u| < R`) is the node sum of `ctRoscAiry`
(`ctBudget_nodes`).  Also `ctPhiR (-R) = -R'`, and `ctPhiR ∘ û = id` on the window.

All proved.
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- **The `ψ_ε`-window for the chart range** (constants independent of `c`): `PsiWin ε ρ M`, `2M ≤ c`, `λM ≤ 1/2` and `μ R_max < ρ`
(`μ R_max = 4·2^{2/3} ctChartC1²` does not depend on `c`). -/
structure CtWinHyp (ε c ρ M : ℝ) : Prop where
  win : PsiWin ε ρ M
  cM : 2 * M ≤ c
  lam : ctLam c * M ≤ 1 / 2
  nu : ctMu c * ctRmax ctChartC1 c < ρ

namespace CtRealChartHyp

variable {ε c C ρ M : ℝ}

/-- `φ_c(û(w)) = w` for `-R_max ≤ w < 0` (the defining property of the complex chart on the real window). -/
lemma ctPhiR_ctUhat (H : CtRealChartHyp ε c C) {w : ℝ} (hw0 : w < 0) (hw : -ctRmax ctChartC1 c ≤ w) :
    ctPhiR ε c (ctUhat ε c w) = w := by
  have hdom : w ∈ ctPhiDom ε c := H.body.2.1 w hw hw0.le
  have h := (ctPhiC_spec H.body.1).2 w hdom hw0 (by rw [abs_of_neg hw0]; linarith)
  unfold ctPhiR
  rw [h]; simp

end CtRealChartHyp

namespace CtWinHyp

variable {ε c ρ M : ℝ}

lemma mu_mul_lt (W : CtWinHyp ε c ρ M) {y : ℝ} (hc : 0 < c) (hy : -ctRmax ctChartC1 c ≤ y) : -ρ < ctMu c * y := by
  have := mul_le_mul_of_nonneg_left hy (ctMu_pos hc).le
  have h := W.nu
  nlinarith

end CtWinHyp

section Budget

variable {ε c C ρ M : ℝ}

/-- `ctPhi` and the real restriction `ctPhiR` of the complex chart agree near every `y ∈ (-R_max, -1)`. -/
lemma ctPhi_eventuallyEq (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) {a : ℝ} (ha1 : a < -1)
    (haR : -ctRmax ctChartC1 c < a) : ctPhi ε c =ᶠ[𝓝 a] ctPhiR ε c := by
  have hU : IsOpen (Ioo (-ctRmax ctChartC1 c) (-1 : ℝ)) := isOpen_Ioo
  filter_upwards [hU.mem_nhds ⟨haR, ha1⟩] with y hy
  obtain ⟨u, hu, huv, huφ⟩ := ctPhi_pre W.win H.c_pos W.cM W.lam hy.2 (W.mu_mul_lt H.c_pos hy.1.le)
  rw [huφ, ← huv, H.ctPhiR_ctUhat (by linarith [hu.2]) (by linarith [hu.1, hy.1])]

/-- **`ctFc = ctFr` at the Airy nodes** (real inverse chart and complex chart give the same `f_c`). -/
lemma ctFc_eq_ctFr (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) (f : ℝ → ℝ) {a : ℝ} (ha1 : a < -1)
    (haR : -ctRmax ctChartC1 c < a) : ctFc ε c f a = ctFr ε c f a := by
  have hev := ctPhi_eventuallyEq H W ha1 haR
  have habs : |a| < ctRmax ctChartC1 c := abs_lt.2 ⟨haR, by linarith [H.Rm_pos]⟩
  unfold ctFc ctFr
  rw [hev.self_of_nhds, hev.deriv_eq, (H.ctPhiR_hasDerivAt habs).deriv]

/-- `φ_c(-R) = ctPhi(-R) = -R'` (`R' = ctRprime`), for `1 ≤ R ≤ R_max`. -/
lemma ctPhiR_neg_R (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M) {R : ℝ} (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) : ctPhiR ε c (-R) = -ctRprime ε c R := by
  have haw : -ρ < ctMu c * (-R) := W.mu_mul_lt H.c_pos (by linarith)
  obtain ⟨u, hu, huv, huφ⟩ := ctPhi_pre W.win H.c_pos W.cM W.lam (a := -R) (by linarith) haw
  unfold ctRprime
  rw [huφ, neg_neg, ← huv, H.ctPhiR_ctUhat (by linarith [hu.2]) (by linarith [hu.1])]

end Budget

section Nodes

open scoped Real

/-- `H(a)/Ai'(a)²` at a node, as the real-chart expression. -/
lemma ctBudget_nodes {ε c C ρ M R : ℝ} {f : ℝ → ℝ} (H : CtRealChartHyp ε c C) (W : CtWinHyp ε c ρ M)
    (hRm : R ≤ ctRmax ctChartC1 c) {N : ℕ}
    (hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R)) :
    (((ctBudget R ε c f + ε * f 0 : ℝ)) : ℂ) =
      ∑ n ∈ Finset.Icc 1 N, (ctW6 R (airyZero n : ℂ) * ctFcC ctChartC1 ε c f (airyZero n : ℂ)) /
        (deriv airyAiC (airyZero n : ℂ)) ^ 2 := by
  set t : ℕ → ℝ := fun n => if -R < airyZero (n + 1) then
      ctH R ε c f (airyZero (n + 1)) / (deriv airyAi (airyZero (n + 1))) ^ 2 else 0 with ht
  have hbud : ctBudget R ε c f + ε * f 0 = ∑' n, t n := by
    unfold ctBudget; ring
  have hzero : ∀ n ∉ Finset.range N, t n = 0 := by
    intro n hn
    have hn' : ¬ (n + 1 ≤ N) := by simpa using hn
    have : ¬ (-R < airyZero (n + 1)) := fun h => hn' ((hN (n + 1) (by omega)).2 (by linarith))
    simp [ht, this]
  rw [hbud, tsum_eq_sum hzero]
  push_cast
  have hshift : ∑ n ∈ Finset.range N, (t n : ℂ) = ∑ k ∈ Finset.Icc 1 N, (t (k - 1) : ℂ) := by
    refine Finset.sum_nbij' (fun n => n + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn; simp at hn ⊢; omega
    · intro k hk; simp at hk ⊢; omega
    · intro n _; simp
    · intro k hk; simp at hk ⊢; omega
    · intro n _; simp
  rw [hshift]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
  have hlt : -airyZero k < R := (hN k hk1).1 hkN
  have hk' : k - 1 + 1 = k := by omega
  have ha1 : airyZero k < -1 := by
    have := airyZero_anti (le_refl 1) hk1
    have h1 := airyZero_one
    linarith [h1.2]
  have haR : -ctRmax ctChartC1 c < airyZero k := by linarith
  have habs : |airyZero k| < ctRmax ctChartC1 c := abs_lt.2 ⟨haR, by linarith [H.Rm_pos]⟩
  simp only [ht, hk']
  rw [if_pos (by linarith)]
  rw [deriv_airyAiC_ofReal, H.ctFcC_ofReal habs, ← ctFc_eq_ctFr H W f ha1 haR]
  unfold ctH ctW6
  rw [deriv_airyAi]
  push_cast
  rfl

end Nodes

/-- info: 'FormalResearch.SignUncertainty.ctBudget_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctBudget_nodes

end FormalResearch.SignUncertainty

module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscBound

/-!
# `ct:dyadic` (3)-(4), `(ct:rosc)`: proof of the Hankel bookkeeping `CtRoscBook`

`constant_terms_lower.tex`, `ct:dyadic` (3), `(ct:rosc)` and (4), expansion of `I_R(H)`.  `ct_rosc_book : 0 < c₁ → c₁ ≤ ctChartC1 → CtRoscBook c₁` (for every such `c₁`):
the concrete quantity `budget + M_all + 2(s₁ - s₂)` equals `ctRoscAiry` up to `10 c^{-4/3}`.

The pieces (in separate modules): `T1` the budget `tsum` is the node sum (`ctBudget_nodes`, `CtRoscBudget`); `T2`-`T4` the expansion
`∫_{-R}^R W₆ f_c = ∫ f_c - ∫_{-R}^0 w_R f_c - ∫_0^R w_R f_c` with the mass identity `∫_ℝ h dL = ε f(0)` and the taper transport (`ct_rosc_mass`, `CtRoscMass`, `ct_trans_transport`);
`T5` the positive lobe, from the total mass and the deep-lobe mass instead of the pointwise decay of `Ψ̃` (`pos_lobe_le`, `CtRoscPos`); `T6` the edge strip `s₂^{lit} - s₂^L`
(`slit_edge`, `CtRoscAlg`).  The `ψ_ε`-window and chart constants are chosen once, independent of `c` (`ct_rosc_setup`).

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma eventually_rpow_ge {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (y : ℝ) : ∀ᶠ c : ℝ in atTop, y ≤ k * c ^ a :=
  ((tendsto_rpow_atTop ha).const_mul_atTop hk).eventually_ge_atTop y

lemma eventually_rpow_neg_le {a : ℝ} (ha : 0 < a) (C : ℝ) {y : ℝ} (hy : 0 < y) :
    ∀ᶠ c : ℝ in atTop, C * c ^ (-a) ≤ y := by
  have := (tendsto_rpow_neg_atTop ha).const_mul C
  rw [mul_zero] at this
  exact this.eventually (Iic_mem_nhds hy)

/-- **Window and chart constants independent of `c`**: the chart constant `C` of `CtChartComplex ctChartC1`, `c₀`, and for each sign a `ψ_ε`-window `(ρ, M)` with `μ R_max < ρ`. -/
lemma ct_rosc_setup : ∃ C c₀ : ℝ, 0 ≤ C ∧ (∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c → CtChartBody ctChartC1 ε c C) ∧
    ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∃ ρ M : ℝ, PsiWin ε ρ M ∧ 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * ctChartC1 ^ 2 < ρ := by
  obtain ⟨C, c₀, hC, H⟩ := (ctChartComplex_iff ctChartC1).1 ctChartComplex_ctChartC1
  refine ⟨C, max c₀ 1, hC, fun ε hε c hc => H ε hε c ((le_max_left _ _).trans hc), fun ε hε => ?_⟩
  have hc1 : (0 : ℝ) < max c₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb := H ε hε (max c₀ 1) (le_max_left _ _)
  have hRm := ctRmax_pos ctChartC1_pos hc1
  obtain ⟨-, ρ, M, hW, -, hlt⟩ := hb.2.1 (-ctRmax ctChartC1 (max c₀ 1)) le_rfl (by linarith)
  refine ⟨ρ, M, hW, ?_⟩
  rw [← ctMu_mul_ctRmax (c₁ := ctChartC1) hc1]
  have : ctMu (max c₀ 1) * -ctRmax ctChartC1 (max c₀ 1) = -(ctMu (max c₀ 1) * ctRmax ctChartC1 (max c₀ 1)) := by ring
  linarith

/-- **`CtRoscBook` for one sign**: the bound `10 c^{-4/3}` for all large `c`. -/
lemma ct_rosc_book_core {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {C c₀ : ℝ} (hC : 0 ≤ C)
    (hbody : ∀ c : ℝ, c₀ ≤ c → CtChartBody ctChartC1 ε c C) {ρ M : ℝ} (hW : PsiWin ε ρ M)
    (hν : 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * ctChartC1 ^ 2 < ρ) {c₁ : ℝ} (hc₁ : 0 < c₁) (hle : c₁ ≤ ctChartC1) :
    ∃ c₂ : ℝ, ∀ c : ℝ, c₂ ≤ c → ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
        ∀ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R)) →
          ‖((ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) : ℝ) : ℂ) -
              ctRoscAiry R ε c f N‖ ≤ 10 * c ^ (-(4 / 3) : ℝ) := by
  have hM0 := hW.2.1
  have hb : 0 < langerLobeK * c₁ ^ 2 / 2 := by have := langerLobeK_pos; positivity
  have hB : 0 < 5 * (langerLobeK * c₁ ^ 2 / 2) ^ (3 / 2 : ℝ) := by positivity
  have hev : ∀ᶠ c : ℝ in atTop, c₀ ≤ c ∧ 3e6 ≤ c ∧ 2 * M ≤ c ∧ (2 * M) ^ 3 ≤ c ∧ C * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 ∧
      2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧ RoscRates c₁ C M c := by
    filter_upwards [eventually_ge_atTop c₀, eventually_ge_atTop (3e6 : ℝ), eventually_ge_atTop (2 * M),
      eventually_ge_atTop ((2 * M) ^ 3), eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) C (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2) 2, rate_Ar, rate_exp_lin,
      rate_exp_rpow hB, rate_pow_inv (M / c₁ ^ 2), eventually_rpow_ge (by norm_num : (0 : ℝ) < 5 / 9) hb 1,
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) (2 * C) (by norm_num : (0 : ℝ) < 1),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 5 / 9) (by positivity : 0 < c₁ ^ 2) 1, eventually_ge_atTop (1 : ℝ)]
      with c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    exact ⟨h1, h2, h3, h4, h5, h6, ⟨h14, h7.1, h7.2, h8, h9, h10, h11, h12.trans h13⟩⟩
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 hev
  refine ⟨c₂, fun c hc f hf hM R hR N hN => ?_⟩
  obtain ⟨hc0', hc3, hcM, hcM3, hsm, hR1', hrates⟩ := hc₂ c hc
  have hc0 : 0 < c := by linarith
  have hbody' := hbody c hc0'
  have hlam : ctLam c * M ≤ 1 / 2 := by
    have hl := ctLam_le hc0
    have h13 : 2 * M ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hcM3 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num,
        Real.rpow_one] at this
    have hp : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    calc ctLam c * M ≤ (c ^ (1 / 3 : ℝ))⁻¹ * M := mul_le_mul_of_nonneg_right hl hM0
      _ ≤ 1 / 2 := by
        rw [inv_mul_le_iff₀ hp]; linarith
  have hH : CtRealChartHyp ε c C := ⟨hbody', hC, hc3, hsm⟩
  have hWin : CtWinHyp ε c ρ M := ⟨hW, hcM, hlam, by rw [ctMu_mul_ctRmax hc0]; exact hν⟩
  have hcC : C * c ^ (-(1 / 3 : ℝ)) < 1 := by linarith
  obtain ⟨ρ', hρ', hFd, -, -⟩ := ctFcC_holo ctChartC1_pos ctChartC1_le hbody' hc3 hcC hf
  have hcont : ContinuousOn (fun u : ℝ => ctFcC ctChartC1 ε c f (u : ℂ))
      (Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c)) := by
    refine hFd.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun u hu => ?_)
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  have X : CtRoscCtx ε c C ρ M f := ⟨hH, hWin, hf, hε, hM, hcont⟩
  have hRm : R ≤ ctRmax ctChartC1 c := hR.2.trans (ctRmax_mono hc0.le hc₁.le hle)
  have hR1 : 1 < R := lt_of_lt_of_le (by linarith) hR.1
  rw [X.ctRosc_alg hR1 hRm hN, Complex.norm_real, Real.norm_eq_abs]
  exact ctRosc_bound X hc₁ hrates hR1 hRm hR.1

/-- **`CtRoscBook`** (the Hankel bookkeeping of `(ct:rosc)`; `constant_terms_lower.tex`, `ct:dyadic` (3)-(4)): for every `0 < c₁ ≤ ctChartC1`,
`|budget + M_all + 2(s₁ - s₂) - ctRoscAiry| ≤ 10 c^{-4/3}` at every good radius in `[c₁²c^{2/3}, 4c₁²c^{2/3}]`.  Proved. -/
theorem ct_rosc_book {c₁ : ℝ} (hc₁ : 0 < c₁) (hle : c₁ ≤ ctChartC1) : CtRoscBook c₁ := by
  obtain ⟨C, c₀, hC, hbody, hwin⟩ := ct_rosc_setup
  obtain ⟨ρ₁, M₁, hW₁, hν₁⟩ := hwin 1 (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hW₂, hν₂⟩ := hwin (-1) (Or.inr rfl)
  obtain ⟨c₂₁, h₁⟩ := ct_rosc_book_core (Or.inl rfl) hC (hbody 1 (Or.inl rfl)) hW₁ hν₁ hc₁ hle
  obtain ⟨c₂₂, h₂⟩ := ct_rosc_book_core (Or.inr rfl) hC (hbody (-1) (Or.inr rfl)) hW₂ hν₂ hc₁ hle
  refine ⟨10, max c₂₁ c₂₂, fun c hc ε hε T f hf hM _ _ R hR _ N hN => ?_⟩
  rcases hε with rfl | rfl
  · exact h₁ c ((le_max_left _ _).trans hc) f hf.toIsHankelEigenfn hM R hR N hN
  · exact h₂ c ((le_max_right _ _).trans hc) f hf.toIsHankelEigenfn hM R hR N hN

/-- info: 'FormalResearch.SignUncertainty.ct_rosc_book' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_rosc_book

end FormalResearch.SignUncertainty

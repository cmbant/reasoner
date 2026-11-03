module

public import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQK

/-!
# The Rényi envelope above order one, assuming the sharp bound QV

`SharpQuadraticVarianceBound` is (QV), `thm:fqe-sharp-quadratic-variance`: `F² + 3P(P - 1) ≥ 6 V_P` for every
unit pure four-qubit state (an exact-rational certificate in the paper, QVA; a hypothesis here).

* `qk_of_qv_scalar`: the scalar implication behind `thm:fqe-quadratic-variance` (QK as a corollary of QV).
  On `P ≤ 3/2` the defect of (QK) exceeds that of (QV) by `3(P-1)(3/2-P) ≥ 0`; above `3/2` the purity box
  `p_j ∈ [1/4, 1]` gives (QK) without (QV).
* `quadraticVarianceBound_of_sharp`: (QV) ⇒ (QK) for states.
* `renyi_envelope_above_one_QV`: `cor:fqe-renyi-gw` for `q > 1`, assuming only (QV).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **(QV), `thm:fqe-sharp-quadratic-variance`**: `F² + 3P(P-1) ≥ 6 V_P` for every unit pure four-qubit
state (an exact-rational certificate in the paper; hypothesis here). -/
def SharpQuadraticVarianceBound : Prop :=
  ∀ ψ : Psi, normSqPsi ψ = 1 →
    6 * ((cutPurity12 ψ - purity ψ / 3) ^ 2 + (cutPurity13 ψ - purity ψ / 3) ^ 2
        + (cutPurity14 ψ - purity ψ / 3) ^ 2) ≤ sexticF ψ ^ 2 + 3 * purity ψ * (purity ψ - 1)

/-- QV implies QK for any three purities in `[1/4, 1]` with sum at least one. -/
theorem qk_of_qv_scalar {a b c F : ℝ} (ha : 1 / 4 ≤ a) (ha' : a ≤ 1) (hb : 1 / 4 ≤ b) (hb' : b ≤ 1)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 1) (hP : 1 ≤ a + b + c)
    (hQV : 6 * ((a - (a + b + c) / 3) ^ 2 + (b - (a + b + c) / 3) ^ 2 + (c - (a + b + c) / 3) ^ 2)
      ≤ F ^ 2 + 3 * (a + b + c) * (a + b + c - 1)) :
    6 * ((a - (a + b + c) / 3) ^ 2 + (b - (a + b + c) / 3) ^ 2 + (c - (a + b + c) / 3) ^ 2)
      ≤ F ^ 2 + 9 / 2 * (a + b + c - 1) := by
  rcases le_total (a + b + c) (3 / 2) with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 h)]
  · nlinarith [sq_nonneg F, mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'),
      mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 hc'), mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hc'),
      mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb), mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hc),
      mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hc), mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 ha'),
      mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 hb'), mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hc'),
      mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 ha'), mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hb'),
      mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hc')]

/-- A probability vector of length four has purity at most one. -/
theorem pur_le_one {l : Fin 4 → ℝ} (h : IsProb4 l) : pur l ≤ 1 := by
  have h0 := h.1; have h1 := h.2
  unfold pur; simp only [Fin.sum_univ_four] at h1 ⊢
  nlinarith [h0 0, h0 1, h0 2, h0 3, mul_nonneg (h0 0) (h0 1), mul_nonneg (h0 0) (h0 2),
    mul_nonneg (h0 0) (h0 3), mul_nonneg (h0 1) (h0 2), mul_nonneg (h0 1) (h0 3), mul_nonneg (h0 2) (h0 3)]

/-- **QK is a corollary of QV** (`thm:fqe-quadratic-variance` from `thm:fqe-sharp-quadratic-variance`). -/
theorem quadraticVarianceBound_of_sharp (hQV : SharpQuadraticVarianceBound) : QuadraticVarianceBound := by
  intro ψ hψ
  have p2 := isProb4_spec4 (isProb12 hψ)
  have p3 := isProb4_spec4 (isProb13 hψ)
  have p4 := isProb4_spec4 (isProb14 hψ)
  have e2 : pur (cutSpec₂ ψ) = cutPurity12 ψ := by unfold cutSpec₂ cutPurity12; rw [pur_spec4]
  have e3 : pur (cutSpec₃ ψ) = cutPurity13 ψ := by unfold cutSpec₃ cutPurity13; rw [pur_spec4]
  have e4 : pur (cutSpec₄ ψ) = cutPurity14 ψ := by unfold cutSpec₄ cutPurity14; rw [pur_spec4]
  have hP := purity_ge ψ
  rw [hψ] at hP
  have h := hQV ψ hψ
  have hpe : purity ψ = cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ := by
    rw [← Pm_cutSpec, ← e2, ← e3, ← e4]; rfl
  rw [hpe] at hP h ⊢
  have := qk_of_qv_scalar (F := sexticF ψ) (e2 ▸ pur_ge_quarter p2) (e2 ▸ pur_le_one p2)
    (e3 ▸ pur_ge_quarter p3) (e3 ▸ pur_le_one p3) (e4 ▸ pur_ge_quarter p4) (e4 ▸ pur_le_one p4)
    (by linarith) h
  exact this

/-- **`cor:fqe-renyi-gw` for `q > 1`**, assuming only (QV). -/
theorem renyi_envelope_above_one_QV (hQV : SharpQuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) :
    meanRenyi q ψ ≤ max (hsRenyi q) (5 / 3) ∧
    (5 / 3 < hsRenyi q → meanRenyi q ψ = hsRenyi q → LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) ∧
    (hsRenyi q < 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) ∧
    (hsRenyi q = 5 / 3 → meanRenyi q ψ = 5 / 3 →
      IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :=
  renyi_envelope_above_one_QK (quadraticVarianceBound_of_sharp hQV) hψ hq

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.quadraticVarianceBound_of_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quadraticVarianceBound_of_sharp

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.renyi_envelope_above_one_QV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms renyi_envelope_above_one_QV

end FormalResearch.FourQubitEntropy.RenyiFull

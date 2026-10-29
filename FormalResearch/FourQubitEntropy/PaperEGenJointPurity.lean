import FormalResearch.FourQubitEntropy.RenyiTwoUp
import FormalResearch.FourQubitEntropy.RenyiRankTwo
import FormalResearch.FourQubitEntropy.Corollaries

/-!
# The joint purity bound (JV) from the quadratic variance bound (QK)

Paper E, `purity_variance_certificate.tex`, `thm:fqe-joint-purity`: for every pure four-qubit state
`T + Σ_j p_j² ≤ 3P - 9/4` (`p_j = tr ρ_{1j}²`).  The paper derives it from the quadratic variance
inequality (QK) `F² + (9/2)(P-1) ≥ 6 V_P`, `V_P = Σ_j (p_j - P/3)²` (an exact-rational certificate,
`thm:fqe-quadratic-variance`, **not** formalized), together with `F ≥ 0` (formalized),
`p_j ∈ [1/4, 1]` and `P ≥ 1`.

This file formalizes that derivation, i.e. the implication `(QK) ⇒ (JV)`:

* `joint_purity_real`: the elementary real inequality in `(p₂, p₃, p₄, F)`: the identity (JI)
  `12 G = F(1-2F) + 2(P-1)(3-2P) + 2Q` for `1 ≤ P ≤ 3/2`, `F ≤ 1/2`, and the three box ranges
  of (JB) otherwise.
* `joint_purity_of_QK`: the statement about a unit four-qubit vector, with (QK) as an explicit
  hypothesis (stated with the cut purities `p_j = Σ_i λ_i²`).

The equality classification of (JV) is not formalized.

Trust: no `native_decide` here.  `joint_purity_real` and `joint_purity_of_QK` use only `propext`,
`Classical.choice`, `Quot.sound`; the latter uses the kernel-checked sextic identity of `Identity.lean` (via
`sexticF_nonneg`, `F ≥ 0`).
-/

namespace FormalResearch.FourQubitEntropy

/-- The case analysis of (JV) in terms of `P`, `U = Σ p_j²` and `F`. -/
theorem joint_purity_PU {P U F : ℝ} (hP : 1 ≤ P) (hP3 : P ≤ 3) (hF : 0 ≤ F)
    (hU1 : U ≤ P ^ 2 - P + 3 / 8) (hU2 : U ≤ P ^ 2 - 5 / 2 * P + 21 / 8)
    (hU3 : U ≤ 2 + (P - 2) ^ 2)
    (hQK : 6 * (U - P ^ 2 / 3) ≤ F ^ 2 + 9 / 2 * (P - 1)) :
    (17 * P - 12 - F) / 12 + U ≤ 3 * P - 9 / 4 := by
  by_cases hA : P ≤ 3 / 2 ∧ F ≤ 1 / 2
  · obtain ⟨hPa, hFa⟩ := hA
    -- the identity (JI): 12 G = F(1-2F) + 2(P-1)(3-2P) + 2Q
    have t1 : 0 ≤ F * (1 - 2 * F) := mul_nonneg hF (by linarith)
    have t2 : 0 ≤ (P - 1) * (3 - 2 * P) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · rw [not_and_or] at hA
    rcases hA with hA | hA
    · push Not at hA
      by_cases hB : P ≤ 9 / 4
      · have : 0 ≤ (2 * P - 3) * (31 - 12 * P) := mul_nonneg (by linarith) (by linarith)
        nlinarith
      · push Not at hB
        have : 0 ≤ (P - 9 / 4) * (3 - P) := mul_nonneg (by linarith) (by linarith)
        nlinarith
    · push Not at hA
      by_cases hB : P ≤ 3 / 2
      · have : 0 ≤ (P - 1) * (19 - 12 * P) := mul_nonneg (by linarith) (by linarith)
        nlinarith
      · push Not at hB
        by_cases hC : P ≤ 9 / 4
        · have : 0 ≤ (2 * P - 3) * (31 - 12 * P) := mul_nonneg (by linarith) (by linarith)
          nlinarith
        · push Not at hC
          have : 0 ≤ (P - 9 / 4) * (3 - P) := mul_nonneg (by linarith) (by linarith)
          nlinarith

/-- The elementary inequality behind (JV), in terms of the three cut purities and `F`. -/
theorem joint_purity_real {p₂ p₃ p₄ F : ℝ}
    (h2 : 1 / 4 ≤ p₂) (h3 : 1 / 4 ≤ p₃) (h4 : 1 / 4 ≤ p₄)
    (h2' : p₂ ≤ 1) (h3' : p₃ ≤ 1) (h4' : p₄ ≤ 1)
    (hP : 1 ≤ p₂ + p₃ + p₄) (hF : 0 ≤ F)
    (hQK : 6 * ((p₂ - (p₂ + p₃ + p₄) / 3) ^ 2 + (p₃ - (p₂ + p₃ + p₄) / 3) ^ 2
        + (p₄ - (p₂ + p₃ + p₄) / 3) ^ 2) ≤ F ^ 2 + 9 / 2 * (p₂ + p₃ + p₄ - 1)) :
    (17 * (p₂ + p₃ + p₄) - 12 - F) / 12 + (p₂ ^ 2 + p₃ ^ 2 + p₄ ^ 2)
      ≤ 3 * (p₂ + p₃ + p₄) - 9 / 4 := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ p₂ = a + 1 / 4 := ⟨p₂ - 1 / 4, by linarith, by ring⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ p₃ = b + 1 / 4 := ⟨p₃ - 1 / 4, by linarith, by ring⟩
  obtain ⟨c, hc, rfl⟩ : ∃ c, 0 ≤ c ∧ p₄ = c + 1 / 4 := ⟨p₄ - 1 / 4, by linarith, by ring⟩
  have ha' : 0 ≤ 3 / 4 - a := by linarith
  have hb' : 0 ≤ 3 / 4 - b := by linarith
  have hc' : 0 ≤ 3 / 4 - c := by linarith
  have e0 : (a + 1 / 4) + (b + 1 / 4) + (c + 1 / 4) = a + b + c + 3 / 4 := by ring
  rw [e0] at hP hQK ⊢
  refine joint_purity_PU (U := (a + 1 / 4) ^ 2 + (b + 1 / 4) ^ 2 + (c + 1 / 4) ^ 2) hP
    (by linarith) hF ?_ ?_ ?_ ?_
  · have : (a + b + c + 3 / 4) ^ 2 - (a + b + c + 3 / 4) + 3 / 8
        - ((a + 1 / 4) ^ 2 + (b + 1 / 4) ^ 2 + (c + 1 / 4) ^ 2) = 2 * (a * b + b * c + a * c) := by
      ring
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
  · have : (a + b + c + 3 / 4) ^ 2 - 5 / 2 * (a + b + c + 3 / 4) + 21 / 8
        - ((a + 1 / 4) ^ 2 + (b + 1 / 4) ^ 2 + (c + 1 / 4) ^ 2)
        = 8 / 3 * ((3 / 4 - a) * (3 / 4 - b) * (3 / 4 - c) + a * b * c) := by
      ring
    nlinarith [mul_nonneg (mul_nonneg ha' hb') hc', mul_nonneg (mul_nonneg ha hb) hc]
  · have : 2 + (a + b + c + 3 / 4 - 2) ^ 2
        - ((a + 1 / 4) ^ 2 + (b + 1 / 4) ^ 2 + (c + 1 / 4) ^ 2)
        = 2 * ((3 / 4 - a) * (3 / 4 - b) + (3 / 4 - b) * (3 / 4 - c) + (3 / 4 - a) * (3 / 4 - c)) := by
      ring
    nlinarith [mul_nonneg ha' hb', mul_nonneg hb' hc', mul_nonneg ha' hc']
  · nlinarith

/-- Cut purities of a unit vector: `p₁ⱼ = Σ_i λ_i²`. -/
noncomputable def cutPurity12 (ψ : Psi) : ℝ := ∑ i, (red12_herm ψ).eigenvalues i ^ 2
noncomputable def cutPurity13 (ψ : Psi) : ℝ := ∑ i, (red13_herm ψ).eigenvalues i ^ 2
noncomputable def cutPurity14 (ψ : Psi) : ℝ := ∑ i, (red14_herm ψ).eigenvalues i ^ 2

theorem purity_eq_cutPurities (ψ : Psi) :
    purity ψ = cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ :=
  purity_eq_sum_sq ψ

theorem cutPurity_le_one {l : Fin 2 × Fin 2 → ℝ} (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    ∑ i, l i ^ 2 ≤ 1 := by
  calc ∑ i, l i ^ 2 ≤ ∑ i, l i := Finset.sum_le_sum fun i _ => by
        have h1 : l i ≤ 1 := by
          rw [← hs]
          exact Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)
        nlinarith [hl i]
    _ = 1 := hs

/-- **(QK) ⇒ (JV)** (`thm:fqe-joint-purity`, the derivation from `thm:fqe-quadratic-variance`).
For a unit four-qubit vector satisfying the quadratic purity-variance inequality
`F² + (9/2)(P-1) ≥ 6 V_P`, one has `T + Σ_j p_j² ≤ 3P - 9/4`.  The hypothesis (QK) is the
exact-rational certificate of the paper and is not proved here. -/
theorem joint_purity_of_QK (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (hQK : 6 * ((cutPurity12 ψ - purity ψ / 3) ^ 2 + (cutPurity13 ψ - purity ψ / 3) ^ 2
        + (cutPurity14 ψ - purity ψ / 3) ^ 2) ≤ sexticF ψ ^ 2 + 9 / 2 * (purity ψ - 1)) :
    cubicMoment ψ + (cutPurity12 ψ ^ 2 + cutPurity13 ψ ^ 2 + cutPurity14 ψ ^ 2)
      ≤ 3 * purity ψ - 9 / 4 := by
  have i12 := isProb12 hψ
  have i13 := isProb13 hψ
  have i14 := isProb14 hψ
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hF := sexticF_nonneg ψ
  have hT : cubicMoment ψ = (17 * purity ψ - 12 - sexticF ψ) / 12 := by
    unfold sexticF; rw [hψ]; ring
  have hPe := purity_eq_cutPurities ψ
  have key := joint_purity_real (p₂ := cutPurity12 ψ) (p₃ := cutPurity13 ψ) (p₄ := cutPurity14 ψ)
    (F := sexticF ψ) (sum_sq_ge_quarter i12.2) (sum_sq_ge_quarter i13.2) (sum_sq_ge_quarter i14.2)
    (cutPurity_le_one i12.1 i12.2) (cutPurity_le_one i13.1 i13.2) (cutPurity_le_one i14.1 i14.2)
    (by rw [← hPe]; linarith) hF (by rw [← hPe]; exact hQK)
  rw [hT, hPe]
  exact key

/-- info: 'FormalResearch.FourQubitEntropy.joint_purity_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms joint_purity_real

/-- info: 'FormalResearch.FourQubitEntropy.joint_purity_of_QK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms joint_purity_of_QK

end FormalResearch.FourQubitEntropy

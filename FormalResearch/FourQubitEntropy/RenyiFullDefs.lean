import FormalResearch.FourQubitEntropy.RenyiSingleCrossing
import FormalResearch.FourQubitEntropy.PaperEGenJointPurity
import FormalResearch.FourQubitEntropy.PaperECriticalRenyiEq
import FormalResearch.FourQubitEntropy.PaperECriticalRenyiThreshold

/-!
# The classical relaxation of the Rényi envelope above one: definitions

Paper E, `thm:fqe-renyi-classical` (`renyi_uncapped_covering.tex`) and `lem:fqe-dual`.

Three four-point probability vectors `λ² , λ³, λ⁴` (the spectra of the three balanced cuts) with
`p_j = Σ λ²`, `t_j = Σ λ³`, `P = Σ p_j`, `T = Σ t_j`, `ε = P - 1`, `F = 17P - 12T - 12`,
`V_P = Σ (p_j - P/3)²` and `E_q = mean of the three Rényi entropies`.
The *relaxation* keeps only `P ≥ 1`, `F ≥ 0` and the quadratic variance bound (QK)
`F² + (9/2)(P-1) ≥ 6 V_P`.

This file only sets up the objects; the statements of the per-spectrum certificates and of the
classical theorem are in `RenyiFullClassical.lean`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-! ### Moments of a four-point spectrum and of a triple -/

/-- Purity `p = Σ λᵢ²`. -/
noncomputable def pur (l : Fin 4 → ℝ) : ℝ := ∑ i, l i ^ 2

/-- Third moment `t = Σ λᵢ³`. -/
noncomputable def cub (l : Fin 4 → ℝ) : ℝ := ∑ i, l i ^ 3

/-- `P = Σ_j p_j` of a triple. -/
noncomputable def Pm (l₂ l₃ l₄ : Fin 4 → ℝ) : ℝ := pur l₂ + pur l₃ + pur l₄

/-- `T = Σ_j t_j` of a triple. -/
noncomputable def Tm (l₂ l₃ l₄ : Fin 4 → ℝ) : ℝ := cub l₂ + cub l₃ + cub l₄

/-- The moment slack `F = 17 P - 12 T - 12`. -/
noncomputable def Fm (l₂ l₃ l₄ : Fin 4 → ℝ) : ℝ := 17 * Pm l₂ l₃ l₄ - 12 * Tm l₂ l₃ l₄ - 12

/-- `V_P = Σ_j (p_j - P/3)²`. -/
noncomputable def Vm (l₂ l₃ l₄ : Fin 4 → ℝ) : ℝ :=
  (pur l₂ - Pm l₂ l₃ l₄ / 3) ^ 2 + (pur l₃ - Pm l₂ l₃ l₄ / 3) ^ 2 + (pur l₄ - Pm l₂ l₃ l₄ / 3) ^ 2

/-- The quadratic purity-variance inequality (QK) for a triple. -/
def QKTriple (l₂ l₃ l₄ : Fin 4 → ℝ) : Prop :=
  6 * Vm l₂ l₃ l₄ ≤ Fm l₂ l₃ l₄ ^ 2 + 9 / 2 * (Pm l₂ l₃ l₄ - 1)

/-- A triple of the classical relaxation: probability vectors with `P ≥ 1`, `F ≥ 0` and (QK). -/
structure RelaxTriple (l₂ l₃ l₄ : Fin 4 → ℝ) : Prop where
  prob₂ : IsProb4 l₂
  prob₃ : IsProb4 l₃
  prob₄ : IsProb4 l₄
  P_ge : 1 ≤ Pm l₂ l₃ l₄
  F_ge : 0 ≤ Fm l₂ l₃ l₄
  QK : QKTriple l₂ l₃ l₄

/-! ### The distinguished spectra -/

/-- The uniform-two spectrum `c₁ = (1/2, 1/2, 0, 0)`. -/
noncomputable def c1 : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- The uniform-four spectrum `c₂ = (1/4)⁴`. -/
noncomputable def c2 : Fin 4 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4]

/-- Uniform on two points: a permutation of `c₁ = (1/2, 1/2, 0, 0)`. -/
def UniformTwo (l : Fin 4 → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ l i = 1 / 2 ∧ l j = 1 / 2 ∧ ∀ k, k ≠ i → k ≠ j → l k = 0

/-- Uniform on four points: `c₂ = (1/4)⁴`. -/
def UniformFour (l : Fin 4 → ℝ) : Prop := ∀ i, l i = 1 / 4

/-- `(c₁, c₂, c₂)` up to a permutation of the three cuts and of each spectrum (the cluster triple). -/
def IsClusterTriple (l₂ l₃ l₄ : Fin 4 → ℝ) : Prop :=
  (UniformTwo l₂ ∧ UniformFour l₃ ∧ UniformFour l₄) ∨
  (UniformFour l₂ ∧ UniformTwo l₃ ∧ UniformFour l₄) ∨
  (UniformFour l₂ ∧ UniformFour l₃ ∧ UniformTwo l₄)

/-- Three HS spectra (each a permutation of `σ = (1/2, 1/6, 1/6, 1/6)`). -/
def IsHsTriple (l₂ l₃ l₄ : Fin 4 → ℝ) : Prop := IsHsPerm l₂ ∧ IsHsPerm l₃ ∧ IsHsPerm l₄

/-! ### The two anchor orders and the hypotheses on the dual -/

/-- The lower anchor `q_s = 1587/1000`. -/
noncomputable def qS : ℝ := 1587 / 1000

/-- The upper anchor `q_u = 8/5`. -/
noncomputable def qU : ℝ := 8 / 5

/-- `h_q = H_q(σ)`, the mean Rényi entropy of `M₄` (`hsRenyi q = renyiSpec q hsSpec`). -/
noncomputable def hsq (q : ℝ) : ℝ := renyiSpec q hsSpec

theorem hsq_eq (q : ℝ) : hsq q = hsRenyi q := (hsRenyi_eq q).symm

/-- The quantity `E_q` of a triple (re-exported from `renyiE`). -/
noncomputable def Em (q : ℝ) (l₂ l₃ l₄ : Fin 4 → ℝ) : ℝ := renyiE q l₂ l₃ l₄


/-! ### Elementary facts -/

theorem pur_ge_quarter {l : Fin 4 → ℝ} (h : IsProb4 l) : 1 / 4 ≤ pur l := by
  obtain ⟨-, hs⟩ := h
  unfold pur
  simp only [Fin.sum_univ_four] at hs ⊢
  nlinarith [sq_nonneg (l 0 - l 1), sq_nonneg (l 0 - l 2), sq_nonneg (l 0 - l 3),
    sq_nonneg (l 1 - l 2), sq_nonneg (l 1 - l 3), sq_nonneg (l 2 - l 3)]

theorem pur_eq_quarter {l : Fin 4 → ℝ} (h : IsProb4 l) (hp : pur l = 1 / 4) : UniformFour l := by
  obtain ⟨-, hs⟩ := h
  unfold pur at hp
  simp only [Fin.sum_univ_four] at hs hp
  have e : (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2 = 0 := by
    nlinarith
  have n0 := sq_nonneg (l 0 - 1 / 4)
  have n1 := sq_nonneg (l 1 - 1 / 4)
  have n2 := sq_nonneg (l 2 - 1 / 4)
  have n3 := sq_nonneg (l 3 - 1 / 4)
  have h0 : l 0 = 1 / 4 := by nlinarith
  have h1 : l 1 = 1 / 4 := by nlinarith
  have h2 : l 2 = 1 / 4 := by nlinarith
  have h3 : l 3 = 1 / 4 := by nlinarith
  intro i; fin_cases i <;> assumption

theorem uniformFour_pur {l : Fin 4 → ℝ} (h : UniformFour l) : pur l = 1 / 4 := by
  unfold pur; simp only [Fin.sum_univ_four, h _]; norm_num

end FormalResearch.FourQubitEntropy.RenyiFull

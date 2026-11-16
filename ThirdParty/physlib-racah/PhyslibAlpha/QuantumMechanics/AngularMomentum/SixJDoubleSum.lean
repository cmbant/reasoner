/-
Copyright (c) 2026 Antony Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antony Lewis
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.RacahDoubleSumCollapse
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJCollapseConst
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJProjection
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SixJWeightRule

/-!

# The 6j symbol as a constant times Racah's single sum

The operator-defined 6j symbol `sixJ` is an explicit constant times Racah's double sum
`collapseSum`, and hence times the single sum `Xs`.

## i. Overview

This is the operator half of the proof of Racah's closed formula, composed with the combinatorial
half. For `0 < a`, `0 < c` and admissible `k₁`, `k₃`, `K` (`ValidA`, `ValidB`), the projection
identity `sum_cgCoefficient_mul_eq_recoupling` at `μ = 0`, `γ = K - k₁` expresses the recoupling
coefficient `⟨(j₁ j₂) j₁₂, j₃; J J | j₁, (j₂ j₃) j₂₃; J J⟩` times the top-weight coefficient
`⟨j₁₂ 0 j₃ k₂ | J J⟩` as a triple sum of Clebsch–Gordan coefficients. The weight rule
(`sum_three_cg_eq`) reduces it to a single sum of the products `collapseConst * collapseTerm`
(`cg_three_eq`), which is `collapseConst * collapseSum` (`collapseSum_eq_sum_collapseTerm`).
Dividing by the top-weight coefficient and by `√((2 j₁₂ + 1)(2 j₂₃ + 1))`, the definition of
`sixJ` gives `sixJ = Cconst * collapseSum` (`collapseConst_div`, `Cconst_eq`). Finally
`collapseSum_eq_Xs_of_valid` replaces the double sum by `Xs`.

The cases `a = 0` and `c = 0` are not covered, as in `sixJ_eq_sixJSym`.

## ii. Key results

- `sixJ_eq_const_mul_collapseSum`: `sixJ = Cconst * collapseSum`.
- `sixJ_eq_const_mul_Xs`: `sixJ = Cconst * Xs * X! / ((c-K+k₁)! k₃! (b-k₃)! (c-k₃)!)`, with
  `X = b + c - k₃ - K`.

## iii. Table of contents

- A. The double sum
- B. The single sum

## iv. References

- G. Racah, *Theory of complex spectra. II*, Phys. Rev. 62, 438 (1942).

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

/-!

## A. The double sum

-/

/-- **The 6j symbol of `SixJ` as a double sum.** For `0 < a`, `0 < c` and admissible `k₁`, `k₃`,
`K` (`ValidA`, `ValidB`; `k₁ ≤ min a b`, `k₃ ≤ min b c` are the `Fin` bounds),
`{j₁ j₂ j₁₂; j₃ J j₂₃} = Cconst · collapseSum`. The cases `a = 0` and `c = 0` are not covered
(`sixJ_eq_sixJSym` has the same hypotheses). -/
lemma sixJ_eq_const_mul_collapseSum {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ = Cconst a b c K k₁ k₃ * collapseSum a b c K k₁ k₃ := by
  have hk₁ := k₁.isLt
  have hk₃ := k₃.isLt
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hproj := sum_cgCoefficient_mul_eq_recoupling hab hbc ha hc ⟨hA1, hA2, hA3⟩
    ⟨hB1, hB2, hB3⟩ 0 (K - k₁)
  rw [sum_three_cg_eq ha hab (by omega) (by omega) hB2 hB3,
    Finset.sum_congr rfl fun α hα => cg_three_eq ha (by omega) (by omega) (by omega) (by omega)
      hA1 hA3 hB1 hB2 hB3 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hα)),
    ← Finset.mul_sum,
    ← collapseSum_eq_sum_collapseTerm (by omega) (by omega) (by omega) hA1 hB1 hB3] at hproj
  have hpos := cgCoefficient_top_pos (m := a + b - 2 * (k₁ : ℕ)) (n := c) (k := K - k₁) hA2 hA3
  have hR : recoupling hab hbc K 0 k₁ k₃ = collapseConst a b c K k₁ k₃ *
      collapseSum a b c K k₁ k₃ / cgCoefficient (a + b - 2 * (k₁ : ℕ)) c (K - k₁) 0 0 (K - k₁) := by
    rw [eq_div_iff hpos.ne']
    exact hproj.symm
  have hE : 0 < Real.sqrt (((a + b - 2 * (k₁ : ℕ) + 1 : ℕ) : ℝ) *
      ((b + c - 2 * (k₃ : ℕ) + 1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  rw [sixJ, ite_eq_left ⟨⟨hA1, hA2, hA3⟩, ⟨hB1, hB2, hB3⟩⟩, hR,
    Cconst_eq (by omega) (by omega) (by omega) (by omega) hA1 hA2 hA3 hB1 hB2 hB3,
    ← collapseConst_div hA2 hA3 (by omega) (by omega) (by omega) (by omega) hA1 hB1 hB2 hB3]
  field_simp

/-!

## B. The single sum

-/

/-- `sixJ` is the constant `Cconst` times the single sum `Xs`, up to explicit factorials. -/
lemma sixJ_eq_const_mul_Xs {a b c : ℕ} (hab : 0 < a + b) (hbc : 0 < b + c)
    (ha : 0 < a) (hc : 0 < c) {K : ℕ} {k₁ : Fin (min a b + 1)} {k₃ : Fin (min b c + 1)}
    (hA : ValidA a b c K k₁) (hB : ValidB a b c K k₃) :
    sixJ hab hbc K k₁ k₃ = Cconst a b c K k₁ k₃ *
      (Xs a b c K k₁ k₃ * factZ ((b : ℤ) + c - k₃ - K) /
        (factZ ((c : ℤ) - K + k₁) * factZ k₃ * factZ ((b : ℤ) - k₃) * factZ ((c : ℤ) - k₃))) := by
  rw [sixJ_eq_const_mul_collapseSum hab hbc ha hc hA hB]
  congr 1
  exact collapseSum_eq_Xs_of_valid k₁.isLt k₃.isLt hA hB

end PhyslibAlpha.Sl2

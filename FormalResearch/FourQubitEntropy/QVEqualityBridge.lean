module

public import FormalResearch.FourQubitEntropy.QVEqualityCore
public import FormalResearch.FourQubitEntropy.PaperETwoFlatTF
public import FormalResearch.FourQubitEntropy.PaperEGapTwoFlatQF

/-!
# The critical bridge: cut spectra of a critical unit state in `(m, n)` coordinates

Paper E, proof of `prop:fqe-critical-variance` (`renyi_compatibility.tex`): at `P = 1` the Bloch correlation
matrix is `Θ = m nᵀ` with unit `m, n ∈ ℝ³` and the cut spectra are `(1 + σ · g^c)/4`.  Here the same
structure is obtained in the magic-basis coordinates of the normal form `G(v)`, `v = a + i b`, `Σ v_k² = 0`:
with the Plücker coordinates `ω = a ∧ b`, the self-dual and anti-self-dual parts `m, n` (`mOf`, `nOf`) are
unit vectors and the three cut spectra `|v|²`, `|H₊ v|²`, `|H₋ v|²` are `spc0, spc1, spc2` of `(m, n)`
(`QVEqualityCore.lean`).  The nine identities `g^c_a = ± m_i n_j` are polynomial identities modulo
`Σ a² = Σ b² = 1/2`, `Σ a b = 0`, with explicit cofactors (found by linear algebra over `ℚ`, checked here
by `linear_combination`).
-/

@[expose] public section


set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-- Real Hadamard-type matrix `H₊` (`wp`) on `ℝ⁴`, in the order `(00, 01, 10, 11)`. -/
noncomputable def Hp (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(u 0 - u 1 + u 2 - u 3) / 2, (-u 0 + u 1 + u 2 - u 3) / 2, (u 0 + u 1 + u 2 + u 3) / 2,
    (-u 0 - u 1 + u 2 + u 3) / 2]

/-- Real Hadamard-type matrix `H₋` (`wm`). -/
noncomputable def Hm (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(u 0 - u 1 - u 2 - u 3) / 2, (-u 0 + u 1 - u 2 - u 3) / 2, (-u 0 - u 1 + u 2 - u 3) / 2,
    (-u 0 - u 1 - u 2 + u 3) / 2]

/-- Self-dual part `m` of the bivector `ω = a ∧ b` (normalised so that `|m| = 1` when
`|a|² = |b|² = 1/2`, `a ⊥ b`). -/
noncomputable def mOf (a b : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![2 * ((a 0 * b 1 - a 1 * b 0) + (a 2 * b 3 - a 3 * b 2)),
    2 * ((a 0 * b 2 - a 2 * b 0) - (a 1 * b 3 - a 3 * b 1)),
    2 * ((a 0 * b 3 - a 3 * b 0) + (a 1 * b 2 - a 2 * b 1))]

/-- Anti-self-dual part `n` of `ω = a ∧ b`. -/
noncomputable def nOf (a b : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![2 * ((a 0 * b 1 - a 1 * b 0) - (a 2 * b 3 - a 3 * b 2)),
    2 * ((a 0 * b 2 - a 2 * b 0) + (a 1 * b 3 - a 3 * b 1)),
    2 * ((a 0 * b 3 - a 3 * b 0) - (a 1 * b 2 - a 2 * b 1))]

section Real

variable (a b : Fin 4 → ℝ)
  (hA : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 = 1 / 2)
  (hB : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1 / 2)
  (hC : a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 = 0)

include hA hB hC in
theorem mOf_unit : mOf a b 0 ^ 2 + mOf a b 1 ^ 2 + mOf a b 2 ^ 2 = 1 := by
  simp only [mOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination 4 * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) * hA + 2 * hB
    - 4 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3) * hC

include hA hB hC in
theorem nOf_unit : nOf a b 0 ^ 2 + nOf a b 1 ^ 2 + nOf a b 2 ^ 2 = 1 := by
  simp only [nOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination 4 * (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) * hA + 2 * hB
    - 4 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3) * hC

include hA hB hC in
theorem bridge_cut0 (k : Fin 4) : a k ^ 2 + b k ^ 2 = spc0 (mOf a b) (nOf a b) k := by
  fin_cases k
  · simp only [spc0, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-(b 0)^2 + (b 1)^2 + (b 2)^2 + (b 3)^2) * hA + (1/2 - 2*(a 0)^2) * hB + (3*a 0*b 0 - a 1*b 1 - a 2*b 2 - a 3*b 3) * hC
  · simp only [spc0, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination ((b 0)^2 - (b 1)^2 + (b 2)^2 + (b 3)^2) * hA + (1/2 - 2*(a 1)^2) * hB + (-a 0*b 0 + 3*a 1*b 1 - a 2*b 2 - a 3*b 3) * hC
  · simp only [spc0, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination ((b 0)^2 + (b 1)^2 - (b 2)^2 + (b 3)^2) * hA + (1/2 - 2*(a 2)^2) * hB + (-a 0*b 0 - a 1*b 1 + 3*a 2*b 2 - a 3*b 3) * hC
  · simp only [spc0, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-(b 0)^2 - (b 1)^2 - (b 2)^2 - 3*(b 3)^2 + 1) * hA + (2*(a 0)^2 + 2*(a 1)^2 + 2*(a 2)^2 - 1/2) * hB + (-a 0*b 0 - a 1*b 1 - a 2*b 2 + 3*a 3*b 3) * hC

include hA hB hC in
theorem bridge_cut1 (k : Fin 4) : Hp a k ^ 2 + Hp b k ^ 2 = spc1 (mOf a b) (nOf a b) k := by
  fin_cases k
  · simp only [spc1, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (b 0*b 1 - b 0*b 2 + b 0*b 3 + b 1*b 2 - b 1*b 3 + b 2*b 3 + 1/4) * hA + (a 0*a 1 - a 0*a 2 + a 0*a 3 + a 1*a 2 - a 1*a 3 + a 2*a 3 + 1/4) * hB + (-a 0*b 1 + a 0*b 2 - a 0*b 3 - a 1*b 0 - a 1*b 2 + a 1*b 3 + a 2*b 0 - a 2*b 1 - a 2*b 3 - a 3*b 0 + a 3*b 1 - a 3*b 2) * hC
  · simp only [spc1, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (b 0*b 1 + b 0*b 2 - b 0*b 3 - b 1*b 2 + b 1*b 3 + b 2*b 3 + 1/4) * hA + (a 0*a 1 + a 0*a 2 - a 0*a 3 - a 1*a 2 + a 1*a 3 + a 2*a 3 + 1/4) * hB + (-a 0*b 1 - a 0*b 2 + a 0*b 3 - a 1*b 0 + a 1*b 2 - a 1*b 3 - a 2*b 0 + a 2*b 1 - a 2*b 3 + a 3*b 0 - a 3*b 1 - a 3*b 2) * hC
  · simp only [spc1, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-b 0*b 1 - b 0*b 2 - b 0*b 3 - b 1*b 2 - b 1*b 3 - b 2*b 3 + 1/4) * hA + (-a 0*a 1 - a 0*a 2 - a 0*a 3 - a 1*a 2 - a 1*a 3 - a 2*a 3 + 1/4) * hB + (a 0*b 1 + a 0*b 2 + a 0*b 3 + a 1*b 0 + a 1*b 2 + a 1*b 3 + a 2*b 0 + a 2*b 1 + a 2*b 3 + a 3*b 0 + a 3*b 1 + a 3*b 2) * hC
  · simp only [spc1, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-b 0*b 1 + b 0*b 2 + b 0*b 3 + b 1*b 2 + b 1*b 3 - b 2*b 3 + 1/4) * hA + (-a 0*a 1 + a 0*a 2 + a 0*a 3 + a 1*a 2 + a 1*a 3 - a 2*a 3 + 1/4) * hB + (a 0*b 1 - a 0*b 2 - a 0*b 3 + a 1*b 0 - a 1*b 2 - a 1*b 3 - a 2*b 0 - a 2*b 1 + a 2*b 3 - a 3*b 0 - a 3*b 1 + a 3*b 2) * hC

include hA hB hC in
theorem bridge_cut2 (k : Fin 4) : Hm a k ^ 2 + Hm b k ^ 2 = spc2 (mOf a b) (nOf a b) k := by
  fin_cases k
  · simp only [spc2, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (b 0*b 1 + b 0*b 2 + b 0*b 3 - b 1*b 2 - b 1*b 3 - b 2*b 3 + 1/4) * hA + (a 0*a 1 + a 0*a 2 + a 0*a 3 - a 1*a 2 - a 1*a 3 - a 2*a 3 + 1/4) * hB + (-a 0*b 1 - a 0*b 2 - a 0*b 3 - a 1*b 0 + a 1*b 2 + a 1*b 3 - a 2*b 0 + a 2*b 1 + a 2*b 3 - a 3*b 0 + a 3*b 1 + a 3*b 2) * hC
  · simp only [spc2, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (b 0*b 1 - b 0*b 2 - b 0*b 3 + b 1*b 2 + b 1*b 3 - b 2*b 3 + 1/4) * hA + (a 0*a 1 - a 0*a 2 - a 0*a 3 + a 1*a 2 + a 1*a 3 - a 2*a 3 + 1/4) * hB + (-a 0*b 1 + a 0*b 2 + a 0*b 3 - a 1*b 0 - a 1*b 2 - a 1*b 3 + a 2*b 0 - a 2*b 1 + a 2*b 3 + a 3*b 0 - a 3*b 1 + a 3*b 2) * hC
  · simp only [spc2, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-b 0*b 1 + b 0*b 2 - b 0*b 3 + b 1*b 2 - b 1*b 3 + b 2*b 3 + 1/4) * hA + (-a 0*a 1 + a 0*a 2 - a 0*a 3 + a 1*a 2 - a 1*a 3 + a 2*a 3 + 1/4) * hB + (a 0*b 1 - a 0*b 2 + a 0*b 3 + a 1*b 0 - a 1*b 2 + a 1*b 3 - a 2*b 0 - a 2*b 1 - a 2*b 3 + a 3*b 0 + a 3*b 1 - a 3*b 2) * hC
  · simp only [spc2, specG, mOf, nOf, Hp, Hm, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (-b 0*b 1 - b 0*b 2 + b 0*b 3 - b 1*b 2 + b 1*b 3 + b 2*b 3 + 1/4) * hA + (-a 0*a 1 - a 0*a 2 + a 0*a 3 - a 1*a 2 + a 1*a 3 + a 2*a 3 + 1/4) * hB + (a 0*b 1 + a 0*b 2 - a 0*b 3 + a 1*b 0 + a 1*b 2 - a 1*b 3 + a 2*b 0 + a 2*b 1 - a 2*b 3 - a 3*b 0 - a 3*b 1 - a 3*b 2) * hC

end Real

end FormalResearch.FourQubitEntropy.QVEquality

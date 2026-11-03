module

public import Mathlib

/-!
# GO certificate: the analytic remainders `R_sq` and `R_ax`

The 19 normal-slice coordinates are `x 0 .. x 18 = t, u₁ u₂ u₃, a₁ a₂ a₃, e₁₂ e₁₃ e₂₃, b₁₂ b₁₃ b₂₃, p₁ p₂ p₃, q₁ q₂ q₃`
(the variable order of `orbit_certificate_polynomials.py`).  `Xm`, `Ym` are the matrices `Z = √3 X + i Y` of
`global_overlap_certificate.tex` (the slice parametrisation), `nn = 3‖X‖² + ‖Y‖²`, `h0 = 6t + a₁ + a₂ + a₃`,
and

* `Rsq = γ/27 · nn · h0² · J` with `γ = 10⁻⁷` and `J` the sum of squares of the paper;
* `Rax = ω/216 · nn · h0 · zᵀ L* z` with `z = (b₂₃, −b₁₃, b₁₂)`, `ω = 794424/10¹²` and `L* = L_{-1,-1,-1/2,1/2}`.

`Rsq_nonneg` is unconditional; `Rax_nonneg` needs `h0 ≥ 0` and `L* ⪰ 0` (one of the constraint matrices, up to the
factor `h0/216`).  Invariance of the remainders is not needed: the checker `check` verifies the identity for the
symmetrised polynomial directly.  Claim class: proved.
-/

@[expose] public section


open Finset

namespace FormalResearch.FourQubitEntropy.GOProbe

/-- Index of the pair `(j, k)`, `1 ≤ j < k ≤ 3`, among `(1,2), (1,3), (2,3)`. -/
def pidx (j k : ℕ) : ℕ := if j = 1 ∧ k = 2 then 0 else if j = 1 ∧ k = 3 then 1 else 2

/-- `X` of `Z = √3 X + i Y`. -/
noncomputable def Xm (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then (if j = 0 then x 0 else x (12 + j))
  else if j = 0 then x (15 + i) / 3
  else if i = j then x i
  else if i < j then x (7 + pidx i j) + x (10 + pidx i j)
  else x (7 + pidx j i) - x (10 + pidx j i)

/-- `Y` of `Z = √3 X + i Y`. -/
noncomputable def Ym (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then (if j = 0 then x 1 + x 2 + x 3 else x (15 + j))
  else if j = 0 then 3 * x (12 + i)
  else if i = j then x 0 + x (3 + i)
  else if i < j then -x (7 + pidx i j) / 2
  else -x (7 + pidx j i) / 2

/-- `n = 3‖X‖² + ‖Y‖²`. -/
noncomputable def nn (x : ℕ → ℝ) : ℝ :=
  3 * ∑ i ∈ range 4, ∑ j ∈ range 4, Xm x i j ^ 2 + ∑ i ∈ range 4, ∑ j ∈ range 4, Ym x i j ^ 2

noncomputable def h0 (x : ℕ → ℝ) : ℝ := 6 * x 0 + x 4 + x 5 + x 6

/-- `J = 5[∑ (p_j² + q_j²) + ∑_{j<k} (e_jk² + b_jk²)] + 2 ∑_{j<k} [(u_j − u_k)² + (a_j − a_k)²]`. -/
noncomputable def Jsq (x : ℕ → ℝ) : ℝ :=
  5 * (∑ j ∈ range 3, (x (13 + j) ^ 2 + x (16 + j) ^ 2) + ∑ k ∈ range 3, (x (7 + k) ^ 2 + x (10 + k) ^ 2))
    + 2 * ((x 1 - x 2) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + (x 4 - x 5) ^ 2 + (x 4 - x 6) ^ 2 + (x 5 - x 6) ^ 2)

noncomputable def Rsq (x : ℕ → ℝ) : ℝ := (1 / 10 ^ 7 : ℝ) / 27 * nn x * h0 x ^ 2 * Jsq x

theorem nn_nonneg (x : ℕ → ℝ) : 0 ≤ nn x := by
  unfold nn
  have h1 : 0 ≤ ∑ i ∈ range 4, ∑ j ∈ range 4, Xm x i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i ∈ range 4, ∑ j ∈ range 4, Ym x i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

theorem Jsq_nonneg (x : ℕ → ℝ) : 0 ≤ Jsq x := by
  unfold Jsq
  have h1 : 0 ≤ ∑ j ∈ range 3, (x (13 + j) ^ 2 + x (16 + j) ^ 2) :=
    Finset.sum_nonneg fun j _ => by positivity
  have h2 : 0 ≤ ∑ k ∈ range 3, (x (7 + k) ^ 2 + x (10 + k) ^ 2) :=
    Finset.sum_nonneg fun j _ => by positivity
  nlinarith [sq_nonneg (x 1 - x 2), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3), sq_nonneg (x 4 - x 5),
    sq_nonneg (x 4 - x 6), sq_nonneg (x 5 - x 6)]

theorem Rsq_nonneg (x : ℕ → ℝ) : 0 ≤ Rsq x := by
  unfold Rsq
  have := nn_nonneg x
  have := Jsq_nonneg x
  positivity

/-- `L* = L_{-1,-1,-1/2,1/2}` restricted to the lower indices (entries `(i, j)`, `i, j ∈ {0,1,2}` stand for
`i + 1, j + 1`). -/
noncomputable def Lstar (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  let c : ℝ := -1 / 2
  let s : ℝ := 1 / 2
  let σ : ℝ := -1
  let r0 := σ * Ym x 0 0 + σ * (Ym x 1 1 + Ym x 2 2 + Ym x 3 3)
  let i0 := -σ * Xm x 0 0 - σ * (Xm x 1 1 + Xm x 2 2 + Xm x 3 3)
  let xx := (Xm x (i + 1) (j + 1) + Xm x (j + 1) (i + 1)) / 2
  let yy := Ym x (i + 1) (j + 1)
  (if i = j then h0 x - c * r0 - 3 * s * i0 else 0) - c * (3 * xx - σ * yy) - 3 * s * (yy + σ * xx)

/-- The axial vector `z = (b₂₃, −b₁₃, b₁₂)`. -/
noncomputable def zax (x : ℕ → ℝ) : ℕ → ℝ := fun i => if i = 0 then x 12 else if i = 1 then -x 11 else x 10

noncomputable def Rax (x : ℕ → ℝ) : ℝ :=
  (794424 / 10 ^ 12 : ℝ) / 216 * nn x * h0 x * ∑ i ∈ range 3, ∑ j ∈ range 3, zax x i * Lstar x i j * zax x j

theorem Rax_nonneg (x : ℕ → ℝ) (hh : 0 ≤ h0 x)
    (hL : ∀ v : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, v i * Lstar x i j * v j) : 0 ≤ Rax x := by
  unfold Rax
  have := nn_nonneg x
  have := hL (zax x)
  positivity

end FormalResearch.FourQubitEntropy.GOProbe

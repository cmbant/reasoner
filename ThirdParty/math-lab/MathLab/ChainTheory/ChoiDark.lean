module

/-
ChoiDark.lean

The (3,3) pair type is dark: a positive map on M₃(ℂ) that is not decomposable.

The alpha Letter of Chain Theory calls a type (d₁, d₂) readable when every positive map between the
operator algebras of its ends is decomposable (a completely positive map plus a completely positive
map composed with the transpose), and dark otherwise. Its Lean file carries the "read cap"
(readable ⇔ d₁ d₂ ≤ 6) as a named hypothesis citing Størmer, Woronowicz and Choi. This file proves
the (3,3) instance of the dark direction from scratch, with Choi's map:

  Part 1  Choi's inequality in real form, via the cyclic AM-GM inequality and a weighted Lagrange
          identity.
  Part 2  The Choi map Φ(X)_ii = X_ii + X_{i+1,i+1}, Φ(X)_ij = -X_ij is positive: it takes every
          positive semidefinite matrix Bᴴ B to a positive semidefinite one.
  Part 3  A PPT state ρ on ℂ³ ⊗ ℂ³ (the Horodecki family at a = 7/2), written as a nonnegative sum
          of rational rank-one terms, and its partial transpose as another; checked by the kernel.
  Part 4  The witness tr(ρ C_Φ) is ≥ 0 on every map X ↦ K X Kᴴ and every map X ↦ L Xᵀ Lᴴ, but equals
          -1/14 on the Choi map. Hence the Choi map is not decomposable.
  Part 5  Corollaries: the (3,3) type is dark; ρ is PPT and entangled.
  Part 6  Every type with both ends of dimension at least three is dark: the Choi map extends to a
          positive, non-decomposable map M_{d₁} → M_{d₂} for all d₁, d₂ ≥ 3.
  Part 7  The (2,4) type is dark: an integer-coefficient positive map M₂ → M₄, certified positive by
          a sum-of-squares identity with multiplier ‖v‖², and non-decomposable by the PPT state of
          P. Horodecki's 2 ⊗ 4 family at b = 3/5 (witness value -1).
  Part 8  The dark direction of the read cap: if every positive map between the ends of a type
          (d₁, d₂) with d₁, d₂ ≥ 2 is decomposable, then d₁ d₂ ≤ 6 (`readable_imp_le_six`).

Definitions (Part 0): positive maps, decomposable maps and readability. `Readable` quantifies over
ℂ-linear maps, and `IsPositive` asks that `w† Φ(Bᴴ B) w` be real and nonnegative, i.e. that `Φ` take
positive semidefinite matrices to positive semidefinite ones.

Revision, 26 Oct 2026: the version published on 25-26 Oct (public commit 3b95151) quantified over all
functions and asked only for a nonnegative real part. With those definitions no type is readable (a
nonlinear map vanishing on positive matrices, or the linear map X ↦ (1 + i) X, is "positive" but not
decomposable), so `readable_imp_le_six` held vacuously. The explicit maps and their theorems were
unaffected; the statements of `dark_33`, `dark_of_three_le` and `readable_imp_le_six` now carry content.

Mathematical status: the existence statements are classical (Choi, Linear Algebra Appl. 12, 95 (1975);
Woronowicz, Rep. Math. Phys. 10, 165 (1976); P. Horodecki, Phys. Lett. A 232, 333 (1997); Horodecki,
Horodecki and Horodecki, PRL 80, 5239 (1998)). The explicit (2,4) map and its certificate are our own,
found by semidefinite programming and rationalized exactly. New here is the formal check.
Not formalized: the readable direction d₁ d₂ ≤ 6 (Størmer 1963, Woronowicz 1976).

Check: from a Lake project with Mathlib v4.26.0 built, `lake env lean ChoiDark.lean`.
-/
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix

namespace ChoiDark

/-! ## Part 0. Definitions -/

/-- A map `M_n(ℂ) → M_m(ℂ)` is positive: it takes every positive semidefinite `Bᴴ B` to a positive
semidefinite matrix, i.e. every `w† Φ(Bᴴ B) w` is real and nonnegative. -/
def IsPositive {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ (r : ℕ) (B : Matrix (Fin r) (Fin n) ℂ) (w : Fin m → ℂ),
    0 ≤ (star w ⬝ᵥ (Φ (Bᴴ * B) *ᵥ w)).re ∧ (star w ⬝ᵥ (Φ (Bᴴ * B) *ᵥ w)).im = 0

/-- A map is decomposable: a completely positive map plus a completely positive map composed with the
transpose, both in Kraus form. -/
def IsDecomposable {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (p q : ℕ) (K : Fin p → Matrix (Fin m) (Fin n) ℂ) (L : Fin q → Matrix (Fin m) (Fin n) ℂ),
    ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ

/-- The Letter's readability of a type `(d₁, d₂)`: every positive linear map between the operator
algebras of its two ends, in either direction, is decomposable. -/
def Readable (d₁ d₂ : ℕ) : Prop :=
  (∀ Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ, IsPositive Φ → IsDecomposable Φ) ∧
  (∀ Ψ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] Matrix (Fin d₁) (Fin d₁) ℂ, IsPositive Ψ → IsDecomposable Ψ)

/-! ## Part 1. Choi's inequality in real form -/

theorem cyclic_amgm {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ x ^ 2 * z + x * y ^ 2 + y * z ^ 2 - 3 * x * y * z := by
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total z x with hzx | hzx <;>
    nlinarith [mul_nonneg hz (sq_nonneg (x - y)), mul_nonneg hx (sq_nonneg (y - z)),
      mul_nonneg hy (sq_nonneg (z - x)), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx,
      mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hyz), mul_nonneg (sub_nonneg.2 hyz) (sub_nonneg.2 hzx),
      mul_nonneg (sub_nonneg.2 hzx) (sub_nonneg.2 hxy)]

/-- The identity behind Choi's inequality (a weighted Lagrange identity). -/
theorem choi_key (a0 a1 a2 b0 b1 b2 : ℝ) :
    ((2 * b0 ^ 2 + b1 ^ 2) * (2 * b1 ^ 2 + b2 ^ 2) * (2 * b2 ^ 2 + b0 ^ 2)) *
      (((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        - (a0 * b0 + a1 * b1 + a2 * b2) ^ 2)
    = ((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        * ((b0 ^ 2) ^ 2 * b2 ^ 2 + b0 ^ 2 * (b1 ^ 2) ^ 2 + b1 ^ 2 * (b2 ^ 2) ^ 2 - 3 * b0 ^ 2 * b1 ^ 2 * b2 ^ 2)
      + (2 * b2 ^ 2 + b0 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b1 - (2 * b1 ^ 2 + b2 ^ 2) * a1 * b0) ^ 2
      + (2 * b1 ^ 2 + b2 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b0) ^ 2
      + (2 * b0 ^ 2 + b1 ^ 2) * ((2 * b1 ^ 2 + b2 ^ 2) * a1 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b1) ^ 2 := by
  ring

theorem sq_zero_of_two_sq_add_sq {x y : ℝ} (h : 2 * x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 hx, pow_eq_zero_iff (two_ne_zero) |>.1 hy⟩

/-- **Choi's inequality**, real form: with `d_i = 2 b_i² + b_{i+1}²`, `(∑ a_i b_i)² ≤ ∑ d_i a_i²`. -/
theorem choi_real (a0 a1 a2 b0 b1 b2 : ℝ) :
    (a0 * b0 + a1 * b1 + a2 * b2) ^ 2 ≤
      (2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2 := by
  have hP := cyclic_amgm (sq_nonneg b0) (sq_nonneg b1) (sq_nonneg b2)
  have hprod : 0 ≤ (2 * b0 ^ 2 + b1 ^ 2) * (2 * b1 ^ 2 + b2 ^ 2) * (2 * b2 ^ 2 + b0 ^ 2) := by positivity
  rcases hprod.lt_or_eq with hpos | hzero
  · have hR := choi_key a0 a1 a2 b0 b1 b2
    have hS : 0 ≤ (2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2
        + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2 := by positivity
    have hrhs : 0 ≤ ((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        * ((b0 ^ 2) ^ 2 * b2 ^ 2 + b0 ^ 2 * (b1 ^ 2) ^ 2 + b1 ^ 2 * (b2 ^ 2) ^ 2 - 3 * b0 ^ 2 * b1 ^ 2 * b2 ^ 2)
      + (2 * b2 ^ 2 + b0 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b1 - (2 * b1 ^ 2 + b2 ^ 2) * a1 * b0) ^ 2
      + (2 * b1 ^ 2 + b2 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b0) ^ 2
      + (2 * b0 ^ 2 + b1 ^ 2) * ((2 * b1 ^ 2 + b2 ^ 2) * a1 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b1) ^ 2 := by
      have := mul_nonneg hS hP
      positivity
    rw [← hR] at hrhs
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_right (by linarith) hpos)
  · rcases mul_eq_zero.1 hzero.symm with h | h
    · rcases mul_eq_zero.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
        nlinarith [sq_nonneg (a1 * b2), sq_nonneg (a2 * b2)]
      · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
        nlinarith [sq_nonneg (a0 * b0), sq_nonneg (a2 * b0)]
    · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
      nlinarith [sq_nonneg (a0 * b1), sq_nonneg (a1 * b1)]


/-! ## Part 2. The Choi map is positive -/

def nxt : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The Choi map on `M₃(ℂ)`: diagonal `X i i + X (i+1) (i+1)`, off-diagonal `-X i j`. -/
def choiMap (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then X i i + X (nxt i) (nxt i) else -X i j

theorem choi_form_eq (v w : Fin 3 → ℂ) :
    star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)
      = (2 * (star (v 0) * v 0) + star (v 1) * v 1) * (star (w 0) * w 0)
        + (2 * (star (v 1) * v 1) + star (v 2) * v 2) * (star (w 1) * w 1)
        + (2 * (star (v 2) * v 2) + star (v 0) * v 0) * (star (w 2) * w 2)
        - (star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2)
          * star (star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2) := by
  simp only [dotProduct, mulVec, choiMap, vecMulVec_apply, Fin.sum_univ_three, Pi.star_apply, nxt,
    star_add, star_mul', star_star]
  simp
  ring

theorem normSq_sum3_le (z0 z1 z2 : ℂ) :
    Complex.normSq (z0 + z1 + z2) ≤ (‖z0‖ + ‖z1‖ + ‖z2‖) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h : ‖z0 + z1 + z2‖ ≤ ‖z0‖ + ‖z1‖ + ‖z2‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem star_mul_self_eq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-- **The Choi map is positive** (on rank-one inputs; Part 3 extends to every PSD input):
`w† Φ(v v†) w` is real and nonnegative. -/
theorem choi_positive (v w : Fin 3 → ℂ) :
    0 ≤ (star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)).re ∧
      (star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)).im = 0 := by
  set T := star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2 with hT
  have hTT : T * star T = (Complex.normSq T : ℂ) := Complex.mul_conj T
  have hE : star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)
      = (((2 * Complex.normSq (v 0) + Complex.normSq (v 1)) * Complex.normSq (w 0)
        + (2 * Complex.normSq (v 1) + Complex.normSq (v 2)) * Complex.normSq (w 1)
        + (2 * Complex.normSq (v 2) + Complex.normSq (v 0)) * Complex.normSq (w 2)
        - Complex.normSq T : ℝ) : ℂ) := by
    rw [choi_form_eq, ← hT, hTT]
    simp only [star_mul_self_eq]
    push_cast
    ring
  rw [hE, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hT2 : Complex.normSq T ≤ (‖w 0‖ * ‖v 0‖ + ‖w 1‖ * ‖v 1‖ + ‖w 2‖ * ‖v 2‖) ^ 2 := by
    have := normSq_sum3_le (star (w 0) * v 0) (star (w 1) * v 1) (star (w 2) * v 2)
    rw [hT]
    simpa [norm_mul, norm_star] using this
  have hc := choi_real ‖w 0‖ ‖w 1‖ ‖w 2‖ ‖v 0‖ ‖v 1‖ ‖v 2‖
  simp only [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq] at hT2
  nlinarith [hT2, hc]


/-! ## Part 3. The PPT state

The PPT state rho_{7/2} of the Horodecki family, as an explicit nonnegative sum of rank-one
terms over ℚ, and its partial transpose as another. Index `(i, a)`: first factor `i`, second `a`. -/


def basisQ (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 → ℚ := fun x => if x = p then 1 else 0

/-- The seven rank-one terms of rho: `Σ|ii⟩` with weight 2/21, `|i, i+1⟩` with 1/6, `|i+1, i⟩` with 1/14. -/
def rhoVec : Fin 7 → Fin 3 × Fin 3 → ℚ := ![
  fun x => if x.1 = x.2 then 1 else 0,
  basisQ (0, 1), basisQ (1, 2), basisQ (2, 0),
  basisQ (1, 0), basisQ (2, 1), basisQ (0, 2)]
def rhoWt : Fin 7 → ℚ := ![2/21, 1/6, 1/6, 1/6, 1/14, 1/14, 1/14]

def rhoQ (x y : Fin 3 × Fin 3) : ℚ := ∑ k, rhoWt k * rhoVec k x * rhoVec k y

/-- The nine rank-one terms of the partial transpose: `|ii⟩` with 2/21,
`|i+1, i⟩ + (4/3)|i, i+1⟩` with 1/14, and `|i, i+1⟩` with 5/126. -/
def ptVec : Fin 9 → Fin 3 × Fin 3 → ℚ := ![
  basisQ (0, 0), basisQ (1, 1), basisQ (2, 2),
  fun x => basisQ (1, 0) x + 4/3 * basisQ (0, 1) x,
  fun x => basisQ (2, 1) x + 4/3 * basisQ (1, 2) x,
  fun x => basisQ (0, 2) x + 4/3 * basisQ (2, 0) x,
  basisQ (0, 1), basisQ (1, 2), basisQ (2, 0)]
def ptWt : Fin 9 → ℚ := ![2/21, 2/21, 2/21, 1/14, 1/14, 1/14, 5/126, 5/126, 5/126]

/-- The partial transpose on the second factor, `ρ^Γ((j,a),(i,b)) = ρ((j,b),(i,a))`, equals the
nonnegative sum `ptQ`. -/
theorem rho_partialTranspose :
    ∀ j a i b : Fin 3, rhoQ (j, b) (i, a) = ∑ k, ptWt k * ptVec k (j, a) * ptVec k (i, b) := by
  decide +kernel

theorem rho_trace : ∑ x, rhoQ x x = 1 := by decide +kernel



/-- The entries of `ρ` as an explicit table. -/
def rhoE (x y : Fin 3 × Fin 3) : ℚ :=
  (if x.1 = x.2 ∧ y.1 = y.2 then 2 / 21 else 0) +
  (if x = y ∧ (x = (0, 1) ∨ x = (1, 2) ∨ x = (2, 0)) then 1 / 6 else 0) +
  (if x = y ∧ (x = (1, 0) ∨ x = (2, 1) ∨ x = (0, 2)) then 1 / 14 else 0)

theorem rhoQ_eq_rhoE : ∀ x y, rhoQ x y = rhoE x y := by decide +kernel

/-- The same table in `ℂ`. -/
noncomputable def rhoC (x y : Fin 3 × Fin 3) : ℂ :=
  (if x.1 = x.2 ∧ y.1 = y.2 then 2 / 21 else 0) +
  (if x = y ∧ (x = (0, 1) ∨ x = (1, 2) ∨ x = (2, 0)) then 1 / 6 else 0) +
  (if x = y ∧ (x = (1, 0) ∨ x = (2, 1) ∨ x = (0, 2)) then 1 / 14 else 0)

theorem rhoQ_cast (x y : Fin 3 × Fin 3) : (rhoQ x y : ℂ) = rhoC x y := by
  rw [rhoQ_eq_rhoE]; unfold rhoE rhoC; split_ifs <;> norm_num

/-! ## Part 4. The witness and non-decomposability -/

set_option maxHeartbeats 4000000

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The matrix unit `E i j`. -/
def E (i j : Fin 3) : M3 := fun r c => if r = i ∧ c = j then 1 else 0

/-- The witness functional of `ρ` on a linear map `Φ` of `M₃`: `tr(ρ C_Φ)`, with the Choi matrix
`C_Φ = Σ E_ij ⊗ Φ(E_ij)`, entries `C_Φ((i,a),(j,b)) = Φ(E_ij)_ab`. -/
noncomputable def W (Φ : M3 → M3) : ℂ := ∑ i, ∑ j, ∑ a, ∑ b, (rhoQ (j, b) (i, a) : ℂ) * Φ (E i j) a b

theorem W_add (Φ Ψ : M3 → M3) : W (fun X => Φ X + Ψ X) = W Φ + W Ψ := by
  simp only [W, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem W_sum {ι : Type*} (s : Finset ι) (F : ι → M3 → M3) :
    W (fun X => ∑ k ∈ s, F k X) = ∑ k ∈ s, W (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [W_add (F a) (fun X => ∑ k ∈ s, F k X), ih]

theorem kEK (K : M3) (i j a b : Fin 3) : (K * E i j * Kᴴ) a b = K a i * star (K b j) := by
  simp [Matrix.mul_apply, E, Matrix.conjTranspose_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem LEtL (L : M3) (i j a b : Fin 3) : (L * (E i j)ᵀ * Lᴴ) a b = L a j * star (L b i) := by
  simp [Matrix.mul_apply, E, Matrix.conjTranspose_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

/-- On a completely positive part `X ↦ K X Kᴴ`, the witness is a nonnegative sum of squares
(one for each rank-one term of `ρ`). -/
theorem W_kraus (K : M3) :
    W (fun X => K * X * Kᴴ)
      = ((2 / 21 : ℚ) : ℂ) * ((K 0 0 + K 1 1 + K 2 2) * star (K 0 0 + K 1 1 + K 2 2))
        + ((1 / 6 : ℚ) : ℂ) * (K 1 0 * star (K 1 0) + K 2 1 * star (K 2 1) + K 0 2 * star (K 0 2))
        + ((1 / 14 : ℚ) : ℂ) * (K 0 1 * star (K 0 1) + K 1 2 * star (K 1 2) + K 2 0 * star (K 2 0)) := by
  simp only [W, kEK, rhoQ_cast, rhoC, Fin.sum_univ_three]
  simp
  ring

/-- On a part composed with the transpose, `X ↦ L Xᵀ Lᴴ`, the witness is again a nonnegative sum of
squares, now one for each rank-one term of the partial transpose of `ρ`. -/
theorem W_transpose (L : M3) :
    W (fun X => L * Xᵀ * Lᴴ)
      = ((2 / 21 : ℚ) : ℂ) * (L 0 0 * star (L 0 0) + L 1 1 * star (L 1 1) + L 2 2 * star (L 2 2))
        + ((1 / 14 : ℚ) : ℂ) * ((L 0 1 + 4 / 3 * L 1 0) * star (L 0 1 + 4 / 3 * L 1 0)
            + (L 1 2 + 4 / 3 * L 2 1) * star (L 1 2 + 4 / 3 * L 2 1)
            + (L 2 0 + 4 / 3 * L 0 2) * star (L 2 0 + 4 / 3 * L 0 2))
        + ((5 / 126 : ℚ) : ℂ) * (L 1 0 * star (L 1 0) + L 2 1 * star (L 2 1) + L 0 2 * star (L 0 2)) := by
  simp only [W, LEtL, rhoQ_cast, rhoC, Fin.sum_univ_three]
  simp [star_add, star_mul']
  ring


/-- **The witness is negative on the Choi map**: `tr(ρ C_Φ) = -1/14`. -/
theorem W_choi : W choiMap = -1 / 14 := by
  simp only [W, rhoQ_cast, rhoC, choiMap, E, nxt, Fin.sum_univ_three]
  simp
  norm_num

theorem re_wsq_nonneg (c : ℚ) (hc : 0 ≤ c) (z : ℂ) : 0 ≤ ((c : ℂ) * (z * star z)).re := by
  have hz : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have hcr : (c : ℂ) = ((c : ℝ) : ℂ) := by norm_cast
  rw [hz, hcr, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (by exact_mod_cast hc) (Complex.normSq_nonneg z)

theorem re_wsum3_nonneg (c : ℚ) (hc : 0 ≤ c) (z1 z2 z3 : ℂ) :
    0 ≤ ((c : ℂ) * (z1 * star z1 + z2 * star z2 + z3 * star z3)).re := by
  rw [mul_add, mul_add, Complex.add_re, Complex.add_re]
  exact add_nonneg (add_nonneg (re_wsq_nonneg c hc z1) (re_wsq_nonneg c hc z2)) (re_wsq_nonneg c hc z3)

/-- **The Choi map is not decomposable.** No finite families `K`, `L` give
`Φ(X) = Σ K X Kᴴ + Σ L Xᵀ Lᴴ`: it is not a completely positive map plus a completely positive map
composed with the transpose. -/
theorem choi_not_decomposable :
    ¬ ∃ (m n : ℕ) (K : Fin m → M3) (L : Fin n → M3),
      ∀ X, choiMap X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, h⟩
  have hfun : choiMap = fun X => (fun X => ∑ k, K k * X * (K k)ᴴ) X
      + (fun X => ∑ l, L l * Xᵀ * (L l)ᴴ) X := funext h
  have h1 : W choiMap = ∑ k, W (fun X => K k * X * (K k)ᴴ) + ∑ l, W (fun X => L l * Xᵀ * (L l)ᴴ) := by
    rw [hfun, W_add, W_sum, W_sum]
  have h2 : 0 ≤ (W choiMap).re := by
    rw [h1, Complex.add_re, Complex.re_sum, Complex.re_sum]
    refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (Finset.sum_nonneg fun l _ => ?_)
    · rw [W_kraus, Complex.add_re, Complex.add_re]
      exact add_nonneg (add_nonneg (re_wsq_nonneg _ (by norm_num) _) (re_wsum3_nonneg _ (by norm_num) _ _ _))
        (re_wsum3_nonneg _ (by norm_num) _ _ _)
    · rw [W_transpose, Complex.add_re, Complex.add_re]
      exact add_nonneg (add_nonneg (re_wsum3_nonneg _ (by norm_num) _ _ _)
        (re_wsum3_nonneg _ (by norm_num) _ _ _)) (re_wsum3_nonneg _ (by norm_num) _ _ _)
  rw [W_choi] at h2
  norm_num at h2


/-! ### Positivity on every positive semidefinite input (completes Part 2) -/

theorem choiMap_sum {ι : Type*} (s : Finset ι) (X : ι → M3) :
    choiMap (∑ r ∈ s, X r) = ∑ r ∈ s, choiMap (X r) := by
  ext i j
  simp only [choiMap, Matrix.sum_apply]
  split_ifs <;> simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- The Choi map takes every positive semidefinite matrix `Bᴴ B` to a positive semidefinite one. -/
theorem choi_positive_psd {m : ℕ} (B : Matrix (Fin m) (Fin 3) ℂ) (w : Fin 3 → ℂ) :
    0 ≤ (star w ⬝ᵥ (choiMap (Bᴴ * B) *ᵥ w)).re ∧ (star w ⬝ᵥ (choiMap (Bᴴ * B) *ᵥ w)).im = 0 := by
  have hB : Bᴴ * B = ∑ r, vecMulVec (fun i => star (B r i)) (star fun i => star (B r i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply]
  rw [hB, choiMap_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Complex.im_sum]
  exact ⟨Finset.sum_nonneg fun r _ => (choi_positive _ w).1,
    Finset.sum_eq_zero fun r _ => (choi_positive _ w).2⟩

/-- The Choi map as a `ℂ`-linear map. -/
def choiLin : M3 →ₗ[ℂ] M3 where
  toFun := choiMap
  map_add' X Y := by
    ext i j
    simp only [choiMap, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c X := by
    ext i j
    simp only [choiMap, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-! ### The state is PPT and entangled -/

/-- The witness pairing for a general kernel `r`. -/
noncomputable def Wr (r : Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℂ) (Φ : M3 → M3) : ℂ :=
  ∑ i, ∑ j, ∑ a, ∑ b, r (j, b) (i, a) * Φ (E i j) a b

theorem Wr_sum {ι : Type*} (s : Finset ι) (p : ι → ℂ) (r : ι → Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℂ)
    (Φ : M3 → M3) : Wr (fun x y => ∑ k ∈ s, p k * r k x y) Φ = ∑ k ∈ s, p k * Wr (r k) Φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Wr]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    simp only [Wr, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- On a product state `x ⊗ y`, the pairing is `y† Φ(x̄ x̄†) y`. -/
theorem Wr_product (x y : Fin 3 → ℂ) :
    Wr (fun s t => x s.1 * y s.2 * star (x t.1 * y t.2)) choiMap
      = star y ⬝ᵥ (choiMap (vecMulVec (star x) (star (star x))) *ᵥ y) := by
  simp only [Wr, choiMap, E, nxt, dotProduct, mulVec, vecMulVec_apply, Fin.sum_univ_three, Pi.star_apply]
  simp [star_mul']
  ring

/-- **ρ is PPT**: both `ρ` and its partial transpose are nonnegative sums of rank-one terms. -/
theorem rho_ppt : (∀ k, 0 ≤ rhoWt k) ∧ (∀ k, 0 ≤ ptWt k) ∧
    (∀ j a i b : Fin 3, rhoQ (j, b) (i, a) = ∑ k, ptWt k * ptVec k (j, a) * ptVec k (i, b)) :=
  ⟨by decide +kernel, by decide +kernel, rho_partialTranspose⟩

/-- **ρ is entangled**: it is not a nonnegative combination of product states `x ⊗ y`. Together with
`rho_ppt`, a PPT entangled state on `ℂ³ ⊗ ℂ³`. -/
theorem rho_entangled :
    ¬ ∃ (N : ℕ) (p : Fin N → ℝ) (x y : Fin N → Fin 3 → ℂ), (∀ k, 0 ≤ p k) ∧
      ∀ s t, (rhoQ s t : ℂ) = ∑ k, (p k : ℂ) * (x k s.1 * y k s.2 * star (x k t.1 * y k t.2)) := by
  rintro ⟨N, p, x, y, hp, h⟩
  have h1 : W choiMap = ∑ k, (p k : ℂ) * Wr (fun s t => x k s.1 * y k s.2 * star (x k t.1 * y k t.2)) choiMap := by
    rw [← Wr_sum]
    unfold W Wr
    simp only [h]
  have h2 : 0 ≤ (W choiMap).re := by
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [Wr_product, Complex.re_ofReal_mul]
    exact mul_nonneg (hp k) (choi_positive _ _).1
  rw [W_choi] at h2
  norm_num at h2

/-! ## Part 5. The (3,3) type is dark -/

/-- **The (3,3) type is dark**: there is a positive linear map on `M₃(ℂ)`, taking every positive
semidefinite `Bᴴ B` to a positive semidefinite matrix, that is not decomposable. -/
theorem dark_33 : ∃ Φ : M3 →ₗ[ℂ] M3, IsPositive Φ ∧ ¬ IsDecomposable Φ :=
  ⟨choiLin, fun _ B w => choi_positive_psd B w, choi_not_decomposable⟩


/-! ## Part 6. Every type with both ends of dimension at least three is dark

The Choi map on `M₃` extends to `M_{d₁} → M_{d₂}` for all `d₁, d₂ ≥ 3` by `X ↦ J₂ Φ(J₁ᴴ X J₁) J₂ᴴ`, where
`Jᵢ` includes `ℂ³` as the first three coordinates. The extension is positive, and a decomposition of it
would compress to one of the Choi map. -/

/-- The inclusion of `ℂ³` into `ℂᵈ` as the first three coordinates. -/
def incl (d : ℕ) : Matrix (Fin d) (Fin 3) ℂ := fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem incl_conjTranspose_mul_incl {d : ℕ} (h : 3 ≤ d) : (incl d)ᴴ * incl d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, incl, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨a, by omega⟩]
  · fin_cases a <;> fin_cases b <;> simp
  · intro i _ hi
    have : (i : ℕ) ≠ (a : ℕ) := fun h' => hi (Fin.ext h')
    simp [this]
  · simp

theorem incl_transpose (d : ℕ) : (incl d)ᵀ = (incl d)ᴴ := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, incl]
  split_ifs <;> simp

/-- The extension of the Choi map to `M_{d₁} → M_{d₂}`. -/
noncomputable def extendChoi (d₁ d₂ : ℕ) (X : Matrix (Fin d₁) (Fin d₁) ℂ) : Matrix (Fin d₂) (Fin d₂) ℂ :=
  incl d₂ * choiMap ((incl d₁)ᴴ * X * incl d₁) * (incl d₂)ᴴ

theorem quad_conj {n p : Type*} [Fintype n] [Fintype p] (J : Matrix n p ℂ) (M : Matrix p p ℂ) (w : n → ℂ) :
    star w ⬝ᵥ ((J * M * Jᴴ) *ᵥ w) = star (Jᴴ *ᵥ w) ⬝ᵥ (M *ᵥ (Jᴴ *ᵥ w)) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

/-- The extension as a `ℂ`-linear map. -/
noncomputable def extendChoiLin (d₁ d₂ : ℕ) :
    Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ where
  toFun := extendChoi d₁ d₂
  map_add' X Y := by
    simp only [extendChoi, Matrix.mul_add, Matrix.add_mul]
    rw [show choiMap _ = choiLin _ from rfl, choiLin.map_add]
    simp only [show ∀ Z, choiLin Z = choiMap Z from fun _ => rfl, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [extendChoi, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    rw [show choiMap _ = choiLin _ from rfl, choiLin.map_smul]
    simp only [show ∀ Z, choiLin Z = choiMap Z from fun _ => rfl, Matrix.mul_smul, Matrix.smul_mul]

/-- The extension is positive. -/
theorem extendChoi_positive (d₁ d₂ : ℕ) {m : ℕ} (B : Matrix (Fin m) (Fin d₁) ℂ) (w : Fin d₂ → ℂ) :
    0 ≤ (star w ⬝ᵥ (extendChoi d₁ d₂ (Bᴴ * B) *ᵥ w)).re ∧
      (star w ⬝ᵥ (extendChoi d₁ d₂ (Bᴴ * B) *ᵥ w)).im = 0 := by
  unfold extendChoi
  rw [quad_conj]
  have hB : (incl d₁)ᴴ * (Bᴴ * B) * incl d₁ = (B * incl d₁)ᴴ * (B * incl d₁) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hB]
  exact choi_positive_psd _ _

/-- The extension is not decomposable. -/
theorem extendChoi_not_decomposable {d₁ d₂ : ℕ} (h₁ : 3 ≤ d₁) (h₂ : 3 ≤ d₂) :
    ¬ ∃ (m n : ℕ) (K : Fin m → Matrix (Fin d₂) (Fin d₁) ℂ) (L : Fin n → Matrix (Fin d₂) (Fin d₁) ℂ),
      ∀ X, extendChoi d₁ d₂ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, h⟩
  apply choi_not_decomposable
  refine ⟨m, n, fun k => (incl d₂)ᴴ * K k * incl d₁, fun l => (incl d₂)ᴴ * L l * incl d₁, fun Y => ?_⟩
  have hc : choiMap Y = (incl d₂)ᴴ * extendChoi d₁ d₂ (incl d₁ * Y * (incl d₁)ᴴ) * incl d₂ := by
    unfold extendChoi
    have e₁ : (incl d₁)ᴴ * (incl d₁ * Y * (incl d₁)ᴴ) * incl d₁ = Y := by
      rw [show (incl d₁)ᴴ * (incl d₁ * Y * (incl d₁)ᴴ) * incl d₁
          = ((incl d₁)ᴴ * incl d₁) * Y * ((incl d₁)ᴴ * incl d₁) by simp only [Matrix.mul_assoc],
        incl_conjTranspose_mul_incl h₁, Matrix.one_mul, Matrix.mul_one]
    rw [e₁]
    rw [show (incl d₂)ᴴ * (incl d₂ * choiMap Y * (incl d₂)ᴴ) * incl d₂
        = ((incl d₂)ᴴ * incl d₂) * choiMap Y * ((incl d₂)ᴴ * incl d₂) by simp only [Matrix.mul_assoc],
      incl_conjTranspose_mul_incl h₂, Matrix.one_mul, Matrix.mul_one]
  rw [hc, h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have hreal : ((incl d₁)ᴴ)ᵀ = incl d₁ := by
      rw [← incl_transpose, Matrix.transpose_transpose]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hreal, incl_transpose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **Every type with both ends of dimension at least three is dark**: for all `d₁, d₂ ≥ 3` there is
a positive map `M_{d₁}(ℂ) → M_{d₂}(ℂ)` that is not decomposable. This covers Chain Theory's (3,3), (3,4),
(4,3) and (4,4) genres; the (2,4) genre needs a separate map (Woronowicz's). -/
theorem dark_of_three_le {d₁ d₂ : ℕ} (h₁ : 3 ≤ d₁) (h₂ : 3 ≤ d₂) :
    ∃ Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ, IsPositive Φ ∧ ¬ IsDecomposable Φ :=
  ⟨extendChoiLin d₁ d₂, fun _ B w => extendChoi_positive d₁ d₂ B w, extendChoi_not_decomposable h₁ h₂⟩


/-! ## Part 7. The (2,4) type is dark

A positive map `Φ₂₄ : M₂(ℂ) → M₄(ℂ)` with integer coefficients. Positivity is certified by a
sum-of-squares identity with the multiplier `‖v‖²` (`phi24_certificate`). Non-decomposability is shown
by the PPT state of P. Horodecki's 2 ⊗ 4 family at `b = 3/5`, on which the witness value is `-1`. The map
and its certificate were found by semidefinite programming and rationalized exactly; everything below
is checked by the kernel. -/

/-- The (2,4) map: `Φ₂₄(X)_kl = Σ_ab X_ab W((a,k),(b,l))` with the integer witness `W` below. -/
def phi24 (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![((32 : ℤ) : ℂ) * X 0 0 + ((75 : ℤ) : ℂ) * X 1 1, ((-82 : ℤ) : ℂ) * X 0 1, ((20 : ℤ) : ℂ) * X 1 0, ((30 : ℤ) : ℂ) * X 0 0 + ((-74 : ℤ) : ℂ) * X 1 1;
    ((-82 : ℤ) : ℂ) * X 1 0, ((206 : ℤ) : ℂ) * X 0 0 + ((187 : ℤ) : ℂ) * X 1 1, ((-316 : ℤ) : ℂ) * X 0 1, ((20 : ℤ) : ℂ) * X 1 0;
    ((20 : ℤ) : ℂ) * X 0 1, ((-316 : ℤ) : ℂ) * X 1 0, ((206 : ℤ) : ℂ) * X 0 0 + ((187 : ℤ) : ℂ) * X 1 1, ((-82 : ℤ) : ℂ) * X 0 1;
    ((30 : ℤ) : ℂ) * X 0 0 + ((-74 : ℤ) : ℂ) * X 1 1, ((20 : ℤ) : ℂ) * X 0 1, ((-82 : ℤ) : ℂ) * X 1 0, ((32 : ℤ) : ℂ) * X 0 0 + ((75 : ℤ) : ℂ) * X 1 1]

/-- The sum-of-squares certificate: `‖v‖² · w†Φ₂₄(vv†)w` is a nonnegative combination of squared moduli. -/
theorem phi24_certificate (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :
    (v 0 * star (v 0) + v 1 * star (v 1)) * (((32 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 0) * w 0) + ((30 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 0) * w 3) + ((-82 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 1) * w 1) + ((206 : ℤ) : ℂ) * (v 0 * star (w 1) * star (v 0) * w 1) + ((-316 : ℤ) : ℂ) * (v 0 * star (w 1) * star (v 1) * w 2) + ((206 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 0) * w 2) + ((20 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 1) * w 0) + ((-82 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 1) * w 3) + ((30 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 0) * w 0) + ((32 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 0) * w 3) + ((20 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 1) * w 1) + ((20 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 0) * w 2) + ((75 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 1) * w 0) + ((-74 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 1) * w 3) + ((-82 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 0) * w 0) + ((20 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 0) * w 3) + ((187 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 1) * w 1) + ((-316 : ℤ) : ℂ) * (v 1 * star (w 2) * star (v 0) * w 1) + ((187 : ℤ) : ℂ) * (v 1 * star (w 2) * star (v 1) * w 2) + ((-82 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 0) * w 2) + ((-74 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 1) * w 0) + ((75 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 1) * w 3))
      = ((1 / 1206000 : ℚ) : ℂ) * ((((2010 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 0) + ((1610 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 3) + ((6399 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-7512 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2)) * star (((2010 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 0) + ((1610 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 3) + ((6399 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-7512 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2))) + ((1 / 22588800 : ℚ) : ℂ) * ((((37648 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 1) + ((-28833 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 2) + ((10842 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((-10842 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3)) * star (((37648 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 1) + ((-28833 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 2) + ((10842 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((-10842 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3))) + ((1 / 1205600 : ℚ) : ℂ) * ((((6028 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 2) + ((2158 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 0) + ((-6053 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((422 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1)) * star (((6028 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 2) + ((2158 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 0) + ((-6053 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((422 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1))) + ((1 / 69851520000 : ℚ) : ℂ) * ((((289600 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 3) + ((523377 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-600156 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2)) * star (((289600 : ℤ) : ℂ) * (star (v 0) * star (v 0) * w 3) + ((523377 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-600156 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2))) + ((1 / 85190684079600 : ℚ) : ℂ) * ((((47108319 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 0) + ((-2131351 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((-45188067 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1)) * star (((47108319 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 0) + ((-2131351 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((-45188067 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1))) + ((1 / 66565639281280000 : ℚ) : ℂ) * ((((574634317 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-589887276 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2)) * star (((574634317 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 1) + ((-589887276 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2))) + ((1 / 53461673449600 : ℚ) : ℂ) * ((((7100201 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 2) + ((-816634 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((797810 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3)) * star (((7100201 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 2) + ((-816634 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((797810 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3))) + ((1 / 11487148401833519968800 : ℚ) : ℂ) * ((((101602263373 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((-17161485180 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1)) * star (((101602263373 : ℤ) : ℂ) * (star (v 0) * star (v 1) * w 3) + ((-17161485180 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1))) + ((1 / 854327105695355000 : ℚ) : ℂ) * ((((601621775 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((-133416826 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3)) * star (((601621775 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 0) + ((-133416826 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3))) + ((44597024133767 / 40640905349200 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1)) * star (((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 1))) + ((64571935258 / 43097573775 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2)) * star (((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 2))) + ((48538675599 / 120324355000 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3)) * star (((1 : ℤ) : ℂ) * (star (v 1) * star (v 1) * w 3))) + ((1 / 9108000 : ℚ) : ℂ) * ((((15180 : ℤ) : ℂ) * (v 0 * star (v 0) * w 0) + ((14780 : ℤ) : ℂ) * (v 0 * star (v 0) * w 3) + ((-15105 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-15078 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((3 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-26 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((15180 : ℤ) : ℂ) * (v 0 * star (v 0) * w 0) + ((14780 : ℤ) : ℂ) * (v 0 * star (v 0) * w 3) + ((-15105 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-15078 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((3 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-26 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((1 / 162873600 : ℚ) : ℂ) * ((((135728 : ℤ) : ℂ) * (v 0 * star (v 0) * w 1) + ((-131922 : ℤ) : ℂ) * (v 0 * star (v 1) * w 2) + ((-44670 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((28347 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((37932 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1)) * star (((135728 : ℤ) : ℂ) * (v 0 * star (v 0) * w 1) + ((-131922 : ℤ) : ℂ) * (v 0 * star (v 1) * w 2) + ((-44670 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((28347 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((37932 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1))) + ((1 / 18100800 : ℚ) : ℂ) * ((((45252 : ℤ) : ℂ) * (v 0 * star (v 0) * w 2) + ((9452 : ℤ) : ℂ) * (v 0 * star (v 1) * w 0) + ((-14890 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((-43986 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((12645 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2)) * star (((45252 : ℤ) : ℂ) * (v 0 * star (v 0) * w 2) + ((9452 : ℤ) : ℂ) * (v 0 * star (v 1) * w 0) + ((-14890 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((-43986 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((12645 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2))) + ((1 / 1091502720000 : ℚ) : ℂ) * ((((1198400 : ℤ) : ℂ) * (v 0 * star (v 0) * w 3) + ((-560937 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-644106 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((-43902 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((42982 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((1198400 : ℤ) : ℂ) * (v 0 * star (v 0) * w 3) + ((-560937 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-644106 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((-43902 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((42982 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((1 / 85325166536400 : ℚ) : ℂ) * ((((18855557 : ℤ) : ℂ) * (v 0 * star (v 1) * w 0) + ((-9810502 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((78824058 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-68061510 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2)) * star (((18855557 : ℤ) : ℂ) * (v 0 * star (v 1) * w 0) + ((-9810502 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((78824058 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-68061510 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2))) + ((1 / 7062728026014080000 : ℚ) : ℂ) * ((((14733661603 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-14168373586 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((-20871375862 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((20851666142 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((14733661603 : ℤ) : ℂ) * (v 0 * star (v 1) * w 1) + ((-14168373586 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((-20871375862 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((20851666142 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((1 / 572164920040147200 : ℚ) : ℂ) * ((((7025876754 : ℤ) : ℂ) * (v 0 * star (v 1) * w 2) + ((-455326158 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((1418093683 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-6339357132 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1)) * star (((7025876754 : ℤ) : ℂ) * (v 0 * star (v 1) * w 2) + ((-455326158 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((1418093683 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-6339357132 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1))) + ((1 / 47624653142371605350400 : ℚ) : ℂ) * ((((1052400916928 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((157004189514 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-1158874165773 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2)) * star (((1052400916928 : ℤ) : ℂ) * (v 0 * star (v 1) * w 3) + ((157004189514 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-1158874165773 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2))) + ((1 / 758811310388390740794768000 : ℚ) : ℂ) * ((((135002957096490 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((-5847344715263 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-128287077781140 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1)) * star (((135002957096490 : ℤ) : ℂ) * (v 1 * star (v 0) * w 0) + ((-5847344715263 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-128287077781140 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1))) + ((1 / 2287852440291009061433617561600 : ℚ) : ℂ) * ((((5434840476406418 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-4682424345843921 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2)) * star (((5434840476406418 : ℤ) : ℂ) * (v 1 * star (v 0) * w 1) + ((-4682424345843921 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2))) + ((1 / 8030848657084248606420068000 : ℚ) : ℂ) * ((((136267020267539 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((96180177158126 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-100933720015052 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((136267020267539 : ℤ) : ℂ) * (v 1 * star (v 0) * w 2) + ((96180177158126 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-100933720015052 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((1 / 63948167374189559959930819208472000 : ℚ) : ℂ) * ((((197366563757575697 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-103183341871362090 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1)) * star (((197366563757575697 : ℤ) : ℂ) * (v 1 * star (v 0) * w 3) + ((-103183341871362090 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1))) + ((1 / 95022973599946202050891159880700000 : ℚ) : ℂ) * ((((290553837523633875 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-179799634037043124 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((290553837523633875 : ℤ) : ℂ) * (v 1 * star (v 1) * w 0) + ((-179799634037043124 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((171573728181777020717 / 78946625503030278800 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1)) * star (((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 1))) + ((14192729429993321393 / 6521808571687701600 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2)) * star (((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 2))) + ((23882771514144117001 / 43583075628545081250 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3)) * star (((1 : ℤ) : ℂ) * (v 1 * star (v 1) * w 3))) + ((1 / 301500 : ℚ) : ℂ) * ((((1005 : ℤ) : ℂ) * (v 0 * v 0 * w 0) + ((805 : ℤ) : ℂ) * (v 0 * v 0 * w 3) + ((3213 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-3756 : ℤ) : ℂ) * (v 1 * v 1 * w 1)) * star (((1005 : ℤ) : ℂ) * (v 0 * v 0 * w 0) + ((805 : ℤ) : ℂ) * (v 0 * v 0 * w 3) + ((3213 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-3756 : ℤ) : ℂ) * (v 1 * v 1 * w 1))) + ((1 / 43411200 : ℚ) : ℂ) * ((((36176 : ℤ) : ℂ) * (v 0 * v 0 * w 1) + ((-36318 : ℤ) : ℂ) * (v 0 * v 1 * w 0) + ((12951 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((2532 : ℤ) : ℂ) * (v 1 * v 1 * w 2)) * star (((36176 : ℤ) : ℂ) * (v 0 * v 0 * w 1) + ((-36318 : ℤ) : ℂ) * (v 0 * v 1 * w 0) + ((12951 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((2532 : ℤ) : ℂ) * (v 1 * v 1 * w 2))) + ((1 / 22582800 : ℚ) : ℂ) * ((((37638 : ℤ) : ℂ) * (v 0 * v 0 * w 2) + ((-28827 : ℤ) : ℂ) * (v 0 * v 1 * w 1) + ((-10842 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((10838 : ℤ) : ℂ) * (v 1 * v 1 * w 3)) * star (((37638 : ℤ) : ℂ) * (v 0 * v 0 * w 2) + ((-28827 : ℤ) : ℂ) * (v 0 * v 1 * w 1) + ((-10842 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((10838 : ℤ) : ℂ) * (v 1 * v 1 * w 3))) + ((1 / 17462880000 : ℚ) : ℂ) * ((((144800 : ℤ) : ℂ) * (v 0 * v 0 * w 3) + ((251613 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-300480 : ℤ) : ℂ) * (v 1 * v 1 * w 1)) * star (((144800 : ℤ) : ℂ) * (v 0 * v 0 * w 3) + ((251613 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-300480 : ℤ) : ℂ) * (v 1 * v 1 * w 1))) + ((1 / 451676301753600 : ℚ) : ℂ) * ((((20809206 : ℤ) : ℂ) * (v 0 * v 1 * w 0) + ((-25579399 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((21288468 : ℤ) : ℂ) * (v 1 * v 1 * w 2)) * star (((20809206 : ℤ) : ℂ) * (v 0 * v 1 * w 0) + ((-25579399 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((21288468 : ℤ) : ℂ) * (v 1 * v 1 * w 2))) + ((1 / 5901088885200 : ℚ) : ℂ) * ((((2351781 : ℤ) : ℂ) * (v 0 * v 1 * w 1) + ((245049 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((-264134 : ℤ) : ℂ) * (v 1 * v 1 * w 3)) * star (((2351781 : ℤ) : ℂ) * (v 0 * v 1 * w 1) + ((245049 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((-264134 : ℤ) : ℂ) * (v 1 * v 1 * w 3))) + ((1 / 4160588124320000 : ℚ) : ℂ) * ((((143666717 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-147158000 : ℤ) : ℂ) * (v 1 * v 1 * w 1)) * star (((143666717 : ℤ) : ℂ) * (v 0 * v 1 * w 2) + ((-147158000 : ℤ) : ℂ) * (v 1 * v 1 * w 1))) + ((1 / 61358061434920249665600 : ℚ) : ℂ) * ((((1228584066649 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((-1187861122290 : ℤ) : ℂ) * (v 1 * v 1 * w 2)) * star (((1228584066649 : ℤ) : ℂ) * (v 0 * v 1 * w 3) + ((-1187861122290 : ℤ) : ℂ) * (v 1 * v 1 * w 2))) + ((1 / 3381557494116409200 : ℚ) : ℂ) * ((((1198225761 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((-270103502 : ℤ) : ℂ) * (v 1 * v 1 * w 3)) * star (((1198225761 : ℤ) : ℂ) * (v 1 * v 1 * w 0) + ((-270103502 : ℤ) : ℂ) * (v 1 * v 1 * w 3))) + ((53646365563 / 35916679250 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * v 1 * w 1)) * star (((1 : ℤ) : ℂ) * (v 1 * v 1 * w 1))) + ((323133982937873 / 294860175995760 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * v 1 * w 2)) * star (((1 : ℤ) : ℂ) * (v 1 * v 1 * w 2))) + ((145656196333 / 359467728300 : ℚ) : ℂ) * ((((1 : ℤ) : ℂ) * (v 1 * v 1 * w 3)) * star (((1 : ℤ) : ℂ) * (v 1 * v 1 * w 3))) := by
  simp only [star_add, star_mul', star_star, star_intCast]
  ring

/-- The 5 rank-one terms of the witness state ρ (Horodecki, b = 3/5), index `4a + k`. -/
def rho24Wt : Fin 5 → ℚ := ![(2 / 13 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ)]
def rho24Vec : Fin 5 → Fin 8 → ℚ := ![![(0 : ℚ), (0 : ℚ), (3 / 4 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],
  ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],
  ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (-1 / 2 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]]
/-- The 5 rank-one terms of its partial transpose. -/
def pt24Wt : Fin 5 → ℚ := ![(2 / 13 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ), (3 / 26 : ℚ)]
def pt24Vec : Fin 5 → Fin 8 → ℚ := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 2 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(1 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)]]
/-- The witness integer matrix `W` (the Choi matrix of `phi24`), index `4a + k`. -/
def W24 : Fin 8 → Fin 8 → ℚ := ![![(32 : ℚ), (0 : ℚ), (0 : ℚ), (30 : ℚ), (0 : ℚ), (-82 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (206 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-316 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (206 : ℚ), (0 : ℚ), (20 : ℚ), (0 : ℚ), (0 : ℚ), (-82 : ℚ)],
  ![(30 : ℚ), (0 : ℚ), (0 : ℚ), (32 : ℚ), (0 : ℚ), (20 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (20 : ℚ), (0 : ℚ), (75 : ℚ), (0 : ℚ), (0 : ℚ), (-74 : ℚ)],
  ![(-82 : ℚ), (0 : ℚ), (0 : ℚ), (20 : ℚ), (0 : ℚ), (187 : ℚ), (0 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (-316 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (187 : ℚ), (0 : ℚ)],
  ![(0 : ℚ), (0 : ℚ), (-82 : ℚ), (0 : ℚ), (-74 : ℚ), (0 : ℚ), (0 : ℚ), (75 : ℚ)]]

theorem phi24_quad (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :
    star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w) = ((32 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 0) * w 0) + ((30 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 0) * w 3) + ((-82 : ℤ) : ℂ) * (v 0 * star (w 0) * star (v 1) * w 1) + ((206 : ℤ) : ℂ) * (v 0 * star (w 1) * star (v 0) * w 1) + ((-316 : ℤ) : ℂ) * (v 0 * star (w 1) * star (v 1) * w 2) + ((206 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 0) * w 2) + ((20 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 1) * w 0) + ((-82 : ℤ) : ℂ) * (v 0 * star (w 2) * star (v 1) * w 3) + ((30 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 0) * w 0) + ((32 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 0) * w 3) + ((20 : ℤ) : ℂ) * (v 0 * star (w 3) * star (v 1) * w 1) + ((20 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 0) * w 2) + ((75 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 1) * w 0) + ((-74 : ℤ) : ℂ) * (v 1 * star (w 0) * star (v 1) * w 3) + ((-82 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 0) * w 0) + ((20 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 0) * w 3) + ((187 : ℤ) : ℂ) * (v 1 * star (w 1) * star (v 1) * w 1) + ((-316 : ℤ) : ℂ) * (v 1 * star (w 2) * star (v 0) * w 1) + ((187 : ℤ) : ℂ) * (v 1 * star (w 2) * star (v 1) * w 2) + ((-82 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 0) * w 2) + ((-74 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 1) * w 0) + ((75 : ℤ) : ℂ) * (v 1 * star (w 3) * star (v 1) * w 3) := by
  simp only [dotProduct, mulVec, phi24, vecMulVec_apply, Fin.sum_univ_four, Pi.star_apply]
  simp
  ring

/-- `Φ₂₄` is positive on rank-one inputs: `w† Φ₂₄(v v†) w` is real and nonnegative. -/
theorem phi24_positive (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :
    0 ≤ (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w)).re ∧
      (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w)).im = 0 := by
  have hc := phi24_certificate v w
  rw [← phi24_quad] at hc
  have h0 : v 0 * star (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj (v 0)
  have h1 : v 1 * star (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj (v 1)
  have him : ∀ (c : ℚ) (z : ℂ), ((c : ℂ) * (z * star z)).im = 0 := fun c z => by
    simp only [Complex.mul_im, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hR : 0 ≤ (((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ)
      * (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w))).re := by
    rw [Complex.ofReal_add, ← h0, ← h1, hc]
    simp only [Complex.add_re]
    repeat' (first | (apply re_wsq_nonneg; norm_num) | apply add_nonneg)
  have hI : (((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ)
      * (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w))).im = 0 := by
    rw [Complex.ofReal_add, ← h0, ← h1, hc]
    simp only [Complex.add_im, him, add_zero]
  rw [Complex.re_ofReal_mul] at hR
  rw [Complex.im_ofReal_mul] at hI
  rcases (add_nonneg (Complex.normSq_nonneg (v 0)) (Complex.normSq_nonneg (v 1))).lt_or_eq with hpos | hzero
  · exact ⟨(mul_nonneg_iff_of_pos_left hpos).1 hR, (mul_eq_zero.1 hI).resolve_left hpos.ne'⟩
  · have hv0 : v 0 = 0 := by
      have := Complex.normSq_nonneg (v 1)
      exact Complex.normSq_eq_zero.1 (by linarith [Complex.normSq_nonneg (v 0)])
    have hv1 : v 1 = 0 := by
      exact Complex.normSq_eq_zero.1 (by linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)])
    rw [phi24_quad, hv0, hv1]
    simp

theorem phi24_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    phi24 (∑ r ∈ s, X r) = ∑ r ∈ s, phi24 (X r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi24, Matrix.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]

/-- `Φ₂₄` takes every positive semidefinite matrix `Bᴴ B` to a positive semidefinite one. -/
theorem phi24_positive_psd {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℂ) (w : Fin 4 → ℂ) :
    0 ≤ (star w ⬝ᵥ (phi24 (Bᴴ * B) *ᵥ w)).re ∧ (star w ⬝ᵥ (phi24 (Bᴴ * B) *ᵥ w)).im = 0 := by
  have hB : Bᴴ * B = ∑ r, vecMulVec (fun i => star (B r i)) (star fun i => star (B r i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply]
  rw [hB, phi24_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Complex.im_sum]
  exact ⟨Finset.sum_nonneg fun r _ => (phi24_positive _ w).1,
    Finset.sum_eq_zero fun r _ => (phi24_positive _ w).2⟩

/-! ### The witness state and non-decomposability -/

def ix (a : Fin 2) (k : Fin 4) : Fin 8 := ⟨4 * a.val + k.val, by omega⟩

/-- The witness state `ρ((a,k),(b,l))`, a nonnegative sum of rational rank-one terms. -/
def rho24 (a : Fin 2) (k : Fin 4) (b : Fin 2) (l : Fin 4) : ℚ :=
  ∑ j, rho24Wt j * rho24Vec j (ix a k) * rho24Vec j (ix b l)

theorem rho24_weights_nonneg : (∀ j, 0 ≤ rho24Wt j) ∧ (∀ j, 0 ≤ pt24Wt j) := by decide +kernel

theorem rho24_trace : ∑ a, ∑ k, rho24 a k a k = 1 := by decide +kernel

/-- The partial transpose of `ρ` (on the second factor) is the nonnegative sum `pt24`. -/
theorem rho24_pt : ∀ a k b l, rho24 b l a k = ∑ j, pt24Wt j * pt24Vec j (ix b k) * pt24Vec j (ix a l) := by
  decide +kernel

theorem rho24_witness_value :
    ∑ a, ∑ k, ∑ b, ∑ l, rho24 b l a k * W24 (ix a k) (ix b l) = -1 := by decide +kernel

def E2 (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := fun r c => if r = a ∧ c = b then 1 else 0

/-- The witness pairing `tr(ρ C_Φ)` of a map `M₂ → M₄`. -/
noncomputable def W2 (Φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ a, ∑ k, ∑ b, ∑ l, (rho24 b l a k : ℂ) * Φ (E2 a b) k l

theorem W2_add (Φ Ψ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    W2 (fun X => Φ X + Ψ X) = W2 Φ + W2 Ψ := by
  simp only [W2, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem W2_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    W2 (fun X => ∑ k ∈ s, F k X) = ∑ k ∈ s, W2 (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W2]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [W2_add (F a) (fun X => ∑ k ∈ s, F k X), ih]

theorem phi24_E (a b : Fin 2) (k l : Fin 4) : phi24 (E2 a b) k l = (W24 (ix a k) (ix b l) : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases l <;>
    simp [phi24, E2, W24, ix]

/-- **The witness is negative on `Φ₂₄`**: `tr(ρ C_Φ) = -1`. -/
theorem W2_phi24 : W2 phi24 = -1 := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) rho24_witness_value
  push_cast at h
  simpa [W2, phi24_E] using h

theorem kEK24 (K : Matrix (Fin 4) (Fin 2) ℂ) (a b : Fin 2) (k l : Fin 4) :
    (K * E2 a b * Kᴴ) k l = K k a * star (K l b) := by
  simp [Matrix.mul_apply, E2, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

theorem LEtL24 (L : Matrix (Fin 4) (Fin 2) ℂ) (a b : Fin 2) (k l : Fin 4) :
    (L * (E2 a b)ᵀ * Lᴴ) k l = L k b * star (L l a) := by
  simp [Matrix.mul_apply, E2, Matrix.conjTranspose_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

theorem star_ratC (q : ℚ) : star (q : ℂ) = q := by
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast]
  exact Complex.conj_ofReal _

/-- On a completely positive part, the witness is a nonnegative sum of squares. -/
theorem W2_kraus (K : Matrix (Fin 4) (Fin 2) ℂ) :
    W2 (fun X => K * X * Kᴴ) = ∑ j, (rho24Wt j : ℂ) *
      ((∑ a, ∑ k, (rho24Vec j (ix a k) : ℂ) * K k a) * star (∑ a, ∑ k, (rho24Vec j (ix a k) : ℂ) * K k a)) := by
  simp only [W2, kEK24, rho24, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_five,
    star_add, star_mul', star_ratC]
  push_cast
  ring

/-- On a part composed with the transpose, the witness is again a nonnegative sum of squares, from the
rank-one terms of the partial transpose. -/
theorem W2_transpose (L : Matrix (Fin 4) (Fin 2) ℂ) :
    W2 (fun X => L * Xᵀ * Lᴴ) = ∑ j, (pt24Wt j : ℂ) *
      ((∑ b, ∑ k, (pt24Vec j (ix b k) : ℂ) * L k b) * star (∑ b, ∑ k, (pt24Vec j (ix b k) : ℂ) * L k b)) := by
  simp only [W2, LEtL24, rho24_pt, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_five,
    star_add, star_mul', star_ratC]
  push_cast
  ring

theorem re_wsum_nonneg {n : ℕ} (c : Fin n → ℚ) (hc : ∀ j, 0 ≤ c j) (z : Fin n → ℂ) :
    0 ≤ (∑ j, (c j : ℂ) * (z j * star (z j))).re := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => re_wsq_nonneg (c j) (hc j) (z j)

/-- **`Φ₂₄` is not decomposable.** -/
theorem phi24_not_decomposable :
    ¬ ∃ (m n : ℕ) (K : Fin m → Matrix (Fin 4) (Fin 2) ℂ) (L : Fin n → Matrix (Fin 4) (Fin 2) ℂ),
      ∀ X, phi24 X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, h⟩
  have hfun : phi24 = fun X => (fun X => ∑ k, K k * X * (K k)ᴴ) X
      + (fun X => ∑ l, L l * Xᵀ * (L l)ᴴ) X := funext h
  have h1 : W2 phi24 = ∑ k, W2 (fun X => K k * X * (K k)ᴴ) + ∑ l, W2 (fun X => L l * Xᵀ * (L l)ᴴ) := by
    rw [hfun, W2_add, W2_sum, W2_sum]
  have h2 : 0 ≤ (W2 phi24).re := by
    rw [h1, Complex.add_re, Complex.re_sum, Complex.re_sum]
    refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (Finset.sum_nonneg fun l _ => ?_)
    · rw [W2_kraus]; exact re_wsum_nonneg _ rho24_weights_nonneg.1 _
    · rw [W2_transpose]; exact re_wsum_nonneg _ rho24_weights_nonneg.2 _
  rw [W2_phi24] at h2
  norm_num at h2

/-! ## Part 8. Every type with `d₁ d₂ ≥ 8` is dark: the dark direction of the read cap -/

/-- The inclusion of `ℂⁿ` into `ℂᵈ` as the first `n` coordinates. -/
def inclN (n d : ℕ) : Matrix (Fin d) (Fin n) ℂ := fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem inclN_conjTranspose_mul {n d : ℕ} (h : n ≤ d) : (inclN n d)ᴴ * inclN n d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclN, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨a, by omega⟩]
  · by_cases hab : a = b
    · subst hab; simp
    · have : (a : ℕ) ≠ (b : ℕ) := fun h' => hab (Fin.ext h')
      simp [hab, this]
  · intro i _ hi
    have : (i : ℕ) ≠ (a : ℕ) := fun h' => hi (Fin.ext h')
    simp [this]
  · simp

/-- The extension of `Φ₂₄` to `M₂ → M_d`. -/
noncomputable def extend24 (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  inclN 4 d * phi24 X * (inclN 4 d)ᴴ

/-- `Φ₂₄` as a `ℂ`-linear map. -/
def phi24Lin : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := phi24
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phi24] <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phi24] <;> ring

/-- The extension of `Φ₂₄` to `M₂ → M_d` as a `ℂ`-linear map. -/
noncomputable def extend24Lin (d : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun := extend24 d
  map_add' X Y := by
    simp only [extend24]
    rw [show phi24 (X + Y) = phi24Lin (X + Y) from rfl, phi24Lin.map_add]
    simp only [show ∀ Z, phi24Lin Z = phi24 Z from fun _ => rfl, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [extend24, RingHom.id_apply]
    rw [show phi24 (c • X) = phi24Lin (c • X) from rfl, phi24Lin.map_smul]
    simp only [show ∀ Z, phi24Lin Z = phi24 Z from fun _ => rfl, Matrix.mul_smul, Matrix.smul_mul]

theorem extend24_positive (d : ℕ) {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℂ) (w : Fin d → ℂ) :
    0 ≤ (star w ⬝ᵥ (extend24 d (Bᴴ * B) *ᵥ w)).re ∧ (star w ⬝ᵥ (extend24 d (Bᴴ * B) *ᵥ w)).im = 0 := by
  unfold extend24
  rw [quad_conj]
  exact phi24_positive_psd _ _

theorem extend24_not_decomposable {d : ℕ} (h : 4 ≤ d) :
    ¬ ∃ (m n : ℕ) (K : Fin m → Matrix (Fin d) (Fin 2) ℂ) (L : Fin n → Matrix (Fin d) (Fin 2) ℂ),
      ∀ X, extend24 d X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, hK⟩
  apply phi24_not_decomposable
  refine ⟨m, n, fun k => (inclN 4 d)ᴴ * K k, fun l => (inclN 4 d)ᴴ * L l, fun X => ?_⟩
  have hc : phi24 X = (inclN 4 d)ᴴ * extend24 d X * inclN 4 d := by
    unfold extend24
    rw [show (inclN 4 d)ᴴ * (inclN 4 d * phi24 X * (inclN 4 d)ᴴ) * inclN 4 d
        = ((inclN 4 d)ᴴ * inclN 4 d) * phi24 X * ((inclN 4 d)ᴴ * inclN 4 d) by simp only [Matrix.mul_assoc],
      inclN_conjTranspose_mul h, Matrix.one_mul, Matrix.mul_one]
  rw [hc, hK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **The dark direction of the read cap.** A readable type with both ends of dimension at least two has
`d₁ d₂ ≤ 6`. Equivalently, every type with `d₁ d₂ ≥ 8` (no product of two integers `≥ 2` is 7) has a
positive, non-decomposable map between its ends. -/
theorem readable_imp_le_six {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (hr : Readable d₁ d₂) :
    d₁ * d₂ ≤ 6 := by
  by_contra hlt
  push Not at hlt
  by_cases h33 : 3 ≤ d₁ ∧ 3 ≤ d₂
  · obtain ⟨Φ, hpos, hnd⟩ := dark_of_three_le h33.1 h33.2
    exact hnd (hr.1 Φ fun r B w => hpos r B w)
  · rcases Nat.lt_or_ge d₁ 3 with hd₁ | hd₁
    · obtain rfl : d₁ = 2 := by omega
      have h4 : 4 ≤ d₂ := by omega
      exact extend24_not_decomposable h4
        (hr.1 (extend24Lin d₂) fun r B w => extend24_positive d₂ B w)
    · obtain rfl : d₂ = 2 := by omega
      have h4 : 4 ≤ d₁ := by omega
      exact extend24_not_decomposable h4
        (hr.2 (extend24Lin d₁) fun r B w => extend24_positive d₁ B w)

end ChoiDark

end -- public section

#print axioms ChoiDark.choi_real
#print axioms ChoiDark.choi_positive
#print axioms ChoiDark.choi_positive_psd
#print axioms ChoiDark.rho_partialTranspose
#print axioms ChoiDark.W_choi
#print axioms ChoiDark.choi_not_decomposable
#print axioms ChoiDark.rho_ppt
#print axioms ChoiDark.rho_entangled
#print axioms ChoiDark.dark_33
#print axioms ChoiDark.dark_of_three_le
#print axioms ChoiDark.phi24_positive_psd
#print axioms ChoiDark.phi24_not_decomposable
#print axioms ChoiDark.readable_imp_le_six

import Mathlib

/-!
# Permanent algebra for the critical envelope (`prop:fqe-critical-envelope`, equality case)

Real `3 × 3` algebra used in the equality classification of `sextic_identity.tex`,
`prop:fqe-critical-envelope` / `thm:fqe-general-envelope` (the permanent bound
`perm Θ ≥ -(2 + 3κ² + 4κ³)/9` and its equality cases). Nothing here mentions quantum states.

* `perm3`: the permanent of a `3 × 3` real matrix.
* `cf`, `cw`, `cmon`, `perm3_pair`, `perm3_sq_sum`: the Fischer (apolar) pairing of the cubic forms
  `x ↦ ∏ᵢ (X x)ᵢ`: `perm (X Yᵀ) = Σ_α α! c_α(X) c_α(Y)`; hence `perm(XXᵀ) + perm(YYᵀ) + 2 perm(XYᵀ)`
  is a sum of squares (the Cauchy–Schwarz step `|perm Θ| ≤ (perm(ODOᵀ) perm D)^{1/2}` of the paper, in the
  AM–GM form that needs no square root), with the equality case `c_α(X) = -c_α(Y)`.
* `perm_rank1_le`, `perm_rank1_eq`: `perm(κ I + (1-κ) u uᵀ) ≤ (2 + 3κ² + 4κ³)/9` for a unit `u`, with
  equality (`0 < κ < 1`) only at `u_i² = 1/3` (the Maclaurin step).
* `IsSignedCyclic`, `signedCyclic_of_cubic`: an orthogonal `O` of determinant `-1` with
  `∏ᵢ (O y)ᵢ = -∏ᵢ yᵢ` is one of the twelve signed cyclic permutation matrices whose three signs have
  product `-1`.

No hypotheses beyond those stated; no `sorry`, no `native_decide`.
-/

namespace FormalResearch.FourQubitEntropy
open Matrix

def perm3 (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 +
  M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 + M 0 2 * M 1 1 * M 2 0

def cf (X : Matrix (Fin 3) (Fin 3) ℝ) : Fin 10 → ℝ := ![
  X 0 0 * X 1 0 * X 2 0, X 0 1 * X 1 1 * X 2 1, X 0 2 * X 1 2 * X 2 2,
  X 0 0 * X 1 0 * X 2 1 + X 0 0 * X 1 1 * X 2 0 + X 0 1 * X 1 0 * X 2 0,
  X 0 0 * X 1 0 * X 2 2 + X 0 0 * X 1 2 * X 2 0 + X 0 2 * X 1 0 * X 2 0,
  X 0 1 * X 1 1 * X 2 0 + X 0 1 * X 1 0 * X 2 1 + X 0 0 * X 1 1 * X 2 1,
  X 0 1 * X 1 1 * X 2 2 + X 0 1 * X 1 2 * X 2 1 + X 0 2 * X 1 1 * X 2 1,
  X 0 2 * X 1 2 * X 2 0 + X 0 2 * X 1 0 * X 2 2 + X 0 0 * X 1 2 * X 2 2,
  X 0 2 * X 1 2 * X 2 1 + X 0 2 * X 1 1 * X 2 2 + X 0 1 * X 1 2 * X 2 2,
  X 0 0 * X 1 1 * X 2 2 + X 0 0 * X 1 2 * X 2 1 + X 0 1 * X 1 0 * X 2 2 + X 0 1 * X 1 2 * X 2 0 + X 0 2 * X 1 0 * X 2 1 + X 0 2 * X 1 1 * X 2 0]

def cw : Fin 10 → ℝ := ![6, 6, 6, 2, 2, 2, 2, 2, 2, 1]

/-- the monomials -/
def cmon (x : Fin 3 → ℝ) : Fin 10 → ℝ := ![x 0 ^ 3, x 1 ^ 3, x 2 ^ 3, x 0 ^ 2 * x 1, x 0 ^ 2 * x 2,
  x 1 ^ 2 * x 0, x 1 ^ 2 * x 2, x 2 ^ 2 * x 0, x 2 ^ 2 * x 1, x 0 * x 1 * x 2]

theorem perm3_pair (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    perm3 (X * Yᵀ) = ∑ i, cw i * (cf X i * cf Y i) := by
  simp only [perm3, Matrix.mul_apply, Matrix.transpose_apply, cw, cf, Fin.sum_univ_succ]
  simp
  ring

theorem cprod_eval (X : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    (X.mulVec x) 0 * (X.mulVec x) 1 * (X.mulVec x) 2 = ∑ i, cf X i * cmon x i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, cf, cmon, Fin.sum_univ_succ]
  simp
  ring

theorem perm3_sq_sum (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    perm3 (X * Xᵀ) + perm3 (Y * Yᵀ) + 2 * perm3 (X * Yᵀ)
      = ∑ i, cw i * (cf X i + cf Y i) ^ 2 := by
  rw [perm3_pair, perm3_pair, perm3_pair, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem cw_pos (i : Fin 10) : 0 < cw i := by
  fin_cases i <;> simp [cw] <;> norm_num

theorem perm3_sq_sum_nonneg (X Y : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ perm3 (X * Xᵀ) + perm3 (Y * Yᵀ) + 2 * perm3 (X * Yᵀ) := by
  rw [perm3_sq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (cw_pos i).le (sq_nonneg _)

theorem cf_add_eq_zero (X Y : Matrix (Fin 3) (Fin 3) ℝ)
    (h : perm3 (X * Xᵀ) + perm3 (Y * Yᵀ) + 2 * perm3 (X * Yᵀ) = 0) (i : Fin 10) :
    cf X i + cf Y i = 0 := by
  rw [perm3_sq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (cw_pos i).le (sq_nonneg
    (cf X i + cf Y i)))).1 h i (Finset.mem_univ i)
  have h2 := (mul_eq_zero.1 this).resolve_left (cw_pos i).ne'
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h2


noncomputable def pmax (κ : ℝ) : ℝ := (2 + 3 * κ ^ 2 + 4 * κ ^ 3) / 9

theorem perm3_scalar_rank1 (κ c : ℝ) (u : Fin 3 → ℝ) :
    perm3 (κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + c • Matrix.vecMulVec u u)
      = κ ^ 3 + κ ^ 2 * c * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2)
        + 2 * κ * c ^ 2 * (u 0 ^ 2 * u 1 ^ 2 + u 0 ^ 2 * u 2 ^ 2 + u 1 ^ 2 * u 2 ^ 2)
        + 6 * c ^ 3 * (u 0 ^ 2 * u 1 ^ 2 * u 2 ^ 2) := by
  simp [perm3, Matrix.one_apply, Matrix.vecMulVec_apply]
  ring

theorem amgm3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
    27 * (a * b * c) ≤ 1 := by
  have : (a + b + c) ^ 3 - 27 * (a * b * c) = (a + b + c) / 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)
      + 3 * (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) := by ring
  rw [h] at this
  nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (c - a)),
    mul_nonneg hc (sq_nonneg (a - b)), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem amgm3_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1)
    (he : 27 * (a * b * c) = 1) : a = 1 / 3 ∧ b = 1 / 3 ∧ c = 1 / 3 := by
  have : (a + b + c) ^ 3 - 27 * (a * b * c) = (a + b + c) / 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2)
      + 3 * (a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2) := by ring
  rw [h, he] at this
  have h1 := mul_nonneg ha (sq_nonneg (b - c))
  have h2 := mul_nonneg hb (sq_nonneg (c - a))
  have h3 := mul_nonneg hc (sq_nonneg (a - b))
  have hs : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have e1 : a - b = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have e2 : b - c = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Maclaurin: on the simplex. -/
theorem e2_le {a b c : ℝ} (h : a + b + c = 1) : a * b + a * c + b * c ≤ 1 / 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem perm_rank1_le {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (u : Fin 3 → ℝ)
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) :
    perm3 (κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ) • Matrix.vecMulVec u u) ≤ pmax κ := by
  rw [perm3_scalar_rank1, hu]
  have e2 := e2_le (a := u 0 ^ 2) (b := u 1 ^ 2) (c := u 2 ^ 2) hu
  have e3 := amgm3 (sq_nonneg (u 0)) (sq_nonneg (u 1)) (sq_nonneg (u 2)) hu
  unfold pmax
  have a1 : 0 ≤ 2 * κ * (1 - κ) ^ 2 := by have : 0 ≤ 1 - κ := by linarith
                                          positivity
  have a2 : 0 ≤ 6 * (1 - κ) ^ 3 := by have : 0 ≤ 1 - κ := by linarith
                                      positivity
  nlinarith [mul_le_mul_of_nonneg_left e2 a1, mul_le_mul_of_nonneg_left (show u 0 ^ 2 * u 1 ^ 2 * u 2 ^ 2 ≤ 1/27 by nlinarith) a2]

theorem perm_rank1_eq {κ : ℝ} (h0 : 0 < κ) (h1 : κ < 1) (u : Fin 3 → ℝ)
    (hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1)
    (heq : pmax κ ≤ perm3 (κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ) • Matrix.vecMulVec u u)) :
    ∀ i, u i ^ 2 = 1 / 3 := by
  rw [perm3_scalar_rank1, hu] at heq
  have e2 := e2_le (a := u 0 ^ 2) (b := u 1 ^ 2) (c := u 2 ^ 2) hu
  have e3 := amgm3 (sq_nonneg (u 0)) (sq_nonneg (u 1)) (sq_nonneg (u 2)) hu
  unfold pmax at heq
  have hk : 0 < 1 - κ := by linarith
  have a1 : 0 < 2 * κ * (1 - κ) ^ 2 := by positivity
  have a2 : 0 ≤ 6 * (1 - κ) ^ 3 := by positivity
  have h3 := mul_le_mul_of_nonneg_left (show u 0 ^ 2 * u 1 ^ 2 * u 2 ^ 2 ≤ 1/27 by nlinarith) a2
  have he2 : u 0 ^ 2 * u 1 ^ 2 + u 0 ^ 2 * u 2 ^ 2 + u 1 ^ 2 * u 2 ^ 2 = 1 / 3 := by
    by_contra hne
    have hlt : u 0 ^ 2 * u 1 ^ 2 + u 0 ^ 2 * u 2 ^ 2 + u 1 ^ 2 * u 2 ^ 2 < 1 / 3 := lt_of_le_of_ne e2 hne
    nlinarith [mul_lt_mul_of_pos_left hlt a1]
  have hsq : (u 0 ^ 2 - u 1 ^ 2) ^ 2 + (u 1 ^ 2 - u 2 ^ 2) ^ 2 + (u 2 ^ 2 - u 0 ^ 2) ^ 2 = 0 := by
    nlinarith
  have q1 : u 0 ^ 2 - u 1 ^ 2 = 0 := by nlinarith [sq_nonneg (u 0 ^ 2 - u 1 ^ 2), sq_nonneg (u 1 ^ 2 - u 2 ^ 2), sq_nonneg (u 2 ^ 2 - u 0 ^ 2)]
  have q2 : u 1 ^ 2 - u 2 ^ 2 = 0 := by nlinarith [sq_nonneg (u 0 ^ 2 - u 1 ^ 2), sq_nonneg (u 1 ^ 2 - u 2 ^ 2), sq_nonneg (u 2 ^ 2 - u 0 ^ 2)]
  intro i
  fin_cases i <;> simp <;> linarith


def IsSignedCyclic (O : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ (k : Fin 3) (σ : Fin 3 → ℝ), (∀ j, σ j = 1 ∨ σ j = -1) ∧ σ 0 * σ 1 * σ 2 = -1 ∧
    ∀ i j, O i j = if i = j + k then σ j else 0

theorem lin3_core (a0 a1 a2 b0 b1 b2 : ℝ) (E2 : b0 * b1 * b2 = 0)
    (c1 : a0 * a1 * b2 + a0 * a2 * b1 + a1 * a2 * b0 = 0)
    (c2 : a0 * b1 * b2 + a1 * b0 * b2 + a2 * b0 * b1 = 0) (h : a0 = 0) :
    (a0 = 0 ∧ b0 = 0) ∨ (a1 = 0 ∧ b1 = 0) ∨ (a2 = 0 ∧ b2 = 0) := by
  subst h
  by_cases hb0 : b0 = 0
  · exact Or.inl ⟨rfl, hb0⟩
  have c1' : a1 * a2 = 0 := by
    have : a1 * a2 * b0 = 0 := by linear_combination c1
    exact (mul_eq_zero.1 this).resolve_right hb0
  rcases mul_eq_zero.1 c1' with ha1 | ha2
  · subst ha1
    have : a2 * b1 = 0 := by
      have : b0 * (a2 * b1) = 0 := by linear_combination c2
      exact (mul_eq_zero.1 this).resolve_left hb0
    rcases mul_eq_zero.1 this with ha2 | hb1
    · subst ha2
      have : b1 * b2 = 0 := by
        have : b0 * (b1 * b2) = 0 := by linear_combination E2
        exact (mul_eq_zero.1 this).resolve_left hb0
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl ⟨rfl, hb1⟩)
  · subst ha2
    have : a1 * b2 = 0 := by
      have : b0 * (a1 * b2) = 0 := by linear_combination c2
      exact (mul_eq_zero.1 this).resolve_left hb0
    rcases mul_eq_zero.1 this with ha1 | hb2
    · subst ha1
      have : b1 * b2 = 0 := by
        have : b0 * (b1 * b2) = 0 := by linear_combination E2
        exact (mul_eq_zero.1 this).resolve_left hb0
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, hb2⟩)

theorem lin3_zero (a b : Fin 3 → ℝ)
    (h : ∀ p q : ℝ, (a 0 * p + b 0 * q) * (a 1 * p + b 1 * q) * (a 2 * p + b 2 * q) = 0) :
    ∃ i, a i = 0 ∧ b i = 0 := by
  have E1 := h 1 0
  have E2 := h 0 1
  have E3 := h 1 1
  have E4 := h 1 (-1)
  simp only [mul_one, mul_zero, add_zero, zero_add, mul_neg, one_mul, zero_mul] at E1 E2 E3 E4
  have c1 : a 0 * a 1 * b 2 + a 0 * a 2 * b 1 + a 1 * a 2 * b 0 = 0 := by
    linear_combination (E3 - E4) / 2 - E2
  have c2 : a 0 * b 1 * b 2 + a 1 * b 0 * b 2 + a 2 * b 0 * b 1 = 0 := by
    linear_combination (E3 + E4) / 2 - E1
  rcases mul_eq_zero.1 E1 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases lin3_core (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) E2 c1 c2 h2 with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
      · exact ⟨0, x, y⟩
      · exact ⟨1, x, y⟩
      · exact ⟨2, x, y⟩
    · rcases lin3_core (a 1) (a 0) (a 2) (b 1) (b 0) (b 2) (by linear_combination E2)
        (by linear_combination c1) (by linear_combination c2) h2 with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
      · exact ⟨1, x, y⟩
      · exact ⟨0, x, y⟩
      · exact ⟨2, x, y⟩
  · rcases lin3_core (a 2) (a 0) (a 1) (b 2) (b 0) (b 1) (by linear_combination E2)
        (by linear_combination c1) (by linear_combination c2) h1 with ⟨x, y⟩ | ⟨x, y⟩ | ⟨x, y⟩
    · exact ⟨2, x, y⟩
    · exact ⟨0, x, y⟩
    · exact ⟨1, x, y⟩


theorem rows_norm (O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O * Oᵀ = 1) (i : Fin 3) :
    O i 0 ^ 2 + O i 1 ^ 2 + O i 2 ^ 2 = 1 := by
  have := congrFun (congrFun hO i) i
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at this
  nlinarith [this]

theorem cprod_plane (O : Matrix (Fin 3) (Fin 3) ℝ)
    (hcub : ∀ y : Fin 3 → ℝ, (O.mulVec y) 0 * (O.mulVec y) 1 * (O.mulVec y) 2 = -(y 0 * y 1 * y 2)) :
    (∃ i, O i 1 = 0 ∧ O i 2 = 0) ∧ (∃ i, O i 0 = 0 ∧ O i 2 = 0) ∧ (∃ i, O i 0 = 0 ∧ O i 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · refine lin3_zero (fun i => O i 1) (fun i => O i 2) fun p q => ?_
    have := hcub ![0, p, q]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
      zero_mul, neg_zero, zero_add] at this
    linear_combination this
  · refine lin3_zero (fun i => O i 0) (fun i => O i 2) fun p q => ?_
    have := hcub ![p, 0, q]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
      zero_mul, neg_zero, add_zero, zero_add] at this
    linear_combination this
  · refine lin3_zero (fun i => O i 0) (fun i => O i 1) fun p q => ?_
    have := hcub ![p, q, 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
      zero_mul, neg_zero, add_zero] at this
    linear_combination this


theorem pm1 {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

section shapes
variable (O : Matrix (Fin 3) (Fin 3) ℝ)

theorem shape_k0 (n0 : O 0 0 ^ 2 + O 0 1 ^ 2 + O 0 2 ^ 2 = 1) (n1 : O 1 0 ^ 2 + O 1 1 ^ 2 + O 1 2 ^ 2 = 1)
    (n2 : O 2 0 ^ 2 + O 2 1 ^ 2 + O 2 2 ^ 2 = 1)
    (hc1 : (O 0 0 + O 0 1 + O 0 2) * (O 1 0 + O 1 1 + O 1 2) * (O 2 0 + O 2 1 + O 2 2) = -1)
    (h01 : O 0 1 = 0) (h02 : O 0 2 = 0) (h10 : O 1 0 = 0) (h12 : O 1 2 = 0) (h20 : O 2 0 = 0)
    (h21 : O 2 1 = 0) : IsSignedCyclic O := by
  rw [h01, h02] at n0; rw [h10, h12] at n1; rw [h20, h21] at n2
  rw [h01, h02, h10, h12, h20, h21] at hc1
  refine ⟨0, ![O 0 0, O 1 1, O 2 2], ?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact pm1 (by simpa using n0)
    · exact pm1 (by simpa using n1)
    · exact pm1 (by simpa using n2)
  · simpa using (by linarith : O 0 0 * O 1 1 * O 2 2 = -1)
  · intro i j; fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]

theorem shape_k1 (n0 : O 0 0 ^ 2 + O 0 1 ^ 2 + O 0 2 ^ 2 = 1) (n1 : O 1 0 ^ 2 + O 1 1 ^ 2 + O 1 2 ^ 2 = 1)
    (n2 : O 2 0 ^ 2 + O 2 1 ^ 2 + O 2 2 ^ 2 = 1)
    (hc1 : (O 0 0 + O 0 1 + O 0 2) * (O 1 0 + O 1 1 + O 1 2) * (O 2 0 + O 2 1 + O 2 2) = -1)
    (h01 : O 1 1 = 0) (h02 : O 1 2 = 0) (h10 : O 2 0 = 0) (h12 : O 2 2 = 0) (h20 : O 0 0 = 0)
    (h21 : O 0 1 = 0) : IsSignedCyclic O := by
  rw [h20, h21] at n0; rw [h01, h02] at n1; rw [h10, h12] at n2
  rw [h01, h02, h10, h12, h20, h21] at hc1
  refine ⟨1, ![O 1 0, O 2 1, O 0 2], ?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact pm1 (by simpa using n1)
    · exact pm1 (by simpa using n2)
    · exact pm1 (by simpa using n0)
  · simpa using (by linarith : O 1 0 * O 2 1 * O 0 2 = -1)
  · intro i j; fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]

theorem shape_k2 (n0 : O 0 0 ^ 2 + O 0 1 ^ 2 + O 0 2 ^ 2 = 1) (n1 : O 1 0 ^ 2 + O 1 1 ^ 2 + O 1 2 ^ 2 = 1)
    (n2 : O 2 0 ^ 2 + O 2 1 ^ 2 + O 2 2 ^ 2 = 1)
    (hc1 : (O 0 0 + O 0 1 + O 0 2) * (O 1 0 + O 1 1 + O 1 2) * (O 2 0 + O 2 1 + O 2 2) = -1)
    (h01 : O 2 1 = 0) (h02 : O 2 2 = 0) (h10 : O 0 0 = 0) (h12 : O 0 2 = 0) (h20 : O 1 0 = 0)
    (h21 : O 1 1 = 0) : IsSignedCyclic O := by
  rw [h10, h12] at n0; rw [h20, h21] at n1; rw [h01, h02] at n2
  rw [h01, h02, h10, h12, h20, h21] at hc1
  refine ⟨2, ![O 2 0, O 0 1, O 1 2], ?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact pm1 (by simpa using n2)
    · exact pm1 (by simpa using n0)
    · exact pm1 (by simpa using n1)
  · simpa using (by linarith : O 2 0 * O 0 1 * O 1 2 = -1)
  · intro i j; fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]

end shapes

theorem signedCyclic_of_cubic (O : Matrix (Fin 3) (Fin 3) ℝ) (hO : O * Oᵀ = 1) (hdet : O.det = -1)
    (hcub : ∀ y : Fin 3 → ℝ, (O.mulVec y) 0 * (O.mulVec y) 1 * (O.mulVec y) 2 = -(y 0 * y 1 * y 2)) :
    IsSignedCyclic O := by
  obtain ⟨⟨i0, h01, h02⟩, ⟨i1, h10, h12⟩, ⟨i2, h20, h21⟩⟩ := cprod_plane O hcub
  have n0 := rows_norm O hO 0
  have n1 := rows_norm O hO 1
  have n2 := rows_norm O hO 2
  have hc1 := hcub ![1, 1, 1]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one] at hc1
  rw [Matrix.det_fin_three] at hdet
  have c3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases c3 i0 with rfl | rfl | rfl <;> rcases c3 i1 with rfl | rfl | rfl <;>
    rcases c3 i2 with rfl | rfl | rfl <;>
    first
    | exact shape_k0 O n0 n1 n2 (by linarith) h01 h02 h10 h12 h20 h21
    | exact shape_k1 O n0 n1 n2 (by linarith) h01 h02 h10 h12 h20 h21
    | exact shape_k2 O n0 n1 n2 (by linarith) h01 h02 h10 h12 h20 h21
    | (exfalso; simp [h01, h02, h10, h12, h20, h21] at n0 n1 n2; done)
    | (exfalso; simp [h01, h02, h10, h12, h20, h21] at hc1 hdet; linarith)


theorem sc_mul (a c a' c' : ℝ) (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + c • Matrix.vecMulVec u u) *
      (a' • (1 : Matrix (Fin 3) (Fin 3) ℝ) + c' • Matrix.vecMulVec u u)
      = (a * a') • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (a * c' + a' * c + c * c') • Matrix.vecMulVec u u := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hu, one_smul, smul_smul, smul_add]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem sc_transpose (a c : ℝ) (u : Fin 3 → ℝ) :
    (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + c • Matrix.vecMulVec u u)ᵀ
      = a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + c • Matrix.vecMulVec u u := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.one_apply, eq_comm, mul_comm]


end FormalResearch.FourQubitEntropy

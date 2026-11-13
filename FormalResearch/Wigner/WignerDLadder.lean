module

public import FormalResearch.Wigner.WignerDODE
public import FormalResearch.Special.JacobiRec

/-!
# Rank ladders and rank recurrence for the Wigner `d`-function

Paper: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`: `eq:dranklower`, `eq:drankupper` (rank ladders)
and the `t = 0` case of `eq:3jrank` (rank recurrence of `d`).  Standard references: Varshalovich
§4.8 (recursion relations), Edmonds 4.1; contiguous Jacobi relations (Szegő §4.5, DLMF §18.9(iii)).

**Dictionary.**  Paper `d^f_{nm}(x)`, `x = cos θ`, is `wignerSmallD f n m θ` (`n = m'` row index,
`m` column index; everything below is symmetric in `(m, m')`), `' = d/dx`.  Since
`(1-x²) d/dx = - sin θ · d/dθ`, the paper's `(1-x²) d_f'` is `-(sin θ · deriv d θ)`, and
`R_k = √((k²-m²)(k²-n²))` is `wigR k n m`.  The three relations hold for **all** rational
`f, m', m` and all real `θ` (zero-extended `d`, so no admissibility hypothesis; `R_f = 0` exactly
where the rank `f-1` or `f+1` function is not defined):

* `wignerSmallD_rank_lower` (`eq:dranklower`):
  `R_f d^{f-1} = -f · sin θ d^f'(θ) + (f² cos θ - m m') d^f`, i.e. `f(1-x²) d_f' + (f²x - mn) d_f`;
* `wignerSmallD_rank_upper` (`eq:drankupper`):
  `R_{f+1} d^{f+1} = ((f+1)² cos θ - m m') d^f + (f+1) sin θ d^f'(θ)`, i.e.
  `((f+1)²x - mn) d_f - (f+1)(1-x²) d_f'`;
* `wignerSmallD_rank_rec` (`eq:3jrank` at `t = 0`, Varshalovich 4.8.1):
  `(2f+1)(f(f+1) cos θ - m m') d^f = (f+1) R_f d^{f-1} + f R_{f+1} d^{f+1}`.

(`eq:3jrank` has `x` for `cos θ` and `M σ` for `m' m`; the `√(1 - L²h²)` factors are 1 at `t = 0`.)
The recurrence is the `(f+1) ·` lower `+ f ·` upper combination, in which `d'` cancels.

**Route.**  In the chamber `m' ≥ m`, `m' + m ≥ 0` (`μ = m'-m`, `ν = m'+m`, `k = j-m'`) the ladders
are the Jacobi contiguous relations `jacobi_ladder_lower`, `jacobi_ladder_upper` (proved here from
the coefficient recurrence of `jacobi` and `jacobi_three_term`, for `α + β + 1 > 0`) transported
through `wigG_deriv` (`FormalResearch.Wigner.WignerDODE`) and the normalisation identities
`wigR_mul_wigNorm_lower/upper`; the other chambers follow from `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'} =
d^j_{-m,-m'}` (`chamber_reduce`).
-/

@[expose] public section

namespace FormalResearch.Wigner

open Polynomial FormalResearch.Special

/-! ### Contiguous relations for Jacobi polynomials -/

lemma jacRecCoeff_of_le {α β : ℝ} {m ℓ : ℕ} (h : ℓ ≤ m) :
    jacRecCoeff α β m ℓ = jacobiCoeff α β m ℓ := by
  simp only [jacRecCoeff, h, ↓reduceIte]

lemma jacRecCoeff_of_gt {α β : ℝ} {m ℓ : ℕ} (h : ¬ ℓ ≤ m) : jacRecCoeff α β m ℓ = 0 := by
  simp only [jacRecCoeff, h, ↓reduceIte]

lemma poch_shift (ℓ : ℕ) (x : ℝ) :
    (ascPochhammer ℝ ℓ).eval (x + 1) * x = (ascPochhammer ℝ ℓ).eval x * (x + ℓ) := by
  have h1 := poch_succ_left_eval ℓ x
  have h2 := ascPochhammer_succ_eval ℓ x
  rw [h1] at h2
  linarith [mul_comm x ((ascPochhammer ℝ ℓ).eval (x + 1))]

lemma jacLow_rel (α β : ℝ) (n ℓ : ℕ) (h : ℓ ≤ n) :
    ((n : ℝ) + α + β + 1) * ((n : ℝ) + 1 - ℓ) * jacobiCoeff α β (n + 1) ℓ =
      ((n : ℝ) + α + β + 1 + ℓ) * ((n : ℝ) + α + 1) * jacobiCoeff α β n ℓ := by
  obtain ⟨d, rfl⟩ : ∃ d, n = ℓ + d := ⟨n - ℓ, by omega⟩
  have e1 : ℓ + d + 1 - ℓ = d + 1 := by omega
  have e2 : ℓ + d - ℓ = d := by omega
  have hs := poch_shift ℓ (((ℓ + d : ℕ) : ℝ) + α + β + 1)
  unfold jacobiCoeff
  rw [e1, e2, jacRec_poch_r (α + ℓ + 1) d, Nat.factorial_succ d]
  have e3 : ((ℓ + d + 1 : ℕ) : ℝ) + α + β + 1 = (((ℓ + d : ℕ) : ℝ) + α + β + 1) + 1 := by
    push_cast; ring
  rw [e3]
  have e4 : α + ℓ + 1 + d = ((ℓ + d : ℕ) : ℝ) + α + 1 := by push_cast; ring
  rw [e4]
  generalize (ascPochhammer ℝ ℓ).eval ((((ℓ + d : ℕ) : ℝ) + α + β + 1) + 1) = A at hs ⊢
  generalize (ascPochhammer ℝ ℓ).eval (((ℓ + d : ℕ) : ℝ) + α + β + 1) = A' at hs ⊢
  generalize (ascPochhammer ℝ d).eval (α + ℓ + 1) = B
  have hf : (0:ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos ℓ
  have hg : (0:ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  push_cast at hs ⊢
  field_simp
  linear_combination ((d:ℝ) + 1) * B * ((ℓ:ℝ) + d + α + 1) * hs


lemma jacLow_coeff (α β : ℝ) (hαβ : 0 < α + β + 1) (n j : ℕ) :
    (2 * (n : ℝ) + 2 + α + β) * ((n : ℝ) + 1 - j) * jacRecCoeff α β (n + 1) j
      + jacRecCoeff α β (n + 1) (j + 1) *
          ((2 * (n : ℝ) + 2 + α + β) * ((n : ℝ) - 1 - 2 * j) - ((n : ℝ) + 1) * (α - β))
      = 2 * ((n : ℝ) + 1 + α) * ((n : ℝ) + 1 + β) * jacRecCoeff α β n (j + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases h1 : j + 1 ≤ n
  · have hc0 : jacRecCoeff α β (n + 1) j = jacobiCoeff α β (n + 1) j := by
      rw [jacRecCoeff_of_le (by omega)]
    have hc1 : jacRecCoeff α β (n + 1) (j + 1) = jacobiCoeff α β (n + 1) (j + 1) := by
      rw [jacRecCoeff_of_le (by omega)]
    have hb1 : jacRecCoeff α β n (j + 1) = jacobiCoeff α β n (j + 1) := by
      rw [jacRecCoeff_of_le h1]
    rw [hc0, hc1, hb1]
    have hi := jacobiCoeff_succ α β (n + 1) j (by omega)
    have hii := jacLow_rel α β n (j + 1) h1
    push_cast at hi hii
    generalize jacobiCoeff α β (n + 1) j = c0 at hi ⊢
    generalize jacobiCoeff α β (n + 1) (j + 1) = c1 at hi hii ⊢
    generalize jacobiCoeff α β n (j + 1) = bb at hii ⊢
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast h1
    have hD1 : 0 < (n : ℝ) + (j + 1) + α + β + 1 := by linarith
    have hD2 : 0 < ((n : ℝ) + α + β + 1) * ((n : ℝ) + 1 - (j + 1)) := by
      apply mul_pos (by linarith); linarith
    refine mul_left_cancel₀ (mul_pos hD1 hD2).ne' ?_
    generalize (n : ℝ) = N at *
    generalize (j : ℝ) = J at *
    linear_combination (-(2 * N + 2 + α + β) * ((N + α + β + 1) * (N + 1 - (J + 1)))) * hi
      + ((N + (J + 1) + α + β + 1) * ((2 * N + 2 + α + β) * (N - 1 - 2 * J) - (N + 1) * (α - β))
         + 2 * (2 * N + 2 + α + β) * (J + 1) * (α + J + 1)) * hii
  · have hj : n ≤ j := by omega
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · have hc0 : jacRecCoeff α β (n + 1) n = jacobiCoeff α β (n + 1) n := by
        rw [jacRecCoeff_of_le (by omega)]
      have hc1 : jacRecCoeff α β (n + 1) (n + 1) = jacobiCoeff α β (n + 1) (n + 1) := by
        rw [jacRecCoeff_of_le (by omega)]
      have hb1 : jacRecCoeff α β n (n + 1) = 0 := by
        rw [jacRecCoeff_of_gt (by omega)]
      rw [hc0, hc1, hb1]
      have hi := jacobiCoeff_succ α β (n + 1) n (by omega)
      push_cast at hi
      generalize jacobiCoeff α β (n + 1) n = c0 at hi ⊢
      generalize jacobiCoeff α β (n + 1) (n + 1) = c1 at hi ⊢
      generalize (n : ℝ) = N at *
      linear_combination (-1 : ℝ) * hi
    · have hc0 : jacRecCoeff α β (n + 1) j = 0 ∨ (n : ℝ) + 1 - j = 0 := by
        rcases Nat.eq_or_lt_of_le (show n + 1 ≤ j by omega) with h | h
        · right; rw [← h]; push_cast; ring
        · left; rw [jacRecCoeff_of_gt (by omega)]
      have hc1 : jacRecCoeff α β (n + 1) (j + 1) = 0 := by
        rw [jacRecCoeff_of_gt (by omega)]
      have hb1 : jacRecCoeff α β n (j + 1) = 0 := by
        rw [jacRecCoeff_of_gt (by omega)]
      rw [hc1, hb1]
      rcases hc0 with h | h <;> simp [h]

lemma jacLow_zero (α β : ℝ) (hαβ : 0 < α + β + 1) (n : ℕ) :
    ((n : ℝ) + 1) * (α - β - (2 * (n : ℝ) + 2 + α + β)) * jacRecCoeff α β (n + 1) 0
      + 2 * ((n : ℝ) + 1 + α) * ((n : ℝ) + 1 + β) * jacRecCoeff α β n 0 = 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc0 : jacRecCoeff α β (n + 1) 0 = jacobiCoeff α β (n + 1) 0 := by
    rw [jacRecCoeff_of_le (by omega)]
  have hb0 : jacRecCoeff α β n 0 = jacobiCoeff α β n 0 := by
    rw [jacRecCoeff_of_le (by omega)]
  rw [hc0, hb0]
  have hii := jacLow_rel α β n 0 (by omega)
  push_cast at hii
  generalize jacobiCoeff α β (n + 1) 0 = c0 at hii ⊢
  generalize jacobiCoeff α β n 0 = bb at hii ⊢
  have hT : 0 < (n : ℝ) + α + β + 1 := by linarith
  have h2 : ((n : ℝ) + 1) * c0 = ((n : ℝ) + α + 1) * bb := by
    refine mul_left_cancel₀ hT.ne' ?_
    linear_combination hii
  generalize (n : ℝ) = N at *
  linear_combination (α - β - (2 * N + 2 + α + β)) * h2

/-- Coefficient-sum bookkeeping for the lower ladder, with abstract coefficient sequences. -/
lemma jacLow_assemble (κ A K : ℝ) (n : ℕ) (c b : ℕ → ℝ) (u : ℝ)
    (h0 : ((n : ℝ) + 1) * (A - κ) * c 0 + 2 * K * b 0 = 0)
    (hS : ∀ j, j < n + 2 → κ * ((n : ℝ) + 1 - j) * c j
      + c (j + 1) * (κ * ((n : ℝ) - 1 - 2 * j) - ((n : ℝ) + 1) * A) = 2 * K * b (j + 1))
    (htop : c (n + 2) = 0) :
    -κ * (u + 2) * ∑ ℓ ∈ Finset.range (n + 3), (ℓ : ℝ) * c ℓ * u ^ ℓ
      = ((n : ℝ) + 1) * (A - κ * (u + 1)) * ∑ ℓ ∈ Finset.range (n + 3), c ℓ * u ^ ℓ
        + 2 * K * ∑ ℓ ∈ Finset.range (n + 3), b ℓ * u ^ ℓ := by
  have hP : ∀ f : ℕ → ℝ, ∑ ℓ ∈ Finset.range (n + 3), f ℓ
      = ∑ j ∈ Finset.range (n + 2), f (j + 1) + f 0 := by
    intro f
    rw [Finset.sum_range_succ' _ (n + 2)]
  have hu1 : u * ∑ ℓ ∈ Finset.range (n + 3), (ℓ : ℝ) * c ℓ * u ^ ℓ
      = ∑ j ∈ Finset.range (n + 2), (j : ℝ) * c j * u ^ (j + 1) := by
    rw [Finset.sum_range_succ, htop]
    simp only [mul_zero, zero_mul, add_zero]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hu0 : u * ∑ ℓ ∈ Finset.range (n + 3), c ℓ * u ^ ℓ
      = ∑ j ∈ Finset.range (n + 2), c j * u ^ (j + 1) := by
    rw [Finset.sum_range_succ, htop]
    simp only [zero_mul, add_zero]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hkey : ∑ j ∈ Finset.range (n + 2),
      (κ * ((n : ℝ) + 1) * (c j * u ^ (j + 1)) - κ * ((j : ℝ) * c j * u ^ (j + 1))
        + (κ * ((n : ℝ) - 1) - ((n : ℝ) + 1) * A) * (c (j + 1) * u ^ (j + 1))
        - 2 * κ * ((j : ℝ) * c (j + 1) * u ^ (j + 1)) - 2 * K * (b (j + 1) * u ^ (j + 1))) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have := hS j (Finset.mem_range.1 hj)
    linear_combination u ^ (j + 1) * this
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hkey
  have hS1 : ∑ ℓ ∈ Finset.range (n + 3), (ℓ : ℝ) * c ℓ * u ^ ℓ
      = ∑ j ∈ Finset.range (n + 2), c (j + 1) * u ^ (j + 1)
        + ∑ j ∈ Finset.range (n + 2), (j : ℝ) * c (j + 1) * u ^ (j + 1) := by
    rw [hP, ← Finset.sum_add_distrib]
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hS0 := hP (fun ℓ => c ℓ * u ^ ℓ)
  have hSb := hP (fun ℓ => b ℓ * u ^ ℓ)
  simp only [pow_zero, mul_one] at hS0 hSb
  linear_combination (-κ) * hu1 + ((n : ℝ) + 1) * κ * hu0 - 2 * κ * hS1
    - ((n : ℝ) + 1) * (A - κ) * hS0 - 2 * K * hSb + hkey - h0

/-- `(x-1) P_m'(x)` as a sum over any range `N ≥ m+1`. -/
lemma jacobi_xsub_deriv_eval (α β : ℝ) (m N : ℕ) (h : m + 1 ≤ N) (x : ℝ) :
    (x - 1) * (derivative (jacobi α β m)).eval x =
      ∑ ℓ ∈ Finset.range N, (ℓ : ℝ) * jacRecCoeff α β m ℓ * (x - 1) ^ ℓ := by
  have h1 : (x - 1) * (derivative (jacobi α β m)).eval x =
      ∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * jacRecCoeff α β m ℓ * (x - 1) ^ ℓ := by
    unfold jacobi
    simp only [derivative_sum, derivative_C_mul, derivative_xsub_pow, eval_finsetSum, eval_mul,
      eval_C, eval_pow, eval_sub, eval_X, eval_one, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    have hℓ' : ℓ ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    rw [jacRecCoeff_of_le hℓ']
    rcases ℓ with _ | ℓ
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
  rw [h1]
  refine Finset.sum_subset (Finset.range_mono h) (fun ℓ hℓ hn => ?_)
  have : ¬ ℓ ≤ m := fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  simp [jacRecCoeff, this]

/-- **Lower contiguous relation for Jacobi polynomials** (a standard contiguous relation, cf. Szegő §4.5, DLMF §18.9(iii)), index `n+1`, for `α + β + 1 > 0`:
`(2n+2+α+β)(1-x²) P_{n+1}' = (n+1)(α-β-(2n+2+α+β)x) P_{n+1} + 2(n+1+α)(n+1+β) P_n`. -/
theorem jacobi_ladder_lower (α β : ℝ) (hαβ : 0 < α + β + 1) (n : ℕ) :
    C (2 * (n : ℝ) + 2 + α + β) * ((1 - X ^ 2) * derivative (jacobi α β (n + 1))) =
      C ((n : ℝ) + 1) * (C (α - β) - C (2 * (n : ℝ) + 2 + α + β) * X) * jacobi α β (n + 1)
        + C (2 * ((n : ℝ) + 1 + α) * ((n : ℝ) + 1 + β)) * jacobi α β n := by
  refine Polynomial.funext (fun x => ?_)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X]
  have hd := jacobi_xsub_deriv_eval α β (n + 1) (n + 3) (by omega) x
  rw [jacRec_eval_ext α β (n + 1) (n + 3) (by omega) x, jacRec_eval_ext α β n (n + 3) (by omega) x]
  have key := jacLow_assemble (2 * (n : ℝ) + 2 + α + β) (α - β)
    (((n : ℝ) + 1 + α) * ((n : ℝ) + 1 + β)) n (jacRecCoeff α β (n + 1)) (jacRecCoeff α β n) (x - 1)
    (by have := jacLow_zero α β hαβ n; linear_combination this)
    (fun j _ => by have := jacLow_coeff α β hαβ n j; linear_combination this)
    (by rw [jacRecCoeff_of_gt (by omega)])
  rw [← hd] at key
  have e : (1 - x ^ 2) = -((x - 1) * (x - 1 + 2)) := by ring
  rw [e]
  have e2 : x - 1 + 1 = x := by ring
  rw [e2] at key
  linear_combination key

/-- **Upper contiguous relation for Jacobi polynomials** (a standard contiguous relation, cf. Szegő §4.5, DLMF §18.9(iii)), for `α + β + 1 > 0`:
`(2n+2+α+β)(1-x²) P_n' = (n+α+β+1)(α-β+(2n+2+α+β)x) P_n - 2(n+1)(n+α+β+1) P_{n+1}`.
Derived from `jacobi_ladder_lower` and the three-term recurrence. -/
theorem jacobi_ladder_upper (α β : ℝ) (hαβ : 0 < α + β + 1) (n : ℕ) :
    C (2 * (n : ℝ) + 2 + α + β) * ((1 - X ^ 2) * derivative (jacobi α β n)) =
      C ((n : ℝ) + α + β + 1) * (C (α - β) + C (2 * (n : ℝ) + 2 + α + β) * X) * jacobi α β n
        - C (2 * ((n : ℝ) + 1) * ((n : ℝ) + α + β + 1)) * jacobi α β (n + 1) := by
  refine Polynomial.funext (fun x => ?_)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X]
  rcases n with _ | m
  · rw [jacobi_zero, jacobi_one]
    simp only [eval_mul, eval_C, eval_add, eval_one, eval_X, derivative_one,
      eval_zero, mul_zero, Nat.cast_zero]
    ring
  · have hL := congrArg (Polynomial.eval x) (jacobi_ladder_lower α β hαβ m)
    simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at hL
    have hT := jacRec_three_term_eval α β m x
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hκ : 0 < 2 * (m : ℝ) + 2 + α + β := by linarith
    generalize (jacobi α β m).eval x = p0 at hL hT ⊢
    generalize (jacobi α β (m + 1)).eval x = p1 at hL hT ⊢
    generalize (jacobi α β (m + 2)).eval x = p2 at hL hT ⊢
    generalize (derivative (jacobi α β (m + 1))).eval x = d1 at hL ⊢
    push_cast
    refine mul_left_cancel₀ hκ.ne' ?_
    linear_combination (2 * (m : ℝ) + 4 + α + β) * hL + hT


/-! ### Normalisation identities -/

/-- `R_f = √((f² - m²)(f² - m'²))`, the rank factor of the ladders (paper `R_k`). -/
noncomputable def wigR (j m' m : ℚ) : ℝ :=
  Real.sqrt (((j : ℝ) ^ 2 - (m : ℝ) ^ 2) * ((j : ℝ) ^ 2 - (m' : ℝ) ^ 2))

lemma wigR_symm (j m' m : ℚ) : wigR j m' m = wigR j m m' := by
  unfold wigR; rw [mul_comm]

lemma wigR_neg (j m' m : ℚ) : wigR j (-m) (-m') = wigR j m' m := by
  unfold wigR; push_cast; simp only [neg_sq]; rw [mul_comm]

/-- In the chamber: `R_j = √((k+μ)(k+ν) · k(k+μ+ν))`. -/
lemma wigR_A {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν) (hk : j - m' = k) :
    wigR j m' m =
      Real.sqrt ((((k : ℝ) + μ) * ((k : ℝ) + ν)) * ((k : ℝ) * ((k : ℝ) + μ + ν))) := by
  obtain ⟨e1, e2, e3⟩ := chamberA_real hμ hν hk
  unfold wigR
  congr 1
  rw [e1, e2, e3]; ring

lemma fact_cast_succ (n : ℕ) : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  rw [Nat.factorial_succ]; push_cast; ring

/-- `√((k+μ)(k+ν) k (k+μ+ν)) · N_{k-1} = (k+μ)(k+ν) N_k`, written for `k = k' + 1`. -/
lemma wigR_mul_wigNorm_lower (μ ν k' : ℕ) :
    Real.sqrt ((((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν) *
        (((k' + 1 : ℕ) : ℝ) * (((k' + 1 : ℕ) : ℝ) + μ + ν))) * wigNorm μ ν k' =
      (((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν) * wigNorm μ ν (k' + 1) := by
  unfold wigNorm
  have hZ : 0 ≤ (((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν) := by positivity
  have e : ∀ y : ℝ, (((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν) * Real.sqrt y =
      Real.sqrt (((((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν)) ^ 2 * y) := by
    intro y
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hZ]
  rw [e, ← Real.sqrt_mul (by positivity)]
  congr 1
  have f1 : ((k' + 1).factorial : ℝ) = ((k' : ℝ) + 1) * (k'.factorial : ℝ) := fact_cast_succ k'
  have f2 : ((k' + 1 + μ + ν).factorial : ℝ) =
      ((k' : ℝ) + μ + ν + 1) * ((k' + μ + ν).factorial : ℝ) := by
    rw [show k' + 1 + μ + ν = (k' + μ + ν) + 1 by omega, fact_cast_succ]; push_cast; ring
  have f3 : ((k' + 1 + μ).factorial : ℝ) = ((k' : ℝ) + μ + 1) * ((k' + μ).factorial : ℝ) := by
    rw [show k' + 1 + μ = (k' + μ) + 1 by omega, fact_cast_succ]; push_cast; ring
  have f4 : ((k' + 1 + ν).factorial : ℝ) = ((k' : ℝ) + ν + 1) * ((k' + ν).factorial : ℝ) := by
    rw [show k' + 1 + ν = (k' + ν) + 1 by omega, fact_cast_succ]; push_cast; ring
  rw [f1, f2, f3, f4]
  have h1 : (0 : ℝ) < k'.factorial := by positivity
  have h2 : (0 : ℝ) < (k' + μ + ν).factorial := by positivity
  have h3 : (0 : ℝ) < (k' + μ).factorial := by positivity
  have h4 : (0 : ℝ) < (k' + ν).factorial := by positivity
  push_cast
  field_simp
  ring

/-- `√((k+1+μ)(k+1+ν)(k+1)(k+1+μ+ν)) · N_{k+1} = (k+1)(k+1+μ+ν) N_k`. -/
lemma wigR_mul_wigNorm_upper (μ ν k : ℕ) :
    Real.sqrt ((((k + 1 : ℕ) : ℝ) + μ) * (((k + 1 : ℕ) : ℝ) + ν) *
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν))) * wigNorm μ ν (k + 1) =
      (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν)) * wigNorm μ ν k := by
  have hlow := wigR_mul_wigNorm_lower μ ν k
  set R := Real.sqrt ((((k + 1 : ℕ) : ℝ) + μ) * (((k + 1 : ℕ) : ℝ) + ν) *
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν))) with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R ^ 2 = (((k + 1 : ℕ) : ℝ) + μ) * (((k + 1 : ℕ) : ℝ) + ν) *
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν)) := Real.sq_sqrt (by positivity)
  refine mul_left_cancel₀ hRpos.ne' ?_
  generalize wigNorm μ ν (k + 1) = N1 at hlow ⊢
  generalize wigNorm μ ν k = N0 at hlow ⊢
  generalize (((k + 1 : ℕ) : ℝ) + μ) * (((k + 1 : ℕ) : ℝ) + ν) = Z at hlow hR2 ⊢
  generalize ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν) = W at hlow hR2 ⊢
  linear_combination N1 * hR2 - W * hlow

/-! ### The ladders at the level of `G_P` -/

lemma wigG_half_E (μ ν : ℕ) (P : ℝ[X]) (θ : ℝ) :
    wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν P) θ =
      Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
        (1 / 2 * (((μ : ℝ) * (1 + Real.cos θ) - ν * (1 - Real.cos θ)) * P.eval (Real.cos θ)
          - 2 * (1 - Real.cos θ ^ 2) * (derivative P).eval (Real.cos θ))) := by
  unfold wigG Epoly
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X, eval_ofNat]

/-- Lower ladder for `G_P` (`k = k'+1 ≥ 1`), from `jacobi_ladder_lower`. -/
lemma wigG_lower (μ ν k' : ℕ) (θ : ℝ) :
    (((k' + 1 : ℕ) : ℝ) + μ) * (((k' + 1 : ℕ) : ℝ) + ν) * wigG μ ν (jacobi μ ν k') θ =
      -(((k' + 1 : ℕ) : ℝ) + ((μ : ℝ) + ν) / 2) *
          wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν (jacobi μ ν (k' + 1))) θ +
        ((((k' + 1 : ℕ) : ℝ) + ((μ : ℝ) + ν) / 2) ^ 2 * Real.cos θ -
          ((ν : ℝ) ^ 2 - (μ : ℝ) ^ 2) / 4) * wigG μ ν (jacobi μ ν (k' + 1)) θ := by
  have hL := congrArg (Polynomial.eval (Real.cos θ))
    (jacobi_ladder_lower (μ : ℝ) ν (by positivity) k')
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at hL
  rw [wigG_half_E]
  unfold wigG
  push_cast
  generalize (jacobi (μ : ℝ) ν k').eval (Real.cos θ) = p0 at hL ⊢
  generalize (jacobi (μ : ℝ) ν (k' + 1)).eval (Real.cos θ) = p1 at hL ⊢
  generalize (derivative (jacobi (μ : ℝ) ν (k' + 1))).eval (Real.cos θ) = d1 at hL ⊢
  generalize Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν = W
  linear_combination (-(1 / 2 : ℝ) * W) * hL

/-- `k = 0`: `G_1` is the `k'`-free base case of the lower ladder (the right side vanishes). -/
lemma wigG_lower_zero (μ ν : ℕ) (θ : ℝ) :
    0 = -(((μ : ℝ) + ν) / 2) * wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν (jacobi μ ν 0)) θ +
        ((((μ : ℝ) + ν) / 2) ^ 2 * Real.cos θ - ((ν : ℝ) ^ 2 - (μ : ℝ) ^ 2) / 4) *
          wigG μ ν (jacobi μ ν 0) θ := by
  rw [wigG_half_E, jacobi_zero]
  unfold wigG
  simp only [eval_one, derivative_one, eval_zero]
  ring

/-- Upper ladder for `G_P`, from `jacobi_ladder_upper`. -/
lemma wigG_upper (μ ν k : ℕ) (θ : ℝ) :
    (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + μ + ν)) * wigG μ ν (jacobi μ ν (k + 1)) θ =
      ((((k : ℝ) + ((μ : ℝ) + ν) / 2 + 1) ^ 2 * Real.cos θ - ((ν : ℝ) ^ 2 - (μ : ℝ) ^ 2) / 4) *
          wigG μ ν (jacobi μ ν k) θ +
        ((k : ℝ) + ((μ : ℝ) + ν) / 2 + 1) *
          wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν (jacobi μ ν k)) θ) := by
  have hU := congrArg (Polynomial.eval (Real.cos θ))
    (jacobi_ladder_upper (μ : ℝ) ν (by positivity) k)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at hU
  rw [wigG_half_E]
  unfold wigG
  push_cast
  generalize (jacobi (μ : ℝ) ν k).eval (Real.cos θ) = p0 at hU ⊢
  generalize (jacobi (μ : ℝ) ν (k + 1)).eval (Real.cos θ) = p1 at hU ⊢
  generalize (derivative (jacobi (μ : ℝ) ν k)).eval (Real.cos θ) = d0 at hU ⊢
  generalize Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν = W
  linear_combination ((1 / 2 : ℝ) * W) * hU

/-! ### The ladders for `wignerSmallD` in the chamber `m' ≥ m`, `m' + m ≥ 0` -/

lemma sin_mul_deriv_wignerSmallD_A {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) (θ : ℝ) :
    Real.sin θ * deriv (wignerSmallD j m' m) θ =
      ((-1 : ℝ) ^ μ * wigNorm μ ν k) *
        wigG μ ν (C (1 / 2 : ℝ) * Epoly μ ν (jacobi μ ν k)) θ := by
  rw [wignerSmallD_chamber_A_fun hμ hν hk, deriv_const_mul_field', ← sin_mul_deriv_wigG]
  ring

lemma wignerSmallD_chamber_A_val {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) (θ : ℝ) :
    wignerSmallD j m' m θ = ((-1 : ℝ) ^ μ * wigNorm μ ν k) * wigG μ ν (jacobi μ ν k) θ := by
  rw [wignerSmallD_chamber_A_fun hμ hν hk]

lemma not_isNat_neg_one : ¬ IsNat (-1 : ℚ) := by
  rintro ⟨n, hn⟩
  have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  linarith

lemma isNat_succ_of {x y : ℚ} (h : IsNat x) (hy : y = x + 1) : IsNat y := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [hy, hn]; push_cast; ring⟩

lemma WAdm_of_sub_one {j m' m : ℚ} (h : WAdm (j - 1) m' m) : WAdm j m' m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨isNat_succ_of h1 (by ring), isNat_succ_of h2 (by ring), isNat_succ_of h3 (by ring),
    isNat_succ_of h4 (by ring)⟩

lemma wigR_succ_zero {j m' m : ℚ} (h : WAdm (j + 1) m' m) (hn : ¬ WAdm j m' m) :
    wigR (j + 1) m' m = 0 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  have hcon : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ha0, hb0, hc0, hd0⟩ := hcon
    apply hn
    refine ⟨⟨a - 1, ?_⟩, ⟨b - 1, ?_⟩, ⟨c - 1, ?_⟩, ⟨d - 1, ?_⟩⟩ <;>
      rw [Nat.cast_sub (by omega)] <;> push_cast <;> linarith
  have ha' : (j : ℝ) + 1 + m' = a := by exact_mod_cast ha
  have hb' : (j : ℝ) + 1 - m' = b := by exact_mod_cast hb
  have hc' : (j : ℝ) + 1 + m = c := by exact_mod_cast hc
  have hd' : (j : ℝ) + 1 - m = d := by exact_mod_cast hd
  unfold wigR
  have hprod : (((j + 1 : ℚ) : ℝ) ^ 2 - (m : ℝ) ^ 2) * (((j + 1 : ℚ) : ℝ) ^ 2 - (m' : ℝ) ^ 2) =
      (c : ℝ) * d * (a * b) := by
    rw [← ha', ← hb', ← hc', ← hd']; push_cast; ring
  rw [hprod]
  rcases hcon with h | h | h | h <;> simp [h]

lemma wignerSmallD_deriv_zero {j m' m : ℚ} (h : ¬ WAdm j m' m) (θ : ℝ) :
    deriv (wignerSmallD j m' m) θ = 0 := by
  rw [wignerSmallD_eq_zero_of_not_adm h]; simp

/-- **Lower rank ladder** (`eq:dranklower`) in the chamber `m' ≥ m`, `m' + m ≥ 0`. -/
lemma wignerSmallD_rank_lower_A (j m' m : ℚ) (h1 : 0 ≤ m' - m) (h2 : 0 ≤ m' + m) (θ : ℝ) :
    wigR j m' m * wignerSmallD (j - 1) m' m θ =
      -(j : ℝ) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) +
        ((j : ℝ) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ := by
  by_cases hadm : WAdm j m' m
  · obtain ⟨μ, ν, k, hμ, hν, hk⟩ := adm_chamberA hadm h1 h2
    obtain ⟨e1, e2, e3⟩ := chamberA_real hμ hν hk
    rw [sin_mul_deriv_wignerSmallD_A hμ hν hk, wignerSmallD_chamber_A_val hμ hν hk]
    rcases k with _ | k'
    · have hn : ¬ WAdm (j - 1) m' m := by
        rintro ⟨-, h, -⟩
        apply not_isNat_neg_one
        rwa [show (-1 : ℚ) = j - 1 - m' by simp at hk; linarith]
      rw [wignerSmallD_eq_zero_of_not_adm hn, wigR_A hμ hν hk]
      have := wigG_lower_zero μ ν θ
      simp only [Nat.cast_zero, zero_add, zero_mul, mul_zero, Real.sqrt_zero, Pi.zero_apply] at e3 ⊢
      rw [e1, e2, e3]
      linear_combination ((-1 : ℝ) ^ μ * wigNorm μ ν 0) * this
    · have hk' : j - 1 - m' = k' := by
        have : j - m' = (k' : ℚ) + 1 := by rw [hk]; push_cast; ring
        linarith
      rw [wignerSmallD_chamber_A_val hμ hν hk', wigR_A hμ hν hk]
      have hN := wigR_mul_wigNorm_lower μ ν k'
      have hG := wigG_lower μ ν k' θ
      rw [e1, e2, e3]
      generalize Real.sqrt _ = R at hN ⊢
      linear_combination ((-1 : ℝ) ^ μ * wigG μ ν (jacobi μ ν k') θ) * hN +
        ((-1 : ℝ) ^ μ * wigNorm μ ν (k' + 1)) * hG
  · have h0 := wignerSmallD_eq_zero_of_not_adm hadm
    have hn : ¬ WAdm (j - 1) m' m := fun h => hadm (WAdm_of_sub_one h)
    rw [wignerSmallD_eq_zero_of_not_adm hn, h0]
    simp

/-- **Upper rank ladder** (`eq:drankupper`) in the chamber `m' ≥ m`, `m' + m ≥ 0`. -/
lemma wignerSmallD_rank_upper_A (j m' m : ℚ) (h1 : 0 ≤ m' - m) (h2 : 0 ≤ m' + m) (θ : ℝ) :
    wigR (j + 1) m' m * wignerSmallD (j + 1) m' m θ =
      (((j : ℝ) + 1) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ +
        ((j : ℝ) + 1) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) := by
  by_cases hadm : WAdm j m' m
  · obtain ⟨μ, ν, k, hμ, hν, hk⟩ := adm_chamberA hadm h1 h2
    obtain ⟨e1, e2, e3⟩ := chamberA_real hμ hν hk
    have hk' : j + 1 - m' = ((k + 1 : ℕ) : ℚ) := by rw [Nat.cast_add, Nat.cast_one]; linarith
    rw [sin_mul_deriv_wignerSmallD_A hμ hν hk, wignerSmallD_chamber_A_val hμ hν hk,
      wignerSmallD_chamber_A_val hμ hν hk', wigR_A hμ hν hk']
    have hN := wigR_mul_wigNorm_upper μ ν k
    have hG := wigG_upper μ ν k θ
    rw [e1, e2, e3]
    generalize Real.sqrt _ = R at hN ⊢
    linear_combination ((-1 : ℝ) ^ μ * wigG μ ν (jacobi μ ν (k + 1)) θ) * hN +
      ((-1 : ℝ) ^ μ * wigNorm μ ν k) * hG
  · have h0 := wignerSmallD_eq_zero_of_not_adm hadm
    by_cases hadm' : WAdm (j + 1) m' m
    · rw [wigR_succ_zero hadm' hadm, h0]
      simp
    · rw [wignerSmallD_eq_zero_of_not_adm hadm', h0]
      simp

/-! ### All chambers -/

lemma wignerSmallD_swap_fun (j m' m : ℚ) :
    wignerSmallD j m' m = fun t => sgn (m' - m) * wignerSmallD j m m' t :=
  funext fun t => wignerSmallD_swap j m' m t

lemma wignerSmallD_neg_fun (j m' m : ℚ) : wignerSmallD j m' m = wignerSmallD j (-m) (-m') :=
  funext fun t => (wignerSmallD_neg j m' m t).symm

/-- **Lower rank ladder** (paper `eq:dranklower`): for all rational `f, m', m` and real `θ`,
`R_f d^{f-1}_{m'm}(θ) = -f · sin θ · ∂_θ d^f_{m'm}(θ) + (f² cos θ - m m') d^f_{m'm}(θ)`,
`R_f = √((f²-m²)(f²-m'²))`.  With `x = cos θ` and `(1-x²) ∂_x = -sin θ ∂_θ` this is
`R_f d_{f-1} = f(1-x²) d_f' + (f²x - mn) d_f`. -/
theorem wignerSmallD_rank_lower (j m' m : ℚ) (θ : ℝ) :
    wigR j m' m * wignerSmallD (j - 1) m' m θ =
      -(j : ℝ) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) +
        ((j : ℝ) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ := by
  have key : ∀ m' m : ℚ, ∀ (j : ℚ) (θ : ℝ), wigR j m' m * wignerSmallD (j - 1) m' m θ =
      -(j : ℝ) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) +
        ((j : ℝ) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ := by
    refine chamber_reduce (fun m' m => ∀ (j : ℚ) (θ : ℝ), wigR j m' m * wignerSmallD (j - 1) m' m θ =
      -(j : ℝ) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) +
        ((j : ℝ) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ) ?_ ?_ ?_
    · intro m' m h1 h2 j θ
      exact wignerSmallD_rank_lower_A j m' m h1 h2 θ
    · intro m' m h j θ
      have := h j θ
      rw [wignerSmallD_swap_fun j m' m, wignerSmallD_swap_fun (j - 1) m' m, wigR_symm j m' m,
        deriv_const_mul_field']
      simp only
      rw [mul_comm (m : ℝ) (m' : ℝ)]
      linear_combination (sgn (m' - m)) * this
    · intro m' m h j θ
      have := h j θ
      rw [wignerSmallD_neg_fun j m' m, wignerSmallD_neg_fun (j - 1) m' m, wigR_neg] at *
      push_cast at this
      linear_combination this
  exact key m' m j θ

/-- **Upper rank ladder** (paper `eq:drankupper`): for all rational `f, m', m` and real `θ`,
`R_{f+1} d^{f+1}_{m'm}(θ) = ((f+1)² cos θ - m m') d^f_{m'm}(θ) + (f+1) · sin θ · ∂_θ d^f_{m'm}(θ)`;
with `x = cos θ` this is `R_{f+1} d_{f+1} = ((f+1)²x - mn) d_f - (f+1)(1-x²) d_f'`. -/
theorem wignerSmallD_rank_upper (j m' m : ℚ) (θ : ℝ) :
    wigR (j + 1) m' m * wignerSmallD (j + 1) m' m θ =
      (((j : ℝ) + 1) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ +
        ((j : ℝ) + 1) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) := by
  have key : ∀ m' m : ℚ, ∀ (j : ℚ) (θ : ℝ), wigR (j + 1) m' m * wignerSmallD (j + 1) m' m θ =
      (((j : ℝ) + 1) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ +
        ((j : ℝ) + 1) * (Real.sin θ * deriv (wignerSmallD j m' m) θ) := by
    refine chamber_reduce (fun m' m => ∀ (j : ℚ) (θ : ℝ),
      wigR (j + 1) m' m * wignerSmallD (j + 1) m' m θ =
      (((j : ℝ) + 1) ^ 2 * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ +
        ((j : ℝ) + 1) * (Real.sin θ * deriv (wignerSmallD j m' m) θ)) ?_ ?_ ?_
    · intro m' m h1 h2 j θ
      exact wignerSmallD_rank_upper_A j m' m h1 h2 θ
    · intro m' m h j θ
      have := h j θ
      rw [wignerSmallD_swap_fun j m' m, wignerSmallD_swap_fun (j + 1) m' m, wigR_symm (j + 1) m' m,
        deriv_const_mul_field']
      simp only
      rw [mul_comm (m : ℝ) (m' : ℝ)]
      linear_combination (sgn (m' - m)) * this
    · intro m' m h j θ
      have := h j θ
      rw [wignerSmallD_neg_fun j m' m, wignerSmallD_neg_fun (j + 1) m' m, wigR_neg] at *
      push_cast at this
      linear_combination this
  exact key m' m j θ

/-- **Rank recurrence** of `d` (paper `eq:3jrank` at `t = 0`; Varshalovich 4.8.1): for all rational
`f, m', m` and real `θ`, with `x = cos θ`,
`(2f+1)(f(f+1) x - m m') d^f = (f+1) R_f d^{f-1} + f R_{f+1} d^{f+1}`. -/
theorem wignerSmallD_rank_rec (j m' m : ℚ) (θ : ℝ) :
    (2 * (j : ℝ) + 1) * ((j : ℝ) * (j + 1) * Real.cos θ - (m : ℝ) * m') * wignerSmallD j m' m θ =
      ((j : ℝ) + 1) * (wigR j m' m * wignerSmallD (j - 1) m' m θ) +
        (j : ℝ) * (wigR (j + 1) m' m * wignerSmallD (j + 1) m' m θ) := by
  rw [wignerSmallD_rank_lower j m' m θ, wignerSmallD_rank_upper j m' m θ]
  ring

/-! ### The ladders in the variable `x = cos θ` (paper form) -/

/-- **Paper `eq:dranklower`** (`f(1-x²) d_f' + (f²x - mn) d_f = R_f d_{f-1}`), with
`d_f(x) = wignerSmallDx f n m x = d^f_{nm}(arccos x)` and `' = d/dx`, for `x ∈ (-1,1)`. -/
theorem wignerSmallDx_rank_lower (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    wigR j m' m * wignerSmallDx (j - 1) m' m x =
      (j : ℝ) * (1 - x ^ 2) * deriv (wignerSmallDx j m' m) x +
        ((j : ℝ) ^ 2 * x - (m : ℝ) * m') * wignerSmallDx j m' m x := by
  have hcos : Real.cos (Real.arccos x) = x :=
    Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have h := wignerSmallD_rank_lower j m' m (Real.arccos x)
  have h2 := one_sub_sq_mul_deriv_wignerSmallDx j m' m hx
  rw [hcos] at h
  change wigR j m' m * wignerSmallD (j - 1) m' m (Real.arccos x) =
    (j : ℝ) * (1 - x ^ 2) * deriv (wignerSmallDx j m' m) x +
      ((j : ℝ) ^ 2 * x - (m : ℝ) * m') * wignerSmallD j m' m (Real.arccos x)
  rw [h, mul_assoc, h2]
  ring

/-- **Paper `eq:drankupper`** (`R_{f+1} d_{f+1} = ((f+1)²x - mn) d_f - (f+1)(1-x²) d_f'`), for
`x ∈ (-1,1)`. -/
theorem wignerSmallDx_rank_upper (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    wigR (j + 1) m' m * wignerSmallDx (j + 1) m' m x =
      (((j : ℝ) + 1) ^ 2 * x - (m : ℝ) * m') * wignerSmallDx j m' m x -
        ((j : ℝ) + 1) * (1 - x ^ 2) * deriv (wignerSmallDx j m' m) x := by
  have hcos : Real.cos (Real.arccos x) = x :=
    Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  have h := wignerSmallD_rank_upper j m' m (Real.arccos x)
  have h2 := one_sub_sq_mul_deriv_wignerSmallDx j m' m hx
  rw [hcos] at h
  change wigR (j + 1) m' m * wignerSmallD (j + 1) m' m (Real.arccos x) =
    (((j : ℝ) + 1) ^ 2 * x - (m : ℝ) * m') * wignerSmallD j m' m (Real.arccos x) -
      ((j : ℝ) + 1) * (1 - x ^ 2) * deriv (wignerSmallDx j m' m) x
  rw [h, mul_assoc, h2]
  ring

/-- **Rank recurrence in `x`** (paper `eq:3jrank` at `t = 0`), for `x ∈ [-1,1]`. -/
theorem wignerSmallDx_rank_rec (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (2 * (j : ℝ) + 1) * ((j : ℝ) * (j + 1) * x - (m : ℝ) * m') * wignerSmallDx j m' m x =
      ((j : ℝ) + 1) * (wigR j m' m * wignerSmallDx (j - 1) m' m x) +
        (j : ℝ) * (wigR (j + 1) m' m * wignerSmallDx (j + 1) m' m x) := by
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have h := wignerSmallD_rank_rec j m' m (Real.arccos x)
  rw [hcos] at h
  exact h

/-- info: 'FormalResearch.Wigner.jacobi_ladder_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_ladder_lower

/-- info: 'FormalResearch.Wigner.jacobi_ladder_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_ladder_upper

/-- info: 'FormalResearch.Wigner.wignerSmallD_rank_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_rank_lower

/-- info: 'FormalResearch.Wigner.wignerSmallD_rank_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_rank_upper

/-- info: 'FormalResearch.Wigner.wignerSmallD_rank_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_rank_rec

/-- info: 'FormalResearch.Wigner.wignerSmallDx_rank_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallDx_rank_lower

/-- info: 'FormalResearch.Wigner.wignerSmallDx_rank_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallDx_rank_upper

/-- info: 'FormalResearch.Wigner.wignerSmallDx_rank_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallDx_rank_rec

end FormalResearch.Wigner

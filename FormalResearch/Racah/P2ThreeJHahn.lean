module

public import FormalResearch.Racah.P2ThreeJSeed

/-!
# Explicit Hahn realization of the finite kernel: dictionary and the `n = 0` case (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `sec:explicitHahn`
(`eq:HahnParametersPaper`--`eq:ExactHahnKernel`).

Dictionary (chamber `M ≥ |σ|`, `L = M+n`): `α_H = M-σ`, `β_H = M+σ`, `D = N-M-1`, `n = L-M` are
natural numbers `α β D n`; the lattice index is `u = j_++m_+` (`hu` below), and
`x_u = 1 - (α_H+1+2u)/N` (`hahn_x_of_u`).  `hahnW α β D u = (α+1)_u/u! · (β+1)_{D-u}/(D-u)!`
(`eq:HahnWeightPaper`), `hahnQ α β D n u` is the terminating `₃F₂` of `eq:HahnDefinitionPaper`,
`hahnNorm α β D n = Σ_u w_H(u) Q_n(u)²` (`eq:HahnNormPaper`).

## What is proved, and what is not

* `Phi3j_hahn_zero`: `eq:ExactHahnKernel` for **`n = 0`** (the extremal rank `L = M`), exactly the
  paper's boxed statement, derived from the one-term seed (`Phi3j_seed`) and the Chu--Vandermonde
  type convolution `hahnW_sum` (`Σ_u w_H(u) = C(α+β+D+1, D)`).
* The general `n` is **not** proved.  It needs (a) a terminating `₃F₂(1)` transformation taking
  Racah's sum (parameters `-(n), -(L-σ), -(a)`; `β+1`, `1+u-n`...) to the Hahn polynomial
  `Q_n(u)` (the Koornwinder / Bitencourt et al. correspondence, a Whipple/Sheppard-type
  transformation, which is not termwise), and (b) the Hahn norm `h_{H,n}` in closed form, i.e. the
  discrete orthogonality of the Hahn polynomials (equivalently `3j` orthogonality: a type (B)
  input).  The statement was checked numerically for all chambers `M ≥ |σ|` (exact rationals vs
  `sympy.physics.wigner.wigner_3j`).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- Chu--Vandermonde-type convolution of upper-index binomials. -/
theorem conv_choose (α β D : ℕ) :
    ∑ u ∈ Finset.range (D + 1), (α + u).choose α * (β + (D - u)).choose β =
      (α + β + 1 + D).choose (α + β + 1) := by
  have h := congrArg (fun p : PowerSeries ℤ => PowerSeries.coeff D p)
    (congrArg Units.val (PowerSeries.invOneSubPow_add ℤ (α + 1) (β + 1)))
  simp only [Units.val_mul, PowerSeries.coeff_mul] at h
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    show α + 1 + (β + 1) = (α + β + 1) + 1 by ring,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose] at h
  simp only [PowerSeries.coeff_mk] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have h' : ((∑ u ∈ Finset.range (D + 1), (α + u).choose α * (β + (D - u)).choose β : ℕ) : ℤ) =
      (((α + β + 1 + D).choose (α + β + 1) : ℕ) : ℤ) := by
    push_cast; rw [← h]
  exact_mod_cast h'

/-- The Hahn weight `w_H(u) = (α+1)_u/u! · (β+1)_{D-u}/(D-u)! = C(α+u,u) C(β+D-u,D-u)`
(`eq:HahnWeightPaper`). -/
def hahnW (α β D u : ℕ) : ℕ := (α + u).choose u * (β + (D - u)).choose (D - u)

/-- `Σ_{u=0}^{D} w_H(u) = C(α+β+D+1, D)`. -/
theorem hahnW_sum (α β D : ℕ) :
    ∑ u ∈ Finset.range (D + 1), hahnW α β D u = (α + β + 1 + D).choose (α + β + 1) := by
  rw [← conv_choose]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold hahnW
  rw [← Nat.choose_symm_add (a := α) (b := u), ← Nat.choose_symm_add (a := β) (b := D - u)]

/-- The Hahn polynomial `Q_n(u;α,β,D) = ₃F₂(-n, n+α+β+1, -u; α+1, -D; 1)` (DLMF convention,
`eq:HahnDefinitionPaper`), as the terminating sum over `k ≤ n` with `(x)_k = ascPochhammer`. -/
noncomputable def hahnQ (α β D n u : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) *
      (ascPochhammer ℝ k).eval (-(u : ℝ)) /
    ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (ascPochhammer ℝ k).eval (-(D : ℝ)) *
      (k.factorial : ℝ))

lemma hahnQ_zero (α β D u : ℕ) : hahnQ α β D 0 u = 1 := by
  simp [hahnQ]

/-- The squared norm `h_{H,n} = Σ_u w_H(u) Q_n(u)²` (`eq:HahnNormPaper`). -/
noncomputable def hahnNorm (α β D n : ℕ) : ℝ :=
  ∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) * hahnQ α β D n u ^ 2

lemma hahnNorm_zero (α β D : ℕ) :
    hahnNorm α β D 0 = ((α + β + 1 + D).choose (α + β + 1) : ℝ) := by
  unfold hahnNorm
  simp only [hahnQ_zero, one_pow, mul_one]
  rw [← Nat.cast_sum, hahnW_sum]

/-- `x_u = 1 - (α_H+1+2u)/N` for `x = 2μ/N` and `u = j_++m_+` (`eq:HahnGridPaper`), with
`α_H = M-σ`, `u = (N-1-M+σ-2μ)/2`. -/
lemma hahn_x_of_u (M σ N μ : ℚ) (u : ℚ) (hN : N ≠ 0) (hu : jPlus N σ + mPlus M μ = u) :
    2 * μ / N = 1 - ((M - σ) + 1 + 2 * u) / N := by
  have : 2 * μ = N - ((M - σ) + 1 + 2 * u) := by
    unfold jPlus mPlus at hu; linarith
  rw [this]; field_simp

lemma hahn_u_formula (M σ N μ : ℚ) :
    jPlus N σ + mPlus M μ = (N - 1 - M + σ - 2 * μ) / 2 := by
  unfold jPlus mPlus; ring

/-- **`eq:ExactHahnKernel` for `n = 0`** (extremal rank `L = M`): with `α = M-σ`, `β = M+σ`,
`D = N-M-1` natural numbers and `u = j_++m_+ ∈ {0,…,D}`,
`Φ_M^{M,σ}(x_u) = (-1)^α √(N/(2M+1)) √(w_H(u)/h_{H,0}) Q_0(u)`  (`Q_0 = 1`). -/
theorem Phi3j_hahn_zero (M σ N μ : ℚ) (α β D u : ℕ) (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (hu : jPlus N σ + mPlus M μ = u) (huD : u ≤ D) :
    Phi3j M M σ N μ =
      (-1 : ℝ) ^ α * Real.sqrt ((N : ℝ) / (2 * (M : ℝ) + 1)) *
        Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D 0) * hahnQ α β D 0 u := by
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le huD
  have ha : jMinus N σ + mMinus M μ = ((A : ℕ) : ℚ) := by
    unfold jMinus jPlus mMinus mPlus at *; push_cast at hD; linarith
  have hseed := Phi3j_seed M σ N μ β α A u hβ hα ha hu
  obtain ⟨hCp, hCq, hCPi⟩ := seed_Cvalues M σ N μ β α A u hβ hα ha hu
  have hNq : N = (A : ℚ) + u + 1 + M := by
    unfold jMinus jPlus mMinus mPlus at *; linarith
  have hNpos : (0 : ℝ) < N := by
    have h1 : (0 : ℚ) ≤ M := by
      linarith [(Nat.cast_nonneg α : (0 : ℚ) ≤ α), (Nat.cast_nonneg β : (0 : ℚ) ≤ β)]
    have : (0 : ℚ) < N := by
      rw [hNq]; have := (Nat.cast_nonneg A : (0 : ℚ) ≤ A)
      have := (Nat.cast_nonneg u : (0 : ℚ) ≤ u); linarith
    exact_mod_cast this
  have hM2 : 2 * (M : ℝ) + 1 = (α : ℝ) + β + 1 := by
    have : 2 * M + 1 = (α : ℚ) + β + 1 := by linarith
    exact_mod_cast this
  rw [hseed, hCp, hCq, hCPi, hahnQ_zero, hahnNorm_zero, hM2, hα, sgn_natCast]
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by positivity
  have hW : (hahnW α β (u + A) u : ℝ) =
      ((α + u).factorial : ℝ) / ((u.factorial : ℝ) * α.factorial) *
        (((β + A).factorial : ℝ) / ((A.factorial : ℝ) * β.factorial)) := by
    unfold hahnW
    rw [Nat.add_sub_cancel_left]
    push_cast
    rw [Nat.cast_choose ℝ (by omega : u ≤ α + u), Nat.cast_choose ℝ (by omega : A ≤ β + A)]
    simp only [Nat.add_sub_cancel]
  have hh0 : (((α + β + 1 + (u + A)).choose (α + β + 1) : ℕ) : ℝ) =
      ((α + β + 1 + (u + A)).factorial : ℝ) /
        (((α + β + 1).factorial : ℝ) * ((u + A).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : α + β + 1 ≤ α + β + 1 + (u + A))]
    simp only [Nat.add_sub_cancel_left]
  have hidx : u + A + (β + α + 1) = α + β + 1 + (u + A) := by ring
  rw [add_comm A u, hidx, hW, hh0]
  have hα1 := hpos α
  have hβ1 := hpos β
  have hu1 := hpos u
  have hA1 := hpos A
  have h2 := hpos (α + u)
  have h3 := hpos (β + A)
  have h4 := hpos (A + β)
  have h5 := hpos (u + α)
  have h6 := hpos (β + α)
  have h7 := hpos (α + β + 1)
  have h8 := hpos (α + β + 1 + (u + A))
  have h9 := hpos (u + A)
  have hab : (α + β + 1).factorial = (α + β + 1) * (α + β).factorial := Nat.factorial_succ _
  have hNn : (N : ℝ) ≠ 0 := hNpos.ne'
  have key : Real.sqrt (((β + α).factorial : ℝ) / ((β.factorial : ℝ) * α.factorial)) *
      Real.sqrt (((A + β).factorial : ℝ) / (A.factorial : ℝ) / (N : ℝ) ^ β *
        (((u + α).factorial : ℝ) / (u.factorial : ℝ) / (N : ℝ) ^ α)) /
      Real.sqrt (((α + β + 1 + (u + A)).factorial : ℝ) / (((u + A).factorial : ℝ)) /
        (N : ℝ) ^ (β + α + 1)) =
      Real.sqrt ((N : ℝ) / ((α : ℝ) + β + 1)) *
        Real.sqrt (((α + u).factorial : ℝ) / ((u.factorial : ℝ) * α.factorial) *
          (((β + A).factorial : ℝ) / ((A.factorial : ℝ) * β.factorial)) /
          (((α + β + 1 + (u + A)).factorial : ℝ) /
            (((α + β + 1).factorial : ℝ) * ((u + A).factorial : ℝ)))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_div (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [show α + u = u + α by ring, show β + A = A + β by ring, show β + α = α + β by ring]
    rw [show ((α + β + 1).factorial : ℝ) = ((α : ℝ) + β + 1) * ((α + β).factorial : ℝ) by
      rw [hab]; push_cast; ring]
    have : (α : ℝ) + β + 1 ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    ring
  linear_combination ((-1 : ℝ) ^ α) * key

/-- info: 'FormalResearch.Racah.Phi3j_hahn_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_hahn_zero

/-- info: 'FormalResearch.Racah.conv_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conv_choose

end FormalResearch.Racah

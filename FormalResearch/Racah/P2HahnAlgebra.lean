module

public import FormalResearch.Racah.P2ThreeJOperator

/-!
# Exact finite Hahn-to-Jacobi algebra (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:HahnJacobi` (`eq:finiteHahn1`,
`eq:finiteHahn2`).

Dictionary: lattice functions are `ψ : ℚ → ℝ` as for `Hh`; `Xop ψ = x ψ(x)` is `𝖷`;
`Cop M σ N ψ = 𝖧_h(𝖷ψ) - 𝖷(𝖧_hψ)` is `𝖢_h = [𝖧_h, 𝖷]`; `h = 1/N`, `Σ = M²+σ²`, `τ = Mσ`.

## What is proved

* `Cop_eq`: the explicit nearest-neighbour form `(𝖢_hψ)(x) = -(N/2)(a_h(x+h)ψ(x+2h) - a_h(x-h)ψ(x-2h))`
  (the paper's `(𝖢_h)_{ij} = (𝖧_h)_{ij}(x_j - x_i)`).
* `finiteHahn1`: `[𝖢_h, 𝖷] = 2(𝖷²-1) + 4h²(𝖧_h - (Σ-1)/2)`, pointwise at every `x` and every
  lattice function (no hypothesis).
* `finiteHahn2`: `[𝖧_h, 𝖢_h] = 2{𝖧_h, 𝖷} - 4τ`, pointwise at every `x` for which the four radicand
  factors at `x ± h` are nonnegative (`|σ-M| ≤ N(1-x)-1`, `|σ+M| ≤ N(1+x)-1`, which hold at every
  point of the physical lattice, where the first and last are the edge conditions); at such a point
  it holds for every lattice function, the second-neighbour terms cancelling.

Not covered: the contraction to the Jacobi algebra as `h → 0` (analytic).
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- Multiplication `𝖷` by `x` on lattice functions. -/
def Xop (ψ : ℚ → ℝ) : ℚ → ℝ := fun x => (x : ℝ) * ψ x

/-- `𝖢_h = [𝖧_h, 𝖷]`. -/
noncomputable def Cop (M σ N : ℚ) (ψ : ℚ → ℝ) : ℚ → ℝ :=
  fun x => Hh M σ N (Xop ψ) x - (x : ℝ) * Hh M σ N ψ x

/-- Explicit form of `𝖢_h`: `(𝖢_hψ)(x) = -(N/2)(a_h(x+h)ψ(x+2h) - a_h(x-h)ψ(x-2h))`. -/
lemma Cop_eq (M σ N : ℚ) (hN : N ≠ 0) (ψ : ℚ → ℝ) (x : ℚ) :
    Cop M σ N ψ x = -((N : ℝ) / 2) * (aMid M σ N ((x : ℝ) + 1 / N) * ψ (x + 2 / N) -
      aMid M σ N ((x : ℝ) - 1 / N) * ψ (x - 2 / N)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold Cop Hh Xop
  push_cast
  field_simp
  ring

/-- **`eq:finiteHahn1`**: `[𝖢_h, 𝖷] = 2(𝖷² - 1) + 4h²(𝖧_h - (Σ-1)/2)` (`h = 1/N`), at every point. -/
theorem finiteHahn1 (M σ N : ℚ) (hN : N ≠ 0) (ψ : ℚ → ℝ) (x : ℚ) :
    Cop M σ N (Xop ψ) x - Xop (Cop M σ N ψ) x =
      2 * ((x : ℝ) ^ 2 - 1) * ψ x +
        4 * (1 / (N : ℝ)) ^ 2 *
          (Hh M σ N ψ x - (((M : ℝ) ^ 2 + (σ : ℝ) ^ 2 - 1) / 2) * ψ x) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold Xop
  rw [Cop_eq M σ N hN, Cop_eq M σ N hN]
  unfold Hh
  push_cast
  field_simp
  ring

/-- The radicand factors at `x ± h` are nonnegative at lattice points. -/
lemma radicand_nonneg (M σ N : ℚ) (hN : 0 < N) (x : ℚ)
    (h1 : |(σ : ℝ) - M| ≤ (N : ℝ) * (1 - x) - 1) (h2 : |(σ : ℝ) + M| ≤ (N : ℝ) * (1 + x) - 1) :
    0 ≤ ((1 - ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2) ∧
    0 ≤ ((1 - ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ (s : ℝ) (p q : ℝ), 0 ≤ q → |p| ≤ q → 0 ≤ (s * q) ^ 2 - (s * p) ^ 2 := by
    intro s p q hq hpq
    have : p ^ 2 ≤ q ^ 2 := sq_le_sq' (by linarith [abs_le.mp hpq |>.1]) (abs_le.mp hpq |>.2)
    nlinarith [sq_nonneg s]
  have a1 : 0 ≤ (1 - ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2 := by
    have := key (1 / (N : ℝ)) ((σ : ℝ) - M) ((N : ℝ) * (1 - x) - 1) (le_trans (abs_nonneg _) h1) h1
    have e : (1 - ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2 =
        (1 / (N : ℝ) * ((N : ℝ) * (1 - x) - 1)) ^ 2 - (1 / (N : ℝ) * ((σ : ℝ) - M)) ^ 2 := by
      field_simp; ring
    rw [e]; exact this
  have a2 : 0 ≤ (1 + ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2 := by
    have := key (1 / (N : ℝ)) ((σ : ℝ) + M) ((N : ℝ) * (1 + x) - 1 + 2)
      (by linarith [abs_nonneg ((σ : ℝ) + M)]) (by linarith)
    have e : (1 + ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2 =
        (1 / (N : ℝ) * ((N : ℝ) * (1 + x) - 1 + 2)) ^ 2 - (1 / (N : ℝ) * ((σ : ℝ) + M)) ^ 2 := by
      field_simp; ring
    rw [e]; exact this
  have b1 : 0 ≤ (1 - ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2 := by
    have := key (1 / (N : ℝ)) ((σ : ℝ) - M) ((N : ℝ) * (1 - x) - 1 + 2)
      (by linarith [abs_nonneg ((σ : ℝ) - M)]) (by linarith)
    have e : (1 - ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2 =
        (1 / (N : ℝ) * ((N : ℝ) * (1 - x) - 1 + 2)) ^ 2 - (1 / (N : ℝ) * ((σ : ℝ) - M)) ^ 2 := by
      field_simp; ring
    rw [e]; exact this
  have b2 : 0 ≤ (1 + ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2 := by
    have := key (1 / (N : ℝ)) ((σ : ℝ) + M) ((N : ℝ) * (1 + x) - 1) (le_trans (abs_nonneg _) h2) h2
    have e : (1 + ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2 =
        (1 / (N : ℝ) * ((N : ℝ) * (1 + x) - 1)) ^ 2 - (1 / (N : ℝ) * ((σ : ℝ) + M)) ^ 2 := by
      field_simp; ring
    rw [e]; exact this
  exact ⟨mul_nonneg a1 a2, mul_nonneg b1 b2⟩

/-- `[𝖧_h, 𝖢_h] = 2{𝖧_h, 𝖷} - 4τ` under the radicand hypotheses (second-neighbour terms cancel). -/
lemma finiteHahn2_aux (M σ N : ℚ) (hN : N ≠ 0) (ψ : ℚ → ℝ) (x : ℚ)
    (hp : 0 ≤ ((1 - ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2))
    (hm : 0 ≤ ((1 - ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2)) :
    Hh M σ N (Cop M σ N ψ) x - Cop M σ N (Hh M σ N ψ) x =
      2 * (Hh M σ N (Xop ψ) x + (x : ℝ) * Hh M σ N ψ x) - 4 * (M : ℝ) * σ * ψ x := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Cop_eq M σ N hN (Hh M σ N ψ) x]
  simp only [Hh, Cop_eq M σ N hN, Xop]
  have e1 : x + 2 / N + 2 / N = x + 4 / N := by ring
  have e2 : x - 2 / N - 2 / N = x - 4 / N := by ring
  have e3 : x + 2 / N - 2 / N = x := by ring
  have e4 : x - 2 / N + 2 / N = x := by ring
  have f1 : (((x + 2 / N : ℚ) : ℝ) + 1 / N) = (x : ℝ) + 3 / N := by push_cast; ring
  have f2 : (((x + 2 / N : ℚ) : ℝ) - 1 / N) = (x : ℝ) + 1 / N := by push_cast; ring
  have f3 : (((x - 2 / N : ℚ) : ℝ) + 1 / N) = (x : ℝ) - 1 / N := by push_cast; ring
  have f4 : (((x - 2 / N : ℚ) : ℝ) - 1 / N) = (x : ℝ) - 3 / N := by push_cast; ring
  rw [e1, e2, e3, e4, f1, f2, f3, f4]
  have sp := aMid_sq hp
  have sm := aMid_sq hm
  push_cast
  generalize aMid M σ N ((x : ℝ) + 1 / N) = ap at sp ⊢
  generalize aMid M σ N ((x : ℝ) - 1 / N) = am at sm ⊢
  generalize ψ (x + 4 / N) = p4
  generalize ψ (x + 2 / N) = p2
  generalize ψ (x - 2 / N) = m2
  generalize ψ (x - 4 / N) = m4
  generalize aMid M σ N ((x : ℝ) + 3 / N) = ap3
  generalize aMid M σ N ((x : ℝ) - 3 / N) = am3
  field_simp at sp sm ⊢
  apply mul_left_cancel₀ hN'
  linear_combination (-4 * ψ x) * sp + (4 * ψ x) * sm

/-- **`eq:finiteHahn2`**: `[𝖧_h, 𝖢_h] = 2{𝖧_h, 𝖷} - 4τ` (`τ = Mσ`), at every `x` with
`|σ-M| ≤ N(1-x)-1` and `|σ+M| ≤ N(1+x)-1` (every point of the physical lattice, see
`finiteHahn2_lattice`), for every lattice function `ψ`. -/
theorem finiteHahn2 (M σ N : ℚ) (hN : 0 < N) (ψ : ℚ → ℝ) (x : ℚ)
    (h1 : |(σ : ℝ) - M| ≤ (N : ℝ) * (1 - x) - 1) (h2 : |(σ : ℝ) + M| ≤ (N : ℝ) * (1 + x) - 1) :
    Hh M σ N (Cop M σ N ψ) x - Cop M σ N (Hh M σ N ψ) x =
      2 * (Hh M σ N (Xop ψ) x + (x : ℝ) * Hh M σ N ψ x) - 4 * (M : ℝ) * σ * ψ x := by
  obtain ⟨hp, hm⟩ := radicand_nonneg M σ N hN x h1 h2
  exact finiteHahn2_aux M σ N hN.ne' ψ x hp hm

/-- The physical-lattice conditions (`j_±±m_± ∈ ℕ` at `x = 2μ/N`) imply the edge inequalities of
`finiteHahn2`. -/
lemma lat_edge (M σ N μ : ℚ) (a1 : IsNat (jMinus N σ + mMinus M μ))
    (a4 : IsNat (jPlus N σ - mPlus M μ)) (b1 : IsNat (jMinus N σ - mMinus M μ))
    (b3 : IsNat (jPlus N σ + mPlus M μ)) (hN : N ≠ 0) :
    |(σ : ℝ) - M| ≤ (N : ℝ) * (1 - ((2 * μ / N : ℚ) : ℝ)) - 1 ∧
      |(σ : ℝ) + M| ≤ (N : ℝ) * (1 + ((2 * μ / N : ℚ) : ℝ)) - 1 := by
  obtain ⟨k1, hk1⟩ := a1
  obtain ⟨k4, hk4⟩ := a4
  obtain ⟨l1, hl1⟩ := b1
  obtain ⟨l3, hl3⟩ := b3
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have e1 : (N : ℝ) * (1 - ((2 * μ / N : ℚ) : ℝ)) - 1 = (N : ℝ) - 2 * μ - 1 := by
    push_cast; field_simp
  have e2 : (N : ℝ) * (1 + ((2 * μ / N : ℚ) : ℝ)) - 1 = (N : ℝ) + 2 * μ - 1 := by
    push_cast; field_simp
  simp only [jMinus, jPlus, mMinus, mPlus] at hk1 hk4 hl1 hl3
  have r1 := congrArg (fun q : ℚ => (q : ℝ)) hk1
  have r4 := congrArg (fun q : ℚ => (q : ℝ)) hk4
  have s1 := congrArg (fun q : ℚ => (q : ℝ)) hl1
  have s3 := congrArg (fun q : ℚ => (q : ℝ)) hl3
  push_cast at r1 r4 s1 s3
  have n1 : (0 : ℝ) ≤ k1 := Nat.cast_nonneg k1
  have n4 : (0 : ℝ) ≤ k4 := Nat.cast_nonneg k4
  have m1 : (0 : ℝ) ≤ l1 := Nat.cast_nonneg l1
  have m3 : (0 : ℝ) ≤ l3 := Nat.cast_nonneg l3
  rw [e1, e2]
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- **`eq:finiteHahn2`** at every point of the physical lattice (the four admissibility
conditions of `Hh_Phi`). -/
theorem finiteHahn2_lattice (M σ N μ : ℚ) (hN : 0 < N) (ψ : ℚ → ℝ)
    (a1 : IsNat (jMinus N σ + mMinus M μ)) (a4 : IsNat (jPlus N σ - mPlus M μ))
    (b1 : IsNat (jMinus N σ - mMinus M μ)) (b3 : IsNat (jPlus N σ + mPlus M μ)) :
    Hh M σ N (Cop M σ N ψ) (2 * μ / N) - Cop M σ N (Hh M σ N ψ) (2 * μ / N) =
      2 * (Hh M σ N (Xop ψ) (2 * μ / N) + ((2 * μ / N : ℚ) : ℝ) * Hh M σ N ψ (2 * μ / N)) -
        4 * (M : ℝ) * σ * ψ (2 * μ / N) := by
  obtain ⟨h1, h2⟩ := lat_edge M σ N μ a1 a4 b1 b3 hN.ne'
  exact finiteHahn2 M σ N hN ψ _ h1 h2

/-- info: 'FormalResearch.Racah.finiteHahn1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteHahn1

/-- info: 'FormalResearch.Racah.finiteHahn2_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteHahn2_lattice

end FormalResearch.Racah

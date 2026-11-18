module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Paper J engine, JE1: the Abel--Casoratian identity and the Cramer identities (`lem:eng-abel`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, Section 2 (`sec:eng-cas`):
`def:eng-cas` (the Casoratian `𝒲_j`) and `lem:eng-abel` (i) (Abel identity, hard-edge form) and (ii) (the two
Cramer identities of `eq:eng-cramer`).  The source branch is `agents/m7-m1-global-racah` of QIprojects.

Dictionary to the paper (the paper's notation in brackets).
* `A j` is the bond coefficient `𝒜_h(s_j)`; `Q j` is `𝒬_h(u_j)`.
* `Lop A Q f j := A j * f (j+1) + A (j-1) * f (j-1) - Q j * f j`.  This is `h · (L_h f)_j`, i.e. the paper's
  `L_h` *without* its factor `h⁻¹`.  Hence the paper's identity `h[g_j (L_h f)_j - f_j (L_h g)_j] = 𝒲_j - 𝒲_{j-1}`
  reads here `g_j (Lop f)_j - f_j (Lop g)_j = 𝒲_j - 𝒲_{j-1}`, the same identity with `h` absorbed.
* `cas A f g j := A j * (f (j+1) * g j - f j * g (j+1))` is the paper's `𝒲_j(f,g)` with the same sign.

Reuse.  The Abel identity is the Lagrange identity `cas_sub` of `FormalResearch.DiscreteAiry`
(`Special/DiscreteJacobiCalculus.lean`) under the dictionary `a k := A (k-1)`: then `jac a Q = Lop A Q` and
`DiscreteAiry.cas a f g = - cas A f g` (`Lop_eq_jac`, `cas_eq_neg_cas_DA`).

Statements formalised (all exact, no asymptotics, no hypotheses beyond those displayed):
* `abel_pointwise` (`lem:eng-abel`(i), every `j`, including `j = 0` at a hard edge);
* `cas_hard_edge`, `Lop_hard_ghost`, `abel_hard_edge`: under the hard-edge condition `A (-1) = 0` one has
  `𝒲_{-1} = 0`, the operator at `j = 0` does not involve the ghost value `f (-1)`, and the Abel identity holds at `0`;
* `abel_sum`: the summed (Green) form `∑_{j ∈ [a,b]} (g_j (Lop f)_j - f_j (Lop g)_j) = 𝒲_b - 𝒲_{a-1}`;
* `cas_const_of_sol` (finite range) and `cas_const_global`: `𝒲_j(f,g)` is constant when `Lop f = Lop g = 0`;
  `cas_zero_of_hard_sol`: at a hard edge two solutions on `[0,b]` have `𝒲 ≡ 0` on `[-1,b]`;
* `cramer_first`, `cramer_second` (`lem:eng-abel`(ii), both identities of `eq:eng-cramer`, pure `ring`);
* `cas_comm`, `cas_self`, `cas_add_right`, `cas_smul_right`, `Lop_sub`: antisymmetry and bilinearity.

Non-vacuity: `cos_sin_solutions` exhibits the constant-coefficient pair `cos(jθ), sin(jθ)` solving `Lop f = 0`
with `Q = 2 cos θ` and Casoratian `𝒲_j = -sin θ` (constant, nonzero for `sin θ ≠ 0`).

Not formalised: anything asymptotic; the `h⁻¹` factor of the paper (dropped by convention, see above).
Differences from the paper: none in the statements (only the `h⁻¹` convention).
-/

@[expose] public section

open Finset

namespace FormalResearch.JE

/-- The Jacobi operator `Lop A Q f j = A j f(j+1) + A(j-1) f(j-1) - Q j f j`, equal to `h · (L_h f)_j`. -/
def Lop (A Q f : ℤ → ℝ) (j : ℤ) : ℝ := A j * f (j + 1) + A (j - 1) * f (j - 1) - Q j * f j

/-- The Casoratian across the bond `(j, j+1)`: `cas A f g j = A j (f (j+1) g j - f j g (j+1))`. -/
def cas (A f g : ℤ → ℝ) (j : ℤ) : ℝ := A j * (f (j + 1) * g j - f j * g (j + 1))

section Basic

variable (A Q f g : ℤ → ℝ) (j : ℤ)

lemma cas_self : cas A f f j = 0 := by unfold cas; ring

lemma cas_comm : cas A g f j = -cas A f g j := by unfold cas; ring

lemma cas_add_right (g₁ g₂ : ℤ → ℝ) :
    cas A f (fun i => g₁ i + g₂ i) j = cas A f g₁ j + cas A f g₂ j := by
  unfold cas; ring

lemma cas_smul_right (t : ℝ) : cas A f (fun i => t * g i) j = t * cas A f g j := by
  unfold cas; ring

lemma Lop_sub (f₁ f₂ : ℤ → ℝ) :
    Lop A Q (fun i => f₁ i - f₂ i) j = Lop A Q f₁ j - Lop A Q f₂ j := by
  unfold Lop; ring

/-- Dictionary: `Lop` is the discrete Jacobi row operator of `FormalResearch.DiscreteAiry` with `a k = A (k-1)`. -/
lemma Lop_eq_jac : Lop A Q f j = FormalResearch.DiscreteAiry.jac (fun k => A (k - 1)) Q f j := by
  simp [Lop, FormalResearch.DiscreteAiry.jac]

/-- Dictionary: the Casoratian is minus the one of `FormalResearch.DiscreteAiry` with `a k = A (k-1)`. -/
lemma cas_eq_neg_cas_DA :
    cas A f g j = -FormalResearch.DiscreteAiry.cas (fun k => A (k - 1)) f g j := by
  simp [cas, FormalResearch.DiscreteAiry.cas]; ring

/-- **Abel identity** (`lem:eng-abel`(i)), at every site `j`:
`g_j (Lop f)_j - f_j (Lop g)_j = 𝒲_j(f,g) - 𝒲_{j-1}(f,g)`.  The paper's form is `h[...] = 𝒲_j - 𝒲_{j-1}`. -/
theorem abel_pointwise :
    g j * Lop A Q f j - f j * Lop A Q g j = cas A f g j - cas A f g (j - 1) := by
  have h := FormalResearch.DiscreteAiry.cas_sub (fun k => A (k - 1)) Q f g j
  rw [← Lop_eq_jac, ← Lop_eq_jac] at h
  have e1 := cas_eq_neg_cas_DA A f g j
  have e2 := cas_eq_neg_cas_DA A f g (j - 1)
  linarith

/-- Hard edge: `A (-1) = 0` makes the bond `𝒲_{-1}` vanish. -/
lemma cas_hard_edge (hA : A (-1) = 0) : cas A f g (-1) = 0 := by
  simp [cas, hA]

/-- Hard edge: the operator at `j = 0` does not involve the ghost value `f (-1)`. -/
lemma Lop_hard_ghost (hA : A (-1) = 0) : Lop A Q f 0 = A 0 * f 1 - Q 0 * f 0 := by
  simp [Lop, hA]

/-- Hard-edge Abel identity at `j = 0` (`lem:eng-abel`(i), `𝒲_{-1} = 0`). -/
theorem abel_hard_edge (hA : A (-1) = 0) :
    g 0 * Lop A Q f 0 - f 0 * Lop A Q g 0 = cas A f g 0 := by
  have h := abel_pointwise A Q f g 0
  have h1 : cas A f g (0 - 1) = 0 := by simpa using cas_hard_edge A f g hA
  linarith

/-- The Abel identity summed over a window: `∑_{j=a}^{b} (g_j (Lop f)_j - f_j (Lop g)_j) = 𝒲_b - 𝒲_{a-1}`. -/
theorem abel_sum (a b : ℤ) (hab : a - 1 ≤ b) :
    ∑ j ∈ Icc a b, (g j * Lop A Q f j - f j * Lop A Q g j) = cas A f g b - cas A f g (a - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a - 1 + n := ⟨(b - (a - 1)).toNat, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : a - 1 ≤ a - 1 + (n : ℤ) := by omega
    have ih' := ih hb
    have hcast : a - 1 + ((n + 1 : ℕ) : ℤ) = (a - 1 + (n : ℤ)) + 1 := by push_cast; ring
    have hset : Icc a (a - 1 + ((n + 1 : ℕ) : ℤ)) =
        insert (a - 1 + ((n + 1 : ℕ) : ℤ)) (Icc a (a - 1 + (n : ℤ))) := by
      rw [hcast]
      exact (insert_Icc_right_eq_Icc_add_one (by omega)).symm
    rw [hset, Finset.sum_insert (by simp)]
    have hd := abel_pointwise A Q f g (a - 1 + ((n + 1 : ℕ) : ℤ))
    have hx : a - 1 + ((n + 1 : ℕ) : ℤ) - 1 = a - 1 + (n : ℤ) := by push_cast; ring
    rw [hx] at hd
    linarith

/-- Finite-range constancy: if `Lop f = Lop g = 0` on `[a,b]` then `𝒲_j(f,g) = 𝒲_{a-1}(f,g)` on `[a-1,b]`. -/
theorem cas_const_of_sol (a b : ℤ) (hf : ∀ i ∈ Icc a b, Lop A Q f i = 0)
    (hg : ∀ i ∈ Icc a b, Lop A Q g i = 0) :
    ∀ i ∈ Icc (a - 1) b, cas A f g i = cas A f g (a - 1) := by
  have key : ∀ n : ℕ, a - 1 + (n : ℤ) ≤ b → cas A f g (a - 1 + (n : ℤ)) = cas A f g (a - 1) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hle
      have hn : a - 1 + (n : ℤ) ≤ b := by push_cast at hle; omega
      have ih' := ih hn
      have hmem : a - 1 + ((n + 1 : ℕ) : ℤ) ∈ Icc a b := by
        rw [mem_Icc]; push_cast; constructor <;> omega
      have hd := abel_pointwise A Q f g (a - 1 + ((n + 1 : ℕ) : ℤ))
      have hx : a - 1 + ((n + 1 : ℕ) : ℤ) - 1 = a - 1 + (n : ℤ) := by push_cast; ring
      rw [hx, hf _ hmem, hg _ hmem, mul_zero, mul_zero] at hd
      have hfin : cas A f g (a - 1 + ((n + 1 : ℕ) : ℤ)) = cas A f g (a - 1 + (n : ℤ)) := by
        linarith
      exact hfin.trans ih'
  intro i hi
  rw [mem_Icc] at hi
  have hnn : ((i - (a - 1)).toNat : ℤ) = i - (a - 1) := Int.toNat_of_nonneg (by omega)
  have hfin := key (i - (a - 1)).toNat (by rw [hnn]; omega)
  have hsum : a - 1 + (i - (a - 1)) = i := by ring
  rwa [hnn, hsum] at hfin

/-- Global constancy: if `Lop f = Lop g = 0` everywhere then `𝒲_j(f,g)` does not depend on `j`. -/
theorem cas_const_global (hf : ∀ i, Lop A Q f i = 0) (hg : ∀ i, Lop A Q g i = 0) (i k : ℤ) :
    cas A f g i = cas A f g k := by
  have step : ∀ i, cas A f g i = cas A f g (i - 1) := by
    intro i
    have hd := abel_pointwise A Q f g i
    rw [hf i, hg i] at hd
    linarith
  have hconst : ∀ i, cas A f g i = cas A f g 0 := by
    intro i
    induction i using Int.induction_on with
    | zero => rfl
    | succ p ih => rw [step (p + 1)]; simpa using ih
    | pred p ih => have h := step (-(p : ℤ)); rw [← h]; exact ih
  rw [hconst i, hconst k]

/-- Hard edge, global form on a window: two solutions on `[0,b]` with `A (-1) = 0` have `𝒲_j = 0` on `[-1,b]`. -/
theorem cas_zero_of_hard_sol (hA : A (-1) = 0) (b : ℤ) (hf : ∀ i ∈ Icc 0 b, Lop A Q f i = 0)
    (hg : ∀ i ∈ Icc 0 b, Lop A Q g i = 0) :
    ∀ i ∈ Icc (-1) b, cas A f g i = 0 := by
  intro i hi
  have h := cas_const_of_sol A Q f g 0 b hf hg i (by simpa using hi)
  have h0 : cas A f g (0 - 1) = 0 := by simpa using cas_hard_edge A f g hA
  exact h.trans h0

end Basic

/-- **Cramer identity, first form** (`eq:eng-cramer`, first line), for any three sequences and every bond `i`. -/
theorem cramer_first (e f₁ f₂ : ℤ → ℝ) (A : ℤ → ℝ) (i : ℤ) :
    f₁ (i + 1) * cas A e f₂ i - f₂ (i + 1) * cas A e f₁ i = e (i + 1) * cas A f₁ f₂ i := by
  unfold cas; ring

/-- **Cramer identity, second form** (`eq:eng-cramer`, second line). -/
theorem cramer_second (e f₁ f₂ : ℤ → ℝ) (A : ℤ → ℝ) (i : ℤ) :
    f₁ i * cas A e f₂ i - f₂ i * cas A e f₁ i = e i * cas A f₁ f₂ i := by
  unfold cas; ring

/-- Non-vacuity: with `A = 1` and `Q = 2 cos θ`, the pair `cos(jθ)`, `sin(jθ)` solves `Lop f = 0` and has the
constant Casoratian `𝒲_j = -sin θ`. -/
theorem cos_sin_solutions (θ : ℝ) :
    (∀ j : ℤ, Lop (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i => Real.cos (i * θ)) j = 0) ∧
    (∀ j : ℤ, Lop (fun _ => 1) (fun _ => 2 * Real.cos θ) (fun i => Real.sin (i * θ)) j = 0) ∧
    (∀ j : ℤ, cas (fun _ => 1) (fun i => Real.cos (i * θ)) (fun i => Real.sin (i * θ)) j = -Real.sin θ) := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [Lop]
    have h1 : Real.cos (((j + 1 : ℤ) : ℝ) * θ) = Real.cos (j * θ + θ) := by push_cast; ring_nf
    have h2 : Real.cos (((j - 1 : ℤ) : ℝ) * θ) = Real.cos (j * θ - θ) := by push_cast; ring_nf
    rw [h1, h2, Real.cos_add, Real.cos_sub]; ring
  · simp only [Lop]
    have h1 : Real.sin (((j + 1 : ℤ) : ℝ) * θ) = Real.sin (j * θ + θ) := by push_cast; ring_nf
    have h2 : Real.sin (((j - 1 : ℤ) : ℝ) * θ) = Real.sin (j * θ - θ) := by push_cast; ring_nf
    rw [h1, h2, Real.sin_add, Real.sin_sub]; ring
  · simp only [cas]
    have h1 : ((j + 1 : ℤ) : ℝ) * θ = j * θ + θ := by push_cast; ring
    rw [h1, one_mul]
    have key := Real.sin_sub (j * θ) (j * θ + θ)
    have h2 : j * θ - (j * θ + θ) = -θ := by ring
    rw [h2, Real.sin_neg] at key
    linear_combination (-1 : ℝ) * key


-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JE.abel_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.abel_pointwise

/-- info: 'FormalResearch.JE.abel_hard_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.abel_hard_edge

/-- info: 'FormalResearch.JE.abel_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.abel_sum

/-- info: 'FormalResearch.JE.cas_const_of_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cas_const_of_sol

/-- info: 'FormalResearch.JE.cas_const_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cas_const_global

/-- info: 'FormalResearch.JE.cas_zero_of_hard_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cas_zero_of_hard_sol

/-- info: 'FormalResearch.JE.cramer_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cramer_first

/-- info: 'FormalResearch.JE.cramer_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cramer_second

/-- info: 'FormalResearch.JE.cos_sin_solutions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cos_sin_solutions

end FormalResearch.JE

end

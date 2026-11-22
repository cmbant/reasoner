module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Engine.Casoratian

/-!
# Paper J engine, L1.4: the Green identities of a finite Jacobi window (used by lem:tha-count)

Source: Paper J, `app_thmA.tex`, the proof of lem:tha-count ("Green's identity for two values of `X` gives `D'(X) = sum_n p_n q_n`",
with `D(X) = W(p,q)` constant in `n`), and the summed Abel identity `lem:eng-abel` (i) of `engine.tex`, which is `abel_sum` of
`Casoratian.lean` and is reused, not redone.

Generic form.  The bonds are `A : ℤ → ℝ` (with the hard edges `A (-1) = 0` and `A N = 0`), the diagonal is `X - B n`, and the window is
`0 ≤ n ≤ N`.  The statements are about arbitrary families `p X`, `q X` indexed by the energy `X`, so they do not depend on the
sequences `pSol`, `qSol` of `TheoremA/Statements.lean` (the instantiation is item L2.C5).  Dictionary: `cas A f g j` is the
Casoratian `𝒲_j(f,g) = A_j (f_{j+1} g_j - f_j g_{j+1})` and `Lop A Q f j` is the row operator, as in `Casoratian.lean`.

## Statements

* `green_cas_const` (`D` constant in `n`): if `Lop f = 0` on `[0, N-1]` and `Lop g = 0` on `[1, N]`, then `𝒲_i(f,g) = 𝒲_0(f,g)`
  for `i ∈ [0, N-1]`.  Pure algebra (`cas_const_of_sol`).
* `green_cas_last`: with also `A N = 0` and `g_N = 1`, `𝒲_0(f,g) = (X - B_N) f_N - A_{N-1} f_{N-1}`.
* `green_hasDerivAt` (`D' = sum p q`): with `p_0 = 1`, `Lop p = 0` on `[0, N-1]`, `Lop q = 0` on `[1, N]`, `q_N = 1`, and `p(·)`
  differentiable coordinatewise, the map `X ↦ 𝒲_0(p X, q X)` has derivative `∑_{i=0}^{N} p_i q_i`.  Here `N ≥ 1` (for `N = 0`
  the bond `𝒲_0` is not defined by the window), `A (-1) = 0`, `A N = 0`.

No positivity of the bonds is used: the identities are exact for any `A` with the two hard-edge conditions.  Positivity (and
`N ≥ 1`) is needed only for the zero counting of lem:tha-count (L2.C5).

## Differences from the paper

None in the identities.  The paper's `D` is `W(p,q)` at any bond; `green_cas_const` and `green_cas_last` give the constancy and the
explicit value at the bond `0`, which is the `casD` of the frozen `TheoremA/Statements.lean` (up to the instantiation of `pSol`, `qSol`).

## Not formalised

The zero counting of lem:tha-count is formalised in `TheoremA/Count.lean` (`propThaCount`, using `green_hasDerivAt` instantiated to `pSol`, `qSol`).
Its statement `PropThaCount` carries the hypotheses `1 ≤ N` and `0 < bondA` (the frozen statement is false without them: two degenerate families with
all bonds zero give counterexamples at `N = 0` and `N = 1`); the instantiation of `green_hasDerivAt` needs nonzero bonds.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Engine

open Finset

/-- **Constancy of the Casoratian** (`D` constant in `n`, lem:tha-count): for `Lop f = 0` on `[0, N-1]` and `Lop g = 0` on `[1, N]`,
`𝒲_i(f,g) = 𝒲_0(f,g)` for all `i ∈ [0, N-1]`. -/
theorem green_cas_const (A B : ℤ → ℝ) (X : ℝ) (N : ℤ) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ Icc 0 (N - 1), Lop A (fun n => X - B n) f i = 0)
    (hg : ∀ i ∈ Icc 1 N, Lop A (fun n => X - B n) g i = 0) :
    ∀ i ∈ Icc 0 (N - 1), cas A f g i = cas A f g 0 := by
  have h := cas_const_of_sol A (fun n => X - B n) f g 1 (N - 1)
    (fun i hi => hf i (mem_Icc.mpr ⟨by have := (mem_Icc.mp hi).1; omega, (mem_Icc.mp hi).2⟩))
    (fun i hi => hg i (mem_Icc.mpr ⟨by have := (mem_Icc.mp hi).1; omega,
      by have := (mem_Icc.mp hi).2; omega⟩))
  intro i hi
  have := h i (mem_Icc.mpr ⟨by have := (mem_Icc.mp hi).1; omega, (mem_Icc.mp hi).2⟩)
  simpa using this

/-- **Casoratian at the bond `0` as the last-row expression**: `𝒲_0(f,g) = (X - B_N) f_N - A_{N-1} f_{N-1}` when `Lop f = 0` on
`[0, N-1]`, `Lop g = 0` on `[1, N]`, `A N = 0` and `g_N = 1`. -/
theorem green_cas_last (A B : ℤ → ℝ) (X : ℝ) (N : ℤ) (hN : 1 ≤ N) (hAN : A N = 0) (f g : ℤ → ℝ)
    (hf : ∀ i ∈ Icc 0 (N - 1), Lop A (fun n => X - B n) f i = 0)
    (hg : ∀ i ∈ Icc 1 N, Lop A (fun n => X - B n) g i = 0) (hgN : g N = 1) :
    cas A f g 0 = (X - B N) * f N - A (N - 1) * f (N - 1) := by
  have hc := green_cas_const A B X N f g hf hg
  have hcN1 : cas A f g (N - 1) = cas A f g 0 := hc (N - 1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hab := abel_pointwise A (fun n => X - B n) f g N
  have hLg : Lop A (fun n => X - B n) g N = 0 := hg N (mem_Icc.mpr ⟨hN, le_rfl⟩)
  have hcasN : cas A f g N = 0 := by
    unfold cas
    rw [hAN]
    ring
  have hLf : Lop A (fun n => X - B n) f N = A (N - 1) * f (N - 1) - (X - B N) * f N := by
    unfold Lop
    rw [hAN]
    ring
  rw [hLg, hcasN, hgN, hLf] at hab
  linarith

/-- **Green identity for the derivative** (`D' = sum p q`, lem:tha-count): `X ↦ 𝒲_0(p X, q X)` has derivative
`∑_{i=0}^{N} p_i(X) q_i(X)`.  Hypotheses: `p X 0 = 1`; `Lop p X = 0` on `[0, N-1]`; `Lop q X = 0` on `[1, N]`; `q X N = 1`;
the hard edges `A (-1) = 0`, `A N = 0`; and each coordinate `X ↦ p X i` has derivative `p' X i`. -/
theorem green_hasDerivAt (A B : ℤ → ℝ) (N : ℤ) (hN : 1 ≤ N) (hA1 : A (-1) = 0) (hAN : A N = 0)
    (p q p' : ℝ → ℤ → ℝ)
    (hp0 : ∀ Y, p Y 0 = 1)
    (hp : ∀ Y, ∀ i ∈ Icc 0 (N - 1), Lop A (fun n => Y - B n) (p Y) i = 0)
    (hq : ∀ Y, ∀ i ∈ Icc 1 N, Lop A (fun n => Y - B n) (q Y) i = 0)
    (hqN : ∀ Y, q Y N = 1)
    (hpd : ∀ Y i, HasDerivAt (fun Z => p Z i) (p' Y i) Y) (X : ℝ) :
    HasDerivAt (fun Y => cas A (p Y) (q Y) 0) (∑ i ∈ Icc 0 N, p X i * q X i) X := by
  -- the Casoratian is the last-row expression for every energy
  have hD : ∀ Y, cas A (p Y) (q Y) 0 = (Y - B N) * p Y N - A (N - 1) * p Y (N - 1) :=
    fun Y => green_cas_last A B Y N hN hAN (p Y) (q Y) (hp Y) (hq Y) (hqN Y)
  have hfun : (fun Y => cas A (p Y) (q Y) 0) = fun Y => (Y - B N) * p Y N - A (N - 1) * p Y (N - 1) :=
    funext hD
  rw [hfun]
  -- derivative of the last-row expression
  have hdN : HasDerivAt (fun Y => (Y - B N) * p Y N - A (N - 1) * p Y (N - 1))
      (1 * p X N + (X - B N) * p' X N - A (N - 1) * p' X (N - 1)) X := by
    have h1 : HasDerivAt (fun Y => (Y - B N) * p Y N) (1 * p X N + (X - B N) * p' X N) X :=
      ((hasDerivAt_id' X).sub_const (B N)).mul (hpd X N)
    have h2 : HasDerivAt (fun Y => A (N - 1) * p Y (N - 1)) (A (N - 1) * p' X (N - 1)) X :=
      (hpd X (N - 1)).const_mul (A (N - 1))
    exact h1.sub h2
  -- the derivative of the zero coordinate `p_0 = 1` vanishes
  have hp'0 : p' X 0 = 0 := by
    have hc : HasDerivAt (fun Y => p Y 0) 0 X := by
      have e : (fun Y => p Y 0) = fun _ => (1 : ℝ) := funext hp0
      rw [e]
      exact hasDerivAt_const X 1
    exact (hpd X 0).unique hc
  -- the differentiated recurrence: `Lop (p') = p` on `[0, N-1]`
  have hrel : ∀ i ∈ Icc 0 (N - 1), Lop A (fun n => X - B n) (p' X) i = p X i := by
    intro i hi
    have hF : HasDerivAt (fun Y => A i * p Y (i + 1) + A (i - 1) * p Y (i - 1) - (Y - B i) * p Y i)
        (A i * p' X (i + 1) + A (i - 1) * p' X (i - 1) - (1 * p X i + (X - B i) * p' X i)) X := by
      have e1 := ((hpd X (i + 1)).const_mul (A i)).add ((hpd X (i - 1)).const_mul (A (i - 1)))
      have e2 := ((hasDerivAt_id' X).sub_const (B i)).mul (hpd X i)
      exact e1.sub e2
    have hzero : (fun Y => A i * p Y (i + 1) + A (i - 1) * p Y (i - 1) - (Y - B i) * p Y i) = fun _ => 0 := by
      funext Y
      have := hp Y i hi
      simp only [Lop] at this
      linarith
    rw [hzero] at hF
    have h0 := hF.unique (hasDerivAt_const X (0 : ℝ))
    simp only [Lop]
    linarith
  -- Green (summed Abel identity) over `[0, N]`: `∑ q_j (Lop p')_j = 0`
  have hcN : cas A (p' X) (q X) N = 0 := by
    unfold cas
    rw [hAN]
    ring
  have hc1 : cas A (p' X) (q X) (0 - 1) = 0 := by
    simpa using cas_hard_edge A (p' X) (q X) hA1
  have hsum1 : ∑ j ∈ Icc 0 N, (q X j * Lop A (fun n => X - B n) (p' X) j
      - p' X j * Lop A (fun n => X - B n) (q X) j) = cas A (p' X) (q X) N - cas A (p' X) (q X) (0 - 1) :=
    abel_sum A (fun n => X - B n) (p' X) (q X) 0 N (by omega)
  have hterm : ∑ j ∈ Icc 0 N, p' X j * Lop A (fun n => X - B n) (q X) j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rcases eq_or_ne j 0 with hj0 | hj0
    · rw [hj0, hp'0, zero_mul]
    · have hj1 : j ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega, (mem_Icc.mp hj).2⟩
      rw [hq X j hj1, mul_zero]
  have hsumq : ∑ j ∈ Icc 0 N, q X j * Lop A (fun n => X - B n) (p' X) j = 0 := by
    have e : ∑ j ∈ Icc 0 N, (q X j * Lop A (fun n => X - B n) (p' X) j
        - p' X j * Lop A (fun n => X - B n) (q X) j) = 0 := by
      rw [hsum1, hcN, hc1]
      ring
    rw [Finset.sum_sub_distrib, hterm, sub_zero] at e
    exact e
  -- splitting off the last site
  have hsplit : ∀ F : ℤ → ℝ, ∑ j ∈ Icc 0 N, F j = ∑ j ∈ Icc 0 (N - 1), F j + F N := by
    intro F
    have hset : Icc 0 N = insert N (Icc 0 (N - 1)) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    have hnot : N ∉ Icc 0 (N - 1) := by
      intro hmem
      have := (mem_Icc.mp hmem).2
      omega
    rw [hset, Finset.sum_insert hnot, add_comm]
  -- assemble
  have hfin : 1 * p X N + (X - B N) * p' X N - A (N - 1) * p' X (N - 1) = ∑ i ∈ Icc 0 N, p X i * q X i := by
    have hS := hsplit (fun i => p X i * q X i)
    have hT : ∑ j ∈ Icc 0 (N - 1), q X j * Lop A (fun n => X - B n) (p' X) j
        = ∑ j ∈ Icc 0 (N - 1), p X j * q X j :=
      Finset.sum_congr rfl (fun j hj => by rw [hrel j hj]; ring)
    have hU := hsplit (fun j => q X j * Lop A (fun n => X - B n) (p' X) j)
    have hLpN : Lop A (fun n => X - B n) (p' X) N = A (N - 1) * p' X (N - 1) - (X - B N) * p' X N := by
      unfold Lop
      rw [hAN]
      ring
    rw [hLpN, hqN X] at hU
    rw [hS, hqN X]
    linarith [hU, hsumq, hT]
  rw [← hfin]
  exact hdN

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.green_cas_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.green_cas_const

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.green_cas_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.green_cas_last

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.green_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.green_hasDerivAt

end FormalResearch.JacobiEigenvectors.Engine

end

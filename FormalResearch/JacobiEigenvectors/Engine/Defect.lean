module

public import FormalResearch.JacobiEigenvectors.Engine.Casoratian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

/-!
# Paper J engine, JE2: exact defect, h-parity and the Casoratian--Green identity (`thm:eng-defect`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, Section 2, `def:eng-ladder` (symplectic model
ladder, (SM1)--(SM3)), `eq:eng-ansatz`, `thm:eng-defect` (1)--(3); proofs in `app_engine.tex`
(`app:eng-defect`).  Branch `agents/m7-m1-global-racah` of QIprojects.

## Conventions
* Lattice points are real numbers `u` (the paper's `u_j = (j+γ)h`); `Z_j = ζ_h(u_j)` is absorbed into the model
  columns: `w α u h : Fin 2 → ℝ` is `𝐰^{(α)}_j(Z_j) = (w^{(α)}_j(Z_j), w̃^{(α)}_j(Z_j))` at `u = u_j`.  For fixed `h`
  the index `j` is determined by `u_j`, so this loses nothing.
* `dd s h` is `𝒟(s,h)`; `Dp u h := dd (u+h/2) h`, `Dm u h := dd (u-h/2) h` (the paper's `𝒟_±`).
* `pp s h` is `P_h(s)`, `qq u h` is `𝒬_h(u)`, `AA u h = A(u,h²)`, `BB u h = B(u,h²)`, `v(u,h) = (A, hB)` (`vrow`).
* `PiP u h = Π₊(u,h)`, `PiM u h = Π₋(u,h)` (`M2 = Matrix (Fin 2) (Fin 2) ℝ`), `Sg = Σ = diag(1,-1)`.
* Row vectors multiply matrices on the right (`rowMul v M`), column vectors on the left (`colMul M x`); the
  2-dimensional determinants are `colDet x y = det[x|y]` and `rowDet a b = det[a;b]`.
* The bond coefficient is `𝒜_h(s_j) = pp s_j h * dd s_j h`; the site form of `L_h` with the paper's `h⁻¹` removed is
  `siteLop`, so `h (L_h ψ̂)_j = siteLop` (the convention of `Casoratian`: `Lop = h L_h`).

## Statements formalised
* `SymplecticLadder γ` (`γ` a fixed shift parameter), indexed by `j ∈ ℕ` (the paper's `j_min = 0`):
  (SM1) `det[𝐰^{(1)}|𝐰^{(2)}] = ω_mod(h)` at every site `u_j`, and `ω_mod ≠ 0` (for `h > 0`, as in the paper's
  `h ∈ (0,h₀]`; the lattice relations (SM1), (SM2) carry the hypothesis `0 < h`);
  (SM2) the upper shift relation `𝒟₊(u_j,h) 𝐰^{(α)}(u_j+h) = Π₊(u_j,h) 𝐰^{(α)}(u_j)` at every `j ≥ 0`, and the lower
  shift relation `𝒟₋(u_j,h) 𝐰^{(α)}(u_j-h) = Π₋(u_j,h) 𝐰^{(α)}(u_j)` at every `j ≥ 1` (no guard on `𝒟₋`; at a hard
  edge `j = 0` the lower relation is replaced by `𝒟₋(u_0,h) = 0` and `Π₋ 𝐰^{(1)}_0 = 0`); `det Π± = D±²` and
  `Π₋(u+h,h) Π₊(u,h) = D₊(u,h)² I` for all `u`; (SM3) `D₊(u,-h) = D₋(u,h)` and `Π₊(u,-h) = Σ Π₋(u,h) Σ` for all `u`.
  The lattice relations are used through `IsSite γ h u` (`u = (j+γ)h` for some `j : ℕ`) and `IsSitePos γ h u`
  (the same with `j ≥ 1`), with closure lemmas `IsSite.add_h`, `IsSite.add_h_pos`.
* `defect_identity_interior` (`thm:eng-defect`(1), interior `j ≥ 1`), `defect_identity_hard` (`thm:eng-defect`(1) at the
  hard edge `j = 0`, `u = γh`): `siteLop = 𝔄^tot w_0 + 𝔅^tot w̃_0`, with the hard-edge case `Dm = 0` requiring the
  annihilation `Π₋(u,h) 𝐰^{(1)} = 0`.
* `defectRow_parity` (`thm:eng-defect`(2)): `𝔄^tot(u,-h) = 𝔄^tot(u,h)`, `𝔅^tot(u,-h) = -𝔅^tot(u,h)`, under
  evenness of `P`, `Q`, `A`, `B` in `h`; holds for all `u`, `h` (no site hypothesis).
* `casSite_eq_omega_Fcas` (`thm:eng-defect`(3a)): `𝒲_j(ψ̂¹,ψ̂²) = ω_mod(h) F_cas(s_j,h)` at every lattice point `u_j`
  (`j ≥ 0`), with no bond hypothesis.
* `Fcas_even` (`thm:eng-defect`(3b)): `F_cas(s,-h) = F_cas(s,h)` at a bond with `𝒟(s,h) ≠ 0`; `Fcas_zero`:
  `F_cas(s,0) = A(s,0)² V₀(s)` with `V₀(s) = P₀(s) Π₋(s,0)₁₂`.
* `green_identity` (`thm:eng-defect`(3c), eq:eng-green): `A 𝔅 - h B 𝔄 = -[F_cas(u+h/2,h) - F_cas(u-h/2,h)]`, at a
  point with `𝒟(u+h/2,h) ≠ 0`.
* `Lop_seq_eq_siteLop`: the bridge to the sequence operator `FormalResearch.JacobiEigenvectors.Engine.Lop` of `Casoratian` (with
  `u_j = (j+γ)h`, `A j = 𝒜_h(s_j)`, `Q j = 𝒬_h(u_j)`): the defect identity holds for `Lop` itself.
* `constant_ladder`: non-vacuity, the constant instance (`𝒟 ≡ P ≡ 1`, `Q ≡ 0`, `Π± = I`, `𝐰^{(1)} = e_1`,
  `𝐰^{(2)} = e_2`, `ω_mod = 1`, `A ≡ 1`, `B ≡ 0`) satisfies every field of `SymplecticLadder`.

## Differences from the paper (all deliberate, all minor)
1. **Bond nondegeneracy.** `(3b)` and `(3c)` are stated under `𝒟(s,h) ≠ 0` at the bond concerned.  The paper
   states them for every bond; they need it.  For `(3c)` the identity `Π₊(u) = adj Π₋(u+h)` (from
   `Π₋(u+h)Π₊(u) = D₊²I`) requires `D₊(u,h) ≠ 0`, and when `D₊ = 0` the products vanish.  `(3a)` needs no such
   hypothesis: its proof uses the lower shift at `u_{j+1}` (available for every `j ≥ 0`) and no division.
   Every bond with `𝒜_h(s_j) ≠ 0` (in particular all bonds of the ladder) satisfies the hypothesis.
2. **Lower shift relation.** `SymplecticLadder.shift_dn` is assumed at every `j ≥ 1`, with no guard on `𝒟₋`, as in the
   paper.  At the hard edge `j = 0` the defect identity uses the hypotheses `𝒟₋(u_0,h) = 0` and the annihilation
   `Π₋ 𝐰^{(1)}_0 = 0` directly (`defect_identity_hard`), and `α = 2` is not claimed there.
3. **Parity of `𝒟`.** `D₊(u,-h)=D₋(u,h)` is recorded as a field (SM3) but is not needed for the three identities.
4. **Lattice sites only, `h > 0` only.** The relations (SM1), (SM2) are assumed only for `h > 0` (the paper's
   `h ∈ (0,h₀]`; the model functions need not be defined for `h ≤ 0`), hence the theorems that use them take `0 < h`. The Wronskian and the two shift relations (SM1), (SM2) are assumed only at the lattice
   points `u_j = (j+γ)h`, `j ∈ ℕ`, as in `def:eng-ladder` (they are statements about the model sequences `w_j(Z_j)`),
   not for all real `u`.  The relations `det Π± = D±²`, `Π₋(u+h)Π₊(u) = D₊²I` and (SM3) are identities between
   smooth functions of `(u,h)` in the paper and are kept for all `u`, `h`, since (SM3) involves `-h`.  The theorems
   that use a lattice relation take `IsSite γ h u` (`j ≥ 0`) or `IsSitePos γ h u` (`j ≥ 1`) or `u = γh` (`j = 0`);
   `defectRow_parity`, `Fcas_zero`, `Fcas_even`, `green_identity` use no site hypothesis.
5. **Global domain of the algebraic identities (a restriction relative to the paper).** `det Π± = D±²`,
   `Π₋(u+h)Π₊(u) = D₊²I` and (SM3) are required for all real `(u,h)`, whereas the paper has them on
   `I_u × (-h₀,h₀)`.  They are used only by `defectRow_parity`, `Fcas_even` and `green_identity`; the defect
   identities, `casSite_eq_omega_Fcas` and hence the stability theorems (`VolterraLadder`) use only the lattice
   relations.  A ladder defined on an interval only must be extended to `ℝ` with these identities to fit the
   structure; stating them on a domain is an open improvement.

Not formalised here: the existence of the ladder (the paper's Remark on the Weber/parabolic-cylinder charts) and the
parity-freezing identity of Section 3.  The corrector recursion and the defect order (`thm:eng-corr`) are formalised
in `Engine/CorrectorOrder.lean`, `Engine/CorrectorDefect.lean` and `Engine/Corrector.lean` (`eng_corr`), on top of the
identities of this file.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Engine

/-- Real 2-vectors (columns, or rows when written on the left of a matrix). -/
abbrev V2 := Fin 2 → ℝ

/-- Real `2×2` matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The paper's `Σ = diag(1,-1)`. -/
def Sg : M2 := !![1, 0; 0, -1]

/-- Row vector times matrix. -/
def rowMul (v : V2) (M : M2) : V2 := ![v 0 * M 0 0 + v 1 * M 1 0, v 0 * M 0 1 + v 1 * M 1 1]

/-- Matrix times column vector. -/
def colMul (M : M2) (x : V2) : V2 := ![M 0 0 * x 0 + M 0 1 * x 1, M 1 0 * x 0 + M 1 1 * x 1]

/-- The Euclidean pairing of a row and a column vector. -/
def dot (v x : V2) : ℝ := v 0 * x 0 + v 1 * x 1

/-- `det[x | y]` for two column vectors. -/
def colDet (x y : V2) : ℝ := x 0 * y 1 - x 1 * y 0

/-- `det[a ; b]` for two row vectors. -/
def rowDet (a b : V2) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The row vector `v(u,h) = (A(u,h²), h B(u,h²))`. -/
def vrow (AA BB : ℝ → ℝ → ℝ) (u h : ℝ) : V2 := ![AA u h, h * BB u h]

/-- `D₊(u,h) = 𝒟(u + h/2, h)`. -/
def Dp (dd : ℝ → ℝ → ℝ) (u h : ℝ) : ℝ := dd (u + h / 2) h

/-- `D₋(u,h) = 𝒟(u - h/2, h)`. -/
def Dm (dd : ℝ → ℝ → ℝ) (u h : ℝ) : ℝ := dd (u - h / 2) h

/-- The site bond coefficients `𝒜_h(s_j) = P_h(s_j) 𝒟(s_j,h)` at `s_j = u + h/2` and `𝒜_h(s_{j-1})` at `u - h/2`. -/
def bondUp (dd pp : ℝ → ℝ → ℝ) (u h : ℝ) : ℝ := pp (u + h / 2) h * Dp dd u h

/-- See `bondUp`: the lower bond `𝒜_h(s_{j-1})`. -/
def bondDn (dd pp : ℝ → ℝ → ℝ) (u h : ℝ) : ℝ := pp (u - h / 2) h * Dm dd u h

/-- The defect row vector `𝔇(u,h) = P_h(u+h/2) v(u+h,h) Π₊(u,h) + P_h(u-h/2) v(u-h,h) Π₋(u,h) - Q_h(u) v(u,h)`,
whose components are `𝔄^tot` (component 0) and `𝔅^tot` (component 1). -/
def defectRow (pp qq AA BB : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (u h : ℝ) : V2 :=
  fun k => pp (u + h / 2) h * rowMul (vrow AA BB (u + h) h) (PiP u h) k
    + pp (u - h / 2) h * rowMul (vrow AA BB (u - h) h) (PiM u h) k - qq u h * vrow AA BB u h k

/-- The site form of `h (L_h ψ̂)_j`: `𝒜(s_j) ψ̂_{j+1} + 𝒜(s_{j-1}) ψ̂_{j-1} - 𝒬(u_j) ψ̂_j`, where
`ψ̂ x = v(x,h)·𝐰^{(α)}(x)` is the comparison sequence at the lattice point `x`. -/
def siteLop (dd pp qq AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (α : Fin 2) (u h : ℝ) : ℝ :=
  bondUp dd pp u h * dot (vrow AA BB (u + h) h) (w α (u + h) h)
    + bondDn dd pp u h * dot (vrow AA BB (u - h) h) (w α (u - h) h)
    - qq u h * dot (vrow AA BB u h) (w α u h)

/-- The Casoratian of the comparison pair across the bond `s_j = u + h/2`:
`𝒲_j(ψ̂¹,ψ̂²) = 𝒜(s_j) (ψ̂¹_{j+1} ψ̂²_j - ψ̂¹_j ψ̂²_{j+1})`. -/
def casSite (dd pp AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (u h : ℝ) : ℝ :=
  bondUp dd pp u h * (dot (vrow AA BB (u + h) h) (w 0 (u + h) h) * dot (vrow AA BB u h) (w 1 u h)
    - dot (vrow AA BB u h) (w 0 u h) * dot (vrow AA BB (u + h) h) (w 1 (u + h) h))

/-- The paper's `𝓕^tot_cas(s,h) = P_h(s) det[v(s+h/2,h); v(s-h/2,h) Π₋(s+h/2,h)]`. -/
def Fcas (pp AA BB : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s h : ℝ) : ℝ :=
  pp s h * rowDet (vrow AA BB (s + h / 2) h) (rowMul (vrow AA BB (s - h / 2) h) (PiM (s + h / 2) h))

/-- The lattice points `u_j = (j+γ)h`, `j ∈ ℕ`, of the shift `γ` (the paper's `u_j`, `j_min = 0`). -/
def IsSite (γ h u : ℝ) : Prop := ∃ j : ℕ, u = ((j : ℝ) + γ) * h

/-- The lattice points `u_j = (j+γ)h` with `j ≥ 1`, the sites that carry a lower shift relation. -/
def IsSitePos (γ h u : ℝ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ u = ((j : ℝ) + γ) * h

lemma IsSitePos.isSite {γ h u : ℝ} (hu : IsSitePos γ h u) : IsSite γ h u := by
  obtain ⟨j, _, rfl⟩ := hu
  exact ⟨j, rfl⟩

lemma IsSite.add_h {γ h u : ℝ} (hu : IsSite γ h u) : IsSite γ h (u + h) := by
  obtain ⟨j, rfl⟩ := hu
  exact ⟨j + 1, by push_cast; ring⟩

/-- The upper neighbour of a lattice point is a lattice point with index `≥ 1`. -/
lemma IsSite.add_h_pos {γ h u : ℝ} (hu : IsSite γ h u) : IsSitePos γ h (u + h) := by
  obtain ⟨j, rfl⟩ := hu
  exact ⟨j + 1, by omega, by push_cast; ring⟩

/-- **Symplectic model ladder** (`def:eng-ladder`) with shift parameter `γ`: the hypotheses (SM1)--(SM3), one named
field each.  The functions are those of `Defect` (see the module docstring for the lattice-point convention).  The
Wronskian and the upper shift relation are required at the lattice points `u_j = (j+γ)h`, `j ∈ ℕ`; the lower shift
relation at those with `j ≥ 1` (the paper's `j > j_min`), with no guard on `𝒟₋`. -/
structure SymplecticLadder (γ : ℝ) (dd pp qq : ℝ → ℝ → ℝ) (PiP PiM : ℝ → ℝ → M2) (w : Fin 2 → ℝ → ℝ → V2)
    (ω : ℝ → ℝ) : Prop where
  /-- (SM1) constant model Wronskian at the lattice points: `det[𝐰^{(1)}|𝐰^{(2)}] = ω_mod(h)` at `u_j = (j+γ)h`. -/
  wronsk : ∀ (h : ℝ), 0 < h → ∀ (j : ℕ), colDet (w 0 (((j : ℝ) + γ) * h) h) (w 1 (((j : ℝ) + γ) * h) h) = ω h
  /-- (SM1) `ω_mod(h) ≠ 0`. -/
  wronsk_ne : ∀ h, 0 < h → ω h ≠ 0
  /-- (SM2) upper shift relation `𝒟₊(u_j,h) 𝐰^{(α)}(u_j+h) = Π₊(u_j,h) 𝐰^{(α)}(u_j)`, at every lattice point
  (`u_j + h` is the lattice point `u_{j+1}`). -/
  shift_up : ∀ (α : Fin 2) (h : ℝ), 0 < h → ∀ (j : ℕ),
    Dp dd (((j : ℝ) + γ) * h) h • w α (((j : ℝ) + γ) * h + h) h
      = colMul (PiP (((j : ℝ) + γ) * h) h) (w α (((j : ℝ) + γ) * h) h)
  /-- (SM2) lower shift relation `𝒟₋(u_j,h) 𝐰^{(α)}(u_j-h) = Π₋(u_j,h) 𝐰^{(α)}(u_j)` at every lattice point with
  `j ≥ 1`; at the hard edge `j = 0` the relation is replaced by the annihilation hypothesis. -/
  shift_dn : ∀ (α : Fin 2) (h : ℝ), 0 < h → ∀ (j : ℕ), 1 ≤ j →
    Dm dd (((j : ℝ) + γ) * h) h • w α (((j : ℝ) + γ) * h - h) h
      = colMul (PiM (((j : ℝ) + γ) * h) h) (w α (((j : ℝ) + γ) * h) h)
  /-- (SM2) `det Π₊(u,h) = 𝒟₊(u,h)²`. -/
  det_up : ∀ u h, (PiP u h).det = Dp dd u h ^ 2
  /-- (SM2) `det Π₋(u,h) = 𝒟₋(u,h)²`. -/
  det_dn : ∀ u h, (PiM u h).det = Dm dd u h ^ 2
  /-- (SM2) `Π₋(u+h,h) Π₊(u,h) = 𝒟₊(u,h)² I₂`. -/
  prod : ∀ u h, PiM (u + h) h * PiP u h = Dp dd u h ^ 2 • (1 : M2)
  /-- (SM3) `𝒟₊(u,-h) = 𝒟₋(u,h)`. -/
  par_D : ∀ u h, Dp dd u (-h) = Dm dd u h
  /-- (SM3) `Π₊(u,-h) = Σ Π₋(u,h) Σ`. -/
  par_Pi : ∀ u h, PiP u (-h) = Sg * PiM u h * Sg

section Algebra

/-- `Σ X Σ` has entries `(X₀₀, -X₀₁, -X₁₀, X₁₁)`. -/
lemma sg_conj_entries (X : M2) :
    (Sg * X * Sg) 0 0 = X 0 0 ∧ (Sg * X * Sg) 0 1 = -X 0 1 ∧
    (Sg * X * Sg) 1 0 = -X 1 0 ∧ (Sg * X * Sg) 1 1 = X 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Sg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;> ring

/-- The entries of `Π₊ = adj Π₋` when `Π₋ Π₊ = δ I` and `det Π₋ = δ ≠ 0` (`Π₊` is the adjugate of `Π₋`). -/
lemma adj_entries_of_prod (M N : M2) (δ : ℝ) (hδ : δ ≠ 0)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = δ) (hprod : M * N = δ • (1 : M2)) :
    N 0 0 = M 1 1 ∧ N 0 1 = -M 0 1 ∧ N 1 0 = -M 1 0 ∧ N 1 1 = M 0 0 := by
  have E00 : M 0 0 * N 0 0 + M 0 1 * N 1 0 = δ := by
    have := congrFun (congrFun hprod 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have E01 : M 0 0 * N 0 1 + M 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hprod 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have E10 : M 1 0 * N 0 0 + M 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hprod 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have E11 : M 1 0 * N 0 1 + M 1 1 * N 1 1 = δ := by
    have := congrFun (congrFun hprod 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have n01 : N 0 1 = -M 0 1 := by
    have : δ * (N 0 1 + M 0 1) = 0 := by
      linear_combination M 1 1 * E01 - M 0 1 * E11 - N 0 1 * hdet
    have := (mul_eq_zero.mp this).resolve_left hδ
    linarith
  have n11 : N 1 1 = M 0 0 := by
    have : δ * (N 1 1 - M 0 0) = 0 := by
      linear_combination M 0 0 * E11 - M 1 0 * E01 - N 1 1 * hdet
    have := (mul_eq_zero.mp this).resolve_left hδ
    linarith
  have n00 : N 0 0 = M 1 1 := by
    have : δ * (N 0 0 - M 1 1) = 0 := by
      linear_combination M 1 1 * E00 - M 0 1 * E10 - N 0 0 * hdet
    have := (mul_eq_zero.mp this).resolve_left hδ
    linarith
  have n10 : N 1 0 = -M 1 0 := by
    have : δ * (N 1 0 + M 1 0) = 0 := by
      linear_combination M 0 0 * E10 - M 1 0 * E00 - N 1 0 * hdet
    have := (mul_eq_zero.mp this).resolve_left hδ
    linarith
  exact ⟨n00, n01, n10, n11⟩

/-- Binet--Cauchy in dimension 2: `(a·x)(b·y) - (b·x)(a·y) = det[a;b] det[x|y]`. -/
lemma binet_cauchy (a b x y : V2) :
    dot a x * dot b y - dot b x * dot a y = rowDet a b * colDet x y := by
  simp only [dot, rowDet, colDet]; ring

end Algebra

section SiteAccess

variable {γ : ℝ} {dd pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- The Wronskian relation at a lattice point `u = u_j`. -/
lemma SymplecticLadder.wronsk_at (L : SymplecticLadder γ dd pp qq PiP PiM w ω) {u h : ℝ} (hh : 0 < h)
    (hu : IsSite γ h u) : colDet (w 0 u h) (w 1 u h) = ω h := by
  obtain ⟨j, rfl⟩ := hu
  exact L.wronsk h hh j

/-- The upper shift relation at a lattice point `u = u_j`. -/
lemma SymplecticLadder.shift_up_at (L : SymplecticLadder γ dd pp qq PiP PiM w ω) {u h : ℝ} (hh : 0 < h)
    (hu : IsSite γ h u) (α : Fin 2) : Dp dd u h • w α (u + h) h = colMul (PiP u h) (w α u h) := by
  obtain ⟨j, rfl⟩ := hu
  exact L.shift_up α h hh j

/-- The lower shift relation at a lattice point `u = u_j` with `j ≥ 1`. -/
lemma SymplecticLadder.shift_dn_at (L : SymplecticLadder γ dd pp qq PiP PiM w ω) {u h : ℝ} (hh : 0 < h)
    (hu : IsSitePos γ h u) (α : Fin 2) : Dm dd u h • w α (u - h) h = colMul (PiM u h) (w α u h) := by
  obtain ⟨j, hj, rfl⟩ := hu
  exact L.shift_dn α h hh j hj

end SiteAccess

section Shifts

variable {γ : ℝ} {dd pp qq AA BB : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- The componentwise upper shift relation at a lattice point. -/
lemma shift_up_comp (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (α : Fin 2) (u h : ℝ) (hh : 0 < h)
    (hu : IsSite γ h u) :
    Dp dd u h * w α (u + h) h 0 = PiP u h 0 0 * w α u h 0 + PiP u h 0 1 * w α u h 1 ∧
    Dp dd u h * w α (u + h) h 1 = PiP u h 1 0 * w α u h 0 + PiP u h 1 1 * w α u h 1 := by
  have := L.shift_up_at hh hu α
  exact ⟨congrFun this 0, congrFun this 1⟩

/-- The componentwise lower shift relation at a lattice point with `j ≥ 1`. -/
lemma shift_dn_comp (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (α : Fin 2) (u h : ℝ) (hh : 0 < h)
    (hu : IsSitePos γ h u) :
    Dm dd u h * w α (u - h) h 0 = PiM u h 0 0 * w α u h 0 + PiM u h 0 1 * w α u h 1 ∧
    Dm dd u h * w α (u - h) h 1 = PiM u h 1 0 * w α u h 0 + PiM u h 1 1 * w α u h 1 := by
  have := L.shift_dn_at hh hu α
  exact ⟨congrFun this 0, congrFun this 1⟩

end Shifts

section Parities

variable {γ : ℝ} {dd pp qq AA BB : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- The entries of `Π±(u,-h)` in terms of `Π∓(u,h)` (from (SM3) and `Σ² = I`). -/
lemma par_Pi_entries (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (u h : ℝ) :
    PiP u (-h) 0 0 = PiM u h 0 0 ∧ PiP u (-h) 0 1 = -PiM u h 0 1 ∧
    PiP u (-h) 1 0 = -PiM u h 1 0 ∧ PiP u (-h) 1 1 = PiM u h 1 1 ∧
    PiM u (-h) 0 0 = PiP u h 0 0 ∧ PiM u (-h) 0 1 = -PiP u h 0 1 ∧
    PiM u (-h) 1 0 = -PiP u h 1 0 ∧ PiM u (-h) 1 1 = PiP u h 1 1 := by
  have h1 := L.par_Pi u h
  have h2 := L.par_Pi u (-h)
  rw [neg_neg] at h2
  obtain ⟨a1, b1, c1, d1⟩ := sg_conj_entries (PiM u h)
  obtain ⟨a2, b2, c2, d2⟩ := sg_conj_entries (PiP u h)
  obtain ⟨a3, b3, c3, d3⟩ := sg_conj_entries (PiM u (-h))
  have e1 : PiP u (-h) = Sg * PiM u h * Sg := h1
  have e2 : PiP u h = Sg * PiM u (-h) * Sg := h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, a1]
  · rw [e1, b1]
  · rw [e1, c1]
  · rw [e1, d1]
  · have := congrFun (congrFun e2 0) 0
    rw [a3] at this
    exact this.symm
  · have := congrFun (congrFun e2 0) 1
    rw [b3] at this
    linarith
  · have := congrFun (congrFun e2 1) 0
    rw [c3] at this
    linarith
  · have := congrFun (congrFun e2 1) 1
    rw [d3] at this
    exact this.symm

/-- The entries of `Π₊(u,h) = adj Π₋(u+h,h)` at a point with `𝒟₊(u,h) ≠ 0`. -/
lemma Pp_entries_of_prod (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (u h : ℝ) (hD : Dp dd u h ≠ 0) :
    PiP u h 0 0 = PiM (u + h) h 1 1 ∧ PiP u h 0 1 = -PiM (u + h) h 0 1 ∧
    PiP u h 1 0 = -PiM (u + h) h 1 0 ∧ PiP u h 1 1 = PiM (u + h) h 0 0 := by
  have hmDp : Dm dd (u + h) h = Dp dd u h := by
    simp only [Dm, Dp]; congr 1; ring
  have hdet := L.det_dn (u + h) h
  rw [hmDp, Matrix.det_fin_two] at hdet
  exact adj_entries_of_prod (PiM (u + h) h) (PiP u h) (Dp dd u h ^ 2) (pow_ne_zero 2 hD)
    hdet (L.prod u h)

/-- Parity (`thm:eng-defect`(2)): `𝔄^tot(u,-h) = 𝔄^tot(u,h)` and `𝔅^tot(u,-h) = -𝔅^tot(u,h)`, for `P`, `Q`, `A`, `B`
even in `h`. -/
theorem defectRow_parity (L : SymplecticLadder γ dd pp qq PiP PiM w ω)
    (hP : ∀ s h, pp s (-h) = pp s h) (hQ : ∀ u h, qq u (-h) = qq u h)
    (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h) (u h : ℝ) :
    defectRow pp qq AA BB PiP PiM u (-h) 0 = defectRow pp qq AA BB PiP PiM u h 0 ∧
    defectRow pp qq AA BB PiP PiM u (-h) 1 = -defectRow pp qq AA BB PiP PiM u h 1 := by
  obtain ⟨p00, p01, p10, p11, m00, m01, m10, m11⟩ := par_Pi_entries L u h
  have e1 : u + -h / 2 = u - h / 2 := by ring
  have e2 : u - -h / 2 = u + h / 2 := by ring
  have e3 : u + -h = u - h := by ring
  have e4 : u - -h = u + h := by ring
  simp only [defectRow, e1, e2, e3, e4, hP, hQ, vrow, hAe, hBe, p00, p01, p10, p11, m00, m01, m10, m11,
    rowMul, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> ring

/-- `F_cas(s,0) = A(s,0)² V₀(s)` with `V₀(s) = P₀(s) Π₋(s,0)₁₂` (`thm:eng-defect`(3b), value at `h = 0`). -/
theorem Fcas_zero (pp AA BB : ℝ → ℝ → ℝ) (PiM : ℝ → ℝ → M2) (s : ℝ) :
    Fcas pp AA BB PiM s 0 = AA s 0 ^ 2 * (pp s 0 * PiM s 0 0 1) := by
  simp [Fcas, vrow, rowDet, rowMul]
  ring

/-- Evenness of `F_cas` in `h` (`thm:eng-defect`(3b)), at a bond with `𝒟(s,h) ≠ 0`. -/
theorem Fcas_even (L : SymplecticLadder γ dd pp qq PiP PiM w ω)
    (hP : ∀ s h, pp s (-h) = pp s h)
    (hAe : ∀ u h, AA u (-h) = AA u h) (hBe : ∀ u h, BB u (-h) = BB u h) (s h : ℝ)
    (hD : dd s h ≠ 0) :
    Fcas pp AA BB PiM s (-h) = Fcas pp AA BB PiM s h := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + h / 2 := ⟨s - h / 2, by ring⟩
  have hD' : Dp dd u h ≠ 0 := hD
  obtain ⟨p00, p01, p10, p11⟩ := Pp_entries_of_prod L u h hD'
  obtain ⟨_, _, _, _, m00, m01, m10, m11⟩ := par_Pi_entries L u h
  have e1 : u + h / 2 + -h / 2 = u := by ring
  have e2 : u + h / 2 - -h / 2 = u + h := by ring
  have e3 : u + h / 2 + h / 2 = u + h := by ring
  have e4 : u + h / 2 - h / 2 = u := by ring
  simp only [Fcas, e1, e2, e3, e4, hP, vrow, hAe, hBe, rowMul, rowDet, m00, m01, m10, m11, p00, p01, p10, p11,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end Parities

section Casoratian

variable {γ : ℝ} {dd pp qq AA BB : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- The lower shift at the lattice point `u+h`, rewritten at the lattice point `u` (`IsSite γ h u`, `j ≥ 0`); the
lower relation at `u+h` has index `j+1 ≥ 1`, so no bond hypothesis is needed. -/
lemma lower_shift_at_succ (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (u h : ℝ) (hh : 0 < h)
    (hu : IsSite γ h u) (α : Fin 2) :
    Dp dd u h * w α u h 0 = PiM (u + h) h 0 0 * w α (u + h) h 0 + PiM (u + h) h 0 1 * w α (u + h) h 1 ∧
    Dp dd u h * w α u h 1 = PiM (u + h) h 1 0 * w α (u + h) h 0 + PiM (u + h) h 1 1 * w α (u + h) h 1 := by
  have hmDp : Dm dd (u + h) h = Dp dd u h := by
    simp only [Dm, Dp]; congr 1; ring
  have hz := shift_dn_comp L α (u + h) h hh hu.add_h_pos
  have e : u + h - h = u := by ring
  rw [e, hmDp] at hz
  exact hz

/-- **Casoratian identity** (`thm:eng-defect`(3a)): `𝒲_j(ψ̂¹,ψ̂²) = ω_mod(h) 𝓕^tot_cas(s_j,h)` at every lattice point
`u = u_j`, `j ≥ 0` (`IsSite γ h u`), where `s_j = u + h/2`. -/
theorem casSite_eq_omega_Fcas (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (u h : ℝ) (hh : 0 < h)
    (hu : IsSite γ h u) :
    casSite dd pp AA BB w u h = ω h * Fcas pp AA BB PiM (u + h / 2) h := by
  obtain ⟨k00, k01⟩ := lower_shift_at_succ L u h hh hu 0
  obtain ⟨k10, k11⟩ := lower_shift_at_succ L u h hh hu 1
  have e1 : u + h / 2 + h / 2 = u + h := by ring
  have e2 : u + h / 2 - h / 2 = u := by ring
  have wr := L.wronsk_at hh hu.add_h
  have hbin := binet_cauchy (vrow AA BB (u + h) h) (rowMul (vrow AA BB u h) (PiM (u + h) h))
    (w 0 (u + h) h) (w 1 (u + h) h)
  have K0 : Dp dd u h * dot (vrow AA BB u h) (w 0 u h) =
      dot (rowMul (vrow AA BB u h) (PiM (u + h) h)) (w 0 (u + h) h) := by
    simp only [dot, rowMul, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (AA u h) * k00 + (h * BB u h) * k01
  have K1 : Dp dd u h * dot (vrow AA BB u h) (w 1 u h) =
      dot (rowMul (vrow AA BB u h) (PiM (u + h) h)) (w 1 (u + h) h) := by
    simp only [dot, rowMul, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (AA u h) * k10 + (h * BB u h) * k11
  have hb : bondUp dd pp u h = pp (u + h / 2) h * Dp dd u h := rfl
  simp only [casSite, Fcas, e1, e2]
  rw [hb]
  linear_combination (pp (u + h / 2) h * dot (vrow AA BB (u + h) h) (w 0 (u + h) h)) * K1
    - (pp (u + h / 2) h * dot (vrow AA BB (u + h) h) (w 1 (u + h) h)) * K0
    + pp (u + h / 2) h * hbin
    + (pp (u + h / 2) h * rowDet (vrow AA BB (u + h) h) (rowMul (vrow AA BB u h) (PiM (u + h) h))) * wr

end Casoratian

section Green

variable {γ : ℝ} {dd pp qq AA BB : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- **Casoratian--Green identity** (`thm:eng-defect`(3c), `eq:eng-green`), at a point with `𝒟(u+h/2,h) ≠ 0`:
`A(u,h²) 𝔅^tot(u,h) - h B(u,h²) 𝔄^tot(u,h) = -[𝓕_cas(u+h/2,h) - 𝓕_cas(u-h/2,h)]`. -/
theorem green_identity (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (u h : ℝ) (hD : Dp dd u h ≠ 0) :
    AA u h * defectRow pp qq AA BB PiP PiM u h 1 - h * BB u h * defectRow pp qq AA BB PiP PiM u h 0 =
      -(Fcas pp AA BB PiM (u + h / 2) h - Fcas pp AA BB PiM (u - h / 2) h) := by
  obtain ⟨p00, p01, p10, p11⟩ := Pp_entries_of_prod L u h hD
  have e1 : u + h / 2 + h / 2 = u + h := by ring
  have e2 : u + h / 2 - h / 2 = u := by ring
  have e3 : u - h / 2 + h / 2 = u := by ring
  have e4 : u - h / 2 - h / 2 = u - h := by ring
  simp only [defectRow, Fcas, e1, e2, e3, e4, vrow, rowMul, rowDet, p00, p01, p10, p11,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end Green

section Defect

variable {γ : ℝ} {dd pp qq AA BB : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2} {ω : ℝ → ℝ}

/-- **Defect identity, interior form** (`thm:eng-defect`(1), interior `j ≥ 1`): `h (L_h ψ̂)_j = 𝔄^tot w_j + 𝔅^tot w̃_j`,
in the convention `siteLop = h (L_h ψ̂)_j`. -/
theorem defect_identity_interior (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (AA' BB' : ℝ → ℝ → ℝ)
    (α : Fin 2) (u h : ℝ) (hh : 0 < h) (hu : IsSitePos γ h u) :
    siteLop dd pp qq AA' BB' w α u h =
      defectRow pp qq AA' BB' PiP PiM u h 0 * w α u h 0 + defectRow pp qq AA' BB' PiP PiM u h 1 * w α u h 1 := by
  obtain ⟨hy0, hy1⟩ := shift_up_comp L α u h hh hu.isSite
  obtain ⟨hz0, hz1⟩ := shift_dn_comp L α u h hh hu
  simp only [siteLop, bondUp, bondDn, defectRow, dot, rowMul, vrow, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (pp (u + h / 2) h * AA' (u + h) h) * hy0
    + (pp (u + h / 2) h * (h * BB' (u + h) h)) * hy1
    + (pp (u - h / 2) h * AA' (u - h) h) * hz0
    + (pp (u - h / 2) h * (h * BB' (u - h) h)) * hz1

/-- **Defect identity, hard-edge form** (`thm:eng-defect`(1) at `j = 0`, the site `u = γh`): with `𝒟₋(u_0,h) = 0` the
lower bond is absent, and the identity holds for `α = 1` under the annihilation `Π₋(u_0,h) 𝐰^{(1)}_0 = 0`. -/
theorem defect_identity_hard (L : SymplecticLadder γ dd pp qq PiP PiM w ω) (AA' BB' : ℝ → ℝ → ℝ)
    (α : Fin 2) (u h : ℝ) (hh : 0 < h) (hu : u = γ * h) (hD : Dm dd u h = 0) (hann : colMul (PiM u h) (w α u h) = 0) :
    siteLop dd pp qq AA' BB' w α u h =
      defectRow pp qq AA' BB' PiP PiM u h 0 * w α u h 0 + defectRow pp qq AA' BB' PiP PiM u h 1 * w α u h 1 := by
  have hs : IsSite γ h u := ⟨0, by rw [hu]; simp⟩
  obtain ⟨hy0, hy1⟩ := shift_up_comp L α u h hh hs
  have a0 : PiM u h 0 0 * w α u h 0 + PiM u h 0 1 * w α u h 1 = 0 := by
    simpa [colMul] using congrFun hann 0
  have a1 : PiM u h 1 0 * w α u h 0 + PiM u h 1 1 * w α u h 1 = 0 := by
    simpa [colMul] using congrFun hann 1
  simp only [siteLop, bondUp, bondDn, defectRow, dot, rowMul, vrow, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linear_combination (pp (u + h / 2) h * AA' (u + h) h) * hy0
    + (pp (u + h / 2) h * (h * BB' (u + h) h)) * hy1
    + (pp (u - h / 2) h * (AA' (u - h) h * w α (u - h) h 0 + h * BB' (u - h) h * w α (u - h) h 1)) * hD
    - (pp (u - h / 2) h * AA' (u - h) h) * a0
    - (pp (u - h / 2) h * (h * BB' (u - h) h)) * a1

end Defect

section Bridge

/-- The bond coefficient at the lower neighbour is the upper one: `𝒜(s_{j-1})` at `u_j` equals `𝒜(s_{j-1})` at
`u_{j-1}` read as an upper bond. -/
lemma bondUp_sub (dd pp : ℝ → ℝ → ℝ) (u h : ℝ) : bondUp dd pp (u - h) h = bondDn dd pp u h := by
  have e : u - h + h / 2 = u - h / 2 := by ring
  simp only [bondUp, bondDn, Dp, Dm, e]

/-- **Sequence form.** With `u_j = (j+γ)h`, the comparison sequence `ψ̂_j = v(u_j,h)·𝐰^{(α)}(u_j,h)` and the
Jacobi operator `FormalResearch.JacobiEigenvectors.Engine.Lop` of `Casoratian` (bond `A j = 𝒜_h(s_j)`, `Q j = 𝒬_h(u_j)`), the sequence
operator at `j` is `siteLop` at `u_j`.  Hence `thm:eng-defect`(1) holds for the sequence operator. -/
theorem Lop_seq_eq_siteLop (dd pp qq AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (α : Fin 2) (γ h : ℝ) (j : ℤ) :
    FormalResearch.JacobiEigenvectors.Engine.Lop (fun k : ℤ => bondUp dd pp (((k : ℝ) + γ) * h) h)
      (fun k : ℤ => qq (((k : ℝ) + γ) * h) h)
      (fun k : ℤ => dot (vrow AA BB (((k : ℝ) + γ) * h) h) (w α (((k : ℝ) + γ) * h) h)) j
    = siteLop dd pp qq AA BB w α (((j : ℝ) + γ) * h) h := by
  have e1 : (((j + 1 : ℤ) : ℝ) + γ) * h = ((j : ℝ) + γ) * h + h := by push_cast; ring
  have e2 : (((j - 1 : ℤ) : ℝ) + γ) * h = ((j : ℝ) + γ) * h - h := by push_cast; ring
  unfold FormalResearch.JacobiEigenvectors.Engine.Lop siteLop
  simp only []
  rw [e1, e2, bondUp_sub]

end Bridge

/-- Non-vacuity of `SymplecticLadder`: for every shift `γ`, the constant ladder (`𝒟 ≡ P ≡ 1`, `Q ≡ 0`, `Π± = I`,
`𝐰^{(1)} = e₁`, `𝐰^{(2)} = e₂`, `ω_mod ≡ 1`) satisfies every field. -/
theorem constant_ladder (γ : ℝ) :
    SymplecticLadder γ (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ))
      (fun _ _ => (1 : M2)) (fun _ _ => (1 : M2))
      (fun α _ _ => if α = 0 then ![1, 0] else ![0, 1]) (fun _ => (1 : ℝ)) := by
  have colMul_one : ∀ x : V2, colMul (1 : M2) x = x := by
    intro x; funext i; fin_cases i <;> simp [colMul]
  have SgSg : Sg * (1 : M2) * Sg = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h _ j
    simp [colDet]
  · intro h _; norm_num
  · intro α h _ j
    simp only [Dp, one_smul, colMul_one]
  · intro α h _ j _
    simp only [Dm, one_smul, colMul_one]
  · intro u h; simp [Dp]
  · intro u h; simp [Dm]
  · intro u h; simp [Dp]
  · intro u h; rfl
  · intro u h; rw [SgSg]

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JacobiEigenvectors.Engine.defectRow_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.defectRow_parity

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.Fcas_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.Fcas_zero

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.Fcas_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.Fcas_even

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.casSite_eq_omega_Fcas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.casSite_eq_omega_Fcas

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.green_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.green_identity

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.defect_identity_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.defect_identity_interior

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.defect_identity_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.defect_identity_hard

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.Lop_seq_eq_siteLop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.Lop_seq_eq_siteLop

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.constant_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.constant_ladder

end FormalResearch.JacobiEigenvectors.Engine

end

end

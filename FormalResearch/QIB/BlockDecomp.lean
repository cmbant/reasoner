import Mathlib
import FormalResearch.FrameFree.HelstromPure
import FormalResearch.FrameFree.Helstrom
import FormalResearch.QIB.MatrixHelstrom
import FormalResearch.QIB.BlockOps

/-!
# Exact sector decomposition of the invariant error (`lem:blockdecomp`, second formula)

Namespace `FormalResearch.QIB`.  Claim class: **proved under explicit hypothesis**
(`IsotypicInvariants`, the isotypic structure of the invariants: see below).  No new axiom, no Haar
measure, no characters.

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, Lemma `lem:blockdecomp`:
`P_e^K(d) = Σ_λ ½ Tr min(τ_λ^x, τ_λ^y)`, with `Tr min(A,B) = ½(Tr A + Tr B - ‖A-B‖₁)`.

**Setting.**  `G` is any set of matrices on the coordinates `Idx A B = Σ λ, A λ × B λ` of
`⊕_λ V_λ ⊗ M_λ`.  The hypothesis `IsotypicInvariants A G` says that the matrices commuting with every
`U ∈ G` are exactly the block operators `⊕_λ I_{V_λ} ⊗ X_λ`.  This is what Schur's lemma gives for
`G` acting by `⊕ u_λ ⊗ I` on pairwise inequivalent irreducible carriers (the paper's "Schur's lemma ...
orthogonality of the isotypic blocks"); it is a *hypothesis* in this file.  It is discharged, in unitary
coordinates `W`, for every conjugate-transpose-closed `G` (in particular the frame group) by
`BlockStructure.exists_isotypic_coordinates` and `BlockCoordinates.exists_isotypic_invariants` /
`BlockCoordinates.Pe_blockdecomp` (structure theorem of the commutant `*`-algebra; no Schur-Weyl).

* `invErr G a b`: the best equal-prior error of a `G`-invariant effect `0 ≤ E ≤ 1` between the vectors
  `a, b` (the paper's `P_e^K(d)` for `a = x^{⊗d}`, `b = y^{⊗d}`); `Helstrom.Pe` is the instance for
  `rotK` (`Pe_eq_invErr`).
* `invErr_eq`: `invErr G a b = ½ Σ_λ trMin (τ_λ a) (τ_λ b)`, with `τ_λ v = tau v λ`.
* `invErr_eq_one_sub`: for unit vectors, `P_e = ½ (1 - ½ Σ_λ ‖τ_λ a - τ_λ b‖₁)`
  (paper eq. `eq:helstrom-twirls` read blockwise).  The optimal test (inside the proof of `invErr_eq`)
  is `⊕ I ⊗ Π_λ^-`, `Π_λ^-` the negative spectral projector of `τ_λ a - τ_λ b`.
* `sum_trace_tau`: `Σ_λ Tr τ_λ(v) = ⟨v|v⟩`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect qf err)

/-- Best equal-prior error of a `G`-invariant effect between `a` and `b`. -/
noncomputable def invErr {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Set (Matrix ι ι ℂ))
    (a b : ι → ℂ) : ℝ :=
  sInf {r | ∃ E, IsEffect E ∧ (∀ U ∈ G, U * E = E * U) ∧ r = err E a b}

section Blocks

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- **Isotypic hypothesis.**  The commutant of `G` is exactly the set of block operators
`⊕_λ I_{A λ} ⊗ X_λ` (Schur's lemma for pairwise inequivalent irreducible carriers). -/
def IsotypicInvariants (A : Λ → Type*) [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)]
    (G : Set (Matrix (Idx A B) (Idx A B) ℂ)) : Prop :=
  ∀ M, (∀ U ∈ G, U * M = M * U) ↔ ∃ X : ∀ l, Matrix (B l) (B l) ℂ, M = blockOp A X

/-- Error of a block test. -/
theorem err_blockOp (X : ∀ l, Matrix (B l) (B l) ℂ) (a b : Idx A B → ℂ) :
    err (blockOp A X) a b =
      (∑ l, (X l * tau a l).trace).re / 2 +
        (∑ l, ((1 - X l) * tau b l).trace).re / 2 := by
  unfold err
  have e : (1 : Matrix (Idx A B) (Idx A B) ℂ) - blockOp A X =
      blockOp A (fun l => (1 : Matrix (B l) (B l) ℂ) - X l) := by
    rw [blockOp_sub, blockOp_one]
  rw [e, qf_blockOp_self, qf_blockOp_self]

theorem err_blockOp_sum (X : ∀ l, Matrix (B l) (B l) ℂ) (a b : Idx A B → ℂ) :
    err (blockOp A X) a b =
      (1 / 2) * ∑ l, ((X l * tau a l).trace.re + ((1 - X l) * tau b l).trace.re) := by
  rw [err_blockOp, Complex.re_sum, Complex.re_sum, Finset.sum_add_distrib]
  ring

/-- Per-sector Helstrom: the sector error of an effect is at least `trMin`. -/
theorem sector_ge {m : Type*} [Fintype m] [DecidableEq m] {τa τb : Matrix m m ℂ}
    (ha : τa.IsHermitian) (hb : τb.IsHermitian) {X : Matrix m m ℂ} (hX : IsEffect X) :
    trMin τa τb ≤ (X * τa).trace.re + ((1 - X) * τb).trace.re := by
  have hD : (τa - τb).IsHermitian := ha.sub hb
  have h := trace_mul_ge hD hX
  have e : ((1 - X) * τb).trace = τb.trace - (X * τb).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  have e2 : (X * (τa - τb)).trace = (X * τa).trace - (X * τb).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [e2, Matrix.trace_sub] at h
  rw [e]
  unfold trMin
  simp only [Complex.sub_re] at h ⊢
  linarith

theorem sector_attain {m : Type*} [Fintype m] [DecidableEq m] {τa τb : Matrix m m ℂ}
    (ha : τa.IsHermitian) (hb : τb.IsHermitian) :
    ∃ X : Matrix m m ℂ, IsEffect X ∧
      (X * τa).trace.re + ((1 - X) * τb).trace.re = trMin τa τb := by
  obtain ⟨X, hX, hXe⟩ := exists_effect_trace_mul_eq (ha.sub hb)
  refine ⟨X, hX, ?_⟩
  have e : ((1 - X) * τb).trace = τb.trace - (X * τb).trace := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  have e2 : (X * (τa - τb)).trace = (X * τa).trace - (X * τb).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [e2, Matrix.trace_sub] at hXe
  rw [e]
  unfold trMin
  simp only [Complex.sub_re] at hXe ⊢
  linarith

/-- **`lem:blockdecomp`, second formula.**  Under the isotypic hypothesis, the optimal invariant error
is `½ Σ_λ Tr min(τ_λ^a, τ_λ^b)`. -/
theorem invErr_eq [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (a b : Idx A B → ℂ) :
    invErr G a b = (1 / 2) * ∑ l, trMin (tau a l) (tau b l) := by
  unfold invErr
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · -- attained
    choose X hXe hXv using fun l => sector_attain (tau_isHermitian a l) (tau_isHermitian b l)
    refine ⟨blockOp A X, ?_, fun U hU => (hG _).2 ⟨X, rfl⟩ U hU, ?_⟩
    · exact (blockOp_isEffect_iff X).2 hXe
    · rw [err_blockOp_sum]
      simp only [hXv]
  · rintro r ⟨E, hE, hEinv, rfl⟩
    obtain ⟨X, rfl⟩ := (hG E).1 hEinv
    have hXe := (blockOp_isEffect_iff X).1 hE
    rw [err_blockOp_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by norm_num)
    exact sector_ge (tau_isHermitian a l) (tau_isHermitian b l) (hXe l)

/-- The sector masses sum to the squared norm: `Σ_λ Tr τ_λ(v) = ⟨v|v⟩`. -/
theorem sum_trace_tau (v : Idx A B → ℂ) : ∑ l, (tau v l).trace = star v ⬝ᵥ v := by
  have h := qf_blockOp_self (A := A) (fun l => (1 : Matrix (B l) (B l) ℂ)) v
  rw [blockOp_one, FormalResearch.FrameFree.Helstrom.qf_one] at h
  simpa using h.symm

/-- **`lem:blockdecomp`, `‖·‖₁` form** (paper eq. `eq:helstrom-twirls` read blockwise): for unit vectors,
`P_e = ½ (1 - ½ Σ_λ ‖τ_λ^a - τ_λ^b‖₁)`. -/
theorem invErr_eq_one_sub [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {a b : Idx A B → ℂ} (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    invErr G a b = (1 / 2) * (1 - (1 / 2) * ∑ l, tnorm (tau a l - tau b l)) := by
  rw [invErr_eq hG]
  have h1 := congrArg Complex.re (sum_trace_tau a)
  have h2 := congrArg Complex.re (sum_trace_tau b)
  rw [ha, Complex.re_sum] at h1
  rw [hb, Complex.re_sum] at h2
  unfold trMin
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  simp
  ring

end Blocks

/-! ### The existing `Helstrom.Pe` is the instance `G = {rotK k u}` -/

open FormalResearch.FrameFree.Helstrom (Pe rotK copies IsInvEffect)
open FormalResearch.FrameFree.NQubit (Ψ Θ SU2 Op1)

/-- The frame group `{⊗_a u_a^{⊗k} : u ∈ SU(2)^n}` on `k` copies of `n` qubits. -/
def frameGroup (n k : ℕ) : Set (Matrix (Fin k → Fin n → Fin 2) (Fin k → Fin n → Fin 2) ℂ) :=
  {M | ∃ u : Fin n → Op1, (∀ i, SU2 (u i)) ∧ M = rotK k u}

/-- `Helstrom.Pe k ψ` (best `SU(2)^n`-invariant test between `ψ^{⊗k}` and `(Θψ)^{⊗k}`) is `invErr` of
the frame group. -/
theorem Pe_eq_invErr {n : ℕ} (k : ℕ) (ψ : Ψ n) :
    Pe k ψ = invErr (frameGroup n k) (copies k ψ) (copies k (Θ ψ)) := by
  unfold Pe invErr
  congr 1
  ext r
  constructor
  · rintro ⟨E, ⟨hE, hc⟩, hr⟩
    exact ⟨E, hE, fun U ⟨u, hu, hUu⟩ => hUu ▸ hc u hu, hr⟩
  · rintro ⟨E, hE, hc, hr⟩
    exact ⟨E, ⟨hE, fun u hu => hc _ ⟨u, hu, rfl⟩⟩, hr⟩

end FormalResearch.QIB

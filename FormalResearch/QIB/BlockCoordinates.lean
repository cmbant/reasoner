import Mathlib
import FormalResearch.QIB.BlockStructure
import FormalResearch.QIB.BlockDecomp
import FormalResearch.QIB.BlockAntiunitary
import FormalResearch.FrameFree.HelstromSupport

/-!
# Discharging `IsotypicInvariants`: unitary isotypic coordinates for the frame group

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

`BlockDecomp.lean` proves the QI-B block formulas under the hypothesis `IsotypicInvariants A G`
(the commutant of `G` is `{⊕_λ I_{A λ} ⊗ X_λ}`).  `BlockStructure.lean` proves the structure theorem
for any `*`-closed algebra; this file transports it to a group of matrices and applies it.

* `transportSet W G = {Wᴴ U W : U ∈ G}` and `invErr_transport`: for `Wᴴ W = 1 = W Wᴴ`,
  `invErr (transportSet W G) (Wᴴ a) (Wᴴ b) = invErr G a b` (coordinate invariance of the optimal
  invariant error; effects, commutation and `err` are all transported).
* `exists_isotypic_invariants`: for **every** conjugate-transpose-closed set `G` of matrices (every
  group of unitaries) there are unitary coordinates `W` onto `Σ l, Fin (a l) × Fin (b l)` with all
  `a l > 0` such that `IsotypicInvariants (fun l => Fin (a l)) (transportSet W G)`.  The index family
  is the *isotypic labelling of the commutant `G'`* (`b l` = dimension of the `l`-th simple
  `G'`-module, `a l` its multiplicity); it is not named (not Young diagrams), which `lem:blockdecomp`
  does not need.
* `Pe_blockdecomp`: for the concrete frame group of `Helstrom.Pe` (`rotK k u`, `u ∈ SU(2)^n`,
  `k` copies of `n` qubits), `P_e(k) = ½ Σ_l Tr min(τ_l(ψ^{⊗k}), τ_l((Θψ)^{⊗k}))` unconditionally, and
  for unit `ψ` the trace-norm form, in the coordinates `W`.

That `W` can be taken *real* (so that `Θ`, an entrywise conjugation up to the frame element
`ε^{⊗n} ∈ SU(2)^n`, acts as entrywise conjugation of the multiplicity blocks) is not proved here; it is
`RealCoordsFrame.realIsotypicCoords`, which discharges the hypothesis `hconj` of `antiunitary_block`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect qf err)

section Transport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The set `{Wᴴ U W : U ∈ G}`: the matrices of `G` in the coordinates `W`. -/
def transportSet (W : Matrix ι κ ℂ) (G : Set (Matrix ι ι ℂ)) : Set (Matrix κ κ ℂ) :=
  {U' | ∃ U ∈ G, U' = Wᴴ * U * W}

variable {W : Matrix ι κ ℂ}

theorem conj_inj (hW1 : Wᴴ * W = 1) {X Y : Matrix κ κ ℂ} (h : W * X * Wᴴ = W * Y * Wᴴ) : X = Y := by
  have e : ∀ Z : Matrix κ κ ℂ, Z = Wᴴ * (W * Z * Wᴴ) * W := by
    intro Z
    have : Wᴴ * (W * Z * Wᴴ) * W = (Wᴴ * W) * Z * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
    rw [this, hW1]; simp
  rw [e X, e Y, h]

theorem comm_conj_iff (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (U : Matrix ι ι ℂ)
    (M : Matrix κ κ ℂ) :
    (Wᴴ * U * W) * M = M * (Wᴴ * U * W) ↔ U * (W * M * Wᴴ) = (W * M * Wᴴ) * U := by
  have e1 : W * ((Wᴴ * U * W) * M) * Wᴴ = (W * Wᴴ) * U * (W * M * Wᴴ) := by
    simp only [Matrix.mul_assoc]
  have e2 : W * (M * (Wᴴ * U * W)) * Wᴴ = (W * M * Wᴴ) * U * (W * Wᴴ) := by
    simp only [Matrix.mul_assoc]
  constructor
  · intro h
    have := congrArg (fun X => W * X * Wᴴ) h
    simp only [e1, e2, hW2, Matrix.one_mul, Matrix.mul_one] at this
    exact this
  · intro h
    refine conj_inj hW1 ?_
    rw [e1, e2, hW2, Matrix.one_mul, Matrix.mul_one]
    exact h

theorem isEffect_conj (hW1 : Wᴴ * W = 1) {E : Matrix ι ι ℂ} (hE : IsEffect E) :
    IsEffect (Wᴴ * E * W) := by
  refine ⟨hE.1.conjTranspose_mul_mul_same W, ?_⟩
  have : 1 - Wᴴ * E * W = Wᴴ * (1 - E) * W := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hW1]
  rw [this]
  exact hE.2.conjTranspose_mul_mul_same W

theorem isEffect_conj_back (hW2 : W * Wᴴ = 1) {E : Matrix κ κ ℂ} (hE : IsEffect E) :
    IsEffect (W * E * Wᴴ) := by
  refine ⟨hE.1.mul_mul_conjTranspose_same W, ?_⟩
  have : 1 - W * E * Wᴴ = W * (1 - E) * Wᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hW2]
  rw [this]
  exact hE.2.mul_mul_conjTranspose_same W

theorem star_mulVec_dot (a : ι → ℂ) (w : κ → ℂ) : star (Wᴴ *ᵥ a) ⬝ᵥ w = star a ⬝ᵥ (W *ᵥ w) := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose]

theorem qf_conj (hW2 : W * Wᴴ = 1) (M : Matrix ι ι ℂ) (a b : ι → ℂ) :
    qf (Wᴴ * M * W) (Wᴴ *ᵥ a) (Wᴴ *ᵥ b) = qf M a b := by
  unfold qf
  rw [star_mulVec_dot]
  simp only [Matrix.mulVec_mulVec]
  have : W * (Wᴴ * M * W * Wᴴ) = M := by
    have : W * (Wᴴ * M * W * Wᴴ) = (W * Wᴴ) * M * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
    rw [this, hW2]; simp
  rw [this]

theorem err_conj (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (E : Matrix ι ι ℂ) (a b : ι → ℂ) :
    err (Wᴴ * E * W) (Wᴴ *ᵥ a) (Wᴴ *ᵥ b) = err E a b := by
  unfold err
  have : 1 - Wᴴ * E * W = Wᴴ * (1 - E) * W := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hW1]
  rw [this, qf_conj hW2, qf_conj hW2]

/-- **Coordinate change for the invariant error.**  For a unitary `W` (`Wᴴ W = 1 = W Wᴴ`),
`invErr` of the transported group at the transported vectors equals `invErr G a b`. -/
theorem invErr_transport (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (G : Set (Matrix ι ι ℂ))
    (a b : ι → ℂ) :
    invErr (transportSet W G) (Wᴴ *ᵥ a) (Wᴴ *ᵥ b) = invErr G a b := by
  unfold invErr
  congr 1
  ext r
  constructor
  · rintro ⟨E', hE', hc, rfl⟩
    refine ⟨W * E' * Wᴴ, isEffect_conj_back hW2 hE', ?_, ?_⟩
    · intro U hU
      have := hc (Wᴴ * U * W) ⟨U, hU, rfl⟩
      exact (comm_conj_iff hW1 hW2 U E').1 this
    · have e : Wᴴ * (W * E' * Wᴴ) * W = E' := by
        have : Wᴴ * (W * E' * Wᴴ) * W = (Wᴴ * W) * E' * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
        rw [this, hW1]; simp
      rw [← err_conj hW1 hW2, e]
  · rintro ⟨E, hE, hc, rfl⟩
    refine ⟨Wᴴ * E * W, isEffect_conj hW1 hE, ?_, (err_conj hW1 hW2 E a b).symm⟩
    rintro _ ⟨U, hU, rfl⟩
    have h1 := hc U hU
    have : W * (Wᴴ * E * W) * Wᴴ = E := by
      have : W * (Wᴴ * E * W) * Wᴴ = (W * Wᴴ) * E * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
      rw [this, hW2]; simp
    rw [comm_conj_iff hW1 hW2 U (Wᴴ * E * W), this]
    exact h1


/-- The unit-vector hypothesis survives a unitary change of coordinates. -/
theorem star_dot_transport (hW2 : W * Wᴴ = 1) {a : ι → ℂ} (ha : star a ⬝ᵥ a = 1) :
    star (Wᴴ *ᵥ a) ⬝ᵥ (Wᴴ *ᵥ a) = 1 := by
  rw [star_mulVec_dot, Matrix.mulVec_mulVec, hW2, Matrix.one_mulVec, ha]

theorem conj_back (hW1 : Wᴴ * W = 1) (Z : Matrix κ κ ℂ) : Wᴴ * (W * Z * Wᴴ) * W = Z := by
  have : Wᴴ * (W * Z * Wᴴ) * W = (Wᴴ * W) * Z * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
  rw [this, hW1]; simp

end Transport

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Discharge of `IsotypicInvariants` for every `*`-closed set of matrices.**  If `G` is closed under
the conjugate transpose (e.g. any group of unitaries), then in suitable unitary coordinates `W` the
commutant of `G` is exactly the set of block operators `⊕_l I_{a_l} ⊗ X_l`, `X_l` ranging over all
`b_l × b_l` matrices, with every carrier `Fin (a l)` nonempty. -/
theorem exists_isotypic_invariants (G : Set (Matrix ι ι ℂ)) (hG : ∀ U ∈ G, Uᴴ ∈ G) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix ι (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W G) := by
  let C : Subalgebra ℂ (Matrix ι ι ℂ) := Subalgebra.centralizer ℂ G
  have hC : ∀ c ∈ C, cᴴ ∈ C := by
    intro c hc
    rw [Subalgebra.mem_centralizer_iff] at hc ⊢
    intro g hg
    have h2 := congrArg Matrix.conjTranspose (hc gᴴ (hG g hg))
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose] at h2
    exact h2.symm
  obtain ⟨r, a, b, W, ha, hW1, hW2, hM⟩ := exists_isotypic_coordinates hC
  refine ⟨r, a, b, W, ha, hW1, hW2, fun M' => ?_⟩
  have h1 : (∀ U' ∈ transportSet W G, U' * M' = M' * U') ↔ W * M' * Wᴴ ∈ C := by
    rw [Subalgebra.mem_centralizer_iff]
    constructor
    · intro h g hg
      exact (comm_conj_iff hW1 hW2 g M').1 (h _ ⟨g, hg, rfl⟩)
    · rintro h _ ⟨g, hg, rfl⟩
      exact (comm_conj_iff hW1 hW2 g M').2 (h g hg)
  rw [h1, hM]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, by rw [← conj_back hW1 M']; exact hX⟩
  · rintro ⟨X, rfl⟩
    exact ⟨X, by rw [conj_back hW1]⟩


end Main

section FrameGroup

open FormalResearch.FrameFree.Helstrom (Pe rotK copies Copies)
open FormalResearch.FrameFree.NQubit (Ψ Θ SU2 Op1 nsq)

theorem frameGroup_star_closed (n k : ℕ) : ∀ U ∈ frameGroup n k, Uᴴ ∈ frameGroup n k := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨fun i => (u i)ᴴ, fun i => FormalResearch.FrameFree.NQubit.SU2_adjoint (hu i),
    FormalResearch.FrameFree.Helstrom.rotK_conjTranspose k u⟩

/-- **Unconditional sector decomposition of the frame-group error** (`lem:blockdecomp`, second formula,
for the concrete group `{rotK k u : u ∈ SU(2)^n}` on `k` copies of `n` qubits).  There are unitary
isotypic coordinates `W` (independent of `ψ`) in which the commutant of the frame group is the full
block algebra `⊕_l I_{a_l} ⊗ M_{b_l}(ℂ)` and

`P_e(k) = ½ Σ_l Tr min(τ_l(ψ^{⊗k}), τ_l((Θψ)^{⊗k}))`,  `τ_l v = Σ_α |v_{lα}⟩⟨v_{lα}|`,

with `v = Wᴴ (·)` the coordinates of the vector.  For unit `ψ` the `‖·‖₁` form
`P_e = ½ (1 - ½ Σ_l ‖τ_l^a - τ_l^b‖₁)` holds as well. -/
theorem Pe_blockdecomp (n k : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ ψ : Ψ n,
        Pe k ψ = (1 / 2) * ∑ l, trMin (tau (Wᴴ *ᵥ copies k ψ) l) (tau (Wᴴ *ᵥ copies k (Θ ψ)) l) ∧
        (nsq ψ = 1 → Pe k ψ = (1 / 2) * (1 - (1 / 2) * ∑ l,
          tnorm (tau (Wᴴ *ᵥ copies k ψ) l - tau (Wᴴ *ᵥ copies k (Θ ψ)) l))) := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hG⟩ :=
    exists_isotypic_invariants (frameGroup n k) (frameGroup_star_closed n k)
  refine ⟨r, a, b, W, ha, hW1, hW2, hG, fun ψ => ?_⟩
  have : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  have hPe : Pe k ψ = invErr (transportSet W (frameGroup n k)) (Wᴴ *ᵥ copies k ψ)
      (Wᴴ *ᵥ copies k (Θ ψ)) := by
    rw [invErr_transport hW1 hW2, Pe_eq_invErr]
  refine ⟨by rw [hPe, invErr_eq hG], fun hψ => ?_⟩
  have h1 : star (copies k ψ) ⬝ᵥ copies k ψ = 1 :=
    FormalResearch.FrameFree.Helstrom.star_copies_self k ψ hψ
  have h2 : star (copies k (Θ ψ)) ⬝ᵥ copies k (Θ ψ) = 1 :=
    FormalResearch.FrameFree.Helstrom.star_copies_self k (Θ ψ)
      (by rw [FormalResearch.FrameFree.NQubit.nsq_Θ]; exact hψ)
  rw [hPe, invErr_eq_one_sub hG (star_dot_transport hW2 h1) (star_dot_transport hW2 h2)]

end FrameGroup

end FormalResearch.QIB

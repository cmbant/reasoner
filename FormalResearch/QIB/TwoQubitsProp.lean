import Mathlib
import FormalResearch.QIB.TwoQubitsDecomp
import FormalResearch.QIB.TwoQubitsSectorIrr
import FormalResearch.QIB.TwoQubitsStabiliser
import FormalResearch.QIB.BlockCoordinates
import FormalResearch.QIB.EasyRankOneSandwich

/-!
# `prop:twoqubits`: two qubits under collective `SU(2)` have multiplicity blocks of rank at most one

Namespace `FormalResearch.QIB.TwoQubits`.  Claim class: **proved** (finite linear algebra; no
exponentials, no analysis, no Lean-external input).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `prop:twoqubits`.

The collective group is `Gcoll d = {u^{⊗ 2d} : u ∈ SU(2)}` on `(ℂ²⊗ℂ²)^{⊗ d}` (`Copies 2 d`).  For *any*
isotypic coordinates `W` of it (`IsotypicInvariants A (transportSet W (Gcoll d))`, `Wᴴ W = 1 = W Wᴴ`), and
every two-qubit vector `ψ` and every `d`, every multiplicity block `τ_l((Wᴴ ψ^{⊗ d}))` has rank at most
one: `twoqubits_rank_le_one`.  `exists_twoqubits_coordinates` produces such coordinates (from
`BlockCoordinates.exists_isotypic_invariants`).

Proof (the stabiliser argument of the paper, in matrix form): `𝓗, 𝓔, 𝓕` are the collective `sl₂`
generators in the coordinates `W`.  `L1` (commutant of the group commutes with `Lc H₁, Lc E₁, Lc F₁`) and
`L2` (converse) are `commute_Lc_of_commGroup` and `commGroup_of_commute_Lc`; they make each sector carrier
an irreducible `sl₂`-module (`TwoQubitsSectorIrr`).  Every two-qubit vector has a nonzero stabiliser in
`sl₂` (`exists_two_qubit_killer`), which by the Leibniz rule kills `ψ^{⊗ d}` (`Lc_mulVec_copies`); its
kernel on an irreducible module is at most one-dimensional (`Sl2Kernel.kernel_sl2`, with no
semisimple/nilpotent case split), so `τ_l` has rank at most one (`rank_tau_le_one_of_stabiliser`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Matrix
open FormalResearch.FrameFree.NQubit (SU2 Op1 Ψ)
open FormalResearch.FrameFree.Helstrom

namespace FormalResearch.QIB.TwoQubits

section Transport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {W : Matrix ι κ ℂ}

theorem conjW_mul (hW2 : W * Wᴴ = 1) (X Y : Matrix ι ι ℂ) :
    (Wᴴ * X * W) * (Wᴴ * Y * W) = Wᴴ * (X * Y) * W := by
  calc (Wᴴ * X * W) * (Wᴴ * Y * W) = Wᴴ * X * (W * Wᴴ) * Y * W := by simp only [Matrix.mul_assoc]
    _ = Wᴴ * (X * Y) * W := by rw [hW2, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem conjW_mul' (hW1 : Wᴴ * W = 1) (A B : Matrix κ κ ℂ) :
    (W * A * Wᴴ) * (W * B * Wᴴ) = W * (A * B) * Wᴴ := by
  calc (W * A * Wᴴ) * (W * B * Wᴴ) = W * A * (Wᴴ * W) * B * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = W * (A * B) * Wᴴ := by rw [hW1, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem commute_conjW_iff (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) {M : Matrix κ κ ℂ}
    {X : Matrix ι ι ℂ} : Commute M (Wᴴ * X * W) ↔ Commute (W * M * Wᴴ) X := by
  have hX : W * (Wᴴ * X * W) * Wᴴ = X := by
    calc W * (Wᴴ * X * W) * Wᴴ = (W * Wᴴ) * X * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hW2, Matrix.one_mul, Matrix.mul_one]
  have hM : Wᴴ * (W * M * Wᴴ) * W = M := by
    calc Wᴴ * (W * M * Wᴴ) * W = (Wᴴ * W) * M * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hW1, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro h
    have := congrArg (fun Z => W * Z * Wᴴ) h.eq
    rw [← conjW_mul' hW1, ← conjW_mul' hW1, hX] at this
    exact this
  · intro h
    have := congrArg (fun Z => Wᴴ * Z * W) h.eq
    rw [← conjW_mul hW2, ← conjW_mul hW2, hM] at this
    exact this

theorem conjW_sub (X Y : Matrix ι ι ℂ) : Wᴴ * (X - Y) * W = Wᴴ * X * W - Wᴴ * Y * W := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem conjW_add (X Y : Matrix ι ι ℂ) : Wᴴ * (X + Y) * W = Wᴴ * X * W + Wᴴ * Y * W := by
  rw [Matrix.mul_add, Matrix.add_mul]

theorem conjW_smul (c : ℂ) (X : Matrix ι ι ℂ) : Wᴴ * (c • X) * W = c • (Wᴴ * X * W) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem conjW_neg (X : Matrix ι ι ℂ) : Wᴴ * (-X) * W = -(Wᴴ * X * W) := by
  rw [Matrix.mul_neg, Matrix.neg_mul]

theorem conjW_conjTranspose (X : Matrix ι ι ℂ) : (Wᴴ * X * W)ᴴ = Wᴴ * Xᴴ * W := by
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Transport

theorem H1_conjTranspose : H1ᴴ = H1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H1, conjTranspose_apply]

theorem E1_conjTranspose : E1ᴴ = F1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E1, F1, conjTranspose_apply]

section Main

variable {d : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- **`prop:twoqubits`, product form.**  In any isotypic coordinates `W` of the collective `SU(2)` on
`d` copies of two qubits, every multiplicity block of `ψ^{⊗ d}` is `|u⟩⟨u|` for some `u`, for every
two-qubit vector `ψ` (in particular of rank at most one: `twoqubits_rank_le_one`). -/
theorem twoqubits_tau_eq_vecMulVec (W : Matrix (Copies 2 d) (Idx A B) ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W (Gcoll d)))
    (ψ : Ψ 2) (l : Λ) [Nonempty (A l)] :
    ∃ u : B l → ℂ, tau (Wᴴ *ᵥ copies d ψ) l = Matrix.vecMulVec u (star u) := by
  by_cases hB : Nonempty (B l)
  swap
  · have he : IsEmpty (B l) := not_nonempty_iff.1 hB
    exact ⟨fun b => he.elim b, Subsingleton.elim _ _⟩
  obtain ⟨b0⟩ := hB
  obtain ⟨α, β, γ, hne, hkill⟩ := exists_two_qubit_killer ψ
  have hLc : Lc d (α • H1 + β • E1 + γ • F1) *ᵥ copies d ψ = 0 := Lc_mulVec_copies d _ ψ hkill
  have htrip := Lc_matTriple (d := d) matTriple_H1E1F1
  have hHE : (Wᴴ * Lc d H1 * W) * (Wᴴ * Lc d E1 * W) - (Wᴴ * Lc d E1 * W) * (Wᴴ * Lc d H1 * W)
      = (2 : ℂ) • (Wᴴ * Lc d E1 * W) := by
    rw [conjW_mul hW2, conjW_mul hW2, ← conjW_sub, htrip.HE, conjW_smul]
  have hHF : (Wᴴ * Lc d H1 * W) * (Wᴴ * Lc d F1 * W) - (Wᴴ * Lc d F1 * W) * (Wᴴ * Lc d H1 * W)
      = -((2 : ℂ) • (Wᴴ * Lc d F1 * W)) := by
    rw [conjW_mul hW2, conjW_mul hW2, ← conjW_sub, htrip.HF, conjW_neg, conjW_smul]
  have hEF : (Wᴴ * Lc d E1 * W) * (Wᴴ * Lc d F1 * W) - (Wᴴ * Lc d F1 * W) * (Wᴴ * Lc d E1 * W)
      = Wᴴ * Lc d H1 * W := by
    rw [conjW_mul hW2, conjW_mul hW2, ← conjW_sub, htrip.EF]
  have hHh : (Wᴴ * Lc d H1 * W)ᴴ = Wᴴ * Lc d H1 * W := by
    rw [conjW_conjTranspose, Lc_conjTranspose, H1_conjTranspose]
  have hEh : (Wᴴ * Lc d E1 * W)ᴴ = Wᴴ * Lc d F1 * W := by
    rw [conjW_conjTranspose, Lc_conjTranspose, E1_conjTranspose]
  have hL1 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ,
      (∀ U ∈ transportSet W (Gcoll d), U * M = M * U) →
      M * (Wᴴ * Lc d H1 * W) = (Wᴴ * Lc d H1 * W) * M ∧
      M * (Wᴴ * Lc d E1 * W) = (Wᴴ * Lc d E1 * W) * M ∧
      M * (Wᴴ * Lc d F1 * W) = (Wᴴ * Lc d F1 * W) * M := by
    intro M hM
    have hM' : CommGroup d (W * M * Wᴴ) := by
      intro u hu
      have h := hM (Wᴴ * rotK d (fun _ : Fin 2 => u) * W) ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact (commute_conjW_iff hW1 hW2).1 (show Commute M _ from h.symm)
    obtain ⟨c1, c2, c3⟩ := commute_Lc_of_commGroup hM'
    exact ⟨((commute_conjW_iff hW1 hW2).2 c1).eq, ((commute_conjW_iff hW1 hW2).2 c2).eq,
      ((commute_conjW_iff hW1 hW2).2 c3).eq⟩
  have hL2 : ∀ M : Matrix (Idx A B) (Idx A B) ℂ,
      M * (Wᴴ * Lc d H1 * W) = (Wᴴ * Lc d H1 * W) * M →
      M * (Wᴴ * Lc d E1 * W) = (Wᴴ * Lc d E1 * W) * M →
      M * (Wᴴ * Lc d F1 * W) = (Wᴴ * Lc d F1 * W) * M →
      ∀ U ∈ transportSet W (Gcoll d), U * M = M * U := by
    intro M h1 h2 h3 U hU
    obtain ⟨U0, ⟨u, hu, rfl⟩, rfl⟩ := hU
    have c1 := (commute_conjW_iff hW1 hW2).1 (show Commute M _ from h1)
    have c2 := (commute_conjW_iff hW1 hW2).1 (show Commute M _ from h2)
    have c3 := (commute_conjW_iff hW1 hW2).1 (show Commute M _ from h3)
    have c := commGroup_of_commute_Lc c1 c2 c3 u hu
    exact ((commute_conjW_iff hW1 hW2).2 c).eq.symm
  have hv : (α • (Wᴴ * Lc d H1 * W) + β • (Wᴴ * Lc d E1 * W) + γ • (Wᴴ * Lc d F1 * W)) *ᵥ
      (Wᴴ *ᵥ copies d ψ) = 0 := by
    have e : α • (Wᴴ * Lc d H1 * W) + β • (Wᴴ * Lc d E1 * W) + γ • (Wᴴ * Lc d F1 * W)
        = Wᴴ * Lc d (α • H1 + β • E1 + γ • F1) * W := by
      rw [Lc_add, Lc_add, Lc_smul, Lc_smul, Lc_smul, conjW_add, conjW_add, conjW_smul,
        conjW_smul, conjW_smul]
    rw [e, Matrix.mulVec_mulVec]
    have e2 : Wᴴ * Lc d (α • H1 + β • E1 + γ • F1) * W * Wᴴ = Wᴴ * Lc d (α • H1 + β • E1 + γ • F1) := by
      rw [Matrix.mul_assoc _ W Wᴴ, hW2, Matrix.mul_one]
    rw [e2, ← Matrix.mulVec_mulVec, hLc, Matrix.mulVec_zero]
  exact exists_vecMulVec_of_group hG hHE hHF hEF hHh hEh hL1 hL2 l b0 α β γ hne _ hv

/-- **`prop:twoqubits`.**  Every multiplicity block of `ψ^{⊗ d}` has rank at most one. -/
theorem twoqubits_rank_le_one (W : Matrix (Copies 2 d) (Idx A B) ℂ) (hW1 : Wᴴ * W = 1)
    (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W (Gcoll d)))
    (ψ : Ψ 2) (l : Λ) [Nonempty (A l)] : (tau (Wᴴ *ᵥ copies d ψ) l).rank ≤ 1 := by
  obtain ⟨u, hu⟩ := twoqubits_tau_eq_vecMulVec W hW1 hW2 hG ψ l
  rw [hu]
  exact Matrix.rank_vecMulVec_le _ _

/-- **"Therefore the rank-one sandwich applies".**  For two-qubit vectors `ψ, φ` and the collective
`SU(2)`, the optimal invariant error between `ψ^{⊗ d}` and `φ^{⊗ d}` satisfies
`¼ S ≤ P_e ≤ ½ S`, `S = Σ_l |⟨u_l, v_l⟩|² / max(‖u_l‖², ‖v_l‖²)`, with `u_l, v_l` the product vectors
of the two multiplicity blocks. -/
theorem twoqubits_sandwich [∀ l, Nonempty (A l)] (W : Matrix (Copies 2 d) (Idx A B) ℂ)
    (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (hG : IsotypicInvariants A (transportSet W (Gcoll d)))
    (ψ φ : Ψ 2) :
    ∃ u v : ∀ l, B l → ℂ,
      (1 / 4) * ∑ l, rankOneTerm (u l) (v l) ≤
          invErr (transportSet W (Gcoll d)) (Wᴴ *ᵥ copies d ψ) (Wᴴ *ᵥ copies d φ) ∧
        invErr (transportSet W (Gcoll d)) (Wᴴ *ᵥ copies d ψ) (Wᴴ *ᵥ copies d φ) ≤
          (1 / 2) * ∑ l, rankOneTerm (u l) (v l) := by
  choose u hu using fun l => twoqubits_tau_eq_vecMulVec W hW1 hW2 hG ψ l
  choose v hv using fun l => twoqubits_tau_eq_vecMulVec W hW1 hW2 hG φ l
  exact ⟨u, v, invErr_rankOne_sandwich hG _ _ u v hu hv⟩

/-- **Existence of the coordinates.**  There are unitary isotypic coordinates of the collective `SU(2)`
in which the block statement `twoqubits_rank_le_one` holds for all two-qubit `ψ`. -/
theorem exists_twoqubits_coordinates (d : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies 2 d) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (Gcoll d)) ∧
      ∀ (ψ : Ψ 2) (l : Fin r), (tau (Wᴴ *ᵥ copies d ψ) l).rank ≤ 1 := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hG⟩ := exists_isotypic_invariants (Gcoll d) (Gcoll_star_closed d)
  refine ⟨r, a, b, W, ha, hW1, hW2, hG, fun ψ l => ?_⟩
  have : Nonempty (Fin (a l)) := ⟨⟨0, ha l⟩⟩
  exact twoqubits_rank_le_one W hW1 hW2 hG ψ l

end Main

end FormalResearch.QIB.TwoQubits

import Mathlib
import FormalResearch.QIB.BlockDecomp

/-!
# Abelian groups have one-dimensional carriers (the "rank-one blocks" half of `thm:abelian`)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (finite linear algebra, no new axiom).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `thm:abelian` ("every total-weight block of
a pure-state twirl has rank one") and `prop:collapseregimes` (i).

In the coordinates of `IsotypicInvariants` (the commutant of `G` is `{⊕_λ I_{A λ} ⊗ X_λ}`), if the
matrices of `G` pairwise commute (any torus, any abelian group) then every carrier `A λ` is a single
point.  Consequently `τ_λ(v) = |v_λ⟩⟨v_λ|` has rank at most one for every vector `v`.

* `blockOp_mul`: `(⊕ I⊗X)(⊕ I⊗Y) = ⊕ I⊗XY`.
* `eq_diag_of_comm`: under `IsotypicInvariants` and pairwise commutativity every `U ∈ G` is diagonal,
  constant on sectors.
* `subsingleton_carrier_of_comm`: `A λ` is a subsingleton whenever `B λ` is nonempty.
* `tau_eq_vecMulVec_of_comm`, `rank_tau_le_one_of_comm`: the multiplicity block is `|v_λ⟩⟨v_λ|`.

Not formalized here: the identification of the sectors with the total-weight spaces of the torus
`U(1)^r` acting on `(⊕_i V_i)^{⊗d}` (the Lean statement is for any abelian set `G` in isotypic
coordinates).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped Kronecker

namespace FormalResearch.QIB

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

theorem blockOp_mul (X Y : ∀ l, Matrix (B l) (B l) ℂ) :
    blockOp A X * blockOp A Y = blockOp A (fun l => X l * Y l) := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_mul]
  congr 1; funext l
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Under the isotypic hypothesis, a set of pairwise commuting matrices consists of matrices that are
scalar on each sector (diagonal in the coordinates). -/
theorem eq_diag_of_comm [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (hcomm : ∀ U ∈ G, ∀ V ∈ G, U * V = V * U)
    {U : Matrix (Idx A B) (Idx A B) ℂ} (hU : U ∈ G) :
    ∃ c : Λ → ℂ, ∀ r s : Idx A B, U r s = if r = s then c r.1 else 0 := by
  obtain ⟨X, hX⟩ := (hG U).1 fun V hV => hcomm V hV U hU
  -- each `X l` is central
  have hcent : ∀ l, ∃ c : ℂ, X l = Matrix.scalar (B l) c := by
    intro l
    have hl : ∀ Z : Matrix (B l) (B l) ℂ, X l * Z = Z * X l := by
      intro Z
      have hY := (hG (blockOp A (Function.update (fun l' => (0 : Matrix (B l') (B l') ℂ)) l Z))).2
        ⟨_, rfl⟩ U hU
      rw [hX, blockOp_mul, blockOp_mul] at hY
      have := congrFun (blockOp_inj hY) l
      simpa using this
    have := Matrix.mem_range_scalar_of_commute_single (M := X l)
      (fun i j _ => (hl _).symm)
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  choose c hc using hcent
  refine ⟨c, fun r s => ?_⟩
  obtain ⟨l, α, b⟩ := r
  obtain ⟨l', α', b'⟩ := s
  by_cases hll : l = l'
  · subst hll
    rw [hX, blockOp_apply_same, hc]
    by_cases h1 : α = α' <;> by_cases h2 : b = b' <;> simp [h1, h2, Matrix.scalar_apply]
  · rw [hX, blockOp_apply_ne _ hll]
    have : (⟨l, (α, b)⟩ : Idx A B) ≠ ⟨l', (α', b')⟩ := by
      intro h; exact hll (congrArg Sigma.fst h)
    simp [this]

/-- **Abelian groups have one-dimensional carriers.** -/
theorem subsingleton_carrier_of_comm [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (hcomm : ∀ U ∈ G, ∀ V ∈ G, U * V = V * U) (l : Λ)
    (b : B l) : Subsingleton (A l) := by
  refine ⟨fun α α' => ?_⟩
  by_contra hne
  let p : Idx A B := ⟨l, (α, b)⟩
  let M : Matrix (Idx A B) (Idx A B) ℂ := Matrix.single p p 1
  have hM : ∀ U ∈ G, U * M = M * U := by
    intro U hU
    obtain ⟨c, hc⟩ := eq_diag_of_comm hG hcomm hU
    have hUd : U = Matrix.diagonal (fun r => c r.1) := by
      ext r s; rw [hc]; simp [Matrix.diagonal_apply]
    rw [hUd]
    ext r s
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rcases eq_or_ne r p with h1 | h1 <;> rcases eq_or_ne s p with h2 | h2
    · subst h1; subst h2; simp [M]
    · subst h1; simp [M, Matrix.single_apply, h2, Ne.symm h2]
    · subst h2; simp [M, Matrix.single_apply, h1, Ne.symm h1]
    · simp [M, Matrix.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]
  obtain ⟨X, hX⟩ := (hG M).1 hM
  have hne' : (⟨l, (α', b)⟩ : Idx A B) ≠ p := by
    intro h; apply hne
    simp only [p, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h
    exact h.2.1.symm
  have e1 := congrFun (congrFun hX p) p
  have e2 := congrFun (congrFun hX ⟨l, (α', b)⟩) ⟨l, (α', b)⟩
  rw [blockOp_apply_same] at e1 e2
  have h1 : X l b b = 1 := by simpa [M, p] using e1.symm
  have h2 : X l b b = 0 := by
    simp [M, hne'.symm] at e2
    simpa using e2.symm
  exact one_ne_zero (h1.symm.trans h2)

/-- **The multiplicity block is `|v_λ⟩⟨v_λ|`** when the carrier is a singleton `{α₀}`. -/
theorem tau_eq_vecMulVec_of_subsingleton (v : Idx A B → ℂ) (l : Λ) (α₀ : A l)
    (hA : Subsingleton (A l)) :
    tau v l = Matrix.vecMulVec (slice v l α₀) (star (slice v l α₀)) := by
  unfold tau
  rw [Finset.sum_eq_single α₀]
  · intro α _ h; exact absurd (Subsingleton.elim α α₀) h
  · simp

theorem rank_tau_le_one_of_comm [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (hcomm : ∀ U ∈ G, ∀ V ∈ G, U * V = V * U)
    (v : Idx A B → ℂ) (l : Λ) : (tau v l).rank ≤ 1 := by
  by_cases hB : Nonempty (B l)
  · obtain ⟨b⟩ := hB
    have hs := subsingleton_carrier_of_comm hG hcomm l b
    obtain ⟨α₀⟩ := ‹∀ l, Nonempty (A l)› l
    rw [tau_eq_vecMulVec_of_subsingleton v l α₀ hs]
    exact Matrix.rank_vecMulVec_le _ _
  · rw [not_nonempty_iff] at hB
    have h : (tau v l).rank ≤ Fintype.card (B l) := Matrix.rank_le_card_height _
    simp only [Fintype.card_eq_zero] at h
    omega

end FormalResearch.QIB

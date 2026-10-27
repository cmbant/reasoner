import Mathlib
import FormalResearch.FrameFree.CopyThresholdNever
import FormalResearch.FrameFree.CopyThresholdWitness
import FormalResearch.FrameFree.TwirlsOneCopy

/-!
# The copy thresholds of Paper P, `thm:copythreshold` (b): `k_*(π) = 1, 2, 3, ∞`

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (reduction to the slot-permutation criterion
of `TwirlsTwirl`) with **exact-symbolic certificates** for the four witnesses of `CopyThresholdWitness`
(`decide +kernel`); no `native_decide`, no new axiom.

`VisibleCopies π` is the set of copy numbers `k` at which some unit pure state `ψ` has different `K_π`-twirls of
`ψ^{⊗k}` and `(Θψ)^{⊗k}`; the threshold `k_*(π) = copyThreshold π` is its least element (`⊤` if empty).
`blockSize π b` is the number of spins sharing the frame `b`; `b = max_b blockSize π b`.

* `isLeast_visibleCopies_of_block_three`: some block has `≥ 3` spins `⟹ k_*(π) = 1`.
* `isLeast_visibleCopies_of_block_two`: largest block of size `2` `⟹ k_*(π) = 2`.
* `isLeast_visibleCopies_independent`: independent frames (`π` injective), `n ≥ 4` spins `⟹ k_*(π) = 3`.
* `visibleCopies_independent_card_le_two`: independent frames, `n ≤ 2` spins `⟹ k_*(π) = ∞`.
* `not_mem_visibleCopies_independent_three`: three independent spins: `k = 1, 2` never separate (the value
  `k_* = 6` of the table is recalled input R6/R12 of the paper; see `docs` of this file's PR note).

The lower bounds are `twirlsCoincide_of_small` (`|B|·k ≤ 2`, so every word is an involution); the attainment is
a non-real word value of an explicit Gaussian-integer state, transferred to the pattern by
`wordVal_pad`/`blockPres_extPerm` (the word acts on the spins of the block only).  The genericity clause of
`thm:copythreshold` (b) (`k_*(ψ,π) = k_*(π)` off a nowhere dense real-algebraic set; `k_*(ψ,π) < ∞ ⟺
F_K^π(ψ) < 1`) is not formalised here (it needs real-algebraic geometry and the separation of orbits by
invariants of a compact group, neither of which is in Mathlib).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

variable {α β κ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ]

/-- For `n` qubits `TwirlsCoincide` is the statement of the paper: the `K_π`-twirls of `ψ^{⊗k}` and
`(Θψ)^{⊗k}` agree, with `Θψ = ε^{⊗n} ψ̄` of `Foundations`. -/
theorem twirlsCoincide_iff_theta {n : ℕ} (π : Fin n → κ) (γ : Type*) [Fintype γ] [DecidableEq γ]
    (ψ : FormalResearch.FrameFree.NQubit.Ψ n) :
    TwirlsCoincide π γ (pureOp ψ) ↔ ∀ Z Z' : OpS (Fin n × γ),
      IsTwirl (copyPattern γ π) (kronPow γ (pureOp ψ)) Z →
      IsTwirl (copyPattern γ π) (kronPow γ (pureOp (FormalResearch.FrameFree.NQubit.Θ ψ))) Z' → Z = Z' := by
  unfold TwirlsCoincide
  rw [show thetaConj (pureOp ψ) = pureOp (FormalResearch.FrameFree.NQubit.Θ ψ) from thetaConj_proj ψ]

/-- The number of spins sharing the frame `b`. -/
def blockSize (π : α → κ) (b : κ) : ℕ := (Finset.univ.filter fun a => π a = b).card

/-- The copy numbers at which some unit pure state has separated twirls over `K_π`. -/
def VisibleCopies (π : α → κ) : Set ℕ :=
  {k | ∃ ψ : (α → Fin 2) → ℂ, ∑ x, Complex.normSq (ψ x) = 1 ∧ ¬ TwirlsCoincide π (Fin k) (pureOp ψ)}

/-- The copy threshold `k_*(π)`: the least visible copy number (`⊤` if there is none). -/
noncomputable def copyThreshold (π : α → κ) : ℕ∞ := sInf (((↑) : ℕ → ℕ∞) '' VisibleCopies π)

theorem copyThreshold_eq_of_isLeast {π : α → κ} {k : ℕ} (h : IsLeast (VisibleCopies π) k) :
    copyThreshold π = k :=
  le_antisymm (sInf_le ⟨k, h.1, rfl⟩)
    (le_sInf (by rintro _ ⟨j, hj, rfl⟩; exact_mod_cast h.2 hj))

theorem copyThreshold_eq_top_of_empty {π : α → κ} (h : VisibleCopies π = ∅) : copyThreshold π = ⊤ := by
  simp [copyThreshold, h]

/-- `thm:copythreshold` (a): no separation when every block has at most two slots over the `k` copies. -/
theorem not_mem_visibleCopies_of_small (π : α → κ) {k : ℕ} (hk : ∀ b, blockSize π b * k ≤ 2) :
    k ∉ VisibleCopies π := by
  rintro ⟨ψ, -, hψ⟩
  exact hψ (twirlsCoincide_of_small π (fun b => by simpa [blockSize] using hk b) (pureOp_isHermitian ψ))

/-- A word with a non-real value on the spins `e(β)` makes `k` visible. -/
theorem mem_visibleCopies_of_word (π : α → κ) (e : β ↪ α) {k : ℕ} (φ : (β → Fin 2) → ℂ)
    (s : Equiv.Perm (β × Fin k)) (hs : BlockPres (π ∘ e) s) (him : (wordVal (Fin k) s (pureOp φ)).im ≠ 0) :
    k ∈ VisibleCopies π := by
  have h1 : ¬ TwirlsCoincide π (Fin k) (pureOp (padVec e φ)) :=
    not_twirlsCoincide_of_im_ne π _ (extPerm e s) (blockPres_extPerm π e s hs)
      (by rw [wordVal_pad]; exact him)
  exact exists_unit_differ π _ h1

theorem blockSize_le_one_of_injective {π : α → κ} (hπ : Function.Injective π) (b : κ) : blockSize π b ≤ 1 :=
  Finset.card_le_one.2 fun a ha a' ha' => hπ (by simp at ha ha'; rw [ha, ha'])

/-! ### The thresholds -/

/-- **Blocks of at least three spins: `k_*(π) = 1`.** -/
theorem isLeast_visibleCopies_of_block_three (π : α → κ) {i j l : α} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (h1 : π i = π j) (h2 : π j = π l) : IsLeast (VisibleCopies π) 1 := by
  refine ⟨?_, fun k hk => ?_⟩
  · let e : Fin 3 ↪ α := ⟨![i, j, l], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp_all) ⟩
    obtain ⟨φ, s, hφ⟩ := witness_block3
    have hp : ∀ a : Fin 3, π (![i, j, l] a) = π i := by
      intro a
      fin_cases a
      · rfl
      · exact h1.symm
      · exact (h1.trans h2).symm
    have hconst : ∀ a b : Fin 3, π (e a) = π (e b) := fun a b => (hp a).trans (hp b).symm
    exact mem_visibleCopies_of_word π e φ s (fun q => hconst _ _) hφ
  · by_contra h0
    have : k = 0 := by omega
    subst this
    exact not_mem_visibleCopies_of_small π (fun b => by simp) hk

/-- **Largest block of two spins: `k_*(π) = 2`.** -/
theorem isLeast_visibleCopies_of_block_two (π : α → κ) (hb : ∀ b, blockSize π b ≤ 2) {i j : α}
    (hij : i ≠ j) (h : π i = π j) : IsLeast (VisibleCopies π) 2 := by
  refine ⟨?_, fun k hk => ?_⟩
  · let e : Fin 2 ↪ α := ⟨![i, j], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp_all) ⟩
    obtain ⟨φ, s, hφ⟩ := witness_block2
    have hp : ∀ a : Fin 2, π (![i, j] a) = π i := by
      intro a
      fin_cases a
      · rfl
      · exact h.symm
    have hconst : ∀ a b : Fin 2, π (e a) = π (e b) := fun a b => (hp a).trans (hp b).symm
    exact mem_visibleCopies_of_word π e φ s (fun q => hconst _ _) hφ
  · by_contra h0
    have : k ≤ 1 := by omega
    exact not_mem_visibleCopies_of_small π (fun b => by nlinarith [hb b]) hk

/-- **Independent frames, at least four spins: `k_*(π) = 3`.** -/
theorem isLeast_visibleCopies_independent (π : α → κ) (hπ : Function.Injective π)
    (hα : 4 ≤ Fintype.card α) : IsLeast (VisibleCopies π) 3 := by
  refine ⟨?_, fun k hk => ?_⟩
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := α) (by simpa using hα)
    obtain ⟨φ, s, hs, hφ⟩ := witness_indep4
    exact mem_visibleCopies_of_word π e φ s (fun q => by simp [hs q]) hφ
  · by_contra h0
    have : k ≤ 2 := by omega
    exact not_mem_visibleCopies_of_small π
      (fun b => by nlinarith [blockSize_le_one_of_injective hπ b]) hk

/-- **Independent frames, at most two spins: `k_*(π) = ∞`.** -/
theorem visibleCopies_independent_card_le_two (π : α → κ) (hπ : Function.Injective π)
    (hα : Fintype.card α ≤ 2) : VisibleCopies π = ∅ := by
  ext k
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨ψ, -, hψ⟩
  exact hψ (twirlsCoincide_of_card_le_two π hπ hα ψ)

/-- Three independent spins: one and two copies never separate the twirls. -/
theorem not_mem_visibleCopies_independent {π : α → κ} (hπ : Function.Injective π) {k : ℕ} (hk : k ≤ 2) :
    k ∉ VisibleCopies π :=
  not_mem_visibleCopies_of_small π (fun b => by nlinarith [blockSize_le_one_of_injective hπ b])

theorem copyThreshold_block_three (π : α → κ) {i j l : α} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (h1 : π i = π j) (h2 : π j = π l) : copyThreshold π = 1 :=
  copyThreshold_eq_of_isLeast (isLeast_visibleCopies_of_block_three π hij hil hjl h1 h2)

theorem copyThreshold_block_two (π : α → κ) (hb : ∀ b, blockSize π b ≤ 2) {i j : α} (hij : i ≠ j)
    (h : π i = π j) : copyThreshold π = 2 :=
  copyThreshold_eq_of_isLeast (isLeast_visibleCopies_of_block_two π hb hij h)

theorem copyThreshold_independent (π : α → κ) (hπ : Function.Injective π) (hα : 4 ≤ Fintype.card α) :
    copyThreshold π = 3 :=
  copyThreshold_eq_of_isLeast (isLeast_visibleCopies_independent π hπ hα)

theorem copyThreshold_independent_card_le_two (π : α → κ) (hπ : Function.Injective π)
    (hα : Fintype.card α ≤ 2) : copyThreshold π = ⊤ :=
  copyThreshold_eq_top_of_empty (visibleCopies_independent_card_le_two π hπ hα)

end FormalResearch.FrameFree.Twirls

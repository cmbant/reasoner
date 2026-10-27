import Mathlib
import FormalResearch.QIB.RealCoordsFrame
import FormalResearch.FrameFree.HelstromWindow

/-!
# `prop:blind` with multiplicity counted inside `Sym^k`

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no extra hypotheses).

`BlockRealPe.Pe_blockdecomp_blind` counts the multiplicity `b_l` of a sector in the full tensor power
`(ℂ^{2^n})^{⊗k}`.  The paper (`prop:blind`) counts it inside the symmetric subspace `Sym^k ∋ ψ^{⊗k}`, which
is smaller, so more sectors qualify.  Here:

* `multSupport W S l`: the *multiplicity support* of a subspace `S` in sector `l` of the coordinates `W`: the
  span in the multiplicity space `ℂ^{b_l}` of all slices `(Wᴴ s)_{lα}`, `s ∈ S`, `α` a carrier index.
  For a frame-invariant `S` one has `S_l = ℂ^{a_l} ⊗ multSupport W S l`, so
  `finrank (multSupport W S l)` is the multiplicity of the sector inside `S`; the tensor decomposition itself is
  not formalised and `finrank ≤ 1` is taken as the definition of "multiplicity at most one in `S`".
* `finrank_multSupport_le`: `finrank (multSupport W S l) ≤ b_l`, so the old statement is a special case.
* `tau_real_of_finrank_le_one`: for real `W` and conjugation-closed `S`, if the multiplicity support of `l` in
  `S` has dimension `≤ 1` then `τ_l(Wᴴ s)` is a real matrix for every `s ∈ S`.  (The support is conjugation closed,
  hence spanned by one real vector `g`, and `τ_l(Wᴴ s) = (Σ_α |c_α|²) |g⟩⟨g|`.)
* `Pe_ge_blind_sym`: in real isotypic coordinates of the frame group, for every set `T` of sectors of
  multiplicity `≤ 1` in `Sym^k` (`symSub n k`), `P_e(k) ≥ ½ Σ_{l ∈ T} Tr τ_l(ψ^{⊗k})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (qf Pe rotK copies Copies symSpace copies_mem_symSpace cnt)
open FormalResearch.FrameFree.NQubit (Ψ Θ eps cj)

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
  {A B : Λ → Type*} [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)]
  [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- The span, in the multiplicity space of sector `l`, of all slices `(Wᴴ s)_{lα}` with `s ∈ S`. -/
def multSupport (W : Matrix ι (Idx A B) ℂ) (S : Submodule ℂ (ι → ℂ)) (l : Λ) :
    Submodule ℂ (B l → ℂ) :=
  Submodule.span ℂ {m | ∃ s ∈ S, ∃ α : A l, m = slice (Wᴴ *ᵥ s) l α}

theorem finrank_multSupport_le (W : Matrix ι (Idx A B) ℂ) (S : Submodule ℂ (ι → ℂ)) (l : Λ) :
    Module.finrank ℂ (multSupport W S l) ≤ Fintype.card (B l) := by
  have := Submodule.finrank_le (multSupport W S l)
  simpa using this

theorem star_slice {W : Matrix ι (Idx A B) ℂ} (hreal : W.map conj = W) (s : ι → ℂ) (l : Λ)
    (α : A l) : star (slice (Wᴴ *ᵥ s) l α) = slice (Wᴴ *ᵥ star s) l α := by
  have hW : ∀ i j, conj (W i j) = W i j := fun i j => congrFun (congrFun hreal i) j
  have h2 : star (Wᴴ *ᵥ s) = Wᴴ *ᵥ star s := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul', Matrix.conjTranspose_apply, hW]
  funext b
  have := congrFun h2 ⟨l, (α, b)⟩
  simpa [slice] using this

theorem conjClosed_multSupport {W : Matrix ι (Idx A B) ℂ} (hreal : W.map conj = W)
    {S : Submodule ℂ (ι → ℂ)} (hS : ConjClosed S) (l : Λ) : ConjClosed (multSupport W S l) := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s, hs, α, rfl⟩ := hm
    exact Submodule.subset_span ⟨star s, hS s hs, α, star_slice hreal s l α⟩
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [star_smul_vec]; exact Submodule.smul_mem _ _ hx

/-- If the multiplicity support of sector `l` in a conjugation-closed `S` has dimension `≤ 1` (multiplicity at
most one inside `S`), then `τ_l` of every vector of `S` is real. -/
theorem tau_real_of_finrank_le_one {W : Matrix ι (Idx A B) ℂ} (hreal : W.map conj = W)
    {S : Submodule ℂ (ι → ℂ)} (hS : ConjClosed S) (l : Λ)
    (hfin : Module.finrank ℂ (multSupport W S l) ≤ 1) {s : ι → ℂ} (hs : s ∈ S) :
    (tau (Wᴴ *ᵥ s) l).map conj = tau (Wᴴ *ᵥ s) l := by
  set N := multSupport W S l with hN
  have hmem : ∀ α, slice (Wᴴ *ᵥ s) l α ∈ N := fun α => Submodule.subset_span ⟨s, hs, α, rfl⟩
  by_cases hbot : N = ⊥
  · have h0 : ∀ α, slice (Wᴴ *ᵥ s) l α = 0 := fun α => by
      have := hmem α; rw [hbot] at this; simpa using this
    ext b b'
    have h0' : ∀ α b, (Wᴴ *ᵥ s) ⟨l, (α, b)⟩ = 0 := fun α b => congrFun (h0 α) b
    simp [tau_apply, h0']
  · obtain ⟨g, hgN, hg0, hgr⟩ := exists_real_vec_of_ne_bot N (conjClosed_multSupport hreal hS l) hbot
    have hne : (⟨g, hgN⟩ : N) ≠ 0 := fun h => hg0 (by simpa using congrArg Subtype.val h)
    have hone : Module.finrank ℂ N = 1 :=
      le_antisymm hfin (Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, hne⟩)
    have hspan := (finrank_eq_one_iff_of_nonzero' (⟨g, hgN⟩ : N) hne).1 hone
    have hc : ∀ α, ∃ c : ℂ, slice (Wᴴ *ᵥ s) l α = c • g := fun α => by
      obtain ⟨c, hc⟩ := hspan ⟨_, hmem α⟩
      exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
    choose c hc using hc
    have hg : ∀ b, conj (g b) = g b := fun b => by
      have := congrFun hgr b
      simpa [Pi.star_apply] using this
    ext b b'
    have e : ∀ α b, (Wᴴ *ᵥ s) ⟨l, (α, b)⟩ = c α * g b := fun α b => by
      have := congrFun (hc α) b
      simpa [slice] using this
    simp only [Matrix.map_apply, tau_apply, e, map_sum, map_mul, Complex.star_def, Complex.conj_conj, hg]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring

end Generic

/-! ### The symmetric subspace as a subspace of functions -/

/-- `Sym^k`, as a subspace of `Copies n k → ℂ`. -/
def symSub (n k : ℕ) : Submodule ℂ (Copies n k → ℂ) where
  carrier := {w | ∀ i j : Copies n k, cnt k i = cnt k j → w i = w j}
  add_mem' := by
    intro a b ha hb i j h
    simp [ha i j h, hb i j h]
  zero_mem' := by intro i j h; simp
  smul_mem' := by
    intro c a ha i j h
    simp [ha i j h]

theorem copies_mem_symSub {n : ℕ} (k : ℕ) (φ : Ψ n) : copies k φ ∈ symSub n k :=
  FormalResearch.FrameFree.Helstrom.copies_mem_symSpace k φ

theorem conjClosed_symSub (n k : ℕ) : ConjClosed (symSub n k) := by
  intro v hv i j h
  simp [Pi.star_apply, hv i j h]

/-- **`prop:blind` with multiplicity counted in `Sym^k`** (paper form), for `Helstrom.Pe`, unconditionally.
In real isotypic coordinates `W` of the frame group, for every set `T` of sectors whose multiplicity inside
`Sym^k` is at most one (`finrank (multSupport W (symSub n k) l) ≤ 1`), the multiplicity blocks of `ψ^{⊗k}` are
real and `½ Σ_{l ∈ T} Tr τ_l(ψ^{⊗k}) ≤ P_e(k)`. -/
theorem Pe_ge_blind_sym (n k : ℕ) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ W.map conj = W ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ (ψ : Ψ n) (T : Finset (Fin r)),
        (∀ l ∈ T, Module.finrank ℂ (multSupport W (symSub n k) l) ≤ 1) →
        (1 / 2) * ∑ l ∈ T, (tau (Wᴴ *ᵥ copies k ψ) l).trace.re ≤ Pe k ψ := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hreal, hG⟩ := realIsotypicCoords n k
  refine ⟨r, a, b, W, ha, hW1, hW2, hreal, hG, fun ψ T hT => ?_⟩
  exact Pe_ge_blind ha hW1 hW2 hreal hG ψ T fun l hl =>
    tau_real_of_finrank_le_one hreal (conjClosed_symSub n k) l (hT l hl) (copies_mem_symSub k ψ)

end FormalResearch.QIB

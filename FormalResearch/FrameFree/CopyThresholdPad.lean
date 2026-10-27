import Mathlib
import FormalResearch.FrameFree.CopyThresholdWords

/-!
# Transfer of word values to more spins, scaling, and Gaussian-integer evaluation

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (no hypothesis, no new axiom).

* `wordVal_pad`: if a word `s` acts on the spins `e(β) ⊆ α` only (`extPerm e s` is `s` on the slots of `e(β)`
  and the identity elsewhere) and the state is `φ` on `e(β)` times `|0…0⟩` on the others (`padVec e φ`), the
  word value is that of `φ` ("a word acting on some spins returns the same value on `ψ ⊗ φ`", proof of
  `thm:copythreshold`).  `blockPres_extPerm`: `extPerm e s` preserves the blocks of `π` if `s` preserves those
  of `π ∘ e`.  `nsq_padVec`: the norm is unchanged.
* `wordVal_smul`, `exists_unit_of_im_ne`: a non-real word value is unchanged in kind by a positive rescaling,
  so a witness can be normalised to a unit vector.
* `giWord`, `wordVal_giVec`: for a state with Gaussian-integer amplitudes the word value is the image of an
  explicit sum in `ℤ[i]`, which `decide +kernel` evaluates (used for the witnesses in `CopyThresholdWitness`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

variable {α β κ γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] [Fintype γ] [DecidableEq γ]

/-! ### Padding by spins in `|0⟩` -/

open Classical in
/-- `φ` on the spins `e(β)` tensored with `|0⟩` on the remaining spins. -/
noncomputable def padVec (e : β ↪ α) (φ : (β → Fin 2) → ℂ) : (α → Fin 2) → ℂ :=
  fun x => if ∀ a, a ∉ Set.range e → x a = 0 then φ (x ∘ e) else 0

theorem padVec_of (e : β ↪ α) (φ : (β → Fin 2) → ℂ) {x : α → Fin 2}
    (hx : ∀ a, a ∉ Set.range e → x a = 0) : padVec e φ x = φ (x ∘ e) := by
  simp only [padVec]
  exact if_pos hx

theorem forall_of_padVec_ne_zero (e : β ↪ α) (φ : (β → Fin 2) → ℂ) {x : α → Fin 2}
    (h : padVec e φ x ≠ 0) : ∀ a, a ∉ Set.range e → x a = 0 := by
  by_contra hc
  exact h (by simp only [padVec]; exact if_neg hc)

/-- The slots `β × γ` inside `α × γ`. -/
def slotEmb (e : β ↪ α) (γ : Type*) : β × γ ↪ α × γ := e.prodMap (Function.Embedding.refl γ)

theorem notMem_range_slotEmb (e : β ↪ α) {a : α} (ha : a ∉ Set.range e) (c : γ) :
    (a, c) ∉ Set.range (slotEmb e γ) := by
  rintro ⟨⟨b, c'⟩, h⟩
  exact ha ⟨b, congrArg Prod.fst h⟩

/-- The word `s` on the slots of `e(β)`, extended by the identity. -/
noncomputable def extPerm (e : β ↪ α) (s : Equiv.Perm (β × γ)) : Equiv.Perm (α × γ) :=
  Equiv.Perm.viaFintypeEmbedding s (slotEmb e γ)

theorem extPerm_apply_slot (e : β ↪ α) (s : Equiv.Perm (β × γ)) (q : β × γ) :
    extPerm e s (slotEmb e γ q) = slotEmb e γ (s q) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image s (slotEmb e γ) q

theorem extPerm_apply_of_notMem (e : β ↪ α) (s : Equiv.Perm (β × γ)) {a : α} (ha : a ∉ Set.range e)
    (c : γ) : extPerm e s (a, c) = (a, c) :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range s (slotEmb e γ) (notMem_range_slotEmb e ha c)

theorem blockPres_extPerm (π : α → κ) (e : β ↪ α) (s : Equiv.Perm (β × γ)) (hs : BlockPres (π ∘ e) s) :
    BlockPres π (extPerm e s) := by
  rintro ⟨a, c⟩
  by_cases ha : a ∈ Set.range e
  · obtain ⟨b, rfl⟩ := ha
    have := extPerm_apply_slot e s (b, c)
    have e1 : ((e b, c) : α × γ) = slotEmb e γ (b, c) := rfl
    rw [e1, this]
    exact hs (b, c)
  · rw [extPerm_apply_of_notMem e s ha c]

/-- Extension of a slot configuration on `β × γ` by `0`. -/
noncomputable def extCfg (e : β ↪ α) (Y : β × γ → Fin 2) : α × γ → Fin 2 :=
  Function.extend (slotEmb e γ) Y 0

theorem extCfg_slot (e : β ↪ α) (Y : β × γ → Fin 2) (q : β × γ) : extCfg e Y (slotEmb e γ q) = Y q :=
  (slotEmb e γ).injective.extend_apply Y 0 q

theorem extCfg_of_notMem (e : β ↪ α) (Y : β × γ → Fin 2) {a : α} (ha : a ∉ Set.range e) (c : γ) :
    extCfg e Y (a, c) = 0 := by
  have h := notMem_range_slotEmb e ha c
  exact Function.extend_apply' _ _ _ (by simpa using h)

theorem extCfg_injective (e : β ↪ α) : Function.Injective (extCfg (γ := γ) e) := by
  intro Y Y' h
  funext q
  have := congrFun h (slotEmb e γ q)
  rwa [extCfg_slot, extCfg_slot] at this

/-- **A word acting on some spins returns the same value on `φ ⊗ |0…0⟩`.** -/
theorem wordVal_pad (e : β ↪ α) (s : Equiv.Perm (β × γ)) (φ : (β → Fin 2) → ℂ) :
    wordVal γ (extPerm e s) (pureOp (padVec e φ)) = wordVal γ s (pureOp φ) := by
  rw [wordVal_pure, wordVal_pure]
  symm
  refine Fintype.sum_of_injective (extCfg e) (extCfg_injective e) _ _ ?_ ?_
  · intro X hX
    by_contra hne
    apply hX
    have hcol : ∀ c, ∀ a, a ∉ Set.range e → X (a, c) = 0 := by
      intro c
      have h1 := Finset.prod_ne_zero_iff.1 hne c (Finset.mem_univ c)
      have h2 : conj (padVec e φ (col X c)) ≠ 0 := right_ne_zero_of_mul h1
      exact forall_of_padVec_ne_zero e φ ((map_ne_zero (starRingEnd ℂ)).1 h2)
    refine ⟨fun q => X (slotEmb e γ q), ?_⟩
    funext ⟨a, c⟩
    by_cases ha : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := ha
      exact extCfg_slot e (fun q => X (slotEmb e γ q)) (b, c)
    · rw [extCfg_of_notMem e _ ha c, hcol c a ha]
  · intro Y
    refine Finset.prod_congr rfl fun c _ => ?_
    have h1 : padVec e φ (col (extCfg e Y) c) = φ (col Y c) := by
      refine (padVec_of e φ (x := col (extCfg e Y) c) (fun a ha => extCfg_of_notMem e Y ha c)).trans ?_
      congr 1
      funext b
      exact extCfg_slot e Y (b, c)
    have h2 : padVec e φ (fun a => extCfg e Y (extPerm e s (a, c))) = φ (fun b => Y (s (b, c))) := by
      rw [padVec_of e φ (fun a ha => by rw [extPerm_apply_of_notMem e s ha c]; exact extCfg_of_notMem e Y ha c)]
      congr 1
      funext b
      show extCfg e Y (extPerm e s (slotEmb e γ (b, c))) = Y (s (b, c))
      rw [extPerm_apply_slot, extCfg_slot]
    rw [h1, h2]

/-- The norm of `φ ⊗ |0…0⟩` is that of `φ`. -/
theorem nsq_padVec (e : β ↪ α) (φ : (β → Fin 2) → ℂ) :
    ∑ x, Complex.normSq (padVec e φ x) = ∑ y, Complex.normSq (φ y) := by
  symm
  refine Fintype.sum_of_injective (fun y => Function.extend e y (0 : α → Fin 2)) ?_ _ _ ?_ ?_
  · intro y y' h
    funext b
    have := congrFun h (e b)
    beta_reduce at this
    rwa [e.injective.extend_apply, e.injective.extend_apply] at this
  · intro x hx
    by_contra hne
    apply hx
    have hz : ∀ a, a ∉ Set.range e → x a = 0 := forall_of_padVec_ne_zero e φ (fun h => hne (by simp [h]))
    refine ⟨x ∘ e, funext fun a => ?_⟩
    by_cases ha : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := ha
      exact e.injective.extend_apply (x ∘ e) (0 : α → Fin 2) b
    · show Function.extend e (x ∘ e) (0 : α → Fin 2) a = x a
      rw [Function.extend_apply' _ _ _ (by simpa using ha), hz a ha]; rfl
  · intro y
    have hx : ∀ a, a ∉ Set.range e → Function.extend e y (0 : α → Fin 2) a = 0 := fun a ha =>
      by rw [Function.extend_apply' _ _ _ (by simpa using ha)]; rfl
    rw [padVec_of e φ hx]
    congr 2
    funext b
    exact (e.injective.extend_apply y (0 : α → Fin 2) b).symm

/-! ### Scaling and normalisation -/

theorem wordVal_smul (s : Equiv.Perm (α × γ)) (c : ℂ) (φ : (α → Fin 2) → ℂ) :
    wordVal γ s (pureOp (c • φ)) = (c * conj c) ^ Fintype.card γ * wordVal γ s (pureOp φ) := by
  rw [wordVal_pure, wordVal_pure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  have : ∀ c' : γ, (c • φ) (fun a => X (s (a, c'))) * conj ((c • φ) (col X c')) =
      (c * conj c) * (φ (fun a => X (s (a, c'))) * conj (φ (col X c'))) := fun c' => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem nsq_smul (c : ℂ) (φ : (α → Fin 2) → ℂ) :
    ∑ x, Complex.normSq ((c • φ) x) = Complex.normSq c * ∑ x, Complex.normSq (φ x) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [map_mul]

/-- A witness of separated twirls can be taken to be a unit vector. -/
theorem exists_unit_differ (π : α → κ) (ψ : (α → Fin 2) → ℂ) (h : ¬ TwirlsCoincide π γ (pureOp ψ)) :
    ∃ ψ' : (α → Fin 2) → ℂ, ∑ x, Complex.normSq (ψ' x) = 1 ∧ ¬ TwirlsCoincide π γ (pureOp ψ') := by
  have hk : 0 < Fintype.card γ := by
    by_contra h0
    have h0' : Fintype.card γ = 0 := by omega
    exact h (twirlsCoincide_of_small π (fun b => by rw [h0']; simp) (pureOp_isHermitian ψ))
  rw [twirlsCoincide_iff] at h
  push Not at h
  obtain ⟨s, hs, him⟩ := h
  set N : ℝ := ∑ x, Complex.normSq (ψ x) with hN
  have hNpos : 0 < N := by
    rcases (Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (ψ x)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hz : ψ = (0 : ℂ) • ψ := by
        funext x
        have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => Complex.normSq_nonneg (ψ x)).1 h1.symm x
          (Finset.mem_univ x)
        simp [Complex.normSq_eq_zero.1 this]
      rw [hz, wordVal_smul] at him
      simp [Nat.pos_iff_ne_zero.1 hk] at him
  set r : ℝ := (Real.sqrt N)⁻¹ with hr
  refine ⟨(r : ℂ) • ψ, ?_, ?_⟩
  · rw [nsq_smul, Complex.normSq_ofReal, ← hN, hr, ← mul_inv, Real.mul_self_sqrt hNpos.le,
      inv_mul_cancel₀ hNpos.ne']
  · rw [twirlsCoincide_iff]
    push Not
    refine ⟨s, hs, ?_⟩
    rw [wordVal_smul, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_pow]
    rw [Complex.im_ofReal_mul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (Real.sqrt_pos.2 hNpos).ne')
      (inv_ne_zero (Real.sqrt_pos.2 hNpos).ne'))) him

/-! ### Gaussian-integer amplitudes -/

/-- A state with Gaussian-integer amplitudes. -/
def giVec (φ' : (β → Fin 2) → GaussianInt) : (β → Fin 2) → ℂ := fun x => ((φ' x : GaussianInt) : ℂ)

/-- The word value of `giVec φ'`, computed in `ℤ[i]`. -/
def giWord (γ : Type*) [Fintype γ] [DecidableEq γ] (s : Equiv.Perm (β × γ)) (φ' : (β → Fin 2) → GaussianInt) :
    GaussianInt :=
  ∑ X : β × γ → Fin 2, ∏ c : γ, φ' (fun b => X (s (b, c))) * star (φ' (fun b => X (b, c)))

theorem wordVal_giVec (s : Equiv.Perm (β × γ)) (φ' : (β → Fin 2) → GaussianInt) :
    wordVal γ s (pureOp (giVec φ')) = ((giWord γ s φ' : GaussianInt) : ℂ) := by
  rw [wordVal_pure, giWord]
  simp only [giVec, map_sum, map_prod, map_mul, GaussianInt.toComplex_star]
  rfl

theorem im_wordVal_giVec_ne_zero (s : Equiv.Perm (β × γ)) (φ' : (β → Fin 2) → GaussianInt)
    (h : (giWord γ s φ').im ≠ 0) : (wordVal γ s (pureOp (giVec φ'))).im ≠ 0 := by
  rw [wordVal_giVec, ← GaussianInt.intCast_im]
  exact Int.cast_ne_zero.2 h

end FormalResearch.FrameFree.Twirls

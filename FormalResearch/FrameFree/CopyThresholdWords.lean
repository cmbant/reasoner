import Mathlib
import FormalResearch.FrameFree.TwirlsTwirl

/-!
# Word values of pure-state copies and the reality criterion (Paper P, `thm:copythreshold`)

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved** (no hypothesis, no new axiom).

Builds on `TwirlsTwirl.copy_twirl_eq_iff`.  For a pure state `ρ = |ψ⟩⟨ψ|` on the qubits `α`, a *word* is a
slot permutation `s ∈ Perm (α × γ)` of the `k = |γ|` copies, and its *value* is `Tr(P_s ρ^{⊗k})`.

* `TwirlsCoincide π γ ρ`: all `K_π`-twirls of `ρ^{⊗γ}` and `(ΘρΘ⁻¹)^{⊗γ}` agree (twirls exist and are unique,
  so this is "the two twirled states are equal").
* `twirlsCoincide_iff`: they coincide iff every block-preserving word value is real (`thm:copythreshold` (a)).
* `twirlsCoincide_of_small`: no block has more than two slots over the `k` copies (`|B|k ≤ 2`).
* `wordVal_pure`: `Tr(P_s ρ^{⊗k}) = ∑_X ∏_c ψ(X∘s)_c conj ψ(X)_c`, a single explicit sum.
* `conj_wordVal`, `wordVal_diag_mul`, `wordVal_mul_diag`: `conj Tr(P_s ρ^{⊗k}) = Tr(P_{s⁻¹} ρ^{⊗k})`, and the
  value of a pure state is unchanged under multiplying `s` by a permutation of the copies (`id × w`) on
  either side.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

variable {α κ γ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  [Fintype γ] [DecidableEq γ]

/-- The rank-one operator `|ψ⟩⟨ψ|` on any finite family of qubits. -/
def pureOp (ψ : (α → Fin 2) → ℂ) : OpS α := Matrix.vecMulVec ψ (star ψ)

theorem pureOp_isHermitian (ψ : (α → Fin 2) → ℂ) : (pureOp ψ)ᴴ = pureOp ψ := by
  ext x y
  simp [pureOp, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

/-- The value `Tr(P_s ρ^{⊗γ})` of the word `s` on `k = |γ|` copies of `ρ`. -/
noncomputable def wordVal (γ : Type*) [Fintype γ] [DecidableEq γ] (s : Equiv.Perm (α × γ)) (ρ : OpS α) : ℂ :=
  (permOp s * kronPow γ ρ).trace

/-- `s` preserves the blocks of the sharing pattern `π` on the slots `α × γ`. -/
def BlockPres (π : α → κ) (s : Equiv.Perm (α × γ)) : Prop := ∀ q, π (s q).1 = π q.1

/-- The twirls over `K_π` of `ρ^{⊗γ}` and `(ΘρΘ⁻¹)^{⊗γ}` coincide. -/
def TwirlsCoincide (π : α → κ) (γ : Type*) [Fintype γ] [DecidableEq γ] (ρ : OpS α) : Prop :=
  ∀ Z Z' : OpS (α × γ), IsTwirl (copyPattern γ π) (kronPow γ ρ) Z →
    IsTwirl (copyPattern γ π) (kronPow γ (thetaConj ρ)) Z' → Z = Z'

/-- **`thm:copythreshold` (a).**  The twirls coincide iff every block-preserving word value is real. -/
theorem twirlsCoincide_iff (π : α → κ) (ρ : OpS α) :
    TwirlsCoincide π γ ρ ↔ ∀ s : Equiv.Perm (α × γ), BlockPres π s → (wordVal γ s ρ).im = 0 := by
  obtain ⟨Z, hZ⟩ := exists_twirl (copyPattern γ π) (kronPow γ ρ)
  obtain ⟨Z', hZ'⟩ := exists_twirl (copyPattern γ π) (kronPow γ (thetaConj ρ))
  have key := copy_twirl_eq_iff π ρ hZ hZ'
  constructor
  · intro h s hs
    have := key.1 (h Z Z' hZ hZ') s hs
    exact Complex.conj_eq_iff_im.1 this
  · intro h Z₁ Z₂ h₁ h₂
    have key' := copy_twirl_eq_iff π ρ h₁ h₂
    exact key'.2 fun s hs => Complex.conj_eq_iff_im.2 (h s hs)

/-- A block-preserving word with a non-real value separates the twirls. -/
theorem not_twirlsCoincide_of_im_ne (π : α → κ) (ρ : OpS α) (s : Equiv.Perm (α × γ))
    (hs : BlockPres π s) (h : (wordVal γ s ρ).im ≠ 0) : ¬ TwirlsCoincide π γ ρ :=
  fun hc => h ((twirlsCoincide_iff π ρ).1 hc s hs)

/-- If no block has more than two slots over the `k` copies (`|B|·k ≤ 2`) the twirls coincide. -/
theorem twirlsCoincide_of_small (π : α → κ)
    (hk : ∀ b : κ, (Finset.univ.filter fun a => π a = b).card * Fintype.card γ ≤ 2)
    {ρ : OpS α} (hρ : ρᴴ = ρ) : TwirlsCoincide π γ ρ :=
  fun _ _ h h' => copy_twirl_eq_of_small π hk hρ h h'

/-! ### The explicit sum for a pure state -/

/-- Column `c` of the slot configuration `X`: the spins of copy `c`. -/
def col (X : α × γ → Fin 2) (c : γ) : α → Fin 2 := fun a => X (a, c)

theorem wordVal_pure (s : Equiv.Perm (α × γ)) (ψ : (α → Fin 2) → ℂ) :
    wordVal γ s (pureOp ψ) =
      ∑ X : α × γ → Fin 2, ∏ c : γ, ψ (fun a => X (s (a, c))) * conj (ψ (col X c)) := by
  simp only [wordVal, Matrix.trace, Matrix.diag_apply, permOp_mul_apply, kronPow, Matrix.of_apply,
    pureOp, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def]
  rfl

theorem conj_wordVal (s : Equiv.Perm (α × γ)) {ρ : OpS α} (hρ : ρᴴ = ρ) :
    conj (wordVal γ s ρ) = wordVal γ s⁻¹ ρ := by
  have h1 : conj (wordVal γ s ρ) = ((permOp s * kronPow γ ρ)ᴴ).trace := by
    rw [Matrix.trace_conjTranspose]; rfl
  rw [h1, Matrix.conjTranspose_mul, kronPow_isHermitian hρ, permOp_conjTranspose, wordVal,
    Matrix.trace_mul_comm]

/-- The copy permutation `(a, c) ↦ (a, w c)`. -/
def diagPerm (α : Type*) (w : Equiv.Perm γ) : Equiv.Perm (α × γ) := Equiv.prodCongr (Equiv.refl α) w

theorem permOp_diag_mul (w : Equiv.Perm γ) (ψ : (α → Fin 2) → ℂ) :
    permOp (diagPerm α w) * kronPow γ (pureOp ψ) = kronPow γ (pureOp ψ) := by
  ext X Y
  rw [permOp_mul_apply]
  simp only [kronPow, Matrix.of_apply, pureOp, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def]
  have : ∀ c, (fun a => (X ∘ ⇑(diagPerm α w)) (a, c)) = fun a => X (a, w c) := fun c => rfl
  simp only [this]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp w (fun c => ψ (fun a => X (a, c)))

theorem mul_permOp_diag (w : Equiv.Perm γ) (ψ : (α → Fin 2) → ℂ) :
    kronPow γ (pureOp ψ) * permOp (diagPerm α w) = kronPow γ (pureOp ψ) := by
  ext X Y
  rw [mul_permOp_apply]
  simp only [kronPow, Matrix.of_apply, pureOp, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def]
  have : ∀ c, (fun a => (Y ∘ ⇑((diagPerm α w)⁻¹)) (a, c)) = fun a => Y (a, w⁻¹ c) := fun c => rfl
  simp only [this]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp w⁻¹ (fun c => conj (ψ fun a => Y (a, c)))

theorem wordVal_diag_mul (w : Equiv.Perm γ) (s : Equiv.Perm (α × γ)) (ψ : (α → Fin 2) → ℂ) :
    wordVal γ (diagPerm α w * s) (pureOp ψ) = wordVal γ s (pureOp ψ) := by
  rw [wordVal, wordVal, ← permOp_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    mul_permOp_diag]

theorem wordVal_mul_diag (w : Equiv.Perm γ) (s : Equiv.Perm (α × γ)) (ψ : (α → Fin 2) → ℂ) :
    wordVal γ (s * diagPerm α w) (pureOp ψ) = wordVal γ s (pureOp ψ) := by
  rw [wordVal, wordVal, ← permOp_mul, Matrix.mul_assoc, permOp_diag_mul]

end FormalResearch.FrameFree.Twirls

import Mathlib
import FormalResearch.FrameFree.CopyThresholdPad

/-!
# Exact witnesses of non-real word values (Paper P, `thm:copythreshold` (b), CT-3)

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **exact-symbolic certificate** (`decide +kernel`
evaluation of a finite sum in `ℤ[i]`) wrapped by proved bridge lemmas; no `native_decide`, no new axiom.

The word value `Tr(P_s ρ^{⊗k})` of a state with Gaussian-integer amplitudes is the image in `ℂ` of the explicit
`ℤ[i]` sum `giWord` (`CopyThresholdPad`).  `giWord_eq_sumPi` restricts that sum to the support of the state
(`pts`), as a nested sum `sumPi` over `Fin k → Fin r` that the kernel evaluates.  Witnesses, all with an
imaginary part `≠ 0`:

* `witness_block3`: three spins in one block, `k = 1`; `φ = (|001⟩ + i|010⟩)` and the cyclic word (value `i`).
* `witness_block2`: two spins in one block, `k = 2`; `φ = (1, i, 1+i, -1)` and a three-cycle of the four slots
  (value `18 + i`, the state of `verify_copy_threshold.py` CT-3).
* `witness_indep4`: four independent spins, `k = 3`; `ψ_+` (the paper's two-singlet state) and the word
  `(e, (23), (12), (012))` per spin (value `80 + 24 i`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.Twirls

/-- Nested sum over the tuples `Fin n → T`. -/
def sumPi {T M : Type*} [Fintype T] [AddCommMonoid M] : (n : ℕ) → ((Fin n → T) → M) → M
  | 0, F => F Fin.elim0
  | n + 1, F => ∑ t : T, sumPi n (fun f => F (Fin.cons t f))

theorem sum_eq_sumPi {T M : Type*} [Fintype T] [AddCommMonoid M] (n : ℕ) (F : (Fin n → T) → M) :
    ∑ f, F f = sumPi n F := by
  induction n with
  | zero => exact Fintype.sum_unique _
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ => T)).sum_comp, Fintype.sum_prod_type]
    simp only [sumPi, ← ih]
    rfl

section Eval

variable {m k r : ℕ}

/-- **Support enumeration.**  If `φ'` vanishes off `pts`, the `ℤ[i]` word sum is a sum over the tuples of
support points. -/
theorem giWord_eq_sumPi (s : Equiv.Perm (Fin m × Fin k)) (φ' : (Fin m → Fin 2) → GaussianInt)
    (pts : Fin r → (Fin m → Fin 2)) (hinj : Function.Injective pts)
    (hsupp : ∀ x, (∀ j, pts j ≠ x) → φ' x = 0) :
    giWord (Fin k) s φ' = sumPi k (fun u : Fin k → Fin r => ∏ c : Fin k,
      φ' (fun b => pts (u (s (b, c)).2) (s (b, c)).1) * star (φ' (pts (u c)))) := by
  rw [← sum_eq_sumPi]
  unfold giWord
  rw [← (copyEquiv (α := Fin m) (γ := Fin k)).symm.sum_comp]
  symm
  refine Fintype.sum_of_injective (fun u c => pts (u c)) ?_ _ _ ?_ ?_
  · intro u u' h
    funext c
    exact hinj (congrFun h c)
  · intro v hv
    have : ∃ c, v c ∉ Set.range pts := by
      by_contra hne
      push Not at hne
      apply hv
      choose u hu using hne
      exact ⟨u, funext hu⟩
    obtain ⟨c, hc⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    have := hsupp _ (fun j hj => hc ⟨j, hj⟩)
    simp [copyEquiv, this]
  · intro u
    rfl

/-- A word value with non-zero imaginary part, from a kernel-checked `ℤ[i]` sum over the support. -/
theorem im_ne_zero_of_sumPi (s : Equiv.Perm (Fin m × Fin k)) (φ' : (Fin m → Fin 2) → GaussianInt)
    (pts : Fin r → (Fin m → Fin 2)) (hinj : Function.Injective pts)
    (hsupp : ∀ x, (∀ j, pts j ≠ x) → φ' x = 0)
    (h : (sumPi k (fun u : Fin k → Fin r => ∏ c : Fin k,
      φ' (fun b => pts (u (s (b, c)).2) (s (b, c)).1) * star (φ' (pts (u c))))).im ≠ 0) :
    (wordVal (Fin k) s (pureOp (giVec φ'))).im ≠ 0 :=
  im_wordVal_giVec_ne_zero s φ' (by rw [giWord_eq_sumPi s φ' pts hinj hsupp]; exact h)

/-- The permutation of the slots `Fin m × Fin k` given by an injective table. -/
noncomputable def slotPerm (tab : Fin m × Fin k → Fin m × Fin k) (h : Function.Injective tab) :
    Equiv.Perm (Fin m × Fin k) :=
  Equiv.ofBijective tab (Finite.injective_iff_bijective.1 h)

theorem slotPerm_apply (tab : Fin m × Fin k → Fin m × Fin k) (h : Function.Injective tab) (q : Fin m × Fin k) :
    slotPerm tab h q = tab q := rfl

/-- Amplitudes indexed by the binary number `∑ x_i 2^i`. -/
def listVec (l : List GaussianInt) (x : Fin m → Fin 2) : GaussianInt :=
  l.getD (∑ i, (x i).val * 2 ^ i.val) 0

end Eval

/-! ### Three spins in one block, one copy -/

def tab3 : Fin 3 × Fin 1 → Fin 3 × Fin 1 := fun q => (![1, 2, 0] q.1, q.2)

theorem tab3_inj : Function.Injective tab3 := by decide

/-- `|001⟩ + i|010⟩`. -/
def phi3 (x : Fin 3 → Fin 2) : GaussianInt := listVec [0, 0, ⟨0, 1⟩, 0, 1, 0, 0, 0] x

def pts3 : Fin 2 → (Fin 3 → Fin 2) := ![![0, 0, 1], ![0, 1, 0]]

theorem witness_block3 : ∃ (φ : (Fin 3 → Fin 2) → ℂ) (s : Equiv.Perm (Fin 3 × Fin 1)),
    (wordVal (Fin 1) s (pureOp φ)).im ≠ 0 :=
  ⟨giVec phi3, slotPerm tab3 tab3_inj,
    im_ne_zero_of_sumPi _ phi3 pts3 (by decide) (by decide) (by decide +kernel)⟩

/-! ### Two spins in one block, two copies -/

/-- The three-cycle `(0,1) → (1,0) → (1,1) → (0,1)` of the four slots, fixing `(0,0)`. -/
def tab2 : Fin 2 × Fin 2 → Fin 2 × Fin 2 := fun q => ![![(0, 0), (1, 0)], ![(1, 1), (0, 1)]] q.1 q.2

theorem tab2_inj : Function.Injective tab2 := by decide

/-- `(1, i, 1+i, -1)` in the basis order `|00⟩, |10⟩, |01⟩, |11⟩` (`x₀ + 2x₁`). -/
def phi2 (x : Fin 2 → Fin 2) : GaussianInt := listVec [1, ⟨1, 1⟩, ⟨0, 1⟩, -1] x

def pts2 : Fin 4 → (Fin 2 → Fin 2) := ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]

theorem witness_block2 : ∃ (φ : (Fin 2 → Fin 2) → ℂ) (s : Equiv.Perm (Fin 2 × Fin 2)),
    (wordVal (Fin 2) s (pureOp φ)).im ≠ 0 :=
  ⟨giVec phi2, slotPerm tab2 tab2_inj,
    im_ne_zero_of_sumPi _ phi2 pts2 (by decide) (by decide) (by decide +kernel)⟩

/-! ### Four independent spins, three copies -/

/-- Per spin, a permutation of the three copies: `e, (12), (01), (012)`. -/
def tab4 : Fin 4 × Fin 3 → Fin 4 × Fin 3 := fun q =>
  (q.1, (![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0]] q.1 q.2 : Fin 3))

theorem tab4_inj : Function.Injective tab4 := by decide

/-- `ψ_+ = |s s⟩_{12|34} + i |s s⟩_{13|24}` with Gaussian-integer amplitudes (norm squared `8`), in the basis
order `x₀ + 2x₁ + 4x₂ + 8x₃`. -/
def psiPlus (x : Fin 4 → Fin 2) : GaussianInt :=
  listVec [0, 0, 0, ⟨0, 1⟩, 0, 1, ⟨-1, -1⟩, 0, 0, ⟨-1, -1⟩, 1, 0, ⟨0, 1⟩, 0, 0, 0] x

def ptsPlus : Fin 6 → (Fin 4 → Fin 2) :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 0, 0, 1], ![0, 1, 0, 1], ![0, 0, 1, 1]]

theorem witness_indep4 : ∃ (φ : (Fin 4 → Fin 2) → ℂ) (s : Equiv.Perm (Fin 4 × Fin 3)),
    (∀ q, (s q).1 = q.1) ∧ (wordVal (Fin 3) s (pureOp φ)).im ≠ 0 :=
  ⟨giVec psiPlus, slotPerm tab4 tab4_inj, fun _ => rfl,
    im_ne_zero_of_sumPi _ psiPlus ptsPlus (by decide) (by decide) (by decide +kernel)⟩

end FormalResearch.FrameFree.Twirls

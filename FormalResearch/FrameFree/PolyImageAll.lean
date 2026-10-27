import Mathlib
import FormalResearch.FrameFree.PolyImageMain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Euclidean density of polynomial images (arbitrary index types)

Namespace `FormalResearch.FrameFree.PolyImage`.

`polyImageClosure_all`: the finite case `polyImageClosure_fin` for arbitrary index types `ι`, `κ` (a basic
neighbourhood of `z` in the product topology constrains finitely many coordinates, and finitely many polynomials
involve finitely many variables).
-/

namespace FormalResearch.FrameFree.PolyImage

theorem polyImageClosure_all {ι κ : Type*} (Φ : ι → MvPolynomial κ ℂ) (z : ι → ℂ)
    (h : ∀ p : MvPolynomial ι ℂ, (∀ t : κ → ℂ, MvPolynomial.eval (fun i => MvPolynomial.eval t (Φ i)) p = 0) →
      MvPolynomial.eval z p = 0) :
    z ∈ closure (Set.range fun (t : κ → ℂ) (i : ι) => MvPolynomial.eval t (Φ i)) := by
  classical
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.1 hU
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hVo z hzV
  -- finitely many variables
  let s : Finset κ := I.biUnion fun i => (Φ i).vars
  have hq : ∀ i : ↥I, ∃ q : MvPolynomial ↥s ℂ, MvPolynomial.rename (Subtype.val : ↥s → κ) q = Φ i.1 := by
    intro i
    have : Φ i.1 ∈ MvPolynomial.supported ℂ (↑s : Set κ) := by
      refine (MvPolynomial.mem_supported (R := ℂ)).2 ?_
      intro k hk
      simp only [Finset.mem_coe, s, Finset.mem_biUnion]
      exact ⟨i.1, i.2, by simpa using hk⟩
    rw [MvPolynomial.supported_eq_range_rename] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  choose q hq using hq
  have hev : ∀ (i : ↥I) (t : κ → ℂ), MvPolynomial.eval t (Φ i.1) = MvPolynomial.eval (fun k : ↥s => t k.1) (q i) := by
    intro i t
    rw [← hq i, MvPolynomial.eval_rename]
    rfl
  -- the finite statement
  have hfin := polyImageClosure_fin (fun i : ↥I => q i) (fun i => z i.1) (by
    intro p' hp'
    have := h (MvPolynomial.rename (Subtype.val : ↥I → ι) p') (by
      intro t
      rw [MvPolynomial.eval_rename]
      have e : ((fun i => MvPolynomial.eval t (Φ i)) ∘ (Subtype.val : ↥I → ι)) =
          fun i : ↥I => MvPolynomial.eval (fun k : ↥s => t k.1) (q i) := funext fun i => hev i t
      rw [e]
      exact hp' (fun k : ↥s => t k.1))
    rwa [MvPolynomial.eval_rename] at this)
  have hVo' : IsOpen (Set.pi Set.univ fun i : ↥I => u i.1) :=
    isOpen_set_pi Set.finite_univ fun i _ => (hu i.1 i.2).1
  obtain ⟨_, hmem, ⟨t', rfl⟩⟩ := mem_closure_iff.1 hfin _ hVo' (fun i _ => (hu i.1 i.2).2)
  let t : κ → ℂ := fun k => if hk : k ∈ s then t' ⟨k, hk⟩ else 0
  have ht : ∀ k : ↥s, t k.1 = t' k := fun k => by simp [t, k.2]
  refine ⟨_, hVU (hsub ?_), ⟨t, rfl⟩⟩
  intro i hi
  have := hmem ⟨i, hi⟩ (Set.mem_univ _)
  show MvPolynomial.eval t (Φ i) ∈ u i
  rw [hev ⟨i, hi⟩ t]
  have e : (fun k : ↥s => t k.1) = t' := funext ht
  rw [e]
  exact this

end FormalResearch.FrameFree.PolyImage

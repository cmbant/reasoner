import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Symmetric multilinear maps are determined by their diagonal

A finite real symmetric continuous multilinear map is determined by the
homogeneous polynomial obtained by evaluating it on the diagonal. This is the
polarization principle needed to attack QI-A's coherent-copy separation lemma
without first building a SymmetricPower-to-polynomial API.
-/

namespace FormalResearch.QIA

open Equiv

noncomputable section

/-- A symmetric continuous `n`-linear map over `ℝ` that vanishes on the
diagonal is zero. Symmetry is expressed by invariance under every permutation
of the `Fin n` inputs. -/
theorem continuousMultilinearMap_eq_zero_of_symmetric_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (f : E [×n]→L[ℝ] F)
    (hsymm : ∀ σ : Equiv.Perm (Fin n), f.domDomCongr σ = f)
    (hdiag : ∀ x : E, f (fun _ => x) = 0) :
    f = 0 := by
  apply ContinuousMultilinearMap.ext
  intro v
  have hz :
      iteratedFDeriv ℝ n (fun x : E => f (fun _ => x)) 0 v = 0 := by
    have hfun : (fun x : E => f (fun _ => x)) = (fun _ : E => (0 : F)) := by
      funext x
      exact hdiag x
    rw [hfun]
    simp
  rw [f.iteratedFDeriv_comp_diagonal] at hz
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      f (fun i => v (σ i)) = f v := by
    intro σ
    have h := congrArg
      (fun g : E [×n]→L[ℝ] F => g v) (hsymm σ)
    simpa [ContinuousMultilinearMap.domDomCongr_apply] using h
  simp_rw [hperm] at hz
  have hnat : Nat.factorial n • f v = 0 := by
    simpa [Finset.sum_const, Fintype.card_perm, Fintype.card_fin] using hz
  have hreal : (Nat.factorial n : ℝ) • f v = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hnat
  exact (smul_eq_zero.mp hreal).resolve_left (by positivity)

end

end FormalResearch.QIA

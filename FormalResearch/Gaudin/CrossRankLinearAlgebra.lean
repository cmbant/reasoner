import Mathlib

namespace FormalResearch.Gaudin

/-- Rank-nullity for the joint differential map.  In the manuscript this is
applied to the pair of complete integrable systems `(I,J)` at one tangent
space; `I.prod J` is the linearization of the joint map. -/
theorem joint_rank_via_common_kernel
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B) :
    Module.finrank K (LinearMap.range (I.prod J)) +
        Module.finrank K ((LinearMap.ker I ⊓ LinearMap.ker J : Submodule K V)) =
      Module.finrank K V := by
  rw [← LinearMap.ker_prod]
  exact (I.prod J).finrank_range_add_finrank_ker

/-- If the tangent space has dimension `2n` and the common kernel of the two
joint differentials has dimension `n-r`, then the joint differential has rank
`n+r`.  This is the rank-nullity form of the first identity in the manuscript's
cross-rank lemma. -/
theorem joint_rank_eq_n_add_r
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (n r : Nat)
    (hV : Module.finrank K V = 2 * n)
    (hcommon : Module.finrank K
      ((LinearMap.ker I ⊓ LinearMap.ker J : Submodule K V)) = n - r)
    (hr : r ≤ n) :
    Module.finrank K (LinearMap.range (I.prod J)) = n + r := by
  have h := joint_rank_via_common_kernel I J
  rw [hV, hcommon] at h
  omega

/-- Grassmann dimension identity in the form used for common action
differentials.  If two regular complete systems span `n`-planes and their
combined differential span has dimension `n+r`, then the common differential
span has dimension `n-r`. -/
theorem common_action_span_finrank
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (S T : Submodule K W) (n r : Nat)
    (hS : Module.finrank K S = n)
    (hT : Module.finrank K T = n)
    (hSup : Module.finrank K ((S ⊔ T : Submodule K W)) = n + r) :
    Module.finrank K ((S ⊓ T : Submodule K W)) = n - r := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hSup, hS, hT] at h
  omega

/-- Converse Grassmann form: knowing the common-action dimension `n-r`
forces the combined span to have dimension `n+r`. -/
theorem joint_span_finrank_of_common_actions
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (S T : Submodule K W) (n r : Nat)
    (hS : Module.finrank K S = n)
    (hT : Module.finrank K T = n)
    (hInf : Module.finrank K ((S ⊓ T : Submodule K W)) = n - r)
    (hr : r ≤ n) :
    Module.finrank K ((S ⊔ T : Submodule K W)) = n + r := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hInf, hS, hT] at h
  omega

end FormalResearch.Gaudin

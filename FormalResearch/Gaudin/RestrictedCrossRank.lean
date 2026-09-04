import Mathlib
import FormalResearch.Gaudin.CrossRankLinearAlgebra

namespace FormalResearch.Gaudin

/-- The kernel of `J` restricted to the `I`-fiber is canonically the common
kernel of `I` and `J`. -/
noncomputable def kerRestrictedEquivCommonKernel
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B) :
    LinearMap.ker (J.domRestrict (LinearMap.ker I)) ≃ₗ[K]
      ((LinearMap.ker I ⊓ LinearMap.ker J : Submodule K V)) where
  toFun x := ⟨x.1.1, by
    constructor
    · exact x.1.2
    · have hx : (J.domRestrict (LinearMap.ker I)) x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      exact LinearMap.mem_ker.mpr (by simpa using hx)⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, by
    rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.mp y.2.2⟩
  left_inv x := by
    rfl
  right_inv y := by
    rfl
  map_add' x y := by
    rfl
  map_smul' a x := by
    rfl

/-- Dimension form of the kernel identification. -/
theorem restricted_kernel_finrank_eq_common_kernel
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B) :
    Module.finrank K (LinearMap.ker (J.domRestrict (LinearMap.ker I))) =
      Module.finrank K ((LinearMap.ker I ⊓ LinearMap.ker J : Submodule K V)) := by
  exact LinearEquiv.finrank_eq (kerRestrictedEquivCommonKernel I J)

/-- Exact rank decomposition for a joint map: the extra rank contributed by
`J` beyond `I` is precisely the rank of `J` restricted to the fiber
`ker I`.  This is the finite-dimensional algebraic core of the cross-Poisson
rank lemma. -/
theorem joint_rank_eq_rank_add_restricted_rank
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B) :
    Module.finrank K (LinearMap.range (I.prod J)) =
      Module.finrank K (LinearMap.range I) +
        Module.finrank K
          (LinearMap.range (J.domRestrict (LinearMap.ker I))) := by
  have hI := I.finrank_range_add_finrank_ker
  have hJ := (J.domRestrict (LinearMap.ker I)).finrank_range_add_finrank_ker
  have hIJ := joint_rank_via_common_kernel I J
  have hker := restricted_kernel_finrank_eq_common_kernel I J
  omega

/-- Regular-complete specialization: if `I` has rank `n` and the restricted
`J` map on the `I`-fiber has rank `r`, then the joint differential has rank
`n+r`. -/
theorem joint_rank_eq_n_add_cross_rank
    {K V A B : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B) (n r : Nat)
    (hI : Module.finrank K (LinearMap.range I) = n)
    (hCross : Module.finrank K
      (LinearMap.range (J.domRestrict (LinearMap.ker I))) = r) :
    Module.finrank K (LinearMap.range (I.prod J)) = n + r := by
  rw [joint_rank_eq_rank_add_restricted_rank I J, hI, hCross]

/-- Common-codomain Grassmann companion.  If the two differential spans live
in one cotangent space, each has dimension `n`, and their sum has the joint
rank `n+r`, then their intersection has dimension `n-r`. -/
theorem common_action_dimension_from_joint_span
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (S T : Submodule K W) (n r : Nat)
    (hS : Module.finrank K S = n)
    (hT : Module.finrank K T = n)
    (hJointSpan : Module.finrank K ((S ⊔ T : Submodule K W)) = n + r) :
    Module.finrank K ((S ⊓ T : Submodule K W)) = n - r :=
  common_action_span_finrank S T n r hS hT hJointSpan

end FormalResearch.Gaudin

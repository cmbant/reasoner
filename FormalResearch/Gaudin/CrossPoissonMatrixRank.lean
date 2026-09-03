import Mathlib
import FormalResearch.Gaudin.RestrictedCrossRank

namespace FormalResearch.Gaudin

/-- Basis matrix of the second differential restricted to the regular fiber of
the first one.  In a symplectic application, once the domain basis is chosen to
be Hamiltonian fields of the first integrals, these entries are the cross
Poisson brackets. -/
def crossFiberMatrix
    {K V A B ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B) :
    Matrix κ ι K :=
  LinearMap.toMatrix bFiber bB (J.domRestrict (LinearMap.ker I))

/-- Matrix rank is exactly the rank of the restricted fiber map, independently
of the chosen fiber and target bases.  This is the finite-dimensional linear
algebra statement behind the G-I cross-Poisson rank identification. -/
theorem crossFiberMatrix_rank_eq_restricted_rank
    {K V A B ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B) :
    (crossFiberMatrix I J bFiber bB).rank =
      Module.finrank K
        (LinearMap.range (J.domRestrict (LinearMap.ker I))) := by
  unfold crossFiberMatrix
  rw [Matrix.rank_eq_finrank_range_toLin _ bB bFiber,
    Matrix.toLin_toMatrix]

/-- If the displayed cross-fiber matrix has rank `r`, then the restricted map
has rank `r`. -/
theorem restricted_rank_eq_of_crossFiberMatrix_rank
    {K V A B ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B)
    (r : Nat)
    (hMatrix : (crossFiberMatrix I J bFiber bB).rank = r) :
    Module.finrank K
      (LinearMap.range (J.domRestrict (LinearMap.ker I))) = r := by
  rw [← crossFiberMatrix_rank_eq_restricted_rank I J bFiber bB]
  exact hMatrix

/-- Matrix form of the regular cross-rank lemma.  If the first differential has
rank `n` and the cross-fiber matrix has rank `r`, the joint differential has
rank `n+r`. -/
theorem joint_rank_eq_n_add_crossFiberMatrix_rank
    {K V A B ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    [FiniteDimensional K V]
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (I : V →ₗ[K] A) (J : V →ₗ[K] B)
    (bFiber : Basis ι K (LinearMap.ker I)) (bB : Basis κ K B)
    (n r : Nat)
    (hI : Module.finrank K (LinearMap.range I) = n)
    (hMatrix : (crossFiberMatrix I J bFiber bB).rank = r) :
    Module.finrank K (LinearMap.range (I.prod J)) = n + r := by
  apply joint_rank_eq_n_add_cross_rank I J n r hI
  exact restricted_rank_eq_of_crossFiberMatrix_rank
    I J bFiber bB r hMatrix

end FormalResearch.Gaudin

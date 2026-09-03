import Mathlib
import FormalResearch.QIC.Endpoint14PolynomialIdentity
import FormalResearch.QIC.QubitTailAllLNonvanishing

namespace FormalResearch.QIC

/-- Faithful embedding of the lightweight certificate pairs into mathlib's
actual Gaussian-integer Euclidean domain. -/
def toGaussian (z : GInt) : GaussianInt := ⟨z.1, z.2⟩

@[simp] lemma toGaussian_zero : toGaussian giZero = 0 := by rfl
@[simp] lemma toGaussian_one : toGaussian giOne = 1 := by rfl
@[simp] lemma toGaussian_const (c : Int) : toGaussian (giConst c) = c := by rfl

@[simp] lemma toGaussian_add (z w : GInt) :
    toGaussian (giAdd z w) = toGaussian z + toGaussian w := by
  rfl

@[simp] lemma toGaussian_mul (z w : GInt) :
    toGaussian (giMul z w) = toGaussian z * toGaussian w := by
  ext <;> simp [toGaussian, giMul, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

@[simp] lemma toGaussian_sub (z w : GInt) :
    toGaussian (giSub z w) = toGaussian z - toGaussian w := by
  rfl

@[simp] lemma toGaussian_pow (z : GInt) (n : Nat) :
    toGaussian (giPow z n) = toGaussian z ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [giPow, pow_succ]
      rw [toGaussian_mul, ih]

lemma toGaussian_injective : Function.Injective toGaussian := by
  intro z w h
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  exact Prod.ext hr hi

lemma toGaussian_ne_zero {z : GInt} (hz : z ≠ giZero) : toGaussian z ≠ 0 := by
  intro h
  exact hz (toGaussian_injective (by simpa using h))

/-- Horner evaluation is preserved by the Gaussian-integer embedding. -/
lemma toGaussian_eval5 (c0 c1 c2 c3 c4 c5 : Int) (z : GInt) :
    toGaussian (giEval5 c0 c1 c2 c3 c4 c5 z) =
      c0 + toGaussian z *
        (c1 + toGaussian z *
          (c2 + toGaussian z *
            (c3 + toGaussian z * (c4 + toGaussian z * c5)))) := by
  simp [giEval5]

/-- The physical tail parameter as a genuine Gaussian integer. -/
def gaussianTail (L : Nat) : GaussianInt := toGaussian (giPow giBase L)

lemma gaussianTail_pow (L : Nat) :
    gaussianTail L = (⟨1, -1⟩ : GaussianInt) ^ L := by
  simp [gaussianTail, toGaussian_pow, giBase, toGaussian]

lemma gaussianTail_ne_zero (L : Nat) : gaussianTail L ≠ 0 :=
  toGaussian_ne_zero (giPow_ne_zero (by native_decide : giBase ≠ giZero) L)

lemma gaussianTail_ne_one {L : Nat} (hL : 1 ≤ L) : gaussianTail L ≠ 1 := by
  intro h
  exact giPow_base_ne_one hL (toGaussian_injective (by simpa [gaussianTail] using h))

lemma gaussianTail_ne_two {L : Nat} (hL : 1 ≤ L) : gaussianTail L ≠ 2 := by
  intro h
  exact giPow_base_ne_two hL (toGaussian_injective (by simpa [gaussianTail] using h))

lemma gaussian_p3_nonzero (L : Nat) :
    2 * gaussianTail L ^ 3 - 3 * gaussianTail L ^ 2 - gaussianTail L - 3 ≠ 0 := by
  have h := toGaussian_ne_zero (p3_all_powers_nonzero L)
  rw [toGaussian_eval5] at h
  simpa [gaussianTail] using h

lemma gaussian_p4_nonzero (L : Nat) :
    144 * gaussianTail L ^ 4 - 60 * gaussianTail L ^ 3 -
      841 * gaussianTail L ^ 2 + 633 * gaussianTail L + 258 ≠ 0 := by
  have h := toGaussian_ne_zero (p4_all_powers_nonzero L)
  rw [toGaussian_eval5] at h
  simpa [gaussianTail] using h

/-- The manuscript's complete endpoint determinant factor is nonzero at every
physical tail length. -/
theorem expectedEndpointPoly_gaussian_nonzero {L : Nat} (hL : 1 ≤ L) :
    Polynomial.eval₂ (Int.castRingHom GaussianInt) (gaussianTail L)
      expectedEndpointPoly ≠ 0 := by
  rw [show Polynomial.eval₂ (Int.castRingHom GaussianInt) (gaussianTail L)
      expectedEndpointPoly =
      (195689447424 : GaussianInt) * gaussianTail L ^ 28 *
        (gaussianTail L - 1)^8 * (gaussianTail L - 2)^2 *
        (2 * gaussianTail L^3 - 3 * gaussianTail L^2 - gaussianTail L - 3) *
        (144 * gaussianTail L^4 - 60 * gaussianTail L^3 -
          841 * gaussianTail L^2 + 633 * gaussianTail L + 258) := by
      simp [expectedEndpointPoly]
      ring]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (pow_ne_zero _ (gaussianTail_ne_zero L)))
          (pow_ne_zero _ (sub_ne_zero.mpr (gaussianTail_ne_one hL))))
        (pow_ne_zero _ (sub_ne_zero.mpr (gaussianTail_ne_two hL))))
      (gaussian_p3_nonzero L))
    (gaussian_p4_nonzero L)

/-- Evaluate the actual endpoint polynomial matrix at the physical Gaussian
parameter. -/
def endpointGaussian (L : Nat) : Matrix Fin14 Fin14 GaussianInt :=
  endpointPoly.map
    (Polynomial.eval₂RingHom (Int.castRingHom GaussianInt) (gaussianTail L))

/-- The fixed 14x14 endpoint minor is nonsingular for every `L≥1`.  This is the
kernel-checked endpoint rank certificate needed in the all-qubit tail proof. -/
theorem endpointGaussian_det_nonzero {L : Nat} (hL : 1 ≤ L) :
    Matrix.det (endpointGaussian L) ≠ 0 := by
  have hpoly := congrArg
    (Polynomial.eval₂RingHom (Int.castRingHom GaussianInt) (gaussianTail L))
    endpoint_det_polynomial_identity
  rw [RingHom.map_det] at hpoly
  change Matrix.det (endpointGaussian L) = _ at hpoly
  rw [hpoly]
  exact expectedEndpointPoly_gaussian_nonzero hL

end FormalResearch.QIC

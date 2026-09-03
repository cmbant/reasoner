import Mathlib
import FormalResearch.QIC.GaussianIntegerLift

namespace FormalResearch.QIC

/-- Squared Gaussian norm on the lightweight integer-pair model used by the
certificate files. -/
def giNormSq (z : GInt) : Int := z.1 ^ 2 + z.2 ^ 2

def giSub (z w : GInt) : GInt := (z.1 - w.1, z.2 - w.2)

lemma giNormSq_mul (z w : GInt) :
    giNormSq (giMul z w) = giNormSq z * giNormSq w := by
  simp [giNormSq, giMul]
  ring

lemma giNormSq_zero : giNormSq giZero = 0 := by norm_num [giNormSq, giZero]
lemma giNormSq_one : giNormSq giOne = 1 := by norm_num [giNormSq, giOne]
lemma giNormSq_base : giNormSq giBase = 2 := by norm_num [giNormSq, giBase]
lemma giNormSq_const_two : giNormSq (giConst 2) = 4 := by norm_num [giNormSq, giConst]

lemma giNormSq_eq_zero_iff (z : GInt) : giNormSq z = 0 ↔ z = giZero := by
  constructor
  · intro h
    have hx : z.1 = 0 := by
      have hx0 : 0 ≤ z.1 ^ 2 := sq_nonneg z.1
      have hy0 : 0 ≤ z.2 ^ 2 := sq_nonneg z.2
      nlinarith [h]
    have hy : z.2 = 0 := by
      have hx0 : 0 ≤ z.1 ^ 2 := sq_nonneg z.1
      have hy0 : 0 ≤ z.2 ^ 2 := sq_nonneg z.2
      nlinarith [h]
    ext <;> simp [giZero, hx, hy]
  · rintro rfl
    exact giNormSq_zero

lemma giMul_ne_zero {z w : GInt} (hz : z ≠ giZero) (hw : w ≠ giZero) :
    giMul z w ≠ giZero := by
  intro h
  have hn : giNormSq (giMul z w) = 0 := (giNormSq_eq_zero_iff _).2 h
  rw [giNormSq_mul] at hn
  rcases mul_eq_zero.mp hn with hz0 | hw0
  · exact hz ((giNormSq_eq_zero_iff z).1 hz0)
  · exact hw ((giNormSq_eq_zero_iff w).1 hw0)

lemma giPow_ne_zero {z : GInt} (hz : z ≠ giZero) (n : Nat) :
    giPow z n ≠ giZero := by
  induction n with
  | zero => norm_num [giPow, giOne, giZero]
  | succ n ih =>
      simpa [giPow] using giMul_ne_zero ih hz

lemma giNormSq_base_pow (L : Nat) :
    giNormSq (giPow giBase L) = (2 : Int) ^ L := by
  induction L with
  | zero => norm_num [giPow, giNormSq_one]
  | succ L ih =>
      rw [giPow, giNormSq_mul, ih, giNormSq_base, pow_succ]

lemma giPow_base_ne_one {L : Nat} (hL : 1 ≤ L) :
    giPow giBase L ≠ giOne := by
  intro h
  have hn := congrArg giNormSq h
  rw [giNormSq_base_pow, giNormSq_one] at hn
  have hzero : L = 0 := by
    apply Int.pow_right_injective (a := 2) (by norm_num)
    simpa using hn
  omega

lemma giPow_base_ne_two {L : Nat} (hL : 1 ≤ L) :
    giPow giBase L ≠ giConst 2 := by
  intro h
  have hn := congrArg giNormSq h
  rw [giNormSq_base_pow, giNormSq_const_two] at hn
  have htwo : L = 2 := by
    apply Int.pow_right_injective (a := 2) (by norm_num)
    norm_num at hn ⊢
    exact hn
  subst L
  native_decide

lemma giSub_eq_zero_iff (z w : GInt) : giSub z w = giZero ↔ z = w := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp [giSub, giZero] at h1 h2
    ext <;> assumption
  · rintro rfl
    ext <;> simp [giSub, giZero]

lemma giSub_ne_zero_of_ne {z w : GInt} (h : z ≠ w) : giSub z w ≠ giZero := by
  intro hz
  exact h ((giSub_eq_zero_iff z w).1 hz)

lemma giConst_ne_zero {c : Int} (h : c ≠ 0) : giConst c ≠ giZero := by
  intro hc
  have := congrArg Prod.fst hc
  simpa [giConst, giZero] using this

/-- The common linear factors in both 8x8 determinants are nonzero at every
physical tail power `t=(1-i)^L`, `L≥1`. -/
theorem tail_linear_factors_nonzero {L : Nat} (hL : 1 ≤ L) :
    giSub (giPow giBase L) giOne ≠ giZero ∧
    giSub (giPow giBase L) (giConst 2) ≠ giZero := by
  exact ⟨giSub_ne_zero_of_ne (giPow_base_ne_one hL),
    giSub_ne_zero_of_ne (giPow_base_ne_two hL)⟩

/-- Direct characteristic-zero nonvanishing of the fraction-free scalar for
`D(t)+R(t)` at every physical tail length. -/
def tailPlusScalar (L : Nat) : GInt :=
  giMul (giConst (-6144)) <|
    giMul (giSub (giPow giBase L) (giConst 2)) <|
      giMul (giSub (giPow giBase L) giOne)
        (giEval5 76323 (-31772) (-68674) (-8079) 11018 2448 (giPow giBase L))

/-- Direct characteristic-zero nonvanishing of the fraction-free scalar for
`D(t)-R(t)` at every physical tail length. -/
def tailMinusScalar (L : Nat) : GInt :=
  giMul (giConst 6144) <|
    giMul (giSub (giPow giBase L) (giConst 2)) <|
      giMul (giSub (giPow giBase L) giOne)
        (giEval5 (-2181) 51862 (-195988) 249625 (-126366) 20304 (giPow giBase L))

theorem tailPlusScalar_nonzero {L : Nat} (hL : 1 ≤ L) :
    tailPlusScalar L ≠ giZero := by
  rcases tail_linear_factors_nonzero hL with ⟨h1, h2⟩
  unfold tailPlusScalar
  exact giMul_ne_zero (giConst_ne_zero (by norm_num))
    (giMul_ne_zero h2 (giMul_ne_zero h1 (qPlus_all_powers_nonzero L)))

theorem tailMinusScalar_nonzero {L : Nat} (hL : 1 ≤ L) :
    tailMinusScalar L ≠ giZero := by
  rcases tail_linear_factors_nonzero hL with ⟨h1, h2⟩
  unfold tailMinusScalar
  exact giMul_ne_zero (giConst_ne_zero (by norm_num))
    (giMul_ne_zero h2 (giMul_ne_zero h1 (qMinus_all_powers_nonzero L)))

/-- Scalar factor of the fixed 14x14 endpoint minor, omitting only its nonzero
integer constant. -/
def endpointScalar (L : Nat) : GInt :=
  let t := giPow giBase L
  giMul (giPow t 28) <|
    giMul (giPow (giSub t giOne) 8) <|
      giMul (giPow (giSub t (giConst 2)) 2) <|
        giMul (giEval5 (-3) (-1) (-3) 2 0 0 t)
          (giEval5 258 633 (-841) (-60) 144 0 t)

/-- The endpoint minor's complete nonconstant factor is nonzero for every
`L≥1`. This combines the finite-field certificates for the cubic/quartic with
exact Gaussian norm arguments for `t`, `t-1`, and `t-2`. -/
theorem endpointScalar_nonzero {L : Nat} (hL : 1 ≤ L) :
    endpointScalar L ≠ giZero := by
  rcases tail_linear_factors_nonzero hL with ⟨h1, h2⟩
  have ht : giPow giBase L ≠ giZero := giPow_ne_zero (by native_decide : giBase ≠ giZero) L
  unfold endpointScalar
  exact giMul_ne_zero (giPow_ne_zero ht 28)
    (giMul_ne_zero (giPow_ne_zero h1 8)
      (giMul_ne_zero (giPow_ne_zero h2 2)
        (giMul_ne_zero (p3_all_powers_nonzero L) (p4_all_powers_nonzero L))))

end FormalResearch.QIC

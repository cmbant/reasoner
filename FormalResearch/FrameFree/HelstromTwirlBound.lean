import Mathlib
import FormalResearch.FrameFree.HelstromPure
import FormalResearch.FrameFree.HelstromLinAlg
import FormalResearch.FrameFree.HelstromTwirl
import FormalResearch.FrameFree.HelstromPS

/-!
# Twirled Powers-Stormer bound (generic finite-dimensional statement)

Namespace `FormalResearch.FrameFree.Helstrom`.  `twirl_helstrom`: for a set `G` of unitaries closed under
products, vectors `a, b` whose `G`-orbits lie in a subspace `W`, and `F ≥ |⟨a|U b⟩|²` for all `U ∈ G`,
there is a `G`-invariant effect `E` with `err E a b ≤ ½ √(dim W · F)`.

Proof (no Haar measure, no trace norm): `twirl_props` twirls `|a⟩⟨a|` and `|b⟩⟨b|` to `G`-invariant
positive semidefinite matrices `Z_a, Z_b` supported in `W` (`HelstromTwirl.twirl_exists`), with
`tr(E Z) = ⟨v|E|v⟩` for invariant `E` and `tr(Z_b Z_a) = ⟨a|Z_b|a⟩ ≤ F`.  The Powers-Stormer projector
(`HelstromPS.power_stormer`) of `√Z_b, √Z_a` is `G`-invariant and has error at most
`½ tr(√Z_b √Z_a) ≤ ½ √(dim W · tr(Z_b Z_a))` by the Hilbert-Schmidt Cauchy-Schwarz inequality
(`HelstromLinAlg.hs_cs`) and `tr(projMat W) = dim W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped MatrixOrder ComplexOrder InnerProductSpace
open Matrix

namespace FormalResearch.FrameFree.Helstrom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tr_mul_vecMulVec (A : Matrix ι ι ℂ) (c : ι → ℂ) :
    (A * Matrix.vecMulVec c (star c)).trace = star c ⬝ᵥ (A *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [dotProduct_comm]

theorem conj_vecMulVec (U : Matrix ι ι ℂ) (c : ι → ℂ) :
    U * Matrix.vecMulVec c (star c) * Uᴴ = Matrix.vecMulVec (U *ᵥ c) (star (U *ᵥ c)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem vecMulVec_posSemidef (c : ι → ℂ) : (Matrix.vecMulVec c (star c)).PosSemidef := by
  exact posSemidef_vecMulVec_self_star c

theorem qf_vecMulVec_re (a c : ι → ℂ) :
    (star a ⬝ᵥ (Matrix.vecMulVec c (star c) *ᵥ a)).re = Complex.normSq (star a ⬝ᵥ c) := by
  have h1 : Matrix.vecMulVec c (star c) *ᵥ a = (star c ⬝ᵥ a) • c := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [h1, dotProduct_smul, smul_eq_mul]
  have : star c ⬝ᵥ a = star (star a ⬝ᵥ c) := by
    rw [star_dotProduct]
  rw [this]
  generalize star a ⬝ᵥ c = z
  simp [Complex.normSq_apply, Complex.mul_re]

theorem closed_fixed (Q : Matrix ι ι ℂ) : IsClosed {M : Matrix ι ι ℂ | Q * M * Q = M} :=
  isClosed_eq ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) continuous_id

theorem convex_fixed (Q : Matrix ι ι ℂ) : Convex ℝ {M : Matrix ι ι ℂ | Q * M * Q = M} := by
  intro A hA B hB a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_mul, hA, hB]

theorem closed_trace (A : Matrix ι ι ℂ) (c : ℂ) :
    IsClosed {M : Matrix ι ι ℂ | (A * M).trace = c} :=
  isClosed_eq (continuous_const.matrix_mul continuous_id).matrix_trace continuous_const

theorem convex_trace (A : Matrix ι ι ℂ) (c : ℂ) : Convex ℝ {M : Matrix ι ι ℂ | (A * M).trace = c} := by
  intro P hP Q hQ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, hP, hQ, ← add_smul, hab, one_smul]

theorem closed_qf_le (x : ι → ℂ) (F : ℝ) :
    IsClosed {M : Matrix ι ι ℂ | (star x ⬝ᵥ (M *ᵥ x)).re ≤ F} :=
  isClosed_le (Complex.continuous_re.comp (continuous_qf x x)) continuous_const

theorem convex_qf_le (x : ι → ℂ) (F : ℝ) :
    Convex ℝ {M : Matrix ι ι ℂ | (star x ⬝ᵥ (M *ᵥ x)).re ≤ F} := by
  intro P hP Q hQ a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul]
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have h1 := mul_le_mul_of_nonneg_left hP ha
  have h2 := mul_le_mul_of_nonneg_left hQ hb
  have h3 : a * F + b * F = F := by rw [← add_mul, hab, one_mul]
  linarith

theorem twirl_props (G : Set (Matrix ι ι ℂ)) (hG1 : ∀ U ∈ G, Uᴴ * U = 1)
    (hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G) (hne : G.Nonempty)
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) (c : ι → ℂ)
    (hc : ∀ U ∈ G, WithLp.toLp 2 (U *ᵥ c) ∈ W) :
    ∃ Z : Matrix ι ι ℂ, Z.PosSemidef ∧ projMat W * Z * projMat W = Z ∧
      (∀ U ∈ G, U * Z = Z * U) ∧
      (∀ E : Matrix ι ι ℂ, (∀ U ∈ G, U * E = E * U) → (E * Z).trace = star c ⬝ᵥ (E *ᵥ c)) ∧
      (∀ (x : ι → ℂ) (F : ℝ),
        (∀ U ∈ G, (star x ⬝ᵥ (Matrix.vecMulVec (U *ᵥ c) (star (U *ᵥ c)) *ᵥ x)).re ≤ F) →
        (star x ⬝ᵥ (Z *ᵥ x)).re ≤ F) := by
  obtain ⟨Z, hZ, hcomm⟩ := twirl_exists G hG1 hmul hne (Matrix.vecMulVec c (star c))
  have hPj : (projMat W)ᴴ = projMat W := (projMat_posSemidef W).1
  refine ⟨Z, ?_, ?_, hcomm, ?_, ?_⟩
  · refine hZ _ isClosed_posSemidef convex_posSemidef (fun U hU => ?_)
    rw [conj_vecMulVec]
    exact posSemidef_vecMulVec_self_star _
  · refine hZ {M | projMat W * M * projMat W = M} (closed_fixed _) (convex_fixed _) (fun U hU => ?_)
    show projMat W * (U * Matrix.vecMulVec c (star c) * Uᴴ) * projMat W = U * Matrix.vecMulVec c (star c) * Uᴴ
    rw [conj_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      projMat_mulVec_of_mem W (hc U hU)]
    have h := Matrix.star_mulVec (projMat W) (U *ᵥ c)
    rw [projMat_mulVec_of_mem W (hc U hU), hPj] at h
    rw [← h]
  · intro E hE
    have := hZ {M | (E * M).trace = (E * Matrix.vecMulVec c (star c)).trace}
      (closed_trace _ _) (convex_trace _ _) (fun U hU => ?_)
    · exact (this.trans (tr_mul_vecMulVec E c))
    · show (E * (U * Matrix.vecMulVec c (star c) * Uᴴ)).trace = _
      calc (E * (U * Matrix.vecMulVec c (star c) * Uᴴ)).trace
          = (U * (E * Matrix.vecMulVec c (star c)) * Uᴴ).trace := by
            rw [show E * (U * Matrix.vecMulVec c (star c) * Uᴴ)
              = (E * U) * Matrix.vecMulVec c (star c) * Uᴴ by simp only [Matrix.mul_assoc], ← hE U hU]
            simp only [Matrix.mul_assoc]
        _ = (Uᴴ * U * (E * Matrix.vecMulVec c (star c))).trace := Matrix.trace_mul_cycle _ _ _
        _ = _ := by rw [hG1 U hU, Matrix.one_mul]
  · intro x F hF
    exact hZ {M | (star x ⬝ᵥ (M *ᵥ x)).re ≤ F} (closed_qf_le x F) (convex_qf_le x F)
      (fun U hU => by rw [Set.mem_setOf_eq, conj_vecMulVec]; exact hF U hU)

/-- **Twirled Powers-Stormer bound** (generic).  Let `G` be a set of unitaries closed under products, `W` a
subspace containing all `U a` and `U b` (`U ∈ G`), and `F` a bound for `|⟨a|U b⟩|²`.  Then there is a
`G`-invariant effect with error at most `½ √(dim W · F)`. -/
theorem twirl_helstrom (G : Set (Matrix ι ι ℂ)) (hG1 : ∀ U ∈ G, Uᴴ * U = 1)
    (hmul : ∀ U ∈ G, ∀ V ∈ G, U * V ∈ G) (hne : G.Nonempty)
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) (a b : ι → ℂ)
    (ha : ∀ U ∈ G, WithLp.toLp 2 (U *ᵥ a) ∈ W) (hb : ∀ U ∈ G, WithLp.toLp 2 (U *ᵥ b) ∈ W)
    (F : ℝ) (hF : ∀ U ∈ G, Complex.normSq (star a ⬝ᵥ (U *ᵥ b)) ≤ F) :
    ∃ E : Matrix ι ι ℂ, IsEffect E ∧ (∀ U ∈ G, U * E = E * U) ∧
      err E a b ≤ Real.sqrt ((Module.finrank ℂ W : ℝ) * F) / 2 := by
  obtain ⟨Zr, hr1, hr2, hr3, hr4, hr5⟩ := twirl_props G hG1 hmul hne W a ha
  obtain ⟨Zs, hs1, hs2, hs3, hs4, hs5⟩ := twirl_props G hG1 hmul hne W b hb
  have hq : (star a ⬝ᵥ (Zs *ᵥ a)).re ≤ F :=
    hs5 a F (fun U hU => by rw [qf_vecMulVec_re]; exact hF U hU)
  have htr : (Zs * Zr).trace = star a ⬝ᵥ (Zs *ᵥ a) := hr4 Zs hs3
  have hXn : 0 ≤ Zs := Matrix.nonneg_iff_posSemidef.2 hs1
  have hYn : 0 ≤ Zr := Matrix.nonneg_iff_posSemidef.2 hr1
  obtain ⟨X, hXdef⟩ : ∃ X, X = CFC.sqrt Zs := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = CFC.sqrt Zr := ⟨_, rfl⟩
  have hXp : X.PosSemidef := hXdef ▸ (CFC.sqrt_nonneg Zs).posSemidef
  have hYp : Y.PosSemidef := hYdef ▸ (CFC.sqrt_nonneg Zr).posSemidef
  have hXX : X * X = Zs := hXdef ▸ CFC.sqrt_mul_sqrt_self Zs hXn
  have hYY : Y * Y = Zr := hYdef ▸ CFC.sqrt_mul_sqrt_self Zr hYn
  have hXc : ∀ U ∈ G, Commute X U := fun U hU =>
    hXdef ▸ Commute.cfcₙ_nnreal (a := Zs) (b := U) (hs3 U hU).symm NNReal.sqrt
  have hYc : ∀ U ∈ G, Commute Y U := fun U hU =>
    hYdef ▸ Commute.cfcₙ_nnreal (a := Zr) (b := U) (hr3 U hU).symm NNReal.sqrt
  obtain ⟨P, hP1, hP2, hP3, hP4⟩ := power_stormer hXp hYp
  have hPc : ∀ U ∈ G, U * P = P * U := fun U hU => ((hP3 U (hXc U hU) (hYc U hU)).eq).symm
  have hPc' : ∀ U ∈ G, U * (1 - P) = (1 - P) * U := fun U hU => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hPc U hU]
  refine ⟨P, ⟨hP1, hP2⟩, hPc, ?_⟩
  -- the trace bound
  have hPrP : (Y * Y * P).trace = star a ⬝ᵥ (P *ᵥ a) := by
    rw [hYY, Matrix.trace_mul_comm]; exact hr4 P hPc
  have hPsP : (X * X * (1 - P)).trace = star b ⬝ᵥ ((1 - P) *ᵥ b) := by
    rw [hXX, Matrix.trace_mul_comm]; exact hs4 (1 - P) hPc'
  have hmain : (star a ⬝ᵥ (P *ᵥ a)).re + (star b ⬝ᵥ ((1 - P) *ᵥ b)).re ≤ (X * Y).trace.re := by
    have := hP4
    rw [hPrP, hPsP] at this
    linarith
  -- support: Y = Pj Y
  have hPjh : (projMat W)ᴴ = projMat W := (projMat_posSemidef W).1
  have hPj2 := projMat_mul_self W
  have hQZ : (1 - projMat W) * Zr = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    nth_rewrite 2 [← hr2]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPj2]
    simp [hr2]
  have hYQ : Y * (1 - projMat W) = 0 := by
    have hQh : (1 - projMat W)ᴴ = 1 - projMat W := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPjh]
    have h0 : (Y * (1 - projMat W))ᴴ * (Y * (1 - projMat W)) = 0 := by
      rw [Matrix.conjTranspose_mul, hQh, hYp.1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYY,
        ← Matrix.mul_assoc, hQZ, Matrix.zero_mul]
    exact Matrix.conjTranspose_mul_self_eq_zero.1 h0
  have hPjY : projMat W * Y = Y := by
    have h1 : Y = Y * projMat W := by
      have := hYQ
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
      exact this
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, hPjh, hYp.1.eq] at h2
    exact h2.symm
  have hcs := hs_cs (projMat W) (Y * X)
  have e1 : projMat W * (Y * X) = Y * X := by rw [← Matrix.mul_assoc, hPjY]
  have e2 : ((projMat W)ᴴ * projMat W).trace.re = (Module.finrank ℂ W : ℝ) := by
    rw [hPjh, hPj2, trace_projMat]; simp
  have e3 : (Y * X * (Y * X)ᴴ).trace = (Zs * Zr).trace := by
    rw [Matrix.conjTranspose_mul, hXp.1.eq, hYp.1.eq]
    calc (Y * X * (X * Y)).trace = (Y * (X * X) * Y).trace := by simp only [Matrix.mul_assoc]
      _ = (Y * Y * (X * X)).trace := Matrix.trace_mul_cycle _ _ _
      _ = (Zr * Zs).trace := by rw [hXX, hYY]
      _ = (Zs * Zr).trace := Matrix.trace_mul_comm _ _
  rw [e1, e2, e3, htr, Matrix.trace_mul_comm Y X] at hcs
  have hfr : (0 : ℝ) ≤ (Module.finrank ℂ W : ℝ) := Nat.cast_nonneg _
  have hcs2 : Complex.normSq (X * Y).trace ≤ (Module.finrank ℂ W : ℝ) * F :=
    hcs.trans (mul_le_mul_of_nonneg_left hq hfr)
  have hre : (X * Y).trace.re ≤ Real.sqrt ((Module.finrank ℂ W : ℝ) * F) := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    refine le_trans ?_ hcs2
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (X * Y).trace.im]
  show (star a ⬝ᵥ (P *ᵥ a)).re / 2 + (star b ⬝ᵥ ((1 - P) *ᵥ b)).re / 2 ≤ _
  linarith

end FormalResearch.FrameFree.Helstrom

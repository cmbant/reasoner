module

public import Mathlib

/-!
# Polar unitary of a finite intertwiner (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:polarintertwiner`.

Finite-dimensional complex Hilbert spaces `V`, `W`; `H₀ : V → V`, `H₁ : W → W` self-adjoint;
`T : V → W` bijective with `H₁ T = T H₀`.  Then `T*T` commutes with `H₀` and
`U = T (T*T)^{-1/2}` (`polarU T = T ∘ (√(T*T))⁻¹`, square root of the positive operator `T*T` by the
continuous functional calculus) is unitary and still intertwines.

The hypothesis `dim V = dim W` of the paper is implied by bijectivity of `T`; the proof is over `ℂ`
(the functional calculus of Mathlib is for `C*`-algebras over `ℂ`), which contains the real case
by complexification.
-/

@[expose] public section

namespace FormalResearch.Racah

open scoped ComplexOrder

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

open ContinuousLinearMap in
/-- The positive operator `T*T`. -/
noncomputable def gram (T : V →L[ℂ] W) : V →L[ℂ] V := (adjoint T).comp T

/-- The polar unitary `U = T (T*T)^{-1/2}`. -/
noncomputable def polarU (T : V →L[ℂ] W) : V →L[ℂ] W :=
  T.comp (Ring.inverse (CFC.sqrt (gram T)))

open ContinuousLinearMap in
/-- **`lem:polarintertwiner`**, first claim: `T*T` commutes with `H₀`. -/
theorem gram_commute (H0 : V →L[ℂ] V) (H1 : W →L[ℂ] W) (hH0 : IsSelfAdjoint H0)
    (hH1 : IsSelfAdjoint H1) (T : V →L[ℂ] W) (hint : H1.comp T = T.comp H0) :
    Commute (gram T) H0 := by
  have h1 : (adjoint T).comp H1 = H0.comp (adjoint T) := by
    have := congrArg adjoint hint
    rw [adjoint_comp, adjoint_comp] at this
    have e1 : adjoint H1 = H1 := by rw [← star_eq_adjoint]; exact hH1.star_eq
    have e0 : adjoint H0 = H0 := by rw [← star_eq_adjoint]; exact hH0.star_eq
    rwa [e1, e0] at this
  show (gram T) * H0 = H0 * (gram T)
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  unfold gram
  calc ((adjoint T).comp T).comp H0 = (adjoint T).comp (T.comp H0) := rfl
    _ = (adjoint T).comp (H1.comp T) := by rw [hint]
    _ = ((adjoint T).comp H1).comp T := rfl
    _ = (H0.comp (adjoint T)).comp T := by rw [h1]
    _ = H0.comp ((adjoint T).comp T) := rfl

lemma exists_inv (T : V →L[ℂ] W) (hT : Function.Bijective T) :
    ∃ Ti : W →L[ℂ] V, T.comp Ti = ContinuousLinearMap.id ℂ W ∧
      Ti.comp T = ContinuousLinearMap.id ℂ V := by
  let Te := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hT.1)
    (LinearMap.range_eq_top.mpr hT.2)
  refine ⟨Te.symm.toContinuousLinearMap, ?_, ?_⟩
  · ext w; simp [Te]
  · ext v; simp [Te]

open ContinuousLinearMap in
/-- The facts about `R = √(T*T)` and `S = R⁻¹` used below. -/
lemma sqrt_inv_facts (T : V →L[ℂ] W) (hT : Function.Bijective T) :
    (CFC.sqrt (gram T)) * (CFC.sqrt (gram T)) = gram T ∧
      IsSelfAdjoint (Ring.inverse (CFC.sqrt (gram T))) ∧
      (CFC.sqrt (gram T)) * Ring.inverse (CFC.sqrt (gram T)) = 1 ∧
      Ring.inverse (CFC.sqrt (gram T)) * (CFC.sqrt (gram T)) = 1 ∧
      ∃ Ti : W →L[ℂ] V, T.comp Ti = ContinuousLinearMap.id ℂ W ∧
        Ti.comp T = ContinuousLinearMap.id ℂ V ∧
        Ring.inverse (CFC.sqrt (gram T)) * Ring.inverse (CFC.sqrt (gram T)) =
          Ti.comp (adjoint Ti) := by
  obtain ⟨Ti, hTT, hTT'⟩ := exists_inv T hT
  set R := CFC.sqrt (gram T) with hR
  have hP0 : 0 ≤ gram T := by
    rw [nonneg_iff_isPositive]; exact isPositive_adjoint_comp_self T
  have hRR : R * R = gram T := CFC.sqrt_mul_sqrt_self _ hP0
  have hRsa : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have hTTa : ∀ w, T (Ti w) = w := fun w => by simpa using congrArg (fun f => f w) hTT
  have hA : (adjoint T).comp (adjoint Ti) = ContinuousLinearMap.id ℂ V := by
    rw [← adjoint_comp, hTT', adjoint_id]
  have hPPi : gram T * Ti.comp (adjoint Ti) = 1 := by
    ext v
    have := congrArg (fun f => f v) hA
    simpa [gram, ContinuousLinearMap.mul_def, hTTa] using this
  have hPiP : Ti.comp (adjoint Ti) * gram T = 1 := by
    have hA' : (adjoint Ti).comp (adjoint T) = ContinuousLinearMap.id ℂ W := by
      rw [← adjoint_comp, hTT, adjoint_id]
    ext v
    have := congrArg (fun f => f (T v)) hA'
    simp only [ContinuousLinearMap.mul_def, gram, ContinuousLinearMap.comp_apply] at this ⊢
    have h2 := hTT'
    simp only [ContinuousLinearMap.id_apply] at this
    have h3 : Ti (T v) = v := by simpa using congrArg (fun f => f v) h2
    simp [this, h3]
  have hPunit : IsUnit (gram T) := ⟨⟨gram T, Ti.comp (adjoint Ti), hPPi, hPiP⟩, rfl⟩
  have hRunit : IsUnit R := ((Commute.refl R).isUnit_mul_iff.mp (hRR ▸ hPunit)).1
  have hRS : R * Ring.inverse R = 1 := Ring.mul_inverse_cancel R hRunit
  have hSR : Ring.inverse R * R = 1 := Ring.inverse_mul_cancel R hRunit
  have hSsa : IsSelfAdjoint (Ring.inverse R) := by
    have h1 : star (Ring.inverse R) * R = 1 := by
      have := congrArg star hRS
      rw [star_mul, star_one, hRsa.star_eq] at this
      exact this
    have h2 : star (Ring.inverse R) = Ring.inverse R := by
      calc star (Ring.inverse R) = star (Ring.inverse R) * (R * Ring.inverse R) := by rw [hRS, mul_one]
        _ = (star (Ring.inverse R) * R) * Ring.inverse R := by rw [mul_assoc]
        _ = Ring.inverse R := by rw [h1, one_mul]
    exact h2
  refine ⟨hRR, hSsa, hRS, hSR, Ti, hTT, hTT', ?_⟩
  calc Ring.inverse R * Ring.inverse R
      = (Ring.inverse R * Ring.inverse R) * (gram T * Ti.comp (adjoint Ti)) := by rw [hPPi, mul_one]
    _ = Ti.comp (adjoint Ti) := by
      rw [← hRR]
      calc (Ring.inverse R * Ring.inverse R) * ((R * R) * Ti.comp (adjoint Ti))
          = (Ring.inverse R * (Ring.inverse R * R) * R) * Ti.comp (adjoint Ti) := by
            simp only [mul_assoc]
        _ = Ti.comp (adjoint Ti) := by rw [hSR, mul_one, hSR, one_mul]

open ContinuousLinearMap in
/-- **`lem:polarintertwiner`**, second claim: `U = T (T*T)^{-1/2}` is unitary
(`U*U = 1` and `U U* = 1`). -/
theorem polarU_unitary (T : V →L[ℂ] W) (hT : Function.Bijective T) :
    (adjoint (polarU T)).comp (polarU T) = ContinuousLinearMap.id ℂ V ∧
      (polarU T).comp (adjoint (polarU T)) = ContinuousLinearMap.id ℂ W := by
  obtain ⟨hRR, hSsa, hRS, hSR, Ti, hTT, hTT', hSS⟩ := sqrt_inv_facts T hT
  set R := CFC.sqrt (gram T) with hR
  set S := Ring.inverse R with hS
  have hSa : adjoint S = S := by rw [← star_eq_adjoint]; exact hSsa.star_eq
  have hU : adjoint (polarU T) = S.comp (adjoint T) := by
    unfold polarU
    rw [adjoint_comp, hSa]
  constructor
  · rw [hU]
    show S * (gram T) * S = 1
    rw [← hRR]
    calc S * (R * R) * S = (S * R) * (R * S) := by simp only [mul_assoc]
      _ = 1 := by rw [hSR, hRS, one_mul]
  · rw [hU]
    have e : (polarU T).comp (S.comp (adjoint T)) =
        T.comp ((S * S).comp (adjoint T)) := rfl
    rw [e, hSS]
    have e2 : T.comp ((Ti.comp (adjoint Ti)).comp (adjoint T)) =
        (T.comp Ti).comp ((adjoint Ti).comp (adjoint T)) := rfl
    rw [e2, ← adjoint_comp, hTT, adjoint_id]
    rfl

open ContinuousLinearMap in
/-- **`lem:polarintertwiner`**, third claim: `U` still intertwines, `H₁ U = U H₀`. -/
theorem polarU_intertwines (H0 : V →L[ℂ] V) (H1 : W →L[ℂ] W) (hH0 : IsSelfAdjoint H0)
    (hH1 : IsSelfAdjoint H1) (T : V →L[ℂ] W) (hT : Function.Bijective T)
    (hint : H1.comp T = T.comp H0) :
    H1.comp (polarU T) = (polarU T).comp H0 := by
  obtain ⟨hRR, hSsa, hRS, hSR, Ti, hTT, hTT', hSS⟩ := sqrt_inv_facts T hT
  have hc : Commute (gram T) H0 := gram_commute H0 H1 hH0 hH1 T hint
  set R := CFC.sqrt (gram T) with hR
  set S := Ring.inverse R with hS
  have hRc : Commute R H0 := by
    rw [hR, CFC.sqrt_eq_cfc]; exact Commute.cfc_nnreal hc _
  have hSc : Commute S H0 := by
    show S * H0 = H0 * S
    calc S * H0 = S * H0 * (R * S) := by rw [hRS, mul_one]
      _ = S * (H0 * R) * S := by simp only [mul_assoc]
      _ = S * (R * H0) * S := by rw [hRc.eq]
      _ = (S * R) * H0 * S := by simp only [mul_assoc]
      _ = H0 * S := by rw [hSR, one_mul]
  have hSc' : S.comp H0 = H0.comp S := hSc.eq
  unfold polarU
  calc H1.comp (T.comp S) = (H1.comp T).comp S := rfl
    _ = (T.comp H0).comp S := by rw [hint]
    _ = T.comp (H0.comp S) := rfl
    _ = T.comp (S.comp H0) := by rw [hSc']
    _ = (T.comp S).comp H0 := rfl

/-- info: 'FormalResearch.Racah.polarU_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarU_unitary

/-- info: 'FormalResearch.Racah.polarU_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarU_intertwines

/-- info: 'FormalResearch.Racah.gram_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gram_commute

end FormalResearch.Racah

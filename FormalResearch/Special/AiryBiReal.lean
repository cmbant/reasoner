module

public import FormalResearch.Special.AiryValues
public import FormalResearch.Special.AiryAsymNeg

/-!
# `Bi'` on the real axis

`airyBiDeriv x = Re Bi'(x)` is the derivative of `airyBi`; `Bi'' = x Bi`; `Bi` and `Bi'` are real on `ℝ`;
the real Wronskian `Ai Bi' - Ai' Bi = 1/π`.  (`airyBiDeriv` is named so as not to clash with other branches;
it is the function `Bi'` of DLMF 9.2.)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `Bi'(x)` for real `x` (the real part of `airyBiC' x`; it is real, `airyBiC'_ofReal`). -/
noncomputable def airyBiDeriv (x : ℝ) : ℝ := (airyBiC' x).re

lemma deriv_airyBiC (z : ℂ) : deriv airyBiC z = airyBiC' z := (isAirySol_airyBiC z).1.deriv

lemma conj_airyBiC' (z : ℂ) : (starRingEnd ℂ) (airyBiC' z) = airyBiC' ((starRingEnd ℂ) z) := by
  have e1 : (starRingEnd ℂ) (airyOmega * z) = airyOmega ^ 2 * (starRingEnd ℂ) z := by
    rw [map_mul, conj_airyOmega]
  have e2 : (starRingEnd ℂ) (airyOmega ^ 2 * z) = airyOmega * (starRingEnd ℂ) z := by
    rw [map_mul, conj_airyOmega_sq]
  unfold airyBiC'
  rw [map_add, map_mul, map_mul, map_mul, map_mul, conj_deriv_airyAiC, conj_deriv_airyAiC, e1, e2,
    conj_airyOmega, map_pow, conj_airyOmega, Complex.conj_conj]
  have h3 : airyOmega ^ 2 * airyOmega ^ 2 = airyOmega := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]
  rw [sq (airyOmega ^ 2), h3]
  ring


theorem airyBiC'_im_ofReal (x : ℝ) : (airyBiC' (x : ℂ)).im = 0 := by
  have h := conj_airyBiC' (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem airyBiC'_ofReal (x : ℝ) : airyBiC' (x : ℂ) = (airyBiDeriv x : ℂ) :=
  Complex.ext (by simp [airyBiDeriv]) (by simpa using airyBiC'_im_ofReal x)

theorem hasDerivAt_airyBi (x : ℝ) : HasDerivAt airyBi (airyBiDeriv x) x := by
  have h : HasDerivAt (fun y : ℝ => airyBiC (y : ℂ)) (airyBiC' (x : ℂ)) x := by
    have := ((isAirySol_airyBiC (x : ℂ)).1).comp_ofReal
    exact this
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  convert this using 1
  · rfl
  · rfl

/-- `(Bi')' = x Bi`. -/
theorem hasDerivAt_airyBiDeriv (x : ℝ) : HasDerivAt airyBiDeriv (x * airyBi x) x := by
  have h : HasDerivAt (fun y : ℝ => airyBiC' (y : ℂ)) ((x : ℂ) * airyBiC (x : ℂ)) x :=
    ((isAirySol_airyBiC (x : ℂ)).2).comp_ofReal
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have e : (fun y : ℝ => (airyBiC' (y : ℂ)).re) = airyBiDeriv := rfl
  simpa [Function.comp_def, e, airyBiC_ofReal] using this

theorem differentiable_airyBi : Differentiable ℝ airyBi := fun x => (hasDerivAt_airyBi x).differentiableAt

/-- **Real Wronskian**: `Ai Bi' - Ai' Bi = 1/π`. -/
theorem airyWronskian_real (x : ℝ) : airyAi x * airyBiDeriv x - airyAi' x * airyBi x = 1 / π := by
  have h := airyAiC_wronskian_airyBiC_eq (x : ℂ)
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal, airyBiC_ofReal, airyBiC'_ofReal] at h
  exact_mod_cast h

end FormalResearch.Special

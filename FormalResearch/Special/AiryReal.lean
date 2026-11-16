module

public import FormalResearch.Special.AiryDef

/-!
# The Airy function on `ℝ`

Corollaries of `AiryDef` for the real variable.

* `conj_airyMom`: `conj M_k(c, z) = M_k(c, conj z)` (the substitution `s ↦ -s`); hence
  `conj Ai(z) = Ai(conj z)` (`conj_airyAiC`) and `Ai(x)`, `Ai'(x)` are real for real `x`.
* `airyAi : ℝ → ℝ` is the real Airy function, `airyAi x = Re Ai(x)` with `Ai(x) = airyAi x` as a
  complex number (`airyAiC_ofReal`); `airyAi'` its derivative, and the equation `y'' = x y`
  (`hasDerivAt_airyAi`, `hasDerivAt_airyAi'`), smoothness (`contDiff_airyAi`).
* `airyAi_eq_re_airyMom`: `Ai(x) = Re (1/2π) ∫ exp((c+is)³/3 - x(c+is)) ds` for every `c > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma conj_airyLine (c s : ℝ) : (starRingEnd ℂ) (airyLine c s) = airyLine c (-s) := by
  simp [airyLine]

lemma conj_airyPoly (k : ℕ) (c : ℝ) (z : ℂ) (s : ℝ) :
    (starRingEnd ℂ) (airyPoly k c z s) = airyPoly k c ((starRingEnd ℂ) z) (-s) := by
  unfold airyPoly airyKernel
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := map_ofNat _ 3
  rw [map_mul, map_pow, map_neg, conj_airyLine, ← Complex.exp_conj]
  simp [conj_airyLine, h3]

/-- Schwarz reflection for the moments: `conj M_k(c, z) = M_k(c, conj z)`. -/
theorem conj_airyMom (k : ℕ) (c : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (airyMom k c z) = airyMom k c ((starRingEnd ℂ) z) := by
  unfold airyMom
  rw [map_mul, ← integral_conj]
  have : ∀ s, (starRingEnd ℂ) (airyPoly k c z s) = airyPoly k c ((starRingEnd ℂ) z) (-s) :=
    conj_airyPoly k c z
  simp_rw [this]
  rw [integral_neg_eq_self (fun s => airyPoly k c ((starRingEnd ℂ) z) s) volume]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [h2]

/-- Schwarz reflection: `conj Ai(z) = Ai(conj z)`. -/
theorem conj_airyAiC (z : ℂ) : (starRingEnd ℂ) (airyAiC z) = airyAiC ((starRingEnd ℂ) z) :=
  conj_airyMom 0 1 z

lemma airyMom_im_ofReal (k : ℕ) (c x : ℝ) : (airyMom k c (x : ℂ)).im = 0 := by
  have h := conj_airyMom k c (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The real Airy function: `Ai(x) = (1/2π) ∫ exp((1+is)³/3 - x (1+is)) ds`, real for real `x`
(`airyAiC_ofReal`). -/
noncomputable def airyAi (x : ℝ) : ℝ := (airyAiC x).re

/-- The derivative `Ai'(x)`, as a real number. -/
noncomputable def airyAi' (x : ℝ) : ℝ := (deriv airyAiC x).re

theorem airyAiC_ofReal (x : ℝ) : airyAiC (x : ℂ) = (airyAi x : ℂ) :=
  (Complex.ext_iff.mpr ⟨by simp [airyAi], by simpa [airyAiC] using airyMom_im_ofReal 0 1 x⟩)

theorem deriv_airyAiC_ofReal (x : ℝ) : deriv airyAiC (x : ℂ) = (airyAi' x : ℂ) := by
  rw [deriv_airyAiC one_pos]
  exact Complex.ext_iff.mpr ⟨by simp [airyAi', deriv_airyAiC one_pos], by
    simpa using airyMom_im_ofReal 1 1 x⟩

theorem airyAi_eq_re_airyMom {c : ℝ} (hc : 0 < c) (x : ℝ) : airyAi x = (airyMom 0 c x).re := by
  simp [airyAi, airyAiC_eq_airyMom hc]

theorem airyAi'_eq_re_airyMom {c : ℝ} (hc : 0 < c) (x : ℝ) : airyAi' x = (airyMom 1 c x).re := by
  simp [airyAi', deriv_airyAiC hc]

theorem hasDerivAt_airyAi (x : ℝ) : HasDerivAt airyAi (airyAi' x) x := by
  have h : HasDerivAt (fun y : ℝ => airyAiC (y : ℂ)) (deriv airyAiC (x : ℂ)) x :=
    (differentiable_airyAiC.differentiableAt.hasDerivAt).comp_ofReal
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  convert this using 1
  · rfl
  · rfl

/-- The real Airy equation, first-order form: `(Ai')' = x Ai`. -/
theorem hasDerivAt_airyAi' (x : ℝ) : HasDerivAt airyAi' (x * airyAi x) x := by
  have h : HasDerivAt (fun y : ℝ => deriv airyAiC (y : ℂ)) ((x : ℂ) * airyAiC x) x :=
    (hasDerivAt_deriv_airyAiC (x : ℂ)).comp_ofReal
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have e : (fun y : ℝ => (deriv airyAiC (y : ℂ)).re) = airyAi' := rfl
  simpa [Function.comp_def, e, airyAiC_ofReal] using this

theorem deriv_airyAi (x : ℝ) : deriv airyAi x = airyAi' x := (hasDerivAt_airyAi x).deriv

/-- **The Airy equation** on `ℝ`: `Ai'' = x Ai`. -/
theorem iteratedDeriv_two_airyAi (x : ℝ) : iteratedDeriv 2 airyAi x = x * airyAi x := by
  have : deriv airyAi = airyAi' := funext deriv_airyAi
  rw [iteratedDeriv_succ, iteratedDeriv_one, this]
  exact (hasDerivAt_airyAi' x).deriv

theorem differentiable_airyAi : Differentiable ℝ airyAi := fun x =>
  (hasDerivAt_airyAi x).differentiableAt

/-- `Ai` is smooth on `ℝ`. -/
theorem contDiff_airyAi : ContDiff ℝ ⊤ airyAi := by
  have h : ContDiff ℂ ⊤ airyAiC := differentiable_airyAiC.contDiff
  have h2 : ContDiff ℝ ⊤ (fun x : ℝ => airyAiC (x : ℂ)) :=
    (h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  exact (Complex.reCLM.contDiff.comp h2 : ContDiff ℝ ⊤ fun x : ℝ => (airyAiC (x : ℂ)).re)

end FormalResearch.Special

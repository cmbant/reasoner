module

public import FormalResearch.PPTThreeQubit.Criterion

/-!
# The rank-five family `ρ_t`: genuine multipartite entanglement

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`,
`thm:ppt3-family` (GME part), with `eq:ppt3-rho`, `eq:ppt3-h5-value`, `eq:ppt3-interval` and the
explicit member at `t = 10/3`.

`ρ_t = (t uu† + 3t vv† + 3 ww† + 3 ee† + oo†) / (7 (t + 3)) = B X_t B†` with
`X_t = diag(t, 3t, 3, 3, 1) / (7 (t + 3))`.

Covered: the GME part of `thm:ppt3-family`, namely `tr(H_5 X_t) = (29 - 9t)/(7(t+3))` and
`ρ_t` is not biseparable for every real `t > 29/9`, in particular for `t ≥ t_-` (the lower end
of the PPT interval) and `t = 10/3`.
Not covered here: the PPT interval `[t_-, t_+]`, the rank profile, and minimality of rank five
(these are the Sylvester-minor and low-rank-PPT parts of the theorem).
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- The coefficient matrix `X_t = diag(t, 3t, 3, 3, 1) / (7 (t + 3))` of `ρ_t` in the basis
`(u, v, w, e, o)`. -/
def Xt (t : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun a => ((![t, 3 * t, 3, 3, 1] a / (7 * (t + 3)) : ℝ) : ℂ)

/-- The state `ρ_t = B X_t B†` of `eq:ppt3-rho` (with `B = B_1`). -/
def rhoT (t : ℝ) : Matrix (Fin 8) (Fin 8) ℂ := Bs 1 * Xt t * (Bs 1)ᴴ

/-- `eq:ppt3-rho`: `ρ_t = (t uu† + 3t vv† + 3 ww† + 3 ee† + oo†) / (7 (t + 3))`. -/
theorem rhoT_eq (t : ℝ) :
    rhoT t = ((1 / (7 * (t + 3)) : ℝ) : ℂ) •
      ((t : ℂ) • vecMulVec (uVec 1) (star (uVec 1)) + (3 * t : ℂ) • vecMulVec vVec (star vVec)
        + (3 : ℂ) • vecMulVec wVec (star wVec) + (3 : ℂ) • vecMulVec eVec (star eVec)
        + vecMulVec oVec (star oVec)) := by
  ext i j
  simp only [rhoT, Xt, Bs, bCols, mul_apply, Fin.sum_univ_five, diagonal_apply,
    conjTranspose_apply, of_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    smul_eq_mul]
  simp
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- `eq:ppt3-h5-value`: `tr(H_5 X_t) = (29 - 9t)/(7(t+3))`. -/
theorem trace_H5_Xt (t : ℝ) (ht : 0 < t) :
    (Hs 1 * Xt t).trace = (((29 - 9 * t) / (7 * (t + 3)) : ℝ) : ℂ) := by
  have h : (7 * (t + 3) : ℝ) ≠ 0 := by positivity
  simp [Hs, Xt, trace, diag, Fin.sum_univ_five, hDiag]
  field_simp
  ring

/-- **`thm:ppt3-family`, GME part.**  For every real `t > 29/9`, the state `ρ_t` is genuinely
multipartite entangled, i.e. not a finite sum of rank-one operators each a product across one of
the three single-qubit cuts.  The proof is the supported-witness criterion with
`tr(H_5 X_t) = (29 - 9t)/(7(t+3)) < 0` (`eq:ppt3-h5-value`). -/
theorem ppt3_family_gme (t : ℝ) (ht : 29 / 9 < t) : IsGME (rhoT t) := by
  intro hb
  have ht0 : 0 < t := by linarith
  have h := trace_Hs_nonneg_of_biseparable (s := 1) one_pos (Xt t) hb
  rw [trace_H5_Xt t ht0, Complex.ofReal_re] at h
  have h7 : 0 < 7 * (t + 3) := by positivity
  have : (29 - 9 * t) / (7 * (t + 3)) < 0 := div_neg_of_neg_of_pos (by linarith) h7
  linarith

/-- The lower endpoint `t_- = (15 + 9√17)/16` of the PPT interval `eq:ppt3-interval`. -/
def tMinus : ℝ := (15 + 9 * Real.sqrt 17) / 16

/-- `t_- > 29/9`, the numerical input of the proof of GME in `thm:ppt3-family`. -/
theorem tMinus_gt : 29 / 9 < tMinus := by
  have h : (329 / 81 : ℝ) < Real.sqrt 17 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold tMinus; linarith

/-- **`thm:ppt3-family`, GME on the PPT range.**  `ρ_t` is GME for every `t ≥ t_-`, in particular
throughout the PPT interval `[t_-, t_+]` (whose PPT claim is not formalised here). -/
theorem ppt3_family_gme_of_tMinus_le (t : ℝ) (ht : tMinus ≤ t) : IsGME (rhoT t) :=
  ppt3_family_gme t (lt_of_lt_of_le tMinus_gt ht)

/-- The explicit member `t = 10/3`: `tr(H_5 X_{10/3}) = -3/133` and `ρ_{10/3}` is GME. -/
theorem ppt3_family_explicit_member :
    (Hs 1 * Xt (10 / 3)).trace = (((-3 / 133 : ℝ)) : ℂ) ∧ IsGME (rhoT (10 / 3)) := by
  refine ⟨?_, ppt3_family_gme _ (by norm_num)⟩
  rw [trace_H5_Xt _ (by norm_num)]
  norm_num

end

/-- info: 'FormalResearch.PPTThreeQubit.trace_H5_Xt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_H5_Xt

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_gme

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_gme_of_tMinus_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_gme_of_tMinus_le

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_explicit_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_explicit_member

end FormalResearch.PPTThreeQubit

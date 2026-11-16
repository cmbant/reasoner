module

public import FormalResearch.Special.AiryZeros

/-!
# Rotations of `Ai`, and `Bi`

Let `ω = e^{2πi/3} = -1/2 + (√3/2) i` (`airyOmega`) and `ε = e^{iπ/6} = √3/2 + i/2` (`airyEps`); these are
written in algebraic form, so that every algebraic fact is a `Complex.ext` computation.

* `isAirySol_airyAiC_rot`: for `a³ = 1`, `z ↦ Ai(a z)` (with derivative `a Ai'(a z)`) is again a solution
  of `y'' = z y` on `ℂ`.
* `airyAiC_rotation`: `Ai(z) + ω Ai(ω z) + ω² Ai(ω² z) = 0` for all `z ∈ ℂ`.  Proof: the left side is a
  solution (sum of rotated solutions) with `u(0) = Ai(0)(1 + ω + ω²) = 0`, `u'(0) = Ai'(0)(1 + ω² + ω) = 0`,
  so it vanishes on `ℝ` by ODE uniqueness (`airy_unique_real`) and hence identically (entire).
* `airyBiC z = ε Ai(ω z) + ε̄ Ai(ω² z)` (`ε̄ = e^{-iπ/6}`), i.e. `e^{iπ/6} Ai(z e^{2πi/3}) +
  e^{-iπ/6} Ai(z e^{-2πi/3})`: entire (`differentiable_airyBiC`), `Bi'' = z Bi`
  (`isAirySol_airyBiC`), real on `ℝ` (`airyBiC_ofReal`), and the Wronskian
  `Ai Bi' - Ai' Bi = -2√3 Ai(0) Ai'(0) > 0` is constant (`airyAiC_wronskian_airyBiC`).

The value `-2√3 Ai(0) Ai'(0) = 1/π` (so `W(Ai, Bi) = 1/π`), `Ai(0) = 3^{-2/3}/Γ(2/3)` and `Ai'(0)` are in
`AiryValues`.  Not formalised here: the growth of `Bi` and the asymptotics of `Ai` in sectors.
-/

@[expose] public section

open Filter Topology MeasureTheory Set Complex
open scoped Real

namespace FormalResearch.Special

/-- `ω = e^{2πi/3}`. -/
noncomputable def airyOmega : ℂ := ⟨-1 / 2, √3 / 2⟩

/-- `ε = e^{iπ/6}`. -/
noncomputable def airyEps : ℂ := ⟨√3 / 2, 1 / 2⟩

private lemma sqrt3_mul : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)

private lemma sqrt3_cube : √(3 : ℝ) * √3 * √3 = 3 * √3 := by rw [sqrt3_mul]

lemma airyOmega_eq_exp : airyOmega = Complex.exp (2 * π * I / 3) := by
  have h : (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hs : Real.sin (2 * π / 3) = √3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hc, hs]
  apply Complex.ext <;> simp [airyOmega]

lemma airyEps_eq_exp : airyEps = Complex.exp (π * I / 6) := by
  have h : (π * I / 6 : ℂ) = ((π / 6 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six]
  apply Complex.ext <;> simp [airyEps]

lemma airyOmega_cube : airyOmega ^ 3 = 1 := by
  apply Complex.ext <;> simp [airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul, sqrt3_cube]

lemma airyOmega_sq_add : 1 + airyOmega + airyOmega ^ 2 = 0 := by
  apply Complex.ext <;> simp [airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul, sqrt3_cube]

lemma conj_airyOmega : (starRingEnd ℂ) airyOmega = airyOmega ^ 2 := by
  apply Complex.ext <;> simp [airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul, sqrt3_cube]

lemma conj_airyOmega_sq : (starRingEnd ℂ) (airyOmega ^ 2) = airyOmega := by
  rw [map_pow, conj_airyOmega, ← pow_mul]
  have : airyOmega ^ 4 = airyOmega := by
    rw [show 4 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]
  simpa using this

lemma airyEps_add_conj : airyEps + (starRingEnd ℂ) airyEps = (√3 : ℝ) := by
  apply Complex.ext <;> simp [airyEps]

lemma airyEps_mul_omega_add :
    airyEps * airyOmega + (starRingEnd ℂ) airyEps * airyOmega ^ 2 = -(√3 : ℝ) := by
  apply Complex.ext <;> simp [airyEps, airyOmega, pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt3_mul, sqrt3_cube]

/-- Rotated solutions. -/
lemma isAirySol_airyAiC_rot {a : ℂ} (ha : a ^ 3 = 1) :
    IsAirySol (fun z : ℂ => airyAiC (a * z)) (fun z => a * deriv airyAiC (a * z)) := by
  intro z
  have h1 : HasDerivAt (fun z : ℂ => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  refine ⟨?_, ?_⟩
  · have := (differentiable_airyAiC.differentiableAt.hasDerivAt (x := a * z)).comp z h1
    refine this.congr_deriv ?_
    ring
  · have h2 := (hasDerivAt_deriv_airyAiC (a * z)).comp z h1
    have := h2.const_mul a
    refine this.congr_deriv ?_
    have : a * (a * z * airyAiC (a * z) * a) = a ^ 3 * (z * airyAiC (a * z)) := by ring
    rw [this, ha, one_mul]

lemma IsAirySol.const_mul' {y y' : ℂ → ℂ} (h : IsAirySol y y') (c : ℂ) :
    IsAirySol (fun z => c * y z) (fun z => c * y' z) := fun z =>
  ⟨((h z).1).const_mul c, by simpa [mul_left_comm] using ((h z).2).const_mul c⟩

lemma IsAirySol.add' {y y' w w' : ℂ → ℂ} (h : IsAirySol y y') (h2 : IsAirySol w w') :
    IsAirySol (fun z => y z + w z) (fun z => y' z + w' z) := fun z =>
  ⟨((h z).1).add ((h2 z).1), by
    have := ((h z).2).add ((h2 z).2)
    convert this using 1
    ring⟩


/-- The three-fold sum `u = Ai + ω Ai(ω ·) + ω² Ai(ω² ·)`, with derivative `u'`. -/
private noncomputable def rotSum (z : ℂ) : ℂ :=
  airyAiC z + airyOmega * airyAiC (airyOmega * z) + airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z)

private noncomputable def rotSum' (z : ℂ) : ℂ :=
  deriv airyAiC z + airyOmega * (airyOmega * deriv airyAiC (airyOmega * z)) +
    airyOmega ^ 2 * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z))

private lemma isAirySol_rotSum : IsAirySol rotSum rotSum' := by
  have h0 : IsAirySol airyAiC (deriv airyAiC) := isAirySol_airyAiC
  have h1 : IsAirySol (fun z => airyAiC (airyOmega * z))
      (fun z => airyOmega * deriv airyAiC (airyOmega * z)) :=
    isAirySol_airyAiC_rot airyOmega_cube
  have h2 : IsAirySol (fun z => airyAiC (airyOmega ^ 2 * z))
      (fun z => airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z)) :=
    isAirySol_airyAiC_rot (a := airyOmega ^ 2) (by
      rw [← pow_mul, mul_comm, pow_mul, airyOmega_cube, one_pow])
  exact (h0.add' (h1.const_mul' airyOmega)).add' (h2.const_mul' (airyOmega ^ 2))

/-- **Three-fold rotation identity**: `Ai(z) + ω Ai(ω z) + ω² Ai(ω² z) = 0`, `ω = e^{2πi/3}`. -/
theorem airyAiC_rotation (z : ℂ) :
    airyAiC z + airyOmega * airyAiC (airyOmega * z) +
      airyOmega ^ 2 * airyAiC (airyOmega ^ 2 * z) = 0 := by
  have hsol := isAirySol_rotSum
  have hω := airyOmega_sq_add
  have hω4 : airyOmega ^ 2 * airyOmega ^ 2 = airyOmega := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]
  have hu0 : rotSum 0 = 0 := by
    simp only [rotSum, mul_zero]
    linear_combination (airyAiC 0) * hω
  have hu0' : rotSum' 0 = 0 := by
    simp only [rotSum', mul_zero]
    rw [← mul_assoc, ← mul_assoc, hω4]
    linear_combination (deriv airyAiC 0) * hω
  have hreal := airy_unique_real (fun x : ℝ => rotSum (x : ℂ)) (fun x : ℝ => rotSum' (x : ℂ))
    (fun x => ⟨((hsol x).1).comp_ofReal, ((hsol x).2).comp_ofReal⟩)
    (by simpa using hu0) (by simpa using hu0')
  have hdiff : Differentiable ℂ rotSum := fun z => ((hsol z).1).differentiableAt
  have := entire_eq_zero_of_ray hdiff 0 (fun x _ => by simpa using hreal x) z
  exact this

/-- `Bi(z) = e^{iπ/6} Ai(z e^{2πi/3}) + e^{-iπ/6} Ai(z e^{-2πi/3})`. -/
noncomputable def airyBiC (z : ℂ) : ℂ :=
  airyEps * airyAiC (airyOmega * z) + (starRingEnd ℂ) airyEps * airyAiC (airyOmega ^ 2 * z)

/-- The derivative of `Bi`. -/
noncomputable def airyBiC' (z : ℂ) : ℂ :=
  airyEps * (airyOmega * deriv airyAiC (airyOmega * z)) +
    (starRingEnd ℂ) airyEps * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z))

/-- `Bi'' = z Bi` on `ℂ`. -/
theorem isAirySol_airyBiC : IsAirySol airyBiC airyBiC' := by
  have h1 : IsAirySol (fun z => airyAiC (airyOmega * z))
      (fun z => airyOmega * deriv airyAiC (airyOmega * z)) :=
    isAirySol_airyAiC_rot airyOmega_cube
  have h2 : IsAirySol (fun z => airyAiC (airyOmega ^ 2 * z))
      (fun z => airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z)) :=
    isAirySol_airyAiC_rot (a := airyOmega ^ 2) (by
      rw [← pow_mul, mul_comm, pow_mul, airyOmega_cube, one_pow])
  exact (h1.const_mul' airyEps).add' (h2.const_mul' ((starRingEnd ℂ) airyEps))

theorem differentiable_airyBiC : Differentiable ℂ airyBiC := fun z =>
  ((isAirySol_airyBiC z).1).differentiableAt

/-- Schwarz reflection for `Bi`: `conj Bi(z) = Bi(conj z)`. -/
theorem conj_airyBiC (z : ℂ) : (starRingEnd ℂ) (airyBiC z) = airyBiC ((starRingEnd ℂ) z) := by
  have e1 : (starRingEnd ℂ) (airyOmega * z) = airyOmega ^ 2 * (starRingEnd ℂ) z := by
    rw [map_mul, conj_airyOmega]
  have e2 : (starRingEnd ℂ) (airyOmega ^ 2 * z) = airyOmega * (starRingEnd ℂ) z := by
    rw [map_mul, conj_airyOmega_sq]
  unfold airyBiC
  rw [map_add, map_mul, map_mul, conj_airyAiC, conj_airyAiC, e1, e2, Complex.conj_conj]
  ring

/-- `Bi` is real on `ℝ`. -/
theorem airyBiC_im_ofReal (x : ℝ) : (airyBiC (x : ℂ)).im = 0 := by
  have h := conj_airyBiC (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The real Bi function, `Bi(x) = Re (e^{iπ/6} Ai(x e^{2πi/3}) + e^{-iπ/6} Ai(x e^{-2πi/3}))`. -/
noncomputable def airyBi (x : ℝ) : ℝ := (airyBiC x).re

theorem airyBiC_ofReal (x : ℝ) : airyBiC (x : ℂ) = (airyBi x : ℂ) :=
  Complex.ext (by simp [airyBi]) (by simpa using airyBiC_im_ofReal x)

/-- At `0`: `Bi(0) = √3 Ai(0)` and `Bi'(0) = -√3 Ai'(0)`. -/
lemma airyBiC_zero : airyBiC 0 = (√3 : ℝ) * airyAiC 0 := by
  unfold airyBiC
  simp only [mul_zero]
  rw [← add_mul, airyEps_add_conj]

lemma airyBiC'_zero : airyBiC' 0 = -(√3 : ℝ) * deriv airyAiC 0 := by
  unfold airyBiC'
  simp only [mul_zero]
  rw [← mul_assoc, ← mul_assoc, ← add_mul, airyEps_mul_omega_add]

/-- **Wronskian of `Ai` and `Bi`**: constant on `ℂ`, equal to `-2√3 Ai(0) Ai'(0)`, a positive number. -/
theorem airyAiC_wronskian_airyBiC (z : ℂ) :
    airyAiC z * airyBiC' z - deriv airyAiC z * airyBiC z =
      ((-2 * √3 * airyAi 0 * airyAi' 0 : ℝ) : ℂ) := by
  have := isAirySol_airyAiC.wronskian_const isAirySol_airyBiC z
  have e1 : airyAiC 0 = (airyAi 0 : ℂ) := by simpa using airyAiC_ofReal 0
  have e2 : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by simpa using deriv_airyAiC_ofReal 0
  rw [this, airyBiC_zero, airyBiC'_zero, e1, e2]
  push_cast
  ring

theorem airyWronskian_pos : 0 < -2 * √3 * airyAi 0 * airyAi' 0 := by
  have h1 := airyAi_pos (le_refl (0 : ℝ))
  have h2 := airyAi'_neg (le_refl (0 : ℝ))
  have h3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [mul_pos h3 h1]

/-- info: 'FormalResearch.Special.airyAiC_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_rotation

/-- info: 'FormalResearch.Special.isAirySol_airyBiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.isAirySol_airyBiC

/-- info: 'FormalResearch.Special.conj_airyBiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.conj_airyBiC

/-- info: 'FormalResearch.Special.airyBiC_im_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiC_im_ofReal

/-- info: 'FormalResearch.Special.airyBiC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiC_ofReal

/-- info: 'FormalResearch.Special.airyAiC_wronskian_airyBiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_wronskian_airyBiC

/-- info: 'FormalResearch.Special.airyWronskian_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyWronskian_pos

end FormalResearch.Special

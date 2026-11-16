module

public import FormalResearch.Special.AiryValues

/-!
# The Taylor series of the Airy function

`Ai` is entire, so it equals its Taylor series at `0` (Mathlib: `Complex.hasSum_taylorSeries_of_entire`).
The derivative recurrence `Ai^{(k+3)}(0) = (k+1) Ai^{(k)}(0)` of `AiryDef` and `Ai''(0) = 0` give
`Ai^{(3j)}(0) = A_j Ai(0)`, `Ai^{(3j+1)}(0) = B_j Ai'(0)`, `Ai^{(3j+2)}(0) = 0` with
`A_j = ∏_{i<j}(3i+1)`, `B_j = ∏_{i<j}(3i+2)` (`airyCoefA`, `airyCoefB`).  Splitting the Taylor series into
residue classes of the exponent mod 3 (`Nat.sumByResidueClasses`) gives, for every `z ∈ ℂ`,

* `airyAiC_eq_taylor`: `Ai(z) = Ai(0) F(z) + Ai'(0) G(z)`, where
  `F(z) = Σ_j A_j z^{3j}/(3j)!` and `G(z) = Σ_j B_j z^{3j+1}/(3j+1)!` (`airyTaylorF`, `airyTaylorG`;
  classically `0F1(; 2/3; z³/9)` and `z · 0F1(; 4/3; z³/9)`, identified in `AiryHypergeometric`);
* `hasSum_airyTaylorF`, `hasSum_airyTaylorG`: both series converge for every `z` (they are the
  residue-class subseries of the absolutely convergent Taylor series of `Ai`, whose first two
  coefficients `Ai(0), Ai'(0)` are nonzero), so `F, G` are entire;
* `airyTaylorF_eq`, `airyTaylorG_eq`: `3 Ai(0) F(z) = Σ_{ζ³=1} Ai(ζz)`, `3 Ai'(0) G(z) = Σ_{ζ³=1} ζ^{-1} Ai(ζz)`
  (the projections onto the exponent classes `0` and `1` mod 3), hence
* `isAirySol_airyTaylorF`, `isAirySol_airyTaylorG`: `F'' = zF`, `G'' = zG` on `ℂ`, with
  `F(0) = 1, F'(0) = 0, G(0) = 0, G'(0) = 1` (`airyTaylorF_zero`, ...), and
* `airyAiC_eq_explicit`: with the exact values of `AiryValues`,
  `Ai(z) = 3^{-2/3}/Γ(2/3) · F(z) - 3^{-1/3}/Γ(1/3) · G(z)`.

The decomposition is proved from the Taylor expansion, not by ODE uniqueness; the ODE and initial
data for `F, G` are consequences (and, with `airy_eq_of_initial`, characterise them).
-/

@[expose] public section

open Complex Filter Topology
open scoped Real Nat

namespace FormalResearch.Special

/-- `A_j = ∏_{i<j} (3i+1) = 3^j (1/3)_j`: `Ai^{(3j)}(0) = A_j Ai(0)`. -/
noncomputable def airyCoefA (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (3 * (i : ℝ) + 1)

/-- `B_j = ∏_{i<j} (3i+2) = 3^j (2/3)_j`: `Ai^{(3j+1)}(0) = B_j Ai'(0)`. -/
noncomputable def airyCoefB (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (3 * (i : ℝ) + 2)

lemma iteratedDeriv_airyAiC_zero_mod0 (j : ℕ) :
    iteratedDeriv (3 * j) airyAiC 0 = (airyCoefA j : ℂ) * airyAiC 0 := by
  induction j with
  | zero => simp [airyCoefA]
  | succ j ih =>
    rw [show 3 * (j + 1) = 3 * j + 3 by ring, iteratedDeriv_airyAiC_zero_succ_succ_succ, ih]
    simp only [airyCoefA, Finset.prod_range_succ] at *
    push_cast; ring

lemma iteratedDeriv_airyAiC_zero_mod1 (j : ℕ) :
    iteratedDeriv (3 * j + 1) airyAiC 0 = (airyCoefB j : ℂ) * deriv airyAiC 0 := by
  induction j with
  | zero => simp [airyCoefB, iteratedDeriv_one]
  | succ j ih =>
    rw [show 3 * (j + 1) + 1 = (3 * j + 1) + 3 by ring,
      iteratedDeriv_airyAiC_zero_succ_succ_succ, ih]
    simp only [airyCoefB, Finset.prod_range_succ] at *
    push_cast; ring

lemma iteratedDeriv_airyAiC_zero_mod2 (j : ℕ) : iteratedDeriv (3 * j + 2) airyAiC 0 = 0 := by
  induction j with
  | zero => simp [iteratedDeriv_two_airyAiC]
  | succ j ih =>
    rw [show 3 * (j + 1) + 2 = (3 * j + 2) + 3 by ring,
      iteratedDeriv_airyAiC_zero_succ_succ_succ, ih, mul_zero]

/-- The entire series `F(z) = Σ_j A_j z^{3j}/(3j)!` (`= 0F1(; 2/3; z³/9)`). -/
noncomputable def airyTaylorF (z : ℂ) : ℂ :=
  ∑' j : ℕ, (airyCoefA j : ℂ) / ((3 * j) ! : ℂ) * z ^ (3 * j)

/-- The entire series `G(z) = Σ_j B_j z^{3j+1}/(3j+1)!` (`= z · 0F1(; 4/3; z³/9)`). -/
noncomputable def airyTaylorG (z : ℂ) : ℂ :=
  ∑' j : ℕ, (airyCoefB j : ℂ) / ((3 * j + 1) ! : ℂ) * z ^ (3 * j + 1)

/-- The Taylor terms of `Ai` at `0`. -/
lemma taylorTerm_mod0 (z : ℂ) (m : ℕ) :
    ((3 * m)! : ℂ)⁻¹ • z ^ (3 * m) • iteratedDeriv (3 * m) airyAiC 0 =
      airyAiC 0 * ((airyCoefA m : ℂ) / ((3 * m) ! : ℂ) * z ^ (3 * m)) := by
  rw [iteratedDeriv_airyAiC_zero_mod0]
  simp only [smul_eq_mul]
  ring

lemma taylorTerm_mod1 (z : ℂ) (m : ℕ) :
    ((3 * m + 1)! : ℂ)⁻¹ • z ^ (3 * m + 1) • iteratedDeriv (3 * m + 1) airyAiC 0 =
      deriv airyAiC 0 * ((airyCoefB m : ℂ) / ((3 * m + 1) ! : ℂ) * z ^ (3 * m + 1)) := by
  rw [iteratedDeriv_airyAiC_zero_mod1]
  simp only [smul_eq_mul]
  ring

/-- **`Ai = Ai(0) F + Ai'(0) G`** on `ℂ`, with `F, G` the explicit power series (Taylor series of
`Ai` split into residue classes of the exponent mod 3). -/
theorem airyAiC_eq_taylor (z : ℂ) :
    airyAiC z = airyAiC 0 * airyTaylorF z + deriv airyAiC 0 * airyTaylorG z := by
  have hs := Complex.hasSum_taylorSeries_of_entire differentiable_airyAiC 0 z
  rw [sub_zero] at hs
  have h := Nat.sumByResidueClasses hs.summable 3
  rw [hs.tsum_eq] at h
  rw [h]
  have e := Fin.sum_univ_three (fun j : Fin 3 => ∑' m : ℕ, ((j.val + 3 * m)! : ℂ)⁻¹ •
    z ^ (j.val + 3 * m) • iteratedDeriv (j.val + 3 * m) airyAiC 0)
  refine e.trans ?_
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add]
  have h1 : ∀ m : ℕ, 1 + 3 * m = 3 * m + 1 := fun m => add_comm _ _
  have h2 : ∀ m : ℕ, 2 + 3 * m = 3 * m + 2 := fun m => add_comm _ _
  simp_rw [h1, h2, taylorTerm_mod0, taylorTerm_mod1, iteratedDeriv_airyAiC_zero_mod2]
  simp only [smul_zero, tsum_zero, add_zero]
  rw [tsum_mul_left, tsum_mul_left]
  rfl

lemma airyAiC_zero_ne : airyAiC 0 ≠ 0 := by
  have h := airyAi_pos (le_refl (0 : ℝ))
  have e : airyAiC 0 = (airyAi 0 : ℂ) := by simpa using airyAiC_ofReal 0
  rw [e]; exact_mod_cast h.ne'

lemma deriv_airyAiC_zero_ne : deriv airyAiC 0 ≠ 0 := by
  have h := airyAi'_neg (le_refl (0 : ℝ))
  have e : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by simpa using deriv_airyAiC_ofReal 0
  rw [e]; exact_mod_cast h.ne

/-- The series for `F` converges for every `z` (so `F` is entire). -/
theorem hasSum_airyTaylorF (z : ℂ) :
    HasSum (fun j : ℕ => (airyCoefA j : ℂ) / ((3 * j) ! : ℂ) * z ^ (3 * j)) (airyTaylorF z) := by
  have hs := (Complex.hasSum_taylorSeries_of_entire differentiable_airyAiC 0 z).summable
  have hinj : Function.Injective (fun m : ℕ => 3 * m) := fun a b h => by simpa using h
  have h1 := hs.comp_injective hinj
  simp only [sub_zero, Function.comp_def, taylorTerm_mod0] at h1
  exact ((summable_mul_left_iff airyAiC_zero_ne).mp h1).hasSum

/-- The series for `G` converges for every `z`. -/
theorem hasSum_airyTaylorG (z : ℂ) :
    HasSum (fun j : ℕ => (airyCoefB j : ℂ) / ((3 * j + 1) ! : ℂ) * z ^ (3 * j + 1))
      (airyTaylorG z) := by
  have hs := (Complex.hasSum_taylorSeries_of_entire differentiable_airyAiC 0 z).summable
  have hinj : Function.Injective (fun m : ℕ => 3 * m + 1) := fun a b h => by simpa using h
  have h1 := hs.comp_injective hinj
  simp only [sub_zero, Function.comp_def, taylorTerm_mod1] at h1
  exact ((summable_mul_left_iff deriv_airyAiC_zero_ne).mp h1).hasSum

lemma airyTaylorF_rot {a : ℂ} (ha : a ^ 3 = 1) (z : ℂ) : airyTaylorF (a * z) = airyTaylorF z := by
  unfold airyTaylorF
  congr 1; ext j
  rw [mul_pow, pow_mul, ha, one_pow, one_mul]

lemma airyTaylorG_rot {a : ℂ} (ha : a ^ 3 = 1) (z : ℂ) :
    airyTaylorG (a * z) = a * airyTaylorG z := by
  unfold airyTaylorG
  rw [← tsum_mul_left]
  congr 1; ext j
  rw [mul_pow, pow_succ, pow_mul, ha, one_pow, one_mul]; ring

private lemma airyOmega_sq_cube : (airyOmega ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, airyOmega_cube, one_pow]

/-- Projection formula: `3 Ai(0) F(z) = Ai(z) + Ai(ωz) + Ai(ω²z)`. -/
theorem airyTaylorF_eq (z : ℂ) :
    3 * airyAiC 0 * airyTaylorF z =
      airyAiC z + airyAiC (airyOmega * z) + airyAiC (airyOmega ^ 2 * z) := by
  rw [airyAiC_eq_taylor z, airyAiC_eq_taylor (airyOmega * z),
    airyAiC_eq_taylor (airyOmega ^ 2 * z), airyTaylorF_rot airyOmega_cube,
    airyTaylorG_rot airyOmega_cube, airyTaylorF_rot airyOmega_sq_cube,
    airyTaylorG_rot airyOmega_sq_cube]
  have := airyOmega_sq_add
  linear_combination (-(deriv airyAiC 0 * airyTaylorG z)) * this

/-- Projection formula: `3 Ai'(0) G(z) = Ai(z) + ω² Ai(ωz) + ω Ai(ω²z)`. -/
theorem airyTaylorG_eq (z : ℂ) :
    3 * deriv airyAiC 0 * airyTaylorG z =
      airyAiC z + airyOmega ^ 2 * airyAiC (airyOmega * z) + airyOmega * airyAiC (airyOmega ^ 2 * z) := by
  rw [airyAiC_eq_taylor z, airyAiC_eq_taylor (airyOmega * z),
    airyAiC_eq_taylor (airyOmega ^ 2 * z), airyTaylorF_rot airyOmega_cube,
    airyTaylorG_rot airyOmega_cube, airyTaylorF_rot airyOmega_sq_cube,
    airyTaylorG_rot airyOmega_sq_cube]
  have h3 := airyOmega_cube
  have := airyOmega_sq_add
  linear_combination (-(airyAiC 0 * airyTaylorF z)) * this + (-2 * (deriv airyAiC 0 * airyTaylorG z)) * h3

private lemma isAirySol_rotω : IsAirySol (fun z => airyAiC (airyOmega * z))
    (fun z => airyOmega * deriv airyAiC (airyOmega * z)) :=
  isAirySol_airyAiC_rot airyOmega_cube

private lemma isAirySol_rotω2 : IsAirySol (fun z => airyAiC (airyOmega ^ 2 * z))
    (fun z => airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z)) :=
  isAirySol_airyAiC_rot airyOmega_sq_cube

/-- The derivative of `F`. -/
noncomputable def airyTaylorF' (z : ℂ) : ℂ :=
  (3 * airyAiC 0)⁻¹ * ((deriv airyAiC z + airyOmega * deriv airyAiC (airyOmega * z)) +
    airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z))

/-- The derivative of `G`. -/
noncomputable def airyTaylorG' (z : ℂ) : ℂ :=
  (3 * deriv airyAiC 0)⁻¹ * ((deriv airyAiC z + airyOmega ^ 2 * (airyOmega * deriv airyAiC (airyOmega * z))) +
    airyOmega * (airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * z)))

/-- **`F` solves the Airy equation** `F'' = z F` on `ℂ` (in particular it is entire). -/
theorem isAirySol_airyTaylorF : IsAirySol airyTaylorF airyTaylorF' := by
  have h := ((isAirySol_airyAiC.add' isAirySol_rotω).add' isAirySol_rotω2).const_mul'
    (3 * airyAiC 0)⁻¹
  have hF : airyTaylorF = fun z => (3 * airyAiC 0)⁻¹ *
      ((airyAiC z + airyAiC (airyOmega * z)) + airyAiC (airyOmega ^ 2 * z)) := by
    funext z
    have h3 : 3 * airyAiC 0 ≠ 0 := mul_ne_zero (by norm_num) airyAiC_zero_ne
    rw [← airyTaylorF_eq, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  rw [hF]
  exact h

/-- **`G` solves the Airy equation** `G'' = z G` on `ℂ`. -/
theorem isAirySol_airyTaylorG : IsAirySol airyTaylorG airyTaylorG' := by
  have h := ((isAirySol_airyAiC.add' (isAirySol_rotω.const_mul' (airyOmega ^ 2))).add'
    (isAirySol_rotω2.const_mul' airyOmega)).const_mul' (3 * deriv airyAiC 0)⁻¹
  have hG : airyTaylorG = fun z => (3 * deriv airyAiC 0)⁻¹ *
      ((airyAiC z + airyOmega ^ 2 * airyAiC (airyOmega * z)) + airyOmega * airyAiC (airyOmega ^ 2 * z)) := by
    funext z
    have h3 : 3 * deriv airyAiC 0 ≠ 0 := mul_ne_zero (by norm_num) deriv_airyAiC_zero_ne
    rw [← airyTaylorG_eq, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  rw [hG]
  exact h

theorem differentiable_airyTaylorF : Differentiable ℂ airyTaylorF := fun z =>
  ((isAirySol_airyTaylorF z).1).differentiableAt

theorem differentiable_airyTaylorG : Differentiable ℂ airyTaylorG := fun z =>
  ((isAirySol_airyTaylorG z).1).differentiableAt

theorem airyTaylorF_zero : airyTaylorF 0 = 1 := by
  have h := airyTaylorF_eq 0
  simp only [mul_zero] at h
  have h3 : 3 * airyAiC 0 ≠ 0 := mul_ne_zero (by norm_num) airyAiC_zero_ne
  apply mul_left_cancel₀ h3
  rw [h]; ring

theorem airyTaylorG_zero : airyTaylorG 0 = 0 := by
  have h := airyTaylorG_eq 0
  simp only [mul_zero] at h
  have hω := airyOmega_sq_add
  have h3 : 3 * deriv airyAiC 0 ≠ 0 := mul_ne_zero (by norm_num) deriv_airyAiC_zero_ne
  apply mul_left_cancel₀ h3
  rw [h, mul_zero]
  linear_combination (airyAiC 0) * hω

theorem airyTaylorF'_zero : airyTaylorF' 0 = 0 := by
  unfold airyTaylorF'
  simp only [mul_zero]
  have hω := airyOmega_sq_add
  rw [show ((deriv airyAiC 0 + airyOmega * deriv airyAiC 0) + airyOmega ^ 2 * deriv airyAiC 0) =
    deriv airyAiC 0 * (1 + airyOmega + airyOmega ^ 2) by ring, hω, mul_zero, mul_zero]

theorem airyTaylorG'_zero : airyTaylorG' 0 = 1 := by
  unfold airyTaylorG'
  simp only [mul_zero]
  have h3 := airyOmega_cube
  have hne : 3 * deriv airyAiC 0 ≠ 0 := mul_ne_zero (by norm_num) deriv_airyAiC_zero_ne
  rw [show ((deriv airyAiC 0 + airyOmega ^ 2 * (airyOmega * deriv airyAiC 0)) +
    airyOmega * (airyOmega ^ 2 * deriv airyAiC 0)) = 3 * deriv airyAiC 0 by
      linear_combination (2 * deriv airyAiC 0) * h3]
  exact inv_mul_cancel₀ hne

/-- **Explicit power-series representation of `Ai`**:
`Ai(z) = 3^{-2/3}/Γ(2/3) · F(z) - 3^{-1/3}/Γ(1/3) · G(z)`. -/
theorem airyAiC_eq_explicit (z : ℂ) :
    airyAiC z = (((3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3) : ℝ) : ℂ) * airyTaylorF z -
      (((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3) : ℝ) : ℂ) * airyTaylorG z := by
  have e1 : airyAiC 0 = (airyAi 0 : ℂ) := by simpa using airyAiC_ofReal 0
  have e2 : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by simpa using deriv_airyAiC_ofReal 0
  rw [airyAiC_eq_taylor z, e1, e2, airyAi_zero, airyAi'_zero]
  push_cast
  ring

/-- info: 'FormalResearch.Special.airyAiC_eq_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_eq_taylor

/-- info: 'FormalResearch.Special.hasSum_airyTaylorF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hasSum_airyTaylorF

/-- info: 'FormalResearch.Special.hasSum_airyTaylorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hasSum_airyTaylorG

/-- info: 'FormalResearch.Special.isAirySol_airyTaylorF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.isAirySol_airyTaylorF

/-- info: 'FormalResearch.Special.isAirySol_airyTaylorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.isAirySol_airyTaylorG

/-- info: 'FormalResearch.Special.airyAiC_eq_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_eq_explicit

end FormalResearch.Special

module

public import FormalResearch.Complex.ChebyshevBernstein
public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryReal

/-!
# Chebyshev approximation of `Ai(s + ·)` on `[0, R]` (Bernstein ellipse parameter `ρ = 2`)

**Proved.**  Specialises `FormalResearch.Chebyshev.BernsteinHyp.error_real_re` to the entire function
`z ↦ Ai(s + R/2 + (R/2) z)`, whose restriction to `x ∈ [-1,1]` is `Ai(s + ζ)` for `ζ = R(x+1)/2 ∈ [0,R]`.
With `ρ = 2` the boundary ellipse is `joukowski '' {|w| = 2}`, contained in `|z| ≤ 5/4`, so for `|s| ≤ R` the
argument of `Ai` stays in `|·| ≤ 17R/8` and the order-`3/2` growth bound `airyAiC_norm_le_exp_rpow` gives
`M = airyChebM R = 3 exp((2/3)(17R/8)^{3/2})`.  Result (`airy_cheb_pointwise`): for `|s| ≤ R`, `ζ ∈ [0,R]`, `n ∈ ℕ`,

`|Ai(s+ζ) - Σ_{k ≤ n} a_k(s) T_k(2ζ/R - 1)| ≤ 2 M / 2^n`,  `a_k(s) = Re chebCoeff` (`airyChebCoeff R s k`),

a rank-`(n+1)` separated approximation of the kernel `Ai(s+ζ)` in the variable `ζ`.  The coefficients `a_k`
depend continuously on `s` (`continuous_airyChebCoeff`), hence measurably.  This is the pointwise half of
`lem:airydecay` in `Weyl/free_fermion/paper/parts/edge.tex` (there with Chebyshev *interpolation* and `ρ = e`; the
truncation used here has the same rank; `ρ = 2` is chosen only to make the constants explicit).

**Not formalised:** the optimal choice of `ρ`, the interpolation (Chebyshev-point) version.
-/

@[expose] public section

open Complex Set FormalResearch.Chebyshev

namespace FormalResearch.Special

/-- `z ↦ Ai(c + h z)` for real `c, h`. -/
noncomputable def airyShiftScale (c h : ℝ) (z : ℂ) : ℂ := airyAiC ((c : ℂ) + (h : ℂ) * z)

lemma differentiable_airyShiftScale (c h : ℝ) : Differentiable ℂ (airyShiftScale c h) :=
  differentiable_airyAiC.comp (differentiable_const _ |>.add (differentiable_const _ |>.mul differentiable_id))

lemma norm_joukowski_le_of_norm_eq_two {w : ℂ} (hw : ‖w‖ = 2) : ‖joukowski w‖ ≤ 5 / 4 := by
  unfold joukowski
  rw [norm_div]
  have h1 : ‖w + w⁻¹‖ ≤ 5 / 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv, hw]; norm_num
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  linarith

/-- The uniform bound `M(R) = 3 exp((2/3)(17R/8)^{3/2})` for `|Ai|` on the boundary ellipse. -/
noncomputable def airyChebM (R : ℝ) : ℝ := 3 * Real.exp ((2 / 3) * ((17 / 8) * R) ^ (3 / 2 : ℝ))

lemma airyChebM_nonneg (R : ℝ) : 0 ≤ airyChebM R := by unfold airyChebM; positivity

lemma bernsteinHyp_airy {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ R) :
    BernsteinHyp (airyShiftScale (s + R / 2) (R / 2)) 2 (airyChebM R) := by
  refine bernsteinHyp_of_differentiable (by norm_num) (differentiable_airyShiftScale _ _) ?_
  intro w hw
  unfold airyShiftScale
  refine (airyAiC_norm_le_exp_rpow _).trans ?_
  unfold airyChebM
  have h5 := norm_joukowski_le_of_norm_eq_two hw
  have h1 : ‖((s + R / 2 : ℝ) : ℂ) + ((R / 2 : ℝ) : ℂ) * joukowski w‖ ≤ (17 / 8) * R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < R / 2)]
    have : |s + R / 2| ≤ 3 / 2 * R := by
      rw [abs_le] at hs ⊢; constructor <;> linarith [hs.1, hs.2]
    have h2 : R / 2 * ‖joukowski w‖ ≤ R / 2 * (5 / 4) := by gcongr
    linarith
  have h3 := Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h4 : (2 / 3 : ℝ) * ‖((s + R / 2 : ℝ) : ℂ) + ((R / 2 : ℝ) : ℂ) * joukowski w‖ ^ (3 / 2 : ℝ) ≤
      (2 / 3) * ((17 / 8) * R) ^ (3 / 2 : ℝ) := by linarith
  have := Real.exp_le_exp.2 h4
  linarith

/-- The real part of the `k`-th Chebyshev coefficient of `ζ ↦ Ai(s + ζ)` on `[0, R]` (`ρ = 2`). -/
noncomputable def airyChebCoeff (R s : ℝ) (k : ℕ) : ℝ :=
  (chebCoeff (fun w => airyShiftScale (s + R / 2) (R / 2) (joukowski w)) 2 k).re

/-- **Pointwise Chebyshev approximation of the Airy kernel in `ζ`**: for `|s| ≤ R`, `0 ≤ ζ ≤ R`. -/
theorem airy_cheb_pointwise {R s ζ : ℝ} (hR : 0 < R) (hs : |s| ≤ R) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ R)
    (n : ℕ) :
    |airyAi (s + ζ) - ∑ k ∈ Finset.range (n + 1), airyChebCoeff R s k *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (2 * ζ / R - 1)| ≤ 2 * airyChebM R / 2 ^ n := by
  have hx : |2 * ζ / R - 1| ≤ 1 := by
    rw [abs_le]; constructor
    · have : 0 ≤ 2 * ζ / R := by positivity
      linarith
    · have : 2 * ζ / R ≤ 2 := by rw [div_le_iff₀ hR]; linarith
      linarith
  have h := (bernsteinHyp_airy hR hs).error_real_re n hx
  have e : (airyShiftScale (s + R / 2) (R / 2) (((2 * ζ / R - 1 : ℝ)) : ℂ)).re = airyAi (s + ζ) := by
    unfold airyShiftScale airyAi
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    congr 2
    push_cast
    field_simp
    ring
  rw [e] at h
  simpa [airyChebCoeff] using h.trans (le_of_eq (by norm_num))

lemma continuous_airyChebCoeff (R : ℝ) (k : ℕ) :
    Continuous fun s => airyChebCoeff R s k := by
  unfold airyChebCoeff
  refine Complex.continuous_re.comp (continuous_chebCoeff (S := ℝ)
    (G := fun s w => airyShiftScale (s + R / 2) (R / 2) (joukowski w)) ?_ (by norm_num) k)
  refine (differentiable_airyAiC.continuous.comp_continuousOn ?_)
  refine ContinuousOn.add (by fun_prop) (continuousOn_const.mul ?_)
  unfold joukowski
  refine ContinuousOn.div_const (ContinuousOn.add (by fun_prop) ?_) _
  exact ContinuousOn.inv₀ (by fun_prop) fun p hp => hp

/-- info: 'FormalResearch.Special.airy_cheb_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_cheb_pointwise

/-- info: 'FormalResearch.Special.continuous_airyChebCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.continuous_airyChebCoeff

end FormalResearch.Special

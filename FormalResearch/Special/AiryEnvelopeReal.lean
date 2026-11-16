module

public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryEnvelopeNeg

/-!
# The real-axis envelope of `Ai` on `[-1, ∞)`

With `ξ(X) = (2/3) (max X 0)^{3/2}` (`airyXi`), for every `X ≥ -1`:

* `airyAi_envelope_real`: `(1/20) (2+X)^{-1/4} e^{-ξ(X)} ≤ Ai(X) ≤ 4 (2+X)^{-1/4} e^{-ξ(X)}`
  (so `Ai(X) ≍ (2+X)^{-1/4} e^{-ξ(X)}`, in particular `Ai > 0`);
* `abs_airyAi'_le_mul_airyAi`: `|Ai'(X)| ≤ 120 (2+X)^{1/2} Ai(X)`.

The upper bounds are (E1), (E1′) on the real axis, where `Re X^{3/2} = (max X 0)^{3/2}`
(`re_ofReal_cpow_three_halves`: it vanishes on the negative axis).  The lower bound is `airyAi_lower_bound`
on `[1, ∞)`, monotonicity on `[0, 1]` and the Sturm-type bound `Ai(x) ≥ Ai(0) cos x` of `AiryEnvelopeNeg` on
`[-1, 0]`.  The constants are far from optimal (the true two-sided ratio constants are about `0.28` and `0.57`
on this range, by a numerical check) and the range `X ≥ -1` is not sharp (`Ai > 0` up to the first zero
`≈ -2.338`, which is not located here).
-/

@[expose] public section

open Complex Set
open scoped Real

namespace FormalResearch.Special

/-- `ξ(X) = (2/3) (X₊)^{3/2}`. -/
noncomputable def airyXi (X : ℝ) : ℝ := (2 / 3) * (max X 0) ^ (3 / 2 : ℝ)

lemma airyXi_nonneg (X : ℝ) : 0 ≤ airyXi X := by
  unfold airyXi
  have := Real.rpow_nonneg (le_max_right X 0) (3 / 2 : ℝ)
  positivity

/-- On the real axis the principal `X^{3/2}` has real part `(X₊)^{3/2}` (zero for `X < 0`). -/
lemma re_ofReal_cpow_three_halves (X : ℝ) :
    ((X : ℂ) ^ (3 / 2 : ℂ)).re = (max X 0) ^ (3 / 2 : ℝ) := by
  rcases le_or_gt 0 X with hX | hX
  · rw [max_eq_left hX]
    have := Complex.ofReal_cpow hX (3 / 2 : ℝ)
    push_cast at this
    rw [← this, Complex.ofReal_re]
  · rw [max_eq_right hX.le, Real.zero_rpow (by norm_num), ← cpow_half_cube]
    set w := (X : ℂ) ^ (1 / 2 : ℂ) with hw
    have h2 := cpow_half_sq (X : ℂ)
    rw [← hw] at h2
    have hre := congrArg Complex.re h2
    have him := congrArg Complex.im h2
    rw [re_sq] at hre
    rw [im_sq] at him
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
    have ha := cpow_half_re_nonneg (X : ℂ)
    rw [← hw] at ha
    have hmul : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h | h
    · rw [re_cube, h]; ring
    · rw [h] at hre; nlinarith [sq_nonneg w.re]

lemma norm_airyAiC_ofReal (X : ℝ) : ‖airyAiC (X : ℂ)‖ = |airyAi X| := by
  rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]

lemma norm_deriv_airyAiC_ofReal (X : ℝ) : ‖deriv airyAiC (X : ℂ)‖ = |airyAi' X| := by
  rw [deriv_airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs]

lemma two_rpow_quarter_le : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 6 / 5 := by
  have h4 := rpow_quarter_pow_four (t := 1) (by norm_num)
  norm_num at h4
  set q := (2 : ℝ) ^ (1 / 4 : ℝ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  by_contra h
  rw [not_le] at h
  have := pow_lt_pow_left₀ h (by norm_num) (four_ne_zero)
  nlinarith

/-- `(1 + |X|)^{1/4} ≤ (6/5) (2 + X)^{1/4}` and `(2+X)^{1/4} ≤ (6/5) (1 + |X|)^{1/4}` for `X ≥ -1`. -/
lemma rpow_quarter_compare {X : ℝ} (hX : -1 ≤ X) :
    (1 + |X|) ^ (1 / 4 : ℝ) ≤ 6 / 5 * (2 + X) ^ (1 / 4 : ℝ) ∧
      (2 + X) ^ (1 / 4 : ℝ) ≤ 6 / 5 * (1 + |X|) ^ (1 / 4 : ℝ) := by
  have h1 : 0 < 1 + |X| := by positivity
  have h2 : 0 < 2 + X := by linarith
  have h3 : 1 + |X| ≤ 2 * (2 + X) := by
    rcases le_or_gt 0 X with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have h4 : 2 + X ≤ 2 * (1 + |X|) := by
    rcases le_or_gt 0 X with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have := two_rpow_quarter_le
  constructor
  · calc (1 + |X|) ^ (1 / 4 : ℝ) ≤ (2 * (2 + X)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow h1.le h3 (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * (2 + X) ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) h2.le
      _ ≤ _ := by gcongr
  · calc (2 + X) ^ (1 / 4 : ℝ) ≤ (2 * (1 + |X|)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow h2.le h4 (by norm_num)
      _ = 2 ^ (1 / 4 : ℝ) * (1 + |X|) ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) h1.le
      _ ≤ _ := by gcongr

lemma exp_neg_two_thirds_ge : 1 / 2 ≤ Real.exp (-(2 / 3)) := by
  have h3 : Real.exp (2 / 3) ^ 3 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hE2 := exp_two_le
  have hp := Real.exp_pos (2 / 3 : ℝ)
  have h2 : Real.exp (2 / 3) ≤ 2 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (three_ne_zero)
    nlinarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hp h2

/-- `Ai(1) ≥ 1/9`. -/
lemma airyAi_one_ge : 1 / 9 ≤ airyAi 1 := by
  have h := airyAi_lower_bound (x := 1) one_pos
  simp only [Real.one_rpow, neg_mul, Real.exp_neg] at h
  have h2 := exp_neg_two_thirds_ge
  rw [Real.exp_neg] at h2
  obtain ⟨-, hs2⟩ := sqrt_pi_bounds
  have hs1 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hexp : 0 < Real.exp (2 / 3) := Real.exp_pos _
  have hex2 : Real.exp (2 / 3) ≤ 2 := by
    have := Real.exp_neg (2 / 3 : ℝ)
    have h3 : (Real.exp (2 / 3))⁻¹ ≥ 1 / 2 := by simpa using h2
    by_contra hc
    rw [not_le] at hc
    have : (Real.exp (2 / 3))⁻¹ < 1 / 2 := by
      rw [inv_lt_comm₀ hexp (by norm_num)]; simpa using hc
    linarith
  have key : 1 / (2 * √π) * (Real.exp (2 / 3))⁻¹ * (1 - 5 / 48 / 1) ≤ airyAi 1 := by
    simpa [Real.rpow_neg_one, mul_comm, mul_assoc, mul_left_comm] using h
  refine le_trans ?_ key
  have hinv : 1 / 2 ≤ (Real.exp (2 / 3))⁻¹ := by simpa using h2
  have : 1 / 4 ≤ 1 / (2 * √π) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have h0 : 0 ≤ 1 / (2 * √π) := by positivity
  calc (1 : ℝ) / 9 ≤ 1 / 4 * (1 / 2) * (1 - 5 / 48 / 1) := by norm_num
    _ ≤ 1 / (2 * √π) * (Real.exp (2 / 3))⁻¹ * (1 - 5 / 48 / 1) := by
        gcongr


/-- Upper bound: `|Ai(X)| ≤ 4 (2+X)^{-1/4} e^{-ξ(X)}` for `X ≥ -1`. -/
theorem abs_airyAi_le_real {X : ℝ} (hX : -1 ≤ X) :
    |airyAi X| ≤ 4 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) := by
  have h := airyAiC_envelope (X : ℂ)
  rw [norm_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real, Real.norm_eq_abs] at h
  have hE : Real.exp (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ)) = Real.exp (-airyXi X) := by
    unfold airyXi; congr 1; ring
  rw [hE] at h
  have h2 : 0 < 2 + X := by linarith
  have h1 : 0 < 1 + |X| := by positivity
  obtain ⟨-, hc⟩ := rpow_quarter_compare hX
  have hq : (1 + |X|) ^ (-(1 / 4) : ℝ) ≤ 6 / 5 * (2 + X) ^ (-(1 / 4) : ℝ) := by
    have hu := Real.rpow_pos_of_pos h1 (1 / 4 : ℝ)
    have hv := Real.rpow_pos_of_pos h2 (1 / 4 : ℝ)
    rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
      div_le_div_iff₀ hu hv]
    linarith
  have hEp := Real.exp_pos (-airyXi X)
  calc |airyAi X| ≤ 3 * (1 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) := h
    _ ≤ 3 * (6 / 5 * (2 + X) ^ (-(1 / 4) : ℝ)) * Real.exp (-airyXi X) := by gcongr
    _ ≤ 4 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) := by
        have := Real.rpow_pos_of_pos h2 (-(1 / 4) : ℝ)
        nlinarith [mul_pos this hEp]

/-- Lower bound: `(1/20) (2+X)^{-1/4} e^{-ξ(X)} ≤ Ai(X)` for `X ≥ -1`. -/
theorem airyAi_ge_real {X : ℝ} (hX : -1 ≤ X) :
    1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) ≤ airyAi X := by
  have h2 : 0 < 2 + X := by linarith
  have hE1 : Real.exp (-airyXi X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [airyXi_nonneg X])
  have hEp := Real.exp_pos (-airyXi X)
  rcases le_or_gt 1 X with h1 | h1
  · -- `X ≥ 1`: the lower bound of `AiryPositive`
    have hX0 : 0 < X := by linarith
    have hl := airyAi_lower_bound hX0
    have hmax : max X 0 = X := max_eq_left hX0.le
    have hξ : airyXi X = (2 / 3) * X ^ (3 / 2 : ℝ) := by unfold airyXi; rw [hmax]
    have hX32 : 1 ≤ X ^ (3 / 2 : ℝ) := Real.one_le_rpow h1 (by norm_num)
    have hfac : 43 / 48 ≤ 1 - 5 / 48 / X ^ (3 / 2 : ℝ) := by
      have : 5 / 48 / X ^ (3 / 2 : ℝ) ≤ 5 / 48 := div_le_self (by norm_num) hX32
      linarith
    have hq : (2 + X) ^ (-(1 / 4) : ℝ) ≤ X ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX0 (by linarith) (by norm_num)
    obtain ⟨-, hs2⟩ := sqrt_pi_bounds
    have hs1 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    have hc : 1 / 4 ≤ 1 / (2 * √π) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have hXq := Real.rpow_pos_of_pos hX0 (-(1 / 4) : ℝ)
    have hexp : Real.exp (-(2 / 3) * X ^ (3 / 2 : ℝ)) = Real.exp (-airyXi X) := by
      rw [hξ]; congr 1; ring
    rw [hexp] at hl
    refine le_trans ?_ hl
    have hp : 0 < X ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) := mul_pos hXq hEp
    have : 1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) ≤
        1 / 20 * X ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) := by gcongr
    refine this.trans ?_
    have hmain : 1 / 20 ≤ 1 / (2 * √π) * (1 - 5 / 48 / X ^ (3 / 2 : ℝ)) := by
      have h43 : 0 ≤ 1 / (2 * √π) := by positivity
      calc (1 : ℝ) / 20 ≤ 1 / 4 * (43 / 48) := by norm_num
        _ ≤ _ := by gcongr
    calc 1 / 20 * X ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)
        = 1 / 20 * (X ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)) := by ring
      _ ≤ (1 / (2 * √π) * (1 - 5 / 48 / X ^ (3 / 2 : ℝ))) *
            (X ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)) := mul_le_mul_of_nonneg_right hmain hp.le
      _ = _ := by ring
  · -- `-1 ≤ X < 1`
    have hq1 : (2 + X) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hq0 := Real.rpow_pos_of_pos h2 (-(1 / 4) : ℝ)
    have hrhs : 1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) ≤ 1 / 20 := by
      have : (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) ≤ 1 :=
        (mul_le_mul hq1 hE1 hEp.le zero_le_one).trans (by norm_num)
      nlinarith
    refine hrhs.trans ?_
    have hA1 : 1 / 9 ≤ airyAi 1 := airyAi_one_ge
    rcases le_or_gt 0 X with h0 | h0
    · have hmono := strictAntiOn_airyAi.antitoneOn (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr zero_le_one)
        h1.le
      linarith
    · have hge := airyAi_ge_on_Icc hX h0.le
      have hA0 : airyAi 1 ≤ airyAi 0 :=
        strictAntiOn_airyAi.antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
          zero_le_one
      have hcos : 1 / 2 ≤ Real.cos X := by
        have := Real.one_sub_sq_div_two_le_cos (x := X)
        nlinarith
      have hApos : 0 < airyAi 0 := airyAi_pos le_rfl
      nlinarith

/-- **Two-sided real-axis envelope**: for `X ≥ -1`,
`(1/20) (2+X)^{-1/4} e^{-ξ(X)} ≤ Ai(X) ≤ 4 (2+X)^{-1/4} e^{-ξ(X)}`, `ξ(X) = (2/3)(max X 0)^{3/2}`. -/
theorem airyAi_envelope_real {X : ℝ} (hX : -1 ≤ X) :
    1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) ≤ airyAi X ∧
      airyAi X ≤ 4 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) :=
  ⟨airyAi_ge_real hX, (le_abs_self _).trans (abs_airyAi_le_real hX)⟩

/-- **`|Ai'| ≤ C (2+X)^{1/2} Ai` on `[-1, ∞)`** (`C = 120`). -/
theorem abs_airyAi'_le_mul_airyAi {X : ℝ} (hX : -1 ≤ X) :
    |airyAi' X| ≤ 120 * (2 + X) ^ (1 / 2 : ℝ) * airyAi X := by
  have h := airyAiC_deriv_envelope (X : ℂ)
  rw [norm_deriv_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real,
    Real.norm_eq_abs] at h
  have hE : Real.exp (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ)) = Real.exp (-airyXi X) := by
    unfold airyXi; congr 1; ring
  rw [hE] at h
  have h2 : 0 < 2 + X := by linarith
  have h1 : 0 < 1 + |X| := by positivity
  obtain ⟨hc, -⟩ := rpow_quarter_compare hX
  have hlow := airyAi_ge_real hX
  have hEp := Real.exp_pos (-airyXi X)
  have hp : 0 < (2 + X) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos h2 _
  have hsq : (2 + X) ^ (1 / 4 : ℝ) * (2 + X) ^ (1 / 4 : ℝ) = (2 + X) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add h2]; norm_num
  have hneg : (2 + X) ^ (1 / 4 : ℝ) * (2 + X) ^ (-(1 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add h2]; norm_num
  -- `Ai ≥ (1/20) (2+X)^{-1/4} e^{-ξ}` gives `e^{-ξ} ≤ 20 (2+X)^{1/4} Ai`
  have hexp : Real.exp (-airyXi X) ≤ 20 * (2 + X) ^ (1 / 4 : ℝ) * airyAi X := by
    have := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 20 * (2 + X) ^ (1 / 4 : ℝ))
    calc Real.exp (-airyXi X) = 20 * (2 + X) ^ (1 / 4 : ℝ) *
          (1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)) := by
          have : 20 * (2 + X) ^ (1 / 4 : ℝ) *
            (1 / 20 * (2 + X) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X)) =
            ((2 + X) ^ (1 / 4 : ℝ) * (2 + X) ^ (-(1 / 4) : ℝ)) * Real.exp (-airyXi X) := by ring
          rw [this, hneg, one_mul]
      _ ≤ _ := this
  calc |airyAi' X| ≤ 5 * (1 + |X|) ^ (1 / 4 : ℝ) * Real.exp (-airyXi X) := h
    _ ≤ 5 * (6 / 5 * (2 + X) ^ (1 / 4 : ℝ)) * Real.exp (-airyXi X) := by gcongr
    _ ≤ 5 * (6 / 5 * (2 + X) ^ (1 / 4 : ℝ)) * (20 * (2 + X) ^ (1 / 4 : ℝ) * airyAi X) := by
        gcongr
    _ = 120 * ((2 + X) ^ (1 / 4 : ℝ) * (2 + X) ^ (1 / 4 : ℝ)) * airyAi X := by ring
    _ = _ := by rw [hsq]

/-- info: 'FormalResearch.Special.airyAi_envelope_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_envelope_real

/-- info: 'FormalResearch.Special.abs_airyAi'_le_mul_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyAi'_le_mul_airyAi

end FormalResearch.Special

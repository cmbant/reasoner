module

public import FormalResearch.Special.AiryPositive
public import FormalResearch.Special.AiryRotation

/-!
# Saddle-point formula for `Ai(w²)` and its second-order Gaussian estimate

For `Re w > 0` the abscissa `c = Re w` is admissible in the contour-independent integral of `AiryDef`, and
the substitution `t = w + i s` (a real shift `s ↦ s + Im w` of the integration variable on the line
`Re t = Re w`) turns the exponent into the *exact* saddle-point form
`t³/3 - w² t = -(2/3) w³ - w s² - i s³/3`.  Hence, with `ρ = Re w`,

* `airyAiC_sq_eq` : `Ai(w²) = (e^{-(2/3) w³}/(2π)) ∫_ℝ exp(-w s² - i s³/3) ds`;
* `deriv_airyAiC_sq_eq` : `Ai'(w²) = -(e^{-(2/3) w³}/(2π)) ∫_ℝ (w + i s) exp(-w s² - i s³/3) ds`.

Expanding `exp(-i s³/3) = 1 - i s³/3 + R(s)`, `|R(s)| ≤ s⁶/18`, the odd term integrates to `0`
against the even Gaussian and the Gaussian moments `∫ s^6 e^{-ρ s²} = (15/8)√(π/ρ)/ρ³`,
`∫ s^4 e^{-ρ s²} = (3/4)√(π/ρ)/ρ²` give, for every `w` with `Re w > 0` (no other restriction):

* `norm_airyAiC_sq_sub_le` :
  `‖Ai(w²) - (e^{-(2/3) w³}/(2π)) (π/w)^{1/2}‖ ≤ (5/(96√π)) ‖e^{-(2/3) w³}‖ ρ^{-7/2}`
  (the bound is stated as `(1/(2π)) ‖e^{-(2/3)w³}‖ · (5/48) √(π/ρ)/ρ³`);
* `norm_deriv_airyAiC_sq_add_le` :
  `‖Ai'(w²) + (e^{-(2/3) w³}/(2π)) w (π/w)^{1/2}‖ ≤ (1/(2π)) ‖e^{-(2/3)w³}‖ (|w| (5/48)√(π/ρ)/ρ³ + (1/4)√(π/ρ)/ρ²)`.

No Olver theory is used; the contour is the line through the saddle `t = w` of `t³/3 - w² t`.
Not proved here: the higher terms of the asymptotic series, sector-uniform statements beyond
`Re w > 0`, `Ai` outside the sector `|arg z| < π` (the negative axis is `AiryAsymNeg`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The Gaussian factor `exp(-w s²)`. -/
noncomputable def saddleGauss (w : ℂ) (s : ℝ) : ℂ := cexp (-w * (s : ℂ) ^ 2)

/-- The cubic phase `exp(-i s³/3)`. -/
noncomputable def saddlePhase (s : ℝ) : ℂ := cexp (I * ((-(s ^ 3 / 3) : ℝ) : ℂ))

/-- `∫ exp(-w s² - i s³/3) ds`. -/
noncomputable def saddleJ0 (w : ℂ) : ℂ := ∫ s : ℝ, saddlePhase s * saddleGauss w s

/-- `∫ s exp(-w s² - i s³/3) ds`. -/
noncomputable def saddleJ1 (w : ℂ) : ℂ := ∫ s : ℝ, (s : ℂ) * saddlePhase s * saddleGauss w s

lemma continuous_saddleGauss (w : ℂ) : Continuous (saddleGauss w) := by
  unfold saddleGauss; fun_prop

lemma continuous_saddlePhase : Continuous saddlePhase := by
  unfold saddlePhase; fun_prop

lemma norm_saddleGauss (w : ℂ) (s : ℝ) : ‖saddleGauss w s‖ = Real.exp (-w.re * s ^ 2) := by
  unfold saddleGauss
  exact norm_cexp_neg_mul_sq w s

lemma norm_saddlePhase (s : ℝ) : ‖saddlePhase s‖ = 1 := by
  unfold saddlePhase
  exact Complex.norm_exp_I_mul_ofReal _

/-! ### The exact saddle-point change of variables -/

lemma airyPoly_shift (k : ℕ) (w : ℂ) (s : ℝ) :
    airyPoly k w.re (w ^ 2) (s + w.im) =
      (-(w + (s : ℂ) * I)) ^ k * cexp (-(2 / 3) * w ^ 3) * (saddlePhase s * saddleGauss w s) := by
  have hl : airyLine w.re (s + w.im) = w + (s : ℂ) * I := by
    refine Complex.ext (by simp [airyLine]) (by simp [airyLine]; ring)
  unfold airyPoly airyKernel
  rw [hl]
  have hexp : cexp ((w + (s : ℂ) * I) ^ 3 / 3 - w ^ 2 * (w + (s : ℂ) * I)) =
      cexp (-(2 / 3) * w ^ 3) * (saddlePhase s * saddleGauss w s) := by
    unfold saddlePhase saddleGauss
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (w * (s : ℂ) ^ 2 + (s : ℂ) ^ 3 * I / 3) * Complex.I_sq
  rw [hexp]
  ring

/-- Saddle-point form of the moments: for `Re w > 0`,
`M_k(Re w, w²) = (e^{-(2/3)w³}/(2π)) ∫ (-(w + i s))^k exp(-w s² - i s³/3) ds`. -/
lemma airyMom_sq_eq (k : ℕ) (w : ℂ) :
    airyMom k w.re (w ^ 2) = (1 / (2 * (π : ℂ))) * (cexp (-(2 / 3) * w ^ 3) *
      ∫ s : ℝ, (-(w + (s : ℂ) * I)) ^ k * (saddlePhase s * saddleGauss w s)) := by
  unfold airyMom
  rw [← integral_add_right_eq_self (fun s' => airyPoly k w.re (w ^ 2) s') w.im]
  simp_rw [airyPoly_shift]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext s
  ring

/-! ### Elementary integrals -/

lemma integrable_abs_pow_gauss {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun s : ℝ => |s| ^ n * Real.exp (-a * s ^ 2)) := by
  simpa using integrable_absAdd_pow_gauss 0 ha n

lemma integrable_gauss_mul_of_le {w : ℂ} (hw : 0 < w.re) {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ)
    (C : ℝ) (hb : ∀ s, ‖f s‖ ≤ C * |s| ^ n) : Integrable (fun s => f s * saddleGauss w s) := by
  refine Integrable.mono' ((integrable_abs_pow_gauss hw n).const_mul C) ?_ ?_
  · exact (hf.mul (continuous_saddleGauss w)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [norm_mul, norm_saddleGauss]
    have := mul_le_mul_of_nonneg_right (hb s) (Real.exp_pos (-w.re * s ^ 2)).le
    simpa [mul_assoc] using this

lemma integral_eq_zero_of_odd {f : ℝ → ℂ} (h : ∀ s, f (-s) = -f s) : ∫ s, f s = 0 := by
  have h1 : ∫ s, f (-s) = ∫ s, f s := integral_neg_eq_self f volume
  simp_rw [h, integral_neg] at h1
  have : (2 : ℂ) * ∫ s, f s = 0 := by linear_combination -h1
  simpa using this

lemma integral_fourth_gauss {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, s ^ 4 * Real.exp (-c * s ^ 2) = 3 / 4 * √(π / c) / c ^ 2 := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 4 * Real.exp (-c * y ^ 2))
  simp only [sq_abs] at h
  have h4 : ∀ s : ℝ, |s| ^ 4 = s ^ 4 := fun s => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  simp only [h4] at h
  rw [h]
  have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 4) (b := c) two_pos (by norm_num) hc
  simp only [Real.rpow_two, show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast] at this
  rw [this]
  have hG : Real.Gamma (5 / 2) = 3 / 4 * √π := by
    have := Real.Gamma_nat_add_half 2
    norm_num [Nat.doubleFactorial] at this
    rw [this]
    ring
  have hE : c ^ (-(((4 : ℕ) : ℝ) + 1) / 2) = (c ^ (1 / 2 : ℝ))⁻¹ / c ^ 2 := by
    rw [show -(((4 : ℕ) : ℝ) + 1) / 2 = -(2 + 1 / 2 : ℝ) by norm_num, Real.rpow_neg hc.le,
      Real.rpow_add hc, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hS : √(π / c) = √π / c ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow c]
  rw [show (((4 : ℕ) : ℝ) + 1) / 2 = 5 / 2 by norm_num, hG, hE, hS]
  field_simp

/-- Second-order Taylor bound for the unit-circle exponential: `‖e^{ix} - 1 - ix‖ ≤ x²/2`. -/
lemma norm_exp_I_mul_sub_one_sub_le (x : ℝ) :
    ‖cexp (I * (x : ℂ)) - 1 - I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
  have hpos : ∀ x : ℝ, 0 ≤ x → ‖cexp (I * (x : ℂ)) - 1 - I * (x : ℂ)‖ ≤ x ^ 2 / 2 := by
    intro x hx
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * (t : ℂ)) - 1 - I * (t : ℂ))
        (I * (cexp (I * (t : ℂ)) - 1)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_mul I
      have h2 := (h1.cexp.sub_const 1).sub h1
      refine h2.congr_deriv ?_
      ring
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun t : ℝ => cexp (I * (t : ℂ)) - 1 - I * (t : ℂ)) (a := 0) (b := x)
      (f' := fun t => I * (cexp (I * (t : ℂ)) - 1))
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv t).hasDerivWithinAt) (B := fun t => t ^ 2 / 2) (B' := fun t => t)
      (by simp) (fun t => by simpa using (hasDerivAt_pow 2 t).div_const 2)
      (fun t ht => by
        rw [norm_mul, Complex.norm_I, one_mul]
        have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
        simpa [abs_of_nonneg ht.1] using this) ⟨hx, le_rfl⟩
    simpa using this
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have h := hpos (-x) (by linarith)
    have : cexp (I * ((-x : ℝ) : ℂ)) - 1 - I * ((-x : ℝ) : ℂ) =
        (starRingEnd ℂ) (cexp (I * (x : ℂ)) - 1 - I * (x : ℂ)) := by
      simp only [map_sub, map_one, map_mul, Complex.conj_I, ← Complex.exp_conj, Complex.conj_ofReal]
      push_cast
      simp only [mul_neg, neg_mul]
    rw [this, RCLike.norm_conj] at h
    simpa using h

/-! ### The Gaussian-cubic integrals -/

lemma integrable_saddle_phase_gauss {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun s : ℝ => saddlePhase s * saddleGauss w s) :=
  integrable_gauss_mul_of_le hw continuous_saddlePhase 0 1 (fun s => by simp [norm_saddlePhase])

lemma integrable_saddle_s_phase_gauss {w : ℂ} (hw : 0 < w.re) :
    Integrable (fun s : ℝ => (s : ℂ) * saddlePhase s * saddleGauss w s) :=
  integrable_gauss_mul_of_le hw (by unfold saddlePhase; fun_prop) 1 1
    (fun s => by simp [norm_saddlePhase])

lemma abs_pow_six (s : ℝ) : |s| ^ 6 = s ^ 6 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_mul, sq_abs]

lemma abs_pow_four (s : ℝ) : |s| ^ 4 = s ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]

/-- The second-order Gaussian estimate for `∫ exp(-w s² - i s³/3)`:
`‖J₀ - (π/w)^{1/2}‖ ≤ (5/48) √(π/ρ)/ρ³`, `ρ = Re w`. -/
lemma norm_saddleJ0_sub_le {w : ℂ} (hw : 0 < w.re) :
    ‖saddleJ0 w - (π / w) ^ (1 / 2 : ℂ)‖ ≤ 5 / 48 * (√(π / w.re) / w.re ^ 3) := by
  set D : ℝ → ℂ := fun s => saddlePhase s - 1 + I * ((s ^ 3 / 3 : ℝ) : ℂ) with hD
  have hDb : ∀ s, ‖D s‖ ≤ 1 / 18 * s ^ 6 := by
    intro s
    have := norm_exp_I_mul_sub_one_sub_le (-(s ^ 3 / 3))
    have e : D s = cexp (I * ((-(s ^ 3 / 3) : ℝ) : ℂ)) - 1 - I * ((-(s ^ 3 / 3) : ℝ) : ℂ) := by
      simp only [hD, saddlePhase]; push_cast; ring
    rw [e]
    refine this.trans (le_of_eq ?_)
    ring
  have hDc : Continuous D := by simp only [hD, saddlePhase]; fun_prop
  have iG : Integrable (fun s : ℝ => saddleGauss w s) := by
    have := integrable_gauss_mul_of_le (f := fun _ => (1 : ℂ)) hw continuous_const 0 1
      (fun s => by simp)
    simpa using this
  have iDG : Integrable (fun s : ℝ => D s * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw hDc 6 (1 / 18) (fun s => by
      rw [abs_pow_six]; exact hDb s)
  have iTG : Integrable (fun s : ℝ => I * ((s ^ 3 / 3 : ℝ) : ℂ) * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw (by fun_prop) 3 (1 / 3) (fun s => by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_pow]
      norm_num
      linarith)
  have hsplit : ∀ s, saddlePhase s * saddleGauss w s =
      saddleGauss w s + D s * saddleGauss w s - I * ((s ^ 3 / 3 : ℝ) : ℂ) * saddleGauss w s := by
    intro s; simp only [hD]; ring
  have hodd : ∫ s : ℝ, I * ((s ^ 3 / 3 : ℝ) : ℂ) * saddleGauss w s = 0 := by
    refine integral_eq_zero_of_odd fun s => ?_
    simp only [saddleGauss]
    push_cast
    ring_nf
  have hJ : saddleJ0 w - (π / w) ^ (1 / 2 : ℂ) = ∫ s : ℝ, D s * saddleGauss w s := by
    have iA : Integrable (fun s : ℝ => saddleGauss w s + D s * saddleGauss w s) := iG.add iDG
    unfold saddleJ0
    simp_rw [hsplit]
    rw [integral_sub iA iTG, integral_add iG iDG, hodd]
    have := integral_gaussian_complex hw
    simp only [saddleGauss]
    rw [this]
    ring
  rw [hJ]
  have i6 : Integrable (fun s : ℝ => 1 / 18 * (s ^ 6 * Real.exp (-w.re * s ^ 2))) := by
    have := (integrable_abs_pow_gauss hw 6).const_mul (1 / 18)
    simpa [abs_pow_six] using this
  refine (norm_integral_le_of_norm_le i6 (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, norm_saddleGauss]
    have := mul_le_mul_of_nonneg_right (hDb s) (Real.exp_pos (-w.re * s ^ 2)).le
    simpa [mul_assoc] using this
  · rw [integral_const_mul, integral_sixth_gauss hw]
    apply le_of_eq
    ring

/-- The first-order estimate for `∫ s exp(-w s² - i s³/3)`: `‖J₁‖ ≤ (1/4) √(π/ρ)/ρ²`. -/
lemma norm_saddleJ1_le {w : ℂ} (hw : 0 < w.re) :
    ‖saddleJ1 w‖ ≤ 1 / 4 * (√(π / w.re) / w.re ^ 2) := by
  set E : ℝ → ℂ := fun s => saddlePhase s - 1 with hE
  have hEb : ∀ s, ‖E s‖ ≤ 1 / 3 * |s| ^ 3 := by
    intro s
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(s ^ 3 / 3))
    simp only [hE, saddlePhase]
    refine this.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_neg, abs_div, abs_pow]
    norm_num
    ring
  have hEc : Continuous E := by simp only [hE, saddlePhase]; fun_prop
  have iSG : Integrable (fun s : ℝ => (s : ℂ) * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw Complex.continuous_ofReal 1 1 (fun s => by simp)
  have iSEG : Integrable (fun s : ℝ => (s : ℂ) * E s * saddleGauss w s) :=
    integrable_gauss_mul_of_le hw (by simp only [hE, saddlePhase]; fun_prop) 4 (1 / 3) (fun s => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |s| * ‖E s‖ ≤ |s| * (1 / 3 * |s| ^ 3) :=
            mul_le_mul_of_nonneg_left (hEb s) (abs_nonneg _)
        _ = 1 / 3 * |s| ^ 4 := by ring)
  have hsplit : ∀ s : ℝ, (s : ℂ) * saddlePhase s * saddleGauss w s =
      (s : ℂ) * saddleGauss w s + (s : ℂ) * E s * saddleGauss w s := by
    intro s; simp only [hE]; ring
  have hodd : ∫ s : ℝ, (s : ℂ) * saddleGauss w s = 0 := by
    refine integral_eq_zero_of_odd fun s => ?_
    simp only [saddleGauss]
    push_cast
    ring_nf
  unfold saddleJ1
  simp_rw [hsplit]
  rw [integral_add iSG iSEG, hodd, zero_add]
  have i4 : Integrable (fun s : ℝ => 1 / 3 * (s ^ 4 * Real.exp (-w.re * s ^ 2))) := by
    have := (integrable_abs_pow_gauss hw 4).const_mul (1 / 3)
    simpa [abs_pow_four] using this
  refine (norm_integral_le_of_norm_le i4 (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, norm_saddleGauss, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |s| * ‖E s‖ ≤ 1 / 3 * |s| ^ 4 := by
      calc |s| * ‖E s‖ ≤ |s| * (1 / 3 * |s| ^ 3) :=
            mul_le_mul_of_nonneg_left (hEb s) (abs_nonneg _)
        _ = 1 / 3 * |s| ^ 4 := by ring
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-w.re * s ^ 2)).le
    rw [abs_pow_four] at this
    simpa [mul_assoc] using this
  · rw [integral_const_mul, integral_fourth_gauss hw]
    apply le_of_eq
    ring

/-! ### The saddle-point formulas and the main estimates -/

/-- **Saddle-point formula** (S): for `Re w > 0`,
`Ai(w²) = (e^{-(2/3) w³}/(2π)) ∫_ℝ exp(-w s² - i s³/3) ds`. -/
theorem airyAiC_sq_eq {w : ℂ} (hw : 0 < w.re) :
    airyAiC (w ^ 2) = (1 / (2 * (π : ℂ))) * (cexp (-(2 / 3) * w ^ 3) * saddleJ0 w) := by
  rw [airyAiC_eq_airyMom hw, airyMom_sq_eq]
  simp [saddleJ0]

/-- Saddle-point formula for the derivative: for `Re w > 0`,
`Ai'(w²) = -(e^{-(2/3) w³}/(2π)) (w ∫ exp(-w s² - i s³/3) ds + i ∫ s exp(-w s² - i s³/3) ds)`. -/
theorem deriv_airyAiC_sq_eq {w : ℂ} (hw : 0 < w.re) :
    deriv airyAiC (w ^ 2) =
      -((1 / (2 * (π : ℂ))) * (cexp (-(2 / 3) * w ^ 3) * (w * saddleJ0 w + I * saddleJ1 w))) := by
  rw [deriv_airyAiC hw, airyMom_sq_eq]
  have iA := integrable_saddle_phase_gauss hw
  have iB := integrable_saddle_s_phase_gauss hw
  have : ∀ s : ℝ, (-(w + (s : ℂ) * I)) ^ 1 * (saddlePhase s * saddleGauss w s) =
      -(w * (saddlePhase s * saddleGauss w s) + I * ((s : ℂ) * saddlePhase s * saddleGauss w s)) := by
    intro s; ring
  simp_rw [this]
  rw [integral_neg, integral_add (iA.const_mul w) (iB.const_mul I), integral_const_mul,
    integral_const_mul]
  simp only [saddleJ0, saddleJ1]
  ring

/-- **Second-order saddle-point estimate for `Ai(w²)`**, every `w` with `ρ = Re w > 0`:
`‖Ai(w²) - (e^{-(2/3) w³}/(2π)) (π/w)^{1/2}‖ ≤ (1/(2π)) ‖e^{-(2/3) w³}‖ (5/48) √(π/ρ)/ρ³`,
i.e. `≤ (5/(96√π)) ‖e^{-(2/3) w³}‖ ρ^{-7/2}`.  Here `(π/w)^{1/2}` is the principal square root. -/
theorem norm_airyAiC_sq_sub_le {w : ℂ} (hw : 0 < w.re) :
    ‖airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (π / w) ^ (1 / 2 : ℂ)‖ ≤
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ * (5 / 48 * (√(π / w.re) / w.re ^ 3)) := by
  have e : airyAiC (w ^ 2) - (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (π / w) ^ (1 / 2 : ℂ) =
      (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (saddleJ0 w - (π / w) ^ (1 / 2 : ℂ)) := by
    rw [airyAiC_sq_eq hw]; ring
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_saddleJ0_sub_le hw) (by positivity)

/-- **Second-order saddle-point estimate for `Ai'(w²)`**, every `w` with `ρ = Re w > 0`:
`‖Ai'(w²) + (e^{-(2/3) w³}/(2π)) w (π/w)^{1/2}‖ ≤
  (1/(2π)) ‖e^{-(2/3) w³}‖ (‖w‖ (5/48) √(π/ρ)/ρ³ + (1/4) √(π/ρ)/ρ²)`. -/
theorem norm_deriv_airyAiC_sq_add_le {w : ℂ} (hw : 0 < w.re) :
    ‖deriv airyAiC (w ^ 2) +
        (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (w * (π / w) ^ (1 / 2 : ℂ))‖ ≤
      1 / (2 * π) * ‖cexp (-(2 / 3) * w ^ 3)‖ *
        (‖w‖ * (5 / 48 * (√(π / w.re) / w.re ^ 3)) + 1 / 4 * (√(π / w.re) / w.re ^ 2)) := by
  have e : deriv airyAiC (w ^ 2) +
        (1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) * (w * (π / w) ^ (1 / 2 : ℂ)) =
      -((1 / (2 * (π : ℂ))) * cexp (-(2 / 3) * w ^ 3) *
        (w * (saddleJ0 w - (π / w) ^ (1 / 2 : ℂ)) + I * saddleJ1 w)) := by
    rw [deriv_airyAiC_sq_eq hw]; ring
  rw [e, norm_neg, norm_mul, norm_mul]
  have h1 : ‖(1 / (2 * (π : ℂ)))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_saddleJ0_sub_le hw) (norm_nonneg _)
  · rw [norm_mul, Complex.norm_I, one_mul]
    exact norm_saddleJ1_le hw

/-- info: 'FormalResearch.Special.airyAiC_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_sq_eq

/-- info: 'FormalResearch.Special.norm_airyAiC_sq_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiC_sq_sub_le

/-- info: 'FormalResearch.Special.norm_deriv_airyAiC_sq_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_deriv_airyAiC_sq_add_le

end FormalResearch.Special

module

public import FormalResearch.Special.AiryTransform

/-!
# Derivatives of the Airy kernel `K(x, y)` in `x`

`airyD j s = Ai^{(j)}(s)` (real) is the `j`-th derivative of `Ai` on `ℝ`, with the three-term recurrence
`Ai^{(k+3)} = s Ai^{(k+1)} + (k+1) Ai^{(k)}` and the bound `|Ai^{(j)}(s)| ≤ C_j (1+|s|)^j e^{-(2/3)(s-1)}`
(from the envelope (E1), (E1') of `AiryEnvelope`, by induction).  Hence `t ↦ Ai^{(j)}(x+t) Ai(y+t)` is integrable on
`(0,∞)` with any polynomial weight, the Gram integral `K(x,y) = ∫_0^∞ Ai(x+t) Ai(y+t) dt`
(`airyKer_eq_integral`) can be differentiated in `x` under the integral sign, and
`∂_x^j K(x,y) = ∫_0^∞ Ai^{(j)}(x+t) Ai(y+t) dt` (`iteratedDeriv_airyKer_eq`).

These are the analytic inputs of `AiryPwsSum` (the identities `Σ_n |L_n^{(j)}(y)|² = ∫_y^∞ Ai^{(j)}(t)² dt`
and the expansion of `H = ∫ Ai(·+t) v(t) dt` in the functions `L_n = Ai/(u - a_n)`).

**Not formalised** here: the bound with the sharp exponent of `(1+|s|)` (`j/2 + ...`), explicit constants.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `Ai^{(j)}` on the real line: `(Ai^{(j)}(s)).re`, with `Ai^{(j)} = M_j(1, ·)` (`iteratedDeriv_airyAiC`). -/
noncomputable def airyD (j : ℕ) (s : ℝ) : ℝ := (airyMom j 1 (s : ℂ)).re

lemma airyD_zero : airyD 0 = airyAi := by
  funext s; simp [airyD, airyAi_eq_re_airyMom one_pos]

lemma airyD_one : airyD 1 = airyAi' := by
  funext s; simp [airyD, airyAi'_eq_re_airyMom one_pos]

theorem hasDerivAt_airyD (j : ℕ) (s : ℝ) : HasDerivAt (airyD j) (airyD (j + 1) s) s := by
  have h : HasDerivAt (fun y : ℝ => airyMom j 1 (y : ℂ)) (airyMom (j + 1) 1 (s : ℂ)) s :=
    (hasDerivAt_airyMom one_pos j (s : ℂ)).comp_ofReal
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h

lemma continuous_airyD (j : ℕ) : Continuous (airyD j) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_airyD j s).continuousAt

/-- `Ai^{(j)}` is `iteratedDeriv j airyAi` on `ℝ`. -/
theorem iteratedDeriv_airyAi_eq (j : ℕ) : iteratedDeriv j airyAi = airyD j := by
  induction j with
  | zero => rw [iteratedDeriv_zero, airyD_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (hasDerivAt_airyD j s).deriv

lemma airyMom_ofReal_im (j : ℕ) (s : ℝ) : (airyMom j 1 (s : ℂ)).im = 0 :=
  airyMom_im_ofReal j 1 s

lemma airyMom_ofReal_eq (j : ℕ) (s : ℝ) : airyMom j 1 (s : ℂ) = (airyD j s : ℂ) :=
  Complex.ext (by simp [airyD]) (by simpa using airyMom_ofReal_im j s)

lemma airyD_succ_succ_succ (k : ℕ) (s : ℝ) :
    airyD (k + 3) s = s * airyD (k + 1) s + (k + 1) * airyD k s := by
  have h := iteratedDeriv_airyAiC_succ_succ_succ k (s : ℂ)
  rw [iteratedDeriv_airyAiC, iteratedDeriv_airyAiC, iteratedDeriv_airyAiC, airyMom_ofReal_eq,
    airyMom_ofReal_eq, airyMom_ofReal_eq] at h
  have := congrArg Complex.re h
  simpa using this

/-! ### The real exponent `Re s^{3/2}` -/

lemma re_cpow_three_halves_ofReal (s : ℝ) :
    s - 1 ≤ ((s : ℂ) ^ (3 / 2 : ℂ)).re ∧ 0 ≤ ((s : ℂ) ^ (3 / 2 : ℂ)).re := by
  rcases lt_or_ge s 0 with hs | hs
  · have h := airyEnv_ofReal_neg hs
    unfold airyEnv at h
    have h2 := (Real.exp_eq_one_iff _).mp h
    have : ((s : ℂ) ^ (3 / 2 : ℂ)).re = 0 := by linarith
    rw [this]; exact ⟨by linarith, le_rfl⟩
  · have e : ((s : ℂ) ^ (3 / 2 : ℂ)).re = s ^ (3 / 2 : ℝ) := by
      have := Complex.ofReal_cpow hs (3 / 2 : ℝ)
      rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
      rw [← this, Complex.ofReal_re]
    rw [e]
    have h0 := Real.rpow_nonneg hs (3 / 2 : ℝ)
    refine ⟨?_, h0⟩
    rcases le_total s 1 with h1 | h1
    · linarith
    · have := Real.rpow_le_rpow_of_exponent_le h1 (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rw [Real.rpow_one] at this
      linarith

lemma exp_neg_re_cpow_le_one (s : ℝ) :
    Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [(re_cpow_three_halves_ofReal s).2])

lemma exp_neg_re_cpow_le_exp (s : ℝ) :
    Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) ≤ Real.exp (2 / 3) * Real.exp (-(2 / 3) * s) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [(re_cpow_three_halves_ofReal s).1])

/-! ### Bounds for `Ai^{(j)}` on `ℝ` -/

/-- `‖Ai^{(j)}(s)‖ ≤ C_j (1+|s|)^j exp(-(2/3) Re s^{3/2})`, for real `s`. -/
theorem norm_airyMom_ofReal_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖airyMom j 1 (s : ℂ)‖ ≤
      C * (1 + |s|) ^ j * Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hbase : ∀ s : ℝ, 1 ≤ 1 + |s| := fun s => by linarith [abs_nonneg s]
    match j, ih with
    | 0, _ =>
      refine ⟨3, by norm_num, fun s => ?_⟩
      have h := airyAiC_envelope (s : ℂ)
      have h1 := rpow_neg_quarter_le_one (s : ℂ)
      have h0 := Real.exp_pos (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re)
      have : airyMom 0 1 (s : ℂ) = airyAiC (s : ℂ) := by simp [airyAiC]
      rw [this, pow_zero, mul_one]
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) h0.le)
    | 1, _ =>
      refine ⟨5, by norm_num, fun s => ?_⟩
      have h := airyAiC_deriv_envelope (s : ℂ)
      have h0 := Real.exp_pos (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re)
      have : airyMom 1 1 (s : ℂ) = deriv airyAiC (s : ℂ) := by
        rw [deriv_airyAiC one_pos]
      rw [this, pow_one]
      refine h.trans ?_
      have h2 : (1 + ‖(s : ℂ)‖) ^ (1 / 4 : ℝ) ≤ 1 + |s| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        calc (1 + |s|) ^ (1 / 4 : ℝ) ≤ (1 + |s|) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (hbase s) (by norm_num)
          _ = 1 + |s| := Real.rpow_one _
      gcongr
    | 2, _ =>
      refine ⟨3, by norm_num, fun s => ?_⟩
      have h := airyAiC_envelope (s : ℂ)
      have h1 := rpow_neg_quarter_le_one (s : ℂ)
      have h0 := Real.exp_pos (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re)
      have : airyMom 2 1 (s : ℂ) = (s : ℂ) * airyAiC (s : ℂ) := by
        simpa [airyAiC] using airyMom_two one_pos (s : ℂ)
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hA : ‖airyAiC (s : ℂ)‖ ≤ 3 * Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) := by
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) h0.le)
      have hs : |s| ≤ (1 + |s|) ^ 2 := by nlinarith [abs_nonneg s]
      calc |s| * ‖airyAiC (s : ℂ)‖ ≤ (1 + |s|) ^ 2 * (3 * Real.exp (-(2 / 3) *
              ((s : ℂ) ^ (3 / 2 : ℂ)).re)) := by gcongr
        _ = _ := by ring
    | k + 3, ih =>
      obtain ⟨C1, hC1, h1⟩ := ih (k + 1) (by omega)
      obtain ⟨C0, hC0, h0⟩ := ih k (by omega)
      refine ⟨C1 + (k + 1) * C0, by positivity, fun s => ?_⟩
      have hrec := iteratedDeriv_airyAiC_succ_succ_succ k (s : ℂ)
      rw [iteratedDeriv_airyAiC, iteratedDeriv_airyAiC, iteratedDeriv_airyAiC] at hrec
      rw [hrec]
      set E := Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) with hE
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hb := hbase s
      have a1 := h1 s
      have a0 := h0 s
      calc ‖(s : ℂ) * airyMom (k + 1) 1 (s : ℂ) + ((k : ℂ) + 1) * airyMom k 1 (s : ℂ)‖
          ≤ ‖(s : ℂ)‖ * ‖airyMom (k + 1) 1 (s : ℂ)‖ + ‖((k : ℂ) + 1)‖ * ‖airyMom k 1 (s : ℂ)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (1 + |s|) * (C1 * (1 + |s|) ^ (k + 1) * E) + ((k : ℝ) + 1) * (C0 * (1 + |s|) ^ k * E) := by
            have e1 : ‖(s : ℂ)‖ ≤ 1 + |s| := by
              rw [Complex.norm_real, Real.norm_eq_abs]; linarith
            have e2 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
              rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
                Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            rw [e2]
            gcongr
        _ ≤ (C1 + (k + 1) * C0) * (1 + |s|) ^ (k + 3) * E := by
            have p1 : (1 + |s|) ^ k ≤ (1 + |s|) ^ (k + 2) := pow_le_pow_right₀ hb (by omega)
            have p2 : (1 + |s|) * (1 + |s|) ^ (k + 1) = (1 + |s|) ^ (k + 2) := by ring
            have p3 : (1 + |s|) ^ (k + 2) ≤ (1 + |s|) ^ (k + 3) := pow_le_pow_right₀ hb (by omega)
            have q1 : (1 + |s|) * (C1 * (1 + |s|) ^ (k + 1) * E) = C1 * (1 + |s|) ^ (k + 2) * E := by
              rw [← p2]; ring
            rw [q1]
            have : C0 * (1 + |s|) ^ k * E ≤ C0 * (1 + |s|) ^ (k + 3) * E := by gcongr; omega
            nlinarith [mul_nonneg hC1 hE0, mul_nonneg hC0 hE0, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + |s|) (k + 2),
              pow_nonneg (by linarith : (0:ℝ) ≤ 1 + |s|) (k + 3), mul_nonneg (mul_nonneg hC1 (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + |s|) (k + 3))) hE0,
              mul_nonneg (mul_nonneg hC1 (pow_nonneg (by linarith : (0:ℝ) ≤ 1 + |s|) (k + 2))) hE0]

/-- `|Ai^{(j)}(s)| ≤ C_j (1+|s|)^j e^{-(2/3) s}` for real `s` (the factor `e^{-(2/3)s}` is large for `s < 0`). -/
theorem abs_airyD_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |airyD j s| ≤ C * (1 + |s|) ^ j * Real.exp (-(2 / 3) * s) := by
  obtain ⟨C, hC, h⟩ := norm_airyMom_ofReal_le j
  refine ⟨C * Real.exp (2 / 3), by positivity, fun s => ?_⟩
  have h1 := h s
  rw [airyMom_ofReal_eq, Complex.norm_real, Real.norm_eq_abs] at h1
  have hp : 0 ≤ C * (1 + |s|) ^ j := by positivity
  calc |airyD j s| ≤ C * (1 + |s|) ^ j * Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) := h1
    _ ≤ C * (1 + |s|) ^ j * (Real.exp (2 / 3) * Real.exp (-(2 / 3) * s)) :=
        mul_le_mul_of_nonneg_left (exp_neg_re_cpow_le_exp s) hp
    _ = _ := by ring

/-- `|Ai^{(j)}(s)| ≤ C_j (1+|s|)^j` for real `s`. -/
theorem abs_airyD_le_poly (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |airyD j s| ≤ C * (1 + |s|) ^ j := by
  obtain ⟨C, hC, h⟩ := norm_airyMom_ofReal_le j
  refine ⟨C, hC, fun s => ?_⟩
  have h1 := h s
  rw [airyMom_ofReal_eq, Complex.norm_real, Real.norm_eq_abs] at h1
  have hp : 0 ≤ C * (1 + |s|) ^ j := by positivity
  calc |airyD j s| ≤ C * (1 + |s|) ^ j * Real.exp (-(2 / 3) * ((s : ℂ) ^ (3 / 2 : ℂ)).re) := h1
    _ ≤ C * (1 + |s|) ^ j * 1 := mul_le_mul_of_nonneg_left (exp_neg_re_cpow_le_one s) hp
    _ = _ := by ring

/-- `|Ai(s)| ≤ C e^{-(2/3) s}` for every real `s`. -/
theorem abs_airyAi_le_exp : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |airyAi s| ≤ C * Real.exp (-(2 / 3) * s) := by
  obtain ⟨C, hC, h⟩ := abs_airyD_le 0
  refine ⟨C, hC, fun s => ?_⟩
  have := h s
  rwa [airyD_zero, pow_zero, mul_one] at this

/-! ### Integrability and differentiation under the integral -/

/-- `(1+t)^m e^{-ct}` is integrable on `(0,∞)` for `c > 0`. -/
lemma integrableOn_pow_mul_exp (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ m * Real.exp (-c * t)) (Ioi 0) := by
  set ε := c / 2 with hε
  have hε0 : 0 < ε := by positivity
  set c' : ℝ := max 1 (m / ε) with hc'
  have hc1 : 1 ≤ c' := le_max_left _ _
  have hc0 : 0 < c' := by linarith
  have hmc : (m : ℝ) / c' ≤ ε := by
    rw [div_le_iff₀ hc0]
    have : (m : ℝ) / ε ≤ c' := le_max_right _ _
    rw [div_le_iff₀ hε0] at this
    linarith
  have hint : IntegrableOn (fun t : ℝ => c' ^ m * Real.exp (-ε * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hε0).const_mul _
  refine Integrable.mono' hint ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_)
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : 1 + t ≤ c' * Real.exp (t / c') := by
      have := Real.add_one_le_exp (t / c')
      have h2 : 1 + t = c' * (1 + t / c') - (c' - 1) := by field_simp; ring
      nlinarith
    have h2 : (1 + t) ^ m ≤ (c' * Real.exp (t / c')) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    have h3 : (c' * Real.exp (t / c')) ^ m = c' ^ m * Real.exp (m * (t / c')) := by
      rw [mul_pow, ← Real.exp_nat_mul]
    have h4 : Real.exp (m * (t / c')) ≤ Real.exp (ε * t) := by
      refine Real.exp_le_exp.mpr ?_
      have : (m : ℝ) * (t / c') = (m / c') * t := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hmc ht0
    calc (1 + t) ^ m * Real.exp (-c * t) ≤ c' ^ m * Real.exp (ε * t) * Real.exp (-c * t) := by
          rw [h3] at h2
          have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ c' ^ m)
          exact mul_le_mul_of_nonneg_right (h2.trans this) (Real.exp_pos _).le
      _ = c' ^ m * Real.exp (-ε * t) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hε]; ring

/-- Uniform domination: for `|x| ≤ R` and `t ≥ 0`,
`|Ai^{(j)}(x+t) Ai(y+t)| ≤ A (1+t)^j e^{-(2/3) t}`. -/
lemma abs_airyD_mul_le (j : ℕ) (R y : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, |x| ≤ R → ∀ t : ℝ, 0 ≤ t →
      |airyD j (x + t) * airyAi (y + t)| ≤ A * ((1 + t) ^ j * Real.exp (-(2 / 3) * t)) := by
  obtain ⟨C, hC, h1⟩ := abs_airyD_le_poly j
  obtain ⟨C0, hC0, h0⟩ := abs_airyAi_le_exp
  refine ⟨C * (1 + R) ^ j * (C0 * Real.exp (-(2 / 3) * y)), by positivity, fun x hx t ht => ?_⟩
  rw [abs_mul]
  have a1 := h1 (x + t)
  have a0 := h0 (y + t)
  have hb : 1 + |x + t| ≤ (1 + R) * (1 + t) := by
    have : |x + t| ≤ |x| + |t| := abs_add_le _ _
    rw [abs_of_nonneg ht] at this
    nlinarith [abs_nonneg x]
  have a1' : |airyD j (x + t)| ≤ C * ((1 + R) * (1 + t)) ^ j :=
    a1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb j) hC)
  have e0 : Real.exp (-(2 / 3) * (y + t)) = Real.exp (-(2 / 3) * y) * Real.exp (-(2 / 3) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e0] at a0
  calc |airyD j (x + t)| * |airyAi (y + t)|
      ≤ (C * ((1 + R) * (1 + t)) ^ j) * (C0 * (Real.exp (-(2 / 3) * y) * Real.exp (-(2 / 3) * t))) :=
        mul_le_mul a1' a0 (abs_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma integrableOn_airyD_mul (j : ℕ) (x y : ℝ) :
    IntegrableOn (fun t => airyD j (x + t) * airyAi (y + t)) (Ioi 0) := by
  obtain ⟨A, hA, hb⟩ := abs_airyD_mul_le j |x| y (abs_nonneg x)
  refine Integrable.mono' ((integrableOn_pow_mul_exp j (by norm_num : (0 : ℝ) < 2 / 3)).const_mul A) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have := continuous_airyD j
    have := continuous_airyAi
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact hb x le_rfl t (le_of_lt ht)

/-- Differentiation in `x` under the integral sign. -/
theorem hasDerivAt_airyKerD (j : ℕ) (y x0 : ℝ) :
    HasDerivAt (fun x => ∫ t in Ioi 0, airyD j (x + t) * airyAi (y + t))
      (∫ t in Ioi 0, airyD (j + 1) (x0 + t) * airyAi (y + t)) x0 := by
  obtain ⟨A, hA, hb⟩ := abs_airyD_mul_le (j + 1) (|x0| + 1) y (by positivity)
  have hI : Integrable (fun t : ℝ => A * ((1 + t) ^ (j + 1) * Real.exp (-(2 / 3) * t)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_pow_mul_exp (j + 1) (by norm_num : (0 : ℝ) < 2 / 3)).const_mul A
  have hc := continuous_airyD j
  have hc1 := continuous_airyD (j + 1)
  have hA0 := continuous_airyAi
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x t => airyD j (x + t) * airyAi (y + t))
    (F' := fun x t => airyD (j + 1) (x + t) * airyAi (y + t))
    (s := Metric.ball x0 1) (x₀ := x0)
    (bound := fun t => A * ((1 + t) ^ (j + 1) * Real.exp (-(2 / 3) * t)))
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun x => by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop)
    (integrableOn_airyD_mul j x0 y)
    (by refine Continuous.aestronglyMeasurable ?_; fun_prop)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht x hx => by
      rw [Real.norm_eq_abs]
      refine hb x ?_ t (le_of_lt ht)
      have := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub x x0
      linarith [abs_lt.mp ‹|x - x0| < 1›]))
    hI
    (Eventually.of_forall fun t x _ => by
      have h1 : HasDerivAt (fun x : ℝ => airyD j (x + t)) (airyD (j + 1) (x + t)) x :=
        (hasDerivAt_airyD j (x + t)).comp_add_const x t
      exact h1.mul_const _)
  exact key.2

/-- `K_j(x,y) = ∫_0^∞ Ai^{(j)}(x+t) Ai(y+t) dt`, the `j`-th `x`-derivative of the Airy kernel. -/
noncomputable def airyKerD (j : ℕ) (x y : ℝ) : ℝ := ∫ t in Ioi 0, airyD j (x + t) * airyAi (y + t)

lemma airyKerD_zero (x y : ℝ) : airyKerD 0 x y = airyKer x y := by
  rw [airyKer_eq_integral]; simp [airyKerD, airyD_zero]

theorem hasDerivAt_airyKerD' (j : ℕ) (x y : ℝ) :
    HasDerivAt (fun x => airyKerD j x y) (airyKerD (j + 1) x y) x :=
  hasDerivAt_airyKerD j y x

/-- **`∂_x^j K(x,y) = ∫_0^∞ Ai^{(j)}(x+t) Ai(y+t) dt`.** -/
theorem iteratedDeriv_airyKer_eq (j : ℕ) (y : ℝ) :
    iteratedDeriv j (fun x => airyKer x y) = fun x => airyKerD j x y := by
  induction j with
  | zero => funext x; rw [iteratedDeriv_zero, airyKerD_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_airyKerD' j x y).deriv

/-- `Ai^{(j)}(y+·)²` is integrable on `(0,∞)`. -/
lemma integrableOn_airyD_sq (j : ℕ) (y : ℝ) :
    IntegrableOn (fun t => airyD j (y + t) ^ 2) (Ioi 0) := by
  obtain ⟨C, hC, h1⟩ := abs_airyD_le j
  have hI := (integrableOn_pow_mul_exp (2 * j) (by norm_num : (0 : ℝ) < 4 / 3)).const_mul
    (C ^ 2 * (1 + |y|) ^ (2 * j) * Real.exp (-(4 / 3) * y))
  refine Integrable.mono' hI ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have := continuous_airyD j
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have a1 := h1 (y + t)
    have hb : 1 + |y + t| ≤ (1 + |y|) * (1 + t) := by
      have : |y + t| ≤ |y| + |t| := abs_add_le _ _
      rw [abs_of_nonneg ht0] at this
      nlinarith [abs_nonneg y]
    have a2 : |airyD j (y + t)| ≤ C * ((1 + |y|) * (1 + t)) ^ j * Real.exp (-(2 / 3) * (y + t)) :=
      a1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb j) hC) (Real.exp_pos _).le)
    have a3 := pow_le_pow_left₀ (abs_nonneg _) a2 2
    rw [sq_abs] at a3
    refine a3.trans (le_of_eq ?_)
    have e0 : Real.exp (-(2 / 3) * (y + t)) ^ 2 = Real.exp (-(4 / 3) * y) * Real.exp (-(4 / 3) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, mul_pow, e0, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
    ring

/-- info: 'FormalResearch.Special.iteratedDeriv_airyKer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.iteratedDeriv_airyKer_eq

/-- info: 'FormalResearch.Special.abs_airyD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_airyD_le

/-- info: 'FormalResearch.Special.iteratedDeriv_airyAi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.iteratedDeriv_airyAi_eq

end FormalResearch.Special

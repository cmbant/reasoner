module

public import FormalResearch.Special.AiryShiftTaylor
public import FormalResearch.Special.AiryParametrixTaylor

/-!
# Parametrix defect, part 2: a priori bounds and Taylor remainders of the exact shift functions

`C(X,s)`, `S(X,s)` of the Airy shift identity (`AiryShift`) solve `Y'' = (X+s) Y` with data `(1,0)`, `(0,1)`.
Put `u = 1 + |X|`.  For `|s| ≤ 1` and `|s| √u ≤ Λ`:

* `apx_lyapunov`: the Lyapunov function `Y² + Y'²/u` of a solution of `Y'' = (X+t)Y` grows at most like
  `exp(2 √u |t|)` on `|t| ≤ 1` (`|X+t| ≤ u`; Grönwall by monotonicity of `V · exp(∓2√u t)`);
* `apx_CS_bounds`: `|C| ≤ e^Λ`, `|C_s| ≤ √u e^Λ`, `|S| ≤ e^Λ/√u`, `|S_s| ≤ e^Λ` on the segment `[0, s]`;
* `apx_C_taylor`, `apx_S_taylor`: with `s = Δ`, the fifth-order Taylor polynomials
  `P₅ = 1 + XΔ²/2 + Δ³/6 + X²Δ⁴/24 + XΔ⁵/30` of `C` and `Δ + XΔ³/6 + Δ⁴/12 + X²Δ⁵/120` of `S` have
  remainders `≤ 11 e^Λ u³ |Δ|⁶` and `≤ 11 e^Λ u²√u |Δ|⁶`.

These use only the ODE (no envelope of `Ai`, no `X ≥ -1` restriction), so they hold on the oscillatory side
too; the polynomial growth in `u` (not small when `u ~ h^{-2/3}`) is the reason why the window-type defect
estimate (`AiryParametrixDefect`) carries the weight `h² (1+|X|)³`.  Proved; constants explicit.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **Lyapunov bound.**  If `y'' = (X+t) y` along `t ∈ [-1, 1]` then `V = y² + y'²/(1+|X|)` satisfies
`V(t) ≤ exp(2 √(1+|X|) |s|) V(0)` for `t ∈ [0, s]`, `|s| ≤ 1`. -/
lemma apx_lyapunov {X s : ℝ} {y y' : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : ∀ t, HasDerivAt y' ((X + t) * y t) t) (hs : |s| ≤ 1) :
    ∀ t ∈ uIcc 0 s, y t ^ 2 + y' t ^ 2 / (1 + |X|) ≤
      Real.exp (2 * √(1 + |X|) * |s|) * (y 0 ^ 2 + y' 0 ^ 2 / (1 + |X|)) := by
  set u : ℝ := 1 + |X| with hu
  have hu1 : 1 ≤ u := by have := abs_nonneg X; linarith
  have hu0 : 0 < u := by linarith
  set r : ℝ := √u with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hu0
  have hrr : r * r = u := Real.mul_self_sqrt hu0.le
  set V : ℝ → ℝ := fun t => y t ^ 2 + y' t ^ 2 / u with hV
  have hVd : ∀ t, HasDerivAt V (2 * y t * y' t + 2 * y' t * ((X + t) * y t) / u) t := by
    intro t
    have h1 := (hy t).pow 2
    have h2 := ((hy' t).pow 2).div_const u
    convert h1.add h2 using 1
    simp
  have hV0 : ∀ t, 0 ≤ V t := fun t => by positivity
  -- derivative bound on `|t| ≤ 1`
  have hVb : ∀ t, |t| ≤ 1 →
      |2 * y t * y' t + 2 * y' t * ((X + t) * y t) / u| ≤ 2 * r * V t := by
    intro t ht
    have hXt : |X + t| ≤ u := by
      have := abs_add_le X t; linarith
    have hAM : 2 * |y t| * (|y' t| / r) ≤ y t ^ 2 + y' t ^ 2 / u := by
      have : (|y t| - |y' t| / r) ^ 2 ≥ 0 := sq_nonneg _
      have e : (|y' t| / r) ^ 2 = y' t ^ 2 / u := by
        have hr2 : r ^ 2 = u := by rw [sq]; exact hrr
        rw [div_pow, sq_abs, hr2]
      nlinarith [sq_abs (y t)]
    have e1 : 2 * y t * y' t + 2 * y' t * ((X + t) * y t) / u =
        2 * y t * y' t * (1 + (X + t) / u) := by field_simp
    rw [e1, abs_mul, abs_mul, abs_mul]
    have h2 : |1 + (X + t) / u| ≤ 2 := by
      have : |(X + t) / u| ≤ 1 := by
        rw [abs_div, abs_of_pos hu0]; exact (div_le_one hu0).2 hXt
      calc |1 + (X + t) / u| ≤ |(1:ℝ)| + |(X + t) / u| := abs_add_le _ _
        _ ≤ 2 := by norm_num; linarith
    have h3 : |y t| * |y' t| ≤ r / 2 * V t := by
      have : |y' t| = r * (|y' t| / r) := by field_simp
      calc |y t| * |y' t| = r * (|y t| * (|y' t| / r)) := by
            conv_lhs => rw [this]
            ring
        _ ≤ r * ((y t ^ 2 + y' t ^ 2 / u) / 2) := by
            apply mul_le_mul_of_nonneg_left _ hr0.le; linarith
        _ = r / 2 * V t := by simp only [hV]; ring
    have h4 : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [h4]
    calc 2 * |y t| * |y' t| * |1 + (X + t) / u| ≤ 2 * (r / 2 * V t) * 2 := by
          apply mul_le_mul (by linarith) h2 (abs_nonneg _) (by nlinarith [hV0 t, hr0])
      _ = 2 * r * V t := by ring
  intro t ht
  rcases le_total 0 s with hs0 | hs0
  · -- forward: `V e^{-2 r t}` is nonincreasing on `[0, s]`
    rw [uIcc_of_le hs0] at ht
    set W : ℝ → ℝ := fun t => V t * Real.exp (-(2 * r * t)) with hW
    have hWd : ∀ t, HasDerivAt W
        ((2 * y t * y' t + 2 * y' t * ((X + t) * y t) / u) * Real.exp (-(2 * r * t)) +
          V t * (Real.exp (-(2 * r * t)) * (-(2 * r)))) t := by
      intro t
      have hE : HasDerivAt (fun t => Real.exp (-(2 * r * t))) (Real.exp (-(2 * r * t)) * (-(2 * r))) t := by
        simpa using (((hasDerivAt_id t).const_mul (2 * r)).neg.exp)
      exact (hVd t).mul hE
    have hanti : AntitoneOn W (Icc 0 s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
      · exact fun x _ => (hWd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hWd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hWd x).deriv]
        have hx1 : |x| ≤ 1 := by
          rw [abs_of_nonneg hx.1.le]
          have : |s| = s := abs_of_nonneg hs0
          linarith [hx.2]
        have := hVb x hx1
        have hE := Real.exp_pos (-(2 * r * x))
        have := (abs_le.1 this).2
        nlinarith [mul_nonneg hE.le (sub_nonneg.2 this)]
    have h1 := hanti ⟨le_refl _, hs0⟩ ⟨ht.1, ht.2⟩ ht.1
    have h2 : W t ≤ W 0 := hanti ⟨le_refl _, ht.1.trans ht.2⟩ ht ht.1
    simp only [hW, mul_zero, neg_zero, Real.exp_zero, mul_one] at h2
    have h5 : V t ≤ Real.exp (2 * r * t) * V 0 := by
      have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (2 * r * t)).le
      calc V t = Real.exp (2 * r * t) * (V t * Real.exp (-(2 * r * t))) := by
            rw [mul_left_comm, ← Real.exp_add]; simp
        _ ≤ _ := this
    have h6 : Real.exp (2 * r * t) ≤ Real.exp (2 * r * |s|) := by
      apply Real.exp_le_exp.2
      rw [abs_of_nonneg hs0]; nlinarith [ht.2]
    calc V t ≤ Real.exp (2 * r * t) * V 0 := h5
      _ ≤ Real.exp (2 * r * |s|) * V 0 := mul_le_mul_of_nonneg_right h6 (hV0 0)
  · -- backward: `V e^{2 r t}` is nondecreasing on `[s, 0]`
    rw [uIcc_of_ge hs0] at ht
    set W : ℝ → ℝ := fun t => V t * Real.exp (2 * r * t) with hW
    have hWd : ∀ t, HasDerivAt W
        ((2 * y t * y' t + 2 * y' t * ((X + t) * y t) / u) * Real.exp (2 * r * t) +
          V t * (Real.exp (2 * r * t) * (2 * r))) t := by
      intro t
      have hE : HasDerivAt (fun t => Real.exp (2 * r * t)) (Real.exp (2 * r * t) * (2 * r)) t := by
        simpa using (((hasDerivAt_id t).const_mul (2 * r)).exp)
      exact (hVd t).mul hE
    have hmono : MonotoneOn W (Icc s 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc s 0)
      · exact fun x _ => (hWd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hWd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hWd x).deriv]
        have hx1 : |x| ≤ 1 := by
          rw [abs_of_nonpos hx.2.le]
          have : |s| = -s := abs_of_nonpos hs0
          linarith [hx.1]
        have := hVb x hx1
        have hE := Real.exp_pos (2 * r * x)
        have := (abs_le.1 this).1
        nlinarith [mul_nonneg hE.le (by linarith : 0 ≤ (2 * y x * y' x +
          2 * y' x * ((X + x) * y x) / u) + 2 * r * V x)]
    have h2 : W t ≤ W 0 := hmono ht (⟨hs0, le_refl _⟩) ht.2
    simp only [hW, mul_zero, Real.exp_zero, mul_one] at h2
    have h5 : V t ≤ Real.exp (-(2 * r * t)) * V 0 := by
      have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(2 * r * t))).le
      calc V t = Real.exp (-(2 * r * t)) * (V t * Real.exp (2 * r * t)) := by
            rw [mul_left_comm, ← Real.exp_add]; simp
        _ ≤ _ := this
    have h6 : Real.exp (-(2 * r * t)) ≤ Real.exp (2 * r * |s|) := by
      apply Real.exp_le_exp.2
      rw [abs_of_nonpos hs0]; nlinarith [ht.1]
    calc V t ≤ Real.exp (-(2 * r * t)) * V 0 := h5
      _ ≤ Real.exp (2 * r * |s|) * V 0 := mul_le_mul_of_nonneg_right h6 (hV0 0)

/-- **A priori bounds for `C`, `S`** on the segment: `|C| ≤ e^Λ`, `|C_s| ≤ √u e^Λ`, `|S| ≤ e^Λ/√u`,
`|S_s| ≤ e^Λ` (`u = 1 + |X|`, `|s| ≤ 1`, `|s| √u ≤ Λ`). -/
theorem apx_CS_bounds {X s Λ : ℝ} (hs : |s| ≤ 1) (hΛ : |s| * √(1 + |X|) ≤ Λ) :
    ∀ t ∈ uIcc 0 s, |airyShiftC X t| ≤ Real.exp Λ ∧
      |airyShiftCd X t| ≤ √(1 + |X|) * Real.exp Λ ∧
      |airyShiftS X t| ≤ Real.exp Λ / √(1 + |X|) ∧ |airyShiftSd X t| ≤ Real.exp Λ := by
  intro t ht
  have hu0 : 0 < 1 + |X| := by positivity
  have hr0 : 0 < √(1 + |X|) := Real.sqrt_pos.mpr hu0
  have hrr : √(1 + |X|) * √(1 + |X|) = 1 + |X| := Real.mul_self_sqrt hu0.le
  have hE : Real.exp (2 * √(1 + |X|) * |s|) ≤ Real.exp (Λ + Λ) := by
    apply Real.exp_le_exp.2; nlinarith
  have hee : Real.exp (Λ + Λ) = Real.exp Λ ^ 2 := by rw [sq, ← Real.exp_add]
  have hE0 := Real.exp_pos Λ
  obtain ⟨i1, i2, i3, i4⟩ := airyShift_initial X
  have hC := apx_lyapunov (X := X) (s := s) (fun t => hasDerivAt_airyShiftC X t)
    (fun t => hasDerivAt_airyShiftCd X t) hs t ht
  have hS := apx_lyapunov (X := X) (s := s) (fun t => hasDerivAt_airyShiftS X t)
    (fun t => hasDerivAt_airyShiftSd X t) hs t ht
  rw [i1, i2] at hC
  rw [i3, i4] at hS
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero,
    one_pow, one_div, zero_add] at hC hS
  have hu : (1 + |X|)⁻¹ * 1 ≤ 1 := by
    rw [mul_one]; exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg X])
  -- bounds
  have hCV : airyShiftC X t ^ 2 + airyShiftCd X t ^ 2 / (1 + |X|) ≤ Real.exp Λ ^ 2 := by
    have : Real.exp (2 * √(1 + |X|) * |s|) * (1 + 0 / (1 + |X|)) ≤ Real.exp Λ ^ 2 := by
      simp only [zero_div, add_zero, mul_one]; rw [← hee]; exact hE
    simpa using hC.trans (by simpa using this)
  have hSV : airyShiftS X t ^ 2 + airyShiftSd X t ^ 2 / (1 + |X|) ≤ Real.exp Λ ^ 2 / (1 + |X|) := by
    have h1 : Real.exp (2 * √(1 + |X|) * |s|) * (0 + 1 ^ 2 / (1 + |X|)) ≤
        Real.exp Λ ^ 2 / (1 + |X|) := by
      rw [zero_add, one_pow, ← mul_div_assoc, mul_one]
      exact div_le_div_of_nonneg_right (by rw [← hee]; exact hE) hu0.le
    simpa using hS.trans (by simpa using h1)
  have a1 : airyShiftC X t ^ 2 ≤ Real.exp Λ ^ 2 := by
    have := div_nonneg (sq_nonneg (airyShiftCd X t)) hu0.le
    linarith
  have a2 : airyShiftCd X t ^ 2 ≤ (√(1 + |X|) * Real.exp Λ) ^ 2 := by
    have h := div_nonneg (sq_nonneg (airyShiftC X t)) hu0.le
    have h2 : airyShiftCd X t ^ 2 / (1 + |X|) ≤ Real.exp Λ ^ 2 := by nlinarith [sq_nonneg (airyShiftC X t)]
    rw [div_le_iff₀ hu0] at h2
    rw [mul_pow, sq (√(1 + |X|)), hrr]; linarith
  have a3 : airyShiftS X t ^ 2 ≤ (Real.exp Λ / √(1 + |X|)) ^ 2 := by
    have := div_nonneg (sq_nonneg (airyShiftSd X t)) hu0.le
    rw [div_pow, sq (√(1 + |X|)), hrr]; linarith
  have a4 : airyShiftSd X t ^ 2 ≤ Real.exp Λ ^ 2 := by
    have h2 : airyShiftSd X t ^ 2 / (1 + |X|) ≤ Real.exp Λ ^ 2 / (1 + |X|) := by
      linarith [sq_nonneg (airyShiftS X t)]
    rwa [div_le_div_iff_of_pos_right hu0] at h2
  exact ⟨abs_le_of_sq_le_sq a1 hE0.le, abs_le_of_sq_le_sq a2 (by positivity),
    abs_le_of_sq_le_sq a3 (by positivity), abs_le_of_sq_le_sq a4 hE0.le⟩

/-- Elementary: `|X+t| ≤ 1 + |X|` for `|t| ≤ 1`. -/
lemma apx_abs_add_le {X t : ℝ} (ht : |t| ≤ 1) : |X + t| ≤ 1 + |X| := by
  have := abs_add_le X t; linarith

lemma apx_abs_of_mem_uIcc {s t : ℝ} (ht : t ∈ uIcc 0 s) : |t| ≤ |s| := abs_le_abs_of_mem_uIcc ht

/-- **Fifth-order Taylor remainder of `C`**: for `|s| ≤ 1`, `|s| √(1+|X|) ≤ Λ`,
`|C(X,s) - (1 + X s²/2 + s³/6 + X² s⁴/24 + X s⁵/30)| ≤ 11 e^Λ (1+|X|)³ |s|⁶`. -/
theorem apx_C_taylor {X s Λ : ℝ} (hs : |s| ≤ 1) (hΛ : |s| * √(1 + |X|) ≤ Λ) :
    |airyShiftC X s - (1 + X * s ^ 2 / 2 + s ^ 3 / 6 + X ^ 2 * s ^ 4 / 24 + X * s ^ 5 / 30)| ≤
      11 * Real.exp Λ * (1 + |X|) ^ 3 * |s| ^ 6 := by
  have hu0 : 1 ≤ 1 + |X| := by linarith [abs_nonneg X]
  set u : ℝ := 1 + |X| with hu
  have hr1 : 1 ≤ √u := by rw [Real.one_le_sqrt]; exact hu0
  have hrr : √u * √u = u := Real.mul_self_sqrt (by linarith)
  have hru : √u ≤ u := by nlinarith
  have hE0 := Real.exp_pos Λ
  refine airyShiftC_taylor X s _ (fun t ht => ?_)
  have htt : |t| ≤ 1 := (apx_abs_of_mem_uIcc ht).trans hs
  obtain ⟨b1, b2, -, -⟩ := apx_CS_bounds hs hΛ t ht
  have hXt : |X + t| ≤ u := apx_abs_add_le htt
  have hc3 : |(X + t) ^ 3 + 4| ≤ 5 * u ^ 3 := by
    calc |(X + t) ^ 3 + 4| ≤ |(X + t) ^ 3| + |(4:ℝ)| := abs_add_le _ _
      _ ≤ u ^ 3 + 4 := by
          rw [abs_pow]; norm_num; exact pow_le_pow_left₀ (abs_nonneg _) hXt 3
      _ ≤ 5 * u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu0 3]
  calc |((X + t) ^ 3 + 4) * airyShiftC X t + 6 * (X + t) * airyShiftCd X t|
      ≤ |((X + t) ^ 3 + 4) * airyShiftC X t| + |6 * (X + t) * airyShiftCd X t| := abs_add_le _ _
    _ = |(X + t) ^ 3 + 4| * |airyShiftC X t| + 6 * |X + t| * |airyShiftCd X t| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
    _ ≤ 5 * u ^ 3 * Real.exp Λ + 6 * u * (√u * Real.exp Λ) := by
        gcongr
    _ ≤ 11 * Real.exp Λ * u ^ 3 := by
        have : u * √u ≤ u ^ 3 := by
          have : u ≤ u ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hru (by linarith : (0:ℝ) ≤ u)]
        nlinarith [mul_le_mul_of_nonneg_right this hE0.le]

/-- **Fifth-order Taylor remainder of `S`**:
`|S(X,s) - (s + X s³/6 + s⁴/12 + X² s⁵/120)| ≤ 11 e^Λ (1+|X|)² √(1+|X|) |s|⁶`. -/
theorem apx_S_taylor {X s Λ : ℝ} (hs : |s| ≤ 1) (hΛ : |s| * √(1 + |X|) ≤ Λ) :
    |airyShiftS X s - (s + X * s ^ 3 / 6 + s ^ 4 / 12 + X ^ 2 * s ^ 5 / 120)| ≤
      11 * Real.exp Λ * ((1 + |X|) ^ 2 * √(1 + |X|)) * |s| ^ 6 := by
  have hu0 : 1 ≤ 1 + |X| := by linarith [abs_nonneg X]
  set u : ℝ := 1 + |X| with hu
  have hr1 : 1 ≤ √u := by rw [Real.one_le_sqrt]; exact hu0
  have hrr : √u * √u = u := Real.mul_self_sqrt (by linarith)
  have hE0 := Real.exp_pos Λ
  refine airyShiftS_taylor X s _ (fun t ht => ?_)
  have htt : |t| ≤ 1 := (apx_abs_of_mem_uIcc ht).trans hs
  obtain ⟨-, -, b3, b4⟩ := apx_CS_bounds hs hΛ t ht
  have hXt : |X + t| ≤ u := apx_abs_add_le htt
  have hc3 : |(X + t) ^ 3 + 4| ≤ 5 * u ^ 3 := by
    calc |(X + t) ^ 3 + 4| ≤ |(X + t) ^ 3| + |(4:ℝ)| := abs_add_le _ _
      _ ≤ u ^ 3 + 4 := by
          rw [abs_pow]; norm_num; exact pow_le_pow_left₀ (abs_nonneg _) hXt 3
      _ ≤ 5 * u ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu0 3]
  calc |((X + t) ^ 3 + 4) * airyShiftS X t + 6 * (X + t) * airyShiftSd X t|
      ≤ |((X + t) ^ 3 + 4) * airyShiftS X t| + |6 * (X + t) * airyShiftSd X t| := abs_add_le _ _
    _ = |(X + t) ^ 3 + 4| * |airyShiftS X t| + 6 * |X + t| * |airyShiftSd X t| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
    _ ≤ 5 * u ^ 3 * (Real.exp Λ / √u) + 6 * u * Real.exp Λ := by
        gcongr
    _ ≤ 11 * Real.exp Λ * (u ^ 2 * √u) := by
        have e1 : u ^ 3 / √u = u ^ 2 * √u := by
          field_simp; nlinarith [hrr]
        have e2 : 5 * u ^ 3 * (Real.exp Λ / √u) = 5 * Real.exp Λ * (u ^ 3 / √u) := by ring
        have h3 : u ≤ u ^ 2 * √u := by
          have : u ≤ u ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hr1 (by positivity : (0:ℝ) ≤ u ^ 2)]
        rw [e2, e1]
        nlinarith [mul_le_mul_of_nonneg_right h3 hE0.le]

end FormalResearch.Special

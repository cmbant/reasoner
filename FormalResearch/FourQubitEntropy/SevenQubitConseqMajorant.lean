import Mathlib

/-!
# A quadratic majorant of `-x ln x` (Hermite, double contact at `b`)

For `0 < b ≤ a` put `f = negMulLog`, `T(x) = f b + f'(b)(x - b)` and `c = (f a - T a)/(a - b)²`
(`c = 0` when `a = b`).  Then `f x ≤ T x + c (x - b)²` for every `x ∈ [0, a]`, with equality at
`x = a` and `x = b`.

Proof.  `u(y) = f y - T y + (y-b)²/(2b)` has `u' = ln(b/y) + y/b - 1 ≥ 0`, so `u ≤ 0` on `[0,b]`
and `u ≥ 0` on `[b,∞)`; hence `c ≥ -1/(2b)` and `f x ≤ T x - (x-b)²/(2b) ≤ T x + c(x-b)²` for
`x ≤ b`.  For `x ∈ (b,a]` the second divided difference `ρ(y) = (f y - T y)/(y-b)²` is increasing
on `(b,∞)`: `ρ' = N/(y-b)³` with `N = (y+b) ln(y/b) - 2(y-b)` and `N' = ln(y/b) + b/y - 1 ≥ 0`.
-/

open Real

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- The tangent line of `negMulLog` at `b`. -/
noncomputable def tang (b x : ℝ) : ℝ := negMulLog b + (-log b - 1) * (x - b)

/-- `f - T`. -/
noncomputable def rem (b x : ℝ) : ℝ := negMulLog x - tang b x

theorem rem_at (b : ℝ) : rem b b = 0 := by simp [rem, tang]

theorem hasDerivAt_rem {b y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (rem b) (log b - log y) y := by
  have h1 := Real.hasDerivAt_negMulLog hy
  have h2 : HasDerivAt (fun x => tang b x) (-log b - 1) y := by
    have := (((hasDerivAt_id y).sub_const b).const_mul (-log b - 1)).const_add (negMulLog b)
    simpa [tang] using this
  exact (h1.sub h2).congr_deriv (by ring)

/-- `u(y) = f y - T y + (y-b)²/(2b)`. -/
noncomputable def uf (b y : ℝ) : ℝ := rem b y + (y - b) ^ 2 / (2 * b)

theorem hasDerivAt_uf {b y : ℝ} (hb : 0 < b) (hy : y ≠ 0) :
    HasDerivAt (uf b) (log b - log y + (y / b - 1)) y := by
  have h3 : HasDerivAt (fun y => (y - b) ^ 2 / (2 * b)) (y / b - 1) y := by
    have := (((hasDerivAt_id y).sub_const b).pow 2).div_const (2 * b)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  exact (hasDerivAt_rem hy).add h3

/-- `u` is nondecreasing on `[0,∞)`. -/
theorem u_mono {b : ℝ} (hb : 0 < b) : MonotoneOn (uf b) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · apply Continuous.continuousOn
    unfold uf rem tang
    fun_prop
  · intro y hy
    rw [interior_Ici] at hy
    exact (hasDerivAt_uf hb (ne_of_gt hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := hy
    rw [(hasDerivAt_uf hb hy0.ne').deriv]
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hb)
    rw [Real.log_div hy0.ne' hb.ne'] at this
    linarith

theorem rem_le_of_le {b x : ℝ} (hb : 0 < b) (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    rem b x ≤ -((x - b) ^ 2 / (2 * b)) := by
  have h := u_mono hb (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 hb.le) hxb
  have h0 : rem b b = 0 := rem_at b
  simp only [uf, h0, sub_self] at h
  simp at h
  linarith

theorem rem_ge_of_ge {b x : ℝ} (hb : 0 < b) (hxb : b ≤ x) :
    -((x - b) ^ 2 / (2 * b)) ≤ rem b x := by
  have h := u_mono hb (Set.mem_Ici.2 hb.le) (Set.mem_Ici.2 (hb.le.trans hxb)) hxb
  have h0 : rem b b = 0 := rem_at b
  simp only [uf, h0, sub_self] at h
  simp at h
  linarith

/-- The Hermite coefficient. -/
noncomputable def hc (a b : ℝ) : ℝ := rem b a / (a - b) ^ 2

theorem hc_ge {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) : -(1 / (2 * b)) ≤ hc a b := by
  rcases hba.eq_or_lt with h | h
  · subst h
    simp only [hc, sub_self]
    simp
    positivity
  · unfold hc
    have h1 := rem_ge_of_ge hb hba
    have hp : 0 < (a - b) ^ 2 := by positivity
    rw [le_div_iff₀ hp]
    have : -(1 / (2 * b)) * (a - b) ^ 2 = -((a - b) ^ 2 / (2 * b)) := by field_simp
    linarith

/-- The numerator `N(y) = (y+b) ln(y/b) - 2(y-b)`: `ρ' = N/(y-b)³`. -/
noncomputable def Nn (b y : ℝ) : ℝ := (y + b) * (log y - log b) - 2 * (y - b)

theorem Nn_nonneg {b y : ℝ} (hb : 0 < b) (hy : b ≤ y) : 0 ≤ Nn b y := by
  have hmono : MonotoneOn (Nn b) (Set.Ici b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
    · apply ContinuousOn.sub
      · apply ContinuousOn.mul (by fun_prop)
        apply ContinuousOn.sub
        · exact Real.continuousOn_log.mono (fun y hy => ne_of_gt (lt_of_lt_of_le hb hy))
        · exact continuousOn_const
      · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0 : ℝ) < y := hb.trans hy
      have := (((hasDerivAt_id y).add_const b).mul (((Real.hasDerivAt_log hy0.ne').sub_const (log b)))).sub
        (((hasDerivAt_id y).sub_const b).const_mul 2)
      exact this.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0 : ℝ) < y := hb.trans hy
      have hd := (((hasDerivAt_id y).add_const b).mul (((Real.hasDerivAt_log hy0.ne').sub_const (log b)))).sub
        (((hasDerivAt_id y).sub_const b).const_mul 2)
      have hd' : HasDerivAt (Nn b) (1 * (log y - log b) + (id y + b) * y⁻¹ - 2 * 1) y := by
        unfold Nn; exact hd
      rw [hd'.deriv]
      have := Real.one_sub_inv_le_log_of_pos (div_pos hy0 hb)
      rw [Real.log_div hy0.ne' hb.ne'] at this
      simp only [id]
      have e : (1 * (log y - log b) + (y + b) * (y⁻¹)) - 2 * (1) = (log y - log b) + b / y - 1 := by
        field_simp; ring
      have e2 : 1 - (y / b)⁻¹ = 1 - b / y := by rw [inv_div]
      rw [e2] at this
      have : (log y - log b) + b / y - 1 ≥ 0 := by
        have h3 : b / y ≤ 1 := by rw [div_le_one hy0]; exact hy.le
        have h4 := Real.log_le_sub_one_of_pos (div_pos hb hy0)
        rw [Real.log_div hb.ne' hy0.ne'] at h4
        linarith
      simp at *
      nlinarith [this]
  have h0 : Nn b b = 0 := by simp [Nn]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  rw [h0] at this
  exact this

theorem rho_mono {b : ℝ} (hb : 0 < b) :
    MonotoneOn (fun y => rem b y / (y - b) ^ 2) (Set.Ioi b) := by
  have hd : ∀ y ∈ Set.Ioi b, HasDerivAt (fun y => rem b y / (y - b) ^ 2)
      (((log b - log y) * (y - b) ^ 2 - rem b y * (2 * (y - b))) / ((y - b) ^ 2) ^ 2) y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hb.trans hy
    have hyb : y - b ≠ 0 := sub_ne_zero.2 (ne_of_gt hy)
    have h2 : HasDerivAt (fun y => (y - b) ^ 2) (2 * (y - b)) y := by
      have := ((hasDerivAt_id y).sub_const b).pow 2
      refine this.congr_deriv ?_
      simp
    exact (hasDerivAt_rem hy0.ne').div h2 (pow_ne_zero 2 hyb)
  apply monotoneOn_of_deriv_nonneg (convex_Ioi b)
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hd y hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hd y hy).deriv]
    have hy0 : (0 : ℝ) < y := hb.trans hy
    have hyb : 0 < y - b := sub_pos.2 hy
    have hN := Nn_nonneg hb hy.le
    apply div_nonneg _ (by positivity)
    have e : (log b - log y) * (y - b) ^ 2 - rem b y * (2 * (y - b)) = (y - b) * Nn b y := by
      simp only [rem, tang, Nn, negMulLog]
      ring
    rw [e]
    exact mul_nonneg hyb.le hN

/-- **Hermite majorant** of `-x ln x` with double contact at `b`, valid on `[0, a]`, `0 < b ≤ a`. -/
theorem majorant {a b x : ℝ} (hb : 0 < b) (hba : b ≤ a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    negMulLog x ≤ tang b x + hc a b * (x - b) ^ 2 := by
  have key : rem b x ≤ hc a b * (x - b) ^ 2 := by
    rcases le_or_gt x b with hxb | hxb
    · have h1 := rem_le_of_le hb hx0 hxb
      have h2 := hc_ge hb hba
      have : -(1 / (2 * b)) * (x - b) ^ 2 ≤ hc a b * (x - b) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      have e : -(1 / (2 * b)) * (x - b) ^ 2 = -((x - b) ^ 2 / (2 * b)) := by field_simp
      linarith
    · have hmono := rho_mono hb (Set.mem_Ioi.2 hxb) (Set.mem_Ioi.2 (hxb.trans_le hxa)) hxa
      have hp : 0 < (x - b) ^ 2 := by have := sub_pos.2 hxb; positivity
      have : rem b x / (x - b) ^ 2 ≤ hc a b := hmono
      rw [div_le_iff₀ hp] at this
      exact this
  unfold rem at key
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq

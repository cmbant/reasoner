module

public import FormalResearch.Special.AiryAsymPos
public import FormalResearch.Special.AiryReal
public import FormalResearch.Asymptotics.RiccatiBarrier
public import FormalResearch.Special.AiryCftMittagLeffler

/-!
# Three-term asymptotics of `Ai'/Ai` on the positive axis, and the two-term sum rule

For `x ≥ 1` let `G = -Ai'/Ai` (`riccG`).  It satisfies the Riccati equation `G' = G² - x` (`hasDerivAt_riccG`) and the
a priori bound `|G - √x| ≤ (22/43)/x` (`riccG_sub_sqrt_le`, from `AiryAsymPos`).  With the formal series
`g₃ = 1/(4x) - 5/(32 x^{5/2})` (`riccG3`) the error `e = G - √x - g₃` solves the linear equation `e' = p e - r`,
`p = √x + G + g₃ ≥ √x`, `r = (15/32) x^{-7/2} - (25/1024) x^{-5}` (`hasDerivAt_riccE`), and the barrier lemma
`abs_le_of_riccati_barrier` (`FormalResearch.Asymptotics.RiccatiBarrier`) with `ρ = x^{-4}` gives (proved)

* **`riccG_threeTerm`**: `|G - √x - 1/(4x) + 5/(32 x^{5/2})| ≤ x^{-4}` for `x ≥ 1`;
* **`airy_sq_sub_x_asymp`**: `|(Ai'/Ai)² - x - 1/(2√x) + 1/(4x²)| ≤ 5 x^{-7/2}` for `x ≥ 1`;
* **`airy_zero_sum_asymp`**: combined with the Hadamard sum rule `airyAi_sq_series_real`,
  `Σ_n (x + m_n)^{-2} = 1/(2√x) - 1/(4x²) + O(x^{-7/2})` for `m_n = -a_{n+1}`.

All constants are explicit and not optimal.  No phase and no Paper II object enters; the only inputs are the Airy
equation, the leading bounds of `AiryAsymPos` and the sum rule.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The logarithmic derivative `G = -Ai'/Ai` on the positive axis. -/
noncomputable def riccG (x : ℝ) : ℝ := -airyAi' x / airyAi x

/-- A priori bound `|G - √x| ≤ (22/43)/x` for `x ≥ 1` (from the two-sided bounds of `AiryAsymPos`). -/
theorem riccG_sub_sqrt_le {x : ℝ} (hx : 1 ≤ x) : |riccG x - √x| ≤ 22 / 43 / x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hT : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h1 := airyAi_sub_leading_le hx0
  have h2 := airyAi'_add_leading_le hx0
  set u : ℝ := x ^ (-(1 / 4) : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (1 / 4 : ℝ) = u * √x := by
    rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
  have e2 : x ^ (-(5 / 4) : ℝ) = u / x := by
    rw [show (-(5 / 4) : ℝ) = -(1 / 4) + (-1) by norm_num, Real.rpow_add hx0, Real.rpow_neg_one, hu]; ring
  have e3 : x ^ (3 / 2 : ℝ) = x * √x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by norm_num)]; norm_num
  set E : ℝ := Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rw [e1] at h2
  rw [e2] at h2
  rw [e3] at h1
  set A := airyAi x with hA
  set B := airyAi' x with hB
  set P : ℝ := 1 / (2 * √π) * u * E with hP
  have hP0 : 0 < P := by positivity
  have hxs : 0 < x * √x := by positivity
  have h1' : |A - P| ≤ 5 / 48 / (x * √x) * P := h1
  have h2' : |B + √x * P| ≤ 17 / 48 / x * P := by
    have e : |B + √x * P| = |B + 1 / (2 * √π) * (u * √x) * E| := congrArg abs (by rw [hP]; ring)
    rw [e]
    refine h2.trans (le_of_eq ?_)
    rw [hP]; field_simp; ring
  -- G - √x = (-B - √x A)/A
  have hAp : 43 / 48 * P ≤ A := by
    have := (abs_le.mp h1').1
    have h3 : 5 / 48 / (x * √x) ≤ 5 / 48 := by
      rw [div_le_iff₀ hxs]; nlinarith only [hx, hs1, hss]
    nlinarith only [this, h3, hP0]
  have hA0 : 0 < A := by linarith
  have hnum : |-B - √x * A| ≤ 22 / 48 / x * P := by
    have a1 := abs_le.mp h1'
    have a2 := abs_le.mp h2'
    have h3 : √x * (5 / 48 / (x * √x)) = 5 / 48 / x := by field_simp
    have h4 : √x * (5 / 48 / (x * √x) * P) = 5 / 48 / x * P := by rw [← mul_assoc, h3]
    have b1 := mul_le_mul_of_nonneg_left a1.2 hs.le
    have b2 := mul_le_mul_of_nonneg_left a1.1 hs.le
    have h5 : √x * (-(5 / 48 / (x * √x) * P)) = -(5 / 48 / x * P) := by rw [mul_neg, h4]
    have h6 : 22 / 48 / x * P = 17 / 48 / x * P + 5 / 48 / x * P := by ring
    rw [abs_le]
    constructor
    · rw [h5] at b2
      nlinarith only [b1, b2, a2.1, a2.2, h4, h6]
    · rw [h5] at b2
      nlinarith only [b1, b2, a2.1, a2.2, h4, h6]
  unfold riccG
  have : -airyAi' x / airyAi x - √x = (-B - √x * A) / A := by
    rw [← hA, ← hB]; field_simp
  rw [this, abs_div, abs_of_pos hA0, div_le_iff₀ hA0]
  calc |-B - √x * A| ≤ 22 / 48 / x * P := hnum
    _ ≤ 22 / 43 / x * A := by
      have : 22 / 48 / x * P ≤ 22 / 43 / x * (43 / 48 * P) := by
        apply le_of_eq; field_simp
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_left hAp (by positivity)

/-- Derivative of `G`: the Riccati equation `G' = G² - x` (from `Ai'' = x Ai`). -/
theorem hasDerivAt_riccG {x : ℝ} (hx : 1 ≤ x) : HasDerivAt riccG (riccG x ^ 2 - x) x := by
  have hA : airyAi x ≠ 0 := (airyAi_pos (by linarith)).ne'
  have h := (hasDerivAt_airyAi' x).neg.div (hasDerivAt_airyAi x) hA
  unfold riccG
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- The three-term formal part `1/(4x) - 5/(32 x^{5/2})` of `G - √x`. -/
noncomputable def riccG3 (x : ℝ) : ℝ := 1 / (4 * x) - 5 / (32 * (x ^ 2 * √x))

/-- Its derivative. -/
noncomputable def riccG3d (x : ℝ) : ℝ := -1 / (4 * x ^ 2) + 25 / (64 * (x ^ 3 * √x))

theorem hasDerivAt_riccG3 {x : ℝ} (hx : 0 < x) : HasDerivAt riccG3 (riccG3d x) x := by
  have hs : 0 < √x := Real.sqrt_pos.mpr hx
  have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 * √y) (2 * x * √x + x ^ 2 * (1 / (2 * √x))) x := by
    have := (hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sqrt hx.ne')
    refine this.congr_deriv ?_
    simp
  have h3 := h2.inv (by positivity)
  have h4 := (h1.const_mul (1 / 4 : ℝ)).sub (h3.const_mul (5 / 32 : ℝ))
  have e : riccG3 = fun y : ℝ => 1 / 4 * y⁻¹ - 5 / 32 * (y ^ 2 * √y)⁻¹ := by
    funext y; unfold riccG3; field_simp
  rw [e]
  refine h4.congr_deriv ?_
  unfold riccG3d
  have hss : x = √x ^ 2 := (Real.sq_sqrt hx.le).symm
  generalize √x = s at hs hss ⊢
  subst hss
  field_simp
  ring

/-- The algebraic identity behind the Riccati error equation. -/
lemma airy_riccati_alg {x s : ℝ} (hs : 0 < s) (hx : x = s ^ 2) :
    15 / (32 * (x ^ 3 * s)) - 25 / (1024 * x ^ 5) =
      riccG3d x + 1 / (2 * s) - 2 * s * (1 / (4 * x) - 5 / (32 * (x ^ 2 * s))) -
        (1 / (4 * x) - 5 / (32 * (x ^ 2 * s))) ^ 2 := by
  have hsq : √x = s := by rw [hx]; exact Real.sqrt_sq hs.le
  unfold riccG3d
  rw [hsq]
  subst hx
  field_simp
  ring

/-- The error `e = G - √x - g₃` of the three-term formal series. -/
noncomputable def riccE (x : ℝ) : ℝ := riccG x - √x - riccG3 x

/-- The coefficient `p = 2√x + (G - √x) + g₃` of the linear error equation. -/
noncomputable def riccP (x : ℝ) : ℝ := √x + riccG x + riccG3 x

/-- The residual of the formal series. -/
noncomputable def riccR (x : ℝ) : ℝ := 15 / (32 * (x ^ 3 * √x)) - 25 / (1024 * x ^ 5)

theorem hasDerivAt_riccE {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt riccE (riccP x * riccE x - riccR x) x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have h := ((hasDerivAt_riccG hx).sub (Real.hasDerivAt_sqrt hx0.ne')).sub (hasDerivAt_riccG3 hx0)
  refine h.congr_deriv ?_
  have halg := airy_riccati_alg (x := x) hs (by rw [sq]; exact hss.symm)
  unfold riccP riccE riccR
  rw [halg]
  unfold riccG3
  linear_combination hss

theorem riccG3_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ riccG3 x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
  have : riccG3 x = (8 * x * √x - 5) / (32 * x ^ 2 * √x) := by unfold riccG3; field_simp; ring
  rw [this]
  apply div_nonneg (by nlinarith only [hx, hs1]) (by positivity)

theorem riccG3_le {x : ℝ} (hx : 1 ≤ x) : riccG3 x ≤ 1 / (4 * x) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  unfold riccG3
  have : 0 < 5 / (32 * (x ^ 2 * √x)) := by positivity
  linarith

/-- **Three-term asymptotics of `Ai'/Ai`** on the positive axis (DLMF 9.7.5-9.7.6, quantitative):
`|Ai'(x)/Ai(x) + √x + 1/(4x) - 5/(32 x^{5/2})| ≤ x^{-4}` for `x ≥ 1`.  Proof: the Riccati equation `G' = G² - x` for
`G = -Ai'/Ai` and the barrier lemma of `RiccatiBarrier`, starting from the a priori bound `riccG_sub_sqrt_le`. -/
theorem riccG_threeTerm {x : ℝ} (hx : 1 ≤ x) : |riccE x| ≤ 1 / x ^ 4 := by
  have key := FormalResearch.Asymptotics.abs_le_of_riccati_barrier (e := riccE)
    (e' := fun x => riccP x * riccE x - riccR x) (p := riccP) (r := riccR)
    (ρ := fun x => 1 / x ^ 4) (ρ' := fun x => -4 / x ^ 5) (x0 := 1) (M := 1)
    (fun x hx => hasDerivAt_riccE hx)
    (fun x hx => by
      have hx0 : 0 < x := by linarith
      have := (hasDerivAt_pow 4 x).inv (by positivity)
      have e1 : (fun y : ℝ => 1 / y ^ 4) = fun y => (y ^ 4)⁻¹ := by funext y; simp
      rw [e1]
      refine this.congr_deriv ?_
      field_simp
      norm_num
      ring)
    (fun x hx => by positivity)
    (fun x hx => by
      have hx0 : 0 < x := by linarith
      have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
      have h1 := riccG_sub_sqrt_le hx
      have h2 : 22 / 43 / x ≤ 22 / 43 := by
        rw [div_le_iff₀ hx0]; nlinarith only [hx]
      have h3 := (abs_le.mp h1).1
      have h4 := riccG3_nonneg hx
      unfold riccP
      linarith only [hs1, h3, h2, h4])
    (fun x hx => by
      have hx0 : 0 < x := by linarith
      have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
      have h1 := riccG_sub_sqrt_le hx
      have h2 : 22 / 43 / x ≤ 22 / 43 := by
        rw [div_le_iff₀ hx0]; nlinarith only [hx]
      have h3 := (abs_le.mp h1).1
      have h4 := riccG3_nonneg hx
      have hpc : ContinuousAt riccG x := (hasDerivAt_riccG hx).continuousAt
      have hsc : ContinuousAt (fun y : ℝ => √y) x := (Real.hasDerivAt_sqrt hx0.ne').continuousAt
      have hgc : ContinuousAt riccG3 x := (hasDerivAt_riccG3 hx0).continuousAt
      exact (hsc.add hpc).add hgc)
    (fun x hx => rfl)
    (fun x hx => by
      have hx0 : 0 < x := by linarith
      have hs : 0 < √x := Real.sqrt_pos.mpr hx0
      have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
      have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
      have h1 := riccG_sub_sqrt_le hx
      have h2 : 22 / 43 / x ≤ 22 / 43 := by
        rw [div_le_iff₀ hx0]; nlinarith only [hx]
      have h3 := (abs_le.mp h1).1
      have h4 := riccG3_nonneg hx
      have hp : √x ≤ riccP x := by unfold riccP; linarith only [hs1, h3, h2, h4]
      have hρ : 0 ≤ 1 / x ^ 4 := by positivity
      have hpρ := mul_le_mul_of_nonneg_right hp hρ
      have hA : 15 / (32 * (x ^ 3 * √x)) ≤ √x * (1 / x ^ 4) := by
        have : √x * (1 / x ^ 4) = 1 / (x ^ 3 * √x) := by
          field_simp; nlinarith only [hss]
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [pow_pos hx0 3, hs]
      have hB : 25 / (1024 * x ^ 5) ≤ 4 / x ^ 5 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [pow_pos hx0 5]
      have hA0 : 0 ≤ 15 / (32 * (x ^ 3 * √x)) := by positivity
      have hB0 : 0 ≤ 25 / (1024 * x ^ 5) := by positivity
      have e4 : -4 / x ^ 5 = -(4 / x ^ 5) := by ring
      show |riccR x| ≤ riccP x * (1 / x ^ 4) - -4 / x ^ 5
      rw [e4, sub_neg_eq_add]
      unfold riccR
      rw [abs_le]
      constructor <;> linarith only [hpρ, hA, hB, hA0, hB0, hρ, hs])
    (fun x hx => by
      have hx0 : 0 < x := by linarith
      have h1 := riccG_sub_sqrt_le hx
      have h2 : 22 / 43 / x ≤ 22 / 43 := by
        rw [div_le_iff₀ hx0]; nlinarith only [hx]
      have h3 := abs_le.mp h1
      have h4 := riccG3_nonneg hx
      have h5 := riccG3_le hx
      have h6 : 1 / (4 * x) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hx]
      unfold riccE
      rw [abs_le]
      constructor <;> linarith only [h3.1, h3.2, h2, h4, h5, h6])
  exact key x hx

/-- **Two-term asymptotics of `(Ai'/Ai)² - x`**: `|(Ai'/Ai)² - x - 1/(2√x) + 1/(4x²)| ≤ 5/(x^{7/2})` for `x ≥ 1`
(the `x^{-3/2}`-relative expansion `1/(2√x) - 1/(4x²) + O(x^{-7/2})` of the sum rule). -/
theorem airy_sq_sub_x_asymp {x : ℝ} (hx : 1 ≤ x) :
    |(airyAi' x / airyAi x) ^ 2 - x - (1 / (2 * √x) - 1 / (4 * x ^ 2))| ≤ 5 / (x ^ 3 * √x) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have he := riccG_threeTerm hx
  have hg0 := riccG3_nonneg hx
  have hg1 := riccG3_le hx
  have hGsq : (airyAi' x / airyAi x) ^ 2 = riccG x ^ 2 := by unfold riccG; ring
  set e := riccE x with hedef
  set g3 := riccG3 x with hg3
  have hG : riccG x = √x + g3 + e := by rw [hedef, riccE]; ring
  have hid : riccG x ^ 2 - x - (1 / (2 * √x) - 1 / (4 * x ^ 2)) =
      (-5 / (64 * (x ^ 3 * √x)) + 25 / (1024 * x ^ 5)) + 2 * √x * e + 2 * g3 * e + e ^ 2 := by
    rw [hG]
    have hx2 : x = √x ^ 2 := (Real.sq_sqrt hx0.le).symm
    rw [hg3, riccG3]
    generalize √x = s at hs hs1 hss hx2 ⊢
    subst hx2
    field_simp
    ring
  rw [hGsq, hid]
  set u : ℝ := 1 / (x ^ 3 * √x) with hu
  have hu0 : 0 < u := by positivity
  have h4 : 1 / x ^ 4 = u / √x := by rw [hu]; field_simp; nlinarith only [hss]
  have h4' : 1 / x ^ 4 ≤ u := by
    rw [h4, div_le_iff₀ hs]; nlinarith only [hu0, hs1]
  have h5 : 1 / x ^ 5 ≤ u := by
    rw [hu, div_le_div_iff₀ (by positivity) (by positivity)]
    have : x ^ 3 * √x ≤ x ^ 5 := by
      have h2 : √x ≤ x := by nlinarith only [hss, hs1]
      have h3 : x ^ 3 * √x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_left h2 (by positivity)
      have h45 : x ^ 4 ≤ x ^ 5 := pow_le_pow_right₀ hx (by norm_num)
      have h34 : x ^ 3 * x = x ^ 4 := by ring
      linarith only [h3, h45, h34]
    linarith only [this]
  have hea := abs_le.mp he
  have hse : |2 * √x * e| ≤ 2 * u := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * √x)]
    have : |e| ≤ u / √x := he.trans (le_of_eq h4)
    calc 2 * √x * |e| ≤ 2 * √x * (u / √x) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * u := by field_simp
  have hge : |2 * g3 * e| ≤ u / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * g3)]
    have hg1' : g3 ≤ 1 / 4 := hg1.trans (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hx])
    calc 2 * g3 * |e| ≤ 2 * (1 / 4) * u := by
          have : |e| ≤ u := he.trans h4'
          exact mul_le_mul (by linarith only [hg1']) this (abs_nonneg _) (by norm_num)
      _ = u / 2 := by ring
  have hee : |e ^ 2| ≤ u := by
    rw [abs_pow]
    have h1 : |e| ≤ 1 := he.trans (by rw [div_le_one (by positivity)]; exact one_le_pow₀ hx)
    have : |e| ^ 2 ≤ |e| * 1 := by nlinarith only [abs_nonneg e, h1]
    nlinarith only [this, he, h4', abs_nonneg e]
  have ht : |-5 / (64 * (x ^ 3 * √x)) + 25 / (1024 * x ^ 5)| ≤ u := by
    have a1 : -5 / (64 * (x ^ 3 * √x)) = -(5 / 64 * u) := by rw [hu]; field_simp
    have a2 : 25 / (1024 * x ^ 5) = 25 / 1024 * (1 / x ^ 5) := by field_simp
    rw [a1, a2, abs_le]
    constructor <;> nlinarith only [h5, hu0, one_div_pos.mpr (pow_pos hx0 5)]
  calc _ ≤ |-5 / (64 * (x ^ 3 * √x)) + 25 / (1024 * x ^ 5)| + |2 * √x * e| + |2 * g3 * e| + |e ^ 2| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ u + 2 * u + u / 2 + u := by gcongr
    _ ≤ 5 / (x ^ 3 * √x) := by
        have : 5 / (x ^ 3 * √x) = 5 * u := by rw [hu]; ring
        rw [this]; nlinarith only [hu0]

/-- **The sum rule with its two-term asymptotics**: with `m_n = -a_{n+1} ≥ 0` (the Airy zeros), for `x ≥ 1`
`Σ_n (x + m_n)^{-2} = 1/(2√x) - 1/(4x²) + O(x^{-7/2})`. -/
theorem airy_zero_sum_asymp {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun n : ℕ => ((x + -airyZero (n + 1)) ^ 2)⁻¹) ((airyAi' x / airyAi x) ^ 2 - x) ∧
    |(airyAi' x / airyAi x) ^ 2 - x - (1 / (2 * √x) - 1 / (4 * x ^ 2))| ≤ 5 / (x ^ 3 * √x) := by
  refine ⟨?_, airy_sq_sub_x_asymp hx⟩
  have := airyAi_sq_series_real (airyAi_pos (by linarith : 0 ≤ x)).ne'
  simpa [sub_eq_add_neg] using this

/-- info: 'FormalResearch.Special.riccG_threeTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riccG_threeTerm

/-- info: 'FormalResearch.Special.airy_zero_sum_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_zero_sum_asymp

end FormalResearch.Special

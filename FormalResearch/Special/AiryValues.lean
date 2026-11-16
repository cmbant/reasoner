module

public import FormalResearch.Special.AiryRotation

/-!
# Exact values of the Airy function at `0`, and `W(Ai, Bi) = 1/π`

Proved here (all by the same contour rotation, with no appeal to Cauchy's theorem):

* `airyAi_zero`: `Ai(0) = 3^{-2/3} / Γ(2/3)`; `airyAi'_zero`: `Ai'(0) = -3^{-1/3} / Γ(1/3)`;
  `airyAi_mul_airyAi'_zero`: `Ai(0) Ai'(0) = -1/(2√3 π)`.
* `airyAiC_wronskian_airyBiC_eq`: `Ai Bi' - Ai' Bi = 1/π` on `ℂ`; `airyBi_zero`, `airyBiC'_zero_eq`:
  `Bi(0) = 3^{-1/6}/Γ(2/3)`, `Bi'(0) = 3^{1/6}/Γ(1/3)`.

**Method.**  For `w(τ) = (τ² + i√3)/2` (so `w(0)` is vertical, `w(1) = e^{iπ/3}`), `c > 0`, put
`F_k(τ) = ∫_0^∞ w(τ) G_k(c + r w(τ)) dr`, `G_k(t) = (-t)^k exp(t³/3)`.  Then `∂_τ` of the integrand is the
total `r`-derivative `τ ∂_r [r G_k(c + r w)]`, so `F_k'(τ) = 0` (`hasDerivAt_airyRayInt_zero`,
dominated differentiation; the Gaussian majorant is uniform for `τ² ≤ 8/5` because `Re w² < 0` and
`Re w³ ≤ 0`).  Hence `F_k(1) = F_k(0) = i ∫_0^∞ G_k(c + is) ds`, whose imaginary part is
`π Ai^{(k)}(0)` (the lower half-line is the complex conjugate).  Letting `c → 0⁺` (dominated
convergence on the ray `τ = 1`, where `w³ = -1`) gives `Ai^{(k)}(0) = (1/π) Im[w (-w)^k ∫_0^∞ r^k e^{-r³/3} dr]`,
and the Gamma integral `∫_0^∞ r^k e^{-r³/3} dr = 3^{(k+1)/3 - 1} Γ((k+1)/3)` is Mathlib's.  The reflection
formula `Γ(1/3)Γ(2/3) = 2π/√3` turns `Γ(1/3)` into `1/Γ(2/3)` and gives the Wronskian.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `G_k(t) = (-t)^k exp(t³/3)`: the integrand of the `k`-th derivative `Ai^{(k)}(0)`. -/
noncomputable def airyG (k : ℕ) (t : ℂ) : ℂ := (-t) ^ k * cexp (t ^ 3 / 3)

/-- The derivative of `airyG k`. -/
noncomputable def airyGd (k : ℕ) (t : ℂ) : ℂ :=
  (-(k : ℂ) * (-t) ^ (k - 1) + (-t) ^ k * t ^ 2) * cexp (t ^ 3 / 3)

/-- The ray direction `w(τ) = (τ² + i√3)/2`: `w(0) = i√3/2` is vertical, `w(1) = e^{iπ/3}`. -/
noncomputable def airyRayDir (τ : ℝ) : ℂ := ⟨τ ^ 2 / 2, √3 / 2⟩

lemma airyRayDir_re (τ : ℝ) : (airyRayDir τ).re = τ ^ 2 / 2 := rfl
lemma airyRayDir_im (τ : ℝ) : (airyRayDir τ).im = √3 / 2 := rfl

lemma sqrt3_sq : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma re_cube (t : ℂ) : (t ^ 3).re = t.re ^ 3 - 3 * t.re * t.im ^ 2 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma hasDerivAt_airyG (k : ℕ) (t : ℂ) : HasDerivAt (airyG k) (airyGd k t) t := by
  have h1 : HasDerivAt (fun t : ℂ => (-t) ^ k) ((k : ℂ) * (-t) ^ (k - 1) * (-1)) t :=
    (hasDerivAt_id t).neg.pow k
  have h2 : HasDerivAt (fun t : ℂ => cexp (t ^ 3 / 3)) (cexp (t ^ 3 / 3) * t ^ 2) t := by
    have := (((hasDerivAt_id t).pow 3).div_const 3).cexp
    refine this.congr_deriv ?_
    simp
  refine (h1.mul h2).congr_deriv ?_
  unfold airyGd
  ring

lemma norm_airyG (k : ℕ) (t : ℂ) :
    ‖airyG k t‖ = ‖t‖ ^ k * Real.exp ((t.re ^ 3 - 3 * t.re * t.im ^ 2) / 3) := by
  unfold airyG
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_exp]
  congr 2
  simp [re_cube]

lemma re_cube_ray_le {c a r : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (ha : a ≤ 4 / 5) (hr : 0 ≤ r) :
    (c + r * a) ^ 3 - 3 * (c + r * a) * (r * (√3 / 2)) ^ 2 ≤ c ^ 3 + 3 * c ^ 2 * a * r - c / 4 * r ^ 2 := by
  have h1 : (r * (√3 / 2)) ^ 2 = r ^ 2 * 3 / 4 := by
    have := sqrt3_sq
    calc (r * (√3 / 2)) ^ 2 = r ^ 2 * (√3 ^ 2) / 4 := by ring
      _ = _ := by rw [this]
  rw [h1]
  have h2 : 0 ≤ c * r ^ 2 * (2 - 3 * a ^ 2) :=
    mul_nonneg (mul_nonneg hc.le (sq_nonneg r)) (by nlinarith)
  have h3 : 0 ≤ a * r ^ 3 * (9 / 4 - a ^ 2) :=
    mul_nonneg (mul_nonneg ha0 (pow_nonneg hr 3)) (by nlinarith)
  nlinarith [h2, h3]

/-- `‖exp(t³/3)‖` along the ray `t = c + r w`, `Re w = a ∈ [0, 4/5]`, `Im w = √3/2`: Gaussian bound. -/
lemma exp_ray_le {c a r : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (ha : a ≤ 4 / 5) (hr : 0 ≤ r) {t : ℂ}
    (hre : t.re = c + r * a) (him : t.im = r * (√3 / 2)) :
    (t.re ^ 3 - 3 * t.re * t.im ^ 2) / 3 ≤ 19 * c ^ 3 / 3 - c / 24 * r ^ 2 := by
  rw [hre, him]
  have h1 := re_cube_ray_le hc ha0 ha hr
  have h2 : c ^ 2 * a * r ≤ c ^ 2 * r := by nlinarith [mul_nonneg (sq_nonneg c) hr]
  have h3 : 0 ≤ c / 24 * (r - 12 * c) ^ 2 := by positivity
  nlinarith [h1, h2, h3]

/-- The point `c + r w(τ)` of the ray. -/
noncomputable def airyRayPt (c τ r : ℝ) : ℂ := (c : ℂ) + (r : ℂ) * airyRayDir τ

lemma airyRayPt_re (c τ r : ℝ) : (airyRayPt c τ r).re = c + r * (τ ^ 2 / 2) := by
  simp [airyRayPt, airyRayDir_re]

lemma airyRayPt_im (c τ r : ℝ) : (airyRayPt c τ r).im = r * (√3 / 2) := by
  simp [airyRayPt, airyRayDir_im]

lemma norm_airyRayPt_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) :
    ‖airyRayPt c τ r‖ ≤ c + 2 * r := by
  have h1 : ‖airyRayPt c τ r‖ ≤ |(airyRayPt c τ r).re| + |(airyRayPt c τ r).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [airyRayPt_re, airyRayPt_im] at h1
  have h3 : √(3 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
  have e1 : |c + r * (τ ^ 2 / 2)| = c + r * (τ ^ 2 / 2) :=
    abs_of_nonneg (by positivity)
  have e2 : |r * (√3 / 2)| = r * (√3 / 2) := abs_of_nonneg (by positivity)
  rw [e1, e2] at h1
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hτ), mul_nonneg hr (sub_nonneg.mpr h3)]

lemma re_exponent_ray_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) :
    ((airyRayPt c τ r).re ^ 3 - 3 * (airyRayPt c τ r).re * (airyRayPt c τ r).im ^ 2) / 3 ≤
      19 * c ^ 3 / 3 - c / 24 * r ^ 2 :=
  exp_ray_le hc (by positivity) (by linarith) hr (airyRayPt_re c τ r) (airyRayPt_im c τ r)

/-- Gaussian-type majorant of the ray integrands, `(1+r)^n · exp(-(c/24) r²)`. -/
noncomputable def airyRayBd (c : ℝ) (n : ℕ) (r : ℝ) : ℝ := (|(1 : ℝ)| + |r|) ^ n * Real.exp (-(c / 24) * r ^ 2)

lemma integrable_airyRayBd {c : ℝ} (hc : 0 < c) (n : ℕ) : Integrable (airyRayBd c n) :=
  integrable_absAdd_pow_gauss 1 (a := c / 24) (by positivity) n

lemma airyRayBd_nonneg (c : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ airyRayBd c n r := by
  unfold airyRayBd; positivity

lemma tendsto_airyRayBd {c : ℝ} (hc : 0 < c) (n : ℕ) : Tendsto (airyRayBd c n) atTop (𝓝 0) :=
  (tendsto_absAdd_pow_gauss 1 (a := c / 24) (by positivity) n).mono_left atTop_le_cocompact

/-- Key majorant: `‖t‖^j · |exp(t³/3)| ≤ ((3+c)(1+r))^j · exp(19c³/3) · exp(-(c/24)r²)`. -/
lemma norm_pow_mul_exp_ray_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r)
    {j n : ℕ} (hjn : j ≤ n) :
    ‖airyRayPt c τ r‖ ^ j * ‖cexp (airyRayPt c τ r ^ 3 / 3)‖ ≤
      ((3 + c) ^ n * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c n r := by
  have h1 := norm_airyRayPt_le hc hτ hr
  have h2 : ‖airyRayPt c τ r‖ ≤ (3 + c) * (|(1 : ℝ)| + |r|) := by
    rw [abs_one, abs_of_nonneg hr]; nlinarith
  have h3 : ‖cexp (airyRayPt c τ r ^ 3 / 3)‖ ≤
      Real.exp (19 * c ^ 3 / 3) * Real.exp (-(c / 24) * r ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := re_exponent_ray_le hc hτ hr
    have e : (airyRayPt c τ r ^ 3 / 3).re = ((airyRayPt c τ r).re ^ 3 -
        3 * (airyRayPt c τ r).re * (airyRayPt c τ r).im ^ 2) / 3 := by
      simp [re_cube]
    rw [e]; linarith
  have hX : 1 ≤ (3 + c) * (|(1 : ℝ)| + |r|) := by
    rw [abs_one]; nlinarith [abs_nonneg r]
  calc ‖airyRayPt c τ r‖ ^ j * ‖cexp (airyRayPt c τ r ^ 3 / 3)‖
      ≤ ((3 + c) * (|(1 : ℝ)| + |r|)) ^ n *
        (Real.exp (19 * c ^ 3 / 3) * Real.exp (-(c / 24) * r ^ 2)) :=
        mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) h2 j).trans (pow_le_pow_right₀ hX hjn)) h3
          (norm_nonneg _) (by positivity)
    _ = _ := by unfold airyRayBd; rw [mul_pow]; ring

/-- The ray integrand `w(τ) G_k(c + r w(τ))`. -/
noncomputable def airyRayF (k : ℕ) (c τ r : ℝ) : ℂ := airyRayDir τ * airyG k (airyRayPt c τ r)

/-- Its `τ`-derivative, `τ (G + r w G')(c + r w)`: a total `r`-derivative (see `hasDerivAt_airyRayR`). -/
noncomputable def airyRayD (k : ℕ) (c τ r : ℝ) : ℂ :=
  (τ : ℂ) * (airyG k (airyRayPt c τ r) + (r : ℂ) * airyRayDir τ * airyGd k (airyRayPt c τ r))

lemma airyRayDir_eq (τ : ℝ) :
    airyRayDir τ = ((τ ^ 2 / 2 : ℝ) : ℂ) + ((√3 / 2 : ℝ) : ℂ) * I :=
  Complex.ext (by rw [Complex.add_re, Complex.ofReal_re]; simp [airyRayDir_re])
    (by rw [Complex.add_im, Complex.ofReal_im]; simp [airyRayDir_im])

lemma hasDerivAt_airyRayDir (τ : ℝ) : HasDerivAt airyRayDir (τ : ℂ) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => ((τ ^ 2 / 2 : ℝ) : ℂ)) (τ : ℂ) τ := by
    have := ((hasDerivAt_pow 2 τ).div_const 2).ofReal_comp
    refine this.congr_deriv ?_
    push_cast; ring
  have h2 := h1.add_const (((√3 / 2 : ℝ) : ℂ) * I)
  have : airyRayDir = fun τ : ℝ => ((τ ^ 2 / 2 : ℝ) : ℂ) + ((√3 / 2 : ℝ) : ℂ) * I :=
    funext airyRayDir_eq
  rw [this]; exact h2

lemma hasDerivAt_airyRayPt_tau (c r τ : ℝ) :
    HasDerivAt (fun τ => airyRayPt c τ r) ((r : ℂ) * τ) τ := by
  unfold airyRayPt
  exact ((hasDerivAt_airyRayDir τ).const_mul (r : ℂ)).const_add (c : ℂ)

lemma hasDerivAt_airyRayF (k : ℕ) (c r τ : ℝ) :
    HasDerivAt (fun τ => airyRayF k c τ r) (airyRayD k c τ r) τ := by
  have h1 := (hasDerivAt_airyG k (airyRayPt c τ r)).scomp τ (hasDerivAt_airyRayPt_tau c r τ)
  have h2 := (hasDerivAt_airyRayDir τ).mul h1
  refine h2.congr_deriv ?_
  unfold airyRayD
  simp only [smul_eq_mul, Function.comp_apply]
  ring

lemma continuous_airyG (k : ℕ) : Continuous (airyG k) := by
  unfold airyG; fun_prop

lemma continuous_airyGd (k : ℕ) : Continuous (airyGd k) := by
  unfold airyGd; fun_prop

lemma continuous_airyRayPt_r (c τ : ℝ) : Continuous (fun r => airyRayPt c τ r) := by
  unfold airyRayPt; fun_prop

lemma continuous_airyRayF (k : ℕ) (c τ : ℝ) : Continuous (fun r => airyRayF k c τ r) := by
  unfold airyRayF
  exact continuous_const.mul ((continuous_airyG k).comp (continuous_airyRayPt_r c τ))

lemma continuous_airyRayD (k : ℕ) (c τ : ℝ) : Continuous (fun r => airyRayD k c τ r) := by
  unfold airyRayD
  exact continuous_const.mul (((continuous_airyG k).comp (continuous_airyRayPt_r c τ)).add
    ((Complex.continuous_ofReal.mul continuous_const).mul
      ((continuous_airyGd k).comp (continuous_airyRayPt_r c τ))))

lemma norm_airyRayDir_le {τ : ℝ} (hτ : τ ^ 2 ≤ 8 / 5) : ‖airyRayDir τ‖ ≤ 2 := by
  have h1 : ‖airyRayDir τ‖ ≤ |(airyRayDir τ).re| + |(airyRayDir τ).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [airyRayDir_re, airyRayDir_im] at h1
  have h3 : √(3 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
  linarith

lemma norm_airyG_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) (k : ℕ) :
    ‖airyG k (airyRayPt c τ r)‖ ≤ ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c k r := by
  unfold airyG
  rw [norm_mul, norm_pow, norm_neg]
  exact norm_pow_mul_exp_ray_le hc hτ hr le_rfl

lemma norm_airyGd_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) (k : ℕ) :
    ‖airyGd k (airyRayPt c τ r)‖ ≤
      ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3))) * airyRayBd c (k + 2) r := by
  set t := airyRayPt c τ r with ht
  have hE := norm_pow_mul_exp_ray_le hc hτ hr (j := k + 2) (n := k + 2) le_rfl
  have hE1 := norm_pow_mul_exp_ray_le hc hτ hr (j := k - 1) (n := k + 2) (by omega)
  unfold airyGd
  rw [norm_mul]
  calc ‖(-(k : ℂ) * (-t) ^ (k - 1) + (-t) ^ k * t ^ 2)‖ * ‖cexp (t ^ 3 / 3)‖
      ≤ ((k : ℝ) * ‖t‖ ^ (k - 1) + ‖t‖ ^ (k + 2)) * ‖cexp (t ^ 3 / 3)‖ := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        simp [norm_pow, pow_add, pow_two]
    _ = (k : ℝ) * (‖t‖ ^ (k - 1) * ‖cexp (t ^ 3 / 3)‖) +
          ‖t‖ ^ (k + 2) * ‖cexp (t ^ 3 / 3)‖ := by ring
    _ ≤ (k : ℝ) * (((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c (k + 2) r) +
          ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c (k + 2) r := by
        gcongr
    _ = _ := by ring

lemma airyRayBd_mono (c : ℝ) {n m : ℕ} (h : n ≤ m) (r : ℝ) : airyRayBd c n r ≤ airyRayBd c m r := by
  unfold airyRayBd
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ?_ h) (Real.exp_pos _).le
  rw [abs_one]; linarith [abs_nonneg r]

lemma mul_airyRayBd_le (c : ℝ) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r * airyRayBd c n r ≤ airyRayBd c (n + 1) r := by
  unfold airyRayBd
  have hp := Real.exp_pos (-(c / 24) * r ^ 2)
  rw [abs_one, abs_of_nonneg hr, pow_succ (1 + r) n]
  nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + r) n) hp.le]

/-- The constant of the `τ`-derivative majorant. -/
noncomputable def airyRayC (k : ℕ) (c : ℝ) : ℝ :=
  3 / 2 * ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3) +
    2 * ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3))))

lemma norm_airyRayD_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) (k : ℕ) :
    ‖airyRayD k c τ r‖ ≤ airyRayC k c * airyRayBd c (k + 3) r := by
  have hτ' : |τ| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hG := norm_airyG_le hc hτ hr k
  have hGd := norm_airyGd_le hc hτ hr k
  have hw := norm_airyRayDir_le hτ
  have b1 := airyRayBd_mono c (show k ≤ k + 3 by omega) r
  have b2 := mul_airyRayBd_le c (k + 2) hr
  have hB := airyRayBd_nonneg c (k + 2) r
  have hE : 0 ≤ (3 + c) ^ k * Real.exp (19 * c ^ 3 / 3) := by positivity
  have hE2 : 0 ≤ (k + 1 : ℝ) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3)) := by positivity
  unfold airyRayD airyRayC
  rw [norm_mul]
  have hN : ‖airyG k (airyRayPt c τ r) + (r : ℂ) * airyRayDir τ * airyGd k (airyRayPt c τ r)‖ ≤
      ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3) +
        2 * ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3)))) * airyRayBd c (k + 3) r := by
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖(r : ℂ) * airyRayDir τ * airyGd k (airyRayPt c τ r)‖ ≤
        2 * ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3))) * airyRayBd c (k + 3) r := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
      calc r * ‖airyRayDir τ‖ * ‖airyGd k (airyRayPt c τ r)‖
          ≤ r * 2 * (((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3))) *
              airyRayBd c (k + 2) r) := by gcongr
        _ = 2 * ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3))) *
              (r * airyRayBd c (k + 2) r) := by ring
        _ ≤ _ := by gcongr
    have e2 : ‖airyG k (airyRayPt c τ r)‖ ≤
        ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c (k + 3) r :=
      hG.trans (by gcongr)
    nlinarith
  calc ‖(τ : ℂ)‖ * ‖airyG k (airyRayPt c τ r) + (r : ℂ) * airyRayDir τ * airyGd k (airyRayPt c τ r)‖
      ≤ (3 / 2) * (((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3) +
        2 * ((k + 1) * ((3 + c) ^ (k + 2) * Real.exp (19 * c ^ 3 / 3)))) * airyRayBd c (k + 3) r) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hτ' hN (norm_nonneg _) (by norm_num)
    _ = _ := by ring

lemma norm_airyRayF_le {c τ r : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (hr : 0 ≤ r) (k : ℕ) :
    ‖airyRayF k c τ r‖ ≤ 2 * ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c k r := by
  unfold airyRayF
  rw [norm_mul]
  have := norm_airyG_le hc hτ hr k
  have := norm_airyRayDir_le hτ
  calc ‖airyRayDir τ‖ * ‖airyG k (airyRayPt c τ r)‖
      ≤ 2 * (((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c k r) := by gcongr
    _ = _ := by ring

/-- The ray integral `∫_0^∞ w(τ) G_k(c + r w(τ)) dr`. -/
noncomputable def airyRayInt (k : ℕ) (c τ : ℝ) : ℂ := ∫ r in Ioi (0 : ℝ), airyRayF k c τ r

lemma hasDerivAt_airyRayR (k : ℕ) (c τ r : ℝ) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * airyG k (airyRayPt c τ r))
      (airyG k (airyRayPt c τ r) + (r : ℂ) * airyRayDir τ * airyGd k (airyRayPt c τ r)) r := by
  have hpt : HasDerivAt (fun r : ℝ => airyRayPt c τ r) (airyRayDir τ) r := by
    unfold airyRayPt
    exact ((hasDerivAt_id r).ofReal_comp.mul_const (airyRayDir τ)).const_add (c : ℂ) |>.congr_deriv
      (by simp)
  have h1 := (hasDerivAt_airyG k (airyRayPt c τ r)).scomp r hpt
  have h2 := (hasDerivAt_id r).ofReal_comp.mul h1
  refine h2.congr_deriv ?_
  simp only [smul_eq_mul, Function.comp_apply]
  simp
  ring

lemma tendsto_airyRayR {c τ : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (k : ℕ) :
    Tendsto (fun r : ℝ => (r : ℂ) * airyG k (airyRayPt c τ r)) atTop (𝓝 0) := by
  have hb : Tendsto (fun r => ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c (k + 1) r)
      atTop (𝓝 0) := by
    simpa using (tendsto_airyRayBd hc (k + 1)).const_mul ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  calc r * ‖airyG k (airyRayPt c τ r)‖
      ≤ r * (((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * airyRayBd c k r) :=
        by gcongr; exact norm_airyG_le hc hτ hr k
    _ = ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)) * (r * airyRayBd c k r) := by ring
    _ ≤ _ := by gcongr; exact mul_airyRayBd_le c k hr

lemma integrableOn_airyRayD {c τ : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (k : ℕ) :
    IntegrableOn (fun r => airyRayD k c τ r) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrable_airyRayBd hc (k + 3)).const_mul (airyRayC k c)).integrableOn
    (continuous_airyRayD k c τ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  exact norm_airyRayD_le hc hτ (le_of_lt hr) k

lemma integrableOn_airyRayF {c τ : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (k : ℕ) :
    IntegrableOn (fun r => airyRayF k c τ r) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrable_airyRayBd hc k).const_mul
    (2 * ((3 + c) ^ k * Real.exp (19 * c ^ 3 / 3)))).integrableOn
    (continuous_airyRayF k c τ).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
  exact norm_airyRayF_le hc hτ (le_of_lt hr) k

/-- The `r`-integral of the `τ`-derivative vanishes: it is a total derivative of `r G(c + r w)`. -/
lemma integral_airyRayD {c τ : ℝ} (hc : 0 < c) (hτ : τ ^ 2 ≤ 8 / 5) (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), airyRayD k c τ r = 0 := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt
      (fun r : ℝ => (τ : ℂ) * ((r : ℂ) * airyG k (airyRayPt c τ r))) (airyRayD k c τ r) r :=
    fun r _ => (hasDerivAt_airyRayR k c τ r).const_mul (τ : ℂ)
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_airyRayD hc hτ k)
    (m := 0) (by simpa using (tendsto_airyRayR hc hτ k).const_mul (τ : ℂ))
  simpa using this

lemma hasDerivAt_airyRayInt_zero {c : ℝ} (hc : 0 < c) (k : ℕ) {τ₀ : ℝ} (h0 : 0 ≤ τ₀)
    (h1 : τ₀ ≤ 1) : HasDerivAt (airyRayInt k c) 0 τ₀ := by
  have hs : Metric.ball τ₀ (1 / 4) ∈ 𝓝 τ₀ := Metric.ball_mem_nhds _ (by norm_num)
  have hball : ∀ τ ∈ Metric.ball τ₀ (1 / 4), τ ^ 2 ≤ 8 / 5 := by
    intro τ hτ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hτ
    nlinarith [hτ.1, hτ.2]
  have h00 : τ₀ ^ 2 ≤ 8 / 5 := hball τ₀ (Metric.mem_ball_self (by norm_num))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (τ : ℝ) (r : ℝ) => airyRayF k c τ r)
    (F' := fun (τ : ℝ) (r : ℝ) => airyRayD k c τ r) hs
    (Eventually.of_forall fun τ => (continuous_airyRayF k c τ).aestronglyMeasurable)
    (integrableOn_airyRayF hc h00 k) (continuous_airyRayD k c τ₀).aestronglyMeasurable
    (bound := fun r => airyRayC k c * airyRayBd c (k + 3) r)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr τ hτ =>
      norm_airyRayD_le hc (hball τ hτ) (le_of_lt hr) k))
    ((integrable_airyRayBd hc (k + 3)).const_mul (airyRayC k c)).integrableOn
    (Eventually.of_forall fun r τ _ => hasDerivAt_airyRayF k c r τ)
  have h := key.2
  rw [integral_airyRayD hc h00 k] at h
  exact h

lemma airyRayInt_one_eq_zero {c : ℝ} (hc : 0 < c) (k : ℕ) : airyRayInt k c 1 = airyRayInt k c 0 := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (airyRayInt k c) 0 x :=
    fun x hx => hasDerivAt_airyRayInt_zero hc k hx.1 hx.2
  exact constant_of_has_deriv_right_zero
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩

lemma airyPoly_zero_eq (k : ℕ) (c s : ℝ) : airyPoly k c 0 s = airyG k (airyLine c s) := by
  simp [airyPoly, airyKernel, airyG]

/-- `Ai^{(k)}(0) = (1/2π) ∫_ℝ airyPoly` splits into the two half-lines, which are complex
conjugate: `M_k(c, 0) = (1/π) Re ∫_0^∞ G_k(c + is) ds`. -/
lemma airyMom_zero_re {c : ℝ} (hc : 0 < c) (k : ℕ) :
    (airyMom k c 0).re = (∫ s in Ioi (0 : ℝ), airyPoly k c 0 s).re / π := by
  have hi := integrable_airyPoly hc k 0
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := airyPoly k c 0) (b := 0) hi.integrableOn hi.integrableOn
  have hneg : ∫ s in Iic (0 : ℝ), airyPoly k c 0 s =
      (starRingEnd ℂ) (∫ s in Ioi (0 : ℝ), airyPoly k c 0 s) := by
    have h1 := integral_comp_neg_Ioi (0 : ℝ) (airyPoly k c 0)
    rw [neg_zero] at h1
    rw [← h1, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [conj_airyPoly]
    simp
  unfold airyMom
  rw [← hsplit, hneg]
  set A := ∫ s in Ioi (0 : ℝ), airyPoly k c 0 s
  have : (starRingEnd ℂ) A + A = ((2 * A.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [this]
  simp
  have := Real.pi_pos.ne'
  field_simp

/-- On the vertical ray the ray integral is `i ∫_0^∞ G_k(c + is) ds`. -/
lemma airyRayInt_zero_eq (k : ℕ) (c : ℝ) :
    airyRayInt k c 0 = I * ∫ s in Ioi (0 : ℝ), airyPoly k c 0 s := by
  have hβ : 0 < √(3 : ℝ) / 2 := by positivity
  have hw : airyRayDir 0 = ((√3 / 2 : ℝ) : ℂ) * I := by
    rw [airyRayDir_eq]; simp
  have hpt : ∀ r : ℝ, airyRayPt c 0 r = airyLine c ((√3 / 2) * r) := by
    intro r
    simp only [airyRayPt, airyLine, hw]
    push_cast; ring
  unfold airyRayInt airyRayF
  have h1 : ∀ r : ℝ, airyRayDir 0 * airyG k (airyRayPt c 0 r) =
      (((√3 / 2 : ℝ) : ℂ) * I) * airyPoly k c 0 ((√3 / 2) * r) := by
    intro r
    rw [hw, hpt, airyPoly_zero_eq]
  simp_rw [h1]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun s => airyPoly k c 0 s) 0 hβ]
  rw [mul_zero, Complex.real_smul]
  have : ((√3 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  push_cast
  field_simp

lemma airyMom_zero_re_eq {c : ℝ} (hc : 0 < c) (k : ℕ) :
    (airyMom k c 0).re = (airyRayInt k c 0).im / π := by
  rw [airyMom_zero_re hc k, airyRayInt_zero_eq]
  simp

/-- Uniform majorant on the ray `τ = 1` for `0 < c ≤ 1` (cubic decay `-r³` gives a Gaussian bound). -/
lemma norm_airyRayF_one_le {c r : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hr : 0 ≤ r) (k : ℕ) :
    ‖airyRayF k c 1 r‖ ≤ Real.exp 1 * airyRayBd 8 k r := by
  have hw : ‖airyRayDir 1‖ = 1 := by
    have h : ‖airyRayDir 1‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, airyRayDir_re, airyRayDir_im]
      have := sqrt3_sq
      nlinarith
    nlinarith [norm_nonneg (airyRayDir 1)]
  have h1 : ‖airyRayPt c 1 r‖ ≤ 1 + |r| := by
    have : ‖airyRayPt c 1 r‖ ≤ c + r := by
      unfold airyRayPt
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hw, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr,
        Real.norm_of_nonneg hc.le]
      linarith
    rw [abs_of_nonneg hr]; linarith
  have h2 : ‖cexp (airyRayPt c 1 r ^ 3 / 3)‖ ≤ Real.exp 1 * Real.exp (-(8 / 24) * r ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : (airyRayPt c 1 r ^ 3 / 3).re = ((airyRayPt c 1 r).re ^ 3 -
        3 * (airyRayPt c 1 r).re * (airyRayPt c 1 r).im ^ 2) / 3 := by
      simp [re_cube]
    rw [e, airyRayPt_re, airyRayPt_im]
    have hs := sqrt3_sq
    have h3 : (r * (√3 / 2)) ^ 2 = r ^ 2 * 3 / 4 := by
      calc (r * (√3 / 2)) ^ 2 = r ^ 2 * (√3 ^ 2) / 4 := by ring
        _ = _ := by rw [hs]
    rw [h3]
    have h4 : r ^ 3 - 3 / 2 * r + (-r ^ 2 + 2) ≥ 0 := by
      nlinarith [sq_nonneg (r - 6 / 5), mul_nonneg hr (sq_nonneg (r - 6 / 5)), sq_nonneg r]
    nlinarith [mul_nonneg (sq_nonneg c) hr, mul_nonneg hc.le (sq_nonneg r), pow_le_one₀ hc.le hc1 (n := 3),
      mul_le_mul_of_nonneg_right hc1 (mul_nonneg hc.le hr)]
  unfold airyRayF airyG airyRayBd
  rw [norm_mul, norm_mul, norm_pow, norm_neg, hw, one_mul, abs_one]
  calc ‖airyRayPt c 1 r‖ ^ k * ‖cexp (airyRayPt c 1 r ^ 3 / 3)‖
      ≤ (1 + |r|) ^ k * (Real.exp 1 * Real.exp (-(8 / 24) * r ^ 2)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 k) h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring_nf

lemma tendsto_airyRayInt_c (k : ℕ) :
    Tendsto (fun c : ℝ => airyRayInt k c 1) (𝓝[>] 0) (𝓝 (airyRayInt k 0 1)) := by
  unfold airyRayInt
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun r => Real.exp 1 * airyRayBd 8 k r) (Eventually.of_forall fun c => ?_) ?_
    ((integrable_airyRayBd (c := 8) (by norm_num) k).const_mul (Real.exp 1)).integrableOn ?_
  · exact (continuous_airyRayF k c 1).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun r hr => norm_airyRayF_one_le hc.1 hc.2.le (le_of_lt hr) k)
  · refine Eventually.of_forall fun r => ?_
    have hcont : Continuous (fun c : ℝ => airyRayF k c 1 r) := by
      unfold airyRayF airyRayPt
      have := continuous_airyG k
      fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

/-- `Ai^{(k)}(0) = (1/π) Im ∫_0^∞ w G_k(r w) dr`, `w = e^{iπ/3}`: the contour rotated to the rays
`arg t = ±π/3`. -/
theorem airyMom_one_zero_re (k : ℕ) :
    (airyMom k 1 0).re = (airyRayInt k 0 1).im / π := by
  have hlim := (Complex.continuous_im.tendsto _).comp (tendsto_airyRayInt_c k)
  have hconst : Tendsto (fun c : ℝ => (airyRayInt k c 1).im) (𝓝[>] 0)
      (𝓝 (π * (airyMom k 1 0).re)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with c hc
    rw [airyRayInt_one_eq_zero hc.1 k]
    have h := airyMom_zero_re_eq hc.1 k
    rw [airyMom_indep hc.1 k 0] at h
    have := Real.pi_pos.ne'
    rw [h]; field_simp
  have := tendsto_nhds_unique hconst hlim
  have hp := Real.pi_pos.ne'
  rw [← this]
  field_simp

lemma airyRayDir_one_cube : airyRayDir 1 ^ 3 = -1 := by
  have hs := sqrt3_sq
  have h4 : √(3 : ℝ) ^ 3 = 3 * √3 := by rw [pow_succ, hs]
  apply Complex.ext
  · simp [pow_succ, Complex.mul_re, Complex.mul_im, airyRayDir_re, airyRayDir_im]
    nlinarith [hs, h4]
  · simp [pow_succ, Complex.mul_re, Complex.mul_im, airyRayDir_re, airyRayDir_im]
    nlinarith [hs, h4]

/-- At `c = 0` on the ray `e^{iπ/3}` the integrand is real-exponential: `w³ = -1`. -/
lemma airyRayInt_zero_one (k : ℕ) :
    airyRayInt k 0 1 = airyRayDir 1 * (-airyRayDir 1) ^ k *
      ((∫ r in Ioi (0 : ℝ), r ^ k * Real.exp (-(1 / 3) * r ^ 3) : ℝ) : ℂ) := by
  unfold airyRayInt
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [airyRayF, airyG, airyRayPt]
  have h3 : ((((0 : ℝ) : ℂ) + (r : ℂ) * airyRayDir 1)) ^ 3 = -((r : ℂ) ^ 3) := by
    simp only [Complex.ofReal_zero, zero_add]
    rw [mul_pow, airyRayDir_one_cube]; ring
  rw [h3]
  have : cexp (-(r : ℂ) ^ 3 / 3) = ((Real.exp (-(1 / 3) * r ^ 3) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [this]
  simp only [Complex.ofReal_zero, zero_add, neg_mul_eq_mul_neg]
  push_cast
  ring

/-- `∫_0^∞ r^k e^{-r³/3} dr = 3^{(k+1)/3 - 1} Γ((k+1)/3)`. -/
lemma integral_pow_exp_cube (k : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ k * Real.exp (-(1 / 3) * r ^ 3) =
      (3 : ℝ) ^ (((k : ℝ) + 1) / 3 - 1) * Real.Gamma (((k : ℝ) + 1) / 3) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 3) (q := (k : ℝ)) (b := 1 / 3)
    (by norm_num) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by norm_num)
  have e : ∀ r : ℝ, r ^ (k : ℝ) * Real.exp (-(1 / 3) * r ^ (3 : ℝ)) =
      r ^ k * Real.exp (-(1 / 3) * r ^ 3) := by
    intro r
    rw [Real.rpow_natCast, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [e] at h
  rw [h]
  have h3 : ((1 : ℝ) / 3) ^ (-((k : ℝ) + 1) / 3) = (3 : ℝ) ^ (((k : ℝ) + 1) / 3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [h3, Real.rpow_sub (by norm_num), Real.rpow_one]
  ring

lemma integral_exp_cube_zero :
    ∫ r in Ioi (0 : ℝ), r ^ 0 * Real.exp (-(1 / 3) * r ^ 3) =
      (3 : ℝ) ^ (-(2 / 3 : ℝ)) * Real.Gamma (1 / 3) := by
  rw [integral_pow_exp_cube]; norm_num

lemma integral_exp_cube_one :
    ∫ r in Ioi (0 : ℝ), r ^ 1 * Real.exp (-(1 / 3) * r ^ 3) =
      (3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.Gamma (2 / 3) := by
  rw [integral_pow_exp_cube]; norm_num

/-- `Ai(0) = (√3/(2π)) 3^{-2/3} Γ(1/3)` (before the reflection formula). -/
lemma airyAi_zero_gamma_third : airyAi 0 = √3 / (2 * π) * ((3 : ℝ) ^ (-(2 / 3 : ℝ)) * Real.Gamma (1 / 3)) := by
  have h := airyAi_eq_re_airyMom (c := 1) one_pos 0
  rw [Complex.ofReal_zero] at h
  rw [h, airyMom_one_zero_re, airyRayInt_zero_one, pow_zero, mul_one, ← integral_exp_cube_zero]
  rw [Complex.im_mul_ofReal, airyRayDir_im]
  ring

/-- `Ai'(0) = -(√3/(2π)) 3^{-1/3} Γ(2/3)` (before the reflection formula). -/
lemma airyAi'_zero_gamma_two_thirds :
    airyAi' 0 = -(√3 / (2 * π)) * ((3 : ℝ) ^ (-(1 / 3 : ℝ)) * Real.Gamma (2 / 3)) := by
  have h := airyAi'_eq_re_airyMom (c := 1) one_pos 0
  rw [Complex.ofReal_zero] at h
  rw [h, airyMom_one_zero_re, airyRayInt_zero_one, ← integral_exp_cube_one, pow_one]
  rw [Complex.im_mul_ofReal]
  simp [Complex.mul_im, airyRayDir_re, airyRayDir_im]
  ring

/-- Reflection formula at `1/3`: `Γ(1/3) Γ(2/3) = 2π/√3`. -/
lemma gamma_third_mul_two_thirds : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) = 2 * π / √3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3 : ℝ) = π / 3 by ring,
    Real.sin_pi_div_three] at h
  rw [h]
  have : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  field_simp

/-- **`Ai(0) = 3^{-2/3} / Γ(2/3)`.** -/
theorem airyAi_zero : airyAi 0 = (3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3) := by
  rw [airyAi_zero_gamma_third]
  have h2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hg := gamma_third_mul_two_thirds
  have hg' : Real.Gamma (1 / 3) = 2 * π / √3 / Real.Gamma (2 / 3) := by
    rw [eq_div_iff h2.ne', hg]
  rw [hg']
  field_simp

/-- **`Ai'(0) = -3^{-1/3} / Γ(1/3)`.** -/
theorem airyAi'_zero : airyAi' 0 = -((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)) := by
  rw [airyAi'_zero_gamma_two_thirds]
  have h1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hg := gamma_third_mul_two_thirds
  have hg' : Real.Gamma (2 / 3) = 2 * π / √3 / Real.Gamma (1 / 3) := by
    rw [eq_div_iff h1.ne', mul_comm, hg]
  rw [hg']
  field_simp

/-- **`Ai(0) Ai'(0) = -1/(2√3 π) = -√3/(6π)`.** -/
theorem airyAi_mul_airyAi'_zero : airyAi 0 * airyAi' 0 = -(1 / (2 * √3 * π)) := by
  rw [airyAi_zero, airyAi'_zero]
  have h1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hg := gamma_third_mul_two_thirds
  have h3 : (3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 3 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hss : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hp := Real.pi_pos
  have e : (3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3) *
      -((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)) =
      -(((3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (-(1 / 3 : ℝ))) /
        (Real.Gamma (1 / 3) * Real.Gamma (2 / 3))) := by
    field_simp
  rw [e, h3, hg]
  field_simp
  nlinarith [hss]

/-- **`W(Ai, Bi) = -2√3 Ai(0) Ai'(0) = 1/π`.** -/
theorem airyWronskian_eq : -2 * √3 * airyAi 0 * airyAi' 0 = 1 / π := by
  have h := airyAi_mul_airyAi'_zero
  have hs : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hp := Real.pi_pos
  calc -2 * √3 * airyAi 0 * airyAi' 0 = -2 * √3 * (airyAi 0 * airyAi' 0) := by ring
    _ = 1 / π := by rw [h]; field_simp

/-- **The Wronskian of `Ai` and `Bi` is `1/π`** (constant on `ℂ`). -/
theorem airyAiC_wronskian_airyBiC_eq (z : ℂ) :
    airyAiC z * airyBiC' z - deriv airyAiC z * airyBiC z = ((1 / π : ℝ) : ℂ) := by
  rw [airyAiC_wronskian_airyBiC, airyWronskian_eq]

/-- **`Bi(0) = 3^{-1/6}/Γ(2/3)`** (`= √3 Ai(0)`). -/
theorem airyBi_zero : airyBi 0 = (3 : ℝ) ^ (-(1 / 6 : ℝ)) / Real.Gamma (2 / 3) := by
  have h : airyBi 0 = √3 * airyAi 0 := by
    have := airyBiC_zero
    have e : airyAiC 0 = (airyAi 0 : ℂ) := by simpa using airyAiC_ofReal 0
    rw [e] at this
    have h2 := airyBiC_ofReal 0
    rw [Complex.ofReal_zero] at h2
    rw [h2] at this
    exact_mod_cast this
  rw [h, airyAi_zero, Real.sqrt_eq_rpow, ← mul_div_assoc, ← Real.rpow_add (by norm_num)]
  norm_num

/-- **`Bi'(0) = 3^{1/6}/Γ(1/3)`** (`= -√3 Ai'(0)`). -/
theorem airyBiC'_zero_eq : airyBiC' 0 = (((3 : ℝ) ^ (1 / 6 : ℝ) / Real.Gamma (1 / 3) : ℝ) : ℂ) := by
  rw [airyBiC'_zero]
  have e : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by simpa using deriv_airyAiC_ofReal 0
  rw [e, airyAi'_zero]
  have : -((√3 : ℝ) : ℂ) * (((-((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)) : ℝ)) : ℂ) =
      ((√3 * ((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  congr 1
  rw [Real.sqrt_eq_rpow, ← mul_div_assoc, ← Real.rpow_add (by norm_num)]
  norm_num

/-- info: 'FormalResearch.Special.airyAi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_zero

/-- info: 'FormalResearch.Special.airyAi'_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_zero

/-- info: 'FormalResearch.Special.airyAi_mul_airyAi'_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_mul_airyAi'_zero

/-- info: 'FormalResearch.Special.airyAiC_wronskian_airyBiC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiC_wronskian_airyBiC_eq

/-- info: 'FormalResearch.Special.airyBi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_zero

/-- info: 'FormalResearch.Special.airyBiC'_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiC'_zero_eq

end FormalResearch.Special

module

public import FormalResearch.SignUncertainty.UctEnv2
public import FormalResearch.SignUncertainty.UctOuterGrowth
public import FormalResearch.SignUncertainty.CtOuterPart3Plus
public import FormalResearch.SignUncertainty.CtOuterU2
public import FormalResearch.SignUncertainty.CtOuterBdryIm

/-!
# `W^seed` edge trace: the outer factor `e^{-h(iτ)}` as an `Env2` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `uct:outer-growth` and `ct:outer` (2)-(3).  **Proved.**

`h(iτ) = u_r(τ) + i(θ_-(τ) + arctan τ)` (`re_outerHbar_left`, `outerTheta_minus`), with `u_r`, `θ_-` smooth, `u_r', u_r''` of
polynomial growth (`ct:outer` proof of (1)) and `θ_-^{(j)}` bounded (`ct_outer_part3`).  Hence `τ ↦ e^{-h(iτ)}` is `C²` and
`|E|, |E'|, |E''| ≤ C(1+|τ|)⁶` (`env2_outerE`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtOuter

lemma poly_env_of_far {v : ℝ → ℝ} (hc : Continuous v) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (h : ∀ t : ℝ, 1 ≤ |t| → |v t| ≤ a + b * |t| + c * t ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |v t| ≤ A * (1 + |t|) ^ 2 := by
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hB : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨B0 + a + b + c, by positivity, fun t => ?_⟩
  have ht0 := abs_nonneg t
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  rcases le_or_gt 1 |t| with h1 | h1
  · have := h t h1
    rw [hsq] at this
    nlinarith [mul_nonneg hb ht0, mul_nonneg hc0 ht0, mul_nonneg ha ht0, mul_nonneg hB ht0, sq_nonneg |t|,
      mul_nonneg hc0 (sq_nonneg |t|), mul_nonneg hB (sq_nonneg |t|), mul_nonneg ha (sq_nonneg |t|),
      mul_nonneg hb (sq_nonneg |t|)]
  · have hmem : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
    have h2 := hB0 t hmem
    rw [Real.norm_eq_abs] at h2
    nlinarith [mul_nonneg hb ht0, mul_nonneg hc0 ht0, mul_nonneg ha ht0, mul_nonneg hB ht0, sq_nonneg |t|,
      mul_nonneg hc0 (sq_nonneg |t|), mul_nonneg hB (sq_nonneg |t|), mul_nonneg ha (sq_nonneg |t|),
      mul_nonneg hb (sq_nonneg |t|)]

lemma uR1_env : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |uR1 t| ≤ A * (1 + |t|) ^ 2 := by
  refine poly_env_of_far continuous_uR1 (a := 1) (b := π ^ 2 / 3) (c := 0) (by norm_num) (by positivity) le_rfl
    fun t ht => ?_
  rcases le_total 0 t with h0 | h0
  · have h1 : 1 ≤ t := by rwa [abs_of_nonneg h0] at ht
    rw [uR1_eq (by linarith), abs_of_nonneg h0]
    have := abs_w1_le h1
    linarith only [this]
  · have h1 : 1 ≤ -t := by rwa [abs_of_nonpos h0] at ht
    have e : uR1 t = -uR1 (-t) := by rw [uR1_neg]; ring
    rw [e, abs_neg, uR1_eq (by linarith), abs_of_nonpos h0]
    have := abs_w1_le h1
    linarith only [this]

lemma uR2_env : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |uR2 t| ≤ A * (1 + |t|) ^ 2 := by
  refine poly_env_of_far continuous_uR2 (a := 3 / 2) (b := 2 + 3 * π ^ 3) (c := 2 * π ^ 4 / 9)
    (by norm_num) (by positivity) (by positivity) fun t ht => ?_
  rcases le_total 0 t with h0 | h0
  · have h1 : 1 ≤ t := by rwa [abs_of_nonneg h0] at ht
    rw [uR2_eq (by linarith), abs_of_nonneg h0]
    exact abs_w2_le h1
  · have h1 : 1 ≤ -t := by rwa [abs_of_nonpos h0] at ht
    rw [← uR2_neg t, uR2_eq (by linarith), abs_of_nonpos h0]
    have := abs_w2_le h1
    nlinarith only [this]

lemma uR_env : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |uR t| ≤ A * (1 + |t|) ^ 2 := by
  refine ⟨|(1 / 2) * Real.log (6 / π ^ 2)| + 2, by positivity, fun t => ?_⟩
  have h1 := uR_le t
  have h2 := uR_ge t
  have h3 := log_one_add_sq_le t
  have h4 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  have ht := abs_nonneg t
  have hA := abs_nonneg ((1 / 2) * Real.log (6 / π ^ 2))
  have hle := le_abs_self ((1 / 2) * Real.log (6 / π ^ 2))
  have hge := neg_abs_le ((1 / 2) * Real.log (6 / π ^ 2))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hA ht, mul_nonneg hA (sq_nonneg |t|), sq_nonneg |t|]

lemma theta_env : ∃ C : ℝ, 0 ≤ C ∧ (∀ τ : ℝ, |outerTheta (-1) τ| ≤ C * |τ|) ∧
    (∀ τ : ℝ, |deriv (outerTheta (-1)) τ| ≤ C) ∧ (∀ τ : ℝ, |deriv (deriv (outerTheta (-1))) τ| ≤ C) := by
  obtain ⟨-, h3⟩ := ct_outer_part3
  obtain ⟨-, C1, hC1⟩ := h3 (-1) (Or.inl rfl) 1 le_rfl
  obtain ⟨-, C2, hC2⟩ := h3 (-1) (Or.inl rfl) 2 (by norm_num)
  have hθ : ContDiff ℝ ⊤ (outerTheta (-1)) := contDiff_outerTheta (-1)
  have hdiff : Differentiable ℝ (outerTheta (-1)) := hθ.differentiable (by simp)
  have b1 : ∀ τ : ℝ, |deriv (outerTheta (-1)) τ| ≤ |C1| := fun τ => by
    have := hC1 τ
    rw [iteratedDeriv_one] at this
    have hp : 1 ≤ (1 + |τ|) ^ (1 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
    calc _ ≤ C1 / (1 + |τ|) ^ (1 + 1) := this
      _ ≤ |C1| / (1 + |τ|) ^ (1 + 1) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C1| := div_le_self (abs_nonneg _) hp
  have b2 : ∀ τ : ℝ, |deriv (deriv (outerTheta (-1))) τ| ≤ |C2| := fun τ => by
    have := hC2 τ
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    have hp : 1 ≤ (1 + |τ|) ^ (2 + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
    calc _ ≤ C2 / (1 + |τ|) ^ (2 + 1) := this
      _ ≤ |C2| / (1 + |τ|) ^ (2 + 1) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C2| := div_le_self (abs_nonneg _) hp
  have h0 : outerTheta (-1) 0 = 0 := by
    have := outerTheta_neg (-1) 0
    simp at this
    linarith
  refine ⟨max |C1| |C2|, by positivity, fun τ => ?_, fun τ => (b1 τ).trans (le_max_left _ _),
    fun τ => (b2 τ).trans (le_max_right _ _)⟩
  have hd : ∀ t, HasDerivAt (outerTheta (-1)) (deriv (outerTheta (-1)) t) t := fun t => (hdiff t).hasDerivAt
  have := abs_sub_le_of_deriv hd (r := |τ|) (K := |C1|) (x := τ)
    (fun y hy => b1 y) le_rfl
  rw [h0, sub_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg τ))

lemma arctan_env : (∀ τ : ℝ, |Real.arctan τ| ≤ |τ|) ∧ (∀ τ : ℝ, |deriv Real.arctan τ| ≤ 1) ∧
    (∀ τ : ℝ, |deriv (deriv Real.arctan) τ| ≤ 1) := by
  have hd1 : deriv Real.arctan = fun x : ℝ => (1 + x ^ 2)⁻¹ := by
    funext x; rw [Real.deriv_arctan]; simp
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · exact Real.abs_arctan_le_abs
  · rw [hd1]
    have : 0 < 1 + τ ^ 2 := by positivity
    rw [abs_of_pos (inv_pos.mpr this)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg τ])
  · rw [hd1]
    have h : HasDerivAt (fun x : ℝ => (1 + x ^ 2)⁻¹) (-(2 * τ) / (1 + τ ^ 2) ^ 2) τ := by
      have h0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * τ) τ := by
        simpa using (hasDerivAt_pow 2 τ).const_add 1
      exact h0.inv (by positivity)
    rw [h.deriv]
    have hp : 0 < (1 + τ ^ 2) ^ 2 := by positivity
    rw [abs_div, abs_neg, abs_of_pos hp, div_le_one hp]
    rw [abs_mul, abs_two]
    nlinarith [sq_nonneg (|τ| - 1), sq_abs τ, abs_nonneg τ, sq_nonneg τ]


lemma outerHbar_edge (τ : ℝ) :
    outerHbar (Complex.I * (τ : ℂ)) = (uR τ : ℂ) + Complex.I * (outerTheta (-1) τ : ℂ) + Complex.I * (Real.arctan τ : ℂ) := by
  apply Complex.ext
  · have := re_outerHbar_left τ
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_sub, sub_zero, zero_add, add_zero, neg_zero, sub_self]
    linarith
  · have h := outerTheta_minus τ
    have : (outerHbar (Complex.I * (τ : ℂ))).im = outerTheta (-1) τ + Real.arctan τ := by linarith
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_sub, sub_zero, zero_add, add_zero, neg_zero]
    linarith

lemma one_add_abs_le_sq (τ : ℝ) : 1 + |τ| ≤ (1 + |τ|) ^ 2 := by
  have := abs_nonneg τ
  nlinarith

theorem env2_outerG : ∃ Ag : ℝ, 0 ≤ Ag ∧
    Env2 (fun τ : ℝ => outerHbar (Complex.I * (τ : ℂ))) (fun τ => Ag * (1 + |τ|) ^ 2) := by
  obtain ⟨Au, hAu, hu0⟩ := uR_env
  obtain ⟨A1, hA1, hu1⟩ := uR1_env
  obtain ⟨A2, hA2, hu2⟩ := uR2_env
  obtain ⟨Cθ, hCθ, ht0, ht1, ht2⟩ := theta_env
  obtain ⟨ha0, ha1, ha2⟩ := arctan_env
  have hθcd : ContDiff ℝ 2 (outerTheta (-1)) := ((contDiff_outerTheta (-1)).of_le (by simp))
  have hacd : ContDiff ℝ 2 Real.arctan := Real.contDiff_arctan
  have hucd : ContDiff ℝ 2 uR := contDiff_uR.of_le (by simp)
  have hb : ∀ τ : ℝ, (1 : ℝ) ≤ 1 + |τ| := fun τ => by linarith [abs_nonneg τ]
  have e1 : Env2 (fun τ => (uR τ : ℂ)) (fun τ => (Au + A1 + A2) * (1 + |τ|) ^ 2) := by
    refine Env2.ofReal hucd _ (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
    · have := hu0 τ; have h := mul_nonneg (add_nonneg hA1 hA2) (sq_nonneg (1 + |τ|)); nlinarith
    · have := hu1 τ; have h := mul_nonneg (add_nonneg hAu hA2) (sq_nonneg (1 + |τ|)); show |uR1 τ| ≤ _; nlinarith
    · have := hu2 τ; have h := mul_nonneg (add_nonneg hAu hA1) (sq_nonneg (1 + |τ|)); show |uR2 τ| ≤ _; nlinarith
  have e2 : Env2 (fun τ => (outerTheta (-1) τ : ℂ)) (fun τ => Cθ * (1 + |τ|)) := by
    refine Env2.ofReal hθcd _ (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
    · have := ht0 τ; nlinarith [abs_nonneg τ]
    · have := ht1 τ; nlinarith [abs_nonneg τ]
    · have := ht2 τ; nlinarith [abs_nonneg τ]
  have e3 : Env2 (fun τ => (Real.arctan τ : ℂ)) (fun τ => 1 * (1 + |τ|)) := by
    refine Env2.ofReal hacd _ (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
    · have := ha0 τ; nlinarith [abs_nonneg τ]
    · have := ha1 τ; nlinarith [abs_nonneg τ]
    · have := ha2 τ; nlinarith [abs_nonneg τ]
  have hsum := (e1.add (e2.const_mul Complex.I)).add (e3.const_mul Complex.I)
  have hfun : (fun τ : ℝ => outerHbar (Complex.I * (τ : ℂ))) = fun τ : ℝ =>
      ((uR τ : ℂ) + Complex.I * (outerTheta (-1) τ : ℂ)) + Complex.I * (Real.arctan τ : ℂ) := by
    funext τ; rw [outerHbar_edge]
  rw [hfun]
  refine ⟨(Au + A1 + A2) + 4 * Cθ + 4, by positivity, hsum.mono fun τ => ?_⟩
  have h1 := one_add_abs_le_sq τ
  simp only [Complex.norm_I, mul_one]
  have hc : 0 ≤ Cθ * (1 + |τ|) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hCθ]

theorem env2_outerE : ∃ aE : ℝ, 0 ≤ aE ∧
    Env2 (fun τ : ℝ => Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) (fun τ => aE * (1 + |τ|) ^ 6) := by
  obtain ⟨Ag, hAg, hG⟩ := env2_outerG
  obtain ⟨CE, hCE⟩ := norm_exp_neg_outerHbar_le
  have hCE0 : 0 ≤ max CE 0 := le_max_right _ _
  have hE := hG.exp_neg (fun τ => max CE 0 * (1 + |τ|) ^ 2) (fun τ => by
    have hmem : (Complex.I * (τ : ℂ)) ∈ closedStrip := ⟨by simp, by simp⟩
    have := hCE _ hmem
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
      zero_add] at this
    have h2 : 1 + τ ^ 2 ≤ (1 + |τ|) ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    calc _ ≤ CE * (1 + τ ^ 2) := this
      _ ≤ max CE 0 * (1 + τ ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hCE0)
  refine ⟨max CE 0 * (1 + 2 * Ag + Ag ^ 2), by positivity, hE.mono fun τ => ?_⟩
  have hx : (1 : ℝ) ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have p2 : (1 + |τ|) ^ 2 ≤ (1 + |τ|) ^ 6 := pow_le_pow_right₀ hx (by norm_num)
  have p4 : (1 + |τ|) ^ 4 ≤ (1 + |τ|) ^ 6 := pow_le_pow_right₀ hx (by norm_num)
  have p0 : (1 : ℝ) ≤ (1 + |τ|) ^ 4 := one_le_pow₀ hx
  have hq : (1 + |τ|) ^ 2 * (1 + 2 * (Ag * (1 + |τ|) ^ 2) + (Ag * (1 + |τ|) ^ 2) ^ 2) ≤
      (1 + 2 * Ag + Ag ^ 2) * (1 + |τ|) ^ 6 := by
    have a1 : (1 + |τ|) ^ 2 * 1 ≤ (1 + |τ|) ^ 6 := by linarith
    have a2 : (1 + |τ|) ^ 2 * (1 + |τ|) ^ 2 ≤ (1 + |τ|) ^ 6 := by nlinarith [sq_nonneg (1 + |τ|), pow_pos (by linarith : (0:ℝ) < 1 + |τ|) 2]
    have a3 : (1 + |τ|) ^ 2 * ((1 + |τ|) ^ 2) ^ 2 = (1 + |τ|) ^ 6 := by ring
    nlinarith [mul_nonneg hAg (sq_nonneg (1 + |τ|)), sq_nonneg Ag, mul_nonneg (sq_nonneg Ag) (sq_nonneg (1 + |τ|))]
  calc max CE 0 * (1 + |τ|) ^ 2 * (1 + 2 * (Ag * (1 + |τ|) ^ 2) + (Ag * (1 + |τ|) ^ 2) ^ 2)
      = max CE 0 * ((1 + |τ|) ^ 2 * (1 + 2 * (Ag * (1 + |τ|) ^ 2) + (Ag * (1 + |τ|) ^ 2) ^ 2)) := by ring
    _ ≤ max CE 0 * ((1 + 2 * Ag + Ag ^ 2) * (1 + |τ|) ^ 6) := mul_le_mul_of_nonneg_left hq hCE0
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.env2_outerG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_outerG

/-- info: 'FormalResearch.SignUncertainty.env2_outerE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_outerE

end FormalResearch.SignUncertainty

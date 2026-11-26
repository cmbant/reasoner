module

public import FormalResearch.CohnElkies.ComplexEdgePhase
public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.SignUncertainty.UctMcSmallA

/-!
# The edge dispersion integrand `ℓ(u) = log(tanh(πu/2)/(πu/2))` is smooth with `|ℓ'| ≤ 1` (F2a helper for `uct:bump-symbol`)

`ellFun u = log (tanh (π u / 2) / (π u / 2))` is `C^∞` on `ℝ` (it is `stripG (i u)`), even, `ellFun = -ceEll (π u/2)`,
`|ellFun'| ≤ π²/12 ≤ 1` (`m2_bounds`) and so `|ellFun u| ≤ |u|`.  `ellN τ = ∫₀^τ ℓ` is `C^∞` with `ellN' = ℓ`, `|ellN τ| ≤ τ²`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

noncomputable def ellFun (u : ℝ) : ℝ := Real.log (Real.tanh (Real.pi * u / 2) / (Real.pi * u / 2))

lemma ellFun_eq_neg_ceEll (u : ℝ) : ellFun u = -ceEll (Real.pi * u / 2) := by
  unfold ellFun ceEll
  rw [← Real.log_inv, inv_div]

lemma ellFun_zero : ellFun 0 = 0 := by simp [ellFun]

lemma ellFun_even (u : ℝ) : ellFun (-u) = ellFun u := by
  unfold ellFun
  rw [show Real.pi * -u / 2 = -(Real.pi * u / 2) by ring, Real.tanh_neg, neg_div_neg_eq]

lemma stripG_I_mul (u : ℝ) : stripG (Complex.I * (u : ℂ)) = (ellFun u : ℂ) := by
  by_cases hu : u = 0
  · subst hu; simp [stripG, ellFun]
  · have hne : Complex.I * (u : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu)
    simp only [stripG, hne, ↓reduceIte]
    set x : ℝ := Real.pi * u / 2
    have hx0 : x ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hu) two_ne_zero
    have harg : (Real.pi : ℂ) * (Complex.I * (u : ℂ)) / 2 = (x : ℂ) * Complex.I := by
      push_cast [x]; ring
    rw [harg, Complex.tan_mul_I, mul_div_mul_right _ _ Complex.I_ne_zero]
    have hcy : Complex.tanh (x : ℂ) = (Real.tanh x : ℂ) := by
      simp [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Complex.ofReal_sinh, Complex.ofReal_cosh]
    have hpos : 0 < Real.tanh x / x := by
      rcases lt_or_gt_of_ne hx0 with hlt | hgt
      · rw [← neg_div_neg_eq, ← Real.tanh_neg]
        exact div_pos (tanh_pos_of_pos (neg_pos.mpr hlt)) (neg_pos.mpr hlt)
      · exact div_pos (tanh_pos_of_pos hgt) hgt
    rw [hcy, ← Complex.ofReal_div, ← Complex.ofReal_log hpos.le]
    rfl

lemma contDiff_ellFun : ContDiff ℝ (⊤ : ℕ∞) ellFun := by
  have hU : IsOpen edgeStrip := isOpen_edgeStrip
  have hF : ContDiffOn ℂ (⊤ : ℕ∞) stripG edgeStrip := differentiableOn_stripG.contDiffOn hU
  have hFr : ContDiffOn ℝ (⊤ : ℕ∞) stripG edgeStrip := hF.restrict_scalars ℝ
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Complex.I * (u : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hmem : ∀ u : ℝ, Complex.I * (u : ℂ) ∈ edgeStrip := fun u => by simp [edgeStrip]
  have h := hFr.comp_contDiff hℓ hmem
  have e : ellFun = fun u : ℝ => (stripG (Complex.I * (u : ℂ))).re := by
    funext u; rw [stripG_I_mul]; simp
  rw [e]
  exact Complex.reCLM.contDiff.comp h

lemma deriv_ellFun_pos_bound {t : ℝ} (ht : 0 < t) : |deriv ellFun t| ≤ 1 := by
  obtain ⟨hd, h1, h2⟩ := m2_bounds ht
  have hfun : ellFun = fun s : ℝ => -(ceEll (Real.pi * s / 2)) := funext ellFun_eq_neg_ceEll
  have hd' : HasDerivAt ellFun (edgePhiDeriv2 t) t := by
    rw [hfun]
    exact hd.neg.congr_deriv (neg_neg _)
  rw [hd'.deriv]
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have h3 : t / (1 + t ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg (t - 1)]
  have h4 : 0 ≤ t / (1 + t ^ 2) := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hpi.le h4]
  · nlinarith [h1, h4]

lemma deriv_ellFun_bound (t : ℝ) : |deriv ellFun t| ≤ 1 := by
  have hdiff : Differentiable ℝ ellFun := contDiff_ellFun.differentiable (by simp)
  have hodd : ∀ x, deriv ellFun (-x) = -deriv ellFun x := by
    intro x
    have h := congrArg (fun g => deriv g x) (show (fun y : ℝ => ellFun (-y)) = ellFun from funext ellFun_even)
    simp only [deriv_comp_neg] at h
    linarith
  rcases lt_trichotomy t 0 with h | h | h
  · have := deriv_ellFun_pos_bound (neg_pos.mpr h)
    rw [hodd, abs_neg] at this
    exact this
  · subst h
    have := hodd 0
    simp at this
    have h0 : deriv ellFun 0 = 0 := by linarith
    simp [h0]
  · exact deriv_ellFun_pos_bound h

lemma abs_ellFun_le (t : ℝ) : |ellFun t| ≤ |t| := by
  have hdiff : Differentiable ℝ ellFun := contDiff_ellFun.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := ellFun) (s := Set.univ) (C := 1)
    (fun x _ => hdiff x) (fun x _ => by simpa using deriv_ellFun_bound x) convex_univ
    (Set.mem_univ 0) (Set.mem_univ t)
  simpa [ellFun_zero] using this

/-- `N(τ) = ∫₀^τ ℓ`. -/
noncomputable def ellN (τ : ℝ) : ℝ := ∫ u in (0 : ℝ)..τ, ellFun u

lemma hasDerivAt_ellN (τ : ℝ) : HasDerivAt ellN (ellFun τ) τ := by
  have hc : Continuous ellFun := contDiff_ellFun.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

lemma deriv_ellN : deriv ellN = ellFun := funext fun τ => (hasDerivAt_ellN τ).deriv

lemma contDiff_ellN : ContDiff ℝ 3 ellN := by
  have hd : Differentiable ℝ ellN := fun τ => (hasDerivAt_ellN τ).differentiableAt
  have h : ContDiff ℝ ((2 : ℕ) + 1) ellN := by
    refine (contDiff_succ_iff_deriv (𝕜 := ℝ)).mpr ⟨hd, by simp, ?_⟩
    rw [deriv_ellN]
    exact contDiff_ellFun.of_le (by norm_cast)
  exact_mod_cast h

lemma abs_ellN_le (τ : ℝ) : |ellN τ| ≤ τ ^ 2 := by
  unfold ellN
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ) (f := ellFun) (C := |τ|)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      refine (abs_ellFun_le u).trans ?_
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hu) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.mpr ⟨by linarith [abs_nonneg τ], by linarith [le_abs_self τ]⟩
      · exact abs_le.mpr ⟨by linarith [neg_abs_le τ], by linarith [abs_nonneg τ]⟩)
  have h2 : |τ| * |τ - 0| = τ ^ 2 := by rw [sub_zero, ← _root_.sq, sq_abs]
  rw [Real.norm_eq_abs, h2] at this
  exact this

/-- info: 'FormalResearch.SignUncertainty.abs_ellN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_ellN_le

/-- info: 'FormalResearch.SignUncertainty.deriv_ellFun_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deriv_ellFun_bound

/-- info: 'FormalResearch.SignUncertainty.contDiff_ellN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_ellN

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.BinetDecay

/-!
# Binet remainder on vertical lines (`ct:dual-id` (1), decay and holomorphic extension)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (1),
equation `(ct:binet-decay)` and the extension to `Im τ > -1`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty.BinetDecay

lemma analyticOnNhd_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    have : iteratedDeriv (r + 1) f = deriv (iteratedDeriv r f) := iteratedDeriv_succ
    rw [this]
    exact ih.deriv

lemma analyticOnNhd_binetRem : AnalyticOnNhd ℂ binetRem {w : ℂ | 0 < w.re} :=
  binetRem_differentiableOn.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

lemma hasDerivAt_iteratedDeriv_binetRem (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (iteratedDeriv r binetRem) (iteratedDeriv (r + 1) binetRem w) w := by
  have h := (analyticOnNhd_iteratedDeriv analyticOnNhd_binetRem r) w hw
  have := h.differentiableAt.hasDerivAt
  rwa [← iteratedDeriv_succ] at this

/-- Chain rule for the real parameter: `∂_τ^r B_Bin(aτ+b) = a^r B_Bin^{(r)}(aτ+b)`. -/
lemma iteratedDeriv_binetRem_aff (a b : ℂ) (r : ℕ) (τ : ℝ) (h : 0 < (a * (τ : ℂ) + b).re) :
    iteratedDeriv r (fun τ : ℝ => binetRem (a * (τ : ℂ) + b)) τ =
      a ^ r * iteratedDeriv r binetRem (a * (τ : ℂ) + b) := by
  induction r generalizing τ with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have hcont : Continuous fun τ : ℝ => (a * (τ : ℂ) + b).re := by fun_prop
    have hev : ∀ᶠ τ' : ℝ in 𝓝 τ, 0 < (a * (τ' : ℂ) + b).re :=
      hcont.continuousAt.eventually (lt_mem_nhds h)
    have heq : (iteratedDeriv r fun τ : ℝ => binetRem (a * (τ : ℂ) + b)) =ᶠ[𝓝 τ]
        fun τ' : ℝ => a ^ r * iteratedDeriv r binetRem (a * (τ' : ℂ) + b) := by
      filter_upwards [hev] with τ' hτ' using ih τ' hτ'
    rw [heq.deriv_eq]
    have hh : HasDerivAt (fun τ' : ℝ => a * (τ' : ℂ) + b) a τ := by
      have := ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
      simpa using this.comp_ofReal
    have hg := hasDerivAt_iteratedDeriv_binetRem r h
    have hc : HasDerivAt (fun τ' : ℝ => a ^ r * iteratedDeriv r binetRem (a * (τ' : ℂ) + b))
        (a ^ r * (a • iteratedDeriv (r + 1) binetRem (a * (τ : ℂ) + b))) τ :=
      (hg.scomp τ hh).const_mul (a ^ r)
    rw [hc.deriv]
    simp only [smul_eq_mul, pow_succ]
    ring

/-- The `r`-th `τ`-derivative of `B_c(iτ)` for `r ≥ 1`. -/
theorem iteratedDeriv_binetDiff_vertical {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) (τ : ℝ) :
    iteratedDeriv r (fun τ : ℝ => binetDiff c (Complex.I * (τ : ℂ))) τ =
      (-(Complex.I * (c : ℂ))) ^ r *
        iteratedDeriv r binetRem ((c : ℂ) * (1 - Complex.I * (τ : ℂ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
  have hfun : (fun τ : ℝ => binetDiff c (Complex.I * (τ : ℂ))) =
      fun τ : ℝ => binetRem ((-(Complex.I * (c : ℂ))) * (τ : ℂ) + (c : ℂ)) - binetRem (c : ℂ) := by
    funext τ
    unfold binetDiff
    congr 2
    ring
  have hre : 0 < ((-(Complex.I * (c : ℂ))) * (τ : ℂ) + (c : ℂ)).re := by simpa using hc
  rw [hfun, iteratedDeriv_succ']
  have hd : deriv (fun τ : ℝ => binetRem ((-(Complex.I * (c : ℂ))) * (τ : ℂ) + (c : ℂ)) - binetRem (c : ℂ)) =
      deriv (fun τ : ℝ => binetRem ((-(Complex.I * (c : ℂ))) * (τ : ℂ) + (c : ℂ))) := by
    funext x
    exact deriv_sub_const _
  rw [hd, ← iteratedDeriv_succ', iteratedDeriv_binetRem_aff _ _ _ _ hre]
  have : (-(Complex.I * (c : ℂ))) * (τ : ℂ) + (c : ℂ) = (c : ℂ) * (1 - Complex.I * (τ : ℂ)) := by ring
  rw [this]

lemma norm_c_one_sub_ge {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    c * (1 + |τ|) / 2 ≤ ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖ := by
  have h1 : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]
  have hn : ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖ = c * Real.sqrt (1 + τ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    congr 1
    have : (1 - Complex.I * (τ : ℂ)) = ⟨1, -τ⟩ := by apply Complex.ext <;> simp
    rw [this, Complex.norm_def, Complex.normSq_mk]
    congr 1; ring
  rw [hn]
  have : (1 + |τ|) / 2 ≤ Real.sqrt (1 + τ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  nlinarith

/-- **Binet vertical-line decay** (`(ct:binet-decay)`): for `c > 0`, `r ≥ 1` and real `τ`,
`|∂_τ^r B_c(iτ)| ≤ r! 4^r / (c (1+|τ|)^{r+1})`. -/
theorem binetDiff_vertical_decay {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) (τ : ℝ) :
    ‖iteratedDeriv r (fun τ : ℝ => binetDiff c (Complex.I * (τ : ℂ))) τ‖ ≤
      (r.factorial : ℝ) * 4 ^ r / (c * (1 + |τ|) ^ (r + 1)) := by
  rw [iteratedDeriv_binetDiff_vertical hc hr, norm_mul, norm_pow, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.norm_I, one_mul]
  have hw : 0 < ((c : ℂ) * (1 - Complex.I * (τ : ℂ))).re := by simpa using hc
  have hb := binetRem_iteratedDeriv_decay r hw
  have hlow := norm_c_one_sub_ge hc τ
  have hpos : 0 < c * (1 + |τ|) / 2 := by positivity
  have hpow : (c * (1 + |τ|) / 2) ^ (r + 1) ≤ ‖(c : ℂ) * (1 - Complex.I * (τ : ℂ))‖ ^ (r + 1) :=
    pow_le_pow_left₀ hpos.le hlow _
  have hb2 : ‖iteratedDeriv r binetRem ((c : ℂ) * (1 - Complex.I * (τ : ℂ)))‖ ≤
      (r.factorial : ℝ) * 2 ^ (r + 2) / (8 * (c * (1 + |τ|) / 2) ^ (r + 1)) :=
    hb.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  calc c ^ r * ‖iteratedDeriv r binetRem ((c : ℂ) * (1 - Complex.I * (τ : ℂ)))‖
      ≤ c ^ r * ((r.factorial : ℝ) * 2 ^ (r + 2) / (8 * (c * (1 + |τ|) / 2) ^ (r + 1))) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = (r.factorial : ℝ) * 4 ^ r / (c * (1 + |τ|) ^ (r + 1)) := by
        have hc0 : c ≠ 0 := hc.ne'
        have h1 : (1 + |τ|) ≠ 0 := by positivity
        rw [div_pow, mul_pow]
        field_simp
        rw [show (4 : ℝ) ^ r = 2 ^ r * 2 ^ r by rw [← mul_pow]; norm_num]
        ring

/-- **Holomorphic extension** of `τ ↦ B_c(iτ)` to `{Im τ > -1}`. -/
theorem differentiableOn_binetDiff_vertical {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (fun τ : ℂ => binetDiff c (Complex.I * τ)) {τ : ℂ | -1 < τ.im} := by
  intro τ hτ
  have hre : 0 < ((c : ℂ) * (1 - Complex.I * τ)).re := by
    have : ((c : ℂ) * (1 - Complex.I * τ)).re = c * (1 + τ.im) := by simp
    rw [this]
    have : -1 < τ.im := hτ
    exact mul_pos hc (by linarith)
  have h1 : DifferentiableAt ℂ (fun τ : ℂ => binetRem ((c : ℂ) * (1 - Complex.I * τ))) τ := by
    have hb := (binetRem_differentiableOn _ hre).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)
    exact DifferentiableAt.comp (g := binetRem) (f := fun τ : ℂ => (c : ℂ) * (1 - Complex.I * τ)) τ hb
      ((differentiableAt_id.const_mul Complex.I).const_sub 1 |>.const_mul (c : ℂ))
  exact (h1.sub_const _).differentiableWithinAt

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.iteratedDeriv_binetDiff_vertical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_binetDiff_vertical

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.binetDiff_vertical_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binetDiff_vertical_decay

/-- info: 'FormalResearch.SignUncertainty.BinetDecay.differentiableOn_binetDiff_vertical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_binetDiff_vertical

end FormalResearch.SignUncertainty.BinetDecay

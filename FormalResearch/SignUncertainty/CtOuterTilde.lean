module

public import FormalResearch.SignUncertainty.CtOuterLogId
public import FormalResearch.SignUncertainty.BinetVertical

/-!
# The amplitude `ũ` and the identity `θ_- = -π/2 + Im h̃(iτ)`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (3).  **Proved.**

`ũ(t) = ½ log(1 - π|t|/sinh(π|t|))` (here `utl = u_r + w` with `w = ½ log((π²/6) t² (1+t²))`), and for `τ > 0`
`θ_-(τ) = -π/2 + ∫ (ũ(t) - ũ(τ))/sinh(π(t-τ)) dt`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `ũ = u_r + w`. -/
noncomputable def utl (t : ℝ) : ℝ := uR t + wpl t

lemma bdryF_add {a b : ℝ → ℝ} {τ δ : ℝ} (hδ : 0 < δ) (ha : Measurable a) (hb : Measurable b) {Ma Mb : ℝ}
    (hMa : ∀ t, |a t| ≤ Ma * wlog t) (hMb : ∀ t, |b t| ≤ Mb * wlog t) {La Lb : ℝ}
    (hLa : ∀ t, |t - τ| ≤ δ → |a t - a τ| ≤ La * |t - τ|) (hLb : ∀ t, |t - τ| ≤ δ → |b t - b τ| ≤ Lb * |t - τ|) :
    bdryF (fun t => a t + b t) τ = bdryF a τ + bdryF b τ := by
  have ia := integrable_bdry_major ha hMa hδ hLa
  have ib := integrable_bdry_major hb hMb hδ hLb
  have ja : Integrable fun t : ℝ => (a t - a τ) / Real.sinh (π * (t - τ)) := by
    refine Integrable.mono' ia ?_ (Eventually.of_forall fun t => ?_)
    · exact ((ha.sub measurable_const).div (by fun_prop : Measurable fun t : ℝ => Real.sinh (π * (t - τ)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_div]
  have jb : Integrable fun t : ℝ => (b t - b τ) / Real.sinh (π * (t - τ)) := by
    refine Integrable.mono' ib ?_ (Eventually.of_forall fun t => ?_)
    · exact ((hb.sub measurable_const).div (by fun_prop : Measurable fun t : ℝ => Real.sinh (π * (t - τ)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_div]
  unfold bdryF
  rw [← integral_add ja jb]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  ring

/-- **`θ_-(τ) = -π/2 + F_ũ(τ)` for `τ > 0`.** -/
theorem outerTheta_neg_eq_utl {τ : ℝ} (hτ : 0 < τ) : outerTheta (-1) τ = bdryF utl τ - π / 2 := by
  obtain ⟨M, hM⟩ := uR_wlog
  obtain ⟨L, hL⟩ := uR_lipschitz τ
  obtain ⟨L', hL'⟩ := wpl_lipschitz hτ
  have h := bdryF_add (a := uR) (b := wpl) (δ := min 1 (τ / 2)) (lt_min one_pos (half_pos hτ)) continuous_uR.measurable
    measurable_wpl hM wpl_bound (La := L) (Lb := L')
    (fun t ht => hL t (ht.trans (min_le_left _ _))) (fun t ht => hL' t (ht.trans (min_le_right _ _)))
  rw [outerTheta_neg_eq]
  have e : bdryF utl τ = bdryF uR τ + bdryF wpl τ := h
  rw [e, bdryF_wpl hτ]
  ring


/-- For `t > 0`: `ũ(t) = ½ log(1 - πt/sinh(πt))`. -/
lemma utl_eq_log {t : ℝ} (ht : 0 < t) : utl t = (1 / 2) * Real.log (1 - π * t / Real.sinh (π * t)) := by
  unfold utl wpl
  have hN := mPrime_pos ht
  have hpi := Real.pi_pos
  rw [uR_eq ht.ne', abs_of_pos ht]
  unfold Freal
  have hX : 1 - π * t / Real.sinh (π * t) = mPrime t * t := by
    unfold mPrime
    have hs : Real.sinh (π * t) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    field_simp
  rw [hX]
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have hF : 0 < 6 / π ^ 2 * mPrime t / (t * (1 + t ^ 2)) := by positivity
  have hprod : 6 / π ^ 2 * mPrime t / (t * (1 + t ^ 2)) * t ^ 2 * (1 + t ^ 2) * (π ^ 2 / 6) = mPrime t * t := by
    field_simp
  have hlog : Real.log (6 / π ^ 2 * mPrime t / (t * (1 + t ^ 2))) + Real.log (t ^ 2) + Real.log (1 + t ^ 2) +
      Real.log (π ^ 2 / 6) = Real.log (mPrime t * t) := by
    rw [← hprod, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  unfold cLog
  have h2 : Real.log (t ^ 2) = 2 * Real.log t := by rw [Real.log_pow]; push_cast; ring
  linarith only [hlog, h2]

/-- Complex extension `ũ_c(z) = ½ Log(1 - πz/sinh(πz))`. -/
noncomputable def utlC (z : ℂ) : ℂ := (1 / 2) * Complex.log (1 - π * z / Complex.sinh (π * z))

lemma norm_sinh_ge (z : ℂ) : Real.sinh |z.re| ≤ ‖Complex.sinh z‖ := by
  have h := norm_sin_sq (z * Complex.I)
  have e : Complex.sin (z * Complex.I) = Complex.sinh z * Complex.I := Complex.sin_mul_I z
  have hn : ‖Complex.sin (z * Complex.I)‖ = ‖Complex.sinh z‖ := by rw [e, norm_mul, Complex.norm_I, mul_one]
  rw [hn] at h
  have hre : (z * Complex.I).re = -z.im := by simp
  have him : (z * Complex.I).im = z.re := by simp
  rw [hre, him] at h
  have h0 : Real.sinh z.re ^ 2 ≤ ‖Complex.sinh z‖ ^ 2 := by
    rw [h]; nlinarith only [sq_nonneg (Real.sin (-z.im))]
  have h1 : Real.sinh |z.re| = |Real.sinh z.re| := by
    rcases le_total 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h0)]
    · rw [abs_of_nonpos h0, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h0), Real.sinh_neg]
  rw [h1]
  exact le_of_sq_le_sq (by rw [sq_abs]; exact h0) (norm_nonneg _)


/-- `‖πz/sinh(πz)‖ ≤ 4π e^π (t+1) e^{-πt}` on the disc `|z - t| ≤ 1`, `t ≥ 4`. -/
lemma eps_bound {t : ℝ} (ht : 4 ≤ t) {z : ℂ} (hz : z ∈ closedBall (t : ℂ) 1) :
    Complex.sinh (π * z) ≠ 0 ∧
      ‖(π : ℂ) * z / Complex.sinh (π * z)‖ ≤ 4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by
  have hd : ‖z - t‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hre : t - 1 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - t)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith [(abs_le.mp this).1]
  have hnz : ‖z‖ ≤ t + 1 := by
    have : ‖z‖ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := by
      calc ‖z‖ = ‖(z - t) + t‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
    linarith
  have hpre : (π * z).re = π * z.re := by simp [Complex.mul_re]
  have hge : Real.sinh |(π * z).re| ≤ ‖Complex.sinh (π * z)‖ := norm_sinh_ge _
  have hpos : 0 ≤ π * z.re := by nlinarith [Real.pi_pos]
  rw [hpre, abs_of_nonneg hpos] at hge
  have h1 : 1 ≤ π * z.re := by nlinarith [Real.pi_gt_three]
  have h2 := exp_div_four_le_sinh h1
  have hlow : Real.exp (π * z.re) / 4 ≤ ‖Complex.sinh (π * z)‖ := h2.trans hge
  have hpos' : 0 < Real.exp (π * z.re) / 4 := by positivity
  have hne : Complex.sinh (π * z) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  refine ⟨hne, ?_⟩
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hsn : 0 < ‖Complex.sinh (π * z)‖ := norm_pos_iff.mpr hne
  calc π * ‖z‖ / ‖Complex.sinh (π * z)‖ ≤ π * (t + 1) / (Real.exp (π * z.re) / 4) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnz Real.pi_pos.le) hpos' hlow
    _ = 4 * π * (t + 1) * Real.exp (-(π * z.re)) := by rw [Real.exp_neg]; field_simp
    _ ≤ 4 * π * (t + 1) * Real.exp (-(π * (t - 1))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) (by positivity)
    _ = 4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by
        rw [show -(π * (t - 1)) = π + -π * t by ring, Real.exp_add]; ring

lemma eps_small {t : ℝ} (ht : 4 ≤ t) : 4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) ≤ 1 / 2 := by
  have h1 : t + 1 ≤ 5 * Real.exp (π * (t - 4)) := by
    have := Real.add_one_le_exp (π * (t - 4))
    nlinarith only [this, Real.pi_gt_three, ht]
  have h2 : (t + 1) * Real.exp (-π * t) ≤ 5 * Real.exp (-(4 * π)) := by
    calc (t + 1) * Real.exp (-π * t) ≤ 5 * Real.exp (π * (t - 4)) * Real.exp (-π * t) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 5 * Real.exp (-(4 * π)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h3 : (2 : ℝ) ^ 9 ≤ Real.exp (3 * π) := by
    have : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h4 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 9 ≤ Real.exp (3 * π) := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    calc (2 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) this 9
      _ = Real.exp 9 := h4.symm
      _ ≤ _ := h5
  have h6 : Real.exp π * Real.exp (-(4 * π)) = Real.exp (-(3 * π)) := by rw [← Real.exp_add]; ring_nf
  have h7 : Real.exp (-(3 * π)) * Real.exp (3 * π) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(3 * π))
  calc 4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) ≤ 4 * π * Real.exp π * (5 * Real.exp (-(4 * π))) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 20 * π * Real.exp (-(3 * π)) := by rw [← h6]; ring
    _ ≤ 1 / 2 := by
        have hπ : π ≤ 4 := Real.pi_le_four
        nlinarith only [h3, h7, hE, hπ, Real.pi_pos]


/-- The open region where `ũ_c` is controlled. -/
def regU : Set ℂ := {z : ℂ | 4 < z.re ∧ |z.im| < 1}

lemma isOpen_regU : IsOpen regU :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

lemma mem_closedBall_re {z : ℂ} (hz : z ∈ regU) : z ∈ closedBall ((z.re : ℝ) : ℂ) 1 := by
  rw [mem_closedBall, dist_eq_norm]
  have : z - ((z.re : ℝ) : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  exact hz.2.le

lemma differentiableOn_utlC : DifferentiableOn ℂ utlC regU := by
  intro z hz
  obtain ⟨hne, hb⟩ := eps_bound (t := z.re) hz.1.le (mem_closedBall_re hz)
  have hsm := hb.trans (eps_small hz.1.le)
  have hslit : (1 - π * z / Complex.sinh (π * z)) ∈ slitPlane := by
    left
    have := Complex.abs_re_le_norm ((π : ℂ) * z / Complex.sinh (π * z))
    have h2 := (abs_le.mp (this.trans hsm)).2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * z / Complex.sinh (π * z)) z :=
    (differentiableAt_const _ |>.mul differentiableAt_id).div
      ((Complex.differentiableAt_sinh).comp z ((differentiableAt_const _ |>.mul differentiableAt_id))) hne
  have := ((differentiableAt_const (1 : ℂ)).sub h1).clog hslit
  unfold utlC
  exact (this.const_mul _).differentiableWithinAt

lemma utlC_ofReal {t : ℝ} (ht : 0 < t) : utlC (t : ℂ) = ((utl t : ℝ) : ℂ) := by
  rw [utl_eq_log ht]
  unfold utlC
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : 0 < 1 - π * t / Real.sinh (π * t) := by
    have := FormalResearch.CohnElkies.sinh_gt_id (show 0 < π * t by positivity)
    rw [sub_pos, div_lt_one hs]; exact this
  have e : (1 : ℂ) - (π : ℂ) * (t : ℂ) / Complex.sinh (π * (t : ℂ)) = ((1 - π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sinh]
    push_cast; ring
  rw [e, ← Complex.ofReal_log h1.le]
  push_cast; ring

lemma norm_utlC_le {t : ℝ} (ht : 4 ≤ t) {z : ℂ} (hz : z ∈ closedBall (t : ℂ) 1) :
    ‖utlC z‖ ≤ 3 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by
  obtain ⟨hne, hb⟩ := eps_bound ht hz
  have hsm := hb.trans (eps_small ht)
  unfold utlC
  rw [norm_mul]
  have hlog := Complex.norm_log_one_add_half_le_self (z := -((π : ℂ) * z / Complex.sinh (π * z)))
    (by rwa [norm_neg])
  rw [norm_neg, ← sub_eq_add_neg] at hlog
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  have hpos : 0 ≤ 4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by
    have : 0 ≤ t + 1 := by linarith
    positivity
  calc 1 / 2 * ‖Complex.log (1 - (π : ℂ) * z / Complex.sinh (π * z))‖
      ≤ 1 / 2 * (3 / 2 * ‖(π : ℂ) * z / Complex.sinh (π * z)‖) := by gcongr
    _ ≤ 1 / 2 * (3 / 2 * (4 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)))) := by gcongr
    _ = 3 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by ring


/-- Iterated real derivatives of `f` are the iterated complex derivatives of a holomorphic extension `F` that agrees
with `f` on the real points of `U`. -/
lemma iteratedDeriv_ofReal_eq {f : ℝ → ℝ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hfF : ∀ t : ℝ, (t : ℂ) ∈ U → F (t : ℂ) = ((f t : ℝ) : ℂ)) :
    ∀ (n : ℕ) (t : ℝ), (t : ℂ) ∈ U → ((iteratedDeriv n f t : ℝ) : ℂ) = iteratedDeriv n F (t : ℂ) := by
  intro n
  induction n with
  | zero => intro t ht; simp [hfF t ht]
  | succ n ih =>
    intro t ht
    have han := FormalResearch.SignUncertainty.BinetDecay.analyticOnNhd_iteratedDeriv
      (hF.analyticOnNhd hU) n
    have hG : HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n + 1) F (t : ℂ)) (t : ℂ) := by
      have := (han (t : ℂ) ht).differentiableAt.hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    have hG' : HasDerivAt (fun s : ℝ => iteratedDeriv n F (s : ℂ)) (iteratedDeriv (n + 1) F (t : ℂ)) t :=
      hG.comp_ofReal
    have hev : (fun s : ℝ => ((iteratedDeriv n f s : ℝ) : ℂ)) =ᶠ[𝓝 t] fun s : ℝ => iteratedDeriv n F (s : ℂ) := by
      have : ∀ᶠ s : ℝ in 𝓝 t, (s : ℂ) ∈ U :=
        (Complex.continuous_ofReal.continuousAt.eventually (hU.mem_nhds ht))
      filter_upwards [this] with s hs using ih s hs
    have h1 : HasDerivAt (fun s : ℝ => ((iteratedDeriv n f s : ℝ) : ℂ)) (iteratedDeriv (n + 1) F (t : ℂ)) t :=
      hG'.congr_of_eventuallyEq hev
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (iteratedDeriv n f) ((iteratedDeriv (n + 1) F (t : ℂ)).re) t := by
      have e : (⇑Complex.reCLM ∘ fun s : ℝ => ((iteratedDeriv n f s : ℝ) : ℂ)) = iteratedDeriv n f := by
        funext s; simp
      rw [e] at h2
      simpa using h2
    have h4 : HasDerivAt (fun s : ℝ => ((iteratedDeriv n f s : ℝ) : ℂ))
        (((iteratedDeriv (n + 1) F (t : ℂ)).re : ℝ) : ℂ) t := h3.ofReal_comp
    have h5 := h1.unique h4
    rw [iteratedDeriv_succ, h3.deriv]
    exact h5.symm


/-- **Derivative bounds for `ũ` at infinity** (Cauchy estimates on the discs `|z - t| = 1/2`):
`|ũ^{(n)}(t)| ≤ K_n (t+1) e^{-πt}` for `t ≥ 5`. -/
theorem utl_deriv_bound (n : ℕ) :
    ∃ K : ℝ, ∀ t : ℝ, 5 ≤ t → |iteratedDeriv n utl t| ≤ K * ((t + 1) * Real.exp (-π * t)) := by
  refine ⟨n.factorial * 2 ^ n * (3 * π * Real.exp π), fun t ht => ?_⟩
  have htU : (t : ℂ) ∈ regU := ⟨by simpa using (by linarith : (4 : ℝ) < t), by simp⟩
  have h := iteratedDeriv_ofReal_eq (f := utl) (F := utlC) isOpen_regU differentiableOn_utlC
    (fun s hs => utlC_ofReal (by have := hs.1; simp at this; linarith)) n t htU
  have hsub : closedBall (t : ℂ) (1 / 2) ⊆ regU := by
    intro z hz
    have hd : ‖z - t‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm] using hz
    refine ⟨?_, ?_⟩
    · have := Complex.abs_re_le_norm (z - t)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith [(abs_le.mp this).1]
    · have := Complex.abs_im_le_norm (z - t)
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
  have hdc : DiffContOnCl ℂ utlC (ball (t : ℂ) (1 / 2)) := by
    have : DifferentiableOn ℂ utlC (closure (ball (t : ℂ) (1 / 2))) := by
      rw [closure_ball _ (by norm_num)]
      exact differentiableOn_utlC.mono hsub
    exact this.diffContOnCl
  have hbd : ∀ z ∈ sphere (t : ℂ) (1 / 2), ‖utlC z‖ ≤ 3 * π * Real.exp π * ((t + 1) * Real.exp (-π * t)) := by
    intro z hz
    refine norm_utlC_le (by linarith) ?_
    rw [mem_closedBall]
    have : dist z t = 1 / 2 := hz
    linarith
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num : (0 : ℝ) < 1 / 2) hdc hbd
  have h2 : |iteratedDeriv n utl t| = ‖iteratedDeriv n utlC (t : ℂ)‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  refine hC.trans (le_of_eq ?_)
  rw [div_pow, one_pow]
  field_simp

/-- info: 'FormalResearch.SignUncertainty.CtOuter.outerTheta_neg_eq_utl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerTheta_neg_eq_utl

/-- info: 'FormalResearch.SignUncertainty.CtOuter.utl_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms utl_deriv_bound

end FormalResearch.SignUncertainty.CtOuter

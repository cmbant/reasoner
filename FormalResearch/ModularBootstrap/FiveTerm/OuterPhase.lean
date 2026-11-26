module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterPL

/-!
# The phase of `h̄_a` on the left edge: `Im H_xb(it) = (1/4)(arctan sinh πt - arctan 2 v_T(t))` (FIVE-S)

From `exp(4 H_xb) = K̄` (`OuterPL`) and the explicit edge value of `K̄`
(`K̄(it) = c(t) (1 + i sinh πt)(1/2 - i v_T(t))` with `c > 0`) one gets
`4 Im H_xb(it) ≡ arctan sinh πt - arctan 2 v_T(t) (mod 2π)`; both sides are continuous in `t` and vanish at `t = 0`.
Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- Polar form of `a + b i` with `a > 0`. -/
lemma polar_aux {a b : ℝ} (ha : 0 < a) :
    (a : ℂ) + (b : ℂ) * Complex.I =
      ((√(a ^ 2 + b ^ 2) : ℝ) : ℂ) * Complex.exp (((Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan, Real.sin_arctan]
  have h1 : 0 < 1 + (b / a) ^ 2 := by positivity
  have hs : 0 < √(1 + (b / a) ^ 2) := Real.sqrt_pos.mpr h1
  have h2 : √(a ^ 2 + b ^ 2) = a * √(1 + (b / a) ^ 2) := by
    rw [show a ^ 2 + b ^ 2 = a ^ 2 * (1 + (b / a) ^ 2) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  rw [h2]
  generalize √(1 + (b / a) ^ 2) = r at hs ⊢
  push_cast
  have hs' : (r : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp

/-- A continuous function with values in `2πℤ` on `(0, ∞)` and `D 0 = 0` vanishes on `[0, ∞)`. -/
lemma zero_of_int_cont {D : ℝ → ℝ} (hc : ContinuousOn D (Ici 0)) (h0 : D 0 = 0)
    (hz : ∀ t, 0 < t → ∃ n : ℤ, D t = 2 * π * n) : ∀ t, 0 ≤ t → D t = 0 := by
  intro t0 ht0
  rcases ht0.eq_or_lt with h | h
  · rw [← h]; exact h0
  by_contra hne
  obtain ⟨n, hn⟩ := hz t0 h
  have hpi := Real.pi_pos
  have hn0 : n ≠ 0 := by
    rintro rfl; apply hne; simpa using hn
  have hIcc : ContinuousOn D (Icc 0 t0) := hc.mono (fun x hx => hx.1)
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have hn1 : n ≤ -1 := by omega
    have hD : D t0 ≤ -(2 * π) := by
      rw [hn]
      have : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
      nlinarith
    obtain ⟨t1, ht1, hv⟩ := intermediate_value_Icc' h.le hIcc (show -π ∈ Icc (D t0) (D 0) from
      ⟨by linarith, by rw [h0]; linarith⟩)
    have ht1pos : 0 < t1 := by
      rcases ht1.1.eq_or_lt with h' | h'
      · rw [← h', h0] at hv; linarith
      · exact h'
    obtain ⟨m, hm⟩ := hz t1 ht1pos
    rw [hv] at hm
    have : (2 * m + 1 : ℝ) * π = 0 := by linarith
    have h3 : (2 * (m : ℝ) + 1) = 0 := by
      rcases mul_eq_zero.mp this with h4 | h4
      · exact h4
      · exact absurd h4 hpi.ne'
    have : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  · have hn1 : 1 ≤ n := by omega
    have hD : 2 * π ≤ D t0 := by
      rw [hn]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
    obtain ⟨t1, ht1, hv⟩ := intermediate_value_Icc h.le hIcc (show π ∈ Icc (D 0) (D t0) from
      ⟨by rw [h0]; linarith, by linarith⟩)
    have ht1pos : 0 < t1 := by
      rcases ht1.1.eq_or_lt with h' | h'
      · rw [← h', h0] at hv; linarith
      · exact h'
    obtain ⟨m, hm⟩ := hz t1 ht1pos
    rw [hv] at hm
    have : (2 * m - 1 : ℝ) * π = 0 := by linarith
    have h3 : (2 * (m : ℝ) - 1) = 0 := by
      rcases mul_eq_zero.mp this with h4 | h4
      · exact h4
      · exact absurd h4 hpi.ne'
    have : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h3
    omega


/-- The phase function `θ(t) = arctan sinh πt - arctan 2 v_T(t)`. -/
noncomputable def thetaXb (t : ℝ) : ℝ := Real.arctan (Real.sinh (π * t)) - Real.arctan (2 * vT t)

lemma slitVal_tanh {t : ℝ} (ht : 0 < t) :
    slitVal (Real.tanh (π * t / 4)) = ((1 / 2 : ℝ) + (-(vT t) : ℝ) * Complex.I) / (xT t : ℂ) := by
  have hpi := Real.pi_pos
  have hx := xT_pos t
  have hxo : Real.arsinh (√(uSlit (Real.tanh (π * t / 4)))) = π * xT t := by
    have := xOf_tanh t
    unfold xOf at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this]; ring
  have hvo : Real.arsinh (√(uSlit (Real.tanh (π * t / 4)) - 1)) = π * vT t := by
    have := vOf_tanh ht.le
    unfold vOf at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this]; ring
  unfold slitVal
  rw [hxo, hvo]
  have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hx' : (xT t : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp
  ring

lemma Kb_left_polar {t : ℝ} (ht : 0 < t) :
    ∃ R : ℝ, 0 < R ∧ Kb ((t : ℂ) * Complex.I) = (R : ℂ) * Complex.exp ((thetaXb t : ℝ) * Complex.I) := by
  have hpi := Real.pi_pos
  have hx := xT_pos t
  have hxi := xiStar_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hy0 : 0 < Real.tanh (π * t / 4) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have hy1 : Real.tanh (π * t / 4) < 1 := Real.tanh_lt_one _
  have hlim : Tendsto qHat (𝓝[halfDisc] (sTan ((t : ℂ) * Complex.I)))
      (𝓝 (slitVal (Real.tanh (π * t / 4)))) := by
    rw [sTan_I_mul]; exact tendsto_qHat_slit hy0 hy1
  rw [Kb_left_val (by simp) hlim, slitVal_tanh ht, gS_left]
  have hsin : Complex.sin ((π : ℂ) * ((t : ℂ) * Complex.I)) = ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by
    have : (π : ℂ) * ((t : ℂ) * Complex.I) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hsin]
  have p1 := polar_aux (a := 1) (b := Real.sinh (π * t)) one_pos
  have p2 := polar_aux (a := 1 / 2) (b := -(vT t)) (by norm_num)
  have e1 : (1 : ℂ) + ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I =
      ((1 : ℝ) : ℂ) + ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by simp
  rw [e1, p1, p2]
  set Cc : ℝ := (π * xT t / √(Real.cosh (π * t))) ^ 2 / (xT t * (π ^ 2 * xiStar ^ 2)) with hCc
  have hCpos : 0 < Cc := by
    have := Real.sqrt_pos.mpr hc
    positivity
  refine ⟨Cc * √(1 ^ 2 + Real.sinh (π * t) ^ 2) * √((1 / 2) ^ 2 + (-(vT t)) ^ 2), by positivity, ?_⟩
  have hth : (thetaXb t : ℝ) = Real.arctan (Real.sinh (π * t) / 1) + Real.arctan (-(vT t) / (1 / 2)) := by
    unfold thetaXb
    rw [div_one, show -(vT t) / (1 / 2) = -(2 * vT t) by ring, Real.arctan_neg]; ring
  rw [hth]
  push_cast
  rw [add_mul, Complex.exp_add]
  have hx' : (xT t : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hxi' : (xiStar : ℂ) ≠ 0 := by exact_mod_cast hxi.ne'
  simp only [hCc]
  push_cast
  field_simp


lemma continuous_thetaXb : Continuous thetaXb := by
  unfold thetaXb
  exact (Real.continuous_arctan.comp (Real.continuous_sinh.comp (by fun_prop))).sub
    (Real.continuous_arctan.comp (continuous_const.mul continuous_vT))

lemma thetaXb_zero : thetaXb 0 = 0 := by
  unfold thetaXb; rw [vT_zero]; simp

lemma thetaXb_neg (t : ℝ) : thetaXb (-t) = -thetaXb t := by
  unfold thetaXb
  rw [vT_odd, show π * -t = -(π * t) by ring, Real.sinh_neg, mul_neg, Real.arctan_neg, Real.arctan_neg]; ring

lemma Hxb_edge_mem (t : ℝ) : (t : ℂ) * Complex.I ∈ closedStrip := ⟨by simp, by simp⟩

lemma continuousOn_im_Hxb_edge : Continuous fun t : ℝ => (Hxb ((t : ℂ) * Complex.I)).im := by
  have h : ContinuousOn (fun t : ℝ => Hxb ((t : ℂ) * Complex.I)) univ := by
    refine continuousOn_Hxb.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * Complex.I).continuousOn
      (fun t _ => Hxb_edge_mem t)
  exact Complex.continuous_im.comp (continuousOn_univ.mp h)

lemma exists_int_im_Hxb {t : ℝ} (ht : 0 < t) :
    ∃ n : ℤ, 4 * (Hxb ((t : ℂ) * Complex.I)).im - thetaXb t = 2 * π * n := by
  obtain ⟨R, hR, hK⟩ := Kb_left_polar ht
  have h := exp_four_Hxb (s := (t : ℂ) * Complex.I) ⟨by simp, by simp⟩
  rw [hK] at h
  set w : ℂ := (4 : ℂ) * Hxb ((t : ℂ) * Complex.I) - ((thetaXb t : ℝ) : ℂ) * Complex.I with hw
  have hexp : Complex.exp w = (R : ℂ) := by
    rw [hw, Complex.exp_sub, h]
    have : Complex.exp (((thetaXb t : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have h1 : Complex.exp (w - ((Real.log R : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_sub, hexp, ← Complex.ofReal_exp, Real.exp_log hR]
    have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp [hw] at this
  linarith

lemma im_Hxb_zero : (Hxb ((0 : ℝ) * Complex.I : ℂ)).im = 0 := by
  have := im_Hxb_real (s := 0) ⟨by simp, by simp⟩ (by simp)
  simpa using this

lemma im_Hxb_left_nonneg {t : ℝ} (ht : 0 ≤ t) : (Hxb ((t : ℂ) * Complex.I)).im = thetaXb t / 4 := by
  have hD : ∀ t : ℝ, 0 ≤ t → 4 * (Hxb ((t : ℂ) * Complex.I)).im - thetaXb t = 0 := by
    refine zero_of_int_cont (D := fun t => 4 * (Hxb ((t : ℂ) * Complex.I)).im - thetaXb t)
      ((continuousOn_im_Hxb_edge.const_smul (4 : ℝ) |>.sub continuous_thetaXb).continuousOn) ?_ ?_
    · simp only [Complex.ofReal_zero, zero_mul]
      have := im_Hxb_zero
      simp only [Complex.ofReal_zero, zero_mul] at this
      rw [this, thetaXb_zero]; ring
    · intro t ht
      exact exists_int_im_Hxb ht
  have := hD t ht
  linarith

/-- **The phase on the left edge.** -/
theorem im_Hxb_left_edge (t : ℝ) : (Hxb ((t : ℂ) * Complex.I)).im = thetaXb t / 4 := by
  rcases le_total 0 t with ht | ht
  · exact im_Hxb_left_nonneg ht
  · have h := im_Hxb_left_nonneg (t := -t) (by linarith)
    have hconj : Hxb (((-t : ℝ) : ℂ) * Complex.I) = starRingEnd ℂ (Hxb ((t : ℂ) * Complex.I)) := by
      unfold Hxb
      have e : ((-t : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((t : ℂ) * Complex.I) := by simp
      rw [e, hbarA_conj amp_aAmp (Hxb_edge_mem t), hbarA_conj amp_aRest (Hxb_edge_mem t), map_sub]
    rw [hconj, Complex.conj_im, thetaXb_neg] at h
    linarith

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.im_Hxb_left_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_Hxb_left_edge

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

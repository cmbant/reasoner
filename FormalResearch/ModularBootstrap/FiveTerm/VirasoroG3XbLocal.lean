module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Main

/-!
# Local structure of `Ψ̂` at the corners `s = 0` and `s = 1` (FIVE-0b, third-order strip identity)

`Ψ̂` extends holomorphically across the corner `s = 0` (an even function `psiOne (gS, kC, cC)`) and across
`s = 1` (as `Φ(k(s))`, `Φ` holomorphic at `k = 0`).  This file builds both extensions, shows that
`Ψ̂ - p` vanishes to second order at the corners for a suitable even-in-`s` comparison function
`p(s) = P₀ + P₁ cos πs + P₂ sin πs sin(πs/2)`, and bounds `(Ψ̂ - p)/sin²(πs)` near the corners.
Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- A function holomorphic near `z₀` with a double zero there, divided by the square of a function with a simple
zero, is bounded on a punctured neighbourhood. -/
lemma quad_div_bdd {R σ : ℂ → ℂ} {z0 d : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : DifferentiableOn ℂ R (ball z0 r)) (hR0 : R z0 = 0) (hR1 : HasDerivAt R 0 z0)
    (hσ : DifferentiableOn ℂ σ (ball z0 r)) (hσ0 : σ z0 = 0) (hσ1 : HasDerivAt σ d z0) (hd : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ s : ℂ, ‖s - z0‖ < δ → s ≠ z0 → ‖R s / σ s ^ 2‖ ≤ M := by
  have hnh : ball z0 r ∈ 𝓝 z0 := isOpen_ball.mem_nhds (mem_ball_self hr)
  have hD1 : DifferentiableOn ℂ (dslope R z0) (ball z0 r) :=
    (Complex.differentiableOn_dslope hnh).mpr hR
  have hD2 : DifferentiableOn ℂ (dslope (dslope R z0) z0) (ball z0 r) :=
    (Complex.differentiableOn_dslope hnh).mpr hD1
  have hS : DifferentiableOn ℂ (dslope σ z0) (ball z0 r) :=
    (Complex.differentiableOn_dslope hnh).mpr hσ
  have hD10 : dslope R z0 z0 = 0 := by rw [dslope_same, hR1.deriv]
  have hS0 : dslope σ z0 z0 = d := by rw [dslope_same, hσ1.deriv]
  have hSc : ContinuousAt (dslope σ z0) z0 := (hS.differentiableAt hnh).continuousAt
  have hev : ∀ᶠ s in 𝓝 z0, ‖d‖ / 2 < ‖dslope σ z0 s‖ := by
    have := hSc.norm.eventually (lt_mem_nhds (show ‖d‖ / 2 < ‖dslope σ z0 z0‖ by
      rw [hS0]; have := norm_pos_iff.mpr hd; linarith))
    exact this
  obtain ⟨δ1, hδ1, hball1⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min (r / 2) (δ1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hcpt : IsCompact (closedBall z0 δ) := isCompact_closedBall _ _
  have hsub : closedBall z0 δ ⊆ ball z0 r := by
    intro s hs
    rw [mem_closedBall] at hs
    rw [mem_ball]
    have : δ ≤ r / 2 := min_le_left _ _
    linarith
  obtain ⟨M2, hM2⟩ := hcpt.exists_bound_of_continuousOn
    ((hD2.mono hsub).continuousOn)
  refine ⟨δ, hδpos, M2 / (‖d‖ / 2) ^ 2, fun s hs hne => ?_⟩
  have hsm : s ∈ closedBall z0 δ := by rw [mem_closedBall, dist_eq_norm]; exact hs.le
  have hsS : ‖d‖ / 2 < ‖dslope σ z0 s‖ := by
    refine hball1 ?_
    rw [dist_eq_norm]
    have : δ ≤ δ1 / 2 := min_le_right _ _
    linarith
  have h1 : R s = (s - z0) * ((s - z0) * dslope (dslope R z0) z0 s) := by
    have a1 := sub_smul_dslope R z0 s
    have a2 := sub_smul_dslope (dslope R z0) z0 s
    rw [hD10, sub_zero] at a2
    simp only [smul_eq_mul] at a1 a2
    rw [hR0, sub_zero] at a1
    rw [a2]; exact a1.symm
  have h2 : σ s = (s - z0) * dslope σ z0 s := by
    have a1 := sub_smul_dslope σ z0 s
    simp only [smul_eq_mul] at a1
    rw [hσ0, sub_zero] at a1
    exact a1.symm
  have hsz : s - z0 ≠ 0 := sub_ne_zero.mpr hne
  have hSne : dslope σ z0 s ≠ 0 := by
    intro h
    rw [h] at hsS; simp at hsS
    have := norm_pos_iff.mpr hd; linarith
  have key : R s / σ s ^ 2 = dslope (dslope R z0) z0 s / dslope σ z0 s ^ 2 := by
    rw [h1, h2]; field_simp
  rw [key, norm_div, norm_pow]
  have hpos : 0 < (‖d‖ / 2) ^ 2 := by have := norm_pos_iff.mpr hd; positivity
  have hM2s := hM2 s hsm
  have hden : (‖d‖ / 2) ^ 2 ≤ ‖dslope σ z0 s‖ ^ 2 := by
    gcongr
  have hM2nn : 0 ≤ M2 := (norm_nonneg _).trans hM2s
  calc ‖dslope (dslope R z0) z0 s‖ / ‖dslope σ z0 s‖ ^ 2 ≤ M2 / ‖dslope σ z0 s‖ ^ 2 := by
        gcongr
    _ ≤ M2 / (‖d‖ / 2) ^ 2 := by
        apply div_le_div_of_nonneg_left hM2nn hpos hden

/-- A function differentiable at `0` and even near `0` has derivative `0` there. -/
lemma hasDerivAt_zero_of_even {f : ℂ → ℂ} (hd : DifferentiableAt ℂ f 0)
    (he : ∀ᶠ s in 𝓝 (0 : ℂ), f (-s) = f s) : HasDerivAt f 0 0 := by
  have h1 : HasDerivAt f (deriv f 0) 0 := hd.hasDerivAt
  have h1' : HasDerivAt f (deriv f 0) (-(0 : ℂ)) := by simpa using h1
  have h2 : HasDerivAt (fun s => f (-s)) (-(deriv f 0)) 0 :=
    (h1'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))).congr_deriv (by ring)
  have h3 : HasDerivAt (fun s => f (-s)) (deriv f 0) 0 := h1.congr_of_eventuallyEq (he.mono fun s hs => hs)
  have h4 := h2.unique h3
  have h5 : deriv f 0 = 0 := by linear_combination -h4 / 2
  rw [h5] at h1
  exact h1

/-! ### The extension across `s = 0` -/

/-- The holomorphic extension of `Ψ̂` across `s = 0`: the same formula, valid on the disc `|s| < 1/4`. -/
noncomputable def psiE0 (s : ℂ) : ℂ := psiOne (gS s) (kC s) (cC s)

lemma re_cC_pos_ball {s : ℂ} (h : ‖s‖ < 1 / 4) : 0 < (cC s).re := by
  have hpi := Real.pi_pos
  have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  rw [re_cC]
  have : 0 < Real.cos (π * s.re) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [abs_le.mp h1, Real.pi_gt_three], by
      nlinarith [abs_le.mp h1, Real.pi_gt_three]⟩
  positivity

lemma re_kC_pos_ball {s : ℂ} (h : ‖s‖ < 1 / 4) : 0 < (kC s).re := by
  have hpi := Real.pi_pos
  have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  unfold kC
  rw [re_cos']
  rw [show ((π : ℂ) * s / 2).re = π * s.re / 2 by simp,
    show ((π : ℂ) * s / 2).im = π * s.im / 2 by simp]
  have : 0 < Real.cos (π * s.re / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [abs_le.mp h1, Real.pi_gt_three], by
      nlinarith [abs_le.mp h1, Real.pi_gt_three]⟩
  positivity

lemma cC_mem_sDom_ball {s : ℂ} (h : ‖s‖ < 1 / 4) : cC s ∈ sDom := by
  rintro ⟨-, hre⟩
  have := re_cC_pos_ball h
  linarith

lemma differentiableOn_psiE0 : DifferentiableOn ℂ psiE0 (ball (0 : ℂ) (1 / 4)) := by
  intro s hs
  have hs' : ‖s‖ < 1 / 4 := by simpa using hs
  have hk : kC s ≠ 0 := fun h => by have := re_kC_pos_ball hs'; rw [h] at this; simp at this
  have hc : cC s ≠ 0 := fun h => by have := re_cC_pos_ball hs'; rw [h] at this; simp at this
  have hg : gS s ≠ 0 := sInt_ne_zero (cC_mem_sDom_ball hs')
  have hDk : DifferentiableAt ℂ kC s := by unfold kC; fun_prop
  have hDc : DifferentiableAt ℂ cC s := by unfold cC; fun_prop
  have hDg : DifferentiableAt ℂ gS s := by
    unfold gS
    have h2 : DifferentiableAt ℂ sInt (Complex.cos ((π : ℂ) * s)) :=
      differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (cC_mem_sDom_ball hs'))
    exact DifferentiableAt.comp (g := sInt) (f := fun s : ℂ => Complex.cos ((π : ℂ) * s)) s h2 (by fun_prop)
  unfold psiE0 psiOne
  have hd : ((√2 : ℝ) : ℂ) * kC s * gS s ≠ 0 := mul_ne_zero (mul_ne_zero sqrt2_ne hk) hg
  have hN : DifferentiableAt ℂ (fun s => 1 / (((√2 : ℝ) : ℂ) * kC s * gS s) - 1) s :=
    ((differentiableAt_const _).div (((differentiableAt_const _).mul hDk).mul hDg) hd).sub
      (differentiableAt_const _)
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (((differentiableAt_const (-(π : ℂ))).mul hN).div hDc hc).sub
    ((differentiableAt_const _).div hDk hk)

lemma psiE0_even (s : ℂ) : psiE0 (-s) = psiE0 s := by
  have h1 : cC (-s) = cC s := by unfold cC; rw [mul_neg, Complex.cos_neg]
  have h2 : kC (-s) = kC s := by
    unfold kC
    rw [show (π : ℂ) * -s / 2 = -((π : ℂ) * s / 2) by ring, Complex.cos_neg]
  have h3 : gS (-s) = gS s := by unfold gS; rw [← cC, ← cC, h1]
  unfold psiE0; rw [h1, h2, h3]

lemma psiE0_eq {s : ℂ} (hs : s ∈ unitStrip) (h : ‖s‖ < 1 / 4) : psiHat s = psiE0 s := by
  have hne : s ≠ 1 / 2 := by
    intro e; rw [e] at h; norm_num at h
  exact psiHat_eq' hs hne

lemma psiE0_zero : psiE0 0 = ((-(π / (√2 * Real.arsinh 1)) + π - √2 : ℝ) : ℂ) := by
  have h1 : cC 0 = 1 := by unfold cC; simp
  have h2 : kC 0 = 1 := by unfold kC; simp
  have h3 : gS 0 = ((Real.arsinh 1 : ℝ) : ℂ) := by unfold gS; rw [← cC, h1]; exact sInt_one_eq
  unfold psiE0 psiOne
  rw [h1, h2, h3]
  have hA : (Real.arsinh 1 : ℝ) ≠ 0 := arsinh_one_pos.ne'
  have hA' : ((Real.arsinh 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
  have hs := sqrt2_ne
  have hs' : (0 : ℝ) < √2 := by positivity
  push_cast
  field_simp
  ring

/-! ### The comparison function `p` -/

/-- `p(s) = P₀ + P₁ cos πs + P₂ sin πs sin(πs/2)`. -/
noncomputable def pC (P0 P1 P2 : ℝ) (s : ℂ) : ℂ :=
  (P0 : ℂ) + (P1 : ℂ) * Complex.cos (π * s) + (P2 : ℂ) * (Complex.sin (π * s) * Complex.sin (π * s / 2))

lemma pC_even (P0 P1 P2 : ℝ) (s : ℂ) : pC P0 P1 P2 (-s) = pC P0 P1 P2 s := by
  unfold pC
  rw [mul_neg, Complex.cos_neg, Complex.sin_neg, show -((π : ℂ) * s) / 2 = -((π : ℂ) * s / 2) by ring,
    Complex.sin_neg]
  ring

lemma differentiable_pC (P0 P1 P2 : ℝ) : Differentiable ℂ (pC P0 P1 P2) := by
  unfold pC; fun_prop

lemma pC_zero (P0 P1 P2 : ℝ) : pC P0 P1 P2 0 = ((P0 + P1 : ℝ) : ℂ) := by
  unfold pC; simp

lemma pC_one (P0 P1 P2 : ℝ) : pC P0 P1 P2 1 = ((P0 - P1 : ℝ) : ℂ) := by
  unfold pC; simp; ring

lemma hasDerivAt_pC_one (P0 P1 P2 : ℝ) : HasDerivAt (pC P0 P1 P2) (-((π : ℂ) * P2)) 1 := by
  have hl : HasDerivAt (fun s : ℂ => (π : ℂ) * s) (π : ℂ) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_mul (π : ℂ)
  have hl2 : HasDerivAt (fun s : ℂ => (π : ℂ) * s / 2) ((π : ℂ) / 2) 1 := hl.div_const 2
  have hc := hl.ccos
  have hs1 := hl.csin
  have hs2 := hl2.csin
  have h := (((hasDerivAt_const (1 : ℂ) (P0 : ℂ)).add (hc.const_mul (P1 : ℂ))).add
    ((hs1.mul hs2).const_mul (P2 : ℂ)))
  unfold pC
  refine h.congr_deriv ?_
  simp only [mul_one, Complex.sin_pi, Complex.cos_pi, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
  ring

/-! ### The extension across `s = 1` -/

/-- `Mf₁(k) = -π/(√2 (2k²-1) E₁(√2 k)) - √2` (a holomorphic function vanishing at `0`). -/
noncomputable def Mf1 (k : ℂ) : ℂ :=
  -(π : ℂ) / (((√2 : ℝ) : ℂ) * (2 * k ^ 2 - 1) * tipE (((√2 : ℝ) : ℂ) * k)) - ((√2 : ℝ) : ℂ)

/-- `Φ₁(k) = Mf₁(k)/k + π/(2k²-1)`; `Ψ̂(s) = Φ₁(cos(πs/2))` near `s = 1`. -/
noncomputable def Phi1 (k : ℂ) : ℂ := dslope Mf1 0 k + (π : ℂ) / (2 * k ^ 2 - 1)

lemma Phi1_data : ∃ r₀ : ℝ, 0 < r₀ ∧ DifferentiableOn ℂ Phi1 (ball (0 : ℂ) r₀) ∧
    ∀ s ∈ unitStrip, ‖kC s‖ < min r₀ (1 / 4) → psiHat s = Phi1 (kC s) := by
  have hT0 : tipE 0 = (π : ℂ) / 2 := tipE_zero
  have hTc : ContinuousAt (fun k : ℂ => tipE (((√2 : ℝ) : ℂ) * k)) 0 := by
    have : ContinuousAt tipE (((√2 : ℝ) : ℂ) * 0) := by
      rw [mul_zero]
      exact differentiableOn_tipE.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
    exact this.comp (f := fun k : ℂ => ((√2 : ℝ) : ℂ) * k) (by fun_prop)
  have hev : ∀ᶠ k in 𝓝 (0 : ℂ), tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 ∧ 2 * k ^ 2 - 1 ≠ 0 ∧
      ‖((√2 : ℝ) : ℂ) * k‖ < 1 := by
    have h1 : ∀ᶠ k in 𝓝 (0 : ℂ), tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 := by
      have : tipE (((√2 : ℝ) : ℂ) * 0) ≠ 0 := by
        rw [mul_zero, hT0]; simp
      exact hTc.eventually_ne this
    have h2 : ∀ᶠ k in 𝓝 (0 : ℂ), 2 * k ^ 2 - 1 ≠ 0 := by
      have hc : ContinuousAt (fun k : ℂ => 2 * k ^ 2 - 1) 0 := by fun_prop
      exact hc.eventually_ne (by norm_num)
    have h3 : ∀ᶠ k in 𝓝 (0 : ℂ), ‖((√2 : ℝ) : ℂ) * k‖ < 1 := by
      have hc : ContinuousAt (fun k : ℂ => ‖((√2 : ℝ) : ℂ) * k‖) 0 := by fun_prop
      exact hc.eventually (gt_mem_nhds (by simp))
    exact h1.and (h2.and h3)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hMfd : DifferentiableOn ℂ Mf1 (Metric.ball (0 : ℂ) r₀) := by
    intro k hk
    have hk' := hball (by simpa using hk)
    have hd : DifferentiableAt ℂ tipE (((√2 : ℝ) : ℂ) * k) :=
      differentiableOn_tipE.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hk'.2.2))
    have hd2 : DifferentiableAt ℂ (fun k : ℂ => tipE (((√2 : ℝ) : ℂ) * k)) k :=
      DifferentiableAt.comp (g := tipE) (f := fun k : ℂ => ((√2 : ℝ) : ℂ) * k) k hd (by fun_prop)
    have hden : ((√2 : ℝ) : ℂ) * (2 * k ^ 2 - 1) * tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 :=
      mul_ne_zero (mul_ne_zero sqrt2_ne hk'.2.1) hk'.1
    have : DifferentiableAt ℂ Mf1 k := by
      unfold Mf1
      refine DifferentiableAt.sub (DifferentiableAt.div (differentiableAt_const _) ?_ hden)
        (differentiableAt_const _)
      exact ((differentiableAt_const _).mul (by fun_prop)).mul hd2
    exact this.differentiableWithinAt
  have hMf0 : Mf1 0 = 0 := by
    unfold Mf1
    rw [mul_zero, hT0]
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 := sqrt2_ne
    have h3 : (((√2 : ℝ)) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    field_simp
    simp
    linear_combination h3
  refine ⟨r₀, hr₀, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (dslope Mf1 0) (Metric.ball (0 : ℂ) r₀) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))).mpr hMfd
    intro k hk
    have hk' := hball (by simpa using hk)
    unfold Phi1
    exact (h1 k hk).add (DifferentiableWithinAt.div (differentiableWithinAt_const _) (by fun_prop) hk'.2.1)
  · intro s hs hks
    have hkne := kC_ne_zero hs
    have hkr : ‖kC s‖ < r₀ := lt_of_lt_of_le hks (min_le_left _ _)
    have hk4 : ‖kC s‖ < 1 / 4 := lt_of_lt_of_le hks (min_le_right _ _)
    have hne : s ≠ 1 / 2 := by
      intro h; rw [h, kC_half] at hk4
      have : (0 : ℝ) < √2 := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hk4
      have h2 : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hb := hball (by simpa using hkr : dist (kC s) 0 < r₀)
    have hg := gS_eq_tipE hs hb.2.2
    have hcc : cC s = 2 * kC s ^ 2 - 1 := by linear_combination one_add_cC s
    rw [psiHat_eq hs hne]
    unfold Nf Phi1
    rw [hg, hcc]
    have h0 : dslope Mf1 0 (kC s) = Mf1 (kC s) / kC s := by
      rw [dslope_of_ne _ hkne, slope_def_field, hMf0]; simp
    rw [h0]
    unfold Mf1
    have h2 := sqrt2_ne
    have h3 := hb.1
    have h4 := hb.2.1
    field_simp
    ring_nf

/-! ### The imaginary part of `Ψ̃` on the right edge, near `τ = 0` -/

/-- The imaginary part of `Ψ̃(1 + iτ)`. -/
noncomputable def imR (τ : ℝ) : ℝ :=
  √(Real.cosh (π * τ)) / (2 * √2 * (√(Real.cosh (π * τ)) * √(Real.cosh (π * τ))) *
    Real.sinh (π * τ / 2) * (vT τ ^ 2 + 1 / 4)) - √2 / Real.sinh (π * τ / 2)

lemma psiTil_right_im {τ : ℝ} (hτ : τ ≠ 0) : (psiTil (1 + (τ : ℂ) * Complex.I)).im = imR τ := by
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hr : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hc
  have hqq : √(Real.cosh (π * τ)) * √(Real.cosh (π * τ)) = Real.cosh (π * τ) :=
    Real.mul_self_sqrt hc.le
  have hσ : Real.sinh (π * τ / 2) ≠ 0 := by
    intro h
    have := Real.sinh_eq_zero.mp h
    have hpi := Real.pi_pos
    apply hτ
    nlinarith
  rw [psiTil_right hτ, kC_right, cC_right]
  have hcast : ((Real.cosh (π * τ) : ℝ) : ℂ) = ((√(Real.cosh (π * τ)) * √(Real.cosh (π * τ)) : ℝ) : ℂ) := by
    rw [hqq]
  rw [hcast]
  unfold Lg
  rw [right_aux _ _ _ hr hσ]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  unfold imR
  rfl

lemma tendsto_sinh_half_div : Tendsto (fun τ : ℝ => Real.sinh (π * τ / 2) / τ) (𝓝[≠] 0) (𝓝 (π / 2)) := by
  have h : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ / 2)) (π / 2) 0 := by
    have := (hasDerivAt_sinh_arg 2 0)
    simpa using this
  have := hasDerivAt_iff_tendsto_slope.mp h
  refine this.congr (fun τ => ?_)
  simp [slope_def_field, div_eq_inv_mul]

lemma tendsto_vT_div : Tendsto (fun τ : ℝ => vT τ / τ) (𝓝[≠] 0) (𝓝 (√2 / 2)) := by
  have h := hasDerivAt_vT 0
  have hv : vD 0 = √2 / 2 := by unfold vD; simp
  rw [hv] at h
  have := hasDerivAt_iff_tendsto_slope.mp h
  refine this.congr (fun τ => ?_)
  have : vT 0 = 0 := by unfold vT; simp
  simp [slope_def_field, div_eq_inv_mul, this]

lemma continuousAt_vT_zero : ContinuousAt vT 0 := (hasDerivAt_vT 0).continuousAt

lemma tendsto_imR_div : Tendsto (fun τ : ℝ => imR τ / τ) (𝓝[≠] 0)
    (𝓝 (-(√2 * (π ^ 2 / 2 + 4)) / π)) := by
  have hpi := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσt := tendsto_sinh_half_div
  have hvt := tendsto_vT_div
  have hv0 : Tendsto vT (𝓝[≠] 0) (𝓝 0) := by
    have := continuousAt_vT_zero.tendsto
    have h0 : vT 0 = 0 := by unfold vT; simp
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hch : Tendsto (fun τ : ℝ => Real.cosh (π * τ)) (𝓝[≠] 0) (𝓝 1) := by
    have : Tendsto (fun τ : ℝ => Real.cosh (π * τ)) (𝓝 0) (𝓝 (Real.cosh (π * 0))) :=
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun τ : ℝ => √(Real.cosh (π * τ))) (𝓝[≠] 0) (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hch
    simpa [Function.comp_def] using this
  -- ν = r (1 + 4 v²)
  set ν : ℝ → ℝ := fun τ => √(Real.cosh (π * τ)) * (1 + 4 * vT τ ^ 2) with hν
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    have : Tendsto (fun τ : ℝ => 1 + 4 * vT τ ^ 2) (𝓝[≠] 0) (𝓝 (1 + 4 * 0 ^ 2)) :=
      tendsto_const_nhds.add ((hv0.pow 2).const_mul 4)
    simpa using hr.mul this
  -- (c - 1)/τ² → π²/2
  have hc2 : Tendsto (fun τ : ℝ => (Real.cosh (π * τ) - 1) / τ ^ 2) (𝓝[≠] 0) (𝓝 (π ^ 2 / 2)) := by
    have : Tendsto (fun τ : ℝ => 2 * (Real.sinh (π * τ / 2) / τ) ^ 2) (𝓝[≠] 0)
        (𝓝 (2 * (π / 2) ^ 2)) := (hσt.pow 2).const_mul 2
    have e : 2 * (π / 2) ^ 2 = π ^ 2 / 2 := by ring
    rw [e] at this
    refine this.congr (fun τ => ?_)
    rw [cosh_sub_one_eq]; ring
  have hv2 : Tendsto (fun τ : ℝ => (vT τ / τ) ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have := hvt.pow 2
    have e : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, hs2]; norm_num
    rwa [e] at this
  -- (ν² - 1)/τ² → π²/2 + 4
  have hnu2 : Tendsto (fun τ : ℝ => (ν τ ^ 2 - 1) / τ ^ 2) (𝓝[≠] 0) (𝓝 (π ^ 2 / 2 + 4)) := by
    have hA : Tendsto (fun τ : ℝ => (1 + 4 * vT τ ^ 2) ^ 2) (𝓝[≠] 0) (𝓝 ((1 + 4 * 0 ^ 2) ^ 2)) :=
      (tendsto_const_nhds.add ((hv0.pow 2).const_mul 4)).pow 2
    have hB : Tendsto (fun τ : ℝ => 4 * (vT τ / τ) ^ 2 * (2 + 4 * vT τ ^ 2)) (𝓝[≠] 0)
        (𝓝 (4 * (1 / 2) * (2 + 4 * 0 ^ 2))) :=
      (hv2.const_mul 4).mul (tendsto_const_nhds.add ((hv0.pow 2).const_mul 4))
    have := (hc2.mul hA).add hB
    have e : π ^ 2 / 2 * (1 + 4 * 0 ^ 2) ^ 2 + 4 * (1 / 2) * (2 + 4 * 0 ^ 2) = π ^ 2 / 2 + 4 := by ring
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : τ ≠ 0 := hτ
    have hc : 0 ≤ Real.cosh (π * τ) := (Real.cosh_pos _).le
    simp only [hν, mul_pow, Real.sq_sqrt hc]
    field_simp
    ring
  -- (ν - 1)/τ² → π²/4 + 2
  have hnu : Tendsto (fun τ : ℝ => (ν τ - 1) / τ ^ 2) (𝓝[≠] 0) (𝓝 (π ^ 2 / 4 + 2)) := by
    have hden : Tendsto (fun τ : ℝ => ν τ + 1) (𝓝[≠] 0) (𝓝 (1 + 1)) := hν1.add tendsto_const_nhds
    have := hnu2.div hden (by norm_num)
    have e : (π ^ 2 / 2 + 4) / (1 + 1) = π ^ 2 / 4 + 2 := by ring
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, (hν1.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
      with τ hτ hν0
    have hτ0 : τ ≠ 0 := hτ
    have : ν τ + 1 ≠ 0 := by linarith
    simp only [Pi.div_apply]
    field_simp
    ring
  -- assemble
  have hτσ : Tendsto (fun τ : ℝ => τ / Real.sinh (π * τ / 2)) (𝓝[≠] 0) (𝓝 (2 / π)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div hσt (by positivity)
    have e : 1 / (π / 2) = 2 / π := by field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ0 : τ ≠ 0 := hτ
    have hσ : Real.sinh (π * τ / 2) ≠ 0 := by
      intro h
      have := Real.sinh_eq_zero.mp h
      apply hτ0; nlinarith
    simp only [Pi.div_apply]
    field_simp
  have hfin : Tendsto (fun τ : ℝ => √2 * (τ / Real.sinh (π * τ / 2)) * (-((ν τ - 1) / τ ^ 2) / ν τ))
      (𝓝[≠] 0) (𝓝 (√2 * (2 / π) * (-(π ^ 2 / 4 + 2) / 1))) :=
    (hτσ.const_mul √2).mul (hnu.neg.div hν1 one_ne_zero)
  have e : √2 * (2 / π) * (-(π ^ 2 / 4 + 2) / 1) = -(√2 * (π ^ 2 / 2 + 4)) / π := by
    field_simp; ring
  rw [e] at hfin
  refine hfin.congr' ?_
  have hν0 : ∀ᶠ τ : ℝ in 𝓝[≠] 0, 0 < ν τ := hν1.eventually (lt_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hν0] with τ hτ hν0
  have hτ0 : τ ≠ 0 := hτ
  have hσ : Real.sinh (π * τ / 2) ≠ 0 := by
    intro h
    have := Real.sinh_eq_zero.mp h
    apply hτ0; nlinarith
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hr : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hc
  have hw : 0 < vT τ ^ 2 + 1 / 4 := by positivity
  unfold imR
  simp only [hν] at hν0 ⊢
  field_simp
  ring_nf
  simp only [hs2]
  ring

/-- The holomorphic extension of `Ψ̂` across `s = 1`. -/
noncomputable def psiE1 (s : ℂ) : ℂ := Phi1 (kC s)

lemma kC_one : kC 1 = 0 := by
  unfold kC
  have : (π : ℂ) * 1 / 2 = (π : ℂ) / 2 := by ring
  rw [this]; exact Complex.cos_pi_div_two

lemma psiE1_data : ∃ r1 : ℝ, 0 < r1 ∧ DifferentiableOn ℂ psiE1 (ball (1 : ℂ) r1) ∧
    ∀ s ∈ unitStrip, ‖s - 1‖ < r1 → psiHat s = psiE1 s := by
  obtain ⟨r₀, hr₀, hΦ, heq⟩ := Phi1_data
  have hρ : 0 < min r₀ (1 / 4) := lt_min hr₀ (by norm_num)
  have hkc : ContinuousAt kC 1 := continuousAt_kC 1
  obtain ⟨r1, hr1, hk⟩ := Metric.continuousAt_iff.mp hkc (min r₀ (1 / 4)) hρ
  have hk' : ∀ s : ℂ, ‖s - 1‖ < r1 → ‖kC s‖ < min r₀ (1 / 4) := by
    intro s hs
    have := hk (x := s) (by rw [dist_eq_norm]; exact hs)
    rwa [kC_one, dist_zero_right] at this
  refine ⟨r1, hr1, ?_, ?_⟩
  · intro s hs
    have hs' : ‖s - 1‖ < r1 := by simpa [dist_eq_norm] using hs
    have h1 : kC s ∈ ball (0 : ℂ) r₀ := by
      rw [mem_ball_zero_iff]; exact lt_of_lt_of_le (hk' s hs') (min_le_left _ _)
    have h2 : DifferentiableAt ℂ Phi1 (kC s) := hΦ.differentiableAt (isOpen_ball.mem_nhds h1)
    have h3 : DifferentiableAt ℂ kC s := by unfold kC; fun_prop
    exact (DifferentiableAt.comp (g := Phi1) (f := kC) s h2 h3).differentiableWithinAt
  · intro s hs hs1
    unfold psiE1
    exact heq s hs (hk' s hs1)

lemma psiTil_eq_of_ext {g : ℂ → ℂ} {z : ℂ} (hz : z ∈ closure unitStrip) (hg : ContinuousAt g z)
    (heq : ∀ᶠ s in 𝓝 z, s ∈ unitStrip → psiHat s = g s) : psiTil z = g z := by
  refine extLim_eq_of_tendsto hz ?_
  refine (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  exact eventually_nhdsWithin_iff.mpr (heq.mono fun s h hs => (h hs).symm)

lemma fR_even (τ : ℝ) : fR (-τ) = fR τ := by
  unfold fR
  rw [vA_even, mul_neg, Real.cosh_neg]

/-- **The derivative of `Ψ̂` at the corner `s = 1`** (computed from the right-edge formula). -/
lemma hasDerivAt_psiE1_one :
    HasDerivAt psiE1 (((-(√2 * (π ^ 2 / 2 + 4)) / π : ℝ)) : ℂ) 1 ∧ (psiE1 1).im = 0 := by
  obtain ⟨r1, hr1, hdiff, heq1⟩ := psiE1_data
  have hnh : ball (1 : ℂ) r1 ∈ 𝓝 (1 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self hr1)
  have hd1 : HasDerivAt psiE1 (deriv psiE1 1) 1 := (hdiff.differentiableAt hnh).hasDerivAt
  set d : ℂ := deriv psiE1 1 with hd
  have hline : HasDerivAt (fun τ : ℝ => (1 : ℂ) + (τ : ℂ) * Complex.I) Complex.I 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add (1 : ℂ)
    simpa using this
  have hg : HasDerivAt (fun τ : ℝ => psiE1 (1 + (τ : ℂ) * Complex.I)) (Complex.I * d) 0 := by
    have h1 : HasDerivAt psiE1 d ((1 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by simpa using hd1
    exact (h1.scomp (0 : ℝ) hline).congr_deriv (smul_eq_mul _ _)
  -- edge identification
  have hedge : ∀ τ : ℝ, τ ≠ 0 → |τ| < r1 →
      psiTil (1 + (τ : ℂ) * Complex.I) = psiE1 (1 + (τ : ℂ) * Complex.I) := by
    intro τ hτ hτr
    have hz : (1 + (τ : ℂ) * Complex.I) ∈ ball (1 : ℂ) r1 := by
      rw [mem_ball, dist_eq_norm]; simpa using hτr
    refine psiTil_eq_of_ext (unitStripCl_subset_closure ⟨by simp, by simp⟩) ?_ ?_
    · exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
    · filter_upwards [isOpen_ball.mem_nhds hz] with s hs hsu
      exact heq1 s hsu (by simpa [dist_eq_norm] using hs)
  have hnear : ∀ᶠ τ : ℝ in 𝓝[≠] (0 : ℝ), τ ≠ 0 ∧ |τ| < r1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hr1)] with τ hτ hτr
    exact ⟨hτ, by simpa using hτr⟩
  have him : ∀ᶠ τ : ℝ in 𝓝[≠] (0 : ℝ), (psiE1 (1 + (τ : ℂ) * Complex.I)).im = imR τ := by
    filter_upwards [hnear] with τ ⟨hτ, hτr⟩
    rw [← hedge τ hτ hτr]; exact psiTil_right_im hτ
  have hκ := tendsto_imR_div
  have himR0 : Tendsto imR (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun τ : ℝ => τ) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have := hκ.mul h0
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have : τ ≠ 0 := hτ
    field_simp
  -- continuity of g at 0 and the value of the imaginary part
  have hgc : Tendsto (fun τ : ℝ => psiE1 (1 + (τ : ℂ) * Complex.I)) (𝓝[≠] (0 : ℝ))
      (𝓝 (psiE1 1)) := by
    have := hg.continuousAt.tendsto
    simpa using this.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have himg : (psiE1 1).im = 0 := by
    have h1 : Tendsto (fun τ : ℝ => (psiE1 (1 + (τ : ℂ) * Complex.I)).im) (𝓝[≠] (0 : ℝ))
        (𝓝 (psiE1 1).im) := (Complex.continuous_im.tendsto _).comp hgc
    have h2 : Tendsto (fun τ : ℝ => (psiE1 (1 + (τ : ℂ) * Complex.I)).im) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      himR0.congr' (him.mono fun τ h => h.symm)
    exact tendsto_nhds_unique h1 h2
  refine ⟨?_, himg⟩
  -- the slope along the vertical direction
  have hslope := hasDerivAt_iff_tendsto_slope.mp hg
  have hre_d : d.re = -(√2 * (π ^ 2 / 2 + 4)) / π := by
    have h1 : Tendsto (fun τ : ℝ => (slope (fun τ : ℝ => psiE1 (1 + (τ : ℂ) * Complex.I)) 0 τ).im)
        (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.I * d).im) := (Complex.continuous_im.tendsto _).comp hslope
    have h2 : Tendsto (fun τ : ℝ => (slope (fun τ : ℝ => psiE1 (1 + (τ : ℂ) * Complex.I)) 0 τ).im)
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(√2 * (π ^ 2 / 2 + 4)) / π)) := by
      refine hκ.congr' ?_
      filter_upwards [him] with τ h
      rw [slope_def_module]
      simp only [Complex.smul_im, smul_eq_mul, Complex.sub_im, Complex.ofReal_zero, zero_mul, add_zero, sub_zero]
      rw [h, himg]
      simp [div_eq_inv_mul]
    have := tendsto_nhds_unique h1 h2
    simpa using this
  have him_d : d.im = 0 := by
    -- the real part of `g` is even
    set hf : ℝ → ℝ := fun τ => (psiE1 (1 + (τ : ℂ) * Complex.I)).re with hhf
    have hhd : HasDerivAt hf (Complex.I * d).re 0 := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
      simpa [hhf, Function.comp_def] using this
    have hevn : ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ), hf (-τ) = hf τ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr1] with τ hτr
      by_cases hτ : τ = 0
      · rw [hτ]; simp
      · have hτr' : |τ| < r1 := by simpa using hτr
        have h1 := hedge τ hτ hτr'
        have h2 := hedge (-τ) (neg_ne_zero.mpr hτ) (by rwa [abs_neg])
        have h3 := psiTil_right_re hτ
        have h4 := psiTil_right_re (neg_ne_zero.mpr hτ)
        have e1 : hf τ = fR τ := by simp only [hhf]; rw [← h1]; exact h3
        have e2 : hf (-τ) = fR (-τ) := by simp only [hhf]; rw [← h2]; exact h4
        rw [e1, e2, fR_even]
    have hneg : HasDerivAt (fun τ : ℝ => hf (-τ)) (-(Complex.I * d).re) 0 := by
      have h0 : HasDerivAt hf (Complex.I * d).re (-(0 : ℝ)) := by simpa using hhd
      exact (h0.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).congr_deriv (by ring)
    have hneg' : HasDerivAt (fun τ : ℝ => hf (-τ)) (Complex.I * d).re 0 :=
      hhd.congr_of_eventuallyEq (hevn.mono fun τ h => h)
    have := hneg.unique hneg'
    have hz : (Complex.I * d).re = 0 := by linarith
    simpa using hz
  have hdeq : d = ((-(√2 * (π ^ 2 / 2 + 4)) / π : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hre_d
    · rw [Complex.ofReal_im]; exact him_d
  rw [← hdeq]; exact hd1

/-! ### The constants of `p` and the local bounds -/

/-- The value of `Ψ` at `s = 0`. -/
noncomputable def Psi0v : ℝ := -(π / (√2 * Real.arsinh 1)) + π - √2

/-- The value of `Ψ` at `s = 1` (real). -/
noncomputable def Psi1v : ℝ := (psiE1 1).re

/-- The coefficient `P₂` of `sin πs sin(πs/2)`: `-Ψ'(1)/π`. -/
noncomputable def cP2 : ℝ := √2 * (π ^ 2 / 2 + 4) / π ^ 2

/-- The even-in-`s` comparison function with `p(0) = Ψ(0)`, `p(1) = Ψ(1)`, `p'(1) = Ψ'(1)`. -/
noncomputable def pG : ℂ → ℂ := pC ((Psi0v + Psi1v) / 2) ((Psi0v - Psi1v) / 2) cP2

lemma psiE1_one : psiE1 1 = ((Psi1v : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Psi1v]
  · simpa using hasDerivAt_psiE1_one.2

lemma pG_zero : pG 0 = psiE0 0 := by
  unfold pG; rw [pC_zero, psiE0_zero]
  congr 1; unfold Psi0v; ring

lemma pG_one : pG 1 = psiE1 1 := by
  unfold pG; rw [pC_one, psiE1_one]
  congr 1; ring

lemma hasDerivAt_pG_one : HasDerivAt pG (((-(√2 * (π ^ 2 / 2 + 4)) / π : ℝ)) : ℂ) 1 := by
  have h := hasDerivAt_pC_one ((Psi0v + Psi1v) / 2) ((Psi0v - Psi1v) / 2) cP2
  unfold pG
  refine h.congr_deriv ?_
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold cP2
  push_cast
  field_simp

lemma sin_pi_mul_hasDerivAt (z : ℂ) : HasDerivAt (fun s : ℂ => Complex.sin ((π : ℂ) * s))
    (Complex.cos ((π : ℂ) * z) * (π : ℂ)) z := by
  have := ((hasDerivAt_id z).const_mul (π : ℂ)).csin
  simpa using this

/-- The quotient `(Ψ̂ - p)/sin²(πs)` is bounded near the corner `s = 0` (inside the strip). -/
lemma bound_zero : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ s ∈ unitStrip, ‖s‖ < δ →
    ‖(psiHat s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2‖ ≤ M := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdR : DifferentiableOn ℂ (fun s => psiE0 s - pG s) (ball (0 : ℂ) (1 / 4)) :=
    differentiableOn_psiE0.sub (differentiable_pC _ _ _).differentiableOn
  have hR1 : HasDerivAt (fun s => psiE0 s - pG s) 0 0 := by
    refine hasDerivAt_zero_of_even
      ((hdR.differentiableAt (isOpen_ball.mem_nhds (by simp))))
      (Eventually.of_forall fun s => ?_)
    simp only [psiE0_even]
    unfold pG; rw [pC_even]
  have hσd : DifferentiableOn ℂ (fun s : ℂ => Complex.sin ((π : ℂ) * s)) (ball (0 : ℂ) (1 / 4)) := by
    intro s _; exact (sin_pi_mul_hasDerivAt s).differentiableAt.differentiableWithinAt
  have hσ1 : HasDerivAt (fun s : ℂ => Complex.sin ((π : ℂ) * s)) (π : ℂ) 0 := by
    have := sin_pi_mul_hasDerivAt 0; simpa using this
  obtain ⟨δ, hδ, M, hM⟩ := quad_div_bdd (z0 := 0) (r := 1 / 4) (by norm_num) hdR
    (by simp only [pG_zero, sub_self]) hR1 hσd (by simp) hσ1 hpi
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), M, fun s hs hsn => ?_⟩
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp [unitStrip] at hs
  have h1 : ‖s‖ < 1 / 4 := lt_of_lt_of_le hsn (min_le_right _ _)
  have h2 : ‖s - 0‖ < δ := by rw [sub_zero]; exact lt_of_lt_of_le hsn (min_le_left _ _)
  have := hM s h2 hs0
  rw [psiE0_eq hs h1]
  exact this

/-- The quotient `(Ψ̂ - p)/sin²(πs)` is bounded near the corner `s = 1` (inside the strip). -/
lemma bound_one : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ s ∈ unitStrip, ‖s - 1‖ < δ →
    ‖(psiHat s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2‖ ≤ M := by
  obtain ⟨r1, hr1, hdiff, heq1⟩ := psiE1_data
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdR : DifferentiableOn ℂ (fun s => psiE1 s - pG s) (ball (1 : ℂ) r1) := by
    refine hdiff.sub ?_
    exact (differentiable_pC _ _ _).differentiableOn
  have hR1 : HasDerivAt (fun s => psiE1 s - pG s) 0 1 := by
    exact (hasDerivAt_psiE1_one.1.fun_sub hasDerivAt_pG_one).congr_deriv (by simp)
  have hσd : DifferentiableOn ℂ (fun s : ℂ => Complex.sin ((π : ℂ) * s)) (ball (1 : ℂ) r1) := by
    intro s _; exact (sin_pi_mul_hasDerivAt s).differentiableAt.differentiableWithinAt
  have hσ1 : HasDerivAt (fun s : ℂ => Complex.sin ((π : ℂ) * s)) (-(π : ℂ)) 1 := by
    have := sin_pi_mul_hasDerivAt 1
    simpa using this
  obtain ⟨δ, hδ, M, hM⟩ := quad_div_bdd (z0 := 1) (r := r1) hr1 hdR
    (by simp only [pG_one, sub_self]) hR1 hσd (by simp) hσ1 (neg_ne_zero.mpr hpi)
  refine ⟨min δ r1, lt_min hδ hr1, M, fun s hs hsn => ?_⟩
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp [unitStrip] at hs
  have h2 : ‖s - 1‖ < δ := lt_of_lt_of_le hsn (min_le_left _ _)
  have h3 : ‖s - 1‖ < r1 := lt_of_lt_of_le hsn (min_le_right _ _)
  have := hM s h2 hs1
  rw [heq1 s hs h3]
  exact this

end FormalResearch.ModularBootstrap.FiveTerm

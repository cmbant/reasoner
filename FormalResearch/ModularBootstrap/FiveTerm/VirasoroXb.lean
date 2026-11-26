module

public import FormalResearch.ModularBootstrap.FiveTerm.StripCauchy
public import FormalResearch.ModularBootstrap.FiveTerm.StripCoord
public import FormalResearch.ModularBootstrap.FiveTerm.QFactor
public import FormalResearch.ModularBootstrap.FiveTerm.QBounds
public import FormalResearch.ModularBootstrap.FiveTerm.SchwarzSBoundary
public import FormalResearch.ModularBootstrap.FiveTerm.BoundaryExt
public import FormalResearch.ModularBootstrap.FiveTerm.CombData

/-!
# The strip function behind the `x`/`b` part of `g₁` (FIVE-0; paper Piece 3)

With `S = sInt`, `c = cos(πs)`, `g(s) = S(c)` and `k(s) = cos(πs/2)` (so `1 + c = 2k²`), the function
`Ψ(s) = -π (1/(√2 k g) - 1)/c - √2/k` is holomorphic on `0 < Re s < 1` (the singularity at `s = 1/2` is
removable), and the pole of `Ψ` at `s = 1` is subtracted.  Its edge values are explicit in `x_T`, `v_T`.
Cauchy on the strip (`strip_edge_integral_eq`) then gives the integral identity of `VirasoroXbMain`.
-/

@[expose] public section

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `g(s) = S(cos πs)`. -/
noncomputable def gS (s : ℂ) : ℂ := sInt (Complex.cos ((π : ℂ) * s))

/-- `k(s) = cos(πs/2)`. -/
noncomputable def kC (s : ℂ) : ℂ := Complex.cos ((π : ℂ) * s / 2)

/-- `c(s) = cos πs`. -/
noncomputable def cC (s : ℂ) : ℂ := Complex.cos ((π : ℂ) * s)

lemma cos_eq_re_im (w : ℂ) : Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ) +
    ((-(Real.sin w.re * Real.sinh w.im) : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  push_cast; ring

lemma re_cos' (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  rw [cos_eq_re_im]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]

lemma im_cos' (w : ℂ) : (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
  rw [cos_eq_re_im]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, zero_add, mul_one, add_zero]

lemma re_pi_mul (s : ℂ) : ((π : ℂ) * s).re = π * s.re := by simp
lemma im_pi_mul (s : ℂ) : ((π : ℂ) * s).im = π * s.im := by simp

lemma re_cC (s : ℂ) : (cC s).re = Real.cos (π * s.re) * Real.cosh (π * s.im) := by
  unfold cC; rw [re_cos', re_pi_mul, im_pi_mul]

lemma im_cC (s : ℂ) : (cC s).im = -(Real.sin (π * s.re) * Real.sinh (π * s.im)) := by
  unfold cC; rw [im_cos', re_pi_mul, im_pi_mul]

lemma cC_mem_sDom {s : ℂ} (hs : s ∈ unitStrip) : cC s ∈ sDom := by
  rintro ⟨him, hre⟩
  rw [im_cC] at him
  rw [re_cC] at hre
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin (π * s.re) := Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])
  have hsinh : Real.sinh (π * s.im) = 0 := by
    have : Real.sin (π * s.re) * Real.sinh (π * s.im) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hsin.ne'
    · exact h
  have him0 : s.im = 0 := by
    have := Real.sinh_eq_zero.mp hsinh
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hpi.ne'
    · exact h
  rw [him0] at hre
  simp at hre
  have : -1 < Real.cos (π * s.re) := by
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := π * s.re) (y := π) (by nlinarith [hs.1]) le_rfl
      (by nlinarith [hs.2])
    rw [Real.cos_pi] at h1; exact h1
  linarith

lemma differentiableOn_cC : DifferentiableOn ℂ cC unitStrip := by
  unfold cC; fun_prop

lemma differentiableOn_kC : DifferentiableOn ℂ kC unitStrip := by
  unfold kC; fun_prop

lemma differentiableOn_gS : DifferentiableOn ℂ gS unitStrip := by
  unfold gS
  exact differentiableOn_sInt.comp (by fun_prop) (fun s hs => cC_mem_sDom hs)

lemma gS_ne_zero {s : ℂ} (hs : s ∈ unitStrip) : gS s ≠ 0 := sInt_ne_zero (cC_mem_sDom hs)

lemma re_kC_pos {s : ℂ} (hs : s ∈ unitStrip) : 0 < (kC s).re := by
  unfold kC
  rw [re_cos']
  have hpi := Real.pi_pos
  have : (π * s / 2 : ℂ).re = π * s.re / 2 := by simp
  have h2 : ((π : ℂ) * s / 2).im = π * s.im / 2 := by simp
  rw [show ((π : ℂ) * s / 2).re = π * s.re / 2 by simp, h2]
  have : 0 < Real.cos (π * s.re / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  positivity

lemma kC_ne_zero {s : ℂ} (hs : s ∈ unitStrip) : kC s ≠ 0 := by
  intro h; have := re_kC_pos hs; rw [h] at this; simp at this

lemma one_add_cC (s : ℂ) : 1 + cC s = 2 * kC s ^ 2 := by
  unfold cC kC
  have := Complex.cos_two_mul ((π : ℂ) * s / 2)
  rw [show 2 * ((π : ℂ) * s / 2) = (π : ℂ) * s by ring] at this
  rw [this]; ring

lemma cC_eq_zero_iff {s : ℂ} (hs : s ∈ unitStrip) : cC s = 0 ↔ s = 1 / 2 := by
  constructor
  · intro h
    unfold cC at h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs' : s = (2 * k + 1) / 2 := by
      have : (π : ℂ) * s = (π : ℂ) * ((2 * k + 1) / 2) := by rw [hk]; ring
      exact mul_left_cancel₀ hpi this
    have hre : s.re = (2 * k + 1) / 2 := by rw [hs']; simp
    have h0 := hs.1; have h1 := hs.2
    rw [hre] at h0 h1
    have hk0 : (-1 : ℝ) < k := by linarith
    have hk1 : (k : ℝ) < 1 := by linarith
    have : k = 0 := by
      have a : -1 < k := by exact_mod_cast hk0
      have b : k < 1 := by exact_mod_cast hk1
      omega
    rw [hs', this]; norm_num
  · intro h
    rw [h]; unfold cC
    have : (π : ℂ) * (1 / 2) = π / 2 := by ring
    rw [this]
    exact Complex.cos_pi_div_two

lemma sInt_zero' : sInt 0 = 1 := by unfold sInt; simp

lemma half_mem : (1 / 2 : ℂ) ∈ unitStrip := by
  constructor <;> simp; norm_num

lemma kC_half : kC (1 / 2) = (((√2 / 2 : ℝ)) : ℂ) := by
  unfold kC
  have : (π : ℂ) * (1 / 2) / 2 = ((π / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_cos, Real.cos_pi_div_four]

lemma cC_half : cC (1 / 2) = 0 := (cC_eq_zero_iff half_mem).mpr rfl

lemma gS_half : gS (1 / 2) = 1 := by
  unfold gS
  have : Complex.cos ((π : ℂ) * (1 / 2)) = 0 := cC_half
  rw [this, sInt_zero']

/-- `N = 1/(√2 k g) - 1`, vanishing at `s = 1/2`. -/
noncomputable def Nf (s : ℂ) : ℂ := 1 / (((√2 : ℝ) : ℂ) * kC s * gS s) - 1

lemma Nf_half : Nf (1 / 2) = 0 := by
  unfold Nf
  rw [kC_half, gS_half]
  have h2 : (0 : ℝ) < √2 := by positivity
  have : (((√2 : ℝ)) : ℂ) * (((√2 / 2 : ℝ)) : ℂ) * 1 = 1 := by
    have : √2 * (√2 / 2) = 1 := by
      have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    exact_mod_cast (by rw [mul_one]; exact this : √2 * (√2 / 2) * 1 = 1)
  rw [this]; simp

lemma sqrt2_ne : (((√2 : ℝ)) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < √2 := by positivity
  exact_mod_cast this.ne'

lemma differentiableOn_Nf : DifferentiableOn ℂ Nf unitStrip := by
  intro s hs
  have h1 : DifferentiableAt ℂ kC s := differentiableOn_kC.differentiableAt (isOpen_unitStrip.mem_nhds hs)
  have h2 : DifferentiableAt ℂ gS s := differentiableOn_gS.differentiableAt (isOpen_unitStrip.mem_nhds hs)
  have hd : ((√2 : ℝ) : ℂ) * kC s * gS s ≠ 0 :=
    mul_ne_zero (mul_ne_zero sqrt2_ne (kC_ne_zero hs)) (gS_ne_zero hs)
  unfold Nf
  exact ((differentiableAt_const _).div ((differentiableAt_const _).mul h1 |>.mul h2) hd |>.sub
    (differentiableAt_const _)).differentiableWithinAt

lemma dslope_cC_ne_zero {s : ℂ} (hs : s ∈ unitStrip) : dslope cC (1 / 2) s ≠ 0 := by
  by_cases h : s = 1 / 2
  · rw [h, dslope_same]
    have : HasDerivAt cC (-Complex.sin ((π : ℂ) * (1 / 2)) * ((π : ℂ) * 1)) (1 / 2) := by
      unfold cC
      exact HasDerivAt.ccos ((hasDerivAt_id (1 / 2 : ℂ)).const_mul (π : ℂ))
    rw [this.deriv]
    have : (π : ℂ) * (1 / 2) = π / 2 := by ring
    rw [this, Complex.sin_pi_div_two]
    simp
  · rw [dslope_of_ne _ h, slope_def_field, cC_half, sub_zero]
    exact div_ne_zero (fun h0 => h ((cC_eq_zero_iff hs).mp h0)) (sub_ne_zero.mpr h)

/-- The strip function: `Ψ̂(s) = -π (1/(√2 k g) - 1)/cos(πs) - √2/k`, with the removable singularity at
`s = 1/2` filled by `dslope`. -/
noncomputable def psiHat (s : ℂ) : ℂ :=
  -(π : ℂ) * dslope Nf (1 / 2) s / dslope cC (1 / 2) s - ((√2 : ℝ) : ℂ) / kC s

lemma differentiableOn_psiHat : DifferentiableOn ℂ psiHat unitStrip := by
  have h1 : DifferentiableOn ℂ (dslope Nf (1 / 2)) unitStrip :=
    (Complex.differentiableOn_dslope (isOpen_unitStrip.mem_nhds half_mem)).mpr differentiableOn_Nf
  have h2 : DifferentiableOn ℂ (dslope cC (1 / 2)) unitStrip :=
    (Complex.differentiableOn_dslope (isOpen_unitStrip.mem_nhds half_mem)).mpr differentiableOn_cC
  intro s hs
  unfold psiHat
  refine DifferentiableWithinAt.sub (DifferentiableWithinAt.div ?_ (h2 s hs) (dslope_cC_ne_zero hs)) ?_
  · exact (differentiableWithinAt_const (-(π : ℂ))).mul (h1 s hs)
  · exact DifferentiableWithinAt.div (differentiableWithinAt_const _) (differentiableOn_kC s hs) (kC_ne_zero hs)

lemma psiHat_eq {s : ℂ} (hs : s ∈ unitStrip) (hne : s ≠ 1 / 2) :
    psiHat s = -(π : ℂ) * Nf s / cC s - ((√2 : ℝ) : ℂ) / kC s := by
  unfold psiHat
  rw [dslope_of_ne _ hne, dslope_of_ne _ hne, slope_def_field, slope_def_field, Nf_half, cC_half,
    sub_zero, sub_zero]
  have h1 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : cC s ≠ 0 := fun h0 => hne ((cC_eq_zero_iff hs).mp h0)
  have h3 : s * 2 - 1 ≠ 0 := by intro h; apply h1; linear_combination h / 2
  field_simp

/-! ### Boundedness of `Ψ̂` near `s = 1` (through `tipE`) -/

lemma gS_eq_tipE {s : ℂ} (hs : s ∈ unitStrip) (hk' : ‖((√2 : ℝ) : ℂ) * kC s‖ < 1) :
    gS s = tipE (((√2 : ℝ) : ℂ) * kC s) := by
  have hre : 0 < (((√2 : ℝ) : ℂ) * kC s).re := by
    have : (0 : ℝ) < √2 := by positivity
    simpa using mul_pos this (re_kC_pos hs)
  rw [← sInt_sub_one_sq hk' hre]
  unfold gS
  congr 1
  have h2 : (((√2 : ℝ) : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have := one_add_cC s
  rw [mul_pow, h2]
  show cC s = _
  linear_combination this

lemma psiHat_bdd_near_one : ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, ∀ s ∈ unitStrip, ‖kC s‖ < r → ‖psiHat s‖ ≤ M := by
  have hT0 : tipE 0 = (π : ℂ) / 2 := tipE_zero
  have hTc : ContinuousAt (fun k : ℂ => tipE (((√2 : ℝ) : ℂ) * k)) 0 := by
    have : ContinuousAt tipE (((√2 : ℝ) : ℂ) * 0) := by
      rw [mul_zero]
      exact differentiableOn_tipE.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
    exact this.comp (f := fun k : ℂ => ((√2 : ℝ) : ℂ) * k) (by fun_prop)
  have hev : ∀ᶠ k in 𝓝 (0 : ℂ), tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 ∧ 2 * k ^ 2 - 1 ≠ 0 ∧ ‖((√2 : ℝ) : ℂ) * k‖ < 1 := by
    have h1 : ∀ᶠ k in 𝓝 (0 : ℂ), tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 := by
      have : tipE (((√2 : ℝ) : ℂ) * 0) ≠ 0 := by
        rw [mul_zero, hT0]
        simp
      exact hTc.eventually_ne this
    have h2 : ∀ᶠ k in 𝓝 (0 : ℂ), 2 * k ^ 2 - 1 ≠ 0 := by
      have hc : ContinuousAt (fun k : ℂ => 2 * k ^ 2 - 1) 0 := by fun_prop
      exact hc.eventually_ne (by norm_num)
    have h3 : ∀ᶠ k in 𝓝 (0 : ℂ), ‖((√2 : ℝ) : ℂ) * k‖ < 1 := by
      have hc : ContinuousAt (fun k : ℂ => ‖((√2 : ℝ) : ℂ) * k‖) 0 := by fun_prop
      exact hc.eventually (gt_mem_nhds (by simp))
    exact h1.and (h2.and h3)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set r : ℝ := min r₀ (1 / 4) with hr
  have hrpos : 0 < r := lt_min hr₀ (by norm_num)
  set Mf : ℂ → ℂ := fun k => -(π : ℂ) / (((√2 : ℝ) : ℂ) * (2 * k ^ 2 - 1) * tipE (((√2 : ℝ) : ℂ) * k)) -
    ((√2 : ℝ) : ℂ) with hMf
  have hMfd : DifferentiableOn ℂ Mf (Metric.ball (0 : ℂ) r₀) := by
    intro k hk
    have hk' := hball (by simpa using hk)
    have hd : DifferentiableAt ℂ tipE (((√2 : ℝ) : ℂ) * k) :=
      differentiableOn_tipE.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hk'.2.2))
    have hd2 : DifferentiableAt ℂ (fun k : ℂ => tipE (((√2 : ℝ) : ℂ) * k)) k :=
      DifferentiableAt.comp (g := tipE) (f := fun k : ℂ => ((√2 : ℝ) : ℂ) * k) k hd (by fun_prop)
    have hden : ((√2 : ℝ) : ℂ) * (2 * k ^ 2 - 1) * tipE (((√2 : ℝ) : ℂ) * k) ≠ 0 :=
      mul_ne_zero (mul_ne_zero sqrt2_ne hk'.2.1) hk'.1
    have : DifferentiableAt ℂ Mf k := by
      refine DifferentiableAt.sub (DifferentiableAt.div (differentiableAt_const _) ?_ hden)
        (differentiableAt_const _)
      exact ((differentiableAt_const _).mul (by fun_prop)).mul hd2
    exact this.differentiableWithinAt
  have hMf0 : Mf 0 = 0 := by
    simp only [hMf]
    rw [mul_zero, hT0]
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 := sqrt2_ne
    field_simp
    have h3 : (((√2 : ℝ)) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    simp
    linear_combination h3
  have hφd : DifferentiableOn ℂ (fun k => dslope Mf 0 k + (π : ℂ) / (2 * k ^ 2 - 1)) (Metric.ball (0 : ℂ) r₀) := by
    have h1 : DifferentiableOn ℂ (dslope Mf 0) (Metric.ball (0 : ℂ) r₀) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))).mpr hMfd
    intro k hk
    have hk' := hball (by simpa using hk)
    refine (h1 k hk).add (DifferentiableWithinAt.div (differentiableWithinAt_const _) (by fun_prop) hk'.2.1)
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) (r / 2)) := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun k => dslope Mf 0 k + (π : ℂ) / (2 * k ^ 2 - 1)) (Metric.closedBall (0 : ℂ) (r / 2)) :=
    hφd.continuousOn.mono (fun k hk => by
      rw [Metric.mem_closedBall, dist_zero_right] at hk
      rw [Metric.mem_ball, dist_zero_right]
      have : r ≤ r₀ := min_le_left _ _
      linarith)
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
  refine ⟨r / 2, by positivity, M, fun s hs hks => ?_⟩
  have hkne := kC_ne_zero hs
  have hkr : ‖kC s‖ < r₀ := by
    have : r ≤ r₀ := min_le_left _ _
    linarith
  have hk4 : ‖kC s‖ < 1 / 4 := by
    have : r ≤ 1 / 4 := min_le_right _ _
    linarith
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
  have hbound := hM (kC s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hks.le)
  convert hbound using 1
  · unfold Nf
    rw [hg, hcc]
    have h0 : dslope Mf 0 (kC s) = Mf (kC s) / kC s := by
      rw [dslope_of_ne _ hkne, slope_def_field, hMf0]; simp
    rw [h0]
    simp only [hMf]
    have hden : ((√2 : ℝ) : ℂ) * (2 * kC s ^ 2 - 1) * tipE (((√2 : ℝ) : ℂ) * kC s) ≠ 0 :=
      mul_ne_zero (mul_ne_zero sqrt2_ne hb.2.1) hb.1
    have h2 := sqrt2_ne
    have h3 := hb.1
    have h4 := hb.2.1
    field_simp
    ring_nf

/-! ### Edge values -/

/-- The explicit expression `Ψ₁ = -π N/c - √2/k` (valid on the strip off `s = 1/2`). -/
noncomputable def psiOne (g : ℂ) (k c : ℂ) : ℂ :=
  -(π : ℂ) * (1 / (((√2 : ℝ) : ℂ) * k * g) - 1) / c - ((√2 : ℝ) : ℂ) / k

lemma psiHat_eq' {s : ℂ} (hs : s ∈ unitStrip) (hne : s ≠ 1 / 2) :
    psiHat s = psiOne (gS s) (kC s) (cC s) := by
  rw [psiHat_eq hs hne]; unfold psiOne Nf; ring

lemma kC_left (τ : ℝ) : kC ((τ : ℂ) * Complex.I) = ((Real.cosh (π * τ / 2) : ℝ) : ℂ) := by
  unfold kC
  have : (π : ℂ) * ((τ : ℂ) * Complex.I) / 2 = ((π * τ / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.cos_mul_I, ← Complex.ofReal_cosh]

lemma cC_left (τ : ℝ) : cC ((τ : ℂ) * Complex.I) = ((Real.cosh (π * τ) : ℝ) : ℂ) := by
  unfold cC
  have : (π : ℂ) * ((τ : ℂ) * Complex.I) = ((π * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.cos_mul_I, ← Complex.ofReal_cosh]

lemma kC_right (τ : ℝ) : kC (1 + (τ : ℂ) * Complex.I) = -(Complex.I * ((Real.sinh (π * τ / 2) : ℝ) : ℂ)) := by
  unfold kC
  have : (π : ℂ) * (1 + (τ : ℂ) * Complex.I) / 2 = ((π / 2 : ℝ) : ℂ) + ((π * τ / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, ← Complex.ofReal_sin,
    Real.sin_pi_div_two, ← Complex.ofReal_sinh]
  push_cast; ring

lemma cC_right (τ : ℝ) : cC (1 + (τ : ℂ) * Complex.I) = -((Real.cosh (π * τ) : ℝ) : ℂ) := by
  unfold cC
  have : (π : ℂ) * (1 + (τ : ℂ) * Complex.I) = ((π : ℝ) : ℂ) + ((π * τ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.cos_add_mul_I, ← Complex.ofReal_cos, Real.cos_pi, ← Complex.ofReal_sin, Real.sin_pi,
    ← Complex.ofReal_cosh]
  push_cast; ring

lemma continuousAt_cC (z : ℂ) : ContinuousAt cC z := by unfold cC; fun_prop
lemma continuousAt_kC (z : ℂ) : ContinuousAt kC z := by unfold kC; fun_prop

lemma cosh_pos_aux (x : ℝ) : (0 : ℝ) < Real.cosh x := Real.cosh_pos x

lemma psiHat_limit_left {τ : ℝ} (_hτ : τ ≠ 0) :
    Tendsto psiHat (𝓝[unitStrip] ((τ : ℂ) * Complex.I))
      (𝓝 (psiOne (sInt (((Real.cosh (π * τ) : ℝ)) : ℂ)) ((Real.cosh (π * τ / 2) : ℝ) : ℂ)
        ((Real.cosh (π * τ) : ℝ) : ℂ))) := by
  set z : ℂ := (τ : ℂ) * Complex.I with hz
  have hcz : cC z ∈ sDom := by
    rw [hz, cC_left]
    rintro ⟨_, hre⟩
    simp only [Complex.ofReal_re] at hre
    have := Real.one_le_cosh (π * τ); linarith
  have hcosh_ne : ((Real.cosh (π * τ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have hcosh2_ne : ((Real.cosh (π * τ / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
  have hsI : ContinuousAt sInt (cC z) :=
    differentiableOn_sInt.continuousOn.continuousAt (isOpen_sDom.mem_nhds hcz)
  have hg : ContinuousAt (fun s => sInt (cC s)) z := hsI.comp (f := cC) (continuousAt_cC z)
  have hgne : sInt (cC z) ≠ 0 := sInt_ne_zero hcz
  have hcont : ContinuousAt (fun s => psiOne (sInt (cC s)) (kC s) (cC s)) z := by
    unfold psiOne
    have hk := continuousAt_kC z
    have hc := continuousAt_cC z
    have hk0 : kC z ≠ 0 := by rw [hz, kC_left]; exact hcosh2_ne
    have hc0 : cC z ≠ 0 := by rw [hz, cC_left]; exact hcosh_ne
    refine ContinuousAt.sub (ContinuousAt.div (ContinuousAt.mul continuousAt_const
      (ContinuousAt.sub (ContinuousAt.div continuousAt_const
        ((continuousAt_const.mul hk).mul hg) (mul_ne_zero (mul_ne_zero sqrt2_ne hk0) hgne))
        continuousAt_const)) hc hc0)
      (ContinuousAt.div continuousAt_const hk hk0)
  have hval : psiOne (sInt (cC z)) (kC z) (cC z) =
      psiOne (sInt (((Real.cosh (π * τ) : ℝ)) : ℂ)) ((Real.cosh (π * τ / 2) : ℝ) : ℂ)
        ((Real.cosh (π * τ) : ℝ) : ℂ) := by
    rw [hz, cC_left, kC_left]
  rw [← hval]
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hne : ∀ᶠ s in 𝓝 z, s ≠ 1 / 2 := by
    refine eventually_ne_nhds ?_
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hne] with s hs hne
  exact (psiHat_eq' hs hne).symm

lemma cosh_sub_one_eq (τ : ℝ) : Real.cosh (π * τ) - 1 = 2 * Real.sinh (π * τ / 2) ^ 2 := by
  have := Real.cosh_two_mul (π * τ / 2)
  rw [show 2 * (π * τ / 2) = π * τ by ring] at this
  rw [this]; nlinarith [Real.cosh_sq (π * τ / 2)]

lemma sqrt_cosh_sub_one (τ : ℝ) : √(Real.cosh (π * τ) - 1) = √2 * |Real.sinh (π * τ / 2)| := by
  rw [cosh_sub_one_eq, Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]

lemma arsinh_sqrt_cosh_sub_one_pos {τ : ℝ} (hτ : 0 < τ) :
    Real.arsinh (√(Real.cosh (π * τ) - 1)) = π * vT τ := by
  have hs : 0 < Real.sinh (π * τ / 2) := Real.sinh_pos_iff.mpr (by positivity)
  rw [sqrt_cosh_sub_one, abs_of_pos hs]
  unfold vT
  have := Real.pi_pos
  field_simp

lemma arsinh_sqrt_cosh_sub_one_neg {τ : ℝ} (hτ : τ < 0) :
    Real.arsinh (√(Real.cosh (π * τ) - 1)) = -(π * vT τ) := by
  have hs : Real.sinh (π * τ / 2) < 0 := Real.sinh_neg_iff.mpr (by
    have := Real.pi_pos; nlinarith)
  rw [sqrt_cosh_sub_one, abs_of_neg hs]
  unfold vT
  have := Real.pi_pos
  rw [show √2 * -Real.sinh (π * τ / 2) = -(√2 * Real.sinh (π * τ / 2)) by ring, Real.arsinh_neg]
  field_simp

/-- The boundary value of `g` on the right edge (uniform in the sign of `τ`). -/
noncomputable def Lg (τ : ℝ) : ℂ :=
  ((π / √(Real.cosh (π * τ)) : ℝ) : ℂ) * (1 / 2 + Complex.I * ((vT τ : ℝ) : ℂ))

lemma sDom_conj {v : ℂ} (hv : v ∈ sDom) : starRingEnd ℂ v ∈ sDom := by
  rintro ⟨h1, h2⟩
  apply hv
  simp at h1 h2
  exact ⟨by linarith, by linarith⟩

lemma re_sInt_oncut_pos {c : ℝ} (hc : 1 < c) : 0 < (sInt (-(c : ℂ))).re := by
  rw [sInt_oncut hc]
  have : 0 < c := by linarith
  simp
  positivity

lemma tendsto_gS_right {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto gS (𝓝[unitStrip] (1 + (τ : ℂ) * Complex.I)) (𝓝 (Lg τ)) := by
  set z : ℂ := 1 + (τ : ℂ) * Complex.I with hz
  have hc1 : 1 < Real.cosh (π * τ) := by
    have h := Real.one_lt_cosh.mpr (mul_ne_zero Real.pi_ne_zero hτ)
    exact h
  have hc₀ : cC z = -((Real.cosh (π * τ) : ℝ) : ℂ) := by rw [hz, cC_right]
  have hhere : (cC z).im = 0 ∧ (cC z).re < 0 := by
    rw [hc₀]
    constructor
    · simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]
    · simp only [Complex.neg_re, Complex.ofReal_re]; linarith [Real.cosh_pos (π * τ)]
  have hcl : Tendsto cC (𝓝[unitStrip] z) (𝓝 (cC z)) :=
    (continuousAt_cC z).tendsto.mono_left nhdsWithin_le_nhds
  have hcut := continuousWithinAt_sInt_cut hhere.1 hhere.2
  have himsign : ∀ s ∈ unitStrip, (cC s).im = -(Real.sin (π * s.re) * Real.sinh (π * s.im)) := fun s _ => im_cC s
  have hsinpos : ∀ s ∈ unitStrip, 0 < Real.sin (π * s.re) := fun s hs =>
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1, Real.pi_pos]) (by nlinarith [hs.2, Real.pi_pos])
  have hval := sInt_oncut hc1
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · -- τ < 0 : upper half plane
    have hev : ∀ᶠ s in 𝓝[unitStrip] z, cC s ∈ {v : ℂ | 0 ≤ v.im} := by
      have : ∀ᶠ s in 𝓝 z, s.im < 0 := by
        have hc : ContinuousAt (fun s : ℂ => s.im) z := Complex.continuous_im.continuousAt
        exact hc.eventually (gt_mem_nhds (by simp [hz, hneg]))
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with s hs hsi
      show 0 ≤ (cC s).im
      rw [himsign s hs]
      have : Real.sinh (π * s.im) < 0 := Real.sinh_neg_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith [hsinpos s hs]
    have h1 : Tendsto cC (𝓝[unitStrip] z) (𝓝[{v : ℂ | 0 ≤ v.im}] (cC z)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hcl, hev⟩
    have h2 := hcut.tendsto.comp h1
    have : sInt (cC z) = Lg τ := by
      rw [hc₀, hval]
      have hv := arsinh_sqrt_cosh_sub_one_neg hneg
      unfold Lg
      rw [hv]
      push_cast
      ring
    rw [← this]
    exact h2
  · -- τ > 0 : lower half plane, use conjugation
    set u : ℂ → ℂ := fun s => starRingEnd ℂ (cC s) with hu
    have hev : ∀ᶠ s in 𝓝[unitStrip] z, u s ∈ {v : ℂ | 0 ≤ v.im} := by
      have : ∀ᶠ s in 𝓝 z, 0 < s.im := by
        have hc : ContinuousAt (fun s : ℂ => s.im) z := Complex.continuous_im.continuousAt
        exact hc.eventually (lt_mem_nhds (by simp [hz, hpos]))
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with s hs hsi
      show 0 ≤ (starRingEnd ℂ (cC s)).im
      rw [Complex.conj_im, himsign s hs]
      have : 0 < Real.sinh (π * s.im) := Real.sinh_pos_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith [hsinpos s hs]
    have hcl' : Tendsto u (𝓝[unitStrip] z) (𝓝 (starRingEnd ℂ (cC z))) :=
      (Complex.continuous_conj.tendsto _).comp hcl
    have hcz : starRingEnd ℂ (cC z) = cC z := by
      rw [hc₀, map_neg, Complex.conj_ofReal]
    rw [hcz] at hcl'
    have h1 : Tendsto u (𝓝[unitStrip] z) (𝓝[{v : ℂ | 0 ≤ v.im}] (cC z)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hcl', hev⟩
    have h2 := (Complex.continuous_conj.tendsto _).comp (hcut.tendsto.comp h1)
    have heq : ∀ s ∈ unitStrip, gS s = starRingEnd ℂ (sInt (u s)) := by
      intro s hs
      unfold gS
      rw [← sInt_conj (sDom_conj (cC_mem_sDom hs))]
      simp only [Complex.conj_conj]
      rfl
    have : starRingEnd ℂ (sInt (cC z)) = Lg τ := by
      rw [hc₀, hval]
      have hv := arsinh_sqrt_cosh_sub_one_pos hpos
      unfold Lg
      rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal, hv]
      push_cast
      ring
    rw [← this]
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (heq s hs).symm

lemma tendsto_psiOne {F : Filter ℂ} {gf kf cf : ℂ → ℂ} {g₀ k₀ c₀ : ℂ} (hg : Tendsto gf F (𝓝 g₀))
    (hk : Tendsto kf F (𝓝 k₀)) (hc : Tendsto cf F (𝓝 c₀)) (hg0 : g₀ ≠ 0) (hk0 : k₀ ≠ 0) (hc0 : c₀ ≠ 0) :
    Tendsto (fun s => psiOne (gf s) (kf s) (cf s)) F (𝓝 (psiOne g₀ k₀ c₀)) := by
  unfold psiOne
  have h1 : Tendsto (fun s => ((√2 : ℝ) : ℂ) * kf s * gf s) F (𝓝 (((√2 : ℝ) : ℂ) * k₀ * g₀)) :=
    (tendsto_const_nhds.mul hk).mul hg
  have h2 := (tendsto_const_nhds (x := (1 : ℂ))).div h1 (mul_ne_zero (mul_ne_zero sqrt2_ne hk0) hg0)
  have h3 := (tendsto_const_nhds (x := -(π : ℂ))).mul (h2.sub (tendsto_const_nhds (x := (1 : ℂ))))
  exact (h3.div hc hc0).sub ((tendsto_const_nhds (x := ((√2 : ℝ) : ℂ))).div hk hk0)

lemma re_Lg (τ : ℝ) : (Lg τ).re = π / √(Real.cosh (π * τ)) * (1 / 2) := by
  unfold Lg; rw [Complex.re_ofReal_mul]; simp

lemma Lg_ne_zero (τ : ℝ) : Lg τ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_Lg] at this
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hs : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hc
  have hp : 0 < π / √(Real.cosh (π * τ)) * (1 / 2) := by positivity
  simp at this
  linarith

lemma psiHat_limit_right {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto psiHat (𝓝[unitStrip] (1 + (τ : ℂ) * Complex.I))
      (𝓝 (psiOne (Lg τ) (kC (1 + (τ : ℂ) * Complex.I)) (cC (1 + (τ : ℂ) * Complex.I)))) := by
  set z : ℂ := 1 + (τ : ℂ) * Complex.I with hz
  have hsh : Real.sinh (π * τ / 2) ≠ 0 := by
    intro h
    have := Real.sinh_eq_zero.mp h
    have hp := Real.pi_pos
    rcases mul_eq_zero.mp (by simpa using this : π * τ = 0) with h | h
    · exact hp.ne' h
    · exact hτ h
  have hk0 : kC z ≠ 0 := by
    rw [hz, kC_right]
    intro h
    have : Complex.I * ((Real.sinh (π * τ / 2) : ℝ) : ℂ) = 0 := neg_eq_zero.mp h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Complex.I_ne_zero h1
    · exact hsh (by exact_mod_cast h1)
  have hc0 : cC z ≠ 0 := by
    rw [hz, cC_right]
    intro h
    have : ((Real.cosh (π * τ) : ℝ) : ℂ) = 0 := neg_eq_zero.mp h
    exact (Real.cosh_pos _).ne' (by exact_mod_cast this)
  have hlim := tendsto_psiOne (F := 𝓝[unitStrip] z) (gf := gS) (kf := kC) (cf := cC)
    (tendsto_gS_right hτ) ((continuousAt_kC z).tendsto.mono_left nhdsWithin_le_nhds)
    ((continuousAt_cC z).tendsto.mono_left nhdsWithin_le_nhds) (Lg_ne_zero τ) hk0 hc0
  refine hlim.congr' ?_
  have hne : ∀ᶠ s in 𝓝 z, s ≠ 1 / 2 := by
    refine eventually_ne_nhds ?_
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hne] with s hs hne
  exact (psiHat_eq' hs hne).symm

/-! ### Limits at all edge points; the boundary extension -/

lemma closure_unitStrip_subset : closure unitStrip ⊆ unitStripCl :=
  closure_minimal unitStrip_subset_cl
    (isClosed_le continuous_const Complex.continuous_re |>.inter (isClosed_le Complex.continuous_re continuous_const))

lemma exists_limit_psiHat {z : ℂ} (hz : z ∈ unitStripCl \ {0, 1}) :
    ∃ L, Tendsto psiHat (𝓝[unitStrip] z) (𝓝 L) := by
  obtain ⟨⟨h0, h1⟩, hne⟩ := hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  rcases h0.eq_or_lt with hre0 | hre0
  · -- left edge
    have hz' : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [← hre0]
    have hτ : z.im ≠ 0 := by
      intro h; apply hne.1; apply Complex.ext <;> simp [← hre0, h]
    rw [hz']
    exact ⟨_, psiHat_limit_left hτ⟩
  · rcases h1.eq_or_lt with hre1 | hre1
    · have hz' : z = 1 + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hre1]
      have hτ : z.im ≠ 0 := by
        intro h; apply hne.2; apply Complex.ext <;> simp [hre1, h]
      rw [hz']
      exact ⟨_, psiHat_limit_right hτ⟩
    · have hzs : z ∈ unitStrip := ⟨hre0, hre1⟩
      exact ⟨psiHat z, (differentiableOn_psiHat.continuousOn.continuousAt
        (isOpen_unitStrip.mem_nhds hzs)).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The boundary extension of `Ψ̂`. -/
noncomputable def psiTil : ℂ → ℂ := extLim unitStrip psiHat

lemma psiTil_of_mem {s : ℂ} (hs : s ∈ unitStrip) : psiTil s = psiHat s :=
  extLim_of_mem hs (differentiableOn_psiHat.continuousOn.continuousAt
    (isOpen_unitStrip.mem_nhds hs)).continuousWithinAt

lemma continuousOn_psiTil : ContinuousOn psiTil (unitStripCl \ {0, 1}) :=
  (continuousOn_extLim (U := unitStrip) (f := psiHat) (bad := {0, 1})
    (fun _z hz => exists_limit_psiHat ⟨closure_unitStrip_subset hz.1, hz.2⟩)).mono
    (fun _z hz => ⟨unitStripCl_subset_closure hz.1, hz.2⟩)

lemma psiTil_left {τ : ℝ} (hτ : τ ≠ 0) :
    psiTil ((τ : ℂ) * Complex.I) = psiOne (sInt (((Real.cosh (π * τ) : ℝ)) : ℂ))
      ((Real.cosh (π * τ / 2) : ℝ) : ℂ) ((Real.cosh (π * τ) : ℝ) : ℂ) :=
  extLim_eq_of_tendsto (unitStripCl_subset_closure ⟨by simp, by simp⟩) (psiHat_limit_left hτ)

lemma psiTil_right {τ : ℝ} (hτ : τ ≠ 0) :
    psiTil (1 + (τ : ℂ) * Complex.I) = psiOne (Lg τ) (kC (1 + (τ : ℂ) * Complex.I))
      (cC (1 + (τ : ℂ) * Complex.I)) :=
  extLim_eq_of_tendsto (unitStripCl_subset_closure ⟨by simp, by simp⟩) (psiHat_limit_right hτ)

/-! ### The decay bound for `Ψ̂` far from the real axis -/

lemma norm_cos_sq (w : ℂ) : ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_cos', im_cos']
  have := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [this, h2]

lemma sinh_ge_exp {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h2 : 2 ≤ Real.exp x ^ 2 := by
    have : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx
    have h3 : 2 < Real.exp 1 := by
      have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith
    nlinarith
  have hp := Real.exp_pos x
  have hq := Real.exp_pos (-x)
  nlinarith

lemma cosh_le_two_sinh {x : ℝ} (hx : 1 ≤ x) : Real.cosh x ≤ 2 * Real.sinh x := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have h1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h2 : 3 ≤ Real.exp x ^ 2 := by
    have : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx
    have h3 : 2.7 < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    nlinarith
  have hp := Real.exp_pos x
  have hq := Real.exp_pos (-x)
  nlinarith

lemma arsinh_ge {x : ℝ} (hx : 0 < x) : x / (1 + x) ≤ Real.arsinh x := by
  have h1 : Real.log (1 + x) ≤ Real.arsinh x := by
    unfold Real.arsinh
    apply Real.log_le_log (by linarith)
    have : 1 ≤ √(1 + x ^ 2) := Real.one_le_sqrt.mpr (by nlinarith)
    linarith
  have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
  have h3 : x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
  linarith

lemma norm_gS_lower {s : ℂ} (hs : s ∈ unitStrip) (hτ : s.im ≠ 0) :
    (1 / √2) * (1 / (1 + √‖cC s‖)) ≤ ‖gS s‖ := by
  have hsin : 0 < Real.sin (π * s.re) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1, Real.pi_pos]) (by nlinarith [hs.2, Real.pi_pos])
  have hρ : 0 < ‖cC s‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.im h
    rw [im_cC] at this
    simp at this
    rcases this with h1 | h1
    · linarith
    · exact hτ h1
  have hlow : ∀ u : ℂ, u.im < 0 → 0 < ‖u‖ → (1 / √2) * (1 / (1 + √‖u‖)) ≤ ‖sInt u‖ := by
    intro u hu hu0
    refine le_trans ?_ (norm_sInt_lower hu hu0)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hr : 0 < √‖u‖ := Real.sqrt_pos.mpr hu0
    have := arsinh_ge hr
    rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at this
    have h2 : 1 ≤ Real.arsinh (√‖u‖) / √‖u‖ * (1 + √‖u‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]; linarith
    exact h2
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · -- τ < 0: Im cC s > 0, conjugate
    have hu : (starRingEnd ℂ (cC s)).im < 0 := by
      rw [Complex.conj_im, im_cC]
      have : Real.sinh (π * s.im) < 0 := Real.sinh_neg_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith
    have := hlow _ hu (by rw [Complex.norm_conj]; exact hρ)
    rw [Complex.norm_conj] at this
    have e : ‖gS s‖ = ‖sInt (starRingEnd ℂ (cC s))‖ := by
      unfold gS
      rw [sInt_conj (cC_mem_sDom hs), Complex.norm_conj]
      rfl
    rw [e]; exact this
  · have hu : (cC s).im < 0 := by
      rw [im_cC]
      have : 0 < Real.sinh (π * s.im) := Real.sinh_pos_iff.mpr (by nlinarith [Real.pi_pos])
      nlinarith
    exact hlow _ hu hρ

lemma norm_psiOne_le {g k c : ℂ} :
    ‖psiOne g k c‖ ≤ π * (1 / (√2 * ‖k‖ * ‖g‖) + 1) / ‖c‖ + √2 / ‖k‖ := by
  unfold psiOne
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_one]
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < √2)]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < √2)]

lemma norm_kC_ge {s : ℂ} : Real.sinh (π * |s.im| / 2) ≤ ‖kC s‖ := by
  have h := norm_cos_sq (π * s / 2)
  have hre : ((π : ℂ) * s / 2).re = π * s.re / 2 := by simp
  have him : ((π : ℂ) * s / 2).im = π * s.im / 2 := by simp
  rw [hre, him] at h
  have hsq : Real.sinh (π * |s.im| / 2) ^ 2 ≤ ‖kC s‖ ^ 2 := by
    unfold kC; rw [h]
    have : Real.sinh (π * |s.im| / 2) ^ 2 = Real.sinh (π * s.im / 2) ^ 2 := by
      rcases abs_cases s.im with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
      · rw [h1, show π * -s.im / 2 = -(π * s.im / 2) by ring, Real.sinh_neg]; ring
    rw [this]; nlinarith [sq_nonneg (Real.cos (π * s.re / 2))]
  exact le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _) |> fun h => by
    simpa using abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2

lemma norm_cC_ge {s : ℂ} : Real.sinh (π * |s.im|) ≤ ‖cC s‖ := by
  have h := norm_cos_sq ((π : ℂ) * s)
  rw [re_pi_mul, im_pi_mul] at h
  have hsq : Real.sinh (π * |s.im|) ^ 2 ≤ ‖cC s‖ ^ 2 := by
    unfold cC; rw [h]
    have : Real.sinh (π * |s.im|) ^ 2 = Real.sinh (π * s.im) ^ 2 := by
      rcases abs_cases s.im with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
      · rw [h1, show π * -s.im = -(π * s.im) by ring, Real.sinh_neg]; ring
    rw [this]; nlinarith [sq_nonneg (Real.cos (π * s.re))]
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2

lemma norm_cC_le {s : ℂ} : ‖cC s‖ ≤ Real.cosh (π * |s.im|) := by
  have h := norm_cos_sq ((π : ℂ) * s)
  rw [re_pi_mul, im_pi_mul] at h
  have hsq : ‖cC s‖ ^ 2 ≤ Real.cosh (π * |s.im|) ^ 2 := by
    unfold cC; rw [h]
    have : Real.sinh (π * s.im) ^ 2 = Real.sinh (π * |s.im|) ^ 2 := by
      rcases abs_cases s.im with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
      · rw [h1, show π * -s.im = -(π * s.im) by ring, Real.sinh_neg]; ring
    rw [Real.cosh_sq, ← this]
    nlinarith [Real.cos_sq_le_one (π * s.re)]
  exact abs_le_of_sq_le_sq' hsq (Real.cosh_pos _).le |>.2

lemma psiHat_far : ∃ M : ℝ, ∀ s ∈ unitStrip, 1 ≤ |s.im| →
    ‖psiHat s‖ ≤ M * Real.exp (-(π / 2 * |s.im|)) := by
  have hpi := Real.pi_pos
  have hs1 : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  set B : ℝ := 1 / Real.sinh 1 + 2 * √2 with hB
  refine ⟨4 * π * (B + 1) + 4 * √2, fun s hs hτ => ?_⟩
  set X : ℝ := π * |s.im| / 2 with hX
  have hX1 : 1 ≤ X := by
    have : (2 : ℝ) < π := by linarith [Real.pi_gt_three]
    rw [hX]; nlinarith
  have hne : s ≠ 1 / 2 := by
    intro h; rw [h] at hτ; simp at hτ; linarith
  have hτ0 : s.im ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
  rw [psiHat_eq' hs hne]
  have hk := norm_kC_ge (s := s)
  have hc := norm_cC_ge (s := s)
  have hcle := norm_cC_le (s := s)
  have hg := norm_gS_lower hs hτ0
  rw [← hX] at hk
  have hπτ : π * |s.im| = 2 * X := by rw [hX]; ring
  rw [hπτ] at hc hcle
  have hsX : Real.exp X / 4 ≤ Real.sinh X := sinh_ge_exp hX1
  have hsX1 : Real.sinh 1 ≤ Real.sinh X := Real.sinh_le_sinh.mpr hX1
  have hs2X : Real.exp X / 4 ≤ Real.sinh (2 * X) := by
    have := sinh_ge_exp (show 1 ≤ 2 * X by linarith)
    have h3 : Real.exp X ≤ Real.exp (2 * X) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hkpos : 0 < ‖kC s‖ := lt_of_lt_of_le (lt_of_lt_of_le hs1 hsX1) hk
  have hcpos : 0 < ‖cC s‖ := lt_of_lt_of_le (by
    have := Real.exp_pos X; linarith) (hc.trans' hs2X)
  have hgpos : 0 < ‖gS s‖ := norm_pos_iff.mpr (gS_ne_zero hs)
  refine norm_psiOne_le.trans ?_
  -- bound `1/(√2 ‖k‖ ‖g‖) ≤ B`
  have hcosh2 : Real.cosh (2 * X) ≤ 2 * Real.cosh X ^ 2 := by
    rw [Real.cosh_two_mul]; nlinarith [Real.cosh_sq X]
  have hsq : √‖cC s‖ ≤ 2 * √2 * ‖kC s‖ := by
    have h1 : ‖cC s‖ ≤ (2 * √2 * ‖kC s‖) ^ 2 := by
      have h2 : Real.cosh X ≤ 2 * Real.sinh X := cosh_le_two_sinh hX1
      have h3 : Real.cosh X ≤ 2 * ‖kC s‖ := by linarith
      calc ‖cC s‖ ≤ Real.cosh (2 * X) := hcle
        _ ≤ 2 * Real.cosh X ^ 2 := hcosh2
        _ ≤ 2 * (2 * ‖kC s‖) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact pow_le_pow_left₀ (Real.cosh_pos _).le h3 2
        _ = (2 * √2 * ‖kC s‖) ^ 2 := by
            rw [show (2 * √2 * ‖kC s‖) ^ 2 = 4 * (√2) ^ 2 * ‖kC s‖ ^ 2 by ring,
              Real.sq_sqrt (by norm_num)]; ring
    calc √‖cC s‖ ≤ √((2 * √2 * ‖kC s‖) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 2 * √2 * ‖kC s‖ := Real.sqrt_sq (by positivity)
  have hinv : 1 / (√2 * ‖kC s‖ * ‖gS s‖) ≤ B := by
    have hs2 : (0 : ℝ) < √2 := by positivity
    have h1 : ‖kC s‖ / (1 + √‖cC s‖) ≤ √2 * ‖kC s‖ * ‖gS s‖ := by
      have := mul_le_mul_of_nonneg_left hg (mul_nonneg hs2.le hkpos.le)
      calc ‖kC s‖ / (1 + √‖cC s‖) = √2 * ‖kC s‖ * ((1 / √2) * (1 / (1 + √‖cC s‖))) := by
            field_simp
        _ ≤ _ := this
    have hden : 0 < ‖kC s‖ / (1 + √‖cC s‖) := by positivity
    calc 1 / (√2 * ‖kC s‖ * ‖gS s‖) ≤ 1 / (‖kC s‖ / (1 + √‖cC s‖)) :=
          one_div_le_one_div_of_le hden h1
      _ = (1 + √‖cC s‖) / ‖kC s‖ := by field_simp
      _ ≤ (1 + 2 * √2 * ‖kC s‖) / ‖kC s‖ := by
          apply div_le_div_of_nonneg_right _ hkpos.le; linarith
      _ = 1 / ‖kC s‖ + 2 * √2 := by field_simp
      _ ≤ B := by
          rw [hB]
          have : 1 / ‖kC s‖ ≤ 1 / Real.sinh 1 :=
            one_div_le_one_div_of_le hs1 (hsX1.trans hk)
          linarith
  have hexp : Real.exp (-(π / 2 * |s.im|)) = Real.exp (-X) := by rw [hX]; ring_nf
  rw [hexp]
  have he : Real.exp (-X) = (Real.exp X)⁻¹ := Real.exp_neg X
  have hpos := Real.exp_pos X
  have h4c : 1 / ‖cC s‖ ≤ 4 * Real.exp (-X) := by
    rw [he, div_le_iff₀ hcpos]
    have : Real.exp X / 4 ≤ ‖cC s‖ := hc.trans' hs2X
    field_simp
    linarith
  have h4k : 1 / ‖kC s‖ ≤ 4 * Real.exp (-X) := by
    rw [he, div_le_iff₀ hkpos]
    have : Real.exp X / 4 ≤ ‖kC s‖ := hsX.trans hk
    field_simp
    linarith
  calc π * (1 / (√2 * ‖kC s‖ * ‖gS s‖) + 1) / ‖cC s‖ + √2 / ‖kC s‖
      ≤ π * (B + 1) * (1 / ‖cC s‖) + √2 * (1 / ‖kC s‖) := by
        rw [mul_one_div (π * (B + 1)), mul_one_div √2 ‖kC s‖]
        refine add_le_add ?_ le_rfl
        apply div_le_div_of_nonneg_right _ hcpos.le
        exact mul_le_mul_of_nonneg_left (by linarith) hpi.le
    _ ≤ π * (B + 1) * (4 * Real.exp (-X)) + √2 * (4 * Real.exp (-X)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h4c (by
            have : 0 < B := by rw [hB]; positivity
            positivity)
        · exact mul_le_mul_of_nonneg_left h4k (by positivity)
    _ = (4 * π * (B + 1) + 4 * √2) * Real.exp (-X) := by ring

/-! ### Boundedness near `s = 0`, the compact middle region, and the global bound -/

lemma psiHat_bdd_near_zero : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ s ∈ unitStrip, ‖s‖ < δ → ‖psiHat s‖ ≤ M := by
  have hc0 : cC 0 = 1 := by simp [cC]
  have hk0 : kC 0 = 1 := by simp [kC]
  have h1sD : (1 : ℂ) ∈ sDom := by rintro ⟨_, h⟩; simp at h; linarith
  have hsI : ContinuousAt sInt (cC 0) := by
    rw [hc0]; exact differentiableOn_sInt.continuousOn.continuousAt (isOpen_sDom.mem_nhds h1sD)
  have hg : Tendsto gS (𝓝 0) (𝓝 (gS 0)) :=
    (hsI.comp (f := cC) (continuousAt_cC 0)).tendsto
  have hgne : gS 0 ≠ 0 := by
    unfold gS; rw [show Complex.cos ((π : ℂ) * 0) = 1 by simp]; exact sInt_ne_zero h1sD
  have hlim := tendsto_psiOne (F := 𝓝 0) (gf := gS) (kf := kC) (cf := cC) hg
    (continuousAt_kC 0).tendsto (continuousAt_cC 0).tendsto hgne (by rw [hk0]; exact one_ne_zero)
    (by rw [hc0]; exact one_ne_zero)
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), ‖psiOne (gS s) (kC s) (cC s)‖ < ‖psiOne (gS 0) (kC 0) (cC 0)‖ + 1 :=
    hlim.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hne : ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 1 / 2 := eventually_ne_nhds (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hne)
  refine ⟨δ, hδ, ‖psiOne (gS 0) (kC 0) (cC 0)‖ + 1, fun s hs hsδ => ?_⟩
  have := hball (by simpa using hsδ : dist s 0 < δ)
  rw [psiHat_eq' hs this.2]
  exact this.1.le

lemma psiHat_bdd_mid {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ s ∈ unitStrip, |s.im| ≤ 1 → r ≤ ‖kC s‖ → δ ≤ ‖s‖ → ‖psiHat s‖ ≤ M := by
  set K : Set ℂ := {s | s ∈ unitStripCl ∧ |s.im| ≤ 1 ∧ r ≤ ‖kC s‖ ∧ δ ≤ ‖s‖} with hK
  have hKc : IsClosed K := by
    have h1 : IsClosed unitStripCl :=
      (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)
    have h2 : IsClosed {s : ℂ | |s.im| ≤ 1} := isClosed_le (by fun_prop) continuous_const
    have h3 : IsClosed {s : ℂ | r ≤ ‖kC s‖} :=
      isClosed_le continuous_const (by unfold kC; fun_prop)
    have h4 : IsClosed {s : ℂ | δ ≤ ‖s‖} := isClosed_le continuous_const continuous_norm
    exact h1.inter (h2.inter (h3.inter h4))
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset (fun s hs => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre := hs.1
    have him := hs.2.1
    have : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    have hre' : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith [hre.1], hre.2⟩
    linarith
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have hsub : K ⊆ unitStripCl \ {0, 1} := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h; have := hs.2.2.2; rw [h] at this; simp at this; linarith
    · intro h
      have := hs.2.2.1
      rw [h] at this
      have hk1 : kC 1 = 0 := by
        unfold kC; rw [show (π : ℂ) * 1 / 2 = π / 2 by ring]; exact Complex.cos_pi_div_two
      rw [hk1] at this; simp at this; linarith
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn (continuousOn_psiTil.mono hsub)
  refine ⟨M, fun s hs h1 h2 h3 => ?_⟩
  have := hM s ⟨unitStrip_subset_cl hs, h1, h2, h3⟩
  rwa [psiTil_of_mem hs] at this

/-- **The global bound** `‖Ψ̂(s)‖ ≤ C e^{-(π/2)|Im s|}` on the open strip. -/
theorem psiHat_bound : ∃ C : ℝ, ∀ s ∈ unitStrip, ‖psiHat s‖ ≤ C * Real.exp (-(π / 2 * |s.im|)) := by
  obtain ⟨r, hr, M1, h1⟩ := psiHat_bdd_near_one
  obtain ⟨δ, hδ, M0, h0⟩ := psiHat_bdd_near_zero
  obtain ⟨Mf, hf⟩ := psiHat_far
  obtain ⟨Mm, hm⟩ := psiHat_bdd_mid hr hδ
  have hpi := Real.pi_pos
  set E : ℝ := Real.exp (π / 2) with hE
  have hE1 : 0 < E := Real.exp_pos _
  refine ⟨|Mf| + |M1| * E + |M0| * E + |Mm| * E, fun s hs => ?_⟩
  have hpos := Real.exp_pos (-(π / 2 * |s.im|))
  by_cases hfar : 1 ≤ |s.im|
  · calc ‖psiHat s‖ ≤ Mf * Real.exp (-(π / 2 * |s.im|)) := hf s hs hfar
      _ ≤ |Mf| * Real.exp (-(π / 2 * |s.im|)) := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
      _ ≤ _ := by
          have : 0 ≤ |M1| * E + |M0| * E + |Mm| * E := by positivity
          nlinarith
  · push Not at hfar
    have hlow : 1 ≤ E * Real.exp (-(π / 2 * |s.im|)) := by
      rw [hE, ← Real.exp_add]
      apply Real.one_le_exp
      have : π / 2 * |s.im| ≤ π / 2 := by nlinarith [abs_nonneg s.im]
      linarith
    have key : ∀ M : ℝ, ‖psiHat s‖ ≤ M → ‖psiHat s‖ ≤ |M| * E * Real.exp (-(π / 2 * |s.im|)) := by
      intro M hM
      calc ‖psiHat s‖ ≤ |M| := hM.trans (le_abs_self _)
        _ = |M| * 1 := (mul_one _).symm
        _ ≤ |M| * (E * Real.exp (-(π / 2 * |s.im|))) := mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
        _ = _ := by ring
    have hnn : 0 ≤ |Mf| * Real.exp (-(π / 2 * |s.im|)) := by positivity
    by_cases hk : ‖kC s‖ < r
    · have := key M1 (h1 s hs hk)
      nlinarith [mul_nonneg (abs_nonneg M0) hE1.le, mul_nonneg (abs_nonneg Mm) hE1.le,
        mul_nonneg (mul_nonneg (abs_nonneg M0) hE1.le) hpos.le, mul_nonneg (mul_nonneg (abs_nonneg Mm) hE1.le) hpos.le]
    · push Not at hk
      by_cases h0' : ‖s‖ < δ
      · have := key M0 (h0 s hs h0')
        nlinarith [mul_nonneg (abs_nonneg M1) hE1.le, mul_nonneg (abs_nonneg Mm) hE1.le,
          mul_nonneg (mul_nonneg (abs_nonneg M1) hE1.le) hpos.le, mul_nonneg (mul_nonneg (abs_nonneg Mm) hE1.le) hpos.le]
      · push Not at h0'
        have := key Mm (hm s hs hfar.le hk h0')
        nlinarith [mul_nonneg (abs_nonneg M1) hE1.le, mul_nonneg (abs_nonneg M0) hE1.le,
          mul_nonneg (mul_nonneg (abs_nonneg M1) hE1.le) hpos.le, mul_nonneg (mul_nonneg (abs_nonneg M0) hE1.le) hpos.le]

end FormalResearch.ModularBootstrap.FiveTerm

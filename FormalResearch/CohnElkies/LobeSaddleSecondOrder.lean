module

public import FormalResearch.CohnElkies.LobeSaddleBounds
public import FormalResearch.CohnElkies.MellinT3Complete

/-!
# Second-Order Lobe Saddle Estimate (`ce_rate.tex`, `cel:total-saddle-2`)

Proves the second-order uniform saddle-point asymptotic (`cel:total-saddle-2` of `ce_rate.tex`)
for an abstract total multiplier `V(ζ)` that is holomorphic on `{ζ : ‖ζ - σ_*‖ < 3 d / 4}`
(`d = min σ_* (1 - σ_*)`) and bounded by `D · A` on `{‖ζ - σ_*‖ ≤ d / 2}`:
`(2π ξ I_val.re) / (K₀ √(2π) τ_sd) = V(σ_*) + O_{M, Λ, D}(A ε_L^2) + O_*(Λ_add ε e^{-3 z_+/320})`.

In particular, `V(σ_*)` is allowed to vanish (used by `cepe:abs-saddle` in `PreEdgeTangency.lean`
when the dual multiplier `W_D` has zeros on a compact tangency interval `J`).
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace FormalResearch.CohnElkies

/-! ### Auxiliary analytic and Taylor lemmas -/

private lemma norm_exp_sub_one_sub_id_le (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ (‖z‖ ^ 2 / 2) * Real.exp (max z.re 0) := by
  let φ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * z) - 1 - (t : ℂ) * z
  have hφ_deriv : ∀ t : ℝ, HasDerivAt φ (z * (Complex.exp ((t : ℂ) * z) - 1)) t := fun t => by
    have he : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * z)) (z * Complex.exp ((t : ℂ) * z)) t :=
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp).congr_deriv (by simp; ring)
    have hl : HasDerivAt (fun s : ℝ => (1 : ℂ) + (s : ℂ) * z) z t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).const_add 1
    exact ((he.sub hl).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp [φ]; ring)).congr_deriv (by ring)
  have hφ_cont : Continuous (fun t : ℝ => z * (Complex.exp ((t : ℂ) * z) - 1)) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ_deriv t)
    (hφ_cont.intervalIntegrable 0 1)
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hφ1 : φ 1 = Complex.exp z - 1 - z := by simp [φ]
  rw [hφ1, hφ0, sub_zero] at hftc
  have hexp_diff : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Complex.exp ((t : ℂ) * z) - 1‖ ≤ t * ‖z‖ * Real.exp (max z.re 0) := by
    intro t ht
    let ψ : ℝ → ℂ := fun u => Complex.exp ((u : ℂ) * z)
    have hψ_deriv : ∀ u : ℝ, HasDerivAt ψ (z * Complex.exp ((u : ℂ) * z)) u := fun u =>
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const z).cexp).congr_deriv (by simp; ring)
    have hψ_int := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hψ_deriv u)
      ((by fun_prop : Continuous fun u : ℝ => z * Complex.exp ((u : ℂ) * z)).intervalIntegrable 0 t)
    have hψ0 : ψ 0 = 1 := by simp [ψ]
    rw [hψ0] at hψ_int
    rw [← hψ_int]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := ‖z‖ * Real.exp (max z.re 0)) fun u hu => ?_).trans_eq (by
        rw [sub_zero, abs_of_nonneg ht.1]; ring)
    rw [uIoc_of_le ht.1] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u ≤ 1 := hu.2.trans ht.2
    rw [norm_mul, Complex.norm_exp]
    have hre : ((u : ℂ) * z).re ≤ max z.re 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rcases le_or_gt z.re 0 with hz | hz
      · exact (mul_nonpos_of_nonneg_of_nonpos hu0 hz).trans (le_max_right _ _)
      · exact (mul_le_of_le_one_left hz.le hu1).trans (le_max_left _ _)
    gcongr
  rw [← hftc]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  have hmono : ∫ t in (0 : ℝ)..1, ‖z * (Complex.exp ((t : ℂ) * z) - 1)‖ ≤
      ∫ t in (0 : ℝ)..1, (‖z‖ ^ 2 * Real.exp (max z.re 0)) * t := by
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hφ_cont.norm).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ => (‖z‖ ^ 2 * Real.exp (max z.re 0)) * t).intervalIntegrable 0 1) fun t ht => ?_
    rw [norm_mul]
    calc ‖z‖ * ‖Complex.exp ((t : ℂ) * z) - 1‖
        ≤ ‖z‖ * (t * ‖z‖ * Real.exp (max z.re 0)) :=
          mul_le_mul_of_nonneg_left (hexp_diff t ht) (norm_nonneg z)
      _ = (‖z‖ ^ 2 * Real.exp (max z.re 0)) * t := by ring
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

private lemma norm_intervalIntegral_le_abs_pow_loc {f : ℝ → ℂ} {C : ℝ} {n : ℕ} (_hC : 0 ≤ C)
    (hf : Continuous f) (u : ℝ) (hbd : ∀ v ∈ uIcc (0 : ℝ) u, ‖f v‖ ≤ C * |v| ^ n) :
    ‖∫ v in (0 : ℝ)..u, f v‖ ≤ C * |u| ^ (n + 1) / ((n : ℝ) + 1) := by
  have hg : Continuous (fun v : ℝ => C * |v| ^ n) := continuous_const.mul (continuous_abs.pow n)
  rcases le_or_gt 0 u with hu | hu
  · have h1 := intervalIntegral.norm_integral_le_integral_norm hu (f := f) (μ := volume)
    have h2 := intervalIntegral.integral_mono_on hu (hf.intervalIntegrable (μ := volume) 0 u).norm
      (hg.intervalIntegrable (μ := volume) 0 u) fun v hv => hbd v (uIcc_of_le hu ▸ hv)
    have h3 : ∫ v in (0 : ℝ)..u, C * |v| ^ n = C * u ^ (n + 1) / ((n : ℝ) + 1) := by
      have h_eq : ∫ v in (0 : ℝ)..u, C * |v| ^ n = ∫ v in (0 : ℝ)..u, C * v ^ n :=
        intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1]
      rw [h_eq, intervalIntegral.integral_const_mul, integral_pow]; ring
    rw [abs_of_nonneg hu]; linarith only [h1, h2, h3]
  · rw [intervalIntegral.integral_symm, norm_neg]
    have h1 := intervalIntegral.norm_integral_le_integral_norm hu.le (f := f) (μ := volume)
    have h2 := intervalIntegral.integral_mono_on hu.le (hf.intervalIntegrable (μ := volume) u 0).norm
      (hg.intervalIntegrable (μ := volume) u 0) fun v hv => hbd v ((uIcc_comm u 0 ▸ uIcc_of_le hu.le) ▸ hv)
    have h3 : ∫ v in u..0, C * |v| ^ n = C * (-u) ^ (n + 1) / ((n : ℝ) + 1) := by
      have h_eq : ∫ v in u..0, C * |v| ^ n = ∫ v in u..0, C * (-v) ^ n :=
        intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu.le] at hv; rw [abs_of_nonpos hv.2]
      rw [h_eq, intervalIntegral.integral_const_mul]
      have hc := intervalIntegral.integral_comp_neg (fun v : ℝ => v ^ n) (a := u) (b := 0)
      simp only [neg_zero] at hc; rw [hc, integral_pow]; ring
    rw [abs_of_neg hu]; linarith only [h1, h2, h3]

private lemma one_sub_imag_rpow_neg_half_taylor (t : ℝ) :
    ‖(1 - (t : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) - (1 + (Complex.I / 2) * (t : ℂ))‖ ≤ t ^ 2 := by
  let φ : ℝ → ℂ := fun u => (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let φ₁ : ℝ → ℂ := fun u => (Complex.I / 2) * (1 - (u : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ))
  let φ₂ : ℝ → ℂ := fun u => -(3 / 4 : ℂ) * (1 - (u : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))
  have hslit : ∀ u : ℝ, (1 - (u : ℂ) * Complex.I) ∈ Complex.slitPlane := fun u => by
    left; simp [Complex.sub_re, Complex.mul_re]
  have hne : ∀ u : ℝ, (1 - (u : ℂ) * Complex.I) ≠ 0 := fun u h => by
    have := congrArg Complex.re h; simp [Complex.sub_re, Complex.mul_re] at this
  have hd0 : ∀ u : ℝ, HasDerivAt φ (φ₁ u) u := fun u => by
    have hlin : HasDerivAt (fun v : ℝ => (1 : ℂ) - (v : ℂ) * Complex.I) (-Complex.I) u := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_sub (1 : ℂ)
      exact this.congr_deriv (by simp)
    have hcp : HasDerivAt (fun w : ℂ => w ^ (-(1 / 2 : ℂ)))
        ((-(1 / 2 : ℂ)) * (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ) - 1)) (1 - (u : ℂ) * Complex.I) :=
      simpa using ((hasDerivAt_id (1 - (u : ℂ) * Complex.I)).cpow_const (c := -(1 / 2 : ℂ)) (hslit u))
    refine (hcp.comp u hlin).congr_deriv ?_
    dsimp [φ₁]; rw [show (-(1 / 2 : ℂ) - 1 : ℂ) = -(3 / 2 : ℂ) by norm_num]; ring
  have hd1 : ∀ u : ℝ, HasDerivAt φ₁ (φ₂ u) u := fun u => by
    have hlin : HasDerivAt (fun v : ℝ => (1 : ℂ) - (v : ℂ) * Complex.I) (-Complex.I) u := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_sub (1 : ℂ)
      exact this.congr_deriv (by simp)
    have hcp : HasDerivAt (fun w : ℂ => w ^ (-(3 / 2 : ℂ)))
        ((-(3 / 2 : ℂ)) * (1 - (u : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ) - 1)) (1 - (u : ℂ) * Complex.I) :=
      simpa using ((hasDerivAt_id (1 - (u : ℂ) * Complex.I)).cpow_const (c := -(3 / 2 : ℂ)) (hslit u))
    refine ((hcp.comp u hlin).const_mul (Complex.I / 2)).congr_deriv ?_
    dsimp [φ₂]; rw [show (-(3 / 2 : ℂ) - 1 : ℂ) = -(5 / 2 : ℂ) by norm_num]
    calc (Complex.I / 2) * (-(3 / 2 : ℂ) * (1 - (u : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) * -Complex.I)
        = (Complex.I * Complex.I) * (3 / 4 : ℂ) * (1 - (u : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
      _ = -(3 / 4 : ℂ) * (1 - (u : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by rw [Complex.I_mul_I]; ring
  have hnorm_ge1 : ∀ u : ℝ, 1 ≤ ‖1 - (u : ℂ) * Complex.I‖ := fun u => by
    have := Complex.re_le_norm (1 - (u : ℂ) * Complex.I)
    simpa [Complex.sub_re, Complex.mul_re] using this
  have hφ2_bd : ∀ u : ℝ, ‖φ₂ u‖ ≤ 3 / 4 := fun u => by
    dsimp [φ₂]
    rw [norm_mul, norm_neg, show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num]
    have hcp : ‖(1 - (u : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))‖ ≤ 1 := by
      rw [show (-(5 / 2 : ℂ)) = ((-(5 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_of_ne_zero (hne u)]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hnorm_ge1 u) (by norm_num)
    nlinarith only [hcp]
  have hφ₂_cont : Continuous φ₂ := by
    refine continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun u => hslit u)
  have hφ₁_cont : Continuous φ₁ := continuous_iff_continuousAt.mpr fun u => (hd1 u).continuousAt
  have hbd1 : ∀ u : ℝ, ‖φ₁ u - (Complex.I / 2)‖ ≤ (3 / 4 : ℝ) * |u| := fun u => by
    have hφ10 : φ₁ 0 = Complex.I / 2 := by simp [φ₁]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd1 v)
      (hφ₂_cont.intervalIntegrable 0 u)
    rw [hφ10] at hftc
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (n := 0) (by norm_num) hφ₂_cont u
      fun v _ => (hφ2_bd v).trans_eq (by simp)).trans_eq (by norm_num)
  have hcont1 : Continuous (fun v : ℝ => φ₁ v - Complex.I / 2) := hφ₁_cont.sub continuous_const
  have hd_sub : ∀ v : ℝ, HasDerivAt (fun u : ℝ => φ u - (1 + (Complex.I / 2) * (u : ℂ)))
      (φ₁ v - Complex.I / 2) v := fun v =>
    ((hd0 v).fun_sub (((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (Complex.I / 2)).const_add 1)).congr_deriv
      (by simp)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd_sub v)
    (hcont1.intervalIntegrable 0 t)
  have h0 : φ 0 - (1 + (Complex.I / 2) * ((0 : ℝ) : ℂ)) = 0 := by simp [φ]
  rw [h0, sub_zero] at hftc
  rw [← hftc]
  refine (norm_intervalIntegral_le_abs_pow_loc (n := 1) (by norm_num) hcont1 t
    fun v _ => (hbd1 v).trans_eq (by simp)).trans ?_
  rw [sq_abs]; norm_num; nlinarith only [sq_nonneg t]

/-! ### Third derivative of `stripG` and third-order phase remainder -/

private lemma deriv2_stripG_differentiableAt {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    DifferentiableAt ℂ (deriv^[2] stripG) w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hev : deriv^[2] stripG =ᶠ[𝓝 w] fun z : ℂ =>
      -(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * z) / Complex.sin ((π : ℂ) * z) ^ 2 + 1 / z ^ 2 :=
    Filter.eventually_of_mem (hopen.mem_nhds ⟨h0, h1⟩) fun z hz => deriv2_stripG_eq hz.1 hz.2
  have hw_ne : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hsin_ne : Complex.sin ((π : ℂ) * w) ≠ 0 := sin_pi_ne_zero_halfStrip h0.le h1 hw_ne
  have hdiff : DifferentiableAt ℂ (fun z : ℂ =>
      -(π : ℂ) ^ 2 * Complex.cos ((π : ℂ) * z) / Complex.sin ((π : ℂ) * z) ^ 2 + 1 / z ^ 2) w :=
    (((differentiableAt_const _).mul (Complex.differentiable_cos.differentiableAt.comp w
        ((differentiableAt_const (π : ℂ)).mul differentiableAt_id))).div
      ((Complex.differentiable_sin.differentiableAt.comp w ((differentiableAt_const (π : ℂ)).mul differentiableAt_id)).pow 2)
      (pow_ne_zero 2 hsin_ne)).add
      ((differentiableAt_const _).div (differentiableAt_id.pow 2) (pow_ne_zero 2 hw_ne))
  exact hdiff.congr_of_eventuallyEq hev

private lemma deriv3_stripG_vert_norm_le {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht : |t| ≤ min σ (1 - σ) / 8) :
    ‖deriv^[3] stripG ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (1024 / 9 : ℝ) / ((1 - σ) ^ 2 * min σ (1 - σ)) := by
  have h1s_pos : 0 < 1 - σ := sub_pos.mpr hσ1
  let d : ℝ := min σ (1 - σ)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let r : ℝ := d / 4
  have hr_pos : 0 < r := by positivity
  have hsub : ∀ w ∈ Metric.closedBall z r, 0 < w.re ∧ w.re < 1 ∧
      (3 / 4 : ℝ) * (1 - σ) ≤ 1 - w.re ∧ |w.im| ≤ (1 - w.re) / 2 := by
    intro w hw
    have hdist : ‖w - z‖ ≤ r := by simpa only [Metric.mem_closedBall, Complex.dist_eq] using hw
    have hre_dist : |w.re - z.re| ≤ r := (Complex.abs_re_le_norm (w - z)).trans hdist
    have him_dist : |w.im - z.im| ≤ r := (Complex.abs_im_le_norm (w - z)).trans hdist
    have hz_re : z.re = σ := by simp [z]
    have hz_im : z.im = t := by simp [z]
    rw [hz_re] at hre_dist; rw [hz_im] at him_dist
    dsimp [r] at hre_dist him_dist
    have hre_lo : σ - d / 4 ≤ w.re := by linarith only [(abs_le.mp hre_dist).1]
    have hre_hi : w.re ≤ σ + d / 4 := by linarith only [(abs_le.mp hre_dist).2]
    have hd_σ : d ≤ σ := min_le_left _ _
    have hd_1s : d ≤ 1 - σ := min_le_right _ _
    have hw0 : 0 < w.re := by linarith only [hσ0, hd_σ, hre_lo]
    have hw1 : w.re < 1 := by linarith only [h1s_pos, hd_1s, hre_hi]
    have h1w : (3 / 4 : ℝ) * (1 - σ) ≤ 1 - w.re := by linarith only [hd_1s, hre_hi]
    have him_bd : |w.im| ≤ (3 / 8 : ℝ) * d := by
      have htri := abs_add_le (w.im - t) t
      rw [sub_add_cancel] at htri
      linarith only [htri, him_dist, ht]
    have him_half : |w.im| ≤ (1 - w.re) / 2 := by
      rcases le_or_gt σ (1 / 2) with hhalf | hhalf
      · have hd_eq : d = σ := min_eq_left (by linarith only [hhalf])
        have h1 : (3 / 8 : ℝ) * d ≤ (1 - w.re) / 2 := by
          nlinarith only [hre_hi, hhalf, hd_eq]
        exact him_bd.trans h1
      · have hd_eq : d = 1 - σ := min_eq_right (by linarith only [hhalf])
        have h1 : (3 / 8 : ℝ) * d ≤ (1 - w.re) / 2 := by
          linarith only [h1w, hd_eq]
        exact him_bd.trans h1
    exact ⟨hw0, hw1, h1w, him_half⟩
  have hdiff_on : DifferentiableOn ℂ (deriv^[2] stripG) (Metric.ball z r) := fun w hw =>
    let hs := hsub w (Metric.ball_subset_closedBall hw)
    (deriv2_stripG_differentiableAt hs.1 hs.2.1).differentiableWithinAt
  have hcont_on : ContinuousOn (deriv^[2] stripG) (Metric.closedBall z r) := fun w hw =>
    let hs := hsub w hw
    (deriv2_stripG_differentiableAt hs.1 hs.2.1).continuousAt.continuousWithinAt
  have hsphere : ∀ w ∈ Metric.sphere z r,
      ‖deriv^[2] stripG w‖ ≤ (256 / 9 : ℝ) / (1 - σ) ^ 2 := fun w hw => by
    have hs := hsub w (Metric.sphere_subset_closedBall hw)
    have h1w_pos : 0 < 1 - w.re := sub_pos.mpr hs.2.1
    have hw_eq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h2 := deriv2_stripG_norm_le hs.1 hs.2.1 hs.2.2.2
    rw [← hw_eq] at h2
    refine h2.trans ?_
    have hsq : (9 / 16 : ℝ) * (1 - σ) ^ 2 ≤ (1 - w.re) ^ 2 := by
      have h34_pos : 0 ≤ (3 / 4 : ℝ) * (1 - σ) := by positivity
      calc (9 / 16 : ℝ) * (1 - σ) ^ 2 = ((3 / 4 : ℝ) * (1 - σ)) ^ 2 := by ring
        _ ≤ (1 - w.re) ^ 2 := pow_le_pow_left₀ h34_pos hs.2.2.1 2
    calc 16 / (1 - w.re) ^ 2 ≤ 16 / ((9 / 16 : ℝ) * (1 - σ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      _ = (256 / 9 : ℝ) / (1 - σ) ^ 2 := by field_simp [(by positivity : (1 - σ) ^ 2 ≠ 0)]; norm_num; ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 1) hr_pos
    ⟨hdiff_on, by simpa only [closure_ball z hr_pos.ne'] using hcont_on⟩ hsphere
  have h3_eq : deriv^[3] stripG z = iteratedDeriv 1 (deriv^[2] stripG) z := by
    rw [iteratedDeriv_one, Function.iterate_succ_apply']
  rw [h3_eq]
  refine hcauchy.trans_eq ?_
  rw [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
  dsimp [r]; ring

private lemma hasDerivAt_mellinPhi_vert_loc {σ ξ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => mellinPhi ((σ : ℂ) + (u : ℂ) * Complex.I) ξ - mellinPhi (σ : ℂ) ξ)
      (Complex.I * (stripG ((σ : ℂ) + (τ : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))) τ := by
  have hlin : HasDerivAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * Complex.I) Complex.I τ :=
    (((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_add (σ : ℂ)).congr_deriv (by simp)
  have hre : |((σ : ℂ) + (τ : ℂ) * Complex.I).re| < 1 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, abs_of_pos hσ0]
    exact hσ1
  have hs := (hasDerivAt_stripS0Tilde hre).comp τ hlin
  have hl := hlin.mul_const (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))
  exact (((hs.fun_add hl).sub_const (mellinPhi (σ : ℂ) ξ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => rfl)).congr_deriv (by ring)

private lemma c_r_ph_second_order {c ξ σ_star τ : ℝ}
    (hc_pos : 0 < c) (hξ_pos : 0 < ξ) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (hτ : |τ| ≤ min σ_star (1 - σ_star) / 8) :
    let g' := stripGDerivReal σ_star
    let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
    let ε_L := saddleEpsL c σ_star
    let s := τ / τ_sd
    let α₃ := -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)
    ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) -
        (-((s ^ 2 / 2 : ℝ) : ℂ) + α₃ * ((s ^ 3 : ℝ) : ℂ))‖ ≤ 13 * ε_L ^ 2 * s ^ 4 ∧
    ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) +
        ((s ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 17 * ε_L * |s| ^ 3 := by
  dsimp only
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let d : ℝ := min σ_star (1 - σ_star)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  let g' : ℝ := stripGDerivReal σ_star
  let τ_sd : ℝ := (c * g') ^ (-(1 / 2 : ℝ))
  let ε_L : ℝ := saddleEpsL c σ_star
  let s : ℝ := τ / τ_sd
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
    dsimp [τ_sd]
    rw [Real.rpow_neg (by positivity), inv_pow, ← Real.rpow_natCast ((c * g') ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hεL_def : ε_L = τ_sd / d := rfl
  let φ : ℝ → ℂ := fun u => mellinPhi ((σ_star : ℂ) + (u : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ
  let φ₁ : ℝ → ℂ := fun u => Complex.I * (stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I) + Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))
  let φ₂ : ℝ → ℂ := fun u => -deriv stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I)
  let φ₃ : ℝ → ℂ := fun u => -Complex.I * deriv^[2] stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I)
  let φ₄ : ℝ → ℂ := fun u => deriv^[3] stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I)
  have hre : ∀ u : ℝ, 0 < ((σ_star : ℂ) + (u : ℂ) * Complex.I).re ∧
      ((σ_star : ℂ) + (u : ℂ) * Complex.I).re < 1 := fun _ => by simpa using ⟨hσ0, hσ1⟩
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hd0 : ∀ u, HasDerivAt φ (φ₁ u) u := fun u => hasDerivAt_mellinPhi_vert_loc hσ0 hσ1 u
  have hd1 : ∀ u, HasDerivAt φ₁ (φ₂ u) u := fun u => by
    have hdg := hasDerivAt_stripG (hre u).1 (hre u).2
    have hlin : HasDerivAt (fun v : ℝ => (σ_star : ℂ) + (v : ℂ) * Complex.I) Complex.I u :=
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (σ_star : ℂ)).congr_deriv (by simp)
    have hcomp := ((hdg.comp u hlin).add_const (Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))).const_mul Complex.I
    refine hcomp.congr_deriv ?_
    dsimp [φ₂]
    rw [show deriv stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I) =
        (π : ℂ) / Complex.sin ((π : ℂ) * ((σ_star : ℂ) + (u : ℂ) * Complex.I)) -
          1 / ((σ_star : ℂ) + (u : ℂ) * Complex.I) from hdg.deriv,
      show Complex.I * (((π : ℂ) / Complex.sin ((π : ℂ) * ((σ_star : ℂ) + (u : ℂ) * Complex.I)) -
        1 / ((σ_star : ℂ) + (u : ℂ) * Complex.I)) * Complex.I) =
        (Complex.I * Complex.I) * ((π : ℂ) / Complex.sin ((π : ℂ) * ((σ_star : ℂ) + (u : ℂ) * Complex.I)) -
        1 / ((σ_star : ℂ) + (u : ℂ) * Complex.I)) by ring,
      Complex.I_mul_I]
    ring
  have hd2 : ∀ u, HasDerivAt φ₂ (φ₃ u) u := fun u => by
    let z : ℂ := (σ_star : ℂ) + (u : ℂ) * Complex.I
    have hev : deriv stripG =ᶠ[𝓝 z] fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w :=
      Filter.eventually_of_mem (hopen.mem_nhds (hre u)) fun w hw => (hasDerivAt_stripG hw.1 hw.2).deriv
    have hdz_ne : z ≠ 0 := fun h => by have := congrArg Complex.re h; simp [z] at this; linarith only [this, hσ0]
    have hd_diff : DifferentiableAt ℂ (fun w : ℂ => (π : ℂ) / Complex.sin ((π : ℂ) * w) - 1 / w) z :=
      (differentiableAt_const _ |>.div (Complex.differentiable_sin.differentiableAt.comp z ((differentiableAt_const (π : ℂ)).mul differentiableAt_id))
        (sin_pi_ne_zero_halfStrip (hre u).1.le (hre u).2 hdz_ne)).sub (differentiableAt_const _ |>.div differentiableAt_id hdz_ne)
    have hd_s2 : HasDerivAt (deriv stripG) (deriv^[2] stripG z) z := by
      change HasDerivAt (deriv stripG) (deriv (deriv stripG) z) z
      have hd' := hd_diff.hasDerivAt.congr_of_eventuallyEq hev
      rw [hev.deriv_eq]; exact hd'
    have hlin : HasDerivAt (fun v : ℝ => (σ_star : ℂ) + (v : ℂ) * Complex.I) Complex.I u :=
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (σ_star : ℂ)).congr_deriv (by simp)
    have hneg := (hd_s2.comp u hlin).neg
    change HasDerivAt (fun v : ℝ => -deriv stripG ((σ_star : ℂ) + (v : ℂ) * Complex.I))
      (-Complex.I * deriv^[2] stripG ((σ_star : ℂ) + (u : ℂ) * Complex.I)) u
    exact hneg.congr_deriv (by ring)
  have hd3 : ∀ u, HasDerivAt φ₃ (φ₄ u) u := fun u => by
    let z : ℂ := (σ_star : ℂ) + (u : ℂ) * Complex.I
    have hd_s3 := (deriv2_stripG_differentiableAt (hre u).1 (hre u).2).hasDerivAt
    have hlin : HasDerivAt (fun v : ℝ => (σ_star : ℂ) + (v : ℂ) * Complex.I) Complex.I u :=
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (σ_star : ℂ)).congr_deriv (by simp)
    have hcomp := (hd_s3.comp u hlin).const_mul (-Complex.I)
    refine hcomp.congr_deriv ?_
    dsimp [φ₄]
    rw [congrFun (Function.iterate_succ_apply' deriv 2 stripG) z]
    calc -Complex.I * (deriv (deriv^[2] stripG) z * Complex.I)
        = -(Complex.I * Complex.I) * deriv (deriv^[2] stripG) z := by ring
      _ = deriv (deriv^[2] stripG) z := by rw [Complex.I_mul_I]; ring
  have hφ₄_cont : Continuous φ₄ := continuous_iff_continuousAt.mpr fun u => by
    have hd_on : DifferentiableOn ℂ (deriv^[2] stripG) {w : ℂ | 0 < w.re ∧ w.re < 1} := fun w hw =>
      (deriv2_stripG_differentiableAt hw.1 hw.2).differentiableWithinAt
    have hcont3 := (hd_on.analyticOnNhd hopen).deriv.continuousOn
    have hcont_fun : Continuous (fun v : ℝ => deriv (deriv^[2] stripG) ((σ_star : ℂ) + (v : ℂ) * Complex.I)) :=
      hcont3.comp_continuous (by fun_prop) fun v => hre v
    have hfun_eq : (fun v : ℝ => deriv (deriv^[2] stripG) ((σ_star : ℂ) + (v : ℂ) * Complex.I)) = φ₄ := by
      ext v; exact (congrFun (Function.iterate_succ_apply' deriv 2 stripG) _).symm
    rw [← hfun_eq]; exact hcont_fun.continuousAt
  have hφ₃_cont : Continuous φ₃ := continuous_iff_continuousAt.mpr fun u => (hd3 u).continuousAt
  have hφ₂_cont : Continuous φ₂ := continuous_iff_continuousAt.mpr fun u => (hd2 u).continuousAt
  have hφ₁_cont : Continuous φ₁ := continuous_iff_continuousAt.mpr fun u => (hd1 u).continuousAt
  have h_uIcc_abs : ∀ u v : ℝ, v ∈ uIcc (0 : ℝ) u → |v| ≤ |u| := fun u v hv => by
    rcases le_or_gt 0 u with hu | hu
    · rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1, abs_of_nonneg hu]; exact hv.2
    · rw [uIcc_of_ge hu.le] at hv; rw [abs_of_nonpos hv.2, abs_of_neg hu]; linarith only [hv.1]
  set B₃ : ℝ := (1024 / 9 : ℝ) / ((1 - σ_star) ^ 2 * d)
  have hB₃ : 0 ≤ B₃ := by positivity
  have hbd3 : ∀ u : ℝ, |u| ≤ d / 8 → ‖φ₃ u - φ₃ 0‖ ≤ B₃ * |u| := fun u hu => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd3 v)
      (hφ₄_cont.intervalIntegrable 0 u)
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (n := 0) hB₃ hφ₄_cont u fun v hv => by
      simpa only [pow_zero, mul_one] using deriv3_stripG_vert_norm_le hσ0 hσ1 ((h_uIcc_abs u v hv).trans hu)).trans_eq
      (by ring)
  have hcont3 : Continuous (fun v : ℝ => φ₃ v - φ₃ 0) := hφ₃_cont.sub continuous_const
  have hbd2 : ∀ u : ℝ, |u| ≤ d / 8 → ‖φ₂ u - φ₂ 0 - φ₃ 0 * (u : ℂ)‖ ≤ (B₃ / 2) * |u| ^ 2 := fun u hu => by
    have hd_sub : ∀ v : ℝ, HasDerivAt (fun x : ℝ => φ₂ x - φ₂ 0 - φ₃ 0 * (x : ℂ)) (φ₃ v - φ₃ 0) v := fun v =>
      (((hd2 v).sub_const _).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (φ₃ 0))).congr_deriv
        (by simp)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd_sub v)
      (hcont3.intervalIntegrable 0 u)
    simp only [Complex.ofReal_zero, mul_zero, sub_self, sub_zero] at hftc
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (n := 1) hB₃ hcont3 u fun v hv => by
      simpa only [pow_one] using hbd3 v ((h_uIcc_abs u v hv).trans hu)).trans_eq (by norm_num; ring)
  have hcont2 : Continuous (fun v : ℝ => φ₂ v - φ₂ 0 - φ₃ 0 * (v : ℂ)) :=
    (hφ₂_cont.sub continuous_const).sub (continuous_const.mul Complex.continuous_ofReal)
  have hφ1_0 : φ₁ 0 = 0 := by
    dsimp [φ₁]; simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [stripG_ofReal hσ0 hσ1, hσ_eq, show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity : 0 ≤ π ^ 2 * ξ)]; push_cast; ring
  have hbd1 : ∀ u : ℝ, |u| ≤ d / 8 →
      ‖φ₁ u - φ₂ 0 * (u : ℂ) - φ₃ 0 / 2 * (u : ℂ) ^ 2‖ ≤ (B₃ / 6) * |u| ^ 3 := fun u hu => by
    have hd_sub : ∀ v : ℝ, HasDerivAt (fun x : ℝ => φ₁ x - φ₂ 0 * (x : ℂ) - φ₃ 0 / 2 * (x : ℂ) ^ 2)
        (φ₂ v - φ₂ 0 - φ₃ 0 * (v : ℂ)) v := fun v =>
      (((hd1 v).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (φ₂ 0))).fun_sub
        (((Complex.ofRealCLM.hasDerivAt (x := v)).pow 2).const_mul (φ₃ 0 / 2))).congr_deriv (by simp; ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd_sub v)
      (hcont2.intervalIntegrable 0 u)
    simp only [Complex.ofReal_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, hφ1_0] at hftc
    rw [← hftc]
    refine (norm_intervalIntegral_le_abs_pow_loc (n := 2) (by positivity) hcont2 u fun v hv =>
      hbd2 v ((h_uIcc_abs u v hv).trans hu)).trans_eq ?_
    norm_num; ring
  have hcont1 : Continuous (fun v : ℝ => φ₁ v - φ₂ 0 * (v : ℂ) - φ₃ 0 / 2 * (v : ℂ) ^ 2) :=
    ((hφ₁_cont.sub (continuous_const.mul Complex.continuous_ofReal)).sub
      (continuous_const.mul (Complex.continuous_ofReal.pow 2)))
  have hbd0 : ‖φ τ - φ₂ 0 / 2 * (τ : ℂ) ^ 2 - φ₃ 0 / 6 * (τ : ℂ) ^ 3‖ ≤ (B₃ / 24) * |τ| ^ 4 := by
    have hφ0 : φ 0 = 0 := by dsimp [φ]; simp
    have hd_sub : ∀ v : ℝ, HasDerivAt (fun x : ℝ => φ x - φ₂ 0 / 2 * (x : ℂ) ^ 2 - φ₃ 0 / 6 * (x : ℂ) ^ 3)
        (φ₁ v - φ₂ 0 * (v : ℂ) - φ₃ 0 / 2 * (v : ℂ) ^ 2) v := fun v =>
      (((hd0 v).fun_sub (((Complex.ofRealCLM.hasDerivAt (x := v)).pow 2).const_mul (φ₂ 0 / 2))).fun_sub
        (((Complex.ofRealCLM.hasDerivAt (x := v)).pow 3).const_mul (φ₃ 0 / 6))).congr_deriv (by simp; ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd_sub v)
      (hcont1.intervalIntegrable 0 τ)
    simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, sub_zero, hφ0] at hftc
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (n := 3) (by positivity) hcont1 τ fun v hv =>
      hbd1 v ((h_uIcc_abs τ v hv).trans hτ)).trans_eq (by norm_num; ring)
  have hφ₂_0 : φ₂ 0 = -((g' : ℝ) : ℂ) := by
    dsimp [φ₂]
    have hdg := hasDerivAt_stripG (by simpa using hσ0 : 0 < (σ_star : ℂ).re) (by simpa using hσ1)
    simp only [Complex.ofReal_zero, zero_mul, add_zero, hdg.deriv]
    dsimp [g', stripGDerivReal]; push_cast; ring
  have hcτ_eq : (c : ℂ) * (φ₂ 0 / 2 * (τ : ℂ) ^ 2) = -((s ^ 2 / 2 : ℝ) : ℂ) := by
    rw [hφ₂_0]
    have hmul_id : c * g' * τ ^ 2 = s ^ 2 := by
      dsimp [s]; rw [div_pow, hτsd_sq]; field_simp [(mul_pos hc_pos hg'_pos).ne']
    calc (c : ℂ) * (-((g' : ℂ)) / 2 * (τ : ℂ) ^ 2)
        = -(((c * g' * τ ^ 2 / 2 : ℝ) : ℂ)) := by push_cast; ring
      _ = -((s ^ 2 / 2 : ℝ) : ℂ) := by rw [hmul_id]
  have hcφ₃_eq : (c : ℂ) * (φ₃ 0 / 6 * (τ : ℂ) ^ 3) =
      -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6) *
        ((s ^ 3 : ℝ) : ℂ) := by
    dsimp [φ₃, s]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    push_cast
    field_simp [hτsd_pos.ne']
  have hbound_coeff : c * (B₃ / 24) * τ_sd ^ 4 ≤ 13 * ε_L ^ 2 := by
    have hcτ4 : c * B₃ * τ_sd ^ 4 = ((1024 / 9 : ℝ) * (d / (g' * (1 - σ_star) ^ 2))) * ε_L ^ 2 := by
      have hid1 : c * τ_sd ^ 2 = g'⁻¹ := by rw [hτsd_sq]; field_simp [hc_pos.ne', hg'_pos.ne']
      have hid2 : τ_sd ^ 2 = d ^ 2 * ε_L ^ 2 := by dsimp [ε_L, saddleEpsL]; rw [div_pow]; field_simp [hd_pos.ne']
      dsimp [B₃]
      calc c * ((1024 / 9 : ℝ) / ((1 - σ_star) ^ 2 * d)) * τ_sd ^ 4
          = (1024 / 9 : ℝ) * (c * τ_sd ^ 2) * τ_sd ^ 2 / ((1 - σ_star) ^ 2 * d) := by ring
        _ = (1024 / 9 : ℝ) * g'⁻¹ * (d ^ 2 * ε_L ^ 2) / ((1 - σ_star) ^ 2 * d) := by rw [hid1, hid2]
        _ = ((1024 / 9 : ℝ) * (d / (g' * (1 - σ_star) ^ 2))) * ε_L ^ 2 := by
            field_simp [hg'_pos.ne', h1s_pos.ne', hd_pos.ne']
    have hd_ratio : d / (g' * (1 - σ_star) ^ 2) ≤ 8 / 3 := by
      have hg'_lo : (3 / 4 : ℝ) * σ_star / (1 - σ_star) < g' := (stripG_deriv_bounds hσ0 hσ1).1
      have hden : (3 / 4 : ℝ) * σ_star * (1 - σ_star) < g' * (1 - σ_star) ^ 2 := by
        have := mul_lt_mul_of_pos_right hg'_lo (pow_pos h1s_pos 2)
        refine this.trans_eq' ?_
        field_simp [h1s_pos.ne']
      have h1 : d / (g' * (1 - σ_star) ^ 2) < (4 / 3 : ℝ) * (d / (σ_star * (1 - σ_star))) := by
        refine (div_lt_div_of_pos_left hd_pos (by positivity) hden).trans_eq ?_
        field_simp [hσ0.ne', h1s_pos.ne']; ring
      have h2 : d / (σ_star * (1 - σ_star)) ≤ 2 := by
        rcases le_or_gt σ_star (1 / 2) with hh | hh
        · rw [show d = σ_star from min_eq_left (by linarith only [hh]),
            show σ_star / (σ_star * (1 - σ_star)) = (1 - σ_star)⁻¹ by field_simp [hσ0.ne']]
          exact inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
        · rw [show d = 1 - σ_star from min_eq_right (by linarith only [hh]),
            show (1 - σ_star) / (σ_star * (1 - σ_star)) = σ_star⁻¹ by field_simp [h1s_pos.ne']]
          exact inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
      linarith only [h1, h2]
    rw [show c * (B₃ / 24) * τ_sd ^ 4 = (c * B₃ * τ_sd ^ 4) / 24 by ring, hcτ4]
    calc ((1024 / 9 : ℝ) * (d / (g' * (1 - σ_star) ^ 2)) * ε_L ^ 2) / 24
        ≤ ((1024 / 9 : ℝ) * (8 / 3 : ℝ) * ε_L ^ 2) / 24 := by gcongr
      _ = (1024 / 81 : ℝ) * ε_L ^ 2 := by ring
      _ ≤ 13 * ε_L ^ 2 := by gcongr; norm_num
  have h1st : ‖(c : ℂ) * φ τ - (-((s ^ 2 / 2 : ℝ) : ℂ) +
      -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6) *
        ((s ^ 3 : ℝ) : ℂ))‖ ≤ 13 * ε_L ^ 2 * s ^ 4 := by
    rw [← hcτ_eq, ← hcφ₃_eq,
      show (c : ℂ) * φ τ - ((c : ℂ) * (φ₂ 0 / 2 * (τ : ℂ) ^ 2) + (c : ℂ) * (φ₃ 0 / 6 * (τ : ℂ) ^ 3)) =
        (c : ℂ) * (φ τ - φ₂ 0 / 2 * (τ : ℂ) ^ 2 - φ₃ 0 / 6 * (τ : ℂ) ^ 3) by ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
    have hmul := mul_le_mul_of_nonneg_left hbd0 hc_pos.le
    refine hmul.trans ?_
    have hτ4 : |τ| ^ 4 = τ_sd ^ 4 * s ^ 4 := by
      dsimp [s]; rw [show |τ| ^ 4 = τ ^ 4 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs], div_pow]
      field_simp [hτsd_pos.ne']
    rw [hτ4]
    calc c * (B₃ / 24 * (τ_sd ^ 4 * s ^ 4))
        = (c * (B₃ / 24) * τ_sd ^ 4) * s ^ 4 := by ring
      _ ≤ 13 * ε_L ^ 2 * s ^ 4 := by gcongr
  have hα₃_bd : ‖-(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)‖ ≤
      (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 := by
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc_pos.le,
      Real.norm_of_nonneg (pow_nonneg hτsd_pos.le 3), show ‖(6 : ℂ)‖ = 6 by norm_num]
    have hd2 := deriv2_stripG_norm_le hσ0 hσ1 (by simp [abs_zero]; positivity : |(0 : ℝ)| ≤ (1 - σ_star) / 2)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hd2
    calc c * ‖deriv^[2] stripG (σ_star : ℂ)‖ * τ_sd ^ 3 / 6
        ≤ c * (16 / (1 - σ_star) ^ 2) * τ_sd ^ 3 / 6 := by gcongr
      _ = (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 := by ring
  have hc17 : (8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2 ≤ 17 * ε_L := by
    have hg'_lo : (3 / 4 : ℝ) * σ_star / (1 - σ_star) < g' := (stripG_deriv_bounds hσ0 hσ1).1
    have hrat_sq : (((8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2) / ε_L) ^ 2 =
        (64 / 9 : ℝ) * d ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4) := by
      dsimp [ε_L, saddleEpsL]
      rw [div_pow, div_pow, mul_pow, mul_pow, div_pow, show (τ_sd ^ 3) ^ 2 = (τ_sd ^ 2) ^ 3 by ring, hτsd_sq]
      field_simp [hc_pos.ne', hg'_pos.ne', hd_pos.ne', h1s_pos.ne']
    have hm_sq : d ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) ≤ 4 := by
      rcases le_or_gt σ_star (1 / 2) with hh | hh
      · rw [show d = σ_star from min_eq_left (by linarith only [hh])]
        have : σ_star ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) = (1 - σ_star)⁻¹ ^ 2 := by field_simp [hσ0.ne']
        rw [this]
        have hinv : (1 - σ_star)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
        have hnn : 0 ≤ (1 - σ_star)⁻¹ := by positivity
        nlinarith only [hinv, hnn]
      · rw [show d = 1 - σ_star from min_eq_right (by linarith only [hh])]
        have : (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) = σ_star⁻¹ ^ 2 := by field_simp [h1s_pos.ne']
        rw [this]
        have hinv : σ_star⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
        have hnn : 0 ≤ σ_star⁻¹ := by positivity
        nlinarith only [hinv, hnn]
    have hg'2 : (9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2) < g' ^ 2 * (1 - σ_star) ^ 4 := by
      have h1 : (3 / 4 : ℝ) * σ_star * (1 - σ_star) < g' * (1 - σ_star) ^ 2 := by
        have := mul_lt_mul_of_pos_right hg'_lo (pow_pos h1s_pos 2)
        refine this.trans_eq' ?_; field_simp [h1s_pos.ne']
      nlinarith only [h1, hσ0, h1s_pos, hg'_pos]
    have hsq17 : (((8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2) / ε_L) ^ 2 < 17 ^ 2 := by
      rw [hrat_sq]
      calc (64 / 9 : ℝ) * d ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4)
          < (64 / 9 : ℝ) * d ^ 2 / ((9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2)) :=
            div_lt_div_of_pos_left (by positivity) (by positivity) hg'2
        _ = (1024 / 81 : ℝ) * (d ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2)) := by
            field_simp [hσ0.ne', h1s_pos.ne']; norm_num
        _ ≤ (1024 / 81 : ℝ) * 4 := by gcongr
        _ < 17 ^ 2 := by norm_num
    have hlt := lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq17
    exact (div_lt_iff₀ hεL_pos).mp hlt |>.le
  refine ⟨h1st, ?_⟩
  have hes_le : ε_L * |s| ≤ 1 / 8 := by
    have : |τ| / d = ε_L * |s| := by
      dsimp [ε_L, saddleEpsL, s]; rw [abs_div, abs_of_pos hτsd_pos]; field_simp [hd_pos.ne', hτsd_pos.ne']
    have hd8 : (d / 8) / d = 1 / 8 := by field_simp [hd_pos.ne']
    linarith only [this, div_le_div_of_nonneg_right hτ hd_pos.le, hd8]
  let α₃ := -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)
  have htri : ‖(c : ℂ) * φ τ + ((s ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      ‖(c : ℂ) * φ τ - (-((s ^ 2 / 2 : ℝ) : ℂ) + α₃ * ((s ^ 3 : ℝ) : ℂ))‖ + ‖α₃‖ * |s| ^ 3 := by
    have hid : (c : ℂ) * φ τ + ((s ^ 2 / 2 : ℝ) : ℂ) =
        ((c : ℂ) * φ τ - (-((s ^ 2 / 2 : ℝ) : ℂ) + α₃ * ((s ^ 3 : ℝ) : ℂ))) + α₃ * ((s ^ 3 : ℝ) : ℂ) := by
      ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have hα₃_le_15 : ‖α₃‖ ≤ 15 * ε_L := by
    have h8 : (1024 / 81 : ℝ) * 4 < 15 ^ 2 := by norm_num
    have hsq15 : (((8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2) / ε_L) ^ 2 < 15 ^ 2 := by
      have hg'_lo : (3 / 4 : ℝ) * σ_star / (1 - σ_star) < g' := (stripG_deriv_bounds hσ0 hσ1).1
      have hrat_sq : (((8 / 3 : ℝ) * c * τ_sd ^ 3 / (1 - σ_star) ^ 2) / ε_L) ^ 2 =
          (64 / 9 : ℝ) * d ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4) := by
        dsimp [ε_L, saddleEpsL]
        rw [div_pow, div_pow, mul_pow, mul_pow, div_pow, show (τ_sd ^ 3) ^ 2 = (τ_sd ^ 2) ^ 3 by ring, hτsd_sq]
        field_simp [hc_pos.ne', hg'_pos.ne', hd_pos.ne', h1s_pos.ne']
      have hm_sq : d ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) ≤ 4 := by
        rcases le_or_gt σ_star (1 / 2) with hh | hh
        · rw [show d = σ_star from min_eq_left (by linarith only [hh])]
          rw [show σ_star ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) = (1 - σ_star)⁻¹ ^ 2 by field_simp [hσ0.ne']]
          have hinv : (1 - σ_star)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
          have hnn : 0 ≤ (1 - σ_star)⁻¹ := by positivity
          nlinarith only [hinv, hnn]
        · rw [show d = 1 - σ_star from min_eq_right (by linarith only [hh])]
          rw [show (1 - σ_star) ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2) = σ_star⁻¹ ^ 2 by field_simp [h1s_pos.ne']]
          have hinv : σ_star⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith only [hh])
          have hnn : 0 ≤ σ_star⁻¹ := by positivity
          nlinarith only [hinv, hnn]
      have hg'2 : (9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2) < g' ^ 2 * (1 - σ_star) ^ 4 := by
        have h1 : (3 / 4 : ℝ) * σ_star * (1 - σ_star) < g' * (1 - σ_star) ^ 2 := by
          have := mul_lt_mul_of_pos_right hg'_lo (pow_pos h1s_pos 2)
          refine this.trans_eq' ?_; field_simp [h1s_pos.ne']
        nlinarith only [h1, hσ0, h1s_pos, hg'_pos]
      rw [hrat_sq]
      calc (64 / 9 : ℝ) * d ^ 2 / (g' ^ 2 * (1 - σ_star) ^ 4)
          < (64 / 9 : ℝ) * d ^ 2 / ((9 / 16 : ℝ) * (σ_star ^ 2 * (1 - σ_star) ^ 2)) :=
            div_lt_div_of_pos_left (by positivity) (by positivity) hg'2
        _ = (1024 / 81 : ℝ) * (d ^ 2 / (σ_star ^ 2 * (1 - σ_star) ^ 2)) := by
            field_simp [hσ0.ne', h1s_pos.ne']; norm_num
        _ ≤ (1024 / 81 : ℝ) * 4 := by gcongr
        _ < 15 ^ 2 := h8
    exact hα₃_bd.trans ((div_lt_iff₀ hεL_pos).mp (lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq15)).le
  calc ‖(c : ℂ) * φ τ + ((s ^ 2 / 2 : ℝ) : ℂ)‖
      ≤ 13 * ε_L ^ 2 * s ^ 4 + 15 * ε_L * |s| ^ 3 := by
        refine htri.trans (add_le_add h1st (mul_le_mul_of_nonneg_right hα₃_le_15 (by positivity)))
    _ = 13 * ε_L * (ε_L * |s|) * |s| ^ 3 + 15 * ε_L * |s| ^ 3 := by
        have hs4 : s ^ 4 = |s| * |s| ^ 3 := by
          calc s ^ 4 = |s| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
            _ = |s| * |s| ^ 3 := by ring
        rw [hs4]; ring
    _ ≤ 13 * ε_L * (1 / 8) * |s| ^ 3 + 15 * ε_L * |s| ^ 3 := by gcongr
    _ ≤ 17 * ε_L * |s| ^ 3 := by nlinarith only [hεL_pos, pow_nonneg (abs_nonneg s) 3]

/-! ### Holomorphic multiplier `V` second-order Taylor bound and `B_c` `O(ε_L^3)` bound -/

/-- Second-order vertical-line hypotheses extending `TotalSaddleAmp c σ_star` (`cel:total-saddle-2`). -/
structure TotalSaddleSecondOrderAmp (c σ_star : ℝ) extends TotalSaddleAmp c σ_star where
  D : ℝ
  hD : 1 ≤ D
  hV_holo : DifferentiableOn ℂ V (Metric.ball (σ_star : ℂ) (3 / 4 * min σ_star (1 - σ_star)))
  hV_disk : ∀ ζ ∈ Metric.closedBall (σ_star : ℂ) (min σ_star (1 - σ_star) / 2), ‖V ζ‖ ≤ D * A

private lemma V_second_order_taylor {c σ_star τ : ℝ} (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (amp : TotalSaddleSecondOrderAmp c σ_star) (hτ : |τ| ≤ min σ_star (1 - σ_star) / 8) :
    let d := min σ_star (1 - σ_star)
    let V₁ := Complex.I * deriv amp.V (σ_star : ℂ) / (amp.A : ℂ)
    ‖amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (amp.A : ℂ) -
        (amp.V (σ_star : ℂ) / (amp.A : ℂ) + V₁ * (τ : ℂ))‖ ≤ 16 * amp.D * (τ / d) ^ 2 ∧
    ‖V₁‖ ≤ 2 * amp.D / d := by
  dsimp only
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let d : ℝ := min σ_star (1 - σ_star)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  have hA_pos : 0 < amp.A := amp.hA
  have hD_pos : 0 < amp.D := by linarith only [amp.hD]
  have hr2_pos : 0 < d / 2 := by positivity
  have hr4_pos : 0 < d / 4 := by positivity
  have hsub2 : Metric.closedBall (σ_star : ℂ) (d / 2) ⊆ Metric.ball (σ_star : ℂ) (3 / 4 * d) :=
    Metric.closedBall_subset_ball (by linarith only [hd_pos])
  have hV1_bd : ‖deriv amp.V (σ_star : ℂ)‖ ≤ 2 * amp.D * amp.A / d := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 1) hr2_pos
      ⟨amp.hV_holo.mono (Metric.ball_subset_closedBall.trans hsub2),
        by simpa only [closure_ball _ hr2_pos.ne'] using (amp.hV_holo.continuousOn.mono hsub2)⟩
      fun ω hω => amp.hV_disk ω (Metric.sphere_subset_closedBall hω)
    rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at hc
    refine hc.trans_eq (by ring)
  have hV2_bd : ∀ u : ℝ, |u| ≤ d / 8 →
      ‖iteratedDeriv 2 amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I)‖ ≤ 32 * amp.D * amp.A / d ^ 2 := by
    intro u hu
    let z : ℂ := (σ_star : ℂ) + (u : ℂ) * Complex.I
    have hsub_u : Metric.closedBall z (d / 4) ⊆ Metric.closedBall (σ_star : ℂ) (d / 2) := by
      intro ω hω
      rw [Metric.mem_closedBall] at hω ⊢
      have hdist_z : dist z (σ_star : ℂ) ≤ d / 8 := by
        rw [Complex.dist_eq]
        simpa only [z, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one] using hu
      dsimp [r] at hω
      linarith only [dist_triangle ω z (σ_star : ℂ), Metric.mem_closedBall.mp hω, hdist_z]
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 2) hr4_pos
      ⟨amp.hV_holo.mono (Metric.ball_subset_closedBall.trans (hsub_u.trans hsub2)),
        by simpa only [closure_ball _ hr4_pos.ne'] using (amp.hV_holo.continuousOn.mono (hsub_u.trans hsub2))⟩
      fun ω hω => amp.hV_disk ω (hsub_u (Metric.sphere_subset_closedBall hω))
    refine hc.trans_eq ?_
    norm_num; ring
  let ψ : ℝ → ℂ := fun u => amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I) / (amp.A : ℂ)
  let ψ₁ : ℝ → ℂ := fun u => Complex.I * deriv amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I) / (amp.A : ℂ)
  let ψ₂ : ℝ → ℂ := fun u => -(iteratedDeriv 2 amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I)) / (amp.A : ℂ)
  have hmem_ball : ∀ u : ℝ, |u| ≤ d / 8 → ((σ_star : ℂ) + (u : ℂ) * Complex.I) ∈ Metric.ball (σ_star : ℂ) (3 / 4 * d) := by
    intro u hu
    rw [Metric.mem_ball, Complex.dist_eq]
    simpa [Complex.norm_real] using lt_of_le_of_lt hu (by linarith only [hd_pos] : d / 8 < 3 / 4 * d)
  have hlin : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (σ_star : ℂ) + (v : ℂ) * Complex.I) Complex.I u := fun u =>
    (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (σ_star : ℂ)).congr_deriv (by simp)
  have hd_C1 : ∀ u : ℝ, |u| ≤ d / 8 →
      HasDerivAt amp.V (deriv amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I)) ((σ_star : ℂ) + (u : ℂ) * Complex.I) := fun u hu =>
    ((amp.hV_holo _ (hmem_ball u hu)).differentiableAt (Metric.isOpen_ball.mem_nhds (hmem_ball u hu))).hasDerivAt
  have hd_C2 : ∀ u : ℝ, |u| ≤ d / 8 →
      HasDerivAt (deriv amp.V) (iteratedDeriv 2 amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I))
        ((σ_star : ℂ) + (u : ℂ) * Complex.I) := fun u hu => by
    have hcont : AnalyticOnNhd ℂ amp.V (Metric.ball (σ_star : ℂ) (3 / 4 * d)) :=
      amp.hV_holo.analyticOnNhd Metric.isOpen_ball
    have hd2 := hcont.deriv _ (hmem_ball u hu) |>.differentiableAt.hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  have h_uIcc_abs_gen : ∀ u v : ℝ, v ∈ uIcc (0 : ℝ) u → |v| ≤ |u| := fun u v hv => by
    rcases le_or_gt 0 u with hu | hu
    · rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1, abs_of_nonneg hu]; exact hv.2
    · rw [uIcc_of_ge hu.le] at hv; rw [abs_of_nonpos hv.2, abs_of_neg hu]; linarith only [hv.1]
  have hsub_uIcc_u : ∀ u : ℝ, |u| ≤ d / 8 → uIcc (0 : ℝ) u ⊆ Icc (-(d / 8)) (d / 8) := fun u hu v hv =>
    abs_le.mp ((h_uIcc_abs_gen u v hv).trans hu)
  have hψ0_hd : ∀ u : ℝ, |u| ≤ d / 8 → HasDerivAt ψ (ψ₁ u) u := fun u hu =>
    (((hd_C1 u hu).comp u (hlin u)).div_const (amp.A : ℂ)).congr_deriv (by dsimp [ψ₁]; ring)
  have hψ1_hd : ∀ u : ℝ, |u| ≤ d / 8 → HasDerivAt ψ₁ (ψ₂ u) u := fun u hu => by
    have hcomp := (((hd_C2 u hu).comp u (hlin u)).const_mul Complex.I).div_const (amp.A : ℂ)
    refine hcomp.congr_deriv ?_
    dsimp [ψ₂]
    rw [show Complex.I * (iteratedDeriv 2 amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I) * Complex.I) =
      (Complex.I * Complex.I) * iteratedDeriv 2 amp.V ((σ_star : ℂ) + (u : ℂ) * Complex.I) by ring,
      Complex.I_mul_I]
    ring
  have hψ₁_cont : ContinuousOn ψ₁ (Icc (-(d / 8)) (d / 8)) := by
    have hcont : ContinuousOn (deriv amp.V) (Metric.ball (σ_star : ℂ) (3 / 4 * d)) :=
      (amp.hV_holo.analyticOnNhd Metric.isOpen_ball).deriv.continuousOn
    exact ((continuousOn_const.mul (hcont.comp (by fun_prop) fun u hu =>
      hmem_ball u (abs_le.mpr hu)))).div_const (amp.A : ℂ)
  have hψ₂_cont : ContinuousOn ψ₂ (Icc (-(d / 8)) (d / 8)) := by
    have hcont : ContinuousOn (iteratedDeriv 2 amp.V) (Metric.ball (σ_star : ℂ) (3 / 4 * d)) := by
      have ha := (amp.hV_holo.analyticOnNhd Metric.isOpen_ball).deriv.deriv.continuousOn
      refine ha.congr fun z _ => ?_
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hcont.comp (by fun_prop) fun u hu =>
      hmem_ball u (abs_le.mpr hu)).neg).div_const (amp.A : ℂ)
  have hψ₂_contOn : ∀ u : ℝ, |u| ≤ d / 8 → ContinuousOn ψ₂ (uIcc (0 : ℝ) u) := fun u hu =>
    hψ₂_cont.mono (hsub_uIcc_u u hu)
  have hψ₁_sub_contOn : ∀ u : ℝ, |u| ≤ d / 8 → ContinuousOn (fun v : ℝ => ψ₁ v - ψ₁ 0) (uIcc (0 : ℝ) u) := fun u hu =>
    ((hψ₁_cont.mono (hsub_uIcc_u u hu)).sub continuousOn_const)
  have hnorm_on : ∀ (f : ℝ → ℂ) (C : ℝ) (n : ℕ) (u : ℝ), 0 ≤ C →
      ContinuousOn f (uIcc (0 : ℝ) u) → (∀ v ∈ uIcc (0 : ℝ) u, ‖f v‖ ≤ C * |v| ^ n) →
      ‖∫ v in (0 : ℝ)..u, f v‖ ≤ C * |u| ^ (n + 1) / ((n : ℝ) + 1) := by
    intro f C n u hC hf hbd
    have hg : Continuous (fun v : ℝ => C * |v| ^ n) := continuous_const.mul (continuous_abs.pow n)
    rcases le_or_gt 0 u with hu | hu
    · have h1 := intervalIntegral.norm_integral_le_integral_norm hu (f := f) (μ := volume)
      have h2 := intervalIntegral.integral_mono_on hu
        ((hf.mono (by rw [uIcc_of_le hu])).intervalIntegrable_of_Icc hu |>.norm)
        (hg.intervalIntegrable 0 u) fun v hv => hbd v (uIcc_of_le hu ▸ hv)
      have h3 : ∫ v in (0 : ℝ)..u, C * |v| ^ n = C * u ^ (n + 1) / ((n : ℝ) + 1) := by
        have h_eq : ∫ v in (0 : ℝ)..u, C * |v| ^ n = ∫ v in (0 : ℝ)..u, C * v ^ n :=
          intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu] at hv; rw [abs_of_nonneg hv.1]
        rw [h_eq, intervalIntegral.integral_const_mul, integral_pow]; ring
      rw [abs_of_nonneg hu]; linarith only [h1, h2, h3]
    · rw [intervalIntegral.integral_symm, norm_neg]
      have h1 := intervalIntegral.norm_integral_le_integral_norm hu.le (f := f) (μ := volume)
      have h2 := intervalIntegral.integral_mono_on hu.le
        ((hf.mono (by rw [uIcc_of_ge hu.le])).intervalIntegrable_of_Icc hu.le |>.norm)
        (hg.intervalIntegrable u 0) fun v hv => hbd v ((uIcc_comm u 0 ▸ uIcc_of_le hu.le) ▸ hv)
      have h3 : ∫ v in u..0, C * |v| ^ n = C * (-u) ^ (n + 1) / ((n : ℝ) + 1) := by
        have h_eq : ∫ v in u..0, C * |v| ^ n = ∫ v in u..0, C * (-v) ^ n :=
          intervalIntegral.integral_congr fun v hv => by rw [uIcc_of_le hu.le] at hv; rw [abs_of_nonpos hv.2]
        rw [h_eq, intervalIntegral.integral_const_mul]
        have hc := intervalIntegral.integral_comp_neg (fun v : ℝ => v ^ n) (a := u) (b := 0)
        simp only [neg_zero] at hc; rw [hc, integral_pow]; ring
      rw [abs_of_neg hu]; linarith only [h1, h2, h3]
  have hbd1 : ∀ u : ℝ, |u| ≤ d / 8 → ‖ψ₁ u - ψ₁ 0‖ ≤ (32 * amp.D / d ^ 2) * |u| := fun u hu => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hψ1_hd v (abs_le.mpr (hsub_uIcc_u u hu hv)))
      ((hψ₂_contOn u hu).intervalIntegrable)
    rw [← hftc]
    refine (hnorm_on ψ₂ (32 * amp.D / d ^ 2) 0 u (by positivity) (hψ₂_contOn u hu)
      fun v hv => ?_).trans_eq (by norm_num; ring)
    have hv' : |v| ≤ d / 8 := (h_uIcc_abs_gen u v hv).trans hu
    dsimp [ψ₂]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hA_pos.le, div_le_iff₀ hA_pos, pow_zero, mul_one]
    exact (hV2_bd v hv').trans_eq (by ring)
  have hbd0 : ‖ψ τ - (ψ 0 + ψ₁ 0 * (τ : ℂ))‖ ≤ 16 * amp.D * (τ / d) ^ 2 := by
    have hd_sub : ∀ v ∈ uIcc (0 : ℝ) τ,
        HasDerivAt (fun x : ℝ => ψ x - (ψ 0 + ψ₁ 0 * (x : ℂ))) (ψ₁ v - ψ₁ 0) v := fun v hv =>
      ((hψ0_hd v (abs_le.mpr (hsub_uIcc_u τ hτ hv))).fun_sub
        (((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (ψ₁ 0)).const_add (ψ 0))).congr_deriv
        (by simp)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd_sub
      ((hψ₁_sub_contOn τ hτ).intervalIntegrable)
    simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_self, sub_zero] at hftc
    rw [← hftc]
    refine (hnorm_on (fun v => ψ₁ v - ψ₁ 0) (32 * amp.D / d ^ 2) 1 τ (by positivity)
      (hψ₁_sub_contOn τ hτ) fun v hv => ?_).trans_eq ?_
    · simpa only [pow_one] using hbd1 v ((h_uIcc_abs_gen τ v hv).trans hτ)
    · rw [div_pow, sq_abs]; ring
  have hV1_norm : ‖Complex.I * deriv amp.V (σ_star : ℂ) / (amp.A : ℂ)‖ ≤ 2 * amp.D / d := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hA_pos.le, div_le_iff₀ hA_pos]
    exact hV1_bd.trans_eq (by ring)
  refine ⟨?_, hV1_norm⟩
  simpa [ψ, ψ₁] using hbd0

private lemma binet_order_three_bound {c σ_star τ : ℝ} (hc_pos : 0 < c) (hσ0 : 0 < σ_star)
    (hσ1 : σ_star < 1) (hτ : |τ| ≤ min σ_star (1 - σ_star) / 8)
    (hεL : saddleEpsL c σ_star ≤ 3 / 1000) :
    let d := min σ_star (1 - σ_star)
    let g' := stripGDerivReal σ_star
    let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
    let ε_L := saddleEpsL c σ_star
    let s := τ / τ_sd
    ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) -
        FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ)) - 1‖ ≤ (1 / 5 : ℝ) * ε_L ^ 2 := by
  dsimp only
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let d := min σ_star (1 - σ_star)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  have hg'_pos : 0 < stripGDerivReal σ_star := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < saddleEpsL c σ_star := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_sq : ((c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))) ^ 2 = (c * stripGDerivReal σ_star)⁻¹ := by
    rw [Real.rpow_neg (by positivity), inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hεL_sq : saddleEpsL c σ_star ^ 2 = (c * stripGDerivReal σ_star * d ^ 2)⁻¹ := by
    change ((c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) / d) ^ 2 = _
    rw [div_pow, hτsd_sq, div_eq_mul_inv, ← mul_inv]
  have hinv_z : (c * (1 - σ_star))⁻¹ ≤ 2 * saddleEpsL c σ_star ^ 2 := by
    rw [hεL_sq, show 2 * (c * stripGDerivReal σ_star * d ^ 2)⁻¹ = (c * stripGDerivReal σ_star * d ^ 2 / 2)⁻¹ by ring]
    apply inv_anti₀ (by positivity)
    have hg'_lt : stripGDerivReal σ_star < 2 * σ_star / (1 - σ_star) := (stripG_deriv_bounds hσ0 hσ1).2
    have hprod : stripGDerivReal σ_star * d ^ 2 / 2 ≤ 1 - σ_star := by
      rcases le_or_gt σ_star (1 / 2) with hh | hh
      · have hd_eq : d = σ_star := min_eq_left (by linarith only [hh])
        have h1 : stripGDerivReal σ_star ≤ 2 := by
          have : 2 * σ_star / (1 - σ_star) ≤ 2 := by rw [div_le_iff₀ h1s_pos]; linarith only [hh]
          linarith only [hg'_lt, this]
        have hsq : σ_star ^ 2 ≤ 1 / 4 := by nlinarith only [hσ0, hh]
        rw [hd_eq]
        calc stripGDerivReal σ_star * σ_star ^ 2 / 2 ≤ 2 * (1 / 4) / 2 := by gcongr; exact hg'_pos.le
          _ = 1 / 4 := by ring
          _ ≤ 1 - σ_star := by linarith only [hh]
      · have hd_eq : d = 1 - σ_star := min_eq_right (by linarith only [hh])
        have hlt : stripGDerivReal σ_star < 2 / (1 - σ_star) :=
          hg'_lt.trans (div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos)
        rw [hd_eq]
        have hm : stripGDerivReal σ_star * (1 - σ_star) ^ 2 ≤ 2 * (1 - σ_star) := by
          have h1 := mul_lt_mul_of_pos_right hlt (pow_pos h1s_pos 2)
          have h2 : 2 / (1 - σ_star) * (1 - σ_star) ^ 2 = 2 * (1 - σ_star) := by
            field_simp [h1s_pos.ne']
          linarith only [h1, h2]
        linarith only [hm]
    have hmc := mul_le_mul_of_nonneg_left hprod hc_pos.le
    linarith only [hmc]
  let δ := FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) -
    FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ)
  -- Bound `‖δ‖` directly from `binetDiff` derivative on the vertical segment `[0, τ]`.
  have hδ : ‖δ‖ ≤ c * |τ| / (12 * (c * (1 - σ_star)) ^ 2) := by
    let w : ℝ → ℂ := fun v => (c : ℂ) * (1 - ((σ_star : ℂ) + (v : ℂ) * Complex.I))
    let F : ℝ → ℂ := fun v => FormalResearch.Asymptotics.binetRem (w v)
    let F' : ℝ → ℂ := fun v => (-((c : ℂ) * Complex.I)) * deriv FormalResearch.Asymptotics.binetRem (w v)
    have hre : ∀ v : ℝ, (w v).re = c * (1 - σ_star) := fun v => by simp [w, Complex.mul_re, Complex.sub_re]
    have hre_pos : ∀ v : ℝ, 0 < (w v).re := fun v => by rw [hre]; exact mul_pos hc_pos h1s_pos
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : ∀ v : ℝ, HasDerivAt F (F' v) v := fun v => by
      have hlin : HasDerivAt w (-((c : ℂ) * Complex.I)) v :=
        (((((Complex.ofRealCLM.hasDerivAt (x := v)).mul_const Complex.I).const_add (σ_star : ℂ)).const_sub 1).const_mul (c : ℂ)).congr_deriv
          (by simp)
      have hbr := ((FormalResearch.Asymptotics.binetRem_differentiableOn _ (hre_pos v)).differentiableAt
        (hopen.mem_nhds (hre_pos v))).hasDerivAt
      exact (hbr.comp v hlin).congr_deriv (by dsimp [F']; ring)
    have hF'_cont : Continuous F' := continuous_const.mul
      (((FormalResearch.Asymptotics.binetRem_differentiableOn.analyticOnNhd hopen).deriv).continuousOn.comp_continuous
        (by fun_prop) hre_pos)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) (hF'_cont.intervalIntegrable 0 τ)
    have hdiff : δ = F τ - F 0 := by
      simp only [δ, FormalResearch.Asymptotics.binetDiff, F, w, Complex.ofReal_zero, zero_mul, add_zero]; ring
    rw [hdiff, ← hftc]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ)
      (C := c / (12 * (c * (1 - σ_star)) ^ 2)) fun v _ => by
        dsimp [F']
        rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_pos.le,
          Complex.norm_I, mul_one, ← iteratedDeriv_one]
        have h1 := FormalResearch.Asymptotics.binetRem_iteratedDeriv_norm_le 1 (hre_pos v)
        rw [hre, Nat.factorial_one, Nat.cast_one] at h1
        calc c * ‖iteratedDeriv 1 FormalResearch.Asymptotics.binetRem (w v)‖
            ≤ c * (1 / (12 * (c * (1 - σ_star)) ^ 2)) := mul_le_mul_of_nonneg_left (by simpa using h1) hc_pos.le
          _ = c / (12 * (c * (1 - σ_star)) ^ 2) := by ring).trans_eq (by rw [sub_zero]; ring)
  have hδ_le : ‖δ‖ ≤ (1 / 48 : ℝ) * saddleEpsL c σ_star ^ 2 := by
    have hrat : c * |τ| / (12 * (c * (1 - σ_star)) ^ 2) =
        (|τ| / (1 - σ_star)) * (1 / (12 * (c * (1 - σ_star)))) := by
      field_simp [hc_pos.ne', h1s_pos.ne']
    have hτ_1s : |τ| / (1 - σ_star) ≤ 1 / 8 := by
      calc |τ| / (1 - σ_star) ≤ (d / 8) / (1 - σ_star) := by gcongr
        _ ≤ ((1 - σ_star) / 8) / (1 - σ_star) := by gcongr; exact min_le_right _ _
        _ = 1 / 8 := by field_simp [h1s_pos.ne']
    have hz_bd : 1 / (12 * (c * (1 - σ_star))) ≤ 1 / 6 * saddleEpsL c σ_star ^ 2 := by
      rw [one_div, mul_inv, ← one_div]
      calc (1 / 12 : ℝ) * (c * (1 - σ_star))⁻¹ ≤ (1 / 12 : ℝ) * (2 * saddleEpsL c σ_star ^ 2) := by gcongr
        _ = 1 / 6 * saddleEpsL c σ_star ^ 2 := by ring
    calc ‖δ‖ ≤ c * |τ| / (12 * (c * (1 - σ_star)) ^ 2) := hδ
      _ = (|τ| / (1 - σ_star)) * (1 / (12 * (c * (1 - σ_star)))) := hrat
      _ ≤ (1 / 8 : ℝ) * (1 / 6 * saddleEpsL c σ_star ^ 2) :=
          mul_le_mul hτ_1s hz_bd (by positivity) (by norm_num)
      _ = (1 / 48 : ℝ) * saddleEpsL c σ_star ^ 2 := by ring
  have hδ1 : ‖δ‖ ≤ 1 / 2 := hδ_le.trans (by nlinarith only [hεL, hεL_pos])
  have hexp_le : Real.exp ‖δ‖ ≤ 2 := by
    have h1 : 1 / 2 ≤ Real.exp (-‖δ‖) := by linarith only [hδ1, Real.add_one_le_exp (-‖δ‖)]
    rw [Real.exp_neg] at h1
    have h2 := inv_anti₀ (by norm_num) h1
    rw [inv_inv] at h2
    exact h2.trans_eq (by norm_num)
  have hnorm_e : ‖Complex.exp δ - 1‖ ≤ ‖δ‖ * Real.exp ‖δ‖ := by
    let γ : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * δ)
    have hd : ∀ t : ℝ, HasDerivAt γ (δ * γ t) t := fun t =>
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const δ).cexp).congr_deriv (by simp [γ]; ring)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous fun t : ℝ => δ * γ t).intervalIntegrable 0 1)
    have h0 : γ 0 = 1 := by simp [γ]
    have h1 : γ 1 = Complex.exp δ := by simp [γ]
    rw [h1, h0] at hftc
    rw [← hftc]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := ‖δ‖ * Real.exp ‖δ‖) fun t ht => ?_).trans_eq (by norm_num)
    rw [uIoc_of_le zero_le_one] at ht
    rw [norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * δ).re ≤ ‖δ‖ := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans'
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm δ) ht.1.le)
    gcongr
  calc ‖Complex.exp δ - 1‖ ≤ ‖δ‖ * Real.exp ‖δ‖ := hnorm_e
    _ ≤ ((1 / 48 : ℝ) * saddleEpsL c σ_star ^ 2) * 2 := mul_le_mul hδ_le hexp_le (Real.exp_pos _).le (by positivity)
    _ ≤ (1 / 5 : ℝ) * saddleEpsL c σ_star ^ 2 := by nlinarith only [sq_nonneg (saddleEpsL c σ_star)]

/-! ### Second-order core and outer bounds and Proposition `cel:total-saddle-2` -/

private lemma poly_even_exp_neg_quarter_le (s : ℝ) :
    (1 + s ^ 2 + s ^ 4 + s ^ 6) * Real.exp (-(1 / 4 : ℝ) * s ^ 2) ≤
      1375 * Real.exp (-(1 / 12 : ℝ) * s ^ 2) := by
  have hpow : ∀ k : ℕ, s ^ (2 * k) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ (6 : ℝ) ^ k * (Nat.factorial k : ℝ) := by
    intro k
    have h1 : (1 / 6 * s ^ 2) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (1 / 6 * s ^ 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) k
    have hfac_pos : (0 : ℝ) < Nat.factorial k := by positivity
    have hpow' : (1 / 6 * s ^ 2) ^ k = (6 : ℝ)⁻¹ ^ k * s ^ (2 * k) := by rw [mul_pow, pow_mul, one_div]
    rw [hpow', div_le_iff₀ hfac_pos] at h1
    rw [show -(1 / 6 : ℝ) * s ^ 2 = -(1 / 6 * s ^ 2) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_le_iff₀ (Real.exp_pos _)]
    calc s ^ (2 * k) = (6 : ℝ) ^ k * ((6 : ℝ)⁻¹ ^ k * s ^ (2 * k)) := by
          rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, one_mul]
      _ ≤ (6 : ℝ) ^ k * (Real.exp (1 / 6 * s ^ 2) * (Nat.factorial k : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (6 : ℝ) ^ k * (Nat.factorial k : ℝ) * Real.exp (1 / 6 * s ^ 2) := by ring
  have h0 : 1 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1 := by
    rw [one_mul]; exact Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg s])
  have h2 : s ^ 2 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 6 := by
    simpa using (hpow 1).trans_eq (by norm_num)
  have h4 : s ^ 4 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 72 := by
    simpa [Nat.factorial] using (hpow 2).trans_eq (by norm_num)
  have h6 : s ^ 6 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1296 := by
    simpa [Nat.factorial] using (hpow 3).trans_eq (by norm_num)
  have hsum : (1 + s ^ 2 + s ^ 4 + s ^ 6) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) ≤ 1375 := by
    linarith only [h0, h2, h4, h6,
      show (1 + s ^ 2 + s ^ 4 + s ^ 6) * Real.exp (-(1 / 6 : ℝ) * s ^ 2) =
        1 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) + s ^ 2 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) +
        s ^ 4 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) + s ^ 6 * Real.exp (-(1 / 6 : ℝ) * s ^ 2) by ring]
  have hsplit : Real.exp (-(1 / 4 : ℝ) * s ^ 2) =
      Real.exp (-(1 / 6 : ℝ) * s ^ 2) * Real.exp (-(1 / 12 : ℝ) * s ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le

private lemma exp_c_r_ph_second_order {c ξ σ_star τ : ℝ}
    (hc_pos : 0 < c) (hξ_pos : 0 < ξ) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (hs_core : |τ / (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))| ≤
      saddleEpsL c σ_star ^ (-(1 / 4 : ℝ)))
    (hεL : saddleEpsL c σ_star ≤ 3 / 1000) :
    let g' := stripGDerivReal σ_star
    let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
    let ε_L := saddleEpsL c σ_star
    let s := τ / τ_sd
    let r_ph := mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ
    let α₃ := -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)
    ‖Complex.exp ((c : ℂ) * r_ph) - (1 + α₃ * ((s ^ 3 : ℝ) : ℂ)) * (Real.exp (-s ^ 2 / 2) : ℂ)‖ ≤
      (13 * s ^ 4 + 289 * s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) ∧
    ‖Complex.exp ((c : ℂ) * r_ph)‖ ≤ Real.exp (-s ^ 2 / 4) := by
  dsimp only
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let d := min σ_star (1 - σ_star)
  have hd_pos : 0 < d := lt_min hσ0 h1s_pos
  have hg'_pos : 0 < stripGDerivReal σ_star := stripGDerivReal_pos hσ0 hσ1
  have hτsd_pos : 0 < (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
  let ε_L := saddleEpsL c σ_star
  let s := τ / τ_sd
  let r_ph := mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ
  let α₃ := -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hεL_34_pow4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 = ε_L ^ 3 := by
    rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
      show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
    have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
      rw [hεL_34_pow4]; exact (pow_le_pow_left₀ hεL_pos.le hεL 3).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have h17_le : 17 * ε_L ^ (3 / 4 : ℝ) ≤ 1 / 4 := by
    have h4 : (17 * ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by
      rw [mul_pow, hεL_34_pow4]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hεL_pos.le hεL 3) (by norm_num)).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have hτ_d8 : |τ| ≤ d / 8 := by
    have hτ_eq : |τ| = (ε_L * |s|) * d := by
      dsimp [ε_L, saddleEpsL, s, d]
      rw [abs_div, abs_of_pos hτsd_pos]
      field_simp [hd_pos.ne', hτsd_pos.ne']
    have hes_34 : ε_L * |s| ≤ ε_L ^ (3 / 4 : ℝ) := by
      calc ε_L * |s| ≤ ε_L * ε_L ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hs_core hεL_pos.le
        _ = ε_L ^ (3 / 4 : ℝ) := by
            nth_rw 1 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    rw [hτ_eq]
    calc (ε_L * |s|) * d ≤ ε_L ^ (3 / 4 : ℝ) * d := mul_le_mul_of_nonneg_right hes_34 hd_pos.le
      _ ≤ (1 / 8 : ℝ) * d := mul_le_mul_of_nonneg_right hεL_34_le_18 hd_pos.le
      _ = d / 8 := by ring
  have hphase := c_r_ph_second_order hc_pos hξ_pos hσ0 hσ1 hσ_eq hτ_d8
  let z : ℂ := (c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ)
  let z₀ : ℂ := α₃ * ((s ^ 3 : ℝ) : ℂ)
  have hz_norm : ‖z‖ ≤ 17 * ε_L * |s| ^ 3 := hphase.2
  have hz_s2 : ‖z‖ ≤ s ^ 2 / 4 := by
    have hpow3 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
    have hes_34 : ε_L * |s| ≤ ε_L ^ (3 / 4 : ℝ) := by
      calc ε_L * |s| ≤ ε_L * ε_L ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hs_core hεL_pos.le
        _ = ε_L ^ (3 / 4 : ℝ) := by
            nth_rw 1 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    calc ‖z‖ ≤ 17 * ε_L * (|s| * s ^ 2) := by rw [← hpow3]; exact hz_norm
      _ = 17 * (ε_L * |s|) * s ^ 2 := by ring
      _ ≤ 17 * ε_L ^ (3 / 4 : ℝ) * s ^ 2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hes_34 (by norm_num)) (sq_nonneg s)
      _ ≤ (1 / 4 : ℝ) * s ^ 2 := mul_le_mul_of_nonneg_right h17_le (sq_nonneg s)
      _ = s ^ 2 / 4 := by ring
  have hz_re : z.re ≤ s ^ 2 / 4 := (Complex.re_le_norm z).trans hz_s2
  have hmax_re : max z.re 0 ≤ s ^ 2 / 4 := max_le hz_re (by positivity)
  have hexp_eq : Complex.exp ((c : ℂ) * r_ph) = Complex.exp z * (Real.exp (-s ^ 2 / 2) : ℂ) := by
    rw [show (c : ℂ) * r_ph = z + ((-s ^ 2 / 2 : ℝ) : ℂ) by dsimp [z]; push_cast; ring,
      Complex.exp_add, Complex.ofReal_exp]
  have hdiff_eq : Complex.exp ((c : ℂ) * r_ph) - (1 + α₃ * ((s ^ 3 : ℝ) : ℂ)) * (Real.exp (-s ^ 2 / 2) : ℂ) =
      ((Complex.exp z - 1 - z) + (z - z₀)) * (Real.exp (-s ^ 2 / 2) : ℂ) := by
    rw [hexp_eq]; dsimp [z₀]; ring
  have hrem1 : ‖Complex.exp z - 1 - z‖ ≤ (289 / 2 : ℝ) * s ^ 6 * ε_L ^ 2 * Real.exp (s ^ 2 / 4) := by
    have h1 := norm_exp_sub_one_sub_id_le z
    have hzsq : ‖z‖ ^ 2 / 2 ≤ (289 / 2 : ℝ) * s ^ 6 * ε_L ^ 2 := by
      have hp6 : |s| ^ 6 = s ^ 6 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs, ← pow_mul]
      calc ‖z‖ ^ 2 / 2 ≤ (17 * ε_L * |s| ^ 3) ^ 2 / 2 := by gcongr
        _ = (289 / 2 : ℝ) * |s| ^ 6 * ε_L ^ 2 := by ring
        _ = (289 / 2 : ℝ) * s ^ 6 * ε_L ^ 2 := by rw [hp6]
    calc ‖Complex.exp z - 1 - z‖ ≤ (‖z‖ ^ 2 / 2) * Real.exp (max z.re 0) := h1
      _ ≤ ((289 / 2 : ℝ) * s ^ 6 * ε_L ^ 2) * Real.exp (s ^ 2 / 4) :=
          mul_le_mul hzsq (Real.exp_le_exp.mpr hmax_re) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hrem2 : ‖z - z₀‖ ≤ 13 * s ^ 4 * ε_L ^ 2 * Real.exp (s ^ 2 / 4) := by
    have h1 : ‖z - z₀‖ ≤ 13 * ε_L ^ 2 * s ^ 4 := by
      simpa only [z, z₀, show ((c : ℂ) * r_ph + ((s ^ 2 / 2 : ℝ) : ℂ)) - α₃ * ((s ^ 3 : ℝ) : ℂ) =
        (c : ℂ) * r_ph - (-((s ^ 2 / 2 : ℝ) : ℂ) + α₃ * ((s ^ 3 : ℝ) : ℂ)) by ring] using hphase.1
    have hexp1 : 1 ≤ Real.exp (s ^ 2 / 4) := Real.one_le_exp (by positivity)
    calc ‖z - z₀‖ ≤ 13 * s ^ 4 * ε_L ^ 2 * 1 := by linarith only [h1]
      _ ≤ 13 * s ^ 4 * ε_L ^ 2 * Real.exp (s ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
  have hexp_split : Real.exp (s ^ 2 / 4) * Real.exp (-s ^ 2 / 2) = Real.exp (-s ^ 2 / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · rw [hdiff_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc ‖(Complex.exp z - 1 - z) + (z - z₀)‖ * Real.exp (-s ^ 2 / 2)
        ≤ (‖Complex.exp z - 1 - z‖ + ‖z - z₀‖) * Real.exp (-s ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
      _ ≤ ((289 / 2 : ℝ) * s ^ 6 * ε_L ^ 2 * Real.exp (s ^ 2 / 4) +
            13 * s ^ 4 * ε_L ^ 2 * Real.exp (s ^ 2 / 4)) * Real.exp (-s ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (add_le_add hrem1 hrem2) (Real.exp_pos _).le
      _ = ((13 * s ^ 4 + (289 / 2 : ℝ) * s ^ 6) * ε_L ^ 2) *
            (Real.exp (s ^ 2 / 4) * Real.exp (-s ^ 2 / 2)) := by ring
      _ = (13 * s ^ 4 + (289 / 2 : ℝ) * s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by rw [hexp_split]
      _ ≤ (13 * s ^ 4 + 289 * s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
          gcongr; norm_num
  · rw [hexp_eq, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp z.re * Real.exp (-s ^ 2 / 2)
        ≤ Real.exp (s ^ 2 / 4) * Real.exp (-s ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hz_re) (Real.exp_pos _).le
      _ = Real.exp (-s ^ 2 / 4) := hexp_split

private lemma A1_second_order_taylor {u : ℝ} (hu : |u| ≤ 1 / 8) :
    let A₁ := (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
    ‖A₁ - (1 + (Complex.I / 2 : ℂ) * (u : ℂ))‖ ≤ (3 / 8 : ℝ) * u ^ 2 ∧ ‖A₁‖ ≤ 1 := by
  dsimp only
  let g : ℝ → ℂ := fun v => (1 - (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let g₁ : ℝ → ℂ := fun v => (Complex.I / 2 : ℂ) * (1 - (v : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ))
  let g₂ : ℝ → ℂ := fun v => (-(3 / 4 : ℂ)) * (1 - (v : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))
  have hre1 : ∀ v : ℝ, (1 - (v : ℂ) * Complex.I).re = 1 := fun v => by
    simp [Complex.sub_re, Complex.mul_re]
  have hre_pos : ∀ v : ℝ, 0 < (1 - (v : ℂ) * Complex.I).re := fun v => by rw [hre1]; exact one_pos
  have hlin : ∀ v : ℝ, HasDerivAt (fun x : ℝ => 1 - (x : ℂ) * Complex.I) (-Complex.I) v := fun v =>
    (((Complex.ofRealCLM.hasDerivAt (x := v)).mul_const Complex.I).const_sub 1).congr_deriv (by simp)
  have hcpow_d : ∀ (α : ℂ) (v : ℝ),
      HasDerivAt (fun x : ℝ => (1 - (x : ℂ) * Complex.I) ^ α)
        (-Complex.I * α * (1 - (v : ℂ) * Complex.I) ^ (α - 1)) v := fun α v => by
    have hnz : 1 - (v : ℂ) * Complex.I ∈ Complex.slitPlane := Or.inl (hre_pos v)
    have hd := ((hasDerivAt_id (1 - (v : ℂ) * Complex.I)).cpow_const (c := α) hnz).comp v (hlin v)
    exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by simp; ring)
  have hg0 : ∀ v : ℝ, HasDerivAt g (g₁ v) v := fun v => by
    refine (hcpow_d (-(1 / 2 : ℂ)) v).congr_deriv ?_
    dsimp [g₁]
    rw [show -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) by ring]
    ring
  have hg1 : ∀ v : ℝ, HasDerivAt g₁ (g₂ v) v := fun v => by
    refine ((hcpow_d (-(3 / 2 : ℂ)) v).const_mul (Complex.I / 2 : ℂ)).congr_deriv ?_
    dsimp [g₂]
    rw [show -(3 / 2 : ℂ) - 1 = -(5 / 2 : ℂ) by ring]
    calc (Complex.I / 2 : ℂ) * (-Complex.I * -(3 / 2 : ℂ) * (1 - (v : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)))
        = (3 / 4 : ℂ) * (Complex.I * Complex.I) * (1 - (v : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
      _ = -(3 / 4 : ℂ) * (1 - (v : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by rw [Complex.I_mul_I]; ring
  have hcpow_norm_le1 : ∀ (q : ℝ) (v : ℝ), 0 < q → ‖(1 - (v : ℂ) * Complex.I) ^ ((-q : ℝ) : ℂ)‖ ≤ 1 := fun q v hq => by
    let w : ℂ := 1 - (v : ℂ) * Complex.I
    have hw_re : 0 < w.re := hre_pos v
    have hw_norm : 1 ≤ ‖w‖ := le_trans (by rw [hre1]) (Complex.re_le_norm w)
    have hne : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw_re; exact lt_irrefl _ hw_re
    rw [Complex.norm_cpow_of_ne_zero hne]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hw_norm (by linarith only [hq])
  have hg2_cont : Continuous g₂ := by
    refine continuous_const.mul (Continuous.cpow (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)) continuous_const ?_)
    intro v; exact Or.inl (hre_pos v)
  have hg1_cont : Continuous g₁ := by
    refine continuous_const.mul (Continuous.cpow (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)) continuous_const ?_)
    intro v; exact Or.inl (hre_pos v)
  have hg2_bd : ∀ v : ℝ, ‖g₂ v‖ ≤ (3 / 4 : ℝ) := fun v => by
    dsimp [g₂]
    rw [norm_mul, norm_neg, show (3 / 4 : ℂ) = ((3 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    have hb := hcpow_norm_le1 (5 / 2) v (by norm_num)
    rw [show ((-(5 / 2 : ℝ) : ℝ) : ℂ) = -(5 / 2 : ℂ) by push_cast; ring] at hb
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (mul_one _)
  have hg1_bd : ∀ v : ℝ, ‖g₁ v - g₁ 0‖ ≤ (3 / 4 : ℝ) * |v| := fun v => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg1 x) (hg2_cont.intervalIntegrable 0 v)
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (by norm_num) hg2_cont v fun x _ => (hg2_bd x).trans_eq (by simp)).trans_eq (by norm_num)
  have hg0_bd : ‖g u - (g 0 + g₁ 0 * (u : ℂ))‖ ≤ (3 / 8 : ℝ) * u ^ 2 := by
    have hsub : ∀ v : ℝ, HasDerivAt (fun x : ℝ => g x - (g 0 + g₁ 0 * (x : ℂ))) (g₁ v - g₁ 0) v := fun v =>
      ((hg0 v).fun_sub (((Complex.ofRealCLM.hasDerivAt (x := v)).const_mul (g₁ 0)).const_add (g 0))).congr_deriv (by simp)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hsub x)
      ((hg1_cont.sub continuous_const).intervalIntegrable 0 u)
    simp only [Complex.ofReal_zero, mul_zero, add_zero, sub_self, sub_zero] at hftc
    rw [← hftc]
    exact (norm_intervalIntegral_le_abs_pow_loc (by norm_num) (hg1_cont.sub continuous_const) u fun x _ =>
      (hg1_bd x).trans_eq (by simp)).trans_eq (by rw [sq_abs]; norm_num; ring)
  refine ⟨?_, ?_⟩
  · have hg00 : g 0 = 1 := by simp [g]
    have hg10 : g₁ 0 = Complex.I / 2 := by simp [g₁]
    simpa only [g, hg00, hg10] using hg0_bd
  · have hb := hcpow_norm_le1 (1 / 2) u (by norm_num)
    rw [show ((-(1 / 2 : ℝ) : ℝ) : ℂ) = -(1 / 2 : ℂ) by push_cast; ring] at hb
    exact hb

private lemma integral_Icc_odd_eq_zero {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Continuous f)
    (hodd : ∀ s : ℝ, f (-s) = -f s) :
    ∫ s in Icc (-a) a, f s = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [ha])]
  have hneg : ∫ s in (-a)..a, f s = ∫ s in (-a)..a, -f s := by
    calc ∫ s in (-a)..a, f s = ∫ s in (-a)..a, f (-s) := by
          have hc := intervalIntegral.integral_comp_neg f (a := -a) (b := a)
          simpa using hc.symm
      _ = ∫ s in (-a)..a, -f s := intervalIntegral.integral_congr fun s _ => hodd s
  rw [intervalIntegral.integral_neg] at hneg
  exact eq_zero_of_neg_eq hneg.symm

private lemma total_core_second_order_bound {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : TotalSaddleSecondOrderAmp c σ_star)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let ε_L := saddleEpsL c σ_star
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let v₀ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
    let F_rel := fun τ : ℝ => (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
      amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ)
    (1 / (Real.sqrt (2 * π) * τ_sd)) *
      (|∫ τ in Icc (-τ_core) τ_core, ((F_rel τ).re - v₀.re * Real.exp (-(τ / τ_sd) ^ 2 / 2))| +
        2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2)) ≤ 980000 * amp.D * ε_L ^ 2 := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have hΔ_pos : 0 < Δ := by linarith
  have hξ_pos : 0 < ξ := by rw [hξ]; positivity
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let d := min σ_star (1 - σ_star)
  have hm_pos : 0 < d := lt_min hσ0 h1s_pos
  let g' := stripGDerivReal σ_star
  let ε_L := saddleEpsL c σ_star
  let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let a := ε_L ^ (-(1 / 4 : ℝ))
  let τ_core := a * τ_sd
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  let v₀ : ℂ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
  have hv₀_le : ‖v₀‖ ≤ 1 := by
    dsimp [v₀]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg amp.hA.le, div_le_one amp.hA]
    exact amp.hV0_le
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hεL_pos _
  have hK₀_spec := mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1
  have hK₀_pos : 0 < K₀ := hK₀_spec.2
  have hεL_ub := (saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq).2.2
  have hεL_le_3e3 : ε_L ≤ 3 / 1000 := hεL_ub.le.trans (h_eps0.trans (min_le_left _ _))
  have hεL_34_pow4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 = ε_L ^ 3 := by
    rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
      show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
    have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
      rw [hεL_34_pow4]; exact (pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 3).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have h15_14_le4 : 15 * ε_L ^ (1 / 4 : ℝ) ≤ 4 := by
    have h4 : (15 * ε_L ^ (1 / 4 : ℝ)) ^ 4 ≤ (4 : ℝ) ^ 4 := by
      rw [mul_pow, ← Real.rpow_natCast (ε_L ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
        show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
      nlinarith only [hεL_le_3e3]
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have hτsd_le_epsd : τ_sd = ε_L * d := by
    dsimp [ε_L, saddleEpsL, τ_sd, d]; field_simp [(lt_min hσ0 h1s_pos).ne']
  have hτsd_le_1s : τ_sd / (1 - σ_star) ≤ ε_L := by
    rw [hτsd_le_epsd]
    have hm1 : d ≤ 1 - σ_star := min_le_right _ _
    calc ε_L * d / (1 - σ_star) = ε_L * (d / (1 - σ_star)) := by ring
      _ ≤ ε_L * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hm1 h1s_pos.le) hεL_pos.le
      _ = ε_L := mul_one _
  let F_rel := fun τ : ℝ => (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
    amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ)
  have hFrel_int : Integrable F_rel :=
    (totalSaddle_integrable hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp.toTotalSaddleAmp).div_const _
  let α₃ : ℂ := -(Complex.I * (c : ℂ) * deriv^[2] stripG (σ_star : ℂ) * ((τ_sd ^ 3 : ℝ) : ℂ) / 6)
  let V₁ : ℂ := Complex.I * deriv amp.V (σ_star : ℂ) / (amp.A : ℂ)
  let a₁ : ℂ := (Complex.I / (2 * ((1 - σ_star : ℝ) : ℂ))) * (τ_sd : ℂ)
  let b₁ : ℂ := V₁ * (τ_sd : ℂ)
  let c₁ : ℂ := b₁ + v₀ * a₁
  let OddProf : ℝ → ℂ := fun s =>
    (c₁ * (s : ℂ) + v₀ * α₃ * ((s ^ 3 : ℝ) : ℂ)) * (Real.exp (-s ^ 2 / 2) : ℂ)
  have hOdd_cont : Continuous OddProf := by fun_prop
  have hOdd_int0 : ∫ s in Icc (-a) a, OddProf s = 0 :=
    integral_Icc_odd_eq_zero ha_pos.le hOdd_cont fun s => by
      dsimp [OddProf]; push_cast; ring
  have hV_im : (amp.V (σ_star : ℂ)).im = 0 := amp.V_im_zero
  have hv₀_im : v₀.im = 0 := by
    dsimp [v₀]; rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hV_im]; ring
  have h_ptwise : ∀ s ∈ Icc (-a) a,
      ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s‖ ≤
        289 * amp.D * (1 + s ^ 2 + s ^ 4 + s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
    intro s hs
    have hs_abs : |s| ≤ a := abs_le.mpr hs
    let τ : ℝ := τ_sd * s
    have hs_core' : |τ / τ_sd| ≤ ε_L ^ (-(1 / 4 : ℝ)) := by
      simpa only [τ, mul_div_cancel_left₀ s hτsd_pos.ne'] using hs_abs
    have hτ_d8 : |τ| ≤ d / 8 := by
      dsimp [τ]; rw [abs_mul, abs_of_pos hτsd_pos, hτsd_le_epsd]
      calc (ε_L * d) * |s| = (ε_L * |s|) * d := by ring
        _ ≤ (ε_L * a) * d := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_abs hεL_pos.le) hm_pos.le
        _ = ε_L ^ (3 / 4 : ℝ) * d := by
            dsimp [a]; nth_rw 1 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
        _ ≤ (1 / 8 : ℝ) * d := mul_le_mul_of_nonneg_right hεL_34_le_18 hm_pos.le
        _ = d / 8 := by ring
    let u : ℝ := τ / (1 - σ_star)
    have hu_abs : |u| ≤ 1 / 8 := by
      dsimp [u]; rw [abs_div, abs_of_pos h1s_pos]
      calc |τ| / (1 - σ_star) ≤ (d / 8) / (1 - σ_star) := div_le_div_of_nonneg_right hτ_d8 h1s_pos.le
        _ ≤ ((1 - σ_star) / 8) / (1 - σ_star) := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h1s_pos.le
        _ = 1 / 8 := by field_simp [h1s_pos.ne']
    let A₁ : ℂ := (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
    let A₂ : ℂ := Complex.exp (FormalResearch.Asymptotics.binetDiff c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) -
      FormalResearch.Asymptotics.binetDiff c (σ_star : ℂ))
    let A₃ : ℂ := amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I) / (amp.A : ℂ)
    let r_ph : ℂ := mellinPhi ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ
    let E : ℂ := Complex.exp ((c : ℂ) * r_ph)
    have hF_fac : F_rel τ = A₁ * A₂ * A₃ * E := by
      -- Factorization identical to `LobeSaddleCore.total_core_pointwise`.
      have hK₀_eq : mellinK0 c (σ_star : ℂ) ξ = (K₀ : ℂ) := Complex.ext rfl (by simp [K₀, hK₀_spec.1])
      have hcpow : (1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) / (1 - (σ_star : ℂ)) ^ (-(1 / 2 : ℂ)) = A₁ := by
        have h1s_c : (1 - (σ_star : ℂ)) = ((1 - σ_star : ℝ) : ℂ) := by push_cast; rfl
        have h1sc_ne : ((1 - σ_star : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1s_pos.ne'
        have h1sc_ne' : (1 - (σ_star : ℂ)) ≠ 0 := by exact_mod_cast h1s_pos.ne'
        have hmul : 1 - ((σ_star : ℂ) + (τ : ℂ) * Complex.I) =
            ((1 - σ_star : ℝ) : ℂ) * (1 - (u : ℂ) * Complex.I) := by
          dsimp [u]; push_cast; field_simp [h1sc_ne']; ring
        have h1z_ne : (1 - (σ_star : ℂ)) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
          rw [h1s_c, show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow h1s_pos.le]
          exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos h1s_pos _).ne'
        have hz2_re : (1 - (u : ℂ) * Complex.I).re = 1 := by simp [Complex.sub_re, Complex.mul_re]
        have hz2_ne : (1 - (u : ℂ) * Complex.I) ≠ 0 := fun h => by rw [h] at hz2_re; simp at hz2_re
        have hlog_1s : Complex.log ((1 - σ_star : ℝ) : ℂ) = ((Real.log (1 - σ_star) : ℝ) : ℂ) := by
          simpa using Complex.log_ofReal_mul h1s_pos (one_ne_zero : (1 : ℂ) ≠ 0)
        have hmul_cpow : (((1 - σ_star : ℝ) : ℂ) * (1 - (u : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) =
            ((1 - σ_star : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (u : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) := by
          rw [Complex.cpow_def_of_ne_zero (mul_ne_zero h1sc_ne hz2_ne),
            Complex.cpow_def_of_ne_zero h1sc_ne, Complex.cpow_def_of_ne_zero hz2_ne,
            Complex.log_ofReal_mul h1s_pos hz2_ne, hlog_1s, add_mul, Complex.exp_add]
        rw [hmul, hmul_cpow, ← h1s_c, mul_div_cancel_left₀ _ h1z_ne]
      rw [show F_rel τ = (mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
          amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)) / ((K₀ * amp.A : ℝ) : ℂ) from rfl,
        Complex.ofReal_mul K₀ amp.A, mul_div_mul_comm, ← hK₀_eq,
        mellinK0, mellinK0, mul_div_mul_comm, mul_div_mul_comm, hcpow, ← Complex.exp_sub, ← Complex.exp_sub,
        show (c : ℂ) * mellinPhi _ ξ - (c : ℂ) * mellinPhi (σ_star : ℂ) ξ = (c : ℂ) * r_ph by dsimp [r_ph]; ring]
      dsimp [A₂, A₃, E]; ring
    obtain ⟨hA1_rem, hA1_le1⟩ := A1_second_order_taylor hu_abs
    have hA2_rem : ‖A₂ - 1‖ ≤ (1 / 5 : ℝ) * ε_L ^ 2 := binet_order_three_bound hc_pos hσ0 hσ1 hτ_d8 hεL_le_3e3
    obtain ⟨hV_rem, hV1_norm⟩ := V_second_order_taylor hσ0 hσ1 amp hτ_d8
    obtain ⟨hE_rem, hE_norm⟩ := exp_c_r_ph_second_order hc_pos hξ_pos hσ0 hσ1 hσ_eq hs_core' hεL_le_3e3
    have hphase := c_r_ph_second_order hc_pos hξ_pos hσ0 hσ1 hσ_eq hτ_d8
    have hD0 : 0 ≤ amp.D := by linarith only [amp.hD]
    have hα3_bd : ‖α₃‖ ≤ 18 * ε_L := by
      have hτsd_d8 : |τ_sd| ≤ d / 8 := by
        rw [abs_of_pos hτsd_pos, hτsd_le_epsd]; nlinarith only [hεL_le_3e3, hm_pos]
      have hp1 := c_r_ph_second_order hc_pos hξ_pos hσ0 hσ1 hσ_eq hτsd_d8
      change ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) -
            (-(((τ_sd / τ_sd) ^ 2 / 2 : ℝ) : ℂ) + α₃ * (((τ_sd / τ_sd) ^ 3 : ℝ) : ℂ))‖ ≤
          13 * ε_L ^ 2 * (τ_sd / τ_sd) ^ 4 ∧
        ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) +
            (((τ_sd / τ_sd) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
          17 * ε_L * |τ_sd / τ_sd| ^ 3 at hp1
      simp only [div_self hτsd_pos.ne', one_pow, mul_one, abs_one] at hp1
      have heq : α₃ = ((c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) +
        ((1 / 2 : ℝ) : ℂ)) - (((c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) -
        (-((1 / 2 : ℝ) : ℂ) + α₃ * ((1 : ℝ) : ℂ)))) := by
        dsimp [α₃]; push_cast; ring
      rw [heq]
      calc ‖((c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) +
              ((1 / 2 : ℝ) : ℂ)) - (((c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) -
              (-((1 / 2 : ℝ) : ℂ) + α₃ * ((1 : ℝ) : ℂ))))‖
          ≤ ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) +
              ((1 / 2 : ℝ) : ℂ)‖ +
            ‖(c : ℂ) * (mellinPhi ((σ_star : ℂ) + (τ_sd : ℂ) * Complex.I) ξ - mellinPhi (σ_star : ℂ) ξ) -
              (-((1 / 2 : ℝ) : ℂ) + α₃ * ((1 : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 17 * ε_L + 13 * ε_L ^ 2 := add_le_add hp1.2 hp1.1
        _ ≤ 18 * ε_L := by nlinarith only [hεL_pos, hεL_le_3e3]
    have hA3_bd : ‖A₃‖ ≤ amp.D := by
      have hmem : (σ_star : ℂ) + (τ : ℂ) * Complex.I ∈ Metric.closedBall (σ_star : ℂ) (d / 2) := by
        rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_I, mul_one]
        linarith only [hτ_d8, hm_pos]
      dsimp [A₃]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg amp.hA.le, div_le_iff₀ amp.hA]
      exact amp.hV_disk _ hmem
    have ha1_norm : ‖a₁‖ ≤ (1 / 2 : ℝ) * ε_L := by
      dsimp [a₁]
      simp only [norm_mul, norm_div, Complex.norm_I,
        show (2 : ℂ) * ((1 - σ_star : ℝ) : ℂ) = ((2 * (1 - σ_star) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * (1 - σ_star)),
        abs_of_pos hτsd_pos]
      rw [show 1 / (2 * (1 - σ_star)) * τ_sd = (1 / 2 : ℝ) * (τ_sd / (1 - σ_star)) by ring]
      exact mul_le_mul_of_nonneg_left hτsd_le_1s (by norm_num)
    have hb1_norm : ‖b₁‖ ≤ 2 * amp.D * ε_L := by
      dsimp [b₁]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτsd_pos.le, hτsd_le_epsd]
      calc ‖V₁‖ * (ε_L * d) ≤ (2 * amp.D / d) * (ε_L * d) :=
            mul_le_mul_of_nonneg_right hV1_norm (mul_nonneg hεL_pos.le hm_pos.le)
        _ = 2 * amp.D * ε_L := by field_simp [hm_pos.ne']
    have hc1_norm : ‖c₁‖ ≤ (5 / 2 : ℝ) * amp.D * ε_L := by
      dsimp [c₁]
      calc ‖b₁ + v₀ * a₁‖ ≤ ‖b₁‖ + ‖v₀‖ * ‖a₁‖ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul _ _).le)
        _ ≤ 2 * amp.D * ε_L + 1 * ((1 / 2 : ℝ) * ε_L) :=
            add_le_add hb1_norm (mul_le_mul hv₀_le ha1_norm (norm_nonneg _) zero_le_one)
        _ ≤ (5 / 2 : ℝ) * amp.D * ε_L := by nlinarith only [amp.hD, hεL_pos]
    have hR1_norm : ‖A₁ - (1 + a₁ * (s : ℂ))‖ ≤ (3 / 8 : ℝ) * ε_L ^ 2 * s ^ 2 := by
      have ha1s : a₁ * (s : ℂ) = (Complex.I / 2 : ℂ) * (u : ℂ) := by
        dsimp [a₁, u, τ]; push_cast; field_simp [h1s_pos.ne']
      have hu2 : u ^ 2 = (τ_sd / (1 - σ_star)) ^ 2 * s ^ 2 := by dsimp [u, τ]; ring
      rw [ha1s]
      refine hA1_rem.trans ?_
      rw [hu2]
      calc (3 / 8 : ℝ) * ((τ_sd / (1 - σ_star)) ^ 2 * s ^ 2) ≤ (3 / 8 : ℝ) * (ε_L ^ 2 * s ^ 2) := by
            gcongr
        _ = (3 / 8 : ℝ) * ε_L ^ 2 * s ^ 2 := by ring
    have hR3_norm : ‖A₃ - (v₀ + b₁ * (s : ℂ))‖ ≤ 16 * amp.D * ε_L ^ 2 * s ^ 2 := by
      have hb1s : b₁ * (s : ℂ) = V₁ * (τ : ℂ) := by dsimp [b₁, τ]; push_cast; ring
      have htd : (τ / d) ^ 2 = ε_L ^ 2 * s ^ 2 := by
        dsimp [τ]; rw [hτsd_le_epsd]; field_simp [hm_pos.ne']
      rw [hb1s]
      exact hV_rem.trans_eq (by rw [htd]; ring)
    -- Bound `‖A₁ * A₃ - (v₀ + c₁ * s)‖ ≤ 19 * amp.D * ε_L^2 * s^2`.
    have hA13_rem : ‖A₁ * A₃ - (v₀ + c₁ * (s : ℂ))‖ ≤ 19 * amp.D * ε_L ^ 2 * s ^ 2 := by
      let R₁ := A₁ - (1 + a₁ * (s : ℂ))
      let R₃ := A₃ - (v₀ + b₁ * (s : ℂ))
      have hid : A₁ * A₃ - (v₀ + c₁ * (s : ℂ)) =
          R₁ * A₃ + (1 + a₁ * (s : ℂ)) * R₃ + (a₁ * b₁) * ((s ^ 2 : ℝ) : ℂ) := by
        dsimp [R₁, R₃, c₁]; push_cast; ring
      rw [hid]
      have h1a : ‖1 + a₁ * (s : ℂ)‖ ≤ 17 / 16 := by
        have htri := norm_add_le (1 : ℂ) (a₁ * (s : ℂ))
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs] at htri
        have has : ‖a₁‖ * |s| ≤ 1 / 16 := by
          calc ‖a₁‖ * |s| ≤ ((1 / 2 : ℝ) * ε_L) * a :=
                mul_le_mul ha1_norm hs_abs (abs_nonneg s) (by positivity)
            _ = (1 / 2 : ℝ) * ε_L ^ (3 / 4 : ℝ) := by
                dsimp [a]; nth_rw 1 [← Real.rpow_one ε_L]; rw [mul_assoc, ← Real.rpow_add hεL_pos]; norm_num
            _ ≤ (1 / 2 : ℝ) * (1 / 8 : ℝ) := by gcongr
            _ = 1 / 16 := by ring
        linarith only [htri, has]
      calc ‖R₁ * A₃ + (1 + a₁ * (s : ℂ)) * R₃ + (a₁ * b₁) * ((s ^ 2 : ℝ) : ℂ)‖
          ≤ ‖R₁ * A₃‖ + ‖(1 + a₁ * (s : ℂ)) * R₃‖ + ‖(a₁ * b₁) * ((s ^ 2 : ℝ) : ℂ)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ = ‖R₁‖ * ‖A₃‖ + ‖1 + a₁ * (s : ℂ)‖ * ‖R₃‖ + (‖a₁‖ * ‖b₁‖) * |s ^ 2| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ((3 / 8 : ℝ) * ε_L ^ 2 * s ^ 2) * amp.D + (17 / 16 : ℝ) * (16 * amp.D * ε_L ^ 2 * s ^ 2) +
              (((1 / 2 : ℝ) * ε_L) * (2 * amp.D * ε_L)) * s ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg s)]
            refine add_le_add (add_le_add
              (mul_le_mul hR1_norm hA3_bd (norm_nonneg _) (by positivity))
              (mul_le_mul h1a hR3_norm (norm_nonneg _) (by positivity)))
              (mul_le_mul_of_nonneg_right (mul_le_mul ha1_norm hb1_norm (norm_nonneg _) (by positivity)) (sq_nonneg s))
        _ = (147 / 8 : ℝ) * amp.D * ε_L ^ 2 * s ^ 2 := by ring
        _ ≤ 19 * amp.D * ε_L ^ 2 * s ^ 2 := by gcongr; norm_num
    -- Combine `(A₁ * A₂ * A₃ * E) - (v₀ + OddProf)`:
    let E₀ : ℂ := (Real.exp (-s ^ 2 / 2) : ℂ)
    let E_app : ℂ := (1 + α₃ * ((s ^ 3 : ℝ) : ℂ)) * E₀
    have hid_tot : F_rel (τ_sd * s) - v₀ * E₀ - OddProf s =
        (A₁ * (A₂ - 1) * A₃ * E) +
        (A₁ * A₃ * (E - E_app)) +
        (E_app * (A₁ * A₃ - (v₀ + c₁ * (s : ℂ)))) +
        ((α₃ * ((s ^ 3 : ℝ) : ℂ) * E₀) * (c₁ * (s : ℂ))) := by
      rw [hF_fac]
      dsimp [OddProf, E_app, E₀, τ]
      ring
    have hE0_le : Real.exp (-s ^ 2 / 2) ≤ Real.exp (-s ^ 2 / 4) :=
      Real.exp_le_exp.mpr (by linarith only [sq_nonneg s])
    have hEapp_bd : ‖1 + α₃ * ((s ^ 3 : ℝ) : ℂ)‖ ≤ 11 / 2 := by
      have h18_le : 18 * ε_L ^ (1 / 4 : ℝ) ≤ 9 / 2 := by
        have h4 : (18 * ε_L ^ (1 / 4 : ℝ)) ^ 4 ≤ (9 / 2 : ℝ) ^ 4 := by
          rw [mul_pow, ← Real.rpow_natCast (ε_L ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
            show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
          nlinarith only [hεL_le_3e3]
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
      have hpow3 : |s| ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hs_abs 3
      have ha3_eq : ε_L * a ^ 3 = ε_L ^ (1 / 4 : ℝ) := by
        dsimp [a]; rw [← Real.rpow_natCast (ε_L ^ (-(1 / 4 : ℝ))) 3, ← Real.rpow_mul hεL_pos.le]
        nth_rw 1 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
      have htri := norm_add_le (1 : ℂ) (α₃ * ((s ^ 3 : ℝ) : ℂ))
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow] at htri
      calc ‖1 + α₃ * ((s ^ 3 : ℝ) : ℂ)‖ ≤ 1 + (18 * ε_L) * a ^ 3 :=
            htri.trans (add_le_add le_rfl (mul_le_mul hα3_bd hpow3 (by positivity) (by positivity)))
        _ = 1 + 18 * ε_L ^ (1 / 4 : ℝ) := by rw [mul_assoc, ha3_eq]
        _ ≤ 1 + 9 / 2 := by linarith only [h18_le]
        _ = 11 / 2 := by norm_num
    have h_p1 : ‖A₁ * (A₂ - 1) * A₃ * E‖ ≤ (1 / 5 : ℝ) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
      calc ‖A₁ * (A₂ - 1) * A₃ * E‖ = ‖A₁‖ * ‖A₂ - 1‖ * ‖A₃‖ * ‖E‖ := by simp only [norm_mul]
        _ ≤ 1 * ((1 / 5 : ℝ) * ε_L ^ 2) * amp.D * Real.exp (-s ^ 2 / 4) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul hA1_le1 hA2_rem (norm_nonneg _) zero_le_one)
              hA3_bd (norm_nonneg _) (by positivity)) (by exact hE_norm) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h_p2 : ‖A₁ * A₃ * (E - E_app)‖ ≤ (13 * s ^ 4 + 289 * s ^ 6) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
      calc ‖A₁ * A₃ * (E - E_app)‖ = ‖A₁‖ * ‖A₃‖ * ‖E - E_app‖ := by simp only [norm_mul]
        _ ≤ (1 * amp.D) * ((13 * s ^ 4 + 289 * s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4)) :=
            mul_le_mul (mul_le_mul hA1_le1 hA3_bd (norm_nonneg _) zero_le_one) (by exact hE_rem) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h_p3 : ‖E_app * (A₁ * A₃ - (v₀ + c₁ * (s : ℂ)))‖ ≤ (209 / 2 : ℝ) * amp.D * s ^ 2 * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
      have hEapp_n : ‖E_app‖ ≤ (11 / 2 : ℝ) * Real.exp (-s ^ 2 / 4) := by
        dsimp [E_app, E₀]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul hEapp_bd hE0_le (Real.exp_pos _).le (by norm_num)
      calc ‖E_app * (A₁ * A₃ - (v₀ + c₁ * (s : ℂ)))‖ = ‖E_app‖ * ‖A₁ * A₃ - (v₀ + c₁ * (s : ℂ))‖ := norm_mul _ _
        _ ≤ ((11 / 2 : ℝ) * Real.exp (-s ^ 2 / 4)) * (19 * amp.D * ε_L ^ 2 * s ^ 2) :=
            mul_le_mul hEapp_n hA13_rem (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h_p4 : ‖(α₃ * ((s ^ 3 : ℝ) : ℂ) * E₀) * (c₁ * (s : ℂ))‖ ≤ 45 * amp.D * s ^ 4 * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
      have hs4 : |s ^ 3| * |s| = s ^ 4 := by
        rw [abs_pow, ← pow_succ, show (3 : ℕ) + 1 = 2 * 2 by norm_num, pow_mul, sq_abs]
      calc ‖(α₃ * ((s ^ 3 : ℝ) : ℂ) * E₀) * (c₁ * (s : ℂ))‖
          = (‖α₃‖ * ‖c₁‖) * (|s ^ 3| * |s|) * Real.exp (-s ^ 2 / 2) := by
            dsimp [E₀]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_of_nonneg (Real.exp_pos _).le]; ring
        _ ≤ ((18 * ε_L) * ((5 / 2 : ℝ) * amp.D * ε_L)) * s ^ 4 * Real.exp (-s ^ 2 / 4) := by
            rw [hs4]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hα3_bd hc1_norm (norm_nonneg _) (by positivity)) (by positivity))
              hE0_le (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    rw [hid_tot]
    have htri := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    refine htri.trans ?_
    calc _ ≤ ((1 / 5 : ℝ) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) +
              (13 * s ^ 4 + 289 * s ^ 6) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4)) +
              (209 / 2 : ℝ) * amp.D * s ^ 2 * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) +
              45 * amp.D * s ^ 4 * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) :=
            add_le_add (add_le_add (add_le_add h_p1 h_p2) h_p3) h_p4
      _ = ((1 / 5 : ℝ) + (209 / 2 : ℝ) * s ^ 2 + 58 * s ^ 4 + 289 * s ^ 6) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by ring
      _ ≤ (289 * (1 + s ^ 2 + s ^ 4 + s ^ 6)) * amp.D * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by
          gcongr; nlinarith only [sq_nonneg s, sq_nonneg (s ^ 2), sq_nonneg (s ^ 3)]
      _ = 289 * amp.D * (1 + s ^ 2 + s ^ 4 + s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := by ring
  -- Integrate `|F_rel.re - v₀.re exp(-s^2/2)|`:
  let G_int : ℝ → ℝ := fun τ => (F_rel τ).re - v₀.re * Real.exp (-(τ / τ_sd) ^ 2 / 2)
  have hτcore_eq : τ_core = a * τ_sd := rfl
  have hcov : ∫ τ in Icc (-τ_core) τ_core, G_int τ =
      τ_sd * ∫ s in Icc (-a) a, G_int (τ_sd * s) := by
    rw [hτcore_eq, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [mul_pos ha_pos hτsd_pos]),
      ← intervalIntegral.integral_of_le (by linarith [ha_pos])]
    have hc_int := intervalIntegral.integral_comp_mul_left G_int hτsd_pos.ne' (a := -a) (b := a)
    simp_rw [show τ_sd * -a = -(a * τ_sd) by ring, show τ_sd * a = a * τ_sd by ring, smul_eq_mul] at hc_int
    rw [hc_int, ← mul_assoc, mul_inv_cancel₀ hτsd_pos.ne', one_mul]
  have hG_re_int : IntegrableOn (fun s : ℝ => G_int (τ_sd * s)) (Icc (-a) a) := by
    have h1 : Integrable (fun s : ℝ => (F_rel (τ_sd * s)).re) :=
      Complex.reCLM.integrable_comp (hFrel_int.comp_mul_left' hτsd_pos.ne')
    have h2 : Continuous (fun s : ℝ => v₀.re * Real.exp (-s ^ 2 / 2)) := by fun_prop
    refine (h1.integrableOn.sub h2.continuousOn.integrableOn_Icc).congr_fun (fun s _ => ?_) measurableSet_Icc
    dsimp [G_int]; rw [mul_div_cancel_left₀ s hτsd_pos.ne']
  have hOdd_re_int : IntegrableOn (fun s : ℝ => (OddProf s).re) (Icc (-a) a) :=
    (Complex.continuous_re.comp hOdd_cont).continuousOn.integrableOn_Icc
  have hOdd_re0 : ∫ s in Icc (-a) a, (OddProf s).re = 0 := by
    simp_rw [← Complex.reCLM_apply]
    rw [Complex.reCLM.integral_comp_comm hOdd_cont.continuousOn.integrableOn_Icc,
      hOdd_int0, Complex.reCLM_apply, Complex.zero_re]
  have h_re_sub : ∫ s in Icc (-a) a, G_int (τ_sd * s) =
      ∫ s in Icc (-a) a, (F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s).re := by
    rw [← sub_zero (∫ s in Icc (-a) a, G_int (τ_sd * s)), ← hOdd_re0,
      ← integral_sub hG_re_int hOdd_re_int]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    dsimp [G_int]
    rw [mul_div_cancel_left₀ s hτsd_pos.ne']
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hv₀_im, mul_zero, sub_zero]
  have h_re_bd : |∫ τ in Icc (-τ_core) τ_core, G_int τ| ≤
      τ_sd * (289 * 1375 * amp.D * ε_L ^ 2 * Real.sqrt (12 * π)) := by
    have hD_pos : 0 < amp.D := by linarith only [amp.hD]
    have hgauss12 : Integrable (fun s : ℝ => Real.exp (-(1 / 12 : ℝ) * s ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num)
    have hgauss12_val : ∫ s : ℝ, Real.exp (-(1 / 12 : ℝ) * s ^ 2) = Real.sqrt (12 * π) := by
      rw [integral_gaussian, show π / (1 / 12 : ℝ) = 12 * π by ring]
    have hdiff_re_int : IntegrableOn (fun s : ℝ =>
        (F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s).re) (Icc (-a) a) :=
      (hG_re_int.sub hOdd_re_int).congr_fun (fun s _ => by
        dsimp [G_int]; rw [mul_div_cancel_left₀ s hτsd_pos.ne']
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hv₀_im, mul_zero, sub_zero])
        measurableSet_Icc
    have h_abs : |∫ s in Icc (-a) a, G_int (τ_sd * s)| ≤
        289 * 1375 * amp.D * ε_L ^ 2 * Real.sqrt (12 * π) := by
      rw [h_re_sub]
      calc |∫ s in Icc (-a) a, (F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s).re|
          ≤ ∫ s in Icc (-a) a, |(F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s).re| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ s in Icc (-a) a, (289 * 1375 * amp.D * ε_L ^ 2) * Real.exp (-(1 / 12 : ℝ) * s ^ 2) := by
            refine setIntegral_mono_on hdiff_re_int.abs (hgauss12.const_mul _).integrableOn measurableSet_Icc fun s hs => ?_
            calc |(F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s).re|
                ≤ ‖F_rel (τ_sd * s) - v₀ * (Real.exp (-s ^ 2 / 2) : ℂ) - OddProf s‖ := Complex.abs_re_le_norm _
              _ ≤ 289 * amp.D * (1 + s ^ 2 + s ^ 4 + s ^ 6) * ε_L ^ 2 * Real.exp (-s ^ 2 / 4) := h_ptwise s hs
              _ = 289 * amp.D * ε_L ^ 2 * ((1 + s ^ 2 + s ^ 4 + s ^ 6) * Real.exp (-(1 / 4 : ℝ) * s ^ 2)) := by ring
              _ ≤ 289 * amp.D * ε_L ^ 2 * (1375 * Real.exp (-(1 / 12 : ℝ) * s ^ 2)) :=
                  mul_le_mul_of_nonneg_left (poly_even_exp_neg_quarter_le s) (by positivity)
              _ = _ := by ring
        _ ≤ ∫ s : ℝ, (289 * 1375 * amp.D * ε_L ^ 2) * Real.exp (-(1 / 12 : ℝ) * s ^ 2) :=
            setIntegral_le_integral (hgauss12.const_mul _) (Filter.Eventually.of_forall fun _ => by positivity)
        _ = 289 * 1375 * amp.D * ε_L ^ 2 * Real.sqrt (12 * π) := by
            rw [integral_const_mul, hgauss12_val]
    rw [hcov, abs_mul, abs_of_pos hτsd_pos]
    exact mul_le_mul_of_nonneg_left h_abs hτsd_pos.le
  -- Gaussian tail: `exp(-u/2) ≤ 384 / u^4` (`4! / (u/2)^4` via `pow_div_factorial_le_exp`), `u = ε_L^{-1/2}`.
  have h_gauss_tail : 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) ≤ τ_sd * (400 * ε_L ^ 2) := by
    let k_g := 1 / (2 * τ_sd ^ 2)
    have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
      dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
    have h_eq : (fun τ : ℝ => Real.exp (-(τ / τ_sd) ^ 2 / 2)) = fun τ => Real.exp (-k_g * τ ^ 2) := by
      ext τ; dsimp [k_g]; congr 1; field_simp [hτsd_pos.ne']
    obtain ⟨_, hbd⟩ := integral_exp_neg_div_Ioi_le (mul_pos ha_pos hτsd_pos) (by positivity : 0 < k_g)
    have ha_sq : a ^ 2 = ε_L ^ (-(1 / 2 : ℝ)) := by
      dsimp [a]; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hεL_pos.le]; norm_num
    have ha_inv : a⁻¹ = ε_L ^ (1 / 4 : ℝ) := by
      dsimp [a]; rw [← Real.rpow_neg_one, ← Real.rpow_mul hεL_pos.le]; norm_num
    let u_s : ℝ := ε_L ^ (-(1 / 2 : ℝ))
    have hu_ge : (18.25 : ℝ) ≤ u_s := le_of_sq_le_sq (by
      rw [← Real.rpow_natCast u_s 2, ← Real.rpow_mul hεL_pos.le,
        show -(1 / 2 : ℝ) * (2 : ℕ) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hεL_pos]
      linarith only [hεL_le_3e3]) (Real.rpow_nonneg hεL_pos.le _)
    have hu_pos : 0 < u_s := by linarith only [hu_ge]
    have hexp_u : Real.exp (-u_s / 2) ≤ 384 * ε_L ^ 2 := by
      have hfac := Real.pow_div_factorial_le_exp (u_s / 2) (by linarith only [hu_ge]) 4
      have hu4 : (u_s ^ 4)⁻¹ = ε_L ^ 2 := by
        dsimp [u_s]; rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hεL_pos.le,
          show -(1 / 2 : ℝ) * (4 : ℕ) = (-2 : ℝ) by norm_num, show (-2 : ℝ) = -(2 : ℕ) by norm_num,
          Real.rpow_neg hεL_pos.le, Real.rpow_natCast, inv_inv]
      have hden : (u_s / 2) ^ 4 / (Nat.factorial 4 : ℝ) = u_s ^ 4 / 384 := by
        norm_num [Nat.factorial]; ring
      rw [hden] at hfac
      rw [show -u_s / 2 = -(u_s / 2) by ring, Real.exp_neg]
      refine (inv_anti₀ (div_pos (pow_pos hu_pos 4) (by norm_num)) hfac).trans_eq ?_
      rw [inv_div, div_eq_mul_inv, hu4]
    have ha_ge2 : 2 ≤ a := by
      refine le_of_sq_le_sq ?_ (by positivity)
      rw [ha_sq]; linarith only [hu_ge]
    have h_rhs : 2 * ((1 / (2 * k_g * τ_core)) * Real.exp (-k_g * τ_core ^ 2)) =
        τ_sd * (2 * a⁻¹ * Real.exp (-u_s / 2)) := by
      have h1 : 1 / (2 * k_g * τ_core) = τ_sd * a⁻¹ := by
        dsimp [k_g, τ_core]; field_simp [hτsd_pos.ne', ha_pos.ne']
      have h2 : -k_g * τ_core ^ 2 = -u_s / 2 := by
        dsimp [k_g, τ_core]; rw [mul_pow, ha_sq]; field_simp [hτsd_pos.ne']; ring
      rw [h1, h2]; ring
    have h_int_nn : 0 ≤ ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le
    have h2 : 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) ≤
        2 * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2) := by
      nlinarith only [hv₀_le, h_int_nn]
    refine h2.trans ?_
    rw [h_eq]
    calc 2 * ∫ τ in Ioi τ_core, Real.exp (-k_g * τ ^ 2)
        ≤ 2 * ((1 / (2 * k_g * τ_core)) * Real.exp (-k_g * τ_core ^ 2)) :=
          mul_le_mul_of_nonneg_left hbd (by norm_num)
      _ = τ_sd * (2 * a⁻¹ * Real.exp (-u_s / 2)) := h_rhs
      _ ≤ τ_sd * (2 * (1 / 2 : ℝ) * (384 * ε_L ^ 2)) := by
          gcongr
          rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) ha_ge2
      _ = τ_sd * (384 * ε_L ^ 2) := by ring
      _ ≤ τ_sd * (400 * ε_L ^ 2) := by gcongr; norm_num
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have hsqrt_div : Real.sqrt (12 * π) / Real.sqrt (2 * π) = Real.sqrt 6 := by
    rw [← Real.sqrt_div (by positivity), show 12 * π / (2 * π) = 6 by field_simp [Real.pi_pos.ne']; norm_num]
  have hsqrt6 : Real.sqrt 6 ≤ 2.45 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hterm1_bd : (1 / (Real.sqrt (2 * π) * τ_sd)) * |∫ τ in Icc (-τ_core) τ_core, G_int τ| ≤
      974000 * amp.D * ε_L ^ 2 := by
    have hD_pos : 0 < amp.D := by linarith only [amp.hD]
    calc (1 / (Real.sqrt (2 * π) * τ_sd)) * |∫ τ in Icc (-τ_core) τ_core, G_int τ|
        ≤ (1 / (Real.sqrt (2 * π) * τ_sd)) * (τ_sd * (289 * 1375 * amp.D * ε_L ^ 2 * Real.sqrt (12 * π))) :=
          mul_le_mul_of_nonneg_left h_re_bd (by positivity)
      _ = 289 * 1375 * amp.D * ε_L ^ 2 * (Real.sqrt (12 * π) / Real.sqrt (2 * π)) := by
          field_simp [hτsd_pos.ne', (Real.sqrt_pos.mpr (by positivity : 0 < 2 * π)).ne']
      _ ≤ 289 * 1375 * amp.D * ε_L ^ 2 * 2.45 := by rw [hsqrt_div]; gcongr; positivity
      _ ≤ 974000 * amp.D * ε_L ^ 2 := by
          have hnn : 0 ≤ amp.D * ε_L ^ 2 := mul_nonneg (by linarith only [amp.hD]) (sq_nonneg ε_L)
          nlinarith only [hnn]
  have hterm2_bd : (1 / (Real.sqrt (2 * π) * τ_sd)) *
      (2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2)) ≤ 1000 * amp.D * ε_L ^ 2 := by
    calc (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2))
        ≤ (1 / (Real.sqrt (2 * π) * τ_sd)) * (τ_sd * (400 * ε_L ^ 2)) :=
          mul_le_mul_of_nonneg_left h_gauss_tail (by positivity)
      _ = (400 / Real.sqrt (2 * π)) * ε_L ^ 2 := by field_simp [hτsd_pos.ne']
      _ ≤ (400 / 2.506) * ε_L ^ 2 := by gcongr
      _ ≤ 1000 * 1 * ε_L ^ 2 := by gcongr; norm_num
      _ ≤ 1000 * amp.D * ε_L ^ 2 := by gcongr; exact amp.hD
  calc (1 / (Real.sqrt (2 * π) * τ_sd)) *
        (|∫ τ in Icc (-τ_core) τ_core, G_int τ| +
          2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2))
      = (1 / (Real.sqrt (2 * π) * τ_sd)) * |∫ τ in Icc (-τ_core) τ_core, G_int τ| +
        (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ‖v₀‖ * ∫ τ in Ioi τ_core, Real.exp (-(τ / τ_sd) ^ 2 / 2)) := by ring
    _ ≤ 974000 * amp.D * ε_L ^ 2 + 1000 * amp.D * ε_L ^ 2 := add_le_add hterm1_bd hterm2_bd
    _ ≤ 980000 * amp.D * ε_L ^ 2 := by
        have hnn : 0 ≤ amp.D * ε_L ^ 2 := mul_nonneg (by linarith only [amp.hD]) (sq_nonneg ε_L)
        nlinarith only [hnn]


private lemma second_order_outer_bound {Δ₁ U c Δ ξ σ_star M Λ_add : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤ min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ)))) :
    let ε_L := saddleEpsL c σ_star
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd
    let z_pos := c * (1 - σ_star)
    let ε := c ^ (-(1 / 3 : ℝ))
    let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
    let F_add := fun τ : ℝ => F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1
    IntegrableOn F_out (Ioi τ_core) ∧
    (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ ≤ 500000 * ε_L ^ 2 ∧
    (0 < Λ_add → IntegrableOn F_add (Ioi ((1 - σ_star) / 2)) ∧
      (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi ((1 - σ_star) / 2), F_add τ ≤ 150 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos)) := by
  dsimp only
  have hc60 : 60 ≤ c := by
    have := Real.one_le_rpow hU (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith [(le_max_right (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))).trans hc]
  have hc_pos : 0 < c := by linarith
  have h1s_pos : 0 < 1 - σ_star := sub_pos.mpr hσ1
  let g' := stripGDerivReal σ_star
  let ε_L := saddleEpsL c σ_star
  let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let a := ε_L ^ (-(1 / 4 : ℝ))
  let τ_core := a * τ_sd
  let z_pos := c * (1 - σ_star)
  let ε := c ^ (-(1 / 3 : ℝ))
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hεL_pos _
  have hτcore_pos : 0 < τ_core := mul_pos ha_pos hτsd_pos
  have hτsd_sq : τ_sd ^ 2 = (c * g')⁻¹ := by
    dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity)]
  obtain ⟨_, _, hz_gt⟩ := saddle_endpoint_scales hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  obtain ⟨hz_eps, hx_eps, hεL_ub⟩ := saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
  have hεL_le_3e3 : ε_L ≤ 3 / 1000 := hεL_ub.le.trans (h_eps0.trans (min_le_left _ _))
  have hεL_34_pow4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 = ε_L ^ 3 := by
    rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
      show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hεL_34_le_18 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
    have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
      rw [hεL_34_pow4]; exact (pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 3).trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
  have hεL_inv2_ge : (100000 : ℝ) ≤ ε_L ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast, inv_eq_one_div, le_div_iff₀ (pow_pos hεL_pos 2)]
    nlinarith [pow_le_pow_left₀ hεL_pos.le hεL_le_3e3 2]
  have hτcore_eq : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star) := by
    have hm := (lt_min hσ0 h1s_pos).ne'
    have h_add : ε_L ^ (-(1 / 4 : ℝ)) * ε_L = ε_L ^ (3 / 4 : ℝ) := by
      nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
    calc τ_core = (ε_L ^ (-(1 / 4 : ℝ)) * ε_L) * min σ_star (1 - σ_star) := by
          dsimp [τ_core, a, τ_sd, ε_L, saddleEpsL]; rw [mul_assoc, div_mul_cancel₀ _ hm]
      _ = _ := by rw [h_add]
  have hsqrt2pi : (2.506 : ℝ) ≤ Real.sqrt (2 * π) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [Real.pi_gt_d4, Real.pi_pos])
  have h_gauss10 : ∀ b : ℝ, τ_core ≤ b →
      (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2) ≤ 600000 * ε_L ^ 2 := by
    intro b _
    let k_10 := (1 / 10 : ℝ) * (c * g')
    obtain ⟨hint, hbd⟩ := integral_exp_neg_div_Ioi_le hτcore_pos (by positivity : 0 < k_10)
    have hm : ∫ τ in Ioc τ_core b, Real.exp (-k_10 * τ ^ 2) ≤ ∫ τ in Ioi τ_core, Real.exp (-k_10 * τ ^ 2) :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) Ioc_subset_Ioi_self.eventuallySubset
    let u_s : ℝ := ε_L ^ (-(1 / 2 : ℝ))
    have ha_sq : a ^ 2 = u_s := by
      dsimp [a, u_s]; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hεL_pos.le]; norm_num
    have hu_ge : (18.25 : ℝ) ≤ u_s := le_of_sq_le_sq (by
      rw [← Real.rpow_natCast u_s 2, ← Real.rpow_mul hεL_pos.le,
        show -(1 / 2 : ℝ) * (2 : ℕ) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hεL_pos]
      linarith only [hεL_le_3e3]) (Real.rpow_nonneg hεL_pos.le _)
    have ha_ge2 : 2 ≤ a := le_of_sq_le_sq (by rw [ha_sq]; linarith only [hu_ge]) (by positivity)
    have hexp_u : Real.exp (-u_s / 10) ≤ 240000 * ε_L ^ 2 := by
      have hu_pos : 0 < u_s := by linarith only [hu_ge]
      have hfac := Real.pow_div_factorial_le_exp (u_s / 10) (by linarith only [hu_pos]) 4
      have hu4 : (u_s ^ 4)⁻¹ = ε_L ^ 2 := by
        dsimp [u_s]; rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hεL_pos.le,
          show -(1 / 2 : ℝ) * (4 : ℕ) = (-2 : ℝ) by norm_num, show (-2 : ℝ) = -(2 : ℕ) by norm_num,
          Real.rpow_neg hεL_pos.le, Real.rpow_natCast, inv_inv]
      have hden : (u_s / 10) ^ 4 / (Nat.factorial 4 : ℝ) = u_s ^ 4 / 240000 := by
        norm_num [Nat.factorial]; ring
      rw [hden] at hfac
      rw [show -u_s / 10 = -(u_s / 10) by ring, Real.exp_neg]
      refine (inv_anti₀ (div_pos (pow_pos hu_pos 4) (by norm_num)) hfac).trans_eq ?_
      rw [inv_div, div_eq_mul_inv, hu4]
    have h_rhs : (1 / τ_sd) * ((1 / (2 * k_10 * τ_core)) * Real.exp (-k_10 * τ_core ^ 2)) =
        5 * a⁻¹ * Real.exp (-u_s / 10) := by
      have h1 : (1 / τ_sd) * (1 / (2 * k_10 * τ_core)) = 5 * a⁻¹ := by
        dsimp [k_10, τ_core]; calc _ = 5 * (c * g')⁻¹ / (a * τ_sd ^ 2) := by ring
          _ = 5 * τ_sd ^ 2 / (a * τ_sd ^ 2) := by rw [← hτsd_sq]
          _ = 5 * a⁻¹ := by field_simp [hτsd_pos.ne', ha_pos.ne']
      have h2 : -k_10 * τ_core ^ 2 = -u_s / 10 := by
        dsimp [k_10, τ_core]; rw [mul_pow, ha_sq]; calc _ = -(1 / 10) * (c * g' * τ_sd ^ 2) * u_s := by ring
          _ = -(1 / 10) * 1 * u_s := by rw [hτsd_sq, mul_inv_cancel₀ (mul_pos hc_pos hg'_pos).ne']
          _ = -u_s / 10 := by ring
      rw [← mul_assoc, h1, h2]
    rw [show (fun τ : ℝ => Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)) = fun τ => Real.exp (-k_10 * τ ^ 2) by
      ext τ; dsimp [k_10]; ring_nf]
    calc (1 / τ_sd) * ∫ τ in Ioc τ_core b, Real.exp (-k_10 * τ ^ 2)
        ≤ (1 / τ_sd) * ((1 / (2 * k_10 * τ_core)) * Real.exp (-k_10 * τ_core ^ 2)) :=
          mul_le_mul_of_nonneg_left (hm.trans hbd) (by positivity)
      _ = 5 * a⁻¹ * Real.exp (-u_s / 10) := h_rhs
      _ ≤ 5 * (1 / 2 : ℝ) * (240000 * ε_L ^ 2) := by
          gcongr; rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) ha_ge2
      _ = 600000 * ε_L ^ 2 := by ring
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  let F_add := fun τ : ℝ => F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1
  obtain ⟨hFout_int, _, h_add_spec⟩ :=
    lobe_outer_and_add_bounds (M := M) (Λ_add := Λ_add) hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq hΛ_add_half h_eps0
  obtain ⟨hA_dec, hB_dec⟩ := lobe_vertical_phase_decay_bounds (c := c) (σ_star := σ_star) (by linarith) hσ0 hσ1
  have hf_cont : Continuous F_out :=
    (Continuous.rpow (by fun_prop) continuous_const fun _ => Or.inl (by positivity)).mul
      (Real.continuous_exp.comp (continuous_const.mul
        (intervalIntegral.continuous_primitive (fun a b => (vertUpsilon_continuousIntegrand σ_star).intervalIntegrable (μ := volume) a b) 0)))
  have h_alg_le1 : ∀ τ : ℝ, (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [div_nonneg (sq_nonneg τ) (sq_nonneg (1 - σ_star))]) (by norm_num)
  have h_inv_eps2 : ∀ X : ℝ, 0 < X → ε_L ^ (-2 : ℝ) < X → X⁻¹ ≤ ε_L ^ 2 := fun X hX hlt => by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast] at hlt
    exact (inv_lt_inv₀ hlt.trans' (inv_pos.mpr (pow_pos hεL_pos 2))).mp hlt |>.le.trans_eq (inv_inv _)
  have hexp_neg_sq : ∀ (k X : ℝ), 0 < k → 0 < X → Real.exp (-k * X) ≤ 2 / (k ^ 2 * X ^ 2) := fun k X hk hX => by
    have hfac := Real.pow_div_factorial_le_exp (k * X) (by positivity) 2
    have hden : (k * X) ^ 2 / (Nat.factorial 2 : ℝ) = (k ^ 2 * X ^ 2) / 2 := by
      norm_num [Nat.factorial]; ring
    rw [hden] at hfac
    rw [show -k * X = -(k * X) by ring, Real.exp_neg]
    exact (inv_anti₀ (div_pos (by positivity) (by norm_num)) hfac).trans_eq (by rw [inv_div])
  have h_out_bd : (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ ≤ 500000 * ε_L ^ 2 := by
    rcases le_or_gt σ_star (1 / 2) with hhalf | hhalf
    · have hτcore_lt : τ_core < 1 / 2 := by
        rw [hτcore_eq]
        nlinarith only [min_le_left σ_star (1 - σ_star), hεL_34_le_18, hhalf, lt_min hσ0 h1s_pos, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
      have h_Ioc_int : IntegrableOn F_out (Ioc τ_core (1 / 2)) :=
        hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hm_eps2 : ε_L ^ (-2 : ℝ) < c * σ_star := by
        have hsq := pow_lt_pow_left₀ hx_eps (by positivity) (by decide : 2 ≠ 0)
        rw [mul_pow, ← Real.rpow_natCast ((c ^ (1 / 3 : ℝ) * σ_star) ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul (by positivity),
          show -(3 / 2 : ℝ) * (2 : ℕ) = -(3 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast] at hsq
        have h3 : (4 * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3)⁻¹ < ε_L ^ 2 := by
          rw [mul_inv, show (4 : ℝ)⁻¹ = (1 / 2 : ℝ) ^ 2 by norm_num]; exact hsq
        have h4 : 4 * (c ^ (1 / 3 : ℝ) * σ_star) ^ 3 ≤ c * σ_star := by
          have hσsq : 4 * σ_star ^ 2 ≤ 1 := by nlinarith only [hσ0, hhalf]
          rw [mul_pow, rpow_one_third_cube hc_pos]
          calc 4 * (c * σ_star ^ 3) = c * (4 * σ_star ^ 2) * σ_star := by ring
            _ ≤ c * 1 * σ_star := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσsq hc_pos.le) hσ0.le
            _ = c * σ_star := by ring
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast]
        exact (((inv_lt_inv₀ (pow_pos hεL_pos 2) (by positivity)).mpr h3).trans_eq (inv_inv _)).trans_le h4
      have hm_ge : (100000 : ℝ) ≤ c * σ_star := hεL_inv2_ge.trans hm_eps2.le
      have h_Ioi_int : IntegrableOn F_out (Ioi (1 / 2)) := by
        refine ((integral_inv_sq_Ioi (a := (1 / 2 : ℝ)) (by norm_num)).1.const_mul (Real.exp (-(3 / 160 : ℝ) * (c * σ_star)))).mono'
          hf_cont.aestronglyMeasurable ?_
        rw [ae_restrict_iff' measurableSet_Ioi]; refine Filter.Eventually.of_forall fun τ hτ => ?_
        have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)]
        have hlog1 : Real.log τ ≤ Real.log (2 * τ) := Real.log_le_log hτ0 (le_mul_of_one_le_left hτ0.le one_le_two)
        have h320 : (2 : ℝ) ≤ (3 / 20 : ℝ) * (c * σ_star) :=
          (by norm_num : (2 : ℝ) ≤ (3 / 20 : ℝ) * 100000).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num))
        have hlog : 2 * Real.log τ ≤ (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) :=
          (mul_le_mul_of_nonneg_left hlog1 (by norm_num)).trans
            (mul_le_mul_of_nonneg_right h320 (Real.log_nonneg (by linarith only [mem_Ioi.mp hτ])))
        have hid : Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) = Real.exp (-((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log τ)) := by
          rw [Real.rpow_def_of_pos hτ0, ← Real.exp_add]; congr 1; ring
        have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) := by
          rw [hid]
          exact Real.exp_le_exp.mpr (by linarith only [hA_dec.2 τ hτ, hlog])
        exact (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
      have h_part1 : (1 / τ_sd) * ∫ τ in Ioc τ_core (1 / 2), F_out τ ≤ 600000 * ε_L ^ 2 := by
        have hm := setIntegral_mono_on h_Ioc_int ((by fun_prop : Continuous fun τ : ℝ =>
            Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
          fun τ hτ => (mul_le_mul (h_alg_le1 τ) (Real.exp_le_exp.mpr (by
            linarith only [(hA_dec.1 τ ⟨hτcore_pos.trans hτ.1, hτ.2⟩)]))
            (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
        exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans (h_gauss10 (1 / 2) hτcore_lt.le)
      have h_part2 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ 100 * ε_L ^ 2 := by
        obtain ⟨hint2, hval2⟩ := integral_inv_sq_Ioi (a := (1 / 2 : ℝ)) (by norm_num)
        have hval2_eq : ∫ τ in Ioi (1 / 2 : ℝ), τ ^ (-2 : ℝ) = 2 := by linarith only [hval2]
        have hm := setIntegral_mono_on h_Ioi_int (hint2.const_mul (Real.exp (-(3 / 160 : ℝ) * (c * σ_star)))) measurableSet_Ioi fun τ hτ => by
          have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
          have hlog1 : Real.log τ ≤ Real.log (2 * τ) := Real.log_le_log hτ0 (le_mul_of_one_le_left hτ0.le one_le_two)
          have h320 : (2 : ℝ) ≤ (3 / 20 : ℝ) * (c * σ_star) :=
            (by norm_num : (2 : ℝ) ≤ (3 / 20 : ℝ) * 100000).trans (mul_le_mul_of_nonneg_left hm_ge (by norm_num))
          have hlog : 2 * Real.log τ ≤ (3 / 20 : ℝ) * (c * σ_star) * Real.log (2 * τ) :=
            (mul_le_mul_of_nonneg_left hlog1 (by norm_num)).trans
              (mul_le_mul_of_nonneg_right h320 (Real.log_nonneg (by linarith only [mem_Ioi.mp hτ])))
          have hid : Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) = Real.exp (-((3 / 160 : ℝ) * (c * σ_star) + 2 * Real.log τ)) := by
            rw [Real.rpow_def_of_pos hτ0, ← Real.exp_add]; congr 1; ring
          have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * τ ^ (-2 : ℝ) := by
            rw [hid]; exact Real.exp_le_exp.mpr (by linarith only [hA_dec.2 τ hτ, hlog])
          exact (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
        rw [integral_const_mul, hval2_eq] at hm
        have h1sd : 1 / τ_sd ≤ 2 * Real.sqrt (c * σ_star) := by
          have hg'_lt : g' < 4 * σ_star := by
            have h1 : 1 - σ_star ≥ 1 / 2 := by linarith only [hhalf]
            have h2 := (stripG_deriv_bounds hσ0 hσ1).2
            rw [← div_mul_eq_mul_div]; calc g' < 2 * σ_star / (1 - σ_star) := h2
              _ ≤ 2 * σ_star / (1 / 2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) h1
              _ = 4 * σ_star := by ring
          rw [hτsd_sq |> fun _ => rfl, show τ_sd = (c * g') ^ (-(1 / 2 : ℝ)) from rfl,
            rpow_neg_half_eq_inv_sqrt (mul_pos hc_pos hg'_pos).le, one_div, inv_inv]
          calc Real.sqrt (c * g') ≤ Real.sqrt (4 * (c * σ_star)) := Real.sqrt_le_sqrt (by nlinarith only [hg'_lt, hc_pos])
            _ = 2 * Real.sqrt (c * σ_star) := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
        have hexp_cs : Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) ≤ 2 / ((3 / 160 : ℝ) ^ 2 * (c * σ_star) ^ 2) :=
          hexp_neg_sq (3 / 160) (c * σ_star) (by norm_num) (by positivity)
        have hcs_inv2 : Real.sqrt (c * σ_star) / (c * σ_star) ^ 2 = (c * σ_star) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (c * σ_star) 2, ← Real.rpow_sub (by positivity)]; norm_num
        have hcs_bd : (c * σ_star) ^ (-(3 / 2 : ℝ)) ≤ ε_L ^ 2 * (1 / 300) := by
          have h1 : (c * σ_star)⁻¹ ≤ ε_L ^ 2 := h_inv_eps2 (c * σ_star) (by positivity) hm_eps2
          have h2 : (c * σ_star) ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt 100000 := by
            rw [rpow_neg_half_eq_inv_sqrt (by positivity), one_div]; exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt hm_ge)
          have h3 : (1 / Real.sqrt 100000 : ℝ) ≤ 1 / 300 := by
            rw [one_div, one_div]; refine inv_anti₀ (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num))
          calc (c * σ_star) ^ (-(3 / 2 : ℝ)) = (c * σ_star)⁻¹ * (c * σ_star) ^ (-(1 / 2 : ℝ)) := by
                rw [← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]; norm_num
            _ ≤ ε_L ^ 2 * (1 / 300) := mul_le_mul h1 (h2.trans h3) (by positivity) (sq_nonneg _)
        calc (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ
            ≤ (2 * Real.sqrt (c * σ_star)) * (Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * 2) :=
              mul_le_mul h1sd hm (setIntegral_nonneg measurableSet_Ioi fun _ _ => by dsimp [F_out]; positivity) (by positivity)
          _ ≤ 4 * Real.sqrt (c * σ_star) * (2 / ((3 / 160 : ℝ) ^ 2 * (c * σ_star) ^ 2)) := by
              have : 4 * Real.sqrt (c * σ_star) * Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) =
                  (2 * Real.sqrt (c * σ_star)) * (Real.exp (-(3 / 160 : ℝ) * (c * σ_star)) * 2) := by ring
              rw [← this]; exact mul_le_mul_of_nonneg_left hexp_cs (by positivity)
          _ = (8 / (3 / 160 : ℝ) ^ 2) * (Real.sqrt (c * σ_star) / (c * σ_star) ^ 2) := by ring
          _ = (8 / (3 / 160 : ℝ) ^ 2) * (c * σ_star) ^ (-(3 / 2 : ℝ)) := by rw [hcs_inv2]
          _ ≤ (8 / (3 / 160 : ℝ) ^ 2) * (ε_L ^ 2 * (1 / 300)) := by gcongr
          _ ≤ 100 * ε_L ^ 2 := by
              have : (8 / (3 / 160 : ℝ) ^ 2) * (1 / 300) ≤ 100 := by norm_num
              calc (8 / (3 / 160 : ℝ) ^ 2) * (ε_L ^ 2 * (1 / 300)) = ((8 / (3 / 160 : ℝ) ^ 2) * (1 / 300)) * ε_L ^ 2 := by ring
                _ ≤ 100 * ε_L ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have hsplit : ∫ τ in Ioi τ_core, F_out τ = (∫ τ in Ioc τ_core (1 / 2), F_out τ) + ∫ τ in Ioi (1 / 2), F_out τ := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt.le]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc_int h_Ioi_int
      calc (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ
          = (2 / Real.sqrt (2 * π)) * ((1 / τ_sd) * ∫ τ in Ioi τ_core, F_out τ) := by ring
        _ ≤ (2 / 2.506) * ((600100 : ℝ) * ε_L ^ 2) := mul_le_mul
            (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt2pi)
            (by rw [hsplit, mul_add]; linarith only [h_part1, h_part2])
            (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by dsimp [F_out]; positivity))
            (by norm_num)
        _ ≤ 500000 * ε_L ^ 2 := by
            have hnn : 0 ≤ ε_L ^ 2 := sq_nonneg _
            nlinarith only [hnn]
    · let τ₁ := (1 - σ_star) / 2
      have hτ₁_lt : τ₁ < 1 / 4 := by dsimp [τ₁]; linarith only [hhalf]
      have hτcore_lt_τ₁ : τ_core < τ₁ := by
        rw [hτcore_eq, min_eq_right (by linarith only [hhalf])]; dsimp [τ₁]
        nlinarith only [hεL_34_le_18, h1s_pos, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
      have hz_eps2 : ε_L ^ (-2 : ℝ) < 2 * z_pos := by
        have h1 := pow_lt_pow_left₀ hz_eps (by positivity) (by decide : 2 ≠ 0)
        rw [mul_pow, show (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)],
          ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), show -(1 / 2 : ℝ) * (2 : ℕ) = -1 by norm_num,
          Real.rpow_neg_one] at h1
        have h1' : (2 * (c * (1 - σ_star)))⁻¹ < ε_L ^ 2 := by rw [mul_inv, inv_eq_one_div (2 : ℝ)]; exact h1
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast]
        exact ((inv_lt_inv₀ (pow_pos hεL_pos 2) (by positivity)).mpr h1').trans_eq (inv_inv _)
      have hc_100k : (100000 : ℝ) ≤ c := by
        linarith only [show 2 * z_pos < c by dsimp [z_pos]; nlinarith only [hc_pos, hhalf], hεL_inv2_ge, hz_eps2]
      have h_Ioc1 : IntegrableOn F_out (Ioc τ_core τ₁) := hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have h_Ioc2 : IntegrableOn F_out (Ioc τ₁ (1 / 2)) := hf_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      obtain ⟨h_tail_int, h_tail_bd⟩ := integrable_log_tail (K := (3 / 40 : ℝ) * c) (by linarith only [hc_100k])
      have h_half_B : ∀ τ ∈ Ioi (1 / 2 : ℝ),
          (1 / τ_sd) * ((1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ))) ≤ Real.sqrt (2 * c) * τ ^ (-(1 / 2 : ℝ)) := fun τ hτ => by
        have hg'_lt : g' < 2 / (1 - σ_star) :=
          ((stripG_deriv_bounds hσ0 hσ1).2).trans (div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos)
        have h1 : 1 / τ_sd ≤ Real.sqrt (2 * c / (1 - σ_star)) := by
          dsimp [τ_sd]; rw [rpow_neg_half_eq_inv_sqrt (mul_pos hc_pos hg'_pos).le, one_div, inv_inv]
          exact Real.sqrt_le_sqrt (by nlinarith only [mul_lt_mul_of_pos_left hg'_lt hc_pos, show c * (2 / (1 - σ_star)) = 2 * c / (1 - σ_star) by ring])
        have h2 : (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (1 - σ_star) ^ (1 / 2 : ℝ) * τ ^ (-(1 / 2 : ℝ)) := by
          have hτ0 : 0 < τ := lt_trans (by norm_num) (mem_Ioi.mp hτ)
          have hr := Real.rpow_le_rpow_of_nonpos (z := -(1 / 4 : ℝ)) (div_pos (pow_pos hτ0 2) (pow_pos h1s_pos 2))
            (by linarith only [] : τ ^ 2 / (1 - σ_star) ^ 2 ≤ 1 + τ ^ 2 / (1 - σ_star) ^ 2) (by norm_num)
          refine hr.trans_eq ?_
          rw [Real.div_rpow (sq_nonneg τ) (sq_nonneg (1 - σ_star)), ← Real.rpow_natCast τ 2, ← Real.rpow_natCast (1 - σ_star) 2,
            ← Real.rpow_mul hτ0.le, ← Real.rpow_mul h1s_pos.le,
            show (2 : ℕ) * -(1 / 4 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg h1s_pos.le, div_eq_mul_inv, inv_inv, mul_comm]
        have h3 : Real.sqrt (2 * c / (1 - σ_star)) * (1 - σ_star) ^ (1 / 2 : ℝ) = Real.sqrt (2 * c) := by
          rw [Real.sqrt_div (by positivity), ← Real.sqrt_eq_rpow]; field_simp [(Real.sqrt_pos.mpr h1s_pos).ne']
        calc _ ≤ Real.sqrt (2 * c / (1 - σ_star)) * ((1 - σ_star) ^ (1 / 2 : ℝ) * τ ^ (-(1 / 2 : ℝ))) := mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = _ := by rw [← mul_assoc, h3]
      have h_half_mono : ∀ τ ∈ Ioi (1 / 2 : ℝ), (1 / τ_sd) * F_out τ ≤
          (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c)) *
            (τ ^ (-(1 / 2 : ℝ)) * Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ))) := fun τ hτ => by
        have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * c) * Real.exp (-((3 / 40 : ℝ) * c) * max 0 (Real.log τ)) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hB_dec.2.2 τ hτ, show 0 ≤ (3 / 320 : ℝ) * z_pos by dsimp [z_pos]; positivity])
        calc (1 / τ_sd) * F_out τ = ((1 / τ_sd) * (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ))) * Real.exp (-c * vertUpsilon σ_star τ) := by
              dsimp [F_out]; ring
          _ ≤ (Real.sqrt (2 * c) * τ ^ (-(1 / 2 : ℝ))) * _ :=
              mul_le_mul (h_half_B τ hτ) h_exp (Real.exp_pos _).le
                (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (lt_trans (by norm_num) (mem_Ioi.mp hτ)).le _))
          _ = _ := by ring
      have h_Ioi : IntegrableOn F_out (Ioi (1 / 2)) := by
        have h1 : IntegrableOn (fun τ : ℝ => (1 / τ_sd) * F_out τ) (Ioi (1 / 2)) := by
          refine (h_tail_int.const_mul (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c))).mono'
            ((continuous_const.mul hf_cont).continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
          rw [ae_restrict_iff' measurableSet_Ioi]; exact Filter.Eventually.of_forall fun τ hτ => by
            rw [Real.norm_of_nonneg (by dsimp [F_out]; positivity)]; exact h_half_mono τ hτ
        have h2 : IntegrableOn (fun τ : ℝ => τ_sd * ((1 / τ_sd) * F_out τ)) (Ioi (1 / 2)) := h1.const_mul τ_sd
        exact h2.congr_fun (fun τ _ => by field_simp [hτsd_pos.ne']) measurableSet_Ioi
      have h_part1 : (1 / τ_sd) * ∫ τ in Ioc τ_core τ₁, F_out τ ≤ 600000 * ε_L ^ 2 := by
        have hm := setIntegral_mono_on h_Ioc1 ((by fun_prop : Continuous fun τ : ℝ =>
            Real.exp (-(1 / 10 : ℝ) * (c * g') * τ ^ 2)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
          fun τ hτ => (mul_le_mul (h_alg_le1 τ) (Real.exp_le_exp.mpr (by
            linarith only [hB_dec.1 τ ⟨hτcore_pos.trans hτ.1, hτ.2⟩]))
            (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
        exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans (h_gauss10 τ₁ hτcore_lt_τ₁.le)
      have h_part2 : (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_out τ ≤ 20 * ε_L ^ 2 := by
        have hdom_int : IntegrableOn (fun τ : ℝ => Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))) (Ioc τ₁ (1 / 2)) :=
          (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hm := setIntegral_mono_on h_Ioc2 hdom_int measurableSet_Ioc fun τ hτ => by
          have h_exp : Real.exp (-c * vertUpsilon σ_star τ) ≤ Real.exp (-(3 / 320 : ℝ) * z_pos) * Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by dsimp [z_pos, τ₁]; linarith only [hB_dec.2.1 τ hτ])
          exact (mul_le_mul (h_alg_le1 τ) h_exp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
        rw [integral_const_mul] at hm
        have hm2 : ∫ τ in Ioc τ₁ (1 / 2), Real.exp (-(3 / 80 : ℝ) * c * (τ - τ₁)) ≤ 80 / (3 * c) := by
          rw [← intervalIntegral.integral_of_le (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2),
            intervalIntegral.integral_comp_sub_right (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) τ₁, sub_self,
            intervalIntegral.integral_of_le (by linarith only [hτ₁_lt])]
          obtain ⟨hl, hvl⟩ := integral_exp_neg_lin_Ioi (a := (0 : ℝ)) (k := (3 / 80 : ℝ) * c) (by positivity)
          have hvl' : ∫ u in Ioi (0 : ℝ), Real.exp (-(3 / 80 : ℝ) * c * u) = 80 / (3 * c) := by
            simpa only [mul_zero, Real.exp_zero, neg_mul] using hvl.trans (by ring)
          have hs' : IntegrableOn (fun u : ℝ => Real.exp (-(3 / 80 : ℝ) * c * u)) (Ioi 0) := by
            simpa only [neg_mul] using hl
          exact (setIntegral_mono_set hs' (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
            Ioc_subset_Ioi_self.eventuallySubset).trans_eq hvl'
        have hz_pos_pos : 0 < z_pos := by dsimp [z_pos]; positivity
        have hexp_z : Real.exp (-(3 / 320 : ℝ) * z_pos) ≤ 1 / ((3 / 320 : ℝ) * z_pos) := by
          have h1 : (3 / 320 : ℝ) * z_pos ≤ Real.exp ((3 / 320 : ℝ) * z_pos) := by
            linarith only [Real.add_one_le_exp ((3 / 320 : ℝ) * z_pos)]
          rw [show -(3 / 320 : ℝ) * z_pos = -((3 / 320 : ℝ) * z_pos) by ring, Real.exp_neg, one_div]
          exact inv_anti₀ (by positivity) h1
        have hz_inv : z_pos⁻¹ ≤ 2 * ε_L ^ 2 := by
          have h := h_inv_eps2 (2 * z_pos) (by positivity) hz_eps2
          rw [mul_inv, inv_eq_one_div, div_le_iff₀ (by positivity)] at h
          linarith only [h]
        have h_pref : 1 / (c * τ_sd) ≤ 2 * ε_L := le_of_sq_le_sq (by
          have hg'_lt : g' < 2 / (1 - σ_star) := ((stripG_deriv_bounds hσ0 hσ1).2).trans (div_lt_div_of_pos_right (by linarith only [hσ1]) h1s_pos)
          have h1 : (1 / (c * τ_sd)) ^ 2 = g' / c := by rw [div_pow, one_pow, mul_pow, hτsd_sq]; field_simp [hc_pos.ne', hg'_pos.ne']
          have h2 : g' / c < 2 / z_pos := by
            rw [show z_pos = c * (1 - σ_star) from rfl]
            exact (div_lt_div_iff₀ hc_pos (mul_pos hc_pos h1s_pos)).mpr (by nlinarith only [(lt_div_iff₀ h1s_pos).mp hg'_lt, hc_pos])
          have h3 : 2 / z_pos < (2 * ε_L) ^ 2 := by
            rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hεL_pos.le, Real.rpow_natCast,
              inv_lt_iff_one_lt_mul₀ (pow_pos hεL_pos 2)] at hz_eps2
            rw [div_lt_iff₀ (mul_pos hc_pos h1s_pos)]; nlinarith only [hz_eps2]
          linarith only [h1, h2, h3]) (by positivity)
        calc (1 / τ_sd) * ∫ τ in Ioc τ₁ (1 / 2), F_out τ
            ≤ (1 / τ_sd) * (Real.exp (-(3 / 320 : ℝ) * z_pos) * (80 / (3 * c))) :=
              mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hm2 (Real.exp_pos _).le)) (by positivity)
          _ = (1 / (c * τ_sd)) * (80 / 3 : ℝ) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
              field_simp [hc_pos.ne', hτsd_pos.ne']
          _ ≤ (2 * ε_L) * (80 / 3 : ℝ) * (320 / 3 * z_pos⁻¹) := by
              gcongr; refine hexp_z.trans_eq ?_; ring
          _ ≤ (2 * (3 / 1000 : ℝ)) * (80 / 3 : ℝ) * (320 / 3 * (2 * ε_L ^ 2)) := by gcongr
          _ ≤ 20 * ε_L ^ 2 := by
              have hnn : 0 ≤ ε_L ^ 2 := sq_nonneg _; nlinarith only [hnn]
      have h_part3 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ 100 * ε_L ^ 2 := by
        have hm1 := setIntegral_mono_on (h_Ioi.const_mul _) (h_tail_int.const_mul _) measurableSet_Ioi h_half_mono
        rw [integral_const_mul, integral_const_mul] at hm1
        have hm2 : (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ ≤ (Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c)) * 2 :=
          hm1.trans (mul_le_mul_of_nonneg_left (h_tail_bd.trans (by norm_num)) (by positivity))
        have hc_eps2 : ε_L ^ (-2 : ℝ) < c := hz_eps2.trans (by dsimp [z_pos]; nlinarith only [hc_pos, hhalf])
        have hexp_c : Real.exp (-(3 / 320 : ℝ) * c) ≤ 2 / ((3 / 320 : ℝ) ^ 2 * c ^ 2) :=
          hexp_neg_sq (3 / 320) c (by norm_num) hc_pos
        have hc_bd : c ^ (-(3 / 2 : ℝ)) ≤ ε_L ^ 2 * (1 / 300) := by
          have h1 : c⁻¹ ≤ ε_L ^ 2 := h_inv_eps2 c hc_pos hc_eps2
          have h2 : c ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt 100000 := by
            rw [rpow_neg_half_eq_inv_sqrt hc_pos.le, one_div]; exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt hc_100k)
          have h3 : (1 / Real.sqrt 100000 : ℝ) ≤ 1 / 300 := by
            rw [one_div, one_div]; refine inv_anti₀ (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num))
          calc c ^ (-(3 / 2 : ℝ)) = c⁻¹ * c ^ (-(1 / 2 : ℝ)) := by
                rw [← Real.rpow_neg_one, ← Real.rpow_add hc_pos]; norm_num
            _ ≤ ε_L ^ 2 * (1 / 300) := mul_le_mul h1 (h2.trans h3) (by positivity) (sq_nonneg _)
        have hsqrt_c : Real.sqrt (2 * c) / c ^ 2 = Real.sqrt 2 * c ^ (-(3 / 2 : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow c, ← Real.rpow_natCast c 2,
            ← Real.rpow_sub hc_pos]; norm_num; ring
        have hsq2 : Real.sqrt 2 ≤ 1.42 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        calc (1 / τ_sd) * ∫ τ in Ioi (1 / 2 : ℝ), F_out τ
            ≤ 2 * Real.sqrt (2 * c) * Real.exp (-(3 / 320 : ℝ) * c) := hm2.trans_eq (by ring)
          _ ≤ 2 * Real.sqrt (2 * c) * (2 / ((3 / 320 : ℝ) ^ 2 * c ^ 2)) :=
              mul_le_mul_of_nonneg_left hexp_c (by positivity)
          _ = (4 / (3 / 320 : ℝ) ^ 2) * (Real.sqrt (2 * c) / c ^ 2) := by ring
          _ = (4 / (3 / 320 : ℝ) ^ 2) * Real.sqrt 2 * c ^ (-(3 / 2 : ℝ)) := by rw [hsqrt_c]; ring
          _ ≤ (4 / (3 / 320 : ℝ) ^ 2) * 1.42 * (ε_L ^ 2 * (1 / 300)) := by gcongr
          _ ≤ 100 * ε_L ^ 2 := by
              have : (4 / (3 / 320 : ℝ) ^ 2) * 1.42 * (1 / 300) ≤ 100 := by norm_num
              calc _ = ((4 / (3 / 320 : ℝ) ^ 2) * 1.42 * (1 / 300)) * ε_L ^ 2 := by ring
                _ ≤ 100 * ε_L ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have h_Ioi_τ1 : IntegrableOn F_out (Ioi τ₁) := by
        rw [← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2)]; exact h_Ioc2.union h_Ioi
      have hsplit : ∫ τ in Ioi τ_core, F_out τ = (∫ τ in Ioc τ_core τ₁, F_out τ) + (∫ τ in Ioc τ₁ (1 / 2), F_out τ) + ∫ τ in Ioi (1 / 2), F_out τ := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc1 h_Ioi_τ1,
          ← Ioc_union_Ioi_eq_Ioi (by linarith only [hτ₁_lt] : τ₁ ≤ 1 / 2), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc2 h_Ioi]; ring
      calc (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ
          = (2 / Real.sqrt (2 * π)) * ((1 / τ_sd) * ∫ τ in Ioi τ_core, F_out τ) := by ring
        _ ≤ (2 / 2.506) * ((600120 : ℝ) * ε_L ^ 2) := mul_le_mul
            (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt2pi)
            (by rw [hsplit, mul_add, mul_add]; linarith only [h_part1, h_part2, h_part3])
            (mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => by dsimp [F_out]; positivity))
            (by norm_num)
        _ ≤ 500000 * ε_L ^ 2 := by
            have hnn : 0 ≤ ε_L ^ 2 := sq_nonneg _
            nlinarith only [hnn]
  exact ⟨hFout_int, h_out_bd, h_add_spec⟩

/-- **Proposition `cel:total-saddle-2` (`ce_rate.tex`):**
second-order uniform lobe saddle asymptotic for holomorphic amplitudes `V` bounded on a fixed strip disk,
without requiring `V(σ_*) ≠ 0`. -/
theorem lobe_total_saddle_second_order {Δ₁ U c Δ ξ σ_star : ℝ}
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (amp : TotalSaddleSecondOrderAmp c σ_star)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ)))) :
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
    let I_val := totalSaddleIntegral amp.V c ξ σ_star
    let z_pos := c * (1 - σ_star)
    let ε := c ^ (-(1 / 3 : ℝ))
    (mellinK0 c (σ_star : ℂ) ξ).im = 0 ∧ 0 < K₀ ∧ I_val.im = 0 ∧
      (amp.V (σ_star : ℂ)).im = 0 ∧
      |(2 * π * ξ * I_val.re) / (K₀ * Real.sqrt (2 * π) * τ_sd) - (amp.V (σ_star : ℂ)).re| ≤
        (1000000 * amp.D + 500000 * amp.Λ) * amp.A * saddleEpsL c σ_star ^ 2 +
          150 * amp.Λ_add * ε * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
  dsimp only
  have hc_pos : 0 < c := by linarith [(le_max_left _ _).trans hc]
  have hξ_pos : 0 < ξ := by rw [hξ]; exact div_pos (by linarith) hc_pos
  let g' := stripGDerivReal σ_star; let ε_L := saddleEpsL c σ_star; let τ_sd := (c * g') ^ (-(1 / 2 : ℝ))
  let τ_core := ε_L ^ (-(1 / 4 : ℝ)) * τ_sd; let ε := c ^ (-(1 / 3 : ℝ))
  let z_pos := c * (1 - σ_star); let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  have hg'_pos : 0 < g' := stripGDerivReal_pos hσ0 hσ1
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have hεL_pos : 0 < ε_L := saddleEpsL_pos hc_pos hσ0 hσ1
  have hτcore_pos : 0 < τ_core := mul_pos (Real.rpow_pos_of_pos hεL_pos _) hτsd_pos
  have hK₀_spec := mellinK0_saddle_pos hc_pos hξ_pos hσ0 hσ1
  have hK₀_pos : 0 < K₀ := hK₀_spec.2
  have hA_pos : 0 < amp.A := amp.hA
  let f := fun τ : ℝ => mellinK0 c ((σ_star : ℂ) + (τ : ℂ) * Complex.I) ξ *
    amp.V ((σ_star : ℂ) + (τ : ℂ) * Complex.I)
  have hf_int : Integrable f := totalSaddle_integrable hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp.toTotalSaddleAmp
  obtain ⟨_, h_symm, h_outer_pt⟩ := total_integrand_meas_symm_bound hc_pos hξ_pos hσ0 hσ1 amp.toTotalSaddleAmp
  have h_int_real : (∫ τ : ℝ, f τ).im = 0 := by
    have hconj : starRingEnd ℂ (∫ τ : ℝ, f τ) = ∫ τ : ℝ, f τ := by
      rw [← integral_conj]
      calc ∫ τ : ℝ, starRingEnd ℂ (f τ) = ∫ τ : ℝ, f (-τ) := integral_congr_ae (Filter.Eventually.of_forall fun τ => (h_symm τ).symm)
        _ = ∫ τ : ℝ, f τ := integral_neg_eq_self f volume
    exact Complex.conj_eq_iff_im.mp hconj
  have hI_eq : totalSaddleIntegral amp.V c ξ σ_star = ((1 / (2 * π * ξ) : ℝ) : ℂ) * ∫ τ : ℝ, f τ := rfl
  have h_Ival_im : (totalSaddleIntegral amp.V c ξ σ_star).im = 0 := by
    rw [hI_eq]; simp [Complex.mul_im, h_int_real]
  have hV_im : (amp.V (σ_star : ℂ)).im = 0 := amp.V_im_zero
  refine ⟨hK₀_spec.1, hK₀_pos, h_Ival_im, hV_im, ?_⟩
  let F_rel := fun τ : ℝ => f τ / ((K₀ * amp.A : ℝ) : ℂ)
  let v₀ : ℂ := amp.V (σ_star : ℂ) / (amp.A : ℂ)
  have hv₀_im : v₀.im = 0 := by
    dsimp [v₀]; rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hV_im]; ring
  have hv₀_re : v₀.re = (amp.V (σ_star : ℂ)).re / amp.A := by
    dsimp [v₀]; rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hV_im]; ring
  have hF_rel_int : Integrable F_rel := hf_int.div_const _
  have hI_re_eq : (totalSaddleIntegral amp.V c ξ σ_star).re = (1 / (2 * π * ξ)) * (K₀ * amp.A) * ∫ τ : ℝ, (F_rel τ).re := by
    have hf_eq : f = fun τ => ((K₀ * amp.A : ℝ) : ℂ) * F_rel τ := funext fun τ => by
      dsimp [F_rel]; rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (mul_pos hK₀_pos hA_pos).ne')]
    rw [hI_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    conv_lhs => rw [hf_eq, integral_const_mul]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hF_rel_int]
    simp [Complex.reCLM_apply]; ring
  have h_div_eq : (2 * π * ξ * (totalSaddleIntegral amp.V c ξ σ_star).re) / (K₀ * Real.sqrt (2 * π) * τ_sd) -
      (amp.V (σ_star : ℂ)).re =
      amp.A * ((1 / (Real.sqrt (2 * π) * τ_sd)) * ((∫ τ : ℝ, (F_rel τ).re) - v₀.re * (Real.sqrt (2 * π) * τ_sd))) := by
    rw [hI_re_eq, hv₀_re]
    have h1 : 2 * π * ξ ≠ 0 := by positivity
    have h2 : K₀ ≠ 0 := hK₀_pos.ne'
    have h3 : Real.sqrt (2 * π) * τ_sd ≠ 0 := by positivity
    have h4 : amp.A ≠ 0 := hA_pos.ne'
    field_simp [h1, h2, h3, h4]
  let G_g := fun τ : ℝ => Real.exp (-(τ / τ_sd) ^ 2 / 2)
  have hG_int : Integrable G_g := by
    rw [show G_g = fun τ => Real.exp (-(1 / (2 * τ_sd ^ 2)) * τ ^ 2) by ext τ; dsimp [G_g]; congr 1; field_simp [hτsd_pos.ne']]
    exact integrable_exp_neg_mul_sq (by positivity)
  have hG_val : ∫ τ : ℝ, G_g τ = Real.sqrt (2 * π) * τ_sd := by
    rw [show G_g = fun τ => Real.exp (-(1 / (2 * τ_sd ^ 2)) * τ ^ 2) by ext τ; dsimp [G_g]; congr 1; field_simp [hτsd_pos.ne'],
      integral_gaussian, show π / (1 / (2 * τ_sd ^ 2)) = (2 * π) * τ_sd ^ 2 by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hτsd_pos.le]
  let G_diff : ℝ → ℝ := fun τ => (F_rel τ).re - v₀.re * G_g τ
  have hG_diff_int : Integrable G_diff := (Complex.reCLM.integrable_comp hF_rel_int).sub (hG_int.const_mul v₀.re)
  have h_even_Iio : ∀ {g : ℝ → ℝ}, Integrable g → (∀ τ, g (-τ) = g τ) → ∫ τ in Iio (-τ_core), g τ = ∫ τ in Ioi τ_core, g τ :=
    fun {g} _ hev => by
      calc ∫ τ in Iio (-τ_core), g τ = ∫ τ in Iic (-τ_core), g τ := (integral_Iic_eq_integral_Iio).symm
        _ = ∫ τ in Iic (-τ_core), g (-τ) := setIntegral_congr_fun measurableSet_Iic fun τ _ => (hev τ).symm
        _ = ∫ τ in Ioi (- -τ_core), g τ := integral_comp_neg_Iic (-τ_core) g
        _ = ∫ τ in Ioi τ_core, g τ := by rw [neg_neg]
  have hcompl_eq : (Icc (-τ_core) τ_core)ᶜ = Iio (-τ_core) ∪ Ioi τ_core := by
    ext τ; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro h; by_cases h1 : τ < -τ_core
      · exact Or.inl h1
      · exact Or.inr (lt_of_not_ge fun h2 => h ⟨not_lt.mp h1, h2⟩)
    · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  have h_disj : Disjoint (Iio (-τ_core)) (Ioi τ_core) :=
    disjoint_iff_forall_ne.mpr fun a ha b hb => by linarith [mem_Iio.mp ha, mem_Ioi.mp hb]
  have h_compl_le : |∫ τ in (Icc (-τ_core) τ_core)ᶜ, G_diff τ| ≤
      2 * (∫ τ in Ioi τ_core, ‖F_rel τ‖) + 2 * ‖v₀‖ * (∫ τ in Ioi τ_core, G_g τ) := by
    have h_tri : |∫ τ in (Icc (-τ_core) τ_core)ᶜ, G_diff τ| ≤
        ∫ τ in (Icc (-τ_core) τ_core)ᶜ, (‖F_rel τ‖ + ‖v₀‖ * G_g τ) := by
      refine abs_integral_le_integral_abs.trans (setIntegral_mono_on hG_diff_int.integrableOn.abs
        (hF_rel_int.norm.add (hG_int.const_mul ‖v₀‖)).integrableOn measurableSet_Icc.compl fun τ _ => ?_)
      calc |G_diff τ| ≤ |(F_rel τ).re| + |v₀.re * G_g τ| := by dsimp [G_diff]; exact abs_sub _ _
        _ ≤ ‖F_rel τ‖ + ‖v₀‖ * G_g τ := by
            gcongr
            · exact Complex.abs_re_le_norm _
            · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm v₀) (Real.exp_pos _).le
    rw [integral_add hF_rel_int.norm.integrableOn (hG_int.const_mul ‖v₀‖).integrableOn, hcompl_eq,
      setIntegral_union h_disj measurableSet_Ioi hF_rel_int.norm.integrableOn hF_rel_int.norm.integrableOn,
      setIntegral_union h_disj measurableSet_Ioi (hG_int.const_mul ‖v₀‖).integrableOn (hG_int.const_mul ‖v₀‖).integrableOn,
      h_even_Iio hF_rel_int.norm (fun τ => by
        have h_symm' : f (-τ) = starRingEnd ℂ (f τ) := h_symm τ
        dsimp [F_rel]; rw [h_symm', norm_div, Complex.norm_conj, norm_div]),
      h_even_Iio (hG_int.const_mul ‖v₀‖) (fun τ => by dsimp [G_g]; simp [neg_div]),
      integral_const_mul] at h_tri
    rw [hcompl_eq]
    linarith only [h_tri]
  have h_abs_split : |(∫ τ : ℝ, (F_rel τ).re) - v₀.re * (Real.sqrt (2 * π) * τ_sd)| ≤
      (|∫ τ in Icc (-τ_core) τ_core, G_diff τ| + 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, G_g τ) +
        2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖ := by
    have heq : (∫ τ : ℝ, (F_rel τ).re) - v₀.re * (Real.sqrt (2 * π) * τ_sd) =
        (∫ τ in Icc (-τ_core) τ_core, G_diff τ) + ∫ τ in (Icc (-τ_core) τ_core)ᶜ, G_diff τ := by
      have hre_int : Integrable fun τ : ℝ => (F_rel τ).re := Complex.reCLM.integrable_comp hF_rel_int
      rw [← hG_val, ← integral_const_mul, ← integral_sub hre_int (hG_int.const_mul v₀.re)]
      exact (integral_add_compl measurableSet_Icc hG_diff_int).symm
    rw [heq]
    calc |(∫ τ in Icc (-τ_core) τ_core, G_diff τ) + ∫ τ in (Icc (-τ_core) τ_core)ᶜ, G_diff τ|
        ≤ |∫ τ in Icc (-τ_core) τ_core, G_diff τ| + |∫ τ in (Icc (-τ_core) τ_core)ᶜ, G_diff τ| := abs_add_le _ _
      _ ≤ |∫ τ in Icc (-τ_core) τ_core, G_diff τ| +
            (2 * (∫ τ in Ioi τ_core, ‖F_rel τ‖) + 2 * ‖v₀‖ * (∫ τ in Ioi τ_core, G_g τ)) :=
          add_le_add le_rfl h_compl_le
      _ = _ := by ring
  have h_core := total_core_second_order_bound hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp h_eps0
  obtain ⟨hFout_int, h_outer_bd, h_add_spec⟩ :=
    second_order_outer_bound (M := amp.M) (Λ_add := amp.Λ_add) hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp.hΛ_add_half h_eps0
  let F_out := fun τ : ℝ => (1 + τ ^ 2 / (1 - σ_star) ^ 2) ^ (-(1 / 4 : ℝ)) * Real.exp (-c * vertUpsilon σ_star τ)
  let F_add_pt := fun τ : ℝ => if (1 - σ_star) / 2 < τ then F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 else 0
  have h_F_outer_le : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) ≤
      500000 * amp.Λ * ε_L ^ 2 + 150 * amp.Λ_add * (ε / amp.A) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
    by_cases h_add : 0 < amp.Λ_add
    · obtain ⟨hFadd_int, h_add_bd⟩ := h_add_spec h_add
      have hhalf := amp.hΛ_add_half h_add
      let τ₁ := (1 - σ_star) / 2
      have hεL_34 : ε_L ^ (3 / 4 : ℝ) ≤ 1 / 8 := by
        have h4 : (ε_L ^ (3 / 4 : ℝ)) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
          rw [← Real.rpow_natCast (ε_L ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul hεL_pos.le,
            show (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
          have h_le3 : ε_L ≤ 3 / 1000 := (saddleEpsL_bounds hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq).2.2.le.trans (h_eps0.trans (min_le_left _ _))
          exact (pow_le_pow_left₀ hεL_pos.le h_le3 3).trans (by norm_num)
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h4
      have hτcore_lt_τ₁ : τ_core < τ₁ := by
        have hid : τ_core = ε_L ^ (3 / 4 : ℝ) * min σ_star (1 - σ_star) := by
          have hm := (lt_min hσ0 (sub_pos.mpr hσ1)).ne'
          have h_add : ε_L ^ (-(1 / 4 : ℝ)) * ε_L = ε_L ^ (3 / 4 : ℝ) := by
            nth_rw 2 [← Real.rpow_one ε_L]; rw [← Real.rpow_add hεL_pos]; norm_num
          calc τ_core = (ε_L ^ (-(1 / 4 : ℝ)) * ε_L) * min σ_star (1 - σ_star) := by
                dsimp [τ_core, ε_L, saddleEpsL, τ_sd]; rw [mul_assoc, div_mul_cancel₀ _ hm]
            _ = _ := by rw [h_add]
        rw [hid, min_eq_right (by linarith only [hhalf])]; dsimp [τ₁]
        nlinarith [hεL_34, sub_pos.mpr hσ1, Real.rpow_nonneg hεL_pos.le (3 / 4 : ℝ)]
      have h_add_zero : ∀ τ ∈ Ioc τ_core τ₁, F_add_pt τ = 0 := fun τ hτ => by
        dsimp [F_add_pt]; split_ifs with h <;> first | rfl | exact absurd h (not_lt.mpr (hτ.2 : τ ≤ (1 - σ_star) / 2))
      have h_add_pos : ∀ τ ∈ Ioi τ₁, F_add_pt τ = F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 := fun τ hτ => by
        dsimp [F_add_pt]; split_ifs with h <;> first | rfl | exact absurd (hτ : (1 - σ_star) / 2 < τ) h
      have hFadd_pt_Ioc : IntegrableOn F_add_pt (Ioc τ_core τ₁) :=
        integrableOn_zero.congr_fun (fun τ hτ => (h_add_zero τ hτ).symm) measurableSet_Ioc
      have hFadd_pt_Ioi : IntegrableOn F_add_pt (Ioi τ₁) :=
        hFadd_int.congr_fun (fun τ hτ => (h_add_pos τ hτ).symm) measurableSet_Ioi
      have hFadd_pt_int : IntegrableOn F_add_pt (Ioi τ_core) := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le]; exact hFadd_pt_Ioc.union hFadd_pt_Ioi
      have hFadd_pt_eq : ∫ τ in Ioi τ_core, F_add_pt τ = ∫ τ in Ioi τ₁, F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1 := by
        rw [← Ioc_union_Ioi_eq_Ioi hτcore_lt_τ₁.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hFadd_pt_Ioc hFadd_pt_Ioi,
          setIntegral_eq_zero_of_forall_eq_zero h_add_zero, zero_add,
          setIntegral_congr_fun measurableSet_Ioi h_add_pos]
      have hm := setIntegral_mono_on hF_rel_int.norm.integrableOn ((hFout_int.const_mul amp.Λ).add (hFadd_pt_int.const_mul (amp.Λ_add / amp.A)))
        measurableSet_Ioi fun τ hτ => (h_outer_pt τ (hτcore_pos.trans hτ).le).trans_eq (by dsimp [F_add_pt]; split_ifs <;> ring)
      dsimp only [Pi.add_apply] at hm
      rw [integral_add (hFout_int.const_mul _) (hFadd_pt_int.const_mul _), integral_const_mul, integral_const_mul, hFadd_pt_eq] at hm
      have hlhs : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) =
          (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, ‖F_rel τ‖ := by ring
      calc (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖)
          ≤ amp.Λ * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ) +
              (amp.Λ_add / amp.A) * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ₁, F_out τ * min (c ^ (1 / 6 : ℝ) * τ ^ (1 / 2 : ℝ)) 1) := by
            rw [hlhs]; exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
        _ ≤ amp.Λ * (500000 * ε_L ^ 2) + (amp.Λ_add / amp.A) * (150 * ε * Real.exp (-(3 / 320 : ℝ) * z_pos)) :=
            add_le_add (mul_le_mul_of_nonneg_left h_outer_bd (by linarith only [amp.hΛ]))
              (mul_le_mul_of_nonneg_left h_add_bd (div_nonneg amp.hΛ_add hA_pos.le))
        _ = _ := by ring
    · have h0 : amp.Λ_add = 0 := le_antisymm (not_lt.mp h_add) amp.hΛ_add
      have hm := setIntegral_mono_on hF_rel_int.norm.integrableOn (hFout_int.const_mul amp.Λ) measurableSet_Ioi fun τ hτ =>
        (h_outer_pt τ (hτcore_pos.trans hτ).le).trans_eq (by rw [h0]; simp; ring)
      rw [integral_const_mul] at hm
      have hlhs : (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) =
          (2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, ‖F_rel τ‖ := by ring
      calc (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖)
          ≤ amp.Λ * ((2 / (Real.sqrt (2 * π) * τ_sd)) * ∫ τ in Ioi τ_core, F_out τ) := by
            rw [hlhs]; exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
        _ ≤ amp.Λ * (500000 * ε_L ^ 2) := mul_le_mul_of_nonneg_left h_outer_bd (by linarith [amp.hΛ])
        _ = 500000 * amp.Λ * ε_L ^ 2 + 150 * amp.Λ_add * (ε / amp.A) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by rw [h0]; ring
  rw [h_div_eq, abs_mul, abs_of_pos hA_pos, abs_mul, abs_of_pos (by positivity : 0 < 1 / (Real.sqrt (2 * π) * τ_sd))]
  dsimp only at h_core
  have h1 := mul_le_mul_of_nonneg_left h_abs_split (by positivity : 0 ≤ 1 / (Real.sqrt (2 * π) * τ_sd))
  have h1' : (1 / (Real.sqrt (2 * π) * τ_sd)) * |(∫ τ : ℝ, (F_rel τ).re) - v₀.re * (Real.sqrt (2 * π) * τ_sd)| ≤
      (1 / (Real.sqrt (2 * π) * τ_sd)) * (|∫ τ in Icc (-τ_core) τ_core, G_diff τ| + 2 * ‖v₀‖ * ∫ τ in Ioi τ_core, G_g τ) +
        (1 / (Real.sqrt (2 * π) * τ_sd)) * (2 * ∫ τ in Ioi τ_core, ‖F_rel τ‖) :=
    h1.trans_eq (by ring)
  have hnorm : (1 / (Real.sqrt (2 * π) * τ_sd)) * |(∫ τ : ℝ, (F_rel τ).re) - v₀.re * (Real.sqrt (2 * π) * τ_sd)| ≤
      (1000000 * amp.D + 500000 * amp.Λ) * ε_L ^ 2 + 150 * amp.Λ_add * (ε / amp.A) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
    have hnn : 0 ≤ amp.D * ε_L ^ 2 := mul_nonneg (by linarith only [amp.hD]) (sq_nonneg _)
    linarith only [h1', h_core, h_F_outer_le, hnn]
  exact (mul_le_mul_of_nonneg_left hnorm hA_pos.le).trans_eq (by dsimp only [ε_L, ε, z_pos]; field_simp [hA_pos.ne'])

/-- info: 'FormalResearch.CohnElkies.lobe_total_saddle_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.lobe_total_saddle_second_order

end FormalResearch.CohnElkies

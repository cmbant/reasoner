module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualStrip

/-!
# `η ↓ 0` Contour Identity (`cts:cauchy-dual` Step 1, Part B)

Takes the `η ↓ 0` limit in `lowerDual_contour_eq_eta` (`LowerDualStrip`) by dominated convergence:
* `wslit_xD_identity`: the slit-to-`xT` Jacobian identity
  `y W_slit(y) (1 - y²) (π / 4) = C₀ √x (1 - e^{-4π x})² xD τ`.
* `integrableOn_Ioi_comp_xT`: `|g(c' xT²/3)| V(c' xT²/3) (2 c' xT / 3) xD ∈ L¹((0, ∞))`.
* `lowerDual_contour_eq`:
  `∫ τ in Ioi 0, (lowerDualPsi c' ε 0 g (-τ * I)).re = ∫ τ in Ioi 0, (lowerDualPsi c' ε 0 g (1 - τ * I)).re`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Saddle

noncomputable section

lemma wslit_xD_identity {τ : ℝ} (hτ : 0 < τ) :
    Real.tanh (π * τ / 4) * Wslit (Real.tanh (π * τ / 4)) *
        (1 - Real.tanh (π * τ / 4) ^ 2) * (π / 4) =
      (π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)) *
        √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ := by
  set θ : ℝ := π * τ / 4 with hθ
  set y : ℝ := Real.tanh θ with hydef
  have hpi := Real.pi_pos
  have hc_pos : 0 < Real.cosh θ := Real.cosh_pos θ
  have hsh_pos : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr (by positivity)
  have hy_pos : 0 < y := by
    rw [hydef, Real.tanh_eq_sinh_div_cosh]; exact div_pos hsh_pos hc_pos
  have hy_lt : y < 1 := Real.tanh_lt_one _
  have h1y_pos : 0 < 1 - y ^ 2 := by nlinarith
  have hu : uSlit y = Real.cosh (π * τ) := by
    rw [hydef, uSlit_tanh]; congr 1; dsimp [θ]; ring
  have hxOf_eq : xOf y = xT τ := by unfold xOf xT; rw [hu]
  have hsq_p : 1 + 6 * y ^ 2 + y ^ 4 = uSlit y * (1 - y ^ 2) ^ 2 := by
    unfold uSlit; field_simp
  have hP_pos : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
  have hsqrtP : √(1 + 6 * y ^ 2 + y ^ 4) = √(Real.cosh (π * τ)) / Real.cosh θ ^ 2 := by
    rw [hsq_p, hu, Real.sqrt_mul (Real.cosh_pos _).le, Real.sqrt_sq h1y_pos.le,
      hydef, one_sub_tanh_sq]
    ring
  have h4θ : π * τ = 4 * θ := by dsimp [θ]; ring
  have hsinh_eq : Real.sinh (π * τ) = 4 * Real.sinh θ * Real.cosh θ * Real.cosh (2 * θ) := by
    rw [h4θ, show 4 * θ = 2 * (2 * θ) by ring, Real.sinh_two_mul, Real.sinh_two_mul]; ring
  have h1cosh_eq : 1 + Real.cosh (π * τ) = 2 * Real.cosh (2 * θ) ^ 2 := by
    rw [h4θ, show 4 * θ = 2 * (2 * θ) by ring, cosh_two_mul_aux]; ring
  have hsqrt_1c : √(1 + Real.cosh (π * τ)) = √2 * Real.cosh (2 * θ) := by
    rw [h1cosh_eq, Real.sqrt_mul zero_le_two, Real.sqrt_sq (Real.cosh_pos _).le]
  have hxD_eq : xD τ = √2 * y / √(1 + 6 * y ^ 2 + y ^ 4) := by
    unfold xD
    rw [hsinh_eq, hsqrt_1c, hsqrtP, hydef, Real.tanh_eq_sinh_div_cosh]
    have hc2 : 0 < Real.cosh (2 * θ) := Real.cosh_pos _
    have hc4 : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
    field_simp
    rw [Real.sq_sqrt zero_le_two]; ring
  unfold Wslit
  rw [hxOf_eq]
  have hxi := xiStar_pos
  have hxT := xT_pos τ
  have hne_xi : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
    intro h; have := sub_eq_zero.mp h
    have : Real.exp (-(4 * π * xiStar)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  have hx_mul : √(xT τ / xiStar) = √(xT τ) / √xiStar := Real.sqrt_div hxT.le _
  rw [hx_mul, hxD_eq]
  have hs2 : (√2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsx : √xiStar ≠ 0 := (Real.sqrt_pos.mpr hxi).ne'
  have hP0 : √(1 + 6 * y ^ 2 + y ^ 4) ≠ 0 := (Real.sqrt_pos.mpr hP_pos).ne'
  field_simp

private lemma xT_mul_one_sub_tanh_sq_le (τ : ℝ) (hτ : 0 ≤ τ) :
    xT τ * (1 - Real.tanh (π * τ / 4) ^ 2) ≤ 4 * (Real.log 3 / π + 1) := by
  have hpi := Real.pi_pos
  have hx := xT_le τ
  rw [abs_of_nonneg hτ] at hx
  have h1 : 1 - Real.tanh (π * τ / 4) ^ 2 = 1 / Real.cosh (π * τ / 4) ^ 2 := one_sub_tanh_sq _
  have hch : Real.exp (π * τ / 4) / 2 ≤ Real.cosh (π * τ / 4) := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-(π * τ / 4)); linarith
  have hexp_pos : 0 < Real.exp (π * τ / 4) := Real.exp_pos _
  have h2 : 1 - Real.tanh (π * τ / 4) ^ 2 ≤ 4 * Real.exp (-(π * τ / 2)) := by
    rw [h1, one_div]
    have hsq : Real.exp (π * τ / 2) / 4 ≤ Real.cosh (π * τ / 4) ^ 2 := by
      have : (Real.exp (π * τ / 4) / 2) ^ 2 ≤ Real.cosh (π * τ / 4) ^ 2 := by gcongr
      have heq : (Real.exp (π * τ / 4) / 2) ^ 2 = Real.exp (π * τ / 2) / 4 := by
        rw [div_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
      linarith
    rw [Real.exp_neg]
    calc (Real.cosh (π * τ / 4) ^ 2)⁻¹ ≤ (Real.exp (π * τ / 2) / 4)⁻¹ :=
          inv_anti₀ (by positivity) hsq
      _ = 4 * (Real.exp (π * τ / 2))⁻¹ := by field_simp
  have htau : τ ≤ Real.exp (π * τ / 2) := by
    have h := Real.add_one_le_exp (π * τ / 2)
    have hpi2 : 2 ≤ π := by linarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_right hpi2 hτ]
  have hte : τ / 2 * Real.exp (-(π * τ / 2)) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith [Real.exp_pos (π * τ / 2)]
  have he_le1 : Real.exp (-(π * τ / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hxpos := (xT_pos τ).le
  calc xT τ * (1 - Real.tanh (π * τ / 4) ^ 2)
      ≤ (Real.log 3 / π + τ / 2) * (4 * Real.exp (-(π * τ / 2))) :=
        mul_le_mul hx h2 (by rw [one_sub_tanh_sq]; positivity) (by
          have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num); positivity)
    _ = 4 * (Real.log 3 / π * Real.exp (-(π * τ / 2)) + τ / 2 * Real.exp (-(π * τ / 2))) := by ring
    _ ≤ 4 * (Real.log 3 / π * 1 + 1 / 2) := by
        gcongr
    _ ≤ 4 * (Real.log 3 / π + 1) := by linarith

lemma integrableOn_Ioi_comp_xT {c' : ℝ} (hc' : 10000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    IntegrableOn (fun τ : ℝ =>
      |g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
        (2 * c' * xT τ / 3 * xD τ)) (Ioi 0) := by
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hV_int : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi 0) := by
    refine hg.int_cardy.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [Integration.virasoro_cardyV_eq_besselV ha (mem_Ioi.mp ht).le]
  have hV_cont : ContinuousOn (Bessel.besselV (c' / 12)) (Ici 0) :=
    (continuous_cardyV virasoroProblem (c' / 12)).continuousOn.congr fun t ht =>
      (Integration.virasoro_cardyV_eq_besselV ha (mem_Ici.mp ht)).symm
  let φ : ℝ → ℝ := fun τ => c' * xT τ ^ 2 / 3
  let φ' : ℝ → ℝ := fun τ => 2 * c' * xT τ / 3 * xD τ
  set t₀ : ℝ := φ 0 with ht₀_def
  have ht₀_pos : 0 < t₀ := by dsimp [t₀, φ]; positivity [xT_pos 0]
  have hV_Ioi : IntegrableOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (Ioi t₀) :=
    hV_int.mono_set (Ioi_subset_Ioi ht₀_pos.le)
  have hφ_cont : Continuous φ := by
    dsimp [φ]; exact ((continuous_xT_local.pow 2).const_mul c').div_const 3
  have hφ'_cont : Continuous φ' := by
    dsimp [φ']; unfold xD
    have hden : ∀ τ : ℝ, 2 * (√(Real.cosh (π * τ)) * √(1 + Real.cosh (π * τ))) ≠ 0 :=
      fun τ => by positivity [Real.cosh_pos (π * τ)]
    exact ((continuous_xT_local.const_mul (2 * c')).div_const 3).mul
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
        (continuous_const.mul ((Real.continuous_sqrt.comp (Real.continuous_cosh.comp
          (continuous_const.mul continuous_id))).mul
          (Real.continuous_sqrt.comp (continuous_const.add (Real.continuous_cosh.comp
            (continuous_const.mul continuous_id)))))) hden)
  have hcont_all : Continuous (fun τ => |g (φ τ)| * Bessel.besselV (c' / 12) (φ τ) * φ' τ) := by
    have hφ_nn : ∀ τ : ℝ, 0 ≤ φ τ := fun τ => by dsimp [φ]; positivity
    exact ((hg.cont.abs.comp_continuous hφ_cont hφ_nn).mul (hV_cont.comp_continuous hφ_cont hφ_nn)).mul
      hφ'_cont
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (∫ t in Ioi t₀, |g t| * Bessel.besselV (c' / 12) t) 0
    (fun R => (hcont_all.intervalIntegrable 0 R).1) tendsto_id ?_
  refine eventually_atTop.mpr ⟨0, fun R hR => ?_⟩
  have hd : ∀ τ ∈ uIcc (0 : ℝ) R, HasDerivAt φ (φ' τ) τ := fun τ _ => by
    dsimp [φ, φ']
    exact ((((hasDerivAt_xT τ).pow 2).const_mul c').div_const 3).congr_deriv (by ring)
  have hcont_t : ContinuousOn (fun t => |g t| * Bessel.besselV (c' / 12) t) (φ '' uIcc 0 R) := by
    have himg : φ '' uIcc 0 R ⊆ Ici 0 := by rintro t ⟨τ, _, rfl⟩; exact show 0 ≤ c' * xT τ ^ 2 / 3 by positivity
    exact (hg.cont.abs.mul hV_cont).mono himg
  have hcov := intervalIntegral.integral_comp_mul_deriv' hd hφ'_cont.continuousOn hcont_t
  dsimp only [Function.comp] at hcov
  have hnorm_eq : ∫ τ in (0 : ℝ)..R, ‖|g (φ τ)| * Bessel.besselV (c' / 12) (φ τ) * φ' τ‖ =
      ∫ τ in (0 : ℝ)..R, |g (φ τ)| * Bessel.besselV (c' / 12) (φ τ) * φ' τ := by
    refine intervalIntegral.integral_congr fun τ hτ => Real.norm_of_nonneg ?_
    rw [uIcc_of_le hR] at hτ
    have hφ_nn : 0 ≤ φ τ := by dsimp [φ]; positivity
    have hV0 : 0 ≤ Bessel.besselV (c' / 12) (φ τ) := by
      rw [← Integration.virasoro_cardyV_eq_besselV ha hφ_nn]
      exact virasoroProblem.cardyV_nonneg hshift hφ_nn
    have hφ'0 : 0 ≤ φ' τ := by
      rcases hτ.1.eq_or_lt with rfl | hτ_pos
      · dsimp [φ', xD]; simp
      · dsimp [φ']; exact mul_nonneg (by positivity [xT_pos τ]) (xD_pos τ hτ_pos).le
    exact mul_nonneg (mul_nonneg (abs_nonneg _) hV0) hφ'0
  have ht₀_le : t₀ ≤ φ R := by
    rw [ht₀_def]
    rcases hR.eq_or_lt with rfl | hR_pos
    · rfl
    · have hxlt := xT_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hR) hR_pos
      dsimp [φ]
      have hx0 := xT_pos 0
      gcongr
  rw [hnorm_eq, hcov, ← ht₀_def, intervalIntegral.integral_of_le ht₀_le]
  refine setIntegral_mono_set hV_Ioi ?_ Ioc_subset_Ioi_self.eventuallySubset
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    mul_nonneg (abs_nonneg _) (by
      rw [← Integration.virasoro_cardyV_eq_besselV ha (ht₀_pos.le.trans (mem_Ioi.mp ht).le)]
      exact virasoroProblem.cardyV_nonneg hshift (ht₀_pos.le.trans (mem_Ioi.mp ht).le))

private lemma lowerDualPsi_left_dom {c' ε : ℝ} (hc' : 10000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) (hε : 0 < ε) :
    ∃ F : ℝ → ℝ, IntegrableOn F (Ioi 0) ∧ ∀ η ∈ Ioc (0 : ℝ) 1, ∀ τ ∈ Ioi (0 : ℝ),
      ‖(lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re‖ ≤ F τ := by
  have hc0 : 0 < c' := by linarith
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  let N : ℕ := Nat.ceil c' + 2
  let C₀ : ℝ := π / (4 * √2 * √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2)
  have hC₀ : 0 < C₀ := by
    have hsub : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
      rw [sub_pos, Real.exp_lt_one_iff]; nlinarith
    dsimp [C₀]; positivity
  let Mx : ℝ := 4 * (Real.log 3 / π + 1)
  have hMx : 0 ≤ Mx := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    dsimp [Mx]; positivity
  let K : ℝ := (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * Mx) *
      (C₀ * (6 * π * √(c' / 3)) * (3 / (2 * c' * xiStar)))
  refine ⟨fun τ => K * (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
      (2 * c' * xT τ / 3 * xD τ)), (integrableOn_Ioi_comp_xT hc' hg).const_mul K, ?_⟩
  intro η hη τ hτ
  have hτ_pos : 0 < τ := mem_Ioi.mp hτ
  let y : ℝ := Real.tanh (π * τ / 4)
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨by dsimp [y]; rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _),
      Real.tanh_lt_one _⟩
  have hz_eq : sTan (-((τ : ℂ) * Complex.I)) = -Complex.I * (y : ℂ) := by
    rw [show -((τ : ℂ) * Complex.I) = ((-τ : ℝ) : ℂ) * Complex.I by push_cast; ring, sTan_I_mul,
      show π * -τ / 4 = -(π * τ / 4) by ring, Real.tanh_neg]
    push_cast; simp [y]
  have hcl : (-((τ : ℂ) * Complex.I)) ∈ unitStripCl \ {0, 1} := ⟨⟨by simp, by norm_num⟩, fun h => by
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · have := congrArg Complex.im h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this⟩
  have hzs_cl : sTan (-((τ : ℂ) * Complex.I)) ∈ closure halfDisc := (sTan_mem_cl_diff_singPts hcl).1
  have hb_eq : dualBStrip (-((τ : ℂ) * Complex.I)) = (xT τ : ℂ) := dualBStrip_imag_neg hτ_pos
  have hG_eq : hankelContinuation c' g (xT τ : ℂ) = (g (c' * xT τ ^ 2 / 3) : ℂ) :=
    hankelContinuation_ofReal hc0 hg (xT τ)
  have hΦ_norm : ‖Complex.exp (-((c' : ℂ) * dualPhi0Strip (-((τ : ℂ) * Complex.I))))‖ =
      Real.exp (c' * Bessel.besselL (xT τ)) := by
    rw [dualPhi0Strip_imag_neg hτ_pos, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.I_re, mul_zero, sub_zero, zero_mul]
    ring_nf
  have hGout_norm : ‖Gout (-Complex.I * (y : ℂ))‖ = Wslit y := by
    have hc := gout_conj_closure (slit_mem_diff hy_mem)
    rw [show starRingEnd ℂ (Complex.I * (y : ℂ)) = -Complex.I * (y : ℂ) by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]] at hc
    rw [hc, Complex.norm_conj, gout_modulus hy_mem]
  have h1z2 : (1 : ℂ) + (-Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, neg_sq, Complex.I_sq]; push_cast; ring
  have hMη : ‖lowerMt η (sTan (-((τ : ℂ) * Complex.I))) ^ N‖ ≤ (2 : ℝ) ^ N := by
    rw [norm_pow]
    have hle := (norm_lowerMt_le hη.1.le hzs_cl).trans (show 1 + η ≤ 2 by linarith [hη.2])
    exact pow_le_pow_left₀ (norm_nonneg _) hle N
  have hMε : ‖lowerMt ε (sTan (-((τ : ℂ) * Complex.I))) ^ 2‖ ≤
      (1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2) := by
    rw [norm_pow, sq]
    have hle1 := norm_lowerMt_le hε.le hzs_cl
    have hle2 := norm_lowerMt_decay hε hzs_cl
    rw [hz_eq, h1z2, Complex.norm_real, Real.norm_of_nonneg (by nlinarith [hy_mem.1, hy_mem.2])] at hle2
    rw [hz_eq]
    calc ‖lowerMt ε (-Complex.I * (y : ℂ))‖ * ‖lowerMt ε (-Complex.I * (y : ℂ))‖
        ≤ (1 + ε) * (((1 + ε) / ε) * (1 - y ^ 2)) := by
          rw [← hz_eq]; exact mul_le_mul hle1 (by rw [hz_eq]; exact hle2) (norm_nonneg _) (by positivity)
      _ = (1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2) := by ring
  have hx_gt : xiStar < xT τ := xT_gt_xiStar hτ_pos
  have hx_cmp : xiStar / 2 ≤ xT τ := by linarith
  have hbes := (Bessel.besselV_comparison hc' hx_cmp).2
  have hbes1 := (Bessel.besselV_comparison hc' hx_cmp).1
  have hV_nn : 0 ≤ Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
    rw [← Integration.virasoro_cardyV_eq_besselV (by linarith) (by positivity)]
    exact virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith) (by positivity)
  have hexp_le : √(xT τ) * Real.exp (c' * Bessel.besselL (xT τ)) ≤
      (6 * π * √(c' / 3)) * xT τ * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
    have ht_pos : 0 < c' * xT τ ^ 2 / 3 := by positivity [xT_pos τ]
    have hsq_t : √(c' * xT τ ^ 2 / 3) = √(c' / 3) * xT τ := by
      rw [show c' * xT τ ^ 2 / 3 = (c' / 3) * xT τ ^ 2 by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (xT_pos τ).le]
    by_cases hV0 : Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) = 0
    · exfalso
      rw [hV0, div_zero] at hbes1
      have : 0 < 5 * π / 3 / √(xT τ) := by positivity [Real.sqrt_pos.mpr (xT_pos τ)]
      linarith
    · have hVpos : 0 < Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := lt_of_le_of_ne hV_nn (Ne.symm hV0)
      have hmul := mul_le_mul_of_nonneg_right hbes (mul_pos (Real.sqrt_pos.mpr ht_pos) hVpos).le
      have hmul2 := mul_le_mul_of_nonneg_right hmul (Real.sqrt_pos.mpr (xT_pos τ)).le
      have : 1 / √(c' * xT τ ^ 2 / 3) * Real.exp (c' * Bessel.besselL (xT τ)) /
          Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * (√(c' * xT τ ^ 2 / 3) *
            Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) * √(xT τ) =
          √(xT τ) * Real.exp (c' * Bessel.besselL (xT τ)) := by field_simp
      rw [this] at hmul2
      calc √(xT τ) * Real.exp (c' * Bessel.besselL (xT τ))
          ≤ 6 * π / √(xT τ) * (√(c' * xT τ ^ 2 / 3) * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) *
              √(xT τ) := hmul2
        _ = 6 * π * √(c' / 3) * xT τ * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) := by
            rw [hsq_t]; field_simp [(Real.sqrt_pos.mpr (xT_pos τ)).ne']
  have hsub_sq : (1 - Real.exp (-(4 * π * xT τ))) ^ 2 ≤ 1 := by
    have h1 : 0 < Real.exp (-(4 * π * xT τ)) := Real.exp_pos _
    have h2 : Real.exp (-(4 * π * xT τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [xT_pos τ])
    nlinarith
  have hxD_le : xD τ ≤ 3 / (2 * c' * xiStar) * (2 * c' * xT τ / 3 * xD τ) := by
    have h1 : (2 * c' * xiStar / 3) * xD τ ≤ (2 * c' * xT τ / 3) * xD τ := by
      gcongr; exact (xD_pos τ hτ_pos).le
    calc xD τ = 3 / (2 * c' * xiStar) * (2 * c' * xiStar / 3 * xD τ) := by field_simp
      _ ≤ 3 / (2 * c' * xiStar) * (2 * c' * xT τ / 3 * xD τ) := by gcongr
  have hjacob := wslit_xD_identity hτ_pos
  change y * Wslit y * (1 - y ^ 2) * (π / 4) =
    C₀ * √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ at hjacob
  have h1y_nn : 0 ≤ 1 - y ^ 2 := by nlinarith [hy_mem.1, hy_mem.2]
  have hmx := xT_mul_one_sub_tanh_sq_le τ hτ_pos.le
  change xT τ * (1 - y ^ 2) ≤ Mx at hmx
  have hxD_nn : 0 ≤ xD τ := (xD_pos τ hτ_pos).le
  have hW_nn : 0 ≤ Wslit y := by rw [← hGout_norm]; exact norm_nonneg _
  calc ‖(lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re‖
      ≤ ‖lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))‖ := Complex.abs_re_le_norm _
    _ ≤ y * |g (c' * xT τ ^ 2 / 3)| * Real.exp (c' * Bessel.besselL (xT τ)) * Wslit y *
          ((1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2)) * (2 : ℝ) ^ N * ((π / 4) * (1 - y ^ 2)) := by
        unfold lowerDualPsi
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
          hb_eq, hG_eq, hz_eq, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_of_nonneg hy_mem.1.le, Complex.norm_real,
          Real.norm_eq_abs, hGout_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          h1z2, Complex.norm_real, Real.norm_of_nonneg h1y_nn]
        rw [hz_eq] at hMε hMη
        rw [hΦ_norm]
        gcongr
        · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hy_mem.1.le (abs_nonneg _))
            (Real.exp_pos _).le) hW_nn) (by positivity [h1y_nn])
        · exact mul_nonneg (mul_nonneg (mul_nonneg hy_mem.1.le (abs_nonneg _))
            (Real.exp_pos _).le) hW_nn
    _ = (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2)) *
          (|g (c' * xT τ ^ 2 / 3)| * Real.exp (c' * Bessel.besselL (xT τ)) *
            (y * Wslit y * (1 - y ^ 2) * (π / 4))) := by ring
    _ = (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2)) *
          (|g (c' * xT τ ^ 2 / 3)| * Real.exp (c' * Bessel.besselL (xT τ)) *
            (C₀ * √(xT τ) * (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ)) := by rw [hjacob]
    _ = (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2)) *
          (C₀ * |g (c' * xT τ ^ 2 / 3)| * (√(xT τ) * Real.exp (c' * Bessel.besselL (xT τ))) *
            (1 - Real.exp (-(4 * π * xT τ))) ^ 2 * xD τ) := by ring
    _ ≤ (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * (1 - y ^ 2)) *
          (C₀ * |g (c' * xT τ ^ 2 / 3)| * ((6 * π * √(c' / 3)) * xT τ *
            Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3)) * 1 * xD τ) := by
        gcongr
        exact mul_nonneg (mul_nonneg hC₀.le (abs_nonneg _))
          (mul_nonneg (mul_nonneg (by positivity) (xT_pos τ).le) hV_nn)
    _ = (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * (xT τ * (1 - y ^ 2))) *
          (C₀ * (6 * π * √(c' / 3))) *
          (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) * xD τ) := by ring
    _ ≤ (2 : ℝ) ^ N * ((1 + ε) * ((1 + ε) / ε) * Mx) *
          (C₀ * (6 * π * √(c' / 3))) *
          (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
            (3 / (2 * c' * xiStar) * (2 * c' * xT τ / 3 * xD τ))) := by
        gcongr
    _ = K * (|g (c' * xT τ ^ 2 / 3)| * Bessel.besselV (c' / 12) (c' * xT τ ^ 2 / 3) *
          (2 * c' * xT τ / 3 * xD τ)) := by dsimp [K]; ring

private lemma lowerDualPsi_right_dom {c' ε : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) (hε : 0 < ε) :
    ∃ F : ℝ → ℝ, IntegrableOn F (Ioi 0) ∧ ∀ η ∈ Ioc (0 : ℝ) 1, ∀ τ ∈ Ioi (0 : ℝ),
      ‖(lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re‖ ≤ F τ := by
  obtain ⟨C_G, hCG, hG_bd⟩ := gout_global_bound
  let M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  let N : ℕ := Nat.ceil c' + 2
  have hc0 : 0 < c' := by linarith
  have hpi := Real.pi_pos
  have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; linarith) g
  let C_R : ℝ := (4 * π * Real.exp 92 * c' ^ 2 * M) *
      (C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ)) * (((1 + ε) / ε) * 4) ^ 2 * (2 : ℝ) ^ N
  refine ⟨fun τ => C_R * Real.exp (-(7 * π / 8) * τ),
    (integrableOn_exp_mul_Ioi (by linarith : -(7 * π / 8) < 0) 0).const_mul C_R, fun η hη τ hτ => ?_⟩
  have hτ_pos : 0 < τ := mem_Ioi.mp hτ
  set s : ℂ := 1 - (τ : ℂ) * Complex.I with hsdef
  have hscl : s ∈ unitStripCl := ⟨by simp [s], by simp [s]⟩
  have hsd : s ∈ unitStripCl \ {0, 1} := ⟨hscl, fun h => by
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · have := congrArg Complex.re h; simp [s] at this
    · have := congrArg Complex.im h; simp [s] at this; linarith⟩
  have hzs_cl : sTan s ∈ closure halfDisc := (sTan_mem_cl_diff_singPts hsd).1
  have him_abs : |s.im| = τ := by simp [s, abs_of_pos hτ_pos]
  have h1 : ‖sTan s‖ ≤ 1 := (closure_halfDisc_subset (sTan_mem_closure hscl)).1
  have him_b : |(dualBStrip s).im| ≤ 1 / 2 := by
    rw [hsdef, dualBStrip_one_add_imag_neg hτ_pos]; simp
  have h2 : ‖hankelContinuation c' g (dualBStrip s)‖ ≤ 4 * π * Real.exp 92 * c' ^ 2 * M :=
    lemmaB_d_sup hc' hg him_b
  have h3 : ‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ = 1 := by
    rw [hsdef, dualPhi0Strip_one_add_imag_neg hτ_pos, Complex.norm_exp]
    simp [edgePhi0Blaschke_re_edge]
  have h1z2_pos : 0 < ‖1 + sTan s ^ 2‖ := by
    rw [norm_one_add_sTan_sq hscl]; exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (cos_ne_zero_of_cl hscl)) 2)
  have h4 : ‖Gout (sTan s) * (((π / 4 : ℝ) : ℂ) * (1 + sTan s ^ 2))‖ ≤
      C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * τ) := by
    have hgb := hG_bd (sTan s) (sTan_mem_cl_diff_singPts hsd)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hcomb : ‖1 + sTan s ^ 2‖ ^ (-(5 / 4 : ℝ)) * ‖1 + sTan s ^ 2‖ =
        (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) := by
      rw [Real.inv_rpow h1z2_pos.le, ← Real.rpow_neg h1z2_pos.le, ← Real.rpow_add_one h1z2_pos.ne']
      congr 1; norm_num
    have hinv_le := (inv_one_add_sTan_sq_norm_le hscl).trans_eq (by rw [him_abs])
    have hinv4 : (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) ≤
        (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * τ) := by
      calc (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ)
          ≤ (2 * Real.exp (π * τ / 2)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (inv_nonneg.mpr h1z2_pos.le) hinv_le (by norm_num)
        _ = (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * τ) := by
            rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
            congr 2; ring
    calc ‖Gout (sTan s)‖ * (π / 4 * ‖1 + sTan s ^ 2‖)
        ≤ (C_G * ‖1 + sTan s ^ 2‖ ^ (-(5 / 4 : ℝ))) * (π / 4 * ‖1 + sTan s ^ 2‖) := by gcongr
      _ = C_G * (π / 4) * (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) := by rw [← hcomb]; ring
      _ ≤ C_G * (π / 4) * ((2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * τ)) := by gcongr
      _ = _ := by ring
  have h5 : ‖lowerMt ε (sTan s) ^ 2‖ ≤ (((1 + ε) / ε) * 4) ^ 2 * Real.exp (-(π * τ)) := by
    rw [norm_pow]
    have hM := (norm_lowerMt_decay hε hzs_cl).trans
      (mul_le_mul_of_nonneg_left ((norm_one_add_sTan_sq_le hscl).trans_eq (by rw [him_abs])) (by positivity))
    calc ‖lowerMt ε (sTan s)‖ ^ 2
        ≤ (((1 + ε) / ε) * 4 * Real.exp (-(π * τ / 2))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hM.trans_eq (by ring)) 2
      _ = (((1 + ε) / ε) * 4) ^ 2 * Real.exp (-(π * τ)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have h6 : ‖lowerMt η (sTan s) ^ N‖ ≤ (2 : ℝ) ^ N := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_lowerMt_le hη.1.le hzs_cl).trans (by linarith [hη.2])) N
  have hexp : Real.exp (π / 8 * τ) * Real.exp (-(π * τ)) = Real.exp (-(7 * π / 8) * τ) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖(lowerDualPsi c' ε η g s).re‖ ≤ ‖lowerDualPsi c' ε η g s‖ := Complex.abs_re_le_norm _
    _ ≤ 1 * ((4 * π * Real.exp 92 * c' ^ 2 * M) * (1 *
          ((C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * τ)) *
            ((((1 + ε) / ε) * 4) ^ 2 * Real.exp (-(π * τ)) * (2 : ℝ) ^ N)))) := by
        unfold lowerDualPsi
        simp only [norm_mul]
        calc ‖sTan s‖ * ‖hankelContinuation c' g (dualBStrip s)‖ *
              ‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ * ‖Gout (sTan s)‖ *
              ‖lowerMt ε (sTan s) ^ 2‖ * ‖lowerMt η (sTan s) ^ N‖ *
              (‖((π / 4 : ℝ) : ℂ)‖ * ‖1 + sTan s ^ 2‖)
            = ‖sTan s‖ * (‖hankelContinuation c' g (dualBStrip s)‖ *
                (‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ *
                  (‖Gout (sTan s) * (((π / 4 : ℝ) : ℂ) * (1 + sTan s ^ 2))‖ *
                    (‖lowerMt ε (sTan s) ^ 2‖ * ‖lowerMt η (sTan s) ^ N‖)))) := by
              rw [norm_mul (Gout (sTan s)), norm_mul ((π / 4 : ℝ) : ℂ)]; ring
          _ ≤ _ := by rw [h3]; gcongr
    _ = C_R * (Real.exp (π / 8 * τ) * Real.exp (-(π * τ))) := by dsimp [C_R]; ring
    _ = C_R * Real.exp (-(7 * π / 8) * τ) := by rw [hexp]

private lemma tendsto_lowerDualPsi_re_edge {c' ε : ℝ} (s : ℂ) (hs : s ∈ unitStripMinusCl \ {0, 1})
    (g : ℝ → ℝ) :
    Tendsto (fun η : ℝ => (lowerDualPsi c' ε η g s).re) (𝓝[>] 0)
      (𝓝 (lowerDualPsi c' ε 0 g s).re) := by
  have h1z2 : 1 + sTan s ^ 2 ≠ 0 := by
    rw [one_add_sTan_sq ⟨hs.1.1, hs.1.2.1⟩]
    exact inv_ne_zero (pow_ne_zero 2 (cos_ne_zero_of_cl ⟨hs.1.1, hs.1.2.1⟩))
  have hm0 : lowerMt 0 (sTan s) = 1 := by unfold lowerMt; simp [h1z2]
  have hmt : Tendsto (fun η : ℝ => lowerMt η (sTan s)) (𝓝[>] 0) (𝓝 (lowerMt 0 (sTan s))) := by
    rw [hm0]
    exact tendsto_lowerMt_eta_zero h1z2
  refine Complex.continuous_re.continuousAt.tendsto.comp ?_
  unfold lowerDualPsi
  exact (((tendsto_const_nhds.mul (hmt.pow _)).mul tendsto_const_nhds).congr fun η => by ring)

/-- **Contour identity at `η = 0`** (`cts:cauchy-dual` Step 1): letting `η ↓ 0` in the
Cauchy strip identity gives equality of the left (`s = -iτ`) and right (`s = 1 - iτ`)
edge real-part integrals. -/
theorem lowerDual_contour_eq {c' ε : ℝ} (hc' : 10000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g) (hε : 0 < ε) :
    ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re =
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I)).re := by
  obtain ⟨FL, hFL_int, hFL⟩ := lowerDualPsi_left_dom hc' hg hε
  obtain ⟨FR, hFR_int, hFR⟩ := lowerDualPsi_right_dom (by linarith) hg hε
  have hcontL : ∀ η ∈ Ioc (0 : ℝ) 1, ContinuousOn
      (fun τ : ℝ => (lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re) (Ioi 0) := fun η hη => by
    refine Complex.continuous_re.comp_continuousOn ((lowerDualPsi_continuousOn (by linarith) hg hε hη.1.le).comp
      (by fun_prop : Continuous fun τ : ℝ => -((τ : ℂ) * Complex.I)).continuousOn fun τ hτ => ?_)
    exact ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩, fun h => by
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h
      · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]
      · have := congrArg Complex.re h; simp at this⟩
  have hcontR : ∀ η ∈ Ioc (0 : ℝ) 1, ContinuousOn
      (fun τ : ℝ => (lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re) (Ioi 0) := fun η hη => by
    refine Complex.continuous_re.comp_continuousOn ((lowerDualPsi_continuousOn (by linarith) hg hε hη.1.le).comp
      (by fun_prop : Continuous fun τ : ℝ => 1 - (τ : ℂ) * Complex.I).continuousOn fun τ hτ => ?_)
    exact ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩, fun h => by
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h | h
      · have := congrArg Complex.re h; simp at this
      · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]⟩
  have hTL : Tendsto (fun η : ℝ => ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re)
      (𝓝[>] 0) (𝓝 (∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (-((τ : ℂ) * Complex.I))).re)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
      (l := 𝓝[>] 0) FL ?_ ?_ hFL_int ?_
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with η hη
      exact (hcontL η hη).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with η hη
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
      exact hFL η hη τ hτ
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
      exact tendsto_lowerDualPsi_re_edge _ ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩,
        fun h => by
          simp only [mem_insert_iff, mem_singleton_iff] at h
          rcases h with h | h
          · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]
          · have := congrArg Complex.re h; simp at this⟩ g
  have hTR : Tendsto (fun η : ℝ => ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re)
      (𝓝[>] 0) (𝓝 (∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε 0 g (1 - (τ : ℂ) * Complex.I)).re)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
      (l := 𝓝[>] 0) FR ?_ ?_ hFR_int ?_
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with η hη
      exact (hcontR η hη).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with η hη
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
      exact hFR η hη τ hτ
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
      exact tendsto_lowerDualPsi_re_edge _ ⟨⟨by simp, by norm_num, by simp; exact (mem_Ioi.mp hτ).le⟩,
        fun h => by
          simp only [mem_insert_iff, mem_singleton_iff] at h
          rcases h with h | h
          · have := congrArg Complex.re h; simp at this
          · have := congrArg Complex.im h; simp at this; linarith [mem_Ioi.mp hτ]⟩ g
  have heq : (fun η : ℝ => ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re) =ᶠ[𝓝[>] 0]
      (fun η : ℝ => ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re) := by
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    exact lowerDual_contour_eq_eta (by linarith) hg hε hη
  exact tendsto_nhds_unique (hTL.congr' heq) hTR

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerDual_contour_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerDual_contour_eq

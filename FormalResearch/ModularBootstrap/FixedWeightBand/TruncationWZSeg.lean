module

public import FormalResearch.ModularBootstrap.FixedWeightBand.TruncationWZWitness

/-!
# Lemma Z at weight `w`: per-segment bound along the saddle contour

`lemma_Z_seg_bound_W` is the weight-`w` version of `Contour.lemma_Z_seg_bound`: along each segment of the
`dpConfig_spec` contour, `‖∫ mellinDensityIntegrandW ∘ ω · ω'‖ ≤ K_seg * B_seg_unit`, where the window near the
saddle `s` uses the interior bound on `tildeWW`, and the tails use Lemmas S4/S2 at weight `w`.
The Stirling^(w) prefactor is carried by the hypothesis `‖stirlingPrefW‖ ≤ P_Γ` on the segment.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

private lemma const_seg_integral_le {f : ℝ → ℂ} {a b K C_tail B_unit : ℝ}
    (hab : a ≤ b) (hba : b - a ≤ 1) (hK_nn : 0 ≤ K) (hC_nn : 0 ≤ C_tail)
    (hC_le : C_tail ≤ B_unit)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc a b))
    (hpt : ∀ τ ∈ Icc a b, ‖f τ‖ ≤ K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤ K * B_unit := by
  have hKC_nn : 0 ≤ K * C_tail := mul_nonneg hK_nn hC_nn
  have h1 : ‖∫ τ in a..b, f τ‖ ≤ ∫ τ in a..b, K * C_tail :=
    (intervalIntegral.norm_integral_le_integral_norm hab).trans
      (intervalIntegral.integral_mono_on hab (hf_cont.intervalIntegrable_of_Icc hab)
        intervalIntegrable_const hpt)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  calc ‖∫ τ in a..b, f τ‖
      ≤ (b - a) * (K * C_tail) := h1
    _ ≤ 1 * (K * C_tail) := mul_le_mul_of_nonneg_right hba hKC_nn
    _ = K * C_tail := one_mul _
    _ ≤ K * B_unit := mul_le_mul_of_nonneg_left hC_le hK_nn

private lemma ray_seg_integral_le {f : ℝ → ℂ} {d : ℝ → ℝ} {a b t_max α_g K W_pt C_tail : ℝ}
    (ha : a = 0) (hb : b = t_max) (ht_nn : 0 ≤ t_max) (ht_le1 : t_max ≤ 1)
    (_hα : 0 < α_g) (hK_nn : 0 ≤ K) (hW_nn : 0 ≤ W_pt) (hC_nn : 0 ≤ C_tail)
    (hd_cont : Continuous d)
    (hf_cont : ContinuousOn (fun τ => ‖f τ‖) (Icc 0 t_max))
    (hgauss : ∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2) ≤
      (Real.pi / 2) / Real.sqrt α_g)
    (hpt : ∀ τ ∈ Icc (0 : ℝ) t_max,
      ‖f τ‖ ≤ (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :
    ‖∫ τ in a..b, f τ‖ ≤
      K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by
  rw [ha, hb]
  have hg_cont : ContinuousOn (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2))
      (Icc 0 t_max) := by fun_prop
  have hrhs_cont : ContinuousOn
      (fun τ : ℝ => (K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail)
      (Icc 0 t_max) := hg_cont.add continuousOn_const
  have hint_le : ‖∫ τ in (0 : ℝ)..t_max, f τ‖ ≤
      ∫ τ in (0 : ℝ)..t_max,
        ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) :=
    (intervalIntegral.norm_integral_le_integral_norm ht_nn).trans
      (intervalIntegral.integral_mono_on ht_nn
        (hf_cont.intervalIntegrable_of_Icc ht_nn)
        (hrhs_cont.intervalIntegrable_of_Icc ht_nn) hpt)
  have hint_split : ∫ τ in (0 : ℝ)..t_max,
        ((K * W_pt) * Real.exp (-α_g * d τ ^ 2) + K * C_tail) =
      (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
        t_max * (K * C_tail) := by
    rw [intervalIntegral.integral_add (hg_cont.intervalIntegrable_of_Icc ht_nn)
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero]
  calc ‖∫ τ in (0 : ℝ)..t_max, f τ‖
      ≤ (K * W_pt) * (∫ τ in (0 : ℝ)..t_max, Real.exp (-α_g * d τ ^ 2)) +
          t_max * (K * C_tail) := hint_le.trans_eq hint_split
    _ ≤ (K * W_pt) * ((Real.pi / 2) / Real.sqrt α_g) + 1 * (K * C_tail) :=
        add_le_add (mul_le_mul_of_nonneg_left hgauss (mul_nonneg hK_nn hW_nn))
          (mul_le_mul_of_nonneg_right ht_le1 (mul_nonneg hK_nn hC_nn))
    _ = K * (W_pt * ((Real.pi / 2) / Real.sqrt α_g) + C_tail) := by ring

lemma lemma_Z_seg_bound_W {prob : FixedWeightProblem} {D : UniformPropositionPData prob}
    (W : ZWitnessW D) (P : ZPConfig)
    {c' Λ φ ρ κ_all ρ_min_Z M_g K_seg B_seg_unit P_Γ : ℝ}
    {g : ℝ → ℝ} {s b t u : ℂ} (S : ContourSeg)
    (hc'_pos : 0 < c') (hc'_ge1 : 1 ≤ c') (hc'_24 : max 1 (24 * prob.totalShift) ≤ c')
    (hc'_48 : stirThr prob.w / P.c_Γ ≤ c') (hc'_S4 : W.c_S4 ≤ c')
    (hΛ_nn : 0 ≤ Λ) (hsin_pos : 0 < Real.sin φ) (hρ_pos : 0 < ρ) (hs_re_pos : 0 < s.re)
    (hρ_min_pos : 0 < ρ_min_Z) (hρ_ge_min : ρ_min_Z ≤ ρ)
    (hc_ρ_sre_sq : (25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ) ≤ c' * ρ * s.re ^ 2)
    (_hκ_all_pos : 0 < κ_all)
    (hκ_ray : κ_all ≤ (P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3)
    (hκ_arc : κ_all ≤ P.κ_arc * ρ_min_Z ^ 3)
    (hκ_strip : κ_all ≤ P.κ_strip)
    (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < M_g) (hM_eq : M_g = prob.cardyNorm (c' / 12) g)
    (hb_re_pos : 0 < b.re) (hb_arg : |b.arg| < Real.pi / 4) (ht_re_pos : 0 < t.re)
    (hPΓ_pos : 0 < P_Γ)
    (hPΓ : ∀ τ ∈ Icc S.a S.b, ‖stirlingPrefW prob.w (S.ω τ) b‖ ≤ P_Γ) (ht_eq : t = (c' : ℂ) * b ^ 2 / 3)
    (ht_half_ub : ‖t ^ (-(1 / 2 : ℂ))‖ ≤ (2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)))
    (hair_eq : Real.exp (c' * (chartPhiV s b).re) = airyEnv u)
    (hK_seg_eq : K_seg = (4 * Real.sqrt 3 / xiStar) * P_Γ * P.C_d * M_g *
      c' ^ (-(1 / 2 : ℝ)) * Real.exp (-(c' * (tipL b).re)) * airyEnv u)
    (hB_seg_eq : B_seg_unit =
      (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ) *
        ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) +
      max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)))
    (hwin_wv : ∀ ζ ∈ stripClosed, ‖ζ - s‖ ≤ s.re / 4 →
      ‖tildeWW prob.w c' g ζ‖ ≤ M_g * (2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ))
    (hS2_P : ∀ {ω : ℂ}, P.μ₀ ≤ ω.re →
      ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * ω)‖ ≤
        W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB ω) * M_g)
    (hba : S.b - S.a ≤ 1)
    (hω_bd : ∀ τ ∈ Icc S.a S.b,
      0 ≤ (S.ω τ).re ∧ P.c_Γ ≤ ‖S.ω τ‖ ∧ ‖S.ω τ‖ ≤ P.C_Γ ∧ ‖S.ω' τ‖ ≤ P.C_d)
    (h_ur : S.isStrip = true → S.kind = .upperRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = t_max - τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * (t_max - τ) ^ 2)
    (h_lr : S.isStrip = true → S.kind = .lowerRay →
      ∃ t_max ≥ (0 : ℝ), S.a = 0 ∧ S.b = t_max ∧ t_max ≤ 11 * ρ ∧
        ∀ τ ∈ Icc 0 t_max, ‖S.ζ τ - s‖ = τ ∧ ‖S.ζ' τ‖ = 1 ∧
          (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * τ ^ 2)
    (h_ar : S.isStrip = true → S.kind = .arcRadial →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_arc * ρ ^ 3)
    (h_fs : S.isStrip = true → S.kind = .fixedStrip →
      ∀ τ ∈ Icc S.a S.b, (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.κ_strip)
    (hnonstrip : S.isStrip = false → ∀ τ ∈ Icc S.a S.b,
      P.μ₀ ≤ (S.ω τ).re ∧ crudeExponentEc (S.ω τ) b ≤ (chartPhiV s b).re - P.c_γ * ρ * s.re ^ 2)
    (h_no_crude : S.isStrip = true → S.kind ≠ .crudeEdge) :
    ‖∫ τ in S.a..S.b, mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖ ≤
      K_seg * B_seg_unit := by
  have hK_seg_pos : 0 < K_seg := by
    rw [hK_seg_eq]
    have := xiStar_pos; have := P.hC_d_pos; have := airyEnv_pos u; positivity
  have hKM_nn : 0 ≤ K_seg / M_g := div_nonneg hK_seg_pos.le hM_pos.le
  have hCS_max_pos : 0 < max W.C_S4 W.C_S2 := lt_of_lt_of_le W.hCS4 (le_max_left _ _)
  set C_tail_u : ℝ := max W.C_S4 W.C_S2 * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))
  have hC_tail_nn : 0 ≤ C_tail_u := mul_nonneg hCS_max_pos.le (Real.exp_pos _).le
  set W_pt : ℝ := 2 * Λ * c' ^ (-(5 / 6 : ℝ)) / Real.sin φ
  have hW_pt_nn : 0 ≤ W_pt := by dsimp [W_pt]; positivity
  have hwin_term_nn : 0 ≤ W_pt * ((Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) := by
    have := P.hc_γ_pos; positivity
  have hC_tail_le_B : C_tail_u ≤ B_seg_unit := by
    rw [hB_seg_eq]; dsimp [W_pt, C_tail_u]; linarith only [hwin_term_nn]
  have hc56_le_c : c' ^ (5 / 6 : ℝ) ≤ c' :=
    (Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num)).trans_eq (Real.rpow_one c')
  have hstrip_mul_le : ∀ {A B E₁ E₂ : ℝ}, 0 ≤ B → A ≤ B → 0 ≤ E₁ → E₁ ≤ E₂ →
      (K_seg / M_g) * A * E₁ ≤ (K_seg / M_g) * B * E₂ := fun hB hAB hE1 hE =>
    mul_le_mul (mul_le_mul_of_nonneg_left hAB hKM_nn) hE hE1 (mul_nonneg hKM_nn hB)
  have hcont_seg : ContinuousOn (fun τ => mellinDensityIntegrandW prob.w c' g t (S.ω τ))
      (Icc S.a S.b) := by
    intro τ hτ
    have hω_re_nn := (hω_bd τ hτ).1
    have hz_re : 0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ).re :=
      re_wHalf_add_mul_pos prob.hw hc'_pos.le hω_re_nn
    have hGam_d : DifferentiableAt ℂ Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ) :=
      Complex.differentiableAt_Gamma _ (fun m hm => by
        have hrm := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at hrm
        linarith only [hz_re, hrm, Nat.cast_nonneg (α := ℝ) m])
    have h_an_w : DifferentiableAt ℂ (mellinDensityIntegrandW prob.w c' g t) (S.ω τ) := by
      have hm_d := (testClass_differentiable_mellinMGEntireW prob hc'_24 hg).differentiableAt
        (x := (prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ)
      have ht_ne : (2 * (Real.pi : ℂ) * t) ≠ 0 := by
        have ht0 : t ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at ht_re_pos; exact lt_irrefl 0 ht_re_pos
        exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht0
      have hlin : DifferentiableAt ℂ (fun ω : ℂ => (prob.w : ℂ) / 2 + (c' : ℂ) * ω) (S.ω τ) := by
        fun_prop
      have hp_d : DifferentiableAt ℂ (fun ω : ℂ =>
          (2 * (Real.pi : ℂ) * t) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) (S.ω τ) := by
        have hex : (fun ω : ℂ => (2 * (Real.pi : ℂ) * t) ^ (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) =
            fun ω => Complex.exp (Complex.log (2 * (Real.pi : ℂ) * t) *
              (-((prob.w : ℂ) / 2 + (c' : ℂ) * ω))) := by
          ext ω; rw [Complex.cpow_def_of_ne_zero ht_ne]
        rw [hex]; fun_prop
      have h1 := DifferentiableAt.comp (g := Complex.Gamma) (S.ω τ) hGam_d hlin
      have h2 := DifferentiableAt.comp (g := mellinMGEntireW prob.w g) (S.ω τ) hm_d hlin
      exact (h1.mul hp_d).mul h2
    exact h_an_w.continuousAt.comp_continuousWithinAt (S.hω_cont τ hτ)
  have hf_cont : ContinuousOn
      (fun τ => ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖) (Icc S.a S.b) :=
    (hcont_seg.mul S.hω'_cont).norm
  have hcω_all : ∀ τ ∈ Icc S.a S.b, stirThr prob.w ≤ c' * ‖S.ω τ‖ := fun τ hτ =>
    ((div_le_iff₀ P.hc_Γ_pos).mp hc'_48).trans
      (mul_le_mul_of_nonneg_left (hω_bd τ hτ).2.1 hc'_pos.le)
  have hω_ne_all : ∀ τ ∈ Icc S.a S.b, S.ω τ ≠ 0 := fun τ hτ h0 => by
    have h1 := hcω_all τ hτ
    rw [h0, norm_zero, mul_zero] at h1
    linarith only [h1, stirThr_pos prob.w]
  have hpt_stirling : ∀ τ ∈ Icc S.a S.b,
      let ω := S.ω τ
      0 < ((prob.w : ℂ) / 2 + (c' : ℂ) * ω).re ∧
      ‖stirlingSW prob.w c' ω‖ ≤ 2 ∧
      mellinDensityIntegrandW prob.w c' g t ω =
        stirlingPrefW prob.w ω b * t ^ (-(1 / 2 : ℂ)) * stirlingSW prob.w c' ω *
          Complex.exp ((c' : ℂ) * ComplexBessel.stirlingJ ω b) *
          mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * ω) := fun τ hτ => by
    obtain ⟨hω_re, _, _, _⟩ := hω_bd τ hτ
    refine ⟨re_wHalf_add_mul_pos prob.hw hc'_pos.le hω_re,
      (norm_stirlingSW_le_two_of_stirThr_le prob.hw hc'_pos hω_re (hcω_all τ hτ)).1, ?_⟩
    rw [ht_eq]
    exact mellinDensityIntegrandW_crude_eq prob.hw hc'_pos g hω_re (hω_ne_all τ hτ) hb_re_pos hb_arg
  have hpt_strip_prod : ∀ (hstr : S.isStrip = true), ∀ τ ∈ Icc S.a S.b,
      ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖ ≤
        (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
    intro hstr τ hτ
    obtain ⟨_, hS_bd, _⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    have hω_ζ := (S.hζ_strip hstr τ hτ).2.2.1
    have hpref := hPΓ τ hτ
    have hω_re := (hω_bd τ hτ).1
    have hω_ne := hω_ne_all τ hτ
    have hstrip_id : mellinDensityIntegrandW prob.w c' g t (S.ω τ) =
        stirlingPrefW prob.w (S.ω τ) b * t ^ (-(1 / 2 : ℂ)) * stirlingSW prob.w c' (S.ω τ) *
          Complex.exp ((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b) *
          tildeWW prob.w c' g (S.ζ τ) := by
      rw [ht_eq]
      rw [hω_ζ] at hω_re hω_ne ⊢
      exact mellinDensityIntegrandW_strip_eq prob.hw hc'_pos g hω_re hω_ne hb_re_pos hb_arg
    rw [norm_mul, hstrip_id, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    have hexp_eq : Real.exp (((c' : ℂ) * chartPhiV (S.ζ τ) b - (c' : ℂ) * tipL b).re) =
        Real.exp (-(c' * (tipL b).re)) * airyEnv u *
          Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
      rw [← hair_eq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Complex.sub_re, Complex.re_ofReal_mul]
      ring
    rw [hexp_eq]
    calc ‖stirlingPrefW prob.w (S.ω τ) b‖ * ‖t ^ (-(1 / 2 : ℂ))‖ *
            ‖stirlingSW prob.w c' (S.ω τ)‖ *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWW prob.w c' g (S.ζ τ)‖ * ‖S.ω' τ‖
        ≤ (P_Γ * ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)))) * 2 *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))) *
            ‖tildeWW prob.w c' g (S.ζ τ)‖ * P.C_d := by
          have := xiStar_pos; have := airyEnv_pos u; gcongr
      _ = (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
            Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) := by
          rw [hK_seg_eq]; field_simp [hM_pos.ne']; ring
  -- Unified ray case handler for `.upperRay` (`d τ = t_max - τ`) and `.lowerRay` (`d τ = τ`)
  have hray_unified : ∀ (hstr : S.isStrip = true) (t_max : ℝ) (ht_nn : 0 ≤ t_max)
      (ha_eq : S.a = 0) (hb_eq_t : S.b = t_max) (d : ℝ → ℝ),
      Continuous d →
      (∫ τ in (0 : ℝ)..t_max, Real.exp (-(c' * P.c_γ * ρ) * d τ ^ 2) ≤
        (Real.pi / 2) / Real.sqrt (c' * P.c_γ * ρ)) →
      (∀ τ ∈ Icc (0 : ℝ) t_max, ‖S.ζ τ - s‖ = d τ ∧
        (chartPhiV (S.ζ τ) b).re ≤ (chartPhiV s b).re - P.c_γ * ρ * d τ ^ 2) →
      ‖∫ τ in S.a..S.b, mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖ ≤
        K_seg * B_seg_unit := by
    intro hstr t_max ht_nn ha_eq hb_eq_t d hd_cont hgauss hray_d
    set α_g : ℝ := c' * P.c_γ * ρ
    have hα_g_pos : 0 < α_g := mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos
    have hpt_ray : ∀ τ ∈ Icc (0 : ℝ) t_max,
        ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖ ≤
          (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) + K_seg * C_tail_u := by
      intro τ hτ
      have hτ' : τ ∈ Icc S.a S.b := by rwa [ha_eq, hb_eq_t]
      have hbase := hpt_strip_prod hstr τ hτ'
      obtain ⟨hdist_eq, hphi_bd⟩ := hray_d τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ'
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hexp_gauss : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-α_g * d τ ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤
            -P.c_γ * ρ * d τ ^ 2 := by linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        dsimp [α_g]; linarith only [hm]
      by_cases hwin : d τ ≤ s.re / 4
      · have hdist_win : ‖S.ζ τ - s‖ ≤ s.re / 4 := hdist_eq.trans_le hwin
        have hwv := hwin_wv (S.ζ τ) hζ_cl hdist_win
        have h1 : (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by
          calc (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (M_g * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
                hstrip_mul_le (mul_nonneg hM_pos.le hW_pt_nn) hwv (Real.exp_pos _).le hexp_gauss
            _ = (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) := by
                field_simp [hM_pos.ne']
        have hct_nn : 0 ≤ K_seg * C_tail_u := mul_nonneg hK_seg_pos.le hC_tail_nn
        linarith only [hbase, h1, hct_nn]
      · have hgt : s.re / 4 ≤ d τ := le_of_not_ge hwin
        have hsq_ge : (s.re / 4) ^ 2 ≤ d τ ^ 2 :=
          pow_le_pow_left₀ (div_nonneg hs_re_pos.le (by norm_num)) hgt 2
        have hexp_tail : Real.exp (-α_g * d τ ^ 2) ≤
            Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : κ_all * c' ^ (5 / 6 : ℝ) ≤ α_g * (s.re / 4) ^ 2 := by
            have hcγ_nn := (div_pos P.hc_γ_pos (by norm_num : (0 : ℝ) < 16)).le
            calc κ_all * c' ^ (5 / 6 : ℝ)
                ≤ ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ) :=
                  mul_le_mul_of_nonneg_right hκ_ray (Real.rpow_nonneg hc'_pos.le _)
              _ = (P.c_γ / 16) * ((25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)) := by ring
              _ ≤ (P.c_γ / 16) * (c' * ρ * s.re ^ 2) :=
                  mul_le_mul_of_nonneg_left hc_ρ_sre_sq hcγ_nn
              _ = α_g * (s.re / 4) ^ 2 := by dsimp [α_g]; ring
          have h2 : α_g * (s.re / 4) ^ 2 ≤ α_g * d τ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq_ge hα_g_pos.le
          linarith only [h1, h2]
        have hwv_s4 : ‖tildeWW prob.w c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
          have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
          rw [← hM_eq] at h0
          exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
        have h1 : (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
              Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
            K_seg * C_tail_u := by
          calc (K_seg / M_g) * ‖tildeWW prob.w c' g (S.ζ τ)‖ *
                  Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re))
              ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
                  Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
                hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
                  (Real.exp_pos _).le (hexp_gauss.trans hexp_tail)
            _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
        have hcw_nn : 0 ≤ (K_seg * W_pt) * Real.exp (-α_g * d τ ^ 2) :=
          mul_nonneg (mul_nonneg hK_seg_pos.le hW_pt_nn) (Real.exp_pos _).le
        linarith only [hbase, h1, hcw_nn]
    have hf_cont0 : ContinuousOn
        (fun τ => ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖) (Icc 0 t_max) := by
      rwa [← ha_eq, ← hb_eq_t]
    have ht_le1 : t_max ≤ 1 := by
      have h1 := hba; rw [ha_eq, hb_eq_t, sub_zero] at h1; exact h1
    have hres := ray_seg_integral_le ha_eq hb_eq_t ht_nn ht_le1 hα_g_pos
      hK_seg_pos.le hW_pt_nn hC_tail_nn hd_cont hf_cont0 hgauss hpt_ray
    rwa [← hB_seg_eq] at hres
  cases hstr : S.isStrip
  · -- `S.isStrip = false`: crude left-edge piece (`lemma_S2`)
    refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
    intro τ hτ
    obtain ⟨_, hS_bd, hmel_eq⟩ := hpt_stirling τ hτ
    have hω'_bd := (hω_bd τ hτ).2.2.2
    obtain ⟨hμ₀_le, hEc_le⟩ := hnonstrip hstr τ hτ
    have hS2_bd := hS2_P hμ₀_le
    rw [norm_mul, hmel_eq, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_exp,
      Complex.re_ofReal_mul]
    have hexp_ec : Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
        Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) ≤
        Real.exp (-(c' * (tipL b).re)) * airyEnv u * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
      rw [← hair_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hEc_def : crudeExponentEc (S.ω τ) b =
          ComplexBessel.crudeExponentB (S.ω τ) + (ComplexBessel.stirlingJ (S.ω τ) b).re +
            (tipL b).re := rfl
      have h1 : c' * crudeExponentEc (S.ω τ) b ≤
          c' * (chartPhiV s b).re - c' * P.c_γ * ρ * s.re ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left hEc_le hc'_pos.le
        linarith only [hm]
      have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * P.c_γ * ρ * s.re ^ 2 := by
        have hcγ_nn := (div_pos P.hc_γ_pos (by norm_num : (0 : ℝ) < 16)).le
        have hkr : ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ) ≤
            (P.c_γ / 16) * (c' * ρ * s.re ^ 2) := by
          calc ((P.c_γ / 16) * (25 / 9 : ℝ) * ρ_min_Z ^ 3) * c' ^ (5 / 6 : ℝ)
              = (P.c_γ / 16) * ((25 / 9 : ℝ) * ρ_min_Z ^ 3 * c' ^ (5 / 6 : ℝ)) := by ring
            _ ≤ (P.c_γ / 16) * (c' * ρ * s.re ^ 2) :=
                mul_le_mul_of_nonneg_left hc_ρ_sre_sq hcγ_nn
        have h16 : (P.c_γ / 16) * (c' * ρ * s.re ^ 2) ≤ c' * P.c_γ * ρ * s.re ^ 2 := by
          have hnn : 0 ≤ P.c_γ * (c' * ρ * s.re ^ 2) :=
            mul_nonneg P.hc_γ_pos.le (mul_nonneg (mul_nonneg hc'_pos.le hρ_pos.le) (sq_nonneg _))
          linarith only [hnn]
        exact (mul_le_mul_of_nonneg_right hκ_ray (Real.rpow_nonneg hc'_pos.le _)).trans
          (hkr.trans h16)
      rw [hEc_def, mul_add, mul_add] at h1
      linarith only [h1, h2]
    have hCS2_max : W.C_S2 ≤ max W.C_S4 W.C_S2 := le_max_right _ _
    have hK_pref_nn : 0 ≤ (4 * Real.sqrt 3 / xiStar) * P_Γ * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) := by
      have := xiStar_pos; have := P.hC_d_pos; positivity
    calc ‖stirlingPrefW prob.w (S.ω τ) b‖ * ‖t ^ (-(1 / 2 : ℂ))‖ *
            ‖stirlingSW prob.w c' (S.ω τ)‖ *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * S.ω τ)‖ * ‖S.ω' τ‖
        ≤ (P_Γ * ((2 * Real.sqrt 3 / xiStar) * c' ^ (-(1 / 2 : ℝ)))) * 2 *
            Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
            (W.C_S2 * Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ)) * M_g) *
            P.C_d := by
          have := xiStar_pos; have := W.hCS2; have := hPΓ τ hτ; gcongr
      _ = ((4 * Real.sqrt 3 / xiStar) * P_Γ * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * W.C_S2) *
            (Real.exp (c' * (ComplexBessel.stirlingJ (S.ω τ) b).re) *
              Real.exp (c' * ComplexBessel.crudeExponentB (S.ω τ))) := by ring
      _ ≤ ((4 * Real.sqrt 3 / xiStar) * P_Γ * P.C_d * M_g * c' ^ (-(1 / 2 : ℝ)) * max W.C_S4 W.C_S2) *
            (Real.exp (-(c' * (tipL b).re)) * airyEnv u * Real.exp (-κ_all * c' ^ (5 / 6 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hCS2_max hK_pref_nn) hexp_ec
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (mul_nonneg hK_pref_nn hCS_max_pos.le)
      _ = K_seg * C_tail_u := by rw [hK_seg_eq]; dsimp [C_tail_u]; ring
  · -- `S.isStrip = true`: case split on `S.kind`
    cases hkind : S.kind
    · -- `.upperRay`
      obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_ur hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => t_max - τ)
        (continuous_const.sub continuous_id)
        (integral_exp_neg_mul_sub_sq_leW (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · -- `.lowerRay`
      obtain ⟨t_max, ht_max_nn, ha_eq, hb_eq_t, _, hray⟩ := h_lr hstr hkind
      exact hray_unified hstr t_max ht_max_nn ha_eq hb_eq_t (fun τ => τ)
        continuous_id
        (integral_exp_neg_mul_sq_leW (mul_pos (mul_pos hc'_pos P.hc_γ_pos) hρ_pos) ht_max_nn)
        (fun τ hτ => ⟨(hray τ hτ).1, (hray τ hτ).2.2⟩)
    · -- `.arcRadial`
      refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_ar hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWW prob.w c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_arc : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_arc * ρ ^ 3 := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have hρ_cube : ρ_min_Z ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hρ_min_pos.le hρ_ge_min 3
        have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * (P.κ_arc * ρ ^ 3) := by
          calc κ_all * c' ^ (5 / 6 : ℝ) ≤ (P.κ_arc * ρ_min_Z ^ 3) * c' :=
                mul_le_mul hκ_arc hc56_le_c (Real.rpow_nonneg hc'_pos.le _)
                  (mul_nonneg P.hκ_arc_pos.le (pow_nonneg hρ_min_pos.le 3))
            _ = c' * (P.κ_arc * ρ_min_Z ^ 3) := mul_comm _ _
            _ ≤ c' * (P.κ_arc * ρ ^ 3) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hρ_cube P.hκ_arc_pos.le) hc'_pos.le
        linarith only [hm, h2]
      calc ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_arc)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']
    · -- `.crudeEdge`: impossible when `S.isStrip = true`
      exact absurd hkind (h_no_crude hstr)
    · -- `.fixedStrip`
      refine const_seg_integral_le S.hab hba hK_seg_pos.le hC_tail_nn hC_tail_le_B hf_cont ?_
      intro τ hτ
      have hbase := hpt_strip_prod hstr τ hτ
      have hphi_bd := h_fs hstr hkind τ hτ
      have hζ_d := S.hζ_strip hstr τ hτ
      have hζ_cl : S.ζ τ ∈ stripClosed := ⟨hζ_d.1, hζ_d.2.1.trans (by norm_num)⟩
      have hwv_s4 : ‖tildeWW prob.w c' g (S.ζ τ)‖ ≤ max W.C_S4 W.C_S2 * M_g := by
        have h0 := W.hS4 hc'_S4 hg (S.ζ τ) hζ_cl
        rw [← hM_eq] at h0
        exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left W.C_S4 W.C_S2) hM_pos.le)
      have hexp_fs : Real.exp (c' * ((chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re)) ≤
          Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (chartPhiV (S.ζ τ) b).re - (chartPhiV s b).re ≤ -P.κ_strip := by
          linarith only [hphi_bd]
        have hm := mul_le_mul_of_nonneg_left h1 hc'_pos.le
        have h2 : κ_all * c' ^ (5 / 6 : ℝ) ≤ c' * P.κ_strip := by
          calc κ_all * c' ^ (5 / 6 : ℝ) ≤ P.κ_strip * c' :=
                mul_le_mul hκ_strip hc56_le_c (Real.rpow_nonneg hc'_pos.le _) P.hκ_strip_pos.le
            _ = c' * P.κ_strip := mul_comm _ _
        linarith only [hm, h2]
      calc ‖mellinDensityIntegrandW prob.w c' g t (S.ω τ) * S.ω' τ‖
          ≤ (K_seg / M_g) * (max W.C_S4 W.C_S2 * M_g) *
              Real.exp (-κ_all * c' ^ (5 / 6 : ℝ)) :=
            hbase.trans (hstrip_mul_le (mul_nonneg hCS_max_pos.le hM_pos.le) hwv_s4
              (Real.exp_pos _).le hexp_fs)
        _ = K_seg * C_tail_u := by dsimp [C_tail_u]; field_simp [hM_pos.ne']

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_Z_seg_bound_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_Z_seg_bound_W

end FormalResearch.ModularBootstrap.FixedWeightBand

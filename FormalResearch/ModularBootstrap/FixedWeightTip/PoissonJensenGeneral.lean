module

public import FormalResearch.ModularBootstrap.WeightAxioms.Axioms
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen
public import FormalResearch.ModularBootstrap.Crossing.GapFromPJ
public import FormalResearch.ModularBootstrap.Integration.StripTheoremA

/-!
# General Fixed-Weight `(w, Q)` Lemma PJ, Lemma G, and Theorem A

Generalizes the Spinless Virasoro real and complex Poisson–Jensen estimates
(`PoissonJensen.stripPoissonJensen`, `TipFront.stripPoissonJensen_complex`),
Proposition M (`proposition_M`), the deep-lobe estimate Lemma G (`lemmaG_of_cut`,
`lemmaG_general_delta`), and Theorem A (`theorem_A`) to an arbitrary fixed-weight
problem `prob : FixedWeightProblem` satisfying `PropositionPAxioms prob c'`
(`lower_o1_two_edge.tex`, Lemmas PJ, G, and Proposition M).

Notice that `(P0)–(P3)` / `(W1)–(W4)` enter only through:
* the strip bound `C_e * c'^p_e` / `C_e * (1 + c'^p_e)` on `hankelContinuationW prob.w c' g`,
* the band comparison `c_band * K_a^{(w)} ≤ V` on `[ξ̄ c', ∞)`,
* the general-`w` Bessel `I_{w-1}` asymptotic and kernel upper bound on `[0, ξ_*]`.

In particular, `p_e` (which equals `2` for Virasoro) becomes general, changing the
edge exponent `(5 / 2)` in Lemma PJ and Proposition M to `(p_e + 1 / 2)`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology Metric
open scoped Interval

namespace FormalResearch.ModularBootstrap.FixedWeightTip

open Crossing WeightAxioms PoissonJensen Integration Bessel TipFront

/-! ### 1. General-`w` Bessel / kernel bounds along the slit `[ξ_*, ∞)` -/

/-- Exact evaluation of `kernelK w (c' / 12) (c' * x^2 / 3)` for `c' > 0`, `x > 0`. -/
lemma kernelK_at_slit {w : ℕ} (hw : 1 ≤ w) {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) :
    kernelK w (c' / 12) (c' * x ^ 2 / 3) =
      (2 * x) ^ (w - 1) * besselI (w - 1) (c' * slitL x) := by
  have ha : 0 < c' / 12 := by positivity
  have ht : 0 < c' * x ^ 2 / 3 := by positivity
  rw [Crossing.kernelK_eq_besselI hw ha ht]
  have h1 : Real.sqrt ((c' * x ^ 2 / 3) / (c' / 12)) = 2 * x := by
    have heq : (c' * x ^ 2 / 3) / (c' / 12) = (2 * x) ^ 2 := by
      field_simp [hc'.ne']; ring
    rw [heq, Real.sqrt_sq (by positivity)]
  have h2 : 4 * π * Real.sqrt ((c' / 12) * (c' * x ^ 2 / 3)) = c' * slitL x := by
    have heq : (c' / 12) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
    rw [heq, Real.sqrt_sq (by positivity)]
    unfold slitL
    rw [abs_of_pos hx]
    ring
  rw [h1, h2]

/-- Strict positivity of `kernelK w α t` for `α ≥ 0` and `t > 0`. -/
lemma kernelK_pos_of_pos (w : ℕ) {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    0 < kernelK w α t := by
  unfold kernelK
  refine mul_pos (pow_pos (by positivity) _) ?_
  refine (summable_kernelKTerm w α t).tsum_pos (fun k => ?_) 0 ?_
  · unfold kernelKTerm; positivity
  · unfold kernelKTerm
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, zero_add, one_mul]
    positivity

/-- Lower and upper bounds on `log (kernelK w (c' / 12) (c' * x^2 / 3))` for `x ≥ ξ_*`. -/
lemma log_kernelK_slit_bounds (w : ℕ) (hw : 1 ≤ w) :
    ∃ C_Klo C_Kup c_Kw : ℝ, 0 ≤ C_Klo ∧ 0 ≤ C_Kup ∧ 8 ≤ c_Kw ∧
      ∀ {c' x : ℝ}, c_Kw ≤ c' → xiStar ≤ x →
        c' * slitL x - (1 / 2 : ℝ) * Real.log c' - (1 / 2 : ℝ) * slitL x - C_Klo ≤
          Real.log (kernelK w (c' / 12) (c' * x ^ 2 / 3)) ∧
        Real.log (kernelK w (c' / 12) (c' * x ^ 2 / 3)) ≤
          c' * slitL x + ((w : ℝ) + 1) * slitL x + C_Kup := by
  obtain ⟨C_I, hCI_nn, hI_bd⟩ := besselI_asymptotic_real (w - 1)
  have hL_xi_pos : 0 < slitL xiStar := by unfold slitL; positivity [xiStar_pos]
  let c_Kw : ℝ := max 8 (2 * C_I / slitL xiStar)
  have hcKw8 : 8 ≤ c_Kw := le_max_left _ _
  let C_Klo : ℝ :=
    ((w - 1 : ℕ) : ℝ) * |Real.log (2 * xiStar)| + Real.log 2 + (1 / 2 : ℝ) * Real.log (2 * π)
  refine ⟨C_Klo, 0, c_Kw, ?_, le_rfl, hcKw8, fun {c' x} hc' hx => ?_⟩
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    dsimp [C_Klo]
    positivity
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 ≤ c' := by linarith
  have hx_pos : 0 < x := lt_of_lt_of_le xiStar_pos hx
  have hK_eq := kernelK_at_slit hw hc0 hx_pos
  have hL_ge : slitL xiStar ≤ slitL x := by
    unfold slitL
    rw [abs_of_pos xiStar_pos, abs_of_pos hx_pos]
    gcongr
  have hL_pos : 0 < slitL x := lt_of_lt_of_le hL_xi_pos hL_ge
  let z : ℝ := c' * slitL x
  have hz_ge : 2 * C_I ≤ z := by
    have h1 : 2 * C_I / slitL xiStar ≤ c' := (le_max_right _ _).trans hc'
    have h2 : 2 * C_I ≤ c' * slitL xiStar := (div_le_iff₀ hL_xi_pos).mp h1
    exact h2.trans (mul_le_mul_of_nonneg_left hL_ge hc0.le)
  have hz_pos : 0 < z := by dsimp [z]; positivity
  have hAs_pos : 0 < besselAs z := besselAs_pos hz_pos
  have hCI_z : C_I / z ≤ 1 / 2 := by
    rw [div_le_iff₀ hz_pos]; linarith
  have hI_rel := (abs_le.mp (hI_bd hz_pos)).1
  have hI_ge : (1 / 2 : ℝ) * besselAs z ≤ besselI (w - 1) z := by
    have h1 : (1 / 2 : ℝ) ≤ besselI (w - 1) z / besselAs z := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hAs_pos.le
    rwa [div_mul_cancel₀ _ hAs_pos.ne'] at h2
  have hI_pos : 0 < besselI (w - 1) z := lt_of_lt_of_le (by positivity) hI_ge
  have h2x_pos : 0 < 2 * x := by positivity
  have h2xi_pos : 0 < 2 * xiStar := by positivity [xiStar_pos]
  -- Lower bound
  have hlo : c' * slitL x - (1 / 2 : ℝ) * Real.log c' - (1 / 2 : ℝ) * slitL x - C_Klo ≤
      Real.log (kernelK w (c' / 12) (c' * x ^ 2 / 3)) := by
    rw [hK_eq, Real.log_mul (pow_pos h2x_pos _).ne' hI_pos.ne', Real.log_pow]
    have hlog_x : Real.log (2 * xiStar) ≤ Real.log (2 * x) :=
      Real.log_le_log h2xi_pos (by linarith)
    have hpow_ge : -((w - 1 : ℕ) : ℝ) * |Real.log (2 * xiStar)| ≤
        ((w - 1 : ℕ) : ℝ) * Real.log (2 * x) := by
      have h1 : -|Real.log (2 * xiStar)| ≤ Real.log (2 * x) :=
        (neg_abs_le (Real.log (2 * xiStar))).trans hlog_x
      calc -((w - 1 : ℕ) : ℝ) * |Real.log (2 * xiStar)|
          = ((w - 1 : ℕ) : ℝ) * (-|Real.log (2 * xiStar)|) := by ring
        _ ≤ ((w - 1 : ℕ) : ℝ) * Real.log (2 * x) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    have hlog_I : Real.log ((1 / 2 : ℝ) * besselAs z) ≤ Real.log (besselI (w - 1) z) :=
      Real.log_le_log (by positivity) hI_ge
    have hlog_as : Real.log ((1 / 2 : ℝ) * besselAs z) =
        -Real.log 2 + z - (1 / 2 : ℝ) * (Real.log (2 * π) + Real.log c' + Real.log (slitL x)) := by
      rw [Real.log_mul (by positivity) hAs_pos.ne', one_div, Real.log_inv]
      unfold besselAs
      rw [Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (by positivity)).ne',
        Real.log_exp, Real.log_sqrt (by positivity),
        Real.log_mul (by positivity) hz_pos.ne',
        show z = c' * slitL x from rfl,
        Real.log_mul hc0.ne' hL_pos.ne']
      ring
    have hlogL_le : Real.log (slitL x) ≤ slitL x := by
      linarith [Real.log_le_sub_one_of_pos hL_pos]
    rw [hlog_as] at hlog_I
    dsimp [C_Klo]
    linarith [hpow_ge, hlog_I, hlogL_le]
  -- Upper bound via `kernelK_le_pow_mul_exp`
  have hup : Real.log (kernelK w (c' / 12) (c' * x ^ 2 / 3)) ≤
      c' * slitL x + ((w : ℝ) + 1) * slitL x + 0 := by
    have hKub := WeightAxioms.kernelK_le_pow_mul_exp hw (by positivity : 0 < c' / 12)
      (by positivity : 0 ≤ c' * x ^ 2 / 3)
    have hs1 : Real.sqrt ((c' * x ^ 2 / 3) / (c' / 12)) = 2 * x := by
      have heq : (c' * x ^ 2 / 3) / (c' / 12) = (2 * x) ^ 2 := by
        field_simp [hc0.ne']; ring
      rw [heq, Real.sqrt_sq (by positivity)]
    have hs2 : 4 * π * Real.sqrt ((c' / 12) * (c' * x ^ 2 / 3)) = c' * slitL x := by
      have heq : (c' / 12) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
      rw [heq, Real.sqrt_sq (by positivity)]
      unfold slitL
      rw [abs_of_pos hx_pos]
      ring
    rw [hs1, hs2] at hKub
    have hKpos : 0 < kernelK w (c' / 12) (c' * x ^ 2 / 3) :=
      kernelK_pos_of_pos w (by positivity) (by positivity)
    have hlogK := Real.log_le_log hKpos hKub
    rw [Real.log_mul (pow_pos h2x_pos _).ne' (Real.exp_pos _).ne', Real.log_pow,
      Real.log_exp] at hlogK
    have hlog2x : Real.log (2 * x) ≤ slitL x := by
      have h1 : Real.log (2 * x) ≤ 2 * x := by linarith [Real.log_le_sub_one_of_pos h2x_pos]
      have h2 : 2 * x ≤ slitL x := by
        unfold slitL
        rw [abs_of_pos hx_pos]
        nlinarith [Real.pi_gt_three]
      exact h1.trans h2
    have hcast : ((w - 1 : ℕ) : ℝ) ≤ (w : ℝ) + 1 := by
      have h1 : w - 1 ≤ w := Nat.sub_le w 1
      have h2 : ((w - 1 : ℕ) : ℝ) ≤ (w : ℝ) := by exact_mod_cast h1
      linarith
    have hmul : ((w - 1 : ℕ) : ℝ) * Real.log (2 * x) ≤ ((w : ℝ) + 1) * slitL x := by
      rcases le_or_gt (Real.log (2 * x)) 0 with hle | hpos
      · calc ((w - 1 : ℕ) : ℝ) * Real.log (2 * x)
            ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hle
          _ ≤ ((w : ℝ) + 1) * slitL x := mul_nonneg (by positivity) hL_pos.le
      · exact mul_le_mul hcast hlog2x hpos.le (by positivity)
    linarith
  exact ⟨hlo, hup⟩

/-! ### 2. General slit-mass bound `(eSlitMass)` and boundary a.e. nonvanishing -/

/-- General `(w, Q)` slit-mass bound (`eSlitMass`):
`∫_{ξ_*}^∞ |g(c' x² / 3)| K_{c'/12}^{(w)}(c' x² / 3) dx ≤ (3 / (2 ξ_* c_band)) * c'⁻¹ * M[g]`. -/
theorem eSlitMass_general (prob : FixedWeightProblem) {c' : ℝ} (P : PropositionPAxioms prob c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) :
    IntegrableOn (fun x : ℝ => |g (c' * x ^ 2 / 3)| * kernelK prob.w (c' / 12) (c' * x ^ 2 / 3))
        (Ioi xiStar) ∧
      ∫ x in Ioi xiStar, |g (c' * x ^ 2 / 3)| * kernelK prob.w (c' / 12) (c' * x ^ 2 / 3) ≤
        (3 / (2 * xiStar * P.c_band)) * c'⁻¹ * prob.cardyNorm (c' / 12) g := by
  have hc0 : 0 < c' := P.hc'_pos
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 * c' / 3) * x
  have hφ_xi_eq : φ xiStar = xiBar * c' := by
    dsimp [φ]; unfold xiBar; ring
  have hφ_xi_pos : 0 < φ xiStar := by dsimp [φ]; positivity [xiStar_pos]
  have hφ_deriv : ∀ x ∈ Ioi xiStar, HasDerivWithinAt φ (φ' x) (Ioi xiStar) x := fun x _ => by
    dsimp [φ, φ']
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    exact ((hsq.const_mul c').div_const 3).congr_deriv (by ring) |>.hasDerivWithinAt
  have hφ_inj : InjOn φ (Ioi xiStar) := fun x hx y hy hxy => by
    dsimp [φ] at hxy
    have hsq : x ^ 2 = y ^ 2 := by
      have hne : c' / 3 ≠ 0 := by positivity
      calc x ^ 2 = (c' * x ^ 2 / 3) / (c' / 3) := by field_simp
        _ = (c' * y ^ 2 / 3) / (c' / 3) := by rw [hxy]
        _ = y ^ 2 := by field_simp
    have hx0 : 0 ≤ x := (xiStar_pos.trans hx).le
    have hy0 : 0 ≤ y := (xiStar_pos.trans hy).le
    nlinarith [sq_nonneg (x - y)]
  have hφ_img : φ '' Ioi xiStar = Ioi (φ xiStar) := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      have hlt : xiStar < x := hx
      have hxs : 0 < xiStar := xiStar_pos
      have hsq : xiStar ^ 2 < x ^ 2 := by nlinarith
      dsimp [φ]; exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq hc0) (by norm_num)
    · intro ht
      have ht_pos : 0 < t := lt_trans hφ_xi_pos ht
      have h3t_pos : 0 ≤ 3 * t / c' := div_nonneg (by positivity) hc0.le
      refine ⟨Real.sqrt (3 * t / c'), ?_, ?_⟩
      · have hlt : xiStar ^ 2 < 3 * t / c' := by
          rw [lt_div_iff₀ hc0]
          have hgt : φ xiStar < t := ht
          dsimp [φ] at hgt; linarith
        rw [← Real.sqrt_sq xiStar_pos.le]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt
      · dsimp [φ]
        rw [Real.sq_sqrt h3t_pos]
        field_simp [hc0.ne']
  let fV : ℝ → ℝ := fun t => |g t| * prob.cardyV (c' / 12) t
  have hfV_int : IntegrableOn fV (Ioi (φ xiStar)) :=
    hg.int_cardy.mono_set (Ioi_subset_Ioi hφ_xi_pos.le)
  have hfV_pull : IntegrableOn (fun x : ℝ => |φ' x| • fV (φ x)) (Ioi xiStar) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj fV).mp
      (hφ_img ▸ hfV_int)
  have hfV_eq_int : ∫ x in Ioi xiStar, |φ' x| • fV (φ x) = ∫ t in Ioi (φ xiStar), fV t := by
    rw [← hφ_img]
    exact (integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ_deriv hφ_inj fV).symm
  have hM_ge : ∫ t in Ioi (φ xiStar), fV t ≤ prob.cardyNorm (c' / 12) g := by
    unfold FixedWeightProblem.cardyNorm
    refine setIntegral_mono_set hg.int_cardy ?_
      (ae_of_all _ fun t ht => Ioi_subset_Ioi hφ_xi_pos.le ht)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (P.p1_pos (mem_Ioi.mp ht)).le
  have hmeas_K : AEStronglyMeasurable
      (fun x : ℝ => |g (φ x)| * kernelK prob.w (c' / 12) (φ x)) (volume.restrict (Ioi xiStar)) := by
    have hcont_g : ContinuousOn (fun x : ℝ => |g (φ x)|) (Ioi xiStar) :=
      (hg.cont.abs).comp (by fun_prop : Continuous φ).continuousOn
        (fun x _ => show 0 ≤ c' * x ^ 2 / 3 by positivity)
    have hcont_K : Continuous fun x : ℝ => kernelK prob.w (c' / 12) (φ x) :=
      (continuous_kernelK prob.w (c' / 12)).comp (by fun_prop)
    exact (hcont_g.mul hcont_K.continuousOn).aestronglyMeasurable measurableSet_Ioi
  let coeff : ℝ := (2 * c' * xiStar / 3) * P.c_band
  have hcoeff_pos : 0 < coeff := mul_pos (by positivity [xiStar_pos]) P.hc_band_pos
  have hpt_bd : ∀ x ∈ Ioi xiStar,
      coeff * (|g (φ x)| * kernelK prob.w (c' / 12) (φ x)) ≤ |φ' x| • fV (φ x) := by
    intro x hx
    have hx_gt : xiStar < x := hx
    have hφ_ge : xiBar * c' ≤ φ x := by
      rw [← hφ_xi_eq]
      dsimp [φ]
      gcongr
      exact xiStar_pos.le
    have hband := P.p1_band hφ_ge
    have hφ'_pos : 0 ≤ φ' x := by dsimp [φ']; positivity [xiStar_pos.trans hx_gt]
    rw [smul_eq_mul, abs_of_nonneg hφ'_pos]
    have hK_nn : 0 ≤ kernelK prob.w (c' / 12) (φ x) :=
      kernelK_nonneg (by positivity) (by dsimp [φ]; positivity)
    calc coeff * (|g (φ x)| * kernelK prob.w (c' / 12) (φ x))
        = (2 * c' * xiStar / 3) * (|g (φ x)| * (P.c_band * kernelK prob.w (c' / 12) (φ x))) := by
          dsimp [coeff]; ring
      _ ≤ (2 * c' / 3 * x) * (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) := by
          have hcoeff_le : 2 * c' * xiStar / 3 ≤ 2 * c' / 3 * x := by
            calc 2 * c' * xiStar / 3 = (2 * c' / 3) * xiStar := by ring
              _ ≤ (2 * c' / 3) * x := mul_le_mul_of_nonneg_left hx_gt.le (by positivity)
              _ = 2 * c' / 3 * x := by ring
          exact mul_le_mul hcoeff_le (mul_le_mul_of_nonneg_left hband (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (mul_nonneg P.hc_band_pos.le hK_nn))
            (by positivity [xiStar_pos.trans hx_gt])
      _ = φ' x * fV (φ x) := by simp only [φ', fV]
  have hK_int_mul : IntegrableOn
      (fun x : ℝ => coeff * (|g (φ x)| * kernelK prob.w (c' / 12) (φ x))) (Ioi xiStar) := by
    refine hfV_pull.mono' (hmeas_K.const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnn : 0 ≤ coeff * (|g (φ x)| * kernelK prob.w (c' / 12) (φ x)) :=
      mul_nonneg hcoeff_pos.le (mul_nonneg (abs_nonneg _) (kernelK_nonneg (by positivity)
        (by dsimp [φ]; positivity)))
    rw [Real.norm_of_nonneg hnn]
    exact hpt_bd x hx
  have hK_int : IntegrableOn (fun x : ℝ => |g (φ x)| * kernelK prob.w (c' / 12) (φ x))
      (Ioi xiStar) := by
    have hfun : (fun x : ℝ => coeff * (|g (φ x)| * kernelK prob.w (c' / 12) (φ x)) / coeff) =
        fun x : ℝ => |g (φ x)| * kernelK prob.w (c' / 12) (φ x) := by
      ext x; field_simp [hcoeff_pos.ne']
    rw [← hfun]
    exact hK_int_mul.div_const coeff
  refine ⟨hK_int, ?_⟩
  have hmono := setIntegral_mono_on hK_int_mul hfV_pull measurableSet_Ioi hpt_bd
  rw [integral_const_mul, hfV_eq_int] at hmono
  have hle_M : coeff * ∫ x in Ioi xiStar, |g (φ x)| * kernelK prob.w (c' / 12) (φ x) ≤
      prob.cardyNorm (c' / 12) g := hmono.trans hM_ge
  have hdiv : ∫ x in Ioi xiStar, |g (φ x)| * kernelK prob.w (c' / 12) (φ x) ≤
      coeff⁻¹ * prob.cardyNorm (c' / 12) g := by
    rw [mul_comm] at hle_M
    calc ∫ x in Ioi xiStar, |g (φ x)| * kernelK prob.w (c' / 12) (φ x)
        ≤ prob.cardyNorm (c' / 12) g / coeff := (le_div_iff₀ hcoeff_pos).mpr hle_M
      _ = coeff⁻¹ * prob.cardyNorm (c' / 12) g := by ring
  refine hdiv.trans_eq ?_
  dsimp [coeff]
  field_simp [hc0.ne', xiStar_pos.ne', P.hc_band_pos.ne']

lemma hankelContinuationW_neg (w : ℕ) (c' : ℝ) (g : ℝ → ℝ) (b : ℂ) :
    hankelContinuationW w c' g (-b) = hankelContinuationW w c' g b := by
  unfold hankelContinuationW
  simp

/-- A.e. nonvanishing along `slitPreimage` for any holomorphic strip extension `G` of
`x ↦ g(c' x^2 / 3)` that is nonzero at a strip point `b₀` (`|b₀.im| < 1/2`). -/
theorem strip_ext_bdy_ne_zero_ae (_prob : FixedWeightProblem) {c' : ℝ}
    {g : ℝ → ℝ} {G : ℂ → ℂ}
    (hG_diff : DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2})
    (_hG_real : ∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ))
    {b₀ : ℂ} (hb₀ : |b₀.im| < 1 / 2) (hb₀_ne : G b₀ ≠ 0) :
    ∀ᵐ σ ∂(volume.restrict slitPreimage),
      G (slitBoundaryMap σ : ℂ) ≠ 0 := by
  have han : AnalyticOnNhd ℂ G {b : ℂ | |b.im| < 1 / 2} :=
    hG_diff.analyticOnNhd (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hconv : Convex ℝ {b : ℂ | |b.im| < 1 / 2} := by
    have heq : {b : ℂ | |b.im| < 1 / 2} = Complex.imCLM ⁻¹' Ioo (-(1 / 2)) (1 / 2) := by
      ext b; simp [Complex.imCLM_apply, abs_lt]
    rw [heq]
    exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap
  have hpre : IsPreconnected {b : ℂ | |b.im| < 1 / 2} := hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | G (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | G (r : ℂ) = 0} =
        ⋃ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ G (r : ℂ) = 0} := by
      ext r
      simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |r|
      exact ⟨n, ⟨by linarith [abs_le.mp hn], by linarith [abs_le.mp hn]⟩, hr⟩
    rw [heq]
    have hfin : ∀ n : ℕ,
        {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ G (r : ℂ) = 0}.Finite := by
      intro n
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hr₀_mem : (r₀ : ℂ) ∈ {b : ℂ | |b.im| < 1 / 2} := by simp
      have hfreq : ∃ᶠ z in 𝓝[≠] (r₀ : ℂ), G z = 0 := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
        obtain ⟨V, hV, hVU⟩ := hU
        obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
          (hacc.and_eventually (Metric.ball_mem_nhds r₀ hε_pos)).exists
        have hrC_ne : (r : ℂ) ≠ (r₀ : ℂ) := fun he => hr_ne (Complex.ofReal_injective he)
        have hrC_ball : (r : ℂ) ∈ Metric.ball (r₀ : ℂ) ε := by
          rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
        exact ⟨(r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hr₀_mem hfreq
      exact hb₀_ne (hzero hb₀)
    exact Set.countable_iUnion fun n => (hfin n).countable
  have hσ_cnt : {σ : ℝ | σ ∈ slitPreimage ∧ G (slitBoundaryMap σ : ℂ) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧ G (slitBoundaryMap σ : ℂ) = 0} ⊆
        ⋃ r ∈ {r : ℝ | G (r : ℂ) = 0}, {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} :=
      fun σ ⟨hσ, h0⟩ => mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  have hnull : volume {σ : ℝ | σ ∈ slitPreimage ∧ G (slitBoundaryMap σ : ℂ) = 0} = 0 :=
    hσ_cnt.measure_zero volume
  change ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1)), G (slitBoundaryMap σ : ℂ) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

/-- Any holomorphic strip extension `G` of `x ↦ g(c' x^2 / 3)` agrees with
`hankelContinuationW prob.w c' g` on `{b : ℂ | |b.im| < 1/2}` when `hankelContinuationW`
is differentiable there. -/
theorem strip_ext_eq_hankelContinuationW (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : 0 < c') {g : ℝ → ℝ}
    (hH_diff : DifferentiableOn ℂ (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| < 1 / 2})
    (hg : TestClass prob (c' / 12) g)
    {G : ℂ → ℂ} (hG_diff : DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2})
    (hG_real : ∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ)) :
    EqOn G (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| < 1 / 2} := by
  have han : AnalyticOnNhd ℂ (fun b => G b - hankelContinuationW prob.w c' g b)
      {b : ℂ | |b.im| < 1 / 2} :=
    (hG_diff.sub hH_diff).analyticOnNhd (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hconv : Convex ℝ {b : ℂ | |b.im| < 1 / 2} := by
    have heq : {b : ℂ | |b.im| < 1 / 2} = Complex.imCLM ⁻¹' Ioo (-(1 / 2)) (1 / 2) := by
      ext b; simp [Complex.imCLM_apply, abs_lt]
    rw [heq]
    exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap
  have hpre : IsPreconnected {b : ℂ | |b.im| < 1 / 2} := hconv.isPreconnected
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), G z - hankelContinuationW prob.w c' g z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
    let r : ℝ := ε / 2
    have hr_pos : 0 < r := half_pos hε_pos
    have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    have hr_ball : (r : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]
      dsimp [r]; linarith
    refine ⟨(r : ℂ), hVU ⟨hball hr_ball, hr_ne⟩, ?_⟩
    rw [hG_real r, WeightAxioms.hankelContinuationW_ofReal prob.hw hc' hg.cont hg.int_lift hg.fourier_odd r,
      sub_self]
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre (by simp) hfreq
  intro b hb
  exact sub_eq_zero.mp (hzero hb)

/-! ### 3. Shared half-plane Poisson–Jensen core and real / complex Lemma PJ -/

private lemma abs_slitBoundaryMap_ge_xiStar' {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    xiStar ≤ |slitBoundaryMap σ| := by
  rcases hσ with hIoo | hIoi
  · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
  · have := slitBoundaryMap_le_neg_xiStar hIoi
    linarith [neg_abs_le (slitBoundaryMap σ)]

private lemma slitPreimage_disjoint_edgePreimage : Disjoint slitPreimage edgePreimage := by
  rw [Set.disjoint_left]
  intro σ h1 h2
  rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
  · linarith [h1.1]
  · linarith [h1.2, h2.1]
  · linarith
  · linarith [h2.2]

private lemma slitPreimage_union_edgePreimage_ae :
    (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
  have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
    ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
  refine Filter.eventuallyEqSet_iff'.2 ?_
  change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
  rw [ae_iff]
  refine measure_mono_null (fun σ hσ => ?_) hnull
  by_contra hnot
  apply hσ; apply propext
  simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
  rcases lt_or_gt_of_ne hnot.1 with hm | hm
  · exact Or.inr (Or.inl hm)
  · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
    · exact Or.inl (Or.inl ⟨hm, h0⟩)
    · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
      · exact Or.inr (Or.inr ⟨h0, h1⟩)
      · exact Or.inl (Or.inr h1)

private lemma slitMass_pos' {x y : ℝ} (hy : 0 < y) : 0 < slitMass x y := by
  have hIoo_pos : 0 < ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_
      (integrable_poissonKernel x hy).integrableOn).mpr ?_
    · exact Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ
    · have hsupp : Function.support (poissonKernel x y) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1) 0 := by
        ext σ
        simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
        intro _; exact (poissonKernel_pos (x := x) hy σ).ne'
      rw [hsupp, Real.volume_Ioo]; norm_num
  have hle : ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ ≤ slitMass x y := by
    unfold slitMass slitPreimage
    exact setIntegral_mono_set (integrable_poissonKernel x hy).integrableOn
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
      (ae_of_all _ fun σ hσ => Set.subset_union_left hσ)
  linarith

private lemma slitMass_le_one'' {x y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  unfold slitMass
  calc ∫ σ in slitPreimage, poissonKernel x y σ
      ≤ ∫ σ : ℝ, poissonKernel x y σ :=
        setIntegral_le_integral (integrable_poissonKernel x hy)
          (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
    _ = 1 := integral_poissonKernel x hy

private lemma one_sub_slitMass_eq_edgeMass'' {x y : ℝ} (hy : 0 < y) :
    1 - slitMass x y = ∫ σ in edgePreimage, poissonKernel x y σ := by
  have hint := integrable_poissonKernel x hy
  have htot : slitMass x y + ∫ σ in edgePreimage, poissonKernel x y σ = 1 := by
    unfold slitMass
    rw [← setIntegral_union slitPreimage_disjoint_edgePreimage
        (measurableSet_Iio.union measurableSet_Ioo)
        hint.integrableOn hint.integrableOn,
      setIntegral_congr_set slitPreimage_union_edgePreimage_ae, setIntegral_univ]
    exact integral_poissonKernel x hy
  linarith

private lemma log_integral_jensen_slitPreimage_aux {x y : ℝ} (hy : 0 < y)
    {f : ℝ → ℝ} (hf_pos : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ)
    (hf_int : IntegrableOn (fun σ => f σ * poissonKernel x y σ) slitPreimage)
    (hlog_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x y σ) slitPreimage)
    {B : ℝ} (_hB_pos : 0 < B)
    (hI_le : ∫ σ in slitPreimage, f σ * poissonKernel x y σ ≤ B) :
    ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      slitMass x y * Real.log B + (1 - slitMass x y) := by
  have hm_pos : 0 < slitMass x y := slitMass_pos' hy
  set m := slitMass x y
  set I_f := ∫ σ in slitPreimage, f σ * poissonKernel x y σ
  have hIf_pos : 0 < I_f := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf_int).mpr ?_
    · filter_upwards [hf_pos] with σ hσ
      exact mul_nonneg hσ.le (poissonKernel_nonneg hy.le σ)
    · have hIoo_sub : Ioo (-1 : ℝ) 0 ⊆ slitPreimage := Set.subset_union_left
      have hIoo_pos : 0 < volume (Ioo (-1 : ℝ) 0) := by rw [Real.volume_Ioo]; norm_num
      have hae_pos : ∀ᵐ σ ∂volume, σ ∈ Ioo (-1 : ℝ) 0 → 0 < f σ * poissonKernel x y σ := by
        have h1 : ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), 0 < f σ :=
          hf_pos.filter_mono (ae_mono (Measure.restrict_mono hIoo_sub le_rfl))
        rw [ae_restrict_iff' measurableSet_Ioo] at h1
        filter_upwards [h1] with σ hσ hm
        exact mul_pos (hσ hm) (poissonKernel_pos (x := x) hy σ)
      by_contra h0
      have hzero : volume ((Function.support fun σ => f σ * poissonKernel x y σ) ∩ slitPreimage) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp h0)
      have hnull1 : ∀ᵐ σ ∂volume, ¬(σ ∈ Ioo (-1 : ℝ) 0 ∧ f σ * poissonKernel x y σ ≠ 0) := by
        rw [← compl_mem_ae_iff] at hzero
        filter_upwards [hzero] with σ hσ ⟨h1, h2⟩
        exact hσ ⟨h2, hIoo_sub h1⟩
      have hsub_empty : ∀ᵐ σ ∂volume, σ ∉ Ioo (-1 : ℝ) 0 := by
        filter_upwards [hae_pos, hnull1] with σ hp hn hm
        exact hn ⟨hm, (hp hm).ne'⟩
      have hv0 : volume (Ioo (-1 : ℝ) 0) = 0 := by
        rw [ae_iff] at hsub_empty
        convert hsub_empty using 2
        ext σ; simp
      exact hIoo_pos.ne' hv0
  set c_avg := I_f / m
  have hc_pos : 0 < c_avg := div_pos hIf_pos hm_pos
  have hlog_bd : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x y σ ≤
        (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by
    filter_upwards [hf_pos] with σ hσ
    have h1 : Real.log (f σ / c_avg) ≤ f σ / c_avg - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hσ hc_pos)
    rw [Real.log_div hσ.ne' hc_pos.ne'] at h1
    have h2 : Real.log (f σ) ≤ (Real.log c_avg - 1) + c_avg⁻¹ * f σ := by
      linarith [show f σ / c_avg = c_avg⁻¹ * f σ by ring]
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    calc Real.log (f σ) * poissonKernel x y σ
        ≤ ((Real.log c_avg - 1) + c_avg⁻¹ * f σ) * poissonKernel x y σ := by gcongr
      _ = (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by
          ring
  have hpk_int : IntegrableOn (poissonKernel x y) slitPreimage :=
    (integrable_poissonKernel x hy).integrableOn
  have hrhs_int : IntegrableOn
      (fun σ => (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ))
      slitPreimage :=
    (hpk_int.const_mul _).add (hf_int.const_mul _)
  have hint_mono : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) :=
    setIntegral_mono_ae_restrict hlog_int hrhs_int hlog_bd
  have heval : ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) =
      m * Real.log (I_f / m) := by
    rw [integral_add (hpk_int.const_mul _) (hf_int.const_mul _),
      integral_const_mul, integral_const_mul]
    change (Real.log c_avg - 1) * m + c_avg⁻¹ * I_f = m * Real.log (I_f / m)
    have hc_eq : c_avg⁻¹ * I_f = m := by
      dsimp [c_avg]; field_simp [hm_pos.ne', hIf_pos.ne']
    rw [hc_eq]
    dsimp [c_avg]
    ring
  have hdiv_le : m * Real.log (I_f / m) ≤ m * Real.log B + (1 - m) := by
    rw [div_eq_mul_inv, Real.log_mul hIf_pos.ne' (inv_ne_zero hm_pos.ne')]
    have hlogI : Real.log I_f ≤ Real.log B := Real.log_le_log hIf_pos hI_le
    have hlogm : Real.log m⁻¹ ≤ m⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hm_pos)
    have hm1 : m * Real.log m⁻¹ ≤ 1 - m := by
      calc m * Real.log m⁻¹ ≤ m * (m⁻¹ - 1) := mul_le_mul_of_nonneg_left hlogm hm_pos.le
        _ = 1 - m := by field_simp [hm_pos.ne']
    calc m * (Real.log I_f + Real.log m⁻¹)
        = m * Real.log I_f + m * Real.log m⁻¹ := by ring
      _ ≤ m * Real.log B + (1 - m) := add_le_add (mul_le_mul_of_nonneg_left hlogI hm_pos.le) hm1
  exact hint_mono.trans (heval.le.trans hdiv_le)

/-- Explicit constant `C_PJ` for the general-`(w, Q)` strip Poisson–Jensen bound from
`(C_e, c_band, C_Klo, U_bd)`. -/
noncomputable def pjConstOf (C_e c_band C_Klo U_bd : ℝ) : ℝ :=
  max 0 (Real.log C_e) + max 0 (Real.log (3 / (xiStar * c_band))) + 1 +
    (1 / 2 : ℝ) * U_bd + C_Klo

private lemma halfPlane_pj_core (prob : FixedWeightProblem) {c' : ℝ}
    (P : PropositionPAxioms prob c')
    {C_Klo C_Kup c_Kw : ℝ} (hCKlo : 0 ≤ C_Klo) (_hCKup : 0 ≤ C_Kup) (hcKw8 : 8 ≤ c_Kw)
    (hlogK_bd : ∀ {c'' x : ℝ}, c_Kw ≤ c'' → xiStar ≤ x →
      c'' * slitL x - (1 / 2 : ℝ) * Real.log c'' - (1 / 2 : ℝ) * slitL x - C_Klo ≤
        Real.log (kernelK prob.w (c'' / 12) (c'' * x ^ 2 / 3)) ∧
      Real.log (kernelK prob.w (c'' / 12) (c'' * x ^ 2 / 3)) ≤
        c'' * slitL x + ((prob.w : ℝ) + 1) * slitL x + C_Kup)
    (hc' : c_Kw ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    {G : ℂ → ℂ} (hG_cont : ContinuousOn G {b : ℂ | |b.im| ≤ 1 / 2})
    (hG_diff : DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2})
    (hG_real : ∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ))
    (hG_bd : ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
      ‖G b‖ ≤ P.C_e * c' ^ P.p_e * prob.cardyNorm (c' / 12) g)
    (x₀ y₀ : ℝ) (hy₀_pos : 0 < y₀)
    (hb_ne : G (confB ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≠ 0)
    (U_val U_bd : ℝ)
    (hU_eq : -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ = U_val)
    (hU_bd : -U_val ≤ U_bd) :
    Real.log ‖G (confB ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I))‖ -
        Real.log (prob.cardyNorm (c' / 12) g) ≤
      c' * U_val - (1 / 2 : ℝ) * Real.log c' +
        (P.p_e + 1 / 2) * (1 - slitMass x₀ y₀) * Real.log c' +
        slitEntropy x₀ y₀ + pjConstOf P.C_e P.c_band C_Klo U_bd := by
  have hc0 : 0 < c' := P.hc'_pos
  have hc1 : 1 ≤ c' := by linarith
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc1
  set M : ℝ := prob.cardyNorm (c' / 12) g
  set z₀ : ℂ := (x₀ : ℂ) + (y₀ : ℂ) * Complex.I
  have hz₀_im : 0 < z₀.im := by simpa [z₀] using hy₀_pos
  have hz₀_re : z₀.re = x₀ := by simp [z₀]
  have hm_pos : 0 < slitMass x₀ y₀ := slitMass_pos' hy₀_pos
  have hm_le : slitMass x₀ y₀ ≤ 1 := slitMass_le_one'' hy₀_pos
  set m : ℝ := slitMass x₀ y₀
  let F : ℂ → ℂ := fun z => (M⁻¹ : ℂ) * G (confB z)
  let F_bdy : ℝ → ℂ := fun σ => (M⁻¹ : ℂ) * G (confB (σ : ℂ))
  let C_e0 : ℝ := max 1 P.C_e
  have hCe0_pos : 0 < C_e0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let M_strip : ℝ := C_e0 * c' ^ P.p_e
  have hc_pe_ge1 : 1 ≤ c' ^ P.p_e := Real.one_le_rpow hc1 P.hp_e_nn
  have hMstrip_ge1 : 1 ≤ M_strip := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hc_pe_ge1
  have hMstrip_pos : 0 < M_strip := lt_of_lt_of_le zero_lt_one hMstrip_ge1
  have hF_diff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := by
    intro z hz
    have hcb : confB z ∈ slitStrip := confB_mem_slitStrip hz
    have hc_diff : DifferentiableAt ℂ confB z := (hasDerivAt_confB hz).differentiableAt
    have hg_diff : DifferentiableAt ℂ G (confB z) :=
      hG_diff.differentiableAt ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds hcb.1)
    exact ((hg_diff.comp z hc_diff).const_mul (M⁻¹ : ℂ)).differentiableWithinAt
  have hG_strip_bd : ∀ b : ℂ, |b.im| ≤ 1 / 2 → ‖G b‖ ≤ M_strip * M := by
    intro b hb
    have hsup := hG_bd hb
    calc ‖G b‖
        ≤ P.C_e * c' ^ P.p_e * M := hsup
      _ ≤ C_e0 * c' ^ P.p_e * M := by
          gcongr; exact le_max_right _ _
      _ = M_strip * M := rfl
  have hF_bd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M_strip := by
    intro z hz
    have hcb : |(confB z).im| ≤ 1 / 2 := (confB_mem_slitStrip hz).1.le
    dsimp [F]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
    calc M⁻¹ * ‖G (confB z)‖
        ≤ M⁻¹ * (M_strip * M) := by gcongr; exact hG_strip_bd _ hcb
      _ = M_strip := by field_simp [hM_pos.ne']
  have hconfB_im_real : ∀ σ : ℝ, σ ∉ ({-1, 0, 1} : Set ℝ) → |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
    intro σ hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_trichotomy σ (-1) with hm | rfl | hm1
    · rw [confB_real_im_of_lt_neg_one hm]; norm_num
    · exact absurd rfl hnot.1
    · rcases lt_trichotomy σ 0 with h0 | rfl | h0
      · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
      · exact absurd rfl hnot.2.1
      · rcases lt_trichotomy σ 1 with h1 | rfl | h1
        · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
        · exact absurd rfl hnot.2.2
        · rw [confB_real_im_of_one_lt h1]; norm_num
  have hF_bdy : ∀ᵐ σ : ℝ ∂volume,
      Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 :=
      ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have htend_B : Tendsto confB (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ))
        (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (σ : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).tendsto.mono_left
          (nhdsWithin_mono _ fun z (hz : 0 < z.im) => hz.le)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (confB_mem_slitStrip hz).1.le
    have htend_G : Tendsto (fun z : ℂ => G (confB z))
        (𝓝[{z : ℂ | 0 < z.im}] (σ : ℂ)) (𝓝 (G (confB (σ : ℂ)))) :=
      (hG_cont.continuousWithinAt (hconfB_im_real σ hnot)).tendsto.comp htend_B
    exact tendsto_const_nhds.mul htend_G
  have hFz₀_ne : F z₀ ≠ 0 := by
    dsimp [F]
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hb_ne
  obtain ⟨hPJ_int, hPJ_le⟩ := halfPlane_poissonJensen hMstrip_pos hF_diff hF_bd hF_bdy hz₀_im hFz₀_ne
  rw [hz₀_re, show z₀.im = y₀ by simp [z₀] ] at hPJ_int hPJ_le
  have hlhs_eq : Real.log ‖F z₀‖ =
      Real.log ‖G (confB z₀)‖ - Real.log M := by
    dsimp [F]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos,
      Real.log_mul (inv_ne_zero hM_pos.ne') (norm_pos_iff.mpr hb_ne).ne', Real.log_inv]
    ring
  rw [hlhs_eq] at hPJ_le
  have hsplit_eq : ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) +
        (∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set slitPreimage_union_edgePreimage_ae]
    exact setIntegral_union slitPreimage_disjoint_edgePreimage
      (measurableSet_Iio.union measurableSet_Ioo) hPJ_int.integrableOn hPJ_int.integrableOn
  -- 1. Edge bound:
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      (1 - m) * Real.log C_e0 + P.p_e * (1 - m) * Real.log c' := by
    have hint_edge := hPJ_int.integrableOn (s := edgePreimage)
    have hpk_edge : IntegrableOn (fun σ => Real.log M_strip * poissonKernel x₀ y₀ σ) edgePreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn.const_mul _
    have hpt_edge : ∀ σ ∈ edgePreimage,
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤ Real.log M_strip * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hσ with (hlt : σ < -1) | ⟨h0, h1⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
      have hbd_σ : ‖F_bdy σ‖ ≤ M_strip := by
        dsimp [F_bdy]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM_pos]
        calc M⁻¹ * ‖G (confB (σ : ℂ))‖
            ≤ M⁻¹ * (M_strip * M) := by gcongr; exact hG_strip_bd _ (hconfB_im_real σ hnot)
          _ = M_strip := by field_simp [hM_pos.ne']
      have hlog_le : Real.log ‖F_bdy σ‖ ≤ Real.log M_strip := by
        by_cases h0 : ‖F_bdy σ‖ = 0
        · rw [h0, Real.log_zero]; exact Real.log_nonneg hMstrip_ge1
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hbd_σ
      exact mul_le_mul_of_nonneg_right hlog_le (poissonKernel_nonneg hy₀_pos.le σ)
    have hmono := setIntegral_mono_on hint_edge hpk_edge
      (measurableSet_Iio.union measurableSet_Ioo) hpt_edge
    rw [integral_const_mul, ← one_sub_slitMass_eq_edgeMass'' hy₀_pos, ← show m = slitMass x₀ y₀ from rfl]
      at hmono
    have hMstrip_log : Real.log M_strip = Real.log C_e0 + P.p_e * Real.log c' := by
      dsimp [M_strip]
      rw [Real.log_mul hCe0_pos.ne' (Real.rpow_pos_of_pos hc0 _).ne', Real.log_rpow hc0]
    rw [hMstrip_log] at hmono
    linarith [hmono]
  -- 2. Slit bound:
  have hslit_confB : ∀ σ ∈ slitPreimage, confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := by
    intro σ hσ
    rcases hσ with hIoo | hIoi
    · have h0 : σ ≠ 0 := hIoo.2.ne
      have h1 : σ ≠ 1 := by linarith [hIoo.2]
      have hm1 : σ ≠ -1 := hIoo.1.ne'
      exact Complex.ext (confB_real_re h0 h1 hm1) (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · have hgt : 1 < σ := hIoi
      exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith))
        (confB_real_im_of_one_lt hgt)
  let C_slit : ℝ := 3 / (2 * xiStar * P.c_band)
  have hCslit_pos : 0 < C_slit := by dsimp [C_slit]; positivity [xiStar_pos, P.hc_band_pos]
  let K_of : ℝ → ℝ := fun t => kernelK prob.w (c' / 12) (c' * t ^ 2 / 3)
  let φ : ℝ → ℝ := fun t => (|g (c' * t ^ 2 / 3)| / M) * K_of t
  have hφ_cont : Continuous φ := by
    have hg_cont : Continuous (fun t : ℝ => g (c' * t ^ 2 / 3)) :=
      hg.cont.comp_continuous (by fun_prop) (fun t => by change 0 ≤ c' * t ^ 2 / 3; positivity)
    have hK_cont : Continuous K_of := (continuous_kernelK prob.w (c' / 12)).comp (by fun_prop)
    exact (hg_cont.abs.div_const M).mul hK_cont
  have hφ_meas : Measurable φ := hφ_cont.measurable
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun t _ => by
    dsimp [φ, K_of]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hM_pos.le)
      (kernelK_nonneg (by positivity) (by positivity))
  obtain ⟨heS_int, heS_le⟩ := eSlitMass_general prob P hg
  have hφ_int : IntegrableOn φ (Ioi xiStar) := by
    have hi : IntegrableOn (fun t => |g (c' * t ^ 2 / 3)| * K_of t / M) (Ioi xiStar) :=
      heS_int.div_const M
    exact hi.congr_fun (fun t _ => by dsimp [φ, K_of]; ring) measurableSet_Ioi
  have hIφ_le : 2 * ∫ t in Ioi xiStar, φ t ≤ 2 * C_slit * c'⁻¹ := by
    have hfun : EqOn φ (fun t => |g (c' * t ^ 2 / 3)| * K_of t / M) (Ioi xiStar) :=
      fun t _ => by dsimp [φ, K_of]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_div]
    calc 2 * ((∫ t in Ioi xiStar, |g (c' * t ^ 2 / 3)| * K_of t) / M)
        ≤ 2 * ((C_slit * c'⁻¹ * M) / M) := by gcongr
      _ = 2 * C_slit * c'⁻¹ := by field_simp [hM_pos.ne']
  obtain ⟨hf_pull_int, hf_pull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hy₀_pos hφ_meas hφ_nn hφ_int
  let K_val : ℝ → ℝ := fun σ => K_of |slitBoundaryMap σ|
  let f : ℝ → ℝ := fun σ => φ |slitBoundaryMap σ| / slitDensity x₀ y₀ σ
  have hK_pos : ∀ σ ∈ slitPreimage, 0 < K_val σ := fun σ hσ => by
    have hge := xiStar_pos.trans_le (abs_slitBoundaryMap_ge_xiStar' hσ)
    dsimp [K_val, K_of]
    exact kernelK_pos_of_pos prob.w (by positivity) (by positivity)
  have hFbdy_eq : ∀ σ ∈ slitPreimage,
      ‖F_bdy σ‖ = |g (c' * (slitBoundaryMap σ) ^ 2 / 3)| / M := fun σ hσ => by
    dsimp [F_bdy]
    rw [hslit_confB σ hσ, hG_real (slitBoundaryMap σ),
      norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hM_pos, inv_mul_eq_div]
  have hf_eq_Fbdy : ∀ σ ∈ slitPreimage, f σ = ‖F_bdy σ‖ * K_val σ / slitDensity x₀ y₀ σ := by
    intro σ hσ
    dsimp [f, φ, K_val]
    rw [hFbdy_eq σ hσ, sq_abs]
  have hG_ne_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      G (slitBoundaryMap σ : ℂ) ≠ 0 :=
    strip_ext_bdy_ne_zero_ae prob hG_diff hG_real (confB_mem_slitStrip hz₀_im).1 hb_ne
  have hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ := by
    have hω_pos := slitDensity_pos_ae (x := x₀) hy₀_pos
    have hmem_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), σ ∈ slitPreimage :=
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)
    filter_upwards [hG_ne_ae, hω_pos, hmem_ae] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]
      rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    exact div_pos (mul_pos hF_pos (hK_pos σ hσ)) hω
  have hlogK_int : IntegrableOn
      (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    have hident := identification_integrand_integrable x₀ hy₀_pos
    have hpk_int : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn
    let Ck : ℝ := (1 / 2 : ℝ) * |Real.log c'| + max C_Klo C_Kup
    let dom : ℝ → ℝ := fun σ =>
      (c' + (prob.w : ℝ) + 1) * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) +
        Ck * poissonKernel x₀ y₀ σ
    have hdom_int : IntegrableOn dom slitPreimage :=
      (hident.const_mul _).add (hpk_int.const_mul _)
    have hmeas_K_val : AEStronglyMeasurable
        (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) (volume.restrict slitPreimage) := by
      have hm_cont : Continuous K_of := (continuous_kernelK prob.w (c' / 12)).comp (by fun_prop)
      have hm_meas : Measurable K_val :=
        hm_cont.measurable.comp measurable_slitBoundaryMap.abs
      exact ((Real.measurable_log.comp hm_meas).mul
        (continuous_poissonKernel x₀ hy₀_pos).measurable).aestronglyMeasurable
    refine hdom_int.mono' hmeas_K_val ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hσ
    have hge := abs_slitBoundaryMap_ge_xiStar' hσ
    have hbL_eq : slitL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) := by
      unfold slitL; rw [abs_abs]
    have hL_pos : 0 < slitL (slitBoundaryMap σ) := by
      have hpos : 0 < |slitBoundaryMap σ| := xiStar_pos.trans_le hge
      unfold slitL; positivity
    have hbd_σ := hlogK_bd hc' hge
    rw [hbL_eq] at hbd_σ
    have hlogK_lo : -(((c' + (prob.w : ℝ) + 1) * slitL (slitBoundaryMap σ) + Ck)) ≤
        Real.log (K_val σ) := by
      have h1 : (1 / 2 : ℝ) * slitL (slitBoundaryMap σ) ≤
          ((prob.w : ℝ) + 1) * slitL (slitBoundaryMap σ) := by
        have hw1 : (1 / 2 : ℝ) ≤ (prob.w : ℝ) + 1 := by
          linarith [show (0 : ℝ) ≤ prob.w from Nat.cast_nonneg _]
        exact mul_le_mul_of_nonneg_right hw1 hL_pos.le
      dsimp [K_val, K_of, Ck]
      linarith [hbd_σ.1, le_abs_self (Real.log c'), le_max_left C_Klo C_Kup,
        mul_nonneg hc0.le hL_pos.le]
    have hlogK_hi : Real.log (K_val σ) ≤
        (c' + (prob.w : ℝ) + 1) * slitL (slitBoundaryMap σ) + Ck := by
      dsimp [K_val, K_of, Ck]
      have hlog_nn : 0 ≤ (1 / 2 : ℝ) * |Real.log c'| := by positivity
      linarith [hbd_σ.2, le_max_right C_Klo C_Kup, hlog_nn]
    have hlogK_abs : |Real.log (K_val σ)| ≤
        (c' + (prob.w : ℝ) + 1) * slitL (slitBoundaryMap σ) + Ck :=
      abs_le.mpr ⟨hlogK_lo, hlogK_hi⟩
    have hP0 := poissonKernel_nonneg (x := x₀) hy₀_pos.le σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    calc |Real.log (K_val σ)| * poissonKernel x₀ y₀ σ
        ≤ ((c' + (prob.w : ℝ) + 1) * slitL (slitBoundaryMap σ) + Ck) * poissonKernel x₀ y₀ σ := by
          gcongr
      _ = dom σ := by dsimp [dom]; ring
  have hlogω_int : IntegrableOn
      (fun σ => Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    (integrableOn_poisson_mul_log_slitDensity x₀ hy₀_pos).congr_fun
      (fun σ _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogF_slit_int : IntegrableOn
      (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) slitPreimage :=
    hPJ_int.integrableOn
  have hlogf_eq_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ =
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
          Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
    have hω_pos := slitDensity_pos_ae (x := x₀) hy₀_pos
    have hmem_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), σ ∈ slitPreimage :=
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)
    filter_upwards [hG_ne_ae, hω_pos, hmem_ae] with σ hG hω hσ
    rw [hf_eq_Fbdy σ hσ]
    have hF_pos : 0 < ‖F_bdy σ‖ := by
      dsimp [F_bdy]
      rw [hslit_confB σ hσ]
      exact norm_pos_iff.mpr (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hM_pos.ne')) hG)
    rw [Real.log_div (mul_pos hF_pos (hK_pos σ hσ)).ne' hω.ne',
      Real.log_mul hF_pos.ne' (hK_pos σ hσ).ne']
    ring
  have hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    refine ((hlogF_slit_int.sub hlogω_int).add hlogK_int).congr ?_
    filter_upwards [hlogf_eq_ae] with σ h
    exact h.symm
  have hjensen := log_integral_jensen_slitPreimage_aux hy₀_pos hf_pos_ae hf_pull_int hlogf_int
    (by positivity) (hf_pull_eq.le.trans hIφ_le)
  have hdecomp : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
        (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
        (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) := by
    have hFW_sub : IntegrableOn
        (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
      hlogF_slit_int.sub hlogω_int
    rw [integral_congr_ae hlogf_eq_ae, integral_add hFW_sub hlogK_int,
      integral_sub hlogF_slit_int hlogω_int]
    ring
  have hent_le : ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ ≤
      slitEntropy x₀ y₀ := by
    calc ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ * Real.log (slitDensity x₀ y₀ σ) :=
          integral_congr_ae (Eventually.of_forall fun σ => by ring)
      _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hy₀_pos
  have hlogK_lb : -(∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) ≤
      c' * U_val + (1 / 2 : ℝ) * m * Real.log c' + (1 / 2 : ℝ) * U_bd + C_Klo := by
    have hident := identification_integrand_integrable x₀ hy₀_pos
    have hpk_int : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn
    let rhs : ℝ → ℝ := fun σ =>
      c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
        ((1 / 2 : ℝ) * Real.log c' + C_Klo) * poissonKernel x₀ y₀ σ -
        (1 / 2 : ℝ) * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ)
    have hrhs_int : IntegrableOn rhs slitPreimage :=
      ((hident.const_mul c').sub (hpk_int.const_mul _)).sub (hident.const_mul _)
    have hpt : ∀ σ ∈ slitPreimage, rhs σ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ := by
      intro σ hσ
      have hge := abs_slitBoundaryMap_ge_xiStar' hσ
      have hbL_eq : slitL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) := by
        unfold slitL; rw [abs_abs]
      have hbd_σ := (hlogK_bd hc' hge).1
      rw [hbL_eq] at hbd_σ
      have hP0 := poissonKernel_nonneg (x := x₀) hy₀_pos.le σ
      calc rhs σ
          = (c' * slitL (slitBoundaryMap σ) - (1 / 2 : ℝ) * Real.log c' -
              (1 / 2 : ℝ) * slitL (slitBoundaryMap σ) - C_Klo) * poissonKernel x₀ y₀ σ := by
            dsimp [rhs]; ring
        _ ≤ Real.log (K_val σ) * poissonKernel x₀ y₀ σ :=
            mul_le_mul_of_nonneg_right hbd_σ hP0
    have hmono := setIntegral_mono_on hrhs_int hlogK_int
      (measurableSet_Ioo.union measurableSet_Ioi) hpt
    have hrhs_eval : ∫ σ in slitPreimage, rhs σ =
        c' * (∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
          ((1 / 2 : ℝ) * Real.log c' + C_Klo) * m -
          (1 / 2 : ℝ) * (∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) := by
      dsimp [rhs]
      have h12 : IntegrableOn
          (fun σ => c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) -
            ((1 / 2 : ℝ) * Real.log c' + C_Klo) * poissonKernel x₀ y₀ σ) slitPreimage :=
        (hident.const_mul c').sub (hpk_int.const_mul _)
      rw [integral_sub h12 (hident.const_mul _),
        integral_sub (hident.const_mul c') (hpk_int.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul]
      change _ - ((1 / 2 : ℝ) * Real.log c' + C_Klo) * slitMass x₀ y₀ - _ = _
      rfl
    rw [hrhs_eval] at hmono
    have hharm_eq : ∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ =
        -U_val := by linarith
    rw [hharm_eq] at hmono
    have hCKlo_m : C_Klo * m ≤ C_Klo := by
      calc C_Klo * m ≤ C_Klo * 1 := mul_le_mul_of_nonneg_left hm_le hCKlo
        _ = C_Klo := mul_one _
    linarith
  have hjensen_bd : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ ≤
      max 0 (Real.log (2 * C_slit)) - m * Real.log c' + 1 := by
    have h1 : m * Real.log (2 * C_slit * c'⁻¹) =
        m * Real.log (2 * C_slit) - m * Real.log c' := by
      rw [Real.log_mul (by positivity) (inv_ne_zero hc0.ne'), Real.log_inv]
      ring
    have h2 : m * Real.log (2 * C_slit) ≤ max 0 (Real.log (2 * C_slit)) := by
      have := mul_le_mul_of_nonneg_left (le_max_right 0 (Real.log (2 * C_slit))) hm_pos.le
      calc m * Real.log (2 * C_slit)
          ≤ m * max 0 (Real.log (2 * C_slit)) := this
        _ ≤ 1 * max 0 (Real.log (2 * C_slit)) :=
            mul_le_mul_of_nonneg_right hm_le (le_max_left _ _)
        _ = max 0 (Real.log (2 * C_slit)) := one_mul _
    have h3 : 1 - m ≤ 1 := by linarith [hm_pos]
    linarith [hjensen, h1, h2, h3]
  have hedge_const : (1 - m) * Real.log C_e0 ≤ max 0 (Real.log P.C_e) := by
    have hCe0_ge1 : 1 ≤ C_e0 := le_max_left _ _
    have hln_nn : 0 ≤ Real.log C_e0 := Real.log_nonneg hCe0_ge1
    have hCe0_log : Real.log C_e0 = max 0 (Real.log P.C_e) := by
      rcases le_total P.C_e 1 with hle | hge
      · have heq : C_e0 = 1 := max_eq_left hle
        rw [heq, Real.log_one]
        exact (max_eq_left (Real.log_nonpos P.hCe_pos.le hle)).symm
      · have heq : C_e0 = P.C_e := max_eq_right hge
        rw [heq]
        exact (max_eq_right (Real.log_nonneg hge)).symm
    calc (1 - m) * Real.log C_e0
        ≤ 1 * Real.log C_e0 := mul_le_mul_of_nonneg_right (by linarith [hm_pos]) hln_nn
      _ = max 0 (Real.log P.C_e) := by rw [one_mul, hCe0_log]
  have h2Cslit_eq : 2 * C_slit = 3 / (xiStar * P.c_band) := by
    dsimp [C_slit]; ring
  have hslit_le : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤
      c' * U_val - (1 / 2 : ℝ) * m * Real.log c' + slitEntropy x₀ y₀ +
        (max 0 (Real.log (3 / (xiStar * P.c_band))) + 1 + (1 / 2 : ℝ) * U_bd + C_Klo) := by
    rw [← h2Cslit_eq]
    linarith [hdecomp, hjensen_bd, hent_le, hlogK_lb]
  have hlogc_comb :
      P.p_e * (1 - m) * Real.log c' - (1 / 2 : ℝ) * m * Real.log c' =
        -(1 / 2 : ℝ) * Real.log c' + (P.p_e + 1 / 2) * (1 - m) * Real.log c' := by
    ring
  dsimp [pjConstOf]
  linarith [hPJ_le, hsplit_eq, hedge_le, hedge_const, hslit_le, hlogc_comb]

private lemma realSliceData_preimage_mem {x : ℝ} (hx : x ∈ Ico 0 xiStar) :
    0 < realSliceData.yUHP (xiStar - x) ∧
      confB ((realSliceData.xUHP (xiStar - x) : ℂ) +
        (realSliceData.yUHP (xiStar - x) : ℂ) * Complex.I) = (x : ℂ) := by
  have hδ : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hp := realSliceData_preimage hδ
  refine ⟨hp.1, ?_⟩
  simpa [sub_sub_cancel] using hp.2

private lemma neg_majorantReal_le {x : ℝ} (hx : x ∈ Ico 0 xiStar) :
    -majorantReal x ≤ slitL xiStar := by
  have hx_le : |x| ≤ xiStar := by rw [abs_of_nonneg hx.1]; exact hx.2.le
  rw [majorantReal_of_abs_le hx_le]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_arcsinSinh 0 |x|) (intervalIntegrable_arcsinSinh |x| xiStar)
  have hnn : 0 ≤ ∫ s in |x|..xiStar, arcsinSinh s :=
    intervalIntegral.integral_nonneg hx_le fun s hs => by
      have hpi := Real.pi_pos
      unfold arcsinSinh
      exact Real.arcsin_nonneg.mpr (Real.sinh_nonneg_iff.mpr (by nlinarith [hs.1, abs_nonneg x]))
  unfold majorantU0
  rw [← hsplit]
  linarith [hnn]

/-- **General-`(w, Q)` Real-`b` Lemma PJ** (`lower_o1_two_edge.tex`, Lemma `vlo:PJ` at fixed `(w, Q)`).
Given `P : PropositionPAxioms prob c'` with `c_Kw ≤ c'`, for any `g ∈ TestClass prob (c' / 12)`
with `M = M[g] > 0` and any `x ∈ [0, ξ_*)` with `g(c' x² / 3) ≠ 0`:
`log |g(c' x² / 3)| ≤ c' U_ℝ(x) + log M - (1/2) log c' + (p_e + 1/2)(1 - m(x)) log c' + H(x) + C_PJ`. -/
theorem stripPoissonJensen_general (prob : FixedWeightProblem) :
    ∃ c_Kw C_Klo : ℝ, 8 ≤ c_Kw ∧ 0 ≤ C_Klo ∧
      ∀ {c' : ℝ} (P : PropositionPAxioms prob c'), c_Kw ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
            Real.log |g (c' * x ^ 2 / 3)| ≤
              c' * majorantReal x + Real.log (prob.cardyNorm (c' / 12) g) -
                (1 / 2 : ℝ) * Real.log c' +
                (P.p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
                realSliceData.slitEntropyAt x + pjConstOf P.C_e P.c_band C_Klo (slitL xiStar) := by
  obtain ⟨C_Klo, C_Kup, c_Kw, hCKlo, hCKup, hcKw8, hlogK⟩ :=
    log_kernelK_slit_bounds prob.w prob.hw
  refine ⟨c_Kw, C_Klo, hcKw8, hCKlo, fun {c'} P hc' {g} hg hM_pos x hx hx_ne => ?_⟩
  obtain ⟨G, hG_cont, hG_diff, hG_real, hG_bd⟩ := P.p0_strip hg
  obtain ⟨hy₀_pos, hconfB_z₀⟩ := realSliceData_preimage_mem hx
  let x₀ : ℝ := realSliceData.xUHP (xiStar - x)
  let y₀ : ℝ := realSliceData.yUHP (xiStar - x)
  have hb_eq : confB ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I) = (x : ℂ) := hconfB_z₀
  have hG_eq : G (confB ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)) = (g (c' * x ^ 2 / 3) : ℂ) := by
    rw [hb_eq, hG_real x]
  have hb_ne : G (confB ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)) ≠ 0 := by
    rw [hG_eq]; exact Complex.ofReal_ne_zero.mpr hx_ne
  have hharm : -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ =
      majorantReal x := (harmonicMajorantIdentification x hx).symm
  have hcore := halfPlane_pj_core prob P hCKlo hCKup hcKw8 hlogK hc' hg hM_pos
    hG_cont hG_diff hG_real hG_bd x₀ y₀ hy₀_pos hb_ne
    (majorantReal x) (slitL xiStar) hharm (neg_majorantReal_le hx)
  rw [hG_eq, Complex.norm_real, Real.norm_eq_abs] at hcore
  change Real.log |g (c' * x ^ 2 / 3)| - Real.log (prob.cardyNorm (c' / 12) g) ≤ _ at hcore
  change Real.log |g (c' * x ^ 2 / 3)| ≤
    c' * majorantReal x + Real.log (prob.cardyNorm (c' / 12) g) - (1 / 2 : ℝ) * Real.log c' +
      (P.p_e + 1 / 2) * (1 - slitMass x₀ y₀) * Real.log c' +
      slitEntropy x₀ y₀ + pjConstOf P.C_e P.c_band C_Klo (slitL xiStar)
  linarith [hcore]

/-- **General-`(w, Q)` Complex-`b` Lemma PJ** (`lower_o1_two_edge.tex`, Lemma `vlo:PJ` at complex
tip points `b = slitBoundaryMapC z` with `0 < z.im`, `‖z - σ_*‖ ≤ 0.1`, `|b.im| < 1/2`). -/
theorem stripPoissonJensen_complex_general (prob : FixedWeightProblem) :
    ∃ c_Kw C_Klo : ℝ, 8 ≤ c_Kw ∧ 0 ≤ C_Klo ∧
      ∀ {c' : ℝ} (P : PropositionPAxioms prob c'), c_Kw ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          ∀ {z : ℂ}, 0 < z.im → ‖z - (sigmaStar : ℂ)‖ ≤ 0.1 →
            |(slitBoundaryMapC z).im| < 1 / 2 →
            hankelContinuationW prob.w c' g (slitBoundaryMapC z) ≠ 0 →
            Real.log ‖hankelContinuationW prob.w c' g (slitBoundaryMapC z)‖ ≤
              c' * majorant2D (slitBoundaryMapC z) + Real.log (prob.cardyNorm (c' / 12) g) -
                (1 / 2 : ℝ) * Real.log c' +
                (P.p_e + 1 / 2) * (1 - slitMass z.re z.im) * Real.log c' +
                slitEntropy z.re z.im +
                pjConstOf P.C_e P.c_band C_Klo
                  (|majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2) := by
  obtain ⟨C_Klo, C_Kup, c_Kw, hCKlo, hCKup, hcKw8, hlogK⟩ :=
    log_kernelK_slit_bounds prob.w prob.hw
  obtain ⟨c₀_diff, _, hdiff_W⟩ := WeightAxioms.differentiableOn_hankelContinuationW prob
  let C_U : ℝ := |majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2
  refine ⟨max c_Kw c₀_diff, C_Klo, le_trans hcKw8 (le_max_left _ _), hCKlo,
    fun {c'} P hc' {g} hg hM_pos {z} hz_im hz_tip hb_im hb_ne => ?_⟩
  have hcKw' : c_Kw ≤ c' := (le_max_left _ _).trans hc'
  have hc0' : c₀_diff ≤ c' := (le_max_right _ _).trans hc'
  obtain ⟨G, hG_cont, hG_diff, hG_real, hG_bd⟩ := P.p0_strip hg
  have hGW := strip_ext_eq_hankelContinuationW prob P.hc'_pos (hdiff_W hc0' hg) hg hG_diff hG_real
  have hG_at_z : G (slitBoundaryMapC z) = hankelContinuationW prob.w c' g (slitBoundaryMapC z) :=
    hGW hb_im
  have hb_eq : confB ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = slitBoundaryMapC z := by
    rw [Complex.re_add_im z, slitBoundaryMapC_eq_confB hz_im]
  have hb_ne' : G (confB ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) ≠ 0 := by
    rw [hb_eq, hG_at_z]; exact hb_ne
  have hharm : -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel z.re z.im σ =
      majorant2D (slitBoundaryMapC z) := by
    rw [slitBoundaryMapC_eq_confB hz_im]
    exact (harmonicMajorantIdentification_complex hz_im).symm
  have hU_bd : -majorant2D (slitBoundaryMapC z) ≤ C_U := by
    rw [slitBoundaryMapC_eq_confB hz_im]
    have hbd := majorant2D_abs_le (confB_mem_slitStrip hz_im)
    have hre := abs_confB_re_le_of_tip_ball hz_im hz_tip
    have hneg := neg_le_abs (majorant2D (confB z))
    calc -majorant2D (confB z) ≤ |majorant2D (confB z)| := hneg
      _ ≤ |majorantU0| + (4 * π / 3) * (|(confB z).re| + 2) ^ 2 := hbd
      _ ≤ |majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2 := by gcongr
  have hcore := halfPlane_pj_core prob P hCKlo hCKup hcKw8 hlogK hcKw' hg hM_pos
    hG_cont hG_diff hG_real hG_bd z.re z.im hz_im hb_ne' (majorant2D (slitBoundaryMapC z)) C_U
    hharm hU_bd
  rw [hb_eq, hG_at_z] at hcore
  linarith

/-! ### 4. General Proposition M and Lemma G for every `δ ∈ (0, ξ_*)` -/

/-- **General Proposition M (`proposition_M_general`)**: passes from Lemma PJ with arbitrary
edge exponent factor `(p_e + 1/2)` to explicit `C_M1 * √(ξ_* - x) log c' + log(1/(ξ_* - x)) + C_M2`. -/
theorem proposition_M_general (rs : RealSliceData) {c_PJ C_PJ p_e : ℝ}
    (hc_PJ : 1 ≤ c_PJ) (hp_e : 0 ≤ p_e) :
    ∃ C_M1 C_M2 : ℝ, 0 ≤ C_M1 ∧
      ∀ {c' M : ℝ} {U g : ℝ → ℝ}, c_PJ ≤ c' → 0 < M →
        (∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
          Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            (p_e + 1 / 2) * (1 - rs.slitMassAt x) * Real.log c' + rs.slitEntropyAt x + C_PJ) →
        ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
          Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            C_M1 * Real.sqrt (xiStar - x) * Real.log c' + Real.log (1 / (xiStar - x)) + C_M2 := by
  obtain ⟨C_E, _, hE⟩ := lemmaE_real rs.hC_e rs.hc_y rs.hC_y rs.re_bound rs.im_lower rs.im_upper
  obtain ⟨_, C_S', hS⟩ := lemmaS_real rs.hC_e rs.hc_y rs.hC_y rs.re_bound rs.im_lower rs.im_upper
  refine ⟨(p_e + 1 / 2) * C_E, C_S' + C_PJ, by positivity, fun {c' M U g} hc' _ hPJ x hx hne => ?_⟩
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg (hc_PJ.trans hc')
  have hδ : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hm_raw : 1 - rs.slitMassAt x ≤ C_E * Real.sqrt (xiStar - x) := hE (xiStar - x) hδ
  have hm_term : (p_e + 1 / 2) * (1 - rs.slitMassAt x) * Real.log c' ≤
      (p_e + 1 / 2) * C_E * Real.sqrt (xiStar - x) * Real.log c' :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_raw (by positivity))
      hlogc'_nn).trans_eq (by ring)
  have hS_ub : rs.slitEntropyAt x ≤ Real.log (1 / (xiStar - x)) + C_S' :=
    (hS (xiStar - x) hδ).1.trans (hS (xiStar - x) hδ).2
  linarith [hPJ x hx hne, hm_term, hS_ub]

/-- Helper turning `stripPoissonJensen_general` and `proposition_M_general` into an
exponential pointwise bound on `|g(c' x^2 / 3)|` on `[0, ξ_*)`. -/
lemma proposition_M_exp_general (rs : RealSliceData) {c_PJ C_PJ p_e : ℝ}
    (hc_PJ : 1 ≤ c_PJ) (hp_e : 0 ≤ p_e) :
    ∃ C_M1 C_M2 : ℝ, 0 ≤ C_M1 ∧
      ∀ {c' M : ℝ} {U g : ℝ → ℝ}, c_PJ ≤ c' → 0 < M →
        (∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
          Real.log |g (c' * x ^ 2 / 3)| ≤ c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            (p_e + 1 / 2) * (1 - rs.slitMassAt x) * Real.log c' + rs.slitEntropyAt x + C_PJ) →
        ∀ x ∈ Ico 0 xiStar,
          |g (c' * x ^ 2 / 3)| ≤
            Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
              Real.exp (c' * U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
  obtain ⟨C_M1, C_M2, hCM1, hprop⟩ := proposition_M_general rs hc_PJ hp_e
  refine ⟨C_M1, C_M2, hCM1, fun {c' M U g} hc' hM hPJ x hx => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hdx : 0 < xiStar - x := sub_pos.mpr hx.2
  by_cases hg0 : g (c' * x ^ 2 / 3) = 0
  · rw [hg0, abs_zero]
    positivity
  · have hlog := hprop hc' hM hPJ x hx hg0
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (abs_pos.mpr hg0)] at hexp
    have hc_pow : Real.exp (-(1 / 2 : ℝ) * Real.log c') = c' ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_def_of_pos hc0]; ring_nf
    have hdx_eq : Real.exp (Real.log (1 / (xiStar - x))) = (xiStar - x)⁻¹ := by
      rw [one_div, Real.exp_log (inv_pos.mpr hdx)]
    calc |g (c' * x ^ 2 / 3)|
        ≤ Real.exp (c' * U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
            C_M1 * Real.sqrt (xiStar - x) * Real.log c' + Real.log (1 / (xiStar - x)) + C_M2) :=
          hexp
      _ = Real.exp C_M2 * Real.exp (Real.log M) * Real.exp (-(1 / 2 : ℝ) * Real.log c') *
            Real.exp (Real.log (1 / (xiStar - x))) *
            Real.exp (c' * U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1; ring
      _ = Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
            Real.exp (c' * U x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
          rw [Real.exp_log hM, hc_pow, hdx_eq]

private lemma cardyV_nonneg_of_p1_pos {prob : FixedWeightProblem} {c' : ℝ}
    (P : PropositionPAxioms prob c') {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ prob.cardyV (c' / 12) t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · have hlim : Tendsto (prob.cardyV (c' / 12)) (𝓝[>] (0 : ℝ)) (𝓝 (prob.cardyV (c' / 12) 0)) :=
      (continuous_cardyV prob (c' / 12)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs => (P.p1_pos hs).le)
  · exact (P.p1_pos ht_pos).le

private lemma cut_integral_zero_of_norm_zero (prob : FixedWeightProblem) {c' : ℝ}
    (P : PropositionPAxioms prob c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM0 : ¬ 0 < prob.cardyNorm (c' / 12) g) {x₀ : ℝ} (_hx₀ : 0 ≤ x₀) :
    ∫ t in (0 : ℝ)..(c' * x₀ ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t = 0 := by
  have hc0 : 0 < c' := P.hc'_pos
  have ht₀nn : 0 ≤ c' * x₀ ^ 2 / 3 := by positivity
  have hMnn : 0 ≤ prob.cardyNorm (c' / 12) g := by
    unfold FixedWeightProblem.cardyNorm
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (P.p1_pos ht).le
  have hMeq0 : prob.cardyNorm (c' / 12) g = 0 := le_antisymm (not_lt.mp hM0) hMnn
  have hint_Ioc : IntegrableOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioc 0 (c' * x₀ ^ 2 / 3)) :=
    hg.int_cardy.mono_set Ioc_subset_Ioi_self
  have hnonneg : ∀ t ∈ Ioc (0 : ℝ) (c' * x₀ ^ 2 / 3), 0 ≤ |g t| * prob.cardyV (c' / 12) t :=
    fun t ht => mul_nonneg (abs_nonneg _) (P.p1_pos ht.1).le
  have hle_M : ∫ t in Ioc 0 (c' * x₀ ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t ≤
      prob.cardyNorm (c' / 12) g := by
    unfold FixedWeightProblem.cardyNorm
    refine setIntegral_mono_set hg.int_cardy ?_ Ioc_subset_Ioi_self.eventuallySubset
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (P.p1_pos ht).le
  have hnonneg_int : 0 ≤ ∫ t in Ioc 0 (c' * x₀ ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t :=
    setIntegral_nonneg measurableSet_Ioc hnonneg
  rw [intervalIntegral.integral_of_le ht₀nn]
  linarith

/-- **General-`(w, Q)` Lemma G for every fixed gap `δ ∈ (0, ξ_*)`** (`lower_o1_two_edge.tex`,
Lemma `vlo:Gap`, uniform over any family of `PropositionPAxioms` with uniform `(C_e, p_e, c_band, C_up, p_u)`).
Produces explicit constants `c_deep ≥ 1`, `C_deep > 0`, `κ_deep > 0` such that
`∫₀^{c' (ξ_* - δ)² / 3} |g(t)| V(t) dt ≤ C_deep e^{-κ_deep c'} M[g]`. -/
theorem lemmaG_general_of_uniform (prob : FixedWeightProblem)
    {c₀ C_e p_e c_band C_up p_u : ℝ}
    (hc₀ : 1 ≤ c₀) (_hCe : 0 < C_e) (hpe : 0 ≤ p_e)
    (_hcb : 0 < c_band) (hCup : 0 < C_up) (hpu : 0 ≤ p_u)
    (hP : ∀ {c' : ℝ}, c₀ ≤ c' →
      ∃ P : PropositionPAxioms prob c',
        P.C_e = C_e ∧ P.p_e = p_e ∧ P.c_band = c_band ∧ P.C_up = C_up ∧ P.p_u = p_u)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < xiStar) :
    ∃ c_deep C_deep κ_deep : ℝ, 1 ≤ c_deep ∧ 0 < C_deep ∧ 0 < κ_deep ∧
      ∀ {c' : ℝ}, c_deep ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          ∫ t in (0 : ℝ)..(c' * (xiStar - δ) ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t ≤
            C_deep * Real.exp (-κ_deep * c') * prob.cardyNorm (c' / 12) g := by
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general prob
  let C_PJ : ℝ := pjConstOf C_e c_band C_Klo (slitL xiStar)
  let c_PJ : ℝ := max c₀ c_Kw
  have hcPJ1 : 1 ≤ c_PJ := le_trans hc₀ (le_max_left _ _)
  obtain ⟨C_M1, C_M2, hCM1, hpropM⟩ := proposition_M_exp_general realSliceData
    (C_PJ := C_PJ) (p_e := p_e) hcPJ1 hpe
  let κ₀ : ℝ := 2.228 * δ ^ ((3 : ℝ) / 2)
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, hC₄, hC₄le⟩ := exists_rpow_le_mul_exp (p := C_M1 + p_u + 1) (κ := κ₀ / 2)
    (by positivity)
  have hC₄_pos : 0 < C₄ := by
    have h1 := hC₄le 1 le_rfl
    simp only [Real.one_rpow] at h1
    have hexp_pos : 0 < Real.exp (κ₀ / 2 * 1) := Real.exp_pos _
    nlinarith
  let x₀ : ℝ := xiStar - δ
  have hx₀_pos : 0 < x₀ := sub_pos.mpr hδ1
  let c_deep : ℝ := c_PJ
  let C_deep : ℝ := (2 / δ) * Real.exp C_M2 * C_up * 2 ^ (prob.w + 1) * C₄
  let κ_deep : ℝ := κ₀ / 2
  refine ⟨c_deep, C_deep, κ_deep, hcPJ1,
    by dsimp [C_deep]; exact mul_pos (mul_pos (mul_pos (mul_pos (div_pos (by norm_num : (0 : ℝ) < 2) hδ0) (Real.exp_pos _)) hCup) (pow_pos (by norm_num : (0 : ℝ) < 2) _)) hC₄_pos,
    by dsimp [κ_deep]; exact half_pos hκ₀, fun {c'} hc' {g} hg => ?_⟩
  have hc₀' : c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hcKw' : c_Kw ≤ c' := (le_max_right _ _).trans hc'
  have hc1 : 1 ≤ c' := hcPJ1.trans hc'
  have hc0 : 0 < c' := by linarith
  obtain ⟨P, hPCe, hPpe, hPcb, hPCup, hPpu⟩ := hP hc₀'
  by_cases hMpos : 0 < prob.cardyNorm (c' / 12) g
  swap
  · have hzero := cut_integral_zero_of_norm_zero prob P hg hMpos hx₀_pos.le
    rw [hzero]
    have hMnn : 0 ≤ prob.cardyNorm (c' / 12) g := by
      unfold FixedWeightProblem.cardyNorm
      exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (P.p1_pos ht).le
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hMnn
  set M : ℝ := prob.cardyNorm (c' / 12) g
  have hPJ_at : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤ c' * majorantReal x + Real.log M -
        (1 / 2 : ℝ) * Real.log c' +
        (p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
        realSliceData.slitEntropyAt x + C_PJ := by
    intro x hx hx_ne
    have h := hPJ_thm P hcKw' hg hMpos x hx hx_ne
    rwa [hPCe, hPpe, hPcb] at h
  have hexp_bd := hpropM hc' hMpos hPJ_at
  let t₀ : ℝ := c' * x₀ ^ 2 / 3
  have ht₀_nn : 0 ≤ t₀ := by positivity
  -- Change of variables `t = c' * x^2 / 3` on `[0, x₀]`.
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
  have hsub : ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x =
      ∫ t in (0 : ℝ)..t₀, |g t| * prob.cardyV (c' / 12) t := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) x₀, HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']
      exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hcont_φ' : ContinuousOn φ' (uIcc (0 : ℝ) x₀) := by dsimp [φ']; fun_prop
    have hcont_f : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (φ '' uIcc 0 x₀) := by
      refine (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
      rintro t ⟨x, _, rfl⟩
      exact mem_Ici.mpr (div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num))
    have hcov := intervalIntegral.integral_comp_mul_deriv' hd hcont_φ' hcont_f
    simpa [φ, t₀] using hcov
  rw [← hsub]
  have hpt : ∀ x ∈ Icc (0 : ℝ) x₀,
      (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x ≤
        Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
          (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · have hφ0 : φ' 0 = 0 := by dsimp [φ']; ring
      rw [hφ0, mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le hMpos.le) (Real.rpow_nonneg hc0.le _)) (inv_nonneg.mpr hδ0.le))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCup.le) (Real.rpow_nonneg hc0.le _))
          (pow_nonneg (by norm_num) _))) hc0.le) (Real.exp_pos _).le
    have hx_mem : x ∈ Ico 0 xiStar := ⟨hx.1, hx.2.trans_lt (by linarith)⟩
    have hx_lt1 : x < 1 := hx_mem.2.trans xiStar_lt_one
    have hx_pos_δ : δ ≤ xiStar - x := by dsimp [x₀] at hx; linarith [hx.2]
    have hMexp := hexp_bd x hx_mem
    have hUdef : majorantReal x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x) :=
      majorantReal_g_deficit hx_mem
    have hslit_def := slitDeficit_ge (le_trans hδ0.le hx_pos_δ) (by linarith [hx.1])
    have hδ_rpow : δ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hδ0.le hx_pos_δ (by norm_num)
    have hU_le : majorantReal x + (2 * π / 3) * x ≤ -κ₀ := by
      calc majorantReal x + (2 * π / 3) * x
          ≤ -slitDeficit (xiStar - x) := hUdef
        _ ≤ -(2.228 * (xiStar - x) ^ ((3 : ℝ) / 2)) := neg_le_neg hslit_def
        _ ≤ -(2.228 * δ ^ ((3 : ℝ) / 2)) :=
            neg_le_neg (mul_le_mul_of_nonneg_left hδ_rpow (by norm_num))
        _ = -κ₀ := rfl
    have hsqrt_le : Real.sqrt (xiStar - x) ≤ 1 := by
      have hle1 : xiStar - x ≤ 1 := by linarith [hx.1, xiStar_lt_one]
      calc Real.sqrt (xiStar - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle1
        _ = 1 := Real.sqrt_one
    have hinv_le : (xiStar - x)⁻¹ ≤ δ⁻¹ :=
      inv_anti₀ hδ0 hx_pos_δ
    have hdx_pos : 0 < xiStar - x := lt_of_lt_of_le hδ0 hx_pos_δ
    have hφx_pos : 0 < φ x := by dsimp [φ]; exact div_pos (mul_pos hc0 (sq_pos_of_pos hx_pos)) (by norm_num)
    have hV_le : prob.cardyV (c' / 12) (φ x) ≤
        2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1) * Real.exp (c' * (2 * π / 3) * x) := by
      have ht_le_x : φ x ≤ c' * xiStar ^ 2 / 3 := by
        dsimp [φ]
        have hxle : x ≤ xiStar := hx_mem.2.le
        have hxsq : x ^ 2 ≤ xiStar ^ 2 := by nlinarith [hx.1, hxle]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxsq hc0.le) (by norm_num)
      have ht_le_bar : φ x ≤ xiBar * c' := by
        have heq : xiBar * c' = c' * xiStar ^ 2 / 3 := by unfold xiBar; ring
        linarith [ht_le_x]
      have hφx_nn : 0 ≤ φ x := hφx_pos.le
      have hPup := P.p1_up hφx_pos ht_le_bar
      rw [hPCup, hPpu] at hPup
      have h1cpu : 1 + c' ^ p_u ≤ 2 * c' ^ p_u := by
        have h1le : 1 ≤ c' ^ p_u := Real.one_le_rpow hc1 hpu
        linarith
      have hK_ub := WeightAxioms.kernelK_le_pow_mul_exp prob.hw (by positivity : 0 < c' / 12) hφx_nn
      have hs1 : Real.sqrt ((φ x) / (c' / 12)) ≤ 2 := by
        have heq : (φ x) / (c' / 12) = (2 * x) ^ 2 := by
          dsimp [φ]; field_simp [hc0.ne']; ring
        rw [heq, Real.sqrt_sq (by linarith [hx_pos])]
        linarith [hx_lt1]
      have hs2 : 4 * π * Real.sqrt ((c' / 12) * (φ x)) = c' * (2 * π / 3) * x := by
        have heq : (c' / 12) * (φ x) = (c' * x / 6) ^ 2 := by dsimp [φ]; ring
        rw [heq, Real.sqrt_sq (by positivity [hx_pos])]
        ring
      rw [hs2] at hK_ub
      have hK_ub2 : kernelK prob.w (c' / 12) (φ x) ≤
          2 ^ (prob.w - 1) * Real.exp (c' * (2 * π / 3) * x) :=
        hK_ub.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs1 _) (Real.exp_pos _).le)
      calc prob.cardyV (c' / 12) (φ x)
          ≤ C_up * (1 + c' ^ p_u) * kernelK prob.w (c' / 12) (φ x) := hPup
        _ ≤ C_up * (2 * c' ^ p_u) * (2 ^ (prob.w - 1) * Real.exp (c' * (2 * π / 3) * x)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1cpu hCup.le) hK_ub2
              (kernelK_nonneg (by positivity) hφx_nn) (by positivity)
        _ = 2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1) * Real.exp (c' * (2 * π / 3) * x) := by
            ring
    have hexp_comb :
        Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
          Real.exp (c' * (2 * π / 3) * x) ≤
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : c' * (majorantReal x + (2 * π / 3) * x) ≤ c' * (-κ₀) :=
        mul_le_mul_of_nonneg_left hU_le hc0.le
      have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc1
      have h2 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
        calc C_M1 * Real.sqrt (xiStar - x) * Real.log c'
            ≤ C_M1 * 1 * Real.log c' := by gcongr
          _ = C_M1 * Real.log c' := by ring
      linarith
    have hφx_nn : 0 ≤ φ x := div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
    have hV_nn : 0 ≤ prob.cardyV (c' / 12) (φ x) := cardyV_nonneg_of_p1_pos P hφx_nn
    have hgV : |g (φ x)| * prob.cardyV (c' / 12) (φ x) ≤
        Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
          (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
      calc |g (φ x)| * prob.cardyV (c' / 12) (φ x)
          ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
              Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
              (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1) * Real.exp (c' * (2 * π / 3) * x)) :=
            mul_le_mul hMexp hV_le hV_nn (by positivity [hdx_pos])
        _ = (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹) *
              (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) *
              (Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                Real.exp (c' * (2 * π / 3) * x)) := by ring
        _ ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹) *
              (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) *
              Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by gcongr
        _ = _ := by ring
    have hφ'_le : φ' x ≤ c' := by
      dsimp [φ']
      nlinarith [hx_lt1, hc0]
    have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity [hx_pos]
    have hgV_nn : 0 ≤ |g (φ x)| * prob.cardyV (c' / 12) (φ x) :=
      mul_nonneg (abs_nonneg _) hV_nn
    calc (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x
        ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
            (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) *
            Real.exp (-κ₀ * c' + C_M1 * Real.log c')) * c' :=
          mul_le_mul hgV hφ'_le hφ'_nn (by positivity)
      _ = _ := by ring
  have hcont_lhs : ContinuousOn (fun x => (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x)
      (uIcc 0 x₀) := by
    have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := fun x =>
      div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
    have h1 : ContinuousOn (fun x => g (φ x)) (uIcc 0 x₀) :=
      hg.cont.comp (by dsimp [φ]; fun_prop) (fun x _ => mem_Ici.mpr (hφ_nonneg x))
    exact ((h1.abs.mul ((continuous_cardyV prob (c' / 12)).continuousOn.comp
      (by dsimp [φ]; fun_prop) (fun _ _ => mem_univ _)))).mul (by dsimp [φ']; fun_prop)
  have hint_bd : ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x ≤
      x₀ * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
        (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) * c' *
        Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by
    have hmono := intervalIntegral.integral_mono_on hx₀_pos.le
      (hcont_lhs.intervalIntegrable (μ := volume)) (intervalIntegrable_const (μ := volume)) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    exact hmono
  have hx₀_le1 : x₀ ≤ 1 := by dsimp [x₀]; linarith [xiStar_lt_one]
  have hcm_eq : Real.exp (C_M1 * Real.log c') = c' ^ C_M1 := by
    rw [Real.rpow_def_of_pos hc0]; ring_nf
  have hpow_comb : c' ^ (-(1 / 2 : ℝ)) * c' ^ p_u * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c') ≤
      C₄ * Real.exp (-κ_deep * c') := by
    have hcm1_nn : c' ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hpow_tot : c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c' ^ p_u * c') ≤
        c' ^ (C_M1 + p_u + 1) := by
      have heq : c' ^ C_M1 * c' ^ p_u * c' = c' ^ (C_M1 + p_u + 1) := by
        calc c' ^ C_M1 * c' ^ p_u * c'
            = (c' ^ C_M1 * c' ^ p_u) * c' ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = c' ^ (C_M1 + p_u) * c' ^ (1 : ℝ) := by rw [← Real.rpow_add hc0]
          _ = c' ^ (C_M1 + p_u + 1) := by rw [← Real.rpow_add hc0]
      calc c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c' ^ p_u * c')
          ≤ 1 * (c' ^ C_M1 * c' ^ p_u * c') := by gcongr
        _ = c' ^ (C_M1 + p_u + 1) := by rw [one_mul, heq]
    have hc4 := hC₄le c' hc1
    calc c' ^ (-(1 / 2 : ℝ)) * c' ^ p_u * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c')
        = (c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c' ^ p_u * c')) * Real.exp (-κ₀ * c') := by
          rw [Real.exp_add, hcm_eq]; ring
      _ ≤ (C₄ * Real.exp ((κ₀ / 2) * c')) * Real.exp (-κ₀ * c') := by
          exact mul_le_mul (hpow_tot.trans hc4) le_rfl (Real.exp_pos _).le (by positivity)
      _ = C₄ * Real.exp (-κ_deep * c') := by
          rw [mul_assoc, ← Real.exp_add]
          dsimp [κ_deep]
          congr 2; ring
  have h2w : (2 : ℝ) ^ (prob.w - 1) ≤ (2 : ℝ) ^ (prob.w + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * prob.cardyV (c' / 12) (φ x)) * φ' x
      ≤ x₀ * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
          (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := hint_bd
    _ ≤ 1 * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
          (2 * C_up * c' ^ p_u * 2 ^ (prob.w - 1)) * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by gcongr
    _ = ((2 / δ) * Real.exp C_M2 * C_up * 2 ^ (prob.w - 1) * M) *
          (c' ^ (-(1 / 2 : ℝ)) * c' ^ p_u * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by
          ring
    _ ≤ ((2 / δ) * Real.exp C_M2 * C_up * 2 ^ (prob.w + 1) * M) *
          (C₄ * Real.exp (-κ_deep * c')) := by
          refine mul_le_mul ?_ hpow_comb (by positivity) (by positivity)
          gcongr
    _ = C_deep * Real.exp (-κ_deep * c') * M := by dsimp [C_deep]; ring

/-- Unconditional general-`(w, Q)` **Lemma G** for every `prob : FixedWeightProblem` and every
fixed gap `δ ∈ (0, ξ_*)` (`lower_o1_two_edge.tex`, Lemma `vlo:Gap`). -/
theorem lemmaG_of_problem (prob : FixedWeightProblem) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < xiStar) :
    ∃ c_deep C_deep κ_deep : ℝ, 1 ≤ c_deep ∧ 0 < C_deep ∧ 0 < κ_deep ∧
      ∀ {c' : ℝ}, c_deep ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          ∫ t in (0 : ℝ)..(c' * (xiStar - δ) ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t ≤
            C_deep * Real.exp (-κ_deep * c') * prob.cardyNorm (c' / 12) g := by
  obtain ⟨U⟩ := WeightAxioms.fixedWeightAxioms_of_problem prob
  have hP : ∀ {c' : ℝ}, max 1 U.c₀ ≤ c' →
      ∃ P : PropositionPAxioms prob c',
        P.C_e = U.C_e ∧ P.p_e = U.p_e ∧ P.c_band = U.c_band ∧ P.C_up = U.C_up ∧ P.p_u = U.p_u := by
    intro c' hc'
    have hc₀' : U.c₀ ≤ c' := (le_max_right _ _).trans hc'
    refine ⟨(U.axioms_at hc₀').toPropositionPAxioms, ?_, ?_, ?_, ?_, ?_⟩
    · exact U.uniform_C_e hc₀'
    · exact U.uniform_p_e hc₀'
    · exact U.uniform_c_band hc₀'
    · exact U.uniform_C_up hc₀'
    · exact U.uniform_p_u hc₀'
  exact lemmaG_general_of_uniform prob (le_max_left 1 U.c₀) U.hCe_pos U.hp_e_nn
    U.hc_band_pos U.hCup_pos U.hp_u_nn hP hδ0 hδ1

/-! ### 5. Unconditional General-`(w, Q)` Theorem A (`t₁ ≥ ξ̄ c' - C_A c'^{1/3}`) -/

/-- Any nonzero `TestClass prob a g` with `prob.totalShift ≤ a` has strictly positive `M[g]`. -/
lemma cardyNorm_pos_of_nonzero_general (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) {g : ℝ → ℝ} (hg : TestClass prob a g)
    (hnonzero : ∃ t ≥ 0, g t ≠ 0) :
    0 < prob.cardyNorm a g := by
  unfold FixedWeightProblem.cardyNorm
  have hint : IntegrableOn (fun t => |g t| * prob.cardyV a t) (Ioi 0) := hg.int_cardy
  have hcont : ContinuousOn (fun t => |g t| * prob.cardyV a t) (Ioi 0) :=
    (hg.cont.abs.mul (continuous_cardyV prob a).continuousOn).mono Ioi_subset_Ici_self
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ |g t| * prob.cardyV a t := fun t ht =>
    mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg ha (mem_Ioi.mp ht).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg) hint]
  obtain ⟨t₀, ht₀, hgt₀⟩ := hnonzero
  have hmem_t₀ : t₀ ∈ Ici (0 : ℝ) := ht₀
  have hcont_t₀ : ContinuousWithinAt g (Ici 0) t₀ := hg.cont.continuousWithinAt hmem_t₀
  obtain ⟨r, hr_pos, hr_ne⟩ := Metric.continuousWithinAt_iff.mp hcont_t₀ (|g t₀| / 2) (by positivity [abs_pos.mpr hgt₀])
  let t₁ : ℝ := t₀ + r / 2
  have ht₁_pos : 0 < t₁ := by dsimp [t₁]; linarith
  have ht₁_mem : t₁ ∈ Ici (0 : ℝ) := ht₁_pos.le
  have ht₁_dist : dist t₁ t₀ < r := by
    dsimp [t₁]
    rw [Real.dist_eq, show t₀ + r / 2 - t₀ = r / 2 by ring, abs_of_pos (half_pos hr_pos)]
    linarith
  have hgt₁ : g t₁ ≠ 0 := by
    have hlt := hr_ne ht₁_mem ht₁_dist
    rw [Real.dist_eq] at hlt
    intro h0
    rw [h0, zero_sub, abs_neg] at hlt
    linarith [abs_pos.mpr hgt₀]
  have hV_pos : 0 < prob.cardyV a t₁ := prob.cardyV_pos ha ht₁_pos
  have hf_pos : 0 < |g t₁| * prob.cardyV a t₁ := mul_pos (abs_pos.mpr hgt₁) hV_pos
  have hsupp_nonempty : ∃ δ > 0, Ioo (t₁ - δ) (t₁ + δ) ⊆
      Function.support (fun t => |g t| * prob.cardyV a t) ∩ Ioi 0 := by
    have hcont_at : ContinuousAt (fun t => |g t| * prob.cardyV a t) t₁ :=
      hcont.continuousAt (Ioi_mem_nhds ht₁_pos)
    obtain ⟨ε, hε_pos, hε⟩ := Metric.continuousAt_iff.mp hcont_at
      (|g t₁| * prob.cardyV a t₁ / 2) (half_pos hf_pos)
    refine ⟨min ε (t₁ / 2), lt_min hε_pos (half_pos ht₁_pos), fun t ht => ?_⟩
    have hmem : t ∈ Ioo (t₁ - ε) (t₁ + ε) := ⟨by linarith [ht.1, min_le_left ε (t₁ / 2)],
      by linarith [ht.2, min_le_left ε (t₁ / 2)]⟩
    have ht_pos : 0 < t := by linarith [ht.1, min_le_right ε (t₁ / 2)]
    have hdist : dist t t₁ < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have hne : |g t| * prob.cardyV a t ≠ 0 := by
      have h1 := hε hdist
      rw [Real.dist_eq] at h1
      intro h0
      rw [h0, zero_sub, abs_neg, abs_of_pos hf_pos] at h1
      linarith
    exact ⟨hne, ht_pos⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hsupp_nonempty
  have hvol_pos : 0 < volume (Ioo (t₁ - δ) (t₁ + δ)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact lt_of_lt_of_le hvol_pos (measure_mono hδ_sub)

/-- For any weakly feasible test `g` at `prob.totalShift ≤ c' / 12`:
1. `0 < M[g]`,
2. `0 < t₁`,
3. `M[g] / 2 ≤ ∫₀^{t₁} |g(t)| V(t) dt`. -/
lemma weaklyFeasible_halfMass (prob : FixedWeightProblem) {c' t₁ : ℝ}
    (hc' : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ}
    (hwf : prob.IsWeaklyFeasible (c' / 12) t₁ g) :
    0 < prob.cardyNorm (c' / 12) g ∧ 0 < t₁ ∧
      prob.cardyNorm (c' / 12) g / 2 ≤
        ∫ t in (0 : ℝ)..t₁, |g t| * prob.cardyV (c' / 12) t := by
  rcases hwf with ⟨hg, hnz, hvac, htail⟩
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero_general prob hc' hg hnz
  have hV_nn : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun ht =>
    prob.cardyV_nonneg hc' ht
  have hint_gV : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) := by
    refine hg.int_cardy.mono' ?_ ?_
    · exact ((hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hV_nn (mem_Ioi.mp ht).le)]
  have hint_g_le0 : ∫ t in Ioi 0, g t * prob.cardyV (c' / 12) t ≤ 0 := by
    have hv : 0 ≤ -2 * π * ∫ t in Ioi 0, g t * prob.cardyV (c' / 12) t := hvac
    have h2pi : 0 < 2 * π := by positivity
    nlinarith
  have ht₁_pos : 0 < t₁ := by
    by_contra ht₁_le
    push Not at ht₁_le
    have heq : EqOn (fun t => g t * prob.cardyV (c' / 12) t)
        (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioi 0) := by
      intro t ht
      dsimp only
      have hgt : 0 ≤ g t := htail t (by linarith [mem_Ioi.mp ht])
      rw [abs_of_nonneg hgt]
    have hM_eq : ∫ t in Ioi 0, g t * prob.cardyV (c' / 12) t = prob.cardyNorm (c' / 12) g := by
      unfold FixedWeightProblem.cardyNorm
      exact setIntegral_congr_fun measurableSet_Ioi heq
    linarith
  refine ⟨hM_pos, ht₁_pos, ?_⟩
  have hdisj : Disjoint (Ioc (0 : ℝ) t₁) (Ioi t₁) := by
    rw [Set.disjoint_left]; intro t h1 h2; linarith [h1.2, mem_Ioi.mp h2]
  have hunion : Ioc (0 : ℝ) t₁ ∪ Ioi t₁ = Ioi 0 := Ioc_union_Ioi_eq_Ioi ht₁_pos.le
  have hM_split : prob.cardyNorm (c' / 12) g =
      (∫ t in Ioc 0 t₁, |g t| * prob.cardyV (c' / 12) t) +
        (∫ t in Ioi t₁, |g t| * prob.cardyV (c' / 12) t) := by
    unfold FixedWeightProblem.cardyNorm
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hg.int_cardy.mono_set Ioc_subset_Ioi_self)
      (hg.int_cardy.mono_set (Ioi_subset_Ioi ht₁_pos.le))
  have hgV_split : ∫ t in Ioi 0, g t * prob.cardyV (c' / 12) t =
      (∫ t in Ioc 0 t₁, g t * prob.cardyV (c' / 12) t) +
        (∫ t in Ioi t₁, g t * prob.cardyV (c' / 12) t) := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hint_gV.mono_set Ioc_subset_Ioi_self)
      (hint_gV.mono_set (Ioi_subset_Ioi ht₁_pos.le))
  have htail_eq : ∫ t in Ioi t₁, g t * prob.cardyV (c' / 12) t =
      ∫ t in Ioi t₁, |g t| * prob.cardyV (c' / 12) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [abs_of_nonneg (htail t (mem_Ioi.mp ht).le)]
  have hhead_le : -(∫ t in Ioc 0 t₁, |g t| * prob.cardyV (c' / 12) t) ≤
      ∫ t in Ioc 0 t₁, g t * prob.cardyV (c' / 12) t := by
    rw [← integral_neg]
    refine setIntegral_mono_on
      ((hg.int_cardy.mono_set Ioc_subset_Ioi_self).neg)
      (hint_gV.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
    have hV : 0 ≤ prob.cardyV (c' / 12) t := hV_nn ht.1.le
    calc -(|g t| * prob.cardyV (c' / 12) t)
        = (-|g t|) * prob.cardyV (c' / 12) t := by ring
      _ ≤ g t * prob.cardyV (c' / 12) t :=
          mul_le_mul_of_nonneg_right (neg_abs_le (g t)) hV
  rw [intervalIntegral.integral_of_le ht₁_pos.le]
  linarith

private lemma theorem_A_mid_lt (prob : FixedWeightProblem)
    {c' C_I C_K' C_M1 C_M2 C_pref lam0 δ₀ δ_c M : ℝ} {g : ℝ → ℝ}
    (hc'_ge1 : 1 ≤ c') (hS_lt : prob.totalShift ≤ c' / 12)
    (hg : TestClass prob (c' / 12) g) (hM_pos : 0 < M)
    (hI_bd : ∀ {x : ℝ}, 0 < x → |besselI (prob.w - 1) x / besselAs x - 1| ≤ C_I / x)
    (hL005_pos : 0 < slitL 0.05) (hc'_I0 : max 8 (2 * C_I / slitL 0.05) ≤ c')
    (hCK'_eq : C_K' = 2 ^ (prob.w - 1) * ((3 / 2 : ℝ) / Real.sqrt (2 * π * slitL 0.05)))
    (hCpref_eq : C_pref = 2 * C_K' * Real.exp C_M2)
    (hC_pref_pos : 0 < C_pref)
    (hlam0_ge1 : 1 ≤ lam0) (hlam0_gt : Real.log (4 * C_pref) < lam0)
    (hδ₀_eq : δ₀ = xiStar - 0.05) (hδ_c_eq : δ_c = lam0 * c' ^ (-(2 / 3 : ℝ)))
    (hδ_c_pos : 0 < δ_c) (hδ_c_lt_δ₀ : δ_c < δ₀) (h005_lt_x : (0.05 : ℝ) < xiStar - δ_c)
    (hlogc_bd : C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1)
    (hexp_bd : ∀ x ∈ Ico 0 xiStar,
      |g (c' * x ^ 2 / 3)| ≤
        Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
          Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) :
    ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3),
      |g t| * prob.cardyV (c' / 12) t < M / 4 := by
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'_ge1
  have hlam0_pos : 0 < lam0 := zero_lt_one.trans_le hlam0_ge1
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
  have hφ_eq : ∫ x in (0.05 : ℝ)..(xiStar - δ_c),
      |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x =
      ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3),
        |g t| * prob.cardyV (c' / 12) t := by
    have hd : ∀ x ∈ uIcc (0.05 : ℝ) (xiStar - δ_c), HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']
      exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hcont_φ' : ContinuousOn φ' (uIcc (0.05 : ℝ) (xiStar - δ_c)) := by dsimp [φ']; fun_prop
    have hcont_f : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t)
        (φ '' uIcc 0.05 (xiStar - δ_c)) := by
      refine (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
      rintro t ⟨x, _, rfl⟩
      exact mem_Ici.mpr (div_nonneg (mul_nonneg hc'_pos.le (sq_nonneg x)) (by norm_num))
    exact intervalIntegral.integral_comp_mul_deriv' hd hcont_φ' hcont_f
  let F_δ : ℝ → ℝ := fun δ =>
    C_pref * M * δ⁻¹ * Real.exp (-2.228 * c' * δ ^ ((3 : ℝ) / 2) + C_M1 * Real.sqrt δ * Real.log c')
  let F_x : ℝ → ℝ := fun x => F_δ (xiStar - x)
  have hV_slit_ub : ∀ x ∈ Icc (0.05 : ℝ) xiStar,
      prob.cardyV (c' / 12) (φ x) ≤ C_K' * Real.exp (c' * slitL x) / Real.sqrt c' := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have hK_ub1 := WeightAxioms.cardyV_le_kernelK prob hS_lt (t := φ x) (by dsimp [φ]; positivity)
    rw [show φ x = c' * x ^ 2 / 3 from rfl, kernelK_at_slit prob.hw hc'_pos hx_pos] at hK_ub1
    let z : ℝ := c' * slitL x
    have hL_ge : slitL 0.05 ≤ slitL x := by
      unfold slitL
      rw [abs_of_pos (by norm_num), abs_of_pos hx_pos]
      gcongr; exact hx.1
    have hL_pos : 0 < slitL x := lt_of_lt_of_le hL005_pos hL_ge
    have hz_ge : 2 * C_I ≤ z := by
      have h1 : 2 * C_I / slitL 0.05 ≤ c' := (le_max_right _ _).trans hc'_I0
      have h2 : 2 * C_I ≤ c' * slitL 0.05 := (div_le_iff₀ hL005_pos).mp h1
      exact h2.trans (mul_le_mul_of_nonneg_left hL_ge hc'_pos.le)
    have hz_pos : 0 < z := by dsimp [z]; positivity
    have hAs_pos : 0 < besselAs z := besselAs_pos hz_pos
    have hI_rel := (abs_le.mp (hI_bd hz_pos)).2
    have hCI_z : C_I / z ≤ 1 / 2 := (div_le_iff₀ hz_pos).mpr (by linarith [hz_ge])
    have hI_le : besselI (prob.w - 1) z ≤ (3 / 2 : ℝ) * besselAs z := by
      have h1 : besselI (prob.w - 1) z / besselAs z ≤ 3 / 2 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hAs_pos.le
      rwa [div_mul_cancel₀ _ hAs_pos.ne'] at h2
    have h2x_le : (2 * x) ^ (prob.w - 1) ≤ 2 ^ (prob.w - 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      linarith [hx.2, xiStar_lt_one]
    have has_ub : besselAs z ≤
        Real.exp (c' * slitL x) / (Real.sqrt c' * Real.sqrt (2 * π * slitL 0.05)) := by
      unfold besselAs
      have hsq_ge : Real.sqrt c' * Real.sqrt (2 * π * slitL 0.05) ≤ Real.sqrt (2 * π * z) := by
        rw [← Real.sqrt_mul hc'_pos.le,
          show c' * (2 * π * slitL 0.05) = 2 * π * (c' * slitL 0.05) by ring]
        apply Real.sqrt_le_sqrt
        dsimp [z]
        gcongr
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hsq_ge
    calc prob.cardyV (c' / 12) (c' * x ^ 2 / 3)
        ≤ (2 * x) ^ (prob.w - 1) * besselI (prob.w - 1) z := hK_ub1
      _ ≤ 2 ^ (prob.w - 1) * ((3 / 2 : ℝ) * besselAs z) := by
          refine mul_le_mul h2x_le hI_le ?_ (by positivity)
          have hK_nn : 0 ≤ kernelK prob.w (c' / 12) (c' * x ^ 2 / 3) :=
            kernelK_nonneg (by positivity) (div_nonneg (mul_nonneg hc'_pos.le (sq_nonneg x)) (by norm_num))
          rw [kernelK_at_slit prob.hw hc'_pos hx_pos] at hK_nn
          exact nonneg_of_mul_nonneg_right hK_nn (pow_pos (by positivity) _)
      _ ≤ 2 ^ (prob.w - 1) *
            ((3 / 2 : ℝ) * (Real.exp (c' * slitL x) / (Real.sqrt c' * Real.sqrt (2 * π * slitL 0.05)))) := by
          gcongr
      _ = C_K' * Real.exp (c' * slitL x) / Real.sqrt c' := by
          rw [hCK'_eq]; ring
  have hmono_x : ∫ x in (0.05 : ℝ)..(xiStar - δ_c),
      |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x ≤
      ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x := by
    have hcont_lhs : ContinuousOn (fun x => |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x)
        (uIcc (0.05 : ℝ) (xiStar - δ_c)) := by
      have hφ_nonneg : ∀ x : ℝ, 0 ≤ φ x := fun x =>
        div_nonneg (mul_nonneg hc'_pos.le (sq_nonneg x)) (by norm_num)
      have h1 : ContinuousOn (fun x => g (φ x)) (uIcc (0.05 : ℝ) (xiStar - δ_c)) :=
        hg.cont.comp (by dsimp [φ]; fun_prop) (fun x _ => mem_Ici.mpr (hφ_nonneg x))
      exact ((h1.abs.mul ((continuous_cardyV prob (c' / 12)).continuousOn.comp
        (by dsimp [φ]; fun_prop) (fun _ _ => mem_univ _)))).mul (by dsimp [φ']; fun_prop)
    have hcont_Fx : ContinuousOn F_x (uIcc (0.05 : ℝ) (xiStar - δ_c)) := by
      dsimp [F_x, F_δ]
      rw [uIcc_of_le h005_lt_x.le]
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const
        (ContinuousOn.inv₀ (by fun_prop) fun x hx => ne_of_gt (by linarith [hx.2]))) ?_
      refine ContinuousOn.rexp (ContinuousOn.add ?_ ?_)
      · exact (continuousOn_const.mul ((ContinuousOn.sub continuousOn_const continuousOn_id).rpow_const
          fun x hx => Or.inr (by norm_num))).congr (fun x _ => rfl)
      · exact (continuousOn_const.mul (Continuous.continuousOn (Real.continuous_sqrt.comp (by fun_prop)))).mul
          continuousOn_const
    refine intervalIntegral.integral_mono_on h005_lt_x.le
      hcont_lhs.intervalIntegrable hcont_Fx.intervalIntegrable fun x hx => ?_
    have hx_mem : x ∈ Ico 0 xiStar := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx_Icc : x ∈ Icc (0.05 : ℝ) xiStar := ⟨hx.1, by linarith [hx.2]⟩
    have hMexp := hexp_bd x hx_mem
    have hVub := hV_slit_ub x hx_Icc
    have hUdef : majorantReal x + slitL x ≤ -slitDeficit (xiStar - x) := by
      unfold slitL
      rw [abs_of_nonneg hx_mem.1, show 2 * π * x / 3 = (2 * π / 3) * x by ring]
      exact majorantReal_g_deficit hx_mem
    have hU_le : majorantReal x + slitL x ≤ -2.228 * (xiStar - x) ^ ((3 : ℝ) / 2) := by
      have hsd := slitDeficit_ge (by linarith [hx.2] : 0 ≤ xiStar - x) (by linarith [hx.1])
      linarith [hUdef, hsd]
    have hc_sqrt : c' ^ (-(1 / 2 : ℝ)) * (Real.sqrt c')⁻¹ = c'⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hc'_pos.le, ← Real.rpow_add hc'_pos,
        show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have hφ'_le : φ' x ≤ 2 * c' := by
      have hx1 : x ≤ 1 := hx_Icc.2.trans xiStar_lt_one.le
      dsimp [φ']; nlinarith [hx.1]
    have hV_nn : 0 ≤ prob.cardyV (c' / 12) (φ x) :=
      prob.cardyV_nonneg hS_lt (div_nonneg (mul_nonneg hc'_pos.le (sq_nonneg x)) (by norm_num))
    have hdx_pos : 0 < xiStar - x := by linarith [hx.2]
    have hCK'_pos : 0 < C_K' := by rw [hCK'_eq]; positivity [hL005_pos]
    have hgV : |g (φ x)| * prob.cardyV (c' / 12) (φ x) ≤
        (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
          Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
          (C_K' * Real.exp (c' * slitL x) / Real.sqrt c') :=
      mul_le_mul hMexp hVub hV_nn (by positivity [hdx_pos])
    have hmain_mul : |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x ≤
        C_pref * M * (xiStar - x)⁻¹ *
          Real.exp (c' * (majorantReal x + slitL x) + C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
      calc |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x
          ≤ ((Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
              Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
              (C_K' * Real.exp (c' * slitL x) / Real.sqrt c')) * (2 * c') :=
            mul_le_mul hgV hφ'_le (by dsimp [φ']; positivity [hx.1]) (by positivity [hdx_pos, hCK'_pos])
        _ = (2 * C_K' * Real.exp C_M2) * M * (xiStar - x)⁻¹ * (c' * (c' ^ (-(1 / 2 : ℝ)) * (Real.sqrt c')⁻¹)) *
              (Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                Real.exp (c' * slitL x)) := by ring
        _ = C_pref * M * (xiStar - x)⁻¹ *
              Real.exp (c' * (majorantReal x + slitL x) + C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
            rw [hc_sqrt, mul_inv_cancel₀ hc'_pos.ne', mul_one, ← Real.exp_add, hCpref_eq]
            ring_nf
    refine hmain_mul.trans ?_
    have hexp_le' : Real.exp (c' * (majorantReal x + slitL x) + C_M1 * Real.sqrt (xiStar - x) * Real.log c') ≤
        Real.exp (-2.228 * c' * (xiStar - x) ^ ((3 : ℝ) / 2) +
          C_M1 * Real.sqrt (xiStar - x) * Real.log c') := by
      apply Real.exp_le_exp.mpr
      have hcU : c' * (majorantReal x + slitL x) ≤ c' * (-2.228 * (xiStar - x) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hU_le hc'_pos.le
      linarith
    exact mul_le_mul_of_nonneg_left hexp_le' (by positivity [hdx_pos])
  have hsub_δ : ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x = ∫ δ in δ_c..δ₀, F_δ δ := by
    have hcomp := intervalIntegral.integral_comp_sub_left F_δ xiStar (a := 0.05) (b := xiStar - δ_c)
    rw [hδ₀_eq]
    simpa only [sub_sub_cancel] using hcomp
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hc'_pos _
  let B_lam : ℝ := δ₀ / s
  have hscale_lam : ∫ δ in δ_c..δ₀, F_δ δ = ∫ l in lam0..B_lam, s * F_δ (s * l) := by
    have hcomp := intervalIntegral.integral_comp_mul_left F_δ hs_pos.ne' (a := lam0) (b := B_lam)
    rw [show s * lam0 = δ_c by rw [hδ_c_eq]; dsimp [s]; ring,
      show s * B_lam = δ₀ by dsimp [B_lam]; exact mul_div_cancel₀ _ hs_pos.ne'] at hcomp
    calc ∫ δ in δ_c..δ₀, F_δ δ
        = s * (s⁻¹ * ∫ δ in δ_c..δ₀, F_δ δ) := by field_simp [hs_pos.ne']
      _ = s * ∫ l in lam0..B_lam, F_δ (s * l) := by rw [← smul_eq_mul s⁻¹, ← hcomp]
      _ = ∫ l in lam0..B_lam, s * F_δ (s * l) := (intervalIntegral.integral_const_mul _ _).symm
  have hlam0_le_B : lam0 ≤ B_lam := by
    dsimp [B_lam, s]
    rw [le_div_iff₀ hs_pos]
    calc lam0 * c' ^ (-(2 / 3 : ℝ)) = δ_c := hδ_c_eq.symm
      _ ≤ δ₀ := hδ_c_lt_δ₀.le
  have hCpref_lt : C_pref * Real.exp (-lam0) < 1 / 4 := by
    have hlog_exp := hlam0_gt
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)] at hlog_exp
    have hexp_lt : Real.exp (-lam0) < (4 * C_pref)⁻¹ := by
      rw [Real.exp_neg]; exact inv_strictAnti₀ (by positivity) hlog_exp
    calc C_pref * Real.exp (-lam0)
        < C_pref * (4 * C_pref)⁻¹ := mul_lt_mul_of_pos_left hexp_lt hC_pref_pos
      _ = 1 / 4 := by field_simp [hC_pref_pos.ne']
  have hlam_bound : ∫ l in lam0..B_lam, s * F_δ (s * l) ≤ C_pref * M * Real.exp (-lam0) := by
    have hint_sFδ : IntervalIntegrable (fun l => s * F_δ (s * l)) volume lam0 B_lam := by
      have hcont : ContinuousOn (fun l => s * F_δ (s * l)) (uIcc lam0 B_lam) := by
        rw [uIcc_of_le hlam0_le_B]
        dsimp [F_δ]
        refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul (ContinuousOn.mul
          continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun l hl =>
            ne_of_gt (mul_pos hs_pos (lt_of_lt_of_le hlam0_pos hl.1)))) ?_)
        refine ContinuousOn.rexp (ContinuousOn.add ?_ ?_)
        · exact (continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).rpow_const
            fun l hl => Or.inr (by norm_num))).congr (fun l _ => rfl)
        · exact (continuousOn_const.mul (Continuous.continuousOn (Real.continuous_sqrt.comp (by fun_prop)))).mul
            continuousOn_const
      exact hcont.intervalIntegrable
    have hmono_lam : ∫ l in lam0..B_lam, s * F_δ (s * l) ≤
        ∫ l in lam0..B_lam, (C_pref * M) * Real.exp (-l) := by
      refine intervalIntegral.integral_mono_on hlam0_le_B hint_sFδ
        ((Continuous.intervalIntegrable (by fun_prop) _ _).const_mul _) fun l hl => ?_
      have hl_ge1 : 1 ≤ l := hlam0_ge1.trans hl.1
      have hl_pos : 0 < l := zero_lt_one.trans_le hl_ge1
      have hcancel_1 : s * (s * l)⁻¹ = l⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul]
      have hcancel_2 : c' * (s * l) ^ ((3 : ℝ) / 2) = l ^ ((3 : ℝ) / 2) := by
        rw [Real.mul_rpow hs_pos.le hl_pos.le]; dsimp [s]
        rw [← Real.rpow_mul hc'_pos.le, show (-(2 / 3 : ℝ)) * (3 / 2) = -1 by norm_num,
          ← mul_assoc, Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne', one_mul]
      have hcancel_3 : Real.sqrt (s * l) = c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l := by
        rw [Real.sqrt_mul hs_pos.le, Real.sqrt_eq_rpow]; dsimp [s]
        rw [← Real.rpow_mul hc'_pos.le]; norm_num
      have hCM1_ub : C_M1 * Real.sqrt (s * l) * Real.log c' ≤ Real.sqrt l := by
        rw [hcancel_3]
        calc C_M1 * (c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l) * Real.log c'
            = (C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') * Real.sqrt l := by ring
          _ ≤ 1 * Real.sqrt l := by gcongr
          _ = Real.sqrt l := one_mul _
      have hsqrt_le_l : Real.sqrt l ≤ l :=
        Real.sqrt_le_iff.mpr ⟨hl_pos.le, by calc l ≤ l * l := le_mul_of_one_le_left hl_pos.le hl_ge1
          _ = l ^ 2 := (sq l).symm⟩
      have hl_le_32 : l ≤ l ^ ((3 : ℝ) / 2) := by
        calc l = l ^ (1 : ℝ) := (Real.rpow_one l).symm
          _ ≤ l ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hl_ge1 (by norm_num)
      have hexp_arg : -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
          C_M1 * Real.sqrt (s * l) * Real.log c' ≤ -l := by
        rw [show -2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) = -2.228 * (c' * (s * l) ^ ((3 : ℝ) / 2)) by ring,
          hcancel_2]
        have h2228 : -2.228 * l ^ ((3 : ℝ) / 2) ≤ -2.228 * l := by
          linarith [mul_le_mul_of_nonneg_left hl_le_32 (by norm_num : (0 : ℝ) ≤ 2.228)]
        linarith [h2228, hCM1_ub, hsqrt_le_l, hl_pos]
      dsimp [F_δ]
      calc s * (C_pref * M * (s * l)⁻¹ *
              Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
                C_M1 * Real.sqrt (s * l) * Real.log c'))
          = C_pref * M * (s * (s * l)⁻¹) *
              Real.exp (-2.228 * c' * (s * l) ^ ((3 : ℝ) / 2) +
                C_M1 * Real.sqrt (s * l) * Real.log c') := by ring
        _ ≤ C_pref * M * 1 * Real.exp (-l) := by
            rw [hcancel_1]
            have hCM_nn : 0 ≤ C_pref * M := mul_nonneg hC_pref_pos.le hM_pos.le
            exact mul_le_mul (mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hl_ge1) hCM_nn)
              (Real.exp_le_exp.mpr hexp_arg) (Real.exp_pos _).le (mul_nonneg hCM_nn zero_le_one)
        _ = C_pref * M * Real.exp (-l) := by ring
    have hexp_int_ub : ∫ l in lam0..B_lam, Real.exp (-l) ≤ Real.exp (-lam0) := by
      have hd : ∀ l ∈ uIcc lam0 B_lam, HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-l)) l :=
        fun l _ => ((Real.hasDerivAt_exp _).comp l (hasDerivAt_neg l)).neg.congr_deriv (by ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
      have hexpB : 0 < Real.exp (-B_lam) := Real.exp_pos (-B_lam)
      linarith
    calc ∫ l in lam0..B_lam, s * F_δ (s * l)
        ≤ ∫ l in lam0..B_lam, C_pref * M * Real.exp (-l) := hmono_lam
      _ = C_pref * M * ∫ l in lam0..B_lam, Real.exp (-l) := intervalIntegral.integral_const_mul _ _
      _ ≤ C_pref * M * Real.exp (-lam0) :=
          mul_le_mul_of_nonneg_left hexp_int_ub (mul_nonneg hC_pref_pos.le hM_pos.le)
  calc ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3),
        |g t| * prob.cardyV (c' / 12) t
      = ∫ x in (0.05 : ℝ)..(xiStar - δ_c), |g (φ x)| * prob.cardyV (c' / 12) (φ x) * φ' x :=
        hφ_eq.symm
    _ ≤ ∫ x in (0.05 : ℝ)..(xiStar - δ_c), F_x x := hmono_x
    _ = ∫ δ in δ_c..δ₀, F_δ δ := hsub_δ
    _ = ∫ l in lam0..B_lam, s * F_δ (s * l) := hscale_lam
    _ ≤ C_pref * M * Real.exp (-lam0) := hlam_bound
    _ = (C_pref * Real.exp (-lam0)) * M := by ring
    _ < (1 / 4 : ℝ) * M := mul_lt_mul_of_pos_right hCpref_lt hM_pos
    _ = M / 4 := by ring

/-- **Unconditional General-`(w, Q)` Theorem A (`theorem_A_general`)**:
for any fixed-weight problem `prob : FixedWeightProblem`, there exist constants `C_A > 0`
and `c_A ≥ 1` such that for all `c' ≥ c_A` and every weakly feasible test `g` at threshold `t₁`,
`ξ̄ c' - C_A c'^{1/3} ≤ t₁`. Note that `p_u = 0`, `C_up = 1` unconditionally via
`WeightAxioms.cardyV_le_kernelK`. -/
theorem theorem_A_general (prob : FixedWeightProblem) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 1 ≤ c_A ∧
      ∀ {c' : ℝ}, c_A ≤ c' →
        ∀ {g : ℝ → ℝ} {t₁ : ℝ}, prob.IsWeaklyFeasible (c' / 12) t₁ g →
          xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ t₁ := by
  obtain ⟨U⟩ := WeightAxioms.fixedWeightAxioms_of_problem prob
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general prob
  let C_PJ : ℝ := pjConstOf U.C_e U.c_band C_Klo (slitL xiStar)
  let c_PJ : ℝ := max (max 1 U.c₀) c_Kw
  have hcPJ1 : 1 ≤ c_PJ := le_trans (le_max_left 1 U.c₀) (le_max_left _ _)
  obtain ⟨C_M1, C_M2, hCM1_nn, hpropM⟩ := proposition_M_exp_general realSliceData
    (C_PJ := C_PJ) (p_e := U.p_e) hcPJ1 U.hp_e_nn
  let δ₀ : ℝ := xiStar - 0.05
  have hδ₀_pos : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  obtain ⟨c_deep, C_deep, κ_deep, hc_deep1, hC_deep_pos, hκ_deep_pos, hdeep⟩ :=
    lemmaG_of_problem prob hδ₀_pos (by dsimp [δ₀]; linarith [xiStar_gt_005])
  obtain ⟨C_I, hCI_nn, hI_bd⟩ := besselI_asymptotic_real (prob.w - 1)
  have hL005_pos : 0 < slitL 0.05 := by unfold slitL; positivity
  let c_I0 : ℝ := max 8 (2 * C_I / slitL 0.05)
  let C_K' : ℝ := 2 ^ (prob.w - 1) * ((3 / 2 : ℝ) / Real.sqrt (2 * π * slitL 0.05))
  have hCK'_pos : 0 < C_K' := by positivity [hL005_pos]
  let C_pref : ℝ := 2 * C_K' * Real.exp C_M2
  have hC_pref_pos : 0 < C_pref := by positivity
  let lam0 : ℝ := max 1 (Real.log (4 * C_pref) + 1)
  have hlam0_ge1 : 1 ≤ lam0 := le_max_left _ _
  have hlam0_pos : 0 < lam0 := zero_lt_one.trans_le hlam0_ge1
  let c_A : ℝ := max (max c_PJ (max c_deep c_I0))
    (max ((max 1 (6 * C_M1)) ^ 6)
      (max ((lam0 / δ₀) ^ ((3 : ℝ) / 2) + 1)
        (Real.log (4 * C_deep + 1) / κ_deep + 1)))
  let C_A : ℝ := (2 * xiStar / 3) * lam0
  have hCA_pos : 0 < C_A := mul_pos (div_pos (mul_pos two_pos xiStar_pos) (by norm_num)) hlam0_pos
  have hcA_ge1 : 1 ≤ c_A := le_trans hcPJ1 ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C_A, c_A, hCA_pos, hcA_ge1, fun {c'} hc' {g t₁} hwf => ?_⟩
  have hc'_ge1 : 1 ≤ c' := hcA_ge1.trans hc'
  have hc'_pos : 0 < c' := zero_lt_one.trans_le hc'_ge1
  have hc'_PJ : c_PJ ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc'_c₀ : U.c₀ ≤ c' := (le_max_right 1 U.c₀).trans ((le_max_left _ _).trans hc'_PJ)
  have hc'_Kw : c_Kw ≤ c' := (le_max_right _ _).trans hc'_PJ
  have hc'_deep : c_deep ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc'))
  have hc'_I0 : c_I0 ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc'))
  have hc'_log : (max 1 (6 * C_M1)) ^ 6 ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc'_delta : (lam0 / δ₀) ^ ((3 : ℝ) / 2) + 1 ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc'_kdeep : Real.log (4 * C_deep + 1) / κ_deep + 1 ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  let hax := U.axioms_at hc'_c₀
  let P := hax.toPropositionPAxioms
  have hS_lt : prob.totalShift ≤ c' / 12 := hax.ha_shift
  obtain ⟨hM_pos, ht₁_pos, hhalfMass⟩ := weaklyFeasible_halfMass prob hS_lt hwf
  set hg : TestClass prob (c' / 12) g := hwf.1
  set M : ℝ := prob.cardyNorm (c' / 12) g
  have hdeep_lt : ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t <
      M / 4 := by
    have h1 := hdeep hc'_deep hg
    rw [show (xiStar - δ₀) = (0.05 : ℝ) by dsimp [δ₀]; ring] at h1
    have hlog_lt : Real.log (4 * C_deep + 1) < κ_deep * c' := by
      have hsub : Real.log (4 * C_deep + 1) / κ_deep < c' := by linarith
      linarith [(div_lt_iff₀ hκ_deep_pos).mp hsub]
    have hexp_lt : C_deep * Real.exp (-κ_deep * c') < 1 / 4 := by
      rw [← Real.exp_lt_exp] at hlog_lt
      rw [Real.exp_log (by linarith)] at hlog_lt
      have heneg : Real.exp (-κ_deep * c') < (4 * C_deep + 1)⁻¹ := by
        rw [show -κ_deep * c' = -(κ_deep * c') by ring, Real.exp_neg]
        exact inv_strictAnti₀ (by positivity) hlog_lt
      have hpos4 : 0 < 4 * C_deep + 1 := by linarith
      have hmul : C_deep * Real.exp (-κ_deep * c') < C_deep / (4 * C_deep + 1) := by
        rw [div_eq_mul_inv]
        exact mul_lt_mul_of_pos_left heneg hC_deep_pos
      have hfrac : C_deep / (4 * C_deep + 1) < 1 / 4 := by
        rw [div_lt_div_iff₀ hpos4 (by norm_num)]; linarith
      exact hmul.trans hfrac
    calc ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t
        ≤ (C_deep * Real.exp (-κ_deep * c')) * M := h1
      _ < (1 / 4 : ℝ) * M := mul_lt_mul_of_pos_right hexp_lt hM_pos
      _ = M / 4 := by ring
  let δ_c : ℝ := lam0 * c' ^ (-(2 / 3 : ℝ))
  have hδ_c_pos : 0 < δ_c := by positivity
  have hδ_c_lt_δ₀ : δ_c < δ₀ := by
    have h2 : ((lam0 / δ₀) ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) < c' ^ ((2 : ℝ) / 3) :=
      Real.rpow_lt_rpow (by positivity) (by linarith) (by norm_num)
    rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num,
      Real.rpow_one] at h2
    have hpow_pos : 0 < c' ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc'_pos _
    rw [div_lt_iff₀ hδ₀_pos] at h2
    have hneg : c' ^ (-(2 / 3 : ℝ)) = (c' ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg hc'_pos.le _
    dsimp [δ_c]
    rw [hneg, mul_inv_lt_iff₀ hpow_pos]
    linarith
  have h005_lt_x : (0.05 : ℝ) < xiStar - δ_c := by dsimp [δ₀] at hδ_c_lt_δ₀; linarith
  have hlogc_bd : C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1 := by
    have hlog_le : Real.log c' ≤ 6 * c' ^ ((1 / 6 : ℝ)) := by
      have h16 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6 : ℝ))
      have h2 := Real.log_rpow hc'_pos (1 / 6 : ℝ)
      linarith
    have hmax1 : max 1 (6 * C_M1) ≤ c' ^ (1 / 6 : ℝ) := by
      have h1 : (max 1 (6 * C_M1) ^ 6 : ℝ) ^ (1 / 6 : ℝ) ≤ c' ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hc'_log (by positivity)
      rwa [← Real.rpow_natCast (max 1 (6 * C_M1)) 6, ← Real.rpow_mul (by positivity),
        show (6 : ℕ) * (1 / 6 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
    have hC6_le : 6 * C_M1 ≤ c' ^ (1 / 6 : ℝ) := (le_max_right _ _).trans hmax1
    have hcomb : c' ^ (1 / 6 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = c' ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos]; norm_num
    have hle1 : c' ^ (-(1 / 6 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
    have hlogc_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_ge1
    calc C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        ≤ C_M1 * c' ^ (-(1 / 3 : ℝ)) * (6 * c' ^ (1 / 6 : ℝ)) := by gcongr
      _ = (6 * C_M1) * (c' ^ (1 / 6 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ c' ^ (1 / 6 : ℝ) * c' ^ (-(1 / 6 : ℝ)) := by
          rw [hcomb]; gcongr
      _ ≤ 1 := by
          rw [← Real.rpow_add hc'_pos, add_neg_cancel, Real.rpow_zero]
  have hPJ_at : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤ c' * majorantReal x + Real.log M -
        (1 / 2 : ℝ) * Real.log c' +
        (U.p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
        realSliceData.slitEntropyAt x + C_PJ := by
    intro x hx hx_ne
    have h := hPJ_thm P hc'_Kw hg hM_pos x hx hx_ne
    have hCe : P.C_e = U.C_e := U.uniform_C_e hc'_c₀
    have hpe : P.p_e = U.p_e := U.uniform_p_e hc'_c₀
    have hcb : P.c_band = U.c_band := U.uniform_c_band hc'_c₀
    rw [hCe, hpe, hcb] at h
    exact h
  have hexp_bd := hpropM hc'_PJ hM_pos hPJ_at
  have hlam0_gt : Real.log (4 * C_pref) < lam0 := by
    dsimp [lam0]; linarith [le_max_right (1 : ℝ) (Real.log (4 * C_pref) + 1)]
  have hmid_lt : ∫ t in (c' * (0.05 : ℝ) ^ 2 / 3)..(c' * (xiStar - δ_c) ^ 2 / 3),
      |g t| * prob.cardyV (c' / 12) t < M / 4 :=
    theorem_A_mid_lt prob (C_K' := C_K') (C_pref := C_pref) (δ₀ := δ₀) (δ_c := δ_c)
      hc'_ge1 hS_lt hg hM_pos hI_bd hL005_pos hc'_I0 rfl rfl
      hC_pref_pos hlam0_ge1 hlam0_gt rfl rfl hδ_c_pos hδ_c_lt_δ₀ h005_lt_x hlogc_bd hexp_bd
  let t_cut : ℝ := c' * (xiStar - δ_c) ^ 2 / 3
  have hcut_lt : ∫ t in (0 : ℝ)..t_cut, |g t| * prob.cardyV (c' / 12) t < M / 2 := by
    have hcont_f : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ici 0) :=
      hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn
    have h1 : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume 0
        (c' * (0.05 : ℝ) ^ 2 / 3) :=
      (hcont_f.mono (by rintro t ht; rw [uIcc_of_le (by positivity)] at ht; exact mem_Ici.mpr ht.1)).intervalIntegrable
    have h2 : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume
        (c' * (0.05 : ℝ) ^ 2 / 3) t_cut := by
      have hle : c' * (0.05 : ℝ) ^ 2 / 3 ≤ t_cut := by
        dsimp [t_cut]; gcongr
      exact (hcont_f.mono (by
        rintro t ht; rw [uIcc_of_le hle] at ht
        exact mem_Ici.mpr (le_trans (by positivity) ht.1))).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hdeep_lt, hmid_lt]
  have ht_cut_lt_t₁ : t_cut < t₁ := by
    by_contra hle
    push Not at hle
    have hcont_f : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ici 0) :=
      hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn
    have h1 : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume 0 t₁ :=
      (hcont_f.mono (by rintro t ht; rw [uIcc_of_le ht₁_pos.le] at ht; exact mem_Ici.mpr ht.1)).intervalIntegrable
    have h2 : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume t₁ t_cut :=
      (hcont_f.mono (by
        rintro t ht; rw [uIcc_of_le hle] at ht
        exact mem_Ici.mpr (ht₁_pos.le.trans ht.1))).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
    have htail_nn : 0 ≤ ∫ t in t₁..t_cut, |g t| * prob.cardyV (c' / 12) t :=
      intervalIntegral.integral_nonneg hle fun t ht =>
        mul_nonneg (abs_nonneg _) (prob.cardyV_nonneg hS_lt (ht₁_pos.le.trans ht.1))
    linarith [hhalfMass, hcut_lt, hsplit, htail_nn]
  have hsq : (xiStar - δ_c) ^ 2 ≥ xiStar ^ 2 - 2 * xiStar * δ_c := by
    rw [sub_sq]; linarith [sq_nonneg δ_c]
  have hcut_ge : c' * (xiStar ^ 2 - 2 * xiStar * δ_c) / 3 ≤ t_cut := by
    dsimp [t_cut]
    gcongr
  have hlin_eq : c' * (xiStar ^ 2 - 2 * xiStar * δ_c) / 3 = xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) := by
    have hpow : c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ ((1 : ℝ) / 3) := by
      calc c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
        _ = c' ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := (Real.rpow_add hc'_pos _ _).symm
        _ = c' ^ ((1 : ℝ) / 3) := by norm_num
    unfold xiBar
    dsimp [C_A, δ_c]
    have hcalc : c' * (xiStar ^ 2 - 2 * xiStar * (lam0 * c' ^ (-(2 / 3 : ℝ)))) / 3 =
        (xiStar ^ 2 / 3) * c' - (2 * xiStar / 3 * lam0) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
    rw [hcalc, hpow]
  linarith [ht_cut_lt_t₁, hcut_ge, hlin_eq]

/-! ### Axiom Checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.eSlitMass_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eSlitMass_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.stripPoissonJensen_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripPoissonJensen_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.stripPoissonJensen_complex_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripPoissonJensen_complex_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.lemmaG_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaG_of_problem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.theorem_A_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_A_general

end FormalResearch.ModularBootstrap.FixedWeightTip



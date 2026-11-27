module

public import FormalResearch.SignUncertainty.GenRationalAiryTail
public import FormalResearch.CohnElkies.HighBandEstimate
public import FormalResearch.CohnElkies.HighBandUniform
public import FormalResearch.SignUncertainty.ConvSourceTail

/-!
# `u1c:U1` expansion, `SmoothSymbol`, `SymbolTail`, and high-band `(e4)` bounds for `ℛ_Ai^gen`

For any `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁` (`X u := (F (u : ℂ)).re`):
1. Branch-point decomposition `F = (-β₀₀) f₁ + β₁₁ g₁' + F_rem` with `HasGenRationalAiryCoeffs F_rem 0 0`.
2. On `{Re y ≥ 0}`, one integration by parts in the `r01 · Ai · Ai'` tail gives a `O(‖y‖)`
   remainder for `airyTwistedLaplaceC X_rem y - airyTwistedLaplaceC X_rem 0` (`u1c:U1`).
3. Splitting `X_rem(-x)` into its stationary (`SymBd` order `5/2`) and oscillatory (`SymBd` order `5/2`,
   frequency `±4/3 x^{3/2}`) parts gives `SmoothSymbol` for `X_rem` (`γ₀ = 0`), `SymbolTail` for any
   `F ∈ ℛ_Ai^gen`, and hence the uniform high-band estimate `(e4)` with leading coefficient
   `(β₀₀ + β₁₁) * g0 = airyBetaInf F * g0`, plus bounded finite linear combinations.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies
open FormalResearch.Special

/-! ### Section 1: Elementary exponential and `SymBd` helpers -/

private lemma norm_cexp_real_mul_I (r : ℝ) : ‖cexp ((r : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I r

private lemma norm_cexp_neg_I_mul (q x : ℝ) : ‖cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (q : ℂ) * (x : ℂ)) = ((-q * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma contDiff_ofReal_cexp_aff (n : ℕ) (a : ℂ) (b c : ℝ) :
    ContDiff ℝ n (fun q : ℝ => a * cexp (Complex.I * ((b - q * c : ℝ) : ℂ))) := by
  have hfn : (fun q : ℝ => a * cexp (Complex.I * ((b - q * c : ℝ) : ℂ))) =
      fun q => a * cexp (Complex.I * (b : ℂ) - Complex.I * (c : ℂ) * Complex.ofRealCLM q) := by
    ext q; congr 2; simp [Complex.ofRealCLM_apply]; ring
  rw [hfn]
  exact contDiff_const.mul ((contDiff_const.sub (contDiff_const.mul Complex.ofRealCLM.contDiff)).cexp)

lemma norm_cexp_neg_mul_sub_one_le {w : ℂ} (hw : 0 ≤ w.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖cexp (-w * (x : ℂ)) - 1‖ ≤ ‖w‖ * x := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => cexp (-w * (s : ℂ))) (-w * cexp (-w * (t : ℂ))) t := fun t _ => by
    have h1 : HasDerivAt (fun s : ℝ => -w * (s : ℂ)) (-w) t := by
      have hof := (hasDerivAt_id (t : ℂ)).comp_ofReal
      simpa using hof.const_mul (-w)
    exact (h1.cexp).congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => -w * cexp (-w * (t : ℂ))) (Icc 0 x) :=
    continuousOn_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.mono (by rw [uIcc_of_le hx])).intervalIntegrable
  have hint : cexp (-w * (x : ℂ)) - 1 = ∫ t in (0 : ℝ)..x, -w * cexp (-w * (t : ℂ)) := by
    simpa using hid.symm
  rw [hint, intervalIntegral.integral_of_le hx]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) x, ‖-w * cexp (-w * (t : ℂ))‖ ≤ ‖w‖ := fun t ht => by
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have hre : (-w * (t : ℂ)).re ≤ 0 := by
      have : (-w * (t : ℂ)).re = -w.re * t := by simp [Complex.mul_re]
      nlinarith [ht.1.le]
    simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hre) (norm_nonneg w)
  have hconst : IntegrableOn (fun _ : ℝ => ‖w‖) (Ioc 0 x) := integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hnorm_int : IntegrableOn (fun t : ℝ => ‖-w * cexp (-w * (t : ℂ))‖) (Ioc 0 x) :=
    (hcont.norm).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc ‖∫ t in Ioc (0 : ℝ) x, -w * cexp (-w * (t : ℂ))‖
      ≤ ∫ t in Ioc (0 : ℝ) x, ‖-w * cexp (-w * (t : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Ioc (0 : ℝ) x, ‖w‖ := setIntegral_mono_on hnorm_int hconst measurableSet_Ioc hpt
    _ = ‖w‖ * x := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hx, sub_zero, mul_comm]

lemma norm_cexp_mul_sub_one_le {w : ℂ} {R u : ℝ} (hR : ‖w‖ ≤ R) :
    ‖cexp (w * (u : ℂ)) - 1‖ ≤ ‖w‖ * |u| * Real.exp (R * |u|) := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => cexp ((s : ℂ) * (w * (u : ℂ))))
        ((w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))) t := fun t _ => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * (w * (u : ℂ))) (w * (u : ℂ)) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal).mul_const (w * (u : ℂ))
    exact (h1.cexp).congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => (w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))) (Icc 0 1) :=
    continuousOn_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).continuousOn
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  have hint : cexp (w * (u : ℂ)) - 1 = ∫ t in (0 : ℝ)..1, (w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ))) := by
    simpa using hid.symm
  rw [hint, intervalIntegral.integral_of_le zero_le_one]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖(w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))‖ ≤ ‖w‖ * |u| * Real.exp (R * |u|) := fun t ht => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : ((t : ℂ) * (w * (u : ℂ))).re ≤ R * |u| := by
      calc ((t : ℂ) * (w * (u : ℂ))).re ≤ ‖(t : ℂ) * (w * (u : ℂ))‖ := Complex.re_le_norm _
        _ = |t| * (‖w‖ * |u|) := by simp [abs_of_pos ht.1]
        _ ≤ 1 * (R * |u|) := mul_le_mul (by rw [abs_of_pos ht.1]; exact ht.2)
            (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) (by positivity) (by positivity)
        _ = R * |u| := one_mul _
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (by positivity)
  have hnorm_int : IntegrableOn (fun t : ℝ => ‖(w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))‖) (Ioc 0 1) :=
    (hcont.norm).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc ‖∫ t in Ioc (0 : ℝ) 1, (w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, ‖(w * (u : ℂ)) * cexp ((t : ℂ) * (w * (u : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Ioc (0 : ℝ) 1, ‖w‖ * |u| * Real.exp (R * |u|) :=
        setIntegral_mono_on hnorm_int (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hpt
    _ = ‖w‖ * |u| * Real.exp (R * |u|) := by simp

lemma norm_cexp_neg_cube_sub_one_le {y : ℂ} {R : ℝ} (hR : ‖y‖ ≤ R) :
    ‖cexp (-(y ^ 3) / 12) - 1‖ ≤ (R ^ 2 * Real.exp (R ^ 3 / 12) + 1) * ‖y‖ := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => cexp (-(((s : ℂ) * y) ^ 3) / 12))
        (-((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12)) t := fun t _ => by
    have ht : HasDerivAt (fun s : ℝ => -(((s : ℂ) * y) ^ 3) / 12) (-((t : ℂ) ^ 2 * y ^ 3 / 4)) t := by
      have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * y) y t := by
        simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal).mul_const y
      have hpow : HasDerivAt (fun s : ℝ => ((s : ℂ) * y) ^ 3) (3 * ((t : ℂ) * y) ^ 2 * y) t :=
        hlin.pow 3
      exact ((hpow.neg).div_const 12).congr_deriv (by ring)
    exact (ht.cexp).congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => -((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12))
      (Icc 0 1) :=
    (((Complex.continuous_ofReal.pow 2).mul continuous_const).div_const 4 |>.neg).mul
      (Complex.continuous_exp.comp ((((Complex.continuous_ofReal.mul continuous_const).pow 3).neg).div_const 12))
      |>.continuousOn
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  have hint : cexp (-(y ^ 3) / 12) - 1 =
      ∫ t in (0 : ℝ)..1, -((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12) := by
    simpa using hid.symm
  rw [hint, intervalIntegral.integral_of_le zero_le_one]
  have hR0 : 0 ≤ R := (norm_nonneg y).trans hR
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖-((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12)‖ ≤ R ^ 2 * Real.exp (R ^ 3 / 12) * ‖y‖ :=
    fun t ht => by
      have hn1 : ‖-((t : ℂ) ^ 2 * y ^ 3 / 4)‖ = t ^ 2 * ‖y‖ ^ 3 / 4 := by
        rw [norm_neg, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht.1]
        norm_num
      rw [norm_mul, hn1, Complex.norm_exp]
      have ht1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have hre : (-(((t : ℂ) * y) ^ 3) / 12).re ≤ R ^ 3 / 12 := by
        calc (-(((t : ℂ) * y) ^ 3) / 12).re ≤ ‖-(((t : ℂ) * y) ^ 3) / 12‖ := Complex.re_le_norm _
          _ = t ^ 3 * ‖y‖ ^ 3 / 12 := by
              rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
              norm_num; ring
          _ ≤ 1 * R ^ 3 / 12 := by
              have : t ^ 3 ≤ 1 := pow_le_one₀ ht.1.le ht.2
              gcongr
          _ = R ^ 3 / 12 := by ring
      have hy3 : ‖y‖ ^ 3 ≤ R ^ 2 * ‖y‖ := by
        have h2 : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hR 2
        calc ‖y‖ ^ 3 = ‖y‖ ^ 2 * ‖y‖ := by ring
          _ ≤ R ^ 2 * ‖y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg y)
      calc t ^ 2 * ‖y‖ ^ 3 / 4 * Real.exp _
          ≤ (1 * (R ^ 2 * ‖y‖) / 4) * Real.exp (R ^ 3 / 12) := by gcongr
        _ ≤ R ^ 2 * ‖y‖ * Real.exp (R ^ 3 / 12) := by
            have : 0 ≤ R ^ 2 * ‖y‖ * Real.exp (R ^ 3 / 12) := by positivity
            linarith
        _ = R ^ 2 * Real.exp (R ^ 3 / 12) * ‖y‖ := by ring
  have hnorm_int : IntegrableOn (fun t : ℝ =>
      ‖-((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12)‖) (Ioc 0 1) :=
    (hcont.norm).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc ‖∫ t in Ioc (0 : ℝ) 1, -((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12)‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, ‖-((t : ℂ) ^ 2 * y ^ 3 / 4) * cexp (-(((t : ℂ) * y) ^ 3) / 12)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Ioc (0 : ℝ) 1, R ^ 2 * Real.exp (R ^ 3 / 12) * ‖y‖ :=
        setIntegral_mono_on hnorm_int (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hpt
    _ = R ^ 2 * Real.exp (R ^ 3 / 12) * ‖y‖ := by simp
    _ ≤ (R ^ 2 * Real.exp (R ^ 3 / 12) + 1) * ‖y‖ := by nlinarith [norm_nonneg y]

lemma SymBd.deriv_gt {N : ℕ} {x₀ x₁ β M : ℝ} {b : ℝ → ℂ} (hx : x₀ < x₁)
    (hb : SymBd (N + 1) x₀ β M b) : SymBd N x₁ (β + 1) M (deriv b) := by
  refine ⟨?_, fun k hk x hx1 => ?_⟩
  · have hcd_oi : ContDiffOn ℝ (((N + 1 : ℕ) : WithTop ℕ∞) + 1) b (Ioi x₀) := by
      simpa only [Nat.cast_succ] using hb.cd.mono (Ioi_subset_Ici_self : Ioi x₀ ⊆ Ici x₀)
    exact (hcd_oi.deriv_of_isOpen isOpen_Ioi le_rfl).mono (Ici_subset_Ioi.mpr hx)
  · have hdn : iteratedDeriv (k + 1) b x = iteratedDeriv k (deriv b) x :=
      congrFun (iteratedDeriv_succ' (f := b) (n := k)) x
    have hbd := hb.bd (k + 1) (by omega) x (lt_trans hx hx1)
    rw [hdn, Nat.cast_add, Nat.cast_one] at hbd
    rw [show β + 1 + (k : ℝ) = β + ((k : ℝ) + 1) by ring]
    exact hbd

lemma SymBd.mono_left {N : ℕ} {x₀ x₁ β M : ℝ} {b : ℝ → ℂ} (hx : x₀ ≤ x₁)
    (hb : SymBd N x₀ β M b) : SymBd N x₁ β M b :=
  ⟨hb.cd.mono (Ici_subset_Ici.mpr hx), fun k hk x hx1 => hb.bd k hk x (lt_of_le_of_lt hx hx1)⟩

lemma SymBd.of_le_N {N N' : ℕ} {x₀ β M : ℝ} {b : ℝ → ℂ} (hN : N' ≤ N) (hb : SymBd N x₀ β M b) :
    SymBd N' x₀ β M b :=
  ⟨hb.cd.of_le (by exact_mod_cast Nat.succ_le_succ hN), fun k hk x hx => hb.bd k (by omega) x hx⟩

lemma SymBd.bd0_le {N : ℕ} {x₀ β M : ℝ} {b : ℝ → ℂ} (hx₀ : 0 < x₀)
    (hb : SymBd N x₀ β M b) {x : ℝ} (hx : x₀ ≤ x) :
    ‖b x‖ ≤ M * x ^ (-β) := by
  have hpos : 0 < x := lt_of_lt_of_le hx₀ hx
  have hmul : x ^ β * ‖b x‖ ≤ M := by
    rcases eq_or_lt_of_le hx with rfl | hlt
    · have hcc := ((hb.cd.continuousOn) x₀ (mem_Ici.mpr le_rfl)).norm
      have hcb : ContinuousWithinAt (fun t : ℝ => t ^ β * ‖b t‖) (Ici x₀) x₀ :=
        ((continuousAt_id.rpow_const (Or.inl hx₀.ne')).continuousWithinAt).mul hcc
      exact le_of_tendsto (hcb.mono Ioi_subset_Ici_self)
        (eventually_nhdsWithin_of_forall fun t ht => by simpa using hb.bd 0 (Nat.zero_le N) t ht)
    · simpa using hb.bd 0 (Nat.zero_le N) x hlt
  rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos β), mul_comm]
  exact hmul

lemma symBd_inv_sqrt {N : ℕ} {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd N x₀ (1 / 2) M (fun x : ℝ => ((x : ℂ) ^ (-(1 / 2 : ℂ)))) := by
  obtain ⟨Kc, hKc, hsym⟩ := symBd_of_sector N (1 / 2)
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => w ^ (-(1 / 2 : ℂ)))
      {w : ℂ | x₀ / 2 < w.re ∧ |w.im| < w.re / 2} := fun w hw => by
    have hmem : w ∈ Complex.slitPlane := Or.inl (by linarith [hw.1])
    exact (differentiableAt_id.cpow_const hmem).differentiableWithinAt
  let M₀ : ℝ := Real.exp (Real.pi / 4)
  have hM₀ : 0 ≤ M₀ := (Real.exp_pos _).le
  have hsec : ∀ w : ℂ, x₀ / 2 < w.re → |w.im| < w.re / 2 →
      ‖w ^ (-(1 / 2 : ℂ))‖ ≤ M₀ * ‖w‖ ^ (-(1 / 2 : ℝ)) := fun w hw _ => by
    have hre : 0 < w.re := by linarith
    have hw0 : w ≠ 0 := fun h => by simp [h] at hre
    rw [Complex.norm_cpow_of_ne_zero hw0]
    have hre_c : (-(1 / 2 : ℂ)).re = -(1 / 2 : ℝ) := by norm_num
    have him_c : (-(1 / 2 : ℂ)).im = 0 := by norm_num
    rw [hre_c, him_c, mul_zero, Real.exp_zero, div_one]
    have hM1 : 1 ≤ M₀ := Real.one_le_exp (by positivity)
    exact le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg w) _) hM1
  exact ⟨Kc * M₀, mul_nonneg hKc hM₀, hsym hx₀ hM₀ hdiff hsec⟩

private lemma integrableOn_Ici_rpow_of_lt {x₀ p : ℝ} (hx₀ : 0 < x₀) (hp : p < -1) :
    IntegrableOn (fun x : ℝ => x ^ p) (Ici x₀) :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_rpow_of_lt hp hx₀)

lemma integrableOn_rpow_exp_right {X : ℝ → ℝ} (hcont : Continuous X) (hU2 : HasU2 X)
    (a R : ℝ) (hR : 0 ≤ R) {k : ℕ} (hk : k ≤ 2) :
    IntegrableOn (fun u : ℝ => |u| ^ k * ‖(X u : ℂ)‖ * Real.exp (R * |u|)) (Ici a) := by
  have hint_pos : Integrable (fun u : ℝ => (X u : ℂ) * cexp (((R + 2 : ℝ) : ℂ) * (u : ℂ))) :=
    hU2.integrable (((R + 2 : ℝ) : ℂ)) (by simp; linarith)
  have hsub : Ici a ⊆ Icc a (max a 0) ∪ Ioi (max a 0) := fun u hu => by
    rcases le_or_gt u (max a 0) with hle | hgt
    · exact Or.inl ⟨hu, hle⟩
    · exact Or.inr hgt
  refine (IntegrableOn.union ?_ ?_).mono_set hsub
  · exact (((continuous_abs.pow k).mul ((Complex.continuous_ofReal.comp hcont).norm)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).continuousOn.integrableOn_Icc
  · refine (hint_pos.norm.integrableOn).mono'
      ((((continuous_abs.pow k).mul ((Complex.continuous_ofReal.comp hcont).norm)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : max a 0 < u)
    have hu0 : 0 ≤ u := (le_max_right a 0).trans hu.le
    rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_exp,
      show (((R + 2 : ℝ) : ℂ) * (u : ℂ)).re = (R + 2) * u by simp]
    have hpow_exp : |u| ^ k ≤ Real.exp (2 * u) := by
      rw [abs_of_pos ((le_max_right a 0).trans_lt hu)]
      have hexp := Real.add_one_le_exp u
      have hu1 : u ≤ u + 1 := by linarith
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · simpa using (Real.one_le_exp (by linarith : 0 ≤ 2 * u))
      · calc u ^ 1 = u := pow_one u
          _ ≤ Real.exp u := by linarith
          _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
      · calc u ^ 2 ≤ (u + 1) ^ 2 := pow_le_pow_left₀ hu0 hu1 2
          _ ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ (by linarith) hexp 2
          _ = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; ring_nf
    rw [abs_of_nonneg hu0] at hpow_exp
    calc |u| ^ k * ‖(X u : ℂ)‖ * Real.exp (R * |u|)
        ≤ Real.exp (2 * u) * ‖(X u : ℂ)‖ * Real.exp (R * u) := by
          rw [abs_of_nonneg hu0]; gcongr
      _ = ‖(X u : ℂ)‖ * Real.exp ((R + 2) * u) := by
          rw [mul_assoc, mul_comm ‖(X u : ℂ)‖, ← mul_assoc, ← Real.exp_add]; ring_nf

/-! ### Section 2: `HasGenRationalAiryCoeffs F 0 0` decomposition and `u1c:U1` bound -/

lemma hasGenRational_decomp {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    let F_rem : ℂ → ℂ := fun z => F z - (((-β₀₀ : ℝ) : ℂ) * airySeedF 0 z + (β₁₁ : ℂ) * airySeedG1Deriv z)
    HasGenRationalAiryCoeffs F_rem 0 0 ∧
      (∀ u : ℝ, (F (u : ℂ)).re = airySeedU2 (-β₀₀) 0 β₁₁ u + (F_rem (u : ℂ)).re) := by
  intro F_rem
  have hlin : HasGenRationalAiryCoeffs
      (fun z => ((-β₀₀ : ℝ) : ℂ) * airySeedF 0 z + (β₁₁ : ℂ) * airySeedG1Deriv z) β₀₀ β₁₁ := by
    have h1 := (hasGenRationalAiryCoeffs_airySeedF 0).smul (-β₀₀)
    have h2 := hasGenRationalAiryCoeffs_airySeedG1Deriv.smul β₁₁
    have hsum := h1.add h2
    convert hsum using 2 <;> ring
  have hrem := hF.sub hlin
  have hrem0 : HasGenRationalAiryCoeffs F_rem 0 0 := by
    convert hrem using 2 <;> ring
  refine ⟨hrem0, fun u => ?_⟩
  have hF0 : (airySeedF 0 (u : ℂ)).re = ceF1 u := by
    rw [airySeedF_re, airyCardinalR_zero_eq_dslope]; rfl
  have hG1d : (airySeedG1Deriv (u : ℂ)).re = ceG1Deriv airyDerivFirstZero u := airySeedG1Deriv_re u
  have hlre : (((-β₀₀ : ℝ) : ℂ) * airySeedF 0 (u : ℂ) + (β₁₁ : ℂ) * airySeedG1Deriv (u : ℂ)).re =
      airySeedU2 (-β₀₀) 0 β₁₁ u := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hF0, hG1d, airySeedU2, zero_mul, add_zero]
  have hfre : (F_rem (u : ℂ)).re = (F (u : ℂ)).re - airySeedU2 (-β₀₀) 0 β₁₁ u := by
    simp only [F_rem, Complex.sub_re, hlre]
  linarith

lemma airyAi_neg_rpow_bound {x₀ : ℝ} (hx₀ : 4 ≤ x₀) :
    ∃ CAi > 0, ∀ x : ℝ, x₀ ≤ x →
      ‖(airyAi (-x) : ℂ)‖ ≤ CAi * x ^ (-(1 / 4 : ℝ)) ∧
      ‖(airyAi' (-x) : ℂ)‖ ≤ CAi * x ^ (1 / 4 : ℝ) := by
  obtain ⟨MA, hMA, hAP⟩ := symBd_negAmpP (by norm_num : (2 : ℝ) ≤ 2)
  obtain ⟨MB, hMB, hAM⟩ := symBd_negAmpM (by norm_num : (2 : ℝ) ≤ 2)
  obtain ⟨MA', hMA', hAP'⟩ := symBd_negAmpP' (by norm_num : (2 : ℝ) ≤ 2)
  obtain ⟨MB', hMB', hAM'⟩ := symBd_negAmpM' (by norm_num : (2 : ℝ) ≤ 2)
  let CAi : ℝ := (MA + MB) + (MA' + MB') + 1
  refine ⟨CAi, by positivity, fun x hx => ?_⟩
  have h2x : (2 : ℝ) ≤ x := by linarith
  have hp1 : ‖negAmpP (x : ℂ)‖ ≤ MA * x ^ (-(1 / 4 : ℝ)) := by simpa using hAP.bd0_le (by norm_num) h2x
  have hm1 : ‖negAmpM (x : ℂ)‖ ≤ MB * x ^ (-(1 / 4 : ℝ)) := by simpa using hAM.bd0_le (by norm_num) h2x
  have hp2 : ‖negAmpP' (x : ℂ)‖ ≤ MA' * x ^ (1 / 4 : ℝ) := by simpa using hAP'.bd0_le (by norm_num) h2x
  have hm2 : ‖negAmpM' (x : ℂ)‖ ≤ MB' * x ^ (1 / 4 : ℝ) := by simpa using hAM'.bd0_le (by norm_num) h2x
  have hsp := ai_real_split (by linarith : 0 ≤ x)
  have hsp' := aip_real_split (by linarith : 0 ≤ x)
  have he1 : ‖cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have he2 : ‖cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hCa1 : MA + MB ≤ CAi := by dsimp [CAi]; linarith
  have hCa2 : MA' + MB' ≤ CAi := by dsimp [CAi]; linarith
  have hx0 : 0 ≤ x := by linarith
  constructor
  · have htri : ‖negAmpP (x : ℂ) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) +
        negAmpM (x : ℂ) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))‖ ≤
        MA * x ^ (-(1 / 4 : ℝ)) + MB * x ^ (-(1 / 4 : ℝ)) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, he1, mul_one]; exact hp1
      · rw [norm_mul, he2, mul_one]; exact hm1
    calc ‖(airyAi (-x) : ℂ)‖ = ‖negAmpP (x : ℂ) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) +
          negAmpM (x : ℂ) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))‖ := by rw [hsp]
      _ ≤ (MA + MB) * x ^ (-(1 / 4 : ℝ)) := by rw [add_mul]; exact htri
      _ ≤ CAi * x ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_right hCa1 (Real.rpow_nonneg hx0 _)
  · have htri : ‖negAmpP' (x : ℂ) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) +
        negAmpM' (x : ℂ) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))‖ ≤
        MA' * x ^ (1 / 4 : ℝ) + MB' * x ^ (1 / 4 : ℝ) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, he1, mul_one]; exact hp2
      · rw [norm_mul, he2, mul_one]; exact hm2
    calc ‖(airyAi' (-x) : ℂ)‖ = ‖negAmpP' (x : ℂ) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) +
          negAmpM' (x : ℂ) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))‖ := by rw [hsp']
      _ ≤ (MA' + MB') * x ^ (1 / 4 : ℝ) := by rw [add_mul]; exact htri
      _ ≤ CAi * x ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hCa2 (Real.rpow_nonneg hx0 _)

lemma genRational_zero_coeff_bounds {F : ℂ → ℂ} (hF : HasGenRationalAiryCoeffs F 0 0) :
    ∃ x₀ C_r : ℝ, 12 ≤ x₀ ∧ 0 ≤ C_r ∧
      ∃ (r00 r01 r11 : ℝ → ℂ),
        SymBd 12 x₀ 2 C_r r00 ∧
        SymBd 12 x₀ 2 C_r r01 ∧
        SymBd 12 x₀ 3 C_r r11 ∧
        (∀ x : ℝ, x₀ ≤ x →
          (F (-(x : ℂ))) =
            r00 x * ((airyAi (-x) : ℂ) ^ 2) +
            r01 x * ((airyAi (-x) : ℂ) * (airyAi' (-x) : ℂ)) +
            r11 x * ((airyAi' (-x) : ℂ) ^ 2)) := by
  obtain ⟨hIn, R_star, C, P00, Q00, P01, Q01, P11, Q11, hR4, hC0, _, _, _, hQ00, hQ01, hQ11, hrep, hasym⟩ := hF
  let x₀ : ℝ := 2 * (R_star + 2)
  have hx0_ge12 : 12 ≤ x₀ := by dsimp [x₀]; linarith
  have hbd00 : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P00 / Polynomial.aeval (-w) Q00‖ ≤ C * ‖w‖ ^ (-2 : ℝ) := fun w hw => by
    simpa [zero_mul, sub_zero] using (hasym w hw).1
  have hbd01 : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P01 / Polynomial.aeval (-w) Q01‖ ≤ C * ‖w‖ ^ (-2 : ℝ) := fun w hw =>
    (hasym w hw).2.1
  have hbd11 : ∀ w : ℂ, R_star + 2 ≤ ‖w‖ →
      ‖Polynomial.aeval (-w) P11 / Polynomial.aeval (-w) Q11‖ ≤ C * ‖w‖ ^ (-3 : ℝ) := fun w hw => by
    simpa [zero_mul, sub_zero] using (hasym w hw).2.2
  obtain ⟨M00, hM00, s00⟩ := symBd_neg_rat P00 Q00 hR4 hQ00 hC0 hbd00
  obtain ⟨M01, hM01, s01⟩ := symBd_neg_rat P01 Q01 hR4 hQ01 hC0 hbd01
  obtain ⟨M11, hM11, s11⟩ := symBd_neg_rat P11 Q11 hR4 hQ11 hC0 hbd11
  let M : ℝ := M00 + M01 + M11
  refine ⟨x₀, M, hx0_ge12, by positivity,
    fun x => Polynomial.aeval (-(x : ℂ)) P00 / Polynomial.aeval (-(x : ℂ)) Q00,
    fun x => Polynomial.aeval (-(x : ℂ)) P01 / Polynomial.aeval (-(x : ℂ)) Q01,
    fun x => Polynomial.aeval (-(x : ℂ)) P11 / Polynomial.aeval (-(x : ℂ)) Q11,
    ⟨s00.cd, fun k hk x hx => (s00.bd k hk x hx).trans (by dsimp [M]; linarith)⟩,
    ⟨s01.cd, fun k hk x hx => (s01.bd k hk x hx).trans (by dsimp [M]; linarith)⟩,
    ⟨s11.cd, fun k hk x hx => (s11.bd k hk x hx).trans (by dsimp [M]; linarith)⟩,
    fun x hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hgt : R_star < ‖-(x : ℂ)‖ := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
    dsimp [x₀] at hx; linarith
  have hrx := hrep (-(x : ℂ)) hgt
  rw [← Complex.ofReal_neg, airyAiC_ofReal, deriv_airyAiC_ofReal] at hrx
  simpa [Complex.ofReal_neg] using hrx

/-- Exact half-plane IBP representation of `lapC X y` (`0 ≤ y.re`) for `HasGenRationalAiryCoeffs F 0 0`. -/
lemma genRational_zero_lapC_split {F : ℂ → ℂ} (hF : HasGenRationalAiryCoeffs F 0 0) :
    let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
    ∃ x₀ C_h : ℝ, 16 ≤ x₀ ∧ 0 ≤ C_h ∧ ∃ (r00 r01 r11 : ℝ → ℂ),
      SymBd 12 (x₀ - 4) 2 C_h r00 ∧ SymBd 12 (x₀ - 4) 2 C_h r01 ∧ SymBd 12 (x₀ - 4) 3 C_h r11 ∧
      let h₀ : ℝ → ℂ := fun x =>
        r00 x * ((airyAi (-x) : ℂ) ^ 2) +
        r11 x * ((airyAi' (-x) : ℂ) ^ 2) +
        (1 / 2 : ℂ) * (deriv r01 x * ((airyAi (-x) : ℂ) ^ 2))
      let h₁ : ℝ → ℂ := fun x => r01 x * ((airyAi (-x) : ℂ) ^ 2)
      ContinuousOn h₀ (Ici x₀) ∧ ContinuousOn h₁ (Ici x₀) ∧
      (∀ x : ℝ, x₀ ≤ x → ‖h₀ x‖ ≤ C_h * x ^ (-(5 / 2 : ℝ)) ∧ ‖h₁ x‖ ≤ C_h * x ^ (-(5 / 2 : ℝ))) ∧
      (∀ y : ℂ, 0 ≤ y.re →
        IntegrableOn (fun u : ℝ => (X u : ℂ) * cexp (y * (u : ℂ))) (Ici (-x₀)) ∧
        IntegrableOn (fun x : ℝ => h₀ x * cexp (-y * (x : ℂ))) (Ici x₀) ∧
        IntegrableOn (fun x : ℝ => h₁ x * cexp (-y * (x : ℂ))) (Ici x₀) ∧
        lapC X y =
          (∫ u in Ici (-x₀), (X u : ℂ) * cexp (y * (u : ℂ))) +
          (∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ))) +
          (1 / 2 : ℂ) * h₁ x₀ * cexp (-y * (x₀ : ℂ)) -
          (y / 2) * (∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ)))) := by
  intro X
  obtain ⟨y₀, C_r, hy12, hCr, r00, r01, r11, sr00_y, sr01_y, sr11_y, hrep_y⟩ := genRational_zero_coeff_bounds hF
  let x₀ : ℝ := y₀ + 4
  have hx16 : 16 ≤ x₀ := by dsimp [x₀]; linarith
  have hy_eq : x₀ - 4 = y₀ := by dsimp [x₀]; ring
  have sr00_x : SymBd 12 x₀ 2 C_r r00 := sr00_y.mono_left (by dsimp [x₀]; linarith)
  have sr01_x : SymBd 12 x₀ 2 C_r r01 := sr01_y.mono_left (by dsimp [x₀]; linarith)
  have hrep : ∀ x : ℝ, x₀ ≤ x →
      F (-(x : ℂ)) =
        r00 x * (airyAi (-x) : ℂ) ^ 2 +
        r01 x * ((airyAi (-x) : ℂ) * (airyAi' (-x) : ℂ)) +
        r11 x * (airyAi' (-x) : ℂ) ^ 2 :=
    fun x hx => hrep_y x (by dsimp [x₀] at hx; linarith)
  obtain ⟨CAi, hCAi, hAi⟩ := airyAi_neg_rpow_bound (by linarith : 4 ≤ x₀)
  have hx0_pos : 0 < x₀ := by linarith
  have hIn := hF.1
  have hX_cont : Continuous X := (contDiff_re_of_differentiable hIn.1).1.continuous
  let C_h : ℝ := 3 * C_r * CAi ^ 2 + C_r + 1
  have hCh_pos : 0 < C_h := by positivity
  have hCr_le : C_r ≤ C_h := by dsimp [C_h]; linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hCr) (sq_nonneg CAi)]
  have sr00' : SymBd 12 (x₀ - 4) 2 C_h r00 := by
    rw [hy_eq]
    exact ⟨sr00_y.cd, fun k hk x hx => (sr00_y.bd k hk x hx).trans hCr_le⟩
  have sr01' : SymBd 12 (x₀ - 4) 2 C_h r01 := by
    rw [hy_eq]
    exact ⟨sr01_y.cd, fun k hk x hx => (sr01_y.bd k hk x hx).trans hCr_le⟩
  have sr11' : SymBd 12 (x₀ - 4) 3 C_h r11 := by
    rw [hy_eq]
    exact ⟨sr11_y.cd, fun k hk x hx => (sr11_y.bd k hk x hx).trans hCr_le⟩
  refine ⟨x₀, C_h, hx16, hCh_pos.le, r00, r01, r11, sr00', sr01', sr11', ?_⟩
  dsimp only
  let h₀ : ℝ → ℂ := fun x =>
    r00 x * ((airyAi (-x) : ℂ) ^ 2) +
    r11 x * ((airyAi' (-x) : ℂ) ^ 2) +
    (1 / 2 : ℂ) * (deriv r01 x * ((airyAi (-x) : ℂ) ^ 2))
  let h₁ : ℝ → ℂ := fun x => r01 x * ((airyAi (-x) : ℂ) ^ 2)
  have sr01d : SymBd 11 (y₀ + 1) 3 C_r (deriv r01) := by
    simpa [show (2 : ℝ) + 1 = 3 by norm_num] using sr01_y.deriv_gt (by linarith : y₀ < y₀ + 1)
  have hAi_cont : Continuous fun x : ℝ => (airyAi (-x) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_airyAi.comp continuous_neg)
  have hAip_cont : Continuous fun x : ℝ => (airyAi' (-x) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_airyAi'.comp continuous_neg)
  have hr00_c : ContinuousOn r00 (Ici x₀) := sr00_x.cd.continuousOn
  have hr01_c : ContinuousOn r01 (Ici x₀) := sr01_x.cd.continuousOn
  have hr11_c : ContinuousOn r11 (Ici x₀) := (sr11_y.mono_left (by dsimp [x₀]; linarith)).cd.continuousOn
  have hr01d_c : ContinuousOn (deriv r01) (Ici x₀) := (sr01d.mono_left (by dsimp [x₀]; linarith)).cd.continuousOn
  have hh0_cont : ContinuousOn h₀ (Ici x₀) :=
    ((hr00_c.mul (hAi_cont.continuousOn.pow 2)).add
      ((hr11_c.mul (hAip_cont.continuousOn.pow 2)).add
        ((continuousOn_const (c := (1 / 2 : ℂ))).mul (hr01d_c.mul (hAi_cont.continuousOn.pow 2))))).congr
      fun x _ => by dsimp [h₀]; simp [add_assoc]
  have hh1_cont : ContinuousOn h₁ (Ici x₀) := hr01_c.mul (hAi_cont.continuousOn.pow 2)
  have hh_bd : ∀ x : ℝ, x₀ ≤ x → ‖h₀ x‖ ≤ C_h * x ^ (-(5 / 2 : ℝ)) ∧ ‖h₁ x‖ ≤ C_h * x ^ (-(5 / 2 : ℝ)) :=
    fun x hx => by
      have hy0_pos : 0 < y₀ := by linarith
      have hxgt_y : y₀ ≤ x := by dsimp [x₀] at hx; linarith
      have hxgt_y1 : y₀ + 1 ≤ x := by dsimp [x₀] at hx; linarith
      have hxpos : 0 < x := by linarith
      have hx1 : 1 ≤ x := by linarith
      have b00 : ‖r00 x‖ ≤ C_r * x ^ (-2 : ℝ) := by simpa using sr00_y.bd0_le hy0_pos hxgt_y
      have b01 : ‖r01 x‖ ≤ C_r * x ^ (-2 : ℝ) := by simpa using sr01_y.bd0_le hy0_pos hxgt_y
      have b11 : ‖r11 x‖ ≤ C_r * x ^ (-3 : ℝ) := by simpa using sr11_y.bd0_le hy0_pos hxgt_y
      have b01d : ‖deriv r01 x‖ ≤ C_r * x ^ (-3 : ℝ) := by simpa using sr01d.bd0_le (by linarith) hxgt_y1
      have ⟨hai, haip⟩ := hAi x hx
      have hai2 : ‖(airyAi (-x) : ℂ) ^ 2‖ ≤ CAi ^ 2 * x ^ (-(1 / 2 : ℝ)) := by
        rw [norm_pow]
        calc ‖(airyAi (-x) : ℂ)‖ ^ 2 ≤ (CAi * x ^ (-(1 / 4 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hai 2
          _ = CAi ^ 2 * (x ^ (-(1 / 4 : ℝ))) ^ 2 := by ring
          _ = CAi ^ 2 * x ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast (x ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hxpos.le]; norm_num
      have haip2 : ‖(airyAi' (-x) : ℂ) ^ 2‖ ≤ CAi ^ 2 * x ^ (1 / 2 : ℝ) := by
        rw [norm_pow]
        calc ‖(airyAi' (-x) : ℂ)‖ ^ 2 ≤ (CAi * x ^ (1 / 4 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) haip 2
          _ = CAi ^ 2 * (x ^ (1 / 4 : ℝ)) ^ 2 := by ring
          _ = CAi ^ 2 * x ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hxpos.le]; norm_num
      have e1 : x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have e2 : x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have e3' : x ^ (-3 : ℝ) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(7 / 2 : ℝ)) := by
        rw [← Real.rpow_add hxpos]; norm_num
      have e3_le : x ^ (-(7 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have t1 : ‖r00 x * (airyAi (-x) : ℂ) ^ 2‖ ≤ C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
        rw [norm_mul]
        calc ‖r00 x‖ * ‖(airyAi (-x) : ℂ) ^ 2‖
            ≤ (C_r * x ^ (-2 : ℝ)) * (CAi ^ 2 * x ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul b00 hai2 (norm_nonneg _) (by positivity)
          _ = C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by rw [← e1]; ring
      have t2 : ‖r11 x * (airyAi' (-x) : ℂ) ^ 2‖ ≤ C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
        rw [norm_mul]
        calc ‖r11 x‖ * ‖(airyAi' (-x) : ℂ) ^ 2‖
            ≤ (C_r * x ^ (-3 : ℝ)) * (CAi ^ 2 * x ^ (1 / 2 : ℝ)) :=
              mul_le_mul b11 haip2 (norm_nonneg _) (by positivity)
          _ = C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by rw [← e2]; ring
      have t3 : ‖(1 / 2 : ℂ) * (deriv r01 x * (airyAi (-x) : ℂ) ^ 2)‖ ≤ C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
        rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
        calc (1 / 2) * (‖deriv r01 x‖ * ‖(airyAi (-x) : ℂ) ^ 2‖)
            ≤ 1 * ((C_r * x ^ (-3 : ℝ)) * (CAi ^ 2 * x ^ (-(1 / 2 : ℝ)))) := by
              gcongr; norm_num
          _ = C_r * CAi ^ 2 * x ^ (-(7 / 2 : ℝ)) := by rw [one_mul, ← e3']; ring
          _ ≤ C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by gcongr
      have s1 : ‖h₁ x‖ ≤ C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
        dsimp [h₁]; rw [norm_mul]
        calc ‖r01 x‖ * ‖(airyAi (-x) : ℂ) ^ 2‖
            ≤ (C_r * x ^ (-2 : ℝ)) * (CAi ^ 2 * x ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul b01 hai2 (norm_nonneg _) (by positivity)
          _ = C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by rw [← e1]; ring
      constructor
      · have htot : ‖h₀ x‖ ≤ 3 * C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) :=
          calc ‖h₀ x‖ ≤ ‖r00 x * (airyAi (-x) : ℂ) ^ 2 + r11 x * (airyAi' (-x) : ℂ) ^ 2‖ +
                ‖(1 / 2 : ℂ) * (deriv r01 x * (airyAi (-x) : ℂ) ^ 2)‖ := norm_add_le _ _
            _ ≤ (‖r00 x * (airyAi (-x) : ℂ) ^ 2‖ + ‖r11 x * (airyAi' (-x) : ℂ) ^ 2‖) +
                ‖(1 / 2 : ℂ) * (deriv r01 x * (airyAi (-x) : ℂ) ^ 2)‖ := add_le_add (norm_add_le _ _) le_rfl
            _ ≤ (C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) + C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ))) +
                C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := add_le_add (add_le_add t1 t2) t3
            _ = 3 * C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by ring
        exact htot.trans (mul_le_mul_of_nonneg_right (by dsimp [C_h]; linarith)
          (Real.rpow_nonneg hxpos.le _))
      · refine s1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hxpos.le _))
        dsimp [C_h]; nlinarith [sq_nonneg CAi, hCr]
  refine ⟨hh0_cont, hh1_cont, hh_bd, fun y hy => ?_⟩
  have hU2 : HasU2 X := hasU2_of_genRational hF
  have hint_full : Integrable (fun u : ℝ => (X u : ℂ) * cexp (y * (u : ℂ))) := hU2.integrable y hy
  have hint_right : IntegrableOn (fun u : ℝ => (X u : ℂ) * cexp (y * (u : ℂ))) (Ici (-x₀)) :=
    hint_full.integrableOn
  have hexp_le : ∀ x : ℝ, 0 ≤ x → ‖cexp (-y * (x : ℂ))‖ ≤ 1 := fun x hx => by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have : (-y * (x : ℂ)).re = -y.re * x := by simp [Complex.mul_re]
    nlinarith
  have hint_h0 : IntegrableOn (fun x : ℝ => h₀ x * cexp (-y * (x : ℂ))) (Ici x₀) := by
    have hmaj := (integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul C_h
    refine hmaj.mono' ((hh0_cont.aestronglyMeasurable measurableSet_Ici).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hexp_le x (by linarith [mem_Ici.mp hx]))).trans (hh_bd x hx).1
  have hint_h1 : IntegrableOn (fun x : ℝ => h₁ x * cexp (-y * (x : ℂ))) (Ici x₀) := by
    have hmaj := (integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul C_h
    refine hmaj.mono' ((hh1_cont.aestronglyMeasurable measurableSet_Ici).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hexp_le x (by linarith [mem_Ici.mp hx]))).trans (hh_bd x hx).2
  refine ⟨hint_right, hint_h0, hint_h1, ?_⟩
  have hsplit : lapC X y =
      (∫ u in Ici (-x₀), (X u : ℂ) * cexp (y * (u : ℂ))) +
      (∫ u in Iio (-x₀), (X u : ℂ) * cexp (y * (u : ℂ))) := by
    unfold lapC
    have hu := integral_add_compl (measurableSet_Ici (a := -x₀)) hint_full
    rw [← hu, compl_Ici]
  have hcov : ∫ u in Iio (-x₀), (X u : ℂ) * cexp (y * (u : ℂ)) =
      ∫ x in Ioi x₀, (X (-x) : ℂ) * cexp (-y * (x : ℂ)) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
    rw [← integral_neg_eq_self (fun u : ℝ => (Iio (-x₀)).indicator (fun t => (X t : ℂ) * cexp (y * (t : ℂ))) u)]
    congr 1; ext x
    by_cases hx : x₀ < x
    · have h1 : -x ∈ Iio (-x₀) := by simp; linarith
      simp [hx, h1, mul_neg]
    · have h1 : -x ∉ Iio (-x₀) := by simp; linarith
      simp [hx, h1]
  have hX_real : ∀ x : ℝ, (X (-x) : ℂ) = F (-(x : ℂ)) := fun x =>
    Complex.ext (by simp [X]) (by simpa using (hIn.2.2.2 (-x)).symm)
  have hX_oi_int : IntegrableOn (fun x : ℝ => (X (-x) : ℂ) * cexp (-y * (x : ℂ))) (Ioi x₀) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    have h2 : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ici x₀) := integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num)
    let C_x : ℝ := 3 * C_r * CAi ^ 2 + 1
    refine (h2.const_mul C_x).mono'
      ((Complex.continuous_ofReal.comp (hX_cont.comp continuous_neg)).aestronglyMeasurable.mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [hX_real x, hrep x hx, norm_mul]
    have hy0_pos : 0 < y₀ := by linarith
    have hxgt_y : y₀ ≤ x := by dsimp [x₀] at *; linarith [mem_Ici.mp hx]
    have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
    have hx1 : 1 ≤ x := by linarith [mem_Ici.mp hx]
    have b00 : ‖r00 x‖ ≤ C_r * x ^ (-2 : ℝ) := by simpa using sr00_y.bd0_le hy0_pos hxgt_y
    have b01 : ‖r01 x‖ ≤ C_r * x ^ (-2 : ℝ) := by simpa using sr01_y.bd0_le hy0_pos hxgt_y
    have b11 : ‖r11 x‖ ≤ C_r * x ^ (-3 : ℝ) := by simpa using sr11_y.bd0_le hy0_pos hxgt_y
    have ⟨hai, haip⟩ := hAi x hx
    have s1 : ‖r00 x * (airyAi (-x) : ℂ) ^ 2‖ ≤ C_r * CAi ^ 2 * x ^ (-2 : ℝ) := by
      rw [norm_mul, norm_pow]
      calc ‖r00 x‖ * ‖(airyAi (-x) : ℂ)‖ ^ 2
          ≤ (C_r * x ^ (-2 : ℝ)) * (CAi * x ^ (-(1 / 4 : ℝ))) ^ 2 :=
            mul_le_mul b00 (pow_le_pow_left₀ (norm_nonneg _) hai 2) (sq_nonneg _) (by positivity)
        _ = C_r * CAi ^ 2 * (x ^ (-2 : ℝ) * x ^ (-(1 / 2 : ℝ))) := by
            rw [mul_pow, ← Real.rpow_natCast (x ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hxpos.le]; norm_num; ring
        _ ≤ C_r * CAi ^ 2 * x ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_of_le_one_right (Real.rpow_nonneg hxpos.le _)
                (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)))
              (by positivity)
    have s2 : ‖r01 x * ((airyAi (-x) : ℂ) * (airyAi' (-x) : ℂ))‖ ≤ C_r * CAi ^ 2 * x ^ (-2 : ℝ) := by
      rw [norm_mul, norm_mul]
      calc ‖r01 x‖ * (‖(airyAi (-x) : ℂ)‖ * ‖(airyAi' (-x) : ℂ)‖)
          ≤ (C_r * x ^ (-2 : ℝ)) * (CAi * x ^ (-(1 / 4 : ℝ)) * (CAi * x ^ (1 / 4 : ℝ))) :=
            mul_le_mul b01 (mul_le_mul hai haip (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ = C_r * CAi ^ 2 * (x ^ (-2 : ℝ) * (x ^ (-(1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ))) := by ring
        _ = C_r * CAi ^ 2 * x ^ (-2 : ℝ) := by
            rw [← Real.rpow_add hxpos, show -(1 / 4 : ℝ) + 1 / 4 = 0 by norm_num, Real.rpow_zero, mul_one]
    have s3 : ‖r11 x * (airyAi' (-x) : ℂ) ^ 2‖ ≤ C_r * CAi ^ 2 * x ^ (-2 : ℝ) := by
      rw [norm_mul, norm_pow]
      calc ‖r11 x‖ * ‖(airyAi' (-x) : ℂ)‖ ^ 2
          ≤ (C_r * x ^ (-3 : ℝ)) * (CAi * x ^ (1 / 4 : ℝ)) ^ 2 :=
            mul_le_mul b11 (pow_le_pow_left₀ (norm_nonneg _) haip 2) (sq_nonneg _) (by positivity)
        _ = C_r * CAi ^ 2 * (x ^ (-3 : ℝ) * x ^ (1 / 2 : ℝ)) := by
            rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hxpos.le]; norm_num; ring
        _ = C_r * CAi ^ 2 * x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
        _ ≤ C_r * CAi ^ 2 * x ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by positivity)
    have hnorm := mul_le_of_le_one_right (norm_nonneg _) (hexp_le x (by linarith [mem_Ici.mp hx]))
    have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add s1 s2)) s3)
    exact hnorm.trans (hsum.trans (by dsimp [C_x]; have := Real.rpow_nonneg hxpos.le (-2 : ℝ); nlinarith))
  have hh0_oi := (integrableOn_Ici_iff_integrableOn_Ioi).mp hint_h0
  have hh1_oi := (integrableOn_Ici_iff_integrableOn_Ioi).mp hint_h1
  have hdiff_r01 : ∀ t : ℝ, y₀ < t → HasDerivAt r01 (deriv r01 t) t := fun t ht =>
    ((sr01_y.cd.mono (Ioi_subset_Ici_self : Ioi y₀ ⊆ Ici y₀)).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds ht) |>.hasDerivAt
  have hdiff_ai2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (airyAi (-s) : ℂ) ^ 2)
      (-2 * (airyAi (-t) : ℂ) * (airyAi' (-t) : ℂ)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => airyAi (-s)) (-(airyAi' (-t))) t :=
      ((hasDerivAt_airyAi (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring)
    have h1c : HasDerivAt (fun s : ℝ => (airyAi (-s) : ℂ)) (-(airyAi' (-t) : ℂ)) t := by
      simpa using h1.ofReal_comp
    exact (h1c.pow 2).congr_deriv (by ring)
  have hinterval : ∀ R : ℝ, x₀ ≤ R →
      ∫ x in x₀..R, (X (-x) : ℂ) * cexp (-y * (x : ℂ)) =
        (∫ x in x₀..R, h₀ x * cexp (-y * (x : ℂ))) +
        (1 / 2 : ℂ) * h₁ x₀ * cexp (-y * (x₀ : ℂ)) -
        (1 / 2 : ℂ) * h₁ R * cexp (-y * (R : ℂ)) -
        (y / 2) * ∫ x in x₀..R, h₁ x * cexp (-y * (x : ℂ)) := fun R hR => by
    have hftc : ∫ x in x₀..R, ((deriv r01 x * (airyAi (-x) : ℂ) ^ 2 -
        2 * r01 x * ((airyAi (-x) : ℂ) * (airyAi' (-x) : ℂ)) - y * h₁ x) * cexp (-y * (x : ℂ))) =
        h₁ R * cexp (-y * (R : ℂ)) - h₁ x₀ * cexp (-y * (x₀ : ℂ)) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => h₁ x * cexp (-y * (x : ℂ))) (fun t ht => ?_) ?_
      · have ht0 : x₀ ≤ t := (uIcc_of_le hR ▸ ht).1
        have h_h1 : HasDerivAt h₁
            (deriv r01 t * (airyAi (-t) : ℂ) ^ 2 + r01 t * (-2 * (airyAi (-t) : ℂ) * (airyAi' (-t) : ℂ))) t :=
          (hdiff_r01 t (by have hx0_eq : x₀ = y₀ + 4 := rfl; linarith)).mul (hdiff_ai2 t)
        have h_exp : HasDerivAt (fun s : ℝ => cexp (-y * (s : ℂ))) (-y * cexp (-y * (t : ℂ))) t :=
          (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-y)).congr_of_eventuallyEq
            (Eventually.of_forall fun _ => by simp)).cexp.congr_deriv (by simp; ring)
        exact (h_h1.mul h_exp).congr_deriv (by dsimp only [h₁]; ring)
      · have hicc : Icc x₀ R ⊆ Ici x₀ := fun t ht => ht.1
        rw [← uIcc_of_le hR] at hicc
        exact (((hr01d_c.mono hicc |>.mul (hAi_cont.continuousOn.pow 2)).sub
          ((continuousOn_const.mul (hr01_c.mono hicc)).mul (hAi_cont.continuousOn.mul hAip_cont.continuousOn))).sub
          (continuousOn_const.mul (hh1_cont.mono hicc))).mul (by fun_prop) |>.intervalIntegrable
    have hi_h0 : IntervalIntegrable (fun x => h₀ x * cexp (-y * (x : ℂ))) volume x₀ R :=
      (hh0_cont.mono (by rw [uIcc_of_le hR]; exact fun _ h => h.1) |>.mul (by fun_prop)).intervalIntegrable
    have hi_h1 : IntervalIntegrable (fun x => h₁ x * cexp (-y * (x : ℂ))) volume x₀ R :=
      (hh1_cont.mono (by rw [uIcc_of_le hR]; exact fun _ h => h.1) |>.mul (by fun_prop)).intervalIntegrable
    have hi_X : IntervalIntegrable (fun x => (X (-x) : ℂ) * cexp (-y * (x : ℂ))) volume x₀ R :=
      ((Complex.continuous_ofReal.comp (hX_cont.comp continuous_neg)).mul (by fun_prop)).intervalIntegrable _ _
    have hcomb : ∫ x in x₀..R, ((X (-x) : ℂ) * cexp (-y * (x : ℂ)) -
        (h₀ x * cexp (-y * (x : ℂ)) - (y / 2) * (h₁ x * cexp (-y * (x : ℂ))))) =
        -(1 / 2 : ℂ) * (h₁ R * cexp (-y * (R : ℂ)) - h₁ x₀ * cexp (-y * (x₀ : ℂ))) := by
      rw [← hftc, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx0' : x₀ ≤ x := (uIcc_of_le hR ▸ hx).1
      rw [hX_real x, hrep x hx0']
      dsimp [h₀, h₁]; ring
    rw [intervalIntegral.integral_sub hi_X (hi_h0.sub (hi_h1.const_mul _)),
      intervalIntegral.integral_sub hi_h0 (hi_h1.const_mul _),
      intervalIntegral.integral_const_mul] at hcomb
    linear_combination hcomb
  have htend_X : Tendsto (fun R : ℝ => ∫ x in x₀..R, (X (-x) : ℂ) * cexp (-y * (x : ℂ))) atTop
      (𝓝 (∫ x in Ioi x₀, (X (-x) : ℂ) * cexp (-y * (x : ℂ)))) :=
    intervalIntegral_tendsto_integral_Ioi x₀ hX_oi_int tendsto_id
  have htend_h0 : Tendsto (fun R : ℝ => ∫ x in x₀..R, h₀ x * cexp (-y * (x : ℂ))) atTop
      (𝓝 (∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ)))) := by
    simpa [integral_Ici_eq_integral_Ioi] using intervalIntegral_tendsto_integral_Ioi x₀ hh0_oi tendsto_id
  have htend_h1 : Tendsto (fun R : ℝ => ∫ x in x₀..R, h₁ x * cexp (-y * (x : ℂ))) atTop
      (𝓝 (∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ)))) := by
    simpa [integral_Ici_eq_integral_Ioi] using intervalIntegral_tendsto_integral_Ioi x₀ hh1_oi tendsto_id
  have htend_bdry : Tendsto (fun R : ℝ => (1 / 2 : ℂ) * h₁ R * cexp (-y * (R : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht0 : Tendsto (fun R : ℝ => (1 / 2 * C_h) * R ^ (-(5 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).const_mul (1 / 2 * C_h)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop x₀] with R hR
    rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    calc 1 / 2 * ‖h₁ R‖ * ‖cexp (-y * (R : ℂ))‖
        ≤ 1 / 2 * (C_h * R ^ (-(5 / 2 : ℝ))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hh_bd R hR).2 (by norm_num))
            (hexp_le R (by linarith)) (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hCh_pos.le (Real.rpow_nonneg (by linarith) _)))
      _ = (1 / 2 * C_h) * R ^ (-(5 / 2 : ℝ)) := by ring
  have htend_rhs : Tendsto (fun R : ℝ =>
      (∫ x in x₀..R, h₀ x * cexp (-y * (x : ℂ))) + (1 / 2 : ℂ) * h₁ x₀ * cexp (-y * (x₀ : ℂ)) -
      (1 / 2 : ℂ) * h₁ R * cexp (-y * (R : ℂ)) - (y / 2) * ∫ x in x₀..R, h₁ x * cexp (-y * (x : ℂ)))
      atTop
      (𝓝 ((∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ))) + (1 / 2 : ℂ) * h₁ x₀ * cexp (-y * (x₀ : ℂ)) - 0 -
        (y / 2) * ∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ)))) :=
    (((htend_h0.add tendsto_const_nhds).sub htend_bdry).sub (htend_h1.const_mul (y / 2)))
  have hlim_eq : ∫ x in Ioi x₀, (X (-x) : ℂ) * cexp (-y * (x : ℂ)) =
      (∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ))) + (1 / 2 : ℂ) * h₁ x₀ * cexp (-y * (x₀ : ℂ)) -
      (y / 2) * ∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ)) := by
    have h1 := tendsto_nhds_unique htend_X (htend_rhs.congr' (by
      filter_upwards [eventually_ge_atTop x₀] with R hR using (hinterval R hR).symm))
    simpa using h1
  rw [hsplit, hcov, hlim_eq]
  ring

/-- **`u1c:U1` Lipschitz remainder bound** for `F` with `HasGenRationalAiryCoeffs F 0 0` on
`0 ≤ y.re, ‖y‖ ≤ R`. -/
theorem u1c_lip_of_genRational_zero {F : ℂ → ℂ} (hF : HasGenRationalAiryCoeffs F 0 0) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ R →
      ‖airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) y -
        airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) 0‖ ≤ C * ‖y‖ := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨x₀, C_h, hx12, hCh, r00, r01, r11, _, _, _, hh0_c, hh1_c, hh_bd, hsplit⟩ := genRational_zero_lapC_split hF
  have hx0_pos : 0 < x₀ := by linarith
  have hIn := hF.1
  have hX_cont : Continuous X := (contDiff_re_of_differentiable hIn.1).1.continuous
  have hU2 : HasU2 X := hasU2_of_genRational hF
  have hmaj_R := integrableOn_rpow_exp_right hX_cont hU2 (-x₀) R hR (k := 1) (by norm_num)
  have hmaj_0 := integrableOn_rpow_exp_right hX_cont hU2 (-x₀) 0 le_rfl (k := 0) (by norm_num)
  have hI52 : IntegrableOn (fun x : ℝ => C_h * x ^ (-(5 / 2 : ℝ))) (Ici x₀) :=
    (integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul C_h
  have hI32 : IntegrableOn (fun x : ℝ => C_h * x ^ (-(3 / 2 : ℝ))) (Ici x₀) :=
    (integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul C_h
  let h₀ : ℝ → ℂ := fun x =>
    r00 x * ((airyAi (-x) : ℂ) ^ 2) + r11 x * ((airyAi' (-x) : ℂ) ^ 2) +
    (1 / 2 : ℂ) * (deriv r01 x * ((airyAi (-x) : ℂ) ^ 2))
  let h₁ : ℝ → ℂ := fun x => r01 x * ((airyAi (-x) : ℂ) ^ 2)
  set Mr1 := ∫ u in Ici (-x₀), |u| ^ 1 * ‖(X u : ℂ)‖ * Real.exp (R * |u|)
  set Mr0 := ∫ u in Ici (-x₀), |u| ^ 0 * ‖(X u : ℂ)‖ * Real.exp (0 * |u|)
  set M52 := ∫ x in Ici x₀, C_h * x ^ (-(5 / 2 : ℝ))
  set M32 := ∫ x in Ici x₀, C_h * x ^ (-(3 / 2 : ℝ))
  have hMr1 : 0 ≤ Mr1 := setIntegral_nonneg measurableSet_Ici fun u _ => by positivity
  have hMr0 : 0 ≤ Mr0 := setIntegral_nonneg measurableSet_Ici fun u _ => by positivity
  have hM52 : 0 ≤ M52 := setIntegral_nonneg measurableSet_Ici fun x hx =>
    mul_nonneg hCh (Real.rpow_nonneg (by linarith [mem_Ici.mp hx]) _)
  have hM32 : 0 ≤ M32 := setIntegral_nonneg measurableSet_Ici fun x hx =>
    mul_nonneg hCh (Real.rpow_nonneg (by linarith [mem_Ici.mp hx]) _)
  obtain ⟨hR0, hh0_0, hh1_0, hlap0⟩ := hsplit 0 le_rfl
  let C_lap : ℝ := Mr1 + M32 + (1 / 2) * (C_h * x₀ ^ (-(5 / 2 : ℝ))) * x₀ + (1 / 2) * M52 + 1
  let L₀ : ℝ := Mr0 + M52 + (1 / 2) * (C_h * x₀ ^ (-(5 / 2 : ℝ))) + 1
  let C_exp : ℝ := R ^ 2 * Real.exp (R ^ 3 / 12) + Real.exp (R ^ 3 / 12) + 1
  refine ⟨ceK * C_exp * (L₀ + C_lap) + 1, by have := ceK_pos; positivity, fun {y} hy hyn => ?_⟩
  obtain ⟨hRy, hh0_y, hh1_y, hlapy⟩ := hsplit y hy
  have hL0_le : ‖lapC X 0‖ ≤ L₀ := by
    rw [hlap0]
    simp only [neg_zero, zero_mul, Complex.exp_zero, zero_div, mul_one, sub_zero]
    have i1 : ‖∫ u in Ici (-x₀), (X u : ℂ) * cexp (0 * (u : ℂ))‖ ≤ Mr0 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on hR0.norm hmaj_0 measurableSet_Ici fun u _ => ?_
      simp [pow_zero, Real.exp_zero]
    have i2 : ‖∫ x in Ici x₀, h₀ x * cexp (-0 * (x : ℂ))‖ ≤ M52 := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine setIntegral_mono_on hh0_0.norm hI52 measurableSet_Ici fun x hx => ?_
      simpa [h₀] using (hh_bd x hx).1
    have i3 : ‖(1 / 2 : ℂ) * h₁ x₀‖ ≤ (1 / 2) * (C_h * x₀ ^ (-(5 / 2 : ℝ))) := by
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      exact mul_le_mul_of_nonneg_left (hh_bd x₀ le_rfl).2 (by norm_num)
    simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one] at i1 i2
    dsimp only [X, h₀, h₁] at i1 i2 i3
    refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
    refine (add_le_add (add_le_add i1 i2) i3).trans ?_
    dsimp [L₀]; linarith
  have hDiff_le : ‖lapC X y - lapC X 0‖ ≤ C_lap * ‖y‖ := by
    have hdiff_eq : lapC X y - lapC X 0 =
        ((∫ u in Ici (-x₀), (X u : ℂ) * cexp (y * (u : ℂ))) -
          ∫ u in Ici (-x₀), (X u : ℂ) * cexp (0 * (u : ℂ))) +
        ((∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ))) -
          ∫ x in Ici x₀, h₀ x * cexp (-0 * (x : ℂ))) +
        ((1 / 2 : ℂ) * h₁ x₀ * (cexp (-y * (x₀ : ℂ)) - 1)) -
        ((y / 2) * ∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ))) := by
      rw [hlapy, hlap0]
      simp only [neg_zero, zero_mul, Complex.exp_zero, zero_div, mul_one, sub_zero]
      ring
    have d1 : ‖(∫ u in Ici (-x₀), (X u : ℂ) * cexp (y * (u : ℂ))) -
        ∫ u in Ici (-x₀), (X u : ℂ) * cexp (0 * (u : ℂ))‖ ≤ Mr1 * ‖y‖ := by
      rw [← integral_sub hRy hR0]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hsub_eq : (fun u : ℝ => ‖(X u : ℂ) * cexp (y * (u : ℂ)) - (X u : ℂ) * cexp (0 * (u : ℂ))‖) =
          fun u : ℝ => ‖(X u : ℂ) * (cexp (y * (u : ℂ)) - 1)‖ := by
        ext u; simp [mul_sub]
      have hint_sub : IntegrableOn (fun u : ℝ => ‖(X u : ℂ) * (cexp (y * (u : ℂ)) - 1)‖) (Ici (-x₀)) :=
        ((hRy.sub hR0).norm).congr (ae_of_all _ fun u => congrArg norm (by simp only [Pi.sub_apply, zero_mul, Complex.exp_zero, mul_one]; ring))
      rw [hsub_eq, mul_comm Mr1 ‖y‖, ← integral_const_mul ‖y‖]
      refine setIntegral_mono_on hint_sub (hmaj_R.const_mul ‖y‖) measurableSet_Ici fun u _ => ?_
      rw [norm_mul]
      calc ‖(X u : ℂ)‖ * ‖cexp (y * (u : ℂ)) - 1‖
          ≤ ‖(X u : ℂ)‖ * (‖y‖ * |u| * Real.exp (R * |u|)) :=
            mul_le_mul_of_nonneg_left (norm_cexp_mul_sub_one_le hyn) (norm_nonneg _)
        _ = ‖y‖ * (|u| ^ 1 * ‖(X u : ℂ)‖ * Real.exp (R * |u|)) := by ring
    have d2 : ‖(∫ x in Ici x₀, h₀ x * cexp (-y * (x : ℂ))) -
        ∫ x in Ici x₀, h₀ x * cexp (-0 * (x : ℂ))‖ ≤ M32 * ‖y‖ := by
      rw [← integral_sub hh0_y hh0_0]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hsub_eq : (fun x : ℝ => ‖h₀ x * cexp (-y * (x : ℂ)) - h₀ x * cexp (-0 * (x : ℂ))‖) =
          fun x : ℝ => ‖h₀ x * (cexp (-y * (x : ℂ)) - 1)‖ := by
        ext x; simp [mul_sub]
      have hint_sub : IntegrableOn (fun x : ℝ => ‖h₀ x * (cexp (-y * (x : ℂ)) - 1)‖) (Ici x₀) :=
        ((hh0_y.sub hh0_0).norm).congr (ae_of_all _ fun x => congrArg norm (by simp only [Pi.sub_apply, neg_zero, zero_mul, Complex.exp_zero, mul_one]; ring))
      rw [hsub_eq, mul_comm M32 ‖y‖, ← integral_const_mul ‖y‖]
      refine setIntegral_mono_on hint_sub (hI32.const_mul ‖y‖) measurableSet_Ici fun x hx => ?_
      have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
      rw [norm_mul]
      calc ‖h₀ x‖ * ‖cexp (-y * (x : ℂ)) - 1‖
          ≤ (C_h * x ^ (-(5 / 2 : ℝ))) * (‖y‖ * x) :=
            mul_le_mul (hh_bd x hx).1 (norm_cexp_neg_mul_sub_one_le hy hxpos.le) (norm_nonneg _) (by positivity)
        _ = ‖y‖ * (C_h * (x ^ (-(5 / 2 : ℝ)) * x ^ (1 : ℝ))) := by simp; ring
        _ = ‖y‖ * (C_h * x ^ (-(3 / 2 : ℝ))) := by
            rw [← Real.rpow_add hxpos]; norm_num
    have d3 : ‖(1 / 2 : ℂ) * h₁ x₀ * (cexp (-y * (x₀ : ℂ)) - 1)‖ ≤
        ((1 / 2) * (C_h * x₀ ^ (-(5 / 2 : ℝ))) * x₀) * ‖y‖ := by
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
      calc 1 / 2 * ‖h₁ x₀‖ * ‖cexp (-y * (x₀ : ℂ)) - 1‖
          ≤ 1 / 2 * (C_h * x₀ ^ (-(5 / 2 : ℝ))) * (‖y‖ * x₀) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hh_bd x₀ le_rfl).2 (by norm_num))
              (norm_cexp_neg_mul_sub_one_le hy hx0_pos.le) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have d4 : ‖(y / 2) * ∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ))‖ ≤ ((1 / 2) * M52) * ‖y‖ := by
      rw [norm_mul, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
      have hint_m : ‖∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ))‖ ≤ M52 := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine setIntegral_mono_on hh1_y.norm hI52 measurableSet_Ici fun x hx => ?_
        rw [norm_mul]
        have hexp : ‖cexp (-y * (x : ℂ))‖ ≤ 1 := by
          rw [Complex.norm_exp, Real.exp_le_one_iff]
          have : (-y * (x : ℂ)).re = -y.re * x := by simp [Complex.mul_re]
          nlinarith [mem_Ici.mp hx]
        exact (mul_le_of_le_one_right (norm_nonneg _) hexp).trans (hh_bd x hx).2
      calc ‖y‖ / 2 * ‖∫ x in Ici x₀, h₁ x * cexp (-y * (x : ℂ))‖
          ≤ ‖y‖ / 2 * M52 := mul_le_mul_of_nonneg_left hint_m (by positivity)
        _ = ((1 / 2) * M52) * ‖y‖ := by ring
    rw [hdiff_eq]
    have hsum := ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add d1 d2)) d3)) d4))
    exact hsum.trans (by dsimp [C_lap]; nlinarith [norm_nonneg y])
  rw [airyTwistedLaplaceC_eq_lapC, airyTwistedLaplaceC_eq_lapC]
  have htw : (ceK : ℂ) * cexp (-(y ^ 3) / 12) * lapC X y - (ceK : ℂ) * cexp (-((0 : ℂ) ^ 3) / 12) * lapC X 0 =
      (ceK : ℂ) * ((cexp (-(y ^ 3) / 12) - 1) * lapC X 0 + cexp (-(y ^ 3) / 12) * (lapC X y - lapC X 0)) := by
    simp; ring
  rw [htw, norm_mul, show ‖(ceK : ℂ)‖ = ceK by simp [ceK_pos.le]]
  have he_bd : ‖cexp (-(y ^ 3) / 12)‖ ≤ C_exp := by
    rw [Complex.norm_exp]
    have hre : (-(y ^ 3) / 12).re ≤ R ^ 3 / 12 := by
      calc (-(y ^ 3) / 12).re ≤ ‖-(y ^ 3) / 12‖ := Complex.re_le_norm _
        _ = ‖y‖ ^ 3 / 12 := by rw [norm_div, norm_neg, norm_pow]; norm_num
        _ ≤ R ^ 3 / 12 := by gcongr
    have h1 : Real.exp (-(y ^ 3) / 12).re ≤ Real.exp (R ^ 3 / 12) := Real.exp_le_exp.mpr hre
    dsimp [C_exp]; linarith [mul_nonneg (sq_nonneg R) (Real.exp_pos (R ^ 3 / 12)).le]
  have he_sub : ‖cexp (-(y ^ 3) / 12) - 1‖ ≤ C_exp * ‖y‖ :=
    (norm_cexp_neg_cube_sub_one_le hyn).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C_exp]; linarith [(Real.exp_pos (R ^ 3 / 12)).le]) (norm_nonneg y))
  have h1 := norm_mul_le (cexp (-(y ^ 3) / 12) - 1) (lapC X 0)
  have h2 := norm_mul_le (cexp (-(y ^ 3) / 12)) (lapC X y - lapC X 0)
  have hb1 : ‖(cexp (-(y ^ 3) / 12) - 1) * lapC X 0‖ ≤ C_exp * ‖y‖ * L₀ :=
    h1.trans (mul_le_mul he_sub hL0_le (norm_nonneg _) (by positivity))
  have hb2 : ‖cexp (-(y ^ 3) / 12) * (lapC X y - lapC X 0)‖ ≤ C_exp * (C_lap * ‖y‖) :=
    h2.trans (mul_le_mul he_bd hDiff_le (norm_nonneg _) (by positivity))
  calc ceK * ‖(cexp (-(y ^ 3) / 12) - 1) * lapC X 0 + cexp (-(y ^ 3) / 12) * (lapC X y - lapC X 0)‖
      ≤ ceK * (C_exp * ‖y‖ * L₀ + C_exp * (C_lap * ‖y‖)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hb1 hb2)) ceK_pos.le
    _ = ceK * C_exp * (L₀ + C_lap) * ‖y‖ := by ring
    _ ≤ (ceK * C_exp * (L₀ + C_lap) + 1) * ‖y‖ := by nlinarith [norm_nonneg y]

/-! ### Section 3: `SymbolTail` and Fourier/stationary/oscillatory symbol regularity -/

/-- `SymbolTail` for any `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
theorem symbolTail_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    ∃ CT > 0, SymbolTail (fun v : ℝ => airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) (yv v)) CT := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨AW, hAW, hgt⟩ := gt1Bounds_of_genRational hF (by norm_num : 3 ≤ 3)
  obtain ⟨W1, W2, W3, hd, _, _, _, _⟩ := hgt ⟨le_rfl, by norm_num⟩
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := imagAxisBounds_of_genRational hF
  let c : ℝ := ceCs
  have hc1 : 1 < c := ceCs_one_lt
  have hc0 : 0 < c := by linarith
  have hω : ∀ v : ℝ, 1 < |v| → 1 < |c * v| := fun v hv => by
    rw [abs_mul, abs_of_pos hc0]; nlinarith [abs_nonneg v]
  have hyv : ∀ w : ℝ, yv w = ((c * w : ℝ) : ℂ) * Complex.I := fun w => by unfold yv; push_cast; ring
  have hopen : IsOpen {w : ℝ | 1 < |w|} := isOpen_lt continuous_const continuous_abs
  have hlin : ∀ v : ℝ, HasDerivAt (fun w : ℝ => c * w) c v := fun v => by
    simpa using (hasDerivAt_id v).const_mul c
  have hd1 : ∀ v : ℝ, 1 < |v| → HasDerivAt (fun w : ℝ => airyTwistedLaplaceC X (yv w)) ((c : ℂ) * g1 (c * v)) v :=
    fun v hv => by
      have h := (h1 (c * v) (hω v hv)).scomp v (hlin v)
      have h' : HasDerivAt (fun w : ℝ => airyTwistedLaplaceC X (((c * w : ℝ) : ℂ) * Complex.I))
          ((c : ℂ) * g1 (c * v)) v := h.congr_deriv (by simp [Complex.real_smul])
      simpa only [hyv] using h'
  have hderiv1 : ∀ v : ℝ, 1 < |v| → deriv (fun w : ℝ => airyTwistedLaplaceC X (yv w)) v = (c : ℂ) * g1 (c * v) :=
    fun v hv => (hd1 v hv).deriv
  have hd2 : ∀ v : ℝ, 1 < |v| →
      deriv (deriv (fun w : ℝ => airyTwistedLaplaceC X (yv w))) v = (c : ℂ) * ((c : ℂ) * g2 (c * v)) :=
    fun v hv => by
      have hev2 : deriv (fun w : ℝ => airyTwistedLaplaceC X (yv w)) =ᶠ[𝓝 v] fun w => (c : ℂ) * g1 (c * w) := by
        filter_upwards [hopen.mem_nhds hv] with w hw using hderiv1 w hw
      rw [hev2.deriv_eq]
      have h := (h2 (c * v) (hω v hv)).scomp v (hlin v)
      have h' : HasDerivAt (fun w : ℝ => g1 (c * w)) ((c : ℂ) * g2 (c * v)) v :=
        h.congr_deriv (by simp [Complex.real_smul])
      exact (h'.const_mul (c : ℂ)).deriv
  have hG_eq : (fun v : ℝ => airyTwistedLaplaceC X (yv v)) = liftW X 0 3 := by
    ext v
    unfold liftW liftSymbol liftMultiplier yv
    have h0 : (((ceCs : ℝ) * 0 / (3 : ℕ) : ℝ) : ℂ) * ((v : ℂ) * Complex.I) = 0 := by simp
    rw [h0, bsplineE1_zero, one_pow, one_mul]
  have hcd2 : ContDiffOn ℝ 2 (fun v : ℝ => airyTwistedLaplaceC X (yv v)) {v : ℝ | v ≠ 0} := by
    rw [hG_eq]
    have hU : IsOpen {v : ℝ | v ≠ 0} := isOpen_ne
    have hdiff0 : DifferentiableOn ℝ (liftW X 0 3) {v : ℝ | v ≠ 0} := fun v hv =>
      (hd v hv).1.differentiableAt.differentiableWithinAt
    have hderivW : EqOn (deriv (liftW X 0 3)) W1 {v : ℝ | v ≠ 0} := fun v hv => (hd v hv).1.deriv
    have hdiff1 : DifferentiableOn ℝ W1 {v : ℝ | v ≠ 0} := fun v hv =>
      (hd v hv).2.1.differentiableAt.differentiableWithinAt
    have hderivW1 : EqOn (deriv W1) W2 {v : ℝ | v ≠ 0} := fun v hv => (hd v hv).2.1.deriv
    have hcont2 : ContinuousOn W2 {v : ℝ | v ≠ 0} := fun v hv =>
      (hd v hv).2.2.differentiableAt.continuousAt.continuousWithinAt
    have hW1_cd : ContDiffOn ℝ 1 W1 {v : ℝ | v ≠ 0} := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
      exact ⟨hdiff1, by simp, contDiffOn_zero.mpr (hcont2.congr hderivW1)⟩
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
    exact ⟨hdiff0, by simp, hW1_cd.congr hderivW⟩
  refine ⟨C, hC, hcd2, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    have := (hb (c * v) (hω v hv)).1
    rw [← hyv v] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [habs]; exact rpow_cmul_le (abs_nonneg v) (by norm_num)
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    rw [hderiv1 v hv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have := (hb (c * v) (hω v hv)).2.1
    rw [habs, Real.mul_rpow hc0.le (abs_nonneg v)] at this
    have hcr : c * c ^ (-(7 / 2 : ℝ)) ≤ 1 := by
      have : c * c ^ (-(7 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
        rw [show c * c ^ (-(7 / 2 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(7 / 2 : ℝ)) by rw [Real.rpow_one],
          ← Real.rpow_add hc0]; norm_num
      rw [this]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
    calc c * ‖g1 (c * v)‖ ≤ c * (C * (c ^ (-(7 / 2 : ℝ)) * |v| ^ (-(7 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left this hc0.le
      _ = C * (c * c ^ (-(7 / 2 : ℝ))) * |v| ^ (-(7 / 2 : ℝ)) := by ring
      _ ≤ C * 1 * |v| ^ (-(7 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    rw [hd2 v hv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have := (hb (c * v) (hω v hv)).2.2
    rw [habs, Real.mul_rpow hc0.le (abs_nonneg v)] at this
    have hcr : c * (c * c ^ (-(9 / 2 : ℝ))) ≤ 1 := by
      have : c * (c * c ^ (-(9 / 2 : ℝ))) = c ^ (-(5 / 2 : ℝ)) := by
        rw [show c * (c * c ^ (-(9 / 2 : ℝ))) = c ^ (1 : ℝ) * (c ^ (1 : ℝ) * c ^ (-(9 / 2 : ℝ))) by rw [Real.rpow_one],
          ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      rw [this]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
    calc c * (c * ‖g2 (c * v)‖) ≤ c * (c * (C * (c ^ (-(9 / 2 : ℝ)) * |v| ^ (-(9 / 2 : ℝ))))) := by gcongr
      _ = C * (c * (c * c ^ (-(9 / 2 : ℝ)))) * |v| ^ (-(9 / 2 : ℝ)) := by ring
      _ ≤ C * 1 * |v| ^ (-(9 / 2 : ℝ)) := by gcongr
      _ = _ := by ring

/-- Stationary tail Fourier transform `∫_{x₀}^∞ b(x) e^{-i q x} dx` for `b` of `SymBd 1 x₀ (5/2) M b`:
`C¹` on `ℝ`, `C²` on `{q ≠ 0}`, and `‖g''(q)‖ ≤ C |q|^{-1/2}` on `0 < |q| ≤ ceCs`. -/
lemma fourier_sym_stationary {x₀ M : ℝ} (hx₀ : 1 ≤ x₀) (hM : 0 ≤ M) {b : ℝ → ℂ}
    (hb : SymBd 1 x₀ (5 / 2) M b) :
    let g : ℝ → ℂ := fun q => ∫ x in Ici x₀, b x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
    ContDiff ℝ 1 g ∧ ∃ C > 0, ∀ q : ℝ, q ≠ 0 → |q| ≤ ceCs →
      DifferentiableAt ℝ (deriv g) q ∧ ‖deriv (deriv g) q‖ ≤ C * |q| ^ (-(1 / 2 : ℝ)) := by
  intro g
  have hx0_pos : 0 < x₀ := by linarith
  have hbc : ContinuousOn b (Ici x₀) := hb.cd.continuousOn
  have hbm_i : AEStronglyMeasurable b (volume.restrict (Ici x₀)) := hbc.aestronglyMeasurable measurableSet_Ici
  have hint0 : ∀ q : ℝ, IntegrableOn (fun x : ℝ => b x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ici x₀) := fun q => by
    refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul M).mono'
      (hbm_i.mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
    exact hb.bd0_le hx0_pos (mem_Ici.mp hx)
  have hint1 : ∀ q : ℝ, IntegrableOn (fun x : ℝ => (-Complex.I * (x : ℂ) * b x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ici x₀) := fun q => by
    refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M).mono'
      (((by fun_prop : AEStronglyMeasurable (fun x : ℝ => -Complex.I * (x : ℂ)) _).mul hbm_i).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
    have h0 := hb.bd0_le hx0_pos (mem_Ici.mp hx)
    calc x * ‖b x‖ ≤ x * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 hxpos.le
      _ = M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
  let g₁ : ℝ → ℂ := fun q => ∫ x in Ici x₀, (-Complex.I * (x : ℂ) * b x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
  have hhd1 : ∀ q : ℝ, HasDerivAt g (g₁ q) q := fun q => by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ici x₀))
      (F := fun (q' : ℝ) (x : ℝ) => b x * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))))
      (F' := fun (q' : ℝ) (x : ℝ) => (-Complex.I * (x : ℂ) * b x) * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))))
      (ball_mem_nhds q one_pos)
      (Eventually.of_forall fun (q' : ℝ) => (hint0 q').aestronglyMeasurable)
      (hint0 q) (hint1 q).aestronglyMeasurable ?_
      ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M) ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx q' _
      have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
      have h0 := hb.bd0_le hx0_pos (mem_Ici.mp hx)
      calc x * ‖b x‖ ≤ x * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 hxpos.le
        _ = M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x _ q' _
      have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (s : ℂ) * (x : ℂ))) (-Complex.I * (x : ℂ)) q' :=
        (((Complex.ofRealCLM.hasDerivAt (x := q')).const_mul (-Complex.I * (x : ℂ))).congr_of_eventuallyEq
          (Eventually.of_forall fun s => by simp; ring)).congr_deriv (by simp)
      exact (hl.cexp.const_mul (b x)).congr_deriv (by ring)
  have hcont_g1 : Continuous g₁ := by
    refine continuous_of_dominated (fun q => (hint1 q).aestronglyMeasurable) (fun q => ?_)
      ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M)
      (ae_of_all _ fun x => by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
    have h0 := hb.bd0_le hx0_pos (mem_Ici.mp hx)
    calc x * ‖b x‖ ≤ x * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 hxpos.le
      _ = M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ = M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
  have hcd1 : ContDiff ℝ 1 g := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiff_succ_iff_deriv]
    refine ⟨fun q => (hhd1 q).differentiableAt, fun h => by simp at h, ?_⟩
    rw [show deriv g = g₁ from funext fun q => (hhd1 q).deriv, contDiff_zero]
    exact hcont_g1
  refine ⟨hcd1, 2 * M * (4 * x₀ + 1) ^ (1 / 2 : ℝ) + 12 * M + 1, by positivity, fun q₀ hq₀ hqcs => ?_⟩
  rw [show deriv g = g₁ from funext fun q => (hhd1 q).deriv]
  have hqabs : 0 < |q₀| := abs_pos.mpr hq₀
  let T : ℝ := max (2 * x₀) (1 / |q₀|)
  have hT_gt : x₀ < T := by
    have : x₀ < 2 * x₀ := by linarith
    exact this.trans_le (le_max_left _ _)
  have hT_pos : 0 < T := lt_trans hx0_pos hT_gt
  have hTq : 1 / |q₀| ≤ T := le_max_right _ _
  have hT_up : T ≤ (4 * x₀ + 1) * |q₀|⁻¹ := by
    have h1 : 2 * x₀ ≤ 4 * x₀ * |q₀|⁻¹ := by
      have hcs2 := (show ceCs < 2 from by
        have hpi : Real.pi < 3.15 := Real.pi_lt_d2
        have h3 : Real.pi ^ 2 / 3 < 2 ^ 3 := by nlinarith [Real.pi_pos]
        calc ceCs = (Real.pi ^ 2 / 3) ^ (1 / 3 : ℝ) := rfl
          _ < (2 ^ 3 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) h3 (by norm_num)
          _ = 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num)
      have h2x : 2 * x₀ * |q₀| ≤ 4 * x₀ := by nlinarith
      rw [← div_eq_mul_inv, le_div_iff₀ hqabs]
      linarith
    exact max_le (by linarith [inv_pos.mpr hqabs]) (by rw [one_div]; linarith [mul_nonneg (show 0 ≤ 4 * x₀ by linarith) (inv_nonneg.mpr hqabs.le)])
  -- Split `g₁ q = near T q + far T q`
  let F_q : ℝ → ℝ → ℂ := fun q x => (-Complex.I * (x : ℂ) * b x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
  let g_near : ℝ → ℂ := fun q => ∫ x in Ico x₀ T, F_q q x
  let g_far : ℝ → ℂ := fun q => ∫ x in Ici T, F_q q x
  have hsplit_g1 : ∀ q : ℝ, g₁ q = g_near q + g_far q := fun q => by
    have hu : Ico x₀ T ∪ Ici T = Ici x₀ := Ico_union_Ici_eq_Ici hT_gt.le
    have hdisj : Disjoint (Ico x₀ T) (Ici T) := Set.disjoint_left.mpr fun _ h1 h2 => not_le_of_gt h1.2 h2
    dsimp [g₁, g_near, g_far]
    rw [← hu]
    exact setIntegral_union hdisj measurableSet_Ici
      ((hint1 q).mono_set (hu ▸ subset_union_left)) ((hint1 q).mono_set (hu ▸ subset_union_right))
  -- Derivative of `g_near` at `q₀`
  have hint_near2 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q₀ : ℂ) * (x : ℂ)))) (Ico x₀ T) := by
    have hicc : IntegrableOn (fun _ : ℝ => M * x₀ ^ (-(1 / 2 : ℝ))) (Ico x₀ T) :=
      integrableOn_const (hs := measure_Ico_lt_top.ne)
    refine hicc.mono' ((((Complex.continuous_ofReal.pow 2).continuousOn.mul (hbc.mono Ico_subset_Ici_self)).aestronglyMeasurable
      measurableSet_Ico).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hxpos : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos,
      norm_cexp_neg_I_mul, mul_one]
    have h0 := hb.bd0_le hx0_pos hx.1
    calc x ^ 2 * ‖b x‖ ≤ x ^ 2 * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 (sq_nonneg x)
      _ = M * (x ^ (2 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by simp; ring
      _ = M * x ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
      _ ≤ M * x₀ ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hx0_pos hx.1 (by norm_num)) hM
  have hhd_near : HasDerivAt g_near
      (-∫ x in Ico x₀ T, (x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q₀ : ℂ) * (x : ℂ)))) q₀ := by
    have hneg_meas : AEStronglyMeasurable
        (fun x : ℝ => -((x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q₀ : ℂ) * (x : ℂ))))) (volume.restrict (Ico x₀ T)) :=
      hint_near2.neg.aestronglyMeasurable
    have hd_pos := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ico x₀ T))
      (F := fun (q' : ℝ) (x : ℝ) => (-Complex.I * (x : ℂ) * b x) * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))))
      (F' := fun (q' : ℝ) (x : ℝ) => -((x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ)))))
      (ball_mem_nhds q₀ one_pos)
      (Eventually.of_forall fun (q' : ℝ) => ((hint1 q').mono_set Ico_subset_Ici_self).aestronglyMeasurable)
      ((hint1 q₀).mono_set Ico_subset_Ici_self)
      hneg_meas ?_
      (integrableOn_const (hs := measure_Ico_lt_top.ne) (C := M * x₀ ^ (-(1 / 2 : ℝ)))) ?_).2
    · rw [integral_neg] at hd_pos; exact hd_pos
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx q' _
      have hxpos : 0 < x := by linarith [hx.1]
      rw [norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos,
        norm_cexp_neg_I_mul, mul_one]
      have h0 := hb.bd0_le hx0_pos hx.1
      calc x ^ 2 * ‖b x‖ ≤ x ^ 2 * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 (sq_nonneg x)
        _ = M * (x ^ (2 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_two]; ring
        _ = M * x ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
        _ ≤ M * x₀ ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hx0_pos hx.1 (by norm_num)) hM
    · filter_upwards [ae_restrict_mem measurableSet_Ico] with x _ q' _
      have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (s : ℂ) * (x : ℂ))) (-Complex.I * (x : ℂ)) q' :=
        (((Complex.ofRealCLM.hasDerivAt (x := q')).const_mul (-Complex.I * (x : ℂ))).congr_of_eventuallyEq
          (Eventually.of_forall fun s => by simp; ring)).congr_deriv (by simp)
      exact (hl.cexp.const_mul (-Complex.I * (x : ℂ) * b x)).congr_deriv (by
        have hi2 : -Complex.I * (-Complex.I) = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
        linear_combination (x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))) * hi2)
  have hnorm_near : ‖-∫ x in Ico x₀ T, (x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q₀ : ℂ) * (x : ℂ)))‖ ≤
      (2 * M * (4 * x₀ + 1) ^ (1 / 2 : ℝ)) * |q₀| ^ (-(1 / 2 : ℝ)) := by
    rw [norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hi_norm : IntegrableOn (fun x : ℝ => M * x ^ (-(1 / 2 : ℝ))) (Ico x₀ T) := by
      have hcIcc : ContinuousOn (fun x : ℝ => M * x ^ (-(1 / 2 : ℝ))) (Icc x₀ T) :=
        continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
          Or.inl (ne_of_gt (hx0_pos.trans_le (mem_Icc.mp hx).1)))
      exact hcIcc.integrableOn_Icc.mono_set Ico_subset_Icc_self
    have h1 := setIntegral_mono_on hint_near2.norm hi_norm measurableSet_Ico fun x hx => by
      have hxpos : 0 < x := by linarith [hx.1]
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
      have h0 := hb.bd0_le hx0_pos hx.1
      calc x ^ 2 * ‖b x‖ ≤ x ^ 2 * (M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h0 (sq_nonneg x)
        _ = M * (x ^ (2 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_two]; ring
        _ = M * x ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    have hint_sqrt : ∫ x in Ico x₀ T, M * x ^ (-(1 / 2 : ℝ)) ≤ 2 * M * T ^ (1 / 2 : ℝ) := by
      rw [integral_const_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT_gt.le]
      have hftc : ∫ x in x₀..T, x ^ (-(1 / 2 : ℝ)) = 2 * T ^ (1 / 2 : ℝ) - 2 * x₀ ^ (1 / 2 : ℝ) := by
        have hc_u : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (uIcc x₀ T) := by
          rw [uIcc_of_le hT_gt.le]
          exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hx0_pos.trans_le (mem_Icc.mp hx).1))
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x₀) (b := T)
          (f := fun x : ℝ => 2 * x ^ (1 / 2 : ℝ)) (f' := fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
          (fun x hx => by
            have hxpos : 0 < x := by rw [uIcc_of_le hT_gt.le] at hx; exact hx0_pos.trans_le (mem_Icc.mp hx).1
            exact (((hasDerivAt_id x).rpow_const (Or.inl hxpos.ne')).const_mul 2).congr_deriv (by norm_num; ring))
          hc_u.intervalIntegrable
      rw [hftc]
      have hx0_s : 0 ≤ x₀ ^ (1 / 2 : ℝ) := by positivity
      nlinarith
    have hT_sq : T ^ (1 / 2 : ℝ) ≤ (4 * x₀ + 1) ^ (1 / 2 : ℝ) * |q₀| ^ (-(1 / 2 : ℝ)) := by
      calc T ^ (1 / 2 : ℝ) ≤ ((4 * x₀ + 1) * |q₀|⁻¹) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hT_pos.le hT_up (by norm_num)
        _ = (4 * x₀ + 1) ^ (1 / 2 : ℝ) * (|q₀|⁻¹) ^ (1 / 2 : ℝ) :=
            Real.mul_rpow (by linarith) (inv_nonneg.mpr hqabs.le)
        _ = (4 * x₀ + 1) ^ (1 / 2 : ℝ) * |q₀| ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_neg hqabs.le, Real.inv_rpow hqabs.le]
    calc _ ≤ ∫ x in Ico x₀ T, M * x ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ 2 * M * T ^ (1 / 2 : ℝ) := hint_sqrt
      _ ≤ 2 * M * ((4 * x₀ + 1) ^ (1 / 2 : ℝ) * |q₀| ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = (2 * M * (4 * x₀ + 1) ^ (1 / 2 : ℝ)) * |q₀| ^ (-(1 / 2 : ℝ)) := by ring
  -- On `Ici T`, `g_far q` equals IBP form on `q ∈ ball q₀ (|q₀|/2)`!
  have hbd : SymBd 0 (2 * x₀) (7 / 2) M (deriv b) := by
    simpa [show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num] using hb.deriv_gt (by linarith : x₀ < 2 * x₀)
  have hbdc : ContinuousOn (deriv b) (Ici T) := (hbd.mono_left (le_max_left _ _)).cd.continuousOn
  let u : ℝ → ℂ := fun x => (x : ℂ) * b x
  let du : ℝ → ℂ := fun x => b x + (x : ℂ) * deriv b x
  have hdu_bd : ∀ x : ℝ, T ≤ x → ‖du x‖ ≤ 2 * M * x ^ (-(5 / 2 : ℝ)) := fun x hx => by
    have hxpos : 0 < x := by linarith
    have b0 := hb.bd0_le hx0_pos (by linarith)
    have b1 := hbd.bd0_le (by linarith : 0 < 2 * x₀) (le_trans (le_max_left _ _) hx)
    have s2 : ‖(x : ℂ) * deriv b x‖ ≤ M * x ^ (-(5 / 2 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
      calc x * ‖deriv b x‖ ≤ x * (M * x ^ (-(7 / 2 : ℝ))) := mul_le_mul_of_nonneg_left b1 hxpos.le
        _ = M * (x ^ (1 : ℝ) * x ^ (-(7 / 2 : ℝ))) := by simp; ring
        _ = M * x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    exact (norm_add_le _ _).trans (add_le_add b0 s2 |>.trans_eq (by ring))
  have hdu_cont : ContinuousOn du (Ici T) :=
    (hbc.mono (Ici_subset_Ici.mpr hT_gt.le)).add (Complex.continuous_ofReal.continuousOn.mul hbdc)
  have hfar_ibp : ∀ q : ℝ, q ≠ 0 →
      g_far q = -(((T : ℂ) * b T) / (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (T : ℂ))) -
        (1 / (q : ℂ)) * ∫ x in Ici T, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ))) := fun q hq => by
    have hq_ne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    have hdu_int : IntegrableOn (fun x : ℝ => du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ioi T) := by
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul (2 * M)).mono'
        ((hdu_cont.aestronglyMeasurable measurableSet_Ici).mul (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
      exact hdu_bd x hx
    have hF_oi : IntegrableOn (F_q q) (Ioi T) :=
      ((hint1 q).mono_set (Ici_subset_Ici.mpr hT_gt.le)).mono_set Ioi_subset_Ici_self
    have hinterval : ∀ R : ℝ, T ≤ R →
        ∫ x in T..R, F_q q x =
          -(((T : ℂ) * b T) / (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (T : ℂ))) +
          (((R : ℂ) * b R) / (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (R : ℂ))) -
          (1 / (q : ℂ)) * ∫ x in T..R, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ))) := fun R hR => by
      have hftc : ∫ x in T..R, (-Complex.I * (q : ℂ) * u x + du x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ))) =
          u R * cexp (-(Complex.I * (q : ℂ) * (R : ℂ))) - u T * cexp (-(Complex.I * (q : ℂ) * (T : ℂ))) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => u s * cexp (-(Complex.I * (q : ℂ) * (s : ℂ))))
          (fun t ht => ?_) ?_
        · have ht_gt : x₀ < t := by rw [uIcc_of_le hR] at ht; linarith [(mem_Icc.mp ht).1]
          have hdb : HasDerivAt b (deriv b t) t :=
            ((hb.cd.mono Ioi_subset_Ici_self).differentiableOn (by norm_num)).differentiableAt
              (isOpen_Ioi.mem_nhds ht_gt) |>.hasDerivAt
          have hdu' : HasDerivAt u (du t) t :=
            ((Complex.ofRealCLM.hasDerivAt (x := t)).mul hdb).congr_of_eventuallyEq
              (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by dsimp [du]; simp)
          have hexp' : HasDerivAt (fun s : ℝ => cexp (-(Complex.I * (q : ℂ) * (s : ℂ))))
              ((-Complex.I * (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (t : ℂ)))) t := by
            have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (q : ℂ) * (s : ℂ))) (-Complex.I * (q : ℂ)) t :=
              (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(Complex.I * (q : ℂ)))).congr_of_eventuallyEq
                (Eventually.of_forall fun s => by simp)).congr_deriv (by simp)
            exact hl.cexp.congr_deriv (by ring)
          exact (hdu'.mul hexp').congr_deriv (by ring)
        · have hicc : uIcc T R ⊆ Ici T := by rw [uIcc_of_le hR]; exact fun _ h => h.1
          have huc : ContinuousOn u (uIcc T R) :=
            Complex.continuous_ofReal.continuousOn.mul ((hbc.mono (Ici_subset_Ici.mpr hT_gt.le)).mono hicc)
          exact ((continuousOn_const.mul huc).add (hdu_cont.mono hicc)).mul (by fun_prop) |>.intervalIntegrable
      have hi_1 : IntervalIntegrable (F_q q) volume T R := by
        have hicc : uIcc T R ⊆ Ici T := by rw [uIcc_of_le hR]; exact fun _ h => h.1
        exact ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn)).mul
          ((hbc.mono (Ici_subset_Ici.mpr hT_gt.le)).mono hicc)).mul (by fun_prop) |>.intervalIntegrable
      have hi_2 : IntervalIntegrable (fun x : ℝ => du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) volume T R := by
        have hicc : uIcc T R ⊆ Ici T := by rw [uIcc_of_le hR]; exact fun _ h => h.1
        exact ((hdu_cont.mono hicc).mul (by fun_prop)).intervalIntegrable
      have heq_f : (fun x : ℝ => (-Complex.I * (q : ℂ) * u x + du x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) =
          fun x : ℝ => (q : ℂ) * F_q q x + du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ))) := by
        ext x; dsimp [F_q, u]; ring
      rw [heq_f, intervalIntegral.integral_add (hi_1.const_mul _) hi_2, intervalIntegral.integral_const_mul] at hftc
      have hdiv := congrArg (fun z : ℂ => z / (q : ℂ)) hftc
      rw [add_div, mul_div_cancel_left₀ _ hq_ne] at hdiv
      dsimp [u] at hdiv
      calc ∫ x in T..R, F_q q x
          = ((R : ℂ) * b R * cexp (-(Complex.I * (q : ℂ) * (R : ℂ))) -
              (T : ℂ) * b T * cexp (-(Complex.I * (q : ℂ) * (T : ℂ)))) / (q : ℂ) -
              (∫ x in T..R, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) / (q : ℂ) :=
            eq_sub_of_add_eq hdiv
        _ = _ := by field_simp; ring
    have ht1 : Tendsto (fun R : ℝ => ∫ x in T..R, F_q q x) atTop (𝓝 (g_far q)) := by
      simpa [g_far, integral_Ici_eq_integral_Ioi] using intervalIntegral_tendsto_integral_Ioi T hF_oi tendsto_id
    have ht2 : Tendsto (fun R : ℝ => ∫ x in T..R, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) atTop
        (𝓝 (∫ x in Ici T, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ))))) := by
      simpa [integral_Ici_eq_integral_Ioi] using intervalIntegral_tendsto_integral_Ioi T hdu_int tendsto_id
    have htb : Tendsto (fun R : ℝ => (((R : ℂ) * b R) / (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (R : ℂ)))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have ht0 : Tendsto (fun R : ℝ => (M / |q|) * R ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (M / |q|)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht0
        (Eventually.of_forall fun _ => norm_nonneg _) ?_
      filter_upwards [eventually_ge_atTop T] with R hR
      have hRp : 0 < R := by linarith
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp,
        Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_I_mul, mul_one]
      have hbR := hb.bd0_le hx0_pos (by linarith)
      calc R * ‖b R‖ / |q| ≤ R * (M * R ^ (-(5 / 2 : ℝ))) / |q| := by gcongr
        _ = (M / |q|) * (R ^ (1 : ℝ) * R ^ (-(5 / 2 : ℝ))) := by simp; ring
        _ = (M / |q|) * R ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hRp]; norm_num
    have htr := ((tendsto_const_nhds.add htb).sub (ht2.const_mul (1 / (q : ℂ))))
    simpa [add_zero] using tendsto_nhds_unique ht1 (htr.congr' (by
      filter_upwards [eventually_ge_atTop T] with R hR using (hinterval R hR).symm))
  -- Differentiate the RHS of `hfar_ibp` at `q₀`
  let J_du : ℝ → ℂ := fun q => ∫ x in Ici T, du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
  let J_du' : ℝ → ℂ := fun q => ∫ x in Ici T, (-Complex.I * (x : ℂ) * du x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
  have hJdu_int : ∀ q : ℝ, IntegrableOn (fun x : ℝ => du x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ici T) := fun q => by
    refine ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul (2 * M)).mono'
      ((hdu_cont.aestronglyMeasurable measurableSet_Ici).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
    exact hdu_bd x hx
  have hJdu'_int : ∀ q : ℝ, IntegrableOn (fun x : ℝ => (-Complex.I * (x : ℂ) * du x) * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ici T) := fun q => by
    refine ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul (2 * M)).mono'
      (((by fun_prop : AEStronglyMeasurable (fun x : ℝ => -Complex.I * (x : ℂ)) _).mul
        (hdu_cont.aestronglyMeasurable measurableSet_Ici)).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
    calc x * ‖du x‖ ≤ x * (2 * M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hdu_bd x hx) hxpos.le
      _ = 2 * M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by simp; ring
      _ = 2 * M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
  have hhd_Jdu : HasDerivAt J_du (J_du' q₀) q₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ici T))
      (F := fun (q' : ℝ) (x : ℝ) => du x * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))))
      (F' := fun (q' : ℝ) (x : ℝ) => (-Complex.I * (x : ℂ) * du x) * cexp (-(Complex.I * (q' : ℂ) * (x : ℂ))))
      (ball_mem_nhds q₀ one_pos)
      (Eventually.of_forall fun (q' : ℝ) => (hJdu_int q').aestronglyMeasurable)
      (hJdu_int q₀) (hJdu'_int q₀).aestronglyMeasurable ?_
      ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul (2 * M)) ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx q' _
      have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
      calc x * ‖du x‖ ≤ x * (2 * M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hdu_bd x hx) hxpos.le
        _ = 2 * M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = 2 * M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x _ q' _
      have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (s : ℂ) * (x : ℂ))) (-Complex.I * (x : ℂ)) q' :=
        (((Complex.ofRealCLM.hasDerivAt (x := q')).const_mul (-Complex.I * (x : ℂ))).congr_of_eventuallyEq
          (Eventually.of_forall fun s => by simp; ring)).congr_deriv (by simp)
      exact (hl.cexp.const_mul (du x)).congr_deriv (by ring)
  have hinv_q : HasDerivAt (fun q : ℝ => (1 : ℂ) / (q : ℂ)) (-(1 : ℂ) / (q₀ : ℂ) ^ 2) q₀ := by
    have hq0_c : (q₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀
    exact ((Complex.ofRealCLM.hasDerivAt (x := q₀)).inv hq0_c).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => by simp) |>.congr_deriv (by simp)
  let bdry : ℝ → ℂ := fun q => -(((T : ℂ) * b T) / (q : ℂ)) * cexp (-(Complex.I * (q : ℂ) * (T : ℂ)))
  let bdry' : ℂ := ((T : ℂ) * b T / (q₀ : ℂ) ^ 2 +
      Complex.I * (T : ℂ) ^ 2 * b T / (q₀ : ℂ)) * cexp (-(Complex.I * (q₀ : ℂ) * (T : ℂ)))
  have hhd_bdry : HasDerivAt bdry bdry' q₀ := by
    have h1 := hinv_q.const_mul (-((T : ℂ) * b T))
    have h2 : HasDerivAt (fun q : ℝ => cexp (-(Complex.I * (q : ℂ) * (T : ℂ))))
        ((-Complex.I * (T : ℂ)) * cexp (-(Complex.I * (q₀ : ℂ) * (T : ℂ)))) q₀ := by
      have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (s : ℂ) * (T : ℂ))) (-Complex.I * (T : ℂ)) q₀ :=
        (((Complex.ofRealCLM.hasDerivAt (x := q₀)).const_mul (-Complex.I * (T : ℂ))).congr_of_eventuallyEq
          (Eventually.of_forall fun s => by simp; ring)).congr_deriv (by simp)
      exact hl.cexp.congr_deriv (by ring)
    exact ((h1.mul h2).congr_of_eventuallyEq (Eventually.of_forall fun q => by dsimp [bdry]; ring)).congr_deriv
      (by dsimp [bdry']; ring)
  let far_rhs : ℝ → ℂ := fun q => bdry q - (1 / (q : ℂ)) * J_du q
  let far_rhs' : ℂ := bdry' - (-(1 : ℂ) / (q₀ : ℂ) ^ 2 * J_du q₀ + (1 / (q₀ : ℂ)) * J_du' q₀)
  have hhd_far_rhs : HasDerivAt far_rhs far_rhs' q₀ := hhd_bdry.sub (hinv_q.mul hhd_Jdu)
  have hev_eq : g_far =ᶠ[𝓝 q₀] far_rhs := by
    filter_upwards [isOpen_ne.mem_nhds hq₀] with q hq
    exact hfar_ibp q hq
  have hhd_far : HasDerivAt g_far far_rhs' q₀ := hhd_far_rhs.congr_of_eventuallyEq hev_eq
  have hhd_g1 : HasDerivAt g₁ ((-∫ x in Ico x₀ T, (x : ℂ) ^ 2 * b x * cexp (-(Complex.I * (q₀ : ℂ) * (x : ℂ)))) + far_rhs') q₀ :=
    (hhd_near.add hhd_far).congr_of_eventuallyEq (Eventually.of_forall hsplit_g1)
  refine ⟨hhd_g1.differentiableAt, ?_⟩
  rw [hhd_g1.deriv]
  -- Bound `‖far_rhs'‖ ≤ 12 * M * |q₀|^{-1/2}`
  have hT_inv_le : T⁻¹ ≤ |q₀| := (inv_le_comm₀ hT_pos hqabs).mpr (by simpa using hTq)
  have hT_32 : T ^ (-(3 / 2 : ℝ)) ≤ |q₀| ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg hT_pos.le, ← Real.inv_rpow hT_pos.le]
    exact Real.rpow_le_rpow (by positivity) hT_inv_le (by norm_num)
  have hT_12 : T ^ (-(1 / 2 : ℝ)) ≤ |q₀| ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hT_pos.le, ← Real.inv_rpow hT_pos.le]
    exact Real.rpow_le_rpow (by positivity) hT_inv_le (by norm_num)
  have hbT : ‖b T‖ ≤ M * T ^ (-(5 / 2 : ℝ)) := hb.bd0_le hx0_pos (by linarith)
  have hbd_bdry : ‖bdry'‖ ≤ 2 * M * |q₀| ^ (-(1 / 2 : ℝ)) := by
    dsimp [bdry']
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
    have t1 : ‖(T : ℂ) * b T / (q₀ : ℂ) ^ 2‖ ≤ M * |q₀| ^ (-(1 / 2 : ℝ)) := by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT_pos,
        Complex.norm_real, Real.norm_eq_abs]
      calc T * ‖b T‖ / |q₀| ^ 2 ≤ T * (M * T ^ (-(5 / 2 : ℝ))) / |q₀| ^ 2 := by gcongr
        _ = M * (T ^ (1 : ℝ) * T ^ (-(5 / 2 : ℝ))) * |q₀| ^ (-2 : ℝ) := by
            rw [Real.rpow_one, div_eq_mul_inv, ← Real.rpow_natCast |q₀| 2, ← Real.rpow_neg hqabs.le]; ring
        _ = M * T ^ (-(3 / 2 : ℝ)) * |q₀| ^ (-2 : ℝ) := by
            rw [← Real.rpow_add hT_pos]; norm_num
        _ ≤ M * |q₀| ^ (3 / 2 : ℝ) * |q₀| ^ (-2 : ℝ) := by gcongr
        _ = M * |q₀| ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hqabs]; norm_num
    have t2 : ‖Complex.I * (T : ℂ) ^ 2 * b T / (q₀ : ℂ)‖ ≤ M * |q₀| ^ (-(1 / 2 : ℝ)) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hT_pos, Complex.norm_real, Real.norm_eq_abs]
      calc T ^ 2 * ‖b T‖ / |q₀| ≤ T ^ 2 * (M * T ^ (-(5 / 2 : ℝ))) / |q₀| := by gcongr
        _ = M * (T ^ (2 : ℝ) * T ^ (-(5 / 2 : ℝ))) * |q₀| ^ (-1 : ℝ) := by
            rw [Real.rpow_two, div_eq_mul_inv, ← Real.rpow_neg_one |q₀|]; ring
        _ = M * T ^ (-(1 / 2 : ℝ)) * |q₀| ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hT_pos]; norm_num
        _ ≤ M * |q₀| ^ (1 / 2 : ℝ) * |q₀| ^ (-1 : ℝ) := by gcongr
        _ = M * |q₀| ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hqabs]; norm_num
    exact (norm_add_le _ _).trans (add_le_add t1 t2 |>.trans_eq (by ring))
  have hI_52 : ∫ x in Ici T, x ^ (-(5 / 2 : ℝ)) ≤ (2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ)) := by
    have hid := intervalIntegral_tendsto_integral_Ioi T (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) hT_pos) tendsto_id
    have hftc : ∀ R : ℝ, T ≤ R → ∫ x in T..R, x ^ (-(5 / 2 : ℝ)) =
        -(2 / 3 : ℝ) * R ^ (-(3 / 2 : ℝ)) + (2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ)) := fun R hR => by
      have hc_u : ContinuousOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ))) (uIcc T R) := by
        rw [uIcc_of_le hR]
        exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hT_pos.trans_le (mem_Icc.mp hx).1))
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := T) (b := R)
        (f := fun x : ℝ => -(2 / 3 : ℝ) * x ^ (-(3 / 2 : ℝ))) (f' := fun x : ℝ => x ^ (-(5 / 2 : ℝ)))
        (fun x hx => by
          have hxpos : 0 < x := by rw [uIcc_of_le hR] at hx; exact hT_pos.trans_le (mem_Icc.mp hx).1
          exact (((hasDerivAt_id x).rpow_const (Or.inl hxpos.ne')).const_mul (-(2 / 3 : ℝ))).congr_deriv
            (by norm_num; ring))
        hc_u.intervalIntegrable
      linarith [hi]
    have ht0 : Tendsto (fun R : ℝ => -(2 / 3 : ℝ) * R ^ (-(3 / 2 : ℝ)) + (2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ)))
        atTop (𝓝 ((2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ)))) := by
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (-(2 / 3 : ℝ))
      simpa using this.add tendsto_const_nhds
    have hlim := tendsto_nhds_unique hid (ht0.congr' (by
      filter_upwards [eventually_ge_atTop T] with R hR using (hftc R hR).symm))
    rw [integral_Ici_eq_integral_Ioi, hlim]
  have hI_32 : ∫ x in Ici T, x ^ (-(3 / 2 : ℝ)) ≤ 2 * T ^ (-(1 / 2 : ℝ)) := by
    have hid := intervalIntegral_tendsto_integral_Ioi T (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hT_pos) tendsto_id
    have hftc : ∀ R : ℝ, T ≤ R → ∫ x in T..R, x ^ (-(3 / 2 : ℝ)) =
        -2 * R ^ (-(1 / 2 : ℝ)) + 2 * T ^ (-(1 / 2 : ℝ)) := fun R hR => by
      have hc_u : ContinuousOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (uIcc T R) := by
        rw [uIcc_of_le hR]
        exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hT_pos.trans_le (mem_Icc.mp hx).1))
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := T) (b := R)
        (f := fun x : ℝ => -2 * x ^ (-(1 / 2 : ℝ))) (f' := fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
        (fun x hx => by
          have hxpos : 0 < x := by rw [uIcc_of_le hR] at hx; exact hT_pos.trans_le (mem_Icc.mp hx).1
          exact (((hasDerivAt_id x).rpow_const (Or.inl hxpos.ne')).const_mul (-2)).congr_deriv
            (by norm_num; ring))
        hc_u.intervalIntegrable
      linarith [hi]
    have ht0 : Tendsto (fun R : ℝ => -2 * R ^ (-(1 / 2 : ℝ)) + 2 * T ^ (-(1 / 2 : ℝ)))
        atTop (𝓝 (2 * T ^ (-(1 / 2 : ℝ)))) := by
      have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (-2 : ℝ)
      simpa using this.add tendsto_const_nhds
    have hlim := tendsto_nhds_unique hid (ht0.congr' (by
      filter_upwards [eventually_ge_atTop T] with R hR using (hftc R hR).symm))
    rw [integral_Ici_eq_integral_Ioi, hlim]
  have hJdu_norm : ‖J_du q₀‖ ≤ 2 * M * ((2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := setIntegral_mono_on (hJdu_int q₀).norm
      ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul (2 * M))
      measurableSet_Ici fun x hx => by
        rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
        exact hdu_bd x hx
    exact hmono.trans ((integral_const_mul (2 * M) _).le.trans (mul_le_mul_of_nonneg_left hI_52 (by positivity)))
  have hJdu'_norm : ‖J_du' q₀‖ ≤ 2 * M * (2 * T ^ (-(1 / 2 : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := setIntegral_mono_on (hJdu'_int q₀).norm
      ((integrableOn_Ici_rpow_of_lt hT_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul (2 * M))
      measurableSet_Ici fun x hx => by
        have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
        rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos, norm_cexp_neg_I_mul, mul_one]
        calc x * ‖du x‖ ≤ x * (2 * M * x ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hdu_bd x hx) hxpos.le
          _ = 2 * M * (x ^ (1 : ℝ) * x ^ (-(5 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
          _ = 2 * M * x ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hxpos]; norm_num
    exact hmono.trans ((integral_const_mul (2 * M) _).le.trans (mul_le_mul_of_nonneg_left hI_32 (by positivity)))
  have t3 : ‖-(1 : ℂ) / (q₀ : ℂ) ^ 2 * J_du q₀‖ ≤ (4 / 3 : ℝ) * M * |q₀| ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_div, norm_neg, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc 1 / |q₀| ^ 2 * ‖J_du q₀‖ ≤ 1 / |q₀| ^ 2 * (2 * M * ((2 / 3 : ℝ) * T ^ (-(3 / 2 : ℝ)))) := by gcongr
      _ = (4 / 3 : ℝ) * M * T ^ (-(3 / 2 : ℝ)) * |q₀| ^ (-2 : ℝ) := by
          rw [one_div, ← Real.rpow_natCast |q₀| 2, ← Real.rpow_neg hqabs.le]; ring
      _ ≤ (4 / 3 : ℝ) * M * |q₀| ^ (3 / 2 : ℝ) * |q₀| ^ (-2 : ℝ) := by gcongr
      _ = (4 / 3 : ℝ) * M * |q₀| ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hqabs]; norm_num
  have t4 : ‖(1 / (q₀ : ℂ)) * J_du' q₀‖ ≤ 4 * M * |q₀| ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs]
    calc 1 / |q₀| * ‖J_du' q₀‖ ≤ 1 / |q₀| * (2 * M * (2 * T ^ (-(1 / 2 : ℝ)))) := by gcongr
      _ = 4 * M * T ^ (-(1 / 2 : ℝ)) * |q₀| ^ (-1 : ℝ) := by
          rw [one_div, ← Real.rpow_neg_one |q₀|]; ring
      _ ≤ 4 * M * |q₀| ^ (1 / 2 : ℝ) * |q₀| ^ (-1 : ℝ) := by gcongr
      _ = 4 * M * |q₀| ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add hqabs]; norm_num
  have hfar_bd : ‖far_rhs'‖ ≤ 12 * M * |q₀| ^ (-(1 / 2 : ℝ)) := by
    dsimp [far_rhs']
    have hr := (norm_sub_le _ _).trans (add_le_add hbd_bdry ((norm_add_le _ _).trans (add_le_add t3 t4)))
    have hp : 0 ≤ M * |q₀| ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hqnn : 0 ≤ |q₀| ^ (-(1 / 2 : ℝ)) := by positivity
  exact (norm_add_le _ _).trans ((add_le_add hnorm_near hfar_bd).trans (by nlinarith))

/-- Oscillatory phase Fourier transform for `b` of `SymBd 3 x₀ 2 M b` (`σ = ±1`): `ContDiff ℝ 2`. -/
lemma fourier_sym_osc {x₀ M σ : ℝ} (hx₀ : 4 ≤ x₀) (hM : 0 ≤ M) (hσ : σ = 1 ∨ σ = -1)
    {b : ℝ → ℂ} (hb : SymBd 3 (x₀ - 3) 2 M b) :
    ContDiff ℝ 2 (fun q : ℝ =>
      ∫ x in Ici x₀, b x * cexp (Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))) := by
  have hx0_pos : 0 < x₀ := by linarith
  have hx0_1 : 1 ≤ x₀ := by linarith
  have hσ_ne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  let ph : ℝ → ℝ → ℂ := fun q x => cexp (Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))
  have hph_norm : ∀ q x : ℝ, ‖ph q x‖ = 1 := fun q x => by
    dsimp [ph]; rw [mul_comm Complex.I]; exact norm_cexp_real_mul_I _
  have hph_cont : ∀ q : ℝ, Continuous (ph q) := fun q =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).sub
        (continuous_const.mul continuous_id))))
  let J_osc : (ℝ → ℂ) → ℝ → ℂ := fun c q => ∫ x in Ici x₀, c x * ph q x
  have hc_72 : ∀ {M' : ℝ} {c : ℝ → ℂ}, 0 ≤ M' → SymBd 0 x₀ (7 / 2) M' c → ContDiff ℝ 2 (J_osc c) :=
    fun {M' c} hM' hc => by
      have hcc : ContinuousOn c (Ici x₀) := hc.cd.continuousOn
      have hint_k : ∀ (k : ℕ), k ≤ 2 → ∀ q : ℝ,
          IntegrableOn (fun x : ℝ => ((-Complex.I * (x : ℂ)) ^ k * c x) * ph q x) (Ici x₀) := fun k hk q => by
        refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M').mono'
          ((((continuous_const.mul Complex.continuous_ofReal).pow k).aestronglyMeasurable.mul
            (hcc.aestronglyMeasurable measurableSet_Ici)).mul (hph_cont q).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
        have hx1 : 1 ≤ x := by linarith [mem_Ici.mp hx]
        rw [norm_mul, hph_norm, mul_one, norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
        have hb0 := hc.bd0_le hx0_pos (mem_Ici.mp hx)
        calc x ^ k * ‖c x‖ ≤ x ^ k * (M' * x ^ (-(7 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hb0 (pow_nonneg hxpos.le k)
          _ = M' * (x ^ (k : ℝ) * x ^ (-(7 / 2 : ℝ))) := by rw [Real.rpow_natCast]; ring
          _ = M' * x ^ ((k : ℝ) - 7 / 2) := by rw [← Real.rpow_add hxpos, sub_eq_add_neg]
          _ ≤ M' * x ^ (-(3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hx1
                  (by have : (k : ℝ) ≤ 2 := (by exact_mod_cast hk); linarith)) hM'
      let K_fn : ℕ → ℝ → ℂ := fun k q => ∫ x in Ici x₀, ((-Complex.I * (x : ℂ)) ^ k * c x) * ph q x
      have hK_deriv : ∀ k : ℕ, k < 2 → ∀ q : ℝ, HasDerivAt (K_fn k) (K_fn (k + 1) q) q := fun k hk q => by
        refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ici x₀))
          (F := fun (q' : ℝ) (x : ℝ) => ((-Complex.I * (x : ℂ)) ^ k * c x) * ph q' x)
          (F' := fun (q' : ℝ) (x : ℝ) => ((-Complex.I * (x : ℂ)) ^ (k + 1) * c x) * ph q' x)
          (ball_mem_nhds q one_pos)
          (Eventually.of_forall fun (q' : ℝ) => (hint_k k (by omega) q').aestronglyMeasurable)
          (hint_k k (by omega) q) (hint_k (k + 1) (by omega) q).aestronglyMeasurable ?_
          ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M') ?_).2
        · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx q' _
          have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
          have hx1 : 1 ≤ x := by linarith [mem_Ici.mp hx]
          rw [norm_mul, hph_norm, mul_one, norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
          have hb0 := hc.bd0_le hx0_pos (mem_Ici.mp hx)
          calc x ^ (k + 1) * ‖c x‖ ≤ x ^ (k + 1) * (M' * x ^ (-(7 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left hb0 (pow_nonneg hxpos.le _)
            _ = M' * (x ^ ((k + 1 : ℕ) : ℝ) * x ^ (-(7 / 2 : ℝ))) := by rw [Real.rpow_natCast]; ring
            _ = M' * x ^ (((k + 1 : ℕ) : ℝ) - 7 / 2) := by rw [← Real.rpow_add hxpos, sub_eq_add_neg]
            _ ≤ M' * x ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_le hx1
                    (by have : ((k + 1 : ℕ) : ℝ) ≤ 2 := (by exact_mod_cast (by omega : k + 1 ≤ 2)); linarith)) hM'
        · filter_upwards [ae_restrict_mem measurableSet_Ici] with x _ q' _
          have hl : HasDerivAt (fun s : ℝ => Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - s * x : ℝ) : ℂ))
              (-Complex.I * (x : ℂ)) q' := by
            have h1 : HasDerivAt (fun s : ℝ => ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - s * x : ℝ) : ℂ)) (-(x : ℂ)) q' := by
              have hr : HasDerivAt (fun s : ℝ => σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - s * x) (-x) q' :=
                ((hasDerivAt_const q' (σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ))).sub ((hasDerivAt_id q').mul_const x)).congr_of_eventuallyEq
                  (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by ring)
              exact hr.ofReal_comp.congr_deriv (by push_cast; ring)
            exact (h1.const_mul Complex.I).congr_deriv (by ring)
          exact (hl.cexp.const_mul ((-Complex.I * (x : ℂ)) ^ k * c x)).congr_deriv (by rw [pow_succ]; ring)
      have hK_cd : ∀ d k : ℕ, d + k ≤ 2 → ContDiff ℝ (d : ℕ) (K_fn k) := fun d => by
        induction d with
        | zero =>
            intro k hk
            rw [Nat.cast_zero, contDiff_zero]
            refine continuous_of_dominated (fun q => (hint_k k (by omega) q).aestronglyMeasurable) (fun q => ?_)
              ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(3 / 2 : ℝ) < -1)).const_mul M')
              (ae_of_all _ fun x => by
                have hcd : Continuous (fun q : ℝ => Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ)) :=
                  continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_id.mul continuous_const)))
                exact continuous_const.mul (Complex.continuous_exp.comp hcd))
            filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
            have hxpos : 0 < x := by linarith [mem_Ici.mp hx]
            have hx1 : 1 ≤ x := by linarith [mem_Ici.mp hx]
            rw [norm_mul, hph_norm, mul_one, norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
            have hb0 := hc.bd0_le hx0_pos (mem_Ici.mp hx)
            calc x ^ k * ‖c x‖ ≤ x ^ k * (M' * x ^ (-(7 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hb0 (pow_nonneg hxpos.le _)
              _ = M' * (x ^ (k : ℝ) * x ^ (-(7 / 2 : ℝ))) := by rw [Real.rpow_natCast]; ring
              _ = M' * x ^ ((k : ℝ) - 7 / 2) := by rw [← Real.rpow_add hxpos, sub_eq_add_neg]
              _ ≤ M' * x ^ (-(3 / 2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left
                    (Real.rpow_le_rpow_of_exponent_le hx1
                      (by have : (k : ℝ) ≤ 2 := (by exact_mod_cast (by omega : k ≤ 2)); linarith)) hM'
        | succ d ih =>
            intro k hk
            rw [show ((d + 1 : ℕ) : WithTop ℕ∞) = (d : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_deriv]
            refine ⟨fun q => (hK_deriv k (by omega) q).differentiableAt, fun h => by simp at h, ?_⟩
            rw [show deriv (K_fn k) = K_fn (k + 1) from funext fun q => (hK_deriv k (by omega) q).deriv]
            exact ih (k + 1) (by omega)
      have h0 : J_osc c = K_fn 0 := by ext q; simp [J_osc, K_fn]
      rw [h0]; exact hK_cd 2 0 (by norm_num)
  -- Helper IBP step shifting left endpoint `x₁ → x₁ + 1` via `SymBd.deriv_gt`
  let c0 : ℂ := (2 * (σ : ℂ) * Complex.I)⁻¹
  let ψ : (ℝ → ℂ) → ℝ → ℂ := fun c x => (c0 * c x) * ((x : ℂ) ^ (-(1 / 2 : ℂ)))
  have hibp_step : ∀ {N : ℕ} {x₁ β M' : ℝ} {c : ℝ → ℂ},
      0 < x₁ → x₁ + 1 ≤ x₀ → N ≤ 2 → 3 / 2 ≤ β → 0 ≤ M' → SymBd (N + 1) x₁ β M' c →
      ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ SymBd (N + 1) x₁ (β + 1 / 2) M₁ (ψ c) ∧
        SymBd N (x₁ + 1) (β + 3 / 2) M₂ (deriv (ψ c)) ∧
        (∀ q : ℝ, J_osc c q = -ψ c x₀ * ph q x₀ - J_osc (deriv (ψ c)) q + (Complex.I * (q : ℂ)) * J_osc (ψ c) q) := by
    intro N x₁ β M' c hx1_pos hx1_le hN hβ hM' hc
    obtain ⟨K_h, hKh, hinv_s⟩ := symBd_inv_sqrt (N := 3) hx1_pos
    have hψ_bd : SymBd (N + 1) x₁ (β + 1 / 2) (2 ^ (N + 1) * (‖c0‖ * M') * K_h) (ψ c) :=
      (SymBd.const_mul c0 hc).mul hx1_pos (hinv_s.of_le_N (by omega))
    have hdψ_bd : SymBd N (x₁ + 1) (β + 3 / 2) (2 ^ (N + 1) * (‖c0‖ * M') * K_h) (deriv (ψ c)) := by
      rw [show β + 3 / 2 = (β + 1 / 2) + 1 by ring]
      exact hψ_bd.deriv_gt (by linarith : x₁ < x₁ + 1)
    have hM1 : 0 ≤ 2 ^ (N + 1) * (‖c0‖ * M') * K_h := by positivity
    refine ⟨_, _, hM1, hM1, hψ_bd, hdψ_bd, fun q => ?_⟩
    have hc_x0 := hc.mono_left (by linarith : x₁ ≤ x₀)
    have hψ_x0 := hψ_bd.mono_left (by linarith : x₁ ≤ x₀)
    have hdψ_x0 := hdψ_bd.mono_left hx1_le
    have hc_c : ContinuousOn c (Ici x₀) := hc_x0.cd.continuousOn
    have hψ_c : ContinuousOn (ψ c) (Ici x₀) := hψ_x0.cd.continuousOn
    have hdψ_c : ContinuousOn (deriv (ψ c)) (Ici x₀) := hdψ_x0.cd.continuousOn
    have hint_c : IntegrableOn (fun x : ℝ => c x * ph q x) (Ioi x₀) := by
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by linarith : -β < -1)).const_mul M').mono'
        ((hc_c.aestronglyMeasurable measurableSet_Ici).mul (hph_cont q).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [norm_mul, hph_norm, mul_one]
      exact hc_x0.bd0_le hx0_pos (mem_Ici.mp hx)
    have hint_ψ : IntegrableOn (fun x : ℝ => ψ c x * ph q x) (Ioi x₀) := by
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by linarith : -(β + 1 / 2) < -1)).const_mul
        (2 ^ (N + 1) * (‖c0‖ * M') * K_h)).mono'
        ((hψ_c.aestronglyMeasurable measurableSet_Ici).mul (hph_cont q).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [norm_mul, hph_norm, mul_one]
      exact hψ_x0.bd0_le hx0_pos (mem_Ici.mp hx)
    have hint_dψ : IntegrableOn (fun x : ℝ => deriv (ψ c) x * ph q x) (Ioi x₀) := by
      rw [← integrableOn_Ici_iff_integrableOn_Ioi]
      refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by linarith : -(β + 3 / 2) < -1)).const_mul
        (2 ^ (N + 1) * (‖c0‖ * M') * K_h)).mono'
        ((hdψ_c.aestronglyMeasurable measurableSet_Ici).mul (hph_cont q).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      rw [norm_mul, hph_norm, mul_one]
      exact hdψ_x0.bd0_le hx0_pos (mem_Ici.mp hx)
    have hint_x : ∀ R : ℝ, x₀ ≤ R →
        ∫ x in x₀..R, c x * ph q x =
          ψ c R * ph q R - ψ c x₀ * ph q x₀ - (∫ x in x₀..R, deriv (ψ c) x * ph q x) +
            (Complex.I * (q : ℂ)) * ∫ x in x₀..R, ψ c x * ph q x := fun R hR => by
      have hftc : ∫ x in x₀..R, (deriv (ψ c) x + (2 * (σ : ℂ) * Complex.I * ((x : ℂ) ^ (1 / 2 : ℂ)) - Complex.I * (q : ℂ)) * ψ c x) * ph q x =
          ψ c R * ph q R - ψ c x₀ * ph q x₀ := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => ψ c s * ph q s) (fun t ht => ?_) ?_
        · have ht_pos : 0 < t := by rw [uIcc_of_le hR] at ht; linarith [ht.1]
          have ht_gt : x₁ < t := by rw [uIcc_of_le hR] at ht; linarith [ht.1]
          have hd_ψ : HasDerivAt (ψ c) (deriv (ψ c) t) t :=
            ((hψ_bd.cd.mono (Ioi_subset_Ici_self : Ioi x₁ ⊆ Ici x₁)).differentiableOn
              (by exact_mod_cast Nat.succ_ne_zero (N + 1))).differentiableAt (isOpen_Ioi.mem_nhds ht_gt) |>.hasDerivAt
          have hd_ph : HasDerivAt (fun s : ℝ => ph q s)
              ((2 * (σ : ℂ) * Complex.I * ((t : ℂ) ^ (1 / 2 : ℂ)) - Complex.I * (q : ℂ)) * ph q t) t := by
            have hr1 : HasDerivAt (fun s : ℝ => σ * (4 / 3 : ℝ) * s ^ (3 / 2 : ℝ) - q * s)
                (2 * σ * t ^ (1 / 2 : ℝ) - q) t := by
              have hp := ((hasDerivAt_id t).rpow_const (p := (3 / 2 : ℝ)) (Or.inl ht_pos.ne')).const_mul (σ * (4 / 3 : ℝ))
              have hl := (hasDerivAt_id t).const_mul q
              exact (hp.sub hl).congr_deriv (by norm_num; ring)
            have hc1 : HasDerivAt (fun s : ℝ => ((σ * (4 / 3 : ℝ) * s ^ (3 / 2 : ℝ) - q * s : ℝ) : ℂ))
                (((2 * σ * t ^ (1 / 2 : ℝ) - q : ℝ) : ℂ)) t :=
              hr1.ofReal_comp
            have ht12 : ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
              rw [Complex.ofReal_cpow ht_pos.le]; norm_num
            exact ((hc1.const_mul Complex.I).cexp).congr_deriv (by
              dsimp [ph]; rw [← ht12]; push_cast; ring)
          exact (hd_ψ.mul hd_ph).congr_deriv (by ring)
        · have hicc : uIcc x₀ R ⊆ Ici x₀ := by rw [uIcc_of_le hR]; exact fun _ h => h.1
          have hcp : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) (uIcc x₀ R) := fun t ht =>
            (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (by rw [uIcc_of_le hR] at ht; linarith [ht.1]))).continuousWithinAt
          exact (((hdψ_c.mono hicc).add ((continuousOn_const.mul hcp |>.sub continuousOn_const).mul (hψ_c.mono hicc))).mul
            (hph_cont q).continuousOn) |>.intervalIntegrable
      have heq_f : ∀ x ∈ uIcc x₀ R,
          (deriv (ψ c) x + (2 * (σ : ℂ) * Complex.I * ((x : ℂ) ^ (1 / 2 : ℂ)) - Complex.I * (q : ℂ)) * ψ c x) * ph q x =
            c x * ph q x + (deriv (ψ c) x * ph q x - (Complex.I * (q : ℂ)) * (ψ c x * ph q x)) := fun x hx => by
        have hxpos : 0 < x := by rw [uIcc_of_le hR] at hx; linarith [hx.1]
        have hpow_mul : (x : ℂ) ^ (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
          rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hxpos.ne'), add_neg_cancel, Complex.cpow_zero]
        have h2s : (2 * (σ : ℂ) * Complex.I) * c0 = 1 := by
          dsimp [c0]; exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hσ_ne)) Complex.I_ne_zero)
        have hterm : (2 * (σ : ℂ) * Complex.I * (x : ℂ) ^ (1 / 2 : ℂ)) * ψ c x = c x := by
          dsimp [ψ]
          calc (2 * (σ : ℂ) * Complex.I * (x : ℂ) ^ (1 / 2 : ℂ)) * (c0 * c x * (x : ℂ) ^ (-(1 / 2 : ℂ)))
              = ((2 * (σ : ℂ) * Complex.I) * c0) * ((x : ℂ) ^ (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ))) * c x := by ring
            _ = 1 * 1 * c x := by rw [h2s, hpow_mul]
            _ = c x := by ring
        linear_combination ph q x * hterm
      have hicc : uIcc x₀ R ⊆ Ici x₀ := by rw [uIcc_of_le hR]; exact fun _ h => h.1
      have hi1 : IntervalIntegrable (fun x => c x * ph q x) volume x₀ R := ((hc_c.mono hicc).mul (hph_cont q).continuousOn).intervalIntegrable
      have hi2 : IntervalIntegrable (fun x => deriv (ψ c) x * ph q x) volume x₀ R := ((hdψ_c.mono hicc).mul (hph_cont q).continuousOn).intervalIntegrable
      have hi3 : IntervalIntegrable (fun x => ψ c x * ph q x) volume x₀ R := ((hψ_c.mono hicc).mul (hph_cont q).continuousOn).intervalIntegrable
      rw [intervalIntegral.integral_congr heq_f, intervalIntegral.integral_add hi1 (hi2.sub (hi3.const_mul _)),
        intervalIntegral.integral_sub hi2 (hi3.const_mul _), intervalIntegral.integral_const_mul] at hftc
      rw [eq_sub_of_add_eq hftc]; ring
    have ht1 := intervalIntegral_tendsto_integral_Ioi x₀ hint_c tendsto_id
    have ht2 := intervalIntegral_tendsto_integral_Ioi x₀ hint_dψ tendsto_id
    have ht3 := intervalIntegral_tendsto_integral_Ioi x₀ hint_ψ tendsto_id
    have htb : Tendsto (fun R : ℝ => ψ c R * ph q R) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h0 : Tendsto (fun R : ℝ => (2 ^ (N + 1) * (‖c0‖ * M') * K_h) * R ^ (-(β + 1 / 2))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < β + 1 / 2)).const_mul _
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 (Eventually.of_forall fun _ => norm_nonneg _) ?_
      filter_upwards [eventually_ge_atTop x₀] with R hR
      rw [norm_mul, hph_norm, mul_one]
      exact hψ_bd.bd0_le hx1_pos (by linarith)
    have htr := (((htb.sub (tendsto_const_nhds (x := ψ c x₀ * ph q x₀))).sub ht2).add (ht3.const_mul (Complex.I * (q : ℂ))))
    simpa [J_osc, integral_Ici_eq_integral_Ioi] using
      tendsto_nhds_unique ht1 (htr.congr' (by filter_upwards [eventually_ge_atTop x₀] with R hR using (hint_x R hR).symm))
  -- 3 IBP steps: `2 -> 5/2 -> 3 -> 7/2`, shifting `x₀ - 3 → x₀ - 2 → x₀ - 1 → x₀`
  obtain ⟨M1, M1', hM1, hM1', sψ1, sdψ1, h1⟩ :=
    hibp_step (N := 2) (x₁ := x₀ - 3) (by linarith) (by linarith) (by norm_num) (by norm_num) hM hb
  rw [show (2 + 1 / 2 : ℝ) = 5 / 2 by norm_num] at sψ1
  rw [show (2 + 3 / 2 : ℝ) = 7 / 2 by norm_num] at sdψ1
  have sψ1_next : SymBd 2 (x₀ - 2) (5 / 2) M1 (ψ b) :=
    (sψ1.of_le_N (by norm_num : 2 ≤ 3)).mono_left (by linarith : x₀ - 3 ≤ x₀ - 2)
  obtain ⟨M2, M2', hM2, hM2', sψ2, sdψ2, h2⟩ :=
    hibp_step (N := 1) (x₁ := x₀ - 2) (by linarith) (by linarith) (by norm_num) (by norm_num) hM1 sψ1_next
  rw [show (5 / 2 + 1 / 2 : ℝ) = 3 by norm_num] at sψ2
  have sψ2_next : SymBd 1 (x₀ - 1) 3 M2 (ψ (ψ b)) :=
    (sψ2.of_le_N (by norm_num : 1 ≤ 2)).mono_left (by linarith : x₀ - 2 ≤ x₀ - 1)
  obtain ⟨M3, M3', hM3, hM3', sψ3, sdψ3, h3⟩ :=
    hibp_step (N := 0) (x₁ := x₀ - 1) (by linarith) (by linarith) (by norm_num) (by norm_num) hM2 sψ2_next
  rw [show (3 + 1 / 2 : ℝ) = 7 / 2 by norm_num] at sψ3
  have hcd_d1 : ContDiff ℝ 2 (J_osc (deriv (ψ b))) :=
    hc_72 hM1' ((sdψ1.of_le_N (by norm_num : 0 ≤ 2)).mono_left (by linarith : x₀ - 3 + 1 ≤ x₀))
  have hcd_d2 : ContDiff ℝ 2 (J_osc (deriv (ψ (ψ b)))) :=
    hc_72 hM2' ((sdψ2.of_le_N (by norm_num : 0 ≤ 1)).mono_left (by linarith : x₀ - 2 + 1 ≤ x₀) |>.mono_order hx0_1 (by norm_num))
  have hcd_d3 : ContDiff ℝ 2 (J_osc (deriv (ψ (ψ (ψ b))))) :=
    hc_72 hM3' ((sdψ3.mono_left (by linarith : x₀ - 1 + 1 ≤ x₀)).mono_order hx0_1 (by norm_num))
  have hcd_ψ3 : ContDiff ℝ 2 (J_osc (ψ (ψ (ψ b)))) :=
    hc_72 hM3 ((sψ3.of_le_N (by norm_num : 0 ≤ 1)).mono_left (by linarith : x₀ - 1 ≤ x₀))
  have hcd_ph0 : ∀ (a : ℂ), ContDiff ℝ 2 (fun q : ℝ => a * ph q x₀) := fun a =>
    contDiff_ofReal_cexp_aff 2 a (σ * (4 / 3 : ℝ) * x₀ ^ (3 / 2 : ℝ)) x₀
  have hcd_Iq : ContDiff ℝ 2 (fun q : ℝ => Complex.I * (q : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hJ_ψ2 : ContDiff ℝ 2 (J_osc (ψ (ψ b))) := by
    have heq : J_osc (ψ (ψ b)) = fun q => -ψ (ψ (ψ b)) x₀ * ph q x₀ - J_osc (deriv (ψ (ψ (ψ b)))) q +
        (Complex.I * (q : ℂ)) * J_osc (ψ (ψ (ψ b))) q := funext h3
    rw [heq]
    exact (((hcd_ph0 _).sub hcd_d3).add (hcd_Iq.mul hcd_ψ3))
  have hJ_ψ1 : ContDiff ℝ 2 (J_osc (ψ b)) := by
    have heq : J_osc (ψ b) = fun q => -ψ (ψ b) x₀ * ph q x₀ - J_osc (deriv (ψ (ψ b))) q +
        (Complex.I * (q : ℂ)) * J_osc (ψ (ψ b)) q := funext h2
    rw [heq]
    exact (((hcd_ph0 _).sub hcd_d2).add (hcd_Iq.mul hJ_ψ2))
  have hJ_b : J_osc b = fun q => -ψ b x₀ * ph q x₀ - J_osc (deriv (ψ b)) q +
      (Complex.I * (q : ℂ)) * J_osc (ψ b) q := funext h1
  change ContDiff ℝ 2 (J_osc b)
  rw [hJ_b]
  exact (((hcd_ph0 _).sub hcd_d1).add (hcd_Iq.mul hJ_ψ1))

/-! ### Section 4: `SmoothSymbol` for `HasGenRationalAiryCoeffs F 0 0` (`γ₀ = 0`) -/

/-- For `F` with `HasGenRationalAiryCoeffs F 0 0`, the unsubtracted symbol `G(v) = X̃(i c_s v)`
already satisfies `SmoothSymbol G CG` (so `γ₀ = 0` in `hb_inner`). -/
theorem smoothSymbol_of_genRational_zero {F : ℂ → ℂ} (hF : HasGenRationalAiryCoeffs F 0 0) :
    ∃ CG : ℝ, 0 ≤ CG ∧
      SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) (yv v)) CG := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨CT, hCT, htail⟩ := symbolTail_of_genRational hF
  obtain ⟨x₀, C_h, hx12, hCh, r00, r01, r11, sr00, sr01, sr11, _, _, _, hsplit⟩ :=
    genRational_zero_lapC_split hF
  have hx0_pos : 0 < x₀ := by linarith
  have hx0_1 : 1 ≤ x₀ := by linarith
  have hx0_2 : 2 ≤ x₀ := by linarith
  have hIn := hF.1
  have hX_cont : Continuous X := (contDiff_re_of_differentiable hIn.1).1.continuous
  have hU2 : HasU2 X := hasU2_of_genRational hF
  -- Step A: `I_right (yv v)` is `ContDiff ℝ 2`
  let I_r : ℝ → ℂ := fun v => ∫ u in Ici (-x₀), (X u : ℂ) * cexp (yv v * (u : ℂ))
  have hint_Ir : ∀ (k : ℕ), k ≤ 2 → ∀ v : ℝ,
      IntegrableOn (fun u : ℝ => ((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ k * (X u : ℂ) * cexp (yv v * (u : ℂ))) (Ici (-x₀)) :=
    fun k hk v => by
      have hmaj := integrableOn_rpow_exp_right hX_cont hU2 (-x₀) 0 le_rfl (k := k) hk
      refine (hmaj.const_mul (ceCs ^ k)).mono'
        (((by fun_prop : AEStronglyMeasurable (fun u : ℝ => ((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ k) _).mul
          ((Complex.continuous_ofReal.comp hX_cont).aestronglyMeasurable)).mul (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u _
      rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, show yv v * (u : ℂ) = ((ceCs * v * u : ℝ) : ℂ) * Complex.I by unfold yv; push_cast; ring,
        norm_cexp_real_mul_I, mul_one, zero_mul, Real.exp_zero, mul_one]
      rw [mul_pow]; ring_nf; exact le_rfl
  let Ir_k : ℕ → ℝ → ℂ := fun k v =>
    ∫ u in Ici (-x₀), (((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ k * (X u : ℂ)) * cexp (yv v * (u : ℂ))
  have hIr_deriv : ∀ k : ℕ, k < 2 → ∀ v : ℝ, HasDerivAt (Ir_k k) (Ir_k (k + 1) v) v := fun k hk v => by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ici (-x₀)))
      (F := fun v' u => (((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ k * (X u : ℂ)) * cexp (yv v' * (u : ℂ)))
      (F' := fun v' u => (((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ (k + 1) * (X u : ℂ)) * cexp (yv v' * (u : ℂ)))
      (ball_mem_nhds v one_pos)
      (Eventually.of_forall fun v' => (hint_Ir k (by omega) v').congr (ae_of_all _ fun u => by ring) |>.aestronglyMeasurable)
      ((hint_Ir k (by omega) v).congr (ae_of_all _ fun u => by ring))
      ((hint_Ir (k + 1) (by omega) v).congr (ae_of_all _ fun u => by ring)).aestronglyMeasurable ?_
      ((integrableOn_rpow_exp_right hX_cont hU2 (-x₀) 0 le_rfl (k := k + 1) (by omega)).const_mul (ceCs ^ (k + 1))) ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u _ v' _
      rw [norm_mul, show yv v' * (u : ℂ) = ((ceCs * v' * u : ℝ) : ℂ) * Complex.I by unfold yv; push_cast; ring,
        norm_cexp_real_mul_I, mul_one, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ceCs_pos, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        zero_mul, Real.exp_zero, mul_one, mul_pow]
      ring_nf; exact le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u _ v' _
      have hl := ((hasDerivAt_yv v').mul_const (u : ℂ)).cexp.const_mul (((ceCs : ℂ) * Complex.I * (u : ℂ)) ^ k * (X u : ℂ))
      exact hl.congr_deriv (by rw [pow_succ]; ring)
  have hIr_cd : ∀ d k : ℕ, d + k ≤ 2 → ContDiff ℝ (d : ℕ) (Ir_k k) := fun d => by
    induction d with
    | zero =>
        intro k hk; rw [Nat.cast_zero, contDiff_zero]
        refine continuous_of_dominated
          (fun v => ((hint_Ir k (by omega) v).congr (ae_of_all _ fun u => by ring)).aestronglyMeasurable)
          (fun v => ?_)
          ((integrableOn_rpow_exp_right hX_cont hU2 (-x₀) 0 le_rfl (k := k) (by omega)).const_mul (ceCs ^ k))
          (ae_of_all _ fun u => by unfold yv; fun_prop)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with u _
        rw [norm_mul, show yv v * (u : ℂ) = ((ceCs * v * u : ℝ) : ℂ) * Complex.I by unfold yv; push_cast; ring,
          norm_cexp_real_mul_I, mul_one, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ceCs_pos, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          zero_mul, Real.exp_zero, mul_one, mul_pow]
        ring_nf; exact le_rfl
    | succ d ih =>
        intro k hk
        rw [show ((d + 1 : ℕ) : WithTop ℕ∞) = (d : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_deriv]
        refine ⟨fun v => (hIr_deriv k (by omega) v).differentiableAt, fun h => by simp at h, ?_⟩
        rw [show deriv (Ir_k k) = Ir_k (k + 1) from funext fun v => (hIr_deriv k (by omega) v).deriv]
        exact ih (k + 1) (by omega)
  have hcd_Ir : ContDiff ℝ 2 I_r := by
    rw [show I_r = Ir_k 0 from by ext v; simp [I_r, Ir_k]]
    exact hIr_cd 2 0 (by norm_num)
  -- Step B: Decompose `h₀` and `h₁` into `b₀, bPos, bNeg` on `w₀ = x₀ - 3` (`SymBd 3 w₀ 2` / `SymBd 1 w₀ (5/2)`)
  have hw0_pos : 0 < x₀ - 3 := by linarith
  have hw0_1 : 1 ≤ x₀ - 3 := by linarith
  have hw0_2 : 2 ≤ x₀ - 4 := by linarith
  have hx0_4 : 4 ≤ x₀ := by linarith
  obtain ⟨MA, _, hAP⟩ := symBd_negAmpP hw0_2
  obtain ⟨MB, _, hAM⟩ := symBd_negAmpM hw0_2
  obtain ⟨MA', _, hAP'⟩ := symBd_negAmpP' hw0_2
  obtain ⟨MB', _, hAM'⟩ := symBd_negAmpM' hw0_2
  let aP : ℝ → ℂ := fun x => negAmpP (x : ℂ)
  let aM : ℝ → ℂ := fun x => negAmpM (x : ℂ)
  let aP' : ℝ → ℂ := fun x => negAmpP' (x : ℂ)
  let aM' : ℝ → ℂ := fun x => negAmpM' (x : ℂ)
  have sr01d : SymBd 11 (x₀ - 3) 3 C_h (deriv r01) := by
    simpa [show (2 : ℝ) + 1 = 3 by norm_num] using sr01.deriv_gt (by linarith : x₀ - 4 < x₀ - 3)
  have s00_3 := (sr00.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have s01_3 := (sr01.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have s11_3 := (sr11.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have s01d_3 := sr01d.of_le_N (by norm_num : 3 ≤ 11)
  have sAP := (hAP.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have sAM := (hAM.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have sAP' := (hAP'.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have sAM' := (hAM'.of_le_N (by norm_num : 3 ≤ 12)).mono_left (by linarith : x₀ - 4 ≤ x₀ - 3)
  have mk_split : ∀ {r : ℝ → ℂ} {βr Mr : ℝ} (hβ : 2 ≤ βr) (hs : SymBd 3 (x₀ - 3) βr Mr r),
      0 ≤ Mr →
      ∃ b0 bP bN : ℝ → ℂ, ∃ M0 MP MN : ℝ, 0 ≤ M0 ∧ 0 ≤ MP ∧ 0 ≤ MN ∧
        SymBd 1 (x₀ - 3) (5 / 2) M0 b0 ∧ SymBd 3 (x₀ - 3) 2 MP bP ∧ SymBd 3 (x₀ - 3) 2 MN bN ∧
        (∀ x : ℝ, 0 ≤ x → r x * (airyAi (-x) : ℂ) ^ 2 =
          b0 x + bP x * cexp (Complex.I * (((4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) +
          bN x * cexp (Complex.I * (((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
    intro r βr Mr hβ hs hMr
    have sb0 := (SymBd.const_mul (2 : ℂ) (hs.mul hw0_pos (sAP.mul hw0_pos sAM))).mono_order hw0_1 (by linarith : (5 / 2 : ℝ) ≤ βr + (1 / 4 + 1 / 4))
    have sbP := (hs.mul hw0_pos (sAM.mul hw0_pos sAM)).mono_order hw0_1 (by linarith : (2 : ℝ) ≤ βr + (1 / 4 + 1 / 4))
    have sbN := (hs.mul hw0_pos (sAP.mul hw0_pos sAP)).mono_order hw0_1 (by linarith : (2 : ℝ) ≤ βr + (1 / 4 + 1 / 4))
    refine ⟨_, _, _, _, _, _, SymBd.nonneg' hw0_pos sb0, SymBd.nonneg' hw0_pos sbP, SymBd.nonneg' hw0_pos sbN,
      sb0.of_le_N (by norm_num), sbP, sbN, fun x hx => ?_⟩
    rw [ai_real_split hx]
    have hE := exp_mul_exp_neg (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))
    have hEp : cexp (Complex.I * (((4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hEn : cexp (Complex.I * (((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1
      rw [← neg_add, ← mul_add, ← mul_neg, ← Complex.ofReal_add, ← Complex.ofReal_neg]
      congr 1; ring
    rw [hEp, hEn]
    linear_combination (2 * r x * negAmpP (x : ℂ) * negAmpM (x : ℂ)) * hE
  -- Same for `r11 * Ai'^2`!
  have mk_split' : ∃ b0 bP bN : ℝ → ℂ, ∃ M0 MP MN : ℝ, 0 ≤ M0 ∧ 0 ≤ MP ∧ 0 ≤ MN ∧
      SymBd 1 (x₀ - 3) (5 / 2) M0 b0 ∧ SymBd 3 (x₀ - 3) 2 MP bP ∧ SymBd 3 (x₀ - 3) 2 MN bN ∧
      (∀ x : ℝ, 0 ≤ x → r11 x * (airyAi' (-x) : ℂ) ^ 2 =
        b0 x + bP x * cexp (Complex.I * (((4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) +
        bN x * cexp (Complex.I * (((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
    have sb0 := (SymBd.const_mul (2 : ℂ) (s11_3.mul hw0_pos (sAP'.mul hw0_pos sAM'))).mono_order hw0_1 (by norm_num : (5 / 2 : ℝ) ≤ 3 + (-(1 / 4) + -(1 / 4)))
    have sbP := (s11_3.mul hw0_pos (sAM'.mul hw0_pos sAM')).mono_order hw0_1 (by norm_num : (2 : ℝ) ≤ 3 + (-(1 / 4) + -(1 / 4)))
    have sbN := (s11_3.mul hw0_pos (sAP'.mul hw0_pos sAP')).mono_order hw0_1 (by norm_num : (2 : ℝ) ≤ 3 + (-(1 / 4) + -(1 / 4)))
    refine ⟨_, _, _, _, _, _, SymBd.nonneg' hw0_pos sb0, SymBd.nonneg' hw0_pos sbP, SymBd.nonneg' hw0_pos sbN,
      sb0.of_le_N (by norm_num), sbP, sbN, fun x hx => ?_⟩
    rw [aip_real_split hx]
    have hE := exp_mul_exp_neg (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))
    have hEp : cexp (Complex.I * (((4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) * cexp (Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hEn : cexp (Complex.I * (((-1 : ℝ) * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) * cexp (-(Complex.I * (((2 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)))) := by
      rw [← Complex.exp_add]; congr 1
      rw [← neg_add, ← mul_add, ← mul_neg, ← Complex.ofReal_add, ← Complex.ofReal_neg]
      congr 1; ring
    rw [hEp, hEn]
    linear_combination (2 * r11 x * negAmpP' (x : ℂ) * negAmpM' (x : ℂ)) * hE
  obtain ⟨b0a, bPa, bNa, M0a, MPa, MNa, h0a, hPa, hNa, sb0a, sbPa, sbNa, hsplit_a⟩ := mk_split le_rfl s00_3 hCh
  obtain ⟨b0b, bPb, bNb, M0b, MPb, MNb, h0b, hPb, hNb, sb0b, sbPb, sbNb, hsplit_b⟩ := mk_split (by norm_num) s01d_3 hCh
  obtain ⟨b0c, bPc, bNc, M0c, MPc, MNc, h0c, hPc, hNc, sb0c, sbPc, sbNc, hsplit_c⟩ := mk_split'
  obtain ⟨b01, bP1, bN1, M01, MP1, MN1, h01, hP1, hN1, sb01, sbP1, sbN1, hsplit_1⟩ := mk_split le_rfl s01_3 hCh
  let h₀_st := fun x => b0a x + (b0c x + (1 / 2 : ℂ) * b0b x)
  let h₀_P := fun x => bPa x + (bPc x + (1 / 2 : ℂ) * bPb x)
  let h₀_N := fun x => bNa x + (bNc x + (1 / 2 : ℂ) * bNb x)
  have sb_h0_st : SymBd 1 (x₀ - 3) (5 / 2) _ h₀_st := sb0a.add hw0_pos (sb0c.add hw0_pos (SymBd.const_mul (1 / 2 : ℂ) sb0b))
  have sb_h0_P : SymBd 3 (x₀ - 3) 2 _ h₀_P := sbPa.add hw0_pos (sbPc.add hw0_pos (SymBd.const_mul (1 / 2 : ℂ) sbPb))
  have sb_h0_N : SymBd 3 (x₀ - 3) 2 _ h₀_N := sbNa.add hw0_pos (sbNc.add hw0_pos (SymBd.const_mul (1 / 2 : ℂ) sbNb))
  -- Combine Fourier integrals of `h₀` and `h₁` at `yv v` (`q = ceCs * v`)
  let F_st : (ℝ → ℂ) → ℝ → ℂ := fun b q => ∫ x in Ici x₀, b x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))
  let F_P : (ℝ → ℂ) → ℝ → ℂ := fun b q => ∫ x in Ici x₀, b x * cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))
  let F_N : (ℝ → ℂ) → ℝ → ℂ := fun b q => ∫ x in Ici x₀, b x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))
  have int_st : ∀ {M' : ℝ} {b : ℝ → ℂ}, 0 ≤ M' → SymBd 1 x₀ (5 / 2) M' b → ∀ q : ℝ,
      IntegrableOn (fun x => b x * cexp (-(Complex.I * (q : ℂ) * (x : ℂ)))) (Ici x₀) := fun {M' b} _ hb q => by
    refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : -(5 / 2 : ℝ) < -1)).const_mul M').mono'
      ((hb.cd.continuousOn.aestronglyMeasurable measurableSet_Ici).mul (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul, norm_cexp_neg_I_mul, mul_one]
    exact hb.bd0_le hx0_pos (mem_Ici.mp hx)
  have int_osc : ∀ {σ : ℝ} {M' : ℝ} {b : ℝ → ℂ}, 0 ≤ M' → SymBd 3 (x₀ - 3) 2 M' b → ∀ q : ℝ,
      IntegrableOn (fun x => b x * cexp (Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))) (Ici x₀) := fun {σ M' b} _ hb q => by
    have hph_c : Continuous (fun x : ℝ => cexp (Complex.I * ((σ * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - q * x : ℝ) : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).sub
          (continuous_const.mul continuous_id))))
    have hb_x0 := hb.mono_left (by linarith : x₀ - 3 ≤ x₀)
    refine ((integrableOn_Ici_rpow_of_lt hx0_pos (by norm_num : (-2 : ℝ) < -1)).const_mul M').mono'
      ((hb_x0.cd.continuousOn.aestronglyMeasurable measurableSet_Ici).mul hph_c.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [norm_mul, mul_comm Complex.I, norm_cexp_real_mul_I, mul_one]
    exact hb_x0.bd0_le hx0_pos (mem_Ici.mp hx)
  have sb_h0_st_x0 := sb_h0_st.mono_left (by linarith : x₀ - 3 ≤ x₀)
  have sb01_x0 := sb01.mono_left (by linarith : x₀ - 3 ≤ x₀)
  obtain ⟨hF0_cd1, Cst0, hCst0, hF0_d2⟩ := fourier_sym_stationary hx0_1 (SymBd.nonneg' hx0_pos sb_h0_st_x0) sb_h0_st_x0
  obtain ⟨hF1_cd1, Cst1, hCst1, hF1_d2⟩ := fourier_sym_stationary hx0_1 h01 sb01_x0
  have hFP0_cd2 := fourier_sym_osc hx0_4 (SymBd.nonneg' hw0_pos sb_h0_P) (Or.inl rfl) sb_h0_P
  have hFN0_cd2 := fourier_sym_osc hx0_4 (SymBd.nonneg' hw0_pos sb_h0_N) (Or.inr rfl) sb_h0_N
  have hFP1_cd2 := fourier_sym_osc hx0_4 hP1 (Or.inl rfl) sbP1
  have hFN1_cd2 := fourier_sym_osc hx0_4 hN1 (Or.inr rfl) sbN1
  let Jh0_v : ℝ → ℂ := fun v => F_st h₀_st (ceCs * v) + F_P h₀_P (ceCs * v) + F_N h₀_N (ceCs * v)
  let Jh1_v : ℝ → ℂ := fun v => F_st b01 (ceCs * v) + F_P bP1 (ceCs * v) + F_N bN1 (ceCs * v)
  have hJh0_eq : ∀ v : ℝ,
      ∫ x in Ici x₀, (r00 x * (airyAi (-x) : ℂ) ^ 2 + r11 x * (airyAi' (-x) : ℂ) ^ 2 +
        (1 / 2 : ℂ) * (deriv r01 x * (airyAi (-x) : ℂ) ^ 2)) * cexp (-yv v * (x : ℂ)) = Jh0_v v := fun v => by
    have hpt : Set.EqOn
        (fun x => (r00 x * (airyAi (-x) : ℂ) ^ 2 + r11 x * (airyAi' (-x) : ℂ) ^ 2 +
          (1 / 2 : ℂ) * (deriv r01 x * (airyAi (-x) : ℂ) ^ 2)) * cexp (-yv v * (x : ℂ)))
        (fun x => h₀_st x * cexp (-(Complex.I * ((ceCs * v : ℝ) : ℂ) * (x : ℂ))) +
          (h₀_P x * cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) +
           h₀_N x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ))))
        (Ici x₀) := fun x hx => by
      dsimp only
      have hx0' : 0 ≤ x := by linarith [mem_Ici.mp hx]
      rw [hsplit_a x hx0', hsplit_b x hx0', hsplit_c x hx0']
      have hexp_yv : cexp (-yv v * (x : ℂ)) = cexp (-(Complex.I * ((ceCs * v : ℝ) : ℂ) * (x : ℂ))) := by
        unfold yv; congr 1; push_cast; ring
      have hexp_P : cexp (Complex.I * ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)) =
          cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; unfold yv; congr 1; push_cast; ring
      have hexp_N : cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)) =
          cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; unfold yv; congr 1; push_cast; ring
      dsimp [h₀_st, h₀_P, h₀_N]
      calc _ = (h₀_st x + h₀_P x * cexp (Complex.I * ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) +
              h₀_N x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ))) * cexp (-yv v * (x : ℂ)) := by ring
        _ = h₀_st x * cexp (-yv v * (x : ℂ)) +
            (h₀_P x * (cexp (Complex.I * ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ))) +
             h₀_N x * (cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)))) := by ring
        _ = _ := by rw [hexp_P, hexp_N, hexp_yv]
    have hosc_int : IntegrableOn (fun x =>
        h₀_P x * cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) +
        h₀_N x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ))) (Ici x₀) :=
      (int_osc (SymBd.nonneg' hw0_pos sb_h0_P) sb_h0_P _).add (int_osc (SymBd.nonneg' hw0_pos sb_h0_N) sb_h0_N _)
    rw [setIntegral_congr_fun measurableSet_Ici hpt,
      integral_add (int_st (SymBd.nonneg' hx0_pos sb_h0_st_x0) sb_h0_st_x0 _) hosc_int,
      integral_add (int_osc (SymBd.nonneg' hw0_pos sb_h0_P) sb_h0_P _) (int_osc (SymBd.nonneg' hw0_pos sb_h0_N) sb_h0_N _)]
    dsimp [Jh0_v, F_st, F_P, F_N]; ring
  have hJh1_eq : ∀ v : ℝ,
      ∫ x in Ici x₀, (r01 x * (airyAi (-x) : ℂ) ^ 2) * cexp (-yv v * (x : ℂ)) = Jh1_v v := fun v => by
    have hpt : Set.EqOn
        (fun x => (r01 x * (airyAi (-x) : ℂ) ^ 2) * cexp (-yv v * (x : ℂ)))
        (fun x => b01 x * cexp (-(Complex.I * ((ceCs * v : ℝ) : ℂ) * (x : ℂ))) +
          (bP1 x * cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) +
           bN1 x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ))))
        (Ici x₀) := fun x hx => by
      dsimp only
      have hx0' : 0 ≤ x := by linarith [mem_Ici.mp hx]
      rw [hsplit_1 x hx0']
      have hexp_yv : cexp (-yv v * (x : ℂ)) = cexp (-(Complex.I * ((ceCs * v : ℝ) : ℂ) * (x : ℂ))) := by
        unfold yv; congr 1; push_cast; ring
      have hexp_P : cexp (Complex.I * ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)) =
          cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; unfold yv; congr 1; push_cast; ring
      have hexp_N : cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)) =
          cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; unfold yv; congr 1; push_cast; ring
      calc _ = b01 x * cexp (-yv v * (x : ℂ)) +
            (bP1 x * (cexp (Complex.I * ((4 / 3 * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ))) +
             bN1 x * (cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * cexp (-yv v * (x : ℂ)))) := by ring
        _ = _ := by rw [hexp_P, hexp_N, hexp_yv]
    have hosc1 : IntegrableOn (fun x =>
        bP1 x * cexp (Complex.I * ((1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ)) +
        bN1 x * cexp (Complex.I * ((-1 * (4 / 3 : ℝ) * x ^ (3 / 2 : ℝ) - (ceCs * v) * x : ℝ) : ℂ))) (Ici x₀) :=
      (int_osc hP1 sbP1 _).add (int_osc hN1 sbN1 _)
    rw [setIntegral_congr_fun measurableSet_Ici hpt,
      integral_add (int_st h01 sb01_x0 _) hosc1,
      integral_add (int_osc hP1 sbP1 _) (int_osc hN1 sbN1 _)]
    dsimp [Jh1_v, F_st, F_P, F_N]; ring
  -- Express `G v = airyTwistedLaplaceC X (yv v)` using `Jh0_v, Jh1_v`!
  let G : ℝ → ℂ := fun v => airyTwistedLaplaceC X (yv v)
  let Φ : ℝ → ℂ := fun v => (ceK : ℂ) * cexp (-(yv v ^ 3) / 12)
  let F0v : ℝ → ℂ := fun v => F_st h₀_st (ceCs * v)
  let F1v : ℝ → ℂ := fun v => F_st b01 (ceCs * v)
  let Y2v : ℝ → ℂ := fun v => yv v / 2
  let B_sym : ℝ → ℂ := fun v => I_r v + (1 / 2 : ℂ) * (r01 x₀ * (airyAi (-x₀) : ℂ) ^ 2) * cexp (-yv v * (x₀ : ℂ)) +
    F_P h₀_P (ceCs * v) + F_N h₀_N (ceCs * v) - Y2v v * (F_P bP1 (ceCs * v) + F_N bN1 (ceCs * v))
  let H : ℝ → ℂ := fun v => B_sym v + F0v v - Y2v v * F1v v
  have hG_split : G = fun v => Φ v * H v := by
    ext v
    have hl := (hsplit (yv v) (by rw [yv_re])).2.2.2
    dsimp [G]
    rw [airyTwistedLaplaceC_eq_lapC, hl, hJh0_eq v, hJh1_eq v]
    dsimp [Φ, H, B_sym, F0v, F1v, Y2v, I_r, Jh0_v, Jh1_v]; ring
  have hcd_yv : ContDiff ℝ 2 yv := by
    unfold yv
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hcd_Φ : ContDiff ℝ 2 Φ :=
    contDiff_const.mul (((hcd_yv.pow 3).neg.div_const 12).cexp)
  have hcd_Y2 : ContDiff ℝ 2 Y2v := hcd_yv.div_const 2
  have hcd_lin : ContDiff ℝ 1 (fun v : ℝ => ceCs * v) := contDiff_const.mul contDiff_id
  have hcd_lin2 : ContDiff ℝ 2 (fun v : ℝ => ceCs * v) := contDiff_const.mul contDiff_id
  have hcd_B : ContDiff ℝ 2 B_sym := by
    dsimp [B_sym]
    have hcexp_x0 : ContDiff ℝ 2 (fun v : ℝ => (1 / 2 : ℂ) * (r01 x₀ * (airyAi (-x₀) : ℂ) ^ 2) * cexp (-yv v * (x₀ : ℂ))) :=
      contDiff_const.mul ((hcd_yv.neg.mul contDiff_const).cexp)
    exact ((((hcd_Ir.add hcexp_x0).add (hFP0_cd2.comp hcd_lin2)).add
      (hFN0_cd2.comp hcd_lin2)).sub (hcd_Y2.mul ((hFP1_cd2.comp hcd_lin2).add (hFN1_cd2.comp hcd_lin2))))
  have hcd_F0 : ContDiff ℝ 1 F0v := hF0_cd1.comp hcd_lin
  have hcd_F1 : ContDiff ℝ 1 F1v := hF1_cd1.comp hcd_lin
  have hcd_H : ContDiff ℝ 1 H := ((hcd_B.of_le (by norm_num)).add hcd_F0).sub ((hcd_Y2.of_le (by norm_num)).mul hcd_F1)
  have hG_cd1 : ContDiff ℝ 1 G := by rw [hG_split]; exact (hcd_Φ.of_le (by norm_num)).mul hcd_H
  have hb_box : ∀ {f : ℝ → ℂ}, Continuous f → ∃ C ≥ 0, ∀ v : ℝ, |v| ≤ 1 → ‖f v‖ ≤ C := fun hf => by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun v hv => (hM v (abs_le.mp hv)).trans (le_max_left _ _)⟩
  obtain ⟨MΦ0, hMΦ0, bΦ0⟩ := hb_box (hcd_Φ.continuous)
  obtain ⟨MΦ1, hMΦ1, bΦ1⟩ := hb_box ((hcd_Φ.of_le (by norm_num)).continuous_deriv_one)
  obtain ⟨MΦ2, hMΦ2, bΦ2⟩ := hb_box (((contDiff_succ_iff_deriv (n := 1)).mp hcd_Φ).2.2.continuous_deriv_one)
  obtain ⟨MH0, hMH0, bH0⟩ := hb_box (hcd_H.continuous)
  obtain ⟨MH1, hMH1, bH1⟩ := hb_box (hcd_H.continuous_deriv_one)
  obtain ⟨MB2, hMB2, bB2⟩ := hb_box (((contDiff_succ_iff_deriv (n := 1)).mp hcd_B).2.2.continuous_deriv_one)
  obtain ⟨MF1_0, hMF1_0, bF1_0⟩ := hb_box (hcd_F1.continuous)
  obtain ⟨MF1_1, hMF1_1, bF1_1⟩ := hb_box (hcd_F1.continuous_deriv_one)
  obtain ⟨MY0, hMY0, bY0⟩ := hb_box (hcd_Y2.continuous)
  obtain ⟨MY1, hMY1, bY1⟩ := hb_box ((hcd_Y2.of_le (by norm_num)).continuous_deriv_one)
  obtain ⟨MY2, hMY2, bY2⟩ := hb_box (((contDiff_succ_iff_deriv (n := 1)).mp hcd_Y2).2.2.continuous_deriv_one)
  -- Bound `‖deriv (deriv G) v‖ ≤ Ms * |v|^{-1/2}` on `0 < |v| ≤ 1`
  let C_F : ℝ := ceCs ^ (3 / 2 : ℝ) * (Cst0 + Cst1)
  have hCF : 0 ≤ C_F := mul_nonneg (Real.rpow_nonneg ceCs_pos.le _) (add_nonneg hCst0.le hCst1.le)
  let Ms : ℝ := MΦ2 * MH0 + 2 * MΦ1 * MH1 + MΦ0 * (MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F)
  have hMs : 0 ≤ Ms := by positivity
  have h_small_d2 : ∀ v : ℝ, v ≠ 0 → |v| ≤ 1 →
      ‖deriv (deriv G) v‖ ≤ Ms * |v| ^ (-(1 / 2 : ℝ)) := fun v hv hv1 => by
    have hq0 : ceCs * v ≠ 0 := mul_ne_zero ceCs_pos.ne' hv
    have hqcs : |ceCs * v| ≤ ceCs := by
      rw [abs_mul, abs_of_pos ceCs_pos]
      exact mul_le_of_le_one_right ceCs_pos.le hv1
    obtain ⟨hF0_at, bF0''⟩ := hF0_d2 (ceCs * v) hq0 hqcs
    obtain ⟨hF1_at, bF1''⟩ := hF1_d2 (ceCs * v) hq0 hqcs
    have hF0_deriv_eq : ∀ w : ℝ, deriv F0v w = (ceCs : ℂ) * deriv (F_st h₀_st) (ceCs * w) := fun w => by
      have hlin' : HasDerivAt (fun t : ℝ => ceCs * t) ceCs w := by simpa using (hasDerivAt_id w).const_mul ceCs
      have hd : HasDerivAt (F_st h₀_st ∘ fun t : ℝ => ceCs * t) ((ceCs : ℂ) * deriv (F_st h₀_st) (ceCs * w)) w := by
        simpa [Complex.real_smul] using (hF0_cd1.differentiable (by norm_num) (ceCs * w)).hasDerivAt.scomp w hlin'
      rw [show F0v = F_st h₀_st ∘ fun t : ℝ => ceCs * t from rfl]
      exact hd.deriv
    have hF1_deriv_eq : ∀ w : ℝ, deriv F1v w = (ceCs : ℂ) * deriv (F_st b01) (ceCs * w) := fun w => by
      have hlin' : HasDerivAt (fun t : ℝ => ceCs * t) ceCs w := by simpa using (hasDerivAt_id w).const_mul ceCs
      have hd : HasDerivAt (F_st b01 ∘ fun t : ℝ => ceCs * t) ((ceCs : ℂ) * deriv (F_st b01) (ceCs * w)) w := by
        simpa [Complex.real_smul] using (hF1_cd1.differentiable (by norm_num) (ceCs * w)).hasDerivAt.scomp w hlin'
      rw [show F1v = F_st b01 ∘ fun t : ℝ => ceCs * t from rfl]
      exact hd.deriv
    have hlin' : HasDerivAt (fun t : ℝ => ceCs * t) ceCs v := by simpa using (hasDerivAt_id v).const_mul ceCs
    have hd_F0' : HasDerivAt (deriv F0v) ((ceCs : ℂ) ^ 2 * deriv (deriv (F_st h₀_st)) (ceCs * v)) v := by
      rw [show deriv F0v = fun w => (ceCs : ℂ) * deriv (F_st h₀_st) (ceCs * w) from funext hF0_deriv_eq]
      exact ((hF0_at.hasDerivAt.scomp v hlin').const_mul (ceCs : ℂ)).congr_deriv (by rw [Complex.real_smul]; ring)
    have hd_F1' : HasDerivAt (deriv F1v) ((ceCs : ℂ) ^ 2 * deriv (deriv (F_st b01)) (ceCs * v)) v := by
      rw [show deriv F1v = fun w => (ceCs : ℂ) * deriv (F_st b01) (ceCs * w) from funext hF1_deriv_eq]
      exact ((hF1_at.hasDerivAt.scomp v hlin').const_mul (ceCs : ℂ)).congr_deriv (by rw [Complex.real_smul]; ring)
    have hr_inv : (ceCs * |v|) ^ (-(1 / 2 : ℝ)) = ceCs ^ (-(1 / 2 : ℝ)) * |v| ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow ceCs_pos.le (abs_nonneg v)
    have hcs_32 : ceCs ^ 2 * ceCs ^ (-(1 / 2 : ℝ)) = ceCs ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ceCs 2, ← Real.rpow_add ceCs_pos]; norm_num
    have hF0_2_bd : ‖deriv (deriv F0v) v‖ ≤ C_F * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [hd_F0'.deriv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
      rw [abs_mul, abs_of_pos ceCs_pos, hr_inv] at bF0''
      calc ceCs ^ 2 * ‖deriv (deriv (F_st h₀_st)) (ceCs * v)‖
          ≤ ceCs ^ 2 * (Cst0 * (ceCs ^ (-(1 / 2 : ℝ)) * |v| ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left bF0'' (sq_nonneg _)
        _ = (ceCs ^ (3 / 2 : ℝ) * Cst0) * |v| ^ (-(1 / 2 : ℝ)) := by rw [← hcs_32]; ring
        _ ≤ C_F * |v| ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_add_of_le_of_nonneg le_rfl hCst1.le) (Real.rpow_nonneg ceCs_pos.le _))
              (Real.rpow_nonneg (abs_nonneg v) _)
    have hF1_2_bd : ‖deriv (deriv F1v) v‖ ≤ C_F * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [hd_F1'.deriv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
      rw [abs_mul, abs_of_pos ceCs_pos, hr_inv] at bF1''
      calc ceCs ^ 2 * ‖deriv (deriv (F_st b01)) (ceCs * v)‖
          ≤ ceCs ^ 2 * (Cst1 * (ceCs ^ (-(1 / 2 : ℝ)) * |v| ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left bF1'' (sq_nonneg _)
        _ = (ceCs ^ (3 / 2 : ℝ) * Cst1) * |v| ^ (-(1 / 2 : ℝ)) := by rw [← hcs_32]; ring
        _ ≤ C_F * |v| ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_add_of_nonneg_of_le hCst0.le le_rfl) (Real.rpow_nonneg ceCs_pos.le _))
              (Real.rpow_nonneg (abs_nonneg v) _)
    have hr1 : 1 ≤ |v| ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr hv) hv1 (by norm_num)
    have hr0 : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) := by linarith
    -- Differentiability of `deriv Φ, deriv B_sym, deriv Y2v`
    have hd_Φ : ∀ w : ℝ, HasDerivAt Φ (deriv Φ w) w := fun w => (hcd_Φ.differentiable (by norm_num) w).hasDerivAt
    have hd_Φ' : HasDerivAt (deriv Φ) (deriv (deriv Φ) v) v :=
      (((contDiff_succ_iff_deriv (n := 1)).mp hcd_Φ).2.2.differentiable (by norm_num) v).hasDerivAt
    have hd_B : ∀ w : ℝ, HasDerivAt B_sym (deriv B_sym w) w := fun w => (hcd_B.differentiable (by norm_num) w).hasDerivAt
    have hd_B' : HasDerivAt (deriv B_sym) (deriv (deriv B_sym) v) v :=
      (((contDiff_succ_iff_deriv (n := 1)).mp hcd_B).2.2.differentiable (by norm_num) v).hasDerivAt
    have hd_Y2 : ∀ w : ℝ, HasDerivAt Y2v (deriv Y2v w) w := fun w => (hcd_Y2.differentiable (by norm_num) w).hasDerivAt
    have hd_Y2' : HasDerivAt (deriv Y2v) (deriv (deriv Y2v) v) v :=
      (((contDiff_succ_iff_deriv (n := 1)).mp hcd_Y2).2.2.differentiable (by norm_num) v).hasDerivAt
    have hd_F0 : ∀ w : ℝ, HasDerivAt F0v (deriv F0v w) w := fun w => (hcd_F0.differentiable (by norm_num) w).hasDerivAt
    have hd_F1 : ∀ w : ℝ, HasDerivAt F1v (deriv F1v w) w := fun w => (hcd_F1.differentiable (by norm_num) w).hasDerivAt
    have hderiv_H_eq : deriv H = fun w => deriv B_sym w + deriv F0v w - (deriv Y2v w * F1v w + Y2v w * deriv F1v w) := by
      ext w; exact (((hd_B w).add (hd_F0 w)).sub ((hd_Y2 w).mul (hd_F1 w))).deriv
    have hd_H' : HasDerivAt (deriv H) (deriv (deriv B_sym) v + deriv (deriv F0v) v -
        ((deriv (deriv Y2v) v * F1v v + deriv Y2v v * deriv F1v v) +
         (deriv Y2v v * deriv F1v v + Y2v v * deriv (deriv F1v) v))) v := by
      rw [hderiv_H_eq]
      exact (hd_B'.add (hd_F0'.congr_deriv hd_F0'.deriv.symm)).sub
        (((hd_Y2'.mul (hd_F1 v)).add ((hd_Y2 v).mul (hd_F1'.congr_deriv hd_F1'.deriv.symm))))
    have hH''_bd : ‖deriv (deriv H) v‖ ≤
        (MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F) * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [hd_H'.deriv]
      have t1 : ‖deriv (deriv B_sym) v‖ ≤ MB2 * |v| ^ (-(1 / 2 : ℝ)) :=
        (bB2 v hv1).trans (le_mul_of_one_le_right hMB2 hr1)
      have t2 : ‖deriv (deriv Y2v) v * F1v v‖ ≤ MY2 * MF1_0 * |v| ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul]
        exact (mul_le_mul (bY2 v hv1) (bF1_0 v hv1) (norm_nonneg _) hMY2).trans
          (le_mul_of_one_le_right (by positivity) hr1)
      have t3 : ‖deriv Y2v v * deriv F1v v‖ ≤ MY1 * MF1_1 * |v| ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul]
        exact (mul_le_mul (bY1 v hv1) (bF1_1 v hv1) (norm_nonneg _) hMY1).trans
          (le_mul_of_one_le_right (by positivity) hr1)
      have t4 : ‖Y2v v * deriv (deriv F1v) v‖ ≤ MY0 * C_F * |v| ^ (-(1 / 2 : ℝ)) := by
        rw [norm_mul]
        calc ‖Y2v v‖ * ‖deriv (deriv F1v) v‖ ≤ MY0 * (C_F * |v| ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul (bY0 v hv1) hF1_2_bd (norm_nonneg _) hMY0
          _ = MY0 * C_F * |v| ^ (-(1 / 2 : ℝ)) := by ring
      have hsub := norm_sub_le (deriv (deriv B_sym) v + deriv (deriv F0v) v)
        ((deriv (deriv Y2v) v * F1v v + deriv Y2v v * deriv F1v v) + (deriv Y2v v * deriv F1v v + Y2v v * deriv (deriv F1v) v))
      have ha1 := norm_add_le (deriv (deriv B_sym) v) (deriv (deriv F0v) v)
      have ha2 := norm_add_le (deriv (deriv Y2v) v * F1v v + deriv Y2v v * deriv F1v v) (deriv Y2v v * deriv F1v v + Y2v v * deriv (deriv F1v) v)
      have ha3 := norm_add_le (deriv (deriv Y2v) v * F1v v) (deriv Y2v v * deriv F1v v)
      have ha4 := norm_add_le (deriv Y2v v * deriv F1v v) (Y2v v * deriv (deriv F1v) v)
      calc ‖deriv (deriv B_sym) v + deriv (deriv F0v) v -
            ((deriv (deriv Y2v) v * F1v v + deriv Y2v v * deriv F1v v) +
              (deriv Y2v v * deriv F1v v + Y2v v * deriv (deriv F1v) v))‖
          ≤ (‖deriv (deriv B_sym) v‖ + ‖deriv (deriv F0v) v‖) +
              ((‖deriv (deriv Y2v) v * F1v v‖ + ‖deriv Y2v v * deriv F1v v‖) +
                (‖deriv Y2v v * deriv F1v v‖ + ‖Y2v v * deriv (deriv F1v) v‖)) :=
              hsub.trans (add_le_add ha1 (ha2.trans (add_le_add ha3 ha4)))
        _ ≤ (MB2 * |v| ^ (-(1 / 2 : ℝ)) + C_F * |v| ^ (-(1 / 2 : ℝ))) +
              ((MY2 * MF1_0 * |v| ^ (-(1 / 2 : ℝ)) + MY1 * MF1_1 * |v| ^ (-(1 / 2 : ℝ))) +
                (MY1 * MF1_1 * |v| ^ (-(1 / 2 : ℝ)) + MY0 * C_F * |v| ^ (-(1 / 2 : ℝ)))) :=
              add_le_add (add_le_add t1 hF0_2_bd) (add_le_add (add_le_add t2 t3) (add_le_add t3 t4))
        _ = (MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F) * |v| ^ (-(1 / 2 : ℝ)) := by ring
    have hd_H : ∀ w : ℝ, HasDerivAt H (deriv H w) w := fun w => (hcd_H.differentiable (by norm_num) w).hasDerivAt
    have hderiv_G_eq : deriv G = fun w => deriv Φ w * H w + Φ w * deriv H w := by
      ext w; rw [hG_split]; exact ((hd_Φ w).mul (hd_H w)).deriv
    have hd_G' : HasDerivAt (deriv G) ((deriv (deriv Φ) v * H v + deriv Φ v * deriv H v) +
        (deriv Φ v * deriv H v + Φ v * deriv (deriv H) v)) v := by
      rw [hderiv_G_eq]
      exact (hd_Φ'.mul (hd_H v)).add ((hd_Φ v).mul (hd_H'.congr_deriv hd_H'.deriv.symm))
    rw [hd_G'.deriv]
    have u1 : ‖deriv (deriv Φ) v * H v‖ ≤ MΦ2 * MH0 * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul]; exact (mul_le_mul (bΦ2 v hv1) (bH0 v hv1) (norm_nonneg _) hMΦ2).trans
        (le_mul_of_one_le_right (by positivity) hr1)
    have u2 : ‖deriv Φ v * deriv H v‖ ≤ MΦ1 * MH1 * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul]; exact (mul_le_mul (bΦ1 v hv1) (bH1 v hv1) (norm_nonneg _) hMΦ1).trans
        (le_mul_of_one_le_right (by positivity) hr1)
    have u3 : ‖Φ v * deriv (deriv H) v‖ ≤ MΦ0 * (MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F) * |v| ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul]
      calc ‖Φ v‖ * ‖deriv (deriv H) v‖
          ≤ MΦ0 * ((MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F) * |v| ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul (bΦ0 v hv1) hH''_bd (norm_nonneg _) hMΦ0
        _ = _ := by ring
    have ha := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    calc ‖deriv (deriv Φ) v * H v + deriv Φ v * deriv H v + (deriv Φ v * deriv H v + Φ v * deriv (deriv H) v)‖
        ≤ (‖deriv (deriv Φ) v * H v‖ + ‖deriv Φ v * deriv H v‖) +
            (‖deriv Φ v * deriv H v‖ + ‖Φ v * deriv (deriv H) v‖) := ha
      _ ≤ (MΦ2 * MH0 * |v| ^ (-(1 / 2 : ℝ)) + MΦ1 * MH1 * |v| ^ (-(1 / 2 : ℝ))) +
            (MΦ1 * MH1 * |v| ^ (-(1 / 2 : ℝ)) +
              MΦ0 * (MB2 + C_F + MY2 * MF1_0 + 2 * MY1 * MF1_1 + MY0 * C_F) * |v| ^ (-(1 / 2 : ℝ))) :=
            add_le_add (add_le_add u1 u2) (add_le_add u2 u3)
      _ = Ms * |v| ^ (-(1 / 2 : ℝ)) := by dsimp [Ms]; ring
  -- Global `SmoothSymbol` by stitching `|v| ≤ 1` with `htail` (`1 < |v|`)
  obtain ⟨M0, hM0, b0_sm⟩ := hb_box hG_cd1.continuous
  obtain ⟨M1, hM1, b1_sm⟩ := hb_box hG_cd1.continuous_deriv_one
  let CG : ℝ := 32 * (M0 + M1 + Ms + CT)
  have hCT_CG : 32 * CT ≤ CG := by
    dsimp [CG]
    have : CT ≤ M0 + M1 + Ms + CT := by linarith [hM0, hM1, hMs]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have hM0_CG : 8 * M0 ≤ CG := by
    dsimp [CG]
    have : M0 ≤ 4 * (M0 + M1 + Ms + CT) := by linarith [hM0, hM1, hMs, hCT]
    linarith
  have hM1_CG : 8 * M1 ≤ CG := by
    dsimp [CG]
    have : M1 ≤ 4 * (M0 + M1 + Ms + CT) := by linarith [hM0, hM1, hMs, hCT]
    linarith
  have hMs_CG : 8 * Ms ≤ CG := by
    dsimp [CG]
    have : Ms ≤ 4 * (M0 + M1 + Ms + CT) := by linarith [hM0, hM1, hMs, hCT]
    linarith
  have h5 : ∀ v : ℝ, |v| ≤ 1 → 1 / 8 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := fun v hv =>
    one_add_rpow_ge hv (by norm_num) (by norm_num)
  have h2 : ∀ v : ℝ, |v| ≤ 1 → 1 / 8 ≤ (1 + |v|) ^ (-(2 : ℝ)) := fun v hv =>
    one_add_rpow_ge hv (by norm_num) (by norm_num)
  have P5 : ∀ v : ℝ, 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := fun v => Real.rpow_nonneg (by linarith [abs_nonneg v]) _
  have P2 : ∀ v : ℝ, 0 ≤ (1 + |v|) ^ (-(2 : ℝ)) := fun v => Real.rpow_nonneg (by linarith [abs_nonneg v]) _
  have hr_52 : ∀ {v : ℝ}, 1 < |v| → |v| ^ (-(5 / 2 : ℝ)) ≤ 32 * (1 + |v|) ^ (-(5 / 2 : ℝ)) := fun {v} hv => by
    have h2v : (1 + |v|) ^ (-(5 / 2 : ℝ)) ≥ (2 * |v|) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (abs_nonneg v)] at h2v
    have h2_bd : (2 : ℝ) ^ (-(5 / 2 : ℝ)) ≥ (1 / 32 : ℝ) := by
      have h52 : (2 : ℝ) ^ (-5 : ℝ) ≤ (2 : ℝ) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h32 : (2 : ℝ) ^ (-5 : ℝ) = (1 / 32 : ℝ) := by norm_num
      linarith
    have hvnn : 0 ≤ |v| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg v) _
    have : (1 / 32 : ℝ) * |v| ^ (-(5 / 2 : ℝ)) ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) :=
      (mul_le_mul_of_nonneg_right h2_bd hvnn).trans h2v
    linarith
  have hU : IsOpen {v : ℝ | v ≠ 0} := isOpen_ne
  have hCD1 : ContDiffOn ℝ 1 (deriv G) {v : ℝ | v ≠ 0} := htail.contDiff.deriv_of_isOpen hU (by norm_num)
  refine ⟨CG, by positivity, hG_cd1, fun x hx => ?_, fun v => ?_, fun v => ?_, fun v hv => ?_⟩
  · exact (hCD1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  · by_cases hv : 1 < |v|
    · calc ‖G v‖ ≤ CT * |v| ^ (-(5 / 2 : ℝ)) := htail.b0 v hv
        _ ≤ CT * (32 * (1 + |v|) ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hr_52 hv) hCT.le
        _ = (32 * CT) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by ring
        _ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hCT_CG (P5 v)
    · have hv1 : |v| ≤ 1 := not_lt.mp hv
      have h8 := h5 v hv1
      calc ‖G v‖ ≤ M0 := b0_sm v hv1
        _ = (8 * M0) * (1 / 8) := by ring
        _ ≤ (8 * M0) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h8 (by positivity)
        _ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hM0_CG (P5 v)
  · by_cases hv : 1 < |v|
    · have h75 : |v| ^ (-(7 / 2 : ℝ)) ≤ |v| ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hv.le (by norm_num)
      calc ‖deriv G v‖ ≤ CT * |v| ^ (-(7 / 2 : ℝ)) := htail.b1 v hv
        _ ≤ CT * |v| ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h75 hCT.le
        _ ≤ CT * (32 * (1 + |v|) ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hr_52 hv) hCT.le
        _ = (32 * CT) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by ring
        _ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hCT_CG (P5 v)
    · have hv1 : |v| ≤ 1 := not_lt.mp hv
      have h8 := h5 v hv1
      calc ‖deriv G v‖ ≤ M1 := b1_sm v hv1
        _ = (8 * M1) * (1 / 8) := by ring
        _ ≤ (8 * M1) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h8 (by positivity)
        _ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hM1_CG (P5 v)
  · have hv0 : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg v) _
    have hQ : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := mul_nonneg hv0 (P2 v)
    by_cases hv1 : 1 < |v|
    · have h2v : (1 + |v|) ^ (-(2 : ℝ)) ≥ (2 * |v|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      rw [Real.mul_rpow (by norm_num) (abs_nonneg v)] at h2v
      have h4_bd : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by norm_num
      have h_2_bd : |v| ^ (-(2 : ℝ)) ≤ 4 * (1 + |v|) ^ (-(2 : ℝ)) := by
        rw [h4_bd] at h2v; linarith
      have h4_2 : |v| ^ (-(4 : ℝ)) ≤ |v| ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hv1.le (by norm_num)
      have h_92 : |v| ^ (-(9 / 2 : ℝ)) = |v| ^ (-(1 / 2 : ℝ)) * |v| ^ (-(4 : ℝ)) := by
        rw [← Real.rpow_add (abs_pos.mpr hv)]; norm_num
      calc ‖deriv (deriv G) v‖ ≤ CT * |v| ^ (-(9 / 2 : ℝ)) := htail.b2 v hv1
        _ = CT * (|v| ^ (-(1 / 2 : ℝ)) * |v| ^ (-(4 : ℝ))) := by rw [h_92]
        _ ≤ CT * (|v| ^ (-(1 / 2 : ℝ)) * (4 * (1 + |v|) ^ (-(2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h4_2.trans h_2_bd) hv0) hCT.le
        _ ≤ CT * (32 * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 32) hQ) hCT.le
        _ = (32 * CT) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by ring
        _ ≤ CG * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_right hCT_CG hQ
    · have hle1 : |v| ≤ 1 := not_lt.mp hv1
      have hP := h2 v hle1
      have hm := h_small_d2 v hv hle1
      calc ‖deriv (deriv G) v‖ ≤ Ms * |v| ^ (-(1 / 2 : ℝ)) := hm
        _ = (8 * Ms) * (|v| ^ (-(1 / 2 : ℝ)) * (1 / 8)) := by ring
        _ ≤ (8 * Ms) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hv0) (by positivity)
        _ ≤ CG * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_right hMs_CG hQ

/-! ### Section 5: High-band `(e4)` and `u1c:U1` for `HasGenRationalAiryCoeffs` & bounded families -/

/-- High-band `(e4)` estimate for `F` with `HasGenRationalAiryCoeffs F 0 0` (`γ₀ = 0`). -/
theorem hb_estimate_genRational_zero {F : ℂ → ℂ} (hF : HasGenRationalAiryCoeffs F 0 0)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => (F (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨χ, Kχ, hχ⟩ := exists_cutoffData
  obtain ⟨CG, hCG, hsm⟩ := smoothSymbol_of_genRational_zero hF
  obtain ⟨CT, hCT, htail⟩ := symbolTail_of_genRational hF
  have hsm_zero : SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC X (yv v) +
      ((0 : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ v : ℂ)) CG := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hsm
  have hsm_yv : SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
      ((0 : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ v : ℂ)) CG :=
    hsm_zero
  obtain ⟨Cin, hCin, hin⟩ := hb_inner X 0 CG hχ hsm_yv m
  obtain ⟨Cout, hCout, hout⟩ := hb_outer hCT.le htail hχ hm
  refine ⟨Cin + Cout, add_pos hCin hCout, fun {K M₁ c ξ} hK hM₁ hc8 hc2k hξ hS100 hMS => ?_⟩
  have hU2 : HasU2 X := hasU2_of_genRational hF
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hint_full : Integrable (iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ) :=
    hU2.integrable_iMainIntegrand hδ0 m hc0 hξ
  set vs := tauStar (Real.log (Real.pi ^ 2 * ξ)) / liftEps c
  have hsplit_int : iMain X (ceBeta1 * K * liftEps c / 2) m c ξ =
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, (χ (v / vs) : ℂ) *
        iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) +
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, ((1 - χ (v / vs) : ℝ) : ℂ) *
        iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) := by
    have h1 : Integrable (fun v : ℝ => (χ (v / vs) : ℂ) *
        iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) :=
      hint_full.bdd_mul (Complex.continuous_ofReal.comp (hχ.contDiff.continuous.comp (continuous_id.div_const _))).aestronglyMeasurable
        (ae_of_all _ fun v => by simpa [Complex.norm_real] using hχ.b0 (v / vs))
    have h2 : Integrable (fun v : ℝ => ((1 - χ (v / vs) : ℝ) : ℂ) *
        iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) :=
      hint_full.bdd_mul (Complex.continuous_ofReal.comp (continuous_const.sub (hχ.contDiff.continuous.comp (continuous_id.div_const _)))).aestronglyMeasurable
        (ae_of_all _ fun v => by
          rw [Complex.norm_real, Real.norm_eq_abs]
          calc |1 - χ (v / vs)| ≤ |(1 : ℝ)| + |χ (v / vs)| := abs_sub _ _
            _ ≤ 1 + Kχ := by rw [abs_one]; exact add_le_add le_rfl (hχ.b0 (v / vs)))
    rw [iMain, ← mul_add, ← integral_add h1 h2]
    congr 2; ext v; push_cast; ring
  have h1 := hin hK hc8 hc2k hξ hS100
  have h2 := hout hK hM₁ hc8 hc2k hξ hS100 hMS
  simp only [zero_mul, zero_div, Complex.ofReal_zero, sub_zero] at h1
  have h2' : ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℝ) : ℂ) *
      iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v‖ =
      ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (v / vs) : ℝ) : ℂ) *
      iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v‖ := by
    congr 3; ext v; dsimp [vs]; rw [div_div_eq_mul_div, mul_comm v]
  rw [h2'] at h2
  have hA0 : 0 ≤ hbA c ξ := by
    have hA_eq : hbA c ξ = c * liftEps c * (hbS c ξ * (Real.pi ^ 2 * liftEps c ^ 2)) := by
      unfold hbA hbS; have := liftEps_pos hc0; field_simp
    rw [hA_eq]; have := liftEps_pos hc0; positivity
  have hPpos : 0 ≤ hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) :=
    div_nonneg (Real.rpow_nonneg hA0 _) (by positivity)
  have hE1 : 0 ≤ M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) := by positivity
  have hE2 : 0 ≤ hbS c ξ ^ (-(1 / 2 : ℝ)) := by positivity
  calc ‖iMain X (ceBeta1 * K * liftEps c / 2) m c ξ‖
      ≤ ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, (χ (v / vs) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v‖ +
        ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (v / vs) : ℝ) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v‖ := by
          rw [hsplit_int]; exact norm_add_le _ _
    _ ≤ Cin * hbS c ξ ^ (-(1 / 2 : ℝ)) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) +
        Cout * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ))) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) :=
          add_le_add h1 h2
    _ ≤ (Cin + Cout) * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
          nlinarith [mul_nonneg hCin.le (mul_nonneg hE1 hPpos), mul_nonneg hCout.le (mul_nonneg hE2 hPpos)]

/-- Uniform `(e4)` high-band estimate for any `F` satisfying `HasGenRationalAiryCoeffs F β₀₀ β₁₁`,
with leading coefficient `(β₀₀ + β₁₁) * (2 * ceK * cA * ceCs^{1/2}) = airyBetaInf F * g0`. -/
theorem hb_estimate_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => (F (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          (((β₀₀ + β₁₁) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
            hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  let F_rem : ℂ → ℂ := fun z => F z - (((-β₀₀ : ℝ) : ℂ) * airySeedF 0 z + (β₁₁ : ℂ) * airySeedG1Deriv z)
  obtain ⟨hrem, hdecomp⟩ := hasGenRational_decomp hF
  obtain ⟨Cl, hCl, hlin⟩ := hb_estimate_airySeed_uniform_val hm (max |β₀₀| |β₁₁|) (by positivity)
  obtain ⟨Cr, hCr, hre⟩ := hb_estimate_genRational_zero hrem hm
  refine ⟨Cl + Cr, add_pos hCl hCr, fun {K M₁ c ξ} hK hM₁ hc8 hc2k hξ hS100 hMS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hU_lin : HasU2 (airySeedU2 (-β₀₀) 0 β₁₁) := hasU2_airySeedU2 (-β₀₀) 0 β₁₁
  have hU_rem : HasU2 (fun u => (F_rem (u : ℂ)).re) := hasU2_of_genRational hrem
  have hadd : iMain (fun u => (F (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ =
      iMain (airySeedU2 (-β₀₀) 0 β₁₁) (ceBeta1 * K * liftEps c / 2) m c ξ +
      iMain (fun u => (F_rem (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ := by
    rw [show (fun u : ℝ => (F (u : ℂ)).re) = fun u => airySeedU2 (-β₀₀) 0 β₁₁ u + (F_rem (u : ℂ)).re from
      funext hdecomp]
    exact iMain_add hU_lin hU_rem hδ0 m hc0 hξ
  have h1 := hlin (a := -β₀₀) (b := 0) (c₀ := β₁₁) (by rw [abs_neg]; exact le_max_left _ _)
    (by simp) (le_max_right _ _) hK hM₁ hc8 hc2k hξ hS100 hMS
  have h2 := hre hK hM₁ hc8 hc2k hξ hS100 hMS
  have hcoef : β₁₁ - -β₀₀ = β₀₀ + β₁₁ := by ring
  rw [hcoef] at h1
  have hsplit_sub : ∀ a b t : ℂ, (a + b) - t = (a - t) + b := fun _ _ _ => by ring
  rw [hadd, hsplit_sub]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- Uniform `(e4)` high-band estimate over any uniformly bounded finite linear combination
`∑ i ∈ s, α i K c • B i` in `ℛ_Ai^gen`. -/
theorem hb_estimate_genRational_family {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ)
    (β₀₀ β₁₁ : ι → ℝ) (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (β₀₀ i) (β₁₁ i))
    {R : ℝ} (hR : 0 ≤ R) {α : ι → ℝ → ℝ → ℝ}
    (hα : ∀ i ∈ s, ∀ K c : ℝ, |α i K c| ≤ R) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          (((∑ i ∈ s, α i K c * (β₀₀ i + β₁₁ i)) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
            hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  classical
  have h_each : ∀ i ∈ s, ∃ Ci > 0, ∀ {K M₁ c ξ : ℝ},
      1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          (((β₀₀ i + β₁₁ i) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
            hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        Ci * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := fun i hi => hb_estimate_genRational (hB i hi) hm
  let Ci : ι → ℝ := fun i => if hi : i ∈ s then Classical.choose (h_each i hi) else 1
  have hCi0 : ∀ i, 0 < Ci i := fun i => by
    dsimp [Ci]; split_ifs with hi
    · exact (Classical.choose_spec (h_each i hi)).1
    · exact one_pos
  have hCi : ∀ i (hi : i ∈ s), ∀ {K M₁ c ξ : ℝ},
      1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          (((β₀₀ i + β₁₁ i) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
            hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        Ci i * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) :=
    fun i hi K M₁ c ξ hK hM₁ hc8 hc2k hξ hS100 hMS => by
      dsimp [Ci]; split_ifs
      exact (Classical.choose_spec (h_each i hi)).2 hK hM₁ hc8 hc2k hξ hS100 hMS
  refine ⟨R * ∑ i ∈ s, Ci i + 1, by
    have hsum : 0 ≤ ∑ i ∈ s, Ci i := Finset.sum_nonneg fun i _ => (hCi0 i).le
    positivity, fun {K M₁ c ξ} hK hM₁ hc8 hc2k hξ hS100 hMS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  -- Prove `iMain` distributes over `Finset.sum`
  have him_sum : ∀ (t : Finset ι), (∀ i ∈ t, HasGenRationalAiryCoeffs (B i) (β₀₀ i) (β₁₁ i)) →
      HasU2 (fun u => ∑ i ∈ t, α i K c * (B i (u : ℂ)).re) ∧
      iMain (fun u => ∑ i ∈ t, α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ =
        ∑ i ∈ t, (α i K c : ℂ) * iMain (fun u => (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ := by
    intro t ht
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨?_, ?_⟩
        · have hz : (fun _ : ℝ => (0 : ℝ)) = airySeedU2 0 0 0 := funext fun u => by simp [airySeedU2]
          simpa using hz ▸ hasU2_airySeedU2 0 0 0
        · simp [iMain, iMainIntegrand, liftSymbol, airyTwistedLaplaceC]
    | @insert a t hat ih =>
        have ha : HasGenRationalAiryCoeffs (B a) (β₀₀ a) (β₁₁ a) := ht a (Finset.mem_insert_self a t)
        have hts : ∀ i ∈ t, HasGenRationalAiryCoeffs (B i) (β₀₀ i) (β₁₁ i) :=
          fun i hi => ht i (Finset.mem_insert_of_mem hi)
        obtain ⟨hUt, hmt⟩ := ih hts
        have hUa : HasU2 (fun u => α a K c * (B a (u : ℂ)).re) :=
          (hasU2_of_genRational ha).smul _
        refine ⟨?_, ?_⟩
        · simp_rw [Finset.sum_insert hat]; exact hUa.add hUt
        · have hfn : (fun u : ℝ => ∑ i ∈ insert a t, α i K c * (B i (u : ℂ)).re) =
              fun u : ℝ => α a K c * (B a (u : ℂ)).re + ∑ i ∈ t, α i K c * (B i (u : ℂ)).re :=
            funext fun u => Finset.sum_insert hat
          rw [hfn, iMain_add hUa hUt hδ0 m hc0 hξ,
            iMain_const_mul (α a K c) (fun u => (B a (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ,
            hmt, Finset.sum_insert hat]
  obtain ⟨_, hms⟩ := him_sum s hB
  rw [hms]
  have hmain_eq : (((∑ i ∈ s, α i K c * (β₀₀ i + β₁₁ i)) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
      hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ) =
      ∑ i ∈ s, (α i K c : ℂ) * (((β₀₀ i + β₁₁ i) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi *
        hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ) := by
    push_cast; rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]; simp [mul_assoc, mul_div_assoc]
  rw [hmain_eq, ← Finset.sum_sub_distrib]
  calc ‖∑ i ∈ s, ((α i K c : ℂ) * iMain (fun u => (B i (u : ℂ)).re) _ m c ξ -
          (α i K c : ℂ) * _)‖
      ≤ ∑ i ∈ s, ‖(α i K c : ℂ) * (iMain (fun u => (B i (u : ℂ)).re) _ m c ξ - _)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_); congr 1; ext i; rw [mul_sub]
    _ ≤ ∑ i ∈ s, R * (Ci i * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hα i hi K c) (hCi i hi hK hM₁ hc8 hc2k hξ hS100 hMS) (norm_nonneg _) hR
    _ ≤ _ := by
        have hsum_eq : ∑ i ∈ s, R * (Ci i * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
            (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ))) =
            (R * ∑ i ∈ s, Ci i) * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
              (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
          simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
        rw [hsum_eq]
        have hA0 : 0 ≤ hbA c ξ := by
          have hA_eq : hbA c ξ = c * liftEps c * (hbS c ξ * (Real.pi ^ 2 * liftEps c ^ 2)) := by
            unfold hbA hbS; have := liftEps_pos hc0; field_simp
          rw [hA_eq]; have := liftEps_pos hc0; positivity
        have hP : 0 ≤ (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
            (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) :=
          mul_nonneg (by positivity) (div_nonneg (Real.rpow_nonneg hA0 _) (by positivity))
        nlinarith

/-- **`u1c:U1` branch-point expansion** on `0 ≤ y.re, ‖y‖ ≤ R` for any `F ∈ ℛ_Ai^gen`. -/
theorem u1c_expansion_of_genRational {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ R →
      ‖airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) y -
        airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) 0 +
        (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ ≤ C * ‖y‖ := by
  let F_rem : ℂ → ℂ := fun z => F z - (((-β₀₀ : ℝ) : ℂ) * airySeedF 0 z + (β₁₁ : ℂ) * airySeedG1Deriv z)
  obtain ⟨hrem, hdecomp⟩ := hasGenRational_decomp hF
  obtain ⟨Cr, hCr, hlip⟩ := u1c_lip_of_genRational_zero hrem R hR
  let X_lin : ℝ → ℝ := airySeedU2 (-β₀₀) 0 β₁₁
  have hU_lin := hasU2_airySeedU2 (-β₀₀) 0 β₁₁
  obtain ⟨A, B, hA, hB, hB0, hT⟩ :=
    (airySeedU2_sqFormAt (-β₀₀) 0 β₁₁).closed hU_lin.continuousOn
  have hB0' : B 0 = -(((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) := by
    rw [hB0]; push_cast; ring
  -- `A y - A 0 + y^{1/2} (B y - B 0)`: both `A` and `B` are entire, hence Lipschitz on `‖y‖ ≤ R`!
  have hd_A : ∃ M_A ≥ 0, ∀ {y : ℂ}, ‖y‖ ≤ R → ‖A y - A 0‖ ≤ M_A * ‖y‖ := by
    have hcont : Continuous fun z : ℂ => deriv A z := (hA.contDiff (n := 2)).continuous_deriv (by norm_num)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun {y} hy => ?_⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (C := max M 0)
      (fun z _ => hA z) (fun z hz => (hM z hz).trans (le_max_left M 0))
      (convex_closedBall 0 R) (Metric.mem_closedBall_self hR) (by simpa using hy)
    simpa [sub_zero] using hmvt
  have hd_B : ∃ M_B ≥ 0, ∀ {y : ℂ}, ‖y‖ ≤ R → ‖B y - B 0‖ ≤ M_B * ‖y‖ := by
    have hcont : Continuous fun z : ℂ => deriv B z := (hB.contDiff (n := 2)).continuous_deriv (by norm_num)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun {y} hy => ?_⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (C := max M 0)
      (fun z _ => hB z) (fun z hz => (hM z hz).trans (le_max_left M 0))
      (convex_closedBall 0 R) (Metric.mem_closedBall_self hR) (by simpa using hy)
    simpa [sub_zero] using hmvt
  obtain ⟨MA, hMA, bA⟩ := hd_A
  obtain ⟨MB, hMB, bB⟩ := hd_B
  refine ⟨MA + R ^ (1 / 2 : ℝ) * MB + Cr + 1, by positivity, fun {y} hy hyn => ?_⟩
  have hU_rem := hasU2_of_genRational hrem
  have heq_y : airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) y =
      airyTwistedLaplaceC X_lin y + airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) y := by
    rw [show (fun u : ℝ => (F (u : ℂ)).re) = fun u => X_lin u + (F_rem (u : ℂ)).re from funext hdecomp]
    exact airyTwistedLaplaceC_add (hU_lin.integrable y hy) (hU_rem.integrable y hy)
  have heq_0 : airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) 0 =
      airyTwistedLaplaceC X_lin 0 + airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) 0 := by
    rw [show (fun u : ℝ => (F (u : ℂ)).re) = fun u => X_lin u + (F_rem (u : ℂ)).re from funext hdecomp]
    exact airyTwistedLaplaceC_add (hU_lin.integrable 0 le_rfl) (hU_rem.integrable 0 le_rfl)
  have hTy := hT y hy
  have hT0 := hT 0 le_rfl
  simp only [Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), zero_mul, add_zero] at hT0
  have hdiff_lin : airyTwistedLaplaceC X_lin y - airyTwistedLaplaceC X_lin 0 +
      (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ) =
      (A y - A 0) + y ^ (1 / 2 : ℂ) * (B y - B 0) := by
    rw [hTy, hT0, hB0']; ring
  have hsqrt_le : ‖y ^ (1 / 2 : ℂ)‖ ≤ R ^ (1 / 2 : ℝ) := by
    by_cases hy0 : y = 0
    · simp [hy0]; positivity
    · rw [Complex.norm_cpow_of_ne_zero hy0]
      have hre_y : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      have him_y : (1 / 2 : ℂ).im = 0 := by norm_num
      rw [hre_y, him_y, mul_zero, Real.exp_zero, div_one]
      exact Real.rpow_le_rpow (norm_nonneg _) hyn (by norm_num)
  rw [heq_y, heq_0]
  calc ‖(airyTwistedLaplaceC X_lin y + airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) y) -
        (airyTwistedLaplaceC X_lin 0 + airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) 0) +
        (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖
      = ‖(airyTwistedLaplaceC X_lin y - airyTwistedLaplaceC X_lin 0 +
          (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) +
         (airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) y -
          airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) 0)‖ := by congr 1; ring
    _ ≤ ‖A y - A 0‖ + ‖y ^ (1 / 2 : ℂ)‖ * ‖B y - B 0‖ +
        ‖airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) y -
          airyTwistedLaplaceC (fun u => (F_rem (u : ℂ)).re) 0‖ := by
        rw [hdiff_lin]
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) le_rfl)
    _ ≤ MA * ‖y‖ + R ^ (1 / 2 : ℝ) * (MB * ‖y‖) + Cr * ‖y‖ := by
        gcongr
        · exact bA hyn
        · exact bB hyn
        · exact hlip hy hyn
    _ ≤ (MA + R ^ (1 / 2 : ℝ) * MB + Cr + 1) * ‖y‖ := by nlinarith [norm_nonneg y]

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.SignUncertainty.u1c_lip_of_genRational_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.u1c_lip_of_genRational_zero
/-- info: 'FormalResearch.SignUncertainty.symbolTail_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.symbolTail_of_genRational
/-- info: 'FormalResearch.SignUncertainty.smoothSymbol_of_genRational_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.smoothSymbol_of_genRational_zero
/-- info: 'FormalResearch.SignUncertainty.hb_estimate_genRational_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.hb_estimate_genRational_zero
/-- info: 'FormalResearch.SignUncertainty.hb_estimate_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.hb_estimate_genRational
/-- info: 'FormalResearch.SignUncertainty.hb_estimate_genRational_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.hb_estimate_genRational_family
/-- info: 'FormalResearch.SignUncertainty.u1c_expansion_of_genRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.SignUncertainty.u1c_expansion_of_genRational

end FormalResearch.SignUncertainty


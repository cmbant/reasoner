module

public import FormalResearch.ModularBootstrap.FixedWeightBand.GaussianPairingW
public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinConvergenceW

/-!
# Lemma S1 at Weight `w` (`vlo:S1`): `m_g` Entire with `m_g(w - z) = -m_g(z)`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`):
"`m_g` is entire and `m_g(w - z) = -m_g(z)`", with `m_g(z) = (2π)^z Mg(z)/Γ(z)` and
`Mg(z) = ∫₀^∞ g t^{z-1} dt`.

Proof, as in the paper:
1. (`MellinConvergenceW`, `MellinGrowthW`) `Mg(z)` converges absolutely on `Re z > 0` and `m_g` is
   holomorphic there (`t^r ≤ C_r V` on `[1, ∞)`, `g` bounded near `0`).
2. (`GaussianPairingW`) Gaussian pairing on `ℝ^{2w}`: `Φ(1/λ) = -λ^w Φ(λ)`,
   `Φ(λ) = ∫₀^∞ g t^{w-1} e^{-2πλt} dt`.
3. (`mellin_laplacePairW_eq`) Fubini on `0 < Re z < w`:
   `∫₀^∞ λ^{w-z-1} Φ(λ) dλ = (2π)^{z-w} Γ(w - z) Mg(z)`.
4. (`mellinMGW_reflection`) the substitution `λ → 1/λ` gives `m_g(w - z) = -m_g(z)` on
   `0 < Re z < w`.
5. (`mellinMGEntireW`, `lemma_S1_W`) gluing `m_g(z)` on `Re z > 0` with `-m_g(w - z)` on `Re z < w`
   gives an entire function with `F(w - z) = -F(z)` on `ℂ`.

The weight `w` replaces `1` of the spinless case: the reflection is `z ↦ w - z`, the Gaussian Fourier
transform lives on `ℝ^{2w}`.  The hypotheses on `a` are `S ≤ a` and `0 < a` (the latter is automatic for
`Q ≢ 1`), which give `V ≥ c t^{n}` for every `n`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing

/-! ### Section 1: Scaled Gamma integrals -/

private lemma gamma_integral_scaled_complex {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ))) (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)) =
        Complex.Gamma s * (r : ℂ) ^ (-s) := by
  have hint0 : IntegrableOn (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) (Ioi 0) :=
    Complex.GammaIntegral_convergent hs
  have hint_comp : IntegrableOn (fun lam : ℝ => (((-(r * lam)).exp : ℝ) : ℂ) *
      ((r * lam : ℝ) : ℂ) ^ (s - 1)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) 0 hr).mpr
      (by simpa using hint0)
  have hfac_ne : (r : ℂ) ^ (s - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
  have hint : IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)))
      (Ioi 0) := by
    have hmul_int : IntegrableOn (fun lam : ℝ => ((r : ℂ) ^ (s - 1))⁻¹ *
        ((((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1))) (Ioi 0) :=
      hint_comp.const_mul _
    refine hmul_int.congr_fun (fun lam hlam => ?_) measurableSet_Ioi
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (mem_Ioi.mp hlam).le,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    have hmul : (-(lam : ℂ) * (r : ℂ)) = -((r : ℂ) * (lam : ℂ)) := by ring
    rw [hmul]
    calc ((r : ℂ) ^ (s - 1))⁻¹ * (Complex.exp (-((r : ℂ) * (lam : ℂ))) *
            ((r : ℂ) ^ (s - 1) * (lam : ℂ) ^ (s - 1)))
        = (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ) ^ (s - 1)) *
            ((lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))) := by ring
      _ = (lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ))) := by
          rw [inv_mul_cancel₀ hfac_ne, one_mul]
  refine ⟨hint, ?_⟩
  have hcomp_val : ∫ lam in Ioi (0 : ℝ),
      (((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1) =
      (r : ℂ)⁻¹ * Complex.Gamma s := by
    have h1 := integral_comp_mul_left_Ioi (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) 0 hr
    rw [mul_zero] at h1
    change ∫ lam in Ioi (0 : ℝ), (((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1) =
      r⁻¹ • ∫ u in Ioi (0 : ℝ), ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1) at h1
    rw [h1, Complex.real_smul, Complex.ofReal_inv, ← Complex.GammaIntegral,
      ← Complex.Gamma_eq_integral hs]
  have heq : EqOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)))
      (fun lam : ℝ => ((r : ℂ) ^ (s - 1))⁻¹ *
        ((((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1))) (Ioi 0) := by
    intro lam hlam
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (mem_Ioi.mp hlam).le,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    have hmul : (-(lam : ℂ) * (r : ℂ)) = -((r : ℂ) * (lam : ℂ)) := by ring
    rw [hmul]
    calc (lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))
        = (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ) ^ (s - 1)) *
            ((lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))) := by
          rw [inv_mul_cancel₀ hfac_ne, one_mul]
      _ = ((r : ℂ) ^ (s - 1))⁻¹ * (Complex.exp (-((r : ℂ) * (lam : ℂ))) *
            ((r : ℂ) ^ (s - 1) * (lam : ℂ) ^ (s - 1))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hcomp_val]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpow_neg : ((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ)⁻¹ = (r : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hrc]
    congr 1; ring
  calc ((r : ℂ) ^ (s - 1))⁻¹ * ((r : ℂ)⁻¹ * Complex.Gamma s)
      = Complex.Gamma s * (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ)⁻¹) := by ring
    _ = Complex.Gamma s * (r : ℂ) ^ (-s) := by rw [hpow_neg]

private lemma gamma_integral_scaled_real {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-lam * r)) (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), lam ^ (s - 1) * Real.exp (-lam * r) =
        Real.Gamma s * r ^ (-s) := by
  have heq : (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-lam * r)) =
      fun lam : ℝ => lam ^ (s - 1) * Real.exp (-(r * lam)) := by
    ext lam; ring_nf
  rw [heq]
  have hint0 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (s - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hs
  have hint_comp : IntegrableOn (fun lam : ℝ => Real.exp (-(r * lam)) * (r * lam) ^ (s - 1))
      (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u) * u ^ (s - 1)) 0 hr).mpr
      (by simpa using hint0)
  have hint : IntegrableOn (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-(r * lam))) (Ioi 0) := by
    have hmul_int : IntegrableOn (fun lam : ℝ => (r ^ (s - 1))⁻¹ *
        (Real.exp (-(r * lam)) * (r * lam) ^ (s - 1))) (Ioi 0) :=
      hint_comp.const_mul _
    refine hmul_int.congr_fun (fun lam hlam => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.mul_rpow hr.le (mem_Ioi.mp hlam).le]
    have hne : r ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp [hne]
  refine ⟨hint, ?_⟩
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, Real.rpow_neg hr.le, one_div,
    ← Real.inv_rpow hr.le, mul_comm]

/-! ### Section 2: Mellin–Laplace Fubini identity on `0 < Re z < w` -/

/-- `Φ` is integrable against `t^{w-1}`-weighted integrand for every `λ ≥ 0`. -/
private lemma integrableOn_pairing {w : ℕ} {g : ℝ → ℝ} (hlift : Integrable (radialLift w g))
    (hw : 1 ≤ w) (hcont : ContinuousOn g (Ici 0)) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t)) (Ioi 0) := by
  have hA : IntegrableOn (fun t : ℝ => t ^ (w - 1) * g t) (Ioi 0) :=
    (integrable_radialLift_iff hw g).1 hlift
  refine hA.norm.mono' ?_ ?_
  · have hcont_g : ContinuousOn (fun t : ℝ => g t) (Ioi 0) := hcont.mono Ioi_subset_Ici_self
    have hcont_e : Continuous (fun t : ℝ => Real.exp (-2 * π * lam * t)) := by fun_prop
    exact ((hcont_g.mul (continuousOn_id.pow (w - 1))).mul
      hcont_e.continuousOn).aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := mem_Ioi.mp ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg ht0.le _), Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg ht0.le _)]
    have hexp1 : Real.exp (-2 * π * lam * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have harg_nn : 0 ≤ 2 * π * lam * t := by positivity
      linarith
    calc |g t| * t ^ (w - 1) * Real.exp (-2 * π * lam * t) ≤ |g t| * t ^ (w - 1) * 1 := by
          gcongr
      _ = t ^ (w - 1) * |g t| := by ring

private lemma mellin_laplace_integrand_eq (w : ℕ) (g : ℝ → ℝ) (s : ℂ) (lam t : ℝ) :
    (lam : ℂ) ^ (s - 1) * (((g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t)) : ℝ) : ℂ) =
      (((g t * t ^ (w - 1) : ℝ)) : ℂ) * ((lam : ℂ) ^ (s - 1) *
        Complex.exp (-(lam : ℂ) * ((2 * π * t : ℝ) : ℂ))) := by
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  have hexp : (-2 * π * lam * t : ℝ) = -(lam * (2 * π * t)) := by ring
  rw [hexp]
  push_cast; ring_nf

/-- **Mellin–Laplace Fubini identity** (`vlo:S1` proof): for `0 < Re z < w`, the function
`λ ↦ λ^{w-z-1} Φ(λ)` is integrable on `(0, ∞)` and its integral equals
`(2π)^{z-w} Γ(w - z) Mg(z)`. -/
theorem mellin_laplacePairW_eq {w : ℕ} (hw : 1 ≤ w) {g V : ℝ → ℝ}
    (hcont : ContinuousOn g (Ici 0)) (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0))
    (hdom : PolyDom V) (hlift : Integrable (radialLift w g)) {z : ℂ}
    (hz0 : 0 < z.re) (hzw : z.re < w) :
    IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ ((w : ℂ) - z - 1) * (laplacePairW w g lam : ℂ))
        (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ ((w : ℂ) - z - 1) * (laplacePairW w g lam : ℂ) =
        (2 * (Real.pi : ℂ)) ^ (z - w) * Complex.Gamma ((w : ℂ) - z) * mellinTransformW g z := by
  set s : ℂ := (w : ℂ) - z with hs_def
  have hs_re : 0 < s.re := by simp [hs_def, hzw]
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let H : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (s - 1) * (((g p.2 * p.2 ^ (w - 1) * Real.exp (-2 * π * p.1 * p.2)) : ℝ) : ℂ)
  have hH_meas : AEStronglyMeasurable H (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) by
      dsimp [μ]; rw [Measure.prod_restrict, ← Measure.volume_eq_prod]]
    have hcont_pow : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 1)) (Ioi 0 ×ˢ Ioi 0) := by
      intro p hp
      have hp1 : (p.1 : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hp.1))
      exact ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.cpow
        continuousAt_const hp1).continuousWithinAt
    have hcont_g : ContinuousOn (fun p : ℝ × ℝ => g p.2 * p.2 ^ (w - 1)) (Ioi 0 ×ˢ Ioi 0) := by
      refine ContinuousOn.mul ?_ (by fun_prop)
      exact hcont.comp continuous_snd.continuousOn fun p hp => (mem_Ioi.mp hp.2).le
    have hcont_gt : ContinuousOn (fun p : ℝ × ℝ =>
        (((g p.2 * p.2 ^ (w - 1) * Real.exp (-2 * π * p.1 * p.2)) : ℝ) : ℂ)) (Ioi 0 ×ˢ Ioi 0) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact hcont_g.mul (by fun_prop)
    exact (hcont_pow.mul hcont_gt).aestronglyMeasurable
      (isOpen_Ioi.prod isOpen_Ioi).measurableSet
  have hinner_int : ∀ t ∈ Ioi (0 : ℝ),
      Integrable (fun lam : ℝ => H (lam, t)) μ := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have h2pit : 0 < 2 * π * t := by positivity
    have hgam : IntegrableOn (fun lam : ℝ => (((g t * t ^ (w - 1) : ℝ)) : ℂ) *
        ((lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * ((2 * π * t : ℝ) : ℂ))))
        (Ioi 0) :=
      (gamma_integral_scaled_complex hs_re h2pit).1.const_mul _
    have heq : EqOn (fun lam : ℝ => (((g t * t ^ (w - 1) : ℝ)) : ℂ) *
          ((lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * ((2 * π * t : ℝ) : ℂ))))
        (fun lam : ℝ => H (lam, t)) (Ioi 0) :=
      fun lam _ => (mellin_laplace_integrand_eq w g s lam t).symm
    exact hgam.congr_fun heq measurableSet_Ioi
  have houter_int : Integrable (fun t : ℝ => ∫ lam : ℝ, ‖H (lam, t)‖ ∂μ) μ := by
    have hnorm_eq : EqOn (fun t : ℝ => ∫ lam : ℝ, ‖H (lam, t)‖ ∂μ)
        (fun t : ℝ => (Real.Gamma (w - z.re) * (2 * π) ^ (z.re - w)) *
          (|g t| * t ^ (z.re - 1))) (Ioi 0) := by
      intro t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      have h2pit : 0 < 2 * π * t := by positivity
      have hlam_eq : EqOn (fun lam : ℝ => ‖H (lam, t)‖)
          (fun lam : ℝ => |g t| * t ^ (w - 1) *
            (lam ^ ((w - z.re) - 1) * Real.exp (-lam * (2 * π * t)))) (Ioi 0) := by
        intro lam hlam
        have hlam0 : 0 < lam := mem_Ioi.mp hlam
        dsimp [H]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hlam0, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (pow_nonneg ht0.le _)]
        have he1 : (s - 1).re = (w - z.re) - 1 := by simp [hs_def]
        have he2 : -2 * π * lam * t = -lam * (2 * π * t) := by ring
        rw [he1, he2]; ring
      change ∫ lam in Ioi (0 : ℝ), ‖H (lam, t)‖ = _
      have hgam_r := (gamma_integral_scaled_real
        (by linarith : 0 < (w : ℝ) - z.re) h2pit).2
      rw [setIntegral_congr_fun measurableSet_Ioi hlam_eq, integral_const_mul, hgam_r]
      have hmul_rpow : (2 * π * t) ^ (-((w : ℝ) - z.re)) =
          (2 * π) ^ (z.re - w) * t ^ (z.re - w) := by
        rw [Real.mul_rpow (by positivity) ht0.le]
        have he : -((w : ℝ) - z.re) = z.re - w := by ring
        rw [he]
      have htpow : t ^ (w - 1) * t ^ (z.re - w) = t ^ (z.re - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
        congr 1
        rw [Nat.cast_sub hw, Nat.cast_one]; ring
      rw [hmul_rpow]
      calc |g t| * t ^ (w - 1) *
            (Real.Gamma (↑w - z.re) * ((2 * π) ^ (z.re - ↑w) * t ^ (z.re - ↑w)))
          = (Real.Gamma (w - z.re) * (2 * π) ^ (z.re - w)) *
            (|g t| * (t ^ (w - 1) * t ^ (z.re - w))) := by ring
        _ = _ := by rw [htpow]
    have hmg : IntegrableOn (fun t : ℝ =>
        (Real.Gamma (w - z.re) * (2 * π) ^ (z.re - w)) * (|g t| * t ^ (z.re - 1))) (Ioi 0) :=
      (integrableOn_abs_mellinW hcont hint hdom hz0).const_mul _
    exact hmg.congr_fun hnorm_eq.symm measurableSet_Ioi
  have hH_prod : Integrable H (μ.prod μ) := by
    rw [integrable_prod_iff' hH_meas]
    refine ⟨?_, houter_int⟩
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall hinner_int
  have hleft_int : IntegrableOn (fun lam : ℝ => ∫ t : ℝ, H (lam, t) ∂μ) (Ioi 0) :=
    hH_prod.integral_prod_left
  have hleft_eq : EqOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * (laplacePairW w g lam : ℂ))
      (fun lam : ℝ => ∫ t : ℝ, H (lam, t) ∂μ) (Ioi 0) := by
    intro lam hlam
    have hlam0 : 0 < lam := mem_Ioi.mp hlam
    have hcast : ((∫ t in Ioi (0 : ℝ), g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t) : ℝ) : ℂ) =
        ∫ t in Ioi (0 : ℝ), (((g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t) : ℝ)) : ℂ) := by
      simpa using (Complex.ofRealCLM.integral_comp_comm
        (integrableOn_pairing hlift hw hcont hlam0)).symm
    dsimp [H, laplacePairW, μ]
    rw [hcast]
    change (lam : ℂ) ^ (s - 1) *
        ∫ t in Ioi (0 : ℝ), (((g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t) : ℝ)) : ℂ) =
      ∫ t in Ioi (0 : ℝ), (lam : ℂ) ^ (s - 1) *
        (((g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t) : ℝ)) : ℂ)
    rw [← integral_const_mul]
  have hs_eq : (w : ℂ) - z - 1 = s - 1 := by rw [hs_def]
  rw [hs_eq]
  refine ⟨hleft_int.congr_fun hleft_eq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hleft_eq]
  change ∫ lam : ℝ, (∫ t : ℝ, H (lam, t) ∂μ) ∂μ = _
  rw [integral_integral_swap hH_prod]
  have hinner_val : EqOn (fun t : ℝ => ∫ lam : ℝ, H (lam, t) ∂μ)
      (fun t : ℝ => (2 * (Real.pi : ℂ)) ^ (z - w) * Complex.Gamma s *
        ((g t : ℂ) * (t : ℂ) ^ (z - 1))) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have h2pit : 0 < 2 * π * t := by positivity
    have heq : EqOn (fun lam : ℝ => H (lam, t))
        (fun lam : ℝ => (((g t * t ^ (w - 1) : ℝ)) : ℂ) * ((lam : ℂ) ^ (s - 1) *
          Complex.exp (-(lam : ℂ) * ((2 * π * t : ℝ) : ℂ)))) (Ioi 0) :=
      fun lam _ => mellin_laplace_integrand_eq w g s lam t
    change ∫ lam in Ioi (0 : ℝ), H (lam, t) = _
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      (gamma_integral_scaled_complex hs_re h2pit).2]
    have hcpow_split : ((2 * π * t : ℝ) : ℂ) ^ (-s) =
        (2 * (Real.pi : ℂ)) ^ (z - w) * (t : ℂ) ^ (z - w) := by
      have hneg : -s = z - w := by rw [hs_def]; ring
      rw [hneg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) ht0.le]
      push_cast; rfl
    have htw : (t : ℂ) ^ (w - 1) * (t : ℂ) ^ (z - w) = (t : ℂ) ^ (z - 1) := by
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ htc]
      congr 1
      rw [Nat.cast_sub hw, Nat.cast_one]; ring
    rw [hcpow_split]
    push_cast
    calc ((g t : ℂ) * (t : ℂ) ^ (w - 1)) *
          (Complex.Gamma s * ((2 * (Real.pi : ℂ)) ^ (z - w) * (t : ℂ) ^ (z - w)))
        = (2 * (Real.pi : ℂ)) ^ (z - w) * Complex.Gamma s *
          ((g t : ℂ) * ((t : ℂ) ^ (w - 1) * (t : ℂ) ^ (z - w))) := by ring
      _ = _ := by rw [htw]
  change ∫ t in Ioi (0 : ℝ), (∫ lam : ℝ, H (lam, t) ∂μ) = _
  rw [setIntegral_congr_fun measurableSet_Ioi hinner_val, integral_const_mul]
  unfold mellinTransformW
  rfl

/-! ### Section 3: Reflection `m_g(w - z) = -m_g(z)` on `0 < Re z < w` -/

/-- **Reflection identity for `m_g` on `0 < Re z < w`** (`vlo:S1`). -/
theorem mellinMGW_reflection {w : ℕ} (hw : 1 ≤ w) {g V : ℝ → ℝ}
    (hcont : ContinuousOn g (Ici 0)) (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0))
    (hdom : PolyDom V) (hlift : Integrable (radialLift w g))
    (hodd : 𝓕 (radialLift w g) = -(radialLift w g)) {z : ℂ}
    (hz0 : 0 < z.re) (hzw : z.re < w) :
    mellinMGW g ((w : ℂ) - z) = -mellinMGW g z := by
  have hz1_re0 : 0 < ((w : ℂ) - z).re := by simp [hzw]
  have hz1_rew : ((w : ℂ) - z).re < w := by simp [hz0]
  have hz_lhs := (mellin_laplacePairW_eq hw hcont hint hdom hlift hz0 hzw).2
  have hz_rhs := (mellin_laplacePairW_eq hw hcont hint hdom hlift hz1_re0 hz1_rew).2
  rw [sub_sub_cancel] at hz_rhs
  have himg : (fun u : ℝ => u⁻¹) '' Ioi 0 = Ioi 0 := by
    ext lam; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact inv_pos.mpr hu
    · intro hlam; exact ⟨lam⁻¹, inv_pos.mpr hlam, inv_inv lam⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := fun u : ℝ => u⁻¹)
    (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi
    (fun u hu => (hasDerivAt_inv (mem_Ioi.mp hu).ne').hasDerivWithinAt)
    (fun u₁ _ u₂ _ h => inv_injective h)
    (fun lam : ℝ => (lam : ℂ) ^ ((w : ℂ) - z - 1) * (laplacePairW w g lam : ℂ))
  rw [himg] at hcov
  have hcov_eq : ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ ((w : ℂ) - z - 1) * (laplacePairW w g lam : ℂ) =
      -∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * (laplacePairW w g u : ℂ) := by
    rw [hcov, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := mem_Ioi.mp hu
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    rw [abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu0)), Complex.real_smul,
      laplacePairW_inv hw hlift hodd hu0]
    have hpow1 : ((u⁻¹ : ℝ) : ℂ) ^ ((w : ℂ) - z - 1) = (u : ℂ) ^ (-((w : ℂ) - z - 1)) := by
      have harg : (u : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hu0.le]
        exact Real.pi_pos.ne
      rw [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow (u : ℂ) _ harg]
    have hkey : (((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ (-((w : ℂ) - z - 1)) * ((u ^ w : ℝ) : ℂ) =
        (u : ℂ) ^ (z - 1) := by
      have hu2 : (((u ^ 2)⁻¹ : ℝ) : ℂ) = (u : ℂ) ^ (-2 : ℂ) := by
        rw [Complex.ofReal_inv, Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg]
        norm_num
      have huw : ((u ^ w : ℝ) : ℂ) = (u : ℂ) ^ (w : ℂ) := by
        rw [Complex.ofReal_pow, ← Complex.cpow_natCast]
      rw [hu2, huw, ← Complex.cpow_add _ _ huc, ← Complex.cpow_add _ _ huc]
      congr 1; ring
    rw [hpow1]
    calc _ = -((((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ (-((w : ℂ) - z - 1)) * ((u ^ w : ℝ) : ℂ)) *
            (laplacePairW w g u : ℂ) := by push_cast; ring
      _ = -((u : ℂ) ^ (z - 1) * (laplacePairW w g u : ℂ)) := by rw [hkey]; ring
  have hid : (2 * (Real.pi : ℂ)) ^ (z - w) * Complex.Gamma ((w : ℂ) - z) * mellinTransformW g z =
      -((2 * (Real.pi : ℂ)) ^ ((w : ℂ) - z - w) * Complex.Gamma z *
        mellinTransformW g ((w : ℂ) - z)) := by
    rw [← hz_lhs, ← hz_rhs, hcov_eq]
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hgwz : Complex.Gamma ((w : ℂ) - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz1_re0
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hpw : (2 * (Real.pi : ℂ)) ^ (w : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2pi_ne)
  have hp1 : (2 * (Real.pi : ℂ)) ^ (z - w) * (2 * (Real.pi : ℂ)) ^ (w : ℂ) =
      (2 * (Real.pi : ℂ)) ^ z := by
    rw [← Complex.cpow_add _ _ h2pi_ne]; congr 1; ring
  have hp2 : (2 * (Real.pi : ℂ)) ^ ((w : ℂ) - z - w) * (2 * (Real.pi : ℂ)) ^ (w : ℂ) =
      (2 * (Real.pi : ℂ)) ^ ((w : ℂ) - z) := by
    rw [← Complex.cpow_add _ _ h2pi_ne]; congr 1; ring
  have hid2 : (2 * (Real.pi : ℂ)) ^ z * Complex.Gamma ((w : ℂ) - z) * mellinTransformW g z =
      -((2 * (Real.pi : ℂ)) ^ ((w : ℂ) - z) * Complex.Gamma z *
        mellinTransformW g ((w : ℂ) - z)) := by
    rw [← hp1, ← hp2]
    linear_combination (2 * (Real.pi : ℂ)) ^ (w : ℂ) * hid
  unfold mellinMGW
  rw [eq_neg_iff_add_eq_zero]
  field_simp [hgz, hgwz]
  linear_combination hid2

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.mellinMGW_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.mellinMGW_reflection

/-! ### Section 4: Entire extension `mellinMGEntireW` and Lemma S1 -/

/-- Glued entire extension of `m_g(z) = (2π)^z Mg(z) / Γ(z)` to all of `ℂ` (`vlo:S1`):
`m_g(z)` on `Re z > 0` and `-m_g(w - z)` otherwise. -/
noncomputable def mellinMGEntireW (w : ℕ) (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  if 0 < z.re then mellinMGW g z else -mellinMGW g ((w : ℂ) - z)

theorem mellinMGEntireW_of_re_pos (w : ℕ) (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.re) :
    mellinMGEntireW w g z = mellinMGW g z := by
  simp [mellinMGEntireW, hz]

section Glue

variable {w : ℕ} {g V : ℝ → ℝ}

theorem mellinMGEntireW_sub (hw : 1 ≤ w) (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V)
    (hlift : Integrable (radialLift w g)) (hodd : 𝓕 (radialLift w g) = -(radialLift w g))
    (z : ℂ) :
    mellinMGEntireW w g ((w : ℂ) - z) = -mellinMGEntireW w g z := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  unfold mellinMGEntireW
  by_cases hz0 : 0 < z.re
  · by_cases hz1 : 0 < ((w : ℂ) - z).re
    · simp only [hz0, hz1, ↓reduceIte]
      exact mellinMGW_reflection hw hcont hint hdom hlift hodd hz0 (by simpa using hz1)
    · simp only [hz0, hz1, ↓reduceIte, sub_sub_cancel]
  · have hz1 : 0 < ((w : ℂ) - z).re := by
      simp only [Complex.sub_re, Complex.natCast_re]; linarith [not_lt.mp hz0]
    simp only [hz0, hz1, ↓reduceIte, neg_neg]

theorem differentiable_mellinMGEntireW (hw : 1 ≤ w) (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V)
    (hlift : Integrable (radialLift w g)) (hodd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    Differentiable ℂ (mellinMGEntireW w g) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hdiff_pos : DifferentiableOn ℂ (mellinMGW g) {z : ℂ | 0 < z.re} :=
    differentiableOn_mellinMGW hcont hint hdom
  have hopen_pos : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  intro z
  by_cases hz0 : 0 < z.re
  · have hda : DifferentiableAt ℂ (mellinMGW g) z :=
      (hdiff_pos z hz0).differentiableAt (hopen_pos.mem_nhds hz0)
    refine hda.congr_of_eventuallyEq ?_
    filter_upwards [hopen_pos.mem_nhds hz0] with u hu
    exact mellinMGEntireW_of_re_pos w g hu
  · have hz1 : z.re < w := by linarith [not_lt.mp hz0]
    have hopen : IsOpen {u : ℂ | u.re < w} := isOpen_lt Complex.continuous_re continuous_const
    have h1z_pos : 0 < ((w : ℂ) - z).re := by simp [hz1]
    have hda : DifferentiableAt ℂ (fun u : ℂ => -mellinMGW g ((w : ℂ) - u)) z := by
      have h1 : DifferentiableAt ℂ (mellinMGW g) ((w : ℂ) - z) :=
        (hdiff_pos _ h1z_pos).differentiableAt (hopen_pos.mem_nhds h1z_pos)
      exact (h1.comp z ((differentiableAt_const (w : ℂ)).sub differentiableAt_id)).neg
    refine hda.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hz1] with u hu
    by_cases hu0 : 0 < u.re
    · rw [mellinMGEntireW_of_re_pos w g hu0,
        mellinMGW_reflection hw hcont hint hdom hlift hodd hu0 hu, neg_neg]
    · unfold mellinMGEntireW
      simp only [hu0, ↓reduceIte]

end Glue

/-- **Lemma S1 at weight `w`** (`lower_o1_two_edge.tex`, §J2, `vlo:S1`): for a fixed-weight problem
`prob` (weight `w = prob.w ≥ 1`, any `Q`), `S ≤ a`, `0 < a` and `g ∈ TestClass prob a`, the function
`m_g(z) = (2π)^z Mg(z)/Γ(z)` extends to an entire `F : ℂ → ℂ` with `F (w - z) = -F z` on `ℂ`.
The reflection is `z ↦ w - z` (not `1 - z`); at `w = 1` it is the spinless statement. -/
theorem lemma_S1_W (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a) (ha0 : 0 < a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * mellinTransformW g z / Complex.Gamma z) ∧
      ∀ z : ℂ, F ((prob.w : ℂ) - z) = -F z :=
  ⟨mellinMGEntireW prob.w g,
    differentiable_mellinMGEntireW prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob ha ha0)
      hg.int_lift hg.fourier_odd,
    fun _ hz => mellinMGEntireW_of_re_pos prob.w g hz,
    mellinMGEntireW_sub prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob ha ha0)
      hg.int_lift hg.fourier_odd⟩

/-- **Lemma S1 at weight `w`, `c'` form**: for `c₀ ≤ c'` with `12 S ≤ c'` and `0 < c'`,
`g ∈ TestClass prob (c' / 12)` gives the entire antisymmetric `m_g`. -/
theorem lemma_S1_W_of_c' (prob : FixedWeightProblem) {c' : ℝ} (hc : prob.totalShift * 12 ≤ c')
    (hc0 : 0 < c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * mellinTransformW g z / Complex.Gamma z) ∧
      ∀ z : ℂ, F ((prob.w : ℂ) - z) = -F z :=
  lemma_S1_W prob (by linarith) (by linarith) hg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W_of_c'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S1_W_of_c'

end FormalResearch.ModularBootstrap.FixedWeightBand

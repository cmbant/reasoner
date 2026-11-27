module

public import FormalResearch.ModularBootstrap.Spin.SpinS4Rc2Bound
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_2

/-!
# SPIN-S4 Calibrated Adjoint Identities (`s4:eP.0`, `s4:eR.6`)

Proves:
1. `spinHbCalReal`, `spinHbCal_ofReal`, `spinGcal_re_ofReal`.
2. Exact kernel factorisations `spinHbCalReal_eq_spinRc1` (`|d| ≤ b`) and `spinHbCalReal_eq_spinRc2` (`|b| ≤ d`).
3. `spinCal_adjoint_identity`: unified `(s4:eP.0)` and `(s4:eR.6)` calibrated adjoint identity.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

/-! ### Calibrated real kernel factorisation -/

noncomputable def spinCalFac (b : ℝ) : ℝ :=
  Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2)

noncomputable def spinHbCalReal (b d : ℝ) : ℝ :=
  (1 + xiStar ^ 2) / (1 + b ^ 2) *
    (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
    (Real.tanh (xiStar / 2) ^ 4) *
    Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) * spinCalFac b

lemma spinHbCalReal_nonneg (b d : ℝ) : 0 ≤ spinHbCalReal b d := by
  unfold spinHbCalReal spinCalFac
  positivity

lemma spinHbCalReal_neg (b d : ℝ) : spinHbCalReal (-b) (-d) = spinHbCalReal b d := by
  unfold spinHbCalReal spinCalFac
  have h1 : (-b + -d) / 2 = -((b + d) / 2) := by ring
  have h2 : (-b - -d) / 2 = -((b - d) / 2) := by ring
  rw [h1, h2, Real.tanh_neg, Real.tanh_neg, neg_sq, neg_sq, neg_sq, neg_sq]

lemma spinHbCal_ofReal (b : ℝ) (d : ℝ) :
    spinHbCal (b : ℂ) d = ((spinHbCalReal b d : ℝ) : ℂ) := by
  unfold spinHbCal spinHb spinHbCalReal
  have htanh : ∀ r : ℝ, Complex.tanh (r : ℂ) = ((Real.tanh r : ℝ) : ℂ) := fun r => by
    rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    push_cast; rfl
  have h1 : (((b : ℂ) + (d : ℂ)) / 2) = (((b + d) / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (((b : ℂ) - (d : ℂ)) / 2) = (((b - d) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hexp : Complex.exp
      (-((spinAlpha1 : ℂ) * ((b : ℂ) ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) / (2 * (xiStar : ℂ))) -
        ((b : ℂ) ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) ^ 2) = ((spinCalFac b : ℝ) : ℂ) := by
    unfold spinCalFac
    have he : -((spinAlpha1 : ℂ) * ((b : ℂ) ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) / (2 * (xiStar : ℂ))) -
        ((b : ℂ) ^ 2 - ((xiStar ^ 2 : ℝ) : ℂ)) ^ 2 =
        (((-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [he, ← Complex.ofReal_exp]
  rw [h1, h2, htanh, htanh, hexp]
  push_cast; ring

lemma spinGcal_re_ofReal {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (b : ℝ) :
    (spinGcal a Φ (b : ℂ)).re =
      4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * spinG a Φ (b + d) (b - d) := by
  unfold spinGcal
  have hreal_int : ∀ d : ℝ,
      spinHbCal (b : ℂ) d * spinGC a Φ ((b : ℂ) + (d : ℂ)) ((b : ℂ) - (d : ℂ)) =
        ((spinHbCalReal b d * spinG a Φ (b + d) (b - d) : ℝ) : ℂ) := fun d => by
    have hL : (b : ℂ) + (d : ℂ) = ((b + d : ℝ) : ℂ) := by push_cast; rfl
    have hR : (b : ℂ) - (d : ℂ) = ((b - d : ℝ) : ℂ) := by push_cast; rfl
    rw [spinHbCal_ofReal, hL, hR, spinGC_ofReal_eq_spinG ha hΦ]
    push_cast; ring
  simp_rw [hreal_int, ← Complex.coe_algebraMap, integral_ofReal]
  simp only [Complex.coe_algebraMap]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

private lemma spinHbCalReal_eq_spinRc1 {a b d : ℝ} (ha : 2 < a) (hb : |d| ≤ b) :
    4 * spinCalF xiStar ^ 2 * (a * Real.exp (12 * a * spinL b) * spinHbCalReal b d) =
      4 * spinRc1 a b d * spinWc a (b + d) * spinWc a (b - d) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := (abs_nonneg d).trans hb
  have hxp : 0 ≤ b + d := by linarith [abs_le.mp hb]
  have hxm : 0 ≤ b - d := by linarith [abs_le.mp hb]
  rcases eq_or_lt_of_le hxp with hxp0 | hxp_pos
  · have hzero : spinWc a (b + d) = 0 := by rw [← hxp0, spinWc_zero]
    have hbd0 : (b + d) / 2 = 0 := by linarith
    unfold spinHbCalReal
    rw [hbd0, Real.tanh_zero, hzero]; ring
  · rcases eq_or_lt_of_le hxm with hxm0 | hxm_pos
    · have hzero : spinWc a (b - d) = 0 := by rw [← hxm0, spinWc_zero]
      have hbd0 : (b - d) / 2 = 0 := by linarith
      unfold spinHbCalReal
      rw [hbd0, Real.tanh_zero, hzero]; ring
    · have hfp_pos : 0 < spinCalFc a (b + d) := spinCalFc_pos_of_pos ha hxp_pos
      have hfm_pos : 0 < spinCalFc a (b - d) := spinCalFc_pos_of_pos ha hxm_pos
      have hwL : spinWc a (b + d) = Real.sqrt a * Real.exp (4 * π * a * (b + d)) * spinCalFc a (b + d) := by
        rw [spinWc_factorization ha.le, abs_of_pos hxp_pos]
      have hwR : spinWc a (b - d) = Real.sqrt a * Real.exp (4 * π * a * (b - d)) * spinCalFc a (b - d) := by
        rw [spinWc_factorization ha.le, abs_of_pos hxm_pos]
      have hphip : spinCalPhic a (b + d) * spinCalFc a (b + d) = Real.tanh ((b + d) / 2) ^ 2 := by
        unfold spinCalPhic; simp only [hxp_pos.ne', ↓reduceIte]; exact div_mul_cancel₀ _ hfp_pos.ne'
      have hphim : spinCalPhic a (b - d) * spinCalFc a (b - d) = Real.tanh ((b - d) / 2) ^ 2 := by
        unfold spinCalPhic; simp only [hxm_pos.ne', ↓reduceIte]; exact div_mul_cancel₀ _ hfm_pos.ne'
      have hexp : Real.exp (12 * a * spinL b) =
          Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d)) := by
        rw [← Real.exp_add]; unfold spinL; rw [abs_of_nonneg hb0]; congr 1; ring
      have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
      have ht_xs : Real.tanh (xiStar / 2) ^ 4 ≠ 0 :=
        pow_ne_zero 4 (spinTanh_pos (half_pos xiStar_pos)).ne'
      have hcal_ratio : 4 * spinCalF xiStar ^ 2 / Real.tanh (xiStar / 2) ^ 4 =
          4 / spinCalPhi xiStar ^ 2 := by
        unfold spinCalPhi; field_simp [ht_xs, (spinCalF_pos' xiStar_pos).ne']
      unfold spinRc1 spinHbCalReal spinCalFac
      rw [hwL, hwR, hexp]
      have hL_rew : 4 * spinCalF xiStar ^ 2 *
            (a * (Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d))) *
              ((1 + xiStar ^ 2) / (1 + b ^ 2) * (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
                Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2))) =
          (4 * spinCalF xiStar ^ 2 / Real.tanh (xiStar / 2) ^ 4) *
            ((1 + xiStar ^ 2) / (1 + b ^ 2) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
              Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2) *
              a * (Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d))) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2)) := by ring
      rw [hL_rew, hcal_ratio]
      symm
      calc ((1 + xiStar ^ 2) / (1 + b ^ 2) * (spinCalPhic a (b + d) * spinCalPhic a (b - d) / spinCalPhi xiStar ^ 2) *
              Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (b ^ 2 - xiStar ^ 2) ^ 2)) *
              (Real.sqrt a * Real.exp (4 * π * a * (b + d)) * spinCalFc a (b + d)) *
              (Real.sqrt a * Real.exp (4 * π * a * (b - d)) * spinCalFc a (b - d))
          = ((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2) +
                (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2))) *
              (Real.sqrt a * Real.sqrt a) *
              (Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d))) *
              ((spinCalPhic a (b + d) * spinCalFc a (b + d)) *
               (spinCalPhic a (b - d) * spinCalFc a (b - d))) := by ring
        _ = ((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2)) *
              a *
              (Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d))) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) := by
              rw [Real.exp_add, hsqa, hphip, hphim]
      calc 4 * ((1 + xiStar ^ 2) / (1 + b ^ 2) *
              (spinCalPhic a (b + d) * spinCalPhic a (b - d) / spinCalPhi xiStar ^ 2) *
              Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (b ^ 2 - xiStar ^ 2) ^ 2)) *
            (Real.sqrt a * Real.exp (4 * π * a * (b + d)) * spinCalFc a (b + d)) *
            (Real.sqrt a * Real.exp (4 * π * a * (b - d)) * spinCalFc a (b - d))
          = 4 * (((1 + xiStar ^ 2) / (1 + b ^ 2) *
                (spinCalPhic a (b + d) * spinCalPhic a (b - d) / spinCalPhi xiStar ^ 2) *
                Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                  (b ^ 2 - xiStar ^ 2) ^ 2)) *
              (Real.sqrt a * Real.exp (4 * π * a * (b + d)) * spinCalFc a (b + d)) *
              (Real.sqrt a * Real.exp (4 * π * a * (b - d)) * spinCalFc a (b - d))) := by ring
        _ = 4 * (((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2)) *
              a *
              (Real.exp (4 * π * a * (b + d)) * Real.exp (4 * π * a * (b - d))) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2)) := by rw [hR]
        _ = _ := by ring

private lemma spinHbCalReal_eq_spinRc2 {a b d : ℝ} (ha : 2 < a) (hd : |b| ≤ d) :
    4 * spinCalF xiStar ^ 2 * (a * Real.exp (12 * a * spinL b) * spinHbCalReal b d) =
      4 * spinRc2 a d b * spinWc a (b + d) * spinWc a (b - d) := by
  have ha0 : 0 < a := by linarith
  have hxp : 0 ≤ d + b := by linarith [abs_le.mp hd]
  have hxm : 0 ≤ d - b := by linarith [abs_le.mp hd]
  rcases eq_or_lt_of_le hxp with hxp0 | hxp_pos
  · have hzero : spinWc a (b + d) = 0 := by rw [show b + d = 0 by linarith, spinWc_zero]
    have hbd0 : (b + d) / 2 = 0 := by linarith
    unfold spinHbCalReal; rw [hbd0, Real.tanh_zero, hzero]; ring
  · rcases eq_or_lt_of_le hxm with hxm0 | hxm_pos
    · have hzero : spinWc a (b - d) = 0 := by rw [show b - d = 0 by linarith, spinWc_zero]
      have hbd0 : (b - d) / 2 = 0 := by linarith
      unfold spinHbCalReal; rw [hbd0, Real.tanh_zero, hzero]; ring
    · have hfp_pos : 0 < spinCalFc a (d + b) := spinCalFc_pos_of_pos ha hxp_pos
      have hfm_pos : 0 < spinCalFc a (d - b) := spinCalFc_pos_of_pos ha hxm_pos
      have hwL : spinWc a (b + d) = Real.sqrt a * Real.exp (4 * π * a * (d + b)) * spinCalFc a (d + b) := by
        rw [show b + d = d + b by ring, spinWc_factorization ha.le, abs_of_pos hxp_pos]
      have hwR : spinWc a (b - d) = Real.sqrt a * Real.exp (4 * π * a * (d - b)) * spinCalFc a (d - b) := by
        rw [show b - d = -(d - b) by ring, spinWc_even, spinWc_factorization ha.le, abs_of_pos hxm_pos]
      have hphip : spinCalPhic a (d + b) * spinCalFc a (d + b) = Real.tanh ((b + d) / 2) ^ 2 := by
        unfold spinCalPhic; simp only [hxp_pos.ne', ↓reduceIte]
        rw [div_mul_cancel₀ _ hfp_pos.ne', show (d + b) / 2 = (b + d) / 2 by ring]
      have hphim : spinCalPhic a (d - b) * spinCalFc a (d - b) = Real.tanh ((b - d) / 2) ^ 2 := by
        unfold spinCalPhic; simp only [hxm_pos.ne', ↓reduceIte]
        rw [div_mul_cancel₀ _ hfm_pos.ne', show (b - d) / 2 = -((d - b) / 2) by ring, Real.tanh_neg, neg_sq]
      have hexp : Real.exp (-(12 * a) * (2 * π / 3) * (d - |b|)) *
          (Real.exp (4 * π * a * (d + b)) * Real.exp (4 * π * a * (d - b))) =
          Real.exp (12 * a * spinL b) := by
        rw [← Real.exp_add, ← Real.exp_add]; unfold spinL; congr 1; ring
      have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
      have ht_xs : Real.tanh (xiStar / 2) ^ 4 ≠ 0 :=
        pow_ne_zero 4 (spinTanh_pos (half_pos xiStar_pos)).ne'
      have hcal_ratio : 4 * spinCalF xiStar ^ 2 / Real.tanh (xiStar / 2) ^ 4 =
          4 / spinCalPhi xiStar ^ 2 := by
        unfold spinCalPhi; field_simp [ht_xs, (spinCalF_pos' xiStar_pos).ne']
      unfold spinRc2 spinHbCalReal spinCalFac
      rw [hwL, hwR]
      have hL_rew : 4 * spinCalF xiStar ^ 2 *
            (a * Real.exp (12 * a * spinL b) *
              ((1 + xiStar ^ 2) / (1 + b ^ 2) * (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) /
                Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2))) =
          (4 * spinCalF xiStar ^ 2 / Real.tanh (xiStar / 2) ^ 4) *
            ((1 + xiStar ^ 2) / (1 + b ^ 2) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
              Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2) *
              a * Real.exp (12 * a * spinL b) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2)) := by ring
      rw [hL_rew, hcal_ratio]
      symm
      calc Real.exp (-(12 * a) * (2 * π / 3) * (d - |b|)) * ((1 + xiStar ^ 2) / (1 + b ^ 2)) *
              (spinCalPhic a (d + b) * spinCalPhic a (d - b) / spinCalPhi xiStar ^ 2) *
              Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (b ^ 2 - xiStar ^ 2) ^ 2) *
              (Real.sqrt a * Real.exp (4 * π * a * (d + b)) * spinCalFc a (d + b)) *
              (Real.sqrt a * Real.exp (4 * π * a * (d - b)) * spinCalFc a (d - b))
          = ((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2) +
                (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2))) *
              (Real.sqrt a * Real.sqrt a) *
              (Real.exp (-(12 * a) * (2 * π / 3) * (d - |b|)) *
                (Real.exp (4 * π * a * (d + b)) * Real.exp (4 * π * a * (d - b)))) *
              ((spinCalPhic a (d + b) * spinCalFc a (d + b)) *
               (spinCalPhic a (d - b) * spinCalFc a (d - b))) := by ring
        _ = ((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2)) *
              a * Real.exp (12 * a * spinL b) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2) := by
              rw [Real.exp_add, hsqa, hexp, hphip, hphim]
      calc 4 * (Real.exp (-(12 * a) * (2 * π / 3) * (d - |b|)) * ((1 + xiStar ^ 2) / (1 + b ^ 2)) *
              (spinCalPhic a (d + b) * spinCalPhic a (d - b) / spinCalPhi xiStar ^ 2) *
              Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (b ^ 2 - xiStar ^ 2) ^ 2)) *
            (Real.sqrt a * Real.exp (4 * π * a * (d + b)) * spinCalFc a (d + b)) *
            (Real.sqrt a * Real.exp (4 * π * a * (d - b)) * spinCalFc a (d - b))
          = 4 * ((Real.exp (-(12 * a) * (2 * π / 3) * (d - |b|)) * ((1 + xiStar ^ 2) / (1 + b ^ 2)) *
                (spinCalPhic a (d + b) * spinCalPhic a (d - b) / spinCalPhi xiStar ^ 2) *
                Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                  (b ^ 2 - xiStar ^ 2) ^ 2)) *
              (Real.sqrt a * Real.exp (4 * π * a * (d + b)) * spinCalFc a (d + b)) *
              (Real.sqrt a * Real.exp (4 * π * a * (d - b)) * spinCalFc a (d - b))) := by ring
        _ = 4 * (((1 + xiStar ^ 2) / (1 + b ^ 2) / spinCalPhi xiStar ^ 2) *
              (Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                Real.exp (-spinAlpha1 * (b ^ 2 - xiStar ^ 2) / (2 * xiStar) - (b ^ 2 - xiStar ^ 2) ^ 2)) *
              a * Real.exp (12 * a * spinL b) *
              (Real.tanh ((b + d) / 2) ^ 2 * Real.tanh ((b - d) / 2) ^ 2)) := by rw [hR]
        _ = _ := by ring

/-! ### Coordinate changes and `D_4` transfer on `ℝ × ℝ` -/

private noncomputable def xdToUV_s4 : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun q := ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
  left_inv p := by exact Prod.ext (by dsimp; ring) (by dsimp; ring)
  right_inv q := by exact Prod.ext (by dsimp; ring) (by dsimp; ring)
  measurable_toFun := (measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun :=
    ((measurable_fst.add measurable_snd).div_const 2).prodMk
      ((measurable_fst.sub measurable_snd).div_const 2)

private lemma map_volume_xdToUV_s4 :
    Measure.map xdToUV_s4 (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2) • (volume : Measure (ℝ × ℝ)) := by
  let e₁ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1 + q.2, q.2)
      invFun := fun q => (q.1 - q.2, q.2)
      left_inv := fun q => Prod.ext (by ring) rfl
      right_inv := fun q => Prod.ext (by ring) rfl
      measurable_toFun := (measurable_fst.add measurable_snd).prodMk measurable_snd
      measurable_invFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd }
  let e₂ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1, q.1 - 2 * q.2)
      invFun := fun q => (q.1, (q.1 - q.2) / 2)
      left_inv := fun q => Prod.ext rfl (by ring)
      right_inv := fun q => Prod.ext rfl (by ring)
      measurable_toFun := measurable_fst.prodMk (measurable_fst.sub (measurable_const.mul measurable_snd))
      measurable_invFun := measurable_fst.prodMk ((measurable_fst.sub measurable_snd).div_const 2) }
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := e₁.trans e₂
  have h1 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₁ q) = ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₁ q)) (hg.comp e₁.measurable).aemeasurable,
      lintegral_lintegral_swap (f := fun x y => g (e₁ (x, y))) (hg.comp e₁.measurable).aemeasurable,
      lintegral_lintegral_swap (f := fun x y => g (x, y)) hg.aemeasurable]
    refine lintegral_congr fun y => ?_
    simpa [e₁] using lintegral_add_right_eq_self (fun x => g (x, y)) y
  have h2 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₂ q) = ENNReal.ofReal (1 / 2) * ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₂ q)) (hg.comp e₂.measurable).aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    let e4 : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ (-2 : ℝ) (by norm_num)
    have hm4 : Measure.map e4 (volume : Measure ℝ) = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ) := by
      have h := Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0)
      have habs : |(-2 : ℝ)⁻¹| = 1 / 2 := by norm_num
      rwa [habs] at h
    have hl : ∫⁻ y : ℝ, g (x, x + (-2 : ℝ) * y) =
        ENNReal.ofReal (1 / 2) * ∫⁻ z : ℝ, g (x, x + z) := by
      have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun z => g (x, x + z)) e4).symm
      rwa [hm4, lintegral_smul_measure, smul_eq_mul] at h
    have hshift : ∫⁻ z : ℝ, g (x, x + z) = ∫⁻ z : ℝ, g (x, z) :=
      lintegral_add_left_eq_self (fun z => g (x, z)) x
    have heq : (fun y : ℝ => g (e₂ (x, y))) = fun y : ℝ => g (x, x + (-2 : ℝ) * y) := by
      ext y; simp [e₂, sub_eq_add_neg]
    rw [heq, hl, hshift]
  have he_eq : (e : ℝ × ℝ → ℝ × ℝ) = (xdToUV_s4 : ℝ × ℝ → ℝ × ℝ) := by
    ext q
    · change (e₂ (e₁ q)).1 = q.1 + q.2; simp [e₁, e₂]
    · change (e₂ (e₁ q)).2 = q.1 - q.2; simp [e₁, e₂]; ring
  ext s hs
  rw [← he_eq, Measure.map_apply e.measurable hs, smul_apply, smul_eq_mul]
  have h_ind := h1 (fun q => (s.indicator 1) (e₂ q)) ((measurable_const.indicator hs).comp e₂.measurable)
  have h_ind2 := h2 (s.indicator 1) (measurable_const.indicator hs)
  have h_lhs : ∫⁻ q : ℝ × ℝ, (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q)) = volume (e ⁻¹' s) := by
    have : (fun q => (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q))) =
        (e ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞) := by ext q; rfl
    rw [this, lintegral_indicator_one (e.measurable hs)]
  rw [← h_lhs, h_ind, h_ind2, lintegral_indicator_one hs]

private lemma integral_xi_d_s4 (f : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, f (p.1 + p.2, p.1 - p.2) = (1 / 2 : ℝ) * ∫ q : ℝ × ℝ, f q := by
  have h := (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) xdToUV_s4 f).symm
  rw [map_volume_xdToUV_s4, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul] at h
  exact h

private lemma volume_axes_zero_s4 : volume {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} = 0 := by
  have h1 : volume {q : ℝ × ℝ | q.1 = 0} = 0 := by
    have : {q : ℝ × ℝ | q.1 = 0} = {(0 : ℝ)} ×ˢ Set.univ := by ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have h2 : volume {q : ℝ × ℝ | q.2 = 0} = 0 := by
    have : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ {(0 : ℝ)} := by ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  have heq : {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} = {q : ℝ × ℝ | q.1 = 0} ∪ {q : ℝ × ℝ | q.2 = 0} := by
    ext q; rfl
  rw [heq]
  exact measure_union_null h1 h2

private lemma map_volume_neg_left :
    Measure.map ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ))
      (volume : Measure (ℝ × ℝ)) = volume := by
  rw [Measure.volume_eq_prod]
  have h1 : (⇑((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)) : ℝ × ℝ → ℝ × ℝ) =
      Prod.map Neg.neg id := rfl
  rw [h1, ← Measure.map_prod_map _ _ measurable_neg measurable_id, Measure.map_neg_eq_self,
    Measure.map_id]

private lemma map_volume_neg_right :
    Measure.map ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ))
      (volume : Measure (ℝ × ℝ)) = volume := by
  rw [Measure.volume_eq_prod]
  have h1 : (⇑((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)) : ℝ × ℝ → ℝ × ℝ) =
      Prod.map id Neg.neg := rfl
  rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_neg, Measure.map_neg_eq_self,
    Measure.map_id]

private lemma map_volume_neg_both :
    Measure.map ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ))
      (volume : Measure (ℝ × ℝ)) = volume := by
  rw [Measure.volume_eq_prod]
  have h1 : (⇑((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)) : ℝ × ℝ → ℝ × ℝ) =
      Prod.map Neg.neg Neg.neg := rfl
  rw [h1, ← Measure.map_prod_map _ _ measurable_neg measurable_neg, Measure.map_neg_eq_self]

private lemma map_volume_swap_s4 :
    Measure.map (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) (volume : Measure (ℝ × ℝ)) = volume := by
  change Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = volume
  rw [Measure.volume_eq_prod, Measure.prod_swap]

private lemma integral_quad1_d4 {F : ℝ × ℝ → ℝ}
    (hF_int : Integrable F volume)
    (hF_nl : ∀ x y : ℝ, F (-x, y) = F (x, y))
    (hF_nr : ∀ x y : ℝ, F (x, -y) = F (x, y)) :
    4 * ∫ q in {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}, F q = ∫ q : ℝ × ℝ, F q := by
  let Qpp : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2}
  let Qnp : Set (ℝ × ℝ) := {q | q.1 < 0 ∧ 0 < q.2}
  let Qpn : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.2 < 0}
  let Qnn : Set (ℝ × ℝ) := {q | q.1 < 0 ∧ q.2 < 0}
  let Q1 : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2}
  have hm_pp : MeasurableSet Qpp :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet
  have hm_np : MeasurableSet Qnp :=
    (isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet
  have hm_pn : MeasurableSet Qpn :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet
  have hm_nn : MeasurableSet Qnn :=
    (isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet
  have hQ1_eq_pp : ∫ q in Q1, F q = ∫ q in Qpp, F q := by
    refine setIntegral_congr_set ?_
    filter_upwards [compl_mem_ae_iff.mpr volume_axes_zero_s4] with q hq
    have hq1 : q.1 ≠ 0 := fun h => hq (Or.inl h)
    have hq2 : q.2 ≠ 0 := fun h => hq (Or.inr h)
    simp only [Q1, Qpp, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨a1, a2⟩
    · exact ⟨lt_of_le_of_ne a1 hq1.symm, lt_of_le_of_ne a2 hq2.symm⟩
    · exact ⟨a1.le, a2.le⟩
  have h_np : ∫ q in Qnp, F q = ∫ q in Qpp, F q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have heq : ∫ q in Qnp, F q = ∫ q, Qpp.indicator F (e q) := by
      rw [← integral_indicator hm_np]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      have he_val : e q = (-q.1, q.2) := rfl
      by_cases hq : q ∈ Qnp
      · have hq' : e q ∈ Qpp := by rw [he_val]; exact ⟨by linarith [hq.1], hq.2⟩
        simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hq']; rw [he_val, hF_nl]
      · have hq' : e q ∉ Qpp := by rw [he_val]; exact fun hm => hq ⟨by linarith [hm.1], hm.2⟩
        simp [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    rw [heq, (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (Qpp.indicator F)).symm,
      map_volume_neg_left, integral_indicator hm_pp]
  have h_pn : ∫ q in Qpn, F q = ∫ q in Qpp, F q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have heq : ∫ q in Qpn, F q = ∫ q, Qpp.indicator F (e q) := by
      rw [← integral_indicator hm_pn]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      have he_val : e q = (q.1, -q.2) := rfl
      by_cases hq : q ∈ Qpn
      · have hq' : e q ∈ Qpp := by rw [he_val]; exact ⟨hq.1, by linarith [hq.2]⟩
        simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hq']; rw [he_val, hF_nr]
      · have hq' : e q ∉ Qpp := by rw [he_val]; exact fun hm => hq ⟨hm.1, by linarith [hm.2]⟩
        simp [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    rw [heq, (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (Qpp.indicator F)).symm,
      map_volume_neg_right, integral_indicator hm_pp]
  have h_nn : ∫ q in Qnn, F q = ∫ q in Qpp, F q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have heq : ∫ q in Qnn, F q = ∫ q, Qpp.indicator F (e q) := by
      rw [← integral_indicator hm_nn]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      have he_val : e q = (-q.1, -q.2) := rfl
      by_cases hq : q ∈ Qnn
      · have hq' : e q ∈ Qpp := by rw [he_val]; exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
        simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hq']; rw [he_val, hF_nl, hF_nr]
      · have hq' : e q ∉ Qpp := by
          rw [he_val]; exact fun hm => hq ⟨by linarith [hm.1], by linarith [hm.2]⟩
        simp [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    rw [heq, (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (Qpp.indicator F)).symm,
      map_volume_neg_both, integral_indicator hm_pp]
  have hunion : Qpp ∪ Qnp ∪ Qpn ∪ Qnn =ᵐ[volume] (Set.univ : Set (ℝ × ℝ)) := by
    filter_upwards [compl_mem_ae_iff.mpr volume_axes_zero_s4] with q hq
    have hq1 : q.1 ≠ 0 := fun h => hq (Or.inl h)
    have hq2 : q.2 ≠ 0 := fun h => hq (Or.inr h)
    simp only [Set.mem_union, Qpp, Qnp, Qpn, Qnn, Set.mem_univ, iff_true]
    rcases lt_or_gt_of_ne hq1 with h1 | h1 <;> rcases lt_or_gt_of_ne hq2 with h2 | h2
    · right; exact ⟨h1, h2⟩
    · left; left; right; exact ⟨h1, h2⟩
    · left; right; exact ⟨h1, h2⟩
    · left; left; left; exact ⟨h1, h2⟩
  have hd1 : Disjoint Qpp Qnp := Set.disjoint_left.mpr fun _ h1 h2 => absurd h1.1 h2.1.not_gt
  have hd2 : Disjoint (Qpp ∪ Qnp) Qpn :=
    Set.disjoint_left.mpr fun _ h1 h2 => h1.elim (fun ha => absurd ha.2 h2.2.not_gt)
      (fun hb => absurd hb.2 h2.2.not_gt)
  have hd3 : Disjoint (Qpp ∪ Qnp ∪ Qpn) Qnn :=
    Set.disjoint_left.mpr fun _ h1 h2 => by
      rcases h1 with (ha | hb) | hc
      · exact absurd ha.1 h2.1.not_gt
      · exact absurd hb.2 h2.2.not_gt
      · exact absurd hc.1 h2.1.not_gt
  calc 4 * ∫ q in Q1, F q
      = ∫ q in Qpp, F q + ∫ q in Qnp, F q + ∫ q in Qpn, F q + ∫ q in Qnn, F q := by
        rw [hQ1_eq_pp, h_np, h_pn, h_nn]; ring
    _ = ∫ q in (Qpp ∪ Qnp ∪ Qpn ∪ Qnn), F q := by
        rw [setIntegral_union hd3 hm_nn hF_int.integrableOn hF_int.integrableOn,
          setIntegral_union hd2 hm_pn hF_int.integrableOn hF_int.integrableOn,
          setIntegral_union hd1 hm_np hF_int.integrableOn hF_int.integrableOn]
        rfl
    _ = ∫ q in (Set.univ : Set (ℝ × ℝ)), F q := setIntegral_congr_set hunion
    _ = ∫ q : ℝ × ℝ, F q := setIntegral_univ

/-! ### Unified calibrated adjoint formula `(s4:eP.0)` and `(s4:eR.6)` -/

lemma spinCal_adjoint_identity
    {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {F : ℝ × ℝ → ℝ} (hF_meas : Measurable F)
    (hF_bd : ∀ p : ℝ × ℝ, |F p| ≤ |spinG ((c - 1) / 12) Φ p.1 p.2|)
    (hF_nl : ∀ x y : ℝ, F (-x, y) = F (x, y))
    (hF_nr : ∀ x y : ℝ, F (x, -y) = F (x, y))
    {φ : ℝ → ℝ} (hφ_meas : Measurable φ) {Mφ : ℝ} (hMφ : 0 ≤ Mφ)
    (hφ_bd : ∀ x : ℝ, |φ x| ≤ Mφ) :
    let n := c - 1
    let a := n / 12
    Integrable (fun p : ℝ × ℝ =>
      a * Real.exp (n * spinL p.1) * φ |p.1| *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * F (p.1 + p.2, p.1 - p.2))) ∧
    Integrable (fun p : ℝ × ℝ =>
      (spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p) +
       spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p)) *
        F p * spinWc a p.1 * spinWc a p.2) ∧
    (∫ b : ℝ, a * Real.exp (n * spinL b) * φ |b| *
        (4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * F (b + d, b - d))) =
      ∫ p : ℝ × ℝ,
        (spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p) +
         spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p)) *
          F p * spinWc a p.1 * spinWc a p.2 := by
  intro n a
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hn_eq : 12 * a = n := by dsimp [a]; ring
  obtain ⟨_c_σ, C_rc, _hcσ_pos, hCrc_pos, hRc_bd⟩ := spinS4_2_2_abs_bound
  have hRc_ub : ∀ ξ d : ℝ, |d| ≤ ξ → spinRc a ξ d ≤ 1 + C_rc / n := fun ξ d hd => by
    have h1 := (hRc_bd hc (ξ + d, ξ - d)).2.2
    have habs_p : |(ξ + d : ℝ)| = ξ + d := abs_of_nonneg (by linarith [abs_le.mp hd])
    have habs_m : |(ξ - d : ℝ)| = ξ - d := abs_of_nonneg (by linarith [abs_le.mp hd])
    have hs1 : (|(ξ + d)| + |(ξ - d)|) / 2 = ξ := by rw [habs_p, habs_m]; ring
    have hs2 : (|(ξ + d)| - |(ξ - d)|) / 2 = d := by rw [habs_p, habs_m]; ring
    rw [hs1, hs2, abs_of_nonneg (spinRc_nonneg_all' ha2.le ξ d)] at h1
    exact h1
  have hRc1_ub : ∀ ξ d : ℝ, |d| ≤ ξ → spinRc1 a ξ d ≤ 1 + C_rc / n := fun ξ d hd =>
    (le_add_of_nonneg_right (spinRc2_nonneg ha2.le ξ d)).trans (hRc_ub ξ d hd)
  have hRc2_ub : ∀ ξ d : ℝ, |d| ≤ ξ → spinRc2 a ξ d ≤ 1 + C_rc / n := fun ξ d hd =>
    (le_add_of_nonneg_left (spinRc1_nonneg ha2.le ξ d)).trans (hRc_ub ξ d hd)
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  let K_rhs : ℝ × ℝ → ℝ := fun p =>
    (spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p) +
     spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p)) *
      F p * spinWc a p.1 * spinWc a p.2
  have hK_meas : Measurable K_rhs := by
    have hL : Measurable spinLongDist :=
      measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
    have hT : Measurable spinTransDist :=
      measurable_const.mul (((measurable_fst.abs).sub (measurable_snd.abs)).abs)
    exact ((((measurable_spinRc1 a).mul (hφ_meas.comp hL)).add
      ((measurable_spinRc2 a).mul (hφ_meas.comp hT))).mul hF_meas |>.mul
        (hWc_cont.comp continuous_fst).measurable).mul (hWc_cont.comp continuous_snd).measurable
  have hK_int : Integrable K_rhs := by
    refine (hG_int.const_mul (Mφ * (1 + C_rc / n))).mono' hK_meas.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have hξd : |(|p.1| - |p.2|) / 2| ≤ spinLongDist p := by
      unfold spinLongDist
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rcases le_total |p.1| |p.2| with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg p.1]
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg p.2]
    have hr1 := spinRc1_nonneg ha2.le (spinLongDist p) ((|p.1| - |p.2|) / 2)
    have hr2 := spinRc2_nonneg ha2.le (spinLongDist p) ((|p.1| - |p.2|) / 2)
    have hrc_sum := hRc_ub (spinLongDist p) ((|p.1| - |p.2|) / 2) hξd
    have hbr_bd : |spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p) +
        spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p)| ≤
        Mφ * (1 + C_rc / n) := by
      calc _ ≤ |spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p)| +
            |spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p)| := abs_add_le _ _
        _ = spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * |φ (spinLongDist p)| +
            spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * |φ (spinTransDist p)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hr1, abs_of_nonneg hr2]
        _ ≤ spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * Mφ +
            spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * Mφ := by
            gcongr <;> exact hφ_bd _
        _ = Mφ * spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) := by unfold spinRc; ring
        _ ≤ Mφ * (1 + C_rc / n) := mul_le_mul_of_nonneg_left hrc_sum hMφ
    have hw1 := spinWc_nonneg ha2.le p.1
    have hw2 := spinWc_nonneg ha2.le p.2
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
    have hF_abs : |F p| ≤ |spinG a Φ p.1 p.2| := hF_bd p
    calc |(spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinLongDist p) +
            spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * φ (spinTransDist p))| *
          |F p| * spinWc a p.1 * spinWc a p.2
        ≤ (Mφ * (1 + C_rc / n)) * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
      _ = _ := by ring
  let H_bd : ℝ × ℝ → ℝ := fun p =>
    a * Real.exp (n * spinL p.1) * φ |p.1| *
      (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * F (p.1 + p.2, p.1 - p.2))
  have hHb_cont : Continuous (fun p : ℝ × ℝ => spinHbCalReal p.1 p.2) := by
    unfold spinHbCalReal spinCalFac
    have hp : Continuous (fun p : ℝ × ℝ => Real.tanh ((p.1 + p.2) / 2) ^ 2) :=
      (continuous_spinTanh.comp ((continuous_fst.add continuous_snd).div_const 2)).pow 2
    have hm : Continuous (fun p : ℝ × ℝ => Real.tanh ((p.1 - p.2) / 2) ^ 2) :=
      (continuous_spinTanh.comp ((continuous_fst.sub continuous_snd).div_const 2)).pow 2
    have hrat : Continuous (fun p : ℝ × ℝ => (1 + xiStar ^ 2) / (1 + p.1 ^ 2)) :=
      continuous_const.div (continuous_const.add (continuous_fst.pow 2))
        (fun p => (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
    have he1 : Continuous (fun p : ℝ × ℝ => Real.exp (-(p.2 ^ 2 / spinSigma0 ^ 2))) :=
      Real.continuous_exp.comp ((continuous_snd.pow 2).div_const _).neg
    have he2 : Continuous (fun p : ℝ × ℝ =>
        Real.exp (-spinAlpha1 * (p.1 ^ 2 - xiStar ^ 2) / (2 * xiStar) - (p.1 ^ 2 - xiStar ^ 2) ^ 2)) :=
      Real.continuous_exp.comp
        ((((continuous_const.mul ((continuous_fst.pow 2).sub continuous_const)).div_const _).sub
          (((continuous_fst.pow 2).sub continuous_const).pow 2)))
    exact ((((hrat.mul (hp.mul hm)).div_const _).mul he1).mul he2)
  have hHb_meas : Measurable (fun p : ℝ × ℝ => spinHbCalReal p.1 p.2) := hHb_cont.measurable
  have hH_meas : Measurable H_bd := by
    have hL : Measurable (fun p : ℝ × ℝ => spinL p.1) :=
      (measurable_const.mul measurable_fst.abs).div_const 3
    exact ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hL))).mul
      (hφ_meas.comp measurable_fst.abs)).mul
      ((measurable_const.mul hHb_meas).mul (hF_meas.comp xdToUV_s4.measurable))
  have hG_uv_int : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) := by
    have hsm : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
        (Measure.map xdToUV_s4 volume) := by
      rw [map_volume_xdToUV_s4]
      exact hG_int.smul_measure ENNReal.ofReal_lt_top.ne
    exact (integrable_map_measure hsm.aestronglyMeasurable xdToUV_s4.measurable.aemeasurable).mp hsm
  have hH_pt : ∀ p : ℝ × ℝ, ‖H_bd p‖ ≤
      (4 * Mφ * (1 + C_rc / n)) *
        (|spinG a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) := by
    rintro ⟨b, d⟩
    rw [Real.norm_eq_abs]
    have hker_nn : 0 ≤ 4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL b) * spinHbCalReal b d) := by
      have := spinHbCalReal_nonneg b d; positivity
    have hrew : H_bd (b, d) =
        (4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL b) * spinHbCalReal b d)) *
          φ |b| * F (b + d, b - d) := by dsimp [H_bd]; ring
    rw [hrew, abs_mul, abs_mul, abs_of_nonneg hker_nn]
    have hker_bd : 4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL b) * spinHbCalReal b d) ≤
        4 * (1 + C_rc / n) * (spinWc a (b + d) * spinWc a (b - d)) := by
      rcases le_total |d| |b| with hbd | hbd
      · rcases le_total 0 b with hb0 | hb0
        · have hb' : |d| ≤ b := by rwa [abs_of_nonneg hb0] at hbd
          have heq := spinHbCalReal_eq_spinRc1 ha2 hb'
          rw [hn_eq] at heq
          rw [heq, mul_assoc (4 * spinRc1 a b d)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRc1_ub b d hb') (by norm_num))
            (mul_nonneg (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _))
        · have hb' : |(-d)| ≤ -b := by rw [abs_neg]; rwa [abs_of_nonpos hb0] at hbd
          have hL_neg : spinL (-b) = spinL b := by unfold spinL; rw [abs_neg]
          have hwc_nl : spinWc a (b + d) = spinWc a (-b + -d) := by
            rw [show -b + -d = -(b + d) by ring, spinWc_even]
          have hwc_nr : spinWc a (b - d) = spinWc a (-b - -d) := by
            rw [show -b - -d = -(b - d) by ring, spinWc_even]
          have heq := spinHbCalReal_eq_spinRc1 ha2 hb'
          rw [hn_eq, hL_neg, spinHbCalReal_neg] at heq
          rw [heq, hwc_nl, hwc_nr, mul_assoc (4 * spinRc1 a (-b) (-d))]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRc1_ub (-b) (-d) hb') (by norm_num))
            (mul_nonneg (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _))
      · rcases le_total 0 d with hd0 | hd0
        · have hd' : |b| ≤ d := by rwa [abs_of_nonneg hd0] at hbd
          have heq := spinHbCalReal_eq_spinRc2 ha2 hd'
          rw [hn_eq] at heq
          rw [heq, mul_assoc (4 * spinRc2 a d b)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRc2_ub d b hd') (by norm_num))
            (mul_nonneg (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _))
        · have hd' : |(-b)| ≤ -d := by rw [abs_neg]; rwa [abs_of_nonpos hd0] at hbd
          have hL_neg : spinL (-b) = spinL b := by unfold spinL; rw [abs_neg]
          have hwc_nl : spinWc a (b + d) = spinWc a (-b + -d) := by
            rw [show -b + -d = -(b + d) by ring, spinWc_even]
          have hwc_nr : spinWc a (b - d) = spinWc a (-b - -d) := by
            rw [show -b - -d = -(b - d) by ring, spinWc_even]
          have heq := spinHbCalReal_eq_spinRc2 ha2 hd'
          rw [hn_eq, hL_neg, spinHbCalReal_neg] at heq
          rw [heq, hwc_nl, hwc_nr, mul_assoc (4 * spinRc2 a (-d) (-b))]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hRc2_ub (-d) (-b) hd') (by norm_num))
            (mul_nonneg (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _))
    have hw_nn : 0 ≤ spinWc a (b + d) * spinWc a (b - d) :=
      mul_nonneg (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _)
    have hF_abs : |F (b + d, b - d)| ≤ |spinG a Φ (b + d) (b - d)| := hF_bd (b + d, b - d)
    have hφ_abs : |φ (|b|)| ≤ Mφ := hφ_bd |b|
    calc (4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL b) * spinHbCalReal b d)) *
            |φ (|b|)| * |F (b + d, b - d)|
        ≤ (4 * (1 + C_rc / n) * (spinWc a (b + d) * spinWc a (b - d))) * Mφ *
            |spinG a Φ (b + d) (b - d)| := by
          gcongr
      _ = (4 * Mφ * (1 + C_rc / n)) *
            (|spinG a Φ (b + d) (b - d)| * spinWc a (b + d) * spinWc a (b - d)) := by ring
  have hH_int : Integrable H_bd :=
    (hG_uv_int.const_mul (4 * Mφ * (1 + C_rc / n))).mono' hH_meas.aestronglyMeasurable
      (Eventually.of_forall hH_pt)
  refine ⟨hH_int, hK_int, ?_⟩
  have hH_prod : Integrable H_bd (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
  have hfub : ∫ b : ℝ, a * Real.exp (n * spinL b) * φ |b| *
        (4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * F (b + d, b - d)) =
      ∫ p : ℝ × ℝ, H_bd p := by
    rw [Measure.volume_eq_prod, integral_prod H_bd hH_prod]
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    dsimp [H_bd]
    simp_rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun d => by ring)
  rw [hfub]
  let S₁ : Set (ℝ × ℝ) := {p | |p.2| ≤ p.1}
  let S₂ : Set (ℝ × ℝ) := {p | p.1 ≤ -|p.2| ∧ p.1 < 0}
  let S₃ : Set (ℝ × ℝ) := {p | |p.1| < p.2}
  let S₄ : Set (ℝ × ℝ) := {p | p.2 < -|p.1|}
  have hm1 : MeasurableSet S₁ := (isClosed_le continuous_snd.abs continuous_fst).measurableSet
  have hm2 : MeasurableSet S₂ :=
    (isClosed_le continuous_fst continuous_snd.abs.neg).measurableSet.inter
      (isOpen_lt continuous_fst continuous_const).measurableSet
  have hm3 : MeasurableSet S₃ := (isOpen_lt continuous_fst.abs continuous_snd).measurableSet
  have hm4 : MeasurableSet S₄ := (isOpen_lt continuous_snd continuous_fst.abs.neg).measurableSet
  have hd12 : Disjoint S₁ S₂ := Set.disjoint_left.mpr fun p h1 h2 => by linarith [abs_nonneg p.2, h1, h2.2]
  have hd123 : Disjoint (S₁ ∪ S₂) S₃ := Set.disjoint_left.mpr fun p h12 h3 => by
    rcases h12 with h1 | h2
    · exact absurd h1 (not_le_of_gt (lt_of_abs_lt h3))
    · have : |p.2| ≤ |p.1| := by rw [abs_of_neg h2.2]; linarith [h2.1]
      exact absurd h3 (not_lt_of_ge (this.trans (le_abs_self p.2)))
  have hd1234 : Disjoint (S₁ ∪ S₂ ∪ S₃) S₄ := Set.disjoint_left.mpr fun p h123 h4 => by
    rcases h123 with (h1 | h2) | h3
    · have : p.2 ≤ |p.2| := le_abs_self _; exact absurd h4 (by linarith [abs_nonneg p.1, h1])
    · have : -p.1 = |p.1| := (abs_of_neg h2.2).symm
      have : -|p.2| ≤ -|p.1| := by linarith [h2.1]
      linarith [neg_abs_le p.2]
    · linarith [abs_nonneg p.1, h3]
  have huniv : S₁ ∪ S₂ ∪ S₃ ∪ S₄ = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true, S₁, S₂, S₃, S₄]
    rcases le_total |p.2| |p.1| with h | h
    · rcases le_or_gt 0 p.1 with hp1 | hp1
      · left; left; left; rwa [abs_of_nonneg hp1] at h
      · left; left; right; exact ⟨by rw [abs_of_neg hp1] at h; linarith, hp1⟩
    · rcases le_total 0 p.2 with hp2 | hp2
      · left; right; rwa [abs_of_nonneg hp2] at h
      · right; rw [abs_of_neg hp2] at h; linarith
  let K1 : ℝ × ℝ → ℝ := fun q =>
    spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinLongDist q) *
      F q * spinWc a q.1 * spinWc a q.2
  let K2 : ℝ × ℝ → ℝ := fun q =>
    spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinTransDist q) *
      F q * spinWc a q.1 * spinWc a q.2
  have hK1_int : Integrable K1 := by
    refine (hG_int.const_mul (Mφ * (1 + C_rc / n))).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_spinRc1 a).mul (hφ_meas.comp
        (measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))))).mul hF_meas |>.mul
        (hWc_cont.comp continuous_fst).measurable).mul (hWc_cont.comp continuous_snd).measurable).aestronglyMeasurable
    · have hξd : |(|p.1| - |p.2|) / 2| ≤ spinLongDist p := by
        unfold spinLongDist
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rcases le_total |p.1| |p.2| with h | h
        · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg p.1]
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg p.2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (spinRc1_nonneg ha2.le _ _), abs_of_nonneg (spinWc_nonneg ha2.le _),
        abs_of_nonneg (spinWc_nonneg ha2.le _)]
      calc _ ≤ (1 + C_rc / n) * Mφ * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
            gcongr
            · exact hRc1_ub _ _ hξd
            · exact hφ_bd _
            · exact hF_bd p
            · exact spinWc_nonneg ha2.le _
            · exact spinWc_nonneg ha2.le _
        _ = _ := by ring
  have hK2_int : Integrable K2 := by
    refine (hG_int.const_mul (Mφ * (1 + C_rc / n))).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_spinRc2 a).mul (hφ_meas.comp
        (measurable_const.mul (((measurable_fst.abs).sub (measurable_snd.abs)).abs)))).mul hF_meas |>.mul
        (hWc_cont.comp continuous_fst).measurable).mul (hWc_cont.comp continuous_snd).measurable).aestronglyMeasurable
    · have hξd : |(|p.1| - |p.2|) / 2| ≤ spinLongDist p := by
        unfold spinLongDist
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rcases le_total |p.1| |p.2| with h | h
        · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg p.1]
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg p.2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (spinRc2_nonneg ha2.le _ _), abs_of_nonneg (spinWc_nonneg ha2.le _),
        abs_of_nonneg (spinWc_nonneg ha2.le _)]
      calc _ ≤ (1 + C_rc / n) * Mφ * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
            gcongr
            · exact hRc2_ub _ _ hξd
            · exact hφ_bd _
            · exact hF_bd p
            · exact spinWc_nonneg ha2.le _
            · exact spinWc_nonneg ha2.le _
        _ = _ := by ring
  have hK_split : ∫ p, K_rhs p = ∫ p, K1 p + ∫ p, K2 p := by
    rw [← integral_add hK1_int hK2_int]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    dsimp [K_rhs, K1, K2]; ring
  have hS1_eq : 2 * ∫ p in S₁, H_bd p = ∫ p, K1 p := by
    let Q₁ : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2}
    have hS1_pre : ∫ p in S₁, H_bd p =
        ∫ p : ℝ × ℝ, Q₁.indicator (fun q => (4 : ℝ) * K1 q) (xdToUV_s4 p) := by
      rw [← integral_indicator hm1]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ S₁
      · have hq : xdToUV_s4 p ∈ Q₁ := by
          simp only [xdToUV_s4, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Q₁, Set.mem_ofPred_eq]
          have := abs_le.mp hp; constructor <;> linarith
        simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
        dsimp [H_bd, K1, xdToUV_s4, spinLongDist]
        have hb0 : 0 ≤ p.1 := (abs_nonneg p.2).trans hp
        have hxL0 : 0 ≤ p.1 + p.2 := by linarith [abs_le.mp hp]
        have hxR0 : 0 ≤ p.1 - p.2 := by linarith [abs_le.mp hp]
        have heq := spinHbCalReal_eq_spinRc1 ha2 hp
        rw [hn_eq] at heq
        have hs1 : (1 / 2 : ℝ) * (|p.1 + p.2| + |p.1 - p.2|) = p.1 := by
          rw [abs_of_nonneg hxL0, abs_of_nonneg hxR0]; ring
        have hs2 : (|p.1 + p.2| - |p.1 - p.2|) / 2 = p.2 := by
          rw [abs_of_nonneg hxL0, abs_of_nonneg hxR0]; ring
        rw [abs_of_nonneg hb0, hs1, hs2]
        calc a * Real.exp (n * spinL p.1) * φ p.1 * (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * F (p.1 + p.2, p.1 - p.2))
            = (4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL p.1) * spinHbCalReal p.1 p.2)) *
                φ p.1 * F (p.1 + p.2, p.1 - p.2) := by ring
          _ = (4 * spinRc1 a p.1 p.2 * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) *
                φ p.1 * F (p.1 + p.2, p.1 - p.2) := by rw [heq]
          _ = _ := by ring
      · have hq : xdToUV_s4 p ∉ Q₁ := by
          simp only [xdToUV_s4, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Q₁, Set.mem_ofPred_eq, not_and, not_le]
          intro h1 h2; apply hp; exact abs_le.mpr ⟨by linarith, by linarith⟩
        simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
    rw [hS1_pre, integral_xi_d_s4 (Q₁.indicator (fun q => (4 : ℝ) * K1 q)),
      integral_indicator ((isClosed_le continuous_const continuous_fst).measurableSet.inter
        (isClosed_le continuous_const continuous_snd).measurableSet)]
    have hpull : ∫ q in Q₁, (4 : ℝ) * K1 q = (4 : ℝ) * ∫ q in Q₁, K1 q := by
      simp_rw [integral_const_mul]
    rw [hpull, ← mul_assoc, show (2 : ℝ) * ((1 / 2 : ℝ) * (4 : ℝ)) = 4 by ring]
    have hK1_nl : ∀ x y : ℝ, K1 (-x, y) = K1 (x, y) := fun x y => by
      dsimp [K1, spinLongDist]; rw [abs_neg, hF_nl, spinWc_even]
    have hK1_nr : ∀ x y : ℝ, K1 (x, -y) = K1 (x, y) := fun x y => by
      dsimp [K1, spinLongDist]; rw [abs_neg, hF_nr, spinWc_even]
    exact integral_quad1_d4 hK1_int hK1_nl hK1_nr
  have hS2_eq : ∫ p in S₂, H_bd p = ∫ p in S₁, H_bd p := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hS2_ae : (fun p => H_bd (e p)) = H_bd := by
      ext ⟨b, d⟩
      dsimp [H_bd, e]
      rw [show spinL (-b) = spinL b by unfold spinL; rw [abs_neg],
        abs_neg, spinHbCalReal_neg, show -b + -d = -(b + d) by ring,
        show -b - -d = -(b - d) by ring, hF_nl, hF_nr]
    have hS2_set : e ⁻¹' S₁ =ᵐ[volume] S₂ := by
      have h0 : volume ({(0, 0)} : Set (ℝ × ℝ)) = 0 := Real.volume_singleton
      filter_upwards [compl_mem_ae_iff.mpr h0] with p hp
      simp only [e, MeasurableEquiv.prodCongr_apply, MeasurableEquiv.coe_neg, Prod.map_apply,
        Set.mem_preimage, Set.mem_ofPred_eq, S₁, S₂, abs_neg]
      constructor
      · intro h
        refine ⟨by linarith, ?_⟩
        by_contra h00
        have hp1 : p.1 = 0 := by linarith [abs_nonneg p.2]
        have hp2 : p.2 = 0 := by
          have : |p.2| ≤ 0 := by linarith
          exact abs_nonpos_iff.mp this
        exact hp (Prod.ext hp1 hp2)
      · rintro ⟨h1, _⟩; linarith
    have he1 : ∫ p in S₁, H_bd p = ∫ p, S₂.indicator H_bd p := by
      rw [← integral_indicator hm1,
        ← (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (S₁.indicator H_bd)).symm,
        map_volume_neg_both]
      refine integral_congr_ae ?_
      filter_upwards [hS2_set] with p hp
      have hLHS : S₁.indicator H_bd (e p) = (e ⁻¹' S₁).indicator (fun q => H_bd (e q)) p := by
        by_cases h : p ∈ e ⁻¹' S₁ <;> simp [Set.indicator, h]
      rw [hLHS, hS2_ae]
      by_cases h1 : p ∈ e ⁻¹' S₁
      · have h2 : p ∈ S₂ := hp.mp h1
        simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · have h2 : p ∉ S₂ := fun h => h1 (hp.mpr h)
        simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    rw [he1, integral_indicator hm2]
  have hS3_eq : 2 * ∫ p in S₃, H_bd p = ∫ p, K2 p := by
    let Q₁ : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2}
    let e_sw : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodComm
    have hS3_pre : ∫ p in S₃, H_bd p =
        ∫ p : ℝ × ℝ, Q₁.indicator (fun q => (4 : ℝ) * K2 q) (xdToUV_s4 (e_sw p)) := by
      rw [← integral_indicator hm3]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ S₃
      · have hq : xdToUV_s4 (e_sw p) ∈ Q₁ := by
          simp only [xdToUV_s4, e_sw, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
            MeasurableEquiv.coe_prodComm, Q₁, Set.mem_ofPred_eq]
          have := abs_lt.mp hp; constructor <;> linarith
        simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
        dsimp [H_bd, K2, xdToUV_s4, e_sw, spinLongDist, spinTransDist]
        have hdp0 : 0 ≤ p.2 + p.1 := by linarith [abs_lt.mp hp]
        have hdm0 : 0 ≤ p.2 - p.1 := by linarith [abs_lt.mp hp]
        have heq := spinHbCalReal_eq_spinRc2 ha2 hp.le
        rw [hn_eq] at heq
        have hs1 : (1 / 2 : ℝ) * (|p.2 + p.1| + |p.2 - p.1|) = p.2 := by
          rw [abs_of_nonneg hdp0, abs_of_nonneg hdm0]; ring
        have hs2 : (|p.2 + p.1| - |p.2 - p.1|) / 2 = p.1 := by
          rw [abs_of_nonneg hdp0, abs_of_nonneg hdm0]; ring
        have ht : (1 / 2 : ℝ) * |(|p.2 + p.1| - |p.2 - p.1|)| = |p.1| := by
          rw [abs_of_nonneg hdp0, abs_of_nonneg hdm0, show p.2 + p.1 - (p.2 - p.1) = 2 * p.1 by ring,
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
        rw [hs1, hs2, ht]
        have hF_eq : F (p.2 + p.1, p.2 - p.1) = F (p.1 + p.2, p.1 - p.2) := by
          rw [show p.2 + p.1 = p.1 + p.2 by ring, show p.2 - p.1 = -(p.1 - p.2) by ring, hF_nr]
        have hw_eq : spinWc a (p.2 + p.1) * spinWc a (p.2 - p.1) =
            spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2) := by
          rw [show p.2 + p.1 = p.1 + p.2 by ring, show p.2 - p.1 = -(p.1 - p.2) by ring, spinWc_even]
        rw [hF_eq, hw_eq]
        calc a * Real.exp (n * spinL p.1) * φ |p.1| *
                (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * F (p.1 + p.2, p.1 - p.2))
            = (4 * spinCalF xiStar ^ 2 * (a * Real.exp (n * spinL p.1) * spinHbCalReal p.1 p.2)) *
                φ |p.1| * F (p.1 + p.2, p.1 - p.2) := by ring
          _ = (4 * spinRc2 a p.2 p.1 * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) *
                φ |p.1| * F (p.1 + p.2, p.1 - p.2) := by rw [heq]
          _ = _ := by ring
      · by_cases hq : xdToUV_s4 (e_sw p) ∈ Q₁
        · simp only [Set.indicator_of_notMem hp, Set.indicator_of_mem hq]
          simp only [xdToUV_s4, e_sw, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
            MeasurableEquiv.coe_prodComm, Q₁, Set.mem_ofPred_eq] at hq
          have hle : |p.1| ≤ p.2 := abs_le.mpr ⟨by linarith, by linarith⟩
          have heq_abs : |p.1| = p.2 := le_antisymm hle (not_lt.mp hp)
          have hwc0 : spinWc a (p.2 + p.1) * spinWc a (p.2 - p.1) = 0 := by
            rcases le_or_gt 0 p.1 with hp1 | hp1
            · rw [abs_of_nonneg hp1] at heq_abs
              rw [show p.2 - p.1 = 0 by linarith, spinWc_zero, mul_zero]
            · rw [abs_of_neg hp1] at heq_abs
              rw [show p.2 + p.1 = 0 by linarith, spinWc_zero, zero_mul]
          dsimp [K2, xdToUV_s4, e_sw]
          rw [mul_assoc, hwc0, mul_zero, mul_zero]
        · simp [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq]
    have hsw_eq : ∫ p : ℝ × ℝ, Q₁.indicator (fun q => (4 : ℝ) * K2 q) (xdToUV_s4 (e_sw p)) =
        ∫ p : ℝ × ℝ, Q₁.indicator (fun q => (4 : ℝ) * K2 q) (xdToUV_s4 p) := by
      rw [← (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e_sw
          (fun q => Q₁.indicator (fun q => (4 : ℝ) * K2 q) (xdToUV_s4 q))).symm,
        map_volume_swap_s4]
    rw [hS3_pre, hsw_eq, integral_xi_d_s4 (Q₁.indicator (fun q => (4 : ℝ) * K2 q)),
      integral_indicator ((isClosed_le continuous_const continuous_fst).measurableSet.inter
        (isClosed_le continuous_const continuous_snd).measurableSet)]
    have hpull : ∫ q in Q₁, (4 : ℝ) * K2 q = (4 : ℝ) * ∫ q in Q₁, K2 q := by
      simp_rw [integral_const_mul]
    rw [hpull, ← mul_assoc, show (2 : ℝ) * ((1 / 2 : ℝ) * (4 : ℝ)) = 4 by ring]
    have hK2_nl : ∀ x y : ℝ, K2 (-x, y) = K2 (x, y) := fun x y => by
      dsimp [K2, spinLongDist, spinTransDist]; rw [abs_neg, hF_nl, spinWc_even]
    have hK2_nr : ∀ x y : ℝ, K2 (x, -y) = K2 (x, y) := fun x y => by
      dsimp [K2, spinLongDist, spinTransDist]; rw [abs_neg, hF_nr, spinWc_even]
    exact integral_quad1_d4 hK2_int hK2_nl hK2_nr
  have hS4_eq : ∫ p in S₄, H_bd p = ∫ p in S₃, H_bd p := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hS4_ae : (fun p => H_bd (e p)) = H_bd := by
      ext ⟨b, d⟩
      dsimp [H_bd, e]
      rw [show spinL (-b) = spinL b by unfold spinL; rw [abs_neg],
        abs_neg, spinHbCalReal_neg, show -b + -d = -(b + d) by ring,
        show -b - -d = -(b - d) by ring, hF_nl, hF_nr]
    have hS4_set : e ⁻¹' S₃ = S₄ := by
      ext p
      simp only [e, MeasurableEquiv.prodCongr_apply, MeasurableEquiv.coe_neg,
        Set.mem_preimage, Set.mem_ofPred_eq, S₃, S₄, abs_neg]
      constructor <;> intro h <;> linarith
    have he1 : ∫ p in S₃, H_bd p = ∫ p, S₄.indicator H_bd p := by
      rw [← integral_indicator hm3,
        ← (integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (S₃.indicator H_bd)).symm,
        map_volume_neg_both]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have hLHS : S₃.indicator H_bd (e p) = (e ⁻¹' S₃).indicator (fun q => H_bd (e q)) p := by
        by_cases h : p ∈ e ⁻¹' S₃ <;> simp [Set.indicator, h]
      rw [hLHS, hS4_ae, hS4_set]
    rw [he1, integral_indicator hm4]
  have hu1 : ∫ p in S₁ ∪ S₂, H_bd p = ∫ p in S₁, H_bd p + ∫ p in S₂, H_bd p :=
    setIntegral_union hd12 hm2 hH_int.integrableOn hH_int.integrableOn
  have hu2 : ∫ p in S₁ ∪ S₂ ∪ S₃, H_bd p = ∫ p in S₁ ∪ S₂, H_bd p + ∫ p in S₃, H_bd p :=
    setIntegral_union hd123 hm3 hH_int.integrableOn hH_int.integrableOn
  have hu3 : ∫ p in S₁ ∪ S₂ ∪ S₃ ∪ S₄, H_bd p = ∫ p in S₁ ∪ S₂ ∪ S₃, H_bd p + ∫ p in S₄, H_bd p :=
    setIntegral_union hd1234 hm4 hH_int.integrableOn hH_int.integrableOn
  have hu_all : ∫ p : ℝ × ℝ, H_bd p = ∫ p in S₁ ∪ S₂ ∪ S₃ ∪ S₄, H_bd p := by
    rw [← setIntegral_univ, huniv]
  linarith only [hu1, hu2, hu3, hu_all, hS1_eq, hS2_eq, hS3_eq, hS4_eq, hK_split]

end FormalResearch.ModularBootstrap.Spin

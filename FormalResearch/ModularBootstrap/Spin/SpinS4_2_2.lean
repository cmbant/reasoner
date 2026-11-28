module

public import FormalResearch.ModularBootstrap.Spin.ScalC1
public import FormalResearch.ModularBootstrap.Spin.SpinS4Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS2xS23

/-!
# SPIN-S4 Lemma `s4:2.2` and Calibrated Adjoint Identities

Proves:
1. `spinCalPhic_neg`, `spinRc_le_abs`: for `2 ≤ a` and EVERY `p : ℝ × ℝ`,
   `0 ≤ spinRc a ((p.1 + p.2)/2) ((p.1 - p.2)/2) ≤ spinRc a ((|p.1| + |p.2|)/2) ((|p.1| - |p.2|)/2)`.
2. **`spinS4_2_2 : SpinS4_2_2`** (`spinning_s4.tex`, Lemma 2.2) from `scalC1`.
3. Exact calibrated adjoint identities (`s4:eP.0`, `s4:eR.6`) expressing `spinCalInt c Φ`
   and weighted integrals of `spinCalProjFn` via `spinRc1` and `spinRc2`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

private lemma spinGamma_sq_sub_one {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ 1 - spinGamma a ∧ spinGamma a ≤ 1 := by
  have hg1 : spinGamma a ≤ 1 := by
    unfold spinGamma
    exact Real.sqrt_le_one.mpr (by linarith [div_nonneg two_pos.le (by positivity : 0 ≤ a)])
  exact ⟨sub_nonneg.mpr hg1, hg1⟩

private lemma spinCalFc_neg {a : ℝ} (_ha : 2 ≤ a) (r : ℝ) :
    spinCalFc a (-r) = Real.exp (8 * π * a * r) * spinCalFc a r := by
  unfold spinCalFc
  set u1 : ℝ := π * (12 * a) * (1 + spinGamma a) * r / 3
  set u2 : ℝ := π * (12 * a) * (1 - spinGamma a) * r / 3
  have hsum : u1 + u2 = 8 * π * a * r := by dsimp [u1, u2]; ring
  have hn1 : -π * (12 * a) * (1 + spinGamma a) * (-r) / 3 = u1 := by dsimp [u1]; ring
  have hn2 : -π * (12 * a) * (1 - spinGamma a) * (-r) / 3 = u2 := by dsimp [u2]; ring
  have hm1 : -π * (12 * a) * (1 + spinGamma a) * r / 3 = -u1 := by dsimp [u1]; ring
  have hm2 : -π * (12 * a) * (1 - spinGamma a) * r / 3 = -u2 := by dsimp [u2]; ring
  rw [hn1, hn2, hm1, hm2]
  have e1 : 1 - Real.exp u1 = -(Real.exp u1 * (1 - Real.exp (-u1))) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
  have e2 : 1 - Real.exp u2 = -(Real.exp u2 * (1 - Real.exp (-u2))) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
  calc (1 - Real.exp u1) * (1 - Real.exp u2)
      = (-(Real.exp u1 * (1 - Real.exp (-u1)))) * (-(Real.exp u2 * (1 - Real.exp (-u2)))) := by
        rw [e1, e2]
    _ = (Real.exp u1 * Real.exp u2) * ((1 - Real.exp (-u1)) * (1 - Real.exp (-u2))) := by ring
    _ = Real.exp (8 * π * a * r) * ((1 - Real.exp (-u1)) * (1 - Real.exp (-u2))) := by
        rw [← Real.exp_add, hsum]

private lemma spinCalPhic_neg {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    spinCalPhic a (-r) = Real.exp (-8 * π * a * r) * spinCalPhic a r := by
  by_cases hr : r = 0
  · subst hr; simp [spinCalPhic]
  · have hnr : -r ≠ 0 := neg_ne_zero.mpr hr
    unfold spinCalPhic
    simp only [hnr, hr, ite_false]
    rw [show -r / 2 = -(r / 2) by ring, Real.tanh_neg, neg_sq, spinCalFc_neg ha r]
    calc Real.tanh (r / 2) ^ 2 / (Real.exp (8 * π * a * r) * spinCalFc a r)
        = (Real.exp (8 * π * a * r))⁻¹ * (Real.tanh (r / 2) ^ 2 / spinCalFc a r) := by
          rw [div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = Real.exp (-8 * π * a * r) * (Real.tanh (r / 2) ^ 2 / spinCalFc a r) := by
          rw [← Real.exp_neg, show -(8 * π * a * r) = -8 * π * a * r by ring]

private lemma spinCalPhic_nonneg' {a : ℝ} (ha : 2 ≤ a) (x : ℝ) : 0 ≤ spinCalPhic a x := by
  rcases le_total 0 x with hx | hx
  · unfold spinCalPhic
    split_ifs with hx0
    · exact le_rfl
    · have h1 : 0 ≤ Real.tanh (x / 2) ^ 2 := sq_nonneg _
      have ha0 : 0 < a := by linarith
      have hg0 : 0 ≤ spinGamma a := Real.sqrt_nonneg _
      have hg1 : spinGamma a ≤ 1 := (spinGamma_sq_sub_one ha).2
      have hfc_nn : 0 ≤ spinCalFc a x := by
        unfold spinCalFc
        have h1e : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have : 0 ≤ π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
            linarith)
        have h2e : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have h1g : 0 ≤ 1 - spinGamma a := sub_nonneg.mpr hg1
            have : 0 ≤ π * (12 * a) * (1 - spinGamma a) * x / 3 := by positivity
            linarith)
        exact mul_nonneg (sub_nonneg.mpr h1e) (sub_nonneg.mpr h2e)
      exact div_nonneg h1 hfc_nn
  · have heq : x = -(-x) := by ring
    rw [heq, spinCalPhic_neg ha (-x)]
    refine mul_nonneg (Real.exp_pos _).le ?_
    unfold spinCalPhic
    split_ifs with hx0
    · exact le_rfl
    · have h1 : 0 ≤ Real.tanh (-x / 2) ^ 2 := sq_nonneg _
      have ha0 : 0 ≤ a := by linarith
      have hg0 : 0 ≤ spinGamma a := Real.sqrt_nonneg _
      have hg1 : spinGamma a ≤ 1 := (spinGamma_sq_sub_one ha).2
      have hfc_nn : 0 ≤ spinCalFc a (-x) := by
        unfold spinCalFc
        have hnx : 0 ≤ -x := by linarith
        have h1e : Real.exp (-π * (12 * a) * (1 + spinGamma a) * (-x) / 3) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have : 0 ≤ π * (12 * a) * (1 + spinGamma a) * (-x) / 3 := by positivity
            linarith)
        have h2e : Real.exp (-π * (12 * a) * (1 - spinGamma a) * (-x) / 3) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have h1g : 0 ≤ 1 - spinGamma a := sub_nonneg.mpr hg1
            have : 0 ≤ π * (12 * a) * (1 - spinGamma a) * (-x) / 3 := by positivity
            linarith)
        exact mul_nonneg (sub_nonneg.mpr h1e) (sub_nonneg.mpr h2e)
      exact div_nonneg h1 hfc_nn

private lemma spinRc_nonneg_all {a : ℝ} (ha : 2 ≤ a) (ξ d : ℝ) : 0 ≤ spinRc a ξ d := by
  have hphi_nn : ∀ y, 0 ≤ spinCalPhic a y := spinCalPhic_nonneg' ha
  unfold spinRc spinRc1 spinRc2
  have h1 : 0 ≤ (1 + xiStar ^ 2) / (1 + ξ ^ 2) *
      (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) / spinCalPhi xiStar ^ 2) *
      Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (ξ ^ 2 - xiStar ^ 2) ^ 2) :=
    mul_nonneg (mul_nonneg (div_nonneg (add_nonneg zero_le_one (sq_nonneg _))
      (add_nonneg zero_le_one (sq_nonneg _)))
      (div_nonneg (mul_nonneg (hphi_nn _) (hphi_nn _)) (sq_nonneg _))) (Real.exp_pos _).le
  have h2 : 0 ≤ Real.exp (-(12 * a) * (2 * π / 3) * (ξ - |d|)) *
      ((1 + xiStar ^ 2) / (1 + d ^ 2)) *
      (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) / spinCalPhi xiStar ^ 2) *
      Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (d ^ 2 - xiStar ^ 2) ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (div_nonneg (add_nonneg zero_le_one (sq_nonneg _)) (add_nonneg zero_le_one (sq_nonneg _))))
      (div_nonneg (mul_nonneg (hphi_nn _) (hphi_nn _)) (sq_nonneg _))) (Real.exp_pos _).le
  exact add_nonneg h1 h2

lemma spinRc_le_abs {a : ℝ} (ha : 2 ≤ a) (p : ℝ × ℝ) :
    spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) ≤
      spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) := by
  rcases p with ⟨x, y⟩
  set ξ := (x + y) / 2
  set d := (x - y) / 2
  set ξ' := (|x| + |y|) / 2
  set d' := (|x| - |y|) / 2
  have hsum : ξ + d = x := by dsimp [ξ, d]; ring
  have hdiff : ξ - d = y := by dsimp [ξ, d]; ring
  have hsum' : ξ' + d' = |x| := by dsimp [ξ', d']; ring
  have hdiff' : ξ' - d' = |y| := by dsimp [ξ', d']; ring
  have hphi_nn : ∀ z, 0 ≤ spinCalPhic a z := spinCalPhic_nonneg' ha
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · -- Quadrant I: x ≥ 0, y ≥ 0
    dsimp [ξ, d, ξ', d']
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · -- Quadrant IV: x ≥ 0, y ≤ 0
    have hy' : |y| = -y := abs_of_nonpos hy
    have hx' : |x| = x := abs_of_nonneg hx
    have hξd_eq : ξ - |d| = -|y| := by
      dsimp [ξ, d]; rw [abs_of_nonneg (by linarith)]; linarith [hy']
    have hξ2 : ξ ^ 2 = d' ^ 2 := by dsimp [ξ, d']; rw [hx', hy']; ring
    have hd2 : d ^ 2 = ξ' ^ 2 := by dsimp [d, ξ']; rw [hx', hy']; ring
    have hφ_prod : spinCalPhic a x * spinCalPhic a y =
        Real.exp (-8 * π * a * |y|) * (spinCalPhic a |x| * spinCalPhic a |y|) := by
      have hy_neg : y = -|y| := by linarith [hy']
      conv_lhs => rw [hy_neg, spinCalPhic_neg ha |y|]
      rw [hx']; ring
    have hr2_eq : spinRc2 a ξ d = spinRc1 a ξ' d' := by
      unfold spinRc2 spinRc1
      rw [hsum, hdiff, hsum', hdiff', hξd_eq, hξ2, hd2, hφ_prod]
      have hexp : Real.exp (-(12 * a) * (2 * π / 3) * -|y|) * Real.exp (-8 * π * a * |y|) = 1 := by
        rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
      calc Real.exp (-(12 * a) * (2 * π / 3) * -|y|) * ((1 + xiStar ^ 2) / (1 + ξ' ^ 2)) *
            (Real.exp (-8 * π * a * |y|) * (spinCalPhic a |x| * spinCalPhic a |y|) / spinCalPhi xiStar ^ 2) *
            Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (ξ' ^ 2 - xiStar ^ 2) ^ 2)
          = (Real.exp (-(12 * a) * (2 * π / 3) * -|y|) * Real.exp (-8 * π * a * |y|)) *
              ((1 + xiStar ^ 2) / (1 + ξ' ^ 2) *
                (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
                Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                  (ξ' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ = _ := by rw [hexp, one_mul]
    have hr1_le : spinRc1 a ξ d ≤ spinRc2 a ξ' d' := by
      unfold spinRc1 spinRc2
      rw [hsum, hdiff, hsum', hdiff', hξ2, hd2, hφ_prod]
      have hsub_le : ξ' - |d'| ≤ |y| := by
        dsimp [ξ', d']
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rcases le_total |x| |y| with hxy | hxy
        · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; linarith
        · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith
      have hexp_le : Real.exp (-8 * π * a * |y|) ≤ Real.exp (-(12 * a) * (2 * π / 3) * (ξ' - |d'|)) := by
        refine Real.exp_le_exp.mpr ?_
        have ha0 : 0 ≤ a := by linarith
        have : 8 * π * a * (ξ' - |d'|) ≤ 8 * π * a * |y| :=
          mul_le_mul_of_nonneg_left hsub_le (by positivity)
        linarith
      have hfac_nn : 0 ≤ (1 + xiStar ^ 2) / (1 + d' ^ 2) *
          (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
          Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (d' ^ 2 - xiStar ^ 2) ^ 2) :=
        mul_nonneg (mul_nonneg (div_nonneg (add_nonneg zero_le_one (sq_nonneg _))
          (add_nonneg zero_le_one (sq_nonneg _)))
          (div_nonneg (mul_nonneg (hphi_nn _) (hphi_nn _)) (sq_nonneg _))) (Real.exp_pos _).le
      calc (1 + xiStar ^ 2) / (1 + d' ^ 2) *
            (Real.exp (-8 * π * a * |y|) * (spinCalPhic a |x| * spinCalPhic a |y|) / spinCalPhi xiStar ^ 2) *
            Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (d' ^ 2 - xiStar ^ 2) ^ 2)
          = Real.exp (-8 * π * a * |y|) * ((1 + xiStar ^ 2) / (1 + d' ^ 2) *
              (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
              Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (d' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ ≤ Real.exp (-(12 * a) * (2 * π / 3) * (ξ' - |d'|)) * _ :=
            mul_le_mul_of_nonneg_right hexp_le hfac_nn
        _ = _ := by ring
    unfold spinRc; linarith
  · -- Quadrant II: x ≤ 0, y ≥ 0
    have hx' : |x| = -x := abs_of_nonpos hx
    have hy' : |y| = y := abs_of_nonneg hy
    have hξd_eq : ξ - |d| = -|x| := by
      dsimp [ξ, d]; rw [abs_of_nonpos (by linarith)]; linarith [hx']
    have hξ2 : ξ ^ 2 = d' ^ 2 := by dsimp [ξ, d']; rw [hx', hy']; ring
    have hd2 : d ^ 2 = ξ' ^ 2 := by dsimp [d, ξ']; rw [hx', hy']; ring
    have hφ_prod : spinCalPhic a x * spinCalPhic a y =
        Real.exp (-8 * π * a * |x|) * (spinCalPhic a |x| * spinCalPhic a |y|) := by
      have hx_neg : x = -|x| := by linarith [hx']
      conv_lhs => rw [hx_neg, spinCalPhic_neg ha |x|]
      rw [hy']; ring
    have hr2_eq : spinRc2 a ξ d = spinRc1 a ξ' d' := by
      unfold spinRc2 spinRc1
      rw [hsum, hdiff, hsum', hdiff', hξd_eq, hξ2, hd2, hφ_prod]
      have hexp : Real.exp (-(12 * a) * (2 * π / 3) * -|x|) * Real.exp (-8 * π * a * |x|) = 1 := by
        rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
      calc Real.exp (-(12 * a) * (2 * π / 3) * -|x|) * ((1 + xiStar ^ 2) / (1 + ξ' ^ 2)) *
            (Real.exp (-8 * π * a * |x|) * (spinCalPhic a |x| * spinCalPhic a |y|) / spinCalPhi xiStar ^ 2) *
            Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (ξ' ^ 2 - xiStar ^ 2) ^ 2)
          = (Real.exp (-(12 * a) * (2 * π / 3) * -|x|) * Real.exp (-8 * π * a * |x|)) *
              ((1 + xiStar ^ 2) / (1 + ξ' ^ 2) *
                (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
                Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                  (ξ' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ = _ := by rw [hexp, one_mul]
    have hr1_le : spinRc1 a ξ d ≤ spinRc2 a ξ' d' := by
      unfold spinRc1 spinRc2
      rw [hsum, hdiff, hsum', hdiff', hξ2, hd2, hφ_prod]
      have hsub_le : ξ' - |d'| ≤ |x| := by
        dsimp [ξ', d']
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rcases le_total |x| |y| with hxy | hxy
        · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; linarith
        · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith
      have hexp_le : Real.exp (-8 * π * a * |x|) ≤ Real.exp (-(12 * a) * (2 * π / 3) * (ξ' - |d'|)) := by
        refine Real.exp_le_exp.mpr ?_
        have ha0 : 0 ≤ a := by linarith
        have : 8 * π * a * (ξ' - |d'|) ≤ 8 * π * a * |x| :=
          mul_le_mul_of_nonneg_left hsub_le (by positivity)
        linarith
      have hfac_nn : 0 ≤ (1 + xiStar ^ 2) / (1 + d' ^ 2) *
          (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
          Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (d' ^ 2 - xiStar ^ 2) ^ 2) :=
        mul_nonneg (mul_nonneg (div_nonneg (add_nonneg zero_le_one (sq_nonneg _))
          (add_nonneg zero_le_one (sq_nonneg _)))
          (div_nonneg (mul_nonneg (hphi_nn _) (hphi_nn _)) (sq_nonneg _))) (Real.exp_pos _).le
      calc (1 + xiStar ^ 2) / (1 + d' ^ 2) *
            (Real.exp (-8 * π * a * |x|) * (spinCalPhic a |x| * spinCalPhic a |y|) / spinCalPhi xiStar ^ 2) *
            Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (d' ^ 2 - xiStar ^ 2) ^ 2)
          = Real.exp (-8 * π * a * |x|) * ((1 + xiStar ^ 2) / (1 + d' ^ 2) *
              (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
              Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (d' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ ≤ Real.exp (-(12 * a) * (2 * π / 3) * (ξ' - |d'|)) * _ :=
            mul_le_mul_of_nonneg_right hexp_le hfac_nn
        _ = _ := by ring
    unfold spinRc; linarith
  · -- Quadrant III: x ≤ 0, y ≤ 0
    have hx' : |x| = -x := abs_of_nonpos hx
    have hy' : |y| = -y := abs_of_nonpos hy
    have hξ_sq : ξ ^ 2 = ξ' ^ 2 := by dsimp [ξ, ξ']; rw [hx', hy']; ring
    have hd_sq : d ^ 2 = d' ^ 2 := by dsimp [d, d']; rw [hx', hy']; ring
    have hξd_eq : ξ - |d| = -(ξ' + |d'|) := by
      have hξm : ξ = -ξ' := by dsimp [ξ, ξ']; linarith [hx', hy']
      have hd_abs : |d| = |d'| := by dsimp [d, d']; rw [hx', hy', ← abs_neg]; congr 1; ring
      linarith
    have hφ_prod : spinCalPhic a x * spinCalPhic a y =
        Real.exp (-8 * π * a * (|x| + |y|)) * (spinCalPhic a |x| * spinCalPhic a |y|) := by
      have hx_neg : x = -|x| := by linarith [hx']
      have hy_neg : y = -|y| := by linarith [hy']
      conv_lhs => rw [hx_neg, hy_neg, spinCalPhic_neg ha |x|, spinCalPhic_neg ha |y|]
      calc (Real.exp (-8 * π * a * |x|) * spinCalPhic a |x|) *
              (Real.exp (-8 * π * a * |y|) * spinCalPhic a |y|)
          = (Real.exp (-8 * π * a * |x|) * Real.exp (-8 * π * a * |y|)) *
              (spinCalPhic a |x| * spinCalPhic a |y|) := by ring
        _ = Real.exp (-8 * π * a * (|x| + |y|)) * (spinCalPhic a |x| * spinCalPhic a |y|) := by
            rw [← Real.exp_add]; congr 2; ring
    have hexp1 : Real.exp (-8 * π * a * (|x| + |y|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have ha0 : 0 ≤ a := by linarith
        have : 0 ≤ 8 * π * a * (|x| + |y|) := by positivity
        linarith)
    have hr1_le : spinRc1 a ξ d ≤ spinRc1 a ξ' d' := by
      unfold spinRc1
      rw [hsum, hdiff, hsum', hdiff', hξ_sq, hd_sq, hφ_prod]
      have hfac_nn : 0 ≤ (1 + xiStar ^ 2) / (1 + ξ' ^ 2) *
          (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
          Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (ξ' ^ 2 - xiStar ^ 2) ^ 2) :=
        mul_nonneg (mul_nonneg (div_nonneg (add_nonneg zero_le_one (sq_nonneg _))
          (add_nonneg zero_le_one (sq_nonneg _)))
          (div_nonneg (mul_nonneg (hphi_nn _) (hphi_nn _)) (sq_nonneg _))) (Real.exp_pos _).le
      calc (1 + xiStar ^ 2) / (1 + ξ' ^ 2) *
            (Real.exp (-8 * π * a * (|x| + |y|)) * (spinCalPhic a |x| * spinCalPhic a |y|) /
              spinCalPhi xiStar ^ 2) *
            Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (ξ' ^ 2 - xiStar ^ 2) ^ 2)
          = Real.exp (-8 * π * a * (|x| + |y|)) * ((1 + xiStar ^ 2) / (1 + ξ' ^ 2) *
              (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
              Real.exp (-d' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                (ξ' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hexp1 hfac_nn
        _ = _ := one_mul _
    have hr2_eq : spinRc2 a ξ d = spinRc2 a ξ' d' := by
      unfold spinRc2
      rw [hsum, hdiff, hsum', hdiff', hξ_sq, hd_sq, hξd_eq, hφ_prod]
      have hexp2 : Real.exp (-(12 * a) * (2 * π / 3) * -(ξ' + |d'|)) *
          Real.exp (-8 * π * a * (|x| + |y|)) =
          Real.exp (-(12 * a) * (2 * π / 3) * (ξ' - |d'|)) := by
        rw [← Real.exp_add]; congr 1
        have hxy2 : |x| + |y| = 2 * ξ' := by dsimp [ξ']; ring
        rw [hxy2]; ring
      calc Real.exp (-(12 * a) * (2 * π / 3) * -(ξ' + |d'|)) * ((1 + xiStar ^ 2) / (1 + d' ^ 2)) *
            (Real.exp (-8 * π * a * (|x| + |y|)) * (spinCalPhic a |x| * spinCalPhic a |y|) /
              spinCalPhi xiStar ^ 2) *
            Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (d' ^ 2 - xiStar ^ 2) ^ 2)
          = (Real.exp (-(12 * a) * (2 * π / 3) * -(ξ' + |d'|)) * Real.exp (-8 * π * a * (|x| + |y|))) *
              ((1 + xiStar ^ 2) / (1 + d' ^ 2) *
                (spinCalPhic a |x| * spinCalPhic a |y| / spinCalPhi xiStar ^ 2) *
                Real.exp (-ξ' ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d' ^ 2 - xiStar ^ 2) / (2 * xiStar) -
                  (d' ^ 2 - xiStar ^ 2) ^ 2)) := by ring
        _ = _ := by rw [hexp2]; ring
    unfold spinRc; linarith

private lemma one_sub_exp_ge_min {u : ℝ} (hu : 0 ≤ u) :
    (1 - Real.exp (-1)) * min u 1 ≤ 1 - Real.exp (-u) := by
  rcases le_or_gt u 1 with hu1 | hu1
  · rw [min_eq_left hu1]
    have hconv := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-1 : ℝ))
      (sub_nonneg.mpr hu1) hu (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at hconv
    linarith
  · rw [min_eq_right hu1.le]
    have : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    linarith

lemma spinS4_2_2_abs_bound :
    ∃ (c_σ C : ℝ), 0 < c_σ ∧ 0 < C ∧
      ∀ {c : ℝ}, 40 ≤ c →
        let n := c - 1
        let a := n / 12
        ∀ p : ℝ × ℝ,
          c_σ * min (spinTransDist p ^ 2) 1 - C / n ≤
            1 - spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) ∧
          c_σ * min (spinTransDist p ^ 2) 1 - C / n ≤
            1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) ∧
          |spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2)| ≤ 1 + C / n := by
  obtain ⟨C, _, _, hC_pos, _, _, hC1⟩ := scalC1
  let c_σ : ℝ := 1 - Real.exp (-1)
  have hc_pos : 0 < c_σ := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  refine ⟨c_σ, C, hc_pos, hC_pos, fun {c} hc p => ?_⟩
  let n := c - 1
  let a := n / 12
  have ha2 : 2 ≤ a := by dsimp [a, n]; linarith
  have hhd : |(|p.1| - |p.2|) / 2| ≤ (|p.1| + |p.2|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine div_le_div_of_nonneg_right ?_ two_pos.le
    rcases le_total |p.1| |p.2| with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg p.1]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg p.2]
  obtain ⟨⟨h0, hub⟩, _⟩ := hC1 hc ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) hhd
  have hd_eq : ((|p.1| - |p.2|) / 2) ^ 2 = spinTransDist p ^ 2 := by
    unfold spinTransDist
    rw [mul_pow, sq_abs]; ring
  have hexp_le : Real.exp (-(1 / 2 : ℝ) * (((|p.1| + |p.2|) / 2) ^ 2 - xiStar ^ 2) ^ 2 -
      ((|p.1| - |p.2|) / 2) ^ 2 / spinSigma0 ^ 2) ≤
      Real.exp (-(spinTransDist p ^ 2 / spinSigma0 ^ 2)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [← hd_eq]
    have hnn : 0 ≤ (1 / 2 : ℝ) * (((|p.1| + |p.2|) / 2) ^ 2 - xiStar ^ 2) ^ 2 := by positivity
    linarith [hnn]
  have hmin_le : min (spinTransDist p ^ 2) 1 ≤ min (spinTransDist p ^ 2 / spinSigma0 ^ 2) 1 := by
    have hdiv : spinTransDist p ^ 2 ≤ spinTransDist p ^ 2 / spinSigma0 ^ 2 := by
      have : spinSigma0 ^ 2 = (1 / 400 : ℝ) := by unfold spinSigma0; norm_num
      rw [this]; linarith [sq_nonneg (spinTransDist p)]
    exact min_le_min_right 1 hdiv
  have h1_sub : c_σ * min (spinTransDist p ^ 2) 1 ≤
      1 - Real.exp (-(spinTransDist p ^ 2 / spinSigma0 ^ 2)) := by
    calc c_σ * min (spinTransDist p ^ 2) 1
        ≤ c_σ * min (spinTransDist p ^ 2 / spinSigma0 ^ 2) 1 :=
          mul_le_mul_of_nonneg_left hmin_le hc_pos.le
      _ ≤ 1 - Real.exp (-(spinTransDist p ^ 2 / spinSigma0 ^ 2)) :=
          one_sub_exp_ge_min (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hub' : spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) ≤
      Real.exp (-(spinTransDist p ^ 2 / spinSigma0 ^ 2)) + C / n :=
    hub.trans (add_le_add hexp_le (le_refl _))
  have hRc_le : spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) ≤
      spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) := spinRc_le_abs ha2 p
  have hexp_le1 : Real.exp (-(spinTransDist p ^ 2 / spinSigma0 ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_of_nonneg h0]
  linarith

/-- **`s4:2.2` (Lemma 2.2, positive-mass angular-variance penalty).** -/
theorem spinS4_2_2 : SpinS4_2_2 := by
  obtain ⟨c_σ, C, hc_pos, hC_pos, hpt_all⟩ := spinS4_2_2_abs_bound
  refine ⟨c_σ, C, 40, hc_pos, hC_pos, le_rfl, fun {c} hc {Φ} hΦ hM2 => ?_⟩
  let n := c - 1
  let a := n / 12
  have ha0 : 0 < a := by dsimp [a, n]; linarith
  have ha2 : 2 ≤ a := by dsimp [a, n]; linarith
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hM_int : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) :=
    integrable_spinG_wc ha0 hΦ
  have hG_cont : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG
    exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hmax_int : Integrable (fun p : ℝ × ℝ => max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by
    refine hM_int.mono' (((hG_cont.max continuous_const).mul
        (hWc_cont.comp continuous_fst)).mul (hWc_cont.comp continuous_snd) |>.aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    have hnn : 0 ≤ max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
    rw [Real.norm_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
      (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
  have hmax_le1 : ∫ p : ℝ × ℝ, max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤ 1 := by
    rw [← hM2, spinM2_eq_spinWc ha0 Φ]
    refine integral_mono hmax_int hM_int fun p => ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
      (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
  have hmax_nn : 0 ≤ ∫ p : ℝ × ℝ, max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
  have hV_int : Integrable (fun p : ℝ × ℝ =>
      min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by
    have hcont_d : Continuous (fun p : ℝ × ℝ => spinTransDist p) := by
      unfold spinTransDist
      exact continuous_const.mul
        ((continuous_abs.comp continuous_fst).sub (continuous_abs.comp continuous_snd)).abs
    have hcont_v : Continuous (fun p : ℝ × ℝ => min (spinTransDist p ^ 2) 1) :=
      (hcont_d.pow 2).min continuous_const
    refine hmax_int.mono' ((((hcont_v.mul (hG_cont.max continuous_const)).mul
        (hWc_cont.comp continuous_fst)).mul (hWc_cont.comp continuous_snd)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    have hv_nn : 0 ≤ min (spinTransDist p ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    have hv_le1 : min (spinTransDist p ^ 2) 1 ≤ 1 := min_le_right _ _
    have hbase_nn : 0 ≤ max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
    have hprod_nn : 0 ≤ min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 *
        spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hv_nn (le_max_right (spinG a Φ p.1 p.2) 0))
        (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
    rw [Real.norm_of_nonneg hprod_nn]
    calc min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
        = min (spinTransDist p ^ 2) 1 * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by ring
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hv_le1 hbase_nn
      _ = _ := one_mul _
  have hRc_int : Integrable (fun p : ℝ × ℝ =>
      (1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)) *
        max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by
    have hmeas_calphi : Measurable (spinCalPhic a) := by
      unfold spinCalPhic spinCalFc
      have hdiv : Measurable (fun x : ℝ => Real.tanh (x / 2) ^ 2 /
          ((1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3)) *
           (1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3)))) := by
        refine Measurable.div ?_ ?_
        · have htanh : Continuous (fun x : ℝ => Real.tanh (x / 2)) := by
            rw [show (fun x : ℝ => Real.tanh (x / 2)) = fun x => Real.sinh (x / 2) / Real.cosh (x / 2) from
              funext fun x => Real.tanh_eq_sinh_div_cosh _]
            exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).div
              (Real.continuous_cosh.comp (continuous_id.div_const 2))
              (fun x => (Real.cosh_pos _).ne')
          exact htanh.measurable.pow_const 2
        · fun_prop
      exact Measurable.ite (measurableSet_singleton 0) measurable_const hdiv
    have hmeas_rc : Measurable (fun p : ℝ × ℝ => spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)) := by
      unfold spinRc spinRc1 spinRc2
      have hξ : Measurable (fun p : ℝ × ℝ => (p.1 + p.2) / 2) :=
        (measurable_fst.add measurable_snd).div_const 2
      have hd : Measurable (fun p : ℝ × ℝ => (p.1 - p.2) / 2) :=
        (measurable_fst.sub measurable_snd).div_const 2
      have hx : Measurable (fun p : ℝ × ℝ => (p.1 + p.2) / 2 + (p.1 - p.2) / 2) := hξ.add hd
      have hy : Measurable (fun p : ℝ × ℝ => (p.1 + p.2) / 2 - (p.1 - p.2) / 2) := hξ.sub hd
      have hp1 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((p.1 + p.2) / 2 + (p.1 - p.2) / 2)) :=
        hmeas_calphi.comp hx
      have hp2 : Measurable (fun p : ℝ × ℝ => spinCalPhic a ((p.1 + p.2) / 2 - (p.1 - p.2) / 2)) :=
        hmeas_calphi.comp hy
      have h1 : Measurable (fun p : ℝ × ℝ => (1 + xiStar ^ 2) / (1 + ((p.1 + p.2) / 2) ^ 2) *
          (spinCalPhic a ((p.1 + p.2) / 2 + (p.1 - p.2) / 2) *
            spinCalPhic a ((p.1 + p.2) / 2 - (p.1 - p.2) / 2) / spinCalPhi xiStar ^ 2) *
          Real.exp (-((p.1 - p.2) / 2) ^ 2 / spinSigma0 ^ 2 -
            spinAlpha1 * (((p.1 + p.2) / 2) ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (((p.1 + p.2) / 2) ^ 2 - xiStar ^ 2) ^ 2)) := by
        refine ((((measurable_const.div (measurable_const.add (hξ.pow_const 2))).mul
          ((hp1.mul hp2).div_const _))).mul ?_)
        exact Real.measurable_exp.comp (((((hd.pow_const 2).neg.div_const _).sub
          (((measurable_const.mul ((hξ.pow_const 2).sub measurable_const))).div_const _))).sub
            (((hξ.pow_const 2).sub measurable_const).pow_const 2))
      have h2 : Measurable (fun p : ℝ × ℝ =>
          Real.exp (-(12 * a) * (2 * π / 3) * ((p.1 + p.2) / 2 - |(p.1 - p.2) / 2|)) *
          ((1 + xiStar ^ 2) / (1 + ((p.1 - p.2) / 2) ^ 2)) *
          (spinCalPhic a ((p.1 + p.2) / 2 + (p.1 - p.2) / 2) *
            spinCalPhic a ((p.1 + p.2) / 2 - (p.1 - p.2) / 2) / spinCalPhi xiStar ^ 2) *
          Real.exp (-((p.1 + p.2) / 2) ^ 2 / spinSigma0 ^ 2 -
            spinAlpha1 * (((p.1 - p.2) / 2) ^ 2 - xiStar ^ 2) / (2 * xiStar) -
            (((p.1 - p.2) / 2) ^ 2 - xiStar ^ 2) ^ 2)) := by
        refine (((((Real.measurable_exp.comp (measurable_const.mul (hξ.sub hd.abs))).mul
          (measurable_const.div (measurable_const.add (hd.pow_const 2)))).mul
          ((hp1.mul hp2).div_const _))).mul ?_)
        exact Real.measurable_exp.comp (((((hξ.pow_const 2).neg.div_const _).sub
          (((measurable_const.mul ((hd.pow_const 2).sub measurable_const))).div_const _))).sub
            (((hd.pow_const 2).sub measurable_const).pow_const 2))
      exact h1.add h2
    refine (hmax_int.const_mul (1 + C / n)).mono'
      ((((measurable_const.sub hmeas_rc).mul (hG_cont.max continuous_const).measurable).mul
        (hWc_cont.comp continuous_fst).measurable).mul (hWc_cont.comp continuous_snd).measurable
        |>.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    have hbase_nn : 0 ≤ max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
    have hrc_nn : 0 ≤ spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) := spinRc_nonneg_all ha2 _ _
    have hrc_ub : spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) ≤ 1 + C / n := by
      have h1 := spinRc_le_abs ha2 p
      have h2 := (hpt_all hc p).2.2
      have h0 : 0 ≤ spinRc a ((|p.1| + |p.2|) / 2) ((|p.1| - |p.2|) / 2) := spinRc_nonneg_all ha2 _ _
      rw [abs_of_nonneg h0] at h2
      exact h1.trans h2
    have habs_rc : |1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)| ≤ 1 + C / n :=
      abs_le.mpr ⟨by linarith, by linarith [hrc_nn, div_nonneg hC_pos.le hn_pos.le]⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (le_max_right (spinG a Φ p.1 p.2) 0),
      abs_of_nonneg (spinWc_nonneg ha2 _), abs_of_nonneg (spinWc_nonneg ha2 _)]
    calc |1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)| *
            max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
        = |1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)| *
            (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by ring
      _ ≤ (1 + C / n) * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) :=
          mul_le_mul_of_nonneg_right habs_rc hbase_nn
      _ = (1 + C / n) * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := rfl
  have hlhs_int : Integrable (fun p : ℝ × ℝ =>
      c_σ * (min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) -
        (C / n) * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2)) :=
    (hV_int.const_mul c_σ).sub (hmax_int.const_mul (C / n))
  have hmono : ∫ p : ℝ × ℝ,
        (c_σ * (min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) -
          (C / n) * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2)) ≤
      ∫ p : ℝ × ℝ, (1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)) *
        max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 := by
    refine integral_mono hlhs_int hRc_int fun p => ?_
    have hpt := (hpt_all hc p).2.1
    have hbase_nn : 0 ≤ max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2 _)) (spinWc_nonneg ha2 _)
    calc c_σ * (min (spinTransDist p ^ 2) 1 * max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) -
          (C / n) * (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2)
        = (c_σ * min (spinTransDist p ^ 2) 1 - C / n) *
            (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) := by ring
      _ ≤ (1 - spinRc a ((p.1 + p.2) / 2) ((p.1 - p.2) / 2)) *
            (max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2) :=
          mul_le_mul_of_nonneg_right hpt hbase_nn
      _ = _ := by ring
  rw [integral_sub (hV_int.const_mul c_σ) (hmax_int.const_mul (C / n)),
    integral_const_mul, integral_const_mul] at hmono
  have hmax_Cn : (C / n) * ∫ p : ℝ × ℝ, max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤ C / n := by
    calc (C / n) * ∫ p : ℝ × ℝ, max (spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
        ≤ (C / n) * 1 := mul_le_mul_of_nonneg_left hmax_le1 (div_nonneg hC_pos.le hn_pos.le)
      _ = C / n := mul_one _
  unfold spinPosAngVar
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_2_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_2_2

end FormalResearch.ModularBootstrap.Spin

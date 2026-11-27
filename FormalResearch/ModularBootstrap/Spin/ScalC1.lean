module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proposition `scal:C1`: Calibrated Adjoint Ratio Bounds

Proves `ScalC1` (`spinning_calibration.tex`, Proposition `scal:C1`):
uniformly for `c ≥ 40` (`n = c - 1`, `a = n / 12`) and `|d| ≤ ξ`:
1. `0 ≤ spinRc a ξ d ≤ exp(-1/2 (ξ^2 - ξ_*^2)^2 - d^2 / σ_0^2) + C / n`,
2. for `|ξ - ξ_*| + |d| ≤ r_0`, `|spinRc a ξ d - 1| ≤ C_1 ((ξ - ξ_*)^2 + d^2 + n^{-1})`.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

section Helpers

private lemma spinCalF_pos {x : ℝ} (hx : 0 < x) : 0 < spinCalF x := by
  unfold spinCalF
  rw [sub_pos, Real.exp_lt_one_iff]
  have hpi : 0 < π := Real.pi_pos
  nlinarith

private lemma spinCalF_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ spinCalF x := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [spinCalF]
  · exact (spinCalF_pos hx0).le

private lemma tanh_half_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh (x / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le

private lemma tanh_half_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh (x / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)

private lemma tanh_half_le_one_sub_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh (x / 2) ≤ 1 - Real.exp (-x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hp : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hm : Real.exp (-(x / 2)) = Real.exp (-x) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp (x / 2) - Real.exp (-(x / 2)) = (1 - Real.exp (-x)) * Real.exp (x / 2) := by
    rw [hm]; ring
  have h2 : Real.exp (x / 2) + Real.exp (-(x / 2)) = (1 + Real.exp (-x)) * Real.exp (x / 2) := by
    rw [hm]; ring
  have hfrac : ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) /
      ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) =
      (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
    rw [h1, h2]
    field_simp [hp.ne']
  rw [hfrac]
  have hnn : 0 ≤ 1 - Real.exp (-x) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hden : 1 ≤ 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  exact div_le_self hnn hden

private lemma tanh_half_le_half {x : ℝ} (hx : 0 ≤ x) : Real.tanh (x / 2) ≤ x / 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  refine div_le_iff₀ (Real.cosh_pos _) |>.mpr ?_
  let g : ℝ → ℝ := fun u => u * Real.cosh u - Real.sinh u
  have hg_deriv : ∀ u : ℝ, HasDerivAt g (u * Real.sinh u) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
        (1 * Real.cosh u + u * Real.sinh u) u :=
      (hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)
    have h2 : HasDerivAt Real.sinh (Real.cosh u) u := Real.hasDerivAt_sinh u
    convert h1.sub h2 using 1
    ring
  have hg_mono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
    · intro u _; exact (hg_deriv u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
      rw [(hg_deriv u).deriv]
      exact mul_nonneg hu0 (Real.sinh_nonneg_iff.mpr hu0)
  have h0 : g 0 ≤ g (x / 2) := hg_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
  dsimp [g] at h0
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h0
  linarith

private lemma spinCalPhi_pos {x : ℝ} (hx : 0 < x) : 0 < spinCalPhi x := by
  unfold spinCalPhi
  exact div_pos (pow_pos (tanh_half_pos hx) 2) (spinCalF_pos hx)

private lemma spinCalPhi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ spinCalPhi x := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [spinCalPhi]
  · exact (spinCalPhi_pos hx0).le

private lemma spinCalPhi_le_one {x : ℝ} (hx : 0 ≤ x) : spinCalPhi x ≤ 1 := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [spinCalPhi]
  · unfold spinCalPhi
    refine (div_le_one (spinCalF_pos hx0)).mpr ?_
    have ht0 : 0 ≤ Real.tanh (x / 2) := tanh_half_nonneg hx
    have ht1 : Real.tanh (x / 2) ≤ 1 - Real.exp (-x) := tanh_half_le_one_sub_exp hx
    have hle1 : Real.tanh (x / 2) ≤ 1 := by linarith [Real.exp_pos (-x)]
    have hsq : Real.tanh (x / 2) ^ 2 ≤ Real.tanh (x / 2) := by nlinarith
    have hpi : (1 : ℝ) ≤ 4 * π := by linarith [Real.pi_gt_three]
    have hexp : Real.exp (-4 * π * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hF : 1 - Real.exp (-x) ≤ spinCalF x := by unfold spinCalF; linarith
    linarith

private lemma one_sub_exp_ge_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h1 : 1 ≤ (1 + t) * (1 - t / 2) := by nlinarith
  have hexp_ge : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : (1 + t) * (1 - t / 2) ≤ Real.exp t * (1 - t / 2) :=
    mul_le_mul_of_nonneg_right hexp_ge (by linarith)
  have h3 : Real.exp (-t) * 1 ≤ Real.exp (-t) * (Real.exp t * (1 - t / 2)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  rw [mul_one, ← mul_assoc, hexp, one_mul] at h3
  linarith

private lemma spinCalPhi_le_mul {x : ℝ} (hx : 0 ≤ x) : spinCalPhi x ≤ 4 * π * x := by
  have hpi : 0 < π := Real.pi_pos
  rcases le_total (1 / (4 * π)) x with hx_big | hx_small
  · have h1 : 1 ≤ 4 * π * x := by
      calc 1 = 4 * π * (1 / (4 * π)) := by field_simp [hpi.ne']
        _ ≤ 4 * π * x := by nlinarith
    exact (spinCalPhi_le_one hx).trans h1
  · rcases eq_or_lt_of_le hx with rfl | hx0
    · simp [spinCalPhi]
    · unfold spinCalPhi
      have ht0 : 0 ≤ Real.tanh (x / 2) := tanh_half_nonneg hx
      have ht_le : Real.tanh (x / 2) ≤ x / 2 := tanh_half_le_half hx
      have hsq : Real.tanh (x / 2) ^ 2 ≤ x ^ 2 / 4 := by nlinarith
      have ht4pi : 4 * π * x ≤ 1 := by
        calc 4 * π * x ≤ 4 * π * (1 / (4 * π)) := by nlinarith
          _ = 1 := by field_simp [hpi.ne']
      have hF : 2 * π * x ≤ spinCalF x := by
        unfold spinCalF
        have h := one_sub_exp_ge_half (by positivity : 0 ≤ 4 * π * x) ht4pi
        rw [show -(4 * π * x) = -4 * π * x by ring] at h
        linarith
      have hdiv : Real.tanh (x / 2) ^ 2 / spinCalF x ≤ (x ^ 2 / 4) / (2 * π * x) :=
        div_le_div₀ (by positivity) hsq (by positivity) hF
      have halg : (x ^ 2 / 4) / (2 * π * x) = x / (8 * π) := by
        field_simp [hpi.ne', hx0.ne']
        norm_num
      have h8pi : x / (8 * π) ≤ 4 * π * x := by
        have hgt : 1 ≤ 32 * π ^ 2 := by nlinarith [Real.pi_gt_three]
        have h1 : x ≤ 32 * π ^ 2 * x := by nlinarith
        exact (div_le_iff₀ (by positivity : 0 < 8 * π)).mpr (by linarith)
      linarith

private lemma spinCalFc_pos {a x : ℝ} (ha : 2 < a) (hx : 0 < x) : 0 < spinCalFc a x := by
  unfold spinCalFc
  have hγ0 : 0 < spinGamma a := spinGamma_pos ha
  have hγ1 : spinGamma a < 1 := spinGamma_lt_one ha
  have hpi : 0 < π := Real.pi_pos
  have ha0 : 0 < a := by linarith
  have h1 : 0 < 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have hp : 0 < π * (12 * a) * (1 + spinGamma a) * x / 3 := by positivity
    linarith
  have h2 : 0 < 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    have hsub : 0 < 1 - spinGamma a := sub_pos.mpr hγ1
    have hp : 0 < π * (12 * a) * (1 - spinGamma a) * x / 3 := by positivity
    linarith
  exact mul_pos h1 h2

private lemma spinCalPhic_nonneg {a x : ℝ} (ha : 2 < a) (hx : 0 ≤ x) : 0 ≤ spinCalPhic a x := by
  unfold spinCalPhic
  split_ifs with h
  · exact le_rfl
  · have hx0 : 0 < x := lt_of_le_of_ne hx (Ne.symm h)
    exact div_nonneg (sq_nonneg _) (spinCalFc_pos ha hx0).le

private lemma one_sub_exp_mul_le {r y : ℝ} (hr : 1 ≤ r) (hy : 0 ≤ y) :
    1 - Real.exp (-r * y) ≤ r * (1 - Real.exp (-y)) := by
  let f : ℝ → ℝ := fun t => r * (1 - Real.exp (-t)) - (1 - Real.exp (-r * t))
  have hf_deriv : ∀ t : ℝ, HasDerivAt f (r * (Real.exp (-t) - Real.exp (-r * t))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => r * (1 - Real.exp (-s))) (r * Real.exp (-t)) t := by
      have he : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
      convert ((hasDerivAt_const t 1).sub he.exp).const_mul r using 1
      ring
    have h2 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-r * s)) (r * Real.exp (-r * t)) t := by
      have hm : HasDerivAt (fun s : ℝ => -r * s) (-r) t := by
        simpa using (hasDerivAt_id t).const_mul (-r)
      convert (hasDerivAt_const t 1).sub hm.exp using 1
      ring
    convert h1.sub h2 using 1
    ring
  have hf_mono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact ((continuous_const.mul (continuous_const.sub continuous_neg.rexp)).sub
        (continuous_const.sub (continuous_const.mul continuous_id).rexp)).continuousOn
    · intro t _; exact (hf_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      rw [(hf_deriv t).deriv]
      have hexp : Real.exp (-r * t) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by nlinarith)
      exact mul_nonneg (by linarith) (sub_nonneg.mpr hexp)
  have h0 : f 0 ≤ f y := hf_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
  dsimp [f] at h0
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero] at h0
  linarith

private lemma spinCalPhic_upper {c x : ℝ} (hc : 40 ≤ c) (hx : 0 ≤ x) :
    spinCalPhic ((c - 1) / 12) x ≤ spinCalPhi x + 4 * π / (c - 1) := by
  let n : ℝ := c - 1
  let a : ℝ := n / 12
  have hn : 39 ≤ n := by dsimp [n]; linarith
  have ha : 2 < a := by dsimp [a, n]; linarith
  have hpi : 0 < π := Real.pi_pos
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [spinCalPhic, spinCalPhi]
    positivity
  · unfold spinCalPhic
    simp only [hx0.ne', ↓reduceIte]
    let α₁ : ℝ := π * (12 * a) * (1 + spinGamma a) / 3
    let α₂ : ℝ := π * (12 * a) * (1 - spinGamma a) / 3
    have hγ0 : 0 < spinGamma a := spinGamma_pos ha
    have hγ1 : spinGamma a < 1 := spinGamma_lt_one ha
    have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha.le
    have hα₁ : n ≤ α₁ := by
      have ha12 : 12 * a = n := by dsimp [a]; ring
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      have hpin : 0 ≤ π * n := by positivity
      have h1 : π * n * 1 / 3 ≤ π * n * (1 + spinGamma a) / 3 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (by linarith) hpin
      have h2 : n ≤ π * n / 3 := by nlinarith
      calc n ≤ π * n / 3 := h2
        _ = π * n * 1 / 3 := by ring
        _ ≤ π * (12 * a) * (1 + spinGamma a) / 3 := by rw [ha12]; exact h1
    have hα₂ : 4 * π ≤ α₂ := by
      have hdiff : 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := by nlinarith
      have h1γ : 1 / a < 1 - spinGamma a := by
        have ha0 : 0 < a := by linarith
        have hlt : 2 / a < (1 - spinGamma a) * 2 := by
          rw [hdiff]
          exact mul_lt_mul_of_pos_left (by linarith) (sub_pos.mpr hγ1)
        have : 2 < a * ((1 - spinGamma a) * 2) := by
          calc 2 = a * (2 / a) := by field_simp [ha0.ne']
            _ < a * ((1 - spinGamma a) * 2) := mul_lt_mul_of_pos_left hlt ha0
        have : 1 < a * (1 - spinGamma a) := by linarith
        calc 1 / a = a⁻¹ := one_div a
          _ < a⁻¹ * (a * (1 - spinGamma a)) := by nlinarith [inv_pos.mpr ha0]
          _ = 1 - spinGamma a := by field_simp [ha0.ne']
      dsimp [α₂]
      have ha0 : a ≠ 0 := by linarith
      have h1 : 4 * π = π * (12 * a) * (1 / a) / 3 := by
        field_simp [ha0]; ring
      rw [h1]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1γ.le (by positivity)) (by norm_num)
    let u : ℝ := n * x
    have hu_pos : 0 < u := by dsimp [u]; nlinarith
    have hFc1 : 1 - Real.exp (-u) ≤ 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) := by
      have he : -π * (12 * a) * (1 + spinGamma a) * x / 3 ≤ -u := by
        have heq : -π * (12 * a) * (1 + spinGamma a) * x / 3 = -α₁ * x := by dsimp [α₁]; ring
        rw [heq]; dsimp [u]; nlinarith
      linarith [Real.exp_le_exp.mpr he]
    have hFc2 : spinCalF x ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
      unfold spinCalF
      have he : -π * (12 * a) * (1 - spinGamma a) * x / 3 ≤ -4 * π * x := by
        have heq : -π * (12 * a) * (1 - spinGamma a) * x / 3 = -α₂ * x := by dsimp [α₂]; ring
        rw [heq]; nlinarith
      linarith [Real.exp_le_exp.mpr he]
    have hnx_pos : 0 < 1 - Real.exp (-u) := by
      rw [sub_pos, Real.exp_lt_one_iff]; linarith
    have hFc_lb : (1 - Real.exp (-u)) * spinCalF x ≤ spinCalFc a x := by
      unfold spinCalFc
      exact mul_le_mul hFc1 hFc2 (spinCalF_pos hx0).le (by linarith)
    have hdiv : Real.tanh (x / 2) ^ 2 / spinCalFc a x ≤
        spinCalPhi x / (1 - Real.exp (-u)) := by
      calc Real.tanh (x / 2) ^ 2 / spinCalFc a x
          ≤ Real.tanh (x / 2) ^ 2 / ((1 - Real.exp (-u)) * spinCalF x) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hnx_pos (spinCalF_pos hx0)) hFc_lb
        _ = spinCalPhi x / (1 - Real.exp (-u)) := by
            unfold spinCalPhi
            have hF0 : spinCalF x ≠ 0 := (spinCalF_pos hx0).ne'
            field_simp [hF0, hnx_pos.ne']
    have hrem : spinCalPhi x / (1 - Real.exp (-u)) - spinCalPhi x ≤ 4 * π / n := by
      have hexp_diff : 1 / (1 - Real.exp (-u)) - 1 =
          Real.exp (-u) / (1 - Real.exp (-u)) := by
        field_simp [hnx_pos.ne']; ring
      have he_gt1 : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu_pos
      have hne_sub : Real.exp u - 1 ≠ 0 := (sub_pos.mpr he_gt1).ne'
      have hexp_inv : Real.exp (-u) / (1 - Real.exp (-u)) = 1 / (Real.exp u - 1) := by
        have he : Real.exp (-u) * Real.exp u = 1 := by
          rw [← Real.exp_add]; simp
        field_simp [hnx_pos.ne', hne_sub]
        linear_combination he
      have h1 : spinCalPhi x / (1 - Real.exp (-u)) - spinCalPhi x =
          spinCalPhi x * (1 / (Real.exp u - 1)) := by
        rw [← hexp_inv, ← hexp_diff]; ring
      have h2 : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
      have h3 : 1 / (Real.exp u - 1) ≤ 1 / u :=
        one_div_le_one_div_of_le hu_pos h2
      calc spinCalPhi x / (1 - Real.exp (-u)) - spinCalPhi x
          = spinCalPhi x * (1 / (Real.exp u - 1)) := h1
        _ ≤ (4 * π * x) * (1 / u) :=
            mul_le_mul (spinCalPhi_le_mul hx) h3 (by positivity) (by positivity)
        _ = 4 * π / n := by dsimp [u]; field_simp [hx0.ne', (by linarith : n ≠ 0)]
    linarith

private lemma spinCalPhic_lower {c x : ℝ} (hc : 40 ≤ c) (hx : 0 ≤ x) :
    (1 - 24 / (c - 1)) * spinCalPhi x ≤ spinCalPhic ((c - 1) / 12) x := by
  let n : ℝ := c - 1
  let a : ℝ := n / 12
  have hn : 39 ≤ n := by dsimp [n]; linarith
  have ha : 2 < a := by dsimp [a, n]; linarith
  have hpi : 0 < π := Real.pi_pos
  rcases eq_or_lt_of_le hx with rfl | hx0
  · simp [spinCalPhic, spinCalPhi]
  · unfold spinCalPhic
    simp only [hx0.ne', ↓reduceIte]
    let α₂ : ℝ := π * (12 * a) * (1 - spinGamma a) / 3
    have hγ0 : 0 < spinGamma a := spinGamma_pos ha
    have hγ1 : spinGamma a < 1 := spinGamma_lt_one ha
    have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha.le
    have hα₂_ge : 4 * π ≤ α₂ := by
      have ha0 : 0 < a := by linarith
      have hdiff : 2 / a = (1 - spinGamma a) * (1 + spinGamma a) := by nlinarith
      have h1γ : 1 / a < 1 - spinGamma a := by
        have hlt : 2 / a < (1 - spinGamma a) * 2 := by
          rw [hdiff]; exact mul_lt_mul_of_pos_left (by linarith) (sub_pos.mpr hγ1)
        have : 2 < a * ((1 - spinGamma a) * 2) := by
          calc 2 = a * (2 / a) := by field_simp [ha0.ne']
            _ < a * ((1 - spinGamma a) * 2) := mul_lt_mul_of_pos_left hlt ha0
        have : 1 < a * (1 - spinGamma a) := by linarith
        calc 1 / a = a⁻¹ := one_div a
          _ < a⁻¹ * (a * (1 - spinGamma a)) := by nlinarith [inv_pos.mpr ha0]
          _ = 1 - spinGamma a := by field_simp [ha0.ne']
      dsimp [α₂]
      rw [show 4 * π = π * (12 * a) * (1 / a) / 3 by field_simp [ha0.ne']; ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1γ.le (by positivity)) (by norm_num)
    have hα₂_le : α₂ ≤ 4 * π * (1 + 24 / n) := by
      have ha12 : 12 * a = n := by dsimp [a]; ring
      have ha2n : 2 / a = 24 / n := by dsimp [a]; field_simp; ring
      have hprod_id : (1 - spinGamma a) * (1 + spinGamma a) = 24 / n := by
        calc (1 - spinGamma a) * (1 + spinGamma a) = 1 - spinGamma a ^ 2 := by ring
          _ = 2 / a := by rw [hγ_sq]; ring
          _ = 24 / n := ha2n
      have h1p : 1 + spinGamma a ≠ 0 := by linarith
      have hdiff : 1 - spinGamma a = (24 / n) / (1 + spinGamma a) :=
        (eq_div_iff h1p).mpr hprod_id
      have h_eq : π * n * ((24 / n) / (1 + spinGamma a)) / 3 =
          8 * π / (1 + spinGamma a) := by
        have hn0 : n ≠ 0 := by linarith
        field_simp [hn0]; ring
      have hsub : α₂ - 4 * π ≤ 4 * π * (24 / n) := by
        have hdiff2 : α₂ - 4 * π = π * n * (24 / n / (1 + spinGamma a)) / 3 - 4 * π := by
          dsimp [α₂]; rw [ha12, hdiff]
        rw [hdiff2, h_eq]
        have hcalc : 8 * π / (1 + spinGamma a) - 4 * π =
            4 * π * ((1 - spinGamma a) / (1 + spinGamma a)) := by
          field_simp [h1p]; ring
        rw [hcalc, hdiff]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1sq : 1 ≤ (1 + spinGamma a) * (1 + spinGamma a) := by nlinarith
        calc (24 / n / (1 + spinGamma a)) / (1 + spinGamma a)
            = (24 / n) / ((1 + spinGamma a) * (1 + spinGamma a)) := div_div _ _ _
          _ ≤ 24 / n := div_le_self (by positivity) h1sq
      linarith
    have hFc1 : 1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ 1 := by
      linarith [Real.exp_pos (-π * (12 * a) * (1 + spinGamma a) * x / 3)]
    have hFc2 : 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤
        (1 + 24 / n) * spinCalF x := by
      have heq1 : -π * (12 * a) * (1 - spinGamma a) * x / 3 = -(α₂ / (4 * π)) * (4 * π * x) := by
        dsimp [α₂]; field_simp [hpi.ne']
      rw [heq1]
      have hr1 : 1 ≤ α₂ / (4 * π) := (one_le_div (by positivity)).mpr hα₂_ge
      have h1 := one_sub_exp_mul_le hr1 (by positivity : 0 ≤ 4 * π * x)
      have hr2 : α₂ / (4 * π) ≤ 1 + 24 / n := (div_le_iff₀ (by positivity)).mpr (by linarith)
      have hF_nn : 0 ≤ 1 - Real.exp (-(4 * π * x)) := by
        rw [show -(4 * π * x) = -4 * π * x by ring]
        exact (spinCalF_pos hx0).le
      calc 1 - Real.exp (-(α₂ / (4 * π)) * (4 * π * x))
          ≤ (α₂ / (4 * π)) * (1 - Real.exp (-(4 * π * x))) := h1
        _ ≤ (1 + 24 / n) * (1 - Real.exp (-(4 * π * x))) :=
            mul_le_mul_of_nonneg_right hr2 hF_nn
        _ = (1 + 24 / n) * spinCalF x := by
            unfold spinCalF
            rw [show -(4 * π * x) = -4 * π * x by ring]
    have hFc_ub : spinCalFc a x ≤ (1 + 24 / n) * spinCalF x := by
      unfold spinCalFc
      have h2_nn : 0 ≤ 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := by
        rw [sub_nonneg, Real.exp_le_one_iff]
        have he : -π * (12 * a) * (1 - spinGamma a) * x / 3 = -α₂ * x := by dsimp [α₂]; ring
        rw [he]; nlinarith
      calc (1 - Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3)) *
              (1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3))
          ≤ 1 * (1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3)) :=
            mul_le_mul_of_nonneg_right hFc1 h2_nn
        _ = 1 - Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) := one_mul _
        _ ≤ (1 + 24 / n) * spinCalF x := hFc2
    have hdiv : spinCalPhi x / (1 + 24 / n) ≤ Real.tanh (x / 2) ^ 2 / spinCalFc a x := by
      unfold spinCalPhi
      rw [div_div, mul_comm (spinCalF x) (1 + 24 / n)]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (spinCalFc_pos ha hx0) hFc_ub
    have hmul_le : 1 - 24 / n ≤ 1 / (1 + 24 / n) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : 0 ≤ (24 / n) ^ 2 := sq_nonneg _
      nlinarith
    calc (1 - 24 / n) * spinCalPhi x
        ≤ (1 / (1 + 24 / n)) * spinCalPhi x :=
          mul_le_mul_of_nonneg_right hmul_le (spinCalPhi_nonneg hx)
      _ = spinCalPhi x / (1 + 24 / n) := by ring
      _ ≤ Real.tanh (x / 2) ^ 2 / spinCalFc a x := hdiv

private lemma spinCalPhic_abs_sub_le {c x : ℝ} (hc : 40 ≤ c) (hx : 0 ≤ x) :
    |spinCalPhic ((c - 1) / 12) x - spinCalPhi x| ≤ 24 / (c - 1) := by
  have hu := spinCalPhic_upper hc hx
  have hl := spinCalPhic_lower hc hx
  have hpi : 4 * π ≤ 24 := by linarith [Real.pi_lt_four]
  have hn : 0 < c - 1 := by linarith
  have h1 : spinCalPhic ((c - 1) / 12) x - spinCalPhi x ≤ 24 / (c - 1) := by
    have : 4 * π / (c - 1) ≤ 24 / (c - 1) := div_le_div_of_nonneg_right hpi hn.le
    linarith
  have h2 : -(24 / (c - 1)) ≤ spinCalPhic ((c - 1) / 12) x - spinCalPhi x := by
    have hphi : spinCalPhi x ≤ 1 := spinCalPhi_le_one hx
    have hnn : 0 ≤ 24 / (c - 1) := div_nonneg (by norm_num) hn.le
    have h3 : (24 / (c - 1)) * spinCalPhi x ≤ 24 / (c - 1) := by nlinarith
    linarith
  exact abs_sub_le_iff.mpr ⟨h1, by linarith⟩

private lemma sinh_two_pi_gt {x : ℝ} (hx : 0 < x) :
    2 * π * Real.sinh x < Real.sinh (2 * π * x) := by
  let g : ℝ → ℝ := fun t => Real.sinh (2 * π * t) - 2 * π * Real.sinh t
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (2 * π * (Real.cosh (2 * π * t) - Real.cosh t)) t := by
    intro t
    have hm : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * π)
    have h1 : HasDerivAt (fun s : ℝ => Real.sinh (2 * π * s)) (2 * π * Real.cosh (2 * π * t)) t :=
      ((Real.hasDerivAt_sinh (2 * π * t)).comp t hm).congr_deriv (by ring)
    have h2 : HasDerivAt (fun s : ℝ => 2 * π * Real.sinh s) (2 * π * Real.cosh t) t :=
      (Real.hasDerivAt_sinh t).const_mul (2 * π)
    convert h1.sub h2 using 1; ring
  have hg_strict : StrictMonoOn g (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).sub
        (continuous_const.mul Real.continuous_sinh)).continuousOn
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      rw [(hg_deriv t).deriv]
      have hpi : 1 < 2 * π := by linarith [Real.pi_gt_three]
      have hcosh : Real.cosh t < Real.cosh (2 * π * t) := by
        rw [Real.cosh_lt_cosh, abs_of_pos ht0, abs_of_pos (by positivity)]
        nlinarith
      exact mul_pos (by positivity) (sub_pos.mpr hcosh)
  have h0 : g 0 < g x := hg_strict (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  dsimp [g] at h0
  simp only [mul_zero, Real.sinh_zero, sub_self] at h0
  linarith

private noncomputable def logPhiDeriv (x : ℝ) : ℝ :=
  2 / Real.sinh x - 4 * π / (Real.exp (4 * π * x) - 1)

private noncomputable def logPhiDeriv2 (x : ℝ) : ℝ :=
  -(2 * Real.cosh x / Real.sinh x ^ 2) + 4 * π ^ 2 / Real.sinh (2 * π * x) ^ 2

private lemma hasDerivAt_log_spinCalPhi {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.log (spinCalPhi t)) (logPhiDeriv x) x := by
  have hpi : 0 < π := Real.pi_pos
  have hth_pos : 0 < Real.tanh (x / 2) := tanh_half_pos hx
  have hF_pos : 0 < spinCalF x := spinCalF_pos hx
  have heq : ∀ᶠ t in 𝓝 x, Real.log (spinCalPhi t) =
      2 * Real.log (Real.tanh (t / 2)) - Real.log (spinCalF t) := by
    filter_upwards [(isOpen_Ioi.mem_nhds hx)] with t ht
    have ht_th : 0 < Real.tanh (t / 2) := tanh_half_pos ht
    have ht_F : 0 < spinCalF t := spinCalF_pos ht
    unfold spinCalPhi
    rw [Real.log_div (pow_pos ht_th 2).ne' ht_F.ne', Real.log_pow]
    norm_cast
  have hd_half : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hd_tanh : HasDerivAt (fun t : ℝ => Real.tanh (t / 2))
      (1 / (2 * Real.cosh (x / 2) ^ 2)) x := by
    have hc : (Real.cosh (x / 2)) ≠ 0 := (Real.cosh_pos _).ne'
    have hd_s : HasDerivAt (fun t : ℝ => Real.sinh (t / 2)) (Real.cosh (x / 2) * (1 / 2)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sinh (x / 2)).comp x hd_half
    have hd_c : HasDerivAt (fun t : ℝ => Real.cosh (t / 2)) (Real.sinh (x / 2) * (1 / 2)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cosh (x / 2)).comp x hd_half
    have hfun : (fun t : ℝ => Real.tanh (t / 2)) =
        fun t => Real.sinh (t / 2) / Real.cosh (t / 2) := by
      ext t; exact Real.tanh_eq_sinh_div_cosh _
    rw [hfun]
    convert hd_s.div hd_c hc using 1
    have h1 := Real.cosh_sq_sub_sinh_sq (x / 2)
    field_simp [hc]
    linarith [h1]
  have hd_log_tanh : HasDerivAt (fun t : ℝ => 2 * Real.log (Real.tanh (t / 2)))
      (2 / Real.sinh x) x := by
    have hl := (hd_tanh.log hth_pos.ne').const_mul 2
    convert hl using 1
    have hsinh_dbl : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      have h := Real.sinh_two_mul (x / 2)
      rwa [show 2 * (x / 2) = x by ring] at h
    have hth : Real.tanh (x / 2) = Real.sinh (x / 2) / Real.cosh (x / 2) :=
      Real.tanh_eq_sinh_div_cosh _
    have hs_pos : Real.sinh (x / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
    have hc_pos : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    rw [hsinh_dbl, hth]
    field_simp [hs_pos, hc_pos]
  have hd_F : HasDerivAt spinCalF (4 * π * Real.exp (-4 * π * x)) x := by
    unfold spinCalF
    have he : HasDerivAt (fun t : ℝ => -4 * π * t) (-4 * π) x := by
      simpa using (hasDerivAt_id x).const_mul (-4 * π)
    convert (hasDerivAt_const x 1).sub he.exp using 1
    ring
  have hd_log_F : HasDerivAt (fun t : ℝ => Real.log (spinCalF t))
      (4 * π / (Real.exp (4 * π * x) - 1)) x := by
    have hl := hd_F.log hF_pos.ne'
    convert hl using 1
    have hne1 : Real.exp (4 * π * x) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
    have hexp_neg : Real.exp (-4 * π * x) = (Real.exp (4 * π * x))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    have he_pos : Real.exp (4 * π * x) ≠ 0 := (Real.exp_pos _).ne'
    have hF_ne : 1 - (Real.exp (4 * π * x))⁻¹ ≠ 0 := by
      rw [← hexp_neg]; exact hF_pos.ne'
    unfold spinCalF
    rw [hexp_neg]
    field_simp [hne1, he_pos, hF_ne]
  exact (hd_log_tanh.sub hd_log_F).congr_of_eventuallyEq heq

private lemma hasDerivAt_logPhiDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt logPhiDeriv (logPhiDeriv2 x) x := by
  have hpi : 0 < π := Real.pi_pos
  have hs0 : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hs20 : Real.sinh (2 * π * x) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hene : Real.exp (4 * π * x) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have hd1 : HasDerivAt (fun t : ℝ => 2 / Real.sinh t)
      (-(2 * Real.cosh x / Real.sinh x ^ 2)) x := by
    have hi := (Real.hasDerivAt_sinh x).inv hs0
    convert hi.const_mul 2 using 1
    · ext t; simp [div_eq_mul_inv]
    · ring
  have hd2 : HasDerivAt (fun t : ℝ => 4 * π / (Real.exp (4 * π * t) - 1))
      (-(4 * π ^ 2 / Real.sinh (2 * π * x) ^ 2)) x := by
    have hm4 : HasDerivAt (fun t : ℝ => 4 * π * t) (4 * π) x := by
      simpa using (hasDerivAt_id x).const_mul (4 * π)
    have he4 : HasDerivAt (fun t : ℝ => Real.exp (4 * π * t) - 1)
        (4 * π * Real.exp (4 * π * x)) x := by
      convert (hm4.exp).sub (hasDerivAt_const x 1) using 1
      ring
    convert he4.inv hene |>.const_mul (4 * π) using 1
    · ext t; simp [div_eq_mul_inv]
    · have he_pos : Real.exp (2 * π * x) ≠ 0 := (Real.exp_pos _).ne'
      have he4_eq : Real.exp (4 * π * x) = Real.exp (2 * π * x) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hsinh_eq : Real.sinh (2 * π * x) =
          (Real.exp (2 * π * x) - (Real.exp (2 * π * x))⁻¹) / 2 := by
        rw [Real.sinh_eq, Real.exp_neg]
      rw [he4_eq, hsinh_eq]
      have hs_nz : (Real.exp (2 * π * x) - (Real.exp (2 * π * x))⁻¹) / 2 ≠ 0 := by
        rw [← hsinh_eq]; exact hs20
      have he_nz : Real.exp (2 * π * x) ^ 2 - 1 ≠ 0 := by
        rw [← he4_eq]; exact hene
      field_simp [he_pos, hs_nz, he_nz]
      ring
  unfold logPhiDeriv logPhiDeriv2
  convert hd1.sub hd2 using 1
  ring

private lemma logPhiDeriv_pos {x : ℝ} (hx : 0 < x) : 0 < logPhiDeriv x := by
  unfold logPhiDeriv
  have hpi : 0 < π := Real.pi_pos
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hs2 : 0 < Real.sinh (2 * π * x) := Real.sinh_pos_iff.mpr (by positivity)
  have h2pi : 2 * π * Real.sinh x < Real.sinh (2 * π * x) := sinh_two_pi_gt hx
  have he2 : 1 < Real.exp (2 * π * x) := Real.one_lt_exp_iff.mpr (by positivity)
  have hrel : Real.exp (4 * π * x) - 1 = 2 * Real.exp (2 * π * x) * Real.sinh (2 * π * x) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (2 * π * x) * Real.exp (2 * π * x) = Real.exp (4 * π * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (2 * π * x) * Real.exp (-(2 * π * x)) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination -h1 + h2
  have hden1 : 2 * π * Real.sinh x < Real.exp (2 * π * x) * Real.sinh (2 * π * x) := by
    calc 2 * π * Real.sinh x < 1 * Real.sinh (2 * π * x) := by linarith
      _ < Real.exp (2 * π * x) * Real.sinh (2 * π * x) := mul_lt_mul_of_pos_right he2 hs2
  have hden : 4 * π * Real.sinh x < 2 * (Real.exp (4 * π * x) - 1) := by
    have hprod_pos : 0 < Real.exp (2 * π * x) * Real.sinh (2 * π * x) := mul_pos (by linarith) hs2
    calc 4 * π * Real.sinh x < 2 * (Real.exp (2 * π * x) * Real.sinh (2 * π * x)) := by linarith
      _ ≤ 4 * (Real.exp (2 * π * x) * Real.sinh (2 * π * x)) := by linarith
      _ = 2 * (Real.exp (4 * π * x) - 1) := by rw [hrel]; ring
  have hepos : 0 < Real.exp (4 * π * x) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  rw [sub_pos, div_lt_div_iff₀ hepos hs]
  exact hden

private lemma logPhiDeriv2_neg {x : ℝ} (hx : 0 < x) : logPhiDeriv2 x < 0 := by
  unfold logPhiDeriv2
  have hpi : 0 < π := Real.pi_pos
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hs2 : 0 < Real.sinh (2 * π * x) := Real.sinh_pos_iff.mpr (by positivity)
  have h2pi : 2 * π * Real.sinh x < Real.sinh (2 * π * x) := sinh_two_pi_gt hx
  have hsq : (2 * π * Real.sinh x) ^ 2 < Real.sinh (2 * π * x) ^ 2 :=
    pow_lt_pow_left₀ h2pi (by positivity) two_ne_zero
  have h1 : 4 * π ^ 2 / Real.sinh (2 * π * x) ^ 2 < 1 / Real.sinh x ^ 2 := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hs2) (sq_pos_of_pos hs)]
    calc 4 * π ^ 2 * Real.sinh x ^ 2 = (2 * π * Real.sinh x) ^ 2 := by ring
      _ < 1 * Real.sinh (2 * π * x) ^ 2 := by linarith
  have hc : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have h2 : 1 / Real.sinh x ^ 2 < 2 * Real.cosh x / Real.sinh x ^ 2 :=
    div_lt_div_of_pos_right (by linarith) (sq_pos_of_pos hs)
  have hlt : 4 * π ^ 2 / Real.sinh (2 * π * x) ^ 2 < 2 * Real.cosh x / Real.sinh x ^ 2 :=
    h1.trans h2
  linarith

private lemma log_spinCalPhi_concave_symm {ξ d : ℝ} (hd : |d| < ξ) :
    Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) ≤
      2 * Real.log (spinCalPhi ξ) := by
  have hanti : StrictAntiOn logPhiDeriv (Ioi 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
    · intro x hx
      exact (hasDerivAt_logPhiDeriv (mem_Ioi.mp hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(hasDerivAt_logPhiDeriv (mem_Ioi.mp hx)).deriv]
      exact logPhiDeriv2_neg (mem_Ioi.mp hx)
  let t0 : ℝ := |d|
  have ht0_nn : 0 ≤ t0 := abs_nonneg d
  have ht0_lt : t0 < ξ := hd
  let g : ℝ → ℝ := fun t => Real.log (spinCalPhi (ξ + t)) + Real.log (spinCalPhi (ξ - t))
  have hg_deriv : ∀ t : ℝ, 0 ≤ t → t < ξ →
      HasDerivAt g (logPhiDeriv (ξ + t) - logPhiDeriv (ξ - t)) t := by
    intro t ht0 htξ
    have hp : 0 < ξ + t := by linarith
    have hm : 0 < ξ - t := by linarith
    have ha : HasDerivAt (fun u : ℝ => ξ + u) 1 t := (hasDerivAt_id t).const_add ξ
    have hb : HasDerivAt (fun u : ℝ => ξ - u) (-1) t := by
      simpa [sub_eq_add_neg, add_comm] using ((hasDerivAt_id t).neg).const_add ξ
    have h1 : HasDerivAt (fun u => Real.log (spinCalPhi (ξ + u))) (logPhiDeriv (ξ + t)) t :=
      ((hasDerivAt_log_spinCalPhi hp).comp t ha).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u => Real.log (spinCalPhi (ξ - u))) (-logPhiDeriv (ξ - t)) t :=
      ((hasDerivAt_log_spinCalPhi hm).comp t hb).congr_deriv (by ring)
    exact h1.add h2
  have hg_anti : AntitoneOn g (Ico 0 ξ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 ξ) ?_ ?_ ?_
    · intro t ht
      exact (hg_deriv t ht.1 ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hg_deriv t ht.1.le ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hg_deriv t ht.1.le ht.2).deriv]
      have ht_pos1 : 0 < ξ + t := by linarith [ht.1, ht.2]
      have ht_pos2 : 0 < ξ - t := by linarith [ht.1, ht.2]
      have hle : logPhiDeriv (ξ + t) ≤ logPhiDeriv (ξ - t) :=
        (hanti.antitoneOn) (mem_Ioi.mpr ht_pos2) (mem_Ioi.mpr ht_pos1) (by linarith [ht.1])
      linarith
  have hgt0 : g t0 ≤ g 0 := hg_anti ⟨le_rfl, by linarith⟩ ⟨ht0_nn, ht0_lt⟩ ht0_nn
  have hgd : g d = g t0 := by
    rcases le_total 0 d with hd0 | hd0
    · simp [g, t0, abs_of_nonneg hd0]
    · simp [g, t0, abs_of_nonpos hd0, add_comm, sub_eq_add_neg]
  have hgt0' : Real.log (spinCalPhi (ξ + t0)) + Real.log (spinCalPhi (ξ - t0)) ≤
      2 * Real.log (spinCalPhi ξ) := by
    dsimp [g] at hgt0
    simp only [add_zero, sub_zero] at hgt0
    linarith
  have hgd' : Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) =
      Real.log (spinCalPhi (ξ + t0)) + Real.log (spinCalPhi (ξ - t0)) := hgd
  linarith

private noncomputable def calB (s : ℝ) : ℝ :=
  Real.log ((1 + xiStar ^ 2) / (1 + s)) +
    2 * (Real.log (spinCalPhi (Real.sqrt s)) - Real.log (spinCalPhi xiStar)) -
    (spinAlpha1 / (2 * xiStar)) * (s - xiStar ^ 2) -
    (1 / 2 : ℝ) * (s - xiStar ^ 2) ^ 2

private noncomputable def calBDeriv (s : ℝ) : ℝ :=
  -1 / (1 + s) + logPhiDeriv (Real.sqrt s) / Real.sqrt s -
    spinAlpha1 / (2 * xiStar) - (s - xiStar ^ 2)

private noncomputable def calBDeriv2 (s : ℝ) : ℝ :=
  1 / (1 + s) ^ 2 + logPhiDeriv2 (Real.sqrt s) / (2 * s) -
    logPhiDeriv (Real.sqrt s) / (2 * s * Real.sqrt s) - 1

private lemma calBDeriv_xiStar_sq : calBDeriv (xiStar ^ 2) = 0 := by
  have hx : 0 < xiStar := xiStar_pos
  unfold calBDeriv
  rw [Real.sqrt_sq hx.le]
  unfold logPhiDeriv spinAlpha1
  field_simp [hx.ne']
  ring

private lemma calB_xiStar_sq : calB (xiStar ^ 2) = 0 := by
  have hx : 0 < xiStar := xiStar_pos
  unfold calB
  rw [Real.sqrt_sq hx.le, div_self (by positivity), Real.log_one]
  ring

private lemma hasDerivAt_calB {s : ℝ} (hs : 0 < s) : HasDerivAt calB (calBDeriv s) s := by
  have hx : 0 < xiStar := xiStar_pos
  have hs1 : 1 + s ≠ 0 := by linarith
  have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1p : HasDerivAt (fun t : ℝ => 1 + t) 1 s := (hasDerivAt_id s).const_add 1
  have hsub : HasDerivAt (fun t : ℝ => t - xiStar ^ 2) 1 s := (hasDerivAt_id s).sub_const (xiStar ^ 2)
  have h1 : HasDerivAt (fun t : ℝ => Real.log ((1 + xiStar ^ 2) / (1 + t))) (-1 / (1 + s)) s := by
    have hf : HasDerivAt (fun t : ℝ => (1 + xiStar ^ 2) / (1 + t))
        (-(1 + xiStar ^ 2) / (1 + s) ^ 2) s := by
      have hi := h1p.inv hs1
      convert hi.const_mul (1 + xiStar ^ 2) using 1
      · ext t; simp [div_eq_mul_inv]
      · ring
    convert hf.log (div_pos (by positivity) (by linarith)).ne' using 1
    field_simp [hs1, (by positivity : 1 + xiStar ^ 2 ≠ 0)]
  have h2 : HasDerivAt (fun t : ℝ => 2 * (Real.log (spinCalPhi (Real.sqrt t)) - Real.log (spinCalPhi xiStar)))
      (logPhiDeriv (Real.sqrt s) / Real.sqrt s) s := by
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
    have hc : HasDerivAt (fun t : ℝ => Real.log (spinCalPhi (Real.sqrt t)))
        (logPhiDeriv (Real.sqrt s) * (1 / (2 * Real.sqrt s))) s :=
      (hasDerivAt_log_spinCalPhi hsq_pos).comp s hsqrt
    convert (hc.sub_const _).const_mul 2 using 1
    field_simp [hsq_pos.ne']
  have h3 : HasDerivAt (fun t : ℝ => (spinAlpha1 / (2 * xiStar)) * (t - xiStar ^ 2))
      (spinAlpha1 / (2 * xiStar)) s := by
    simpa using hsub.const_mul (spinAlpha1 / (2 * xiStar))
  have h4 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * (t - xiStar ^ 2) ^ 2) (s - xiStar ^ 2) s := by
    have hp : HasDerivAt (fun t : ℝ => (t - xiStar ^ 2) ^ 2) (2 * (s - xiStar ^ 2)) s := by
      convert hsub.pow 2 using 1
      ring
    convert hp.const_mul (1 / 2 : ℝ) using 1
    ring
  unfold calB calBDeriv
  convert ((h1.add h2).sub h3).sub h4 using 1

private lemma hasDerivAt_calBDeriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt calBDeriv (calBDeriv2 s) s := by
  have hs1 : 1 + s ≠ 0 := by linarith
  have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1p : HasDerivAt (fun t : ℝ => 1 + t) 1 s := (hasDerivAt_id s).const_add 1
  have h1 : HasDerivAt (fun t : ℝ => -1 / (1 + t)) (1 / (1 + s) ^ 2) s := by
    have hi := h1p.inv hs1
    convert hi.neg using 1
    · ext t; simp [div_eq_mul_inv]
    · ring
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hl' : HasDerivAt (fun t : ℝ => logPhiDeriv (Real.sqrt t))
      (logPhiDeriv2 (Real.sqrt s) * (1 / (2 * Real.sqrt s))) s :=
    (hasDerivAt_logPhiDeriv hsq_pos).comp s hsqrt
  have h2 : HasDerivAt (fun t : ℝ => logPhiDeriv (Real.sqrt t) / Real.sqrt t)
      (logPhiDeriv2 (Real.sqrt s) / (2 * s) -
        logPhiDeriv (Real.sqrt s) / (2 * s * Real.sqrt s)) s := by
    convert hl'.div hsqrt hsq_pos.ne' using 1
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    field_simp [hsq_pos.ne', hs.ne']
    linear_combination (logPhiDeriv2 (Real.sqrt s) * Real.sqrt s - logPhiDeriv (Real.sqrt s)) * hsq
  have h3 : HasDerivAt (fun t : ℝ => spinAlpha1 / (2 * xiStar)) 0 s := hasDerivAt_const s _
  have h4 : HasDerivAt (fun t : ℝ => t - xiStar ^ 2) 1 s := by
    simpa using (hasDerivAt_id s).sub_const (xiStar ^ 2)
  unfold calBDeriv calBDeriv2
  convert ((h1.add h2).sub h3).sub h4 using 1
  ring

private lemma calBDeriv2_neg {s : ℝ} (hs : 0 < s) : calBDeriv2 s < 0 := by
  unfold calBDeriv2
  have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1 : 1 / (1 + s) ^ 2 < 1 := by
    have : 1 < (1 + s) ^ 2 := by nlinarith
    exact (div_lt_one (by positivity)).mpr this
  have h2 : logPhiDeriv2 (Real.sqrt s) / (2 * s) < 0 :=
    div_neg_of_neg_of_pos (logPhiDeriv2_neg hsq_pos) (by positivity)
  have h3 : 0 < logPhiDeriv (Real.sqrt s) / (2 * s * Real.sqrt s) :=
    div_pos (logPhiDeriv_pos hsq_pos) (by positivity)
  linarith

private lemma calB_le_zero {s : ℝ} (hs : 0 < s) : calB s ≤ 0 := by
  have hx2 : 0 < xiStar ^ 2 := sq_pos_of_pos xiStar_pos
  have hanti_d : AntitoneOn calBDeriv (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · intro t ht
      exact (hasDerivAt_calBDeriv (mem_Ioi.mp ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      exact (hasDerivAt_calBDeriv (mem_Ioi.mp ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      rw [(hasDerivAt_calBDeriv (mem_Ioi.mp ht)).deriv]
      exact (calBDeriv2_neg (mem_Ioi.mp ht)).le
  rcases le_total s (xiStar ^ 2) with hs_le | hs_ge
  · have hmono : MonotoneOn calB (Ioc 0 (xiStar ^ 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 (xiStar ^ 2)) ?_ ?_ ?_
      · intro t ht
        exact (hasDerivAt_calB ht.1).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        exact (hasDerivAt_calB ht.1).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ioc] at ht
        rw [(hasDerivAt_calB ht.1).deriv]
        have h := hanti_d (mem_Ioi.mpr ht.1) (mem_Ioi.mpr hx2) ht.2.le
        linarith [calBDeriv_xiStar_sq]
    have hle := hmono ⟨hs, hs_le⟩ ⟨hx2, le_rfl⟩ hs_le
    linarith [calB_xiStar_sq]
  · have hanti : AntitoneOn calB (Ici (xiStar ^ 2)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici (xiStar ^ 2)) ?_ ?_ ?_
      · intro t ht
        exact (hasDerivAt_calB (hx2.trans_le (mem_Ici.mp ht))).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        exact (hasDerivAt_calB (hx2.trans (mem_Ioi.mp ht))).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hasDerivAt_calB (hx2.trans (mem_Ioi.mp ht))).deriv]
        have h := hanti_d (mem_Ioi.mpr hx2) (mem_Ioi.mpr (hx2.trans (mem_Ioi.mp ht)))
          (mem_Ioi.mp ht).le
        linarith [calBDeriv_xiStar_sq]
    have hle := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs_ge) hs_ge
    linarith [calB_xiStar_sq]

private noncomputable def spinRInf (ξ d : ℝ) : ℝ :=
  (1 + xiStar ^ 2) / (1 + ξ ^ 2) *
    (spinCalPhi (ξ + d) * spinCalPhi (ξ - d) / spinCalPhi xiStar ^ 2) *
    Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
      (ξ ^ 2 - xiStar ^ 2) ^ 2)

private lemma log_spinRInf_eq {ξ d : ℝ} (hd : |d| < ξ) :
    Real.log (spinRInf ξ d) =
      calB (ξ ^ 2) +
        (Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
          2 * Real.log (spinCalPhi ξ)) -
        (1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2 := by
  have hξ_pos : 0 < ξ := (abs_nonneg d).trans_lt hd
  have hxd_p : 0 < ξ + d := by linarith [neg_abs_le d, abs_le.mp hd.le]
  have hxd_m : 0 < ξ - d := by linarith [le_abs_self d, abs_le.mp hd.le]
  have hφp : 0 < spinCalPhi (ξ + d) := spinCalPhi_pos hxd_p
  have hφm : 0 < spinCalPhi (ξ - d) := spinCalPhi_pos hxd_m
  have hφξ : 0 < spinCalPhi ξ := spinCalPhi_pos hξ_pos
  have hφs : 0 < spinCalPhi xiStar := spinCalPhi_pos xiStar_pos
  unfold spinRInf calB
  have h1_pos : 0 < (1 + xiStar ^ 2) / (1 + ξ ^ 2) := by positivity
  have h2_pos : 0 < spinCalPhi (ξ + d) * spinCalPhi (ξ - d) / spinCalPhi xiStar ^ 2 := by positivity
  rw [Real.log_mul (mul_pos h1_pos h2_pos).ne' (Real.exp_pos _).ne',
    Real.log_mul h1_pos.ne' h2_pos.ne',
    Real.log_div (mul_pos hφp hφm).ne' (pow_pos hφs 2).ne',
    Real.log_mul hφp.ne' hφm.ne', Real.log_pow, Real.log_exp, Real.sqrt_sq hξ_pos.le]
  norm_cast
  ring

private lemma spinRInf_le_exp {ξ d : ℝ} (hd : |d| ≤ ξ) :
    spinRInf ξ d ≤ Real.exp (-(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2) := by
  rcases eq_or_lt_of_le hd with hEq | hLt
  · have hzero : spinCalPhi (ξ + d) * spinCalPhi (ξ - d) = 0 := by
      rcases abs_cases d with ⟨hd0, h⟩ | ⟨hd0, h⟩
      · have : ξ - d = 0 := by linarith
        simp [this, spinCalPhi]
      · have : ξ + d = 0 := by linarith
        simp [this, spinCalPhi]
    unfold spinRInf
    rw [hzero, zero_div, mul_zero, zero_mul]
    exact (Real.exp_pos _).le
  · have hξ_pos : 0 < ξ := (abs_nonneg d).trans_lt hLt
    have hlog := log_spinRInf_eq hLt
    have hB := calB_le_zero (sq_pos_of_pos hξ_pos)
    have hC := log_spinCalPhi_concave_symm hLt
    have hle : Real.log (spinRInf ξ d) ≤
        -(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2 := by
      linarith
    have hpos : 0 < spinRInf ξ d := by
      have hxd_p : 0 < ξ + d := by linarith [abs_lt.mp hLt]
      have hxd_m : 0 < ξ - d := by linarith [abs_lt.mp hLt]
      unfold spinRInf
      have h1 : 0 < spinCalPhi (ξ + d) := spinCalPhi_pos hxd_p
      have h2 : 0 < spinCalPhi (ξ - d) := spinCalPhi_pos hxd_m
      have h3 : 0 < spinCalPhi xiStar := spinCalPhi_pos xiStar_pos
      positivity
    calc spinRInf ξ d = Real.exp (Real.log (spinRInf ξ d)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (-(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2) :=
          Real.exp_le_exp.mpr hle

private lemma exp_linear_sub_sq_le (k t : ℝ) :
    Real.exp (-k * t - t ^ 2) ≤ Real.exp (k ^ 2 / 4) := by
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ (t + k / 2) ^ 2 := sq_nonneg _
  linarith

private lemma pref_bound (x : ℝ) :
    ((1 + xiStar ^ 2) / (1 + x ^ 2)) / spinCalPhi xiStar ^ 2 *
      Real.exp (-spinAlpha1 * (x ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (x ^ 2 - xiStar ^ 2) ^ 2) ≤
      (1 + xiStar ^ 2) / spinCalPhi xiStar ^ 2 *
        Real.exp ((spinAlpha1 / (2 * xiStar)) ^ 2 / 4) := by
  have hφs : 0 < spinCalPhi xiStar := spinCalPhi_pos xiStar_pos
  have h1 : (1 + xiStar ^ 2) / (1 + x ^ 2) ≤ 1 + xiStar ^ 2 :=
    div_le_self (by positivity) (by linarith [sq_nonneg x])
  have h2 : Real.exp (-spinAlpha1 * (x ^ 2 - xiStar ^ 2) / (2 * xiStar) -
      (x ^ 2 - xiStar ^ 2) ^ 2) ≤ Real.exp ((spinAlpha1 / (2 * xiStar)) ^ 2 / 4) := by
    have heq : -spinAlpha1 * (x ^ 2 - xiStar ^ 2) / (2 * xiStar) - (x ^ 2 - xiStar ^ 2) ^ 2 =
        -(spinAlpha1 / (2 * xiStar)) * (x ^ 2 - xiStar ^ 2) - (x ^ 2 - xiStar ^ 2) ^ 2 := by
      ring
    rw [heq]
    exact exp_linear_sub_sq_le _ _
  exact mul_le_mul (div_le_div_of_nonneg_right h1 (by positivity)) h2 (Real.exp_pos _).le (by positivity)

private lemma continuousOn_logPhiDeriv2_Ioi : ContinuousOn logPhiDeriv2 (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := mem_Ioi.mp hx
  have hpi : 0 < π := Real.pi_pos
  have hsh1 : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx0).ne'
  have hsh2 : Real.sinh (2 * π * x) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hc1 : ContinuousAt (fun t : ℝ => -(2 * Real.cosh t / Real.sinh t ^ 2)) x :=
    ((continuousAt_const.mul Real.continuous_cosh.continuousAt).div
      (Real.continuous_sinh.continuousAt.pow 2) (pow_ne_zero 2 hsh1)).neg
  have hc2 : ContinuousAt (fun t : ℝ => 4 * π ^ 2 / Real.sinh (2 * π * t) ^ 2) x :=
    continuousAt_const.div
      ((Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)).pow 2)
      (pow_ne_zero 2 hsh2)
  exact (hc1.add hc2).continuousWithinAt

private lemma continuousOn_calBDeriv2_Ioi : ContinuousOn calBDeriv2 (Ioi 0) := by
  intro s hs
  have hs0 : 0 < s := mem_Ioi.mp hs
  have hpi : 0 < π := Real.pi_pos
  have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hsq_cont : ContinuousAt Real.sqrt s := Real.continuous_sqrt.continuousAt
  have hsh1 : Real.sinh (Real.sqrt s) ≠ 0 := (Real.sinh_pos_iff.mpr hsq_pos).ne'
  have hene : Real.exp (4 * π * Real.sqrt s) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have h1 : ContinuousAt (fun t : ℝ => 1 / (1 + t) ^ 2) s := by
    have h1p0 : 0 < 1 + s := by linarith
    exact continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2) (by positivity)
  have h2 : ContinuousAt (fun t : ℝ => logPhiDeriv2 (Real.sqrt t) / (2 * t)) s := by
    have hc_l2 := (continuousOn_logPhiDeriv2_Ioi.continuousAt (Ioi_mem_nhds hsq_pos)).comp hsq_cont
    exact hc_l2.div (continuousAt_const.mul continuousAt_id) (by linarith)
  have h3 : ContinuousAt (fun t : ℝ => logPhiDeriv (Real.sqrt t) / (2 * t * Real.sqrt t)) s := by
    have hc_s := Real.continuous_sinh.continuousAt.comp hsq_cont
    have hc_e : ContinuousAt (fun t : ℝ => Real.exp (4 * π * Real.sqrt t) - 1) s :=
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hsq_cont)).sub continuousAt_const
    have hc_l1 : ContinuousAt (fun t : ℝ => logPhiDeriv (Real.sqrt t)) s :=
      (continuousAt_const.div hc_s hsh1).sub (continuousAt_const.div hc_e hene)
    have hden : 2 * s * Real.sqrt s ≠ 0 := (by positivity : 0 < 2 * s * Real.sqrt s).ne'
    exact hc_l1.div ((continuousAt_const.mul continuousAt_id).mul hsq_cont) hden
  unfold calBDeriv2
  exact (((h1.add h2).sub h3).sub continuousAt_const).continuousWithinAt

end Helpers

/-- Proposition `scal:C1` (`spinning_calibration.tex`): uniform global bound and local
quadratic contact of the calibrated adjoint ratio `spinRc`. -/
theorem scalC1 : ScalC1 := by
  let K0 : ℝ := (1 + xiStar ^ 2) / spinCalPhi xiStar ^ 2 *
    Real.exp ((spinAlpha1 / (2 * xiStar)) ^ 2 / 4)
  have hK0_pos : 0 < K0 := by
    have := spinCalPhi_pos xiStar_pos
    positivity
  let C_glob : ℝ := K0 * (72 + 2 * (6 + 24)) + 1
  have hC_glob_pos : 0 < C_glob := by positivity
  let r₀ : ℝ := xiStar / 4
  have hr₀_pos : 0 < r₀ := by dsimp [r₀]; linarith [xiStar_pos]
  let I_s : Set ℝ := Icc (xiStar ^ 2 / 2) (2 * xiStar ^ 2)
  have hIs_sub : I_s ⊆ Ioi 0 := fun s hs => by
    have h0 : 0 < xiStar ^ 2 / 2 := by have := xiStar_pos; positivity
    exact h0.trans_le hs.1
  obtain ⟨K_B, _, hKB_max⟩ := isCompact_Icc.exists_isMaxOn
    ⟨xiStar ^ 2 / 2, le_rfl, by linarith [sq_pos_of_pos xiStar_pos]⟩
    ((continuousOn_calBDeriv2_Ioi.mono hIs_sub).abs)
  let M_B : ℝ := max (|calBDeriv2 K_B|) 1
  have hMB_pos : 0 < M_B := by positivity
  let I_x : Set ℝ := Icc (xiStar / 2) (2 * xiStar)
  have hIx_sub : I_x ⊆ Ioi 0 := fun x hx => by
    have h0 : 0 < xiStar / 2 := by linarith [xiStar_pos]
    exact h0.trans_le hx.1
  obtain ⟨K_L, _, hKL_max⟩ := isCompact_Icc.exists_isMaxOn
    ⟨xiStar / 2, le_rfl, by linarith [xiStar_pos]⟩
    ((continuousOn_logPhiDeriv2_Ioi.mono hIx_sub).abs)
  let M_L : ℝ := max (|logPhiDeriv2 K_L|) 1
  have hML_pos : 0 < M_L := by positivity
  let K_quad : ℝ := (M_B + 1 / 2) * ((9 / 4 : ℝ) * xiStar) ^ 2 + (2 * M_L + 1 / spinSigma0 ^ 2)
  have hKq_pos : 0 < K_quad := by positivity
  let M_log : ℝ := K_quad * r₀ ^ 2
  have hMlog_pos : 0 < M_log := by positivity
  let C₁ : ℝ := Real.exp M_log * K_quad + K0 * (72 + 2 * (6 + 24)) + 1
  have hC1_pos : 0 < C₁ := by positivity
  refine ⟨C_glob, C₁, r₀, hC_glob_pos, hC1_pos, hr₀_pos, ?_⟩
  intro c hc n a ξ d hd
  have hn39 : 39 ≤ n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hξ_nn : 0 ≤ ξ := (abs_nonneg d).trans hd
  have hxd_p : 0 ≤ ξ + d := by linarith [abs_le.mp hd]
  have hxd_m : 0 ≤ ξ - d := by linarith [abs_le.mp hd]
  have hRc_nn : 0 ≤ spinRc a ξ d := by
    have hφ1 : 0 ≤ spinCalPhic a (ξ + d) := spinCalPhic_nonneg ha2 hxd_p
    have hφ2 : 0 ≤ spinCalPhic a (ξ - d) := spinCalPhic_nonneg ha2 hxd_m
    have h1 : 0 ≤ spinRc1 a ξ d := by
      unfold spinRc1
      have := spinCalPhi_pos xiStar_pos
      positivity
    have h2 : 0 ≤ spinRc2 a ξ d := by
      unfold spinRc2
      have := spinCalPhi_pos xiStar_pos
      positivity
    unfold spinRc
    linarith
  have hdiff_R1 : |spinRc1 a ξ d - spinRInf ξ d| ≤ K0 * 72 / n := by
    let P1 : ℝ := (1 + xiStar ^ 2) / (1 + ξ ^ 2) / spinCalPhi xiStar ^ 2 *
      Real.exp (-d ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (ξ ^ 2 - xiStar ^ 2) ^ 2)
    have hP1_nn : 0 ≤ P1 := by
      have := spinCalPhi_pos xiStar_pos; positivity
    have hP1_bd : P1 ≤ K0 := by
      have hexp1 : Real.exp (-d ^ 2 / spinSigma0 ^ 2 -
            spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) - (ξ ^ 2 - xiStar ^ 2) ^ 2) =
          Real.exp (-d ^ 2 / spinSigma0 ^ 2) *
            Real.exp (-spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (ξ ^ 2 - xiStar ^ 2) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have harg_np : -d ^ 2 / spinSigma0 ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg d)) (sq_nonneg _)
      have hg1 : Real.exp (-d ^ 2 / spinSigma0 ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr harg_np
      have hpb := pref_bound ξ
      calc P1 = ((1 + xiStar ^ 2) / (1 + ξ ^ 2) / spinCalPhi xiStar ^ 2 *
            Real.exp (-spinAlpha1 * (ξ ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (ξ ^ 2 - xiStar ^ 2) ^ 2)) * Real.exp (-d ^ 2 / spinSigma0 ^ 2) := by
            dsimp [P1]; rw [hexp1]; ring
        _ ≤ K0 * 1 := mul_le_mul hpb hg1 (Real.exp_pos _).le hK0_pos.le
        _ = K0 := mul_one _
    have hR1_eq : spinRc1 a ξ d = P1 * (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)) := by
      unfold spinRc1; dsimp [P1]; ring
    have hRi_eq : spinRInf ξ d = P1 * (spinCalPhi (ξ + d) * spinCalPhi (ξ - d)) := by
      unfold spinRInf; dsimp [P1]; ring
    have h_p := spinCalPhic_abs_sub_le hc hxd_p
    have h_m := spinCalPhic_abs_sub_le hc hxd_m
    have hφp_le : spinCalPhi (ξ + d) ≤ 1 := spinCalPhi_le_one hxd_p
    have hφc_m_le : spinCalPhic a (ξ - d) ≤ 2 := by
      have : spinCalPhic a (ξ - d) ≤ spinCalPhi (ξ - d) + 24 / n :=
        by linarith [abs_sub_le_iff.mp h_m]
      have : 24 / n ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith [spinCalPhi_le_one hxd_m]
    have hprod_diff : |spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) -
        spinCalPhi (ξ + d) * spinCalPhi (ξ - d)| ≤ 72 / n := by
      have halg : spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) -
          spinCalPhi (ξ + d) * spinCalPhi (ξ - d) =
          (spinCalPhic a (ξ + d) - spinCalPhi (ξ + d)) * spinCalPhic a (ξ - d) +
            spinCalPhi (ξ + d) * (spinCalPhic a (ξ - d) - spinCalPhi (ξ - d)) := by ring
      rw [halg]
      have ht := abs_add_le
        ((spinCalPhic a (ξ + d) - spinCalPhi (ξ + d)) * spinCalPhic a (ξ - d))
        (spinCalPhi (ξ + d) * (spinCalPhic a (ξ - d) - spinCalPhi (ξ - d)))
      rw [abs_mul, abs_mul, abs_of_nonneg (spinCalPhic_nonneg ha2 hxd_m),
        abs_of_nonneg (spinCalPhi_nonneg hxd_p)] at ht
      have ht1 : |spinCalPhic a (ξ + d) - spinCalPhi (ξ + d)| * spinCalPhic a (ξ - d) ≤
          (24 / n) * 2 :=
        mul_le_mul h_p hφc_m_le (spinCalPhic_nonneg ha2 hxd_m) (by positivity)
      have ht2 : spinCalPhi (ξ + d) * |spinCalPhic a (ξ - d) - spinCalPhi (ξ - d)| ≤
          1 * (24 / n) :=
        mul_le_mul hφp_le h_m (abs_nonneg _) zero_le_one
      have hsum72 : (24 / n) * 2 + 1 * (24 / n) = 72 / n := by ring
      linarith
    rw [hR1_eq, hRi_eq, ← mul_sub, abs_mul, abs_of_nonneg hP1_nn]
    calc P1 * |spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) -
            spinCalPhi (ξ + d) * spinCalPhi (ξ - d)|
        ≤ K0 * (72 / n) := mul_le_mul hP1_bd hprod_diff (abs_nonneg _) hK0_pos.le
      _ = K0 * 72 / n := by ring
  have hRc2_bd : spinRc2 a ξ d ≤ K0 * (2 * (6 + 24)) / n := by
    let P2 : ℝ := (1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 *
      Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 - spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
        (d ^ 2 - xiStar ^ 2) ^ 2)
    have hP2_bd : P2 ≤ K0 := by
      have hexp1 : Real.exp (-ξ ^ 2 / spinSigma0 ^ 2 -
            spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) - (d ^ 2 - xiStar ^ 2) ^ 2) =
          Real.exp (-ξ ^ 2 / spinSigma0 ^ 2) *
            Real.exp (-spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (d ^ 2 - xiStar ^ 2) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have harg_np : -ξ ^ 2 / spinSigma0 ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg ξ)) (sq_nonneg _)
      have hg1 : Real.exp (-ξ ^ 2 / spinSigma0 ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr harg_np
      have hpb := pref_bound d
      calc P2 = ((1 + xiStar ^ 2) / (1 + d ^ 2) / spinCalPhi xiStar ^ 2 *
            Real.exp (-spinAlpha1 * (d ^ 2 - xiStar ^ 2) / (2 * xiStar) -
              (d ^ 2 - xiStar ^ 2) ^ 2)) * Real.exp (-ξ ^ 2 / spinSigma0 ^ 2) := by
            dsimp [P2]; rw [hexp1]; ring
        _ ≤ K0 * 1 := mul_le_mul hpb hg1 (Real.exp_pos _).le hK0_pos.le
        _ = K0 := mul_one _
    let q : ℝ := ξ - |d|
    have hq_nn : 0 ≤ q := sub_nonneg.mpr hd
    have hpair_bd : spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d) ≤ 2 * spinCalPhic a q := by
      have hle2 : ∀ y : ℝ, 0 ≤ y → spinCalPhic a y ≤ 2 := fun y hy => by
        have h := spinCalPhic_abs_sub_le hc hy
        have : spinCalPhic a y ≤ spinCalPhi y + 24 / n := by linarith [abs_sub_le_iff.mp h]
        have : 24 / n ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith [spinCalPhi_le_one hy]
      rcases le_total 0 d with hd0 | hd0
      · have hq_eq : q = ξ - d := by dsimp [q]; rw [abs_of_nonneg hd0]
        rw [hq_eq]
        exact mul_le_mul_of_nonneg_right (hle2 (ξ + d) hxd_p) (spinCalPhic_nonneg ha2 hxd_m)
      · have hq_eq : q = ξ + d := by dsimp [q]; rw [abs_of_nonpos hd0]; ring
        rw [hq_eq, mul_comm]
        exact mul_le_mul_of_nonneg_right (hle2 (ξ - d) hxd_m) (spinCalPhic_nonneg ha2 hxd_p)
    have hq_exp : Real.exp (-(12 * a) * (2 * π / 3) * q) * spinCalPhic a q ≤ (6 + 24) / n := by
      have ha12 : 12 * a = n := by dsimp [a]; ring
      have harg : -(12 * a) * (2 * π / 3) * q = -(2 * π * n * q / 3) := by rw [ha12]; ring
      rw [harg]
      have hφc_ub : spinCalPhic a q ≤ 4 * π * q + 24 / n := by
        have h1 := spinCalPhic_upper hc hq_nn
        have h2 := spinCalPhi_le_mul hq_nn
        have hpi : 4 * π / n ≤ 24 / n :=
          div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) (by linarith)
        linarith
      have hu_exp : (2 * π * n * q / 3) * Real.exp (-(2 * π * n * q / 3)) ≤ 1 := by
        have h := Real.add_one_le_exp (2 * π * n * q / 3)
        have h1 : 2 * π * n * q / 3 ≤ Real.exp (2 * π * n * q / 3) := by linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(2 * π * n * q / 3))).le
        have h3 : Real.exp (2 * π * n * q / 3) * Real.exp (-(2 * π * n * q / 3)) = 1 := by
          rw [← Real.exp_add]; simp
        linarith
      have ht1 : Real.exp (-(2 * π * n * q / 3)) * (4 * π * q) ≤ 6 / n := by
        have halg : Real.exp (-(2 * π * n * q / 3)) * (4 * π * q) =
            (6 / n) * ((2 * π * n * q / 3) * Real.exp (-(2 * π * n * q / 3))) := by
          have hpi0 : π ≠ 0 := Real.pi_pos.ne'
          have hn0 : n ≠ 0 := by linarith
          field_simp [hpi0, hn0]; ring
        rw [halg]
        exact mul_le_of_le_one_right (by positivity) hu_exp
      have ht2 : Real.exp (-(2 * π * n * q / 3)) * (24 / n) ≤ 24 / n := by
        have harg_nn : 0 ≤ 2 * π * n * q / 3 := by positivity
        have he1 : Real.exp (-(2 * π * n * q / 3)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        exact mul_le_of_le_one_left (by positivity) he1
      calc Real.exp (-(2 * π * n * q / 3)) * spinCalPhic a q
          ≤ Real.exp (-(2 * π * n * q / 3)) * (4 * π * q + 24 / n) :=
            mul_le_mul_of_nonneg_left hφc_ub (Real.exp_pos _).le
        _ = Real.exp (-(2 * π * n * q / 3)) * (4 * π * q) +
              Real.exp (-(2 * π * n * q / 3)) * (24 / n) := mul_add _ _ _
        _ ≤ 6 / n + 24 / n := add_le_add ht1 ht2
        _ = (6 + 24) / n := by ring
    have hR2_eq : spinRc2 a ξ d = P2 * (Real.exp (-(12 * a) * (2 * π / 3) * q) *
        (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d))) := by
      unfold spinRc2; dsimp [P2, q]; ring
    rw [hR2_eq]
    have hprod_le : Real.exp (-(12 * a) * (2 * π / 3) * q) *
        (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)) ≤ 2 * (6 + 24) / n := by
      calc Real.exp (-(12 * a) * (2 * π / 3) * q) * (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d))
          ≤ Real.exp (-(12 * a) * (2 * π / 3) * q) * (2 * spinCalPhic a q) :=
            mul_le_mul_of_nonneg_left hpair_bd (Real.exp_pos _).le
        _ = 2 * (Real.exp (-(12 * a) * (2 * π / 3) * q) * spinCalPhic a q) := by ring
        _ ≤ 2 * ((6 + 24) / n) := by linarith
        _ = 2 * (6 + 24) / n := by ring
    have hprod_nn : 0 ≤ Real.exp (-(12 * a) * (2 * π / 3) * q) *
        (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)) :=
      mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (spinCalPhic_nonneg ha2 hxd_p) (spinCalPhic_nonneg ha2 hxd_m))
    calc P2 * (Real.exp (-(12 * a) * (2 * π / 3) * q) *
            (spinCalPhic a (ξ + d) * spinCalPhic a (ξ - d)))
        ≤ K0 * (2 * (6 + 24) / n) :=
          mul_le_mul hP2_bd hprod_le hprod_nn hK0_pos.le
      _ = K0 * (2 * (6 + 24)) / n := by ring
  refine ⟨⟨hRc_nn, ?_⟩, ?_⟩
  · have hRi := spinRInf_le_exp hd
    have hR1 : spinRc1 a ξ d ≤ spinRInf ξ d + K0 * 72 / n := by linarith [abs_sub_le_iff.mp hdiff_R1]
    have halg : K0 * 72 / n + K0 * (2 * (6 + 24)) / n = K0 * (72 + 2 * (6 + 24)) / n := by ring
    have hsum : spinRc a ξ d ≤
        Real.exp (-(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 - d ^ 2 / spinSigma0 ^ 2) +
          (K0 * (72 + 2 * (6 + 24))) / n := by
      unfold spinRc; linarith
    have hC : K0 * (72 + 2 * (6 + 24)) / n ≤ C_glob / n :=
      div_le_div_of_nonneg_right (by dsimp [C_glob]; linarith) (by linarith)
    linarith
  · intro hloc
    have hξ_lo : (3 / 4 : ℝ) * xiStar ≤ ξ := by
      have : |ξ - xiStar| ≤ r₀ := by linarith [abs_nonneg d]
      have := (abs_le.mp this).1
      dsimp [r₀] at this; linarith
    have hξ_hi : ξ ≤ (5 / 4 : ℝ) * xiStar := by
      have : |ξ - xiStar| ≤ r₀ := by linarith [abs_nonneg d]
      have := (abs_le.mp this).2
      dsimp [r₀] at this; linarith
    have hd_abs : |d| ≤ r₀ := by linarith [abs_nonneg (ξ - xiStar)]
    have hlt_d : |d| < ξ := by dsimp [r₀] at hd_abs; linarith [xiStar_pos]
    have hξ2_mem : ξ ^ 2 ∈ I_s := by
      refine ⟨?_, ?_⟩
      · have : (9 / 16 : ℝ) * xiStar ^ 2 ≤ ξ ^ 2 := by nlinarith [xiStar_pos]
        linarith [sq_pos_of_pos xiStar_pos]
      · have : ξ ^ 2 ≤ (25 / 16 : ℝ) * xiStar ^ 2 := by nlinarith [xiStar_pos]
        linarith [sq_pos_of_pos xiStar_pos]
    have hxs2_mem : xiStar ^ 2 ∈ I_s :=
      ⟨by linarith [sq_pos_of_pos xiStar_pos], by linarith [sq_pos_of_pos xiStar_pos]⟩
    have hB_bd : |calB (ξ ^ 2)| ≤ M_B * (ξ ^ 2 - xiStar ^ 2) ^ 2 := by
      let J_s : Set ℝ := Icc (min (xiStar ^ 2) (ξ ^ 2)) (max (xiStar ^ 2) (ξ ^ 2))
      have hJs_sub : J_s ⊆ I_s := fun t ht =>
        ⟨le_trans (le_min hxs2_mem.1 hξ2_mem.1) ht.1,
          ht.2.trans (max_le hxs2_mem.2 hξ2_mem.2)⟩
      have hB'_bd : ∀ t ∈ J_s, |calBDeriv t| ≤ M_B * |ξ ^ 2 - xiStar ^ 2| := by
        intro t ht
        have htI : t ∈ I_s := hJs_sub ht
        have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
          (fun u hu => (hasDerivAt_calBDeriv (hIs_sub hu)).differentiableAt)
          (fun u hu => by
            rw [(hasDerivAt_calBDeriv (hIs_sub hu)).deriv, Real.norm_eq_abs]
            have hle : |calBDeriv2 u| ≤ |calBDeriv2 K_B| := hKB_max hu
            exact hle.trans (le_max_left (|calBDeriv2 K_B|) 1))
          (convex_Icc _ _) hxs2_mem htI
        have h1 : |calBDeriv t| ≤ M_B * |t - xiStar ^ 2| := by
          simpa [Real.norm_eq_abs, calBDeriv_xiStar_sq] using hmvt
        have hseg : |t - xiStar ^ 2| ≤ |ξ ^ 2 - xiStar ^ 2| := by
          rcases le_total (xiStar ^ 2) (ξ ^ 2) with hle | hle
          · have ht1 : xiStar ^ 2 ≤ t := by simpa [J_s, min_eq_left hle] using ht.1
            have ht2 : t ≤ ξ ^ 2 := by simpa [J_s, max_eq_right hle] using ht.2
            rw [abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg (sub_nonneg.mpr hle)]
            linarith
          · have ht1 : ξ ^ 2 ≤ t := by simpa [J_s, min_eq_right hle] using ht.1
            have ht2 : t ≤ xiStar ^ 2 := by simpa [J_s, max_eq_left hle] using ht.2
            rw [abs_of_nonpos (sub_nonpos.mpr ht2), abs_of_nonpos (sub_nonpos.mpr hle)]
            linarith
        exact h1.trans (mul_le_mul_of_nonneg_left hseg hMB_pos.le)
      have hmvt2 := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hasDerivAt_calB (hIs_sub (hJs_sub ht))).differentiableAt)
        (fun t ht => by
          rw [(hasDerivAt_calB (hIs_sub (hJs_sub ht))).deriv, Real.norm_eq_abs]
          exact hB'_bd t ht)
        (convex_Icc _ _) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
      have h2 : |calB (ξ ^ 2)| ≤ M_B * |ξ ^ 2 - xiStar ^ 2| * |ξ ^ 2 - xiStar ^ 2| := by
        simpa [Real.norm_eq_abs, calB_xiStar_sq] using hmvt2
      calc |calB (ξ ^ 2)| ≤ M_B * |ξ ^ 2 - xiStar ^ 2| * |ξ ^ 2 - xiStar ^ 2| := h2
        _ = M_B * (ξ ^ 2 - xiStar ^ 2) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
    have hL_bd : |Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
        2 * Real.log (spinCalPhi ξ)| ≤ 2 * M_L * d ^ 2 := by
      let g : ℝ → ℝ := fun t => Real.log (spinCalPhi (ξ + t)) + Real.log (spinCalPhi (ξ - t))
      let g' : ℝ → ℝ := fun t => logPhiDeriv (ξ + t) - logPhiDeriv (ξ - t)
      have hg_deriv : ∀ t : ℝ, |t| ≤ r₀ → HasDerivAt g (g' t) t := by
        intro t ht
        have hp : 0 < ξ + t := by dsimp [r₀] at *; linarith [abs_le.mp ht, xiStar_pos]
        have hm : 0 < ξ - t := by dsimp [r₀] at *; linarith [abs_le.mp ht, xiStar_pos]
        have ha : HasDerivAt (fun u : ℝ => ξ + u) 1 t := (hasDerivAt_id t).const_add ξ
        have hb : HasDerivAt (fun u : ℝ => ξ - u) (-1) t := by
          simpa [sub_eq_add_neg, add_comm] using ((hasDerivAt_id t).neg).const_add ξ
        have h1 : HasDerivAt (fun u => Real.log (spinCalPhi (ξ + u))) (logPhiDeriv (ξ + t)) t :=
          ((hasDerivAt_log_spinCalPhi hp).comp t ha).congr_deriv (by ring)
        have h2 : HasDerivAt (fun u => Real.log (spinCalPhi (ξ - u))) (-logPhiDeriv (ξ - t)) t :=
          ((hasDerivAt_log_spinCalPhi hm).comp t hb).congr_deriv (by ring)
        exact h1.add h2
      have hJ_r0 : ∀ t ∈ Icc (min 0 d) (max 0 d), |t| ≤ |d| := by
        intro t ht
        rcases le_total 0 d with hd0 | hd0
        · have h1 : 0 ≤ t := by simpa [min_eq_left hd0] using ht.1
          have h2 : t ≤ d := by simpa [max_eq_right hd0] using ht.2
          rw [abs_of_nonneg h1, abs_of_nonneg hd0]; exact h2
        · have h1 : d ≤ t := by simpa [min_eq_right hd0] using ht.1
          have h2 : t ≤ 0 := by simpa [max_eq_left hd0] using ht.2
          rw [abs_of_nonpos h2, abs_of_nonpos hd0]; linarith
      have hg'_bd : ∀ t ∈ Icc (min 0 d) (max 0 d), |g' t| ≤ 2 * M_L * |d| := by
        intro t ht
        have ht_le := hJ_r0 t ht
        have hxm : ξ - t ∈ I_x := ⟨by dsimp [r₀] at *; linarith [abs_le.mp (ht_le.trans hd_abs)],
          by dsimp [r₀] at *; linarith [abs_le.mp (ht_le.trans hd_abs)]⟩
        have hxp : ξ + t ∈ I_x := ⟨by dsimp [r₀] at *; linarith [abs_le.mp (ht_le.trans hd_abs)],
          by dsimp [r₀] at *; linarith [abs_le.mp (ht_le.trans hd_abs)]⟩
        have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
          (fun u hu => (hasDerivAt_logPhiDeriv (hIx_sub hu)).differentiableAt)
          (fun u hu => by
            rw [(hasDerivAt_logPhiDeriv (hIx_sub hu)).deriv, Real.norm_eq_abs]
            have hle : |logPhiDeriv2 u| ≤ |logPhiDeriv2 K_L| := hKL_max hu
            exact hle.trans (le_max_left (|logPhiDeriv2 K_L|) 1))
          (convex_Icc _ _) hxm hxp
        have hdiff_eq : (ξ + t) - (ξ - t) = 2 * t := by ring
        have h1 : |g' t| ≤ M_L * (2 * |t|) := by
          dsimp [g']
          simpa [Real.norm_eq_abs, hdiff_eq, abs_mul] using hmvt
        have h2 : 2 * |t| ≤ 2 * |d| := by linarith
        calc |g' t| ≤ M_L * (2 * |t|) := h1
          _ ≤ M_L * (2 * |d|) := mul_le_mul_of_nonneg_left h2 hML_pos.le
          _ = 2 * M_L * |d| := by ring
      have hmvt_g := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hg_deriv t ((hJ_r0 t ht).trans hd_abs)).differentiableAt)
        (fun t ht => by
          rw [(hg_deriv t ((hJ_r0 t ht).trans hd_abs)).deriv, Real.norm_eq_abs]
          exact hg'_bd t ht)
        (convex_Icc _ _) ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
      have hg0 : g 0 = 2 * Real.log (spinCalPhi ξ) := by
        dsimp [g]; ring_nf
      calc |Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
              2 * Real.log (spinCalPhi ξ)|
          = ‖g d - g 0‖ := by rw [Real.norm_eq_abs, hg0]
        _ ≤ (2 * M_L * |d|) * ‖d - 0‖ := hmvt_g
        _ = 2 * M_L * d ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, ← sq, sq_abs]
    have hlog_Rinf := log_spinRInf_eq hlt_d
    have hsq_diff : (ξ ^ 2 - xiStar ^ 2) ^ 2 ≤ ((9 / 4 : ℝ) * xiStar) ^ 2 * (ξ - xiStar) ^ 2 := by
      have hsum_le : |ξ + xiStar| ≤ (9 / 4 : ℝ) * xiStar := by
        rw [abs_of_nonneg (by linarith [xiStar_pos])]
        linarith
      have halg : (ξ ^ 2 - xiStar ^ 2) ^ 2 = (ξ + xiStar) ^ 2 * (ξ - xiStar) ^ 2 := by ring
      rw [halg]
      have hsq : (ξ + xiStar) ^ 2 ≤ ((9 / 4 : ℝ) * xiStar) ^ 2 := by
        rw [← sq_abs (ξ + xiStar)]
        exact pow_le_pow_left₀ (abs_nonneg _) hsum_le 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hlog_bd : |Real.log (spinRInf ξ d)| ≤ K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) := by
      have htri1 : |Real.log (spinRInf ξ d)| ≤
          |calB (ξ ^ 2)| +
            |Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
              2 * Real.log (spinCalPhi ξ)| +
            |(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2| + |d ^ 2 / spinSigma0 ^ 2| := by
        rw [hlog_Rinf]
        have ha1 := abs_sub
          (calB (ξ ^ 2) + (Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
            2 * Real.log (spinCalPhi ξ)) - (1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2)
          (d ^ 2 / spinSigma0 ^ 2)
        have ha2 := abs_sub
          (calB (ξ ^ 2) + (Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
            2 * Real.log (spinCalPhi ξ)))
          ((1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2)
        have ha3 := abs_add_le (calB (ξ ^ 2))
          (Real.log (spinCalPhi (ξ + d)) + Real.log (spinCalPhi (ξ - d)) -
            2 * Real.log (spinCalPhi ξ))
        linarith
      have hq1 : |(1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2| = (1 / 2 : ℝ) * (ξ ^ 2 - xiStar ^ 2) ^ 2 :=
        abs_of_nonneg (by positivity)
      have hq2 : |d ^ 2 / spinSigma0 ^ 2| = (1 / spinSigma0 ^ 2) * d ^ 2 := by
        rw [abs_of_nonneg (by positivity)]; ring
      rw [hq1, hq2] at htri1
      have hstep1 : |Real.log (spinRInf ξ d)| ≤
          (M_B + 1 / 2) * (ξ ^ 2 - xiStar ^ 2) ^ 2 + (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 := by
        linarith
      have hstep2 : (M_B + 1 / 2) * (ξ ^ 2 - xiStar ^ 2) ^ 2 +
            (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 ≤
          (M_B + 1 / 2) * (((9 / 4 : ℝ) * xiStar) ^ 2 * (ξ - xiStar) ^ 2) +
            (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 := by
        have hMBnn : 0 ≤ M_B + 1 / 2 := by positivity
        linarith [mul_le_mul_of_nonneg_left hsq_diff hMBnn]
      have h1 : (M_B + 1 / 2) * ((9 / 4 : ℝ) * xiStar) ^ 2 ≤ K_quad := by
        dsimp [K_quad]; linarith [show 0 ≤ 2 * M_L + 1 / spinSigma0 ^ 2 by positivity]
      have h2 : 2 * M_L + 1 / spinSigma0 ^ 2 ≤ K_quad := by
        dsimp [K_quad]; linarith [show 0 ≤ (M_B + 1 / 2) * ((9 / 4 : ℝ) * xiStar) ^ 2 by positivity]
      have hstep3 : (M_B + 1 / 2) * (((9 / 4 : ℝ) * xiStar) ^ 2 * (ξ - xiStar) ^ 2) +
            (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 ≤
          K_quad * (ξ - xiStar) ^ 2 + K_quad * d ^ 2 := by
        rw [← mul_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      calc |Real.log (spinRInf ξ d)|
          ≤ (M_B + 1 / 2) * (ξ ^ 2 - xiStar ^ 2) ^ 2 +
              (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 := hstep1
        _ ≤ (M_B + 1 / 2) * (((9 / 4 : ℝ) * xiStar) ^ 2 * (ξ - xiStar) ^ 2) +
              (2 * M_L + 1 / spinSigma0 ^ 2) * d ^ 2 := hstep2
        _ ≤ K_quad * (ξ - xiStar) ^ 2 + K_quad * d ^ 2 := hstep3
        _ = K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) := by ring
    have hlog_M : |Real.log (spinRInf ξ d)| ≤ M_log := by
      have hsum_r0 : (ξ - xiStar) ^ 2 + d ^ 2 ≤ r₀ ^ 2 := by
        have hsq : |ξ - xiStar| ^ 2 + |d| ^ 2 ≤ (|ξ - xiStar| + |d|) ^ 2 := by
          have : 0 ≤ 2 * |ξ - xiStar| * |d| := by positivity
          linarith [add_sq (|ξ - xiStar|) (|d|)]
        rw [sq_abs, sq_abs] at hsq
        exact hsq.trans (pow_le_pow_left₀ (by positivity) hloc 2)
      calc |Real.log (spinRInf ξ d)| ≤ K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) := hlog_bd
        _ ≤ K_quad * r₀ ^ 2 := mul_le_mul_of_nonneg_left hsum_r0 hKq_pos.le
        _ = M_log := rfl
    have hRinf_pos : 0 < spinRInf ξ d := by
      have hxd_p0 : 0 < ξ + d := by linarith [abs_lt.mp hlt_d]
      have hxd_m0 : 0 < ξ - d := by linarith [abs_lt.mp hlt_d]
      unfold spinRInf
      have h1 := spinCalPhi_pos hxd_p0
      have h2 := spinCalPhi_pos hxd_m0
      have h3 := spinCalPhi_pos xiStar_pos
      positivity
    have hRinf_loc : |spinRInf ξ d - 1| ≤ Real.exp M_log * K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) := by
      have hmvt_exp := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ => (Real.hasDerivAt_exp t).differentiableAt)
        (fun t ht => by
          rw [(Real.hasDerivAt_exp t).deriv, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
          exact Real.exp_le_exp.mpr ht.2)
        (convex_Icc (-M_log) M_log) ⟨by linarith, hMlog_pos.le⟩ (abs_le.mp hlog_M)
      rw [Real.exp_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero,
        Real.exp_log hRinf_pos] at hmvt_exp
      calc |spinRInf ξ d - 1| ≤ Real.exp M_log * |Real.log (spinRInf ξ d)| := hmvt_exp
        _ ≤ Real.exp M_log * (K_quad * ((ξ - xiStar) ^ 2 + d ^ 2)) :=
            mul_le_mul_of_nonneg_left hlog_bd (Real.exp_pos M_log).le
        _ = Real.exp M_log * K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) := by ring
    have hRc2_nn : 0 ≤ spinRc2 a ξ d := by
      have hφ1 : 0 ≤ spinCalPhic a (ξ + d) := spinCalPhic_nonneg ha2 hxd_p
      have hφ2 : 0 ≤ spinCalPhic a (ξ - d) := spinCalPhic_nonneg ha2 hxd_m
      unfold spinRc2
      have := spinCalPhi_pos xiStar_pos
      positivity
    have htri_all : |spinRc a ξ d - 1| ≤
        |spinRInf ξ d - 1| + |spinRc1 a ξ d - spinRInf ξ d| + spinRc2 a ξ d := by
      unfold spinRc
      have h1 := abs_add_le ((spinRc1 a ξ d - spinRInf ξ d) + (spinRInf ξ d - 1)) (spinRc2 a ξ d)
      have h2 := abs_add_le (spinRc1 a ξ d - spinRInf ξ d) (spinRInf ξ d - 1)
      rw [abs_of_nonneg hRc2_nn] at h1
      have heq : spinRc1 a ξ d + spinRc2 a ξ d - 1 =
          (spinRc1 a ξ d - spinRInf ξ d + (spinRInf ξ d - 1)) + spinRc2 a ξ d := by ring
      rw [heq]
      linarith
    have hinv_eq : K0 * 72 / n + K0 * (2 * (6 + 24)) / n = K0 * (72 + 2 * (6 + 24)) * n⁻¹ := by
      ring
    calc |spinRc a ξ d - 1|
        ≤ Real.exp M_log * K_quad * ((ξ - xiStar) ^ 2 + d ^ 2) +
            K0 * (72 + 2 * (6 + 24)) * n⁻¹ := by
          linarith [htri_all, hRinf_loc, hdiff_R1, hRc2_bd, hinv_eq]
      _ ≤ C₁ * ((ξ - xiStar) ^ 2 + d ^ 2) + C₁ * n⁻¹ := by
          have h1 : Real.exp M_log * K_quad ≤ C₁ := by dsimp [C₁]; linarith
          have h2 : K0 * (72 + 2 * (6 + 24)) ≤ C₁ := by
            dsimp [C₁]
            have : 0 ≤ Real.exp M_log * K_quad := by positivity
            linarith
          have hn_nn : 0 ≤ n⁻¹ := inv_nonneg.mpr (by linarith)
          exact add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
            (mul_le_mul_of_nonneg_right h2 hn_nn)
      _ = C₁ * ((ξ - xiStar) ^ 2 + d ^ 2 + n⁻¹) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.scalC1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.scalC1

end FormalResearch.ModularBootstrap.Spin

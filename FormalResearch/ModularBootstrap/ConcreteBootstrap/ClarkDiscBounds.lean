module

public import FormalResearch.Special.AiryCft2Ball
public import FormalResearch.Special.AiryCft2Clark

/-!
# Integral-split defect bound for a general pair `(N, M)` and for the Clark functions `ψ_α`

`Theorem FT-L.FW` Step 4 (`lower_o1_two_edge.tex`, `wone:ftlfw`): the Hermite-Biehler quadrature of
`lem:hb-quadrature` on a good circle of `N = P Ai + Q Ai'` (Lemma 1.0′, `gt:1.0p`), in the form needed by the
arc estimates of `teb:bootstrap`: the quadrature defect is bounded by an integral over the circle of any integrable
majorant `B` of `‖f‖ / e`.

* `cft2_defect_ball_split`: the generic statement (an entire `N` with `CftCircleData`, an entire `M`, a positive
  weight `env`, ratio bounds `‖M/N ∓ i‖ env ≤ C` on the half circles, `f` holomorphic on a larger disc):
  `‖-π Σ f(c_i) M(c_i)/N'(c_i) - ∫_{-R}^{R} f‖ ≤ (C/2) R ∫_{-π}^{π} B`.  Its case `N = Ai`, `M = Bi`,
  `env = airyEnv`, `C = 30 √π` is `airy_defect_ball_split` (`AiryDiscBounds`).
* `clark_defect_ball_split`: the case `N = P Ai + Q Ai'`, `M = P Bi + Q Bi'` (`Q ≠ 0`), the sum over the finite set of
  the zeros of `N` in the closed disc with the weights `D/N'² = 1/K(z, z)`; for `P = cos α`, `Q = -sin α` these are the
  nodes `z_n(α)` of `ψ_α` and `K(z, z) = Ai'(z)² - z Ai(z)²`.
* `clark_defect_ball_split_uniform`: the constants are uniform for `α` with `|sin α| ≥ σ > 0` (the compact sets of
  `ℝ` avoiding `sin α = 0`, equivalently `|cot α|` bounded and `|sin α|` bounded below): one `C₀`, `k₀` such
  that every `[k, k + 1]`, `k ≥ k₀` contains a good radius `r` (independent of `α`) on which the hypotheses of
  `clark_defect_ball_split` hold with `C = C₀`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special

/-- **Integral-split defect bound for a general pair `(N, M)`** on a circle `‖w‖ = R` (`CftCircleData N c s R`):
`f` holomorphic on `ball 0 R'` (`R < R'`), `M` entire, `‖M/N - i‖ env ≤ C` on the upper and `‖M/N + i‖ env ≤ C` on the
lower half circle, and `‖f (R e^{iθ})‖ / env (R e^{iθ}) ≤ B θ` for an integrable `B`:
`‖-π Σ_{i ∈ s} f(c_i) M(c_i)/N'(c_i) - ∫_{-R}^{R} f‖ ≤ (C/2) R ∫_{-π}^{π} B`. -/
theorem cft2_defect_ball_split {N M f : ℂ → ℂ} {env : ℂ → ℝ} {c : ℕ → ℂ} {s : Finset ℕ} {R R' C : ℝ}
    (hD : CftCircleData N c s R) (hM : Differentiable ℂ M) (hRR : R < R')
    (hf : DifferentiableOn ℂ f (ball 0 R')) (henv : ∀ w : ℂ, 0 < env w)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖M w / N w - I‖ * env w ≤ C)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖M w / N w + I‖ * env w ≤ C)
    {B : ℝ → ℝ} (hB_int : IntervalIntegrable B volume (-π) π)
    (hB_bd : ∀ θ ∈ Icc (-π) π, ‖f (circleMap 0 R θ)‖ / env (circleMap 0 R θ) ≤ B θ) :
    ‖(-(π : ℂ)) * (∑ i ∈ s, f (c i) * M (c i) / deriv N (c i)) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (C / 2 * R) * ∫ θ in (-π)..π, B θ := by
  have hR := hD.radius_pos
  have hN := hD.entire
  obtain ⟨F, _, hF⟩ := hf.isExactOn_ball.with_val_at 0 0
  have hF' : ∀ z ∈ ball (0 : ℂ) R', HasDerivAt F (f z) z := fun z hz => hF z hz
  set w : ℝ → ℂ := circleMap 0 R
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    simp [w, norm_circleMap_zero, abs_of_pos hR]
  have hNw : ∀ θ, N (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  have hfc : Continuous (fun θ : ℝ => f (w θ)) :=
    hf.continuousOn.comp_continuous hwc (fun θ => cft2_mem_ball hR hRR θ)
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ)
  have hJc : Continuous J := (hwc.mul continuous_const).mul hfc
  set Rp : ℝ → ℂ := fun θ => M (w θ) / N (w θ) - I
  set Rm : ℝ → ℂ := fun θ => M (w θ) / N (w θ) + I
  have hQc : Continuous (fun θ => M (w θ) / N (w θ)) :=
    (hM.continuous.comp hwc).div (hN.continuous.comp hwc) hNw
  have hRpc : Continuous Rp := hQc.sub continuous_const
  have hRmc : Continuous Rm := hQc.add continuous_const
  have hcirc : ∮ z in C(0, R), f z * M z / N z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (M (w θ) / N (w θ)) := by
    rw [circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, J, w]
    ring
  have hΦc : Continuous (fun θ => J θ * (M (w θ) / N (w θ))) := hJc.mul hQc
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (M (w θ) / N (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 h2]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Rp]; ring
  have hlow : ∫ θ in π..(2 * π), J θ * (M (w θ) / N (w θ)) =
      (∫ θ in π..(2 * π), J θ * Rm θ) - I * (∫ θ in π..(2 * π), J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rm θ) volume π (2 * π) :=
      (hJc.mul hRmc).intervalIntegrable π (2 * π)
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume π (2 * π) :=
      (hJc.const_mul I).intervalIntegrable π (2 * π)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub h1 h2]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Rm]; ring
  have hJup : ∫ θ in (0 : ℝ)..π, J θ = F (-(R : ℂ)) - F R := by
    have := cft2_arc_ball hR hRR hF' hf 0 π
    rw [cftDef_circleMap_pi, cftDef_circleMap_zero] at this
    simpa [J, w] using this
  have hJlow : ∫ θ in π..(2 * π), J θ = F R - F (-(R : ℂ)) := by
    have := cft2_arc_ball hR hRR hF' hf π (2 * π)
    rw [cftDef_circleMap_pi, cftDef_circleMap_two_pi] at this
    simpa [J, w] using this
  have hdiam' : ∫ x in (-R)..R, f (x : ℂ) = F R - F (-(R : ℂ)) := by
    simpa using cft2_diam_ball hR hRR hF' hf
  have hres := cft2_residue_ball hD hRR (H := fun z => f z * M z) (hf.mul hM.differentiableOn)
  rw [hcirc, ← intervalIntegral.integral_add_adjacent_intervals
    (hΦc.intervalIntegrable 0 π) (hΦc.intervalIntegrable π (2 * π)),
    hup, hlow, hJup, hJlow] at hres
  set T : ℂ := ∑ i ∈ s, f (c i) * M (c i) / deriv N (c i)
  set A1 : ℂ := ∫ θ in (0 : ℝ)..π, J θ * Rp θ
  set A2 : ℂ := ∫ θ in π..(2 * π), J θ * Rm θ
  have key : (-(π : ℂ)) * T - ∫ x in (-R)..R, f (x : ℂ) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres - ((π : ℂ) * T + (F R - F (-(R : ℂ)))) * hI
  have hle_neg_pi : -π ≤ π := by linarith [Real.pi_pos]
  have hB_int_0pi : IntervalIntegrable B volume 0 π :=
    hB_int.mono_set (by rw [Set.uIcc_of_le hle_neg_pi,
      Set.uIcc_of_le Real.pi_pos.le]; exact Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
  have hB_int_negpi0 : IntervalIntegrable B volume (-π) 0 :=
    hB_int.mono_set (by rw [Set.uIcc_of_le hle_neg_pi,
      Set.uIcc_of_le (by linarith [Real.pi_pos])]; exact Icc_subset_Icc le_rfl Real.pi_pos.le)
  have hA1_bd : ‖A1‖ ≤ (C * R) * ∫ θ in (0 : ℝ)..π, B θ := by
    dsimp [A1]
    have hnorm_le : ‖∫ θ in (0 : ℝ)..π, J θ * Rp θ‖ ≤
        ∫ θ in (0 : ℝ)..π, ‖J θ * Rp θ‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
    refine hnorm_le.trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on Real.pi_pos.le
      ((hJc.mul hRpc).norm.intervalIntegrable 0 π) (hB_int_0pi.const_mul _) fun θ hθ => ?_
    have him : 0 ≤ (w θ).im := by
      simp only [w, cftDef_im_circleMap]
      exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
    have hRp_bd := hRp (w θ) (hwn θ) him
    have he_pos : 0 < env (w θ) := henv (w θ)
    have hf_bd : ‖f (w θ)‖ ≤ B θ * env (w θ) := by
      have h1 := hB_bd θ ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
      exact (div_le_iff₀ he_pos).mp h1
    have hB_nn : 0 ≤ B θ := by
      have := hB_bd θ ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
      exact (div_nonneg (norm_nonneg _) he_pos.le).trans this
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one]
    calc R * ‖f (w θ)‖ * ‖M (w θ) / N (w θ) - I‖
        ≤ R * (B θ * env (w θ)) * ‖M (w θ) / N (w θ) - I‖ := by gcongr
      _ = R * B θ * (‖M (w θ) / N (w θ) - I‖ * env (w θ)) := by ring
      _ ≤ R * B θ * C := by gcongr
      _ = C * R * B θ := by ring
  have hA2_bd : ‖A2‖ ≤ (C * R) * ∫ θ in (-π)..(0 : ℝ), B θ := by
    dsimp [A2]
    have hshift : ∫ θ in π..(2 * π), J θ * Rm θ =
        ∫ θ in (-π)..(0 : ℝ), J (θ + 2 * π) * Rm (θ + 2 * π) := by
      have := intervalIntegral.integral_comp_add_right (fun θ => J θ * Rm θ) (2 * π) (a := -π) (b := 0)
      simpa only [neg_add_cancel_right, zero_add, show -π + 2 * π = π by ring] using this.symm
    have hper : ∀ θ : ℝ, w (θ + 2 * π) = w θ := fun θ => by
      simp only [w, circleMap, Complex.ofReal_add, add_mul, Complex.exp_add]
      rw [show (((2 * π : ℝ) : ℂ) * I) = (2 * π : ℝ) * I by rfl]
      rw [show (↑(2 * π) : ℂ) * I = 2 * ↑π * I by push_cast; rfl, Complex.exp_two_pi_mul_I, mul_one]
    have hper2 : ∀ θ : ℝ, J (θ + 2 * π) * Rm (θ + 2 * π) = J θ * Rm θ := fun θ => by
      simp only [J, Rm, hper θ]
    rw [hshift]
    have hcongr : ∫ θ in (-π)..(0 : ℝ), J (θ + 2 * π) * Rm (θ + 2 * π) =
        ∫ θ in (-π)..(0 : ℝ), J θ * Rm θ :=
      intervalIntegral.integral_congr fun θ _ => hper2 θ
    rw [hcongr]
    have hnorm_le : ‖∫ θ in (-π)..(0 : ℝ), J θ * Rm θ‖ ≤
        ∫ θ in (-π)..(0 : ℝ), ‖J θ * Rm θ‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos])
    refine hnorm_le.trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      ((hJc.mul hRmc).norm.intervalIntegrable (-π) 0) (hB_int_negpi0.const_mul _) fun θ hθ => ?_
    have him : (w θ).im ≤ 0 := by
      simp only [w, cftDef_im_circleMap]
      have hsin : Real.sin θ ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -θ) (by linarith [hθ.2]) (by linarith [hθ.1])
        rw [Real.sin_neg] at this; linarith
      exact mul_nonpos_of_nonneg_of_nonpos hR.le hsin
    have hRm_bd := hRm (w θ) (hwn θ) him
    have he_pos : 0 < env (w θ) := henv (w θ)
    have hf_bd : ‖f (w θ)‖ ≤ B θ * env (w θ) := by
      have h1 := hB_bd θ ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
      exact (div_le_iff₀ he_pos).mp h1
    have hB_nn : 0 ≤ B θ := by
      have := hB_bd θ ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
      exact (div_nonneg (norm_nonneg _) he_pos.le).trans this
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one]
    calc R * ‖f (w θ)‖ * ‖M (w θ) / N (w θ) + I‖
        ≤ R * (B θ * env (w θ)) * ‖M (w θ) / N (w θ) + I‖ := by gcongr
      _ = R * B θ * (‖M (w θ) / N (w θ) + I‖ * env (w θ)) := by ring
      _ ≤ R * B θ * C := by gcongr
      _ = C * R * B θ := by ring
  have hsum_int : (∫ θ in (-π)..(0 : ℝ), B θ) + (∫ θ in (0 : ℝ)..π, B θ) =
      ∫ θ in (-π)..π, B θ :=
    intervalIntegral.integral_add_adjacent_intervals hB_int_negpi0 hB_int_0pi
  rw [key, norm_mul]
  have hI2 : ‖(I / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hI2]
  calc (1 / 2 : ℝ) * ‖A1 + A2‖
      ≤ (1 / 2 : ℝ) * (‖A1‖ + ‖A2‖) := mul_le_mul_of_nonneg_left (norm_add_le A1 A2) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((C * R) * (∫ θ in (0 : ℝ)..π, B θ) +
          (C * R) * (∫ θ in (-π)..(0 : ℝ), B θ)) := by gcongr
    _ = (C / 2 * R) * ((∫ θ in (-π)..(0 : ℝ), B θ) + (∫ θ in (0 : ℝ)..π, B θ)) := by ring
    _ = (C / 2 * R) * ∫ θ in (-π)..π, B θ := by rw [hsum_int]

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.cft2_defect_ball_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cft2_defect_ball_split

/-! ### The Clark pair `N = P Ai + Q Ai'`, `M = P Bi + Q Bi'` -/

/-- **Integral-split defect bound for `N = P Ai + Q Ai'` on a `CftCircleData` circle.**  The weights are
`D(t)/N'(t)² = 1/K(t, t)` (`airyNC_weight_eq`, `airyNC_weight_eq_inv_K`), `D = P² - z Q²`. -/
theorem clark_defect_ball_split_cd (P Q : ℝ) {c : ℕ → ℂ} {s : Finset ℕ} {R R' C : ℝ}
    (hD : CftCircleData (airyNC P Q) c s R) (hRR : R < R') {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖airyMC P Q w / airyNC P Q w - I‖ * airyEnv w ≤ C)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖airyMC P Q w / airyNC P Q w + I‖ * airyEnv w ≤ C)
    {B : ℝ → ℝ} (hB_int : IntervalIntegrable B volume (-π) π)
    (hB_bd : ∀ θ ∈ Icc (-π) π,
      ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ) :
    ‖(∑ i ∈ s, f (c i) * (airyDC P Q (c i) / airyNC' P Q (c i) ^ 2)) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (C / 2 * R) * ∫ θ in (-π)..π, B θ := by
  have h := cft2_defect_ball_split hD (differentiable_airyMC P Q) hRR hf airyEnv_pos hRp hRm
    hB_int hB_bd
  have hsum : (-(π : ℂ)) * (∑ i ∈ s, f (c i) * airyMC P Q (c i) / deriv (airyNC P Q) (c i)) =
      ∑ i ∈ s, f (c i) * (airyDC P Q (c i) / airyNC' P Q (c i) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hd := hD.simple i hi
    rw [deriv_airyNC] at hd ⊢
    rw [← airyNC_weight_eq P Q (hD.zero i hi) hd]
    ring
  rw [hsum] at h
  exact h

/-- **Integral-split defect bound for `N = P Ai + Q Ai'`, `Q ≠ 0`, over the finite set of its zeros in the closed disc**
(`lem:hb-quadrature`(1)-(2) with `f` holomorphic only on `ball 0 R'`): for `S` the set of the zeros of `N` in
`‖z‖ ≤ R`, `N ≠ 0` on `‖z‖ = R`, the ratio bounds `‖M/N ∓ i‖ e ≤ C` on the half circles and
`‖f‖/e ≤ B(θ)` on the circle,
`‖Σ_{t∈S} f(t) D(t)/N'(t)² - ∫_{-R}^{R} f‖ ≤ (C/2) R ∫_{-π}^{π} B`. -/
theorem clark_defect_ball_split (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} {R R' C : ℝ} (hr : 0 < R)
    (hRR : R < R') (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hN : ∀ u : ℂ, ‖u‖ = R → airyNC P Q u ≠ 0)
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖airyMC P Q w / airyNC P Q w - I‖ * airyEnv w ≤ C)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖airyMC P Q w / airyNC P Q w + I‖ * airyEnv w ≤ C)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ S ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ R)
    {B : ℝ → ℝ} (hB_int : IntervalIntegrable B volume (-π) π)
    (hB_bd : ∀ θ ∈ Icc (-π) π,
      ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ) :
    ‖(∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (C / 2 * R) * ∫ θ in (-π)..π, B θ := by
  have hin : ∀ t ∈ S, ‖t‖ < R := by
    intro t ht
    obtain ⟨h0, h1⟩ := (hS t).mp ht
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd h0 (hN t h)
  have hder : ∀ t ∈ S, deriv (airyNC P Q) t ≠ 0 := by
    intro t ht
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have him := airyNC_zero_im P Q hQ h0
    have e : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [e] at h0
    rw [deriv_airyNC, e]
    exact (airyNC_zero_weight_pos P Q hQ h0).2
  obtain ⟨c, s, hD, hsum⟩ := cft2_circleData_of_finset (differentiable_airyNC P Q) hr S hin
    (fun t ht => ((hS t).mp ht).1) hder (fun w hw h0 => (hS w).mpr ⟨h0, hw⟩)
  have h := clark_defect_ball_split_cd P Q hD hRR hf hRp hRm hB_int hB_bd
  rw [hsum (fun t => f t * (airyDC P Q t / airyNC' P Q t ^ 2))] at h
  exact h

/-- The Clark form of `clark_defect_ball_split_cd`: weights `1/K(t, t)`, `K = Ai'² - z Ai²`
(`airyNC_weight_eq_inv_K`; no normalisation of `(P, Q)` is needed). -/
theorem clark_defect_ball_split_K (P Q : ℝ) (hQ : Q ≠ 0) {c : ℕ → ℂ} {s : Finset ℕ} {R R' C : ℝ}
    (hD : CftCircleData (airyNC P Q) c s R) (hRR : R < R') {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖airyMC P Q w / airyNC P Q w - I‖ * airyEnv w ≤ C)
    (hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖airyMC P Q w / airyNC P Q w + I‖ * airyEnv w ≤ C)
    {B : ℝ → ℝ} (hB_int : IntervalIntegrable B volume (-π) π)
    (hB_bd : ∀ θ ∈ Icc (-π) π,
      ‖f (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ) :
    ‖(∑ i ∈ s, f (c i) / (deriv airyAiC (c i) ^ 2 - c i * airyAiC (c i) ^ 2)) -
        ∫ x in (-R)..R, f (x : ℂ)‖ ≤ (C / 2 * R) * ∫ θ in (-π)..π, B θ := by
  have h := clark_defect_ball_split_cd P Q hD hRR hf hRp hRm hB_int hB_bd
  have hsum : ∑ i ∈ s, f (c i) * (airyDC P Q (c i) / airyNC' P Q (c i) ^ 2) =
      ∑ i ∈ s, f (c i) / (deriv airyAiC (c i) ^ 2 - c i * airyAiC (c i) ^ 2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [airyNC_weight_eq_inv_K P Q hQ (hD.zero i hi)]
    ring
  rw [hsum] at h
  exact h

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_defect_ball_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_defect_ball_split

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.clark_defect_ball_split_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_defect_ball_split_K

end FormalResearch.ModularBootstrap.ConcreteBootstrap

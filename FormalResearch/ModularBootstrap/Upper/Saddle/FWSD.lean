module

public import FormalResearch.ModularBootstrap.Upper.Saddle.SDV

/-!
# Lemma `FW-SD` (Part 2): Fixed-Order `p` Analytic Edge Transfer

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma `fw:SDp` (`FW-SD`), part (2),
l.278–334 (`fw:e1.4`–`fw:e1.5`).

Deduces the fixed-order `p : ℕ` two-saddle steepest-descent asymptotic (`fw:e1.4`) directly from
`lemma_SD_V_prime` applied to `A_p(b) = e^{-iπp/2} (b/x)^p A_0^∘(b) (1 + ε_p(kb))` with uniform
constants `M = M₀ + 4p + 1` and `M' = M₀' + 16p + 1`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Fixed-order `p` amplitude, integral, and Hankel-order-`p` hypotheses -/

/-- Order-zero base amplitude `A_0^∘(b) = ℰ(b) e^{Φ₁(b)} b^{1/2}` (`upper_transfer.tex`, l.285). -/
noncomputable def fwsdAmplitudeCirc (ℰ Φ₁ : ℂ → ℂ) (b : ℂ) : ℂ :=
  ℰ b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)

/-- Fixed-order `p` amplitude `A_p(b) = e^{-iπp/2} (b/x)^p A_0^∘(b) (1 + ε_p(kb))`
(`upper_transfer.tex`, l.319). -/
noncomputable def fwsdAmplitude (p : ℕ) (x n : ℝ) (ℰ Φ₁ εp : ℂ → ℂ) (b : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (b / (x : ℂ)) ^ p *
    fwsdAmplitudeCirc ℰ Φ₁ b * (1 + εp ((sdvWave n x : ℂ) * b))

/-- Order-zero envelope prefactor `𝒜_x^∘` (`(SD.4)` without the `|1 + ε_H|` factor, which is
absorbed into the `O_p(R_p / (n m_x^3))` error in `(1.4)`). -/
noncomputable def fwsdPrefactor0 (n x : ℝ) (ℰ Φ₁ : ℂ → ℂ) : ℝ :=
  2 * Real.exp (-2 * Real.pi * n * x / 3) * ‖ℰ (bX x)‖ *
    Real.exp (Φ₁ (bX x)).re * √(‖bX x‖ / (x * edgeF' (edgeV x)))

/-- Order-zero phase `Θ_x^(0)` of `A_0^∘` at the edge saddle (`upper_transfer.tex`, l.329). -/
noncomputable def fwsdPhase0 (Φ₀ : ℂ → ℂ) (n x : ℝ) (ℰ Φ₁ : ℂ → ℂ) : ℝ :=
  n * (Φ₀ (bX x)).im + sdvWave n x * edgeV x - Real.pi / 2 +
    Complex.arg (fwsdAmplitudeCirc ℰ Φ₁ (bX x))

/-- Amplitude ratio `R_p(x) = (|b_x| / x)^p` (`upper_transfer.tex`, l.307, `fw:e1.5`). -/
noncomputable def fwsdRatio (p : ℕ) (x : ℝ) : ℝ :=
  (‖bX x‖ / x) ^ p

/-- Order-`p` edge integral `\frac{2πn}{3} ∫_{E_+} h_0(b) (b/x)^p H_p^{(1)}(kb) b db`
(`upper_transfer.tex`, l.313, `fw:e1.2a`). -/
noncomputable def fwsdIntegral (p : ℕ) (Φ₀ : ℂ → ℂ) (n x : ℝ) (ℰ Φ₁ Hp : ℂ → ℂ) : ℂ :=
  ((2 * Real.pi * n / 3 : ℝ) : ℂ) *
    ∫ v : ℝ, (ℰ ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + Complex.I / 2) + Φ₁ ((v : ℂ) + Complex.I / 2))) *
      (((v : ℂ) + Complex.I / 2) / (x : ℂ)) ^ p *
      Hp ((sdvWave n x : ℂ) * ((v : ℂ) + Complex.I / 2)) * ((v : ℂ) + Complex.I / 2)

/-- Hypotheses for **Lemma `FW-SD` part (2)** (`upper_transfer.tex`, `fw:SDp`, l.280–327):
* `A_0^∘` analytic, nonvanishing, with `|(log A_0^∘)'| ≤ M₀`, `|(log A_0^∘)''| ≤ M₀'` on `𝒩_δ`;
* order-`p` Hankel asymptotic `H_p(kb) = (2/(πkb))^{1/2} e^{i(kb - pπ/2 - π/4)} (1 + ε_p(kb))`
  on `𝒩_δ`, with `b ↦ 1 + ε_p(kb)` analytic, zero-free, bounded log-derivatives `≤ 1` on `𝒩_δ`,
  and relative error `‖ε_p(kb_x)‖ ≤ C_ε / (n * mX x ^ 3)` (valid for large `n` since `k ≍ nx`
  and `m_x ≤ 1`);
* strip exponential decay of `h_0(b) = ℰ(b) e^{n Φ₀(b) + Φ₁(b)}`;
* edge reflection symmetry of the order-`p` integrand on `E_+`. -/
structure FWSDHypotheses (p : ℕ) (Φ₀ : ℂ → ℂ) (x n δ M₀ M₀' C_ε : ℝ)
    (ℰ Φ₁ Hp εp : ℂ → ℂ) : Prop where
  circ_analytic : AnalyticOnNhd ℂ (fwsdAmplitudeCirc ℰ Φ₁) (edgeStrip δ)
  circ_nonzero : ∀ b ∈ edgeStrip δ, fwsdAmplitudeCirc ℰ Φ₁ b ≠ 0
  circ_logDeriv : ∀ b ∈ edgeStrip δ,
    ‖deriv (fwsdAmplitudeCirc ℰ Φ₁) b / fwsdAmplitudeCirc ℰ Φ₁ b‖ ≤ M₀
  circ_logDeriv2 : ∀ b ∈ edgeStrip δ,
    ‖deriv (fun z => deriv (fwsdAmplitudeCirc ℰ Φ₁) z / fwsdAmplitudeCirc ℰ Φ₁ z) b‖ ≤ M₀'
  hankel_p : ∀ b ∈ edgeStrip δ,
    Hp ((sdvWave n x : ℂ) * b) =
      ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
        Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
        (1 + εp ((sdvWave n x : ℂ) * b))
  eps_analytic : AnalyticOnNhd ℂ (fun b => 1 + εp ((sdvWave n x : ℂ) * b)) (edgeStrip δ)
  eps_nonzero : ∀ b ∈ edgeStrip δ, 1 + εp ((sdvWave n x : ℂ) * b) ≠ 0
  eps_logDeriv : ∀ b ∈ edgeStrip δ,
    ‖deriv (fun z => 1 + εp ((sdvWave n x : ℂ) * z)) b / (1 + εp ((sdvWave n x : ℂ) * b))‖ ≤ 1
  eps_logDeriv2 : ∀ b ∈ edgeStrip δ,
    ‖deriv (fun w => deriv (fun z => 1 + εp ((sdvWave n x : ℂ) * z)) w /
      (1 + εp ((sdvWave n x : ℂ) * w))) b‖ ≤ 1
  eps_strip_bound : ∃ C_s : ℝ, ∀ b ∈ edgeStrip δ, ‖1 + εp ((sdvWave n x : ℂ) * b)‖ ≤ C_s
  eps_saddle_bound : ‖εp ((sdvWave n x : ℂ) * bX x)‖ ≤ C_ε / (n * mX x ^ 3)
  h_decay : ∃ C_h a_h : ℝ, 0 ≤ C_h ∧ 0 < a_h ∧
    ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      ‖ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
          Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C_h * Real.exp (-a_h * |v|)
  edge_symm : ∀ v : ℝ,
    let b : ℂ := (v : ℂ) + Complex.I / 2
    let bm : ℂ := (-v : ℂ) + Complex.I / 2
    let h : ℂ → ℂ := fun z => ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)
    h bm * (bm / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * bm) * bm =
      starRingEnd ℂ (h b * (b / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * b) * b)

/-! ### 2. Log-derivative bounds and `TwoSaddleAmplitude` reduction -/

private lemma logDeriv_mul_three {f₁ f₂ f₃ : ℂ → ℂ} {b : ℂ}
    (hf₁ : AnalyticAt ℂ f₁ b) (hf₂ : AnalyticAt ℂ f₂ b) (hf₃ : AnalyticAt ℂ f₃ b)
    (h1 : f₁ b ≠ 0) (h2 : f₂ b ≠ 0) (h3 : f₃ b ≠ 0) :
    deriv (fun z => f₁ z * f₂ z * f₃ z) b / (f₁ b * f₂ b * f₃ b) =
      deriv f₁ b / f₁ b + deriv f₂ b / f₂ b + deriv f₃ b / f₃ b := by
  have hd1 := hf₁.differentiableAt.hasDerivAt
  have hd2 := hf₂.differentiableAt.hasDerivAt
  have hd3 := hf₃.differentiableAt.hasDerivAt
  have h12 := hd1.fun_mul hd2
  have h123 := h12.fun_mul hd3
  rw [h123.deriv]
  field_simp [h1, h2, h3]

lemma fwsd_logDeriv_bounds {p : ℕ} {Φ₀ : ℂ → ℂ} {x n δ M₀ M₀' C_ε : ℝ}
    {ℰ Φ₁ Hp εp : ℂ → ℂ} (hδ1 : δ ≤ 1 / 4) (hx : xiStar < x)
    (hH : FWSDHypotheses p Φ₀ x n δ M₀ M₀' C_ε ℰ Φ₁ Hp εp) :
    AnalyticOnNhd ℂ (fwsdAmplitude p x n ℰ Φ₁ εp) (edgeStrip δ) ∧
    (∀ b ∈ edgeStrip δ, fwsdAmplitude p x n ℰ Φ₁ εp b ≠ 0) ∧
    (∀ b ∈ edgeStrip δ,
      ‖deriv (fwsdAmplitude p x n ℰ Φ₁ εp) b / fwsdAmplitude p x n ℰ Φ₁ εp b‖ ≤
        M₀ + 4 * (p : ℝ) + 1) ∧
    (∀ b ∈ edgeStrip δ,
      ‖deriv (fun z => deriv (fwsdAmplitude p x n ℰ Φ₁ εp) z / fwsdAmplitude p x n ℰ Φ₁ εp z) b‖ ≤
        M₀' + 16 * (p : ℝ) + 1) := by
  have hx_pos : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
  let pref : ℂ := Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2))
  let f₁ : ℂ → ℂ := fun z => pref * (z / (x : ℂ)) ^ p
  let f₂ : ℂ → ℂ := fwsdAmplitudeCirc ℰ Φ₁
  let f₃ : ℂ → ℂ := fun z => 1 + εp ((sdvWave n x : ℂ) * z)
  have hf₁_an : AnalyticOnNhd ℂ f₁ (edgeStrip δ) := fun b _ =>
    analyticAt_const.mul ((analyticAt_id.div analyticAt_const hx_ne).pow p)
  have hf₁_ne : ∀ b ∈ edgeStrip δ, f₁ b ≠ 0 := fun b hb => by
    have hnorm : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter hδ1 hb
    have hb_ne : b ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    exact mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero p (div_ne_zero hb_ne hx_ne))
  have hf₁_log_at : ∀ z : ℂ, z ≠ 0 → deriv f₁ z / f₁ z = (p : ℂ) / z := fun z hz_ne => by
    rcases p with _ | k
    · have hconst : f₁ = fun _ => 1 := by ext y; simp [f₁, pref]
      rw [hconst]
      simp
    · have hdiv : HasDerivAt (fun y : ℂ => y / (x : ℂ)) (1 / (x : ℂ)) z := by
        simpa using (hasDerivAt_id z).div_const (x : ℂ)
      have hpow : HasDerivAt (fun y : ℂ => (y / (x : ℂ)) ^ (k + 1))
          (((k + 1 : ℕ) : ℂ) * (z / (x : ℂ)) ^ k * (1 / (x : ℂ))) z :=
        (hdiv.pow (k + 1)).congr_deriv (by push_cast; ring)
      have h_f1 : HasDerivAt f₁
          (pref * (((k + 1 : ℕ) : ℂ) * (z / (x : ℂ)) ^ k * (1 / (x : ℂ)))) z := by
        simpa [f₁] using hpow.const_mul pref
      have hpref_ne : pref ≠ 0 := Complex.exp_ne_zero _
      change deriv f₁ z / f₁ z = ((k + 1 : ℕ) : ℂ) / z
      rw [h_f1.deriv]
      dsimp [f₁]
      rw [pow_succ]
      have hz_x : z / (x : ℂ) ≠ 0 := div_ne_zero hz_ne hx_ne
      field_simp [hz_ne, hx_ne, hpref_ne, pow_ne_zero k hz_x]
  have hf₁_log : ∀ b ∈ edgeStrip δ, deriv f₁ b / f₁ b = (p : ℂ) / b := fun b hb => by
    have hnorm : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter hδ1 hb
    exact hf₁_log_at b (norm_ne_zero_iff.mp (by linarith))
  have hf₁_log_ev : ∀ b ∈ edgeStrip δ,
      (fun z => deriv f₁ z / f₁ z) =ᶠ[𝓝 b] (fun z => (p : ℂ) / z) := fun b hb => by
    have him : 0 < b.im := mem_edgeStrip_im_pos hδ1 hb
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    refine Filter.eventually_of_mem (hopen.mem_nhds him) fun z hz => ?_
    exact hf₁_log_at z (fun h => by simp [h] at hz)
  have hA_eq_fun : (fun z => f₁ z * f₂ z * f₃ z) = fwsdAmplitude p x n ℰ Φ₁ εp := rfl
  have hA_an : AnalyticOnNhd ℂ (fwsdAmplitude p x n ℰ Φ₁ εp) (edgeStrip δ) := fun b hb =>
    ((hf₁_an b hb).mul (hH.circ_analytic b hb)).mul (hH.eps_analytic b hb)
  have hA_ne : ∀ b ∈ edgeStrip δ, fwsdAmplitude p x n ℰ Φ₁ εp b ≠ 0 := fun b hb =>
    mul_ne_zero (mul_ne_zero (hf₁_ne b hb) (hH.circ_nonzero b hb)) (hH.eps_nonzero b hb)
  have hlog_bd : ∀ b ∈ edgeStrip δ,
      ‖deriv (fwsdAmplitude p x n ℰ Φ₁ εp) b / fwsdAmplitude p x n ℰ Φ₁ εp b‖ ≤
        M₀ + 4 * (p : ℝ) + 1 := fun b hb => by
    have hsum := logDeriv_mul_three (hf₁_an b hb) (hH.circ_analytic b hb) (hH.eps_analytic b hb)
      (hf₁_ne b hb) (hH.circ_nonzero b hb) (hH.eps_nonzero b hb)
    rw [hA_eq_fun] at hsum
    have h_den : f₁ b * f₂ b * f₃ b = fwsdAmplitude p x n ℰ Φ₁ εp b := rfl
    rw [h_den] at hsum
    rw [hsum, hf₁_log b hb]
    have hnorm : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter hδ1 hb
    have h1 : ‖(p : ℂ) / b‖ ≤ 4 * (p : ℝ) := by
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
      calc (p : ℝ) = (p : ℝ) * 1 := (mul_one _).symm
        _ ≤ (p : ℝ) * (4 * ‖b‖) := mul_le_mul_of_nonneg_left (by linarith) hp0
        _ = 4 * (p : ℝ) * ‖b‖ := by ring
    have htri : ‖(p : ℂ) / b + deriv f₂ b / f₂ b + deriv f₃ b / f₃ b‖ ≤
        ‖(p : ℂ) / b‖ + ‖deriv f₂ b / f₂ b‖ + ‖deriv f₃ b / f₃ b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    calc ‖(p : ℂ) / b + deriv f₂ b / f₂ b + deriv f₃ b / f₃ b‖
        ≤ ‖(p : ℂ) / b‖ + ‖deriv f₂ b / f₂ b‖ + ‖deriv f₃ b / f₃ b‖ := htri
      _ ≤ 4 * (p : ℝ) + M₀ + 1 := add_le_add (add_le_add h1 (hH.circ_logDeriv b hb)) (hH.eps_logDeriv b hb)
      _ = M₀ + 4 * (p : ℝ) + 1 := by ring
  have hlog2_bd : ∀ b ∈ edgeStrip δ,
      ‖deriv (fun z => deriv (fwsdAmplitude p x n ℰ Φ₁ εp) z / fwsdAmplitude p x n ℰ Φ₁ εp z) b‖ ≤
        M₀' + 16 * (p : ℝ) + 1 := fun b hb => by
    let L₁ : ℂ → ℂ := fun z => (p : ℂ) / z
    let L₂ : ℂ → ℂ := fun z => deriv f₂ z / f₂ z
    let L₃ : ℂ → ℂ := fun z => deriv f₃ z / f₃ z
    have hf₂_an_ev : ∀ᶠ z in 𝓝 b, f₂ z ≠ 0 ∧ AnalyticAt ℂ f₂ z :=
      ((hH.circ_analytic b hb).continuousAt.eventually_ne (hH.circ_nonzero b hb)).and
        (isOpen_analyticAt ℂ f₂ |>.mem_nhds (hH.circ_analytic b hb))
    have hf₃_an_ev : ∀ᶠ z in 𝓝 b, f₃ z ≠ 0 ∧ AnalyticAt ℂ f₃ z :=
      ((hH.eps_analytic b hb).continuousAt.eventually_ne (hH.eps_nonzero b hb)).and
        (isOpen_analyticAt ℂ f₃ |>.mem_nhds (hH.eps_analytic b hb))
    have him : 0 < b.im := mem_edgeStrip_im_pos hδ1 hb
    have h_f1_ev : ∀ᶠ z in 𝓝 b, f₁ z ≠ 0 ∧ AnalyticAt ℂ f₁ z ∧ deriv f₁ z / f₁ z = L₁ z := by
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds him, hf₁_log_ev b hb] with z hz hlog
      have hz_ne : z ≠ 0 := fun h => by simp [h] at hz
      have hne : f₁ z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero p (div_ne_zero hz_ne hx_ne))
      have han : AnalyticAt ℂ f₁ z :=
        analyticAt_const.mul ((analyticAt_id.div analyticAt_const hx_ne).pow p)
      exact ⟨hne, han, hlog⟩
    have hsum_ev : (fun z => deriv (fwsdAmplitude p x n ℰ Φ₁ εp) z / fwsdAmplitude p x n ℰ Φ₁ εp z) =ᶠ[𝓝 b]
        fun z => L₁ z + L₂ z + L₃ z := by
      filter_upwards [h_f1_ev, hf₂_an_ev, hf₃_an_ev] with z ⟨h1, han1, hl1⟩ ⟨h2, han2⟩ ⟨h3, han3⟩
      have hs := logDeriv_mul_three han1 han2 han3 h1 h2 h3
      rw [hA_eq_fun] at hs
      have h_den : f₁ z * f₂ z * f₃ z = fwsdAmplitude p x n ℰ Φ₁ εp z := rfl
      rw [h_den] at hs
      rw [hs, hl1]
    have hnorm : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter hδ1 hb
    have hb_ne : b ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    have hL₁_d : HasDerivAt L₁ (-(p : ℂ) / b ^ 2) b := by
      have hinv := hasDerivAt_inv hb_ne
      simpa [L₁, div_eq_mul_inv, neg_div] using hinv.const_mul (p : ℂ)
    have hL₂_d : DifferentiableAt ℂ L₂ b := by
      have han2 : AnalyticAt ℂ f₂ b := hH.circ_analytic b hb
      exact (han2.deriv.div han2 (hH.circ_nonzero b hb)).differentiableAt
    have hL₃_d : DifferentiableAt ℂ L₃ b := by
      have han3 : AnalyticAt ℂ f₃ b := hH.eps_analytic b hb
      exact (han3.deriv.div han3 (hH.eps_nonzero b hb)).differentiableAt
    have hsum_d : HasDerivAt (fun z => L₁ z + L₂ z + L₃ z) (-(p : ℂ) / b ^ 2 + deriv L₂ b + deriv L₃ b) b :=
      (hL₁_d.add hL₂_d.hasDerivAt).add hL₃_d.hasDerivAt
    rw [hsum_ev.deriv_eq, hsum_d.deriv]
    have h1 : ‖-(p : ℂ) / b ^ 2‖ ≤ 16 * (p : ℝ) := by
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow,
        div_le_iff₀ (pow_pos (by linarith : 0 < ‖b‖) 2)]
      have hsq : (1 : ℝ) ≤ 16 * ‖b‖ ^ 2 := by nlinarith
      calc (p : ℝ) = (p : ℝ) * 1 := (mul_one _).symm
        _ ≤ (p : ℝ) * (16 * ‖b‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hp0
        _ = 16 * (p : ℝ) * ‖b‖ ^ 2 := by ring
    have htri : ‖-(p : ℂ) / b ^ 2 + deriv L₂ b + deriv L₃ b‖ ≤
        ‖-(p : ℂ) / b ^ 2‖ + ‖deriv L₂ b‖ + ‖deriv L₃ b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    calc ‖-(p : ℂ) / b ^ 2 + deriv L₂ b + deriv L₃ b‖
        ≤ ‖-(p : ℂ) / b ^ 2‖ + ‖deriv L₂ b‖ + ‖deriv L₃ b‖ := htri
      _ ≤ 16 * (p : ℝ) + M₀' + 1 :=
          add_le_add (add_le_add h1 (hH.circ_logDeriv2 b hb)) (hH.eps_logDeriv2 b hb)
      _ = M₀' + 16 * (p : ℝ) + 1 := by ring
  exact ⟨hA_an, hA_ne, hlog_bd, hlog2_bd⟩

lemma fwsd_integrand_eq {p : ℕ} {Φ₀ : ℂ → ℂ} {x n δ M₀ M₀' C_ε : ℝ} {ℰ Φ₁ Hp εp : ℂ → ℂ}
    (hx : xiStar < x) (hn : 0 < n) (hδ1 : δ ≤ 1 / 4)
    (hH : FWSDHypotheses p Φ₀ x n δ M₀ M₀' C_ε ℰ Φ₁ Hp εp)
    {b : ℂ} (hb : b ∈ edgeStrip δ) :
    (ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) * (b / (x : ℂ)) ^ p *
        Hp ((sdvWave n x : ℂ) * b) * b =
      (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
        (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          fwsdAmplitude p x n ℰ Φ₁ εp b * Complex.exp ((n : ℂ) * phiX Φ₀ x b)) := by
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave; positivity [Real.pi_pos]
  have him_pos : 0 < b.im := mem_edgeStrip_im_pos hδ1 hb
  rw [hH.hankel_p b hb]
  have hmul : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) * b =
      (√(2 / (Real.pi * sdvWave n x)) : ℂ) * b ^ (1 / 2 : ℂ) :=
    hankelZeroPrefactor_mul (sdvWave n x) hk_pos him_pos
  have hexp_phase :
      Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) =
        (Real.exp (-(sdvWave n x) / 2) : ℝ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) *
          Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold sdvWave
    push_cast
    have hsplit : (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (b - Complex.I / 2)) =
        (n : ℂ) * (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * b) -
          ((n : ℂ) * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) / 2) * (Complex.I * Complex.I) := by
      ring
    rw [hsplit, Complex.I_mul_I]
    ring
  have hexp_n : Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
        Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2))) =
      Complex.exp (Φ₁ b) * Complex.exp ((n : ℂ) * phiX Φ₀ x b) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; unfold phiX; ring
  calc (ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) * (b / (x : ℂ)) ^ p *
        (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
          (1 + εp ((sdvWave n x : ℂ) * b))) * b
      = ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) * (b / (x : ℂ)) ^ p *
          (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) * b) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
          (1 + εp ((sdvWave n x : ℂ) * b)) := by ring
    _ = ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) * (b / (x : ℂ)) ^ p *
          ((√(2 / (Real.pi * sdvWave n x)) : ℂ) * b ^ (1 / 2 : ℂ)) *
          ((Real.exp (-(sdvWave n x) / 2) : ℝ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) *
            Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) * (b - Complex.I / 2)))) *
          (1 + εp ((sdvWave n x : ℂ) * b)) := by rw [hmul, hexp_phase]
    _ = (√(2 / (Real.pi * sdvWave n x)) : ℂ) * (Real.exp (-(sdvWave n x) / 2) : ℝ) *
          (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            (Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (b / (x : ℂ)) ^ p *
              (ℰ b * b ^ (1 / 2 : ℂ) * (1 + εp ((sdvWave n x : ℂ) * b)) *
                (Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b) *
                  Complex.exp ((n : ℂ) * (Complex.I * (4 * Real.pi / 3) * (x : ℂ) *
                    (b - Complex.I / 2))))))) := by ring
    _ = (√(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2) : ℝ) *
          (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
            fwsdAmplitude p x n ℰ Φ₁ εp b * Complex.exp ((n : ℂ) * phiX Φ₀ x b)) := by
          rw [hexp_n]
          unfold fwsdAmplitude fwsdAmplitudeCirc
          push_cast
          ring

lemma twoSaddleAmplitude_of_fwsd {p : ℕ} {Φ₀ : ℂ → ℂ} {x n δ M₀ M₀' C_ε : ℝ}
    {ℰ Φ₁ Hp εp : ℂ → ℂ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hx : xiStar < x) (hn : 0 < n)
    (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) (hH : FWSDHypotheses p Φ₀ x n δ M₀ M₀' C_ε ℰ Φ₁ Hp εp) :
    TwoSaddleAmplitude Φ₀ x n δ (M₀ + 4 * (p : ℝ) + 1) (M₀' + 16 * (p : ℝ) + 1)
      (fwsdAmplitude p x n ℰ Φ₁ εp) := by
  let A := fwsdAmplitude p x n ℰ Φ₁ εp
  obtain ⟨hA_an, hA_ne, hlog, hlog2⟩ := fwsd_logDeriv_bounds hδ1 hx hH
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave; positivity [Real.pi_pos]
  let c₀ : ℝ := √(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2)
  have hc₀_pos : 0 < c₀ := by positivity
  obtain ⟨C_h, a_h, hCh_nn, hah_pos, hh_dec⟩ := hH.h_decay
  obtain ⟨C_s, hCs⟩ := hH.eps_strip_bound
  have hCs_nn : 0 ≤ C_s := (norm_nonneg _).trans (hCs (bX x) (bX_mem_edgeStrip hδ0.le x))
  have hx_pos : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
  have hstrip_point_bd : ∀ v t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      ‖A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        (c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_s * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
          ((1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖) ^ (p + 1) / x ^ p)) *
          Real.exp (-a_h * |v|) := by
    intro v t ht1 ht2
    have hb : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
      show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
      have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [him]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hid := fwsd_integrand_eq hx hn hδ1 hH hb
    have hA_eq : A ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)) =
        ((c₀ : ℂ)⁻¹ * Complex.exp (Complex.I * (Real.pi / 4 : ℂ))) *
          ((ℰ ((v : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + (t : ℂ) * Complex.I) +
                Φ₁ ((v : ℂ) + (t : ℂ) * Complex.I))) *
            (((v : ℂ) + (t : ℂ) * Complex.I) / (x : ℂ)) ^ p *
            Hp ((sdvWave n x : ℂ) * ((v : ℂ) + (t : ℂ) * Complex.I)) *
            ((v : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [hid]
      have h_pref_unit : Complex.exp (Complex.I * (Real.pi / 4 : ℂ)) *
          Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) = 1 := by
        rw [← Complex.exp_add]; simp
      have hc₀_ne : (c₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc₀_pos.ne'
      calc A ((v : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))
          = 1 * (A ((v : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))) := (one_mul _).symm
        _ = ((c₀ : ℂ)⁻¹ * (c₀ : ℂ)) *
              ((Complex.exp (Complex.I * (Real.pi / 4 : ℂ)) *
                Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) *
              (A ((v : ℂ) + (t : ℂ) * Complex.I) *
                Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)))) := by
              rw [inv_mul_cancel₀ hc₀_ne, h_pref_unit]; ring
        _ = _ := by ring
    have he_unit : ‖Complex.exp (Complex.I * (Real.pi / 4 : ℂ))‖ = 1 := by
      rw [show Complex.I * (Real.pi / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    let z : ℂ := (v : ℂ) + (t : ℂ) * Complex.I
    have hH_bd : ‖(z / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * z) * z‖ ≤
        √(2 / (Real.pi * sdvWave n x)) * C_s * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
          ((1 + ‖z‖) ^ (p + 1) / x ^ p) := by
      rw [hH.hankel_p _ hb]
      have him_pos : 0 < z.im := mem_edgeStrip_im_pos hδ1 hb
      have hmul : ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * z))) ^ (1 / 2 : ℂ) * z =
          (√(2 / (Real.pi * sdvWave n x)) : ℂ) * z ^ (1 / 2 : ℂ) :=
        hankelZeroPrefactor_mul (sdvWave n x) hk_pos him_pos
      have h_eq : (z / (x : ℂ)) ^ p *
            (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * z))) ^ (1 / 2 : ℂ) *
              Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
                Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
              (1 + εp ((sdvWave n x : ℂ) * z))) * z =
          (√(2 / (Real.pi * sdvWave n x)) : ℂ) * (z / (x : ℂ)) ^ p * z ^ (1 / 2 : ℂ) *
            Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
              Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
            (1 + εp ((sdvWave n x : ℂ) * z)) := by
        calc (z / (x : ℂ)) ^ p *
              (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * z))) ^ (1 / 2 : ℂ) *
                Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
                  Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
                (1 + εp ((sdvWave n x : ℂ) * z))) * z
            = (z / (x : ℂ)) ^ p *
                (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * z))) ^ (1 / 2 : ℂ) * z) *
                Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
                  Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
                (1 + εp ((sdvWave n x : ℂ) * z)) := by ring
          _ = _ := by rw [hmul]; ring
      rw [h_eq, norm_mul, norm_mul, norm_mul, norm_mul]
      have h_sqrt_norm : ‖(√(2 / (Real.pi * sdvWave n x)) : ℂ)‖ =
          √(2 / (Real.pi * sdvWave n x)) := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      have h_z_half : ‖z ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖z‖ := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
          ← Real.sqrt_eq_rpow]
        rcases le_total ‖z‖ 1 with hle | hge
        · exact (Real.sqrt_le_one.mpr hle).trans (by linarith [norm_nonneg z])
        · have h1 : √‖z‖ ≤ ‖z‖ := by
            calc √‖z‖ ≤ √(‖z‖ ^ 2) := by gcongr; exact le_self_pow₀ hge (by decide)
              _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)
          linarith
      have h_zp : ‖(z / (x : ℂ)) ^ p‖ ≤ (1 + ‖z‖) ^ p / x ^ p := by
        rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hx_pos.le, div_pow]
        gcongr
        linarith
      have h_exp_norm : ‖Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
            Real.pi * (p : ℂ) / 2 - Real.pi / 4))‖ ≤
          Real.exp (-(sdvWave n x) * (1 / 2 - δ)) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        have hre : (Complex.I * ((sdvWave n x : ℂ) * z -
            Real.pi * (p : ℂ) / 2 - Real.pi / 4)).re = -(sdvWave n x) * t := by
          dsimp [z]; simp
        rw [hre]; nlinarith
      rw [h_sqrt_norm]
      calc √(2 / (Real.pi * sdvWave n x)) * ‖(z / (x : ℂ)) ^ p‖ * ‖z ^ (1 / 2 : ℂ)‖ *
            ‖Complex.exp (Complex.I * ((sdvWave n x : ℂ) * z -
              Real.pi * (p : ℂ) / 2 - Real.pi / 4))‖ *
            ‖1 + εp ((sdvWave n x : ℂ) * z)‖
          ≤ √(2 / (Real.pi * sdvWave n x)) * ((1 + ‖z‖) ^ p / x ^ p) * (1 + ‖z‖) *
              Real.exp (-(sdvWave n x) * (1 / 2 - δ)) * C_s := by
            gcongr
            exact hCs _ hb
        _ = √(2 / (Real.pi * sdvWave n x)) * C_s * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
              ((1 + ‖z‖) ^ (p + 1) / x ^ p) := by
            rw [pow_succ]; ring
    have hA_eq' : A z * Complex.exp ((n : ℂ) * phiX Φ₀ x z) =
        ((c₀ : ℂ)⁻¹ * Complex.exp (Complex.I * (Real.pi / 4 : ℂ))) *
          ((ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)) *
            ((z / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * z) * z)) := by
      dsimp [z]; rw [hA_eq]; ring
    rw [hA_eq', norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hc₀_pos.le, he_unit, mul_one, norm_mul]
    calc c₀⁻¹ * (‖ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)‖ *
          ‖(z / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * z) * z‖)
        ≤ c₀⁻¹ * ((C_h * Real.exp (-a_h * |v|)) *
            (√(2 / (Real.pi * sdvWave n x)) * C_s * Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
              ((1 + ‖z‖) ^ (p + 1) / x ^ p))) := by
          gcongr
          exact hh_dec v t ht1 ht2
      _ = (c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_s *
            Real.exp (-(sdvWave n x) * (1 / 2 - δ)) *
            ((1 + ‖z‖) ^ (p + 1) / x ^ p)) * Real.exp (-a_h * |v|) := by ring
  let K : ℝ := c₀⁻¹ * C_h * √(2 / (Real.pi * sdvWave n x)) * C_s *
    Real.exp (-(sdvWave n x) * (1 / 2 - δ)) / x ^ p
  have hK_nn : 0 ≤ K := by positivity
  have h_pow_int : ∀ m : ℕ, Integrable (fun v : ℝ => (1 + |v|) ^ m * Real.exp (-a_h * |v|)) volume := by
    intro m
    have h_half : 0 < a_h / 2 := half_pos hah_pos
    have h_exp : Integrable (fun v : ℝ => Real.exp (-(a_h / 2) * |v|)) volume := by
      have h1 : IntegrableOn (fun v : ℝ => Real.exp (-(a_h / 2) * |v|)) (Iic 0) := by
        refine (integrableOn_exp_mul_Iic h_half 0).congr_fun (fun v hv => ?_) measurableSet_Iic
        rw [mem_Iic] at hv
        rw [abs_of_nonpos hv, show -(a_h / 2) * -v = (a_h / 2) * v by ring]
      have h2 : IntegrableOn (fun v : ℝ => Real.exp (-(a_h / 2) * |v|)) (Ioi 0) := by
        refine (integrableOn_exp_mul_Ioi (by linarith : -(a_h / 2) < 0) 0).congr_fun
          (fun v hv => ?_) measurableSet_Ioi
        rw [mem_Ioi] at hv
        rw [abs_of_pos hv]
      have huniv : (univ : Set ℝ) = Iic 0 ∪ Ioi 0 := by ext v; simp
      rw [← integrableOn_univ, huniv]
      exact h1.union h2
    let M_cap : ℝ := max (m : ℝ) 1
    let D : ℝ := max 1 (M_cap / (a_h / 2))
    have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hm1_pos : (0 : ℝ) < M_cap := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h_dom : ∀ v : ℝ, (1 + |v|) ^ m * Real.exp (-a_h * |v|) ≤
        D ^ m * Real.exp (-(a_h / 2) * |v|) := fun v => by
      have hv0 : 0 ≤ |v| := abs_nonneg v
      have h_lin : 1 + |v| ≤ D * Real.exp (((a_h / 2) / M_cap) * |v|) := by
        have h1 : 1 + ((a_h / 2) / M_cap) * |v| ≤ Real.exp (((a_h / 2) / M_cap) * |v|) := by
          linarith [Real.add_one_le_exp (((a_h / 2) / M_cap) * |v|)]
        have h1D : 1 ≤ D := le_max_left _ _
        have hvD : |v| ≤ D * (((a_h / 2) / M_cap) * |v|) := by
          have hle : M_cap / (a_h / 2) ≤ D := le_max_right _ _
          calc |v| = (M_cap / (a_h / 2)) * (((a_h / 2) / M_cap) * |v|) := by
                  field_simp [hm1_pos.ne', h_half.ne']
            _ ≤ D * (((a_h / 2) / M_cap) * |v|) := by gcongr
        calc 1 + |v| ≤ D * 1 + D * (((a_h / 2) / M_cap) * |v|) := by linarith
          _ = D * (1 + ((a_h / 2) / M_cap) * |v|) := by ring
          _ ≤ D * Real.exp (((a_h / 2) / M_cap) * |v|) := by gcongr
      have h_pow : (1 + |v|) ^ m ≤ D ^ m * Real.exp ((a_h / 2) * |v|) := by
        have hp := pow_le_pow_left₀ (by positivity) h_lin m
        rw [mul_pow, ← Real.exp_nat_mul] at hp
        have hexp_le : Real.exp ((m : ℝ) * (((a_h / 2) / M_cap) * |v|)) ≤
            Real.exp ((a_h / 2) * |v|) := by
          refine Real.exp_le_exp.mpr ?_
          have hm_le : (m : ℝ) ≤ M_cap := le_max_left _ _
          calc (m : ℝ) * (((a_h / 2) / M_cap) * |v|)
              = ((m : ℝ) / M_cap) * ((a_h / 2) * |v|) := by ring
            _ ≤ 1 * ((a_h / 2) * |v|) := by
                gcongr
                exact (div_le_one hm1_pos).mpr hm_le
            _ = (a_h / 2) * |v| := one_mul _
        exact hp.trans (mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hD_pos.le m))
      calc (1 + |v|) ^ m * Real.exp (-a_h * |v|)
          ≤ (D ^ m * Real.exp ((a_h / 2) * |v|)) * Real.exp (-a_h * |v|) := by gcongr
        _ = D ^ m * (Real.exp ((a_h / 2) * |v|) * Real.exp (-a_h * |v|)) := by ring
        _ = D ^ m * Real.exp (-(a_h / 2) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    refine (h_exp.const_mul (D ^ m)).mono'
      ((by fun_prop : Continuous fun v : ℝ => (1 + |v|) ^ m * Real.exp (-a_h * |v|)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact h_dom v
  have h_horiz_int : ∀ t : ℝ, 1 / 2 - δ ≤ t → t ≤ 1 / 2 →
      Integrable (fun v : ℝ => A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))) volume := by
    intro t ht1 ht2
    have hcont : Continuous fun v : ℝ => A ((v : ℂ) + (t : ℂ) * Complex.I) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I)) := by
      have hf : Continuous fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I := by fun_prop
      refine Continuous.mul ?_ (Complex.continuous_exp.comp (continuous_const.mul ?_))
      · rw [continuous_iff_continuousAt]
        intro v
        have hmem : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
          show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [him]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact ContinuousAt.comp (g := fun z : ℂ => A z)
          (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) (x := v)
          (hA_an _ hmem).continuousAt hf.continuousAt
      · rw [continuous_iff_continuousAt]
        intro v
        have hmem : (v : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
          show |((v : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
          have him : ((v : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [him]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact ContinuousAt.comp (g := fun z : ℂ => phiX Φ₀ x z)
          (f := fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) (x := v)
          ((phiX_analyticOnNhd hΦ x) _ hmem).continuousAt hf.continuousAt
    have hint_dom : Integrable (fun v : ℝ =>
        (K * (1 + |t|) ^ (p + 1)) * ((1 + |v|) ^ (p + 1) * Real.exp (-a_h * |v|))) volume :=
      (h_pow_int (p + 1)).const_mul (K * (1 + |t|) ^ (p + 1))
    refine hint_dom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    have hpt := hstrip_point_bd v t ht1 ht2
    have h_norm_v : 1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + |t|) * (1 + |v|) := by
      have h1 : ‖(v : ℂ) + (t : ℂ) * Complex.I‖ ≤ |v| + |t| := by
        calc ‖(v : ℂ) + (t : ℂ) * Complex.I‖
            ≤ ‖(v : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |v| + |t| := by simp [Complex.norm_real]
      have h2 : 0 ≤ |t| * |v| := mul_nonneg (abs_nonneg t) (abs_nonneg v)
      nlinarith
    have h_pow_v : (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖) ^ (p + 1) ≤
        (1 + |t|) ^ (p + 1) * (1 + |v|) ^ (p + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h_norm_v (p + 1)
    calc ‖A ((v : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ (K * (1 + ‖(v : ℂ) + (t : ℂ) * Complex.I‖) ^ (p + 1)) * Real.exp (-a_h * |v|) := by
            refine hpt.trans_eq ?_; dsimp [K]; ring
      _ ≤ (K * ((1 + |t|) ^ (p + 1) * (1 + |v|) ^ (p + 1))) * Real.exp (-a_h * |v|) := by
          gcongr
      _ = (K * (1 + |t|) ^ (p + 1)) * ((1 + |v|) ^ (p + 1) * Real.exp (-a_h * |v|)) := by ring
  have h_edge_int : Integrable (fun v : ℝ => A ((v : ℂ) + Complex.I / 2) *
      Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) volume := by
    have h12 : 1 / 2 - δ ≤ (1 / 2 : ℝ) := by linarith [hδ0]
    have hpt : (fun v : ℝ => A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) =
        fun v : ℝ => A ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)) := by
      ext v
      have hz : (v : ℂ) + Complex.I / 2 = (v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hz]
    rw [hpt]
    exact h_horiz_int (1 / 2) h12 le_rfl
  have h_lower_int : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Integrable (fun v : ℝ => A ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)) *
        Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 - u₀ : ℝ) : ℂ)))) volume := by
    intro u₀ hu₀_pos hu₀_le
    simpa [mul_comm Complex.I _] using h_horiz_int (1 / 2 - u₀) (by linarith) (by linarith)
  have h_vert_bd : ∀ s : ℝ, |s| = 1 → ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
    intro s hs u₀ hu₀_pos hu₀_le
    have hbound : ∀ᶠ R : ℝ in atTop,
        ‖∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
          A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          (K * u₀) * ((2 + R) ^ (p + 1) * Real.exp (-a_h * R)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      have ha_le : (1 / 2 - u₀ : ℝ) ≤ 1 / 2 := by linarith
      have hm_le : ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ), K * (2 + R) ^ (p + 1) * Real.exp (-a_h * R) := by
        refine intervalIntegral.integral_mono_on ha_le ?_ intervalIntegrable_const ?_
        · have hcont_seg : ContinuousOn (fun t : ℝ => A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
              (Icc (1 / 2 - u₀) (1 / 2 : ℝ)) := by
            have hf : Continuous fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I := by fun_prop
            refine ContinuousOn.mul ?_ (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_))
            · intro t ht
              have ht' : t ∈ Icc (1 / 2 - u₀) (1 / 2 : ℝ) := ht
              have hmem : ((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
                show |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
                have him : (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
                rw [him]
                exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2, hδ0]⟩
              exact ContinuousAt.comp_continuousWithinAt (g := fun z : ℂ => A z)
                (f := fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
                (s := Icc (1 / 2 - u₀) (1 / 2 : ℝ)) (x := t)
                (hA_an _ hmem).continuousAt hf.continuousWithinAt
            · intro t ht
              have ht' : t ∈ Icc (1 / 2 - u₀) (1 / 2 : ℝ) := ht
              have hmem : ((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
                show |(((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im - 1 / 2| ≤ δ
                have him : (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
                rw [him]
                exact abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2, hδ0]⟩
              exact ContinuousAt.comp_continuousWithinAt (g := fun z : ℂ => phiX Φ₀ x z)
                (f := fun y : ℝ => ((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
                (s := Icc (1 / 2 - u₀) (1 / 2 : ℝ)) (x := t)
                ((phiX_analyticOnNhd hΦ x) _ hmem).continuousAt hf.continuousWithinAt
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le ha_le]
          exact hcont_seg.norm
        · intro t ht
          have ht1 : 1 / 2 - δ ≤ t := by linarith [ht.1]
          have ht2 : t ≤ 1 / 2 := ht.2
          have hpt := hstrip_point_bd (s * R) t ht1 ht2
          have habs : |s * R| = R := by rw [abs_mul, hs, one_mul, abs_of_nonneg hR]
          have h_norm_z : ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + R := by
            have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            calc ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖
                ≤ ‖((s * R : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
              _ = |s * R| + |t| := by simp [Complex.norm_real]
              _ ≤ R + 1 := by rw [habs]; linarith
              _ = 1 + R := by ring
          have h_pow_z : (1 + ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) ^ (p + 1) ≤ (2 + R) ^ (p + 1) := by
            exact pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)
          calc ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
                Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
              ≤ (K * (1 + ‖((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I‖) ^ (p + 1)) * Real.exp (-a_h * |s * R|) := by
                  refine hpt.trans_eq ?_; dsimp [K]; ring
            _ ≤ K * (2 + R) ^ (p + 1) * Real.exp (-a_h * R) := by rw [habs]; gcongr
      have hn_int : ‖∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
          ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
            ‖A (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * phiX Φ₀ x (((s * R : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ :=
        intervalIntegral.norm_integral_le_integral_norm ha_le
      have hc_eq : ∫ _t in (1 / 2 - u₀)..(1 / 2 : ℝ), K * (2 + R) ^ (p + 1) * Real.exp (-a_h * R) =
          (K * u₀) * ((2 + R) ^ (p + 1) * Real.exp (-a_h * R)) := by
        simp only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul]
        ring
      exact hn_int.trans (hm_le.trans_eq hc_eq)
    have ht_zero : Tendsto (fun R : ℝ => (K * u₀) * ((2 + R) ^ (p + 1) * Real.exp (-a_h * R)))
        atTop (𝓝 0) := by
      let m : ℕ := p + 1
      let D : ℝ := max 2 (((m : ℝ) / (a_h / 2)))
      have hD_pos : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hm_pos : (0 : ℝ) < m := by positivity
      have h_half_pos : 0 < a_h / 2 := half_pos hah_pos
      have hsub : Tendsto (fun R : ℝ => D ^ m * (2 / (a_h * R))) atTop (𝓝 0) := by
        have hinv : Tendsto (fun R : ℝ => (D ^ m * 2 / a_h) / R) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        refine hinv.congr' (Filter.Eventually.of_forall fun R => by ring)
      have hsq : Tendsto (fun R : ℝ => (2 + R) ^ m * Real.exp (-a_h * R)) atTop (𝓝 0) := by
        refine squeeze_zero' ?_ ?_ hsub
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
          exact mul_nonneg (pow_nonneg (by linarith) m) (Real.exp_pos _).le
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
          have h_lin : 2 + R ≤ D * Real.exp (((a_h / 2) / m) * R) := by
            have h1 : 1 + ((a_h / 2) / m) * R ≤ Real.exp (((a_h / 2) / m) * R) := by
              linarith [Real.add_one_le_exp (((a_h / 2) / m) * R)]
            have h2D : (2 : ℝ) ≤ D := le_max_left _ _
            have hRD : R ≤ D * (((a_h / 2) / m) * R) := by
              have hle : (m : ℝ) / (a_h / 2) ≤ D := le_max_right _ _
              calc R = ((m : ℝ) / (a_h / 2)) * (((a_h / 2) / m) * R) := by
                      field_simp [hm_pos.ne', h_half_pos.ne']
                _ ≤ D * (((a_h / 2) / m) * R) := by gcongr
            calc 2 + R ≤ D * 1 + D * (((a_h / 2) / m) * R) := by linarith
              _ = D * (1 + ((a_h / 2) / m) * R) := by ring
              _ ≤ D * Real.exp (((a_h / 2) / m) * R) := by gcongr
          have h_pow : (2 + R) ^ m ≤ D ^ m * Real.exp ((a_h / 2) * R) := by
            have hp := pow_le_pow_left₀ (by linarith) h_lin m
            rw [mul_pow, ← Real.exp_nat_mul] at hp
            have harg : (m : ℝ) * (((a_h / 2) / m) * R) = (a_h / 2) * R := by
              field_simp [hm_pos.ne']
            rwa [harg] at hp
          have h2 : Real.exp (-(a_h / 2) * R) ≤ 2 / (a_h * R) := by
            have h1 : (a_h / 2) * R ≤ Real.exp ((a_h / 2) * R) := by
              linarith [Real.add_one_le_exp ((a_h / 2) * R)]
            calc Real.exp (-(a_h / 2) * R)
                = (Real.exp ((a_h / 2) * R))⁻¹ := by
                    rw [show -(a_h / 2) * R = -((a_h / 2) * R) by ring, Real.exp_neg]
              _ ≤ ((a_h / 2) * R)⁻¹ := inv_anti₀ (by positivity) h1
              _ = 2 / (a_h * R) := by field_simp [hah_pos.ne', hR.ne']
          calc (2 + R) ^ m * Real.exp (-a_h * R)
              ≤ (D ^ m * Real.exp ((a_h / 2) * R)) * Real.exp (-a_h * R) := by gcongr
            _ = D ^ m * Real.exp (-(a_h / 2) * R) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
            _ ≤ D ^ m * (2 / (a_h * R)) := by gcongr
      simpa using hsq.const_mul (K * u₀)
    exact squeeze_zero_norm' hbound ht_zero
  have h_vert_R : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa using h_vert_bd 1 abs_one u₀ hu₀_pos hu₀_le
  have h_vert_L : ∀ u₀ : ℝ, 0 < u₀ → u₀ ≤ δ →
      Tendsto (fun R : ℝ => ∫ t in (1 / 2 - u₀)..(1 / 2 : ℝ),
        A ((-R : ℂ) + (t : ℂ) * Complex.I) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((-R : ℂ) + (t : ℂ) * Complex.I)))
        atTop (𝓝 0) := fun u₀ hu₀_pos hu₀_le => by
    simpa [Complex.ofReal_neg] using h_vert_bd (-1) (by norm_num) u₀ hu₀_pos hu₀_le
  have h_symm : ∀ v : ℝ,
      Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A ((-v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((-v : ℂ) + Complex.I / 2)) =
        starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) * A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
    intro v
    have hb : (v : ℂ) + Complex.I / 2 ∈ edgeStrip δ := mem_edgeStrip_edge hδ0.le v
    have hbm : (-v : ℂ) + Complex.I / 2 ∈ edgeStrip δ := by
      simpa [Complex.ofReal_neg] using mem_edgeStrip_edge hδ0.le (-v)
    have h1 := fwsd_integrand_eq hx hn hδ1 hH hb
    have h2 := fwsd_integrand_eq hx hn hδ1 hH hbm
    have hs := hH.edge_symm v
    dsimp only at hs
    rw [h1, h2] at hs
    have hconj : starRingEnd ℂ ((c₀ : ℂ) * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2)))) =
        (c₀ : ℂ) * starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          A ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconj] at hs
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc₀_pos.ne') hs
  exact ⟨hA_an, hA_ne, hlog, hlog2, h_edge_int, h_lower_int, h_vert_R, h_vert_L, h_symm⟩

/-! ### 3. Main theorem: Lemma `FW-SD` part (2) (`upper_transfer.tex`, `fw:SDp`, `(fw:e1.4)`) -/

/-- **Lemma `FW-SD` (Part 2)** (`upper_transfer.tex`, Lemma `fw:SDp`, l.295–334, `fw:e1.4`):
For fixed order `p : ℕ`, `0 < δ ≤ 1/4`, and uniform bounds `(M₀, M₀', C_ε)`, there exist constants
`N₀ ≥ 1` and `C_p ≥ 0` depending only on `(p, δ, C₃, C₄, M₀, M₀', C_ε)` such that for any
`EdgePhaseData δ C₃ C₄ Φ₀`, `x > ξ_*`, `n > 0` with `N₀ ≤ n m_x³`, and `FWSDHypotheses`,
`fwsdIntegral p Φ₀ n x ℰ Φ₁ Hp = 𝒜_x^∘ (Re[(-i b_x / x)^p e^{i Θ_x^(0)}] + O_p(R_p(x) / (n m_x³)))`. -/
theorem lemma_FW_SD_part2 (p : ℕ) {δ C₃ C₄ M₀ M₀' C_ε : ℝ} (hδ : 0 < δ) (hδ_le : δ ≤ 1 / 4)
    (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hM₀ : 0 ≤ M₀) (hM₀' : 0 ≤ M₀') (hCε : 0 ≤ C_ε) :
    ∃ N₀ C_p : ℝ, 1 ≤ N₀ ∧ 0 ≤ C_p ∧
      ∀ {Φ₀ : ℂ → ℂ} {x n : ℝ} {ℰ Φ₁ Hp εp : ℂ → ℂ},
        xiStar < x → 0 < n → N₀ ≤ n * mX x ^ 3 →
        EdgePhaseData δ C₃ C₄ Φ₀ →
        FWSDHypotheses p Φ₀ x n δ M₀ M₀' C_ε ℰ Φ₁ Hp εp →
        ∃ err : ℝ,
          |err| ≤ C_p * fwsdRatio p x / (n * mX x ^ 3) ∧
          fwsdIntegral p Φ₀ n x ℰ Φ₁ Hp =
            ((fwsdPrefactor0 n x ℰ Φ₁ *
              (((-Complex.I * (bX x / (x : ℂ))) ^ p *
                Complex.exp (Complex.I * (fwsdPhase0 Φ₀ n x ℰ Φ₁ : ℂ))).re + err) : ℝ) : ℂ) := by
  obtain ⟨N₀, C, hN₀, hC, h_sdvp⟩ := lemma_SD_V_prime hδ hδ_le hC₃ hC₄
    (by positivity : 0 ≤ M₀ + 4 * (p : ℝ) + 1)
    (by positivity : 0 ≤ M₀' + 16 * (p : ℝ) + 1)
  refine ⟨N₀, (1 + C_ε) * C + C_ε, hN₀, by positivity,
    fun {Φ₀ x n ℰ Φ₁ Hp εp} hx hn hnm hΦ hH => ?_⟩
  have hA := twoSaddleAmplitude_of_fwsd hδ hδ_le hx hn hΦ hH
  obtain ⟨err₀, herr₀_le, h_edge_eq⟩ := h_sdvp hx hn hnm hΦ hA
  have hk_pos : 0 < sdvWave n x := by
    have hxi : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
    unfold sdvWave; positivity [Real.pi_pos]
  let c₀ : ℝ := √(2 / (Real.pi * sdvWave n x)) * Real.exp (-(sdvWave n x) / 2)
  have hc₀_pos : 0 < c₀ := by positivity
  have h_int_eq : fwsdIntegral p Φ₀ n x ℰ Φ₁ Hp =
      ((2 * Real.pi * n / 3 : ℝ) : ℂ) * (c₀ : ℂ) *
        edgeIntegral Φ₀ x n (fwsdAmplitude p x n ℰ Φ₁ εp) := by
    unfold fwsdIntegral edgeIntegral saddleIntegrand
    have h_fn : (fun v : ℝ => (ℰ ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * Φ₀ ((v : ℂ) + Complex.I / 2) +
            Φ₁ ((v : ℂ) + Complex.I / 2))) *
          (((v : ℂ) + Complex.I / 2) / (x : ℂ)) ^ p *
          Hp ((sdvWave n x : ℂ) * ((v : ℂ) + Complex.I / 2)) * ((v : ℂ) + Complex.I / 2)) =
        fun v : ℝ => (c₀ : ℂ) * (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) *
          fwsdAmplitude p x n ℰ Φ₁ εp ((v : ℂ) + Complex.I / 2) *
          Complex.exp ((n : ℂ) * phiX Φ₀ x ((v : ℂ) + Complex.I / 2))) := by
      ext v
      exact fwsd_integrand_eq hx hn hδ_le hH (mem_edgeStrip_edge hδ.le v)
    rw [h_fn, integral_const_mul]
    ring
  have hx_pos : 0 < x := lt_trans (by simp [xiStar]; positivity) hx
  have hF'_pos : 0 < edgeF' (edgeV x) := edgeF'_pos (edgeV_pos hx)
  have ha_pos : 0 < alphaX x := alphaX_pos hx
  have h_sqrt_simp :
      (2 * Real.pi * n / 3) * √(2 / (Real.pi * sdvWave n x)) * √(2 * Real.pi / (n * alphaX x)) =
        √(1 / (x * edgeF' (edgeV x))) := by
    have hpi := Real.pi_pos
    have h1 : 0 ≤ 2 / (Real.pi * sdvWave n x) := by positivity
    have h2 : 0 ≤ 2 * Real.pi / (n * alphaX x) := by positivity
    have hprod : √(2 / (Real.pi * sdvWave n x)) * √(2 * Real.pi / (n * alphaX x)) =
        √((3 / (2 * Real.pi * n)) ^ 2 * (1 / (x * edgeF' (edgeV x)))) := by
      rw [← Real.sqrt_mul h1]
      congr 1
      unfold sdvWave alphaX
      field_simp [hpi.ne', hn.ne', hx_pos.ne', hF'_pos.ne']
      ring
    rw [mul_assoc (2 * Real.pi * n / 3), hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    field_simp [hpi.ne', hn.ne']
  have h_circ_norm : ‖fwsdAmplitudeCirc ℰ Φ₁ (bX x)‖ =
      ‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re * √‖bX x‖ := by
    unfold fwsdAmplitudeCirc
    rw [norm_mul, norm_mul, Complex.norm_exp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
      ← Real.sqrt_eq_rpow]
  have h_pref0_eq : (2 * Real.pi * n / 3) * c₀ *
        (2 * ‖fwsdAmplitudeCirc ℰ Φ₁ (bX x)‖ * √(2 * Real.pi / (n * alphaX x))) =
      fwsdPrefactor0 n x ℰ Φ₁ := by
    have hexp_wave : Real.exp (-(sdvWave n x) / 2) = Real.exp (-2 * Real.pi * n * x / 3) := by
      unfold sdvWave; congr 1; ring
    have hsqrt_bx : √‖bX x‖ * √(1 / (x * edgeF' (edgeV x))) =
        √(‖bX x‖ / (x * edgeF' (edgeV x))) := by
      rw [← Real.sqrt_mul (norm_nonneg _)]
      congr 1; ring
    calc (2 * Real.pi * n / 3) * c₀ *
          (2 * ‖fwsdAmplitudeCirc ℰ Φ₁ (bX x)‖ * √(2 * Real.pi / (n * alphaX x)))
        = 2 * Real.exp (-(sdvWave n x) / 2) * ‖fwsdAmplitudeCirc ℰ Φ₁ (bX x)‖ *
            ((2 * Real.pi * n / 3) * √(2 / (Real.pi * sdvWave n x)) *
              √(2 * Real.pi / (n * alphaX x))) := by
          dsimp [c₀]; ring
      _ = 2 * Real.exp (-2 * Real.pi * n * x / 3) *
            (‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re * √‖bX x‖) *
            √(1 / (x * edgeF' (edgeV x))) := by
          rw [hexp_wave, h_circ_norm, h_sqrt_simp]
      _ = 2 * Real.exp (-2 * Real.pi * n * x / 3) * ‖ℰ (bX x)‖ * Real.exp (Φ₁ (bX x)).re *
            (√‖bX x‖ * √(1 / (x * edgeF' (edgeV x)))) := by ring
      _ = fwsdPrefactor0 n x ℰ Φ₁ := by rw [hsqrt_bx]; rfl
  let Ap := fwsdAmplitude p x n ℰ Φ₁ εp (bX x)
  let Ac := fwsdAmplitudeCirc ℰ Φ₁ (bX x)
  let ep : ℂ := εp ((sdvWave n x : ℂ) * bX x)
  let w_ratio : ℂ := -Complex.I * (bX x / (x : ℂ))
  have h_ep_half : Complex.exp (-Complex.I * (Real.pi / 2 : ℂ)) = -Complex.I := by
    rw [show -Complex.I * (Real.pi / 2 : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_ofReal_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h_Ap_eq : Ap = w_ratio ^ p * Ac * (1 + ep) := by
    dsimp [Ap, Ac, ep, w_ratio]
    unfold fwsdAmplitude fwsdAmplitudeCirc
    have hpow_I : Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) = (-Complex.I) ^ p := by
      conv_rhs => rw [← h_ep_half, ← Complex.exp_nat_mul]
      congr 1; ring
    rw [hpow_I, mul_pow]
  have h_ratio_norm : ‖w_ratio ^ p‖ = fwsdRatio p x := by
    dsimp [w_ratio]; unfold fwsdRatio
    rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hx_pos.le]
  let ψ₀ : ℝ := n * (Φ₀ (bX x)).im + sdvWave n x * edgeV x - Real.pi / 2
  let Θ_p : ℝ := n * (Φ₀ (bX x)).im + 4 * Real.pi * n * x / 3 * edgeV x - Real.pi / 2 +
    Complex.arg Ap
  have h_Θp_eq : Θ_p = ψ₀ + Complex.arg Ap := by
    dsimp [Θ_p, ψ₀]; unfold sdvWave; rfl
  let main : ℂ := w_ratio ^ p * Complex.exp (Complex.I * (fwsdPhase0 Φ₀ n x ℰ Φ₁ : ℂ))
  have h_cos_polar : ‖Ap‖ * Real.cos Θ_p =
      ‖Ac‖ * (main.re + (main * ep).re) := by
    have h_Z1 : (‖Ap‖ : ℂ) * Complex.exp (Complex.I * (Θ_p : ℂ)) =
        Complex.exp (Complex.I * (ψ₀ : ℂ)) * Ap := by
      have h_ap := (Complex.norm_mul_exp_arg_mul_I Ap).symm
      rw [h_Θp_eq]
      push_cast
      rw [mul_add, Complex.exp_add]
      calc (‖Ap‖ : ℂ) * (Complex.exp (Complex.I * (ψ₀ : ℂ)) * Complex.exp (Complex.I * (Complex.arg Ap : ℂ)))
          = Complex.exp (Complex.I * (ψ₀ : ℂ)) *
              ((‖Ap‖ : ℂ) * Complex.exp ((Complex.arg Ap : ℂ) * Complex.I)) := by
            rw [mul_comm (Complex.arg Ap : ℂ) Complex.I]; ring
        _ = Complex.exp (Complex.I * (ψ₀ : ℂ)) * Ap := by rw [← h_ap]
    have h_Z2 : Complex.exp (Complex.I * (ψ₀ : ℂ)) * Ac =
        (‖Ac‖ : ℂ) * Complex.exp (Complex.I * (fwsdPhase0 Φ₀ n x ℰ Φ₁ : ℂ)) := by
      have h_ac := (Complex.norm_mul_exp_arg_mul_I Ac).symm
      have h_ph : fwsdPhase0 Φ₀ n x ℰ Φ₁ = ψ₀ + Complex.arg Ac := by
        dsimp [ψ₀, Ac]; unfold fwsdPhase0; rfl
      rw [h_ph]
      push_cast
      rw [mul_add, Complex.exp_add]
      calc Complex.exp (Complex.I * (ψ₀ : ℂ)) * Ac
          = Complex.exp (Complex.I * (ψ₀ : ℂ)) *
              ((‖Ac‖ : ℂ) * Complex.exp ((Complex.arg Ac : ℂ) * Complex.I)) := by
            rw [← h_ac]
        _ = (‖Ac‖ : ℂ) * (Complex.exp (Complex.I * (ψ₀ : ℂ)) * Complex.exp (Complex.I * (Complex.arg Ac : ℂ))) := by
            rw [mul_comm (Complex.arg Ac : ℂ) Complex.I]; ring
    have h_Z_eq : (‖Ap‖ : ℂ) * Complex.exp (Complex.I * (Θ_p : ℂ)) =
        (‖Ac‖ : ℂ) * (main * (1 + ep)) := by
      rw [h_Z1, h_Ap_eq]
      calc Complex.exp (Complex.I * (ψ₀ : ℂ)) * (w_ratio ^ p * Ac * (1 + ep))
          = w_ratio ^ p * (Complex.exp (Complex.I * (ψ₀ : ℂ)) * Ac) * (1 + ep) := by ring
        _ = w_ratio ^ p * ((‖Ac‖ : ℂ) * Complex.exp (Complex.I * (fwsdPhase0 Φ₀ n x ℰ Φ₁ : ℂ))) *
              (1 + ep) := by rw [h_Z2]
        _ = (‖Ac‖ : ℂ) * (main * (1 + ep)) := by dsimp [main]; ring
    have h_lhs_re : ((‖Ap‖ : ℂ) * Complex.exp (Complex.I * (Θ_p : ℂ))).re = ‖Ap‖ * Real.cos Θ_p := by
      rw [mul_comm Complex.I (Θ_p : ℂ), Complex.exp_ofReal_mul_I]
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    have h_rhs_re : ((‖Ac‖ : ℂ) * (main * (1 + ep))).re = ‖Ac‖ * (main.re + (main * ep).re) := by
      have hdistrib : (‖Ac‖ : ℂ) * (main * (1 + ep)) =
          (‖Ac‖ : ℂ) * main + (‖Ac‖ : ℂ) * (main * ep) := by ring
      rw [hdistrib, Complex.add_re]
      simp
      ring
    rw [← h_lhs_re, h_Z_eq, h_rhs_re]
  let err : ℝ := (main * ep).re + fwsdRatio p x * ‖1 + ep‖ * err₀
  have hm_pos : 0 < mX x := mX_pos hx
  have hnm_pos : 0 < n * mX x ^ 3 := by positivity
  have hnm1 : 1 ≤ n * mX x ^ 3 := le_trans hN₀ hnm
  have hep_bd : ‖ep‖ ≤ C_ε / (n * mX x ^ 3) := hH.eps_saddle_bound
  have h1ep_bd : ‖1 + ep‖ ≤ 1 + C_ε := by
    calc ‖1 + ep‖ ≤ ‖(1 : ℂ)‖ + ‖ep‖ := norm_add_le _ _
      _ = 1 + ‖ep‖ := by rw [norm_one]
      _ ≤ 1 + C_ε / (n * mX x ^ 3) := by gcongr
      _ ≤ 1 + C_ε := by gcongr; exact div_le_self hCε hnm1
  have herr_le : |err| ≤ ((1 + C_ε) * C + C_ε) * fwsdRatio p x / (n * mX x ^ 3) := by
    have hr0 : 0 ≤ fwsdRatio p x := by unfold fwsdRatio; positivity
    have hmain_norm : ‖main‖ = fwsdRatio p x := by
      dsimp [main]
      rw [norm_mul, h_ratio_norm, mul_comm Complex.I _, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 : |(main * ep).re| ≤ fwsdRatio p x * (C_ε / (n * mX x ^ 3)) := by
      calc |(main * ep).re| ≤ ‖main * ep‖ := Complex.abs_re_le_norm _
        _ = ‖main‖ * ‖ep‖ := norm_mul _ _
        _ = fwsdRatio p x * ‖ep‖ := by rw [hmain_norm]
        _ ≤ fwsdRatio p x * (C_ε / (n * mX x ^ 3)) := by gcongr
    have h2 : |fwsdRatio p x * ‖1 + ep‖ * err₀| ≤
        fwsdRatio p x * (1 + C_ε) * (C / (n * mX x ^ 3)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg (norm_nonneg _)]
      gcongr
    calc |err| ≤ |(main * ep).re| + |fwsdRatio p x * ‖1 + ep‖ * err₀| := abs_add_le _ _
      _ ≤ fwsdRatio p x * (C_ε / (n * mX x ^ 3)) +
            fwsdRatio p x * (1 + C_ε) * (C / (n * mX x ^ 3)) := add_le_add h1 h2
      _ = ((1 + C_ε) * C + C_ε) * fwsdRatio p x / (n * mX x ^ 3) := by ring
  refine ⟨err, herr_le, ?_⟩
  have h_Ap_norm : ‖Ap‖ = ‖Ac‖ * fwsdRatio p x * ‖1 + ep‖ := by
    rw [h_Ap_eq, norm_mul, norm_mul, h_ratio_norm]
    ring
  rw [h_int_eq, h_edge_eq]
  change ((2 * Real.pi * n / 3 : ℝ) : ℂ) * (c₀ : ℂ) *
      ((2 * ‖Ap‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.cos Θ_p + err₀) : ℝ) : ℂ) = _
  have h_real_eq : (2 * Real.pi * n / 3) * c₀ *
        (2 * ‖Ap‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.cos Θ_p + err₀)) =
      fwsdPrefactor0 n x ℰ Φ₁ * (main.re + err) := by
    calc (2 * Real.pi * n / 3) * c₀ *
          (2 * ‖Ap‖ * √(2 * Real.pi / (n * alphaX x)) * (Real.cos Θ_p + err₀))
        = (2 * Real.pi * n / 3) * c₀ * (2 * √(2 * Real.pi / (n * alphaX x))) *
            (‖Ap‖ * Real.cos Θ_p + ‖Ap‖ * err₀) := by ring
      _ = (2 * Real.pi * n / 3) * c₀ * (2 * √(2 * Real.pi / (n * alphaX x))) *
            (‖Ac‖ * (main.re + (main * ep).re) + (‖Ac‖ * fwsdRatio p x * ‖1 + ep‖) * err₀) := by
          rw [h_cos_polar, h_Ap_norm]
      _ = ((2 * Real.pi * n / 3) * c₀ * (2 * ‖Ac‖ * √(2 * Real.pi / (n * alphaX x)))) *
            (main.re + err) := by
          dsimp [err]; ring
      _ = fwsdPrefactor0 n x ℰ Φ₁ * (main.re + err) := by rw [h_pref0_eq]
  rw [← h_real_eq]
  push_cast
  ring

/-- Non-vacuity of `lemma_FW_SD_part2`: for every order `p : ℕ` and every `0 < δ ≤ 1/4`, there exist
`C₃, C₄, Φ₀, x, n, M₀, M₀', C_ε, ℰ, Φ₁, Hp, εp` satisfying `EdgePhaseData` and `FWSDHypotheses`. -/
theorem fwsd_nonvacuous (p : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ (C₃ C₄ : ℝ) (Φ₀ : ℂ → ℂ) (x n M₀ M₀' C_ε : ℝ) (ℰ Φ₁ Hp εp : ℂ → ℂ),
      xiStar < x ∧ 0 < n ∧
      EdgePhaseData δ C₃ C₄ Φ₀ ∧ FWSDHypotheses p Φ₀ x n δ M₀ M₀' C_ε ℰ Φ₁ Hp εp := by
  obtain ⟨C₃, C₄, Φ₀, ℰ, hΦ, hS⟩ := sdv_canonical_witness hδ0 hδ1
  let x : ℝ := xiStar + 1
  let n : ℝ := 1
  let Φ₁ : ℂ → ℂ := fun _ => 0
  let εp : ℂ → ℂ := fun _ => 0
  let H0 : ℂ → ℂ := fun z =>
    ((2 : ℂ) / ((Real.pi : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * (z - Real.pi / 4))
  let Hp : ℂ → ℂ := fun z =>
    Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * H0 z
  have h_circ_eq : fwsdAmplitudeCirc ℰ Φ₁ = sdvAmplitude x n ℰ Φ₁ εp := by
    ext b; unfold fwsdAmplitudeCirc sdvAmplitude; simp [εp]
  have h_circ_an : AnalyticOnNhd ℂ (fwsdAmplitudeCirc ℰ Φ₁) (edgeStrip δ) := by
    rw [h_circ_eq]; exact hS.analytic
  have h_circ_ne : ∀ b ∈ edgeStrip δ, fwsdAmplitudeCirc ℰ Φ₁ b ≠ 0 := by
    rw [h_circ_eq]; exact hS.nonzero
  have h_circ_log : ∀ b ∈ edgeStrip δ,
      ‖deriv (fwsdAmplitudeCirc ℰ Φ₁) b / fwsdAmplitudeCirc ℰ Φ₁ b‖ ≤ √2 / 2 := by
    rw [h_circ_eq]; exact hS.logDeriv_bound
  have h_circ_log2 : ∀ b ∈ edgeStrip δ,
      ‖deriv (fun z => deriv (fwsdAmplitudeCirc ℰ Φ₁) z / fwsdAmplitudeCirc ℰ Φ₁ z) b‖ ≤ 1 / 2 := by
    rw [h_circ_eq]; exact hS.logDeriv2_bound
  have h_hankel_p : ∀ b ∈ edgeStrip δ,
      Hp ((sdvWave n x : ℂ) * b) =
        ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
          (1 + εp ((sdvWave n x : ℂ) * b)) := by
    intro b hb
    have h0 := hS.hankel b hb
    dsimp [Hp, H0, εp] at h0 ⊢
    calc Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) *
          (((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
            Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4)))
        = ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
            (Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) *
              Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi / 4))) *
            (1 + 0) := by ring
      _ = ((2 : ℂ) / ((Real.pi : ℂ) * ((sdvWave n x : ℂ) * b))) ^ (1 / 2 : ℂ) *
            Complex.exp (Complex.I * ((sdvWave n x : ℂ) * b - Real.pi * (p : ℂ) / 2 - Real.pi / 4)) *
            (1 + 0) := by
          rw [← Complex.exp_add]
          congr 3
          ring
  have h_eps_an : AnalyticOnNhd ℂ (fun b => 1 + εp ((sdvWave n x : ℂ) * b)) (edgeStrip δ) := by
    simpa [εp] using analyticOnNhd_const
  have h_eps_ne : ∀ b ∈ edgeStrip δ, 1 + εp ((sdvWave n x : ℂ) * b) ≠ 0 := by
    intro b _; simp [εp]
  have h_eps_log : ∀ b ∈ edgeStrip δ,
      ‖deriv (fun z => 1 + εp ((sdvWave n x : ℂ) * z)) b / (1 + εp ((sdvWave n x : ℂ) * b))‖ ≤ 1 := by
    intro b _; simp [εp]
  have h_eps_log2 : ∀ b ∈ edgeStrip δ,
      ‖deriv (fun w => deriv (fun z => 1 + εp ((sdvWave n x : ℂ) * z)) w /
        (1 + εp ((sdvWave n x : ℂ) * w))) b‖ ≤ 1 := by
    intro b _; simp [εp]
  have h_eps_strip : ∃ C_s : ℝ, ∀ b ∈ edgeStrip δ, ‖1 + εp ((sdvWave n x : ℂ) * b)‖ ≤ C_s :=
    ⟨1, fun b _ => by simp [εp]⟩
  have h_eps_saddle : ‖εp ((sdvWave n x : ℂ) * bX x)‖ ≤ 0 / (n * mX x ^ 3) := by
    simp [εp]
  have h_ep_half : Complex.exp (-Complex.I * (Real.pi / 2 : ℂ)) = -Complex.I := by
    rw [show -Complex.I * (Real.pi / 2 : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.exp_ofReal_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h_edge_symm : ∀ v : ℝ,
      let b : ℂ := (v : ℂ) + Complex.I / 2
      let bm : ℂ := (-v : ℂ) + Complex.I / 2
      let h : ℂ → ℂ := fun z => ℰ z * Complex.exp ((n : ℂ) * Φ₀ z + Φ₁ z)
      h bm * (bm / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * bm) * bm =
        starRingEnd ℂ (h b * (b / (x : ℂ)) ^ p * Hp ((sdvWave n x : ℂ) * b) * b) := by
    intro v
    dsimp only
    let b : ℂ := (v : ℂ) + Complex.I / 2
    let bm : ℂ := (-v : ℂ) + Complex.I / 2
    have h0 := hS.edge_symm v
    dsimp only at h0
    have h_ratio_conj : Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (bm / (x : ℂ)) ^ p =
        starRingEnd ℂ (Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (b / (x : ℂ)) ^ p) := by
      have hpow_I : Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) = (-Complex.I) ^ p := by
        conv_rhs => rw [← h_ep_half, ← Complex.exp_nat_mul]
        congr 1; ring
      rw [hpow_I, ← mul_pow, ← mul_pow, map_pow]
      congr 1
      have hbm_id : -Complex.I * (bm / (x : ℂ)) =
          ((x⁻¹ : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) := by
        dsimp [bm]; rw [div_eq_mul_inv]; push_cast
        have h1 : -Complex.I * ((-v + Complex.I / 2) * (x : ℂ)⁻¹) =
            (x : ℂ)⁻¹ * (-(Complex.I * Complex.I) / 2 + (v : ℂ) * Complex.I) := by ring
        rw [h1, Complex.I_mul_I]; ring
      have hb_id : -Complex.I * (b / (x : ℂ)) =
          ((x⁻¹ : ℝ) : ℂ) * (((1 / 2 : ℝ) : ℂ) - (v : ℂ) * Complex.I) := by
        dsimp [b]; rw [div_eq_mul_inv]; push_cast
        have h1 : -Complex.I * ((v + Complex.I / 2) * (x : ℂ)⁻¹) =
            (x : ℂ)⁻¹ * (-(Complex.I * Complex.I) / 2 - (v : ℂ) * Complex.I) := by ring
        rw [h1, Complex.I_mul_I]; ring
      rw [hbm_id, hb_id, map_mul, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    have h_eq1 : (ℰ bm * Complex.exp ((n : ℂ) * Φ₀ bm + Φ₁ bm)) * (bm / (x : ℂ)) ^ p *
          Hp ((sdvWave n x : ℂ) * bm) * bm =
        (Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (bm / (x : ℂ)) ^ p) *
          ((ℰ bm * Complex.exp ((n : ℂ) * Φ₀ bm + Φ₁ bm)) * H0 ((sdvWave n x : ℂ) * bm) * bm) := by
      dsimp [Hp]; ring
    have h_eq2 : (ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) * (b / (x : ℂ)) ^ p *
          Hp ((sdvWave n x : ℂ) * b) * b =
        (Complex.exp (-Complex.I * (Real.pi * (p : ℂ) / 2)) * (b / (x : ℂ)) ^ p) *
          ((ℰ b * Complex.exp ((n : ℂ) * Φ₀ b + Φ₁ b)) * H0 ((sdvWave n x : ℂ) * b) * b) := by
      dsimp [Hp]; ring
    rw [h_eq1, h_eq2, map_mul, h_ratio_conj, h0]
  refine ⟨C₃, C₄, Φ₀, x, n, √2 / 2, 1 / 2, 0, ℰ, Φ₁, Hp, εp,
    by dsimp [x]; linarith, zero_lt_one, hΦ,
    ⟨h_circ_an, h_circ_ne, h_circ_log, h_circ_log2, h_hankel_p, h_eps_an, h_eps_ne,
      h_eps_log, h_eps_log2, h_eps_strip, h_eps_saddle, hS.h_decay, h_edge_symm⟩⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.lemma_FW_SD_part2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.lemma_FW_SD_part2

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.fwsd_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.fwsd_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Saddle




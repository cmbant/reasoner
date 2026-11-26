module

public import FormalResearch.ModularBootstrap.Mixtures.RebaseAnalysis
public import FormalResearch.ModularBootstrap.Upper.Rigidity.VagueLimit

/-!
# `pmix:rebase` (c): invariance of vague convergence under rebasing

`positive_mixtures.tex`, Lemma PM.1 (c), last sentence: for positive Radon measures `ν_j` at `n_j → ∞`, the
push-forwards `(u_{n_j})_* ((2π V_mix J_{n_j})^{-1} dν_j)` converge vaguely to `μ` if and only if the rebased
push-forwards `(u_{n'_j})_* ((2π V_mix J_{n'_j})^{-1} dν_j)` (`n' = n - 12 r_min`) do.

* `wpush u J W ν`: the weighted push-forward `u_* ((W/J) dν)` (`W = (2π V_mix)^{-1}` is the same for both charts, since
  `V_mix` is unchanged by rebasing, `pmix:rebase` (a)).
* `vague_of_close`: an abstract form.  If two charts `(u₁, J₁)`, `(u₂, J₂)` are uniformly close on every window
  (`|u₁ - u₂| ≤ ε`, `|J₁/J₂ - 1| ≤ ε` wherever `|u₁| ≤ R` or `|u₂| ≤ R`, eventually), and the weighted
  push-forwards are locally finite, then vague convergence of one family to `μ₀` gives vague convergence of the other.
  The proof is the paper's: both integrals of `φ ∈ C_c` differ by `≤ ε' ∫ χ dμ¹_j` (`χ ≥ 1_{window}`), and `∫ χ dμ¹_j` is
  bounded because it converges.
* `rebase_vague_iff`: the charts `(u_n, J_n)` and `(u_{n'}, J_{n'})` are close in this sense by `rebase_c_u`,
  `rebase_window_rev`, `rebase_c_J`, `rebase_c_J_inv`.

Hypotheses: `ν_j` carried by `(0, ∞)`, `W_j ≥ 0` measurable, and the weighted push-forwards locally finite (automatic for a
Radon measure `ν_j` on `(0, ∞)` and a locally bounded weight, because `{|u_n| ≤ R}` is compact in `(0, ∞)`; it is
assumed here).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Rigidity

/-- The weighted push-forward `u_* ((W/J) dν)`. -/
noncomputable def wpush (u J W : ℝ → ℝ) (ν : Measure ℝ) : Measure ℝ :=
  Measure.map u (ν.withDensity fun t => ENNReal.ofReal (W t / J t))

section Integrals

variable {u J W : ℝ → ℝ} {ν : Measure ℝ}

lemma integral_wpush (hu : Measurable u) (hW : Measurable W) (hJ : Measurable J)
    (hnn : ∀ᵐ t ∂ν, 0 ≤ W t / J t) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂(wpush u J W ν) = ∫ t, (W t / J t) * φ (u t) ∂ν := by
  have hmeas : Measurable fun t => ENNReal.ofReal (W t / J t) := by fun_prop
  unfold wpush
  rw [integral_map hu.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (hnn.mono fun t ht => ?_)
  simp [ENNReal.toReal_ofReal ht, smul_eq_mul]

lemma integrable_wpush_comp (hu : Measurable u) (hW : Measurable W) (hJ : Measurable J)
    (hnn : ∀ᵐ t ∂ν, 0 ≤ W t / J t) [IsLocallyFiniteMeasure (wpush u J W ν)] {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcs : HasCompactSupport φ) :
    Integrable (fun t => (W t / J t) * φ (u t)) ν := by
  have h1 : Integrable φ (wpush u J W ν) := integrable_of_cs hφ hcs
  unfold wpush at h1
  rw [integrable_map_measure hφ.aestronglyMeasurable hu.aemeasurable] at h1
  have hmeas : Measurable fun t => ENNReal.ofReal (W t / J t) := by fun_prop
  have h2 := (integrable_withDensity_iff_integrable_smul' hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).1 h1
  refine h2.congr (hnn.mono fun t ht => ?_)
  simp [ENNReal.toReal_ofReal ht, smul_eq_mul]

end Integrals

/-- **Abstract invariance of vague convergence** under a uniformly small change of chart and Jacobian. -/
theorem vague_of_close (u₁ u₂ J₁ J₂ W : ℕ → ℝ → ℝ) (ν : ℕ → Measure ℝ)
    (hu₁ : ∀ j, Measurable (u₁ j)) (hu₂ : ∀ j, Measurable (u₂ j))
    (hJ₁ : ∀ j, Measurable (J₁ j)) (hJ₂ : ∀ j, Measurable (J₂ j)) (hW : ∀ j, Measurable (W j))
    (hpos : ∀ j, ∀ᵐ t ∂ν j, 0 ≤ W j t ∧ 0 < J₁ j t ∧ 0 < J₂ j t)
    (hlf₁ : ∀ j, IsLocallyFiniteMeasure (wpush (u₁ j) (J₁ j) (W j) (ν j)))
    (hlf₂ : ∀ j, IsLocallyFiniteMeasure (wpush (u₂ j) (J₂ j) (W j) (ν j)))
    (hclose : ∀ R ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᵐ t ∂ν j,
      (|u₁ j t| ≤ R ∨ |u₂ j t| ≤ R) → |u₁ j t - u₂ j t| ≤ ε ∧ |J₁ j t / J₂ j t - 1| ≤ ε)
    {μ₀ : Measure ℝ} (h : IsVagueLimit atTop (fun j => wpush (u₁ j) (J₁ j) (W j) (ν j)) μ₀) :
    IsVagueLimit atTop (fun j => wpush (u₂ j) (J₂ j) (W j) (ν j)) μ₀ := by
  intro φ hφ hcs
  have hnn₁ : ∀ j, ∀ᵐ t ∂ν j, 0 ≤ W j t / J₁ j t := fun j =>
    (hpos j).mono fun t ht => div_nonneg ht.1 ht.2.1.le
  have hnn₂ : ∀ j, ∀ᵐ t ∂ν j, 0 ≤ W j t / J₂ j t := fun j =>
    (hpos j).mono fun t ht => div_nonneg ht.1 ht.2.2.le
  have h1 := h φ hφ hcs
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hφ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨R0, hR0⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hφ0 : ∀ x : ℝ, R0 < |x| → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hR0 hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith
  -- the cutoff `χ`
  set χ : ℝ → ℝ := fun x => max 0 (min 1 (R0 + 2 - |x|)) with hχ
  have hχc : Continuous χ := by rw [hχ]; fun_prop
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχcs : HasCompactSupport χ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R0 + 2)) fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
      have : min 1 (R0 + 2 - |x|) ≤ 0 := (min_le_right _ _).trans (by linarith)
      exact max_eq_left this
  have hχ1 : ∀ x : ℝ, |x| ≤ R0 + 1 → χ x = 1 := fun x hx => by
    have : min 1 (R0 + 2 - |x|) = 1 := min_eq_left (by linarith)
    rw [hχ]; simp only [this]; norm_num
  set M : ℝ := ∫ x, χ x ∂μ₀ + 1 with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∫ x, χ x ∂μ₀ := integral_nonneg hχ0
    linarith
  have hM0 : 0 < M := by linarith
  have hevM : ∀ᶠ j in atTop, ∫ x, χ x ∂(wpush (u₁ j) (J₁ j) (W j) (ν j)) < M :=
    (h χ hχc hχcs).eventually (gt_mem_nhds (by linarith))
  have hD : Tendsto (fun j => ∫ x, φ x ∂(wpush (u₂ j) (J₂ j) (W j) (ν j)) -
      ∫ x, φ x ∂(wpush (u₁ j) (J₁ j) (W j) (ν j))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ε₁ : ℝ := ε / (4 * M) with hε₁
    have hε₁0 : 0 < ε₁ := by positivity
    obtain ⟨η, hη, hηφ⟩ := Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hφ) ε₁ hε₁0
    set ε' : ℝ := min (η / 2) (min 1 (ε₁ / (B + 1))) with hε'
    have hε'0 : 0 < ε' := lt_min (by positivity) (lt_min one_pos (by positivity))
    have hε'η : ε' < η := (min_le_left _ _).trans_lt (by linarith)
    have hε'1 : ε' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hε'B : B * ε' ≤ ε₁ := by
      have h2 : ε' ≤ ε₁ / (B + 1) := (min_le_right _ _).trans (min_le_right _ _)
      calc B * ε' ≤ B * (ε₁ / (B + 1)) := mul_le_mul_of_nonneg_left h2 hB0
        _ = ε₁ * (B / (B + 1)) := by ring
        _ ≤ ε₁ * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by linarith)]; linarith) hε₁0.le
        _ = ε₁ := mul_one _
    filter_upwards [hclose R0 ε' hε'0, hevM] with j hj hjM
    set F₁ : ℝ → ℝ := fun t => (W j t / J₁ j t) * φ (u₁ j t) with hF₁
    set F₂ : ℝ → ℝ := fun t => (W j t / J₂ j t) * φ (u₂ j t) with hF₂
    have hi₁ : Integrable F₁ (ν j) :=
      @integrable_wpush_comp _ _ _ _ (hu₁ j) (hW j) (hJ₁ j) (hnn₁ j) (hlf₁ j) _ hφ hcs
    have hi₂ : Integrable F₂ (ν j) :=
      @integrable_wpush_comp _ _ _ _ (hu₂ j) (hW j) (hJ₂ j) (hnn₂ j) (hlf₂ j) _ hφ hcs
    have hiχ : Integrable (fun t => (W j t / J₁ j t) * χ (u₁ j t)) (ν j) :=
      @integrable_wpush_comp _ _ _ _ (hu₁ j) (hW j) (hJ₁ j) (hnn₁ j) (hlf₁ j) _ hχc hχcs
    rw [integral_wpush (hu₂ j) (hW j) (hJ₂ j) (hnn₂ j) hφ,
      integral_wpush (hu₁ j) (hW j) (hJ₁ j) (hnn₁ j) hφ, ← integral_sub hi₂ hi₁]
    have hχint : ∫ t, (W j t / J₁ j t) * χ (u₁ j t) ∂(ν j) =
        ∫ x, χ x ∂(wpush (u₁ j) (J₁ j) (W j) (ν j)) :=
      (integral_wpush (hu₁ j) (hW j) (hJ₁ j) (hnn₁ j) hχc).symm
    have hbound : ‖∫ t, (F₂ t - F₁ t) ∂(ν j)‖ ≤
        ∫ t, 2 * ε₁ * ((W j t / J₁ j t) * χ (u₁ j t)) ∂(ν j) := by
      refine norm_integral_le_of_norm_le (hiχ.const_mul _) ?_
      filter_upwards [hj, hpos j] with t ht hpt
      obtain ⟨hW0, hJ1, hJ2⟩ := hpt
      have hWJ : 0 ≤ W j t / J₁ j t := div_nonneg hW0 hJ1.le
      have hrepr : F₂ t - F₁ t =
          (W j t / J₁ j t) * (φ (u₂ j t) * (J₁ j t / J₂ j t) - φ (u₁ j t)) := by
        simp only [hF₁, hF₂]; field_simp
      rw [hrepr, Real.norm_eq_abs, abs_mul, abs_of_nonneg hWJ]
      by_cases hwin : |u₁ j t| ≤ R0 ∨ |u₂ j t| ≤ R0
      · obtain ⟨hu, hJ⟩ := ht hwin
        have hu1 : |u₁ j t| ≤ R0 + 1 := by
          rcases hwin with h | h
          · linarith
          · have := abs_sub_abs_le_abs_sub (u₁ j t) (u₂ j t)
            linarith
        rw [hχ1 _ hu1, mul_one]
        have hbr : |φ (u₂ j t) * (J₁ j t / J₂ j t) - φ (u₁ j t)| ≤ 2 * ε₁ := by
          have e1 : φ (u₂ j t) * (J₁ j t / J₂ j t) - φ (u₁ j t) =
              φ (u₂ j t) * (J₁ j t / J₂ j t - 1) + (φ (u₂ j t) - φ (u₁ j t)) := by ring
          have e2 : |φ (u₂ j t) * (J₁ j t / J₂ j t - 1)| ≤ ε₁ := by
            rw [abs_mul]
            have := hB (u₂ j t)
            rw [Real.norm_eq_abs] at this
            calc |φ (u₂ j t)| * |J₁ j t / J₂ j t - 1| ≤ B * ε' :=
                  mul_le_mul this hJ (abs_nonneg _) hB0
              _ ≤ ε₁ := hε'B
          have e3 : |φ (u₂ j t) - φ (u₁ j t)| ≤ ε₁ := by
            have := @hηφ (u₂ j t) (u₁ j t) (by
              rw [Real.dist_eq, abs_sub_comm]; exact lt_of_le_of_lt hu hε'η)
            rw [Real.dist_eq] at this
            exact this.le
          rw [e1]
          calc _ ≤ |φ (u₂ j t) * (J₁ j t / J₂ j t - 1)| + |φ (u₂ j t) - φ (u₁ j t)| := abs_add_le _ _
            _ ≤ 2 * ε₁ := by linarith
        calc (W j t / J₁ j t) * |φ (u₂ j t) * (J₁ j t / J₂ j t) - φ (u₁ j t)|
            ≤ (W j t / J₁ j t) * (2 * ε₁) := mul_le_mul_of_nonneg_left hbr hWJ
          _ = 2 * ε₁ * (W j t / J₁ j t) := by ring
      · push Not at hwin
        have h1' : φ (u₁ j t) = 0 := hφ0 _ hwin.1
        have h2' : φ (u₂ j t) = 0 := hφ0 _ hwin.2
        rw [h1', h2', zero_mul, zero_sub, abs_neg, abs_zero, mul_zero]
        have := hχ0 (u₁ j t)
        positivity
    have hrhs : ∫ t, 2 * ε₁ * ((W j t / J₁ j t) * χ (u₁ j t)) ∂(ν j) ≤ ε / 2 := by
      rw [integral_const_mul, hχint]
      calc 2 * ε₁ * ∫ x, χ x ∂(wpush (u₁ j) (J₁ j) (W j) (ν j)) ≤ 2 * ε₁ * M :=
            mul_le_mul_of_nonneg_left hjM.le (by positivity)
        _ = ε / 2 := by rw [hε₁]; field_simp; ring
    rw [Real.dist_eq, sub_zero]
    have : |∫ t, (F₂ t - F₁ t) ∂(ν j)| ≤ ε / 2 := by
      have := hbound.trans hrhs
      rwa [Real.norm_eq_abs] at this
    linarith
  have := hD.add h1
  simpa using this

/-- Two-sided form of `vague_of_close`: vague convergence of the `(u₁, J₁)`-push-forwards to `μ₀` is equivalent to
that of the `(u₂, J₂)`-push-forwards, if the charts are close on every window in both ratios. -/
theorem vague_iff_of_close (u₁ u₂ J₁ J₂ W : ℕ → ℝ → ℝ) (ν : ℕ → Measure ℝ)
    (hu₁ : ∀ j, Measurable (u₁ j)) (hu₂ : ∀ j, Measurable (u₂ j))
    (hJ₁ : ∀ j, Measurable (J₁ j)) (hJ₂ : ∀ j, Measurable (J₂ j)) (hW : ∀ j, Measurable (W j))
    (hpos : ∀ j, ∀ᵐ t ∂ν j, 0 ≤ W j t ∧ 0 < J₁ j t ∧ 0 < J₂ j t)
    (hlf₁ : ∀ j, IsLocallyFiniteMeasure (wpush (u₁ j) (J₁ j) (W j) (ν j)))
    (hlf₂ : ∀ j, IsLocallyFiniteMeasure (wpush (u₂ j) (J₂ j) (W j) (ν j)))
    (hclose : ∀ R ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᵐ t ∂ν j,
      (|u₁ j t| ≤ R ∨ |u₂ j t| ≤ R) → |u₁ j t - u₂ j t| ≤ ε ∧
        |J₁ j t / J₂ j t - 1| ≤ ε ∧ |J₂ j t / J₁ j t - 1| ≤ ε)
    (μ₀ : Measure ℝ) :
    IsVagueLimit atTop (fun j => wpush (u₁ j) (J₁ j) (W j) (ν j)) μ₀ ↔
      IsVagueLimit atTop (fun j => wpush (u₂ j) (J₂ j) (W j) (ν j)) μ₀ := by
  constructor
  · exact vague_of_close u₁ u₂ J₁ J₂ W ν hu₁ hu₂ hJ₁ hJ₂ hW hpos hlf₁ hlf₂ (fun R ε hε =>
      (hclose R ε hε).mono fun j hj => hj.mono fun t ht hw => ⟨(ht hw).1, (ht hw).2.1⟩)
  · exact vague_of_close u₂ u₁ J₂ J₁ W ν hu₂ hu₁ hJ₂ hJ₁ hW
      (fun j => (hpos j).mono fun t ht => ⟨ht.1, ht.2.2, ht.2.1⟩) hlf₂ hlf₁ (fun R ε hε =>
      (hclose R ε hε).mono fun j hj => hj.mono fun t ht hw =>
        ⟨by rw [abs_sub_comm]; exact (ht hw.symm).1, (ht hw.symm).2.2⟩)

/-! ### The rebased charts -/

private lemma measurable_uAiry (c : ℝ) : Measurable (uAiry c) := by
  unfold uAiry; fun_prop

private lemma measurable_jAiry (c : ℝ) : Measurable (jAiry c) := by
  unfold jAiry; fun_prop

/-- **`pmix:rebase` (c)**, vague convergence: with `n'_j = n_j - 12 r` (`r = r_min ≥ 0`), the push-forwards
`(u_{n_j})_* ((W_j / J_{n_j}) dν_j)` converge vaguely to `μ₀` if and only if the rebased push-forwards
`(u_{n'_j})_* ((W_j / J_{n'_j}) dν_j)` do (`W_j = (2π V_mix)^{-1}`; `ν_j` carried by `(0, ∞)`). -/
theorem rebase_vague_iff {r : ℝ} (hr : 0 ≤ r) {n : ℕ → ℝ} (hn : Tendsto n atTop atTop)
    (hn0 : ∀ j, 12 * r < n j)
    (ν : ℕ → Measure ℝ) (hν : ∀ j, ν j (Iic 0) = 0) (W : ℕ → ℝ → ℝ)
    (hW : ∀ j, Measurable (W j)) (hW0 : ∀ j t, 0 < t → 0 ≤ W j t)
    (hlf₁ : ∀ j, IsLocallyFiniteMeasure (wpush (uAiry (n j)) (jAiry (n j)) (W j) (ν j)))
    (hlf₂ : ∀ j, IsLocallyFiniteMeasure
      (wpush (uAiry (n j - 12 * r)) (jAiry (n j - 12 * r)) (W j) (ν j)))
    (μ₀ : Measure ℝ) :
    IsVagueLimit atTop (fun j => wpush (uAiry (n j)) (jAiry (n j)) (W j) (ν j)) μ₀ ↔
      IsVagueLimit atTop (fun j => wpush (uAiry (n j - 12 * r)) (jAiry (n j - 12 * r)) (W j) (ν j))
        μ₀ := by
  have hβ := betaTip_pos
  have hξ := xiStar_pos
  have hJpos : ∀ c t : ℝ, 0 < c → 0 < t → 0 < jAiry c t := fun c t hc ht => by
    unfold jAiry
    have : 0 < √(3 * t / c) := Real.sqrt_pos.mpr (by positivity)
    have := Real.rpow_pos_of_pos hc ((1 : ℝ) / 3)
    positivity
  have hae : ∀ j, ∀ᵐ t ∂ν j, 0 < t := fun j => by
    rw [ae_iff, show {t : ℝ | ¬ 0 < t} = Iic 0 by ext t; simp]
    exact hν j
  refine vague_iff_of_close (fun j => uAiry (n j)) (fun j => uAiry (n j - 12 * r))
    (fun j => jAiry (n j)) (fun j => jAiry (n j - 12 * r)) W ν
    (fun j => measurable_uAiry _) (fun j => measurable_uAiry _) (fun j => measurable_jAiry _)
    (fun j => measurable_jAiry _) hW ?_ hlf₁ hlf₂ ?_ μ₀
  · intro j
    filter_upwards [hae j] with t ht
    exact ⟨hW0 j t ht, hJpos (n j) t (by linarith [hn0 j]) ht,
      hJpos (n j - 12 * r) t (by linarith [hn0 j]) ht⟩
  · intro R ε hε
    obtain ⟨C, n₁, hC, hn₁, hcu⟩ := rebase_c_u (R + 1) hr
    obtain ⟨n₂, hn₂1, hrev⟩ := rebase_window_rev R hr
    have hE : Tendsto (fun x : ℝ => 6 * betaTip * r * xiStar / x ^ ((1 : ℝ) / 3) + C / x) atTop (𝓝 0) := by
      have h1 := (tendsto_const_nhds (x := 6 * betaTip * r * xiStar)).div_atTop
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
      have h2 := (tendsto_const_nhds (x := C)).div_atTop tendsto_id
      simpa using h1.add h2
    have hE24 : Tendsto (fun x : ℝ => 24 * r / x) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 24 * r)).div_atTop tendsto_id
    have hev : ∀ᶠ x : ℝ in atTop, max (max n₁ n₂) (24 * r) ≤ x ∧
        6 * betaTip * r * xiStar / x ^ ((1 : ℝ) / 3) + C / x < ε ∧ 24 * r / x < ε :=
      (eventually_ge_atTop _).and ((hE.eventually (gt_mem_nhds hε)).and
        (hE24.eventually (gt_mem_nhds hε)))
    filter_upwards [hn.eventually hev] with j hj
    obtain ⟨hjn, hjE, hj24⟩ := hj
    have hjn₁ : n₁ ≤ n j := (le_max_left _ _).trans ((le_max_left _ _).trans hjn)
    have hjn₂ : n₂ ≤ n j := (le_max_right _ _).trans ((le_max_left _ _).trans hjn)
    have hjn24 : 24 * r ≤ n j := (le_max_right _ _).trans hjn
    have hn1 : 1 ≤ n j := hn₁.trans hjn₁
    filter_upwards [hae j] with t ht hwin
    have hu2 : |uAiry (n j - 12 * r) t| ≤ R + 1 := by
      rcases hwin with h | h
      · exact hrev (n j) hjn₂ t ht h
      · linarith
    have hu := hcu (n j) hjn₁ t ht hu2
    have hnn : 0 < n j := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have : |uAiry (n j) t - uAiry (n j - 12 * r) t| ≤
          6 * betaTip * r * xiStar / n j ^ ((1 : ℝ) / 3) + C / n j := by
        have h3 := abs_sub_abs_le_abs_sub (uAiry (n j) t - uAiry (n j - 12 * r) t)
          (6 * betaTip * r * xiStar / n j ^ ((1 : ℝ) / 3))
        have h4 : |6 * betaTip * r * xiStar / n j ^ ((1 : ℝ) / 3)| =
            6 * betaTip * r * xiStar / n j ^ ((1 : ℝ) / 3) := by
          refine abs_of_nonneg ?_
          have := Real.rpow_pos_of_pos hnn ((1 : ℝ) / 3)
          positivity
        linarith
      linarith
    · have := rebase_c_J hr hn1 hjn24 ht
      have h24 : 12 * r / n j ≤ 24 * r / n j :=
        div_le_div_of_nonneg_right (by linarith) hnn.le
      show |jAiry (n j) t / jAiry (n j - 12 * r) t - 1| ≤ ε
      linarith
    · have := rebase_c_J_inv hr hn1 hjn24 ht
      show |jAiry (n j - 12 * r) t / jAiry (n j) t - 1| ≤ ε
      linarith

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.vague_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vague_of_close

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rebase_vague_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rebase_vague_iff

end FormalResearch.ModularBootstrap.Mixtures

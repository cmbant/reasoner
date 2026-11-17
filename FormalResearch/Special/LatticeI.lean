module

public import FormalResearch.Special.LatticeSmooth

/-!
# `lem:latticesum` (i), abstract form

`‖∫_{-X}^{X} φ ({t} - ½)‖ ≤ C_φ·wconst κ·ε·(1 + 4(M+2ε+1)/m) + C_φ e^{-κX}/m
 + (1/12)(2C_w y₁ e^{-κX} + (2C_w/κ) e^{-2πmy₁})`

for `t` `ε`-close to the calibrated phase `t₀` (`LevelData`), `φ` holomorphic on `|Im s| ≤ y₀`,
`y₁ + r ≤ y₀`.  First term: `fract_diff_integral_le` (`{t}` against `{t₀}`); the rest:
`smooth_saw_bound` (integration by parts, Fourier series of `B₂({·})`, contour shift).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma continuous_real_of_strip {φ : ℂ → ℂ} {y0 : ℝ} (hy0 : 0 < y0)
    (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0}) : Continuous (fun s : ℝ => φ (s : ℂ)) := by
  refine continuous_iff_continuousAt.mpr (fun s => ?_)
  have hU : IsOpen {s : ℂ | |s.im| < y0} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hmem : {s : ℂ | |s.im| ≤ y0} ∈ 𝓝 (s : ℂ) :=
    Filter.mem_of_superset (hU.mem_nhds (by show |(s : ℂ).im| < y0; simpa using hy0))
      (fun z hz => le_of_lt (show |z.im| < y0 from hz))
  have h1 : ContinuousAt φ (s : ℂ) := (hφd.differentiableAt hmem).continuousAt
  exact h1.comp (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt

theorem latticeI_bound {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (hd : LevelData τ0 X y0 m M K ε t S) {φ : ℂ → ℂ} {Cφ κ y1 r : ℝ} (hκ : 0 < κ) (hCφ : 0 ≤ Cφ)
    (hy1 : 0 < y1) (hr : 0 < r) (hyr : y1 + r ≤ y0)
    (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0})
    (hφb : ∀ s : ℂ, |s.im| ≤ y0 → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|)) :
    ‖∫ s in (-X)..X, φ (s : ℂ) * (((Int.fract (t s) - 1 / 2 : ℝ)) : ℂ)‖ ≤
      Cφ * wconst κ * ε * (1 + 4 * (M + 2 * ε + 1) / m) +
      (Cφ * Real.exp (-κ * X) / m +
        1 / 12 * (2 * smoothCw Cφ κ r m K * y1 * Real.exp (-κ * X) +
          2 * smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)))) := by
  have h := hd.cal
  have hX := h.hX
  have hy0 : 0 < y0 := h.hy0
  have hφc : Continuous (fun s : ℝ => φ (s : ℂ)) := continuous_real_of_strip hy0 hφd
  have hφr : ∀ s : ℝ, ‖φ (s : ℂ)‖ ≤ Cφ * Real.exp (-κ * |s|) := fun s => by
    have := hφb (s : ℂ) (by simpa using hy0.le)
    simpa using this
  have hsub : Icc (-X) X ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc (by linarith) (by linarith)
  have hI1 : IntervalIntegrable (fractDiff (fun s : ℝ => φ (s : ℂ)) τ0 t) volume (-X) X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact (fractDiff_integrableOn hd hφc hκ.le hCφ hφr).mono_set hsub
  have hI2 : IntervalIntegrable (fun s : ℝ => φ (s : ℂ) * (((Int.fract (realPhase τ0 s) - 1 / 2 : ℝ)) : ℂ))
      volume (-X) X := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    have hm : AEStronglyMeasurable (fun s : ℝ => φ (s : ℂ) * (((Int.fract (realPhase τ0 s) - 1 / 2 : ℝ)) : ℂ))
        (volume.restrict (Icc (-X) X)) := by
      refine hφc.aestronglyMeasurable.mul ?_
      refine (Complex.measurable_ofReal.comp_aemeasurable ?_).aestronglyMeasurable
      exact (measurable_fract.comp_aemeasurable
        ((h.continuousOn_realPhase.mono hsub).aemeasurable measurableSet_Icc)).sub_const (1 / 2 : ℝ)
    show Integrable _ (volume.restrict (Icc (-X) X))
    refine Integrable.of_bound hm (Cφ * (1 / 2)) ?_
    refine Filter.Eventually.of_forall (fun s => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Int.fract (realPhase τ0 s) - 1 / 2| ≤ 1 / 2 := by
      have := Int.fract_nonneg (realPhase τ0 s); have := Int.fract_lt_one (realPhase τ0 s)
      rw [abs_le]; constructor <;> linarith
    have h2 : ‖φ (s : ℂ)‖ ≤ Cφ := by
      refine (hφr s).trans ?_
      have : Real.exp (-κ * |s|) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg s]
      nlinarith
    exact mul_le_mul h2 h1 (abs_nonneg _) hCφ
  have hsplit : ∫ s in (-X)..X, φ (s : ℂ) * (((Int.fract (t s) - 1 / 2 : ℝ)) : ℂ) =
      (∫ s in (-X)..X, fractDiff (fun s : ℝ => φ (s : ℂ)) τ0 t s) +
      ∫ s in (-X)..X, φ (s : ℂ) * (((Int.fract (realPhase τ0 s) - 1 / 2 : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [fractDiff]
    push_cast
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact fract_diff_integral_le hd hφc hκ hCφ hφr
  · exact smooth_saw_bound h hκ hCφ hy1 hr hyr hφd hφb

end FormalResearch.Special.Lattice

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Generalized Scheffé Lemma

If integrable `E`-valued functions `f n` converge `μ`-a.e. to an integrable `g` along a countably
generated filter `p` and `∫ ‖f n‖ ∂μ → ∫ ‖g‖ ∂μ`, then `∫ ‖f n - g‖ ∂μ → 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FormalResearch.Analysis

/-- **Generalized Scheffé Lemma.** If integrable `E`-valued functions `f n` converge a.e. to an
integrable `g` along a countably generated filter `p`, and `∫ ‖f n‖ → ∫ ‖g‖`, then
`∫ ‖f n - g‖ → 0`. -/
theorem tendsto_integral_norm_sub_of_tendsto_ae
    {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : Filter ι} [p.IsCountablyGenerated]
    {f : ι → α → E} {g : α → E}
    (hf_int : ∀ᶠ n in p, Integrable (f n) μ) (hg_int : Integrable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) p (𝓝 (g x)))
    (hnorm : Tendsto (fun n => ∫ x, ‖f n x‖ ∂μ) p (𝓝 (∫ x, ‖g x‖ ∂μ))) :
    Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂μ) p (𝓝 0) := by
  let h : ι → α → ℝ := fun n x => ‖f n x‖ + ‖g x‖ - ‖f n x - g x‖
  let bound : α → ℝ := fun x => 2 * ‖g x‖
  have hh_meas : ∀ᶠ n in p, AEStronglyMeasurable (h n) μ :=
    hf_int.mono fun n hn => ((hn.norm.add hg_int.norm).sub (hn.sub hg_int).norm).aestronglyMeasurable
  have hh_bound : ∀ᶠ n in p, ∀ᵐ x ∂μ, ‖h n x‖ ≤ bound x :=
    Eventually.of_forall fun n => Eventually.of_forall fun x => by
      have h1 : ‖f n x - g x‖ ≤ ‖f n x‖ + ‖g x‖ := norm_sub_le _ _
      have h2 : ‖f n x‖ ≤ ‖f n x - g x‖ + ‖g x‖ := by simpa using norm_add_le (f n x - g x) (g x)
      rw [Real.norm_of_nonneg (sub_nonneg.mpr h1)]
      dsimp [h, bound]; linarith
  have hh_lim : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) p (𝓝 (bound x)) := by
    filter_upwards [hae] with x hx
    have hx_sub : Tendsto (fun n => ‖f n x - g x‖) p (𝓝 0) := by
      simpa [sub_self, norm_zero] using (hx.sub (tendsto_const_nhds (x := g x))).norm
    simpa [h, bound, two_mul] using (hx.norm.add (tendsto_const_nhds (x := ‖g x‖))).sub hx_sub
  have ht_h : Tendsto (fun n => ∫ x, h n x ∂μ) p (𝓝 (2 * ∫ x, ‖g x‖ ∂μ)) := by
    simpa [bound, integral_const_mul] using
      tendsto_integral_filter_of_dominated_convergence bound hh_meas hh_bound (hg_int.norm.const_mul 2) hh_lim
  have heq : ∀ᶠ n in p, ∫ x, ‖f n x - g x‖ ∂μ =
      (∫ x, ‖f n x‖ ∂μ) + (∫ x, ‖g x‖ ∂μ) - ∫ x, h n x ∂μ := by
    filter_upwards [hf_int] with n hn
    have hint_h : ∫ x, h n x ∂μ = (∫ x, ‖f n x‖ ∂μ) + (∫ x, ‖g x‖ ∂μ) - ∫ x, ‖f n x - g x‖ ∂μ := by
      have hadd : Integrable (fun x => ‖f n x‖ + ‖g x‖) μ := hn.norm.add hg_int.norm
      have hsub : Integrable (fun x => ‖f n x - g x‖) μ := (hn.sub hg_int).norm
      change ∫ x, (‖f n x‖ + ‖g x‖) - ‖f n x - g x‖ ∂μ =
        (∫ x, ‖f n x‖ ∂μ) + (∫ x, ‖g x‖ ∂μ) - ∫ x, ‖f n x - g x‖ ∂μ
      rw [integral_sub hadd hsub, integral_add hn.norm hg_int.norm]
    linarith
  have ht_rhs : Tendsto (fun n => (∫ x, ‖f n x‖ ∂μ) + (∫ x, ‖g x‖ ∂μ) - ∫ x, h n x ∂μ) p (𝓝 0) := by
    simpa [two_mul] using (hnorm.add (tendsto_const_nhds (x := ∫ x, ‖g x‖ ∂μ))).sub ht_h
  exact ht_rhs.congr' (heq.mono fun _ h => h.symm)


/-- info: 'FormalResearch.Analysis.tendsto_integral_norm_sub_of_tendsto_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.tendsto_integral_norm_sub_of_tendsto_ae

end FormalResearch.Analysis

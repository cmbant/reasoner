module

public import FormalResearch.SignUncertainty.RadialProfileDeriv

/-!
# `L¹` clause (Fatou) and reality of the limit (`lem:radial-compactness`, Step 4)

* `integrable_of_fatou`: a pointwise limit of functions with `∫ |Ψ_k| ≤ M` is integrable.
* `XiL_im_eq_zero`: `Ξ_W` is real on `ℝ` (limit of the real `Ξ_{c_k}`), so `F = radialF W` is real on `ℝ`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

theorem integrable_of_fatou {Ψ : ℕ → ℝ → ℝ} {φ : ℝ → ℝ} {M : ℝ}
    (hint : ∀ k, Integrable (Ψ k)) (hM : ∀ k, ∫ u, |Ψ k u| ≤ M)
    (hlim : ∀ u, Tendsto (fun k => Ψ k u) atTop (𝓝 (φ u))) (hφ : AEStronglyMeasurable φ volume) :
    Integrable φ := by
  refine ⟨hφ, ?_⟩
  have hF := lintegral_liminf_le' (μ := volume) (u := (atTop : Filter ℕ)) (f := fun k u => ‖Ψ k u‖ₑ)
    (fun k => (hint k).aestronglyMeasurable.enorm)
  have h1 : ∀ u, Filter.liminf (fun k => ‖Ψ k u‖ₑ) atTop = ‖φ u‖ₑ := fun u =>
    ((continuous_enorm.tendsto _).comp (hlim u)).liminf_eq
  simp_rw [h1] at hF
  have h2 : ∀ k, ∫⁻ u, ‖Ψ k u‖ₑ ≤ ENNReal.ofReal M := by
    intro k
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hint k)]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hM k)
  have h3 : Filter.liminf (fun k => ∫⁻ u, ‖Ψ k u‖ₑ) atTop ≤ ENNReal.ofReal M :=
    liminf_le_of_frequently_le' (Frequently.of_forall h2)
  exact (hF.trans h3).trans_lt ENNReal.ofReal_lt_top

theorem XiL_im_eq_zero {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) (s : ℝ) :
    (XiL W (s : ℂ)).im = 0 := by
  have h1 := radial_value_limit hε hc hf hM hW
  have h2 : Tendsto (fun k => (∫ v : ℝ, radialA (c k) (f k) s v).im) atTop (𝓝 (XiL W (s : ℂ)).im) := by
    have := (Complex.continuous_im.tendsto _).comp
      ((h1.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ s))
    rw [XiL_ofReal]; exact this
  have h3 : ∀ᶠ k in atTop, (∫ v : ℝ, radialA (c k) (f k) s v).im = 0 := by
    filter_upwards [eventually_good hc |s|] with k hk
    have hc0 : 0 < c k := by linarith [hk.1]
    obtain ⟨hξ, -⟩ := radialXi_facts hc0 (le_refl |s|) hk.2
    rw [integral_radialA_eq (by linarith [hk.1]) (hf k) hε hξ]
    exact Complex.ofReal_im _
  exact tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (h3.mono fun k hk => hk.symm))

lemma radialF_ofReal (W : ℂ → ℂ) (u : ℝ) :
    radialF W (u : ℂ) = ((hankelBeta1⁻¹ : ℝ) : ℂ) * XiL W ((-u / hankelBeta1 : ℝ) : ℂ) := by
  unfold radialF
  congr 2
  push_cast; ring

lemma radialF_re (W : ℂ → ℂ) (u : ℝ) :
    (radialF W (u : ℂ)).re = hankelBeta1⁻¹ * (XiL W ((-u / hankelBeta1 : ℝ) : ℂ)).re := by
  rw [radialF_ofReal, Complex.re_ofReal_mul]

end FormalResearch.SignUncertainty

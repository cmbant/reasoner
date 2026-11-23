module

public import FormalResearch.SignUncertainty.RadialValueLimit

/-!
# `Ξ_{c_k} → Ξ` locally uniformly (`lem:radial-compactness`, Step 3)

If `W_{c_k}(w) → W(w)` for `Re w > 0` then `s ↦ ∫ radialA (c k) (f k) s v dv` converges locally uniformly to
`s ↦ ∫ (π/2) K_lim(1+iv, s) W(1+iv) dv` (`radial_value_limit`), by the dominated-convergence principle
`tendstoLocallyUniformly_integral`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The limit integrand `(π/2) K_lim(1+iv, s) W(1+iv)`. -/
noncomputable def radialAlim (W : ℂ → ℂ) (s v : ℝ) : ℂ :=
  ((Real.pi / 2 : ℝ) : ℂ) * (radialKlim (1 + (v : ℂ) * Complex.I) s * W (1 + (v : ℂ) * Complex.I))

lemma radialA_tendsto {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ} (hc : Tendsto c atTop atTop) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    ∀ s₀ v : ℝ, Tendsto (fun p : ℕ × ℝ => radialA (c p.1) (f p.1) p.2 v)
      (atTop ×ˢ 𝓝 s₀) (𝓝 (radialAlim W s₀ v)) := by
  have hεc : Tendsto (fun k => radialEps (c k)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  intro s₀ v
  have hc' : Tendsto (fun p : ℕ × ℝ => c p.1) (atTop ×ˢ 𝓝 s₀) atTop := hc.comp tendsto_fst
  have hs' : Tendsto (fun p : ℕ × ℝ => p.2) (atTop ×ˢ 𝓝 s₀) (𝓝 s₀) := tendsto_snd
  have hK := radialK_tendsto hc' hs' (1 + (v : ℂ) * Complex.I)
  have hWp : Tendsto (fun p : ℕ × ℝ => radialW (c p.1) (f p.1) (1 + (v : ℂ) * Complex.I))
      (atTop ×ˢ 𝓝 s₀) (𝓝 (W (1 + (v : ℂ) * Complex.I))) :=
    (hW _ (by simp)).comp tendsto_fst
  have hξ : Tendsto (fun p : ℕ × ℝ => radialXi (c p.1) p.2) (atTop ×ˢ 𝓝 s₀) (𝓝 (1 / Real.pi ^ 2)) := by
    have he : Tendsto (fun p : ℕ × ℝ => radialEps (c p.1)) (atTop ×ˢ 𝓝 s₀) (𝓝 0) :=
      hεc.comp tendsto_fst
    have := (he.pow 2).mul hs'
    have h2 : Tendsto (fun p : ℕ × ℝ => 1 / Real.pi ^ 2 + radialEps (c p.1) ^ 2 * p.2)
        (atTop ×ˢ 𝓝 s₀) (𝓝 (1 / Real.pi ^ 2 + 0 ^ 2 * s₀)) := tendsto_const_nhds.add this
    simpa [radialXi] using h2
  have hco : Tendsto (fun p : ℕ × ℝ => ((1 / (2 * Real.pi * radialXi (c p.1) p.2) : ℝ) : ℂ))
      (atTop ×ˢ 𝓝 s₀) (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) := by
    have h1 : Tendsto (fun p : ℕ × ℝ => 1 / (2 * Real.pi * radialXi (c p.1) p.2)) (atTop ×ˢ 𝓝 s₀)
        (𝓝 (1 / (2 * Real.pi * (1 / Real.pi ^ 2)))) := by
      refine tendsto_const_nhds.div (tendsto_const_nhds.mul hξ) ?_
      positivity
    have h2 : 1 / (2 * Real.pi * (1 / Real.pi ^ 2)) = Real.pi / 2 := by field_simp
    rw [h2] at h1
    exact (Complex.continuous_ofReal.tendsto _).comp h1
  exact hco.mul (hK.mul hWp)

set_option maxHeartbeats 1000000 in
theorem radial_value_limit {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ} {M₀ : ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    TendstoLocallyUniformly (fun k s => ∫ v : ℝ, radialA (c k) (f k) s v)
      (fun s => ∫ v : ℝ, radialAlim W s v) atTop := by
  have hpi := Real.pi_pos
  have hεc : Tendsto (fun k => radialEps (c k)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  have hev : ∀ S : ℝ, ∃ N : ℕ, ∀ k ≥ N, 1000 ≤ c k ∧ Real.pi ^ 2 * radialEps (c k) ^ 2 * S ≤ 1 / 2 := by
    intro S
    have h1 := hc.eventually_ge_atTop 1000
    have h2 : Tendsto (fun k => Real.pi ^ 2 * radialEps (c k) ^ 2 * S) atTop (𝓝 0) := by
      simpa using ((hεc.pow 2).const_mul (Real.pi ^ 2)).mul_const S
    have h3 := h2.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    exact eventually_atTop.mp (h1.and h3)
  set Bd : ℝ → ℝ → ℝ := fun S v => Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
    (2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ))) with hBd
  have hBdi : ∀ S, Integrable (Bd S) := fun S => integrable_dom.const_mul _
  have hAb : ∀ S : ℝ, ∃ N : ℕ, ∀ k ≥ N, ∀ s, |s| ≤ S → ∀ v, ‖radialA (c k) (f k) s v‖ ≤ Bd S v := by
    intro S
    obtain ⟨N, hN⟩ := hev S
    exact ⟨N, fun k hk s hs v => radialA_norm_le (hN k hk).1 (hf k) hε (hM k) hs (hN k hk).2⟩
  have hlim := radialA_tendsto hc hW
  -- apply the general lemma
  refine tendstoLocallyUniformly_integral (F := fun k s v => radialA (c k) (f k) s v) (Flim := radialAlim W) ?_ ?_ hlim ?_
  · intro s₀
    obtain ⟨N, hN⟩ := hev (|s₀| + 1)
    have : ∀ᶠ y in (atTop ×ˢ 𝓝 s₀ : Filter (ℕ × ℝ)), y.1 ≥ N ∧ |y.2 - s₀| < 1 :=
      (tendsto_fst.eventually (eventually_ge_atTop N)).and
        (tendsto_snd.eventually (by
          filter_upwards [Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1)] with y hy
          simpa [Real.dist_eq] using hy))
    filter_upwards [this] with y hy
    have hs : |y.2| ≤ |s₀| + 1 := by
      have := abs_sub_abs_le_abs_sub y.2 s₀; linarith [hy.2]
    obtain ⟨hξ, -⟩ := radialXi_facts (by linarith [(hN y.1 hy.1).1] : 0 < c y.1) hs (hN y.1 hy.1).2
    have hcont := continuous_radialKW (by linarith [(hN y.1 hy.1).1] : 3 / 2 < c y.1) (hf y.1) hξ
    exact (continuous_const.mul hcont).aestronglyMeasurable
  · intro s₀
    obtain ⟨N, hN⟩ := hAb (|s₀| + 1)
    refine ⟨Bd (|s₀| + 1), hBdi _, N, 1, one_pos, fun k hk s hs v => hN k hk s ?_ v⟩
    have := abs_sub_abs_le_abs_sub s s₀; linarith
  · refine continuous_integral_lim (F := fun k s v => radialA (c k) (f k) s v) (Flim := radialAlim W) ?_ ?_ hlim ?_
    · intro s₀
      obtain ⟨N, hN⟩ := hev (|s₀| + 1)
      have : ∀ᶠ y in (atTop ×ˢ 𝓝 s₀ : Filter (ℕ × ℝ)), y.1 ≥ N ∧ |y.2 - s₀| < 1 :=
        (tendsto_fst.eventually (eventually_ge_atTop N)).and
          (tendsto_snd.eventually (by
            filter_upwards [Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1)] with y hy
            simpa [Real.dist_eq] using hy))
      filter_upwards [this] with y hy
      have hs : |y.2| ≤ |s₀| + 1 := by
        have := abs_sub_abs_le_abs_sub y.2 s₀; linarith [hy.2]
      obtain ⟨hξ, -⟩ := radialXi_facts (by linarith [(hN y.1 hy.1).1] : 0 < c y.1) hs (hN y.1 hy.1).2
      have hcont := continuous_radialKW (by linarith [(hN y.1 hy.1).1] : 3 / 2 < c y.1) (hf y.1) hξ
      exact (continuous_const.mul hcont).aestronglyMeasurable
    · intro s₀
      obtain ⟨N, hN⟩ := hAb (|s₀| + 1)
      refine ⟨Bd (|s₀| + 1), hBdi _, N, 1, one_pos, fun k hk s hs v => hN k hk s ?_ v⟩
      have := abs_sub_abs_le_abs_sub s s₀; linarith
    · intro v
      unfold radialAlim radialKlim
      fun_prop

/-- info: 'FormalResearch.SignUncertainty.radial_value_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radial_value_limit

end FormalResearch.SignUncertainty

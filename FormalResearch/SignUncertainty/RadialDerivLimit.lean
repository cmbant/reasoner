module

public import FormalResearch.SignUncertainty.RadialDerivMain
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating `Ξ_c` under the integral and the derivative limit (`lem:radial-compactness`, Step 3)
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma continuous_radialA {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {s : ℝ}
    (hξ : 0 < radialXi c s) : Continuous fun v : ℝ => radialA c f s v := by
  unfold radialA
  exact continuous_const.mul (continuous_radialKW hc hf hξ)

lemma continuous_radialdA {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {s : ℝ}
    (hξ : 0 < radialXi c s) : Continuous fun v : ℝ => radialdA c f s v := by
  unfold radialdA
  have : Continuous fun v : ℝ => (1 + (v : ℂ) * Complex.I - ((radialEps c ^ 2 : ℝ) : ℂ)) *
      ((radialXi c s : ℝ) : ℂ)⁻¹ := by fun_prop
  exact this.mul (continuous_radialA hc hf hξ)

theorem hasDerivAt_radialXi {c ε s₀ : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hS : Real.pi ^ 2 * radialEps c ^ 2 * (|s₀| + 1) ≤ 1 / 2) :
    HasDerivAt (fun s => ∫ v : ℝ, radialA c f s v) (∫ v : ℝ, radialdA c f s₀ v) s₀ := by
  have hc0 : 0 < c := by linarith
  set M₀ := hankelMass c f with hM₀
  set K : ℝ := 4 * Real.pi ^ 2 * (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * (|s₀| + 1))) *
    (M₀ * (11 / 10)) * (2 * 200 ^ 5)) with hK
  have hsS : ∀ s ∈ ball s₀ (1 : ℝ), |s| ≤ |s₀| + 1 := fun s hs => by
    have := abs_sub_abs_le_abs_sub s s₀
    have h2 : |s - s₀| < 1 := by simpa [Real.dist_eq] using hs
    linarith
  have hξall : ∀ s ∈ ball s₀ (1 : ℝ), 0 < radialXi c s := fun s hs =>
    (radialXi_facts hc0 (hsS s hs) hS).1
  have hbound : ∀ s ∈ ball s₀ (1 : ℝ), ∀ v, ‖radialdA c f s v‖ ≤ K * (1 + |v|) ^ (-(2 : ℝ)) := by
    intro s hs v
    have := radialdA_norm_le (v := v) hc hf hε le_rfl (hsS s hs) hS
    calc _ ≤ _ := this
      _ = _ := by rw [hK]; ring
  have hAb : ∀ v, ‖radialA c f s₀ v‖ ≤ Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * (|s₀| + 1))) *
      (M₀ * (11 / 10)) * (2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ))) := fun v =>
    radialA_norm_le (v := v) hc hf hε le_rfl (by linarith [abs_nonneg s₀]) hS
  have hint : Integrable (fun v : ℝ => K * (1 + |v|) ^ (-(2 : ℝ))) := by
    have := integrable_dom2.const_mul (K / (2 * 200 ^ 5))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only; field_simp
  have hF_int : Integrable (radialA c f s₀) volume := by
    refine Integrable.mono' (integrable_dom.const_mul (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * (|s₀| + 1))) *
      (M₀ * (11 / 10)))) (continuous_radialA (by linarith) hf (hξall s₀ (mem_ball_self one_pos))).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    calc _ ≤ _ := hAb v
      _ = _ := by ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun s v => radialA c f s v)
    (F' := fun s v => radialdA c f s v) (x₀ := s₀) (s := ball s₀ 1) (bound := fun v => K * (1 + |v|) ^ (-(2 : ℝ)))
    (ball_mem_nhds s₀ one_pos)
    (by filter_upwards [ball_mem_nhds s₀ (one_pos : (0 : ℝ) < 1)] with s hs
        exact (continuous_radialA (by linarith) hf (hξall s hs)).aestronglyMeasurable)
    hF_int (continuous_radialdA (by linarith) hf (hξall s₀ (mem_ball_self one_pos))).aestronglyMeasurable
    (Eventually.of_forall fun v s hs => hbound s hs v) hint
    (Eventually.of_forall fun v s hs => hasDerivAt_radialA hc0 (by linarith) f (hξall s hs) v)
  exact this.2

lemma continuousAt_radialdA_s {c : ℝ} (hc : 1 < c) (f : ℝ → ℝ) {s₀ : ℝ} (hξ : 0 < radialXi c s₀) (v : ℝ) :
    ContinuousAt (fun s => radialdA c f s v) s₀ := by
  have hc0 : 0 < c := by linarith
  have hcont : Continuous fun s : ℝ => radialXi c s := by unfold radialXi; fun_prop
  have h1 : ContinuousAt (fun s => radialA c f s v) s₀ := (hasDerivAt_radialA hc0 hc f hξ v).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => ((radialXi c s : ℝ) : ℂ)⁻¹) s₀ := by
    refine ContinuousAt.inv₀ (Complex.continuous_ofReal.continuousAt.comp hcont.continuousAt) ?_
    exact_mod_cast hξ.ne'
  unfold radialdA
  exact (continuousAt_const.mul h2).mul h1

theorem continuousAt_radialXi_deriv {c ε s₀ : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hS : Real.pi ^ 2 * radialEps c ^ 2 * (|s₀| + 1) ≤ 1 / 2) :
    ContinuousAt (fun s => ∫ v : ℝ, radialdA c f s v) s₀ := by
  have hc0 : 0 < c := by linarith
  set M₀ := hankelMass c f with hM₀
  set K : ℝ := 4 * Real.pi ^ 2 * (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * (|s₀| + 1))) *
    (M₀ * (11 / 10)) * (2 * 200 ^ 5)) with hK
  have hsS : ∀ s ∈ ball s₀ (1 : ℝ), |s| ≤ |s₀| + 1 := fun s hs => by
    have := abs_sub_abs_le_abs_sub s s₀
    have h2 : |s - s₀| < 1 := by simpa [Real.dist_eq] using hs
    linarith
  have hξall : ∀ s ∈ ball s₀ (1 : ℝ), 0 < radialXi c s := fun s hs =>
    (radialXi_facts hc0 (hsS s hs) hS).1
  have hint : Integrable (fun v : ℝ => K * (1 + |v|) ^ (-(2 : ℝ))) := by
    have := integrable_dom2.const_mul (K / (2 * 200 ^ 5))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only; field_simp
  refine continuousAt_of_dominated (bound := fun v => K * (1 + |v|) ^ (-(2 : ℝ))) ?_ ?_ hint
    (Eventually.of_forall fun v => continuousAt_radialdA_s (by linarith) f (hξall s₀ (mem_ball_self one_pos)) v)
  · filter_upwards [ball_mem_nhds s₀ (one_pos : (0 : ℝ) < 1)] with s hs
    exact (continuous_radialdA (by linarith) hf (hξall s hs)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds s₀ (one_pos : (0 : ℝ) < 1)] with s hs
    refine Eventually.of_forall fun v => ?_
    have := radialdA_norm_le (v := v) hc hf hε le_rfl (hsS s hs) hS
    calc _ ≤ _ := this
      _ = _ := by rw [hK]; ring

lemma radialdA_tendsto {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ} (hc : Tendsto c atTop atTop) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    ∀ s₀ v : ℝ, Tendsto (fun p : ℕ × ℝ => radialdA (c p.1) (f p.1) p.2 v)
      (atTop ×ˢ 𝓝 s₀) (𝓝 (radialdAlim W s₀ v)) := by
  have hεc : Tendsto (fun k => radialEps (c k)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  intro s₀ v
  have hs' : Tendsto (fun p : ℕ × ℝ => p.2) (atTop ×ˢ 𝓝 s₀) (𝓝 s₀) := tendsto_snd
  have he : Tendsto (fun p : ℕ × ℝ => radialEps (c p.1)) (atTop ×ˢ 𝓝 s₀) (𝓝 0) := hεc.comp tendsto_fst
  have hξ : Tendsto (fun p : ℕ × ℝ => radialXi (c p.1) p.2) (atTop ×ˢ 𝓝 s₀) (𝓝 (1 / Real.pi ^ 2)) := by
    have := (he.pow 2).mul hs'
    have h2 : Tendsto (fun p : ℕ × ℝ => 1 / Real.pi ^ 2 + radialEps (c p.1) ^ 2 * p.2)
        (atTop ×ˢ 𝓝 s₀) (𝓝 (1 / Real.pi ^ 2 + 0 ^ 2 * s₀)) := tendsto_const_nhds.add this
    simpa [radialXi] using h2
  have hm : Tendsto (fun p : ℕ × ℝ => (1 + (v : ℂ) * Complex.I - ((radialEps (c p.1) ^ 2 : ℝ) : ℂ)) *
      ((radialXi (c p.1) p.2 : ℝ) : ℂ)⁻¹) (atTop ×ˢ 𝓝 s₀)
      (𝓝 ((1 + (v : ℂ) * Complex.I - ((0 ^ 2 : ℝ) : ℂ)) * (((1 / Real.pi ^ 2 : ℝ) : ℂ))⁻¹)) := by
    have h1 : Tendsto (fun p : ℕ × ℝ => ((radialEps (c p.1) ^ 2 : ℝ) : ℂ)) (atTop ×ˢ 𝓝 s₀)
        (𝓝 ((0 ^ 2 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp (he.pow 2)
    have h2 : Tendsto (fun p : ℕ × ℝ => ((radialXi (c p.1) p.2 : ℝ) : ℂ)) (atTop ×ˢ 𝓝 s₀)
        (𝓝 (((1 / Real.pi ^ 2 : ℝ)) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp hξ
    refine (tendsto_const_nhds.sub h1).mul (h2.inv₀ ?_)
    have : (1 / Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hlim := (hm.mul (radialA_tendsto hc hW s₀ v))
  have hval : (1 + (v : ℂ) * Complex.I - ((0 ^ 2 : ℝ) : ℂ)) * (((1 / Real.pi ^ 2 : ℝ) : ℂ))⁻¹ *
      radialAlim W s₀ v = radialdAlim W s₀ v := by
    unfold radialdAlim
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    ring
  rw [hval] at hlim
  exact hlim

set_option maxHeartbeats 1000000 in
theorem radial_deriv_limit {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ} {M₀ : ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    TendstoLocallyUniformly (fun k s => ∫ v : ℝ, radialdA (c k) (f k) s v)
      (fun s => ∫ v : ℝ, radialdAlim W s v) atTop := by
  have hpi := Real.pi_pos
  have hεc : Tendsto (fun k => radialEps (c k)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  have hev : ∀ S : ℝ, ∃ N : ℕ, ∀ k ≥ N, 1000 ≤ c k ∧ Real.pi ^ 2 * radialEps (c k) ^ 2 * S ≤ 1 / 2 := by
    intro S
    have h1 := hc.eventually_ge_atTop 1000
    have h2 : Tendsto (fun k => Real.pi ^ 2 * radialEps (c k) ^ 2 * S) atTop (𝓝 0) := by
      simpa using ((hεc.pow 2).const_mul (Real.pi ^ 2)).mul_const S
    have h3 := h2.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    exact eventually_atTop.mp (h1.and h3)
  set Bd : ℝ → ℝ → ℝ := fun S v => 4 * Real.pi ^ 2 *
    (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
      (2 * 200 ^ 5 * (1 + |v|) ^ (-(2 : ℝ)))) with hBd
  have hBdi : ∀ S, Integrable (Bd S) := fun S =>
    (integrable_dom2.const_mul (4 * Real.pi ^ 2 * (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) *
      (M₀ * (11 / 10))))).congr (Eventually.of_forall fun v => by simp only [hBd]; ring)
  have hAb : ∀ S : ℝ, ∃ N : ℕ, ∀ k ≥ N, ∀ s, |s| ≤ S → ∀ v, ‖radialdA (c k) (f k) s v‖ ≤ Bd S v := by
    intro S
    obtain ⟨N, hN⟩ := hev S
    exact ⟨N, fun k hk s hs v => radialdA_norm_le (hN k hk).1 (hf k) hε (hM k) hs (hN k hk).2⟩
  have hlim := radialdA_tendsto (f := f) hc hW
  refine tendstoLocallyUniformly_integral (F := fun k s v => radialdA (c k) (f k) s v) (Flim := radialdAlim W) ?_ ?_ hlim ?_
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
    exact (continuous_radialdA (by linarith [(hN y.1 hy.1).1] : 3 / 2 < c y.1) (hf y.1) hξ).aestronglyMeasurable
  · intro s₀
    obtain ⟨N, hN⟩ := hAb (|s₀| + 1)
    refine ⟨Bd (|s₀| + 1), hBdi _, N, 1, one_pos, fun k hk s hs v => hN k hk s ?_ v⟩
    have := abs_sub_abs_le_abs_sub s s₀; linarith
  · refine continuous_integral_lim (F := fun k s v => radialdA (c k) (f k) s v) (Flim := radialdAlim W) ?_ ?_ hlim ?_
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
      exact (continuous_radialdA (by linarith [(hN y.1 hy.1).1] : 3 / 2 < c y.1) (hf y.1) hξ).aestronglyMeasurable
    · intro s₀
      obtain ⟨N, hN⟩ := hAb (|s₀| + 1)
      refine ⟨Bd (|s₀| + 1), hBdi _, N, 1, one_pos, fun k hk s hs v => hN k hk s ?_ v⟩
      have := abs_sub_abs_le_abs_sub s s₀; linarith
    · intro v
      unfold radialdAlim radialAlim radialKlim
      fun_prop

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_radialXi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_radialXi

/-- info: 'FormalResearch.SignUncertainty.continuousAt_radialXi_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousAt_radialXi_deriv

/-- info: 'FormalResearch.SignUncertainty.radial_deriv_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radial_deriv_limit

end FormalResearch.SignUncertainty

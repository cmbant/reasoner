module

public import FormalResearch.SignUncertainty.RadialDerivLimit
public import FormalResearch.SignUncertainty.RadialAiryBound
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# The window profiles as real parts of `Ξ_c` (`lem:radial-compactness`, Step 4)

On a window `|u| ≤ R`, `Ψ_{f,c}(u) = β₁⁻¹ Re Ξ_c(-u/β₁)` once `π² ε_c² R/β₁ ≤ 1/2`
(`profile_eq_tilde`), and `Ξ_{c_k} → Ξ_W` locally uniformly in `s`, so
`Ψ_{f_k,c_k} → Re F` locally uniformly in `u`, `F = radialF W` (`profile_tlu`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma tlu_congr_eventually {α γ : Type*} [TopologicalSpace α] [PseudoMetricSpace γ]
    {F G : ℕ → α → γ} {g : α → γ} (h : TendstoLocallyUniformly F g atTop)
    (heq : ∀ x, ∃ t ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ t, G k y = F k y) :
    TendstoLocallyUniformly G g atTop := by
  rw [Metric.tendstoLocallyUniformly_iff] at h ⊢
  intro ε hε x
  obtain ⟨t, ht, hk⟩ := h ε hε x
  obtain ⟨t', ht', hk'⟩ := heq x
  refine ⟨t ∩ t', inter_mem ht ht', ?_⟩
  filter_upwards [hk, hk'] with k h1 h2 y hy
  rw [h2 y hy.2]; exact h1 y hy.1

lemma eventually_good {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) (S : ℝ) :
    ∀ᶠ k in atTop, 1000 ≤ c k ∧ Real.pi ^ 2 * radialEps (c k) ^ 2 * S ≤ 1 / 2 := by
  have hεc : Tendsto (fun k => radialEps (c k)) atTop (𝓝 0) := radialEps_tendsto.comp hc
  have h1 := hc.eventually_ge_atTop 1000
  have h2 : Tendsto (fun k => Real.pi ^ 2 * radialEps (c k) ^ 2 * S) atTop (𝓝 0) := by
    simpa using ((hεc.pow 2).const_mul (Real.pi ^ 2)).mul_const S
  exact h1.and (h2.eventually (Iic_mem_nhds (by norm_num)))

lemma c_mul_radialEps_sq {c : ℝ} (hc : 0 < c) : c * radialEps c ^ 2 = c ^ (1 / 3 : ℝ) := by
  have h1 := rpow_third_mul_radialEps hc
  have h3 := radialEps_cube hc
  have he := radialEps_pos hc
  have : c * radialEps c ^ 2 * radialEps c = 1 := by rw [← h3]; ring
  exact mul_right_cancel₀ he.ne' (this.trans h1.symm)

lemma c_mul_radialXi {c : ℝ} (hc : 0 < c) (s : ℝ) :
    c * radialXi c s = c / Real.pi ^ 2 + c ^ (1 / 3 : ℝ) * s := by
  have h := c_mul_radialEps_sq hc
  unfold radialXi
  calc c * (1 / Real.pi ^ 2 + radialEps c ^ 2 * s) = c / Real.pi ^ 2 + (c * radialEps c ^ 2) * s := by ring
    _ = _ := by rw [h]

/-- The real number `c^{1/3} ρ₀(cξ) f(cξ)`, `ξ = ξ_c(s)`. -/
noncomputable def radialXr (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  c ^ (1 / 3 : ℝ) * (hankelRho0 c (c * radialXi c s) * f (c * radialXi c s))

/-- `Ψ̃_{f,c}(u) = β₁⁻¹ Re Ξ_c(-u/β₁)`. -/
noncomputable def profTilde (c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  hankelBeta1⁻¹ * (∫ v : ℝ, radialA c f (-u / hankelBeta1) v).re

lemma integral_radialA_eq {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {s : ℝ} (hξ : 0 < radialXi c s) :
    ∫ v : ℝ, radialA c f s v = ((radialXr c f s : ℝ) : ℂ) := by
  have h := radial_xi_repr hc hf hε hξ
  unfold radialA
  rw [integral_const_mul]
  exact h.symm

lemma profile_eq_tilde {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {u : ℝ} (hξ : 0 < radialXi c (-u / hankelBeta1)) :
    hankelWindowProfile c f u = profTilde c f u := by
  have hc0 : 0 < c := by linarith
  have hΔ : c / Real.pi ^ 2 - u / hankelBeta1 * c ^ (1 / 3 : ℝ) = c * radialXi c (-u / hankelBeta1) := by
    rw [c_mul_radialXi hc0]; ring
  unfold profTilde
  rw [integral_radialA_eq hc hf hε hξ, Complex.ofReal_re]
  unfold hankelWindowProfile radialXr
  dsimp only
  rw [hΔ, if_pos (mul_pos hc0 hξ)]
  ring

lemma window_xi_pos {c R u : ℝ} (hc : 0 < c) (hu : |u| ≤ R)
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * (R / hankelBeta1) ≤ 1 / 2) :
    0 < radialXi c (-u / hankelBeta1) := by
  have hβ := hankelBeta1_pos
  refine (radialXi_facts hc (S := R / hankelBeta1) ?_ hS).1
  rw [abs_div, abs_neg, abs_of_pos hβ]
  gcongr

lemma profTilde_tlu {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    TendstoLocallyUniformly (fun k u => profTilde (c k) (f k) u)
      (fun u : ℝ => hankelBeta1⁻¹ * (XiL W ((-u / hankelBeta1 : ℝ) : ℂ)).re) atTop := by
  have h1 := radial_value_limit hε hc hf hM hW
  have h2 := (Complex.reCLM.uniformContinuous).comp_tendstoLocallyUniformly h1
  have h3 := h2.comp (fun u : ℝ => -u / hankelBeta1) (by fun_prop)
  have hu : UniformContinuous (fun x : ℝ => hankelBeta1⁻¹ * x) :=
    ((ContinuousLinearMap.mul ℝ ℝ) hankelBeta1⁻¹).uniformContinuous
  have h4 := hu.comp_tendstoLocallyUniformly h3
  convert h4 using 1
  · funext k u
    simp [profTilde, Function.comp]
  · funext u
    simp only [Function.comp]
    rw [XiL_ofReal]
    rfl

end FormalResearch.SignUncertainty

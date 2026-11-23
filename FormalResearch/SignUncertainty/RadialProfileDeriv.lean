module

public import FormalResearch.SignUncertainty.RadialProfileValue

/-!
# Derivatives of the window profiles (`lem:radial-compactness`, Step 4)

`Ξ_W` is the locally uniform limit of `Ξ_{c_k}` and `Ξ'_{c_k} → ∫ radialdAlim W`, hence
`(Ξ_W)'(s) = ∫ radialdAlim W s v dv` (`hasDerivAt_XiL_real`); the profile derivatives
`Ψ̃'_k(u) = -β₁⁻² Re ∫ radialdA` converge locally uniformly (`profTildeD_tlu`) and are continuous
(`continuousAt_profTildeD`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

theorem hasDerivAt_XiL_real {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => XiL W (s : ℂ)) (∫ v : ℝ, radialdAlim W s₀ v) s₀ := by
  have h1 := radial_value_limit hε hc hf hM hW
  have h2 := radial_deriv_limit hε hc hf hM hW
  have hev := eventually_good hc (|s₀| + 1 + 1)
  have key : HasDerivAt (fun s : ℝ => ∫ v : ℝ, radialAlim W s v) (∫ v : ℝ, radialdAlim W s₀ v) s₀ := by
    refine hasDerivAt_of_tendstoLocallyUniformlyOn (s := Ioo (-(|s₀| + 1)) (|s₀| + 1))
      (f := fun k s => ∫ v : ℝ, radialA (c k) (f k) s v)
      (f' := fun k s => ∫ v : ℝ, radialdA (c k) (f k) s v)
      (g := fun s => ∫ v : ℝ, radialAlim W s v) (g' := fun s => ∫ v : ℝ, radialdAlim W s v)
      isOpen_Ioo (h2.tendstoLocallyUniformlyOn) ?_ ?_ ?_
    · filter_upwards [hev] with k hk x hx
      refine hasDerivAt_radialXi hk.1 (hf k) hε ?_
      have hx' : |x| ≤ |s₀| + 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
      have : Real.pi ^ 2 * radialEps (c k) ^ 2 * (|x| + 1) ≤
          Real.pi ^ 2 * radialEps (c k) ^ 2 * (|s₀| + 1 + 1) := by gcongr
      linarith [hk.2]
    · intro x _
      exact (h1.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ x)
    · exact abs_lt.mp (lt_add_one |s₀|)
  have e : (fun s : ℝ => XiL W (s : ℂ)) = fun s : ℝ => ∫ v : ℝ, radialAlim W s v :=
    funext fun s => XiL_ofReal W s
  rw [e]; exact key

lemma hasDerivAt_neg_div (u : ℝ) : HasDerivAt (fun u : ℝ => -u / hankelBeta1) (-(1 / hankelBeta1)) u := by
  have := ((hasDerivAt_id u).neg).div_const hankelBeta1
  simpa [neg_div] using this

/-- `-β₁⁻² Re ∫ radialdA`: the derivative of `profTilde`. -/
noncomputable def profTildeD (c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  -(hankelBeta1⁻¹ * hankelBeta1⁻¹) * (∫ v : ℝ, radialdA c f (-u / hankelBeta1) v).re

theorem hasDerivAt_profTilde {c ε : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {u : ℝ}
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * (|-u / hankelBeta1| + 1) ≤ 1 / 2) :
    HasDerivAt (fun u => profTilde c f u) (profTildeD c f u) u := by
  have h1 := hasDerivAt_radialXi hc hf hε hS
  have h2 := h1.scomp u (hasDerivAt_neg_div u)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h2
  have h4 := h3.const_mul hankelBeta1⁻¹
  refine h4.congr_deriv ?_
  rw [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul]
  unfold profTildeD
  ring

theorem profTildeD_tlu {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) :
    TendstoLocallyUniformly (fun k u => profTildeD (c k) (f k) u)
      (fun u : ℝ => -(hankelBeta1⁻¹ * hankelBeta1⁻¹) * (∫ v : ℝ, radialdAlim W (-u / hankelBeta1) v).re)
      atTop := by
  have h1 := radial_deriv_limit hε hc hf hM hW
  have h2 := (Complex.reCLM.uniformContinuous).comp_tendstoLocallyUniformly h1
  have h3 := h2.comp (fun u : ℝ => -u / hankelBeta1) (by fun_prop)
  have hu : UniformContinuous (fun x : ℝ => -(hankelBeta1⁻¹ * hankelBeta1⁻¹) * x) :=
    ((ContinuousLinearMap.mul ℝ ℝ) (-(hankelBeta1⁻¹ * hankelBeta1⁻¹))).uniformContinuous
  exact hu.comp_tendstoLocallyUniformly h3

theorem continuousAt_profTildeD {c ε : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {u : ℝ}
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * (|-u / hankelBeta1| + 1) ≤ 1 / 2) :
    ContinuousAt (profTildeD c f) u := by
  have h1 := continuousAt_radialXi_deriv hc hf hε hS
  have hg : ContinuousAt (fun u : ℝ => -u / hankelBeta1) u := by fun_prop
  have h2 : ContinuousAt (fun u : ℝ => ∫ v : ℝ, radialdA c f (-u / hankelBeta1) v) u :=
    ContinuousAt.comp (g := fun s => ∫ v : ℝ, radialdA c f s v) (x := u) h1 hg
  have h3 : ContinuousAt (fun u : ℝ => (∫ v : ℝ, radialdA c f (-u / hankelBeta1) v).re) u :=
    Complex.continuous_re.continuousAt.comp h2
  exact continuousAt_const.mul h3

theorem hasDerivAt_phi {ε M₀ : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    (hc : Tendsto c atTop atTop) (hf : ∀ k, IsHankelEigenfn (c k) ε (f k))
    (hM : ∀ k, hankelMass (c k) (f k) ≤ M₀) {W : ℂ → ℂ}
    (hW : ∀ w : ℂ, 0 < w.re → Tendsto (fun k => radialW (c k) (f k) w) atTop (𝓝 (W w))) (u : ℝ) :
    HasDerivAt (fun u : ℝ => hankelBeta1⁻¹ * (XiL W ((-u / hankelBeta1 : ℝ) : ℂ)).re)
      (-(hankelBeta1⁻¹ * hankelBeta1⁻¹) * (∫ v : ℝ, radialdAlim W (-u / hankelBeta1) v).re) u := by
  have h1 := hasDerivAt_XiL_real hε hc hf hM hW (-u / hankelBeta1)
  have h2 := h1.scomp u (hasDerivAt_neg_div u)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h2
  have h4 := h3.const_mul hankelBeta1⁻¹
  refine h4.congr_deriv ?_
  rw [Complex.reCLM_apply, Complex.smul_re, smul_eq_mul]
  ring

end FormalResearch.SignUncertainty

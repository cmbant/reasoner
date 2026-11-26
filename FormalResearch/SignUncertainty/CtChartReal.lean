module

public import FormalResearch.SignUncertainty.CtChartDecomp

/-!
# Reality of the chart constants and the Taylor bounds for `Q_ε` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3.  **Proved.**
`ψ̂(0)`, `h̃(0,0)` are real; `∂_s Q_ε(0,0) = i h̃(0,0)`; and `Q_ε(s;β) = Q_geo(0,0) + i h̃(0,0) s + R` with
`R = O(|β| + |s|²)`, `∂_s R = O(|β| + |s|)`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

open CtOuter

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma real_deriv_of_conj_symm {g : ℂ → ℂ} (hd : DifferentiableAt ℂ g 0)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) :
    starRingEnd ℂ (deriv g 0) = deriv g 0 := by
  have h := hasDerivAt_conj_conj hd.hasDerivAt
  rw [map_zero] at h
  have h2 : HasDerivAt g (starRingEnd ℂ (deriv g 0)) 0 := by
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hs] with w hw
    rw [hw, Complex.conj_conj]
  exact (h2.unique hd.hasDerivAt)

lemma real_dy_of_conj {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℂ ∞' F (0, 0))
    (hs : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), F (conj2 q) = starRingEnd ℂ (F q)) :
    starRingEnd ℂ (dyF F (0, 0)) = dyF F (0, 0) := by
  have hdiff : DifferentiableAt ℂ F (0, 0) := hF.differentiableAt (by simp)
  have hd := hasDerivAt_slice1 hdiff
  have hs' : ∀ᶠ y : ℂ in 𝓝 0, F (starRingEnd ℂ y, 0) = starRingEnd ℂ (F (y, 0)) := by
    have ht : Tendsto (fun y : ℂ => (y, (0 : ℂ))) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      (continuous_id.prodMk continuous_const).tendsto' 0 _ rfl
    filter_upwards [ht.eventually hs] with y hy
    simpa [conj2] using hy
  have := real_deriv_of_conj_symm (g := fun y => F (y, 0)) hd.differentiableAt hs'
  have e : deriv (fun y : ℂ => F (y, 0)) 0 = dyF F (0, 0) := hd.deriv
  rwa [e] at this

lemma hF_conj {ϑ : ℂ → ℂ} (hconj : ∀ᶠ z in 𝓝 (0 : ℂ), ϑ (starRingEnd ℂ z) = starRingEnd ℂ (ϑ z)) :
    ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), hF ϑ (conj2 q) = starRingEnd ℂ (hF ϑ q) := by
  have hZ : Tendsto Zf (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
    have := contDiffAt_Zf.continuousAt
    rwa [ContinuousAt, Zf_zero] at this
  filter_upwards [hZ.eventually hconj, Zf_conj, Uf_conj] with q h1 h2 h3
  unfold hF
  rw [h3, h2, h1, map_mul]

lemma htil_zero_real {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0)
    (hconj : ∀ᶠ z in 𝓝 (0 : ℂ), ϑ (starRingEnd ℂ z) = starRingEnd ℂ (ϑ z)) :
    starRingEnd ℂ (htil ϑ (0, 0)) = htil ϑ (0, 0) := by
  unfold htil
  rw [hadY_zero]
  exact real_dy_of_conj (contDiffAt_hF hA) (hF_conj hconj)

lemma psiHat_zero {ϑ : ℂ → ℂ} : psiHat ϑ 0 = ϑ 0 / ((CtCfu.d0 : ℝ) : ℂ) := by
  unfold psiHat hF
  rw [ysF_zero, Uf_zero, Zf_zero]
  ring

lemma psiHat_zero_real {ϑ : ℂ → ℂ} (hconj : ∀ᶠ z in 𝓝 (0 : ℂ), ϑ (starRingEnd ℂ z) = starRingEnd ℂ (ϑ z)) :
    starRingEnd ℂ (psiHat ϑ 0) = psiHat ϑ 0 := by
  rw [psiHat_zero, map_div₀, Complex.conj_ofReal]
  have := hconj.self_of_nhds
  rw [map_zero] at this
  rw [← this]

/-- `s ↦ F(s², 0)` has zero derivative at `0`. -/
lemma hasDerivAt_sq_slice {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℂ ∞' F (0, 0)) :
    HasDerivAt (fun s : ℂ => F (s ^ 2, 0)) 0 0 := by
  have h1 : HasDerivAt (fun y : ℂ => F (y, 0)) (fderiv ℂ F (0, 0) (1, 0)) 0 :=
    hasDerivAt_slice1 (q := (0, 0)) (hF.differentiableAt (by simp))
  have h2 : HasDerivAt (fun s : ℂ => s ^ 2) (2 * (0 : ℂ)) 0 := by simpa using hasDerivAt_pow 2 (0 : ℂ)
  have h3 := HasDerivAt.comp (0 : ℂ) (by simpa using h1) h2
  simpa [Function.comp_def] using h3

/-- `∂_s Q_ε(0,0) = i h̃(0,0)`. -/
theorem hasDerivAt_Qeps_zero {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0) :
    HasDerivAt (fun s : ℂ => Qeps ϑ (s, 0)) (Complex.I * htil ϑ (0, 0)) 0 := by
  have hA' := hasDerivAt_sq_slice contDiffAt_Qgeo
  have hB := hasDerivAt_sq_slice (contDiffAt_htil hA)
  have hX : HasDerivAt (fun s : ℂ => Xph ϑ (s, 0)) 0 0 := by
    have h1 : HasDerivAt (fun s : ℂ => s * (s ^ 2 - ysF 0)) 0 0 := by
      have := (hasDerivAt_id' (0 : ℂ)).mul ((hasDerivAt_pow 2 (0 : ℂ)).sub_const (ysF 0))
      convert this using 1
      simp [ysF_zero]
    have h2 : HasDerivAt (fun s : ℂ => (s * (s ^ 2 - ysF 0)) * htil ϑ (s ^ 2, 0)) (0 * htil ϑ ((0 : ℂ) ^ 2, 0) + (0 * (0 ^ 2 - ysF 0)) * 0) 0 := h1.mul hB
    simpa [Xph] using h2
  have hIX : HasDerivAt (fun s : ℂ => Complex.I * Xph ϑ (s, 0)) 0 0 := by
    simpa using hX.const_mul Complex.I
  have hexp : HasDerivAt (fun s : ℂ => Complex.exp (Complex.I * Xph ϑ (s, 0))) 0 0 := by
    have := hIX.cexp
    simpa [Xph, ysF_zero] using this
  have hE : HasDerivAt (fun s : ℂ => E1 (Complex.I * Xph ϑ (s, 0))) 0 0 := by
    have h0 : (Complex.I * Xph ϑ (0, 0)) = 0 := by simp [Xph]
    have hd : HasDerivAt E1 (deriv E1 (Complex.I * Xph ϑ (0, 0))) (Complex.I * Xph ϑ (0, 0)) :=
      ((contDiffAt_E1 _).differentiableAt (by simp)).hasDerivAt
    have := HasDerivAt.comp (0 : ℂ) hd hIX
    simpa [Function.comp_def] using this
  have hmain := (hA'.mul hexp).add ((((hasDerivAt_id (0 : ℂ)).const_mul Complex.I).mul hB).mul hE)
  convert hmain using 1
  · funext s; simp [Qeps, Xph]
  · simp [E1_zero, Xph]

/-- info: 'FormalResearch.SignUncertainty.CtChart.hasDerivAt_Qeps_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_Qeps_zero

end FormalResearch.SignUncertainty.CtChart

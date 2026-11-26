module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic

/-!
# A parametric scalar implicit function theorem over `ℂ`

Support for the CFU chart of `ct:cfu` (`constant_terms_lower.tex`, Step 2/3): `scalar_ift`.  **Proved.**

If `g(x, q)` is `C^∞` over `ℂ` near `(x₀, q₀)` (`q ∈ ℂ × ℂ` a parameter), `g(x₀, q₀) = 0` and `∂_x g(x₀, q₀) ≠ 0`, there is a
`C^∞` solution `x = ξ(q)` near `q₀`, unique in a neighbourhood of `x₀`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **Parametric scalar implicit function theorem over `ℂ`.** -/
theorem scalar_ift {g : ℂ × (ℂ × ℂ) → ℂ} {x0 : ℂ} {q0 : ℂ × ℂ} {g1 : ℂ}
    (hg : ContDiffAt ℂ ∞' g (x0, q0)) (h0 : g (x0, q0) = 0)
    (hd : HasDerivAt (fun x : ℂ => g (x, q0)) g1 x0) (hg1 : g1 ≠ 0) :
    ∃ ξ : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' ξ q0 ∧ ξ q0 = x0 ∧ (∀ᶠ q in 𝓝 q0, g (ξ q, q) = 0) ∧
      ∃ U ∈ 𝓝 x0, ∃ V ∈ 𝓝 q0, ∀ q ∈ V, ∀ x ∈ U, g (x, q) = 0 → x = ξ q := by
  classical
  set f : ℂ × (ℂ × ℂ) → ℂ × (ℂ × ℂ) := fun p => (g p, p.2) with hf
  have hgd : DifferentiableAt ℂ g (x0, q0) := hg.differentiableAt (by simp)
  set g' : ℂ × (ℂ × ℂ) →L[ℂ] ℂ := fderiv ℂ g (x0, q0) with hg'
  have hg'x : g' (1, 0) = g1 := by
    have h1 : HasDerivAt (fun x : ℂ => (x, q0)) ((1 : ℂ), (0 : ℂ × ℂ)) x0 :=
      (hasDerivAt_id x0).prodMk (hasDerivAt_const x0 q0)
    have h2 := hgd.hasFDerivAt.comp_hasDerivAt x0 h1
    exact h2.unique hd
  have hlin : ∀ v : ℂ × (ℂ × ℂ), g' v = g1 * v.1 + g' (0, v.2) := by
    intro v
    have : v = v.1 • ((1 : ℂ), (0 : ℂ × ℂ)) + ((0 : ℂ), v.2) := by ext <;> simp
    conv_lhs => rw [this, map_add, map_smul, hg'x]
    simp [mul_comm]
  let f' : ℂ × (ℂ × ℂ) →L[ℂ] ℂ × (ℂ × ℂ) :=
    g'.prod (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  let finv : ℂ × (ℂ × ℂ) →L[ℂ] ℂ × (ℂ × ℂ) :=
    (g1⁻¹ • ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)) -
      (g'.comp ((ContinuousLinearMap.inr ℂ ℂ (ℂ × ℂ)).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)))))).prod
      (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  have hl : ∀ v, finv (f' v) = v := by
    intro v
    simp only [finv, f', ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
    refine Prod.ext ?_ rfl
    show g1⁻¹ • (g' v - g' (0, v.2)) = v.1
    rw [hlin v]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hr : ∀ w, f' (finv w) = w := by
    intro w
    simp only [finv, f', ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
    refine Prod.ext ?_ rfl
    show g' ((g1⁻¹ • (w.1 - g' (0, w.2)), w.2)) = w.1
    rw [hlin]
    simp only [smul_eq_mul]
    field_simp
    ring
  let e := ContinuousLinearEquiv.equivOfInverse f' finv hl hr
  have hfd : HasFDerivAt f (e : _ →L[ℂ] _) (x0, q0) := by
    have : (e : _ →L[ℂ] _) = f' := rfl
    rw [this]
    exact hgd.hasFDerivAt.prodMk (hasFDerivAt_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ × ℂ))
  have hfc : ContDiffAt ℂ ∞' f (x0, q0) := hg.prodMk contDiffAt_snd
  have hn : (∞' : WithTop ℕ∞) ≠ 0 := by simp
  set P := hfc.toOpenPartialHomeomorph f hfd hn with hP
  have hsrc : (x0, q0) ∈ P.source := hfc.mem_toOpenPartialHomeomorph_source hfd hn
  have hfq0 : f (x0, q0) = (0, q0) := by simp [hf, h0]
  set ξ : ℂ × ℂ → ℂ := fun q => (hfc.localInverse hfd hn (0, q)).1 with hξ
  have hli : ContDiffAt ℂ ∞' (hfc.localInverse hfd hn) (0, q0) := by
    have := hfc.to_localInverse hfd hn
    rwa [hfq0] at this
  have hξq0 : ξ q0 = x0 := by
    have := hfc.localInverse_apply_image hfd hn
    rw [hfq0] at this
    simp [hξ, this]
  have hξc : ContDiffAt ℂ ∞' ξ q0 :=
    contDiffAt_fst.comp q0 (hli.comp q0 (contDiffAt_const.prodMk contDiffAt_id))
  have hsd : HasStrictFDerivAt f (e : _ →L[ℂ] _) (x0, q0) :=
    hfc.hasStrictFDerivAt hfd hn
  have hrinv : ∀ᶠ w in 𝓝 (0, q0), f (hfc.localInverse hfd hn w) = w := by
    have := hsd.eventually_right_inverse
    rwa [hfq0] at this
  have hev : ∀ᶠ q in 𝓝 q0, g (ξ q, q) = 0 := by
    have h1 : Tendsto (fun q : ℂ × ℂ => ((0 : ℂ), q)) (𝓝 q0) (𝓝 (0, q0)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [h1.eventually hrinv] with q hq
    have h2 := congrArg Prod.fst hq
    have h3 := congrArg Prod.snd hq
    simp only [hf] at h2 h3
    have h5 : (hfc.localInverse hfd hn (0, q)).2 = q := h3
    simp only [hξ]
    have h6 : g ((hfc.localInverse hfd hn (0, q)).1, (hfc.localInverse hfd hn (0, q)).2) = 0 := h2
    rwa [h5] at h6
  refine ⟨ξ, hξc, hξq0, hev, ?_⟩
  -- uniqueness
  have hSopen : P.source ∈ 𝓝 (x0, q0) := P.open_source.mem_nhds hsrc
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hSopen
  have hcc : ContinuousAt (fun q : ℂ × ℂ => (ξ q, q)) q0 := hξc.continuousAt.prodMk continuousAt_id
  have hcont : ∀ᶠ q in 𝓝 q0, (ξ q, q) ∈ P.source := by
    refine hcc.eventually_mem ?_
    have : (ξ q0, q0) = (x0, q0) := by rw [hξq0]
    rw [this]; exact hSopen
  have hVV : ∀ᶠ q in 𝓝 q0, q ∈ V := hV
  refine ⟨U, hU, {q | q ∈ V ∧ (ξ q, q) ∈ P.source ∧ g (ξ q, q) = 0}, ?_, ?_⟩
  · exact (hVV.and (hcont.and hev))
  · rintro q ⟨hqV, hqs, hqg⟩ x hxU hxg
    have hxs : (x, q) ∈ P.source := hUV ⟨hxU, hqV⟩
    have h1 : P (x, q) = P (ξ q, q) := by
      show f (x, q) = f (ξ q, q)
      simp only [hf, hxg, hqg]
    have := P.injOn hxs hqs h1
    exact (Prod.ext_iff.mp this).1

/-- Complex conjugation on a pair. -/
def conj2 (q : ℂ × ℂ) : ℂ × ℂ := (starRingEnd ℂ q.1, starRingEnd ℂ q.2)

lemma continuous_conj2 : Continuous conj2 :=
  ((Complex.continuous_conj.comp continuous_fst).prodMk (Complex.continuous_conj.comp continuous_snd))

/-- **`scalar_ift` with conjugation symmetry.**  If moreover `g(x̄, q̄) = conj g(x, q)` near `(x₀, q₀)` and `x₀`, `q₀` are real, the solution is
conjugation symmetric: `ξ(q̄) = conj ξ(q)` near `q₀` (so real for real `q`). -/
theorem scalar_ift_conj {g : ℂ × (ℂ × ℂ) → ℂ} {x0 : ℂ} {q0 : ℂ × ℂ} {g1 : ℂ}
    (hg : ContDiffAt ℂ ∞' g (x0, q0)) (h0 : g (x0, q0) = 0)
    (hd : HasDerivAt (fun x : ℂ => g (x, q0)) g1 x0) (hg1 : g1 ≠ 0)
    (hx0 : starRingEnd ℂ x0 = x0) (hq0 : conj2 q0 = q0)
    (hsym : ∀ᶠ p in 𝓝 (x0, q0), g (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (g p)) :
    ∃ ξ : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' ξ q0 ∧ ξ q0 = x0 ∧ (∀ᶠ q in 𝓝 q0, g (ξ q, q) = 0) ∧
      (∃ U ∈ 𝓝 x0, ∃ V ∈ 𝓝 q0, ∀ q ∈ V, ∀ x ∈ U, g (x, q) = 0 → x = ξ q) ∧
      ∀ᶠ q in 𝓝 q0, ξ (conj2 q) = starRingEnd ℂ (ξ q) := by
  obtain ⟨ξ, hξc, hξ0, hev, U, hU, V, hV, huniq⟩ := scalar_ift hg h0 hd hg1
  refine ⟨ξ, hξc, hξ0, hev, ⟨U, hU, V, hV, huniq⟩, ?_⟩
  have hc2 : Tendsto conj2 (𝓝 q0) (𝓝 q0) := by
    have := continuous_conj2.tendsto q0
    rwa [hq0] at this
  have hξt : Tendsto ξ (𝓝 q0) (𝓝 x0) := by
    have := hξc.continuousAt.tendsto
    rwa [hξ0] at this
  have hcx : Tendsto (fun q => starRingEnd ℂ (ξ q)) (𝓝 q0) (𝓝 x0) := by
    have := (Complex.continuous_conj.tendsto x0).comp hξt
    rwa [hx0] at this
  have hpt : Tendsto (fun q => (ξ q, q)) (𝓝 q0) (𝓝 (x0, q0)) := by
    have : ContinuousAt (fun q => (ξ q, q)) q0 := hξc.continuousAt.prodMk continuousAt_id
    simpa [hξ0] using this.tendsto
  filter_upwards [hV, hc2.eventually hV, hcx.eventually hU, hev, hpt.eventually hsym] with q hqV hcqV hcxU hq0' hsq
  have h1 : g (starRingEnd ℂ (ξ q), conj2 q) = 0 := by
    have := hsq
    rw [this, hq0', map_zero]
  exact (huniq _ hcqV _ hcxU h1).symm

end FormalResearch.SignUncertainty.CtChart

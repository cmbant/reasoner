/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import FormalResearch.SignUncertainty.FctWarpContraction

/-!
# The coordinates `(û, α̃)` of the zero solve (`fct:warp-asymp` (1), Step 1; `fct:inner-symbols` (b1))

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (b1) and Step 1 of the proof of Proposition `fct:warp-asymp` (1).

This file is the abstract (phase-independent) part: it proves everything of Step 1 that only uses the structure of a perturbed phase
`Φ̃(τ; L, α)` with `∂_L Φ̃ = τ` and a unique nondegenerate positive critical point `τ̃₀(L, α)`.

* `real_scalar_ift`: the parametric scalar implicit function theorem over `ℝ` (the `ℂ` version `CtChart.scalar_ift` is not reused, to keep
  the `CtChart*` chain from being rebuilt).
* `FctPhaseBox Φ Ω τ0` (hypotheses on `Φ̃`): smooth on `(0, ∞) × Ω`, `∂_L Φ̃ = τ`, `τ0` the unique positive critical point, nondegenerate, with
  `Φ̃(τ̃₀) > 0`.  `FctPhaseBox.tau0_contDiffAt`: `τ̃₀` is `C^∞` ("`ã` is smooth because `τ̃₀` is the unique nondegenerate critical point").
* `fctAtil Φ τ0 p = (3/2 · Φ̃(τ̃₀(p), p))^{2/3}` (`ã`), `FctPhaseBox.hasFDerivAt_atil`: the envelope formulas
  `∂_{L₁} ã = τ̃₀/√ã` and `∂_α ã = ∂_αΦ̃(τ̃₀)/√ã`, in particular `∂_{L₁} ã > 0`.
* `fctChart κ λ`: the coordinate map `(L, α) ↦ (û, α̃) = (-κ ã, λ α)` (the paper: `κ = 2^{-2/3} c^{2/3}`, `λ = c^{-2/3}`); `fctChart_injOn`
  (strictly monotone in `L` on a rectangle, hence injective), `fctChart_image_box` (an intermediate-value statement: the image of the
  rectangle contains every target `(û*, α̃*)` that is bracketed in `û` at two `L`-values, which is the paper's "onto a set containing
  `(a₁, 0) + B_r`").
* `fct_zero_transfer`, `fct_warp_zero_chart`: Step 1 feeding Step 4: if `G` (the zero functional) written in the coordinates, `F y = G(Ψ⁻¹(a + y))`,
  satisfies the hypotheses of `exists_unique_zero_of_lipschitz_perturbation`, then `G` has a zero `x*` with `Ψ x* ∈ a + B_ρ`, unique among all
  points of the rectangle with `Ψ x ∈ a + B_r`.

Class: proved; `FctPhaseBox` is a hypothesis structure (the paper's `Φ̃` of `fct:warp-asymp` (1) is not defined in Lean as a function of
`(τ, L, α)`; satisfiability: any `Φ̃ = τ L - Ψ(τ, α)` with `Ψ` smooth, strictly convex in `τ`, e.g. `Ψ = τ²/2`, `τ̃₀ = L`).
-/
@[expose] public section

open Set Filter Topology Metric

namespace FormalResearch.SignUncertainty

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### A parametric scalar implicit function theorem over `ℝ` -/

/-- **Parametric scalar implicit function theorem over `ℝ`** (existence part): if `g(x, q)` is `C^∞` near `(x₀, q₀)`, `g(x₀, q₀) = 0` and
`∂_x g(x₀, q₀) = g₁ ≠ 0`, there is a `C^∞` function `ξ` near `q₀` with `ξ(q₀) = x₀` and `g(ξ(q), q) = 0` for `q` near `q₀`. -/
theorem real_scalar_ift {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {g : ℝ × P → ℝ} {x0 : ℝ} {q0 : P} {g1 : ℝ}
    (hg : ContDiffAt ℝ ∞' g (x0, q0)) (h0 : g (x0, q0) = 0)
    (hd : HasDerivAt (fun x : ℝ => g (x, q0)) g1 x0) (hg1 : g1 ≠ 0) :
    ∃ ξ : P → ℝ, ContDiffAt ℝ ∞' ξ q0 ∧ ξ q0 = x0 ∧ ∀ᶠ q in 𝓝 q0, g (ξ q, q) = 0 := by
  classical
  set f : ℝ × P → ℝ × P := fun p => (g p, p.2) with hf
  have hgd : DifferentiableAt ℝ g (x0, q0) := hg.differentiableAt (by simp)
  set g' : ℝ × P →L[ℝ] ℝ := fderiv ℝ g (x0, q0) with hg'
  have hg'x : g' (1, 0) = g1 := by
    have h1 : HasDerivAt (fun x : ℝ => (x, q0)) ((1 : ℝ), (0 : P)) x0 :=
      (hasDerivAt_id x0).prodMk (hasDerivAt_const x0 q0)
    have h2 := hgd.hasFDerivAt.comp_hasDerivAt x0 h1
    exact h2.unique hd
  have hlin : ∀ v : ℝ × P, g' v = g1 * v.1 + g' (0, v.2) := by
    intro v
    have : v = v.1 • ((1 : ℝ), (0 : P)) + ((0 : ℝ), v.2) := by ext <;> simp
    conv_lhs => rw [this, map_add, map_smul, hg'x]
    simp [mul_comm]
  let f' : ℝ × P →L[ℝ] ℝ × P := g'.prod (ContinuousLinearMap.snd ℝ ℝ P)
  let finv : ℝ × P →L[ℝ] ℝ × P :=
    (g1⁻¹ • ((ContinuousLinearMap.fst ℝ ℝ P) -
      (g'.comp ((ContinuousLinearMap.inr ℝ ℝ P).comp (ContinuousLinearMap.snd ℝ ℝ P))))).prod
      (ContinuousLinearMap.snd ℝ ℝ P)
  have hl : ∀ v, finv (f' v) = v := by
    intro v
    simp only [finv, f', ContinuousLinearMap.prod_apply, smul_apply,
      sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
    refine Prod.ext ?_ rfl
    show g1⁻¹ • (g' v - g' (0, v.2)) = v.1
    rw [hlin v]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hr : ∀ w, f' (finv w) = w := by
    intro w
    simp only [finv, f', ContinuousLinearMap.prod_apply, smul_apply,
      sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inr_apply]
    refine Prod.ext ?_ rfl
    show g' ((g1⁻¹ • (w.1 - g' (0, w.2)), w.2)) = w.1
    rw [hlin]
    simp only [smul_eq_mul]
    field_simp
    ring
  let e := ContinuousLinearEquiv.equivOfInverse f' finv hl hr
  have hfd : HasFDerivAt f (e : _ →L[ℝ] _) (x0, q0) := by
    have : (e : _ →L[ℝ] _) = f' := rfl
    rw [this]
    exact hgd.hasFDerivAt.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := P))
  have hfc : ContDiffAt ℝ ∞' f (x0, q0) := hg.prodMk contDiffAt_snd
  have hn : (∞' : WithTop ℕ∞) ≠ 0 := by simp
  set ξ : P → ℝ := fun q => (hfc.localInverse hfd hn (0, q)).1 with hξ
  have hfq0 : f (x0, q0) = (0, q0) := by simp [hf, h0]
  have hli : ContDiffAt ℝ ∞' (hfc.localInverse hfd hn) (0, q0) := by
    have := hfc.to_localInverse hfd hn
    rwa [hfq0] at this
  have hξq0 : ξ q0 = x0 := by
    have := hfc.localInverse_apply_image hfd hn
    rw [hfq0] at this
    simp [hξ, this]
  have hξc : ContDiffAt ℝ ∞' ξ q0 :=
    contDiffAt_fst.comp q0 (hli.comp q0 (contDiffAt_const.prodMk contDiffAt_id))
  have hsd : HasStrictFDerivAt f (e : _ →L[ℝ] _) (x0, q0) :=
    hfc.hasStrictFDerivAt hfd hn
  have hrinv : ∀ᶠ w in 𝓝 (0, q0), f (hfc.localInverse hfd hn w) = w := by
    have := hsd.eventually_right_inverse
    rwa [hfq0] at this
  have hev : ∀ᶠ q in 𝓝 q0, g (ξ q, q) = 0 := by
    have h1 : Tendsto (fun q : P => ((0 : ℝ), q)) (𝓝 q0) (𝓝 (0, q0)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [h1.eventually hrinv] with q hq
    have h2 := congrArg Prod.fst hq
    have h3 := congrArg Prod.snd hq
    simp only [hf] at h2 h3
    have h5 : (hfc.localInverse hfd hn (0, q)).2 = q := h3
    simp only [hξ]
    have h6 : g ((hfc.localInverse hfd hn (0, q)).1, (hfc.localInverse hfd hn (0, q)).2) = 0 := h2
    rwa [h5] at h6
  exact ⟨ξ, hξc, hξq0, hev⟩


/-! ### The perturbed phase and `ã` -/

/-- `Φ̃(τ; p)` as a function on `ℝ × (ℝ × ℝ)` (`p = (L, α)`). -/
def fctPh (Φ : ℝ → ℝ × ℝ → ℝ) : ℝ × (ℝ × ℝ) → ℝ := fun q => Φ q.1 q.2

/-- `∂_τ Φ̃(τ; p)`. -/
noncomputable def fctPhTau (Φ : ℝ → ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ (fctPh Φ) (τ, p) (1, 0)

/-- `∂_α Φ̃(τ; L, α)`. -/
noncomputable def fctPhAlpha (Φ : ℝ → ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ (fctPh Φ) (τ, p) (0, (0, 1))

/-- **Hypotheses on the perturbed phase** `Φ̃(τ; L, α)` of `fct:warp-asymp` (1) on a parameter set `Ω ∋ p = (L, α)` (an open set, in the paper
`L > c^{-1}θ₁^ε`, `ℓ₁ ≤ 2.6`, `|α| ≤ c^{-1/2}`), with `τ0 = τ̃₀`: `Φ̃` is smooth for `τ > 0`, `∂_L Φ̃ = τ`, `τ̃₀(p) > 0` is the unique positive
critical point of `Φ̃(·; p)`, nondegenerate (`∂_τ²Φ̃ < 0`), with `Φ̃(τ̃₀) > 0` (so `ã = (3/2 Φ̃(τ̃₀))^{2/3}` is defined). -/
structure FctPhaseBox (Φ : ℝ → ℝ × ℝ → ℝ) (Ω : Set (ℝ × ℝ)) (τ0 : ℝ × ℝ → ℝ) : Prop where
  isOpen : IsOpen Ω
  smooth : ContDiffOn ℝ ∞' (fctPh Φ) (Ioi 0 ×ˢ Ω)
  dL : ∀ τ, 0 < τ → ∀ p ∈ Ω, fderiv ℝ (fctPh Φ) (τ, p) (0, (1, 0)) = τ
  pos : ∀ p ∈ Ω, 0 < τ0 p
  crit : ∀ p ∈ Ω, fctPhTau Φ (τ0 p) p = 0
  nondeg : ∀ p ∈ Ω, deriv (fun τ => fctPhTau Φ τ p) (τ0 p) < 0
  unique : ∀ p ∈ Ω, ∀ τ, 0 < τ → fctPhTau Φ τ p = 0 → τ = τ0 p
  val_pos : ∀ p ∈ Ω, 0 < Φ (τ0 p) p

/-- `ã(p) = (3/2 · Φ̃(τ̃₀(p); p))^{2/3}` (`fct:warp-asymp` (1), proof; `fct:inner-symbols` (b1)). -/
noncomputable def fctAtil (Φ : ℝ → ℝ × ℝ → ℝ) (τ0 : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (3 / 2 * Φ (τ0 p) p) ^ (2 / 3 : ℝ)

namespace FctPhaseBox

variable {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}

lemma open_prod (h : FctPhaseBox Φ Ω τ0) : IsOpen (Ioi (0 : ℝ) ×ˢ Ω) := isOpen_Ioi.prod h.isOpen

lemma mem_prod (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) : (τ0 p, p) ∈ Ioi (0 : ℝ) ×ˢ Ω :=
  ⟨h.pos p hp, hp⟩

lemma contDiffAt_ph (h : FctPhaseBox Φ Ω τ0) {τ : ℝ} {p : ℝ × ℝ} (hτ : 0 < τ) (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞' (fctPh Φ) (τ, p) :=
  h.smooth.contDiffAt (h.open_prod.mem_nhds ⟨hτ, hp⟩)

lemma contDiffAt_phTau (h : FctPhaseBox Φ Ω τ0) {τ : ℝ} {p : ℝ × ℝ} (hτ : 0 < τ) (hp : p ∈ Ω) :
    ContDiffAt ℝ ∞' (fun q : ℝ × (ℝ × ℝ) => fctPhTau Φ q.1 q.2) (τ, p) := by
  have h1 : ContDiffOn ℝ ∞' (fun q => fderiv ℝ (fctPh Φ) q) (Ioi (0 : ℝ) ×ˢ Ω) :=
    h.smooth.fderiv_of_isOpen h.open_prod (by simp)
  have h2 : ContDiffAt ℝ ∞' (fun q => fderiv ℝ (fctPh Φ) q) (τ, p) :=
    h1.contDiffAt (h.open_prod.mem_nhds ⟨hτ, hp⟩)
  exact h2.clm_apply contDiffAt_const

/-- **`τ̃₀` is `C^∞`**: the unique nondegenerate positive critical point depends smoothly on `(L, α)` (implicit function theorem). -/
theorem tau0_contDiffAt (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) : ContDiffAt ℝ ∞' τ0 p := by
  set g : ℝ × (ℝ × ℝ) → ℝ := fun q => fctPhTau Φ q.1 q.2 with hg
  have hgc : ContDiffAt ℝ ∞' g (τ0 p, p) := h.contDiffAt_phTau (h.pos p hp) hp
  have hgd : DifferentiableAt ℝ g (τ0 p, p) := hgc.differentiableAt (by simp)
  have hcurve : HasDerivAt (fun x : ℝ => (x, p)) ((1 : ℝ), (0 : ℝ × ℝ)) (τ0 p) :=
    (hasDerivAt_id (τ0 p)).prodMk (hasDerivAt_const (τ0 p) p)
  have hd0 : DifferentiableAt ℝ (fun x : ℝ => g (x, p)) (τ0 p) := by
    have := hgd.hasFDerivAt.comp_hasDerivAt (τ0 p) hcurve
    exact this.differentiableAt
  have hne : deriv (fun x : ℝ => g (x, p)) (τ0 p) ≠ 0 := (h.nondeg p hp).ne
  obtain ⟨ξ, hξc, hξ0, hev⟩ := real_scalar_ift hgc (h.crit p hp) hd0.hasDerivAt hne
  have hξpos : ∀ᶠ q in 𝓝 p, 0 < ξ q := by
    have := hξc.continuousAt.eventually (Ioi_mem_nhds (show (0 : ℝ) < ξ p by rw [hξ0]; exact h.pos p hp))
    exact this
  have hΩ : ∀ᶠ q in 𝓝 p, q ∈ Ω := h.isOpen.mem_nhds hp
  have heq : τ0 =ᶠ[𝓝 p] ξ := by
    filter_upwards [hξpos, hΩ, hev] with q hq1 hq2 hq3
    exact (h.unique q hq2 (ξ q) hq1 hq3).symm
  exact hξc.congr_of_eventuallyEq heq

lemma atil_pos (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) : 0 < fctAtil Φ τ0 p :=
  Real.rpow_pos_of_pos (by linarith [h.val_pos p hp]) _

lemma sqrt_atil (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) :
    √(fctAtil Φ τ0 p) = (3 / 2 * Φ (τ0 p) p) ^ (1 / 3 : ℝ) := by
  have hy : 0 < 3 / 2 * Φ (τ0 p) p := by linarith [h.val_pos p hp]
  rw [Real.sqrt_eq_rpow, fctAtil, ← Real.rpow_mul hy.le]
  norm_num

/-- `ã` is `C^∞` near every point of `Ω`. -/
theorem atil_contDiffAt (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) : ContDiffAt ℝ ∞' (fctAtil Φ τ0) p := by
  have h1 : ContDiffAt ℝ ∞' (fun q : ℝ × ℝ => Φ (τ0 q) q) p :=
    ContDiffAt.comp (g := fctPh Φ) (f := fun q : ℝ × ℝ => (τ0 q, q)) p (h.contDiffAt_ph (h.pos p hp) hp)
      ((h.tau0_contDiffAt hp).prodMk contDiffAt_id)
  have h2 := (contDiffAt_const (c := (3 / 2 : ℝ)).mul h1).rpow_const_of_ne (p := (2 / 3 : ℝ))
    (by linarith [h.val_pos p hp] : 3 / 2 * Φ (τ0 p) p ≠ 0)
  exact h2


lemma fderiv_decomp (D : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (a : ℝ) (v : ℝ × ℝ) :
    D (a, v) = a * D (1, 0) + v.1 * D (0, (1, 0)) + v.2 * D (0, (0, 1)) := by
  have : (a, v) = a • ((1 : ℝ), (0 : ℝ × ℝ)) + v.1 • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) + v.2 • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    ext <;> simp
  conv_lhs => rw [this]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The derivative of `p ↦ Φ̃(τ̃₀(p); p)`: the envelope theorem, `D = τ̃₀ dL + ∂_αΦ̃(τ̃₀) dα` (the `τ̃₀`-derivative drops since `∂_τΦ̃(τ̃₀) = 0`). -/
theorem hasFDerivAt_val (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) :
    HasFDerivAt (fun q : ℝ × ℝ => Φ (τ0 q) q)
      (τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + fctPhAlpha Φ (τ0 p) p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hτ : HasFDerivAt τ0 (fderiv ℝ τ0 p) p :=
    ((h.tau0_contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have hph : HasFDerivAt (fctPh Φ) (fderiv ℝ (fctPh Φ) (τ0 p, p)) (τ0 p, p) :=
    ((h.contDiffAt_ph (h.pos p hp) hp).differentiableAt (by simp)).hasFDerivAt
  have hcurve : HasFDerivAt (fun q : ℝ × ℝ => (τ0 q, q)) ((fderiv ℝ τ0 p).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p :=
    hτ.prodMk (hasFDerivAt_id p)
  have hph' : HasFDerivAt (fctPh Φ) (fderiv ℝ (fctPh Φ) (τ0 p, p)) ((fun q : ℝ × ℝ => (τ0 q, q)) p) := hph
  have hcomp := HasFDerivAt.comp (g := fctPh Φ) (f := fun q : ℝ × ℝ => (τ0 q, q)) p hph' hcurve
  refine hcomp.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := fderiv_decomp (fderiv ℝ (fctPh Φ) (τ0 p, p)) (fderiv ℝ τ0 p v) v
  have h2 : fderiv ℝ (fctPh Φ) (τ0 p, p) (1, 0) = 0 := h.crit p hp
  have h3 : fderiv ℝ (fctPh Φ) (τ0 p, p) (0, (1, 0)) = τ0 p := h.dL (τ0 p) (h.pos p hp) p hp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, add_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  rw [h1, h2, h3]
  simp [fctPhAlpha]
  ring

/-- **The envelope formulas for `ã`** (`fct:inner-symbols` (b1), `fct:warp-asymp` (1) Step 1): `ã` is differentiable with
`∂_{L₁} ã = τ̃₀/√ã` and `∂_α ã = ∂_αΦ̃(τ̃₀)/√ã` (the paper: `c^{-1} ϑ^{(1)}(τ̃₀)/√ã`). -/
theorem hasFDerivAt_atil (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) :
    HasFDerivAt (fctAtil Φ τ0)
      ((τ0 p / √(fctAtil Φ τ0 p)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (fctPhAlpha Φ (τ0 p) p / √(fctAtil Φ τ0 p)) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hy : 0 < 3 / 2 * Φ (τ0 p) p := by linarith [h.val_pos p hp]
  have hG : HasDerivAt (fun x : ℝ => (3 / 2 * x) ^ (2 / 3 : ℝ)) ((3 / 2 * Φ (τ0 p) p) ^ (-(1 / 3) : ℝ)) (Φ (τ0 p) p) := by
    have h1 : HasDerivAt (fun x : ℝ => 3 / 2 * x) (3 / 2) (Φ (τ0 p) p) := by
      simpa using (hasDerivAt_id (Φ (τ0 p) p)).const_mul (3 / 2 : ℝ)
    have h2 := h1.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hy.ne')
    convert h2 using 1
    have : (2 / 3 : ℝ) - 1 = -(1 / 3) := by norm_num
    rw [this]; ring
  have hcomp := HasDerivAt.comp_hasFDerivAt (f := fun q : ℝ × ℝ => Φ (τ0 q) q) p hG (h.hasFDerivAt_val hp)
  have hs : (3 / 2 * Φ (τ0 p) p) ^ (-(1 / 3) : ℝ) = (√(fctAtil Φ τ0 p))⁻¹ := by
    rw [h.sqrt_atil hp, Real.rpow_neg hy.le]
  refine (hcomp.congr_fderiv ?_)
  rw [hs]
  ext <;> simp [div_eq_inv_mul]

lemma sqrt_atil_pos (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) : 0 < √(fctAtil Φ τ0 p) :=
  Real.sqrt_pos.2 (h.atil_pos hp)

/-- `∂_{L₁} ã > 0` (`fct:warp-asymp` (1) Step 1: `∂_{L₁} ã = τ̃₀/√ã > 0`), as a derivative in `L` at fixed `α`. -/
theorem hasDerivAt_atil_L (h : FctPhaseBox Φ Ω τ0) {L α : ℝ} (hp : (L, α) ∈ Ω) :
    HasDerivAt (fun L' : ℝ => fctAtil Φ τ0 (L', α)) (τ0 (L, α) / √(fctAtil Φ τ0 (L, α))) L := by
  have hcurve : HasDerivAt (fun L' : ℝ => (L', α)) ((1 : ℝ), (0 : ℝ)) L :=
    (hasDerivAt_id L).prodMk (hasDerivAt_const L α)
  have := (h.hasFDerivAt_atil hp).comp_hasDerivAt L hcurve
  have h0 := this
  simp at h0
  exact h0

lemma atil_L_pos (h : FctPhaseBox Φ Ω τ0) {L α : ℝ} (hp : (L, α) ∈ Ω) : 0 < τ0 (L, α) / √(fctAtil Φ τ0 (L, α)) :=
  div_pos (h.pos _ hp) (h.sqrt_atil_pos hp)

/-- For fixed `α`, `L ↦ ã(L, α)` is strictly increasing on an open interval `I` with `I × {α} ⊆ Ω`. -/
theorem strictMonoOn_atil (h : FctPhaseBox Φ Ω τ0) {I : Set ℝ} (hI : IsOpen I) (hIo : I.OrdConnected) {α : ℝ}
    (hIΩ : ∀ L ∈ I, (L, α) ∈ Ω) : StrictMonoOn (fun L : ℝ => fctAtil Φ τ0 (L, α)) I := by
  refine strictMonoOn_of_deriv_pos (convex_iff_ordConnected.2 hIo) ?_ ?_
  · intro L hL
    exact (h.hasDerivAt_atil_L (hIΩ L hL)).continuousAt.continuousWithinAt
  · intro L hL
    rw [hI.interior_eq] at hL
    rw [(h.hasDerivAt_atil_L (hIΩ L hL)).deriv]
    exact h.atil_L_pos (hIΩ L hL)

end FctPhaseBox

/-! ### The coordinate map `(L, α) ↦ (û, α̃)` -/

/-- **The coordinates of the zero solve**, `(L₁, α) ↦ (û, α̃) = (-κ ã, λ α)`; in the paper `κ = 2^{-2/3} c^{2/3}` (`û = -2^{-2/3} c^{2/3} ã`) and
`λ = c^{-2/3}` (`α̃ = c^{-2/3} α`). -/
noncomputable def fctChart (κ lam : ℝ) (Φ : ℝ → ℝ × ℝ → ℝ) (τ0 : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-κ * fctAtil Φ τ0 p, lam * p.2)

namespace FctPhaseBox

variable {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}

/-- **Step 1: `(L₁, α) ↦ (û, α̃)` is injective** on a rectangle `I × J ⊆ Ω` (`I` an open interval), because `∂_{L₁} ã > 0`
(`L₁ ↦ û` is strictly decreasing for fixed `α`). -/
theorem fctChart_injOn (h : FctPhaseBox Φ Ω τ0) {κ lam : ℝ} (hκ : 0 < κ) (hlam : lam ≠ 0) {I J : Set ℝ}
    (hI : IsOpen I) (hIo : I.OrdConnected) (hIJ : I ×ˢ J ⊆ Ω) : InjOn (fctChart κ lam Φ τ0) (I ×ˢ J) := by
  rintro ⟨L1, a1⟩ ⟨h1I, h1J⟩ ⟨L2, a2⟩ ⟨h2I, h2J⟩ heq
  simp only [fctChart, Prod.mk.injEq] at heq
  obtain ⟨he1, he2⟩ := heq
  have ha : a1 = a2 := mul_left_cancel₀ hlam he2
  subst ha
  have hmono := h.strictMonoOn_atil hI hIo (α := a1) (fun L hL => hIJ ⟨hL, h1J⟩)
  have : fctAtil Φ τ0 (L1, a1) = fctAtil Φ τ0 (L2, a1) := by
    have := mul_left_cancel₀ (neg_ne_zero.2 hκ.ne') he1
    exact this
  exact Prod.ext (hmono.injOn h1I h2I this) rfl

/-- **Step 1: the image of the rectangle** (the paper's "onto a set containing `(a₁, 0) + B_r`"): a target `y = (y₁, y₂)` with `y₂/λ ∈ J` is
attained if `û = -κ ã` brackets `y₁` at two values `L_lo ≤ L_hi` of `I` (`û(L_lo, y₂/λ) ≥ y₁ ≥ û(L_hi, y₂/λ)`, intermediate value
theorem; the brackets are the paper's `û → 0` as `ℓ₁ ↓ 0` and `û(ℓ₁ = 2.6) → -∞`). -/
theorem fctChart_surj_of_bracket (h : FctPhaseBox Φ Ω τ0) {κ lam : ℝ} (hlam : lam ≠ 0) {I J : Set ℝ}
    (hIo : I.OrdConnected) (hIJ : I ×ˢ J ⊆ Ω) {y : ℝ × ℝ} (hy : y.2 / lam ∈ J) {Llo Lhi : ℝ} (hlo : Llo ∈ I) (hhi : Lhi ∈ I)
    (hle : Llo ≤ Lhi) (h1 : y.1 ≤ -κ * fctAtil Φ τ0 (Llo, y.2 / lam)) (h2 : -κ * fctAtil Φ τ0 (Lhi, y.2 / lam) ≤ y.1) :
    ∃ p ∈ I ×ˢ J, fctChart κ lam Φ τ0 p = y := by
  set α := y.2 / lam with hα
  have hcont : ContinuousOn (fun L : ℝ => -κ * fctAtil Φ τ0 (L, α)) (Icc Llo Lhi) := by
    intro L hL
    have hLI : L ∈ I := hIo.out hlo hhi hL
    have := (h.hasDerivAt_atil_L (hIJ ⟨hLI, hy⟩)).continuousAt
    exact (continuousAt_const.mul this).continuousWithinAt
  obtain ⟨L, hL, hLy⟩ := intermediate_value_Icc' hle hcont ⟨h2, h1⟩
  refine ⟨(L, α), ⟨hIo.out hlo hhi hL, hy⟩, ?_⟩
  simp only [fctChart, hLy]
  ext
  · rfl
  · simp only [hα]; field_simp

end FctPhaseBox


namespace FctPhaseBox

variable {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}

/-- `û_L = ∂_{L₁} û = -κ τ̃₀/√ã` of the chart `(û, α̃) = (-κ ã, λ α)`. -/
noncomputable def uL (κ : ℝ) (Φ : ℝ → ℝ × ℝ → ℝ) (τ0 : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := -κ * (τ0 p / √(fctAtil Φ τ0 p))

/-- `û_α = ∂_α û = -κ ∂_αΦ̃(τ̃₀)/√ã`. -/
noncomputable def uAlpha (κ : ℝ) (Φ : ℝ → ℝ × ℝ → ℝ) (τ0 : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -κ * (fctPhAlpha Φ (τ0 p) p / √(fctAtil Φ τ0 p))

/-- **The chain rule `(fct:chain)`** (`fct:warp-asymp` (1) Step 1): if `Ξ = Ξ̂ ∘ Ψ` near `p` (`Ψ = fctChart κ λ` the coordinates `(û, α̃)`) and `Ξ̂` is
differentiable at `Ψ p` with partial derivatives `Ξ̂_û = D̂(1, 0)`, `Ξ̂_α̃ = D̂(0, 1)`, then `∂_{L₁} Ξ = û_L Ξ̂_û` and
`∂_α Ξ = û_α Ξ̂_û + λ Ξ̂_α̃`, i.e. `Ξ̂_û = ∂_{L₁}Ξ/û_L` and `Ξ̂_α̃ = λ⁻¹(∂_αΞ - û_α Ξ̂_û)`
(for `λ = c^{-2/3}`: `∂_α̃Ξ̂ = c^{2/3} ∂_αΞ - c^{2/3} û_α ∂_ûΞ̂`). -/
theorem chain_rule (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) (κ lam : ℝ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Ξ Ξhat : ℝ × ℝ → F} {D : ℝ × ℝ →L[ℝ] F}
    (hΞ : HasFDerivAt Ξhat D (fctChart κ lam Φ τ0 p)) (hev : Ξ =ᶠ[𝓝 p] fun q => Ξhat (fctChart κ lam Φ τ0 q)) :
    HasFDerivAt Ξ (D.comp ((uL κ Φ τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + uAlpha κ Φ τ0 p • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (lam • ContinuousLinearMap.snd ℝ ℝ ℝ))) p ∧
      fderiv ℝ Ξ p (1, 0) = uL κ Φ τ0 p • D (1, 0) ∧
      fderiv ℝ Ξ p (0, 1) = uAlpha κ Φ τ0 p • D (1, 0) + lam • D (0, 1) := by
  have hA := h.hasFDerivAt_atil hp
  have hΨ : HasFDerivAt (fctChart κ lam Φ τ0)
      ((uL κ Φ τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + uAlpha κ Φ τ0 p • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (lam • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    refine HasFDerivAt.prodMk ?_ ?_
    · have := hA.const_mul (-κ)
      refine this.congr_fderiv ?_
      ext <;> simp [uL, uAlpha]
    · exact ((hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).const_mul lam)
  have hc := (hΞ.comp p hΨ).congr_of_eventuallyEq hev
  have hcomp : HasFDerivAt Ξ (D.comp ((uL κ Φ τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + uAlpha κ Φ τ0 p • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (lam • ContinuousLinearMap.snd ℝ ℝ ℝ))) p := hc
  refine ⟨hcomp, ?_, ?_⟩
  · rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    have e : ((uL κ Φ τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + uAlpha κ Φ τ0 p • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (lam • ContinuousLinearMap.snd ℝ ℝ ℝ)) ((1 : ℝ), (0 : ℝ)) = uL κ Φ τ0 p • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [e, map_smul]
  · rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    have e : ((uL κ Φ τ0 p • ContinuousLinearMap.fst ℝ ℝ ℝ + uAlpha κ Φ τ0 p • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (lam • ContinuousLinearMap.snd ℝ ℝ ℝ)) ((0 : ℝ), (1 : ℝ)) =
        uAlpha κ Φ τ0 p • ((1 : ℝ), (0 : ℝ)) + lam • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul]

end FctPhaseBox

/-! ### Step 1 feeding Step 4 -/

/-- **Transfer of a zero through a chart.**  `Ψ : X → E` is injective on `S` and `S`'s image contains the ball `closedBall a r`; write
`F y = G(Ψ_S⁻¹(a + y))` (`Ψ_S⁻¹ = Function.invFunOn Ψ S`).  A zero `y` of `F` in `closedBall 0 ρ` (`ρ ≤ r`), unique in `closedBall 0 r`, gives a zero
`x = Ψ_S⁻¹(a + y)` of `G` in `S` with `Ψ x ∈ closedBall a ρ`, unique among the points of `S` with `Ψ x' ∈ closedBall a r`. -/
theorem fct_zero_transfer {X E : Type*} [Nonempty X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ψ : X → E) (S : Set X) (G : X → E) (a : E) {r ρ : ℝ} (hρr : ρ ≤ r) (hinj : InjOn Ψ S)
    (hsurj : closedBall a r ⊆ Ψ '' S) {y : E} (hy : y ∈ closedBall (0 : E) ρ)
    (hGy : G (Function.invFunOn Ψ S (a + y)) = 0)
    (huniq : ∀ z ∈ closedBall (0 : E) r, G (Function.invFunOn Ψ S (a + z)) = 0 → z = y) :
    ∃ x ∈ S, Ψ x ∈ closedBall a ρ ∧ G x = 0 ∧ ∀ x' ∈ S, Ψ x' ∈ closedBall a r → G x' = 0 → x' = x := by
  have hball : ∀ z ∈ closedBall (0 : E) r, a + z ∈ closedBall a r := fun z hz => by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hspec : ∀ z ∈ closedBall (0 : E) r, Function.invFunOn Ψ S (a + z) ∈ S ∧ Ψ (Function.invFunOn Ψ S (a + z)) = a + z :=
    fun z hz => Function.invFunOn_pos (hsurj (hball z hz))
  have hyr : y ∈ closedBall (0 : E) r := closedBall_subset_closedBall hρr hy
  obtain ⟨hxS, hΨx⟩ := hspec y hyr
  refine ⟨_, hxS, ?_, hGy, ?_⟩
  · rw [hΨx]; simpa [mem_closedBall, dist_eq_norm] using hy
  · intro x' hx'S hx'r hGx'
    set z := Ψ x' - a with hz
    have hzr : z ∈ closedBall (0 : E) r := by simpa [mem_closedBall, dist_eq_norm, hz] using hx'r
    have hinv : Function.invFunOn Ψ S (a + z) = x' := by
      have : a + z = Ψ x' := by simp [hz]
      rw [this]
      exact hinj.leftInvOn_invFunOn hx'S
    have hz0 := huniq z hzr (by rw [hinv]; exact hGx')
    have : Ψ x' = Ψ (Function.invFunOn Ψ S (a + y)) := by rw [hΨx, ← hz0]; simp [hz]
    exact hinj hx'S hxS this

/-- **Step 1 + Step 4 of `fct:warp-asymp` (1)** (the zero solve in the coordinates `y = Ψ(x) - a`, `a = (a₁, 0)`): with the chart `Ψ = fctChart κ λ`
on a rectangle `S`, injective with image containing `closedBall a r`, and the zero functional `G` (`G = (Re, Im)(N₀ I_ε)`) such that
`F y = G(Ψ_S⁻¹(a + y)) = M y + N y` has `M` invertible and `N` `1/(2κ')`-Lipschitz on `B_r`, `κ' ‖N 0‖ ≤ ρ/2`, `ρ ≤ r`
(`exists_unique_zero_of_lipschitz_perturbation`), `G` has a zero `x ∈ S` with `Ψ x ∈ a + B_ρ`, and it is the only zero in `S ∩ Ψ⁻¹(a + B_r)`. -/
theorem fct_zero_of_chart {X E : Type*} [Nonempty X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ψ : X → E) (S : Set X) (G : X → E) (a : E) {r ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρr : ρ ≤ r) (hinj : InjOn Ψ S)
    (hsurj : closedBall a r ⊆ Ψ '' S) (M : E ≃L[ℝ] E) {κ : ℝ} (hκ : 0 < κ) (hM : ‖(M.symm : E →L[ℝ] E)‖ ≤ κ) {N : E → E}
    (hF : ∀ y, G (Function.invFunOn Ψ S (a + y)) = M y + N y)
    (hLip : ∀ y ∈ closedBall (0 : E) r, ∀ z ∈ closedBall (0 : E) r, ‖N y - N z‖ ≤ 1 / (2 * κ) * ‖y - z‖)
    (h0 : κ * ‖N 0‖ ≤ ρ / 2) :
    ∃ x ∈ S, Ψ x ∈ closedBall a ρ ∧ G x = 0 ∧ ∀ x' ∈ S, Ψ x' ∈ closedBall a r → G x' = 0 → x' = x := by
  obtain ⟨y, hy, hFy, hu⟩ := exists_unique_zero_of_lipschitz_perturbation M hκ hM
    (F := fun y => G (Function.invFunOn Ψ S (a + y))) hF hLip h0 hρ0 hρr
  exact fct_zero_transfer Ψ S G a hρr hinj hsurj hy hFy hu

/-- info: 'FormalResearch.SignUncertainty.fct_zero_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_zero_of_chart

/-- info: 'FormalResearch.SignUncertainty.FctPhaseBox.hasFDerivAt_atil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctPhaseBox.hasFDerivAt_atil

/-- info: 'FormalResearch.SignUncertainty.FctPhaseBox.fctChart_surj_of_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctPhaseBox.fctChart_surj_of_bracket

/-- info: 'FormalResearch.SignUncertainty.FctPhaseBox.fctChart_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctPhaseBox.fctChart_injOn

/-- info: 'FormalResearch.SignUncertainty.FctPhaseBox.tau0_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctPhaseBox.tau0_contDiffAt

end FormalResearch.SignUncertainty

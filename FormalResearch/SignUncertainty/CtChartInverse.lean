module

public import Mathlib

/-!
# Holomorphic inverse of `a ↦ a + κ Ψ(a)` (support for `ct:cfu`, the complex chart `φ_c = û⁻¹`)

`constant_terms_lower.tex`, `ct:phic-exp` / Lemma `ct:cfu`: `φ_c := û⁻¹` with `û(ũ) = ũ + λ ψ_ε(μ ũ)`, `μ λ = c⁻¹`.  In the variable
`a = μ ũ` the map is `a ↦ a + κ Ψ(a)`, `κ = c⁻¹`, with `Ψ` holomorphic on a fixed disc.  **Proved.**

`ct_inv_chart`: if `Ψ` is holomorphic near `closedBall 0 r` with `‖Ψ‖, ‖Ψ'‖ ≤ M` there and `κ M ≤ min(1/2, r/2)`, then on
`ball 0 (r/2)` the equation `a + κ Ψ(a) = b` has a unique solution `G b` in `closedBall 0 r`, and `G` is holomorphic with
`G' = 1/(1 + κ Ψ'(G))` (a contraction argument, then the holomorphic inverse function theorem to see that `G` is the local
inverse).  No analyticity of `Ψ` beyond holomorphy on the disc is used.
-/

@[expose] public section

open Complex Metric Set Filter Topology

namespace FormalResearch.SignUncertainty

section Inverse

variable {Ψ : ℂ → ℂ} {ρ r M κ : ℝ}

/-- Lipschitz bound for `Ψ` on `closedBall 0 r` from the derivative bound. -/
lemma ct_inv_lip (hd : DifferentiableOn ℂ Ψ (ball 0 ρ)) (hr : r < ρ)
    (hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖deriv Ψ z‖ ≤ M) {a₁ a₂ : ℂ} (h₁ : a₁ ∈ closedBall (0 : ℂ) r)
    (h₂ : a₂ ∈ closedBall (0 : ℂ) r) : ‖Ψ a₁ - Ψ a₂‖ ≤ M * ‖a₁ - a₂‖ := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 ρ := closedBall_subset_ball hr
  have hder : ∀ x ∈ closedBall (0 : ℂ) r, HasDerivWithinAt Ψ (deriv Ψ x) (closedBall (0 : ℂ) r) x := fun x hx =>
    ((hd.differentiableAt (isOpen_ball.mem_nhds (hsub hx))).hasDerivAt).hasDerivWithinAt
  have := (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_hasDerivWithin_le hder hM h₂ h₁
  exact this

/-- Existence and uniqueness of the solution of `a + κ Ψ(a) = b` in `closedBall 0 r`. -/
lemma ct_inv_exists_unique (hd : DifferentiableOn ℂ Ψ (ball 0 ρ)) (hr : r < ρ) (hr0 : 0 < r)
    (hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖Ψ z‖ ≤ M ∧ ‖deriv Ψ z‖ ≤ M) (hκ0 : 0 ≤ κ) (hκ : κ * M ≤ 1 / 2)
    (hκr : κ * M ≤ r / 2) {b : ℂ} (hb : ‖b‖ < r / 2) :
    ∃! a : ℂ, a ∈ closedBall (0 : ℂ) r ∧ a + (κ : ℂ) * Ψ a = b := by
  have hlip := fun {a₁ a₂ : ℂ} (h₁ : a₁ ∈ closedBall (0 : ℂ) r) (h₂ : a₂ ∈ closedBall (0 : ℂ) r) =>
    ct_inv_lip hd hr (fun z hz => (hM z hz).2) h₁ h₂
  set f : ℂ → ℂ := fun a => b - (κ : ℂ) * Ψ a with hf
  have hmaps : MapsTo f (closedBall (0 : ℂ) r) (closedBall (0 : ℂ) r) := by
    intro a ha
    rw [mem_closedBall_zero_iff]
    calc ‖f a‖ = ‖b - (κ : ℂ) * Ψ a‖ := rfl
      _ ≤ ‖b‖ + ‖(κ : ℂ) * Ψ a‖ := norm_sub_le _ _
      _ ≤ r / 2 + κ * M := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
          have := (hM a ha).1
          nlinarith
      _ ≤ r := by linarith
  have hdist : ∀ a₁ a₂ : ℂ, a₁ ∈ closedBall (0 : ℂ) r → a₂ ∈ closedBall (0 : ℂ) r →
      ‖f a₁ - f a₂‖ ≤ (1 / 2) * ‖a₁ - a₂‖ := by
    intro a₁ a₂ h₁ h₂
    have : f a₁ - f a₂ = -((κ : ℂ) * (Ψ a₁ - Ψ a₂)) := by simp only [hf]; ring
    rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    have h3 := hlip h₁ h₂
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hr0.le)).1
    calc κ * ‖Ψ a₁ - Ψ a₂‖ ≤ κ * (M * ‖a₁ - a₂‖) := mul_le_mul_of_nonneg_left h3 hκ0
      _ = (κ * M) * ‖a₁ - a₂‖ := by ring
      _ ≤ (1 / 2) * ‖a₁ - a₂‖ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
  have hc : ContractingWith (1 / 2 : NNReal) (hmaps.restrict f (closedBall (0 : ℂ) r) (closedBall (0 : ℂ) r)) := by
    refine ⟨by rw [show ((1 / 2 : NNReal)) = 1 / 2 from rfl]; exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1), ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := hdist x y x.2 y.2
    show dist (f (x : ℂ)) (f (y : ℂ)) ≤ ((1 / 2 : NNReal) : ℝ) * dist (x : ℂ) (y : ℂ)
    rw [dist_eq_norm, dist_eq_norm]
    simpa using this
  obtain ⟨y, hy, hfix, -⟩ := ContractingWith.exists_fixedPoint' (isClosed_closedBall).isComplete hmaps hc
    (mem_closedBall_self hr0.le) (edist_ne_top _ _)
  refine ⟨y, ⟨hy, ?_⟩, ?_⟩
  · have : f y = y := hfix
    simp only [hf] at this
    linear_combination (-1 : ℂ) * this
  · rintro a ⟨ha, hab⟩
    have hay : a = f a := by simp only [hf]; rw [← hab]; ring
    have hyy : y = f y := hfix.symm
    have h1 := hdist a y ha hy
    have : ‖a - y‖ ≤ (1 / 2) * ‖a - y‖ := by
      calc ‖a - y‖ = ‖f a - f y‖ := by rw [← hay, ← hyy]
        _ ≤ _ := h1
    have h0 : ‖a - y‖ = 0 := by linarith [norm_nonneg (a - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **The holomorphic inverse `G` of `a ↦ a + κ Ψ(a)`** on `ball 0 (r/2)`. -/
theorem ct_inv_chart (hd : DifferentiableOn ℂ Ψ (ball 0 ρ)) (hr : r < ρ) (hr0 : 0 < r)
    (hM : ∀ z ∈ closedBall (0 : ℂ) r, ‖Ψ z‖ ≤ M ∧ ‖deriv Ψ z‖ ≤ M) (hκ0 : 0 ≤ κ) (hκ : κ * M ≤ 1 / 2)
    (hκr : κ * M ≤ r / 2) :
    ∃ G : ℂ → ℂ, (∀ b ∈ ball (0 : ℂ) (r / 2), G b ∈ closedBall (0 : ℂ) r ∧ G b + (κ : ℂ) * Ψ (G b) = b) ∧
      (∀ b ∈ ball (0 : ℂ) (r / 2), ∀ a ∈ closedBall (0 : ℂ) r, a + (κ : ℂ) * Ψ a = b → a = G b) ∧
      ∀ b ∈ ball (0 : ℂ) (r / 2), HasDerivAt G (1 / (1 + (κ : ℂ) * deriv Ψ (G b))) b := by
  classical
  have hex := fun {b : ℂ} (hb : ‖b‖ < r / 2) => ct_inv_exists_unique hd hr hr0 hM hκ0 hκ hκr hb
  let G : ℂ → ℂ := fun b => if hb : ‖b‖ < r / 2 then (hex hb).exists.choose else 0
  have hGspec : ∀ b ∈ ball (0 : ℂ) (r / 2), G b ∈ closedBall (0 : ℂ) r ∧ G b + (κ : ℂ) * Ψ (G b) = b := by
    intro b hb
    have hb' : ‖b‖ < r / 2 := by simpa using hb
    simp only [G, dite_eq_left_of_eq_true (eq_true hb')]
    exact (hex hb').exists.choose_spec
  have hGuniq : ∀ b ∈ ball (0 : ℂ) (r / 2), ∀ a ∈ closedBall (0 : ℂ) r, a + (κ : ℂ) * Ψ a = b → a = G b := by
    intro b hb a ha hab
    exact (hex (by simpa using hb)).unique ⟨ha, hab⟩ (hGspec b hb)
  refine ⟨G, hGspec, hGuniq, ?_⟩
  intro b0 hb0
  obtain ⟨hGb0, hGeq⟩ := hGspec b0 hb0
  set a0 := G b0 with ha0
  have hb0' : ‖b0‖ < r / 2 := by simpa using hb0
  have ha0r : ‖a0‖ < r := by
    have h1 : a0 = b0 - (κ : ℂ) * Ψ a0 := by rw [← hGeq]; ring
    have : ‖a0‖ ≤ ‖b0‖ + κ * M := by
      rw [h1]
      calc ‖b0 - (κ : ℂ) * Ψ a0‖ ≤ ‖b0‖ + ‖(κ : ℂ) * Ψ a0‖ := norm_sub_le _ _
        _ ≤ ‖b0‖ + κ * M := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
            have := (hM a0 hGb0).1
            nlinarith
    linarith
  have ha0ρ : a0 ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]; linarith
  have hanΨ : AnalyticAt ℂ Ψ a0 := hd.analyticAt (isOpen_ball.mem_nhds ha0ρ)
  set f : ℂ → ℂ := fun a => a + (κ : ℂ) * Ψ a with hf
  have hanf : AnalyticAt ℂ f a0 := analyticAt_id.add (analyticAt_const.mul hanΨ)
  have hfd : HasDerivAt f (1 + (κ : ℂ) * deriv Ψ a0) a0 :=
    (hasDerivAt_id a0).add (hanΨ.differentiableAt.hasDerivAt.const_mul (κ : ℂ))
  have hfd' : deriv f a0 = 1 + (κ : ℂ) * deriv Ψ a0 := hfd.deriv
  have hne : deriv f a0 ≠ 0 := by
    rw [hfd']
    intro h0
    have h1 : (κ : ℂ) * deriv Ψ a0 = -1 := by linear_combination h0
    have h2 : ‖(κ : ℂ) * deriv Ψ a0‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ0]
      have := (hM a0 hGb0).2
      nlinarith
    rw [h1] at h2
    norm_num at h2
  have hsd : HasStrictDerivAt f (deriv f a0) a0 := hanf.hasStrictDerivAt
  set g := hsd.localInverse f (deriv f a0) a0 hne with hg
  have hgd : HasStrictDerivAt g (deriv f a0)⁻¹ (f a0) := hsd.to_localInverse hne
  have hfa0 : f a0 = b0 := hGeq
  rw [hfa0] at hgd
  have hev1 : ∀ᶠ b in 𝓝 b0, f (g b) = b := by
    have := hsd.eventually_right_inverse hne
    rwa [hfa0] at this
  have hga0 : g b0 = a0 := by
    have := (hsd.eventually_left_inverse hne).self_of_nhds
    rw [← hfa0]; exact this
  have hev2 : ∀ᶠ b in 𝓝 b0, g b ∈ ball (0 : ℂ) r := by
    have hcont : ContinuousAt g b0 := hgd.hasDerivAt.continuousAt
    exact hcont.eventually (isOpen_ball.mem_nhds (by rw [hga0]; simpa using ha0r))
  have hev3 : ∀ᶠ b in 𝓝 b0, b ∈ ball (0 : ℂ) (r / 2) := isOpen_ball.mem_nhds hb0
  have hEq : G =ᶠ[𝓝 b0] g := by
    filter_upwards [hev1, hev2, hev3] with b h1 h2 h3
    exact (hGuniq b h3 (g b) (ball_subset_closedBall h2) h1).symm
  have hgd2 : HasDerivAt g (deriv f a0)⁻¹ b0 := hgd.hasDerivAt
  have : HasDerivAt G (deriv f a0)⁻¹ b0 := hgd2.congr_of_eventuallyEq hEq
  rw [hfd', ← one_div] at this
  exact this

end Inverse

end FormalResearch.SignUncertainty

module

public import FormalResearch.ModularBootstrap.Stability.TerminalStability
public import FormalResearch.ModularBootstrap.Stability.AiryStability
public import FormalResearch.ModularBootstrap.Blowup.ClarkNormLimit

/-!
# Theorem SE.6 (`se:3.1`): sharp two-level stability

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem SE.6 (`se:3.1`):
for the Clark angle `α` with `z₁(α) = u₁`, `z₂ = z₂(α)`, `g_α = ψ_α²/((u - u₁)(u - z₂))`,
`I₂(δ; u₁) = inf { ∫ f/‖f‖₁ : f ∈ 𝒢 \ 0, f(u₁) ≥ 0, f ≥ 0 on (-∞, z₂ + δ] }`.

Proved here (`clark_stability`): `I₂(δ) > 0` for `δ > 0` and
`I₂(δ)/δ → κ₂ = (cos²α - z₂ sin²α)/(‖g_α‖₁ (u₁ - z₂))` as `δ ↓ 0`, with `‖g_α‖₁ = 2L_*(α)`.
This is `terminal_stability` at the Clark datum: weight `1/K(z₂,z₂)` (Clark quadrature,
`airyClark_hasSum_unc`), `-g_α'(z₂) = ψ_α'(z₂)²/(u₁ - z₂)` and `ψ_α'(z₂)² = D(z₂) K(z₂,z₂)`;
the trial family is `g_α - δ g_α/(u - z₂)` (`G/(u - z₂)` is the quotient of `at47_div_point`).

Not proved here: the second assertion of SE.6, `κ₂(u₁) → (2L_*^{(0)})⁻¹` as `u₁ → ∞` (dominated
convergence of `u₁ L_*(α)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup FormalResearch.SignUncertainty
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.TwoEdgeBootstrap

variable {α : ℝ}

/-- The Clark kernel diagonal `K(x,x) = Ai'(x)² - x Ai(x)²`. -/
noncomputable def clarkK (x : ℝ) : ℝ := airyAi' x ^ 2 - x * airyAi x ^ 2

lemma clarkK_pos (x : ℝ) : 0 < clarkK x := airyKer_pos' x

/-- `ψ_α'` on the real axis. -/
noncomputable def clarkP (α x : ℝ) : ℝ := Real.cos α * airyAi' x - Real.sin α * x * airyAi x

lemma psiClark_deriv_ofReal (α x : ℝ) : deriv (psiClark α) (x : ℂ) = ((clarkP α x : ℝ) : ℂ) := by
  have h1 := (differentiable_airyAiC (x : ℂ)).hasDerivAt
  have h2 := hasDerivAt_deriv_airyAiC (x : ℂ)
  have hd : HasDerivAt (psiClark α) ((Real.cos α : ℂ) * deriv airyAiC (x : ℂ) -
      (Real.sin α : ℂ) * ((x : ℂ) * airyAiC (x : ℂ))) (x : ℂ) :=
    (h1.const_mul (Real.cos α : ℂ)).sub (h2.const_mul (Real.sin α : ℂ))
  rw [hd.deriv, deriv_airyAiC_ofReal, airyAiC_ofReal]
  unfold clarkP
  push_cast
  ring

/-- At a Clark node: `ψ_α'(z)² = D(z) K(z,z)` with `D(z) = cos²α - z sin²α`. -/
lemma clarkP_sq {z : ℝ} (hz : Real.cos α * airyAi z - Real.sin α * airyAi' z = 0) :
    clarkP α z ^ 2 = (Real.cos α ^ 2 - z * Real.sin α ^ 2) * clarkK z := by
  unfold clarkP clarkK
  linear_combination (z * (Real.cos α * airyAi z - Real.sin α * airyAi' z)) * hz

lemma psiClark_real_zero {n : ℕ} (hα : Real.sin α ≠ 0) (hn : 1 ≤ n) :
    Real.cos α * airyAi (clarkNode α n) - Real.sin α * airyAi' (clarkNode α n) = 0 := by
  have h := clarkNode_zero hα hn
  rw [psiClark_ofReal] at h
  have := Complex.ofReal_eq_zero.mp h
  simpa [SturmAiry.combo] using this

lemma clarkExtremal_node_zero (hα : Real.sin α ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    clarkExtremal α (clarkNode α n : ℂ) = 0 := by
  rcases eq_or_ne n 1 with rfl | h1
  · exact clarkExtremal_at_one hα
  rcases eq_or_ne n 2 with rfl | h2
  · exact clarkExtremal_at_two hα
  have hn1 : (clarkNode α n : ℂ) ≠ (clarkNode α 1 : ℂ) := fun h => by
    have := Complex.ofReal_injective h
    rcases lt_or_gt_of_ne h1 with hl | hl
    · omega
    · have := clarkNode_lt_of_lt (le_refl 1) hl α
      linarith
  have hn2 : (clarkNode α n : ℂ) ≠ (clarkNode α 2 : ℂ) := fun h => by
    have := Complex.ofReal_injective h
    rcases lt_or_gt_of_ne h2 with hl | hl
    · omega
    · have := clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) hl α
      linarith
  rw [clarkExtremal_eq hα hn1 hn2, clarkNode_zero hα hn]
  simp

/-- `deriv` of a function real on `ℝ` has zero imaginary part on `ℝ`. -/
lemma deriv_im_zero_of_real {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hreal : ∀ x : ℝ, (h (x : ℂ)).im = 0) (x : ℝ) : (deriv h (x : ℂ)).im = 0 := by
  have hdG : HasDerivAt (fun t : ℝ => h (t : ℂ)) (deriv h (x : ℂ)) x := by
    simpa only [mul_one] using (hd (x : ℂ)).hasDerivAt.comp_ofReal
  have hdim : HasDerivAt (fun t : ℝ => (h (t : ℂ)).im) (deriv h (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hdG
  have hconst : (fun t : ℝ => (h (t : ℂ)).im) = fun _ => (0 : ℝ) := funext hreal
  rw [hconst] at hdim
  exact hdim.unique (hasDerivAt_const _ _)

/-- Clark quadrature in real form. -/
theorem clark_hasSum_re (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : AiryG f) :
    HasSum (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
      (f z.1).re / clarkK z.1.re) (∫ x : ℝ, (f (x : ℂ)).re) := by
  obtain ⟨C, ν, hC, hb⟩ := hf.growth
  have hsum := airyClark_hasSum_unc α hα hf.diff hf.integrable hC hb
  have hre := Complex.hasSum_re hsum
  have hw : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      (f z.1 / (deriv airyAiC z.1 ^ 2 - z.1 * airyAiC z.1 ^ 2)).re =
        (f z.1).re / clarkK z.1.re := by
    intro z
    obtain ⟨n, -, hzn⟩ := (psiClark_zero_iff hα z.1).1 z.2
    have him : z.1.im = 0 := by rw [hzn]; simp
    have ez : z.1 = (z.1.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have eK : deriv airyAiC z.1 ^ 2 - z.1 * airyAiC z.1 ^ 2 = ((clarkK z.1.re : ℝ) : ℂ) := by
      conv_lhs => rw [ez]
      rw [deriv_airyAiC_ofReal, airyAiC_ofReal]
      unfold clarkK
      push_cast; ring
    have ef : f z.1 = (((f z.1).re : ℝ) : ℂ) := by
      conv_lhs => rw [ez]
      exact airy_real_cast hf.real z.1.re |>.trans (by rw [← ez])
    conv_lhs => rw [eK, ef, ← Complex.ofReal_div]
    rw [Complex.ofReal_re]
  have hint_re : (∫ x : ℝ, f (x : ℂ)).re = ∫ x : ℝ, (f (x : ℂ)).re := (hf.re_integral).symm
  rw [hint_re] at hre
  simpa only [hw] using hre

/-- Clark quadrature positivity: for `f ∈ 𝒢` with `f(z₁) ≥ 0` and `f ≥ 0` on `(-∞, z₂]`,
`∫ f ≥ 0` and `∫ f ≥ f(z₂)/K(z₂,z₂)`. -/
theorem clark_quad (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : AiryG f)
    (hz1 : 0 ≤ (f (clarkNode α 1 : ℂ)).re) (hpos : ∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (f (x : ℂ)).re) :
    0 ≤ ∫ x : ℝ, (f (x : ℂ)).re ∧
      (clarkK (clarkNode α 2))⁻¹ * (f (clarkNode α 2 : ℂ)).re ≤ ∫ x : ℝ, (f (x : ℂ)).re := by
  have hre := clark_hasSum_re hα hf
  have hnn : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      0 ≤ (f z.1).re / clarkK z.1.re := by
    intro z
    obtain ⟨n, hn, hzn⟩ := (psiClark_zero_iff hα z.1).1 z.2
    have hfre : 0 ≤ (f z.1).re := by
      rcases hn.eq_or_lt with rfl | hgt
      · rw [hzn]; exact hz1
      · have hle : z.1.re ≤ clarkNode α 2 := by
          have hzre : z.1.re = clarkNode α n := by rw [hzn]; simp
          rw [hzre]
          rcases eq_or_ne n 2 with rfl | hn2
          · exact le_rfl
          · exact (clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) (by omega) α).le
        rw [show z.1 = (z.1.re : ℂ) by rw [hzn]; simp]
        exact hpos _ hle
    exact div_nonneg hfre (clarkK_pos _).le
  refine ⟨hre.nonneg hnn, ?_⟩
  let z₂ : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} :=
    ⟨(clarkNode α 2 : ℂ), clarkNode_zero hα (by norm_num)⟩
  have := le_hasSum hre z₂ (fun j _ => hnn j)
  simpa [z₂, div_eq_inv_mul] using this

/-- The derivative of `g_α` at the terminal node: `g_α'(z₂) = ψ_α'(z₂)²/(z₂ - z₁)`. -/
lemma clarkExtremal_deriv_at_two (hα : Real.sin α ≠ 0) :
    deriv (clarkExtremal α) (clarkNode α 2 : ℂ) =
      ((clarkP α (clarkNode α 2) ^ 2 / (clarkNode α 2 - clarkNode α 1) : ℝ) : ℂ) := by
  set z₁ := clarkNode α 1 with hz₁
  set z₂ := clarkNode α 2 with hz₂
  have hne : z₂ ≠ z₁ := by linarith [clarkNode_two_lt_one α]
  have hnec : (z₂ : ℂ) - (z₁ : ℂ) ≠ 0 := sub_ne_zero.mpr (fun h => hne (Complex.ofReal_injective h))
  set D₁ := dslope (psiClark α) (z₁ : ℂ) with hD₁
  set D₂ := dslope (psiClark α) (z₂ : ℂ) with hD₂
  have hpd : Differentiable ℂ (psiClark α) := differentiable_psiClark α
  have hD₁d : Differentiable ℂ D₁ := EntireDiv.differentiable_dslope_entire hpd _
  have hD₂d : Differentiable ℂ D₂ := EntireDiv.differentiable_dslope_entire hpd _
  have hψz₁ : psiClark α (z₁ : ℂ) = 0 := clarkNode_zero hα le_rfl
  have hψz₂ : psiClark α (z₂ : ℂ) = 0 := clarkNode_zero hα (by norm_num)
  have hD₁eq : ∀ u : ℂ, (u - (z₁ : ℂ)) * D₁ u = psiClark α u := fun u => by
    have := sub_smul_dslope (psiClark α) (z₁ : ℂ) u
    rwa [smul_eq_mul, hψz₁, sub_zero] at this
  have hD₁z₂ : D₁ (z₂ : ℂ) = 0 := by
    have := hD₁eq (z₂ : ℂ)
    rw [hψz₂] at this
    exact (mul_eq_zero.mp this).resolve_left hnec
  have hD₂z₂ : D₂ (z₂ : ℂ) = deriv (psiClark α) (z₂ : ℂ) := by rw [hD₂, dslope_same]
  -- derivative of `D₁` at `z₂`: differentiate `(u - z₁) D₁ u = ψ u`
  have hD₁' : deriv D₁ (z₂ : ℂ) = deriv (psiClark α) (z₂ : ℂ) / ((z₂ : ℂ) - (z₁ : ℂ)) := by
    have hl : HasDerivAt (fun u : ℂ => (u - (z₁ : ℂ)) * D₁ u)
        (1 * D₁ (z₂ : ℂ) + ((z₂ : ℂ) - (z₁ : ℂ)) * deriv D₁ (z₂ : ℂ)) (z₂ : ℂ) :=
      ((hasDerivAt_id _).sub_const _).mul (hD₁d (z₂ : ℂ)).hasDerivAt
    have hr : HasDerivAt (psiClark α) (deriv (psiClark α) (z₂ : ℂ)) (z₂ : ℂ) :=
      (hpd (z₂ : ℂ)).hasDerivAt
    have heq : (fun u : ℂ => (u - (z₁ : ℂ)) * D₁ u) = psiClark α := funext hD₁eq
    rw [heq] at hl
    have := hl.unique hr
    rw [hD₁z₂] at this
    field_simp
    linear_combination this
  have hG : HasDerivAt (clarkExtremal α)
      (deriv D₁ (z₂ : ℂ) * D₂ (z₂ : ℂ) + D₁ (z₂ : ℂ) * deriv D₂ (z₂ : ℂ)) (z₂ : ℂ) :=
    (hD₁d (z₂ : ℂ)).hasDerivAt.mul (hD₂d (z₂ : ℂ)).hasDerivAt
  rw [hG.deriv, hD₁', hD₁z₂, hD₂z₂, psiClark_deriv_ofReal]
  push_cast
  ring

/-- The Clark datum for `terminal_stability`. -/
noncomputable def clarkTerminalData (hα : Real.sin α ≠ 0) : TerminalData Unit where
  G := clarkExtremal α
  zT := clarkNode α 2
  nodes := fun _ => clarkNode α 1
  w := (clarkK (clarkNode α 2))⁻¹
  γ := clarkP α (clarkNode α 2) ^ 2 / (clarkNode α 1 - clarkNode α 2)
  hG := clarkExtremalProfile hα
  hGgrowth := by
    obtain ⟨C, hC, hb⟩ := clarkExtremal_bound hα
    exact ⟨C, -(3 / 2), hC, hb⟩
  hP := clarkEqualityPrinciple hα
  hw := inv_pos.mpr (clarkK_pos _)
  hγ := by
    have hp : clarkP α (clarkNode α 2) ≠ 0 := by
      intro h
      have := clarkNode_deriv_ne_zero hα (n := 2) (by norm_num)
      rw [psiClark_deriv_ofReal, h] at this
      simp at this
    have hgap : 0 < clarkNode α 1 - clarkNode α 2 := by linarith [clarkNode_two_lt_one α]
    positivity
  hderiv := by
    rw [clarkExtremal_deriv_at_two hα, Complex.ofReal_re]
    have hgap : clarkNode α 2 - clarkNode α 1 = -(clarkNode α 1 - clarkNode α 2) := by ring
    rw [hgap, div_neg]
  quad := fun f hf hpos hnodes =>
    clark_quad hα hf (hnodes ()) hpos

/-- The Clark two-level infimum `I₂(δ; u₁)` of Theorem SE.6. -/
noncomputable def clarkI (hα : Real.sin α ≠ 0) (δ : ℝ) : ℝ := termI (clarkTerminalData hα) δ

/-- The terminal-node weight times `|g_α'(z₂)|` equals `D(z₂)/(z₁ - z₂)`. -/
lemma clark_wγ (hα : Real.sin α ≠ 0) :
    (clarkTerminalData hα).w * (clarkTerminalData hα).γ =
      (Real.cos α ^ 2 - clarkNode α 2 * Real.sin α ^ 2) / (clarkNode α 1 - clarkNode α 2) := by
  show (clarkK (clarkNode α 2))⁻¹ * (clarkP α (clarkNode α 2) ^ 2 / (clarkNode α 1 - clarkNode α 2)) = _
  rw [clarkP_sq (psiClark_real_zero hα (by norm_num))]
  have := (clarkK_pos (clarkNode α 2)).ne'
  field_simp

/-- The quotient `ψ = g_α/(u - z₂)` (entire, in `𝒢`) used for the trial family. -/
lemma clark_trial_data (hα : Real.sin α ≠ 0) :
    ∃ ψ : ℂ → ℂ, AiryG ψ ∧ (∀ u, clarkExtremal α u = ψ u * (u - (clarkNode α 2 : ℂ))) ∧
      ψ (clarkNode α 2 : ℂ) = deriv (clarkExtremal α) (clarkNode α 2 : ℂ) := by
  obtain ⟨C, hC, hb⟩ := clarkExtremal_bound hα
  obtain ⟨ψ, hψd, heq, C', hC', hb'⟩ := at47_div_point (differentiable_clarkExtremal α)
    (clarkNode α 2) (clarkExtremal_at_two hα) hC hb
  have hder : ψ (clarkNode α 2 : ℂ) = deriv (clarkExtremal α) (clarkNode α 2 : ℂ) := by
    have hG : (clarkExtremal α) = fun u => ψ u * (u - (clarkNode α 2 : ℂ)) := funext heq
    have hd : HasDerivAt (fun u => ψ u * (u - (clarkNode α 2 : ℂ)))
        (deriv ψ (clarkNode α 2 : ℂ) * ((clarkNode α 2 : ℂ) - (clarkNode α 2 : ℂ)) +
          ψ (clarkNode α 2 : ℂ) * 1) (clarkNode α 2 : ℂ) :=
      (hψd (clarkNode α 2 : ℂ)).hasDerivAt.mul ((hasDerivAt_id _).sub_const _)
    rw [hG, hd.deriv]
    ring
  have hreal : ∀ x : ℝ, (ψ (x : ℂ)).im = 0 := by
    intro x
    by_cases hx : x = clarkNode α 2
    · rw [hx, hder]
      exact deriv_im_zero_of_real (differentiable_clarkExtremal α) (clarkExtremal_ofReal hα) _
    · have h := congrArg Complex.im (heq (x : ℂ))
      rw [clarkExtremal_ofReal hα x, Complex.mul_im] at h
      have hxr : ((x : ℂ) - (clarkNode α 2 : ℂ)).re = x - clarkNode α 2 := by simp
      have hxi : ((x : ℂ) - (clarkNode α 2 : ℂ)).im = 0 := by simp
      rw [hxr, hxi] at h
      have hne : x - clarkNode α 2 ≠ 0 := sub_ne_zero.mpr hx
      have : (ψ (x : ℂ)).im * (x - clarkNode α 2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hne
  exact ⟨ψ, ⟨hψd, airy_integrable_real hψd hC' (by norm_num) hb', ⟨C', -(3 / 2), hC', hb'⟩, hreal⟩,
    heq, hder⟩

lemma clark_re_psi {ψ : ℂ → ℂ}
    (heq : ∀ u, clarkExtremal α u = ψ u * (u - (clarkNode α 2 : ℂ)))
    (hreal : ∀ x : ℝ, (ψ (x : ℂ)).im = 0) (x : ℝ) :
    (clarkExtremal α (x : ℂ)).re = (ψ (x : ℂ)).re * (x - clarkNode α 2) := by
  have h := congrArg Complex.re (heq (x : ℂ))
  rw [Complex.mul_re, hreal x] at h
  simpa using h

/-- **Theorem SE.6 (`se:3.1`), first assertion.**  For every Clark angle (`sin α ≠ 0`), `I₂(δ) > 0` for
`δ > 0` and `I₂(δ)/δ → κ₂ = (cos²α - z₂ sin²α)/((z₁ - z₂) ‖g_α‖₁)` as `δ ↓ 0`, where
`‖g_α‖₁ = 2L_*(α) = 2 ∫_{z₂}^{z₁} |g_α|` (`clarkExtremal_l1_norm`). -/
theorem clark_stability (hα : Real.sin α ≠ 0) :
    (∀ δ : ℝ, 0 < δ → 0 < clarkI hα δ) ∧
      Tendsto (fun δ : ℝ => clarkI hα δ / δ) (𝓝[>] 0)
        (𝓝 ((Real.cos α ^ 2 - clarkNode α 2 * Real.sin α ^ 2) /
          ((clarkNode α 1 - clarkNode α 2) *
            (2 * ∫ x in Set.Ioo (clarkNode α 2) (clarkNode α 1), -(clarkExtremal α (x : ℂ)).re)))) := by
  set T := clarkTerminalData hα with hT
  set z₁ := clarkNode α 1 with hz₁
  set z₂ := clarkNode α 2 with hz₂
  have hgap : 0 < z₁ - z₂ := by linarith [clarkNode_two_lt_one α]
  obtain ⟨ψ, hψ, heq, hψz₂⟩ := clark_trial_data hα
  have hψreal := hψ.real
  have hGre := clark_re_psi heq hψreal
  -- `ψ(z₂)` and the sign data
  have hψz₂re : (ψ (z₂ : ℂ)).re = -T.γ := by
    rw [hψz₂]; exact T.hderiv
  have hγ := T.hγ
  have hψz₁ : ψ (z₁ : ℂ) = 0 := by
    have h := heq (z₁ : ℂ)
    rw [clarkExtremal_at_one hα] at h
    have hne : (z₁ : ℂ) - (z₂ : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (fun h' => by have := Complex.ofReal_injective h'; linarith)
    exact (mul_eq_zero.mp h.symm).resolve_right hne
  have hψnode : ∀ n : ℕ, 1 ≤ n → n ≠ 2 → ψ (clarkNode α n : ℂ) = 0 := by
    intro n hn hn2
    have h := heq (clarkNode α n : ℂ)
    rw [clarkExtremal_node_zero hα hn] at h
    have hne : (clarkNode α n : ℂ) - (clarkNode α 2 : ℂ) ≠ 0 := by
      refine sub_ne_zero.mpr (fun h' => ?_)
      have := Complex.ofReal_injective h'
      rcases lt_or_gt_of_ne hn2 with hl | hl
      · have hn1 : n = 1 := by omega
        subst hn1
        linarith [clarkNode_two_lt_one α]
      · have := clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) hl α
        linarith
    exact (mul_eq_zero.mp h.symm).resolve_right hne
  -- the integral of `ψ`
  have hsum := clark_hasSum_re hα hψ
  have hint_ψ : ∫ x : ℝ, (ψ (x : ℂ)).re = T.w * (ψ (z₂ : ℂ)).re := by
    let b : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} :=
      ⟨(z₂ : ℂ), clarkNode_zero hα (by norm_num)⟩
    have hsingle : HasSum (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z -
        (Real.sin α : ℂ) * deriv airyAiC z = 0} => (ψ z.1).re / clarkK z.1.re)
        ((ψ b.1).re / clarkK b.1.re) := by
      refine hasSum_single b fun z hz => ?_
      obtain ⟨n, hn, hzn⟩ := (psiClark_zero_iff hα z.1).1 z.2
      have hn2 : n ≠ 2 := by
        rintro rfl
        exact hz (Subtype.ext (by simpa [b, hz₂] using hzn))
      rw [hzn, hψnode n hn hn2]
      simp
    have := hsum.unique hsingle
    rw [this]
    simp only [b, Complex.ofReal_re]
    rw [div_eq_inv_mul]
    rfl
  -- the trial family `G + δ W`, `W = -ψ`
  set W : ℂ → ℂ := fun u => (((-1 : ℝ)) : ℂ) * ψ u with hW
  have hWG : AiryG W := hψ.smul (-1)
  have hWint : ∫ x : ℝ, (W (x : ℂ)).re = T.w * T.γ := by
    have : ∀ x : ℝ, (W (x : ℂ)).re = -(ψ (x : ℂ)).re := fun x => by simp [hW]
    simp_rw [this]
    rw [integral_neg, hint_ψ, hψz₂re]
    ring
  have hnn : ∀ δ : ℝ, 0 < δ → δ < z₁ - z₂ → ∀ x : ℝ, x ≤ z₂ + δ →
      0 ≤ (T.G (x : ℂ) + (δ : ℂ) * W (x : ℂ)).re := by
    intro δ hδ hδ1 x hx
    have hre : (T.G (x : ℂ) + (δ : ℂ) * W (x : ℂ)).re =
        (clarkExtremal α (x : ℂ)).re - δ * (ψ (x : ℂ)).re := by
      show ((clarkExtremal α (x : ℂ)) + (δ : ℂ) * ((((-1 : ℝ)) : ℂ) * ψ (x : ℂ))).re = _
      simp [Complex.add_re, Complex.mul_re, hψreal x]
      ring
    rw [hre]
    rcases lt_trichotomy x z₂ with hlt | heq2 | hgt
    · have hG0 := clarkExtremal_nonneg_band hα hlt.le
      have hψ' : (ψ (x : ℂ)).re = (clarkExtremal α (x : ℂ)).re / (x - z₂) := by
        rw [hGre x, ← hz₂]; field_simp [(sub_neg.mpr hlt).ne]
      rw [hψ']
      have hneg : x - z₂ < 0 := by linarith
      have : (clarkExtremal α (x : ℂ)).re - δ * ((clarkExtremal α (x : ℂ)).re / (x - z₂)) =
          (clarkExtremal α (x : ℂ)).re * (1 + δ / (z₂ - x)) := by
        field_simp [hneg.ne, (sub_pos.mpr hlt).ne']
        ring
      rw [this]
      exact mul_nonneg hG0 (by have : 0 < δ / (z₂ - x) := div_pos hδ (by linarith); linarith)
    · have h0 : (clarkExtremal α (z₂ : ℂ)).re = 0 := by
        rw [hz₂, clarkExtremal_at_two hα]; simp
      rw [heq2, h0, hψz₂re]
      nlinarith [mul_pos hδ hγ]
    · have hlt1 : x < z₁ := by linarith
      have hG0 := clarkExtremal_neg_between hα hgt hlt1
      have hψ' : (ψ (x : ℂ)).re = (clarkExtremal α (x : ℂ)).re / (x - z₂) := by
        rw [hGre x, ← hz₂]; field_simp [(sub_pos.mpr hgt).ne']
      rw [hψ']
      have hpos : 0 < x - z₂ := by linarith
      have hle : x - z₂ ≤ δ := by linarith
      have : (clarkExtremal α (x : ℂ)).re - δ * ((clarkExtremal α (x : ℂ)).re / (x - z₂)) =
          (clarkExtremal α (x : ℂ)).re * (1 - δ / (x - z₂)) := by
        field_simp
      rw [this]
      have h1 : 1 ≤ δ / (x - z₂) := by rw [le_div_iff₀ hpos]; linarith
      exact mul_nonneg_of_nonpos_of_nonpos hG0.le (by linarith)
  have hnode : ∀ δ : ℝ, 0 < δ → δ < z₁ - z₂ → ∀ i : Unit,
      0 ≤ (T.G (T.nodes i : ℂ) + (δ : ℂ) * W (T.nodes i : ℂ)).re := by
    intro δ hδ hδ1 i
    show 0 ≤ ((clarkExtremal α (z₁ : ℂ)) + (δ : ℂ) * ((((-1 : ℝ)) : ℂ) * ψ (z₁ : ℂ))).re
    rw [clarkExtremal_at_one hα, hψz₁]
    simp
  -- nonemptiness
  have hne : ∀ δ : ℝ, 0 < δ → (termSet T δ).Nonempty := by
    intro δ hδ
    set c : ℝ := max (max z₁ (z₂ + δ)) (airyZero 1 + 1) with hc
    have hp : 0 < c - airyZero 1 := by
      have := le_max_right (max z₁ (z₂ + δ)) (airyZero 1 + 1); linarith
    have hz1c : z₁ ≤ c := by
      rw [hc]; exact (le_max_left z₁ (z₂ + δ)).trans (le_max_left _ _)
    have hz2c : z₂ + δ ≤ c := by
      rw [hc]; exact (le_max_right z₁ (z₂ + δ)).trans (le_max_left _ _)
    refine ⟨_, airyTrial (c - airyZero 1), airyTrial_G _, airyTrial_ne _ hp, fun i => ?_,
      fun x hx => airyTrial_re_nonneg (by have hx' : x ≤ z₂ + δ := hx; linarith), rfl⟩
    exact airyTrial_re_nonneg (x := z₁) (by linarith)
  obtain ⟨hpos, hlim⟩ := terminal_stability T hne W hWG hWint hgap hnn hnode
  refine ⟨hpos, ?_⟩
  have hnorm : T.w * T.γ / profileMass T.G =
      (Real.cos α ^ 2 - z₂ * Real.sin α ^ 2) /
        ((z₁ - z₂) * (2 * ∫ x in Set.Ioo z₂ z₁, -(clarkExtremal α (x : ℂ)).re)) := by
    rw [clark_wγ hα]
    show _ / (∫ x : ℝ, ‖clarkExtremal α (x : ℂ)‖) = _
    rw [clarkExtremal_l1_norm hα, div_div]
  rw [← hnorm]
  exact hlim

/-- info: 'FormalResearch.ModularBootstrap.Stability.clark_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clark_stability

end FormalResearch.ModularBootstrap.Stability

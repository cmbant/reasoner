module

public import FormalResearch.CohnElkies.CubicNormalFormBridge

/-!
# Lemma `O.4(2)`: the holomorphic remainder `H` and the bound `|H| < 1/4`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of Lemma `O.4(2)`.

For `L ∈ (0, 0.002]` and the normal form `τ(θ) = σ₀ θ (1 + (θ² - θ₀²) η(θ))` of `O4NormalForm`
(the fixed-point profile `η` is part of that structure), the paper's remainder is
`H(θ) = θ⁻³ (τ(θ) - κ₀ θ)` for `θ ≠ 0`. This file proves:

* `even_quotient_differentiableOn` (Q1): the quotient `(η(θ) - η(0)) / θ²` of an even holomorphic
  function extends holomorphically across `0`;
* `even_quotient_bound` (Q2): the maximum-modulus bound for that quotient, from `‖η‖ ≤ B`;
* `O4NormalForm.H_bound` (Q3): `H` extends to a holomorphic function on `D(0, 0.22)` with
  `H(θ) = θ⁻³ (τ(θ) - κ₀ θ)` for `θ ≠ 0` and `|H| ≤ 1/4`. The evenness of `η` is derived from the
  oddness of `τ` (identity theorem, `θ₀ ≠ 0`), and `κ₀ = σ₀ (1 - θ₀² η(0))` from `hasDerivAt_zero`.
  The numerics are `|H| ≤ σ₀ (1/5)(1 + 2 θ₀² / 0.0484) ≤ 1.003 · 0.2 · 1.1008 < 1/4`.

What is covered: everything above, unconditionally given an `O4NormalForm L τ`.  The interval
certificate `M_F ≤ 0.13` enters only through the `eta` field of `O4NormalForm`, which is produced by `o4_normal_form` from
`O4QuotientBound L`; that bound is proved for every `L ∈ (0, 0.002]` as `SignUncertainty.o4QuotientBound`, so an `O4NormalForm L τ`
exists for each such `L`.
Not covered: the iterated-derivative bounds `‖H^{(j)}‖` (optional step Q4 of the brief).
-/

@[expose] public section

open Metric Set Filter Topology Complex

namespace FormalResearch.CohnElkies

/-- **Q1.** The quotient `(η θ - η 0) / θ²` of an even function holomorphic on `D(0, r)` extends
holomorphically across `0`. -/
theorem even_quotient_differentiableOn {η : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ η (ball 0 r)) (he : ∀ θ ∈ ball (0 : ℂ) r, η (-θ) = η θ) :
    ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z (ball 0 r) ∧
      ∀ θ ∈ ball (0 : ℂ) r, θ ≠ 0 → Z θ = (η θ - η 0) / θ ^ 2 := by
  have hball : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self hr)
  have hη0 : HasDerivAt η (deriv η 0) 0 := (hd.differentiableAt hball).hasDerivAt
  have hderiv0 : deriv η 0 = 0 := by
    have hc : HasDerivAt η (deriv η 0) (-(0 : ℂ)) := by simpa using hη0
    have hneg : HasDerivAt (fun θ : ℂ => η (-θ)) (deriv η 0 * -1) 0 :=
      HasDerivAt.comp (0 : ℂ) hc (hasDerivAt_neg' (0 : ℂ))
    have h3 : HasDerivAt η (deriv η 0 * -1) 0 := hneg.congr_of_eventuallyEq (by
      filter_upwards [hball] with x hx
      exact (he x hx).symm)
    linear_combination (1 / 2 : ℂ) * hη0.unique h3
  have hg : DifferentiableOn ℂ (dslope η 0) (ball 0 r) := (differentiableOn_dslope hball).mpr hd
  have hg0 : dslope η 0 0 = 0 := by rw [dslope_same, hderiv0]
  have hZ : DifferentiableOn ℂ (dslope (dslope η 0) 0) (ball 0 r) :=
    (differentiableOn_dslope hball).mpr hg
  refine ⟨dslope (dslope η 0) 0, hZ, fun θ _ hθ => ?_⟩
  rw [dslope_of_ne _ hθ, slope_def_field, hg0, dslope_of_ne _ hθ, slope_def_field]
  simp only [sub_zero]
  ring

/-- info: 'FormalResearch.CohnElkies.even_quotient_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.even_quotient_differentiableOn

/-- **Q2.** Maximum-modulus bound: if `Z` is holomorphic on `D(0, r)` and equals the quotient
`(η θ - η 0) / θ²` off `0`, with `‖η‖ ≤ B` on `D(0, r)`, then `‖Z θ‖ ≤ 2B / r²` on `D(0, r)`. -/
theorem even_quotient_bound {η Z : ℂ → ℂ} {r B : ℝ} (hr : 0 < r)
    (hZ : DifferentiableOn ℂ Z (ball 0 r))
    (hZeq : ∀ θ ∈ ball (0 : ℂ) r, θ ≠ 0 → Z θ = (η θ - η 0) / θ ^ 2)
    (hB : ∀ θ ∈ ball (0 : ℂ) r, ‖η θ‖ ≤ B) :
    ∀ θ ∈ ball (0 : ℂ) r, ‖Z θ‖ ≤ 2 * B / r ^ 2 := by
  have h0 : ‖η 0‖ ≤ B := hB 0 (mem_ball_self hr)
  -- the bound on each sphere `‖θ‖ = ρ < r`, where `Z` is the explicit quotient
  have hsph : ∀ ρ : ℝ, 0 < ρ → ρ < r → ∀ θ ∈ sphere (0 : ℂ) ρ, ‖Z θ‖ ≤ 2 * B / ρ ^ 2 := by
    intro ρ hρ hρr θ hθ
    have hθn : ‖θ‖ = ρ := by simpa using hθ
    have hθ0 : θ ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hθn
      linarith
    have hθb : θ ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, hθn]
      exact hρr
    have hd : ‖η θ - η 0‖ ≤ 2 * B := by
      have := norm_sub_le (η θ) (η 0)
      linarith [hB θ hθb]
    rw [hZeq θ hθb hθ0, norm_div, norm_pow, hθn]
    exact div_le_div_of_nonneg_right hd (by positivity)
  intro θ hθ
  have hθr : ‖θ‖ < r := mem_ball_zero_iff.mp hθ
  have hlim : Tendsto (fun ρ : ℝ => 2 * B / ρ ^ 2) (𝓝[<] r) (𝓝 (2 * B / r ^ 2)) := by
    have hc : ContinuousAt (fun ρ : ℝ => 2 * B / ρ ^ 2) r :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hr.ne')
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ρ in 𝓝[<] r, ‖Z θ‖ ≤ 2 * B / ρ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT hθr] with ρ hρ
    have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hρ.1
    have hd : DiffContOnCl ℂ Z (ball (0 : ℂ) ρ) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball (0 : ℂ) hρ0.ne']
      exact hZ.mono (closedBall_subset_ball hρ.2)
    have hC : ∀ z ∈ frontier (ball (0 : ℂ) ρ), ‖Z z‖ ≤ 2 * B / ρ ^ 2 := by
      intro z hz
      rw [frontier_ball (0 : ℂ) hρ0.ne'] at hz
      exact hsph ρ hρ0 hρ.2 z hz
    have hmem : θ ∈ closure (ball (0 : ℂ) ρ) := subset_closure (mem_ball_zero_iff.mpr hρ.1)
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC hmem
  exact ge_of_tendsto hlim hev

/-- info: 'FormalResearch.CohnElkies.even_quotient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.even_quotient_bound

/-- **Q3 (`O.4(2)`, `|H| < 1/4`).** For an `O4NormalForm L τ` with `0 < L ≤ 0.002` there is a
holomorphic `H` on `D(0, 0.22)` with `H θ = θ⁻³ (τ θ - κ₀ θ)` for `θ ≠ 0` and `‖H θ‖ ≤ 1/4`. -/
theorem O4NormalForm.H_bound {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L)
    (hL2 : L ≤ 0.002) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 0.22) ∧
      (∀ θ ∈ ball (0 : ℂ) 0.22, θ ≠ 0 → H θ = θ⁻¹ ^ 3 * (τ θ - (edgeKappa0 L : ℂ) * θ)) ∧
      ∀ θ ∈ ball (0 : ℂ) 0.22, ‖H θ‖ ≤ 1 / 4 := by
  obtain ⟨η, hηd, hη⟩ := h.eta
  have hball : ball (0 : ℂ) 0.22 ∈ 𝓝 (0 : ℂ) :=
    isOpen_ball.mem_nhds (mem_ball_self (by norm_num))
  have hηb : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 := fun θ hθ => (hη θ hθ).1
  have hσ : 0 < o4Sigma0 L := o4Sigma0_pos hL0
  have hσle : o4Sigma0 L ≤ 1.003 := o4Sigma0_le hL0 hL2
  have ht : 0 < o4Theta0Sq L := o4Theta0Sq_pos hL0
  have htle : o4Theta0Sq L ≤ 0.00244 := o4Theta0Sq_le hL0 hL2
  have hθ0pos : 0 < o4Theta0 L := o4Theta0_pos hL0
  have hθ0sq : o4Theta0 L ^ 2 = o4Theta0Sq L := o4Theta0_sq hL0
  have hθ0lt : o4Theta0 L < 0.05 := o4Theta0_lt hL0 hL2
  -- Evenness of `η` on the whole disc, from the oddness of `τ`.
  have he : ∀ θ ∈ ball (0 : ℂ) 0.22, η (-θ) = η θ := by
    have hmaps : MapsTo (fun θ : ℂ => -θ) (ball (0 : ℂ) 0.22) (ball (0 : ℂ) 0.22) :=
      fun x hx => by simpa [mem_ball_zero_iff, norm_neg] using hx
    have hnegd : DifferentiableOn ℂ (fun θ : ℂ => -θ) (ball (0 : ℂ) 0.22) :=
      differentiableOn_id.neg
    have hdiff : DifferentiableOn ℂ (fun θ : ℂ => η (-θ) - η θ) (ball (0 : ℂ) 0.22) :=
      (hηd.comp hnegd hmaps).sub hηd
    have hana := hdiff.analyticOnNhd isOpen_ball
    -- pointwise: off `0` and off `±θ₀`, the oddness gives `η(-θ) = η θ`
    have hpt : ∀ θ ∈ ball (0 : ℂ) 0.22, θ ≠ 0 → θ ^ 2 - (o4Theta0Sq L : ℂ) ≠ 0 →
        η (-θ) - η θ = 0 := by
      intro θ hθ hθne hne
      have hmθ : -θ ∈ ball (0 : ℂ) 0.22 := hmaps hθ
      have e1 := h.odd θ hθ
      rw [(hη (-θ) hmθ).2, (hη θ hθ).2] at e1
      have key : (o4Sigma0 L : ℂ) * θ * ((θ ^ 2 - (o4Theta0Sq L : ℂ)) * (η (-θ) - η θ)) = 0 := by
        linear_combination (-1 : ℂ) * e1
      have hσc : (o4Sigma0 L : ℂ) * θ ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hσ.ne') hθne
      rcases mul_eq_zero.mp key with h1 | h1
      · exact absurd h1 hσc
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hne
        · exact h2
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun θ : ℂ => η (-θ) - η θ) z = 0 := by
      have hsmall : ball (0 : ℂ) (o4Theta0 L) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hθ0pos
      have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (fun θ : ℂ => η (-θ) - η θ) z = 0 := by
        filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with z hz hz0
        have hz0' : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz0
        have hzr : ‖z‖ < o4Theta0 L := mem_ball_zero_iff.mp hz
        have hzb : z ∈ ball (0 : ℂ) 0.22 := mem_ball_zero_iff.mpr (lt_trans hzr (by linarith))
        have hne : z ^ 2 - (o4Theta0Sq L : ℂ) ≠ 0 := by
          intro hc
          have h2 : z ^ 2 = ((o4Theta0Sq L : ℝ) : ℂ) := sub_eq_zero.mp hc
          have h3 : ‖z‖ ^ 2 = o4Theta0Sq L := by
            have := congrArg norm h2
            rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
            exact this
          nlinarith [mul_pos (sub_pos.mpr hzr) (add_pos_of_pos_of_nonneg hθ0pos (norm_nonneg z))]
        show η (-z) - η z = 0
        rw [sub_eq_zero]
        have := hpt z hzb hz0' hne
        rw [sub_eq_zero] at this
        exact this
      exact hev.frequently
    have hid := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) 0.22).isPreconnected (mem_ball_self (by norm_num)) hfreq
    intro θ hθ
    have := hid hθ
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  obtain ⟨Z, hZd, hZeq⟩ := even_quotient_differentiableOn (η := η) (r := 0.22) (by norm_num) hηd he
  -- the constant `κ₀ = σ₀ (1 - θ₀² η(0))`, from `hasDerivAt_zero`
  have hκ : (edgeKappa0 L : ℂ) = (o4Sigma0 L : ℂ) * (1 - (o4Theta0Sq L : ℂ) * η 0) := by
    have hη0 : HasDerivAt η (deriv η 0) 0 := (hηd.differentiableAt hball).hasDerivAt
    have h1 : HasDerivAt (fun θ : ℂ => θ) 1 0 := hasDerivAt_id' 0
    have h2 : HasDerivAt (fun θ : ℂ => θ ^ 2 - (o4Theta0Sq L : ℂ))
        ((2 : ℕ) * (0 : ℂ) ^ (2 - 1)) 0 := (hasDerivAt_pow 2 (0 : ℂ)).sub_const _
    have h3 : HasDerivAt (fun θ : ℂ => 1 + (θ ^ 2 - (o4Theta0Sq L : ℂ)) * η θ) _ 0 :=
      ((h2.mul hη0).const_add 1)
    have h4 := (h1.mul h3).const_mul (o4Sigma0 L : ℂ)
    have hτd : HasDerivAt τ _ 0 := h4.congr_of_eventuallyEq (by
      filter_upwards [hball] with θ hθ
      exact (hη θ hθ).2)
    have hκeq := h.hasDerivAt_zero.unique hτd
    rw [hκeq]
    ring
  refine ⟨fun θ => (o4Sigma0 L : ℂ) * η θ - (o4Sigma0 L : ℂ) * (o4Theta0Sq L : ℂ) * Z θ,
    (hηd.const_mul _).sub (hZd.const_mul _), ?_, ?_⟩
  · intro θ hθ hθne
    have hτ := (hη θ hθ).2
    have hZe := hZeq θ hθ hθne
    show (o4Sigma0 L : ℂ) * η θ - (o4Sigma0 L : ℂ) * (o4Theta0Sq L : ℂ) * Z θ
        = θ⁻¹ ^ 3 * (τ θ - (edgeKappa0 L : ℂ) * θ)
    rw [hτ, hκ, hZe]
    field_simp
    ring
  · intro θ hθ
    have hZb := even_quotient_bound (η := η) (Z := Z) (r := 0.22) (B := 1 / 5) (by norm_num)
      hZd hZeq hηb θ hθ
    have hnorm : ‖(o4Sigma0 L : ℂ) * η θ - (o4Sigma0 L : ℂ) * (o4Theta0Sq L : ℂ) * Z θ‖
        ≤ ‖(o4Sigma0 L : ℂ) * η θ‖ + ‖(o4Sigma0 L : ℂ) * (o4Theta0Sq L : ℂ) * Z θ‖ :=
      norm_sub_le _ _
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le, Real.norm_of_nonneg ht.le]
      at hnorm
    have a1 : o4Sigma0 L * ‖η θ‖ ≤ o4Sigma0 L * (1 / 5) :=
      mul_le_mul_of_nonneg_left (hηb θ hθ) hσ.le
    have a2 : o4Sigma0 L * o4Theta0Sq L ≤ 1.003 * 0.00244 :=
      mul_le_mul hσle htle ht.le (by norm_num)
    have a3 : o4Sigma0 L * o4Theta0Sq L * ‖Z θ‖ ≤ 1.003 * 0.00244 * (2 * (1 / 5) / 0.22 ^ 2) :=
      mul_le_mul a2 hZb (norm_nonneg _) (by norm_num)
    norm_num at a3 ⊢
    linarith


/-- info: 'FormalResearch.CohnElkies.O4NormalForm.H_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.O4NormalForm.H_bound

end FormalResearch.CohnElkies

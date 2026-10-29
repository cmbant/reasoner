import FormalResearch.FourQubitEntropy.FlipSos

/-!
# The spin-flip pencil of a flip-orthogonal unit vector

`φ` is a unit vector with `s(φ) = φᵀ ε^{⊗4} φ = 0` (the "midpoint" of the spin-flip split of
`thm:fqe-general-envelope`), `φ̃` its spin flip, and `xr φ ρ = φ + ρ φ̃` the pencil. Then
`‖xr‖² = 1 + ρ²`, `s(xr) = 2ρ`, `W₁(xr) = (1 - ρ²)² W₁(φ)`, and, with `h(ρ) = Hval (xr φ ρ)`,
the derivative of `h` is determined by the flip-gradient identity (FG) of `FlipGradientReal.lean`,
because `xr φ ρ + s (xr φ ρ)~ = (1 + ρ s) xr φ ρ'` and `Hval` is homogeneous of degree six:
`(1 - ρ²) h'(ρ) = D(ρ) - 6ρ h(ρ)`, `D = (1/4) Re Y + 32 ρ (1 - ρ²)² (1 + (7/8) W₁(φ))`.
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy

/-- The pencil point `φ + ρ φ̃`. -/
noncomputable def xr (φ : Psi) (ρ : ℝ) : Psi := φ + ρ • flipPsi φ

theorem Hval_smul (c : ℝ) (ψ : Psi) : Hval (c • ψ) = c ^ 6 * Hval ψ := by
  have h := Hval_smulC_aux (c : ℂ) ψ
  rw [← real_smul_eq] at h
  unfold Hval
  rw [h, Complex.normSq_ofReal]
  ring

theorem flipPsi_xr (φ : Psi) (ρ : ℝ) : flipPsi (xr φ ρ) = flipPsi φ + ρ • φ := by
  unfold xr
  rw [flipPsi_add, flipPsi_smul_real, flipPsi_flipPsi]

theorem xr_zero (φ : Psi) : xr φ 0 = φ := by
  unfold xr; simp

/-- `xr φ ρ + s (xr φ ρ)~ = (1 + ρ s) xr φ ρ'`, `ρ' = (ρ + s)/(1 + ρ s)`. -/
theorem xr_step (φ : Psi) (ρ s : ℝ) (h : 1 + ρ * s ≠ 0) :
    xr φ ρ + s • flipPsi (xr φ ρ) = (1 + ρ * s) • xr φ ((ρ + s) / (1 + ρ * s)) := by
  rw [flipPsi_xr]
  funext a b c d
  simp only [xr, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  push_cast
  have h' : (1 + (ρ : ℂ) * s) ≠ 0 := by exact_mod_cast h
  field_simp
  ring

section Pencil

variable {φ : Psi}

theorem normSqPsi_xr (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) (ρ : ℝ) :
    normSqPsi (xr φ ρ) = 1 + ρ ^ 2 := by
  unfold xr
  rw [normSqPsi_pencil, hφ, hs]
  simp

theorem spinFlipForm_xr (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) (ρ : ℝ) :
    spinFlipForm (xr φ ρ) = ((2 * ρ : ℝ) : ℂ) := by
  unfold xr
  rw [spinFlipForm_pencil, hs, hφ]
  simp

theorem blochSq_xr (ρ : ℝ) : blochSq (xr φ ρ) = (1 - ρ ^ 2) ^ 2 * blochSq φ :=
  blochSq_pencil φ ρ

/-- The derivative of `Hval` at `xr φ ρ` along its own spin-flip pencil. -/
theorem hasDerivAt_K (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) (ρ : ℝ) :
    HasDerivAt (fun s : ℝ => Hval (xr φ ρ + s • flipPsi (xr φ ρ)))
      ((Ysum (xr φ ρ) (xr φ ρ).conj).re / 4
        + 32 * ρ * (1 - ρ ^ 2) ^ 2 * (1 + 7 / 8 * blochSq φ)) 0 := by
  have h := flipGradient (xr φ ρ)
  rw [normSqPsi_xr hφ hs, blochSq_xr, spinFlipForm_xr hφ hs] at h
  convert h using 1
  simp only [Complex.ofReal_re, Complex.normSq_ofReal]
  ring

/-- `h(ρ) = Hval (xr φ ρ)` is differentiable on `(-1, 1)` with
`(1 - ρ²) h'(ρ) = D(ρ) - 6ρ h(ρ)`. -/
theorem hasDerivAt_h (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) {ρ : ℝ} (hρ : |ρ| < 1) :
    HasDerivAt (fun σ : ℝ => Hval (xr φ σ))
      (((Ysum (xr φ ρ) (xr φ ρ).conj).re / 4
          + 32 * ρ * (1 - ρ ^ 2) ^ 2 * (1 + 7 / 8 * blochSq φ) - 6 * ρ * Hval (xr φ ρ))
        / (1 - ρ ^ 2)) ρ := by
  have hρ2 : 1 - ρ ^ 2 ≠ 0 := by
    have : ρ ^ 2 < 1 := by
      have := sq_lt_one_iff_abs_lt_one ρ
      exact this.mpr hρ
    linarith
  have hK := hasDerivAt_K hφ hs ρ
  -- the reparametrisation `σ ↦ (σ - ρ)/(1 - ρσ)`
  have hden : (1 - ρ * ρ) ≠ 0 := by rw [← sq]; exact hρ2
  have hsf : HasDerivAt (fun σ : ℝ => (σ - ρ) / (1 - ρ * σ)) (1 / (1 - ρ ^ 2)) ρ := by
    have h1 : HasDerivAt (fun σ : ℝ => σ - ρ) 1 ρ := (hasDerivAt_id ρ).sub_const ρ
    have h2 : HasDerivAt (fun σ : ℝ => 1 - ρ * σ) (-ρ) ρ := by
      simpa using ((hasDerivAt_id ρ).const_mul ρ).const_sub 1
    have := h1.div h2 hden
    convert this using 1
    field_simp
    ring
  have hsf0 : (ρ - ρ) / (1 - ρ * ρ) = 0 := by simp
  have hcomp : HasDerivAt (fun σ : ℝ => Hval (xr φ ρ + ((σ - ρ) / (1 - ρ * σ)) • flipPsi (xr φ ρ)))
      (((Ysum (xr φ ρ) (xr φ ρ).conj).re / 4
        + 32 * ρ * (1 - ρ ^ 2) ^ 2 * (1 + 7 / 8 * blochSq φ)) * (1 / (1 - ρ ^ 2))) ρ := by
    have := HasDerivAt.scomp_of_eq ρ hK hsf hsf0.symm
    exact this.congr_deriv (by rw [smul_eq_mul]; ring)
  have h3 : (1 - ρ * ρ) / (1 - ρ ^ 2) = 1 := by rw [← sq]; exact div_self hρ2
  have hpow : HasDerivAt (fun σ : ℝ => ((1 - ρ * σ) / (1 - ρ ^ 2)) ^ 6)
      (6 * 1 ^ 5 * (-ρ / (1 - ρ ^ 2))) ρ := by
    have h2 : HasDerivAt (fun σ : ℝ => (1 - ρ * σ) / (1 - ρ ^ 2)) (-ρ / (1 - ρ ^ 2)) ρ := by
      simpa using (((hasDerivAt_id ρ).const_mul ρ).const_sub 1).div_const (1 - ρ ^ 2)
    have := h2.pow 6
    rw [h3] at this
    exact this
  have hmul := hcomp.mul hpow
  have hK0 : Hval (xr φ ρ + ((ρ - ρ) / (1 - ρ * ρ)) • flipPsi (xr φ ρ)) = Hval (xr φ ρ) := by
    rw [hsf0]; simp
  refine (hmul.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [hK0, h3]; ring
  · have hnb : ∀ᶠ σ in nhds ρ, |σ| < 1 :=
      (continuous_abs.continuousAt.eventually_lt continuousAt_const hρ)
    filter_upwards [hnb] with σ hσ
    have h1 : 1 - ρ * σ ≠ 0 := by
      intro h0
      have : |ρ * σ| < 1 := by
        rw [abs_mul]
        calc |ρ| * |σ| < 1 * 1 := mul_lt_mul'' hρ hσ (abs_nonneg _) (abs_nonneg _)
          _ = 1 := by norm_num
      have := abs_lt.mp this
      linarith [this.2]
    set t := (σ - ρ) / (1 - ρ * σ) with ht
    have ht' : t * (1 - ρ * σ) = σ - ρ := by rw [ht]; exact div_mul_cancel₀ _ h1
    have h2 : 1 + ρ * t = (1 - ρ ^ 2) / (1 - ρ * σ) := by
      rw [eq_div_iff h1]; linear_combination ρ * ht'
    have h3 : 1 + ρ * t ≠ 0 := by rw [h2]; exact div_ne_zero hρ2 h1
    have h4 : (ρ + t) / (1 + ρ * t) = σ := by
      rw [div_eq_iff h3]; linear_combination ht' 
    show Hval (xr φ σ) = Hval (xr φ ρ + t • flipPsi (xr φ ρ)) * ((1 - ρ * σ) / (1 - ρ ^ 2)) ^ 6
    rw [xr_step φ ρ t h3, h4, Hval_smul, h2]
    field_simp

/-- The calibrated remainder `M(ρ) = h(ρ)/(1-ρ)⁶ - 16 c ρ²/(1-ρ)⁴`, `c = 1 + (7/8) W₁(φ)`
(`eq:fqe-spin-flip-calibration`, in the parameter `ρ` with `t = 2ρ/(1+ρ²)`). -/
noncomputable def calM (φ : Psi) (ρ : ℝ) : ℝ :=
  Hval (xr φ ρ) / (1 - ρ) ^ 6 - 16 * (1 + 7 / 8 * blochSq φ) * ρ ^ 2 / (1 - ρ) ^ 4

/-- **The exact transport law** `M'(ρ) = ((Re Y + A)/4 + 36 C) / ((1 + ρ)(1 - ρ)⁷) ≥ 0`. -/
theorem calM_hasDerivAt_nonneg (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) {ρ : ℝ}
    (hρ : |ρ| < 1) : ∃ d : ℝ, HasDerivAt (calM φ) d ρ ∧ 0 ≤ d := by
  obtain ⟨A, C, hC, hYA, hh⟩ := flip_sos (xr φ ρ)
  have hρ' := abs_lt.mp hρ
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + ρ := by linarith
  have hh' := hasDerivAt_h hφ hs hρ
  have hlin : HasDerivAt (fun σ : ℝ => 1 - σ) (-1) ρ := by
    simpa using (hasDerivAt_id ρ).const_sub 1
  have hp6 : HasDerivAt (fun σ : ℝ => (1 - σ) ^ 6) (6 * (1 - ρ) ^ 5 * (-1)) ρ :=
    HasDerivAt.comp ρ (hasDerivAt_pow 6 (1 - ρ)) hlin
  have hp4 : HasDerivAt (fun σ : ℝ => (1 - σ) ^ 4) (4 * (1 - ρ) ^ 3 * (-1)) ρ :=
    HasDerivAt.comp ρ (hasDerivAt_pow 4 (1 - ρ)) hlin
  have hq : HasDerivAt (fun σ : ℝ => 16 * (1 + 7 / 8 * blochSq φ) * σ ^ 2) (16 * (1 + 7 / 8 * blochSq φ) * (2 * ρ)) ρ := by
    simpa using ((hasDerivAt_pow 2 ρ).const_mul (16 * (1 + 7 / 8 * blochSq φ)))
  have hM := (hh'.div hp6 (by positivity)).sub (hq.div hp4 (by positivity))
  refine ⟨_, hM, ?_⟩
  have e : (((Ysum (xr φ ρ) (xr φ ρ).conj).re / 4
          + 32 * ρ * (1 - ρ ^ 2) ^ 2 * (1 + 7 / 8 * blochSq φ) - 6 * ρ * Hval (xr φ ρ)) / (1 - ρ ^ 2)
            * (1 - ρ) ^ 6 - Hval (xr φ ρ) * (6 * (1 - ρ) ^ 5 * -1)) / ((1 - ρ) ^ 6) ^ 2
        - (16 * (1 + 7 / 8 * blochSq φ) * (2 * ρ) * (1 - ρ) ^ 4
            - 16 * (1 + 7 / 8 * blochSq φ) * ρ ^ 2 * (4 * (1 - ρ) ^ 3 * -1)) / ((1 - ρ) ^ 4) ^ 2
      = (((Ysum (xr φ ρ) (xr φ ρ).conj).re + A) / 4 + 36 * C) / ((1 + ρ) * (1 - ρ) ^ 7) := by
    have hH : Hval (xr φ ρ) = (A + 144 * C) / 24 := by linarith
    rw [hH]
    have h1' : (1 - ρ ^ 2) = (1 - ρ) * (1 + ρ) := by ring
    rw [h1']
    field_simp
    ring
  rw [e]
  exact div_nonneg (by linarith) (by positivity)

theorem calM_mono (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : calM φ 0 ≤ calM φ r := by
  have hder : ∀ ρ ∈ Set.Icc 0 r, ∃ d, HasDerivAt (calM φ) d ρ ∧ 0 ≤ d := fun ρ hρ =>
    calM_hasDerivAt_nonneg hφ hs (by rw [abs_lt]; constructor <;> linarith [hρ.1, hρ.2])
  have hcont : ContinuousOn (calM φ) (Set.Icc 0 r) := fun ρ hρ => by
    obtain ⟨d, hd, -⟩ := hder ρ hρ
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (calM φ) (interior (Set.Icc 0 r)) := fun ρ hρ => by
    obtain ⟨d, hd, -⟩ := hder ρ (interior_subset hρ)
    exact hd.differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hcont hdiff (fun ρ hρ => by
    obtain ⟨d, hd, hd0⟩ := hder ρ (interior_subset hρ)
    rw [hd.deriv]; exact hd0)
  exact hmono (Set.left_mem_Icc.2 hr0) (Set.right_mem_Icc.2 hr0) hr0

/-- **The pencil envelope**: for a flip-orthogonal unit `φ` and `0 ≤ r < 1`,
`Hval (φ + r φ̃) ≥ (1-r)⁶ Hval φ + 16 (1 + (7/8) W₁(φ)) r² (1-r)²`. -/
theorem envelope_pencil (hφ : normSqPsi φ = 1) (hs : spinFlipForm φ = 0) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    (1 - r) ^ 6 * Hval φ + 16 * (1 + 7 / 8 * blochSq φ) * r ^ 2 * (1 - r) ^ 2 ≤ Hval (xr φ r) := by
  have h := calM_mono hφ hs hr0 hr1
  have h1 : 0 < 1 - r := by linarith
  unfold calM at h
  rw [xr_zero] at h
  simp only [sub_zero, one_pow, div_one, zero_pow (two_ne_zero), mul_zero, zero_div] at h
  have h6 : 0 < (1 - r) ^ 6 := by positivity
  have key : Hval (xr φ r) / (1 - r) ^ 6 - 16 * (1 + 7 / 8 * blochSq φ) * r ^ 2 / (1 - r) ^ 4
      = (Hval (xr φ r) - 16 * (1 + 7 / 8 * blochSq φ) * r ^ 2 * (1 - r) ^ 2) / (1 - r) ^ 6 := by
    field_simp
  rw [key, le_div_iff₀ h6] at h
  linarith

end Pencil


/-! ### From the pencil to an arbitrary unit state with real `s ≥ 0` -/

section Split

variable {ψ : Psi}

/-- `κ = 2r/(1+r²)` for `r = κ/(1+√(1-κ²))`. -/
theorem split_param (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ κ = 2 * r / (1 + r ^ 2) := by
  have hq : 0 < 1 - κ ^ 2 := by nlinarith
  set q := Real.sqrt (1 - κ ^ 2) with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 hq
  have hq2 : q ^ 2 = 1 - κ ^ 2 := Real.sq_sqrt hq.le
  have hq1 : q < 1 ∨ q = 1 := by
    have : q ^ 2 ≤ 1 := by rw [hq2]; nlinarith
    rcases lt_or_eq_of_le (show q ≤ 1 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨κ / (1 + q), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · have h1 : (1 + q) ≠ 0 := by positivity
    field_simp
    nlinarith [hq2]

/-- **General envelope for a unit state with real `s = κ ∈ [0, 1)`** (`thm:fqe-general-envelope`
after the global phase making `s ≥ 0`): `Hval ψ = 4F - 3 W₁ ≥ 4 κ² (1-κ) (1 + (7/8) W₁/(1-κ²))`. -/
theorem envelope_real (hψ : normSqPsi ψ = 1) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hs : spinFlipForm ψ = (κ : ℂ)) :
    4 * κ ^ 2 * (1 - κ) * (1 + 7 / 8 * (blochSq ψ / (1 - κ ^ 2))) ≤ Hval ψ := by
  obtain ⟨r, hr0, hr1, hκr⟩ := split_param κ hκ0 hκ1
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hp : 0 < 1 + r ^ 2 := by positivity
  have hng : normSqPsi (ψ + (-r) • flipPsi ψ) = (1 - r ^ 2) ^ 2 / (1 + r ^ 2) := by
    rw [normSqPsi_pencil, hψ, hs]
    simp only [Complex.ofReal_re]
    rw [hκr]; field_simp; ring
  have hsg : spinFlipForm (ψ + (-r) • flipPsi ψ) = 0 := by
    rw [spinFlipForm_pencil, hs, hψ]
    simp only [Complex.conj_ofReal]
    have h0 : κ + (-r) ^ 2 * κ + 2 * (-r) * 1 = 0 := by rw [hκr]; field_simp; ring
    have h0' := congrArg (Complex.ofReal) h0
    push_cast at h0' ⊢
    linear_combination h0'
  set c₀ : ℝ := Real.sqrt (1 + r ^ 2) / (1 - r ^ 2) with hc0
  have hc0sq : c₀ ^ 2 = (1 + r ^ 2) / (1 - r ^ 2) ^ 2 := by
    rw [hc0, div_pow, Real.sq_sqrt hp.le]
  have hc1 : c₀ * (1 - r ^ 2) = Real.sqrt (1 + r ^ 2) := by
    rw [hc0]; field_simp
  set φ : Psi := c₀ • (ψ + (-r) • flipPsi ψ) with hφdef
  have hφ1 : normSqPsi φ = 1 := by
    rw [hφdef, normSqPsi_smul, hng, hc0sq]; field_simp
  have hφs : spinFlipForm φ = 0 := by
    rw [hφdef, real_smul_eq, spinFlipForm_smulC, hsg]; simp
  have hxr : xr φ r = Real.sqrt (1 + r ^ 2) • ψ := by
    unfold xr
    rw [hφdef, flipPsi_smul_real, flipPsi_add, flipPsi_smul_real, flipPsi_flipPsi]
    funext a b c d
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    rw [← hc1]
    push_cast
    ring
  have hsq : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt hp.le
  have hH : Hval (xr φ r) = (1 + r ^ 2) ^ 3 * Hval ψ := by
    rw [hxr, Hval_smul, show Real.sqrt (1 + r ^ 2) ^ 6 = (1 + r ^ 2) ^ 3 by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hsq]]
  have hW : blochSq (xr φ r) = (1 + r ^ 2) ^ 2 * blochSq ψ := by
    rw [hxr, blochSq_smul, show Real.sqrt (1 + r ^ 2) ^ 4 = (1 + r ^ 2) ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]]
  have hW0 : (1 - r ^ 2) ^ 2 * blochSq φ = (1 + r ^ 2) ^ 2 * blochSq ψ := by
    rw [← blochSq_xr, hW]
  have hHφ : 0 ≤ Hval φ := by
    unfold Hval
    have := sexticF_ge φ
    rw [hφ1] at this
    nlinarith [blochSq_nonneg φ]
  have key := envelope_pencil hφ1 hφs hr0 hr1
  rw [hH] at key
  have hden : 1 - κ ^ 2 = (1 - r ^ 2) ^ 2 / (1 + r ^ 2) ^ 2 := by
    rw [hκr]; field_simp; ring
  have e1 : blochSq ψ / (1 - κ ^ 2) = blochSq φ := by
    rw [hden, div_div_eq_mul_div, div_eq_iff (by positivity)]
    nlinarith [hW0]
  have e2 : 4 * κ ^ 2 * (1 - κ) = 16 * r ^ 2 * (1 - r) ^ 2 / (1 + r ^ 2) ^ 3 := by
    rw [hκr]; field_simp; ring
  have hfin : 4 * κ ^ 2 * (1 - κ) * (1 + 7 / 8 * (blochSq ψ / (1 - κ ^ 2)))
      = 16 * (1 + 7 / 8 * blochSq φ) * r ^ 2 * (1 - r) ^ 2 / (1 + r ^ 2) ^ 3 := by
    rw [e1, e2]; ring
  rw [hfin, div_le_iff₀ (by positivity)]
  have h6 : 0 ≤ (1 - r) ^ 6 * Hval φ := mul_nonneg (by positivity) hHφ
  nlinarith [key, h6]

end Split


/-! ### Arbitrary unit states -/

theorem psi_zero_of_normSqPsi_zero {g : Psi} (h : normSqPsi g = 0) : g = 0 := by
  have h1 : ∀ a b c d, Complex.normSq (g a b c d) ≤ normSqPsi g := by
    intro a b c d
    unfold normSqPsi
    have e4 : Complex.normSq (g a b c d) ≤ ∑ d', Complex.normSq (g a b c d') :=
      Finset.single_le_sum (f := fun d' => Complex.normSq (g a b c d')) (fun _ _ =>
        Complex.normSq_nonneg _) (Finset.mem_univ d)
    have e3 : ∑ d', Complex.normSq (g a b c d') ≤ ∑ c', ∑ d', Complex.normSq (g a b c' d') :=
      Finset.single_le_sum (f := fun c' => ∑ d', Complex.normSq (g a b c' d')) (fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ c)
    have e2 : ∑ c', ∑ d', Complex.normSq (g a b c' d') ≤ ∑ b', ∑ c', ∑ d', Complex.normSq (g a b' c' d') :=
      Finset.single_le_sum (f := fun b' => ∑ c', ∑ d', Complex.normSq (g a b' c' d')) (fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        (Finset.mem_univ b)
    have e1 : ∑ b', ∑ c', ∑ d', Complex.normSq (g a b' c' d')
        ≤ ∑ a', ∑ b', ∑ c', ∑ d', Complex.normSq (g a' b' c' d') :=
      Finset.single_le_sum (f := fun a' => ∑ b', ∑ c', ∑ d', Complex.normSq (g a' b' c' d'))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
    linarith
  funext a b c d
  have := h1 a b c d
  rw [h] at this
  exact Complex.normSq_eq_zero.1 (le_antisymm this (Complex.normSq_nonneg _))

/-- A unit vector with `s(ψ) = 1` is flip-invariant, hence has no Bloch vectors. -/
theorem blochSq_eq_zero_of_spin_one {ψ : Psi} (hψ : normSqPsi ψ = 1) (hs : spinFlipForm ψ = 1) :
    blochSq ψ = 0 := by
  have hng : normSqPsi (ψ + (-1 : ℝ) • flipPsi ψ) = 0 := by
    rw [normSqPsi_pencil, hψ, hs]; norm_num
  have h0 := psi_zero_of_normSqPsi_zero hng
  have hf : flipPsi ψ = ψ := by
    funext a b c d
    have := congrFun (congrFun (congrFun (congrFun h0 a) b) c) d
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, Pi.zero_apply] at this
    push_cast at this
    linear_combination -this
  have h1 := blochSq_pencil ψ 1
  rw [hf] at h1
  have h2 : ψ + (1 : ℝ) • ψ = (2 : ℝ) • ψ := by
    funext a b c d; simp [Complex.real_smul]; ring
  rw [h2, blochSq_smul] at h1
  norm_num at h1
  exact h1

/-- **`thm:fqe-general-envelope`** (inequality part), for unit states: with `τ = |ψᵀ ε^{⊗4} ψ|²`,
`F ≥ (3/4 + 7τ/(8(1+√τ))) W₁ + τ - τ^{3/2}`. -/
theorem general_envelope_unit (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    (3 / 4 + 7 * Complex.normSq (spinFlipForm ψ)
        / (8 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) * blochSq ψ
      + Complex.normSq (spinFlipForm ψ)
      - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
    ≤ sexticF ψ := by
  set s := spinFlipForm ψ with hsdef
  set κ := Real.sqrt (Complex.normSq s) with hκdef
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = Complex.normSq s := Real.sq_sqrt (Complex.normSq_nonneg _)
  obtain ⟨u, hu1, hus⟩ : ∃ u : ℂ, Complex.normSq u = 1 ∧ u ^ 2 * s = (κ : ℂ) := by
    by_cases h0 : s = 0
    · refine ⟨1, by simp, ?_⟩
      have : κ = 0 := by rw [hκdef, h0]; simp
      rw [h0, this]; simp
    · obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((κ : ℂ) / s) (n := 2) two_pos
      have hn : Complex.normSq (κ / s : ℂ) = 1 := by
        rw [map_div₀, Complex.normSq_ofReal, ← hκ2]
        have : κ ≠ 0 := by
          intro h; apply h0
          have : Complex.normSq s = 0 := by rw [← hκ2, h]; ring
          exact Complex.normSq_eq_zero.1 this
        field_simp
      refine ⟨u, ?_, ?_⟩
      · have h2 : Complex.normSq u ^ 2 = 1 := by
          rw [← map_pow, hu, hn]
        have := Complex.normSq_nonneg u
        nlinarith
      · rw [hu]; field_simp
  have hN' : normSqPsi (u • ψ) = 1 := by rw [normSqPsi_smulC, hu1, hψ]; ring
  have hs' : spinFlipForm (u • ψ) = (κ : ℂ) := by rw [spinFlipForm_smulC, hus]
  have hW' : blochSq (u • ψ) = blochSq ψ := by rw [blochSq_smulC, hu1]; simp
  have hF' : sexticF (u • ψ) = sexticF ψ := by rw [sexticF_smulC, hu1]; simp
  have hH' : Hval (u • ψ) = 4 * sexticF ψ - 3 * blochSq ψ := by
    unfold Hval; rw [hN', hW', hF']; ring
  -- κ ≤ 1
  have hκ1 : κ ≤ 1 := by
    have := normSqPsi_nonneg (u • ψ + (-1 : ℝ) • flipPsi (u • ψ))
    rw [normSqPsi_pencil, hN', hs'] at this
    simp only [Complex.ofReal_re] at this
    linarith
  rw [← hκ2]
  rcases lt_or_eq_of_le hκ1 with hlt | heq
  · have h := envelope_real hN' hκ0 hlt hs'
    rw [hH', hW'] at h
    have h1 : 0 < 1 - κ := by linarith
    have h1' : 0 < 1 + κ := by linarith
    have e : 4 * κ ^ 2 * (1 - κ) * (1 + 7 / 8 * (blochSq ψ / (1 - κ ^ 2)))
        = 4 * κ ^ 2 * (1 - κ) + 7 / 2 * κ ^ 2 / (1 + κ) * blochSq ψ := by
      rw [show 1 - κ ^ 2 = (1 - κ) * (1 + κ) by ring]
      field_simp
      ring
    rw [e] at h
    have e2 : 7 * κ ^ 2 / (8 * (1 + κ)) = 7 / 8 * (κ ^ 2 / (1 + κ)) := by
      field_simp
    have e3 : 7 / 2 * κ ^ 2 / (1 + κ) = 7 / 2 * (κ ^ 2 / (1 + κ)) := by ring
    rw [e3] at h
    rw [e2]
    nlinarith [h]
  · -- κ = 1: the state is flip invariant and has no Bloch vectors
    have hs1 : spinFlipForm (u • ψ) = 1 := by rw [hs', heq]; simp
    have hW0 := blochSq_eq_zero_of_spin_one hN' hs1
    rw [hW'] at hW0
    rw [heq, hW0]
    have := sexticF_nonneg ψ
    norm_num
    linarith


/-- **`thm:fqe-general-envelope`, weak form** (`F ≥ (3/4) W₁ + τ - τ^{3/2}`), the consequence used by the
stability estimates. -/
theorem envelope_weak (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    3 / 4 * blochSq ψ + Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ := by
  have h := general_envelope_unit ψ hψ
  have hW := blochSq_nonneg ψ
  have hτ := Complex.normSq_nonneg (spinFlipForm ψ)
  have hx : 0 ≤ 7 * Complex.normSq (spinFlipForm ψ)
      / (8 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) * blochSq ψ := by positivity
  nlinarith [h, hx]

/-- **`prop:fqe-critical-envelope`, inequality (CE)**: every critical unit four-qubit state
(`W₁ = 0`, i.e. all one-qubit marginals maximally mixed) has `F ≥ τ - τ^{3/2}`,
`τ = |ψᵀ ε^{⊗4} ψ|²`. This is the `W₁ = 0` case of `general_envelope_unit`; the equality
characterization and the closed form `F = 1/2 + (7/4) τ + (9/4) perm Θ` are not formalized. -/
theorem critical_envelope (ψ : Psi) (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ := by
  have h := envelope_weak ψ hψ
  rw [hW] at h
  linarith

end FormalResearch.FourQubitEntropy

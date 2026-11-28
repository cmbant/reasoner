module

public import FormalResearch.SignUncertainty.CtBoasOscIbp
public import FormalResearch.SignUncertainty.CtBoasHhatHol
public import FormalResearch.SignUncertainty.CtBoasNeg
public import FormalResearch.SignUncertainty.CtBoasStrip
public import FormalResearch.SignUncertainty.CtBoasMBounds
public import FormalResearch.SignUncertainty.CtBoasBlocks

/-!
# `ct:boas` Step 4–5 (contour infrastructure): exact Fourier identity & strip contour shift

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Steps 3–5.
For `c > 3/2`, `f ∈ 𝒜_c^ε` (`IsHankelEigenfn`), `ε = ±1`, and `u ∈ C_c²(ℝ)` (`supp u ⊆ Icc a' b' ⊂ Ioo a b`):

* `boasB0 L₀ u c a b ζ := ∫ L in a..b, u L * exp (c * ζ * (L - L₀))`: entire transform of `u` shifted to `L₀`;
* `hankelHL_compact_fourier`: exact Plancherel/Fourier identity
  `∫ u(L) h(L) dL = (c / 2π) ∫_ℝ ĥ(iτ) e^{icτL₀} B₀(iτ) dτ`;
* `hankel_contour_shift_norm_le`: Cauchy deformation of the `|τ| ≥ T` tails onto `Re ζ = s ∈ (0, 1/4]`
  plus horizontal connectors at `τ = ±T`, justified by `hankelHhat_continuousOn_strip`,
  `hankelHhat_differentiableOn_strip`, `hankelHhat_bound`, `re_stripS0Tilde_le_const`, and
  `osc_ibp_linear_two` (`O(τ⁻²)` decay on horizontal tops/bottoms as `Y → ∞`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology FourierTransform
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Shifted complex transform `B₀(ζ) = ∫_{a..b} u(L) exp(c ζ (L - L₀)) dL`. -/
noncomputable def boasB0 (L₀ : ℝ) (u : ℝ → ℂ) (c a b : ℝ) (ζ : ℂ) : ℂ :=
  ∫ L in a..b, u L * Complex.exp ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ))

lemma boasB0_differentiable (L₀ : ℝ) (u : ℝ → ℂ) {c a b : ℝ} (hab : a ≤ b) (huc : Continuous u) :
    Differentiable ℂ (boasB0 L₀ u c a b) := by
  intro ζ₀
  obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn huc.continuousOn
  set D : ℝ := max (|a - L₀|) (|b - L₀|)
  have hD0 : 0 ≤ D := le_max_of_le_left (abs_nonneg _)
  set Bnd : ℝ := Mu * (|c| * D * Real.exp (|c| * (‖ζ₀‖ + 1) * D))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := a) (b := b) (μ := volume)
    (F := fun ζ L => u L * Complex.exp ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ)))
    (F' := fun ζ L => u L * ((c : ℂ) * ((L - L₀ : ℝ) : ℂ) * Complex.exp ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ))))
    (x₀ := ζ₀) (s := Metric.ball ζ₀ 1) (bound := fun _ => Bnd) (Metric.ball_mem_nhds ζ₀ one_pos)
    (Filter.Eventually.of_forall fun ζ => (huc.mul (by fun_prop)).aestronglyMeasurable)
    ((huc.mul (by fun_prop)).intervalIntegrable a b)
    ((huc.mul ((continuous_const.mul (by fun_prop)).mul (by fun_prop))).aestronglyMeasurable)
    (by
      refine Filter.Eventually.of_forall fun L hL ζ hζ => ?_
      rw [uIoc_of_le hab] at hL
      have hLI : L ∈ Icc a b := ⟨hL.1.le, hL.2⟩
      have hDL : |L - L₀| ≤ D := by
        rcases le_total L L₀ with h | h
        · rw [abs_of_nonpos (sub_nonpos.2 h)]
          calc -(L - L₀) = L₀ - L := by ring
            _ ≤ L₀ - a := by linarith only [hLI.1]
            _ ≤ |a - L₀| := by rw [abs_sub_comm]; exact le_abs_self _
            _ ≤ D := le_max_left _ _
        · rw [abs_of_nonneg (sub_nonneg.2 h)]
          calc L - L₀ ≤ b - L₀ := by linarith only [hLI.2]
            _ ≤ |b - L₀| := le_abs_self _
            _ ≤ D := le_max_right _ _
      have hnz : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
        have : ‖ζ - ζ₀‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hζ
        calc ‖ζ‖ = ‖ζ₀ + (ζ - ζ₀)‖ := by ring_nf
          _ ≤ ‖ζ₀‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
          _ ≤ ‖ζ₀‖ + 1 := by linarith
      have hexp_bd : ‖Complex.exp ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ))‖ ≤
          Real.exp (|c| * (‖ζ₀‖ + 1) * D) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ?_
        calc ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ)).re
            ≤ ‖(c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ)‖ := Complex.re_le_norm _
          _ = |c| * ‖ζ‖ * |L - L₀| := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |c| * (‖ζ₀‖ + 1) * D := by gcongr
      have huL : ‖u L‖ ≤ Mu := hMu L hLI
      have hMu_nn : 0 ≤ Mu := le_trans (norm_nonneg (u a)) (hMu a ⟨le_rfl, hab⟩)
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      calc ‖u L‖ * (|c| * |L - L₀| * ‖Complex.exp ((c : ℂ) * ζ * ((L - L₀ : ℝ) : ℂ))‖)
          ≤ Mu * (|c| * D * Real.exp (|c| * (‖ζ₀‖ + 1) * D)) := by gcongr
        _ = Bnd := rfl)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun L _ ζ _ => by
      have h := (((hasDerivAt_id' ζ).const_mul (c : ℂ)).mul_const ((L - L₀ : ℝ) : ℂ)).cexp.const_mul (u L)
      exact h.congr_deriv (by ring))
  exact key.2.differentiableAt

/-- Uniform `τ⁻²` bound on `‖boasB0 L₀ u c a b (σ + i τ)‖` for `σ ∈ [0, s]` and `τ ≠ 0`, plus a
uniform constant bound on `[0, s]`. -/
lemma boasB0_strip_decay (L₀ : ℝ) {u : ℝ → ℂ} {c a a' b' b s : ℝ} (hc : 0 < c)
    (haa : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b) (hs0 : 0 ≤ s)
    (hcd : ContDiff ℝ 2 u) (hsupp : ∀ L ∉ Icc a' b', u L = 0) :
    ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧
      (∀ σ ∈ Icc (0 : ℝ) s, ∀ τ : ℝ, ‖boasB0 L₀ u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M₀) ∧
      (∀ σ ∈ Icc (0 : ℝ) s, ∀ {τ : ℝ}, τ ≠ 0 →
        ‖boasB0 L₀ u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M₂ / τ ^ 2) := by
  have hab : a ≤ b := by linarith only [haa, ha'b', hb'b]
  have hKc : IsCompact (Icc a b) := isCompact_Icc
  obtain ⟨Mu0, hMu0⟩ := hKc.exists_bound_of_continuousOn hcd.continuous.continuousOn
  have hcd1 : Continuous (deriv u) := hcd.continuous_deriv (by norm_num)
  have hcd2 : Continuous (iteratedDeriv 2 u) := by
    have h2 : ContDiff ℝ 0 (iteratedDeriv 2 u) := hcd.iteratedDeriv_right (by norm_num)
    exact h2.continuous
  obtain ⟨Mu1, hMu1⟩ := hKc.exists_bound_of_continuousOn hcd1.continuousOn
  obtain ⟨Mu2, hMu2⟩ := hKc.exists_bound_of_continuousOn hcd2.continuousOn
  set Mu : ℝ := max (max Mu0 Mu1) (max Mu2 0)
  have hMu_nn : 0 ≤ Mu := le_max_of_le_right (le_max_right _ _)
  set D : ℝ := max (|a - L₀|) (|b - L₀|)
  have hD0 : 0 ≤ D := le_max_of_le_left (abs_nonneg _)
  set Eσ : ℝ := Real.exp (c * s * D)
  have hEσ_pos : 0 < Eσ := Real.exp_pos _
  set M_unif : ℝ := Mu * Eσ * (1 + c * s) ^ 2
  have hMunif_nn : 0 ≤ M_unif := by positivity
  refine ⟨(b - a) * Mu * Eσ, (b - a) * M_unif / c ^ 2, by positivity, by positivity, ?_, ?_⟩
  · intro σ hσ τ
    unfold boasB0
    have hle : ∀ L ∈ uIoc a b, ‖u L * Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * ((L - L₀ : ℝ) : ℂ))‖ ≤
        Mu * Eσ := by
      intro L hL
      rw [uIoc_of_le hab] at hL
      have hLI : L ∈ Icc a b := ⟨hL.1.le, hL.2⟩
      have hDL : c * σ * (L - L₀) ≤ c * s * D := by
        have h1 : L - L₀ ≤ D := by
          calc L - L₀ ≤ b - L₀ := by linarith only [hLI.2]
            _ ≤ |b - L₀| := le_abs_self _
            _ ≤ D := le_max_right _ _
        calc c * σ * (L - L₀) ≤ c * σ * D := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc.le hσ.1)
          _ ≤ c * s * D := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ.2 hc.le) hD0
      rw [norm_mul, Complex.norm_exp]
      have hre : ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * ((L - L₀ : ℝ) : ℂ)).re = c * σ * (L - L₀) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre]
      have hnorm0 : ‖u L‖ ≤ Mu := (hMu0 L hLI).trans (le_max_of_le_left (le_max_left _ _))
      exact mul_le_mul hnorm0 (Real.exp_le_exp.2 hDL) (Real.exp_pos _).le hMu_nn
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const hle
    calc ‖∫ L in a..b, u L * Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * ((L - L₀ : ℝ) : ℂ))‖
        ≤ Mu * Eσ * |b - a| := hni
      _ = (b - a) * Mu * Eσ := by rw [abs_of_nonneg (sub_nonneg.2 hab)]; ring
  · intro σ hσ τ hτ
    set α : ℝ := c * σ
    set φ : ℝ → ℂ := fun L => Complex.exp ((α * (L - L₀) : ℝ) : ℂ)
    set g : ℝ → ℂ := fun L => u L * φ L
    have hsplit : boasB0 L₀ u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I) =
        Complex.exp (-(Complex.I * ((c * τ * L₀ : ℝ) : ℂ))) *
          ∫ L in a..b, g L * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ)) := by
      unfold boasB0
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun L _ => ?_
      simp only [g, φ, α]
      have hexp : Complex.exp (-(Complex.I * ((c * τ * L₀ : ℝ) : ℂ))) *
          (Complex.exp ((c * σ * (L - L₀) : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ))) =
          Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * ((L - L₀ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [← hexp]; ring
    rw [hsplit, norm_mul,
      show -(Complex.I * ((c * τ * L₀ : ℝ) : ℂ)) = ((-(c * τ * L₀) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have hcd_exp : ContDiff ℝ 2 φ :=
      (Complex.ofRealCLM.contDiff.comp ((contDiff_const (c := α)).mul (contDiff_id.sub contDiff_const))).cexp
    have hcd_g : ContDiff ℝ 2 g := hcd.mul hcd_exp
    have hsupp_g : ∀ L ∉ Icc a' b', g L = 0 := fun L hL => by simp only [g, hsupp L hL, zero_mul]
    have hφ_deriv : ∀ L : ℝ, HasDerivAt φ ((α : ℂ) * φ L) L := fun L => by
      have h := (((hasDerivAt_id L).sub_const L₀).const_mul α).ofReal_comp.cexp
      exact h.congr_deriv (by simp only [φ, id_eq]; push_cast; ring)
    have hderiv_g : ∀ L : ℝ, deriv g L = deriv u L * φ L + u L * ((α : ℂ) * φ L) := fun L => by
      have hu1 : HasDerivAt u (deriv u L) L := (hcd.differentiable (by norm_num) L).hasDerivAt
      exact (hu1.mul (hφ_deriv L)).deriv
    have h2g : ∀ L ∈ Icc a b, ‖iteratedDeriv 2 g L‖ ≤ M_unif := by
      intro L hLI
      have hdu1 : HasDerivAt (deriv u) (iteratedDeriv 2 u L) L := by
        have hcd_du : ContDiff ℝ 1 (deriv u) := by
          have hs : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u := hcd
          rw [contDiff_succ_iff_deriv] at hs
          exact hs.2.2
        have h := (hcd_du.differentiable one_ne_zero L).hasDerivAt
        have h2e : deriv (deriv u) L = iteratedDeriv 2 u L := by
          rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
        rwa [h2e] at h
      have hg' : HasDerivAt (deriv g)
          (iteratedDeriv 2 u L * φ L + 2 * (α : ℂ) * deriv u L * φ L + (α : ℂ) ^ 2 * u L * φ L) L := by
        have hfun : deriv g = fun x => deriv u x * φ x + u x * ((α : ℂ) * φ x) := funext hderiv_g
        rw [hfun]
        have hu1 : HasDerivAt u (deriv u L) L := (hcd.differentiable (by norm_num) L).hasDerivAt
        have hA := hdu1.mul (hφ_deriv L)
        have hB := hu1.mul ((hφ_deriv L).const_mul (α : ℂ))
        exact (hA.add hB).congr_deriv (by ring)
      have h2eq : iteratedDeriv 2 g L =
          (iteratedDeriv 2 u L + 2 * (α : ℂ) * deriv u L + (α : ℂ) ^ 2 * u L) * φ L := by
        rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hg'.deriv]
        ring
      have hφ_bd : ‖φ L‖ ≤ Eσ := by
        rw [Complex.norm_exp]
        have hre : ((α * (L - L₀) : ℝ) : ℂ).re = c * σ * (L - L₀) := rfl
        rw [hre]
        refine Real.exp_le_exp.2 ?_
        have h1 : L - L₀ ≤ D := by
          calc L - L₀ ≤ b - L₀ := by linarith only [hLI.2]
            _ ≤ |b - L₀| := le_abs_self _
            _ ≤ D := le_max_right _ _
        calc c * σ * (L - L₀) ≤ c * σ * D := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc.le hσ.1)
          _ ≤ c * s * D := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ.2 hc.le) hD0
      have hα_bd : 0 ≤ α ∧ α ≤ c * s := ⟨mul_nonneg hc.le hσ.1, mul_le_mul_of_nonneg_left hσ.2 hc.le⟩
      have h0 : ‖u L‖ ≤ Mu := (hMu0 L hLI).trans (le_max_of_le_left (le_max_left _ _))
      have h1 : ‖deriv u L‖ ≤ Mu := (hMu1 L hLI).trans (le_max_of_le_left (le_max_right _ _))
      have h2 : ‖iteratedDeriv 2 u L‖ ≤ Mu := (hMu2 L hLI).trans (le_max_of_le_right (le_max_left _ _))
      rw [h2eq, norm_mul]
      calc ‖iteratedDeriv 2 u L + 2 * (α : ℂ) * deriv u L + (α : ℂ) ^ 2 * u L‖ * ‖φ L‖
          ≤ (‖iteratedDeriv 2 u L‖ + ‖2 * (α : ℂ) * deriv u L‖ + ‖(α : ℂ) ^ 2 * u L‖) * Eσ := by
            gcongr
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (Mu + 2 * α * Mu + α ^ 2 * Mu) * Eσ := by
            gcongr
            · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα_bd.1]
              norm_num; exact mul_le_mul_of_nonneg_left h1 (by linarith only [hα_bd.1])
            · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα_bd.1]
              exact mul_le_mul_of_nonneg_left h0 (by positivity)
        _ = Mu * Eσ * (1 + α) ^ 2 := by ring
        _ ≤ Mu * Eσ * (1 + c * s) ^ 2 := by
            have h1α : 0 ≤ 1 + α := by linarith only [hα_bd.1]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1α (by linarith only [hα_bd.2]) 2) (by positivity)
        _ = M_unif := rfl
    have hct : c * τ ≠ 0 := mul_ne_zero hc.ne' hτ
    have hibp := osc_ibp_linear_two hct haa ha'b' hb'b hcd_g hsupp_g h2g
    refine hibp.trans (le_of_eq ?_)
    field_simp

/-- **Exact Fourier identity** (`ct:boas`): for `c > 3/2`, `f ∈ 𝒜_c^ε`, and `u ∈ C_c²(ℝ)` supported in
`Icc a' b' ⊂ Ioo a b`,
`∫ u(L) h(L) dL = (c / 2π) ∫_ℝ ĥ(iτ) e^{icτL₀} B₀(iτ) dτ`. -/
theorem hankelHL_compact_fourier {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {u : ℝ → ℂ} {a a' b' b : ℝ} (haa : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b)
    (hcd : ContDiff ℝ 2 u) (hsupp : ∀ L ∉ Icc a' b', u L = 0) (L₀ : ℝ) :
    Integrable (fun τ : ℝ => hankelHhat c f ((τ : ℂ) * Complex.I) *
        Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) *
        boasB0 L₀ u c a b ((τ : ℂ) * Complex.I)) ∧
      ∫ L : ℝ, u L * (hankelHL c f L : ℂ) =
        ((c / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, hankelHhat c f ((τ : ℂ) * Complex.I) *
          Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) *
          boasB0 L₀ u c a b ((τ : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hab : a ≤ b := by linarith only [haa, ha'b', hb'b]
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf
  obtain ⟨M₀, M₂, hM₀, hM₂, hg₀, hg₂⟩ := boasB0_strip_decay L₀ hc0 haa ha'b' hb'b le_rfl hcd hsupp
  set gτ : ℝ → ℂ := fun τ =>
    Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) * boasB0 L₀ u c a b ((τ : ℂ) * Complex.I)
  have hgτ_eq : ∀ τ : ℝ, gτ τ = ∫ L : ℝ, u L * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ)) := by
    intro τ
    have h1 : gτ τ = ∫ L in a..b, u L * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ)) := by
      simp only [gτ, boasB0, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun L _ => ?_
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [h1, intervalIntegral.integral_of_le hab]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun L hL => ?_
    have hL' : L ∉ Icc a' b' := fun h => hL ⟨lt_of_lt_of_le haa h.1, (h.2.trans_lt hb'b).le⟩
    simp [hsupp L hL']
  have hgτ_cont : Continuous gτ := by
    have hB_cont := (boasB0_differentiable L₀ u (c := c) hab hcd.continuous).continuous
    exact (by fun_prop : Continuous fun τ : ℝ => Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ))).mul
      (hB_cont.comp (by fun_prop))
  have hgτ_bound : ∀ τ : ℝ, ‖gτ τ‖ ≤ (2 * (M₀ + M₂)) * (1 + τ ^ 2)⁻¹ := by
    intro τ
    have hnorm : ‖gτ τ‖ = ‖boasB0 L₀ u c a b ((0 : ℝ) + (τ : ℂ) * Complex.I)‖ := by
      simp only [gτ, norm_mul, Complex.ofReal_zero, zero_add]
      rw [show (c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ) = ((c * τ * L₀ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hnorm]
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
    by_cases hτ : |τ| ≤ 1
    · have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [sq_abs τ, abs_nonneg τ]
      have h1 : 1 + τ ^ 2 ≤ 2 := by linarith only [hτ2]
      calc ‖boasB0 L₀ u c a b ((0 : ℝ) + (τ : ℂ) * Complex.I)‖ ≤ M₀ := hg₀ 0 h0mem τ
        _ = (2 * M₀) * 2⁻¹ := by ring
        _ ≤ (2 * M₀) * (1 + τ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (by positivity)
        _ ≤ (2 * (M₀ + M₂)) * (1 + τ ^ 2)⁻¹ := by gcongr; linarith only [hM₂]
    · push Not at hτ
      have hτne : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; linarith
      have hτ2 : 1 ≤ τ ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
      have h1 : 1 + τ ^ 2 ≤ 2 * τ ^ 2 := by linarith only [hτ2]
      calc ‖boasB0 L₀ u c a b ((0 : ℝ) + (τ : ℂ) * Complex.I)‖ ≤ M₂ / τ ^ 2 := hg₂ 0 h0mem hτne
        _ = (2 * M₂) * (2 * τ ^ 2)⁻¹ := by ring
        _ ≤ (2 * M₂) * (1 + τ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (by positivity)
        _ ≤ (2 * (M₀ + M₂)) * (1 + τ ^ 2)⁻¹ := by gcongr; linarith only [hM₀]
  have hgτ_int : Integrable gτ :=
    (integrable_inv_one_add_sq.const_mul (2 * (M₀ + M₂))).mono' hgτ_cont.aestronglyMeasurable
      (ae_of_all _ hgτ_bound)
  have hhat_bd : ∀ τ : ℝ, ‖hankelHhat c f ((τ : ℂ) * Complex.I)‖ ≤ hankelMass c f := by
    intro τ
    unfold hankelHhat
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    have h1 : (∫ L : ℝ, ‖Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I) * (L : ℂ))) * (hankelHL c f L : ℂ)‖) =
        ∫ L : ℝ, |hankelHL c f L| := by
      refine integral_congr_ae (ae_of_all _ fun L => ?_)
      dsimp only
      rw [norm_mul,
        show -((c : ℂ) * ((τ : ℂ) * Complex.I) * (L : ℂ)) = ((-(c * τ * L) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, integral_abs_hankelHL hc0 hf]
  have hhat_cont : Continuous (fun τ : ℝ => hankelHhat c f ((τ : ℂ) * Complex.I)) :=
    (hankelHhat_continuousOn_strip hc hf).comp_continuous (by fun_prop) fun τ => by
      show 0 ≤ ((τ : ℂ) * Complex.I).re ∧ ((τ : ℂ) * Complex.I).re ≤ 1 / 4
      simp
  have hprod_int : Integrable (fun τ : ℝ => hankelHhat c f ((τ : ℂ) * Complex.I) *
      Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) *
      boasB0 L₀ u c a b ((τ : ℂ) * Complex.I)) := by
    have hM := hankelMass_nonneg hc0 f
    have hcont_p : Continuous fun τ : ℝ =>
        hankelHhat c f ((τ : ℂ) * Complex.I) *
          Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) *
          boasB0 L₀ u c a b ((τ : ℂ) * Complex.I) := by
      have h1 : Continuous fun τ : ℝ => hankelHhat c f ((τ : ℂ) * Complex.I) * gτ τ := hhat_cont.mul hgτ_cont
      refine h1.congr fun τ => ?_
      simp only [gτ, mul_assoc]
    refine (hgτ_int.norm.const_mul (hankelMass c f)).mono' hcont_p.aestronglyMeasurable ?_
    refine ae_of_all _ fun τ => ?_
    rw [mul_assoc, norm_mul]
    exact mul_le_mul (hhat_bd τ) (le_refl ‖gτ τ‖) (norm_nonneg _) hM
  refine ⟨hprod_int, ?_⟩
  have hu_int : Integrable u := by
    have hi : Integrable (Set.indicator (Icc a b) u) :=
      (integrable_indicator_iff measurableSet_Icc).2 hcd.continuous.continuousOn.integrableOn_Icc
    refine hi.congr (ae_of_all _ fun L => ?_)
    by_cases hL : L ∈ Icc a b
    · rw [indicator_of_mem hL]
    · rw [indicator_of_notMem hL]
      exact (hsupp L fun h => hL ⟨haa.le.trans h.1, h.2.trans hb'b.le⟩).symm
  set R : ℝ := -(2 * π / c) with hRdef
  have hRne : R ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hFu_eq : ∀ w : ℝ, 𝓕 u w = gτ (w * R) := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul, hgτ_eq]
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    simp only [smul_eq_mul, hRdef]
    rw [mul_comm (u L)]
    congr 2
    push_cast
    field_simp [hc0.ne']
  have hFu_int : Integrable (𝓕 u) :=
    (hgτ_int.comp_mul_right' hRne).congr (ae_of_all _ fun w => (hFu_eq w).symm)
  have hinv := hcd.continuous.fourierInv_fourier_eq hu_int hFu_int
  have hpoint : ∀ y : ℝ,
      ((c / (2 * π) : ℝ) : ℂ) *
        ∫ τ : ℝ, Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ = u y := by
    intro y
    have h1 := congrFun hinv y
    rw [Real.fourierInv_eq'] at h1
    simp only [hFu_eq, smul_eq_mul] at h1
    have h2 : ∫ w : ℝ, Complex.exp (↑(2 * π * inner ℝ w y) * Complex.I) * gτ (w * R) =
        ∫ w : ℝ, (fun τ : ℝ => Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ) (w * R) := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      simp only [RCLike.inner_apply, conj_trivial, hRdef]
      congr 2
      push_cast
      field_simp [hc0.ne']
    rw [h2, Measure.integral_comp_mul_right (fun τ : ℝ =>
        Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ) R] at h1
    have hRinv : |R⁻¹| = c / (2 * π) := by
      rw [hRdef, abs_inv, abs_neg, abs_of_pos (by positivity), inv_div]
    rw [hRinv, Complex.real_smul] at h1
    exact h1
  set Ψ : ℝ → ℝ → ℂ := fun y τ =>
    (hankelHL c f y : ℂ) * (Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ)
  have hΨ_int : Integrable (Function.uncurry Ψ) (volume.prod volume) := by
    refine (hh.norm.mul_prod hgτ_int.norm).mono' ?_ (ae_of_all _ fun p => ?_)
    · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (hankelHL c f p.1 : ℂ)) (volume.prod volume) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable).comp_fst
      have m2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          Complex.exp (-(Complex.I * (c : ℂ) * (p.2 : ℂ) * (p.1 : ℂ)))) (volume.prod volume) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (-(Complex.I * (c : ℂ) * (p.2 : ℂ) * (p.1 : ℂ)))).aestronglyMeasurable
      have m3 : AEStronglyMeasurable (fun p : ℝ × ℝ => gτ p.2) (volume.prod volume) :=
        hgτ_int.aestronglyMeasurable.comp_snd
      exact m1.mul (m2.mul m3)
    · obtain ⟨y, τ⟩ := p
      simp only [Ψ, Function.uncurry, norm_mul, Complex.norm_real]
      rw [show -(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ)) = ((-(c * τ * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ∫ L : ℝ, u L * (hankelHL c f L : ℂ)
      = ∫ y : ℝ, (((c / (2 * π) : ℝ) : ℂ) *
          ∫ τ : ℝ, Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ) * (hankelHL c f y : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_); dsimp only; rw [hpoint y]
    _ = ((c / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, ∫ τ : ℝ, Ψ y τ := by
        rw [← integral_const_mul]
        congr 1
        funext y
        calc (((c / (2 * π) : ℝ) : ℂ) *
              ∫ τ : ℝ, Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ) *
            (hankelHL c f y : ℂ)
            = ((c / (2 * π) : ℝ) : ℂ) * ((hankelHL c f y : ℂ) *
              ∫ τ : ℝ, Complex.exp (-(Complex.I * (c : ℂ) * (τ : ℂ) * (y : ℂ))) * gτ τ) := by ring
          _ = ((c / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, Ψ y τ := by rw [← integral_const_mul]
    _ = ((c / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, ∫ y : ℝ, Ψ y τ := by
        rw [integral_integral_swap hΨ_int]
    _ = ((c / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, hankelHhat c f ((τ : ℂ) * Complex.I) *
          Complex.exp ((c : ℂ) * ((τ : ℂ) * Complex.I) * (L₀ : ℂ)) *
          boasB0 L₀ u c a b ((τ : ℂ) * Complex.I) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun τ => ?_)
        have e : (∫ y : ℝ, Ψ y τ) = hankelHhat c f ((τ : ℂ) * Complex.I) * gτ τ := by
          simp only [Ψ, hankelHhat]
          rw [← integral_mul_const]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          rw [mul_left_comm]
          congr 2
          push_cast; ring
        dsimp only
        rw [e, mul_assoc]

/-- **Cauchy contour deformation norm bound** (`ct:boas` Steps 4–5):
deforms `|τ| ≥ T` onto `Re ζ = s ∈ (0, 1/4]` with horizontal connectors at `τ = ±T`, splitting the
integral of `Φ(ζ) = ĥ(ζ) e^{c ζ L₀} B₀(ζ)` along `i ℝ` into 5 integrable norm pieces. -/
theorem hankel_contour_shift_norm_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {u : ℝ → ℂ} {a a' b' b : ℝ}
    (haa : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b) (hcd : ContDiff ℝ 2 u)
    (hsupp : ∀ L ∉ Icc a' b', u L = 0) {T s : ℝ} (hT : 0 < T) (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (L₀ : ℝ) :
    let Φ : ℂ → ℂ := fun ζ =>
      hankelHhat c f ζ * Complex.exp ((c : ℂ) * ζ * (L₀ : ℂ)) * boasB0 L₀ u c a b ζ
    IntegrableOn (fun τ : ℝ => ‖Φ ((τ : ℂ) * Complex.I)‖) (Icc (-T) T) ∧
      IntervalIntegrable (fun σ : ℝ => ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖) volume 0 s ∧
      IntervalIntegrable (fun σ : ℝ => ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖) volume 0 s ∧
      IntegrableOn (fun τ : ℝ => ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) (Ioi T) ∧
      IntegrableOn (fun τ : ℝ => ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) (Iio (-T)) ∧
      ‖∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I)‖ ≤
        (∫ τ in Icc (-T) T, ‖Φ ((τ : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖) +
          (∫ τ in Ioi T, ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) +
          (∫ τ in Iio (-T), ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) := by
  intro Φ
  have hc0 : 0 < c := by linarith
  have hab : a ≤ b := by linarith only [haa, ha'b', hb'b]
  have hΦ_cont : ContinuousOn Φ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ s} := by
    have hhat := (hankelHhat_continuousOn_strip hc hf).mono
      (fun ζ (hζ : ζ ∈ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ s}) => ⟨hζ.1, hζ.2.trans hs4⟩)
    have hexp : ContinuousOn (fun ζ : ℂ => Complex.exp ((c : ℂ) * ζ * (L₀ : ℂ)))
        {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ s} := by fun_prop
    have hB : ContinuousOn (boasB0 L₀ u c a b) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ s} :=
      (boasB0_differentiable L₀ u hab hcd.continuous).continuous.continuousOn
    exact (hhat.mul hexp).mul hB
  have hΦ_diff : DifferentiableOn ℂ Φ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < s} := by
    have hhat := (hankelHhat_differentiableOn_strip hc hf).mono
      (fun ζ (hζ : ζ ∈ {ζ : ℂ | 0 < ζ.re ∧ ζ.re < s}) => ⟨hζ.1, hζ.2.trans_le hs4⟩)
    have hexp : DifferentiableOn ℂ (fun ζ : ℂ => Complex.exp ((c : ℂ) * ζ * (L₀ : ℂ)))
        {ζ : ℂ | 0 < ζ.re ∧ ζ.re < s} := by fun_prop
    have hB : DifferentiableOn ℂ (boasB0 L₀ u c a b) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < s} :=
      (boasB0_differentiable L₀ u hab hcd.continuous).differentiableOn
    exact (hhat.mul hexp).mul hB
  obtain ⟨M₀, M₂, hM₀, hM₂, _, hg₂⟩ := boasB0_strip_decay L₀ hc0 haa ha'b' hb'b hs0.le hcd hsupp
  set C_strip : ℝ := 3 * hankelMass c f * Real.exp (c * (π ^ 2 / 1280)) * Real.exp (c * s * |L₀|) * M₂
  have hM := hankelMass_nonneg hc0 f
  have hCstrip_nn : 0 ≤ C_strip := by positivity
  have hbd_strip : ∀ σ ∈ Icc (0 : ℝ) s, ∀ {τ : ℝ}, τ ≠ 0 →
      ‖Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C_strip / τ ^ 2 := by
    intro σ hσ τ hτ
    simp only [Φ]
    rw [norm_mul, norm_mul]
    have h1 : ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        3 * hankelMass c f * Real.exp (c * (π ^ 2 / 1280)) := by
      refine (hankelHhat_bound hc hf hε hσ.1 (hσ.2.trans hs4) τ).trans ?_
      have hs0re := re_stripS0Tilde_le_const hσ.1 (hσ.2.trans hs4) τ
      gcongr
    have h2 : ‖Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (L₀ : ℂ))‖ ≤
        Real.exp (c * s * |L₀|) := by
      rw [Complex.norm_exp]
      have hre : ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (L₀ : ℂ)).re = c * σ * L₀ := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre]
      refine Real.exp_le_exp.2 ?_
      have hσL : σ * L₀ ≤ s * |L₀| :=
        calc σ * L₀ ≤ σ * |L₀| := mul_le_mul_of_nonneg_left (le_abs_self _) hσ.1
          _ ≤ s * |L₀| := mul_le_mul_of_nonneg_right hσ.2 (abs_nonneg _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hσL hc0.le
    have h3 : ‖boasB0 L₀ u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ M₂ / τ ^ 2 := hg₂ σ hσ hτ
    calc ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ *
          ‖Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (L₀ : ℂ))‖ *
          ‖boasB0 L₀ u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (3 * hankelMass c f * Real.exp (c * (π ^ 2 / 1280))) * Real.exp (c * s * |L₀|) * (M₂ / τ ^ 2) := by gcongr
      _ = C_strip / τ ^ 2 := by ring
  set K_T : ℝ := C_strip * (1 + T⁻¹ ^ 2)
  have hmaj : ∀ σ ∈ Icc (0 : ℝ) s, ∀ {τ : ℝ}, T ≤ |τ| →
      ‖Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ K_T * (1 + τ ^ 2)⁻¹ := by
    intro σ hσ τ hτ
    have hτne : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; linarith
    have h1 := hbd_strip σ hσ hτne
    have hτ2 : T ^ 2 ≤ τ ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
    have hden : 1 + τ ^ 2 ≤ (1 + T⁻¹ ^ 2) * τ ^ 2 := by
      have : 1 ≤ T⁻¹ ^ 2 * τ ^ 2 := by
        rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
        exact hτ2
      linarith
    refine h1.trans ?_
    rw [div_eq_mul_inv, show K_T * (1 + τ ^ 2)⁻¹ = C_strip * ((1 + T⁻¹ ^ 2) * (1 + τ ^ 2)⁻¹) by simp only [K_T]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hCstrip_nn
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + T⁻¹ ^ 2) * τ ^ 2) := by gcongr
      _ = 1 + T⁻¹ ^ 2 := by field_simp [pow_ne_zero 2 hτne]
  have hline_cont : ∀ σ ∈ Icc (0 : ℝ) s, Continuous fun τ : ℝ => Φ ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
    intro σ hσ
    exact hΦ_cont.comp_continuous (by fun_prop) fun τ => by simpa using hσ
  have hline_Ioi : ∀ σ ∈ Icc (0 : ℝ) s, IntegrableOn (fun τ : ℝ => Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)) (Ioi T) := by
    intro σ hσ
    refine (integrable_inv_one_add_sq.const_mul K_T).integrableOn.mono'
      (hline_cont σ hσ).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : T < τ) => ?_)
    exact hmaj σ hσ (le_trans hτ.le (le_abs_self τ))
  have hline_Iio : ∀ σ ∈ Icc (0 : ℝ) s, IntegrableOn (fun τ : ℝ => Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)) (Iio (-T)) := by
    intro σ hσ
    refine (integrable_inv_one_add_sq.const_mul K_T).integrableOn.mono'
      (hline_cont σ hσ).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (ae_of_all _ fun τ (hτ : τ < -T) => ?_)
    have : T ≤ |τ| := by rw [abs_of_neg (by linarith only [hτ, hT])]; linarith
    exact hmaj σ hσ this
  have hIcc_int : IntegrableOn (fun τ : ℝ => ‖Φ ((τ : ℂ) * Complex.I)‖) (Icc (-T) T) := by
    have hc0_line : Continuous fun τ : ℝ => ‖Φ ((τ : ℂ) * Complex.I)‖ := by
      have := (hline_cont 0 ⟨le_rfl, hs0.le⟩).norm
      simpa using this
    exact hc0_line.continuousOn.integrableOn_Icc
  have hhor_top : IntervalIntegrable (fun σ : ℝ => ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖) volume 0 s := by
    have hcont : ContinuousOn (fun σ : ℝ => ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖) (Icc 0 s) :=
      ContinuousOn.norm (hΦ_cont.comp (by fun_prop) fun σ hσ => by simpa using hσ)
    exact (hcont.mono (by rw [uIcc_of_le hs0.le])).intervalIntegrable
  have hhor_bot : IntervalIntegrable (fun σ : ℝ => ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖) volume 0 s := by
    have hcont : ContinuousOn (fun σ : ℝ => ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖) (Icc 0 s) :=
      ContinuousOn.norm (hΦ_cont.comp (by fun_prop) fun σ hσ => by simpa using hσ)
    exact (hcont.mono (by rw [uIcc_of_le hs0.le])).intervalIntegrable
  refine ⟨hIcc_int, hhor_top, hhor_bot, (hline_Ioi s ⟨hs0.le, le_rfl⟩).norm,
    (hline_Iio s ⟨hs0.le, le_rfl⟩).norm, ?_⟩
  -- Cauchy theorem on `[0, s] × [Y₁, Y₂]`
  have hrect : ∀ Y₁ Y₂ : ℝ,
      (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (Y₁ : ℂ) * Complex.I)) -
        (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (Y₂ : ℂ) * Complex.I)) +
        Complex.I * (∫ τ in Y₁..Y₂, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) -
        Complex.I * (∫ τ in Y₁..Y₂, Φ ((τ : ℂ) * Complex.I)) = 0 := by
    intro Y₁ Y₂
    have hsub1 : [[(⟨0, Y₁⟩ : ℂ).re, (⟨s, Y₂⟩ : ℂ).re]] ×ℂ
        [[(⟨0, Y₁⟩ : ℂ).im, (⟨s, Y₂⟩ : ℂ).im]] ⊆ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ s} := by
      intro ζ hζ
      have h1 : ζ.re ∈ [[(0 : ℝ), s]] := hζ.1
      rw [Set.uIcc_of_le hs0.le] at h1
      exact h1
    have hsub2 : Ioo (min (⟨0, Y₁⟩ : ℂ).re (⟨s, Y₂⟩ : ℂ).re) (max (⟨0, Y₁⟩ : ℂ).re (⟨s, Y₂⟩ : ℂ).re) ×ℂ
        Ioo (min (⟨0, Y₁⟩ : ℂ).im (⟨s, Y₂⟩ : ℂ).im) (max (⟨0, Y₁⟩ : ℂ).im (⟨s, Y₂⟩ : ℂ).im) ⊆
        {ζ : ℂ | 0 < ζ.re ∧ ζ.re < s} := by
      intro ζ hζ
      have h1 := hζ.1
      simp only [min_eq_left hs0.le, max_eq_right hs0.le] at h1
      exact h1
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn Φ ⟨0, Y₁⟩ ⟨s, Y₂⟩
      (hΦ_cont.mono hsub1) (hΦ_diff.mono hsub2)
    simpa [smul_eq_mul] using hcauchy
  have hhor_tend : ∀ e : ℝ, |e| = 1 →
      Tendsto (fun Y : ℝ => ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + ((e * Y : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    intro e he
    have hlim : Tendsto (fun Y : ℝ => C_strip * s * (Y ^ 2)⁻¹) atTop (𝓝 0) := by
      have h2 : Tendsto (fun Y : ℝ => (Y ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
      simpa using h2.const_mul (C_strip * s)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop T] with Y hY
    have hYne : e * Y ≠ 0 := mul_ne_zero
      (fun h => by rw [h, abs_zero] at he; norm_num at he)
      (lt_of_lt_of_le hT hY).ne'
    have hb : ∀ σ ∈ Ι (0 : ℝ) s, ‖Φ ((σ : ℂ) + ((e * Y : ℝ) : ℂ) * Complex.I)‖ ≤ C_strip / Y ^ 2 := by
      intro σ hσ
      rw [uIoc_of_le hs0.le] at hσ
      have := hbd_strip σ ⟨hσ.1.le, hσ.2⟩ hYne
      have hesq : (e * Y) ^ 2 = Y ^ 2 := by
        rw [mul_pow, show e ^ 2 = 1 by nlinarith [sq_abs e], one_mul]
      rwa [hesq] at this
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s) hb
    calc ‖∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + ((e * Y : ℝ) : ℂ) * Complex.I)‖
        ≤ C_strip / Y ^ 2 * |s - 0| := hni
      _ = C_strip * s * (Y ^ 2)⁻¹ := by
          rw [sub_zero, abs_of_pos hs0, div_eq_mul_inv]; ring
  -- Top vertical tail `Ioi T`
  have htop_eq : ∫ τ in Ioi T, Φ ((τ : ℂ) * Complex.I) =
      (∫ τ in Ioi T, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) -
        Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    have hlimL : Tendsto (fun Y : ℝ => ∫ τ in T..Y, Φ ((τ : ℂ) * Complex.I)) atTop
        (𝓝 (∫ τ in Ioi T, Φ ((τ : ℂ) * Complex.I))) := by
      have h0 := hline_Ioi 0 ⟨le_rfl, hs0.le⟩
      have h1 := intervalIntegral_tendsto_integral_Ioi T h0 tendsto_id
      simpa using h1
    have hlimR : Tendsto (fun Y : ℝ => (∫ τ in T..Y, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) -
        Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + ((1 * Y : ℝ) : ℂ) * Complex.I))) atTop
        (𝓝 ((∫ τ in Ioi T, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) -
          Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I))) := by
      have h1 := intervalIntegral_tendsto_integral_Ioi T (hline_Ioi s ⟨hs0.le, le_rfl⟩) tendsto_id
      have h2 := (hhor_tend 1 (by norm_num)).const_mul Complex.I
      simpa using (h1.sub_const _).add h2
    refine tendsto_nhds_unique hlimL (hlimR.congr fun Y => ?_)
    have hr := hrect T Y
    simp only [one_mul] at hr ⊢
    have hr' := congrArg (fun z : ℂ => (-Complex.I) * z) hr
    have hII : (-Complex.I) * Complex.I = (1 : ℂ) := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    simp only [mul_zero, mul_sub, mul_add] at hr'
    rw [← mul_assoc (-Complex.I) Complex.I, ← mul_assoc (-Complex.I) Complex.I, hII, one_mul, one_mul] at hr'
    linear_combination hr'
  -- Bottom vertical tail `Iio (-T)`
  have hbot_eq : ∫ τ in Iio (-T), Φ ((τ : ℂ) * Complex.I) =
      (∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) +
        Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I) := by
    have hcomp : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) s →
        (∫ τ in Iio (-T), Φ ((x : ℂ) + (τ : ℂ) * Complex.I)) =
          ∫ u in Ioi T, Φ ((x : ℂ) + (-u : ℝ) * Complex.I) := by
      intro x _
      rw [← integral_indicator measurableSet_Iio, ← integral_neg_eq_self]
      have : (fun u : ℝ => (Iio (-T)).indicator (fun τ => Φ ((x : ℂ) + (τ : ℂ) * Complex.I)) (-u)) =
          (Ioi T).indicator (fun u => Φ ((x : ℂ) + (-u : ℝ) * Complex.I)) := by
        ext u
        by_cases hu : T < u
        · have hu' : -u ∈ Iio (-T) := by change -u < -T; linarith
          rw [indicator_of_mem hu', indicator_of_mem hu]
        · have hu' : -u ∉ Iio (-T) := by change ¬ (-u < -T); linarith
          rw [indicator_of_notMem hu', indicator_of_notMem hu]
      rw [this, integral_indicator measurableSet_Ioi]
    have hcomp_int : ∀ (x : ℝ), x ∈ Icc (0 : ℝ) s →
        IntegrableOn (fun u : ℝ => Φ ((x : ℂ) + (-u : ℝ) * Complex.I)) (Ioi T) := by
      intro x hx
      refine (integrable_inv_one_add_sq.const_mul K_T).integrableOn.mono'
        ((hline_cont x hx).comp (by fun_prop)).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun u (hu : T < u) => ?_)
      have h1 : T ≤ |-u| := by rw [abs_neg, abs_of_pos (lt_trans hT hu)]; exact hu.le
      simpa using hmaj x hx h1
    have hlimL : Tendsto (fun Y : ℝ => ∫ τ in (-Y)..(-T), Φ ((τ : ℂ) * Complex.I)) atTop
        (𝓝 (∫ τ in Iio (-T), Φ ((τ : ℂ) * Complex.I))) := by
      have h0 : Tendsto (fun Y : ℝ => ∫ u in T..Y, Φ ((-u : ℝ) * Complex.I)) atTop
          (𝓝 (∫ u in Ioi T, Φ ((-u : ℝ) * Complex.I))) := by
        simpa using intervalIntegral_tendsto_integral_Ioi T (hcomp_int 0 ⟨le_rfl, hs0.le⟩) tendsto_id
      have heq0 := hcomp 0 ⟨le_rfl, hs0.le⟩
      simp only [Complex.ofReal_zero, zero_add] at heq0 h0
      rw [← heq0] at h0
      refine h0.congr fun Y => ?_
      simpa using intervalIntegral.integral_comp_neg (a := T) (b := Y) (fun τ => Φ ((τ : ℂ) * Complex.I))
    have hlimR : Tendsto (fun Y : ℝ => (∫ τ in (-Y)..(-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) +
        Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)) -
        Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + ((-1 * Y : ℝ) : ℂ) * Complex.I))) atTop
        (𝓝 ((∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) +
          Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I))) := by
      have h1 : Tendsto (fun Y : ℝ => ∫ u in T..Y, Φ ((s : ℂ) + (-u : ℝ) * Complex.I)) atTop
          (𝓝 (∫ u in Ioi T, Φ ((s : ℂ) + (-u : ℝ) * Complex.I))) :=
        intervalIntegral_tendsto_integral_Ioi T (hcomp_int s ⟨hs0.le, le_rfl⟩) tendsto_id
      rw [← hcomp s ⟨hs0.le, le_rfl⟩] at h1
      have h1' : Tendsto (fun Y : ℝ => ∫ τ in (-Y)..(-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) atTop
          (𝓝 (∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I))) :=
        h1.congr fun Y => by
          simpa using intervalIntegral.integral_comp_neg (a := T) (b := Y)
            (fun τ => Φ ((s : ℂ) + (τ : ℂ) * Complex.I))
      have h2 := (hhor_tend (-1) (by norm_num)).const_mul Complex.I
      simpa using (h1'.add_const _).sub h2
    refine tendsto_nhds_unique hlimL (hlimR.congr fun Y => ?_)
    have hr := hrect (-Y) (-T)
    simp only [neg_one_mul] at hr ⊢
    have hr' := congrArg (fun z : ℂ => Complex.I * z) hr
    simp only [mul_zero, mul_sub, mul_add] at hr'
    rw [← mul_assoc Complex.I Complex.I, ← mul_assoc Complex.I Complex.I, Complex.I_mul_I] at hr'
    linear_combination -hr'
  -- Combine `ℝ = Iic (-T) ∪ Ioc (-T) T ∪ Ioi T`
  have hΦ0_int := (hankelHL_compact_fourier hc hf haa ha'b' hb'b hcd hsupp L₀).1
  have hsplit_all : ∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I) =
      (∫ τ in Iio (-T), Φ ((τ : ℂ) * Complex.I)) +
        (∫ τ in Icc (-T) T, Φ ((τ : ℂ) * Complex.I)) +
        (∫ τ in Ioi T, Φ ((τ : ℂ) * Complex.I)) := by
    have h1 : ∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I) =
        (∫ τ in Iic (-T), Φ ((τ : ℂ) * Complex.I)) + ∫ τ in Ioi (-T), Φ ((τ : ℂ) * Complex.I) := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := -T)]
      exact setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hΦ0_int.integrableOn hΦ0_int.integrableOn
    have h2 : ∫ τ in Ioi (-T), Φ ((τ : ℂ) * Complex.I) =
        (∫ τ in Ioc (-T) T, Φ ((τ : ℂ) * Complex.I)) + ∫ τ in Ioi T, Φ ((τ : ℂ) * Complex.I) := by
      rw [← Ioc_union_Ioi_eq_Ioi (by linarith only [hT] : -T ≤ T)]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hΦ0_int.integrableOn hΦ0_int.integrableOn
    have h3 : ∫ τ in Iic (-T), Φ ((τ : ℂ) * Complex.I) = ∫ τ in Iio (-T), Φ ((τ : ℂ) * Complex.I) :=
      setIntegral_congr_set Iio_ae_eq_Iic.symm
    have h4 : ∫ τ in Ioc (-T) T, Φ ((τ : ℂ) * Complex.I) = ∫ τ in Icc (-T) T, Φ ((τ : ℂ) * Complex.I) :=
      setIntegral_congr_set Ioc_ae_eq_Icc
    rw [h1, h2, h3, h4]; ring
  rw [hsplit_all, hbot_eq, htop_eq]
  have hn_mid : ‖∫ τ in Icc (-T) T, Φ ((τ : ℂ) * Complex.I)‖ ≤ ∫ τ in Icc (-T) T, ‖Φ ((τ : ℂ) * Complex.I)‖ :=
    norm_integral_le_integral_norm _
  have hn_topV : ‖∫ τ in Ioi T, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ ∫ τ in Ioi T, ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_integral_le_integral_norm _
  have hn_botV : ‖∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ ∫ τ in Iio (-T), ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_integral_le_integral_norm _
  have hn_topH : ‖Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      ∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, intervalIntegral.integral_of_le hs0.le, intervalIntegral.integral_of_le hs0.le]
    exact norm_integral_le_integral_norm _
  have hn_botH : ‖Complex.I * ∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖ ≤
      ∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, intervalIntegral.integral_of_le hs0.le, intervalIntegral.integral_of_le hs0.le]
    exact norm_integral_le_integral_norm _
  calc ‖((∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) +
          Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I))) +
          (∫ τ in Icc (-T) T, Φ ((τ : ℂ) * Complex.I)) +
          ((∫ τ in Ioi T, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)) -
            Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I)))‖
      ≤ ‖∫ τ in Iio (-T), Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ +
          ‖Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (-T : ℝ) * Complex.I))‖ +
          ‖∫ τ in Icc (-T) T, Φ ((τ : ℂ) * Complex.I)‖ +
          (‖∫ τ in Ioi T, Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖ +
            ‖Complex.I * (∫ σ in (0 : ℝ)..s, Φ ((σ : ℂ) + (T : ℂ) * Complex.I))‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sub_le _ _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (∫ τ in Icc (-T) T, ‖Φ ((τ : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (T : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..s, ‖Φ ((σ : ℂ) + (-T : ℝ) * Complex.I)‖) +
          (∫ τ in Ioi T, ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) +
          (∫ τ in Iio (-T), ‖Φ ((s : ℂ) + (τ : ℂ) * Complex.I)‖) := by
        linarith only [hn_mid, hn_topV, hn_botV, hn_topH, hn_botH]

end FormalResearch.SignUncertainty

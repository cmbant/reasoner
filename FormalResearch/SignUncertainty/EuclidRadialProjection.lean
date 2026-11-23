module

public import FormalResearch.SignUncertainty.EuclidHankelDictionary
public import FormalResearch.SignUncertainty.SphereAverage
public import FormalResearch.SignUncertainty.FourierCompactSupport

/-!
# The Euclid-to-Hankel step of `gt:7.9`: radial averaging of a sign-uncertainty competitor

Given a sign-uncertainty competitor `f` on `ℝ^{n+1}` (`IsSignWitness ε (n+1) R f`, `ε = ±1`,
`ε f(0) ≤ 0`), its radial average `F = radialAvg f` is a radial competitor with the same radius and the same
value at the origin, `F̂ = ε F` (`fourier_radialAvg`), and `G(Δ) = F(√(2Δ) e₀)` is Hankel-feasible at
`R²/2`: `F` is continuous (`F = ε⁻¹ F̂`), `F ≥ 0` on `‖x‖ ≥ R`, and `F ≠ 0`: otherwise `f ≥ 0` has zero mean
on every sphere of radius `≥ R`, so `f` vanishes there, and `f` and `f̂ = ε f` both have compact support,
which forces `f = 0` (`fourier_compact_support_eq_zero`).

`radialProjection : RadialProjection` and the dictionary `hankel_euclid_dictionary` (`gt:7.9`), unconditional.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace FourierTransform Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The Fourier transform of an integrable function is continuous. -/
lemma continuous_fourier_of_integrable {d : ℕ} {g : EuclSp d → ℂ} (hg : Integrable g) :
    Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hg

/-- A competitor with `ε ≠ 0` is continuous (`f = ε⁻¹ f̂`). -/
lemma IsSignWitness.continuous_ofReal {ε : ℝ} {d : ℕ} {R : ℝ} {f : EuclSp d → ℝ}
    (h : IsSignWitness ε d R f) (hε : ε ≠ 0) : Continuous (fun x => (f x : ℂ)) := by
  have hc : Continuous (𝓕 (fun x : EuclSp d => (f x : ℂ))) :=
    continuous_fourier_of_integrable h.integrable.ofReal
  have : (fun x => (f x : ℂ)) = fun y => ((ε : ℂ))⁻¹ * 𝓕 (fun x : EuclSp d => (f x : ℂ)) y := by
    ext y
    rw [h.fourier_eq y]
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
    field_simp
  rw [this]
  exact continuous_const.mul hc

/-- The real radial average profile `r ↦ |S^n|⁻¹ ∫_{S^n} f(r ω) dω`. -/
noncomputable def realAvg (n : ℕ) (f : EuclSp (n + 1) → ℝ) (r : ℝ) : ℝ :=
  (sphTotal n)⁻¹ * ∫ ω : USph (n + 1), f (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1)

lemma radialAvg_ofReal (n : ℕ) (f : EuclSp (n + 1) → ℝ) (x : EuclSp (n + 1)) :
    radialAvg (fun x => (f x : ℂ)) x = ((realAvg n f ‖x‖ : ℝ) : ℂ) := by
  unfold radialAvg sphMean realAvg
  rw [integral_complex_ofReal]
  push_cast
  rfl

lemma realAvg_zero (n : ℕ) (f : EuclSp (n + 1) → ℝ) : realAvg n f 0 = f 0 := by
  have hpos := sphTotal_pos n
  unfold realAvg
  simp only [zero_smul, integral_const, smul_eq_mul]
  have : (sphMeas (n + 1)).real univ = sphTotal n := rfl
  rw [this]
  field_simp

lemma norm_smul_sphere (r : ℝ) (hr : 0 ≤ r) (ω : USph (n + 1)) :
    ‖r • (ω : EuclSp (n + 1))‖ = r := by
  rw [norm_smul, mem_sphere_zero_iff_norm.1 ω.2, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]

lemma realAvg_nonneg (n : ℕ) {f : EuclSp (n + 1) → ℝ} {R r : ℝ} (hr : 0 ≤ r) (hRr : R ≤ r)
    (hf : ∀ x, R ≤ ‖x‖ → 0 ≤ f x) : 0 ≤ realAvg n f r := by
  unfold realAvg
  refine mul_nonneg (inv_nonneg.2 (sphTotal_pos n).le) (integral_nonneg fun ω => ?_)
  exact hf _ (by rw [norm_smul_sphere r hr]; exact hRr)

/-- A continuous nonnegative function on the sphere of radius `r` with zero mean vanishes. -/
lemma eq_zero_of_realAvg_zero (n : ℕ) {f : EuclSp (n + 1) → ℝ} {r : ℝ} (hf : Continuous f)
    (hnn : ∀ ω : USph (n + 1), 0 ≤ f (r • (ω : EuclSp (n + 1)))) (h : realAvg n f r = 0)
    (ω : USph (n + 1)) : f (r • (ω : EuclSp (n + 1))) = 0 := by
  set g : USph (n + 1) → ℝ := fun ω => f (r • (ω : EuclSp (n + 1))) with hg
  have hgc : Continuous g := hf.comp (by fun_prop)
  have hint : Integrable g (sphMeas (n + 1)) :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∫ ω, g ω ∂sphMeas (n + 1) = 0 := by
    unfold realAvg at h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 (inv_ne_zero (sphTotal_pos n).ne')
    · exact h1
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 h0
  have := (Continuous.ae_eq_iff_eq (sphMeas (n + 1)) hgc continuous_const).1 hae
  exact congrFun this ω

/-- **The Euclid-to-Hankel step of `gt:7.9`** (`RadialProjection`): the radial average of a competitor is
a Hankel-feasible profile at the same threshold, with the same value at the origin. -/
theorem radialProjection : RadialProjection := by
  intro d hd ε hε R f hW h0
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hR : 0 < R := hW.pos_radius hε h0
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc]
  set fc : EuclSp (n + 1) → ℂ := fun x => (f x : ℂ) with hfc
  have hfint : Integrable fc := hW.integrable.ofReal
  have hW' : ∀ y, 𝓕 fc y = (ε : ℂ) * fc y := hW.fourier_eq
  set G : ℝ → ℝ := fun Δ => realAvg n f (√(2 * Δ)) with hG
  have hFG : ∀ x : EuclSp (n + 1), radialAvg fc x = ((G (‖x‖ ^ 2 / 2) : ℝ) : ℂ) := by
    intro x
    have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
      rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg x)
    rw [hfc, radialAvg_ofReal]
    simp only [hG, e]
  have hFour : ∀ y, 𝓕 (radialAvg fc) y = (ε : ℂ) * radialAvg fc y := by
    intro y
    rw [fourier_radialAvg hfint y]
    unfold radialAvg sphMean
    simp_rw [hW']
    rw [integral_const_mul]
    ring
  have hFcont : Continuous (radialAvg fc) := by
    have : radialAvg fc = fun y => (ε : ℂ)⁻¹ * 𝓕 (radialAvg fc) y := by
      ext y
      rw [hFour y]
      have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
      field_simp
    rw [this]
    exact continuous_const.mul (continuous_fourier_of_integrable (integrable_radialAvg hfint))
  set e₀ : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with he₀
  have hne : ‖e₀‖ = 1 := by rw [he₀, PiLp.norm_single]; simp
  have hGe : ∀ Δ, G Δ = (radialAvg fc (√(2 * Δ) • e₀)).re := by
    intro Δ
    rw [radialAvg_ofReal, norm_smul, hne, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
    simp [hG]
  have hGcont : ContinuousOn G (Ici 0) := by
    have : Continuous G := by
      have h1 : Continuous fun Δ : ℝ => (radialAvg fc (√(2 * Δ) • e₀)).re :=
        Complex.continuous_re.comp (hFcont.comp
          ((Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).smul continuous_const))
      exact h1.congr fun Δ => (hGe Δ).symm
    exact this.continuousOn
  have hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) :=
    (integrable_radialAvg hfint).congr (Eventually.of_forall hFG)
  have hGint : IntegrableOn (fun Δ => G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0) :=
    (integrable_radialLift_iff n hn G).1 hint
  have heigen : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform (((n : ℝ) + 1) / 2) G Δ = ε * G Δ := by
    intro Δ hΔ
    have hΔ0 : 0 ≤ Δ := hΔ
    set y : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ) with hy
    have hy2 : ‖y‖ ^ 2 / 2 = Δ := by
      rw [hy, PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]; ring
    have h1 := fourier_radial_hankel n hn hGcont hint y
    have h2 : (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) = radialAvg fc :=
      funext fun x => (hFG x).symm
    rw [h2, hFour y, hFG y, hy2] at h1
    exact_mod_cast h1.symm
  have hG0 : G 0 = f 0 := by simp [hG, realAvg_zero]
  have htail : ∀ Δ ≥ R ^ 2 / 2, 0 ≤ G Δ := by
    intro Δ hΔ
    refine realAvg_nonneg n (Real.sqrt_nonneg _) ?_ hW.tail_nonneg
    exact (Real.le_sqrt hR.le (by have := sq_nonneg R; linarith)).2 (by linarith)
  have hnz : ∃ Δ ∈ Ici (0 : ℝ), G Δ ≠ 0 := by
    by_contra hz
    push Not at hz
    have hfcont : Continuous f := by
      have := Complex.continuous_re.comp (hW.continuous_ofReal hε0)
      exact this.congr (fun x => by simp)
    have hvan : ∀ x : EuclSp (n + 1), R ≤ ‖x‖ → f x = 0 := by
      intro x hx
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx; linarith
      have hr : realAvg n f ‖x‖ = 0 := by
        have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
          rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg x)
        have hGx : G (‖x‖ ^ 2 / 2) = realAvg n f ‖x‖ := by
          show realAvg n f (√(2 * (‖x‖ ^ 2 / 2))) = _
          rw [e]
        rw [← hGx]
        exact hz _ (mem_Ici.2 (by positivity))
      have hnn : ∀ ω : USph (n + 1), 0 ≤ f (‖x‖ • (ω : EuclSp (n + 1))) := fun ω =>
        hW.tail_nonneg _ (by rw [norm_smul_sphere _ (norm_nonneg x)]; exact hx)
      let ω : USph (n + 1) := ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]⟩
      have := eq_zero_of_realAvg_zero n hfcont hnn hr ω
      simpa [ω, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0)] using this
    have hzero : fc = 0 := by
      refine fourier_compact_support_eq_zero (hW.continuous_ofReal hε0) ?_ R (fun y hy => ?_)
      · refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclSp (n + 1)) R) fun x hx => ?_
        have : R ≤ ‖x‖ := by
          rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le
        simp [hfc, hvan x this]
      · rw [hW' y]; simp [hfc, hvan y hy]
    obtain ⟨x, hx⟩ := hW.nonzero
    exact hx (by simpa [hfc] using congrFun hzero x)
  exact ⟨G, ⟨⟨hGcont, hGint, heigen⟩, hnz, by rw [hG0]; exact h0, htail⟩, hG0⟩

/-- **`gt:7.9`, the Euclidean-to-Hankel dictionary** (every integer `d ≥ 2`): `A_sign^+(d)²/2 = T_{d/2}^{+1}`
and `A_sign^-(d)²/2 = T_{d/2}^{-1,0}`. -/
theorem hankel_euclid_dictionary (d : ℕ) (hd : 2 ≤ d) :
    aSignPos d ^ 2 / 2 = hankelT 1 ((d : ℝ) / 2) ∧ aSignNeg d ^ 2 / 2 = hankelT0 ((d : ℝ) / 2) :=
  hankel_euclid_dictionary_of_radial_projection radialProjection d hd

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.radialProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialProjection

/-- info: 'FormalResearch.SignUncertainty.hankel_euclid_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_euclid_dictionary

end FormalResearch.SignUncertainty

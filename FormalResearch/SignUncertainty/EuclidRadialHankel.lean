module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import FormalResearch.SignUncertainty.EuclidRadialFourier

/-!
# The radial Fourier transform on `ℝ^d` is the Hankel transform (`d = n + 1 ≥ 2`)

For `G` continuous on `[0,∞)` with `x ↦ G(‖x‖²/2)` integrable on `ℝ^{n+1}`, `n ≥ 1`,
`𝓕 (G(‖·‖²/2)) (r e₀) = 𝓗_{(n+1)/2} G (r²/2)` for `r ≥ 0` (`fourier_radial_single_hankel`), with the
real-order Bessel kernel of `HankelBessel.lean`.

Route (every integer `n ≥ 1`, odd and even): slice `ℝ^{n+1} = ℝ × ℝ^n` (`fourier_radial_single`), polar
coordinates in the `(u, ρ)` half plane, the Poisson integral for `besselNorm` (`besselNorm_eq_integral`)
for the angular integral, the substitution `t = s²/2`, and the constant identity
`n V_n 2^{(n-1)/2} / P_{(n-1)/2} = (2π)^{(n+1)/2} / Γ((n+1)/2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Membership

/-- The angular integral of the slice integrand. -/
lemma polar_theta_integral (n : ℕ) (hn : 1 ≤ n) (G : ℝ → ℝ) (r s : ℝ) (hs : 0 < s) :
    ∫ θ in Ioo (0 : ℝ) Real.pi, s • sliceH n G r (s * Real.cos θ, s * Real.sin θ) =
      ((s ^ n * G (s ^ 2 / 2) *
        (besselNorm (((n : ℝ) - 1) / 2) (2 * Real.pi * s * r) /
          besselPoissonConst (((n : ℝ) - 1) / 2)) : ℝ) : ℂ) := by
  set ν : ℝ := ((n : ℝ) - 1) / 2 with hν
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hν' : -1 / 2 < ν := by rw [hν]; linarith
  have hpt : ∀ θ : ℝ, s • sliceH n G r (s * Real.cos θ, s * Real.sin θ) =
      ((s ^ n * G (s ^ 2 / 2) : ℝ) : ℂ) * (((Real.sin θ ^ (n - 1) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((2 * Real.pi * s * r : ℝ) : ℂ) * (Real.cos θ : ℂ)))) := by
    intro θ
    have h1 : ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2 = s ^ 2 / 2 := by
      calc ((s * Real.cos θ) ^ 2 + (s * Real.sin θ) ^ 2) / 2
          = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) / 2 := by ring
        _ = s ^ 2 / 2 := by rw [Real.cos_sq_add_sin_sq]; ring
    have h2 : s ^ n = s * s ^ (n - 1) := by
      rw [← pow_succ' s (n - 1), Nat.sub_add_cancel hn]
    simp only [sliceH, sliceF, h1, Complex.real_smul]
    have h3 : -2 * (Real.pi : ℂ) * Complex.I * (((s * Real.cos θ : ℝ) : ℂ) * (r : ℂ)) =
        -(Complex.I * ((2 * Real.pi * s * r : ℝ) : ℂ) * (Real.cos θ : ℂ)) := by push_cast; ring
    rw [h3, h2, mul_pow]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, sinpow_exp_integral n hn, poissonW_exp_integral n hn]
  have hB := besselNorm_eq_integral hν' (2 * Real.pi * s * r)
  have hP := besselPoissonConst_pos hν'
  have hI : ∫ t in (-1 : ℝ)..1, poissonW n t * Real.cos (2 * Real.pi * s * r * t) =
      besselNorm ν (2 * Real.pi * s * r) / besselPoissonConst ν := by
    rw [hB, mul_div_cancel_left₀ _ hP.ne']
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [poissonW, hν]
    congr 2
    ring
  rw [hI]
  push_cast
  ring

/-- The constant identity `n V_n 2^{(n-1)/2} / P_{(n-1)/2} = (2π)^{(n+1)/2} / Γ((n+1)/2)`. -/
lemma radial_constant_identity (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal * (2 : ℝ) ^ (((n : ℝ) - 1) / 2) /
        besselPoissonConst (((n : ℝ) - 1) / 2) =
      (2 * Real.pi) ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hvol : (volume (Metric.ball (0 : EuclSp n) 1)).toReal =
      Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
    rw [EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hG1 : Real.Gamma ((n : ℝ) / 2 + 1) = (n : ℝ) / 2 * Real.Gamma ((n : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hGpos : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hGc : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hν1 : ((n : ℝ) - 1) / 2 + 1 = ((n : ℝ) + 1) / 2 := by ring
  have hν2 : ((n : ℝ) - 1) / 2 + 1 / 2 = (n : ℝ) / 2 := by ring
  have hsq : Real.sqrt Real.pi ^ n * Real.sqrt Real.pi = Real.pi ^ (((n : ℝ) + 1) / 2) := by
    rw [← pow_succ, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    push_cast; ring
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (((n : ℝ) - 1) / 2) = (2 : ℝ) ^ (((n : ℝ) + 1) / 2) := by
    rw [← hν1, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), mul_comm]
  unfold besselPoissonConst
  rw [hvol, hν1, hν2, hG1, Real.mul_rpow (by norm_num) Real.pi_pos.le, ← hsq, ← h2]
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

/-- **The radial Fourier transform at `r e₀` is the Hankel transform** (`n ≥ 1`, `r ≥ 0`). -/
theorem fourier_radial_single_hankel (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) {r : ℝ} (hr : 0 ≤ r) :
    𝓕 (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) (EuclideanSpace.single (0 : Fin (n + 1)) r) =
      ((besselHankelTransform (((n : ℝ) + 1) / 2) G (r ^ 2 / 2) : ℝ) : ℂ) := by
  set ν : ℝ := ((n : ℝ) - 1) / 2 with hν
  set P : ℝ := besselPoissonConst ν with hP
  set c : ℝ := ((n : ℝ) + 1) / 2 with hc
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH := integrableOn_sliceH n hn hG hint r
  rw [fourier_radial_single n hn hG hint r,
    setIntegral_polarCoord_Ioi _ hH (continuous_sliceH n hG r)]
  have h1 : ∀ s ∈ Ioi (0 : ℝ), ∫ θ in Ioo (0 : ℝ) Real.pi,
      s • sliceH n G r (s * Real.cos θ, s * Real.sin θ) =
        ((s ^ n * G (s ^ 2 / 2) * (besselNorm ν (2 * Real.pi * s * r) / P) : ℝ) : ℂ) :=
    fun s hs => polar_theta_integral n hn G r s hs
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 1
  -- real identity
  set Φ : ℝ → ℝ := fun t => (2 * t) ^ ν * G t * (besselNorm ν (2 * Real.pi * r * √(2 * t)) / P) with hΦ
  have h2 : ∀ s ∈ Ioi (0 : ℝ), s ^ n * G (s ^ 2 / 2) * (besselNorm ν (2 * Real.pi * s * r) / P) =
      s • Φ (s ^ 2 / 2) := by
    intro s hs
    have hs0 : 0 < s := hs
    have e1 : 2 * (s ^ 2 / 2) = s ^ 2 := by ring
    have e2 : (s ^ 2) ^ ν = s ^ (n - 1) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le, ← Real.rpow_natCast s (n - 1),
        Nat.cast_sub hn]
      congr 1
      rw [hν]; push_cast; ring
    have e3 : s ^ n = s * s ^ (n - 1) := by
      rw [← pow_succ' s (n - 1), Nat.sub_add_cancel hn]
    simp only [hΦ, e1, e2, Real.sqrt_sq hs0.le, smul_eq_mul, e3]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi h2, setIntegral_sq_div_two_Ioi Φ,
    besselHankelTransform, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hid : (n : ℝ) * (volume (Metric.ball (0 : EuclSp n) 1)).toReal * (2 : ℝ) ^ ν / P =
      (2 * Real.pi) ^ c / Real.Gamma c := radial_constant_identity n hn
  have hk : hankelKernel c (r ^ 2 / 2) t = besselNorm ν (2 * Real.pi * r * √(2 * t)) := by
    unfold hankelKernel hankelPhi
    have hsq : √(r ^ 2 / 2 * t) = r * √(2 * t) / 2 := by
      rw [show r ^ 2 / 2 * t = (r * √(2 * t) / 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring]
      exact Real.sqrt_sq (by positivity)
    rw [hsq, show c - 1 = ν by rw [hc, hν]; ring]
    congr 1
    ring
  unfold hankelRho0
  rw [hk, show c - 1 = ν by rw [hc, hν]; ring, hΦ]
  simp only
  rw [← hid]
  have hPpos : P ≠ 0 := (besselPoissonConst_pos (by rw [hν]; linarith)).ne'
  have e4 : (2 * t) ^ ν = 2 ^ ν * t ^ ν := Real.mul_rpow (by norm_num) ht0.le
  rw [e4]
  field_simp

/-- Two vectors of the same norm are exchanged by a linear isometry equivalence (a reflection). -/
lemma exists_linearIsometryEquiv_map {d : ℕ} {u v : EuclSp d} (h : ‖u‖ = ‖v‖) :
    ∃ A : EuclSp d ≃ₗᵢ[ℝ] EuclSp d, A u = v :=
  ⟨Submodule.reflection (ℝ ∙ (u - v))ᗮ, Submodule.reflection_sub h⟩

/-- **The radial Fourier transform is the Hankel transform** (`gt:7.9`, `d = n + 1 ≥ 2`, every integer
dimension): for `G` continuous on `[0,∞)` with integrable radial lift, and all `y`,
`𝓕 (G(‖·‖²/2)) y = 𝓗_{d/2} G (‖y‖²/2)`. -/
theorem fourier_radial_hankel (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) (y : EuclSp (n + 1)) :
    𝓕 (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) y =
      ((besselHankelTransform (((n : ℝ) + 1) / 2) G (‖y‖ ^ 2 / 2) : ℝ) : ℂ) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_map
    (u := EuclideanSpace.single (0 : Fin (n + 1)) ‖y‖) (v := y)
    (by rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)])
  have hcomp : (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) ∘ A =
      fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ) := by
    ext x; simp [Function.comp_apply]
  have h := Real.fourier_comp_linearIsometry A (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))
    (EuclideanSpace.single (0 : Fin (n + 1)) ‖y‖)
  rw [hcomp, hA] at h
  rw [← h]
  exact fourier_radial_single_hankel n hn hG hint (norm_nonneg y)

/-- Integrability under `t = s²/2`: `∫_{(0,∞)} Φ` converges iff `∫ s Φ(s²/2) ds` does. -/
lemma integrableOn_sq_div_two_iff (Φ : ℝ → ℝ) :
    IntegrableOn Φ (Ioi (0 : ℝ)) ↔ IntegrableOn (fun s : ℝ => s * Φ (s ^ 2 / 2)) (Ioi 0) := by
  have him : (fun s : ℝ => s ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨s, hs, rfl⟩; exact div_pos (sq_pos_of_pos hs) zero_lt_two
    · intro ht
      refine ⟨Real.sqrt (2 * t), Real.sqrt_pos.mpr (mul_pos zero_lt_two ht), ?_⟩
      dsimp only
      rw [Real.sq_sqrt (mul_pos zero_lt_two ht).le]; ring
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) s (Ioi 0) s := fun s _ => by
    have h1 := ((hasDerivAt_pow 2 s).div_const 2).hasDerivWithinAt (s := Ioi 0)
    simpa [Nat.cast_ofNat] using h1
  have hinj : InjOn (fun s : ℝ => s ^ 2 / 2) (Ioi 0) := fun x hx y hy hxy => by
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
    have hsq : x ^ 2 = y ^ 2 := by linarith
    nlinarith [sq_nonneg (x - y)]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj Φ
  rw [him] at h
  rw [h]
  refine integrableOn_congr_fun (fun s hs => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [abs_of_pos hs]

/-- The radial lift `x ↦ G(‖x‖²/2)` of `ℝ^{n+1}` is integrable iff `G ρ₀` is integrable on `(0,∞)`
with `ρ₀` the Hankel weight of `c = (n+1)/2` (any `G : ℝ → ℝ`). -/
theorem integrable_radialLift_iff (n : ℕ) (hn : 1 ≤ n) (G : ℝ → ℝ) :
    Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) ↔
      IntegrableOn (fun t => G t * hankelRho0 (((n : ℝ) + 1) / 2) t) (Ioi 0) := by
  have hdim : Module.finrank ℝ (EuclSp (n + 1)) = n + 1 := finrank_euclideanSpace_fin
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) ↔
      Integrable (fun x : EuclSp (n + 1) => G (‖x‖ ^ 2 / 2)) :=
    ⟨fun h => by simpa using h.re, fun h => h.ofReal⟩
  rw [h0]
  have h1 := integrable_fun_norm_addHaar (volume : Measure (EuclSp (n + 1)))
    (f := fun ρ : ℝ => G (ρ ^ 2 / 2))
  rw [hdim] at h1
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h1
  set ν : ℝ := ((n : ℝ) - 1) / 2 with hν
  set c : ℝ := ((n : ℝ) + 1) / 2 with hc
  rw [h1, integrableOn_sq_div_two_iff (fun t => G t * hankelRho0 c t)]
  set κ : ℝ := (2 * Real.pi) ^ c / Real.Gamma c / (2 : ℝ) ^ ν with hκ
  have hκ0 : 0 < κ := by
    have := Real.Gamma_pos_of_pos (show 0 < c by rw [hc]; linarith)
    positivity
  have key : ∀ s ∈ Ioi (0 : ℝ), s * (G (s ^ 2 / 2) * hankelRho0 c (s ^ 2 / 2)) =
      κ * (s ^ n * G (s ^ 2 / 2)) := by
    intro s hs
    have hs0 : 0 < s := hs
    have e2 : (s ^ 2 / 2) ^ (c - 1) = s ^ (n - 1) / 2 ^ ν := by
      rw [Real.div_rpow (by positivity) (by norm_num), show c - 1 = ν by rw [hc, hν]; ring,
        ← Real.rpow_natCast s 2, ← Real.rpow_mul hs0.le, ← Real.rpow_natCast s (n - 1),
        Nat.cast_sub hn]
      congr 2
      rw [hν]; push_cast; ring
    have e3 : s ^ n = s * s ^ (n - 1) := by
      rw [← pow_succ' s (n - 1), Nat.sub_add_cancel hn]
    unfold hankelRho0
    rw [e2, hκ, e3]
    ring
  rw [integrableOn_congr_fun key measurableSet_Ioi]
  constructor
  · intro h
    exact h.const_mul κ
  · intro h
    have h' := h.const_mul κ⁻¹
    refine IntegrableOn.congr_fun h' (fun s _ => ?_) measurableSet_Ioi
    field_simp

/-! ### Non-vacuity: the Gaussian -/

/-- Non-vacuity witness for `fourier_radial_hankel` and a check of its normalisation: the Gaussian
`G(t) = e^{-2π t}` (radial lift `e^{-π‖x‖²}`, self-dual under `𝓕`) is a Hankel eigenfunction, in every
dimension `d = n + 1 ≥ 2`. -/
theorem besselHankel_gaussian (n : ℕ) (hn : 1 ≤ n) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    besselHankelTransform (((n : ℝ) + 1) / 2) (fun t => Real.exp (-(2 * π * t))) Δ =
      Real.exp (-(2 * π * Δ)) := by
  set G : ℝ → ℝ := fun t => Real.exp (-(2 * π * t)) with hG
  have hcg : ∀ x : EuclSp (n + 1), (G (‖x‖ ^ 2 / 2) : ℂ) = Complex.exp (-(π : ℂ) * ‖x‖ ^ 2) := by
    intro x
    simp only [hG]
    push_cast
    congr 1
    ring
  have hπ : (0 : ℝ) < ((π : ℂ)).re := by simpa using Real.pi_pos
  have hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclSp (n + 1))
      (b := (π : ℂ)) hπ 0 0
    simpa [hcg] using this
  have hGc : ContinuousOn G (Ici 0) := by simp only [hG]; fun_prop
  set y : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ) with hy
  have hy2 : ‖y‖ ^ 2 / 2 = Δ := by
    rw [hy, PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]; ring
  have h := fourier_radial_hankel n hn hGc hint y
  rw [hy2] at h
  have h2 : 𝓕 (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) y =
      ((Real.exp (-(2 * π * Δ)) : ℝ) : ℂ) := by
    simp_rw [hcg]
    rw [fourier_gaussian_innerProductSpace hπ, div_self (by exact_mod_cast Real.pi_ne_zero),
      Complex.one_cpow, one_mul, Complex.ofReal_exp]
    congr 1
    have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((‖y‖ : ℝ) : ℂ) ^ 2 = ((2 * Δ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow]; congr 1; linarith
    rw [this]
    push_cast
    field_simp
  rw [h2] at h
  exact (Complex.ofReal_injective h).symm

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.fourier_radial_single_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radial_single_hankel

/-- info: 'FormalResearch.SignUncertainty.fourier_radial_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radial_hankel

/-- info: 'FormalResearch.SignUncertainty.integrable_radialLift_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrable_radialLift_iff

/-- info: 'FormalResearch.SignUncertainty.besselHankel_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselHankel_gaussian

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.CtOuterMain
public import FormalResearch.SignUncertainty.UctStripSplit
public import FormalResearch.SignUncertainty.UctAiryTransAsymp

/-!
# The regularised strip factor `Z_ε` of `W^seed` (`uct:Wseed-def`, F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, `(uct:Wseed-def)`.  **Proved.**

In `(uct:Wseed-def)` the factor `ζ^{5/2}(1-ζ)^{5/2} H_*(ζ)/G_ε(ζ)` has the double poles of `H_* = π² cos(πζ)/sin²(πζ)` at
`ζ = 0, 1` cancelled by `ζ²(1-ζ)²`, and (for `ε = +1`) the simple zero of `G_+` at `ζ = 1/2` (the zero of `b_{1/2}`)
cancelled by the simple zero of `H_*`.  With `G_ε = b^{[ε=1]} ζ^{1/2}(1-ζ)^{1/2} e^{h}` it equals `Z_ε(ζ) e^{-h(ζ)}`, where

`Z_-(ζ) = ζ²(1-ζ)² H_*(ζ) = cos(πζ)·(π ζ(1-ζ)/sin πζ)²`,
`Z_+(ζ) = ζ²(1-ζ)² H_*(ζ)/b_{1/2}(ζ) = 2 cos²(π/4 - πζ/2)·(π ζ(1-ζ)/sin πζ)²`
(`cos(πζ) = 2 sin w cos w`, `b_{1/2} = tan w`, `w = π/4 - πζ/2`), which is holomorphic on `ℂ ∖ (ℤ ∖ {0,1})`.

* `sincInv z = z / sin z` (value `1` at `0`), `uctSeedZ ε`: `Z_ε`, glued from the charts `zL` (`Re ζ ≤ 1/2`) and `zR`;
* `differentiableOn_uctSeedZ`: `Z_ε` is holomorphic on `-1 < Re ζ < 2`;
* `uctSeedZ_oneSub`, `uctSeedZ_conj`: `Z_ε(1-ζ) = ε Z_ε(ζ)` and real symmetry;
* `uctSeedZ_zero`, `uctSeedZ_one`: `Z_ε(0) = 1`, `Z_ε(1) = ε`;
* `uctSeedZ_bound`: `|Z_ε(σ+iτ)| ≤ C (1+|τ|)⁴ e^{-π|τ|}` on `closedStrip` for `|τ| ≥ 1/2`;
* `seed_factor_eq`: `ζ^{5/2}(1-ζ)^{5/2} H_*(ζ)/G_ε(ζ) = Z_ε(ζ) e^{-h(ζ)}` on `S` (off the zero of `b_{1/2}` for `ε = 1`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtOuter

/-- `z / sin z`, with value `1` at `z = 0`: `(dslope sin 0 z)⁻¹`. -/
noncomputable def sincInv (z : ℂ) : ℂ := (dslope Complex.sin 0 z)⁻¹

lemma dslope_sin_of_ne {z : ℂ} (hz : z ≠ 0) : dslope Complex.sin 0 z = Complex.sin z / z := by
  rw [dslope_of_ne _ hz, slope_def_module, smul_eq_mul]
  simp [div_eq_inv_mul]

lemma dslope_sin_zero : dslope Complex.sin 0 0 = 1 := by
  rw [dslope_same]; simp

lemma sincInv_of_ne {z : ℂ} (hz : z ≠ 0) : sincInv z = z / Complex.sin z := by
  unfold sincInv; rw [dslope_sin_of_ne hz, inv_div]

lemma sincInv_zero : sincInv 0 = 1 := by unfold sincInv; rw [dslope_sin_zero]; simp

lemma sincInv_eq (z : ℂ) : sincInv z = if z = 0 then 1 else z / Complex.sin z := by
  by_cases hz : z = 0
  · simp [hz, sincInv_zero]
  · simp [hz, sincInv_of_ne hz]

lemma differentiable_dslope_sin : Differentiable ℂ (dslope Complex.sin 0) := by
  intro z
  exact ((differentiableOn_dslope Filter.univ_mem).mpr Complex.differentiable_sin.differentiableOn).differentiableAt
    Filter.univ_mem

lemma dslope_sin_ne_zero {z : ℂ} (h : ∀ n : ℤ, n ≠ 0 → z ≠ n * π) : dslope Complex.sin 0 z ≠ 0 := by
  by_cases hz : z = 0
  · rw [hz, dslope_sin_zero]; exact one_ne_zero
  · rw [dslope_sin_of_ne hz]
    refine div_ne_zero (fun hs => ?_) hz
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs
    have hn0 : n ≠ 0 := by rintro rfl; apply hz; rw [← hn]; simp
    exact h n hn0 hn

lemma differentiableAt_sincInv {z : ℂ} (h : ∀ n : ℤ, n ≠ 0 → z ≠ n * π) : DifferentiableAt ℂ sincInv z :=
  (differentiable_dslope_sin z).inv (dslope_sin_ne_zero h)

lemma sincInv_conj (z : ℂ) : sincInv (starRingEnd ℂ z) = starRingEnd ℂ (sincInv z) := by
  rw [sincInv_eq, sincInv_eq]
  by_cases hz : z = 0
  · simp [hz]
  · have : starRingEnd ℂ z ≠ 0 := by simpa using hz
    simp [hz, this, Complex.sin_conj]

/-- The amplitude: `2 cos²(π/4 - πζ/2)` for `ε = 1`, `cos(πζ)` otherwise. -/
noncomputable def seedA (ε : ℝ) (ζ : ℂ) : ℂ :=
  if ε = 1 then 2 * Complex.cos (bArg ζ) ^ 2 else Complex.cos (π * ζ)

/-- Left chart, regular away from `ℤ ∖ {0}`. -/
noncomputable def seedZL (ε : ℝ) (ζ : ℂ) : ℂ := seedA ε ζ * ((1 - ζ) * sincInv (π * ζ)) ^ 2

/-- Right chart, regular away from `ℤ ∖ {1}`. -/
noncomputable def seedZR (ε : ℝ) (ζ : ℂ) : ℂ := seedA ε ζ * (ζ * sincInv (π * (1 - ζ))) ^ 2

/-- The regularised factor `Z_ε = ζ²(1-ζ)² H_* / b^{[ε=1]}`. -/
noncomputable def uctSeedZ (ε : ℝ) (ζ : ℂ) : ℂ := if ζ.re ≤ 1 / 2 then seedZL ε ζ else seedZR ε ζ

lemma sin_pi_one_sub (ζ : ℂ) : Complex.sin (π * (1 - ζ)) = Complex.sin (π * ζ) := by
  rw [show (π : ℂ) * (1 - ζ) = π - π * ζ by ring, Complex.sin_pi_sub]

lemma seedZL_eq_of_sin {ε : ℝ} {ζ : ℂ} (hs : Complex.sin (π * ζ) ≠ 0) :
    seedZL ε ζ = seedA ε ζ * ((π : ℂ) * ζ * (1 - ζ) / Complex.sin (π * ζ)) ^ 2 := by
  have hz : (π : ℂ) * ζ ≠ 0 := fun h => hs (by rw [h]; simp)
  unfold seedZL
  rw [sincInv_of_ne hz]
  congr 1
  field_simp

lemma seedZR_eq_of_sin {ε : ℝ} {ζ : ℂ} (hs : Complex.sin (π * ζ) ≠ 0) :
    seedZR ε ζ = seedA ε ζ * ((π : ℂ) * ζ * (1 - ζ) / Complex.sin (π * ζ)) ^ 2 := by
  have hs' : Complex.sin (π * (1 - ζ)) ≠ 0 := by rw [sin_pi_one_sub]; exact hs
  have hz : (π : ℂ) * (1 - ζ) ≠ 0 := fun h => hs' (by rw [h]; simp)
  unfold seedZR
  rw [sincInv_of_ne hz, sin_pi_one_sub]
  congr 1
  field_simp

lemma seedZL_eq_seedZR {ε : ℝ} {ζ : ℂ} (hs : Complex.sin (π * ζ) ≠ 0) : seedZL ε ζ = seedZR ε ζ := by
  rw [seedZL_eq_of_sin hs, seedZR_eq_of_sin hs]

lemma sin_ne_zero_of_re_half {ζ : ℂ} (h : ζ.re = 1 / 2) : Complex.sin (π * ζ) ≠ 0 := by
  intro hs
  have h1 := norm_sin_arg_sq ζ 0
  have : Complex.sin (π * (ζ - Complex.I * ((0 : ℝ) : ℂ))) = Complex.sin (π * ζ) := by simp
  rw [this, hs, norm_zero] at h1
  rw [h, show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two] at h1
  nlinarith [sq_nonneg (Real.sinh (π * (ζ.im - ((0 : ℝ)))))]

lemma differentiable_seedA (ε : ℝ) : Differentiable ℂ (seedA ε) := by
  unfold seedA
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    exact (by unfold bArg; fun_prop : Differentiable ℂ fun ζ : ℂ => 2 * Complex.cos (bArg ζ) ^ 2)
  · simp only [h, ↓reduceIte]
    fun_prop

lemma ne_int_mul_pi_of_ne {ζ : ℂ} (n : ℤ) (h : ζ ≠ n) : (π : ℂ) * ζ ≠ n * π := by
  intro h'
  apply h
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  rw [h']; ring

lemma differentiableAt_seedZL {ε : ℝ} {ζ : ℂ} (h : ∀ n : ℤ, n ≠ 0 → ζ ≠ n) : DifferentiableAt ℂ (seedZL ε) ζ := by
  unfold seedZL
  refine (differentiable_seedA ε ζ).mul (DifferentiableAt.pow (DifferentiableAt.mul (by fun_prop) ?_) 2)
  have h1 : ∀ n : ℤ, n ≠ 0 → (π : ℂ) * ζ ≠ n * π := fun n hn => ne_int_mul_pi_of_ne n (h n hn)
  exact (differentiableAt_sincInv h1).comp ζ (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * z) ζ)

lemma differentiableAt_seedZR {ε : ℝ} {ζ : ℂ} (h : ∀ n : ℤ, n ≠ 1 → ζ ≠ n) : DifferentiableAt ℂ (seedZR ε) ζ := by
  unfold seedZR
  refine (differentiable_seedA ε ζ).mul (DifferentiableAt.pow (DifferentiableAt.mul (by fun_prop) ?_) 2)
  have h1 : ∀ n : ℤ, n ≠ 0 → (π : ℂ) * (1 - ζ) ≠ n * π := by
    intro n hn
    have : (1 - ζ) ≠ n := by
      intro e; apply h (1 - n) (by intro e2; apply hn; omega)
      push_cast; linear_combination -e
    exact ne_int_mul_pi_of_ne n this
  exact (differentiableAt_sincInv h1).comp ζ (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * (1 - z)) ζ)

lemma int_of_re_mem {ζ : ℂ} {n : ℤ} (h : ζ = n) (h1 : -1 < ζ.re) (h2 : ζ.re < 2) : n = 0 ∨ n = 1 := by
  rw [h] at h1 h2
  simp only [Complex.intCast_re] at h1 h2
  have a : (-1 : ℝ) < n := h1
  have b : (n : ℝ) < 2 := h2
  have a' : (-1 : ℤ) < n := by exact_mod_cast a
  have b' : n < (2 : ℤ) := by exact_mod_cast b
  omega

/-- `Z_ε` is holomorphic on the strip `-1 < Re ζ < 2`. -/
theorem differentiableOn_uctSeedZ (ε : ℝ) : DifferentiableOn ℂ (uctSeedZ ε) {ζ : ℂ | -1 < ζ.re ∧ ζ.re < 2} := by
  intro ζ hζ
  have hL : ∀ ζ : ℂ, -1 < ζ.re → ζ.re < 2 → ∀ n : ℤ, n ≠ 0 → ζ ≠ n → True := fun _ _ _ _ _ _ => trivial
  rcases lt_trichotomy ζ.re (1 / 2) with h | h | h
  · -- left chart
    have hev : uctSeedZ ε =ᶠ[𝓝 ζ] seedZL ε := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h] with z hz
      simp [uctSeedZ, hz.le]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_seedZL (fun n hn e => ?_)
    rcases int_of_re_mem e hζ.1 hζ.2 with h0 | h1
    · exact hn h0
    · have : ζ.re = 1 := by rw [e, h1]; simp
      linarith
  · have hev : uctSeedZ ε =ᶠ[𝓝 ζ] seedZL ε := by
      have hs := sin_ne_zero_of_re_half h
      have hc : ContinuousAt (fun z : ℂ => Complex.sin (π * z)) ζ := by fun_prop
      filter_upwards [hc.eventually_ne hs] with z hz
      by_cases hr : z.re ≤ 1 / 2
      · simp [uctSeedZ, hr]
      · simp only [uctSeedZ, hr, ↓reduceIte]
        exact (seedZL_eq_seedZR hz).symm
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_seedZL (fun n hn e => ?_)
    rcases int_of_re_mem e hζ.1 hζ.2 with h0 | h1
    · exact hn h0
    · have : ζ.re = 1 := by rw [e, h1]; simp
      linarith
  · have hev : uctSeedZ ε =ᶠ[𝓝 ζ] seedZR ε := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with z hz
      have : ¬ z.re ≤ 1 / 2 := not_le.mpr hz
      simp [uctSeedZ, this]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_seedZR (fun n hn e => ?_)
    rcases int_of_re_mem e hζ.1 hζ.2 with h0 | h1
    · have : ζ.re = 0 := by rw [e, h0]; simp
      linarith
    · exact hn h1

lemma seedA_oneSub (ε : ℝ) (ζ : ℂ) : seedA ε (1 - ζ) = (if ε = 1 then 1 else -1) * seedA ε ζ := by
  unfold seedA
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte, one_mul]
    have : bArg (1 - ζ) = -bArg ζ := by unfold bArg; ring
    rw [this, Complex.cos_neg]
  · simp only [h, ↓reduceIte]
    rw [show (π : ℂ) * (1 - ζ) = π - π * ζ by ring, Complex.cos_pi_sub]
    ring

lemma seedZL_oneSub (ε : ℝ) (ζ : ℂ) : seedZL ε (1 - ζ) = (if ε = 1 then 1 else -1) * seedZR ε ζ := by
  unfold seedZL seedZR
  rw [seedA_oneSub]
  simp only [sub_sub_cancel]
  ring

lemma seedZR_oneSub (ε : ℝ) (ζ : ℂ) : seedZR ε (1 - ζ) = (if ε = 1 then 1 else -1) * seedZL ε ζ := by
  unfold seedZL seedZR
  rw [seedA_oneSub]
  simp only [sub_sub_cancel]
  ring

/-- Parity `Z_ε(1-ζ) = ε Z_ε(ζ)` (`ε = ±1`). -/
theorem uctSeedZ_oneSub {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (ζ : ℂ) : uctSeedZ ε (1 - ζ) = ε * uctSeedZ ε ζ := by
  have hsign : (if ε = 1 then (1 : ℂ) else -1) = (ε : ℂ) := by
    rcases hε with h | h
    · simp [h]
    · have : ε ≠ 1 := by rw [h]; norm_num
      simp [h, this]
  have e : ∀ x : ℂ, (if ε = 1 then (1 : ℂ) else -1) * x = ε * x := fun x => by rw [hsign]
  rcases lt_trichotomy ζ.re (1 / 2) with h | h | h
  · have h1 : ¬ (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    simp only [uctSeedZ, h1, h.le, ↓reduceIte, seedZR_oneSub, e]
  · have hs := sin_ne_zero_of_re_half h
    have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    simp only [uctSeedZ, h1, h.le, ↓reduceIte, seedZL_oneSub, e, seedZL_eq_seedZR hs]
  · have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    have h2 : ¬ ζ.re ≤ 1 / 2 := not_le.mpr h
    simp only [uctSeedZ, h1, h2, ↓reduceIte, seedZL_oneSub, e]

/-- Real symmetry. -/
theorem uctSeedZ_conj (ε : ℝ) (ζ : ℂ) : uctSeedZ ε (starRingEnd ℂ ζ) = starRingEnd ℂ (uctSeedZ ε ζ) := by
  have hA : seedA ε (starRingEnd ℂ ζ) = starRingEnd ℂ (seedA ε ζ) := by
    unfold seedA bArg
    by_cases h : ε = 1
    · simp only [h, ↓reduceIte]
      simp [map_div₀, map_mul, map_sub, Complex.cos_conj, map_ofNat]
    · simp only [h, ↓reduceIte]
      rw [← Complex.cos_conj]; simp
  have hs1 : sincInv (π * starRingEnd ℂ ζ) = starRingEnd ℂ (sincInv (π * ζ)) := by
    rw [← sincInv_conj]; congr 1; simp
  have hs2 : sincInv (π * (1 - starRingEnd ℂ ζ)) = starRingEnd ℂ (sincInv (π * (1 - ζ))) := by
    rw [← sincInv_conj]; congr 1; simp
  have hL : seedZL ε (starRingEnd ℂ ζ) = starRingEnd ℂ (seedZL ε ζ) := by
    unfold seedZL
    rw [hA, hs1]
    simp [map_mul, map_pow, map_sub]
  have hR : seedZR ε (starRingEnd ℂ ζ) = starRingEnd ℂ (seedZR ε ζ) := by
    unfold seedZR
    rw [hA, hs2]
    simp [map_mul, map_pow, map_sub]
  unfold uctSeedZ
  simp only [Complex.conj_re]
  split_ifs
  · exact hL
  · exact hR

end FormalResearch.SignUncertainty

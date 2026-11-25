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
    have hn0 : n ≠ 0 := by rintro rfl; apply hz; simpa using hn
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

lemma uctSeedZ_of_le {ε : ℝ} {z : ℂ} (h : z.re ≤ 1 / 2) : uctSeedZ ε z = seedZL ε z := ite_eq_left h

lemma uctSeedZ_of_gt {ε : ℝ} {z : ℂ} (h : 1 / 2 < z.re) : uctSeedZ ε z = seedZR ε z := ite_eq_right (not_le.mpr h)

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
  exact DifferentiableAt.comp (g := sincInv) ζ (differentiableAt_sincInv h1)
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * z) ζ)

lemma differentiableAt_seedZR {ε : ℝ} {ζ : ℂ} (h : ∀ n : ℤ, n ≠ 1 → ζ ≠ n) : DifferentiableAt ℂ (seedZR ε) ζ := by
  unfold seedZR
  refine (differentiable_seedA ε ζ).mul (DifferentiableAt.pow (DifferentiableAt.mul (by fun_prop) ?_) 2)
  have h1 : ∀ n : ℤ, n ≠ 0 → (π : ℂ) * (1 - ζ) ≠ n * π := by
    intro n hn
    have : (1 - ζ) ≠ n := by
      intro e; apply h (1 - n) (by intro e2; apply hn; omega)
      push_cast; linear_combination -e
    exact ne_int_mul_pi_of_ne n this
  exact DifferentiableAt.comp (g := sincInv) ζ (differentiableAt_sincInv h1)
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * (1 - z)) ζ)

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
      exact uctSeedZ_of_le hz.le
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
      · exact uctSeedZ_of_le hr
      · rw [uctSeedZ_of_gt (not_le.mp hr)]
        exact (seedZL_eq_seedZR hz).symm
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_seedZL (fun n hn e => ?_)
    rcases int_of_re_mem e hζ.1 hζ.2 with h0 | h1
    · exact hn h0
    · have : ζ.re = 1 := by rw [e, h1]; simp
      linarith
  · have hev : uctSeedZ ε =ᶠ[𝓝 ζ] seedZR ε := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with z hz
      exact uctSeedZ_of_gt hz
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
      rw [ite_eq_right this, h]; simp
  have e : ∀ x : ℂ, (if ε = 1 then (1 : ℂ) else -1) * x = ε * x := fun x => by rw [hsign]
  rcases lt_trichotomy ζ.re (1 / 2) with h | h | h
  · have h1 : 1 / 2 < (1 - ζ).re := by simp; linarith
    rw [uctSeedZ_of_gt h1, uctSeedZ_of_le h.le, seedZR_oneSub, e]
  · have hs := sin_ne_zero_of_re_half h
    have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    rw [uctSeedZ_of_le h1, uctSeedZ_of_le h.le, seedZL_oneSub, e, seedZL_eq_seedZR hs]
  · have h1 : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
    rw [uctSeedZ_of_le h1, uctSeedZ_of_gt h, seedZL_oneSub, e]

/-- Real symmetry. -/
theorem uctSeedZ_conj (ε : ℝ) (ζ : ℂ) : uctSeedZ ε (starRingEnd ℂ ζ) = starRingEnd ℂ (uctSeedZ ε ζ) := by
  have hA : seedA ε (starRingEnd ℂ ζ) = starRingEnd ℂ (seedA ε ζ) := by
    have hb : bArg (starRingEnd ℂ ζ) = starRingEnd ℂ (bArg ζ) := by
      unfold bArg; simp [map_sub, map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]
    unfold seedA
    by_cases h : ε = 1
    · simp only [h, ↓reduceIte]
      rw [hb, Complex.cos_conj, map_mul, map_pow, map_ofNat]
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
    simp [map_mul, map_pow]
  by_cases hr : ζ.re ≤ 1 / 2
  · rw [uctSeedZ_of_le (by simpa using hr), uctSeedZ_of_le hr, hL]
  · rw [uctSeedZ_of_gt (by simpa using not_le.mp hr), uctSeedZ_of_gt (not_le.mp hr), hR]


lemma seedA_zero (ε : ℝ) : seedA ε 0 = 1 := by
  unfold seedA bArg
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    rw [show (π : ℂ) / 4 - π * 0 / 2 = π / 4 by ring, Complex.cos_sq,
      show 2 * ((π : ℂ) / 4) = π / 2 by ring, Complex.cos_pi_div_two]
    norm_num
  · simp only [h, ↓reduceIte]; simp

theorem uctSeedZ_zero (ε : ℝ) : uctSeedZ ε 0 = 1 := by
  rw [uctSeedZ_of_le (by simp), seedZL, seedA_zero, mul_zero, sincInv_zero]; simp

theorem uctSeedZ_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : uctSeedZ ε 1 = ε := by
  have := uctSeedZ_oneSub hε 0
  simpa [uctSeedZ_zero] using this

lemma uctSeedZ_eq_of_sin {ε : ℝ} {ζ : ℂ} (hs : Complex.sin (π * ζ) ≠ 0) :
    uctSeedZ ε ζ = seedA ε ζ * ((π : ℂ) * ζ * (1 - ζ) / Complex.sin (π * ζ)) ^ 2 := by
  by_cases hr : ζ.re ≤ 1 / 2
  · rw [uctSeedZ_of_le hr, seedZL_eq_of_sin hs]
  · rw [uctSeedZ_of_gt (not_le.mp hr), seedZR_eq_of_sin hs]

lemma cosh_div_sinh_sq_le {a : ℝ} (ha : 1 ≤ a) : Real.cosh a / Real.sinh a ^ 2 ≤ 16 * Real.exp (-a) := by
  have hE : 1 ≤ Real.exp a := Real.one_le_exp (by linarith)
  have he2 : 2 ≤ Real.exp a := by
    have := Real.add_one_le_exp a
    linarith
  have hpos : 0 < Real.exp a := Real.exp_pos a
  have hinv : (Real.exp a)⁻¹ ≤ Real.exp a / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
  have hsinh : Real.exp a / 4 ≤ Real.sinh a := by
    rw [Real.sinh_eq, Real.exp_neg]
    linarith
  have hcosh : Real.cosh a ≤ Real.exp a := by
    rw [Real.cosh_eq, Real.exp_neg]
    linarith
  have hs2 : (Real.exp a / 4) ^ 2 ≤ Real.sinh a ^ 2 := pow_le_pow_left₀ (by positivity) hsinh 2
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hs2), Real.exp_neg]
  have : 16 * (Real.exp a)⁻¹ * Real.sinh a ^ 2 ≥ 16 * (Real.exp a)⁻¹ * (Real.exp a / 4) ^ 2 :=
    mul_le_mul_of_nonneg_left hs2 (by positivity)
  have e : 16 * (Real.exp a)⁻¹ * (Real.exp a / 4) ^ 2 = Real.exp a := by field_simp; ring
  linarith

lemma norm_seedA_le (ε : ℝ) (ζ : ℂ) : ‖seedA ε ζ‖ ≤ 2 * Real.cosh (π * ζ.im) := by
  have hc := Real.cosh_pos (π * ζ.im)
  unfold seedA
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    rw [norm_mul, norm_pow]
    have h1 := norm_cos_sq (bArg ζ)
    have hy : (bArg ζ).im = -(π * ζ.im / 2) := bArg_im ζ
    have h2 : ‖Complex.cos (bArg ζ)‖ ^ 2 ≤ Real.cosh (π * ζ.im / 2) ^ 2 := by
      rw [h1, hy, Real.sinh_neg, neg_sq, Real.cosh_sq (π * ζ.im / 2)]
      nlinarith [Real.sin_sq_add_cos_sq (bArg ζ).re, Real.cos_sq_le_one (bArg ζ).re]
    have h3 : Real.cosh (π * ζ.im / 2) ^ 2 ≤ Real.cosh (π * ζ.im) := by
      have := Real.cosh_two_mul (π * ζ.im / 2)
      rw [show 2 * (π * ζ.im / 2) = π * ζ.im by ring] at this
      nlinarith [Real.one_le_cosh (π * ζ.im)]
    simp only [norm_ofNat]
    nlinarith
  · simp only [h, ↓reduceIte]
    have h1 := norm_cos_sq (π * ζ)
    have hy : ((π : ℂ) * ζ).im = π * ζ.im := by simp [Complex.mul_im]
    have h2 : ‖Complex.cos (π * ζ)‖ ^ 2 ≤ Real.cosh (π * ζ.im) ^ 2 := by
      rw [h1, hy, Real.cosh_sq]
      nlinarith [Real.cos_sq_le_one ((π : ℂ) * ζ).re]
    have := abs_le_of_sq_le_sq' h2 hc.le
    nlinarith [this.2]

lemma norm_sin_pi_sq_ge (ζ : ℂ) : Real.sinh (π * ζ.im) ^ 2 ≤ ‖Complex.sin (π * ζ)‖ ^ 2 := by
  have := norm_sin_arg_sq ζ 0
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at this
  rw [this]
  nlinarith [sq_nonneg (Real.sin (π * ζ.re))]

/-- `|Z_ε(σ+iτ)| ≤ 32π²(1+|τ|)⁴ e^{-π|τ|}` on `closedStrip` for `|τ| ≥ 1/2`. -/
theorem uctSeedZ_bound (ε : ℝ) {ζ : ℂ} (hζ : ζ ∈ closedStrip) (hτ : 1 / 2 ≤ |ζ.im|) :
    ‖uctSeedZ ε ζ‖ ≤ 32 * π ^ 2 * (1 + |ζ.im|) ^ 4 * Real.exp (-(π * |ζ.im|)) := by
  set a : ℝ := π * |ζ.im| with ha
  have ha1 : 1 ≤ a := by
    have := Real.pi_gt_three; rw [ha]; nlinarith
  have hcosh : Real.cosh (π * ζ.im) = Real.cosh a := by
    rw [ha]; rcases abs_cases ζ.im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cosh_neg]
  have hsh : Real.sinh (π * ζ.im) ^ 2 = Real.sinh a ^ 2 := by
    rw [ha]; rcases abs_cases ζ.im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sinh_neg, neg_sq]
  have hsinhpos : 0 < Real.sinh a := Real.sinh_pos_iff.mpr (by linarith)
  have hsin2 : Real.sinh a ^ 2 ≤ ‖Complex.sin (π * ζ)‖ ^ 2 := by
    rw [← hsh]; exact norm_sin_pi_sq_ge ζ
  have hsne : Complex.sin (π * ζ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hsin2; nlinarith [pow_pos hsinhpos 2]
  rw [uctSeedZ_eq_of_sin hsne, norm_mul, norm_pow, norm_div, norm_mul, norm_mul]
  have hn1 : ‖ζ‖ ≤ 1 + |ζ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im ζ
    have h2 : |ζ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2]
    linarith
  have hn2 : ‖1 - ζ‖ ≤ 1 + |ζ.im| := by
    have := Complex.norm_le_abs_re_add_abs_im (1 - ζ)
    have h2 : |(1 - ζ).re| ≤ 1 := by rw [abs_le]; simp; constructor <;> linarith [hζ.1, hζ.2]
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    linarith
  have hπ : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [hπ]
  have hA := norm_seedA_le ε ζ
  rw [hcosh] at hA
  have hcs := cosh_div_sinh_sq_le ha1
  have hsinpos : 0 < ‖Complex.sin (π * ζ)‖ := norm_pos_iff.mpr hsne
  set N : ℝ := π * ‖ζ‖ * ‖1 - ζ‖ with hN
  have hN0 : 0 ≤ N := by positivity
  have hNb : N ≤ π * (1 + |ζ.im|) ^ 2 := by
    rw [hN, mul_assoc, sq]
    have : ‖ζ‖ * ‖1 - ζ‖ ≤ (1 + |ζ.im|) * (1 + |ζ.im|) :=
      mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  have hsq : (N / ‖Complex.sin (π * ζ)‖) ^ 2 ≤ π ^ 2 * (1 + |ζ.im|) ^ 4 / Real.sinh a ^ 2 := by
    rw [div_pow]
    have h1 : N ^ 2 ≤ (π * (1 + |ζ.im|) ^ 2) ^ 2 := pow_le_pow_left₀ hN0 hNb 2
    calc N ^ 2 / ‖Complex.sin (π * ζ)‖ ^ 2 ≤ (π * (1 + |ζ.im|) ^ 2) ^ 2 / ‖Complex.sin (π * ζ)‖ ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (π * (1 + |ζ.im|) ^ 2) ^ 2 / Real.sinh a ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsin2
      _ = π ^ 2 * (1 + |ζ.im|) ^ 4 / Real.sinh a ^ 2 := by ring
  calc ‖seedA ε ζ‖ * (N / ‖Complex.sin (π * ζ)‖) ^ 2
      ≤ 2 * Real.cosh a * (π ^ 2 * (1 + |ζ.im|) ^ 4 / Real.sinh a ^ 2) :=
        mul_le_mul hA hsq (by positivity) (by positivity)
    _ = 2 * π ^ 2 * (1 + |ζ.im|) ^ 4 * (Real.cosh a / Real.sinh a ^ 2) := by ring
    _ ≤ 2 * π ^ 2 * (1 + |ζ.im|) ^ 4 * (16 * Real.exp (-a)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by rw [ha]; ring

lemma sin_pi_ne_zero_of_strip {ζ : ℂ} (hζ : ζ ∈ strip) : Complex.sin (π * ζ) ≠ 0 := by
  have h1 := norm_sin_arg_sq ζ 0
  intro h
  have : Complex.sin (π * (ζ - Complex.I * ((0 : ℝ) : ℂ))) = Complex.sin (π * ζ) := by simp
  rw [this, h, norm_zero] at h1
  have hs : 0 < Real.sin (π * ζ.re) := Real.sin_pos_of_pos_of_lt_pi (by have := hζ.1; positivity)
    (by have := hζ.2; nlinarith [Real.pi_pos])
  nlinarith [sq_nonneg (Real.sinh (π * (ζ.im - ((0 : ℝ))))), pow_pos hs 2]

/-- `ζ^{5/2}(1-ζ)^{5/2} H_*(ζ)/G_ε(ζ) = Z_ε(ζ) e^{-h(ζ)}` on `S` (for `ε = 1` off the zero `ζ = 1/2` of `b_{1/2}`). -/
theorem seed_factor_eq {ε : ℝ} {ζ : ℂ} (hζ : ζ ∈ strip) (hb : ε = 1 → bHalf ζ ≠ 0) :
    ζ ^ (5 / 2 : ℂ) * (1 - ζ) ^ (5 / 2 : ℂ) * uctHstar ζ / outerG ε ζ = uctSeedZ ε ζ * Complex.exp (-outerH ζ) := by
  have hcl := strip_subset_closedStrip hζ
  have hζ0 : ζ ≠ 0 := fun h => by have := hζ.1; rw [h] at this; simp at this
  have hζ1 : 1 - ζ ≠ 0 := fun h => by
    have := hζ.2
    have e : ζ.re = 1 := by have := congrArg Complex.re h; simp at this; linarith
    linarith
  have hs1 := cpow_half_ne_zero hζ0
  have hs2 := cpow_half_ne_zero hζ1
  have hsin := sin_pi_ne_zero_of_strip hζ
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [uctSeedZ_eq_of_sin hsin, cpow_five_half, cpow_five_half]
  unfold outerG outerGm uctHstar seedA
  rw [Complex.exp_neg]
  have hE : Complex.exp (outerH ζ) ≠ 0 := Complex.exp_ne_zero _
  by_cases h : ε = 1
  · simp only [h, ↓reduceIte]
    have hbn := hb h
    have hc := cos_bArg_ne_zero hcl
    have hbs : Complex.sin (bArg ζ) ≠ 0 := by
      intro h0; apply hbn; unfold bHalf; rw [Complex.tan]
      rw [show (π : ℂ) / 4 - π * ζ / 2 = bArg ζ from rfl, h0]; simp
    have hbt : bHalf ζ = Complex.sin (bArg ζ) / Complex.cos (bArg ζ) := rfl
    have hcosπ : Complex.cos (π * ζ) = 2 * Complex.sin (bArg ζ) * Complex.cos (bArg ζ) := by
      rw [← Complex.sin_two_mul, ← Complex.sin_pi_div_two_sub]
      congr 1; unfold bArg; ring
    rw [hbt, hcosπ]
    field_simp
  · simp only [h, ↓reduceIte]
    field_simp

/-- info: 'FormalResearch.SignUncertainty.differentiableOn_uctSeedZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_uctSeedZ

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_oneSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_oneSub

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_conj

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_zero

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_one

/-- info: 'FormalResearch.SignUncertainty.uctSeedZ_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSeedZ_bound

/-- info: 'FormalResearch.SignUncertainty.seed_factor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seed_factor_eq

end FormalResearch.SignUncertainty

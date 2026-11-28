/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpMidSym

/-!
# Physical bump four-piece decomposition and pre-transition bound (`fct:bump-5`, `fct:bump-sym-check`)

Proves:
* `bumpHrefl_add`, `bumpHrefl_const_mul`, `bumpHmain_lin4`;
* `BSym_of_symW`, `iteratedDeriv_eq_zero_of_eqOn_Iio`, `iteratedDeriv_eq_zero_of_eqOn_Ioi`;
* `phys_mac_positivity`: on `[3δ_L, ∞)`, `O ≥ 0`, `F ≥ (1/4) I_fl`, `γ ∈ [1/2, 1]`;
* `physBump_decomp`: splits `physBump` into the four `BSym` pieces `p₁, p₂, p₃, p₄` with `p₄ ≥ 0` and
  `p₄ = 0` on `[6δ_L, ∞)`, `n_c ∈ [1/2, 2]`, and scales independent of `K₁`;
* `physBump_pretrans_bound` (Regime 1, `L ≤ 3 δ_L / 4`): `|normDensity (ctWbump B ε c) c ξ| ≤ c⁻²`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctSym.SymW
open FormalResearch.SignUncertainty.FctCompD

namespace FormalResearch.SignUncertainty

section Helpers

/-- Linearity of `bumpHrefl` in `B`. -/
lemma bumpHrefl_add {B1 B2 : ℝ → ℝ} {δ M1 M2 α1 α2 β1 β2 c ξ : ℝ} {K1 K2 : ℕ → ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1) (hβ1 : 3 / 2 ≤ β1) (hβ2 : 3 / 2 ≤ β2)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hξ : 0 < ξ)
    (h1 : BumpProfile (3 / 2) δ M1 α1 β1 K1 B1) (h2 : BumpProfile (3 / 2) δ M2 α2 β2 K2 B2) :
    bumpHrefl c (fun x => B1 x + B2 x) ξ = bumpHrefl c B1 ξ + bumpHrefl c B2 ξ := by
  have hc0 : 0 < c := by linarith only [hc]
  have hb0 : 0 ≤ (3 / 2 : ℝ) * δ := by positivity
  have hδ_le1 : δ ≤ 1 := by linarith only [hδ0, hδ1]
  have hadm1 := (bump_stripAdmissFull (b := 3 / 2) (by norm_num) hβ1 K1 hδ0 hδ_le1 hδ1 hM1 hc0 h1).reflect
  have hadm2 := (bump_stripAdmissFull (b := 3 / 2) (by norm_num) hβ2 K2 hδ0 hδ_le1 hδ1 hM2 hc0 h2).reflect
  have i1 := admiss_edge0_integrable hc hξ hadm1
  have i2 := admiss_edge0_integrable hc hξ hadm2
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c (fun x => B1 x + B2 x) (1 - (τ : ℂ) * Complex.I)) =
      fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B1 (1 - (τ : ℂ) * Complex.I) +
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B2 (1 - (τ : ℂ) * Complex.I) := by
    funext τ
    have hre : ((c : ℂ) * (1 - (τ : ℂ) * Complex.I)).re = c := by simp
    unfold bumpDW
    rw [bumpLaplace_add hb0 hδ1 (by linarith only [hβ1]) (by linarith only [hβ2]) h1 h2 (hre.symm ▸ hc0.le)]
    ring
  unfold bumpHrefl bumpDW
  unfold bumpDW at hpt
  rw [hpt, integral_add i1 i2]
  ring

/-- Homogeneity of `bumpHrefl` in `B`. -/
lemma bumpHrefl_const_mul (a c : ℝ) (B : ℝ → ℝ) (ξ : ℝ) :
    bumpHrefl c (fun x => a * B x) ξ = (a : ℂ) * bumpHrefl c B ξ := by
  unfold bumpHrefl
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c (fun x => a * B x) (1 - (τ : ℂ) * Complex.I)) =
      fun τ : ℝ => (a : ℂ) * (mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B (1 - (τ : ℂ) * Complex.I)) := by
    funext τ; unfold bumpDW; rw [bumpLaplace_const_mul]; ring
  rw [hpt, integral_const_mul]
  ring

/-- Four-term linear expansion for `bumpHmain`. -/
lemma bumpHmain_lin4 {n δ c ξ : ℝ} {B1 B2 B3 B4 : ℝ → ℝ}
    {M1 M2 M3 M4 α1 α2 α3 α4 β1 β2 β3 β4 : ℝ} {K1 K2 K3 K4 : ℕ → ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : 3 / 2 * δ ≤ 1)
    (hβ1 : 3 / 2 ≤ β1) (hβ2 : 3 / 2 ≤ β2) (hβ3 : 3 / 2 ≤ β3) (hβ4 : 3 / 2 ≤ β4)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hξ : 0 < ξ)
    (hb1 : BumpProfile (3 / 2) δ M1 α1 β1 K1 B1) (hb2 : BumpProfile (3 / 2) δ M2 α2 β2 K2 B2)
    (hb3 : BumpProfile (3 / 2) δ M3 α3 β3 K3 B3) (hb4 : BumpProfile (3 / 2) δ M4 α4 β4 K4 B4) :
    bumpHmain c (fun x => n * (B1 x + B2 x + B3 x + B4 x)) ξ =
      (n : ℂ) * (bumpHmain c B1 ξ + bumpHmain c B2 ξ + bumpHmain c B3 ξ + bumpHmain c B4 ξ) := by
  have hb0 : 0 ≤ (3 / 2 : ℝ) * δ := by positivity
  have i1 := bumpDW_edge_integrable hc hδ0 hδ1 hβ1 hM1 hξ hb1
  have i2 := bumpDW_edge_integrable hc hδ0 hδ1 hβ2 hM2 hξ hb2
  have i3 := bumpDW_edge_integrable hc hδ0 hδ1 hβ3 hM3 hξ hb3
  have i4 := bumpDW_edge_integrable hc hδ0 hδ1 hβ4 hM4 hξ hb4
  rw [bumpHmain_const_mul]
  congr 1
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ *
        bumpDW c (fun x => B1 x + B2 x + B3 x + B4 x) ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ =>
        ((mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B1 ((τ : ℂ) * Complex.I) +
          mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B2 ((τ : ℂ) * Complex.I)) +
          mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B3 ((τ : ℂ) * Complex.I)) +
          mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B4 ((τ : ℂ) * Complex.I) := by
    funext τ
    have hre : ((c : ℂ) * ((τ : ℂ) * Complex.I)).re = 0 := by simp
    have l1 : Integrable (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B1 x : ℂ)) := by
      simpa using hb1.integrable_laplace_mul hb0 hδ1 (by linarith only [hβ1]) 0 hre.ge
    have l2 : Integrable (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B2 x : ℂ)) := by
      simpa using hb2.integrable_laplace_mul hb0 hδ1 (by linarith only [hβ2]) 0 hre.ge
    have l3 : Integrable (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B3 x : ℂ)) := by
      simpa using hb3.integrable_laplace_mul hb0 hδ1 (by linarith only [hβ3]) 0 hre.ge
    have l4 : Integrable (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B4 x : ℂ)) := by
      simpa using hb4.integrable_laplace_mul hb0 hδ1 (by linarith only [hβ4]) 0 hre.ge
    have hlap : bumpLaplace (fun x => B1 x + B2 x + B3 x + B4 x) ((c : ℂ) * ((τ : ℂ) * Complex.I)) =
        bumpLaplace B1 ((c : ℂ) * ((τ : ℂ) * Complex.I)) + bumpLaplace B2 ((c : ℂ) * ((τ : ℂ) * Complex.I)) +
        bumpLaplace B3 ((c : ℂ) * ((τ : ℂ) * Complex.I)) + bumpLaplace B4 ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
      unfold bumpLaplace
      have hf : (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) *
            ((B1 x + B2 x + B3 x + B4 x : ℝ) : ℂ)) =
          fun x : ℝ =>
            ((Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B1 x : ℂ) +
              Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B2 x : ℂ)) +
              Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B3 x : ℂ)) +
              Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B4 x : ℂ) := by
        funext x; push_cast; ring
      have l12 : Integrable (fun x : ℝ => Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B1 x : ℂ) +
          Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B2 x : ℂ)) := l1.add l2
      have l123 : Integrable (fun x : ℝ => (Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B1 x : ℂ) +
          Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B2 x : ℂ)) +
          Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I)) * (x : ℂ)) * (B3 x : ℂ)) := l12.add l3
      rw [hf, integral_add l123 l4, integral_add l12 l3, integral_add l1 l2]
    unfold bumpDW; rw [hlap]; ring
  have i12 : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B1 ((τ : ℂ) * Complex.I) +
      mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B2 ((τ : ℂ) * Complex.I)) := i1.add i2
  have i123 : Integrable (fun τ : ℝ => (mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B1 ((τ : ℂ) * Complex.I) +
      mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B2 ((τ : ℂ) * Complex.I)) +
      mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B3 ((τ : ℂ) * Complex.I)) := i12.add i3
  unfold bumpHmain bumpDW
  unfold bumpDW at hpt i1 i2 i3 i4 i12 i123
  rw [hpt, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  ring

/-- Convert `SymW (Ici (3/2 * δ)) (pw M α β)` (`α ≤ β`) into `BSym δ M α β`. -/
lemma BSym_of_symW {δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}
    (h : SymW (Ici (3 / 2 * δ)) (pw M α β) K B) (hδ : 0 < δ) (hM : 0 ≤ M) (hαβ : α ≤ β)
    (hsup : ∀ x : ℝ, x < 3 / 2 * δ → B x = 0) :
    BSym δ M α β K B where
  smooth := (h.toBumpProfile hM hsup).smooth
  support := hsup
  K_nonneg := h.K_nonneg
  bound r x hx := by
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    have hbd := h.bound r x hx
    have hpw : pw M α β x * (x ^ r)⁻¹ = M * min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ))) := by
      rw [← Real.rpow_natCast x r, ← Real.rpow_neg hx0.le]
      by_cases hx1 : x ≤ 1
      · have hpw1 : pw M α β x = M * x ^ (-α) := by simp only [pw, hx1, ↓reduceIte]
        have hmin : min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ))) = x ^ (-α - (r : ℝ)) := by
          apply min_eq_left
          exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith only [hαβ])
        rw [hpw1, hmin, mul_assoc, ← Real.rpow_add hx0]; ring_nf
      · have hx1gt : 1 ≤ x := (not_le.mp hx1).le
        have hpw1 : pw M α β x = M * x ^ (-β) := by simp only [pw, hx1, ↓reduceIte]
        have hmin : min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ))) = x ^ (-β - (r : ℝ)) := by
          apply min_eq_right
          exact Real.rpow_le_rpow_of_exponent_le hx1gt (by linarith only [hαβ])
        rw [hpw1, hmin, mul_assoc, ← Real.rpow_add hx0]; ring_nf
    calc |iteratedDeriv r B x| ≤ K r * pw M α β x * (x ^ r)⁻¹ := hbd
      _ = K r * (pw M α β x * (x ^ r)⁻¹) := by ring
      _ = K r * (M * min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ)))) := by rw [hpw]
      _ = K r * M * min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ))) := by ring

/-- Smooth functions vanishing on `(-∞, a)` have all derivatives vanishing on `(-∞, a]`. -/
lemma iteratedDeriv_eq_zero_of_eqOn_Iio {f : ℝ → ℝ} {a : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h0 : ∀ x < a, f x = 0) : ∀ k : ℕ, ∀ x ≤ a, iteratedDeriv k f x = 0 := by
  have hlt : ∀ k : ℕ, ∀ x < a, iteratedDeriv k f x = 0 := by
    intro k x hx
    have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) h0
    rw [hev.iteratedDeriv_eq k]
    simp
  intro k x hx
  rcases lt_or_eq_of_le hx with h | rfl
  · exact hlt k x h
  · have hcont : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
    have h1 : Tendsto (iteratedDeriv k f) (𝓝[<] x) (𝓝 (iteratedDeriv k f x)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (iteratedDeriv k f) (𝓝[<] x) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => (hlt k y hy).symm)
    exact tendsto_nhds_unique h1 h2

/-- Smooth functions vanishing on `(b, ∞)` have all derivatives vanishing on `[b, ∞)`. -/
lemma iteratedDeriv_eq_zero_of_eqOn_Ioi {f : ℝ → ℝ} {b : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h0 : ∀ x > b, f x = 0) : ∀ k : ℕ, ∀ x ≥ b, iteratedDeriv k f x = 0 := by
  have hgt : ∀ k : ℕ, ∀ x > b, iteratedDeriv k f x = 0 := by
    intro k x hx
    have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) h0
    rw [hev.iteratedDeriv_eq k]
    simp
  intro k x hx
  rcases lt_or_eq_of_le hx with h | rfl
  · exact hgt k x h
  · have hcont : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
    have h1 : Tendsto (iteratedDeriv k f) (𝓝[>] b) (𝓝 (iteratedDeriv k f b)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (iteratedDeriv k f) (𝓝[>] b) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => (hgt k y hy).symm)
    exact tendsto_nhds_unique h1 h2

/-- Exponential tail absorption `exp (-(κ c^{1/4})) * c^3 ≤ (12! / κ^{12})`. -/
lemma exp_quarter_absorb {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-(κ * c ^ (1 / 4 : ℝ))) * c ^ 3 ≤ (Nat.factorial 12 : ℝ) * (κ ^ 12)⁻¹ := by
  have hpow := Real.pow_div_factorial_le_exp (κ * c ^ (1 / 4 : ℝ)) (by positivity) 12
  have hc4 : (c ^ (1 / 4 : ℝ)) ^ (12 : ℕ) = c ^ 3 := by
    rw [← Real.rpow_natCast (c ^ (1 / 4 : ℝ)) 12, ← Real.rpow_mul hc.le]; norm_num
  have he : κ ^ 12 * c ^ 3 / (Nat.factorial 12 : ℝ) ≤ Real.exp (κ * c ^ (1 / 4 : ℝ)) := by
    rw [mul_pow, hc4] at hpow; exact hpow
  have hexp0 : 0 < Real.exp (κ * c ^ (1 / 4 : ℝ)) := Real.exp_pos _
  have hfac0 : (0 : ℝ) < (Nat.factorial 12 : ℝ) := by positivity
  rw [Real.exp_neg, inv_eq_one_div, one_div_mul_eq_div, div_le_iff₀ hexp0]
  have hm := mul_le_mul_of_nonneg_left he hfac0.le
  have hd := div_le_div_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ κ ^ 12)
  have hl : (Nat.factorial 12 : ℝ) * (κ ^ 12 * c ^ 3 / (Nat.factorial 12 : ℝ)) / κ ^ 12 = c ^ 3 := by field_simp
  calc c ^ 3 = (Nat.factorial 12 : ℝ) * (κ ^ 12 * c ^ 3 / (Nat.factorial 12 : ℝ)) / κ ^ 12 := hl.symm
    _ ≤ (Nat.factorial 12 : ℝ) * Real.exp (κ * c ^ (1 / 4 : ℝ)) / κ ^ 12 := hd
    _ = (Nat.factorial 12 : ℝ) * (κ ^ 12)⁻¹ * Real.exp (κ * c ^ (1 / 4 : ℝ)) := by rw [div_eq_mul_inv]; ring

/-- Exponential tail absorption `exp (-(κ √c)) * c^3 ≤ (6! / κ^6)`. -/
lemma exp_half_absorb {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-(κ * Real.sqrt c)) * c ^ 3 ≤ (Nat.factorial 6 : ℝ) * (κ ^ 6)⁻¹ := by
  have hpow := Real.pow_div_factorial_le_exp (κ * Real.sqrt c) (by positivity) 6
  have hc2 : Real.sqrt c ^ (6 : ℕ) = c ^ 3 := by
    calc Real.sqrt c ^ 6 = (Real.sqrt c ^ 2) ^ 3 := by ring
      _ = c ^ 3 := by rw [Real.sq_sqrt hc.le]
  have he : κ ^ 6 * c ^ 3 / (Nat.factorial 6 : ℝ) ≤ Real.exp (κ * Real.sqrt c) := by
    rw [mul_pow, hc2] at hpow; exact hpow
  have hexp0 : 0 < Real.exp (κ * Real.sqrt c) := Real.exp_pos _
  have hfac0 : (0 : ℝ) < (Nat.factorial 6 : ℝ) := by positivity
  rw [Real.exp_neg, inv_eq_one_div, one_div_mul_eq_div, div_le_iff₀ hexp0]
  have hm := mul_le_mul_of_nonneg_left he hfac0.le
  have hd := div_le_div_of_nonneg_right hm (by positivity : (0 : ℝ) ≤ κ ^ 6)
  have hl : (Nat.factorial 6 : ℝ) * (κ ^ 6 * c ^ 3 / (Nat.factorial 6 : ℝ)) / κ ^ 6 = c ^ 3 := by field_simp
  calc c ^ 3 = (Nat.factorial 6 : ℝ) * (κ ^ 6 * c ^ 3 / (Nat.factorial 6 : ℝ)) / κ ^ 6 := hl.symm
    _ ≤ (Nat.factorial 6 : ℝ) * Real.exp (κ * Real.sqrt c) / κ ^ 6 := hd
    _ = (Nat.factorial 6 : ℝ) * (κ ^ 6)⁻¹ * Real.exp (κ * Real.sqrt c) := by rw [div_eq_mul_inv]; ring

/-- On `[3δ, ∞)`, `physOscDatum ≥ 0`, `physF ≥ 1/4 * uctIfl`, and `physGamma ∈ [1/2, 1]`. -/
lemma phys_mac_positivity {K4 : ℝ} (hK4 : 1 ≤ K4) {T1 alpha : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) :
    ∃ c₀ : ℝ, 2 ≤ c₀ ∧ ∀ ε c L : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 3 * physDelta c ≤ L →
      0 ≤ physOscDatum StripKernelChoice.star K4 T1 alpha ε c L ∧
      1 / 4 * uctIfl L ≤ physF (physShift ε c) (physL1 T1 ε c) L ∧
      1 / 2 ≤ physGamma c (physShift ε c) L ∧
      physGamma c (physShift ε c) L ≤ 1 := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).1⟩
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  obtain ⟨Kα, cα, hαf⟩ := hα
  have hKα0 : 0 ≤ Kα := by
    have := hαf 1 (max cα 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cα 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (alpha 1 (max cα 1))]
  obtain ⟨cs, a₀, _, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨τa, hτa, _, hΔall⟩ := stripDeltaCurv_le_all StripKernelChoice.star
  obtain ⟨CD, hCD, hΔ⟩ := hΔall K4 hK4
  obtain ⟨c_tau, _, hc_tau⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4) (η := min τa (1 / 20))
    (by norm_num) (lt_min hτa (by norm_num))
  obtain ⟨c_al, _, hc_al⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6) (η := 1 / (Kα + 1)) (by norm_num) (by positivity)
  obtain ⟨c_d, _, hc_d⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2) (η := 1 / (2 * (CD + 1))) (by norm_num) (by positivity)
  obtain ⟨c_g, _, hc_g⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := (3 / 2 * a₀) ^ 3 / (5 * Real.pi ^ 2 / 48 + 1)) (by norm_num) (by positivity)
  refine ⟨max (max cs cα) (max (max c_tau c_al) (max c_d (max c_g 2))),
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))), ?_⟩
  intro ε c L hε hc hL3
  simp only [max_le_iff] at hc
  obtain ⟨⟨hcs', hcα'⟩, ⟨⟨hct', hcal'⟩, ⟨hcd', ⟨hcg', hc2⟩⟩⟩⟩ := hc
  obtain ⟨hδ0, _, hs_le, hL1_le, _, _, hδ_lo, _, _⟩ := hsc ε c hε hcs'
  have hc0 : 0 < c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_bd : τ₁ ≤ min τa (1 / 20) := hc_tau c hct'
  have hτa' : τ₁ ≤ τa := hτ₁_bd.trans (min_le_left _ _)
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_bd.trans (min_le_right _ _)
  have hτ₁_four : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hc0.le,
        show (-(1 / 4 : ℝ)) * (4 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp
  have hα_bd : |alpha ε c| ≤ τ₁ ^ 2 := by
    have h1 := hαf ε c hε hcα'
    have h2 : c ^ (-(1 / 6 : ℝ)) ≤ 1 / (Kα + 1) := hc_al c hcal'
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
    have hk : Kα * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
      calc Kα * c ^ (-(1 / 6 : ℝ)) ≤ Kα * (1 / (Kα + 1)) := mul_le_mul_of_nonneg_left h2 hKα0
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith only [hKα0]
    rw [hτ₁_sq]
    calc |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) := h1
      _ = (Kα * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h23]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hc0.le _)
      _ = c ^ (-(1 / 2 : ℝ)) := one_mul _
  have hLpos : 0 < L := by linarith only [hL3, hδ0]
  have hs_abs : |s| ≤ 1 / 4 * L := by linarith only [hs_le, hL3]
  have hL1_abs : |L1| ≤ 1 / 4 * L := by linarith only [hL1_le, hL3]
  have hLs_pos : 0 < L - s := by linarith only [(abs_le.mp hs_abs).2, hLpos]
  have hL1_pos : 0 < L - L1 := by linarith only [(abs_le.mp hL1_abs).2, hLpos]
  have hO_nn : 0 ≤ physOscDatum StripKernelChoice.star K4 T1 alpha ε c L := by
    have htpos : 0 < tau0 (L - s) := tau0_pos hLs_pos
    have hΔ_bd := hΔ hc0 hτ₁pos hτa' hτ₁_four hα_bd (tau0 (L - s)) htpos
    have hτ2 : τ₁ ^ 3 ≤ c ^ (-(1 / 2 : ℝ)) := by
      have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
      rw [← hτ₁_sq]
      exact pow_le_pow_of_le_one hτ₁pos.le (by linarith only [hτ₁_20]) (by norm_num)
    have hΔ_half : |stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) (tau0 (L - s))| ≤ 1 / 2 := by
      have hbd := hc_d c hcd'
      have hratCD : CD / (CD + 1) ≤ 1 := by rw [div_le_one (by linarith only [hCD])]; linarith only [hCD]
      have hC : CD * c ^ (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
        calc CD * c ^ (-(1 / 2 : ℝ)) ≤ CD * (1 / (2 * (CD + 1))) := mul_le_mul_of_nonneg_left hbd hCD
          _ = 1 / 2 * (CD / (CD + 1)) := by field_simp
          _ ≤ 1 / 2 := by linarith only [hratCD]
      exact hΔ_bd.trans (le_trans (mul_le_mul_of_nonneg_left hτ2 hCD) hC)
    have h1Δ : 0 ≤ 1 + stripDeltaCurv c (FctMoment.fctThetaD (v0 StripKernelChoice.star K4 τ₁)) (tau0 (L - s)) := by
      linarith only [(abs_le.mp hΔ_half).1]
    have hIosc_nn : 0 ≤ stripIosc StripKernelChoice.star (L - s) := by
      unfold stripIosc uctIoscStar
      have hα0 : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
      have hm0 : 0 < uctMderiv (tau0 (L - s)) := uctMderiv_pos (tau0_pos hLs_pos)
      exact div_nonneg (mul_nonneg hα0 (norm_nonneg _)) hm0.le
    have hvp : 0 ≤ vacP StripKernelChoice.star K4 c (alpha ε c) τ₁ (L - s) := by
      unfold vacP stripIoscD
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hIosc_nn) h1Δ
    unfold physOscDatum physOsc
    exact div_nonneg (mul_nonneg hvp (norm_nonneg _)) hL1_pos.le
  have hF_lo : 1 / 4 * uctIfl L ≤ physF s L1 L := by
    unfold physF uctIfl
    have hls_lo : 3 / 4 * L ≤ L - s := by linarith only [(abs_le.mp hs_abs).2]
    have hls_hi : L - s ≤ 5 / 4 * L := by linarith only [(abs_le.mp hs_abs).1]
    have hl1_hi : L - L1 ≤ 5 / 4 * L := by linarith only [(abs_le.mp hL1_abs).1]
    have hrat : 3 / 5 ≤ (L - s) / (L - L1) := by
      rw [le_div_iff₀ hL1_pos]; linarith only [hls_lo, hl1_hi]
    have hu_rpow : (L - s) ^ (-(3 / 2 : ℝ)) ≥ (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      have hp := Real.rpow_le_rpow_of_nonpos hLs_pos hls_hi (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
      rw [Real.mul_rpow (by norm_num) hLpos.le] at hp; exact hp
    have h54 : 1 / 2 ≤ (5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have hsq : ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = (4 / 5 : ℝ) ^ 3 := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num),
          show (-(3 / 2 : ℝ)) * (2 : ℕ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
          Real.rpow_natCast]
        norm_num
      have h12 : (1 / 2 : ℝ) ^ 2 ≤ ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 := by rw [hsq]; norm_num
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) (-(3 / 2 : ℝ))]
    have hα_pos : 0 < uctAlphaFl := by
      unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    have hL32 : 0 ≤ L ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hLpos.le _
    calc 1 / 4 * (uctAlphaFl * L ^ (-(3 / 2 : ℝ)))
        ≤ (3 / 5) * (uctAlphaFl * ((1 / 2) * L ^ (-(3 / 2 : ℝ)))) := by
          have : 0 ≤ uctAlphaFl * L ^ (-(3 / 2 : ℝ)) := mul_nonneg hα_pos.le hL32
          nlinarith only [this]
      _ ≤ ((L - s) / (L - L1)) * (uctAlphaFl * ((5 / 4 : ℝ) ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)))) := by
          refine mul_le_mul hrat (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h54 hL32) hα_pos.le)
            (by positivity) (by positivity)
      _ ≤ ((L - s) / (L - L1)) * (uctAlphaFl * (L - s) ^ (-(3 / 2 : ℝ))) := by gcongr
  have hγ1 : physGamma c s L ≤ 1 := by
    unfold physGamma
    have : 0 ≤ (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (L - s) ^ (-3 : ℝ) := by positivity
    linarith only [this]
  have hγ_half : 1 / 2 ≤ physGamma c s L := by
    unfold physGamma
    have hLs_lo : 3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ L - s := by
      have : 3 / 2 * δ ≤ L - s := by linarith only [(abs_le.mp hs_le).2, hL3, hδ0]
      nlinarith only [this, hδ_lo]
    have hpow : (L - s) ^ (-3 : ℝ) ≤ (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hLs_lo]) (by norm_num)
    have hp3 : (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) = (3 / 2 * a₀) ^ (-3 : ℝ) * c ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc0.le,
        show (-(1 / 2 : ℝ)) * (-3 : ℝ) = 3 / 2 by norm_num]
    have hcpow : c⁻¹ ^ 2 * c ^ (3 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_natCast (c ^ (-1 : ℝ)) 2, ← Real.rpow_mul hc0.le,
        ← Real.rpow_add hc0]; norm_num
    have hcg := hc_g c hcg'
    have h5 := Real.pi_pos
    have hgam_half : (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) ≤ 1 / 2 := by
      calc (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ)
          = (5 * Real.pi ^ 2 / 96) * (3 / 2 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
            rw [hp3]; linear_combination (5 * Real.pi ^ 2 / 96) * (3 / 2 * a₀) ^ (-3 : ℝ) * hcpow
        _ ≤ (1 / 2 * (5 * Real.pi ^ 2 / 48 + 1)) * (3 / 2 * a₀) ^ (-3 : ℝ) *
              ((3 / 2 * a₀) ^ 3 / (5 * Real.pi ^ 2 / 48 + 1)) := by
            have ha3_pos : 0 < (3 / 2 * a₀) ^ (-3 : ℝ) := by positivity
            have hc12_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
            have hlt : 5 * Real.pi ^ 2 / 96 ≤ 1 / 2 * (5 * Real.pi ^ 2 / 48 + 1) := by linarith
            calc (5 * Real.pi ^ 2 / 96) * (3 / 2 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ))
                ≤ (1 / 2 * (5 * Real.pi ^ 2 / 48 + 1)) * (3 / 2 * a₀) ^ (-3 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by gcongr
              _ ≤ _ := by gcongr
        _ = 1 / 2 := by
            rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
            field_simp
    have hmul : (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (L - s) ^ (-3 : ℝ) ≤
        (5 * Real.pi ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    linarith only [hmul, hgam_half]
  exact ⟨hO_nn, hF_lo, hγ_half, hγ1⟩

end Helpers

section Decomposition

/-- Structural four-piece decomposition of `physBump` for the concrete physical datum,
with explicit `BSym`, `BumpProfile`, `n ∈ [1/2, 2]`, and scales independent of `K1`. -/
lemma physBump_decomp {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∃ (c_d a₀ a₁ M1 M2_0 M3_0 M4 M_B0 M_BK : ℝ) (K1_k K2_k K3_k K4_k K_B : ℕ → ℝ),
      2 ≤ c_d ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 ≤ M1 ∧ 0 ≤ M2_0 ∧ 0 ≤ M3_0 ∧ 0 ≤ M4 ∧ 0 ≤ M_B0 ∧ 0 ≤ M_BK ∧
      (∀ r, 0 ≤ K1_k r ∧ 0 ≤ K2_k r ∧ 0 ≤ K3_k r ∧ 0 ≤ K4_k r ∧ 0 ≤ K_B r) ∧
      ∀ K1 ε c : ℝ, 0 ≤ K1 → (ε = 1 ∨ ε = -1) → c_d ≤ c →
        let δ := physDelta c
        let s := physShift ε c
        let L1 := physL1 T1 ε c
        let n := 1 / Nc ε c
        let F := physF s L1
        let O := physOscDatum StripKernelChoice.star K4 T1 alpha ε c
        let T4 : ℝ → ℝ := fun L => tau0 L ^ 4 * uctIfl L
        let R : ℝ → ℝ := fun x => O x / F x
        let p1 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (F x * R x - F x)
        let p2 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))
        let p3 : ℝ → ℝ := fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))
        let p4 : ℝ → ℝ := fun x => 2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * T4 x))
        (a₀ * c ^ (-(1 / 2 : ℝ)) ≤ δ ∧ δ ≤ a₁ * c ^ (-(1 / 2 : ℝ)) ∧ a₀ ≤ Real.sqrt c * δ ∧
          0 < δ ∧ δ ≤ 1 ∧ 3 / 2 * δ ≤ 1 ∧ 6 * δ ≤ 1 ∧ 1 / 2 ≤ n ∧ n ≤ 2 ∧
          |s| ≤ 3 / 2 * δ / 2 ∧ |L1| ≤ 3 / 2 * δ / 2) ∧
        (physBump χ n c δ s K1 K4 O F T4 = fun x => n * (p1 x + p2 x + p3 x + p4 x)) ∧
        BSym δ M1 (1 / 2) (3 / 2) K1_k p1 ∧
        BSym δ (M2_0 * K1 * c ^ (-2 : ℝ)) (7 / 2) (7 / 2) K2_k p2 ∧
        BSym δ (M3_0 * K1 * c⁻¹) (3 / 2) (3 / 2) K3_k p3 ∧
        BSym δ M4 (-(1 / 2)) (3 / 2) K4_k p4 ∧
        (∀ x : ℝ, 0 ≤ p4 x) ∧
        (∀ x : ℝ, 6 * δ ≤ x → p4 x = 0) ∧
        BumpProfile (3 / 2) δ (M_B0 + M_BK * K1 * c⁻¹) (7 / 2) (3 / 2) K_B
          (physBump χ n c δ s K1 K4 O F T4) := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).1⟩
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  have ha₁ : 0 < a₁ := by
    have ⟨hδ0, _, _, _, _, _, _, hδ_hi, _⟩ := hsc 1 (max cs 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cs 1) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) h0.le
    linarith only [hδ0, hδ_hi, this]
  obtain ⟨cR, MR, KR, hMR, hR⟩ :=
    physR_symW_of_factors StripKernelChoice.star K4 T1 alpha hT1 (hQ_of_alpha StripKernelChoice.star hK4 alpha hα)
  obtain ⟨cT, MT, KT, hMT, hT⟩ := physT_symW
  obtain ⟨C_nc, c_nc, hNc_bd⟩ := hNc
  obtain ⟨Kχ, hKχ0, hKχ⟩ := isCutoff_deriv_bound hχ
  set MΦ : ℝ := |uctAlphaFl|
  have hMΦ : 0 ≤ MΦ := abs_nonneg _
  set KΦ := Kmul (fun r => Kone r + Kpow (-1) r) (Kpow (-(3 / 2)))
  set M1 := MΦ * MR
  set M2_0 := MΦ * (MR + 2)
  set M3_0 := MΦ * (MR + 2)
  set M4 := |2 * K4| * MT
  set M_B0 := 2 * (M1 + M4)
  set M_BK := 2 * (M2_0 + M3_0)
  set cn : ℝ := max c_nc (2 * |C_nc| + 1)
  set c_d := max (max (max cs cR) (max cT cn)) 2
  have hc_d2 : 2 ≤ c_d := le_max_right _ _
  have h_pieces_cd :=
    let ⟨hδ0, _, hs_le, hL1_le, hLs_le, hsmall, _, _, _⟩ :=
      hsc 1 c_d (Or.inl rfl) ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    let hF := physF_sym (by positivity) hs_le hL1_le hLs_le
    let hR_cd := hR 1 c_d (Or.inl rfl) ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    let hT_cd := hT 1 c_d (Or.inl rfl) ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    physBump_pieces hχ hKχ (K1 := 1) (K4 := K4) (c := c_d) (δ := physDelta c_d) (s := physShift 1 c_d)
      (MΦ := MΦ) (αΦ := 3 / 2) (βΦ := 3 / 2) (MR := MR) (MT := MT)
      hδ0 hs_le hsmall hMR hMT hF hR_cd hT_cd
  refine ⟨c_d, a₀, a₁, M1, M2_0, M3_0, M4, M_B0, M_BK,
    KpDiff Kχ KΦ KR, KpMar1 Kχ KΦ KR, KpMar2 Kχ KΦ KR, KpTr Kχ KT, KpTot Kχ KΦ KR KT,
    hc_d2, ha₀, ha₁, mul_nonneg hMΦ hMR, mul_nonneg hMΦ (by linarith only [hMR]),
    mul_nonneg hMΦ (by linarith only [hMR]), mul_nonneg (abs_nonneg _) hMT, by positivity, by positivity, ?_, ?_⟩
  · intro r
    obtain ⟨hp1, hp2, hp3, hp4⟩ := h_pieces_cd
    have hp1k := hp1.K_nonneg r
    have hp2k := hp2.K_nonneg r
    have hp3k := hp3.K_nonneg r
    have hp4k := hp4.K_nonneg r
    exact ⟨hp1k, hp2k, hp3k, hp4k, by unfold KpTot; linarith only [hp1k, hp2k, hp3k, hp4k]⟩
  · intro K1 ε c hK1 hε hc
    have hc' := hc
    simp only [c_d, max_le_iff] at hc'
    obtain ⟨⟨⟨hcs', hcR'⟩, ⟨hcT', hcn'⟩⟩, hc2⟩ := hc'
    have hc0 : 0 < c := by linarith only [hc2]
    have hc1 : 1 ≤ c := by linarith only [hc2]
    obtain ⟨hδ0, hδ1, hs_le, hL1_le, hLs_le, hsmall, hδ_lo, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
    have hδ_le1 : physDelta c ≤ 1 := by linarith only [hδ0, hδ1]
    have hsqrt_δ : a₀ ≤ Real.sqrt c * physDelta c := by
      have hsq : Real.sqrt c * c ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc0]; norm_num
      calc a₀ = a₀ * c ^ (-(1 / 2 : ℝ)) * Real.sqrt c := by rw [mul_assoc, mul_comm (c ^ _), hsq, mul_one]
        _ ≤ physDelta c * Real.sqrt c := mul_le_mul_of_nonneg_right hδ_lo (Real.sqrt_nonneg _)
        _ = Real.sqrt c * physDelta c := mul_comm _ _
    have hnc_bounds : 1 / 2 ≤ 1 / Nc ε c ∧ 1 / Nc ε c ≤ 2 := by
      simp only [cn, max_le_iff] at hcn'
      have h1 := hNc_bd ε c hε hcn'.1
      have h2 : C_nc * c⁻¹ ≤ 1 / 2 := by
        have h3 : |C_nc| * c⁻¹ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_iff₀ hc0]; linarith only [hcn'.2]
        exact (mul_le_mul_of_nonneg_right (le_abs_self C_nc) (inv_nonneg.mpr hc0.le)).trans h3
      have h3 : -(1 / 2 : ℝ) ≤ C_nc * c⁻¹ := by
        have h3' : |C_nc| * c⁻¹ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_iff₀ hc0]; linarith only [hcn'.2]
        have h4 : -(|C_nc| * c⁻¹) ≤ C_nc * c⁻¹ := by
          have := mul_le_mul_of_nonneg_right (neg_abs_le C_nc) (inv_nonneg.mpr hc0.le)
          linarith only [this]
        linarith only [h3', h4]
      have hNc_lo : 1 / 2 ≤ Nc ε c := by linarith only [(abs_le.mp h1).1, h2, h3]
      have hNc_hi : Nc ε c ≤ 2 := by linarith only [(abs_le.mp h1).2, h2]
      have hNc_pos : 0 < Nc ε c := by linarith only [hNc_lo]
      exact ⟨(le_div_iff₀ hNc_pos).mpr (by linarith only [hNc_hi]),
        (div_le_iff₀ hNc_pos).mpr (by linarith only [hNc_lo])⟩
    obtain ⟨hn_lo, hn_hi⟩ := hnc_bounds
    have hF := physF_sym (by positivity) hs_le hL1_le hLs_le
    have hR_c := hR ε c hε hcR'
    have hT_c := hT ε c hε hcT'
    obtain ⟨hp1, hp2, hp3, hp4⟩ := physBump_pieces hχ hKχ (K1 := K1) (K4 := K4) (c := c)
      (δ := physDelta c) (s := physShift ε c) (MΦ := MΦ) (αΦ := 3 / 2) (βΦ := 3 / 2)
      (MR := MR) (MT := MT) hδ0 hs_le hsmall hMR hMT hF hR_c hT_c
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hp1
    rw [show (3 / 2 : ℝ) + 2 = 7 / 2 by norm_num] at hp2
    have hz : ∀ x : ℝ, x < 3 / 2 * physDelta c → χ (x / (3 * physDelta c)) = 0 := fun x hx =>
      hχ.zero _ (by rw [div_le_iff₀ (by positivity)]; linarith only [hx, hδ0])
    have hp2_M : |K1 * c⁻¹ ^ 2| * M2_0 = M2_0 * K1 * c ^ (-2 : ℝ) := by
      rw [abs_of_nonneg (by positivity),
        show c⁻¹ ^ 2 = c ^ (-2 : ℝ) by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast, inv_pow]]
      ring
    have hp3_M : |K1 * c⁻¹| * M3_0 = M3_0 * K1 * c⁻¹ := by
      rw [abs_of_nonneg (by positivity)]; ring
    have hBeq : physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
        (physOscDatum StripKernelChoice.star K4 T1 alpha ε c) (physF (physShift ε c) (physL1 T1 ε c))
        (fun L => tau0 L ^ 4 * uctIfl L) =
        fun x => (1 / Nc ε c) * ((χ (x / (3 * physDelta c)) * physGamma c (physShift ε c) x *
          (physF (physShift ε c) (physL1 T1 ε c) x * (physOscDatum StripKernelChoice.star K4 T1 alpha ε c x /
            physF (physShift ε c) (physL1 T1 ε c) x) - physF (physShift ε c) (physL1 T1 ε c) x)) +
          (χ (x / (3 * physDelta c)) * physGamma c (physShift ε c) x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) *
            (physF (physShift ε c) (physL1 T1 ε c) x * (physOscDatum StripKernelChoice.star K4 T1 alpha ε c x /
              physF (physShift ε c) (physL1 T1 ε c) x) + physF (physShift ε c) (physL1 T1 ε c) x))) +
          (χ (x / (3 * physDelta c)) * physGamma c (physShift ε c) x * (K1 * c⁻¹ *
            (physF (physShift ε c) (physL1 T1 ε c) x * (physOscDatum StripKernelChoice.star K4 T1 alpha ε c x /
              physF (physShift ε c) (physL1 T1 ε c) x) + physF (physShift ε c) (physL1 T1 ε c) x))) +
          (2 * K4 * (χ (x / (3 * physDelta c)) * ((1 - χ (x / (6 * physDelta c))) * (tau0 x ^ 4 * uctIfl x))))) := by
      rw [physBump_eq_ratio hχ hδ0 hs_le hL1_le]
      funext x
      simp only [physBump, physEta]
      ring
    have hp4_nn : ∀ x : ℝ, 0 ≤ 2 * K4 * (χ (x / (3 * physDelta c)) *
        ((1 - χ (x / (6 * physDelta c))) * (tau0 x ^ 4 * uctIfl x))) := fun x => by
      rcases le_or_gt x 0 with hx0 | hx0
      · have hx3 : x / (3 * physDelta c) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith only [hx0, hδ0]
        simp [hχ.zero _ hx3]
      · have hχ3 : 0 ≤ χ (x / (3 * physDelta c)) := (hχ.mem _).1
        have hχ6 : 0 ≤ 1 - χ (x / (6 * physDelta c)) := sub_nonneg.mpr (hχ.mem _).2
        have hifl : 0 ≤ uctIfl x := (uctIfl_pos' hx0).le
        have ht4 : 0 ≤ tau0 x ^ 4 := pow_nonneg (tau0_pos hx0).le 4
        have hK40 : 0 ≤ 2 * K4 := by linarith only [hK4]
        exact mul_nonneg hK40 (mul_nonneg hχ3 (mul_nonneg hχ6 (mul_nonneg ht4 hifl)))
    have hp4_far : ∀ x : ℝ, 6 * physDelta c ≤ x →
        2 * K4 * (χ (x / (3 * physDelta c)) * ((1 - χ (x / (6 * physDelta c))) * (tau0 x ^ 4 * uctIfl x))) = 0 := fun x hx => by
      have hx6 : 1 ≤ x / (6 * physDelta c) := by rw [le_div_iff₀ (by positivity)]; linarith only [hx]
      simp [hχ.one _ hx6]
    have hprof0 := physBump_profile hχ hKχ (n := 1 / Nc ε c) (c := c) (δ := physDelta c)
      (s := physShift ε c) (K1 := K1) (K4 := K4) (MΦ := MΦ) (MR := MR) (MT := MT)
      (F := physF (physShift ε c) (physL1 T1 ε c))
      (R := fun x => physOscDatum StripKernelChoice.star K4 T1 alpha ε c x / physF (physShift ε c) (physL1 T1 ε c) x)
      (T4 := fun L => tau0 L ^ 4 * uctIfl L) hδ0 hs_le hsmall hMΦ hMR hMT hF hR_c hT_c
    have hM_le : |1 / Nc ε c| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) +
        |2 * K4| * MT) ≤ M_B0 + M_BK * K1 * c⁻¹ := by
      have hn_abs : |1 / Nc ε c| ≤ 2 := by rw [abs_of_nonneg (by linarith only [hn_lo])]; exact hn_hi
      have hc2_1 : c⁻¹ ^ 2 ≤ c⁻¹ := by
        have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
        nlinarith only [hci, inv_nonneg.mpr hc0.le]
      have ha1 : |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) ≤ M2_0 * K1 * c⁻¹ := by
        rw [abs_of_nonneg (by positivity)]
        calc K1 * c⁻¹ ^ 2 * (MΦ * (MR + 2)) ≤ K1 * c⁻¹ * (MΦ * (MR + 2)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2_1 hK1) (mul_nonneg hMΦ (by linarith only [hMR]))
          _ = M2_0 * K1 * c⁻¹ := by dsimp only [M2_0]; ring
      have ha2 : |K1 * c⁻¹| * (MΦ * (MR + 2)) = M3_0 * K1 * c⁻¹ := by
        rw [abs_of_nonneg (by positivity)]; dsimp only [M3_0]; ring
      have hpos_sum : 0 ≤ MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT := by
        positivity
      calc |1 / Nc ε c| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT)
          ≤ 2 * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT) :=
            mul_le_mul_of_nonneg_right hn_abs hpos_sum
        _ ≤ 2 * (M1 + (M2_0 * K1 * c⁻¹ + M3_0 * K1 * c⁻¹) + M4) := by
            dsimp only [M1, M4]; linarith only [ha1, ha2]
        _ = M_B0 + M_BK * K1 * c⁻¹ := by dsimp only [M_B0, M_BK]; ring
    have hprof : BumpProfile (3 / 2) (physDelta c) (M_B0 + M_BK * K1 * c⁻¹) (7 / 2) (3 / 2)
        (KpTot Kχ KΦ KR KT)
        (physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
          (physOscDatum StripKernelChoice.star K4 T1 alpha ε c) (physF (physShift ε c) (physL1 T1 ε c))
          (fun L => tau0 L ^ 4 * uctIfl L)) := by
      rw [physBump_eq_ratio hχ hδ0 hs_le hL1_le]
      exact {
        smooth := hprof0.smooth
        support := hprof0.support
        near := fun k x hx0 hx1 => (hprof0.near k x hx0 hx1).trans (by
          have hxpos : 0 ≤ x := le_trans (by positivity) hx0
          have hKp : 0 ≤ KpTot Kχ KΦ KR KT k := by
            unfold KpTot
            linarith only [hp1.K_nonneg k, hp2.K_nonneg k, hp3.K_nonneg k, hp4.K_nonneg k]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le hKp) (Real.rpow_nonneg hxpos _))
        far := fun k x hx1 => (hprof0.far k x hx1).trans (by
          have hxpos : 0 ≤ x := le_trans zero_le_one hx1
          have hKp : 0 ≤ KpTot Kχ KΦ KR KT k := by
            unfold KpTot
            linarith only [hp1.K_nonneg k, hp2.K_nonneg k, hp3.K_nonneg k, hp4.K_nonneg k]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le hKp) (Real.rpow_nonneg hxpos _)) }
    refine ⟨⟨hδ_lo, hδ_hi, hsqrt_δ, hδ0, hδ_le1, hδ1, h6δ, hn_lo, hn_hi, hs_le, hL1_le⟩, hBeq,
      BSym_of_symW hp1 hδ0 (mul_nonneg hMΦ hMR) (by norm_num) (fun x hx => by simp [hz x hx]),
      ?_, ?_, BSym_of_symW hp4 hδ0 (mul_nonneg (abs_nonneg _) hMT) (by norm_num) (fun x hx => by simp [hz x hx]),
      hp4_nn, hp4_far, hprof⟩
    · have hp2_b := BSym_of_symW hp2 hδ0 (mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith only [hMR])))
        (le_refl _) (fun x hx => by simp [hz x hx])
      rwa [hp2_M] at hp2_b
    · have hp3_b := BSym_of_symW hp3 hδ0 (mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith only [hMR])))
        (le_refl _) (fun x hx => by simp [hz x hx])
      rwa [hp3_M] at hp3_b

end Decomposition

section Pretrans

/-- **Regime 1 (`L ≤ 3 δ_L / 4`)**: `|normDensity (ctWbump B ε c) c ξ| ≤ c⁻²`. -/
theorem physBump_pretrans_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha Nc : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) (hNc : FctSplittingNormStmt Nc) :
    ∀ K1 : ℝ, 0 ≤ K1 → ∃ c₀ : ℝ, 2 ≤ c₀ ∧
      ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
        Real.log (Real.pi ^ 2 * ξ) ≤ 3 / 4 * physDelta c →
        |normDensity (ctWbump (physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
            (physOscDatum StripKernelChoice.star K4 T1 alpha ε c)
            (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)) ε c) c ξ| ≤ c ^ (-2 : ℝ) := by
  obtain ⟨c_d, a₀, _, _, _, _, _, M_B0, M_BK, _, _, _, _, K_B, _, ha₀, _, _, _, _, _, hMB0, hMBK, _, hdec⟩ :=
    physBump_decomp hχ hK4 hwarp hNc
  obtain ⟨C_m, κ_m, hCm0, hκm0, hmain⟩ := fct_bump5_main_small (α := 7 / 2) (β := 3 / 2) le_rfl K_B ha₀
  obtain ⟨C_r, κ_r, hCr0, hκr0, hrefl⟩ := fct_bump5_refl (α := 7 / 2) (β := 3 / 2) le_rfl K_B ha₀
  intro K1 hK1
  set Mtot : ℝ := M_B0 + M_BK * K1
  set C_exp : ℝ := (C_m * (Nat.factorial 12 : ℝ) * (κ_m ^ 12)⁻¹ + C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹) * Mtot
  set c_r1 : ℝ := (1 / a₀ + 1) ^ 2
  set c₀ : ℝ := max (max c_d c_r1) (max 2 (C_exp + 1))
  refine ⟨c₀, le_max_of_le_right (le_max_left _ _), fun ε c ξ hε hc hξ hL => ?_⟩
  simp only [c₀, max_le_iff] at hc
  obtain ⟨⟨hcd', hcr1'⟩, ⟨hc2, hcexp'⟩⟩ := hc
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  obtain ⟨⟨_, _, hsqrt_δ, hδ0, hδ1', hδ32, _, _, _, _, _⟩, _, _, _, _, _, _, _, hprof⟩ := hdec K1 ε c hK1 hε hcd'
  have hMB_le : M_B0 + M_BK * K1 * c⁻¹ ≤ Mtot := by
    have hci : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
    have hmul : M_BK * K1 * c⁻¹ ≤ M_BK * K1 * 1 := mul_le_mul_of_nonneg_left hci (mul_nonneg hMBK hK1)
    dsimp only [Mtot]; linarith only [hmul]
  have hM0' : 0 ≤ M_B0 + M_BK * K1 * c⁻¹ := by positivity
  have ha0_sq : 1 ≤ a₀ * Real.sqrt c := by
    have h1 : 1 / a₀ + 1 ≤ Real.sqrt c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / a₀ + 1)]; exact Real.sqrt_le_sqrt hcr1'
    have h2 : 1 ≤ a₀ * (1 / a₀ + 1) := by field_simp; linarith only [ha₀]
    calc 1 ≤ a₀ * (1 / a₀ + 1) := h2
      _ ≤ a₀ * Real.sqrt c := mul_le_mul_of_nonneg_left h1 ha₀.le
  have hL' : Real.log (Real.pi ^ 2 * ξ) ≤ 3 / 2 * physDelta c / 2 := by linarith only [hL]
  set B := physBump χ (1 / Nc ε c) c (physDelta c) (physShift ε c) K1 K4
    (physOscDatum StripKernelChoice.star K4 T1 alpha ε c)
    (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L)
  have hm := hmain B (physDelta c) (M_B0 + M_BK * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 hM0' hc1 hsqrt_δ hξ hL' hprof
  have hr := (hrefl B (physDelta c) (M_B0 + M_BK * K1 * c⁻¹) c ξ hδ0 hδ1' hδ32 hM0' hc2 ha0_sq hsqrt_δ hξ hprof).1
  have hsqsq : Real.sqrt (Real.sqrt c) = c ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num
  rw [hsqsq] at hm
  have hc3_pos : 0 < c ^ 3 := by positivity
  have hm_bd : ‖bumpHmain c B ξ‖ * c ^ 3 ≤ C_m * (Nat.factorial 12 : ℝ) * (κ_m ^ 12)⁻¹ * Mtot := by
    calc ‖bumpHmain c B ξ‖ * c ^ 3
        ≤ C_m * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_m * c ^ (1 / 4 : ℝ))) * c ^ 3 :=
          mul_le_mul_of_nonneg_right hm hc3_pos.le
      _ ≤ C_m * Mtot * (Real.exp (-(κ_m * c ^ (1 / 4 : ℝ))) * c ^ 3) := by
          calc C_m * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_m * c ^ (1 / 4 : ℝ))) * c ^ 3
              = (C_m * (M_B0 + M_BK * K1 * c⁻¹)) * (Real.exp (-(κ_m * c ^ (1 / 4 : ℝ))) * c ^ 3) := by ring
            _ ≤ (C_m * Mtot) * (Real.exp (-(κ_m * c ^ (1 / 4 : ℝ))) * c ^ 3) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB_le hCm0) (by positivity)
      _ ≤ C_m * Mtot * ((Nat.factorial 12 : ℝ) * (κ_m ^ 12)⁻¹) :=
          mul_le_mul_of_nonneg_left (exp_quarter_absorb hκm0 hc0) (by positivity)
      _ = C_m * (Nat.factorial 12 : ℝ) * (κ_m ^ 12)⁻¹ * Mtot := by ring
  have hr_bd : ‖bumpHrefl c B ξ‖ * c ^ 3 ≤ C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * Mtot := by
    calc ‖bumpHrefl c B ξ‖ * c ^ 3
        ≤ C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3 :=
          mul_le_mul_of_nonneg_right hr hc3_pos.le
      _ ≤ C_r * Mtot * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := by
          calc C_r * (M_B0 + M_BK * K1 * c⁻¹) * Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3
              = (C_r * (M_B0 + M_BK * K1 * c⁻¹)) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) := by ring
            _ ≤ (C_r * Mtot) * (Real.exp (-(κ_r * Real.sqrt c)) * c ^ 3) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB_le hCr0) (by positivity)
      _ ≤ C_r * Mtot * ((Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹) :=
          mul_le_mul_of_nonneg_left (exp_half_absorb hκr0 hc0) (by positivity)
      _ = C_r * (Nat.factorial 6 : ℝ) * (κ_r ^ 6)⁻¹ * Mtot := by ring
  change |normDensity (ctWbump B ε c) c ξ| ≤ c ^ (-2 : ℝ)
  rw [normDensity_ctWbump hc1 hδ0 hδ32 le_rfl hM0' hξ hprof]
  have hnorm_sum : ‖bumpHmain c B ξ + (ε : ℂ) * bumpHrefl c B ξ‖ ≤ ‖bumpHmain c B ξ‖ + ‖bumpHrefl c B ξ‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases hε with rfl | rfl <;> simp
  have hre_bd : |(bumpHmain c B ξ + (ε : ℂ) * bumpHrefl c B ξ).re| * c ^ 3 ≤ C_exp := by
    have h1 := mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hnorm_sum) hc3_pos.le
    rw [add_mul] at h1
    exact h1.trans (by dsimp only [C_exp]; linarith only [hm_bd, hr_bd])
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hc0.le, Real.rpow_natCast]
  have h3 : (c ^ 2)⁻¹ * c ^ 3 = c := by field_simp
  have h4 : |(bumpHmain c B ξ + (ε : ℂ) * bumpHrefl c B ξ).re| * c ^ 3 ≤ (c ^ 2)⁻¹ * c ^ 3 := by
    linarith only [hre_bd, hcexp', h3]
  exact le_of_mul_le_mul_right h4 hc3_pos

end Pretrans

/-- info: 'FormalResearch.SignUncertainty.physBump_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_decomp

/-- info: 'FormalResearch.SignUncertainty.physBump_pretrans_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_pretrans_bound

end FormalResearch.SignUncertainty

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCompDPart1
public import FormalResearch.SignUncertainty.FctMainHankelDefs

/-!
# The outer compensator `D_{τ₁}` of `fct:main-hankel` as a definition (`fct:comp-D`)

`fctDcomp K4 alpha ε c = exp (g_D[v])` on the closed strip, with `v = vTotal ⋆ K4 c α τ₁` the localized compensator density
`v = v₀ + v₁ + v_α` of Lemma FCT.3 (`fct:comp-D`, `FctCompDPart1`), `H₀ = H_*` (`StripKernelChoice.star`; the paper's warp
witness uses `H_*`), `τ₁ = c^{-1/4}`, and `α = alpha ε c` the zero-solve value of `fct:warp-asymp` (1).  `g_D` is the continuous extension
to the closed strip (`stripCompGExt`; the Poisson integral itself is singular on the boundary).

`fctDcomp_bound`: `D_{τ₁}` is bounded on the closed strip for large `c` (the `r = 0` case of the global closed-strip bound of
`fct_comp_D_part1`, with `|α| ≤ C c^{-2/3} ≤ c^{-1/2} = τ₁²` from the warp-zero size bound), uniformly in `(ε, c)`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.CtOuter

/-- **`D_{τ₁}`** of `fct:comp-D`: `exp (g_D[v])` on the closed strip, `v = v₀ + v₁ + v_α` (`vTotal`) for `H₀ = H_*`, `τ₁ = c^{-1/4}`,
`α = alpha ε c`. -/
noncomputable def fctDcomp (K4 : ℝ) (alpha : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ → ℂ :=
  fun ε c ζ => Complex.exp (stripCompGExt (vTotal StripKernelChoice.star K4 c (alpha ε c) (c ^ (-(1 / 4 : ℝ)))) ζ)

/-- **The smooth data behind `D_{τ₁}`** (`fct:comp-D`): for large `c`, `D_{τ₁} = exp (g_D[v])` on the closed strip, with `v = vTotal` even,
smooth and compactly supported, and `‖g_D[v^{(r)}]‖ ≤ B_r` on the closed strip for `r = 0, 1, 2`, uniformly in `(ε, c)`
(the global closed-strip bound of `fct_comp_D_part1`, `τ₁ ≤ 1`). -/
theorem fctDcomp_vdata {K4 : ℝ} (hK4 : 1 ≤ K4) {alpha : ℝ → ℝ → ℝ}
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ (B : ℕ → ℝ) (c₀ : ℝ), ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∃ v : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ (∀ t, v (-t) = v t) ∧
      (∀ r : ℕ, r ≤ 2 → ∀ ζ ∈ closedStrip, ‖stripCompGExt (iteratedDeriv r v) ζ‖ ≤ B r) ∧
      ∀ ζ, fctDcomp K4 alpha ε c ζ = Complex.exp (stripCompGExt v ζ) := by
  obtain ⟨Kα, cα, hαb⟩ := hα
  obtain ⟨τ₀, hτ₀, -, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m, CL0b, CL0m, CLa, CL1b, CL1m,
    Ctail, Cint, -, -, -, -, hmain⟩ := fct_comp_D_part1 StripKernelChoice.star
  set B : ℕ → ℝ := fun r => |(Cv0b r + K4 * Cv0m r + Cv1b r + K4 * Cv1m r + Cva r) +
    max (Cth0b r + K4 * Cth0m r + Cth1b r + K4 * Cth1m r + Ctha r)
      (Ctail r * ((CL0b + K4 * CL0m) + (CL1b + K4 * CL1m) + CLa) * (12 : ℝ) ^ (-(1 + (r : ℤ))))| with hB
  refine ⟨B, max (max cα (τ₀⁻¹ ^ 4)) (max (|Kα| + 1) 1 ^ 6), fun ε c hε hc => ?_⟩
  simp only [max_le_iff] at hc
  obtain ⟨⟨hcα, hcτ⟩, hcK⟩ := hc
  have h1 : 1 ≤ c := by
    have : (1 : ℝ) ≤ max (|Kα| + 1) 1 ^ 6 := one_le_pow₀ (le_max_right _ _)
    linarith
  have hcpos : 0 < c := by linarith
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ)) with hτ₁
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hcpos _
  have hτ₁4 : τ₁ ^ 4 = c⁻¹ := by
    rw [hτ₁, ← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]
    norm_num [Real.rpow_neg_one]
  have hτ₁4c : τ₁ ^ 4 * c = 1 := by rw [hτ₁4]; field_simp
  have hτ₁2 : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [hτ₁, ← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]; norm_num
  have hτ₁le1 : τ₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  have hτle : τ₁ ≤ τ₀ := by
    have h4 : τ₀⁻¹ ^ 4 ≤ c := hcτ
    have hτ₀4 : 0 < τ₀⁻¹ ^ 4 := by positivity
    have : τ₁ ^ 4 ≤ τ₀ ^ 4 := by
      rw [hτ₁4]
      have := inv_anti₀ hτ₀4 h4
      simpa [inv_pow] using this
    exact le_of_pow_le_pow_left₀ (by norm_num) hτ₀.le this
  have hαle : |alpha ε c| ≤ τ₁ ^ 2 := by
    refine (hαb ε c hε hcα).trans ?_
    have h6 : (|Kα| + 1) ≤ c ^ (1 / 6 : ℝ) := by
      have hK : (|Kα| + 1) ^ 6 ≤ c := by
        have : max (|Kα| + 1) 1 ^ 6 ≤ c := hcK
        exact le_trans (pow_le_pow_left₀ (by positivity) (le_max_left _ _) 6) this
      have := Real.rpow_le_rpow (by positivity) hK (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this |> fun h => by
        simpa using h
    have hsplit : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hcpos]; norm_num
    have hinv : Kα * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
      have hpos : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hcpos _
      have : c ^ (-(1 / 6 : ℝ)) = (c ^ (1 / 6 : ℝ))⁻¹ := Real.rpow_neg hcpos.le _
      rw [this, ← div_eq_mul_inv, div_le_one hpos]
      linarith [le_abs_self Kα]
    rw [hτ₁2, hsplit, ← mul_assoc, mul_comm Kα, mul_assoc]
    have hp : 0 ≤ c ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hcpos _).le
    nlinarith
  have hbound := hmain (K4 := K4) (c := c) (α := alpha ε c) (τ₁ := τ₁) hK4 hcpos hτ₁pos hτle hτ₁4c hαle
  obtain ⟨⟨-, -, -, -, -, hvcd⟩, ⟨-, -, -, -, -, hveven⟩, -, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvcs⟩,
    -, -, -, -, -, -, -, hglob, -⟩ := hbound
  refine ⟨_, hvcd, hvcs, hveven, fun r hr ζ hζ => ?_, fun ζ => rfl⟩
  have h0 := hglob r ζ hζ
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul] at h0
  refine h0.trans ?_
  have hτ2 : τ₁ ^ ((2 : ℤ) - (r : ℤ)) ≤ 1 := by
    have : (2 : ℤ) - (r : ℤ) = ((2 - r : ℕ) : ℤ) := by omega
    rw [this, zpow_natCast]
    exact pow_le_one₀ hτ₁pos.le hτ₁le1
  calc _ ≤ |_| * τ₁ ^ ((2 : ℤ) - (r : ℤ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |_| * 1 := mul_le_mul_of_nonneg_left hτ2 (abs_nonneg _)
    _ = B r := by rw [mul_one]

/-- `D_{τ₁}` is bounded on the closed strip, uniformly for large `c` (`fct:comp-D`, global bound with `r = 0`). -/
theorem fctDcomp_bound {K4 : ℝ} (hK4 : 1 ≤ K4) {alpha : ℝ → ℝ → ℝ}
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ ζ ∈ closedStrip, ‖fctDcomp K4 alpha ε c ζ‖ ≤ C := by
  obtain ⟨B, c₀, h⟩ := fctDcomp_vdata hK4 hα
  refine ⟨Real.exp (B 0), c₀, fun ε c hε hc ζ hζ => ?_⟩
  obtain ⟨v, -, -, -, hb, hD⟩ := h ε c hε hc
  rw [hD, Complex.norm_exp]
  have := hb 0 (by norm_num) ζ hζ
  simp only [iteratedDeriv_zero] at this
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans this)

/-- info: 'FormalResearch.SignUncertainty.fctDcomp_vdata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctDcomp_vdata

/-- info: 'FormalResearch.SignUncertainty.fctDcomp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctDcomp_bound

end FormalResearch.SignUncertainty

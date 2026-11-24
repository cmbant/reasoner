module

public import FormalResearch.SignUncertainty.Gt1Interface

/-!
# `O.5(2)` = `(e6)`: the middle band of `I_main`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `O.5`(2) (`u1co:O5`, `(e6)`): for `100 ≤ S` and `0 < L ≤ 0.002` (`L = log(π²ξ) = π² ε² S`,
`ε = c^{-1/3}`), with `ṽ = κ₀(L) β₁ S`,
`|I_main[F](ξ) - (k β₁/(π² ξ)) F_ψ(-ṽ - ε/(2c_s))| ≤ C_mid ξ⁻¹ [S^{-3/2} ε² S + c^{-5/2}]`.

* `o5_e6`: this statement for any seed `X` with `HasU2` and the `GT.1` bounds `Gt1Bounds A (liftW X δ₀ m)` (derived from `middle_transfer_gt1`; `F_ψ = windowSmooth`).
* `o5_e6_airySeed`: the same for `X = airySeedU2 a b c₀` with `|a|, |b|, |c₀| ≤ R` and `δ₀ ∈ [0, 2]`, from the single named input `Gt1BasisInput m`; the constant depends
  on `m`, `R` only.

Status: proved, conditional on the named hypothesis `O4QuotientBound L` and on `Gt1Bounds` (`Gt1BasisInput m`).  Not formalised here: those two hypotheses themselves.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- **`(e6)`**, for a seed with the `GT.1` bounds. -/
theorem o5_e6 {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℝ → ℝ} {δ₀ : ℝ} {m : ℕ} {c ξ L : ℝ},
      HasU2 X → Continuous X → 0 ≤ δ₀ → 2 ≤ c → 0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) →
      O4QuotientBound L → 0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ → Gt1Bounds A (liftW X δ₀ m) →
      ‖iMain X δ₀ m c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
          ((windowSmooth δ₀ m X (-(edgeKappa0 L * ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs))) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (hbS c ξ ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * hbS c ξ) + c ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨C0, hC0, hM⟩ := middle_transfer_gt1 hϑ A hA
  refine ⟨C0 * Real.pi ^ 2, by positivity, ?_⟩
  intro X δ₀ m c ξ L hX hXc hδ hc hξ hLdef hQ hL0 hL2 hS100 hG
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hcε : c * liftEps c ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  set S : ℝ := hbS c ξ with hSdef
  have hSe : S = L / (Real.pi ^ 2 * liftEps c ^ 2) := by rw [hSdef, hbS, ← hLdef]
  have hS : L = Real.pi ^ 2 * liftEps c ^ 2 * S := by rw [hSe]; field_simp
  have hS0 : 0 < S := by linarith
  obtain ⟨hpf1, -⟩ := param_facts hL0 hL2 hε hcε hS hS100
  have hmain := hM hX hXc hδ hc hξ hLdef hQ hL0 hL2 hS100 hG
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hcs := ceCs_pos
  have hcb : Real.pi ^ 2 = ceCs * ceBeta1 := ceCs_mul_ceBeta1.symm
  -- the argument of the window
  have harg : (c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs =
      edgeKappa0 L * ceBeta1 * S + liftEps c / (2 * ceCs) := by
    rw [hpf1, hcb]; field_simp
  rw [harg] at hmain
  -- the prefactor
  have hpre : (ξ : ℂ) * (((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ)) : ℂ) = (ceK : ℂ) / (ceCs : ℂ) := by
    have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
    have hcs' : (ceCs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcs.ne'
    have hb' : (ceBeta1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceBeta1_pos.ne'
    rw [hcb]; push_cast; field_simp
  have hid : iMain X δ₀ m c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
      ((windowSmooth δ₀ m X (-(edgeKappa0 L * ceBeta1 * S + liftEps c / (2 * ceCs))) : ℝ) : ℂ) =
      (ξ : ℂ)⁻¹ * ((ξ : ℂ) * iMain X δ₀ m c ξ - ((ceK : ℂ) / (ceCs : ℂ)) *
        ((windowSmooth δ₀ m X (-(edgeKappa0 L * ceBeta1 * S + liftEps c / (2 * ceCs))) : ℝ) : ℂ)) := by
    have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
    rw [← hpre]; field_simp
  rw [hid, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
  have hL' : S ^ (-(3 / 2 : ℝ)) * L = Real.pi ^ 2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S)) := by
    rw [hS]; ring
  have hB : 0 ≤ S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) := by positivity
  have hc52 : 0 ≤ c ^ (-(5 / 2 : ℝ)) := by positivity
  calc ξ⁻¹ * ‖(ξ : ℂ) * iMain X δ₀ m c ξ - ((ceK : ℂ) / (ceCs : ℂ)) *
        ((windowSmooth δ₀ m X (-(edgeKappa0 L * ceBeta1 * S + liftEps c / (2 * ceCs))) : ℝ) : ℂ)‖
      ≤ ξ⁻¹ * (C0 * (S ^ (-(3 / 2 : ℝ)) * L + c ^ (-(5 / 2 : ℝ)))) := by gcongr
    _ ≤ C0 * Real.pi ^ 2 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) := by
        rw [hL']
        have h1 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hξi : 0 ≤ ξ⁻¹ := by positivity
        have : Real.pi ^ 2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S)) + c ^ (-(5 / 2 : ℝ)) ≤
            Real.pi ^ 2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) := by nlinarith
        calc ξ⁻¹ * (C0 * (Real.pi ^ 2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S)) + c ^ (-(5 / 2 : ℝ))))
            ≤ ξ⁻¹ * (C0 * (Real.pi ^ 2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))))) := by gcongr
          _ = _ := by ring

/-- `(e6)` for the one-level seeds with coefficients `|a|, |b|, |c₀| ≤ R`, uniform in `δ₀ ∈ [0, 2]`, from the named input `Gt1BasisInput m`. -/
theorem o5_e6_airySeed {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {m : ℕ} (h : Gt1BasisInput m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b c₀ δ₀ : ℝ} {c ξ L : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → δ₀ ∈ Icc (0 : ℝ) 2 →
      2 ≤ c → 0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) → O4QuotientBound L → 0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ →
      ‖iMain (airySeedU2 a b c₀) δ₀ m c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
          ((windowSmooth δ₀ m (airySeedU2 a b c₀) (-(edgeKappa0 L * ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs))) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (hbS c ξ ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * hbS c ξ) + c ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨A, hA, hb⟩ := gt1Bounds_airySeedU2 h
  obtain ⟨C, hC, hE⟩ := o5_e6 hϑ (A * (R + R + R)) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a b c₀ δ₀ c ξ L ha hb' hc' hδ hc hξ hL hQ hL0 hL2 hS
  have hGt := (hb a b c₀ δ₀ hδ).mono (B := A * (R + R + R)) (by gcongr)
  have hδ0 : 0 ≤ δ₀ := hδ.1
  have hX := hasU2_airySeedU2 a b c₀
  have hXc : Continuous (airySeedU2 a b c₀) := by
    exact ((continuous_const.mul continuous_ceF1).add (continuous_const.mul (continuous_ceG1 _))).add
      (continuous_const.mul (continuous_ceG1Deriv _))
  exact hE hX hXc hδ0 hc hξ hL hQ hL0 hL2 hS hGt

/-- info: 'FormalResearch.SignUncertainty.o5_e6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o5_e6
/-- info: 'FormalResearch.SignUncertainty.o5_e6_airySeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o5_e6_airySeed

end FormalResearch.SignUncertainty

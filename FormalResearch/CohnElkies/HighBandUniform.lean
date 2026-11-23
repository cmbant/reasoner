module

public import FormalResearch.CohnElkies.HighBandEstimate

/-!
# `O.3(2)`/`(e4)`, uniform over the coefficients of the one-level seeds

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `O.3`(2) (`u1co:O3`), used with a seed family that varies with `c`
(`u1co:O6`, `u1co:O9p`: `F_δ`, `δ = K c^{-1/3}`).  The one-level seeds `a f₁ + b g₁ + c₀ g₁'` are linear in `(a, b, c₀)`, and `I_main`
is linear in the seed (`iMain_airySeed_lin`), so the absolute estimate of `hb_estimate_airySeed` for the three basis seeds gives
`hb_estimate_airySeed_uniform`: constants `γ₁, γ₂, γ₃, C` depending only on `m` and the coefficient bound `R`, with
`γ₀ = a γ₁ + b γ₂ + c₀ γ₃`.  The `m₀ = 1` Hermite--Biehler seed family is the corollary `hb_estimate_hbSeed_m1_uniform`.

Status: proved, unconditional.  Not formalised: the identification of `γ₀` with `β_∞(F)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

lemma airySeedU2_eq_lin (a b c₀ : ℝ) :
    airySeedU2 a b c₀ = fun u => a * airySeedU2 1 0 0 u + b * airySeedU2 0 1 0 u + c₀ * airySeedU2 0 0 1 u := by
  funext u; simp [airySeedU2]

lemma airyTwistedLaplaceC_airySeedU2_lin (a b c₀ : ℝ) {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (airySeedU2 a b c₀) y =
      (a : ℂ) * airyTwistedLaplaceC (airySeedU2 1 0 0) y + (b : ℂ) * airyTwistedLaplaceC (airySeedU2 0 1 0) y +
        (c₀ : ℂ) * airyTwistedLaplaceC (airySeedU2 0 0 1) y := by
  rw [airySeedU2_eq_lin]
  have h1 := (hasU2_airySeedU2 1 0 0).integrable y hy
  have h2 := (hasU2_airySeedU2 0 1 0).integrable y hy
  have h3 := (hasU2_airySeedU2 0 0 1).integrable y hy
  have i1 : Integrable (fun u : ℝ => (((fun u => a * airySeedU2 1 0 0 u) u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (integrable_const_mul_ofReal h1 (b := a))
  have i2 : Integrable (fun u : ℝ => (((fun u => b * airySeedU2 0 1 0 u) u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (integrable_const_mul_ofReal h2 (b := b))
  rw [airyTwistedLaplaceC_add (X := fun u => a * airySeedU2 1 0 0 u + b * airySeedU2 0 1 0 u) (Y := fun u => c₀ * airySeedU2 0 0 1 u)
      ((i1.add i2).congr (ae_of_all _ fun u => by simp only [Pi.add_apply]; push_cast; ring))
      (integrable_const_mul_ofReal h3 (b := c₀)),
    airyTwistedLaplaceC_add (X := fun u => a * airySeedU2 1 0 0 u) (Y := fun u => b * airySeedU2 0 1 0 u) i1 i2,
    airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul]

lemma liftSymbol_airySeedU2_lin (a b c₀ δ₀ : ℝ) (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    liftSymbol (airySeedU2 a b c₀) δ₀ m w =
      (a : ℂ) * liftSymbol (airySeedU2 1 0 0) δ₀ m w + (b : ℂ) * liftSymbol (airySeedU2 0 1 0) δ₀ m w +
        (c₀ : ℂ) * liftSymbol (airySeedU2 0 0 1) δ₀ m w := by
  unfold liftSymbol
  rw [airyTwistedLaplaceC_airySeedU2_lin a b c₀ (by simp only [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le hw)]
  ring

/-- `I_main` is linear in the coefficients of the one-level seed. -/
theorem iMain_airySeed_lin (a b c₀ : ℝ) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    iMain (airySeedU2 a b c₀) δ₀ m c ξ =
      (a : ℂ) * iMain (airySeedU2 1 0 0) δ₀ m c ξ + (b : ℂ) * iMain (airySeedU2 0 1 0) δ₀ m c ξ +
        (c₀ : ℂ) * iMain (airySeedU2 0 0 1) δ₀ m c ξ := by
  have i1 := (hasU2_airySeedU2 1 0 0).integrable_iMainIntegrand hδ m hc hξ
  have i2 := (hasU2_airySeedU2 0 1 0).integrable_iMainIntegrand hδ m hc hξ
  have i3 := (hasU2_airySeedU2 0 0 1).integrable_iMainIntegrand hδ m hc hξ
  unfold iMain
  have hpt : ∀ v : ℝ, iMainIntegrand (airySeedU2 a b c₀) δ₀ m c ξ v =
      (a : ℂ) * iMainIntegrand (airySeedU2 1 0 0) δ₀ m c ξ v + (b : ℂ) * iMainIntegrand (airySeedU2 0 1 0) δ₀ m c ξ v +
        (c₀ : ℂ) * iMainIntegrand (airySeedU2 0 0 1) δ₀ m c ξ v := fun v => by
    unfold iMainIntegrand
    rw [liftSymbol_airySeedU2_lin a b c₀ δ₀ m (by simp)]
    ring
  simp_rw [hpt]
  have iA := i1.const_mul (a : ℂ)
  have iB := i2.const_mul (b : ℂ)
  have iC := i3.const_mul (c₀ : ℂ)
  have h12 := integral_add iA iB
  have h123 := integral_add (iA.add iB) iC
  simp only [Pi.add_apply] at h12 h123
  rw [h123, h12, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- **`(e4)`, uniform over the seed coefficients** `|a|, |b|, |c₀| ≤ R`.  The constants `γ₁, γ₂, γ₃` (the `γ₀` of the three basis seeds)
and `C` depend only on `m` and `R`; `γ₀ = a γ₁ + b γ₂ + c₀ γ₃`. -/
theorem hb_estimate_airySeed_uniform {m : ℕ} (hm : 1 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ γ₁ γ₂ γ₃ : ℝ, ∃ C > 0, ∀ {a b c₀ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R →
      ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ -
          (((a * γ₁ + b * γ₂ + c₀ * γ₃) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨γ₁, C₁, hC₁, h1⟩ := hb_estimate_airySeed 1 0 0 hm
  obtain ⟨γ₂, C₂, hC₂, h2⟩ := hb_estimate_airySeed 0 1 0 hm
  obtain ⟨γ₃, C₃, hC₃, h3⟩ := hb_estimate_airySeed 0 0 1 hm
  refine ⟨γ₁, γ₂, γ₃, (R + 1) * (C₁ + C₂ + C₃), by positivity, fun {a b c₀} ha hb hc {K M₁ c ξ} hK hM hc8 hc2k hξ hS hMS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have e1 := h1 hK hM hc8 hc2k hξ hS hMS
  have e2 := h2 hK hM hc8 hc2k hξ hS hMS
  have e3 := h3 hK hM hc8 hc2k hξ hS hMS
  rw [iMain_airySeed_lin a b c₀ hδ m hc0 hξ]
  set P : ℝ := hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) with hP
  set B : ℝ := M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 < hbS c ξ := by linarith
    positivity
  have hApos : 0 < hbA c ξ := by
    have hS0 : 0 < hbS c ξ := by linarith
    rw [hbA_eq hc0]; have := Real.pi_pos; positivity
  have hP0 : 0 ≤ P := by positivity
  have eq : (a : ℂ) * iMain (airySeedU2 1 0 0) (ceBeta1 * K * liftEps c / 2) m c ξ +
        (b : ℂ) * iMain (airySeedU2 0 1 0) (ceBeta1 * K * liftEps c / 2) m c ξ +
        (c₀ : ℂ) * iMain (airySeedU2 0 0 1) (ceBeta1 * K * liftEps c / 2) m c ξ -
      (((a * γ₁ + b * γ₂ + c₀ * γ₃) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ) =
      (a : ℂ) * (iMain (airySeedU2 1 0 0) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₁ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)) +
      (b : ℂ) * (iMain (airySeedU2 0 1 0) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₂ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)) +
      (c₀ : ℂ) * (iMain (airySeedU2 0 0 1) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₃ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)) := by
    push_cast; ring
  rw [eq]
  have n1 : ‖(a : ℂ) * (iMain (airySeedU2 1 0 0) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₁ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ))‖ ≤ R * (C₁ * B * P) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul ha e1 (norm_nonneg _) hR
  have n2 : ‖(b : ℂ) * (iMain (airySeedU2 0 1 0) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₂ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ))‖ ≤ R * (C₂ * B * P) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hb e2 (norm_nonneg _) hR
  have n3 : ‖(c₀ : ℂ) * (iMain (airySeedU2 0 0 1) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₃ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ))‖ ≤ R * (C₃ * B * P) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hc e3 (norm_nonneg _) hR
  have hBP : 0 ≤ B * P := mul_nonneg hB0 hP0
  calc _ ≤ _ := norm_add₃_le
    _ ≤ R * (C₁ * B * P) + R * (C₂ * B * P) + R * (C₃ * B * P) := by linarith
    _ ≤ (R + 1) * (C₁ + C₂ + C₃) * B * P := by
        have : R * (C₁ * B * P) + R * (C₂ * B * P) + R * (C₃ * B * P) = R * (C₁ + C₂ + C₃) * (B * P) := by ring
        rw [this]
        have : (R + 1) * (C₁ + C₂ + C₃) * B * P = (R + 1) * (C₁ + C₂ + C₃) * (B * P) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by nlinarith) hBP

/-- info: 'FormalResearch.CohnElkies.hb_estimate_airySeed_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hb_estimate_airySeed_uniform

/-- **`(e4)` for the `m₀ = 1` Hermite--Biehler seed family, uniform in `(γ₁, γ₂, δ, r)` with all four in `[-R', R']`**; the seed is
`airySeedU2 (-1 - γ₂ δ) (-γ₁ δ + γ₂ δ + r) (γ₂ δ)` (`hbSeed_m1_eq_airySeedU2`). -/
theorem hb_estimate_hbSeed_m1_uniform {m : ℕ} (hm : 1 ≤ m) (R' : ℝ) (hR' : 0 ≤ R') :
    ∃ g₁ g₂ g₃ : ℝ, ∃ C > 0, ∀ {γ₁ γ₂ δ r : ℝ}, |γ₁| ≤ R' → |γ₂| ≤ R' → |δ| ≤ R' → |r| ≤ R' →
      ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u)
          (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((((-1 - γ₂ * δ) * g₁ + (-γ₁ * δ + γ₂ * δ + r) * g₂ + (γ₂ * δ) * g₃) * Real.sqrt Real.pi *
              hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨g₁, g₂, g₃, C, hC, h⟩ := hb_estimate_airySeed_uniform hm (1 + 2 * R' ^ 2 + R') (by positivity)
  refine ⟨g₁, g₂, g₃, C, hC, fun {γ₁ γ₂ δ r} h1 h2 h3 h4 {K M₁ c ξ} hK hM hc8 hc2k hξ hS hMS => ?_⟩
  rw [hbSeed_m1_eq_airySeedU2]
  have b2 : |γ₂ * δ| ≤ R' ^ 2 := by rw [abs_mul]; nlinarith [abs_nonneg γ₂, abs_nonneg δ]
  have b1 : |γ₁ * δ| ≤ R' ^ 2 := by rw [abs_mul]; nlinarith [abs_nonneg γ₁, abs_nonneg δ]
  have ha : |-1 - γ₂ * δ| ≤ 1 + 2 * R' ^ 2 + R' := by
    calc |-1 - γ₂ * δ| ≤ |(-1 : ℝ)| + |γ₂ * δ| := by rw [sub_eq_add_neg, ← abs_neg (γ₂ * δ)]; exact abs_add_le _ _ |>.trans_eq' (by simp [abs_neg])
      _ ≤ _ := by rw [abs_neg, abs_one]; nlinarith
  have hb : |-γ₁ * δ + γ₂ * δ + r| ≤ 1 + 2 * R' ^ 2 + R' := by
    calc |-γ₁ * δ + γ₂ * δ + r| ≤ |-γ₁ * δ| + |γ₂ * δ| + |r| := abs_add_three _ _ _
      _ ≤ _ := by rw [neg_mul, abs_neg]; nlinarith
  have hc : |γ₂ * δ| ≤ 1 + 2 * R' ^ 2 + R' := by nlinarith
  exact h ha hb hc hK hM hc8 hc2k hξ hS hMS

/-- info: 'FormalResearch.CohnElkies.hb_estimate_hbSeed_m1_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hb_estimate_hbSeed_m1_uniform

end FormalResearch.CohnElkies

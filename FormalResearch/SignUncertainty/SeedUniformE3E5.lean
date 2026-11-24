module

public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.CohnElkies.DualBoundE3
public import FormalResearch.CohnElkies.HighBandUniform

/-!
# `(e3)` and `(e5)`, uniform over the one-level seeds `a f₁ + b g₁ + c₀ g₁'`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, the dual bound `(e3)` and the window translation `(e5)` (`O.5`(1)),
used with a seed family that varies with its coefficients `(a, b, c₀)`.  The dual integral `I_dual` is linear in the seed
(`iDual_airySeed_lin`, the analogue of `iMain_airySeed_lin`), so the single-seed bounds `iDual_bound_e3_hasU2` and
`window_translation` (for the bounded-coefficient constants of the basis seeds) give bounds uniform over `|a|, |b|, |c₀| ≤ R`:
`iDual_bound_e3_airySeed` (`(e3)`) and `window_translation_airySeed` (`(e5)`, with dual seed `σ · (the same seed)`, `σ = ±1`).

Status: proved, unconditional.  The constant depends only on `m` and `R` (and `S_w` for `(e5)`).  Not formalised: the
identification of the coefficients with the Hermite--Biehler data, and the range `200 ≤ c < 32768` of `(e5)` (inherited from
`window_translation`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `I_dual` is linear in the coefficients of the one-level seed. -/
theorem iDual_airySeed_lin (a b c₀ : ℝ) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    iDual (airySeedU2 a b c₀) δ₀ m c ξ =
      (a : ℂ) * iDual (airySeedU2 1 0 0) δ₀ m c ξ + (b : ℂ) * iDual (airySeedU2 0 1 0) δ₀ m c ξ +
        (c₀ : ℂ) * iDual (airySeedU2 0 0 1) δ₀ m c ξ := by
  have i1 := (hasU2_airySeedU2 1 0 0).integrable_iDualIntegrand hδ m hc hξ
  have i2 := (hasU2_airySeedU2 0 1 0).integrable_iDualIntegrand hδ m hc hξ
  have i3 := (hasU2_airySeedU2 0 0 1).integrable_iDualIntegrand hδ m hc hξ
  have hre : ∀ v : ℝ, 0 ≤ ((((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I).re := fun v => by
    simpa using Real.rpow_nonneg hc.le _
  unfold iDual
  have hpt : ∀ v : ℝ, iDualIntegrand (airySeedU2 a b c₀) δ₀ m c ξ v =
      (a : ℂ) * iDualIntegrand (airySeedU2 1 0 0) δ₀ m c ξ v + (b : ℂ) * iDualIntegrand (airySeedU2 0 1 0) δ₀ m c ξ v +
        (c₀ : ℂ) * iDualIntegrand (airySeedU2 0 0 1) δ₀ m c ξ v := fun v => by
    unfold iDualIntegrand
    rw [liftSymbol_airySeedU2_lin a b c₀ δ₀ m (hre v)]
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

/-- **`(e3)`, uniform over the seed coefficients** `|a|, |b|, |c₀| ≤ R`, with the constant depending only on `m` and `R`. -/
theorem iDual_bound_e3_airySeed {m : ℕ} (hm : 3 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {a b c₀ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → ∀ {δ₀ c ξ : ℝ}, δ₀ ∈ Set.Ioc (0 : ℝ) 2 → 2 ≤ c → 0 < ξ →
      1 ≤ hbS c ξ →
      ‖iDual (airySeedU2 a b c₀) δ₀ m c ξ‖ ≤ C * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C₁, hC₁, h1⟩ := iDual_bound_e3_hasU2 hm (hasU2_airySeedU2 1 0 0)
  obtain ⟨C₂, hC₂, h2⟩ := iDual_bound_e3_hasU2 hm (hasU2_airySeedU2 0 1 0)
  obtain ⟨C₃, hC₃, h3⟩ := iDual_bound_e3_hasU2 hm (hasU2_airySeedU2 0 0 1)
  refine ⟨(R + 1) * (C₁ + C₂ + C₃), by positivity, fun {a b c₀} ha hb hcR {δ₀ c ξ} hδ hc2 hξ hS => ?_⟩
  have hc0 : 0 < c := by linarith
  set B : ℝ := ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) with hBdef
  have e1 : ‖iDual (airySeedU2 1 0 0) δ₀ m c ξ‖ ≤ C₁ * B :=
    (h1 hδ hc2 hξ hS).trans_eq (by rw [hBdef]; ring)
  have e2 : ‖iDual (airySeedU2 0 1 0) δ₀ m c ξ‖ ≤ C₂ * B :=
    (h2 hδ hc2 hξ hS).trans_eq (by rw [hBdef]; ring)
  have e3 : ‖iDual (airySeedU2 0 0 1) δ₀ m c ξ‖ ≤ C₃ * B :=
    (h3 hδ hc2 hξ hS).trans_eq (by rw [hBdef]; ring)
  have hB0 : 0 ≤ B := by
    have h := (norm_nonneg _).trans e1
    nlinarith
  rw [iDual_airySeed_lin a b c₀ hδ.1.le m hc0 hξ]
  have n1 : ‖(a : ℂ) * iDual (airySeedU2 1 0 0) δ₀ m c ξ‖ ≤ R * (C₁ * B) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul ha e1 (norm_nonneg _) hR
  have n2 : ‖(b : ℂ) * iDual (airySeedU2 0 1 0) δ₀ m c ξ‖ ≤ R * (C₂ * B) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hb e2 (norm_nonneg _) hR
  have n3 : ‖(c₀ : ℂ) * iDual (airySeedU2 0 0 1) δ₀ m c ξ‖ ≤ R * (C₃ * B) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hcR e3 (norm_nonneg _) hR
  have hSB : 0 ≤ (C₁ + C₂ + C₃) * B := mul_nonneg (by linarith) hB0
  have hfin : (R + 1) * (C₁ + C₂ + C₃) * B = (R + 1) * (C₁ + C₂ + C₃) * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    rw [hBdef]; ring
  rw [← hfin]
  calc _ ≤ _ := norm_add₃_le
    _ ≤ R * (C₁ * B) + R * (C₂ * B) + R * (C₃ * B) := by linarith
    _ ≤ (R + 1) * (C₁ + C₂ + C₃) * B := by nlinarith

/-- `(e5)`-type bound for the main symbol: the `U.2` right-half-plane bound of `liftSymbol (airySeedU2 a b c₀)`, uniform over
`|a|, |b|, |c₀| ≤ R`, from linearity in the seed and the three basis seeds. -/
lemma liftSymbol_airySeedU2_unif (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    ∃ C > 0, ∀ {a b c₀ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → ∀ {δ₀ : ℝ} {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re →
      ‖liftSymbol (airySeedU2 a b c₀) δ₀ m w‖ ≤ C * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, h1⟩ := hasU2_norm_liftSymbol_le_unif (hasU2_airySeedU2 1 0 0)
  obtain ⟨C₂, hC₂, h2⟩ := hasU2_norm_liftSymbol_le_unif (hasU2_airySeedU2 0 1 0)
  obtain ⟨C₃, hC₃, h3⟩ := hasU2_norm_liftSymbol_le_unif (hasU2_airySeedU2 0 0 1)
  refine ⟨(R + 1) * (C₁ + C₂ + C₃), by positivity, fun {a b c₀} ha hb hcR {δ₀ w} hδ hw => ?_⟩
  have hT : 0 ≤ (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by positivity
  rw [liftSymbol_airySeedU2_lin a b c₀ δ₀ m hw]
  have n1 : ‖(a : ℂ) * liftSymbol (airySeedU2 1 0 0) δ₀ m w‖ ≤ R * (C₁ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul ha (h1 m hδ hw) (norm_nonneg _) hR
  have n2 : ‖(b : ℂ) * liftSymbol (airySeedU2 0 1 0) δ₀ m w‖ ≤ R * (C₂ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hb (h2 m hδ hw) (norm_nonneg _) hR
  have n3 : ‖(c₀ : ℂ) * liftSymbol (airySeedU2 0 0 1) δ₀ m w‖ ≤ R * (C₃ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hcR (h3 m hδ hw) (norm_nonneg _) hR
  have hST : 0 ≤ (C₁ + C₂ + C₃) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := mul_nonneg (by linarith) hT
  calc _ ≤ _ := norm_add₃_le
    _ ≤ R * (C₁ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) + R * (C₂ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) +
          R * (C₃ * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by linarith
    _ ≤ (R + 1) * (C₁ + C₂ + C₃) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by nlinarith

/-- The dual `U.2` bound `‖D̃(c_s w)‖ ≤ C ‖1 + w‖^{-5/2}` of `airySeedU2 a b c₀`, uniform over `|a|, |b|, |c₀| ≤ R`. -/
lemma airyTwistedLaplaceC_airySeedU2_unif (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {a b c₀ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (airySeedU2 a b c₀) ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, h1⟩ := (hasU2_airySeedU2 1 0 0).rhp
  obtain ⟨C₂, hC₂, h2⟩ := (hasU2_airySeedU2 0 1 0).rhp
  obtain ⟨C₃, hC₃, h3⟩ := (hasU2_airySeedU2 0 0 1).rhp
  refine ⟨(R + 1) * (C₁ + C₂ + C₃), by positivity, fun {a b c₀} ha hb hcR {w} hw => ?_⟩
  have hy : 0 ≤ ((ceCs : ℂ) * w).re := by simp only [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le hw
  have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by positivity
  rw [airyTwistedLaplaceC_airySeedU2_lin a b c₀ hy]
  have n1 : ‖(a : ℂ) * airyTwistedLaplaceC (airySeedU2 1 0 0) ((ceCs : ℂ) * w)‖ ≤
      R * (C₁ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul ha (h1 w hw) (norm_nonneg _) hR
  have n2 : ‖(b : ℂ) * airyTwistedLaplaceC (airySeedU2 0 1 0) ((ceCs : ℂ) * w)‖ ≤
      R * (C₂ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hb (h2 w hw) (norm_nonneg _) hR
  have n3 : ‖(c₀ : ℂ) * airyTwistedLaplaceC (airySeedU2 0 0 1) ((ceCs : ℂ) * w)‖ ≤
      R * (C₃ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hcR (h3 w hw) (norm_nonneg _) hR
  have hST : 0 ≤ (C₁ + C₂ + C₃) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := mul_nonneg (by linarith) hT
  calc _ ≤ _ := norm_add₃_le
    _ ≤ R * (C₁ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) + R * (C₂ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) +
          R * (C₃ * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by linarith
    _ ≤ (R + 1) * (C₁ + C₂ + C₃) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by nlinarith

/-- The one-level seed is continuous. -/
lemma continuous_airySeedU2 (a b c₀ : ℝ) : Continuous (airySeedU2 a b c₀) :=
  ((continuous_const.mul continuous_ceF1).add (continuous_const.mul (continuous_ceG1 _))).add
    (continuous_const.mul (continuous_ceG1Deriv _))

/-- **`(e5)`, uniform over the seed coefficients.**  For `m ≥ 1`, `S_w` and `R ≥ 0`, there is `C > 0` such that for all
`|a|, |b|, |c₀| ≤ R` and `σ = ±1`, with the dual seed `σ · (the same seed)`, the window translation holds for `δ₀ ≥ 0`,
`c ≥ 32768`, `ξ > 0`, `|S_eff(ξ)| ≤ S_w`.  The dual term is `σ I_dual[a, b, c₀]` by `iDual_airySeed_lin`.  The threshold `c ≥ 32768`
and the other restrictions are those of `window_translation`. -/
theorem window_translation_airySeed {m : ℕ} (hm : 1 ≤ m) (Sw R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b c₀ σ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → (σ = 1 ∨ σ = -1) →
      ∀ {δ₀ c ξ : ℝ}, 0 ≤ δ₀ → 32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain (airySeedU2 a b c₀) δ₀ m c ξ + (σ : ℂ) * iDual (airySeedU2 a b c₀) δ₀ m c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth δ₀ m (airySeedU2 a b c₀) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨CW, hCW, hW⟩ := liftSymbol_airySeedU2_unif R hR m
  obtain ⟨CD, hCD, hD⟩ := airyTwistedLaplaceC_airySeedU2_unif R hR
  obtain ⟨C, hC, h⟩ := window_translation m hm Sw CW CD hCW hCD
  refine ⟨C, hC, fun {a b c₀ σ} ha hb hcR hσ {δ₀ c ξ} hδ hcc hξ hS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hσa : |σ * a| ≤ R := by rcases hσ with rfl | rfl <;> simpa [abs_neg] using ha
  have hσb : |σ * b| ≤ R := by rcases hσ with rfl | rfl <;> simpa [abs_neg] using hb
  have hσc : |σ * c₀| ≤ R := by rcases hσ with rfl | rfl <;> simpa [abs_neg] using hcR
  have hD' := h (X := airySeedU2 a b c₀) (D := airySeedU2 (σ * a) (σ * b) (σ * c₀))
    (hasU2_airySeedU2 a b c₀) (continuous_airySeedU2 a b c₀)
    (fun {δ₀'} {w} h0 h1 => hW ha hb hcR h0 h1) (fun {w} hw => hD hσa hσb hσc hw) hδ hcc hξ hS
  have hid : iDual (airySeedU2 (σ * a) (σ * b) (σ * c₀)) δ₀ m c ξ = (σ : ℂ) * iDual (airySeedU2 a b c₀) δ₀ m c ξ := by
    rw [iDual_airySeed_lin (σ * a) (σ * b) (σ * c₀) hδ m hc0 hξ, iDual_airySeed_lin a b c₀ hδ m hc0 hξ]
    push_cast
    ring
  rw [hid] at hD'
  exact hD'

/-- info: 'FormalResearch.SignUncertainty.iDual_airySeed_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms iDual_airySeed_lin
/-- info: 'FormalResearch.SignUncertainty.iDual_bound_e3_airySeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms iDual_bound_e3_airySeed
/-- info: 'FormalResearch.SignUncertainty.liftSymbol_airySeedU2_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftSymbol_airySeedU2_unif
/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplaceC_airySeedU2_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airyTwistedLaplaceC_airySeedU2_unif
/-- info: 'FormalResearch.SignUncertainty.continuous_airySeedU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms continuous_airySeedU2
/-- info: 'FormalResearch.SignUncertainty.window_translation_airySeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window_translation_airySeed

end FormalResearch.SignUncertainty

module

public import FormalResearch.CohnElkies.CancelledSymbolAndLaplace

/-!
# `U.2` for the one-level Airy seed family `a f₁ + b g₁ + c g₁'`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `U.2` (`u1c:U2`), used in Theorem `O.9'`
(`u1co:O9p`) at `m₀ = 1`. At `m₀ = 1` the Hermite–Biehler seed of `lem:hb-seed-mass` is
`F_δ = -f₁ - γ₁ δ g₁ + γ₂ δ (g₁ + g₁' - f₁) + r_δ g₁`, a combination of the three Airy squares
`f₁ = ceF1`, `g₁ = ceG1 (airyZero 1)`, `g₁' = ceG1Deriv airyDerivFirstZero`.

`HasU2 X` packages the right-half-plane `‖1 + w‖^{-5/2}` bound of the twisted Laplace transform
together with the integrability and holomorphy it needs. It holds for `f₁`, `g₁`, `g₁'` and is closed
under linear combinations, so the right-half-plane bound and the uniform vertical-line Cauchy
derivative bounds hold for every seed `a f₁ + b g₁ + c g₁'` (all `j : ℕ`, `c ≥ 2`).
Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-- The `U.2` package for a seed `X`: integrability of `X e^{yu}` on `Re y ≥ 0`, holomorphy of its
twisted Laplace transform on `Re y > 0` and the right-half-plane bound `C ‖1 + w‖^{-5/2}` of
`X̃(i c_s w)` on `Re w ≥ 0`. -/
structure HasU2 (X : ℝ → ℝ) : Prop where
  integrable : ∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ)))
  differentiable : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re}
  rhp : ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))

theorem HasU2.smul {X : ℝ → ℝ} (h : HasU2 X) (b : ℝ) : HasU2 (fun u => b * X u) where
  integrable y hy := integrable_const_mul_ofReal (h.integrable y hy)
  differentiable := (h.differentiable.const_mul (b : ℂ)).congr fun y hy => by
    rw [airyTwistedLaplaceC_const_mul]
  rhp := by
    obtain ⟨C, hC, hb⟩ := h.rhp
    refine ⟨|b| * C + 1, by positivity, fun w hw => ?_⟩
    rw [airyTwistedLaplaceC_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    calc |b| * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ |b| * (C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hb w hw) (abs_nonneg b)
      _ ≤ (|b| * C + 1) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by nlinarith

theorem HasU2.add {X Y : ℝ → ℝ} (hX : HasU2 X) (hY : HasU2 Y) : HasU2 (fun u => X u + Y u) where
  integrable y hy := ((hX.integrable y hy).add (hY.integrable y hy)).congr
    (ae_of_all _ fun u => by simp only [Pi.add_apply]; push_cast; ring)
  differentiable := (hX.differentiable.add hY.differentiable).congr fun y hy => by
    rw [airyTwistedLaplaceC_add (hX.integrable y (le_of_lt hy)) (hY.integrable y (le_of_lt hy))]; rfl
  rhp := by
    obtain ⟨C₁, hC₁, h₁⟩ := hX.rhp
    obtain ⟨C₂, hC₂, h₂⟩ := hY.rhp
    refine ⟨C₁ + C₂, by positivity, fun w hw => ?_⟩
    have hy : 0 ≤ ((ceCs : ℂ) * w).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hw]
    rw [airyTwistedLaplaceC_add (hX.integrable _ hy) (hY.integrable _ hy)]
    calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + airyTwistedLaplaceC Y ((ceCs : ℂ) * w)‖
        ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ + ‖airyTwistedLaplaceC Y ((ceCs : ℂ) * w)‖ :=
          norm_add_le _ _
      _ ≤ C₁ * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) + C₂ * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := add_le_add (h₁ w hw) (h₂ w hw)
      _ = (C₁ + C₂) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring

/-- `U.2` for `f₁`. -/
theorem hasU2_ceF1 : HasU2 ceF1 where
  integrable := ceF1_regularity.1
  differentiable := ceF1_regularity.2.2.1
  rhp := airyTwistedLaplaceC_ceF1_rhp

/-- `U.2` for `g₁` (the `y^{-9/2}` expansion of `ceG1` is stronger than needed). -/
theorem hasU2_ceG1 : HasU2 (ceG1 (airyZero 1)) := by
  obtain ⟨C1, hC1, hG1_t⟩ := ceG1_tail_exp_rpow32
  have hreg := airyTwistedLaplaceC_regularity (continuous_ceG1 _) ceG1_integrable hC1 hG1_t
  obtain ⟨CG, hCG, hbd⟩ := airyTwistedLaplaceC_ceG1_bound
  obtain ⟨_, hC_lo, hlo⟩ := hreg.2.2.2
  refine ⟨hreg.1, hreg.2.2.1, ?_⟩
  obtain ⟨C, hC, hpos⟩ := rhp_bound_of_unit_and_tail (F := airyTwistedLaplaceC (ceG1 (airyZero 1)))
    (by norm_num : (0 : ℝ) ≤ 5 / 2) hC_lo (fun y hy => hlo hy.le)
    (C_hi := CG) (fun y hy hy1 => by
      refine (hbd hy hy1).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)) hCG.le)
  exact ⟨C, hC, rhp_extend_to_boundary hreg.2.1 hpos⟩

/-- `U.2` for `g₁'`. -/
theorem hasU2_ceG1Deriv : HasU2 (ceG1Deriv airyDerivFirstZero) := by
  obtain ⟨C1, hC1, hG_t⟩ := ceG1Deriv_tail_exp_rpow32
  have hreg := airyTwistedLaplaceC_regularity (continuous_ceG1Deriv _) ceG1Deriv_integral_eq_M.1 hC1 hG_t
  obtain ⟨CG, hCG, hasy⟩ := airyTwistedLaplaceC_ceG1Deriv_asymp
  obtain ⟨_, hC_lo, hlo⟩ := hreg.2.2.2
  refine ⟨hreg.1, hreg.2.2.1, ?_⟩
  exact rhp_bound_52_of_asymp hreg.2.1 hC_lo hlo fun {y} hy hy1 => norm_le_add_norm_sub_52 hy hy1 (hasy hy hy1)

/-- The one-level Airy seed family `a f₁ + b g₁ + c g₁'`. -/
noncomputable def airySeedU2 (a b c : ℝ) (u : ℝ) : ℝ :=
  a * ceF1 u + b * ceG1 (airyZero 1) u + c * ceG1Deriv airyDerivFirstZero u

theorem hasU2_airySeedU2 (a b c : ℝ) : HasU2 (airySeedU2 a b c) :=
  ((hasU2_ceF1.smul a).add (hasU2_ceG1.smul b)).add (hasU2_ceG1Deriv.smul c)

/-- **Lemma `U.2` (`u1c:U2`) for the one-level seeds**: right-half-plane bound. -/
theorem airySeedU2_rhp (a b c : ℝ) :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (airySeedU2 a b c) ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
  (hasU2_airySeedU2 a b c).rhp

/-- **Lemma `U.2` (`u1c:U2`) for the one-level seeds**: uniform vertical-line Cauchy derivative
bounds `|∂_τ^j [X̃(i c_s c^{1/3} (1 - iτ))]| ≤ C_j c^{-5/6} (1 + τ²)^{-5/4}` for all `j`, `c ≥ 2`. -/
theorem airySeedU2_dual_deriv_bound (a b c₀ : ℝ) :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (airySeedU2 a b c₀)
        (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖
        ≤ C_j * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) :=
  dual_deriv_bound_52 (hasU2_airySeedU2 a b c₀).differentiable (hasU2_airySeedU2 a b c₀).rhp

/-- The Hermite–Biehler seed of `lem:hb-seed-mass` at `m₀ = 1`,
`F_δ = -f₁ - γ₁ δ g₁ + γ₂ δ S_b + r g₁` with `b = 1`, is `airySeedU2 (-1 - γ₂ δ) (-γ₁ δ + γ₂ δ + r) (γ₂ δ)`
(`S_1 = g₁ + g₁' - f₁`). -/
theorem hbSeed_m1_eq_airySeedU2 (γ₁ γ₂ δ r : ℝ) :
    (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u)
      = airySeedU2 (-1 - γ₂ * δ) (-γ₁ * δ + γ₂ * δ + r) (γ₂ * δ) := by
  funext u; unfold airySeedU2 ceSb; ring

/-- **`U.2` for the `m₀ = 1` Hermite–Biehler seed**: all `δ`-dependent coefficients are covered. -/
theorem hbSeed_m1_hasU2 (γ₁ γ₂ δ r : ℝ) :
    HasU2 (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u) := by
  rw [hbSeed_m1_eq_airySeedU2]; exact hasU2_airySeedU2 _ _ _

/-- info: 'FormalResearch.CohnElkies.hbSeed_m1_hasU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hbSeed_m1_hasU2

/-- info: 'FormalResearch.CohnElkies.airySeedU2_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms airySeedU2_dual_deriv_bound

end FormalResearch.CohnElkies

module

public import FormalResearch.SignUncertainty.StripAdmissTail
public import FormalResearch.SignUncertainty.StripAdmissOrigin

/-!
# `uct:admiss` (Lemma T.8): general Mellin-strip admissibility via `C²` edge traces

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.8 (`uct:admiss`), parts (1) and (2).

Statement formalised.  Fix `c ≥ 2`, `α ∈ (0,1)` and `W̃ : ℂ → ℂ` (only its values on `0 ≤ Re ζ ≤ 1` matter) satisfying `StripAdmissData α W`:
(M1) holomorphic on the open strip, continuous on the closed strip, real-symmetric, `|W̃(σ+iτ)| ≤ C (1+|τ|)^{-2}`; (M2) the endpoint Hölder bound at `ζ = 1`;
(M3) for the edge trace `g_0(τ) = W̃(iτ)`: `C²` off `0`, `|∂^j (g_0 - g_0(0))| ≤ C |τ|^{α-j}` on `0 < |τ| ≤ 1` and `|∂^j g_0| ≤ C (1+|τ|)^{-2}` on `|τ| ≥ 1/2`.
Let `f = f_W = admissLift c W` (the lift `(uct:mellin-inv-gen)`, `x₀ = c/2`).  `uct_admiss` states

* (1) the lift does not depend on the line `x₀ ∈ (0,c)`, is real, and `admissF c W` (= `f_W` on `(0,∞)`, `W̃(1)` at `0`) is continuous on `[0,∞)`;
* (2) the vertical representation `(f ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ+iτ,ξ) W̃(σ+iτ) dτ` (`0 ≤ σ < 1`), the tail `|(f ρ₀)(cξ)| ≤ C' ξ⁻¹ L^{-1-α}` (`ξ = e^L/π²`, `L ≥ 4`), `f ∈ L¹(ρ₀)`,
  and the radial decay `|f(r²/2)| ≤ C'' (1+r)^{-2c} (log(2+r))^{-1-α}` (for `d = 2c ∈ ℕ` this is the decay of the radial function `x ↦ f(|x|²/2)` on `ℝ^d`).

Not formalised: part (3) (reflection / Hankel transform of `f`), which needs `W̃(1-·)` satisfying (M3) at the edge `ζ = 1` and the Hankel transform of a general lift; the hypothesis (M2) at `ζ = 0`
and (M3) at the edge `ζ = 1` are only used there (the formalised theorem has weaker hypotheses than the paper's statement).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The hypotheses (M1), (M2) at `1`, (M3) at the edge `Re ζ = 0` of `uct:admiss` (`0 < α < 1` is a separate hypothesis). -/
structure StripAdmissData (α : ℝ) (W : ℂ → ℂ) : Prop extends StripM1 W where
  holder1 : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α
  edge0 : StripEdge0 α W

/-- The lift with its origin value `f_W(0) = W̃(1)`. -/
noncomputable def admissF (c : ℝ) (W : ℂ → ℂ) (Δ : ℝ) : ℝ :=
  if Δ = 0 then (W 1).re else admissLift c W Δ

/-! ### `Δ⁻¹ (log kΔ)^{-p}` is integrable at infinity for `p > 1` -/

theorem integrableOn_inv_log_rpow_of_one_lt {k Δ₁ p : ℝ} (hp : 1 < p) (hk : 0 < k) (hΔ₁ : 0 < Δ₁)
    (hL : 0 < Real.log (k * Δ₁)) :
    IntegrableOn (fun Δ : ℝ => Δ⁻¹ * Real.log (k * Δ) ^ (-p)) (Ioi Δ₁) := by
  set g : ℝ → ℝ := fun Δ => -(1 / (p - 1)) * Real.log (k * Δ) ^ (1 - p) with hg
  have hpos : ∀ Δ : ℝ, Δ₁ ≤ Δ → 0 < Real.log (k * Δ) := fun Δ hΔ =>
    lt_of_lt_of_le hL (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hΔ hk.le))
  have hp1 : p - 1 ≠ 0 := by linarith
  have hder : ∀ Δ ∈ Ioi Δ₁, HasDerivAt g (Δ⁻¹ * Real.log (k * Δ) ^ (-p)) Δ := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := lt_trans hΔ₁ hΔ
    have hlp := hpos Δ (le_of_lt hΔ)
    have h1 : HasDerivAt (fun x : ℝ => Real.log (k * x)) Δ⁻¹ Δ := by
      have := ((hasDerivAt_id Δ).const_mul k).log (by simp only [id_eq]; exact (mul_pos hk hΔ0).ne')
      convert this using 1
      · rfl
      · show Δ⁻¹ = k * 1 / (k * Δ)
        field_simp
    have h2 := (h1.rpow_const (p := 1 - p) (Or.inl hlp.ne')).const_mul (-(1 / (p - 1)))
    convert h2 using 1
    rw [show 1 - p - 1 = -p by ring]
    field_simp
    ring
  refine integrableOn_Ioi_deriv_of_nonneg (g := g) (l := 0) ?_ hder (fun Δ hΔ => ?_) ?_
  · refine ContinuousAt.continuousWithinAt ?_
    have hΔ0 : 0 < Δ₁ := hΔ₁
    refine (continuousAt_const.mul ?_)
    refine ContinuousAt.rpow_const (ContinuousAt.log (by fun_prop) (by positivity)) (Or.inl hL.ne')
  · have := hpos Δ (le_of_lt hΔ)
    have hΔ0 : 0 < Δ := lt_trans hΔ₁ hΔ
    positivity
  · have h1 : Tendsto (fun Δ : ℝ => Real.log (k * Δ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop hk)
    have h2 := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < p - 1)).comp h1
    have := h2.const_mul (-(1 / (p - 1)))
    rw [mul_zero] at this
    refine this.congr fun Δ => ?_
    simp only [Function.comp, hg]
    rw [show -(p - 1) = 1 - p by ring]

/-- Finite mass from a power bound at `0` and the log-tail bound `Δ⁻¹ (log kΔ)^{-p}`, `p > 1`, at `∞`
(the exponent-`p` version of `integrableOn_mass_of_bounds`). -/
theorem integrableOn_mass_of_bounds_p {f : ℝ → ℝ} {c p : ℝ} (hc : 0 < c) (hp : 1 < p) (hcont : ContinuousOn f (Ioi 0))
    {C₀ : ℝ} (hC₀ : ∀ Δ : ℝ, 0 < Δ → |f Δ| ≤ C₀ * Δ ^ (-(c / 2))) {Δ₁ k C : ℝ} (hΔ₁ : 0 < Δ₁) (hk : 0 < k)
    (hL : 0 < Real.log (k * Δ₁))
    (htail : ∀ Δ : ℝ, Δ₁ ≤ Δ → |f Δ * hankelRho0 c Δ| ≤ C * (Δ⁻¹ * Real.log (k * Δ) ^ (-p))) :
    IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0) := by
  have hmeas : ContinuousOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0) :=
    hcont.mul (continuousOn_hankelRho0 c)
  rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hΔ₁)]
  refine IntegrableOn.union ?_ ?_
  · set a : ℝ := (2 * Real.pi) ^ c / Real.Gamma c with ha
    have hint : IntegrableOn (fun Δ : ℝ => |C₀| * a * Δ ^ (c / 2 - 1)) (Ioc 0 Δ₁) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ₁.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul (|C₀| * a)
    refine Integrable.mono' hint (hmeas.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    have hΔ0 : 0 < Δ := hΔ.1
    rw [Real.norm_eq_abs, abs_mul]
    have hρ : |hankelRho0 c Δ| = a * Δ ^ (c - 1) := by
      rw [abs_of_nonneg (hankelRho0_nonneg hc hΔ0.le)]; rfl
    rw [hρ]
    have hGa : 0 ≤ a := by rw [ha]; have := Real.Gamma_pos_of_pos hc; positivity
    calc |f Δ| * (a * Δ ^ (c - 1)) ≤ (C₀ * Δ ^ (-(c / 2))) * (a * Δ ^ (c - 1)) := by
          gcongr
          exact hC₀ Δ hΔ0
      _ ≤ |C₀| * Δ ^ (-(c / 2)) * (a * Δ ^ (c - 1)) := by
          gcongr
          exact le_abs_self _
      _ = |C₀| * a * Δ ^ (c / 2 - 1) := by
          have : Δ ^ (-(c / 2)) * Δ ^ (c - 1) = Δ ^ (c / 2 - 1) := by
            rw [← Real.rpow_add hΔ0]; congr 1; ring
          calc |C₀| * Δ ^ (-(c / 2)) * (a * Δ ^ (c - 1)) = |C₀| * a * (Δ ^ (-(c / 2)) * Δ ^ (c - 1)) := by ring
            _ = _ := by rw [this]
  · have hint := (integrableOn_inv_log_rpow_of_one_lt hp hk hΔ₁ hL).const_mul C
    refine Integrable.mono' hint (hmeas.mono (fun x hx => lt_of_lt_of_le hΔ₁ (le_of_lt hx)) |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
    rw [Real.norm_eq_abs]
    exact htail Δ (le_of_lt hΔ)

/-- The tail bound `(uct:gen-tail)` in the variable `Δ = cξ`: for `Δ ≥ Δ₁ = c e⁴/π²`,
`|f(Δ) ρ₀(Δ)| ≤ C c Δ⁻¹ (log(π²Δ/c))^{-1-α}`. -/
theorem admiss_tail_Delta {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hE : StripEdge0 α W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : ℝ, c * (Real.exp 4 / Real.pi ^ 2) ≤ Δ →
      |admissLift c W Δ * hankelRho0 c Δ| ≤ C * (Δ⁻¹ * Real.log (Real.pi ^ 2 / c * Δ) ^ (-(1 + α))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC0, hC⟩ := admiss_tail hc hα0 hα1 hW hE
  refine ⟨C * c, by positivity, fun Δ hΔ => ?_⟩
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  set L : ℝ := Real.log (Real.pi ^ 2 / c * Δ) with hLdef
  have hpos : 0 < Real.pi ^ 2 / c * Δ := by positivity
  have hL4 : 4 ≤ L := by
    rw [hLdef, ← Real.log_exp 4]
    refine Real.log_le_log (Real.exp_pos _) ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    have : c * (Real.exp 4 / Real.pi ^ 2) * Real.pi ^ 2 = c * Real.exp 4 := by field_simp
    nlinarith
  have hexp : Real.exp L = Real.pi ^ 2 / c * Δ := by rw [hLdef, Real.exp_log hpos]
  have hξ : Real.exp L / Real.pi ^ 2 = Δ / c := by rw [hexp]; field_simp
  have h := hC L hL4
  rw [hξ, show c * (Δ / c) = Δ by field_simp] at h
  rw [mul_comm (admissLift c W Δ)]
  refine h.trans (le_of_eq ?_)
  rw [inv_div]
  field_simp

/-- **`uct:admiss` (2): `f ∈ L¹((0,∞), ρ₀ dΔ)`.** -/
theorem admiss_integrable {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hE : StripEdge0 α W) :
    IntegrableOn (fun Δ : ℝ => admissLift c W Δ * hankelRho0 c Δ) (Ioi 0) := by
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData (by linarith : (1 : ℝ) ≤ c) hW
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_liftFun_le hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨C, hC0, htail⟩ := admiss_tail_Delta hc hα0 hα1 hW hE
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have hΔ₁ : 0 < c * (Real.exp 4 / Real.pi ^ 2) := by positivity
  have hk : 0 < Real.pi ^ 2 / c := by positivity
  have hL : 0 < Real.log (Real.pi ^ 2 / c * (c * (Real.exp 4 / Real.pi ^ 2))) := by
    have : Real.pi ^ 2 / c * (c * (Real.exp 4 / Real.pi ^ 2)) = Real.exp 4 := by field_simp
    rw [this, Real.log_exp]; norm_num
  exact integrableOn_mass_of_bounds_p hc0 (by linarith : 1 < 1 + α) (continuousOn_liftFun hΦ (x₀ := c / 2) (by linarith) (by linarith))
    hC₀ hΔ₁ hk hL htail

/-! ### Radial decay -/

lemma rpow_half_sq_le {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) :
    (r ^ 2 / 2) ^ (-c) ≤ 2 ^ c * 2 ^ (2 * c) * (1 + r) ^ (-(2 * c)) := by
  have hr0 : 0 < r := by linarith
  have e1 : (r ^ 2 / 2) ^ (-c) = 2 ^ c * r ^ (-(2 * c)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    push_cast
    rw [show (2 : ℝ) * -c = -(2 * c) by ring]
    field_simp
  have h2 : (2 * r) ^ (-(2 * c)) ≤ (1 + r) ^ (-(2 * c)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have e2 : (2 * r) ^ (-(2 * c)) = 2 ^ (-(2 * c)) * r ^ (-(2 * c)) := Real.mul_rpow (by norm_num) hr0.le
  have e3 : (2 : ℝ) ^ (2 * c) * 2 ^ (-(2 * c)) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
  have : r ^ (-(2 * c)) ≤ 2 ^ (2 * c) * (1 + r) ^ (-(2 * c)) := by
    calc r ^ (-(2 * c)) = (2 ^ (2 * c) * 2 ^ (-(2 * c))) * r ^ (-(2 * c)) := by rw [e3, one_mul]
      _ = 2 ^ (2 * c) * (2 ^ (-(2 * c)) * r ^ (-(2 * c))) := by ring
      _ ≤ _ := by rw [← e2]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [e1]
  calc 2 ^ c * r ^ (-(2 * c)) ≤ 2 ^ c * (2 ^ (2 * c) * (1 + r) ^ (-(2 * c))) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem admiss_radial_large {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hE : StripEdge0 α W) :
    ∃ C r₁ : ℝ, 0 ≤ C ∧ 1 ≤ r₁ ∧ ∀ r : ℝ, r₁ ≤ r →
      |admissLift c W (r ^ 2 / 2)| ≤ C * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC0, htail⟩ := admiss_tail_Delta hc hα0 hα1 hW hE
  have hπ : 0 < Real.pi ^ 2 := by positivity
  set Δ₁ : ℝ := c * (Real.exp 4 / Real.pi ^ 2) with hΔ₁
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc0
  set a : ℝ := (2 * Real.pi) ^ c / Real.Gamma c with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  refine ⟨C / a * (2 ^ c * 2 ^ (2 * c)), max (max 1 (6 * c / Real.pi ^ 2)) (2 * Δ₁), by positivity,
    (le_max_left _ _).trans' (le_max_left _ _), fun r hr => ?_⟩
  have hr1' : 1 ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr6 : 6 * c / Real.pi ^ 2 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr2 : 2 * Δ₁ ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := by linarith
  set Δ : ℝ := r ^ 2 / 2 with hΔ
  have hΔ0 : 0 < Δ := by positivity
  have hΔge : Δ₁ ≤ Δ := by
    have : r ≤ r ^ 2 := by nlinarith
    rw [hΔ]; linarith
  have ht := htail Δ hΔge
  have hρ : hankelRho0 c Δ = a * Δ ^ (c - 1) := rfl
  have hρpos : 0 < hankelRho0 c Δ := by rw [hρ]; positivity
  -- `L ≥ log (2 + r)`
  set L : ℝ := Real.log (Real.pi ^ 2 / c * Δ) with hL
  have h2r : 2 + r ≤ Real.pi ^ 2 / c * Δ := by
    have h6 : 6 * c ≤ r * Real.pi ^ 2 := by rwa [div_le_iff₀ hπ] at hr6
    have : Real.pi ^ 2 / c * Δ = Real.pi ^ 2 * r ^ 2 / (2 * c) := by rw [hΔ]; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith
  have hlog2 : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hLge : Real.log (2 + r) ≤ L := Real.log_le_log (by positivity) h2r
  have hLp : L ^ (-(1 + α)) ≤ Real.log (2 + r) ^ (-(1 + α)) :=
    Real.rpow_le_rpow_of_nonpos hlog2 hLge (by linarith)
  -- `|f(Δ)| ≤ (C/a) Δ^{-c} L^{-(1+α)}`
  have hf : |admissLift c W Δ| ≤ C / a * (Δ ^ (-c) * L ^ (-(1 + α))) := by
    have h1 : |admissLift c W Δ| * (a * Δ ^ (c - 1)) ≤ C * (Δ⁻¹ * L ^ (-(1 + α))) := by
      rw [← hρ, ← abs_of_pos hρpos, ← abs_mul]; exact ht
    have hq : 0 < a * Δ ^ (c - 1) := by positivity
    have h2 : |admissLift c W Δ| ≤ C * (Δ⁻¹ * L ^ (-(1 + α))) / (a * Δ ^ (c - 1)) := (le_div_iff₀ hq).mpr h1
    refine h2.trans (le_of_eq ?_)
    have : Δ ^ (-c) = Δ⁻¹ / Δ ^ (c - 1) := by
      rw [show -c = -1 - (c - 1) by ring, Real.rpow_sub hΔ0, Real.rpow_neg_one]
    rw [this]
    field_simp
  have hq := rpow_half_sq_le (c := c) hc0 hr1'
  have hlogp : 0 ≤ Real.log (2 + r) ^ (-(1 + α)) := by positivity
  have hLp0 : 0 ≤ L ^ (-(1 + α)) := Real.rpow_nonneg (by linarith [hLge, hlog2]) _
  calc |admissLift c W Δ| ≤ C / a * (Δ ^ (-c) * L ^ (-(1 + α))) := hf
    _ ≤ C / a * ((2 ^ c * 2 ^ (2 * c) * (1 + r) ^ (-(2 * c))) * Real.log (2 + r) ^ (-(1 + α))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hq hLp (Real.rpow_nonneg (by linarith [hLge, hlog2]) _) (by positivity)) (by positivity)
    _ = _ := by ring

lemma W_one_im {W : ℂ → ℂ} (hW : StripM1 W) : (W 1).im = 0 := by
  have := W_one_conj hW
  have h2 := congrArg Complex.im this
  simp only [Complex.conj_im] at h2
  linarith

/-- **`uct:admiss` (1), continuity:** `f_W` extends continuously to `[0, ∞)` with `f_W(0) = W̃(1)`. -/
theorem admissF_continuousOn {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripAdmissData α W) :
    ContinuousOn (admissF c W) (Ici 0) := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hΦ := admissPhi_mellinLiftData hc1 hW.toStripM1
  have hcont : ContinuousOn (admissLift c W) (Ioi 0) :=
    continuousOn_liftFun hΦ (x₀ := c / 2) (by linarith) (by linarith)
  have hev : ∀ Δ : ℝ, 0 < Δ → admissF c W =ᶠ[𝓝 Δ] admissLift c W := fun Δ hΔ => by
    filter_upwards [Ioi_mem_nhds hΔ] with x hx
    simp [admissF, (ne_of_gt hx)]
  intro Δ hΔ
  rcases (mem_Ici.mp hΔ).eq_or_lt with h0 | hpos
  · subst h0
    refine continuousWithinAt_Ioi_iff_Ici.mp ?_
    have hlim := admiss_lift_tendsto hc hα0 hα1 hW.toStripM1 hW.holder1
    have h0 : admissF c W 0 = (W 1).re := by simp [admissF]
    unfold ContinuousWithinAt
    rw [h0]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [admissF, ne_of_gt (show 0 < x from hx)]
  · exact ((hcont.continuousAt (Ioi_mem_nhds hpos)).congr (hev Δ hpos).symm).continuousWithinAt

/-- **`uct:admiss` (2), radial decay:** `|f_W(r²/2)| ≤ C'' (1+r)^{-2c} (log(2+r))^{-1-α}` for `r ≥ 0`
(for `d = 2c ∈ ℕ` this is the decay bound of the radial function `x ↦ f(|x|²/2)` on `ℝ^d`; for `α = 1/2` the logarithmic decay `(log(2+|x|))^{-3/2}`). -/
theorem admiss_radial_decay {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripAdmissData α W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      |admissF c W (r ^ 2 / 2)| ≤ C * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C₁, r₁, hC₁, hr₁, hlarge⟩ := admiss_radial_large hc hα0 hα1 hW.toStripM1 hW.edge0
  have hFc := admissF_continuousOn hc hα0 hα1 hW
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := r₁ ^ 2 / 2)).exists_bound_of_continuousOn
    (hFc.mono Icc_subset_Ici_self)
  set K : ℝ := (1 + r₁) ^ (2 * c) * Real.log (2 + r₁) ^ (1 + α) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < Real.log (2 + r₁) := Real.log_pos (by linarith)
    positivity
  refine ⟨max C₁ (|M| * K), le_max_of_le_left hC₁, fun r hr => ?_⟩
  by_cases hrr : r₁ ≤ r
  · have hr1 : 1 ≤ r := hr₁.trans hrr
    have hne : r ^ 2 / 2 ≠ 0 := by positivity
    have := hlarge r hrr
    simp only [admissF, hne, ite_false]
    refine this.trans ?_
    have : 0 ≤ (1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α)) := by
      have : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
      positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  · replace hrr := not_le.mp hrr
    have hmem : r ^ 2 / 2 ∈ Icc (0 : ℝ) (r₁ ^ 2 / 2) :=
      ⟨by positivity, by nlinarith⟩
    have h1 : |admissF c W (r ^ 2 / 2)| ≤ |M| := by
      have := hM _ hmem
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self M)
    have hlog1 : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
    have hp1 : (1 + r₁) ^ (-(2 * c)) ≤ (1 + r) ^ (-(2 * c)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hp2 : Real.log (2 + r₁) ^ (-(1 + α)) ≤ Real.log (2 + r) ^ (-(1 + α)) :=
      Real.rpow_le_rpow_of_nonpos hlog1 (Real.log_le_log (by linarith) (by linarith)) (by linarith)
    have hlog1' : 0 < Real.log (2 + r₁) := Real.log_pos (by linarith)
    have hlow : 1 ≤ K * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α))) := by
      have e : K * ((1 + r₁) ^ (-(2 * c)) * Real.log (2 + r₁) ^ (-(1 + α))) = 1 := by
        rw [hK, Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + r₁), Real.rpow_neg hlog1'.le]
        have h1 : 0 < (1 + r₁) ^ (2 * c) := Real.rpow_pos_of_pos (by linarith) _
        have h2 : 0 < Real.log (2 + r₁) ^ (1 + α) := Real.rpow_pos_of_pos hlog1' _
        field_simp
      calc 1 = K * ((1 + r₁) ^ (-(2 * c)) * Real.log (2 + r₁) ^ (-(1 + α))) := e.symm
        _ ≤ K * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hp1 hp2 (by positivity) (by positivity)) hK0
    calc |admissF c W (r ^ 2 / 2)| ≤ |M| := h1
      _ ≤ |M| * (K * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α)))) := by
          exact le_mul_of_one_le_right (abs_nonneg _) hlow
      _ = (|M| * K) * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α))) := by ring
      _ ≤ _ := by
          have : 0 ≤ (1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α)) := by positivity
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) this

/-- **Lemma T.8 (`uct:admiss`), parts (1) and (2)** (general Mellin-strip admissibility via `C²` edge traces).

Fix `c ≥ 2`, `0 < α < 1` and `W̃` with `StripAdmissData α W` ((M1), (M2) at `ζ = 1`, (M3) on the edge `Re ζ = 0`).  With
`f = f_W` the inverse Mellin lift `(uct:mellin-inv-gen)` (`liftFun (admissPhi c W) x₀`) and `F = admissF c W` its extension by `W̃(1)` at `0`:

(1) `f` does not depend on `x₀ ∈ (0,c)`, is real-valued, and `F` is continuous on `[0,∞)` with `F(0) = W̃(1)` (real);
(2) for `ξ > 0`, `0 ≤ σ < 1`: `(F ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ+iτ,ξ) W̃(σ+iτ) dτ` (`uct:vert-rep`);
    for `ξ = e^L/π²`, `L ≥ 4`: `|(F ρ₀)(cξ)| ≤ C' ξ⁻¹ L^{-1-α}` (`uct:gen-tail`);
    `F ∈ L¹((0,∞), ρ₀ dΔ)`; and `|F(r²/2)| ≤ C'' (1+r)^{-2c} (log(2+r))^{-1-α}` (`r ≥ 0`), which for `d = 2c ∈ ℕ` is the decay bound of the radial function
    `x ↦ f(|x|²/2)` on `ℝ^d`.

Scope and limits: part (3) (Hankel reflection) is not formalised; the hypotheses are those of the paper's statement except that (M2) at `ζ = 0` and (M3) at the edge `ζ = 1`, used only for (3),
are not assumed.  The paper's constants `C'`, `C''` depend on `c`, `α` and `W̃`; here they are existentially quantified. -/
theorem uct_admiss {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripAdmissData α W) :
    -- (1)
    (∀ x₀ x₁ : ℝ, 0 < x₀ → x₀ < c → 0 < x₁ → x₁ < c → ∀ Δ : ℝ, 0 < Δ →
        liftFun (admissPhi c W) x₀ Δ = liftFun (admissPhi c W) x₁ Δ) ∧
    (∀ x₀ : ℝ, 0 < x₀ → x₀ < c → ∀ Δ : ℝ, 0 < Δ → (mellinInv x₀ (admissPhi c W) Δ).im = 0) ∧
    ContinuousOn (admissF c W) (Ici 0) ∧ admissF c W 0 = (W 1).re ∧ (W 1).im = 0 ∧
    -- (2), vertical representation
    (∀ ξ : ℝ, 0 < ξ → ∀ σ : ℝ, 0 ≤ σ → σ < 1 →
        (((hankelRho0 c (c * ξ) * admissF c W (c * ξ) : ℝ)) : ℂ) =
          ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
            ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)) ∧
    -- (2), tail
    (∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 4 ≤ L →
        |hankelRho0 c (c * (Real.exp L / Real.pi ^ 2)) * admissF c W (c * (Real.exp L / Real.pi ^ 2))| ≤
          C * (Real.exp L / Real.pi ^ 2)⁻¹ * L ^ (-(1 + α))) ∧
    -- (2), integrability and radial decay
    IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
        |admissF c W (r ^ 2 / 2)| ≤ C * ((1 + r) ^ (-(2 * c)) * Real.log (2 + r) ^ (-(1 + α)))) := by
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData hc1 hW.toStripM1
  have hFL : ∀ Δ : ℝ, 0 < Δ → admissF c W Δ = admissLift c W Δ := fun Δ hΔ => by simp [admissF, ne_of_gt hΔ]
  refine ⟨?_, ?_, admissF_continuousOn hc hα0 hα1 hW, by simp [admissF], W_one_im hW.toStripM1, ?_, ?_, ?_,
    admiss_radial_decay hc hα0 hα1 hW⟩
  · intro x₀ x₁ hx0 hx1 hy0 hy1 Δ hΔ
    unfold liftFun
    rw [hΦ.mellinInv_indep hx0 hx1 hy0 hy1 hΔ]
  · intro x₀ hx0 hx1 Δ hΔ
    exact hΦ.im_mellinInv hx0 hx1 hΔ
  · intro ξ hξ σ hσ0 hσ1
    rw [hFL _ (by positivity)]
    exact admiss_vert_rep hc1 hW.toStripM1 hσ0 hσ1 hξ
  · obtain ⟨C, hC0, hC⟩ := admiss_tail hc hα0 hα1 hW.toStripM1 hW.edge0
    refine ⟨C, hC0, fun L hL => ?_⟩
    rw [hFL _ (by positivity)]
    exact hC L hL
  · have := admiss_integrable hc hα0 hα1 hW.toStripM1 hW.edge0
    refine this.congr_fun (fun Δ hΔ => ?_) measurableSet_Ioi
    simp [hFL Δ hΔ]

/-- info: 'FormalResearch.SignUncertainty.admiss_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_integrable

/-- info: 'FormalResearch.SignUncertainty.admissF_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admissF_continuousOn

/-- info: 'FormalResearch.SignUncertainty.admiss_radial_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_radial_decay

/-- info: 'FormalResearch.SignUncertainty.uct_admiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_admiss

end FormalResearch.SignUncertainty

module

public import FormalResearch.CohnElkies.HighBandEstimate
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# `O.3(1)`/`(e3)` for `I_dual`: the dual edge integral of a lift

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `O.3`(1), display `(e3)` (`u1co:O3`), whose phase estimate
`dual_phase_oscillatory_bound` and reflected-line symbol bounds (`o2_reflected_line_deriv_bound`) are in `DualPhaseAndO3`.
This module connects them to the two-edge integral `iDual` of `MellinLiftIntegrals`:

* `iDual_eq_dualEdgeIntegral`: `I_dual[D](ξ) = dualEdgeIntegral c L (W_D(c^{1/3}(1 - i ·)))` with `L = log(π² ξ)`
  (substitution `τ = ε v`, `mellinK0_imag_eq`, `edgePhi_eq_cubic_add_ceHth`);
* `iDual_bound_e3`: `|I_dual[D](ξ)| ≤ C ξ⁻¹ (1 + δ₀ c^{1/3})^{-m} c⁻¹ min(L^{-1/4}, L^{-3/2})` for `m ≥ 3`, `δ₀ ∈ (0, 2]`, `c ≥ 2`
  and `S = hbS c ξ ≥ 1`, with `C` depending only on `m` and the symbol constant `CD` of the dual seed (the uniform
  form: the order of quantifiers is `m, CD, ∃ C, ∀ D, δ₀, c, ξ`);
* `iDual_bound_e3_hasU2`: the same for a fixed seed with `HasU2 D`.

Status: proved, unconditional.  Not formalised: the case `m ∈ {1, 2}` (the paper's `(e3)` is stated for the splines of the
construction, `m ≥ 4`; the proof of `gt2b_dual_integral_general` needs `m ≥ 3`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-- The substitution `τ = ε v` turns `I_dual` into the reflected edge integral of `GT.2b(3)`. -/
theorem iDual_eq_dualEdgeIntegral (D : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    iDual D δ₀ m c ξ = dualEdgeIntegral c (Real.log (Real.pi ^ 2 * ξ))
      (fun τ => liftSymbol D δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))) := by
  have hε : 0 < liftEps c := liftEps_pos hc
  have hR : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hεR : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by
    unfold liftEps; rw [← Real.rpow_add hc]; norm_num
  have hRε : c ^ (1 / 3 : ℝ) = (liftEps c)⁻¹ := eq_inv_of_mul_eq_one_right hεR
  have hexp : Real.exp (Real.log (Real.pi ^ 2 * ξ)) / Real.pi ^ 2 = ξ := by
    rw [Real.exp_log (by positivity)]; field_simp
  set G : ℝ → ℂ := fun τ => ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
      liftSymbol D δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))) *
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ)) with hG
  have hpt : ∀ v : ℝ, iDualIntegrand D δ₀ m c ξ v = G (liftEps c * v) := by
    intro v
    unfold iDualIntegrand
    rw [mellinK0_imag_eq c ξ _ hξ]
    simp only [hG]
    have hw : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I =
        ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * ((liftEps c * v : ℝ) : ℂ)) := by
      have : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((liftEps c : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_comm, hεR]; simp
      push_cast
      linear_combination ((v : ℂ) * Complex.I) * this
    rw [hw, edgePhi_eq_cubic_add_ceHth]
    have hmul : ((liftEps c * v : ℝ) : ℂ) * Complex.I = Complex.I * ((liftEps c * v : ℝ) : ℂ) := mul_comm _ _
    rw [hmul]
    unfold edgeR
    ring_nf
  unfold iDual dualEdgeIntegral
  rw [show (fun v : ℝ => iDualIntegrand D δ₀ m c ξ v) = fun v => G (liftEps c * v) from funext hpt,
    MeasureTheory.Measure.integral_comp_mul_left G (liftEps c), hexp]
  rw [abs_of_pos (inv_pos.mpr hε), Complex.real_smul]
  have h1 : ((liftEps c)⁻¹ : ℝ) = c ^ (1 / 3 : ℝ) := by rw [hRε]
  rw [h1]
  push_cast
  field_simp
  rfl

/-- `(e3)` for the dual edge integral of a lift, uniform over seeds with a given symbol constant `CD`. -/
theorem iDual_bound_e3 {m : ℕ} (hm : 3 ≤ m) {CD : ℝ} (hCD : 0 ≤ CD) :
    ∃ C > 0, ∀ {D : ℝ → ℝ}, DifferentiableOn ℂ (airyTwistedLaplaceC D) {y : ℂ | 0 < y.re} →
      (∀ {w : ℂ}, 0 ≤ w.re → ‖airyTwistedLaplaceC D ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∀ {δ₀ c ξ : ℝ}, δ₀ ∈ Ioc 0 2 → 2 ≤ c → 0 < ξ → 1 ≤ hbS c ξ →
        ‖iDual D δ₀ m c ξ‖ ≤ C * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
          min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C₃, hC₃, h3⟩ := o3_dual_bound hm
  refine ⟨C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD + 1), by positivity, fun {D} hdiff hbd {δ₀ c ξ} hδ hc hξ hS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hε2 : liftEps c ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hL : 0 < Real.log (Real.pi ^ 2 * ξ) := by
    have h0 : 0 < Real.pi ^ 2 * liftEps c ^ 2 := by positivity
    unfold hbS at hS
    rw [le_div_iff₀ h0] at hS
    linarith
  have hS' : 1 ≤ Real.log (Real.pi ^ 2 * ξ) / (Real.pi ^ 2 * c ^ (-(2 / 3 : ℝ))) := by
    unfold hbS at hS; rwa [hε2] at hS
  set F : ℂ → ℂ := fun w => airyTwistedLaplaceC D ((ceCs : ℂ) * w) with hF
  have hFd : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := by
    refine hdiff.comp (differentiableOn_const _ |>.mul differentiableOn_id) fun w hw => ?_
    simp only [Set.mem_ofPred_eq, Complex.re_ofReal_mul] at hw ⊢
    exact mul_pos ceCs_pos hw
  have hFb : ∀ w : ℂ, 0 < w.re → ‖F w‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun w hw => hbd (le_of_lt hw)
  set f : ℝ → ℂ := fun t => F (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ))) with hf
  have hf_cd : ContDiff ℝ 2 f := (o2_reflected_line_contDiff hFd hc0).of_le (by simp)
  have hf_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r f τ‖ ≤
      (2 ^ (9 / 2 : ℝ) * 2 * CD) * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
    intro r hr τ
    refine (o2_reflected_line_deriv_bound hCD hFd hFb hc τ r).trans ?_
    have hr2 : (r : ℝ) ≤ 2 := by exact_mod_cast hr
    have h1 : (2 : ℝ) ^ ((r : ℝ) + 5 / 2) ≤ 2 ^ (9 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hr2])
    have h2 : (r.factorial : ℝ) ≤ 2 := by
      have : r.factorial ≤ (2 : ℕ).factorial := Nat.factorial_le hr
      exact_mod_cast this
    have h3 : 0 ≤ c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by positivity
    calc (2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * CD * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))
        = ((2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * CD) * (c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) := by ring
      _ ≤ ((2 : ℝ) ^ (9 / 2 : ℝ) * 2 * CD) * (c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hb := h3 hδ hc hL hS' (by positivity : 0 ≤ 2 ^ (9 / 2 : ℝ) * 2 * CD) hf_cd hf_bd
  rw [iDual_eq_dualEdgeIntegral D δ₀ m hc0 hξ]
  have hmul : (fun τ : ℝ => liftSymbol D δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))) =
      fun τ => bsplineMult (ceCs * δ₀ * c ^ (1 / 3 : ℝ) / m) m τ * f τ := by
    funext τ
    unfold liftSymbol liftMultiplier bsplineMult
    simp only [hf, hF]
    congr 2
    push_cast
    ring_nf
  rw [hmul]
  have hexp : Real.exp (Real.log (Real.pi ^ 2 * ξ)) / Real.pi ^ 2 = ξ := by
    rw [Real.exp_log (by positivity)]; field_simp
  rw [hexp] at hb
  refine hb.trans ?_
  have hnn : 0 ≤ ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
      min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have : 0 < 1 + δ₀ * c ^ (1 / 3 : ℝ) := by have := hδ.1; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hξ.le) (Real.rpow_nonneg this.le _)) (inv_nonneg.mpr hc0.le))
      (le_min (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hL.le _))
  have : C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD) ≤ C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD + 1) := by nlinarith
  calc _ = (C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD)) * (ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) := by ring
    _ ≤ _ := by
        rw [show C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD + 1) * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
          min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) =
          (C₃ * (2 ^ (9 / 2 : ℝ) * 2 * CD + 1)) * (ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
          min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) by ring]
        exact mul_le_mul_of_nonneg_right this hnn

/-- `(e3)` for a fixed dual seed with the `U.2` package. -/
theorem iDual_bound_e3_hasU2 {m : ℕ} (hm : 3 ≤ m) {D : ℝ → ℝ} (hD : HasU2 D) :
    ∃ C > 0, ∀ {δ₀ c ξ : ℝ}, δ₀ ∈ Ioc 0 2 → 2 ≤ c → 0 < ξ → 1 ≤ hbS c ξ →
        ‖iDual D δ₀ m c ξ‖ ≤ C * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
          min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨CD, hCD, hb⟩ := hD.rhp
  obtain ⟨C, hC, h⟩ := iDual_bound_e3 hm hCD.le
  exact ⟨C, hC, fun {δ₀ c ξ} => h hD.differentiable (fun {w} hw => hb w hw)⟩

/-- info: 'FormalResearch.CohnElkies.iDual_eq_dualEdgeIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.iDual_eq_dualEdgeIntegral

/-- info: 'FormalResearch.CohnElkies.iDual_bound_e3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.iDual_bound_e3

/-- info: 'FormalResearch.CohnElkies.iDual_bound_e3_hasU2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.iDual_bound_e3_hasU2

end FormalResearch.CohnElkies

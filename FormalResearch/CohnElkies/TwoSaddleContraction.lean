module

public import FormalResearch.CohnElkies.MellinAiryToolkit
public import FormalResearch.CohnElkies.AiryTwistedLaplace
public import FormalResearch.CohnElkies.ClosedResolvent
public import FormalResearch.CohnElkies.OriginMellinAndS0
public import FormalResearch.Special.AiryTransformRKHS
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Airy–Curie–Weiss two-saddle contraction, `PF.3` kernel bound, `PF.5` margin, and `O.11f` cardinal identity

Sources (PR 240 commit `58dd780c8`):
* `CFT/sign_uncertainty/paper/ce_o1_route.tex`:
  - Lemma `O.11aw` (`ceo:O11aw`, `(ceo:O11aw.1)`–`(ceo:O11aw.2)`): exact Airy–Curie–Weiss two-saddle
    amplitude contraction `0 < A(x) < 1`, limits at `0⁺` and `∞`, and uniform contraction on `L(x) ≥ L₀`.
  - Lemma `O.11f` (`ceo:O11f`, `(ceo:O11f.1)`): exact infinite Airy-cardinal identity
    `H_*(u) = ∑_{n ≥ 1} c_n L_n(u)` with pointwise `HasSum` (including the removable pole `u = a₁'`
    with value `a₁' Ai(a₁')` and Airy zeros `a_n`), locally uniform convergence on `ℂ` and `ℝ`,
    `L²(ℝ)` orthonormality and convergence, and Parseval identity `∫ H_*² = |a₁'|`.
* `CFT/sign_uncertainty/paper/ce_physical_log_far.tex`:
  - Lemma `PF.3` (`cepf:PF3`, `(cepf:PF.3)`): positive-argument oscillatory kernel bound
    `|K_c(y)| ≤ C c⁻² y⁻²` (`y ≥ y₀ > 0`, `c ≥ 2`) by two integrations by parts, with explicit
    constant `C` independent of `c, y` and explicit non-vacuity witness `a_c(τ) = (1 + τ²)⁻³`, `R = 0`.
  - Theorem `PF.5` (`(cepf:PF.5.4)`–`(cepf:PF5a)`): worst-phase margin
    `0 < (1 - φ)² + (1 - A) φ ≤ 2 - θ(1 - φ²) - (1 + A) φ` and monotone lower bound on `J = [L₀, L₁]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ContDiff ComplexInnerProductSpace

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1: Exact Airy–Curie–Weiss two-saddle contraction (`ce_o1_route.tex` Lemma O.11aw) -/

/-- The saddle curvature factor `η(x) = (3 / (2 x²)) (1 - 2x / sinh(2x))` (`ceo:O11aw`). -/
noncomputable def ceEta (x : ℝ) : ℝ :=
  (3 / (2 * x ^ 2)) * (1 - 2 * x / Real.sinh (2 * x))

/-- The smooth-branch saddle scale `X₀(x) = ℓ(x) / c_s` (`ceo:O11aw`). -/
noncomputable def ceX0 (x : ℝ) : ℝ := ceEll x / ceCs

/-- The coherent saddle scale `X₁(τ) = c_s² τ² / 4` (`ceo:O11aw`). -/
noncomputable def ceX1 (τ : ℝ) : ℝ := ceCs ^ 2 * τ ^ 2 / 4

/-- Exact semiclassical transport ratio `A(x) = (X₀(x) / X₁(2x/π))^{3/2} η(x)^{-1/2}` (`(ceo:O11aw.1)`). -/
noncomputable def ceTransportRatio (x : ℝ) : ℝ :=
  (ceX0 x / ceX1 (2 * x / π)) ^ (3 / 2 : ℝ) * (ceEta x) ^ (-(1 / 2 : ℝ))

private lemma ceCs_cube : ceCs ^ 3 = π ^ 2 / 3 := by
  unfold ceCs
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

lemma ceEll_pos {x : ℝ} (hx : 0 < x) : 0 < ceEll x := by
  unfold ceEll
  exact Real.log_pos ((one_lt_div (tanh_pos_of_pos hx)).mpr (tanh_lt_id hx))

lemma ceEll_lt_sq_div_three {x : ℝ} (hx : 0 < x) : ceEll x < x ^ 2 / 3 := by
  have h1 : ceEll x < x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) := ceEll_lt hx
  have hsq : 1 < Real.sqrt (1 + x ^ 2 / 3) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ < Real.sqrt (1 + x ^ 2 / 3) := Real.sqrt_lt_sqrt zero_le_one (by linarith [sq_pos_of_pos hx])
  calc ceEll x < x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) := h1
    _ < x ^ 2 / (3 * 1) := div_lt_div_of_pos_left (sq_pos_of_pos hx) (by norm_num) (by linarith)
    _ = x ^ 2 / 3 := by ring

lemma ceX0_div_ceX1 {x : ℝ} (hx : 0 < x) :
    ceX0 x / ceX1 (2 * x / π) = 3 * ceEll x / x ^ 2 := by
  unfold ceX0 ceX1
  have hcs : ceCs ≠ 0 := ceCs_pos.ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hx0 : x ≠ 0 := hx.ne'
  field_simp
  rw [ceCs_cube]
  ring

/-- `0 < X₀(x) < X₁(2x / π)` for every `x > 0` (`ceo:O11aw`). -/
theorem ceX0_pos_and_lt_ceX1 {x : ℝ} (hx : 0 < x) :
    0 < ceX0 x ∧ ceX0 x < ceX1 (2 * x / π) := by
  refine ⟨div_pos (ceEll_pos hx) ceCs_pos, ?_⟩
  have hcs : ceCs ≠ 0 := ceCs_pos.ne'
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hX1 : ceX1 (2 * x / π) = (x ^ 2 / 3) / ceCs := by
    unfold ceX1; field_simp; rw [ceCs_cube]; ring
  rw [hX1]
  exact div_lt_div_of_pos_right (ceEll_lt_sq_div_three hx) ceCs_pos

/-- `0 < η(x) < 1` for every `x > 0` (`ceo:O11aw`). -/
theorem ceEta_pos_and_lt_one {x : ℝ} (hx : 0 < x) :
    0 < ceEta x ∧ ceEta x < 1 := by
  have hx2 : 0 < 2 * x := by linarith
  have hsh_gt : 2 * x < Real.sinh (2 * x) := sinh_gt_id hx2
  have hsh_pos : 0 < Real.sinh (2 * x) := by linarith
  constructor
  · unfold ceEta
    exact mul_pos (by positivity) (sub_pos.mpr ((div_lt_one hsh_pos).mpr hsh_gt))
  · set t : ℝ := (2 * x) ^ 2 / 6
    have ht_pos : 0 < t := by dsimp [t]; positivity
    have hsinh_le : Real.sinh (2 * x) / (2 * x) ≤ Real.exp t := sinh_div_le_exp_sq_div_six hx2
    have hexp_le : Real.exp (-t) ≤ 2 * x / Real.sinh (2 * x) := by
      rw [Real.exp_neg]
      exact (inv_anti₀ (div_pos hsh_pos hx2) hsinh_le).trans_eq (inv_div _ _)
    have hexp_lt : 1 - t < Real.exp (-t) := by
      linarith [Real.add_one_lt_exp (neg_ne_zero.mpr ht_pos.ne')]
    have hsub : 1 - 2 * x / Real.sinh (2 * x) < 2 * x ^ 2 / 3 := by
      have ht_eq : t = 2 * x ^ 2 / 3 := by dsimp [t]; ring
      linarith
    unfold ceEta
    calc (3 / (2 * x ^ 2)) * (1 - 2 * x / Real.sinh (2 * x))
        < (3 / (2 * x ^ 2)) * (2 * x ^ 2 / 3) := mul_lt_mul_of_pos_left hsub (by positivity)
      _ = 1 := by field_simp

/-- Closed form `A(x) = ((3 ℓ(x) / x²)³ / η(x))^{1/2}` for `x > 0` (`(ceo:O11aw.1)`). -/
theorem ceTransportRatio_eq_closed {x : ℝ} (hx : 0 < x) :
    ceTransportRatio x = ((3 * ceEll x / x ^ 2) ^ 3 / ceEta x) ^ (1 / 2 : ℝ) := by
  have ha : 0 < 3 * ceEll x / x ^ 2 := div_pos (mul_pos three_pos (ceEll_pos hx)) (sq_pos_of_pos hx)
  have hb : 0 < ceEta x := (ceEta_pos_and_lt_one hx).1
  unfold ceTransportRatio
  rw [ceX0_div_ceX1 hx]
  have ha32 : (3 * ceEll x / x ^ 2) ^ (3 / 2 : ℝ) = ((3 * ceEll x / x ^ 2) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (3 * ceEll x / x ^ 2) 3, ← Real.rpow_mul ha.le]; norm_num
  have hb12 : ceEta x ^ (-(1 / 2 : ℝ)) = (ceEta x)⁻¹ ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hb.le, Real.inv_rpow hb.le]
  rw [ha32, hb12, ← Real.mul_rpow (pow_nonneg ha.le 3) (inv_nonneg.mpr hb.le), ← div_eq_mul_inv]

/-- **Lemma O.11aw (`(ceo:O11aw.1)`):** `0 < A(x) < 1` for every `x > 0`. -/
theorem ceTransportRatio_pos_and_lt_one {x : ℝ} (hx : 0 < x) :
    0 < ceTransportRatio x ∧ ceTransportRatio x < 1 := by
  rw [ceTransportRatio_eq_closed hx]
  have ha : 0 < 3 * ceEll x / x ^ 2 := div_pos (mul_pos three_pos (ceEll_pos hx)) (sq_pos_of_pos hx)
  have hb : 0 < ceEta x := (ceEta_pos_and_lt_one hx).1
  set t : ℝ := x ^ 2 / 3
  have ht1 : 0 < 1 + t := by dsimp [t]; positivity
  have h_ell : 3 * ceEll x / x ^ 2 < (Real.sqrt (1 + t))⁻¹ := by
    have h1 := ceEll_lt hx
    have hsq0 : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr ht1
    have hx0 : x ≠ 0 := hx.ne'
    calc 3 * ceEll x / x ^ 2 < 3 * (x ^ 2 / (3 * Real.sqrt (1 + t))) / x ^ 2 := by gcongr
      _ = (Real.sqrt (1 + t))⁻¹ := by field_simp
  have h_cubed : (3 * ceEll x / x ^ 2) ^ 3 < ((1 + t) ^ (3 / 2 : ℝ))⁻¹ := by
    have hpow := pow_lt_pow_left₀ h_ell ha.le (by norm_num : 3 ≠ 0)
    have hrt : (Real.sqrt (1 + t)) ^ 3 = (1 + t) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht1.le]; norm_num
    rwa [inv_pow, hrt] at hpow
  have h_eta : ((1 + t) ^ (3 / 2 : ℝ))⁻¹ < ceEta x := by
    have hmul := mul_lt_mul_of_pos_left (ceEll_deriv_gt hx) (by positivity : 0 < 3 / (2 * x))
    have hx0 : x ≠ 0 := hx.ne'
    have hden0 : (1 + t) ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht1 _).ne'
    have hsh0 : Real.sinh (2 * x) ≠ 0 := (by linarith [sinh_gt_id (by linarith : 0 < 2 * x)] : 0 < Real.sinh (2 * x)).ne'
    have h_lhs : 3 / (2 * x) * (2 * x / (3 * (1 + t) ^ (3 / 2 : ℝ))) = ((1 + t) ^ (3 / 2 : ℝ))⁻¹ := by field_simp
    have h_rhs : 3 / (2 * x) * (1 / x - 2 / Real.sinh (2 * x)) = ceEta x := by unfold ceEta; field_simp
    rwa [h_lhs, h_rhs] at hmul
  have hpos : 0 < (3 * ceEll x / x ^ 2) ^ 3 / ceEta x := div_pos (pow_pos ha 3) hb
  exact ⟨Real.rpow_pos_of_pos hpos _, Real.rpow_lt_one hpos.le ((div_lt_one hb).mpr (h_cubed.trans h_eta)) (by norm_num)⟩

/-- `A(x) → 1` as `x ↓ 0` (`ceo:O11aw`). -/
theorem ceTransportRatio_tendsto_one_atZero :
    Tendsto ceTransportRatio (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let L_lb : ℝ → ℝ := fun x => ((1 - 2 / 5 * x ^ 2) ^ 3) ^ (1 / 2 : ℝ)
  have hL_lim : Tendsto L_lb (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous L_lb :=
      (((continuous_const.sub (continuous_const.mul (continuous_pow 2))).pow 3).rpow_const
        (fun _ => Or.inr (by norm_num)))
    simpa [L_lb] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h_le : ∀ᶠ x in 𝓝[>] (0 : ℝ), L_lb x ≤ ceTransportRatio x := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x ⟨hx0, hx1⟩
    have hth := ceHth_le_of_le_one hx0 hx1.le
    have hlog : Real.log (Real.tanh x / x) = -ceEll x := by unfold ceEll; rw [← Real.log_inv, inv_div]
    unfold ceHth at hth
    rw [hlog] at hth
    have h_ell_ge : 1 - 2 / 5 * x ^ 2 ≤ 3 * ceEll x / x ^ 2 := by rw [le_div_iff₀ (sq_pos_of_pos hx0)]; linarith
    have h_lb_pos : 0 ≤ 1 - 2 / 5 * x ^ 2 := by nlinarith
    have h_cubed : (1 - 2 / 5 * x ^ 2) ^ 3 ≤ (3 * ceEll x / x ^ 2) ^ 3 := pow_le_pow_left₀ h_lb_pos h_ell_ge 3
    have hη := ceEta_pos_and_lt_one hx0
    have h_div : (1 - 2 / 5 * x ^ 2) ^ 3 ≤ (3 * ceEll x / x ^ 2) ^ 3 / ceEta x := by
      rw [le_div_iff₀ hη.1]
      exact (mul_le_of_le_one_right (by positivity) hη.2.le).trans h_cubed
    rw [ceTransportRatio_eq_closed hx0]
    exact Real.rpow_le_rpow (pow_nonneg h_lb_pos 3) h_div (by norm_num)
  have h_ge : ∀ᶠ x in 𝓝[>] (0 : ℝ), ceTransportRatio x ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (ceTransportRatio_pos_and_lt_one hx).2.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL_lim tendsto_const_nhds h_le h_ge

/-- `A(x) → 0` as `x → ∞` (`ceo:O11aw`). -/
theorem ceTransportRatio_tendsto_zero_atTop :
    Tendsto ceTransportRatio atTop (𝓝 0) := by
  let C0 : ℝ := (5 * Real.sqrt 3) ^ (1 / 2 : ℝ)
  have h_ub_lim : Tendsto (fun x : ℝ => C0 * x ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C0
  have h_nn : ∀ᶠ x in atTop, 0 ≤ ceTransportRatio x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (ceTransportRatio_pos_and_lt_one hx).1.le
  have h_ub : ∀ᶠ x in atTop, ceTransportRatio x ≤ C0 * x ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hx0' : x ≠ 0 := hx0.ne'
    have h_ell : 3 * ceEll x / x ^ 2 ≤ Real.sqrt 3 / x := by
      have hsqrt_ge : x / Real.sqrt 3 ≤ Real.sqrt (1 + x ^ 2 / 3) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ x / Real.sqrt 3)]
        refine Real.sqrt_le_sqrt ?_
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        linarith
      have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have hdiv : ceEll x ≤ x ^ 2 / (3 * (x / Real.sqrt 3)) :=
        (ceEll_lt hx0).le.trans (div_le_div_of_nonneg_left (sq_pos_of_pos hx0).le (by positivity) (by gcongr))
      calc 3 * ceEll x / x ^ 2 ≤ 3 * (x ^ 2 / (3 * (x / Real.sqrt 3))) / x ^ 2 := by gcongr
        _ = Real.sqrt 3 / x := by field_simp
    have h_cubed : (3 * ceEll x / x ^ 2) ^ 3 ≤ 3 * Real.sqrt 3 / x ^ 3 := by
      have ha : 0 ≤ 3 * ceEll x / x ^ 2 := div_nonneg (mul_nonneg (by norm_num) (ceEll_pos hx0).le) (sq_nonneg x)
      have h3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, Real.sq_sqrt (by norm_num)]
      calc (3 * ceEll x / x ^ 2) ^ 3 ≤ (Real.sqrt 3 / x) ^ 3 := pow_le_pow_left₀ ha h_ell 3
        _ = 3 * Real.sqrt 3 / x ^ 3 := by rw [div_pow, h3]
    have h_eta : 3 / (5 * x ^ 2) ≤ ceEta x := by
      have hsh := sinh_taylor_lower (by linarith : 0 ≤ 2 * x)
      have h10 : 10 / 3 * x ≤ Real.sinh (2 * x) := by
        have hx3 : x ≤ x ^ 3 := le_self_pow₀ hx (by norm_num)
        nlinarith [pow_nonneg (by linarith : 0 ≤ 2 * x) 5]
      have hfrac : 2 * x / Real.sinh (2 * x) ≤ 3 / 5 := by rw [div_le_iff₀ (by linarith)]; linarith
      unfold ceEta
      have hsub : 2 / 5 ≤ 1 - 2 * x / Real.sinh (2 * x) := by linarith
      calc 3 / (5 * x ^ 2) = 3 / (2 * x ^ 2) * (2 / 5) := by ring
        _ ≤ 3 / (2 * x ^ 2) * (1 - 2 * x / Real.sinh (2 * x)) := by gcongr
    have h_div : (3 * ceEll x / x ^ 2) ^ 3 / ceEta x ≤ 5 * Real.sqrt 3 * x⁻¹ := by
      calc (3 * ceEll x / x ^ 2) ^ 3 / ceEta x
          ≤ (3 * Real.sqrt 3 / x ^ 3) / (3 / (5 * x ^ 2)) := div_le_div₀ (by positivity) h_cubed (by positivity) h_eta
        _ = 5 * Real.sqrt 3 * x⁻¹ := by field_simp
    have hnn_lhs : 0 ≤ (3 * ceEll x / x ^ 2) ^ 3 / ceEta x :=
      div_nonneg (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (ceEll_pos hx0).le) (sq_nonneg x)) 3)
        (ceEta_pos_and_lt_one hx0).1.le
    rw [ceTransportRatio_eq_closed hx0]
    calc ((3 * ceEll x / x ^ 2) ^ 3 / ceEta x) ^ (1 / 2 : ℝ)
        ≤ (5 * Real.sqrt 3 * x⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hnn_lhs h_div (by norm_num)
      _ = C0 * x ^ (-(1 / 2 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (inv_nonneg.mpr hx0.le), Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_ub_lim h_nn h_ub

private lemma ceTransportRatio_continuousOn_Ioi : ContinuousOn ceTransportRatio (Ioi 0) := by
  intro x (hx : 0 < x)
  have hX0 : ContinuousAt ceX0 x := (ceEll_hasDerivAt hx).continuousAt.div_const ceCs
  have hX1 : ContinuousAt (fun t => ceX1 (2 * t / π)) x := by unfold ceX1; fun_prop
  have hX1_ne : ceX1 (2 * x / π) ≠ 0 :=
    ((ceX0_pos_and_lt_ceX1 hx).1.trans (ceX0_pos_and_lt_ceX1 hx).2).ne'
  have hrat_pos : 0 < ceX0 x / ceX1 (2 * x / π) :=
    div_pos (ceX0_pos_and_lt_ceX1 hx).1 ((ceX0_pos_and_lt_ceX1 hx).1.trans (ceX0_pos_and_lt_ceX1 hx).2)
  have hsh_pos : 0 < Real.sinh (2 * x) := by linarith [sinh_gt_id (by linarith : 0 < 2 * x)]
  have hEta : ContinuousAt ceEta x := by
    unfold ceEta
    refine (continuousAt_const.div ((continuousAt_id.pow 2).const_mul 2)
      (mul_pos two_pos (sq_pos_of_pos hx)).ne').mul ?_
    exact continuousAt_const.sub
      ((continuousAt_id.const_mul 2).div (Real.continuous_sinh.continuousAt.comp (continuousAt_id.const_mul 2))
        hsh_pos.ne')
  have h1 : ContinuousAt (fun t => (ceX0 t / ceX1 (2 * t / π)) ^ (3 / 2 : ℝ)) x :=
    ContinuousAt.rpow_const (p := (3 / 2 : ℝ)) (hX0.div hX1 hX1_ne) (Or.inl hrat_pos.ne')
  have h2 : ContinuousAt (fun t => (ceEta t) ^ (-(1 / 2 : ℝ))) x :=
    ContinuousAt.rpow_const (p := -(1 / 2 : ℝ)) hEta (Or.inl (ceEta_pos_and_lt_one hx).1.ne')
  exact ContinuousWithinAt.congr ((h1.mul h2).continuousWithinAt) (fun _ _ => rfl) rfl

/-- **Lemma O.11aw (`(ceo:O11aw.2)`):** uniform contraction `sup_{L(x) ≥ L₀} A(x) < 1` for every `L₀ > 0`. -/
theorem ceTransportRatio_sup_lt_one :
    ∀ L₀ > 0, ∃ q < 1, ∀ x > 0, L₀ ≤ ceEll x → ceTransportRatio x ≤ q := by
  intro L₀ hL₀
  set a : ℝ := Real.sqrt (3 * L₀)
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha_lt : ∀ x > 0, L₀ ≤ ceEll x → a < x := fun x hx hL => by
    have h1 : L₀ < x ^ 2 / 3 := hL.trans_lt (ceEll_lt_sq_div_three hx)
    rw [← Real.sqrt_sq hx.le]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  obtain ⟨B, hB⟩ := (eventually_atTop.mp (ceTransportRatio_tendsto_zero_atTop.eventually
    (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))))
  set b : ℝ := max a B
  have hcont : ContinuousOn ceTransportRatio (Icc a b) :=
    ceTransportRatio_continuousOn_Ioi.mono fun x hx => lt_of_lt_of_le ha_pos hx.1
  obtain ⟨xm, hxm_mem, hxm_max⟩ := isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr (le_max_left a B)⟩ hcont
  have hxm_lt : ceTransportRatio xm < 1 := (ceTransportRatio_pos_and_lt_one (lt_of_lt_of_le ha_pos hxm_mem.1)).2
  refine ⟨max (1 / 2) (ceTransportRatio xm), max_lt (by norm_num) hxm_lt, fun x hx hL => ?_⟩
  have hax := ha_lt x hx hL
  rcases le_or_gt x b with hxb | hxb
  · exact (hxm_max ⟨hax.le, hxb⟩).trans (le_max_right _ _)
  · exact (hB x ((le_max_right a B).trans hxb.le)).trans (le_max_left _ _)

/-! ### Part 2: Positive-argument oscillatory kernel bound (`ce_physical_log_far.tex` Lemma PF.3) -/

/-- Explicit `c, y`-independent constant for Lemma `PF.3` (`(cepf:PF.3)`). -/
noncomputable def pf3Const (C_a C₂ C₃ y₀ : ℝ) : ℝ :=
  2 * (C_a + 3 * C_a * C₂ / y₀ + C_a * C₃ / y₀ + 3 * C_a * C₂ ^ 2 / y₀ ^ 2)

private lemma integrable_inv_one_add_abs_sq :
    Integrable (fun τ : ℝ => ((1 + |τ|) ^ 2)⁻¹) volume := by
  have h : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-2 : ℝ)) volume :=
    integrable_one_add_norm (E := ℝ) (r := 2) (by rw [Module.finrank_self]; norm_num)
  refine h.congr (ae_of_all _ fun τ => ?_)
  dsimp only
  rw [Real.norm_eq_abs, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]

private lemma integral_one_add_abs_inv_sq :
    ∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹ = 2 := by
  have hint := integrable_inv_one_add_abs_sq
  have h_pos : ∀ T : ℝ, 0 ≤ T → ∫ τ in (0 : ℝ)..T, ((1 + |τ|) ^ 2)⁻¹ = 1 - (1 + T)⁻¹ := by
    intro T hT
    have heq : EqOn (fun τ : ℝ => ((1 + |τ|) ^ 2)⁻¹) (fun τ : ℝ => ((1 + τ) ^ 2)⁻¹) (uIcc 0 T) := by
      intro τ hτ
      rw [uIcc_of_le hT] at hτ
      dsimp only
      rw [abs_of_nonneg hτ.1]
    rw [intervalIntegral.integral_congr heq]
    have hF : ∀ τ ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t : ℝ => -(1 + t)⁻¹) (((1 + τ) ^ 2)⁻¹) τ := by
      intro τ hτ
      rw [uIcc_of_le hT] at hτ
      have hne : 1 + τ ≠ 0 := by linarith [hτ.1]
      exact (((hasDerivAt_id τ).const_add 1).inv hne).neg.congr_deriv (by simp; ring)
    have hcont : ContinuousOn (fun τ : ℝ => ((1 + τ) ^ 2)⁻¹) (uIcc 0 T) :=
      ((continuousOn_const.add continuousOn_id).pow 2).inv₀ fun τ hτ => by
        rw [uIcc_of_le hT] at hτ; change (1 + τ) ^ 2 ≠ 0; exact pow_ne_zero 2 (by linarith [hτ.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
    simp only [add_zero, inv_one]; ring
  have h_neg : ∀ T : ℝ, 0 ≤ T → ∫ τ in (-T)..(0 : ℝ), ((1 + |τ|) ^ 2)⁻¹ = 1 - (1 + T)⁻¹ := by
    intro T hT
    have heq : EqOn (fun τ : ℝ => ((1 + |τ|) ^ 2)⁻¹) (fun τ : ℝ => ((1 - τ) ^ 2)⁻¹) (uIcc (-T) 0) := by
      intro τ hτ
      rw [uIcc_of_le (by linarith)] at hτ
      dsimp only
      rw [abs_of_nonpos hτ.2, sub_eq_add_neg]
    rw [intervalIntegral.integral_congr heq]
    have hF : ∀ τ ∈ uIcc (-T) (0 : ℝ), HasDerivAt (fun t : ℝ => (1 - t)⁻¹) (((1 - τ) ^ 2)⁻¹) τ := by
      intro τ hτ
      rw [uIcc_of_le (by linarith)] at hτ
      have hne : 1 - τ ≠ 0 := by linarith [hτ.2]
      exact (((hasDerivAt_const τ 1).sub (hasDerivAt_id τ)).inv hne).congr_deriv (by simp)
    have hcont : ContinuousOn (fun τ : ℝ => ((1 - τ) ^ 2)⁻¹) (uIcc (-T) 0) :=
      ((continuousOn_const.sub continuousOn_id).pow 2).inv₀ fun τ hτ => by
        rw [uIcc_of_le (by linarith)] at hτ; change (1 - τ) ^ 2 ≠ 0; exact pow_ne_zero 2 (by linarith [hτ.2])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
    simp only [sub_zero, inv_one, sub_neg_eq_add]
  have hI : Tendsto (fun T : ℝ => ∫ τ in (-T)..T, ((1 + |τ|) ^ 2)⁻¹) atTop
      (𝓝 (∫ τ : ℝ, ((1 + |τ|) ^ 2)⁻¹)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => 2 - 2 * (1 + T)⁻¹) atTop (𝓝 2) := by
    have h1 : Tendsto (fun T : ℝ => (1 + T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)
    simpa using tendsto_const_nhds.sub (h1.const_mul 2)
  have hev : ∀ᶠ T in atTop, ∫ τ in (-T)..T, ((1 + |τ|) ^ 2)⁻¹ = 2 - 2 * (1 + T)⁻¹ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [← intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable hint.intervalIntegrable,
      h_neg T hT, h_pos T hT]
    ring
  exact tendsto_nhds_unique (hI.congr' hev) hlim

private lemma rpow_neg_le_inv_sq {s r : ℝ} (hs : 1 ≤ s) (hr : 2 ≤ r) :
    s ^ (-r) ≤ (s ^ 2)⁻¹ := by
  have hs0 : 0 < s := by linarith
  calc s ^ (-r) ≤ s ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    _ = (s ^ 2)⁻¹ := by rw [Real.rpow_neg hs0.le]; norm_cast

private lemma pf3_ibp_step {c : ℝ} {φ' b b' : ℝ → ℝ} {E : ℝ → ℂ}
    (hc_pos : 0 < c) (hφ'_pos : ∀ τ, 0 < φ' τ)
    (hE_hd : ∀ τ, HasDerivAt E (Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ) τ)
    (hb_hd : ∀ τ, HasDerivAt (fun t => b t / φ' t) (b' τ) τ)
    (hb_int : Integrable (fun τ : ℝ => (b τ : ℂ) * E τ))
    (hb'_int : Integrable (fun τ : ℝ => (b' τ : ℂ) * E τ))
    (hu_int : Integrable (fun τ : ℝ => ((b τ / φ' τ : ℝ) : ℂ) * E τ)) :
    ∫ τ : ℝ, (b τ : ℂ) * E τ = -(Complex.I * (c : ℂ))⁻¹ * ∫ τ : ℝ, (b' τ : ℂ) * E τ := by
  have huv' : Integrable (fun τ : ℝ => ((b τ / φ' τ : ℝ) : ℂ) * (Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ)) := by
    have heq : (fun τ : ℝ => ((b τ / φ' τ : ℝ) : ℂ) * (Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ)) =
        fun τ => (Complex.I * (c : ℂ)) * ((b τ : ℂ) * E τ) := by
      funext τ
      have hne : (φ' τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_pos τ).ne'
      push_cast; field_simp
    rw [heq]; exact hb_int.const_mul _
  have hraw := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun τ => ((b τ / φ' τ : ℝ) : ℂ)) (v := E)
    (u' := fun τ => (b' τ : ℂ)) (v' := fun τ => Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ)
    (fun τ _ => (hb_hd τ).ofReal_comp) (fun τ _ => hE_hd τ) huv' hb'_int hu_int
  have hlhs : (∫ τ : ℝ, ((b τ / φ' τ : ℝ) : ℂ) * (Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ)) =
      (Complex.I * (c : ℂ)) * ∫ τ : ℝ, (b τ : ℂ) * E τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    have hne : (φ' τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'_pos τ).ne'
    push_cast; field_simp
  rw [hlhs] at hraw
  have hic : Complex.I * (c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc_pos.ne')
  calc ∫ τ : ℝ, (b τ : ℂ) * E τ
      = (Complex.I * (c : ℂ))⁻¹ * ((Complex.I * (c : ℂ)) * ∫ τ : ℝ, (b τ : ℂ) * E τ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hic, one_mul]
    _ = (Complex.I * (c : ℂ))⁻¹ * (-∫ τ : ℝ, (b' τ : ℂ) * E τ) := by rw [hraw]
    _ = -(Complex.I * (c : ℂ))⁻¹ * ∫ τ : ℝ, (b' τ : ℂ) * E τ := by ring

/-- **Lemma PF.3 (`cepf:PF3`, `(cepf:PF.3)`):** positive-argument oscillatory kernel bound
`‖∫ a_c(τ) exp(i c (y τ + R(τ))) dτ‖ ≤ C c⁻² y⁻²` for `c ≥ 2` and `y ≥ y₀ > 0`,
with explicit constant `C = pf3Const C_a C₂ C₃ y₀` independent of `c, y`. -/
theorem pf3_kernel_bound
    {a_c R : ℝ → ℝ} {m : ℕ} (hm : 4 ≤ m)
    {C_a C₂ C₃ y₀ c : ℝ} (hc : 2 ≤ c) (hy₀ : 0 < y₀)
    (ha_cd : ContDiff ℝ 2 a_c) (hR_cd : ContDiff ℝ 3 R)
    (hR1_nn : ∀ τ, 0 ≤ iteratedDeriv 1 R τ)
    (hR2_bd : ∀ τ, |iteratedDeriv 2 R τ| ≤ C₂ * (1 + |τ|))
    (hR3_bd : ∀ τ, |iteratedDeriv 3 R τ| ≤ C₃)
    (ha_bd : ∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_c τ| ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2))
    {y : ℝ} (hy : y₀ ≤ y) :
    ‖∫ τ : ℝ, (a_c τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))‖ ≤
      pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by
  have hCa_nn : 0 ≤ C_a := by
    have h0 := ha_bd 0 (by omega) 0; simpa [iteratedDeriv_zero] using (abs_nonneg _).trans h0
  have hC₂_nn : 0 ≤ C₂ := by
    have h0 := hR2_bd 0; simpa using (abs_nonneg _).trans h0
  have hC₃_nn : 0 ≤ C₃ := (abs_nonneg _).trans (hR3_bd 0)
  have hc_pos : 0 < c := by linarith
  have hy_pos : 0 < y := by linarith
  -- Derivatives from `ContDiff`
  set a0 := a_c; set a1 := deriv a_c; set a2 := deriv a1
  set R1 := deriv R; set R2 := deriv R1; set R3 := deriv R2
  have ha1_eq : a1 = iteratedDeriv 1 a_c := by rw [iteratedDeriv_one]
  have ha2_eq : a2 = iteratedDeriv 2 a_c := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hR1_eq : R1 = iteratedDeriv 1 R := by rw [iteratedDeriv_one]
  have hR2_eq : R2 = iteratedDeriv 2 R := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hR3_eq : R3 = iteratedDeriv 3 R := by rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  have ha1_cd : ContDiff ℝ 1 a1 := (show ContDiff ℝ (1 + 1 : ℕ) a_c from ha_cd).deriv'
  have hR1_cd : ContDiff ℝ 2 R1 := (show ContDiff ℝ (2 + 1 : ℕ) R from hR_cd).deriv'
  have hR2_cd : ContDiff ℝ 1 R2 := (show ContDiff ℝ (1 + 1 : ℕ) R1 from hR1_cd).deriv'
  have ha0_hd : ∀ τ, HasDerivAt a0 (a1 τ) τ := fun τ => (ha_cd.differentiable (by decide) τ).hasDerivAt
  have ha1_hd : ∀ τ, HasDerivAt a1 (a2 τ) τ := fun τ => (ha1_cd.differentiable (by decide) τ).hasDerivAt
  have hR0_hd : ∀ τ, HasDerivAt R (R1 τ) τ := fun τ => (hR_cd.differentiable (by decide) τ).hasDerivAt
  have hR1_hd : ∀ τ, HasDerivAt R1 (R2 τ) τ := fun τ => (hR1_cd.differentiable (by decide) τ).hasDerivAt
  have hR2_hd : ∀ τ, HasDerivAt R2 (R3 τ) τ := fun τ => (hR2_cd.differentiable (by decide) τ).hasDerivAt
  have ha0_cont : Continuous a0 := ha_cd.continuous
  have ha1_cont : Continuous a1 := ha1_cd.continuous
  have ha2_cont : Continuous a2 := ha1_cd.continuous_deriv (le_refl 1)
  have hR0_cont : Continuous R := hR_cd.continuous
  have hR1_cont : Continuous R1 := hR1_cd.continuous
  have hR2_cont : Continuous R2 := hR2_cd.continuous
  have hR3_cont : Continuous R3 := hR2_cd.continuous_deriv (le_refl 1)
  -- Phase derivative and oscillatory factor
  let φ' : ℝ → ℝ := fun τ => y + R1 τ
  have hφ'_ge_y : ∀ τ, y ≤ φ' τ := fun τ => by
    have := hR1_nn τ; rw [← hR1_eq] at this; dsimp [φ']; linarith
  have hφ'_ge_y0 : ∀ τ, y₀ ≤ φ' τ := fun τ => hy.trans (hφ'_ge_y τ)
  have hφ'_pos : ∀ τ, 0 < φ' τ := fun τ => hy₀.trans_le (hφ'_ge_y0 τ)
  have hφ'_cont : Continuous φ' := continuous_const.add hR1_cont
  have hφ'_hd : ∀ τ, HasDerivAt φ' (R2 τ) τ := fun τ => (hR1_hd τ).const_add y
  let E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))
  have hE_norm : ∀ τ, ‖E τ‖ = 1 := fun τ => by
    dsimp [E]
    have e : Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)) =
        ((c * (y * τ + R τ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hE_cont : Continuous E := Complex.continuous_exp.comp
    (continuous_const.mul ((continuous_const.mul Complex.continuous_ofReal).add
      (Complex.continuous_ofReal.comp hR0_cont)))
  have hE_hd : ∀ τ, HasDerivAt E (Complex.I * (c : ℂ) * (φ' τ : ℂ) * E τ) τ := fun τ => by
    have hre : HasDerivAt (fun t : ℝ => y * t + R t) (φ' τ) τ :=
      ((((hasDerivAt_id τ).const_mul y).add (hR0_hd τ)).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)).congr_deriv (by simp [φ'])
    have h1 : HasDerivAt (fun t : ℝ => (y : ℂ) * (t : ℂ) + (R t : ℂ)) (φ' τ : ℂ) τ := by
      simpa using hre.ofReal_comp
    simpa [E, mul_comm (E τ)] using (h1.const_mul (Complex.I * (c : ℂ))).cexp
  -- Weighted bounds on `a_c^{(j)}`
  have hint_base := integrable_inv_one_add_abs_sq
  have hm_real : (2 : ℝ) ≤ (m : ℝ) - 3 / 2 := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have ha_inv2 : ∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_c τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := fun j hj τ => by
    have hbd := ha_bd j hj τ
    rw [show -(m : ℝ) - 1 / 2 = -((m : ℝ) + 1 / 2) by ring] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_left
      (rpow_neg_le_inv_sq (le_add_of_nonneg_right (abs_nonneg τ)) (by linarith)) hCa_nn)
  have h1_mul_a : ∀ j ≤ 2, ∀ τ, (1 + |τ|) * |iteratedDeriv j a_c τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ :=
    fun j hj τ => by
      have h1 : 1 ≤ 1 + |τ| := le_add_of_nonneg_right (abs_nonneg τ)
      have hpos : 0 < 1 + |τ| := by linarith
      have h_mul : (1 + |τ|) * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) = (1 + |τ|) ^ (-((m : ℝ) - 1 / 2)) := by
        conv_lhs => lhs; rw [← Real.rpow_one (1 + |τ|)]
        rw [← Real.rpow_add hpos]; ring_nf
      calc (1 + |τ|) * |iteratedDeriv j a_c τ|
          ≤ C_a * ((1 + |τ|) * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) := by
            linarith [mul_le_mul_of_nonneg_left (ha_bd j hj τ) hpos.le]
        _ = C_a * (1 + |τ|) ^ (-((m : ℝ) - 1 / 2)) := by rw [h_mul]
        _ ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left (rpow_neg_le_inv_sq h1 (by linarith)) hCa_nn
  have h2_mul_a0 : ∀ τ, (1 + |τ|) ^ 2 * |a0 τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := fun τ => by
    have h1 : 1 ≤ 1 + |τ| := le_add_of_nonneg_right (abs_nonneg τ)
    have hpos : 0 < 1 + |τ| := by linarith
    have h0 := ha_bd 0 (by omega) τ; simp only [iteratedDeriv_zero] at h0
    have h_mul : (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) = (1 + |τ|) ^ (-((m : ℝ) - 3 / 2)) := by
      rw [← Real.rpow_natCast (1 + |τ|) 2, ← Real.rpow_add hpos]; ring_nf
    calc (1 + |τ|) ^ 2 * |a0 τ|
        ≤ C_a * ((1 + |τ|) ^ 2 * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) :=
          (mul_le_mul_of_nonneg_left h0 (sq_nonneg _)).trans_eq (by ring)
      _ = C_a * (1 + |τ|) ^ (-((m : ℝ) - 3 / 2)) := by rw [h_mul]
      _ ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (rpow_neg_le_inv_sq h1 hm_real) hCa_nn
  have ha0_bd : ∀ τ, |a0 τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := fun τ => by
    simpa [a0, iteratedDeriv_zero] using ha_inv2 0 (by omega) τ
  have ha1_bd : ∀ τ, |a1 τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := fun τ => by
    simpa [ha1_eq] using ha_inv2 1 (by omega) τ
  -- Step 1: `b₁ = (a0 / φ')'`
  let b1 : ℝ → ℝ := fun τ => a1 τ / φ' τ - a0 τ * R2 τ / φ' τ ^ 2
  have hb1_cont : Continuous b1 :=
    (ha1_cont.div hφ'_cont (fun τ => (hφ'_pos τ).ne')).sub
      ((ha0_cont.mul hR2_cont).div (hφ'_cont.pow 2) (fun τ => pow_ne_zero 2 (hφ'_pos τ).ne'))
  have hb1_hd : ∀ τ, HasDerivAt (fun t => a0 t / φ' t) (b1 τ) τ := fun τ => by
    refine ((ha0_hd τ).div (hφ'_hd τ) (hφ'_pos τ).ne').congr_deriv ?_
    dsimp [b1]; have hne := (hφ'_pos τ).ne'; field_simp
  have hb1_bd : ∀ τ, |b1 τ| ≤ (C_a / y₀ + C_a * C₂ / y₀ ^ 2) * ((1 + |τ|) ^ 2)⁻¹ := fun τ => by
    have hφ1 : (φ' τ)⁻¹ ≤ y₀⁻¹ := inv_anti₀ hy₀ (hφ'_ge_y0 τ)
    have hφ2 : (φ' τ ^ 2)⁻¹ ≤ (y₀ ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hy₀) (pow_le_pow_left₀ hy₀.le (hφ'_ge_y0 τ) 2)
    have ht1 : |a1 τ / φ' τ| ≤ C_a / y₀ * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_of_pos (hφ'_pos τ), div_eq_mul_inv]
      exact (mul_le_mul (ha1_bd τ) hφ1 (inv_nonneg.mpr (hφ'_pos τ).le)
        (mul_nonneg hCa_nn (by positivity))).trans_eq (by ring)
    have ht2 : |a0 τ * R2 τ / φ' τ ^ 2| ≤ C_a * C₂ / y₀ ^ 2 * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos (hφ'_pos τ)), div_eq_mul_inv]
      have hR2' : |R2 τ| ≤ C₂ * (1 + |τ|) := by simpa [hR2_eq] using hR2_bd τ
      have h1a : (1 + |τ|) * |a0 τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := by
        simpa [iteratedDeriv_zero] using h1_mul_a 0 (by omega) τ
      have hnum : |a0 τ| * |R2 τ| ≤ C_a * C₂ * ((1 + |τ|) ^ 2)⁻¹ :=
        (mul_le_mul_of_nonneg_left hR2' (abs_nonneg _)).trans
          (by linarith [mul_le_mul_of_nonneg_left h1a hC₂_nn])
      exact (mul_le_mul hnum hφ2 (inv_nonneg.mpr (sq_nonneg _))
        (mul_nonneg (mul_nonneg hCa_nn hC₂_nn) (by positivity))).trans_eq (by ring)
    exact (abs_sub _ _).trans ((add_le_add ht1 ht2).trans_eq (by ring))
  have int_of_bd : ∀ {g : ℝ → ℝ} {B : ℝ}, Continuous g → (∀ τ, |g τ| ≤ B * ((1 + |τ|) ^ 2)⁻¹) →
      Integrable (fun τ : ℝ => (g τ : ℂ) * E τ) := fun {g B} hg_cont hg_bd => by
    refine (hint_base.const_mul B).mono'
      ((Complex.continuous_ofReal.comp hg_cont).mul hE_cont).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hE_norm, mul_one]
    exact hg_bd τ
  have ha0E_int := int_of_bd ha0_cont ha0_bd
  have hb1E_int := int_of_bd hb1_cont hb1_bd
  have hu1E_int := int_of_bd (ha0_cont.div hφ'_cont (fun τ => (hφ'_pos τ).ne')) (fun τ => by
    change |a0 τ / φ' τ| ≤ C_a / y₀ * ((1 + |τ|) ^ 2)⁻¹
    rw [abs_div, abs_of_pos (hφ'_pos τ), div_eq_mul_inv]
    exact (mul_le_mul (ha0_bd τ) (inv_anti₀ hy₀ (hφ'_ge_y0 τ))
      (inv_nonneg.mpr (hφ'_pos τ).le) (mul_nonneg hCa_nn (by positivity))).trans_eq (by ring))
  have hibp1 := pf3_ibp_step hc_pos hφ'_pos hE_hd hb1_hd ha0E_int hb1E_int hu1E_int
  -- Step 2: `b₂ = (b₁ / φ')'`
  let b2 : ℝ → ℝ := fun τ =>
    a2 τ / φ' τ ^ 2 - 3 * a1 τ * R2 τ / φ' τ ^ 3 - a0 τ * R3 τ / φ' τ ^ 3 +
      3 * a0 τ * R2 τ ^ 2 / φ' τ ^ 4
  have hb2_cont : Continuous b2 :=
    (((ha2_cont.div (hφ'_cont.pow 2) (fun τ => pow_ne_zero 2 (hφ'_pos τ).ne')).sub
      (((continuous_const.mul ha1_cont).mul hR2_cont).div (hφ'_cont.pow 3)
        (fun τ => pow_ne_zero 3 (hφ'_pos τ).ne'))).sub
      ((ha0_cont.mul hR3_cont).div (hφ'_cont.pow 3) (fun τ => pow_ne_zero 3 (hφ'_pos τ).ne'))).add
      (((continuous_const.mul ha0_cont).mul (hR2_cont.pow 2)).div (hφ'_cont.pow 4)
        (fun τ => pow_ne_zero 4 (hφ'_pos τ).ne'))
  have hb2_hd : ∀ τ, HasDerivAt (fun t => b1 t / φ' t) (b2 τ) τ := fun τ => by
    have h_eq : (fun t => b1 t / φ' t) = fun t => a1 t / φ' t ^ 2 - a0 t * R2 t / φ' t ^ 3 := by
      funext t; dsimp [b1]
      rw [sub_div, div_div, div_div, ← sq, show φ' t ^ 2 * φ' t = φ' t ^ 3 by ring]
    have hφ2_hd : HasDerivAt (fun t => φ' t ^ 2) (2 * φ' τ * R2 τ) τ :=
      (((hφ'_hd τ).pow 2).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv
        (by simp)
    have hφ3_hd : HasDerivAt (fun t => φ' t ^ 3) (3 * φ' τ ^ 2 * R2 τ) τ :=
      (((hφ'_hd τ).pow 3).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv
        (by simp)
    have ha0R2_hd : HasDerivAt (fun t => a0 t * R2 t) (a1 τ * R2 τ + a0 τ * R3 τ) τ :=
      ((ha0_hd τ).mul (hR2_hd τ)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    have hq1 := (ha1_hd τ).div hφ2_hd (pow_ne_zero 2 (hφ'_pos τ).ne')
    have hq2 := ha0R2_hd.div hφ3_hd (pow_ne_zero 3 (hφ'_pos τ).ne')
    rw [h_eq]
    refine ((hq1.sub hq2).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp [b2]
    have hpow : ∀ k : ℕ, φ' τ ^ k ≠ 0 := fun k => pow_ne_zero k (hφ'_pos τ).ne'
    have h2 : ∀ X : ℝ, X / φ' τ ^ 2 * φ' τ ^ 6 = X * φ' τ ^ 4 := fun X => by
      rw [show φ' τ ^ 6 = φ' τ ^ 2 * φ' τ ^ 4 by ring, ← mul_assoc, div_mul_cancel₀ _ (hpow 2)]
    have h3 : ∀ X : ℝ, X / φ' τ ^ 3 * φ' τ ^ 6 = X * φ' τ ^ 3 := fun X => by
      rw [show φ' τ ^ 6 = φ' τ ^ 3 * φ' τ ^ 3 by ring, ← mul_assoc, div_mul_cancel₀ _ (hpow 3)]
    have h4 : ∀ X : ℝ, X / φ' τ ^ 4 * φ' τ ^ 6 = X * φ' τ ^ 2 := fun X => by
      rw [show φ' τ ^ 6 = φ' τ ^ 4 * φ' τ ^ 2 by ring, ← mul_assoc, div_mul_cancel₀ _ (hpow 4)]
    have h22 : ∀ X : ℝ, X / (φ' τ ^ 2) ^ 2 * φ' τ ^ 6 = X * φ' τ ^ 2 := fun X => by
      rw [show (φ' τ ^ 2) ^ 2 = φ' τ ^ 4 by ring]; exact h4 X
    have h32 : ∀ X : ℝ, X / (φ' τ ^ 3) ^ 2 * φ' τ ^ 6 = X := fun X => by
      rw [show (φ' τ ^ 3) ^ 2 = φ' τ ^ 6 by ring, div_mul_cancel₀ _ (hpow 6)]
    apply mul_right_cancel₀ (hpow 6)
    simp only [sub_mul, add_mul, h2, h3, h4, h22, h32]
    ring
  let K2 : ℝ := C_a + 3 * C_a * C₂ / y₀ + C_a * C₃ / y₀ + 3 * C_a * C₂ ^ 2 / y₀ ^ 2
  have hb2_bd : ∀ τ, |b2 τ| ≤ K2 * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := fun τ => by
    have hy2_eq : (φ' τ ^ 2)⁻¹ ≤ y ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hy_pos.le, Real.rpow_natCast]
      exact inv_anti₀ (sq_pos_of_pos hy_pos) (pow_le_pow_left₀ hy_pos.le (hφ'_ge_y τ) 2)
    have hφ3_le : (φ' τ ^ 3)⁻¹ ≤ y₀⁻¹ * y ^ (-2 : ℝ) := by
      rw [show (φ' τ ^ 3)⁻¹ = (φ' τ)⁻¹ * (φ' τ ^ 2)⁻¹ by rw [← mul_inv, pow_succ']]
      exact mul_le_mul (inv_anti₀ hy₀ (hφ'_ge_y0 τ)) hy2_eq (by positivity) (by positivity)
    have hφ4_le : (φ' τ ^ 4)⁻¹ ≤ (y₀ ^ 2)⁻¹ * y ^ (-2 : ℝ) := by
      rw [show (φ' τ ^ 4)⁻¹ = (φ' τ ^ 2)⁻¹ * (φ' τ ^ 2)⁻¹ by rw [← mul_inv, ← pow_add]]
      exact mul_le_mul (inv_anti₀ (sq_pos_of_pos hy₀) (pow_le_pow_left₀ hy₀.le (hφ'_ge_y0 τ) 2))
        hy2_eq (by positivity) (by positivity)
    have ha2_bd : |a2 τ| ≤ C_a * ((1 + |τ|) ^ 2)⁻¹ := by simpa [ha2_eq] using ha_inv2 2 (by omega) τ
    have hR2' : |R2 τ| ≤ C₂ * (1 + |τ|) := by simpa [hR2_eq] using hR2_bd τ
    have hR3' : |R3 τ| ≤ C₃ := by simpa [hR3_eq] using hR3_bd τ
    have ht1 : |a2 τ / φ' τ ^ 2| ≤ C_a * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos (hφ'_pos τ)), div_eq_mul_inv]
      exact (mul_le_mul ha2_bd hy2_eq (by positivity) (by positivity)).trans_eq (by ring)
    have ht2 : |3 * a1 τ * R2 τ / φ' τ ^ 3| ≤ 3 * C_a * C₂ / y₀ * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
        abs_of_pos (pow_pos (hφ'_pos τ) 3), div_eq_mul_inv]
      have h1a := h1_mul_a 1 (by omega) τ; rw [← ha1_eq] at h1a
      have hnum : 3 * |a1 τ| * |R2 τ| ≤ 3 * C_a * C₂ * ((1 + |τ|) ^ 2)⁻¹ :=
        (mul_le_mul_of_nonneg_left hR2' (by positivity)).trans
          (by linarith [mul_le_mul_of_nonneg_left h1a (by positivity : (0 : ℝ) ≤ 3 * C₂)])
      exact (mul_le_mul hnum hφ3_le (inv_nonneg.mpr (pow_nonneg (hφ'_pos τ).le 3))
        (by positivity)).trans_eq (by ring)
    have ht3 : |a0 τ * R3 τ / φ' τ ^ 3| ≤ C_a * C₃ / y₀ * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_mul, abs_of_pos (pow_pos (hφ'_pos τ) 3), div_eq_mul_inv]
      have hnum : |a0 τ| * |R3 τ| ≤ C_a * C₃ * ((1 + |τ|) ^ 2)⁻¹ :=
        (mul_le_mul (ha0_bd τ) hR3' (abs_nonneg _) (by positivity)).trans_eq (by ring)
      exact (mul_le_mul hnum hφ3_le (inv_nonneg.mpr (pow_nonneg (hφ'_pos τ).le 3))
        (by positivity)).trans_eq (by ring)
    have ht4 : |3 * a0 τ * R2 τ ^ 2 / φ' τ ^ 4| ≤
        3 * C_a * C₂ ^ 2 / y₀ ^ 2 * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow,
        abs_of_pos (pow_pos (hφ'_pos τ) 4), div_eq_mul_inv]
      have hR2_sq : |R2 τ| ^ 2 ≤ C₂ ^ 2 * (1 + |τ|) ^ 2 :=
        (pow_le_pow_left₀ (abs_nonneg _) hR2' 2).trans_eq (by ring)
      have hnum : 3 * |a0 τ| * |R2 τ| ^ 2 ≤ 3 * C_a * C₂ ^ 2 * ((1 + |τ|) ^ 2)⁻¹ :=
        (mul_le_mul_of_nonneg_left hR2_sq (by positivity)).trans
          (by linarith [mul_le_mul_of_nonneg_left (h2_mul_a0 τ) (by positivity : (0 : ℝ) ≤ 3 * C₂ ^ 2)])
      exact (mul_le_mul hnum hφ4_le (by positivity) (by positivity)).trans_eq (by ring)
    have htri : |b2 τ| ≤ |a2 τ / φ' τ ^ 2| + |3 * a1 τ * R2 τ / φ' τ ^ 3| +
        |a0 τ * R3 τ / φ' τ ^ 3| + |3 * a0 τ * R2 τ ^ 2 / φ' τ ^ 4| := by
      dsimp [b2]
      calc _ ≤ |a2 τ / φ' τ ^ 2 - 3 * a1 τ * R2 τ / φ' τ ^ 3 - a0 τ * R3 τ / φ' τ ^ 3| +
              |3 * a0 τ * R2 τ ^ 2 / φ' τ ^ 4| := abs_add_le _ _
        _ ≤ _ := by gcongr; exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    exact htri.trans ((add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4).trans_eq
      (by dsimp [K2]; ring))
  have hb2E_int := int_of_bd hb2_cont hb2_bd
  have hu2E_int := int_of_bd (hb1_cont.div hφ'_cont (fun τ => (hφ'_pos τ).ne')) (fun τ => by
    change |b1 τ / φ' τ| ≤ y₀⁻¹ * (C_a / y₀ + C_a * C₂ / y₀ ^ 2) * ((1 + |τ|) ^ 2)⁻¹
    rw [abs_div, abs_of_pos (hφ'_pos τ), div_eq_mul_inv, mul_comm (|b1 τ|)]
    exact (mul_le_mul (inv_anti₀ hy₀ (hφ'_ge_y0 τ)) (hb1_bd τ) (abs_nonneg _) (by positivity)).trans_eq
      (by ring))
  have hibp2 := pf3_ibp_step hc_pos hφ'_pos hE_hd hb2_hd hb1E_int hb2E_int hu2E_int
  have hcomb : ∫ τ : ℝ, (a0 τ : ℂ) * E τ =
      (-(Complex.I * (c : ℂ))⁻¹) ^ 2 * ∫ τ : ℝ, (b2 τ : ℂ) * E τ := by
    rw [hibp1, hibp2]; ring
  change ‖∫ τ : ℝ, (a0 τ : ℂ) * E τ‖ ≤ _
  rw [hcomb, norm_mul, norm_pow, norm_neg, norm_inv, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
  have hc2 : (c⁻¹) ^ 2 = c ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hc_pos.le, Real.rpow_natCast, ← inv_pow]
  have hint_norm : ‖∫ τ : ℝ, (b2 τ : ℂ) * E τ‖ ≤ pf3Const C_a C₂ C₃ y₀ * y ^ (-2 : ℝ) := by
    calc ‖∫ τ : ℝ, (b2 τ : ℂ) * E τ‖ ≤ ∫ τ : ℝ, ‖(b2 τ : ℂ) * E τ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ τ : ℝ, K2 * y ^ (-2 : ℝ) * ((1 + |τ|) ^ 2)⁻¹ := by
          refine integral_mono hb2E_int.norm (hint_base.const_mul _) fun τ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hE_norm, mul_one]; exact hb2_bd τ
      _ = pf3Const C_a C₂ C₃ y₀ * y ^ (-2 : ℝ) := by
          rw [integral_const_mul, integral_one_add_abs_inv_sq]; dsimp [K2, pf3Const]; ring
  calc (c⁻¹) ^ 2 * ‖∫ τ : ℝ, (b2 τ : ℂ) * E τ‖
      ≤ c ^ (-2 : ℝ) * (pf3Const C_a C₂ C₃ y₀ * y ^ (-2 : ℝ)) := by
        rw [hc2]; exact mul_le_mul_of_nonneg_left hint_norm (by positivity)
    _ = pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by ring

/-- Family-uniform phrasing of Lemma `PF.3`: the constant `C` depends only on `m, C_a, C₂, C₃, y₀`
and not on `c, y, a_c, R`. -/
theorem pf3_kernel_bound_uniform (m : ℕ) (hm : 4 ≤ m) (C_a C₂ C₃ y₀ : ℝ)
    (hCa : 0 ≤ C_a) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hy₀ : 0 < y₀) :
    ∃ C ≥ 0, ∀ {a_c R : ℝ → ℝ} {c y : ℝ}, 2 ≤ c → y₀ ≤ y →
      ContDiff ℝ 2 a_c → ContDiff ℝ 3 R →
      (∀ τ, 0 ≤ iteratedDeriv 1 R τ) →
      (∀ τ, |iteratedDeriv 2 R τ| ≤ C₂ * (1 + |τ|)) →
      (∀ τ, |iteratedDeriv 3 R τ| ≤ C₃) →
      (∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_c τ| ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) →
      ‖∫ τ : ℝ, (a_c τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))‖ ≤
        C * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) :=
  ⟨pf3Const C_a C₂ C₃ y₀, by unfold pf3Const; positivity,
    fun hc hy ha_cd hR_cd hR1 hR2 hR3 ha_bd =>
      pf3_kernel_bound hm hc hy₀ ha_cd hR_cd hR1 hR2 hR3 ha_bd hy⟩

/-- Explicit non-vacuity witness for Lemma `PF.3`: `a_c(τ) = (1 + τ²)⁻³`, `R(τ) = 0`,
`m = 4`, `C_a = 336`, `C₂ = 0`, `C₃ = 0`, `y₀ = 1`. -/
theorem pf3_kernel_bound_nonvacuous :
    let a_c : ℝ → ℝ := fun τ => (1 + τ ^ 2) ^ (-3 : ℝ)
    let R : ℝ → ℝ := fun _ => 0
    ContDiff ℝ 2 a_c ∧ ContDiff ℝ 3 R ∧
      (∀ τ, 0 ≤ iteratedDeriv 1 R τ) ∧
      (∀ τ, |iteratedDeriv 2 R τ| ≤ 0 * (1 + |τ|)) ∧
      (∀ τ, |iteratedDeriv 3 R τ| ≤ 0) ∧
      (∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_c τ| ≤ 336 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2)) ∧
      ∀ {c y : ℝ}, 2 ≤ c → 1 ≤ y →
        ‖∫ τ : ℝ, (a_c τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))‖ ≤
          pf3Const 336 0 0 1 * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by
  let a_c : ℝ → ℝ := fun τ => (1 + τ ^ 2) ^ (-3 : ℝ)
  let R : ℝ → ℝ := fun _ => 0
  have ha_eq : a_c = fun τ => ((1 + τ ^ 2) ^ 3)⁻¹ := by
    funext τ; dsimp [a_c]
    rw [show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have ha_cd : ContDiff ℝ 2 a_c := by
    rw [ha_eq]
    fun_prop (disch := intro τ; positivity)
  have hR_cd : ContDiff ℝ 3 R := contDiff_const
  have hR1 : ∀ τ, 0 ≤ iteratedDeriv 1 R τ := fun τ => by simp [R]
  have hR2 : ∀ τ, |iteratedDeriv 2 R τ| ≤ 0 * (1 + |τ|) := fun τ => by simp [R]
  have hR3 : ∀ τ, |iteratedDeriv 3 R τ| ≤ 0 := fun τ => by simp [R]
  have ha_deriv1 : ∀ τ, deriv a_c τ = -6 * τ / (1 + τ ^ 2) ^ 4 := fun τ => by
    have h1 : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ 3) (3 * (1 + τ ^ 2) ^ 2 * (2 * τ)) τ :=
      (((hasDerivAt_const τ 1).add (hasDerivAt_pow 2 τ)).pow 3).congr_deriv (by simp)
    have h2 : HasDerivAt a_c (-(3 * (1 + τ ^ 2) ^ 2 * (2 * τ)) / ((1 + τ ^ 2) ^ 3) ^ 2) τ := by
      rw [ha_eq]; exact h1.inv (by positivity)
    rw [h2.deriv]; have hne : 1 + τ ^ 2 ≠ 0 := by positivity
    field_simp; ring
  have ha_deriv2 : ∀ τ, deriv (deriv a_c) τ = (42 * τ ^ 2 - 6) / (1 + τ ^ 2) ^ 5 := fun τ => by
    rw [show deriv a_c = fun t => -6 * t / (1 + t ^ 2) ^ 4 from funext ha_deriv1]
    have hnum : HasDerivAt (fun t : ℝ => -6 * t) (-6) τ := by simpa using (hasDerivAt_id τ).const_mul (-6)
    have hden : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ 4) (4 * (1 + τ ^ 2) ^ 3 * (2 * τ)) τ :=
      (((hasDerivAt_const τ 1).add (hasDerivAt_pow 2 τ)).pow 4).congr_deriv (by simp)
    have hq : HasDerivAt (fun t : ℝ => -6 * t / (1 + t ^ 2) ^ 4)
        ((-6 * (1 + τ ^ 2) ^ 4 - -6 * τ * (4 * (1 + τ ^ 2) ^ 3 * (2 * τ))) / ((1 + τ ^ 2) ^ 4) ^ 2) τ :=
      hnum.div hden (by positivity)
    rw [hq.deriv]; have hne : 1 + τ ^ 2 ≠ 0 := by positivity
    field_simp; ring
  have hpoly_cmp : ∀ τ : ℝ, ((1 + τ ^ 2) ^ 3)⁻¹ ≤ 8 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := fun τ => by
    have h1 : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by
      have h2abs : 2 * |τ| ≤ 1 + τ ^ 2 := by nlinarith [sq_nonneg (|τ| - 1), sq_abs τ]
      calc (1 + |τ|) ^ 2 = 1 + 2 * |τ| + τ ^ 2 := by rw [add_sq]; ring_nf; rw [sq_abs]
        _ ≤ 2 * (1 + τ ^ 2) := by linarith
    have hcube : (1 + |τ|) ^ 6 ≤ 8 * (1 + τ ^ 2) ^ 3 := by
      calc (1 + |τ|) ^ 6 = ((1 + |τ|) ^ 2) ^ 3 := by ring
        _ ≤ (2 * (1 + τ ^ 2)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
        _ = 8 * (1 + τ ^ 2) ^ 3 := by ring
    have hinv : ((1 + τ ^ 2) ^ 3)⁻¹ ≤ 8 * ((1 + |τ|) ^ 6)⁻¹ := by
      have hle := inv_anti₀ (by positivity : 0 < (1 + |τ|) ^ 6) hcube
      have heq : ((1 + τ ^ 2) ^ 3)⁻¹ = 8 * (8 * (1 + τ ^ 2) ^ 3)⁻¹ := by field_simp
      rw [heq]; exact mul_le_mul_of_nonneg_left hle (by norm_num)
    have hrpow : ((1 + |τ|) ^ 6)⁻¹ ≤ (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := by
      have hpos : 0 < 1 + |τ| := by positivity
      rw [← Real.rpow_natCast (1 + |τ|) 6, ← Real.rpow_neg hpos.le]
      exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (abs_nonneg τ)) (by norm_num)
    exact hinv.trans (mul_le_mul_of_nonneg_left hrpow (by norm_num))
  have ha_bd : ∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_c τ| ≤ 336 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := by
    intro j hj τ
    have hbase := hpoly_cmp τ
    have hpos : 0 < 1 + τ ^ 2 := by positivity
    have h1ge : 1 ≤ 1 + τ ^ 2 := le_add_of_nonneg_right (sq_nonneg τ)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [iteratedDeriv_zero, ha_eq, abs_of_pos (by positivity)]
      exact hbase.trans (by linarith [Real.rpow_nonneg (by positivity : 0 ≤ 1 + |τ|) (-(4 : ℝ) - 1 / 2)])
    · rw [iteratedDeriv_one, ha_deriv1, abs_div, abs_mul, show |(-6 : ℝ)| = 6 by norm_num,
        abs_of_pos (pow_pos hpos 4)]
      have hτ_le : |τ| ≤ 1 + τ ^ 2 := by nlinarith [sq_nonneg (|τ| - 1 / 2), sq_abs τ]
      have hnum : 6 * |τ| ≤ 6 * (1 + τ ^ 2) := by linarith
      have h4 : 6 * (1 + τ ^ 2) / (1 + τ ^ 2) ^ 4 = 6 * ((1 + τ ^ 2) ^ 3)⁻¹ := by
        have hne := hpos.ne'; field_simp
      calc 6 * |τ| / (1 + τ ^ 2) ^ 4 ≤ 6 * ((1 + τ ^ 2) ^ 3)⁻¹ :=
            (div_le_div_of_nonneg_right hnum (pow_nonneg hpos.le 4)).trans_eq h4
        _ ≤ 6 * (8 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2)) := by gcongr
        _ = 48 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := by ring
        _ ≤ 336 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := by gcongr; norm_num
    · rw [iteratedDeriv_succ, iteratedDeriv_one, ha_deriv2, abs_div, abs_of_pos (pow_pos hpos 5)]
      have hnum : |42 * τ ^ 2 - 6| ≤ 42 * (1 + τ ^ 2) := by
        calc |42 * τ ^ 2 - 6| ≤ |42 * τ ^ 2| + |6| := abs_sub _ _
          _ = 42 * τ ^ 2 + 6 := by rw [abs_of_nonneg (by positivity), abs_of_pos (by norm_num)]
          _ ≤ 42 * (1 + τ ^ 2) := by linarith
      have h4 : 42 * (1 + τ ^ 2) / (1 + τ ^ 2) ^ 5 = 42 * ((1 + τ ^ 2) ^ 4)⁻¹ := by
        have hne := hpos.ne'; field_simp
      have h34 : ((1 + τ ^ 2) ^ 4)⁻¹ ≤ ((1 + τ ^ 2) ^ 3)⁻¹ :=
        inv_anti₀ (pow_pos hpos 3) (pow_le_pow_right₀ h1ge (by decide : 3 ≤ 4))
      calc |42 * τ ^ 2 - 6| / (1 + τ ^ 2) ^ 5 ≤ 42 * ((1 + τ ^ 2) ^ 4)⁻¹ :=
            (div_le_div_of_nonneg_right hnum (pow_nonneg hpos.le 5)).trans_eq h4
        _ ≤ 42 * ((1 + τ ^ 2) ^ 3)⁻¹ := by gcongr
        _ ≤ 42 * (8 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2)) := by gcongr
        _ = 336 * (1 + |τ|) ^ (-(4 : ℝ) - 1 / 2) := by ring
  exact ⟨ha_cd, hR_cd, hR1, hR2, hR3, ha_bd, fun hc hy =>
    pf3_kernel_bound (m := 4) (by omega) hc zero_lt_one ha_cd hR_cd hR1 hR2 hR3 ha_bd hy⟩

/-! ### Part 3: Theorem PF.5 worst-phase margin (`ce_physical_log_far.tex` `(cepf:PF.5.4)`–`(cepf:PF5a)`) -/

/-- The fractional cutoff `φ_p(t) = (1 + t^p)⁻¹` (`ceo:O11h`, `(cepf:PF.5.4)`). -/
noncomputable def ceVarphiP (p t : ℝ) : ℝ := (1 + t ^ p)⁻¹

/-- **Worst-phase algebraic margin (`(cepf:PF.5.4)`):**
for `0 < φ ≤ 1`, `0 ≤ θ ≤ 1`, and `0 < A < 1`,
`0 < (1 - φ)² + (1 - A) φ ≤ 2 - θ(1 - φ²) - (1 + A) φ`. -/
theorem pf5_worst_phase_margin {φ θ 𝒜 : ℝ} (hφ0 : 0 < φ) (hφ1 : φ ≤ 1)
    (_hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (_h𝒜0 : 0 < 𝒜) (h𝒜1 : 𝒜 < 1) :
    0 < (1 - φ) ^ 2 + (1 - 𝒜) * φ ∧
      (1 - φ) ^ 2 + (1 - 𝒜) * φ ≤ 2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ := by
  have h1 : 0 < (1 - 𝒜) * φ := mul_pos (sub_pos.mpr h𝒜1) hφ0
  have hdiff : (2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ) - ((1 - φ) ^ 2 + (1 - 𝒜) * φ) =
      (1 - θ) * (1 - φ ^ 2) := by ring
  have hnn : 0 ≤ (1 - θ) * (1 - φ ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hθ1) (by nlinarith [sq_nonneg φ])
  exact ⟨add_pos_of_nonneg_of_pos (sq_nonneg _) h1, by linarith⟩

/-- **Interval margin on `J = [L₀, L₁]` (`(cepf:PF.5.4)`–`(cepf:PF5a)`):**
with `m_J = (1 - φ_p(λ L₀ / c_s))²` and `b_J = k / (π c_s (L₁ / c_s)^{3/2})`,
`0 < b_J m_J` bounds the leading coherent-vs-smooth margin everywhere on `J`. -/
theorem pf5_interval_margin {p lam L₀ L₁ θ 𝒜 L : ℝ} (hp : 0 < p) (hlam : 0 < lam)
    (hL₀ : 0 < L₀) (hJ : L ∈ Icc L₀ L₁) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h𝒜0 : 0 < 𝒜) (h𝒜1 : 𝒜 < 1) :
    let φ := ceVarphiP p (lam * (L / ceCs))
    let mJ := (1 - ceVarphiP p (lam * (L₀ / ceCs))) ^ 2
    let bJ := ceK / (π * ceCs * (L₁ / ceCs) ^ (3 / 2 : ℝ))
    0 < bJ * mJ ∧
      bJ * mJ < ceK / (π * ceCs * (L / ceCs) ^ (3 / 2 : ℝ)) *
        (2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ) := by
  intro φ mJ bJ
  have hcs : 0 < ceCs := ceCs_pos
  have hL : 0 < L := lt_of_lt_of_le hL₀ hJ.1
  have hL₁ : 0 < L₁ := lt_of_lt_of_le hL hJ.2
  have ht0_pos : 0 < lam * (L₀ / ceCs) := by positivity
  have hrpow_le : (lam * (L₀ / ceCs)) ^ p ≤ (lam * (L / ceCs)) ^ p :=
    Real.rpow_le_rpow ht0_pos.le (by gcongr; exact hJ.1) hp.le
  have hφ0_lt : ceVarphiP p (lam * (L₀ / ceCs)) < 1 := by
    unfold ceVarphiP; rw [inv_lt_one_iff₀]; right; linarith [Real.rpow_pos_of_pos ht0_pos p]
  have hφ_pos : 0 < φ := by dsimp [φ]; unfold ceVarphiP; exact inv_pos.mpr (by positivity)
  have hφ_le_φ0 : φ ≤ ceVarphiP p (lam * (L₀ / ceCs)) := by
    dsimp [φ]; unfold ceVarphiP; exact inv_anti₀ (by positivity) (by linarith)
  have hφ_lt : φ < 1 := hφ_le_φ0.trans_lt hφ0_lt
  have hmJ_pos : 0 < mJ := sq_pos_of_pos (sub_pos.mpr hφ0_lt)
  have hbJ_pos : 0 < bJ :=
    div_pos ceK_pos (mul_pos (mul_pos Real.pi_pos hcs) (Real.rpow_pos_of_pos (div_pos hL₁ hcs) _))
  have hm_le : mJ ≤ (1 - φ) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hφ0_lt.le) (by linarith) 2
  have hmargin := pf5_worst_phase_margin hφ_pos hφ_lt.le hθ0 hθ1 h𝒜0 h𝒜1
  have hm_lt : mJ < 2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ := by
    have h1𝒜 : 0 < (1 - 𝒜) * φ := mul_pos (sub_pos.mpr h𝒜1) hφ_pos
    linarith [hm_le, hmargin.2]
  have hb_le : bJ ≤ ceK / (π * ceCs * (L / ceCs) ^ (3 / 2 : ℝ)) := by
    dsimp [bJ]
    have hdiv_le : (L / ceCs) ^ (3 / 2 : ℝ) ≤ (L₁ / ceCs) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (div_pos hL hcs).le (div_le_div_of_nonneg_right hJ.2 hcs.le) (by norm_num)
    exact div_le_div_of_nonneg_left ceK_pos.le (by positivity) (by gcongr)
  refine ⟨mul_pos hbJ_pos hmJ_pos, ?_⟩
  calc bJ * mJ < bJ * (2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ) := mul_lt_mul_of_pos_left hm_lt hbJ_pos
    _ ≤ ceK / (π * ceCs * (L / ceCs) ^ (3 / 2 : ℝ)) * (2 - θ * (1 - φ ^ 2) - (1 + 𝒜) * φ) :=
        mul_le_mul_of_nonneg_right hb_le (by linarith [hmJ_pos, hm_lt])

/-- Coupled form of Theorem `PF.5` margin with the contraction `A(x)` of Lemma `O.11aw`
(`(cepf:PF.5.3)`–`(cepf:PF5a)`). -/
theorem pf5_interval_margin_contraction {p lam L₀ L₁ θ L x : ℝ}
    (hp : 0 < p) (hlam : 0 < lam) (hL₀ : 0 < L₀) (hJ : L ∈ Icc L₀ L₁)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 < x) :
    let φ := ceVarphiP p (lam * (L / ceCs))
    let mJ := (1 - ceVarphiP p (lam * (L₀ / ceCs))) ^ 2
    let bJ := ceK / (π * ceCs * (L₁ / ceCs) ^ (3 / 2 : ℝ))
    0 < bJ * mJ ∧
      bJ * mJ < ceK / (π * ceCs * (L / ceCs) ^ (3 / 2 : ℝ)) *
        (2 - θ * (1 - φ ^ 2) - (1 + ceTransportRatio x) * φ) :=
  let hA := ceTransportRatio_pos_and_lt_one hx
  pf5_interval_margin hp hlam hL₀ hJ hθ0 hθ1 hA.1 hA.2

/-! ### Part 4: Exact infinite Airy-cardinal identity (`ce_o1_route.tex` Lemma O.11f) -/

/-- The cardinal limit function `H_*(u) = Ai'(u) / (u - a)` with its removable value
`a Ai(a)` at `u = a` (`ceo:O11f`). -/
noncomputable def cardinalHstar (a u : ℝ) : ℝ := dslope airyAi' a u

/-- Complex cardinal function `L_n(z) = Ai(z)/(z - a_n)` extended across `z = a_n`. -/
noncomputable def cohnLC (n : ℕ) (z : ℂ) : ℂ :=
  dslope airyAiC (airyZero (n + 1) : ℂ) z

/-- Complex `H_*(z) = Ai'(z)/(z - a)` extended across `z = a`. -/
noncomputable def cardinalHstarC (a : ℝ) (z : ℂ) : ℂ :=
  dslope (deriv airyAiC) (a : ℂ) z

lemma cardinalHstar_of_ne {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) :
    cardinalHstar a u = airyAi' u / (u - a) := by
  unfold cardinalHstar; rw [dslope_of_ne _ hua, slope_def_field, ha, sub_zero]

lemma cardinalHstar_self (a : ℝ) : cardinalHstar a a = a * airyAi a := by
  unfold cardinalHstar; rw [dslope_same, (hasDerivAt_airyAi' a).deriv]

lemma cohnLC_ofReal (n : ℕ) (u : ℝ) : cohnLC n (u : ℂ) = (cohnL n u : ℂ) := by
  unfold cohnLC
  by_cases hu : u = airyZero (n + 1)
  · subst hu; rw [dslope_same, deriv_airyAiC_ofReal, cohnL_self]
  · have huc : (u : ℂ) ≠ (airyZero (n + 1) : ℂ) := fun h => hu (Complex.ofReal_injective h)
    rw [dslope_of_ne _ huc, slope_def_field, airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero,
      Complex.ofReal_zero, sub_zero, airyAiC_ofReal, cohnL_of_ne hu]
    push_cast; rfl

lemma cardinalHstarC_ofReal {a : ℝ} (ha : airyAi' a = 0) (u : ℝ) :
    cardinalHstarC a (u : ℂ) = (cardinalHstar a u : ℂ) := by
  unfold cardinalHstarC
  rcases eq_or_ne u a with rfl | hu
  · rw [dslope_same, (hasDerivAt_deriv_airyAiC (u : ℂ)).deriv, airyAiC_ofReal, cardinalHstar_self]
    push_cast; rfl
  · have huc : (u : ℂ) ≠ (a : ℂ) := fun h => hu (Complex.ofReal_injective h)
    have haC : deriv airyAiC (a : ℂ) = 0 := by rw [deriv_airyAiC_ofReal, ha]; simp
    rw [dslope_of_ne _ huc, slope_def_field, haC, sub_zero, deriv_airyAiC_ofReal, cardinalHstar_of_ne ha hu]
    push_cast; rfl

/-- Complex pointwise `HasSum` on all of `ℂ` (`(ceo:O11f.1)`). -/
theorem cardinal_HstarC_hasSum {a : ℝ} (ha : airyAi' a = 0) (z : ℂ) :
    HasSum (fun n : ℕ => (cohnC a n : ℂ) * cohnLC n z) (cardinalHstarC a z) := by
  have hAa : airyAi a ≠ 0 := airyAi_ne_zero_of_deriv_zero ha
  have hAaC : airyAiC (a : ℂ) ≠ 0 := by rw [airyAiC_ofReal]; exact_mod_cast hAa
  have haC : deriv airyAiC (a : ℂ) = 0 := by rw [deriv_airyAiC_ofReal, ha]; simp
  by_cases hza : z = (a : ℂ)
  · rw [hza]
    have hsq := airyAiC_logDeriv_sq_series hAaC
    rw [haC, zero_div, zero_pow two_ne_zero, zero_sub] at hsq
    have hmul := hsq.mul_left (-airyAiC (a : ℂ))
    rw [mul_neg, neg_mul, neg_neg, mul_comm (airyAiC (a : ℂ)) (a : ℂ)] at hmul
    have hval : (a : ℂ) * airyAiC (a : ℂ) = cardinalHstarC a (a : ℂ) := by
      unfold cardinalHstarC; rw [dslope_same, (hasDerivAt_deriv_airyAiC (a : ℂ)).deriv]
    rw [hval] at hmul
    refine hmul.congr_fun fun n => ?_
    have hne : (a : ℂ) ≠ (airyZero (n + 1) : ℂ) := fun h =>
      hAaC (h ▸ by rw [airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero, Complex.ofReal_zero])
    rw [cohnC, cohnLC, dslope_of_ne _ hne, slope_def_field, airyAiC_ofReal (airyZero (n + 1)),
      airyAi_airyZero, Complex.ofReal_zero, sub_zero]
    have he : ((airyZero (n + 1) - a : ℝ) : ℂ) = -((a : ℂ) - (airyZero (n + 1) : ℂ)) := by
      push_cast; ring
    have hne1 : (a : ℂ) - (airyZero (n + 1) : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    rw [Complex.ofReal_inv, he]; field_simp
  · by_cases hzAi : airyAiC z = 0
    · obtain ⟨k, hk, hkz⟩ := (airyAiC_eq_zero_iff z).mp hzAi
      obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, k = n0 + 1 := ⟨k - 1, by omega⟩
      have hsingle := hasSum_single (f := fun n : ℕ => (cohnC a n : ℂ) * cohnLC n z) n0
        (fun n hn => by
          have hne : z ≠ (airyZero (n + 1) : ℂ) := fun h => hn <| by
            have h1 : airyZero (n + 1) = airyZero (n0 + 1) := Complex.ofReal_injective (h.symm.trans hkz)
            exact airyZ_injective h1
          rw [cohnLC, dslope_of_ne _ hne, slope_def_field,
            airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero, Complex.ofReal_zero, hzAi, sub_zero,
            zero_div, mul_zero])
      convert hsingle using 1
      have hL : cohnLC n0 z = deriv airyAiC (airyZero (n0 + 1) : ℂ) := by rw [hkz, cohnLC, dslope_same]
      have hH : cardinalHstarC a z = deriv airyAiC z / (z - (a : ℂ)) := by
        unfold cardinalHstarC; rw [dslope_of_ne _ hza, slope_def_field, haC, sub_zero]
      rw [hL, hH, hkz, cohnC]
      have hne' : (airyZero (n0 + 1) : ℂ) - (a : ℂ) ≠ 0 := by rw [← hkz]; exact sub_ne_zero.mpr hza
      push_cast; field_simp
    · have hml := (airyAiC_logDeriv_mittagLeffler hzAi).sub (airyAiC_logDeriv_mittagLeffler hAaC)
      have hmul := hml.mul_left (airyAiC z / (z - (a : ℂ)))
      have hval : airyAiC z / (z - (a : ℂ)) *
          ((deriv airyAiC z / airyAiC z - deriv airyAiC 0 / airyAiC 0) -
            (deriv airyAiC (a : ℂ) / airyAiC (a : ℂ) - deriv airyAiC 0 / airyAiC 0)) =
          cardinalHstarC a z := by
        unfold cardinalHstarC
        rw [dslope_of_ne _ hza, slope_def_field, haC, zero_div, sub_sub_sub_cancel_right, sub_zero]
        field_simp [hzAi]; ring
      rw [hval] at hmul
      refine hmul.congr_fun fun n => ?_
      have hne1 : z ≠ (airyZero (n + 1) : ℂ) := fun h =>
        hzAi (h ▸ by rw [airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero, Complex.ofReal_zero])
      have hne2 : (a : ℂ) ≠ (airyZero (n + 1) : ℂ) := fun h =>
        hAaC (h ▸ by rw [airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero, Complex.ofReal_zero])
      have h1 : z - (airyZero (n + 1) : ℂ) ≠ 0 := sub_ne_zero.mpr hne1
      have h2 : (a : ℂ) - (airyZero (n + 1) : ℂ) ≠ 0 := sub_ne_zero.mpr hne2
      have h3 : z - (a : ℂ) ≠ 0 := sub_ne_zero.mpr hza
      have h4 : (airyZero (n + 1) : ℂ) - (a : ℂ) ≠ 0 := sub_ne_zero.mpr hne2.symm
      rw [cohnC, cohnLC, dslope_of_ne _ hne1, slope_def_field, airyAiC_ofReal (airyZero (n + 1)),
        airyAi_airyZero, Complex.ofReal_zero, sub_zero]
      push_cast; field_simp; ring

/-- **Lemma O.11f (`(ceo:O11f.1)`), pointwise `HasSum` on `ℝ`:**
for any real zero `a` of `Ai'` and every `u : ℝ` (including `u = a` and all Airy zeros `a_n`),
`∑_{n ≥ 1} c_n L_n(u) = H_*(u)`. -/
theorem cardinal_Hstar_hasSum {a : ℝ} (ha : airyAi' a = 0) (u : ℝ) :
    HasSum (fun n : ℕ => cohnC a n * cohnL n u) (cardinalHstar a u) := by
  rw [← Complex.hasSum_ofReal]
  have hC := cardinal_HstarC_hasSum ha (u : ℂ)
  rw [cardinalHstarC_ofReal ha u] at hC
  refine hC.congr_fun fun n => ?_
  simp [cohnLC_ofReal]

/-- Pointwise `HasSum` away from `a` and the Airy zeros `a_n`, written directly with
`(airyZero (n + 1) - a)⁻¹ * (airyAi u / (u - airyZero (n + 1)))`. -/
theorem cardinal_Hstar_hasSum_of_ne {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) (huAi : airyAi u ≠ 0) :
    HasSum (fun n : ℕ => (airyZero (n + 1) - a)⁻¹ * (airyAi u / (u - airyZero (n + 1))))
      (airyAi' u / (u - a)) := by
  have h := cardinal_Hstar_hasSum ha u
  rw [cardinalHstar_of_ne ha hua] at h
  exact h.congr_fun fun n => by
    rw [cohnC, cohnL_of_ne (fun h0 : u = airyZero (n + 1) => huAi (by rw [h0, airyAi_airyZero]))]

/-- Pointwise `HasSum` at the removable pole `u = a`, equal to `a * airyAi a`. -/
theorem cardinal_Hstar_hasSum_self {a : ℝ} (ha : airyAi' a = 0) :
    HasSum (fun n : ℕ => (airyZero (n + 1) - a)⁻¹ * (airyAi a / (a - airyZero (n + 1))))
      (a * airyAi a) := by
  have hAa := airyAi_ne_zero_of_deriv_zero ha
  have h := cardinal_Hstar_hasSum ha a
  rw [cardinalHstar_self] at h
  exact h.congr_fun fun n => by
    rw [cohnC, cohnL_of_ne (fun h0 : a = airyZero (n + 1) => hAa (by rw [h0, airyAi_airyZero]))]

/-- Lemma `O.11f` instantiated at `a₁' = airyDerivFirstZero`. -/
theorem cardinal_Hstar_hasSum_firstDerivZero (u : ℝ) :
    HasSum (fun n : ℕ => cohnC airyDerivFirstZero n * cohnL n u)
      (cardinalHstar airyDerivFirstZero u) :=
  cardinal_Hstar_hasSum airyDerivFirstZero_spec.2.2 u

/-- Locally uniform convergence of `∑_{n ≥ 1} c_n L_n(z)` to `H_*(z)` on `ℂ` (`ceo:O11f`). -/
theorem cardinal_HstarC_tendstoLocallyUniformly {a : ℝ} (ha : airyAi' a = 0) :
    TendstoLocallyUniformly
      (fun N z => ∑ n ∈ Finset.range N, (cohnC a n : ℂ) * cohnLC n z)
      (cardinalHstarC a) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [tendstoUniformlyOn_empty]
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn differentiable_airyAiC.continuous.continuousOn
  obtain ⟨z0, hz0⟩ := hKne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z0 hz0)
  have htsum : (fun z => ∑' n, (cohnC a n : ℂ) * cohnLC n z) = cardinalHstarC a :=
    funext fun z => (cardinal_HstarC_hasSum ha z).tsum_eq
  rw [← htsum]
  refine tendstoUniformlyOn_tsum_nat_eventually (airyCft_summable_inv_sq.mul_left (4 * M)) ?_
  filter_upwards [airyCft_eventually_ge (2 * (R + |a| + 1))] with n hn z hz
  have hz_le : ‖z‖ ≤ R := hR z hz
  have hza_ge : -airyZero (n + 1) / 2 ≤ ‖z - (airyZero (n + 1) : ℂ)‖ := by
    have hnorm := norm_sub_norm_le (airyZero (n + 1) : ℂ) z
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg (n + 1))] at hnorm
    linarith [abs_nonneg a]
  have hca_ge : -airyZero (n + 1) / 2 ≤ |airyZero (n + 1) - a| := by
    have := abs_sub_abs_le_abs_sub (airyZero (n + 1)) a
    rw [abs_of_neg (airyZero_neg (n + 1))] at this
    linarith [abs_nonneg a, norm_nonneg z, hz_le]
  have hzne : z ≠ (airyZero (n + 1) : ℂ) := fun h => by
    rw [h, sub_self, norm_zero] at hza_ge; linarith [airyZero_neg (n + 1)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cohnC, abs_inv, cohnLC, dslope_of_ne _ hzne,
    slope_def_field, airyAiC_ofReal (airyZero (n + 1)), airyAi_airyZero, Complex.ofReal_zero,
    sub_zero, norm_div]
  have hpos : 0 < -airyZero (n + 1) / 2 := by linarith [airyZero_neg (n + 1)]
  have h1 : |airyZero (n + 1) - a|⁻¹ ≤ (-airyZero (n + 1) / 2)⁻¹ := inv_anti₀ hpos hca_ge
  have h2 : ‖airyAiC z‖ / ‖z - (airyZero (n + 1) : ℂ)‖ ≤ M / (-airyZero (n + 1) / 2) :=
    div_le_div₀ hM0 (hM z hz) hpos hza_ge
  calc |airyZero (n + 1) - a|⁻¹ * (‖airyAiC z‖ / ‖z - (airyZero (n + 1) : ℂ)‖)
      ≤ (-airyZero (n + 1) / 2)⁻¹ * (M / (-airyZero (n + 1) / 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 4 * M * ((airyZero (n + 1)) ^ 2)⁻¹ := by
        have hne : airyZero (n + 1) ≠ 0 := (airyZero_neg (n + 1)).ne; field_simp; ring

/-- Locally uniform convergence on `ℝ` of `∑_{n ≥ 1} c_n L_n(u)` to `H_*(u)` (`ceo:O11f`). -/
theorem cardinal_Hstar_tendstoLocallyUniformly {a : ℝ} (ha : airyAi' a = 0) :
    TendstoLocallyUniformly
      (fun N u => ∑ n ∈ Finset.range N, cohnC a n * cohnL n u)
      (cardinalHstar a) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have hC := (tendstoLocallyUniformly_iff_forall_isCompact.mp
    (cardinal_HstarC_tendstoLocallyUniformly ha)) (Complex.ofReal '' K)
    (hK.image Complex.continuous_ofReal)
  rw [Metric.tendstoUniformlyOn_iff] at hC ⊢
  intro ε hε
  filter_upwards [hC ε hε] with N hN u hu
  have h := hN (u : ℂ) ⟨u, hu, rfl⟩
  rw [dist_eq_norm, cardinalHstarC_ofReal ha u] at h
  have hsum : (∑ n ∈ Finset.range N, (cohnC a n : ℂ) * cohnLC n (u : ℂ)) =
      ((∑ n ∈ Finset.range N, cohnC a n * cohnL n u : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun n _ => by rw [cohnLC_ofReal]
  rw [hsum, ← Complex.ofReal_sub, Complex.norm_real] at h
  simpa [Real.dist_eq] using h

/-! #### `L²(ℝ)` orthonormality, convergence, and Parseval (`ceo:O11f`) -/

/-- `L_n` as an element of `L²(ℝ; ℂ)`, constructed from `airyKerL2 (a_n) = Ai'(a_n) L_n`. -/
noncomputable def cohnLL2 (n : ℕ) : AiryL2 :=
  (((airyAi' (airyZero (n + 1)))⁻¹ : ℝ) : ℂ) • airyKerL2 (airyZero (n + 1))

lemma cohnLL2_ae (n : ℕ) :
    cohnLL2 n =ᵐ[volume] fun u : ℝ => (cohnL n u : ℂ) := by
  filter_upwards [Lp.coeFn_smul (((airyAi' (airyZero (n + 1)))⁻¹ : ℝ) : ℂ)
    (airyKerL2 (airyZero (n + 1))), airyKerL2_ae (airyZero (n + 1))] with u hu1 hu2
  unfold cohnLL2
  rw [hu1, Pi.smul_apply, hu2, smul_eq_mul]
  have hne : airyAi' (airyZero (n + 1)) ≠ 0 := by simpa [airyZ] using airyAi'_airyZ_ne_zero n
  have hAi0 : airyAi (airyZero (n + 1)) = 0 := airyAi_airyZero (n + 1)
  have hL : airyKer (airyZero (n + 1)) u = airyAi' (airyZero (n + 1)) * cohnL n u := by
    by_cases hu : u = airyZero (n + 1)
    · subst hu; rw [airyKer_self, cohnL_self, hAi0]; ring
    · rw [airyKer_of_ne (Ne.symm hu), airyKernelAi, cohnL_of_ne hu, hAi0]
      have hne' : airyZero (n + 1) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
      have hne'' : u - airyZero (n + 1) ≠ 0 := sub_ne_zero.mpr hu
      field_simp; ring
  rw [hL]; push_cast
  have hneC : (airyAi' (airyZero (n + 1)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  field_simp

lemma cohnLL2_mem_airyPW (n : ℕ) : cohnLL2 n ∈ airyPW :=
  Submodule.smul_mem _ _ (airyKerL2_mem _)

/-- **Orthonormality of `{L_n}` in `L²(ℝ)` (`ceo:O11f`).** -/
theorem cohnLL2_orthonormal : Orthonormal ℂ cohnLL2 := by
  rw [orthonormal_iff_ite]
  intro n m
  unfold cohnLL2
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_airyKerL2_airyKerL2]
  have hker : airyKer (airyZero (n + 1)) (airyZero (m + 1)) =
      if n = m then airyAi' (airyZero (n + 1)) ^ 2 else 0 := by
    simpa [airyZ] using airyKer_airyZ n m
  rw [hker]
  have hne : airyAi' (airyZero (n + 1)) ≠ 0 := by simpa [airyZ] using airyAi'_airyZ_ne_zero n
  by_cases h : n = m
  · subst h; simp only [↓reduceIte]; push_cast
    have hneC : (airyAi' (airyZero (n + 1)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    field_simp
  · simp [h]

/-- Real integral form of cardinal orthonormality: `∫_ℝ L_n(u) L_m(u) du = δ_{nm}` (`ceo:O11f`). -/
theorem cohnL_integral_mul (n m : ℕ) :
    Integrable (fun u : ℝ => cohnL n u * cohnL m u) ∧
      ∫ u : ℝ, cohnL n u * cohnL m u = if n = m then 1 else 0 := by
  have hintC : Integrable (fun u : ℝ => (cohnL n u : ℂ) * (cohnL m u : ℂ)) := by
    refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (cohnLL2 n) (cohnLL2 m)).congr ?_
    filter_upwards [cohnLL2_ae n, cohnLL2_ae m] with u h1 h2
    rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
  have hint : Integrable (fun u : ℝ => cohnL n u * cohnL m u) :=
    hintC.re.congr (ae_of_all _ fun u => by simp [← Complex.ofReal_mul])
  have heq : (∫ u : ℝ, (cohnL n u : ℂ) * (cohnL m u : ℂ)) =
      inner ℂ (cohnLL2 n) (cohnLL2 m) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [cohnLL2_ae n, cohnLL2_ae m] with u h1 h2
    rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
  rw [(orthonormal_iff_ite.mp cohnLL2_orthonormal) n m] at heq
  have hreal : ((∫ u : ℝ, cohnL n u * cohnL m u : ℝ) : ℂ) = if n = m then (1 : ℂ) else 0 := by
    rw [← integral_complex_ofReal]; simpa [Complex.ofReal_mul] using heq
  refine ⟨hint, Complex.ofReal_injective ?_⟩
  split_ifs with h <;> simpa [h] using hreal

private lemma cohnL_finset_sum_ae (a : ℝ) (N : ℕ) :
    (⇑(∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n)) =ᵐ[volume]
      fun u : ℝ => (∑ n ∈ Finset.range N, cohnC a n * cohnL n u : ℝ) := by
  have hsum := Lp.coeFn_finsetSum (Finset.range N) (fun n => (cohnC a n : ℂ) • cohnLL2 n)
  have hsmul : ∀ n ∈ Finset.range N,
      ((cohnC a n : ℂ) • cohnLL2 n : AiryL2) =ᵐ[volume] fun u : ℝ => (cohnC a n * cohnL n u : ℂ) :=
    fun n _ => by
      filter_upwards [Lp.coeFn_smul (cohnC a n : ℂ) (cohnLL2 n), cohnLL2_ae n] with u h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have h_all := (Finset.eventually_all (Finset.range N)).mpr hsmul
  filter_upwards [hsum, h_all] with u hu1 hu2
  rw [hu1, Finset.sum_apply, Finset.sum_congr rfl fun n hn => hu2 n hn]
  push_cast; rfl

/-- **`L²(ℝ)` convergence and Parseval for `H_* = ∑_{n ≥ 1} c_n L_n` (`ceo:O11f`):**
for any real zero `a` of `Ai'`, `H_* ∈ L²(ℝ)`, `∑_{n ≥ 1} c_n L_n = H_*` in `L²(ℝ)`,
`H_* ∈ PW`, and `∫_ℝ H_*(u)² du = -a`. -/
theorem cardinal_Hstar_memLp_and_L2_hasSum {a : ℝ} (ha : airyAi' a = 0) :
    ∃ hmem : MemLp (fun u : ℝ => (cardinalHstar a u : ℂ)) 2 volume,
      HasSum (fun n : ℕ => (cohnC a n : ℂ) • cohnLL2 n) (hmem.toLp _) ∧
      (hmem.toLp _) ∈ airyPW ∧
      ∫ u : ℝ, cardinalHstar a u ^ 2 = -a := by
  have hAa : airyAi a ≠ 0 := airyAi_ne_zero_of_deriv_zero ha
  have hma : cohnM a = 0 := by simp [cohnM, ha]
  have hsq : HasSum (fun n : ℕ => cohnC a n ^ 2) (-a) := by
    have h := hasSum_inv_sq a hAa
    rw [hma, zero_pow two_ne_zero, zero_sub] at h
    refine h.congr_fun fun n => ?_
    rw [cohnC, inv_pow]; ring_nf
  have hs_norm : Summable (fun n : ℕ => ‖(cohnC a n : ℂ)‖ ^ 2) :=
    hsq.summable.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hs_L2 : Summable (fun n : ℕ => (cohnC a n : ℂ) • cohnLL2 n) :=
    (cohnLL2_orthonormal.orthogonalFamily.summable_iff_norm_sq_summable
      (fun n => (cohnC a n : ℂ))).mpr hs_norm
  set HL2 : AiryL2 := ∑' n : ℕ, (cohnC a n : ℂ) • cohnLL2 n
  have hHasSum : HasSum (fun n : ℕ => (cohnC a n : ℂ) • cohnLL2 n) HL2 := hs_L2.hasSum
  have hNat := hHasSum.tendsto_sum_nat
  obtain ⟨ns, hns_mono, hns_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hNat).exists_seq_tendsto_ae
  have h_fin : ∀ᵐ u : ℝ ∂volume, ∀ N : ℕ,
      (⇑(∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n)) u =
        (∑ n ∈ Finset.range N, cohnC a n * cohnL n u : ℝ) :=
    ae_all_iff.mpr fun N => cohnL_finset_sum_ae a N
  have h_ae : HL2 =ᵐ[volume] fun u : ℝ => (cardinalHstar a u : ℂ) := by
    filter_upwards [hns_ae, h_fin] with u hu_lim hu_fin
    have h1 : Tendsto (fun k => ((∑ n ∈ Finset.range (ns k), cohnC a n * cohnL n u : ℝ) : ℂ))
        atTop (𝓝 (HL2 u)) := hu_lim.congr fun k => hu_fin (ns k)
    have h2 : Tendsto (fun k => ((∑ n ∈ Finset.range (ns k), cohnC a n * cohnL n u : ℝ) : ℂ))
        atTop (𝓝 (cardinalHstar a u : ℂ)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_sum] using
        ((Complex.ofRealCLM.hasSum (cardinal_Hstar_hasSum ha u)).tendsto_sum_nat).comp
          hns_mono.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hmem : MemLp (fun u : ℝ => (cardinalHstar a u : ℂ)) 2 volume := (Lp.memLp HL2).ae_eq h_ae
  have htoLp : hmem.toLp _ = HL2 := Lp.ext (hmem.coeFn_toLp.trans h_ae.symm)
  have hPW : hmem.toLp _ ∈ airyPW := by
    rw [htoLp]
    refine isClosed_airyPW.mem_of_tendsto hNat (Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (cohnLL2_mem_airyPW n)
  have h_norm_sq : ‖HL2‖ ^ 2 = -a := by
    have h_partial : ∀ N : ℕ,
        ‖∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n‖ ^ 2 = ∑ n ∈ Finset.range N, cohnC a n ^ 2 := by
      intro N
      have ho := cohnLL2_orthonormal.orthogonalFamily.norm_sum (fun n => (cohnC a n : ℂ)) (Finset.range N)
      change ‖∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n‖ ^ 2 = _ at ho
      rw [ho]
      exact Finset.sum_congr rfl fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact tendsto_nhds_unique ((hNat.norm.pow 2).congr h_partial) hsq.tendsto_sum_nat
  have hint_sq : ∫ u : ℝ, cardinalHstar a u ^ 2 = -a := by
    have hin : inner ℂ HL2 HL2 = ∫ u : ℝ, ((cardinalHstar a u ^ 2 : ℝ) : ℂ) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [h_ae] with u hu
      rw [hu, RCLike.inner_apply, Complex.conj_ofReal]; push_cast; ring
    have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) HL2
    rw [hin, integral_complex_ofReal] at hself
    norm_cast at hself
    exact (Complex.ofReal_injective hself).trans h_norm_sq
  exact ⟨hmem, htoLp ▸ hHasSum, hPW, hint_sq⟩

/-- Explicit `eLpNorm` convergence `‖∑_{n < N} c_n L_n - H_*‖₂ → 0` (`ceo:O11f`). -/
theorem cardinal_Hstar_L2_tendsto {a : ℝ} (ha : airyAi' a = 0) :
    Tendsto (fun N : ℕ =>
        eLpNorm (fun u : ℝ => ∑ n ∈ Finset.range N, cohnC a n * cohnL n u - cardinalHstar a u)
          2 volume)
      atTop (𝓝 0) := by
  obtain ⟨hmem, hHasSum, _, _⟩ := cardinal_Hstar_memLp_and_L2_hasSum ha
  have ht : Tendsto (fun N : ℕ => ‖(∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n) -
      hmem.toLp _‖) atTop (𝓝 0) := by
    simpa using (hHasSum.tendsto_sum_nat.sub (tendsto_const_nhds (x := hmem.toLp _))).norm
  have ht_enn : Tendsto (fun N : ℕ => eLpNorm
      (fun u : ℝ => ((∑ n ∈ Finset.range N, cohnC a n * cohnL n u - cardinalHstar a u : ℝ) : ℂ))
      2 volume) atTop (𝓝 0) := by
    have ht' : Tendsto (fun N : ℕ => ENNReal.ofReal
        ‖(∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n) - hmem.toLp _‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    refine ht'.congr fun N => ?_
    have h_ae : (⇑((∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n) - hmem.toLp _)) =ᵐ[volume]
        fun u : ℝ => ((∑ n ∈ Finset.range N, cohnC a n * cohnL n u - cardinalHstar a u : ℝ) : ℂ) := by
      filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, (cohnC a n : ℂ) • cohnLL2 n) (hmem.toLp _),
        cohnL_finset_sum_ae a N, hmem.coeFn_toLp] with u hu1 hu2 hu4
      rw [hu1, Pi.sub_apply, hu2, hu4]; push_cast; ring
    rw [MeasureTheory.Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_congr_ae h_ae
  refine ht_enn.congr fun N => ?_
  have hm_sum : AEStronglyMeasurable
      (fun u : ℝ => ∑ n ∈ Finset.range N, cohnC a n * cohnL n u) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun n _ =>
      ((Complex.continuous_re.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n))).const_mul _)
  have hm_H : AEStronglyMeasurable (cardinalHstar a) volume :=
    Complex.continuous_re.comp_aestronglyMeasurable hmem.aestronglyMeasurable
  have hm_diff : AEStronglyMeasurable
      (fun u : ℝ => ∑ n ∈ Finset.range N, cohnC a n * cohnL n u - cardinalHstar a u) volume :=
    hm_sum.sub hm_H
  exact eLpNorm_congr_norm_ae
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hm_diff) hm_diff
    (Eventually.of_forall fun u => Complex.norm_real _)

/-- Parseval identity at `a₁' = airyDerivFirstZero`: `∫_ℝ H_*(u)² du = |a₁'|` (`ceo:O11f`). -/
theorem cardinal_Hstar_parseval_firstDerivZero :
    ∫ u : ℝ, cardinalHstar airyDerivFirstZero u ^ 2 = |airyDerivFirstZero| := by
  obtain ⟨_, _, _, hint⟩ := cardinal_Hstar_memLp_and_L2_hasSum airyDerivFirstZero_spec.2.2
  rw [hint, abs_of_neg airyDerivFirstZero_spec.2.1]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.CohnElkies.ceX0_pos_and_lt_ceX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceX0_pos_and_lt_ceX1

/-- info: 'FormalResearch.CohnElkies.ceEta_pos_and_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceEta_pos_and_lt_one

/-- info: 'FormalResearch.CohnElkies.ceTransportRatio_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceTransportRatio_eq_closed

/-- info: 'FormalResearch.CohnElkies.ceTransportRatio_pos_and_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceTransportRatio_pos_and_lt_one

/-- info: 'FormalResearch.CohnElkies.ceTransportRatio_tendsto_one_atZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceTransportRatio_tendsto_one_atZero

/-- info: 'FormalResearch.CohnElkies.ceTransportRatio_tendsto_zero_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceTransportRatio_tendsto_zero_atTop

/-- info: 'FormalResearch.CohnElkies.ceTransportRatio_sup_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceTransportRatio_sup_lt_one

/-- info: 'FormalResearch.CohnElkies.pf3_kernel_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf3_kernel_bound

/-- info: 'FormalResearch.CohnElkies.pf3_kernel_bound_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf3_kernel_bound_uniform

/-- info: 'FormalResearch.CohnElkies.pf3_kernel_bound_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf3_kernel_bound_nonvacuous

/-- info: 'FormalResearch.CohnElkies.pf5_worst_phase_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf5_worst_phase_margin

/-- info: 'FormalResearch.CohnElkies.pf5_interval_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf5_interval_margin

/-- info: 'FormalResearch.CohnElkies.pf5_interval_margin_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.pf5_interval_margin_contraction

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_hasSum

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_hasSum_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_hasSum_of_ne

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_hasSum_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_hasSum_self

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_hasSum_firstDerivZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_hasSum_firstDerivZero

/-- info: 'FormalResearch.CohnElkies.cardinal_HstarC_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_HstarC_hasSum

/-- info: 'FormalResearch.CohnElkies.cardinal_HstarC_tendstoLocallyUniformly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_HstarC_tendstoLocallyUniformly

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_tendstoLocallyUniformly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_tendstoLocallyUniformly

/-- info: 'FormalResearch.CohnElkies.cohnLL2_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnLL2_orthonormal

/-- info: 'FormalResearch.CohnElkies.cohnL_integral_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnL_integral_mul

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_memLp_and_L2_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_memLp_and_L2_hasSum

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_L2_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_L2_tendsto

/-- info: 'FormalResearch.CohnElkies.cardinal_Hstar_parseval_firstDerivZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_Hstar_parseval_firstDerivZero

end FormalResearch.CohnElkies

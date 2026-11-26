/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumConcrete
public import FormalResearch.SignUncertainty.FctPhysicalBudget
public import FormalResearch.SignUncertainty.FctTau0Symbol

/-!
# `fct:physical-budget` for the concrete physical datum: `hvac` discharged (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` and Proposition `fct:warp-asymp` (1), (3).

`physical_budget_field` (`FctPhysicalBudget`) takes the vacuum integral `hvac` as a hypothesis for abstract scales `δf, sf, L1f` and an abstract
envelope `Of`; `vacuum_integral_concrete` (`FctVacuumConcrete`) proves it for the concrete datum from the size bounds `hsize`
(`|s| ≲ a¹²`, `|L₁|, |α| ≲ a⁸`, `a = c^{-1/12}`) and `hO`.  This file *names* the physical datum and proves those two inputs.

**The datum** (the objects of `(fct:B-physical)` and of `fct:warp-asymp` (3)):

* `δ_L = m(c^{-1/4})` (`physDelta`, `uctM`), `m(τ₁) ≍ τ₁² = c^{-1/2}` (`uct_m_lower_small`, `uct_m_upper_small`);
* `s = θ₁^ε / c` (`physShift`, `θ₁^ε = ctTheta1 ε`, a constant), so `|s| ≲ c^{-1} = a¹²`;
* `L₁ = log(π² T₁ / c)` (`physL1`; `T₁ = (c/π²) e^{L₁}` of `fct:warp-asymp` (1)), with `T₁` the abstract `FctMainHankelInputs.T1`;
* `O = I_osc^{warp}` (`physOscDatum`) *defined* by `fct:warp-asymp` (3) from `P = vacP`, `Φ = vacPhi a` at `(s, L₁)`, `α` the zero-solve value
  (so `hO` is `rfl`).

**Size reconciliation.**  `|L₁| ≲ c^{-2/3} = a⁸` (not `c^{-1/2}`): the paper's `fct:warp-asymp` (1) gives `T₁ = Δ₅^ε(c) + O(c^{-1})` and
`Δ₅ = c/π² + A c^{1/3} + O(1)`, hence `π² T₁/c = 1 + O(c^{-2/3})` and `L₁ = O(c^{-2/3})`.  This is **proved here** from the `warp_zero` clause
of `FctMainHankelInputs` (`physL1_le`); `L₁ ≍ δ_L ≍ c^{-1/2}` is not what the paper says (the paper has `|L₁| ≪ δ_L`).  `|s| ≲ c^{-1}`
(`ctTheta1_bound`), `δ_L ≍ c^{-1/2}` and the six scale inequalities of `physical_budget_field`'s `hsize` are likewise proved
(`physDatum_scales`).

**Remaining named inputs.**  For `FctMainHankelInputs` `I`, `T₁ = I.T1` and `α = I.alpha` come with `|T₁ - Δ₅| ≤ C c⁻¹`, `|α| ≤ C c^{-2/3}`
(`I.warp_zero`, `fct:warp-asymp` (1)) and `n_c = 1/I.Nc` with `N_c = 1 + O(c⁻¹)` (`I.splitting_norm`, `fct:splitting` (2); `nc_inv_bound`).
Left: `hdef` (`B = (fct:B-physical)`) and the symbol-class input `hR` of Lemma FCT.7b (b); `hT` is proved (`physT_symW`).

Class: proved under the explicit hypotheses `hdef`, `hR` (and the fields of `I`); `hvac`, `hsize` (scales), `hα`, `hn` and `hO` are proved.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real ContDiff
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctMoment SymW

/-! ### The physical datum -/

/-- `δ_L = m(τ₁)`, `τ₁ = c^{-1/4}` (`fct:comp-D`, `(fct:B-physical)`). -/
noncomputable def physDelta (c : ℝ) : ℝ := uctM (c ^ (-(1 / 4 : ℝ)))

/-- `s = θ₁^ε / c` (`L̃ = L - θ₁^ε/c`, `fct:warp-asymp` (3)). -/
noncomputable def physShift (ε c : ℝ) : ℝ := CtOuter.ctTheta1 ε / c

/-- `L₁ = log(π² T₁ / c)`, i.e. `T₁ = (c/π²) e^{L₁}` (`fct:warp-asymp` (1)), for the threshold datum `T₁`. -/
noncomputable def physL1 (T1 : ℝ → ℝ → ℝ) (ε c : ℝ) : ℝ := Real.log (π ^ 2 * T1 ε c / c)

/-- `O = I_osc^{warp}` of `fct:warp-asymp` (3): `P(u) ‖u - L₁ Φ(u)‖/(L - L₁)`, `P = vacP` (`I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)`),
`Φ = φ_kill(iτ₀(·); c^{-1/12})`, at `s = θ₁^ε/c`, `L₁ = physL1 T1`, and the zero-solve `α = αf ε c`. -/
noncomputable def physOscDatum (kind : StripKernelChoice) (K4 : ℝ) (T1 αf : ℝ → ℝ → ℝ) (ε c x : ℝ) : ℝ :=
  physOsc (vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ)))) (vacPhi (c ^ (-(1 / 12 : ℝ)))) (physShift ε c) (physL1 T1 ε c) x

/-! ### Size facts -/

lemma exists_rpow_neg_le {p η : ℝ} (hp : 0 < p) (hη : 0 < η) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → c ^ (-p) ≤ η := by
  obtain ⟨c₁, hc₁⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_neg_atTop hp).eventually (Iio_mem_nhds hη))
  exact ⟨max c₁ 1, le_max_right _ _, fun c hc => (hc₁ c ((le_max_left _ _).trans hc)).le⟩

/-- `|θ₁^ε| ≤ K` uniformly (`θ₁^- = -3 log 2 + I₀`, `θ₁^+ = θ₁^- - π`). -/
lemma ctTheta1_bound : ∃ K : ℝ, ∀ ε : ℝ, |CtOuter.ctTheta1 ε| ≤ K := by
  refine ⟨|-3 * Real.log 2 + CtOuter.ctI0| + π, fun ε => ?_⟩
  unfold CtOuter.ctTheta1
  have h : |(if ε = 1 then π else 0)| ≤ π := by
    split_ifs
    · exact (abs_of_pos Real.pi_pos).le
    · simpa using Real.pi_pos.le
  calc |-3 * Real.log 2 + CtOuter.ctI0 - (if ε = 1 then π else 0)|
      ≤ |-3 * Real.log 2 + CtOuter.ctI0| + |(if ε = 1 then π else 0)| := abs_sub _ _
    _ ≤ _ := by linarith

lemma abs_le_pm_pm (f : ℝ → ℝ) {ε : ℝ} (h : ε = 1 ∨ ε = -1) : |f ε| ≤ |f 1| + |f (-1)| := by
  rcases h with rfl | rfl
  · linarith [abs_nonneg (f (-1))]
  · linarith [abs_nonneg (f 1)]

lemma abs_log_le_two {y : ℝ} (h : |y - 1| ≤ 1 / 2) : |Real.log y| ≤ 2 * |y - 1| := by
  have hy : 1 / 2 ≤ y := by linarith [(abs_le.mp h).1]
  have hy0 : 0 < y := by linarith
  have h1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have h2 : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy0
  have hyi : y⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hy0 (by norm_num)]; linarith
  have h3 : y⁻¹ - 1 = (1 - y) * y⁻¹ := by field_simp
  have h4 : (1 - y) * y⁻¹ ≤ 2 * |y - 1| := by
    have : (1 - y) ≤ |y - 1| := by rw [abs_sub_comm]; exact le_abs_self _
    have h0 : 0 ≤ y⁻¹ := inv_nonneg.mpr hy0.le
    nlinarith [abs_nonneg (y - 1)]
  rw [abs_le]
  constructor
  · linarith
  · have := le_abs_self (y - 1); linarith [abs_nonneg (y - 1)]

/-- `L₁ = O(c^{-2/3})` (`fct:warp-asymp` (1)): from `|T₁ - Δ₅^ε(c)| ≤ C c⁻¹` and `Δ₅ = c/π² + A c^{1/3} + O(1)`. -/
lemma physL1_le (T1 : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹) :
    ∃ K c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      |physL1 T1 ε c| ≤ K * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C, c₁, hC⟩ := hT1
  set Kk : ℝ := |ctKappa 1| + |ctKappa (-1)| with hKk
  set Kd : ℝ := |ctD2star 1| + |ctD2star (-1)| with hKd
  set Ky : ℝ := π ^ 2 * (|C| + |airyOrderCoeff| + Kk + |ctC1Langer| + Kd) with hKy
  have hKy0 : 0 ≤ Ky := by positivity
  obtain ⟨c₂, hc₂1, hc₂⟩ := exists_rpow_neg_le (p := 2 / 3) (η := 1 / (2 * (Ky + 1))) (by norm_num) (by positivity)
  refine ⟨2 * Ky, max c₁ c₂, le_trans hc₂1 (le_max_right _ _), fun ε c hε hc => ?_⟩
  have hcc₁ : c₁ ≤ c := (le_max_left _ _).trans hc
  have hcc₂ : c₂ ≤ c := (le_max_right _ _).trans hc
  have hc1 : 1 ≤ c := hc₂1.trans hcc₂
  have hc0 : 0 < c := by linarith
  have hq : ∀ q : ℝ, q ≤ -(2 / 3) → c ^ q ≤ c ^ (-(2 / 3 : ℝ)) := fun q hq =>
    Real.rpow_le_rpow_of_exponent_le hc1 hq
  have hmul : ∀ r : ℝ, c⁻¹ * c ^ r = c ^ (r - 1) := fun r => by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; ring_nf
  have hinv : c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
    have := hq (-1) (by norm_num); rwa [Real.rpow_neg_one] at this
  have hpos : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have e1 : c⁻¹ * c ^ (1 / 3 : ℝ) ≤ c ^ (-(2 / 3 : ℝ)) := by
    rw [hmul]; exact le_of_eq (by norm_num)
  have e2 : c⁻¹ * c ^ (-(1 / 3) : ℝ) ≤ c ^ (-(2 / 3 : ℝ)) := by
    rw [hmul]; exact hq _ (by norm_num)
  have e3 : c⁻¹ * c ^ (-(2 / 3) : ℝ) ≤ c ^ (-(2 / 3 : ℝ)) := by
    rw [hmul]; exact hq _ (by norm_num)
  have hTe := hC ε c hε hcc₁
  have hk : |ctKappa ε| ≤ Kk := abs_le_pm_pm ctKappa hε
  have hd : |ctD2star ε| ≤ Kd := abs_le_pm_pm ctD2star hε
  -- `π² T₁ / c - 1`
  have hy : π ^ 2 * T1 ε c / c - 1 = π ^ 2 * c⁻¹ * (T1 ε c - ctDelta5 ε c) +
      π ^ 2 * (airyOrderCoeff * (c⁻¹ * c ^ (1 / 3 : ℝ)) + ctKappa ε * c⁻¹ +
        ctC1Langer * (c⁻¹ * c ^ (-(1 / 3) : ℝ)) + ctD2star ε * (c⁻¹ * c ^ (-(2 / 3) : ℝ))) := by
    unfold ctDelta5
    field_simp
    ring
  have hybd : |π ^ 2 * T1 ε c / c - 1| ≤ Ky * c ^ (-(2 / 3 : ℝ)) := by
    rw [hy]
    have hpi : (0 : ℝ) ≤ π ^ 2 := by positivity
    have t1 : |π ^ 2 * c⁻¹ * (T1 ε c - ctDelta5 ε c)| ≤ π ^ 2 * (|C| * c ^ (-(2 / 3 : ℝ))) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ π ^ 2 * c⁻¹)]
      calc π ^ 2 * c⁻¹ * |T1 ε c - ctDelta5 ε c| ≤ π ^ 2 * c⁻¹ * (C * c⁻¹) :=
            mul_le_mul_of_nonneg_left hTe (by positivity)
        _ ≤ π ^ 2 * c⁻¹ * (|C| * c⁻¹) := by
            gcongr; exact le_abs_self _
        _ ≤ π ^ 2 * (|C| * c ^ (-(2 / 3 : ℝ))) := by
            have : c⁻¹ * (|C| * c⁻¹) ≤ |C| * c ^ (-(2 / 3 : ℝ)) := by
              have h1 : c⁻¹ * c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
                calc c⁻¹ * c⁻¹ ≤ 1 * c ^ (-(2 / 3 : ℝ)) := by
                      apply mul_le_mul _ hinv (by positivity) zero_le_one
                      exact inv_le_one_of_one_le₀ hc1
                  _ = _ := one_mul _
              nlinarith [abs_nonneg C]
            nlinarith
    have t2 : |π ^ 2 * (airyOrderCoeff * (c⁻¹ * c ^ (1 / 3 : ℝ)) + ctKappa ε * c⁻¹ +
        ctC1Langer * (c⁻¹ * c ^ (-(1 / 3) : ℝ)) + ctD2star ε * (c⁻¹ * c ^ (-(2 / 3) : ℝ)))| ≤
        π ^ 2 * ((|airyOrderCoeff| + Kk + |ctC1Langer| + Kd) * c ^ (-(2 / 3 : ℝ))) := by
      rw [abs_mul, abs_of_nonneg hpi]
      refine mul_le_mul_of_nonneg_left ?_ hpi
      have b1 : |airyOrderCoeff * (c⁻¹ * c ^ (1 / 3 : ℝ))| ≤ |airyOrderCoeff| * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c⁻¹ * c ^ (1 / 3 : ℝ))]
        exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
      have b2 : |ctKappa ε * c⁻¹| ≤ Kk * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c⁻¹)]
        calc |ctKappa ε| * c⁻¹ ≤ Kk * c⁻¹ := mul_le_mul_of_nonneg_right hk (by positivity)
          _ ≤ Kk * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hinv (by positivity)
      have b3 : |ctC1Langer * (c⁻¹ * c ^ (-(1 / 3) : ℝ))| ≤ |ctC1Langer| * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c⁻¹ * c ^ (-(1 / 3) : ℝ))]
        exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      have b4 : |ctD2star ε * (c⁻¹ * c ^ (-(2 / 3) : ℝ))| ≤ Kd * c ^ (-(2 / 3 : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c⁻¹ * c ^ (-(2 / 3) : ℝ))]
        calc |ctD2star ε| * (c⁻¹ * c ^ (-(2 / 3) : ℝ)) ≤ Kd * (c⁻¹ * c ^ (-(2 / 3) : ℝ)) :=
              mul_le_mul_of_nonneg_right hd (by positivity)
          _ ≤ Kd * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left e3 (by positivity)
      calc _ ≤ |airyOrderCoeff * (c⁻¹ * c ^ (1 / 3 : ℝ))| + |ctKappa ε * c⁻¹| +
            |ctC1Langer * (c⁻¹ * c ^ (-(1 / 3) : ℝ))| + |ctD2star ε * (c⁻¹ * c ^ (-(2 / 3) : ℝ))| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by linarith
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ π ^ 2 * (|C| * c ^ (-(2 / 3 : ℝ))) +
          π ^ 2 * ((|airyOrderCoeff| + Kk + |ctC1Langer| + Kd) * c ^ (-(2 / 3 : ℝ))) := add_le_add t1 t2
      _ = _ := by rw [hKy]; ring
  have hsmall : Ky * c ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 := by
    have h := hc₂ c hcc₂
    have : Ky * c ^ (-(2 / 3 : ℝ)) ≤ Ky * (1 / (2 * (Ky + 1))) := mul_le_mul_of_nonneg_left h hKy0
    refine this.trans ?_
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have := abs_log_le_two (hybd.trans hsmall)
  unfold physL1
  calc _ ≤ 2 * |π ^ 2 * T1 ε c / c - 1| := this
    _ ≤ 2 * (Ky * c ^ (-(2 / 3 : ℝ))) := by linarith
    _ = _ := by ring

/-- `δ_L = m(c^{-1/4}) ≍ c^{-1/2}` (`m(t) ≍ t²`, `uct_m_lower_small`, `uct_m_upper_small`). -/
lemma physDelta_bounds : ∃ a₀ a₁ c₀ : ℝ, 0 < a₀ ∧ 0 < a₁ ∧ 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
    a₀ * c ^ (-(1 / 2 : ℝ)) ≤ physDelta c ∧ physDelta c ≤ a₁ * c ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨cm, hcm, hcmb⟩ := uct_m_lower_small
  obtain ⟨Cu, hCu, hCub⟩ := uct_m_upper_small
  obtain ⟨c₀, hc₀, hc₀b⟩ := exists_rpow_neg_le (p := 1 / 4) (η := 1 / 8) (by norm_num) (by norm_num)
  refine ⟨cm, Cu, c₀, hcm, hCu, hc₀, fun c hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have hτ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ8 : c ^ (-(1 / 4 : ℝ)) ≤ 1 / 8 := hc₀b c hc
  have hsq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have h1 := (hcmb _ ⟨hτ, hτ8⟩).1
  have h2 := hCub _ ⟨hτ, hτ8⟩
  rw [hsq] at h1 h2
  exact ⟨h1, h2⟩

/-- The scale inequalities of `physical_budget_field`'s `hsize`, for the physical datum, for all large `c` (all proved). -/
lemma physDatum_scales (T1 : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹) :
    ∃ c₀ a₀ a₁ : ℝ, 1 ≤ c₀ ∧ 0 < a₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < physDelta c ∧ 3 / 2 * physDelta c ≤ 1 ∧ |physShift ε c| ≤ 3 / 2 * physDelta c / 2 ∧
        |physL1 T1 ε c| ≤ 3 / 2 * physDelta c / 2 ∧ |physL1 T1 ε c - physShift ε c| ≤ 3 / 2 * physDelta c ∧
        (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * physDelta c) ^ (-3 : ℝ) ≤ 1 ∧
        a₀ * c ^ (-(1 / 2 : ℝ)) ≤ physDelta c ∧ physDelta c ≤ a₁ * c ^ (-(1 / 2 : ℝ)) ∧ 6 * physDelta c ≤ 1 := by
  obtain ⟨a₀, a₁, cδ, ha₀, ha₁, hcδ1, hδ⟩ := physDelta_bounds
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  obtain ⟨Kθ, hKθ⟩ := ctTheta1_bound
  have hKθ0 : 0 ≤ Kθ := (abs_nonneg _).trans (hKθ 0)
  have hKL0 : 0 ≤ KL := by
    have := hL 1 (max cL 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cL 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (physL1 T1 1 (max cL 1))]
  -- smallness thresholds
  obtain ⟨c₁, hc₁1, hc₁⟩ := exists_rpow_neg_le (p := 1 / 2) (η := 3 * a₀ / (8 * (Kθ + 1))) (by norm_num) (by positivity)
  obtain ⟨c₂, hc₂1, hc₂⟩ := exists_rpow_neg_le (p := 1 / 6) (η := 3 * a₀ / (4 * (KL + 1))) (by norm_num) (by positivity)
  obtain ⟨c₃, hc₃1, hc₃⟩ := exists_rpow_neg_le (p := 1 / 2) (η := 1 / (6 * (a₁ + 1))) (by norm_num) (by positivity)
  obtain ⟨c₄, hc₄1, hc₄⟩ := exists_rpow_neg_le (p := 1 / 2)
    (η := 1 / ((5 * π ^ 2 / 96) * (3 * a₀ / 2) ^ (-3 : ℝ) + 1)) (by norm_num) (by positivity)
  refine ⟨max (max (max cδ cL) (max c₁ c₂)) (max c₃ c₄), a₀, a₁, ?_, ha₀, fun ε c hε hc => ?_⟩
  · exact le_trans hc₁1 ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hA : max (max cδ cL) (max c₁ c₂) ≤ c := (le_max_left _ _).trans hc
  have hB : max c₃ c₄ ≤ c := (le_max_right _ _).trans hc
  have hcδ : cδ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hA
  have hcL : cL ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hA
  have hcc₁ : c₁ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hA
  have hcc₂ : c₂ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hA
  have hcc₃ : c₃ ≤ c := (le_max_left _ _).trans hB
  have hcc₄ : c₄ ≤ c := (le_max_right _ _).trans hB
  have hc1 : 1 ≤ c := hcδ1.trans hcδ
  have hc0 : 0 < c := by linarith
  obtain ⟨hδa, hδb⟩ := hδ c hcδ
  have hh : 0 < c ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hδ0 : 0 < physDelta c := lt_of_lt_of_le (by positivity) hδa
  -- `|s| ≤ (3/4) a₀ c^{-1/2}`
  have hs : |physShift ε c| ≤ 3 / 2 * physDelta c / 2 := by
    have h1 : |physShift ε c| ≤ Kθ * c⁻¹ := by
      unfold physShift
      rw [abs_div, abs_of_pos hc0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hKθ ε) (by positivity)
    have h2 : c⁻¹ = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
    have h3 := hc₁ c hcc₁
    have h4 : Kθ * c ^ (-(1 / 2 : ℝ)) ≤ 3 * a₀ / 8 := by
      calc _ ≤ Kθ * (3 * a₀ / (8 * (Kθ + 1))) := mul_le_mul_of_nonneg_left h3 hKθ0
        _ ≤ 3 * a₀ / 8 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [mul_pos ha₀ (by norm_num : (0 : ℝ) < 3)]
    calc |physShift ε c| ≤ Kθ * c⁻¹ := h1
      _ = (Kθ * c ^ (-(1 / 2 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h2]; ring
      _ ≤ (3 * a₀ / 8) * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h4 hh.le
      _ ≤ 3 / 2 * physDelta c / 2 := by nlinarith
  have hL1 : |physL1 T1 ε c| ≤ 3 / 2 * physDelta c / 2 := by
    have h1 := hL ε c hε hcL
    have h2 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have h3 := hc₂ c hcc₂
    have h4 : KL * c ^ (-(1 / 6 : ℝ)) ≤ 3 * a₀ / 4 := by
      calc _ ≤ KL * (3 * a₀ / (4 * (KL + 1))) := mul_le_mul_of_nonneg_left h3 hKL0
        _ ≤ 3 * a₀ / 4 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [mul_pos ha₀ (by norm_num : (0 : ℝ) < 3)]
    calc |physL1 T1 ε c| ≤ KL * c ^ (-(2 / 3 : ℝ)) := h1
      _ = (KL * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h2]; ring
      _ ≤ (3 * a₀ / 4) * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h4 hh.le
      _ ≤ 3 / 2 * physDelta c / 2 := by nlinarith
  have hδ6 : 6 * physDelta c ≤ 1 := by
    have h3 := hc₃ c hcc₃
    calc 6 * physDelta c ≤ 6 * (a₁ * c ^ (-(1 / 2 : ℝ))) := by linarith
      _ ≤ 6 * (a₁ * (1 / (6 * (a₁ + 1)))) := by gcongr
      _ ≤ 1 := by
          rw [mul_one_div, mul_div_assoc', div_le_one (by positivity)]
          nlinarith
  refine ⟨hδ0, by linarith, hs, hL1, ?_, ?_, hδa, hδb, hδ6⟩
  · have := abs_sub (physL1 T1 ε c) (physShift ε c)
    linarith
  · -- `(5π²/96) c⁻² (3δ/2)^{-3} ≤ 1`
    have hylow : 0 < (3 * a₀ / 2) * c ^ (-(1 / 2 : ℝ)) := by positivity
    have hδlow : (3 * a₀ / 2) * c ^ (-(1 / 2 : ℝ)) ≤ 3 / 2 * physDelta c := by linarith
    have hY := (rpow_neg_le_of_le hylow hδlow (by norm_num : (0 : ℝ) ≤ 3))
    rw [rpow_scale_half (by positivity) hc0] at hY
    have hcc : c⁻¹ ^ 2 * c ^ (3 / 2 : ℝ) = c ^ (-(1 / 2 : ℝ)) := by
      rw [show c⁻¹ ^ 2 = c ^ (-(2 : ℝ)) by rw [Real.rpow_neg hc0.le, Real.rpow_two]; simp, ← Real.rpow_add hc0]
      norm_num
    have h3 := hc₄ c hcc₄
    set Z : ℝ := (5 * π ^ 2 / 96) * (3 * a₀ / 2) ^ (-3 : ℝ) with hZ
    have hZ0 : 0 ≤ Z := by positivity
    calc (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * physDelta c) ^ (-3 : ℝ)
        ≤ (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * ((3 * a₀ / 2) ^ (-3 : ℝ) * c ^ ((3 : ℝ) / 2)) := by
          gcongr
      _ = Z * c ^ (-(1 / 2 : ℝ)) := by rw [hZ, ← hcc]; ring
      _ ≤ Z * (1 / (Z + 1)) := mul_le_mul_of_nonneg_left h3 hZ0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith

lemma rpow_a_pow {c : ℝ} (hc : 0 < c) (n : ℕ) : (c ^ (-(1 / 12 : ℝ))) ^ n = c ^ (-((n : ℝ) / 12)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; congr 1; ring

/-- The size bounds `|s| ≲ a¹²`, `|L₁|, |α| ≲ a⁸` (`a = c^{-1/12}`) that `vacuum_integral_concrete` assumes, for the physical datum. -/
lemma physDatum_vacsize (T1 αf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |αf ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ K c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      |physShift ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 12 ∧ |physL1 T1 ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 8 ∧
        |αf ε c| ≤ K * (c ^ (-(1 / 12 : ℝ))) ^ 8 := by
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  obtain ⟨Kα, cα, hα'⟩ := hα
  obtain ⟨Kθ, hKθ⟩ := ctTheta1_bound
  refine ⟨max Kθ (max KL Kα), max cL cα, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := hcL1.trans ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have h12 : (c ^ (-(1 / 12 : ℝ))) ^ 12 = c⁻¹ := by
    rw [rpow_a_pow hc0]; norm_num [Real.rpow_neg_one]
  have h8 : (c ^ (-(1 / 12 : ℝ))) ^ 8 = c ^ (-(2 / 3 : ℝ)) := by
    rw [rpow_a_pow hc0]; norm_num
  have hp12 : 0 ≤ c⁻¹ := by positivity
  have hp8 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  refine ⟨?_, ?_, ?_⟩
  · rw [h12]
    unfold physShift
    rw [abs_div, abs_of_pos hc0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ((hKθ ε).trans (le_max_left _ _)) hp12
  · rw [h8]
    exact (hL ε c hε ((le_max_left _ _).trans hc)).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp8)
  · rw [h8]
    exact (hα' ε c hε ((le_max_right _ _).trans hc)).trans
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp8)

/-! ### `hT`: the transition-bump symbol class -/

/-- **`hT` of Lemma FCT.7b (c), proved**: `τ₀⁴ I_fl ∈ (M_T, -1/2, 3/2)` on `[3δ_L/2, 6δ_L]`, `δ_L = physDelta c`, for all large `c`
(`m(t) = t² mQ(t)`, `τ₀(L) = ψ(√L)` with `ψ` the smooth inverse of `t√mQ(t)` (`tau0_symW`), `I_fl = α_fl L^{-3/2}`;
`6δ_L ≤ L₀` for `c ≥ c₀` since `δ_L ≍ c^{-1/2}`).  The constants `M_T = |α_fl|`, `K_T` do not depend on `c`. -/
theorem physT_symW : ∃ (c₀ MT : ℝ) (KT : ℕ → ℝ), 0 ≤ MT ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    SymW (Icc (3 / 2 * physDelta c) (6 * physDelta c)) (pw MT (-(1 / 2)) (3 / 2)) KT
      (fun L => tau0 L ^ 4 * uctIfl L) := by
  obtain ⟨L₀, K, hL₀, hL₀1, h⟩ := tauT_symW
  obtain ⟨a₀, a₁, cδ, ha₀, ha₁, hcδ1, hδ⟩ := physDelta_bounds
  obtain ⟨c₁, hc₁1, hc₁⟩ := exists_rpow_neg_le (p := 1 / 2) (η := L₀ / (6 * (a₁ + 1))) (by norm_num) (by positivity)
  refine ⟨max cδ c₁, |uctAlphaFl|, K, abs_nonneg _, fun ε c _ hc => ?_⟩
  have hcδ : cδ ≤ c := (le_max_left _ _).trans hc
  have hcc₁ : c₁ ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  obtain ⟨hδa, hδb⟩ := hδ c hcδ
  have hh : 0 < c ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hδ0 : 0 < physDelta c := lt_of_lt_of_le (by positivity) hδa
  have h6 : 6 * physDelta c ≤ L₀ := by
    have h3 := hc₁ c hcc₁
    calc 6 * physDelta c ≤ 6 * (a₁ * c ^ (-(1 / 2 : ℝ))) := by linarith
      _ ≤ 6 * (a₁ * (L₀ / (6 * (a₁ + 1)))) := by gcongr
      _ = L₀ * (a₁ / (a₁ + 1)) := by field_simp
      _ ≤ L₀ * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = L₀ := mul_one _
  have hsub : Icc (3 / 2 * physDelta c) (6 * physDelta c) ⊆ Ioc 0 L₀ := fun x hx =>
    ⟨by linarith [hx.1], hx.2.trans h6⟩
  refine (h.mono_set hsub).of_le (fun x hx => ?_) (fun _ => le_rfl)
  have hx1 : x ≤ 1 := hx.2.trans (h6.trans hL₀1)
  simp only [pw, hx1, ite_true, neg_neg]
  exact le_rfl

/-! ### `hvac` and `hsize` for the physical datum -/

/-- **`hvac` for the physical datum** (`fct:physical-budget` (a)-(d), `vacuum_integral_concrete` with `hO` and `hsize` discharged): for
`δ_L = physDelta`, `s = physShift`, `L₁ = physL1 T1`, `O = physOscDatum`, the vacuum integral `∫ χ(L/3δ_L) γ(L̃)(O − F) dL ≤ A c^{-3/4}`.
Inputs: `hT1` (`T₁ = Δ₅ + O(c⁻¹)`, `fct:warp-asymp` (1)) and `hα` (`|α| ≲ c^{-2/3}`, `fct:warp-asymp` (1)). -/
theorem physDatum_hvac {χ : ℝ → ℝ} (hχ : IsCutoff χ) (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4)
    (T1 αf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |αf ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ A c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (∫ x, χ (x / (3 * physDelta c)) * physGamma c (physShift ε c) x *
        (physOscDatum kind K4 T1 αf ε c x - physF (physShift ε c) (physL1 T1 ε c) x)) ≤ A * c ^ (-(3 / 4 : ℝ)) :=
  vacuum_integral_concrete hχ kind hK4 (fun ε c => physShift ε c) (fun ε c => physL1 T1 ε c) αf
    (physOscDatum kind K4 T1 αf) ⟨0, fun _ _ _ _ _ _ => rfl⟩ (physDatum_vacsize T1 αf hT1 hα)

/-- The `hsize` input of `physical_budget_field` for the physical datum: all scale inequalities proved, `n_c` bounded by `hn`. -/
lemma physDatum_hsize (T1 nf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hn : ∃ nmax c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 ≤ nf ε c ∧ |nf ε c| ≤ nmax) :
    ∃ c₀ a₀ a₁ nmax : ℝ, 1 ≤ c₀ ∧ 0 < a₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      0 < physDelta c ∧ 3 / 2 * physDelta c ≤ 1 ∧ |physShift ε c| ≤ 3 / 2 * physDelta c / 2 ∧
        |physL1 T1 ε c| ≤ 3 / 2 * physDelta c / 2 ∧ |physL1 T1 ε c - physShift ε c| ≤ 3 / 2 * physDelta c ∧
        (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * physDelta c) ^ (-3 : ℝ) ≤ 1 ∧
        a₀ * c ^ (-(1 / 2 : ℝ)) ≤ physDelta c ∧ physDelta c ≤ a₁ * c ^ (-(1 / 2 : ℝ)) ∧ 6 * physDelta c ≤ 1 ∧
        0 ≤ nf ε c ∧ |nf ε c| ≤ nmax := by
  obtain ⟨c₁, a₀, a₁, hc₁, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨nmax, c₂, hn'⟩ := hn
  refine ⟨max c₁ c₂, a₀, a₁, nmax, hc₁.trans (le_max_left _ _), ha₀, fun ε c hε hc => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsc ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨h10, h11⟩ := hn' ε c hε ((le_max_right _ _).trans hc)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ### The corollaries without `hvac` -/

/-- **`physical_budget` of `FctMainHankelInputs` for the concrete physical datum** (Lemma `fct:physical-budget`): `physical_budget_field`
with `δf = m(c^{-1/4})`, `sf = θ₁^ε/c`, `L1f = log(π² T₁/c)`, `Of = I_osc^{warp}` (`physOscDatum`), the hypothesis `hvac` **removed** (proved by
`physDatum_hvac`) and the scale part of `hsize` proved.  Remaining inputs: `hT1`, `hα` (`fct:warp-asymp` (1)), `hn` (`n_c = 1 + O(c⁻¹)`),
`hdef` (the definition `(fct:B-physical)`), and `hR` (the symbol class of Lemma FCT.7b (b)); `hT` is `physT_symW`. -/
theorem physical_budget_field_concrete {χ : ℝ → ℝ} (hχ : IsCutoff χ) (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {Bphys : ℝ → ℝ → ℝ → ℝ → ℝ} (T1 αf nf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |αf ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)))
    (hn : ∃ nmax c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 ≤ nf ε c ∧ |nf ε c| ≤ nmax)
    (hdef : ∀ ε c K1 : ℝ, Bphys ε c K1 = physBump χ (nf ε c) c (physDelta c) (physShift ε c) K1 K4
      (physOscDatum kind K4 T1 αf ε c) (physF (physShift ε c) (physL1 T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hR : ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MR (-1) 0) KR
        (fun x => physOscDatum kind K4 T1 αf ε c x / physF (physShift ε c) (physL1 T1 ε c) x - 1))
    :
    ∃ C0 b2 : ℝ, ∀ K1 : ℝ, 0 < K1 → ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (ctWbump (Bphys ε c K1) ε c 0).re ≤ (C0 + b2 * K1) * c ^ (-(13 / 12 : ℝ)) :=
  physical_budget_field hχ (fun _ c => physDelta c) (fun ε c => physShift ε c) (fun ε c => physL1 T1 ε c) nf K4
    (physOscDatum kind K4 T1 αf) hdef (physDatum_hsize T1 nf hT1 hn) hR physT_symW
    (physDatum_hvac hχ kind hK4 T1 αf hT1 hα)

/-- `n_c = 1/N_c` with `N_c = 1 + O(c⁻¹)` (`fct:splitting` (2)) satisfies `0 ≤ n_c ≤ 2` for large `c`: the `hn` input. -/
lemma nc_inv_bound (Nc : ℝ → ℝ → ℝ)
    (hN : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |Nc ε c - 1| ≤ C * c⁻¹) :
    ∃ nmax c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 ≤ (fun ε c => 1 / Nc ε c) ε c ∧ |(fun ε c => 1 / Nc ε c) ε c| ≤ nmax := by
  obtain ⟨C, c₀, h⟩ := hN
  refine ⟨2, max c₀ (2 * |C| + 1), fun ε c hε hc => ?_⟩
  have hc0 : c₀ ≤ c := (le_max_left _ _).trans hc
  have hc1 : 2 * |C| + 1 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith [abs_nonneg C]
  have h1 := h ε c hε hc0
  have h2 : C * c⁻¹ ≤ 1 / 2 := by
    have : |C| * c⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hcpos]; linarith
    exact (mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hcpos.le)).trans this
  have hN : 1 / 2 ≤ Nc ε c := by linarith [(abs_le.mp h1).1, h2, (abs_le.mp h1).2]
  have hNpos : 0 < Nc ε c := by linarith
  refine ⟨by positivity, ?_⟩
  simp only
  rw [abs_of_pos (by positivity), div_le_iff₀ hNpos]
  linarith

/-- **The fields `bump_profile` and `physical_budget` of `FctMainHankelInputs` for the concrete physical datum**: `fctMainHankel_bump_fields` with
`hvac`, `hα` and `hn` removed and the scale part of `hsize` proved.  `T₁ = I.T1`, `α = I.alpha`, `hT1`, `hα` come from `I.warp_zero`
(`fct:warp-asymp` (1)) and `n_c = 1/I.Nc` (`hn` from `I.splitting_norm`, `fct:splitting` (2)).  The conclusions are literally the types of the
two fields. -/
theorem fctMainHankel_bump_fields_concrete {χ : ℝ → ℝ} (hχ : IsCutoff χ) (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4)
    (I : FctMainHankelInputs)
    (hdef : ∀ ε c K1 : ℝ, I.Bphys ε c K1 = physBump χ (1 / I.Nc ε c) c (physDelta c) (physShift ε c) K1 K4
      (physOscDatum kind K4 I.T1 I.alpha ε c) (physF (physShift ε c) (physL1 I.T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hR : ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MR (-1) 0) KR
        (fun x => physOscDatum kind K4 I.T1 I.alpha ε c x / physF (physShift ε c) (physL1 I.T1 ε c) x - 1))
    :
    type_of% I.bump_profile ∧ type_of% I.physical_budget := by
  obtain ⟨C, c₀, hw⟩ := I.warp_zero
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |I.T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨C, c₀, fun ε c hε hc => (hw ε c hε hc).1⟩
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |I.alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨C, c₀, fun ε c hε hc => (hw ε c hε hc).2⟩
  exact fctMainHankel_bump_fields hχ I (fun _ c => physDelta c) (fun ε c => physShift ε c) (fun ε c => physL1 I.T1 ε c)
    (fun ε c => 1 / I.Nc ε c) K4 (physOscDatum kind K4 I.T1 I.alpha) hdef
    (physDatum_hsize I.T1 _ hT1 (nc_inv_bound I.Nc I.splitting_norm)) hR physT_symW
    (physDatum_hvac hχ kind hK4 I.T1 I.alpha hT1 hα)

/-- info: 'FormalResearch.SignUncertainty.FctSym.physT_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physT_symW

/-- info: 'FormalResearch.SignUncertainty.FctSym.physL1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physL1_le

/-- info: 'FormalResearch.SignUncertainty.FctSym.physDatum_hvac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physDatum_hvac

/-- info: 'FormalResearch.SignUncertainty.FctSym.physical_budget_field_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical_budget_field_concrete

/-- info: 'FormalResearch.SignUncertainty.FctSym.nc_inv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nc_inv_bound

/-- info: 'FormalResearch.SignUncertainty.FctSym.fctMainHankel_bump_fields_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctMainHankel_bump_fields_concrete

end FormalResearch.SignUncertainty.FctSym

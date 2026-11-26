/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctHQ
public import FormalResearch.SignUncertainty.FctR0Symbol
public import FormalResearch.SignUncertainty.FctEVSymbol
public import FormalResearch.SignUncertainty.FctQConv
public import FormalResearch.SignUncertainty.FctDeltaCurvSymbol

/-!
# `QTSym` is a theorem: `hQ` of Lemma FCT.7b (b) from `fct:comp-D` (1) and `(fct:th-tail)`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b) (`fct:bump-sym-check`), `fct:comp-D` (1), `(fct:th-tail)`,
`uct:outer-growth` (the decay `|H_*/G_ε| = O((1+|τ|)² e^{-π|τ|})` enters through the explicit `‖H₀(it)‖`, `stripR0_t_symbol`).

`qtSym_of_alpha`: `QTSym kind K4 αf` for `K₄ ≥ 1` and `|α_f(ε, c)| ≤ K_α c^{-2/3}` (the form given by `FctMainHankelInputs.warp_zero`).
Proof: `stripR0_t_symbol` (`r₀`), `expV_symW` (`e^v - 1`, `fct:comp-D` (1)), `deltaCurv_symW` (`Δ_curv`, `(fct:th-inner)`, `(fct:th-tail)`)
with `τ₁ = c^{-1/4}`, converted to the `min(t², 1)`, `min(1, t^{-8})` form by `raw_min_of_symW` (`tm = τ₀(3δ_L/4) ≥ λ τ₁`,
`tau0_three_quarter_ge`).  `hQ_of_alpha`: the resulting `hQ` of `physR_symW_of_factors`.

Class: proved, no hypotheses beyond `K₄ ≥ 1` and the size bound on `α_f`.
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctMoment

/-- `c = x^{-12}`: `c^{-1/4} = x³`, `c^{-2/3} = x⁸`, `x¹² c = 1`. -/
lemma rpow_scales {c : ℝ} (hc : 0 < c) : ∃ x : ℝ, 0 < x ∧ x ^ 12 * c = 1 ∧ c ^ (-(1 / 4 : ℝ)) = x ^ 3 ∧
    c ^ (-(2 / 3 : ℝ)) = x ^ 8 := by
  set x : ℝ := c ^ (-(1 / 12 : ℝ)) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hc _
  refine ⟨x, hx0, ?_, ?_, ?_⟩
  · have : x ^ 12 = c ^ (-(1 : ℝ)) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
    rw [this, Real.rpow_neg_one]; field_simp
  · rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  · rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num

/-- **`QTSym` from the size bound on `α_f`** (the `t`-level symbol inputs of Lemma FCT.7b (b)). -/
theorem qtSym_of_alpha (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4) (αf : ℝ → ℝ → ℝ)
    (hα : ∃ Kα c₁ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₁ ≤ c → |αf ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    QTSym kind K4 αf := by
  obtain ⟨PR, hPR0, hRsm, hR2, hR8⟩ := stripR0_t_symbol kind
  obtain ⟨lam, hlam, hlam1, hlamb⟩ := tau0_three_quarter_ge
  obtain ⟨τV, KV, hτV, hτV20, hKV, hV⟩ := expV_symW kind K4 hK4
  obtain ⟨τD, KD, CwD, hτD, hτD100, hCwD, hKD, hD⟩ := deltaCurv_symW kind K4 hK4 hlam
  obtain ⟨τθ, Mi, Tt, hτθ, hτθ20, hMT, hθ⟩ := theta_bounds kind K4 hK4
  obtain ⟨Kα, c₁, hαf⟩ := hα
  set τc : ℝ := min (min τV τD) τθ with hτc
  have hτc0 : 0 < τc := lt_min (lt_min hτV hτD) hτθ
  have hτc100 : τc ≤ 1 / 100 := (min_le_left _ _).trans ((min_le_right _ _).trans hτD100)
  set δ : ℝ := min (min 1 τc) (1 / (|Kα| + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min one_pos hτc0) (by positivity)
  set P : ℕ → ℝ := fun j => max (PR j) (max (KV j * 256 / lam ^ 2) (max (KV j * 256)
    (max (KD j * CwD / lam ^ 2) (KD j * CwD)))) with hP
  refine ⟨max c₁ ((δ⁻¹) ^ 12), P, fun j => le_max_of_le_left (hPR0 j), ⟨hRsm, ?_, ?_⟩, ?_⟩
  · intro j t ht
    have hm : 0 ≤ min (t ^ 2) 1 := le_min (sq_nonneg t) zero_le_one
    exact (hR2 j t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm)
  · intro j t ht
    have hm : 0 ≤ min 1 ((t ^ 8)⁻¹) := le_min zero_le_one (inv_nonneg.mpr (pow_nonneg ht.le 8))
    exact (hR8 j t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm)
  intro ε c hε hcc
  have hcδ : (δ⁻¹) ^ 12 ≤ c := (le_max_right _ _).trans hcc
  have hc : 0 < c := lt_of_lt_of_le (by positivity) hcδ
  have hc₁ : c₁ ≤ c := (le_max_left _ _).trans hcc
  obtain ⟨x, hx0, hx12, hτ₁x, hc23⟩ := rpow_scales hc
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ)) with hτ₁
  have hxδ : x ≤ δ := by
    have h1 : x ^ 12 ≤ δ ^ 12 := by
      have : x ^ 12 = c⁻¹ := by field_simp; linarith
      rw [this]
      have h2 : 0 < (δ⁻¹) ^ 12 := by positivity
      calc c⁻¹ ≤ ((δ⁻¹) ^ 12)⁻¹ := inv_anti₀ h2 hcδ
        _ = δ ^ 12 := by rw [inv_pow, inv_inv]
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ0.le h1
  have hx1 : x ≤ 1 := hxδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hxτ : x ≤ τc := hxδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hxK : x ≤ 1 / (|Kα| + 1) := hxδ.trans (min_le_right _ _)
  have hτ₁pos : 0 < τ₁ := by rw [hτ₁x]; positivity
  have hτ₁le : τ₁ ≤ τc := by
    rw [hτ₁x]
    calc x ^ 3 ≤ x := pow_le_of_le_one hx0.le hx1 (by norm_num)
      _ ≤ τc := hxτ
  have hτ₁eq : τ₁ ^ 4 * c = 1 := by rw [hτ₁x, ← pow_mul]; exact hx12
  have hαle : |αf ε c| ≤ τ₁ ^ 2 := by
    refine (hαf ε c hε hc₁).trans ?_
    rw [hc23, hτ₁x, ← pow_mul]
    have hK1 : |Kα| * x ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hxK
      nlinarith [abs_nonneg Kα]
    have hx6 : 0 < x ^ 6 := by positivity
    calc Kα * x ^ 8 ≤ |Kα| * x ^ 8 := by gcongr; exact le_abs_self _
      _ = (|Kα| * x ^ 2) * x ^ 6 := by ring
      _ ≤ 1 * x ^ 6 := by
          gcongr
          nlinarith [abs_nonneg Kα, pow_pos hx0 2, mul_le_mul_of_nonneg_right hK1 hx0.le]
      _ = x ^ (3 * 2) := by ring
  have hτ₁V : τ₁ ≤ τV := hτ₁le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₁D : τ₁ ≤ τD := hτ₁le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ₁θ : τ₁ ≤ τθ := hτ₁le.trans (min_le_right _ _)
  have hτ₁1 : τ₁ ≤ 1 := by linarith [hτc100]
  have hτ₁8 : τ₁ ≤ 1 / 8 := by linarith [hτc100]
  -- the left end of the range
  have htm : lam * τ₁ ≤ tau0 (3 / 4 * physDelta c) := hlamb τ₁ hτ₁pos hτ₁8
  have htm0 : 0 < tau0 (3 / 4 * physDelta c) := lt_of_lt_of_le (by positivity) htm
  -- `e^v - 1`, `Δ_curv`
  have hV0 := hV hc hτ₁pos hτ₁V hτ₁eq hαle
  have hVs := hV0.mono_set (S' := Ici (tau0 (3 / 4 * physDelta c))) (fun t ht => lt_of_lt_of_le htm0 ht)
  have hD0 := hD hc hτ₁pos hτ₁D hτ₁eq hαle
  have hDs := hD0.mono_set (S' := Ici (tau0 (3 / 4 * physDelta c))) (fun t ht => le_trans htm ht)
  obtain ⟨hθcd, _, _⟩ := hθ hc hτ₁pos hτ₁θ hτ₁eq hαle
  have hS : ∀ x ∈ Ici (tau0 (3 / 4 * physDelta c)), lam * τ₁ ≤ x := fun x hx => htm.trans hx
  refine ⟨⟨?_, fun j t ht => ?_, fun j t ht => ?_⟩, ⟨?_, fun j t ht => ?_, fun j t ht => ?_⟩⟩
  · obtain ⟨U, hU, hSU, hfU⟩ := hV0.smooth
    exact ((hfU.mono hSU).add (contDiffOn_const (c := (1 : ℝ)))).congr (fun t _ => by ring)
  · have h := (raw_min_of_symW (le_refl 2) (by norm_num) hτ₁pos hτ₁1 hlam hlam1 hVs hS j (show t ∈ Ici _ from ht)).1
    have hm : 0 ≤ min (t ^ 2) 1 := le_min (sq_nonneg t) zero_le_one
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hm)
  · have h := (raw_min_of_symW (le_refl 2) (by norm_num) hτ₁pos hτ₁1 hlam hlam1 hVs hS j (show t ∈ Ici _ from ht)).2
    have hm : 0 ≤ min 1 ((t ^ 8)⁻¹) := le_min zero_le_one (inv_nonneg.mpr (pow_nonneg (le_of_lt (lt_of_lt_of_le htm0 ht)) 8))
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) hm)
  · exact contDiffOn_const.add (deltaCurv_contDiffOn hθcd)
  · have h := (raw_min_of_symW (a := 3) (by norm_num) hCwD hτ₁pos hτ₁1 hlam hlam1 hDs hS j (show t ∈ Ici _ from ht)).1
    have hm : 0 ≤ min (t ^ 2) 1 := le_min (sq_nonneg t) zero_le_one
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))) hm)
  · have h := (raw_min_of_symW (a := 3) (by norm_num) hCwD hτ₁pos hτ₁1 hlam hlam1 hDs hS j (show t ∈ Ici _ from ht)).2
    have hm : 0 ≤ min 1 ((t ^ 8)⁻¹) := le_min zero_le_one (inv_nonneg.mpr (pow_nonneg (le_of_lt (lt_of_lt_of_le htm0 ht)) 8))
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))) hm)

/-- info: 'FormalResearch.SignUncertainty.FctSym.qtSym_of_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qtSym_of_alpha

/-- **`hQ` of Lemma FCT.7b (b) is a theorem** (`fct:bump-sym-check`): `Q̃ = r₀ e^v (1 + Δ_curv)(τ₀(L̃)) - 1 ∈ SymW [3δ_L/2, ∞) (M, -1, 0)`
uniformly for `ε = ±1`, `c ≥ c₀`, for `K₄ ≥ 1` and `|α_f(ε, c)| ≤ K_α c^{-2/3}` (the form of `FctMainHankelInputs.warp_zero`). -/
theorem hQ_of_alpha (kind : StripKernelChoice) {K4 : ℝ} (hK4 : 1 ≤ K4) (αf : ℝ → ℝ → ℝ)
    (hα : ∃ Kα c₁ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₁ ≤ c → |αf ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ))) :
    ∃ (c₀ MQ : ℝ) (KQ : ℕ → ℝ), 0 ≤ MQ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MQ (-1) 0) KQ
        (fun x => vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) (x - physShift ε c) /
          uctIfl (x - physShift ε c) - 1) :=
  hQ_of_QTSym kind K4 αf (qtSym_of_alpha kind hK4 αf hα)

/-- info: 'FormalResearch.SignUncertainty.FctSym.hQ_of_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hQ_of_alpha

end FormalResearch.SignUncertainty.FctSym

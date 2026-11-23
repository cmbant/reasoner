module

public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure
public import FormalResearch.Special.AiryReal

/-!
# Spectral rigidity: the Airy-variable dictionary (`spectral_rigidity.tex`, §1)

For `c' = c - 1` (written `c` below) and `t > 0` put `b = √(3 t / c')` and
`u(t) = -β (b - ξ_*) / ε`, `ε = c'^{-2/3}`, with Jacobian `J(t) = |dt/du| = 2 b c'^{1/3} / (3 β)`
(`uAiry`, `jAiry`).  This module proves the elementary facts about this chart that the rigidity
theorems use:

* `uAiry_antitone`: larger `t` is more negative `u`;
* `tendsto_uAiry_shift`: `u(T_*(c) + z c^{1/3}) → a₁ - 3 β z / (2 ξ_*)` as `c → ∞`
  (in particular `u(T_*) → a₁`, `uAiry_TStar_tendsto`);
* `eventually_uAiry_le_of_gap`: the condition (Gap) `liminf (τ_j - T_*)/c_j'^{1/3} ≥ 0`, written as
  `∀ δ > 0, ∀ᶠ j, T_*(c_j) - δ c_j^{1/3} ≤ τ_j` (`GapCondition`), gives `limsup u(τ_j) ≤ a₁`;
* `eventually_le_of_uAiry_ge`: `liminf u(τ_j) ≥ a₁` gives `τ_j ≤ T_* + o(c_j'^{1/3})`;
* `gapCondition_of_tendsto`: (Gap) follows from `(τ_j - T_*)/c_j^{1/3} → 0`, the form proved for `T_V` in
  `FixedWeight.corollary_E1`.

All unconditional.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.FixedWeight

/-- The Airy variable `u(t) = -β (√(3t/c) - ξ_*) c^{2/3}` (`sr:sec`, §1), `c = c' = c - 1`. -/
noncomputable def uAiry (c t : ℝ) : ℝ :=
  -betaTip * (√(3 * t / c) - xiStar) * c ^ ((2 : ℝ) / 3)

/-- The Jacobian `J(t) = |dt/du| = 2 b c^{1/3} / (3 β)` with `b = √(3t/c)`. -/
noncomputable def jAiry (c t : ℝ) : ℝ :=
  2 * √(3 * t / c) * c ^ ((1 : ℝ) / 3) / (3 * betaTip)

/-- The condition (Gap) of `sr:Sigma0`, `sr:Sigma`: `liminf_j (τ_j - T_*(c_j)) / c_j^{1/3} ≥ 0`,
written without `liminf`: for every `δ > 0`, eventually `τ_j ≥ T_*(c_j) - δ c_j^{1/3}`. -/
def GapCondition (c τ : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, TStar (c j) - δ * (c j) ^ ((1 : ℝ) / 3) ≤ τ j

/-- (Gap) holds whenever `(τ_j - T_*(c_j)) / c_j^{1/3} → 0`, in particular for the gaps `τ_j = T_V(c_j)`
of `FixedWeight.corollary_E1`. -/
theorem gapCondition_of_tendsto {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (h : Tendsto (fun j => (τ j - TStar (c j)) / (c j) ^ ((1 : ℝ) / 3)) atTop (𝓝 0)) :
    GapCondition c τ := by
  intro δ hδ
  have hpos : ∀ᶠ j in atTop, 0 < c j := hc.eventually_gt_atTop 0
  filter_upwards [h.eventually (lt_mem_nhds (show -δ < 0 by linarith)), hpos] with j hj hjc
  have hp : 0 < (c j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hjc _
  rw [lt_div_iff₀ hp] at hj
  linarith

lemma uAiry_antitone {c : ℝ} (hc : 0 < c) : Antitone (uAiry c) := by
  intro t t' h
  unfold uAiry
  have hb : 0 < betaTip := betaTip_pos
  have hq : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hs : √(3 * t / c) ≤ √(3 * t' / c) :=
    Real.sqrt_le_sqrt (by gcongr)
  have : (√(3 * t / c) - xiStar) ≤ (√(3 * t' / c) - xiStar) := by linarith
  have h2 := mul_le_mul_of_nonneg_right this hq.le
  nlinarith [mul_le_mul_of_nonneg_left h2 hb.le]

private lemma rpow_third_mul_two_thirds {c : ℝ} (hc : 0 < c) :
    c ^ ((1 : ℝ) / 3) * c ^ ((2 : ℝ) / 3) = c := by
  rw [← Real.rpow_add hc]; norm_num

private lemma rpow_neg_two_thirds {c : ℝ} (hc : 0 < c) :
    c ^ (-((2 : ℝ) / 3)) = 1 / c ^ ((2 : ℝ) / 3) := by
  rw [Real.rpow_neg hc.le, one_div]

/-- Rationalised form of `uAiry` on the scale `t = ξ̄ c + y c^{1/3}`. -/
lemma uAiry_eq_of_scale {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3))) :
    uAiry c (xiBar * c + y * c ^ ((1 : ℝ) / 3)) =
      -3 * betaTip * y / (xiStar + √(xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3)))) := by
  set p := c ^ ((1 : ℝ) / 3) with hp
  set q := c ^ ((2 : ℝ) / 3) with hq
  have hp0 : 0 < p := Real.rpow_pos_of_pos hc _
  have hq0 : 0 < q := Real.rpow_pos_of_pos hc _
  have hpq : p * q = c := rpow_third_mul_two_thirds hc
  have hneg : c ^ (-((2 : ℝ) / 3)) = 1 / q := rpow_neg_two_thirds hc
  have hξ : 0 < xiStar := xiStar_pos
  have hX : 3 * (xiBar * c + y * p) / c = xiStar ^ 2 + 3 * y * (1 / q) := by
    unfold xiBar
    field_simp
    rw [← hpq]
    ring
  rw [hneg] at hy ⊢
  unfold uAiry
  rw [hX]
  set S := √(xiStar ^ 2 + 3 * y * (1 / q)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = xiStar ^ 2 + 3 * y * (1 / q) := Real.sq_sqrt hy
  have hden : 0 < xiStar + S := by linarith
  have hkey : (S - xiStar) * q = 3 * y / (xiStar + S) := by
    rw [eq_div_iff hden.ne']
    have : (S - xiStar) * (xiStar + S) = 3 * y * (1 / q) := by nlinarith [hS2]
    calc (S - xiStar) * q * (xiStar + S) = ((S - xiStar) * (xiStar + S)) * q := by ring
      _ = 3 * y * (1 / q) * q := by rw [this]
      _ = 3 * y := by field_simp
  calc -betaTip * (S - xiStar) * q = -betaTip * ((S - xiStar) * q) := by ring
    _ = -betaTip * (3 * y / (xiStar + S)) := by rw [hkey]
    _ = -3 * betaTip * y / (xiStar + S) := by ring

lemma TStar_add_shift (c z : ℝ) :
    TStar c + z * c ^ ((1 : ℝ) / 3) = xiBar * c + (Aopt + z) * c ^ ((1 : ℝ) / 3) := by
  unfold TStar; ring

lemma neg_three_betaTip_Aopt_div :
    -3 * betaTip * Aopt / (xiStar + xiStar) = airyZero 1 := by
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  have hξ : xiStar ≠ 0 := xiStar_pos.ne'
  have ha : |airyZero 1| = -airyZero 1 := abs_of_neg (airyZero_neg 1)
  unfold Aopt cStar
  rw [ha]
  field_simp
  ring

/-- **The chart at the Airy threshold**: `u(T_*(c) + z c^{1/3}) → a₁ - 3 β z / (2 ξ_*)` as
`c → ∞`.  In particular `u(T_*) → a₁` (`z = 0`). -/
theorem tendsto_uAiry_shift (z : ℝ) :
    Tendsto (fun c : ℝ => uAiry c (TStar c + z * c ^ ((1 : ℝ) / 3))) atTop
      (𝓝 (airyZero 1 - 3 * betaTip * z / (2 * xiStar))) := by
  have hξ : 0 < xiStar := xiStar_pos
  set y := Aopt + z with hy
  have hε : Tendsto (fun c : ℝ => c ^ (-((2 : ℝ) / 3))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hX : Tendsto (fun c : ℝ => xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3))) atTop
      (𝓝 (xiStar ^ 2 + 3 * y * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hε)
  have hS : Tendsto (fun c : ℝ => √(xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3)))) atTop
      (𝓝 (√(xiStar ^ 2 + 3 * y * 0))) :=
    (Real.continuous_sqrt.tendsto _).comp hX
  have hS' : √(xiStar ^ 2 + 3 * y * 0) = xiStar := by
    rw [mul_zero, add_zero, Real.sqrt_sq hξ.le]
  rw [hS'] at hS
  have hden : Tendsto (fun c : ℝ => xiStar + √(xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3)))) atTop
      (𝓝 (xiStar + xiStar)) := tendsto_const_nhds.add hS
  have hlim : Tendsto (fun c : ℝ =>
      -3 * betaTip * y / (xiStar + √(xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3))))) atTop
      (𝓝 (-3 * betaTip * y / (xiStar + xiStar))) :=
    tendsto_const_nhds.div hden (by linarith)
  have hval : -3 * betaTip * y / (xiStar + xiStar) =
      airyZero 1 - 3 * betaTip * z / (2 * xiStar) := by
    rw [hy]
    have h1 := neg_three_betaTip_Aopt_div
    have : -3 * betaTip * (Aopt + z) / (xiStar + xiStar) =
        -3 * betaTip * Aopt / (xiStar + xiStar) - 3 * betaTip * z / (2 * xiStar) := by
      field_simp
      ring
    rw [this, h1]
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hpos : ∀ᶠ c : ℝ in atTop, 0 < c := eventually_gt_atTop 0
  have hnn : ∀ᶠ c : ℝ in atTop, 0 ≤ xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3)) := by
    have : ∀ᶠ c : ℝ in atTop, 0 < xiStar ^ 2 + 3 * y * c ^ (-((2 : ℝ) / 3)) := by
      refine hX.eventually (lt_mem_nhds ?_)
      rw [mul_zero, add_zero]; positivity
    exact this.mono fun c hc => hc.le
  filter_upwards [hpos, hnn] with c hc hn
  rw [TStar_add_shift, uAiry_eq_of_scale hc hn]

theorem uAiry_TStar_tendsto :
    Tendsto (fun c : ℝ => uAiry c (TStar c)) atTop (𝓝 (airyZero 1)) := by
  have := tendsto_uAiry_shift 0
  simpa using this

/-- (Gap) gives `limsup_j u(τ_j) ≤ a₁`. -/
theorem eventually_uAiry_le_of_gap {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hgap : GapCondition c τ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, uAiry (c j) (τ j) ≤ airyZero 1 + δ := by
  intro δ hδ
  have hξ : 0 < xiStar := xiStar_pos
  have hb : 0 < betaTip := betaTip_pos
  set z : ℝ := -(xiStar * δ) / (3 * betaTip) with hz
  have hzneg : 0 < -z := by rw [hz]; have : 0 < xiStar * δ / (3 * betaTip) := by positivity
                            linarith [neg_div (3 * betaTip) (xiStar * δ)]
  have hlim := (tendsto_uAiry_shift z).comp hc
  have hval : airyZero 1 - 3 * betaTip * z / (2 * xiStar) = airyZero 1 + δ / 2 := by
    rw [hz]; field_simp; ring
  rw [hval] at hlim
  have h1 : ∀ᶠ j in atTop, uAiry (c j) (TStar (c j) + z * (c j) ^ ((1 : ℝ) / 3)) < airyZero 1 + δ :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have h2 := hgap (-z) hzneg
  have h3 : ∀ᶠ j in atTop, 0 < c j := hc.eventually_gt_atTop 0
  filter_upwards [h1, h2, h3] with j hj1 hj2 hj3
  have : TStar (c j) + z * (c j) ^ ((1 : ℝ) / 3) ≤ τ j := by linarith
  have h4 := uAiry_antitone hj3 this
  linarith

/-- `liminf_j u(τ_j) ≥ a₁` gives `τ_j ≤ T_*(c_j) + o(c_j^{1/3})`. -/
theorem eventually_le_of_uAiry_ge {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hu : ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, airyZero 1 - δ ≤ uAiry (c j) (τ j)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, τ j ≤ TStar (c j) + δ * (c j) ^ ((1 : ℝ) / 3) := by
  intro δ hδ
  have hξ : 0 < xiStar := xiStar_pos
  have hb : 0 < betaTip := betaTip_pos
  set e : ℝ := 3 * betaTip * δ / (4 * xiStar) with he
  have he0 : 0 < e := by positivity
  have hlim := (tendsto_uAiry_shift δ).comp hc
  have hval : airyZero 1 - 3 * betaTip * δ / (2 * xiStar) = airyZero 1 - 2 * e := by
    rw [he]; field_simp; ring
  rw [hval] at hlim
  have h1 : ∀ᶠ j in atTop, uAiry (c j) (TStar (c j) + δ * (c j) ^ ((1 : ℝ) / 3)) < airyZero 1 - e :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have h2 := hu e he0
  have h3 : ∀ᶠ j in atTop, 0 < c j := hc.eventually_gt_atTop 0
  filter_upwards [h1, h2, h3] with j hj1 hj2 hj3
  by_contra hcon
  push Not at hcon
  have h4 := uAiry_antitone hj3 hcon.le
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.gapCondition_of_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.tendsto_uAiry_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.tendsto_uAiry_shift

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.eventually_uAiry_le_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.eventually_uAiry_le_of_gap

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.eventually_le_of_uAiry_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.eventually_le_of_uAiry_ge

end FormalResearch.ModularBootstrap.Upper.Rigidity

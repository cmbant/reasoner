module

public import FormalResearch.ModularBootstrap.Duality.CrossingMeasure

/-!
# Fixed-Weight Proposition D1, Measure-Form Sum Rules, and Explicit Test Finiteness

Generalises the D1 duality layer of `CFT/modular_bootstrap/paper/dual_spectrum.tex` (`ds:D1`,
and the explicit thermal test showing `T_V < ∞` for every `(w, Q)` with `c̃ > 0` and `c̃ ≥ 12 S`)
to every fixed-weight problem `prob : FixedWeightProblem`.

* `trivialProductProblem`: the `m = 0`, `Q ≡ 1` (`S = 0`) fixed-weight problem at weight `w ≥ 1`.
* `gVac_thermalDiff_neg`: for every `(w, Q)`, `a > 0`, and `0 < β < 1`, `g_vac(Ξ_β) < 0`
  (proved as in Lemma M(a) of `dual_spectrum.tex`).
* `explicit_feasible_thermal_test`, `T_V_lt_top`: finiteness `T_V < ∞` for every `(w, Q)` and
  `c̃ > 0`, `c̃ ≥ 12 S` via the explicit test `g = A Ξ_{β₁} - Ξ_{β₂}` (`0 < β₁ < β₂ < 1`).
* `proposition_D1`: full `dual_spectrum.tex` `ds:D1` statement combining threshold exclusion,
  `T_V ≥ τ`, `Δ_best ≥ a + τ`, and both measure-form D1 sum rules (`proposition_P1`,
  `proposition_P2`).
* `sumRule_of_comb_decay`: comb-test exponential decay `C e^{-4π√(at) - π√(3t/c̃)}` satisfies
  the D1 sum-rule decay hypothesis `q > (w + 1) / 2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Additional named fixed-weight problem (`Q ≡ 1`) -/

/-- The trivial-null-product fixed-weight problem `Q ≡ 1` (`m = 0`, `S = 0`) at weight `w ≥ 1`. -/
def trivialProductProblem (w : ℕ) (hw : 1 ≤ w) : FixedWeightProblem where
  w := w
  hw := hw
  m := 0
  μ := Fin.elim0
  hμ := fun l => l.elim0

@[simp] lemma trivialProductProblem_totalShift (w : ℕ) (hw : 1 ≤ w) :
    (trivialProductProblem w hw).totalShift = 0 := by
  unfold FixedWeightProblem.totalShift trivialProductProblem
  simp

@[simp] lemma trivialProductProblem_nullPoly (w : ℕ) (hw : 1 ≤ w) (q : ℝ) :
    (trivialProductProblem w hw).nullPoly q = 1 := by
  unfold FixedWeightProblem.nullPoly trivialProductProblem
  simp

/-! ### Section 2: Vacuum sign of `Ξ_β` and finiteness `T_V < ∞` via the explicit test -/

/-- `Q(q)` is antitone on `[0, 1]`: for `0 ≤ q₁ ≤ q₂ ≤ 1`, `Q(q₂) ≤ Q(q₁)`. -/
lemma nullPoly_antitone_on_Icc (prob : FixedWeightProblem) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₁₂ : q₁ ≤ q₂) (hq₂ : q₂ ≤ 1) :
    prob.nullPoly q₂ ≤ prob.nullPoly q₁ := by
  unfold FixedWeightProblem.nullPoly
  have hterm : ∀ l : Fin prob.m,
      0 ≤ 1 - q₂ ^ prob.μ l ∧ 1 - q₂ ^ prob.μ l ≤ 1 - q₁ ^ prob.μ l := fun l =>
    ⟨sub_nonneg.mpr (Real.rpow_le_one (hq₁.trans hq₁₂) hq₂ (prob.hμ l).le),
     sub_le_sub_left (Real.rpow_le_rpow hq₁ hq₁₂ (prob.hμ l).le) 1⟩
  induction (Finset.univ : Finset (Fin prob.m)) using Finset.cons_induction with
  | empty => simp
  | cons a s _ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons]
    have ha' := hterm a
    have hs₂ : 0 ≤ ∏ x ∈ s, (1 - q₂ ^ prob.μ x) :=
      Finset.prod_nonneg fun x _ => (hterm x).1
    exact mul_le_mul ha'.2 ih hs₂ (ha'.1.trans ha'.2)

/-- Vacuum sign of thermal differences (`dual_spectrum.tex`, Lemma M(a) / explicit test):
for every `(w, Q)`, `a > 0`, and `0 < β < 1`, `g_vac(Ξ_β) < 0`. -/
theorem gVac_thermalDiff_neg (prob : FixedWeightProblem) {a β : ℝ}
    (ha : 0 < a) (hβ0 : 0 < β) (hβ1 : β < 1) :
    prob.gVac a (thermalDiff prob.w β) < 0 := by
  rw [prob.gVac_thermalDiff a hβ0]
  have hq1_pos : 0 < Real.exp (-2 * π * β) := Real.exp_pos _
  have hq1_lt : Real.exp (-2 * π * β) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hq2_pos : 0 < Real.exp (-2 * π / β) := Real.exp_pos _
  have hβ_inv : β < β⁻¹ := lt_trans hβ1 ((one_lt_inv₀ hβ0).mpr hβ1)
  have hq2_le_q1 : Real.exp (-2 * π / β) ≤ Real.exp (-2 * π * β) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show -2 * π / β = -2 * π * β⁻¹ by ring]
    nlinarith [Real.pi_pos]
  have hQ1_pos : 0 < prob.nullPoly (Real.exp (-2 * π * β)) :=
    prob.nullPoly_pos hq1_pos.le hq1_lt
  have hQ1_le_Q2 : prob.nullPoly (Real.exp (-2 * π * β)) ≤ prob.nullPoly (Real.exp (-2 * π / β)) :=
    nullPoly_antitone_on_Icc prob hq2_pos.le hq2_le_q1 hq1_lt.le
  have hbw_gt1 : 1 < β ^ (-(prob.w : ℝ)) := by
    rw [Real.rpow_neg hβ0.le, one_lt_inv₀ (Real.rpow_pos_of_pos hβ0 _)]
    have hw_pos : (0 : ℝ) < (prob.w : ℝ) := by
      have := prob.hw
      exact_mod_cast (by omega : 0 < prob.w)
    exact Real.rpow_lt_one hβ0.le hβ1 hw_pos
  have hexp_lt : Real.exp (2 * π * a * β) < Real.exp (2 * π * a / β) := by
    refine Real.exp_lt_exp.mpr ?_
    rw [div_eq_mul_inv]
    have hdiff : 0 < 2 * π * a * (β⁻¹ - β) := mul_pos (by positivity) (sub_pos.mpr hβ_inv)
    linarith
  have hleft : Real.exp (2 * π * a * β) < β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := by
    calc Real.exp (2 * π * a * β)
        < Real.exp (2 * π * a / β) := hexp_lt
      _ = 1 * Real.exp (2 * π * a / β) := (one_mul _).symm
      _ < β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) :=
          mul_lt_mul_of_pos_right hbw_gt1 (Real.exp_pos _)
  have hprod : Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) <
      β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) :=
    calc Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))
        < (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β)) *
            prob.nullPoly (Real.exp (-2 * π * β)) := mul_lt_mul_of_pos_right hleft hQ1_pos
      _ ≤ (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β)) *
            prob.nullPoly (Real.exp (-2 * π / β)) := mul_le_mul_of_nonneg_left hQ1_le_Q2 (by positivity)
  linarith

/-- **Explicit thermal test for `T_V < ∞`** (`dual_spectrum.tex`, §2 "Strong duality with
attainment"): for any `(w, Q)`, `c̃ > 0`, `c̃ ≥ 12 S`, and `0 < β₁ < β₂ < 1`, there exist `A > 0`
and `T > 0` such that `g = A Ξ_{β₁} - Ξ_{β₂}` is strictly feasible at `(c̃ / 12, T)`. -/
theorem explicit_feasible_thermal_test (prob : FixedWeightProblem) {cTilde β₁ β₂ : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂ : β₂ < 1) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      prob.IsFeasible (cTilde / 12) T (fun t => A * thermalDiff prob.w β₁ t - thermalDiff prob.w β₂ t) := by
  let a : ℝ := cTilde / 12
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have ha : prob.totalShift ≤ a := by dsimp [a]; linarith
  have hβ₂_pos : 0 < β₂ := hβ₁.trans hβ₁₂
  have hβ₁_lt1 : β₁ < 1 := hβ₁₂.trans hβ₂
  have hv1 : prob.gVac a (thermalDiff prob.w β₁) < 0 :=
    gVac_thermalDiff_neg prob ha_pos hβ₁ hβ₁_lt1
  have hv2 : prob.gVac a (thermalDiff prob.w β₂) < 0 :=
    gVac_thermalDiff_neg prob ha_pos hβ₂_pos hβ₂
  let A : ℝ := (-prob.gVac a (thermalDiff prob.w β₂)) / (2 * (-prob.gVac a (thermalDiff prob.w β₁)))
  have hA_pos : 0 < A := div_pos (by linarith) (by linarith)
  let g : ℝ → ℝ := fun t => A * thermalDiff prob.w β₁ t - thermalDiff prob.w β₂ t
  have hg_eq : g = fun t => A * thermalDiff prob.w β₁ t + (-1) * thermalDiff prob.w β₂ t := by
    ext t; ring
  have hg_mem : TestClass prob a g := by
    rw [hg_eq]
    exact ((thermalDiff_mem_TestClass prob ha hβ₁).smul A).add
      ((thermalDiff_mem_TestClass prob ha hβ₂_pos).smul (-1))
  have hg_vac : 0 < prob.gVac a g := by
    have h1 := (thermalDiff_mem_TestClass prob ha hβ₁).smul A
    have h2 := (thermalDiff_mem_TestClass prob ha hβ₂_pos).smul (-1)
    rw [hg_eq, prob.gVac_add h1 h2, prob.gVac_smul A (thermalDiff_mem_TestClass prob ha hβ₁),
      prob.gVac_smul (-1) (thermalDiff_mem_TestClass prob ha hβ₂_pos)]
    have hA_mul : A * (-prob.gVac a (thermalDiff prob.w β₁)) =
        (-prob.gVac a (thermalDiff prob.w β₂)) / 2 := by
      dsimp [A]; field_simp [hv1.ne]
    linarith
  let c₁ : ℝ := 2 * π * (β₂ - β₁)
  let c₂ : ℝ := 2 * π * (1 / β₁ - β₁)
  have hc₁_pos : 0 < c₁ := by dsimp [c₁]; nlinarith [Real.pi_pos]
  have hc₂_pos : 0 < c₂ := by
    dsimp [c₂]
    have : β₁ < 1 / β₁ := by rw [lt_div_iff₀ hβ₁]; nlinarith
    nlinarith [Real.pi_pos]
  let T₁ : ℝ := Real.log (2 / A) / c₁
  let T₂ : ℝ := Real.log (2 * β₁ ^ (-(prob.w : ℝ))) / c₂
  let T : ℝ := max 1 (max T₁ T₂)
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨A, T, hA_pos, hT_pos, hg_mem, hg_vac, fun t ht => ?_⟩
  have ht1 : T₁ ≤ t := (le_max_left _ _ |>.trans (le_max_right _ _)).trans ht
  have ht2 : T₂ ≤ t := (le_max_right _ _ |>.trans (le_max_right _ _)).trans ht
  have ht_pos : 0 < t := lt_of_lt_of_le hT_pos ht
  have hexp1 : Real.exp (-2 * π * β₂ * t) ≤ (A / 2) * Real.exp (-2 * π * β₁ * t) := by
    have hlog : Real.log (2 / A) ≤ c₁ * t := by
      have := (div_le_iff₀ hc₁_pos).mp ht1
      linarith
    have hle : 2 / A ≤ Real.exp (c₁ * t) := by
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    have hle' : Real.exp (-(c₁ * t)) ≤ A / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
      simpa [inv_div] using hle
    have eadd : -2 * π * β₂ * t = -2 * π * β₁ * t + -(c₁ * t) := by dsimp [c₁]; ring
    rw [eadd, Real.exp_add]
    calc Real.exp (-2 * π * β₁ * t) * Real.exp (-(c₁ * t))
        ≤ Real.exp (-2 * π * β₁ * t) * (A / 2) :=
          mul_le_mul_of_nonneg_left hle' (Real.exp_pos _).le
      _ = (A / 2) * Real.exp (-2 * π * β₁ * t) := mul_comm _ _
  have hexp2 : β₁ ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β₁) ≤
      (1 / 2) * Real.exp (-2 * π * β₁ * t) := by
    have hbw_pos : 0 < β₁ ^ (-(prob.w : ℝ)) := Real.rpow_pos_of_pos hβ₁ _
    have hlog : Real.log (2 * β₁ ^ (-(prob.w : ℝ))) ≤ c₂ * t := by
      have := (div_le_iff₀ hc₂_pos).mp ht2
      linarith
    have hle : 2 * β₁ ^ (-(prob.w : ℝ)) ≤ Real.exp (c₂ * t) := by
      have := Real.exp_le_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at this
    have hle' : β₁ ^ (-(prob.w : ℝ)) * Real.exp (-(c₂ * t)) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      linarith
    have eadd : -2 * π * t / β₁ = -2 * π * β₁ * t + -(c₂ * t) := by
      dsimp [c₂]; field_simp [hβ₁.ne']; ring
    rw [eadd, Real.exp_add]
    calc β₁ ^ (-(prob.w : ℝ)) * (Real.exp (-2 * π * β₁ * t) * Real.exp (-(c₂ * t)))
        = (β₁ ^ (-(prob.w : ℝ)) * Real.exp (-(c₂ * t))) * Real.exp (-2 * π * β₁ * t) := by ring
      _ ≤ (1 / 2) * Real.exp (-2 * π * β₁ * t) :=
          mul_le_mul_of_nonneg_right hle' (Real.exp_pos _).le
  have hterm_nn : 0 ≤ β₂ ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * t / β₂) := by positivity
  dsimp [g]; unfold thermalDiff
  nlinarith

/-- **Finiteness `0 ≤ T_V < ∞`** for every fixed `(w, Q)` and `c̃ > 0`, `c̃ ≥ 12 S`,
via the explicit thermal test `A Ξ_{1/4} - Ξ_{1/2}`. -/
theorem T_V_lt_top (prob : FixedWeightProblem) {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde) :
    0 ≤ prob.T_V cTilde ∧
      ∃ T : ℝ, 0 < T ∧ (∃ g, prob.IsFeasible (cTilde / 12) T g) ∧ prob.T_V cTilde ≤ T := by
  obtain ⟨A, T, _, hT_pos, hg⟩ :=
    explicit_feasible_thermal_test prob hc_pos hc (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hne : {T' : ℝ | 0 < T' ∧ ∃ g', prob.IsFeasible (cTilde / 12) T' g'}.Nonempty :=
    ⟨T, hT_pos, _, hg⟩
  have hnn : 0 ≤ prob.T_V cTilde := by
    unfold FixedWeightProblem.T_V
    exact le_csInf hne fun T' hT' => hT'.1.le
  have hle : prob.T_V cTilde ≤ T := by
    unfold FixedWeightProblem.T_V
    exact csInf_le ⟨0, fun T' hT' => hT'.1.le⟩ ⟨hT_pos, _, hg⟩
  exact ⟨hnn, T, hT_pos, ⟨_, hg⟩, hle⟩

/-! ### Section 3: Full Proposition D1 (`ds:D1`) and measure-form D1 sum rules -/

/-- **Proposition D1 (full form, `dual_spectrum.tex`, `ds:D1`)** for every fixed weight `(w, Q)`:
if `meas` is a crossing measure at gap `τ > 0` for `a = c̃ / 12` (`c̃ > 0`, `c̃ ≥ 12 S`), then:
1. no `g ∈ \overline{\mathcal A}_w` is feasible at any `T ≤ τ`, hence `τ ≤ T_V(c̃)` and
   `c̃ / 12 + τ ≤ Δ_best(c̃)`;
2. exact measure-form D1 sum rule: if `g ∈ \overline{\mathcal A}_w` satisfies
   `|g(t)| ≤ C_g (1 + t)^{-q} e^{-4π √(a t)}` with `q > (w + 1) / 2`, then
   `∫ |g| dν < ∞` and `∫ g dν = -g_vac`;
3. one-sided measure-form D1 sum rule: if `g ∈ \overline{\mathcal A}_w` satisfies `g ≥ 0` on
   `[τ, ∞)`, then `0 ≤ ∫ g dν ≤ -g_vac`, and `g_vac ≥ 0` forces `g = 0` `ν`-a.e. -/
theorem proposition_D1 (prob : FixedWeightProblem)
    {cTilde τ : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) (hc_pos : 0 < cTilde) (hτ : 0 < τ)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) (hgap : IsAtGap meas τ) :
    (∀ T ≤ τ, ∀ g, ¬ prob.IsFeasible (cTilde / 12) T g) ∧
      τ ≤ prob.T_V cTilde ∧
      cTilde / 12 + τ ≤ prob.Delta_best cTilde ∧
      (∀ {g : ℝ → ℝ} {q C_g : ℝ},
        TestClass prob (cTilde / 12) g →
        (prob.w + 1 : ℝ) / 2 < q →
        0 ≤ C_g →
        (∀ t, 0 ≤ t → |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt ((cTilde / 12) * t))) →
        IntegrableOn g (Ici 0) meas.ν ∧ ∫ t in Ici 0, g t ∂meas.ν = -prob.gVac (cTilde / 12) g) ∧
      (∀ {g : ℝ → ℝ},
        TestClass prob (cTilde / 12) g →
        (∀ t, τ ≤ t → 0 ≤ g t) →
        IntegrableOn g (Ici 0) meas.ν ∧
          0 ≤ ∫ t in Ici 0, g t ∂meas.ν ∧
          ∫ t in Ici 0, g t ∂meas.ν ≤ -prob.gVac (cTilde / 12) g ∧
          (0 ≤ prob.gVac (cTilde / 12) g → ∀ᵐ t ∂meas.ν, g t = 0)) := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha_pos : 0 < cTilde / 12 := by linarith
  obtain ⟨hnone, hTV, hDelta⟩ := Duality.proposition_D1 prob hc hc_pos hτ ⟨meas, hgap⟩
  refine ⟨hnone, hTV, hDelta, ?_, ?_⟩
  · intro g q C_g hg hq hCg hdecay
    obtain ⟨hint, heq⟩ := Duality.proposition_P1 prob ha ha_pos meas hg hq hCg hdecay
    exact ⟨hint, by linarith⟩
  · intro g hg hg_nn
    obtain ⟨hint, h0, hle, hzero⟩ := Duality.proposition_P2 prob ha ha_pos meas hτ hgap hg hg_nn
    exact ⟨hint, h0, hle, fun hv => (hzero hv).2⟩

/-- **Comb decay implies D1 sum rule** (`dual_spectrum.tex`, Corollary E1 proof):
any test `g ∈ \overline{\mathcal A}_w` with `|g(t)| ≤ C e^{-4π √(a t) - π √(3t / c̃)}`
(`a = c̃ / 12`, `t = c̃ x² / 3`, i.e. `C e^{-c̃ L(x) - π x}`) satisfies the D1 sum rule decay
hypothesis with `q = (w + 2) / 2 > (w + 1) / 2`, hence `∫ g dν = -g_vac`. -/
theorem sumRule_of_comb_decay (prob : FixedWeightProblem)
    {cTilde : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) (hc_pos : 0 < cTilde)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12))
    {g : ℝ → ℝ} (hg : TestClass prob (cTilde / 12) g)
    {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ t, 0 ≤ t →
      |g t| ≤ C * Real.exp (-4 * π * Real.sqrt ((cTilde / 12) * t) - π * Real.sqrt (3 * t / cTilde))) :
    IntegrableOn g (Ici 0) meas.ν ∧
      ∫ t in Ici 0, g t ∂meas.ν = -prob.gVac (cTilde / 12) g := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha_pos : 0 < cTilde / 12 := by linarith
  let k : ℕ := prob.w + 2
  let q : ℝ := (k : ℝ) / 2
  have hq : (prob.w + 1 : ℝ) / 2 < q := by
    dsimp [q, k]; push_cast; linarith
  let d : ℝ := π * Real.sqrt (3 / cTilde)
  have hd_pos : 0 < d := by dsimp [d]; positivity
  let C_g : ℝ := C * ((k.factorial : ℝ) / d ^ k * Real.exp d)
  have hC_g : 0 ≤ C_g := by positivity
  have hpoly : ∀ t : ℝ, 0 ≤ t →
      Real.exp (-π * Real.sqrt (3 * t / cTilde)) ≤
        ((k.factorial : ℝ) / d ^ k * Real.exp d) * (1 + t) ^ (-q) := by
    intro t ht
    have hsqrt_t : Real.sqrt (3 * t / cTilde) = Real.sqrt (3 / cTilde) * Real.sqrt t := by
      rw [show 3 * t / cTilde = (3 / cTilde) * t by ring, Real.sqrt_mul (by positivity)]
    have hpi_eq : π * Real.sqrt (3 * t / cTilde) = d * Real.sqrt t := by
      dsimp [d]; rw [hsqrt_t]; ring
    have h1t : 1 + t ≤ (1 + Real.sqrt t) ^ 2 := by
      have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
      nlinarith [Real.sqrt_nonneg t]
    have hpow_le : (1 + t) ^ q ≤ (1 + Real.sqrt t) ^ k := by
      calc (1 + t) ^ q ≤ ((1 + Real.sqrt t) ^ 2) ^ q :=
            Real.rpow_le_rpow (by positivity) h1t (by positivity)
        _ = (1 + Real.sqrt t) ^ (((2 : ℕ) : ℝ) * q) := by
            rw [← Real.rpow_natCast (1 + Real.sqrt t) 2, ← Real.rpow_mul (by positivity)]
        _ = (1 + Real.sqrt t) ^ (k : ℝ) := by
            rw [show ((2 : ℕ) : ℝ) * q = (k : ℝ) by dsimp [q]; ring]
        _ = (1 + Real.sqrt t) ^ k := Real.rpow_natCast _ k
    have hexp_ser : (d * (1 + Real.sqrt t)) ^ k / (k.factorial : ℝ) ≤
        Real.exp (d * (1 + Real.sqrt t)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      exact (Real.summable_pow_div_factorial _).le_tsum k fun j _ => by positivity
    have hbound1 : (1 + Real.sqrt t) ^ k * Real.exp (-(d * Real.sqrt t)) ≤
        (k.factorial : ℝ) / d ^ k * Real.exp d := by
      have hmul : (1 + Real.sqrt t) ^ k ≤
          (k.factorial : ℝ) / d ^ k * Real.exp (d * (1 + Real.sqrt t)) := by
        rw [mul_pow] at hexp_ser
        have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
        have hd_pow_pos : 0 < d ^ k := by positivity
        calc (1 + Real.sqrt t) ^ k
            = ((k.factorial : ℝ) / d ^ k) * (d ^ k * (1 + Real.sqrt t) ^ k / (k.factorial : ℝ)) := by
              field_simp
          _ ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * (1 + Real.sqrt t)) :=
              mul_le_mul_of_nonneg_left hexp_ser (by positivity)
      calc (1 + Real.sqrt t) ^ k * Real.exp (-(d * Real.sqrt t))
          ≤ ((k.factorial : ℝ) / d ^ k * Real.exp (d * (1 + Real.sqrt t))) *
              Real.exp (-(d * Real.sqrt t)) :=
            mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
        _ = (k.factorial : ℝ) / d ^ k * Real.exp d := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hbound2 : (1 + t) ^ q * Real.exp (-π * Real.sqrt (3 * t / cTilde)) ≤
        (k.factorial : ℝ) / d ^ k * Real.exp d := by
      rw [show -π * Real.sqrt (3 * t / cTilde) = -(d * Real.sqrt t) by rw [← hpi_eq]; ring]
      exact (mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le).trans hbound1
    have h1t_pos : 0 < (1 + t) ^ q := Real.rpow_pos_of_pos (by linarith) q
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ h1t_pos]
    linarith [hbound2]
  obtain ⟨hint, heq⟩ := Duality.proposition_P1 prob ha ha_pos meas hg hq hC_g fun t ht => by
    have h1 := hdecay t ht
    have h2 := hpoly t ht
    have hsplit : -4 * π * Real.sqrt ((cTilde / 12) * t) - π * Real.sqrt (3 * t / cTilde) =
        -π * Real.sqrt (3 * t / cTilde) + -4 * π * Real.sqrt ((cTilde / 12) * t) := by ring
    rw [hsplit, Real.exp_add] at h1
    calc |g t| ≤ C * (Real.exp (-π * Real.sqrt (3 * t / cTilde)) *
            Real.exp (-4 * π * Real.sqrt ((cTilde / 12) * t))) := h1
      _ ≤ C * (((k.factorial : ℝ) / d ^ k * Real.exp d * (1 + t) ^ (-q)) *
            Real.exp (-4 * π * Real.sqrt ((cTilde / 12) * t))) := by gcongr
      _ = C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt ((cTilde / 12) * t)) := by
            dsimp [C_g]; ring
  exact ⟨hint, by linarith⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.gVac_thermalDiff_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.gVac_thermalDiff_neg

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.explicit_feasible_thermal_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.explicit_feasible_thermal_test

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.T_V_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.T_V_lt_top

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.proposition_D1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.proposition_D1

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.sumRule_of_comb_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.sumRule_of_comb_decay

end FormalResearch.ModularBootstrap.FixedWeight

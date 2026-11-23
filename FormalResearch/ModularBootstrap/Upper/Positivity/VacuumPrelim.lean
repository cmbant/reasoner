module

public import FormalResearch.ModularBootstrap.Upper.Window.WindowLimit
public import FormalResearch.ModularBootstrap.Upper.Window.CardyWindow
public import FormalResearch.ModularBootstrap.Upper.Positivity.DesignReal

/-!
# Preliminaries for Proposition V (`ut:Vac`): normalisation and signs

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition V (`ut:Vac`) and Lemma `T` (`ut:T`).

* `windowMeasureNormK_virasoro`: at `w = 1`, `Q = (1-q)²`, the measure normalisation `FK_c` of Lemma `W`
  (`windowMeasureNormK`) is `FK_c^{(1)} = FKc 1 1 c'` of `Window.Cardy`;
* `FKc_ge_mul_sqrt`: `FK_c ≫ √c'` (`FK_c ≍ c'^{5/6}`): for every `M`, `M √c' ≤ FK_c` for large `c'`;
* `designComb_re_nonpos_of_lt`: the design comb `B_D(x)` is a nonpositive real for `0 ≤ x < χ'_1`
  (its only real zero, simple, is `χ'_1`), the sign argument that drops the negative lobe.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes

lemma nullPoly_virasoro (q : ℝ) : Crossing.virasoroProblem.nullPoly q = (1 - q) ^ 2 := by
  unfold Crossing.FixedWeightProblem.nullPoly
  change ∏ l : Fin 2, (1 - q ^ (![1, 1] : Fin 2 → ℝ) l) = _
  rw [Fin.prod_univ_two]
  simp [sq]

/-- `FK_c` of Lemma `W` at `w = 1`, `Q = (1-q)²`, is `FKc 1 1 c'`. -/
theorem windowMeasureNormK_virasoro {c' : ℝ} (hc' : 0 < c') :
    windowMeasureNormK Crossing.virasoroProblem 1 c' = FKc 1 1 c' := by
  have hxi := xiStar_pos
  have hlam := lambdaComb_pos' hc'
  unfold windowMeasureNormK windowNormKTilde
  rw [FKc_one]
  unfold FVc
  simp only [Crossing.virasoroProblem_w, Nat.sub_self, pow_zero, one_mul, nullPoly_virasoro]
  have h3 : √(xiStar / 3) = √xiStar / √3 := Real.sqrt_div hxi.le 3
  rw [h3]
  have e : Real.exp (-4 * π * xiStar) = Real.exp (-(4 * π * xiStar)) := by ring_nf
  rw [e]
  have hexp : (2 * ((1 : ℕ) : ℝ) - 2 * (1 / 4)) = 3 / 2 := by norm_num
  have hexp' : (2 * (((1 : ℕ) : ℝ) - 1 / 4)) = 3 / 2 := by norm_num
  rw [hexp']
  have h3' : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  field_simp

lemma lambda_rpow_three_halves {l : ℝ} (hl : 0 < l) : l ^ (3 / 2 : ℝ) = l * √l := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hl.le (by norm_num)]
  norm_num

/-- `FK_c ≫ √c'`. -/
theorem FKc_ge_mul_sqrt (M : ℝ) : ∀ᶠ c' in atTop, M * √c' ≤ FKc 1 1 c' := by
  have hxi := xiStar_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = √xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 *
      (1 / cosh (π * xiStar / 2) ^ 2) / (√3 * π) * (2 * √2 / π) ^ (3 / 2 : ℝ) :=
    ⟨_, rfl⟩
  have hApos : 0 < A := by
    rw [hA]
    have := one_sub_exp_xiStar_pos
    positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (A / (|M| + 1)) ^ 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  filter_upwards [tendsto_lambdaComb_atTop.eventually_le_const hδpos, eventually_gt_atTop (0 : ℝ)]
    with c' hlc hc'
  have hlam := lambdaComb_pos' hc'
  have hsl : 0 < √(lambdaComb c') := Real.sqrt_pos.mpr hlam
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hc'
  have hform : FKc 1 1 c' = A * √c' / √(lambdaComb c') := by
    rw [FKc_one]
    unfold FVc
    have e2 : 2 * √2 / (π * lambdaComb c') = (2 * √2 / π) / lambdaComb c' := by
      field_simp
    rw [e2, Real.div_rpow (by positivity) hlam.le, lambda_rpow_three_halves hlam, hA]
    have h3' : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
    have := one_sub_exp_xiStar_pos
    have hπ := Real.pi_pos
    have hq : 0 < (2 * √2 / π : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    field_simp
  rw [hform, le_div_iff₀ hsl]
  have hs : √(lambdaComb c') ≤ A / (|M| + 1) := by
    rw [hδ] at hlc
    calc √(lambdaComb c') ≤ √((A / (|M| + 1)) ^ 2) := Real.sqrt_le_sqrt hlc
      _ = A / (|M| + 1) := Real.sqrt_sq (by positivity)
  have h1 : M ≤ |M| := le_abs_self M
  have h2 : (|M| + 1) * √(lambdaComb c') ≤ A := by
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ |M| + 1)
    rwa [mul_div_cancel₀ _ (by positivity : (|M| + 1 : ℝ) ≠ 0)] at this
  nlinarith [mul_pos hsc hsl]

/-- For `0 ≤ x < χ'_1` (first site, `f = 1`) and widths `ε_k ∈ [0, ∞)`, `B_D(x)` is a nonpositive real. -/
theorem designComb_re_nonpos_of_lt {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (N : ℕ) (σ ε : ℕ → ℝ) (hx0 : 0 ≤ x)
    (hx1 : x < designSite c' σ 1) :
    (designComb c' 1 N η₀ σ ε (x : ℂ)).re ≤ 0 := by
  obtain ⟨him, hre⟩ := combTail_real_nonneg hc' hη₀0 hη₀1 hgap N (x := x)
  have htail : combTail c' N η₀ (x : ℂ) = (((combTail c' N η₀ (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  set t : ℝ := (combTail c' N η₀ (x : ℂ)).re with ht
  set tf : ℝ := Real.tanh (π * (x - designSite c' σ 1) / 2) *
    Real.tanh (π * (x + designSite c' σ 1) / 2) with htf
  have hpi := Real.pi_pos
  have htf0 : tf ≤ 0 := by
    rw [htf]
    have h1 : Real.tanh (π * (x - designSite c' σ 1) / 2) < 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr (by nlinarith)) (Real.cosh_pos _)
    have h2 : 0 < Real.tanh (π * (x + designSite c' σ 1) / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by nlinarith)) (Real.cosh_pos _)
    exact mul_nonpos_of_nonpos_of_nonneg h1.le h2.le
  set q : ℝ := ∏ i ∈ Finset.range (N - 1),
    blaschkePairQ (designSite c' σ (1 + 1 + i)) (ε (1 + 1 + i)) x with hq
  have hq0 : 0 ≤ q := Finset.prod_nonneg fun i _ => by unfold blaschkePairQ; positivity
  have hD : designComb c' 1 N η₀ σ ε (x : ℂ) = ((tf * q * t : ℝ) : ℂ) := by
    unfold designComb
    rw [htail, blaschkeT_ofReal_eq]
    have hprod : (∏ i ∈ Finset.range (N - 1),
        pairT (designSite c' σ (1 + 1 + i)) (ε (1 + 1 + i)) (x : ℂ)) = (q : ℂ) := by
      rw [hq, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => pairT_ofReal _ _ _
    rw [hprod, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [hD, Complex.ofReal_re]
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg htf0 hq0) hre

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.windowMeasureNormK_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowMeasureNormK_virasoro

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.FKc_ge_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FKc_ge_mul_sqrt

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.designComb_re_nonpos_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designComb_re_nonpos_of_lt

end FormalResearch.ModularBootstrap.Upper.Positivity

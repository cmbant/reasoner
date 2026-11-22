module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus of Asymptotic Symbol Classes `𝒮_β` and `𝒬_β` (Lemma W.0)

Source: `CFT/sign_uncertainty/paper/ce_cr_airy_wkb_derivatives.tex`, §1, Lemma W.0 (`cecw:W0`).

## Main definitions
* `IsSymbolOn x₀ β F`: `F` is `C^∞` on `[x₀, ∞)` (`ContDiffOn ℝ ∞ F (Set.Ici x₀)`) and for every
  `j : ℕ`, there exists `C ≥ 0` such that `|iteratedDerivWithin j F (Set.Ici x₀) x| ≤ C * x ^ (-β - j)`
  for all `x ≥ x₀`.
* `IsSymbol β F`: `IsSymbolOn 1 β F` (the class `𝒮_β` on `[1, ∞)`).
* `IsWeightedSymbolOn x₀ β q F`: `F` is `C^∞` on `[x₀, ∞)` and for every `j : ℕ`, there exists
  `C ≥ 0` such that `|iteratedDerivWithin j F (Set.Ici x₀) x| ≤ C * q x * x ^ (-β - j)` for all
  `x ≥ x₀` (the weighted class `𝒬_β` on `[x₀, ∞)`).

Note: in Mathlib's `ℕ∞ω` convention (`open scoped ContDiff`), `∞` denotes `C^∞` smoothness while
`⊤ = ω` denotes real-analyticity.

## Main results (Lemma W.0)
* `IsSymbolOn.mul`, `IsSymbolOn.add`, `IsSymbolOn.sub`, `IsSymbolOn.const_mul`,
  `IsSymbolOn.derivWithin`, `IsSymbolOn.deriv`: closure of `𝒮_β` under products, linear
  combinations, and differentiation.
* `IsWeightedSymbolOn.mul_symbol`, `IsWeightedSymbolOn.of_symbol`, `IsWeightedSymbolOn.add`:
  `𝒬_β · 𝒮_γ ⊂ 𝒬_{β+γ}` and `q · 𝒮_β ⊂ 𝒬_β` when `q ∈ 𝒬₀`.
* `IsSymbolOn.comp_sub_zero`, `IsSymbolOn.comp_vanish_deriv`, `IsSymbolOn.comp_Ioi`:
  Lemma W.0(ii) (smooth composition on compact ranges around `0`, quadratic gain `2β` when
  `G(0) = G'(0) = 0`, and positive-domain variant on `(0, ∞)`).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace FormalResearch.Asymptotics

/-! ### Definitions -/

/-- The symbol class `𝒮_β` on `[x₀, ∞)`: `F` is `C^∞` on `[x₀, ∞)` and
`|F^{(j)}(x)| ≤ C_j x^{-β - j}` for all `j : ℕ` and `x ≥ x₀`. -/
def IsSymbolOn (x₀ β : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ F (Set.Ici x₀) ∧
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀,
      |iteratedDerivWithin j F (Set.Ici x₀) x| ≤ C * x ^ (-β - (j : ℝ))

/-- The standard symbol class `𝒮_β` on `[1, ∞)`. -/
def IsSymbol (β : ℝ) (F : ℝ → ℝ) : Prop := IsSymbolOn 1 β F

/-- The weighted symbol class `𝒬_β` on `[x₀, ∞)` with weight `q`: `F` is `C^∞` on `[x₀, ∞)` and
`|F^{(j)}(x)| ≤ C_j q(x) x^{-β - j}` for all `j : ℕ` and `x ≥ x₀`. -/
def IsWeightedSymbolOn (x₀ β : ℝ) (q F : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ F (Set.Ici x₀) ∧
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀,
      |iteratedDerivWithin j F (Set.Ici x₀) x| ≤ C * q x * x ^ (-β - (j : ℝ))

/-! ### Connecting `iteratedDerivWithin` on `Set.Ici x₀` with `iteratedDeriv` -/

lemma iteratedDerivWithin_Ici_eq_iteratedDeriv {x₀ x : ℝ} {F : ℝ → ℝ} (j : ℕ)
    (hF : ContDiffAt ℝ j F x) (hx : x₀ ≤ x) :
    iteratedDerivWithin j F (Set.Ici x₀) x = iteratedDeriv j F x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici x₀) hF hx

lemma iteratedDerivWithin_Ici_eq_iteratedDeriv_of_gt {x₀ x : ℝ} {F : ℝ → ℝ} (j : ℕ)
    (hF : ContDiffOn ℝ ∞ F (Set.Ici x₀)) (hx : x₀ < x) :
    iteratedDerivWithin j F (Set.Ici x₀) x = iteratedDeriv j F x :=
  iteratedDerivWithin_Ici_eq_iteratedDeriv j ((hF.contDiffAt (Ici_mem_nhds hx)).of_le (by simp))
    hx.le

lemma iteratedDerivWithin_Ici_eq_iteratedDeriv_of_contDiffOn_open {x₀ x : ℝ} {U : Set ℝ}
    {F : ℝ → ℝ} (j : ℕ) (hU : IsOpen U) (hsub : Set.Ici x₀ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hx : x₀ ≤ x) :
    iteratedDerivWithin j F (Set.Ici x₀) x = iteratedDeriv j F x :=
  iteratedDerivWithin_Ici_eq_iteratedDeriv j
    ((hF.contDiffAt (hU.mem_nhds (hsub hx))).of_le (by simp)) hx

lemma iteratedDerivWithin_Ici_mono {x₀ x₁ x : ℝ} {F : ℝ → ℝ} (j : ℕ) (hx₀₁ : x₀ ≤ x₁)
    (hF : ContDiffOn ℝ ∞ F (Set.Ici x₀)) (hx : x₁ ≤ x) :
    iteratedDerivWithin j F (Set.Ici x₁) x = iteratedDerivWithin j F (Set.Ici x₀) x := by
  rcases eq_or_lt_of_le hx₀₁ with rfl | hlt
  · rfl
  · have hlt' : x₀ < x := lt_of_lt_of_le hlt hx
    rw [iteratedDerivWithin_Ici_eq_iteratedDeriv_of_gt j hF hlt']
    exact iteratedDerivWithin_Ici_eq_iteratedDeriv j
      ((hF.contDiffAt (Ici_mem_nhds hlt')).of_le (by simp)) hx

lemma isSymbolOn_of_contDiffOn_open {x₀ β : ℝ} {U : Set ℝ} {F : ℝ → ℝ} (hU : IsOpen U)
    (hsub : Set.Ici x₀ ⊆ U) (hF : ContDiffOn ℝ ∞ F U)
    (hbd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀, |iteratedDeriv j F x| ≤ C * x ^ (-β - (j : ℝ))) :
    IsSymbolOn x₀ β F := by
  refine ⟨hF.mono hsub, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hbd j
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [iteratedDerivWithin_Ici_eq_iteratedDeriv_of_contDiffOn_open j hU hsub hF hx]
  exact h x hx

lemma IsSymbolOn.abs_le {x₀ β : ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀, |F x| ≤ C * x ^ (-β) := by
  obtain ⟨C, hC, h⟩ := hF.2 0
  exact ⟨C, hC, fun x hx => by simpa using h x hx⟩

lemma IsSymbolOn.iteratedDeriv_le_of_contDiffOn_open {x₀ β : ℝ} {U : Set ℝ} {F : ℝ → ℝ}
    (hF : IsSymbolOn x₀ β F) (hU : IsOpen U) (hsub : Set.Ici x₀ ⊆ U)
    (hFU : ContDiffOn ℝ ∞ F U) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀, |iteratedDeriv j F x| ≤ C * x ^ (-β - (j : ℝ)) := by
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [← iteratedDerivWithin_Ici_eq_iteratedDeriv_of_contDiffOn_open j hU hsub hFU hx]
  exact h x hx

lemma IsSymbolOn.congr {x₀ β : ℝ} {F G : ℝ → ℝ} (hFG : Set.EqOn F G (Set.Ici x₀))
    (hF : IsSymbolOn x₀ β F) : IsSymbolOn x₀ β G := by
  refine ⟨hF.1.congr fun x hx => (hFG hx).symm, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  exact ⟨C, hC, fun x hx => by rw [iteratedDerivWithin_congr (fun y hy => (hFG hy).symm) hx]; exact h x hx⟩

/-! ### Basic algebra and closure of `IsSymbolOn` -/

lemma IsSymbolOn.zero (x₀ β : ℝ) : IsSymbolOn x₀ β (fun _ => 0) :=
  ⟨contDiffOn_const, fun j => ⟨0, le_rfl, fun x _ => by simp⟩⟩

lemma IsSymbolOn.mono_exp {x₀ β γ : ℝ} {F : ℝ → ℝ} (hx₀ : 0 < x₀) (hβγ : β ≤ γ)
    (hF : IsSymbolOn x₀ γ F) : IsSymbolOn x₀ β F := by
  refine ⟨hF.1, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨C * x₀ ^ (β - γ), by positivity, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
  have hexp : x ^ (-γ - (j : ℝ)) = x ^ (β - γ) * x ^ (-β - (j : ℝ)) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  have hpow : x ^ (β - γ) ≤ x₀ ^ (β - γ) :=
    Real.rpow_le_rpow_of_nonpos hx₀ hx (sub_nonpos.mpr hβγ)
  calc |iteratedDerivWithin j F (Set.Ici x₀) x|
      ≤ C * x ^ (-γ - (j : ℝ)) := h x hx
    _ = C * x ^ (β - γ) * x ^ (-β - (j : ℝ)) := by rw [hexp]; ring
    _ ≤ C * x₀ ^ (β - γ) * x ^ (-β - (j : ℝ)) := by gcongr

lemma IsSymbolOn.mono_domain {x₀ x₁ β : ℝ} {F : ℝ → ℝ} (hx₀₁ : x₀ ≤ x₁)
    (hF : IsSymbolOn x₀ β F) : IsSymbolOn x₁ β F := by
  refine ⟨hF.1.mono (Ici_subset_Ici.mpr hx₀₁), fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [iteratedDerivWithin_Ici_mono j hx₀₁ hF.1 hx]
  exact h x (le_trans hx₀₁ hx)

lemma IsSymbolOn.const {x₀ β : ℝ} (hx₀ : 0 < x₀) (hβ : β ≤ 0) (c : ℝ) :
    IsSymbolOn x₀ β (fun _ => c) := by
  refine ⟨contDiffOn_const, fun j => ?_⟩
  cases j with
  | zero =>
    refine ⟨|c| * x₀ ^ β, by positivity, fun x hx => ?_⟩
    have hpow : x₀ ^ (-β) ≤ x ^ (-β) := Real.rpow_le_rpow hx₀.le hx (neg_nonneg.mpr hβ)
    have h1 : 1 ≤ x₀ ^ β * x ^ (-β) := by
      have hmul : x₀ ^ β * x₀ ^ (-β) = 1 := by
        rw [← Real.rpow_add hx₀, add_neg_cancel, Real.rpow_zero]
      calc (1 : ℝ) = x₀ ^ β * x₀ ^ (-β) := hmul.symm
        _ ≤ x₀ ^ β * x ^ (-β) := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx₀.le _)
    calc |iteratedDerivWithin 0 (fun _ => c) (Set.Ici x₀) x| = |c| * 1 := by simp
      _ ≤ |c| * (x₀ ^ β * x ^ (-β)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| * x₀ ^ β * x ^ (-β - (0 : ℕ)) := by simp; ring
  | succ j =>
    exact ⟨0, le_rfl, fun x _ => by simp [iteratedDerivWithin_const]⟩

private lemma iteratedDeriv_rpow_const_of_pos (p : ℝ) (j : ℕ) :
    ∀ {x : ℝ}, 0 < x →
      iteratedDeriv j (fun y : ℝ => y ^ p) x =
        (∏ i ∈ Finset.range j, (p - (i : ℝ))) * x ^ (p - (j : ℝ)) := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (fun y : ℝ => y ^ p) =ᶠ[𝓝 x]
        fun y : ℝ => (∏ i ∈ Finset.range j, (p - (i : ℝ))) * y ^ (p - (j : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [hev.deriv_eq]
    have hd : HasDerivAt
        (fun y : ℝ => (∏ i ∈ Finset.range j, (p - (i : ℝ))) * y ^ (p - (j : ℝ)))
        ((∏ i ∈ Finset.range j, (p - (i : ℝ))) * ((p - (j : ℝ)) * x ^ (p - (j : ℝ) - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul _
    rw [hd.deriv, Finset.prod_range_succ]
    push_cast; ring_nf

lemma IsSymbolOn.rpow {x₀ : ℝ} (hx₀ : 0 < x₀) (p : ℝ) :
    IsSymbolOn x₀ (-p) (fun x : ℝ => x ^ p) := by
  refine isSymbolOn_of_contDiffOn_open isOpen_Ioi (fun x hx => lt_of_lt_of_le hx₀ hx)
    (fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt) fun j => ?_
  refine ⟨|∏ i ∈ Finset.range j, (p - (i : ℝ))|, abs_nonneg _, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
  rw [iteratedDeriv_rpow_const_of_pos p j hxpos, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hxpos _), neg_neg]

lemma IsSymbolOn.rpow_neg {x₀ : ℝ} (hx₀ : 0 < x₀) (α : ℝ) :
    IsSymbolOn x₀ α (fun x : ℝ => x ^ (-α)) := by
  simpa using IsSymbolOn.rpow hx₀ (-α)

lemma IsSymbolOn.inv {x₀ : ℝ} (hx₀ : 0 < x₀) : IsSymbolOn x₀ 1 (fun x : ℝ => x⁻¹) :=
  (IsSymbolOn.rpow_neg hx₀ 1).congr fun x _ => by rw [Real.rpow_neg_one]

lemma IsSymbolOn.add_same {x₀ β : ℝ} {F G : ℝ → ℝ}
    (hF : IsSymbolOn x₀ β F) (hG : IsSymbolOn x₀ β G) :
    IsSymbolOn x₀ β (fun x => F x + G x) := by
  refine ⟨hF.1.add hG.1, fun j => ?_⟩
  obtain ⟨CF, hCF, hFbd⟩ := hF.2 j
  obtain ⟨CG, hCG, hGbd⟩ := hG.2 j
  refine ⟨CF + CG, add_nonneg hCF hCG, fun x hx => ?_⟩
  have hxI : x ∈ Set.Ici x₀ := hx
  rw [iteratedDerivWithin_fun_add hxI (uniqueDiffOn_Ici x₀)
    ((hF.1 x hx).of_le (by simp)) ((hG.1 x hx).of_le (by simp))]
  calc |iteratedDerivWithin j F (Set.Ici x₀) x + iteratedDerivWithin j G (Set.Ici x₀) x|
      ≤ |iteratedDerivWithin j F (Set.Ici x₀) x| + |iteratedDerivWithin j G (Set.Ici x₀) x| :=
        abs_add_le _ _
    _ ≤ CF * x ^ (-β - (j : ℝ)) + CG * x ^ (-β - (j : ℝ)) := add_le_add (hFbd x hx) (hGbd x hx)
    _ = (CF + CG) * x ^ (-β - (j : ℝ)) := by ring

lemma IsSymbolOn.add {x₀ β γ : ℝ} {F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsSymbolOn x₀ β F) (hG : IsSymbolOn x₀ γ G) :
    IsSymbolOn x₀ (min β γ) (fun x => F x + G x) :=
  (hF.mono_exp hx₀ (min_le_left β γ)).add_same (hG.mono_exp hx₀ (min_le_right β γ))

lemma IsSymbolOn.neg {x₀ β : ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F) :
    IsSymbolOn x₀ β (fun x => -F x) := by
  refine ⟨hF.1.neg, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  exact ⟨C, hC, fun x hx => by rw [iteratedDerivWithin_fun_neg, abs_neg]; exact h x hx⟩

lemma IsSymbolOn.sub {x₀ β γ : ℝ} {F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsSymbolOn x₀ β F) (hG : IsSymbolOn x₀ γ G) :
    IsSymbolOn x₀ (min β γ) (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hx₀ hG.neg

lemma IsSymbolOn.const_mul {x₀ β : ℝ} {F : ℝ → ℝ} (c : ℝ) (hF : IsSymbolOn x₀ β F) :
    IsSymbolOn x₀ β (fun x => c * F x) := by
  refine ⟨contDiffOn_const.mul hF.1, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨|c| * C, by positivity, fun x hx => ?_⟩
  rw [iteratedDerivWithin_const_mul_field, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx) (abs_nonneg c)

lemma IsSymbolOn.mul_const {x₀ β : ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F) (c : ℝ) :
    IsSymbolOn x₀ β (fun x => F x * c) := by
  simpa only [mul_comm] using hF.const_mul c

private lemma leibniz_symbol_bound {x₀ β γ : ℝ} {F G q : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hFcd : ContDiffOn ℝ ∞ F (Set.Ici x₀)) (hGcd : ContDiffOn ℝ ∞ G (Set.Ici x₀))
    {CF CG : ℕ → ℝ} (hCF_nn : ∀ j, 0 ≤ CF j) (hCG_nn : ∀ j, 0 ≤ CG j)
    (hFbd : ∀ j, ∀ x ≥ x₀, |iteratedDerivWithin j F (Set.Ici x₀) x| ≤ CF j * q x * x ^ (-β - (j : ℝ)))
    (hGbd : ∀ j, ∀ x ≥ x₀, |iteratedDerivWithin j G (Set.Ici x₀) x| ≤ CG j * x ^ (-γ - (j : ℝ)))
    (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀,
      |iteratedDerivWithin j (fun y => F y * G y) (Set.Ici x₀) x| ≤
        C * q x * x ^ (-(β + γ) - (j : ℝ)) := by
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * CF i * CG (j - i),
    Finset.sum_nonneg fun i _ => by positivity [hCF_nn i, hCG_nn (j - i)], fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
  have hxI : x ∈ Set.Ici x₀ := hx
  have hleib := iteratedDerivWithin_mul (n := j) hxI (uniqueDiffOn_Ici x₀)
    ((hFcd x hx).of_le (by simp)) ((hGcd x hx).of_le (by simp))
  change |iteratedDerivWithin j (F * G) (Set.Ici x₀) x| ≤ _
  rw [hleib]
  calc |∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * iteratedDerivWithin i F (Set.Ici x₀) x *
        iteratedDerivWithin (j - i) G (Set.Ici x₀) x|
      ≤ ∑ i ∈ Finset.range (j + 1), |(j.choose i : ℝ) * iteratedDerivWithin i F (Set.Ici x₀) x *
        iteratedDerivWithin (j - i) G (Set.Ici x₀) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * CF i * CG (j - i)) * q x * x ^ (-(β + γ) - (j : ℝ)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have h1 := hFbd i x hx
        have h2 := hGbd (j - i) x hx
        have hmul := mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        have hexp : x ^ (-β - (i : ℝ)) * x ^ (-γ - ((j - i : ℕ) : ℝ)) =
            x ^ (-(β + γ) - (j : ℝ)) := by
          rw [← Real.rpow_add hxpos, Nat.cast_sub hij]; congr 1; ring
        calc (j.choose i : ℝ) * |iteratedDerivWithin i F (Set.Ici x₀) x| *
              |iteratedDerivWithin (j - i) G (Set.Ici x₀) x|
            = (j.choose i : ℝ) * (|iteratedDerivWithin i F (Set.Ici x₀) x| *
                |iteratedDerivWithin (j - i) G (Set.Ici x₀) x|) := by ring
          _ ≤ (j.choose i : ℝ) * ((CF i * q x * x ^ (-β - (i : ℝ))) *
                (CG (j - i) * x ^ (-γ - ((j - i : ℕ) : ℝ)))) :=
              mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
          _ = ((j.choose i : ℝ) * CF i * CG (j - i)) * q x *
                (x ^ (-β - (i : ℝ)) * x ^ (-γ - ((j - i : ℕ) : ℝ))) := by ring
          _ = ((j.choose i : ℝ) * CF i * CG (j - i)) * q x * x ^ (-(β + γ) - (j : ℝ)) := by
              rw [hexp]
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * CF i * CG (j - i)) *
          q x * x ^ (-(β + γ) - (j : ℝ)) := by simp_rw [Finset.sum_mul]

/-- **Lemma W.0(i)** (product rule for `𝒮_β`): `𝒮_β · 𝒮_γ ⊂ 𝒮_{β+γ}`. -/
theorem IsSymbolOn.mul {x₀ β γ : ℝ} {F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsSymbolOn x₀ β F) (hG : IsSymbolOn x₀ γ G) :
    IsSymbolOn x₀ (β + γ) (fun x => F x * G x) := by
  refine ⟨hF.1.mul hG.1, fun j => ?_⟩
  choose CF hCF_nn hCF using hF.2
  choose CG hCG_nn hCG using hG.2
  have hbd := leibniz_symbol_bound (q := fun _ => (1 : ℝ)) hx₀ hF.1 hG.1 hCF_nn hCG_nn
    (fun k x hx => by simpa only [mul_one] using hCF k x hx) hCG j
  simpa only [mul_one] using hbd

lemma IsSymbolOn.pow {x₀ β : ℝ} {F : ℝ → ℝ} (hx₀ : 0 < x₀) (hF : IsSymbolOn x₀ β F) (k : ℕ) :
    IsSymbolOn x₀ ((k : ℝ) * β) (fun x => F x ^ k) := by
  induction k with
  | zero => simpa using IsSymbolOn.const hx₀ le_rfl (1 : ℝ)
  | succ k ih =>
    have e : (fun x => F x ^ (k + 1)) = (fun x => F x ^ k * F x) := by ext x; rw [pow_succ]
    rw [e, Nat.cast_succ, add_mul, one_mul]
    exact ih.mul hx₀ hF

/-- Differentiation in `𝒮_β`: `F ∈ 𝒮_β ⇒ derivWithin F [x₀, ∞) ∈ 𝒮_{β+1}`. -/
theorem IsSymbolOn.derivWithin {x₀ β : ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F) :
    IsSymbolOn x₀ (β + 1) (_root_.derivWithin F (Set.Ici x₀)) := by
  refine ⟨hF.1.derivWithin (uniqueDiffOn_Ici x₀) (by simp), fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 (j + 1)
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [← iteratedDerivWithin_succ' (f := F) (s := Set.Ici x₀) (n := j)]
  have hexp : -(β + 1) - (j : ℝ) = -β - ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hexp]
  exact h x hx

lemma IsSymbolOn.deriv {x₀ β : ℝ} {U : Set ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F)
    (hU : IsOpen U) (hsub : Set.Ici x₀ ⊆ U) (hFU : ContDiffOn ℝ ∞ F U) :
    IsSymbolOn x₀ (β + 1) (_root_.deriv F) := by
  refine hF.derivWithin.congr fun x hx => ?_
  exact ((hFU.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici x₀ x hx)

lemma IsSymbolOn.deriv_of_contDiff {x₀ β : ℝ} {F : ℝ → ℝ} (hF : IsSymbolOn x₀ β F)
    (hFU : ContDiff ℝ ∞ F) : IsSymbolOn x₀ (β + 1) (_root_.deriv F) :=
  hF.deriv isOpen_univ (subset_univ _) hFU.contDiffOn

/-! ### Wrappers for `IsSymbol` (`x₀ = 1`) -/

lemma IsSymbol.to_isSymbolOn {x₀ β : ℝ} {F : ℝ → ℝ} (hx₀ : 1 ≤ x₀) (hF : IsSymbol β F) :
    IsSymbolOn x₀ β F := hF.mono_domain hx₀

lemma IsSymbol.congr {β : ℝ} {F G : ℝ → ℝ} (hFG : Set.EqOn F G (Set.Ici 1))
    (hF : IsSymbol β F) : IsSymbol β G := IsSymbolOn.congr hFG hF

lemma IsSymbol.abs_le {β : ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 1, |F x| ≤ C * x ^ (-β) := IsSymbolOn.abs_le hF

lemma IsSymbol.mono_exp {β γ : ℝ} {F : ℝ → ℝ} (hβγ : β ≤ γ) (hF : IsSymbol γ F) :
    IsSymbol β F := IsSymbolOn.mono_exp zero_lt_one hβγ hF

lemma IsSymbol.const {β : ℝ} (hβ : β ≤ 0) (c : ℝ) : IsSymbol β (fun _ => c) :=
  IsSymbolOn.const zero_lt_one hβ c

lemma IsSymbol.rpow (p : ℝ) : IsSymbol (-p) (fun x : ℝ => x ^ p) :=
  IsSymbolOn.rpow zero_lt_one p

lemma IsSymbol.rpow_neg (α : ℝ) : IsSymbol α (fun x : ℝ => x ^ (-α)) :=
  IsSymbolOn.rpow_neg zero_lt_one α

lemma IsSymbol.inv : IsSymbol 1 (fun x : ℝ => x⁻¹) := IsSymbolOn.inv zero_lt_one

lemma IsSymbol.add {β γ : ℝ} {F G : ℝ → ℝ} (hF : IsSymbol β F) (hG : IsSymbol γ G) :
    IsSymbol (min β γ) (fun x => F x + G x) := IsSymbolOn.add zero_lt_one hF hG

lemma IsSymbol.neg {β : ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F) :
    IsSymbol β (fun x => -F x) := IsSymbolOn.neg hF

lemma IsSymbol.sub {β γ : ℝ} {F G : ℝ → ℝ} (hF : IsSymbol β F) (hG : IsSymbol γ G) :
    IsSymbol (min β γ) (fun x => F x - G x) := IsSymbolOn.sub zero_lt_one hF hG

lemma IsSymbol.const_mul {β : ℝ} {F : ℝ → ℝ} (c : ℝ) (hF : IsSymbol β F) :
    IsSymbol β (fun x => c * F x) := IsSymbolOn.const_mul c hF

lemma IsSymbol.mul {β γ : ℝ} {F G : ℝ → ℝ} (hF : IsSymbol β F) (hG : IsSymbol γ G) :
    IsSymbol (β + γ) (fun x => F x * G x) := IsSymbolOn.mul zero_lt_one hF hG

lemma IsSymbol.pow {β : ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F) (k : ℕ) :
    IsSymbol ((k : ℝ) * β) (fun x => F x ^ k) := IsSymbolOn.pow zero_lt_one hF k

lemma IsSymbol.derivWithin {β : ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F) :
    IsSymbol (β + 1) (_root_.derivWithin F (Set.Ici 1)) := IsSymbolOn.derivWithin hF

lemma IsSymbol.deriv {β : ℝ} {U : Set ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F)
    (hU : IsOpen U) (hsub : Set.Ici 1 ⊆ U) (hFU : ContDiffOn ℝ ∞ F U) :
    IsSymbol (β + 1) (_root_.deriv F) := IsSymbolOn.deriv hF hU hsub hFU

lemma IsSymbol.deriv_of_contDiff {β : ℝ} {F : ℝ → ℝ} (hF : IsSymbol β F)
    (hFU : ContDiff ℝ ∞ F) : IsSymbol (β + 1) (_root_.deriv F) :=
  IsSymbolOn.deriv_of_contDiff hF hFU

/-! ### Weighted symbol class `IsWeightedSymbolOn` (`𝒬_β`) -/

lemma IsWeightedSymbolOn.zero (x₀ β : ℝ) (q : ℝ → ℝ) :
    IsWeightedSymbolOn x₀ β q (fun _ => 0) :=
  ⟨contDiffOn_const, fun j => ⟨0, le_rfl, fun x _ => by simp⟩⟩

lemma IsWeightedSymbolOn.congr {x₀ β : ℝ} {q F G : ℝ → ℝ} (hFG : Set.EqOn F G (Set.Ici x₀))
    (hF : IsWeightedSymbolOn x₀ β q F) : IsWeightedSymbolOn x₀ β q G := by
  refine ⟨hF.1.congr fun x hx => (hFG hx).symm, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  exact ⟨C, hC, fun x hx => by rw [iteratedDerivWithin_congr (fun y hy => (hFG hy).symm) hx]; exact h x hx⟩

lemma IsWeightedSymbolOn.mono_exp {x₀ β γ : ℝ} {q F : ℝ → ℝ} (hx₀ : 0 < x₀) (hβγ : β ≤ γ)
    (hF : IsWeightedSymbolOn x₀ γ q F) : IsWeightedSymbolOn x₀ β q F := by
  refine ⟨hF.1, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨C * x₀ ^ (β - γ), by positivity, fun x hx => ?_⟩
  have hxj := h x hx
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · simpa only [zero_mul] using hxj
  · have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
    have hqnn : 0 ≤ q x := nonneg_of_mul_nonneg_right
      (by linarith [le_trans (abs_nonneg _) hxj]) (mul_pos hCpos (Real.rpow_pos_of_pos hxpos _))
    have hexp : x ^ (-γ - (j : ℝ)) = x ^ (β - γ) * x ^ (-β - (j : ℝ)) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    have hpow : x ^ (β - γ) ≤ x₀ ^ (β - γ) :=
      Real.rpow_le_rpow_of_nonpos hx₀ hx (sub_nonpos.mpr hβγ)
    calc |iteratedDerivWithin j F (Set.Ici x₀) x|
        ≤ C * q x * x ^ (-γ - (j : ℝ)) := hxj
      _ = C * q x * x ^ (β - γ) * x ^ (-β - (j : ℝ)) := by rw [hexp]; ring
      _ ≤ C * q x * x₀ ^ (β - γ) * x ^ (-β - (j : ℝ)) := by gcongr
      _ = C * x₀ ^ (β - γ) * q x * x ^ (-β - (j : ℝ)) := by ring

lemma IsWeightedSymbolOn.mono_domain {x₀ x₁ β : ℝ} {q F : ℝ → ℝ} (hx₀₁ : x₀ ≤ x₁)
    (hF : IsWeightedSymbolOn x₀ β q F) : IsWeightedSymbolOn x₁ β q F := by
  refine ⟨hF.1.mono (Ici_subset_Ici.mpr hx₀₁), fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [iteratedDerivWithin_Ici_mono j hx₀₁ hF.1 hx]
  exact h x (le_trans hx₀₁ hx)

lemma IsWeightedSymbolOn.add_same {x₀ β : ℝ} {q F G : ℝ → ℝ}
    (hF : IsWeightedSymbolOn x₀ β q F) (hG : IsWeightedSymbolOn x₀ β q G) :
    IsWeightedSymbolOn x₀ β q (fun x => F x + G x) := by
  refine ⟨hF.1.add hG.1, fun j => ?_⟩
  obtain ⟨CF, hCF, hFbd⟩ := hF.2 j
  obtain ⟨CG, hCG, hGbd⟩ := hG.2 j
  refine ⟨CF + CG, add_nonneg hCF hCG, fun x hx => ?_⟩
  have hxI : x ∈ Set.Ici x₀ := hx
  rw [iteratedDerivWithin_fun_add hxI (uniqueDiffOn_Ici x₀)
    ((hF.1 x hx).of_le (by simp)) ((hG.1 x hx).of_le (by simp))]
  calc |iteratedDerivWithin j F (Set.Ici x₀) x + iteratedDerivWithin j G (Set.Ici x₀) x|
      ≤ |iteratedDerivWithin j F (Set.Ici x₀) x| + |iteratedDerivWithin j G (Set.Ici x₀) x| :=
        abs_add_le _ _
    _ ≤ CF * q x * x ^ (-β - (j : ℝ)) + CG * q x * x ^ (-β - (j : ℝ)) :=
        add_le_add (hFbd x hx) (hGbd x hx)
    _ = (CF + CG) * q x * x ^ (-β - (j : ℝ)) := by ring

lemma IsWeightedSymbolOn.add {x₀ β γ : ℝ} {q F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsWeightedSymbolOn x₀ β q F) (hG : IsWeightedSymbolOn x₀ γ q G) :
    IsWeightedSymbolOn x₀ (min β γ) q (fun x => F x + G x) :=
  (hF.mono_exp hx₀ (min_le_left β γ)).add_same (hG.mono_exp hx₀ (min_le_right β γ))

lemma IsWeightedSymbolOn.neg {x₀ β : ℝ} {q F : ℝ → ℝ}
    (hF : IsWeightedSymbolOn x₀ β q F) : IsWeightedSymbolOn x₀ β q (fun x => -F x) := by
  refine ⟨hF.1.neg, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  exact ⟨C, hC, fun x hx => by rw [iteratedDerivWithin_fun_neg, abs_neg]; exact h x hx⟩

lemma IsWeightedSymbolOn.sub {x₀ β γ : ℝ} {q F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsWeightedSymbolOn x₀ β q F) (hG : IsWeightedSymbolOn x₀ γ q G) :
    IsWeightedSymbolOn x₀ (min β γ) q (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hx₀ hG.neg

lemma IsWeightedSymbolOn.const_mul {x₀ β : ℝ} {q F : ℝ → ℝ} (c : ℝ)
    (hF : IsWeightedSymbolOn x₀ β q F) : IsWeightedSymbolOn x₀ β q (fun x => c * F x) := by
  refine ⟨contDiffOn_const.mul hF.1, fun j => ?_⟩
  obtain ⟨C, hC, h⟩ := hF.2 j
  refine ⟨|c| * C, by positivity, fun x hx => ?_⟩
  rw [iteratedDerivWithin_const_mul_field, abs_mul]
  calc |c| * |iteratedDerivWithin j F (Set.Ici x₀) x|
      ≤ |c| * (C * q x * x ^ (-β - (j : ℝ))) := mul_le_mul_of_nonneg_left (h x hx) (abs_nonneg c)
    _ = |c| * C * q x * x ^ (-β - (j : ℝ)) := by ring

/-- **Lemma W.0(i)** (weighted product rule): `𝒬_β · 𝒮_γ ⊂ 𝒬_{β+γ}`. -/
theorem IsWeightedSymbolOn.mul_symbol {x₀ β γ : ℝ} {q F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsWeightedSymbolOn x₀ β q F) (hG : IsSymbolOn x₀ γ G) :
    IsWeightedSymbolOn x₀ (β + γ) q (fun x => F x * G x) := by
  refine ⟨hF.1.mul hG.1, fun j => ?_⟩
  choose CF hCF_nn hCF using hF.2
  choose CG hCG_nn hCG using hG.2
  exact leibniz_symbol_bound hx₀ hF.1 hG.1 hCF_nn hCG_nn hCF hCG j

lemma IsWeightedSymbolOn.symbol_mul {x₀ β γ : ℝ} {q F G : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hF : IsSymbolOn x₀ β F) (hG : IsWeightedSymbolOn x₀ γ q G) :
    IsWeightedSymbolOn x₀ (β + γ) q (fun x => F x * G x) := by
  simpa only [mul_comm, add_comm] using hG.mul_symbol hx₀ hF

/-- If `q ∈ 𝒬₀` and `F ∈ 𝒮_β`, then `q · F ∈ 𝒬_β`. -/
theorem IsWeightedSymbolOn.of_symbol {x₀ β : ℝ} {q F : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hq : IsWeightedSymbolOn x₀ 0 q q) (hF : IsSymbolOn x₀ β F) :
    IsWeightedSymbolOn x₀ β q (fun x => q x * F x) := by
  simpa only [zero_add] using hq.mul_symbol hx₀ hF

/-! ### Smooth composition — Lemma W.0(ii) -/

private lemma comp_deriv_bound_aux {x₀ β : ℝ} {U t : Set ℝ} {F : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F)
    (hU : IsOpen U) (htU : t ⊆ U) (hFt : ∀ x ≥ x₀, F x ∈ t) :
    ∀ n : ℕ, ∀ H : ℝ → ℝ, ContDiffOn ℝ ∞ H U →
      (∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ t, |_root_.iteratedDeriv k H y| ≤ M) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ x₀,
        |iteratedDerivWithin n (fun y => H (F y)) (Set.Ici x₀) x| ≤
          C * x ^ (-(if n = 0 then (0 : ℝ) else β) - (n : ℝ)) := by
  have hmaps : Set.MapsTo F (Set.Ici x₀) U := fun x hx => htU (hFt x hx)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hH hHbd
    cases n with
    | zero =>
      obtain ⟨M, hM_nn, hM⟩ := hHbd 0
      refine ⟨M, hM_nn, fun x hx => ?_⟩
      simp only [iteratedDerivWithin_zero, ↓reduceIte, neg_zero, Nat.cast_zero, sub_zero,
        Real.rpow_zero, mul_one]
      simpa using hM (F x) (hFt x hx)
    | succ m =>
      have hHderiv : ContDiffOn ℝ ∞ (_root_.deriv H) U := hH.deriv_of_isOpen hU (by simp)
      have hHderiv_bd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ t,
          |_root_.iteratedDeriv k (_root_.deriv H) y| ≤ M := fun k => by
        obtain ⟨M, hM_nn, hM⟩ := hHbd (k + 1)
        exact ⟨M, hM_nn, fun y hy => by simpa [← iteratedDeriv_succ'] using hM y hy⟩
      have hcomp_deriv : Set.EqOn
          (_root_.derivWithin (fun y => H (F y)) (Set.Ici x₀))
          (fun y => _root_.deriv H (F y) * _root_.derivWithin F (Set.Ici x₀) y) (Set.Ici x₀) := by
        intro y hy
        have hHy : HasDerivAt H (_root_.deriv H (F y)) (F y) :=
          ((hH.contDiffAt (hU.mem_nhds (hmaps hy))).differentiableAt (by simp)).hasDerivAt
        have hFy : HasDerivWithinAt F (_root_.derivWithin F (Set.Ici x₀) y) (Set.Ici x₀) y :=
          ((hF.1 y hy).differentiableWithinAt (by simp)).hasDerivWithinAt
        exact (hHy.comp_hasDerivWithinAt y hFy).derivWithin (uniqueDiffOn_Ici x₀ y hy)
      have hHF_cd : ContDiffOn ℝ ∞ (fun y => _root_.deriv H (F y)) (Set.Ici x₀) :=
        hHderiv.comp hF.1 hmaps
      have hih : ∀ i : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧ (i ≤ m → ∀ x ≥ x₀,
          |iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x| ≤
            C' * x ^ (-(i : ℝ))) := by
        intro i
        by_cases him : i < m + 1
        · obtain ⟨C, hC, hbd⟩ := ih i him (_root_.deriv H) hHderiv hHderiv_bd
          by_cases hi0 : i = 0
          · subst hi0; exact ⟨C, hC, fun _ x hx => by simpa using hbd x hx⟩
          · refine ⟨C * x₀ ^ (-β), by positivity, fun _ x hx => ?_⟩
            have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
            have hpow : x ^ (-β) ≤ x₀ ^ (-β) :=
              Real.rpow_le_rpow_of_nonpos hx₀ hx (neg_nonpos.mpr hβ)
            have hexp : x ^ (-β - (i : ℝ)) = x ^ (-β) * x ^ (-(i : ℝ)) := by
              rw [← Real.rpow_add hxpos, sub_eq_add_neg]
            have h1 := hbd x hx
            simp only [hi0, ↓reduceIte] at h1
            calc |iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x|
                ≤ C * x ^ (-β - (i : ℝ)) := h1
              _ = C * x ^ (-β) * x ^ (-(i : ℝ)) := by rw [hexp]; ring
              _ ≤ C * x₀ ^ (-β) * x ^ (-(i : ℝ)) := by gcongr
        · exact ⟨0, le_rfl, fun hle => absurd hle (by omega)⟩
      choose C' hC'_nn hC' using hih
      choose D' hD'_nn hD' using hF.derivWithin.2
      refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C' i * D' (m - i),
        Finset.sum_nonneg fun i _ => by positivity [hC'_nn i, hD'_nn (m - i)],
        fun x hx => ?_⟩
      have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
      have hxI : x ∈ Set.Ici x₀ := hx
      rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr hcomp_deriv hxI]
      have hleib := iteratedDerivWithin_mul (n := m) hxI (uniqueDiffOn_Ici x₀)
        ((hHF_cd x hx).of_le (by simp)) ((hF.derivWithin.1 x hx).of_le (by simp))
      change |iteratedDerivWithin m
          ((fun y => _root_.deriv H (F y)) * _root_.derivWithin F (Set.Ici x₀)) (Set.Ici x₀) x| ≤ _
      rw [hleib]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      calc |∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x *
              iteratedDerivWithin (m - i) (_root_.derivWithin F (Set.Ici x₀)) (Set.Ici x₀) x|
          ≤ ∑ i ∈ Finset.range (m + 1),
            |(m.choose i : ℝ) * iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x *
              iteratedDerivWithin (m - i) (_root_.derivWithin F (Set.Ici x₀)) (Set.Ici x₀) x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (m + 1),
            ((m.choose i : ℝ) * C' i * D' (m - i)) * x ^ (-β - ((m + 1 : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [abs_mul, abs_mul, Nat.abs_cast]
            have h1 := hC' i him x hx
            have h2 := hD' (m - i) x hx
            have hmul := mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
            have hexp : x ^ (-(i : ℝ)) * x ^ (-(β + 1) - ((m - i : ℕ) : ℝ)) =
                x ^ (-β - ((m + 1 : ℕ) : ℝ)) := by
              rw [← Real.rpow_add hxpos, Nat.cast_sub him]; congr 1; push_cast; ring
            calc (m.choose i : ℝ) *
                  |iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x| *
                  |iteratedDerivWithin (m - i) (_root_.derivWithin F (Set.Ici x₀)) (Set.Ici x₀) x|
                = (m.choose i : ℝ) *
                    (|iteratedDerivWithin i (fun y => _root_.deriv H (F y)) (Set.Ici x₀) x| *
                    |iteratedDerivWithin (m - i) (_root_.derivWithin F (Set.Ici x₀)) (Set.Ici x₀) x|) := by
                    ring
              _ ≤ (m.choose i : ℝ) * ((C' i * x ^ (-(i : ℝ))) *
                    (D' (m - i) * x ^ (-(β + 1) - ((m - i : ℕ) : ℝ)))) :=
                  mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
              _ = ((m.choose i : ℝ) * C' i * D' (m - i)) *
                    (x ^ (-(i : ℝ)) * x ^ (-(β + 1) - ((m - i : ℕ) : ℝ))) := by ring
              _ = ((m.choose i : ℝ) * C' i * D' (m - i)) *
                    x ^ (-β - ((m + 1 : ℕ) : ℝ)) := by rw [hexp]
        _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C' i * D' (m - i)) *
              x ^ (-β - ((m + 1 : ℕ) : ℝ)) := by rw [Finset.sum_mul]

private lemma compact_iteratedDeriv_bound {a b a' b' : ℝ} (ha : a < a') (hb : b' < b)
    {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H (Set.Ioo a b)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc a' b', |_root_.iteratedDeriv k H y| ≤ M := by
  have hcont : ContinuousOn (_root_.iteratedDeriv k H) (Set.Icc a' b') := by
    have hcontU : ContinuousOn (_root_.iteratedDeriv k H) (Set.Ioo a b) := by
      have h1 := hH.continuousOn_iteratedDerivWithin (m := k) (by simp) isOpen_Ioo.uniqueDiffOn
      exact h1.congr fun y hy => (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm
    exact hcontU.mono fun y (hy : y ∈ Set.Icc a' b') =>
      ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩

/-- **Lemma W.0(ii), first part**: if `F ∈ 𝒮_β` (`β ≥ 0`) maps `[x₀, ∞)` into a compact
subinterval `[a', b'] ⊂ (a, b)` containing `0`, and `G` is `C^∞` on `(a, b)`, then
`G(F) - G(0) ∈ 𝒮_β`. -/
theorem IsSymbolOn.comp_sub_zero {x₀ β a b a' b' : ℝ} {F G : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F)
    (ha : a < a') (ha' : a' ≤ 0) (hb' : 0 ≤ b') (hb : b' < b)
    (hF_range : ∀ x ≥ x₀, F x ∈ Set.Icc a' b')
    (hG : ContDiffOn ℝ ∞ G (Set.Ioo a b)) :
    IsSymbolOn x₀ β (fun x => G (F x) - G 0) := by
  have hmaps : Set.MapsTo F (Set.Ici x₀) (Set.Ioo a b) := fun x hx =>
    ⟨lt_of_lt_of_le ha (hF_range x hx).1, lt_of_le_of_lt (hF_range x hx).2 hb⟩
  have hGF_cd : ContDiffOn ℝ ∞ (fun x => G (F x)) (Set.Ici x₀) := hG.comp hF.1 hmaps
  refine ⟨hGF_cd.sub contDiffOn_const, fun j => ?_⟩
  cases j with
  | zero =>
    have hGd_cont : ContinuousOn (_root_.deriv G) (Set.Icc a' b') :=
      (hG.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono
        fun y (hy : y ∈ Set.Icc a' b') => ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩
    obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hGd_cont
    obtain ⟨C₀, hC₀, hF₀⟩ := hF.abs_le
    refine ⟨max M₁ (0 : ℝ) * C₀, mul_nonneg (le_max_right _ _) hC₀, fun x hx => ?_⟩
    have hdiff : ∀ y ∈ Set.Icc a' b', DifferentiableAt ℝ G y := fun y hy =>
      (hG.contDiffAt (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩)).differentiableAt
        (by simp)
    have hmvt := (convex_Icc a' b').norm_image_sub_le_of_norm_deriv_le (C := max M₁ (0 : ℝ)) hdiff
      (fun y hy => (hM₁ y hy).trans (le_max_left _ _))
      ⟨ha', hb'⟩ (hF_range x hx)
    simp only [Real.norm_eq_abs, sub_zero, iteratedDerivWithin_zero, Nat.cast_zero] at hmvt ⊢
    calc |G (F x) - G 0| ≤ max M₁ (0 : ℝ) * |F x| := hmvt
      _ ≤ max M₁ (0 : ℝ) * (C₀ * x ^ (-β)) := mul_le_mul_of_nonneg_left (hF₀ x hx) (le_max_right _ _)
      _ = max M₁ (0 : ℝ) * C₀ * x ^ (-β) := by ring
  | succ m =>
    have hsub : Set.Icc a' b' ⊆ Set.Ioo a b := fun y hy =>
      ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩
    obtain ⟨C, hC, hbd⟩ := comp_deriv_bound_aux hx₀ hβ hF isOpen_Ioo hsub hF_range
      (m + 1) G hG (fun k => compact_iteratedDeriv_bound ha hb hG k)
    refine ⟨C, hC, fun x hx => ?_⟩
    have heq : Set.EqOn (_root_.derivWithin (fun y => G (F y) - G 0) (Set.Ici x₀))
        (_root_.derivWithin (fun y => G (F y)) (Set.Ici x₀)) (Set.Ici x₀) := by
      intro y hy
      have hd : HasDerivWithinAt (fun z => G (F z))
          (_root_.derivWithin (fun z => G (F z)) (Set.Ici x₀) y) (Set.Ici x₀) y :=
        ((hGF_cd y hy).differentiableWithinAt (by simp)).hasDerivWithinAt
      exact (hd.sub_const (G 0)).derivWithin (uniqueDiffOn_Ici x₀ y hy)
    have hxI : x ∈ Set.Ici x₀ := hx
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr heq hxI, ← iteratedDerivWithin_succ']
    simpa only [Nat.succ_ne_zero, ↓reduceIte] using hbd x hx

lemma IsSymbolOn.comp_sub_zero_of_contDiff {x₀ β : ℝ} {F G : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F) (hG : ContDiff ℝ ∞ G) :
    IsSymbolOn x₀ β (fun x => G (F x) - G 0) := by
  obtain ⟨C₀, hC₀, hF₀⟩ := hF.abs_le
  set B : ℝ := C₀ * x₀ ^ (-β) + 1
  have hB : 0 < B := by positivity
  refine hF.comp_sub_zero hx₀ hβ (a := -(2 * B)) (a' := -B) (b' := B) (b := 2 * B)
    (by linarith) (by linarith) (by linarith) (by linarith) (fun x hx => ?_) hG.contDiffOn
  have hpow : x ^ (-β) ≤ x₀ ^ (-β) := Real.rpow_le_rpow_of_nonpos hx₀ hx (neg_nonpos.mpr hβ)
  exact _root_.abs_le.mp <| (hF₀ x hx).trans <|
    (mul_le_mul_of_nonneg_left hpow hC₀).trans (by dsimp [B]; linarith)

/-- Positive-domain composition lemma: if `F ∈ 𝒮_β` (`β ≥ 0`) maps `[x₀, ∞)` into `(0, ∞)`,
`G` is `C^∞` on `(0, ∞)` with all higher derivatives `k ≥ 1` uniformly bounded on `(0, ∞)`
and `|G(F(x))| ≤ L * F(x)`, then `G(F) ∈ 𝒮_β`. -/
theorem IsSymbolOn.comp_Ioi {x₀ β : ℝ} {F G : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F)
    (hF_pos : ∀ x ≥ x₀, 0 < F x)
    (hG : ContDiffOn ℝ ∞ G (Set.Ioi 0))
    (hG_zero : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ≥ x₀, |G (F x)| ≤ L * F x)
    (hG_derivs : ∀ k : ℕ, 1 ≤ k → ∃ M : ℝ, 0 ≤ M ∧ ∀ y > 0, |_root_.iteratedDeriv k G y| ≤ M) :
    IsSymbolOn x₀ β (fun x => G (F x)) := by
  have hmaps : Set.MapsTo F (Set.Ici x₀) (Set.Ioi 0) := fun x hx => hF_pos x hx
  refine ⟨hG.comp hF.1 hmaps, fun j => ?_⟩
  cases j with
  | zero =>
    obtain ⟨L, hL, hGL⟩ := hG_zero
    obtain ⟨C₀, hC₀, hF₀⟩ := hF.abs_le
    refine ⟨L * C₀, mul_nonneg hL hC₀, fun x hx => ?_⟩
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero]
    calc |G (F x)| ≤ L * F x := hGL x hx
      _ ≤ L * |F x| := mul_le_mul_of_nonneg_left (le_abs_self _) hL
      _ ≤ L * (C₀ * x ^ (-β)) := mul_le_mul_of_nonneg_left (hF₀ x hx) hL
      _ = L * C₀ * x ^ (-β) := by ring
  | succ m =>
    have hGd : ContDiffOn ℝ ∞ (_root_.deriv G) (Set.Ioi 0) := hG.deriv_of_isOpen isOpen_Ioi (by simp)
    have hGd_bd : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Ioi (0 : ℝ),
        |_root_.iteratedDeriv k (_root_.deriv G) y| ≤ M := fun k => by
      obtain ⟨M, hM, h⟩ := hG_derivs (k + 1) (Nat.succ_pos k)
      exact ⟨M, hM, fun y hy => by simpa [← iteratedDeriv_succ'] using h y hy⟩
    have hcomp_deriv : Set.EqOn
        (_root_.derivWithin (fun y => G (F y)) (Set.Ici x₀))
        (fun y => _root_.deriv G (F y) * _root_.derivWithin F (Set.Ici x₀) y) (Set.Ici x₀) := by
      intro y hy
      have hHy : HasDerivAt G (_root_.deriv G (F y)) (F y) :=
        ((hG.contDiffAt (isOpen_Ioi.mem_nhds (hmaps hy))).differentiableAt (by simp)).hasDerivAt
      have hFy : HasDerivWithinAt F (_root_.derivWithin F (Set.Ici x₀) y) (Set.Ici x₀) y :=
        ((hF.1 y hy).differentiableWithinAt (by simp)).hasDerivWithinAt
      exact (hHy.comp_hasDerivWithinAt y hFy).derivWithin (uniqueDiffOn_Ici x₀ y hy)
    have hGF_cd : IsSymbolOn x₀ 0 (fun y => _root_.deriv G (F y)) := by
      refine ⟨hGd.comp hF.1 hmaps, fun i => ?_⟩
      obtain ⟨C, hC, hbd⟩ := comp_deriv_bound_aux hx₀ hβ hF isOpen_Ioi Subset.rfl hF_pos i
        (_root_.deriv G) hGd hGd_bd
      by_cases hi0 : i = 0
      · subst hi0; exact ⟨C, hC, fun x hx => by simpa using hbd x hx⟩
      · refine ⟨C * x₀ ^ (-β), by positivity, fun x hx => ?_⟩
        have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
        have hpow : x ^ (-β) ≤ x₀ ^ (-β) :=
          Real.rpow_le_rpow_of_nonpos hx₀ hx (neg_nonpos.mpr hβ)
        have hexp : x ^ (-β - (i : ℝ)) = x ^ (-β) * x ^ (-0 - (i : ℝ)) := by
          rw [← Real.rpow_add hxpos]; congr 1; ring
        have h1 := hbd x hx
        simp only [hi0, ↓reduceIte] at h1
        calc |iteratedDerivWithin i (fun y => _root_.deriv G (F y)) (Set.Ici x₀) x|
            ≤ C * x ^ (-β - (i : ℝ)) := h1
          _ = C * x ^ (-β) * x ^ (-0 - (i : ℝ)) := by rw [hexp]; ring
          _ ≤ C * x₀ ^ (-β) * x ^ (-0 - (i : ℝ)) := by gcongr
    have hprod := hGF_cd.mul hx₀ hF.derivWithin
    rw [zero_add] at hprod
    obtain ⟨C, hC, hbd⟩ := hprod.2 m
    refine ⟨C, hC, fun x hx => ?_⟩
    have hxI : x ∈ Set.Ici x₀ := hx
    rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr hcomp_deriv hxI]
    have hexp : -(β + 1) - (m : ℝ) = -β - ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [← hexp]
    exact hbd x hx

private noncomputable def taylorKer (w H : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * H (t * s)

private lemma taylorKer_hasDerivAt {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {w H : ℝ → ℝ} (hw : ContinuousOn w (Set.Icc 0 1)) (hH : ContDiffOn ℝ ∞ H (Set.Ioo a b))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo a b) :
    HasDerivAt (taylorKer w H) (taylorKer (fun t => t * w t) (_root_.deriv H) s₀) s₀ := by
  set δ : ℝ := min (s₀ - a) (b - s₀) / 2
  have hδ : 0 < δ := half_pos (lt_min (sub_pos.mpr hs₀.1) (sub_pos.mpr hs₀.2))
  set lo : ℝ := min 0 (s₀ - δ)
  set hi : ℝ := max 0 (s₀ + δ)
  have hδ1 : δ ≤ (s₀ - a) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ (b - s₀) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hlo_a : a < lo := lt_min ha (by linarith [hs₀.1])
  have bhi_b : hi < b := max_lt hb (by linarith [hs₀.2])
  have hsub_Icc : Set.Icc lo hi ⊆ Set.Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le hlo_a hy.1, lt_of_le_of_lt hy.2 bhi_b⟩
  have hts_mem : ∀ s ∈ Metric.ball s₀ δ, ∀ t ∈ Set.Icc (0 : ℝ) 1, t * s ∈ Set.Icc lo hi := by
    intro s hs t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hlo_s : lo ≤ s := le_trans (min_le_right _ _) (by linarith)
    have hs_hi : s ≤ hi := le_trans (by linarith) (le_max_right _ _)
    rcases le_or_gt 0 s with hs0 | hs0
    · exact ⟨le_trans (min_le_left _ _) (mul_nonneg ht.1 hs0),
        le_trans (mul_le_of_le_one_left hs0 ht.2) hs_hi⟩
    · exact ⟨le_trans hlo_s (by nlinarith [ht.1, ht.2, hs0]),
        le_trans (mul_nonpos_of_nonneg_of_nonpos ht.1 hs0.le) (le_max_left _ _)⟩
  have hHd_cont : ContinuousOn (_root_.deriv H) (Set.Icc lo hi) :=
    (hH.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hsub_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hHd_cont
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  set B : ℝ := max W 0 * max M 0
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
      (fun t => w t * H (t * s)) (volume.restrict (Ι 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds s₀ hδ] with s hs
    have hcont : ContinuousOn (fun t => w t * H (t * s)) (Set.Icc 0 1) :=
      hw.mul (hH.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
        fun t ht => hsub_Icc (hts_mem s hs t ht))
    rw [Set.uIoc_of_le zero_le_one]
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (fun t => w t * H (t * s₀)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact hw.mul (hH.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
      fun t ht => hsub_Icc (hts_mem s₀ (Metric.mem_ball_self hδ) t ht))
  have hF'_meas : AEStronglyMeasurable
      (fun t => (t * w t) * _root_.deriv H (t * s₀)) (volume.restrict (Ι 0 1)) := by
    have hcont : ContinuousOn (fun t => (t * w t) * _root_.deriv H (t * s₀)) (Set.Icc 0 1) :=
      (continuousOn_id.mul hw).mul ((hH.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).comp
        (continuous_id.mul continuous_const).continuousOn
        fun t ht => hsub_Icc (hts_mem s₀ (Metric.mem_ball_self hδ) t ht))
    rw [Set.uIoc_of_le zero_le_one]
    exact (hcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => w t * H (t * s))
    (F' := fun s t => (t * w t) * _root_.deriv H (t * s))
    (bound := fun _ => B)
    (Metric.ball_mem_nhds s₀ hδ) hF_meas hF_int hF'_meas
    (Eventually.of_forall fun t ht s hs => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg htIcc.1]
      have hwbd : |w t| ≤ max W 0 := (hW t htIcc).trans (le_max_left _ _)
      have hHbd : |_root_.deriv H (t * s)| ≤ max M 0 :=
        (hM (t * s) (hts_mem s hs t htIcc)).trans (le_max_left _ _)
      calc t * |w t| * |_root_.deriv H (t * s)| ≤ 1 * max W 0 * max M 0 := by gcongr; exact htIcc.2
        _ = B := by dsimp [B]; ring)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht s hs => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
      have hts := hsub_Icc (hts_mem s hs t htIcc)
      have hdH : HasDerivAt H (_root_.deriv H (t * s)) (t * s) :=
        ((hH.contDiffAt (isOpen_Ioo.mem_nhds hts)).differentiableAt (by simp)).hasDerivAt
      have hd_mul : HasDerivAt (fun x : ℝ => t * x) t s := by
        simpa using (hasDerivAt_id s).const_mul t
      exact ((hdH.comp s hd_mul).const_mul (w t)).congr_deriv (by ring))).2

private lemma contDiffOn_taylorKer {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∀ n : ℕ, ∀ w H : ℝ → ℝ, ContinuousOn w (Set.Icc 0 1) →
      ContDiffOn ℝ ∞ H (Set.Ioo a b) → ContDiffOn ℝ n (taylorKer w H) (Set.Ioo a b) := by
  intro n
  induction n with
  | zero =>
    intro w H hw hH
    change ContDiffOn ℝ 0 (taylorKer w H) (Set.Ioo a b)
    rw [contDiffOn_zero]
    intro s₀ hs₀
    exact (taylorKer_hasDerivAt ha hb hw hH hs₀).continuousAt.continuousWithinAt
  | succ n ih =>
    intro w H hw hH
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun s₀ hs₀ => (taylorKer_hasDerivAt ha hb hw hH hs₀).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hEq : Set.EqOn (_root_.deriv (taylorKer w H))
        (taylorKer (fun t => t * w t) (_root_.deriv H)) (Set.Ioo a b) :=
      fun s₀ hs₀ => (taylorKer_hasDerivAt ha hb hw hH hs₀).deriv
    exact (ih (fun t => t * w t) (_root_.deriv H) (continuousOn_id.mul hw)
      (hH.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp))).congr fun s₀ hs₀ => hEq hs₀

private lemma taylor_second_order_factor {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G (Set.Ioo a b))
    (hG0 : G 0 = 0) (hG'0 : _root_.deriv G 0 = 0) :
    ∀ s ∈ Set.Ioo a b,
      G s = s ^ 2 * taylorKer (fun t => 1 - t) (_root_.deriv (_root_.deriv G)) s := by
  intro s hs
  have hG' : ContDiffOn ℝ ∞ (_root_.deriv G) (Set.Ioo a b) :=
    hG.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp)
  have hG'' : ContDiffOn ℝ ∞ (_root_.deriv (_root_.deriv G)) (Set.Ioo a b) :=
    hG'.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp)
  have hts_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t * s ∈ Set.Ioo a b := by
    intro t ht
    rcases le_or_gt 0 s with hs0 | hs0
    · exact ⟨lt_of_lt_of_le ha (mul_nonneg ht.1 hs0),
        lt_of_le_of_lt (mul_le_of_le_one_left hs0 ht.2) hs.2⟩
    · exact ⟨lt_of_lt_of_le hs.1 (by nlinarith [ht.1, ht.2, hs0]),
        lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ht.1 hs0.le) hb⟩
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u => (1 - u) * (s * _root_.deriv G (u * s)) + G (u * s))
        ((1 - t) * (s ^ 2 * _root_.deriv (_root_.deriv G) (t * s))) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hts : t * s ∈ Set.Ioo a b := hts_mem t ht
    have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) t :=
      ((hasDerivAt_id t).const_sub (1 : ℝ)).congr_deriv (by ring)
    have hmul : HasDerivAt (fun u : ℝ => u * s) s t := by
      simpa using (hasDerivAt_id t).mul_const s
    have hG_at : HasDerivAt G (_root_.deriv G (t * s)) (t * s) :=
      ((hG.contDiffAt (isOpen_Ioo.mem_nhds hts)).differentiableAt (by simp)).hasDerivAt
    have hG'_at : HasDerivAt (_root_.deriv G) (_root_.deriv (_root_.deriv G) (t * s)) (t * s) :=
      ((hG'.contDiffAt (isOpen_Ioo.mem_nhds hts)).differentiableAt (by simp)).hasDerivAt
    have hφ : HasDerivAt (fun u => G (u * s)) (s * _root_.deriv G (t * s)) t :=
      (hG_at.comp t hmul).congr_deriv (by ring)
    have hcomp : HasDerivAt (fun u => _root_.deriv G (u * s))
        (_root_.deriv (_root_.deriv G) (t * s) * s) t := by
      simpa only [Function.comp_def] using hG'_at.comp t hmul
    have hφ' : HasDerivAt (fun u => s * _root_.deriv G (u * s))
        (s ^ 2 * _root_.deriv (_root_.deriv G) (t * s)) t :=
      (hcomp.const_mul s).congr_deriv (by ring)
    exact ((h1.mul hφ').add hφ).congr_deriv (by ring)
  have hint : IntervalIntegrable
      (fun t => (1 - t) * (s ^ 2 * _root_.deriv (_root_.deriv G) (t * s))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_const.sub continuousOn_id).mul (continuousOn_const.mul
      (hG''.continuousOn.comp (continuous_id.mul continuous_const).continuousOn
        fun t ht => hts_mem t ht))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hval : ((1 - (1 : ℝ)) * (s * _root_.deriv G (1 * s)) + G (1 * s)) -
      ((1 - (0 : ℝ)) * (s * _root_.deriv G (0 * s)) + G (0 * s)) = G s := by
    rw [one_mul, zero_mul, hG0, hG'0]; ring
  rw [hval] at hftc
  have heq : (∫ t in (0 : ℝ)..1, (1 - t) * (s ^ 2 * _root_.deriv (_root_.deriv G) (t * s))) =
      s ^ 2 * taylorKer (fun t => 1 - t) (_root_.deriv (_root_.deriv G)) s := by
    dsimp [taylorKer]; rw [← intervalIntegral.integral_const_mul]; congr 1 with t; ring
  linarith

/-- **Lemma W.0(ii), second part**: if `F ∈ 𝒮_β` (`β ≥ 0`) maps `[x₀, ∞)` into `[a', b'] ⊂ (a, b)`
containing `0`, `G` is `C^∞` on `(a, b)`, and `G(0) = G'(0) = 0`, then `G(F) ∈ 𝒮_{2β}`. -/
theorem IsSymbolOn.comp_vanish_deriv {x₀ β a b a' b' : ℝ} {F G : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F)
    (ha : a < a') (ha' : a' ≤ 0) (hb' : 0 ≤ b') (hb : b' < b)
    (hF_range : ∀ x ≥ x₀, F x ∈ Set.Icc a' b')
    (hG : ContDiffOn ℝ ∞ G (Set.Ioo a b))
    (hG0 : G 0 = 0) (hG'0 : _root_.deriv G 0 = 0) :
    IsSymbolOn x₀ (2 * β) (fun x => G (F x)) := by
  have ha0 : a < 0 := lt_of_lt_of_le ha ha'
  have hb0 : 0 < b := lt_of_le_of_lt hb' hb
  let K : ℝ → ℝ := taylorKer (fun t => 1 - t) (_root_.deriv (_root_.deriv G))
  have hG' : ContDiffOn ℝ ∞ (_root_.deriv G) (Set.Ioo a b) :=
    hG.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp)
  have hG'' : ContDiffOn ℝ ∞ (_root_.deriv (_root_.deriv G)) (Set.Ioo a b) :=
    hG'.deriv_of_isOpen (m := ∞) isOpen_Ioo (by simp)
  have hK : ContDiffOn ℝ ∞ K (Set.Ioo a b) :=
    contDiffOn_infty.mpr fun n =>
      contDiffOn_taylorKer ha0 hb0 n (fun t => 1 - t) (_root_.deriv (_root_.deriv G))
        (continuousOn_const.sub continuousOn_id) hG''
  have hmaps : Set.MapsTo F (Set.Ici x₀) (Set.Ioo a b) := fun x hx =>
    ⟨lt_of_lt_of_le ha (hF_range x hx).1, lt_of_le_of_lt (hF_range x hx).2 hb⟩
  have hsub : Set.Icc a' b' ⊆ Set.Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩
  have hKF : IsSymbolOn x₀ 0 (fun x => K (F x)) := by
    refine ⟨hK.comp hF.1 hmaps, fun j => ?_⟩
    obtain ⟨C, hC, hbd⟩ := comp_deriv_bound_aux hx₀ hβ hF isOpen_Ioo hsub hF_range j K hK
      (fun k => compact_iteratedDeriv_bound ha hb hK k)
    rcases eq_or_ne j 0 with rfl | hj
    · exact ⟨C, hC, fun x hx => by simpa using hbd x hx⟩
    · refine ⟨C * x₀ ^ (-β), by positivity, fun x hx => ?_⟩
      have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
      have hpow : x ^ (-β) ≤ x₀ ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos hx₀ hx (neg_nonpos.mpr hβ)
      have hexp : x ^ (-β - (j : ℝ)) = x ^ (-β) * x ^ (-0 - (j : ℝ)) := by
        rw [← Real.rpow_add hxpos]; congr 1; ring
      have h1 := hbd x hx
      simp only [hj, ↓reduceIte] at h1
      calc |iteratedDerivWithin j (fun y => K (F y)) (Set.Ici x₀) x|
          ≤ C * x ^ (-β - (j : ℝ)) := h1
        _ = C * x ^ (-β) * x ^ (-0 - (j : ℝ)) := by rw [hexp]; ring
        _ ≤ C * x₀ ^ (-β) * x ^ (-0 - (j : ℝ)) := by gcongr
  have hF2 : IsSymbolOn x₀ (2 * β) (fun x => F x ^ 2) := by simpa using hF.pow hx₀ 2
  have hprod : IsSymbolOn x₀ (2 * β + 0) (fun x => F x ^ 2 * K (F x)) := hF2.mul hx₀ hKF
  rw [add_zero] at hprod
  exact hprod.congr fun x hx => (taylor_second_order_factor ha0 hb0 hG hG0 hG'0 (F x) (hmaps hx)).symm

lemma IsSymbolOn.comp_vanish_deriv_of_contDiff {x₀ β : ℝ} {F G : ℝ → ℝ}
    (hx₀ : 0 < x₀) (hβ : 0 ≤ β) (hF : IsSymbolOn x₀ β F) (hG : ContDiff ℝ ∞ G)
    (hG0 : G 0 = 0) (hG'0 : _root_.deriv G 0 = 0) :
    IsSymbolOn x₀ (2 * β) (fun x => G (F x)) := by
  obtain ⟨C₀, hC₀, hF₀⟩ := hF.abs_le
  set B : ℝ := C₀ * x₀ ^ (-β) + 1
  have hB : 0 < B := by positivity
  refine hF.comp_vanish_deriv hx₀ hβ (a := -(2 * B)) (a' := -B) (b' := B) (b := 2 * B)
    (by linarith) (by linarith) (by linarith) (by linarith) (fun x hx => ?_) hG.contDiffOn
    hG0 hG'0
  have hpow : x ^ (-β) ≤ x₀ ^ (-β) := Real.rpow_le_rpow_of_nonpos hx₀ hx (neg_nonpos.mpr hβ)
  exact _root_.abs_le.mp <| (hF₀ x hx).trans <|
    (mul_le_mul_of_nonneg_left hpow hC₀).trans (by dsimp [B]; linarith)

lemma IsSymbol.comp_sub_zero {β a b a' b' : ℝ} {F G : ℝ → ℝ}
    (hβ : 0 ≤ β) (hF : IsSymbol β F)
    (ha : a < a') (ha' : a' ≤ 0) (hb' : 0 ≤ b') (hb : b' < b)
    (hF_range : ∀ x ≥ 1, F x ∈ Set.Icc a' b')
    (hG : ContDiffOn ℝ ∞ G (Set.Ioo a b)) :
    IsSymbol β (fun x => G (F x) - G 0) :=
  IsSymbolOn.comp_sub_zero zero_lt_one hβ hF ha ha' hb' hb hF_range hG

lemma IsSymbol.comp_sub_zero_of_contDiff {β : ℝ} {F G : ℝ → ℝ}
    (hβ : 0 ≤ β) (hF : IsSymbol β F) (hG : ContDiff ℝ ∞ G) :
    IsSymbol β (fun x => G (F x) - G 0) :=
  IsSymbolOn.comp_sub_zero_of_contDiff zero_lt_one hβ hF hG

lemma IsSymbol.comp_vanish_deriv {β a b a' b' : ℝ} {F G : ℝ → ℝ}
    (hβ : 0 ≤ β) (hF : IsSymbol β F)
    (ha : a < a') (ha' : a' ≤ 0) (hb' : 0 ≤ b') (hb : b' < b)
    (hF_range : ∀ x ≥ 1, F x ∈ Set.Icc a' b')
    (hG : ContDiffOn ℝ ∞ G (Set.Ioo a b))
    (hG0 : G 0 = 0) (hG'0 : _root_.deriv G 0 = 0) :
    IsSymbol (2 * β) (fun x => G (F x)) :=
  IsSymbolOn.comp_vanish_deriv zero_lt_one hβ hF ha ha' hb' hb hF_range hG hG0 hG'0

lemma IsSymbol.comp_vanish_deriv_of_contDiff {β : ℝ} {F G : ℝ → ℝ}
    (hβ : 0 ≤ β) (hF : IsSymbol β F) (hG : ContDiff ℝ ∞ G)
    (hG0 : G 0 = 0) (hG'0 : _root_.deriv G 0 = 0) :
    IsSymbol (2 * β) (fun x => G (F x)) :=
  IsSymbolOn.comp_vanish_deriv_of_contDiff zero_lt_one hβ hF hG hG0 hG'0

/-- info: 'FormalResearch.Asymptotics.IsSymbolOn.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsSymbolOn.mul

/-- info: 'FormalResearch.Asymptotics.IsSymbolOn.derivWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsSymbolOn.derivWithin

/-- info: 'FormalResearch.Asymptotics.IsWeightedSymbolOn.mul_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsWeightedSymbolOn.mul_symbol

/-- info: 'FormalResearch.Asymptotics.IsWeightedSymbolOn.of_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsWeightedSymbolOn.of_symbol

/-- info: 'FormalResearch.Asymptotics.IsSymbolOn.comp_sub_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsSymbolOn.comp_sub_zero

/-- info: 'FormalResearch.Asymptotics.IsSymbolOn.comp_vanish_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsSymbolOn.comp_vanish_deriv

/-- info: 'FormalResearch.Asymptotics.IsSymbolOn.comp_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.IsSymbolOn.comp_Ioi

end FormalResearch.Asymptotics

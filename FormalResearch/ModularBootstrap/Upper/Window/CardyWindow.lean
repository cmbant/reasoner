module

public import FormalResearch.ModularBootstrap.Bessel.VCorollaries
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge
public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw

/-!
# The Cardy weight in the Airy window (Lemma `A_V`, window form) and the scales `FV_c`, `FK_c^{(f)}`

Sources: `CFT/modular_bootstrap/paper/remainder.tex`, Lemma `A_V` (`rem:cardy`), which refers for the
uniform Cardy asymptotic and the real-axis positivity of `V` to `lower_o1_two_edge.tex`, Lemma `B`
(a), (c) (`vlo:Bessel`; Lean: `Bessel.besselV_asymptotic`, `Bessel.besselV_ge`); and
`upper_transfer.tex`, §5 (notation `FV_c`, `FK_c^{(f)}`) and the proof of Lemma `T` (`ut:T`).

* `FVc q c'`: `FV_c = 𝔮 c'^{1/2} λ √ξ_* (1 - e^{-4πξ_*})² sech²(πξ_*/2) / (√3 π)`, `λ = (k_tip c')^{-2/3}`
  (`lambdaComb`); `q = 𝔮_{w,Q}(ξ_*)` is `1` at Virasoro.
* `FKc q f c'`: `FK_c^{(f)} = FV_c (2√2/(πλ))^{2 n₁}`, `n₁ = f - 1/4`.
* `besselV_window_bound`: **Lemma `A_V`, window form** at `w = 1`: for `c'` large and
  `x ∈ [ξ_*/2, ξ_* + r₀]`, `V(c'x²/3) e^{-c'L(x)} sech²(πx/2) · dt/dσ ≤ C FV_c`, where `x = ξ_* + λσ`,
  `t = c'x²/3`, `dt/dσ = (2/3) c' x λ`.
* `besselV_far_bound`: the far-band form `V e^{-c'L} dt ≤ C √c' √x dx` on `x ≥ x₀ > 0` (`dt/dx = (2/3)c'x`).
* `CardyWindowBound`, `CardyFarBound`: the two bounds as named properties of an abstract weight
  `V : ℝ → ℝ → ℝ` (`V c' t`), which is all that Lemma `T` uses of the Cardy weight; the Virasoro weight
  `besselV (c'/12)` and `virasoroProblem.cardyV (c'/12)` satisfy them (`cardyWindowBound_virasoro`,
  `cardyFarBound_virasoro`, hence non-vacuity).  At general `(w, Q)` they are the Cardy and Peano input
  `fw:e3.6`, which is not formalised.

All results are proved unconditionally.
-/

@[expose] public section

open Real
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Window.Cardy

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Bessel
  FormalResearch.ModularBootstrap.Upper.Comb

/-- `FV_c = 𝔮 c'^{1/2} λ √ξ_* (1 - e^{-4πξ_*})² sech²(πξ_*/2) / (√3 π)` (`upper_transfer.tex`, §5), with
`q = 𝔮_{w,Q}(ξ_*)` (`q = 1` at Virasoro) and `λ = lambdaComb c' = (k_tip c')^{-2/3}`. -/
noncomputable def FVc (q c' : ℝ) : ℝ :=
  q * (√c' * lambdaComb c' * √xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 *
    (1 / cosh (π * xiStar / 2) ^ 2)) / (√3 * π)

/-- `FK_c^{(f)} = FV_c (2√2/(πλ))^{2 n₁}`, `n₁ = f - 1/4` (`upper_transfer.tex`, §5). -/
noncomputable def FKc (q : ℝ) (f : ℕ) (c' : ℝ) : ℝ :=
  FVc q c' * (2 * √2 / (π * lambdaComb c')) ^ (2 * ((f : ℝ) - 1 / 4))

lemma lambdaComb_pos' {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' :=
  Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _

lemma one_sub_exp_xiStar_pos : 0 < 1 - exp (-(4 * π * xiStar)) := by
  have : exp (-(4 * π * xiStar)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := xiStar_pos
    have := Real.pi_pos
    nlinarith
  linarith

lemma FVc_pos {q c' : ℝ} (hq : 0 < q) (hc' : 0 < c') : 0 < FVc q c' := by
  unfold FVc
  have := lambdaComb_pos' hc'
  have := xiStar_pos
  have := one_sub_exp_xiStar_pos
  positivity

lemma FKc_pos {q : ℝ} (hq : 0 < q) (f : ℕ) {c' : ℝ} (hc' : 0 < c') : 0 < FKc q f c' := by
  unfold FKc
  have := FVc_pos hq hc'
  have := lambdaComb_pos' hc'
  positivity

/-- `FKc` with the exponent `2 n₁` written as `2 (f - 1/4)`; `FK_c := FK_c^{(1)}` has exponent `3/2`. -/
lemma FKc_one (q c' : ℝ) :
    FKc q 1 c' = FVc q c' * (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) := by
  unfold FKc; norm_num

/-! ### The exact density of the Cardy weight -/

private lemma sqrt_two_pi_z0 {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) :
    √(2 * π * (c' * besselL x)) = 2 * π * √c' * √x / √3 := by
  have h3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hpos : 0 ≤ 2 * π * √c' * √x / √3 := by positivity
  rw [Real.sqrt_eq_iff_mul_self_eq (by unfold besselL; positivity) hpos]
  have e1 : √c' * √c' = c' := Real.mul_self_sqrt hc'.le
  have e2 : √x * √x = x := Real.mul_self_sqrt hx.le
  have e3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  unfold besselL
  field_simp
  rw [Real.sq_sqrt hc'.le, Real.sq_sqrt hx.le, Real.sq_sqrt (by norm_num)]
  ring

/-- The exact density: with `B = V/as(c'L(x))`, `V(c'x²/3) e^{-c'L(x)} (2/3) c' x = B √c' √x/(√3 π)`. -/
lemma besselV_density {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) :
    besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) =
      besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) *
        (√c' * √x / (√3 * π)) := by
  have hz : 0 < c' * besselL x := by unfold besselL; positivity
  have hA := besselAs_pos hz
  have h3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hs := sqrt_two_pi_z0 hc' hx
  have e1 : √c' * √c' = c' := Real.mul_self_sqrt hc'.le
  have e2 : √x * √x = x := Real.mul_self_sqrt hx.le
  have e3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hc'
  unfold besselAs
  rw [hs]
  have hexp : exp (-(c' * besselL x)) * exp (c' * besselL x) = 1 := by
    rw [← exp_add]; simp
  field_simp
  rw [Real.sq_sqrt hc'.le, Real.sq_sqrt hx.le, Real.sq_sqrt (by norm_num)]
  linear_combination (c' * x * 3 * besselV (c' / 12) (c' * x ^ 2 / 3)) * hexp

/-! ### Lemma `A_V`: the window bound and the far-band bound -/

lemma besselV_nonneg_of_ge {c' x : ℝ} (hc0 : 0 < c') (hc : 24 ≤ c') (hx : 0 < x) :
    0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) :=
  (by positivity : (0 : ℝ) ≤ 8 * π ^ 4 * (c' * x ^ 2 / 3) ^ 2).trans
    (besselV_ge (by linarith) (by positivity))

/-- The uniform Cardy asymptotic (`vlo:Bessel` (c)) gives `0 ≤ B ≤ 2` for `B = V/as(c'L(x))` on
`x ≥ x₀ > 0`, `c' ≥ 96 + 60/x₀`. -/
lemma besselV_ratio_bounds {x₀ c' x : ℝ} (hx₀ : 0 < x₀) (hc : 96 + 60 / x₀ ≤ c') (hx : x₀ ≤ x) :
    0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) ∧
      besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) ≤ 2 := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have h60 : 0 < 60 / x₀ := by positivity
  have hc0 : 0 < c' := by linarith
  have hz : 0 < c' * besselL x := by unfold besselL; positivity
  have hA := besselAs_pos hz
  have hV : 0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) :=
    besselV_nonneg_of_ge hc0 (by linarith) hx0
  refine ⟨div_nonneg hV hA.le, ?_⟩
  have h4 : 4 / x₀ ≤ 60 / x₀ := by gcongr; norm_num
  have hasym := besselV_asymptotic hx₀ (by linarith : 48 + 4 / x₀ ≤ c') hx
  have herr : (96 + 60 / x₀) / c' ≤ 1 := by rw [div_le_one hc0]; exact hc
  have hq0 : 0 < exp (-(4 * π * x)) := exp_pos _
  have hq1 : exp (-(4 * π * x)) ≤ 1 := by
    rw [exp_le_one_iff]; have := Real.pi_pos; nlinarith
  have h1 : (1 - exp (-(4 * π * x))) ^ 2 ≤ 1 := by nlinarith
  have := (abs_le.mp hasym).2
  linarith

/-- **Lemma `A_V`, window form** (`rem:cardy`; `V = V_Vir`, `q = 1`): for `r₀ > 0` there is `C > 0` such
that for `c' ≥ 96 + 120/ξ_*` and `ξ_*/2 ≤ x ≤ ξ_* + r₀`, `V(c'x²/3) ≥ 0` and
`V(t(x)) e^{-c'L(x)} sech²(πx/2) · dt/dσ ≤ C FV_c`, where `x = ξ_* + λσ`, `t = c'x²/3`,
`dt/dσ = (2/3) c' x λ`, `L(x) = 2πx/3`, `FV_c = FVc 1 c'`. -/
theorem besselV_window_bound {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 96 + 120 / xiStar ≤ c' → ∀ x : ℝ, xiStar / 2 ≤ x → x ≤ xiStar + r₀ →
      0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) ∧
      besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
          (2 / 3 * c' * x * lambdaComb c') ≤ C * FVc 1 c' := by
  have hξ := xiStar_pos
  have hE := one_sub_exp_xiStar_pos
  set E : ℝ := (1 - exp (-(4 * π * xiStar))) ^ 2 with hEdef
  have hEp : 0 < E := by positivity
  set H : ℝ := cosh (π * xiStar / 2) ^ 2 with hHdef
  have hHp : 0 < H := by positivity
  have hsξ : 0 < √xiStar := Real.sqrt_pos.mpr hξ
  refine ⟨2 * √(xiStar + r₀) / (√xiStar * E * (1 / H)), by positivity, ?_⟩
  intro c' hc x hx hxr
  have hx₀ : 0 < xiStar / 2 := by positivity
  have hc2 : 96 + 60 / (xiStar / 2) ≤ c' := by
    have : 60 / (xiStar / 2) = 120 / xiStar := by field_simp; ring
    rw [this]; exact hc
  have hx0 : 0 < x := hx₀.trans_le hx
  have hc0 : 0 < c' := by
    have : 0 < 120 / xiStar := by positivity
    linarith
  obtain ⟨hB0, hB2⟩ := besselV_ratio_bounds hx₀ hc2 hx
  have hz : 0 < c' * besselL x := by unfold besselL; positivity
  have hA := besselAs_pos hz
  have hV : 0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) := besselV_nonneg_of_ge hc0 (by
    have : 0 < 120 / xiStar := by positivity
    have : 24 ≤ c' := by
      have h1 : 0 ≤ 120 / xiStar := by positivity
      linarith
    exact this) hx0
  refine ⟨hV, ?_⟩
  rw [show besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) *
        (1 / cosh (π * x / 2) ^ 2) * (2 / 3 * c' * x * lambdaComb c') =
      (besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x)) *
        (1 / cosh (π * x / 2) ^ 2) * lambdaComb c' by ring, besselV_density hc0 hx0]
  have hs2 : 1 / cosh (π * x / 2) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := one_le_cosh (π * x / 2)
    nlinarith
  have hs2p : 0 ≤ 1 / cosh (π * x / 2) ^ 2 := by positivity
  have hlam := lambdaComb_pos' hc0
  have hsx : √x ≤ √(xiStar + r₀) := Real.sqrt_le_sqrt hxr
  have hsx0 : 0 ≤ √x := Real.sqrt_nonneg _
  have h3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hc0
  have hFV : FVc 1 c' = √c' * lambdaComb c' * √xiStar * E * (1 / H) / (√3 * π) := by
    unfold FVc; rw [hEdef, hHdef]; ring
  have hrhs : 2 * √(xiStar + r₀) / (√xiStar * E * (1 / H)) * FVc 1 c' =
      2 * √(xiStar + r₀) * (√c' * lambdaComb c' / (√3 * π)) := by
    rw [hFV]
    have := Real.pi_pos
    have hEn := hEp.ne'
    have hHn := hHp.ne'
    clear_value E H
    field_simp
  rw [hrhs]
  set B := besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) with hB
  have hpi := Real.pi_pos
  have hden : 0 < √3 * π := by positivity
  calc B * (√c' * √x / (√3 * π)) * (1 / cosh (π * x / 2) ^ 2) * lambdaComb c'
      = (B * (1 / cosh (π * x / 2) ^ 2) * √x) * (√c' * lambdaComb c' / (√3 * π)) := by ring
    _ ≤ (2 * 1 * √(xiStar + r₀)) * (√c' * lambdaComb c' / (√3 * π)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h1 : B * (1 / cosh (π * x / 2) ^ 2) ≤ 2 * 1 :=
          mul_le_mul hB2 hs2 hs2p (by norm_num)
        exact mul_le_mul h1 hsx hsx0 (by norm_num)
    _ = _ := by ring

/-- **Lemma `A_V`, far-band form** (`rem:cardy`, `w = 1`): for `x₀ > 0`, `c' ≥ 96 + 60/x₀` and `x ≥ x₀`,
`V(c'x²/3) ≥ 0` and `V e^{-c'L(x)} dt ≤ √c' √x dx` (`dt/dx = (2/3) c' x`). -/
theorem besselV_far_bound {x₀ c' x : ℝ} (hx₀ : 0 < x₀) (hc : 96 + 60 / x₀ ≤ c') (hx : x₀ ≤ x) :
    0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) ∧
      besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤
        √c' * √x := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have h60 : 0 < 60 / x₀ := by positivity
  have hc0 : 0 < c' := by linarith
  obtain ⟨-, hB2⟩ := besselV_ratio_bounds hx₀ hc hx
  refine ⟨besselV_nonneg_of_ge hc0 (by linarith) hx0, ?_⟩
  rw [besselV_density hc0 hx0]
  have h3 : 1 ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hpi := Real.pi_gt_three
  have hden : 0 < √3 * π := by positivity
  have hsc : 0 ≤ √c' * √x := by positivity
  rw [mul_div_assoc']
  rw [div_le_iff₀ hden]
  have h32 : 3 ≤ √3 * π := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hB2 hsc, mul_nonneg hsc (by linarith : (0 : ℝ) ≤ √3 * π - 2)]

/-! ### The abstract Cardy weight -/

/-- **Named property (Lemma `A_V`, window form) of a weight `V c' t`** (`V c'` the weight at central
charge parameter `c'`): for some `C > 0`, `c₀`, all `c' ≥ c₀` and `ξ_*/2 ≤ x ≤ ξ_* + r₀`, `V ≥ 0` at
`t = c'x²/3` and `V e^{-c'L} sech²(πx/2) · dt/dσ ≤ C FV_c` with `FV_c = FVc q c'`.  For the Virasoro weight this
is `besselV_window_bound` (`cardyWindowBound_virasoro`); at general `(w, Q)` it is not formalised. -/
def CardyWindowBound (V : ℝ → ℝ → ℝ) (q r₀ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ ∀ c' : ℝ, c₀ ≤ c' → ∀ x : ℝ, xiStar / 2 ≤ x → x ≤ xiStar + r₀ →
    0 ≤ V c' (c' * x ^ 2 / 3) ∧
      V c' (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
          (2 / 3 * c' * x * lambdaComb c') ≤ C * FVc q c'

/-- **Named property (Lemma `A_V`, far-band form) of a weight `V c' t`**: for `x ≥ x₀`,
`V ≥ 0` and `V e^{-c'L} dt ≤ C √c' √x dx`.  For the Virasoro weight this is `besselV_far_bound`; at general
`(w, Q)` it is the Peano bound `fw:e3.6` (with its factor `(1+x)^{m+p}`), not formalised. -/
def CardyFarBound (V : ℝ → ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ ∀ c' : ℝ, c₀ ≤ c' → ∀ x : ℝ, x₀ ≤ x →
    0 ≤ V c' (c' * x ^ 2 / 3) ∧
      V c' (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤ C * √c' * √x

/-- The Virasoro Cardy weight `V = besselV (c'/12)` satisfies the window bound with `q = 1`. -/
theorem cardyWindowBound_besselV {r₀ : ℝ} (hr₀ : 0 < r₀) :
    CardyWindowBound (fun c' t => besselV (c' / 12) t) 1 r₀ := by
  obtain ⟨C, hC, h⟩ := besselV_window_bound hr₀
  exact ⟨C, 96 + 120 / xiStar, hC, fun c' hc x hx hxr => h c' hc x hx hxr⟩

/-- The Virasoro Cardy weight `V = besselV (c'/12)` satisfies the far-band bound. -/
theorem cardyFarBound_besselV {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CardyFarBound (fun c' t => besselV (c' / 12) t) x₀ :=
  ⟨1, 96 + 60 / x₀, one_pos, fun c' hc x hx => by
    simpa using besselV_far_bound hx₀ hc hx⟩

/-- The concrete Virasoro Cardy kernel `virasoroProblem.cardyV (c'/12)` satisfies the window bound with
`q = 1` (`rem:cardy` at `w = 1`; non-vacuity of `CardyWindowBound`). -/
theorem cardyWindowBound_virasoro {r₀ : ℝ} (hr₀ : 0 < r₀) :
    CardyWindowBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) 1 r₀ := by
  obtain ⟨C, c₀, hC, h⟩ := cardyWindowBound_besselV hr₀
  refine ⟨C, max c₀ 24, hC, fun c' hc x hx hxr => ?_⟩
  have hc0 : 0 < c' := by linarith [le_max_right c₀ 24]
  have hx0 : 0 < x := lt_of_lt_of_le (by have := xiStar_pos; positivity) hx
  beta_reduce
  rw [Integration.virasoro_cardyV_eq_besselV (by linarith [le_max_right c₀ 24])
    (by positivity)]
  exact h c' (le_trans (le_max_left _ _) hc) x hx hxr

/-- The concrete Virasoro Cardy kernel satisfies the far-band bound. -/
theorem cardyFarBound_virasoro {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CardyFarBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) x₀ := by
  obtain ⟨C, c₀, hC, h⟩ := cardyFarBound_besselV hx₀
  refine ⟨C, max c₀ 24, hC, fun c' hc x hx => ?_⟩
  have hc0 : 0 < c' := by linarith [le_max_right c₀ 24]
  have hx0 : 0 < x := hx₀.trans_le hx
  beta_reduce
  rw [Integration.virasoro_cardyV_eq_besselV (by linarith [le_max_right c₀ 24])
    (by positivity)]
  exact h c' (le_trans (le_max_left _ _) hc) x hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.besselV_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_window_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.besselV_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_far_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyWindowBound_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyWindowBound_virasoro

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyFarBound_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyFarBound_virasoro

end FormalResearch.ModularBootstrap.Upper.Window.Cardy

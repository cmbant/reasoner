module

public import FormalResearch.ModularBootstrap.Bessel.VCorollaries
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge
public import FormalResearch.ModularBootstrap.WeightAxioms.ComplexAsymptotics
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
* `cardy_density`, `window_bound_of_ratio`, `far_bound_of_ratio`: the density identity and the two bounds from the
  ratio bound `B = V/as(c'L(x)) ≤ 2`; `cardyV_ratio_bounds`: `0 ≤ B ≤ 2` for every `prob` with `prob.w = 1`, from the
  uniform Cardy asymptotic `cardyV_asymptotic_real` (`n1:L4`(f)) and `0 ≤ Q ≤ 1`.
* `qProb`: `𝔮 = Q(e^{-4πξ_*})/(1 - e^{-4πξ_*})²` (`= 1` at Virasoro, `qProb_virasoro`), so that `FK_c = FKc (qProb prob) 1 c'`;
  `nullPoly_exp_sub_le`: `x ↦ Q(e^{-4πx})` is `4π S`-Lipschitz.
* `CardyWindowBound`, `CardyFarBound`: the two bounds as named properties of an abstract weight
  `V : ℝ → ℝ → ℝ` (`V c' t`), which is all that Lemma `T` uses of the Cardy weight; `prob.cardyV (c'/12)` satisfies
  them for every `prob` with `prob.w = 1` (`cardyWindowBound_prob`, `cardyFarBound_prob`), and in particular the
  Virasoro weight (`cardyWindowBound_virasoro`, `cardyFarBound_virasoro`) and `N = 1` super-Virasoro.  At `w > 1` they
  are the Cardy and Peano input `fw:e3.6`, which is not formalised.

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

lemma FKc_scale (q : ℝ) (f : ℕ) (c' : ℝ) : FKc q f c' = q * FKc 1 f c' := by
  unfold FKc FVc; ring

lemma FKc_pos {q : ℝ} (hq : 0 < q) (f : ℕ) {c' : ℝ} (hc' : 0 < c') : 0 < FKc q f c' := by
  unfold FKc
  have := FVc_pos hq hc'
  have := lambdaComb_pos' hc'
  positivity

/-- `FKc` with the exponent `2 n₁` written as `2 (f - 1/4)`; `FK_c := FK_c^{(1)}` has exponent `3/2`. -/
lemma FKc_one (q c' : ℝ) :
    FKc q 1 c' = FVc q c' * (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) := by
  unfold FKc; norm_num

/-- The scale `q = 𝔮_{w,Q}(ξ_*) = (2ξ_*)^{w-1} Q(e^{-4πξ_*}) / (1 - e^{-4πξ_*})²` of `FV_c` at every weight `w`
(`upper_transfer.tex`, §5); `q = 1` at Virasoro (`qProb_virasoro`) and `q = Q(e^{-4πξ_*})/(1 - e^{-4πξ_*})²` at
`w = 1` (`qProb_of_w_eq_one`). -/
noncomputable def qProb (prob : Crossing.FixedWeightProblem) : ℝ :=
  (2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (exp (-4 * π * xiStar)) / (1 - exp (-(4 * π * xiStar))) ^ 2

/-- At `w = 1` the weight factor `(2ξ_*)^{w-1}` is `1`. -/
lemma qProb_of_w_eq_one (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) :
    qProb prob = prob.nullPoly (exp (-4 * π * xiStar)) / (1 - exp (-(4 * π * xiStar))) ^ 2 := by
  unfold qProb
  simp only [hw, Nat.sub_self, pow_zero, one_mul]

lemma qProb_pos (prob : Crossing.FixedWeightProblem) : 0 < qProb prob := by
  have hq0 : 0 < exp (-4 * π * xiStar) := exp_pos _
  have hq1 : exp (-4 * π * xiStar) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, xiStar_pos])
  unfold qProb
  have := one_sub_exp_xiStar_pos
  have := prob.nullPoly_pos hq0.le hq1
  have := xiStar_pos
  positivity

lemma qProb_virasoro : qProb Crossing.virasoroProblem = 1 := by
  rw [qProb_of_w_eq_one _ rfl, Crossing.virasoroProblem_nullPoly]
  have e : exp (-4 * π * xiStar) = exp (-(4 * π * xiStar)) := by ring_nf
  rw [e]
  have := one_sub_exp_xiStar_pos
  field_simp

/-! ### Lipschitz bound for `x ↦ Q(e^{-4πx})` -/

lemma abs_exp_neg_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |exp (-u) - exp (-v)| ≤ |u - v| := by
  have key : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → exp (-a) - exp (-b) ≤ b - a := by
    intro a b ha hab
    have h1 : exp (-a) ≤ 1 := by rw [exp_le_one_iff]; linarith
    have h2 : exp (-b) = exp (-a) * exp (-(b - a)) := by rw [← exp_add]; ring_nf
    have h3 : 1 - (b - a) ≤ exp (-(b - a)) := by linarith [Real.add_one_le_exp (-(b - a))]
    have h4 : 0 < exp (-a) := exp_pos _
    nlinarith
  rcases le_total u v with h | h
  · have h5 : exp (-v) ≤ exp (-u) := exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (sub_nonneg.2 h5), abs_of_nonpos (by linarith)]
    linarith [key hu h]
  · have h5 : exp (-u) ≤ exp (-v) := exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (sub_nonpos.2 h5), abs_of_nonneg (by linarith)]
    linarith [key hv h]

lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Finset.sum_cons]
    have hP0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i _ => ha0 i
    have hP1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one₀ (fun i _ => ha0 i) fun i _ => ha1 i
    have hR0 : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i _ => hb0 i
    have hR1 : ∏ i ∈ s, b i ≤ 1 := Finset.prod_le_one₀ (fun i _ => hb0 i) fun i _ => hb1 i
    set P := ∏ i ∈ s, a i
    set R := ∏ i ∈ s, b i
    have e : a j * P - b j * R = (a j - b j) * P + b j * (P - R) := by ring
    rw [e]
    calc |(a j - b j) * P + b j * (P - R)| ≤ |(a j - b j) * P| + |b j * (P - R)| := abs_add_le _ _
      _ = |a j - b j| * P + b j * |P - R| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg (hb0 j)]
      _ ≤ |a j - b j| * 1 + 1 * |P - R| := by
          gcongr
          · exact hb1 j
      _ ≤ |a j - b j| + ∑ i ∈ s, |a i - b i| := by linarith

/-- `x ↦ Q(e^{-4πx})` is Lipschitz on `(0, ∞)` with constant `4π S`, `S = totalShift`. -/
lemma nullPoly_exp_sub_le (prob : Crossing.FixedWeightProblem) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |prob.nullPoly (exp (-4 * π * x)) - prob.nullPoly (exp (-4 * π * y))| ≤
      4 * π * prob.totalShift * |x - y| := by
  have hrp : ∀ z : ℝ, ∀ l, (exp (-4 * π * z)) ^ prob.μ l = exp (-(4 * π * prob.μ l * z)) := by
    intro z l
    rw [← Real.exp_mul]; congr 1; ring
  unfold Crossing.FixedWeightProblem.nullPoly
  simp only [hrp]
  have hμ := prob.hμ
  have hpi := Real.pi_pos
  have hterm : ∀ (l : Fin prob.m) (z : ℝ), 0 < z → 0 ≤ 1 - exp (-(4 * π * prob.μ l * z)) ∧
      1 - exp (-(4 * π * prob.μ l * z)) ≤ 1 := by
    intro l z hz
    have h1 : exp (-(4 * π * prob.μ l * z)) ≤ 1 := by
      rw [exp_le_one_iff]; have := hμ l; nlinarith [mul_pos hpi (hμ l)]
    exact ⟨by linarith, by linarith [exp_pos (-(4 * π * prob.μ l * z))]⟩
  refine (abs_prod_sub_prod_le Finset.univ _ _ (fun l => (hterm l x hx).1) (fun l => (hterm l x hx).2)
    (fun l => (hterm l y hy).1) (fun l => (hterm l y hy).2)).trans ?_
  unfold Crossing.FixedWeightProblem.totalShift
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  have hu : 0 ≤ 4 * π * prob.μ l * x := by have := hμ l; positivity
  have hv : 0 ≤ 4 * π * prob.μ l * y := by have := hμ l; positivity
  have := abs_exp_neg_sub_le hu hv
  have e1 : |1 - exp (-(4 * π * prob.μ l * x)) - (1 - exp (-(4 * π * prob.μ l * y)))| =
      |exp (-(4 * π * prob.μ l * x)) - exp (-(4 * π * prob.μ l * y))| := by
    rw [← abs_neg]; congr 1; ring
  rw [e1]
  refine this.trans (le_of_eq ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (by have := hμ l; positivity : (0 : ℝ) ≤ 4 * π * prob.μ l)]

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

/-- The exact density for any value `v` of the Cardy weight: with `B = v/as(c'L(x))`,
`v e^{-c'L(x)} (2/3) c' x = B √c' √x/(√3 π)`. -/
lemma cardy_density {c' x : ℝ} (v : ℝ) (hc' : 0 < c') (hx : 0 < x) :
    v * exp (-(c' * besselL x)) * (2 / 3 * c' * x) =
      v / besselAs (c' * besselL x) * (√c' * √x / (√3 * π)) := by
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
  linear_combination (c' * x * 3 * v) * hexp

/-- The exact density: with `B = V/as(c'L(x))`, `V(c'x²/3) e^{-c'L(x)} (2/3) c' x = B √c' √x/(√3 π)`. -/
lemma besselV_density {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) :
    besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) =
      besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) *
        (√c' * √x / (√3 * π)) :=
  cardy_density _ hc' hx

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

/-- The constant of Lemma `A_V` (window form) for the ratio bound `B ≤ 2 (2x)^p` on `x ≤ ξ_* + r₀` and the scale `q`:
`2 (2(ξ_* + r₀))^p √(ξ_* + r₀) / (q √ξ_* (1 - e^{-4πξ_*})² sech²(πξ_*/2))`. -/
noncomputable def windowConstA (p : ℕ) (q r₀ : ℝ) : ℝ :=
  2 * (2 * (xiStar + r₀)) ^ p * √(xiStar + r₀) / (q * (√xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 *
    (1 / cosh (π * xiStar / 2) ^ 2)))

lemma windowConstA_pos (p : ℕ) {q r₀ : ℝ} (hq : 0 < q) (hr₀ : 0 < r₀) : 0 < windowConstA p q r₀ := by
  unfold windowConstA
  have := xiStar_pos
  have := one_sub_exp_xiStar_pos
  positivity

/-- **Lemma `A_V`, window form, from the ratio bound**: if `B = v/as(c'L(x)) ≤ 2 (2x)^p` at a point
`x ∈ [ξ_*/2, ξ_* + r₀]` then `v e^{-c'L(x)} sech²(πx/2) · dt/dσ ≤ windowConstA p q r₀ · FV_c`
(`dt/dσ = (2/3) c' x λ`, `FV_c = FVc q c'`, any `q > 0`). -/
lemma window_bound_of_ratio (p : ℕ) {q r₀ c' x v : ℝ} (hq : 0 < q) (hc0 : 0 < c')
    (hx : xiStar / 2 ≤ x) (hxr : x ≤ xiStar + r₀)
    (hB2 : v / besselAs (c' * besselL x) ≤ 2 * (2 * x) ^ p) :
    v * exp (-(c' * besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
        (2 / 3 * c' * x * lambdaComb c') ≤ windowConstA p q r₀ * FVc q c' := by
  have hξ := xiStar_pos
  have hE := one_sub_exp_xiStar_pos
  set E : ℝ := (1 - exp (-(4 * π * xiStar))) ^ 2 with hEdef
  have hEp : 0 < E := by positivity
  set H : ℝ := cosh (π * xiStar / 2) ^ 2 with hHdef
  have hHp : 0 < H := by positivity
  have hsξ : 0 < √xiStar := Real.sqrt_pos.mpr hξ
  have hx₀ : 0 < xiStar / 2 := by positivity
  have hx0 : 0 < x := hx₀.trans_le hx
  have hz : 0 < c' * besselL x := by unfold besselL; positivity
  have hA := besselAs_pos hz
  rw [show v * exp (-(c' * besselL x)) *
        (1 / cosh (π * x / 2) ^ 2) * (2 / 3 * c' * x * lambdaComb c') =
      (v * exp (-(c' * besselL x)) * (2 / 3 * c' * x)) *
        (1 / cosh (π * x / 2) ^ 2) * lambdaComb c' by ring, cardy_density v hc0 hx0]
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
  have hFV : FVc q c' = q * (√c' * lambdaComb c' * √xiStar * E * (1 / H)) / (√3 * π) := by
    unfold FVc; rw [hEdef, hHdef]
  have hrhs : windowConstA p q r₀ * FVc q c' =
      2 * (2 * (xiStar + r₀)) ^ p * √(xiStar + r₀) * (√c' * lambdaComb c' / (√3 * π)) := by
    rw [hFV]
    unfold windowConstA
    rw [← hEdef, ← hHdef]
    have := Real.pi_pos
    have hEn := hEp.ne'
    have hHn := hHp.ne'
    have hqn := hq.ne'
    clear_value E H
    field_simp
  rw [hrhs]
  set B := v / besselAs (c' * besselL x) with hB
  have hpi := Real.pi_pos
  have hden : 0 < √3 * π := by positivity
  calc B * (√c' * √x / (√3 * π)) * (1 / cosh (π * x / 2) ^ 2) * lambdaComb c'
      = (B * (1 / cosh (π * x / 2) ^ 2) * √x) * (√c' * lambdaComb c' / (√3 * π)) := by ring
    _ ≤ (2 * (2 * (xiStar + r₀)) ^ p * 1 * √(xiStar + r₀)) * (√c' * lambdaComb c' / (√3 * π)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hxr0 : 0 < xiStar + r₀ := by linarith
        have hxp : (2 * x) ^ p ≤ (2 * (xiStar + r₀)) ^ p :=
          pow_le_pow_left₀ (by positivity) (by linarith) p
        have h1 : B * (1 / cosh (π * x / 2) ^ 2) ≤ 2 * (2 * (xiStar + r₀)) ^ p * 1 :=
          mul_le_mul (hB2.trans (by linarith [hxp])) hs2 hs2p (by positivity)
        exact mul_le_mul h1 hsx hsx0 (by positivity)
    _ = _ := by ring

/-- **Lemma `A_V`, far-band form, from the ratio bound**: if `v/as(c'L(x)) ≤ 2 (2x)^p` at `x > 0` then
`v e^{-c'L(x)} (2/3) c' x ≤ (2x)^p √c' √x`. -/
lemma far_bound_of_ratio (p : ℕ) {c' x v : ℝ} (hc0 : 0 < c') (hx0 : 0 < x)
    (hB2 : v / besselAs (c' * besselL x) ≤ 2 * (2 * x) ^ p) :
    v * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤ (2 * x) ^ p * (√c' * √x) := by
  rw [cardy_density v hc0 hx0]
  have h3 : 1 ≤ √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hpi := Real.pi_gt_three
  have hden : 0 < √3 * π := by positivity
  have hsc : 0 ≤ √c' * √x := by positivity
  have hP : 0 ≤ (2 * x) ^ p := by positivity
  rw [mul_div_assoc']
  rw [div_le_iff₀ hden]
  have h32 : 3 ≤ √3 * π := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hB2 hsc
  have h2 : 0 ≤ (2 * x) ^ p * (√c' * √x) * (√3 * π - 2) :=
    mul_nonneg (mul_nonneg hP hsc) (by linarith)
  nlinarith

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
  refine ⟨windowConstA 0 1 r₀, windowConstA_pos 0 one_pos hr₀, ?_⟩
  intro c' hc x hx hxr
  have hx₀ : 0 < xiStar / 2 := by positivity
  have hc2 : 96 + 60 / (xiStar / 2) ≤ c' := by
    have : 60 / (xiStar / 2) = 120 / xiStar := by field_simp; ring
    rw [this]; exact hc
  have h120 : 0 < 120 / xiStar := by positivity
  have hx0 : 0 < x := hx₀.trans_le hx
  have hc0 : 0 < c' := by linarith
  exact ⟨besselV_nonneg_of_ge hc0 (by linarith) hx0,
    window_bound_of_ratio 0 one_pos hc0 hx hxr (by simpa using (besselV_ratio_bounds hx₀ hc2 hx).2)⟩

/-- **Lemma `A_V`, far-band form** (`rem:cardy`, `w = 1`): for `x₀ > 0`, `c' ≥ 96 + 60/x₀` and `x ≥ x₀`,
`V(c'x²/3) ≥ 0` and `V e^{-c'L(x)} dt ≤ √c' √x dx` (`dt/dx = (2/3) c' x`). -/
theorem besselV_far_bound {x₀ c' x : ℝ} (hx₀ : 0 < x₀) (hc : 96 + 60 / x₀ ≤ c') (hx : x₀ ≤ x) :
    0 ≤ besselV (c' / 12) (c' * x ^ 2 / 3) ∧
      besselV (c' / 12) (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤
        √c' * √x := by
  have hx0 : 0 < x := hx₀.trans_le hx
  have h60 : 0 < 60 / x₀ := by positivity
  have hc0 : 0 < c' := by linarith
  exact ⟨besselV_nonneg_of_ge hc0 (by linarith) hx0,
    by simpa using far_bound_of_ratio 0 hc0 hx0 (by simpa using (besselV_ratio_bounds hx₀ hc hx).2)⟩

/-! ### Lemma `A_V` for every weight-one problem -/

/-- **Lemma `A_V`, uniform Cardy ratio** (`n1:L4`(f); `rem:cardy`), every weight `w = p + 1`: for `x₀ > 0` there is `c₀`
such that for `c' ≥ c₀`, `x ≥ x₀`, the ratio `B = V(c'x²/3)/as(c'L(x))` of the Cardy weight
`V = prob.cardyV (c'/12)` satisfies `0 ≤ B ≤ 2 (2x)^{w-1}` (from `cardyV_asymptotic_real` and `0 ≤ Q ≤ 1`). -/
theorem cardyV_ratio_bounds (prob : Crossing.FixedWeightProblem) {x₀ : ℝ}
    (hx₀ : 0 < x₀) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {c' x : ℝ}, c₀ ≤ c' → x₀ ≤ x →
      0 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ∧
      0 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) ∧
        prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) ≤
          2 * (2 * x) ^ (prob.w - 1) := by
  obtain ⟨C, hC0, hC⟩ := WeightAxioms.cardyV_asymptotic_real prob hx₀
  obtain ⟨-, hQ⟩ := WeightAxioms.nullPoly_exp_bounds prob hx₀
  have hS := prob.totalShift_nonneg
  refine ⟨max (max 1 (24 * prob.totalShift)) C, by positivity, fun {c' x} hc hx => ?_⟩
  have hcm : max 1 (24 * prob.totalShift) ≤ c' := (le_max_left _ _).trans hc
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hcm
  have hcS : 24 * prob.totalShift ≤ c' := (le_max_right _ _).trans hcm
  have hcC : C ≤ c' := (le_max_right _ _).trans hc
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 < x := hx₀.trans_le hx
  have hV : 0 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
    prob.cardyV_nonneg (by linarith) (by positivity)
  have hz : 0 < c' * besselL x := by unfold besselL; positivity
  have hA := besselAs_pos hz
  refine ⟨hV, div_nonneg hV hA.le, ?_⟩
  have h := hC hcm hx
  have hCc : C / c' ≤ 1 := by rw [div_le_one hc0]; exact hcC
  have hQ1 := (hQ hx).2
  have h2 := (abs_le.mp h).2
  have hP : 0 < (2 * x) ^ (prob.w - 1) := by positivity
  have hAA : (0 : ℝ) < besselAs (c' * (2 * π * x / 3)) := by unfold besselL at hA; exact hA
  have e1 : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) =
      (2 * x) ^ (prob.w - 1) *
        (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * π * x / 3)))) := by
    unfold besselL; field_simp
  rw [e1]
  have h3 : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
      ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * π * x / 3))) ≤ 2 := by linarith
  calc _ ≤ (2 * x) ^ (prob.w - 1) * 2 := mul_le_mul_of_nonneg_left h3 hP.le
    _ = _ := by ring

/-! ### The abstract Cardy weight -/

/-- **Named property (Lemma `A_V`, window form) of a weight `V c' t`** (`V c'` the weight at central
charge parameter `c'`): for some `C > 0`, `c₀`, all `c' ≥ c₀` and `ξ_*/2 ≤ x ≤ ξ_* + r₀`, `V ≥ 0` at
`t = c'x²/3` and `V e^{-c'L} sech²(πx/2) · dt/dσ ≤ C FV_c` with `FV_c = FVc q c'`.  The constant absorbs the weight
factor `(2(ξ_* + r₀))^{w-1}` of the Cardy asymptotics.  For the Virasoro weight this
is `besselV_window_bound` (`cardyWindowBound_besselV`), and for every problem, at every weight, `cardyWindowBound_prob`. -/
def CardyWindowBound (V : ℝ → ℝ → ℝ) (q r₀ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ ∀ c' : ℝ, c₀ ≤ c' → ∀ x : ℝ, xiStar / 2 ≤ x → x ≤ xiStar + r₀ →
    0 ≤ V c' (c' * x ^ 2 / 3) ∧
      V c' (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (1 / cosh (π * x / 2) ^ 2) *
          (2 / 3 * c' * x * lambdaComb c') ≤ C * FVc q c'

/-- **Named property (Lemma `A_V`, far-band form) of a weight `V c' t`, order `p`**: for `x ≥ x₀`,
`V ≥ 0` and `V e^{-c'L} dt ≤ C √c' √x (1+x)^p dx` (`rem:cardy` at weight `w = p + 1`; the factor `(2x)^{w-1}` of the
Cardy asymptotics, replacing the Peano bound `fw:e3.6` of the paper: `n1:L4`(f) is uniform for `x → ∞`).
`CardyFarBound` is the case `p = 0`. -/
def CardyFarBoundP (p : ℕ) (V : ℝ → ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ ∀ c' : ℝ, c₀ ≤ c' → ∀ x : ℝ, x₀ ≤ x →
    0 ≤ V c' (c' * x ^ 2 / 3) ∧
      V c' (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤
        C * √c' * √x * (1 + x) ^ p

/-- **Named property (Lemma `A_V`, far-band form) of a weight `V c' t`**: for `x ≥ x₀`,
`V ≥ 0` and `V e^{-c'L} dt ≤ C √c' √x dx`.  For the Virasoro weight this is `besselV_far_bound`, and for every
weight-one problem `cardyFarBound_prob`; at every weight the statement is `CardyFarBoundP (w-1)`
(`cardyFarBoundP_prob`), of which this is the case `p = 0` (`cardyFarBoundP_zero`). -/
def CardyFarBound (V : ℝ → ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ ∀ c' : ℝ, c₀ ≤ c' → ∀ x : ℝ, x₀ ≤ x →
    0 ≤ V c' (c' * x ^ 2 / 3) ∧
      V c' (c' * x ^ 2 / 3) * exp (-(c' * besselL x)) * (2 / 3 * c' * x) ≤ C * √c' * √x

lemma cardyFarBoundP_zero {V : ℝ → ℝ → ℝ} {x₀ : ℝ} :
    CardyFarBoundP 0 V x₀ ↔ CardyFarBound V x₀ := by
  simp [CardyFarBoundP, CardyFarBound]

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

/-- **The window bound for every problem, at every weight** (`rem:cardy`): the concrete Cardy kernel
`prob.cardyV (c'/12)` satisfies `CardyWindowBound` for every scale `q > 0` (the constant absorbs `q` and the factor
`(2(ξ_* + r₀))^{w-1}`; the paper's `q` is `qProb prob`). -/
theorem cardyWindowBound_prob (prob : Crossing.FixedWeightProblem) {q r₀ : ℝ}
    (hq : 0 < q) (hr₀ : 0 < r₀) :
    CardyWindowBound (fun c' t => prob.cardyV (c' / 12) t) q r₀ := by
  have hξ := xiStar_pos
  obtain ⟨c₀, hc₀, h⟩ := cardyV_ratio_bounds prob (half_pos hξ)
  refine ⟨windowConstA (prob.w - 1) q r₀, c₀, windowConstA_pos _ hq hr₀, fun c' hc x hx hxr => ?_⟩
  have hc0 : 0 < c' := hc₀.trans_le hc
  obtain ⟨h1, -, h2⟩ := h hc hx
  exact ⟨h1, window_bound_of_ratio _ hq hc0 hx hxr h2⟩

/-- **The far-band bound for every problem, at every weight** (`rem:cardy`): with `p = w - 1`,
`V e^{-c'L} dt ≤ 2^p √c' √x (1+x)^p dx`. -/
theorem cardyFarBoundP_prob (prob : Crossing.FixedWeightProblem) {x₀ : ℝ}
    (hx₀ : 0 < x₀) : CardyFarBoundP (prob.w - 1) (fun c' t => prob.cardyV (c' / 12) t) x₀ := by
  obtain ⟨c₀, hc₀, h⟩ := cardyV_ratio_bounds prob hx₀
  refine ⟨2 ^ (prob.w - 1), c₀, by positivity, fun c' hc x hx => ?_⟩
  have hc0 : 0 < c' := hc₀.trans_le hc
  have hx0 : 0 < x := hx₀.trans_le hx
  obtain ⟨h1, -, h2⟩ := h hc hx
  refine ⟨h1, (far_bound_of_ratio _ hc0 hx0 h2).trans ?_⟩
  have hp : (2 * x) ^ (prob.w - 1) ≤ 2 ^ (prob.w - 1) * (1 + x) ^ (prob.w - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hs : 0 ≤ √c' * √x := by positivity
  calc (2 * x) ^ (prob.w - 1) * (√c' * √x)
      ≤ (2 ^ (prob.w - 1) * (1 + x) ^ (prob.w - 1)) * (√c' * √x) :=
        mul_le_mul_of_nonneg_right hp hs
    _ = _ := by ring

/-- **The far-band bound for every weight-one problem** (`rem:cardy` at `w = 1`). -/
theorem cardyFarBound_prob (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) {x₀ : ℝ}
    (hx₀ : 0 < x₀) : CardyFarBound (fun c' t => prob.cardyV (c' / 12) t) x₀ := by
  have h := cardyFarBoundP_prob prob hx₀
  rw [hw, Nat.sub_self] at h
  exact cardyFarBoundP_zero.1 h

/-- The concrete Virasoro Cardy kernel `virasoroProblem.cardyV (c'/12)` satisfies the window bound with
`q = 1` (`rem:cardy` at `w = 1`; non-vacuity of `CardyWindowBound`). -/
theorem cardyWindowBound_virasoro {r₀ : ℝ} (hr₀ : 0 < r₀) :
    CardyWindowBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) 1 r₀ :=
  cardyWindowBound_prob Crossing.virasoroProblem one_pos hr₀

/-- The concrete Virasoro Cardy kernel satisfies the far-band bound. -/
theorem cardyFarBound_virasoro {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CardyFarBound (fun c' t => Crossing.virasoroProblem.cardyV (c' / 12) t) x₀ :=
  cardyFarBound_prob Crossing.virasoroProblem rfl hx₀

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

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyWindowBound_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyWindowBound_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyFarBound_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyFarBound_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyV_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyV_ratio_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyFarBoundP_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyFarBoundP_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.Cardy.cardyFarBound_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyFarBound_prob

end FormalResearch.ModularBootstrap.Upper.Window.Cardy

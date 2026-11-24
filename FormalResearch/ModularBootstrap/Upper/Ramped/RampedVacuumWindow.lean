module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumProfile
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumWeight
public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumMain
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFarBand

/-!
# The pointwise window inequality for the ramped comb (`rem:thmU` Step (5), Langer window)

For `x ∈ [ξ_*/2, ξ_* + 1/2]` the weighted Cardy-comb integrand `(2/3) c' x h₀(c'x²/3) V(c'x²/3)` is bounded by
`FK_c C_* κ σ'(x) (w(σ) + |w(σ)| (c₁ λ|σ| + c₂ c'^{-2/3}))`, `σ = τ(x)/λ`, `w(σ) = Re W_D(-κσ)`
(`rampedWindow_pointwise`).

* `signed_amp_le`, `theta_alg`: the signed amplitude step.  The comb is `-amp` where `w < 0` and at most `amp`
  elsewhere, with `amp` within `e^{±δ}` of `G |w|` (`rampedComb_amplitude`); this gives
  `t ≤ G (w + (e^δ - 1)|w|)` without any sign analysis beyond `χ'_1`;
* `density_identity`, `theta_bound`: the Cardy density `V = besselV_density` against `FK_c C_* κ σ'`, and the weight
  `Θ = M_wt (B_c / E)` with `|Θ - 1| + Θ (e^δ - 1) ≤ c₁ λ|σ| + c₂ c'^{-2/3}` (`besselV_asymptotic` two-sided,
  `|M_wt - 1| ≤ C λ|σ|`);
* `rampedWFun`, `rampedW_neg_imp`: the window function and `W_D(-κσ) < 0 → σ < σ_1`.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.Special

lemma signed_amp_le {t amp G w δ : ℝ} (hG : 0 ≤ G)
    (hlo : Real.exp (-δ) * (G * |w|) ≤ amp) (hhi : amp ≤ Real.exp δ * (G * |w|))
    (ht : t ≤ amp) (hneg : w < 0 → t = -amp) :
    t ≤ G * (w + (Real.exp δ - 1) * |w|) := by
  rcases lt_or_ge w 0 with hw | hw
  · have h1 := hneg hw
    rw [abs_of_neg hw] at hlo hhi ⊢
    have hn : 0 ≤ -w := by linarith
    have hamb : Real.exp δ + Real.exp (-δ) ≥ 2 := by
      have := Real.add_one_le_exp δ
      have := Real.add_one_le_exp (-δ)
      linarith
    have e : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
    have hGw : 0 ≤ G * -w := mul_nonneg hG hn
    nlinarith [mul_nonneg hGw (sub_nonneg.2 hamb), Real.exp_pos δ, Real.exp_pos (-δ)]
  · rw [abs_of_nonneg hw] at hhi ⊢
    nlinarith

lemma theta_alg {Θ w δ E : ℝ} (hΘ : 0 ≤ Θ) (hδ : 0 ≤ δ) (hE : |Θ - 1| + Θ * (Real.exp δ - 1) ≤ E) :
    Θ * (w + (Real.exp δ - 1) * |w|) ≤ w + E * |w| := by
  have h1 : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
  have h2 : Θ * w ≤ w + |Θ - 1| * |w| := by
    have : Θ * w = w + (Θ - 1) * w := by ring
    rw [this]
    have := le_abs_self ((Θ - 1) * w)
    rw [abs_mul] at this
    linarith
  have h3 : 0 ≤ Θ * (Real.exp δ - 1) * |w| := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hE (abs_nonneg w)]

lemma density_identity {c' x Bc lam : ℝ} (hc' : 0 < c') (hx : 0 < x) (hlam : 0 < lam)
    (hlamdef : lam = lambdaComb c') :
    (1 / cosh (π * x / 2) ^ 2) * (Bc * √c' * √x / (√3 * π)) *
        ((2 * √2 / (π * lam)) ^ (3 / 2 : ℝ) * Real.exp (-(3 / 2) * kS x) * (CStar * kappaAiry)) =
      FKc 1 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lam) *
        (mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2)) := by
  have hx0 := xiStar_pos
  have hE : 0 < (1 - Real.exp (-(4 * π * x))) ^ 2 := by
    have h : 0 < 1 - Real.exp (-(4 * π * x)) := by
      have : Real.exp (-(4 * π * x)) < 1 := by
        rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
      linarith
    positivity
  have hEs : 0 < (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    have := one_sub_exp_xiStar_pos; positivity
  have hτ := deriv_langerTau_pos hx
  subst hlamdef
  unfold mwt mUnn
  rw [FKc_one]
  unfold FVc
  rw [kS_xiStar]
  simp only [mul_zero, Real.exp_zero, mul_one]
  generalize (1 - Real.exp (-(4 * π * x))) ^ 2 = Ex at *
  generalize (1 - Real.exp (-(4 * π * xiStar))) ^ 2 = Es at *
  have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hs : 0 < √xiStar := Real.sqrt_pos.2 hx0
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have hsc : 0 < √c' := Real.sqrt_pos.2 hc'
  have hpi := Real.pi_pos
  have hch : 0 < cosh (π * x / 2) ^ 2 := by positivity
  have hch0 : 0 < cosh (π * xiStar / 2) ^ 2 := by positivity
  have hq : 0 < (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hκ := kappaAiry_pos
  have hCs : 0 < CStar := by unfold CStar; have := kappaAiry_pos; positivity
  field_simp

/-- `density_identity` at the scale `q > 0`: `FK_c = FKc 1 1 c'` is replaced by `FKc q 1 c' = q FKc 1 1 c'`
and `Θ` by `Θ / q`. -/
lemma density_identity_q {c' x Bc lam q : ℝ} (hq : 0 < q) (hc' : 0 < c') (hx : 0 < x) (hlam : 0 < lam)
    (hlamdef : lam = lambdaComb c') :
    (1 / cosh (π * x / 2) ^ 2) * (Bc * √c' * √x / (√3 * π)) *
        ((2 * √2 / (π * lam)) ^ (3 / 2 : ℝ) * Real.exp (-(3 / 2) * kS x) * (CStar * kappaAiry)) =
      FKc q 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lam) *
        (mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / q) := by
  rw [density_identity hc' hx hlam hlamdef, FKc_scale q 1 c']
  field_simp

lemma one_sub_exp_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-(4 * π * x)) := by
  have : Real.exp (-(4 * π * x)) < 1 := by
    rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
  linarith

/-- The minimum of `(1 - e^{-4πx})²` on `x ≥ ξ_*/2`. -/
noncomputable def Emin : ℝ := (1 - Real.exp (-(2 * π * xiStar))) ^ 2

lemma Emin_pos : 0 < Emin := by
  unfold Emin
  have : 0 < 1 - Real.exp (-(2 * π * xiStar)) := by
    have : Real.exp (-(2 * π * xiStar)) < 1 := by
      rw [Real.exp_lt_one_iff]; have := Real.pi_pos; have := xiStar_pos; nlinarith
    linarith
  positivity

lemma Emin_le {x : ℝ} (hx : xiStar / 2 ≤ x) : Emin ≤ (1 - Real.exp (-(4 * π * x))) ^ 2 := by
  unfold Emin
  have h1 : Real.exp (-(4 * π * x)) ≤ Real.exp (-(2 * π * xiStar)) := by
    apply Real.exp_le_exp.2
    have := Real.pi_pos
    nlinarith
  have h2 : 0 < 1 - Real.exp (-(2 * π * xiStar)) := by
    have : Real.exp (-(2 * π * xiStar)) < 1 := by
      rw [Real.exp_lt_one_iff]; have := Real.pi_pos; have := xiStar_pos; nlinarith
    linarith
  exact pow_le_pow_left₀ h2.le (by linarith) 2

/-- `|E(x) - E(ξ_*)| ≤ 8π |x - ξ_*|` for `E(x) = (1 - e^{-4πx})²`, `x > 0`. -/
lemma abs_E_sub_le {x : ℝ} (hx : 0 < x) :
    |(1 - Real.exp (-(4 * π * x))) ^ 2 - (1 - Real.exp (-(4 * π * xiStar))) ^ 2| ≤
      8 * π * |x - xiStar| := by
  have hxs := xiStar_pos
  have hpi := Real.pi_pos
  have ha0 := Real.exp_pos (-(4 * π * x))
  have hb0 := Real.exp_pos (-(4 * π * xiStar))
  have ha1 : Real.exp (-(4 * π * x)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hb1 : Real.exp (-(4 * π * xiStar)) < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hab := abs_exp_neg_sub_le (u := 4 * π * x) (v := 4 * π * xiStar) (by positivity) (by positivity)
  have e1 : |4 * π * x - 4 * π * xiStar| = 4 * π * |x - xiStar| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
  rw [e1] at hab
  set a := Real.exp (-(4 * π * x))
  set b := Real.exp (-(4 * π * xiStar))
  have e2 : (1 - a) ^ 2 - (1 - b) ^ 2 = (b - a) * (2 - a - b) := by ring
  rw [e2, abs_mul]
  have h2 : |2 - a - b| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h3 : |b - a| ≤ 4 * π * |x - xiStar| := by rw [abs_sub_comm]; exact hab
  calc |b - a| * |2 - a - b| ≤ (4 * π * |x - xiStar|) * 2 :=
        mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
    _ = 8 * π * |x - xiStar| := by ring

/-- The bound on `Θ / q`, `Θ = M_wt(x) · B_c/E(x)`, and `(Θ / q) (e^δ - 1)`, for a Cardy ratio `B_c` within
`K/c'` of `Q(e^{-4πx})`; `q = qProb prob = Q(e^{-4πξ_*})/E(ξ_*)` (`w = 1`). -/
theorem theta_bound (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (K Ca : ℝ) (hK : 0 < K) (hCa : 0 < Ca) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ᶠ c' : ℝ in atTop, ∀ x ∈ langerX (1 / 2), ∀ Bc δ : ℝ, 0 ≤ Bc →
      |Bc - prob.nullPoly (Real.exp (-4 * π * x))| ≤ K / c' → 0 ≤ δ →
      δ ≤ Ca * c' ^ (-(2 / 3 : ℝ)) → δ ≤ 1 / 2 →
      |mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / qProb prob - 1| +
        mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / qProb prob * (Real.exp δ - 1) ≤
        c1 * lambdaComb c' * |langerTau x / lambdaComb c'| + c2 * c' ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨CM, hCM, hMw⟩ := mwt_sub_one_le
  obtain ⟨cτ, hcτ, hτ⟩ := abs_sub_xiStar_le_tau
  have hxs := xiStar_pos
  have hpi := Real.pi_pos
  have hq := qProb_pos prob
  have hS := prob.totalShift_nonneg
  have hEm := Emin_pos
  have hEsp : 0 < (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    have := one_sub_exp_xiStar_pos; positivity
  have hQs : prob.nullPoly (Real.exp (-4 * π * xiStar)) =
      qProb prob * (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    rw [qProb_of_w_eq_one prob hw]
    exact (div_mul_cancel₀ _ hEsp.ne').symm
  set q : ℝ := qProb prob with hqdef
  set Es : ℝ := (1 - Real.exp (-(4 * π * xiStar))) ^ 2 with hEs
  set Qs : ℝ := prob.nullPoly (Real.exp (-4 * π * xiStar)) with hQsdef
  set Lq : ℝ := 4 * π * prob.totalShift with hLq
  have hLq0 : 0 ≤ Lq := by rw [hLq]; positivity
  set C0 : ℝ := (Lq + 8 * π * q) / (Emin * q) with hC0
  have hC0p : 0 < C0 := by rw [hC0]; positivity
  set R : ℝ := 2 + C0 * (1 / 2 + xiStar) with hR
  have hRp : 0 < R := by rw [hR]; positivity
  set Mmax : ℝ := 1 + CM * (1 / 2 + xiStar) with hMmax
  set K1 : ℝ := K / (Emin * q) with hK1
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  refine ⟨(CM * R + C0) / cτ, K1 + 2 * Mmax * R * Ca, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 K1)] with c' hc'
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hc'0 : 0 < c' := by linarith
  have hlam : 0 < lambdaComb c' := lamPos hc'0
  intro x hx Bc δ hBc0 hBc hδ0 hδCa hδ12
  have hx0 : 0 < x := by linarith [hx.1]
  have hxξ : xiStar / 2 ≤ x := hx.1
  set Ex : ℝ := (1 - Real.exp (-(4 * π * x))) ^ 2 with hEx
  have hExm : Emin ≤ Ex := Emin_le hxξ
  have hExp : 0 < Ex := hEm.trans_le hExm
  set ρ : ℝ := Bc / (Ex * q) with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hBc0 (by positivity)
  have hΘ : mwt x * (Bc / Ex) / q = mwt x * ρ := by rw [hρ]; field_simp
  rw [hΘ]
  have hd : |x - xiStar| ≤ 1 / 2 + xiStar := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  -- distance bounds
  have hQ1 : |prob.nullPoly (Real.exp (-4 * π * x)) - Qs| ≤ Lq * |x - xiStar| :=
    nullPoly_exp_sub_le prob hx0 hxs
  have hE1 := abs_E_sub_le hx0
  rw [← hEx, ← hEs] at hE1
  have hnum : |Bc - Ex * q| ≤ K / c' + (Lq + 8 * π * q) * |x - xiStar| := by
    have e : Bc - Ex * q = (Bc - prob.nullPoly (Real.exp (-4 * π * x))) +
        (prob.nullPoly (Real.exp (-4 * π * x)) - Qs) + q * (Es - Ex) := by
      rw [hQs]; ring
    rw [e]
    have h3 : |q * (Es - Ex)| ≤ q * (8 * π * |x - xiStar|) := by
      rw [abs_mul, abs_of_pos hq, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hE1 hq.le
    calc _ ≤ |Bc - prob.nullPoly (Real.exp (-4 * π * x))| +
          |prob.nullPoly (Real.exp (-4 * π * x)) - Qs| + |q * (Es - Ex)| := abs_add_three _ _ _
      _ ≤ K / c' + Lq * |x - xiStar| + q * (8 * π * |x - xiStar|) := by linarith
      _ = _ := by ring
  have hρ1 : |ρ - 1| ≤ K / c' / (Emin * q) + C0 * |x - xiStar| := by
    have : ρ - 1 = (Bc - Ex * q) / (Ex * q) := by rw [hρ]; field_simp
    rw [this, abs_div, abs_of_pos (by positivity : 0 < Ex * q)]
    have hden : Emin * q ≤ Ex * q := mul_le_mul_of_nonneg_right hExm hq.le
    calc |Bc - Ex * q| / (Ex * q) ≤ (K / c' + (Lq + 8 * π * q) * |x - xiStar|) / (Ex * q) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (K / c' + (Lq + 8 * π * q) * |x - xiStar|) / (Emin * q) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by rw [hC0]; field_simp
  have hε1 : K / c' / (Emin * q) ≤ 1 := by
    have : K1 ≤ c' := (le_max_right _ _).trans hc'
    rw [div_le_one (by positivity), div_le_iff₀ hc'0]
    rw [hK1, div_le_iff₀ (by positivity)] at this
    linarith
  have hρ2 : ρ ≤ R := by
    have h1 := (abs_le.1 hρ1).2
    have h2 : C0 * |x - xiStar| ≤ C0 * (1 / 2 + xiStar) := mul_le_mul_of_nonneg_left hd hC0p.le
    rw [hR]; linarith
  have hM1 : |mwt x - 1| ≤ CM * |x - xiStar| := hMw x hx
  have hMle : mwt x ≤ Mmax := by
    have := (abs_le.1 hM1).2
    have h3 : CM * |x - xiStar| ≤ CM * (1 / 2 + xiStar) := mul_le_mul_of_nonneg_left hd hCM.le
    rw [hMmax]; linarith
  have hM0 : 0 ≤ mwt x := by
    unfold mwt
    have := mUnn_pos hx0
    have := mUnn_pos hxs
    have := deriv_langerTau_pos hx0
    positivity
  have hσ : |x - xiStar| ≤ lambdaComb c' * |langerTau x / lambdaComb c'| / cτ := by
    have h := hτ x hxξ
    have : lambdaComb c' * |langerTau x / lambdaComb c'| = |langerTau x| := by
      rw [abs_div, abs_of_pos hlam]; field_simp
    rw [this, le_div_iff₀ hcτ]
    linarith
  have hexp : Real.exp δ - 1 ≤ 2 * δ := by
    have := exp_le_one_add_two_mul hδ0 hδ12
    linarith
  have hT1 : |mwt x * ρ - 1| ≤ |mwt x - 1| * ρ + |ρ - 1| := by
    have : mwt x * ρ - 1 = (mwt x - 1) * ρ + (ρ - 1) := by ring
    rw [this]
    calc |(mwt x - 1) * ρ + (ρ - 1)| ≤ |(mwt x - 1) * ρ| + |ρ - 1| := abs_add_le _ _
      _ = |mwt x - 1| * ρ + |ρ - 1| := by rw [abs_mul, abs_of_nonneg hρ0]
  have hA : |mwt x - 1| * ρ ≤ R * (CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ)) := by
    have h1 : |mwt x - 1| ≤ CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) :=
      hM1.trans (mul_le_mul_of_nonneg_left hσ hCM.le)
    have h2 := mul_le_mul h1 hρ2 hρ0 (by positivity)
    linarith
  have hB : mwt x * ρ * (Real.exp δ - 1) ≤ Mmax * R * (2 * (Ca * c' ^ (-(2 / 3 : ℝ)))) := by
    have h0 : 0 ≤ Real.exp δ - 1 := by linarith [Real.add_one_le_exp δ]
    have h1 : mwt x * ρ ≤ Mmax * R := mul_le_mul hMle hρ2 hρ0 (hM0.trans hMle)
    calc mwt x * ρ * (Real.exp δ - 1) ≤ (Mmax * R) * (2 * (Ca * c' ^ (-(2 / 3 : ℝ)))) :=
          mul_le_mul h1 (hexp.trans (by linarith)) h0 (mul_nonneg (hM0.trans hMle) hRp.le)
      _ = _ := by ring
  have hC : K / c' / (Emin * q) ≤ K1 * c' ^ (-(2 / 3 : ℝ)) := by
    have : c'⁻¹ ≤ c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hc'1 (by norm_num)
    calc K / c' / (Emin * q) = K1 * c'⁻¹ := by rw [hK1]; field_simp
      _ ≤ K1 * c' ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left this (by positivity)
  have hCd : C0 * |x - xiStar| ≤ C0 * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) :=
    mul_le_mul_of_nonneg_left hσ hC0p.le
  have hfin : R * (CM * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ)) +
      C0 * (lambdaComb c' * |langerTau x / lambdaComb c'| / cτ) =
      (CM * R + C0) / cτ * lambdaComb c' * |langerTau x / lambdaComb c'| := by ring
  linarith [hT1, hA, hB, hρ1, hC, hCd, hfin]

lemma combProfile_ofReal_eq {c' x : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (B : ℂ → ℂ) :
    combProfile c' B (c' * x ^ 2 / 3) = 1 / cosh (π * x / 2) ^ 2 * (B (x : ℂ)).re := by
  unfold combProfile combH0
  rw [xOf_comp hc' hx, Upper.Membership.sechSqProfile_ofReal, Complex.re_ofReal_mul]

/-- The window function `σ ↦ Re W_D(-κσ)` of the ramped comb. -/
noncomputable def rampedWFun (P : RampedParams) (d c' : ℝ) (σ : ℝ) : ℝ :=
  (designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * σ)).re

lemma norm_designAiryW_ramped (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (d u : ℝ) :
    ‖designAiryW (rampedNode d c') (rampedEta P c') u‖ = |(designAiryW (rampedNode d c') (rampedEta P c') u).re| := by
  obtain ⟨S, hS, h⟩ := rampedW_form P hc' d u
  rw [h, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]

/-- `W_D(-κσ) < 0` forces `σ < σ_1 = rampedNode d c' 1`. -/
lemma rampedW_neg_imp {P : RampedParams} {c' : ℝ} (hc' : 0 < c') (d σ : ℝ)
    (hw : rampedWFun P d c' σ < 0) : σ < rampedNode d c' 1 := by
  obtain ⟨S, hS, h⟩ := rampedW_form P hc' d (-kappaAiry * σ)
  unfold rampedWFun at hw
  rw [h, Complex.ofReal_re] at hw
  have hκ := kappaAiry_pos
  have h1 : rampedNode d c' 1 = (-airyZero 1 + d) / kappaAiry := by
    simp only [rampedNode, sNodeAiry, ↓reduceIte, abs_of_neg (airyZero_neg 1)]
    ring
  have hpos : 0 < -kappaAiry * σ - (airyZero 1 - d) := by
    by_contra hnot
    push Not at hnot
    have : 0 ≤ -(-kappaAiry * σ - (airyZero 1 - d)) * S := by nlinarith
    linarith
  rw [h1, lt_div_iff₀ hκ]
  linarith

/-- **The pointwise window inequality** (`rem:thmU` Step (5), Langer window): for `x ∈ [ξ_*/2, ξ_* + 1/2]`,
`(2/3) c' x · h₀(c'x²/3) V(c'x²/3) ≤ FK_c C_* κ σ'(x) (w(σ) + |w(σ)| (c₁ λ|σ| + c₂ c'^{-2/3}))`,
`σ = τ(x)/λ`, `w(σ) = Re W_D(-κσ)` (`σ' = τ'(x)/λ`). -/
theorem rampedWindow_pointwise (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ P : RampedParams,
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x ∈ langerX (1 / 2),
      (2 * c' * x / 3) * (combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3) *
          prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) ≤
        FKc (qProb prob) 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') *
          (rampedWFun P d c' (sigmaOf c' x) + |rampedWFun P d c' (sigmaOf c' x)| *
            (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)))) := by
  obtain ⟨Ca, hCa, hampP⟩ := rampedComb_amplitude
  obtain ⟨K0, hK0, hKas⟩ := WeightAxioms.cardyV_asymptotic_real prob (half_pos xiStar_pos)
  obtain ⟨c1, c2, hc1, hc2, hth⟩ := theta_bound prob hw (K0 + 1) Ca (by linarith) hCa
  refine ⟨c1, c2, hc1, hc2, fun P => ?_⟩
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  have hδev := eventually_rpow_neg_le (p := 2 / 3) (ε := 1 / (2 * Ca)) (by norm_num) (by positivity)
  filter_upwards [hampP P, hth, ramped_phaseHyp,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num), h_ev, hδev,
    eventually_ge_atTop (max 1 (24 * prob.totalShift)), eventually_ge_atTop (1 : ℝ)]
    with c' hamp hthc hph hin ⟨_, _, _, hgap⟩ hδ hcS hc1 d hd0 hdD x hx
  have hxs := xiStar_pos
  have hc'0 : 0 < c' := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hlam : 0 < lambdaComb c' := lamPos hc'0
  have hd1 : d ≤ 1 := hdD.trans rampedD0_le_one
  -- the comb is real on the real axis
  have hPh := hph P d hd0 hd1
  have hI : InnerCombHyp c' (rampedComb P d c') :=
    hin (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') hPh.1 hPh.2.1
  have hBim : (rampedComb P d c' (x : ℂ)).im = 0 := hI.real x
  have hBnorm : ‖rampedComb P d c' (x : ℂ)‖ = |(rampedComb P d c' (x : ℂ)).re| := by
    have : rampedComb P d c' (x : ℂ) = (((rampedComb P d c' (x : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hBim])
    conv_lhs => rw [this]
    rw [Complex.norm_real, Real.norm_eq_abs]
  set b : ℝ := (rampedComb P d c' (x : ℂ)).re with hb
  set w : ℝ := rampedWFun P d c' (sigmaOf c' x) with hwdef
  set δ : ℝ := Ca * c' ^ (-(2 / 3 : ℝ)) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ12 : δ ≤ 1 / 2 := by
    rw [hδdef]
    calc Ca * c' ^ (-(2 / 3 : ℝ)) ≤ Ca * (1 / (2 * Ca)) := mul_le_mul_of_nonneg_left hδ hCa.le
      _ = 1 / 2 := by field_simp
  -- amplitude
  obtain ⟨hlo, hhi⟩ := hamp d hd0 hdD x hx
  have hWn : ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ = |w| :=
    norm_designAiryW_ramped P hc'0 d _
  have hsl : slitL x = Bessel.besselL x := Upper.Window.Tail.slitL_eq_besselL hx0.le
  rw [hWn, hsl] at hlo hhi
  set G : ℝ := (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) * Real.exp (-(3 / 2) * kS x) *
    (CStar * kappaAiry) with hG
  have hG0 : 0 ≤ G := by
    have hCs : 0 < CStar := by unfold CStar; have := kappaAiry_pos; positivity
    have := kappaAiry_pos
    positivity
  set amp : ℝ := ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * Bessel.besselL x) with hamp_def
  have hlo' : Real.exp (-δ) * (G * |w|) ≤ amp := by
    refine le_trans (le_of_eq ?_) hlo
    rw [hG, hδdef]; unfold kS; ring_nf
  have hhi' : amp ≤ Real.exp δ * (G * |w|) := by
    refine hhi.trans (le_of_eq ?_)
    rw [hG, hδdef]; unfold kS; ring_nf
  set t : ℝ := b * Real.exp (c' * Bessel.besselL x) with htdef
  have hexpL : 0 < Real.exp (c' * Bessel.besselL x) := Real.exp_pos _
  have ht : t ≤ amp := by
    rw [htdef, hamp_def, hBnorm]
    exact mul_le_mul_of_nonneg_right (le_abs_self b) hexpL.le
  have hneg : w < 0 → t = -amp := by
    intro hwneg
    have hσ1 := rampedW_neg_imp hc'0 d _ hwneg
    -- `x < χ'_1`
    have hsite : designSite c' (rampedSigma d c') 1 = langerTauInv (lambdaComb c' * rampedNode d c' 1) :=
      designSite_rampedSigma hc'0 d 1
    have hn1 : 0 ≤ rampedNode d c' 1 := rampedNode_nonneg hd0 c' le_rfl
    have hτχ : langerTau (designSite c' (rampedSigma d c') 1) = lambdaComb c' * rampedNode d c' 1 := by
      rw [hsite]; exact langerTau_langerTauInv (mul_nonneg hlam.le hn1)
    have hχ0 : 0 < designSite c' (rampedSigma d c') 1 :=
      lt_of_lt_of_le hxs (designSite_ramped_nonneg hc'0 hd0 le_rfl)
    have hτx : langerTau x < lambdaComb c' * rampedNode d c' 1 := by
      have : langerTau x / lambdaComb c' < rampedNode d c' 1 := hσ1
      rw [div_lt_iff₀ hlam] at this; linarith
    have hxlt : x < designSite c' (rampedSigma d c') 1 :=
      (langerTau_strictMonoOn.lt_iff_lt (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 hχ0)).1 (by rw [hτχ]; exact hτx)
    have hre : b ≤ 0 := designComb_re_nonpos_of_lt hc'0 (by norm_num) (by norm_num) hgap
      (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') hx0.le hxlt
    have : b = -‖rampedComb P d c' (x : ℂ)‖ := by rw [hBnorm, abs_of_nonpos hre]; ring
    rw [htdef, hamp_def, this]; ring
  have hsigned := signed_amp_le hG0 hlo' hhi' ht hneg
  -- the integrand
  rw [combProfile_ofReal_eq hc'0 hx0.le]
  set Vv : ℝ := prob.cardyV (c' / 12) (c' * x ^ 2 / 3) with hVv
  set Bc : ℝ := Vv / Bessel.besselAs (c' * Bessel.besselL x) with hBc
  have hVv0 : 0 ≤ Vv := prob.cardyV_nonneg (by linarith [prob.totalShift_nonneg, (le_max_right _ _).trans hcS]) (by positivity)
  have hzA : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hBc0 : 0 ≤ Bc := div_nonneg hVv0 (Bessel.besselAs_pos hzA).le
  have hasy : |Bc - prob.nullPoly (Real.exp (-4 * π * x))| ≤ (K0 + 1) / c' := by
    have h := hKas hcS hx.1
    simp only [hw, Nat.sub_self, pow_zero, one_mul] at h
    have h2 : Bc = Vv / Bessel.besselAs (c' * (2 * π * x / 3)) := rfl
    rw [h2]
    refine h.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hc'0.le
  have hdens := Cardy.cardy_density Vv hc'0 hx0
  have hexp : Real.exp (c' * Bessel.besselL x) * Real.exp (-(c' * Bessel.besselL x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hsech : 0 < 1 / cosh (π * x / 2) ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hZ0 : 0 ≤ Bc * (√c' * √x / (√3 * π)) := by positivity
  -- Hf = sech² · t · Z₀
  have hHf : (2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * b * Vv) =
      1 / cosh (π * x / 2) ^ 2 * t * (Bc * (√c' * √x / (√3 * π))) := by
    rw [← hdens, htdef]
    linear_combination ((2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * b * Vv)) * (-hexp)
  rw [hHf]
  have h1 : 1 / cosh (π * x / 2) ^ 2 * t * (Bc * (√c' * √x / (√3 * π))) ≤
      (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) *
        (G * (w + (Real.exp δ - 1) * |w|)) := by
    have := mul_le_mul_of_nonneg_left hsigned (mul_nonneg hsech.le hZ0)
    calc 1 / cosh (π * x / 2) ^ 2 * t * (Bc * (√c' * √x / (√3 * π)))
        = (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * t := by ring
      _ ≤ _ := this
  have hid := density_identity_q (Bc := Bc) (qProb_pos prob) hc'0 hx0 hlam rfl
  set Θ : ℝ := mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / qProb prob with hΘ
  have hΘ0 : 0 ≤ Θ := by
    have hxp := hx0
    have hm : 0 ≤ mwt x := by
      unfold mwt
      have := mUnn_pos hxp
      have := mUnn_pos hxs
      have := deriv_langerTau_pos hxp
      positivity
    have hE : 0 < (1 - Real.exp (-(4 * π * x))) ^ 2 := by
      have := one_sub_exp_pos hx0; positivity
    have hq := qProb_pos prob
    rw [hΘ]; positivity
  have hE := hthc x hx Bc δ hBc0 hasy hδ0 le_rfl hδ12
  have h2 := theta_alg (w := w) hΘ0 hδ0 hE
  set K : ℝ := FKc (qProb prob) 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') with hK
  have hK0 : 0 ≤ K := by
    have hF := FKc_pos (qProb_pos prob) 1 hc'0
    have hCs : 0 < CStar := by unfold CStar; have := kappaAiry_pos; positivity
    have := kappaAiry_pos
    have := deriv_langerTau_pos hx0
    rw [hK]; positivity
  have h3 : (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) *
      (G * (w + (Real.exp δ - 1) * |w|)) = K * (Θ * (w + (Real.exp δ - 1) * |w|)) := by
    have : 1 / cosh (π * x / 2) ^ 2 * (Bc * √c' * √x / (√3 * π)) * G = K * Θ := by
      rw [hG, hK, hΘ]; exact hid
    calc (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (G * (w + (Real.exp δ - 1) * |w|))
        = (1 / cosh (π * x / 2) ^ 2 * (Bc * √c' * √x / (√3 * π)) * G) * (w + (Real.exp δ - 1) * |w|) := by
          ring
      _ = _ := by rw [this]; ring
  calc _ ≤ _ := h1
    _ = K * (Θ * (w + (Real.exp δ - 1) * |w|)) := h3
    _ ≤ K * (w + (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ))) * |w|) :=
        mul_le_mul_of_nonneg_left h2 hK0
    _ = _ := by rw [hK]; unfold sigmaOf; ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theta_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedWindow_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedWindow_pointwise

end FormalResearch.ModularBootstrap.Upper.Ramped

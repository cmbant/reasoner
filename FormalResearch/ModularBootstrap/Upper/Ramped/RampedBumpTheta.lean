module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumWindow

/-!
# The Cardy weight against the tip-normalised comb weight, every weight (`fw:Ustar`, vacuum step)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), vacuum step, with `upper_transfer.tex`, §5
(`q = 𝔮_{w,Q}(ξ_*) = (2ξ_*)^{w-1} Q(e^{-4πξ_*}) / (1 - e^{-4πξ_*})²`, `qProb`).

* `fW_lipschitz`: `x ↦ (2x)^{w-1} Q(e^{-4πx})` is Lipschitz on `[ξ_*/2, ξ_* + 1/2]` (`w = p + 1`);
* `theta_boundW` (`theta_bound` at every weight): for a Cardy ratio `B_c` within `K/c'` of `(2x)^{w-1} Q(e^{-4πx})`
  (`cardyV_asymptotic_real`), the weight `Θ = M_wt B_c / (E q)` satisfies
  `|Θ - 1| + Θ (e^δ - 1) ≤ c₁ λ |σ| + c₂ c'^{-2/3}` for `δ ≤ C_a c'^{-2/3}`.

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

/-- `x ↦ (2x)^{w-1} Q(e^{-4πx})` is Lipschitz on `[ξ_*/2, ξ_* + 1/2]`, around `ξ_*`. -/
lemma fW_lipschitz (prob : Crossing.FixedWeightProblem) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ langerX (1 / 2),
    |(2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x)) -
        (2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * xiStar))| ≤ L * |x - xiStar| := by
  have hxs := xiStar_pos
  have hpi := Real.pi_pos
  have hS := prob.totalShift_nonneg
  set p : ℕ := prob.w - 1 with hp
  set M : ℝ := 2 * (xiStar + 1 / 2) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨2 * p * M ^ (p - 1) + (2 * xiStar) ^ p * (4 * π * prob.totalShift), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [hx.1]
  obtain ⟨hQpos, hQb⟩ := WeightAxioms.nullPoly_exp_bounds prob (half_pos hxs)
  obtain ⟨hQ0', hQ1⟩ := hQb hx.1
  have hQ0 : 0 ≤ prob.nullPoly (Real.exp (-4 * π * x)) := hQpos.le.trans hQ0'
  have hLQ := nullPoly_exp_sub_le prob hx0 hxs
  have hpow : |(2 * x) ^ p - (2 * xiStar) ^ p| ≤ |2 * x - 2 * xiStar| * p * M ^ (p - 1) := by
    refine (abs_pow_sub_pow_le (2 * x) (2 * xiStar) p).trans ?_
    have hmax : max |2 * x| |2 * xiStar| ≤ M := by
      refine max_le ?_ ?_
      · rw [abs_of_pos (by linarith)]; rw [hM]; linarith [hx.2]
      · rw [abs_of_pos (by linarith)]; rw [hM]; linarith
    have := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax (p - 1)
    gcongr
  set Qx := prob.nullPoly (Real.exp (-4 * π * x))
  set Qs := prob.nullPoly (Real.exp (-4 * π * xiStar))
  have e : (2 * x) ^ p * Qx - (2 * xiStar) ^ p * Qs =
      ((2 * x) ^ p - (2 * xiStar) ^ p) * Qx + (2 * xiStar) ^ p * (Qx - Qs) := by ring
  rw [e]
  have h2 : |2 * x - 2 * xiStar| = 2 * |x - xiStar| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hP0 : 0 ≤ (2 * xiStar) ^ p := by positivity
  calc |((2 * x) ^ p - (2 * xiStar) ^ p) * Qx + (2 * xiStar) ^ p * (Qx - Qs)|
      ≤ |((2 * x) ^ p - (2 * xiStar) ^ p) * Qx| + |(2 * xiStar) ^ p * (Qx - Qs)| := abs_add_le _ _
    _ ≤ |(2 * x) ^ p - (2 * xiStar) ^ p| * 1 + (2 * xiStar) ^ p * (4 * π * prob.totalShift * |x - xiStar|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hQ0]
        gcongr
    _ ≤ _ := by
        rw [h2] at hpow
        nlinarith only [hpow, abs_nonneg (x - xiStar), hP0]

/-- The bound on `Θ / q`, `Θ = M_wt(x) · B_c/E(x)`, and `(Θ / q) (e^δ - 1)`, for a Cardy ratio `B_c` within
`K/c'` of `(2x)^{w-1} Q(e^{-4πx})`; `q = qProb prob = (2ξ_*)^{w-1} Q(e^{-4πξ_*})/E(ξ_*)` (every weight). -/
theorem theta_boundW (prob : Crossing.FixedWeightProblem) (K Ca : ℝ) (hK : 0 < K) (hCa : 0 < Ca) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ᶠ c' : ℝ in atTop, ∀ x ∈ langerX (1 / 2), ∀ Bc δ : ℝ, 0 ≤ Bc →
      |Bc - (2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x))| ≤ K / c' → 0 ≤ δ →
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
  have hQs : (2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * xiStar)) =
      qProb prob * (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
    unfold qProb
    exact (div_mul_cancel₀ _ hEsp.ne').symm
  set q : ℝ := qProb prob with hqdef
  set Es : ℝ := (1 - Real.exp (-(4 * π * xiStar))) ^ 2 with hEs
  set Qs : ℝ := (2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * xiStar)) with hQsdef
  obtain ⟨Lq, hLq0, hLip⟩ := fW_lipschitz prob
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
  have hQ1 : |((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x))) - Qs| ≤ Lq * |x - xiStar| :=
    hLip x hx
  have hE1 := abs_E_sub_le hx0
  rw [← hEx, ← hEs] at hE1
  have hnum : |Bc - Ex * q| ≤ K / c' + (Lq + 8 * π * q) * |x - xiStar| := by
    have e : Bc - Ex * q = (Bc - ((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x)))) +
        (((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x))) - Qs) + q * (Es - Ex) := by
      rw [hQs]; ring
    rw [e]
    have h3 : |q * (Es - Ex)| ≤ q * (8 * π * |x - xiStar|) := by
      rw [abs_mul, abs_of_pos hq, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hE1 hq.le
    calc _ ≤ |Bc - ((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x)))| +
          |((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x))) - Qs| + |q * (Es - Ex)| := abs_add_three _ _ _
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


/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.theta_boundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_boundW

end FormalResearch.ModularBootstrap.Upper.Ramped

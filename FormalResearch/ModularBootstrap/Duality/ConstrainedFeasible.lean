module

public import FormalResearch.ModularBootstrap.FixedWeight.CrossingMeasure
public import FormalResearch.ModularBootstrap.FixedWeight.MomentProblem

/-!
# A strictly feasible test for the constrained threshold `T_F < ∞` (`ds:E`(b))

`dual_spectrum.tex`, proof of Theorem E(b), finiteness: for every compact `F ⊂ (0, ∞)` (possibly
empty) there are `τ > 0` and `g ∈ Ā_w` with `g_vac > 0` and `g ≥ 0` on `F ∪ [τ, ∞)`.

Construction (the paper's `g_1 + λ Ξ_d`): choose `b` so small that `Ξ_b ≥ ½ e^{-2πbR} =: δ` on `F`
(`two_thermalDiff_ge`, `R = max F`); then `γ < b` so small that
`|g_vac(Ξ_γ)| ≥ (2 |g_vac(Ξ_b)| / δ) (1 + γ^{-w})`, which holds as `|g_vac(Ξ_γ)| ≥
q₀ γ^{-w} e^{2πa/γ} - e^{2πa}` (`q₀ = Q(e^{-2π})`); put `g_1 = Ξ_b - c Ξ_γ`
(`c = 2|v_b|/|v_γ|`, so `(g_1)_vac = |v_b|` and `g_1 ≥ δ/2` on `F`), and add `λ Ξ_d`, `d = γ/2`,
`λ` small, which keeps `g_vac > 0` and makes `g ≥ 0` beyond a large `τ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- For `0 < d < γ < b < 1`, `c, λ > 0`: `Ξ_b - c Ξ_γ + λ Ξ_d ≥ 0` for large `t` (the slowest
exponential `λ Ξ_d` wins). -/
lemma tail_nonneg (w : ℕ) {d γ b c lam : ℝ} (hd : 0 < d) (hdγ : d < γ) (hγb : γ < b) (hb1 : b < 1)
    (hc : 0 < c) (hlam : 0 < lam) :
    ∃ τ : ℝ, ∀ t ≥ τ, 0 ≤ (thermalDiff w b t - c * thermalDiff w γ t) + lam * thermalDiff w d t := by
  have hγ0 : 0 < γ := hd.trans hdγ
  have hb0 : 0 < b := hγ0.trans hγb
  have hd1 : d < 1 := hdγ.trans (hγb.trans hb1)
  refine ⟨max (t0 w b) (max (t0 w d) (Real.log (2 * c / lam) / (2 * π * (γ - d)))), fun t ht => ?_⟩
  have htb : t0 w b ≤ t := (le_max_left _ _).trans ht
  have htd : t0 w d ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have htL : Real.log (2 * c / lam) / (2 * π * (γ - d)) ≤ t :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  have h1 := two_thermalDiff_ge hb0 hb1 htb
  have h2 := two_thermalDiff_ge hd hd1 htd
  have hΞb : 0 ≤ thermalDiff w b t := by
    have := Real.exp_pos (-2 * π * b * t); linarith
  have hΞγ : thermalDiff w γ t ≤ Real.exp (-2 * π * γ * t) := by
    unfold thermalDiff
    have : 0 ≤ γ ^ (-(w : ℝ)) * Real.exp (-2 * π * t / γ) := by positivity
    linarith
  have hexp : c * Real.exp (-2 * π * γ * t) ≤ (lam / 2) * Real.exp (-2 * π * d * t) := by
    have hk : 0 < 2 * π * (γ - d) := by nlinarith [Real.pi_pos]
    have h3 : Real.log (2 * c / lam) ≤ 2 * π * (γ - d) * t := by
      have := (div_le_iff₀ hk).1 htL; linarith
    have h4 : 2 * c / lam ≤ Real.exp (2 * π * (γ - d) * t) := by
      have := Real.exp_le_exp.2 h3
      rwa [Real.exp_log (by positivity)] at this
    have e1 : Real.exp (-2 * π * γ * t) =
        Real.exp (-2 * π * d * t) * Real.exp (-(2 * π * (γ - d) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : Real.exp (-(2 * π * (γ - d) * t)) ≤ lam / (2 * c) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact h4
    rw [e1]
    calc c * (Real.exp (-2 * π * d * t) * Real.exp (-(2 * π * (γ - d) * t)))
        ≤ c * (Real.exp (-2 * π * d * t) * (lam / (2 * c))) := by gcongr
      _ = (lam / 2) * Real.exp (-2 * π * d * t) := by field_simp
  have h6 : (lam / 2) * Real.exp (-2 * π * d * t) ≤ lam * thermalDiff w d t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hΞγ hc.le]

/-- `|Ξ_γ(t)| ≤ 1 + γ^{-w}` for `t ≥ 0`. -/
lemma abs_thermalDiff_le_one_add {w : ℕ} {γ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t) :
    |thermalDiff w γ t| ≤ 1 + γ ^ (-(w : ℝ)) := by
  have h := abs_thermalDiff_le (w := w) hγ t
  have h1 : Real.exp (-2 * π * γ * t) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ γ * t := mul_nonneg hγ.le ht
    nlinarith [Real.pi_pos])
  have h2 : Real.exp (-2 * π * t / γ) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ t / γ := div_nonneg ht hγ.le
    have e : -2 * π * t / γ = -2 * π * (t / γ) := by ring
    rw [e]; nlinarith [Real.pi_pos])
  have hp : 0 ≤ γ ^ (-(w : ℝ)) := Real.rpow_nonneg hγ.le _
  have := mul_le_mul_of_nonneg_left h2 hp
  linarith

/-- Lower bound for `-g_vac(Ξ_γ)`: `q₀ γ^{-w} e^{2πa/γ} - e^{2πa}` with `q₀ = Q(e^{-2π})`. -/
lemma neg_gVac_thermalDiff_ge (prob : FixedWeightProblem) {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    prob.nullPoly (Real.exp (-2 * π)) * (γ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / γ)) -
        Real.exp (2 * π * a) ≤ -prob.gVac a (thermalDiff prob.w γ) := by
  rw [prob.gVac_thermalDiff a hγ]
  have hq1 : Real.exp (-2 * π * γ) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  have hA : prob.nullPoly (Real.exp (-2 * π * γ)) ≤ 1 :=
    prob.nullPoly_le_one (Real.exp_pos _).le hq1.le
  have hApos : 0 ≤ prob.nullPoly (Real.exp (-2 * π * γ)) := (prob.nullPoly_pos (Real.exp_pos _).le hq1).le
  have hexp : Real.exp (2 * π * a * γ) ≤ Real.exp (2 * π * a) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * π * a) (sub_nonneg.2 hγ1)])
  have hAA : Real.exp (2 * π * a * γ) * prob.nullPoly (Real.exp (-2 * π * γ)) ≤ Real.exp (2 * π * a) := by
    calc _ ≤ Real.exp (2 * π * a) * 1 := mul_le_mul hexp hA hApos (Real.exp_pos _).le
      _ = _ := mul_one _
  have hq2 : Real.exp (-2 * π / γ) ≤ Real.exp (-2 * π) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hγ]; nlinarith [Real.pi_pos]
  have hq3 : Real.exp (-2 * π) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hQ : prob.nullPoly (Real.exp (-2 * π)) ≤ prob.nullPoly (Real.exp (-2 * π / γ)) :=
    nullPoly_antitone_on_Icc prob (Real.exp_pos _).le hq2 hq3
  have hpos : 0 ≤ γ ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / γ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hQ hpos]

/-- **Finiteness `T_F < ∞`** (`ds:E`(b)): for every compact `F ⊂ (0, ∞)` (possibly empty) and every
`(w, Q)` with `c̃ > 0`, `c̃ ≥ 12 S`, there are `τ > 0` and `g ∈ Ā_w` with `g_vac > 0` and `g ≥ 0` on
`F ∪ [τ, ∞)`. -/
theorem exists_feasible_of_compact (prob : FixedWeightProblem) {cTilde : ℝ} (hc_pos : 0 < cTilde)
    (hc : 12 * prob.totalShift ≤ cTilde) {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ g, prob.IsFeasibleOn (cTilde / 12) (F ∪ Ici τ) g := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top prob hc_pos hc
    exact ⟨T, hT, g, by rw [empty_union, isFeasibleOn_Ici_iff]; exact hg⟩
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha0 : 0 < cTilde / 12 := by linarith
  set a := cTilde / 12 with ha_def
  obtain ⟨m, hmF, hmin⟩ := hFc.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨R, hRF, hmax⟩ := hFc.exists_isMaxOn hne continuous_id.continuousOn
  have hm : 0 < m := hF hmF
  have hmt : ∀ t ∈ F, m ≤ t := fun t ht => isMinOn_iff.1 hmin t ht
  have htR : ∀ t ∈ F, t ≤ R := fun t ht => isMaxOn_iff.1 hmax t ht
  obtain ⟨b, hb0, hb2, hbm⟩ := exists_beta0 prob.w hm
  have hb1 : b < 1 := by linarith
  have ht0b : t0 prob.w b ≤ m := (t0_le_t0Star hb0 le_rfl hb1).trans hbm
  -- the lower bound `δ` for `Ξ_b` on `F`
  set δ : ℝ := (1 / 2) * Real.exp (-2 * π * b * R) with hδdef
  have hδ : 0 < δ := by positivity
  have hΞb : ∀ t ∈ F, δ ≤ thermalDiff prob.w b t := by
    intro t ht
    have h1 := two_thermalDiff_ge hb0 hb1 ((ht0b).trans (hmt t ht))
    have h2 : Real.exp (-2 * π * b * R) ≤ Real.exp (-2 * π * b * t) :=
      Real.exp_le_exp.2 (by nlinarith only [mul_nonneg (mul_nonneg Real.pi_pos.le hb0.le) (sub_nonneg.2 (htR t ht))])
    rw [hδdef]; linarith
  set vb := prob.gVac a (thermalDiff prob.w b) with hvbdef
  have hvb : vb < 0 := gVac_thermalDiff_neg prob ha0 hb0 hb1
  set K : ℝ := 2 * (-vb) / δ with hKdef
  have hvb' : 0 < -vb := neg_pos.2 hvb
  have hK : 0 < K := div_pos (by linarith) hδ
  set q₀ := prob.nullPoly (Real.exp (-2 * π)) with hq₀def
  have hq₀ : 0 < q₀ := prob.nullPoly_pos (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos]))
  -- choose `γ`
  have hev1 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioo (0 : ℝ) b := Ioo_mem_nhdsGT hb0
  have hev2 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), (2 * K + Real.exp (2 * π * a)) / q₀ ≤
      Real.exp (2 * π * a * γ⁻¹) := by
    have h1 : Tendsto (fun γ : ℝ => 2 * π * a * γ⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
    exact (Real.tendsto_exp_atTop.comp h1).eventually_ge_atTop _
  obtain ⟨γ, ⟨hγ0, hγb⟩, hγ2⟩ := (hev1.and hev2).exists
  have hγ1 : γ < 1 := hγb.trans hb1
  set vγ := prob.gVac a (thermalDiff prob.w γ) with hvγdef
  have hvγ : vγ < 0 := gVac_thermalDiff_neg prob ha0 hγ0 hγ1
  set P : ℝ := γ ^ (-(prob.w : ℝ)) with hPdef
  have hP : 1 ≤ P := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hγ0 hγ1.le
    (by simp)
  have hvγK : K * (1 + P) ≤ -vγ := by
    have hlow := neg_gVac_thermalDiff_ge prob ha0 hγ0 hγ1.le
    rw [div_eq_mul_inv] at hlow
    have hX : 2 * K + Real.exp (2 * π * a) ≤ q₀ * Real.exp (2 * π * a * γ⁻¹) := by
      rw [div_le_iff₀ hq₀] at hγ2
      linarith [mul_comm q₀ (Real.exp (2 * π * a * γ⁻¹))]
    have hX' : 0 ≤ q₀ * Real.exp (2 * π * a * γ⁻¹) - K := by
      have := Real.exp_pos (2 * π * a); linarith
    have h3 : q₀ * Real.exp (2 * π * a * γ⁻¹) - K ≤
        P * (q₀ * Real.exp (2 * π * a * γ⁻¹) - K) := le_mul_of_one_le_left hX' hP
    simp only [← hPdef] at hlow
    linarith only [hlow, h3, hX]
  set c : ℝ := 2 * (-vb) / (-vγ) with hcdef
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hcvγ : c * (-vγ) = 2 * (-vb) := by rw [hcdef, div_mul_cancel₀ _ (neg_pos.2 hvγ).ne']
  have hcP : c * (1 + P) ≤ δ := by
    rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ (neg_pos.2 hvγ)]
    have hKδ : K * δ = 2 * (-vb) := by rw [hKdef, div_mul_cancel₀ _ hδ.ne']
    rw [← hKδ]
    linarith only [mul_le_mul_of_nonneg_left hvγK hδ.le]
  -- the small level `d` and the coefficient `λ`
  set d : ℝ := γ / 2 with hddef
  have hd0 : 0 < d := by positivity
  have hdγ : d < γ := by linarith
  set vd := prob.gVac a (thermalDiff prob.w d) with hvddef
  have hvd : vd < 0 := gVac_thermalDiff_neg prob ha0 hd0 (hdγ.trans hγ1)
  set lam : ℝ := (-vb) / (2 * (-vd)) with hlamdef
  have hlam : 0 < lam := div_pos hvb' (by linarith)
  have hvdne : vd ≠ 0 := hvd.ne
  have hlamvd : lam * vd = -((-vb) / 2) := by rw [hlamdef]; field_simp
  obtain ⟨τ₁, hτ₁⟩ := tail_nonneg prob.w hd0 hdγ hγb hb1 hc hlam
  set g : ℝ → ℝ := fun t => (thermalDiff prob.w b t + (-c) * thermalDiff prob.w γ t) +
    lam * thermalDiff prob.w d t with hgdef
  have hTb := thermalDiff_mem_TestClass prob ha hb0
  have hTγ := thermalDiff_mem_TestClass prob ha hγ0
  have hTd := thermalDiff_mem_TestClass prob ha hd0
  have hg : TestClass prob a g := (hTb.add (hTγ.smul (-c))).add (hTd.smul lam)
  have hgvac : prob.gVac a g = (-vb) / 2 := by
    have h1 := prob.gVac_add hTb (hTγ.smul (-c))
    have h2 := prob.gVac_add (hTb.add (hTγ.smul (-c))) (hTd.smul lam)
    rw [prob.gVac_smul (-c) hTγ] at h1
    rw [h1, prob.gVac_smul lam hTd] at h2
    show prob.gVac a (fun t => (thermalDiff prob.w b t + (-c) * thermalDiff prob.w γ t) +
      lam * thermalDiff prob.w d t) = _
    rw [h2]
    have : -c * vγ = 2 * (-vb) := by linarith only [hcvγ]
    rw [this]; linarith only [hlamvd]
  have hd_le : t0 prob.w d ≤ m := by
    have := t0_mono prob.w hd0 (hdγ.le.trans hγb.le) hb1
    exact this.trans ht0b
  refine ⟨max τ₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _), g, hg, ?_, ?_⟩
  · rw [hgvac]; linarith
  · rintro t (ht | ht)
    · -- on `F`
      have htm := hmt t ht
      have htpos : 0 < t := hm.trans_le htm
      have h1 := hΞb t ht
      have h2 := abs_thermalDiff_le_one_add (w := prob.w) hγ0 htpos.le
      have h3 : 0 ≤ thermalDiff prob.w d t := by
        have := two_thermalDiff_ge hd0 (hdγ.trans hγ1) (hd_le.trans htm)
        have := Real.exp_pos (-2 * π * d * t); linarith
      have h4 : c * thermalDiff prob.w γ t ≤ c * (1 + P) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hc.le
      show 0 ≤ (thermalDiff prob.w b t + (-c) * thermalDiff prob.w γ t) + lam * thermalDiff prob.w d t
      linarith only [h1, h4, hcP, mul_nonneg hlam.le h3]
    · have := hτ₁ t ((le_max_left τ₁ 1).trans ht)
      show 0 ≤ (thermalDiff prob.w b t + (-c) * thermalDiff prob.w γ t) + lam * thermalDiff prob.w d t
      linarith

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_feasible_of_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_feasible_of_compact

end FormalResearch.ModularBootstrap.FixedWeight

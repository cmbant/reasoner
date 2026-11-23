module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauBounds
public import FormalResearch.ModularBootstrap.Upper.Comb.Tip

/-!
# `(F1)`: the site map `a ↦ χ_a` in the tip regime and at large `y`

`remainder.tex`, Proposition 1.2(2), input `(F1)`, quantile side.  With `λ = lambdaComb c'` and
`r_a = χ_a - ξ_*` (`siteRadius`):

* `siteGap_two_sided`: for `c'` large and `k ≥ 1` with `r_k ≤ 0.63`,
  `c λ k^{-1/3} ≤ ℓ_k ≤ C λ k^{-1/3}` (`ℓ_k = siteGap c' k`);
* `chiDeriv_sq_logDeriv_le`: for `a ≥ 1` with `r_a ≤ 0.63`,
  `χ_a'^2 (1 + (log ρ_U)'(χ_a)) ≤ C λ a^{-4/3}`;
* `chiDeriv_large_le`, `logDeriv_rhoU_large_le`: for `χ_a ≥ ξ_* + r₁`,
  `χ_a' ≤ C/(c'(1+χ_a))` and `(log ρ_U)'(χ_a) ≤ C/(1+χ_a)`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

lemma chiQuantile_mono_le {c' : ℝ} (hc' : 0 < c') {a b : ℝ} (ha : 1 / 4 ≤ a) (hab : a ≤ b) :
    chiQuantile c' a ≤ chiQuantile c' b :=
  (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab

/-- `ℓ_k ≍ λ k^{-1/3}` while the cell lies in the tip window `χ_k - ξ_* ≤ 0.63`. -/
theorem siteGap_two_sided :
    ∃ c C c0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < c0 ∧ ∀ c' : ℝ, c0 ≤ c' → ∀ k : ℕ, 1 ≤ k →
      siteRadius c' k ≤ 63 / 100 →
      c * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ siteGap c' k ∧
        siteGap c' k ≤ C * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨_, _, _, _, _, hev⟩ : ∃ C : ℝ, 0 < C ∧ True ∧ True ∧ True ∧ ∀ᶠ c' in atTop,
      (∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ siteGap c' 1) ∧ siteGap c' 1 ≤ 1 / 2 := by
    obtain ⟨C, hC, h⟩ := siteGap_eventually_le
    exact ⟨C, hC, trivial, trivial, trivial, h.mono fun c' h => ⟨h.1, h.2.2.2⟩⟩
  obtain ⟨c₁, C₁, c₂, C₂, C₃, hc₁, hC₁, hc₂, hC₂, hC₃, hq⟩ :=
    quantile_tip_bounds (r₀ := 113 / 100) (by norm_num)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨c₂ * (2 : ℝ) ^ (-(1 / 3 : ℝ)), C₂ * (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)), max N0 1,
    by positivity, by positivity, by positivity, fun c' hc'0 k hk hrk => ?_⟩
  have hc' : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hc'0)
  obtain ⟨hmono, hgap1⟩ := hN0 c' ((le_max_left _ _).trans hc'0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgapk : siteGap c' k ≤ 1 / 2 := (hmono k hk).trans hgap1
  have hrk1 : siteRadius c' ((k : ℝ) + 1) ≤ 113 / 100 := by
    have : siteRadius c' ((k : ℝ) + 1) = siteRadius c' k + siteGap c' k := by
      unfold siteRadius siteGap; ring
    rw [this]; linarith
  have hcont : ContinuousOn (chiQuantile c') (Icc (k : ℝ) (k + 1)) :=
    (continuousOn_chiQuantile hc').mono fun x hx => by
      show 1 / 4 ≤ x; linarith [hx.1]
  have hder : ∀ x ∈ Ioo (k : ℝ) (k + 1), HasDerivAt (chiQuantile c') (chiDeriv c' x) x :=
    fun x hx => (hasDerivAt_chiQuantile hc' (by linarith [hx.1])).1
  obtain ⟨a, ha, hslope⟩ := exists_hasDerivAt_eq_slope (chiQuantile c') (chiDeriv c')
    (by linarith : (k : ℝ) < k + 1) hcont hder
  have hgap : siteGap c' k = chiDeriv c' a := by
    rw [hslope]; unfold siteGap; field_simp; ring
  have ha4 : 1 / 4 < a := by linarith [ha.1]
  have hra : siteRadius c' a ≤ 113 / 100 := by
    refine le_trans ?_ hrk1
    unfold siteRadius
    have := chiQuantile_mono_le hc' ha4.le ha.2.le
    linarith
  obtain ⟨_, ⟨hlo, hhi⟩, _⟩ := hq hc' ha4 hra
  have hlam : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hkpos : 0 < (k : ℝ) := by linarith
  -- (a - 1/4)^{-1/3} between (2k)^{-1/3} and (3k/4)^{-1/3}
  have hlow : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ (a - 1 / 4) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) (by linarith [ha.2]) (by norm_num)
  have hup : (a - 1 / 4) ^ (-(1 / 3 : ℝ)) ≤ (3 / 4 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ha.1]) (by norm_num)
  rw [Real.mul_rpow (by norm_num) hkpos.le] at hlow
  rw [Real.mul_rpow (by norm_num) hkpos.le] at hup
  rw [hgap]
  constructor
  · calc c₂ * 2 ^ (-(1 / 3 : ℝ)) * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ))
        = c₂ * lambdaComb c' * (2 ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ c₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ chiDeriv c' a := hlo
  · calc chiDeriv c' a ≤ C₂ * lambdaComb c' * (a - 1 / 4) ^ (-(1 / 3 : ℝ)) := hhi
      _ ≤ C₂ * lambdaComb c' * ((3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = C₂ * (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring

/-- `χ_a'^2 (1 + (log ρ_U)'(χ_a)) ≤ C λ a^{-4/3}` for `a ≥ 1` while `χ_a - ξ_* ≤ 0.63`. -/
theorem chiDeriv_sq_logDeriv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 0 < c' → ∀ a : ℝ, 1 ≤ a → siteRadius c' a ≤ 63 / 100 →
      chiDeriv c' a ^ 2 * (1 + rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) ≤
        C * lambdaComb c' * a ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨c₁, C₁, c₂, C₂, C₃, hc₁, hC₁, hc₂, hC₂, hC₃, hq⟩ :=
    quantile_tip_bounds (r₀ := 63 / 100) (by norm_num)
  have hb : 0 < π / (4 * √2) := by positivity
  set M : ℝ := 63 / 100 + 1 / 2 + π / (4 * √2) * (63 / 100) with hM
  have hMp : 0 < M := by positivity
  refine ⟨C₂ ^ 2 * M / c₁ * ((3 / 4 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 4, by positivity, fun c' hc' a ha hra => ?_⟩
  have ha4 : 1 / 4 < a := by linarith
  have ha14 : 0 < a - 1 / 4 := by linarith
  have hr : 0 < siteRadius c' a := sub_pos.mpr (xiStar_lt_chiQuantile hc' ha4)
  obtain ⟨⟨hrlo, _⟩, ⟨_, hchi⟩, _⟩ := hq hc' ha4 hra
  have hlam : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hχ : chiQuantile c' a = xiStar + siteRadius c' a := by unfold siteRadius; ring
  set Ψ : ℝ := (a - 1 / 4) ^ (-(1 / 3 : ℝ)) with hΨ
  set Φ : ℝ := phiQuantile a with hΦ
  have hΨp : 0 < Ψ := Real.rpow_pos_of_pos ha14 _
  have hΦp : 0 < Φ := by rw [hΦ]; unfold phiQuantile; exact Real.rpow_pos_of_pos ha14 _
  have hΨΦ : Ψ ^ 2 * Φ = 1 := by
    rw [hΨ, hΦ]; unfold phiQuantile
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha14.le, ← Real.rpow_add ha14]
    norm_num
  have hL := (logDeriv_rhoU_tip_bounds hr).2
  have hLpos : 0 < rhoUDeriv (xiStar + siteRadius c' a) / rhoU (xiStar + siteRadius c' a) :=
    (one_div_pos.2 (by positivity : 0 < 2 * siteRadius c' a)).trans_le
      (logDeriv_rhoU_tip_bounds hr).1
  rw [hχ]
  set L := rhoUDeriv (xiStar + siteRadius c' a) / rhoU (xiStar + siteRadius c' a) with hLdef
  set r := siteRadius c' a with hrdef
  have h1L : 1 + L ≤ M / r := by
    rw [le_div_iff₀ hr]
    have h2 : L * r ≤ (1 / (2 * r) + π / (4 * √2)) * r := mul_le_mul_of_nonneg_right hL hr.le
    have h3 : (1 / (2 * r) + π / (4 * √2)) * r = 1 / 2 + π / (4 * √2) * r := by field_simp
    have h4 : π / (4 * √2) * r ≤ π / (4 * √2) * (63 / 100) :=
      mul_le_mul_of_nonneg_left hra hb.le
    rw [hM]; nlinarith
  have hrΦ : c₁ * lambdaComb c' * Φ ≤ r := hrlo
  have hχ' : chiDeriv c' a ≤ C₂ * lambdaComb c' * Ψ := hchi
  have hχ0 : 0 ≤ chiDeriv c' a := by
    unfold chiDeriv; have := rhoU_nonneg (chiQuantile c' a); positivity
  have hstep : chiDeriv c' a ^ 2 * (1 + L) ≤ (C₂ * lambdaComb c' * Ψ) ^ 2 * (M / (c₁ * lambdaComb c' * Φ)) := by
    apply mul_le_mul (pow_le_pow_left₀ hχ0 hχ' 2) _ (by linarith) (by positivity)
    exact h1L.trans (div_le_div_of_nonneg_left hMp.le (by positivity) hrΦ)
  have hcalc : (C₂ * lambdaComb c' * Ψ) ^ 2 * (M / (c₁ * lambdaComb c' * Φ)) =
      C₂ ^ 2 * M / c₁ * lambdaComb c' * Ψ ^ 4 := by
    have : Φ = 1 / Ψ ^ 2 := by field_simp; linarith
    rw [this]; field_simp
  -- Ψ^4 ≤ ((3/4)^{-1/3})^4 * a^{-4/3}
  have hΨle : Ψ ≤ (3 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) * a ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have ha43 : a ^ (-(4 / 3 : ℝ)) = (a ^ (-(1 / 3 : ℝ))) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hΨ4 : Ψ ^ 4 ≤ ((3 / 4 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 4 * a ^ (-(4 / 3 : ℝ)) := by
    rw [ha43, ← mul_pow]; exact pow_le_pow_left₀ hΨp.le hΨle 4
  calc chiDeriv c' a ^ 2 * (1 + L) ≤ _ := hstep
    _ = C₂ ^ 2 * M / c₁ * lambdaComb c' * Ψ ^ 4 := hcalc
    _ ≤ C₂ ^ 2 * M / c₁ * lambdaComb c' * (((3 / 4 : ℝ) ^ (-(1 / 3 : ℝ))) ^ 4 * a ^ (-(4 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hΨ4 (by positivity)
    _ = _ := by ring

/-! ### Large `y` -/

lemma rhoU_ge_large {r1 y : ℝ} (hr1 : 0 < r1) (hy : xiStar + r1 ≤ y) :
    4 / 3 * (1 + y) / ((1 + xiStar) / r1 + 1) ≤ rhoU y := by
  have hxs := xiStar_pos
  set A0 : ℝ := (1 + xiStar) / r1 + 1 with hA0
  have hA0p : 0 < A0 := by positivity
  set r := y - xiStar with hr
  have hrr : r1 ≤ r := by rw [hr]; linarith
  have hu1 : 1 + y ≤ A0 * r := by
    have : (1 + xiStar) ≤ (1 + xiStar) / r1 * r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr1]; nlinarith
    rw [hA0]; nlinarith
  have hy' : xiStar + r = y := by rw [hr]; ring
  have h := (rhoU_ge_max (r := r) (by linarith)).trans_eq' rfl
  have h2 : 4 / 3 * r ≤ rhoU y := by
    have := (le_max_right _ _).trans (rhoU_ge_max (r := r) (by linarith))
    rwa [hy'] at this
  rw [div_le_iff₀ hA0p]
  nlinarith

/-- `χ_a' ≤ C/(c'(1+χ_a))` for `χ_a ≥ ξ_* + r₁`. -/
theorem chiDeriv_large_le {r1 : ℝ} (hr1 : 0 < r1) :
    ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 0 < c' → ∀ a : ℝ, xiStar + r1 ≤ chiQuantile c' a →
      chiDeriv c' a ≤ C / (c' * (1 + chiQuantile c' a)) := by
  have hxs := xiStar_pos
  set A0 : ℝ := (1 + xiStar) / r1 + 1 with hA0
  have hA0p : 0 < A0 := by positivity
  refine ⟨3 * A0 / 2, by positivity, fun c' hc' a ha => ?_⟩
  have hy : 0 < 1 + chiQuantile c' a := by linarith
  have h := rhoU_ge_large hr1 ha
  rw [← hA0] at h
  unfold chiDeriv
  have hρ : 0 < rhoU (chiQuantile c' a) := lt_of_lt_of_le (by positivity) h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 4 / 3 * (1 + chiQuantile c' a) ≤ rhoU (chiQuantile c' a) * A0 := by
    rwa [div_le_iff₀ hA0p] at h
  nlinarith [mul_le_mul_of_nonneg_left this hc'.le]

/-- `(log ρ_U)'(χ_a) ≤ C/(1+χ_a)` for `χ_a ≥ ξ_* + r₁`. -/
theorem logDeriv_rhoU_large_le {r1 : ℝ} (hr1 : 0 < r1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, xiStar + r1 ≤ y → rhoUDeriv y / rhoU y ≤ C / (1 + y) := by
  have hxs := xiStar_pos
  set A0 : ℝ := (1 + xiStar) / r1 + 1 with hA0
  have hA0p : 0 < A0 := by positivity
  set P1 : ℝ := rhoUDeriv (xiStar + r1) with hP1
  have hP1p : 0 ≤ P1 := by
    have := rhoUDeriv_ge (y := xiStar + r1) (by linarith); linarith
  refine ⟨3 * A0 * P1 / 4 + 1, by positivity, fun y hy => ?_⟩
  have hyx : xiStar < y := by linarith
  have hu : 0 < 1 + y := by linarith
  have h := rhoU_ge_large hr1 hy
  rw [← hA0] at h
  have hρ : 0 < rhoU y := lt_of_lt_of_le (by positivity) h
  have hp : rhoUDeriv y ≤ P1 := by
    rcases (show xiStar + r1 ≤ y from hy).eq_or_lt with h | h
    · rw [← h]
    · exact (rhoUDeriv_strictAntiOn (by show xiStar < xiStar + r1; linarith)
        (by show xiStar < y; exact hyx) h).le
  have hp0 : 0 ≤ rhoUDeriv y := by have := rhoUDeriv_ge hyx; linarith
  rw [div_le_div_iff₀ hρ hu]
  have : 4 / 3 * (1 + y) ≤ rhoU y * A0 := by rwa [div_le_iff₀ hA0p] at h
  nlinarith [mul_le_mul hp this (by positivity) hP1p]

end FormalResearch.ModularBootstrap.Upper.Ramped

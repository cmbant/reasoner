module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RpAmplitude

/-!
# Parameter selection for the bump: `r_p`, `X_p`, `M_amp`, `η_big(p)`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, §`fw:s1`: `fw:e2.2`, `fw:e2.3` and the
"Non-circular parameter selection" (steps 1 and 2).  All constants depend on `p` only.

* `exists_rp`: for every `r₀ > 0` there is `r ∈ (0, min(r₀, 1/4)]` with `ρ_∞ R_p ≤ 0.10` on `(ξ_*, ξ_* + 4r]`
  (`fw:e2.2`).
* `exists_Xp`: for every `r` and `X₀` there is `X > max(X₀, ξ_* + 4r + 2)` with `ρ_∞ R_p ≤ 0.60` for `x ≥ X - 1`
  (`fw:e2.3`).
* `mAmp p r X`: `M_amp = sup ρ_∞ R_p` over `[ξ_* + 3r, X - 1]`; `rhoRp_le_mAmp`, `mAmp_nonneg`, `mAmp_le_explicit`.
* `bumpFloor H = 0.700 · (16/5)(H² + 1/4)` and `etaBig`: `bumpFloor_gt_two_mul_add_one` gives
  `0.700 (16/5)(η_big² + 1/4) > 2 M_amp + 1`; `bumpFloor_quarter_not_gt` shows that the unboosted height `1/4`
  never closes the margin.
* `RpParams p`, `exists_rpParams`, `rpParams`: the packaged selection.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes

/-- `fw:e2.2`. -/
theorem exists_rp (p : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ r ≤ 1 / 4 ∧
      ∀ x : ℝ, xiStar < x → x ≤ xiStar + 4 * r → rhoRp p x ≤ 1 / 10 := by
  obtain ⟨C, hC, h⟩ := rhoRp_near_tip p
  have hcont : ContinuousAt (fun t : ℝ => C * t ^ (5 / 4 : ℝ)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (5 / 4) (Or.inr (by norm_num)))
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), C * t ^ (5 / 4 : ℝ) < 1 / 10 := by
    have h0 : C * (0 : ℝ) ^ (5 / 4 : ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num), mul_zero]
    exact hcont.eventually (gt_mem_nhds (by show C * (0 : ℝ) ^ (5 / 4 : ℝ) < 1 / 10; rw [h0]; norm_num))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (min r₀ (1 / 4)) (δ / 8), lt_min (lt_min hr₀ (by norm_num)) (by positivity),
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  intro x hx hx4
  have hr1 : min (min r₀ (1 / 4)) (δ / 8) ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hr2 : min (min r₀ (1 / 4)) (δ / 8) ≤ δ / 8 := min_le_right _ _
  have ht : dist (x - xiStar) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  exact (h x hx (by linarith)).trans (hδ' ht).le

/-- `fw:e2.3`. -/
theorem exists_Xp (p : ℕ) (X₀ : ℝ) {r : ℝ} (_hr : 0 < r) :
    ∃ X : ℝ, X₀ < X ∧ xiStar + 4 * r + 2 < X ∧ ∀ x : ℝ, X - 1 ≤ x → rhoRp p x ≤ 6 / 10 := by
  have hev : ∀ᶠ x in atTop, rhoRp p x < 6 / 10 :=
    (tendsto_order.1 (tendsto_rhoRp_atTop p)).2 _ (by norm_num)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hev
  refine ⟨max (max A X₀) (xiStar + 4 * r + 2) + 1, ?_, ?_, fun x hx => (hA x ?_).le⟩
  · linarith [le_max_right A X₀, le_max_left (max A X₀) (xiStar + 4 * r + 2)]
  · linarith [le_max_right (max A X₀) (xiStar + 4 * r + 2)]
  · linarith [le_max_left A X₀, le_max_left (max A X₀) (xiStar + 4 * r + 2)]

/-- `M_amp = sup_{[ξ_* + 3r, X - 1]} ρ_∞ R_p`. -/
noncomputable def mAmp (p : ℕ) (r X : ℝ) : ℝ :=
  sSup (rhoRp p '' Set.Icc (xiStar + 3 * r) (X - 1))

lemma bddAbove_rhoRp_image (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) :
    BddAbove (rhoRp p '' Set.Icc (xiStar + 3 * r) (X - 1)) :=
  ⟨542 / 1000 * rAmpConst ^ p, by
    rintro _ ⟨x, hx, rfl⟩
    exact rhoRp_le_explicit p (by linarith [hx.1])⟩

theorem rhoRp_le_mAmp (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (xiStar + 3 * r) (X - 1)) : rhoRp p x ≤ mAmp p r X :=
  le_csSup (bddAbove_rhoRp_image p hr X) ⟨x, hx, rfl⟩

theorem mAmp_nonneg (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) : 0 ≤ mAmp p r X := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, hx, rfl⟩
  exact rhoRp_nonneg p (by linarith [hx.1])

theorem mAmp_le_explicit (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) :
    mAmp p r X ≤ 542 / 1000 * rAmpConst ^ p := by
  unfold mAmp
  rcases (Set.Icc (xiStar + 3 * r) (X - 1)).eq_empty_or_nonempty with he | hne
  · rw [he, Set.image_empty, Real.sSup_empty]
    have := rAmpConst_pos
    positivity
  · apply csSup_le (hne.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact rhoRp_le_explicit p (by linarith [hx.1])

/-- The floor of the bumped comb, `0.700 · (16/5)(H² + 1/4)`. -/
noncomputable def bumpFloor (H : ℝ) : ℝ := 7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))

/-- The bump height `η_big = M_amp + 1`. -/
noncomputable def etaBig (p : ℕ) (r X : ℝ) : ℝ := mAmp p r X + 1

theorem bumpFloor_quarter : bumpFloor (1 / 4) = 7 / 10 := by
  unfold bumpFloor; norm_num

theorem bumpFloor_gt_two_mul_add_one {M H : ℝ} (hM : 0 ≤ M) (hH : M + 1 ≤ H) :
    2 * M + 1 < bumpFloor H := by
  unfold bumpFloor
  nlinarith

/-- `0.700 (16/5)(η_big² + 1/4) > 2 M_amp + 1`. -/
theorem etaBig_floor_gt (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) :
    2 * mAmp p r X + 1 < bumpFloor (etaBig p r X) :=
  bumpFloor_gt_two_mul_add_one (mAmp_nonneg p hr X) le_rfl

theorem one_quarter_le_etaBig (p : ℕ) {r : ℝ} (hr : 0 < r) (X : ℝ) : 1 / 4 ≤ etaBig p r X := by
  have := mAmp_nonneg p hr X
  unfold etaBig; linarith

/-- Negative regression: the unboosted height `1/4` (gain 1) never closes the margin `2 M + 1` since
`bumpFloor (1/4) = 0.700 < 1 ≤ 2M + 1`. -/
theorem bumpFloor_quarter_not_gt {M : ℝ} (hM : 0 ≤ M) : ¬ 2 * M + 1 < bumpFloor (1 / 4) := by
  rw [bumpFloor_quarter]; intro h; linarith

/-- The parameters of the selection, depending on `p` only (`fw:e2.2`, `fw:e2.3`, parameter selection). -/
structure RpParams (p : ℕ) where
  r : ℝ
  X : ℝ
  r_pos : 0 < r
  r_le : r ≤ 1 / 4
  X_gt : xiStar + 4 * r + 2 < X
  near : ∀ x : ℝ, xiStar < x → x ≤ xiStar + 4 * r → rhoRp p x ≤ 1 / 10
  far : ∀ x : ℝ, X - 1 ≤ x → rhoRp p x ≤ 6 / 10

namespace RpParams

variable {p : ℕ} (P : RpParams p)

/-- `M_amp`. -/
noncomputable def M : ℝ := mAmp p P.r P.X

/-- `η_big(p)`. -/
noncomputable def eta : ℝ := etaBig p P.r P.X

theorem macro_le {x : ℝ} (hx : x ∈ Set.Icc (xiStar + 3 * P.r) (P.X - 1)) : rhoRp p x ≤ P.M :=
  rhoRp_le_mAmp p P.r_pos P.X hx

theorem M_nonneg : 0 ≤ P.M := mAmp_nonneg p P.r_pos P.X

theorem eta_ge : 1 / 4 ≤ P.eta := one_quarter_le_etaBig p P.r_pos P.X

theorem floor_gt : 2 * P.M + 1 < bumpFloor P.eta := etaBig_floor_gt p P.r_pos P.X

end RpParams

theorem exists_rpParams (p : ℕ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ P : RpParams p, P.r ≤ r₀ := by
  obtain ⟨r, hr, hr0, hr1, hnear⟩ := exists_rp p hr₀
  obtain ⟨X, -, hX, hfar⟩ := exists_Xp p 0 hr
  exact ⟨⟨r, X, hr, hr1, hX, hnear, hfar⟩, hr0⟩

/-- The chosen parameters for `p`. -/
noncomputable def rpParams (p : ℕ) : RpParams p := (exists_rpParams p one_pos).choose

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.exists_rpParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_rpParams

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.etaBig_floor_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms etaBig_floor_gt

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.RpParams.macro_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RpParams.macro_le

end FormalResearch.ModularBootstrap.Upper.Positivity

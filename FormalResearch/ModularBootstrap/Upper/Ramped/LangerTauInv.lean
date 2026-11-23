module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauSpec

/-!
# The inverse Langer coordinate and the site identification

`remainder.tex`, Proposition 1.2(2), inputs `(F1)`: `τ^{-1}` on `[0, ∞)` and the identification
`χ_a = τ^{-1}(λ Φ_a)`.

* `langerTauInv s = χ^{(1)}_{1/4 + k_tip s^{3/2}}` (the quantile of the unit comb `c' = 1`): the unique
  `x ≥ ξ_*` with `N(x) = k_tip s^{3/2}`.
* `langerTau_langerTauInv`, `langerTauInv_langerTau`: `τ` and `τ^{-1}` are mutually inverse between
  `[ξ_*, ∞)` and `[0, ∞)`; `langerTauInv_strictMonoOn`, `continuousOn_langerTauInv`,
  `hasDerivAt_langerTauInv`, `contDiffOn_langerTauInv` (`C^m`, all `m`, on `(0, ∞)`).
* `langerTauInv_expansion`: `0 ≤ ξ_* + s - τ^{-1}(s) ≤ (2 C_1/3) s²` for all `s ≥ 0`
  (`τ^{-1}(s) = ξ_* + s + O(s²)`), from Lemma K0(c).
* `chiQuantile_eq_langerTauInv`: `χ_a = τ^{-1}(λ Φ_a)` (`a ≥ 1/4`, `c' > 0`), equivalently
  `τ(χ_a) = λ Φ_a` (`langerTau_chiQuantile`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-- `τ^{-1}(s) = χ^{(1)}_{1/4 + k_tip s^{3/2}}`: for `s ≥ 0` the unique `x ≥ ξ_*` with
`N(x) = k_tip s^{3/2}`, i.e. `τ(x) = s`. -/
noncomputable def langerTauInv (s : ℝ) : ℝ := chiQuantile 1 (1 / 4 + kTip * s ^ (3 / 2 : ℝ))

lemma quarter_le_arg {s : ℝ} (hs : 0 ≤ s) : 1 / 4 ≤ 1 / 4 + kTip * s ^ (3 / 2 : ℝ) := by
  have := kTip_pos
  have := Real.rpow_nonneg hs (3 / 2 : ℝ)
  have := mul_nonneg kTip_pos.le this
  linarith

lemma langerTauInv_spec {s : ℝ} (hs : 0 ≤ s) :
    xiStar ≤ langerTauInv s ∧ cumulN (langerTauInv s) = kTip * s ^ (3 / 2 : ℝ) := by
  have h : xiStar ≤ langerTauInv s ∧
      1 * cumulN (langerTauInv s) = 1 / 4 + kTip * s ^ (3 / 2 : ℝ) - 1 / 4 :=
    chiQuantile_spec (c' := 1) one_pos (quarter_le_arg hs)
  exact ⟨h.1, by have := h.2; rw [one_mul] at this; linarith⟩

lemma langerTau_nonneg {x : ℝ} (hx : xiStar ≤ x) : 0 ≤ langerTau x := by
  rw [langerTau_eq_of_ge hx]
  exact Real.rpow_nonneg (div_nonneg (cumulN_nonneg hx) kTip_pos.le) _

lemma langerTau_langerTauInv {s : ℝ} (hs : 0 ≤ s) : langerTau (langerTauInv s) = s := by
  obtain ⟨h1, h2⟩ := langerTauInv_spec hs
  rw [langerTau_eq_of_ge h1, h2, mul_div_cancel_left₀ _ kTip_pos.ne', ← Real.rpow_mul hs]
  have : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
  rw [this, Real.rpow_one]

lemma langerTau_strictMonoOn : StrictMonoOn langerTau (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (contDiffOn_langerTau 0 |>.continuousOn) ?_
  intro x hx
  rw [interior_Ioi] at hx
  exact deriv_langerTau_pos hx

lemma langerTauInv_langerTau {x : ℝ} (hx : xiStar ≤ x) : langerTauInv (langerTau x) = x := by
  have hs := langerTau_nonneg hx
  obtain ⟨h1, _⟩ := langerTauInv_spec hs
  have h2 := langerTau_langerTauInv hs
  have hx0 : 0 < x := lt_of_lt_of_le xiStar_pos hx
  have hy0 : 0 < langerTauInv (langerTau x) := lt_of_lt_of_le xiStar_pos h1
  exact langerTau_strictMonoOn.injOn hy0 hx0 h2

lemma langerTauInv_zero : langerTauInv 0 = xiStar := by
  unfold langerTauInv
  rw [Real.zero_rpow (by norm_num), mul_zero, add_zero, chiQuantile_quarter 1 one_pos]

lemma langerTauInv_strictMonoOn : StrictMonoOn langerTauInv (Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  have h1 : a ^ (3 / 2 : ℝ) < b ^ (3 / 2 : ℝ) := Real.rpow_lt_rpow ha' hab (by norm_num)
  have hk := kTip_pos
  exact chiQuantile_strictMonoOn (c' := 1) one_pos (Set.mem_Ici.2 (quarter_le_arg ha'))
    (Set.mem_Ici.2 (quarter_le_arg hb')) (by nlinarith)

lemma continuousOn_langerTauInv : ContinuousOn langerTauInv (Ici 0) := by
  have h1 : ContinuousOn (fun s : ℝ => 1 / 4 + kTip * s ^ (3 / 2 : ℝ)) (Ici 0) :=
    continuousOn_const.add (continuousOn_const.mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).continuousOn))
  exact (continuousOn_chiQuantile one_pos).comp h1 (fun s hs => quarter_le_arg hs)

lemma hasDerivAt_langerTauInv {s : ℝ} (hs : 0 < s) :
    HasDerivAt langerTauInv (deriv langerTau (langerTauInv s))⁻¹ s := by
  obtain ⟨h1, _⟩ := langerTauInv_spec hs.le
  have hx0 : 0 < langerTauInv s := lt_of_lt_of_le xiStar_pos h1
  have hd : DifferentiableAt ℝ langerTau (langerTauInv s) :=
    ((contDiffOn_langerTau 1).differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hx0)
  refine HasDerivAt.of_local_left_inverse
    (continuousOn_langerTauInv.continuousAt (Ici_mem_nhds hs)) hd.hasDerivAt
    (deriv_langerTau_pos hx0).ne' ?_
  filter_upwards [Ioi_mem_nhds hs] with y hy
  exact langerTau_langerTauInv (le_of_lt hy)

lemma contDiffOn_langerTauInv (m : ℕ) : ContDiffOn ℝ m langerTauInv (Ioi 0) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_langerTauInv.mono Ioi_subset_Ici_self
  | succ m ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s hs => (hasDerivAt_langerTauInv hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hτ : ContDiffOn ℝ (m + 1 : ℕ) langerTau (Ioi 0) := contDiffOn_langerTau (m + 1)
    have hdτ : ContDiffOn ℝ m (deriv langerTau) (Ioi 0) :=
      hτ.deriv_of_isOpen isOpen_Ioi (by simp)
    have hmap : MapsTo langerTauInv (Ioi 0) (Ioi 0) := fun s hs =>
      lt_of_lt_of_le xiStar_pos (langerTauInv_spec (le_of_lt hs)).1
    have hc : ContDiffOn ℝ m (fun s => deriv langerTau (langerTauInv s)) (Ioi 0) :=
      hdτ.comp ih hmap
    have hne : ∀ s ∈ Ioi (0 : ℝ), deriv langerTau (langerTauInv s) ≠ 0 := fun s hs =>
      (deriv_langerTau_pos (hmap hs)).ne'
    exact (hc.inv hne).congr fun s hs => (hasDerivAt_langerTauInv hs).deriv

/-- `τ^{-1}(s) = ξ_* + s + O(s²)` (`remainder.tex`, Prop. 1.2(2), `(F1)`): for all `s ≥ 0`,
`0 ≤ ξ_* + s - τ^{-1}(s) ≤ (2 C_1/3) s²` with `C_1 = 3π/(20√2)` (Lemma K0(c)). -/
theorem langerTauInv_expansion {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ xiStar + s - langerTauInv s ∧
      xiStar + s - langerTauInv s ≤ (2 * c1K0 / 3) * s ^ 2 := by
  have ha := quarter_le_arg hs
  have hk := kTip_pos
  have hlam : lambdaComb 1 * phiQuantile (1 / 4 + kTip * s ^ (3 / 2 : ℝ)) = s := by
    have hP : phiQuantile (1 / 4 + kTip * s ^ (3 / 2 : ℝ)) = (kTip * s ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      unfold phiQuantile; congr 1; ring
    rw [hP]
    unfold lambdaComb
    rw [mul_one, Real.mul_rpow hk.le (Real.rpow_nonneg hs _), ← Real.rpow_mul hs]
    have h1 : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
    rw [h1, Real.rpow_one, ← mul_assoc, ← Real.rpow_add hk]
    norm_num
  have h := siteRadius_bounds (c' := 1) one_pos ha
  rw [hlam] at h
  have hr : siteRadius 1 (1 / 4 + kTip * s ^ (3 / 2 : ℝ)) = langerTauInv s - xiStar := rfl
  rw [hr] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · linarith
  · nlinarith

/-! ### Site identification -/

lemma kTip_mul_lambdaPhi_rpow {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    kTip * (lambdaComb c' * phiQuantile a) ^ (3 / 2 : ℝ) = (a - 1 / 4) / c' := by
  have hk := kTip_pos
  have hkc : 0 < kTip * c' := by positivity
  have h1 : 0 ≤ a - 1 / 4 := by linarith
  have hlm : lambdaComb c' ≥ 0 := by unfold lambdaComb; positivity
  have hΦ : 0 ≤ phiQuantile a := by unfold phiQuantile; positivity
  rw [Real.mul_rpow hlm hΦ]
  unfold lambdaComb phiQuantile
  rw [← Real.rpow_mul hkc.le, ← Real.rpow_mul h1]
  have e1 : (-(2 / 3 : ℝ)) * (3 / 2) = -1 := by norm_num
  have e2 : (2 / 3 : ℝ) * (3 / 2) = 1 := by norm_num
  rw [e1, e2, Real.rpow_neg_one, Real.rpow_one]
  field_simp

/-- **Site identification**: `χ_a = τ^{-1}(λ Φ_a)` for `a ≥ 1/4` (`c' > 0`). -/
theorem chiQuantile_eq_langerTauInv {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    chiQuantile c' a = langerTauInv (lambdaComb c' * phiQuantile a) := by
  have hlm : 0 ≤ lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hΦ : 0 ≤ phiQuantile a := by unfold phiQuantile; have : 0 ≤ a - 1 / 4 := by linarith
                                    positivity
  obtain ⟨h1, h2⟩ := langerTauInv_spec (mul_nonneg hlm hΦ)
  rw [kTip_mul_lambdaPhi_rpow hc' ha] at h2
  refine chiQuantile_eq_of_cumulN hc' ha h1 ?_
  rw [h2]; field_simp

/-- `τ(χ_a) = λ Φ_a`. -/
theorem langerTau_chiQuantile {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 ≤ a) :
    langerTau (chiQuantile c' a) = lambdaComb c' * phiQuantile a := by
  have hlm : 0 ≤ lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hΦ : 0 ≤ phiQuantile a := by unfold phiQuantile; have : 0 ≤ a - 1 / 4 := by linarith
                                    positivity
  rw [chiQuantile_eq_langerTauInv hc' ha, langerTau_langerTauInv (mul_nonneg hlm hΦ)]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.chiQuantile_eq_langerTauInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chiQuantile_eq_langerTauInv

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.contDiffOn_langerTauInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiffOn_langerTauInv

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerTauInv_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerTauInv_expansion

end FormalResearch.ModularBootstrap.Upper.Ramped

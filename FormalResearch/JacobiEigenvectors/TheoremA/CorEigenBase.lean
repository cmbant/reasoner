module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssembly

/-!
# Paper J, Layer 2: cor:eigen, shared real analysis (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (Steps 3, 4, 6); frozen statements `CorEigen*` of `TheoremA/EigenvalueStatements.lean`.

## The chain of lemmas for cor:eigen (what is used, what is new)

Inputs.  `S` is *any* family with `SmoothExt F K M S delta Cn`, `EigenRule F K M S hM C`, `ActionFormula F K S` (the conclusion of `thm:smo-spec`/`ThmAi` is
only used through these three, which is how `CorEigen*` quantify); Step 0 (`stepZeroD0`, proved, `StepZero.lean`); and the **slope input** `BandSlope`
(`-S_0' >= 2 c_0` on the closed band, uniformly in `mu`), the paper's Step 3.

* **B1** (`actionS0_bandHi`, `actionS0_bandLo`) `S_0(X_s^+) = 0`, `S_0(X_s^-) = pi L` (the integrand is `arccos z` with `z >= 1`, resp. `z <= -1`, on `(0, L)`).
* **B2** (`BandSlope.strictAntiOn`, `BandSlope.sub_ge`) `S_0` strictly decreasing on the band with `2 c_0 |X - X'| <= |S_0 X - S_0 X'|` (mean value theorem).
* **B3** (`exists_inverse`) the inverse `x_0 : [0, pi L] -> [X_s^-, X_s^+]` of `S_0` (intermediate value theorem with B1), `1/(2 c_0)`-Lipschitz.
* **B4** (`SmoothExt.lip_zero`, `SmoothExt.lip_one`, `SmoothExt.lip_deriv`) Lipschitz bounds from the `C^{M+1}` norm `Cn`: `|S_j(X) - S_j(X')| <= Cn |X - X'|`
  (`M >= 0`), and `|S_j'(X) - S_j'(X')| <= Cn |X - X'|` (`M >= 1`), on the extended interval `D = [X_s^- - delta, X_s^+ + delta]`.
* **B5** (`step_localise`) Step 0 puts every eigenvalue in `D` (`h` small) at distance `<= C_z h` from the band, and the rule gives `|S_0(clamp X_k) - y_k| <= C_1 h`
  (`clamp` the nearest point of the band: B4 moves `S_0` by `Cn C_z h`).
* Counting (`CorEigenCount.lean`), the level equation, gaps (`CorEigenInverse.lean`) are then elementary.

## Differences from the paper and findings

* **F-BB-1 (`0 < delta` is missing from every cor:eigen statement).**  The paper's `S_j` are given on a `delta`-neighbourhood, `delta > 0`.  The frozen `CorEigenS1`, `CorEigenInverse`,
  `CorEigenGap1`, `CorEigenGapM`, `CorEigenCount` quantify over `delta : ℝ` without `0 < delta`; for `delta <= 0` the smoothness domain lies inside the band, `S_j` is unconstrained on the end
  strips (as for `ThmSmoSpec`, finding F-S6-1), and `CorEigenInverse` is then false (its `InvLevel` asks for `0 < delta' <= delta`).  **Minimal correction: add the premise `0 < delta`.**
  All theorems below carry it.
* **F-BB-2 (the slope `-S_0' >= 2 c_0` is not a consequence of the rule and is not in `ThmSmoSpec`).**  Step 3 of the paper computes `S_0' = -int T^{-1/2} du` (PLAN: "not formalised", `MonotoneAction.lean`).
  Here it is the explicit hypothesis `BandSlope F K S`; it is *discharged from the window data* of the assembly in `CorEigenWindows.lean` (`bandSlope_of_windows`: the glued `S_0` has slope `<= -c`).
* **F-BB-3 (`InvExpansion` has no uniform norm bound on `x_r`).**  `CorEigenGapM` quantifies over any `x` with `InvExpansion`, which carries `ContDiffOn` of each `x_r(mu, .)` but no bound on its
  derivatives uniform in `mu`; the Taylor remainder in `CorEigenGapM` needs one (it holds for the actual `x_r`, by uniqueness and the recursion, but not for an arbitrary `x` read off the frozen
  statement).  **Applied** (`InvExpansion` now has the field): `exists Cx, forall mu in K, forall r <= M, forall i <= M + 1 - r, forall y, |iteratedDerivWithin i (x r mu) (Icc 0 (pi L)) y| <= Cx` to `InvExpansion`.
  (Not used by the proofs of this round; see the "Not formalised" of `CorEigenInverse.lean`.)

## Remaining items

`CorEigenGapM.lean` proves the general-order gap expansion from the expansion data and lists, with the chain, the exact statements still missing for `CorEigenS1`, `InvS0` (edge values) and `InvCoeffs` (the `x_r` recursion).

## Proved here (axiom-pinned)

`actionS0_bandHi`, `actionS0_bandLo` (B1); `SmoothExt.lip_zero`, `.diffAt`, `.deriv_bound`, `.deriv_continuousOn`, `.deriv_lip` (B4); `BandSlope.sub_ge`, `.strictAnti`, `.surj` (B2, B3);
`clampB` with `clampB_mem`, `clampB_dist`, `clampB_of_mem`.

## Not formalised

See the individual modules.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-! ### The slope input -/

/-- **The slope input (Step 3 of the proof of cor:eigen)**: `-S_0' >= 2 c_0` on the closed band, with `c_0 > 0` independent of `mu in K`. -/
def BandSlope (F : SymbolFamily Par) (K : Set Par) (S : ℕ → Par → ℝ → ℝ) : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ μ ∈ K, ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X

/-! ### B1: the values of `S_0` at the band ends -/

lemma actionS0_data (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K) :
    ∃ g : ℝ, Hyp F.L (F.G 0 μ) (F.B 0 μ) g ∧ ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) ∧ ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) := by
  obtain ⟨g, hg⟩ := hH
  have hr := hD.reg 0 (Nat.zero_le _)
  have h2 : (2 : WithTop ℕ∞) ≤ ((regBudget 0 - 10 * (0 / 2) : ℕ) : WithTop ℕ∞) := by
    have : (2 : ℕ) ≤ regBudget 0 - 10 * (0 / 2) := by unfold regBudget; omega
    exact_mod_cast this
  exact ⟨g, hg μ hμ, (hr.1.1 μ hμ).of_le h2, (hr.2.1 μ hμ).of_le h2⟩

/-- The action of a symbol whose arccos integrand is the constant `c` on `(0, L)`. -/
lemma actionS0_const_of (F : SymbolFamily Par) (μ : Par) (X c : ℝ)
    (h : ∀ u ∈ Ioo 0 F.L, Real.arccos ((X - F.B 0 μ u) / (2 * Real.sqrt (E0 F.L (F.G 0 μ) u))) = c) :
    actionS0 F μ X = c * F.L := by
  unfold actionS0
  rw [intervalIntegral.integral_of_le F.L_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h]
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo_of_le F.L_pos.le]
  simp [mul_comm]

/-- `S_0(X_s^+) = 0`. -/
lemma actionS0_bandHi (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K) :
    actionS0 F μ (F.bandHi μ) = 0 := by
  obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
  have hfc := HypMorse.fPlus_continuousOn hG2 hB2
  have := actionS0_const_of F μ (F.bandHi μ) 0 (fun u hu => by
    have hE := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hu
    have hs := Real.sqrt_pos.mpr hE
    have hle := HypMorse.fPlus_le_Xsp hfc (Ioo_subset_Icc_self hu)
    rw [Real.arccos_eq_zero, le_div_iff₀ (by positivity)]
    unfold fPlus at hle
    show 1 * (2 * Real.sqrt (E0 F.L (F.G 0 μ) u)) ≤ Xsp F.L (F.G 0 μ) (F.B 0 μ) - F.B 0 μ u
    linarith)
  simpa using this

/-- `S_0(X_s^-) = pi L`. -/
lemma actionS0_bandLo (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K) :
    actionS0 F μ (F.bandLo μ) = Real.pi * F.L := by
  obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
  have hfc := HypMorse.fMinus_continuousOn hG2 hB2
  exact actionS0_const_of F μ (F.bandLo μ) Real.pi (fun u hu => by
    have hE := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hu
    have hs := Real.sqrt_pos.mpr hE
    have hle := HypMorse.Xsm_le_fMinus hfc (Ioo_subset_Icc_self hu)
    rw [Real.arccos_eq_pi, div_le_iff₀ (by positivity)]
    unfold fMinus at hle
    show Xsm F.L (F.G 0 μ) (F.B 0 μ) - F.B 0 μ u ≤ -1 * (2 * Real.sqrt (E0 F.L (F.G 0 μ) u))
    linarith)

/-! ### B4: Lipschitz and derivative bounds from the `C^{M+1}` norm -/

section SmoothFacts

variable {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {M : ℕ} {δ Cn : ℝ}

lemma SmoothExt.lip_zero (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {x y : ℝ}
    (hx : x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) (hy : y ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    |S j μ x - S j μ y| ≤ Cn * |x - y| :=
  lip_of_iterDeriv_one (Nat.succ_pos M) (hS μ hμ j hj).1 (fun z hz => (hS μ hμ j hj).2 1 (by omega) z hz) hx hy

lemma SmoothExt.diffAt (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {x : ℝ}
    (hx : x ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) : DifferentiableAt ℝ (S j μ) x :=
  ((hS μ hμ j hj).1.differentiableOn (by exact_mod_cast Nat.succ_ne_zero M) x (Ioo_subset_Icc_self hx)).differentiableAt
    (Icc_mem_nhds hx.1 hx.2)

lemma SmoothExt.deriv_bound (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {x : ℝ}
    (hx : x ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) : |deriv (S j μ) x| ≤ Cn := by
  have := (hS μ hμ j hj).2 1 (by omega) x (Ioo_subset_Icc_self hx)
  rwa [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)] at this

lemma SmoothExt.deriv_continuousOn (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M)
    (hAB : F.bandLo μ - δ < F.bandHi μ + δ) :
    ContinuousOn (deriv (S j μ)) (Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) := by
  have h1 := (hS μ hμ j hj).1.continuousOn_derivWithin (uniqueDiffOn_Icc hAB) (by exact_mod_cast Nat.succ_pos M)
  exact (h1.mono Ioo_subset_Icc_self).congr (fun x hx => (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm)

/-- `S_j'` is `Cn`-Lipschitz on the open extended interval (needs `M >= 1`: the second derivative is bounded by `Cn`). -/
lemma SmoothExt.deriv_lip (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) (hM : 1 ≤ M)
    (hAB : F.bandLo μ - δ < F.bandHi μ + δ) {x y : ℝ}
    (hx : x ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) (hy : y ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    |deriv (S j μ) x - deriv (S j μ) y| ≤ Cn * |x - y| := by
  set D := Icc (F.bandLo μ - δ) (F.bandHi μ + δ) with hD
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin 1 (S j μ) D) D :=
    (hS μ hμ j hj).1.differentiableOn_iteratedDerivWithin (m := 1) (by exact_mod_cast (by omega : 1 < M + 1)) (uniqueDiffOn_Icc hAB)
  have hb : ∀ z ∈ D, ‖derivWithin (iteratedDerivWithin 1 (S j μ) D) D z‖ ≤ Cn := by
    intro z hz
    have := (hS μ hμ j hj).2 2 (by omega) z hz
    rw [iteratedDerivWithin_succ] at this
    simpa using this
  have key := Convex.norm_image_sub_le_of_norm_derivWithin_le hdiff hb (convex_Icc _ _) (Ioo_subset_Icc_self hy) (Ioo_subset_Icc_self hx)
  have e : ∀ z ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ), iteratedDerivWithin 1 (S j μ) D z = deriv (S j μ) z := fun z hz => by
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Icc_mem_nhds hz.1 hz.2)]
  rw [e x hx, e y hy] at key
  simpa [Real.norm_eq_abs] using key

end SmoothFacts

/-! ### B2, B3: the slope gives bi-Lipschitz monotonicity and the inverse `x_0` -/

section Slope

variable {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {M : ℕ} {δ Cn : ℝ}

lemma band_sub_ext {μ : Par} (hδ : 0 < δ) (hlt : F.bandLo μ < F.bandHi μ) :
    Icc (F.bandLo μ) (F.bandHi μ) ⊆ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := Icc_subset_Icc (by linarith) (by linarith)

lemma ioo_band_sub_ext {μ : Par} (hδ : 0 < δ) :
    Ioo (F.bandLo μ) (F.bandHi μ) ⊆ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ) := Ioo_subset_Ioo (by linarith) (by linarith)

/-- **B2** `2 c_0 |X - X'| <= |S_0 X - S_0 X'|` on the band. -/
lemma BandSlope.sub_ge (hS : SmoothExt F K M S δ Cn) (hδ : 0 < δ) {μ : Par} (hμ : μ ∈ K) (hlt : F.bandLo μ < F.bandHi μ) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hsl : ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X) {x y : ℝ}
    (hx : x ∈ Icc (F.bandLo μ) (F.bandHi μ)) (hy : y ∈ Icc (F.bandLo μ) (F.bandHi μ)) :
    2 * c0 * |x - y| ≤ |S 0 μ x - S 0 μ y| := by
  refine abs_sub_ge_of_deriv_le (c := 2 * c0) ?_ ?_ ?_ (by linarith) hx hy
  · exact ((hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono (band_sub_ext hδ hlt)
  · intro z hz
    exact hS.diffAt hμ (Nat.zero_le _) (ioo_band_sub_ext hδ hz)
  · intro z hz
    have := hsl z (Ioo_subset_Icc_self hz)
    linarith

/-- `S_0` is strictly decreasing on the band. -/
lemma BandSlope.strictAnti (hS : SmoothExt F K M S δ Cn) (hδ : 0 < δ) {μ : Par} (hμ : μ ∈ K) (hlt : F.bandLo μ < F.bandHi μ) {c0 : ℝ}
    (hc0 : 0 < c0) (hsl : ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X) :
    StrictAntiOn (S 0 μ) (Icc (F.bandLo μ) (F.bandHi μ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (((hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono (band_sub_ext hδ hlt)) ?_
  intro z hz
  rw [interior_Icc] at hz
  have := hsl z (Ioo_subset_Icc_self hz)
  linarith

/-- **B3** every value in `[0, pi L]` is taken by `S_0` on the band (intermediate value theorem, `S_0(X_s^+) = 0`, `S_0(X_s^-) = pi L`). -/
lemma BandSlope.surj (hS : SmoothExt F K M S δ Cn) (hδ : 0 < δ) (hA : ActionFormula F K S) (hH : HypOn F K) (hD : DM F K 0)
    {μ : Par} (hμ : μ ∈ K) (hlt : F.bandLo μ < F.bandHi μ) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    ∃ X ∈ Icc (F.bandLo μ) (F.bandHi μ), S 0 μ X = y := by
  have hcont : ContinuousOn (S 0 μ) (Icc (F.bandLo μ) (F.bandHi μ)) :=
    ((hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono (band_sub_ext hδ hlt)
  have hhi : S 0 μ (F.bandHi μ) = 0 := by
    rw [hA μ hμ _ ⟨hlt.le, le_rfl⟩]; exact actionS0_bandHi F K hH hD hμ
  have hlo : S 0 μ (F.bandLo μ) = Real.pi * F.L := by
    rw [hA μ hμ _ ⟨le_rfl, hlt.le⟩]; exact actionS0_bandLo F K hH hD hμ
  have := intermediate_value_Icc' hlt.le hcont
  rw [hhi, hlo] at this
  exact this hy

/-- The nearest point of the band. -/
def clampB (lo hi x : ℝ) : ℝ := max lo (min x hi)

lemma clampB_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clampB lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

lemma clampB_dist {lo hi c x : ℝ} (h : lo ≤ hi) (hc : 0 ≤ c) (hx1 : lo - c ≤ x) (hx2 : x ≤ hi + c) :
    |x - clampB lo hi x| ≤ c := by
  unfold clampB
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

lemma clampB_of_mem {lo hi x : ℝ} (hx : x ∈ Icc lo hi) : clampB lo hi x = x := by
  unfold clampB
  rw [min_eq_left hx.2, max_eq_right hx.1]

end Slope

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_bandHi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_bandHi

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_bandLo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_bandLo

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.sub_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.sub_ge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.strictAnti

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.BandSlope.surj

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SmoothExt.deriv_lip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SmoothExt.deriv_lip

end FormalResearch.JacobiEigenvectors.TheoremA

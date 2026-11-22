module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SmoothSpectrum
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumGlue
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumNorms
public import FormalResearch.JacobiEigenvectors.TheoremA.MonotoneAction
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero

/-!
# Paper J, Layer 2: assembly of the eigenvalue rule `thm:smo-spec` from local phase windows (L2.S5, L2.S6)

Source: Paper J `thmA.tex` `thm:smo-spec`; `app_thmA.tex`, proof of `thm:smo-spec` ("Substitution `t = h`", "Density", "Matching", "Back to `J_h`", "Uniqueness, extensions").
Frozen statements: `ThmSmoSpec`, `ThmAi` (`TheoremA/Statements.lean`); the corrected assembly statement is in `SpectrumAssemblyBulk.lean`.

## The chain of lemmas of the assembly (what exists, what is new, where the soft labels enter)

`I` runs over the *windows* of the cover: the bulk blocks `J_nu = [lo nu, hi nu]` and the two soft windows `I_+- = {|X - X_s^+-| <= delta_0/4}`.  A window carries the data
`WindowPhase` below: phase coefficients `Sigma_j(X,t)` (`j <= M`) jointly `C^{2M+1}` with a uniform norm bound, `Sigma_0 = S_0` on the band, a slope bound, and the
**labelled rule** `eq:smo-BSr2` at `t = h`: `sum_j h^j Sigma_j(X_k, h) = pi h (k + 1/2) + O(h^{M+1})` for every eigenvalue `X_k` of `J_h` in the window, `k` its index.

1. **Local rule per window** `[P]` `window_local`: `Phase substitution` `t = h` (`phase_substitution`, `taylor_bound_of_Sigma_bdd`, `SpectrumTaylor.lean`) turns the labelled rule into
   `sum_l h^l S^I_l(X_k) = pi h (k+1/2) + O(h^{M+1})`, `S^I_l := Scoef Sigma l in C^{M+1}(I)` (`Scoef_contDiffOn`), with the **`C^{M+1}` norm bound of `S^I_l`** from `Sigma_bdd`
   (`scoef_norm_bound`, `SpectrumNorms.lean`).
2. **Density `EigDensity`** `[P]` `density_of_windows` (the paragraph "Density"): order `0` of the local rules, the glued `S_0` (`glue_contDiffOn`) with slope `<= -c`
   (`abs_sub_ge_of_deriv_le`) and the nominal points `pi h (k + 1/2)` (`density_core`); inputs: Step 0 (`stepZeroD0`), `0 <= S_0 <= pi L` (`actionS0_mem_Icc`).
3. **Matching `S^I_l = S^{I'}_l` on overlaps** `[P]` `matching_pair`, `agree_of_windows` (the paragraph "Matching"): `matching_core` on `I cap I'` with the point sets "eigenvalues in `I cap I'`" (both
   local rules hold at them with the same label `k`, so their difference does) and the density of 2.; then `agree_of_windows` (pairs touching in one point agree through a third window).
4. **Gluing** `[P]` `glue_contDiffOn` (positive-length overlaps, `hcov`): `S_l in C^{M+1}([X_s^- - delta, X_s^+ + delta])` with the maximum of the window norms; **the barrier-side extension**
   to `[X_s^- - delta, X_s^+ + delta]` is *inside* the soft windows (`I_+` extends `delta_0/4` beyond `X_s^+`, where the chart's `mu_0, mu_{2r}` are the barrier-side extension
   of `thm:smo-MPS`): no separate extension lemma is needed; its regularity is part of `WindowPhase.Sigma_reg` of the soft windows.
5. **The rule for `S_l`** `[P]` `thmAi_of_windows`: every eigenvalue lies in some window (Step 0 and the cover), where `S_l` coincides with the local `S^I_l`.
6. **Localisation in `mu`** is *not* an assembly step here: `ChartInputs` (and `BulkPhaseInputs`) are already uniform on all of `K` (one cover for all `mu in K`, `ChartInputs.cover`), i.e. the
   localisation of `sec:tha-standing` is part of how those hypotheses are obtained (Layer 4).  The `mu`-dependence of the pieces would in any case be harmless (`SmoothExt`, `EigenRule` are pointwise
   in `mu` with uniform constants, so one may glue pieces over a finite cover of `K` by taking the maximum of the constants).
7. **Back from `tilde J_h` to `J_h`** `[P]` `smo_SM`/`eigClose_of_jets`/`rule_transfer` (`SmoothSpectrum.lean`): see `SpectrumAssemblyBulk.lean`.
8. **Uniqueness, extension independence** `[P]` `thmSmoSpec_unique`, `thmSmoSpec_extend` with `EigDensity` from 2. and `stepZeroD0`.

**Where the soft labels `BulkWindowLabels` / `PropThaW2` (3) enter.**  Only in the field `WindowPhase.rule` (the labelled rule `eq:smo-BSr2`): for a bulk block it is *proved* from `bulk_BSr2` and the
labels `BulkWindowLabels` (`SpectrumAssemblyBulk.lean`, premise `hlabels`); for a soft window it is `PropThaW2` (3) (quantisation with label = index) written for
`Sigma_+ = pi (mu_0 + sum h^{2r} mu_{2r})(X_s^+(t) - X, t)`.  Nothing else in the assembly depends on the labels (the windows of `bulk_count` are labelled by the value of `S_0`, not by the index).

## Proved here (axiom-pinned)

`window_local`, `windows_local_all`, `exists_pos_forall_le`, `lip_of_iterDeriv_one`, `actionS0_mem_Icc`, `overlap_pos`, `density_of_windows` (= `EigDensity` for `J_h`), `matching_pair`, `agree_of_windows`,
`thmAi_of_windows` (the conclusion of `ThmAi` for the family of the windows).

## Differences from the paper and findings

* **F-S6-4 (positive-length overlaps): CONFIRMED against `app_thmA.tex` ("Setting" of `thm:smo-BSr`: "consecutive ones overlapping in intervals of positive length", "two intervals of this cover meet, if at all, in an interval of positive length"), APPLIED (round 8).**
  `ChartInputs.cover_bulk` now puts every point of `[Jlo, Jhi]` in the relative interior of a block (`lo nu < X` or `lo nu = Jlo`, and `X < hi nu` or `hi nu = Jhi`, the form of `WindowCover.cov`), and
  `ChartInputs.cover` has strict ends (`bandHi < Jhi + delta_0`, `Jlo - delta_0 < bandLo`).  The gluing still takes the cover of the *windows* as the hypothesis `hcov : WindowCover` (it involves the
  soft window radii, which are not chart fields); the chart fields now imply the bulk-bulk and bulk-soft overlaps of positive length (`overlap_pos`), but the derivation of `hcov` from them is not done.
* **F-S6-5 (the charts must be those of `tilde J_h = truncSM F M`): CONFIRMED against `app_thmA.tex` ("Setting": "`G_j = B_j := 0` for `M < j <= 2K+1`", the frozen family of `tilde J_h`), APPLIED (round 8).**
  `ThmSmoSpec` now takes `CI`, `_PI` for `truncFamily F M` (moved before `ThmSmoSpec` in `Statements.lean`); the conclusion is about `F`.  `thmSmoSpec` (`SpectrumAssemblyBulk.lean`) proves it modulo `hlabels`, `WS`, `hcov`.
* **F-S6-6 (soft windows lack a phase-regularity input).**  The frozen `SoftEdgeChart` has `muS_bd`, `mu0_deriv`, `mu0_slope` and no joint `C^{2M+1}` regularity in `(X, t)` of `mu_0, mu_{2r}` nor of `X_s^+(t)`,
  no uniform norm bound: the soft analogue of `BulkPhaseInputs` is the new structure `SoftPhaseInputs` (`Charts/SoftPhaseInputs.lean`); `softUpWindow` (`SpectrumAssemblySoft.lean`) builds the upper soft `WindowPhase`
  from it and the labels `SoftLabels` (= `PropThaW2` (3) after Step 0, in the form of `eq:smo-BSr2`).
* **F-S6-7 (`StdAssump` of the frozen family): CONFIRMED, APPLIED (round 8).**  `FrozenStandard` has the hypothesis `DM F K (2 Kidx + 1)`, false for `truncSM F M` when `M < 2 Kidx + 1`; the proof of `frozenStandard` uses only the
  regularity `r >= regBudget (max (2 Kidx - 1) 0)` of the jets `2j, 2j+1` (`j <= Kidx`) and the remainder after the jet `2 Kidx + 1`.  That is the new structure `HypMorse.FrozenReg`; `frozenStandard_of_reg` proves
  `sec:tha-standing` under it, `frozenReg_of_dm` shows `DM F K (2 Kidx + 1)` implies it (so `frozenStandard` is a corollary, the frozen `FrozenStandard` statement is unchanged), `frozenReg_trunc` shows the truncated family
  satisfies it with only `(D_M)`.  The premise `hstd` is therefore proved in `thmSmoSpec`.
* **F-t0 (applied to this assembly).**  The chart data of `ThmSmoSpec` are on `paramSet K t0` with `t0` given, but the standing assumptions hold only for `t0 <= t1`: `thmSmoSpec` restricts the bulk charts, their phase inputs and the
  windows to `min t0 t1` (`SpectrumRestrict.lean`).

## Not formalised

The lower soft window (`WindowPhase` for `I_-`, via the reversal of eigen-systems of `negFamily`); `C^infty` jets.  (The slope bound `|S_0'| >= c` on a bulk block is `bulk_slope`, `BulkSlope.lean`, proved in round 8.)
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Small real-analysis lemmas -/

/-- A finite family of positive numbers has a positive lower bound. -/
lemma exists_pos_forall_le {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min f
    exact ⟨f i0, hf i0, hi0⟩

/-- A `C^{n}` function (`n >= 1`) on `[a, b]` whose first derivative is bounded by `C` is `C`-Lipschitz. -/
lemma lip_of_iterDeriv_one {f : ℝ → ℝ} {a b C : ℝ} {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Icc a b))
    (hb : ∀ x ∈ Icc a b, |iteratedDerivWithin 1 f (Icc a b) x| ≤ C) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ C * |x - y| := by
  have hdiff : DifferentiableOn ℝ f (Icc a b) :=
    hf.differentiableOn (by exact_mod_cast (by omega : n ≠ 0))
  have := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℝ) (f := f) (s := Icc a b) (C := C) hdiff
    (fun z hz => by simpa [Real.norm_eq_abs, iteratedDerivWithin_one] using hb z hz) (convex_Icc a b) hy hx
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- `0 <= S_0 <= pi L`. -/
lemma actionS0_mem_Icc (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K) (X : ℝ) :
    0 ≤ actionS0 F μ X ∧ actionS0 F μ X ≤ Real.pi * F.L := by
  obtain ⟨g, hg⟩ := hH
  have hyp := hg μ hμ
  have hr := hD.reg 0 (Nat.zero_le _)
  have h2 : (2 : WithTop ℕ∞) ≤ ((regBudget 0 - 10 * (0 / 2) : ℕ) : WithTop ℕ∞) := by
    have : (2 : ℕ) ≤ regBudget 0 - 10 * (0 / 2) := by unfold regBudget; omega
    exact_mod_cast this
  have hG2 : ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) := (hr.1.1 μ hμ).of_le h2
  have hB2 : ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) := (hr.2.1 μ hμ).of_le h2
  have hint := intervalIntegrable_arccos_action F.L_pos hyp hG2 hB2 X
  unfold actionS0
  constructor
  · exact intervalIntegral.integral_nonneg F.L_pos.le (fun u _ => Real.arccos_nonneg _)
  · have := intervalIntegral.integral_mono_on F.L_pos.le hint (intervalIntegrable_const (c := Real.pi))
      (fun u _ => Real.arccos_le_pi _)
    simpa [actInt, mul_comm] using this

/-! ### Windows -/

/-- **A phase window** (the data of `thm:smo-BSr` on one interval `I = [a(mu), b(mu)]` of the cover; see the module docstring).  `Sigma mu j X t` are the coefficients of the phase,
jointly `C^{2M+1}` with a uniform norm bound; `Sigma_zero`: `Sigma_0 = S_0` on the band; `slope`: `d_X Sigma_0(X, 0) <= -c` on the open window (paper: `S_0^I` is `C^1` with `d_X S_0^I <= -c`);
`rule`: the labelled rule `eq:smo-BSr2` at `t = h`, for every eigenvalue of `J_h(mu)` (`F.jacobiMat mu N`) in the window, `k` its index from the top. -/
structure WindowPhase (F : SymbolFamily Par) (K : Set Par) (t0 : ℝ) (M : ℕ) (a b : Par → ℝ) where
  Sigma : Par → ℕ → ℝ → ℝ → ℝ
  Sigma_reg : ∀ μ ∈ K, ∀ j ≤ M, JetRegJ (Sigma μ j) (Icc (a μ) (b μ)) t0 (2 * M + 1)
  Sigma_bdd : ∃ C : ℝ, ∀ μ ∈ K, ∀ j ≤ M, ∀ i ≤ 2 * M + 1, ∀ p ∈ Icc (a μ) (b μ) ×ˢ Icc (-t0) t0,
    ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => Sigma μ j q.1 q.2) (Icc (a μ) (b μ) ×ˢ Icc (-t0) t0) p‖ ≤ C
  Sigma_zero : ∀ μ ∈ K, ∀ X ∈ Icc (a μ) (b μ), X ∈ Icc (F.bandLo μ) (F.bandHi μ) → Sigma μ 0 X 0 = actionS0 F μ X
  slope : ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo (a μ) (b μ), deriv (fun X' => Sigma μ 0 X' 0) X ≤ -c
  rule : ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
      ∀ k : Fin (N + 1), Xs k ∈ Icc (a μ) (b μ) →
        |∑ j ∈ range (M + 1), F.step N ^ j * Sigma μ j (Xs k) (F.step N) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)|
          ≤ C * F.step N ^ (M + 1)

/-- **Step 1 of the chain (local rule per window).**  Phase substitution `t = h`: the coefficients `S^I_l = Scoef Sigma l` are `C^{M+1}` on the window with a uniform norm bound, and satisfy
the local rule `sum_l h^l S^I_l(X_k) = pi h (k + 1/2) + O(h^{M+1})` at every eigenvalue in the window. -/
theorem window_local {F : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M : ℕ} {a b : Par → ℝ} (W : WindowPhase F K t0 M a b)
    (ht0 : 0 < t0) (hab : ∀ μ ∈ K, a μ < b μ) :
    ∃ Cn Cr h0 : ℝ, 0 < h0 ∧
      (∀ μ ∈ K, ∀ l ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (Scoef (W.Sigma μ) l) (Icc (a μ) (b μ)) ∧
        ∀ i ≤ M + 1, ∀ x ∈ Icc (a μ) (b μ), |iteratedDerivWithin i (Scoef (W.Sigma μ) l) (Icc (a μ) (b μ)) x| ≤ Cn) ∧
      (∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
          ∀ k : Fin (N + 1), Xs k ∈ Icc (a μ) (b μ) →
            |∑ l ∈ range (M + 1), F.step N ^ l * Scoef (W.Sigma μ) l (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)|
              ≤ Cr * F.step N ^ (M + 1)) := by
  obtain ⟨C, hC⟩ := W.Sigma_bdd
  obtain ⟨Cr0, h0, hh0, hrule⟩ := W.rule
  obtain ⟨Cb, hCb⟩ : ∃ x : ℝ, x = max C 0 := ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; exact le_max_right _ _
  have hCbC : C ≤ Cb := by rw [hCb]; exact le_max_left _ _
  have hb : ∀ μ ∈ K, ∀ j ≤ M, ∀ i ≤ 2 * M + 1, ∀ p ∈ Icc (a μ) (b μ) ×ˢ Icc (-t0) t0,
      ‖iteratedFDerivWithin ℝ i (fun q : ℝ × ℝ => W.Sigma μ j q.1 q.2) (Icc (a μ) (b μ) ×ˢ Icc (-t0) t0) p‖ ≤ Cb :=
    fun μ hμ j hj i hi p hp => (hC μ hμ j hj i hi p hp).trans hCbC
  refine ⟨(M + 1) * Cb, Cr0 + (M + 1) * Cb, min h0 (t0 / 2), lt_min hh0 (by linarith), ?_, ?_⟩
  · intro μ hμ l hl
    have hJ : UniqueDiffOn ℝ (Icc (a μ) (b μ)) := uniqueDiffOn_Icc (hab μ hμ)
    refine ⟨Scoef_contDiffOn hJ ht0 (W.Sigma_reg μ hμ) hl, fun i hi x hx => ?_⟩
    exact scoef_norm_bound hJ ht0 (W.Sigma_reg μ hμ) Cb (hb μ hμ) hl hi hx
  · intro μ hμ N hN Xs Um hE k hk
    have hJ : UniqueDiffOn ℝ (Icc (a μ) (b μ)) := uniqueDiffOn_Icc (hab μ hμ)
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN0 : F.step N ≤ h0 := hN.trans (min_le_left _ _)
    have hNt : F.step N < t0 := lt_of_le_of_lt (hN.trans (min_le_right _ _)) (by linarith)
    have hCt := taylor_bound_of_Sigma_bdd hJ ht0 (W.Sigma_reg μ hμ) Cb (hb μ hμ)
    have hph := (phase_substitution hJ ht0 (W.Sigma_reg μ hμ) Cb hCt).2 (Xs k) hk (F.step N) hpos hNt
    have hr := hrule μ hμ N hN0 Xs Um hE k hk
    calc _ = |(∑ l ∈ range (M + 1), F.step N ^ l * Scoef (W.Sigma μ) l (Xs k)
            - ∑ j ∈ range (M + 1), F.step N ^ j * W.Sigma μ j (Xs k) (F.step N))
          + (∑ j ∈ range (M + 1), F.step N ^ j * W.Sigma μ j (Xs k) (F.step N)
            - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (M + 1) * Cb * F.step N ^ (M + 1) + Cr0 * F.step N ^ (M + 1) := by
          refine add_le_add ?_ hr
          rw [abs_sub_comm]; exact hph
      _ = (Cr0 + (M + 1) * Cb) * F.step N ^ (M + 1) := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.window_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.window_local

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_mem_Icc

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.lip_of_iterDeriv_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.lip_of_iterDeriv_one

/-! ### Cover geometry -/

/-- The geometry of the cover of `U(mu) = [X_s^- - delta, X_s^+ + delta]` by the windows `[a i mu, b i mu]`: all inside `U`, positive length, every point of `U` in the relative interior
of some window (the paper's "consecutive ones overlapping in intervals of positive length"; finding F-S6-4), and distinct windows overlap only inside the band (order-`0` agreement). -/
structure WindowCover {ι : Type*} (F : SymbolFamily Par) (K : Set Par) (a b : ι → Par → ℝ) (δ : ℝ) : Prop where
  sub : ∀ μ ∈ K, ∀ i, F.bandLo μ - δ ≤ a i μ ∧ a i μ < b i μ ∧ b i μ ≤ F.bandHi μ + δ
  cov : ∀ μ ∈ K, ∀ x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∃ i, a i μ ≤ x ∧ x ≤ b i μ ∧
    (a i μ < x ∨ a i μ = F.bandLo μ - δ) ∧ (x < b i μ ∨ b i μ = F.bandHi μ + δ)
  ovl : ∀ μ ∈ K, ∀ i j, i ≠ j → ∀ x ∈ Icc (a i μ) (b i μ), x ∈ Icc (a j μ) (b j μ) → x ∈ Icc (F.bandLo μ) (F.bandHi μ)

/-- Two windows, one of which contains `x` in its relative interior, overlap in a set of positive length. -/
lemma overlap_pos {A B ai bi ak bk x : ℝ} (hi : A ≤ ai ∧ ai < bi ∧ bi ≤ B) (hk : A ≤ ak ∧ ak < bk ∧ bk ≤ B)
    (hxi : ai ≤ x ∧ x ≤ bi) (hxk : ak ≤ x ∧ x ≤ bk) (h3 : ak < x ∨ ak = A) (h4 : x < bk ∨ bk = B) :
    max ai ak < min bi bk := by
  have h1 : ai < bk := by
    rcases h4 with h | h
    · linarith [hxi.1]
    · linarith [hi.2.1, hi.2.2]
  have h2 : ak < bi := by
    rcases h3 with h | h
    · linarith [hxi.2]
    · linarith [hi.1, hi.2.1]
  exact lt_min (max_lt hi.2.1 h2) (max_lt h1 hk.2.1)

section Assembly

variable {ι : Type*} [Fintype ι] {F : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M : ℕ} {a b : ι → Par → ℝ} {δ : ℝ}

/-- Uniform constants over the finitely many windows. -/
lemma windows_local_all (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hab : ∀ μ ∈ K, ∀ i, a i μ < b i μ) :
    ∃ Cn Cr ε : ℝ, 0 ≤ Cn ∧ 0 ≤ Cr ∧ 0 < ε ∧
      (∀ i, ∀ μ ∈ K, ∀ l ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) ∧
        ∀ n ≤ M + 1, ∀ x ∈ Icc (a i μ) (b i μ), |iteratedDerivWithin n (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) x| ≤ Cn) ∧
      (∀ i, ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ ε →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
          ∀ k : Fin (N + 1), Xs k ∈ Icc (a i μ) (b i μ) →
            |∑ l ∈ range (M + 1), F.step N ^ l * Scoef ((W i).Sigma μ) l (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)|
              ≤ Cr * F.step N ^ (M + 1)) := by
  have hloc := fun i => window_local (W i) ht0 (fun μ hμ => hab μ hμ i)
  choose Cn Cr h0 hh0 hreg hrule using hloc
  obtain ⟨ε, hε, hεle⟩ := exists_pos_forall_le h0 hh0
  refine ⟨∑ i, |Cn i|, ∑ i, |Cr i|, ε, Finset.sum_nonneg (fun i _ => abs_nonneg _), Finset.sum_nonneg (fun i _ => abs_nonneg _), hε, ?_, ?_⟩
  · intro i μ hμ l hl
    refine ⟨(hreg i μ hμ l hl).1, fun n hn x hx => ?_⟩
    exact ((hreg i μ hμ l hl).2 n hn x hx).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cn i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
  · intro i μ hμ N hN Xs Um hE k hk
    have := hrule i μ hμ N (hN.trans (hεle i)) Xs Um hE k hk
    refine this.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cr i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))) (pow_nonneg (FormalResearch.JB.stepSize_pos F.L_pos N).le _))

/-- **Step 2 of the chain: density** (paragraph "Density", for `J_h`): every point of the band is within `C h` of an eigenvalue.  From the order-`0` local rules, the glued `S_0`
(slope `<= -c`) and the nominal points (see the module docstring). -/
theorem density_of_windows (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0) :
    ∃ CD hD : ℝ, 0 < hD ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hD →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ), ∃ k : Fin (N + 1), |Xs k - Y| ≤ CD * F.step N := by
  obtain ⟨Cn, Cr, ε, hCn, hCr, hε, hreg, hrule⟩ := windows_local_all W ht0 (fun μ hμ i => (hcov.sub μ hμ i).2.1)
  choose c hc0 hcsl using fun i => (W i).slope
  obtain ⟨c0, hc0pos, hc0le⟩ := exists_pos_forall_le c hc0
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD
  refine ⟨((Cr + M * Cn) + Real.pi) / c0, min (min ε 1) (min hz0 (δ / (|Cz| + 1))),
    lt_min (lt_min hε one_pos) (lt_min hzp (div_pos hδ (by positivity))), ?_⟩
  intro μ hμ N hN Xs Um hE Y hY
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hN1 : F.step N ≤ ε := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hN2 : F.step N ≤ 1 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN3 : F.step N ≤ hz0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN4 : F.step N ≤ δ / (|Cz| + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCzh : |Cz| * F.step N < δ := by
    rw [le_div_iff₀ (by positivity)] at hN4
    nlinarith [abs_nonneg Cz]
  set A := F.bandLo μ - δ with hA
  set B := F.bandHi μ + δ with hB
  have hagree0 : ∀ i j, ∀ x ∈ Icc (a i μ) (b i μ), x ∈ Icc (a j μ) (b j μ) →
      Scoef ((W i).Sigma μ) 0 x = Scoef ((W j).Sigma μ) 0 x := by
    intro i j x hxi hxj
    by_cases hij : i = j
    · rw [hij]
    · have hband := hcov.ovl μ hμ i j hij x hxi hxj
      rw [Scoef_zero, Scoef_zero, (W i).Sigma_zero μ hμ x hxi hband, (W j).Sigma_zero μ hμ x hxj hband]
  obtain ⟨g, hg, hgc, -⟩ := glue_contDiffOn (M + 1) A B (fun i => a i μ) (fun i => b i μ) (fun i => Scoef ((W i).Sigma μ) 0)
    (fun i => hcov.sub μ hμ i) (fun i => (hreg i μ hμ 0 (Nat.zero_le _)).1) hagree0 (hcov.cov μ hμ)
  have hdiff : ∀ z ∈ Ioo A B, DifferentiableAt ℝ g z := fun z hz =>
    (hgc.differentiableOn (by exact_mod_cast Nat.succ_ne_zero M) z (Ioo_subset_Icc_self hz)).differentiableAt (Icc_mem_nhds hz.1 hz.2)
  have hder : ∀ z ∈ Ioo A B, deriv g z ≤ -c0 := by
    intro z hz
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hcov.cov μ hμ z (Ioo_subset_Icc_self hz)
    have hnh : Icc (a i μ) (b i μ) ∈ nhds z := by
      have := Icc_mem_nhdsWithin_Icc (Ioo_subset_Icc_self hz) hi1 hi2 hi3 hi4
      rwa [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hz.1 hz.2)] at this
    have hzI : z ∈ Ioo (a i μ) (b i μ) := by
      have : z ∈ interior (Icc (a i μ) (b i μ)) := mem_interior_iff_mem_nhds.mpr hnh
      rwa [interior_Icc] at this
    have hev : g =ᶠ[nhds z] fun X => (W i).Sigma μ 0 X 0 :=
      Filter.eventually_of_mem hnh (fun y hy => by rw [hg i y hy, Scoef_zero])
    rw [hev.deriv_eq]
    exact (hcsl i μ hμ z hzI).trans (neg_le_neg (hc0le i))
  have hsl : ∀ x ∈ Icc A B, ∀ y ∈ Icc A B, c0 * |x - y| ≤ |g x - g y| := fun x hx y hy =>
    abs_sub_ge_of_deriv_le hgc.continuousOn hdiff hder hc0pos.le hx hy
  have hxU : ∀ k : Fin (N + 1), Xs k ∈ Icc A B := by
    intro k
    obtain ⟨h1, h2⟩ := hzero μ hμ N hN3 Xs Um hE k
    have hle : Cz * F.step N ≤ |Cz| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have hle2 : -(Cz * F.step N) ≤ |Cz| * F.step N := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs Cz) hpos.le
      linarith
    exact ⟨by linarith, by linarith⟩
  have hrule0 : ∀ k : Fin (N + 1), |g (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)| ≤ (Cr + M * Cn) * F.step N := by
    intro k
    obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ (Xs k) (hxU k)
    have hgx : g (Xs k) = Scoef ((W i).Sigma μ) 0 (Xs k) := hg i _ ⟨hi1, hi2⟩
    have hr := hrule i μ hμ N hN1 Xs Um hE k ⟨hi1, hi2⟩
    have hsplit : ∑ l ∈ range (M + 1), F.step N ^ l * Scoef ((W i).Sigma μ) l (Xs k)
        = Scoef ((W i).Sigma μ) 0 (Xs k) + ∑ l ∈ range M, F.step N ^ (l + 1) * Scoef ((W i).Sigma μ) (l + 1) (Xs k) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul]
      ring
    have htail : |∑ l ∈ range M, F.step N ^ (l + 1) * Scoef ((W i).Sigma μ) (l + 1) (Xs k)| ≤ M * Cn * F.step N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ range M, |F.step N ^ (l + 1) * Scoef ((W i).Sigma μ) (l + 1) (Xs k)|
          ≤ ∑ l ∈ range M, Cn * F.step N := by
            apply Finset.sum_le_sum
            intro l hl
            have hl' : l + 1 ≤ M := Finset.mem_range.mp hl
            have hb := (hreg i μ hμ (l + 1) hl').2 0 (Nat.zero_le _) (Xs k) ⟨hi1, hi2⟩
            rw [iteratedDerivWithin_zero] at hb
            rw [abs_mul, abs_of_pos (pow_pos hpos _)]
            calc F.step N ^ (l + 1) * |Scoef ((W i).Sigma μ) (l + 1) (Xs k)| ≤ F.step N * Cn :=
                  mul_le_mul (pow_le_of_le_one hpos.le hN2 (Nat.succ_ne_zero l)) hb (abs_nonneg _) hpos.le
              _ = Cn * F.step N := by ring
        _ = M * Cn * F.step N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hpow : F.step N ^ (M + 1) ≤ F.step N := pow_le_of_le_one hpos.le hN2 (Nat.succ_ne_zero M)
    rw [hsplit] at hr
    have e : g (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)
        = ((Scoef ((W i).Sigma μ) 0 (Xs k) + ∑ l ∈ range M, F.step N ^ (l + 1) * Scoef ((W i).Sigma μ) (l + 1) (Xs k))
            - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2))
          - ∑ l ∈ range M, F.step N ^ (l + 1) * Scoef ((W i).Sigma μ) (l + 1) (Xs k) := by rw [hgx]; ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ Cr * F.step N ^ (M + 1) + M * Cn * F.step N := add_le_add hr htail
      _ ≤ Cr * F.step N + M * Cn * F.step N := by nlinarith [mul_le_mul_of_nonneg_left hpow hCr]
      _ = (Cr + M * Cn) * F.step N := by ring
  have hYU : Y ∈ Icc A B := ⟨by linarith [hY.1], by linarith [hY.2]⟩
  obtain ⟨iY, hY1, hY2, -, -⟩ := hcov.cov μ hμ Y hYU
  have hgY : g Y = actionS0 F μ Y := by
    rw [hg iY Y ⟨hY1, hY2⟩, Scoef_zero]
    exact (W iY).Sigma_zero μ hμ Y ⟨hY1, hY2⟩ hY
  obtain ⟨hS0, hS1⟩ := actionS0_mem_Icc F K hH hD hμ Y
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  exact density_core g (Icc A B) hc0pos hsl hpos hL Xs hxU hrule0 hYU (by rw [hgY]; exact hS0) (by rw [hgY]; exact hS1)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.density_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.density_of_windows

/-- **Step 3 of the chain: matching on one overlap of positive length.**  Two distinct windows have the same local coefficients `S^I_l = S^{I'}_l` on `I cap I'` (given the density). -/
theorem matching_pair (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0)
    (hden : ∃ CD hD : ℝ, 0 < hD ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hD →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ), ∃ k : Fin (N + 1), |Xs k - Y| ≤ CD * F.step N)
    (i j : ι) (hij : i ≠ j) {μ : Par} (hμ : μ ∈ K) (hlt : max (a i μ) (a j μ) < min (b i μ) (b j μ)) :
    ∀ l ≤ M, ∀ x ∈ Icc (max (a i μ) (a j μ)) (min (b i μ) (b j μ)),
      Scoef ((W i).Sigma μ) l x = Scoef ((W j).Sigma μ) l x := by
  obtain ⟨Cn, Cr, ε, hCn, hCr, hε, hreg, hrule⟩ := windows_local_all W ht0 (fun μ hμ i => (hcov.sub μ hμ i).2.1)
  obtain ⟨CD, hDd, hDpos, hdens⟩ := hden
  obtain ⟨he0, hep, hex⟩ := exists_eig_small F K hH hD
  set α := max (a i μ) (a j μ) with hα
  set β := min (b i μ) (b j μ) with hβ
  have hαI : ∀ x ∈ Icc α β, x ∈ Icc (a i μ) (b i μ) ∧ x ∈ Icc (a j μ) (b j μ) := fun x hx =>
    ⟨⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩, ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩⟩
  have hband : ∀ x ∈ Icc α β, x ∈ Icc (F.bandLo μ) (F.bandHi μ) := fun x hx =>
    hcov.ovl μ hμ i j hij x (hαI x hx).1 (hαI x hx).2
  let d : ℕ → ℝ → ℝ := fun l x => Scoef ((W i).Sigma μ) l x - Scoef ((W j).Sigma μ) l x
  have hdbd : ∀ l ≤ M, ∀ x ∈ Icc α β, |d l x| ≤ 2 * Cn := by
    intro l hl x hx
    have h1 := (hreg i μ hμ l hl).2 0 (Nat.zero_le _) x (hαI x hx).1
    have h2 := (hreg j μ hμ l hl).2 0 (Nat.zero_le _) x (hαI x hx).2
    rw [iteratedDerivWithin_zero] at h1 h2
    calc |d l x| ≤ |Scoef ((W i).Sigma μ) l x| + |Scoef ((W j).Sigma μ) l x| := abs_sub _ _
      _ ≤ 2 * Cn := by linarith
  have hdlip : ∀ l ≤ M, ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |d l x - d l y| ≤ (2 * Cn) * |x - y| := by
    intro l hl x hx y hy
    have hli := lip_of_iterDeriv_one (n := M + 1) (by omega) (hreg i μ hμ l hl).1 (fun z hz => (hreg i μ hμ l hl).2 1 (by omega) z hz)
      (hαI x hx).1 (hαI y hy).1
    have hlj := lip_of_iterDeriv_one (n := M + 1) (by omega) (hreg j μ hμ l hl).1 (fun z hz => (hreg j μ hμ l hl).2 1 (by omega) z hz)
      (hαI x hx).2 (hαI y hy).2
    have e : d l x - d l y = (Scoef ((W i).Sigma μ) l x - Scoef ((W i).Sigma μ) l y) - (Scoef ((W j).Sigma μ) l x - Scoef ((W j).Sigma μ) l y) := by
      simp only [d]; ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ Cn * |x - y| + Cn * |x - y| := add_le_add hli hlj
      _ = (2 * Cn) * |x - y| := by ring
  let Ev : ℕ → Set ℝ := fun N => {x | (∃ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
    IsEigenSystem (F.jacobiMat μ N) Xs Um ∧ ∃ k : Fin (N + 1), Xs k = x)} ∩ Icc α β
  suffices key : ∀ l ≤ M, ∀ x ∈ Icc α β, d l x = 0 from fun l hl x hx => sub_eq_zero.mp (key l hl x hx)
  refine matching_core α β hlt M d (2 * Cn) (2 * Cn) hdbd hdlip (fun N => F.step N)
    (fun N => FormalResearch.JB.stepSize_pos F.L_pos N) (fun e he => step_small F he) Ev (2 * Cr) ε (2 * CD) hε
    (fun N x hx => hx.2) ?_ ?_
  · intro N hN x hx
    obtain ⟨⟨Xs, Um, hE, k, rfl⟩, hxI⟩ := hx
    have r1 := hrule i μ hμ N hN Xs Um hE k (hαI _ hxI).1
    have r2 := hrule j μ hμ N hN Xs Um hE k (hαI _ hxI).2
    have e : ∑ l ∈ range (M + 1), F.step N ^ l * d l (Xs k)
        = (∑ l ∈ range (M + 1), F.step N ^ l * Scoef ((W i).Sigma μ) l (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2))
          - (∑ l ∈ range (M + 1), F.step N ^ l * Scoef ((W j).Sigma μ) l (Xs k) - Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) := by
      simp only [d, mul_sub, Finset.sum_sub_distrib]; ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ Cr * F.step N ^ (M + 1) + Cr * F.step N ^ (M + 1) := add_le_add r1 r2
      _ = (2 * Cr) * F.step N ^ (M + 1) := by ring
  · intro X hX
    have hXband := hband X (Ioo_subset_Icc_self hX)
    set r := min (X - α) (β - X) with hr
    have hrpos : 0 < r := lt_min (by linarith [hX.1]) (by linarith [hX.2])
    obtain ⟨N0, hN0⟩ := step_small F (show 0 < min (min hDd he0) (r / (|2 * CD| + 1)) from
      lt_min (lt_min hDpos hep) (div_pos hrpos (by positivity)))
    refine ⟨N0, fun N hN => ?_⟩
    have hlt' := hN0 N hN
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have h1 : F.step N ≤ hDd := (hlt'.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
    have h2 : F.step N ≤ he0 := (hlt'.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
    have h3 : F.step N < r / (|2 * CD| + 1) := hlt'.trans_le (min_le_right _ _)
    obtain ⟨Xs, Um, hE⟩ := hex μ hμ N h2
    obtain ⟨k, hk⟩ := hdens μ hμ N h1 Xs Um hE X hXband
    refine ⟨Xs k, ⟨⟨Xs, Um, hE, k, rfl⟩, ?_⟩, ?_⟩
    · have hCDh : |2 * CD| * F.step N < r := by
        rw [lt_div_iff₀ (by positivity)] at h3
        nlinarith [abs_nonneg (2 * CD)]
      have hle : CD * F.step N ≤ |2 * CD| * F.step N := by
        have : CD ≤ |2 * CD| := by
          rw [abs_mul, abs_two]; nlinarith [abs_nonneg CD, le_abs_self CD]
        exact mul_le_mul_of_nonneg_right this hpos.le
      have hle2 : -(CD * F.step N) ≤ |2 * CD| * F.step N := by
        have : -CD ≤ |2 * CD| := by
          rw [abs_mul, abs_two]; nlinarith [abs_nonneg CD, neg_le_abs CD]
        nlinarith [mul_le_mul_of_nonneg_right this hpos.le]
      have := abs_le.mp hk
      have hmin1 : r ≤ X - α := min_le_left _ _
      have hmin2 : r ≤ β - X := min_le_right _ _
      constructor <;> nlinarith
    · calc |Xs k - X| ≤ CD * F.step N := hk
        _ ≤ 2 * CD * F.step N := by
          have : CD ≤ 2 * CD := by
            have h0 : 0 ≤ CD := by
              have := (abs_nonneg (Xs k - X)).trans hk
              by_contra hneg
              rw [not_le] at hneg
              nlinarith [mul_neg_of_neg_of_pos hneg hpos]
            linarith
          exact mul_le_mul_of_nonneg_right this hpos.le

/-- **Agreement on all overlaps.**  Windows that touch in a single point agree there through a third window containing the point in its relative interior. -/
theorem agree_of_windows (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 0)
    (hden : ∃ CD hD : ℝ, 0 < hD ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hD →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ), ∃ k : Fin (N + 1), |Xs k - Y| ≤ CD * F.step N)
    {μ : Par} (hμ : μ ∈ K) :
    ∀ l ≤ M, ∀ i j, ∀ x ∈ Icc (a i μ) (b i μ), x ∈ Icc (a j μ) (b j μ) →
      Scoef ((W i).Sigma μ) l x = Scoef ((W j).Sigma μ) l x := by
  intro l hl i j x hxi hxj
  have hxU : x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := by
    have h1 := hcov.sub μ hμ i
    exact ⟨by linarith [h1.1, hxi.1], by linarith [h1.2.2, hxi.2]⟩
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hcov.cov μ hμ x hxU
  have pair : ∀ m : ι, x ∈ Icc (a m μ) (b m μ) →
      Scoef ((W m).Sigma μ) l x = Scoef ((W k).Sigma μ) l x := by
    intro m hxm
    by_cases hmk : m = k
    · rw [hmk]
    · have hlt := overlap_pos (hcov.sub μ hμ m) (hcov.sub μ hμ k) ⟨hxm.1, hxm.2⟩ ⟨hk1, hk2⟩ hk3 hk4
      exact matching_pair W ht0 hδ hcov hK hH hD hden m k hmk hμ hlt l hl x ⟨max_le hxm.1 hk1, le_min hxm.2 hk2⟩
  rw [pair i hxi, pair j hxj]

/-- **Steps 4--5 of the chain: the assembly.**  From the windows, the cover and the standing assumptions: `C^{M+1}` functions `S_0, ..., S_M` on `[X_s^- - delta, X_s^+ + delta]` with uniform
norm, `S_0` the action on the band, and the rule `sum h^j S_j(X_k) = pi h (k + 1/2) + O(h^{M+1})` for every eigenvalue of `J_h`.  (This is the conclusion of `ThmAi` for the family `F` of the windows.) -/
theorem thmAi_of_windows (W : ∀ i, WindowPhase F K t0 M (a i) (b i)) (ht0 : 0 < t0) (hδ : 0 < δ) (hcov : WindowCover F K a b δ)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K M) :
    ∃ (δ' Cn C hM : ℝ) (S : ℕ → Par → ℝ → ℝ), 0 < δ' ∧ SmoothExt F K M S δ' Cn ∧ ActionFormula F K S ∧ EigenRule F K M S hM C := by
  classical
  have hD0 : DM F K 0 := dm_zero_of_dm F K M hK hD
  obtain ⟨Cn, Cr, ε, hCn, hCr, hε, hreg, hrule⟩ := windows_local_all W ht0 (fun μ hμ i => (hcov.sub μ hμ i).2.1)
  have hden := density_of_windows W ht0 hδ hcov hK hH hD0
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD0
  have hglue : ∀ μ ∈ K, ∀ l ≤ M, ∃ g : ℝ → ℝ, (∀ i, ∀ x ∈ Icc (a i μ) (b i μ), g x = Scoef ((W i).Sigma μ) l x) ∧
      ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) g (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
      ∀ n : ℕ, ∀ x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∃ i, x ∈ Icc (a i μ) (b i μ) ∧
        iteratedDerivWithin n g (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) x
          = iteratedDerivWithin n (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) x :=
    fun μ hμ l hl => glue_contDiffOn (M + 1) _ _ (fun i => a i μ) (fun i => b i μ) (fun i => Scoef ((W i).Sigma μ) l)
      (hcov.sub μ hμ) (fun i => (hreg i μ hμ l hl).1) (agree_of_windows W ht0 hδ hcov hK hH hD0 hden hμ l hl) (hcov.cov μ hμ)
  let S : ℕ → Par → ℝ → ℝ := fun l μ => if h : μ ∈ K ∧ l ≤ M then Classical.choose (hglue μ h.1 l h.2) else fun _ => 0
  have hS : ∀ μ ∈ K, ∀ l ≤ M, (∀ i, ∀ x ∈ Icc (a i μ) (b i μ), S l μ x = Scoef ((W i).Sigma μ) l x) ∧
      ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (S l μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
      ∀ n : ℕ, ∀ x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ), ∃ i, x ∈ Icc (a i μ) (b i μ) ∧
        iteratedDerivWithin n (S l μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) x
          = iteratedDerivWithin n (Scoef ((W i).Sigma μ) l) (Icc (a i μ) (b i μ)) x := by
    intro μ hμ l hl
    have h := Classical.choose_spec (hglue μ hμ l hl)
    have e : S l μ = Classical.choose (hglue μ hμ l hl) := by simp only [S]; rw [dif_pos ⟨hμ, hl⟩]
    rw [e]
    exact h
  refine ⟨δ, Cn, Cr, min (min ε 1) (min hz0 (δ / (|Cz| + 1))), S, hδ, ?_, ?_, ?_⟩
  · intro μ hμ j hj
    obtain ⟨-, hc, hd⟩ := hS μ hμ j hj
    refine ⟨hc, fun n hn x hx => ?_⟩
    obtain ⟨i, hxi, heq⟩ := hd n x hx
    rw [heq]
    exact (hreg i μ hμ j hj).2 n hn x hxi
  · intro μ hμ X hX
    have hXU : X ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
    obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ X hXU
    obtain ⟨hg, -, -⟩ := hS μ hμ 0 (Nat.zero_le _)
    rw [hg i X ⟨hi1, hi2⟩, Scoef_zero]
    exact (W i).Sigma_zero μ hμ X ⟨hi1, hi2⟩ hX
  · refine ⟨lt_min (lt_min hε one_pos) (lt_min hzp (div_pos hδ (by positivity))), ?_⟩
    intro μ hμ N hN Xs Um hE k
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN1 : F.step N ≤ ε := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN3 : F.step N ≤ hz0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hN4 : F.step N ≤ δ / (|Cz| + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hCzh : |Cz| * F.step N < δ := by
      rw [le_div_iff₀ (by positivity)] at hN4
      nlinarith [abs_nonneg Cz]
    obtain ⟨h1, h2⟩ := hzero μ hμ N hN3 Xs Um hE k
    have hle : Cz * F.step N ≤ |Cz| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have hle2 : -(Cz * F.step N) ≤ |Cz| * F.step N := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs Cz) hpos.le
      linarith
    have hxU : Xs k ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith, by linarith⟩
    obtain ⟨i, hi1, hi2, -, -⟩ := hcov.cov μ hμ (Xs k) hxU
    have hr := hrule i μ hμ N hN1 Xs Um hE k ⟨hi1, hi2⟩
    have e : ∑ j ∈ range (M + 1), F.step N ^ j * S j μ (Xs k) = ∑ j ∈ range (M + 1), F.step N ^ j * Scoef ((W i).Sigma μ) j (Xs k) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
      rw [(hS μ hμ j hjM).1 i (Xs k) ⟨hi1, hi2⟩]
    rw [e]
    exact hr

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.matching_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.matching_pair

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.agree_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.agree_of_windows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_windows

end Assembly

end FormalResearch.JacobiEigenvectors.TheoremA

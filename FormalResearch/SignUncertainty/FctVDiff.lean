/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctChartSetup
public import FormalResearch.SignUncertainty.FctHomotopyJets
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# `(fct:V-diff-jets)`, first line, in one parameter direction (F2a, `fct:comp-cfu`)

* `hasDerivAt_iteratedDeriv_path`: for `f ∈ C^{n+2}` on an open set `U`, `d/dt [∂_s^n f(p₀ + t v, s)](Y) = ∂_s^n [∂_v f](p₀ + t v, s)(Y)`
  (induction on `n`, Schwarz symmetry of the second derivative);
* `V_diff_jets_Y`: the weighted one-variable jets of `V(p₀ + v, ·) - V(p₀, ·)`: `|∂_Y^n (V(p₀+v) - V(p₀))| ≤ C_n |e| max(Y, A_max)^{max(0,4-n)}`,
  obtained by the mean value inequality along the segment from the weighted jets `E_jets` of `∂_v V` (`FctHomotopyJets`);
* `ChartSetup.V_diff_jets`: the same for the chart of `FctChartSetup`.

The `ℓ`-derivative line (weights `3 - j`) and the comparison `A_λ ≍ A_0` are in `FctEJetsU`/`FctChartAcomp`; `(fct:dJ-jets)` is not formalised.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section VDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma path_mem_eventually {U : Set (P × ℝ)} (hU : IsOpen U) (p0 v : P) (Y t0 : ℝ) (h : (p0 + t0 • v, Y) ∈ U) :
    ∀ᶠ t in 𝓝 t0, (p0 + t • v, Y) ∈ U := by
  have hc : Continuous fun t : ℝ => (p0 + t • v, Y) := by fun_prop
  exact hc.continuousAt.eventually (hU.mem_nhds h)

/-- Differentiation in a parameter direction commutes with `∂_Y^n` (Schwarz). -/
theorem hasDerivAt_iteratedDeriv_path {U : Set (P × ℝ)} (hU : IsOpen U) (p0 v : P) (Y : ℝ) :
    ∀ (n : ℕ) (f : P × ℝ → ℝ), ContDiffOn ℝ (n + 2) f U → ∀ t0 : ℝ, (p0 + t0 • v, Y) ∈ U →
      HasDerivAt (fun t : ℝ => iteratedDeriv n (fun s => f (p0 + t • v, s)) Y)
        (iteratedDeriv n (fun s => fderiv ℝ f (p0 + t0 • v, s) (v, 0)) Y) t0 := by
  intro n
  induction n with
  | zero =>
    intro f hf t0 h0
    have hfa : DifferentiableAt ℝ f (p0 + t0 • v, Y) :=
      ((hf.contDiffAt (hU.mem_nhds h0)).differentiableAt (by norm_num))
    have hγ : HasDerivAt (fun t : ℝ => (p0 + t • v, Y)) (v, 0) t0 := by
      have h1 : HasDerivAt (fun t : ℝ => p0 + t • v) v t0 := by
        simpa using ((hasDerivAt_id t0).smul_const v).const_add p0
      exact h1.prodMk (hasDerivAt_const t0 Y)
    have := hfa.hasFDerivAt.comp_hasDerivAt t0 hγ
    simp only [iteratedDeriv_zero]
    exact this
  | succ n ih =>
    intro f hf t0 h0
    have hn3 : ((n + 1 : ℕ) : WithTop ℕ∞) + 2 = ((n + 3 : ℕ) : WithTop ℕ∞) := by norm_cast
    rw [hn3] at hf
    have hfd : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) U :=
      hf.fderiv_of_isOpen hU (by norm_cast)
    have hf' : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) (fun q => fderiv ℝ f q (0, 1)) U := by
      have := hfd.clm_apply (contDiffOn_const (c := ((0 : P), (1 : ℝ))))
      have e : ((n + 2 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 2 := by norm_cast
      rw [e] at this
      exact this
    have key := ih _ hf' t0 h0
    -- differentiability facts
    have hca : ∀ q ∈ U, ContDiffAt ℝ ((n + 3 : ℕ) : WithTop ℕ∞) f q := fun q hq => hf.contDiffAt (hU.mem_nhds hq)
    have hdf : ∀ q ∈ U, DifferentiableAt ℝ (fderiv ℝ f) q := fun q hq =>
      ((hca q hq).fderiv_right (m := 1) (by norm_cast; omega)).differentiableAt (by norm_num)
    have hfa : ∀ q ∈ U, DifferentiableAt ℝ f q := fun q hq => (hca q hq).differentiableAt (by norm_cast)
    -- derivative in `s` of `f (p, s)`
    have hds : ∀ (p : P) (s : ℝ), (p, s) ∈ U → deriv (fun u => f (p, u)) s = fderiv ℝ f (p, s) (0, 1) := by
      intro p s hs
      have hγ : HasDerivAt (fun u : ℝ => (p, u)) ((0 : P), (1 : ℝ)) s := (hasDerivAt_const s p).prodMk (hasDerivAt_id s)
      exact ((hfa _ hs).hasFDerivAt.comp_hasDerivAt s hγ).deriv
    have hmem_s : ∀ (p : P) (s : ℝ), (p, s) ∈ U → ∀ᶠ u in 𝓝 s, (p, u) ∈ U := by
      intro p s hs
      have hc : Continuous fun u : ℝ => (p, u) := by fun_prop
      exact hc.continuousAt.eventually (hU.mem_nhds hs)
    -- Step A: the function being differentiated agrees with the `f'` version near `t0`
    have hA : ∀ᶠ t in 𝓝 t0, iteratedDeriv (n + 1) (fun s => f (p0 + t • v, s)) Y =
        iteratedDeriv n (fun s => fderiv ℝ f (p0 + t • v, s) (0, 1)) Y := by
      filter_upwards [path_mem_eventually hU p0 v Y t0 h0] with t ht
      rw [iteratedDeriv_succ']
      refine Filter.EventuallyEq.iteratedDeriv_eq n ?_
      filter_upwards [hmem_s _ _ ht] with s hs
      exact hds _ _ hs
    -- Step B: the value of the derivative, via Schwarz symmetry
    have hB : iteratedDeriv n (fun s => fderiv ℝ (fun q => fderiv ℝ f q (0, 1)) (p0 + t0 • v, s) (v, 0)) Y =
        iteratedDeriv (n + 1) (fun s => fderiv ℝ f (p0 + t0 • v, s) (v, 0)) Y := by
      rw [iteratedDeriv_succ']
      refine Filter.EventuallyEq.iteratedDeriv_eq n ?_
      filter_upwards [hmem_s _ _ h0] with s hs
      have hs' : (p0 + t0 • v, s) ∈ U := hs
      have hD := hdf _ hs'
      have hsymm : fderiv ℝ (fderiv ℝ f) (p0 + t0 • v, s) (v, 0) (0, 1) = fderiv ℝ (fderiv ℝ f) (p0 + t0 • v, s) (0, 1) (v, 0) :=
        (ContDiffAt.isSymmSndFDerivAt (hca _ hs') (by simp [minSmoothness_of_isRCLikeNormedField]; norm_cast; omega)) _ _
      have e1 : fderiv ℝ (fun q => fderiv ℝ f q (0, 1)) (p0 + t0 • v, s) (v, 0) =
          fderiv ℝ (fderiv ℝ f) (p0 + t0 • v, s) (v, 0) (0, 1) := by
        have h := (ContinuousLinearMap.apply ℝ ℝ ((0 : P), (1 : ℝ))).hasFDerivAt.comp _ hD.hasFDerivAt
        rw [show (fun q => fderiv ℝ f q ((0 : P), (1 : ℝ))) =
          (⇑(ContinuousLinearMap.apply ℝ ℝ ((0 : P), (1 : ℝ)))) ∘ fderiv ℝ f from rfl, h.fderiv]
        simp
      have e2 : deriv (fun u => fderiv ℝ f (p0 + t0 • v, u) (v, 0)) s =
          fderiv ℝ (fderiv ℝ f) (p0 + t0 • v, s) (0, 1) (v, 0) := by
        have hγ : HasDerivAt (fun u : ℝ => (p0 + t0 • v, u)) ((0 : P), (1 : ℝ)) s :=
          (hasDerivAt_const s _).prodMk (hasDerivAt_id s)
        have h1 := ((ContinuousLinearMap.apply ℝ ℝ ((v : P), (0 : ℝ))).hasFDerivAt.comp _ hD.hasFDerivAt).comp_hasDerivAt s hγ
        exact h1.deriv
      rw [e2, e1, hsymm]
    have := key.congr_of_eventuallyEq (hA.mono fun t ht => ht)
    rw [hB] at this
    exact this

/-- The one-variable weighted jets of `V(p₀ + v, ·) - V(p₀, ·)`: the λ-integral of the weighted jets `E_jets` of `∂_v V` along the segment,
`|∂_Y^n (V(p₀+v) - V(p₀))| ≤ C_n |e| max(Y, A_max)^{max(0,4-n)}` (`(fct:V-diff-jets)`, first line, one parameter direction). -/
theorem V_diff_jets_Y {Ω : Set P} (hΩ : IsOpen Ω) {β : ℝ} (hβ : 4 ≤ β) {V θ : P × ℝ → ℝ} {A : P → ℝ} (v : P) (e : ℝ)
    (hV : JCΦ 16 (Ω ×ˢ Yint) V β 0) (hA : JCΦ 16 Ω A β 0) (hθ : JCΦ 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) θ β 0)
    (hAY : ∀ p ∈ Ω, A p ∈ Yint) (hz : ∀ q ∈ Ω ×ˢ Yint, q.2 * V q ^ 2 ∈ Ioo (-1 : ℝ) 6)
    (hode : ∀ q ∈ Ω ×ˢ Yint, (A q.1 - q.2) * fderiv ℝ V q (v, 0) =
      e * (V q + 2 * q.2 * fderiv ℝ V q (0, 1)) *
        (A q.1 ^ 5 * V (q.1, A q.1) ^ 11 * θ (q.1, A q.1 * V (q.1, A q.1) ^ 2) -
          q.2 ^ 5 * V q ^ 11 * θ (q.1, q.2 * V q ^ 2)))
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 14) :
    |iteratedDeriv n (fun s : ℝ => V (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => V (p0, s)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max Y Amax ^ (4 - n)) := by
  have hO : IsOpen (Ω ×ˢ Yint) := hΩ.prod isOpen_Ioo
  have hV2 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 2) V (Ω ×ˢ Yint) :=
    hV.1.of_le (by norm_cast; omega)
  set g : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => V (p0 + t • v, s)) Y with hg
  set g' : ℝ → ℝ := fun t => iteratedDeriv n (fun s : ℝ => fderiv ℝ V (p0 + t • v, s) (v, 0)) Y with hg'
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (0 : ℝ) 1) t := fun t ht =>
    (hasDerivAt_iteratedDeriv_path hO p0 v Y n V hV2 t ⟨hseg t ht, hY⟩).hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤
      |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] β) * max Y Amax ^ (4 - n)) := by
    intro t ht
    have h := E_jets hΩ hβ v e hV hA hθ hAY hz hode (hseg t ht) hY hY0 (hA0 t ht) (n := n) (by omega)
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hΦ : 0 ≤ Φb^[8] β := by
      have := Φb_iter_ge 8 β
      linarith
    have hmx : max Y (A (p0 + t • v)) ≤ max Y Amax := max_le_max le_rfl (hAm t ht)
    have h0 : 0 ≤ max Y (A (p0 + t • v)) := le_trans hY0 (le_max_left _ _)
    gcongr
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one)
  simpa [hg, one_smul, zero_smul, add_zero] using this



namespace ChartSetup
variable (S : ChartSetup P)

/-- `(fct:V-diff-jets)`, first line, for the chart: the segment `p₀ + t v` (`0 ≤ t ≤ 1`) lies in the chart domain, `A ≥ 0` on it and
`A ≤ A_max`, and `∂_v ψ = e z⁵ θ` (`ChartSetup.hode`). -/
theorem V_diff_jets {β : ℝ} (hβ : 4 ≤ β) (v : P) (θ : P × ℝ → ℝ) (e : ℝ)
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ S.Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, S.A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 14) :
    |iteratedDeriv n (fun s : ℝ => S.V (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => S.V (p0, s)) Y| ≤
      |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] (Φb^[3] β)) * max Y Amax ^ (4 - n)) := by
  have hβ3 : 4 ≤ Φb^[3] β := le_trans hβ (Φb_iter_ge 3 β)
  have hV : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 := by
    have := (S.V_jc hβ).mono_m (show 1 ≤ 3 by norm_num)
    simpa [JCΦ] using this
  have hA : JCΦ 16 S.Ω S.A (Φb^[3] β) 0 := by simpa [JCΦ] using S.A_jc hβ
  exact V_diff_jets_Y S.hΩ hβ3 v e hV hA hθ (fun p hp => S.A_mem hp) (fun q hq => S.hz hq) (S.hode v θ e hψ)
    hseg hA0 hAm hY hY0 hn

end ChartSetup

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_iteratedDeriv_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_iteratedDeriv_path

/-- info: 'FormalResearch.SignUncertainty.V_diff_jets_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms V_diff_jets_Y

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.V_diff_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.V_diff_jets

end VDiff
end FormalResearch.SignUncertainty

module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeEdge
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivative
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry

/-!
# Paper J, Layer 2: the soft-edge values of `S_0'` (L2.E, `InvS0` edge values)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(i): `-S_0'(X_s^pm) = pi sqrt(2/(kappa_pm d_pm))` from `eq:cp-S0p` and the limit `eq:cp-edgelim`.

## Proved here

* `edge_limit_hi`, `edge_limit_lo`: under `(H1)--(H3)` and `G_0, B_0 in C^2`, `int_{u_-(X)}^{u_+(X)} T^{-1/2} du -> pi sqrt(2/(kappa_pm d_pm))` as `X -> X_s^+` from below, resp. `X -> X_s^-` from above, with
  `kappa_+ = -f_+''(u_c^+)`, `kappa_- = f_-''(u_c^-)`, `d_pm = 4 sqrt(E_0(u_c^pm))` (the upper edge is `ActionDerivativeEdge.edge_wrapper` for `(f_+, f_-)`; the lower edge is the same for `(-f_-, -f_+)` and `Y = -X`).
* `deriv_hi_of_limit`, `deriv_lo_of_limit`: a `C^1` function with `S0' = -I` inside the band and `I -> v` at an end has `S0' = -v` at that end.
* `invS0_edges`: the second and third conjuncts of `InvS0` (`TheoremA/EigenvalueStatements.lean`) for every `S` with `S_0` `C^1` on `[X_s^- - delta, X_s^+ + delta]` (`delta > 0`) that equals the action on the band
  (so for the `S` of `SmoothExt` and `ActionFormula`, any `M`).

## Differences from the paper

None in the statement.  The first conjunct of `InvS0` (`-S_0' >= 2 c_0` uniformly) is `BandSlope` (`CorEigenWindows.lean`) and is not reproved here.

## Not formalised

The assembly of the three conjuncts of `InvS0` for the `S` of `ThmAi` (needs `BandSlope` from the windows).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts HypMorse ActionDeriv

section Principal

variable {L g : ℝ} {G B : ℝ → ℝ}

/-- **The upper edge limit** `int_{u_-}^{u_+} T^{-1/2} du -> pi sqrt(2/(kappa_+ d_+))` as `X -> X_s^+`, `kappa_+ = -f_+''(u_c^+)`, `d_+ = 4 sqrt(E_0(u_c^+))`. -/
theorem edge_limit_hi (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B (Icc 0 L))
    {uc : ℝ} (hu0 : 0 < uc) (hu1 : uc < L) (hf : fPlus L G B uc = Xsp L G B) :
    Tendsto (fun X => ∫ u in (sInf (Icc 0 L ∩ {u | 0 ≤ Tfun L G B X u}))..(sSup (Icc 0 L ∩ {u | 0 ≤ Tfun L G B X u})),
        1 / Real.sqrt (Tfun L G B X u)) (𝓝[<] Xsp L G B)
      (𝓝 (Real.pi * Real.sqrt (2 / ((-deriv (deriv (fPlus L G B)) uc) * (4 * Real.sqrt (E0 L G uc)))))) := by
  obtain ⟨uc', hc1, hc2, hchar, hcurv⟩ := hyp.H3p
  have hucc : uc = uc' := (hchar uc ⟨hu0.le, hu1.le⟩).1 hf
  subst hucc
  have hG := hyp.G0_lb
  have hg := hyp.gstar_pos
  have hfc := fPlus_continuousOn hG2 hB2
  have hfmc := fMinus_continuousOn hG2 hB2
  have hdiff : fPlus L G B uc - fMinus L G B uc = 4 * Real.sqrt (E0 L G uc) := fPlus_sub_fMinus uc
  have hEp : 0 < E0 L G uc := E0_pos hG hg ⟨hu0, hu1⟩
  have hdpos : fMinus L G B uc < fPlus L G B uc := by
    have := Real.sqrt_pos.2 hEp
    linarith
  have hXlt : Xsm L G B < Xsp L G B := by
    have h1 := Xsm_le_fMinus hfmc (show uc ∈ Icc 0 L from ⟨hu0.le, hu1.le⟩)
    have h2 := fPlus_le_Xsp hfc (show uc ∈ Icc 0 L from ⟨hu0.le, hu1.le⟩)
    linarith
  have h := edge_wrapper (L := L) (f := fPlus L G B) (fm := fMinus L G B) (T := Tfun L G B) (uc := uc) (Xs := Xsp L G B)
    (fun X u hu => Tfun_eq hG hg hu X) (fun u _ => fMinus_le_fPlus u) hfc hfmc (fPlus_contDiffOn hG hg hG2 hB2) ⟨hu0, hu1⟩
    (fun u hu => fPlus_le_Xsp hfc hu) hf (fun u hu h => (hchar u hu).1 h) hcurv hdpos
    (ε0 := Xsp L G B - Xsm L G B) (by linarith) ?_
  · rw [hdiff] at h
    exact h
  · intro X hX1 hX2
    obtain ⟨a, b, ha0, hab, hbL, hset, hTa, hTb, -, -⟩ := hyp.H2 X (by linarith) hX2
    exact ⟨a, b, hab, hset, fun h => (hTa h).1, fun h => (hTb h).1⟩

/-- **The lower edge limit** `int_{u_-}^{u_+} T^{-1/2} du -> pi sqrt(2/(kappa_- d_-))` as `X -> X_s^-`, `kappa_- = f_-''(u_c^-)`, `d_- = 4 sqrt(E_0(u_c^-))` (the upper edge for `(f, f_m) = (-f_-, -f_+)`, `Y = -X`). -/
theorem edge_limit_lo (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B (Icc 0 L))
    {uc : ℝ} (hu0 : 0 < uc) (hu1 : uc < L) (hf : fMinus L G B uc = Xsm L G B) :
    Tendsto (fun X => ∫ u in (sInf (Icc 0 L ∩ {u | 0 ≤ Tfun L G B X u}))..(sSup (Icc 0 L ∩ {u | 0 ≤ Tfun L G B X u})),
        1 / Real.sqrt (Tfun L G B X u)) (𝓝[>] Xsm L G B)
      (𝓝 (Real.pi * Real.sqrt (2 / ((deriv (deriv (fMinus L G B)) uc) * (4 * Real.sqrt (E0 L G uc)))))) := by
  obtain ⟨uc', hc1, hc2, hchar, hcurv⟩ := hyp.H3m
  have hucc : uc = uc' := (hchar uc ⟨hu0.le, hu1.le⟩).1 hf
  subst hucc
  have hG := hyp.G0_lb
  have hg := hyp.gstar_pos
  have hfc := fPlus_continuousOn hG2 hB2
  have hfmc := fMinus_continuousOn hG2 hB2
  have hdiff : fPlus L G B uc - fMinus L G B uc = 4 * Real.sqrt (E0 L G uc) := fPlus_sub_fMinus uc
  have hEp : 0 < E0 L G uc := E0_pos hG hg ⟨hu0, hu1⟩
  have hdpos : fMinus L G B uc < fPlus L G B uc := by
    have := Real.sqrt_pos.2 hEp
    linarith
  have hXlt : Xsm L G B < Xsp L G B := by
    have h1 := Xsm_le_fMinus hfmc (show uc ∈ Icc 0 L from ⟨hu0.le, hu1.le⟩)
    have h2 := fPlus_le_Xsp hfc (show uc ∈ Icc 0 L from ⟨hu0.le, hu1.le⟩)
    linarith
  have e1 : deriv (fun u => -fMinus L G B u) = fun u => -deriv (fMinus L G B) u := by
    funext u; exact deriv.fun_neg
  have e2 : deriv (deriv (fun u => -fMinus L G B u)) uc = -deriv (deriv (fMinus L G B)) uc := by
    rw [e1]; exact deriv.fun_neg
  have h := edge_wrapper (L := L) (f := fun u => -fMinus L G B u) (fm := fun u => -fPlus L G B u)
    (T := fun Y u => Tfun L G B (-Y) u) (uc := uc) (Xs := -Xsm L G B)
    (fun Y u hu => by rw [Tfun_eq hG hg hu (-Y)]; ring) (fun u _ => by have := fMinus_le_fPlus (L := L) (G0 := G) (B0 := B) u; linarith)
    hfmc.neg hfc.neg (fMinus_contDiffOn hG hg hG2 hB2).neg ⟨hu0, hu1⟩
    (fun u hu => by have := Xsm_le_fMinus hfmc hu; linarith) (by rw [hf])
    (fun u hu h => (hchar u hu).1 (by linarith)) (by rw [e2]; linarith) (by linarith)
    (ε0 := Xsp L G B - Xsm L G B) (by linarith) ?_
  · have hval : (-deriv (deriv (fun u => -fMinus L G B u)) uc) * (-fMinus L G B uc - -fPlus L G B uc) =
        deriv (deriv (fMinus L G B)) uc * (4 * Real.sqrt (E0 L G uc)) := by
      rw [e2, ← hdiff]; ring
    rw [hval] at h
    have hneg : Tendsto (fun X : ℝ => -X) (𝓝[>] Xsm L G B) (𝓝[<] (-Xsm L G B)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with X hX
      exact neg_lt_neg hX
    refine (h.comp hneg).congr' (Eventually.of_forall fun X => ?_)
    simp only [Function.comp, neg_neg]
  · intro Y hY1 hY2
    obtain ⟨a, b, ha0, hab, hbL, hset, hTa, hTb, -, -⟩ := hyp.H2 (-Y) (by linarith) (by linarith)
    exact ⟨a, b, hab, hset, fun h => (hTa h).1, fun h => (hTb h).1⟩

end Principal

section Transfer

/-- `S0` is `C^1` across `[lo, hi]` with `S0' = -I` inside and `I -> v` at the right end: `S0'(hi) = -v`. -/
lemma deriv_hi_of_limit {S0 : ℝ → ℝ} {lo hi δ : ℝ} (hlohi : lo < hi) (hδ : 0 < δ)
    (hC : ContDiffOn ℝ 1 S0 (Icc (lo - δ) (hi + δ))) {I : ℝ → ℝ} (hI : ∀ X ∈ Ioo lo hi, HasDerivAt S0 (-I X) X) {v : ℝ}
    (hlim : Tendsto I (𝓝[<] hi) (𝓝 v)) : deriv S0 hi = -v := by
  have hO : IsOpen (Ioo (lo - δ) (hi + δ)) := isOpen_Ioo
  have hC' : ContDiffOn ℝ 1 S0 (Ioo (lo - δ) (hi + δ)) := hC.mono Ioo_subset_Icc_self
  have hd0 : ContDiffOn ℝ 0 (deriv S0) (Ioo (lo - δ) (hi + δ)) := hC'.deriv_of_isOpen hO (by norm_num)
  have hcont : ContinuousAt (deriv S0) hi := hd0.continuousOn.continuousAt (hO.mem_nhds ⟨by linarith, by linarith⟩)
  have h1 : Tendsto (deriv S0) (𝓝[<] hi) (𝓝 (deriv S0 hi)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun X => -I X) (𝓝[<] hi) (𝓝 (-v)) := hlim.neg
  have h3 : deriv S0 =ᶠ[𝓝[<] hi] fun X => -I X := by
    filter_upwards [Ioo_mem_nhdsLT hlohi] with X hX using (hI X hX).deriv
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-- The left-end analogue: `I -> v` as `X -> lo+` gives `S0'(lo) = -v`. -/
lemma deriv_lo_of_limit {S0 : ℝ → ℝ} {lo hi δ : ℝ} (hlohi : lo < hi) (hδ : 0 < δ)
    (hC : ContDiffOn ℝ 1 S0 (Icc (lo - δ) (hi + δ))) {I : ℝ → ℝ} (hI : ∀ X ∈ Ioo lo hi, HasDerivAt S0 (-I X) X) {v : ℝ}
    (hlim : Tendsto I (𝓝[>] lo) (𝓝 v)) : deriv S0 lo = -v := by
  have hO : IsOpen (Ioo (lo - δ) (hi + δ)) := isOpen_Ioo
  have hC' : ContDiffOn ℝ 1 S0 (Ioo (lo - δ) (hi + δ)) := hC.mono Ioo_subset_Icc_self
  have hd0 : ContDiffOn ℝ 0 (deriv S0) (Ioo (lo - δ) (hi + δ)) := hC'.deriv_of_isOpen hO (by norm_num)
  have hcont : ContinuousAt (deriv S0) lo := hd0.continuousOn.continuousAt (hO.mem_nhds ⟨by linarith, by linarith⟩)
  have h1 : Tendsto (deriv S0) (𝓝[>] lo) (𝓝 (deriv S0 lo)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun X => -I X) (𝓝[>] lo) (𝓝 (-v)) := hlim.neg
  have h3 : deriv S0 =ᶠ[𝓝[>] lo] fun X => -I X := by
    filter_upwards [Ioo_mem_nhdsGT hlohi] with X hX using (hI X hX).deriv
  exact tendsto_nhds_unique (h1.congr' h3) h2

end Transfer

section Family

variable {Par : Type*} [TopologicalSpace Par]

/-- **The soft-edge values of `S_0'`** (the paper's `eq:cp-edgelim`): for `S` with `S_0` `C^1` on `[X_s^- - delta, X_s^+ + delta]` (`delta > 0`) and equal to the action on the band,
`S_0'(X_s^+) = -pi sqrt(2/(kappa_+ d_+))` and `S_0'(X_s^-) = -pi sqrt(2/(kappa_- d_-))`. -/
theorem invS0_edges (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn : ℝ}
    (hδ : 0 < δ) (hS : SmoothExt F K M S δ Cn) (hA : ActionFormula F K S) :
    (∀ μ ∈ K, ∀ uc : ℝ, 0 < uc → uc < F.L → fPlus F.L (F.G 0 μ) (F.B 0 μ) uc = F.bandHi μ →
      deriv (S 0 μ) (F.bandHi μ) = -(Real.pi * Real.sqrt (2 / ((-deriv (deriv (fPlus F.L (F.G 0 μ) (F.B 0 μ))) uc) *
        (4 * Real.sqrt (E0 F.L (F.G 0 μ) uc)))))) ∧
    (∀ μ ∈ K, ∀ uc : ℝ, 0 < uc → uc < F.L → fMinus F.L (F.G 0 μ) (F.B 0 μ) uc = F.bandLo μ →
      deriv (S 0 μ) (F.bandLo μ) = -(Real.pi * Real.sqrt (2 / ((deriv (deriv (fMinus F.L (F.G 0 μ) (F.B 0 μ))) uc) *
        (4 * Real.sqrt (E0 F.L (F.G 0 μ) uc)))))) := by
  have key : ∀ μ ∈ K, F.bandLo μ < F.bandHi μ ∧ ContDiffOn ℝ 1 (S 0 μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) ∧
      ∀ X ∈ Ioo (F.bandLo μ) (F.bandHi μ), HasDerivAt (S 0 μ) (-∫ u in (F.uMinus μ X)..(F.uPlus μ X),
        1 / Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) X := by
    intro μ hμ
    obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
    obtain ⟨uc', hc1, hc2, hchar, hcurv⟩ := hyp.H3p
    have hG := hyp.G0_lb
    have hg := hyp.gstar_pos
    have hlt : F.bandLo μ < F.bandHi μ := by
      have hucI : uc' ∈ Icc 0 F.L := ⟨hc1.le, hc2.le⟩
      have h1 := Xsm_le_fMinus (fMinus_continuousOn hG2 hB2) hucI
      have h2 := fPlus_le_Xsp (fPlus_continuousOn hG2 hB2) hucI
      have h3 := fPlus_sub_fMinus (L := F.L) (G0 := F.G 0 μ) (B0 := F.B 0 μ) uc'
      have h4 := Real.sqrt_pos.2 (E0_pos hG hg ⟨hc1, hc2⟩)
      show Xsm _ _ _ < Xsp _ _ _
      linarith
    obtain ⟨hs, -⟩ := hS μ hμ 0 (Nat.zero_le _)
    refine ⟨hlt, hs.of_le (by exact_mod_cast Nat.le_add_left 1 M), fun X hX => ?_⟩
    exact deriv_S0_of_eq F K hH hD hμ hX (hA μ hμ)
  refine ⟨fun μ hμ uc hu0 hu1 hf => ?_, fun μ hμ uc hu0 hu1 hf => ?_⟩
  · obtain ⟨hlt, hC, hI⟩ := key μ hμ
    obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
    exact deriv_hi_of_limit hlt hδ hC hI (edge_limit_hi hyp hG2 hB2 hu0 hu1 hf)
  · obtain ⟨hlt, hC, hI⟩ := key μ hμ
    obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
    exact deriv_lo_of_limit hlt hδ hC hI (edge_limit_lo hyp hG2 hB2 hu0 hu1 hf)

end Family

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.edge_limit_hi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.edge_limit_hi

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.edge_limit_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.edge_limit_lo

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.invS0_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.invS0_edges

end FormalResearch.JacobiEigenvectors.TheoremA

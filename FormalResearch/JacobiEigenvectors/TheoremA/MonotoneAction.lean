module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements

/-!
# Paper J, Layer 2: strict monotonicity of the action `S_0` (L2.S1, the hypothesis `hmono` of `propThaCount`)

Source: Paper J `app_thmA.tex`, `lem:smo-bulkphase` (3) ("`Phi := S_0`, which is strictly decreasing with `|S_0'| ~ 1`"), `lem:tha-geom` (a).

## Proved here

* `intervalIntegrable_arccos_action`: the integrand `u -> arccos((X - B_0(u))/(2 sqrt E_0(u)))` of `S_0` is interval integrable on `[0, L]` (continuous on `(0, L)`, bounded by `pi`).
* `actionS0_strictAntiOn_Sym` (**the strict decrease of `S_0` on any set of energies with a non-degenerate allowed set**): for principal symbols with `(H1)`--`(H3)` of class `C^2`
  and a set `I` of energies with `u_-(X) < u_+(X)` for all `X in I`, `X -> int_0^L arccos(...)` is strictly decreasing on `I`.
  Proof (no derivative, no dominated convergence): the integrand is pointwise antitone in `X`; for `X < X'` in `I` it is strictly larger at `X` than at `X'` on `(u_-(X'), u_+(X'))`, where
  `T(.; X') > 0` (`HypMorse.geomBulk`), i.e. `|X' - B_0| < 2 sqrt E_0`, so the argument at `X'` lies in `(-1, 1)`; and `u_- < u_+` makes that interval non-degenerate.
  `u_-(X) < u_+(X)` puts `X` in the open band `(X_s^-, X_s^+)` (`mem_band_of_uMinus_lt_uPlus`: for `X >= X_s^+` the allowed set is contained in `{u_c^+}`, for `X <= X_s^-` in `{u_c^-}`),
  which is what `geomBulk` needs.
* `bulk_actionS0_strictAnti`: the statement `hmono` of `bulk_count` (`TheoremA/BulkWindows.lean`): for a bulk Weber chart `CL` (its `overlap_in_well` gives `u_- + sigma <= c' < c <= u_+ - sigma`) and the
  standing assumptions, `S_0^{(t)}` is strictly decreasing on `[Jlo, Jhi]` for every `mu in K`, `|t| <= t0`.

## Differences from the paper

The paper states `|S_0'| ~ 1` (`S_0' = -int T^{-1/2}`, a derivative statement that needs the collision charts at `u_- = 0`); only the strict decrease is used by `lem:tha-count`, and that is what is proved
(no quantitative derivative bound; none is used by the formalisation).

## Not formalised

`|S_0'| ~ 1`, the identity `S_0' = -int T^{-1/2}`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology MeasureTheory FormalResearch.JacobiEigenvectors.Setting

section Sym

variable {L g : ℝ} {G0 B0 : ℝ → ℝ}

/-- The integrand of the action. -/
def actInt (L : ℝ) (G0 B0 : ℝ → ℝ) (X u : ℝ) : ℝ := Real.arccos ((X - B0 u) / (2 * Real.sqrt (E0 L G0 u)))

lemma continuousOn_actInt (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (X : ℝ) : ContinuousOn (actInt L G0 B0 X) (Ioo 0 L) := by
  have hE : ContinuousOn (E0 L G0) (Icc 0 L) := (HypMorse.contDiffOn_E0 hG2).continuousOn
  have hs : ContinuousOn (fun u => 2 * Real.sqrt (E0 L G0 u)) (Ioo 0 L) :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn (hE.mono Ioo_subset_Icc_self))
  have hne : ∀ u ∈ Ioo 0 L, 2 * Real.sqrt (E0 L G0 u) ≠ 0 := by
    intro u hu
    have := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hu
    have := Real.sqrt_pos.mpr this
    positivity
  have ha : ContinuousOn (fun u => (X - B0 u) / (2 * Real.sqrt (E0 L G0 u))) (Ioo 0 L) :=
    (continuousOn_const.sub (hB2.continuousOn.mono Ioo_subset_Icc_self)).div hs hne
  exact Real.continuous_arccos.comp_continuousOn ha

lemma intervalIntegrable_arccos_action (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (X : ℝ) :
    IntervalIntegrable (actInt L G0 B0 X) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
  have hm : AEStronglyMeasurable (actInt L G0 B0 X) (volume.restrict (Ioc 0 L)) := by
    have h1 := (continuousOn_actInt hL hyp hG2 hB2 X).aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) := ⟨by simp⟩
  refine (integrable_const Real.pi).mono' hm (Filter.Eventually.of_forall fun u => ?_)
  have h0 : 0 ≤ actInt L G0 B0 X u := Real.arccos_nonneg _
  have h1 : actInt L G0 B0 X u ≤ Real.pi := Real.arccos_le_pi _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The integrand is antitone in the energy, everywhere. -/
lemma actInt_anti {X X' : ℝ} (h : X ≤ X') (u : ℝ) : actInt L G0 B0 X' u ≤ actInt L G0 B0 X u := by
  unfold actInt
  apply Real.arccos_le_arccos
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- For `u in (0, L)` with `T(u; X') > 0` and `X < X'`: strictly smaller integrand at `X'`. -/
lemma actInt_strict (hyp : Hyp L G0 B0 g) {X X' u : ℝ} (hXX : X < X') (hu : u ∈ Ioo 0 L)
    (hT : 0 < Tfun L G0 B0 X' u) : actInt L G0 B0 X' u < actInt L G0 B0 X u := by
  have hE := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hu
  have hs := Real.sqrt_pos.mpr hE
  have hsq := Real.sq_sqrt hE.le
  set s := Real.sqrt (E0 L G0 u) with hsdef
  have hTT : (X' - B0 u) ^ 2 < (2 * s) ^ 2 := by
    unfold Tfun at hT
    nlinarith [hsq]
  have h2 : |X' - B0 u| < 2 * s := by
    apply abs_lt_of_sq_lt_sq hTT (by positivity)
  have hb := abs_lt.mp h2
  unfold actInt
  have hden : 0 < 2 * s := by positivity
  set a2 := (X' - B0 u) / (2 * s) with ha2
  set a1 := (X - B0 u) / (2 * s) with ha1
  have h12 : a1 < a2 := div_lt_div_of_pos_right (by linarith) hden
  have ha2lt : a2 < 1 := by rw [ha2, div_lt_one hden]; linarith
  have ha2gt : -1 < a2 := by rw [ha2, lt_div_iff₀ hden]; linarith
  set a1' := max a1 (-1) with ha1'
  have hA : Real.arccos a1' = Real.arccos a1 := by
    rcases le_total a1 (-1) with h | h
    · rw [ha1', max_eq_right h, Real.arccos_of_le_neg_one h, Real.arccos_of_le_neg_one le_rfl]
    · rw [ha1', max_eq_left h]
  have hlt : a1' < a2 := max_lt h12 ha2gt
  rw [← hA]
  exact Real.arccos_lt_arccos (le_max_right _ _) hlt ha2lt.le

/-- `X >= X_s^+` or `X <= X_s^-` forces `u_+ - u_- <= 0`: the allowed set is a single point. -/
lemma mem_band_of_uMinus_lt_uPlus (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {X : ℝ} (h : uMinusS L G0 B0 X < uPlusS L G0 B0 X) :
    Xsm L G0 B0 < X ∧ X < Xsp L G0 B0 := by
  have hg := hyp.gstar_pos
  have hsub : ∀ x y, x ∈ allowedSet L G0 B0 X → y ∈ allowedSet L G0 B0 X → x = y → True := fun _ _ _ _ _ => trivial
  have key : ∀ S : Set ℝ, S.Subsingleton → sInf S = sSup S := by
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have : S = {x} := hS.eq_singleton_of_mem hx
      rw [this]; simp
  have hnotle : ¬ (uPlusS L G0 B0 X ≤ uMinusS L G0 B0 X) := not_le.mpr h
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    -- allowed set is `{u | f_- u ≤ X ≤ f_+ u}`; `X ≤ Xsm ≤ f_-`, so `f_- u = X = Xsm`
    obtain ⟨uc, -, -, huq, -⟩ := hyp.H3m
    apply hnotle
    refine le_of_eq (Eq.symm (key _ ?_))
    intro x hx y hy
    have hx' := (HypMorse.Tfun_nonneg_iff hyp.G0_lb hg hx.1 X).mp hx.2
    have hy' := (HypMorse.Tfun_nonneg_iff hyp.G0_lb hg hy.1 X).mp hy.2
    have hcont := HypMorse.fMinus_continuousOn hG2 hB2
    have hx1 := HypMorse.Xsm_le_fMinus hcont hx.1
    have hy1 := HypMorse.Xsm_le_fMinus hcont hy.1
    have ex : fMinus L G0 B0 x = Xsm L G0 B0 := by linarith [hx'.1]
    have ey : fMinus L G0 B0 y = Xsm L G0 B0 := by linarith [hy'.1]
    rw [(huq x hx.1).mp ex, (huq y hy.1).mp ey]
  · by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨uc, -, -, huq, -⟩ := hyp.H3p
    apply hnotle
    refine le_of_eq (Eq.symm (key _ ?_))
    intro x hx y hy
    have hx' := (HypMorse.Tfun_nonneg_iff hyp.G0_lb hg hx.1 X).mp hx.2
    have hy' := (HypMorse.Tfun_nonneg_iff hyp.G0_lb hg hy.1 X).mp hy.2
    have hcont := HypMorse.fPlus_continuousOn hG2 hB2
    have hx1 := HypMorse.fPlus_le_Xsp hcont hx.1
    have hy1 := HypMorse.fPlus_le_Xsp hcont hy.1
    have ex : fPlus L G0 B0 x = Xsp L G0 B0 := by linarith [hx'.2]
    have ey : fPlus L G0 B0 y = Xsp L G0 B0 := by linarith [hy'.2]
    rw [(huq x hx.1).mp ex, (huq y hy.1).mp ey]

/-- **Strict decrease of the action** (see the module docstring). -/
theorem actionS0_strictAntiOn_Sym (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {I : Set ℝ} (hI : ∀ X ∈ I, uMinusS L G0 B0 X < uPlusS L G0 B0 X) :
    StrictAntiOn (fun X => ∫ u in (0 : ℝ)..L, actInt L G0 B0 X u) I := by
  intro X hX X' hX' hXX
  have hw := hI X' hX'
  obtain ⟨hb1, hb2⟩ := mem_band_of_uMinus_lt_uPlus hL hyp hG2 hB2 hw
  have hgeo := HypMorse.geomBulk L G0 B0 g hL hyp hG2 hB2 X' hb1 hb2
  have hne : (allowedSet L G0 B0 X').Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : uMinusS L G0 B0 X' = uPlusS L G0 B0 X' := by
      unfold uMinusS uPlusS; rw [hemp]; simp
    linarith
  have hbdd : BddAbove (allowedSet L G0 B0 X') := ⟨L, fun x hx => hx.1.2⟩
  have hbdd' : BddBelow (allowedSet L G0 B0 X') := ⟨0, fun x hx => hx.1.1⟩
  have hum0 : 0 ≤ uMinusS L G0 B0 X' := le_csInf hne (fun x hx => hx.1.1)
  have hupL : uPlusS L G0 B0 X' ≤ L := csSup_le hne (fun x hx => hx.1.2)
  set a := uMinusS L G0 B0 X' with ha
  set b := uPlusS L G0 B0 X' with hb
  have hi1 := intervalIntegrable_arccos_action hL hyp hG2 hB2 X
  have hi2 := intervalIntegrable_arccos_action hL hyp hG2 hB2 X'
  have hd : IntervalIntegrable (fun u => actInt L G0 B0 X u - actInt L G0 B0 X' u) volume 0 L := hi1.sub hi2
  have hdnn : ∀ u, 0 ≤ actInt L G0 B0 X u - actInt L G0 B0 X' u := fun u => by
    have := actInt_anti (L := L) (G0 := G0) (B0 := B0) hXX.le u
    linarith
  have hmid : 0 < ∫ u in a..b, (actInt L G0 B0 X u - actInt L G0 B0 X' u) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hd.mono_set ?_) ?_ hw
    · rw [uIcc_of_le hL.le, uIcc_of_le hw.le]
      exact Icc_subset_Icc hum0 hupL
    · intro u hu
      have hu0 : u ∈ Ioo 0 L := ⟨lt_of_le_of_lt hum0 hu.1, lt_of_lt_of_le hu.2 hupL⟩
      have hT := (hgeo.2.1 u (Ioo_subset_Icc_self hu0)).mpr hu
      have := actInt_strict hyp hXX hu0 hT
      linarith
  have hle : (∫ u in a..b, (actInt L G0 B0 X u - actInt L G0 B0 X' u))
      ≤ ∫ u in (0 : ℝ)..L, (actInt L G0 B0 X u - actInt L G0 B0 X' u) :=
    intervalIntegral.integral_mono_interval hum0 hw.le hupL
      (Filter.Eventually.of_forall hdnn) hd
  have hsub := intervalIntegral.integral_sub hi1 hi2
  show (∫ u in (0 : ℝ)..L, actInt L G0 B0 X' u) < ∫ u in (0 : ℝ)..L, actInt L G0 B0 X u
  linarith

end Sym

section Chart

open FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ}
  {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **The hypothesis `hmono` of `bulk_count`**: `S_0^{(t)}` is strictly decreasing on the energy range of a bulk chart (`lem:smo-bulkphase` (3): "`Phi := S_0`, strictly decreasing"). -/
theorem bulk_actionS0_strictAnti (CL : BulkWeberChart F P Jlo Jhi m U V)
    (hP : ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0, (μ, t) ∈ P) {Kd r : ℕ} (hr : StdAssump F P Kd r) :
    ∀ μ ∈ K, ∀ t ∈ Icc (-t0) t0, StrictAntiOn (fun X => actionS0 F (μ, t) X) (Icc Jlo Jhi) := by
  intro μ hμ t ht
  have hp := hP μ hμ t ht
  obtain ⟨-, hEK, g, hg⟩ := hr
  have hbud : regBudget (max (2 * Kd - 1) 0) ≤ r := hEK.budget
  have hr2 : (2 : ℕ) ≤ r := le_trans (by unfold regBudget; omega) hbud
  have hG2 : ContDiffOn ℝ 2 (F.G 0 (μ, t)) (Icc 0 F.L) := by
    have := (hEK.reg 0 (Nat.zero_le _)).1.1 (μ, t) hp
    simp only [Nat.mul_zero, Nat.sub_zero] at this
    exact this.of_le (by exact_mod_cast hr2)
  have hB2 : ContDiffOn ℝ 2 (F.B 0 (μ, t)) (Icc 0 F.L) := by
    have := (hEK.reg 0 (Nat.zero_le _)).2.1 (μ, t) hp
    simp only [Nat.mul_zero, Nat.sub_zero] at this
    exact this.of_le (by exact_mod_cast hr2)
  have hI : ∀ X ∈ Icc Jlo Jhi, uMinusS F.L (F.G 0 (μ, t)) (F.B 0 (μ, t)) X < uPlusS F.L (F.G 0 (μ, t)) (F.B 0 (μ, t)) X := by
    intro X hX
    obtain ⟨-, -, hσ, -, -, -, -, -, -, -⟩ := CL.consts_pos
    obtain ⟨-, hcc', -, -, -, -, -, -, -, -⟩ := CL.consts_pos
    obtain ⟨h1, h2⟩ := CL.overlap_in_well (μ, t) hp X hX
    rw [uMinus_eq_uMinusS] at h1
    rw [uPlus_eq_uPlusS] at h2
    linarith
  exact actionS0_strictAntiOn_Sym F.L_pos (hg (μ, t) hp) hG2 hB2 hI

end Chart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_strictAntiOn_Sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_strictAntiOn_Sym

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_actionS0_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_actionS0_strictAnti

end FormalResearch.JacobiEigenvectors.TheoremA

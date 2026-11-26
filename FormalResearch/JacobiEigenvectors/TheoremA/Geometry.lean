module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.Count
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements

/-!
# Paper J, Layer 2 (L2.G1): the Morse form of the hypotheses (lem:hyp-morse)

Source: Paper J, `main_results.tex` (`sec:hypotheses`, (H1)--(H3)) and `lem:hyp-morse`, the Morse characterisation of (H2) and (H3).
The statement is `HypMorseEquiv` of `TheoremA/Statements.lean` (frozen).  This file proves it.

## Notation

`E = E0 L G0`, `fp = fPlus L G0 B0 = B0 + 2 sqrt E`, `fm = fMinus L G0 B0 = B0 - 2 sqrt E`, `T X u = 4 E u - (X - B0 u)^2`.
For `u` in `[0, L]`, `T X u = (fp u - X) (X - fm u)` (`T_eq`), so `T X u >= 0` iff `fm u <= X <= fp u` (`T_nonneg_iff`).

## Proof structure

* `Pp` / `Pm`: the first conjunct of the LHS of `HypMorseEquiv` for `fp` / `fm` (a unique critical point in `(0, L)` with the sign of `f''`).
* (M) => (A) and (B), (C): `Pp`, `Pm` give strict monotonicity of `fp` on `[0,uc]`, `[uc,L]` and of `fm` on `[0,q]`, `[q,L]`; the allowed
  set `{T >= 0}` is then a closed, order-connected, nonempty subset of `[0, L]`, hence `Icc a b`; the endpoint conditions follow from
  the derivatives (the endpoints are points where `fp = X` or `fm = X`, with `fp' != 0` resp. `fm' != 0`).
* (A) and (B) => `Pp`: the dips of `fp` at a level `X` would make the allowed set disconnected; a second critical point `c` of `fp` gives a
  level `X = fp c` whose left (resp. right) endpoint `a` of the allowed set has `deriv (T X) a = 0`, contradicting (A).  The minus side is the
  plus side for the data `(G0, -B0)` (`fPlus L G0 (-B0) = -fMinus L G0 B0`, `Tfun L G0 (-B0) X = Tfun L G0 B0 (-X)`).

## Differences from the paper

None in the statement.  `frozenStandard_of_reg` (finding F-S6-7, round 8): `sec:tha-standing` holds under the weaker hypothesis `FrozenReg` (the regularity `r >= regBudget (max (2 Kidx - 1) 0)` of the jets `2j, 2j+1`, `j <= Kidx`,
and the remainder after the jet `2 Kidx + 1`), which `DM F K (2 Kidx + 1)` implies (`frozenReg_of_dm`; `frozenStandard` is the corollary) and which the truncated family `tilde J_h^{[M]}` satisfies with only `(D_M)`.
(The paper's proof of lem:hyp-morse is not reproduced; the argument above is an independent one.)

## Not formalised

Nothing of `HypMorseEquiv`.  Openness (`HypOpen`, L2.G2), `FrozenStandard` (L2.G3) and `TheGeometry` (L2.G4) are not in this file yet.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

namespace HypMorse

variable {L g : ℝ} {G0 B0 : ℝ → ℝ}

/-! ### Pointwise facts -/

lemma E0_nonneg (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) {u : ℝ} (hu : u ∈ Icc 0 L) :
    0 ≤ E0 L G0 u := by
  unfold E0
  have h1 : 0 ≤ u := hu.1
  have h2 : 0 ≤ L - u := by linarith [hu.2]
  exact mul_nonneg (mul_nonneg h1 h2) (by linarith [hG u hu])

lemma E0_pos (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    0 < E0 L G0 u := by
  unfold E0
  have h2 : 0 < L - u := by linarith [hu.2]
  exact mul_pos (mul_pos hu.1 h2) (lt_of_lt_of_le hg (hG u (Ioo_subset_Icc_self hu)))

lemma fPlus_sub_fMinus (u : ℝ) :
    fPlus L G0 B0 u - fMinus L G0 B0 u = 4 * Real.sqrt (E0 L G0 u) := by
  unfold fPlus fMinus; ring

lemma fMinus_le_fPlus (u : ℝ) :
    fMinus L G0 B0 u ≤ fPlus L G0 B0 u := by
  have := fPlus_sub_fMinus (L := L) (G0 := G0) (B0 := B0) u
  have h0 : 0 ≤ Real.sqrt (E0 L G0 u) := Real.sqrt_nonneg _
  linarith

lemma Tfun_eq (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) {u : ℝ} (hu : u ∈ Icc 0 L) (X : ℝ) :
    Tfun L G0 B0 X u = (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u) := by
  have hs : Real.sqrt (E0 L G0 u) ^ 2 = E0 L G0 u := Real.sq_sqrt (E0_nonneg hG hg hu)
  unfold Tfun fPlus fMinus
  linear_combination (-4 : ℝ) * hs

lemma Tfun_nonneg_iff (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) {u : ℝ} (hu : u ∈ Icc 0 L) (X : ℝ) :
    0 ≤ Tfun L G0 B0 X u ↔ fMinus L G0 B0 u ≤ X ∧ X ≤ fPlus L G0 B0 u := by
  rw [Tfun_eq hG hg hu]
  have hle := fMinus_le_fPlus (L := L) (G0 := G0) (B0 := B0) u
  constructor
  · intro h
    constructor <;> by_contra hc <;> push Not at hc <;> nlinarith
  · rintro ⟨h1, h2⟩
    exact mul_nonneg (by linarith) (by linarith)

/-! ### Regularity on the open interval -/

lemma contDiffOn_E0 (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L)) :
    ContDiffOn ℝ 2 (E0 L G0) (Icc 0 L) := by
  unfold E0
  exact ((contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)).mul hG2)

lemma fPlus_contDiffOn (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) : ContDiffOn ℝ 2 (fPlus L G0 B0) (Ioo 0 L) := by
  have hsq : ContDiffOn ℝ 2 (fun u => Real.sqrt (E0 L G0 u)) (Ioo 0 L) := by
    intro u hu
    have hE : ContDiffAt ℝ 2 (E0 L G0) u :=
      (contDiffOn_E0 hG2).contDiffAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) Ioo_subset_Icc_self)
    exact (ContDiffAt.sqrt hE (ne_of_gt (E0_pos hG hg hu))).contDiffWithinAt
  have hB : ContDiffOn ℝ 2 B0 (Ioo 0 L) := hB2.mono Ioo_subset_Icc_self
  have : fPlus L G0 B0 = fun u => B0 u + 2 * Real.sqrt (E0 L G0 u) := rfl
  rw [this]
  exact hB.add (contDiffOn_const.mul hsq)

lemma fMinus_contDiffOn (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) : ContDiffOn ℝ 2 (fMinus L G0 B0) (Ioo 0 L) := by
  have hsq : ContDiffOn ℝ 2 (fun u => Real.sqrt (E0 L G0 u)) (Ioo 0 L) := by
    intro u hu
    have hE : ContDiffAt ℝ 2 (E0 L G0) u :=
      (contDiffOn_E0 hG2).contDiffAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu) Ioo_subset_Icc_self)
    exact (ContDiffAt.sqrt hE (ne_of_gt (E0_pos hG hg hu))).contDiffWithinAt
  have hB : ContDiffOn ℝ 2 B0 (Ioo 0 L) := hB2.mono Ioo_subset_Icc_self
  have : fMinus L G0 B0 = fun u => B0 u - 2 * Real.sqrt (E0 L G0 u) := rfl
  rw [this]
  exact hB.sub (contDiffOn_const.mul hsq)

lemma fPlus_hasDerivAt_of_mem (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt (fPlus L G0 B0) (deriv (fPlus L G0 B0) u) u :=
  ((fPlus_contDiffOn hG hg hG2 hB2).differentiableOn (by norm_num) u hu |>.differentiableAt
    (isOpen_Ioo.mem_nhds hu)).hasDerivAt

lemma fMinus_hasDerivAt_of_mem (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt (fMinus L G0 B0) (deriv (fMinus L G0 B0) u) u :=
  ((fMinus_contDiffOn hG hg hG2 hB2).differentiableOn (by norm_num) u hu |>.differentiableAt
    (isOpen_Ioo.mem_nhds hu)).hasDerivAt

lemma fPlus_continuousOn (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) : ContinuousOn (fPlus L G0 B0) (Icc 0 L) := by
  have hE : ContinuousOn (E0 L G0) (Icc 0 L) := (contDiffOn_E0 hG2).continuousOn
  have : fPlus L G0 B0 = fun u => B0 u + 2 * Real.sqrt (E0 L G0 u) := rfl
  rw [this]
  exact hB2.continuousOn.add (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hE))

lemma fMinus_continuousOn (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) : ContinuousOn (fMinus L G0 B0) (Icc 0 L) := by
  have hE : ContinuousOn (E0 L G0) (Icc 0 L) := (contDiffOn_E0 hG2).continuousOn
  have : fMinus L G0 B0 = fun u => B0 u - 2 * Real.sqrt (E0 L G0 u) := rfl
  rw [this]
  exact hB2.continuousOn.sub (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hE))

/-! ### The extreme values `Xsp`, `Xsm` -/

lemma fPlus_le_Xsp (hcont : ContinuousOn (fPlus L G0 B0) (Icc 0 L)) {u : ℝ} (hu : u ∈ Icc 0 L) :
    fPlus L G0 B0 u ≤ Xsp L G0 B0 :=
  le_csSup ((isCompact_Icc.image_of_continuousOn hcont).bddAbove) (mem_image_of_mem _ hu)

lemma Xsm_le_fMinus (hcont : ContinuousOn (fMinus L G0 B0) (Icc 0 L)) {u : ℝ} (hu : u ∈ Icc 0 L) :
    Xsm L G0 B0 ≤ fMinus L G0 B0 u :=
  csInf_le ((isCompact_Icc.image_of_continuousOn hcont).bddBelow) (mem_image_of_mem _ hu)

lemma exists_Xsp (hcont : ContinuousOn (fPlus L G0 B0) (Icc 0 L)) (hL : 0 < L) :
    ∃ p ∈ Icc 0 L, fPlus L G0 B0 p = Xsp L G0 B0 := by
  have hne : (fPlus L G0 B0 '' Icc 0 L).Nonempty := ⟨_, mem_image_of_mem _ (⟨le_rfl, hL.le⟩ : (0:ℝ) ∈ Icc 0 L)⟩
  have h : Xsp L G0 B0 ∈ fPlus L G0 B0 '' Icc 0 L := (isCompact_Icc.image_of_continuousOn hcont).sSup_mem hne
  obtain ⟨p, hp, hpe⟩ := h
  exact ⟨p, hp, hpe⟩

lemma exists_Xsm (hcont : ContinuousOn (fMinus L G0 B0) (Icc 0 L)) (hL : 0 < L) :
    ∃ q ∈ Icc 0 L, fMinus L G0 B0 q = Xsm L G0 B0 := by
  have hne : (fMinus L G0 B0 '' Icc 0 L).Nonempty := ⟨_, mem_image_of_mem _ (⟨le_rfl, hL.le⟩ : (0:ℝ) ∈ Icc 0 L)⟩
  have h : Xsm L G0 B0 ∈ fMinus L G0 B0 '' Icc 0 L := (isCompact_Icc.image_of_continuousOn hcont).sInf_mem hne
  obtain ⟨q, hq, hqe⟩ := h
  exact ⟨q, hq, hqe⟩

/-! ### Values at the endpoints -/

lemma E0_zero : E0 L G0 0 = 0 := by unfold E0; ring

lemma E0_L : E0 L G0 L = 0 := by unfold E0; ring

lemma fPlus_zero : fPlus L G0 B0 0 = B0 0 := by unfold fPlus; rw [E0_zero]; simp

lemma fMinus_zero : fMinus L G0 B0 0 = B0 0 := by unfold fMinus; rw [E0_zero]; simp

lemma fPlus_L : fPlus L G0 B0 L = B0 L := by unfold fPlus; rw [E0_L]; simp

lemma fMinus_L : fMinus L G0 B0 L = B0 L := by unfold fMinus; rw [E0_L]; simp

/-! ### Negation of the principal symbol: `fPlus (-B0) = -fMinus B0` -/

lemma fPlus_neg_B : fPlus L G0 (fun u => -B0 u) = fun u => -fMinus L G0 B0 u := by
  funext u; unfold fPlus fMinus; ring

lemma fMinus_neg_B : fMinus L G0 (fun u => -B0 u) = fun u => -fPlus L G0 B0 u := by
  funext u; unfold fPlus fMinus; ring

lemma Tfun_neg_B (X : ℝ) : Tfun L G0 (fun u => -B0 u) X = Tfun L G0 B0 (-X) := by
  funext u; unfold Tfun; ring

/-! ### The statements of the two sides, as named predicates (same text as `HypMorseEquiv`) -/

/-- (A): the allowed set is one interval `[a, b]` for every energy in the open band, with the endpoint conditions. -/
def AProp (L : ℝ) (G0 B0 : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, Xsm L G0 B0 < X → X < Xsp L G0 B0 →
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ L ∧ (Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u}) = Icc a b ∧
      (0 < a → deriv (Tfun L G0 B0 X) a ≠ 0) ∧ (b < L → deriv (Tfun L G0 B0 X) b ≠ 0) ∧
      (a = 0 → X = B0 0) ∧ (b = L → X = B0 L)

/-- (B) for `f_+`: the maximum of `f_+` on `[0, L]` is attained at a single interior point, with `f_+'' < 0` there. -/
def BpProp (L : ℝ) (G0 B0 : ℝ → ℝ) : Prop :=
  ∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Icc 0 L, fPlus L G0 B0 u = Xsp L G0 B0 ↔ u = uc) ∧
    deriv (deriv (fPlus L G0 B0)) uc < 0

/-- (C) for `f_-`: the minimum of `f_-` on `[0, L]` is attained at a single interior point, with `f_-'' > 0` there. -/
def BmProp (L : ℝ) (G0 B0 : ℝ → ℝ) : Prop :=
  ∃ uc, 0 < uc ∧ uc < L ∧ (∀ u ∈ Icc 0 L, fMinus L G0 B0 u = Xsm L G0 B0 ↔ u = uc) ∧
    0 < deriv (deriv (fMinus L G0 B0)) uc

/-- The Morse condition (M) for `f_+`: one critical point in `(0, L)`, with `f_+'' < 0` there. -/
def PpProp (L : ℝ) (G0 B0 : ℝ → ℝ) : Prop :=
  ∃ uc ∈ Ioo 0 L, {u ∈ Ioo 0 L | deriv (fPlus L G0 B0) u = 0} = {uc} ∧ deriv (deriv (fPlus L G0 B0)) uc < 0

/-- The Morse condition (M) for `f_-`: one critical point in `(0, L)`, with `f_-'' > 0` there. -/
def PmProp (L : ℝ) (G0 B0 : ℝ → ℝ) : Prop :=
  ∃ uc ∈ Ioo 0 L, {u ∈ Ioo 0 L | deriv (fMinus L G0 B0) u = 0} = {uc} ∧ 0 < deriv (deriv (fMinus L G0 B0)) uc

/-! ### Extreme values -/

lemma Xsp_eq_of_max {p : ℝ} (hp : p ∈ Icc 0 L) (hmax : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u ≤ fPlus L G0 B0 p) :
    Xsp L G0 B0 = fPlus L G0 B0 p :=
  IsGreatest.csSup_eq ⟨mem_image_of_mem _ hp, by rintro _ ⟨u, hu, rfl⟩; exact hmax u hu⟩

lemma Xsm_eq_of_min {q : ℝ} (hq : q ∈ Icc 0 L) (hmin : ∀ u ∈ Icc 0 L, fMinus L G0 B0 q ≤ fMinus L G0 B0 u) :
    Xsm L G0 B0 = fMinus L G0 B0 q :=
  IsLeast.csInf_eq ⟨mem_image_of_mem _ hq, by rintro _ ⟨u, hu, rfl⟩; exact hmin u hu⟩

lemma Xsm_neg_B (hcont : ContinuousOn (fPlus L G0 B0) (Icc 0 L)) {p : ℝ} (hp : p ∈ Icc 0 L)
    (hpe : fPlus L G0 B0 p = Xsp L G0 B0) :
    Xsm L G0 (fun u => -B0 u) = -Xsp L G0 B0 := by
  have hfn : ∀ u, fMinus L G0 (fun u => -B0 u) u = -fPlus L G0 B0 u := fun u => by
    rw [fMinus_neg_B]
  apply IsLeast.csInf_eq
  refine ⟨⟨p, hp, ?_⟩, ?_⟩
  · simp only [hfn, hpe]
  · rintro _ ⟨u, hu, rfl⟩
    rw [hfn]
    linarith [fPlus_le_Xsp hcont hu]

lemma Xsp_neg_B (hcont : ContinuousOn (fMinus L G0 B0) (Icc 0 L)) {q : ℝ} (hq : q ∈ Icc 0 L)
    (hqe : fMinus L G0 B0 q = Xsm L G0 B0) :
    Xsp L G0 (fun u => -B0 u) = -Xsm L G0 B0 := by
  have hfn : ∀ u, fPlus L G0 (fun u => -B0 u) u = -fMinus L G0 B0 u := fun u => by
    rw [fPlus_neg_B]
  apply IsGreatest.csSup_eq
  refine ⟨⟨q, hq, ?_⟩, ?_⟩
  · simp only [hfn, hqe]
  · rintro _ ⟨u, hu, rfl⟩
    rw [hfn]
    linarith [Xsm_le_fMinus hcont hu]

/-! ### Derivatives of the negated data -/

lemma deriv_fPlus_neg : deriv (fPlus L G0 (fun u => -B0 u)) = fun u => -deriv (fMinus L G0 B0) u := by
  rw [fPlus_neg_B]
  have e : (fun u => -fMinus L G0 B0 u) = -fMinus L G0 B0 := rfl
  rw [e, deriv.neg']

lemma deriv_deriv_fPlus_neg :
    deriv (deriv (fPlus L G0 (fun u => -B0 u))) = fun u => -deriv (deriv (fMinus L G0 B0)) u := by
  rw [deriv_fPlus_neg]
  have e : (fun u => -deriv (fMinus L G0 B0) u) = -deriv (fMinus L G0 B0) := rfl
  rw [e, deriv.neg']

/-- (A) is invariant under `B0 ↦ -B0` (with `X ↦ -X`). -/
lemma AProp_neg (hA : AProp L G0 B0) (hcontp : ContinuousOn (fPlus L G0 B0) (Icc 0 L))
    (hcontm : ContinuousOn (fMinus L G0 B0) (Icc 0 L)) {p q : ℝ} (hp : p ∈ Icc 0 L)
    (hpe : fPlus L G0 B0 p = Xsp L G0 B0) (hq : q ∈ Icc 0 L) (hqe : fMinus L G0 B0 q = Xsm L G0 B0) :
    AProp L G0 (fun u => -B0 u) := by
  intro X hX1 hX2
  rw [Xsm_neg_B hcontp hp hpe] at hX1
  rw [Xsp_neg_B hcontm hq hqe] at hX2
  obtain ⟨a, b, ha0, hab, hbL, hS, hda, hdb, ha0B, hbLB⟩ := hA (-X) (by linarith) (by linarith)
  refine ⟨a, b, ha0, hab, hbL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tfun_neg_B]; exact hS
  · rw [Tfun_neg_B]; exact hda
  · rw [Tfun_neg_B]; exact hdb
  · intro h; have := ha0B h; simp only; linarith
  · intro h; have := hbLB h; simp only; linarith

/-! ### Shape of a function with a unique critical point -/

/-- If `f` is `C^2` on `(0,L)` with a unique critical point `uc` there and `f''(uc) < 0`, then `f` is strictly increasing on
`[0, uc]` and strictly decreasing on `[uc, L]`. -/
lemma shape_of_crit {f : ℝ → ℝ} {uc : ℝ} (huc : uc ∈ Ioo 0 L) (hcont : ContinuousOn f (Icc 0 L))
    (hC : ContDiffOn ℝ 2 f (Ioo 0 L)) (hcrit : ∀ u ∈ Ioo 0 L, deriv f u = 0 ↔ u = uc)
    (hneg : deriv (deriv f) uc < 0) :
    StrictMonoOn f (Icc 0 uc) ∧ StrictAntiOn f (Icc uc L) := by
  have hL0 : 0 < uc := huc.1
  have hucL : uc < L := huc.2
  have hcontd : ContinuousOn (deriv f) (Ioo 0 L) := hC.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv f) uc := by
    by_contra h
    have := deriv_zero_of_not_differentiableAt h
    linarith
  have h0 : deriv f uc = 0 := (hcrit uc huc).2 rfl
  obtain ⟨δ, hδ, hright, hleft⟩ :=
    count_local_sign (f := fun x => -deriv f x) (f' := -deriv (deriv f) uc) hdd.hasDerivAt.neg
      (by simp [h0]) (by linarith)
  have hposL : ∀ v ∈ Ioo 0 uc, 0 < deriv f v := by
    intro v hv
    by_contra hnot
    have hnot' : deriv f v ≤ 0 := not_lt.1 hnot
    set w := max (uc - δ / 2) ((v + uc) / 2) with hw
    have hw1 : uc - δ < w := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hw2 : w < uc := max_lt (by linarith) (by linarith [hv.2])
    have hvw : v < w := lt_of_lt_of_le (by linarith [hv.2]) (le_max_right _ _)
    have hpw : 0 < deriv f w := by
      have := hleft w hw1 hw2
      have h' : -deriv f w < 0 := this
      linarith
    have hsub : Icc v w ⊆ Ioo 0 L := fun t ht =>
      ⟨lt_of_lt_of_le hv.1 ht.1, lt_of_le_of_lt ht.2 (lt_trans hw2 hucL)⟩
    have hcIVT : ContinuousOn (deriv f) (Icc v w) := hcontd.mono hsub
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hvw.le hcIVT ⟨hnot', hpw.le⟩
    have hceq : c = uc := (hcrit c (hsub hc)).1 hc0
    linarith [hc.2]
  have hnegR : ∀ v ∈ Ioo uc L, deriv f v < 0 := by
    intro v hv
    by_contra hnot
    have hnot' : 0 ≤ deriv f v := not_lt.1 hnot
    set w := min (uc + δ / 2) ((uc + v) / 2) with hw
    have hw1 : uc < w := lt_min (by linarith) (by linarith [hv.1])
    have hw2 : w < uc + δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hwv : w < v := lt_of_le_of_lt (min_le_right _ _) (by linarith [hv.1])
    have hnw : deriv f w < 0 := by
      have := hright w hw1 hw2
      have h' : 0 < -deriv f w := this
      linarith
    have hsub : Icc w v ⊆ Ioo 0 L := fun t ht =>
      ⟨lt_trans hL0 (lt_of_lt_of_le hw1 ht.1), lt_of_le_of_lt ht.2 hv.2⟩
    have hcIVT : ContinuousOn (deriv f) (Icc w v) := hcontd.mono hsub
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hwv.le hcIVT ⟨hnw.le, hnot'⟩
    have hceq : c = uc := (hcrit c (hsub hc)).1 hc0
    linarith [hc.1]
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 uc)
    · exact hcont.mono (Icc_subset_Icc le_rfl hucL.le)
    · intro x hx
      rw [interior_Icc] at hx
      exact hposL x hx
  · apply strictAntiOn_of_deriv_neg (convex_Icc uc L)
    · exact hcont.mono (Icc_subset_Icc hL0.le le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      exact hnegR x hx

/-! ### The estimates at the two ends (used for the converse) -/

/-- Near `0`: `f_+(u) > f_+(0)` for small `u > 0`. -/
lemma fPlus_gt_near_zero (hL : 0 < L) (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g)
    (hB1 : ContDiffOn ℝ 1 B0 (Icc 0 L)) :
    ∃ δ > 0, ∀ u ∈ Ioo 0 δ, fPlus L G0 B0 0 < fPlus L G0 B0 u := by
  obtain ⟨K, hK⟩ := hB1.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 L) isCompact_Icc
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hLip : ∀ u ∈ Icc 0 L, |B0 u - B0 0| ≤ K' * u := by
    intro u hu
    have h1 := hK.dist_le_mul u hu 0 ⟨le_rfl, hL.le⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hu.1] at h1
    have h3 : 0 ≤ u := hu.1
    nlinarith [abs_nonneg (B0 u - B0 0), K.2]
  refine ⟨min (L / 2) (2 * L * g / K' ^ 2), lt_min (by linarith) (by positivity), fun u hu => ?_⟩
  have hu1 : u < L / 2 := lt_of_lt_of_le hu.2 (min_le_left _ _)
  have hu2 : u < 2 * L * g / K' ^ 2 := lt_of_lt_of_le hu.2 (min_le_right _ _)
  have hu0 := hu.1
  have hIcc : u ∈ Icc 0 L := ⟨hu0.le, by linarith⟩
  have hK2 : K' ^ 2 * u < 2 * L * g := by
    rw [lt_div_iff₀ (by positivity)] at hu2
    linarith
  have hEb : L * g * u / 2 ≤ E0 L G0 u := by
    unfold E0
    have h1 : 0 ≤ u * (L - u) := mul_nonneg hu0.le (by linarith)
    have h2 : 0 ≤ u * (L - u) * (G0 u - g) := mul_nonneg h1 (by linarith [hG u hIcc])
    have h4 : 0 ≤ u * g * (L / 2 - u) := mul_nonneg (mul_nonneg hu0.le hg.le) (by linarith)
    nlinarith [h2, h4]
  have hnn : 0 ≤ L * g * u / 2 := by
    have := mul_pos (mul_pos hL hg) hu0
    linarith
  have hs : Real.sqrt (E0 L G0 u) ^ 2 = E0 L G0 u := Real.sq_sqrt (le_trans hnn hEb)
  have hs0 : 0 ≤ Real.sqrt (E0 L G0 u) := Real.sqrt_nonneg _
  have hKu : K' * u < 2 * Real.sqrt (E0 L G0 u) := by
    have hsq : (K' * u) ^ 2 < (2 * Real.sqrt (E0 L G0 u)) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (K' * u - 2 * Real.sqrt (E0 L G0 u)), mul_nonneg hK'pos.le hu0.le]
  rw [fPlus_zero]
  unfold fPlus
  have := hLip u hIcc
  have := (abs_le.1 this).1
  linarith

/-- Near `L`: `f_+(u) > f_+(L)` for `u` close to `L`. -/
lemma fPlus_gt_near_L (hL : 0 < L) (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g)
    (hB1 : ContDiffOn ℝ 1 B0 (Icc 0 L)) :
    ∃ δ > 0, ∀ u ∈ Ioo (L - δ) L, fPlus L G0 B0 u > fPlus L G0 B0 L := by
  obtain ⟨K, hK⟩ := hB1.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 L) isCompact_Icc
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  have hLip : ∀ u ∈ Icc 0 L, |B0 u - B0 L| ≤ K' * (L - u) := by
    intro u hu
    have h1 := hK.dist_le_mul u hu L ⟨hL.le, le_rfl⟩
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hu.2] : u - L ≤ 0)] at h1
    have h3 : 0 ≤ L - u := by linarith [hu.2]
    nlinarith [abs_nonneg (B0 u - B0 L), K.2]
  refine ⟨min (L / 2) (2 * L * g / K' ^ 2), lt_min (by linarith) (by positivity), fun u hu => ?_⟩
  have hδ1 : min (L / 2) (2 * L * g / K' ^ 2) ≤ L / 2 := min_le_left _ _
  have hδ2 : min (L / 2) (2 * L * g / K' ^ 2) ≤ 2 * L * g / K' ^ 2 := min_le_right _ _
  have hu1 : L / 2 < u := by linarith [hu.1]
  have hu2' : L - u < 2 * L * g / K' ^ 2 := by linarith [hu.1]
  have hu0 : 0 < L - u := by linarith [hu.2]
  have hIcc : u ∈ Icc 0 L := ⟨by linarith, hu.2.le⟩
  have hK2 : K' ^ 2 * (L - u) < 2 * L * g := by
    rw [lt_div_iff₀ (by positivity)] at hu2'
    linarith
  have hEb : L * g * (L - u) / 2 ≤ E0 L G0 u := by
    unfold E0
    have h3 := hG u hIcc
    have h1 : 0 ≤ u * (L - u) := mul_nonneg (by linarith) hu0.le
    have h2 : 0 ≤ u * (L - u) * (G0 u - g) := mul_nonneg h1 (by linarith [h3])
    have h4 : 0 ≤ (u - L / 2) * ((L - u) * g) := mul_nonneg (by linarith) (mul_nonneg hu0.le hg.le)
    nlinarith [h2, h4]
  have hnn : 0 ≤ L * g * (L - u) / 2 := by
    have := mul_pos (mul_pos hL hg) hu0
    linarith
  have hs : Real.sqrt (E0 L G0 u) ^ 2 = E0 L G0 u := Real.sq_sqrt (le_trans hnn hEb)
  have hs0 : 0 ≤ Real.sqrt (E0 L G0 u) := Real.sqrt_nonneg _
  have hKu : K' * (L - u) < 2 * Real.sqrt (E0 L G0 u) := by
    have hsq : (K' * (L - u)) ^ 2 < (2 * Real.sqrt (E0 L G0 u)) ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_right hK2 hu0]
    nlinarith [sq_nonneg (K' * (L - u) - 2 * Real.sqrt (E0 L G0 u)), mul_nonneg hK'pos.le hu0.le]
  rw [fPlus_L]
  unfold fPlus
  have := (abs_le.1 (hLip u hIcc)).1
  linarith

/-! ### (M) implies (A) -/

lemma cont_lower_nbhd {f : ℝ → ℝ} {s : Set ℝ} {a c : ℝ} (hf : ContinuousOn f s) (ha : a ∈ s) (hc : c < f a) :
    ∃ δ > 0, ∀ u ∈ s, |u - a| < δ → c < f u := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hf a ha) (f a - c) (by linarith)
  refine ⟨δ, hδ, fun u hu hua => ?_⟩
  have h := hball hu (by rw [Real.dist_eq]; exact hua)
  rw [Real.dist_eq, abs_lt] at h
  linarith [h.1]

lemma cont_upper_nbhd {f : ℝ → ℝ} {s : Set ℝ} {a c : ℝ} (hf : ContinuousOn f s) (ha : a ∈ s) (hc : f a < c) :
    ∃ δ > 0, ∀ u ∈ s, |u - a| < δ → f u < c := by
  obtain ⟨δ, hδ, h⟩ := cont_lower_nbhd (f := fun u => -f u) hf.neg ha (by linarith : -c < -f a)
  exact ⟨δ, hδ, fun u hu hua => by have h' : -c < -f u := h u hu hua; linarith⟩

/-- At a point `c` of `(0, L)` where `f_+ = X` or `f_- = X` (with `X` in the band), `T(.;X)` has a nonzero derivative. -/
lemma Tfun_deriv_ne_zero (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L))
    {uc q : ℝ} (hcritp : ∀ a ∈ Ioo 0 L, deriv (fPlus L G0 B0) a = 0 → a = uc)
    (hcritm : ∀ a ∈ Ioo 0 L, deriv (fMinus L G0 B0) a = 0 → a = q)
    {X : ℝ} (hXm : Xsm L G0 B0 < X) (hXp : X < Xsp L G0 B0) (huc : fPlus L G0 B0 uc = Xsp L G0 B0)
    (hqe : fMinus L G0 B0 q = Xsm L G0 B0) {c : ℝ} (hc : c ∈ Ioo 0 L)
    (hcX : fPlus L G0 B0 c = X ∨ fMinus L G0 B0 c = X) :
    deriv (Tfun L G0 B0 X) c ≠ 0 := by
  have hfpd := fPlus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hfmd := fMinus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hprod : HasDerivAt (fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u))
      (deriv (fPlus L G0 B0) c * (X - fMinus L G0 B0 c) + (fPlus L G0 B0 c - X) * (0 - deriv (fMinus L G0 B0) c)) c :=
    (hfpd.sub_const X).mul ((hasDerivAt_const c X).sub hfmd)
  have heq : Tfun L G0 B0 X =ᶠ[𝓝 c] fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hc) (fun u hu => Tfun_eq hG hg (Ioo_subset_Icc_self hu) X)
  have hd := (hprod.congr_of_eventuallyEq heq).deriv
  rw [hd]
  have hpos := E0_pos hG hg hc
  have hsq : 0 < Real.sqrt (E0 L G0 c) := Real.sqrt_pos.2 hpos
  have hgap : fMinus L G0 B0 c < fPlus L G0 B0 c := by
    have := fPlus_sub_fMinus (L := L) (G0 := G0) (B0 := B0) c
    linarith
  rcases hcX with h | h
  · -- `f_+(c) = X`: the derivative is `f_+'(c) (X - f_-(c))`
    have hd1 : deriv (fPlus L G0 B0) c ≠ 0 := by
      intro h0
      have := hcritp c hc h0
      have hcu : c = uc := this
      rw [hcu, huc] at h
      linarith
    have hX : X - fMinus L G0 B0 c ≠ 0 := by
      intro h0
      linarith
    rw [h]
    simp only [sub_self, zero_mul, add_zero]
    exact mul_ne_zero hd1 hX
  · -- `f_-(c) = X`: the derivative is `-(f_+(c) - X) f_-'(c)`
    have hd2 : deriv (fMinus L G0 B0) c ≠ 0 := by
      intro h0
      have := hcritm c hc h0
      rw [this, hqe] at h
      -- `X = Xsm`, contradicting `Xsm < X`
      linarith
    have hX : fPlus L G0 B0 c - X ≠ 0 := by
      intro h0
      linarith
    rw [h]
    simp only [sub_self, mul_zero, zero_add]
    have : (0 : ℝ) - deriv (fMinus L G0 B0) c = -deriv (fMinus L G0 B0) c := by ring
    rw [this]
    exact mul_ne_zero hX (neg_ne_zero.2 hd2)

/-- (M) for `f_+`, `f_-` implies (A): the allowed set is an interval `[a, b]` with the endpoint conditions. -/
lemma A_of_shapes (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hL : 0 < L) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {uc q : ℝ} (huc : uc ∈ Ioo 0 L) (hq : q ∈ Ioo 0 L)
    (hpm1 : StrictMonoOn (fPlus L G0 B0) (Icc 0 uc)) (hpm2 : StrictAntiOn (fPlus L G0 B0) (Icc uc L))
    (hmm1 : StrictAntiOn (fMinus L G0 B0) (Icc 0 q)) (hmm2 : StrictMonoOn (fMinus L G0 B0) (Icc q L))
    (hXp : fPlus L G0 B0 uc = Xsp L G0 B0) (hXm : fMinus L G0 B0 q = Xsm L G0 B0)
    (hcritp : ∀ a ∈ Ioo 0 L, deriv (fPlus L G0 B0) a = 0 → a = uc)
    (hcritm : ∀ a ∈ Ioo 0 L, deriv (fMinus L G0 B0) a = 0 → a = q) :
    AProp L G0 B0 := by
  intro X hX1 hX2
  have hcontp := fPlus_continuousOn hG2 hB2
  have hcontm := fMinus_continuousOn hG2 hB2
  have memS : ∀ u, u ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} ↔
      u ∈ Icc 0 L ∧ fMinus L G0 B0 u ≤ X ∧ X ≤ fPlus L G0 B0 u := by
    intro u
    constructor
    · rintro ⟨hu, h⟩
      exact ⟨hu, ((Tfun_nonneg_iff hG hg hu X).1 h)⟩
    · rintro ⟨hu, h⟩
      exact ⟨hu, (Tfun_nonneg_iff hG hg hu X).2 h⟩
  set S : Set ℝ := Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} with hSdef
  have memS' : ∀ u, u ∈ S ↔ u ∈ Icc 0 L ∧ fMinus L G0 B0 u ≤ X ∧ X ≤ fPlus L G0 B0 u := memS
  have hq_mem : q ∈ Icc 0 L := ⟨hq.1.le, hq.2.le⟩
  have huc_mem : uc ∈ Icc 0 L := ⟨huc.1.le, huc.2.le⟩
  have hXpX : X < fPlus L G0 B0 uc := by rw [hXp]; exact hX2
  -- (1) the allowed set is nonempty
  have hne : S.Nonempty := by
    rcases le_total uc q with h | h
    · by_cases hfq : X ≤ fPlus L G0 B0 q
      · exact ⟨q, (memS' q).2 ⟨hq_mem, by rw [hXm]; exact hX1.le, hfq⟩⟩
      · push Not at hfq
        have hIVT := intermediate_value_uIcc (hcontp.mono (uIcc_subset_Icc huc_mem hq_mem))
          (show X ∈ Set.uIcc (fPlus L G0 B0 uc) (fPlus L G0 B0 q) from Set.mem_uIcc.2 (Or.inr ⟨hfq.le, hXpX.le⟩))
        obtain ⟨e, he, hfe⟩ := hIVT
        have heI : e ∈ Icc 0 L := uIcc_subset_Icc huc_mem hq_mem he
        have h1 := fMinus_le_fPlus (L := L) (G0 := G0) (B0 := B0) e
        exact ⟨e, (memS' e).2 ⟨heI, by linarith, by linarith⟩⟩
    · by_cases hfu : fMinus L G0 B0 uc ≤ X
      · exact ⟨uc, (memS' uc).2 ⟨huc_mem, hfu, hXpX.le⟩⟩
      · push Not at hfu
        have hIVT := intermediate_value_uIcc (hcontm.mono (uIcc_subset_Icc hq_mem huc_mem))
          (show X ∈ Set.uIcc (fMinus L G0 B0 q) (fMinus L G0 B0 uc) from
            Set.mem_uIcc.2 (Or.inl ⟨by rw [hXm]; exact hX1.le, hfu.le⟩))
        obtain ⟨e, he, hfe⟩ := hIVT
        have heI : e ∈ Icc 0 L := uIcc_subset_Icc hq_mem huc_mem he
        have h1 := fMinus_le_fPlus (L := L) (G0 := G0) (B0 := B0) e
        exact ⟨e, (memS' e).2 ⟨heI, by linarith, by linarith⟩⟩
  -- (2) closed and compact
  have hSclosed : IsClosed S := by
    have h1 : IsClosed (Icc 0 L ∩ fMinus L G0 B0 ⁻¹' Iic X) :=
      hcontm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have h2 : IsClosed (Icc 0 L ∩ fPlus L G0 B0 ⁻¹' Ici X) :=
      hcontp.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hEq : S = (Icc 0 L ∩ fMinus L G0 B0 ⁻¹' Iic X) ∩ (Icc 0 L ∩ fPlus L G0 B0 ⁻¹' Ici X) := by
      ext u
      rw [memS' u]
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici]
      tauto
    rw [hEq]
    exact h1.inter h2
  have hScpt : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed (fun u hu => hu.1)
  -- (3) order-connected: unimodality of `f_+` and `f_-`
  have hSoc : S.OrdConnected := by
    refine ⟨fun u hu w hw v hv => ?_⟩
    obtain ⟨hu0, hu1, hu2⟩ := (memS' u).1 hu
    obtain ⟨hw0, hw1, hw2⟩ := (memS' w).1 hw
    have hv0 : v ∈ Icc 0 L := ⟨le_trans hu0.1 hv.1, le_trans hv.2 hw0.2⟩
    refine (memS' v).2 ⟨hv0, ?_, ?_⟩
    · rcases le_total v q with hvq | hvq
      · have huq : u ∈ Icc 0 q := ⟨hu0.1, le_trans hv.1 hvq⟩
        have hvq' : v ∈ Icc 0 q := ⟨hv0.1, hvq⟩
        have := hmm1.antitoneOn huq hvq' hv.1
        linarith
      · have hvq' : v ∈ Icc q L := ⟨hvq, hv0.2⟩
        have hwq : w ∈ Icc q L := ⟨le_trans hvq hv.2, hw0.2⟩
        have := hmm2.monotoneOn hvq' hwq hv.2
        linarith
    · rcases le_total v uc with hvu | hvu
      · have huu : u ∈ Icc 0 uc := ⟨hu0.1, le_trans hv.1 hvu⟩
        have hvu' : v ∈ Icc 0 uc := ⟨hv0.1, hvu⟩
        have := hpm1.monotoneOn huu hvu' hv.1
        linarith
      · have hvuL : v ∈ Icc uc L := ⟨hvu, hv0.2⟩
        have hwuL : w ∈ Icc uc L := ⟨le_trans hvu hv.2, hw0.2⟩
        have := hpm2.antitoneOn hvuL hwuL hv.2
        linarith
  -- (4) the allowed set is `[sInf S, sSup S]`
  have ha_mem : sInf S ∈ S := hScpt.sInf_mem hne
  have hb_mem : sSup S ∈ S := hScpt.sSup_mem hne
  have hbdd := hScpt.bddBelow
  have hbdd' := hScpt.bddAbove
  have hSeq : S = Icc (sInf S) (sSup S) := by
    apply Set.Subset.antisymm
    · intro u hu
      exact ⟨csInf_le hbdd hu, le_csSup hbdd' hu⟩
    · exact hSoc.out ha_mem hb_mem
  have hab : sInf S ≤ sSup S := csInf_le hbdd hb_mem
  have ha0 : 0 ≤ sInf S := ((memS' _).1 ha_mem).1.1
  have hbL : sSup S ≤ L := ((memS' _).1 hb_mem).1.2
  have hout_left : ∀ u, u < sInf S → u ∉ S := fun u hu hmem => absurd (csInf_le hbdd hmem) (not_le.2 hu)
  have hout_right : ∀ u, sSup S < u → u ∉ S := fun u hu hmem => absurd (le_csSup hbdd' hmem) (not_le.2 hu)
  -- (5) `sInf S < L` (otherwise `X = B_0(L)` and points just left of `L` are allowed)
  have haL : sInf S < L := by
    by_contra hcon
    have haL' : sInf S = L := le_antisymm (((memS' _).1 ha_mem).1.2) (not_lt.1 hcon)
    have hbL' : sSup S = L := le_antisymm hbL (by linarith)
    have hLS : L ∈ S := by
      have := hb_mem
      rwa [hbL'] at this
    have hLm := (memS' L).1 hLS
    have hXL : X = B0 L := by
      have e1 := fMinus_L (L := L) (G0 := G0) (B0 := B0)
      have e2 := fPlus_L (L := L) (G0 := G0) (B0 := B0)
      linarith [hLm.2.1, hLm.2.2]
    have hm_lt : max uc q < L := max_lt huc.2 hq.2
    have hu_lt : (max uc q + L) / 2 < L := by linarith
    have hu_gt : max uc q < (max uc q + L) / 2 := by linarith
    have hu_mem : (max uc q + L) / 2 ∈ Icc 0 L :=
      ⟨by linarith [huc.1, le_max_left uc q], hu_lt.le⟩
    have hLu : fPlus L G0 B0 L < fPlus L G0 B0 ((max uc q + L) / 2) :=
      hpm2 ⟨by linarith [le_max_left uc q], hu_lt.le⟩ ⟨huc.2.le, le_rfl⟩ hu_lt
    have hLm' : fMinus L G0 B0 ((max uc q + L) / 2) < fMinus L G0 B0 L :=
      hmm2 ⟨by linarith [le_max_right uc q], hu_lt.le⟩ ⟨hq.2.le, le_rfl⟩ hu_lt
    have e1 := fMinus_L (L := L) (G0 := G0) (B0 := B0)
    have e2 := fPlus_L (L := L) (G0 := G0) (B0 := B0)
    have huS : (max uc q + L) / 2 ∈ S :=
      (memS' _).2 ⟨hu_mem, by linarith, by linarith⟩
    have := csInf_le hbdd huS
    linarith
  -- (6) `sSup S > 0`
  have hbpos : 0 < sSup S := by
    by_contra hcon
    have hb0 : sSup S = 0 := le_antisymm (not_lt.1 hcon) (le_trans ha0 hab)
    have ha0' : sInf S = 0 := le_antisymm (by linarith) ha0
    have h0S : (0 : ℝ) ∈ S := by
      have := ha_mem
      rwa [ha0'] at this
    have hX0 : X = B0 0 := by
      have hm := (memS' 0).1 h0S
      have e1 := fMinus_zero (L := L) (G0 := G0) (B0 := B0)
      have e2 := fPlus_zero (L := L) (G0 := G0) (B0 := B0)
      linarith [hm.2.1, hm.2.2]
    have hmu : 0 < min uc q / 2 := by
      have := lt_min huc.1 hq.1
      linarith
    have hmu1 : min uc q / 2 < uc := by linarith [min_le_left uc q, huc.1]
    have hmu2 : min uc q / 2 < q := by linarith [min_le_right uc q, hq.1]
    have hfu0 : fPlus L G0 B0 0 < fPlus L G0 B0 (min uc q / 2) :=
      hpm1 ⟨le_rfl, huc.1.le⟩ ⟨hmu.le, by linarith⟩ hmu
    have hfm0 : fMinus L G0 B0 (min uc q / 2) < fMinus L G0 B0 0 :=
      hmm1 ⟨le_rfl, hq.1.le⟩ ⟨hmu.le, by linarith⟩ hmu
    have e1 := fMinus_zero (L := L) (G0 := G0) (B0 := B0)
    have e2 := fPlus_zero (L := L) (G0 := G0) (B0 := B0)
    have huS : min uc q / 2 ∈ S :=
      (memS' _).2 ⟨⟨hmu.le, by linarith [huc.2, hq.2]⟩, by linarith, by linarith⟩
    have := le_csSup hbdd' huS
    linarith
  -- (7) at an endpoint in `(0, L)` the value of `f_+` or `f_-` is `X`
  have hA_a : 0 < sInf S → fPlus L G0 B0 (sInf S) = X ∨ fMinus L G0 B0 (sInf S) = X := by
    intro hpos
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hm := (memS' _).1 ha_mem
    have hlt1 : X < fPlus L G0 B0 (sInf S) := lt_of_le_of_ne hm.2.2 (Ne.symm h1)
    have hlt2 : fMinus L G0 B0 (sInf S) < X := lt_of_le_of_ne hm.2.1 h2
    have haI : sInf S ∈ Icc 0 L := hm.1
    obtain ⟨δ1, hδ1, hn1⟩ := cont_lower_nbhd hcontp haI hlt1
    obtain ⟨δ2, hδ2, hn2⟩ := cont_upper_nbhd hcontm haI hlt2
    have hmpos : 0 < min (min δ1 δ2 / 2) (sInf S / 2) :=
      lt_min (div_pos (lt_min hδ1 hδ2) two_pos) (div_pos hpos two_pos)
    have hm1 : min (min δ1 δ2 / 2) (sInf S / 2) ≤ min δ1 δ2 / 2 := min_le_left _ _
    have hm2 : min (min δ1 δ2 / 2) (sInf S / 2) ≤ sInf S / 2 := min_le_right _ _
    have hm3 : min δ1 δ2 ≤ δ1 := min_le_left _ _
    have hm4 : min δ1 δ2 ≤ δ2 := min_le_right _ _
    have huI : sInf S - min (min δ1 δ2 / 2) (sInf S / 2) ∈ Icc 0 L :=
      ⟨by linarith, by linarith [hm.1.2]⟩
    have hd1 : |sInf S - min (min δ1 δ2 / 2) (sInf S / 2) - sInf S| < δ1 := by
      rw [abs_lt]; constructor <;> linarith
    have hd2 : |sInf S - min (min δ1 δ2 / 2) (sInf S / 2) - sInf S| < δ2 := by
      rw [abs_lt]; constructor <;> linarith
    have huS : sInf S - min (min δ1 δ2 / 2) (sInf S / 2) ∈ S :=
      (memS' _).2 ⟨huI, le_of_lt (hn2 _ huI hd2), le_of_lt (hn1 _ huI hd1)⟩
    exact hout_left _ (by linarith) huS
  have hA_b : sSup S < L → fPlus L G0 B0 (sSup S) = X ∨ fMinus L G0 B0 (sSup S) = X := by
    intro hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hm := (memS' _).1 hb_mem
    have hlt1 : X < fPlus L G0 B0 (sSup S) := lt_of_le_of_ne hm.2.2 (Ne.symm h1)
    have hlt2 : fMinus L G0 B0 (sSup S) < X := lt_of_le_of_ne hm.2.1 h2
    have hbI : sSup S ∈ Icc 0 L := hm.1
    obtain ⟨δ1, hδ1, hn1⟩ := cont_lower_nbhd hcontp hbI hlt1
    obtain ⟨δ2, hδ2, hn2⟩ := cont_upper_nbhd hcontm hbI hlt2
    have hmpos : 0 < min (min δ1 δ2 / 2) ((L - sSup S) / 2) :=
      lt_min (div_pos (lt_min hδ1 hδ2) two_pos) (div_pos (by linarith) two_pos)
    have hm1 : min (min δ1 δ2 / 2) ((L - sSup S) / 2) ≤ min δ1 δ2 / 2 := min_le_left _ _
    have hm2 : min (min δ1 δ2 / 2) ((L - sSup S) / 2) ≤ (L - sSup S) / 2 := min_le_right _ _
    have hm3 : min δ1 δ2 ≤ δ1 := min_le_left _ _
    have hm4 : min δ1 δ2 ≤ δ2 := min_le_right _ _
    have huI : sSup S + min (min δ1 δ2 / 2) ((L - sSup S) / 2) ∈ Icc 0 L :=
      ⟨by linarith [hm.1.1], by linarith⟩
    have hd1 : |sSup S + min (min δ1 δ2 / 2) ((L - sSup S) / 2) - sSup S| < δ1 := by
      rw [abs_lt]; constructor <;> linarith
    have hd2 : |sSup S + min (min δ1 δ2 / 2) ((L - sSup S) / 2) - sSup S| < δ2 := by
      rw [abs_lt]; constructor <;> linarith
    have huS : sSup S + min (min δ1 δ2 / 2) ((L - sSup S) / 2) ∈ S :=
      (memS' _).2 ⟨huI, le_of_lt (hn2 _ huI hd2), le_of_lt (hn1 _ huI hd1)⟩
    exact hout_right _ (by linarith) huS
  -- (8) assemble
  refine ⟨sInf S, sSup S, ha0, hab, hbL, hSeq, ?_, ?_, ?_, ?_⟩
  · intro hpos
    exact Tfun_deriv_ne_zero hG hg hG2 hB2 hcritp hcritm hX1 hX2 hXp hXm
      ⟨hpos, haL⟩ (hA_a hpos)
  · intro hlt
    exact Tfun_deriv_ne_zero hG hg hG2 hB2 hcritp hcritm hX1 hX2 hXp hXm
      ⟨hbpos, hlt⟩ (hA_b hlt)
  · intro h0
    have hm := (memS' _).1 ha_mem
    rw [h0, fPlus_zero, fMinus_zero] at hm
    linarith [hm.2.1, hm.2.2]
  · intro hL'
    have hm := (memS' _).1 hb_mem
    rw [hL', fPlus_L, fMinus_L] at hm
    linarith [hm.2.1, hm.2.2]

/-- The derivative of `T(.;X)` at an interior point, in terms of `f_±` (`T = (f_+ - X)(X - f_-)` there). -/
lemma deriv_Tfun_eq (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (X : ℝ) {c : ℝ} (hc : c ∈ Ioo 0 L) :
    deriv (Tfun L G0 B0 X) c = deriv (fPlus L G0 B0) c * (X - fMinus L G0 B0 c) +
      (fPlus L G0 B0 c - X) * (0 - deriv (fMinus L G0 B0) c) := by
  have hfpd := fPlus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hfmd := fMinus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hprod : HasDerivAt (fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u))
      (deriv (fPlus L G0 B0) c * (X - fMinus L G0 B0 c) + (fPlus L G0 B0 c - X) * (0 - deriv (fMinus L G0 B0) c)) c :=
    (hfpd.sub_const X).mul ((hasDerivAt_const c X).sub hfmd)
  have heq : Tfun L G0 B0 X =ᶠ[𝓝 c] fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hc) (fun u hu => Tfun_eq hG hg (Ioo_subset_Icc_self hu) X)
  exact (hprod.congr_of_eventuallyEq heq).deriv

/-- A nonnegative-or-positive-sign estimate: between two points the sublevel is controlled (used for the converse). -/
lemma between_allowed (hA : AProp L G0 B0) (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) {X e₁ v e₂ : ℝ}
    (hX1 : Xsm L G0 B0 < X) (hX2 : X < Xsp L G0 B0) (he₁ : e₁ ∈ Icc 0 L) (he₂ : e₂ ∈ Icc 0 L)
    (h₁ : e₁ ≤ v) (h₂ : v ≤ e₂) (hv : v ∈ Icc 0 L)
    (hfe₁ : fMinus L G0 B0 e₁ ≤ X ∧ X ≤ fPlus L G0 B0 e₁) (hfe₂ : fMinus L G0 B0 e₂ ≤ X ∧ X ≤ fPlus L G0 B0 e₂) :
    fMinus L G0 B0 v ≤ X ∧ X ≤ fPlus L G0 B0 v := by
  obtain ⟨a, b, -, -, -, hS, -⟩ := hA X hX1 hX2
  have e1S : e₁ ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} := ⟨he₁, (Tfun_nonneg_iff hG hg he₁ X).2 hfe₁⟩
  have e2S : e₂ ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} := ⟨he₂, (Tfun_nonneg_iff hG hg he₂ X).2 hfe₂⟩
  rw [hS] at e1S e2S
  have hvS : v ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} := by
    rw [hS]
    exact ⟨by linarith [e1S.1], by linarith [e2S.2]⟩
  exact (Tfun_nonneg_iff hG hg hv X).1 hvS.2

/-- (A) and (B) for `f_+` imply (M) for `f_+`: `f_+` is unimodal, and its only critical point is `uc`. -/
lemma crit_of_A (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hL : 0 < L) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (hA : AProp L G0 B0) {uc : ℝ} (huc : uc ∈ Ioo 0 L)
    (hXp : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u = Xsp L G0 B0 ↔ u = uc)
    (hdeg : deriv (deriv (fPlus L G0 B0)) uc < 0) :
    ∃ uc' ∈ Ioo 0 L, {u ∈ Ioo 0 L | deriv (fPlus L G0 B0) u = 0} = {uc'} ∧
      deriv (deriv (fPlus L G0 B0)) uc' < 0 := by
  have hB1 : ContDiffOn ℝ 1 B0 (Icc 0 L) := hB2.of_le (by norm_num)
  have hcontp := fPlus_continuousOn hG2 hB2
  have hcontm := fMinus_continuousOn hG2 hB2
  have hucI : uc ∈ Icc 0 L := ⟨huc.1.le, huc.2.le⟩
  have hfp_uc : fPlus L G0 B0 uc = Xsp L G0 B0 := (hXp uc hucI).2 rfl
  have hle_Xsp : ∀ u ∈ Icc 0 L, fPlus L G0 B0 u ≤ Xsp L G0 B0 := fun u hu => fPlus_le_Xsp hcontp hu
  have hge_Xsm : ∀ u ∈ Icc 0 L, Xsm L G0 B0 ≤ fMinus L G0 B0 u := fun u hu => Xsm_le_fMinus hcontm hu
  have hfpm : ∀ u ∈ Icc 0 L, fMinus L G0 B0 u ≤ fPlus L G0 B0 u := fun u _ => fMinus_le_fPlus u
  -- (i) the dips: `f_+` is nondecreasing on `[0, uc]`
  have dipL : ∀ u v, 0 ≤ u → u ≤ v → v ≤ uc → fPlus L G0 B0 u ≤ fPlus L G0 B0 v := by
    intro u v hu0 huv hvuc
    by_contra hcon
    push Not at hcon
    have hvI : v ∈ Icc 0 L := ⟨le_trans hu0 huv, le_trans hvuc huc.2.le⟩
    have huI : u ∈ Icc 0 L := ⟨hu0, le_trans huv hvI.2⟩
    have hXlo : fPlus L G0 B0 v < (fPlus L G0 B0 u + fPlus L G0 B0 v) / 2 := by linarith
    have hXhi : (fPlus L G0 B0 u + fPlus L G0 B0 v) / 2 < fPlus L G0 B0 u := by linarith
    have hX1 : Xsm L G0 B0 < (fPlus L G0 B0 u + fPlus L G0 B0 v) / 2 := by
      linarith [hge_Xsm v hvI, hfpm v hvI]
    have hX2 : (fPlus L G0 B0 u + fPlus L G0 B0 v) / 2 < Xsp L G0 B0 := by
      linarith [hle_Xsp u huI]
    set X := (fPlus L G0 B0 u + fPlus L G0 B0 v) / 2 with hXdef
    have huv_sub : Icc u v ⊆ Icc 0 L := Icc_subset_Icc hu0 hvI.2
    have hvc_sub : Icc v uc ⊆ Icc 0 L := Icc_subset_Icc hvI.1 hucI.2
    obtain ⟨e2, he2, hfe2⟩ := intermediate_value_Icc' huv (hcontp.mono huv_sub) ⟨hXlo.le, hXhi.le⟩
    obtain ⟨e3, he3, hfe3⟩ := intermediate_value_Icc hvuc (hcontp.mono hvc_sub)
      ⟨hXlo.le, by rw [hfp_uc]; linarith [hX2]⟩
    have he2I : e2 ∈ Icc 0 L := huv_sub he2
    have he3I : e3 ∈ Icc 0 L := hvc_sub he3
    have := between_allowed hA hG hg hX1 hX2 he2I he3I he2.2 he3.1 hvI
      ⟨by linarith [hfpm e2 he2I], by linarith⟩ ⟨by linarith [hfpm e3 he3I], by linarith⟩
    linarith [this.2]
  -- (ii) the dips on the right: `f_+` is nonincreasing on `[uc, L]`
  have dipR : ∀ v w, uc ≤ v → v ≤ w → w ≤ L → fPlus L G0 B0 w ≤ fPlus L G0 B0 v := by
    intro v w hvuc hvw hwL
    by_contra hcon
    push Not at hcon
    have hvI : v ∈ Icc 0 L := ⟨le_trans huc.1.le hvuc, le_trans hvw hwL⟩
    have hwI : w ∈ Icc 0 L := ⟨le_trans hvI.1 hvw, hwL⟩
    have hXlo : fPlus L G0 B0 v < (fPlus L G0 B0 v + fPlus L G0 B0 w) / 2 := by linarith
    have hXhi : (fPlus L G0 B0 v + fPlus L G0 B0 w) / 2 < fPlus L G0 B0 w := by linarith
    have hX1 : Xsm L G0 B0 < (fPlus L G0 B0 v + fPlus L G0 B0 w) / 2 := by
      linarith [hge_Xsm v hvI, hfpm v hvI]
    have hX2 : (fPlus L G0 B0 v + fPlus L G0 B0 w) / 2 < Xsp L G0 B0 := by
      linarith [hle_Xsp w hwI]
    set X := (fPlus L G0 B0 v + fPlus L G0 B0 w) / 2 with hXdef
    have hvu_sub : Icc uc v ⊆ Icc 0 L := fun x hx => ⟨le_trans hucI.1 hx.1, le_trans hx.2 hvI.2⟩
    have hvw_sub : Icc v w ⊆ Icc 0 L := Icc_subset_Icc hvI.1 hwL
    obtain ⟨ea, hea, hfea⟩ := intermediate_value_Icc' hvuc (hcontp.mono hvu_sub)
      ⟨hXlo.le, by rw [hfp_uc]; linarith [hX2]⟩
    obtain ⟨eb, heb, hfeb⟩ := intermediate_value_Icc hvw (hcontp.mono hvw_sub) ⟨hXlo.le, hXhi.le⟩
    have heaI : ea ∈ Icc 0 L := hvu_sub hea
    have hebI : eb ∈ Icc 0 L := hvw_sub heb
    have := between_allowed hA hG hg hX1 hX2 heaI hebI hea.2 heb.1 hvI
      ⟨by linarith [hfpm ea heaI], by linarith⟩ ⟨by linarith [hfpm eb hebI], by linarith⟩
    linarith [this.2]
  -- (iii) the two estimates at the ends
  have hE1 : ∀ c, 0 < c → c ≤ uc → fPlus L G0 B0 0 < fPlus L G0 B0 c := by
    intro c hc hcuc
    obtain ⟨δ, hδ, hn⟩ := fPlus_gt_near_zero hL hG hg hB1
    have hm : min c (δ / 2) ∈ Ioo 0 δ := ⟨lt_min hc (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    have h1 := hn _ hm
    have h2 := dipL (min c (δ / 2)) c (le_of_lt (lt_min hc (by linarith))) (min_le_left _ _) hcuc
    linarith
  have hE2 : ∀ c, uc ≤ c → c < L → fPlus L G0 B0 L < fPlus L G0 B0 c := by
    intro c hcuc hcL
    obtain ⟨δ, hδ, hn⟩ := fPlus_gt_near_L hL hG hg hB1
    have hm : L - min (δ / 2) ((L - c) / 2) ∈ Ioo (L - δ) L :=
      ⟨by linarith [min_le_left (δ / 2) ((L - c) / 2)], by linarith [lt_min (by linarith : (0:ℝ) < δ / 2) (by linarith : (0:ℝ) < (L - c) / 2)]⟩
    have h1 := hn _ hm
    have hmpos : 0 < min (δ / 2) ((L - c) / 2) := lt_min (by linarith) (by linarith)
    have h2 := dipR c (L - min (δ / 2) ((L - c) / 2)) hcuc
      (by linarith [min_le_right (δ / 2) ((L - c) / 2)]) (by linarith)
    linarith
  -- (iv) every critical point of `f_+` in `(0, L)` is `uc`
  have hcrit : ∀ c ∈ Ioo 0 L, deriv (fPlus L G0 B0) c = 0 → c = uc := by
    intro c hc hdc
    rcases lt_trichotomy c uc with hlt | heq | hgt
    · exfalso
      have hcI : c ∈ Icc 0 L := ⟨hc.1.le, hc.2.le⟩
      have hfc_lt : fPlus L G0 B0 c < Xsp L G0 B0 := by
        refine lt_of_le_of_ne (hle_Xsp c hcI) ?_
        intro heq'
        have := (hXp c hcI).1 heq'
        linarith
      have hgap : fMinus L G0 B0 c < fPlus L G0 B0 c := by
        have := fPlus_sub_fMinus (L := L) (G0 := G0) (B0 := B0) c
        have hsq : 0 < Real.sqrt (E0 L G0 c) := Real.sqrt_pos.2 (E0_pos hG hg hc)
        linarith
      have hXsm : Xsm L G0 B0 < fPlus L G0 B0 c := by linarith [hge_Xsm c hcI]
      obtain ⟨a, b, ha0, hab, hbL, hS, hda, hdb, ha0B, hbLB⟩ := hA (fPlus L G0 B0 c) hXsm hfc_lt
      have hcS : c ∈ Icc a b := by
        rw [← hS]
        exact ⟨hcI, (Tfun_nonneg_iff hG hg hcI _).2 ⟨by linarith, le_rfl⟩⟩
      have hac : a ≤ c := hcS.1
      have hbelow : ∀ u, 0 ≤ u → u < a → fPlus L G0 B0 u < fPlus L G0 B0 c := by
        intro u hu0 hua
        by_contra hcon
        push Not at hcon
        have huI : u ∈ Icc 0 L := ⟨hu0, le_trans hua.le (le_trans hac hc.2.le)⟩
        have hfu : fPlus L G0 B0 u ≤ fPlus L G0 B0 c := dipL u c hu0 (le_trans hua.le hac) hlt.le
        have huS : u ∈ Icc a b := by
          rw [← hS]
          exact ⟨huI, (Tfun_nonneg_iff hG hg huI _).2 ⟨by linarith [hfpm u huI], hcon⟩⟩
        linarith [huS.1]
      have hfa : fPlus L G0 B0 a = fPlus L G0 B0 c := by
        have haS : a ∈ Icc a b := ⟨le_rfl, hab⟩
        have haI : a ∈ Icc 0 L := ⟨ha0, le_trans hab hbL⟩
        have hXa : fPlus L G0 B0 c ≤ fPlus L G0 B0 a := by
          rw [← hS] at haS
          exact ((Tfun_nonneg_iff hG hg haI _).1 haS.2).2
        linarith [dipL a c ha0 hac hlt.le]
      have ha_pos : 0 < a := by
        rcases eq_or_lt_of_le ha0 with h0 | h0
        · exfalso
          have := hE1 c hc.1 hlt.le
          rw [← h0] at hfa
          linarith
        · exact h0
      have haI : a ∈ Ioo 0 L := ⟨ha_pos, lt_of_le_of_lt hac hc.2⟩
      have hda0 : deriv (fPlus L G0 B0) a = 0 := by
        rcases eq_or_lt_of_le hac with hace | hace
        · rw [hace]; exact hdc
        · -- `f_+` is constant on `[a, c]`
          have hfd := fPlus_hasDerivAt_of_mem hG hg hG2 hB2 haI
          set d := deriv (fPlus L G0 B0) a with hd
          by_contra hdne
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · obtain ⟨δ, hδ, -, hn⟩ := count_local_sign (f := fun u => -(fPlus L G0 B0 u - fPlus L G0 B0 c))
              (f' := -d) (by exact (hfd.sub_const _).neg) (by simp [hfa]) (by linarith)
            have hmt : a - min (δ / 2) (a / 2) ∈ Ioo (a - δ) a :=
              ⟨by linarith [min_le_left (δ / 2) (a / 2)], by linarith [lt_min (by linarith : (0:ℝ) < δ / 2) (by linarith : (0:ℝ) < a / 2)]⟩
            have h1 := hn _ hmt.1 hmt.2
            have h2 := hbelow (a - min (δ / 2) (a / 2)) (by linarith [min_le_right (δ / 2) (a / 2)])
              (by linarith [lt_min (by linarith : (0:ℝ) < δ / 2) (by linarith : (0:ℝ) < a / 2)])
            linarith
          · obtain ⟨δ, hδ, hn, -⟩ := count_local_sign (f := fun u => fPlus L G0 B0 u - fPlus L G0 B0 c)
              (f' := d) (hfd.sub_const _) (by simp [hfa]) hpos
            obtain ⟨t, htdef⟩ : ∃ t, t = a + min (δ / 2) ((c - a) / 2) := ⟨_, rfl⟩
            have hm1 : 0 < min (δ / 2) ((c - a) / 2) := lt_min (by linarith) (by linarith)
            have hm2 : min (δ / 2) ((c - a) / 2) ≤ (c - a) / 2 := min_le_right _ _
            have hm3 : min (δ / 2) ((c - a) / 2) ≤ δ / 2 := min_le_left _ _
            have ht1 : a < t := by rw [htdef]; linarith
            have ht2 : t ≤ c := by rw [htdef]; linarith
            have ht3 : t < a + δ := by rw [htdef]; linarith
            have h1 := hn t ht1 ht3
            have hpt : fPlus L G0 B0 t = fPlus L G0 B0 c := by
              apply le_antisymm
              · exact dipL t c (by linarith) ht2 hlt.le
              · have := dipL a t ha0 ht1.le (by linarith)
                linarith
            linarith
      have hT := deriv_Tfun_eq hG hg hG2 hB2 (fPlus L G0 B0 c) haI
      have hTz : deriv (Tfun L G0 B0 (fPlus L G0 B0 c)) a = 0 := by
        rw [hT, hda0]
        have : fPlus L G0 B0 a - fPlus L G0 B0 c = 0 := by linarith
        rw [this]
        ring
      exact (hda ha_pos) hTz
    · exact heq
    · exfalso
      have hcI : c ∈ Icc 0 L := ⟨le_trans huc.1.le hgt.le, hc.2.le⟩
      have hfc_lt : fPlus L G0 B0 c < Xsp L G0 B0 := by
        refine lt_of_le_of_ne (hle_Xsp c hcI) ?_
        intro heq'
        have := (hXp c hcI).1 heq'
        linarith
      have hgap : fMinus L G0 B0 c < fPlus L G0 B0 c := by
        have := fPlus_sub_fMinus (L := L) (G0 := G0) (B0 := B0) c
        have hsq : 0 < Real.sqrt (E0 L G0 c) := Real.sqrt_pos.2 (E0_pos hG hg hc)
        linarith
      have hXsm : Xsm L G0 B0 < fPlus L G0 B0 c := by linarith [hge_Xsm c hcI]
      obtain ⟨a, b, ha0, hab, hbL, hS, hda, hdb, ha0B, hbLB⟩ := hA (fPlus L G0 B0 c) hXsm hfc_lt
      have hcS : c ∈ Icc a b := by
        rw [← hS]
        exact ⟨hcI, (Tfun_nonneg_iff hG hg hcI _).2 ⟨by linarith, le_rfl⟩⟩
      have hcb : c ≤ b := hcS.2
      have hbelow : ∀ u, b < u → u ≤ L → fPlus L G0 B0 u < fPlus L G0 B0 c := by
        intro u hbu huL
        by_contra hcon
        push Not at hcon
        have huI : u ∈ Icc 0 L := ⟨by linarith, huL⟩
        have hfu : fPlus L G0 B0 u ≤ fPlus L G0 B0 c := dipR c u hgt.le (le_trans hcb hbu.le) huL
        have huS : u ∈ Icc a b := by
          rw [← hS]
          exact ⟨huI, (Tfun_nonneg_iff hG hg huI _).2 ⟨by linarith [hfpm u huI], hcon⟩⟩
        linarith [huS.2]
      have hbI : b ∈ Ioo 0 L := ⟨lt_of_lt_of_le huc.1 (le_trans hgt.le hcb), by
        rcases eq_or_lt_of_le hbL with h | h
        · exfalso
          have hfb : fPlus L G0 B0 b = fPlus L G0 B0 c := by
            have hbI' : b ∈ Icc 0 L := ⟨by linarith, hbL⟩
            have hbS : b ∈ Icc a b := ⟨hab, le_rfl⟩
            rw [← hS] at hbS
            linarith [((Tfun_nonneg_iff hG hg hbI' _).1 hbS.2).2, dipR c b hgt.le hcb hbL]
          have := hE2 c hgt.le hc.2
          rw [h] at hfb
          linarith
        · exact h⟩
      have hfb : fPlus L G0 B0 b = fPlus L G0 B0 c := by
        have hbI' : b ∈ Icc 0 L := ⟨by linarith [hbI.1], hbI.2.le⟩
        have hbS : b ∈ Icc a b := ⟨hab, le_rfl⟩
        rw [← hS] at hbS
        linarith [((Tfun_nonneg_iff hG hg hbI' _).1 hbS.2).2, dipR c b hgt.le hcb hbI.2.le]
      have hbL' : b < L := hbI.2
      have hdb0 : deriv (fPlus L G0 B0) b = 0 := by
        rcases eq_or_lt_of_le hcb with hceq | hclt
        · rw [← hceq]; exact hdc
        · have hfd := fPlus_hasDerivAt_of_mem hG hg hG2 hB2 hbI
          set d := deriv (fPlus L G0 B0) b with hd
          by_contra hdne
          rcases lt_or_gt_of_ne hdne with hneg | hpos
          · obtain ⟨δ, hδ, -, hn⟩ := count_local_sign (f := fun u => -(fPlus L G0 B0 u - fPlus L G0 B0 c))
              (f' := -d) (hfd.sub_const _).neg (by simp [hfb]) (by linarith)
            obtain ⟨t, htdef⟩ : ∃ t, t = b - min (δ / 2) ((b - c) / 2) := ⟨_, rfl⟩
            have hm1 : 0 < min (δ / 2) ((b - c) / 2) := lt_min (by linarith) (by linarith)
            have hm2 : min (δ / 2) ((b - c) / 2) ≤ (b - c) / 2 := min_le_right _ _
            have hm3 : min (δ / 2) ((b - c) / 2) ≤ δ / 2 := min_le_left _ _
            have ht1 : c < t := by rw [htdef]; linarith
            have ht2 : t < b := by rw [htdef]; linarith
            have ht3 : b - δ < t := by rw [htdef]; linarith
            have h1 := hn t ht3 ht2
            have hpt : fPlus L G0 B0 t = fPlus L G0 B0 c := by
              apply le_antisymm
              · exact dipR c t hgt.le ht1.le (by linarith)
              · have := dipR t b (by linarith) ht2.le hbL
                linarith
            linarith
          · obtain ⟨δ, hδ, hn, -⟩ := count_local_sign (f := fun u => fPlus L G0 B0 u - fPlus L G0 B0 c)
              (f' := d) (hfd.sub_const _) (by simp [hfb]) hpos
            obtain ⟨t, htdef⟩ : ∃ t, t = b + min (δ / 2) ((L - b) / 2) := ⟨_, rfl⟩
            have hm1 : 0 < min (δ / 2) ((L - b) / 2) := lt_min (by linarith) (by linarith)
            have hm2 : min (δ / 2) ((L - b) / 2) ≤ (L - b) / 2 := min_le_right _ _
            have hm3 : min (δ / 2) ((L - b) / 2) ≤ δ / 2 := min_le_left _ _
            have ht1 : b < t := by rw [htdef]; linarith
            have ht2 : t < b + δ := by rw [htdef]; linarith
            have ht3 : t < L := by rw [htdef]; linarith
            have h1 := hn t ht1 ht2
            have := hbelow t ht1 ht3.le
            linarith
      have hT := deriv_Tfun_eq hG hg hG2 hB2 (fPlus L G0 B0 c) hbI
      have hTz : deriv (Tfun L G0 B0 (fPlus L G0 B0 c)) b = 0 := by
        rw [hT, hdb0]
        have : fPlus L G0 B0 b - fPlus L G0 B0 c = 0 := by linarith
        rw [this]
        ring
      exact (hdb hbL') hTz
  -- (v) conclusion
  have hderiv_uc : deriv (fPlus L G0 B0) uc = 0 := by
    have hmax : IsLocalMax (fPlus L G0 B0) uc :=
      Filter.eventually_of_mem (Ioo_mem_nhds huc.1 huc.2)
        (fun y hy => by have := hle_Xsp y (Ioo_subset_Icc_self hy); linarith [hfp_uc])
    exact hmax.deriv_eq_zero
  refine ⟨uc, huc, ?_, hdeg⟩
  ext u
  constructor
  · rintro ⟨hu, hdu⟩
    exact Set.mem_singleton_iff.2 (hcrit u hu hdu)
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact ⟨huc, hderiv_uc⟩

/-! ### Assembly -/

lemma shape_of_Pp {B0 : ℝ → ℝ} (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (hPp : PpProp L G0 B0) :
    ∃ uc ∈ Ioo 0 L, (StrictMonoOn (fPlus L G0 B0) (Icc 0 uc) ∧ StrictAntiOn (fPlus L G0 B0) (Icc uc L)) ∧
      deriv (deriv (fPlus L G0 B0)) uc < 0 ∧ (∀ a ∈ Ioo 0 L, deriv (fPlus L G0 B0) a = 0 → a = uc) := by
  obtain ⟨uc, huc, hset, hneg⟩ := hPp
  have hcrit : ∀ u ∈ Ioo 0 L, deriv (fPlus L G0 B0) u = 0 ↔ u = uc := by
    intro u hu
    exact ⟨fun hd => Set.mem_singleton_iff.1 ((Set.ext_iff.1 hset u).1 ⟨hu, hd⟩),
      fun he => ((Set.ext_iff.1 hset u).2 (Set.mem_singleton_iff.2 he)).2⟩
  have hcont := fPlus_continuousOn hG2 hB2
  have hC := fPlus_contDiffOn hG hg hG2 hB2
  exact ⟨uc, huc, shape_of_crit huc hcont hC hcrit hneg, hneg, fun a ha h => (hcrit a ha).1 h⟩

lemma max_of_shape {f : ℝ → ℝ} {uc : ℝ} (huc : uc ∈ Ioo 0 L) (hm1 : StrictMonoOn f (Icc 0 uc))
    (hm2 : StrictAntiOn f (Icc uc L)) : ∀ u ∈ Icc 0 L, f u ≤ f uc := by
  intro u hu
  rcases le_total u uc with h | h
  · exact hm1.monotoneOn ⟨hu.1, h⟩ ⟨huc.1.le, le_rfl⟩ h
  · exact hm2.antitoneOn ⟨le_rfl, huc.2.le⟩ ⟨h, hu.2⟩ h

lemma Bp_of_shape (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {uc : ℝ} (huc : uc ∈ Ioo 0 L)
    (hm1 : StrictMonoOn (fPlus L G0 B0) (Icc 0 uc)) (hm2 : StrictAntiOn (fPlus L G0 B0) (Icc uc L))
    (hneg : deriv (deriv (fPlus L G0 B0)) uc < 0) : BpProp L G0 B0 := by
  have hmax := max_of_shape huc hm1 hm2
  have hXsp : Xsp L G0 B0 = fPlus L G0 B0 uc := Xsp_eq_of_max ⟨huc.1.le, huc.2.le⟩ hmax
  refine ⟨uc, huc.1, huc.2, ?_, hneg⟩
  intro u hu
  rw [hXsp]
  constructor
  · intro h
    rcases lt_trichotomy u uc with hlt | heq | hgt
    · exfalso
      have := hm1 ⟨hu.1, hlt.le⟩ ⟨huc.1.le, le_rfl⟩ hlt
      linarith
    · exact heq
    · exfalso
      have := hm2 ⟨le_rfl, huc.2.le⟩ ⟨hgt.le, hu.2⟩ hgt
      linarith
  · intro h
    rw [h]

lemma Bm_of_shape_neg (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {q : ℝ} (hq : q ∈ Ioo 0 L)
    (hm1 : StrictMonoOn (fPlus L G0 (fun u => -B0 u)) (Icc 0 q))
    (hm2 : StrictAntiOn (fPlus L G0 (fun u => -B0 u)) (Icc q L))
    (hneg : deriv (deriv (fPlus L G0 (fun u => -B0 u))) q < 0) : BmProp L G0 B0 := by
  have hfpn : ∀ u, fPlus L G0 (fun u => -B0 u) u = -fMinus L G0 B0 u := fun u => congrFun fPlus_neg_B u
  have hmax := max_of_shape hq hm1 hm2
  have hmin : ∀ u ∈ Icc 0 L, fMinus L G0 B0 q ≤ fMinus L G0 B0 u := by
    intro u hu
    have := hmax u hu
    rw [hfpn, hfpn] at this
    linarith
  have hXm : Xsm L G0 B0 = fMinus L G0 B0 q := Xsm_eq_of_min ⟨hq.1.le, hq.2.le⟩ hmin
  have hdd : deriv (deriv (fPlus L G0 (fun u => -B0 u))) q = - deriv (deriv (fMinus L G0 B0)) q :=
    congrFun deriv_deriv_fPlus_neg q
  refine ⟨q, hq.1, hq.2, ?_, by linarith⟩
  intro u hu
  rw [hXm]
  constructor
  · intro h
    rcases lt_trichotomy u q with hlt | heq | hgt
    · exfalso
      have h1 := hm1 ⟨hu.1, hlt.le⟩ ⟨hq.1.le, le_rfl⟩ hlt
      rw [hfpn, hfpn, h] at h1
      exact lt_irrefl _ h1
    · exact heq
    · exfalso
      have h1 := hm2 ⟨le_rfl, hq.2.le⟩ ⟨hgt.le, hu.2⟩ hgt
      rw [hfpn, hfpn, h] at h1
      exact lt_irrefl _ h1
  · intro h
    rw [h]

lemma Bp_neg_of_Bm (hBm : BmProp L G0 B0) (hcontm : ContinuousOn (fMinus L G0 B0) (Icc 0 L)) :
    BpProp L G0 (fun u => -B0 u) := by
  obtain ⟨q, hq, hq', hiff, hpos⟩ := hBm
  have hqe : fMinus L G0 B0 q = Xsm L G0 B0 := (hiff q ⟨hq.le, hq'.le⟩).2 rfl
  have hXsp := Xsp_neg_B hcontm ⟨hq.le, hq'.le⟩ hqe
  have hfpn : ∀ u, fPlus L G0 (fun u => -B0 u) u = -fMinus L G0 B0 u := fun u => congrFun fPlus_neg_B u
  have hdd : deriv (deriv (fPlus L G0 (fun u => -B0 u))) q = - deriv (deriv (fMinus L G0 B0)) q :=
    congrFun deriv_deriv_fPlus_neg q
  refine ⟨q, hq, hq', ?_, by linarith⟩
  intro u hu
  rw [hXsp, hfpn]
  constructor
  · intro h
    have : fMinus L G0 B0 u = Xsm L G0 B0 := by linarith
    exact (hiff u hu).1 this
  · intro h
    rw [h, hqe]

lemma Pm_iff_neg : PmProp L G0 B0 ↔ PpProp L G0 (fun u => -B0 u) := by
  have key : ∀ u, deriv (fPlus L G0 (fun u => -B0 u)) u = -deriv (fMinus L G0 B0) u :=
    fun u => congrFun deriv_fPlus_neg u
  have key2 : ∀ u, deriv (deriv (fPlus L G0 (fun u => -B0 u))) u = -deriv (deriv (fMinus L G0 B0)) u :=
    fun u => congrFun deriv_deriv_fPlus_neg u
  constructor
  · rintro ⟨uc, huc, hset, hpos⟩
    refine ⟨uc, huc, ?_, by rw [key2]; linarith⟩
    have hsetEq : {u ∈ Ioo 0 L | deriv (fPlus L G0 (fun u => -B0 u)) u = 0} =
        {u ∈ Ioo 0 L | deriv (fMinus L G0 B0) u = 0} := by
      ext u
      simp only [Set.mem_ofPred_eq, key, neg_eq_zero]
    rw [hsetEq]
    exact hset
  · rintro ⟨uc, huc, hset, hneg⟩
    refine ⟨uc, huc, ?_, by rw [key2] at hneg; linarith⟩
    have hsetEq : {u ∈ Ioo 0 L | deriv (fMinus L G0 B0) u = 0} =
        {u ∈ Ioo 0 L | deriv (fPlus L G0 (fun u => -B0 u)) u = 0} := by
      ext u
      simp only [Set.mem_ofPred_eq, key, neg_eq_zero]
    rw [hsetEq]
    exact hset

/-- **lem:hyp-morse** (`HypMorseEquiv`), proved. -/
theorem hypMorseEquiv : HypMorseEquiv := by
  intro L G0 B0 g hL hg hG hG2 hB2
  show (PpProp L G0 B0 ∧ PmProp L G0 B0) ↔ (AProp L G0 B0 ∧ BpProp L G0 B0 ∧ BmProp L G0 B0)
  have hB2n : ContDiffOn ℝ 2 (fun u => -B0 u) (Icc 0 L) := hB2.neg
  have hcontp := fPlus_continuousOn hG2 hB2
  have hcontm := fMinus_continuousOn hG2 hB2
  constructor
  · rintro ⟨hPp, hPm⟩
    obtain ⟨uc, huc, hsh, hdeg, hcrit⟩ := shape_of_Pp hG hg hG2 hB2 hPp
    have hPpn : PpProp L G0 (fun u => -B0 u) := Pm_iff_neg.1 hPm
    obtain ⟨q, hq, hshn, hdegn, hcritn⟩ := shape_of_Pp hG hg hG2 hB2n hPpn
    have hfm1 : StrictAntiOn (fMinus L G0 B0) (Icc 0 q) := by
      intro x hx y hy hxy
      have := hshn.1 hx hy hxy
      rw [congrFun fPlus_neg_B x, congrFun fPlus_neg_B y] at this
      linarith
    have hfm2 : StrictMonoOn (fMinus L G0 B0) (Icc q L) := by
      intro x hx y hy hxy
      have := hshn.2 hx hy hxy
      rw [congrFun fPlus_neg_B x, congrFun fPlus_neg_B y] at this
      linarith
    have hcritm : ∀ a ∈ Ioo 0 L, deriv (fMinus L G0 B0) a = 0 → a = q := by
      intro a ha h
      apply hcritn a ha
      rw [congrFun deriv_fPlus_neg a, h, neg_zero]
    have hXp : fPlus L G0 B0 uc = Xsp L G0 B0 :=
      (Xsp_eq_of_max ⟨huc.1.le, huc.2.le⟩ (max_of_shape huc hsh.1 hsh.2)).symm
    have hmaxn := max_of_shape hq hshn.1 hshn.2
    have hXm : fMinus L G0 B0 q = Xsm L G0 B0 := by
      have hmin : ∀ u ∈ Icc 0 L, fMinus L G0 B0 q ≤ fMinus L G0 B0 u := by
        intro u hu
        have := hmaxn u hu
        rw [congrFun fPlus_neg_B u, congrFun fPlus_neg_B q] at this
        linarith
      exact (Xsm_eq_of_min ⟨hq.1.le, hq.2.le⟩ hmin).symm
    have hA := A_of_shapes hG hg hL hG2 hB2 huc hq hsh.1 hsh.2 hfm1 hfm2 hXp hXm hcrit hcritm
    have hBp := Bp_of_shape hG hg hG2 hB2 huc hsh.1 hsh.2 hdeg
    have hBm := Bm_of_shape_neg hG hg hG2 hB2 hq hshn.1 hshn.2 hdegn
    exact ⟨hA, hBp, hBm⟩
  · rintro ⟨hA, hBp, hBm⟩
    have hBp' : BpProp L G0 (fun u => -B0 u) := Bp_neg_of_Bm hBm hcontm
    obtain ⟨uc, hu0, huL, hXpi, hdeg⟩ := hBp
    obtain ⟨q, hq0, hqL, hXmi, hdegm⟩ := hBm
    have huc : uc ∈ Ioo 0 L := ⟨hu0, huL⟩
    have hq : q ∈ Ioo 0 L := ⟨hq0, hqL⟩
    have hucI : uc ∈ Icc 0 L := ⟨huc.1.le, huc.2.le⟩
    have hqI : q ∈ Icc 0 L := ⟨hq.1.le, hq.2.le⟩
    have hpe : fPlus L G0 B0 uc = Xsp L G0 B0 := (hXpi uc hucI).2 rfl
    have hqe : fMinus L G0 B0 q = Xsm L G0 B0 := (hXmi q hqI).2 rfl
    have hPp := crit_of_A hG hg hL hG2 hB2 hA huc hXpi hdeg
    have hA' : AProp L G0 (fun u => -B0 u) := AProp_neg hA hcontp hcontm hucI hpe hqI hqe
    obtain ⟨qn, hqn0, hqnL, hXpn, hdegn⟩ := hBp'
    have hqn' : qn ∈ Ioo 0 L := ⟨hqn0, hqnL⟩
    have hPpn := crit_of_A hG hg hL hG2 hB2n hA' hqn' hXpn hdegn
    exact ⟨hPp, Pm_iff_neg.2 hPpn⟩

/-! ### (L2.G2) openness: the derivative form of (M) and its stability -/

/-- `G'` on `[0, L]` (one-sided at the ends); it is the derivative for `u` in `(0, L)`. -/
def d1 (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ := iteratedDerivWithin 1 G (Icc 0 L) u

/-- `G''` on `[0, L]`. -/
def d2 (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ := iteratedDerivWithin 2 G (Icc 0 L) u

/-- `E_0' = (L - 2u) G + u (L - u) G'`. -/
def Epf (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ := (L - 2 * u) * G u + u * (L - u) * d1 L G u

/-- `E_0'' = -2 G + 2 (L - 2u) G' + u (L - u) G''`. -/
def Epp (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ :=
  -2 * G u + 2 * (L - 2 * u) * d1 L G u + u * (L - u) * d2 L G u

/-- `h = B' sqrt(E) + E'`: `f_+' = h / sqrt(E)`. -/
def hf (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ := d1 L B u * Real.sqrt (E0 L G u) + Epf L G u

/-- `h' = B'' sqrt(E) + B' E' / (2 sqrt(E)) + E''`. -/
def hder (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ :=
  d2 L B u * Real.sqrt (E0 L G u) + d1 L B u * (Epf L G u / (2 * Real.sqrt (E0 L G u))) + Epp L G u

/-- `Q = 2 sqrt(E) h' = 2 B'' E + B' E' + 2 sqrt(E) E''` (division free). -/
def Qf (L : ℝ) (G B : ℝ → ℝ) (u : ℝ) : ℝ :=
  2 * d2 L B u * E0 L G u + d1 L B u * Epf L G u + 2 * Real.sqrt (E0 L G u) * Epp L G u

lemma d1_eq_deriv {G : ℝ → ℝ} {L u : ℝ} (hu : u ∈ Ioo 0 L) : d1 L G u = deriv G u := by
  unfold d1
  rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]

lemma d2_eq_deriv_deriv {G : ℝ → ℝ} {L u : ℝ} (hu : u ∈ Ioo 0 L) : d2 L G u = deriv (deriv G) u := by
  unfold d2
  have h2 : iteratedDerivWithin (1 + 1) G (Icc 0 L) u =
      derivWithin (iteratedDerivWithin 1 G (Icc 0 L)) (Icc 0 L) u := by
    rw [iteratedDerivWithin_succ]
  rw [show (2 : ℕ) = 1 + 1 from rfl, h2, derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
  have hev : iteratedDerivWithin 1 G (Icc 0 L) =ᶠ[𝓝 u] deriv G :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hu) (fun v hv => d1_eq_deriv hv)
  exact hev.deriv_eq

lemma hasDerivAt_of_C2 {G : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt G (d1 L G u) u := by
  have hd : DifferentiableAt ℝ G u :=
    (hG.differentiableOn (by norm_num) u (Ioo_subset_Icc_self hu)).differentiableAt (Icc_mem_nhds hu.1 hu.2)
  rw [d1_eq_deriv hu]
  exact hd.hasDerivAt

lemma hasDerivAt_d1_of_C2 {G : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt (d1 L G) (d2 L G u) u := by
  have hGo : ContDiffOn ℝ 2 G (Ioo 0 L) := hG.mono Ioo_subset_Icc_self
  have hc1 : ContDiffOn ℝ 1 (deriv G) (Ioo 0 L) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1 (by norm_num; exact hGo)).2.2
  have hdd : DifferentiableAt ℝ (deriv G) u :=
    (hc1.differentiableOn (by norm_num) u hu).differentiableAt (isOpen_Ioo.mem_nhds hu)
  have hev : d1 L G =ᶠ[𝓝 u] deriv G :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hu) (fun v hv => d1_eq_deriv hv)
  rw [d2_eq_deriv_deriv hu]
  exact (hdd.hasDerivAt).congr_of_eventuallyEq hev

lemma hasDerivAt_E0 {G : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt (E0 L G) (Epf L G u) u := by
  have h1 : HasDerivAt (fun v => v * (L - v) * G v) (Epf L G u) u := by
    have := ((hasDerivAt_id' u).mul ((hasDerivAt_const u L).sub (hasDerivAt_id' u))).mul
      (hasDerivAt_of_C2 hG hu)
    convert this using 1
    try simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    unfold Epf
    ring
  exact h1

lemma hasDerivAt_Epf {G : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L) :
    HasDerivAt (Epf L G) (Epp L G u) u := by
  have h1 : HasDerivAt (fun v => (L - 2 * v) * G v + v * (L - v) * d1 L G v) (Epp L G u) u := by
    have a1 : HasDerivAt (fun v => (L - 2 * v) * G v) ((-2) * G u + (L - 2 * u) * d1 L G u) u := by
      have := ((hasDerivAt_const u L).sub ((hasDerivAt_id' u).const_mul 2)).mul (hasDerivAt_of_C2 hG hu)
      convert this using 1
      try simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
      ring
    have a2 := ((hasDerivAt_id' u).mul ((hasDerivAt_const u L).sub (hasDerivAt_id' u))).mul
        (hasDerivAt_d1_of_C2 hG hu)
    have := a1.add a2
    convert this using 1
    try simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    unfold Epp
    ring
  exact h1

lemma hasDerivAt_sqrtE0 {G : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) {u : ℝ} (hu : u ∈ Ioo 0 L)
    (hpos : 0 < E0 L G u) :
    HasDerivAt (fun v => Real.sqrt (E0 L G v)) (Epf L G u / (2 * Real.sqrt (E0 L G u))) u :=
  (hasDerivAt_E0 hG hu).sqrt hpos.ne'

lemma hasDerivAt_hf {G B : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) (hB : ContDiffOn ℝ 2 B (Icc 0 L))
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hpos : 0 < E0 L G u) :
    HasDerivAt (hf L G B) (hder L G B u) u := by
  have h1 : HasDerivAt (fun v => d1 L B v * Real.sqrt (E0 L G v))
      (d2 L B u * Real.sqrt (E0 L G u) + d1 L B u * (Epf L G u / (2 * Real.sqrt (E0 L G u)))) u :=
    (hasDerivAt_d1_of_C2 hB hu).mul (hasDerivAt_sqrtE0 hG hu hpos)
  have h2 := h1.add (hasDerivAt_Epf hG hu)
  unfold hder
  exact h2

lemma hasDerivAt_fPlus' {G B : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) (hB : ContDiffOn ℝ 2 B (Icc 0 L))
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hpos : 0 < E0 L G u) :
    HasDerivAt (fPlus L G B) (hf L G B u / Real.sqrt (E0 L G u)) u := by
  have hB' : HasDerivAt B (d1 L B u) u := hasDerivAt_of_C2 hB hu
  have h2 := hB'.add ((hasDerivAt_sqrtE0 hG hu hpos).const_mul 2)
  have hs : 0 < Real.sqrt (E0 L G u) := Real.sqrt_pos.2 hpos
  have e : fPlus L G B = fun v => B v + 2 * Real.sqrt (E0 L G v) := rfl
  rw [e]
  convert h2 using 1
  unfold hf
  field_simp

lemma Qf_eq {G B : ℝ → ℝ} {L u : ℝ} (hpos : 0 < E0 L G u) :
    Qf L G B u = 2 * Real.sqrt (E0 L G u) * hder L G B u := by
  have hs : Real.sqrt (E0 L G u) ^ 2 = E0 L G u := Real.sq_sqrt hpos.le
  have hs0 : Real.sqrt (E0 L G u) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  unfold Qf hder
  generalize Real.sqrt (E0 L G u) = s at hs hs0 ⊢
  rw [← hs]
  field_simp

lemma E0_pos_Ioo {G : ℝ → ℝ} {L u : ℝ} (hGpos : ∀ v ∈ Ioo 0 L, 0 < G v) (hu : u ∈ Ioo 0 L) :
    0 < E0 L G u :=
  mul_pos (mul_pos hu.1 (sub_pos.2 hu.2)) (hGpos u hu)

/-- The derivative form `(M)` of `f_+`: the zeros of `h = hf` in `(0, L)` form one point `uc` with `Q(uc) < 0`. -/
def HPprop (L : ℝ) (G B : ℝ → ℝ) : Prop :=
  ∃ uc ∈ Ioo 0 L, {u ∈ Ioo 0 L | hf L G B u = 0} = {uc} ∧ Qf L G B uc < 0

lemma pp_iff_HP {G B : ℝ → ℝ} {L : ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) (hB : ContDiffOn ℝ 2 B (Icc 0 L))
    (hGpos : ∀ v ∈ Ioo 0 L, 0 < G v) : PpProp L G B ↔ HPprop L G B := by
  have hfp : ∀ v ∈ Ioo 0 L, deriv (fPlus L G B) v = hf L G B v / Real.sqrt (E0 L G v) :=
    fun v hv => (hasDerivAt_fPlus' hG hB hv (E0_pos_Ioo hGpos hv)).deriv
  have hsq : ∀ v ∈ Ioo 0 L, Real.sqrt (E0 L G v) ≠ 0 :=
    fun v hv => (Real.sqrt_pos.2 (E0_pos_Ioo hGpos hv)).ne'
  constructor
  · rintro ⟨uc, huc, hset, hneg⟩
    have hzero : {u ∈ Ioo 0 L | hf L G B u = 0} = {uc} := by
      ext v
      constructor
      · rintro ⟨hv, hz⟩
        have h0 : deriv (fPlus L G B) v = 0 := by rw [hfp v hv, hz, zero_div]
        exact Set.mem_singleton_iff.2 (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hset v).1 ⟨hv, h0⟩))
      · intro hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        have h0 : deriv (fPlus L G B) v = 0 := ((Set.ext_iff.1 hset v).2 (Set.mem_singleton v)).2
        rw [hfp v huc] at h0
        have hz : hf L G B v = 0 := by
          rcases div_eq_zero_iff.1 h0 with h | h
          · exact h
          · exact absurd h (hsq v huc)
        exact ⟨huc, hz⟩
    have hz_uc : hf L G B uc = 0 := by
      have : uc ∈ {u ∈ Ioo 0 L | hf L G B u = 0} := by rw [hzero]; exact Set.mem_singleton uc
      exact this.2
    have hEv : deriv (fPlus L G B) =ᶠ[𝓝 uc] fun v => hf L G B v / Real.sqrt (E0 L G v) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds huc) hfp
    have hdd : deriv (deriv (fPlus L G B)) uc = deriv (fun v => hf L G B v / Real.sqrt (E0 L G v)) uc :=
      hEv.deriv_eq
    have hquot : HasDerivAt (fun v => hf L G B v / Real.sqrt (E0 L G v))
        ((hder L G B uc * Real.sqrt (E0 L G uc) - hf L G B uc *
          (Epf L G uc / (2 * Real.sqrt (E0 L G uc)))) / (Real.sqrt (E0 L G uc)) ^ 2) uc :=
      (hasDerivAt_hf hG hB huc (E0_pos_Ioo hGpos huc)).div
        (hasDerivAt_sqrtE0 hG huc (E0_pos_Ioo hGpos huc)) (hsq uc huc)
    have hkey : deriv (deriv (fPlus L G B)) uc = hder L G B uc / Real.sqrt (E0 L G uc) := by
      rw [hdd, hquot.deriv, hz_uc, zero_mul, sub_zero]
      have hs := hsq uc huc
      field_simp
    have hsp : 0 < Real.sqrt (E0 L G uc) := Real.sqrt_pos.2 (E0_pos_Ioo hGpos huc)
    have hder_neg : hder L G B uc < 0 := by
      rw [hkey] at hneg
      exact (div_neg_iff.1 hneg).elim (fun h => absurd h.2 (not_lt.2 hsp.le)) (fun h => h.1)
    refine ⟨uc, huc, hzero, ?_⟩
    rw [Qf_eq (E0_pos_Ioo hGpos huc)]
    exact mul_neg_of_pos_of_neg (by positivity) hder_neg
  · rintro ⟨uc, huc, hzero, hQ⟩
    have hz_uc : hf L G B uc = 0 := by
      have : uc ∈ {u ∈ Ioo 0 L | hf L G B u = 0} := by rw [hzero]; exact Set.mem_singleton uc
      exact this.2
    have hzeroD : {u ∈ Ioo 0 L | deriv (fPlus L G B) u = 0} = {uc} := by
      ext v
      constructor
      · rintro ⟨hv, h0⟩
        rw [hfp v hv] at h0
        have hz : hf L G B v = 0 := by
          rcases div_eq_zero_iff.1 h0 with h | h
          · exact h
          · exact absurd h (hsq v hv)
        have : v ∈ {u ∈ Ioo 0 L | hf L G B u = 0} := ⟨hv, hz⟩
        rw [hzero] at this
        exact this
      · intro hv
        rw [Set.mem_singleton_iff] at hv
        subst hv
        refine ⟨huc, ?_⟩
        rw [hfp v huc, hz_uc, zero_div]
    have hEv : deriv (fPlus L G B) =ᶠ[𝓝 uc] fun v => hf L G B v / Real.sqrt (E0 L G v) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds huc) hfp
    have hdd : deriv (deriv (fPlus L G B)) uc = deriv (fun v => hf L G B v / Real.sqrt (E0 L G v)) uc :=
      hEv.deriv_eq
    have hquot : HasDerivAt (fun v => hf L G B v / Real.sqrt (E0 L G v))
        ((hder L G B uc * Real.sqrt (E0 L G uc) - hf L G B uc *
          (Epf L G uc / (2 * Real.sqrt (E0 L G uc)))) / (Real.sqrt (E0 L G uc)) ^ 2) uc :=
      (hasDerivAt_hf hG hB huc (E0_pos_Ioo hGpos huc)).div
        (hasDerivAt_sqrtE0 hG huc (E0_pos_Ioo hGpos huc)) (hsq uc huc)
    have hkey : deriv (deriv (fPlus L G B)) uc = hder L G B uc / Real.sqrt (E0 L G uc) := by
      rw [hdd, hquot.deriv, hz_uc, zero_mul, sub_zero]
      have hs := hsq uc huc
      field_simp
    have hsp : 0 < Real.sqrt (E0 L G uc) := Real.sqrt_pos.2 (E0_pos_Ioo hGpos huc)
    have hder_neg : hder L G B uc < 0 := by
      rw [Qf_eq (E0_pos_Ioo hGpos huc)] at hQ
      nlinarith
    refine ⟨uc, huc, hzeroD, ?_⟩
    rw [hkey]
    exact div_neg_of_neg_of_pos hder_neg hsp

/-! ### Uniform continuity of the jet expressions -/

/-- `h` as a function of the jets `(u, G(u), G'(u), B'(u))`. -/
def hfJ (L u g0 g1 b1 : ℝ) : ℝ := b1 * Real.sqrt (u * (L - u) * g0) + ((L - 2 * u) * g0 + u * (L - u) * g1)

/-- `Q` as a function of the jets `(u, G, G', G'', B', B'')`. -/
def QfJ (L u g0 g1 g2 b1 b2 : ℝ) : ℝ :=
  2 * b2 * (u * (L - u) * g0) + b1 * ((L - 2 * u) * g0 + u * (L - u) * g1) +
    2 * Real.sqrt (u * (L - u) * g0) * (-2 * g0 + 2 * (L - 2 * u) * g1 + u * (L - u) * g2)

lemma hfJ_continuous (L : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ => hfJ L p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold hfJ
  fun_prop

lemma QfJ_continuous (L : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ => QfJ L p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  unfold QfJ
  fun_prop

lemma hfJ_unif (L M η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ u ∈ Icc 0 L, ∀ g0 g1 b1 g0' g1' b1' : ℝ,
      g0 ∈ Icc (-M) M → g1 ∈ Icc (-M) M → b1 ∈ Icc (-M) M → g0' ∈ Icc (-M) M → g1' ∈ Icc (-M) M →
      b1' ∈ Icc (-M) M → |g0' - g0| < δ → |g1' - g1| < δ → |b1' - b1| < δ →
      |hfJ L u g0' g1' b1' - hfJ L u g0 g1 b1| < η := by
  set K : Set (ℝ × ℝ × ℝ × ℝ) := Icc 0 L ×ˢ (Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hU := hK.uniformContinuousOn_of_continuous (hfJ_continuous L).continuousOn
  obtain ⟨δ, hδ, hF⟩ := Metric.uniformContinuousOn_iff.1 hU η hη
  refine ⟨δ, hδ, fun u hu g0 g1 b1 g0' g1' b1' h0 h1 hb0 h0' h1' hb0' d0 d1 db => ?_⟩
  have hx : (u, g0, g1, b1) ∈ K := ⟨hu, h0, h1, hb0⟩
  have hy : (u, g0', g1', b1') ∈ K := ⟨hu, h0', h1', hb0'⟩
  have hd : dist ((u, g0, g1, b1) : ℝ × ℝ × ℝ × ℝ) (u, g0', g1', b1') < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    rw [abs_sub_comm g0, abs_sub_comm g1, abs_sub_comm b1]
    exact max_lt hδ (max_lt (by linarith [abs_nonneg (g0 - g0')]) (max_lt (by linarith) (by linarith)))
  have := hF _ hx _ hy hd
  simp only [Real.dist_eq] at this
  rw [abs_sub_comm]
  exact this

lemma QfJ_unif (L M η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ u ∈ Icc 0 L, ∀ g0 g1 g2 b1 b2 g0' g1' g2' b1' b2' : ℝ,
      g0 ∈ Icc (-M) M → g1 ∈ Icc (-M) M → g2 ∈ Icc (-M) M → b1 ∈ Icc (-M) M → b2 ∈ Icc (-M) M →
      g0' ∈ Icc (-M) M → g1' ∈ Icc (-M) M → g2' ∈ Icc (-M) M → b1' ∈ Icc (-M) M → b2' ∈ Icc (-M) M →
      |g0' - g0| < δ → |g1' - g1| < δ → |g2' - g2| < δ → |b1' - b1| < δ → |b2' - b2| < δ →
      |QfJ L u g0' g1' g2' b1' b2' - QfJ L u g0 g1 g2 b1 b2| < η := by
  set K : Set (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
    Icc 0 L ×ˢ (Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc (-M) M) with hKdef
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc))))
  have hU := hK.uniformContinuousOn_of_continuous (QfJ_continuous L).continuousOn
  obtain ⟨δ, hδ, hF⟩ := Metric.uniformContinuousOn_iff.1 hU η hη
  refine ⟨δ, hδ, fun u hu g0 g1 g2 b1 b2 g0' g1' g2' b1' b2' h0 h1 h2 hb1 hb2 h0' h1' h2' hb1' hb2'
    d0 d1 d2 db1 db2 => ?_⟩
  have hx : (u, g0, g1, g2, b1, b2) ∈ K := ⟨hu, h0, h1, h2, hb1, hb2⟩
  have hy : (u, g0', g1', g2', b1', b2') ∈ K := ⟨hu, h0', h1', h2', hb1', hb2'⟩
  have hd : dist ((u, g0, g1, g2, b1, b2) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (u, g0', g1', g2', b1', b2') < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [dist_self, Real.dist_eq]
    rw [abs_sub_comm g0, abs_sub_comm g1, abs_sub_comm g2, abs_sub_comm b1, abs_sub_comm b2]
    exact max_lt hδ (max_lt (by linarith [abs_nonneg (g0 - g0')]) (max_lt (by linarith)
      (max_lt (by linarith) (max_lt (by linarith) (by linarith)))))
  have := hF _ hx _ hy hd
  simp only [Real.dist_eq] at this
  rw [abs_sub_comm]
  exact this

lemma hf_eq_hfJ (L u : ℝ) (G B : ℝ → ℝ) :
    hf L G B u = hfJ L u (G u) (d1 L G u) (d1 L B u) := rfl

lemma Qf_eq_QfJ (L u : ℝ) (G B : ℝ → ℝ) :
    Qf L G B u = QfJ L u (G u) (d1 L G u) (d2 L G u) (d1 L B u) (d2 L B u) := rfl

lemma continuousOn_d1 {G : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G (Icc 0 L)) :
    ContinuousOn (d1 L G) (Icc 0 L) :=
  hG.continuousOn_iteratedDerivWithin (m := 1) (by norm_num) (uniqueDiffOn_Icc hL)

lemma continuousOn_d2 {G : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G (Icc 0 L)) :
    ContinuousOn (d2 L G) (Icc 0 L) :=
  hG.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) (uniqueDiffOn_Icc hL)

lemma continuousOn_hf {G B : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B (Icc 0 L)) : ContinuousOn (hf L G B) (Icc 0 L) := by
  have h1 := continuousOn_d1 hL hG
  have h2 := continuousOn_d1 hL hB
  have hE : ContinuousOn (E0 L G) (Icc 0 L) := (contDiffOn_E0 hG).continuousOn
  have hs : ContinuousOn (fun u => Real.sqrt (E0 L G u)) (Icc 0 L) :=
    Real.continuous_sqrt.comp_continuousOn hE
  have hEp : ContinuousOn (Epf L G) (Icc 0 L) :=
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul hG.continuousOn).add
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul h1)
  unfold hf
  exact (h2.mul hs).add hEp

lemma continuousOn_Qf {G B : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B (Icc 0 L)) : ContinuousOn (Qf L G B) (Icc 0 L) := by
  have h1 := continuousOn_d1 hL hG
  have h2 := continuousOn_d2 hL hG
  have h3 := continuousOn_d1 hL hB
  have h4 := continuousOn_d2 hL hB
  have hE : ContinuousOn (E0 L G) (Icc 0 L) := (contDiffOn_E0 hG).continuousOn
  have hs : ContinuousOn (fun u => Real.sqrt (E0 L G u)) (Icc 0 L) :=
    Real.continuous_sqrt.comp_continuousOn hE
  have hEp : ContinuousOn (Epf L G) (Icc 0 L) :=
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul hG.continuousOn).add
      ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul h1)
  have hEpp : ContinuousOn (Epp L G) (Icc 0 L) := by
    have hA : ContinuousOn (fun u => -2 * G u + 2 * (L - 2 * u) * d1 L G u) (Icc 0 L) :=
      (continuousOn_const.mul hG.continuousOn).add
        ((continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))).mul h1)
    exact hA.add ((continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).mul h2)
  unfold Qf
  exact (((continuousOn_const.mul h4).mul hE).add (h3.mul hEp)).add ((continuousOn_const.mul hs).mul hEpp)

/-- The sign of `h` for the base data: positive before `uc`, negative after. -/
lemma base_sign {G B : ℝ → ℝ} {L g : ℝ} (hL : 0 < L) (hg : 0 < g) (hG : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B (Icc 0 L)) (hGg : ∀ u ∈ Icc 0 L, g ≤ G u) {uc : ℝ} (huc : uc ∈ Ioo 0 L)
    (hzero : {u ∈ Ioo 0 L | hf L G B u = 0} = {uc}) :
    (∀ u ∈ Icc 0 L, u < uc → 0 < hf L G B u) ∧ (∀ u ∈ Icc 0 L, uc < u → hf L G B u < 0) := by
  have hcont := continuousOn_hf hL hG hB
  have hE0 : ∀ v, E0 L G v = v * (L - v) * G v := fun v => rfl
  have h0 : 0 < hf L G B 0 := by
    have e1 : E0 L G 0 = 0 := by rw [hE0]; ring
    have e2 : Epf L G 0 = L * G 0 := by unfold Epf; ring
    unfold hf
    rw [e1, Real.sqrt_zero, mul_zero, zero_add, e2]
    exact mul_pos hL (lt_of_lt_of_le hg (hGg 0 ⟨le_rfl, hL.le⟩))
  have hLn : hf L G B L < 0 := by
    have e1 : E0 L G L = 0 := by rw [hE0]; ring
    have e2 : Epf L G L = -(L * G L) := by unfold Epf; ring
    unfold hf
    rw [e1, Real.sqrt_zero, mul_zero, zero_add, e2]
    have := hGg L ⟨hL.le, le_rfl⟩
    have : 0 < L * G L := mul_pos hL (lt_of_lt_of_le hg this)
    linarith
  constructor
  · intro u hu hlt
    by_contra hcon
    push Not at hcon
    have hsub : Icc 0 u ⊆ Icc 0 L := Icc_subset_Icc le_rfl hu.2
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hu.1 (hcont.mono hsub) ⟨hcon, h0.le⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      linarith
    have hzI : z ∈ Ioo 0 L := ⟨lt_of_le_of_ne hz.1 (Ne.symm hz0), lt_of_le_of_lt hz.2 (hlt.trans huc.2)⟩
    have hzmem : z ∈ {u ∈ Ioo 0 L | hf L G B u = 0} := ⟨hzI, hfz⟩
    rw [hzero, Set.mem_singleton_iff] at hzmem
    linarith [hz.2]
  · intro u hu hgt
    by_contra hcon
    push Not at hcon
    have hsub : Icc u L ⊆ Icc 0 L := Icc_subset_Icc hu.1 le_rfl
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' hu.2 (hcont.mono hsub) ⟨hLn.le, hcon⟩
    have hzL : z ≠ L := by
      rintro rfl
      linarith
    have hzI : z ∈ Ioo 0 L := ⟨lt_of_lt_of_le (huc.1.trans hgt) hz.1, lt_of_le_of_ne hz.2 hzL⟩
    have hzmem : z ∈ {u ∈ Ioo 0 L | hf L G B u = 0} := ⟨hzI, hfz⟩
    rw [hzero, Set.mem_singleton_iff] at hzmem
    linarith [hz.1]

/-- A bound for the jets `G, G', G'', B', B''` on `[0, L]`. -/
lemma jets_bounded {G B : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B (Icc 0 L)) :
    ∃ M : ℝ, ∀ u ∈ Icc 0 L, |G u| ≤ M ∧ |d1 L G u| ≤ M ∧ |d2 L G u| ≤ M ∧ |d1 L B u| ≤ M ∧ |d2 L B u| ≤ M := by
  have hK : IsCompact (Icc 0 L) := isCompact_Icc
  have hG0 : ContinuousOn G (Icc 0 L) := hG.continuousOn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hG0
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (continuousOn_d1 hL hG)
  obtain ⟨C3, hC3⟩ := hK.exists_bound_of_continuousOn (continuousOn_d2 hL hG)
  obtain ⟨C4, hC4⟩ := hK.exists_bound_of_continuousOn (continuousOn_d1 hL hB)
  obtain ⟨C5, hC5⟩ := hK.exists_bound_of_continuousOn (continuousOn_d2 hL hB)
  refine ⟨|C1| + |C2| + |C3| + |C4| + |C5|, fun u hu => ?_⟩
  have a1 := hC1 u hu
  have a2 := hC2 u hu
  have a3 := hC3 u hu
  have a4 := hC4 u hu
  have a5 := hC5 u hu
  simp only [Real.norm_eq_abs] at a1 a2 a3 a4 a5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith [le_abs_self C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5]
  · linarith [le_abs_self C2, abs_nonneg C1, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5]
  · linarith [le_abs_self C3, abs_nonneg C1, abs_nonneg C2, abs_nonneg C4, abs_nonneg C5]
  · linarith [le_abs_self C4, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C5]
  · linarith [le_abs_self C5, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4]

/-- **Stability of (M) (derivative form).**  If `h` has a unique zero `uc` in `(0, L)` with `Q(uc) < 0` for the base data, then
every `C^2`-perturbation within a small `ε` (in the jets of order `≤ 2`, on `[0, L]`) of `G, B` has the same property. -/
lemma HP_stable {G B : ℝ → ℝ} {L g : ℝ} (hL : 0 < L) (hg : 0 < g) (hG : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B (Icc 0 L)) (hGg : ∀ u ∈ Icc 0 L, g ≤ G u) (hH : HPprop L G B) :
    ∃ ε > 0, ∀ G' B' : ℝ → ℝ, ContDiffOn ℝ 2 G' (Icc 0 L) → ContDiffOn ℝ 2 B' (Icc 0 L) →
      (∀ i ≤ 2, ∀ u ∈ Icc 0 L,
        |iteratedDerivWithin i G' (Icc 0 L) u - iteratedDerivWithin i G (Icc 0 L) u| ≤ ε ∧
        |iteratedDerivWithin i B' (Icc 0 L) u - iteratedDerivWithin i B (Icc 0 L) u| ≤ ε) →
      HPprop L G' B' := by
  obtain ⟨uc, huc, hzero, hQuc⟩ := hH
  have hucI : uc ∈ Icc 0 L := ⟨huc.1.le, huc.2.le⟩
  have hQc := continuousOn_Qf hL hG hB
  obtain ⟨δQ0, hδQ0, hQn⟩ := cont_upper_nbhd hQc hucI (by linarith : Qf L G B uc < 0)
  -- the radius `η` of the interval `I = [uc - η, uc + η]`
  have hmin_pos : 0 < min (min δQ0 uc) (L - uc) := lt_min (lt_min hδQ0 huc.1) (sub_pos.2 huc.2)
  have hmin1 : min (min δQ0 uc) (L - uc) ≤ min δQ0 uc := min_le_left _ _
  have hmin2 : min (min δQ0 uc) (L - uc) ≤ L - uc := min_le_right _ _
  have hmin3 : min δQ0 uc ≤ δQ0 := min_le_left _ _
  have hmin4 : min δQ0 uc ≤ uc := min_le_right _ _
  obtain ⟨η, hη, hηQ, hηuc, hηL⟩ : ∃ η : ℝ, 0 < η ∧ η < δQ0 ∧ η < uc ∧ η < L - uc :=
    ⟨min (min δQ0 uc) (L - uc) / 2, by linarith, by linarith, by linarith, by linarith⟩
  have hI_sub : Icc (uc - η) (uc + η) ⊆ Ioo 0 L := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hI_Icc : Icc (uc - η) (uc + η) ⊆ Icc 0 L := fun u hu => ⟨(hI_sub hu).1.le, (hI_sub hu).2.le⟩
  have hQneg_I : ∀ u ∈ Icc (uc - η) (uc + η), Qf L G B u < 0 := by
    intro u hu
    apply hQn u (hI_Icc hu)
    rw [abs_lt]
    constructor <;> linarith [hu.1, hu.2]
  -- the outer set `K_out = [0, uc - η] ∪ [uc + η, L]` where `h` has a fixed sign
  set Kout : Set ℝ := Icc 0 (uc - η) ∪ Icc (uc + η) L with hKout
  have hKout_Icc : Kout ⊆ Icc 0 L := by
    intro u hu
    rcases hu with hu | hu
    · exact ⟨hu.1, by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], hu.2⟩
  have hKout_cpt : IsCompact Kout := isCompact_Icc.union isCompact_Icc
  have hcontB := continuousOn_hf hL hG hB
  have hsign := base_sign hL hg hG hB hGg huc hzero
  have hsign_out : ∀ u ∈ Kout, (0 < hf L G B u ∧ u < uc) ∨ (hf L G B u < 0 ∧ uc < u) := by
    intro u hu
    rcases hu with hu | hu
    · exact Or.inl ⟨hsign.1 u (hKout_Icc (Or.inl hu)) (by linarith [hu.2]), by linarith [hu.2]⟩
    · exact Or.inr ⟨hsign.2 u (hKout_Icc (Or.inr hu)) (by linarith [hu.1]), by linarith [hu.1]⟩
  have hne_out : Kout.Nonempty := ⟨0, Or.inl ⟨le_rfl, by linarith⟩⟩
  obtain ⟨p, hp, hpmin⟩ := hKout_cpt.exists_isMinOn hne_out
    ((hcontB.mono hKout_Icc).abs)
  set m1 : ℝ := |hf L G B p| with hm1
  have hm1pos : 0 < m1 := by
    have := hsign_out p hp
    rw [hm1]
    rcases this with h | h
    · exact abs_pos.2 h.1.ne'
    · exact abs_pos.2 h.1.ne
  have hm1_le : ∀ u ∈ Kout, m1 ≤ |hf L G B u| := fun u hu => hpmin hu
  -- the maximum of `-Q` on `I`
  have hI_cpt : IsCompact (Icc (uc - η) (uc + η)) := isCompact_Icc
  have hI_ne : (Icc (uc - η) (uc + η)).Nonempty := ⟨uc, by constructor <;> linarith⟩
  obtain ⟨q, hq, hqmax⟩ := hI_cpt.exists_isMaxOn hI_ne ((hQc.mono hI_Icc))
  have hQmax : Qf L G B q < 0 := hQneg_I q hq
  set κ : ℝ := -Qf L G B q with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  have hQle : ∀ u ∈ Icc (uc - η) (uc + η), Qf L G B u ≤ Qf L G B q := fun u hu => hqmax hu
  -- bounds on the jets
  obtain ⟨M, hM⟩ := jets_bounded hL hG hB
  set M' : ℝ := |M| + 1 with hM'
  have hMM' : ∀ u ∈ Icc 0 L, |G u| ≤ M' ∧ |d1 L G u| ≤ M' ∧ |d2 L G u| ≤ M' ∧ |d1 L B u| ≤ M' ∧
      |d2 L B u| ≤ M' := by
    intro u hu
    obtain ⟨a, b, c, d, e⟩ := hM u hu
    have hM0 : M ≤ M' := by linarith [le_abs_self M]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  -- the uniform estimates for `h` and `Q`
  obtain ⟨δh, hδh, hhf⟩ := hfJ_unif L M' (m1 / 2) (by linarith)
  obtain ⟨δQ, hδQ, hQJ⟩ := QfJ_unif L M' (κ / 2) (by linarith)
  set ε : ℝ := min (min δh δQ) (min 1 (g / 2)) / 2 with hεdef
  have hεpos0 : 0 < min (min δh δQ) (min 1 (g / 2)) :=
    lt_min (lt_min hδh hδQ) (lt_min one_pos (half_pos hg))
  have hε1 : min (min δh δQ) (min 1 (g / 2)) ≤ min δh δQ := min_le_left _ _
  have hε2 : min (min δh δQ) (min 1 (g / 2)) ≤ min 1 (g / 2) := min_le_right _ _
  have hε3 : min δh δQ ≤ δh := min_le_left _ _
  have hε4 : min δh δQ ≤ δQ := min_le_right _ _
  have hε5 : min 1 (g / 2) ≤ 1 := min_le_left _ _
  have hε6 : min 1 (g / 2) ≤ g / 2 := min_le_right _ _
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεh : ε < δh := by rw [hεdef]; linarith
  have hεQ : ε < δQ := by rw [hεdef]; linarith
  have hε1' : ε ≤ 1 := by rw [hεdef]; linarith
  have hεg : ε ≤ g / 2 := by rw [hεdef]; linarith
  refine ⟨ε, hεpos, fun G' B' hG' hB' hclose => ?_⟩
  have cG : ∀ u ∈ Icc 0 L, |G' u - G u| ≤ ε := fun u hu => by
    have := (hclose 0 (by norm_num) u hu).1
    simpa using this
  have cG1 : ∀ u ∈ Icc 0 L, |d1 L G' u - d1 L G u| ≤ ε := fun u hu => (hclose 1 (by norm_num) u hu).1
  have cG2 : ∀ u ∈ Icc 0 L, |d2 L G' u - d2 L G u| ≤ ε := fun u hu => (hclose 2 le_rfl u hu).1
  have cB1 : ∀ u ∈ Icc 0 L, |d1 L B' u - d1 L B u| ≤ ε := fun u hu => (hclose 1 (by norm_num) u hu).2
  have cB2 : ∀ u ∈ Icc 0 L, |d2 L B' u - d2 L B u| ≤ ε := fun u hu => (hclose 2 le_rfl u hu).2
  have hpos' : ∀ u ∈ Icc 0 L, g / 2 ≤ G' u := fun u hu => by
    have h1 := abs_le.1 (cG u hu)
    linarith [hGg u hu]
  have hboxM : ∀ u ∈ Icc 0 L, ∀ a b : ℝ, |a| ≤ M → |b - a| ≤ ε → |b| ≤ M' := by
    intro u hu a b ha hb
    obtain ⟨h1a, h1b⟩ := abs_le.1 ha
    obtain ⟨h2a, h2b⟩ := abs_le.1 hb
    rw [abs_le]
    constructor <;> linarith [le_abs_self M]
  have hmemM : ∀ x : ℝ, |x| ≤ M' → x ∈ Icc (-M') M' := fun x hx => abs_le.1 hx
  -- closeness of `h`
  have hfclose : ∀ u ∈ Icc 0 L, |hf L G' B' u - hf L G B u| < m1 / 2 := by
    intro u hu
    rw [hf_eq_hfJ, hf_eq_hfJ]
    obtain ⟨b0, b1, b2, b3, b4⟩ := hMM' u hu
    exact hhf u hu (G u) (d1 L G u) (d1 L B u) (G' u) (d1 L G' u) (d1 L B' u)
      (hmemM _ b0) (hmemM _ b1) (hmemM _ b3)
      (hmemM _ (hboxM u hu _ _ (hM u hu).1 (cG u hu)))
      (hmemM _ (hboxM u hu _ _ (hM u hu).2.1 (cG1 u hu)))
      (hmemM _ (hboxM u hu _ _ (hM u hu).2.2.2.1 (cB1 u hu)))
      (lt_of_le_of_lt (cG u hu) hεh)
      (lt_of_le_of_lt (cG1 u hu) hεh)
      (lt_of_le_of_lt (cB1 u hu) hεh)
  -- closeness of `Q` on `I`
  have hQclose : ∀ u ∈ Icc (uc - η) (uc + η), |Qf L G' B' u - Qf L G B u| < κ / 2 := by
    intro u hu
    have huI := hI_Icc hu
    rw [Qf_eq_QfJ, Qf_eq_QfJ]
    obtain ⟨b0, b1, b2, b3, b4⟩ := hMM' u huI
    exact hQJ u huI (G u) (d1 L G u) (d2 L G u) (d1 L B u) (d2 L B u)
      (G' u) (d1 L G' u) (d2 L G' u) (d1 L B' u) (d2 L B' u)
      (hmemM _ b0) (hmemM _ b1) (hmemM _ b2) (hmemM _ b3) (hmemM _ b4)
      (hmemM _ (hboxM u huI _ _ (hM u huI).1 (cG u huI)))
      (hmemM _ (hboxM u huI _ _ (hM u huI).2.1 (cG1 u huI)))
      (hmemM _ (hboxM u huI _ _ (hM u huI).2.2.1 (cG2 u huI)))
      (hmemM _ (hboxM u huI _ _ (hM u huI).2.2.2.1 (cB1 u huI)))
      (hmemM _ (hboxM u huI _ _ (hM u huI).2.2.2.2 (cB2 u huI)))
      (lt_of_le_of_lt (cG u huI) hεQ) (lt_of_le_of_lt (cG1 u huI) hεQ)
      (lt_of_le_of_lt (cG2 u huI) hεQ) (lt_of_le_of_lt (cB1 u huI) hεQ)
      (lt_of_le_of_lt (cB2 u huI) hεQ)
  -- `Q' < 0` on `I`
  have hQneg' : ∀ u ∈ Icc (uc - η) (uc + η), Qf L G' B' u < 0 := fun u hu => by
    have h1 := (abs_sub_lt_iff.1 (hQclose u hu)).1
    have h2 := hQle u hu
    linarith
  -- signs of `h'` on the outer set
  have hout_pos : ∀ u ∈ Icc 0 (uc - η), 0 < hf L G' B' u := fun u hu => by
    have hu' : u ∈ Kout := Or.inl hu
    have hm := hm1_le u hu'
    have hs := hsign.1 u (hKout_Icc hu') (by linarith [hu.2])
    rw [abs_of_pos hs] at hm
    have h3 := (abs_sub_lt_iff.1 (hfclose u (hKout_Icc hu'))).2
    linarith
  have hout_neg : ∀ u ∈ Icc (uc + η) L, hf L G' B' u < 0 := fun u hu => by
    have hu' : u ∈ Kout := Or.inr hu
    have hm := hm1_le u hu'
    have hs := hsign.2 u (hKout_Icc hu') (by linarith [hu.1])
    rw [abs_of_neg hs] at hm
    have h3 := (abs_sub_lt_iff.1 (hfclose u (hKout_Icc hu'))).1
    linarith
  -- existence of a zero of `h'` in `I`
  have hcont' : ContinuousOn (hf L G' B') (Icc 0 L) := continuousOn_hf hL hG' hB'
  have hfa : 0 < hf L G' B' (uc - η) := hout_pos (uc - η) ⟨by linarith, le_rfl⟩
  have hfb : hf L G' B' (uc + η) < 0 := hout_neg (uc + η) ⟨by linarith, by linarith⟩
  obtain ⟨ut, hut, hfut⟩ :=
    intermediate_value_Icc' (by linarith : uc - η ≤ uc + η) (hcont'.mono hI_Icc) ⟨hfb.le, hfa.le⟩
  -- `h'` is strictly decreasing on `I`
  have hanti : StrictAntiOn (hf L G' B') (Icc (uc - η) (uc + η)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hcont'.mono hI_Icc)
    intro x hx
    rw [interior_Icc] at hx
    have hxo : x ∈ Ioo 0 L := hI_sub (Ioo_subset_Icc_self hx)
    have hE : 0 < E0 L G' x :=
      E0_pos_Ioo (fun v hv => lt_of_lt_of_le (half_pos hg) (hpos' v (Ioo_subset_Icc_self hv))) hxo
    rw [(hasDerivAt_hf hG' hB' hxo hE).deriv]
    have hQx := hQneg' x (Ioo_subset_Icc_self hx)
    rw [Qf_eq hE] at hQx
    have hs : 0 < Real.sqrt (E0 L G' x) := Real.sqrt_pos.2 hE
    nlinarith
  -- the zero set
  have hzeroF : {u ∈ Ioo 0 L | hf L G' B' u = 0} = {ut} := by
    ext u
    constructor
    · rintro ⟨hu, hz⟩
      rcases le_total u (uc - η) with h1 | h1
      · exfalso
        have := hout_pos u ⟨hu.1.le, h1⟩
        linarith
      rcases le_total (uc + η) u with h2 | h2
      · exfalso
        have := hout_neg u ⟨h2, hu.2.le⟩
        linarith
      have huI : u ∈ Icc (uc - η) (uc + η) := ⟨h1, h2⟩
      exact Set.mem_singleton_iff.2 (hanti.injOn huI hut (by rw [hz, hfut]))
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact ⟨hI_sub hut, hfut⟩
  exact ⟨ut, hI_sub hut, hzeroF, hQneg' ut hut⟩

/-- (A) gives the form of `H2` of `Hyp` (the endpoint values of `T` vanish). -/
lemma H2_of_AProp {G0 B0 : ℝ → ℝ} {L g : ℝ} (hL : 0 < L) (hG : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB : ContDiffOn ℝ 2 B0 (Icc 0 L)) (hGg : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hA : AProp L G0 B0) :
    ∀ X, Xsm L G0 B0 < X → X < Xsp L G0 B0 →
      ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ L ∧ (Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u}) = Icc a b ∧
        (0 < a → Tfun L G0 B0 X a = 0 ∧ deriv (Tfun L G0 B0 X) a ≠ 0) ∧
        (b < L → Tfun L G0 B0 X b = 0 ∧ deriv (Tfun L G0 B0 X) b ≠ 0) ∧
        (a = 0 → X = B0 0) ∧ (b = L → X = B0 L) := by
  intro X hX1 hX2
  obtain ⟨a, b, ha0, hab, hbL, hS, hda, hdb, ha0B, hbLB⟩ := hA X hX1 hX2
  have hTc : ContinuousOn (Tfun L G0 B0 X) (Icc 0 L) := by
    unfold Tfun
    exact (continuousOn_const.mul (contDiffOn_E0 hG).continuousOn).sub
      ((continuousOn_const.sub hB.continuousOn).pow 2)
  have hmemS : ∀ u ∈ Icc 0 L, u ∈ Icc a b ↔ 0 ≤ Tfun L G0 B0 X u := by
    intro u hu
    constructor
    · intro h
      have : u ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} := by rw [hS]; exact h
      exact this.2
    · intro h
      have : u ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} := ⟨hu, h⟩
      rw [hS] at this
      exact this
  refine ⟨a, b, ha0, hab, hbL, hS, ?_, ?_, ha0B, hbLB⟩
  · intro hpos
    refine ⟨?_, hda hpos⟩
    have hTa : 0 ≤ Tfun L G0 B0 X a := (hmemS a ⟨ha0, le_trans hab hbL⟩).1 ⟨le_rfl, hab⟩
    by_contra hne
    have hpos' : 0 < Tfun L G0 B0 X a := lt_of_le_of_ne hTa (Ne.symm hne)
    obtain ⟨δ, hδ, hn⟩ := cont_lower_nbhd hTc ⟨ha0, le_trans hab hbL⟩ hpos'
    have hmpos : 0 < min (δ / 2) (a / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (δ / 2) (a / 2) ≤ a / 2 := min_le_right _ _
    have hm2 : min (δ / 2) (a / 2) ≤ δ / 2 := min_le_left _ _
    have hu : a - min (δ / 2) (a / 2) ∈ Icc 0 L := ⟨by linarith, by linarith⟩
    have hd := hn _ hu (by rw [abs_lt]; constructor <;> linarith)
    have hnot : a - min (δ / 2) (a / 2) ∉ Icc a b := fun h => by linarith [h.1]
    exact hnot ((hmemS _ hu).2 (le_of_lt hd))
  · intro hpos
    refine ⟨?_, hdb hpos⟩
    have hTb : 0 ≤ Tfun L G0 B0 X b := (hmemS b ⟨le_trans ha0 hab, hbL⟩).1 ⟨hab, le_rfl⟩
    by_contra hne
    have hpos' : 0 < Tfun L G0 B0 X b := lt_of_le_of_ne hTb (Ne.symm hne)
    obtain ⟨δ, hδ, hn⟩ := cont_lower_nbhd hTc ⟨le_trans ha0 hab, hbL⟩ hpos'
    have hmpos : 0 < min (δ / 2) ((L - b) / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (δ / 2) ((L - b) / 2) ≤ (L - b) / 2 := min_le_right _ _
    have hm2 : min (δ / 2) ((L - b) / 2) ≤ δ / 2 := min_le_left _ _
    have hu : b + min (δ / 2) ((L - b) / 2) ∈ Icc 0 L := ⟨by linarith, by linarith⟩
    have hd := hn _ hu (by rw [abs_lt]; constructor <;> linarith)
    have hnot : b + min (δ / 2) ((L - b) / 2) ∉ Icc a b := fun h => by linarith [h.2]
    exact hnot ((hmemS _ hu).2 (le_of_lt hd))

/-- **lem:hyp-morse, openness** (`HypOpen`), proved. -/
theorem hypOpen : HypOpen := by
  intro L G0 B0 g hyp hG2 hB2
  have hL : 0 < L := by
    obtain ⟨uc, h0, h1, -, -⟩ := hyp.H3p
    linarith
  have hg : 0 < g := hyp.gstar_pos
  have hGg : ∀ u ∈ Icc 0 L, g ≤ G0 u := hyp.G0_lb
  have hA : AProp L G0 B0 := fun X h1 h2 => by
    obtain ⟨a, b, ha, hab, hbL, hS, hda, hdb, ha0, hbL'⟩ := hyp.H2 X h1 h2
    exact ⟨a, b, ha, hab, hbL, hS, fun h => (hda h).2, fun h => (hdb h).2, ha0, hbL'⟩
  have hBp : BpProp L G0 B0 := hyp.H3p
  have hBm : BmProp L G0 B0 := hyp.H3m
  obtain ⟨hPp, hPm⟩ := (HypMorse.hypMorseEquiv L G0 B0 g hL hg hGg hG2 hB2).2 ⟨hA, hBp, hBm⟩
  have hGpos : ∀ v ∈ Ioo 0 L, 0 < G0 v := fun v hv => lt_of_lt_of_le hg (hGg v (Ioo_subset_Icc_self hv))
  have hB2n : ContDiffOn ℝ 2 (fun u => -B0 u) (Icc 0 L) := hB2.neg
  have hHP1 := (HypMorse.pp_iff_HP hG2 hB2 hGpos).1 hPp
  have hHP2 := (HypMorse.pp_iff_HP hG2 hB2n hGpos).1 (HypMorse.Pm_iff_neg.1 hPm)
  obtain ⟨ε1, hε1, hst1⟩ := HypMorse.HP_stable hL hg hG2 hB2 hGg hHP1
  obtain ⟨ε2, hε2, hst2⟩ := HypMorse.HP_stable hL hg hG2 hB2n hGg hHP2
  have hεpos : 0 < min (min ε1 ε2) (g / 2) := lt_min (lt_min hε1 hε2) (half_pos hg)
  have hε_le1 : min (min ε1 ε2) (g / 2) ≤ ε1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε_le2 : min (min ε1 ε2) (g / 2) ≤ ε2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_leg : min (min ε1 ε2) (g / 2) ≤ g / 2 := min_le_right _ _
  refine ⟨min (min ε1 ε2) (g / 2), hεpos, fun G0' B0' hG' hB' hclose => ?_⟩
  have hcl1 : ∀ i ≤ 2, ∀ u ∈ Icc 0 L,
      |iteratedDerivWithin i G0' (Icc 0 L) u - iteratedDerivWithin i G0 (Icc 0 L) u| ≤ ε1 ∧
      |iteratedDerivWithin i B0' (Icc 0 L) u - iteratedDerivWithin i B0 (Icc 0 L) u| ≤ ε1 := fun i hi u hu =>
    ⟨le_trans (hclose i hi u hu).1 hε_le1, le_trans (hclose i hi u hu).2 hε_le1⟩
  have hnegB : ∀ i u, iteratedDerivWithin i (fun u => -B0' u) (Icc 0 L) u =
      -iteratedDerivWithin i B0' (Icc 0 L) u := fun i u => by
    show iteratedDerivWithin i (-B0') (Icc 0 L) u = _
    exact iteratedDerivWithin_neg B0'
  have hnegB0 : ∀ i u, iteratedDerivWithin i (fun u => -B0 u) (Icc 0 L) u =
      -iteratedDerivWithin i B0 (Icc 0 L) u := fun i u => by
    show iteratedDerivWithin i (-B0) (Icc 0 L) u = _
    exact iteratedDerivWithin_neg B0
  have hcl2 : ∀ i ≤ 2, ∀ u ∈ Icc 0 L,
      |iteratedDerivWithin i G0' (Icc 0 L) u - iteratedDerivWithin i G0 (Icc 0 L) u| ≤ ε2 ∧
      |iteratedDerivWithin i (fun u => -B0' u) (Icc 0 L) u -
        iteratedDerivWithin i (fun u => -B0 u) (Icc 0 L) u| ≤ ε2 := fun i hi u hu => by
    refine ⟨le_trans (hclose i hi u hu).1 hε_le2, ?_⟩
    rw [hnegB, hnegB0, neg_sub_neg, abs_sub_comm]
    exact le_trans (hclose i hi u hu).2 hε_le2
  have hB2n' : ContDiffOn ℝ 2 (fun u => -B0' u) (Icc 0 L) := hB'.neg
  have hH1 := hst1 G0' B0' hG' hB' hcl1
  have hH2 := hst2 G0' (fun u => -B0' u) hG' hB2n' hcl2
  have hG0'lb : ∀ u ∈ Icc 0 L, g / 2 ≤ G0' u := by
    intro u hu
    have h1 := abs_le.1 (hclose 0 (by norm_num) u hu).1
    have h2 : iteratedDerivWithin 0 G0' (Icc 0 L) u = G0' u := by simp
    have h3 : iteratedDerivWithin 0 G0 (Icc 0 L) u = G0 u := by simp
    have := (hclose 0 (by norm_num) u hu).1
    rw [h2, h3] at this
    have h4 := abs_le.1 this
    linarith [hGg u hu, h4.1]
  have hGpos' : ∀ v ∈ Ioo 0 L, 0 < G0' v := fun v hv =>
    lt_of_lt_of_le (half_pos hg) (hG0'lb v (Ioo_subset_Icc_self hv))
  have hPp' : PpProp L G0' B0' := (HypMorse.pp_iff_HP hG' hB' hGpos').2 hH1
  have hPpn : PpProp L G0' (fun u => -B0' u) := (HypMorse.pp_iff_HP hG' hB2n' hGpos').2 hH2
  have hPm' : PmProp L G0' B0' := HypMorse.Pm_iff_neg.2 hPpn
  obtain ⟨hA', hBp', hBm'⟩ :=
    (HypMorse.hypMorseEquiv L G0' B0' (g / 2) hL (half_pos hg) hG0'lb hG' hB').1 ⟨hPp', hPm'⟩
  exact ⟨half_pos hg, hG0'lb, HypMorse.H2_of_AProp hL hG' hB' hG0'lb (half_pos hg) hA', hBp', hBm'⟩

/-! ### L2.G3: the frozen family and the uniform openness over a compact parameter set -/

/-- Local uniformity in the parameter: a continuous family on `K × [0, L]` is uniformly close to its value at `μ0` in `s`,
for `μ` near `μ0` in `K`. -/
lemma eventually_uniform_close {Par : Type*} [TopologicalSpace Par] {K : Set Par} {L : ℝ}
    (hK : IsCompact K) (f : Par → ℝ → ℝ) (hf : ContinuousOn (fun p : Par × ℝ => f p.1 p.2) (K ×ˢ Icc 0 L))
    {μ0 : Par} (hμ0 : μ0 ∈ K) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ μ in 𝓝 μ0, μ ∈ K → ∀ s ∈ Icc 0 L, |f μ s - f μ0 s| < η := by
  have key : ∀ᶠ μ in 𝓝 μ0, ∀ s ∈ Icc 0 L, (μ ∈ K → s ∈ Icc 0 L → |f μ s - f μ0 s| < η) := by
    apply (isCompact_Icc (a := 0) (b := L)).eventually_forall_of_forall_eventually
    intro s hs
    have h2 : ContinuousOn (fun p : Par × ℝ => f μ0 p.2) (K ×ˢ Icc 0 L) := by
      have h : ContinuousOn (fun s' : ℝ => f μ0 s') (Icc 0 L) :=
        hf.comp (f := fun s' : ℝ => (μ0, s')) (continuousOn_const.prodMk continuousOn_id)
          (fun x hx => ⟨hμ0, hx⟩)
      exact h.comp continuousOn_snd (fun p hp => hp.2)
    have hc : ContinuousWithinAt (fun p : Par × ℝ => f p.1 p.2 - f μ0 p.2) (K ×ˢ Icc 0 L) (μ0, s) :=
      (hf (μ0, s) ⟨hμ0, hs⟩).sub (h2 (μ0, s) ⟨hμ0, hs⟩)
    have ht : Tendsto (fun p : Par × ℝ => f p.1 p.2 - f μ0 p.2) (𝓝[K ×ˢ Icc 0 L] (μ0, s)) (𝓝 0) := by
      have := hc
      simpa [ContinuousWithinAt] using this
    have hev := eventually_nhdsWithin_iff.1 (ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hη))
    filter_upwards [hev] with z hz
    intro hzK hzI
    have := hz ⟨hzK, hzI⟩
    rw [Real.dist_eq, sub_zero] at this
    exact this
  filter_upwards [key] with μ hμ hμK s hs
  exact hμ s hs hμK hs

/-- A family of neighbourhoods of `t = 0` uniform in a compact parameter set. -/
lemma uniform_in_param {Par : Type*} [TopologicalSpace Par] {K : Set Par} (hK : IsCompact K)
    {Q : ℝ → Par → Prop} (h : ∀ μ0 ∈ K, ∀ᶠ z in 𝓝 ((0 : ℝ), μ0), Q z.1 z.2) :
    ∃ t0 > 0, ∀ t : ℝ, |t| < t0 → ∀ μ ∈ K, Q t μ := by
  have h' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ μ ∈ K, Q t μ :=
    hK.eventually_forall_of_forall_eventually (fun μ hμ => h μ hμ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h'
  refine ⟨ε, hε, fun t ht μ hμ => hball ?_ μ hμ⟩
  rw [Real.dist_eq, sub_zero]
  exact ht

/-- Linearity of the iterated within-derivatives in a linear combination (for `i ≤ 2`). -/
lemma iter_lin {f g : ℝ → ℝ} {L t s : ℝ} {i : ℕ} (hL : 0 < L) (hf : ContDiffOn ℝ 2 f (Icc 0 L))
    (hg : ContDiffOn ℝ 2 g (Icc 0 L)) (hs : s ∈ Icc 0 L) (hi : i ≤ 2) :
    iteratedDerivWithin i (fun x => f x + t * g x) (Icc 0 L) s =
      iteratedDerivWithin i f (Icc 0 L) s + t * iteratedDerivWithin i g (Icc 0 L) s := by
  have hu := uniqueDiffOn_Icc hL
  have hi2 : (i : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hi
  have hfi : ContDiffWithinAt ℝ (i : WithTop ℕ∞) f (Icc 0 L) s := (hf.of_le hi2).contDiffWithinAt hs
  have hgi : ContDiffWithinAt ℝ (i : WithTop ℕ∞) g (Icc 0 L) s := (hg.of_le hi2).contDiffWithinAt hs
  have hgt : ContDiffWithinAt ℝ (i : WithTop ℕ∞) (fun x => t * g x) (Icc 0 L) s :=
    contDiffWithinAt_const.mul hgi
  have e1 : (fun x => f x + t * g x) = f + (fun x => t * g x) := rfl
  rw [e1, iteratedDerivWithin_add hs hu hfi hgt, iteratedDerivWithin_const_mul hs hu t hgi]

/-- **Uniform openness** over a compact parameter set: the perturbations `A0 μ + t A1 μ` (`t` small, `μ ∈ K`) of the
principal symbols keep `Hyp` with `g/2`, if `Hyp` holds at each `μ ∈ K` with one `g` (the jets are continuous on `K × [0, L]`). -/
lemma hyp_uniform {Par : Type*} [TopologicalSpace Par] {K : Set Par} {L g : ℝ} (hL : 0 < L) (hK : IsCompact K)
    (A0 A1 B0 B1 : Par → ℝ → ℝ)
    (hC2 : ∀ μ ∈ K, ContDiffOn ℝ 2 (A0 μ) (Icc 0 L) ∧ ContDiffOn ℝ 2 (A1 μ) (Icc 0 L) ∧
      ContDiffOn ℝ 2 (B0 μ) (Icc 0 L) ∧ ContDiffOn ℝ 2 (B1 μ) (Icc 0 L))
    (hcont : ∀ i ≤ 2, ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (A0 p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (A1 p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (B0 p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (B1 p.1) (Icc 0 L) p.2) (K ×ˢ Icc 0 L))
    (hHyp : ∀ μ ∈ K, Hyp L (A0 μ) (B0 μ) g) :
    ∃ t0 > 0, ∀ t : ℝ, |t| < t0 → ∀ μ ∈ K,
      Hyp L (fun s => A0 μ s + t * A1 μ s) (fun s => B0 μ s + t * B1 μ s) (g / 2) := by
  -- a common bound for the derivatives of `A1, B1` of order `≤ 2` on `K × [0, L]`
  have hS : IsCompact (K ×ˢ Icc 0 L) := hK.prod isCompact_Icc
  obtain ⟨c0A, hc0A⟩ := hS.exists_bound_of_continuousOn (hcont 0 (by norm_num)).2.1
  obtain ⟨c1A, hc1A⟩ := hS.exists_bound_of_continuousOn (hcont 1 (by norm_num)).2.1
  obtain ⟨c2A, hc2A⟩ := hS.exists_bound_of_continuousOn (hcont 2 le_rfl).2.1
  obtain ⟨c0B, hc0B⟩ := hS.exists_bound_of_continuousOn (hcont 0 (by norm_num)).2.2.2
  obtain ⟨c1B, hc1B⟩ := hS.exists_bound_of_continuousOn (hcont 1 (by norm_num)).2.2.2
  obtain ⟨c2B, hc2B⟩ := hS.exists_bound_of_continuousOn (hcont 2 le_rfl).2.2.2
  set CB : ℝ := |c0A| + |c1A| + |c2A| + |c0B| + |c1B| + |c2B| + 1 with hCB
  have hCBpos : 0 < CB := by
    rw [hCB]
    have := abs_nonneg c0A; have := abs_nonneg c1A; have := abs_nonneg c2A
    have := abs_nonneg c0B; have := abs_nonneg c1B; have := abs_nonneg c2B
    linarith
  have hbound : ∀ μ ∈ K, ∀ s ∈ Icc 0 L, ∀ i ≤ 2,
      |iteratedDerivWithin i (A1 μ) (Icc 0 L) s| ≤ CB ∧ |iteratedDerivWithin i (B1 μ) (Icc 0 L) s| ≤ CB := by
    intro μ hμ s hs i hi
    have hp : (μ, s) ∈ K ×ˢ Icc 0 L := ⟨hμ, hs⟩
    have a0 := abs_nonneg c0A
    have a1 := abs_nonneg c1A
    have a2 := abs_nonneg c2A
    have b0 := abs_nonneg c0B
    have b1 := abs_nonneg c1B
    have b2 := abs_nonneg c2B
    have hA : |iteratedDerivWithin i (A1 μ) (Icc 0 L) s| ≤ CB := by
      interval_cases i
      · have := hc0A (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c0A]
      · have := hc1A (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c1A]
      · have := hc2A (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c2A]
    have hB : |iteratedDerivWithin i (B1 μ) (Icc 0 L) s| ≤ CB := by
      interval_cases i
      · have := hc0B (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c0B]
      · have := hc1B (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c1B]
      · have := hc2B (μ, s) hp
        simp only [Real.norm_eq_abs] at this
        rw [hCB]; linarith [le_abs_self c2B]
    exact ⟨hA, hB⟩
  -- the local statement at each `μ0 ∈ K`
  have hloc : ∀ μ0 ∈ K, ∀ᶠ z in 𝓝 ((0 : ℝ), μ0), (z.2 ∈ K →
      Hyp L (fun s => A0 z.2 s + z.1 * A1 z.2 s) (fun s => B0 z.2 s + z.1 * B1 z.2 s) (g / 2)) := by
    intro μ0 hμ0
    obtain ⟨ε0, hε0, hH⟩ := hypOpen L (A0 μ0) (B0 μ0) g (hHyp μ0 hμ0) (hC2 μ0 hμ0).1 (hC2 μ0 hμ0).2.2.1
    have hη : 0 < ε0 / 4 := by positivity
    have hcloseA : ∀ i ≤ 2, ∀ᶠ μ in 𝓝 μ0, μ ∈ K → ∀ s ∈ Icc 0 L,
        |iteratedDerivWithin i (A0 μ) (Icc 0 L) s - iteratedDerivWithin i (A0 μ0) (Icc 0 L) s| < ε0 / 4 :=
      fun i hi => eventually_uniform_close hK (fun μ s => iteratedDerivWithin i (A0 μ) (Icc 0 L) s)
        (hcont i hi).1 hμ0 hη
    have hcloseB : ∀ i ≤ 2, ∀ᶠ μ in 𝓝 μ0, μ ∈ K → ∀ s ∈ Icc 0 L,
        |iteratedDerivWithin i (B0 μ) (Icc 0 L) s - iteratedDerivWithin i (B0 μ0) (Icc 0 L) s| < ε0 / 4 :=
      fun i hi => eventually_uniform_close hK (fun μ s => iteratedDerivWithin i (B0 μ) (Icc 0 L) s)
        (hcont i hi).2.2.1 hμ0 hη
    have hμev : ∀ᶠ μ in 𝓝 μ0, μ ∈ K → ∀ i ≤ 2, ∀ s ∈ Icc 0 L,
        |iteratedDerivWithin i (A0 μ) (Icc 0 L) s - iteratedDerivWithin i (A0 μ0) (Icc 0 L) s| < ε0 / 4 ∧
        |iteratedDerivWithin i (B0 μ) (Icc 0 L) s - iteratedDerivWithin i (B0 μ0) (Icc 0 L) s| < ε0 / 4 := by
      have h0 := (hcloseA 0 (by norm_num)).and (hcloseB 0 (by norm_num))
      have h1 := (hcloseA 1 (by norm_num)).and (hcloseB 1 (by norm_num))
      have h2 := (hcloseA 2 le_rfl).and (hcloseB 2 le_rfl)
      filter_upwards [h0, h1, h2] with μ a0 a1 a2 hμK i hi s hs
      interval_cases i
      · exact ⟨a0.1 hμK s hs, a0.2 hμK s hs⟩
      · exact ⟨a1.1 hμK s hs, a1.2 hμK s hs⟩
      · exact ⟨a2.1 hμK s hs, a2.2 hμK s hs⟩
    have hτpos : 0 < ε0 / (4 * CB) := by positivity
    have hτ_ev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ε0 / (4 * CB) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hτpos] with t ht
      simpa [Real.dist_eq] using ht
    filter_upwards [(continuous_fst.tendsto ((0 : ℝ), μ0)).eventually hτ_ev,
      (continuous_snd.tendsto ((0 : ℝ), μ0)).eventually hμev] with z hzt hzμ hzK
    have hzt' : |z.1| < ε0 / (4 * CB) := hzt
    have hC := hC2 z.2 hzK
    apply hH _ _ (hC.1.add (contDiffOn_const.mul hC.2.1)) (hC.2.2.1.add (contDiffOn_const.mul hC.2.2.2))
    intro i hi s hs
    have hlinA := iter_lin hL hC.1 hC.2.1 hs hi (t := z.1)
    have hlinB := iter_lin hL hC.2.2.1 hC.2.2.2 hs hi (t := z.1)
    have hdecA : iteratedDerivWithin i (fun s => A0 z.2 s + z.1 * A1 z.2 s) (Icc 0 L) s -
        iteratedDerivWithin i (A0 μ0) (Icc 0 L) s =
        (iteratedDerivWithin i (A0 z.2) (Icc 0 L) s - iteratedDerivWithin i (A0 μ0) (Icc 0 L) s) +
          z.1 * iteratedDerivWithin i (A1 z.2) (Icc 0 L) s := by
      rw [hlinA]; ring
    have hdecB : iteratedDerivWithin i (fun s => B0 z.2 s + z.1 * B1 z.2 s) (Icc 0 L) s -
        iteratedDerivWithin i (B0 μ0) (Icc 0 L) s =
        (iteratedDerivWithin i (B0 z.2) (Icc 0 L) s - iteratedDerivWithin i (B0 μ0) (Icc 0 L) s) +
          z.1 * iteratedDerivWithin i (B1 z.2) (Icc 0 L) s := by
      rw [hlinB]; ring
    obtain ⟨pA, pB⟩ := hzμ hzK i hi s hs
    obtain ⟨bA, bB⟩ := hbound z.2 hzK s hs i hi
    have hτCB : ε0 / (4 * CB) * CB = ε0 / 4 := by field_simp
    have hmulA : |z.1 * iteratedDerivWithin i (A1 z.2) (Icc 0 L) s| ≤ ε0 / 4 := by
      rw [abs_mul]
      have h1 : |z.1| * |iteratedDerivWithin i (A1 z.2) (Icc 0 L) s| ≤ |z.1| * CB :=
        mul_le_mul_of_nonneg_left bA (abs_nonneg _)
      have h2 : |z.1| * CB ≤ ε0 / (4 * CB) * CB := mul_le_mul_of_nonneg_right hzt'.le hCBpos.le
      linarith
    have hmulB : |z.1 * iteratedDerivWithin i (B1 z.2) (Icc 0 L) s| ≤ ε0 / 4 := by
      rw [abs_mul]
      have h1 : |z.1| * |iteratedDerivWithin i (B1 z.2) (Icc 0 L) s| ≤ |z.1| * CB :=
        mul_le_mul_of_nonneg_left bB (abs_nonneg _)
      have h2 : |z.1| * CB ≤ ε0 / (4 * CB) * CB := mul_le_mul_of_nonneg_right hzt'.le hCBpos.le
      linarith
    constructor
    · rw [hdecA]
      have := abs_add_le ((iteratedDerivWithin i (A0 z.2) (Icc 0 L) s - iteratedDerivWithin i (A0 μ0) (Icc 0 L) s))
        (z.1 * iteratedDerivWithin i (A1 z.2) (Icc 0 L) s)
      linarith [pA.le]
    · rw [hdecB]
      have := abs_add_le ((iteratedDerivWithin i (B0 z.2) (Icc 0 L) s - iteratedDerivWithin i (B0 μ0) (Icc 0 L) s))
        (z.1 * iteratedDerivWithin i (B1 z.2) (Icc 0 L) s)
      linarith [pB.le]
  obtain ⟨t0, ht0, hT⟩ := uniform_in_param hK
    (Q := fun t μ => μ ∈ K → Hyp L (fun s => A0 μ s + t * A1 μ s) (fun s => B0 μ s + t * B1 μ s) (g / 2)) hloc
  exact ⟨t0, ht0, fun t ht μ hμ => hT t ht μ hμ hμ⟩

/-- `iter_lin` with a general regularity index `n ≥ i`. -/
lemma iter_lin' {f g : ℝ → ℝ} {L t s : ℝ} {n i : ℕ} (hL : 0 < L) (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Icc 0 L))
    (hg : ContDiffOn ℝ (n : WithTop ℕ∞) g (Icc 0 L)) (hs : s ∈ Icc 0 L) (hi : i ≤ n) :
    iteratedDerivWithin i (fun x => f x + t * g x) (Icc 0 L) s =
      iteratedDerivWithin i f (Icc 0 L) s + t * iteratedDerivWithin i g (Icc 0 L) s := by
  have hu := uniqueDiffOn_Icc hL
  have hi2 : (i : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hi
  have hfi : ContDiffWithinAt ℝ (i : WithTop ℕ∞) f (Icc 0 L) s := (hf.of_le hi2).contDiffWithinAt hs
  have hgi : ContDiffWithinAt ℝ (i : WithTop ℕ∞) g (Icc 0 L) s := (hg.of_le hi2).contDiffWithinAt hs
  have hgt : ContDiffWithinAt ℝ (i : WithTop ℕ∞) (fun x => t * g x) (Icc 0 L) s :=
    contDiffWithinAt_const.mul hgi
  have e1 : (fun x => f x + t * g x) = f + (fun x => t * g x) := rfl
  rw [e1, iteratedDerivWithin_add hs hu hfi hgt, iteratedDerivWithin_const_mul hs hu t hgi]

/-- The even-odd splitting of a finite sum over `range (2n)`. -/
lemma sum_range_two_mul_split (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The frozen symbol at an even index `2j ≤ 2K`: `G_{2j}(μ) + t G_{2j+1}(μ)`. -/
lemma frozen_G_eq {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (Kidx j : ℕ) (hj : j ≤ Kidx)
    (ν : Par × ℝ) :
    (frozenFamily F Kidx).G (2 * j) ν = fun s => F.G (2 * j) ν.1 s + ν.2 * F.G (2 * j + 1) ν.1 s := by
  funext s
  simp only [frozenFamily]
  rw [ite_eq_left (show 2 * j % 2 = 0 ∧ 2 * j ≤ 2 * Kidx from ⟨by omega, by omega⟩)]

lemma frozen_B_eq {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (Kidx j : ℕ) (hj : j ≤ Kidx)
    (ν : Par × ℝ) :
    (frozenFamily F Kidx).B (2 * j) ν = fun s => F.B (2 * j) ν.1 s + ν.2 * F.B (2 * j + 1) ν.1 s := by
  funext s
  simp only [frozenFamily]
  rw [ite_eq_left (show 2 * j % 2 = 0 ∧ 2 * j ≤ 2 * Kidx from ⟨by omega, by omega⟩)]

/-- The jets of `s ↦ f(μ)(s) + t g(μ)(s)` on `K × [-t0, t0]` (regularity `n`). -/
lemma jetReg_comb {Par : Type*} [TopologicalSpace Par] {K : Set Par} {L : ℝ} {n : ℕ} (hL : 0 < L) (t0 : ℝ)
    {f g : Par → ℝ → ℝ} (hf : JetReg f K L n) (hg : JetReg g K L n) :
    JetReg (fun ν : Par × ℝ => fun s => f ν.1 s + ν.2 * g ν.1 s) (paramSet K t0) L n := by
  refine ⟨fun ν hν => ?_, fun i hi => ?_⟩
  · have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (f ν.1) (Icc 0 L) := hf.1 ν.1 hν.1
    have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (g ν.1) (Icc 0 L) := hg.1 ν.1 hν.1
    exact h1.add (contDiffOn_const.mul h2)
  · have hA : ContinuousOn (fun p : (Par × ℝ) × ℝ => iteratedDerivWithin i (f p.1.1) (Icc 0 L) p.2)
        (paramSet K t0 ×ˢ Icc 0 L) := by
      have hmap : MapsTo (fun p : (Par × ℝ) × ℝ => (p.1.1, p.2)) (paramSet K t0 ×ˢ Icc 0 L) (K ×ˢ Icc 0 L) :=
        fun p hp => ⟨hp.1.1, hp.2⟩
      exact (hf.2 i hi).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn hmap
    have hB : ContinuousOn (fun p : (Par × ℝ) × ℝ => iteratedDerivWithin i (g p.1.1) (Icc 0 L) p.2)
        (paramSet K t0 ×ˢ Icc 0 L) := by
      have hmap : MapsTo (fun p : (Par × ℝ) × ℝ => (p.1.1, p.2)) (paramSet K t0 ×ˢ Icc 0 L) (K ×ˢ Icc 0 L) :=
        fun p hp => ⟨hp.1.1, hp.2⟩
      exact (hg.2 i hi).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn hmap
    have hT : ContinuousOn (fun p : (Par × ℝ) × ℝ => p.1.2 * iteratedDerivWithin i (g p.1.1) (Icc 0 L) p.2)
        (paramSet K t0 ×ˢ Icc 0 L) :=
      ((continuous_snd.comp continuous_fst).continuousOn).mul hB
    refine (hA.add hT).congr (fun p hp => ?_)
    exact iter_lin' (n := n) hL (hf.1 p.1.1 hp.1.1) (hg.1 p.1.1 hp.1.1) hp.2 hi

/-- The remainder identity of the frozen family (`G`-part). -/
lemma frozen_identity_G {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : ℕ) (ν : Par × ℝ) (h s : ℝ) :
    (frozenFamily F K).Gh ν h s - ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * (frozenFamily F K).G (2 * j) ν s
      = F.Gh ν.1 h s - ∑ i ∈ Finset.range (2 * K + 1 + 1), h ^ i * F.G i ν.1 s := by
  have hA : ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * (frozenFamily F K).G (2 * j) ν s =
      ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.G (2 * j) ν.1 s +
        ν.2 * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.G (2 * j + 1) ν.1 s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [congrFun (frozen_G_eq F K j hj' ν) s]
    ring
  have hB : ∑ i ∈ Finset.range (2 * K + 1 + 1), h ^ i * F.G i ν.1 s =
      ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.G (2 * j) ν.1 s +
        h * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.G (2 * j + 1) ν.1 s := by
    have hsplit := sum_range_two_mul_split (fun i => h ^ i * F.G i ν.1 s) (K + 1)
    rw [show 2 * K + 1 + 1 = 2 * (K + 1) by ring]
    rw [hsplit, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hGh : (frozenFamily F K).Gh ν h s =
      F.Gh ν.1 h s + (ν.2 - h) * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.G (2 * j + 1) ν.1 s := rfl
  rw [hA, hB, hGh]
  ring

/-- The remainder identity of the frozen family (`B`-part). -/
lemma frozen_identity_B {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : ℕ) (ν : Par × ℝ) (h s : ℝ) :
    (frozenFamily F K).Bh ν h s - ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * (frozenFamily F K).B (2 * j) ν s
      = F.Bh ν.1 h s - ∑ i ∈ Finset.range (2 * K + 1 + 1), h ^ i * F.B i ν.1 s := by
  have hA : ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * (frozenFamily F K).B (2 * j) ν s =
      ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.B (2 * j) ν.1 s +
        ν.2 * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.B (2 * j + 1) ν.1 s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [congrFun (frozen_B_eq F K j hj' ν) s]
    ring
  have hB : ∑ i ∈ Finset.range (2 * K + 1 + 1), h ^ i * F.B i ν.1 s =
      ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.B (2 * j) ν.1 s +
        h * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.B (2 * j + 1) ν.1 s := by
    have hsplit := sum_range_two_mul_split (fun i => h ^ i * F.B i ν.1 s) (K + 1)
    rw [show 2 * K + 1 + 1 = 2 * (K + 1) by ring]
    rw [hsplit, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBh : (frozenFamily F K).Bh ν h s =
      F.Bh ν.1 h s + (ν.2 - h) * ∑ j ∈ Finset.range (K + 1), h ^ (2 * j) * F.B (2 * j + 1) ν.1 s := rfl
  rw [hA, hB, hBh]
  ring

/-- **The part of `(D_{2 Kidx+1})` that `sec:tha-standing` uses** (finding F-S6-7).  For the jets `G_{2j}, G_{2j+1}, B_{2j}, B_{2j+1}` (`j <= Kidx`) the regularity `C^{r - 10 j}` with
`r >= regBudget (max (2 Kidx - 1) 0)` (so `C^2` and continuity for the jets `0, 1`), and the remainder `G_h - sum_{i <= 2 Kidx + 1} h^i G_i = O(h^{2 Kidx + 2})`.  `DM F K (2 Kidx + 1)` gives it with
`r = regBudget (2 Kidx + 1)` (`frozenReg_of_dm`); the truncated family `tilde J_h^{[M]}` (jets `0` beyond `M`, no remainder), which has only `(D_M)`, `M >= 2 Kidx - 1`, satisfies it with `r = regBudget M`
(`frozenReg_trunc`, `TheoremA/SpectrumAssemblyBulk.lean`). -/
structure FrozenReg {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx r : ℕ) : Prop where
  budget : regBudget (max (2 * Kidx - 1) 0) ≤ r
  reg : ∀ j ≤ Kidx, JetReg (F.G (2 * j)) K F.L (r - 10 * j) ∧ JetReg (F.B (2 * j)) K F.L (r - 10 * j) ∧
    JetReg (F.G (2 * j + 1)) K F.L (r - 10 * j) ∧ JetReg (F.B (2 * j + 1)) K F.L (r - 10 * j)
  rem : ∃ C : ℝ, ∀ μ ∈ K, ∀ N : ℕ, ∀ s ∈ Icc 0 F.L,
    |F.Gh μ (F.step N) s - ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), F.step N ^ i * F.G i μ s| ≤ C * F.step N ^ (2 * Kidx + 2) ∧
    |F.Bh μ (F.step N) s - ∑ i ∈ Finset.range (2 * Kidx + 1 + 1), F.step N ^ i * F.B i μ s| ≤ C * F.step N ^ (2 * Kidx + 2)

/-- `DM F K (2 Kidx + 1)` gives `FrozenReg` (with `r = regBudget (2 Kidx + 1)`). -/
theorem frozenReg_of_dm {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ}
    (hDM : DM F K (2 * Kidx + 1)) : FrozenReg F K Kidx (regBudget (2 * Kidx + 1)) := by
  refine ⟨?_, fun j hj => ?_, hDM.rem⟩
  · unfold regBudget; omega
  · have hG := hDM.reg (2 * j) (by omega)
    have hG1 := hDM.reg (2 * j + 1) (by omega)
    have e1 : (2 * j) / 2 = j := by omega
    have e2 : (2 * j + 1) / 2 = j := by omega
    rw [e1] at hG
    rw [e2] at hG1
    exact ⟨hG.1, hG.2, hG1.1, hG1.2⟩

/-- `(E_K)` for the frozen family on `paramSet K t0`, with the regularity `r` of `FrozenReg`. -/
lemma EK_frozen_of_reg {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx r : ℕ} (t0 : ℝ)
    (hR : FrozenReg F K Kidx r) : EK (frozenFamily F Kidx) (paramSet K t0) Kidx r := by
  refine EK.mk hR.budget ?_ ?_
  · intro j hj
    have hG := hR.reg j hj
    have hfunG : (frozenFamily F Kidx).G (2 * j) =
        fun ν : Par × ℝ => fun s => F.G (2 * j) ν.1 s + ν.2 * F.G (2 * j + 1) ν.1 s :=
      funext (fun ν => frozen_G_eq F Kidx j hj ν)
    have hfunB : (frozenFamily F Kidx).B (2 * j) =
        fun ν : Par × ℝ => fun s => F.B (2 * j) ν.1 s + ν.2 * F.B (2 * j + 1) ν.1 s :=
      funext (fun ν => frozen_B_eq F Kidx j hj ν)
    rw [hfunG, hfunB]
    exact ⟨jetReg_comb F.L_pos t0 hG.1 hG.2.2.1, jetReg_comb F.L_pos t0 hG.2.1 hG.2.2.2⟩
  · obtain ⟨C, hC⟩ := hR.rem
    refine ⟨C, fun ν hν N s hs => ?_⟩
    obtain ⟨hG, hB⟩ := hC ν.1 hν.1 N s hs
    constructor
    · have e := frozen_identity_G F Kidx ν (F.step N) s
      rw [show (frozenFamily F Kidx).step N = F.step N from rfl, e]
      exact hG
    · have e := frozen_identity_B F Kidx ν (F.step N) s
      rw [show (frozenFamily F Kidx).step N = F.step N from rfl, e]
      exact hB

/-- **sec:tha-standing** under the weakened hypothesis `FrozenReg` (finding F-S6-7): for compact `K`, `(H1)`--`(H3)` on `K` and `FrozenReg F K Kidx r`, there is `t0 > 0` such that the frozen
family satisfies `(E_Kidx)` with regularity `r`, and `(H1)`--`(H3)` uniformly on `K x [-t0, t0]`.  Applies to the truncated family `tilde J_h^{[M]}`, which satisfies only `(D_M)`. -/
theorem frozenStandard_of_reg {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx r : ℕ)
    (hK : IsCompact K) (hHypOn : HypOn F K) (hR : FrozenReg F K Kidx r) :
    ∃ t0 : ℝ, 0 < t0 ∧ StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r := by
  obtain ⟨g0, hg0⟩ := hHypOn
  have hreg0 : ∀ μ ∈ K, ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) ∧ ContDiffOn ℝ 2 (F.G 1 μ) (Icc 0 F.L) ∧
      ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) ∧ ContDiffOn ℝ 2 (F.B 1 μ) (Icc 0 F.L) := by
    intro μ hμ
    have hJ := hR.reg 0 (Nat.zero_le _)
    have h2 : (2 : WithTop ℕ∞) ≤ ((r - 10 * 0 : ℕ) : WithTop ℕ∞) := by
      have : (2 : ℕ) ≤ r - 10 * 0 := by
        have := hR.budget
        unfold regBudget at this
        omega
      exact_mod_cast this
    simp only [mul_zero, add_zero] at hJ
    exact ⟨(hJ.1.1 μ hμ).of_le h2, (hJ.2.2.1.1 μ hμ).of_le h2, (hJ.2.1.1 μ hμ).of_le h2, (hJ.2.2.2.1 μ hμ).of_le h2⟩
  have hcont : ∀ i ≤ 2, ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (F.G 0 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (F.G 1 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (F.B 0 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) ∧
      ContinuousOn (fun p : Par × ℝ => iteratedDerivWithin i (F.B 1 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) := by
    intro i hi
    have hle : i ≤ r - 10 * 0 := by
      have := hR.budget
      unfold regBudget at this
      omega
    have hJ := hR.reg 0 (Nat.zero_le _)
    simp only [mul_zero, add_zero] at hJ
    exact ⟨hJ.1.2 i (by simpa using hle), hJ.2.2.1.2 i (by simpa using hle), hJ.2.1.2 i (by simpa using hle),
      hJ.2.2.2.2 i (by simpa using hle)⟩
  obtain ⟨t0, ht0, hT⟩ := hyp_uniform F.L_pos hK (fun μ => F.G 0 μ) (fun μ => F.G 1 μ) (fun μ => F.B 0 μ)
    (fun μ => F.B 1 μ) (fun μ hμ => hreg0 μ hμ) (fun i hi => hcont i hi) (fun μ hμ => hg0 μ hμ)
  refine ⟨t0 / 2, by positivity, ⟨?_, EK_frozen_of_reg (t0 / 2) hR, ?_⟩⟩
  · exact hK.prod isCompact_Icc
  · refine ⟨g0 / 2, fun ν hν => ?_⟩
    obtain ⟨hμ, ht⟩ := hν
    have hf0 : (frozenFamily F Kidx).G 0 ν = fun s => F.G 0 ν.1 s + ν.2 * F.G 1 ν.1 s := by
      have := frozen_G_eq F Kidx 0 (Nat.zero_le _) ν
      simpa using this
    have hb0 : (frozenFamily F Kidx).B 0 ν = fun s => F.B 0 ν.1 s + ν.2 * F.B 1 ν.1 s := by
      have := frozen_B_eq F Kidx 0 (Nat.zero_le _) ν
      simpa using this
    rw [hf0, hb0]
    have hab : |ν.2| < t0 := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    exact hT ν.2 hab ν.1 hμ

/-- **sec:tha-standing** (`FrozenStandard`), proved: the frozen family satisfies `(E_K)` and `(H1)`--`(H3)` on
`K × [-t0, t0]` for a suitable `t0 > 0`.  (The corollary of `frozenStandard_of_reg` for `DM F K (2 Kidx + 1)`.) -/
theorem frozenStandard {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) :
    FrozenStandard F K Kidx := by
  intro hK hHypOn hDM
  obtain ⟨t0, ht0, h⟩ := frozenStandard_of_reg F K Kidx _ hK hHypOn (frozenReg_of_dm hDM)
  exact ⟨t0, ht0, _, h⟩

/-! ### L2.G4 (a): the bulk statement `GeomBulk` -/

lemma hasDerivAt_Tfun_of_mem (hG : ∀ u ∈ Icc 0 L, g ≤ G0 u) (hg : 0 < g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (X : ℝ) {c : ℝ} (hc : c ∈ Ioo 0 L) :
    HasDerivAt (Tfun L G0 B0 X) (deriv (fPlus L G0 B0) c * (X - fMinus L G0 B0 c) +
      (fPlus L G0 B0 c - X) * (0 - deriv (fMinus L G0 B0) c)) c := by
  have hfpd := fPlus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hfmd := fMinus_hasDerivAt_of_mem hG hg hG2 hB2 hc
  have hprod : HasDerivAt (fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u))
      (deriv (fPlus L G0 B0) c * (X - fMinus L G0 B0 c) + (fPlus L G0 B0 c - X) * (0 - deriv (fMinus L G0 B0) c)) c :=
    (hfpd.sub_const X).mul ((hasDerivAt_const c X).sub hfmd)
  have heq : Tfun L G0 B0 X =ᶠ[𝓝 c] fun u => (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hc) (fun u hu => Tfun_eq hG hg (Ioo_subset_Icc_self hu) X)
  exact hprod.congr_of_eventuallyEq heq

/-- The shapes of `f_+` and `f_-` for a `Hyp` pair: strict unimodality with extremal points `uc`, `q` in `(0, L)`. -/
lemma shapes_of_hyp {G0 B0 : ℝ → ℝ} {L g : ℝ} (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) (hL : 0 < L) :
    ∃ uc q : ℝ, uc ∈ Ioo 0 L ∧ q ∈ Ioo 0 L ∧
      (StrictMonoOn (fPlus L G0 B0) (Icc 0 uc) ∧ StrictAntiOn (fPlus L G0 B0) (Icc uc L)) ∧
      (StrictAntiOn (fMinus L G0 B0) (Icc 0 q) ∧ StrictMonoOn (fMinus L G0 B0) (Icc q L)) ∧
      fPlus L G0 B0 uc = Xsp L G0 B0 ∧ fMinus L G0 B0 q = Xsm L G0 B0 := by
  have hg := hyp.gstar_pos
  have hGg := hyp.G0_lb
  have hA : AProp L G0 B0 := fun X h1 h2 => by
    obtain ⟨a, b, ha, hab, hbL, hS, hda, hdb, ha0, hbL'⟩ := hyp.H2 X h1 h2
    exact ⟨a, b, ha, hab, hbL, hS, fun h => (hda h).2, fun h => (hdb h).2, ha0, hbL'⟩
  obtain ⟨hPp, hPm⟩ := (hypMorseEquiv L G0 B0 g hL hg hGg hG2 hB2).2 ⟨hA, hyp.H3p, hyp.H3m⟩
  obtain ⟨uc, huc, hsh, _, _⟩ := shape_of_Pp hGg hg hG2 hB2 hPp
  have hB2n : ContDiffOn ℝ 2 (fun u => -B0 u) (Icc 0 L) := hB2.neg
  obtain ⟨q, hq, hshn, _, _⟩ := shape_of_Pp hGg hg hG2 hB2n (Pm_iff_neg.1 hPm)
  have hfm1 : StrictAntiOn (fMinus L G0 B0) (Icc 0 q) := by
    intro x hx y hy hxy
    have := hshn.1 hx hy hxy
    rw [congrFun fPlus_neg_B x, congrFun fPlus_neg_B y] at this
    linarith
  have hfm2 : StrictMonoOn (fMinus L G0 B0) (Icc q L) := by
    intro x hx y hy hxy
    have := hshn.2 hx hy hxy
    rw [congrFun fPlus_neg_B x, congrFun fPlus_neg_B y] at this
    linarith
  have hmaxn := max_of_shape hq hshn.1 hshn.2
  have hXm : fMinus L G0 B0 q = Xsm L G0 B0 := by
    have hmin : ∀ u ∈ Icc 0 L, fMinus L G0 B0 q ≤ fMinus L G0 B0 u := by
      intro u hu
      have := hmaxn u hu
      rw [congrFun fPlus_neg_B u, congrFun fPlus_neg_B q] at this
      linarith
    exact (Xsm_eq_of_min ⟨hq.1.le, hq.2.le⟩ hmin).symm
  have hXp : fPlus L G0 B0 uc = Xsp L G0 B0 :=
    (Xsp_eq_of_max ⟨huc.1.le, huc.2.le⟩ (max_of_shape huc hsh.1 hsh.2)).symm
  exact ⟨uc, q, huc, hq, hsh, ⟨hfm1, hfm2⟩, hXp, hXm⟩

theorem geomBulk : GeomBulk := by
  intro L G0 B0 g hL hyp hG2 hB2 X hX1 hX2
  have hg : 0 < g := hyp.gstar_pos
  have hGg : ∀ u ∈ Icc 0 L, g ≤ G0 u := hyp.G0_lb
  obtain ⟨a, b, ha0, hab, hbL, hS, hda, hdb, ha0B, hbLB⟩ := hyp.H2 X hX1 hX2
  obtain ⟨uc, q, huc, hq, ⟨hP1, hP2⟩, ⟨hM1, hM2⟩, hXp, hXm⟩ := shapes_of_hyp hyp hG2 hB2 hL
  have hbI : b ∈ Icc 0 L := ⟨ha0.trans hab, hbL⟩
  have haI : a ∈ Icc 0 L := ⟨ha0, hab.trans hbL⟩
  have h0I : (0:ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hLI : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have huM : uMinusS L G0 B0 X = a := by
    unfold uMinusS allowedSet
    rw [hS, csInf_Icc hab]
  have huP : uPlusS L G0 B0 X = b := by
    unfold uPlusS allowedSet
    rw [hS, csSup_Icc hab]
  rw [huM, huP]
  -- the allowed set is `[a, b]`
  have hmem : ∀ u ∈ Icc 0 L, (0 ≤ Tfun L G0 B0 X u ↔ a ≤ u ∧ u ≤ b) := by
    intro u hu
    have h1 : u ∈ Icc 0 L ∩ {u | 0 ≤ Tfun L G0 B0 X u} ↔ u ∈ Icc a b := by rw [hS]
    constructor
    · intro h0
      exact h1.1 ⟨hu, h0⟩
    · intro h
      exact (h1.2 h).2
  have hTeq : ∀ u ∈ Icc 0 L, Tfun L G0 B0 X u = (fPlus L G0 B0 u - X) * (X - fMinus L G0 B0 u) :=
    fun u hu => Tfun_eq hGg hg hu X
  have hTpos : ∀ u ∈ Icc 0 L, fMinus L G0 B0 u < X → X < fPlus L G0 B0 u → 0 < Tfun L G0 B0 X u := by
    intro u hu h1 h2
    rw [hTeq u hu]
    exact mul_pos (by linarith) (by linarith)
  have hXa : fMinus L G0 B0 a ≤ X ∧ X ≤ fPlus L G0 B0 a :=
    (Tfun_nonneg_iff hGg hg haI X).1 ((hmem a haI).2 ⟨le_rfl, hab⟩)
  have hXb : fMinus L G0 B0 b ≤ X ∧ X ≤ fPlus L G0 B0 b :=
    (Tfun_nonneg_iff hGg hg hbI X).1 ((hmem b hbI).2 ⟨hab, le_rfl⟩)
  -- (ii) `T > 0` strictly between `a` and `b`
  have hint : ∀ u, a < u → u < b → 0 < Tfun L G0 B0 X u := by
    intro u hau hub
    have huI : u ∈ Icc 0 L := ⟨ha0.trans hau.le, hub.le.trans hbL⟩
    refine hTpos u huI ?_ ?_
    · rcases le_total u q with huq | huq
      · have h1 := hM1 (show a ∈ Icc 0 q from ⟨ha0, hau.le.trans huq⟩)
          (show u ∈ Icc 0 q from ⟨ha0.trans hau.le, huq⟩) hau
        linarith [hXa.1]
      · have h1 := hM2 (show u ∈ Icc q L from ⟨huq, hub.le.trans hbL⟩)
          (show b ∈ Icc q L from ⟨huq.trans hub.le, hbL⟩) hub
        linarith [hXb.1]
    · rcases le_total u uc with huc' | huc'
      · have h1 := hP1 (show a ∈ Icc 0 uc from ⟨ha0, hau.le.trans huc'⟩)
          (show u ∈ Icc 0 uc from ⟨ha0.trans hau.le, huc'⟩) hau
        linarith [hXa.2]
      · have h1 := hP2 (show u ∈ Icc uc L from ⟨huc', huI.2⟩)
          (show b ∈ Icc uc L from ⟨huc'.trans hub.le, hbL⟩) hub
        linarith [hXb.2]
  -- endpoint collision cases: `X = B_0(0)` forces `T > 0` just right of `0`
  have key0 : X = B0 0 → ∀ u, 0 < u → u < uc → u < q → 0 < Tfun L G0 B0 X u := by
    intro hX u hu0 hu1 hu2
    have huI : u ∈ Icc 0 L := ⟨hu0.le, (hu1.trans huc.2).le⟩
    refine hTpos u huI ?_ ?_
    · have h1 := hM1 (show (0:ℝ) ∈ Icc 0 q from ⟨le_rfl, hq.1.le⟩)
        (show u ∈ Icc 0 q from ⟨hu0.le, hu2.le⟩) hu0
      rw [fMinus_zero] at h1
      linarith
    · have h1 := hP1 (show (0:ℝ) ∈ Icc 0 uc from ⟨le_rfl, huc.1.le⟩)
        (show u ∈ Icc 0 uc from ⟨hu0.le, hu1.le⟩) hu0
      rw [fPlus_zero] at h1
      linarith
  -- endpoint collision cases: `X = B_0(L)` forces `T > 0` just left of `L`
  have keyL : X = B0 L → ∀ u, max uc q < u → u < L → 0 < Tfun L G0 B0 X u := by
    intro hX u hu1 hu2
    have hu0 : 0 < u := by linarith [le_max_left uc q, huc.1]
    have huI : u ∈ Icc 0 L := ⟨hu0.le, hu2.le⟩
    refine hTpos u huI ?_ ?_
    · have h1 := hM2 (show u ∈ Icc q L from ⟨(le_max_right uc q).trans hu1.le, hu2.le⟩)
        (show L ∈ Icc q L from ⟨hq.2.le, le_rfl⟩) hu2
      rw [fMinus_L] at h1
      linarith
    · have h1 := hP2 (show u ∈ Icc uc L from ⟨(le_max_left uc q).trans hu1.le, hu2.le⟩)
        (show L ∈ Icc uc L from ⟨huc.2.le, le_rfl⟩) hu2
      rw [fPlus_L] at h1
      linarith
  -- (i) `a < b`
  have hab' : a < b := by
    refine lt_of_le_of_ne hab (fun h => ?_)
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · -- `a = b = 0`
      have hX : X = B0 0 := ha0B h0.symm
      have hmpos : 0 < min uc q / 2 := by linarith [lt_min huc.1 hq.1]
      have hmuc : min uc q / 2 < uc := by linarith [min_le_left uc q, huc.1]
      have hmq : min uc q / 2 < q := by linarith [min_le_right uc q, hq.1]
      have hmI : min uc q / 2 ∈ Icc 0 L := ⟨hmpos.le, by linarith [huc.2]⟩
      have hT := (hmem _ hmI).1 (key0 hX _ hmpos hmuc hmq).le
      linarith [hT.2]
    · have haL : a ≤ L := hab.trans hbL
      have hT0 : Tfun L G0 B0 X a = 0 := (hda hpos).1
      have hd : deriv (Tfun L G0 B0 X) a ≠ 0 := (hda hpos).2
      rcases eq_or_lt_of_le haL with hal | hal
      · -- `a = b = L`
        have hML : max uc q < L := max_lt huc.2 hq.2
        have hgt : max uc q < (max uc q + L) / 2 := by linarith
        have hlt : (max uc q + L) / 2 < L := by linarith
        have huI : (max uc q + L) / 2 ∈ Icc 0 L := ⟨by linarith [le_max_left uc q, huc.1], hlt.le⟩
        have hT := (hmem _ huI).1 (keyL (hbLB (h.symm.trans hal)) _ hgt hlt).le
        linarith [hT.1]
      · -- `0 < a = b < L`: a sign change of `T` at `a`
        have haI' : a ∈ Ioo 0 L := ⟨hpos, hal⟩
        have hTd : HasDerivAt (Tfun L G0 B0 X) (deriv (Tfun L G0 B0 X) a) a :=
          (hasDerivAt_Tfun_of_mem hGg hg hG2 hB2 X haI').differentiableAt.hasDerivAt
        rcases lt_or_gt_of_ne hd with hneg | hposd
        · obtain ⟨δ, hδ, -, hn⟩ := count_local_sign (f := fun u => -Tfun L G0 B0 X u)
            (f' := -deriv (Tfun L G0 B0 X) a) hTd.neg
            (by show -Tfun L G0 B0 X a = 0; rw [hT0, neg_zero]) (by linarith)
          have hm : 0 < min δ a := lt_min hδ hpos
          have hm2 : min δ a ≤ a := min_le_right _ _
          have htI : a - min δ a / 2 ∈ Icc 0 L := ⟨by linarith, by linarith⟩
          have h3 : -Tfun L G0 B0 X (a - min δ a / 2) < 0 :=
            hn (a - min δ a / 2) (by linarith [min_le_left δ a]) (by linarith)
          have h4 := (hmem _ htI).1 (by linarith)
          linarith [h4.1]
        · obtain ⟨δ, hδ, hn, -⟩ := count_local_sign (f := Tfun L G0 B0 X)
            (f' := deriv (Tfun L G0 B0 X) a) hTd hT0 hposd
          have hm : 0 < min δ (L - a) := lt_min hδ (by linarith)
          have hm2 : min δ (L - a) ≤ L - a := min_le_right _ _
          have htI : a + min δ (L - a) / 2 ∈ Icc 0 L := ⟨by linarith, by linarith⟩
          have h3 : 0 < Tfun L G0 B0 X (a + min δ (L - a) / 2) :=
            hn (a + min δ (L - a) / 2) (by linarith) (by linarith [min_le_left δ (L - a)])
          have h4 := (hmem _ htI).1 h3.le
          linarith [h4.2]
  -- zeros of `T` at the ends
  have hTa0 : Tfun L G0 B0 X a = 0 := by
    rcases eq_or_lt_of_le ha0 with h0 | hpos
    · rw [← h0, Tfun_eq hGg hg h0I X, fPlus_zero, fMinus_zero, ha0B h0.symm]
      ring
    · exact (hda hpos).1
  have hTb0 : Tfun L G0 B0 X b = 0 := by
    rcases eq_or_lt_of_le hbL with h1 | h1
    · rw [h1, Tfun_eq hGg hg hLI X, fPlus_L, fMinus_L, hbLB h1]
      ring
    · exact (hdb h1).1
  have hzero : ∀ u ∈ Icc 0 L, Tfun L G0 B0 X u = 0 ↔ u = a ∨ u = b := by
    intro u hu
    constructor
    · intro h
      have hm := (hmem u hu).1 h.ge
      rcases eq_or_lt_of_le hm.1 with h1 | h1
      · exact Or.inl h1.symm
      rcases eq_or_lt_of_le hm.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd h (hint u h1 h2).ne'
    · rintro (h | h)
      · rw [h]
        exact hTa0
      · rw [h]
        exact hTb0
  have hpos_iff : ∀ u ∈ Icc 0 L, 0 < Tfun L G0 B0 X u ↔ a < u ∧ u < b := by
    intro u hu
    constructor
    · intro h
      have hm := (hmem u hu).1 h.le
      refine ⟨lt_of_le_of_ne hm.1 (fun e => ?_), lt_of_le_of_ne hm.2 (fun e => ?_)⟩
      · have : Tfun L G0 B0 X u = 0 := by
          rw [← e]
          exact hTa0
        linarith
      · have : Tfun L G0 B0 X u = 0 := by
          rw [e]
          exact hTb0
        linarith
    · rintro ⟨h1, h2⟩
      exact hint u h1 h2
  refine ⟨hab', hpos_iff, ?_, hzero, fun h => (hda h).2, fun h => (hdb h).2, ?_, ?_⟩
  · intro u hu hnot
    have h0 : ¬ (0 ≤ Tfun L G0 B0 X u) := fun h => hnot ((hmem u hu).1 h)
    exact not_le.mp h0
  · constructor
    · intro h
      exact ha0B h
    · intro hX
      by_contra hne
      have hpos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
      have hmin : 0 < min a (min uc q) := lt_min hpos (lt_min huc.1 hq.1)
      have hu1 : min a (min uc q) ≤ a := min_le_left _ _
      have hu2 : min a (min uc q) ≤ uc := (min_le_right _ _).trans (min_le_left _ _)
      have hu3 : min a (min uc q) ≤ q := (min_le_right _ _).trans (min_le_right _ _)
      have hu0 : 0 < min a (min uc q) / 2 := by linarith
      have huI : min a (min uc q) / 2 ∈ Icc 0 L := ⟨hu0.le, by linarith [huc.2]⟩
      have hT := (hmem _ huI).1 (key0 hX _ hu0 (by linarith) (by linarith)).le
      linarith [hT.1]
  · constructor
    · intro h
      exact hbLB h
    · intro hX
      by_contra hne
      have hlt : b < L := lt_of_le_of_ne hbL hne
      have hML : max b (max uc q) < L := max_lt hlt (max_lt huc.2 hq.2)
      have hA : max uc q < (max b (max uc q) + L) / 2 := by
        linarith [le_max_right b (max uc q)]
      have hB : (max b (max uc q) + L) / 2 < L := by linarith
      have hBb : b < (max b (max uc q) + L) / 2 := by
        linarith [le_max_left b (max uc q)]
      have huI : (max b (max uc q) + L) / 2 ∈ Icc 0 L :=
        ⟨by linarith [le_max_left b (max uc q), hbI.1, hL], hB.le⟩
      have hT := (hmem _ huI).1 (keyL hX _ hA hB).le
      linarith [hT.2]

end HypMorse

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.hypMorseEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.hypMorseEquiv

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.hypOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.hypOpen

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenStandard_of_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenStandard_of_reg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenReg_of_dm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenReg_of_dm

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenStandard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.frozenStandard

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.geomBulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.HypMorse.geomBulk

end FormalResearch.JacobiEigenvectors.TheoremA

end

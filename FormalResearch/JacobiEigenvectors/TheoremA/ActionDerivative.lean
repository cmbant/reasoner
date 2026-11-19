module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeShift
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenBase

/-!
# Paper J, Layer 2: the derivative of the action, `eq:cp-S0p` (L2.E, Step 1 of cor:eigen, part 3)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 1: `S_0'(X) = -int_{u_-}^{u_+} du/sqrt(T)` on the open band.  Frozen statements: `actionS0` (`TheoremA/Statements.lean`); the use is `CorEigenS1`, `InvS0` (`EigenvalueStatements.lean`).

## Proved here

* `deriv_pos_of_left_neg`, `deriv_neg_of_right_neg`: sign of a simple zero from the sign pattern next to it.
* `E1G`, `hasDerivWithinAt_E0`, `continuousOn_E1G`: `E_0' = (L - 2u) G + u (L - u) G'` within `[0, L]`.
* **`base_data`** (lem:tha-geom (a) in the form needed): for `X` in the open band, `a_0 = u_-(X)`, `b_0 = u_+(X)` satisfy `0 <= a_0 < b_0 <= L`, `T(a_0) = T(b_0) = 0`, `T > 0` on `(a_0, b_0)`, `T < 0` on `[0, L]` outside `[a_0, b_0]`, and `T'(a_0) > 0 > T'(b_0)`
  (one-sided at the hard edges, where the collision `X = B_0(0)` gives `T'(0) = 4 L G_0(0)`).  From `HypMorse.geomBulk`.
* **`actionS0_hasDerivAt_sym`** (`eq:cp-S0p`): `d/dX int_0^L arccos((X - B_0)/(2 sqrt E_0)) du = - int_0^L T^{-1/2} du` at every `X` of the open band (including the collision energies).
* `integral_zero_L_eq`, `intervalIntegrable_inv_sqrtT`: `int_0^L q T^{-1/2} = int_{u_-}^{u_+} q T^{-1/2}`, and the integrand is interval integrable (for continuous `q`).
* **`actionS0_hasDerivAt`** (family form): `HasDerivAt (actionS0 F mu) (- int_{u_-}^{u_+} 1/sqrt T) X` for `mu in K`, `X` in the open band, with `HypOn F K`, `DM F K 0`; `deriv_S0_of_eq` for any `S_0` equal to `actionS0` on the band.

## Differences from the paper

No implicit function theorem and no differentiation under the integral sign: the derivative is obtained from `ActionDerivativeShift.lean` (fundamental theorem of calculus for `arccos` in the energy variable, Fubini,
continuity of `int T^{-1/2}` from `ActionDerivativeStable.lean`).  The convention `x/sqrt y = 0` for `y <= 0` is used in the integrands (so the integrals over `[0, L]` and `[u_-, u_+]` agree, `integral_zero_L_eq`).

## Not formalised

The edge values `-S_0'(X_s^pm) = pi sqrt(2/(kappa_pm d_pm))` (limit `eq:cp-edgelim`); see `CorEigenGapM.lean`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology MeasureTheory FormalResearch.JacobiEigenvectors.Setting

/-! ### Slope lemmas -/

lemma deriv_pos_of_left_neg {f : ℝ → ℝ} {d x : ℝ} (h : HasDerivAt f d x) (hx : f x = 0) {δ : ℝ} (hδ : 0 < δ)
    (hl : ∀ y ∈ Ioo (x - δ) x, f y < 0) (hne : d ≠ 0) : 0 < d := by
  by_contra hcon
  have hd : d < 0 := lt_of_le_of_ne (not_lt.1 hcon) hne
  have h1 : ∀ᶠ y in 𝓝[≠] x, slope f x y < 0 := (h.tendsto_slope).eventually (gt_mem_nhds hd)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, hεy⟩ := h1
  set r := min ε δ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hr1 : r < ε := by have := min_le_left ε δ; rw [hr]; linarith
  have hr2 : r < δ := by have := min_le_right ε δ; rw [hr]; linarith
  have hy : x - r ≠ x := by intro e; linarith
  have := hεy (y := x - r) (by rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith) hy
  rw [slope_def_field, hx, sub_zero] at this
  have hfy : f (x - r) < 0 := hl _ ⟨by linarith, by linarith⟩
  have : 0 < f (x - r) / (x - r - x) := div_pos_of_neg_of_neg hfy (by linarith)
  linarith

lemma deriv_neg_of_right_neg {f : ℝ → ℝ} {d x : ℝ} (h : HasDerivAt f d x) (hx : f x = 0) {δ : ℝ} (hδ : 0 < δ)
    (hl : ∀ y ∈ Ioo x (x + δ), f y < 0) (hne : d ≠ 0) : d < 0 := by
  by_contra hcon
  have hd : 0 < d := lt_of_le_of_ne (not_lt.1 hcon) (Ne.symm hne)
  have h1 : ∀ᶠ y in 𝓝[≠] x, 0 < slope f x y := (h.tendsto_slope).eventually (lt_mem_nhds hd)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨ε, hε, hεy⟩ := h1
  set r := min ε δ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hr1 : r < ε := by have := min_le_left ε δ; rw [hr]; linarith
  have hr2 : r < δ := by have := min_le_right ε δ; rw [hr]; linarith
  have hy : x + r ≠ x := by intro e; linarith
  have := hεy (y := x + r) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith) hy
  rw [slope_def_field, hx, sub_zero] at this
  have hfy : f (x + r) < 0 := hl _ ⟨by linarith, by linarith⟩
  have : f (x + r) / (x + r - x) < 0 := div_neg_of_neg_of_pos hfy (by linarith)
  linarith

/-! ### The derivative of `E_0` and the base structure from lem:tha-geom (a) -/

/-- `E_0'(u) = (L - 2u) G(u) + u (L - u) G'(u)`, with `G'` the derivative within `[0, L]`. -/
def E1G (L : ℝ) (G : ℝ → ℝ) (u : ℝ) : ℝ := (L - 2 * u) * G u + u * (L - u) * derivWithin G (Icc 0 L) u

lemma hasDerivWithinAt_E0 {L : ℝ} {G : ℝ → ℝ} (hG : DifferentiableOn ℝ G (Icc 0 L)) {u : ℝ} (hu : u ∈ Icc 0 L) :
    HasDerivWithinAt (E0 L G) (E1G L G u) (Icc 0 L) u := by
  have h1 : HasDerivWithinAt (fun v : ℝ => v * (L - v)) (1 * (L - u) + u * (-1)) (Icc 0 L) u :=
    (hasDerivWithinAt_id u _).mul ((hasDerivWithinAt_id u _).const_sub L)
  have h2 := h1.mul (hG u hu).hasDerivWithinAt
  refine (h2.congr_deriv ?_)
  simp only [E1G]
  ring

lemma hasDerivWithinAt_B {L : ℝ} {B : ℝ → ℝ} (hB : DifferentiableOn ℝ B (Icc 0 L)) {u : ℝ} (hu : u ∈ Icc 0 L) :
    HasDerivWithinAt B (derivWithin B (Icc 0 L) u) (Icc 0 L) u := (hB u hu).hasDerivWithinAt

lemma continuousOn_E1G {L : ℝ} (hL : 0 < L) {G : ℝ → ℝ} (hG : ContDiffOn ℝ 2 G (Icc 0 L)) :
    ContinuousOn (E1G L G) (Icc 0 L) := by
  have hd : ContinuousOn (derivWithin G (Icc 0 L)) (Icc 0 L) :=
    hG.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)
  unfold E1G
  exact ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul hG.continuousOn).add
    (((continuousOn_id.mul (continuousOn_const.sub continuousOn_id))).mul hd)

section Base

variable {L g : ℝ} {G B : ℝ → ℝ}

/-- **The base structure** (lem:tha-geom (a) in the form used by the shift theorem): for `X` in the open band, the allowed set is `[a_0, b_0]`, `T > 0` inside, `T < 0` outside,
`T(a_0) = T(b_0) = 0` and `T'(a_0) > 0 > T'(b_0)` (one-sided at the hard edges). -/
theorem base_data (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B (Icc 0 L))
    {X : ℝ} (hX1 : Xsm L G B < X) (hX2 : X < Xsp L G B) :
    ∃ a0 b0 : ℝ, 0 ≤ a0 ∧ a0 < b0 ∧ b0 ≤ L ∧ a0 = uMinusS L G B X ∧ b0 = uPlusS L G B X ∧
      4 * E0 L G a0 - (X - B a0) ^ 2 = 0 ∧ 4 * E0 L G b0 - (X - B b0) ^ 2 = 0 ∧
      (∀ u ∈ Icc 0 L, u ∉ Icc a0 b0 → 4 * E0 L G u - (X - B u) ^ 2 < 0) ∧
      (∀ u ∈ Ioo a0 b0, 0 < 4 * E0 L G u - (X - B u) ^ 2) ∧
      0 < 4 * E1G L G a0 + 2 * (X - B a0) * derivWithin B (Icc 0 L) a0 ∧
      4 * E1G L G b0 + 2 * (X - B b0) * derivWithin B (Icc 0 L) b0 < 0 := by
  obtain ⟨hlt, hpos, hneg, hzero, hda, hdb, hum0, hupL⟩ := HypMorse.geomBulk L G B g hL hyp hG2 hB2 X hX1 hX2
  have hne : (allowedSet L G B X).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : uMinusS L G B X = uPlusS L G B X := by unfold uMinusS uPlusS; rw [hemp]; simp
    linarith
  have ha0 : 0 ≤ uMinusS L G B X := le_csInf hne (fun x hx => hx.1.1)
  have hb0 : uPlusS L G B X ≤ L := csSup_le hne (fun x hx => hx.1.2)
  set a0 := uMinusS L G B X with ha
  set b0 := uPlusS L G B X with hb
  have hGd : DifferentiableOn ℝ G (Icc 0 L) := hG2.differentiableOn (by norm_num)
  have hBd : DifferentiableOn ℝ B (Icc 0 L) := hB2.differentiableOn (by norm_num)
  have hTd : ∀ u ∈ Ioo 0 L, HasDerivAt (Tfun L G B X)
      (4 * E1G L G u + 2 * (X - B u) * derivWithin B (Icc 0 L) u) u := by
    intro u hu
    have hmem : Icc 0 L ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have h1 := (hasDerivWithinAt_E0 hGd (Ioo_subset_Icc_self hu)).hasDerivAt hmem
    have h2 := (hasDerivWithinAt_B hBd (Ioo_subset_Icc_self hu)).hasDerivAt hmem
    have h3 := (h1.const_mul 4).sub (((hasDerivAt_const u X).sub h2).pow 2)
    refine (h3.congr_deriv ?_)
    simp only [Pi.sub_apply]
    ring
  have hTz : ∀ u ∈ Icc 0 L, Tfun L G B X u = 0 ↔ u = a0 ∨ u = b0 := hzero
  have ha0mem : a0 ∈ Icc 0 L := ⟨ha0, by linarith⟩
  have hb0mem : b0 ∈ Icc 0 L := ⟨by linarith, hb0⟩
  refine ⟨a0, b0, ha0, hlt, hb0, rfl, rfl, (hTz a0 ha0mem).2 (Or.inl rfl), (hTz b0 hb0mem).2 (Or.inr rfl),
    fun u hu hn => hneg u hu hn, fun u hu => (hpos u ⟨by linarith [hu.1], by linarith [hu.2]⟩).2 hu, ?_, ?_⟩
  · rcases ha0.eq_or_lt with h0 | h0
    · -- collision at the left end
      have hXB : X = B 0 := hum0.1 h0.symm
      rw [← h0]
      have hG0 : 0 < G 0 := lt_of_lt_of_le hyp.gstar_pos (hyp.G0_lb 0 ⟨le_rfl, hL.le⟩)
      simp only [E1G]
      rw [hXB]
      nlinarith [mul_pos hL hG0]
    · have hmem : a0 ∈ Ioo 0 L := ⟨h0, by linarith⟩
      have hd := hTd a0 hmem
      have hd' : deriv (Tfun L G B X) a0 ≠ 0 := hda h0
      rw [hd.deriv] at hd'
      refine deriv_pos_of_left_neg hd ((hTz a0 ha0mem).2 (Or.inl rfl)) (δ := a0) h0 ?_ hd'
      intro y hy
      exact hneg y ⟨by linarith [hy.1], by linarith [hy.2, hmem.2]⟩ (fun hh => by linarith [hy.2, hh.1])
  · rcases hb0.eq_or_lt with h0 | h0
    · have hXB : X = B L := hupL.1 h0
      rw [h0]
      have hGL : 0 < G L := lt_of_lt_of_le hyp.gstar_pos (hyp.G0_lb L ⟨hL.le, le_rfl⟩)
      simp only [E1G]
      rw [hXB]
      nlinarith [mul_pos hL hGL]
    · have hmem : b0 ∈ Ioo 0 L := ⟨by linarith, h0⟩
      have hd := hTd b0 hmem
      have hd' : deriv (Tfun L G B X) b0 ≠ 0 := hdb h0
      rw [hd.deriv] at hd'
      refine deriv_neg_of_right_neg hd ((hTz b0 hb0mem).2 (Or.inr rfl)) (δ := L - b0) (by linarith) ?_ hd'
      intro y hy
      exact hneg y ⟨by linarith [hy.1, hmem.1], by linarith [hy.2]⟩ (fun hh => by linarith [hy.1, hh.2])

end Base

section Sym

variable {L g : ℝ} {G B : ℝ → ℝ}

/-- The data of `ActionDeriv.hasDerivAt_shiftAction` for `E = E_0`, `B = B_0` from `Hyp` and `C^2`: all hypotheses except the weight `rho`. -/
lemma E0_data (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L)) :
    (∀ u ∈ Icc 0 L, HasDerivWithinAt (E0 L G) (E1G L G u) (Icc 0 L) u) ∧ ContinuousOn (E1G L G) (Icc 0 L) ∧
      E0 L G 0 = 0 ∧ E0 L G L = 0 ∧ ∀ u ∈ Ioo 0 L, 0 < E0 L G u :=
  ⟨fun u hu => hasDerivWithinAt_E0 (hG2.differentiableOn (by norm_num)) hu, continuousOn_E1G hL hG2,
    HypMorse.E0_zero, HypMorse.E0_L, fun u hu => HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hu⟩

lemma B_data (hL : 0 < L) (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) :
    (∀ u ∈ Icc 0 L, HasDerivWithinAt B (derivWithin B (Icc 0 L) u) (Icc 0 L) u) ∧
      ContinuousOn (derivWithin B (Icc 0 L)) (Icc 0 L) :=
  ⟨fun u hu => hasDerivWithinAt_B (hB2.differentiableOn (by norm_num)) hu,
    hB2.continuousOn_derivWithin (uniqueDiffOn_Icc hL) (by norm_num)⟩

/-- **`eq:cp-S0p`** (the derivative of the action): for `X` in the open band, `S_0'(X) = - int_0^L T(u; X)^{-1/2} du` (`T^{-1/2} := 0` where `T <= 0`, so this is
`- int_{u_-}^{u_+} du / sqrt T`, `actionS0_deriv_Ioo`). -/
theorem actionS0_hasDerivAt_sym (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ} (hX1 : Xsm L G B < X) (hX2 : X < Xsp L G B) :
    HasDerivAt (fun Y : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((Y - B u) / (2 * Real.sqrt (E0 L G u))))
      (-∫ u in (0 : ℝ)..L, (Real.sqrt (Tfun L G B X u))⁻¹) X := by
  obtain ⟨hEd, hE1c, hE0, hEL, hEpos⟩ := E0_data hL hyp hG2
  obtain ⟨hBd, hB1c⟩ := B_data hL hB2
  obtain ⟨a0, b0, ha0, hab, hb0, -, -, hza, hzb, hneg, hpos, hda, hdb⟩ := base_data hL hyp hG2 hB2 hX1 hX2
  have h := ActionDeriv.hasDerivAt_shiftAction hL (ρ := fun _ _ => (1 : ℝ)) (ρ1 := fun _ _ => (0 : ℝ))
    hEd hE1c hBd hB1c hE0 hEL hEpos continuousOn_const (fun t u hu => hasDerivWithinAt_const u _ 1)
    continuousOn_const ha0 hab hb0 hza hzb hneg hpos hda hdb
  simp only [mul_one] at h
  have h2 : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((X + t - B u) / (2 * Real.sqrt (E0 L G u))))
      (-∫ u in (0 : ℝ)..L, (Real.sqrt (4 * E0 L G u - (X - B u) ^ 2))⁻¹) ((fun Y : ℝ => Y - X) X) := by
    simp only [sub_self]
    simpa [one_div] using h
  have h3 := HasDerivAt.comp (h := fun Y : ℝ => Y - X) X h2 ((hasDerivAt_id X).sub_const X)
  simpa [Function.comp_def, Tfun] using h3

/-- Over `(0, L)` or over the allowed set: `q / sqrt T` vanishes where `T <= 0`. -/
lemma integral_zero_L_eq (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ} (hX1 : Xsm L G B < X) (hX2 : X < Xsp L G B) (q : ℝ → ℝ) :
    ∫ u in (0 : ℝ)..L, q u / Real.sqrt (Tfun L G B X u) =
      ∫ u in (uMinusS L G B X)..(uPlusS L G B X), q u / Real.sqrt (Tfun L G B X u) := by
  obtain ⟨a0, b0, ha0, hab, hb0, rfl, rfl, hza, hzb, hneg, hpos, -, -⟩ := base_data hL hyp hG2 hB2 hX1 hX2
  rw [intervalIntegral.integral_of_le hL.le, intervalIntegral.integral_of_le hab.le]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc (Ioc_subset_Ioc ha0 hb0) ?_
  intro u hu
  have hle : Tfun L G B X u ≤ 0 := by
    by_cases hm : u ∈ Icc (uMinusS L G B X) (uPlusS L G B X)
    · have hua : u = uMinusS L G B X := by
        by_contra hne
        exact hu.2 ⟨lt_of_le_of_ne hm.1 (Ne.symm hne), hm.2⟩
      rw [hua]; exact hza.le
    · exact (hneg u ⟨hu.1.1.le, hu.1.2⟩ hm).le
  rw [Real.sqrt_eq_zero_of_nonpos hle, div_zero]

/-- Integrability of `q / sqrt T` over `[u_-, u_+]` for continuous `q` (the integrand is `T^{-1/2}`, integrable singularities at simple zeros, also at the collision energies). -/
theorem intervalIntegrable_inv_sqrtT (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ} (hX1 : Xsm L G B < X) (hX2 : X < Xsp L G B) {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 L)) :
    IntervalIntegrable (fun u => q u / Real.sqrt (Tfun L G B X u)) volume 0 L ∧
      IntervalIntegrable (fun u => q u / Real.sqrt (Tfun L G B X u)) volume (uMinusS L G B X) (uPlusS L G B X) := by
  obtain ⟨hEd, hE1c, hE0, hEL, hEpos⟩ := E0_data hL hyp hG2
  obtain ⟨hBd, hB1c⟩ := B_data hL hB2
  obtain ⟨a0, b0, ha0, hab, hb0, rfl, rfl, hza, hzb, hneg, hpos, hda, hdb⟩ := base_data hL hyp hG2 hB2 hX1 hX2
  have h := ActionDeriv.intervalIntegrable_base hEd hE1c hBd hB1c hE0 hEL hq ha0 hab hb0 hza hzb hneg hpos hda hdb
  refine ⟨h, h.mono_set ?_⟩
  rw [uIcc_of_le hL.le, uIcc_of_le hab.le]
  exact Icc_subset_Icc ha0 hb0

end Sym

section Family

variable {Par : Type*} [TopologicalSpace Par]

/-- **`eq:cp-S0p` for a family**: for `mu in K` and `X` in the open band, `S_0'(X) = - int_{u_-}^{u_+} du / sqrt(T(u; X))`, the integral absolutely convergent (also at the collision
energies); `S_0 = actionS0 F mu`. -/
theorem actionS0_hasDerivAt (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K)
    {X : ℝ} (hX : X ∈ Ioo (F.bandLo μ) (F.bandHi μ)) :
    HasDerivAt (actionS0 F μ) (-∫ u in (F.uMinus μ X)..(F.uPlus μ X),
      1 / Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) X ∧
    IntervalIntegrable (fun u => 1 / Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) volume (F.uMinus μ X) (F.uPlus μ X) := by
  obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD hμ
  have h1 := actionS0_hasDerivAt_sym F.L_pos hyp hG2 hB2 hX.1 hX.2
  have h2 := integral_zero_L_eq F.L_pos hyp hG2 hB2 hX.1 hX.2 (fun _ => 1)
  have h3 := (intervalIntegrable_inv_sqrtT F.L_pos hyp hG2 hB2 hX.1 hX.2 (q := fun _ => 1) continuousOn_const).2
  refine ⟨?_, h3⟩
  simp only [one_div] at h2 ⊢
  rw [uMinus_eq_uMinusS, uPlus_eq_uPlusS, ← h2]
  exact h1

/-- The value of the derivative of `S_0` at `X` in the band depends only on `S_0` near `X`: for `S` equal to `actionS0 F mu` on the band, `deriv (S 0 mu)` is the same. -/
theorem deriv_S0_of_eq (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) {μ : Par} (hμ : μ ∈ K)
    {X : ℝ} (hX : X ∈ Ioo (F.bandLo μ) (F.bandHi μ)) {S0 : ℝ → ℝ}
    (hS : ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ), S0 Y = actionS0 F μ Y) :
    HasDerivAt S0 (-∫ u in (F.uMinus μ X)..(F.uPlus μ X),
      1 / Real.sqrt (Tfun F.L (F.G 0 μ) (F.B 0 μ) X u)) X := by
  refine (actionS0_hasDerivAt F K hH hD hμ hX).1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hX.1 hX.2] with Y hY
  exact hS Y (Ioo_subset_Icc_self hY)

end Family

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.base_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.base_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_hasDerivAt_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_hasDerivAt_sym

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.integral_zero_L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.integral_zero_L_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.intervalIntegrable_inv_sqrtT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.intervalIntegrable_inv_sqrtT

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.actionS0_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.actionS0_hasDerivAt

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.deriv_S0_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.deriv_S0_of_eq

end FormalResearch.JacobiEigenvectors.TheoremA

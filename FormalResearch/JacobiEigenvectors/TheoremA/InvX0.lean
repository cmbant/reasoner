module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvBounded
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenInverse

/-!
# Paper J, Layer 2: the inverse `x_0` of `S_0` and its derivative bounds (L2.E, `InvCoeffs`)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii): `x_0 = S_0^{-1}` on `[0, pi L]`, `S_0' <= -2 c_0` on the band.

## Proved here

* `InvCtx`: the bundled premises (`0 < delta`, `M >= 1`, `SmoothExt`, `ActionFormula`, `HypOn`, `DM F K 0`, `BandSlope` with constant `c_0`).
* `invX0`: `x_0(y)` = the root of `S_0 = y` in `I' = [X_s^- - delta', X_s^+ + delta']`, `delta' = invDelta`; `InvCtx.x0_band` (`x_0(y)` in the band and `S_0(x_0 y) = y` for `y in [0, pi L]`), `InvCtx.x0_hasDerivAt`
  (`x_0' = 1/S_0'(x_0)` through the local inverse theorem, with `[0, pi L]` in the interior of `S_0(I')`).
* `InvCtx.w_bd`: `y |-> S_j^{(k)}(x_0 y)` is `BD (m)` for `k + m <= M + 1` with a constant independent of `mu` (the derivative of `w_{jk}` is `w_{j,k+1}/w_{01}`, so only products and reciprocals are needed).
* `InvCtx.x0_bd`: `x_0` is `C^{M+1}` with bounded derivatives, given a uniform bound `Cb` on the band ends; `band_bdd`: such `Cb` exists on a compact `K` (from `DM F K 0`).

## Differences from the paper

The paper extends `x_0` by the implicit function theorem on a compact set; here the extension is by the explicit inverse on `I'` (slope `<= -3c_0/2` there, `slope_near_band`).

## Not formalised

Nothing for this file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting InvBD

variable {Par : Type*} [TopologicalSpace Par]

/-- The data of the inverse-expansion construction (cor:eigen (b)(iii)). -/
structure InvCtx (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (S : ℕ → Par → ℝ → ℝ) (δ Cn c0 : ℝ) : Prop where
  hδ : 0 < δ
  hM : 1 ≤ M
  hc0 : 0 < c0
  hS : SmoothExt F K M S δ Cn
  hA : ActionFormula F K S
  hH : HypOn F K
  hD0 : DM F K 0
  hsl : ∀ μ ∈ K, ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X

/-- The radius `delta'` of the neighbourhood `I'` of the band on which `-S_0' >= 3 c_0/2`. -/
def invDelta (δ Cn c0 : ℝ) : ℝ := min (δ / 2) (c0 / (2 * (|Cn| + 1)))

open Classical in
/-- The inverse `x_0` of `S_0` (`S_0 (x_0 y) = y`, `x_0 y` in the extended band `I'`). -/
def invX0 (F : SymbolFamily Par) (S : ℕ → Par → ℝ → ℝ) (δ' : ℝ) (μ : Par) (y : ℝ) : ℝ :=
  if h : ∃ X ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ'), S 0 μ X = y then Classical.choose h else F.bandLo μ

section X0

variable {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn c0 : ℝ} (ctx : InvCtx F K M S δ Cn c0)

include ctx

lemma InvCtx.delta_pos : 0 < invDelta δ Cn c0 :=
  lt_min (by linarith [ctx.hδ]) (by have := ctx.hc0; positivity)

lemma InvCtx.delta_lt : invDelta δ Cn c0 < δ := by
  have h1 : invDelta δ Cn c0 ≤ δ / 2 := min_le_left _ _
  linarith [ctx.hδ]

lemma InvCtx.delta_Cn : Cn * invDelta δ Cn c0 ≤ c0 / 2 := by
  have h1 : invDelta δ Cn c0 ≤ c0 / (2 * (|Cn| + 1)) := min_le_right _ _
  have h2 : 0 ≤ invDelta δ Cn c0 := ctx.delta_pos.le
  have h3 : |Cn| * invDelta δ Cn c0 ≤ |Cn| * (c0 / (2 * (|Cn| + 1))) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h4 : |Cn| * (c0 / (2 * (|Cn| + 1))) ≤ c0 / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg Cn, ctx.hc0]
  calc Cn * invDelta δ Cn c0 ≤ |Cn| * invDelta δ Cn c0 := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ c0 / 2 := h3.trans h4

lemma InvCtx.lt_band {μ : Par} (hμ : μ ∈ K) : F.bandLo μ < F.bandHi μ := bandLo_lt_bandHi F K 0 ctx.hH ctx.hD0 μ hμ

/-- `-S_0' >= 3 c_0/2` on `I'`. -/
lemma InvCtx.slope {μ : Par} (hμ : μ ∈ K) {X : ℝ}
    (hX : X ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0)) : deriv (S 0 μ) X ≤ -(3 * c0 / 2) :=
  slope_near_band ctx.hS ctx.hM hμ ctx.hδ (ctx.lt_band hμ) ctx.delta_pos ctx.delta_lt ctx.delta_Cn (ctx.hsl μ hμ) hX

lemma InvCtx.Iprime_sub {μ : Par} :
    Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0) ⊆ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ) := fun X hX =>
  ⟨by linarith [hX.1, ctx.delta_lt], by linarith [hX.2, ctx.delta_lt]⟩

/-- `S_0` is bi-Lipschitz from below on `I'`. -/
lemma InvCtx.sub_ge {μ : Par} (hμ : μ ∈ K) {x y : ℝ}
    (hx : x ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0))
    (hy : y ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0)) :
    (3 * c0 / 2) * |x - y| ≤ |S 0 μ x - S 0 μ y| := by
  have hc := ctx.hc0
  have hd := ctx.delta_pos
  refine abs_sub_ge_of_deriv_le (c := 3 * c0 / 2) ?_ ?_ ?_ (by positivity) hx hy
  · exact ((ctx.hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono (fun X hX => Ioo_subset_Icc_self (ctx.Iprime_sub hX))
  · intro z hz
    exact ctx.hS.diffAt hμ (Nat.zero_le _) (ctx.Iprime_sub ⟨hz.1.le, hz.2.le⟩)
  · intro z hz
    have := ctx.slope hμ ⟨hz.1.le, hz.2.le⟩
    linarith

lemma InvCtx.strictAnti {μ : Par} (hμ : μ ∈ K) :
    StrictAntiOn (S 0 μ) (Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0)) := by
  have hc := ctx.hc0
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (((ctx.hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono
    (fun X hX => Ioo_subset_Icc_self (ctx.Iprime_sub hX))) ?_
  intro z hz
  rw [interior_Icc] at hz
  have := ctx.slope hμ (Ioo_subset_Icc_self hz)
  linarith

/-- The image interval `J = [S_0(X_s^+ + delta'), S_0(X_s^- - delta')]` of `I'`. -/
def InvCtx.J (μ : Par) : Set ℝ :=
  Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0))

lemma InvCtx.exists_root {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0))) :
    ∃ X ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0), S 0 μ X = y := by
  have hd := ctx.delta_pos
  have hlt := ctx.lt_band hμ
  have hcont : ContinuousOn (S 0 μ) (Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0)) :=
    ((ctx.hS μ hμ 0 (Nat.zero_le _)).1.continuousOn).mono (fun X hX => Ioo_subset_Icc_self (ctx.Iprime_sub hX))
  exact intermediate_value_Icc' (by linarith) hcont hy

lemma InvCtx.x0_spec {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0))) :
    invX0 F S (invDelta δ Cn c0) μ y ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0) ∧
      S 0 μ (invX0 F S (invDelta δ Cn c0) μ y) = y := by
  have h := ctx.exists_root hμ hy
  unfold invX0
  simp only [h, dite_true]
  exact Classical.choose_spec h

lemma InvCtx.x0_left_inv {μ : Par} (hμ : μ ∈ K) {X : ℝ} (hX : X ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0)) :
    invX0 F S (invDelta δ Cn c0) μ (S 0 μ X) = X := by
  have hanti := ctx.strictAnti hμ
  have hlo : F.bandLo μ - invDelta δ Cn c0 ≤ F.bandHi μ + invDelta δ Cn c0 := by
    have := ctx.lt_band hμ; have := ctx.delta_pos; linarith
  have hJ : S 0 μ X ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0)) :=
    ⟨hanti.antitoneOn hX ⟨hlo, le_rfl⟩ hX.2, hanti.antitoneOn ⟨le_rfl, hlo⟩ hX hX.1⟩
  obtain ⟨h1, h2⟩ := ctx.x0_spec hμ hJ
  exact hanti.injOn h1 hX h2

lemma InvCtx.ends {μ : Par} (hμ : μ ∈ K) :
    S 0 μ (F.bandHi μ + invDelta δ Cn c0) < 0 ∧ Real.pi * F.L < S 0 μ (F.bandLo μ - invDelta δ Cn c0) := by
  have hd := ctx.delta_pos
  have hlt := ctx.lt_band hμ
  have hanti := ctx.strictAnti hμ
  have hhi : S 0 μ (F.bandHi μ) = 0 := by
    rw [ctx.hA μ hμ _ ⟨hlt.le, le_rfl⟩]; exact actionS0_bandHi F K ctx.hH ctx.hD0 hμ
  have hlo : S 0 μ (F.bandLo μ) = Real.pi * F.L := by
    rw [ctx.hA μ hμ _ ⟨le_rfl, hlt.le⟩]; exact actionS0_bandLo F K ctx.hH ctx.hD0 hμ
  constructor
  · rw [← hhi]
    exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  · rw [← hlo]
    exact hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

lemma InvCtx.band_in_Y {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    y ∈ Ioo (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0)) := by
  obtain ⟨h1, h2⟩ := ctx.ends hμ
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- `x_0 y` lies in the band for `y in [0, pi L]`. -/
lemma InvCtx.x0_band {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    invX0 F S (invDelta δ Cn c0) μ y ∈ Icc (F.bandLo μ) (F.bandHi μ) ∧ S 0 μ (invX0 F S (invDelta δ Cn c0) μ y) = y := by
  have hlt := ctx.lt_band hμ
  have hJ := Ioo_subset_Icc_self (ctx.band_in_Y hμ hy)
  obtain ⟨h1, h2⟩ := ctx.x0_spec hμ hJ
  refine ⟨?_, h2⟩
  obtain ⟨X, hX, hXy⟩ := BandSlope.surj ctx.hS ctx.hδ ctx.hA ctx.hH ctx.hD0 hμ hlt hy
  have hd := ctx.delta_pos
  have hXI : X ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
  have : invX0 F S (invDelta δ Cn c0) μ y = X := ctx.strictAnti hμ |>.injOn h1 hXI (by rw [h2, hXy])
  rw [this]
  exact hX

lemma InvCtx.x0_dist {μ : Par} (hμ : μ ∈ K) {y y' : ℝ}
    (hy : y ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0)))
    (hy' : y' ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0))) :
    (3 * c0 / 2) * |invX0 F S (invDelta δ Cn c0) μ y - invX0 F S (invDelta δ Cn c0) μ y'| ≤ |y - y'| := by
  obtain ⟨h1, h2⟩ := ctx.x0_spec hμ hy
  obtain ⟨h1', h2'⟩ := ctx.x0_spec hμ hy'
  have := ctx.sub_ge hμ h1 h1'
  rwa [h2, h2'] at this

lemma InvCtx.x0_hasDerivAt {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    HasDerivAt (invX0 F S (invDelta δ Cn c0) μ) (deriv (S 0 μ) (invX0 F S (invDelta δ Cn c0) μ y))⁻¹ y := by
  have hc := ctx.hc0
  have hyJ := ctx.band_in_Y hμ hy
  have hJn : Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0)) ∈ 𝓝 y :=
    Icc_mem_nhds hyJ.1 hyJ.2
  obtain ⟨hx1, hx2⟩ := ctx.x0_spec hμ (Ioo_subset_Icc_self hyJ)
  have hcont : ContinuousAt (invX0 F S (invDelta δ Cn c0) μ) y := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hJn
    refine ⟨min r (ε * (3 * c0 / 2)), lt_min hr (by positivity), fun z hz => ?_⟩
    have hzJ : z ∈ Icc (S 0 μ (F.bandHi μ + invDelta δ Cn c0)) (S 0 μ (F.bandLo μ - invDelta δ Cn c0)) :=
      hball (lt_of_lt_of_le hz (min_le_left _ _))
    have hd := ctx.x0_dist hμ hzJ (Ioo_subset_Icc_self hyJ)
    have hz2 : dist z y < ε * (3 * c0 / 2) := lt_of_lt_of_le hz (min_le_right _ _)
    rw [Real.dist_eq] at hz2 ⊢
    have hpos : 0 < 3 * c0 / 2 := by positivity
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon hpos.le]
  have hS0 : HasDerivAt (S 0 μ) (deriv (S 0 μ) (invX0 F S (invDelta δ Cn c0) μ y)) (invX0 F S (invDelta δ Cn c0) μ y) :=
    (ctx.hS.diffAt hμ (Nat.zero_le _) (ctx.Iprime_sub hx1)).hasDerivAt
  have hne : deriv (S 0 μ) (invX0 F S (invDelta δ Cn c0) μ y) ≠ 0 := by
    have := ctx.slope hμ hx1
    linarith
  refine HasDerivAt.of_local_left_inverse hcont hS0 hne ?_
  filter_upwards [hJn] with z hz
  exact (ctx.x0_spec hμ hz).2

/-- `S_j^{(k)}(x_0(y))`. -/
def invW (F : SymbolFamily Par) (S : ℕ → Par → ℝ → ℝ) (δ δ' : ℝ) (j k : ℕ) (μ : Par) (y : ℝ) : ℝ :=
  iteratedDerivWithin k (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) (invX0 F S δ' μ y)

lemma InvCtx.iter_hasDerivAt {μ : Par} (hμ : μ ∈ K) {j k : ℕ} (hj : j ≤ M) (hk : k ≤ M) {X : ℝ}
    (hX : X ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    HasDerivAt (iteratedDerivWithin k (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)))
      (iteratedDerivWithin (k + 1) (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) X) X := by
  have hAB : F.bandLo μ - δ < F.bandHi μ + δ := by linarith [hX.1, hX.2]
  have hdiff := (ctx.hS μ hμ j hj).1.differentiableOn_iteratedDerivWithin (m := k)
    (by exact_mod_cast (by omega : k < M + 1)) (uniqueDiffOn_Icc hAB)
  have hn : Icc (F.bandLo μ - δ) (F.bandHi μ + δ) ∈ 𝓝 X := Icc_mem_nhds hX.1 hX.2
  have hda := (hdiff X (Ioo_subset_Icc_self hX)).differentiableAt hn
  have := hda.hasDerivAt
  rw [← derivWithin_of_mem_nhds hn, ← iteratedDerivWithin_succ] at this
  exact this

lemma InvCtx.iter_one {μ : Par} {j : ℕ} {X : ℝ} (hX : X ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    iteratedDerivWithin 1 (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) X = deriv (S j μ) X := by
  rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Icc_mem_nhds hX.1 hX.2)]

lemma InvCtx.x0_mem {μ : Par} (hμ : μ ∈ K) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    invX0 F S (invDelta δ Cn c0) μ y ∈ Icc (F.bandLo μ - invDelta δ Cn c0) (F.bandHi μ + invDelta δ Cn c0) :=
  (ctx.x0_spec hμ (Ioo_subset_Icc_self (ctx.band_in_Y hμ hy))).1

lemma InvCtx.x0_continuousOn {μ : Par} (hμ : μ ∈ K) :
    ContinuousOn (invX0 F S (invDelta δ Cn c0) μ) (Icc 0 (Real.pi * F.L)) :=
  fun y hy => (ctx.x0_hasDerivAt hμ hy).continuousAt.continuousWithinAt

/-- The derivatives of `y |-> S_j^{(k)}(x_0 y)` are again of this form (`w_{jk}' = w_{j,k+1}/w_{0,1}`), so all of them are bounded uniformly in `mu`. -/
theorem InvCtx.w_bd : ∀ m : ℕ, ∃ C : ℝ, ∀ μ ∈ K, ∀ j ≤ M, ∀ k : ℕ, k + m ≤ M + 1 →
    BD (Icc 0 (Real.pi * F.L)) m C (invW F S δ (invDelta δ Cn c0) j k μ) := by
  intro m
  induction m with
  | zero =>
    refine ⟨Cn, fun μ hμ j hj k hk => ⟨?_, fun y hy => ?_⟩⟩
    · have hc : ContinuousOn (iteratedDerivWithin k (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ))) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) := by
        have hAB : F.bandLo μ - δ < F.bandHi μ + δ := by
          have := ctx.lt_band hμ; linarith [ctx.hδ]
        exact (ctx.hS μ hμ j hj).1.continuousOn_iteratedDerivWithin (by exact_mod_cast (by omega : k ≤ M + 1)) (uniqueDiffOn_Icc hAB)
      exact hc.comp (ctx.x0_continuousOn hμ) (fun y hy => Ioo_subset_Icc_self (ctx.Iprime_sub (ctx.x0_mem hμ hy)))
    · exact (ctx.hS μ hμ j hj).2 k (by omega) _ (Ioo_subset_Icc_self (ctx.Iprime_sub (ctx.x0_mem hμ hy)))
  | succ m ih =>
    obtain ⟨Cm, hCm⟩ := ih
    have hc := ctx.hc0
    obtain ⟨Ci, hCi⟩ := BD.inv_exists (I := Icc 0 (Real.pi * F.L)) m Cm (3 * c0 / 2) (by positivity)
    obtain ⟨Cp, hCp⟩ := BD.mul_exists (I := Icc 0 (Real.pi * F.L)) m Cm Ci
    refine ⟨max Cn Cp, fun μ hμ j hj k hk => ?_⟩
    have hmM : m ≤ M := by omega
    have hw1 : BD (Icc 0 (Real.pi * F.L)) m Cm (invW F S δ (invDelta δ Cn c0) 0 1 μ) := hCm μ hμ 0 (Nat.zero_le _) 1 (by omega)
    have hw1lo : ∀ y ∈ Icc 0 (Real.pi * F.L), 3 * c0 / 2 ≤ |invW F S δ (invDelta δ Cn c0) 0 1 μ y| := by
      intro y hy
      have hX := ctx.x0_mem hμ hy
      unfold invW
      rw [ctx.iter_one (ctx.Iprime_sub hX), abs_of_nonpos (by linarith [ctx.slope hμ hX])]
      linarith [ctx.slope hμ hX]
    have hinv := hCi _ hw1 hw1lo
    have hw2 : BD (Icc 0 (Real.pi * F.L)) m Cm (invW F S δ (invDelta δ Cn c0) j (k + 1) μ) := hCm μ hμ j hj (k + 1) (by omega)
    refine ⟨fun y hy => ?_, fun y => invW F S δ (invDelta δ Cn c0) j (k + 1) μ y * (invW F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹,
      fun y hy => ?_, (hCp _ _ hw2 hinv).mono_C (le_max_right _ _)⟩
    · exact ((ctx.hS μ hμ j hj).2 k (by omega) _ (Ioo_subset_Icc_self (ctx.Iprime_sub (ctx.x0_mem hμ hy)))).trans (le_max_left _ _)
    · have hX := ctx.x0_mem hμ hy
      have hXo := ctx.Iprime_sub hX
      have h1 := ctx.iter_hasDerivAt hμ hj (by omega : k ≤ M) hXo
      have h2 := ctx.x0_hasDerivAt hμ hy
      have h3 := h1.comp y h2
      have e : (deriv (S 0 μ) (invX0 F S (invDelta δ Cn c0) μ y))⁻¹ = (invW F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹ := by
        unfold invW; rw [ctx.iter_one hXo]
      rw [e] at h3
      exact h3.hasDerivWithinAt

/-- `x_0` is `C^{M+1}` on `[0, pi L]` with all derivatives bounded uniformly in `mu` (given a uniform bound on the band). -/
theorem InvCtx.x0_bd {Cb : ℝ} (hB : ∀ μ ∈ K, |F.bandLo μ| ≤ Cb ∧ |F.bandHi μ| ≤ Cb) :
    ∃ C : ℝ, ∀ μ ∈ K, BD (Icc 0 (Real.pi * F.L)) (M + 1) C (invX0 F S (invDelta δ Cn c0) μ) := by
  have hc := ctx.hc0
  obtain ⟨Cm, hCm⟩ := ctx.w_bd M
  obtain ⟨Ci, hCi⟩ := BD.inv_exists (I := Icc 0 (Real.pi * F.L)) M Cm (3 * c0 / 2) (by positivity)
  refine ⟨max Cb Ci, fun μ hμ => ⟨fun y hy => ?_, fun y => (invW F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹, fun y hy => ?_, ?_⟩⟩
  · have h := (ctx.x0_band hμ hy).1
    have := hB μ hμ
    rw [abs_le]
    constructor <;> linarith [(abs_le.1 this.1).1, (abs_le.1 this.2).2, (abs_le.1 this.1).2, (abs_le.1 this.2).1, h.1, h.2, le_max_left Cb Ci]
  · have hX := ctx.x0_mem hμ hy
    have hXo := ctx.Iprime_sub hX
    have e : (deriv (S 0 μ) (invX0 F S (invDelta δ Cn c0) μ y))⁻¹ = (invW F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹ := by
      unfold invW; rw [ctx.iter_one hXo]
    show HasDerivWithinAt _ (invW F S δ (invDelta δ Cn c0) 0 1 μ y)⁻¹ _ _
    rw [← e]
    exact (ctx.x0_hasDerivAt hμ hy).hasDerivWithinAt
  · have hw1 : BD (Icc 0 (Real.pi * F.L)) M Cm (invW F S δ (invDelta δ Cn c0) 0 1 μ) := hCm μ hμ 0 (Nat.zero_le _) 1 (by omega)
    have hw1lo : ∀ y ∈ Icc 0 (Real.pi * F.L), 3 * c0 / 2 ≤ |invW F S δ (invDelta δ Cn c0) 0 1 μ y| := by
      intro y hy
      have hX := ctx.x0_mem hμ hy
      unfold invW
      rw [ctx.iter_one (ctx.Iprime_sub hX), abs_of_nonpos (by linarith [ctx.slope hμ hX])]
      linarith [ctx.slope hμ hX]
    exact (hCi _ hw1 hw1lo).mono_C (le_max_right _ _)

end X0

section BandBound

/-- The band ends are bounded by the sup norms of the symbols. -/
lemma abs_band_le {L g Kg Kb : ℝ} {G B : ℝ → ℝ} (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) (hGb : ∀ u ∈ Icc 0 L, |G u| ≤ Kg) (hBb : ∀ u ∈ Icc 0 L, |B u| ≤ Kb) :
    |Xsp L G B| ≤ Kb + 2 * L * Real.sqrt Kg ∧ |Xsm L G B| ≤ Kb + 2 * L * Real.sqrt Kg := by
  obtain ⟨uc, hc1, hc2, hchar, -⟩ := hyp.H3p
  have hucI : uc ∈ Icc 0 L := ⟨hc1.le, hc2.le⟩
  have hG := hyp.G0_lb
  have hg := hyp.gstar_pos
  have hE : ∀ u ∈ Icc 0 L, Real.sqrt (E0 L G u) ≤ L * Real.sqrt Kg := by
    intro u hu
    have h1 : E0 L G u ≤ L ^ 2 * Kg := by
      unfold E0
      have h2 : u * (L - u) ≤ L ^ 2 := by nlinarith [hu.1, hu.2]
      have h3 : 0 ≤ u * (L - u) := mul_nonneg hu.1 (by linarith [hu.2])
      have h4 : G u ≤ Kg := (le_abs_self _).trans (hGb u hu)
      have h5 : 0 ≤ G u := by linarith [hG u hu]
      calc u * (L - u) * G u ≤ L ^ 2 * G u := mul_le_mul_of_nonneg_right h2 h5
        _ ≤ L ^ 2 * Kg := mul_le_mul_of_nonneg_left h4 (sq_nonneg L)
    calc Real.sqrt (E0 L G u) ≤ Real.sqrt (L ^ 2 * Kg) := Real.sqrt_le_sqrt h1
      _ = L * Real.sqrt Kg := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]
  have hs0 : ∀ u, 0 ≤ Real.sqrt (E0 L G u) := fun u => Real.sqrt_nonneg _
  have hfc := HypMorse.fPlus_continuousOn hG2 hB2
  have hfmc := HypMorse.fMinus_continuousOn hG2 hB2
  have hne : (fPlus L G B '' Icc 0 L).Nonempty := ⟨_, mem_image_of_mem _ hucI⟩
  have hne' : (fMinus L G B '' Icc 0 L).Nonempty := ⟨_, mem_image_of_mem _ hucI⟩
  have hBu := fun u hu => abs_le.1 (hBb u hu)
  constructor
  · have hup : Xsp L G B ≤ Kb + 2 * L * Real.sqrt Kg := by
      refine csSup_le hne ?_
      rintro _ ⟨u, hu, rfl⟩
      have := hE u hu
      have := (hBu u hu).2
      unfold fPlus
      nlinarith
    have hlo : -Kb ≤ Xsp L G B := by
      have h1 := HypMorse.fPlus_le_Xsp hfc hucI
      have := (hBu uc hucI).1
      have := hs0 uc
      unfold fPlus at h1
      linarith
    rw [abs_le]
    refine ⟨?_, hup⟩
    have : 0 ≤ 2 * L * Real.sqrt Kg := by positivity
    linarith
  · have hlo : -(Kb + 2 * L * Real.sqrt Kg) ≤ Xsm L G B := by
      refine le_csInf hne' ?_
      rintro _ ⟨u, hu, rfl⟩
      have := hE u hu
      have := (hBu u hu).1
      unfold fMinus
      nlinarith
    have hup : Xsm L G B ≤ Kb := by
      have h1 := HypMorse.Xsm_le_fMinus hfmc hucI
      have := (hBu uc hucI).2
      have := hs0 uc
      unfold fMinus at h1
      linarith
    rw [abs_le]
    refine ⟨hlo, ?_⟩
    have : 0 ≤ 2 * L * Real.sqrt Kg := by positivity
    linarith

variable {F : SymbolFamily Par} {K : Set Par}

/-- Uniform bound of the band ends over a compact parameter set. -/
lemma band_bdd (hK : IsCompact K) (hH : HypOn F K) (hD0 : DM F K 0) :
    ∃ Cb : ℝ, ∀ μ ∈ K, |F.bandLo μ| ≤ Cb ∧ |F.bandHi μ| ≤ Cb := by
  obtain ⟨KbG, hKG⟩ := jet_bdd K hK F.L 0 (fun j => regBudget 0 - 10 * (j / 2)) F.G (fun j hj => (hD0.reg j hj).1)
  obtain ⟨KbB, hKB⟩ := jet_bdd K hK F.L 0 (fun j => regBudget 0 - 10 * (j / 2)) F.B (fun j hj => (hD0.reg j hj).2)
  refine ⟨KbB 0 + 2 * F.L * Real.sqrt (KbG 0), fun μ hμ => ?_⟩
  obtain ⟨g, hyp, hG2, hB2⟩ := actionS0_data F K hH hD0 hμ
  have := abs_band_le (L := F.L) F.L_pos hyp hG2 hB2 (Kg := KbG 0) (Kb := KbB 0) (fun u hu => hKG 0 le_rfl μ hμ u hu)
    (fun u hu => hKB 0 le_rfl μ hμ u hu)
  exact ⟨this.2, this.1⟩

end BandBound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.x0_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.x0_hasDerivAt

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.w_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.w_bd

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.x0_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.x0_bd

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.band_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.band_bdd

end FormalResearch.JacobiEigenvectors.TheoremA

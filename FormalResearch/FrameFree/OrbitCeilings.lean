import Mathlib
import FormalResearch.FrameFree.GateOverlap

/-!
# Orbit ceilings, gate reflections and the geodesic separator (Paper P, appendices B and E)

Finite-dimensional real/complex-analysis and algebra results of Paper P ("Detecting time reversal
without reference frames"), from `paper/long/app_e_locc_proof.tex` and `paper/long/app_b_typical.tex`.
Every theorem here is **proved** (kernel-checked, using only the standard Lean axioms); the file imports
`Mathlib` and `FormalResearch.FrameFree.GateOverlap` (for `δg`, `FKmag`, `dgate`).

## What is formalised

* `lem:e-schmidtcap` (`schmidtCap`): the Schmidt cap `‖B(x,y)‖ ≤ a c + b (1-c)` for a bilinear map
  with a rank-one-plus-remainder bound.
* `lem:s3-separator` (`geodesic_sign_separator`; `geodesic_FK_cos` for the `cos²(2ℓ)` corollary of
  `thm:threequbitgeodesicequality` (b)): for a compact geodesic space, both infima are attained and
  equal `2 d(x, Z)`.
* `prop:t34l-universal-schmidt-comparison` (`gsc`): the universal Schmidt comparison, via a rational
  tangent point and monotone reductions.
* The gate algebra of the GLM-Pauli coefficients `u_a` (`Gate`) and its Hadamard image `Tu` (`uT`),
  with `t_j = cos 2c_j`, `s_j = 2 sin c_j cos c_j`; the half-chamber ordering `Gate.Half`.
* `lem:t34l-mixed-sign-exclusion` (`mst_exclusion_direct`, `mst_exclusion_cross`) and
  `lem:t34l-allfour-exclusion` (`afe_four_gate_direct/cross`, `afe_triple_gate_direct/cross`), at the level
  of admissible candidates (`Admissible`, `candVal`), both heavy cuts.
* `lem:t34l-orbit-reflections`: `flip3_u`, `flip3_uT`, `refl_u`, `refl_uT` (the matrix identities GOR-1..3),
  the complex-orthogonal cap `cap` with its invariances (`cap_conj`, `cap_sign`, `cap_perm`, `cap_smul`),
  and `reflections_reduce_to_half_chamber`.
* `lem:t34k-bell-orbit`, the exact algebra: `goc_trace_of_active`, `goc_reconstruct`,
  `goc_candidate_of_active` (GOC-trace to GOC-reconstruct, GOC-positive and GOC-admissible), and the
  unbounded-orbit estimate `ratio_le_half_add` (with `sum_entry_sq`, `two_norm_sq_le`).

## What is not formalised

`lem:e-sqrt` (no short complete argument found); the existence/stationarity analysis of the orbit
maximiser in `lem:t34k-bell-orbit` (orbit closedness, real SVD, first-order conditions).
-/

open scoped InnerProductSpace ComplexConjugate Matrix

set_option linter.unusedSimpArgs false

namespace FormalResearch.FrameFree.OrbitCeilings

noncomputable section
/-! ## `lem:e-schmidtcap` -/

/-- Scalar core: `a·PQ + b·RS ≤ ac + b(1-c)` for `b ≤ a`, `P²+R² = Q²+S² = 1`, `P²,Q² ≤ c`. -/
theorem schmidtCap_scalar {a b c P Q R S : ℝ} (hba : b ≤ a) (hb : 0 ≤ b)
    (hPR : P ^ 2 + R ^ 2 = 1) (hQS : Q ^ 2 + S ^ 2 = 1) (hPc : P ^ 2 ≤ c) (hQc : Q ^ 2 ≤ c) :
    a * (P * Q) + b * (R * S) ≤ a * c + b * (1 - c) := by
  have h1 : P * Q ≤ (P ^ 2 + Q ^ 2) / 2 := by nlinarith [sq_nonneg (P - Q)]
  have h2 : R * S ≤ (R ^ 2 + S ^ 2) / 2 := by nlinarith [sq_nonneg (R - S)]
  have ha : 0 ≤ a := le_trans hb hba
  have h3 : a * (P * Q) ≤ a * ((P ^ 2 + Q ^ 2) / 2) := mul_le_mul_of_nonneg_left h1 ha
  have h4 : b * (R * S) ≤ b * ((R ^ 2 + S ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hb
  have h5 : R ^ 2 + S ^ 2 = 2 - (P ^ 2 + Q ^ 2) := by linarith
  have h6 : P ^ 2 + Q ^ 2 ≤ 2 * c := by linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hba) (sub_nonneg.2 h6)]

section schmidt
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]

/-- The component of `x` orthogonal to a unit vector `u`. -/
noncomputable def perp (u x : E₁) : E₁ := x - inner ℂ u x • u

theorem norm_perp_sq {u x : E₁} (hu : ‖u‖ = 1) :
    ‖perp u x‖ ^ 2 = ‖x‖ ^ 2 - ‖inner ℂ u x‖ ^ 2 := by
  unfold perp
  have h := @norm_sub_sq ℂ E₁ _ _ _ x (inner ℂ u x • u)
  rw [inner_smul_right, norm_smul, hu] at h
  have h2 : inner ℂ x u = conj (inner ℂ u x) := (inner_conj_symm _ _).symm
  rw [h2] at h
  have h3 : (conj (inner ℂ u x) * inner ℂ u x).re = ‖inner ℂ u x‖ ^ 2 := by
    rw [Complex.conj_mul']; simp [← Complex.ofReal_pow]
  rw [h]
  have : RCLike.re (conj (inner ℂ u x) * inner ℂ u x) = ‖inner ℂ u x‖ ^ 2 := h3
  rw [mul_comm (inner ℂ u x), this]; ring

/-- `lem:e-schmidtcap` (RO-Schmidt), proved.  `B x y = ⟨x ⊗ y, χ⟩` is the overlap functional of a unit
vector `χ ∈ E₁ ⊗ E₂` whose top Schmidt term is `a u₀ ⊗ v₀` (`hR`: the rest of the Schmidt expansion lives on
`u₀^⊥ ⊗ v₀^⊥` with operator norm `≤ b`).  If unit `x, y` have `|⟨u₀,x⟩|², |⟨v₀,y⟩|² ≤ c` then
`|B x y| ≤ a c + b (1-c)`. -/
theorem schmidtCap (B : E₁ → E₂ → ℂ) {u₀ : E₁} {v₀ : E₂} (hu : ‖u₀‖ = 1) (hv : ‖v₀‖ = 1)
    {a b c : ℝ} (hba : b ≤ a) (hb : 0 ≤ b)
    (hR : ∀ x y, ‖B x y - (a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀)‖
      ≤ b * ‖perp u₀ x‖ * ‖perp v₀ y‖)
    {x : E₁} {y : E₂} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxc : ‖inner ℂ u₀ x‖ ^ 2 ≤ c) (hyc : ‖inner ℂ v₀ y‖ ^ 2 ≤ c) :
    ‖B x y‖ ≤ a * c + b * (1 - c) := by
  have ha : 0 ≤ a := le_trans hb hba
  have h1 : ‖B x y‖ ≤ a * (‖inner ℂ u₀ x‖ * ‖inner ℂ v₀ y‖)
      + b * (‖perp u₀ x‖ * ‖perp v₀ y‖) := by
    have hn : ‖(a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀)‖
        = a * (‖inner ℂ u₀ x‖ * ‖inner ℂ v₀ y‖) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha, norm_inner_symm x u₀,
        norm_inner_symm y v₀]
    have := hR x y
    calc ‖B x y‖ ≤ ‖(a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀)‖
          + ‖B x y - (a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀)‖ := by
          have := norm_add_le ((a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀))
            (B x y - (a : ℂ) * (inner ℂ x u₀ * inner ℂ y v₀))
          simpa using this
      _ ≤ _ := by rw [hn]; nlinarith [this]
  have hP := norm_perp_sq (u := u₀) (x := x) hu
  have hQ := norm_perp_sq (u := v₀) (x := y) hv
  rw [hx] at hP; rw [hy] at hQ
  have := schmidtCap_scalar (a := a) (b := b) (c := c) (P := ‖inner ℂ u₀ x‖)
    (Q := ‖inner ℂ v₀ y‖) (R := ‖perp u₀ x‖) (S := ‖perp v₀ y‖) hba hb (by linarith)
    (by linarith) hxc hyc
  linarith

end schmidt

/-! ## `lem:s3-separator` (geodesic sign separator) -/

section separator

/-- A (compact) metric space is *geodesic* if any two points are joined by a continuous path along which
distance from the start is `t · d(x,y)` and distance to the end is `(1-t) d(x,y)`. -/
def IsGeodesicSpace (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ x y : Y, ∃ γ : ℝ → Y, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, dist x (γ t) = t * dist x y ∧ dist (γ t) y = (1 - t) * dist x y

variable {Y : Type*} [MetricSpace Y]

/-- An isometry preserving the zero set of `f` preserves the distance to it. -/
theorem infDist_zeroSet_map {f : Y → ℝ} (φ : Y ≃ᵢ Y) (hφ : ∀ y, f (φ y) = 0 ↔ f y = 0) (y : Y) :
    Metric.infDist (φ y) (f ⁻¹' {0}) = Metric.infDist y (f ⁻¹' {0}) := by
  have himg : φ '' (f ⁻¹' {0}) = f ⁻¹' {0} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hφ z).2 hz
    · intro hw
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      have := hφ (φ.symm w)
      rw [φ.apply_symm_apply] at this
      exact this.1 hw
  have := Metric.infDist_image (t := f ⁻¹' {0}) (x := y) φ.isometry
  rw [himg] at this
  exact this

variable [CompactSpace Y]

omit [CompactSpace Y] in
/-- Core of the separator: an isometry `φ` with `f ∘ φ = -f` moves `x` at least `2 d(x, Z)`. -/
theorem dist_ge_two_infDist (hgeo : IsGeodesicSpace Y) {f : Y → ℝ} (hf : Continuous f)
    (φ : Y ≃ᵢ Y) (hφ : ∀ y, f (φ y) = - f y) (x : Y) :
    2 * Metric.infDist x (f ⁻¹' {0}) ≤ dist x (φ x) := by
  by_cases hx : f x = 0
  · have : Metric.infDist x (f ⁻¹' {0}) = 0 :=
      Metric.infDist_zero_of_mem (by simpa using hx)
    rw [this]; simp
  · obtain ⟨γ, hγc, hγ0, hγ1, hγd⟩ := hgeo x (φ x)
    have hcont : ContinuousOn (f ∘ γ) (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]; exact hf.comp_continuousOn hγc
    have hmem : (0 : ℝ) ∈ Set.uIcc ((f ∘ γ) 0) ((f ∘ γ) 1) := by
      simp only [Function.comp, hγ0, hγ1, hφ]
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne hx with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hcont hmem
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
    have hp : γ t ∈ f ⁻¹' {0} := hft
    obtain ⟨hd1, hd2⟩ := hγd t ht'
    have h1 : Metric.infDist x (f ⁻¹' {0}) ≤ dist x (γ t) := Metric.infDist_le_dist_of_mem hp
    have h2 : Metric.infDist (φ x) (f ⁻¹' {0}) ≤ dist (φ x) (γ t) :=
      Metric.infDist_le_dist_of_mem hp
    have h3 : Metric.infDist (φ x) (f ⁻¹' {0}) = Metric.infDist x (f ⁻¹' {0}) :=
      infDist_zeroSet_map φ (fun y => by rw [hφ y]; simp) x
    rw [dist_comm (φ x)] at h2
    have : dist x (φ x) = dist x (γ t) + dist (γ t) (φ x) := by
      rw [hd1, hd2]; ring
    linarith

/-- `lem:s3-separator`.  `Y` compact geodesic, `𝒢` a family of isometries fixing `f`, `𝒞` an isometry with
`f ∘ 𝒞 = -f`, `Z = f⁻¹(0)`, and `𝒥 ⊆ 𝒢𝒞` a family of isometries such that every point of `Z` is fixed by a
member of `𝒥`.  Then for every `x`, `inf_{h∈𝒢} d(x, h𝒞x)` and `inf_{J∈𝒥} d(x, Jx)` are both attained and
equal `2 d(x, Z)`.  (Involutivity of `𝒞`, `𝒥` and the group property of `𝒢` are not needed.) -/
theorem geodesic_sign_separator (hgeo : IsGeodesicSpace Y) {f : Y → ℝ} (hf : Continuous f)
    (G : Set (Y ≃ᵢ Y)) (C : Y ≃ᵢ Y) (hG : ∀ h ∈ G, ∀ y, f (h y) = f y)
    (hC : ∀ y, f (C y) = - f y) (J : Set (Y ≃ᵢ Y))
    (hJG : ∀ j ∈ J, ∃ h ∈ G, ∀ y, j y = h (C y))
    (hJfix : ∀ z, f z = 0 → ∃ j ∈ J, j z = z) (x : Y) :
    IsLeast {r : ℝ | ∃ h ∈ G, r = dist x (h (C x))} (2 * Metric.infDist x (f ⁻¹' {0})) ∧
    IsLeast {r : ℝ | ∃ j ∈ J, r = dist x (j x)} (2 * Metric.infDist x (f ⁻¹' {0})) := by
  set Z : Set Y := f ⁻¹' {0} with hZ
  have hZc : IsClosed Z := isClosed_singleton.preimage hf
  -- the composite `h ∘ C` flips the sign of `f`
  have hflip : ∀ h ∈ G, ∀ y, f ((C.trans h) y) = - f y := by
    intro h hh y
    show f (h (C y)) = - f y
    rw [hG h hh, hC]
  have hlow : ∀ h ∈ G, 2 * Metric.infDist x Z ≤ dist x (h (C x)) := fun h hh =>
    dist_ge_two_infDist hgeo hf (C.trans h) (hflip h hh) x
  -- `Z` is nonempty
  have hZne : Z.Nonempty := by
    by_cases hx : f x = 0
    · exact ⟨x, hx⟩
    · obtain ⟨γ, hγc, hγ0, hγ1, -⟩ := hgeo x (C x)
      have hcont : ContinuousOn (f ∘ γ) (Set.uIcc 0 1) := by
        rw [Set.uIcc_of_le zero_le_one]; exact hf.comp_continuousOn hγc
      have hmem : (0 : ℝ) ∈ Set.uIcc ((f ∘ γ) 0) ((f ∘ γ) 1) := by
        simp only [Function.comp, hγ0, hγ1, hC]
        rw [Set.mem_uIcc]
        rcases lt_or_gt_of_ne hx with h | h
        · left; constructor <;> linarith
        · right; constructor <;> linarith
      obtain ⟨t, -, hft⟩ := intermediate_value_uIcc hcont hmem
      exact ⟨γ t, hft⟩
  obtain ⟨z, hzZ, hzd⟩ := (hZc.isCompact).exists_infDist_eq_dist hZne x
  obtain ⟨j, hjJ, hjz⟩ := hJfix z hzZ
  obtain ⟨h, hhG, hjh⟩ := hJG j hjJ
  have hjx : dist x (j x) ≤ 2 * Metric.infDist x Z := by
    have : dist (j z) (j x) = dist z x := j.dist_eq z x
    rw [hjz] at this
    calc dist x (j x) ≤ dist x z + dist z (j x) := dist_triangle _ _ _
      _ = 2 * Metric.infDist x Z := by rw [this, dist_comm z x, hzd]; ring
  have hjx' : dist x (j x) = dist x (h (C x)) := by rw [hjh]
  have hlowj : 2 * Metric.infDist x Z ≤ dist x (j x) := by rw [hjx']; exact hlow h hhG
  have heq : dist x (j x) = 2 * Metric.infDist x Z := le_antisymm hjx hlowj
  refine ⟨⟨⟨h, hhG, ?_⟩, ?_⟩, ⟨⟨j, hjJ, ?_⟩, ?_⟩⟩
  · rw [← hjx', heq]
  · rintro r ⟨h', hh', rfl⟩; exact hlow h' hh'
  · exact heq.symm
  · rintro r ⟨j', hj', rfl⟩
    obtain ⟨h', hh', hjh'⟩ := hJG j' hj'
    rw [show dist x (j' x) = dist x (h' (C x)) by rw [hjh']]
    exact hlow h' hh'

end separator

/-! ## `prop:t34l-universal-schmidt-comparison` (GSC) -/

section gsc

/-- The tangent point (rational replacement for `√5/8`). -/
noncomputable def h0 : ℝ := 7 / 25

theorem sqrt_le_tangent {p : ℝ} (hp : 0 ≤ p) : Real.sqrt p ≤ (p + h0 ^ 2) / (2 * h0) := by
  have h0pos : 0 < h0 := by unfold h0; norm_num
  rw [le_div_iff₀ (by positivity)]
  have := Real.sq_sqrt hp
  nlinarith [sq_nonneg (Real.sqrt p - h0)]

/-- The comparison at `x = y = z`, `q = z²`, `F ≥ max q (1-q)`. -/
theorem gsc_diag {q F : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hF1 : q ≤ F) (hF2 : 1 - q ≤ F) :
    (1 + 3 * F) / 4 * ((1 + 3 * q) / 4)
      + (1 - (1 + 3 * F) / 4) * (((1 + 3 * q) / 4 * ((1 - q) / 4) + h0 ^ 2) / (2 * h0)) ≤ F := by
  unfold h0
  have hslope : 0 ≤ 22427 / 22400 - 177 * q / 448 - 225 * q ^ 2 / 896 := by nlinarith
  rcases le_total q (1 / 2) with hq | hq
  · have hv : 0 ≤ 1 / 2 - q := by linarith
    have hP : 0 ≤ 5625 * q ^ 3 + 8850 * q ^ 2 - 39227 * q + 16800 := by
      nlinarith [mul_nonneg (mul_nonneg hv hv) hv, mul_nonneg (mul_nonneg hq0 hv) hv,
        mul_nonneg (mul_nonneg hq0 hq0) hv, mul_nonneg (mul_nonneg hq0 hq0) hq0]
    have he : 0 ≤ F - (1 - q) := by linarith
    have key : F - ((1 + 3 * F) / 4 * ((1 + 3 * q) / 4)
      + (1 - (1 + 3 * F) / 4) * (((1 + 3 * q) / 4 * ((1 - q) / 4) + (7 / 25) ^ 2) / (2 * (7 / 25))))
        = (5625 * q ^ 3 + 8850 * q ^ 2 - 39227 * q + 16800) / 22400
          + (F - (1 - q)) * (22427 / 22400 - 177 * q / 448 - 225 * q ^ 2 / 896) := by ring
    nlinarith [mul_nonneg he hslope]
  · have hv : 0 ≤ q - 1 / 2 := by linarith
    have hw : 0 ≤ 1 - q := by linarith
    have hP : 0 ≤ (1 - q) * (5625 * q ^ 2 + 8850 * q - 5627) := by
      apply mul_nonneg hw; nlinarith
    have he : 0 ≤ F - q := by linarith
    have key : F - ((1 + 3 * F) / 4 * ((1 + 3 * q) / 4)
      + (1 - (1 + 3 * F) / 4) * (((1 + 3 * q) / 4 * ((1 - q) / 4) + (7 / 25) ^ 2) / (2 * (7 / 25))))
        = (1 - q) * (5625 * q ^ 2 + 8850 * q - 5627) / 22400
          + (F - q) * (22427 / 22400 - 177 * q / 448 - 225 * q ^ 2 / 896) := by ring
    nlinarith [mul_nonneg he hslope]

/-- The case `y = z` of (GSC) after the tangent bound. -/
theorem gsc_xz {x z F : ℝ} (hx : 0 ≤ x) (hxz : x ≤ z) (hz0 : 0 ≤ z)
    (hF1 : z ^ 2 ≤ F) (hF2 : 1 - x ^ 2 ≤ F) (hF3 : F ≤ 1) :
    (1 + 3 * F) / 4 * ((1 + z ^ 2 + 2 * x * z) / 4)
      + (1 - (1 + 3 * F) / 4) * (((1 + z ^ 2 + 2 * x * z) / 4 * ((1 + z ^ 2 - 2 * x * z) / 4)
        + h0 ^ 2) / (2 * h0)) ≤ F := by
  have hF0 : 0 ≤ F := le_trans (sq_nonneg z) hF1
  have hκ : 0 ≤ 1 - (1 + 3 * F) / 4 := by linarith
  have h0pos : 0 < h0 := by unfold h0; norm_num
  have hdiff : (1 + 3 * F) / 4 * ((1 + 3 * z ^ 2) / 4)
        + (1 - (1 + 3 * F) / 4) * (((1 + 3 * z ^ 2) / 4 * ((1 - z ^ 2) / 4) + h0 ^ 2) / (2 * h0))
      - ((1 + 3 * F) / 4 * ((1 + z ^ 2 + 2 * x * z) / 4)
        + (1 - (1 + 3 * F) / 4) * (((1 + z ^ 2 + 2 * x * z) / 4 * ((1 + z ^ 2 - 2 * x * z) / 4)
        + h0 ^ 2) / (2 * h0)))
      = z * (z - x) * ((1 + 3 * F) / 8 - (1 - (1 + 3 * F) / 4) * z * (z + x) / (8 * h0)) := by
    field_simp; ring
  have hcoef : 0 ≤ (1 + 3 * F) / 8 - (1 - (1 + 3 * F) / 4) * z * (z + x) / (8 * h0) := by
    have h4 : (1 - (1 + 3 * F) / 4) * z * (z + x) ≤ (1 - (1 + 3 * F) / 4) * (2 * F) := by
      have : z * (z + x) ≤ 2 * F := by nlinarith [mul_nonneg hz0 (sub_nonneg.2 hxz)]
      nlinarith [mul_le_mul_of_nonneg_left this hκ]
    have h5 : (1 - (1 + 3 * F) / 4) * (2 * F) ≤ h0 * (1 + 3 * F) := by
      unfold h0; nlinarith [sq_nonneg (F - 11 / 50)]
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h6 := mul_nonneg (mul_nonneg hz0 (sub_nonneg.2 hxz)) hcoef
  have h7 := gsc_diag (q := z ^ 2) (F := F) (by positivity) (by nlinarith) hF1
    (by nlinarith [mul_nonneg hx (sub_nonneg.2 hxz), mul_nonneg hz0 (sub_nonneg.2 hxz)])
  linarith

/-- The two top Schmidt weights of a heavy cut: `α = p₀`, `β = p₁` in terms of `x ≤ y ≤ z`. -/
noncomputable def gscα (x y z : ℝ) : ℝ := (1 + x * y + x * z + y * z) / 4
noncomputable def gscβ (x y z : ℝ) : ℝ := (1 - x * y - x * z + y * z) / 4
/-- `F = max {z², 1 - x²}`. -/
noncomputable def gscF (x z : ℝ) : ℝ := max (z ^ 2) (1 - x ^ 2)

/-- `prop:t34l-universal-schmidt-comparison` (GSC), proved (the paper's argument with the tangent point
`√5/8` replaced by the rational `7/25`; the final comparison is the same cubic Bernstein check). -/
theorem gsc {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (1 + 3 * gscF x z) / 4 * gscα x y z
      + (1 - (1 + 3 * gscF x z) / 4) * Real.sqrt (gscα x y z * gscβ x y z) ≤ gscF x z := by
  have hF1 : z ^ 2 ≤ gscF x z := le_max_left _ _
  have hF2 : 1 - x ^ 2 ≤ gscF x z := le_max_right _ _
  have hy0 : 0 ≤ y := le_trans hx hxy
  have hz0 : 0 ≤ z := le_trans hy0 hyz
  have hxz : x ≤ z := le_trans hxy hyz
  have hF0 : 0 ≤ gscF x z := le_trans (sq_nonneg z) hF1
  have hF3 : gscF x z ≤ 1 := max_le (by nlinarith) (by nlinarith)
  have hκ : 0 ≤ 1 - (1 + 3 * gscF x z) / 4 := by linarith
  have hκ' : 0 ≤ (1 + 3 * gscF x z) / 4 := by linarith
  have hα0 : 0 ≤ gscα x y z := by
    unfold gscα; nlinarith [mul_nonneg hx hy0, mul_nonneg hx hz0, mul_nonneg hy0 hz0]
  have hβ0 : 0 ≤ gscβ x y z := by
    unfold gscβ; nlinarith [mul_nonneg hx hy0, mul_nonneg hy0 hz0, mul_nonneg hx (sub_nonneg.2 hyz),
      mul_nonneg hz0 (sub_nonneg.2 hxy), mul_nonneg hy0 (sub_nonneg.2 hxy), mul_nonneg hx hx]
  have h1 := sqrt_le_tangent (mul_nonneg hα0 hβ0)
  have hαα : gscα x y z ≤ (1 + z ^ 2 + 2 * x * z) / 4 := by
    unfold gscα; nlinarith [mul_nonneg (add_nonneg hx hz0) (sub_nonneg.2 hyz)]
  have hββ : gscβ x y z ≤ (1 + z ^ 2 - 2 * x * z) / 4 := by
    unfold gscβ; nlinarith [mul_nonneg (sub_nonneg.2 hxz) (sub_nonneg.2 hyz), mul_nonneg hz0 (sub_nonneg.2 hyz),
      mul_nonneg hx (sub_nonneg.2 hyz)]
  have hαβ : gscα x y z * gscβ x y z ≤ (1 + z ^ 2 + 2 * x * z) / 4 * ((1 + z ^ 2 - 2 * x * z) / 4) :=
    mul_le_mul hαα hββ hβ0 (le_trans hα0 hαα)
  have hh0 : 0 < 2 * h0 := by unfold h0; norm_num
  have h3 : (gscα x y z * gscβ x y z + h0 ^ 2) / (2 * h0) ≤
      ((1 + z ^ 2 + 2 * x * z) / 4 * ((1 + z ^ 2 - 2 * x * z) / 4) + h0 ^ 2) / (2 * h0) :=
    div_le_div_of_nonneg_right (by linarith) hh0.le
  have h4 := mul_le_mul_of_nonneg_left hαα hκ'
  have h5 := mul_le_mul_of_nonneg_left (le_trans h1 h3) hκ
  have := gsc_xz hx hxz hz0 hF1 hF2 hF3
  linarith

end gsc

/-! ## Gate coefficients (GLM-Pauli, GLM-Schmidt) -/

section gate

/-- `(cos c_j, sin c_j)` data of a Cartan gate `U_c`, as abstract reals on the unit circle. -/
structure Gate where
  C1 : ℝ
  S1 : ℝ
  C2 : ℝ
  S2 : ℝ
  C3 : ℝ
  S3 : ℝ
  h1 : C1 ^ 2 + S1 ^ 2 = 1
  h2 : C2 ^ 2 + S2 ^ 2 = 1
  h3 : C3 ^ 2 + S3 ^ 2 = 1

namespace Gate

/-- Real parts of the GLM-Pauli coefficients `u_0, …, u_3` of `U_c`. -/
def uR (g : Gate) : Fin 4 → ℝ :=
  ![g.C1 * g.C2 * g.C3, g.C1 * g.S2 * g.S3, g.S1 * g.C2 * g.S3, g.S1 * g.S2 * g.C3]
/-- Imaginary parts of the GLM-Pauli coefficients. -/
def uI (g : Gate) : Fin 4 → ℝ :=
  ![g.S1 * g.S2 * g.S3, g.S1 * g.C2 * g.C3, g.C1 * g.S2 * g.C3, g.C1 * g.C2 * g.S3]
/-- `u_a ∈ ℂ`. -/
def u (g : Gate) (a : Fin 4) : ℂ := ⟨g.uR a, g.uI a⟩

/-- `t_j = cos 2c_j`, `s_j = sin 2c_j`. -/
def t1 (g : Gate) : ℝ := g.C1 ^ 2 - g.S1 ^ 2
def t2 (g : Gate) : ℝ := g.C2 ^ 2 - g.S2 ^ 2
def t3 (g : Gate) : ℝ := g.C3 ^ 2 - g.S3 ^ 2
def s1 (g : Gate) : ℝ := 2 * g.S1 * g.C1
def s2 (g : Gate) : ℝ := 2 * g.S2 * g.C2
def s3 (g : Gate) : ℝ := 2 * g.S3 * g.C3
/-- (GLM-Schmidt): squared Schmidt coefficients across the heavy cut `13|24`. -/
def p0 (g : Gate) : ℝ := (1 + g.t1 * g.t2 + g.t1 * g.t3 + g.t2 * g.t3) / 4
def p1 (g : Gate) : ℝ := (1 - g.t1 * g.t2 - g.t1 * g.t3 + g.t2 * g.t3) / 4
def p2 (g : Gate) : ℝ := (1 - g.t1 * g.t2 + g.t1 * g.t3 - g.t2 * g.t3) / 4
def p3 (g : Gate) : ℝ := (1 + g.t1 * g.t2 - g.t1 * g.t3 - g.t2 * g.t3) / 4

theorem abs_sq_0 (g : Gate) : g.uR 0 ^ 2 + g.uI 0 ^ 2 = g.p0 := by
  simp only [Gate.uR, Gate.uI, Gate.p0, Gate.t1, Gate.t2, Gate.t3]
  simp
  linear_combination (-g.C2^2/4 - g.C3^2/4 + g.S2^2/4 + g.S3^2/4 + g.C2^2*g.C3^2) * g.h1 + (-1/4 + g.S1^2/2 + g.S3^2/4 + 3*g.C3^2/4 - g.C3^2*g.S1^2) * g.h2 + (1/2 - g.S1^2/2 - g.S2^2/2 + g.S1^2*g.S2^2) * g.h3
theorem abs_sq_1 (g : Gate) : g.uR 1 ^ 2 + g.uI 1 ^ 2 = g.p1 := by
  simp only [Gate.uR, Gate.uI, Gate.p1, Gate.t1, Gate.t2, Gate.t3]
  simp
  linear_combination (-g.S2^2/4 - g.S3^2/4 + g.C2^2/4 + g.C3^2/4 + g.S2^2*g.S3^2) * g.h1 + (1/4 - g.S1^2/2 - g.C3^2/4 + g.S3^2/4 + g.C3^2*g.S1^2) * g.h2 + (g.S1^2/2 + g.S2^2/2 - g.S1^2*g.S2^2) * g.h3
theorem abs_sq_2 (g : Gate) : g.uR 2 ^ 2 + g.uI 2 ^ 2 = g.p2 := by
  simp only [Gate.uR, Gate.uI, Gate.p2, Gate.t1, Gate.t2, Gate.t3]
  simp
  linear_combination (-g.C3^2/4 - g.S2^2/4 + g.C2^2/4 + g.S3^2/4 + g.C3^2*g.S2^2) * g.h1 + (1/4 - g.S1^2/2 - g.S3^2/4 + g.C3^2/4 + g.S1^2*g.S3^2) * g.h2 + (g.S1^2/2 + g.S2^2/2 - g.S1^2*g.S2^2) * g.h3
theorem abs_sq_3 (g : Gate) : g.uR 3 ^ 2 + g.uI 3 ^ 2 = g.p3 := by
  simp only [Gate.uR, Gate.uI, Gate.p3, Gate.t1, Gate.t2, Gate.t3]
  simp
  linear_combination (-g.C2^2/4 - g.S3^2/4 + g.C3^2/4 + g.S2^2/4 + g.C2^2*g.S3^2) * g.h1 + (-1/4 + g.S1^2/2 + g.C3^2/4 + 3*g.S3^2/4 - g.S1^2*g.S3^2) * g.h2 + (1/2 - g.S1^2/2 - g.S2^2/2 + g.S1^2*g.S2^2) * g.h3
theorem cross_01 (g : Gate) : g.uR 0 * g.uR 1 + g.uI 0 * g.uI 1 = g.s2 * g.s3 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C2*g.C3*g.S2*g.S3) * g.h1
theorem cross_23 (g : Gate) : g.uR 2 * g.uR 3 + g.uI 2 * g.uI 3 = g.s2 * g.s3 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C2*g.C3*g.S2*g.S3) * g.h1
theorem cross_02 (g : Gate) : g.uR 0 * g.uR 2 + g.uI 0 * g.uI 2 = g.s1 * g.s3 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C1*g.C3*g.S1*g.S3) * g.h2
theorem cross_13 (g : Gate) : g.uR 1 * g.uR 3 + g.uI 1 * g.uI 3 = g.s1 * g.s3 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C1*g.C3*g.S1*g.S3) * g.h2
theorem cross_03 (g : Gate) : g.uR 0 * g.uR 3 + g.uI 0 * g.uI 3 = g.s1 * g.s2 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C1*g.C2*g.S1*g.S2) * g.h3
theorem cross_12 (g : Gate) : g.uR 1 * g.uR 2 + g.uI 1 * g.uI 2 = g.s1 * g.s2 / 4 := by
  simp only [Gate.uR, Gate.uI, Gate.s1, Gate.s2, Gate.s3]
  simp
  linear_combination (g.C1*g.C2*g.S1*g.S2) * g.h3

/-- `‖Σ w_a u_a‖²` for a real weight vector `w`. -/
def Qf (g : Gate) (w : Fin 4 → ℝ) : ℝ := (∑ a, w a * g.uR a) ^ 2 + (∑ a, w a * g.uI a) ^ 2

/-- The quadratic form of the weights: diagonal part `Σ w_a² p_a` and the cross terms. -/
theorem Qf_eq (g : Gate) (w : Fin 4 → ℝ) :
    g.Qf w = w 0 ^ 2 * g.p0 + w 1 ^ 2 * g.p1 + w 2 ^ 2 * g.p2 + w 3 ^ 2 * g.p3
      + ((w 0 * w 1 + w 2 * w 3) * (g.s2 * g.s3) + (w 0 * w 2 + w 1 * w 3) * (g.s1 * g.s3)
        + (w 0 * w 3 + w 1 * w 2) * (g.s1 * g.s2)) / 2 := by
  have e0 := abs_sq_0 g
  have e1 := abs_sq_1 g
  have e2 := abs_sq_2 g
  have e3 := abs_sq_3 g
  have c01 := cross_01 g
  have c23 := cross_23 g
  have c02 := cross_02 g
  have c13 := cross_13 g
  have c03 := cross_03 g
  have c12 := cross_12 g
  simp only [Qf, Fin.sum_univ_four]
  linear_combination w 0 ^ 2 * e0 + w 1 ^ 2 * e1 + w 2 ^ 2 * e2 + w 3 ^ 2 * e3
    + 2 * w 0 * w 1 * c01 + 2 * w 2 * w 3 * c23 + 2 * w 0 * w 2 * c02 + 2 * w 1 * w 3 * c13
    + 2 * w 0 * w 3 * c03 + 2 * w 1 * w 2 * c12

/-- `‖Σ w_a u_a‖² = Qf w` in `ℂ`. -/
theorem norm_sq_comb (g : Gate) (w : Fin 4 → ℝ) :
    ‖∑ a, (w a : ℂ) * g.u a‖ ^ 2 = g.Qf w := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Qf, Gate.u, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- The half-chamber ordering (MST-order). -/
structure Half (g : Gate) : Prop where
  o1 : g.s3 ≤ g.s2
  o2 : g.s2 ≤ g.s1
  o3 : g.s1 ≤ g.t3
  o4 : g.s3 ≤ g.t1
  o5 : g.t1 ≤ g.t2
  o6 : g.t2 ≤ g.t3
  o7 : 0 ≤ g.s3

/-- `δ = t₃² - s₃² = cos 4c₃`. -/
def delta (g : Gate) : ℝ := g.t3 ^ 2 - g.s3 ^ 2

/-- Hadamard image of a weight vector (`T` is symmetric and orthogonal). -/
def Tw (w : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(w 0 + w 1 + w 2 + w 3) / 2, (w 0 + w 1 - w 2 - w 3) / 2,
    (w 0 - w 1 + w 2 - w 3) / 2, (w 0 - w 1 - w 2 + w 3) / 2]

theorem Half.delta_nonneg {g : Gate} (hg : g.Half) : 0 ≤ g.delta := by
  have := hg.o7
  have h1 := hg.o4
  have h2 := hg.o5
  have h3 := hg.o6
  unfold delta; nlinarith

/-- The three two-negative-sign bounds on the direct cut. -/
theorem Half.neg_k1 {g : Gate} (hg : g.Half) : g.s2 * g.s3 - g.s1 * (g.s2 + g.s3) ≤ g.delta := by
  have := hg.o1; have := hg.o2; have := hg.o7; have := hg.delta_nonneg
  nlinarith [mul_nonneg (sub_nonneg.2 hg.o1) (sub_nonneg.2 hg.o2), mul_nonneg hg.o7 (sub_nonneg.2 hg.o2)]

theorem Half.neg_k2 {g : Gate} (hg : g.Half) : g.s1 * g.s3 - g.s2 * (g.s1 + g.s3) ≤ g.delta := by
  have := hg.o1; have := hg.o2; have := hg.o7; have := hg.delta_nonneg
  nlinarith [mul_nonneg hg.o7 (sub_nonneg.2 hg.o2), mul_nonneg hg.o7 (sub_nonneg.2 hg.o1),
    mul_nonneg (sub_nonneg.2 hg.o1) (sub_nonneg.2 hg.o2)]

theorem Half.neg_k3 {g : Gate} (hg : g.Half) : g.s1 * g.s2 - g.s3 * (g.s1 + g.s2) ≤ g.delta := by
  have h1 := hg.o1; have h2 := hg.o2; have h3 := hg.o3; have := hg.o4; have := hg.o7
  have ht : g.s3 ≤ g.t3 := le_trans h1 (le_trans h2 h3)
  unfold delta
  nlinarith [mul_nonneg (sub_nonneg.2 (le_trans h1 h2)) (sub_nonneg.2 h1),
    mul_nonneg (sub_nonneg.2 (le_trans h2 h3)) (sub_nonneg.2 (h3)),
    mul_nonneg (sub_nonneg.2 (le_trans h1 h2)) (sub_nonneg.2 h3),
    mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3), mul_nonneg hg.o7 (sub_nonneg.2 ht),
    mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]

theorem Half.cross_p1 {g : Gate} (hg : g.Half) : 4 * g.p1 ≤ 1 + g.delta := by
  have h4 := hg.o4; have h5 := hg.o5; have h6 := hg.o6; have h7 := hg.o7
  have ht : g.s3 ≤ g.t3 := le_trans h4 (le_trans h5 h6)
  unfold Gate.p1 delta
  nlinarith [mul_nonneg (sub_nonneg.2 h4) (add_nonneg (le_trans h7 (le_trans h4 h5)) (le_trans h7 ht)),
    mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 ht), mul_nonneg h7 (sub_nonneg.2 ht)]

theorem Half.cross_p2 {g : Gate} (hg : g.Half) : 4 * g.p2 ≤ 1 := by
  have h4 := hg.o4; have h5 := hg.o5; have h6 := hg.o6; have h7 := hg.o7
  have t1 : 0 ≤ g.t1 := le_trans h7 h4
  unfold Gate.p2
  nlinarith [mul_nonneg t1 (le_trans t1 h5), mul_nonneg (le_trans t1 (le_trans h5 h6)) (sub_nonneg.2 h5)]

theorem Half.cross_p3 {g : Gate} (hg : g.Half) : 4 * g.p3 ≤ 1 := by
  have h4 := hg.o4; have h5 := hg.o5; have h6 := hg.o6; have h7 := hg.o7
  have t1 : 0 ≤ g.t1 := le_trans h7 h4
  have t2 : 0 ≤ g.t2 := le_trans t1 h5
  unfold Gate.p3
  nlinarith [mul_nonneg t1 (sub_nonneg.2 h6), mul_nonneg t2 (le_trans t2 h6)]

theorem sum_p (g : Gate) : g.p0 + g.p1 + g.p2 + g.p3 = 1 := by
  unfold Gate.p0 Gate.p1 Gate.p2 Gate.p3; ring

theorem direct_full {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : ∀ a, w a = 1 ∨ w a = -1)
    (hnc : ¬ (w 0 = w 1 ∧ w 1 = w 2 ∧ w 2 = w 3)) : g.Qf w ≤ 1 + g.delta := by
  have hd := hg.delta_nonneg
  have k1 := hg.neg_k1
  have k2 := hg.neg_k2
  have k3 := hg.neg_k3
  have sc := sum_p g
  rcases hw 0 with h0 | h0 <;> rcases hw 1 with h1 | h1 <;> rcases hw 2 with h2 | h2 <;>
    rcases hw 3 with h3 | h3 <;> (try (exfalso; apply hnc; simp [h0, h1, h2, h3]; done)) <;>
    rw [Qf_eq, h0, h1, h2, h3] <;> norm_num <;> nlinarith

theorem cross_full {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : ∀ a, w a = 1 ∨ w a = -1)
    (hnc : ¬ (w 0 = w 1 ∧ w 1 = w 2 ∧ w 2 = w 3)) : g.Qf (Tw w) ≤ 1 + g.delta := by
  have hd := hg.delta_nonneg
  have c1 := hg.cross_p1
  have c2 := hg.cross_p2
  have c3 := hg.cross_p3
  have sc := sum_p g
  rcases hw 0 with h0 | h0 <;> rcases hw 1 with h1 | h1 <;> rcases hw 2 with h2 | h2 <;>
    rcases hw 3 with h3 | h3 <;> (try (exfalso; apply hnc; simp [h0, h1, h2, h3]; done)) <;>
    rw [Qf_eq] <;> simp [Tw, h0, h1, h2, h3] <;> norm_num <;> nlinarith [hg.delta_nonneg]

/-- Convexity of `Qf` at the midpoint. -/
theorem Qf_midpoint (g : Gate) (x y : Fin 4 → ℝ) :
    g.Qf (fun a => (x a + y a) / 2) ≤ (g.Qf x + g.Qf y) / 2 := by
  simp only [Qf, Fin.sum_univ_four]
  nlinarith [sq_nonneg ((x 0 * g.uR 0 + x 1 * g.uR 1 + x 2 * g.uR 2 + x 3 * g.uR 3)
      - (y 0 * g.uR 0 + y 1 * g.uR 1 + y 2 * g.uR 2 + y 3 * g.uR 3)),
    sq_nonneg ((x 0 * g.uI 0 + x 1 * g.uI 1 + x 2 * g.uI 2 + x 3 * g.uI 3)
      - (y 0 * g.uI 0 + y 1 * g.uI 1 + y 2 * g.uI 2 + y 3 * g.uI 3))]

theorem Tw_midpoint (x y : Fin 4 → ℝ) :
    Tw (fun a => (x a + y a) / 2) = fun a => (Tw x a + Tw y a) / 2 := by
  funext a; fin_cases a <;> simp [Tw] <;> ring

/-- Sign patterns of `(MST-mixed)`: entries `±1` or `0` (the inactive coordinates, at most one of them),
with both signs present. -/
def MixedSigns (w : Fin 4 → ℝ) : Prop :=
  (∀ a, w a = 1 ∨ w a = -1 ∨ w a = 0) ∧ (∀ a b, a ≠ b → w a = 0 → w b ≠ 0) ∧
    ∃ a b, w a = 1 ∧ w b = -1

/-- A mixed pattern is the midpoint of two mixed full patterns. -/
theorem MixedSigns.cases {w : Fin 4 → ℝ} (hw : MixedSigns w) :
    ((∀ a, w a = 1 ∨ w a = -1) ∧ ¬ (w 0 = w 1 ∧ w 1 = w 2 ∧ w 2 = w 3)) ∨
    ∃ x y : Fin 4 → ℝ, (∀ a, x a = 1 ∨ x a = -1) ∧ ¬ (x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3) ∧
      (∀ a, y a = 1 ∨ y a = -1) ∧ ¬ (y 0 = y 1 ∧ y 1 = y 2 ∧ y 2 = y 3) ∧
      w = fun a => (x a + y a) / 2 := by
  obtain ⟨h3, hz, a, b, ha, hb⟩ := hw
  by_cases hex : ∃ m, w m = 0
  · right
    obtain ⟨m, hm⟩ := hex
    have ham : a ≠ m := fun h => by rw [h, hm] at ha; norm_num at ha
    have hbm : b ≠ m := fun h => by rw [h, hm] at hb; norm_num at hb
    have hnz : ∀ c, c ≠ m → w c = 1 ∨ w c = -1 := by
      intro c hc
      rcases h3 c with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hz m c hc.symm hm)
    refine ⟨Function.update w m 1, Function.update w m (-1), ?_, ?_, ?_, ?_, ?_⟩
    · intro c; by_cases hc : c = m
      · subst hc; simp
      · rw [Function.update_of_ne hc]; exact hnz c hc
    · intro hnc
      have e1 : Function.update w m 1 a = 1 := by rw [Function.update_of_ne ham]; exact ha
      have e2 : Function.update w m 1 b = -1 := by rw [Function.update_of_ne hbm]; exact hb
      have : ∀ c d : Fin 4, Function.update w m 1 c = Function.update w m 1 d := by
        intro c d
        obtain ⟨p, q, r⟩ := hnc
        fin_cases c <;> fin_cases d <;> simp_all
      have := this a b; rw [e1, e2] at this; norm_num at this
    · intro c; by_cases hc : c = m
      · subst hc; simp
      · rw [Function.update_of_ne hc]; exact hnz c hc
    · intro hnc
      have e1 : Function.update w m (-1) a = 1 := by rw [Function.update_of_ne ham]; exact ha
      have e2 : Function.update w m (-1) b = -1 := by rw [Function.update_of_ne hbm]; exact hb
      have : ∀ c d : Fin 4, Function.update w m (-1) c = Function.update w m (-1) d := by
        intro c d
        obtain ⟨p, q, r⟩ := hnc
        fin_cases c <;> fin_cases d <;> simp_all
      have := this a b; rw [e1, e2] at this; norm_num at this
    · funext c; by_cases hc : c = m
      · subst hc; simp [hm]
      · rw [Function.update_of_ne hc, Function.update_of_ne hc]; ring
  · left
    push Not at hex
    refine ⟨fun c => ?_, fun hnc => ?_⟩
    · rcases h3 c with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hex c)
    · have : ∀ c d : Fin 4, w c = w d := by
        intro c d
        obtain ⟨p, q, r⟩ := hnc
        fin_cases c <;> fin_cases d <;> simp_all
      have := this a b; rw [ha, hb] at this; norm_num at this

/-- `lem:t34l-mixed-sign-exclusion`, (MST-mixed) on the direct heavy cut: every mixed-sign signed sum over
`r = 3` or `4` coordinates of the coefficient vector `u` has `|Σ ε_j u_j|² ≤ 1 + δ`. -/
theorem mst_mixed_direct {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : MixedSigns w) :
    g.Qf w ≤ 1 + g.delta := by
  rcases hw.cases with ⟨h, hnc⟩ | ⟨x, y, hx, hxn, hy, hyn, rfl⟩
  · exact direct_full hg h hnc
  · have := Qf_midpoint g x y
    have := direct_full hg hx hxn
    have := direct_full hg hy hyn
    linarith

/-- (MST-mixed) on the crossed heavy cut (coefficient vector `T u`; the weights are `T w`). -/
theorem mst_mixed_cross {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : MixedSigns w) :
    g.Qf (Tw w) ≤ 1 + g.delta := by
  rcases hw.cases with ⟨h, hnc⟩ | ⟨x, y, hx, hxn, hy, hyn, rfl⟩
  · exact cross_full hg h hnc
  · rw [Tw_midpoint]
    have := Qf_midpoint g (Tw x) (Tw y)
    have := cross_full hg hx hxn
    have := cross_full hg hy hyn
    linarith

end Gate
end gate

/-! ## Stationary candidates of the orbit ceiling: scalar exclusion -/

section candidate

/-- The scalar exclusion behind (MST-trace), (AFE-triple): a stationary value `c > κ` forces
`|L| ≥ s (2rc-(r-1))/(2c)` with `s² ≥ c`, hence `|L|² ≥ (2rc-(r-1))²/(4c)`, which is increasing in
`c > 1/2`. -/
theorem exceed_scalar {r c κ s Lnorm B : ℝ} (hr : 1 ≤ r) (hκ : 1 / 2 < κ) (hκc : κ < c)
    (hs0 : 0 < s) (hs : c ≤ s ^ 2) (hL : s * (2 * r * c - (r - 1)) / (2 * c) ≤ Lnorm)
    (hB : Lnorm ^ 2 ≤ B) (hBκ : B < (2 * r * κ - (r - 1)) ^ 2 / (4 * κ)) : False := by
  have hc : 1 / 2 < c := lt_trans hκ hκc
  have hc0 : 0 < c := by linarith
  have hκ0 : 0 < κ := by linarith
  have hq : 0 < 2 * r * c - (r - 1) := by nlinarith
  have hN : 0 ≤ s * (2 * r * c - (r - 1)) := by positivity
  have hLpos : 0 ≤ s * (2 * r * c - (r - 1)) / (2 * c) := by positivity
  -- |L|² ≥ (N/(2c))² ≥ c q² / (4c²) = q²/(4c)
  have h1 : (s * (2 * r * c - (r - 1)) / (2 * c)) ^ 2 ≤ Lnorm ^ 2 :=
    pow_le_pow_left₀ hLpos hL 2
  have h2 : (2 * r * c - (r - 1)) ^ 2 / (4 * c) ≤ (s * (2 * r * c - (r - 1)) / (2 * c)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq2 : 0 ≤ (2 * r * c - (r - 1)) ^ 2 * (4 * c) := by positivity
    have key := mul_le_mul_of_nonneg_right hs hq2
    nlinarith [key]
  -- monotonicity of `ψ(x) = (2 r x - (r-1))² / (4x)`
  have h3 : (2 * r * κ - (r - 1)) ^ 2 / (4 * κ) ≤ (2 * r * c - (r - 1)) ^ 2 / (4 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (c - κ) * (4 * r ^ 2 * (c * κ) - (r - 1) ^ 2) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_pos (sub_pos.2 hκ) (sub_pos.2 hc), sq_nonneg (r - 1), sq_nonneg r]
    nlinarith
  linarith

/-- `(MST-trace)` for `r = 3`: `g₃(κ)² - (1+δ) > 0`, i.e. `(57δ²+62δ+9)/(8(3δ+5)) > 0`. -/
theorem mst_trace_three {δ : ℝ} (hδ : 0 ≤ δ) :
    1 + δ < (2 * 3 * ((5 + 3 * δ) / 8) - (3 - 1)) ^ 2 / (4 * ((5 + 3 * δ) / 8)) := by
  rw [lt_div_iff₀ (by positivity)]; nlinarith [sq_nonneg δ]

/-- `(MST-trace)` for `r = 4`. -/
theorem mst_trace_four {δ : ℝ} (hδ : 0 ≤ δ) :
    1 + δ < (2 * 4 * ((5 + 3 * δ) / 8) - (4 - 1)) ^ 2 / (4 * ((5 + 3 * δ) / 8)) := by
  rw [lt_div_iff₀ (by positivity)]; nlinarith [sq_nonneg δ]

/-- `(AFE-triple)`. -/
theorem afe_triple {δ : ℝ} (hδ : 0 ≤ δ) :
    9 * (1 + δ) / 8 < (2 * 3 * ((5 + 3 * δ) / 8) - (3 - 1)) ^ 2 / (4 * ((5 + 3 * δ) / 8)) := by
  rw [lt_div_iff₀ (by positivity)]; nlinarith [sq_nonneg δ]

/-- The reconstruction `c = s/(2h)` of a candidate from `(s,h)` (with `k = s-h`): if `2sh ≥ 1`,
`|L| ≥ s + (r-1)(s-h)` and `|L|² ≤ B < ψ_r(κ)` then `c ≤ κ`. -/
theorem cand_core {r s h κ Lnorm B : ℝ} (hr : 1 ≤ r) (hκ : 1 / 2 < κ) (hs : 0 < s) (hh : 0 < h)
    (hnorm : 1 ≤ 2 * s * h) (hL : s + (r - 1) * (s - h) ≤ Lnorm) (hB : Lnorm ^ 2 ≤ B)
    (hBκ : B < (2 * r * κ - (r - 1)) ^ 2 / (4 * κ)) : s / (2 * h) ≤ κ := by
  by_contra hcon
  push Not at hcon
  refine exceed_scalar (r := r) (c := s / (2 * h)) (κ := κ) (s := s) (Lnorm := Lnorm) (B := B)
    hr hκ hcon hs ?_ ?_ hB hBκ
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · have : s * (2 * r * (s / (2 * h)) - (r - 1)) / (2 * (s / (2 * h))) = s + (r - 1) * (s - h) := by
      field_simp; ring
    rw [this]; exact hL

/-- (GOC-data). -/
def candJ (L Q : ℂ) (W : ℝ) : ℂ := Q * conj L + (W : ℂ) * L
def candK (Q : ℂ) (W : ℝ) : ℝ := ‖Q‖ ^ 2 - W ^ 2
def candH (L Q : ℂ) (W : ℝ) : ℝ := (conj Q * L ^ 2).re + W * ‖L‖ ^ 2
/-- The candidate value of (GOC-ceiling). -/
def candVal (r K H : ℝ) : ℝ := (2 * H - (r - 1) * K) / (4 * H - 2 * r * K)

/-- The numerical part of (GOC-admissible) that is used: `J ≠ 0`, `K, H > 0`, `K/H < 2/r` (that is `h > 0`)
and `2sh ≥ m`, multiplied out by `|J|²`. -/
structure Admissible (r m : ℝ) (L Q : ℂ) (W : ℝ) : Prop where
  J_ne : candJ L Q W ≠ 0
  K_pos : 0 < candK Q W
  H_pos : 0 < candH L Q W
  h_pos : r * candK Q W < 2 * candH L Q W
  norm_ineq : m * ‖candJ L Q W‖ ^ 2 ≤
    2 * (candH L Q W - (r - 1) * candK Q W / 2) * (candH L Q W - r * candK Q W / 2)

/-- `Re (J̄ L) = H` (the identity `Re(J̄L) = H` of (GOC-positive)). -/
theorem re_conj_J_mul (L Q : ℂ) (W : ℝ) : (conj (candJ L Q W) * L).re = candH L Q W := by
  have : conj (candJ L Q W) * L = conj Q * L ^ 2 + (W : ℂ) * ((‖L‖ ^ 2 : ℝ) : ℂ) := by
    unfold candJ
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    have h2 : conj L * L = ((‖L‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    linear_combination (W : ℂ) * h2
  rw [this, Complex.add_re]
  have h3 : (W : ℂ) * ((‖L‖ ^ 2 : ℝ) : ℂ) = ((W * ‖L‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h3, Complex.ofReal_re]; rfl

/-- `H ≤ |J| |L|`. -/
theorem candH_le (L Q : ℂ) (W : ℝ) : candH L Q W ≤ ‖candJ L Q W‖ * ‖L‖ := by
  rw [← re_conj_J_mul]
  calc (conj (candJ L Q W) * L).re ≤ ‖conj (candJ L Q W) * L‖ := Complex.re_le_norm _
    _ = ‖candJ L Q W‖ * ‖L‖ := by rw [norm_mul, RCLike.norm_conj]

/-- **Candidate-level exclusion** (the engine of `lem:t34l-mixed-sign-exclusion` and
`lem:t34l-allfour-exclusion`): an admissible candidate (with `m ≥ 1`) whose signed sum obeys
`|L|² ≤ B < ψ_r(κ)`, `ψ_r(κ) = (2rκ-(r-1))²/(4κ)`, has value `≤ κ`. -/
theorem candidate_le {r m : ℝ} {L Q : ℂ} {W : ℝ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hA : Admissible r m L Q W) {κ B : ℝ} (hκ : 1 / 2 < κ) (hB : ‖L‖ ^ 2 ≤ B)
    (hBκ : B < (2 * r * κ - (r - 1)) ^ 2 / (4 * κ)) :
    candVal r (candK Q W) (candH L Q W) ≤ κ := by
  set j := ‖candJ L Q W‖ with hj
  set K := candK Q W with hK
  set H := candH L Q W with hH
  have hj0 : 0 < j := norm_pos_iff.2 hA.J_ne
  have hK0 : 0 < K := hA.K_pos
  have hH0 : 0 < H := hA.H_pos
  have hh0 : 0 < H - r * K / 2 := by linarith [hA.h_pos]
  set s := (H - (r - 1) * K / 2) / j with hs
  set h := (H - r * K / 2) / j with hh
  have hh1 : 0 < h := by positivity
  have hsh : s - h = K / (2 * j) := by rw [hs, hh]; field_simp; ring
  have hk0 : 0 < s - h := by rw [hsh]; positivity
  have hs0 : 0 < s := by linarith
  have hval : candVal r K H = s / (2 * h) := by
    have hb : 0 < H - r * K / 2 := hh0
    have e1 : s / (2 * h) = (H - (r - 1) * K / 2) / (2 * (H - r * K / 2)) := by
      rw [hs, hh]; field_simp
    unfold candVal
    rw [e1, div_eq_div_iff (by linarith) (by positivity)]
    ring
  have hnorm : 1 ≤ 2 * s * h := by
    have := hA.norm_ineq
    have h1 : 2 * s * h = 2 * (H - (r - 1) * K / 2) * (H - r * K / 2) / j ^ 2 := by
      rw [hs, hh]; field_simp
    rw [h1, le_div_iff₀ (by positivity)]
    nlinarith
  have hL : s + (r - 1) * (s - h) ≤ ‖L‖ := by
    have e : s + (r - 1) * (s - h) = H / j := by rw [hs, hh]; field_simp; ring
    rw [e, div_le_iff₀ hj0]
    have := candH_le L Q W
    linarith
  rw [hval]
  exact cand_core hr hκ hs0 hh1 hnorm hL hB hBκ

end candidate


/-! ## The crossed cut and the exclusion theorems for the gate -/

section gateB

namespace Gate

/-- The coefficient vector `T u` of the crossed heavy cut `14|23` (up to a phase): `T` is the Hadamard matrix. -/
def uT (g : Gate) : Fin 4 → ℂ :=
  ![(g.u 0 + g.u 1 + g.u 2 + g.u 3) / 2, (g.u 0 + g.u 1 - g.u 2 - g.u 3) / 2,
    (g.u 0 - g.u 1 + g.u 2 - g.u 3) / 2, (g.u 0 - g.u 1 - g.u 2 + g.u 3) / 2]

theorem sum_uT (g : Gate) (w : Fin 4 → ℝ) :
    ∑ a, (w a : ℂ) * g.uT a = ∑ a, ((Tw w a : ℝ) : ℂ) * g.u a := by
  simp only [Fin.sum_univ_four, uT, Tw]
  simp
  ring

theorem norm_sq_comb_cross (g : Gate) (w : Fin 4 → ℝ) :
    ‖∑ a, (w a : ℂ) * g.uT a‖ ^ 2 = g.Qf (Tw w) := by
  rw [sum_uT, norm_sq_comb]

/-- `|u_a|² = p_a`. -/
def pw (g : Gate) : Fin 4 → ℝ := ![g.p0, g.p1, g.p2, g.p3]

theorem norm_sq_u (g : Gate) (a : Fin 4) : ‖g.u a‖ ^ 2 = g.pw a := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  fin_cases a
  · have := abs_sq_0 g; simp only [Gate.u, pw]; simp at this ⊢; nlinarith
  · have := abs_sq_1 g; simp only [Gate.u, pw]; simp at this ⊢; nlinarith
  · have := abs_sq_2 g; simp only [Gate.u, pw]; simp at this ⊢; nlinarith
  · have := abs_sq_3 g; simp only [Gate.u, pw]; simp at this ⊢; nlinarith

theorem sum_norm_sq_u (g : Gate) : ∑ a, ‖g.u a‖ ^ 2 = 1 := by
  simp only [Fin.sum_univ_four, norm_sq_u, pw]
  simp
  linarith [sum_p g]

theorem sum_single_mul (a : Fin 4) (f : Fin 4 → ℂ) :
    ∑ x, (((Pi.single a (1 : ℝ) : Fin 4 → ℝ) x : ℝ) : ℂ) * f x = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem sum_norm_sq_uT (g : Gate) : ∑ a, ‖g.uT a‖ ^ 2 = 1 := by
  have h : ∀ a : Fin 4, ‖g.uT a‖ ^ 2 = g.Qf (Tw (Pi.single a 1)) := by
    intro a
    rw [← norm_sq_comb_cross, sum_single_mul]
  simp only [h, Fin.sum_univ_four, Qf_eq, Tw]
  simp [Pi.single_apply]
  linarith [sum_p g]

end Gate

/-- The signed data `(L, Q, W, r)` of a sign pattern `w` (entries `±1` on the active set, `0` off it)
for a coefficient vector `μ`, in the notation of (GOC-data). -/
def sgnL (μ : Fin 4 → ℂ) (w : Fin 4 → ℝ) : ℂ := ∑ a, (w a : ℂ) * μ a
def sgnQ (μ : Fin 4 → ℂ) (w : Fin 4 → ℝ) : ℂ := ∑ a, ((w a ^ 2 : ℝ) : ℂ) * μ a ^ 2
def sgnW (μ : Fin 4 → ℂ) (w : Fin 4 → ℝ) : ℝ := ∑ a, (1 - w a ^ 2) * ‖μ a‖ ^ 2
def sgnR (w : Fin 4 → ℝ) : ℝ := ∑ a, w a ^ 2

theorem MixedSigns_sgnR {w : Fin 4 → ℝ} (hw : Gate.MixedSigns w) : sgnR w = 3 ∨ sgnR w = 4 := by
  obtain ⟨h3, hz, -⟩ := hw
  by_cases hex : ∃ m, w m = 0
  · left
    obtain ⟨m, hm⟩ := hex
    have hone : ∀ c, c ≠ m → w c ^ 2 = 1 := by
      intro c hc
      rcases h3 c with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · exact absurd h (hz m c hc.symm hm)
    have e : ∀ c, w c ^ 2 = 1 - (if c = m then 1 else 0) := by
      intro c
      by_cases hc : c = m
      · subst hc; simp [hm]
      · simp [hc, hone c hc]
    simp only [sgnR, e, Finset.sum_sub_distrib]
    simp
    norm_num
  · right
    push Not at hex
    have hone : ∀ c, w c ^ 2 = 1 := by
      intro c
      rcases h3 c with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · exact absurd h (hex c)
    simp [sgnR, hone]

end gateB


/-! ## `lem:t34l-mixed-sign-exclusion` -/

section mixedExclusion

/-- **`lem:t34l-mixed-sign-exclusion`, direct heavy cut.**  In the half-chamber, for a mixed-sign pattern `w`
on `r = 3` or `4` coordinates (`r = sgnR w`), every admissible candidate of (GOC-ceiling) built from the
direct coefficients `u` has value `≤ κ = (5+3δ)/8`.  (The paper's (MST-mixed) is `mst_mixed_direct`, the
final comparison (MST-trace) is `mst_trace_three/four`.) -/
theorem mst_exclusion_direct {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : Gate.MixedSigns w)
    (hA : Admissible (sgnR w) (∑ a, ‖g.u a‖ ^ 2) (sgnL g.u w) (sgnQ g.u w) (sgnW g.u w)) :
    candVal (sgnR w) (candK (sgnQ g.u w) (sgnW g.u w))
      (candH (sgnL g.u w) (sgnQ g.u w) (sgnW g.u w)) ≤ (5 + 3 * g.delta) / 8 := by
  have hd := hg.delta_nonneg
  have hB : ‖sgnL g.u w‖ ^ 2 ≤ 1 + g.delta := by
    have := Gate.norm_sq_comb g w
    rw [show sgnL g.u w = ∑ a, (w a : ℂ) * g.u a from rfl, this]
    exact Gate.mst_mixed_direct hg hw
  have hm : 1 ≤ ∑ a, ‖g.u a‖ ^ 2 := (Gate.sum_norm_sq_u g).ge
  rcases MixedSigns_sgnR hw with h3 | h4
  · refine candidate_le (by rw [h3]; norm_num) hm hA (κ := (5 + 3 * g.delta) / 8) (by linarith) hB ?_
    rw [h3]; exact mst_trace_three hd
  · refine candidate_le (by rw [h4]; norm_num) hm hA (κ := (5 + 3 * g.delta) / 8) (by linarith) hB ?_
    rw [h4]; exact mst_trace_four hd

/-- The same on the crossed heavy cut (coefficients `T u`). -/
theorem mst_exclusion_cross {g : Gate} (hg : g.Half) {w : Fin 4 → ℝ} (hw : Gate.MixedSigns w)
    (hA : Admissible (sgnR w) (∑ a, ‖g.uT a‖ ^ 2) (sgnL g.uT w) (sgnQ g.uT w) (sgnW g.uT w)) :
    candVal (sgnR w) (candK (sgnQ g.uT w) (sgnW g.uT w))
      (candH (sgnL g.uT w) (sgnQ g.uT w) (sgnW g.uT w)) ≤ (5 + 3 * g.delta) / 8 := by
  have hd := hg.delta_nonneg
  have hB : ‖sgnL g.uT w‖ ^ 2 ≤ 1 + g.delta := by
    have := Gate.norm_sq_comb_cross g w
    rw [show sgnL g.uT w = ∑ a, (w a : ℂ) * g.uT a from rfl, this]
    exact Gate.mst_mixed_cross hg hw
  have hm : 1 ≤ ∑ a, ‖g.uT a‖ ^ 2 := (Gate.sum_norm_sq_uT g).ge
  rcases MixedSigns_sgnR hw with h3 | h4
  · refine candidate_le (by rw [h3]; norm_num) hm hA (κ := (5 + 3 * g.delta) / 8) (by linarith) hB ?_
    rw [h3]; exact mst_trace_three hd
  · refine candidate_le (by rw [h4]; norm_num) hm hA (κ := (5 + 3 * g.delta) / 8) (by linarith) hB ?_
    rw [h4]; exact mst_trace_four hd

end mixedExclusion


/-! ## `lem:t34l-allfour-exclusion` -/

section allfour

/-- The scalar contradiction of the all-aligned `r = 4` case: `λ(h-2) < 2` from `c > κ`, then
`a/K ≤ 2(h-3/2)(h-2)` contradicts (AFE-four). -/
theorem afe_four_scalar {lam a K h : ℝ} (hlam : 1 ≤ lam) (hK : 0 < K) (h2 : 2 < h)
    (hnorm : a ≤ K * (2 * (h - 3 / 2) * (h - 2)))
    (hc : (4 + lam) / 8 < (2 * h - 3) / (4 * (h - 2)))
    (hAFE : (2 * lam + 8) * K ≤ lam ^ 2 * a) : False := by
  have hx : 0 < h - 2 := by linarith
  rw [lt_div_iff₀ (by positivity)] at hc
  have h1 : lam * (h - 2) < 2 := by nlinarith
  have h3 : lam ^ 2 * a ≤ lam ^ 2 * (K * (2 * (h - 3 / 2) * (h - 2))) :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have h4 : (lam * (h - 2)) ^ 2 < 4 := by nlinarith [mul_pos (by linarith : 0 < lam) hx]
  have h5 : lam ^ 2 * (2 * (h - 3 / 2) * (h - 2)) < 2 * lam + 8 := by
    nlinarith [mul_pos (by linarith : 0 < lam) hx]
  nlinarith [mul_lt_mul_of_pos_left h5 hK]

/-- Candidate-level exclusion for the all-aligned `r = 4` candidate (`W = 0`): if `(AFE-four)` holds,
`(2λ+8)|Q|² ≤ λ²|L|²` with `λ = 1+3δ`, then an admissible candidate has value `≤ (5+3δ)/8`. -/
theorem afe_four_candidate {L Q : ℂ} (hA : Admissible 4 1 L Q 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAFE : (2 * (1 + 3 * δ) + 8) * ‖Q‖ ^ 2 ≤ (1 + 3 * δ) ^ 2 * ‖L‖ ^ 2) :
    candVal 4 (candK Q 0) (candH L Q 0) ≤ (5 + 3 * δ) / 8 := by
  by_contra hcon
  push Not at hcon
  have hK : candK Q 0 = ‖Q‖ ^ 2 := by unfold candK; ring
  have hKpos : 0 < ‖Q‖ ^ 2 := by rw [← hK]; exact hA.K_pos
  have hJ : ‖candJ L Q 0‖ ^ 2 = ‖Q‖ ^ 2 * ‖L‖ ^ 2 := by
    unfold candJ
    simp [norm_mul, mul_pow]
  have hn := hA.norm_ineq
  rw [hJ, hK] at hn
  set K := ‖Q‖ ^ 2 with hKdef
  set H := candH L Q 0 with hH
  have hH2 : 2 * K < H := by
    have := hA.h_pos; rw [hK] at this; linarith
  have hKp : 0 < K := hKpos
  set h := H / K with hhdef
  have hh2 : 2 < h := by rw [hhdef, lt_div_iff₀ hKp]; linarith
  have hHh : H = h * K := by rw [hhdef]; field_simp
  have hnorm : ‖L‖ ^ 2 ≤ K * (2 * (h - 3 / 2) * (h - 2)) := by
    have e : 2 * (H - (4 - 1) * K / 2) * (H - 4 * K / 2) = K ^ 2 * (2 * (h - 3 / 2) * (h - 2)) := by
      rw [hHh]; ring
    rw [e] at hn
    have : K * (K * ‖L‖ ^ 2) ≤ K * (K * (K * (2 * (h - 3 / 2) * (h - 2)))) := by nlinarith
    have := le_of_mul_le_mul_left this hKp
    exact le_of_mul_le_mul_left this hKp
  have hval : candVal 4 K H = (2 * h - 3) / (4 * (h - 2)) := by
    unfold candVal; rw [hHh]
    rw [div_eq_div_iff (by nlinarith) (by nlinarith)]
    ring
  rw [hK, hval] at hcon
  exact afe_four_scalar (lam := 1 + 3 * δ) (a := ‖L‖ ^ 2) (K := K) (h := h) (by linarith) hKp hh2 hnorm
    (by have : (4 + (1 + 3 * δ)) / 8 = (5 + 3 * δ) / 8 := by ring
        rw [this]; exact hcon) hAFE

/-- (AFE-four) in the box: for `s ≤ v_j ≤ t`, `s² + t² = 1`, `δ = t² - s²`,
`(2λ+8)(Πv_j² + Π(1-v_j²)) ≤ λ² (1 + Σ_{i<j} v_i v_j)`. -/
theorem afe_four_ineq {s t v1 v2 v3 : ℝ} (hs0 : 0 ≤ s) (hst : s ^ 2 + t ^ 2 = 1)
    (h1 : s ≤ v1) (h1' : v1 ≤ t) (h2 : s ≤ v2) (h2' : v2 ≤ t) (h3 : s ≤ v3) (h3' : v3 ≤ t) :
    (2 * (1 + 3 * (t ^ 2 - s ^ 2)) + 8) * (v1 ^ 2 * v2 ^ 2 * v3 ^ 2
        + (1 - v1 ^ 2) * (1 - v2 ^ 2) * (1 - v3 ^ 2))
      ≤ (1 + 3 * (t ^ 2 - s ^ 2)) ^ 2 * (1 + v1 * v2 + v1 * v3 + v2 * v3) := by
  set δ := t ^ 2 - s ^ 2 with hδ
  have hv0 : ∀ v, s ≤ v → 0 ≤ v := fun v h => le_trans hs0 h
  have hsq : ∀ v, s ≤ v → v ≤ t → |v ^ 2 - 1 / 2| ≤ δ / 2 := by
    intro v hv hv'
    have a1 : s ^ 2 ≤ v ^ 2 := by nlinarith [hv0 v hv]
    have a2 : v ^ 2 ≤ t ^ 2 := by nlinarith [hv0 v hv]
    rw [abs_le]; constructor <;> nlinarith
  have hδ0 : 0 ≤ δ := by
    have := hsq v1 h1 h1'; have := abs_nonneg (v1 ^ 2 - 1 / 2); linarith
  have hδ1 : δ ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg t]
  have hx : ∀ v, s ≤ v → v ≤ t → (v ^ 2 - 1 / 2 ≤ δ / 2 ∧ -(δ / 2) ≤ v ^ 2 - 1 / 2) :=
    fun v hv hv' => ⟨(abs_le.1 (hsq v hv hv')).2, (abs_le.1 (hsq v hv hv')).1⟩
  obtain ⟨x1u, x1l⟩ := hx v1 h1 h1'
  obtain ⟨x2u, x2l⟩ := hx v2 h2 h2'
  obtain ⟨x3u, x3l⟩ := hx v3 h3 h3'
  -- K ≤ 1/4 + 3δ²/4
  have hK : v1 ^ 2 * v2 ^ 2 * v3 ^ 2 + (1 - v1 ^ 2) * (1 - v2 ^ 2) * (1 - v3 ^ 2)
      ≤ (1 + 3 * δ ^ 2) / 4 := by
    have e : v1 ^ 2 * v2 ^ 2 * v3 ^ 2 + (1 - v1 ^ 2) * (1 - v2 ^ 2) * (1 - v3 ^ 2)
        = 1 / 4 + ((v1 ^ 2 - 1 / 2) * (v2 ^ 2 - 1 / 2) + (v1 ^ 2 - 1 / 2) * (v3 ^ 2 - 1 / 2)
          + (v2 ^ 2 - 1 / 2) * (v3 ^ 2 - 1 / 2)) := by ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 x1u) (by linarith : 0 ≤ δ / 2 + (v2 ^ 2 - 1 / 2)),
      mul_nonneg (sub_nonneg.2 x2u) (by linarith : 0 ≤ δ / 2 + (v1 ^ 2 - 1 / 2)),
      mul_nonneg (sub_nonneg.2 x1u) (by linarith : 0 ≤ δ / 2 + (v3 ^ 2 - 1 / 2)),
      mul_nonneg (sub_nonneg.2 x3u) (by linarith : 0 ≤ δ / 2 + (v1 ^ 2 - 1 / 2)),
      mul_nonneg (sub_nonneg.2 x2u) (by linarith : 0 ≤ δ / 2 + (v3 ^ 2 - 1 / 2)),
      mul_nonneg (sub_nonneg.2 x3u) (by linarith : 0 ≤ δ / 2 + (v2 ^ 2 - 1 / 2))]
  -- a ≥ 1 + 3 s²
  have ha : 1 + 3 * s ^ 2 ≤ 1 + v1 * v2 + v1 * v3 + v2 * v3 := by
    nlinarith [mul_le_mul h1 h2 hs0 (hv0 v1 h1), mul_le_mul h1 h3 hs0 (hv0 v1 h1),
      mul_le_mul h2 h3 hs0 (hv0 v2 h2)]
  have hs2 : s ^ 2 = (1 - δ) / 2 := by rw [hδ]; linarith
  have hlam : 0 ≤ (1 + 3 * δ) ^ 2 := sq_nonneg _
  have hc : 0 ≤ 2 * (1 + 3 * δ) + 8 := by linarith
  have e1 := mul_le_mul_of_nonneg_left ha hlam
  have e2 := mul_le_mul_of_nonneg_left hK hc
  have key : 0 ≤ 6 * δ * (1 - δ) * (3 * δ + 2) := by
    have : 0 ≤ 1 - δ := by linarith
    positivity
  rw [hs2] at e1
  nlinarith [key]

end allfour


/-! ## The gate-level all-aligned and lower-triple exclusions -/

section allfourGate

namespace Gate

theorem st1 (g : Gate) : g.s1 ^ 2 + g.t1 ^ 2 = 1 := by
  unfold s1 t1; linear_combination (g.C1 ^ 2 + g.S1 ^ 2 + 1) * g.h1
theorem st2 (g : Gate) : g.s2 ^ 2 + g.t2 ^ 2 = 1 := by
  unfold s2 t2; linear_combination (g.C2 ^ 2 + g.S2 ^ 2 + 1) * g.h2
theorem st3 (g : Gate) : g.s3 ^ 2 + g.t3 ^ 2 = 1 := by
  unfold s3 t3; linear_combination (g.C3 ^ 2 + g.S3 ^ 2 + 1) * g.h3

/-- (AFE-data), `a`: `|Σ u_j|² = 1 + Σ_{i<j} s_i s_j`. -/
theorem norm_sq_sum_u (g : Gate) :
    ‖∑ a, g.u a‖ ^ 2 = 1 + g.s1 * g.s2 + g.s1 * g.s3 + g.s2 * g.s3 := by
  have := norm_sq_comb g (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at this
  rw [this, Qf_eq]
  simp only [one_pow, one_mul, mul_one]
  linarith [sum_p g]

/-- (AFE-data), `a`, crossed cut: `|Σ (Tu)_j|² = 4 p_0 = 1 + Σ_{i<j} t_i t_j`. -/
theorem norm_sq_sum_uT (g : Gate) :
    ‖∑ a, g.uT a‖ ^ 2 = 1 + g.t1 * g.t2 + g.t1 * g.t3 + g.t2 * g.t3 := by
  have := norm_sq_comb_cross g (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at this
  rw [this, Qf_eq]
  simp only [Tw]
  norm_num
  unfold p0
  ring

/-- `Σ u_j² = Π t_j + i Π s_j`. -/
theorem sum_u_sq (g : Gate) : ∑ a, g.u a ^ 2 = ⟨g.t1 * g.t2 * g.t3, g.s1 * g.s2 * g.s3⟩ := by
  apply Complex.ext
  · simp only [Fin.sum_univ_four, Gate.u, uR, uI, t1, t2, t3, Complex.add_re, Complex.mul_re, sq]
    simp
    ring
  · simp only [Fin.sum_univ_four, Gate.u, uR, uI, s1, s2, s3, Complex.add_im, Complex.mul_im, sq]
    simp
    ring

theorem sum_uT_sq (g : Gate) : ∑ a, g.uT a ^ 2 = ∑ a, g.u a ^ 2 := by
  simp only [Fin.sum_univ_four, uT]
  simp
  ring

/-- (AFE-data), `K`: `|Σ μ_j²|² = Π t_j² + Π s_j²`. -/
theorem norm_sq_sum_u_sq (g : Gate) :
    ‖∑ a, g.u a ^ 2‖ ^ 2 = (g.t1 * g.t2 * g.t3) ^ 2 + (g.s1 * g.s2 * g.s3) ^ 2 := by
  rw [sum_u_sq, Complex.sq_norm, Complex.normSq_apply]
  simp only; ring

end Gate

theorem candJ_neg (L Q : ℂ) (W : ℝ) : candJ (-L) Q W = - candJ L Q W := by
  unfold candJ; simp; ring

theorem candH_neg (L Q : ℂ) (W : ℝ) : candH (-L) Q W = candH L Q W := by
  unfold candH; simp

theorem Admissible.neg {r m : ℝ} {L Q : ℂ} {W : ℝ} (h : Admissible r m L Q W) :
    Admissible r m (-L) Q W where
  J_ne := by rw [candJ_neg]; exact neg_ne_zero.2 h.J_ne
  K_pos := h.K_pos
  H_pos := by rw [candH_neg]; exact h.H_pos
  h_pos := by rw [candH_neg]; exact h.h_pos
  norm_ineq := by rw [candJ_neg, candH_neg, norm_neg]; exact h.norm_ineq

theorem cand_neg_val (r : ℝ) (L Q : ℂ) (W : ℝ) :
    candVal r (candK Q W) (candH (-L) Q W) = candVal r (candK Q W) (candH L Q W) := by
  rw [candH_neg]

/-- Signs: `ε L` with `ε = ±1` has the same candidate data. -/
theorem cand_eps {r m : ℝ} {L Q : ℂ} {W ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hA : Admissible r m ((ε : ℂ) * L) Q W) :
    Admissible r m L Q W ∧ candVal r (candK Q W) (candH ((ε : ℂ) * L) Q W)
      = candVal r (candK Q W) (candH L Q W) := by
  rcases hε with rfl | rfl
  · simpa using hA
  · have : ((-1 : ℝ) : ℂ) * L = -L := by simp
    rw [this] at hA ⊢
    exact ⟨by simpa using hA.neg, cand_neg_val r L Q W⟩

/-- **`lem:t34l-allfour-exclusion`, `r = 4`, direct cut.**  The all-aligned four-coordinate candidate
(`W = 0`, `L = ±Σ u_j`, `Q = Σ u_j²`) has value `≤ κ = (5+3δ)/8`. -/
theorem afe_four_gate_direct {g : Gate} (hg : g.Half) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hA : Admissible 4 1 ((ε : ℂ) * ∑ a, g.u a) (∑ a, g.u a ^ 2) 0) :
    candVal 4 (candK (∑ a, g.u a ^ 2) 0) (candH ((ε : ℂ) * ∑ a, g.u a) (∑ a, g.u a ^ 2) 0)
      ≤ (5 + 3 * g.delta) / 8 := by
  obtain ⟨hA', hv⟩ := cand_eps hε hA
  rw [hv]
  have hd := hg.delta_nonneg
  have hAFE : (2 * (1 + 3 * g.delta) + 8) * ‖∑ a, g.u a ^ 2‖ ^ 2
      ≤ (1 + 3 * g.delta) ^ 2 * ‖∑ a, g.u a‖ ^ 2 := by
    rw [Gate.norm_sq_sum_u_sq, Gate.norm_sq_sum_u]
    have e1 : g.t1 ^ 2 = 1 - g.s1 ^ 2 := by linarith [g.st1]
    have e2 : g.t2 ^ 2 = 1 - g.s2 ^ 2 := by linarith [g.st2]
    have e3 : g.t3 ^ 2 = 1 - g.s3 ^ 2 := by linarith [g.st3]
    have := afe_four_ineq (s := g.s3) (t := g.t3) (v1 := g.s1) (v2 := g.s2) (v3 := g.s3) hg.o7
      (by linarith [g.st3]) (le_trans hg.o1 hg.o2) (hg.o3) hg.o1 (le_trans hg.o2 hg.o3) le_rfl
      (le_trans hg.o1 (le_trans hg.o2 hg.o3))
    unfold Gate.delta
    have e4 : (g.t1 * g.t2 * g.t3) ^ 2 + (g.s1 * g.s2 * g.s3) ^ 2
        = g.s1 ^ 2 * g.s2 ^ 2 * g.s3 ^ 2 + (1 - g.s1 ^ 2) * (1 - g.s2 ^ 2) * (1 - g.s3 ^ 2) := by
      rw [mul_pow, mul_pow, e1, e2, e3]; ring
    rw [e4]
    linarith
  exact afe_four_candidate hA' hd hAFE

/-- The same on the crossed cut (`L = ±Σ (Tu)_j`, `Q = Σ (Tu)_j²`). -/
theorem afe_four_gate_cross {g : Gate} (hg : g.Half) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hA : Admissible 4 1 ((ε : ℂ) * ∑ a, g.uT a) (∑ a, g.uT a ^ 2) 0) :
    candVal 4 (candK (∑ a, g.uT a ^ 2) 0) (candH ((ε : ℂ) * ∑ a, g.uT a) (∑ a, g.uT a ^ 2) 0)
      ≤ (5 + 3 * g.delta) / 8 := by
  obtain ⟨hA', hv⟩ := cand_eps hε hA
  rw [hv]
  have hd := hg.delta_nonneg
  have hAFE : (2 * (1 + 3 * g.delta) + 8) * ‖∑ a, g.uT a ^ 2‖ ^ 2
      ≤ (1 + 3 * g.delta) ^ 2 * ‖∑ a, g.uT a‖ ^ 2 := by
    rw [Gate.sum_uT_sq, Gate.norm_sq_sum_u_sq, Gate.norm_sq_sum_uT]
    have e1 : g.s1 ^ 2 = 1 - g.t1 ^ 2 := by linarith [g.st1]
    have e2 : g.s2 ^ 2 = 1 - g.t2 ^ 2 := by linarith [g.st2]
    have e3 : g.s3 ^ 2 = 1 - g.t3 ^ 2 := by linarith [g.st3]
    have := afe_four_ineq (s := g.s3) (t := g.t3) (v1 := g.t1) (v2 := g.t2) (v3 := g.t3) hg.o7
      (by linarith [g.st3]) hg.o4 (le_trans hg.o5 hg.o6) (le_trans hg.o4 hg.o5) hg.o6
      (le_trans hg.o4 (le_trans hg.o5 hg.o6)) le_rfl
    unfold Gate.delta
    have e4 : (g.t1 * g.t2 * g.t3) ^ 2 + (g.s1 * g.s2 * g.s3) ^ 2
        = g.t1 ^ 2 * g.t2 ^ 2 * g.t3 ^ 2 + (1 - g.t1 ^ 2) * (1 - g.t2 ^ 2) * (1 - g.t3 ^ 2) := by
      have : (g.s1 * g.s2 * g.s3) ^ 2 = (1 - g.t1 ^ 2) * (1 - g.t2 ^ 2) * (1 - g.t3 ^ 2) := by
        rw [← e1, ← e2, ← e3]; ring
      rw [this]; ring
    rw [e4]
    linarith
  exact afe_four_candidate hA' hd hAFE

end allfourGate


section tripleGate

theorem norm_sq_three (a b c : ℂ) : ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h := norm_add₃_le (a := a) (b := b) (c := c)
  have h0 : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c]

/-- **`lem:t34l-allfour-exclusion`, lower-only triple `I = {1,2,3}`, direct cut**
(`L = ±(u₁+u₂+u₃)`, `Q = u₁²+u₂²+u₃²`, `W = |u₀|²`): value `≤ κ = (5+3δ)/8`. -/
theorem afe_triple_gate_direct {g : Gate} (hg : g.Half) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hA : Admissible 3 1 ((ε : ℂ) * (g.u 1 + g.u 2 + g.u 3)) (g.u 1 ^ 2 + g.u 2 ^ 2 + g.u 3 ^ 2)
      (‖g.u 0‖ ^ 2)) :
    candVal 3 (candK (g.u 1 ^ 2 + g.u 2 ^ 2 + g.u 3 ^ 2) (‖g.u 0‖ ^ 2))
      (candH ((ε : ℂ) * (g.u 1 + g.u 2 + g.u 3)) (g.u 1 ^ 2 + g.u 2 ^ 2 + g.u 3 ^ 2) (‖g.u 0‖ ^ 2))
      ≤ (5 + 3 * g.delta) / 8 := by
  obtain ⟨hA', hv⟩ := cand_eps hε hA
  rw [hv]
  have hd := hg.delta_nonneg
  have hB : ‖g.u 1 + g.u 2 + g.u 3‖ ^ 2 ≤ 9 * (1 + g.delta) / 8 := by
    have h1 := norm_sq_three (g.u 1) (g.u 2) (g.u 3)
    have h2 := Gate.sum_norm_sq_u g
    simp only [Fin.sum_univ_four] at h2
    have h0 : ‖g.u 0‖ ^ 2 = g.p0 := by rw [Gate.norm_sq_u]; rfl
    have hp : (1 + 3 * g.s3 ^ 2) / 4 ≤ g.p0 := by
      unfold Gate.p0
      have a1 : g.s3 ≤ g.t1 := hg.o4
      have a2 : g.s3 ≤ g.t2 := le_trans hg.o4 hg.o5
      have a3 : g.s3 ≤ g.t3 := le_trans hg.o4 (le_trans hg.o5 hg.o6)
      nlinarith [mul_le_mul a1 a2 hg.o7 (le_trans hg.o7 a1), mul_le_mul a1 a3 hg.o7 (le_trans hg.o7 a1),
        mul_le_mul a2 a3 hg.o7 (le_trans hg.o7 a2)]
    unfold Gate.delta
    nlinarith [g.st3]
  exact candidate_le (by norm_num) (by norm_num) hA' (κ := (5 + 3 * g.delta) / 8) (by linarith) hB
    (afe_triple hd)

/-- The same on the crossed cut: `L = ±(T u)₁+(T u)₂+(T u)₃`, `W = |(Tu)₀|²`. -/
theorem afe_triple_gate_cross {g : Gate} (hg : g.Half) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hA : Admissible 3 1 ((ε : ℂ) * (g.uT 1 + g.uT 2 + g.uT 3))
      (g.uT 1 ^ 2 + g.uT 2 ^ 2 + g.uT 3 ^ 2) (‖g.uT 0‖ ^ 2)) :
    candVal 3 (candK (g.uT 1 ^ 2 + g.uT 2 ^ 2 + g.uT 3 ^ 2) (‖g.uT 0‖ ^ 2))
      (candH ((ε : ℂ) * (g.uT 1 + g.uT 2 + g.uT 3)) (g.uT 1 ^ 2 + g.uT 2 ^ 2 + g.uT 3 ^ 2)
        (‖g.uT 0‖ ^ 2)) ≤ (5 + 3 * g.delta) / 8 := by
  obtain ⟨hA', hv⟩ := cand_eps hε hA
  rw [hv]
  have hd := hg.delta_nonneg
  have hB : ‖g.uT 1 + g.uT 2 + g.uT 3‖ ^ 2 ≤ 9 * (1 + g.delta) / 8 := by
    have h1 := norm_sq_three (g.uT 1) (g.uT 2) (g.uT 3)
    have h2 := Gate.sum_norm_sq_uT g
    simp only [Fin.sum_univ_four] at h2
    have h0 : ‖g.uT 0‖ ^ 2 = ‖∑ a, g.u a‖ ^ 2 / 4 := by
      have : g.uT 0 = (∑ a, g.u a) / 2 := by
        simp only [Gate.uT, Fin.sum_univ_four]; simp
      rw [this, norm_div, div_pow]; norm_num
    rw [Gate.norm_sq_sum_u] at h0
    have hp : (1 + 3 * g.s3 ^ 2) / 4 ≤ ‖g.uT 0‖ ^ 2 := by
      rw [h0]
      have a1 : g.s3 ≤ g.s2 := hg.o1
      have a2 : g.s3 ≤ g.s1 := le_trans hg.o1 hg.o2
      have a3 : g.s3 ≤ g.s3 := le_rfl
      nlinarith [mul_le_mul a2 a1 hg.o7 (le_trans hg.o7 a2), mul_le_mul a2 a3 hg.o7 (le_trans hg.o7 a2),
        mul_le_mul a1 a3 hg.o7 (le_trans hg.o7 a1)]
    unfold Gate.delta
    nlinarith [g.st3]
  exact candidate_le (by norm_num) (by norm_num) hA' (κ := (5 + 3 * g.delta) / 8) (by linarith) hB
    (afe_triple hd)

end tripleGate


/-! ### The complex-orthogonal orbit cap and its invariances (`lem:t34l-orbit-reflections`) -/

section Cap

/-- `R ∈ O(4, ℂ)`: the rows are orthonormal for the *bilinear* form `Σ_k R_{ik} R_{jk}`. -/
def IsOrth (R : Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ i j, ∑ k, R i k * R j k = if i = j then 1 else 0

/-- The entries of `R D Sᵀ` for `D = diag μ`. -/
def entry (R S : Fin 4 → Fin 4 → ℂ) (μ : Fin 4 → ℂ) (i j : Fin 4) : ℂ :=
  ∑ k, R i k * μ k * S j k

/-- `|M₀₀|² / ‖M‖_F²`. -/
def ratio (M : Fin 4 → Fin 4 → ℂ) : ℝ := ‖M 0 0‖ ^ 2 / ∑ i, ∑ j, ‖M i j‖ ^ 2

/-- `ℬ(D)` of `lem:t34k-bell-orbit` (GOC-def) for `D = diag μ`: the supremum of `ratio (R D Sᵀ)`
over `R, S ∈ O(4, ℂ)`. -/
def cap (μ : Fin 4 → ℂ) : ℝ :=
  ⨆ p : {R : Fin 4 → Fin 4 → ℂ // IsOrth R} × {S : Fin 4 → Fin 4 → ℂ // IsOrth S},
    ratio (entry p.1.1 p.2.1 μ)

theorem ratio_nonneg (M : Fin 4 → Fin 4 → ℂ) : 0 ≤ ratio M := by
  unfold ratio
  apply div_nonneg (sq_nonneg _)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem ratio_le_one (M : Fin 4 → Fin 4 → ℂ) : ratio M ≤ 1 := by
  unfold ratio
  have h1 : ‖M 0 0‖ ^ 2 ≤ ∑ j, ‖M 0 j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖M 0 j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ 0)
  have h2 : ∑ j, ‖M 0 j‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ 0)
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖M i j‖))).lt_or_eq with h | h
  · exact (div_le_one h).2 (le_trans h1 h2)
  · rw [← h]; simp

theorem cap_nonneg (μ : Fin 4 → ℂ) : 0 ≤ cap μ :=
  Real.iSup_nonneg (fun _ => ratio_nonneg _)

theorem ratio_le_cap (μ : Fin 4 → ℂ) {R S : Fin 4 → Fin 4 → ℂ} (hR : IsOrth R) (hS : IsOrth S) :
    ratio (entry R S μ) ≤ cap μ :=
  le_ciSup (f := fun p : {R : Fin 4 → Fin 4 → ℂ // IsOrth R} × {S : Fin 4 → Fin 4 → ℂ // IsOrth S} =>
      ratio (entry p.1.1 p.2.1 μ))
    ⟨1, by rintro _ ⟨p, rfl⟩; exact ratio_le_one _⟩ (⟨R, hR⟩, ⟨S, hS⟩)

/-- Comparison principle: if every orbit point of `diag μ'` has the same ratio as an orbit point of
`diag μ`, then `ℬ(diag μ') ≤ ℬ(diag μ)`. -/
theorem cap_le_of {μ μ' : Fin 4 → ℂ}
    (h : ∀ R S, IsOrth R → IsOrth S → ∃ R' S', IsOrth R' ∧ IsOrth S' ∧
      ratio (entry R S μ') = ratio (entry R' S' μ)) : cap μ' ≤ cap μ := by
  apply Real.iSup_le _ (cap_nonneg μ)
  rintro ⟨⟨R, hR⟩, ⟨S, hS⟩⟩
  obtain ⟨R', S', hR', hS', he⟩ := h R S hR hS
  simp only
  rw [he]
  exact ratio_le_cap μ hR' hS'

/-- Phase invariance. -/
theorem cap_smul {ω : ℂ} (hω : ‖ω‖ = 1) (μ : Fin 4 → ℂ) : cap (fun k => ω * μ k) = cap μ := by
  unfold cap
  apply iSup_congr
  intro p
  have he : ∀ i j, entry p.1.1 p.2.1 (fun k => ω * μ k) i j = ω * entry p.1.1 p.2.1 μ i j := by
    intro i j
    simp only [entry, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  unfold ratio
  simp only [he, norm_mul, hω, one_mul]

/-- Complex conjugation of the spectrum. -/
theorem cap_conj_le (μ : Fin 4 → ℂ) : cap (fun k => conj (μ k)) ≤ cap μ := by
  apply cap_le_of
  intro R S hR hS
  refine ⟨fun i k => conj (R i k), fun i k => conj (S i k), ?_, ?_, ?_⟩
  · intro i j
    have := congrArg conj (hR i j)
    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  · intro i j
    have := congrArg conj (hS i j)
    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  · have he : ∀ i j, entry (fun i k => conj (R i k)) (fun i k => conj (S i k)) μ i j
        = conj (entry R S (fun k => conj (μ k)) i j) := by
      intro i j
      simp only [entry, map_sum, map_mul, Complex.conj_conj]
    unfold ratio
    simp only [he, RCLike.norm_conj]

theorem cap_conj (μ : Fin 4 → ℂ) : cap (fun k => conj (μ k)) = cap μ := by
  refine le_antisymm (cap_conj_le μ) ?_
  have := cap_conj_le (fun k => conj (μ k))
  simpa [Complex.conj_conj] using this

/-- Signs: `μ ↦ (ε_k μ_k)` with `ε_k² = 1`. -/
theorem cap_sign_le {ε : Fin 4 → ℂ} (hε : ∀ k, ε k * ε k = 1) (μ : Fin 4 → ℂ) :
    cap (fun k => ε k * μ k) ≤ cap μ := by
  apply cap_le_of
  intro R S hR hS
  refine ⟨fun i k => R i k * ε k, S, ?_, hS, ?_⟩
  · intro i j
    rw [← hR i j]
    exact Finset.sum_congr rfl (fun k _ => by
      have := hε k
      linear_combination (R i k * R j k) * this)
  · congr 1
    funext i j
    unfold entry
    exact Finset.sum_congr rfl (fun k _ => by ring)

theorem cap_sign {ε : Fin 4 → ℂ} (hε : ∀ k, ε k * ε k = 1) (μ : Fin 4 → ℂ) :
    cap (fun k => ε k * μ k) = cap μ := by
  refine le_antisymm (cap_sign_le hε μ) ?_
  have := cap_sign_le hε (fun k => ε k * μ k)
  have e : (fun k => ε k * (ε k * μ k)) = μ := by
    funext k; rw [← mul_assoc, hε k, one_mul]
  rwa [e] at this

/-- Permutations of the spectrum. -/
theorem cap_perm_le (σ : Equiv.Perm (Fin 4)) (μ : Fin 4 → ℂ) : cap (μ ∘ σ) ≤ cap μ := by
  apply cap_le_of
  intro R S hR hS
  refine ⟨fun i k => R i (σ.symm k), fun i k => S i (σ.symm k), ?_, ?_, ?_⟩
  · intro i j
    rw [← hR i j]
    exact Equiv.sum_comp σ.symm (fun k => R i k * R j k)
  · intro i j
    rw [← hS i j]
    exact Equiv.sum_comp σ.symm (fun k => S i k * S j k)
  · congr 1
    funext i j
    unfold entry
    refine Eq.trans ?_ (Equiv.sum_comp σ (fun l => R i (σ.symm l) * μ l * S j (σ.symm l)))
    exact Finset.sum_congr rfl (fun k _ => by simp)

theorem cap_perm (σ : Equiv.Perm (Fin 4)) (μ : Fin 4 → ℂ) : cap (μ ∘ σ) = cap μ := by
  refine le_antisymm (cap_perm_le σ μ) ?_
  have := cap_perm_le σ.symm (μ ∘ σ)
  have e : (μ ∘ σ) ∘ σ.symm = μ := by
    funext k; simp
  rwa [e] at this

end Cap


section Reflect

/-- `√2/2`. -/
def r2 : ℝ := Real.sqrt 2 / 2

theorem r2_sq : r2 ^ 2 = 1 / 2 := by
  unfold r2; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The phase `e^{iπ/4}`. -/
def omega : ℂ := ⟨r2, r2⟩

theorem norm_omega : ‖omega‖ = 1 := by
  have h : ‖omega‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [omega]
    nlinarith [r2_sq]
  have h0 := norm_nonneg omega
  nlinarith

/-- The coordinate swap `u₁ ↔ u₃` (`P₁₃`). -/
def σ13 : Fin 4 → Fin 4 := ![0, 3, 2, 1]

theorem σ13_perm : ∃ σ : Equiv.Perm (Fin 4), ∀ a, σ a = σ13 a :=
  ⟨Equiv.swap 1 3, by decide⟩

/-- The sign matrix `E = diag(1,-1,-1,1)`. -/
def Evec : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- The reversal `a ↦ 3 - a` of the four coordinates. -/
def rev4 : Fin 4 → Fin 4 := ![3, 2, 1, 0]

namespace Gate

/-- The Cartan sign reflection `c₃ ↦ -c₃`. -/
def flip3 (g : Gate) : Gate :=
  { g with S3 := -g.S3, h3 := by rw [neg_sq]; exact g.h3 }

/-- The complementary Weyl reflection `(c₁,c₂,c₃) ↦ (π/4-c₃, π/4-c₂, π/4-c₁)`. -/
def refl (g : Gate) : Gate where
  C1 := r2 * (g.C3 + g.S3)
  S1 := r2 * (g.C3 - g.S3)
  C2 := r2 * (g.C2 + g.S2)
  S2 := r2 * (g.C2 - g.S2)
  C3 := r2 * (g.C1 + g.S1)
  S3 := r2 * (g.C1 - g.S1)
  h1 := by nlinarith [r2_sq, g.h3]
  h2 := by nlinarith [r2_sq, g.h2]
  h3 := by nlinarith [r2_sq, g.h1]


/-- Real part of `T u`. -/
def uTR (g : Gate) : Fin 4 → ℝ :=
  ![(g.uR 0 + g.uR 1 + g.uR 2 + g.uR 3) / 2, (g.uR 0 + g.uR 1 - g.uR 2 - g.uR 3) / 2,
    (g.uR 0 - g.uR 1 + g.uR 2 - g.uR 3) / 2, (g.uR 0 - g.uR 1 - g.uR 2 + g.uR 3) / 2]
/-- Imaginary part of `T u`. -/
def uTI (g : Gate) : Fin 4 → ℝ :=
  ![(g.uI 0 + g.uI 1 + g.uI 2 + g.uI 3) / 2, (g.uI 0 + g.uI 1 - g.uI 2 - g.uI 3) / 2,
    (g.uI 0 - g.uI 1 + g.uI 2 - g.uI 3) / 2, (g.uI 0 - g.uI 1 - g.uI 2 + g.uI 3) / 2]

theorem uT_eq (g : Gate) (a : Fin 4) : g.uT a = ⟨g.uTR a, g.uTI a⟩ := by
  fin_cases a <;> apply Complex.ext <;> simp [uT, uTR, uTI, Gate.u]

/-- (GOR) `u(c₁,c₂,-c₃) = E ū(c₁,c₂,c₃)`. -/
theorem flip3_u (g : Gate) (a : Fin 4) : g.flip3.u a = Evec a * conj (g.u a) := by
  fin_cases a <;> apply Complex.ext <;>
    simp [flip3, Gate.u, Gate.uR, Gate.uI, Evec]

/-- The crossed coefficients of the flipped gate are the reversed conjugates. -/
theorem flip3_uT (g : Gate) (a : Fin 4) : g.flip3.uT a = conj (g.uT (rev4 a)) := by
  fin_cases a <;> apply Complex.ext <;>
    simp [flip3, uT_eq, uTR, uTI, Gate.uR, Gate.uI, rev4] <;> ring

/-- (GOR) `u(c*) = e^{iπ/4} P₁₃ T ū(c)`. -/
theorem refl_u (g : Gate) (a : Fin 4) : g.refl.u a = omega * conj (g.uT (σ13 a)) := by
  fin_cases a
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 + g.C1*g.C2*g.S3 + g.C1*g.C3*g.S2 + g.C1*g.S2*g.S3 + g.C2*g.C3*g.S1 + g.C2*g.S1*g.S3 + g.C3*g.S1*g.S2 + g.S1*g.S2*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 - g.C1*g.C2*g.S3 - g.C1*g.C3*g.S2 + g.C1*g.S2*g.S3 - g.C2*g.C3*g.S1 + g.C2*g.S1*g.S3 + g.C3*g.S1*g.S2 - g.S1*g.S2*g.S3)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 + g.C1*g.C2*g.S3 - g.C1*g.C3*g.S2 - g.C1*g.S2*g.S3 - g.C2*g.C3*g.S1 - g.C2*g.S1*g.S3 + g.C3*g.S1*g.S2 + g.S1*g.S2*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 - g.C1*g.C2*g.S3 + g.C1*g.C3*g.S2 - g.C1*g.S2*g.S3 + g.C2*g.C3*g.S1 - g.C2*g.S1*g.S3 + g.C3*g.S1*g.S2 - g.S1*g.S2*g.S3)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 - g.C1*g.C2*g.S3 + g.C1*g.C3*g.S2 - g.C1*g.S2*g.S3 - g.C2*g.C3*g.S1 + g.C2*g.S1*g.S3 - g.C3*g.S1*g.S2 + g.S1*g.S2*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 + g.C1*g.C2*g.S3 - g.C1*g.C3*g.S2 - g.C1*g.S2*g.S3 + g.C2*g.C3*g.S1 + g.C2*g.S1*g.S3 - g.C3*g.S1*g.S2 - g.S1*g.S2*g.S3)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 - g.C1*g.C2*g.S3 - g.C1*g.C3*g.S2 + g.C1*g.S2*g.S3 + g.C2*g.C3*g.S1 - g.C2*g.S1*g.S3 - g.C3*g.S1*g.S2 + g.S1*g.S2*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(g.C1*g.C2*g.C3 + g.C1*g.C2*g.S3 + g.C1*g.C3*g.S2 + g.C1*g.S2*g.S3 - g.C2*g.C3*g.S1 - g.C2*g.S1*g.S3 - g.C3*g.S1*g.S2 - g.S1*g.S2*g.S3)) * r2_sq

/-- (GOR) the crossed cut of the reflected gate is `e^{iπ/4} P₁₃ ū`. -/
theorem refl_uT (g : Gate) (a : Fin 4) : g.refl.uT a = omega * conj (g.u (σ13 a)) := by
  fin_cases a
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.C2*g.C3 + 2*g.S1*g.S2*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.C2*g.C3 - 2*g.S1*g.S2*g.S3)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.C2*g.S3 + 2*g.C3*g.S1*g.S2)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(-2*g.C1*g.C2*g.S3 + 2*g.C3*g.S1*g.S2)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.C3*g.S2 + 2*g.C2*g.S1*g.S3)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(-2*g.C1*g.C3*g.S2 + 2*g.C2*g.S1*g.S3)) * r2_sq
  · apply Complex.ext
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.S2*g.S3 + 2*g.C2*g.C3*g.S1)) * r2_sq
    · simp [refl, uT_eq, uTR, uTI, Gate.u, Gate.uR, Gate.uI, omega, σ13]
      linear_combination (r2*(2*g.C1*g.S2*g.S3 - 2*g.C2*g.C3*g.S1)) * r2_sq

end Gate

end Reflect


section Reduction

theorem Gate.ext_of {g g' : Gate} (h1 : g.C1 = g'.C1) (h2 : g.S1 = g'.S1) (h3 : g.C2 = g'.C2)
    (h4 : g.S2 = g'.S2) (h5 : g.C3 = g'.C3) (h6 : g.S3 = g'.S3) : g = g' := by
  cases g; cases g'; simp_all

/-- The direct-cut cap `ℬ(D_{U_c})`, with `D_{U_c} = diag(u)`. -/
def capD (g : Gate) : ℝ := cap g.u
/-- The crossed-cut cap `ℬ(D_{U_c SWAP})`, with `D = diag(Tu)` up to a phase. -/
def capX (g : Gate) : ℝ := cap g.uT

theorem cap_comp_perm (f : Fin 4 → Fin 4) (σ : Equiv.Perm (Fin 4)) (h : ∀ a, σ a = f a)
    (μ : Fin 4 → ℂ) : cap (fun k => μ (f k)) = cap μ := by
  have : (fun k => μ (f k)) = μ ∘ σ := funext (fun k => by simp [h])
  rw [this]; exact cap_perm σ μ

theorem Evec_sq : ∀ k, Evec k * Evec k = 1 := by
  intro k; fin_cases k <;> simp [Evec]

theorem capD_flip3 (g : Gate) : capD g.flip3 = capD g := by
  unfold capD
  have : g.flip3.u = fun k => Evec k * conj (g.u k) := funext (Gate.flip3_u g)
  rw [this]
  exact (cap_sign Evec_sq (fun k => conj (g.u k))).trans (cap_conj _)

theorem capX_flip3 (g : Gate) : capX g.flip3 = capX g := by
  unfold capX
  have : g.flip3.uT = fun k => conj (g.uT (rev4 k)) := funext (Gate.flip3_uT g)
  rw [this]
  refine (cap_conj (fun k => g.uT (rev4 k))).trans ?_
  exact cap_comp_perm rev4 Fin.revPerm (by decide) g.uT

theorem capD_refl (g : Gate) : capD g.refl = capX g := by
  unfold capD capX
  have : g.refl.u = fun k => omega * conj (g.uT (σ13 k)) := funext (Gate.refl_u g)
  rw [this]
  obtain ⟨σ, hσ⟩ := σ13_perm
  refine (cap_smul norm_omega (fun k => conj (g.uT (σ13 k)))).trans ?_
  refine (cap_conj (fun k => g.uT (σ13 k))).trans ?_
  exact cap_comp_perm σ13 σ hσ g.uT

theorem capX_refl (g : Gate) : capX g.refl = capD g := by
  unfold capD capX
  have : g.refl.uT = fun k => omega * conj (g.u (σ13 k)) := funext (Gate.refl_uT g)
  rw [this]
  obtain ⟨σ, hσ⟩ := σ13_perm
  refine (cap_smul norm_omega (fun k => conj (g.u (σ13 k)))).trans ?_
  refine (cap_conj (fun k => g.u (σ13 k))).trans ?_
  exact cap_comp_perm σ13 σ hσ g.u

/-! Angle form -/

/-- The gate with Cartan angles `c`. -/
def Gate.ofAngles (c : Fin 3 → ℝ) : Gate where
  C1 := Real.cos (c 0)
  S1 := Real.sin (c 0)
  C2 := Real.cos (c 1)
  S2 := Real.sin (c 1)
  C3 := Real.cos (c 2)
  S3 := Real.sin (c 2)
  h1 := Real.cos_sq_add_sin_sq _
  h2 := Real.cos_sq_add_sin_sq _
  h3 := Real.cos_sq_add_sin_sq _

theorem ofAngles_t (c : Fin 3 → ℝ) :
    (Gate.ofAngles c).t1 = Real.cos (2 * c 0) ∧ (Gate.ofAngles c).t2 = Real.cos (2 * c 1) ∧
    (Gate.ofAngles c).t3 = Real.cos (2 * c 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Gate.t1, Gate.t2, Gate.t3, Gate.ofAngles, Real.cos_two_mul', Real.cos_sq']

theorem ofAngles_s (c : Fin 3 → ℝ) :
    (Gate.ofAngles c).s1 = Real.sin (2 * c 0) ∧ (Gate.ofAngles c).s2 = Real.sin (2 * c 1) ∧
    (Gate.ofAngles c).s3 = Real.sin (2 * c 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Gate.s1, Gate.s2, Gate.s3, Gate.ofAngles, Real.sin_two_mul]

/-- `δ = t₃² - s₃² = cos 4c₃` for the gate of angles `c`. -/
theorem delta_ofAngles (c : Fin 3 → ℝ) : (Gate.ofAngles c).delta = Real.cos (4 * c 2) := by
  have h4 : 4 * c 2 = 2 * (2 * c 2) := by ring
  rw [h4, Real.cos_two_mul, Gate.delta, (ofAngles_t c).2.2, (ofAngles_s c).2.2]
  nlinarith [Real.sin_sq_add_cos_sq (2 * c 2)]

/-- The Cartan sign reflection in angle form. -/
theorem flip3_ofAngles (c : Fin 3 → ℝ) :
    (Gate.ofAngles c).flip3 = Gate.ofAngles ![c 0, c 1, - c 2] := by
  apply Gate.ext_of <;> simp [Gate.flip3, Gate.ofAngles]

/-- The complementary Weyl reflection in angle form. -/
theorem cos_pi4_sub (x : ℝ) : Real.cos (Real.pi / 4 - x) = r2 * (Real.cos x + Real.sin x) := by
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  unfold r2; ring

theorem sin_pi4_sub (x : ℝ) : Real.sin (Real.pi / 4 - x) = r2 * (Real.cos x - Real.sin x) := by
  rw [Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  unfold r2; ring

theorem refl_ofAngles (c : Fin 3 → ℝ) :
    (Gate.ofAngles c).refl = Gate.ofAngles ![Real.pi / 4 - c 2, Real.pi / 4 - c 1, Real.pi / 4 - c 0] := by
  apply Gate.ext_of <;>
    simp only [Gate.refl, Gate.ofAngles, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, cos_pi4_sub, sin_pi4_sub]

/-- The half-chamber (GOR-half). -/
structure Chamber (c : Fin 3 → ℝ) : Prop where
  h0 : 0 ≤ c 2
  h1 : c 2 ≤ c 1
  h2 : c 1 ≤ c 0
  h3 : c 0 + c 2 ≤ Real.pi / 4

theorem Chamber.half {c : Fin 3 → ℝ} (hc : Chamber c) : (Gate.ofAngles c).Half := by
  obtain ⟨ht1, ht2, ht3⟩ := ofAngles_t c
  obtain ⟨hs1, hs2, hs3⟩ := ofAngles_s c
  have hpi := Real.pi_pos
  have c1 : c 1 ≤ Real.pi / 4 := by linarith [hc.h0, hc.h1, hc.h2, hc.h3]
  have c0 : c 0 ≤ Real.pi / 4 := by linarith [hc.h0, hc.h1, hc.h2, hc.h3]
  have cosm : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ Real.pi → Real.cos y ≤ Real.cos x :=
    fun x y hx hxy hy => Real.cos_le_cos_of_nonneg_of_le_pi hx hy hxy
  have sinm : ∀ x y : ℝ, -(Real.pi / 2) ≤ x → x ≤ y → y ≤ Real.pi / 2 → Real.sin x ≤ Real.sin y :=
    fun x y hx hxy hy => Real.sin_le_sin_of_le_of_le_pi_div_two hx hy hxy
  have cos_eq : ∀ x : ℝ, Real.cos x = Real.sin (Real.pi / 2 - x) := fun x => (Real.sin_pi_div_two_sub x).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs3, hs2]; exact sinm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [hs2, hs1]; exact sinm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [hs1, ht3, cos_eq]; exact sinm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [hs3, ht1, cos_eq]; exact sinm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [ht1, ht2]; exact cosm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [ht2, ht3]; exact cosm _ _ (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])
  · rw [hs3]; exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hc.h0, hc.h1, hc.h2, hc.h3]) (by linarith [hc.h0, hc.h1, hc.h2, hc.h3])

/-- In the half-chamber `δ = max_j |cos 4c_j| = cos 4c₃`. -/
theorem δg_chamber {c : Fin 3 → ℝ} (hc : Chamber c) : δg c = Real.cos (4 * c 2) := by
  have hpi := Real.pi_pos
  have hc3 : 0 ≤ Real.cos (4 * c 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hc.h0], by linarith [hc.h0, hc.h1, hc.h2, hc.h3]⟩
  have key : ∀ x : ℝ, c 2 ≤ x → x ≤ Real.pi / 4 - c 2 → |Real.cos (4 * x)| ≤ Real.cos (4 * c 2) := by
    intro x h1 h2
    rw [abs_le]
    constructor
    · have : Real.cos (Real.pi - 4 * c 2) ≤ Real.cos (4 * x) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hc.h0]) (by linarith [hc.h0]) (by linarith)
      rw [Real.cos_pi_sub] at this; linarith
    · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hc.h0]) (by linarith [hc.h0]) (by linarith)
  have e3 : |Real.cos (4 * c 2)| = Real.cos (4 * c 2) := abs_of_nonneg hc3
  have k0 := key (c 0) (by linarith [hc.h1, hc.h2]) (by linarith [hc.h3])
  have k1 := key (c 1) hc.h1 (by linarith [hc.h2, hc.h3])
  unfold δg
  rw [e3]
  exact max_eq_right (max_le k0 k1)

/-- `δ` is preserved by `c₃ ↦ -c₃`. -/
theorem δg_flip3 (c : Fin 3 → ℝ) : δg ![c 0, c 1, - c 2] = δg c := by
  simp [δg, mul_neg, Real.cos_neg]

/-- `δ` is preserved by the complementary Weyl reflection. -/
theorem δg_refl (c : Fin 3 → ℝ) : δg ![Real.pi / 4 - c 2, Real.pi / 4 - c 1, Real.pi / 4 - c 0] = δg c := by
  have h : ∀ x : ℝ, |Real.cos (4 * (Real.pi / 4 - x))| = |Real.cos (4 * x)| := by
    intro x
    have : 4 * (Real.pi / 4 - x) = Real.pi - 4 * x := by ring
    rw [this, Real.cos_pi_sub, abs_neg]
  simp only [δg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, h]
  generalize |Real.cos (4 * c 0)| = a
  generalize |Real.cos (4 * c 1)| = b
  generalize |Real.cos (4 * c 2)| = d
  simp only [max_def]
  split_ifs <;> linarith

/-- In the half-chamber `F_K = (1+δ)/2 = cos² 2c₃` (`FKmag_gate` of `GateOverlap`). -/
theorem FK_chamber {c : Fin 3 → ℝ} (hc : Chamber c) :
    FKmag (dgate c) = Real.cos (2 * c 2) ^ 2 := by
  rw [FKmag_gate]
  have := δg_chamber hc
  unfold δg at this
  rw [this, show 4 * c 2 = 2 * (2 * c 2) by ring, Real.cos_two_mul]
  ring

/-- **`lem:t34l-orbit-reflections`** (reduction part).  For Cartan coordinates in the Weyl chamber
`|c₃| ≤ c₂ ≤ c₁ ≤ π/4`, the sign reflection `c₃ ↦ -c₃` and the complementary reflection (GOR) give
coordinates `c'` in the half-chamber (GOR-half) with the same `δ` and with the pair
`{ℬ(D_{U_c}), ℬ(D_{U_c SWAP})}` of orbit caps unchanged as an unordered pair. -/
theorem reflections_reduce_to_half_chamber (c : Fin 3 → ℝ)
    (hc : |c 2| ≤ c 1 ∧ c 1 ≤ c 0 ∧ c 0 ≤ Real.pi / 4) :
    ∃ c' : Fin 3 → ℝ, Chamber c' ∧ δg c' = δg c ∧
      ((capD (Gate.ofAngles c') = capD (Gate.ofAngles c) ∧
          capX (Gate.ofAngles c') = capX (Gate.ofAngles c)) ∨
        (capD (Gate.ofAngles c') = capX (Gate.ofAngles c) ∧
          capX (Gate.ofAngles c') = capD (Gate.ofAngles c))) := by
  obtain ⟨h1, h2, h3⟩ := hc
  -- step 1: make the third coordinate nonnegative
  have step1 : ∃ c1 : Fin 3 → ℝ, 0 ≤ c1 2 ∧ c1 2 ≤ c1 1 ∧ c1 1 ≤ c1 0 ∧ c1 0 ≤ Real.pi / 4 ∧
      δg c1 = δg c ∧ capD (Gate.ofAngles c1) = capD (Gate.ofAngles c) ∧
      capX (Gate.ofAngles c1) = capX (Gate.ofAngles c) := by
    rcases le_or_gt 0 (c 2) with h | h
    · exact ⟨c, h, by rwa [abs_of_nonneg h] at h1, h2, h3, rfl, rfl, rfl⟩
    · refine ⟨![c 0, c 1, - c 2], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp; linarith
      · simp; rw [abs_of_neg h] at h1; exact h1
      · simpa using h2
      · simpa using h3
      · exact δg_flip3 c
      · rw [← flip3_ofAngles, capD_flip3]
      · rw [← flip3_ofAngles, capX_flip3]
  obtain ⟨c1, a0, a1, a2, a3, hδ, hD, hX⟩ := step1
  rcases le_or_gt (c1 0 + c1 2) (Real.pi / 4) with h | h
  · exact ⟨c1, ⟨a0, a1, a2, h⟩, hδ, Or.inl ⟨hD, hX⟩⟩
  · refine ⟨![Real.pi / 4 - c1 2, Real.pi / 4 - c1 1, Real.pi / 4 - c1 0], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp; linarith
    · simp; linarith
    · simp; linarith
    · simp; linarith
    · rw [δg_refl, hδ]
    · right
      rw [← refl_ofAngles, capD_refl, capX_refl, hD, hX]
      exact ⟨rfl, rfl⟩

end Reduction


section Reconstruct

theorem candJ_norm_sq (L Q : ℂ) (W : ℝ) :
    ‖candJ L Q W‖ ^ 2 = candK Q W * ‖L‖ ^ 2 + 2 * W * candH L Q W := by
  unfold candJ candK candH
  simp only [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  ring

/-- `J̄ Q - J W = K L` of (GOC-positive). -/
theorem conj_J_mul_Q (L Q : ℂ) (W : ℝ) :
    conj (candJ L Q W) * Q - candJ L Q W * W = (candK Q W : ℂ) * L := by
  unfold candJ candK
  have h : conj Q * Q = ((‖Q‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  push_cast at h ⊢
  linear_combination (L) * h

/-- **Algebraic core of `lem:t34k-bell-orbit`**: from the active-block identities (GOC-trace)
`z L = s + (r-1)k + iτ`, `z² Q - 2k z L = W` (with `|z| = 1`, `W ≥ 0`, `0 < k < s`, `r ≥ 1`) one gets
`J ≠ 0`, `z J = |J|`, `K = 2k|J|` and `H = |J|(s + (r-1)k)`: the reconstruction (GOC-reconstruct)
and the identity `|J|² = K|L|² + 2WH` (GOC-positive) are used to exclude the negative phase. -/
theorem goc_reconstruct {r : ℝ} (hr : 1 ≤ r) {z L Q : ℂ} {W s k τ : ℝ}
    (hz : ‖z‖ = 1) (hW : 0 ≤ W) (hk : 0 < k) (hks : k < s)
    (h1 : z * L = ((s + (r - 1) * k : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
    (h2 : z ^ 2 * Q - 2 * (k : ℂ) * (z * L) = (W : ℂ)) :
    candJ L Q W ≠ 0 ∧ candK Q W = 2 * k * ‖candJ L Q W‖ ∧
      candH L Q W = ‖candJ L Q W‖ * (s + (r - 1) * k) ∧ z * candJ L Q W = (‖candJ L Q W‖ : ℂ) := by
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have hA : 0 < s + (r - 1) * k := by nlinarith
  have hre : (z * L).re = s + (r - 1) * k := by rw [h1]; simp
  have hL : L ≠ 0 := by
    intro h; rw [h, mul_zero] at hre; simp at hre; linarith
  have hLn : 0 < ‖L‖ := norm_pos_iff.2 hL
  have e := congrArg conj h2
  simp only [map_sub, map_mul, map_pow, map_ofNat, Complex.conj_ofReal] at e
  have hQc : conj Q = z ^ 2 * W + 2 * k * z * conj L := by
    linear_combination z ^ 2 * e + (-conj Q * (1 + z * conj z) + 2 * k * z * conj L) * hzz
  have hzJ : z ^ 2 * candJ L Q W = conj (candJ L Q W) := by
    unfold candJ
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination (conj L) * h2 + (-L) * hQc
  -- `J ≠ 0`
  have hLL : L * conj L = ((‖L‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hzl : z * L + conj z * conj L = ((2 * (s + (r - 1) * k) : ℝ) : ℂ) := by
    rw [← map_mul, Complex.add_conj, hre]
  have hJ : candJ L Q W ≠ 0 := by
    intro hJ0
    unfold candJ at hJ0
    have e3 : 2 * (k : ℂ) * (L * conj L) = -(W : ℂ) * (z * L + conj z * conj L) := by
      linear_combination (-(conj z * conj L)) * h2 + (z ^ 2 * conj z) * hJ0
        + (-(2 * k * (L * conj L) + W * z * L)) * hzz
    rw [hLL, hzl] at e3
    have e4 : 2 * k * ‖L‖ ^ 2 = -W * (2 * (s + (r - 1) * k)) := by exact_mod_cast e3
    nlinarith [mul_pos hk (pow_pos hLn 2), mul_nonneg hW hA.le]
  -- `2 k z J = K`
  have hKJ : 2 * (k : ℂ) * z * candJ L Q W = (candK Q W : ℂ) := by
    have e5 : 2 * (k : ℂ) * z * candJ L Q W * L = (candK Q W : ℂ) * L := by
      linear_combination (-(candJ L Q W)) * h2 + Q * hzJ + conj_J_mul_Q L Q W
    exact mul_right_cancel₀ hL e5
  set J := candJ L Q W with hJdef
  set ρ : ℝ := candK Q W / (2 * k) with hρ
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hzρ : z * J = (ρ : ℂ) := by
    rw [hρ]; push_cast
    rw [eq_div_iff (mul_ne_zero two_ne_zero hk')]
    linear_combination hKJ
  have hnJ : ‖J‖ = |ρ| := by
    have := congrArg norm hzρ
    rwa [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs] at this
  have hconj : conj J = z * (ρ : ℂ) := by
    have := congrArg conj hzρ
    simp only [map_mul, Complex.conj_ofReal] at this
    linear_combination z * this + (-(conj J)) * hzz
  have hH : candH L Q W = ρ * (s + (r - 1) * k) := by
    rw [← re_conj_J_mul, hconj]
    have : z * (ρ : ℂ) * L = (ρ : ℂ) * (z * L) := by ring
    rw [this, Complex.re_ofReal_mul, hre]
  have hK : candK Q W = 2 * k * ρ := by rw [hρ]; field_simp
  have hJn : 0 < ‖J‖ := norm_pos_iff.2 hJ
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h, abs_zero] at hnJ; linarith
  have hsq := candJ_norm_sq L Q W
  rw [← hJdef, hnJ, sq_abs, hH, hK] at hsq
  have hρpos : 0 < ρ := by
    have : ρ = 2 * k * ‖L‖ ^ 2 + 2 * W * (s + (r - 1) * k) := by
      apply mul_left_cancel₀ hρ0
      linear_combination hsq
    rw [this]
    nlinarith [mul_pos hk (pow_pos hLn 2), mul_nonneg hW hA.le]
  have hnJ' : ‖J‖ = ρ := by rw [hnJ, abs_of_pos hρpos]
  refine ⟨hJ, ?_, ?_, ?_⟩
  · rw [hK, hnJ']
  · rw [hH, hnJ']
  · rw [hzρ, hnJ']

/-- The active-block trace identities: for `M_I = diag(s,k,…,k) + iB` (`B` real symmetric,
`B₀₀ = 0`, `τ = Tr B`, `β = ‖B‖²_F`) with `Tr M_I = zL`, `Tr M_I² = z²Q` and total Frobenius norm
`‖M‖²_F = 2s(s-k)` (spectator part `W`), the second identity of (GOC-trace) holds. -/
theorem goc_trace_of_active {z L Q : ℂ} {r s k β τ W : ℝ}
    (hL : z * L = ((s + (r - 1) * k : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
    (hQ : z ^ 2 * Q = ((s ^ 2 + (r - 1) * k ^ 2 - β : ℝ) : ℂ) + ((2 * k * τ : ℝ) : ℂ) * Complex.I)
    (hF : 2 * s * (s - k) = s ^ 2 + (r - 1) * k ^ 2 + β + W) :
    z ^ 2 * Q - 2 * (k : ℂ) * (z * L) = (W : ℂ) := by
  rw [hQ, hL]
  have e : ((s ^ 2 + (r - 1) * k ^ 2 - β : ℝ) : ℂ) + ((2 * k * τ : ℝ) : ℂ) * Complex.I
      - 2 * (k : ℂ) * (((s + (r - 1) * k : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
      = ((s ^ 2 + (r - 1) * k ^ 2 - β - 2 * k * (s + (r - 1) * k) : ℝ) : ℂ) := by
    push_cast; ring
  have hW' : s ^ 2 + (r - 1) * k ^ 2 - β - 2 * k * (s + (r - 1) * k) = W := by nlinarith [hF]
  rw [e, hW']

/-- **`lem:t34k-bell-orbit`, candidate level.**  A stationary active block with the data above
(and `‖M‖²_F = 2s(s-k) ≥ m = Σ|μ_j|²`, Schur) gives an admissible candidate (GOC-admissible) whose
value `(2H-(r-1)K)/(4H-2rK)` equals the ratio `|M₀₀|²/‖M‖²_F = s²/(2s(s-k))`. -/
theorem goc_candidate_of_active {r m : ℝ} (hr : 1 ≤ r) {z L Q : ℂ} {W s k τ : ℝ}
    (hz : ‖z‖ = 1) (hW : 0 ≤ W) (hk : 0 < k) (hks : k < s)
    (h1 : z * L = ((s + (r - 1) * k : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
    (h2 : z ^ 2 * Q - 2 * (k : ℂ) * (z * L) = (W : ℂ)) (hm : m ≤ 2 * s * (s - k)) :
    Admissible r m L Q W ∧
      s ^ 2 / (2 * s * (s - k)) = candVal r (candK Q W) (candH L Q W) := by
  obtain ⟨hJ, hK, hH, -⟩ := goc_reconstruct hr hz hW hk hks h1 h2
  have hj : 0 < ‖candJ L Q W‖ := norm_pos_iff.2 hJ
  have hA : 0 < s + (r - 1) * k := by nlinarith
  have hsk : 0 < s - k := by linarith
  have hs : 0 < s := by linarith
  refine ⟨⟨hJ, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hK]; positivity
  · rw [hH]; positivity
  · rw [hK, hH]; nlinarith [mul_pos hj hsk]
  · rw [hK, hH]
    have e : 2 * (‖candJ L Q W‖ * (s + (r - 1) * k) - (r - 1) * (2 * k * ‖candJ L Q W‖) / 2) *
        (‖candJ L Q W‖ * (s + (r - 1) * k) - r * (2 * k * ‖candJ L Q W‖) / 2)
        = ‖candJ L Q W‖ ^ 2 * (2 * s * (s - k)) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg ‖candJ L Q W‖)]
  · unfold candVal
    rw [hK, hH]
    have hd : 4 * (‖candJ L Q W‖ * (s + (r - 1) * k)) - 2 * r * (2 * k * ‖candJ L Q W‖)
        = 4 * ‖candJ L Q W‖ * (s - k) := by ring
    have hn : 2 * (‖candJ L Q W‖ * (s + (r - 1) * k)) - (r - 1) * (2 * k * ‖candJ L Q W‖)
        = 2 * ‖candJ L Q W‖ * s := by ring
    rw [hd, hn, div_eq_div_iff (by positivity) (by positivity)]
    ring

end Reconstruct


section Unbounded

theorem IsOrth.mul_transpose {R : Fin 4 → Fin 4 → ℂ} (h : IsOrth R) :
    Matrix.of R * (Matrix.of R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  exact h i j

theorem IsOrth.transpose_mul {R : Fin 4 → Fin 4 → ℂ} (h : IsOrth R) :
    (Matrix.of R)ᵀ * Matrix.of R = 1 :=
  mul_eq_one_comm.1 h.mul_transpose

/-- `Tr(MᵀM) = Σ_{ij} M_{ij}²` is invariant on the orbit: `= Σ μ_k²` (used in `lem:t34k-bell-orbit`). -/
theorem sum_entry_sq {R S : Fin 4 → Fin 4 → ℂ} (hR : IsOrth R) (hS : IsOrth S) (μ : Fin 4 → ℂ) :
    ∑ i, ∑ j, entry R S μ i j * entry R S μ i j = ∑ k, μ k * μ k := by
  have hM : Matrix.of (entry R S μ) = Matrix.of R * Matrix.diagonal μ * (Matrix.of S)ᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, entry]
  have h1 : ∑ i, ∑ j, entry R S μ i j * entry R S μ i j =
      Matrix.trace (Matrix.of (entry R S μ) * (Matrix.of (entry R S μ))ᵀ) := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : Matrix.of (entry R S μ) * (Matrix.of (entry R S μ))ᵀ =
      Matrix.of R * (Matrix.diagonal μ * Matrix.diagonal μ) * (Matrix.of R)ᵀ := by
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose]
    calc _ = Matrix.of R * Matrix.diagonal μ * ((Matrix.of S)ᵀ * Matrix.of S) *
          (Matrix.diagonal μ * (Matrix.of R)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS.transpose_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_cycle, hR.transpose_mul, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- `2|M₀₀|² ≤ ‖M‖²_F + |Σ M_{ij}²|`. -/
theorem two_norm_sq_le (M : Fin 4 → Fin 4 → ℂ) :
    2 * ‖M 0 0‖ ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 + ‖∑ i, ∑ j, M i j * M i j‖ := by
  rw [← Fintype.sum_prod_type' (f := fun i j => ‖M i j‖ ^ 2),
    ← Fintype.sum_prod_type' (f := fun i j => M i j * M i j)]
  have e1 := Finset.add_sum_erase Finset.univ (fun p : Fin 4 × Fin 4 => ‖M p.1 p.2‖ ^ 2)
    (Finset.mem_univ (0, 0))
  have e2 := Finset.add_sum_erase Finset.univ (fun p : Fin 4 × Fin 4 => M p.1 p.2 * M p.1 p.2)
    (Finset.mem_univ (0, 0))
  simp only at e1 e2
  rw [← e1, ← e2]
  have h3 : ‖∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)), M p.1 p.2 * M p.1 p.2‖ ≤
      ∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)), ‖M p.1 p.2‖ ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun p _ => by rw [norm_mul, sq])
  have h4 : ‖M 0 0 * M 0 0‖ ≤ ‖M 0 0 * M 0 0 +
      ∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)), M p.1 p.2 * M p.1 p.2‖ +
      ‖∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)), M p.1 p.2 * M p.1 p.2‖ := by
    have := norm_sub_le (M 0 0 * M 0 0 + ∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)),
      M p.1 p.2 * M p.1 p.2) (∑ p ∈ Finset.univ.erase ((0 : Fin 4), (0 : Fin 4)),
      M p.1 p.2 * M p.1 p.2)
    simpa using this
  rw [norm_mul, ← sq] at h4
  linarith

/-- **Unbounded orbit sequences** (`lem:t34k-bell-orbit`): on the whole orbit,
`|M₀₀|²/‖M‖²_F ≤ 1/2 + |Σ μ_k²| / (2‖M‖²_F)`, so along a sequence with `‖M‖_F → ∞` the ratio is
asymptotically at most `1/2`. -/
theorem ratio_le_half_add {R S : Fin 4 → Fin 4 → ℂ} (hR : IsOrth R) (hS : IsOrth S)
    (μ : Fin 4 → ℂ) :
    ratio (entry R S μ) ≤ 1 / 2 + ‖∑ k, μ k ^ 2‖ / (2 * ∑ i, ∑ j, ‖entry R S μ i j‖ ^ 2) := by
  have h := two_norm_sq_le (entry R S μ)
  rw [sum_entry_sq hR hS μ] at h
  simp only [← sq] at h
  unfold ratio
  set F := ∑ i, ∑ j, ‖entry R S μ i j‖ ^ 2 with hF
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rcases hF0.lt_or_eq with hpos | hz
  · rw [div_add_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ hpos (by positivity)]
    nlinarith [h]
  · rw [← hz]; simp

end Unbounded


section FKcos

theorem FK_eq_cos_sq {F ℓ : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (h : 2 * ℓ = Real.arccos (Real.sqrt F)) : F = Real.cos (2 * ℓ) ^ 2 := by
  rw [h, Real.cos_arccos (by linarith [Real.sqrt_nonneg F]) (Real.sqrt_le_one.2 hF1),
    Real.sq_sqrt hF0]

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

/-- **`thm:threequbitgeodesicequality` (b), abstract form.**  Under the hypotheses of
`geodesic_sign_separator`, if the least distance `min_h d(x, h𝒞x)` equals `arccos √F` (as it does for
`F = F_K` on `ℂP⁷` with the Fubini–Study distance `d([ψ],[φ]) = arccos |⟨ψ,φ⟩|`), then
`F = cos²(2ℓ)` with `ℓ = d(x, Z)`. -/
theorem geodesic_FK_cos (hgeo : IsGeodesicSpace Y) {f : Y → ℝ} (hf : Continuous f)
    (G : Set (Y ≃ᵢ Y)) (C : Y ≃ᵢ Y) (hG : ∀ h ∈ G, ∀ y, f (h y) = f y)
    (hC : ∀ y, f (C y) = - f y) (J : Set (Y ≃ᵢ Y))
    (hJG : ∀ j ∈ J, ∃ h ∈ G, ∀ y, j y = h (C y))
    (hJfix : ∀ z, f z = 0 → ∃ j ∈ J, j z = z) (x : Y) {F : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hmin : IsLeast {r : ℝ | ∃ h ∈ G, r = dist x (h (C x))} (Real.arccos (Real.sqrt F))) :
    F = Real.cos (2 * Metric.infDist x (f ⁻¹' {0})) ^ 2 := by
  have h := (geodesic_sign_separator hgeo hf G C hG hC J hJG hJfix x).1
  exact FK_eq_cos_sq hF0 hF1 (h.unique hmin)

end FKcos


end
end FormalResearch.FrameFree.OrbitCeilings

import FormalResearch.FourQubitEntropy.RenyiFullDivDiff

/-!
# Fixed-purity paths through three distinct entries: the monotonicity engine

Paper E, `lem:fqe-low-tilt-reduction` ("The slope"): along a path of four-point spectra with three
distinct values `e₁ > e₂ > e₃` of multiplicities `n₁, n₂, n₃` (`Σ nᵢ = 4`), preserving trace and
purity, `dZ = (q/3) [e₁,e₂,e₃] x^r dt`, hence `d(H_q - ωt)/du = κ (η - ω)·3`-type formula.

* `three_rpow_deriv_eq`: if `M₁+M₂+M₃ = 0` and `Σ Mᵢ eᵢ = 0` then
  `Σ Mᵢ eᵢ^r = (Σ Mᵢ eᵢ²) · [e₁,e₂,e₃] x^r`.
* `hasDerivAt_pathF`: derivative of `u ↦ log₂ Z(u)/(1-q) - ω T(u)` along such a path.
* `path_strictMonoOn`, `path_strictAntiOn`: strict monotonicity on a closed interval from a strict
  slope bound at interior points (continuity covers coalescing/vanishing entries at the ends).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem three_rpow_deriv_eq {r e1 e2 e3 M1 M2 M3 : ℝ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3)
    (h23 : e2 ≠ e3) (hM0 : M1 + M2 + M3 = 0) (hM1 : M1 * e1 + M2 * e2 + M3 * e3 = 0) :
    M1 * e1 ^ r + M2 * e2 ^ r + M3 * e3 ^ r =
      (M1 * e1 ^ 2 + M2 * e2 ^ 2 + M3 * e3 ^ 2) * dd2 r e1 e2 e3 := by
  have s12 : e1 - e2 ≠ 0 := sub_ne_zero.2 h12
  have s13 : e1 - e3 ≠ 0 := sub_ne_zero.2 h13
  have s23 : e2 - e3 ≠ 0 := sub_ne_zero.2 h23
  have hM2 : M2 = -M1 * (e1 - e3) / (e2 - e3) := by
    field_simp
    have : M3 = -M1 - M2 := by linarith
    rw [this] at hM1
    linarith
  have hM3 : M3 = M1 * (e1 - e2) / (e2 - e3) := by
    have : M3 = -M1 - M2 := by linarith
    rw [this, hM2]
    field_simp
    ring
  rw [hM2, hM3]
  unfold dd2
  have t12 : e2 - e1 ≠ 0 := fun h => s12 (by linarith)
  have t13 : e3 - e1 ≠ 0 := fun h => s13 (by linarith)
  have t23 : e3 - e2 ≠ 0 := fun h => s23 (by linarith)
  field_simp
  ring

/-- `Z(u) = n₁ E₁(u)^q + n₂ E₂(u)^q + n₃ E₃(u)^q`. -/
noncomputable def Zp (q n1 n2 n3 : ℝ) (E1 E2 E3 : ℝ → ℝ) (u : ℝ) : ℝ :=
  n1 * E1 u ^ q + n2 * E2 u ^ q + n3 * E3 u ^ q

/-- The path functional `F(u) = log₂ Z(u)/(1-q) - ω T(u)`. -/
noncomputable def pathF (q ω n1 n2 n3 : ℝ) (E1 E2 E3 T : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.logb 2 (Zp q n1 n2 n3 E1 E2 E3 u) / (1 - q) - ω * T u

/-- The slope `3η = -q [e₁,e₂,e₃]x^r /(r ln 2 · Z)`. -/
noncomputable def slope3 (q n1 n2 n3 : ℝ) (E1 E2 E3 : ℝ → ℝ) (u : ℝ) : ℝ :=
  q * (-dd2 (q - 1) (E1 u) (E2 u) (E3 u)) / ((q - 1) * Real.log 2 * Zp q n1 n2 n3 E1 E2 E3 u)

theorem hasDerivAt_pathF {q ω n1 n2 n3 : ℝ} (hq : 1 < q) {E1 E2 E3 T : ℝ → ℝ} {w1 w2 w3 u : ℝ}
    (h1 : HasDerivAt E1 w1 u) (h2 : HasDerivAt E2 w2 u) (h3 : HasDerivAt E3 w3 u)
    (hT : HasDerivAt T (3 * (n1 * w1 * E1 u ^ 2 + n2 * w2 * E2 u ^ 2 + n3 * w3 * E3 u ^ 2)) u)
    (hZ : 0 < Zp q n1 n2 n3 E1 E2 E3 u)
    (c0 : n1 * w1 + n2 * w2 + n3 * w3 = 0)
    (c1 : n1 * w1 * E1 u + n2 * w2 * E2 u + n3 * w3 * E3 u = 0)
    (o12 : E1 u ≠ E2 u) (o13 : E1 u ≠ E3 u) (o23 : E2 u ≠ E3 u) :
    HasDerivAt (pathF q ω n1 n2 n3 E1 E2 E3 T)
      ((n1 * w1 * E1 u ^ 2 + n2 * w2 * E2 u ^ 2 + n3 * w3 * E3 u ^ 2) *
        (slope3 q n1 n2 n3 E1 E2 E3 u - 3 * ω)) u := by
  have hq1 : (1 : ℝ) ≤ q := hq.le
  have d1 : HasDerivAt (fun u => E1 u ^ q) (w1 * (q * E1 u ^ (q - 1))) u :=
    (Real.hasDerivAt_rpow_const (Or.inr hq1)).comp u h1 |>.congr_deriv (by ring)
  have d2 : HasDerivAt (fun u => E2 u ^ q) (w2 * (q * E2 u ^ (q - 1))) u :=
    (Real.hasDerivAt_rpow_const (Or.inr hq1)).comp u h2 |>.congr_deriv (by ring)
  have d3 : HasDerivAt (fun u => E3 u ^ q) (w3 * (q * E3 u ^ (q - 1))) u :=
    (Real.hasDerivAt_rpow_const (Or.inr hq1)).comp u h3 |>.congr_deriv (by ring)
  have dZ : HasDerivAt (Zp q n1 n2 n3 E1 E2 E3)
      (n1 * (w1 * (q * E1 u ^ (q - 1))) + n2 * (w2 * (q * E2 u ^ (q - 1))) +
        n3 * (w3 * (q * E3 u ^ (q - 1)))) u := by
    unfold Zp
    exact ((d1.const_mul n1).add (d2.const_mul n2)).add (d3.const_mul n3)
  have key := three_rpow_deriv_eq (r := q - 1) (M1 := n1 * w1) (M2 := n2 * w2) (M3 := n3 * w3)
    o12 o13 o23 c0 c1
  have hL := dZ.log hZ.ne'
  have hF := ((hL.div_const (Real.log 2)).div_const (1 - q)).sub (hT.const_mul ω)
  have hfun : pathF q ω n1 n2 n3 E1 E2 E3 T = fun u =>
      Real.log (Zp q n1 n2 n3 E1 E2 E3 u) / Real.log 2 / (1 - q) - ω * T u := by
    funext u; simp only [pathF, Real.logb]
  rw [hfun]
  refine hF.congr_deriv ?_
  unfold slope3
  have hq1' : q - 1 ≠ 0 := by linarith
  have hq1'' : 1 - q ≠ 0 := by linarith
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hsum : n1 * (w1 * (q * E1 u ^ (q - 1))) + n2 * (w2 * (q * E2 u ^ (q - 1))) +
        n3 * (w3 * (q * E3 u ^ (q - 1))) =
      q * ((n1 * w1 * E1 u ^ 2 + n2 * w2 * E2 u ^ 2 + n3 * w3 * E3 u ^ 2) *
        dd2 (q - 1) (E1 u) (E2 u) (E3 u)) := by
    rw [← key]; ring
  rw [hsum]
  field_simp
  ring

theorem path_continuousOn {q ω n1 n2 n3 : ℝ} (hq : 1 < q) {E1 E2 E3 T : ℝ → ℝ} {u0 u1 : ℝ}
    (cE1 : ContinuousOn E1 (Icc u0 u1)) (cE2 : ContinuousOn E2 (Icc u0 u1))
    (cE3 : ContinuousOn E3 (Icc u0 u1)) (cT : ContinuousOn T (Icc u0 u1))
    (hZ : ∀ u ∈ Icc u0 u1, 0 < Zp q n1 n2 n3 E1 E2 E3 u) :
    ContinuousOn (pathF q ω n1 n2 n3 E1 E2 E3 T) (Icc u0 u1) := by
  have hq0 : 0 ≤ q := by linarith
  have r1 : ContinuousOn (fun u => E1 u ^ q) (Icc u0 u1) :=
    (Real.continuous_rpow_const hq0).comp_continuousOn cE1
  have r2 : ContinuousOn (fun u => E2 u ^ q) (Icc u0 u1) :=
    (Real.continuous_rpow_const hq0).comp_continuousOn cE2
  have r3 : ContinuousOn (fun u => E3 u ^ q) (Icc u0 u1) :=
    (Real.continuous_rpow_const hq0).comp_continuousOn cE3
  have cZ : ContinuousOn (Zp q n1 n2 n3 E1 E2 E3) (Icc u0 u1) := by
    unfold Zp
    exact ((r1.const_smul n1).add (r2.const_smul n2)).add (r3.const_smul n3)
  have cL : ContinuousOn (fun u => Real.log (Zp q n1 n2 n3 E1 E2 E3 u)) (Icc u0 u1) :=
    cZ.log (fun u hu => (hZ u hu).ne')
  unfold pathF Real.logb
  exact ((cL.div_const _).div_const _).sub (cT.const_smul ω)

/-- **Monotone path, increasing case**: `κ > 0` and `slope3 > 3ω` on the open interval. -/
theorem path_strictMonoOn {q ω n1 n2 n3 : ℝ} (hq : 1 < q) {E1 E2 E3 T : ℝ → ℝ} {u0 u1 : ℝ}
    (cE1 : ContinuousOn E1 (Icc u0 u1)) (cE2 : ContinuousOn E2 (Icc u0 u1))
    (cE3 : ContinuousOn E3 (Icc u0 u1)) (cT : ContinuousOn T (Icc u0 u1))
    (hZ : ∀ u ∈ Icc u0 u1, 0 < Zp q n1 n2 n3 E1 E2 E3 u)
    {w1 w2 w3 : ℝ → ℝ}
    (d1 : ∀ u ∈ Ioo u0 u1, HasDerivAt E1 (w1 u) u) (d2 : ∀ u ∈ Ioo u0 u1, HasDerivAt E2 (w2 u) u)
    (d3 : ∀ u ∈ Ioo u0 u1, HasDerivAt E3 (w3 u) u)
    (dT : ∀ u ∈ Ioo u0 u1,
      HasDerivAt T (3 * (n1 * w1 u * E1 u ^ 2 + n2 * w2 u * E2 u ^ 2 + n3 * w3 u * E3 u ^ 2)) u)
    (c0 : ∀ u ∈ Ioo u0 u1, n1 * w1 u + n2 * w2 u + n3 * w3 u = 0)
    (c1 : ∀ u ∈ Ioo u0 u1, n1 * w1 u * E1 u + n2 * w2 u * E2 u + n3 * w3 u * E3 u = 0)
    (ord : ∀ u ∈ Ioo u0 u1, E1 u ≠ E2 u ∧ E1 u ≠ E3 u ∧ E2 u ≠ E3 u)
    (hκ : ∀ u ∈ Ioo u0 u1, 0 < n1 * w1 u * E1 u ^ 2 + n2 * w2 u * E2 u ^ 2 + n3 * w3 u * E3 u ^ 2)
    (hη : ∀ u ∈ Ioo u0 u1, 3 * ω < slope3 q n1 n2 n3 E1 E2 E3 u) :
    StrictMonoOn (pathF q ω n1 n2 n3 E1 E2 E3 T) (Icc u0 u1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc u0 u1)
    (path_continuousOn hq cE1 cE2 cE3 cT hZ) ?_
  intro u hu
  rw [interior_Icc] at hu
  have h := hasDerivAt_pathF (ω := ω) (n1 := n1) (n2 := n2) (n3 := n3) hq (d1 u hu) (d2 u hu)
    (d3 u hu) (dT u hu) (hZ u (Ioo_subset_Icc_self hu)) (c0 u hu) (c1 u hu) (ord u hu).1
    (ord u hu).2.1 (ord u hu).2.2
  rw [h.deriv]
  exact mul_pos (hκ u hu) (by linarith [hη u hu])

/-- **Monotone path, decreasing case**: `κ < 0` and `slope3 > 3ω` on the open interval. -/
theorem path_strictAntiOn {q ω n1 n2 n3 : ℝ} (hq : 1 < q) {E1 E2 E3 T : ℝ → ℝ} {u0 u1 : ℝ}
    (cE1 : ContinuousOn E1 (Icc u0 u1)) (cE2 : ContinuousOn E2 (Icc u0 u1))
    (cE3 : ContinuousOn E3 (Icc u0 u1)) (cT : ContinuousOn T (Icc u0 u1))
    (hZ : ∀ u ∈ Icc u0 u1, 0 < Zp q n1 n2 n3 E1 E2 E3 u)
    {w1 w2 w3 : ℝ → ℝ}
    (d1 : ∀ u ∈ Ioo u0 u1, HasDerivAt E1 (w1 u) u) (d2 : ∀ u ∈ Ioo u0 u1, HasDerivAt E2 (w2 u) u)
    (d3 : ∀ u ∈ Ioo u0 u1, HasDerivAt E3 (w3 u) u)
    (dT : ∀ u ∈ Ioo u0 u1,
      HasDerivAt T (3 * (n1 * w1 u * E1 u ^ 2 + n2 * w2 u * E2 u ^ 2 + n3 * w3 u * E3 u ^ 2)) u)
    (c0 : ∀ u ∈ Ioo u0 u1, n1 * w1 u + n2 * w2 u + n3 * w3 u = 0)
    (c1 : ∀ u ∈ Ioo u0 u1, n1 * w1 u * E1 u + n2 * w2 u * E2 u + n3 * w3 u * E3 u = 0)
    (ord : ∀ u ∈ Ioo u0 u1, E1 u ≠ E2 u ∧ E1 u ≠ E3 u ∧ E2 u ≠ E3 u)
    (hκ : ∀ u ∈ Ioo u0 u1, n1 * w1 u * E1 u ^ 2 + n2 * w2 u * E2 u ^ 2 + n3 * w3 u * E3 u ^ 2 < 0)
    (hη : ∀ u ∈ Ioo u0 u1, 3 * ω < slope3 q n1 n2 n3 E1 E2 E3 u) :
    StrictAntiOn (pathF q ω n1 n2 n3 E1 E2 E3 T) (Icc u0 u1) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc u0 u1)
    (path_continuousOn hq cE1 cE2 cE3 cT hZ) ?_
  intro u hu
  rw [interior_Icc] at hu
  have h := hasDerivAt_pathF (ω := ω) (n1 := n1) (n2 := n2) (n3 := n3) hq (d1 u hu) (d2 u hu)
    (d3 u hu) (dT u hu) (hZ u (Ioo_subset_Icc_self hu)) (c0 u hu) (c1 u hu) (ord u hu).1
    (ord u hu).2.1 (ord u hu).2.2
  rw [h.deriv]
  exact mul_neg_of_neg_of_pos (hκ u hu) (by linarith [hη u hu])

end FormalResearch.FourQubitEntropy.RenyiFull

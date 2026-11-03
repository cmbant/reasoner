module

public import FormalResearch.FourQubitEntropy.RenyiTwoUp
public import FormalResearch.FourQubitEntropy.PaperEGenJointPurity
public import FormalResearch.FourQubitEntropy.RenyiFullHeadlineQV
public import FormalResearch.FourQubitEntropy.QVEqualityState

/-!
# Equality in (QV) along the cluster-to-Bell family; sharpness of the coefficient `3`

Paper E, `quadratic_variance_certificate.tex`, `thm:fqe-sharp-quadratic-variance` and `sup_renyi.tex`
(`sec:sup-qk`): the family `eq:fqe-quadratic-family` (`quadFam x y`, `x² + y² = 1`, cut spectra
`(x², y², 0, 0)`, `(1/4)⁴`, `(1/4)⁴`; with `r = x² - y² ∈ [-1, 1]`) has

`P = 1 + r²/2`, `F = (1 - r²)/2`, `V_P = (1 + 2r²)²/24`

(`quadFam_purity_eq`, `quadFam_F_eq`, `quadFam_VP_eq`), hence equality `6 V_P = F² + 3P(P-1)` in (QV) along the
whole family (`quadFam_qv_equality`) and, off the cluster state, `(6V_P - F²)/(P(P-1)) = 3`
(`quadFam_qv_ratio`).  So the coefficient `3` cannot be decreased (`qv_coefficient_optimal`: for every `c < 3` the
Bell-pair product violates `F² + c P(P-1) ≥ 6 V_P`).  Everything here is unconditional and does not use (QV).
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy

theorem quadFam_cutPurity12 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    cutPurity12 (quadFam x y) = (x ^ 2) ^ 2 + (y ^ 2) ^ 2 := by
  unfold cutPurity12
  exact quadFam_cutSum12 hxy (fun t => t ^ 2) (by simp)

theorem quadFam_cutPurity13 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) : cutPurity13 (quadFam x y) = 1 / 4 := by
  unfold cutPurity13; simp [quadFam_eig13 hxy]; norm_num

theorem quadFam_cutPurity14 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) : cutPurity14 (quadFam x y) = 1 / 4 := by
  unfold cutPurity14; simp [quadFam_eig14 hxy]; norm_num

theorem quadFam_cubic {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    cubicMoment (quadFam x y) = (x ^ 2) ^ 3 + (y ^ 2) ^ 3 + 1 / 8 := by
  rw [RenyiFull.cubicMoment_eq_eigen]
  have h12 := quadFam_cutSum12 hxy (fun t => t ^ 3) (by simp)
  rw [h12]
  simp [quadFam_eig13 hxy, quadFam_eig14 hxy]
  ring

theorem quadFam_purity_eq {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    purity (quadFam x y) = 1 + (x ^ 2 - y ^ 2) ^ 2 / 2 := by
  rw [purity_quadFam hxy]
  have : y ^ 2 = 1 - x ^ 2 := by linarith
  rw [this]; ring

theorem quadFam_F_eq {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    sexticF (quadFam x y) = (1 - (x ^ 2 - y ^ 2) ^ 2) / 2 := by
  unfold sexticF
  rw [normSqPsi_quadFam, hxy, quadFam_purity_eq hxy, quadFam_cubic hxy]
  have : y ^ 2 = 1 - x ^ 2 := by linarith
  rw [this]; ring

/-- `V_P` of the family: `(1 + 2r²)²/24`, `r = x² - y²`. -/
theorem quadFam_VP_eq {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    VP (quadFam x y) = (1 + 2 * (x ^ 2 - y ^ 2) ^ 2) ^ 2 / 24 := by
  unfold VP
  rw [quadFam_cutPurity12 hxy, quadFam_cutPurity13 hxy, quadFam_cutPurity14 hxy, quadFam_purity_eq hxy]
  have : y ^ 2 = 1 - x ^ 2 := by linarith
  rw [this]; ring

/-- **Equality in (QV) along the whole cluster-to-Bell family** (`thm:fqe-sharp-quadratic-variance`,
`eq:fqe-quadratic-family`): `6 V_P = F² + 3 P (P - 1)` for `ψ_{x,y}`, `x² + y² = 1`. -/
theorem quadFam_qv_equality {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    6 * VP (quadFam x y) = sexticF (quadFam x y) ^ 2 +
      3 * purity (quadFam x y) * (purity (quadFam x y) - 1) := by
  rw [quadFam_VP_eq hxy, quadFam_F_eq hxy, quadFam_purity_eq hxy]; ring

/-- Along the family `P(P-1) = r²(2 + r²)/4`, positive exactly off the cluster state `x² = y²`. -/
theorem quadFam_P_pos {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hr : x ^ 2 ≠ y ^ 2) :
    0 < purity (quadFam x y) * (purity (quadFam x y) - 1) := by
  rw [quadFam_purity_eq hxy]
  have : 0 < (x ^ 2 - y ^ 2) ^ 2 := by
    have : x ^ 2 - y ^ 2 ≠ 0 := sub_ne_zero.2 hr
    positivity
  nlinarith

/-- **The ratio is exactly `3`** along the family off the cluster state:
`(6 V_P - F²)/(P (P - 1)) = 3`, so the coefficient `3` in (QV) cannot be decreased. -/
theorem quadFam_qv_ratio {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hr : x ^ 2 ≠ y ^ 2) :
    (6 * VP (quadFam x y) - sexticF (quadFam x y) ^ 2) /
      (purity (quadFam x y) * (purity (quadFam x y) - 1)) = 3 := by
  have hpos := quadFam_P_pos hxy hr
  rw [div_eq_iff hpos.ne']
  have := quadFam_qv_equality hxy
  linarith

/-- **The coefficient `3` of (QV) cannot be decreased**: for every `c < 3` the Bell-pair product
`ψ_{1,0}` (the end of the family, `r = 1`) is a unit state violating `F² + c P (P-1) ≥ 6 V_P`. -/
theorem qv_coefficient_optimal {c : ℝ} (hc : c < 3) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧
      sexticF ψ ^ 2 + c * purity ψ * (purity ψ - 1) < 6 * VP ψ := by
  have hxy : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  refine ⟨quadFam 1 0, quadFam_unit hxy, ?_⟩
  have hpos := quadFam_P_pos hxy (by norm_num)
  have h := quadFam_qv_equality hxy
  nlinarith

/-- The same for every other member of the family off the cluster state. -/
theorem qv_coefficient_optimal_family {c x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hr : x ^ 2 ≠ y ^ 2) (hc : c < 3) :
    sexticF (quadFam x y) ^ 2 + c * purity (quadFam x y) * (purity (quadFam x y) - 1) <
      6 * VP (quadFam x y) := by
  have hpos := quadFam_P_pos hxy hr
  have h := quadFam_qv_equality hxy
  nlinarith

end FormalResearch.FourQubitEntropy.QVEquality

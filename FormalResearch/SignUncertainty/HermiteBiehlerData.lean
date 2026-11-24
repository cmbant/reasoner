module

public import FormalResearch.SignUncertainty.HermiteBiehlerUniq

/-!
# Hermite–Biehler extremal data (neutral interface)

The structure `HermiteBiehlerData` packages an Airy-type Hermite–Biehler extremal profile `G` for a
pair `(P, Q)` with `AiryPQHB P Q`: its sign structure on the zero set `S`, the minimal zero `tm`, and the
uniqueness property used by the radial rigidity theorem (`gt:7.5`, `RadialRigidity.lean`) and by any other
profile-compactness argument built on `HermiteBiehlerUniq`. It imports nothing Hankel- or Virasoro-specific,
so that other lanes can share it. The one-level instance `HermiteBiehlerData.airy` is in `RadialRigidity.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- Unified Hermite–Biehler extremal and uniqueness package covering `(P, Q) = (1, 0)` (`m = 1`,
`G_Ai = airyExtremal`) as well as all `AiryPQHB P Q` with `Q ≠ 0` (`hbExtremal`). -/
structure HermiteBiehlerData where
  P : ℝ[X]
  Q : ℝ[X]
  hHB : AiryPQHB P Q
  S : Finset ℝ
  tm : ℝ
  G : ℂ → ℂ
  S_nonempty : S.Nonempty
  tm_mem : tm ∈ S
  tm_min : ∀ t ∈ S, tm ≤ t
  G_diff : Differentiable ℂ G
  G_int : Integrable (fun x : ℝ => G (x : ℂ))
  G_env : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖G u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u
  G_real : ∀ x : ℝ, (G (x : ℂ)).im = 0
  G_integral_zero : (∫ x : ℝ, G (x : ℂ)) = 0
  G_l1_pos : 0 < ∫ x : ℝ, ‖G (x : ℂ)‖
  G_nonneg_left : ∀ x : ℝ, x ≤ tm → 0 ≤ (G (x : ℂ)).re
  G_eq_zero_on_S : ∀ t ∈ S, G (t : ℂ) = 0
  G_deriv_ne_zero : ∀ t ∈ S, deriv G (t : ℂ) ≠ 0
  uniqueness : ∀ {H : ℂ → ℂ} {C ν : ℝ},
    Differentiable ℂ H → Integrable (fun x : ℝ => H (x : ℂ)) →
    0 ≤ C → (∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
    (∀ x : ℝ, (H (x : ℂ)).im = 0) →
    0 ≤ (∫ x : ℝ, H (x : ℂ)).re →
    (∀ t ∈ S, t ≠ tm → (H (t : ℂ)).re ≤ 0) →
    (∀ x : ℝ, x ≤ tm → (H (x : ℂ)).re ≤ 0) →
    ∃ b : ℝ, 0 ≤ b ∧ (∀ z : ℂ, H z = -((b : ℂ) * G z)) ∧
      ((∃ z : ℂ, H z ≠ 0) →
        0 < b ∧
        b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖G (x : ℂ)‖) ∧
        ∀ t ∈ S, deriv H (t : ℂ) ≠ 0)

/-- Unit-`L¹` normalized extremal profile `G_N / ‖G_N‖₁` on `ℝ`. -/
noncomputable def HermiteBiehlerData.normG (D : HermiteBiehlerData) (u : ℝ) : ℝ :=
  (D.G (u : ℂ)).re / ∫ x : ℝ, ‖D.G (x : ℂ)‖

lemma HermiteBiehlerData.normG_continuous (D : HermiteBiehlerData) : Continuous D.normG :=
  ((Complex.continuous_re.comp (D.G_diff.continuous.comp Complex.continuous_ofReal)).div_const _)

lemma HermiteBiehlerData.normG_integrable (D : HermiteBiehlerData) : Integrable D.normG :=
  D.G_int.re.div_const _

lemma HermiteBiehlerData.normG_integral (D : HermiteBiehlerData) : ∫ u : ℝ, D.normG u = 0 := by
  unfold HermiteBiehlerData.normG
  have hre : ∫ u : ℝ, (D.G (u : ℂ)).re = (∫ u : ℝ, D.G (u : ℂ)).re := integral_re D.G_int
  rw [integral_div, hre, D.G_integral_zero, Complex.zero_re, zero_div]

lemma HermiteBiehlerData.normG_abs_integral (D : HermiteBiehlerData) :
    ∫ u : ℝ, |D.normG u| = 1 := by
  have hnorm : (fun u : ℝ => |D.normG u|) =
      fun u : ℝ => ‖D.G (u : ℂ)‖ / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
    ext u
    unfold HermiteBiehlerData.normG
    have hG_cast : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
    rw [abs_div, abs_of_pos D.G_l1_pos]
    congr 1
    conv_rhs => rw [hG_cast, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, integral_div, div_self D.G_l1_pos.ne']

end FormalResearch.SignUncertainty

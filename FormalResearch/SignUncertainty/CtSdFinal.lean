module

public import FormalResearch.SignUncertainty.CtSdFinalAux

/-!
# `(ct:K-airy)` for the concrete outer amplitude (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` (1), `(ct:K-airy)`.  **Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart FormalResearch.Special

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `‖T(s;β)‖ ≤ K ‖s‖` on a polydisc. -/
lemma exists_Tf_lip : ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧ ∀ s β : ℂ, ‖s‖ < r → ‖β‖ < r → ‖Tf (s, β)‖ ≤ K * ‖s‖ := by
  obtain ⟨K, r, hr, hL⟩ := lipschitz_of_cd contDiffAt_Tf
  refine ⟨K, r, K.coe_nonneg, hr, fun s β hs hβ => ?_⟩
  have h1 := hL.dist_le_mul (s, β) (mem_ball_prod hs hβ) (0, β) (mem_ball_prod (by simpa using hr) hβ)
  rw [dist_eq_norm, dist_eq_norm, Tf_zero_left, sub_zero] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  rw [show ((s, β) - ((0 : ℂ), β)) = (s, (0 : ℂ)) by simp, Prod.norm_def]
  simp

lemma momOK_mono {R₀ : ℝ} {p : ℂ} {C C' U : ℝ} {ch : Chain3 R₀ p} (h : MomOK C U ch) (hC : C ≤ C') :
    MomOK C' U ch := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right hC (by positivity)), h2.trans hC,
    h3.trans (mul_le_mul_of_nonneg_right hC (by positivity))⟩

/-- The model parameter `Û = (a + λ³ ψ) / (κ λ²)`. -/
noncomputable def Uhat (lam a psi : ℝ) : ℝ := (a + lam ^ 3 * psi) / (kap * lam ^ 2)

/-- The constant `Q_0 = -(7/200) (18 π²)^{1/3}`. -/
noncomputable def q0c : ℝ := -(7 / 200) * (18 * π ^ 2) ^ ((1 : ℝ) / 3)

/-- The main term of `(ct:K-airy)`. -/
noncomputable def KMain (lam psi q0 hh U : ℝ) : ℝ :=
  (1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)) * (-π * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U)) +
    lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi U * airyBi U))

/-- A bound `ψ(β) = θ̂(β)/d(β)` near `0`. -/
lemma exists_psi_bound {th : ℝ → ℝ} (hth : AnalyticAt ℝ th 0) :
    ∃ δ Cψ : ℝ, 0 < δ ∧ 0 ≤ Cψ ∧ ∀ β : ℝ, |β| < δ → |th β / CtCfu.dF β| ≤ Cψ := by
  have hd := CtCfu.d0_pos
  have hc : ContinuousAt (fun β => th β / CtCfu.dF β) 0 :=
    hth.continuousAt.div CtCfu.contDiffAt_dF.continuousAt (by rw [CtCfu.dF_zero]; exact hd.ne')
  have hev : ∀ᶠ β in 𝓝 (0 : ℝ), |th β / CtCfu.dF β| < |th 0 / CtCfu.dF 0| + 1 :=
    (continuous_abs.continuousAt.comp hc).eventually (gt_mem_nhds (by simp))
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, |th 0 / CtCfu.dF 0| + 1, hδ, by positivity, fun β hβ => (h (by simpa using hβ)).le⟩

end FormalResearch.SignUncertainty.CtSd

import FormalResearch.FrameFree.SupportRateApply
import FormalResearch.FrameFree.HelstromSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate Matrix BigOperators InnerProductSpace
open FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

/-!
# Support rate for the Helstrom support test, conditional on the Zariski-closure supremum

Namespace `FormalResearch.FrameFree.SupportRate`.  `ZClosureSup ψ` says that every `z` whose tensor powers
`z^{⊗k}` all lie in `W_k = span{(gΘψ)^{⊗k}}` satisfies `|⟨ψ|z⟩|² ≤ F_C(ψ) ‖z‖²`: the supremum of the
normalised overlap over the Zariski closure of the filter orbit equals the supremum over the orbit.
Given it, the spectral-radius theorem of `SupportRateApply` proves `SupportRateUpper ψ` and hence the
unconditional-in-`SupportRateUpper` forms of `eventually_neg_log_c_le`, `tendsto_of_calibrated`.
-/

namespace FormalResearch.FrameFree.SupportRate

/-- Supremum of `|⟨ψ|z⟩|²/‖z‖²` over the Zariski-closure cone of the filter orbit is at most `F_C(ψ)`. -/
def ZClosureSup {n : ℕ} (ψ : Ψ n) : Prop :=
  ∀ z : Ψ n, (∀ k : ℕ, WithLp.toLp 2 (copies k z) ∈ suppSpace k ψ) →
    Complex.normSq (ip ψ z) ≤ Ceilings.FCΘ ψ * nsq z

/-- The filter orbit of `Θψ`, as a subset of `ℂ^{{0,1}^n}`. -/
def orbitSet {n : ℕ} (ψ : Ψ n) : Set (V (Fin n → Fin 2)) :=
  {z | ∃ g : Fin n → Op1, (∀ i, (g i).det = 1) ∧ z = WithLp.toLp 2 (rot g (Θ ψ))}

theorem W_orbitSet {n : ℕ} (ψ : Ψ n) (k : ℕ) : W (orbitSet ψ) k = suppSpace k ψ := by
  unfold W suppSpace
  congr 1
  ext w
  constructor
  · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩

/-- **Spectral-radius half of `thm:supportrate`**, given the Zariski-closure supremum bound
(`ZClosureSup`): `limsup R_k^{1/k} ≤ F_C`. -/
theorem supportRateUpper_of_zClosureSup {n : ℕ} (ψ : Ψ n) (h : ZClosureSup ψ) :
    Helstrom.SupportRateUpper ψ := by
  intro c hc
  have hne : (orbitSet ψ).Nonempty :=
    ⟨_, fun _ => 1, fun i => by simp, rfl⟩
  have hF : ∀ z : V (Fin n → Fin 2), (∀ k, pw z k ∈ W (orbitSet ψ) k) →
      ‖⟪(WithLp.toLp 2 ψ : V (Fin n → Fin 2)), z⟫_ℂ‖ ^ 2 ≤ Ceilings.FCΘ ψ * ‖z‖ ^ 2 := by
    intro z hz
    have hz' : ∀ k : ℕ, WithLp.toLp 2 (copies k (WithLp.ofLp z)) ∈ suppSpace k ψ := fun k => by
      rw [← W_orbitSet]; exact hz k
    have := h (WithLp.ofLp z) hz'
    have e1 : ⟪(WithLp.toLp 2 ψ : V (Fin n → Fin 2)), z⟫_ℂ = ip ψ (WithLp.ofLp z) := by
      rw [inner_V]; rfl
    have e2 : ‖z‖ ^ 2 = nsq (WithLp.ofLp z) := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun j _ => (Complex.normSq_eq_norm_sq _).symm
    rw [e1, e2, Complex.sq_norm]
    exact this
  have key := eventually_proj_sq_le (orbitSet ψ) hne (WithLp.toLp 2 ψ) (Ceilings.FCΘ ψ)
    (Ceilings.FCΘ_nonneg ψ) hF hc
  filter_upwards [key] with d hd
  have hS : ∀ (S T : Submodule ℂ (Eg (Fin n → Fin 2) d)) [S.HasOrthogonalProjection]
      [T.HasOrthogonalProjection] (v : Eg (Fin n → Fin 2) d), S = T →
      S.starProjection v = T.starProjection v := by
    intro S T _ _ v e
    subst e
    rfl
  have e := hS _ _ (pw (WithLp.toLp 2 ψ) d) (W_orbitSet ψ d)
  unfold Helstrom.Rk
  rw [e] at hd
  exact hd

theorem eventually_neg_log_c_le_of_zClosureSup {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (h : ZClosureSup ψ)
    {c : ℝ} (hc : Ceilings.FCΘ ψ < c) :
    ∀ᶠ k : ℕ in Filter.atTop, -Real.log c ≤ -(1 / (k : ℝ)) * Real.log (Pe k ψ) :=
  eventually_neg_log_c_le ψ hψ (supportRateUpper_of_zClosureSup ψ h) hc

theorem tendsto_of_calibrated_of_zClosureSup {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (h : ZClosureSup ψ)
    (hcal : Ceilings.FCΘ ψ = FKΘ ψ) :
    Filter.Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop (nhds (CK ψ)) :=
  tendsto_of_calibrated ψ hψ (supportRateUpper_of_zClosureSup ψ h) hcal

end FormalResearch.FrameFree.SupportRate

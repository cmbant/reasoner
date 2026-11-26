module

public import FormalResearch.SignUncertainty.ShellGapHankel

/-!
# The origin mass identity (proof of `thm:ce-physical-profile`; first step of `eq:ce-origin-floor`)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex`, proof of `thm:ce-physical-profile`: "Since `ĥ_c ≥ 0`, the equal
origin values give `M[ĥ_c] = h_c(0) = ĥ_c(0) = ∫ h_c ρ₀ ∈ (0, 1]`" (in the normalisation `M[h_c] = 1`).

`hankelShellProfile_origin_mass`: for a Hankel Cohn–Elkies profile `G` (`HankelShellProfile`) in dimension
`d = n + 1 ≥ 2`, `0 < G(0) = M[𝓗_c G] ≤ M[G]`, where `M[f] = ∫ |f| ρ₀` (`hankelMass`). Proved from the Hankel
inversion `besselHankel_involutive`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Origin mass identity** (proof of `thm:ce-physical-profile`, first step of `eq:ce-origin-floor`, which is not formalised; `d = n + 1 ≥ 2`, `c = d/2`):
for a Hankel Cohn–Elkies profile `G` (`ĥ ≥ 0`, `h(0) = ĥ(0) > 0`), the mass of the Fourier profile equals the
origin value, `M[ĥ] = h(0) = ĥ(0) = ∫ h ρ₀`, which is positive and at most `M[h]`. -/
theorem hankelShellProfile_origin_mass {n : ℕ} (hn : 1 ≤ n) {T : ℝ} {G : ℝ → ℝ}
    (hG : HankelShellProfile (((n : ℝ) + 1) / 2) T G) :
    0 < G 0 ∧ hankelMass (((n : ℝ) + 1) / 2) (besselHankelTransform (((n : ℝ) + 1) / 2) G) = G 0 ∧
      G 0 ≤ hankelMass (((n : ℝ) + 1) / 2) G := by
  set c : ℝ := ((n : ℝ) + 1) / 2 with hc
  have hc1 : 1 / 2 < c := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hc]; linarith
  have hcpos : 0 < c := by linarith
  refine ⟨hG.origin_pos, ?_, ?_⟩
  · -- `M[ĥ] = ∫ ĥ ρ₀ = (𝓗 ĥ)(0) = G(0)`
    have h0 := besselHankel_involutive n hn hG.cont hG.int hG.cont_hat hG.int_hat (Δ := 0) le_rfl
    rw [besselHankelTransform_zero hcpos] at h0
    rw [← h0]
    unfold hankelMass
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    show |besselHankelTransform c G s| * hankelRho0 c s = besselHankelTransform c G s * hankelRho0 c s
    rw [abs_of_nonneg (hG.nonneg_hat s (le_of_lt hs))]
  · -- `G(0) = ĥ(0) = ∫ h ρ₀ ≤ ∫ |h| ρ₀`
    rw [hG.origin, besselHankelTransform_zero hcpos]
    unfold hankelMass
    refine setIntegral_mono_on hG.int (abs_mul_rho0_integrableOn hcpos hG.int) measurableSet_Ioi
      fun s hs => ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (hankelRho0_nonneg hcpos (le_of_lt hs))

/-- info: 'FormalResearch.SignUncertainty.hankelShellProfile_origin_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelShellProfile_origin_mass

end FormalResearch.SignUncertainty

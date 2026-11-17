module

public import FormalResearch.Special.LatticeAlg

/-!
# `lem:latticesum` for the Gamma phase: set-up

`lsum nc L F = ∑ᵢ log(L Fᵢ) = ℓ_Σ`, `gammaG nc ℓ θ₀ s = θ₀ + sℓ - nc·arg Γ(½+is)` (the paper's `G`),
and the verification (for `L` large) of the hypotheses of `calPhase_gamma` for
`m = nc log L/(2π)`, `M = 4m`: `gamma_calPhase`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

/-- `ℓ_Σ = ∑ᵢ log(L Fᵢ)`. -/
noncomputable def lsum (nc : ℕ) (L : ℝ) (F : Fin nc → ℝ) : ℝ := ∑ i, Real.log (L * F i)

/-- The paper's `G(s) = θ₀ + s ℓ_Σ - ϰ arg Γ(½ + is)` on the real line. -/
noncomputable def gammaG (nc : ℕ) (ℓ θ0 s : ℝ) : ℝ := θ0 + s * ℓ - nc * (argGammaHalf (s : ℂ)).re

lemma realPhase_gamma (nc : ℕ) (ℓ θ0 s : ℝ) :
    realPhase (gammaPhase nc ℓ θ0) s = gammaG nc ℓ θ0 s / Real.pi := by
  unfold realPhase gammaPhase gammaG
  rw [Complex.div_ofReal_re]
  simp

lemma continuous_realPhase_gamma (nc : ℕ) (ℓ θ0 : ℝ) : Continuous (realPhase (gammaPhase nc ℓ θ0)) := by
  have hd : ∀ s : ℝ, ContinuousAt (gammaPhase nc ℓ θ0) (s : ℂ) := fun s =>
    (hasDerivAt_gammaPhase nc ℓ θ0 (by simp)).continuousAt
  refine continuous_iff_continuousAt.mpr (fun s => ?_)
  unfold realPhase
  exact Complex.continuous_re.continuousAt.comp ((hd s).comp (f := fun s : ℝ => (s : ℂ))
    Complex.continuous_ofReal.continuousAt)

lemma lsum_bounds (nc : ℕ) {L Fm Fp : ℝ} (hL : 0 < L) (hFm : 0 < Fm) (F : Fin nc → ℝ)
    (hF : ∀ i, Fm ≤ F i ∧ F i ≤ Fp) :
    nc * (Real.log L + Real.log Fm) ≤ lsum nc L F ∧ lsum nc L F ≤ nc * (Real.log L + Real.log Fp) := by
  have hFi : ∀ i, 0 < F i := fun i => lt_of_lt_of_le hFm (hF i).1
  have e : ∀ i, Real.log (L * F i) = Real.log L + Real.log (F i) := fun i =>
    Real.log_mul hL.ne' (hFi i).ne'
  unfold lsum
  simp_rw [e]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor
  · have : (nc : ℝ) * Real.log Fm ≤ ∑ i, Real.log (F i) := by
      calc (nc : ℝ) * Real.log Fm = ∑ _i : Fin nc, Real.log Fm := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => Real.log_le_log hFm (hF i).1)
    linarith
  · have : ∑ i, Real.log (F i) ≤ (nc : ℝ) * Real.log Fp := by
      calc _ ≤ ∑ _i : Fin nc, Real.log Fp :=
            Finset.sum_le_sum (fun i _ => Real.log_le_log (hFi i) (hF i).2)
        _ = _ := by simp
    linarith

/-- Verification of the hypotheses of `calPhase_gamma` for `m = nc log L/(2π)`, `M = 4m`. -/
theorem gamma_calPhase (nc : ℕ) {L Fm Fp cs X θ0 : ℝ} (hnc : 1 ≤ nc) (hL : 1 < L) (hFm : 0 < Fm)
    (F : Fin nc → ℝ) (hF : ∀ i, Fm ≤ F i ∧ F i ≤ Fp) (hcs0 : 0 < cs) (hcs : cs < 1 / 2)
    (hX : L ^ (cs / 2) ≤ X) (hXu : X ≤ L ^ cs)
    (h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L)
    (h2 : Real.log Fp + 3 ≤ Real.log L) :
    CalPhase (gammaPhase nc (lsum nc L F) θ0) X (1 / 4) (nc * Real.log L / (2 * Real.pi))
      (4 * (nc * Real.log L / (2 * Real.pi))) (nc * (16 * invSqSum) / Real.pi) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  have hpi := Real.pi_pos
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hX
  obtain ⟨hlo, hup⟩ := lsum_bounds nc hL0 hFm F hF
  have hLcs : 1 ≤ L ^ cs := Real.one_le_rpow hL.le hcs0.le
  refine calPhase_gamma nc (lsum nc L F) θ0 X _ _ hXpos (by positivity) ?_ ?_
  · have hlog : Real.log (X + 2) ≤ Real.log 3 + cs * Real.log L := by
      have : X + 2 ≤ 3 * L ^ cs := by linarith
      calc Real.log (X + 2) ≤ Real.log (3 * L ^ cs) := Real.log_le_log (by positivity) this
        _ = Real.log 3 + cs * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0]
    have e : Real.pi * (nc * Real.log L / (2 * Real.pi)) = nc * Real.log L / 2 := by field_simp <;> ring
    rw [e]
    have : (nc : ℝ) * (Real.log (X + 2) + 5) + nc * Real.log L / 2 ≤
        nc * (Real.log L + Real.log Fm) := by
      have := mul_le_mul_of_nonneg_left (by linarith : Real.log (X + 2) + 5 + Real.log L / 2 ≤
        Real.log L + Real.log Fm) (by positivity : (0 : ℝ) ≤ nc)
      linarith
    linarith
  · have e : Real.pi * (4 * (nc * Real.log L / (2 * Real.pi))) = 2 * nc * Real.log L := by field_simp <;> ring
    rw [e]
    have : (nc : ℝ) * (Real.log L + Real.log Fp) + 3 * nc ≤ 2 * nc * Real.log L := by
      have := mul_le_mul_of_nonneg_left (by linarith : Real.log Fp + 3 ≤ Real.log L)
        (by positivity : (0 : ℝ) ≤ nc)
      linarith
    linarith

end FormalResearch.Special.Lattice

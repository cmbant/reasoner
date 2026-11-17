module

public import FormalResearch.Special.TraceBlock
public import FormalResearch.Special.TraceAdmissible

/-!
# `thm:tracecore`: the error decomposition (matrix part of the proof)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, proof of `thm:tracecore`.  This module is the part of the
proof that does not involve the phase lattice.  Let `C` be Hermitian with `0 ≤ C ≤ 1`, `U` orthonormal columns
(`Uᴴ U = 1`), `λ_x = ⟨u_x, C u_x⟩` (`blockLam`), `D`, `C'` the block pieces, `ξ_x ∈ ℝ` points (the lattice
`x_r`), `ν_x = ν(2πξ_x)`, `h` admissible, `0 < ρ ≤ 1/8`.  If the eigenvalues `μ` of `C'` satisfy
`μ(1-μ) ≤ ε_op ≤ ρ` (the eigenvalue form of `‖C'(1-C')‖ ≤ ρ`), then

`|Tr h(C) - ∑_x h(ν_x)| ≤ C_h K_ρ [ Tr (C(1-C))^{σ/2} + ∑_x e^{-πσ|ξ_x|} ]`
`                         + Λ₁ [ ‖C - D - C'‖₁ + ∑_x |λ_x - ν_x| ]`

with `K_ρ = (1 + 12/σ)(2ρ)^{5σ/12}`, `Λ₁ = C_h ρ^{σ-1}(1+|log ρ|) + C_h(2ρ)^σ(1+|log ρ|)/ρ`
(`tracecore_decomp`).  The steps are the paper's: `h = h₁ + h₂`; `|Tr h₂(C)| ≤ C_h K_ρ Tr(C(1-C))^{σ/2}`
(small occupations, FM$_σ$); `|Tr h₁(C) - Tr h₁(C₀)| ≤ Λ₁‖C - C₀‖₁` (`traceperturb`), `C₀ = D + C'`;
`Tr h₁(C₀) = ∑_x h₁(λ_x)` (block form, `traceFn_block`, and `h₁ = 0` on the eigenvalues of `C'`);
`|h₁(λ_x) - h₁(ν_x)| ≤ Λ₁|λ_x - ν_x|` (calibration); `|h₂(ν_x)| ≤ C_h K_ρ e^{-πσ|ξ_x|}`.
-/

@[expose] public section

namespace FormalResearch.Special.TraceCore

open Matrix FormalResearch.MatrixAnalysis FormalResearch.Special.Lattice
open scoped ComplexOrder MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Type*} [Fintype s] [DecidableEq s]

theorem tracecore_decomp {σ δ κ Ch : ℝ} {h : ℝ → ℂ} (H : Admissible σ δ κ Ch h) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hCh : 0 ≤ Ch) {ρ : ℝ} (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (hC0 : C.PosSemidef) (hC1 : (1 - C).PosSemidef)
    {U : Matrix ι s ℂ} (hU : Uᴴ * U = 1) (ξ : s → ℝ) {epo : ℝ}
    (hepo : ∀ i, (blockC'_isHermitian hC U).eigenvalues i * (1 - (blockC'_isHermitian hC U).eigenvalues i) ≤ epo)
    (hepoρ : epo ≤ ρ) :
    ‖traceFn h hC - ∑ x, h (nuR (2 * Real.pi * ξ x))‖ ≤
      Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) *
          ((∑ i, ddf (hC.eigenvalues i) ^ (σ / 2)) + ∑ x, Real.exp (-(Real.pi * σ) * |ξ x|)) +
        (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) + Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ)) *
          (tnorm (C - (blockD U (blockLam U C) + blockC' U C)) +
            ∑ x, |blockLam U C x - nuR (2 * Real.pi * ξ x)|) := by
  classical
  set lam := blockLam U C with hlam
  set hB := blockC'_isHermitian hC U with hBdef
  have hlm := fun x => blockLam_mem hU hC0 hC1 x
  set hC0H := (blockD_isHermitian U lam).add hB with hC0Hdef
  have hρ1 : 2 * ρ ≤ 1 := by linarith
  have hρ4 : ρ ≤ 1 / 4 := by linarith
  set Λ : ℝ := Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) + Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ)
    with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set K : ℝ := Ch * ((1 + 12 / σ) * (2 * ρ) ^ (5 * σ / 12)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlip := h1_lipschitz H hσ hσ1 hCh hρ hρ4
  -- spectra of `C` and `C₀` in `[0,1]`
  have hspC : ∀ i, hC.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := eigenvalues_mem_unit hC hC0 hC1
  have hD0 := blockD_psd (U := U) lam (fun x => (hlm x).1)
  have hC0psd : (blockD U lam + blockC' U C).PosSemidef := hD0.add (blockC'_psd U hC0)
  have hC01 := one_sub_block_psd hU lam (fun x => (hlm x).2) hC1
  have hspC0 : ∀ i, hC0H.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := eigenvalues_mem_unit hC0H hC0psd hC01
  -- Step: Lipschitz perturbation for `h₁`
  have hL := traceFn_sub_le_lipschitz hC hC0H hspC hspC0 hΛ0
    (φ := h1fn ρ h) (fun a ha b hb => hlip a ha b hb)
  -- Step: block form
  have hf0 : h1fn ρ h 0 = 0 := h1fn_eq_zero hρ h (by simp [ddf]; exact hρ.le)
  have hblock := traceFn_block hC hU lam (h1fn ρ h) hf0
  -- eigenvalues of `C'` are killed by `h₁`
  have hCp0 : traceFn (h1fn ρ h) hB = 0 := by
    unfold traceFn
    refine Finset.sum_eq_zero fun i _ => ?_
    exact h1fn_eq_zero hρ h ((hepo i).trans hepoρ)
  -- calibration
  have hcal : ‖∑ x, (h1fn ρ h (lam x) - h1fn ρ h (nuR (2 * Real.pi * ξ x)))‖ ≤
      Λ * ∑ x, |lam x - nuR (2 * Real.pi * ξ x)| := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hn := nuR_mem (2 * Real.pi * ξ x)
    exact hlip _ ⟨(hlm x).1, (hlm x).2⟩ _ ⟨hn.1, hn.2⟩
  -- small occupations
  have hsmall : ‖traceFn (h2fn ρ h) hC‖ ≤ K * ∑ i, ddf (hC.eigenvalues i) ^ (σ / 2) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact h2fn_bound H hσ hCh hρ hρ1 (hspC i)
  have hsmall2 : ‖∑ x, h2fn ρ h (nuR (2 * Real.pi * ξ x))‖ ≤
      K * ∑ x, Real.exp (-(Real.pi * σ) * |ξ x|) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hn := nuR_mem (2 * Real.pi * ξ x)
    refine (h2fn_bound H hσ hCh hρ hρ1 ⟨hn.1, hn.2⟩).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have h1 := dd_nuR_le (ξ x)
    have h2 : ddf (nuR (2 * Real.pi * ξ x)) ^ (σ / 2) ≤
        Real.exp (-(2 * Real.pi) * |ξ x|) ^ (σ / 2) :=
      Real.rpow_le_rpow (ddf_nonneg ⟨hn.1, hn.2⟩) h1 (by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.exp_mul]; congr 1; ring
  -- assemble
  have hsplit1 : traceFn h hC = traceFn (h1fn ρ h) hC + traceFn (h2fn ρ h) hC := by
    unfold traceFn
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [h2fn]
  have hsplit2 : ∑ x, h (nuR (2 * Real.pi * ξ x)) =
      ∑ x, h1fn ρ h (nuR (2 * Real.pi * ξ x)) + ∑ x, h2fn ρ h (nuR (2 * Real.pi * ξ x)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by simp [h2fn]
  rw [hCp0, add_zero] at hblock
  have e : traceFn h hC - ∑ x, h (nuR (2 * Real.pi * ξ x)) =
      (traceFn (h1fn ρ h) hC - traceFn (h1fn ρ h) hC0H) +
        ∑ x, (h1fn ρ h (lam x) - h1fn ρ h (nuR (2 * Real.pi * ξ x))) +
        traceFn (h2fn ρ h) hC - ∑ x, h2fn ρ h (nuR (2 * Real.pi * ξ x)) := by
    rw [hsplit1, hsplit2, hblock, Finset.sum_sub_distrib]; ring
  rw [e]
  have b1 := norm_add_le ((traceFn (h1fn ρ h) hC - traceFn (h1fn ρ h) hC0H) +
        ∑ x, (h1fn ρ h (lam x) - h1fn ρ h (nuR (2 * Real.pi * ξ x))) + traceFn (h2fn ρ h) hC)
    (-(∑ x, h2fn ρ h (nuR (2 * Real.pi * ξ x))))
  have b2 := norm_add_le ((traceFn (h1fn ρ h) hC - traceFn (h1fn ρ h) hC0H) +
        ∑ x, (h1fn ρ h (lam x) - h1fn ρ h (nuR (2 * Real.pi * ξ x)))) (traceFn (h2fn ρ h) hC)
  have b3 := norm_add_le (traceFn (h1fn ρ h) hC - traceFn (h1fn ρ h) hC0H)
    (∑ x, (h1fn ρ h (lam x) - h1fn ρ h (nuR (2 * Real.pi * ξ x))))
  rw [norm_neg] at b1
  rw [sub_eq_add_neg]
  have hΛt : Λ * (tnorm (C - (blockD U lam + blockC' U C)) + ∑ x, |lam x - nuR (2 * Real.pi * ξ x)|) =
      Λ * tnorm (C - (blockD U lam + blockC' U C)) + Λ * ∑ x, |lam x - nuR (2 * Real.pi * ξ x)| := by ring
  have hKt : K * ((∑ i, ddf (hC.eigenvalues i) ^ (σ / 2)) + ∑ x, Real.exp (-(Real.pi * σ) * |ξ x|)) =
      K * ∑ i, ddf (hC.eigenvalues i) ^ (σ / 2) + K * ∑ x, Real.exp (-(Real.pi * σ) * |ξ x|) := by ring
  rw [hΛt, hKt]
  linarith

/-- info: 'FormalResearch.Special.TraceCore.tracecore_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tracecore_decomp

end FormalResearch.Special.TraceCore

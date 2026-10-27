import FormalResearch.FrameFree.PsiPlusKramersCore
import FormalResearch.FrameFree.Reversals
import FormalResearch.FrameFree.HelstromSupport

/-!
# `ψ₊` is calibrated: `F_C(ψ₊) = F_K(ψ₊) = 1/2` (Paper P, `thm:psipluskramers`)

Namespace `FormalResearch.FrameFree.PsiPlusKramers`.  `ψ₊` is realised as `psiPlus = ψ_{U_{π/4}}`, the Choi
state of `√SWAP`, the `θ = π/4` case of the exchange law (`Sharing.psiEx`); it is `ψ₊` after exchanging
spins `2` and `4`, a relabelling under which `F_K` and `F_C` are invariant.

* `reduce_filters`, `ov_nsq`: the four `SL(2,ℂ)` filters reduce to three matrices `A, B, E`
  (`SWAP` commutes with `a ⊗ a`), overlap `= tr(V Z)/8`, norm `= ‖Z‖²/8`, `Z = (A ⊗ B) V (1 ⊗ E)`.
* `ratio_le_half`: with `PsiPlusKramersCore.core_ineq` (`|tr(V Z)|² ≤ 4‖Z‖²`) every filter ratio is `≤ 1/2`.
* `exchangeIndepBoundC_pi4`, `exchangeIndepBound_pi4`: the two recalled hypotheses
  `Sharing.ExchangeIndepBound(C) (π/4)` of `Reversals.exchange_pi4` are **proved**.
* `psiplus_kramers`: `F_C(ψ₊) = F_K(ψ₊) = 1/2`; `psiplus_calibrated`; `psiplus_CK`: `C_K = log 2`.
* `psiplus_xi_inv`: `ξ_inv(ψ₊) = log 2`, conditional on `Helstrom.SupportRateUpper`; that hypothesis is now
  a theorem (`PolyImageDischarge`), and `XiInv.psiplus_xi_inv'` (`XiInvUnconditional`) is the unconditional form.
* `Phi8_values'`, `eight_qubit_reversal''`: `Reversals.Phi8_values` and
  `Reversals.eight_qubit_reversal` with the `π/4` hypotheses discharged.

Nothing in `Sharing`, `Reversals` or `RealRep3Discharge` is edited.
-/

open scoped Matrix ComplexConjugate Kronecker Real
open FormalResearch.FrameFree.Sharing FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.PsiPlusKramers

theorem Vg_comm_kron_self (a : Op1) : Vg * (a ⊗ₖ a) = (a ⊗ₖ a) * Vg := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Vg, Ug, Sw, Matrix.mul_apply, Matrix.add_apply, 
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.kroneckerMap_apply] <;> ring

/-- The three-filter reduction: the four `SL(2,ℂ)` filters act on `√SWAP` through the three matrices
`A = u₀ u₂⁻¹`, `B = u₁ u₂⁻¹`, `E = u₂ u₃⁻¹`, because `SWAP` commutes with `a ⊗ a`. -/
theorem reduce_filters (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1) :
    (u 0 ⊗ₖ u 1) * Vg * ((u 2).adjugate ⊗ₖ (u 3).adjugate) =
      Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate) (u 2 * (u 3).adjugate) := by
  have h2 : (u 2).adjugate * u 2 = 1 := by rw [Matrix.adjugate_mul, hu 2]; simp
  have e : ((u 2).adjugate ⊗ₖ (u 3).adjugate) =
      ((u 2).adjugate ⊗ₖ (u 2).adjugate) * ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [e]
  unfold Zm
  calc (u 0 ⊗ₖ u 1) * Vg * (((u 2).adjugate ⊗ₖ (u 2).adjugate) * ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)))
      = (u 0 ⊗ₖ u 1) * (Vg * ((u 2).adjugate ⊗ₖ (u 2).adjugate)) *
          ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by simp only [Matrix.mul_assoc]
    _ = ((u 0 ⊗ₖ u 1) * ((u 2).adjugate ⊗ₖ (u 2).adjugate)) * Vg *
          ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by
        rw [Vg_comm_kron_self]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.mul_kronecker_mul]

theorem cos_pi4_sq : Real.cos (π / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_sq, show 2 * (π / 4) = π / 2 by ring, Real.cos_pi_div_two]; norm_num

theorem sin_pi4 : Real.sin (π / 4) = Real.cos (π / 4) := by
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]

theorem Ug_pi4 : Ug (Real.cos (π / 4) : ℂ) (Complex.I * (Real.sin (π / 4) : ℝ)) =
    (Real.cos (π / 4) : ℂ) • Vg := by
  rw [sin_pi4, Vg, Ug, Ug, smul_add, smul_smul, smul_smul]
  simp [mul_comm]

/-- The overlap and norm of the rotated `√SWAP` probe, in terms of `Z`. -/
theorem ov_nsq (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1) :
    NQubit.ip (psiEx (π / 4)) (NQubit.rot u (psiEx (-(π / 4)))) =
        (1 / 8 : ℂ) * Matrix.trace (Vg * Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate)) ∧
      ((NQubit.nsq (NQubit.rot u (psiEx (-(π / 4)))) : ℝ) : ℂ) =
        (1 / 8 : ℂ) * Matrix.trace ((Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate))ᴴ * Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate)) := by
  have hc2 : ((Real.cos (π / 4) : ℝ) : ℂ) * ((Real.cos (π / 4) : ℝ) : ℂ) = 1 / 2 := by
    have h := cos_pi4_sq
    have : Real.cos (π / 4) * Real.cos (π / 4) = 1 / 2 := by nlinarith
    have := congrArg (fun x : ℝ => (x : ℂ)) this
    simpa using this
  have hM : (u 0 ⊗ₖ u 1) * Uex (-(π / 4)) * ((u 2).adjugate ⊗ₖ (u 3).adjugate) =
      (Real.cos (π / 4) : ℂ) • Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate) := by
    rw [Uex_neg, Ug_pi4]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [reduce_filters u hu]
  constructor
  · unfold psiEx
    rw [rot_choi, ip_choi, Uex_conjT, hM, Ug_pi4]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    linear_combination (Matrix.trace (Vg * Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
      (u 2 * (u 3).adjugate)) / 4) * hc2
  · rw [← NQubit.ip_self]
    unfold psiEx
    rw [rot_choi, ip_choi]
    have hMc : ((u 0 ⊗ₖ u 1) * Uex (-(π / 4)) * ((u 2).adjugate ⊗ₖ (u 3).adjugate))ᴴ =
        (Real.cos (π / 4) : ℂ) • (Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate))ᴴ := by
      rw [hM, Matrix.conjTranspose_smul]
      simp
    rw [hMc, hM]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    linear_combination (Matrix.trace ((Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate))ᴴ * Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate)
          (u 2 * (u 3).adjugate)) / 4) * hc2

/-- Every filter ratio for `ψ_{U_{π/4}}` against `Θψ = ψ_{U_{-π/4}}` is at most `1/2`. -/
theorem ratio_le_half (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1) :
    Complex.normSq (NQubit.ip (psiEx (π / 4)) (NQubit.rot u (psiEx (-(π / 4))))) /
      NQubit.nsq (NQubit.rot u (psiEx (-(π / 4)))) ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := ov_nsq u hu
  have hcore := core_ineq (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate) (u 2 * (u 3).adjugate)
  set Z := Zm (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate) (u 2 * (u 3).adjugate) with hZ
  have hn : NQubit.nsq (NQubit.rot u (psiEx (-(π / 4)))) = (1 / 8) * (Matrix.trace (Zᴴ * Z)).re := by
    have := congrArg Complex.re h2
    simpa [Complex.mul_re] using this
  have ho : Complex.normSq (NQubit.ip (psiEx (π / 4)) (NQubit.rot u (psiEx (-(π / 4))))) =
      (1 / 64) * Complex.normSq (Matrix.trace (Vg * Z)) := by
    rw [h1, Complex.normSq_mul]
    have : Complex.normSq (1 / 8 : ℂ) = 1 / 64 := by simp; norm_num
    rw [this]
  rcases (Sharing.nsq_nonneg (NQubit.rot u (psiEx (-(π / 4))))).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · rw [div_le_iff₀ hpos, ho, hn]
    nlinarith

/-- **`F_C(ψ₊) ≤ 1/2`, independent frames** (`ExchangeIndepBoundC (π/4)`), proved. -/
theorem exchangeIndepBoundC_pi4 : Sharing.ExchangeIndepBoundC (π / 4) := by
  unfold Sharing.ExchangeIndepBoundC Sharing.FCΘs Sharing.FCs
  rw [Sharing.Θ_psiEx, cos_pi4_sq]
  refine csSup_le (Sharing.fiSet_nonempty _ _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  exact ratio_le_half (fun i => v (id i)) (fun i => hv _)

/-- **`F_K(ψ₊) ≤ 1/2`, independent frames** (`ExchangeIndepBound (π/4)`), proved: rotations are filters. -/
theorem exchangeIndepBound_pi4 : Sharing.ExchangeIndepBound (π / 4) := by
  unfold Sharing.ExchangeIndepBound
  calc FKΘ (psiEx (π / 4)) = Sharing.FKs (id : Fin 4 → Fin 4) (psiEx (π / 4)) (Θ (psiEx (π / 4))) :=
        (Sharing.FKs_id _ _).symm
    _ ≤ Sharing.FCs (id : Fin 4 → Fin 4) (psiEx (π / 4)) (Θ (psiEx (π / 4))) :=
        Sharing.FKs_le_FCs _ _ _ (by rw [NQubit.nsq_Θ, Sharing.nsq_psiEx])
    _ ≤ Real.cos (π / 4) ^ 2 := exchangeIndepBoundC_pi4

/-! ### Paper P, `thm:psipluskramers` -/

/-- `ψ₊`, realised as the Choi probe of `√SWAP`: `ψ_{U_{π/4}}`.  (The four-spin state `ψ₊` is this
state after exchanging spins `2` and `4`; `F_K` and `F_C` are invariant under the relabelling.) -/
noncomputable abbrev psiPlus : Ψ 4 := psiEx (π / 4)

/-- **`thm:psipluskramers`, values.**  `F_C(ψ₊) = F_K(ψ₊) = 1/2`, unconditionally. -/
theorem psiplus_kramers : Ceilings.FCΘ psiPlus = 1 / 2 ∧ FKΘ psiPlus = 1 / 2 :=
  Reversals.exchange_pi4 exchangeIndepBound_pi4 exchangeIndepBoundC_pi4

/-- `ψ₊` is calibrated: `F_C(ψ₊) = F_K(ψ₊)`. -/
theorem psiplus_calibrated : Ceilings.FCΘ psiPlus = FKΘ psiPlus := by
  rw [psiplus_kramers.1, psiplus_kramers.2]

/-- `C_K(ψ₊) = -log F_K(ψ₊) = log 2`. -/
theorem psiplus_CK : CK psiPlus = Real.log 2 := by
  unfold CK
  rw [psiplus_kramers.2, Real.log_div (by norm_num) (by norm_num)]
  simp

/-- **`thm:psipluskramers`, rate** (given the upper half of the support rate, `thm:supportrate`, as a
hypothesis, now a theorem: see `XiInv.psiplus_xi_inv'` for the unconditional form): `-(1/k) log P_e(k) → log 2 = C_K(ψ₊) = -log F_C(ψ₊)`, i.e. `ξ_inv(ψ₊) = log 2`. -/
theorem psiplus_xi_inv (hsr : Helstrom.SupportRateUpper psiPlus) :
    Filter.Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Helstrom.Pe k psiPlus)) Filter.atTop
      (nhds (Real.log 2)) := by
  have h := Helstrom.tendsto_of_calibrated psiPlus (Sharing.nsq_psiEx _) hsr psiplus_calibrated
  rwa [psiplus_CK] at h

/-- `Reversals.Phi8_values` with its two hypotheses discharged. -/
theorem Phi8_values' :
    CK Reversals.Phi8 = Real.log 4 ∧ -Real.log (Ceilings.FCΘ Reversals.Phi8) = Real.log 4 :=
  Reversals.Phi8_values exchangeIndepBound_pi4 exchangeIndepBoundC_pi4

/-- `Reversals.eight_qubit_reversal` without the two `π/4` hypotheses (`hK4`, `hC4`). -/
theorem eight_qubit_reversal'' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4)
    (hK : Sharing.ExchangeIndepBound θ) (hC : Sharing.ExchangeIndepBoundC θ)
    (hs0 : 0 < Real.cos (2 * θ)) (hs1 : Real.cos (2 * θ) < 1 / 8) :
    Reversals.StrictReversal (CK (Reversals.Psi8 θ)) (-Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)))
        (CK Reversals.Phi8) (-Real.log (Ceilings.FCΘ Reversals.Phi8)) ∧
      CK (Reversals.Psi8 θ) = Real.log (9 / (2 * (1 + Real.cos (2 * θ)))) ∧
      -Real.log (Ceilings.FCΘ (Reversals.Psi8 θ)) = Real.log (4 / (1 + Real.cos (2 * θ))) :=
  Reversals.eight_qubit_reversal h49 h0 h1 hK hC exchangeIndepBound_pi4
    exchangeIndepBoundC_pi4 hs0 hs1

end FormalResearch.FrameFree.PsiPlusKramers

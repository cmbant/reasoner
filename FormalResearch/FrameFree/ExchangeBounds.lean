import FormalResearch.FrameFree.ExchangeBoundsCartan

/-!
# The independent-frame exchange bounds (`thm:heis`, recalled (R8)): proved

`Sharing.ExchangeIndepBoundC θ : F_C^{1|2|3|4}(ψ_{U_θ}) ≤ cos² θ` and
`Sharing.ExchangeIndepBound θ : F_K(ψ_{U_θ}) ≤ cos² θ` hold for every `θ` with `cos 2θ ≥ 0`
(in particular `0 ≤ θ ≤ π/4`; they fail for `cos 2θ < 0`, e.g. `θ = π/2`, where `F = sin² θ`).

Proof (the paper's proof of `thm:heis`, route QI-B `cor:ftg`):
* `reduce_gate`: for `u i ∈ SL(2,ℂ)` and `G = C + S·SWAP` (which commutes with `a ⊗ a`),
  `(u₀⊗u₁) G (adj u₂ ⊗ adj u₃) = (A ⊗ B) G (1 ⊗ E)`, `A = u₀ adj u₂`, `B = u₁ adj u₂`, `E = u₂ adj u₃`;
* `trace_sq_le`: `|tr[G (A⊗B) G (1⊗E)]|² ≤ 2 (1 + cos 2θ) ‖(A⊗B) G (1⊗E)‖²_F` for `G = U_{-θ}`, from
  `FTG.filtered_gate_law` (`W = 1`), via `FTG_Ug_iso`
  (`FTG.Ug (x,x,x) = e^{ix} (cos 2x - i sin 2x SWAP)`, so `c = (-θ/2)^3`, `dl c = |cos 2θ|`);
* `ratio_le`: with `ip_choi`, `rot_choi` every filter ratio is `≤ (1 + cos 2θ)/2 = cos² θ`.
  The filter set is over `SL(2,ℂ)` (all invertible), so no singular filters need a density argument.

Convention check: the paper's `Ũ = U^{-1}` is `Uex (-θ)` and the Cartan coordinates are `-(t,t,t)`, `θ = 2t`
(up to the global phase `e^{ix}`, which drops out of ratios).  No mismatch was found.
-/

open scoped Matrix ComplexConjugate Kronecker Real
open FormalResearch.FrameFree.Sharing FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.ExchangeBounds

theorem Sw_comm_kron_self (a : Op1) : Sw * (a ⊗ₖ a) = (a ⊗ₖ a) * Sw := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Sw, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply] <;> ring

theorem Ug_comm_kron_self (C S : ℂ) (a : Op1) : Ug C S * (a ⊗ₖ a) = (a ⊗ₖ a) * Ug C S := by
  unfold Ug
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Sw_comm_kron_self, Matrix.one_mul, Matrix.mul_one]

/-- The three-filter reduction for a general exchange gate `G = C + S·SWAP`. -/
theorem reduce_gate (C S : ℂ) (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1) :
    (u 0 ⊗ₖ u 1) * Ug C S * ((u 2).adjugate ⊗ₖ (u 3).adjugate) =
      ((u 0 * (u 2).adjugate) ⊗ₖ (u 1 * (u 2).adjugate)) * Ug C S *
        ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by
  have h2 : (u 2).adjugate * u 2 = 1 := by rw [Matrix.adjugate_mul, hu 2]; simp
  have e : ((u 2).adjugate ⊗ₖ (u 3).adjugate) =
      ((u 2).adjugate ⊗ₖ (u 2).adjugate) * ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [e]
  calc (u 0 ⊗ₖ u 1) * Ug C S * (((u 2).adjugate ⊗ₖ (u 2).adjugate) * ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)))
      = (u 0 ⊗ₖ u 1) * (Ug C S * ((u 2).adjugate ⊗ₖ (u 2).adjugate)) *
          ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by simp only [Matrix.mul_assoc]
    _ = ((u 0 ⊗ₖ u 1) * ((u 2).adjugate ⊗ₖ (u 2).adjugate)) * Ug C S *
          ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) := by
        rw [Ug_comm_kron_self]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.mul_kronecker_mul]

/-- The exchange gate `U_{-θ} = cos θ + i sin θ SWAP`. -/
noncomputable abbrev Gx (θ : ℝ) : Mat4 := Ug (Real.cos θ : ℝ) (Complex.I * (Real.sin θ : ℝ))

/-- `FTG.Ug (-θ/2, -θ/2, -θ/2) = e^{-iθ/2} U_{-θ}`. -/
theorem FTG_Ug_Gx (θ : ℝ) :
    FTG.Ug (fun _ => -θ / 2) =
      ((Real.cos (-θ / 2) : ℂ) + Complex.I * (Real.sin (-θ / 2) : ℂ)) • Gx θ := by
  rw [FTG_Ug_iso]
  have e : 2 * (-θ / 2) = -θ := by ring
  rw [e, Real.cos_neg, Real.sin_neg]
  unfold Gx
  push_cast
  simp

theorem normSq_phase (x : ℝ) : Complex.normSq ((Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ)) = 1 := by
  rw [show ((Real.cos x : ℝ) : ℂ) + Complex.I * (Real.sin x : ℂ) =
    ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I by ring,
    Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq]

/-- The Frobenius norm squared of a matrix. -/
noncomputable abbrev fro (M : Mat4) : ℝ := (Matrix.trace (Mᴴ * M)).re

/-- **Matrix form of `F_C(ψ_{U_θ}) ≤ cos² θ`** (QI-B `cor:ftg` for `W = 1`):
`|tr[G (A⊗B) G (1⊗E)]|² ≤ 2 (1 + cos 2θ) ‖(A⊗B) G (1⊗E)‖_F²`, `G = U_{-θ}`, when `cos 2θ ≥ 0`. -/
theorem trace_sq_le {θ : ℝ} (hθ : 0 ≤ Real.cos (2 * θ)) (A B E : Op1) :
    Complex.normSq (Matrix.trace (Gx θ * ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E)))) ≤
      2 * (1 + Real.cos (2 * θ)) * fro ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E)) := by
  set ω : ℂ := (Real.cos (-θ / 2) : ℂ) + Complex.I * (Real.sin (-θ / 2) : ℂ) with hω
  have hω1 : Complex.normSq ω = 1 := normSq_phase _
  have hωc : star ω * ω = 1 := by
    have := Complex.normSq_eq_conj_mul_self (z := ω)
    rw [hω1] at this
    simpa using this.symm
  have hdl : FTG.dl (fun _ => -θ / 2) = Real.cos (2 * θ) := by
    unfold FTG.dl
    simp only [max_self]
    rw [show 4 * (-θ / 2) = -(2 * θ) by ring, Real.cos_neg, abs_of_nonneg hθ]
  have law := FTG.filtered_gate_law (fun _ => -θ / 2) A B E 1 (by simp)
  rw [hdl, FTG_Ug_Gx] at law
  have e1 : FTG.kr 1 E = (1 : Op1) ⊗ₖ E := rfl
  have e2 : FTG.kr A B = A ⊗ₖ B := rfl
  rw [e1, e2] at law
  have t1 : ((ω • Gx θ) * (A ⊗ₖ B) * (ω • Gx θ) * ((1 : Op1) ⊗ₖ E)) =
      (ω * ω) • (Gx θ * ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E))) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  have t2 : ((A ⊗ₖ B) * (ω • Gx θ) * ((1 : Op1) ⊗ₖ E)) =
      ω • ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [t1, t2, Matrix.trace_smul, smul_eq_mul] at law
  have hn : ‖ω * ω‖ = 1 := by
    have h1 : ‖ω‖ = 1 := by
      have := Complex.sq_norm ω
      rw [hω1] at this
      nlinarith [norm_nonneg ω]
    rw [norm_mul, h1]; norm_num
  have hf : FTG.fro2 (ω • ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E))) =
      fro ((A ⊗ₖ B) * Gx θ * ((1 : Op1) ⊗ₖ E)) := by
    unfold FTG.fro2 fro
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hωc]
    simp
  rw [hf, norm_mul, hn, one_mul] at law
  rwa [Complex.sq_norm] at law

/-- Every filter ratio of `ψ_{U_θ}` against `ψ_{U_{-θ}} = Θ ψ_{U_θ}` is at most `(1 + cos 2θ)/2`. -/
theorem ratio_le {θ : ℝ} (hθ : 0 ≤ Real.cos (2 * θ)) (u : Fin 4 → Op1) (hu : ∀ i, (u i).det = 1) :
    Complex.normSq (NQubit.ip (psiEx θ) (rot u (psiEx (-θ)))) / NQubit.nsq (rot u (psiEx (-θ))) ≤
      (1 + Real.cos (2 * θ)) / 2 := by
  set M : Mat4 := ((u 0 * (u 2).adjugate) ⊗ₖ (u 1 * (u 2).adjugate)) * Gx θ *
    ((1 : Op1) ⊗ₖ (u 2 * (u 3).adjugate)) with hM
  have hrot : rot u (psiEx (-θ)) = choi M := by
    unfold psiEx
    rw [rot_choi, Uex_neg, hM]
    exact congrArg choi (reduce_gate _ _ u hu)
  have hip : NQubit.ip (psiEx θ) (rot u (psiEx (-θ))) = (1 / 4 : ℂ) * Matrix.trace (Gx θ * M) := by
    rw [hrot]
    unfold psiEx
    rw [ip_choi, Uex_conjT]
  have hns : ((NQubit.nsq (rot u (psiEx (-θ))) : ℝ) : ℂ) = (1 / 4 : ℂ) * Matrix.trace (Mᴴ * M) := by
    rw [← NQubit.ip_self, hrot, ip_choi]
  have hn : NQubit.nsq (rot u (psiEx (-θ))) = (1 / 4) * fro M := by
    have := congrArg Complex.re hns
    simpa [Complex.mul_re, fro] using this
  have ho : Complex.normSq (NQubit.ip (psiEx θ) (rot u (psiEx (-θ)))) =
      (1 / 16) * Complex.normSq (Matrix.trace (Gx θ * M)) := by
    rw [hip, Complex.normSq_mul]
    have : Complex.normSq (1 / 4 : ℂ) = 1 / 16 := by simp; norm_num
    rw [this]
  have hk := trace_sq_le hθ (u 0 * (u 2).adjugate) (u 1 * (u 2).adjugate) (u 2 * (u 3).adjugate)
  rw [← hM] at hk
  rcases (Sharing.nsq_nonneg (rot u (psiEx (-θ)))).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; linarith
  · rw [div_le_iff₀ hpos, ho, hn]
    rw [hn] at hpos
    nlinarith

/-- **`ExchangeIndepBoundC θ`, proved** whenever `cos 2θ ≥ 0`: `F_C^{1|2|3|4}(ψ_{U_θ}) ≤ cos² θ`. -/
theorem exchangeIndepBoundC_of_cos {θ : ℝ} (hθ : 0 ≤ Real.cos (2 * θ)) :
    ExchangeIndepBoundC θ := by
  unfold ExchangeIndepBoundC FCΘs FCs
  rw [Θ_psiEx]
  have hc : Real.cos θ ^ 2 = (1 + Real.cos (2 * θ)) / 2 := by rw [Real.cos_sq θ]; ring
  rw [hc]
  refine csSup_le (fiSet_nonempty _ _ _) ?_
  rintro r ⟨v, hv, rfl⟩
  exact ratio_le hθ (fun i => v (id i)) (fun i => hv _)

/-- **`ExchangeIndepBoundC θ`, proved** for `0 ≤ θ ≤ π/4`. -/
theorem exchangeIndepBoundC (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) : ExchangeIndepBoundC θ :=
  exchangeIndepBoundC_of_cos (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)

/-- **`ExchangeIndepBound θ`, proved** whenever `cos 2θ ≥ 0` (`F_K ≤ F_C`, rotations are filters). -/
theorem exchangeIndepBound_of_cos {θ : ℝ} (hθ : 0 ≤ Real.cos (2 * θ)) : ExchangeIndepBound θ := by
  unfold ExchangeIndepBound
  calc FKΘ (psiEx θ) = FKs (id : Fin 4 → Fin 4) (psiEx θ) (Θ (psiEx θ)) := (FKs_id _ _).symm
    _ ≤ FCs (id : Fin 4 → Fin 4) (psiEx θ) (Θ (psiEx θ)) :=
        FKs_le_FCs _ _ _ (by rw [nsq_Θ, nsq_psiEx])
    _ ≤ Real.cos θ ^ 2 := exchangeIndepBoundC_of_cos hθ

/-- **`ExchangeIndepBound θ`, proved** for `0 ≤ θ ≤ π/4`. -/
theorem exchangeIndepBound (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) : ExchangeIndepBound θ :=
  exchangeIndepBound_of_cos (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)

end FormalResearch.FrameFree.ExchangeBounds

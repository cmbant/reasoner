import FormalResearch.FrameFree.ExchangeBounds

/-!
# Exchange gates under frame sharing (`thm:exchangesharing` (ii), (iii) and the `√SWAP` row)

Namespace `FormalResearch.FrameFree.Sharing`.  Claim class: **proved** for `0 ≤ θ ≤ π/4`.  The upper bounds
come from the independent-frame exchange bounds `ExchangeBounds.exchangeIndepBound(C)` (the filtered-gate law);
the lower bounds and case (i) are in `Sharing`.  Case (iii) is open in the paper; only its bounds are stated.
-/

open scoped Matrix ComplexConjugate Kronecker Real
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.Sharing

variable {β : Type*}

/-- **Theorem `thm:exchangesharing` (ii)**, rotation overlap.
If only the pairs `{1,3},{2,4}` share (four patterns, independent frames among them),
`F_K^π = cos² θ`. -/
theorem FKΘs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) : FKΘs g (psiEx θ) = Real.cos θ ^ 2 := by
  refine le_antisymm ?_ (cos_sq_le_FKΘs g h θ)
  exact (FKs_le_FK g _ _).trans (ExchangeBounds.exchangeIndepBound θ h0 h1)

/-- **Theorem `thm:exchangesharing` (iii)**, rotation overlap.
If only the cross pairs `{1,4},{2,3}` share (three patterns),
`max(sin²θ, κ) ≤ F_K^π ≤ cos²θ`. -/
theorem FKΘs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FKΘs g (psiEx θ) ∧ FKΘs g (psiEx θ) ≤ Real.cos θ ^ 2 :=
  ⟨max_le (sin_sq_le_FKΘs g h θ) (kappa_le_FKΘs g θ),
    (FKs_le_FK g _ _).trans (ExchangeBounds.exchangeIndepBound θ h0 h1)⟩

/-- **Theorem `thm:exchangesharing` (ii)**, chiral distance: `C_K^π = -log cos² θ
= log (2/(1+cos 2θ))`. -/
theorem CKs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    CKs g (psiEx θ) = Real.log (2 / (1 + Real.cos (2 * θ))) := by
  unfold CKs
  rw [FKΘs_exchange_ii g h θ h0 h1, ← Real.log_inv, Real.cos_two_mul]
  congr 1
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · field_simp
    ring

/-- **Theorem `thm:exchangesharing` (iii)**, chiral distance:
`log (2/(1+cos 2θ)) ≤ C_K^π ≤ -log max(sin²θ, κ)`. -/
theorem CKs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    Real.log (2 / (1 + Real.cos (2 * θ))) ≤ CKs g (psiEx θ) ∧
      CKs g (psiEx θ) ≤ -Real.log (max (Real.sin θ ^ 2) (kappa θ)) := by
  obtain ⟨h1, h2⟩ := FKΘs_exchange_iii g h θ h0 h1
  have hk := kappa_pos θ
  have hpos : 0 < max (Real.sin θ ^ 2) (kappa θ) := lt_of_lt_of_le hk (le_max_right _ _)
  have hF : 0 < FKΘs g (psiEx θ) := lt_of_lt_of_le hpos h1
  have hcos : 0 < Real.cos θ ^ 2 := lt_of_lt_of_le hF h2
  have hc : Real.cos θ ≠ 0 := by
    intro h0; rw [h0] at hcos; simp at hcos
  constructor
  · have e : Real.log (2 / (1 + Real.cos (2 * θ))) = -Real.log (Real.cos θ ^ 2) := by
      rw [← Real.log_inv, Real.cos_two_mul]
      congr 1
      field_simp
      ring
    rw [e]
    unfold CKs
    have := Real.log_le_log hF h2
    linarith
  · unfold CKs
    have := Real.log_le_log hpos h1
    linarith

/-- **`√SWAP`, every pattern** (`thm:exchangesharing`, last sentence), rotation form: `C_K^π = log 4` if
spins `1,2` or `3,4` share a frame and `log 2` for every other pattern. -/
theorem CKs_sqrtSwap (g : Fin 4 → β) :
    ((g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 4) ∧
    (¬ (g 0 = g 1 ∨ g 2 = g 3) → CKs g (psiEx (Real.pi / 4)) = Real.log 2) := by
  have hcos : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsin : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  constructor
  · intro h
    unfold CKs
    rw [FKΘs_exchange_i g h, kappa_quarter, show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      Real.log_inv, neg_neg]
  · intro h
    have hF : FKΘs g (psiEx (Real.pi / 4)) = 1 / 2 := by
      rcases pattern_trichotomy g with h' | h' | h'
      · exact absurd h' h
      · rw [FKΘs_exchange_ii g h' (Real.pi / 4) (by positivity) le_rfl, hcos]
      · obtain ⟨h1, h2⟩ := FKΘs_exchange_iii g h' (Real.pi / 4) (by positivity) le_rfl
        rw [hcos] at h2
        have : (1 / 2 : ℝ) ≤ max (Real.sin (Real.pi / 4) ^ 2) (kappa (Real.pi / 4)) := by
          rw [hsin]; exact le_max_left _ _
        linarith
    unfold CKs
    rw [hF, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg]

/-- **Theorem `thm:exchangesharing` (ii)**, filters:
`F_C^π = cos² θ` for the four patterns inside `{13|24}`. -/
theorem FCΘs_exchange_ii (g : Fin 4 → β) (h : Refines g pat1324) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) : FCΘs g (psiEx θ) = Real.cos θ ^ 2 := by
  refine le_antisymm ?_ ?_
  · exact (FCs_mono (id_refines g) _ _).trans (ExchangeBounds.exchangeIndepBoundC θ h0 h1)
  · exact (cos_sq_le_FKΘs g h θ).trans
      (FKs_le_FCs g (psiEx θ) (Θ (psiEx θ)) (by rw [nsq_Θ, nsq_psiEx]))

/-- **Theorem `thm:exchangesharing` (iii)**, filters:
`max(sin²θ, κ) ≤ F_C^π ≤ cos²θ` for the three cross patterns. -/
theorem FCΘs_exchange_iii (g : Fin 4 → β) (h : Refines g pat1423) (θ : ℝ)
    (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    max (Real.sin θ ^ 2) (kappa θ) ≤ FCΘs g (psiEx θ) ∧ FCΘs g (psiEx θ) ≤ Real.cos θ ^ 2 := by
  have hle : FKΘs g (psiEx θ) ≤ FCΘs g (psiEx θ) :=
    FKs_le_FCs g (psiEx θ) (Θ (psiEx θ)) (by rw [nsq_Θ, nsq_psiEx])
  exact ⟨((max_le (sin_sq_le_FKΘs g h θ) (kappa_le_FKΘs g θ)).trans hle),
    (FCs_mono (id_refines g) _ _).trans (ExchangeBounds.exchangeIndepBoundC θ h0 h1)⟩

end FormalResearch.FrameFree.Sharing

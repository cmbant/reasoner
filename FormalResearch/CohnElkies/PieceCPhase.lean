module

public import FormalResearch.CohnElkies.PieceCDecomposition
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# Phase bounds `u1c:psibd` for the cut-off main term

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1c:U3`(3), Piece C, `(u1c:psibd)`:
for `ψ(v) = c Φ_Ph(εv; L)` (`pcPhase`) and `|εv| ≤ τ_*(L)`,
`ψ' ≥ A/2`, `|ψ''| ≤ min(π²|v|/6, c^{2/3}/|v|)`, `|ψ'''| ≤ π²/3`, with `A = c ε L`.

* `pcPhase_eq`: `pcPhase c ξ v = c · edgePhi L (εv)`;
* `hasDerivAt_edgePhiDeriv2_of_ne`: `Φ''' = edgePhiDeriv3` off `0`;
* `deriv_pcPhase`, `deriv2_pcPhase`, `deriv3_pcPhase`: derivative formulas;
* `pcPhase_psibd`: the three bounds.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.CohnElkies

/-- `Φ'' ` has derivative `Φ'''` away from `0` (`Φ''(τ) = π/sinh(πτ) - 1/τ`). -/
lemma hasDerivAt_edgePhiDeriv2_of_ne {τ : ℝ} (hτ : τ ≠ 0) : HasDerivAt edgePhiDeriv2 (edgePhiDeriv3 τ) τ := by
  have hy : Real.pi * τ ≠ 0 := mul_ne_zero Real.pi_ne_zero hτ
  have hs : Real.sinh (Real.pi * τ) ≠ 0 := by
    intro h; exact hy (Real.sinh_eq_zero.mp h)
  have h1 : HasDerivAt (fun s : ℝ => Real.pi / Real.sinh (Real.pi * s) - 1 / s)
      (Real.pi * (-(Real.cosh (Real.pi * τ) * Real.pi) / Real.sinh (Real.pi * τ) ^ 2) + 1 / τ ^ 2) τ := by
    have hsh : HasDerivAt (fun s : ℝ => Real.sinh (Real.pi * s)) (Real.cosh (Real.pi * τ) * Real.pi) τ := by
      simpa using ((hasDerivAt_id τ).const_mul Real.pi).sinh
    have := ((hasDerivAt_const τ Real.pi).div hsh hs).sub ((hasDerivAt_const τ (1 : ℝ)).div (hasDerivAt_id τ) hτ)
    refine this.congr_deriv ?_
    simp; ring
  refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_ne.mem_nhds hτ] with s hs'
    have hys : Real.pi * s ≠ 0 := mul_ne_zero Real.pi_ne_zero hs'
    have hss : Real.sinh (Real.pi * s) ≠ 0 := fun h => hys (Real.sinh_eq_zero.mp h)
    unfold edgePhiDeriv2
    field_simp
    ring
  · unfold edgePhiDeriv3
    field_simp
    ring

lemma pcPhase_eq {c : ℝ} (hc : 0 < c) (ξ v : ℝ) :
    pcPhase c ξ v = c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v) := by
  have h3 := liftEps_cube hc
  rw [edgePhi_eq_cubic_add_ceHth]
  unfold pcPhase edgeR
  have : c * (Real.pi ^ 2 / 36 * (liftEps c * v) ^ 3) = Real.pi ^ 2 / 36 * v ^ 3 := by
    calc _ = Real.pi ^ 2 / 36 * v ^ 3 * (c * liftEps c ^ 3) := by ring
      _ = _ := by rw [h3, mul_one]
  linear_combination this

lemma hasDerivAt_pcPhase {c : ℝ} (hc : 0 < c) (ξ v : ℝ) :
    HasDerivAt (pcPhase c ξ) (c * liftEps c * edgePhiDeriv (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v)) v := by
  have hf : pcPhase c ξ = fun v => c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v) := funext (pcPhase_eq hc ξ)
  rw [hf]
  have := ((hasDerivAt_edgePhi (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v)).comp v ((hasDerivAt_id v).const_mul (liftEps c))).const_mul c
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma deriv_pcPhase {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    deriv (pcPhase c ξ) = fun v => c * liftEps c * edgePhiDeriv (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v) :=
  funext fun v => (hasDerivAt_pcPhase hc ξ v).deriv

lemma hasDerivAt_deriv_pcPhase {c : ℝ} (hc : 0 < c) (ξ v : ℝ) :
    HasDerivAt (deriv (pcPhase c ξ)) (c * liftEps c ^ 2 * edgePhiDeriv2 (liftEps c * v)) v := by
  rw [deriv_pcPhase hc ξ]
  have h := ((hasDerivAt_edgePhiDeriv (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v)).comp v ((hasDerivAt_id v).const_mul (liftEps c))).const_mul (c * liftEps c)
  exact h.congr_deriv (by simp; ring)

lemma deriv2_pcPhase {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    deriv (deriv (pcPhase c ξ)) = fun v => c * liftEps c ^ 2 * edgePhiDeriv2 (liftEps c * v) :=
  funext fun v => (hasDerivAt_deriv_pcPhase hc ξ v).deriv

lemma deriv3_pcPhase {c : ℝ} (hc : 0 < c) (ξ : ℝ) {v : ℝ} (hv : v ≠ 0) :
    deriv (deriv (deriv (pcPhase c ξ))) v = edgePhiDeriv3 (liftEps c * v) := by
  have hε := liftEps_pos hc
  have hτ : liftEps c * v ≠ 0 := mul_ne_zero hε.ne' hv
  rw [deriv2_pcPhase hc ξ]
  have h := ((hasDerivAt_edgePhiDeriv2_of_ne hτ).comp v ((hasDerivAt_id v).const_mul (liftEps c))).const_mul (c * liftEps c ^ 2)
  have : (c * liftEps c ^ 2) * (edgePhiDeriv3 (liftEps c * v) * (liftEps c * 1)) = edgePhiDeriv3 (liftEps c * v) := by
    have h3 := liftEps_cube hc
    calc _ = (c * liftEps c ^ 3) * edgePhiDeriv3 (liftEps c * v) := by ring
      _ = _ := by rw [h3, one_mul]
  have h' := h.deriv
  simp only [Function.comp_def] at h'
  rw [this] at h'
  exact h'

/-- **`(u1c:psibd)`**: on `|εv| ≤ τ_*(L)`, `ψ' ≥ A/2`; for `v ≠ 0`, `|ψ''| ≤ min(π²|v|/6, c^{2/3}/|v|)` and `|ψ'''| ≤ π²/3`. -/
theorem pcPhase_psibd {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hL : 0 < Real.log (Real.pi ^ 2 * ξ)) :
    (∀ v : ℝ, |liftEps c * v| ≤ tauStar (Real.log (Real.pi ^ 2 * ξ)) →
      c * liftEps c * Real.log (Real.pi ^ 2 * ξ) / 2 ≤ deriv (pcPhase c ξ) v) ∧
    (∀ v : ℝ, v ≠ 0 → |deriv (deriv (pcPhase c ξ)) v| ≤ min (Real.pi ^ 2 / 6 * |v|) (c ^ (2 / 3 : ℝ) / |v|)) ∧
    (∀ v : ℝ, v ≠ 0 → |deriv (deriv (deriv (pcPhase c ξ))) v| ≤ Real.pi ^ 2 / 3) := by
  have hε := liftEps_pos hc
  have h3 := liftEps_cube hc
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [deriv_pcPhase hc ξ]
    have := edgePhiDeriv_ge hL hv
    have hpos : 0 ≤ c * liftEps c := by positivity
    calc c * liftEps c * Real.log (Real.pi ^ 2 * ξ) / 2 = c * liftEps c * (Real.log (Real.pi ^ 2 * ξ) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hpos
  · rw [deriv2_pcPhase hc ξ]
    dsimp only
    have hτ : liftEps c * v ≠ 0 := mul_ne_zero hε.ne' hv
    have hb := edgePhiDeriv2_abs_le hτ
    have hk : 0 ≤ c * liftEps c ^ 2 := by positivity
    rw [abs_mul, abs_of_nonneg hk]
    have habs : |liftEps c * v| = liftEps c * |v| := by rw [abs_mul, abs_of_pos hε]
    rw [habs] at hb
    have hε1 : c ^ (1 / 3 : ℝ) * liftEps c = 1 := by
      unfold liftEps; rw [Real.rpow_neg hc.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc _).ne']
    have hε2 : c ^ (1 / 3 : ℝ) * (liftEps c)⁻¹ = c ^ (2 / 3 : ℝ) := by
      unfold liftEps; rw [Real.rpow_neg hc.le, inv_inv, ← Real.rpow_add hc]; norm_num
    have hc23 : c * liftEps c ^ 2 = c ^ (1 / 3 : ℝ) := by
      have : liftEps c ^ 2 = liftEps c * liftEps c := sq _
      calc c * liftEps c ^ 2 = (c * liftEps c ^ 3) * (liftEps c)⁻¹ := by field_simp
        _ = c ^ (1 / 3 : ℝ) := by
          rw [h3, one_mul]; unfold liftEps; rw [Real.rpow_neg hc.le, inv_inv]
    have hp : 0 ≤ c ^ (1 / 3 : ℝ) := (Real.rpow_pos_of_pos hc _).le
    rw [hc23] at hk ⊢
    refine le_min ?_ ?_
    · calc c ^ (1 / 3 : ℝ) * |edgePhiDeriv2 (liftEps c * v)| ≤ c ^ (1 / 3 : ℝ) * (Real.pi ^ 2 / 6 * (liftEps c * |v|)) :=
            mul_le_mul_of_nonneg_left (hb.trans (min_le_left _ _)) hp
        _ = Real.pi ^ 2 / 6 * |v| := by
            calc _ = (c ^ (1 / 3 : ℝ) * liftEps c) * (Real.pi ^ 2 / 6 * |v|) := by ring
              _ = _ := by rw [hε1, one_mul]
    · calc c ^ (1 / 3 : ℝ) * |edgePhiDeriv2 (liftEps c * v)| ≤ c ^ (1 / 3 : ℝ) * (liftEps c * |v|)⁻¹ :=
            mul_le_mul_of_nonneg_left (hb.trans (min_le_right _ _)) hp
        _ = c ^ (2 / 3 : ℝ) / |v| := by
            rw [mul_inv, ← hε2]; ring
  · rw [deriv3_pcPhase hc ξ hv]
    exact edgePhiDeriv3_abs_le (mul_ne_zero hε.ne' hv)

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_edgePhiDeriv2_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hasDerivAt_edgePhiDeriv2_of_ne
/-- info: 'FormalResearch.CohnElkies.pcPhase_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pcPhase_eq
/-- info: 'FormalResearch.CohnElkies.deriv3_pcPhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.deriv3_pcPhase
/-- info: 'FormalResearch.CohnElkies.pcPhase_psibd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pcPhase_psibd

end FormalResearch.CohnElkies

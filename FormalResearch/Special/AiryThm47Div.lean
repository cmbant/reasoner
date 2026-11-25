module

public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Complex.EntireDivSq

/-!
# Dividing an entire function of the Airy class by `∏(u - t)` (input to Theorem 4.7)

If `φ` is entire with `‖φ u‖ ≤ C (1+|u|)^ν e(u)` and vanishes at the points of a finite set `S ⊂ ℝ`, then
`φ = ψ ∏_{t∈S}(u - t)` with `ψ` entire and `‖ψ u‖ ≤ C' (1+|u|)^ν e(u)` (`at47_div_finset`).
One point at a time (`at47_div_point`): `ψ = dslope φ t`; for `|u| ≥ |t|+1` we have `|u - t| ≥ 1`; on the compact ball `|u| ≤ |t|+1`
`ψ` is bounded while `(1+|u|)^ν e(u)` is bounded below (`Re u^{3/2} ≤ |u|^{3/2}`).  All proved.
-/

@[expose] public section

open Complex Metric Set

namespace FormalResearch.Special

lemma at47_env_lower {B : ℝ} {u : ℂ} (hu : ‖u‖ ≤ B) (_hB : 0 ≤ B) :
    Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ)) ≤ airyEnv u := by
  unfold airyEnv
  apply Real.exp_le_exp.mpr
  have h1 : (u ^ (3 / 2 : ℂ)).re ≤ ‖u ^ (3 / 2 : ℂ)‖ := Complex.re_le_norm _
  rw [norm_cpow_three_halves] at h1
  have h2 : ‖u‖ ^ (3 / 2 : ℝ) ≤ B ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg _) hu (by norm_num)
  linarith

lemma at47_rpow_lower {B ν : ℝ} {u : ℂ} (hu : ‖u‖ ≤ B) :
    min 1 ((1 + B) ^ ν) ≤ (1 + ‖u‖) ^ ν := by
  have h0 : 1 ≤ 1 + ‖u‖ := by linarith [norm_nonneg u]
  rcases le_or_gt 0 ν with hν | hν
  · exact (min_le_left _ _).trans (Real.one_le_rpow h0 hν)
  · exact (min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hν.le)

lemma at47_div_point {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (t : ℝ) (h0 : φ (t : ℂ) = 0) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖φ u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ (∀ u, φ u = ψ u * (u - (t : ℂ))) ∧
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ u : ℂ, ‖ψ u‖ ≤ C' * (1 + ‖u‖) ^ ν * airyEnv u := by
  have hψ := EntireDiv.differentiable_dslope_entire hφ (t : ℂ)
  refine ⟨dslope φ (t : ℂ), hψ, fun u => ?_, ?_⟩
  · have := sub_smul_dslope φ (t : ℂ) u
    rw [h0, sub_zero, smul_eq_mul] at this
    rw [← this]; ring
  · set B : ℝ := |t| + 1 with hBdef
    have hB0 : 0 ≤ B := by positivity
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn hψ.continuous.continuousOn
    set e0 : ℝ := Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ)) with he0
    set m1 : ℝ := min 1 ((1 + B) ^ ν) with hm1
    have he0p : 0 < e0 := Real.exp_pos _
    have hm1p : 0 < m1 := lt_min one_pos (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 + B) ν)
    refine ⟨max C (|M| / (m1 * e0)), le_max_of_le_left hC, fun u => ?_⟩
    by_cases hu : ‖u‖ ≤ B
    · have h1 : ‖dslope φ (t : ℂ) u‖ ≤ |M| := (hM u (by simpa using hu)).trans (le_abs_self _)
      have h2 : m1 * e0 ≤ (1 + ‖u‖) ^ ν * airyEnv u :=
        mul_le_mul (at47_rpow_lower hu) (at47_env_lower hu hB0) he0p.le (Real.rpow_nonneg (by linarith [norm_nonneg u] : (0:ℝ) ≤ 1 + ‖u‖) _)
      have h3 : |M| ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ ν * airyEnv u) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      calc ‖dslope φ (t : ℂ) u‖ ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ ν * airyEnv u) := h1.trans h3
        _ ≤ max C (|M| / (m1 * e0)) * ((1 + ‖u‖) ^ ν * airyEnv u) := by
          have := mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg u] : (0:ℝ) ≤ 1 + ‖u‖) ν) (airyEnv_pos u).le
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) this
        _ = _ := by ring
    · replace hu := not_le.mp hu
      have hne : u ≠ (t : ℂ) := by
        intro h; rw [h, Complex.norm_real, Real.norm_eq_abs] at hu; linarith
      have hge : 1 ≤ ‖u - (t : ℂ)‖ := by
        have := norm_sub_norm_le u (t : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith
      rw [dslope_of_ne _ hne, slope_def_field, norm_div]
      have hpos : 0 < ‖u - (t : ℂ)‖ := by linarith
      calc ‖φ u - φ (t : ℂ)‖ / ‖u - (t : ℂ)‖ ≤ ‖φ u‖ := by
            rw [h0, sub_zero, div_le_iff₀ hpos]
            nlinarith [norm_nonneg (φ u)]
        _ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u := hb u
        _ ≤ max C (|M| / (m1 * e0)) * (1 + ‖u‖) ^ ν * airyEnv u := by
          have := mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg u] : (0:ℝ) ≤ 1 + ‖u‖) ν) (airyEnv_pos u).le
          have h := mul_le_mul_of_nonneg_right (le_max_left C (|M| / (m1 * e0))) this
          linarith

theorem at47_div_finset (S : Finset ℝ) :
    ∀ {φ : ℂ → ℂ}, Differentiable ℂ φ → (∀ t ∈ S, φ (t : ℂ) = 0) → ∀ {C ν : ℝ}, 0 ≤ C →
    (∀ u : ℂ, ‖φ u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ (∀ u, φ u = ψ u * ∏ t ∈ S, (u - (t : ℂ))) ∧
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ u : ℂ, ‖ψ u‖ ≤ C' * (1 + ‖u‖) ^ ν * airyEnv u := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ _ C ν hC hb
    exact ⟨φ, hφ, fun u => by simp, C, hC, hb⟩
  | insert a S ha ih =>
    intro φ hφ hz C ν hC hb
    obtain ⟨ψ1, hψ1, he1, C1, hC1, hb1⟩ := at47_div_point hφ a (hz a (Finset.mem_insert_self _ _)) hC hb
    have hz1 : ∀ t ∈ S, ψ1 (t : ℂ) = 0 := by
      intro t ht
      have h := he1 (t : ℂ)
      rw [hz t (Finset.mem_insert_of_mem ht)] at h
      have hta : (t : ℂ) - (a : ℂ) ≠ 0 := by
        intro h0
        have : t = a := by exact_mod_cast sub_eq_zero.mp h0
        exact ha (this ▸ ht)
      exact (mul_eq_zero.mp h.symm).resolve_right hta
    obtain ⟨ψ, hψ, he, C', hC', hb'⟩ := ih hψ1 hz1 hC1 hb1
    refine ⟨ψ, hψ, fun u => ?_, C', hC', hb'⟩
    rw [he1 u, he u, Finset.prod_insert ha]; ring

/-- info: 'FormalResearch.Special.at47_div_finset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_div_finset

end FormalResearch.Special

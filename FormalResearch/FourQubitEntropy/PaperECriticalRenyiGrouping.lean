import FormalResearch.FourQubitEntropy.PaperECriticalRenyiJ
import FormalResearch.FourQubitEntropy.RenyiSpec

/-!
# Binary grouping for the Rényi entropy of order `q_b` (`lem:fqe-renyi-grouping`)

Paper E, `renyi_cubic_bound.tex`. For probability vectors `u`, `v` and `0 ≤ a ≤ 1`, with `w = a²(3-2a)`,
`q_b = 4 ln 2/(4 ln 2 - 1)` and `H_q = renyiSpec q` (bits):

`H_{q_b}(a u, (1-a) v) ≤ 4a(1-a) + w H_{q_b}(u) + (1-w) H_{q_b}(v)`   (`renyi_grouping`, `eq:fqe-renyi-grouping`).

Also here: `renyi_binary_bound` (`H_{q_b}(a,1-a) ≤ 4a(1-a)`) and `renyi_cubic_bound`
(`prop:fqe-cubic-bound`, inequality for every four-point probability vector and every `q ≥ q_b`:
`H_q(λ) ≤ 10/3 - 6 Σλ² + (8/3) Σλ³`).

Proved, axiom-free. Inequality parts only: the equality cases of the lemma (`a = 1/2` and `H(u) = H(v)`) and
of `(CB)` (pure, uniform-two, uniform-four spectra) are in `PaperECriticalRenyiEq.lean`. NOT formalised are the
necessity of the threshold `q_b`, the numerical bounds `3/2 < q_b < 313/200`, and `cor:fqe-renyi-high-f`.
The analytic core `J ≥ 0` is `Jf_nonneg` (`PaperECriticalRenyiJ.lean`).
-/

open Real

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- Log-sum inequality: `ln(A+B) ≥ w ln A + (1-w) ln B + h(w)` for `A, B > 0`, `0 < w < 1`. -/
theorem log_add_ge {A B w : ℝ} (hA : 0 < A) (hB : 0 < B) (hw0 : 0 < w) (hw1 : w < 1) :
    w * Real.log A + (1 - w) * Real.log B + Real.binEntropy w ≤ Real.log (A + B) := by
  have h1w : 0 < 1 - w := by linarith
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (show A / w ∈ Set.Ioi (0 : ℝ) from div_pos hA hw0)
    (show B / (1 - w) ∈ Set.Ioi (0 : ℝ) from div_pos hB h1w) hw0.le h1w.le (by ring)
  simp only [smul_eq_mul] at hc
  have e : w * (A / w) + (1 - w) * (B / (1 - w)) = A + B := by field_simp
  rw [e, Real.log_div hA.ne' hw0.ne', Real.log_div hB.ne' h1w.ne'] at hc
  have hb : Real.binEntropy w = -(w * Real.log w) - (1 - w) * Real.log (1 - w) := by
    unfold Real.binEntropy; rw [Real.log_inv, Real.log_inv]; ring
  rw [hb]
  linarith

section Grouping

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_rpow_pos_of_prob {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) {q : ℝ} (hq : 0 < q) :
    0 < ∑ i, u i ^ q := by
  have : ∃ i, 0 < u i := by
    by_contra h
    push Not at h
    have : ∑ i, u i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hu i))
    rw [hs] at this; exact one_ne_zero this
  obtain ⟨i, hi⟩ := this
  exact Finset.sum_pos' (fun j _ => Real.rpow_nonneg (hu j) q) ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos hi q⟩

/-- Binary grouping for the order `q_b` (inequality part of `lem:fqe-renyi-grouping`). -/
theorem renyi_grouping {u : ι → ℝ} {v : κ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hus : ∑ i, u i = 1) (hvs : ∑ j, v j = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    renyiSpec qb (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j)) ≤
      4 * a * (1 - a) + wf a * renyiSpec qb u + (1 - wf a) * renyiSpec qb v := by
  have hr : 0 < rb := by unfold rb; have := four_Lg_sub_one_pos; positivity
  have hq : qb = rb + 1 := qb_eq_rb_add_one
  have hq0 : 0 < qb := by linarith
  have hL : 0 < Lg := by have := Lg_gt; linarith
  have h4 : 4 * Lg * rb = qb := by
    unfold rb qb; have := four_Lg_sub_one_pos; field_simp
  have hSu := sum_rpow_pos_of_prob hu hus hq0
  have hSv := sum_rpow_pos_of_prob hv hvs hq0
  set Su := ∑ i, u i ^ qb with hSu_def
  set Sv := ∑ j, v j ^ qb with hSv_def
  have hden : (1 - qb) = -rb := by linarith
  have hlogb : ∀ x : ℝ, Real.logb 2 x = Real.log x / Lg := fun x => rfl
  -- the three entropies in terms of logs
  have hHu : renyiSpec qb u = -Real.log Su / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hden, ← hSu_def]; field_simp
  have hHv : renyiSpec qb v = -Real.log Sv / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hden, ← hSv_def]; field_simp
  have hcat : ∑ x, (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j) x) ^ qb
      = a ^ qb * Su + (1 - a) ^ qb * Sv := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hSu_def, hSv_def, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Real.mul_rpow ha0 (hu i)
    · exact Finset.sum_congr rfl fun j _ => Real.mul_rpow (by linarith) (hv j)
  have hHc : renyiSpec qb (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j))
      = -Real.log (a ^ qb * Su + (1 - a) ^ qb * Sv) / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hcat, hden]; field_simp
  rw [hHc, hHu, hHv]
  have hLr : 0 < Lg * rb := mul_pos hL hr
  -- reduce to the logarithmic inequality
  suffices key : wf a * Real.log Su + (1 - wf a) * Real.log Sv - qb * a * (1 - a) ≤
      Real.log (a ^ qb * Su + (1 - a) ^ qb * Sv) by
    rw [div_le_iff₀ hLr]
    have e : (4 * a * (1 - a) + wf a * (-Real.log Su / (Lg * rb)) + (1 - wf a) * (-Real.log Sv / (Lg * rb)))
        * (Lg * rb) = qb * a * (1 - a) - wf a * Real.log Su - (1 - wf a) * Real.log Sv := by
      field_simp; rw [← h4]; ring
    rw [e]; linarith
  rcases eq_or_lt_of_le ha0 with h0 | h0
  · -- a = 0
    subst h0
    have : wf 0 = 0 := by unfold wf; norm_num
    rw [this, Real.zero_rpow hq0.ne']
    simp
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · subst h1
    have : wf 1 = 1 := by unfold wf; norm_num
    rw [this, sub_self, Real.zero_rpow hq0.ne']
    simp
  -- interior case
  have hA : 0 < a ^ qb * Su := mul_pos (Real.rpow_pos_of_pos h0 _) hSu
  have hB : 0 < (1 - a) ^ qb * Sv := mul_pos (Real.rpow_pos_of_pos (by linarith) _) hSv
  have hls := log_add_ge hA hB (wf_pos h0 h1) (wf_lt_one h0 h1)
  rw [Real.log_mul (Real.rpow_pos_of_pos h0 _).ne' hSu.ne', Real.log_mul
    (Real.rpow_pos_of_pos (by linarith) _).ne' hSv.ne', Real.log_rpow h0,
    Real.log_rpow (by linarith)] at hls
  have hJ := Jf_nonneg h0.le h1.le
  unfold Jf at hJ
  nlinarith

end Grouping

/-- **Binary consequence** (`H_{q_b}(a, 1-a) ≤ 4a(1-a)`), from the grouping bound with pure `u`, `v`. -/
theorem renyi_binary_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    renyiSpec qb ![a, 1 - a] ≤ 4 * a * (1 - a) := by
  have h := renyi_grouping (u := fun _ : Unit => (1 : ℝ)) (v := fun _ : Unit => (1 : ℝ))
    (fun _ => zero_le_one) (fun _ => zero_le_one) (by simp) (by simp) ha0 ha1
  have h0 : renyiSpec qb (fun _ : Unit => (1 : ℝ)) = 0 := by
    unfold renyiSpec; simp
  rw [h0] at h
  have e : renyiSpec qb (Sum.elim (fun _ : Unit => a * 1) (fun _ : Unit => (1 - a) * 1)) =
      renyiSpec qb ![a, 1 - a] := by
    unfold renyiSpec
    simp [Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [e] at h
  simpa using h



/-! ### The cubic bound `(CB)` -/

theorem split_pair {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ (x + y) * u = x ∧ (x + y) * (1 - u) = y := by
  by_cases h : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0; subst hy0
    exact ⟨0, le_refl _, zero_le_one, by simp, by simp⟩
  · have hp : 0 < x + y := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨x / (x + y), by positivity, ?_, by field_simp, by field_simp; ring⟩
    rw [div_le_one hp]; linarith

/-- **`prop:fqe-cubic-bound` (inequality, `q ≥ q_b`)**: every four-point probability vector satisfies
`H_q(λ) ≤ 10/3 - 6 Σλ² + (8/3) Σλ³ = 4 e₂(λ) + 8 e₃(λ)`. -/
theorem renyi_cubic_bound_qb (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    renyiSpec qb l ≤ 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 := by
  rw [Fin.sum_univ_four] at hs
  obtain ⟨u0, hu0a, hu0b, hu0, hu1⟩ := split_pair (hl 0) (hl 1)
  obtain ⟨v0, hv0a, hv0b, hv0, hv1⟩ := split_pair (hl 2) (hl 3)
  set a := l 0 + l 1 with ha
  have ha0 : 0 ≤ a := by have := hl 0; have := hl 1; linarith
  have hb : l 2 + l 3 = 1 - a := by linarith
  rw [hb] at hv0 hv1
  have ha1 : a ≤ 1 := by have := hl 2; have := hl 3; linarith
  have hcat : renyiSpec qb l = renyiSpec qb (Sum.elim (fun i : Fin 2 => a * ![u0, 1 - u0] i)
      (fun j : Fin 2 => (1 - a) * ![v0, 1 - v0] j)) := by
    unfold renyiSpec
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four, hu0, hu1, hv0, hv1]
    rw [add_assoc (l 0 ^ qb + l 1 ^ qb)]
  have hg := renyi_grouping (u := ![u0, 1 - u0]) (v := ![v0, 1 - v0])
    (by intro i; fin_cases i <;> simp <;> linarith) (by intro i; fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_two]) (by simp [Fin.sum_univ_two]) ha0 ha1
  have hbu := renyi_binary_bound hu0a hu0b
  have hbv := renyi_binary_bound hv0a hv0b
  have hw0 : 0 ≤ wf a := by
    unfold wf; have : 0 ≤ 3 - 2 * a := by linarith
    positivity
  have hw1 : 0 ≤ 1 - wf a := by
    rw [one_sub_wf]; have : 0 ≤ 1 - a := by linarith
    positivity
  have e1 : a ^ 2 * (u0 * (1 - u0)) = l 0 * l 1 := by rw [← hu0, ← hu1]; ring
  have e2 : (1 - a) ^ 2 * (v0 * (1 - v0)) = l 2 * l 3 := by rw [← hv0, ← hv1]; ring
  have hE : 4 * a * (1 - a) + wf a * (4 * u0 * (1 - u0)) + (1 - wf a) * (4 * v0 * (1 - v0))
      = 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 := by
    rw [one_sub_wf]
    unfold wf
    simp only [Fin.sum_univ_four]
    have l3 : l 3 = 1 - l 0 - l 1 - l 2 := by linarith
    have : 4 * a * (1 - a) + a ^ 2 * (3 - 2 * a) * (4 * u0 * (1 - u0)) +
        (1 - a) ^ 2 * (1 + 2 * a) * (4 * v0 * (1 - v0)) =
        4 * a * (1 - a) + 4 * (3 - 2 * a) * (a ^ 2 * (u0 * (1 - u0))) +
        4 * (1 + 2 * a) * ((1 - a) ^ 2 * (v0 * (1 - v0))) := by ring
    rw [this, e1, e2, ha, l3]
    ring
  rw [hcat]
  calc _ ≤ 4 * a * (1 - a) + wf a * renyiSpec qb ![u0, 1 - u0] + (1 - wf a) * renyiSpec qb ![v0, 1 - v0] := hg
    _ ≤ 4 * a * (1 - a) + wf a * (4 * u0 * (1 - u0)) + (1 - wf a) * (4 * v0 * (1 - v0)) := by
        gcongr
    _ = _ := hE

theorem renyi_cubic_bound {q : ℝ} (hq : qb ≤ q) (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) :
    renyiSpec q l ≤ 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 := by
  have hr : 0 < rb := by unfold rb; have := four_Lg_sub_one_pos; positivity
  have h1 : 1 < qb := by rw [qb_eq_rb_add_one]; linarith
  exact (renyiSpec_anti h1 hq hl hs).trans (renyi_cubic_bound_qb l hl hs)

end FormalResearch.FourQubitEntropy.PaperECritical

module

public import FormalResearch.Special.BarnesEntire

/-!
# Orders of the zeros of Barnes' `G`

`G` has a zero of order exactly `m + 1` at `-m`, `m = 0, 1, 2, …` (`analyticOrderAt_barnesG`).

Proof: near `-m`, `G = G₀(· + m + 1) ∏_{k ≤ m} 1/Γ(· + k)` (`BarnesEntire`), `G₀ ≠ 0`, and `1/Γ` has a
simple zero at `-j` for every `j` (`analyticOrderAt_inv_Gamma`): by the recurrence
`1/Γ(u) = u / Γ(u+1)` (valid for all `u` with Mathlib's junk values),
`1/Γ(u) = ∏_{i ≤ j} (u + i) · 1/Γ(u + j + 1)`, whose first factor has a simple zero at `-j` and
second factor equals `1/Γ(1) = 1` there.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

lemma inv_Gamma_rec (u : ℂ) : 1 / Gamma u = u * (1 / Gamma (u + 1)) := by
  by_cases h : u = 0
  · subst h; simp
  · rw [Gamma_add_one u h]
    by_cases hg : Gamma u = 0
    · simp [hg]
    · field_simp

lemma inv_Gamma_eq_prod (j : ℕ) (u : ℂ) :
    1 / Gamma u = (∏ i ∈ Finset.range (j + 1), (u + i)) * (1 / Gamma (u + (j + 1 : ℕ))) := by
  induction j generalizing u with
  | zero => simp [inv_Gamma_rec u]
  | succ j ih =>
    rw [inv_Gamma_rec u, ih (u + 1), Finset.prod_range_succ' _ (j + 1)]
    have : ∀ i : ℕ, (u + 1 + (i : ℂ)) = u + ((i + 1 : ℕ) : ℂ) := fun i => by push_cast; ring
    simp only [this, Nat.cast_zero, add_zero]
    ring

lemma analyticOrderAt_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
    analyticOrderAt (fun w => ∏ i ∈ s, f i w) z = ∑ i ∈ s, analyticOrderAt (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (analyticAt_const (v := (1 : ℂ)) (x := z)).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : AnalyticAt ℂ (f a) z := hf a (Finset.mem_insert_self a s)
    have h2 : AnalyticAt ℂ (fun w => ∏ i ∈ s, f i w) z :=
      Finset.analyticAt_fun_prod s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (analyticOrderAt_mul h1 h2).trans (by rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)])


lemma analyticAt_inv_Gamma_shift (c : ℂ) (z : ℂ) : AnalyticAt ℂ (fun u => 1 / Gamma (u + c)) z := by
  have h : Differentiable ℂ (fun u : ℂ => 1 / Gamma (u + c)) := by
    have := differentiable_one_div_Gamma.comp (differentiable_id.add_const c)
    simpa [Function.comp_def, one_div] using this
  exact h.analyticAt z

/-- `1/Γ` has a simple zero at `-j`. -/
theorem analyticOrderAt_inv_Gamma (j : ℕ) :
    analyticOrderAt (fun u : ℂ => 1 / Gamma u) (-(j : ℂ)) = 1 := by
  have hfun : (fun u : ℂ => 1 / Gamma u) =
      (fun u => ∏ i ∈ Finset.range (j + 1), (u - (-(i : ℂ)))) *
        (fun u => 1 / Gamma (u + ((j + 1 : ℕ) : ℂ))) := by
    funext u
    simp only [Pi.mul_apply, sub_neg_eq_add]
    exact inv_Gamma_eq_prod j u
  have hP : ∀ i ∈ Finset.range (j + 1), AnalyticAt ℂ (fun u : ℂ => u - (-(i : ℂ))) (-(j : ℂ)) :=
    fun i _ => by fun_prop
  have hg := analyticAt_inv_Gamma_shift ((j + 1 : ℕ) : ℂ) (-(j : ℂ))
  rw [hfun, analyticOrderAt_mul (Finset.analyticAt_fun_prod _ hP) hg,
    analyticOrderAt_finset_prod _ _ _ hP]
  have hg0 : analyticOrderAt (fun u : ℂ => 1 / Gamma (u + ((j + 1 : ℕ) : ℂ))) (-(j : ℂ)) = 0 := by
    rw [hg.analyticOrderAt_eq_zero]
    simp
  rw [hg0, add_zero]
  have : ∀ i ∈ Finset.range (j + 1), analyticOrderAt (fun u : ℂ => u - (-(i : ℂ))) (-(j : ℂ)) =
      if i = j then 1 else 0 := by
    intro i _
    by_cases h : i = j
    · subst h; simp only [ite_true]; exact analyticOrderAt_id_sub_const_self
    · simp only [h, ite_false]
      refine analyticOrderAt_id_sub_const_of_ne ?_
      intro h'
      apply h
      have : (i : ℂ) = j := by linear_combination h'
      exact_mod_cast this
  rw [Finset.sum_congr rfl this]
  simp


/-- **Zeros of Barnes' `G`:** a zero of order exactly `m + 1` at `-m`. -/
theorem analyticOrderAt_barnesG (m : ℕ) : analyticOrderAt barnesG (-(m : ℂ)) = (m + 1 : ℕ) := by
  have hev : barnesG =ᶠ[𝓝 (-(m : ℂ))] barnesGn (m + 1) := by
    have ho : IsOpen {u : ℂ | 0 < (u + ((m + 1 : ℕ) : ℂ)).re} :=
      isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))
    have hm : (-(m : ℂ)) ∈ {u : ℂ | 0 < (u + ((m + 1 : ℕ) : ℂ)).re} := by
      show 0 < ((-(m : ℂ)) + ((m + 1 : ℕ) : ℂ)).re
      simp
    filter_upwards [ho.mem_nhds hm] with u hu using barnesG_eq_barnesGn hu
  rw [analyticOrderAt_congr hev]
  unfold barnesGn
  have hG0 : AnalyticAt ℂ (fun w => barnesG0 (w + ((m + 1 : ℕ) : ℂ))) (-(m : ℂ)) := by
    have hre : 0 < ((-(m : ℂ)) + ((m + 1 : ℕ) : ℂ)).re := by simp
    have hd : ∀ᶠ w in 𝓝 (-(m : ℂ)), DifferentiableAt ℂ (fun w => barnesG0 (w + ((m + 1 : ℕ) : ℂ))) w := by
      have ho : IsOpen {u : ℂ | 0 < (u + ((m + 1 : ℕ) : ℂ)).re} :=
        isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))
      filter_upwards [ho.mem_nhds hre] with w hw
      exact ((hasDerivAt_barnesG0 hw).comp_add_const w _).differentiableAt
    exact (Complex.analyticAt_iff_eventually_differentiableAt).mpr hd
  have hP : ∀ k ∈ Finset.range (m + 1), AnalyticAt ℂ (fun w : ℂ => 1 / Gamma (w + (k : ℂ))) (-(m : ℂ)) :=
    fun k _ => analyticAt_inv_Gamma_shift _ _
  have hprod : AnalyticAt ℂ (fun w => ∏ k ∈ Finset.range (m + 1), (1 / Gamma (w + (k : ℂ)))) (-(m : ℂ)) :=
    Finset.analyticAt_fun_prod _ hP
  rw [show (fun w => barnesG0 (w + ((m + 1 : ℕ) : ℂ)) * ∏ k ∈ Finset.range (m + 1), (1 / Gamma (w + (k : ℂ)))) =
    (fun w => barnesG0 (w + ((m + 1 : ℕ) : ℂ))) * (fun w => ∏ k ∈ Finset.range (m + 1), (1 / Gamma (w + (k : ℂ)))) from rfl,
    analyticOrderAt_mul hG0 hprod, analyticOrderAt_finset_prod _ _ _ hP]
  have h0 : analyticOrderAt (fun w => barnesG0 (w + ((m + 1 : ℕ) : ℂ))) (-(m : ℂ)) = 0 := by
    rw [hG0.analyticOrderAt_eq_zero]; exact barnesG0_ne_zero _
  have hk : ∀ k ∈ Finset.range (m + 1),
      analyticOrderAt (fun w : ℂ => 1 / Gamma (w + (k : ℂ))) (-(m : ℂ)) = 1 := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := fun u : ℂ => 1 / Gamma u)
      (g := fun w : ℂ => w + (k : ℂ)) (z₀ := -(m : ℂ)) (by fun_prop) (by simp)
    have e : (-(m : ℂ)) + (k : ℂ) = -((m - k : ℕ) : ℂ) := by
      rw [Nat.cast_sub hkm]; ring
    have := analyticOrderAt_inv_Gamma (m - k)
    simp only [Function.comp_def] at hcomp
    rw [hcomp]
    simp only [e]
    exact this
  rw [h0, zero_add, Finset.sum_congr rfl hk]
  simp

/-- info: 'FormalResearch.Special.Barnes.analyticOrderAt_barnesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOrderAt_barnesG

end FormalResearch.Special.Barnes

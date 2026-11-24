module

public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumClark

/-!
# Comparison of node products (`virasoro_two_level.tex`, `gt:2.6`)

For interlacing sequences `p_k = |a_k|`, `q_k = |z_k|` with `NodeHyp` and reals `ξ, ξ'` the ratio factor
`r_k(ξ, ξ') = ((q_k - ξ)/(p_k - ξ)) / ((q_k - ξ')/(p_k - ξ'))` satisfies

`r_k - 1 = (p_k - q_k)(ξ' - ξ)/((p_k - ξ)(q_k - ξ'))`, `|r_k - 1| ≤ 8R (1/p_{k-1} - 1/p_k)`

for `|ξ|, |ξ'| ≤ R`, `p_{k-1} ≥ 2R`: the deviations telescope (`p_k - p_{k-1}` against `p_k p_{k-1}`), so

* `ratioFac_prod_uniform`: for `k₀ ≥ k₂(R)`, `1/2 ≤ ∏_{k₀ < k ≤ K} r_k ≤ 2` uniformly in `|ξ|, |ξ'| ≤ R` and `K ≥ k₀`;
* `ratioFac_prod_bounds`: for fixed `ξ, ξ' ≤ p_m`, `c ≤ ∏_{m < k ≤ K} r_k ≤ C` for all `K ≥ m`.

All results are proved unconditionally.
-/

@[expose] public section

open Finset Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

/-! ### Elementary product bounds -/

lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ θ i)
    (h1 : ∀ i ∈ s, θ i ≤ 1) : 1 - ∑ i ∈ s, θ i ≤ ∏ i ∈ s, (1 - θ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have ha0 := h0 a (Finset.mem_insert_self _ _)
    have ha1 := h1 a (Finset.mem_insert_self _ _)
    have hS : 0 ≤ ∑ i ∈ s, θ i := Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have := mul_le_mul_of_nonneg_left ih' (by linarith : 0 ≤ 1 - θ a)
    nlinarith

lemma exp_quarter_lt_two : Real.exp (1 / 4) < 2 := by
  by_contra h
  push Not at h
  have h4 := pow_le_pow_left₀ (by norm_num) h 4
  rw [← Real.exp_nat_mul] at h4
  have := Real.exp_one_lt_d9
  norm_num at h4
  linarith

/-- If `|r_i - 1| ≤ θ_i` with `Σ θ_i ≤ 1/4` then `1/2 ≤ ∏ r_i ≤ 2`. -/
lemma prod_bounds_of_dev (s : Finset ℕ) (r θ : ℕ → ℝ) (hθ : ∀ i ∈ s, 0 ≤ θ i)
    (hr : ∀ i ∈ s, |r i - 1| ≤ θ i) (hsum : ∑ i ∈ s, θ i ≤ 1 / 4) :
    1 / 2 ≤ ∏ i ∈ s, r i ∧ ∏ i ∈ s, r i ≤ 2 := by
  have hle : ∀ i ∈ s, θ i ≤ 1 / 4 := fun i hi =>
    (Finset.single_le_sum (f := θ) hθ hi).trans hsum
  have hr1 : ∀ i ∈ s, 1 - θ i ≤ r i := fun i hi => by
    have := (abs_le.1 (hr i hi)).1; linarith
  have hr2 : ∀ i ∈ s, r i ≤ 1 + θ i := fun i hi => by
    have := (abs_le.1 (hr i hi)).2; linarith
  constructor
  · have h1 := prod_one_sub_ge s θ hθ (fun i hi => by linarith [hle i hi])
    have h2 : ∏ i ∈ s, (1 - θ i) ≤ ∏ i ∈ s, r i :=
      Finset.prod_le_prod₀ (fun i hi => by linarith [hle i hi]) hr1
    linarith
  · have h2 : ∏ i ∈ s, r i ≤ ∏ i ∈ s, Real.exp (θ i) :=
      Finset.prod_le_prod₀ (fun i hi => by linarith [hr1 i hi, hle i hi])
        (fun i hi => (hr2 i hi).trans (by linarith [Real.add_one_le_exp (θ i)]))
    rw [← Real.exp_sum] at h2
    have h3 : Real.exp (∑ i ∈ s, θ i) ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 hsum
    linarith [exp_quarter_lt_two]

/-! ### The ratio factors -/

/-- `r_k(ξ, ξ') = ((q_k - ξ)(p_k - ξ'))/((p_k - ξ)(q_k - ξ'))`. -/
noncomputable def ratioFac (p q : ℕ → ℝ) (ξ ξ' : ℝ) (k : ℕ) : ℝ :=
  (q k - ξ) * (p k - ξ') / ((p k - ξ) * (q k - ξ'))

lemma ratioFac_sub_one {p q : ℕ → ℝ} {ξ ξ' : ℝ} {k : ℕ} (h1 : p k - ξ ≠ 0) (h2 : q k - ξ' ≠ 0) :
    ratioFac p q ξ ξ' k - 1 = (p k - q k) * (ξ' - ξ) / ((p k - ξ) * (q k - ξ')) := by
  unfold ratioFac
  field_simp
  ring

namespace NodeHyp

variable {p q : ℕ → ℝ} {k0 : ℕ} (h : NodeHyp p q k0)
include h

lemma exists_p_ge (R : ℝ) : ∃ k₂ : ℕ, 2 ≤ k₂ ∧ R ≤ p k₂ := by
  obtain ⟨k₂, hk₂⟩ := exists_nat_gt (max (|R| ^ 3) 2)
  have hk2 : (2 : ℝ) < k₂ := lt_of_le_of_lt (le_max_right _ _) hk₂
  have hk : 2 ≤ k₂ := by exact_mod_cast hk2.le
  refine ⟨k₂, hk, ?_⟩
  have hp := h.cube_lo k₂ hk
  have hpos := h.pos k₂ (by omega)
  have h1 : |R| ^ 3 < (k₂ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk₂
  have h2 : (k₂ : ℝ) ≤ (k₂ : ℝ) ^ 2 := by nlinarith
  have h3 : |R| ^ 3 ≤ p k₂ ^ 3 := by nlinarith
  have h4 : |R| ≤ p k₂ := le_of_pow_le_pow_left₀ (by norm_num) hpos.le h3
  exact (le_abs_self R).trans h4

lemma ratioFac_dev {k : ℕ} (hk : 2 ≤ k) {ξ ξ' R : ℝ} (hR : |ξ| ≤ R) (hR' : |ξ'| ≤ R)
    (hp : 2 * R ≤ p (k - 1)) :
    |ratioFac p q ξ ξ' k - 1| ≤ 8 * R * (1 / p (k - 1) - 1 / p k) := by
  have hpk1 : 0 < p (k - 1) := h.pos _ (by omega)
  have hpk : 0 < p k := h.pos _ (by omega)
  have hmono : p (k - 1) ≤ p k := h.mono' (by omega) (by omega)
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hξ : ξ ≤ R := (le_abs_self _).trans hR
  have hξ' : ξ' ≤ R := (le_abs_self _).trans hR'
  have hlo := h.int_lo k hk
  have hhi := h.int_hi k hk
  have d1 : p k / 2 ≤ p k - ξ := by linarith
  have d2 : p (k - 1) / 2 ≤ q k - ξ' := by linarith
  have d1p : 0 < p k - ξ := by linarith
  have d2p : 0 < q k - ξ' := by linarith
  rw [ratioFac_sub_one d1p.ne' d2p.ne']
  have hn : 0 ≤ p k - q k := by linarith
  have hn2 : p k - q k ≤ p k - p (k - 1) := by linarith
  have hxx : |ξ' - ξ| ≤ 2 * R := by
    calc |ξ' - ξ| ≤ |ξ'| + |ξ| := abs_sub _ _
      _ ≤ 2 * R := by linarith
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos d1p, abs_of_pos d2p]
  have hden : p k * p (k - 1) / 4 ≤ (p k - ξ) * (q k - ξ') := by
    calc p k * p (k - 1) / 4 = (p k / 2) * (p (k - 1) / 2) := by ring
      _ ≤ (p k - ξ) * (q k - ξ') := mul_le_mul d1 d2 (by positivity) d1p.le
  have hnum : (p k - q k) * |ξ' - ξ| ≤ (p k - p (k - 1)) * (2 * R) :=
    mul_le_mul hn2 hxx (abs_nonneg _) (by linarith)
  have hdenpos : 0 < p k * p (k - 1) / 4 := by positivity
  calc (p k - q k) * |ξ' - ξ| / ((p k - ξ) * (q k - ξ'))
      ≤ (p k - p (k - 1)) * (2 * R) / (p k * p (k - 1) / 4) :=
        div_le_div₀ (by nlinarith) hnum hdenpos hden
    _ = 8 * R * (1 / p (k - 1) - 1 / p k) := by field_simp; ring

omit h in
lemma sum_telescope_inv (k₀ K : ℕ) (hK : k₀ ≤ K) :
    ∑ k ∈ Finset.Ioc k₀ K, (1 / p (k - 1) - 1 / p k) = 1 / p k₀ - 1 / p K := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma ratioFac_prod_uniform (R : ℝ) : ∃ k₂ : ℕ, 2 ≤ k₂ ∧ ∀ ξ ξ' : ℝ, |ξ| ≤ R → |ξ'| ≤ R →
    ∀ k₀, k₂ ≤ k₀ → ∀ K, k₀ ≤ K →
      1 / 2 ≤ ∏ k ∈ Finset.Ioc k₀ K, ratioFac p q ξ ξ' k ∧
        ∏ k ∈ Finset.Ioc k₀ K, ratioFac p q ξ ξ' k ≤ 2 := by
  obtain ⟨k₂, hk₂, hpk₂⟩ := h.exists_p_ge (max (32 * R) 1)
  refine ⟨k₂, hk₂, fun ξ ξ' hξ hξ' k₀ hk₀ K hK => ?_⟩
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hξ
  have hp0 : 32 * R ≤ p k₀ := (le_max_left _ _).trans (hpk₂.trans (h.mono' (by omega) hk₀))
  have hpk0pos : 0 < p k₀ := h.pos _ (by omega)
  refine prod_bounds_of_dev _ _ (fun k => 8 * R * (1 / p (k - 1) - 1 / p k)) (fun k hk => ?_)
    (fun k hk => ?_) ?_
  · have hk' := Finset.mem_Ioc.1 hk
    have h1 : p (k - 1) ≤ p k := h.mono' (by omega) (by omega)
    have h2 : 0 < p (k - 1) := h.pos _ (by omega)
    have : 1 / p k ≤ 1 / p (k - 1) := one_div_le_one_div_of_le h2 h1
    nlinarith
  · have hk' := Finset.mem_Ioc.1 hk
    refine h.ratioFac_dev (by omega) hξ hξ' ?_
    have : p k₀ ≤ p (k - 1) := h.mono' (by omega) (by omega)
    linarith
  · rw [← Finset.mul_sum, sum_telescope_inv (p := p) k₀ K hK]
    have h1 : 0 < 1 / p K := by have := h.pos K (by omega); positivity
    have h2 : 8 * R * (1 / p k₀) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ hpk0pos]; nlinarith
    nlinarith

end NodeHyp

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NodeHyp.ratioFac_prod_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NodeHyp.ratioFac_prod_uniform

end FormalResearch.ModularBootstrap.TwoLevel

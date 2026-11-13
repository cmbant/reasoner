module

public import FormalResearch.Racah.P2AnalyticBulk3j

/-!
# The `3j` uniform edge-factorized expansion (Weyl P2, `thm:uniformedge` (a))

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:uniformedge` (a) (`eq:3juniformedge`),
`lem:sqrtfreecarrier`.

By `lem:sqrtfreecarrier` (`Phi3j_eq_Gc3_spec`) `Φ = E_N W_{3j} · Π_L^{-1/2} P̃_L(τ;N⁻²)`.  With
`edgeEnv3 M σ x t = √(𝔠_{p_+}((1-x)/2,h) 𝔠_{p_-}((1+x)/2,h))` (`= E_N W_{3j}`, `t = h² = N⁻²`) this is
`Φ = edgeEnv3 · H(τ,t)`, `H = P̃_L(τ;t)/√(Π_L(t))`.  Only the scalar `Π_L^{-1/2}` has to be expanded
in `t`.

## Results

* `edgeS3 M σ k r : ℝ[X]`, the polynomial `s_r(τ)` of degree `≤ k = L-L₀` in `τ = (1-x)/2`.
* `taylorCoeff_H3_eq_edgeS3`: it is the `t^r` Taylor coefficient of `H` at every `τ`.
* `natDegree_edgeS3_le`: `deg s_r ≤ k`.
* `edgeEnv3_mul_edgeS3_zero`: `W_{3j} s_0 = dZero3` (the paper's `d^L_{Mσ}(arccos x)`; the
  identification with the Wigner `d` is not made here).
* `Phi3j_uniform_edge` (**`thm:uniformedge` (a), `eq:3juniformedge`**): for every `R` there are
  `C, N₀` such that on the *whole* physical lattice (every admissible `N ≥ N₀`, every `μ` with
  `Lat4`) `|Φ - E_N W · ∑_{r<R} s_r(τ) N^{-2r}| ≤ C · E_N W · N^{-2R}`.

Not covered: the convergence-domain statements, exactness of the radius, and the bounds
`0 < c ≤ E_N ≤ 1` on the edge factor alone.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial Set Filter Topology

/-- `E_N(x) W_{3j}(x) = √(𝔠_{p_+}((1-x)/2, h) 𝔠_{p_-}((1+x)/2, h))`, `t = h² = N⁻²`. -/
noncomputable def edgeEnv3 (M σ : ℚ) (x t : ℝ) : ℝ :=
  Real.sqrt (Ct (pPlus3 M σ) ((1 - x) / 2) t * Ct (pMinus3 M σ) ((1 + x) / 2) t)

/-- `Π_L(t) = 𝔠_{2L+1}(1,h)`, `2L + 1 = p_+ + p_- + 2k + 1`. -/
noncomputable def Pi3 (M σ : ℚ) (k : ℕ) (t : ℝ) : ℝ :=
  Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 t

/-- `H(τ,t) = P̃_{L₀+k}(τ;t) / √(Π_L(t))`. -/
noncomputable def H3 (M σ : ℚ) (k : ℕ) (τ t : ℝ) : ℝ :=
  ptilde3 M σ k τ t / Real.sqrt (Pi3 M σ k t)

lemma edgeEnv3_nonneg (M σ : ℚ) (x t : ℝ) : 0 ≤ edgeEnv3 M σ x t := Real.sqrt_nonneg _

lemma Gc3_eq_env (M σ : ℚ) (k : ℕ) (x t : ℝ) :
    Gc3 M σ k x t = edgeEnv3 M σ x t * H3 M σ k ((1 - x) / 2) t := by
  unfold Gc3 edgeEnv3 H3 Pi3
  ring

lemma Pi3_zero (M σ : ℚ) (k : ℕ) : Pi3 M σ k 0 = 1 := by
  simp [Pi3, Ct_zero_t]

/-! ### The coefficients as polynomials in `τ` -/

lemma ptilde3_eq_sum (M σ : ℚ) (k : ℕ) (τ t : ℝ) :
    ptilde3 M σ k τ t =
      ∑ m ∈ Finset.range (k + 1), eval t ((ptilde3Poly M σ k).coeff m) * τ ^ m := by
  rw [ptilde3_eq_evalP, evalP, evP]
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom]
  have hdeg : ((ptilde3Poly M σ k).map (evalRingHom t)).natDegree < k + 1 :=
    lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le (natDegree_ptilde3Poly_le M σ k))
  rw [eval_eq_sum_range' hdeg]
  simp [coeff_map]

/-- `g_m(t) = [τ^m] P̃(τ;t) / √(Π_L(t))`. -/
noncomputable def g3 (M σ : ℚ) (k m : ℕ) (t : ℝ) : ℝ :=
  eval t ((ptilde3Poly M σ k).coeff m) / Real.sqrt (Pi3 M σ k t)

lemma H3_eq_sum (M σ : ℚ) (k : ℕ) (τ t : ℝ) :
    H3 M σ k τ t = ∑ m ∈ Finset.range (k + 1), τ ^ m * g3 M σ k m t := by
  unfold H3 g3
  rw [ptilde3_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

lemma analyticAt_Pi3 (M σ : ℚ) (k : ℕ) (t : ℝ) :
    AnalyticAt ℝ (fun s => Pi3 M σ k s) t :=
  analyticAt_Ct_comp_3j _ analyticAt_const analyticAt_id

lemma analyticAt_g3 (M σ : ℚ) (k m : ℕ) :
    AnalyticAt ℝ (g3 M σ k m) 0 := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => eval t ((ptilde3Poly M σ k).coeff m)) 0 :=
    (AnalyticOnNhd.eval_polynomial _) 0 (mem_univ _)
  have h2 := analyticAt_sqrt_comp_3j (analyticAt_Pi3 M σ k 0) (by simp [Pi3_zero])
  have h3 : Real.sqrt (Pi3 M σ k 0) ≠ 0 := by simp [Pi3_zero]
  exact h1.div h2 h3

/-- **The polynomial `s_r(τ)`** of `thm:uniformedge` (a): the `t^r` Taylor coefficient of
`H(τ,t) = P̃_L(τ;t)/√Π_L(t)`, written as `∑_{m ≤ k} (t^r-coefficient of g_m) τ^m`. -/
noncomputable def edgeS3 (M σ : ℚ) (k r : ℕ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (k + 1), C (iteratedDeriv r (g3 M σ k m) 0 / (r.factorial : ℝ)) * X ^ m

theorem natDegree_edgeS3_le (M σ : ℚ) (k r : ℕ) : (edgeS3 M σ k r).natDegree ≤ k := by
  unfold edgeS3
  refine natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
  have hm' : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (natDegree_C_mul_X_pow_le _ _).trans hm'

theorem taylorCoeff_H3_eq_edgeS3 (M σ : ℚ) (k r : ℕ) (τ : ℝ) :
    taylorCoeff (fun τ t => H3 M σ k τ t) r τ = (edgeS3 M σ k r).eval τ := by
  unfold taylorCoeff edgeS3
  beta_reduce
  have hf : (fun t => H3 M σ k τ t) = fun t => ∑ m ∈ Finset.range (k + 1), τ ^ m * g3 M σ k m t := by
    funext t; exact H3_eq_sum M σ k τ t
  rw [hf, iteratedDeriv_fun_sum (f := fun m t => τ ^ m * g3 M σ k m t)
    (fun m _ => contDiffAt_const.mul (analyticAt_g3 M σ k m).contDiffAt)]
  have hm : ∀ m ∈ Finset.range (k + 1),
      iteratedDeriv r (fun t => τ ^ m * g3 M σ k m t) 0 = τ ^ m * iteratedDeriv r (g3 M σ k m) 0 := by
    intro m _
    rw [iteratedDeriv_const_mul_fun]
  rw [Finset.sum_congr rfl hm, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- `W_{3j} s_0 = d`: `edgeEnv3 · s_0 = dZero3` at `t = 0` (with `d` the `t = 0` carrier). -/
theorem edgeEnv3_mul_edgeS3_zero (M σ : ℚ) (k : ℕ) (x : ℝ) :
    edgeEnv3 M σ x 0 * (edgeS3 M σ k 0).eval ((1 - x) / 2) = dZero3 M σ k x := by
  rw [← taylorCoeff_H3_eq_edgeS3]
  unfold taylorCoeff
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  unfold H3 edgeEnv3 dZero3
  rw [Pi3_zero]
  simp [Ct_zero_t]

/-! ### `thm:uniformedge` (a) -/

/-- `0 < Π_L(t)` is an open condition; `H` is analytic on it. -/
lemma H3_analyticOnNhd (M σ : ℚ) (k : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ × ℝ => H3 M σ k q.1 q.2) {q : ℝ × ℝ | 0 < Pi3 M σ k q.2} := by
  intro q hq
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => ptilde3 M σ k q.1 q.2) q := analyticAt_ptilde3 M σ k q
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℝ => Pi3 M σ k q.2) q :=
    (analyticAt_Pi3 M σ k q.2).comp_of_eq analyticAt_snd rfl
  have h3 := analyticAt_sqrt_comp_3j h2 hq
  exact h1.div h3 (Real.sqrt_pos.mpr hq).ne'

lemma Pi3_open (M σ : ℚ) (k : ℕ) : IsOpen {q : ℝ × ℝ | 0 < Pi3 M σ k q.2} := by
  have : Continuous (fun q : ℝ × ℝ => Pi3 M σ k q.2) :=
    continuous_iff_continuousAt.mpr fun q =>
      ((analyticAt_Pi3 M σ k q.2).comp_of_eq analyticAt_snd rfl).continuousAt
  exact isOpen_lt continuous_const this

/-- **`thm:uniformedge` (a), `eq:3juniformedge`** (proved).  Fix `L = L₀ + k`, `M`, `σ`, `R`.
There are `C, N₀` such that for every admissible `N ≥ N₀` and **every** physical lattice point `μ`
(no restriction on `x = 2μ/N`, up to the edges), with `τ = (1-x)/2` and `t = N⁻²`,
`|Φ_L^{M,σ} - E_N W_{3j} ∑_{r<R} s_r(τ) N^{-2r}| ≤ C · E_N W_{3j} · N^{-2R}`,
where `E_N W_{3j} = edgeEnv3 M σ x N⁻²` and `s_r = edgeS3 M σ k r` has degree `≤ k` in `τ`
(`natDegree_edgeS3_le`) and `W_{3j} s_0 = dZero3` (`edgeEnv3_mul_edgeS3_zero`). -/
theorem Phi3j_uniform_edge (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (R : ℕ) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      |Phi3j L M σ N μ - edgeEnv3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) *
          ∑ r ∈ Finset.range R,
            (edgeS3 M σ k r).eval ((1 - 2 * (μ : ℝ) / N) / 2) / (N : ℝ) ^ (2 * r)| ≤
        C * edgeEnv3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) / (N : ℝ) ^ (2 * R) := by
  subst hL
  have hKU : (Icc (0 : ℝ) 1) ×ˢ ({0} : Set ℝ) ⊆ {q : ℝ × ℝ | 0 < Pi3 M σ k q.2} := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have : t = 0 := ht
    subst this
    show 0 < Pi3 M σ k 0
    rw [Pi3_zero]; exact one_pos
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic (Pi3_open M σ k) (H3_analyticOnNhd M σ k)
    isCompact_Icc hKU R
  refine ⟨C, max (((max |M| |σ| + k + 1 : ℚ)) : ℝ) (max 1 (1 / ρ)), ?_⟩
  intro N μ hA hlat hN0
  have hN1 : ((max |M| |σ| + k + 1 : ℚ) : ℝ) ≤ N := le_trans (le_max_left _ _) hN0
  have hN2 : max 1 (1 / ρ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN0
  have hk : max |M| |σ| + k + 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hN2)
  have hNq : 0 < N := by exact_mod_cast hNpos
  have hx := hlat.x_mem_Icc hNq
  have hτ : (1 - 2 * (μ : ℝ) / N) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have ht : |1 / (N : ℝ) ^ 2| ≤ ρ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : 1 / ρ ≤ N := le_trans (le_max_right _ _) hN2
    have h2 : (1 : ℝ) ≤ N := le_trans (le_max_left _ _) hN2
    have h3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have h4 : 1 / ρ ≤ N ^ 2 := le_trans h1 h3
    rw [div_le_iff₀ hρ] at h4
    linarith
  have key := hC _ hτ _ ht
  rw [Phi3j_eq_Gc3_spec M σ N μ hA hNq hlat k hk, Gc3_eq_env]
  set E := edgeEnv3 M σ (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) with hE
  have e1 : ∀ r : ℕ, (edgeS3 M σ k r).eval ((1 - 2 * (μ : ℝ) / N) / 2) / (N : ℝ) ^ (2 * r) =
      taylorCoeff (fun τ t => H3 M σ k τ t) r ((1 - 2 * (μ : ℝ) / N) / 2) *
        (1 / (N : ℝ) ^ 2) ^ r := by
    intro r
    rw [taylorCoeff_H3_eq_edgeS3, one_div, inv_pow, ← pow_mul, div_eq_mul_inv]
  simp only [e1]
  have e2 : |1 / (N : ℝ) ^ 2| ^ R = 1 / (N : ℝ) ^ (2 * R) := by
    rw [abs_of_nonneg (by positivity), one_div, inv_pow, ← pow_mul, one_div]
  rw [e2] at key
  have hE0 : 0 ≤ E := edgeEnv3_nonneg _ _ _ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hE0]
  calc E * |H3 M σ k ((1 - 2 * (μ : ℝ) / N) / 2) (1 / (N : ℝ) ^ 2) -
        ∑ r ∈ Finset.range R, taylorCoeff (fun τ t => H3 M σ k τ t) r ((1 - 2 * (μ : ℝ) / N) / 2) *
          (1 / (N : ℝ) ^ 2) ^ r|
      ≤ E * (C * (1 / (N : ℝ) ^ (2 * R))) := mul_le_mul_of_nonneg_left key hE0
    _ = C * E / (N : ℝ) ^ (2 * R) := by ring

/-- info: 'FormalResearch.Racah.taylorCoeff_H3_eq_edgeS3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taylorCoeff_H3_eq_edgeS3

/-- info: 'FormalResearch.Racah.natDegree_edgeS3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms natDegree_edgeS3_le

/-- info: 'FormalResearch.Racah.edgeEnv3_mul_edgeS3_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeEnv3_mul_edgeS3_zero

/-- info: 'FormalResearch.Racah.Phi3j_uniform_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_uniform_edge

end FormalResearch.Racah

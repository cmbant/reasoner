module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryMid

/-!
# The smooth part of the site weight: `(S)` of Proposition 1.2(2) (`rem:P1.2`, Step 2)

With `K = langerK x` (the smooth part `𝒦(x, ·)` of `(F2)`) and `K_*(x) = K(x, ξ_*)`:
`Sm_K := K(x, χ'_1) + 2 ∑_{k=2}^K K(x, χ'_k) - 2 ∫_{1/4}^{K+1/2} K(x, χ_a) da` satisfies
`|Sm_K + (3/2) K_*(x)| ≤ C λ` uniformly in `K ≥ 1`, in `x ∈ [ξ_*/2, ξ_* + 1/2]` and in the design, and
`Sm_K` converges as `K → ∞` (`sm_design`).
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb

/-- The smooth kernel `𝒦(x, ·)` satisfies `KernelHyp` with a constant uniform in `x ∈ X`. -/
theorem kernelHyp_langerK :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ langerX (1 / 2), KernelHyp (langerK x) A := by
  obtain ⟨C, hC, hb⟩ := langerK_deriv_bounds (1 / 2) (by norm_num)
  refine ⟨C, hC.le, fun x hx => ?_⟩
  have hx0 : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have h2 : ContDiffOn ℝ 2 (langerK x) (Ioi 0) := by
    simpa using contDiffOn_langerK 2 hx0
  have h2' : ContDiffOn ℝ (((1 : ℕ) + 1 : ℕ) : WithTop ℕ∞) (langerK x) (Ioi 0) := by simpa using h2
  rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at h2'
  obtain ⟨hd, _, h1⟩ := h2'
  have h1' : ContDiffOn ℝ (((0 : ℕ) + 1 : ℕ) : WithTop ℕ∞) (deriv (langerK x)) (Ioi 0) := by simpa using h1
  rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at h1'
  obtain ⟨hd1, _, h0⟩ := h1'
  refine ⟨hC.le, fun y hy => (hd y hy).differentiableAt (isOpen_Ioi.mem_nhds hy) |>.hasDerivAt,
    fun y hy => (hd1 y hy).differentiableAt (isOpen_Ioi.mem_nhds hy) |>.hasDerivAt, ?_,
    fun y hy => (hb x hx y hy).1, fun y hy => (hb x hx y hy).2⟩
  simpa using h0.continuousOn

/-- Integrability of `a ↦ G(χ_a)` on `[a, b] ⊂ [1/4, ∞)`. -/
lemma intervalIntegrable_comp_chi {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ} {A : ℝ} (hG : KernelHyp G A)
    {a b : ℝ} (ha : 1 / 4 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => G (chiQuantile c' t)) volume a b := by
  refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
  intro t ht
  have h14 : 1 / 4 ≤ t := ha.trans ht.1
  have hy : 0 < chiQuantile c' t := lt_of_lt_of_le xiStar_pos (chiQuantile_spec hc' h14).1
  exact ((hG.d1 _ hy).continuousAt.comp_continuousWithinAt
    ((continuousOn_chiQuantile hc').mono (fun s hs => show 1 / 4 ≤ s from ha.trans hs.1) t ht))

/-- Splitting `∫_{1/4}^{K+1/2}` into the head and the cells. -/
lemma integral_split_cells {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ} {A : ℝ} (hG : KernelHyp G A) (K : ℕ)
    (hK : 1 ≤ K) :
    (∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), G (chiQuantile c' a)) =
      (∫ a in (1 / 4 : ℝ)..(3 / 2), G (chiQuantile c' a)) +
        ∑ k ∈ Finset.Icc 2 K, ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), G (chiQuantile c' a) := by
  induction K, hK using Nat.le_induction with
  | base => simp; norm_num
  | succ K hK ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have e1 : ((K + 1 : ℕ) : ℝ) + 1 / 2 = ((K : ℝ) + 1 / 2) + 1 := by push_cast; ring
    have e2 : ((K + 1 : ℕ) : ℝ) - 1 / 2 = (K : ℝ) + 1 / 2 := by push_cast; ring
    rw [e2, e1]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_comp_chi hc' hG (by norm_num) (by linarith))
      (intervalIntegrable_comp_chi hc' hG (by linarith) (by linarith))).symm

lemma sum_range_add_two (g : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.range n, g (m + 2) = ∑ k ∈ Finset.Icc 2 (n + 1), g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (a := 2) (b := n + 1) (by omega)]

/-- `Sm_K = K(x, χ'_1) + 2 ∑_{k=2}^K K(x, χ'_k) - 2 ∫_{1/4}^{K+1/2} K(x, χ_a) da`. -/
noncomputable def smPartial (c' : ℝ) (σ : ℕ → ℝ) (x : ℝ) (K : ℕ) : ℝ :=
  langerK x (siteX c' σ 1) + 2 * ∑ k ∈ Finset.Icc 2 K, langerK x (siteX c' σ k) -
    2 * ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), langerK x (chiQuantile c' a)

/-- The `k`-th increment `2 (K(x, χ'_k) - ∫_{k-1/2}^{k+1/2} K(x, χ_a) da)`. -/
noncomputable def smTerm (c' : ℝ) (σ : ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  2 * (langerK x (siteX c' σ k) -
    ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' a))

/-- **(S)** (`rem:P1.2`(2), Step 2): `Sm_K` converges as `K → ∞` to a limit within `C λ` of `-(3/2) 𝒦_*(x)`;
the same bound holds for every `Sm_K`, `K ≥ 1`. -/
theorem sm_design (Csh : ℝ) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {csep : ℝ} {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2),
      (∀ K : ℕ, 1 ≤ K → |smPartial c' σ x K + 3 / 2 * langerK x xiStar| ≤ C * lambdaComb c') ∧
      ∃ S : ℝ, Tendsto (smPartial c' σ x) atTop (𝓝 S) ∧ |S + 3 / 2 * langerK x xiStar| ≤ C * lambdaComb c' := by
  obtain ⟨A, hA, hK⟩ := kernelHyp_langerK
  obtain ⟨Cm, c0, hCm, hc0, hmid⟩ := midpoint_sum_le
  obtain ⟨cτ, hcτ, _, hX⟩ := siteX_sub_chi
  have hZ0 := kernZ_nonneg
  refine ⟨A * (2 * |Csh| * kernZ / cτ + 2 * Cm + |Csh| / cτ + 5) + 1, c0, by positivity, hc0, ?_⟩
  intro c' hc' csep σ η h x hx
  have hc'0 : 0 < c' := lt_of_lt_of_le hc0 hc'
  have hlam := lamPos hc'0
  have hG := hK x hx
  set C := A * (2 * |Csh| * kernZ / cτ + 2 * Cm + |Csh| / cτ + 5) + 1 with hC
  have hZ := kernZ_nonneg
  -- site displacement: `|K(x, χ'_k) - K(x, χ_k)| ≤ A λ |Csh| k^{-4/3} / cτ`
  have hdisp : ∀ k : ℕ, 1 ≤ k →
      |langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ))| ≤
        A * (lambdaComb c' * (|Csh| / cτ) * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
    intro k hk
    have hk14 : (1 / 4 : ℝ) ≤ k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h1 := hX hc'0 σ k hk (h.nonneg k hk)
    have h2 := h.near k hk
    have hxs1 := xiStar_le_siteX hc'0 (σ := σ) (h.nonneg k hk)
    have hxs2 := (chiQuantile_spec hc'0 hk14).1
    refine (hG.lipschitz hxs1 hxs2).trans ?_
    have h3 : |siteX c' σ k - chiQuantile c' (k : ℝ)| ≤
        lambdaComb c' * (|Csh| / cτ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
      refine h1.trans ?_
      have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      calc lambdaComb c' * |σ k - phiQuantile (k : ℝ)| / cτ
          ≤ lambdaComb c' * (|Csh| * (k : ℝ) ^ (-(4 / 3 : ℝ))) / cτ := by
            gcongr
            exact h2.trans (by gcongr; exact le_abs_self _)
        _ = _ := by ring
    gcongr
  have hsumdisp : ∀ K : ℕ, ∑ k ∈ Finset.Icc 2 K,
      |langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ))| ≤
        A * (lambdaComb c' * (|Csh| / cτ) * kernZ) := by
    intro K
    calc _ ≤ ∑ k ∈ Finset.Icc 2 K, A * (lambdaComb c' * (|Csh| / cτ) * kern k) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
          rw [kern_eq_rpow hk1]
          exact hdisp k hk1
      _ = A * (lambdaComb c' * (|Csh| / cτ)) * ∑ k ∈ Finset.Icc 2 K, kern k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ A * (lambdaComb c' * (|Csh| / cτ)) * kernZ := by
          gcongr
          calc ∑ k ∈ Finset.Icc 2 K, kern k ≤ ∑ k ∈ Finset.Icc 1 K, kern k :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.Icc_subset_Icc (by norm_num) le_rfl) (fun i _ _ => kern_nonneg i)
            _ ≤ kernZ := sum_kern_le K
      _ = _ := by ring
  -- the cells
  have hcells := hmid hc' hG
  -- the term bound
  have hterm : ∀ K : ℕ, ∑ k ∈ Finset.Icc 2 K, |smTerm c' σ x k| ≤
      2 * (A * (lambdaComb c' * (|Csh| / cτ) * kernZ)) + 2 * (Cm * A * lambdaComb c') := by
    intro K
    calc ∑ k ∈ Finset.Icc 2 K, |smTerm c' σ x k|
        ≤ ∑ k ∈ Finset.Icc 2 K, (2 * |langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ))| +
          2 * |langerK x (chiQuantile c' (k : ℝ)) -
            ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' t)|) := by
          refine Finset.sum_le_sum fun k hk => ?_
          unfold smTerm
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have := abs_add_le (langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ)))
            (langerK x (chiQuantile c' (k : ℝ)) -
              ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' t))
          have e : langerK x (siteX c' σ k) - ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
              langerK x (chiQuantile c' t) = (langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ))) +
              (langerK x (chiQuantile c' (k : ℝ)) -
                ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' t)) := by ring
          rw [e]
          linarith
      _ = 2 * ∑ k ∈ Finset.Icc 2 K, |langerK x (siteX c' σ k) - langerK x (chiQuantile c' (k : ℝ))| +
          2 * ∑ k ∈ Finset.Icc 2 K, |langerK x (chiQuantile c' (k : ℝ)) -
            ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' t)| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          have := hsumdisp K
          have := hcells K
          linarith
  have hhead : |langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
      3 / 2 * langerK x xiStar| ≤ A * (lambdaComb c' * (|Csh| / cτ)) + 5 * A * lambdaComb c' := by
    have h1 := hdisp 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h1
    have h2 := midpoint_head_le hc'0 hG
    have e : langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
        3 / 2 * langerK x xiStar = (langerK x (siteX c' σ 1) - langerK x (chiQuantile c' 1)) +
        (langerK x (chiQuantile c' 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
          3 / 2 * langerK x xiStar) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hident : ∀ K : ℕ, 1 ≤ K → smPartial c' σ x K =
      (langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a))) +
        ∑ k ∈ Finset.Icc 2 K, smTerm c' σ x k := by
    intro K hK
    unfold smPartial smTerm
    rw [integral_split_cells hc'0 hG K hK]
    have : ∑ k ∈ Finset.Icc 2 K, 2 * (langerK x (siteX c' σ k) -
        ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' a)) =
        2 * ∑ k ∈ Finset.Icc 2 K, langerK x (siteX c' σ k) -
          2 * ∑ k ∈ Finset.Icc 2 K, ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), langerK x (chiQuantile c' a) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    rw [this]
    ring
  -- summability
  have hnn : ∀ m : ℕ, 0 ≤ |smTerm c' σ x (m + 2)| := fun m => abs_nonneg _
  have hrange : ∀ n : ℕ, ∑ m ∈ Finset.range n, |smTerm c' σ x (m + 2)| ≤
      2 * (A * (lambdaComb c' * (|Csh| / cτ) * kernZ)) + 2 * (Cm * A * lambdaComb c') := by
    intro n
    rw [sum_range_add_two (fun k => |smTerm c' σ x k|) n]
    exact hterm (n + 1)
  have hsabs : Summable (fun m : ℕ => |smTerm c' σ x (m + 2)|) := summable_of_sum_range_le hnn hrange
  have hsumm : Summable (fun m : ℕ => smTerm c' σ x (m + 2)) := hsabs.of_abs
  have htsum : |∑' m : ℕ, smTerm c' σ x (m + 2)| ≤
      2 * (A * (lambdaComb c' * (|Csh| / cτ) * kernZ)) + 2 * (Cm * A * lambdaComb c') := by
    have h1 : ‖∑' m : ℕ, smTerm c' σ x (m + 2)‖ ≤ ∑' m : ℕ, ‖smTerm c' σ x (m + 2)‖ :=
      norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsabs)
    simp only [Real.norm_eq_abs] at h1
    exact h1.trans (Real.tsum_le_of_sum_range_le hnn hrange)
  have hbnd : A * (lambdaComb c' * (|Csh| / cτ)) + 5 * A * lambdaComb c' +
      (2 * (A * (lambdaComb c' * (|Csh| / cτ) * kernZ)) + 2 * (Cm * A * lambdaComb c')) ≤
      C * lambdaComb c' := by
    rw [hC]
    have : 0 ≤ lambdaComb c' := hlam.le
    have e : A * (lambdaComb c' * (|Csh| / cτ)) + 5 * A * lambdaComb c' +
      (2 * (A * (lambdaComb c' * (|Csh| / cτ) * kernZ)) + 2 * (Cm * A * lambdaComb c')) =
      A * (2 * |Csh| * kernZ / cτ + 2 * Cm + |Csh| / cτ + 5) * lambdaComb c' := by ring
    rw [e]
    nlinarith
  refine ⟨fun K hK => ?_, ?_⟩
  · rw [hident K hK]
    have e : langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
        ∑ k ∈ Finset.Icc 2 K, smTerm c' σ x k + 3 / 2 * langerK x xiStar =
        (langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
          3 / 2 * langerK x xiStar) + ∑ k ∈ Finset.Icc 2 K, smTerm c' σ x k := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    refine le_trans (add_le_add hhead ((Finset.abs_sum_le_sum_abs _ _).trans (hterm K))) hbnd
  · refine ⟨(langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a))) +
      ∑' m : ℕ, smTerm c' σ x (m + 2), ?_, ?_⟩
    · have h1 := hsumm.hasSum.tendsto_sum_nat
      have h2 : Tendsto (fun n : ℕ => smPartial c' σ x (n + 1)) atTop
          (𝓝 ((langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2),
            langerK x (chiQuantile c' a))) + ∑' m : ℕ, smTerm c' σ x (m + 2))) := by
        refine (h1.const_add _).congr fun n => ?_
        rw [hident (n + 1) (by omega), sum_range_add_two (fun k => smTerm c' σ x k) n]
      exact (tendsto_add_atTop_iff_nat 1).mp h2
    · have e : (langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a))) +
          ∑' m : ℕ, smTerm c' σ x (m + 2) + 3 / 2 * langerK x xiStar =
          (langerK x (siteX c' σ 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), langerK x (chiQuantile c' a)) +
            3 / 2 * langerK x xiStar) + ∑' m : ℕ, smTerm c' σ x (m + 2) := by ring
      rw [e]
      exact le_trans ((abs_add_le _ _).trans (add_le_add hhead htsum)) hbnd

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.sm_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sm_design

end FormalResearch.ModularBootstrap.Upper.Ramped

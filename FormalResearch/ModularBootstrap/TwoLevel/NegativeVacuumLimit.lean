module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumFamily
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimum

/-!
# The limit window `f_K` and the convergence of the node values (Theorem 2.5, Step 1)

* `windowF_eq_winC`: `f_K = winC z₁ u₂ (siteLim α K) 0` (the Airy product with zero widths) on `ℂ`;
* `windowInt_eq_sum`: `∫ f_K = Σ_{n ≤ K} Re nodeC z₁ u₂ (siteLim α K) 0 n` (node values vanish for `n > K`);
* `tendsto_nodeC`: for `n ≤ K` the node values of the designs `negDesign α K (K + j) η_j q` converge to those of the
  limit data as `η_j → 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

/-- Two continuous functions agreeing off the real axis agree. -/
lemma eq_of_forall_im_ne_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ u : ℂ, u.im ≠ 0 → f u = g u) : f = g := by
  funext u
  by_cases hu : u.im = 0
  · have hz : Tendsto (fun m : ℕ => u + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) atTop (𝓝 u) := by
      have h1 : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rwa [Complex.ofReal_zero] at this
      simpa using (tendsto_const_nhds (x := u)).add (tendsto_const_nhds.mul h1)
    have e : ∀ m : ℕ, f (u + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) =
        g (u + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) := by
      intro m
      refine h _ ?_
      simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, one_mul, zero_add, mul_zero, hu]
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    exact tendsto_nhds_unique (hf.continuousAt.tendsto.comp hz) ((hg.continuousAt.tendsto.comp hz).congr
      fun m => (e m).symm)
  · exact h u hu

lemma prod_Icc_one_two_mul (K : ℕ) (hK : 2 ≤ K) (f : ℕ → ℂ) :
    (∏ k ∈ Finset.Icc 1 2, f k) * ∏ k ∈ Finset.Icc 3 K, f k = ∏ k ∈ Finset.Icc 1 K, f k := by
  have h1 : Finset.Icc 1 2 = Finset.Ioc 0 2 := by ext; simp; omega
  have h2 : Finset.Icc 3 K = Finset.Ioc 2 K := by ext; simp; omega
  have h3 : Finset.Icc 1 K = Finset.Ioc 0 K := by ext; simp; omega
  rw [h1, h2, h3]
  exact Finset.prod_Ioc_consecutive f (by norm_num) hK

lemma airyProdTail_siteLim {α : ℝ} {K : ℕ} (hK : 3 ≤ K) {u : ℂ} (hu : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ)) :
    airyProdTail 2 (siteLim α K) (fun _ => 0) u =
      ∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ)) ^ 2 / (u - (airyZero k : ℂ)) ^ 2 := by
  unfold airyProdTail
  have hf : ∀ m : ℕ, airyProdFactor (siteLim α K) (fun _ => 0) (2 + 1 + m) u =
      if m < K - 2 then (u - (clarkNode α (3 + m) : ℂ)) ^ 2 / (u - (airyZero (3 + m) : ℂ)) ^ 2 else 1 := by
    intro m
    unfold airyProdFactor siteLim idealLim
    have hne : u - (airyZero (2 + 1 + m) : ℂ) ≠ 0 := sub_ne_zero.mpr (hu _ (by omega))
    by_cases h : m < K - 2
    · simp only [show 3 ≤ 2 + 1 + m by omega, ↓reduceIte, show 2 + 1 + m ≤ K by omega, h,
        show 2 + 1 + m = 3 + m by ring]
      push_cast
      simp
    · simp only [show 3 ≤ 2 + 1 + m by omega, ↓reduceIte, show ¬(2 + 1 + m ≤ K) by omega, h]
      push_cast
      have hne' : u - (airyZero (3 + m) : ℂ) ≠ 0 := by
        simpa [show 2 + 1 + m = 3 + m by ring] using hne
      rw [div_eq_one_iff_eq (pow_ne_zero 2 hne')]
      simp
  rw [tprod_congr hf, tprod_eq_prod (s := Finset.range (K - 2)) (fun m hm => by
    simp only [Finset.mem_range] at hm; simp [hm])]
  have : ∀ m ∈ Finset.range (K - 2), (if m < K - 2 then (u - (clarkNode α (3 + m) : ℂ)) ^ 2 /
      (u - (airyZero (3 + m) : ℂ)) ^ 2 else 1) = (u - (clarkNode α (3 + m) : ℂ)) ^ 2 /
      (u - (airyZero (3 + m) : ℂ)) ^ 2 := fun m hm => by simp [Finset.mem_range.1 hm]
  rw [Finset.prod_congr rfl this]
  have h2 : Finset.Icc 3 K = Finset.Ico 3 (K + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, Finset.prod_Ico_eq_prod_range (fun k => (u - (clarkNode α k : ℂ)) ^ 2 / (u - (airyZero k : ℂ)) ^ 2)]
  have : K + 1 - 3 = K - 2 := by omega
  rw [this]

/-- `f_K` is the Airy product with zero widths. -/
theorem windowF_eq_winC (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    windowF α K u₂ = winC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) := by
  have hdiff : Differentiable ℂ (winC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0)) := by
    unfold winC
    exact (differentiable_id.sub_const _).neg.mul
      (airyWindowProd_differentiable 2 (by norm_num) u₂ _ _ (tailHyp_siteLim α hK))
  refine eq_of_forall_im_ne_zero (differentiable_windowF α K u₂).continuous hdiff.continuous fun u hu => ?_
  have hne : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ) := fun k _ h => hu (by rw [h]; simp)
  have hD : windowD K u ≠ 0 := by
    unfold windowD
    refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hne k (Finset.mem_Icc.mp hk).1)
  have hspec := windowF_spec α K u₂ u
  have hD2 : windowD K u ^ 2 ≠ 0 := pow_ne_zero 2 hD
  refine mul_right_cancel₀ hD2 ?_
  rw [← hspec]
  unfold winC
  rw [airyWindowProd_eq_of_ne 2 u₂ _ _ hne, airyProdTail_siteLim hK hne]
  unfold windowN windowD
  rw [← prod_Icc_one_two_mul K (by omega)]
  rw [Finset.prod_div_distrib]
  have h1 : ∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ)) ^ 2 =
      (∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ))) ^ 2 := Finset.prod_pow _ _ _
  have h2 : ∏ k ∈ Finset.Icc 3 K, (u - (airyZero k : ℂ)) ^ 2 =
      (∏ k ∈ Finset.Icc 3 K, (u - (airyZero k : ℂ))) ^ 2 := Finset.prod_pow _ _ _
  have h3 : ∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ)) ^ 2 =
      (∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ))) ^ 2 := Finset.prod_pow _ _ _
  have hA : (∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hne k (Finset.mem_Icc.mp hk).1)
  have hB : (∏ k ∈ Finset.Icc 3 K, (u - (airyZero k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hne k (by have := (Finset.mem_Icc.mp hk).1; omega))
  rw [h1, h2, h3, mul_pow]
  field_simp

/-- The node values of the limit data vanish for `n > K` (the `n`-th pair sits at `a_n` with zero width). -/
lemma nodeC_lim_eq_zero (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (p q : ℝ) {n : ℕ} (hn : K < n) :
    nodeC p q (siteLim α K) (fun _ => 0) n = 0 :=
  nodeC_idealLim_eq_zero (clarkNode α) (by omega) p q hn

/-- **`∫ f_K` as a finite sum of node values.** -/
theorem windowInt_eq_sum (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    windowInt α K u₂ = ∑ m ∈ Finset.range K,
      (nodeC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) (m + 1)).re := by
  obtain ⟨C, hC, hb⟩ := windowF_bound α hK u₂
  have hb' : ∀ u : ℂ, ‖windowF α K u₂ u‖ ≤ C * (1 + ‖u‖) ^ (-(5 / 2) : ℝ) * airyEnv u := hb
  have h := airy_quadrature (differentiable_windowF α K u₂) hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb'
  have hfi := airy_integrable_real (differentiable_windowF α K u₂) hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb'
  have hre := Complex.hasSum_re h
  have hint : (∫ x : ℝ, windowF α K u₂ (x : ℂ)).re = windowInt α K u₂ := by
    unfold windowInt
    simpa using (integral_re hfi).symm
  rw [hint] at hre
  have hterm : ∀ m : ℕ, (windowF α K u₂ (airyZero (m + 1) : ℂ) /
      (deriv airyAiC (airyZero (m + 1) : ℂ)) ^ 2).re =
      (nodeC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) (m + 1)).re := by
    intro m
    rw [windowF_eq_winC α hK u₂, winC_node _ _ _ _ (by omega)]
  have hre' : HasSum (fun m : ℕ => (nodeC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) (m + 1)).re)
      (windowInt α K u₂) := by
    convert hre using 1
    funext m; exact (hterm m).symm
  have hfin : HasSum (fun m : ℕ => (nodeC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) (m + 1)).re)
      (∑ m ∈ Finset.range K, (nodeC (clarkNode α 1) u₂ (siteLim α K) (fun _ => 0) (m + 1)).re) := by
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [nodeC_lim_eq_zero α hK _ _ (by simp only [Finset.mem_range] at hm; omega)]
    simp
  exact hre'.unique hfin

section Convergence

variable (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {nj : ℕ → ℕ} {η : ℕ → ℝ}

/-- **Convergence of the node values for `n ≤ K`.**  As `η_j → 0` and `n_j → ∞` the node values of the designs
`(p, q, S, W) = (z₁ - η_j, q, siteSeq α K n_j, widthSeq n_j η_j)` tend to those of the limit data
`(z₁, q, siteLim α K, 0)`.  (The case `p_j → p`, arbitrary sites and every `n ≥ 1` is `IdealApprox.tendsto_nodeC`.) -/
theorem tendsto_nodeC {n : ℕ} (hn : 1 ≤ n) (_hnK : n ≤ K) (q : ℝ) (_hnj : ∀ j, K ≤ nj j)
    (hnjt : Tendsto nj atTop atTop) (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1 / 4)
    (hηt : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun j => nodeC (clarkNode α 1 - η j) q (siteSeq α K (nj j)) (widthSeq (nj j) (η j)) n) atTop
      (𝓝 (nodeC (clarkNode α 1) q (siteLim α K) (fun _ => 0) n)) := by
  have hU := unifTail_ideal (clarkNode α) K nj η hη0 (fun j => (hη1 j).trans (by norm_num))
  have hp : Tendsto (fun j => clarkNode α 1 - η j) atTop (𝓝 (clarkNode α 1)) := by
    simpa using (tendsto_const_nhds (x := clarkNode α 1)).sub hηt
  exact IdealApprox.tendsto_nodeC hU hp (idealLim (clarkNode α) K) (fun _ => 0)
    (fun k hk => tendsto_idealSite (clarkNode α) K hnjt hk) (fun k hk => tendsto_idealWidth hnjt hηt hk) hn

end Convergence

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.windowF_eq_winC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowF_eq_winC

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.windowInt_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowInt_eq_sum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum.tendsto_nodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_nodeC

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

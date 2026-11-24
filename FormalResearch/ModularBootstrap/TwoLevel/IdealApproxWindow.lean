module

public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxFactor

/-!
# Window of an approximating design: local bound and pointwise limit (`virasoro_two_level.tex`, `gt:2.6`)

For `N ≥ 2` the complex window `winC p q S W = -(u - p) W^{(2)}(u)` of sites `S` and widths `W` factors, off the Airy
zeros and then on all of `ℂ` near a point whose tail zeros `a_k`, `k > N`, are far away, as

`winC p q S W (u) = (u - p)(u - q) · H_N(u) · ∏_{k=3}^N ((u - S_k)² + W_k²) · ∏_{k > N} ((u - S_k)² + W_k²)/(u - a_k)²`,

with `H_N = Ai² / ∏_{k ≤ N}(u - a_k)²` entire (`airyH`).  A finite polynomial part times a tail that is uniformly close
to `1` gives:

* `exists_winC_bound`: for a `UnifTail` family, `‖winC p q (S j) (W j) x‖ ≤ M` for `|x| ≤ R`, all `j`;
* `tendsto_winC`: `winC p q (S j) (W j) x → winC p q S' W' x` for real `x` whenever the sites and widths converge
  (and `S' k = a_k`, `W' k = 0` beyond some index): at every real `x`, including the Airy zeros.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

lemma exists_airyH (N : ℕ) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ u, airyAiC u ^ 2 = H u * windowD N u ^ 2 := by
  refine FormalResearch.EntireDiv.entire_exists_div_sq (φ := fun u => airyAiC u ^ 2) (ψ := windowD N)
    (differentiable_airyAiC.pow 2) (differentiable_windowD N) ?_
  intro z hz
  unfold windowD at hz
  obtain ⟨k, hk, hzk⟩ := Finset.prod_eq_zero_iff.mp hz
  have hzk' : z = (airyZero k : ℂ) := sub_eq_zero.mp hzk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hA : airyAiC z = 0 := by rw [hzk']; exact airyAiC_airyZero k
  refine ⟨by simp [hA], ?_, ?_⟩
  · have hd : HasDerivAt (fun u => airyAiC u ^ 2) (2 * airyAiC z * deriv airyAiC z) z := by
      have h1 := (differentiable_airyAiC.differentiableAt (x := z)).hasDerivAt.fun_pow 2
      simpa using h1
    rw [hd.deriv, hA]; simp
  · have hfun : windowD N = fun u => (u - (airyZero k : ℂ)) *
        ∏ j ∈ (Finset.Icc 1 N).erase k, (u - (airyZero j : ℂ)) := by
      funext u; unfold windowD; rw [Finset.mul_prod_erase _ (fun j => u - (airyZero j : ℂ)) hk]
    have hd : HasDerivAt (windowD N) (∏ j ∈ (Finset.Icc 1 N).erase k, (z - (airyZero j : ℂ))) z := by
      rw [hfun]
      have h1 : HasDerivAt (fun u : ℂ => u - (airyZero k : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
      have h2 : Differentiable ℂ (fun u : ℂ => ∏ j ∈ (Finset.Icc 1 N).erase k, (u - (airyZero j : ℂ))) := by
        fun_prop
      have := h1.mul (h2.differentiableAt (x := z)).hasDerivAt
      convert this using 1
      rw [hzk']; simp
    rw [hd.deriv]
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)
    obtain ⟨hjk, hj'⟩ := Finset.mem_erase.mp hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj').1
    rw [hzk']
    intro h0
    have : airyZero k = airyZero j := Complex.ofReal_injective (sub_eq_zero.mp h0)
    exact hjk (airyZero_injective_on hj1 hk1 this.symm)

/-- `H_N = Ai² / ∏_{k ≤ N} (u - a_k)²`, entire. -/
noncomputable def airyH (N : ℕ) : ℂ → ℂ := Classical.choose (exists_airyH N)

lemma differentiable_airyH (N : ℕ) : Differentiable ℂ (airyH N) := (Classical.choose_spec (exists_airyH N)).1

lemma airyH_spec (N : ℕ) (u : ℂ) : airyAiC u ^ 2 = airyH N u * windowD N u ^ 2 :=
  (Classical.choose_spec (exists_airyH N)).2 u

/-- The finite polynomial part `∏_{k=3}^N ((u - S_k)² + W_k²)`. -/
noncomputable def finQ (S W : ℕ → ℝ) (N : ℕ) (u : ℂ) : ℂ :=
  ∏ k ∈ Finset.Icc 3 N, ((u - (S k : ℂ)) ^ 2 + (W k : ℂ) ^ 2)

lemma prod_Icc_three_range {M : Type*} [CommMonoid M] (K : ℕ) (f : ℕ → M) :
    ∏ k ∈ Finset.Icc 3 K, f k = ∏ m ∈ Finset.range (K - 2), f (3 + m) := by
  have h2 : Finset.Icc 3 K = Finset.Ico 3 (K + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, Finset.prod_Ico_eq_prod_range]
  have : K + 1 - 3 = K - 2 := by omega
  rw [this]

lemma windowD_split {N : ℕ} (hN : 2 ≤ N) (u : ℂ) :
    windowD N u = (∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ))) * ∏ k ∈ Finset.Icc 3 N, (u - (airyZero k : ℂ)) := by
  unfold windowD
  have h1 : Finset.Icc 1 2 = Finset.Ioc 0 2 := by ext; simp; omega
  have h2 : Finset.Icc 3 N = Finset.Ioc 2 N := by ext; simp; omega
  have h3 : Finset.Icc 1 N = Finset.Ioc 0 N := by ext; simp; omega
  rw [h1, h2, h3]
  exact (Finset.prod_Ioc_consecutive _ (by norm_num) hN).symm

lemma tailHyp_mono {S W : ℕ → ℝ} {f g : ℕ} (h : f ≤ g) (hH : AiryProdTailHypothesis f S W) :
    AiryProdTailHypothesis g S W := by
  obtain ⟨C, hC, hb⟩ := hH
  exact ⟨C, hC, fun k hk => hb k (lt_of_le_of_lt h hk)⟩

/-- **Factorisation of the window off the Airy zeros.** -/
lemma winC_eq_of_ne (p q : ℝ) {S W : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N) (hH : AiryProdTailHypothesis N S W)
    {u : ℂ} (hu : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ)) :
    winC p q S W u = (u - (p : ℂ)) * (u - (q : ℂ)) * airyH N u * finQ S W N u * airyProdTail N S W u := by
  have hp := hasProd_airyProdTail hH (fun k hk => hu k (by omega))
  have hsplit : airyProdTail 2 S W u =
      (∏ k ∈ Finset.Icc 3 N, airyProdFactor S W k u) * airyProdTail N S W u := by
    have hm : Multipliable (fun n : ℕ => airyProdFactor S W (2 + 1 + (n + (N - 2))) u) := by
      have : (fun n : ℕ => airyProdFactor S W (2 + 1 + (n + (N - 2))) u) =
          fun n => airyProdFactor S W (N + 1 + n) u := by
        funext n; congr 1; omega
      rw [this]; exact hp.multipliable
    have hmul := Multipliable.prod_mul_tprod_nat_mul' (f := fun m => airyProdFactor S W (2 + 1 + m) u)
      (k := N - 2) hm
    unfold airyProdTail
    rw [← hmul, prod_Icc_three_range N (fun k => airyProdFactor S W k u)]
    congr 1
    refine tprod_congr fun m => ?_
    congr 1; omega
  have hA12 : (∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr (hu k (Finset.mem_Icc.mp hk).1)
  have hA3 : (∏ k ∈ Finset.Icc 3 N, (u - (airyZero k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk =>
      sub_ne_zero.mpr (hu k (by have := (Finset.mem_Icc.mp hk).1; omega))
  unfold winC
  rw [airyWindowProd_eq_of_ne 2 q S W hu, hsplit]
  have hspec := airyH_spec N u
  rw [windowD_split hN, mul_pow] at hspec
  rw [hspec]
  unfold finQ airyProdFactor
  rw [Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_pow]
  have hA3' : (∏ k ∈ Finset.Icc 3 N, (u - (airyZero k : ℂ)) ^ 2) ≠ 0 := by
    rw [Finset.prod_pow]; exact pow_ne_zero 2 hA3
  have hA12' : (∏ k ∈ Finset.Icc 1 2, (u - (airyZero k : ℂ)) ^ 2) ≠ 0 := by
    rw [Finset.prod_pow]; exact pow_ne_zero 2 hA12
  field_simp

/-- Two functions continuous at a real point and equal off the real axis are equal there. -/
lemma eq_of_continuousAt_of_im_ne_zero {f g : ℂ → ℂ} {u₀ : ℂ} (hu : u₀.im = 0) (hf : ContinuousAt f u₀)
    (hg : ContinuousAt g u₀) (h : ∀ u : ℂ, u.im ≠ 0 → f u = g u) : f u₀ = g u₀ := by
  have hz : Tendsto (fun m : ℕ => u₀ + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) atTop (𝓝 u₀) := by
    have h1 : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [Complex.ofReal_zero] at this
    simpa using (tendsto_const_nhds (x := u₀)).add (tendsto_const_nhds.mul h1)
  have e : ∀ m : ℕ, f (u₀ + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) =
      g (u₀ + Complex.I * (1 / ((m : ℝ) + 1) : ℝ)) := by
    intro m
    refine h _ ?_
    simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, one_mul, zero_add, mul_zero, hu]
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  exact tendsto_nhds_unique (hf.tendsto.comp hz) ((hg.tendsto.comp hz).congr fun m => (e m).symm)

lemma airyZero_ne_of_im_ne_zero {u : ℂ} (hu : u.im ≠ 0) (k : ℕ) : u ≠ (airyZero k : ℂ) :=
  fun h => hu (by rw [h]; simp)

lemma differentiable_winC (p q : ℝ) {S W : ℕ → ℝ} (hH : AiryProdTailHypothesis 2 S W) :
    Differentiable ℂ (winC p q S W) := by
  unfold winC
  exact (differentiable_id.sub_const _).neg.mul (airyWindowProd_differentiable 2 (by norm_num) q S W hH)

/-- **Factorisation of the window on a ball avoiding the tail zeros.** -/
lemma winC_eq_of_lt (p q : ℝ) {S W : ℕ → ℝ} {N : ℕ} (hN : 2 ≤ N) (hH : AiryProdTailHypothesis 2 S W)
    {R : ℝ} (hR : ∀ k : ℕ, N < k → ∀ u : ℂ, ‖u‖ < R → u ≠ (airyZero k : ℂ)) {u : ℂ} (hu : ‖u‖ < R) :
    winC p q S W u = (u - (p : ℂ)) * (u - (q : ℂ)) * airyH N u * finQ S W N u * airyProdTail N S W u := by
  have hHN : AiryProdTailHypothesis N S W := tailHyp_mono hN hH
  by_cases him : u.im = 0
  · refine eq_of_continuousAt_of_im_ne_zero him (differentiable_winC p q hH).continuous.continuousAt ?_
      (fun v hv => winC_eq_of_ne p q hN hHN (fun k _ => airyZero_ne_of_im_ne_zero hv k))
    have hd := differentiableOn_airyProdTail N S W hHN
    have hmem : Metric.ball (0 : ℂ) R ⊆ {u : ℂ | ∀ k : ℕ, N < k → u ≠ (airyZero k : ℂ)} :=
      fun v hv k hk => hR k hk v (by simpa using hv)
    have hT : ContinuousAt (airyProdTail N S W) u :=
      ((hd.mono hmem).differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using hu))).continuousAt
    have hc1 : Continuous (fun u : ℂ => (u - (p : ℂ)) * (u - (q : ℂ)) * airyH N u * finQ S W N u) := by
      have := (differentiable_airyH N).continuous
      unfold finQ
      fun_prop
    exact hc1.continuousAt.mul hT
  · exact winC_eq_of_ne p q hN hHN (fun k _ => airyZero_ne_of_im_ne_zero him k)


lemma norm_finQ_le {S W : ℕ → ℝ} {A R : ℝ} (hA : 0 < A)
    (h : ∀ k : ℕ, 1 ≤ k → |S k - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
      |W k| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ))) (N : ℕ) {x : ℝ} (hx : |x| ≤ R) :
    ‖finQ S W N (x : ℂ)‖ ≤ ∏ k ∈ Finset.Icc 3 N, ((R + |airyZero k| + A) ^ 2 + A ^ 2) := by
  unfold finQ
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k hk => ?_)
  have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
  obtain ⟨h1, h2⟩ := h k hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hp1 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1' (by norm_num)
  have hp2 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1' (by norm_num)
  have hS : |S k - airyZero k| ≤ A := h1.trans (by nlinarith)
  have hWk : |W k| ≤ A := h2.trans (by nlinarith)
  have hSk : |S k| ≤ |airyZero k| + A := by
    have : S k = airyZero k + (S k - airyZero k) := by ring
    calc |S k| = |airyZero k + (S k - airyZero k)| := by rw [← this]
      _ ≤ |airyZero k| + |S k - airyZero k| := abs_add_le _ _
      _ ≤ |airyZero k| + A := by linarith
  have hxS : |x - S k| ≤ R + |airyZero k| + A := by
    calc |x - S k| ≤ |x| + |S k| := abs_sub _ _
      _ ≤ R + |airyZero k| + A := by linarith
  have e : ((x : ℂ) - (S k : ℂ)) ^ 2 + (W k : ℂ) ^ 2 = (((x - S k) ^ 2 + W k ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have a1 : (x - S k) ^ 2 ≤ (R + |airyZero k| + A) ^ 2 := by
    rw [← sq_abs (x - S k)]
    exact pow_le_pow_left₀ (abs_nonneg _) hxS 2
  have a2 : W k ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs (W k)]
    exact pow_le_pow_left₀ (abs_nonneg _) hWk 2
  linarith

/-- The radius beyond which no Airy zero lies in the ball. -/
lemma exists_ball_avoid (R : ℝ) :
    ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ k : ℕ, K₀ ≤ k → ∀ u : ℂ, ‖u‖ ≤ R → u ≠ (airyZero k : ℂ) := by
  obtain ⟨K₀, hK₀2, hK₀⟩ := norm_sub_airyZero_ge_eventually R
  refine ⟨K₀, hK₀2, fun k hk u hu h => ?_⟩
  have := hK₀ k hk u hu
  rw [h, sub_self, norm_zero] at this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have := Real.rpow_pos_of_pos hk0 (2 / 3 : ℝ)
  linarith

/-- **Local uniform bound** for the windows of a `UnifTail` family. -/
theorem exists_winC_bound {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) (p q R : ℝ) :
    ∃ M : ℝ, ∀ (j : ℕ) (x : ℝ), |x| ≤ R → ‖winC p q (S j) (W j) (x : ℂ)‖ ≤ M := by
  obtain ⟨A, hA, hb⟩ := hU
  obtain ⟨N₀, hN₀, B, hB0, hBd⟩ := norm_airyProdTail_le ⟨A, hA, hb⟩ (max R 0 + 1)
  obtain ⟨K₀, hK₀2, hK₀⟩ := exists_ball_avoid (max R 0 + 1)
  set N : ℕ := max N₀ K₀ with hNdef
  have hN2 : 2 ≤ N := le_trans hN₀ (le_max_left _ _)
  have hR : ∀ k : ℕ, N < k → ∀ u : ℂ, ‖u‖ < max R 0 + 1 → u ≠ (airyZero k : ℂ) := fun k hk u hu =>
    hK₀ k (le_trans (le_max_right _ _) hk.le) u hu.le
  obtain ⟨MH, hMH⟩ := (isCompact_closedBall (0 : ℂ) (max R 0)).exists_bound_of_continuousOn
    (differentiable_airyH N).continuous.continuousOn
  set Bq : ℝ := ∏ k ∈ Finset.Icc 3 N, ((max R 0 + |airyZero k| + A) ^ 2 + A ^ 2) with hBq
  have hBq0 : 0 ≤ Bq := Finset.prod_nonneg fun _ _ => by positivity
  refine ⟨(max R 0 + |p|) * (max R 0 + |q|) * max MH 0 * Bq * B, fun j x hx => ?_⟩
  have hx' : |x| ≤ max R 0 := hx.trans (le_max_left _ _)
  have hxn : ‖(x : ℂ)‖ ≤ max R 0 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx'
  have hlt : ‖(x : ℂ)‖ < max R 0 + 1 := by linarith
  rw [winC_eq_of_lt p q hN2 (tailHyp_of_unif hA (hb j) 2) hR hlt]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1 : ‖(x : ℂ) - (p : ℂ)‖ ≤ max R 0 + |p| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith)
  have h2 : ‖(x : ℂ) - (q : ℂ)‖ ≤ max R 0 + |q| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith)
  have h3 : ‖airyH N (x : ℂ)‖ ≤ max MH 0 := (hMH (x : ℂ) (by simpa using hxn)).trans (le_max_left _ _)
  have h4 : ‖finQ (S j) (W j) N (x : ℂ)‖ ≤ Bq := norm_finQ_le hA (hb j) N hx'
  have h5 : ‖airyProdTail N (S j) (W j) (x : ℂ)‖ ≤ B := hBd j (x : ℂ) hlt.le N (le_max_left _ _)
  gcongr

lemma tailHyp_of_eventually_airy {S' W' : ℕ → ℝ} {M₀ : ℕ} (hSa : ∀ k, M₀ < k → S' k = airyZero k)
    (hWa : ∀ k, M₀ < k → W' k = 0) (f : ℕ) : AiryProdTailHypothesis f S' W' := by
  obtain ⟨A₀, hA₀, hb⟩ := uniform_wkb_bound
  refine tailHyp_of_bound (M := M₀) hA₀ fun k hk => ?_
  have hk1 : 1 ≤ k := by omega
  refine ⟨?_, ?_⟩
  · rw [hSa k hk]; exact (hb k hk1).1
  · rw [hWa k hk, abs_zero]; positivity

/-- **Pointwise limit of the windows at every real point** (including the Airy zeros). -/
theorem tendsto_winC {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) (p q : ℝ) (S' W' : ℕ → ℝ) {M₀ : ℕ}
    (hSa : ∀ k, M₀ < k → S' k = airyZero k) (hWa : ∀ k, M₀ < k → W' k = 0)
    (hS : ∀ k, 3 ≤ k → Tendsto (fun j => S j k) atTop (𝓝 (S' k)))
    (hW : ∀ k, 3 ≤ k → Tendsto (fun j => W j k) atTop (𝓝 (W' k))) (x : ℝ) :
    Tendsto (fun j => winC p q (S j) (W j) (x : ℂ)) atTop (𝓝 (winC p q S' W' (x : ℂ))) := by
  obtain ⟨A, hA, hb⟩ := hU
  obtain ⟨N₀, hN₀, hbd⟩ := exists_tail_bound ⟨A, hA, hb⟩ |x|
  obtain ⟨K₀, hK₀2, hK₀⟩ := exists_ball_avoid (|x| + 1)
  set N : ℕ := max (max N₀ K₀) M₀ with hNdef
  have hN2 : 2 ≤ N := le_trans hN₀ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hN₀N : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR : ∀ k : ℕ, N < k → ∀ u : ℂ, ‖u‖ < |x| + 1 → u ≠ (airyZero k : ℂ) := fun k hk u hu =>
    hK₀ k (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk.le) u hu.le
  have hxn : ‖(x : ℂ)‖ ≤ |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hlt : ‖(x : ℂ)‖ < |x| + 1 := by linarith
  have hne : ∀ k : ℕ, N < k → (x : ℂ) ≠ (airyZero k : ℂ) := fun k hk => hR k hk _ hlt
  have hH' := tailHyp_of_eventually_airy hSa hWa 2
  have hMN : M₀ ≤ N := le_max_right _ _
  have hrepj : ∀ j, winC p q (S j) (W j) (x : ℂ) = ((x : ℂ) - (p : ℂ)) * ((x : ℂ) - (q : ℂ)) * airyH N x *
      finQ (S j) (W j) N x * airyProdTail N (S j) (W j) x := fun j =>
    winC_eq_of_lt p q hN2 (tailHyp_of_unif hA (hb j) 2) hR hlt
  have hrep' : winC p q S' W' (x : ℂ) = ((x : ℂ) - (p : ℂ)) * ((x : ℂ) - (q : ℂ)) * airyH N x *
      finQ S' W' N x * airyProdTail N S' W' x := winC_eq_of_lt p q hN2 hH' hR hlt
  have hT' : airyProdTail N S' W' (x : ℂ) = 1 := by
    unfold airyProdTail
    have : ∀ m : ℕ, airyProdFactor S' W' (N + 1 + m) (x : ℂ) = 1 := fun m => by
      have hk : N < N + 1 + m := by omega
      have hden : ((x : ℂ) - (airyZero (N + 1 + m) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (hne _ hk))
      unfold airyProdFactor
      rw [hSa _ (by omega), hWa _ (by omega)]
      simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      exact div_self hden
    simp only [this, tprod_one]
  have hTj : Tendsto (fun j => airyProdTail N (S j) (W j) (x : ℂ)) atTop (𝓝 1) :=
    tendsto_airyProdTail_one hxn hbd (fun k hk => by rw [← hSa k (by omega)]; exact hS k (by omega))
      (fun k hk => by rw [← hWa k (by omega)]; exact hW k (by omega)) hN₀N hne
  have hQj : Tendsto (fun j => finQ (S j) (W j) N (x : ℂ)) atTop (𝓝 (finQ S' W' N (x : ℂ))) := by
    unfold finQ
    refine tendsto_finsetProd _ fun k hk => ?_
    have hk3 := (Finset.mem_Icc.mp hk).1
    have h1 := Complex.continuous_ofReal.continuousAt.tendsto.comp (hS k hk3)
    have h2 := Complex.continuous_ofReal.continuousAt.tendsto.comp (hW k hk3)
    exact ((tendsto_const_nhds.sub h1).pow 2).add (h2.pow 2)
  rw [hrep']
  simp only [hrepj]
  rw [hT']
  exact (tendsto_const_nhds.mul hQj).mul hTj

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.exists_winC_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_winC_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.tendsto_winC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_winC

end FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

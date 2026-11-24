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
    unfold airyProdFactor siteLim
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
    nodeC p q (siteLim α K) (fun _ => 0) n = 0 := by
  unfold nodeC siteLim
  simp [show 3 ≤ n by omega, show ¬(n ≤ K) by omega]

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

lemma airyProdFactor_airyZero (S W : ℕ → ℝ) (n k : ℕ) :
    airyProdFactor S W k (airyZero n : ℂ) =
      ((((airyZero n - S k) ^ 2 + (W k) ^ 2) / (airyZero n - airyZero k) ^ 2 : ℝ) : ℂ) := by
  unfold airyProdFactor
  push_cast
  rfl

lemma norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

section Convergence

variable (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {nj : ℕ → ℕ} {η : ℕ → ℝ}

/-- A uniform `1/k²` bound on `factor - 1` at `a_n`, `n ≤ K`, for all designs of the family with `K ≤ n_j`,
`0 ≤ η_j ≤ 1/4`. -/
lemma exists_factor_bound {n : ℕ} (hn : 1 ≤ n) (hnK : n ≤ K) (hnj : ∀ j, K ≤ nj j)
    (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1 / 4) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ j k, 3 ≤ k → ‖airyProdFactor (siteSeq α K (nj j)) (widthSeq (nj j) (η j)) k
      (airyZero n : ℂ) - 1‖ ≤ Cb / (k : ℝ) ^ 2 := by
  obtain ⟨A, hA, hAb⟩ := exists_uniform_bound
  obtain ⟨C, hC, hCb⟩ := factor_dev hn hnK A hA.le
  set Bk : ℕ → ℝ := fun k => ((airyZero n - clarkNode α k) ^ 2 + gapWKB k ^ 2) / (airyZero n - airyZero k) ^ 2 + 1
    with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := fun k => by positivity
  set Bsum : ℝ := ∑ k ∈ Finset.Icc 3 K, Bk k with hBsum
  have hBsum0 : 0 ≤ Bsum := Finset.sum_nonneg fun k _ => hBk0 k
  refine ⟨Bsum * (K : ℝ) ^ 2 + C, by positivity, fun j k hk3 => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [airyProdFactor_airyZero, norm_ofReal_sub_one]
  by_cases hkK : k ≤ K
  · have hS : siteSeq α K (nj j) k = clarkNode α k := by
      unfold siteSeq
      simp only [show 3 ≤ k ∧ k ≤ nj j + 2 from ⟨hk3, by have := hnj j; omega⟩, and_self, ↓reduceIte, hkK]
    have hW : widthSeq (nj j) (η j) k = η j * gapWKB k := by
      unfold widthSeq
      simp only [show 3 ≤ k ∧ k ≤ nj j + 2 from ⟨hk3, by have := hnj j; omega⟩, and_self, ↓reduceIte]
    rw [hS, hW]
    have hk1 : Bk k ≤ Bsum := Finset.single_le_sum (f := Bk) (fun k _ => hBk0 k)
      (Finset.mem_Icc.mpr ⟨hk3, hkK⟩)
    set x : ℝ := ((airyZero n - clarkNode α k) ^ 2 + (η j * gapWKB k) ^ 2) / (airyZero n - airyZero k) ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ Bk k - 1 := by
      rw [hx, hBk]
      simp only [add_sub_cancel_right]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : (η j * gapWKB k) ^ 2 ≤ gapWKB k ^ 2 := by
        have h0 := hη0 j
        have h1 := hη1 j
        have hη2 : η j ^ 2 ≤ 1 := by nlinarith
        calc (η j * gapWKB k) ^ 2 = η j ^ 2 * gapWKB k ^ 2 := by ring
          _ ≤ 1 * gapWKB k ^ 2 := by gcongr
          _ = gapWKB k ^ 2 := one_mul _
      linarith
    have habs : |x - 1| ≤ Bk k := by
      rw [abs_le]; constructor <;> linarith
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hdiv : Bsum ≤ Bsum * (K : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : (k : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ hk0.le hkK' 2
      nlinarith
    calc |x - 1| ≤ Bsum := habs.trans hk1
      _ ≤ Bsum * (K : ℝ) ^ 2 / (k : ℝ) ^ 2 := hdiv
      _ ≤ (Bsum * (K : ℝ) ^ 2 + C) / (k : ℝ) ^ 2 := by
          rw [add_div]; linarith [div_nonneg hC (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
  · have hkK' : K < k := by omega
    have hk1 : 1 ≤ k := by omega
    obtain ⟨hd, hg⟩ := hAb k hk1
    have hS : |siteSeq α K (nj j) k - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
      unfold siteSeq
      by_cases h : 3 ≤ k ∧ k ≤ nj j + 2
      · simp only [h, and_self, ↓reduceIte, hkK, sub_self, abs_zero]
        positivity
      · simp only [h, ↓reduceIte]
        rw [abs_sub_comm]; exact hd
    have hW : |widthSeq (nj j) (η j) k| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
      unfold widthSeq
      have hgp := (gapWKB_pos hk1).le
      rw [abs_mul, abs_of_nonneg hgp]
      have hη : |(if 3 ≤ k ∧ k ≤ nj j + 2 then η j else (1 / 4 : ℝ))| ≤ 1 := by
        split_ifs
        · rw [abs_of_nonneg (hη0 j)]; linarith [hη1 j]
        · rw [abs_of_nonneg (by norm_num)]; norm_num
      calc _ ≤ 1 * gapWKB k := mul_le_mul_of_nonneg_right hη hgp
        _ ≤ _ := by linarith
    refine (hCb k hkK' _ _ hS hW).trans ?_
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg hBsum0 (sq_nonneg (K : ℝ))]

/-- **Convergence of the node values for `n ≤ K`.**  As `η_j → 0` and `n_j → ∞` the node values of the designs
`(p, q, S, W) = (z₁ - η_j, q, siteSeq α K n_j, widthSeq n_j η_j)` tend to those of the limit data
`(z₁, q, siteLim α K, 0)`. -/
theorem tendsto_nodeC {n : ℕ} (hn : 1 ≤ n) (hnK : n ≤ K) (q : ℝ) (hnj : ∀ j, K ≤ nj j)
    (hnjt : Tendsto nj atTop atTop) (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1 / 4)
    (hηt : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun j => nodeC (clarkNode α 1 - η j) q (siteSeq α K (nj j)) (widthSeq (nj j) (η j)) n) atTop
      (𝓝 (nodeC (clarkNode α 1) q (siteLim α K) (fun _ => 0) n)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_factor_bound α hn hnK hnj hη0 hη1 (η := η)
  have hp : Tendsto (fun j => (((clarkNode α 1 - η j : ℝ)) : ℂ)) atTop (𝓝 (clarkNode α 1 : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto (clarkNode α 1 - 0)).comp (tendsto_const_nhds.sub hηt)
    rwa [sub_zero] at this
  have h1 : Tendsto (fun j => ((airyZero n : ℂ) - ((clarkNode α 1 - η j : ℝ) : ℂ)) * ((airyZero n : ℂ) - q) /
      (∏ k ∈ (Finset.Icc 1 2).erase n, ((airyZero n : ℂ) - airyZero k) ^ 2)) atTop
      (𝓝 (((airyZero n : ℂ) - clarkNode α 1) * ((airyZero n : ℂ) - q) /
      (∏ k ∈ (Finset.Icc 1 2).erase n, ((airyZero n : ℂ) - airyZero k) ^ 2))) :=
    ((tendsto_const_nhds.sub hp).mul tendsto_const_nhds).div_const _
  have h2 : Tendsto (fun j => if 3 ≤ n then ((airyZero n : ℂ) - siteSeq α K (nj j) n) ^ 2 +
      ((widthSeq (nj j) (η j) n : ℝ) : ℂ) ^ 2 else 1) atTop
      (𝓝 (if 3 ≤ n then ((airyZero n : ℂ) - siteLim α K n) ^ 2 + (((fun _ => (0 : ℝ)) n : ℝ) : ℂ) ^ 2
        else 1)) := by
    by_cases h3 : 3 ≤ n
    · simp only [h3, ↓reduceIte]
      have hS : ∀ j, siteSeq α K (nj j) n = siteLim α K n := fun j => by
        unfold siteSeq siteLim
        simp only [show 3 ≤ n ∧ n ≤ nj j + 2 from ⟨h3, by have := hnj j; omega⟩, and_self, ↓reduceIte]
      have hW : Tendsto (fun j => widthSeq (nj j) (η j) n) atTop (𝓝 0) := by
        have : ∀ j, widthSeq (nj j) (η j) n = η j * gapWKB n := fun j => by
          unfold widthSeq
          simp only [show 3 ≤ n ∧ n ≤ nj j + 2 from ⟨h3, by have := hnj j; omega⟩, and_self, ↓reduceIte]
        simp only [this]
        simpa using hηt.mul_const (gapWKB n)
      have hWc : Tendsto (fun j => ((widthSeq (nj j) (η j) n : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp hW
        rwa [Complex.ofReal_zero] at this
      simp only [hS]
      simpa using (tendsto_const_nhds (x := ((airyZero n : ℂ) - siteLim α K n) ^ 2)).add (hWc.pow 2)
    · simp only [h3, ↓reduceIte]; exact tendsto_const_nhds
  have hbsum : Summable (fun m : ℕ => Cb / ((m : ℝ) + 3) ^ 2) := by
    have h := ((summable_nat_add_iff 3).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))).mul_left Cb
    refine h.congr fun m => ?_
    push_cast
    rw [mul_one_div]
  have h3 := tendsto_tailExcept hn (fun j => siteSeq α K (nj j)) (fun j => widthSeq (nj j) (η j))
    (siteLim α K) (fun _ => 0) (fun m => Cb / ((m : ℝ) + 3) ^ 2) hbsum
    (fun k hk3 _ => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hnjt.eventually_ge_atTop k] with j hj
      unfold siteSeq siteLim
      simp only [show 3 ≤ k ∧ k ≤ nj j + 2 from ⟨hk3, by omega⟩, and_self, ↓reduceIte])
    (fun k hk3 _ => by
      have : ∀ j, k ≤ nj j → widthSeq (nj j) (η j) k = η j * gapWKB k := fun j hj => by
        unfold widthSeq
        simp only [show 3 ≤ k ∧ k ≤ nj j + 2 from ⟨hk3, by omega⟩, and_self, ↓reduceIte]
      have hlim : Tendsto (fun j => η j * gapWKB k) atTop (𝓝 0) := by
        simpa using hηt.mul_const (gapWKB k)
      refine hlim.congr' ?_
      filter_upwards [hnjt.eventually_ge_atTop k] with j hj
      exact (this j hj).symm)
    (Eventually.of_forall fun j k hk3 _ => by
      refine (hCb j k hk3).trans (le_of_eq ?_)
      have : ((k - 3 : ℕ) : ℝ) + 3 = k := by
        rw [Nat.cast_sub hk3]; push_cast; ring
      rw [this])
    (fun m => by positivity)
  unfold nodeC
  exact (h1.mul h2).mul h3

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

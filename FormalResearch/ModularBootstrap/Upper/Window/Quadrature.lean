module

public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# Airy Window Quadrature and Uniform Bounds: Lemmas V and E (`upper_transfer.tex`, `ut:V`, `ut:E`)

Formalizes **Lemma V** (`ut:V` / `uc:V`, `upper_transfer.tex` lines 583--589) and **Lemma E**
(`ut:E`, `upper_transfer.tex` lines 591--599):

* `designR1`, `designPi0`, `designPi`, `designE0`.
* **Lemma V (`ut:V`)**:
  - `lemma_V_hasSum`: $V = \int_{\mathbb{R}} W(u)\,du = \sum_{n \ge 1} W(a_n)/\Ai'(a_n)^2$
    (absolutely convergent).
  - `lemma_V_eval_one`, `lemma_V_eval_succ`: explicit evaluation $W(a_1)/\Ai'(a_1)^2 = -d R_1$
    and $W(a_n)/\Ai'(a_n)^2 = \Pi_n(d) = \Pi_n(0)(1 - d/|a_n - a_1|)$ for $n \ge 2$.
  - `lemma_V_identity`: for $d \in [0, |a_1 - a_2|)$, $\Pi_n(d) \ge 0$,
    $V = -d R_1 + \sum_{n \ge 2} \Pi_n(d) \le -d R_1 + E_0$.
* **Lemma E (`ut:E`)**: `lemma_E` gives absolute constants $C > 0$ and $N_0 \ge 1$ such that for
  every $N \ge N_0$ and $0 \le \eta_* \le 1/4$:
  (i) $\Pi_n(0) \le C n^{-4/3}$ ($n \ge 2$),
  (ii) $\Pi_n(0) \le C \eta_*^2 n^{-4/3}$ ($2 \le n \le N$),
  (iii) $E_0 \le C(\eta_*^2 + N^{-1/3})$,
  (iv) $1/2 \le R_1 \le C$.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Window

open FormalResearch.Special

/-! ### Section 1: Definitions of $R_1$, $\Pi_n(0)$, $\Pi_n(d)$, $E_0$ -/

/-- Real factor in $R_1$ and $\Pi_n(0)$:
$\frac{(a_n - u_k)^2 + \varepsilon_k^2}{(a_n - a_k)^2}$. -/
noncomputable def designRealFactor (N : ℕ) (etaStar : ℝ) (n k : ℕ) : ℝ :=
  ((airyZero n - designSiteU N k) ^ 2 + (designWidthU N etaStar k) ^ 2) /
    (airyZero n - airyZero k) ^ 2

/-- Vacuum slope coefficient $R_1 = \prod_{k \ge 2} \frac{(a_1 - u_k)^2 + \varepsilon_k^2}{(a_1 - a_k)^2}$. -/
noncomputable def designR1 (N : ℕ) (etaStar : ℝ) : ℝ :=
  ∏' m : ℕ, designRealFactor N etaStar 1 (m + 2)

/-- Zero-shift weight $\Pi_n(0)$ for $n \ge 2$. -/
noncomputable def designPi0 (N : ℕ) (etaStar : ℝ) (n : ℕ) : ℝ :=
  ((airyZero n - designSiteU N n) ^ 2 + (designWidthU N etaStar n) ^ 2) /
      |airyZero n - airyZero 1| *
    ∏' m : ℕ, if m + 2 = n then 1 else designRealFactor N etaStar n (m + 2)

/-- Shifted weight $\Pi_n(d) = \Pi_n(0) (1 - d / |a_n - a_1|)$ for $n \ge 2$. -/
noncomputable def designPi (N : ℕ) (etaStar d : ℝ) (n : ℕ) : ℝ :=
  designPi0 N etaStar n * (1 - d / |airyZero n - airyZero 1|)

/-- Total zero-shift cost $E_0 = \sum_{n \ge 2} \Pi_n(0)$. -/
noncomputable def designE0 (N : ℕ) (etaStar : ℝ) : ℝ :=
  ∑' n : ℕ, designPi0 N etaStar (n + 2)

private lemma ofReal_designRealFactor (N : ℕ) (etaStar : ℝ) (n k : ℕ) :
    (designRealFactor N etaStar n k : ℂ) =
      airyProdFactor (designSiteU N) (designWidthU N etaStar) k (airyZero n : ℂ) := by
  unfold designRealFactor airyProdFactor
  push_cast; rfl

private lemma hasProd_real_of_complex {f : ℕ → ℝ} {z : ℂ}
    (hf : HasProd (fun m => (f m : ℂ)) z) :
    HasProd f z.re ∧ z = (z.re : ℂ) := by
  have hre : Tendsto (fun s : Finset ℕ => ∏ m ∈ s, f m) atTop (𝓝 z.re) := by
    have h1 := Complex.continuous_re.continuousAt.tendsto.comp hf
    refine h1.congr fun s => ?_
    dsimp only [Function.comp_def]
    have : ∏ m ∈ s, (f m : ℂ) = ((∏ m ∈ s, f m : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have him : z.im = 0 := by
    have h1 := Complex.continuous_im.continuousAt.tendsto.comp hf
    have h0 : ∀ s : Finset ℕ, (∏ m ∈ s, (f m : ℂ)).im = 0 := fun s => by
      have : ∏ m ∈ s, (f m : ℂ) = ((∏ m ∈ s, f m : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_im]
    have h1' : Tendsto (fun _ : Finset ℕ => (0 : ℝ)) atTop (𝓝 z.im) := by
      refine h1.congr fun s => ?_; dsimp only [Function.comp_def]; rw [h0 s]
    exact (tendsto_const_nhds_iff.mp h1').symm
  exact ⟨hre, Complex.ext rfl him⟩

lemma designR1_hasProd (N : ℕ) (etaStar : ℝ) :
    HasProd (fun m : ℕ => designRealFactor N etaStar 1 (m + 2)) (designR1 N etaStar) ∧
    airyProdTail 1 (designSiteU N) (designWidthU N etaStar) (airyZero 1 : ℂ) =
      (designR1 N etaStar : ℂ) := by
  have hH := design_tail_hypothesis N etaStar
  have hne : ∀ k : ℕ, 1 < k → (airyZero 1 : ℂ) ≠ (airyZero k : ℂ) := fun k hk h => by
    have := airyZero_injective_on le_rfl (by omega) (Complex.ofReal_injective h)
    omega
  have hp := hasProd_airyProdTail hH hne
  have hp' : HasProd (fun m : ℕ => (designRealFactor N etaStar 1 (m + 2) : ℂ))
      (airyProdTail 1 (designSiteU N) (designWidthU N etaStar) (airyZero 1 : ℂ)) := by
    refine hp.congr_fun fun m => ?_
    rw [show 1 + 1 + m = m + 2 by ring, ofReal_designRealFactor]
  obtain ⟨hre, hcm⟩ := hasProd_real_of_complex hp'
  have heq : designR1 N etaStar = (airyProdTail 1 (designSiteU N) (designWidthU N etaStar) (airyZero 1 : ℂ)).re :=
    hre.tprod_eq
  rw [← heq] at hre hcm
  exact ⟨hre, hcm⟩

lemma designPi0_hasProd (N : ℕ) (etaStar : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    HasProd (fun m : ℕ => if m + 2 = n then 1 else designRealFactor N etaStar n (m + 2))
      (∏' m : ℕ, if m + 2 = n then 1 else designRealFactor N etaStar n (m + 2)) ∧
    airyProdTailExcept 1 n (designSiteU N) (designWidthU N etaStar) (airyZero n : ℂ) =
      ((∏' m : ℕ, if m + 2 = n then 1 else designRealFactor N etaStar n (m + 2) : ℝ) : ℂ) := by
  have hH := design_tail_hypothesis N etaStar
  have hne : ∀ k : ℕ, 1 < k → k ≠ n → (airyZero n : ℂ) ≠ (airyZero k : ℂ) := fun k hk hkn h =>
    hkn (airyZero_injective_on (by omega) (by omega) (Complex.ofReal_injective h.symm))
  have hp := hasProd_airyProdTailExcept (f := 1) (n := n) hH hne
  have hp' : HasProd (fun m : ℕ =>
      ((if m + 2 = n then (1 : ℝ) else designRealFactor N etaStar n (m + 2) : ℝ) : ℂ))
      (airyProdTailExcept 1 n (designSiteU N) (designWidthU N etaStar) (airyZero n : ℂ)) := by
    refine hp.congr_fun fun m => ?_
    rw [show 1 + 1 + m = m + 2 by ring]
    split_ifs <;> simp [ofReal_designRealFactor]
  obtain ⟨hre, hcm⟩ := hasProd_real_of_complex hp'
  have ht := hre.tprod_eq
  rw [← ht] at hre hcm
  exact ⟨hre, hcm⟩

lemma designR1_nonneg (N : ℕ) (etaStar : ℝ) : 0 ≤ designR1 N etaStar := by
  have hp := (designR1_hasProd N etaStar).1
  refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
  refine Finset.prod_nonneg fun m _ => ?_
  unfold designRealFactor
  positivity

lemma designPi0_nonneg (N : ℕ) (etaStar : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ designPi0 N etaStar n := by
  unfold designPi0
  have hp := (designPi0_hasProd N etaStar hn).1
  have hprod : 0 ≤ ∏' m : ℕ, if m + 2 = n then 1 else designRealFactor N etaStar n (m + 2) := by
    refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
    refine Finset.prod_nonneg fun m _ => ?_
    split_ifs
    · exact zero_le_one
    · unfold designRealFactor; positivity
  have hpre : 0 ≤ ((airyZero n - designSiteU N n) ^ 2 + (designWidthU N etaStar n) ^ 2) /
      |airyZero n - airyZero 1| := by positivity
  exact mul_nonneg hpre hprod

/-! ### Section 2: Lemma V (`ut:V`) — Airy quadrature evaluation -/

/-- **Lemma V (`ut:V`), quadrature and absolute convergence**:
$\int_{\mathbb{R}} W(u)\,du = \sum_{n \ge 1} W(a_n) / \Ai'(a_n)^2$, with the series absolutely convergent. -/
theorem lemma_V_hasSum (N : ℕ) (etaStar d : ℝ) :
    HasSum (fun n : ℕ => designWindowW N etaStar d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, designWindowW N etaStar d (x : ℂ)) ∧
    Summable (fun n : ℕ => ‖designWindowW N etaStar d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖) := by
  obtain ⟨C, hC, hbd⟩ := lemma_G_bound N etaStar d
  have hdiff := designWindowW_differentiable N etaStar d
  exact ⟨airy_quadrature hdiff hC.le (by norm_num) hbd,
    (airy_summable_weighted hC.le (by norm_num) hbd).norm⟩

/-- Evaluation at $a_1$: $W(a_1) / \Ai'(a_1)^2 = -d R_1$. -/
theorem lemma_V_eval_one (N : ℕ) (etaStar d : ℝ) :
    designWindowW N etaStar d (airyZero 1 : ℂ) / (deriv airyAiC (airyZero 1 : ℂ)) ^ 2 =
      ((-d * designR1 N etaStar : ℝ) : ℂ) := by
  unfold designWindowW
  rw [airyWindowProd_at_airyZero_le 1 (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar)
    le_rfl le_rfl]
  have htail := (designR1_hasProd N etaStar).2
  rw [htail]
  have h_erase : (Finset.Icc 1 1).erase 1 = ∅ := by decide
  rw [h_erase, Finset.prod_empty, div_one]
  have hderiv_ne : deriv airyAiC (airyZero 1 : ℂ) ≠ 0 := airyZero_deriv_ne_zero 1
  have hsub : (airyZero 1 : ℂ) - ((airyZero 1 - d : ℝ) : ℂ) = (d : ℂ) := by push_cast; ring
  rw [hsub]
  field_simp [hderiv_ne]
  push_cast
  ring

/-- Evaluation at $a_n$ ($n \ge 2$): $W(a_n) / \Ai'(a_n)^2 = \Pi_n(d)$. -/
theorem lemma_V_eval_succ (N : ℕ) (etaStar d : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    designWindowW N etaStar d (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 =
      (designPi N etaStar d n : ℂ) := by
  unfold designWindowW
  rw [airyWindowProd_at_airyZero_gt 1 (airyZero 1 - d) (designSiteU N) (designWidthU N etaStar)
    (by omega : 1 < n)]
  have htail := (designPi0_hasProd N etaStar hn).2
  rw [htail]
  have hIcc : Finset.Icc 1 1 = {1} := by decide
  rw [hIcc, Finset.prod_singleton]
  have hderiv_ne : deriv airyAiC (airyZero n : ℂ) ≠ 0 := airyZero_deriv_ne_zero n
  have han_lt : airyZero n < airyZero 1 := airyZero_lt_of_lt le_rfl (by omega)
  have hdiff_ne : (airyZero n : ℂ) - (airyZero 1 : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr han_lt.ne)
  have habs : |airyZero n - airyZero 1| = airyZero 1 - airyZero n := by
    rw [abs_of_neg (by linarith)]
    ring
  have hnum : -((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) / ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2 =
      (((1 - d / |airyZero n - airyZero 1|) / |airyZero n - airyZero 1| : ℝ) : ℂ) := by
    have h1 : airyZero 1 - airyZero n ≠ 0 := by linarith
    have hnum_r : -(airyZero n - (airyZero 1 - d)) / (airyZero n - airyZero 1) ^ 2 =
        (1 - d / |airyZero n - airyZero 1|) / |airyZero n - airyZero 1| := by
      rw [habs]
      have hne_sq : airyZero n - airyZero 1 ≠ 0 := by linarith
      field_simp [h1, hne_sq]
      ring
    exact_mod_cast hnum_r
  have heq_lhs : -(deriv airyAiC (airyZero n : ℂ)) ^ 2 * ((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) /
      ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2 *
      (((airyZero n : ℂ) - (designSiteU N n : ℂ)) ^ 2 + (designWidthU N etaStar n : ℂ) ^ 2) *
      ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else designRealFactor N etaStar n (m + 2) : ℝ) : ℂ) /
      (deriv airyAiC (airyZero n : ℂ)) ^ 2 =
      (-((airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ)) / ((airyZero n : ℂ) - (airyZero 1 : ℂ)) ^ 2) *
      (((airyZero n : ℂ) - (designSiteU N n : ℂ)) ^ 2 + (designWidthU N etaStar n : ℂ) ^ 2) *
      ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else designRealFactor N etaStar n (m + 2) : ℝ) : ℂ) := by
    generalize deriv airyAiC (airyZero n : ℂ) = D at hderiv_ne ⊢
    generalize (airyZero n : ℂ) - ((airyZero 1 - d : ℝ) : ℂ) = Num
    generalize (airyZero n : ℂ) - (airyZero 1 : ℂ) = Den at hdiff_ne ⊢
    generalize (((airyZero n : ℂ) - (designSiteU N n : ℂ)) ^ 2 + (designWidthU N etaStar n : ℂ) ^ 2) = Q
    generalize ((∏' m : ℕ, if m + 2 = n then (1 : ℝ) else designRealFactor N etaStar n (m + 2) : ℝ) : ℂ) = T
    field_simp [hderiv_ne, hdiff_ne]
  rw [heq_lhs, hnum]
  unfold designPi designPi0
  push_cast
  ring

/-- **Lemma V (`ut:V`), real identity and upper bound**:
for $d \in [0, |a_1 - a_2|)$, $\Pi_n(d) \ge 0$,
$V := \int_{\mathbb{R}} W(u)\,du = -d R_1 + \sum_{n \ge 2} \Pi_n(d) \le -d R_1 + E_0$. -/
theorem lemma_V_identity (N : ℕ) (etaStar d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < |airyZero 1 - airyZero 2|) :
    (∀ n : ℕ, 2 ≤ n → 0 ≤ designPi N etaStar d n ∧ designPi N etaStar d n ≤ designPi0 N etaStar n) ∧
    Summable (fun n : ℕ => designPi N etaStar d (n + 2)) ∧
    Summable (fun n : ℕ => designPi0 N etaStar (n + 2)) ∧
    (∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re) =
      -d * designR1 N etaStar + ∑' n : ℕ, designPi N etaStar d (n + 2) ∧
    (∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re) ≤
      -d * designR1 N etaStar + designE0 N etaStar := by
  have hpi_le : ∀ n : ℕ, 2 ≤ n →
      0 ≤ designPi N etaStar d n ∧ designPi N etaStar d n ≤ designPi0 N etaStar n := by
    intro n hn
    have h12 : airyZero 1 - airyZero 2 ≤ airyZero 1 - airyZero n := by
      rcases hn.eq_or_lt with rfl | h2n
      · exact le_rfl
      · linarith [airyZero_lt_of_lt (by omega) h2n]
    have habs_12 : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 :=
      abs_of_nonneg (by linarith [airyZero_strictAnti le_rfl])
    have habs_n : |airyZero n - airyZero 1| = airyZero 1 - airyZero n := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < n)])]
    have hd_lt : d < |airyZero n - airyZero 1| := by linarith
    have hpos : 0 < |airyZero n - airyZero 1| := lt_of_le_of_lt hd0 hd_lt
    have hfac_ge : 0 ≤ 1 - d / |airyZero n - airyZero 1| := by
      rw [sub_nonneg, div_le_one hpos]; exact hd_lt.le
    have hfac_le : 1 - d / |airyZero n - airyZero 1| ≤ 1 := by
      have : 0 ≤ d / |airyZero n - airyZero 1| := div_nonneg hd0 hpos.le
      linarith
    have h0 := designPi0_nonneg N etaStar hn
    unfold designPi
    exact ⟨mul_nonneg h0 hfac_ge, mul_le_of_le_one_right h0 hfac_le⟩
  obtain ⟨hhas, hsum_norm⟩ := lemma_V_hasSum N etaStar d
  have hhas_re : HasSum (fun n : ℕ =>
      (designWindowW N etaStar d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re)
      (∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re) := by
    have hint := lemma_G_integrable N etaStar d
    have h_int : (∫ x : ℝ, designWindowW N etaStar d (x : ℂ)).re =
        ∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re := (integral_re hint).symm
    rw [← h_int]
    exact Complex.reCLM.hasSum hhas
  have hsplit := hasSum_nat_add_iff' 1 |>.mpr hhas_re
  have hterm0 : (designWindowW N etaStar d (airyZero 1 : ℂ) /
      (deriv airyAiC (airyZero 1 : ℂ)) ^ 2).re = -d * designR1 N etaStar := by
    rw [lemma_V_eval_one, Complex.ofReal_re]
  have hterm_succ : ∀ n : ℕ, (designWindowW N etaStar d (airyZero (n + 2) : ℂ) /
      (deriv airyAiC (airyZero (n + 2) : ℂ)) ^ 2).re = designPi N etaStar d (n + 2) := fun n => by
    rw [lemma_V_eval_succ N etaStar d (by omega), Complex.ofReal_re]
  have hsum_pi : Summable (fun n : ℕ => designPi N etaStar d (n + 2)) := by
    have hs1 := (summable_nat_add_iff 1).mpr hhas_re.summable
    refine hs1.congr fun n => ?_
    simpa [Nat.add_assoc] using (hterm_succ n)
  have hid : (∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re) =
      -d * designR1 N etaStar + ∑' n : ℕ, designPi N etaStar d (n + 2) := by
    have htsum := hhas_re.tsum_eq.symm
    rw [Summable.tsum_eq_zero_add hhas_re.summable] at htsum
    simp only [zero_add] at htsum
    have hshift : (∑' n : ℕ, (designWindowW N etaStar d (airyZero (n + 1 + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1 + 1) : ℂ)) ^ 2).re) =
        ∑' n : ℕ, designPi N etaStar d (n + 2) := by
      refine tsum_congr fun n => ?_
      rw [show n + 1 + 1 = n + 2 by ring, hterm_succ n]
    rw [hterm0, hshift] at htsum
    exact htsum
  have hsum_pi0 : Summable (fun n : ℕ => designPi0 N etaStar (n + 2)) := by
    have h_ratio_pos : 0 < 1 - d / |airyZero 1 - airyZero 2| := by
      have hpos : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
      rw [sub_pos, div_lt_one hpos]; exact hd1
    have h_le : ∀ n : ℕ, designPi0 N etaStar (n + 2) ≤
        (1 - d / |airyZero 1 - airyZero 2|)⁻¹ * designPi N etaStar d (n + 2) := fun n => by
      have h12 : airyZero 1 - airyZero 2 ≤ airyZero 1 - airyZero (n + 2) := by
        rcases eq_or_lt_of_le (by omega : 2 ≤ n + 2) with h2 | h2n
        · rw [← h2]
        · linarith [airyZero_lt_of_lt (by omega) h2n]
      have habs_12 : |airyZero 1 - airyZero 2| = airyZero 1 - airyZero 2 :=
        abs_of_nonneg (by linarith [airyZero_strictAnti le_rfl])
      have habs_n : |airyZero (n + 2) - airyZero 1| = airyZero 1 - airyZero (n + 2) := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < n + 2)])]
      have hfac_ge : 1 - d / |airyZero 1 - airyZero 2| ≤ 1 - d / |airyZero (n + 2) - airyZero 1| := by
        have hpos12 : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
        have hpos12 : 0 < |airyZero 1 - airyZero 2| := lt_of_le_of_lt hd0 hd1
        have : d / |airyZero (n + 2) - airyZero 1| ≤ d / |airyZero 1 - airyZero 2| :=
          div_le_div_of_nonneg_left hd0 hpos12 (by linarith)
        linarith
      unfold designPi
      have h0 := designPi0_nonneg N etaStar (by omega : 2 ≤ n + 2)
      calc designPi0 N etaStar (n + 2)
          = designPi0 N etaStar (n + 2) * ((1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (1 - d / |airyZero 1 - airyZero 2|)) := by
              rw [inv_mul_cancel₀ h_ratio_pos.ne', mul_one]
        _ ≤ designPi0 N etaStar (n + 2) * ((1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (1 - d / |airyZero (n + 2) - airyZero 1|)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hfac_ge (inv_nonneg.mpr h_ratio_pos.le)) h0
        _ = (1 - d / |airyZero 1 - airyZero 2|)⁻¹ *
              (designPi0 N etaStar (n + 2) * (1 - d / |airyZero (n + 2) - airyZero 1|)) := by ring
    refine Summable.of_nonneg_of_le (fun n => designPi0_nonneg N etaStar (by omega))
      h_le (hsum_pi.mul_left _)
  have hle : (∫ x : ℝ, (designWindowW N etaStar d (x : ℂ)).re) ≤
      -d * designR1 N etaStar + designE0 N etaStar := by
    rw [hid]
    unfold designE0
    exact add_le_add_right (hsum_pi.tsum_le_tsum (fun n => (hpi_le (n + 2) (by omega)).2) hsum_pi0) _
  exact ⟨hpi_le, hsum_pi, hsum_pi0, hid, hle⟩

/-! ### Section 3: Lemma E (`ut:E`) — uniform bounds on $\Pi_n(0)$, $E_0$, and $R_1$ -/

private lemma rpow_neg_four_thirds_sum_tail (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable (fun m : ℕ => ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have h1 := (summable_nat_add_iff (N + 1)).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
    exact h1.congr fun m => by rw [Nat.add_comm m (N + 1)]
  have h_step : ∀ k : ℕ, 1 ≤ k →
      ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤
        3 * (k : ℝ) ^ (-(1 / 3 : ℝ)) - 3 * ((k + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hcont : ContinuousOn (fun t : ℝ => -3 * t ^ (-(1 / 3 : ℝ))) (Icc (k : ℝ) ((k : ℝ) + 1)) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le hk0 ht.1).ne')
    have hdiff : ∀ t ∈ Ioo (k : ℝ) ((k : ℝ) + 1),
        HasDerivAt (fun x : ℝ => -3 * x ^ (-(1 / 3 : ℝ))) (t ^ (-(4 / 3 : ℝ))) t := fun t ht => by
      have ht0 : 0 < t := lt_trans hk0 ht.1
      have hd := ((hasDerivAt_id' t).rpow_const (p := -(1 / 3 : ℝ)) (Or.inl ht0.ne')).const_mul (-3 : ℝ)
      refine hd.congr_deriv ?_
      rw [show -(1 / 3 : ℝ) - 1 = -(4 / 3 : ℝ) by norm_num]; ring
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => -3 * t ^ (-(1 / 3 : ℝ)))
      (fun t => t ^ (-(4 / 3 : ℝ))) (by linarith) hcont hdiff
    rw [show (k : ℝ) + 1 - k = 1 by ring, div_one] at hmv
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hpow : ((k : ℝ) + 1) ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (lt_trans hk0 hc.1) hc.2.le (by norm_num)
    rw [hcast]; linarith
  refine hsum.tsum_le_of_sum_range_le fun M => ?_
  have h_tel : ∑ m ∈ Finset.range M, ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤
      ∑ m ∈ Finset.range M, (3 * ((N + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) -
        3 * ((N + (m + 1) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) :=
    Finset.sum_le_sum fun m _ => by
      calc ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))
          = ((N + m + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
              rw [show N + 1 + m = N + m + 1 by omega]
        _ ≤ 3 * ((N + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) - 3 * ((N + m + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) :=
              h_step (N + m) (by omega)
        _ = 3 * ((N + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) - 3 * ((N + (m + 1) : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
              rw [show N + m + 1 = N + (m + 1) by omega]
  rw [Finset.sum_range_sub' (fun m => 3 * ((N + m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) M] at h_tel
  simp only [add_zero] at h_tel
  have hnn : 0 ≤ 3 * ((N + M : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  linarith


private lemma rpow_neg_two_thirds_partial_sum_q (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ (-(2 / 3 : ℝ))) ≤ 3 * (M : ℝ) ^ (1 / 3 : ℝ) := by
  induction M with
  | zero => simp
  | succ m ih =>
    have h1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp)]
    rcases m.eq_zero_or_pos with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have h_mvt : 3 * ((m : ℝ) + 1) ^ (1 / 3 : ℝ) - 3 * (m : ℝ) ^ (1 / 3 : ℝ) ≥
          ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have hcont : ContinuousOn (fun t : ℝ => t ^ (1 / 3 : ℝ)) (Icc (m : ℝ) ((m : ℝ) + 1)) :=
          continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le hm0 ht.1).ne'
        have hdiff : ∀ t ∈ Ioo (m : ℝ) ((m : ℝ) + 1),
            HasDerivAt (fun x : ℝ => x ^ (1 / 3 : ℝ)) ((1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ))) t := fun t ht => by
          have ht0 : 0 < t := lt_trans hm0 ht.1
          have hd := (hasDerivAt_id' t).rpow_const (p := (1 / 3 : ℝ)) (Or.inl ht0.ne')
          rw [show (1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ)) = 1 * (1 / 3 : ℝ) * t ^ ((1 / 3 : ℝ) - 1) by
            rw [one_mul, show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by norm_num]]
          exact hd
        obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 / 3 : ℝ))
          (fun t => (1 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ))) (by linarith) hcont hdiff
        rw [show (m : ℝ) + 1 - m = 1 by ring, div_one] at hmv
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have hpow : ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := by
          rw [hcast]
          exact Real.rpow_le_rpow_of_nonpos (lt_trans hm0 hc.1) hc.2.le (by norm_num)
        linarith
      calc ((m + 1 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) + ∑ k ∈ Finset.Icc 1 m, (k : ℝ) ^ (-(2 / 3 : ℝ))
          ≤ (3 * ((m : ℝ) + 1) ^ (1 / 3 : ℝ) - 3 * (m : ℝ) ^ (1 / 3 : ℝ)) + 3 * (m : ℝ) ^ (1 / 3 : ℝ) :=
            add_le_add h_mvt ih
        _ = 3 * ((m + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by push_cast; ring

private lemma one_div_sq_sum_tail_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' m : ℕ, 1 / ((N + 1 + m : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
  have hsum : Summable (fun m : ℕ => 1 / ((N + 1 + m : ℕ) : ℝ) ^ 2) := by
    have h1 := (summable_nat_add_iff (N + 1)).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact h1.congr fun m => by rw [Nat.add_comm m (N + 1)]
  refine hsum.tsum_le_of_sum_range_le fun M => ?_
  have h_step : ∀ m : ℕ, 1 / ((N + 1 + m : ℕ) : ℝ) ^ 2 ≤
      1 / ((N + m : ℕ) : ℝ) - 1 / ((N + m + 1 : ℕ) : ℝ) := fun m => by
    have ha : (0 : ℝ) < (N + m : ℕ) := by exact_mod_cast (by omega : 0 < N + m)
    have hb : (0 : ℝ) < (N + m + 1 : ℕ) := by exact_mod_cast (by omega : 0 < N + m + 1)
    have hcast : ((N + m + 1 : ℕ) : ℝ) = ((N + m : ℕ) : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((N + 1 + m : ℕ) : ℝ) = ((N + m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast2, div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h_tel : ∑ m ∈ Finset.range M, 1 / ((N + 1 + m : ℕ) : ℝ) ^ 2 ≤
      ∑ m ∈ Finset.range M, (1 / ((N + m : ℕ) : ℝ) - 1 / ((N + (m + 1) : ℕ) : ℝ)) :=
    Finset.sum_le_sum fun m _ => h_step m
  rw [Finset.sum_range_sub' (fun m => 1 / ((N + m : ℕ) : ℝ)) M] at h_tel
  simp only [add_zero] at h_tel
  have hnn : 0 ≤ 1 / ((N + M : ℕ) : ℝ) := by positivity
  linarith

private lemma exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have hpos1 : 0 < 1 + 2 * t := by linarith
  have hpos2 : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [show (-2 * t : ℝ) = -(2 * t) by ring, Real.exp_neg]
  calc (Real.exp (2 * t))⁻¹ ≤ (1 + 2 * t)⁻¹ := inv_anti₀ hpos1 h2
    _ ≤ 1 - t := by rw [← one_div, div_le_iff₀ hpos1]; linarith

private lemma design_prod_except_le_exists :
    ∃ C_prod > 0, ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 → ∀ n : ℕ, 2 ≤ n →
      ∏' m : ℕ, (if m + 2 = n then 1 else designRealFactor N η n (m + 2)) ≤ C_prod := by
  obtain ⟨C_Z, hC_Z, hδ⟩ := deltaWKB_le_exists
  set C_gap := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)
  set C_eps := (1 / 4 : ℝ) * C_gap
  set C_sq := C_Z ^ 2 + C_eps ^ 2
  set Z43 : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))
  have hZ43 : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
    simpa using this
  set Z2 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2
  have hZ2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ43_nn : 0 ≤ Z43 := tsum_nonneg fun _ => by positivity
  have hZ2_nn : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  -- Uniform exponent bound across the three ranges `2*k < n`, `n ≤ 2*k ≤ 4*n`, `2*n < k`
  set B_left : ℝ := 2 * C_Z / (9 / 10 : ℝ) * Z43 + 3 * C_sq / (9 / 10 : ℝ) ^ 2
  set c_mid : ℝ := (9 / 10 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)
  set B_mid : ℝ := 4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) +
    2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2
  set B_right : ℝ := (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) * Z2
  set B := B_left + B_mid + B_right
  refine ⟨Real.exp B, Real.exp_pos _, fun N η hη0 hη1 n hn => ?_⟩
  have hp := (designPi0_hasProd N η hn).1
  refine le_of_tendsto hp (Eventually.of_forall fun s => ?_)
  -- Bound each factor by `exp(...)`
  have h_fac : ∀ m : ℕ,
      (if m + 2 = n then (1 : ℝ) else designRealFactor N η n (m + 2)) ≤
        Real.exp (if m + 2 = n then 0 else
          2 * |airyZero (m + 2) - designSiteU N (m + 2)| / |airyZero n - airyZero (m + 2)| +
          (|airyZero (m + 2) - designSiteU N (m + 2)| ^ 2 + (designWidthU N η (m + 2)) ^ 2) /
            (airyZero n - airyZero (m + 2)) ^ 2) := by
    intro m
    split_ifs with hm
    · simp
    · unfold designRealFactor
      have hne : airyZero n - airyZero (m + 2) ≠ 0 := by
        intro h
        exact hm (airyZero_injective_on (by omega) (by omega) (sub_eq_zero.mp h)).symm
      have h_decomp : ((airyZero n - designSiteU N (m + 2)) ^ 2 + (designWidthU N η (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2 =
          1 + (2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - designSiteU N (m + 2)) +
            ((airyZero (m + 2) - designSiteU N (m + 2)) ^ 2 + (designWidthU N η (m + 2)) ^ 2)) /
            (airyZero n - airyZero (m + 2)) ^ 2 := by
        field_simp [hne]; ring
      rw [h_decomp]
      have h1 : 1 + (2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - designSiteU N (m + 2)) +
          ((airyZero (m + 2) - designSiteU N (m + 2)) ^ 2 + (designWidthU N η (m + 2)) ^ 2)) /
          (airyZero n - airyZero (m + 2)) ^ 2 ≤
          1 + (2 * |airyZero (m + 2) - designSiteU N (m + 2)| / |airyZero n - airyZero (m + 2)| +
            (|airyZero (m + 2) - designSiteU N (m + 2)| ^ 2 + (designWidthU N η (m + 2)) ^ 2) /
              (airyZero n - airyZero (m + 2)) ^ 2) := by
        have h_cross : 2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - designSiteU N (m + 2)) /
            (airyZero n - airyZero (m + 2)) ^ 2 ≤
            2 * |airyZero (m + 2) - designSiteU N (m + 2)| / |airyZero n - airyZero (m + 2)| := by
          have h_simp : 2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - designSiteU N (m + 2)) /
              (airyZero n - airyZero (m + 2)) ^ 2 =
              2 * (airyZero (m + 2) - designSiteU N (m + 2)) / (airyZero n - airyZero (m + 2)) := by
            field_simp [hne]
          rw [h_simp]
          refine (le_abs_self _).trans (le_of_eq ?_)
          rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [add_div, ← sq_abs (airyZero (m + 2) - designSiteU N (m + 2))]
        linarith
      exact h1.trans (by rw [add_comm 1 _]; exact Real.add_one_le_exp _)
  have h_prod : ∏ m ∈ s, (if m + 2 = n then (1 : ℝ) else designRealFactor N η n (m + 2)) ≤
      Real.exp (∑ m ∈ s, if m + 2 = n then 0 else
        2 * |airyZero (m + 2) - designSiteU N (m + 2)| / |airyZero n - airyZero (m + 2)| +
        (|airyZero (m + 2) - designSiteU N (m + 2)| ^ 2 + (designWidthU N η (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2) := by
    calc ∏ m ∈ s, _ ≤ ∏ m ∈ s, Real.exp _ :=
          Finset.prod_le_prod₀ (fun m _ => by split_ifs; exact zero_le_one; unfold designRealFactor; positivity)
            (fun m _ => h_fac m)
      _ = Real.exp _ := (Real.exp_sum s _).symm
  refine h_prod.trans (Real.exp_le_exp.mpr ?_)
  -- Split `s` into the three ranges via `m + 2`
  have h_site_le : ∀ k : ℕ, 1 ≤ k → |airyZero k - designSiteU N k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro k hk
    unfold designSiteU
    split_ifs
    · simp only [sub_self, abs_zero]; positivity
    · simpa [deltaWKB] using hδ k hk
  have h_width_le : ∀ k : ℕ, 1 ≤ k → (designWidthU N η k) ^ 2 ≤ C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
    intro k hk
    unfold designWidthU
    have hη_abs : |(if k ≤ N then η else (1 / 4 : ℝ))| ≤ 1 / 4 := by
      split_ifs
      · rwa [abs_of_nonneg hη0]
      · norm_num
    have hgap := gapWKB_le_mul_rpow hk
    have hgap_nn : 0 ≤ gapWKB k := (gapWKB_pos hk).le
    have hw_abs : |((if k ≤ N then η else 1 / 4) * gapWKB k)| ≤ C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hgap_nn]
      calc |(if k ≤ N then η else (1 / 4 : ℝ))| * gapWKB k
          ≤ (1 / 4 : ℝ) * (C_gap * (k : ℝ) ^ (-(1 / 3 : ℝ))) := mul_le_mul hη_abs hgap hgap_nn (by norm_num)
        _ = C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by dsimp [C_eps]; ring
    calc ((if k ≤ N then η else (1 / 4 : ℝ)) * gapWKB k) ^ 2
        = |((if k ≤ N then η else (1 / 4 : ℝ)) * gapWKB k)| ^ 2 := (sq_abs _).symm
      _ ≤ (C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw_abs 2
      _ = C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2,
            ← Real.rpow_mul (by positivity),
            show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num]
  have h_sq_le : ∀ k : ℕ, 1 ≤ k →
      |airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2 ≤ C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
    intro k hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (h_site_le k hk) 2
    rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
      show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1
    have h1' : |airyZero k - designSiteU N k| ^ 2 ≤ C_Z ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      exact h1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk' (by norm_num)) (by positivity))
    have h2 := h_width_le k hk
    dsimp [C_sq]; linarith
  let term : ℕ → ℝ := fun k =>
    if k = n then 0 else
      2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| +
      (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2
  have hterm_nn : ∀ k, 0 ≤ term k := fun k => by
    dsimp [term]; split_ifs <;> positivity
  set S_k := s.image (fun m => m + 2)
  have h_eq_Sk : ∑ m ∈ s, (if m + 2 = n then 0 else
        2 * |airyZero (m + 2) - designSiteU N (m + 2)| / |airyZero n - airyZero (m + 2)| +
        (|airyZero (m + 2) - designSiteU N (m + 2)| ^ 2 + (designWidthU N η (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2) =
      ∑ k ∈ S_k, term k := by
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
  rw [h_eq_Sk]
  have hSk_ge2 : ∀ k ∈ S_k, 2 ≤ k := fun k hk => by
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hk; omega
  set S1 := S_k.filter (fun k => 2 * k < n)
  set S2 := S_k.filter (fun k => k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n)
  set S3 := S_k.filter (fun k => 2 * n < k)
  have h_part : ∑ k ∈ S_k, term k ≤ ∑ k ∈ S1, term k + ∑ k ∈ S2, term k + ∑ k ∈ S3, term k := by
    have h_each : ∀ k ∈ S_k, term k ≤
        (if 2 * k < n then term k else 0) +
        (if k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n then term k else 0) +
        (if 2 * n < k then term k else 0) := by
      intro k _
      by_cases hkn : k = n
      · subst hkn; simp [term]
      · by_cases h1 : 2 * k < n
        · have h2 : ¬(k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n) := by omega
          have h3 : ¬(2 * n < k) := by omega
          simp [h1, h2, h3]
        · by_cases h2 : k ≤ 2 * n
          · have h3 : ¬(2 * n < k) := by omega
            have hmid : k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n := ⟨hkn, by omega, h2⟩
            simp [h1, hmid, h3]
          · have h3 : 2 * n < k := by omega
            have hmid : ¬(k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n) := by omega
            simp [h1, hmid, h3]
    have hs := Finset.sum_le_sum h_each
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    have e1 : ∑ k ∈ S_k, (if 2 * k < n then term k else 0) = ∑ k ∈ S1, term k := by
      dsimp [S1]; rw [Finset.sum_filter]
    have e2 : ∑ k ∈ S_k, (if k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n then term k else 0) = ∑ k ∈ S2, term k := by
      dsimp [S2]; rw [Finset.sum_filter]
    have e3 : ∑ k ∈ S_k, (if 2 * n < k then term k else 0) = ∑ k ∈ S3, term k := by
      dsimp [S3]; rw [Finset.sum_filter]
    linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- Bound S1: 2*k < n
  have hS1_bd : ∑ k ∈ S1, term k ≤ B_left := by
    have h1 : ∀ k ∈ S1, term k ≤
        (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) +
        (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      intro k hk
      have hk_mem := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hk_mem.1
      have h2kn : 2 * k < n := hk_mem.2
      have hkn : k ≠ n := by omega
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax : max n k = n := max_eq_left (by omega)
      rw [hmax] at hsep
      have hdiff : (n : ℝ) / 2 ≤ |(n : ℝ) - k| := by
        have : (2 * k : ℝ) < n := by exact_mod_cast h2kn
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h_lb : (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero k| := by
        have hn_pow : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have h1' : (9 / 10 : ℝ) * (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
            (9 / 5 : ℝ) * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
        have h2' : (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (2 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_add hn_pos]; norm_num
        rw [mul_assoc, h2'] at h1'
        linarith
      have h_lb_ge : (9 / 10 : ℝ) ≤ |airyZero n - airyZero k| := by
        have h1' : 1 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (n : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero n - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) h_lb 2
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hn_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have ht_eq : term k = 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| +
          (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have hn43 : (n : ℝ) ^ (-(4 / 3 : ℝ)) = ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹ := Real.rpow_neg hn_pos.le _
      have ha : 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| ≤
          (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        calc 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / (9 / 10 : ℝ) := by
              gcongr; exact h_site_le k (by omega)
          _ = (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
      have hb : (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤
          (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        calc (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (n : ℝ) ^ (4 / 3 : ℝ)) := by
              gcongr; exact h_sq_le k (by omega)
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
              rw [hn43]; ring
      exact add_le_add ha hb
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    have hs1 : ∑ k ∈ S1, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Z43 := by
      let φ : ℕ → ℕ := fun k => k - 1
      have hinj : Set.InjOn φ S1 := fun a ha b hb h => by
        have ha2 := hSk_ge2 a (Finset.mem_filter.mp ha).1
        have hb2 := hSk_ge2 b (Finset.mem_filter.mp hb).1
        dsimp [φ] at h; omega
      have him : ∑ k ∈ S1, (k : ℝ) ^ (-(4 / 3 : ℝ)) =
          ∑ j ∈ S1.image φ, ((j + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk2 := hSk_ge2 k (Finset.mem_filter.mp hk).1
        dsimp [φ]; rw [show k - 1 + 1 = k by omega]
      rw [him]
      exact hZ43.sum_le_tsum _ fun _ _ => by positivity
    have hs2 : ∑ k ∈ S1, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hsub : S1 ⊆ Finset.Icc 1 n := fun k hk => by
        have hm := Finset.mem_filter.mp hk
        exact Finset.mem_Icc.mpr ⟨by have := hSk_ge2 k hm.1; omega, by omega⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
        (rpow_neg_two_thirds_partial_sum_q n)
    have hmul_n : (n : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ 1 := by
      rw [← Real.rpow_add hn_pos, show -(4 / 3 : ℝ) + 1 / 3 = -1 by norm_num, Real.rpow_neg_one]
      rw [inv_le_one_iff₀]; right; exact_mod_cast (by omega : 1 ≤ n)
    calc ∑ k ∈ S1, term k
        ≤ (2 * C_Z / (9 / 10 : ℝ)) * Z43 +
            (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (3 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
          refine h2.trans (add_le_add (mul_le_mul_of_nonneg_left hs1 (by positivity)) ?_)
          exact mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = (2 * C_Z / (9 / 10 : ℝ)) * Z43 +
            3 * C_sq / (9 / 10 : ℝ) ^ 2 * ((n : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ ≤ (2 * C_Z / (9 / 10 : ℝ)) * Z43 + 3 * C_sq / (9 / 10 : ℝ) ^ 2 * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hmul_n (by positivity)) _
      _ = B_left := by dsimp [B_left]; ring
  -- Bound S2: n ≤ 2*k and k ≤ 2*n and k ≠ n
  have hS2_bd : ∑ k ∈ S2, term k ≤ B_mid := by
    have h1 : ∀ k ∈ S2, term k ≤
        (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
        (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
      intro k hk
      have hm := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hm.1
      obtain ⟨hkn, hn2k, hk2n⟩ := hm.2
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax_le : ((max n k : ℕ) : ℝ) ≤ 2 * n := by
        exact_mod_cast max_le (by omega) hk2n
      have hmax_pow : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ((max n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) hmax_le (by norm_num : -(1 / 3 : ℝ) ≤ 0)
        rw [Real.mul_rpow (by norm_num) hn_pos.le,
          show (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) by
            rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]; norm_num] at hpow
        exact hpow
      have hsep' : 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
        have hc : 2 * c_mid = (9 / 5 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ) := by dsimp [c_mid]; ring
        have := mul_le_mul_of_nonneg_left hmax_pow (by positivity : 0 ≤ (9 / 5 : ℝ) * |(n : ℝ) - k|)
        calc 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ))
            = (9 / 5 : ℝ) * |(n : ℝ) - k| * ((1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
              rw [hc]; ring
          _ ≤ (9 / 5 : ℝ) * |(n : ℝ) - k| * ((max n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := this
          _ ≤ |airyZero n - airyZero k| := by linarith
      have hnk_ge1 : (1 : ℝ) ≤ |(n : ℝ) - k| := by
        have h_int : (1 : ℤ) ≤ |(n : ℤ) - k| := by
          have : (n : ℤ) - k ≠ 0 := fun h0 => hkn (by omega)
          exact Int.one_le_abs this
        exact_mod_cast h_int
      have h_lb1 : c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
        have hn13 : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        calc c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * c_mid * 1 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
          _ ≤ 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by gcongr
          _ ≤ |airyZero n - airyZero k| := hsep'
      have h_lb_sq : c_mid ^ 2 * ((n : ℝ) - k) ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          (airyZero n - airyZero k) ^ 2 := by
        have h1' : c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
          have : 0 ≤ c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by dsimp [c_mid]; positivity
          linarith
        have hsq := pow_le_pow_left₀ (by dsimp [c_mid]; positivity) h1' 2
        rw [mul_pow, mul_pow, sq_abs, sq_abs, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2,
          ← Real.rpow_mul hn_pos.le,
          show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
        exact hsq
      have h_k_ge : (n : ℝ) / 2 ≤ k := by
        have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
        linarith
      have h_site_k : |airyZero k - designSiteU N k| ≤
          C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) h_k_ge (by norm_num : -(4 / 3 : ℝ) ≤ 0)
        have hpow_eq : ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) = (n : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (4 / 3 : ℝ) := by
          rw [show (n : ℝ) / 2 = (n : ℝ) * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hn_pos.le (by norm_num),
            show (2 : ℝ)⁻¹ ^ (-(4 / 3 : ℝ)) = (2 : ℝ) ^ (4 / 3 : ℝ) by
              rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]]
        rw [hpow_eq] at hpow
        calc |airyZero k - designSiteU N k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := h_site_le k (by omega)
          _ ≤ C_Z * ((n : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hpow hC_Z.le
          _ = C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
      have h_sq_k : |airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2 ≤
          C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) h_k_ge (by norm_num : -(2 / 3 : ℝ) ≤ 0)
        have hpow_eq : ((n : ℝ) / 2) ^ (-(2 / 3 : ℝ)) = (n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
          rw [show (n : ℝ) / 2 = (n : ℝ) * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hn_pos.le (by norm_num),
            show (2 : ℝ)⁻¹ ^ (-(2 / 3 : ℝ)) = (2 : ℝ) ^ (2 / 3 : ℝ) by
              rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]]
        rw [hpow_eq] at hpow
        calc |airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2 ≤ C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
              h_sq_le k (by omega)
          _ ≤ C_sq * ((n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
      have ht_eq : term k = 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| +
          (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have h_n_rpow : (n : ℝ) ^ (-(4 / 3 : ℝ)) / (n : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / (n : ℝ) := by
        rw [← Real.rpow_sub hn_pos, show -(4 / 3 : ℝ) - -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
      have ha : 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| ≤
          (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) := by
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        calc 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ))) /
                (c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by gcongr
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) *
                ((n : ℝ) ^ (-(4 / 3 : ℝ)) / (n : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) * (1 / (n : ℝ)) := by rw [h_n_rpow]
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) := by ring
      have hb : (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        have hnk_ne : ((n : ℝ) - k) ^ 2 ≠ 0 := pow_ne_zero 2 (by
          intro h0; apply hkn; exact_mod_cast (sub_eq_zero.mp h0).symm)
        have hn23_ne : (n : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
        calc (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ))) /
                (c_mid ^ 2 * ((n : ℝ) - k) ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
              gcongr
          _ = (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
              field_simp [hc_pos.ne', hnk_ne, hn23_ne]
      exact add_le_add ha hb
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib] at h2
    have hcard : (S2.card : ℝ) ≤ 2 * n := by
      have hsub : S2 ⊆ Finset.Icc 1 (2 * n) := fun k hk => by
        have hm := Finset.mem_filter.mp hk
        exact Finset.mem_Icc.mpr ⟨by have := hSk_ge2 k hm.1; omega, hm.2.2.2⟩
      have hc : S2.card ≤ (Finset.Icc 1 (2 * n)).card := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hc
      have : S2.card ≤ 2 * n := by omega
      exact_mod_cast this
    have hs1 : ∑ _k ∈ S2, (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) ≤
        4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcoef : 0 ≤ 2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid := by dsimp [c_mid]; positivity
      calc (S2.card : ℝ) * ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ))
          ≤ (2 * n) * ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ)) := by gcongr
        _ = 2 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by field_simp [hn_pos.ne']
        _ ≤ 4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by linarith
    have hs2 : ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 ≤
        2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2 := by
      have hsplit : S2 = S2.filter (fun k => n < k) ∪ S2.filter (fun k => k < n) := by
        ext k; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hk
          have hk' := hk
          dsimp [S2] at hk'
          rcases lt_or_gt_of_ne (Finset.mem_filter.mp hk').2.1 with hlt | hgt
          · exact Or.inr ⟨hk, hlt⟩
          · exact Or.inl ⟨hk, hgt⟩
        · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
      have hdisj : Disjoint (S2.filter (fun k => n < k)) (S2.filter (fun k => k < n)) :=
        Finset.disjoint_filter.mpr fun k _ h1 h2 => by omega
      have h_hi : ∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 ≤ Z2 := by
        let φ : ℕ → ℕ := fun k => k - n - 1
        have hinj : Set.InjOn φ (S2.filter (fun k => n < k)) := fun a ha b hb h => by
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [φ] at h; omega
        have him : ∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 =
            ∑ j ∈ (S2.filter (fun k => n < k)).image φ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2
          have hcast : ((φ k : ℕ) : ℝ) + 1 = (k : ℝ) - n := by
            dsimp [φ]
            have h2 : (k - n - 1 + 1 : ℕ) + n = k := by omega
            have h2' : ((k - n - 1 + 1 : ℕ) : ℝ) + (n : ℝ) = (k : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast, show ((n : ℝ) - k) ^ 2 = ((k : ℝ) - n) ^ 2 by ring]
        rw [him]
        exact hZ2.sum_le_tsum _ fun _ _ => by positivity
      have h_lo : ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2 ≤ Z2 := by
        let ψ : ℕ → ℕ := fun k => n - k - 1
        have hinj : Set.InjOn ψ (S2.filter (fun k => k < n)) := fun a ha b hb h => by
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [ψ] at h; omega
        have him : ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2 =
            ∑ j ∈ (S2.filter (fun k => k < n)).image ψ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2
          have hcast : ((ψ k : ℕ) : ℝ) + 1 = (n : ℝ) - k := by
            dsimp [ψ]
            have h2 : (n - k - 1 + 1 : ℕ) + k = n := by omega
            have h2' : ((n - k - 1 + 1 : ℕ) : ℝ) + (k : ℝ) = (n : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast]
        rw [him]
        exact hZ2.sum_le_tsum _ fun _ _ => by positivity
      have hsum_s2 : ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 =
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * ∑ k ∈ S2, 1 / ((n : ℝ) - k) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsum_s2, hsplit, Finset.sum_union hdisj]
      have hcoef : 0 ≤ C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2 := by dsimp [c_mid]; positivity
      calc (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) *
            (∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 +
              ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2)
          ≤ (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * (Z2 + Z2) :=
            mul_le_mul_of_nonneg_left (add_le_add h_hi h_lo) hcoef
        _ = 2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2 := by ring
    dsimp [B_mid]
    have hsum_rewrite : ∑ k ∈ S2, ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2) =
        ∑ k ∈ S2, (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
        ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 :=
      Finset.sum_add_distrib
    linarith [h2, hsum_rewrite]
  -- Bound S3: 2*n < k
  have hS3_bd : ∑ k ∈ S3, term k ≤ B_right := by
    have h1 : ∀ k ∈ S3, term k ≤ (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
      intro k hk
      have hm := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hm.1
      have h2nk : 2 * n < k := hm.2
      have hkn : k ≠ n := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax : max n k = k := max_eq_right (by omega)
      rw [hmax] at hsep
      have hdiff : (k : ℝ) / 2 ≤ |(n : ℝ) - k| := by
        have : (2 * n : ℝ) < k := by exact_mod_cast h2nk
        rw [abs_of_neg (by linarith)]
        linarith
      have h_lb : (9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero k| := by
        have hk13 : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have h1' : (9 / 10 : ℝ) * (k : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤
            (9 / 5 : ℝ) * |(n : ℝ) - k| * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
        have h2' : (k : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) = (k : ℝ) ^ (2 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (k : ℝ)]
          rw [← Real.rpow_add hk_pos]; norm_num
        rw [mul_assoc, h2'] at h1'
        linarith
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero n - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) h_lb 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have ht_eq : term k = 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| +
          (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have hk_m2_a : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have hk_m2_b : (k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have ha : 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k| ≤
          (2 * C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by
        calc 2 * |airyZero k - designSiteU N k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by
              gcongr; exact h_site_le k (by omega)
          _ = (2 * C_Z / (9 / 10 : ℝ)) * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
          _ = (2 * C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by rw [hk_m2_a]; ring
      have hb : (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤ (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
        calc (|airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ)) := by
              gcongr; exact h_sq_le k (by omega)
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by rw [hk_m2_b]; ring
      exact (add_le_add ha hb).trans_eq (by ring)
    have h2 := Finset.sum_le_sum h1
    let φ : ℕ → ℕ := fun k => k - 1
    have hinj : Set.InjOn φ S3 := fun a ha b hb h => by
      have ha2 := hSk_ge2 a (Finset.mem_filter.mp ha).1
      have hb2 := hSk_ge2 b (Finset.mem_filter.mp hb).1
      dsimp [φ] at h; omega
    have him : ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 = ∑ j ∈ S3.image φ, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 := hSk_ge2 k (Finset.mem_filter.mp hk).1
      dsimp [φ]
      have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
      rw [hcast]
    have hsum_z2 : ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 ≤ Z2 := by
      rw [him]; exact hZ2.sum_le_tsum _ fun _ _ => by positivity
    have hmul : ∑ k ∈ S3, (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 =
        (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) * ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hmul] at h2
    have hcoef_nn : 0 ≤ 2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2 := by positivity
    exact h2.trans (mul_le_mul_of_nonneg_left hsum_z2 hcoef_nn)
  exact h_part.trans (add_le_add (add_le_add hS1_bd hS2_bd) hS3_bd)

private lemma designR1_bounds_aux (C_Z C_gap C_eps C_sq C_R C_R_ub Z2 : ℝ)
    (hC_Z : 0 < C_Z) (hδ : ∀ k : ℕ, 1 ≤ k → |deltaWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)))
    (hC_gap : C_gap = (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ))
    (hC_eps : C_eps = (1 / 4 : ℝ) * C_gap)
    (hC_sq : C_sq = C_Z ^ 2 + C_eps ^ 2)
    (hC_R : C_R = C_Z / (9 / 10 : ℝ))
    (hC_R_ub : C_R_ub = 2 * C_R + C_sq / (9 / 10 : ℝ) ^ 2)
    (hZ2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2))
    (hZ2_eq : Z2 = ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2)
    (N₁ N₂ : ℕ) (hN₁ : 4 * C_R / Real.log 2 < (N₁ : ℝ)) (hN₂ : √(2 * C_R) < (N₂ : ℝ))
    (N : ℕ) (hN_1 : 1 ≤ N) (hN_N1 : N₁ ≤ N) (hN_N2 : N₂ ≤ N)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (h_a1_sep : ∀ n : ℕ, 2 ≤ n → (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero 1|) :
    1 / 2 ≤ designR1 N η ∧ designR1 N η ≤ Real.exp (C_R_ub * Z2) := by
  subst hC_gap hC_eps hC_sq hC_R hC_R_ub hZ2_eq
  have hp := (designR1_hasProd N η).1
  have hR1_lb : 1 / 2 ≤ designR1 N η := by
    refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
    have h_fac_lb : ∀ m : ℕ,
        (if m + 2 ≤ N then (1 : ℝ) else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) ≤
          designRealFactor N η 1 (m + 2) := by
      intro m
      set k := m + 2
      have hk2 : 2 ≤ k := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      unfold designRealFactor
      split_ifs with hkN
      · have hs : designSiteU N k = airyZero k := by simp [designSiteU, hkN]
        rw [hs]
        have hne : (airyZero 1 - airyZero k) ^ 2 > 0 := sq_pos_of_pos (by
          linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < k)])
        rw [one_le_div hne]
        linarith [sq_nonneg (designWidthU N η k)]
      · have hs : designSiteU N k = uWKB k := by simp [designSiteU, hkN]
        rw [hs]
        have hsep := h_a1_sep k hk2
        rw [abs_sub_comm] at hsep
        have hδk : |airyZero k - uWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
          simpa [deltaWKB] using hδ k (by omega)
        have h_ratio : |airyZero k - uWKB k| / |airyZero 1 - airyZero k| ≤
            (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by
          have hk_rpow : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
              Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
          calc |airyZero k - uWKB k| / |airyZero 1 - airyZero k|
              ≤ (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by gcongr
            _ = (C_Z / (9 / 10 : ℝ)) * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
            _ = (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by rw [hk_rpow]; ring
        have hk_gt_N : N < k := by omega
        have hN2_lt : (N₂ : ℝ) < k := by
          have h2 : (N₂ : ℝ) ≤ N := by exact_mod_cast hN_N2
          have h3 : (N : ℝ) < k := by exact_mod_cast hk_gt_N
          linarith
        have h_t_le : (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 ≤ 1 / 2 := by
          have hsq : 2 * (C_Z / (9 / 10 : ℝ)) < (k : ℝ) ^ 2 := by
            have h1 : √(2 * (C_Z / (9 / 10 : ℝ))) < k := lt_trans hN₂ hN2_lt
            have h2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
            rwa [Real.sq_sqrt (by positivity)] at h2
          rw [div_le_iff₀ (sq_pos_of_pos hk_pos)]
          linarith
        have hexp1 := exp_neg_two_mul_le_one_sub (t := (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) (by positivity) h_t_le
        have h_base : 1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 ≤
            |airyZero 1 - uWKB k| / |airyZero 1 - airyZero k| := by
          have htri : |airyZero 1 - airyZero k| ≤ |airyZero 1 - uWKB k| + |airyZero k - uWKB k| := by
            rw [abs_sub_comm (airyZero k) (uWKB k)]
            simpa [sub_add_sub_cancel] using abs_sub_le (airyZero 1) (uWKB k) (airyZero k)
          have h_abs_pos : 0 < |airyZero 1 - airyZero k| := lt_of_lt_of_le (by positivity) hsep
          rw [le_div_iff₀ h_abs_pos]
          calc (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) * |airyZero 1 - airyZero k|
              ≤ (1 - |airyZero k - uWKB k| / |airyZero 1 - airyZero k|) * |airyZero 1 - airyZero k| := by gcongr
            _ = |airyZero 1 - airyZero k| - |airyZero k - uWKB k| := by
                rw [sub_mul, one_mul, div_mul_cancel₀ _ h_abs_pos.ne']
            _ ≤ |airyZero 1 - uWKB k| := by linarith
        have h_sq_ge : (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ^ 2 ≤
            (airyZero 1 - uWKB k) ^ 2 / (airyZero 1 - airyZero k) ^ 2 := by
          have hexp_nn : 0 ≤ 1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by linarith
          have hsq := pow_le_pow_left₀ hexp_nn h_base 2
          rwa [div_pow, sq_abs, sq_abs] at hsq
        have hexp2 : Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) =
            (Real.exp (-2 * ((C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2))) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hexp_sq : Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ≤
            (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ^ 2 := by
          rw [hexp2]
          exact pow_le_pow_left₀ (Real.exp_pos _).le hexp1 2
        have h_ge_fac : (airyZero 1 - uWKB k) ^ 2 / (airyZero 1 - airyZero k) ^ 2 ≤
            ((airyZero 1 - uWKB k) ^ 2 + (designWidthU N η k) ^ 2) / (airyZero 1 - airyZero k) ^ 2 := by
          gcongr; linarith [sq_nonneg (designWidthU N η k)]
        exact hexp_sq.trans (h_sq_ge.trans h_ge_fac)
    have h_prod_ge : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) ≤
        ∏ m ∈ s, designRealFactor N η 1 (m + 2) :=
      Finset.prod_le_prod₀ (fun m _ => by split_ifs; exact zero_le_one; exact (Real.exp_pos _).le)
        (fun m _ => h_fac_lb m)
    have h_exp_prod : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) =
        Real.exp (∑ m ∈ s, if m + 2 ≤ N then 0 else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun m _ => by split_ifs <;> simp
    rw [h_exp_prod] at h_prod_ge
    have h_sum_ge : -Real.log 2 ≤
        ∑ m ∈ s, if m + 2 ≤ N then 0 else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2 := by
      set s' := s.filter (fun m => ¬(m + 2 ≤ N))
      have h_flip : (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
            else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) =
          ∑ m ∈ s, if ¬(m + 2 ≤ N) then -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2 else 0 :=
        Finset.sum_congr rfl fun m _ => by split_ifs <;> rfl
      have hs'_eq : (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
            else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) =
          -(4 * (C_Z / (9 / 10 : ℝ))) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 := by
        rw [h_flip, ← Finset.sum_filter, Finset.mul_sum]
        dsimp [s']
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hs'_eq]
      let φ : ℕ → ℕ := fun m => m + 2 - (N + 1)
      have hinj : Set.InjOn φ s' := fun a ha b hb h => by
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp [φ] at h; omega
      have him : ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 =
          ∑ j ∈ s'.image φ, 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' := (Finset.mem_filter.mp hm).2
        have hcast : ((N + 1 + φ m : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by
          dsimp [φ]; exact_mod_cast (by omega : N + 1 + (m + 2 - (N + 1)) = m + 2)
        rw [hcast]
      have hsum_tail : Summable (fun j : ℕ => 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
        have h1 := (summable_nat_add_iff (N + 1)).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
        exact h1.congr fun j => by rw [Nat.add_comm j (N + 1)]
      have h_sum_le : ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
        rw [him]
        exact (hsum_tail.sum_le_tsum _ fun _ _ => by positivity).trans (one_div_sq_sum_tail_le N hN_1)
      have hN1_lt : 4 * (C_Z / (9 / 10 : ℝ)) / Real.log 2 < (N : ℝ) := by
        have h2 : (N₁ : ℝ) ≤ N := by exact_mod_cast hN_N1
        linarith
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN_1
      have h4CR : 4 * (C_Z / (9 / 10 : ℝ)) / (N : ℝ) ≤ Real.log 2 := by
        rw [div_le_iff₀ hN_pos]
        rw [div_lt_iff₀ hlog2] at hN1_lt
        linarith
      calc -Real.log 2 ≤ -(4 * (C_Z / (9 / 10 : ℝ)) / (N : ℝ)) := by linarith
        _ = -(4 * (C_Z / (9 / 10 : ℝ))) * (1 / (N : ℝ)) := by ring
        _ ≤ -(4 * (C_Z / (9 / 10 : ℝ))) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonpos_left h_sum_le (neg_nonpos.mpr (by positivity))
    have hexp_half : 1 / 2 ≤ Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    exact hexp_half.trans ((Real.exp_le_exp.mpr h_sum_ge).trans h_prod_ge)
  have hR1_ub : designR1 N η ≤
      Real.exp ((2 * (C_Z / (9 / 10 : ℝ)) +
        (C_Z ^ 2 + (1 / 4 * (2 / 3 * kappaAiry * (4 / 3) ^ (1 / 3 : ℝ))) ^ 2) / (9 / 10 : ℝ) ^ 2) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) := by
    refine le_of_tendsto hp (Eventually.of_forall fun s => ?_)
    set C_gap := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)
    set C_eps := (1 / 4 : ℝ) * C_gap
    set C_sq := C_Z ^ 2 + C_eps ^ 2
    set C_R := C_Z / (9 / 10 : ℝ)
    set C_R_ub := 2 * C_R + C_sq / (9 / 10 : ℝ) ^ 2
    have h_fac_ub : ∀ m : ℕ, designRealFactor N η 1 (m + 2) ≤
        Real.exp (C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) := by
      intro m
      set k := m + 2
      have hk2 : 2 ≤ k := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := h_a1_sep k hk2
      rw [abs_sub_comm] at hsep
      have h_site_k : |airyZero k - designSiteU N k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        unfold designSiteU; split_ifs
        · simp only [sub_self, abs_zero]; positivity
        · simpa [deltaWKB] using hδ k (by omega)
      have h_width_k : (designWidthU N η k) ^ 2 ≤ C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        unfold designWidthU
        have hη_abs : |(if k ≤ N then η else (1 / 4 : ℝ))| ≤ 1 / 4 := by
          split_ifs; rwa [abs_of_nonneg hη0]; norm_num
        have hgap := gapWKB_le_mul_rpow (by omega : 1 ≤ k)
        have hgap_nn : 0 ≤ gapWKB k := (gapWKB_pos (by omega : 1 ≤ k)).le
        have hw_abs : |((if k ≤ N then η else 1 / 4) * gapWKB k)| ≤ C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
          rw [abs_mul, abs_of_nonneg hgap_nn]
          calc |(if k ≤ N then η else (1 / 4 : ℝ))| * gapWKB k
              ≤ (1 / 4 : ℝ) * (C_gap * (k : ℝ) ^ (-(1 / 3 : ℝ))) :=
                mul_le_mul hη_abs hgap hgap_nn (by norm_num)
            _ = C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by dsimp [C_eps]; ring
        calc ((if k ≤ N then η else (1 / 4 : ℝ)) * gapWKB k) ^ 2
            = |((if k ≤ N then η else (1 / 4 : ℝ)) * gapWKB k)| ^ 2 := (sq_abs _).symm
          _ ≤ (C_eps * (k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw_abs 2
          _ = C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
              rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2,
                ← Real.rpow_mul hk_pos.le,
                show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num]
      have h_sq_k : |airyZero k - designSiteU N k| ^ 2 + (designWidthU N η k) ^ 2 ≤
          C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have h1 := pow_le_pow_left₀ (abs_nonneg _) h_site_k 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
          show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1
        have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        have h1' : |airyZero k - designSiteU N k| ^ 2 ≤ C_Z ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
          h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hk1' (by norm_num)) (by positivity))
        dsimp [C_sq]; linarith
      have hk_m2_a : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have hk_m2_b : (k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero 1 - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) hsep 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have hne : airyZero 1 - airyZero k ≠ 0 := fun h0 =>
        (lt_of_lt_of_le (by positivity) hsep).ne' (abs_eq_zero.mpr h0)
      unfold designRealFactor
      have h_decomp : ((airyZero 1 - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2) /
          (airyZero 1 - airyZero k) ^ 2 =
          1 + (2 * (airyZero 1 - airyZero k) * (airyZero k - designSiteU N k) +
            ((airyZero k - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2)) /
            (airyZero 1 - airyZero k) ^ 2 := by
        field_simp [hne]; ring
      rw [h_decomp]
      have hcross : 2 * (airyZero 1 - airyZero k) * (airyZero k - designSiteU N k) /
          (airyZero 1 - airyZero k) ^ 2 ≤ 2 * C_R / (k : ℝ) ^ 2 := by
        have h_simp : 2 * (airyZero 1 - airyZero k) * (airyZero k - designSiteU N k) /
            (airyZero 1 - airyZero k) ^ 2 =
            2 * (airyZero k - designSiteU N k) / (airyZero 1 - airyZero k) := by
          field_simp [hne]
        rw [h_simp]
        refine (le_abs_self _).trans ?_
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc 2 * |airyZero k - designSiteU N k| / |airyZero 1 - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by gcongr
          _ = 2 * C_R * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by dsimp [C_R]; ring
          _ = 2 * C_R / (k : ℝ) ^ 2 := by rw [hk_m2_a]; ring
      have hsqterm : ((airyZero k - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2) /
          (airyZero 1 - airyZero k) ^ 2 ≤ (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
        have h_num' : (airyZero k - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2 ≤
            C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          rw [← sq_abs (airyZero k - designSiteU N k)]; exact h_sq_k
        calc ((airyZero k - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2) / (airyZero 1 - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ)) := by gcongr
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by rw [hk_m2_b]; ring
      have hk_m1_le : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ k)
      have hk2_le : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hk_m1_le 2
      have h_1div : C_R_ub / (k : ℝ) ^ 2 ≤ C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        have : 0 ≤ C_R_ub := by dsimp [C_R_ub, C_R]; positivity
        gcongr
      have h_crub_eq : 2 * C_R / (k : ℝ) ^ 2 + (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 =
          C_R_ub / (k : ℝ) ^ 2 := by dsimp [C_R_ub]; ring
      have hsum1 : 1 + (2 * (airyZero 1 - airyZero k) * (airyZero k - designSiteU N k) +
          ((airyZero k - designSiteU N k) ^ 2 + (designWidthU N η k) ^ 2)) / (airyZero 1 - airyZero k) ^ 2 ≤
          1 + C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [add_div]
        linarith
      exact hsum1.trans (by rw [add_comm 1 _]; exact Real.add_one_le_exp _)
    calc ∏ m ∈ s, designRealFactor N η 1 (m + 2)
        ≤ ∏ m ∈ s, Real.exp (C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun _ _ => by unfold designRealFactor; positivity) (fun m _ => h_fac_ub m)
      _ = Real.exp (∑ m ∈ s, C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) := (Real.exp_sum s _).symm
      _ ≤ Real.exp (C_R_ub * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : ∑ m ∈ s, C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 =
              C_R_ub * ∑ m ∈ s, 1 / ((m : ℝ) + 1) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by push_cast; ring
          rw [h1]
          exact mul_le_mul_of_nonneg_left (hZ2.sum_le_tsum _ fun _ _ => by positivity) (by positivity)
  exact ⟨hR1_lb, hR1_ub⟩

/-- **Lemma E (`ut:E`)**: uniform bounds on $\Pi_n(0)$, $E_0$, and $R_1$ for all
designs with $N \ge N_0$ and $0 \le \eta_* \le 1/4$. -/
theorem lemma_E :
    ∃ C > 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (N : ℕ), N₀ ≤ N → ∀ (η : ℝ), 0 ≤ η → η ≤ 1 / 4 →
      (∀ n : ℕ, 2 ≤ n → designPi0 N η n ≤ C * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
      (∀ n : ℕ, 2 ≤ n → n ≤ N → designPi0 N η n ≤ C * η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
      designE0 N η ≤ C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (1 / 2 ≤ designR1 N η ∧ designR1 N η ≤ C) := by
  obtain ⟨C_prod, hC_prod, hprod_bd⟩ := design_prod_except_le_exists
  obtain ⟨C_Z, hC_Z, hδ⟩ := deltaWKB_le_exists
  set C_gap := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)
  set C_eps := (1 / 4 : ℝ) * C_gap
  set C_sq := C_Z ^ 2 + C_eps ^ 2
  set C_gap_sq := C_gap ^ 2
  -- Bound `R_1` above and below
  set C_R : ℝ := C_Z / (9 / 10 : ℝ)
  set C_R_ub : ℝ := 2 * C_R + C_sq / (9 / 10 : ℝ) ^ 2
  set Z2 : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2
  have hZ2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ2_nn : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  set R1_ub : ℝ := Real.exp (C_R_ub * Z2)
  -- Choose `N₀` large enough that `C_R * (N₀ + 1)^{-2} ≤ 1/2` and `4 * C_R / N₀ ≤ log 2`
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * C_R / Real.log 2)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (√(2 * C_R))
  set N₀ := max 1 (max N₁ N₂)
  set Z43 : ℝ := ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))
  have hZ43 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
  have hZ43_nn : 0 ≤ Z43 := tsum_nonneg fun _ => by positivity
  set C_pref_all : ℝ := C_prod * (C_Z ^ 2 + C_eps ^ 2) / (9 / 10 : ℝ)
  set C_pref_in : ℝ := C_prod * C_gap_sq / (9 / 10 : ℝ)
  set C_i := max C_pref_all (C_pref_in * (1 / 16))
  set C_e := max (C_pref_in * Z43) (3 * C_i)
  set C := max R1_ub (max C_e (max C_i C_pref_in))
  refine ⟨C, by positivity, N₀, le_max_left _ _, fun N hN η hη0 hη1 => ?_⟩
  -- Common separation bound `|a_n - a_1| ≥ 0.9 * n^{2/3}` for `n ≥ 2`
  have h_a1_sep : ∀ n : ℕ, 2 ≤ n → (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero 1| := by
    intro n hn
    have hsep := airyZero_abs_sub_ge le_rfl (by omega : 1 ≤ n) (by omega : 1 ≠ n)
    rw [max_eq_left (by omega : 1 ≤ n)] at hsep
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hdiff : (n : ℝ) / 2 ≤ |(n : ℝ) - 1| := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith)]; linarith
    have hn_pow : (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (2 / 3 : ℝ) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn_pos]; norm_num
    have h1' : (9 / 10 : ℝ) * (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
        (9 / 5 : ℝ) * |(n : ℝ) - 1| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
      have : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
      nlinarith
    rw [mul_assoc, hn_pow] at h1'
    linarith
  -- Bound for `(ii)` (2 ≤ n ≤ N)
  have h_ii : ∀ n : ℕ, 2 ≤ n → n ≤ N → designPi0 N η n ≤ C * η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro n hn hnN
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hprod := hprod_bd N η hη0 hη1 n hn
    have hsite : designSiteU N n = airyZero n := by simp [designSiteU, hnN]
    have hwidth : designWidthU N η n = η * gapWKB n := by simp [designWidthU, hnN]
    have hgap := gapWKB_le_mul_rpow (by omega : 1 ≤ n)
    have hgap_nn : 0 ≤ gapWKB n := (gapWKB_pos (by omega : 1 ≤ n)).le
    have hwidth_sq : (designWidthU N η n) ^ 2 ≤ η ^ 2 * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [hwidth, mul_pow]
      have hsq := pow_le_pow_left₀ hgap_nn hgap 2
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
        show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
      have heta : 0 ≤ η ^ 2 := sq_nonneg η
      calc η ^ 2 * gapWKB n ^ 2 ≤ η ^ 2 * (C_gap ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hsq heta
        _ = η ^ 2 * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
    have hsep := h_a1_sep n hn
    have hsep_pos : 0 < (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
    have hrpow_div : (n : ℝ) ^ (-(2 / 3 : ℝ)) / (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_sub hn_pos]; congr 2; norm_num
    unfold designPi0
    rw [hsite, sub_self, zero_pow two_ne_zero, zero_add]
    calc (designWidthU N η n) ^ 2 / |airyZero n - airyZero 1| *
          ∏' m : ℕ, (if m + 2 = n then 1 else designRealFactor N η n (m + 2))
        ≤ (η ^ 2 * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) * C_prod := by
          gcongr
          have hp := (designPi0_hasProd N η hn).1
          refine ge_of_tendsto hp (Eventually.of_forall fun s =>
            Finset.prod_nonneg fun m _ => by split_ifs; exact zero_le_one; unfold designRealFactor; positivity)
      _ = C_pref_in * η ^ 2 * ((n : ℝ) ^ (-(2 / 3 : ℝ)) / (n : ℝ) ^ (2 / 3 : ℝ)) := by
          dsimp [C_pref_in]; ring
      _ = C_pref_in * η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by rw [hrpow_div]
      _ ≤ C * η ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
          gcongr
          exact (le_max_right C_i C_pref_in).trans ((le_max_right C_e _).trans (le_max_right R1_ub _))
  -- Bound for `(i)` (all n ≥ 2)
  have h_i_all : ∀ n : ℕ, 2 ≤ n → designPi0 N η n ≤ C_i * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro n hn
    by_cases hnN : n ≤ N
    · have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hprod := hprod_bd N η hη0 hη1 n hn
      have hsite : designSiteU N n = airyZero n := by simp [designSiteU, hnN]
      have hwidth : designWidthU N η n = η * gapWKB n := by simp [designWidthU, hnN]
      have hgap := gapWKB_le_mul_rpow (by omega : 1 ≤ n)
      have hgap_nn : 0 ≤ gapWKB n := (gapWKB_pos (by omega : 1 ≤ n)).le
      have hwidth_sq : (designWidthU N η n) ^ 2 ≤ (1 / 16 : ℝ) * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [hwidth, mul_pow]
        have heta2 : η ^ 2 ≤ 1 / 16 := by nlinarith
        have hsq := pow_le_pow_left₀ hgap_nn hgap 2
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
          show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
        calc η ^ 2 * gapWKB n ^ 2 ≤ (1 / 16 : ℝ) * (C_gap ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) :=
              mul_le_mul heta2 hsq (by positivity) (by norm_num)
          _ = (1 / 16 : ℝ) * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
      have hsep := h_a1_sep n hn
      have hrpow_div : (n : ℝ) ^ (-(2 / 3 : ℝ)) / (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_sub hn_pos]; congr 2; norm_num
      unfold designPi0
      rw [hsite, sub_self, zero_pow two_ne_zero, zero_add]
      calc (designWidthU N η n) ^ 2 / |airyZero n - airyZero 1| *
            ∏' m : ℕ, (if m + 2 = n then 1 else designRealFactor N η n (m + 2))
          ≤ ((1 / 16 : ℝ) * C_gap_sq * (n : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) * C_prod := by
            gcongr
            have hp := (designPi0_hasProd N η hn).1
            refine ge_of_tendsto hp (Eventually.of_forall fun s =>
              Finset.prod_nonneg fun m _ => by split_ifs; exact zero_le_one; unfold designRealFactor; positivity)
        _ = (C_pref_in * (1 / 16)) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [← hrpow_div]; dsimp [C_pref_in]; ring
        _ ≤ C_i * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_right _ _
    · have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hprod := hprod_bd N η hη0 hη1 n hn
      have hsite : designSiteU N n = uWKB n := by simp [designSiteU, hnN]
      have hwidth : designWidthU N η n = (1 / 4 : ℝ) * gapWKB n := by simp [designWidthU, hnN]
      have h_site_sq : (airyZero n - designSiteU N n) ^ 2 ≤ C_Z ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [hsite]
        have h1 : |airyZero n - uWKB n| ≤ C_Z * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
          simpa [deltaWKB] using hδ n (by omega)
        have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [sq_abs, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
          show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h2
        have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        exact h2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1' (by norm_num)) (by positivity))
      have hgap := gapWKB_le_mul_rpow (by omega : 1 ≤ n)
      have hgap_nn : 0 ≤ gapWKB n := (gapWKB_pos (by omega : 1 ≤ n)).le
      have h_w_sq : (designWidthU N η n) ^ 2 ≤ C_eps ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [hwidth, mul_pow]
        have hsq := pow_le_pow_left₀ hgap_nn hgap 2
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
          show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
        calc (1 / 4 : ℝ) ^ 2 * gapWKB n ^ 2
            ≤ (1 / 4 : ℝ) ^ 2 * (C_gap ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = C_eps ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by dsimp [C_eps]; ring
      have hsep := h_a1_sep n hn
      have hrpow_div : (n : ℝ) ^ (-(2 / 3 : ℝ)) / (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_sub hn_pos]; congr 2; norm_num
      unfold designPi0
      have h_num_sq : (airyZero n - designSiteU N n) ^ 2 + (designWidthU N η n) ^ 2 ≤
          (C_Z ^ 2 + C_eps ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [add_mul]; exact add_le_add h_site_sq h_w_sq
      have h_tprod_nn : 0 ≤ ∏' m : ℕ, (if m + 2 = n then 1 else designRealFactor N η n (m + 2)) := by
        have hp := (designPi0_hasProd N η hn).1
        refine ge_of_tendsto hp (Eventually.of_forall fun s =>
          Finset.prod_nonneg fun m _ => by split_ifs; exact zero_le_one; unfold designRealFactor; positivity)
      calc ((airyZero n - designSiteU N n) ^ 2 + (designWidthU N η n) ^ 2) / |airyZero n - airyZero 1| *
            ∏' m : ℕ, (if m + 2 = n then 1 else designRealFactor N η n (m + 2))
          ≤ ((C_Z ^ 2 + C_eps ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) * C_prod := by
            gcongr
        _ = C_pref_all * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [← hrpow_div]; dsimp [C_pref_all]; ring
        _ ≤ C_i * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_left _ _
  have h_i : ∀ n : ℕ, 2 ≤ n → designPi0 N η n ≤ C * (n : ℝ) ^ (-(4 / 3 : ℝ)) := fun n hn => by
    refine (h_i_all n hn).trans ?_
    gcongr
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  -- Bound for `(iii)`: `E_0 ≤ C * (η^2 + N^{-1/3})`
  have h_iii : designE0 N η ≤ C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
    have hsum_pi0 : Summable (fun n : ℕ => designPi0 N η (n + 2)) := by
      refine Summable.of_nonneg_of_le (fun n => designPi0_nonneg N η (by omega))
        (fun n => h_i_all (n + 2) (by omega)) (hZ43.mul_left _)
    unfold designE0
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    -- Split `tsum` at index `N - 1` (note `n + 2 ≤ N` iff `n < N - 1`, for `1 ≤ N`)
    have h_split := hsum_pi0.sum_add_tsum_nat_add (N - 1)
    have h_head : ∑ n ∈ Finset.range (N - 1), designPi0 N η (n + 2) ≤ C_pref_in * Z43 * η ^ 2 := by
      have h_term : ∀ n ∈ Finset.range (N - 1),
          designPi0 N η (n + 2) ≤ C_pref_in * η ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
        intro n hn
        have hnN : n + 2 ≤ N := by
          have := Finset.mem_range.mp hn; omega
        -- Use the proof of h_ii with `C_pref_in`
        have hn_pos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
        have hprod := hprod_bd N η hη0 hη1 (n + 2) (by omega)
        have hsite : designSiteU N (n + 2) = airyZero (n + 2) := by simp [designSiteU, hnN]
        have hwidth : designWidthU N η (n + 2) = η * gapWKB (n + 2) := by simp [designWidthU, hnN]
        have hgap := gapWKB_le_mul_rpow (by omega : 1 ≤ n + 2)
        have hgap_nn : 0 ≤ gapWKB (n + 2) := (gapWKB_pos (by omega : 1 ≤ n + 2)).le
        have hwidth_sq : (designWidthU N η (n + 2)) ^ 2 ≤ η ^ 2 * C_gap_sq * ((n + 2 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := by
          rw [hwidth, mul_pow]
          have hsq := pow_le_pow_left₀ hgap_nn hgap 2
          rw [mul_pow, ← Real.rpow_natCast (((n + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
            show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
          have heta : 0 ≤ η ^ 2 := sq_nonneg η
          calc η ^ 2 * gapWKB (n + 2) ^ 2 ≤ η ^ 2 * (C_gap ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ))) :=
                mul_le_mul_of_nonneg_left hsq heta
            _ = η ^ 2 * C_gap_sq * ((n + 2 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
        have hsep := h_a1_sep (n + 2) (by omega)
        have hrpow_div : ((n + 2 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) / ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ) =
            ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
          rw [← Real.rpow_sub hn_pos]; congr 2; norm_num
        unfold designPi0
        rw [hsite, sub_self, zero_pow two_ne_zero, zero_add]
        calc (designWidthU N η (n + 2)) ^ 2 / |airyZero (n + 2) - airyZero 1| *
              ∏' m : ℕ, (if m + 2 = n + 2 then 1 else designRealFactor N η (n + 2) (m + 2))
            ≤ (η ^ 2 * C_gap_sq * ((n + 2 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ))) /
                ((9 / 10 : ℝ) * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * C_prod := by
              gcongr
              have hp := (designPi0_hasProd N η (by omega : 2 ≤ n + 2)).1
              refine ge_of_tendsto hp (Eventually.of_forall fun s =>
                Finset.prod_nonneg fun m _ => by split_ifs; exact zero_le_one; unfold designRealFactor; positivity)
          _ = C_pref_in * η ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
              rw [← hrpow_div]; dsimp [C_pref_in]; ring
      calc ∑ n ∈ Finset.range (N - 1), designPi0 N η (n + 2)
          ≤ ∑ n ∈ Finset.range (N - 1), C_pref_in * η ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) :=
            Finset.sum_le_sum h_term
        _ = C_pref_in * η ^ 2 * ∑ n ∈ Finset.range (N - 1), ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ C_pref_in * η ^ 2 * Z43 := by
            gcongr; exact hZ43.sum_le_tsum _ fun _ _ => by positivity
        _ = C_pref_in * Z43 * η ^ 2 := by ring
    have h_tail : ∑' n : ℕ, designPi0 N η (n + (N - 1) + 2) ≤ 3 * C_i * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
      have h_le : ∀ n : ℕ, designPi0 N η (n + (N - 1) + 2) ≤
          C_i * ((N + 1 + n : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := fun n => by
        rw [show n + (N - 1) + 2 = N + 1 + n by omega]
        exact h_i_all (N + 1 + n) (by omega)
      have hsum_tail : Summable (fun n : ℕ => C_i * ((N + 1 + n : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) := by
        have h1 := (summable_nat_add_iff (N + 1)).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
        exact (h1.congr fun n => by rw [Nat.add_comm n (N + 1)]).mul_left C_i
      have hsum_l : Summable (fun n : ℕ => designPi0 N η (n + (N - 1) + 2)) :=
        (summable_nat_add_iff (f := fun k => designPi0 N η (k + 2)) (N - 1)).mpr hsum_pi0
      calc ∑' n : ℕ, designPi0 N η (n + (N - 1) + 2)
          ≤ ∑' n : ℕ, C_i * ((N + 1 + n : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) :=
            hsum_l.tsum_le_tsum h_le hsum_tail
        _ = C_i * ∑' n : ℕ, ((N + 1 + n : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := tsum_mul_left
        _ ≤ C_i * (3 * (N : ℝ) ^ (-(1 / 3 : ℝ))) := by
            gcongr; exact rpow_neg_four_thirds_sum_tail N hN1
        _ = 3 * C_i * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
    have hCe_le : C_e ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have h1' : C_pref_in * Z43 ≤ C_e := le_max_left _ _
    have h2' : 3 * C_i ≤ C_e := le_max_right _ _
    calc ∑' n : ℕ, designPi0 N η (n + 2)
        = ∑ n ∈ Finset.range (N - 1), designPi0 N η (n + 2) +
            ∑' n : ℕ, designPi0 N η (n + (N - 1) + 2) := h_split.symm
      _ ≤ C_pref_in * Z43 * η ^ 2 + 3 * C_i * (N : ℝ) ^ (-(1 / 3 : ℝ)) := add_le_add h_head h_tail
      _ ≤ C * η ^ 2 + C * (N : ℝ) ^ (-(1 / 3 : ℝ)) :=
          add_le_add
            (mul_le_mul_of_nonneg_right (h1'.trans hCe_le) (sq_nonneg η))
            (mul_le_mul_of_nonneg_right (h2'.trans hCe_le) (by positivity))
      _ = C * (η ^ 2 + (N : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
  -- Bound for `(iv)`: `1/2 ≤ R_1 ≤ C`
  have h_iv : 1 / 2 ≤ designR1 N η ∧ designR1 N η ≤ C := by
    have hN1_le : N₁ ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
    have hN2_le : N₂ ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
    have hN_1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hR1 := designR1_bounds_aux C_Z C_gap C_eps C_sq C_R C_R_ub Z2
      hC_Z hδ rfl rfl rfl rfl rfl hZ2 rfl N₁ N₂ hN₁ hN₂ N hN_1 hN1_le hN2_le η hη0 hη1 h_a1_sep
    exact ⟨hR1.1, hR1.2.trans (le_max_left _ _)⟩
  exact ⟨h_i, h_ii, h_iii, h_iv⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_V_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_V_hasSum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_V_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_V_identity

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Window.lemma_E

end FormalResearch.ModularBootstrap.Upper.Window

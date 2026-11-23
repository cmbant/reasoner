module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileBound

/-!
# Real products of the Airy profile: `R_1`, `Π_n(0)`, `E_0` (`ut:V`, `ut:E`, `rem:profile`)

For an arbitrary site/width profile `(uSite, epsU)` satisfying the tail hypothesis, the real
quantities of Lemma V (`upper_transfer.tex`, `ut:V`) at the Airy zeros:

* `profRealFactor n k = ((a_n - u_k)² + ε_k²) / (a_n - a_k)²`;
* `profR1 = ∏_{k ≥ 2} profRealFactor 1 k`, `profPi0 n` (`Π_n(0)`), `profPi d n = Π_n(d)`, `profE0`;
* `profR1_hasProd`, `profPi0_hasProd`: unconditional convergence, with the identification of the
  complex tail products at `a_n` with these real products; non-negativity.

These are the profile versions of `designR1`, `designPi0`, ... of `Window/Quadrature.lean` (which
are the special case `(designSiteU N, designWidthU N η)`).  The summation helpers at the end are
copies of the private ones there.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- Real factor in `R_1` and `Π_n(0)` for a profile: `((a_n - u_k)² + ε_k²) / (a_n - a_k)²`. -/
noncomputable def profRealFactor (uSite epsU : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ((airyZero n - uSite k) ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2

/-- `R_1 = ∏_{k ≥ 2} ((a_1 - u_k)² + ε_k²) / (a_1 - a_k)²`. -/
noncomputable def profR1 (uSite epsU : ℕ → ℝ) : ℝ :=
  ∏' m : ℕ, profRealFactor uSite epsU 1 (m + 2)

/-- Zero-shift weight `Π_n(0)` for `n ≥ 2`. -/
noncomputable def profPi0 (uSite epsU : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) / |airyZero n - airyZero 1| *
    ∏' m : ℕ, if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2)

/-- Shifted weight `Π_n(d) = Π_n(0) (1 - d / |a_n - a_1|)` for `n ≥ 2`. -/
noncomputable def profPi (uSite epsU : ℕ → ℝ) (d : ℝ) (n : ℕ) : ℝ :=
  profPi0 uSite epsU n * (1 - d / |airyZero n - airyZero 1|)

/-- Total zero-shift cost `E_0 = ∑_{n ≥ 2} Π_n(0)`. -/
noncomputable def profE0 (uSite epsU : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, profPi0 uSite epsU (n + 2)

lemma ofReal_profRealFactor (uSite epsU : ℕ → ℝ) (n k : ℕ) :
    (profRealFactor uSite epsU n k : ℂ) =
      airyProdFactor uSite epsU k (airyZero n : ℂ) := by
  unfold profRealFactor airyProdFactor
  push_cast; rfl

lemma hasProd_real_of_complex {f : ℕ → ℝ} {z : ℂ}
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

lemma profR1_hasProd (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) :
    HasProd (fun m : ℕ => profRealFactor uSite epsU 1 (m + 2)) (profR1 uSite epsU) ∧
    airyProdTail 1 uSite epsU (airyZero 1 : ℂ) =
      (profR1 uSite epsU : ℂ) := by
  have hne : ∀ k : ℕ, 1 < k → (airyZero 1 : ℂ) ≠ (airyZero k : ℂ) := fun k hk h => by
    have := airyZero_injective_on le_rfl (by omega) (Complex.ofReal_injective h)
    omega
  have hp := hasProd_airyProdTail hH hne
  have hp' : HasProd (fun m : ℕ => (profRealFactor uSite epsU 1 (m + 2) : ℂ))
      (airyProdTail 1 uSite epsU (airyZero 1 : ℂ)) := by
    refine hp.congr_fun fun m => ?_
    rw [show 1 + 1 + m = m + 2 by ring, ofReal_profRealFactor]
  obtain ⟨hre, hcm⟩ := hasProd_real_of_complex hp'
  have heq : profR1 uSite epsU = (airyProdTail 1 uSite epsU (airyZero 1 : ℂ)).re :=
    hre.tprod_eq
  rw [← heq] at hre hcm
  exact ⟨hre, hcm⟩

lemma profPi0_hasProd (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) {n : ℕ} (hn : 2 ≤ n) :
    HasProd (fun m : ℕ => if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2))
      (∏' m : ℕ, if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2)) ∧
    airyProdTailExcept 1 n uSite epsU (airyZero n : ℂ) =
      ((∏' m : ℕ, if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2) : ℝ) : ℂ) := by
  have hne : ∀ k : ℕ, 1 < k → k ≠ n → (airyZero n : ℂ) ≠ (airyZero k : ℂ) := fun k hk hkn h =>
    hkn (airyZero_injective_on (by omega) (by omega) (Complex.ofReal_injective h.symm))
  have hp := hasProd_airyProdTailExcept (f := 1) (n := n) hH hne
  have hp' : HasProd (fun m : ℕ =>
      ((if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2) : ℝ) : ℂ))
      (airyProdTailExcept 1 n uSite epsU (airyZero n : ℂ)) := by
    refine hp.congr_fun fun m => ?_
    rw [show 1 + 1 + m = m + 2 by ring]
    split_ifs <;> simp [ofReal_profRealFactor]
  obtain ⟨hre, hcm⟩ := hasProd_real_of_complex hp'
  have ht := hre.tprod_eq
  rw [← ht] at hre hcm
  exact ⟨hre, hcm⟩

lemma profR1_nonneg (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) : 0 ≤ profR1 uSite epsU := by
  have hp := (profR1_hasProd uSite epsU hH).1
  refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
  refine Finset.prod_nonneg fun m _ => ?_
  unfold profRealFactor
  positivity

lemma profPi0_nonneg (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ profPi0 uSite epsU n := by
  unfold profPi0
  have hp := (profPi0_hasProd uSite epsU hH hn).1
  have hprod : 0 ≤ ∏' m : ℕ, if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2) := by
    refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
    refine Finset.prod_nonneg fun m _ => ?_
    split_ifs
    · exact zero_le_one
    · unfold profRealFactor; positivity
  have hpre : 0 ≤ ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) /
      |airyZero n - airyZero 1| := by positivity
  exact mul_nonneg hpre hprod

/-! ### Section 2: Lemma V (`ut:V`) — Airy quadrature evaluation -/

lemma rpow_neg_four_thirds_sum_tail (N : ℕ) (hN : 1 ≤ N) :
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


lemma rpow_neg_two_thirds_partial_sum_q (M : ℕ) :
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

lemma one_div_sq_sum_tail_le (N : ℕ) (hN : 1 ≤ N) :
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

lemma exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
  have hpos1 : 0 < 1 + 2 * t := by linarith
  have hpos2 : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [show (-2 * t : ℝ) = -(2 * t) by ring, Real.exp_neg]
  calc (Real.exp (2 * t))⁻¹ ≤ (1 + 2 * t)⁻¹ := inv_anti₀ hpos1 h2
    _ ≤ 1 - t := by rw [← one_div, div_le_iff₀ hpos1]; linarith


end FormalResearch.ModularBootstrap.Upper.Ramped

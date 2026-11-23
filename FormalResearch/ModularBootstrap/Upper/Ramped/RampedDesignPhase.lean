module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesign

/-!
# `PhaseHyp`, the phase package and Lemma `K7` for the ramped comb `D_*` (`rem:thmU` Step (1))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), Step (1); `upper_transfer.tex`, Lemma `Φ`
(`ut:Phi`) with the pair-change bound `(PC)`.

* `rampedPairChange_le`: the total pair change `|Δ_1| + Σ_j(|ε'_j² - ε⁰_j²| + 2|Δ_j|)` of `D_*` against the
  reference comb is at most `C λ = O(c'^{-2/3})`, uniformly in `C_I, C_mid ≥ 1` and `d ∈ [0, 1]`, with no
  dependence on the number `n_cap ≍ 0.036 c'` of changed pairs (`(1/16)Σℓ_k² = O(c'^{-1})`, `Σ|Δ_k| = O(λ)`);
* `ramped_phaseHyp`: `PhaseHyp c' 1 (n_cap + 6) (1/4) σ ε' 1` for `c'` large (absolute threshold);
* `ramped_phase_package`: the consequences of `phase_package` (`θ = 3/5`): `DesignPhiDecomp` with an absolute `K`,
  the `SD_V` hypotheses with `c'`-independent constants, the transform bound `1 + C c'^{-1/10}` for
  `x ≥ ξ_* + c'^{-3/5}`, the `SD_G` global bound;
* `ramped_k7`: Lemma `K7` for `D_*` (`g ∈ Ā`, the vacuum identity, `|h_{0,vac}| ≤ 8`).

**What the consumers use.**  R5 (Region I) and R6 (Region II) take the global bound
`e^{c'L(x)}‖ĥ₀(c'x²/3)‖ ≤ K_G √(c'/x)` and the transform bound `‖ĥ₀‖ ≤ combAmplitude c' x (1 + C c'^{-1/10})` from
`ramped_phase_package`; R7 (vacuum) takes `ramped_k7`.  The power-sum lemmas `sum_Icc_rpow_neg_lt_one`,
`sum_Ioc_rpow_neg_gt_one` are reused in `RampedDesignShift`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Membership Upper.Hankel Upper.Saddle Crossing

/-! ### 1. Power sums -/

/-- Mean-value lower bound `q (a+1)^{q-1} ≤ (a+1)^q - a^q` for `0 < q < 1`, `a ≥ 0`. -/
lemma rpow_sub_ge {q a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha : 0 ≤ a) :
    q * (a + 1) ^ (q - 1) ≤ (a + 1) ^ q - a ^ q := by
  have hlt : a < a + 1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ q) (Icc a (a + 1)) :=
    continuousOn_id.rpow_const fun t ht => Or.inr hq0.le
  have hdiff : ∀ t ∈ Ioo a (a + 1), HasDerivAt (fun x : ℝ => x ^ q) (q * t ^ (q - 1)) t := fun t ht => by
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    simpa using (hasDerivAt_id t).rpow_const (p := q) (Or.inl ht0.ne')
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ q) (fun t => q * t ^ (q - 1))
    hlt hcont hdiff
  have hc0 : 0 < c := lt_of_le_of_lt ha hc.1
  have hslope : (a + 1) ^ q - a ^ q = q * c ^ (q - 1) := by
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne'), show a + 1 - a = 1 by ring, mul_one] at hmv
    exact hmv.symm
  rw [hslope]
  have : (a + 1) ^ (q - 1) ≤ c ^ (q - 1) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  exact mul_le_mul_of_nonneg_left this hq0.le

/-- Mean-value bound `(p-1) (a+1)^{-p} ≤ a^{1-p} - (a+1)^{1-p}` for `p > 1`, `a > 0`. -/
lemma rpow_sub_ge' {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    (p - 1) * (a + 1) ^ (-p) ≤ a ^ (1 - p) - (a + 1) ^ (1 - p) := by
  have hlt : a < a + 1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 - p)) (Icc a (a + 1)) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (lt_of_lt_of_le ha ht.1).ne'
  have hdiff : ∀ t ∈ Ioo a (a + 1), HasDerivAt (fun x : ℝ => x ^ (1 - p)) ((1 - p) * t ^ (1 - p - 1)) t :=
    fun t ht => by
      have ht0 : 0 < t := lt_trans ha ht.1
      simpa using (hasDerivAt_id t).rpow_const (p := 1 - p) (Or.inl ht0.ne')
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 - p))
    (fun t => (1 - p) * t ^ (1 - p - 1)) hlt hcont hdiff
  have hc0 : 0 < c := lt_trans ha hc.1
  have hslope : (a + 1) ^ (1 - p) - a ^ (1 - p) = (1 - p) * c ^ (1 - p - 1) := by
    rw [eq_div_iff (sub_ne_zero.mpr hlt.ne'), show a + 1 - a = 1 by ring, mul_one] at hmv
    exact hmv.symm
  have h1 : (a + 1) ^ (-p) ≤ c ^ (-p) := Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  have h2 : (1 - p - 1) = -p := by ring
  rw [h2] at hslope
  nlinarith

/-- `∑_{k ∈ (a, b]} k^{-p} ≤ b^{1-p}/(1-p)` for `0 < p < 1`, `a = 0`. -/
lemma sum_Icc_rpow_neg_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-p) ≤ (M : ℝ) ^ (1 - p) / (1 - p) := by
  induction M with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg (by simp) _) (by linarith)
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have h := rpow_sub_ge (q := 1 - p) (a := (M : ℝ)) (by linarith) (by linarith) (Nat.cast_nonneg M)
    rw [show (1 - p - 1) = -p by ring] at h
    have h1p : 0 < 1 - p := by linarith
    have : (M : ℝ) ^ (1 - p) / (1 - p) + ((M : ℝ) + 1) ^ (-p) ≤ ((M : ℝ) + 1) ^ (1 - p) / (1 - p) := by
      rw [← sub_nonneg]
      have e : ((M : ℝ) + 1) ^ (1 - p) / (1 - p) - ((M : ℝ) ^ (1 - p) / (1 - p) + ((M : ℝ) + 1) ^ (-p)) =
          (((M : ℝ) + 1) ^ (1 - p) - (M : ℝ) ^ (1 - p) - (1 - p) * ((M : ℝ) + 1) ^ (-p)) / (1 - p) := by
        field_simp
        ring
      rw [e]
      exact div_nonneg (by linarith) h1p.le
    exact (add_le_add_left ih _).trans this

/-- `∑_{k ∈ (a, b]} k^{-p} ≤ (a^{1-p} - b^{1-p})/(p-1)` for `p > 1`, `1 ≤ a ≤ b`. -/
lemma sum_Ioc_rpow_neg_gt_one_aux {p : ℝ} (hp : 1 < p) {a : ℕ} (ha : 1 ≤ a) {b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (k : ℝ) ^ (-p) ≤ ((a : ℝ) ^ (1 - p) - (b : ℝ) ^ (1 - p)) / (p - 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, Nat.cast_succ]
    have hb0 : (0 : ℝ) < b := by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have h := rpow_sub_ge' hp hb0
    have hp1 : 0 < p - 1 := by linarith
    have : ((a : ℝ) ^ (1 - p) - (b : ℝ) ^ (1 - p)) / (p - 1) + ((b : ℝ) + 1) ^ (-p) ≤
        ((a : ℝ) ^ (1 - p) - ((b : ℝ) + 1) ^ (1 - p)) / (p - 1) := by
      rw [← sub_nonneg]
      have e : ((a : ℝ) ^ (1 - p) - ((b : ℝ) + 1) ^ (1 - p)) / (p - 1) -
          (((a : ℝ) ^ (1 - p) - (b : ℝ) ^ (1 - p)) / (p - 1) + ((b : ℝ) + 1) ^ (-p)) =
          ((b : ℝ) ^ (1 - p) - ((b : ℝ) + 1) ^ (1 - p) - (p - 1) * ((b : ℝ) + 1) ^ (-p)) / (p - 1) := by
        field_simp
        ring
      rw [e]
      exact div_nonneg (by linarith) hp1.le
    exact (add_le_add_left ih _).trans this

/-- Tail bound `∑_{k ∈ (a, b]} k^{-p} ≤ a^{1-p}/(p-1)` for `p > 1`, `a ≥ 1`, every `b`. -/
lemma sum_Ioc_rpow_neg_gt_one {p : ℝ} (hp : 1 < p) {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ k ∈ Finset.Ioc a b, (k : ℝ) ^ (-p) ≤ (a : ℝ) ^ (1 - p) / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  rcases le_or_gt b a with hba | hab
  · rw [Finset.Ioc_eq_empty_of_le hba, Finset.sum_empty]
    have : (0 : ℝ) < a := by exact_mod_cast ha
    positivity
  · refine (sum_Ioc_rpow_neg_gt_one_aux hp ha hab.le).trans ?_
    have hb0 : (0 : ℝ) < b := by
      have : (a : ℝ) < b := by exact_mod_cast hab
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hb0 (1 - p)]) hp1.le


lemma sum_range_shift (g : ℕ → ℝ) (f m : ℕ) :
    ∑ j ∈ Finset.range m, g (f + 1 + j) = ∑ k ∈ Finset.Ioc f (f + m), g k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show f + (m + 1) = (f + m) + 1 by ring,
      Finset.sum_Ioc_succ_top (by omega)]
    congr 2
    ring

lemma eventually_lambda_cbrt : ∀ᶠ c' : ℝ in atTop, lambdaComb c' * c' ^ (1 / 3 : ℝ) ≤ 1 := by
  have hk := kTip_pos
  have hK : 0 < kTip ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hk _
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_rpow_neg_le (p := 1 / 3) (by norm_num) (inv_pos.2 hK)] with c' hc' h
  unfold lambdaComb
  rw [Real.mul_rpow hk.le hc'.le, mul_assoc, ← Real.rpow_add hc']
  have : kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ) + 1 / 3) ≤ kTip ^ (-(2 / 3 : ℝ)) * (kTip ^ (-(2 / 3 : ℝ)))⁻¹ := by
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    rwa [show (-(2 / 3 : ℝ) + 1 / 3) = -(1 / 3 : ℝ) by norm_num]
  rwa [mul_inv_cancel₀ hK.ne'] at this

/-- The total pair change of the ramped comb is `O(λ) = O(c'^{-2/3})`, uniformly in `C_I, C_mid` and
`d ∈ [0, 1]` (`rem:thmU`, Step (1): `Σ|(ε'_k)² - (ε^ref_k)²| ≤ (1/16)Σ ℓ_k² = O(c'^{-1})`, `Σ|Δ_k| = O(λ)`). -/
theorem rampedPairChange_le : ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ),
    0 ≤ d → d ≤ 1 →
      designPairChange c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') ≤ C * lambdaComb c' := by
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  refine ⟨Cs + Cg ^ 2 * 3 / 16 + 2 * Cs * 3, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max c0g 10000), eventually_lambda_cbrt] with c' hc' hlc P d hd hd1
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'
  have hc'1 : 10000 ≤ c' := (le_max_right _ _).trans hc'
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans hc'
  have hl := lambdaComb_pos' hc'0
  set N := nCap P c' + 6 with hN
  have hNc : (N : ℝ) ≤ c' := by
    have := nCap_le P hc'1
    rw [hN]; push_cast; linarith
  rw [designPairChange_eq, sum_range_shift (fun k => |rampedEps P c' k ^ 2 - (1 / 4 * siteGap c' k) ^ 2|),
    sum_range_shift (fun k => |designSite c' (rampedSigma d c') k - chiQuantile c' ((k : ℕ) : ℝ)|)]
  have hN1 : 1 + (N - 1) = N := by omega
  rw [hN1]
  have hNp : (0 : ℝ) < N := by rw [hN]; positivity
  -- the first site
  have h1 : |designSite c' (rampedSigma d c') 1 - chiQuantile c' ((1 : ℕ) : ℝ)| ≤ Cs * lambdaComb c' := by
    have := hsh c' hc'0 d hd hd1 1 le_rfl
    simpa using this
  -- the squared-width changes
  have hpt2 : ∀ k ∈ Finset.Ioc 1 N, |rampedEps P c' k ^ 2 - (1 / 4 * siteGap c' k) ^ 2| ≤
      Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    obtain ⟨-, hgu⟩ := hgap P c' hcg' k (by omega) (by omega)
    have hg0 : 0 ≤ siteGap c' k := siteGap_nonneg hc'0 (by omega)
    have hη2 := rampedEta_sq P hc'0 k
    have hη0 : 0 ≤ etaSq P c' k := etaSq_nonneg P hc'0 k
    have hη1 := etaSq_le P c' k
    have e1 : rampedEps P c' k ^ 2 - (1 / 4 * siteGap c' k) ^ 2 =
        siteGap c' k ^ 2 * (etaSq P c' k - 1 / 16) := by
      unfold rampedEps; rw [mul_pow, hη2]; ring
    rw [e1, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonpos (by linarith)]
    have hkk : ((k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 = (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkp.le]; norm_num
    have hsq : siteGap c' k ^ 2 ≤ Cg ^ 2 * lambdaComb c' ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have h0 : 0 ≤ Cg * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
      calc siteGap c' k ^ 2 ≤ (Cg * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ hg0 hgu 2
        _ = Cg ^ 2 * lambdaComb c' ^ 2 * ((k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by ring
        _ = _ := by rw [hkk]
    nlinarith [sq_nonneg (siteGap c' k)]
  have h2 : ∑ k ∈ Finset.Ioc 1 N, |rampedEps P c' k ^ 2 - (1 / 4 * siteGap c' k) ^ 2| ≤
      Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ)) := by
    refine (Finset.sum_le_sum hpt2).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by
      have := sum_Icc_rpow_neg_lt_one (p := 2 / 3) (by norm_num) (by norm_num) N
      have hsub : ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
          simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega)
          (fun k _ _ => by positivity)
      refine hsub.trans (this.trans ?_)
      rw [show (1 - 2 / 3 : ℝ) = 1 / 3 by norm_num]
      have : (N : ℝ) ^ (1 / 3 : ℝ) / (1 / 3) = 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by ring
      linarith [this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  -- the site displacements
  have h3 : ∑ k ∈ Finset.Ioc 1 N, |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤
      Cs * lambdaComb c' * 3 := by
    have hpt : ∀ k ∈ Finset.Ioc 1 N, |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤
        Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) := fun k hk =>
      hsh c' hc'0 d hd hd1 k (by have := (Finset.mem_Ioc.mp hk).1; omega)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl N
    simp only [Nat.cast_one, Real.one_rpow] at this
    have e : (1 : ℝ) / (4 / 3 - 1) = 3 := by norm_num
    exact mul_le_mul_of_nonneg_left (this.trans (by rw [e])) (by positivity)
  have hlN : lambdaComb c' * (N : ℝ) ^ (1 / 3 : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hNp.le hNc (by norm_num)) hl.le).trans hlc
  have h4 : Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ)) ≤
      Cg ^ 2 * 3 / 16 * lambdaComb c' := by
    calc Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ))
        = Cg ^ 2 * 3 / 16 * lambdaComb c' * (lambdaComb c' * (N : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ ≤ Cg ^ 2 * 3 / 16 * lambdaComb c' * 1 := by gcongr
      _ = _ := by ring
  have h5 := add_le_add (add_le_add h1 (h2.trans h4)) (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2))
  refine h5.trans (le_of_eq ?_)
  ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedPairChange_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedPairChange_le


/-! ### 2. `PhaseHyp` for `D_*` and the phase package -/

/-- **`PhaseHyp` for the ramped comb** (`rem:thmU`, Step (1)): for `c'` large (threshold absolute) and every
`C_I, C_mid ≥ 1`, `d ∈ [0, 1]`, the cut `n_cap + 6 ≥ 1`, the sites `χ'_k ≥ ξ_*`, the widths `η_kℓ_k ≤ 1/8` and the total
pair change `≤ 1` (in fact `O(λ)`, `rampedPairChange_le`).  This is also the non-vacuity statement of the
hypothesis of `phase_package` for the ramped data. -/
theorem ramped_phaseHyp : ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ 1 →
    PhaseHyp c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') 1 := by
  obtain ⟨C, hC, hpc⟩ := rampedPairChange_le
  have hlam : ∀ᶠ c' : ℝ in atTop, C * lambdaComb c' ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [phaseHyp_of_nonneg 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    abs_height_le_eighth, hpc, hlam, eventually_gt_atTop (0 : ℝ)] with c' h1 h2 h3 h4 hc' P d hd hd1
  refine h1 (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') 1 (by omega)
    (xiStar_pos.le.trans (designSite_ramped_nonneg hc' hd le_rfl))
    (fun i _ => xiStar_pos.le.trans (designSite_ramped_nonneg hc' hd (by omega)))
    (fun i _ => h2 _ (by omega) _ (rampedEta_nonneg P c' _) (rampedEta_le P c' _))
    ((h3 P d hd hd1).trans h4)

/-- **The phase package for `D_*`** (`ut:Phi` with `(PC)`, `SD_V`, `SD_G`; `rem:thmU` Step (1)): absolute constants
`K, A, C, K_G` and `c₀` such that for every `c' ≥ c₀`, `C_I, C_mid ≥ 1`, `d ∈ [0, 1]` the ramped comb
`B_{D_*}` has `DesignPhiDecomp` of derivative bound `K`, the `SD_V` hypotheses with `c'`-independent constants
`𝒜₀ + A + K`, `𝒜₀' + A + K`, the transform bound `‖ĥ₀(c'x²/3)‖ ≤ 𝒜_x(1 + C c'^{-1/10})` for `x ≥ ξ_* + c'^{-3/5}`
(`θ = 3/5`, exponent `-1 + 3θ/2 = -1/10`) and the global bound `e^{c'L}‖ĥ₀‖ ≤ K_G √(c'/x)`. -/
theorem ramped_phase_package : ∃ K A C KG : ℝ, 0 < K ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 ≤ KG ∧ ∀ᶠ c' : ℝ in atTop,
    ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ 1 →
      DesignPhiDecomp c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') K ∧
      (∀ x : ℝ, xiStar ≤ x →
        SDVHypotheses edgePhi0Blaschke x c' (1 / 8) (ampM0 + (A + K)) (ampM0' + (A + K)) sechSqProfile
          (designPhi1 c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c')) hankel0 hankelEps) ∧
      (∀ x : ℝ, xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
        ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
          (c' * x ^ 2 / 3)‖ ≤ combAmplitude c' x * (1 + C * c' ^ (-(1 / 10 : ℝ)))) ∧
      (∀ x : ℝ, 0 < x → Real.exp (c' * edgeL x) *
        ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
          (c' * x ^ 2 / 3)‖ ≤ KG * √(c' / x)) := by
  obtain ⟨K, A, C, KG, hK, hA, hC, hKG, hev⟩ := phase_package 1 le_rfl (η₀ := 1 / 4) (by norm_num)
    (by norm_num) (P := 1) zero_le_one (θ := 3 / 5) (by norm_num) (by norm_num)
  refine ⟨K, A, C, KG, hK, hA, hC, hKG, ?_⟩
  filter_upwards [hev, ramped_phaseHyp] with c' h hP P d hd hd1
  obtain ⟨h1, h2, h3, h4⟩ := h (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') (hP P d hd hd1)
  have e : (-1 + 3 * (3 / 5 : ℝ) / 2) = -(1 / 10 : ℝ) := by norm_num
  rw [mul_one] at h1 h2
  rw [e] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- **Lemma `K7` for `D_*`** (`cmb:K7`, `w = 1`): for a fixed-weight problem with `w = 1` there is an absolute
`K > 0` such that for `c'` large and all `C_I, C_mid ≥ 1`, `d ∈ [0, 1]`: `h₀ = sech² B_{D_*}` and `ĥ₀` decay,
`g = ½(h₀ - ĥ₀)` is in the test class (membership in `Ā`), `g_vac = ½ h_{0,vac} - π∫h₀V`, and `|h_{0,vac}| ≤ 8`
for `Q = (1-q)²` (`K7Conclusion`). -/
theorem ramped_k7 {prob : FixedWeightProblem} (hw : prob.w = 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ 1 →
      K7Conclusion prob c' (rampedComb P d c') := by
  obtain ⟨K, hK, hev⟩ := phase_k7 hw 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num) (P := 1) zero_le_one
  refine ⟨K, hK, ?_⟩
  filter_upwards [hev, ramped_phaseHyp] with c' h hP P d hd hd1
  exact h (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') (hP P d hd hd1)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_phaseHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ramped_phaseHyp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_phase_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ramped_phase_package

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_k7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ramped_k7

end FormalResearch.ModularBootstrap.Upper.Ramped

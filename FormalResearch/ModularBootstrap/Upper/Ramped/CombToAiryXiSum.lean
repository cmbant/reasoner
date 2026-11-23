module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryXi

/-!
# `∑_{k ≥ 2} |Ξ_k| ≤ C λ` (`rem:P1.2`, Step 3)

`xi_sum`: for every design and every `x ∈ [ξ_*/2, ξ_* + 1/2]` that is not a site `χ'_k`, `k ≥ 2`, the partial
sums `∑_{k=2}^n |Ξ_k|` are bounded by `C λ`, with `C, c₀` depending only on `C_sh, c_sep`.  The proof sums
the per-pair bound `xi_pair_bound`: the first term by the integral comparison `sum_gap_exp_le` and
`ℓ_k ≤ C_g λ`, the second by the four-range near-pair sum `nearSum_le`.
-/

@[expose] public section

open Filter Topology Set Finset
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb

theorem xi_sum (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2),
      (∀ k : ℕ, 2 ≤ k → x ≠ siteX c' σ k) → ∀ n : ℕ,
        ∑ k ∈ Finset.Icc 2 n, |xiPair c' σ η x k| ≤ C * lambdaComb c' := by
  obtain ⟨C1, C2, c1, hC1, hC2, hc1, hpair⟩ := xi_pair_bound Csh
  obtain ⟨Cn, hCn, hnear⟩ := nearSum_le (c1 := csep) (C0 := 1) hcsep one_pos
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_le_unif
  obtain ⟨cτ, hcτ, _, hX⟩ := siteX_sub_chi
  set l1 : ℝ := cτ / (|Csh| + 1) with hl1
  have hl1p : 0 < l1 := by positivity
  have hev : ∀ᶠ c' in atTop, (∀ k : ℕ, 1 ≤ k →
      siteGap c' k ≤ Cg * lambdaComb c' ∧ siteGap c' k ≤ 1 / 2) ∧ lambdaComb c' < l1 :=
    hgev.and (tendsto_lambdaComb_atTop.eventually (gt_mem_nhds hl1p))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨C1 * Cg * Real.exp π * Real.exp (π / 2) + C2 * Cn, max (max N c1) 1,
    by positivity, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro c' hc' σ η h x hx hxk n
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hc')
  have hcN : N ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hcc1 : c1 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc') |> fun _ =>
    (le_max_right N c1).trans ((le_max_left _ _).trans hc')
  obtain ⟨hgap, hlam⟩ := hN c' hcN
  have hlp := lamPos hc'0
  have hx' : ∀ k : ℕ, 2 ≤ k → xiStar / 2 ≤ x := fun _ _ => hx.1
  -- the near-pair sum
  have hsum_near : ∑ k ∈ Finset.Icc 2 n, nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
      (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1) ≤ Cn := by
    refine hnear σ (fun k => η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
      (h.sep_pair hcsep) (fun k hk => ?_) (sigmaOf c' x) n
    obtain ⟨hp0, hp1⟩ := phi_diff_bounds (by omega : 1 ≤ k)
    obtain ⟨hη0, hη1⟩ := h.height k hk
    have hcr := cr_pos (by omega : 1 ≤ k)
    refine ⟨mul_nonneg hη0 hp0, ?_⟩
    have := mul_le_mul hη1 hp1 hp0 (by norm_num)
    linarith
  -- the exponential sum
  have hsum_exp : ∑ k ∈ Finset.Icc 2 n, siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) ≤
      Cg * lambdaComb c' * Real.exp π * Real.exp (π / 2) := by
    have hterm : ∀ k ∈ Finset.Icc 2 n, siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) ≤
        Cg * lambdaComb c' * Real.exp π *
          (siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)) := by
      intro k hk
      have hk2 := (Finset.mem_Icc.1 hk).1
      have hk1 : 1 ≤ k := by omega
      obtain ⟨hgk1, hgk2⟩ := hgap k hk1
      have hℓ0 : 0 ≤ siteGap c' k := Design.siteGap_nonneg hc'0 hk1
      have hdisp : |siteX c' σ k - chiQuantile c' (k : ℝ)| ≤ 1 := by
        have h1 := hX hc'0 σ k hk1 (h.nonneg k hk1)
        have h2 := h.near k hk1
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have h3 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hkR (by norm_num)
        have h4 : |σ k - phiQuantile (k : ℝ)| ≤ |Csh| := by
          refine h2.trans ?_
          calc Csh * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ |Csh| * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
                gcongr; exact le_abs_self _
            _ ≤ |Csh| * 1 := by gcongr
            _ = |Csh| := mul_one _
        have h5 : lambdaComb c' * |σ k - phiQuantile (k : ℝ)| / cτ ≤ lambdaComb c' * |Csh| / cτ := by
          gcongr
        have h6 : lambdaComb c' * |Csh| / cτ ≤ 1 := by
          rw [div_le_one hcτ]
          have : lambdaComb c' < cτ / (|Csh| + 1) := hlam
          rw [lt_div_iff₀ (by positivity)] at this
          nlinarith [abs_nonneg Csh]
        linarith
      have hexp : Real.exp (-π * |x - siteX c' σ k|) ≤
          Real.exp π * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : |chiQuantile c' (k : ℝ) - x| ≤ |x - siteX c' σ k| + 1 := by
          calc |chiQuantile c' (k : ℝ) - x| = |(chiQuantile c' (k : ℝ) - siteX c' σ k) +
                  (siteX c' σ k - x)| := by ring_nf
            _ ≤ |chiQuantile c' (k : ℝ) - siteX c' σ k| + |siteX c' σ k - x| := abs_add_le _ _
            _ ≤ 1 + |x - siteX c' σ k| := by
                rw [abs_sub_comm (chiQuantile c' (k : ℝ)) (siteX c' σ k), abs_sub_comm (siteX c' σ k) x]
                linarith
            _ = _ := add_comm _ _
        nlinarith [Real.pi_pos]
      have hsq : siteGap c' k ^ 2 ≤ siteGap c' k * (Cg * lambdaComb c') := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hgk1 hℓ0
      calc siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|)
          ≤ (siteGap c' k * (Cg * lambdaComb c')) *
              (Real.exp π * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)) := by
            gcongr
        _ = Cg * lambdaComb c' * Real.exp π *
            (siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)) := by ring
    calc _ ≤ ∑ k ∈ Finset.Icc 2 n, Cg * lambdaComb c' * Real.exp π *
          (siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|)) := Finset.sum_le_sum hterm
      _ = Cg * lambdaComb c' * Real.exp π * ∑ k ∈ Finset.Icc 2 n,
          siteGap c' k * Real.exp (-π * |chiQuantile c' (k : ℝ) - x|) := by rw [← Finset.mul_sum]
      _ ≤ Cg * lambdaComb c' * Real.exp π * Real.exp (π / 2) := by
          have := sum_gap_exp_le hc'0 (fun k hk => (hgap k hk).2) x n
          gcongr
  have hcN1 : c1 ≤ c' := hcc1
  calc ∑ k ∈ Finset.Icc 2 n, |xiPair c' σ η x k|
      ≤ ∑ k ∈ Finset.Icc 2 n, (C1 * (siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|)) +
        C2 * lambdaComb c' * (nearT (η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))
          (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 := (Finset.mem_Icc.1 hk).1
        have := hpair hcN1 h x hx k hk2 (hxk k hk2)
        linarith
    _ = C1 * ∑ k ∈ Finset.Icc 2 n, siteGap c' k ^ 2 * Real.exp (-π * |x - siteX c' σ k|) +
        C2 * lambdaComb c' * ∑ k ∈ Finset.Icc 2 n, nearT (η k * (phiQuantile ((k : ℝ) + 1) -
          phiQuantile (k : ℝ))) (sigmaOf c' x - σ k) * (|sigmaOf c' x - σ k| + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ C1 * (Cg * lambdaComb c' * Real.exp π * Real.exp (π / 2)) + C2 * lambdaComb c' * Cn := by
        gcongr
    _ = (C1 * Cg * Real.exp π * Real.exp (π / 2) + C2 * Cn) * lambdaComb c' := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.xi_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xi_sum

end FormalResearch.ModularBootstrap.Upper.Ramped

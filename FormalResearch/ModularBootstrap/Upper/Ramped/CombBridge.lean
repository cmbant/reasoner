module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryMain
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesign

/-!
# The ramped comb `D_*` is a design of Proposition 1.2(2) (`rem:thmU`, `rem:P1.2`)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Steps (2) and (5) (they call
`Proposition 1.2` for `B_{D_*}`); `remainder.tex`, Proposition 1.2(2) (`combToAiry_amplitude`, `combToAiry_mult`).

The ramped comb `rampedComb P d c'` of `RampedDesign` is `designComb c' 1 (n_cap + 6) (1/4) σ ε'` (a simple zero
at `χ'_1`, pairs `χ'_k ± iε'_k` for `2 ≤ k ≤ n_cap + 6`, the reference pairs `χ_k ± iℓ_k/4` beyond the cut).  The
comb of Proposition 1.2(2) is `combBD c' σ̃ η̃` (`CombToAiryDef`), with sites `χ'_k = τ⁻¹(λ σ̃_k)` for all `k` and
widths `η̃_k ℓ_k`.  The two coincide for the extended sequences

* `σ̃_k = rampedNode d c' k` (the Airy node `s_k` for `k ≤ N_Ai`, `(|a_1| + d)/κ` for `k = 1`, `Φ_k` beyond), so that
  `χ'_k = designSite c' (rampedSigma d c') k = siteX c' σ̃ k` (`designSite_rampedSigma`), and the reference site
  `χ_k = τ⁻¹(λ Φ_k)` for `k > N_Ai`;
* `η̃_k = rampedEta P c' k` for all `k` (`rampedEta_eq_quarter`: `η̃_k = 1/4` for `k ≥ n_cap`, in particular beyond the
  cut), so that `designComb`'s explicit widths `ε'_k = η_k ℓ_k`, its reference tail `ℓ_k/4`, and `widthE c' η̃ k` agree.

Normalisation: both are the unnormalised Blaschke products (`B_D(i/2) = -1`), no `sech²` or `Lev` factor enters.
`‖combBD‖ e^{c'L}` is `combAmp`; the profile is `h₀ = sech²(πx/2) B_D` (`designProfile_ofReal`), so the `sech²`
factor is applied by the consumer.

* `rampedD0 = min(1, (a_1 - a_2)/8)`: the shift range of `rem:thmU` (`airyGap 1 = a_1 - a_2`);
* `rampedComb_eq_combBD`: `rampedComb P d c' b = combBD c' (rampedNode d c') (rampedEta P c') b` for `|Im b| < 7/8`
  once `N_Ai ≤ n_cap` (`eventually_nAi_le_nCap`, eventually in `c'` for fixed `C_I, C_mid`);
* `rampedDesignHyp`: `CombDesignHyp C_sh c_sep (rampedNode d c') (rampedEta P c')` with absolute `C_sh, c_sep` for
  `0 ≤ d ≤ d_0` (Lemma Z gives `|σ̃_k - Φ_k| ≤ C_sh k^{-4/3}`; the Airy gaps (`airyGap_bounds_exists`) and the WKB gaps
  give the separation; the first gap `a_1 - a_2 - d ≥ (7/8)(a_1 - a_2)` is why `d ≤ d_0`);
* `rampedComb_mult`, `rampedComb_amplitude`: `combToAiry_mult` and `combToAiry_amplitude` for `rampedComb P d c'` on
  `[ξ_*/2, ξ_* + 1/2]`, with the error constant `C` absolute (independent of `C_I, C_mid, M_0, d`); only the threshold
  in `c'` depends on `(C_I, C_mid)` (through `N_Ai ≤ n_cap`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.Special

/-- The shift range of `rem:thmU`: `d_0 = min(1, (a_1 - a_2)/8)`. -/
noncomputable def rampedD0 : ℝ := min 1 (airyGap 1 / 8)

lemma rampedD0_pos : 0 < rampedD0 :=
  lt_min one_pos (by have := airyGap_pos (le_refl 1); positivity)

lemma rampedD0_le_one : rampedD0 ≤ 1 := min_le_left _ _

lemma rampedD0_le_gap : rampedD0 ≤ airyGap 1 / 8 := min_le_right _ _

/-! ### 1. The ramped comb is `combBD` of the extended sequences -/

lemma rampedNode_eq_phi {c' d : ℝ} {k : ℕ} (hk : nAi c' < k) (hk1 : 2 ≤ k) :
    rampedNode d c' k = phiWKB k := by
  have h1 : k ≠ 1 := by omega
  have h2 : ¬ k ≤ nAi c' := not_le.2 hk
  simp [rampedNode, h1, h2]

lemma rampedNode_eq_sNode {c' d : ℝ} {k : ℕ} (hk : k ≤ nAi c') (hk1 : 2 ≤ k) :
    rampedNode d c' k = sNodeAiry k := by
  have h1 : k ≠ 1 := by omega
  simp [rampedNode, h1, hk]

lemma rampedNode_one_eq_sNode (c' d : ℝ) : rampedNode d c' 1 = sNodeAiry 1 + d / kappaAiry := by
  simp [rampedNode]

lemma eventually_nAi_le_nCap (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, nAi c' ≤ nCap P c' := by
  have hs : 0 < (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) := by
    have := P.one_le_Cmid
    positivity
  filter_upwards [nCap_ge P, eventually_ge_atTop (1 : ℝ),
    eventually_rpow_neg_le (p := 5 / 6) (by norm_num) (show 0 < (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) / 2 by
      positivity)] with c' hcap hc'1 hsm
  have hc'0 : 0 < c' := by linarith
  have h1 := nAi_le hc'1
  have h2 : c' ^ (1 / 6 : ℝ) = c' * c' ^ (-(5 / 6 : ℝ)) := by
    conv_lhs => rw [show (1 / 6 : ℝ) = 1 + (-(5 / 6 : ℝ)) by norm_num]
    rw [Real.rpow_add hc'0, Real.rpow_one]
  have h3 : 2 * c' ^ (1 / 6 : ℝ) ≤ (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' := by
    rw [h2]
    nlinarith
  have : (nAi c' : ℝ) ≤ (nCap P c' : ℝ) := h1.trans (h3.trans hcap)
  exact_mod_cast this

/-- **The ramped comb is `combBD` of the extended sequences** (`σ̃ = rampedNode`, `η̃ = rampedEta`): once the Airy
cut lies below the height cap, the explicit pairs, the reference tail and `combBD`'s product agree for `|Im b| < 7/8`.
-/
theorem rampedComb_eq_combBD (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → ∀ b : ℂ, |b.im| < 7 / 8 →
      rampedComb P d c' b = combBD c' (rampedNode d c') (rampedEta P c') b := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev, eventually_nAi_le_nCap P] with c' hc' hgap hAi d hd b hb
  obtain ⟨hgap_k, _, _, hgap_1⟩ := hgap
  set N := nCap P c' + 6 with hN
  have ha : ∀ k : ℕ, 1 ≤ k → (1 / 4 : ℝ) ≤ (k : ℝ) := fun k hk => by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hgap_nn : ∀ k : ℕ, 1 ≤ k → 0 ≤ siteGap c' k := fun k hk => by
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha k hk)
      ((ha k hk).trans (by linarith)) (by linarith))
  have hε_bd : ∀ m : ℕ, |1 / 4 * siteGap c' (N + 1 + m)| ≤ 1 / 8 := fun m => by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (hgap_nn _ (by omega)))]
    have hgk := (hgap_k (N + 1 + m) (by omega)).trans hgap_1
    linarith
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (N + 1 + m : ℕ) := fun m =>
    xiStar_pos.le.trans (chiQuantile_spec hc' (ha _ (by omega))).1
  have htail := (comb_pairProd_hasProdLocallyUniformlyOn
    (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)) (fun m : ℕ => 1 / 4 * siteGap c' (N + 1 + m))
    hχ_nn hε_bd (summable_exp_neg_pi_chiQuantile hc' N)).hasProd hb
  set g : ℕ → ℂ := fun m => pairT (siteX c' (rampedNode d c') (m + 2))
    (widthE c' (rampedEta P c') (m + 2)) b with hg
  have hshift : (fun n : ℕ => g (n + (N - 1))) =
      fun n : ℕ => pairT (chiQuantile c' (N + 1 + n : ℕ)) (1 / 4 * siteGap c' (N + 1 + n)) b := by
    funext n
    simp only [hg]
    have hidx : n + (N - 1) + 2 = N + 1 + n := by omega
    have hk1 : nAi c' < N + 1 + n := by omega
    rw [hidx]
    have hs : siteX c' (rampedNode d c') (N + 1 + n) = chiQuantile c' (N + 1 + n : ℕ) := by
      unfold siteX
      rw [rampedNode_eq_phi hk1 (by omega), chiQuantile_nat_eq hc' (by omega)]
    have hw : widthE c' (rampedEta P c') (N + 1 + n) = 1 / 4 * siteGap c' (N + 1 + n) := by
      unfold widthE
      rw [rampedEta_eq_quarter P hc' (by omega : nCap P c' ≤ N + 1 + n)]
    rw [hs, hw]
  have hmul : Multipliable (fun n : ℕ => g (n + (N - 1))) := by
    rw [hshift]; exact htail.multipliable
  have hsplit := hmul.prod_mul_tprod_nat_mul'
  unfold rampedComb designComb combBD combTail
  have hfin : (∏ i ∈ Finset.range (N - 1), pairT (designSite c' (rampedSigma d c') (1 + 1 + i))
      (rampedEps P c' (1 + 1 + i)) b) = ∏ i ∈ Finset.range (N - 1), g i := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have hidx : 1 + 1 + i = i + 2 := by omega
    simp only [hg]
    rw [hidx, designSite_rampedSigma hc']
    rfl
  rw [hfin, mul_assoc, ← hshift, hsplit]
  rw [designSite_rampedSigma hc']
  rfl

/-! ### 2. `CombDesignHyp` for the ramped nodes -/

lemma phiWKB_succ_sub_ge {k : ℕ} (hk : 1 ≤ k) :
    (2 / 3 : ℝ) * ((k : ℝ) + 3 / 4) ^ (-(1 / 3 : ℝ)) ≤ phiWKB (k + 1) - phiWKB k := by
  have hκ := kappaAiry_pos
  have h := (gapWKB_bounds hk).1
  have e : gapWKB k = kappaAiry * (phiWKB (k + 1) - phiWKB k) := by
    unfold gapWKB uWKB; ring
  rw [e] at h
  have : kappaAiry * ((2 / 3 : ℝ) * ((k : ℝ) + 3 / 4) ^ (-(1 / 3 : ℝ))) ≤
      kappaAiry * (phiWKB (k + 1) - phiWKB k) := by linarith
  exact le_of_mul_le_mul_left this hκ

lemma sNode_succ_sub {k : ℕ} : sNodeAiry (k + 1) - sNodeAiry k = airyGap k / kappaAiry := by
  have hκ := kappaAiry_pos
  unfold sNodeAiry airyGap
  rw [abs_of_neg (airyZero_neg (k + 1)), abs_of_neg (airyZero_neg k)]
  field_simp
  ring

/-- **`CombDesignHyp` for the ramped design** (`σ̃ = rampedNode`, `η̃ = rampedEta`): absolute `C_sh`, `c_sep` for every
`C_I, C_mid ≥ 1` and `0 ≤ d ≤ d_0`, for `c'` large (the threshold is absolute). -/
theorem rampedDesignHyp : ∃ Csh csep : ℝ, 0 < Csh ∧ 0 < csep ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ),
    0 ≤ d → d ≤ rampedD0 → CombDesignHyp Csh csep (rampedNode d c') (rampedEta P c') := by
  obtain ⟨Cn, hCn, hnode⟩ := rampedNode_sub_phi_le
  obtain ⟨c₁, c₂, hc₁, hc₂, hag⟩ := airyGap_bounds_exists
  have hκ := kappaAiry_pos
  have hg1 := airyGap_pos (le_refl 1)
  set K1 : ℕ := ⌈12 * Cn⌉₊ + 1 with hK1
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  refine ⟨Cn, min (min (7 / 8 * airyGap 1 / kappaAiry) (c₁ / kappaAiry)) (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))),
    hCn, lt_min (lt_min (by positivity) (by positivity)) (by positivity), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (((K1 + 1 : ℕ) : ℝ) ^ (6 : ℕ)))] with c' hc' P d hd hdD
  have hc'1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hc'0 : 0 < c' := by linarith
  have hnAi : K1 + 1 ≤ nAi c' := by
    have h6 : (((K1 + 1 : ℕ) : ℝ)) ≤ c' ^ (1 / 6 : ℝ) := by
      have hh : (((K1 + 1 : ℕ) : ℝ) ^ (6 : ℕ)) ≤ c' := (le_max_right _ _).trans hc'
      have := Real.rpow_le_rpow (by positivity) hh (show (0 : ℝ) ≤ 1 / 6 by norm_num)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num,
        Real.rpow_one] at this
    have : ((K1 + 1 : ℕ) : ℝ) ≤ nAi c' := h6.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hd1 : d ≤ 1 := hdD.trans rampedD0_le_one
  refine ⟨fun k hk => rampedNode_nonneg hd c' hk, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simpa [phiWKB, phiQuantile] using hnode c' d hd hd1 k hk
  · -- separation
    have hkp : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    by_cases hkK : K1 ≤ k
    · -- asymptotic range
      have hnk := hnode c' d hd hd1 k hk
      have hnk1 := hnode c' d hd hd1 (k + 1) (by omega)
      have hΦ := phiWKB_succ_sub_ge hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hkk1 : ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by norm_num)
      have hk34 : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ ((k : ℝ) + 3 / 4) ^ (-(1 / 3 : ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (by linarith) _ (by norm_num)
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hmul : (2 * (k : ℝ)) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.mul_rpow (by norm_num) hk0.le
      have e43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (k : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hk0]; norm_num
      have hkK' : 12 * Cn ≤ (k : ℝ) := by
        have : (⌈12 * Cn⌉₊ : ℝ) ≤ k := by exact_mod_cast (by omega : ⌈12 * Cn⌉₊ ≤ k)
        linarith [Nat.le_ceil (12 * Cn)]
      have hCk : 2 * Cn * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (1 / 3) * (2 : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [e43]
        have hinv : (k : ℝ)⁻¹ ≤ 1 / (12 * Cn) := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by positivity) hkK'
        have h2lt : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≥ 1 / 2 := by
          have : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≥ (2 : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rwa [Real.rpow_neg_one, ← one_div] at this
        have : 2 * Cn * (k : ℝ)⁻¹ ≤ 1 / 6 := by
          calc 2 * Cn * (k : ℝ)⁻¹ ≤ 2 * Cn * (1 / (12 * Cn)) := by gcongr
            _ = 1 / 6 := by field_simp; ring
        calc 2 * Cn * ((k : ℝ) ^ (-(1 / 3 : ℝ)) * (k : ℝ)⁻¹)
            = (k : ℝ) ^ (-(1 / 3 : ℝ)) * (2 * Cn * (k : ℝ)⁻¹) := by ring
          _ ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) * (1 / 6) := by gcongr
          _ ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) * ((1 / 3) * (2 : ℝ) ^ (-(1 / 3 : ℝ))) := by gcongr; linarith
          _ = _ := by ring
      have hsub : rampedNode d c' (k + 1) - rampedNode d c' k ≥
          (phiWKB (k + 1) - phiWKB k) - 2 * Cn * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        have a1 := (abs_le.mp hnk).1
        have a2 := (abs_le.mp hnk1).2
        have a3 := (abs_le.mp hnk).2
        have a4 := (abs_le.mp hnk1).1
        have hc4 : Cn * ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Cn * (k : ℝ) ^ (-(4 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hkk1 hCn.le
        linarith
      have hcs : min (min (7 / 8 * airyGap 1 / kappaAiry) (c₁ / kappaAiry))
          (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))) ≤ 1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ)) := min_le_right _ _
      have : (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))) * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          (phiWKB (k + 1) - phiWKB k) - 2 * Cn * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        nlinarith [hΦ, hk34, hmul, hCk, hkp]
      calc _ ≤ (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right hcs hkp.le
        _ ≤ _ := this.trans hsub
    · -- Airy range: `k + 1 ≤ N_Ai`
      have hkK' : k + 1 ≤ nAi c' := by omega
      have hk2 : 2 ≤ k + 1 := by omega
      rcases Nat.eq_or_lt_of_le hk with rfl | hk2'
      · rw [rampedNode_eq_sNode hkK' hk2, rampedNode_one_eq_sNode, show (1 : ℕ) + 1 = 2 from rfl]
        have e := sNode_succ_sub (k := 1)
        have hdg : d / kappaAiry ≤ airyGap 1 / 8 / kappaAiry :=
          div_le_div_of_nonneg_right (hdD.trans rampedD0_le_gap) hκ.le
        have hcs : min (min (7 / 8 * airyGap 1 / kappaAiry) (c₁ / kappaAiry))
            (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))) ≤ 7 / 8 * airyGap 1 / kappaAiry :=
          (min_le_left _ _).trans (min_le_left _ _)
        simp only [Nat.cast_one, Real.one_rpow, mul_one]
        have : 7 / 8 * airyGap 1 / kappaAiry = airyGap 1 / kappaAiry - airyGap 1 / 8 / kappaAiry := by
          field_simp; ring
        linarith
      · rw [rampedNode_eq_sNode hkK' hk2, rampedNode_eq_sNode (by omega) (by omega), sNode_succ_sub]
        have hcs : min (min (7 / 8 * airyGap 1 / kappaAiry) (c₁ / kappaAiry))
            (1 / 3 * (2 : ℝ) ^ (-(1 / 3 : ℝ))) ≤ c₁ / kappaAiry :=
          (min_le_left _ _).trans (min_le_right _ _)
        have := (hag k hk).1
        calc _ ≤ c₁ / kappaAiry * (k : ℝ) ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hcs hkp.le
          _ = c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ)) / kappaAiry := by ring
          _ ≤ _ := div_le_div_of_nonneg_right this hκ.le
  · exact ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩

/-! ### 3. Proposition 1.2(2) for the ramped comb -/

/-- **Multiplicative comb-to-Airy identity for `D_*`** (`combToAiry_mult` for `rampedComb`): on `[ξ_*/2, ξ_* + 1/2]`,
`‖B_{D_*}(x)‖ e^{c'L(x)}` is within `exp(± C λ)` of the Airy amplitude
`λ^{-3/2} e^{-(3/2)𝒦_*(x)} C_* κ ‖W_D(-κτ(x)/λ)‖`, `W_D = designAiryW (rampedNode d c') (rampedEta P c')`;
`C` absolute, `c'` large (threshold depending on `C_I, C_mid`), `0 ≤ d ≤ d_0`. -/
theorem rampedComb_mult : ∃ C : ℝ, 0 < C ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d →
    d ≤ rampedD0 → ∀ x ∈ langerX (1 / 2),
      Real.exp (-(C * lambdaComb c')) * airyAmp c' (rampedNode d c') (rampedEta P c') x ≤
          ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * slitL x) ∧
        ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
          Real.exp (C * lambdaComb c') * airyAmp c' (rampedNode d c') (rampedEta P c') x := by
  obtain ⟨Csh, csep, hCsh, hcsep, hH⟩ := rampedDesignHyp
  obtain ⟨C, c0, hC, hc0, hmult⟩ := combToAiry_mult Csh csep hcsep
  refine ⟨C, hC, fun P => ?_⟩
  filter_upwards [hH, rampedComb_eq_combBD P, eventually_ge_atTop c0] with c' hHc hEq hc' d hd hdD x hx
  have hb : |((x : ℝ) : ℂ).im| < 7 / 8 := by simp
  rw [hEq d hd (x : ℂ) hb]
  exact hmult hc' (hHc P d hd hdD) x hx

/-- **Amplitude form for `D_*`** (`combToAiry_amplitude` for `rampedComb`): with `K_s(x) = 𝒦_*(x) + log(2√2/π)`,
`‖B_{D_*}(x)‖ e^{c'L(x)} = (2√2/(πλ))^{3/2} e^{-(3/2)K_s(x)} C_* κ ‖W_D(-κτ(x)/λ)‖ exp(O(c'^{-2/3}))`
uniformly on `[ξ_*/2, ξ_* + 1/2]` (including the real zeros), `W_D = designAiryW (rampedNode d c') (rampedEta P c')`;
`C` absolute, `c'` large (threshold depending on `C_I, C_mid`), `0 ≤ d ≤ d_0`. -/
theorem rampedComb_amplitude : ∃ C : ℝ, 0 < C ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d →
    d ≤ rampedD0 → ∀ x ∈ langerX (1 / 2),
      Real.exp (-(C * c' ^ (-(2 / 3 : ℝ)))) *
          ((2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
            Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) *
            (CStar * kappaAiry *
              ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖)) ≤
        ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * slitL x) ∧
      ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
        Real.exp (C * c' ^ (-(2 / 3 : ℝ))) *
          ((2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
            Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) *
            (CStar * kappaAiry *
              ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖)) := by
  obtain ⟨Csh, csep, hCsh, hcsep, hH⟩ := rampedDesignHyp
  obtain ⟨C, c0, hC, hc0, hamp⟩ := combToAiry_amplitude Csh csep hcsep
  refine ⟨C, hC, fun P => ?_⟩
  filter_upwards [hH, rampedComb_eq_combBD P, eventually_ge_atTop c0] with c' hHc hEq hc' d hd hdD x hx
  have hb : |((x : ℝ) : ℂ).im| < 7 / 8 := by simp
  rw [hEq d hd (x : ℂ) hb]
  exact hamp hc' (hHc P d hd hdD) x hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedComb_eq_combBD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedComb_eq_combBD

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedDesignHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedDesignHyp

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedComb_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedComb_mult

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedComb_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedComb_amplitude

end FormalResearch.ModularBootstrap.Upper.Ramped

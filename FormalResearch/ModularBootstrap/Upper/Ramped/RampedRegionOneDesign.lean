module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneWindow
public import FormalResearch.ModularBootstrap.Upper.Ramped.CombBridge
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignPhase
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionII

/-!
# The ramped Airy profile `W_D` of Region I (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2).  The Airy product of the ramped
design `W_D = designAiryW (rampedNode d c') (rampedEta P c')` is the product `airyWindowProd 1 (a_1 - d) u_k ε_k` with

* `u_k = a_k` for `2 ≤ k ≤ N_Ai` (`ramped_site_near`), `u_k = u_k^W` beyond (`ramped_site_far`), `u_f = a_1 - d`
  (`ramped_site_first`), `ε_k = κ η_k (Φ_{k+1} - Φ_k)`;
* `ramped_window_lower`: the real-line lower bound `window_lower` for `W_D`, absolute constant `c_W`, for every
  `P`, `0 ≤ d ≤ d_0`, `c'` large, in terms of the height profile;
* `rho_lower`: `k^{1/3} ε_k²/(k + 1)^{2/3} ≥ c_ρ η_k²/k`;
* `etaSq_div_lower`: `η_k²/k ≥ min(1/(48 N_tr), C_I²/(3√c'))` for `k ≤ 3 N_tr`, the origin of the defining
  condition `η_n² ≥ C_I² n/√c'` on `n ≤ N_tr`;
* `twoG_pos_of_lt`: `2g > 0` as soon as `‖ĥ_0‖ < h_0` at a real point right of the first zero.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma ramped_site_near {c' d : ℝ} {k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ nAi c') :
    -kappaAiry * rampedNode d c' k = airyZero k := by
  rw [rampedNode_eq_sNode hk hk2]
  unfold sNodeAiry
  have hκ := kappaAiry_pos
  rw [abs_of_neg (airyZero_neg k)]
  field_simp

lemma ramped_site_far {c' d : ℝ} {k : ℕ} (hk2 : 2 ≤ k) (hk : nAi c' < k) :
    -kappaAiry * rampedNode d c' k = uWKB k := by
  rw [rampedNode_eq_phi hk hk2]
  rfl

lemma ramped_site_first (c' d : ℝ) : -kappaAiry * rampedNode d c' 1 = airyZero 1 - d := by
  rw [rampedNode_one_eq_sNode]
  unfold sNodeAiry
  rw [abs_of_neg (airyZero_neg 1)]
  have hκ := kappaAiry_pos
  field_simp
  ring

lemma one_le_nAi {c' : ℝ} (hc' : 1 ≤ c') : 1 ≤ nAi c' := by
  unfold nAi
  have : (1 : ℝ) ≤ c' ^ (1 / 6 : ℝ) := Real.one_le_rpow hc' (by norm_num)
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h
    have := Nat.ceil_eq_zero.mp h
    linarith)

lemma nAi_ge {c' : ℝ} : c' ^ (1 / 6 : ℝ) ≤ nAi c' := Nat.le_ceil _

/-- **`W_D` is bounded below on the real line** (`rem:thmU` Step (2)). -/
theorem ramped_window_lower :
    ∃ cW : ℝ, 0 < cW ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ rampedD0 →
      ∀ K : ℕ, 1 ≤ K → 2 * K ≤ nAi c' → ∀ u : ℝ, airyZero K ≤ u → u < airyZero 1 - d →
        ((airyZero 1 + airyZero 2) / 2 ≤ u →
          cW * (airyZero 1 - d - u) ≤ ‖designAiryW (rampedNode d c') (rampedEta P c') u‖) ∧
        (u ≤ (airyZero 1 + airyZero 2) / 2 → ∀ m : ℝ, 0 ≤ m →
          (∀ k : ℕ, 2 ≤ k → k ≤ K + 1 →
            m ≤ (k : ℝ) ^ (1 / 3 : ℝ) * (kappaAiry * epsHat (rampedEta P c') k) ^ 2 /
              ((k : ℝ) + 1) ^ (2 / 3 : ℝ)) →
          cW * m ≤ ‖designAiryW (rampedNode d c') (rampedEta P c') u‖) := by
  obtain ⟨Csh, csep, hCsh, hcsep, hH⟩ := rampedDesignHyp
  obtain ⟨C_Z, hCZ, hZ⟩ := deltaWKB_le_exists
  obtain ⟨cW, hcW, hwin⟩ := window_lower hCZ
  refine ⟨cW, hcW, ?_⟩
  have hbig : ∀ᶠ c' : ℝ in atTop, 8 * C_Z ≤ (c' ^ (1 / 6 : ℝ)) ^ 2 := by
    have h1 : Tendsto (fun c' : ℝ => c' ^ (1 / 6 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [(h1.eventually_ge_atTop (Real.sqrt (8 * C_Z)))] with c' hc'
    have h0 : 0 ≤ Real.sqrt (8 * C_Z) := Real.sqrt_nonneg _
    calc 8 * C_Z = (Real.sqrt (8 * C_Z)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
      _ ≤ _ := pow_le_pow_left₀ h0 hc' 2
  filter_upwards [hH, hbig, eventually_ge_atTop (1 : ℝ)] with c' hHc hbigc hc'1
  intro P d hd hdD K hK hK2 u hKu huu
  have hCD := hHc P d hd hdD
  have hCt : 0 < max |Csh| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hHyp := airyProdTailHypothesis_of_tail (f := 1) (N := 1) le_rfl hCt (design_tail hCD)
  have hnA1 := one_le_nAi hc'1
  have hM8 : 8 * C_Z ≤ ((nAi c' : ℕ) : ℝ) ^ 2 :=
    hbigc.trans (pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) nAi_ge 2)
  have hsite : ∀ j : ℕ, 2 ≤ j → j ≤ nAi c' → (fun k => -kappaAiry * rampedNode d c' k) j = airyZero j :=
    fun j hj hjM => ramped_site_near hj hjM
  have hdel : ∀ j : ℕ, nAi c' < j →
      |airyZero j - (fun k => -kappaAiry * rampedNode d c' k) j| ≤ C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro j hj
    have hj2 : 2 ≤ j := by omega
    show |airyZero j - -kappaAiry * rampedNode d c' j| ≤ _
    rw [ramped_site_far hj2 hj]
    exact hZ j (by omega)
  have hF : designAiryW (rampedNode d c') (rampedEta P c') u = airyWindowProd 1 (airyZero 1 - d)
      (fun k => -kappaAiry * rampedNode d c' k) (fun k => kappaAiry * epsHat (rampedEta P c') k) (u : ℂ) := by
    unfold designAiryW
    rw [ramped_site_first]
  have hres := hwin (fun k => -kappaAiry * rampedNode d c' k)
    (fun k => kappaAiry * epsHat (rampedEta P c') k) (airyZero 1 - d) hHyp (nAi c') K hK hK2 hM8 hsite hdel
    (by linarith) (by have := hdD.trans rampedD0_le_gap; linarith) u hKu huu
  rw [hF]
  exact hres

/-- `k^{1/3}/((k+1)^{2/3})² ≥ 1/(3k)`-type comparison used in `rho_lower`: with `a = k^{1/3}`, `b = (k+1)^{1/3}`,
`b⁴ ≤ 3 a⁴`. -/
lemma b_four_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ^ 3 ≤ 2 * a ^ 3) : b ^ 4 ≤ 3 * a ^ 4 := by
  by_contra hcon
  push Not at hcon
  have h1 : (3 * a ^ 4) ^ 3 < (b ^ 4) ^ 3 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have h2 : (b ^ 4) ^ 3 = (b ^ 3) ^ 4 := by ring
  have h3 : (b ^ 3) ^ 4 ≤ (2 * a ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
  have h4 : 0 < a ^ 12 := by positivity
  nlinarith

/-- **`k^{1/3} ε_k²/(k+1)^{2/3} ≥ c_ρ η_k²/k`** for `ε_k = κ η_k (Φ_{k+1} - Φ_k)`. -/
theorem rho_lower : ∃ cρ : ℝ, 0 < cρ ∧ ∀ (η : ℝ) (k : ℕ), 1 ≤ k →
    cρ * η ^ 2 / k ≤ (k : ℝ) ^ (1 / 3 : ℝ) *
      (kappaAiry * (η * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))) ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := by
  have hκ := kappaAiry_pos
  refine ⟨4 * kappaAiry ^ 2 / 27, by positivity, fun η k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  set a : ℝ := (k : ℝ) ^ (1 / 3 : ℝ) with ha
  set b : ℝ := ((k : ℝ) + 1) ^ (1 / 3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hk0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hk1 _
  have ha3 : a ^ 3 = k := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hb3 : b ^ 3 = (k : ℝ) + 1 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hk1.le]; norm_num
  have hb2 : ((k : ℝ) + 1) ^ (2 / 3 : ℝ) = b ^ 2 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hk1.le]; norm_num
  have hbm : (k : ℝ) + 3 / 4 ≤ (k : ℝ) + 1 := by linarith
  -- gap lower bound
  have hg := phiWKB_succ_sub_ge hk
  have hphi : phiWKB (k + 1) - phiWKB k = phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ) := by
    unfold phiWKB phiQuantile; push_cast; ring_nf
  rw [hphi] at hg
  have hpow : ((k : ℝ) + 1) ^ (-(1 / 3 : ℝ)) ≤ ((k : ℝ) + 3 / 4) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hbm (by norm_num)
  have hbinv : ((k : ℝ) + 1) ^ (-(1 / 3 : ℝ)) = b⁻¹ := by
    rw [hb, Real.rpow_neg hk1.le]
  rw [hbinv] at hpow
  have hgg : 2 / 3 * b⁻¹ ≤ phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ) :=
    le_trans (by gcongr) hg
  have hgg0 : 0 ≤ 2 / 3 * b⁻¹ := by positivity
  have hsq : (2 / 3 * b⁻¹) ^ 2 ≤ (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hgg0 hgg 2
  rw [hb2]
  have hb4 := b_four_le ha0 hb0 (by rw [ha3, hb3]; have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                    linarith)
  set g := phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ) with hgdef
  have hexp : (kappaAiry * (η * g)) ^ 2 = kappaAiry ^ 2 * η ^ 2 * g ^ 2 := by ring
  rw [hexp]
  have hq : 0 < b ^ 2 := by positivity
  rw [div_le_div_iff₀ hk0 hq]
  -- `c η² b² ≤ a κ² η² g² k`
  have h1 : (4 / 9) * b⁻¹ ^ 2 ≤ g ^ 2 := by
    have : (2 / 3 * b⁻¹) ^ 2 = 4 / 9 * b⁻¹ ^ 2 := by ring
    linarith
  have hbb : b⁻¹ ^ 2 * b ^ 2 = 1 := by field_simp
  have hk_eq : (k : ℝ) = a ^ 3 := ha3.symm
  have hnn : 0 ≤ kappaAiry ^ 2 * η ^ 2 := by positivity
  have h2 : kappaAiry ^ 2 * η ^ 2 * (4 / 9 * b⁻¹ ^ 2) ≤ kappaAiry ^ 2 * η ^ 2 * g ^ 2 :=
    mul_le_mul_of_nonneg_left h1 hnn
  have h3 : 4 * kappaAiry ^ 2 / 27 * η ^ 2 * b ^ 2 ≤
      a * (kappaAiry ^ 2 * η ^ 2 * g ^ 2) * k := by
    have h4 : a * (kappaAiry ^ 2 * η ^ 2 * (4 / 9 * b⁻¹ ^ 2)) * k =
        4 / 9 * kappaAiry ^ 2 * η ^ 2 * (a ^ 4 * b⁻¹ ^ 2) := by rw [hk_eq]; ring
    have h5 : 4 * kappaAiry ^ 2 / 27 * η ^ 2 * b ^ 2 ≤ 4 / 9 * kappaAiry ^ 2 * η ^ 2 * (a ^ 4 * b⁻¹ ^ 2) := by
      have hb4' : b ^ 4 ≤ 3 * a ^ 4 := hb4
      have h6 : b ^ 2 ≤ 3 * (a ^ 4 * b⁻¹ ^ 2) := by
        have : b ^ 2 = b ^ 4 * b⁻¹ ^ 2 := by field_simp
        rw [this]
        have hi : 0 ≤ b⁻¹ ^ 2 := by positivity
        nlinarith
      have hk2 : 0 ≤ kappaAiry ^ 2 * η ^ 2 := hnn
      nlinarith
    have h7 : a * (kappaAiry ^ 2 * η ^ 2 * (4 / 9 * b⁻¹ ^ 2)) * k ≤ a * (kappaAiry ^ 2 * η ^ 2 * g ^ 2) * k := by
      gcongr
    linarith
  linarith

lemma etaSq_div_lower (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : (k : ℝ) ≤ 3 * nTr c') (hN : 0 < nTr c') :
    min (1 / (48 * nTr c')) (P.CI ^ 2 / (3 * √c')) ≤ etaSq P c' k / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  rw [le_div_iff₀ hk0]
  unfold etaSq
  refine le_min ?_ ?_
  · calc min (1 / (48 * nTr c')) (P.CI ^ 2 / (3 * √c')) * k ≤ 1 / (48 * nTr c') * k :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hk0.le
      _ ≤ 1 / (48 * nTr c') * (3 * nTr c') := mul_le_mul_of_nonneg_left hkN (by positivity)
      _ = 1 / 16 := by field_simp; norm_num
  · have hCI : 0 ≤ P.CI ^ 2 := by positivity
    have hmin : (k : ℝ) / 3 ≤ min (k : ℝ) (nTr c') := le_min (by linarith) (by linarith)
    calc min (1 / (48 * nTr c')) (P.CI ^ 2 / (3 * √c')) * k ≤ P.CI ^ 2 / (3 * √c') * k :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hk0.le
      _ = P.CI ^ 2 * ((k : ℝ) / 3) / √c' := by field_simp
      _ ≤ P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' := by gcongr
      _ ≤ etaArg P c' k := by
          unfold etaArg
          have : 0 ≤ P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) := by positivity
          linarith

/-- `2g > 0` as soon as `‖ĥ_0‖ < h_0` at a real point to the right of the first zero. -/
theorem twoG_pos_of_lt {c' x : ℝ} (hc' : 0 < c') (hgap : siteGap c' 1 ≤ 1 / 2) {N : ℕ} (hN : 1 ≤ N)
    (σ ε : ℕ → ℝ) (hfx : designSite c' σ 1 < x) (hf0 : 0 ≤ designSite c' σ 1)
    (h : ‖edgeHankel c' (designProfile c' 1 N (1 / 4) σ ε) (c' * x ^ 2 / 3)‖ <
      1 / Real.cosh (π * x / 2) ^ 2 * ‖designComb c' 1 N (1 / 4) σ ε (x : ℂ)‖) :
    0 < twoG c' 1 N (1 / 4) σ ε x := by
  obtain ⟨r, hr, hr0⟩ := designComb_real_nonneg hc' hgap 1 N σ ε hN hfx hf0
  have hnorm : ‖designComb c' 1 N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hh0 : (designProfile c' 1 N (1 / 4) σ ε (x : ℂ)).re = 1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  unfold twoG
  rw [Complex.sub_re, hh0]
  rw [hnorm] at h
  have hre := Complex.re_le_norm (edgeHankel c' (designProfile c' 1 N (1 / 4) σ ε) (c' * x ^ 2 / 3))
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_window_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ramped_window_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rho_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rho_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.twoG_pos_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoG_pos_of_lt

end FormalResearch.ModularBootstrap.Upper.Ramped

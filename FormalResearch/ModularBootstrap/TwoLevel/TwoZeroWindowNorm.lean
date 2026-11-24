module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumPrelim

/-!
# The normalisation `F_{2,c}` of the two-zero window (`upper_transfer.tex`, `ut:T2`, "Window and vacuum normalisation")

`F_{2,c} := FV_c (2√2/(πλ))^{5/2} = FK_c^{(2)} · πλ/(2√2)` (`eq:ut:T2-norm`) with `FK_c^{(2)}` the `f = 2` measure
normalisation of Lemma `W`.

* `windowMeasureNormK_eq_FKc`: at `w = 1` and every level `f`, `windowMeasureNormK prob f c' = FKc (qProb prob) f c'`
  (the `f`-general form of `Positivity.windowMeasureNormK_eq`);
* `twoZeroF`, `twoZeroF_eq_const_mul`, `twoZeroF_asymp`: `F_{2,c} = Φ₀ c'^{3/2}` exactly, `Φ₀ > 0`, so `F_{2,c} ≍ c'^{3/2}`;
* `CompactCombFamily.tildeW_bound`: `W̃^{±(f)}` is bounded on `[-S, S]` uniformly on a compact family.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- `FK_c` of Lemma `W` at `w = 1` (any null polynomial) and any level `f` is `FKc (qProb prob) f c'`. -/
theorem windowMeasureNormK_eq_FKc (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (f : ℕ) {c' : ℝ}
    (hc' : 0 < c') : windowMeasureNormK prob f c' = FKc (qProb prob) f c' := by
  have hxi := xiStar_pos
  have hlam := lambdaComb_pos' hc'
  unfold windowMeasureNormK windowNormKTilde
  unfold FKc FVc qProb
  simp only [hw, Nat.sub_self, pow_zero, one_mul]
  have h3 : √(xiStar / 3) = √xiStar / √3 := Real.sqrt_div hxi.le 3
  rw [h3]
  have e : Real.exp (-4 * π * xiStar) = Real.exp (-(4 * π * xiStar)) := by ring_nf
  rw [e]
  have h3' : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have := one_sub_exp_xiStar_pos
  generalize prob.nullPoly (Real.exp (-(4 * π * xiStar))) = Q
  generalize Real.exp (-(4 * π * xiStar)) = E at this ⊢
  field_simp

/-- `F_{2,c} = FK_c^{(2)} · πλ/(2√2)` (`eq:ut:T2-norm`). -/
noncomputable def twoZeroF (prob : Crossing.FixedWeightProblem) (c : ℝ) : ℝ :=
  FKc (qProb prob) 2 c * (π * lambdaComb c / (2 * √2))

/-- The constant `Φ₀` with `F_{2,c} = Φ₀ c'^{3/2}`. -/
noncomputable def twoZeroFConst (prob : Crossing.FixedWeightProblem) : ℝ :=
  qProb prob * (√xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 * (1 / cosh (π * xiStar / 2) ^ 2) /
    (√3 * π)) * (2 * √2 / π) ^ (5 / 2 : ℝ) * kTip

lemma twoZeroFConst_pos (prob : Crossing.FixedWeightProblem) : 0 < twoZeroFConst prob := by
  have := qProb_pos prob
  have := xiStar_pos
  have := one_sub_exp_xiStar_pos
  have := kTip_pos
  unfold twoZeroFConst
  positivity

/-- `λ^{3/2} = 1 / (k_tip c')`. -/
lemma lambdaComb_rpow_three_halves {c : ℝ} (hc : 0 < c) : lambdaComb c ^ (3 / 2 : ℝ) = (kTip * c)⁻¹ := by
  have hk : 0 < kTip * c := mul_pos kTip_pos hc
  unfold lambdaComb
  rw [← Real.rpow_mul hk.le, show (-(2 / 3 : ℝ)) * (3 / 2) = -1 by norm_num, Real.rpow_neg_one]

/-- **`F_{2,c} = Φ₀ c'^{3/2}`** for every `c' > 0`. -/
theorem twoZeroF_eq_const_mul (prob : Crossing.FixedWeightProblem) {c : ℝ} (hc : 0 < c) :
    twoZeroF prob c = twoZeroFConst prob * c ^ (3 / 2 : ℝ) := by
  have hl := lambdaComb_pos' hc
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h32 := lambdaComb_rpow_three_halves hc
  have hexp : (2 * (((2 : ℕ) : ℝ) - 1 / 4)) = 7 / 2 := by norm_num
  have hdiv : (2 * √2 / (π * lambdaComb c)) ^ (7 / 2 : ℝ) =
      (2 * √2 / π) ^ (7 / 2 : ℝ) / lambdaComb c ^ (7 / 2 : ℝ) := by
    rw [show 2 * √2 / (π * lambdaComb c) = (2 * √2 / π) / lambdaComb c by field_simp]
    exact Real.div_rpow (by positivity) hl.le _
  have h72 : lambdaComb c ^ (7 / 2 : ℝ) = lambdaComb c ^ (2 : ℕ) * lambdaComb c ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl]; norm_num
  have hs : (2 * √2 / π) ^ (7 / 2 : ℝ) = (2 * √2 / π) ^ (5 / 2 : ℝ) * (2 * √2 / π) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  have hc32 : c ^ (3 / 2 : ℝ) = c * √c := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold twoZeroF twoZeroFConst FKc FVc
  rw [hexp, hdiv, h72, hs, hc32, h32]
  have hkc : kTip * c ≠ 0 := (mul_pos kTip_pos hc).ne'
  have hk := kTip_pos
  field_simp

/-- **`F_{2,c} ≍ c'^{3/2}`** (`eq:ut:T2-norm`): the `F_asymp` field of `TwoZeroTransferData`. -/
theorem twoZeroF_asymp (prob : Crossing.FixedWeightProblem) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, 0 < c →
      A * c ^ ((3 : ℝ) / 2) ≤ twoZeroF prob c ∧ twoZeroF prob c ≤ B * c ^ ((3 : ℝ) / 2) :=
  ⟨twoZeroFConst prob, twoZeroFConst prob, twoZeroFConst_pos prob, twoZeroFConst_pos prob,
    fun c hc => by rw [twoZeroF_eq_const_mul prob hc]; exact ⟨le_rfl, le_rfl⟩⟩

lemma twoZeroF_pos (prob : Crossing.FixedWeightProblem) {c : ℝ} (hc : 0 < c) : 0 < twoZeroF prob c := by
  rw [twoZeroF_eq_const_mul prob hc]
  have := twoZeroFConst_pos prob
  positivity

/-- `F_{2,c} = FK^{(2)}_c · πλ/(2√2)` with the measure normalisation `windowMeasureNormK` of Lemma `W`. -/
lemma twoZeroF_eq_windowMeasureNormK (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) {c : ℝ}
    (hc : 0 < c) :
    twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) := by
  rw [windowMeasureNormK_eq_FKc prob hw 2 hc]; rfl

/-! ### A uniform bound on `W̃^{±(f)}` -/

private lemma tildeW_bound_aux {f N K_min : ℕ} (𝒦 : CompactCombFamily f N)
    {C_W S_win : ℝ} (hS_win : 0 ≤ S_win) (hKmin_N : N ≤ K_min) (hKmin_1 : 1 ≤ K_min)
    (hCW_pos : 0 < C_W)
    (hW_rate : ∀ {σf : ℝ} {σSeq εHat : ℕ → ℝ},
      |σf| ≤ max 𝒦.M 1 →
      (∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ max 𝒦.M 1 ∧ |εHat k| ≤ max 𝒦.M 1) →
      (∀ k : ℕ, N < k →
        |σSeq k - phiWKB k| ≤ 1 * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ 1 * (k : ℝ) ^ (-(1 / 3 : ℝ))) →
      (∀ {K₁ K₂ : ℕ} {σ : ℝ}, K_min ≤ K₁ → K₁ ≤ K₂ → σ ∈ Icc (-S_win) S_win →
        |windowFiniteProd f σf σSeq εHat K₂ σ - windowFiniteProd f σf σSeq εHat K₁ σ| ≤ C_W / (K₁ : ℝ)) ∧
      (∀ {K : ℕ} {σ : ℝ}, K_min ≤ K → σ ∈ Icc (-S_win) S_win →
        |windowFiniteProd f σf σSeq εHat K σ - tildeW f σf σSeq εHat σ| ≤ C_W / (K : ℝ))) :
    ∃ B_W > 0, ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S_win) S_win,
      |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ B_W := by
  let M_lim : ℝ := max 𝒦.M 1
  have hfN : f ≤ N := 𝒦.hN
  have hcont_fq := continuous_continuumFQ (continuumAK K_min) (continuumAK_nonneg K_min)
  obtain ⟨B_fq, _, hB_fq⟩ : ∃ B_fq : ℝ, 0 ≤ B_fq ∧ ∀ σ ∈ Icc (-S_win) S_win,
      |continuumFQ (continuumAK K_min) σ| ≤ B_fq := by
    obtain ⟨σ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by simp [hS_win]⟩ : (Icc (-S_win) S_win).Nonempty)
      (continuous_abs.comp hcont_fq).continuousOn
    exact ⟨max 0 |continuumFQ (continuumAK K_min) σ₀|, le_max_left _ _,
      fun σ hσ => (hmax hσ).trans (le_max_right _ _)⟩
  let B_K : ℝ := Real.exp B_fq * (S_win + M_lim) * (((S_win + M_lim) ^ 2 + M_lim ^ 2) ^ (N - f)) *
    (∏ k ∈ Finset.Icc (N + 1) K_min, ((S_win + phiWKB k + 1) ^ 2 + 1))
  refine ⟨B_K + C_W + 1, by positivity, fun d hd σ hσ => ?_⟩
  have hd_lim := 𝒦.lim_bounds d hd
  have hrate_d := (hW_rate (σf := d.sigmaFLim) (σSeq := d.allSigmaLim) (εHat := d.allEpsLim)
    ((hd_lim.1).trans (le_max_left _ _))
    (fun k hk => by
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk' := hd_lim.2 k hk
      exact ⟨hk'.1.trans (le_max_left _ _), by rw [abs_of_nonneg hk'.2.1]; exact hk'.2.2.trans (le_max_left _ _)⟩)
    (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)).2
    le_rfl hσ
  have hMK_bd : |windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ| ≤ B_K := by
    unfold windowFiniteProd
    have hexp_le : continuumFQ (continuumAK K_min) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) ≤ B_fq := by
      have h1 := (le_abs_self _).trans (hB_fq σ hσ)
      have : 0 ≤ 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) := by positivity
      linarith
    have hσ_abs : |σ| ≤ S_win := abs_le.mpr hσ
    have hlin : |σ - d.sigmaFLim| ≤ S_win + M_lim :=
      (abs_sub _ _).trans (add_le_add hσ_abs ((hd_lim.1).trans (le_max_left _ _)))
    have hIcc : Finset.Icc (f + 1) K_min = Finset.Icc (f + 1) N ∪ Finset.Icc (N + 1) K_min := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc (f + 1) N) (Finset.Icc (N + 1) K_min) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
    have hp1 : |∏ k ∈ Finset.Icc (f + 1) N, ((σ - d.allSigmaLim k) ^ 2 + (d.allEpsLim k) ^ 2)| ≤
        ((S_win + M_lim) ^ 2 + M_lim ^ 2) ^ (N - f) := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      calc ∏ k ∈ Finset.Icc (f + 1) N, _
          ≤ ∏ _k ∈ Finset.Icc (f + 1) N, ((S_win + M_lim) ^ 2 + M_lim ^ 2) := by
            refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
            have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
            simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
            have hk' := hd_lim.2 k hk
            have h1 : |σ - d.sigmaKLim k| ≤ S_win + M_lim :=
              (abs_sub _ _).trans (add_le_add hσ_abs (hk'.1.trans (le_max_left _ _)))
            have h2 : (σ - d.sigmaKLim k) ^ 2 ≤ (S_win + M_lim) ^ 2 := by
              simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
            have h3 : d.epsHatLim k ^ 2 ≤ M_lim ^ 2 :=
              pow_le_pow_left₀ hk'.2.1 (hk'.2.2.trans (le_max_left _ _)) 2
            linarith
        _ = _ := by
            rw [Finset.prod_const, Nat.card_Icc, show N + 1 - (f + 1) = N - f by omega]
    have hp2 : |∏ k ∈ Finset.Icc (N + 1) K_min, ((σ - d.allSigmaLim k) ^ 2 + (d.allEpsLim k) ^ 2)| ≤
        ∏ k ∈ Finset.Icc (N + 1) K_min, ((S_win + phiWKB k + 1) ^ 2 + 1) := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
      have hkN : ¬ k ≤ N := by simp only [Finset.mem_Icc] at hk; omega
      have ht := d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2 k (by omega)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hkr13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
      have hkr43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
      have hs1 : |σ - d.allSigmaLim k| ≤ S_win + phiWKB k + 1 := by
        have hphi_nn : 0 ≤ phiWKB k := by
          unfold phiWKB
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1 / 4) _
        have : |d.allSigmaLim k| ≤ phiWKB k + 1 := by
          have := abs_sub_abs_le_abs_sub (d.allSigmaLim k) (phiWKB k)
          rw [abs_of_nonneg hphi_nn] at this; nlinarith [ht.1]
        exact (abs_sub _ _).trans (by linarith)
      have hs2 : (σ - d.allSigmaLim k) ^ 2 ≤ (S_win + phiWKB k + 1) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs1 2
      have he2 : (d.allEpsLim k) ^ 2 ≤ 1 := by
        have : |d.allEpsLim k| ≤ 1 := by nlinarith [ht.2]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
    rw [hIcc, Finset.prod_union hdisj, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
    have hm1 := mul_le_mul (Real.exp_le_exp.mpr hexp_le) hlin (abs_nonneg _) (Real.exp_pos _).le
    have hm2 := mul_le_mul hm1 hp1 (abs_nonneg _) (by positivity)
    exact (mul_le_mul hm2 hp2 (abs_nonneg _) (by positivity)).trans_eq rfl
  have hKmin_ge1 : (1 : ℝ) ≤ (K_min : ℝ) := by exact_mod_cast hKmin_1
  have hCW_le : C_W / (K_min : ℝ) ≤ C_W := div_le_self hCW_pos.le hKmin_ge1
  have h_abs_diff := abs_sub_abs_le_abs_sub (tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ)
    (windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ)
  have hcomm : |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ -
      windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ| =
      |windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ -
      tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| := abs_sub_comm _ _
  linarith [h_abs_diff, hrate_d, hMK_bd, hCW_le, hcomm]

/-- `W̃^{±(f)}` is bounded on `[-S, S]` uniformly over a compact family
(the bound used inside `lemma_W_measure`). -/
theorem CompactCombFamily.tildeW_bound {f N : ℕ} (𝒦 : CompactCombFamily f N) {S : ℝ} (hS : 0 ≤ S) :
    ∃ B > 0, ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S) S,
      |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ B := by
  obtain ⟨K_min, C_W, hKmin_N, hKmin_1, hCW_pos, hW_rate⟩ :=
    tendsto_windowFiniteProd_uniform f N 𝒦.hf 𝒦.hN (M := max 𝒦.M 1) (C_t := 1) (S := S)
      (by have := 𝒦.hM; positivity) zero_lt_one hS
  exact tildeW_bound_aux 𝒦 hS hKmin_N hKmin_1 hCW_pos hW_rate

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.windowMeasureNormK_eq_FKc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowMeasureNormK_eq_FKc

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.CompactCombFamily.tildeW_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompactCombFamily.tildeW_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroF_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroF_asymp

end FormalResearch.ModularBootstrap.TwoLevel

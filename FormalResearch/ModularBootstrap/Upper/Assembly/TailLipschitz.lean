module

public import FormalResearch.ModularBootstrap.Upper.Assembly.TailLower
public import FormalResearch.ModularBootstrap.Upper.Ramped.PUnif

/-!
# The design-independent Lipschitz bound for `G_k` near `a_1`

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:Sigma0`(b): `|W_A(u)| ≤ (d + ι) Ai'(a_1)² R_1
(1 + C d + C ι)`), `upper_transfer.tex` (`ut:G`, `ut:E`(iv)).

`G_k = W_{k,0}/(a_1 - u)` is the entire function `-dslope W_{k,0} a_1` (`W_{k,0}(a_1) = 0`).  The uniform
growth bound `lemma_G_bound_unif` (uniform in `N`, `η ∈ [0, 1/4]`) bounds `W_{k,0}` by a constant `M` on
`|z - a_1| ≤ 2`; the maximum modulus principle bounds `dslope` by `M/2` on that disc and the Schwarz lemma
gives `|G_k(u) - G_k(a_1)| ≤ (M/2)|u - a_1|` there.  Together with `G_k(a_1) = R_1 Ai'(a_1)² ≥ c > 0`
(`R_1 ≥ 1/2` for `N ≥ N_0` by `lemma_E`, `R_1 > 0` for the finitely many remaining `N`) this is
`Gd_upper`, the upper bound field of `SameSiteTailBounds (Gd N₀)`, for every `N₀`.

Everything is proved.
-/

@[expose] public section

open Real Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity

private lemma airyEnv_le_exp_norm (u : ℂ) :
    airyEnv u ≤ Real.exp ((4 / 3 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) := by
  unfold airyEnv
  apply Real.exp_le_exp.mpr
  have hnorm : ‖u ^ (3 / 2 : ℂ)‖ = ‖u‖ ^ (3 / 2 : ℝ) := by
    by_cases hu : u = 0
    · rw [hu, Complex.zero_cpow (by norm_num)]; simp
    · have hadd : u ^ (3 / 2 : ℂ) = u ^ (1 : ℂ) * u ^ (1 / 2 : ℂ) := by
        rw [← Complex.cpow_add _ _ hu]; congr 1; norm_num
      rw [hadd, Complex.cpow_one, norm_mul, norm_cpow_half u, Real.sqrt_eq_rpow]
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      rw [← Real.rpow_one_add' hpos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
      norm_num
  have hre : -(‖u‖ ^ (3 / 2 : ℝ)) ≤ (u ^ (3 / 2 : ℂ)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (u ^ (3 / 2 : ℂ)))).1
    linarith
  linarith

/-- A bound for `W_{N,η,0}` on `|z - a_1| ≤ 2`, uniform in `N` and `η ∈ [0, 1/4]`. -/
lemma exists_designWindowW_disc_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (η : ℝ), 0 ≤ η → η ≤ 1 / 4 → ∀ z : ℂ,
      ‖z - (airyZero 1 : ℂ)‖ ≤ 2 → ‖designWindowW N η 0 z‖ ≤ M := by
  obtain ⟨C, hC, hbd⟩ := FormalResearch.ModularBootstrap.Upper.Ramped.lemma_G_bound_unif
  set R : ℝ := |airyZero 1| + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨C * Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)), by positivity, fun N η h0 h1 z hz => ?_⟩
  have hzR : ‖z‖ ≤ R := by
    have := norm_le_norm_add_norm_sub' z (airyZero 1 : ℂ)
    have h2 : ‖((airyZero 1 : ℝ) : ℂ)‖ = |airyZero 1| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖z‖ ≤ ‖(airyZero 1 : ℂ)‖ + ‖z - (airyZero 1 : ℂ)‖ := by
      have := norm_le_insert' z (airyZero 1 : ℂ)
      linarith [norm_sub_rev z (airyZero 1 : ℂ)]
    rw [h2] at h3
    linarith
  have hb := hbd N η 0 h0 h1 le_rfl zero_le_one z
  have h1z : (1 + ‖z‖) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by norm_num)
  have hen : airyEnv z ≤ Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) :=
    (airyEnv_le_exp_norm z).trans (Real.exp_le_exp.mpr (by
      have := Real.rpow_le_rpow (norm_nonneg z) hzR (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith))
  calc ‖designWindowW N η 0 z‖ ≤ C * (1 + ‖z‖) ^ (-(3 / 2 : ℝ)) * airyEnv z := hb
    _ ≤ C * 1 * Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) := by
        have := airyEnv_pos z
        gcongr
    _ = _ := by ring

lemma designWindowW_at_a1_zero (N : ℕ) (η : ℝ) :
    designWindowW N η 0 (airyZero 1 : ℂ) = 0 := by
  apply Complex.ext
  · have := designWinW_at_a1 N η 0
    simpa [designWinW] using this
  · simpa using designWindowW_im_eq_zero N η 0 (airyZero 1)

/-- `G_k(u) = -Re (dslope W_{k,0} a_1 u)` for real `u`. -/
lemma Gd_eq_neg_re_dslope (N₀ k : ℕ) (u : ℝ) :
    Gd N₀ k u = -(dslope (designWindowW (N₀ + k) (1 / ((k : ℝ) + 4)) 0) (airyZero 1 : ℂ)
      (u : ℂ)).re := by
  set W := designWindowW (N₀ + k) (1 / ((k : ℝ) + 4)) 0 with hW
  have hWd : Differentiable ℂ W := designWindowW_differentiable _ _ _
  have hHd : DifferentiableOn ℂ (dslope W (airyZero 1 : ℂ)) Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr hWd.differentiableOn
  have hcont : Continuous (fun x : ℝ => -(dslope W (airyZero 1 : ℂ) (x : ℂ)).re) :=
    (Complex.continuous_re.comp (hHd.continuousOn.comp_continuous Complex.continuous_ofReal
      (fun _ => Set.mem_univ _))).neg
  have hW0 : W (airyZero 1 : ℂ) = 0 := designWindowW_at_a1_zero _ _
  have hext : Gd N₀ k = fun x : ℝ => -(dslope W (airyZero 1 : ℂ) (x : ℂ)).re := by
    refine Continuous.ext_on (dense_compl_singleton (airyZero 1)) (continuous_Gd N₀ k) hcont ?_
    intro x hx
    have hx' : x ≠ airyZero 1 := hx
    have hxc : (x : ℂ) ≠ (airyZero 1 : ℂ) := fun h => hx' (Complex.ofReal_injective h)
    simp only [dslope_of_ne _ hxc, slope_def_module, smul_eq_mul, hW0, sub_zero]
    rw [Gd_of_ne N₀ k hx']
    have hne : x - airyZero 1 ≠ 0 := sub_ne_zero.mpr hx'
    have hne' : airyZero 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
    have hinv : (((x : ℂ) - (airyZero 1 : ℂ))⁻¹) = (((x - airyZero 1)⁻¹ : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hinv, Complex.re_ofReal_mul]
    unfold designWinW
    field_simp
    ring
  exact congrFun hext u

/-- **Lipschitz bound**: `G_k(u) ≤ G_k(a_1) + L |u - a_1|` for `|u - a_1| ≤ 1`, `L` independent of `N₀`, `k`. -/
lemma exists_Gd_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N₀ k : ℕ) (u : ℝ), |u - airyZero 1| ≤ 1 →
      Gd N₀ k u ≤ Gd N₀ k (airyZero 1) + L * |u - airyZero 1| := by
  obtain ⟨M, hM0, hM⟩ := exists_designWindowW_disc_bound
  refine ⟨M / 2, by positivity, fun N₀ k u hu => ?_⟩
  set W := designWindowW (N₀ + k) (1 / ((k : ℝ) + 4)) 0 with hW
  have hWd : Differentiable ℂ W := designWindowW_differentiable _ _ _
  set H := dslope W (airyZero 1 : ℂ) with hH
  have hHd : DifferentiableOn ℂ H Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr hWd.differentiableOn
  have hHd' : Differentiable ℂ H := differentiableOn_univ.mp hHd
  have hW0 : W (airyZero 1 : ℂ) = 0 := designWindowW_at_a1_zero _ _
  have hWM : ∀ z : ℂ, ‖z - (airyZero 1 : ℂ)‖ ≤ 2 → ‖W z‖ ≤ M := fun z hz =>
    hM (N₀ + k) _ (eta_pos k).le (eta_le k) z hz
  have hcirc : ∀ z ∈ frontier (ball (airyZero 1 : ℂ) 2), ‖H z‖ ≤ M / 2 := by
    intro z hz
    rw [frontier_ball _ (by norm_num : (2 : ℝ) ≠ 0)] at hz
    have hz2 : ‖z - (airyZero 1 : ℂ)‖ = 2 := by simpa [dist_eq_norm] using hz
    have hzne : z ≠ (airyZero 1 : ℂ) := fun h => by rw [h, sub_self, norm_zero] at hz2; norm_num at hz2
    rw [hH, dslope_of_ne _ hzne, slope_def_module, hW0, sub_zero, norm_smul,
      norm_inv, hz2]
    have := hWM z hz2.le
    rw [hW]; linarith [mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hmax : ∀ z ∈ closedBall (airyZero 1 : ℂ) 2, ‖H z‖ ≤ M / 2 := fun z hz =>
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hHd'.diffContOnCl hcirc
      (by rw [closure_ball _ (by norm_num : (2 : ℝ) ≠ 0)]; exact hz)
  have hmaps : MapsTo H (ball (airyZero 1 : ℂ) 2) (closedBall (H (airyZero 1 : ℂ)) M) := by
    intro z hz
    rw [mem_closedBall_iff_norm]
    have h1 := hmax z (ball_subset_closedBall hz)
    have h2 := hmax (airyZero 1 : ℂ) (mem_closedBall_self (by norm_num))
    calc ‖H z - H (airyZero 1 : ℂ)‖ ≤ ‖H z‖ + ‖H (airyZero 1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ M := by linarith
  have hu2 : (u : ℂ) ∈ ball (airyZero 1 : ℂ) 2 := by
    rw [mem_ball_iff_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hHd'.differentiableOn
    hmaps hu2
  have hdist : dist (u : ℂ) (airyZero 1 : ℂ) = |u - airyZero 1| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hdist] at hS
  have hre : Gd N₀ k u - Gd N₀ k (airyZero 1) ≤ ‖H (u : ℂ) - H (airyZero 1 : ℂ)‖ := by
    rw [Gd_eq_neg_re_dslope N₀ k u, Gd_eq_neg_re_dslope N₀ k (airyZero 1)]
    have := Complex.re_le_norm (H (airyZero 1 : ℂ) - H (u : ℂ))
    rw [norm_sub_rev] at this
    simp only [Complex.sub_re] at this
    rw [hH] at this ⊢
    linarith
  rw [dist_eq_norm] at hS
  have : M / 2 * |u - airyZero 1| = M / 2 * |u - airyZero 1| := rfl
  nlinarith [hS, hre]

lemma designR1_pos (N : ℕ) {η : ℝ} (hη : 0 < η) : 0 < designR1 N η := by
  obtain ⟨-, htail⟩ := designR1_hasProd N η
  obtain ⟨P, hP, hPe⟩ := airyProdTail_real_pos (design_tail_hypothesis N η) (u := airyZero 1)
    (fun k hk h => airyZero_ne_of_ne le_rfl (by omega) (by omega) h)
    (fun k hk => designWidthU_ne_zero N hη hk)
  rw [hPe] at htail
  have : designR1 N η = P := by exact_mod_cast htail.symm
  rw [this]; exact hP

lemma Gd_at_a1_pos (N₀ k : ℕ) : 0 < Gd N₀ k (airyZero 1) := by
  rw [Gd_at_a1]
  have h : airyAi' (airyZero 1) ≠ 0 := airyAi'_airyNode_ne 0
  exact mul_pos (designR1_pos _ (eta_pos k)) (by positivity)

/-- `G_k(a_1) ≥ c > 0` uniformly in `k`: `R_1 ≥ 1/2` for `N ≥ N_0` (`lemma_E`), `R_1 > 0` for the
finitely many remaining `k`. -/
lemma exists_Gd_a1_lower (N₀ : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ Gd N₀ k (airyZero 1) := by
  obtain ⟨C, hC, Nab, hNab, hE⟩ := lemma_E
  have h : airyAi' (airyZero 1) ≠ 0 := airyAi'_airyNode_ne 0
  have hA : 0 < (airyAi' (airyZero 1)) ^ 2 := by positivity
  set S : ℝ := ∑ k ∈ Finset.range Nab, 1 / Gd N₀ k (airyZero 1) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => (one_div_pos.mpr (Gd_at_a1_pos N₀ k)).le
  refine ⟨min ((airyAi' (airyZero 1)) ^ 2 / 2) (1 / (1 + S)), lt_min (by positivity) (by positivity),
    fun k => ?_⟩
  by_cases hk : Nab ≤ N₀ + k
  · refine (min_le_left _ _).trans ?_
    rw [Gd_at_a1]
    have hR := (hE (N₀ + k) hk _ (eta_pos k).le (eta_le k)).2.2.2.1
    nlinarith
  · refine (min_le_right _ _).trans ?_
    have hkm : k ∈ Finset.range Nab := Finset.mem_range.mpr (by omega)
    have h1 : 1 / Gd N₀ k (airyZero 1) ≤ S :=
      Finset.single_le_sum (f := fun k => 1 / Gd N₀ k (airyZero 1))
        (fun k _ => (one_div_pos.mpr (Gd_at_a1_pos N₀ k)).le) hkm
    have hg := Gd_at_a1_pos N₀ k
    rw [div_le_iff₀ (by linarith)]
    calc (1 : ℝ) = Gd N₀ k (airyZero 1) * (1 / Gd N₀ k (airyZero 1)) := by field_simp
      _ ≤ Gd N₀ k (airyZero 1) * (1 + S) := by
          apply mul_le_mul_of_nonneg_left _ hg.le; linarith

/-- **The upper bound field of `SameSiteTailBounds (Gd N₀)`**: `G_k(u) ≤ G_k(a_1)(1 + C|u - a_1|)` on
`|u - a_1| ≤ 1`, with `C` independent of `k`, for every `N₀`. -/
theorem Gd_upper (N₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k u, |u - airyNode 0| ≤ 1 →
      Gd N₀ k u ≤ Gd N₀ k (airyNode 0) * (1 + C * |u - airyNode 0|) := by
  obtain ⟨L, hL0, hL⟩ := exists_Gd_lipschitz
  obtain ⟨c, hc, hcl⟩ := exists_Gd_a1_lower N₀
  refine ⟨L / c, by positivity, fun k u hu => ?_⟩
  rw [airyNode_zero] at hu ⊢
  have h1 := hL N₀ k u hu
  have h2 : L ≤ L / c * Gd N₀ k (airyZero 1) := by
    calc L = L / c * c := by field_simp
      _ ≤ L / c * Gd N₀ k (airyZero 1) := mul_le_mul_of_nonneg_left (hcl k) (by positivity)
  have h3 : L * |u - airyZero 1| ≤ L / c * Gd N₀ k (airyZero 1) * |u - airyZero 1| :=
    mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  nlinarith [h1, h3]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.Gd_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gd_upper

end FormalResearch.ModularBootstrap.Upper.Assembly

module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.AiryDiscBounds
public import FormalResearch.SignUncertainty.HankelTransportMass

/-!
# `HankelQuantC1`: Proposition `TE.0` / `TE.0'` for the Hankel Langer-disc density (type (I) envelope)

Copy-adaptation of `teb_quant_c1_typeII` (`QuantC1Airy.lean`, Airy case `alpha = 0`) to the
*type (I)* a-priori envelope `|Psi(u)| <= C_0 |e(u)| (Re sqrt u)^(-1/2)` (`two_edge_bootstrap.tex`,
`teb:Q1`), with the real-axis data of `HankelTransportMass`:
`Re Psi >= -delta` on `[-R, u_T]`, `int |Psi| <= 1 + delta`, `int_{u_T}^R Psi_- >= 1/2 - delta`,
`int_{-R'}^R Re Psi <= delta` (one error function `delta(c) -> 0` for the paper's `r_inf` and `eta_tr`).
The conclusion is `QuantC1B2Holds Psi u_T` with the same constants as for type (II), so users of
`teb_quant_c1_typeII` are unaffected.

**Cut bound and growth of the limit (shift trick).** `typeII_disc_avg_bound` needs the type-(II) shape
`C_0 |e| e^{varsigma Re sqrt u} |u|^(-1/2) (Re sqrt u)^(-1)`.  For `|u| <= R`, `R >= 1`, put
`Psi'(u) = Psi(u)/(u - 2 i R)`, holomorphic on `closedBall 0 R` (the pole `2iR` lies outside).
Since `Re sqrt u <= |u|^(1/2)` we have `(Re sqrt u)^(1/2) |u|^(1/2) <= |u|^(3/4) <= R <= |u - 2iR|`,
which is exactly `|Psi'(u)| <= C_0 |e(u)| |u|^(-1/2) (Re sqrt u)^(-1)` (type (II) with `varsigma = 0`).
`typeII_disc_avg_bound` then gives `|Psi'(u_0)| <= 8 e^{5/2} C_0 |e(u_0)| (1+|u_0|)^(1/2)`, and
multiplying back by `|u_0 - 2iR| <= 4 (1 + |u_0|)` (with `R = |u_0| + 2`) the loss is the polynomial factor
`(1+|u_0|)`: `|Psi(u_0)| <= 32 e^{5/2} C_0 (1+|u_0|)^(3/2) |e(u_0)|`, i.e. exponent `nu = 3/2`
instead of `1/2`.  `airy_sign_equality` accepts any real `nu` (`AiryCftSignEqualityMain`, hypothesis
`hb : forall u, |f u| <= C (1+|u|)^nu airyEnv u`), so the exponent is irrelevant downstream.  The
`(Re sqrt u)^(-1/2)` singularity itself is never integrated here: its integrability on discs is the
content of `disc_avg_neg_log_tipDist` inside `typeII_disc_avg_bound`, applied to the type-(II)-shaped
`Psi'` (whose singularity `(Re sqrt u)^(-1)|u|^(-1/2)` is the one that lemma handles).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BoundedContinuousFunction

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-- Copy of the private `airyAi'_a1_sq_pos` of `QuantC1Airy`. -/
private lemma airyAi'_a1_sq_pos : 0 < airyAi' (airyZero 1) ^ 2 := by
  let a₁ : ℝ := airyZero 1
  have hne : deriv airyAiC (a₁ : ℂ) ≠ 0 := airyZero_deriv_ne_zero 1
  have hd_ai : HasDerivAt airyAiC (deriv airyAiC (a₁ : ℂ)) (a₁ : ℂ) :=
    (differentiable_airyAiC (a₁ : ℂ)).hasDerivAt
  have hd_real : deriv airyAiC (a₁ : ℂ) = ((airyAi' a₁ : ℝ) : ℂ) := by
    have hdr := (hasDerivAt_airyAi a₁).ofReal_comp
    have hd_c : HasDerivAt (fun x : ℝ => airyAiC (x : ℂ)) (deriv airyAiC (a₁ : ℂ)) a₁ :=
      hd_ai.comp_ofReal
    have heq_r : (fun x : ℝ => airyAiC (x : ℂ)) = (fun x : ℝ => (airyAi x : ℂ)) :=
      funext airyAiC_ofReal
    rw [heq_r] at hd_c
    exact hd_c.unique hdr
  rw [hd_real, Complex.ofReal_ne_zero] at hne
  exact sq_pos_of_ne_zero hne


/-! ### Real-axis tails for the type-(I) envelope -/

/-- On `[1, ∞)` the type-(I) envelope gives `‖Ψ x‖ ≤ C₀ e^{-(4/3) x^{3/2}} ≤ C₀ e^{-(5/6)x}`. -/
private lemma hankelI_pos_real_norm_tail_le
    {Ψ : ℂ → ℂ} {C_0 A B : ℝ}
    (hC0 : 0 < C_0) (h1A : 1 ≤ A) (hAB : A ≤ B)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc A B))
    (hΨ_env : ∀ x : ℝ, 1 ≤ x → x ≤ B → ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ)) :
    ∫ x in A..B, ‖Ψ (x : ℂ)‖ ≤ (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * A) := by
  let f_env : ℝ → ℝ := fun x => C_0 * Real.exp (-(5 / 6 : ℝ) * x)
  have hf_int : IntervalIntegrable f_env volume A B :=
    (Continuous.intervalIntegrable (by unfold f_env; fun_prop) A B)
  have hnorm_int : IntervalIntegrable (fun x : ℝ => ‖Ψ (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hpt : ∀ x ∈ Icc A B, ‖Ψ (x : ℂ)‖ ≤ f_env x := by
    intro x hx
    have hx_ge1 : 1 ≤ x := h1A.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hx32 : x ≤ x ^ (3 / 2 : ℝ) := by
      simpa [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hcpow32 : ((x : ℂ) ^ (3 / 2 : ℂ)).re = x ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re]
    have henv : airyEnv (x : ℂ) ≤ Real.exp (-(5 / 6 : ℝ) * x) := by
      unfold airyEnv
      rw [hcpow32]
      apply Real.exp_le_exp.mpr
      linarith
    calc ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := hΨ_env x hx_ge1 hx.2
      _ ≤ C_0 * Real.exp (-(5 / 6 : ℝ) * x) := by gcongr
      _ = f_env x := rfl
  have hint_le : ∫ x in A..B, ‖Ψ (x : ℂ)‖ ≤ ∫ x in A..B, f_env x :=
    intervalIntegral.integral_mono_on hAB hnorm_int hf_int hpt
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -(6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * t)) (f_env x) x :=
    fun x _ => by
      have hd : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) x := by
        simpa using (hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))
      refine (hd.exp.const_mul (-(6 / 5 : ℝ) * C_0)).congr_deriv ?_
      dsimp [f_env]; ring
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hf_int
  have hB_nn : 0 ≤ (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * B) := by positivity
  linarith

private lemma hankelI_pos_real_tail_lt_quarter
    {Ψ : ℂ → ℂ} {C_0 A B : ℝ}
    (hC0 : 0 < C_0) (hA_lo : quantC1_U0 C_0 ≤ A) (hAB : A ≤ B)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc A B))
    (hΨ_env : ∀ x : ℝ, 1 ≤ x → x ≤ B → ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ)) :
    ∫ x in A..B, max 0 (-(Ψ (x : ℂ)).re) < 1 / 4 := by
  have h1_le_A : 1 ≤ A := (one_le_quantC1_U0 C_0).trans hA_lo
  have hA_log : (6 / 5 : ℝ) * Real.log (5 * C_0 + 1) ≤ A := (le_max_right _ _).trans hA_lo
  have hlog_pos : 0 < 5 * C_0 + 1 := by positivity
  have hmax_cont : ContinuousOn (fun x : ℝ => max 0 (-(Ψ (x : ℂ)).re)) (Icc A B) :=
    ContinuousOn.sup continuousOn_const ((Complex.continuous_re.comp_continuousOn hΨ_cont).neg)
  have hmax_int : IntervalIntegrable (fun x : ℝ => max 0 (-(Ψ (x : ℂ)).re)) volume A B :=
    hmax_cont.intervalIntegrable_of_Icc hAB
  have hnorm_int : IntervalIntegrable (fun x : ℝ => ‖Ψ (x : ℂ)‖) volume A B :=
    (continuous_norm.comp_continuousOn hΨ_cont).intervalIntegrable_of_Icc hAB
  have hle_norm : ∫ x in A..B, max 0 (-(Ψ (x : ℂ)).re) ≤ ∫ x in A..B, ‖Ψ (x : ℂ)‖ := by
    refine intervalIntegral.integral_mono_on hAB hmax_int hnorm_int fun x _ => ?_
    refine max_le (norm_nonneg _) ?_
    exact (neg_le.mp (abs_le.mp (Complex.abs_re_le_norm (Ψ (x : ℂ)))).1).trans (le_refl _)
  have htail := hankelI_pos_real_norm_tail_le hC0 h1_le_A hAB hΨ_cont hΨ_env
  have hexp_A : Real.exp (-(5 / 6 : ℝ) * A) ≤ (5 * C_0 + 1)⁻¹ := by
    rw [show -(5 / 6 : ℝ) * A = -((5 / 6 : ℝ) * A) by ring, Real.exp_neg,
      ← Real.exp_log hlog_pos, inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hmain : (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * A) ≤ (6 / 5 : ℝ) * C_0 * (5 * C_0 + 1)⁻¹ := by
    gcongr
  have hlt : (6 / 5 : ℝ) * C_0 * (5 * C_0 + 1)⁻¹ < 1 / 4 := by
    rw [mul_inv_lt_iff₀ hlog_pos]
    linarith
  linarith

/-- Step 0 (`TE.0`), type (I): `u_T ≤ quantC1_U0 C₀`. -/
private lemma hankelI_uT_le {Ψ : ℂ → ℂ} {C_0 R u_T δ : ℝ}
    (hC0 : 0 < C_0) (hδ_le : δ ≤ 1 / 4) (huT_le : u_T ≤ R)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc u_T R))
    (hΨ_env : ∀ x : ℝ, 1 ≤ x → x ≤ R → ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ))
    (htail : (1 / 2 : ℝ) - δ ≤ ∫ x in u_T..R, max 0 (-(Ψ (x : ℂ)).re)) :
    u_T ≤ quantC1_U0 C_0 := by
  by_contra hlt
  push Not at hlt
  have hq := hankelI_pos_real_tail_lt_quarter hC0 hlt.le huT_le hΨ_cont hΨ_env
  linarith

/-! ### Normal-families diagonal extraction (copy of the private helpers of `QuantC1Airy`) -/

private lemma arzela_ascoli_single_ball
    {F : ℕ → ℂ → ℂ} {r M : ℝ} {N₀ : ℕ} (_hr : 0 < r) (hM : 0 ≤ M)
    (hAn : ∀ n ≥ N₀, AnalyticOnNhd ℂ (F n) (closedBall (0 : ℂ) (r + 1)))
    (hBd : ∀ n ≥ N₀, ∀ z ∈ closedBall (0 : ℂ) (r + 1), ‖F n z‖ ≤ M) :
    ∃ (ψ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono ψ ∧
      TendstoUniformlyOn (fun k => F (ψ k)) g atTop (closedBall (0 : ℂ) r) := by
  classical
  let X := closedBall (0 : ℂ) r
  have : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  have hlips : ∀ n ≥ N₀, ∀ z ∈ X, ∀ w ∈ X, ‖F n z - F n w‖ ≤ M * ‖z - w‖ := fun n hn z hz w hw => by
    have h_diff_C : ∀ u ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ (F n) u := fun u hu =>
      (hAn n hn u (closedBall_subset_closedBall (by linarith) hu)).differentiableAt
    have hderiv_bd : ∀ u ∈ closedBall (0 : ℂ) r, ‖deriv (F n) u‖ ≤ M := fun u hu =>
      (typeII_cauchy_deriv_bounds (hAn n hn) hM (hBd n hn) hu).1
    exact (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le h_diff_C hderiv_bd hw hz
  let bcf : ℕ → (BoundedContinuousFunction X ℂ) := fun n =>
    if hn : n ≥ N₀ then
      BoundedContinuousFunction.mkOfCompact
        ⟨fun x => F n x.1,
          ((hAn n hn).continuousOn.mono (closedBall_subset_closedBall (by linarith))).comp_continuous
            continuous_subtype_val (fun x => x.2)⟩
    else 0
  have hin_s : ∀ (f : BoundedContinuousFunction X ℂ) (x : X),
      f ∈ Set.range bcf → f x ∈ closedBall (0 : ℂ) M := by
    rintro f x ⟨n, hn⟩
    subst hn
    dsimp [bcf]
    split_ifs with hn
    · rw [mem_closedBall_zero_iff]
      exact hBd n hn x.1 (closedBall_subset_closedBall (by linarith) x.2)
    · rw [mem_closedBall_zero_iff, BoundedContinuousFunction.coe_zero, Pi.zero_apply, norm_zero]
      exact hM
  have heq : Equicontinuous (fun f : Set.range bcf => (f.1 : X → ℂ)) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    refine ⟨ball x₀ (ε / (2 * (M + 1))), Metric.ball_mem_nhds x₀ (div_pos hε (by linarith)),
      fun y hy z hz ⟨f, hf⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hf
    dsimp [bcf]
    split_ifs with hn
    · change dist (F n y.1) (F n z.1) < ε
      rw [dist_eq_norm]
      have hyx : ‖y.1 - x₀.1‖ < ε / (2 * (M + 1)) := by
        simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hy
      have hzx : ‖z.1 - x₀.1‖ < ε / (2 * (M + 1)) := by
        simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hz
      have hyz : ‖y.1 - z.1‖ < ε / (M + 1) := by
        calc ‖y.1 - z.1‖ = ‖(y.1 - x₀.1) - (z.1 - x₀.1)‖ := by ring_nf
          _ ≤ ‖y.1 - x₀.1‖ + ‖z.1 - x₀.1‖ := norm_sub_le _ _
          _ < ε / (2 * (M + 1)) + ε / (2 * (M + 1)) := add_lt_add hyx hzx
          _ = ε / (M + 1) := by field_simp [(by linarith : M + 1 ≠ 0)]; ring
      calc ‖F n y.1 - F n z.1‖ ≤ M * ‖y.1 - z.1‖ := hlips n hn y.1 y.2 z.1 z.2
        _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hyz.le hM
        _ < (M + 1) * (ε / (M + 1)) := by
            have : 0 < ε / (M + 1) := div_pos hε (by linarith)
            nlinarith
        _ = ε := by field_simp [(by linarith : M + 1 ≠ 0)]
    · simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, dist_self]
      exact hε
  have hcomp : IsCompact (closure (Set.range bcf)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall 0 M)
      (Set.range bcf) hin_s heq
  obtain ⟨g₀, -, ψ, hψ_mono, hψ_tend⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  let g : ℂ → ℂ := fun z => if hz : z ∈ X then g₀ ⟨z, hz⟩ else 0
  refine ⟨ψ, g, hψ_mono, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at hψ_tend
  obtain ⟨K, hK⟩ := hψ_tend ε hε
  filter_upwards [Filter.eventually_ge_atTop (max K N₀)] with k hk
  intro z hz
  have hkK : K ≤ k := (le_max_left K N₀).trans hk
  have hψN : N₀ ≤ ψ k := (le_max_right K N₀).trans (hk.trans (hψ_mono.id_le k))
  have hdist := hK k hkK
  have hg_eq : g z = g₀ ⟨z, hz⟩ := by
    dsimp only [g]
    split_ifs with h
    · rfl
    · exact absurd hz h
  have hbcf_eq : bcf (ψ k) ⟨z, hz⟩ = F (ψ k) z := by
    dsimp [bcf]; simp [hψN]
  have hcoe : dist (bcf (ψ k) ⟨z, hz⟩) (g₀ ⟨z, hz⟩) ≤ dist (bcf (ψ k)) g₀ :=
    BoundedContinuousFunction.dist_coe_le_dist (x := (⟨z, hz⟩ : X))
  calc dist (g z) (F (ψ k) z)
      = dist (g₀ ⟨z, hz⟩) (bcf (ψ k) ⟨z, hz⟩) := by rw [hg_eq, hbcf_eq]
    _ = dist (bcf (ψ k) ⟨z, hz⟩) (g₀ ⟨z, hz⟩) := dist_comm _ _
    _ ≤ dist (bcf (ψ k)) g₀ := hcoe
    _ < ε := hdist

private lemma arzela_ascoli_diagonal
    {F : ℕ → ℂ → ℂ} {M : ℕ → ℝ} {K : ℕ → ℕ}
    (hM : ∀ m, 0 ≤ M m)
    (hAn : ∀ m, ∀ n ≥ K m, AnalyticOnNhd ℂ (F n) (closedBall (0 : ℂ) ((m : ℝ) + 2)))
    (hBd : ∀ m, ∀ n ≥ K m, ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 2), ‖F n z‖ ≤ M m) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧
      ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) G atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)) := by
  let PSub (m : ℕ) (ψ : ℕ → ℕ) : Prop :=
    StrictMono ψ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (ψ k)) g atTop (closedBall (0 : ℂ) ((m : ℝ) + 1))
  let step : ∀ (m : ℕ) (p : { ψ : ℕ → ℕ // PSub m ψ }),
      { ψ' : ℕ → ℕ // PSub (m + 1) ψ' ∧ ∃ α : ℕ → ℕ, StrictMono α ∧ ψ' = p.1 ∘ α } :=
    fun m p => by
      obtain ⟨ψ, hψ_mono, _⟩ := p
      have hAn' : ∀ n ≥ K (m + 1),
          AnalyticOnNhd ℂ (F (ψ n)) (closedBall (0 : ℂ) ((((m + 1 : ℕ) : ℝ) + 1) + 1)) := by
        intro n hn
        have hψn : K (m + 1) ≤ ψ n := hn.trans (hψ_mono.id_le n)
        rw [show (((m + 1 : ℕ) : ℝ) + 1) + 1 = ((m + 1 : ℕ) : ℝ) + 2 by ring]
        exact hAn (m + 1) (ψ n) hψn
      have hBd' : ∀ n ≥ K (m + 1),
          ∀ z ∈ closedBall (0 : ℂ) ((((m + 1 : ℕ) : ℝ) + 1) + 1), ‖F (ψ n) z‖ ≤ M (m + 1) := by
        intro n hn z hz
        have hψn : K (m + 1) ≤ ψ n := hn.trans (hψ_mono.id_le n)
        rw [show (((m + 1 : ℕ) : ℝ) + 1) + 1 = ((m + 1 : ℕ) : ℝ) + 2 by ring] at hz
        exact hBd (m + 1) (ψ n) hψn z hz
      have hr_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
      have hex :=
        arzela_ascoli_single_ball (F := fun n => F (ψ n)) hr_pos (hM (m + 1)) hAn' hBd'
      let α := Classical.choose hex
      let g := Classical.choose (Classical.choose_spec hex)
      have hspec := Classical.choose_spec (Classical.choose_spec hex)
      exact ⟨ψ ∘ α, ⟨hψ_mono.comp hspec.1, g, hspec.2⟩, α, hspec.1, rfl⟩
  let ψ0_ex := arzela_ascoli_single_ball (F := F) (r := 1) (M := M 0) (N₀ := K 0) zero_lt_one (hM 0)
    (fun n hn => by
      rw [show (1 : ℝ) + 1 = ((0 : ℕ) : ℝ) + 2 by norm_num]
      exact hAn 0 n hn)
    (fun n hn z hz => by
      rw [show (1 : ℝ) + 1 = ((0 : ℕ) : ℝ) + 2 by norm_num] at hz
      exact hBd 0 n hn z hz)
  let base : { ψ : ℕ → ℕ // PSub 0 ψ } :=
    ⟨Classical.choose ψ0_ex, (Classical.choose_spec (Classical.choose_spec ψ0_ex)).1,
      Classical.choose (Classical.choose_spec ψ0_ex), by
        simpa [Nat.cast_zero, zero_add] using
          (Classical.choose_spec (Classical.choose_spec ψ0_ex)).2⟩
  let seq : ∀ m : ℕ, { ψ : ℕ → ℕ // PSub m ψ } :=
    Nat.rec base (fun m prev => ⟨(step m prev).1, (step m prev).2.1⟩)
  have hfactor : ∀ m k : ℕ, m ≤ k → ∃ α : ℕ → ℕ, StrictMono α ∧ (seq k).1 = (seq m).1 ∘ α := by
    intro m k hmk
    induction hmk with
    | refl => exact ⟨id, strictMono_id, rfl⟩
    | @step k _ ih =>
      rcases ih with ⟨α₁, hα₁, heq₁⟩
      obtain ⟨α₂, hα₂, heq₂⟩ := (step k (seq k)).2.2
      exact ⟨α₁ ∘ α₂, hα₁.comp hα₂, by change (step k (seq k)).1 = _; rw [heq₂, heq₁]; rfl⟩
  let φ : ℕ → ℕ := fun k => (seq k).1 k
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨α, hα, heq⟩ := (step k (seq k)).2.2
    have hstep_val : φ (k + 1) = (seq k).1 (α (k + 1)) := by
      dsimp [φ]
      change (step k (seq k)).1 (k + 1) = _
      rw [heq]; rfl
    rw [hstep_val]
    exact (seq k).2.1 (lt_of_lt_of_le (Nat.lt_succ_self k) (hα.id_le (k + 1)))
  have hG_exists : ∀ m : ℕ, ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (φ k)) g atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)) := by
    intro m
    obtain ⟨g, hg⟩ := (seq m).2.2
    refine ⟨g, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hg ε hε)
    refine Filter.eventually_atTop.mpr ⟨max m N, fun k hk z hz => ?_⟩
    obtain ⟨α, hα, heq⟩ := hfactor m k ((le_max_left m N).trans hk)
    have hφk : φ k = (seq m).1 (α k) := by dsimp [φ]; rw [heq]; rfl
    rw [hφk]
    exact hN (α k) (((le_max_right m N).trans hk).trans (hα.id_le k)) z hz
  choose g_m hg_m using hG_exists
  let G : ℂ → ℂ := fun z => g_m ⌈‖z‖⌉₊ z
  have hg_agree : ∀ m : ℕ, ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 1), g_m m z = G z := by
    intro m z hz
    let m' := ⌈‖z‖⌉₊
    have hm'_le : ‖z‖ ≤ (m' : ℝ) := Nat.le_ceil _
    have hz_m' : z ∈ closedBall (0 : ℂ) ((m' : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff]; linarith
    have h1 : Tendsto (fun k => F (φ k) z) atTop (𝓝 (g_m m z)) :=
      (hg_m m).tendsto_at hz
    have h2 : Tendsto (fun k => F (φ k) z) atTop (𝓝 (g_m m' z)) :=
      (hg_m m').tendsto_at hz_m'
    exact tendsto_nhds_unique h1 h2
  refine ⟨φ, G, hφ_mono, fun m => ?_⟩
  exact (hg_m m).congr_right fun z hz => hg_agree m z hz


/-! ### Copies of the private `L¹`/extremal helpers of `QuantC1Airy` -/

private lemma integral_Iic_add_Ioi_univ {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    (∫ x in Iic a, f x) + (∫ x in Ioi a, f x) = ∫ x : ℝ, f x := by
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn hf.integrableOn,
    Iic_union_Ioi, setIntegral_univ]

private lemma integral_Ioi_airyExtremal_max_neg :
    ∫ x in Ioi (airyZero 1), max 0 (-(airyExtremal (x : ℂ)).re) = quantC1Mass / 2 := by
  let a₁ : ℝ := airyZero 1
  have hint_norm : Integrable (fun x : ℝ => ‖airyExtremal (x : ℂ)‖) := airyExtremal_integrable.norm
  have hint_re : Integrable (fun x : ℝ => (airyExtremal (x : ℂ)).re) := airyExtremal_integrable.re
  have hsplit_norm :
      (∫ x in Iic a₁, ‖airyExtremal (x : ℂ)‖) + (∫ x in Ioi a₁, ‖airyExtremal (x : ℂ)‖) =
        quantC1Mass :=
    integral_Iic_add_Ioi_univ hint_norm a₁
  have hsplit_re :
      (∫ x in Iic a₁, (airyExtremal (x : ℂ)).re) + (∫ x in Ioi a₁, (airyExtremal (x : ℂ)).re) = 0 := by
    rw [integral_Iic_add_Ioi_univ hint_re a₁]
    exact airyExtremal_attains.2.2.2.2.2.1
  have hre_Iic : ∫ x in Iic a₁, (airyExtremal (x : ℂ)).re = ∫ x in Iic a₁, ‖airyExtremal (x : ℂ)‖ := by
    refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
    have him : (airyExtremal (x : ℂ)).im = 0 := airyExtremal_attains.2.2.2.1 x
    have hnn : 0 ≤ (airyExtremal (x : ℂ)).re := airyExtremal_attains.2.2.2.2.1 x hx
    have hnorm : ‖airyExtremal (x : ℂ)‖ = |(airyExtremal (x : ℂ)).re| := by
      have heq : airyExtremal (x : ℂ) = ((airyExtremal (x : ℂ)).re : ℂ) := Complex.ext rfl him
      conv_lhs => rw [heq]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_nonneg hnn]
  have hre_Ioi : ∫ x in Ioi a₁, (airyExtremal (x : ℂ)).re = - ∫ x in Ioi a₁, ‖airyExtremal (x : ℂ)‖ := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have him : (airyExtremal (x : ℂ)).im = 0 := airyExtremal_attains.2.2.2.1 x
    have hnp : (airyExtremal (x : ℂ)).re ≤ 0 := by
      rw [airyExtremal_re]
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by linarith [mem_Ioi.mp hx]))
    have hnorm : ‖airyExtremal (x : ℂ)‖ = |(airyExtremal (x : ℂ)).re| := by
      have heq : airyExtremal (x : ℂ) = ((airyExtremal (x : ℂ)).re : ℂ) := Complex.ext rfl him
      conv_lhs => rw [heq]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_nonpos hnp]
    ring
  have hIoi_eq : ∫ x in Ioi a₁, ‖airyExtremal (x : ℂ)‖ = quantC1Mass / 2 := by linarith
  have hmax_eq : ∫ x in Ioi a₁, max 0 (-(airyExtremal (x : ℂ)).re) =
      ∫ x in Ioi a₁, ‖airyExtremal (x : ℂ)‖ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have him : (airyExtremal (x : ℂ)).im = 0 := airyExtremal_attains.2.2.2.1 x
    have hnp : (airyExtremal (x : ℂ)).re ≤ 0 := by
      rw [airyExtremal_re]
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by linarith [mem_Ioi.mp hx]))
    have hnorm : ‖airyExtremal (x : ℂ)‖ = |(airyExtremal (x : ℂ)).re| := by
      have heq : airyExtremal (x : ℂ) = ((airyExtremal (x : ℂ)).re : ℂ) := Complex.ext rfl him
      conv_lhs => rw [heq]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, abs_of_nonpos hnp, max_eq_right (by linarith)]
  rw [hmax_eq, hIoi_eq]

private lemma integrable_of_symmetric_interval_norm_le {f : ℝ → ℂ} {C : ℝ}
    (hf_cont : Continuous f) (hC : ∀ N : ℕ, ∫ x in (-N : ℝ)..(N : ℝ), ‖f x‖ ≤ C) :
    Integrable f := by
  have hC_nn : 0 ≤ C := by
    have := hC 0
    simpa using this
  have h_lint_le : ∀ N : ℕ, ∫⁻ x : ℝ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x ≤
      ENNReal.ofReal C := by
    intro N
    have hle : (-N : ℝ) ≤ (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
    have hint_on : IntegrableOn (fun y => ‖f y‖) (Ioc (-N : ℝ) (N : ℝ)) :=
      (hf_cont.norm.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have h_eq : ∫⁻ x : ℝ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x =
        ENNReal.ofReal (∫ x in (-N : ℝ)..(N : ℝ), ‖f x‖) := by
      rw [lintegral_indicator measurableSet_Ioc,
        show (∫⁻ x in Ioc (-N : ℝ) (N : ℝ), ‖f x‖ₑ) =
            ∫⁻ x in Ioc (-N : ℝ) (N : ℝ), ‖‖f x‖‖ₑ by simp [enorm_norm],
        ← ofReal_integral_norm_eq_lintegral_enorm hint_on, intervalIntegral.integral_of_le hle]
      congr 2; ext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal (hC N)
  have hmono : Monotone (fun (N : ℕ) (x : ℝ) =>
      (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) := by
    intro m n hmn x
    by_cases hx : x ∈ Ioc (-m : ℝ) (m : ℝ)
    · have hx' : x ∈ Ioc (-n : ℝ) (n : ℝ) :=
        ⟨by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; linarith [hx.1],
         hx.2.trans (Nat.cast_le.mpr hmn)⟩
      simp [hx, hx']
    · simp [hx]
  have hsup : (⨆ N : ℕ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ)) = fun y => ‖f y‖ₑ := by
    ext x
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun N => by
        by_cases hx : x ∈ Ioc (-N : ℝ) (N : ℝ)
        · simp [hx]
        · simp [hx]
    · obtain ⟨N, hN⟩ := exists_nat_gt |x|
      have hx : x ∈ Ioc (-N : ℝ) (N : ℝ) :=
        ⟨by linarith [(abs_lt.mp hN).1], (abs_lt.mp hN).2.le⟩
      have h_eq : (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x = ‖f x‖ₑ := by simp [hx]
      rw [← h_eq]
      exact le_iSup (fun N : ℕ => (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) N
  have h_meas : ∀ N : ℕ, Measurable (fun x : ℝ =>
      (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) := fun N =>
    hf_cont.enorm.measurable.indicator measurableSet_Ioc
  have hfin : ∫⁻ x : ℝ, ‖f x‖ₑ ≤ ENNReal.ofReal C := by
    have h_eq_sup : ∀ x : ℝ, ‖f x‖ₑ =
        ⨆ N : ℕ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x := fun x => by
      rw [← congrFun hsup x, iSup_apply]
    rw [lintegral_congr h_eq_sup, lintegral_iSup h_meas hmono]
    exact iSup_le h_lint_le
  exact ⟨hf_cont.aestronglyMeasurable, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top⟩

/-! ### Shift trick: cut bound and growth of a type-(I) function from `typeII_disc_avg_bound` -/

lemma hankelI_sqrt_re_pos {u : ℂ} (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) : 0 < (u ^ (1 / 2 : ℂ)).re := by
  by_contra hle
  have h0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
  have him := airySqrtRe_mul_im u
  have hre := airySqrtRe_sq_sub u
  unfold airySqrtRe at him hre
  rw [h0] at him hre
  exact hcut ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩

/-- The pointwise comparison behind the shift trick: for `‖u‖ ≤ R`, `1 ≤ R`, off the cut,
`(Re √u)^{-1/2} / ‖u - 2iR‖ ≤ ‖u‖^{-1/2} (Re √u)^{-1}`
(because `(Re √u)^{1/2} ‖u‖^{1/2} ≤ ‖u‖^{3/4} ≤ R ≤ ‖u - 2iR‖`). -/
lemma hankelI_shift_ineq {R : ℝ} (hR : 1 ≤ R) {u : ℂ} (hu : ‖u‖ ≤ R)
    (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ)) * ‖u - 2 * R * I‖⁻¹ ≤
      ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  set s : ℝ := (u ^ (1 / 2 : ℂ)).re with hs
  have hs_pos : 0 < s := hankelI_sqrt_re_pos hcut
  have hu0 : u ≠ 0 := fun h => hcut ⟨by simp [h], by simp [h]⟩
  have hn_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set n : ℝ := ‖u‖ with hn
  have hD : R ≤ ‖u - 2 * R * I‖ := by
    have h1 : ‖(2 * R * I : ℂ)‖ = 2 * R := by
      simp [Complex.norm_mul, abs_of_pos (by linarith : (0 : ℝ) < R)]
    have := norm_sub_norm_le (2 * R * I : ℂ) u
    rw [h1, norm_sub_rev] at this
    linarith
  have hs_le : s ≤ n ^ (1 / 2 : ℝ) := by
    have h1 : s ≤ ‖u ^ (1 / 2 : ℂ)‖ := Complex.re_le_norm _
    rw [norm_cpow_half, Real.sqrt_eq_rpow] at h1
    exact h1
  have hb_le : s ^ (1 / 2 : ℝ) ≤ n ^ (1 / 4 : ℝ) := by
    calc s ^ (1 / 2 : ℝ) ≤ (n ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hs_pos.le hs_le (by norm_num)
      _ = n ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hn_pos.le]; norm_num
  have hab : n ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) ≤ ‖u - 2 * R * I‖ := by
    have h34 : n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ) = n ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have hnR : n ^ (3 / 4 : ℝ) ≤ R := by
      calc n ^ (3 / 4 : ℝ) ≤ R ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hn_pos.le hu (by norm_num)
        _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
        _ = R := Real.rpow_one R
    calc n ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) ≤ n ^ (1 / 2 : ℝ) * n ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hb_le (Real.rpow_nonneg hn_pos.le _)
      _ = n ^ (3 / 4 : ℝ) := h34
      _ ≤ R := hnR
      _ ≤ _ := hD
  have ha_pos : 0 < n ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hb_pos : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs_pos _
  have hbb : s = s ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hs_pos]; norm_num
  rw [Real.rpow_neg hs_pos.le, Real.rpow_neg hn_pos.le]
  have hinv : ‖u - 2 * R * I‖⁻¹ ≤ (n ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ))⁻¹ :=
    inv_anti₀ (mul_pos ha_pos hb_pos) hab
  calc (s ^ (1 / 2 : ℝ))⁻¹ * ‖u - 2 * R * I‖⁻¹
      ≤ (s ^ (1 / 2 : ℝ))⁻¹ * (n ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr hb_pos.le)
    _ = (n ^ (1 / 2 : ℝ))⁻¹ * s⁻¹ := by
        conv_rhs => rw [hbb]
        field_simp

/-- **Growth of a type-(I) function, cut included** (`typeII_disc_avg_bound` applied to
`Ψ(u)/(u - 2iR)`, `R = ‖u₀‖ + 2`): `‖Ψ u₀‖ ≤ 32 e^{5/2} C₀ (1+‖u₀‖)^{3/2} airyEnv u₀`. -/
theorem hankelI_disc_bound {Ψ : ℂ → ℂ} {R_dom C_0 : ℝ} (hC0 : 0 < C_0)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R_dom, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ)))
    {u₀ : ℂ} (hR : ‖u₀‖ + 2 ≤ R_dom) :
    ‖Ψ u₀‖ ≤ 32 * Real.exp (5 / 2) * C_0 * (1 + ‖u₀‖) ^ (3 / 2 : ℝ) * airyEnv u₀ := by
  set R : ℝ := ‖u₀‖ + 2 with hRdef
  have hR1 : 1 ≤ R := by have := norm_nonneg u₀; linarith
  let Ψ' : ℂ → ℂ := fun u => Ψ u / (u - 2 * R * I)
  have hpole : ∀ u ∈ closedBall (0 : ℂ) R, u - 2 * R * I ≠ 0 := by
    intro u hu h
    have hu' : ‖u‖ ≤ R := mem_closedBall_zero_iff.mp hu
    have : u = 2 * R * I := sub_eq_zero.mp h
    have h2 : ‖u‖ = 2 * R := by
      rw [this]; simp [Complex.norm_mul, abs_of_pos (by linarith : (0 : ℝ) < R)]
    linarith
  have hΨ'_an : AnalyticOnNhd ℂ Ψ' (closedBall (0 : ℂ) R) := by
    intro u hu
    have h1 : AnalyticAt ℂ Ψ u := hΨ_an u (closedBall_subset_closedBall (by linarith) hu)
    have h2 : AnalyticAt ℂ (fun u : ℂ => u - 2 * R * I) u := by fun_prop
    exact h1.div h2 (hpole u hu)
  have hΨ'_env : ∀ u ∈ closedBall (0 : ℂ) R, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ' u‖ ≤ C_0 * airyEnv u * Real.exp (0 * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
    intro u hu hcut
    have hu' : ‖u‖ ≤ R := mem_closedBall_zero_iff.mp hu
    have h1 := hΨ_env u (closedBall_subset_closedBall (by linarith) hu) hcut
    have h2 := hankelI_shift_ineq hR1 hu' hcut
    have hE := airyEnv_pos u
    simp only [Ψ', norm_div, zero_mul, Real.exp_zero, mul_one]
    rw [div_eq_mul_inv]
    calc ‖Ψ u‖ * ‖u - 2 * R * I‖⁻¹
        ≤ (C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ))) * ‖u - 2 * R * I‖⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (norm_nonneg _))
      _ = C_0 * airyEnv u * (((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ)) * ‖u - 2 * R * I‖⁻¹) := by ring
      _ ≤ C_0 * airyEnv u * (‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have hdisc := (typeII_disc_avg_bound (R_dom := R) (R₁ := ‖u₀‖) (C_0 := C_0) (ς := 0)
    (norm_nonneg u₀) (by rw [hRdef]) hC0 le_rfl hΨ'_an hΨ'_env
    (mem_closedBall_zero_iff.mpr le_rfl)).1
  simp only [zero_mul, Real.exp_zero, mul_one] at hdisc
  have hpole0 : u₀ - 2 * R * I ≠ 0 := hpole u₀ (mem_closedBall_zero_iff.mpr (by rw [hRdef]; linarith))
  have hnorm_pole : ‖u₀ - 2 * R * I‖ ≤ 4 * (1 + ‖u₀‖) := by
    have h1 : ‖(2 * R * I : ℂ)‖ = 2 * R := by
      simp [Complex.norm_mul, abs_of_pos (by linarith : (0 : ℝ) < R)]
    calc ‖u₀ - 2 * R * I‖ ≤ ‖u₀‖ + ‖(2 * R * I : ℂ)‖ := norm_sub_le _ _
      _ = ‖u₀‖ + 2 * (‖u₀‖ + 2) := by rw [h1, hRdef]
      _ ≤ 4 * (1 + ‖u₀‖) := by linarith [norm_nonneg u₀]
  have hΨ_eq : ‖Ψ u₀‖ = ‖Ψ' u₀‖ * ‖u₀ - 2 * R * I‖ := by
    simp only [Ψ', norm_div]
    field_simp [norm_ne_zero_iff.mpr hpole0]
  have hE := airyEnv_pos u₀
  have h1p : 0 < 1 + ‖u₀‖ := by positivity
  have hpow : (1 + ‖u₀‖) ^ (1 / 2 : ℝ) * (1 + ‖u₀‖) = (1 + ‖u₀‖) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add h1p, Real.rpow_one]
  rw [hΨ_eq]
  calc ‖Ψ' u₀‖ * ‖u₀ - 2 * R * I‖
      ≤ (8 * Real.exp (5 / 2) * C_0 * airyEnv u₀ * (1 + ‖u₀‖) ^ (1 / 2 : ℝ)) * (4 * (1 + ‖u₀‖)) :=
        mul_le_mul hdisc hnorm_pole (norm_nonneg _) (by positivity)
    _ = 32 * Real.exp (5 / 2) * C_0 * ((1 + ‖u₀‖) ^ (1 / 2 : ℝ) * (1 + ‖u₀‖)) * airyEnv u₀ := by ring
    _ = _ := by rw [hpow]

/-- Cut-inclusive sup bound on `closedBall 0 R₁` (`R₁ + 2 ≤ R_dom`), type (I). -/
theorem hankelI_cut_bound {Ψ : ℂ → ℂ} {R_dom R₁ C_0 : ℝ} (hR₁ : 0 ≤ R₁) (hC0 : 0 < C_0)
    (hΨ_an : AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) R_dom))
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R_dom, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ)))
    (hR : R₁ + 2 ≤ R_dom) {u₀ : ℂ} (hu₀ : u₀ ∈ closedBall (0 : ℂ) R₁) :
    ‖Ψ u₀‖ ≤ 32 * Real.exp (5 / 2) * C_0 * (1 + R₁) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) := by
  have hn : ‖u₀‖ ≤ R₁ := mem_closedBall_zero_iff.mp hu₀
  have h1 := hankelI_disc_bound hC0 hΨ_an hΨ_env (u₀ := u₀) (by linarith)
  have he : airyEnv u₀ ≤ Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) :=
    (airyEnv_le_exp_three_halves u₀).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hn (by norm_num)) (by norm_num)))
  have hp : (1 + ‖u₀‖) ^ (3 / 2 : ℝ) ≤ (1 + R₁) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  refine h1.trans ?_
  have := airyEnv_pos u₀
  gcongr

/-- On `[1, R]` the type-(I) envelope reduces to `‖Ψ x‖ ≤ C₀ airyEnv x` (`(Re √x)^{-1/2} = x^{-1/4} ≤ 1`). -/
lemma hankelI_pos_real_env {Ψ : ℂ → ℂ} {C_0 R : ℝ} (hC0 : 0 < C_0)
    (hΨ_env : ∀ u ∈ closedBall (0 : ℂ) R, ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ)))
    {x : ℝ} (hx1 : 1 ≤ x) (hxR : x ≤ R) : ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hu : (x : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxR
  have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by
    intro h0; simp only [Complex.ofReal_re] at h0; linarith [h0.2]
  have h1 := hΨ_env (x : ℂ) hu hcut
  have hcp : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
  rw [hcp] at h1
  have hs1 : 1 ≤ √x := Real.one_le_sqrt.mpr hx1
  have hle : (√x) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
  have hE := airyEnv_pos (x : ℂ)
  calc ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) * (√x) ^ (-(1 / 2 : ℝ)) := h1
    _ ≤ C_0 * airyEnv (x : ℂ) * 1 := by gcongr
    _ = C_0 * airyEnv (x : ℂ) := mul_one _

/-! ### The compactness theorem -/

/-- **Proposition `TE.0` / `TE.0'`, type-(I) envelope** (`two_edge_bootstrap.tex`, `teb:quant_c1`
with `teb:Q1` type (I), `(P, Q) = (1, 0)`): for any `C₀ > 0`, `R_dom → ∞` and an error function
`δ → 0` (standing for both `r_∞` and `η_tr`), there is `c₁ ≥ 2` such that every `Ψ, u_T` with
`a₁ < u_T ≤ R_dom c'`, `c' ≥ c₁`, holomorphic on `closedBall 0 (R_dom c')`, real on the real axis,
with `‖Ψ u‖ ≤ C₀ |e(u)| (Re √u)^{-1/2}` off the cut, `Re Ψ ≥ -δ` on `[-R, u_T]`, `∫|Ψ| ≤ 1 + δ`,
`∫_{u_T}^R Ψ_- ≥ 1/2 - δ` and `∫_{-R'}^R Re Ψ ≤ δ` (`-R' ≤ u_T`) obeys `QuantC1B2Holds Ψ u_T`.
No cut bound is assumed: it follows from `hankelI_cut_bound`. -/
theorem hankel_quant_c1_typeI {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom δ_lobe : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c)
    (hδ_lim : Tendsto δ_lobe atTop (𝓝 0)) :
    ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' →
      ∀ (Ψ : ℂ → ℂ) (u_T : ℝ),
        AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R_dom c')) →
        (∀ x ∈ Icc (-R_dom c') (R_dom c'), (Ψ (x : ℂ)).im = 0) →
        (∀ u ∈ closedBall (0 : ℂ) (R_dom c'), ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ))) →
        airyZero 1 < u_T → u_T ≤ R_dom c' →
        (∀ x ∈ Icc (-R_dom c') u_T, -δ_lobe c' ≤ (Ψ (x : ℂ)).re) →
        (∫ x in (-R_dom c')..(R_dom c'), ‖Ψ (x : ℂ)‖ ≤ 1 + δ_lobe c') →
        ((1 / 2 : ℝ) - δ_lobe c' ≤ ∫ x in u_T..(R_dom c'), max 0 (-(Ψ (x : ℂ)).re)) →
        (∀ R' ∈ Icc (0 : ℝ) (R_dom c'), -R' ≤ u_T →
          ∫ x in (-R')..(R_dom c'), (Ψ (x : ℂ)).re ≤ δ_lobe c') →
        QuantC1B2Holds Ψ u_T := by
  by_contra h_none
  push Not at h_none
  have hex_seq : ∀ n : ℕ, ∃ c' ≥ max (n : ℝ) 2, ∃ (Ψ : ℂ → ℂ) (u_T : ℝ),
      AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R_dom c')) ∧
      (∀ x ∈ Icc (-R_dom c') (R_dom c'), (Ψ (x : ℂ)).im = 0) ∧
      (∀ u ∈ closedBall (0 : ℂ) (R_dom c'), ¬ (u.im = 0 ∧ u.re ≤ 0) →
        ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ))) ∧
      airyZero 1 < u_T ∧ u_T ≤ R_dom c' ∧
      (∀ x ∈ Icc (-R_dom c') u_T, -δ_lobe c' ≤ (Ψ (x : ℂ)).re) ∧
      (∫ x in (-R_dom c')..(R_dom c'), ‖Ψ (x : ℂ)‖ ≤ 1 + δ_lobe c') ∧
      ((1 / 2 : ℝ) - δ_lobe c' ≤ ∫ x in u_T..(R_dom c'), max 0 (-(Ψ (x : ℂ)).re)) ∧
      (∀ R' ∈ Icc (0 : ℝ) (R_dom c'), -R' ≤ u_T →
        ∫ x in (-R')..(R_dom c'), (Ψ (x : ℂ)).re ≤ δ_lobe c') ∧
      ¬ QuantC1B2Holds Ψ u_T := by
    intro n
    obtain ⟨c', hc', Ψ, u_T, h1, h2, h3, h4⟩ := h_none (max (n : ℝ) 2) (le_max_right _ _)
    exact ⟨c', hc', Ψ, u_T, h1, h2,
      (fun u hu hcut => h3 u hu (fun him => not_le.mp fun hle => hcut ⟨him, hle⟩)), h4⟩
  choose c'_seq hc'_ge Ψ_seq uT_seq hspec using hex_seq
  have hc'_atTop : Tendsto c'_seq atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) 2).trans (hc'_ge n)) tendsto_natCast_atTop_atTop
  have hR_seq : Tendsto (fun n => R_dom (c'_seq n)) atTop atTop := hR_lim.comp hc'_atTop
  have hδ_seq_nn : ∀ᶠ n in atTop, 0 ≤ δ_lobe (c'_seq n) := hc'_atTop.eventually hδ_nn
  have hδ_seq_lim : Tendsto (fun n => δ_lobe (c'_seq n)) atTop (𝓝 0) := hδ_lim.comp hc'_atTop
  let U₀ : ℝ := quantC1_U0 C_0
  have hU0_ge1 : 1 ≤ U₀ := one_le_quantC1_U0 C_0
  let a₁ : ℝ := airyZero 1
  have ha1_neg : a₁ < 0 := airyZero_neg 1
  let M_seq : ℕ → ℝ := fun m =>
    32 * Real.exp (5 / 2) * C_0 * (1 + ((m : ℝ) + 2)) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * ((m : ℝ) + 2) ^ (3 / 2 : ℝ))
  have hM_nn : ∀ m, 0 ≤ M_seq m := fun m => by dsimp [M_seq]; positivity
  have hK_ex : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ((m : ℝ) + 4) ≤ R_dom (c'_seq n) ∧
      0 ≤ δ_lobe (c'_seq n) ∧ δ_lobe (c'_seq n) ≤ 1 / 4 ∧
      U₀ ≤ R_dom (c'_seq n) := by
    intro m
    have hev_R : ∀ᶠ n in atTop, max ((m : ℝ) + 4) U₀ ≤ R_dom (c'_seq n) :=
      hR_seq (eventually_ge_atTop _)
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ 1 / 4 :=
      hδ_seq_lim (Iic_mem_nhds (by norm_num))
    have hev_all := hev_R.and (hδ_seq_nn.and hev_δ)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev_all
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hR1, hδ0, hδq⟩ := hN n hn
    exact ⟨(le_max_left _ _).trans hR1, hδ0, hδq, (le_max_right _ _).trans hR1⟩
  choose K_seq hK_spec using hK_ex
  have hAn_seq : ∀ m, ∀ n ≥ K_seq m,
      AnalyticOnNhd ℂ (Ψ_seq n) (closedBall (0 : ℂ) ((m : ℝ) + 2)) := by
    intro m n hn
    exact (hspec n).1.mono (closedBall_subset_closedBall (by linarith [(hK_spec m n hn).1]))
  have hBd_seq : ∀ m, ∀ n ≥ K_seq m,
      ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 2), ‖Ψ_seq n z‖ ≤ M_seq m := by
    intro m n hn z hz
    have hsp := hK_spec m n hn
    have hR1 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have hR_dom : ((m : ℝ) + 2) + 2 ≤ R_dom (c'_seq n) := by linarith [hsp.1]
    exact hankelI_cut_bound hR1 hC0 (hspec n).1 (hspec n).2.2.1 hR_dom hz
  obtain ⟨φ, Φ_inf, hφ_mono, hΦ_unif⟩ := arzela_ascoli_diagonal hM_nn hAn_seq hBd_seq
  have hφ_atTop : Tendsto φ atTop atTop := hφ_mono.tendsto_atTop
  -- Holomorphicity of `Φ_inf` on all of `ℂ`
  have hΦ_diff : Differentiable ℂ Φ_inf := by
    intro z
    let m : ℕ := ⌈‖z‖⌉₊ + 1
    have h_open : IsOpen (ball (0 : ℂ) ((m : ℝ) + 1)) := isOpen_ball
    have hz_ball : z ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_ball_zero_iff]
      have : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
      dsimp [m]; push_cast; linarith
    have h_loc : TendstoLocallyUniformlyOn (fun k => Ψ_seq (φ k)) Φ_inf atTop
        (ball (0 : ℂ) ((m : ℝ) + 1)) :=
      (hΦ_unif m).tendstoLocallyUniformlyOn.mono ball_subset_closedBall
    have h_ev_diff : ∀ᶠ k in atTop, DifferentiableOn ℂ (Ψ_seq (φ k)) (ball (0 : ℂ) ((m : ℝ) + 1)) := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      exact (hAn_seq m (φ k) (hN k hk)).differentiableOn.mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
    exact ((h_loc.differentiableOn h_ev_diff h_open) z hz_ball).differentiableAt
      (h_open.mem_nhds hz_ball)
  -- Growth bound on `Φ_inf` from `hankelI_disc_bound` (shift trick, exponent `3/2`)
  let C_env : ℝ := 32 * Real.exp (5 / 2) * C_0
  have hC_env_nn : 0 ≤ C_env := by dsimp [C_env]; positivity
  have hΦ_env : ∀ u : ℂ, ‖Φ_inf u‖ ≤ C_env * (1 + ‖u‖) ^ (3 / 2 : ℝ) * airyEnv u := by
    intro u
    let m : ℕ := ⌈‖u‖⌉₊
    have hu_m : u ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff]; linarith [Nat.le_ceil ‖u‖]
    have ht_pt : Tendsto (fun k => ‖Ψ_seq (φ k) u‖) atTop (𝓝 ‖Φ_inf u‖) :=
      ((hΦ_unif m).tendsto_at hu_m).norm
    have hev_bd : ∀ᶠ k in atTop,
        ‖Ψ_seq (φ k) u‖ ≤ C_env * (1 + ‖u‖) ^ (3 / 2 : ℝ) * airyEnv u := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hsp := hK_spec m (φ k) (hN k hk)
      have hR_dom : ‖u‖ + 2 ≤ R_dom (c'_seq (φ k)) := by
        have := Nat.le_ceil ‖u‖
        linarith [hsp.1]
      have hdisc := hankelI_disc_bound hC0 (hspec (φ k)).1 (hspec (φ k)).2.2.1 (u₀ := u) hR_dom
      calc ‖Ψ_seq (φ k) u‖
          ≤ 32 * Real.exp (5 / 2) * C_0 * (1 + ‖u‖) ^ (3 / 2 : ℝ) * airyEnv u := hdisc
        _ = C_env * (1 + ‖u‖) ^ (3 / 2 : ℝ) * airyEnv u := by dsimp [C_env]
    exact le_of_tendsto ht_pt hev_bd
  -- Real-valued on `ℝ`
  have hΦ_real : ∀ x : ℝ, (Φ_inf (x : ℂ)).im = 0 := by
    intro x
    let m : ℕ := ⌈|x|⌉₊
    have hx_m : (x : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      linarith [Nat.le_ceil |x|]
    have ht_im : Tendsto (fun k => (Ψ_seq (φ k) (x : ℂ)).im) atTop (𝓝 (Φ_inf (x : ℂ)).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp ((hΦ_unif m).tendsto_at hx_m)
    have hev0 : ∀ᶠ k in atTop, (Ψ_seq (φ k) (x : ℂ)).im = 0 := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hR := (hK_spec m (φ k) (hN k hk)).1
      have hx_dom : x ∈ Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k))) :=
        abs_le.mp ((Nat.le_ceil |x|).trans (by linarith))
      exact (hspec (φ k)).2.1 x hx_dom
    exact tendsto_nhds_unique ht_im (tendsto_const_nhds.congr' (hev0.mono fun _ hk => hk.symm))
  -- `L¹` integrability and symmetric-interval norm ≤ 1 on `ℝ`
  have hΦ_symm_norm : ∀ N : ℕ, ∫ x in (-N : ℝ)..(N : ℝ), ‖Φ_inf (x : ℂ)‖ ≤ 1 := by
    intro N
    refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
    obtain ⟨ε, hε, hεdef⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = ε₀ / 2 := ⟨ε₀ / 2, by positivity, rfl⟩
    have hε' : 0 < ε / (2 * (N : ℝ) + 1) := div_pos hε (by positivity)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif N) (ε / (2 * (N : ℝ) + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ ε := hδ_seq_lim (Iic_mem_nhds hε)
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq N))).and (hφ_atTop.eventually hev_δ)))
    let k := K₀
    obtain ⟨hk_unif, hk_K, hk_δ⟩ := hK₀ k le_rfl
    have hR := (hK_spec N (φ k) hk_K).1
    have hNR : (N : ℝ) ≤ R_dom (c'_seq (φ k)) := by linarith
    have hle : (-N : ℝ) ≤ (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
    have h_diff_ball : ∀ x ∈ Icc (-N : ℝ) (N : ℝ), (x : ℂ) ∈ closedBall (0 : ℂ) ((N : ℝ) + 1) := by
      intro x hx
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      linarith [abs_le.mpr hx]
    have h_pt_le : ∀ x ∈ Icc (-N : ℝ) (N : ℝ),
        ‖Φ_inf (x : ℂ)‖ ≤ ‖Ψ_seq (φ k) (x : ℂ)‖ + ε / (2 * (N : ℝ) + 1) := by
      intro x hx
      have hd := hk_unif (x : ℂ) (h_diff_ball x hx)
      rw [dist_eq_norm] at hd
      calc ‖Φ_inf (x : ℂ)‖ = ‖(Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)) + Ψ_seq (φ k) (x : ℂ)‖ := by ring_nf
        _ ≤ ‖Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)‖ + ‖Ψ_seq (φ k) (x : ℂ)‖ := norm_add_le _ _
        _ ≤ ε / (2 * (N : ℝ) + 1) + ‖Ψ_seq (φ k) (x : ℂ)‖ := add_le_add hd.le le_rfl
        _ = ‖Ψ_seq (φ k) (x : ℂ)‖ + ε / (2 * (N : ℝ) + 1) := add_comm _ _
    have hcΦ : ContinuousOn (fun x : ℝ => ‖Φ_inf (x : ℂ)‖) (Icc (-N : ℝ) (N : ℝ)) :=
      (hΦ_diff.continuous.comp continuous_ofReal).norm.continuousOn
    have hcΨ : ContinuousOn (fun x : ℝ => ‖Ψ_seq (φ k) (x : ℂ)‖)
        (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
      (((hspec (φ k)).1.continuousOn).comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx).norm
    have hsub_N : Icc (-N : ℝ) (N : ℝ) ⊆ Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k))) :=
      Icc_subset_Icc (by linarith) hNR
    have hiΦ := hcΦ.intervalIntegrable_of_Icc (μ := volume) hle
    have hiΨ_N := (hcΨ.mono hsub_N).intervalIntegrable_of_Icc (μ := volume) hle
    have hi_const : IntervalIntegrable (fun _ : ℝ => ε / (2 * (N : ℝ) + 1)) volume (-N : ℝ) (N : ℝ) :=
      intervalIntegrable_const
    have h_int1 : ∫ x in (-N : ℝ)..(N : ℝ), ‖Φ_inf (x : ℂ)‖ ≤
        ∫ x in (-N : ℝ)..(N : ℝ), (‖Ψ_seq (φ k) (x : ℂ)‖ + ε / (2 * (N : ℝ) + 1)) :=
      intervalIntegral.integral_mono_on hle hiΦ (hiΨ_N.add hi_const) h_pt_le
    rw [intervalIntegral.integral_add hiΨ_N hi_const, intervalIntegral.integral_const, smul_eq_mul] at h_int1
    have h_mono_R : ∫ x in (-N : ℝ)..(N : ℝ), ‖Ψ_seq (φ k) (x : ℂ)‖ ≤
        ∫ x in (-R_dom (c'_seq (φ k)))..(R_dom (c'_seq (φ k))), ‖Ψ_seq (φ k) (x : ℂ)‖ := by
      have hRR : -R_dom (c'_seq (φ k)) ≤ R_dom (c'_seq (φ k)) := by linarith
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hRR]
      exact setIntegral_mono_set
        ((hcΨ.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioc (by linarith) hNR hx)
    have hΨ_L1 := (hspec (φ k)).2.2.2.2.2.2.1
    have h_err : ((N : ℝ) - (-N : ℝ)) * (ε / (2 * (N : ℝ) + 1)) ≤ ε := by
      have h1 : (N : ℝ) - (-N : ℝ) = 2 * (N : ℝ) := by ring
      rw [h1, mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1)]
      nlinarith
    linarith
  have hΦ_int : Integrable (fun x : ℝ => Φ_inf (x : ℂ)) :=
    integrable_of_symmetric_interval_norm_le (hΦ_diff.continuous.comp continuous_ofReal) hΦ_symm_norm
  have hΦ_norm_int_le1 : ∫ x : ℝ, ‖Φ_inf (x : ℂ)‖ ≤ 1 := by
    have ht0 : Tendsto (fun t : ℝ => ∫ x in (-t)..t, ‖Φ_inf (x : ℂ)‖)
        atTop (𝓝 (∫ x : ℝ, ‖Φ_inf (x : ℂ)‖)) :=
      intervalIntegral_tendsto_integral hΦ_int.norm tendsto_neg_atTop_atBot tendsto_id
    have hcast : Tendsto (fun N : ℕ => ∫ x in (-(N : ℝ))..(N : ℝ), ‖Φ_inf (x : ℂ)‖)
        atTop (𝓝 (∫ x : ℝ, ‖Φ_inf (x : ℂ)‖)) :=
      ht0.comp tendsto_natCast_atTop_atTop
    exact le_of_tendsto hcast (Eventually.of_forall hΦ_symm_norm)
  -- Nonnegativity on `(-∞, a₁]`
  have hΦ_pos_a1 : ∀ x : ℝ, x ≤ a₁ → 0 ≤ (Φ_inf (x : ℂ)).re := by
    intro x hx
    let m : ℕ := ⌈|x|⌉₊
    have hx_m : (x : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [Nat.le_ceil |x|]
    have ht_re : Tendsto (fun k => (Ψ_seq (φ k) (x : ℂ)).re) atTop (𝓝 (Φ_inf (x : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp ((hΦ_unif m).tendsto_at hx_m)
    have hev : ∀ᶠ k in atTop, -δ_lobe (c'_seq (φ k)) ≤ (Ψ_seq (φ k) (x : ℂ)).re := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hR := (hK_spec m (φ k) (hN k hk)).1
      have hx_lo : -R_dom (c'_seq (φ k)) ≤ x := by linarith [(abs_le.mp (Nat.le_ceil |x|)).1]
      have hx_hi : x ≤ uT_seq (φ k) := hx.trans (hspec (φ k)).2.2.2.1.le
      exact (hspec (φ k)).2.2.2.2.2.1 x ⟨hx_lo, hx_hi⟩
    have hδt : Tendsto (fun k => -δ_lobe (c'_seq (φ k))) atTop (𝓝 0) := by
      simpa using (hδ_seq_lim.comp hφ_atTop).neg
    exact le_of_tendsto_of_tendsto hδt ht_re hev
  -- Nonpositive total integral `∫_ℝ (Φ_inf x).re ≤ 0`
  have hΦ_total_int_le : ∫ x : ℝ, (Φ_inf (x : ℂ)).re ≤ 0 := by
    have h_symm_re : ∀ N : ℕ, ⌈|a₁|⌉₊ + 1 ≤ N →
        ∫ x in (-N : ℝ)..(N : ℝ), (Φ_inf (x : ℂ)).re ≤ (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * N) := by
      intro N hN_ge
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hε' : 0 < (ε / 2) / (2 * (N : ℝ) + 1) := div_pos (half_pos hε) (by positivity)
      have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif N) ((ε / 2) / (2 * (N : ℝ) + 1)) hε'
      have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ ε / 2 :=
        hδ_seq_lim (Iic_mem_nhds (half_pos hε))
      obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
        (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq N))).and (hφ_atTop.eventually hev_δ)))
      let k := K₀
      obtain ⟨hk_unif, hk_K, hk_δ⟩ := hK₀ k le_rfl
      have hsp := hK_spec N (φ k) hk_K
      have hNR : (N : ℝ) ≤ R_dom (c'_seq (φ k)) := by linarith [hsp.1]
      have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (by omega) hN_ge
      have hNa1 : |a₁| + 1 ≤ (N : ℝ) := by
        have := Nat.le_ceil |a₁|
        have : (⌈|a₁|⌉₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN_ge
        linarith
      have hN_uT : -(N : ℝ) ≤ uT_seq (φ k) := by
        have := (abs_le.mp (le_refl |a₁|)).1
        linarith [(hspec (φ k)).2.2.2.1]
      obtain ⟨hAn_k, hReal_k, hEnv_k, huT_gt_k, huT_le_k, hPos_k, hL1_k, hTail_k, hTop_k, hFail_k⟩ :=
        hspec (φ k)
      have h_top := hTop_k (N : ℝ) ⟨by positivity, hNR⟩ hN_uT
      have hcΨ_dom : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
          (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
        hAn_k.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx
      have hcΨ_re : ContinuousOn (fun x : ℝ => (Ψ_seq (φ k) (x : ℂ)).re)
          (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
        Complex.continuous_re.comp_continuousOn hcΨ_dom
      have h_int_split :
          (∫ x in (-N : ℝ)..(N : ℝ), (Ψ_seq (φ k) (x : ℂ)).re) +
            (∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), (Ψ_seq (φ k) (x : ℂ)).re) =
          ∫ x in (-N : ℝ)..(R_dom (c'_seq (φ k))), (Ψ_seq (φ k) (x : ℂ)).re := by
        refine intervalIntegral.integral_add_adjacent_intervals ?_ ?_
        · exact (hcΨ_re.mono (Icc_subset_Icc (by linarith) hNR)).intervalIntegrable_of_Icc
            (by linarith [show (0 : ℝ) ≤ N by positivity])
        · exact (hcΨ_re.mono (Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable_of_Icc hNR
      have h_env_pos : ∀ x : ℝ, 1 ≤ x → x ≤ R_dom (c'_seq (φ k)) →
          ‖Ψ_seq (φ k) (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := fun x hx1 hxR =>
        hankelI_pos_real_env hC0 hEnv_k hx1 hxR
      have h_tail_re : -(∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), (Ψ_seq (φ k) (x : ℂ)).re) ≤
          (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * N) := by
        have h_abs_int : ‖∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), (Ψ_seq (φ k) (x : ℂ)).re‖ ≤
            ∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), ‖(Ψ_seq (φ k) (x : ℂ)).re‖ :=
          intervalIntegral.norm_integral_le_integral_norm hNR
        have h_le_c : ∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), ‖(Ψ_seq (φ k) (x : ℂ)).re‖ ≤
            ∫ x in (N : ℝ)..(R_dom (c'_seq (φ k))), ‖Ψ_seq (φ k) (x : ℂ)‖ := by
          refine intervalIntegral.integral_mono_on hNR
            ((continuous_norm.comp_continuousOn (hcΨ_re.mono (Icc_subset_Icc (by linarith) le_rfl))).intervalIntegrable_of_Icc hNR)
            ((continuous_norm.comp_continuousOn (hcΨ_dom.mono (Icc_subset_Icc (by linarith) le_rfl))).intervalIntegrable_of_Icc hNR)
            fun x _ => ?_
          simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (Ψ_seq (φ k) (x : ℂ))
        have h_norm_tail := hankelI_pos_real_norm_tail_le hC0 h1N hNR
          (hcΨ_dom.mono (Icc_subset_Icc (by linarith) le_rfl)) h_env_pos
        rw [Real.norm_eq_abs] at h_abs_int
        have h1 := (abs_le.mp h_abs_int).1
        linarith
      have h_pt_diff : ∀ x ∈ Icc (-N : ℝ) (N : ℝ),
          (Φ_inf (x : ℂ)).re ≤ (Ψ_seq (φ k) (x : ℂ)).re + (ε / 2) / (2 * (N : ℝ) + 1) := by
        intro x hx
        have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) ((N : ℝ) + 1) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [abs_le.mpr hx]
        have hd := (hk_unif (x : ℂ) hx_ball).le
        rw [dist_eq_norm] at hd
        have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd)).2
        simp only [Complex.sub_re] at hre
        linarith
      have hle : (-N : ℝ) ≤ (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
      have hiΦ_re : IntervalIntegrable (fun x : ℝ => (Φ_inf (x : ℂ)).re) volume (-N : ℝ) (N : ℝ) :=
        (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal)).intervalIntegrable _ _
      have hiΨ_N : IntervalIntegrable (fun x : ℝ => (Ψ_seq (φ k) (x : ℂ)).re) volume (-N : ℝ) (N : ℝ) :=
        (hcΨ_re.mono (Icc_subset_Icc (by linarith) hNR)).intervalIntegrable_of_Icc hle
      have h_int_Φ := intervalIntegral.integral_mono_on hle hiΦ_re (hiΨ_N.add intervalIntegrable_const) h_pt_diff
      rw [intervalIntegral.integral_add hiΨ_N intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul] at h_int_Φ
      have h_err : ((N : ℝ) - (-N : ℝ)) * ((ε / 2) / (2 * (N : ℝ) + 1)) ≤ ε / 2 := by
        rw [show (N : ℝ) - (-N : ℝ) = 2 * (N : ℝ) by ring, mul_div_assoc',
          div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1)]
        nlinarith
      linarith
    have ht0 : Tendsto (fun t : ℝ => ∫ x in (-t)..t, (Φ_inf (x : ℂ)).re)
        atTop (𝓝 (∫ x : ℝ, (Φ_inf (x : ℂ)).re)) :=
      intervalIntegral_tendsto_integral hΦ_int.re tendsto_neg_atTop_atBot tendsto_id
    have ht := ht0.comp tendsto_natCast_atTop_atTop
    have h_exp_tend : Tendsto (fun N : ℕ => (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * (N : ℝ)))
        atTop (𝓝 0) := by
      have ht_mul : Tendsto (fun N : ℕ => -(5 / 6 : ℝ) * (N : ℝ)) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by norm_num : -(5 / 6 : ℝ) < 0) tendsto_natCast_atTop_atTop
      simpa using ((Real.tendsto_exp_atBot.comp ht_mul).const_mul ((6 / 5 : ℝ) * C_0))
    exact le_of_tendsto_of_tendsto ht h_exp_tend (eventually_atTop.mpr ⟨⌈|a₁|⌉₊ + 1, h_symm_re⟩)
  -- Non-vanishing via negative mass `1/4 ≤ ∫_{a₁}^{U₀} max 0 (-(Φ_inf x).re)`
  have hΦ_neg_mass : (1 / 4 : ℝ) ≤ ∫ x in a₁..U₀, max 0 (-(Φ_inf (x : ℂ)).re) := by
    have ha1_lt_U0 : a₁ ≤ U₀ := by linarith [hU0_ge1]
    let m₀ : ℕ := ⌈max |a₁| U₀⌉₊
    have hm0_ge : max |a₁| U₀ ≤ (m₀ : ℝ) := Nat.le_ceil _
    have hΦ_m_cont : ContinuousOn (fun x : ℝ => max 0 (-(Φ_inf (x : ℂ)).re)) (Icc a₁ U₀) :=
      ContinuousOn.sup continuousOn_const
        (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal)).neg.continuousOn
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < (ε / 2) / (U₀ - a₁ + 1) := div_pos (half_pos hε) (by linarith)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif m₀) ((ε / 2) / (U₀ - a₁ + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ min (1 / 4) (ε / 2) :=
      hδ_seq_lim (Iic_mem_nhds (lt_min (by norm_num) (half_pos hε)))
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq m₀))).and (hφ_atTop.eventually hev_δ)))
    let k := K₀
    obtain ⟨hk_unif, hk_K, hk_δ⟩ := hK₀ k le_rfl
    have hsp := hK_spec m₀ (φ k) hk_K
    obtain ⟨hAn_k, hReal_k, hEnv_k, huT_gt_k, huT_le_k, hPos_k, hL1_k, hTail_k, hTop_k, hFail_k⟩ :=
      hspec (φ k)
    have h_env_pos : ∀ x : ℝ, 1 ≤ x → x ≤ R_dom (c'_seq (φ k)) →
        ‖Ψ_seq (φ k) (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := fun x hx1 hxR =>
      hankelI_pos_real_env hC0 hEnv_k hx1 hxR
    have huT_le_U0 : uT_seq (φ k) ≤ U₀ := by
      have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
      have ha1_le_R : -R_dom (c'_seq (φ k)) ≤ a₁ := by
        linarith [(abs_le.mp ((le_max_left |a₁| U₀).trans hm0_ge)).1]
      have hcΨ_dom : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
          (Icc (uT_seq (φ k)) (R_dom (c'_seq (φ k)))) :=
        hAn_k.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hx.1, huT_gt_k], hx.2⟩
      exact hankelI_uT_le hC0 hsp.2.2.1 huT_le_k hcΨ_dom h_env_pos hTail_k
    have hU0_le_R : U₀ ≤ R_dom (c'_seq (φ k)) := hsp.2.2.2
    have hcΨ_a1R : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
        (Icc a₁ (R_dom (c'_seq (φ k)))) :=
      hAn_k.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
        have ha1_le_R : -R_dom (c'_seq (φ k)) ≤ a₁ := by
          linarith [(abs_le.mp ((le_max_left |a₁| U₀).trans hm0_ge)).1]
        exact abs_le.mpr ⟨ha1_le_R.trans hx.1, hx.2⟩
    have hcΨ_U0R : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ)) (Icc U₀ (R_dom (c'_seq (φ k)))) :=
      hcΨ_a1R.mono (Icc_subset_Icc_left ha1_lt_U0)
    have h_tail_q : ∫ x in U₀..(R_dom (c'_seq (φ k))), max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) < 1 / 4 :=
      hankelI_pos_real_tail_lt_quarter hC0 le_rfl hU0_le_R hcΨ_U0R h_env_pos
    have h_m_cont_all : ContinuousOn (fun x : ℝ => max 0 (-(Ψ_seq (φ k) (x : ℂ)).re))
        (Icc a₁ (R_dom (c'_seq (φ k)))) :=
      ContinuousOn.sup continuousOn_const (Complex.continuous_re.comp_continuousOn hcΨ_a1R).neg
    have h_split := intervalIntegral.integral_add_adjacent_intervals
      ((h_m_cont_all.mono (Icc_subset_Icc huT_gt_k.le hU0_le_R)).intervalIntegrable_of_Icc
        (μ := volume) huT_le_U0)
      ((h_m_cont_all.mono (Icc_subset_Icc_left ha1_lt_U0)).intervalIntegrable_of_Icc
        (μ := volume) hU0_le_R)
    have h_uT_U0 : ∫ x in (uT_seq (φ k))..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
        ∫ x in a₁..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      rw [intervalIntegral.integral_of_le huT_le_U0, intervalIntegral.integral_of_le ha1_lt_U0]
      exact setIntegral_mono_set
        (((h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).integrableOn_Icc (μ := volume)).mono_set
          Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => le_max_left _ _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioc_left huT_gt_k.le hx)
    have h_Ψ_band : 1 / 4 - ε / 2 ≤ ∫ x in a₁..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      have h2 : δ_lobe (c'_seq (φ k)) ≤ ε / 2 := hk_δ.trans (min_le_right _ _)
      linarith
    have h_pt_m : ∀ x ∈ Icc a₁ U₀,
        max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
          max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - a₁ + 1) := by
      intro x hx
      have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) ((m₀ : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hax : |x| ≤ max |a₁| U₀ := by
          rcases le_total x 0 with hx0 | hx0
          · rw [abs_of_nonpos hx0]
            calc -x ≤ -a₁ := neg_le_neg hx.1
              _ ≤ |a₁| := neg_le_abs a₁
              _ ≤ max |a₁| U₀ := le_max_left _ _
          · rw [abs_of_nonneg hx0]
            exact hx.2.trans (le_max_right _ _)
        linarith [hax.trans hm0_ge]
      have hd := (hk_unif (x : ℂ) hx_ball).le
      rw [dist_eq_norm] at hd
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd)).2
      simp only [Complex.sub_re] at hre
      have hneg : -(Ψ_seq (φ k) (x : ℂ)).re ≤ -(Φ_inf (x : ℂ)).re + (ε / 2) / (U₀ - a₁ + 1) := by linarith
      have h0_le : (0 : ℝ) ≤ max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - a₁ + 1) :=
        add_nonneg (le_max_left _ _) (div_nonneg (half_pos hε).le (by linarith))
      exact max_le h0_le (hneg.trans (add_le_add (le_max_right _ _) le_rfl))
    have h_m_int_Ψ := (h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).intervalIntegrable_of_Icc
      (μ := volume) ha1_lt_U0
    have h_m_int_Φ := hΦ_m_cont.intervalIntegrable_of_Icc (μ := volume) ha1_lt_U0
    have h_int_m := intervalIntegral.integral_mono_on ha1_lt_U0 h_m_int_Ψ
      (h_m_int_Φ.add intervalIntegrable_const) h_pt_m
    rw [intervalIntegral.integral_add h_m_int_Φ intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h_int_m
    have h_err : (U₀ - a₁) * ((ε / 2) / (U₀ - a₁ + 1)) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hΦ_ne : ∃ z : ℂ, Φ_inf z ≠ 0 := by
    by_contra h_all0
    push Not at h_all0
    have h0 : ∫ x in a₁..U₀, max 0 (-(Φ_inf (x : ℂ)).re) = 0 := by
      simp [h_all0]
    linarith [hΦ_neg_mass]
  -- Apply `airy_sign_equality` (`AiryCftSignEqualityMain.lean`)
  obtain ⟨c_eq, hc_eq_neg, hΦ_eq_ext, _⟩ :=
    airy_sign_equality hΦ_diff hΦ_int hC_env_nn hΦ_env hΦ_real hΦ_pos_a1 hΦ_total_int_le hΦ_ne
  let c_lim : ℝ := -c_eq
  have hc_lim_pos : 0 < c_lim := by dsimp [c_lim]; linarith
  have hc_lim_hi : c_lim ≤ quantC1C_hi := by
    have hint_eq : ∫ x : ℝ, ‖Φ_inf (x : ℂ)‖ = c_lim * quantC1Mass := by
      have hfn : (fun x : ℝ => ‖Φ_inf (x : ℂ)‖) = (fun x : ℝ => c_lim * ‖airyExtremal (x : ℂ)‖) := by
        ext x
        rw [hΦ_eq_ext (x : ℂ), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_lim_pos]
      rw [hfn, integral_const_mul]; rfl
    rw [hint_eq] at hΦ_norm_int_le1
    unfold quantC1C_hi
    rw [← one_div, le_div_iff₀ quantC1Mass_pos]
    linarith
  have hc_lim_lo : quantC1C_lo ≤ c_lim := by
    have h_eq_max : ∫ x in a₁..U₀, max 0 (-(Φ_inf (x : ℂ)).re) =
        c_lim * ∫ x in a₁..U₀, max 0 (-(airyExtremal (x : ℂ)).re) := by
      have hfn : (fun x : ℝ => max 0 (-(Φ_inf (x : ℂ)).re)) =
          (fun x : ℝ => c_lim * max 0 (-(airyExtremal (x : ℂ)).re)) := by
        ext x
        rw [hΦ_eq_ext (x : ℂ), Complex.re_ofReal_mul]
        rcases le_total 0 (-(airyExtremal (x : ℂ)).re) with hnn | hnp
        · have hnn2 : 0 ≤ c_lim * (-(airyExtremal (x : ℂ)).re) := mul_nonneg hc_lim_pos.le hnn
          rw [show -(c_lim * (airyExtremal (x : ℂ)).re) = c_lim * (-(airyExtremal (x : ℂ)).re) by ring,
            max_eq_right hnn2, max_eq_right hnn]
        · have hnp2 : c_lim * (-(airyExtremal (x : ℂ)).re) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hc_lim_pos.le hnp
          rw [show -(c_lim * (airyExtremal (x : ℂ)).re) = c_lim * (-(airyExtremal (x : ℂ)).re) by ring,
            max_eq_left hnp2, max_eq_left hnp, mul_zero]
      rw [hfn, intervalIntegral.integral_const_mul]
    have ha1_lt_U0 : a₁ ≤ U₀ := by linarith [hU0_ge1]
    have h_band_le_Ioi : ∫ x in a₁..U₀, max 0 (-(airyExtremal (x : ℂ)).re) ≤ quantC1Mass / 2 := by
      rw [← integral_Ioi_airyExtremal_max_neg, intervalIntegral.integral_of_le ha1_lt_U0]
      refine setIntegral_mono_set ?_ (Eventually.of_forall fun _ => le_max_left _ _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioi_self hx)
      refine (airyExtremal_integrable.norm.mono' ?_ ?_).integrableOn
      · exact (continuous_const.max (Complex.continuous_re.comp
          (differentiable_airyExtremal.continuous.comp continuous_ofReal)).neg).aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        exact max_le (norm_nonneg _)
          ((neg_le.mp (abs_le.mp (Complex.abs_re_le_norm (airyExtremal (x : ℂ)))).1).trans (le_refl _))
    have h_prod_ge : 1 / 4 ≤ c_lim * (quantC1Mass / 2) := by
      have := mul_le_mul_of_nonneg_left h_band_le_Ioi hc_lim_pos.le
      linarith
    unfold quantC1C_lo
    rw [inv_le_iff_one_le_mul₀ (mul_pos two_pos quantC1Mass_pos)]
    linarith
  -- Step A: eventually `uT_seq (φ k) - a₁ ≤ min δ_star (min η₀ 1)`
  let δ_star : ℝ := quantC1DeltaStar
  let x₀ : ℝ := a₁ + δ_star / 2
  have hx0_gt : a₁ < x₀ := by dsimp [x₀]; linarith [quantC1DeltaStar_pos]
  have hx0_neg : (Φ_inf (x₀ : ℂ)).re < 0 := by
    have hai_ne : airyAi x₀ ≠ 0 := by
      intro h0
      have hc0 : airyAiC (x₀ : ℂ) = 0 := by rw [airyAiC_ofReal, h0]; simp
      obtain ⟨n, hn, hnx⟩ := (airyAiC_eq_zero_iff (x₀ : ℂ)).mp hc0
      have hx_eq : x₀ = airyZero n := Complex.ofReal_injective hnx
      have h_le_a1 : airyZero n ≤ a₁ := by
        clear hnx hx_eq
        induction hn with
        | refl => exact le_rfl
        | step hm ih => exact (airyZero_strictAnti hm).le.trans ih
      linarith
    rw [hΦ_eq_ext (x₀ : ℂ), Complex.re_ofReal_mul, airyExtremal_re]
    have hdiv : 0 < airyAi x₀ ^ 2 / (x₀ - a₁) := div_pos (sq_pos_of_ne_zero hai_ne) (by linarith)
    nlinarith
  have hev_uT : ∀ᶠ k in atTop, uT_seq (φ k) - a₁ ≤ min δ_star (min quantC1Eta0 1) := by
    let m₀ : ℕ := ⌈|x₀|⌉₊
    have hx0_m : (x₀ : ℂ) ∈ closedBall (0 : ℂ) ((m₀ : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [Nat.le_ceil |x₀|]
    have ht_x0 : Tendsto (fun k => (Ψ_seq (φ k) (x₀ : ℂ)).re) atTop (𝓝 (Φ_inf (x₀ : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp ((hΦ_unif m₀).tendsto_at hx0_m)
    have ht_sum : Tendsto (fun k => (Ψ_seq (φ k) (x₀ : ℂ)).re + δ_lobe (c'_seq (φ k))) atTop
        (𝓝 ((Φ_inf (x₀ : ℂ)).re + 0)) := ht_x0.add (hδ_seq_lim.comp hφ_atTop)
    have hev_neg : ∀ᶠ k in atTop, (Ψ_seq (φ k) (x₀ : ℂ)).re + δ_lobe (c'_seq (φ k)) < 0 :=
      ht_sum (Iio_mem_nhds (by linarith [hx0_neg]))
    have hev_K : ∀ᶠ k in atTop, K_seq m₀ ≤ φ k := hφ_atTop.eventually (eventually_ge_atTop (K_seq m₀))
    filter_upwards [hev_neg, hev_K] with k hk_neg hk_K
    have hmin_eq : min δ_star (min quantC1Eta0 1) = δ_star := by
      refine le_antisymm (min_le_left _ _) (le_min le_rfl (le_min le_rfl ?_))
      exact quantC1DeltaStar_le.trans (by norm_num)
    rw [hmin_eq]
    by_contra h_gt
    push Not at h_gt
    have hx0_uT : x₀ ≤ uT_seq (φ k) := by dsimp [x₀]; linarith [quantC1DeltaStar_pos]
    have hR := (hK_spec m₀ (φ k) hk_K).1
    have hx0_lo : -R_dom (c'_seq (φ k)) ≤ x₀ := by linarith [(abs_le.mp (Nat.le_ceil |x₀|)).1]
    have hp := (hspec (φ k)).2.2.2.2.2.1 x₀ ⟨hx0_lo, hx0_uT⟩
    linarith
  -- Step B: eventually `deriv (Ψ_seq (φ k))` obeys `QuantC1B2Holds` on `[a₁ - δ_star, a₁ + δ_star]`
  have hev_deriv : ∀ᶠ k in atTop,
      ∀ x ∈ Icc (a₁ - δ_star) (a₁ + δ_star),
        ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖ ≤ quantC1C1 ∧
        (deriv (Ψ_seq (φ k)) (x : ℂ)).re ≤ -2 * quantC1KappaStar := by
    let m₁ : ℕ := ⌈|a₁| + 2⌉₊
    have hm1_ge : |a₁| + 2 ≤ (m₁ : ℝ) := Nat.le_ceil _
    let ε_d : ℝ := min 1 (2 * quantC1KappaStar)
    have hε_d_pos : 0 < ε_d := lt_min one_pos (mul_pos two_pos quantC1KappaStar_pos)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif m₁) ε_d hε_d_pos
    have hev_K : ∀ᶠ k in atTop, K_seq m₁ ≤ φ k := hφ_atTop.eventually (eventually_ge_atTop (K_seq m₁))
    filter_upwards [h_unif, hev_K] with k hk_unif hk_K
    intro x hx
    have h_ball_sub : closedBall (x : ℂ) 1 ⊆ closedBall (0 : ℂ) ((m₁ : ℝ) + 1) := fun z hz => by
      rw [mem_closedBall_zero_iff]
      rw [mem_closedBall, dist_eq_norm] at hz
      have hx_abs : |x| ≤ |a₁| + δ_star := by
        have hsub : |x - a₁| ≤ δ_star := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        calc |x| = |(x - a₁) + a₁| := by ring_nf
          _ ≤ |x - a₁| + |a₁| := abs_add_le _ _
          _ ≤ |a₁| + δ_star := by linarith
      calc ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + |x| := add_le_add hz (by rw [Complex.norm_real, Real.norm_eq_abs])
        _ ≤ (m₁ : ℝ) + 1 := by linarith [quantC1DeltaStar_le]
    have h_diff_holo : DiffContOnCl ℂ (fun z => Ψ_seq (φ k) z - Φ_inf z) (ball (x : ℂ) 1) := by
      have h_Φ_an : AnalyticOnNhd ℂ Φ_inf (closedBall (0 : ℂ) ((m₁ : ℝ) + 1)) :=
        ((analyticOnNhd_iff_differentiableOn isOpen_univ).mpr hΦ_diff.differentiableOn).mono
          (subset_univ _)
      have h_sub_an : AnalyticOnNhd ℂ (fun z => Ψ_seq (φ k) z - Φ_inf z)
          (closedBall (0 : ℂ) ((m₁ : ℝ) + 1)) :=
        ((hAn_seq m₁ (φ k) hk_K).mono (closedBall_subset_closedBall (by linarith))).sub h_Φ_an
      exact ⟨(h_sub_an.differentiableOn.mono (ball_subset_closedBall.trans h_ball_sub)),
        (h_sub_an.mono h_ball_sub).continuousOn.mono closure_ball_subset_closedBall⟩
    have hS : ∀ z ∈ sphere (x : ℂ) 1, ‖Ψ_seq (φ k) z - Φ_inf z‖ ≤ ε_d := fun z hz => by
      have hd := (hk_unif z (h_ball_sub (sphere_subset_closedBall hz))).le
      rw [dist_eq_norm, norm_sub_rev] at hd
      exact hd
    have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos h_diff_holo hS
    rw [div_one] at h_cauchy
    have h_deriv_sub : deriv (fun z => Ψ_seq (φ k) z - Φ_inf z) (x : ℂ) =
        deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ) := by
      have h1 : DifferentiableAt ℂ (Ψ_seq (φ k)) (x : ℂ) :=
        (hAn_seq m₁ (φ k) hk_K (x : ℂ)
          (closedBall_subset_closedBall (by linarith) (h_ball_sub (mem_closedBall_self zero_le_one)))).differentiableAt
      exact deriv_sub h1 (hΦ_diff (x : ℂ))
    rw [h_deriv_sub] at h_cauchy
    have hΦ_deriv_eq : deriv Φ_inf (x : ℂ) = (c_lim : ℂ) * deriv airyExtremal (x : ℂ) := by
      have heq_fun : Φ_inf = fun u => (c_lim : ℂ) * airyExtremal u := funext hΦ_eq_ext
      rw [heq_fun]
      exact ((differentiable_airyExtremal (x : ℂ)).hasDerivAt.const_mul (c_lim : ℂ)).deriv
    have h_ext_sp := quantC1DeltaStar_spec.2.2 x hx
    refine ⟨?_, ?_⟩
    · have hΦ_norm : ‖deriv Φ_inf (x : ℂ)‖ ≤ 2 * quantC1C_hi * airyAi' (airyZero 1) ^ 2 := by
        rw [hΦ_deriv_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc_lim_pos]
        calc c_lim * ‖deriv airyExtremal (x : ℂ)‖ ≤ quantC1C_hi * (2 * airyAi' (airyZero 1) ^ 2) :=
              mul_le_mul hc_lim_hi h_ext_sp.2 (norm_nonneg _) quantC1C_hi_pos.le
          _ = 2 * quantC1C_hi * airyAi' (airyZero 1) ^ 2 := by ring
      have h_tri : ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖ ≤ ‖deriv Φ_inf (x : ℂ)‖ + ε_d := by
        calc ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖
            = ‖(deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)) + deriv Φ_inf (x : ℂ)‖ := by ring_nf
          _ ≤ ‖deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)‖ + ‖deriv Φ_inf (x : ℂ)‖ := norm_add_le _ _
          _ ≤ ε_d + ‖deriv Φ_inf (x : ℂ)‖ := add_le_add h_cauchy le_rfl
          _ = ‖deriv Φ_inf (x : ℂ)‖ + ε_d := add_comm _ _
      have hε1 : ε_d ≤ 1 := min_le_left _ _
      unfold quantC1C1
      linarith [mul_pos quantC1C_hi_pos airyAi'_a1_sq_pos]
    · have hΦ_re : (deriv Φ_inf (x : ℂ)).re ≤ -4 * quantC1KappaStar := by
        rw [hΦ_deriv_eq, Complex.re_ofReal_mul]
        have hneg : c_lim * (deriv airyExtremal (x : ℂ)).re ≤ c_lim * (-(airyAi' (airyZero 1) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h_ext_sp.1 hc_lim_pos.le
        have hlo : c_lim * (-(airyAi' (airyZero 1) ^ 2) / 2) ≤
            quantC1C_lo * (-(airyAi' (airyZero 1) ^ 2) / 2) := by
          nlinarith [hc_lim_lo, airyAi'_a1_sq_pos]
        have heq_k : quantC1C_lo * (-(airyAi' (airyZero 1) ^ 2) / 2) = -4 * quantC1KappaStar := by
          unfold quantC1KappaStar; ring
        linarith
      have h_re_diff : (deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)).re ≤ ε_d :=
        (abs_le.mp ((Complex.abs_re_le_norm _).trans h_cauchy)).2
      simp only [Complex.sub_re] at h_re_diff
      have hεk : ε_d ≤ 2 * quantC1KappaStar := min_le_right _ _
      linarith
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hev_uT.and hev_deriv)
  exact (hspec (φ k)).2.2.2.2.2.2.2.2.2 ⟨(hk k le_rfl).1, (hk k le_rfl).2⟩

/-- info: 'FormalResearch.SignUncertainty.hankelI_disc_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelI_disc_bound

/-- info: 'FormalResearch.SignUncertainty.hankel_quant_c1_typeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_quant_c1_typeI

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.HankelBootBandGen
public import FormalResearch.SignUncertainty.HankelQuantC1Feasible

/-!
# Multilevel `TE.0'` for `ShellHBData` (`HankelQuantC1Multilevel`)

Generalizes `HankelQuantC1` / `HankelQuantC1Feasible` (`gt:7.7p` (d), `teb:quant_c1_hb`) from
`a₁` / `airyExtremal` to arbitrary `D : ShellHBData` with prescribed sites `D.S.erase D.tm`,
offsets bounded by `R_off ≥ 0`, and any upper cap `η_cap > 0` on `u_T - D.tm`.

Closes the blowup compactness limit `Φ_∞` using `D.uniqueness` (`lem:hb-uniqueness`) and
yields `QuantC1MultilevelB2Holds D δ_star κ_star C1 Ψ u_T` with constants `(δ_star, κ_star, C1)`
depending only on `D` (not on `c`, `ε`, `T`, `r`, `f`, or `η_cap`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BoundedContinuousFunction

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

/-! ### Private Arzelà–Ascoli and integrability helpers (as in `HankelQuantC1`) -/

private lemma ml_pos_real_norm_tail_le
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
      unfold airyEnv; rw [hcpow32]; exact Real.exp_le_exp.mpr (by linarith)
    calc ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := hΨ_env x hx_ge1 hx.2
      _ ≤ C_0 * Real.exp (-(5 / 6 : ℝ) * x) := by gcongr
      _ = f_env x := rfl
  have hint_le : ∫ x in A..B, ‖Ψ (x : ℂ)‖ ≤ ∫ x in A..B, f_env x :=
    intervalIntegral.integral_mono_on hAB hnorm_int hf_int hpt
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => -(6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * t)) (f_env x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -(5 / 6 : ℝ) * t) (-(5 / 6 : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-(5 / 6 : ℝ))
    have h2 := (Real.hasDerivAt_exp (-(5 / 6 : ℝ) * x)).comp x h1
    have h3 := h2.const_mul (-(6 / 5 : ℝ) * C_0)
    refine h3.congr_deriv ?_
    dsimp [f_env]; ring
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hf_int
  have hB_nn : 0 ≤ (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * B) := by positivity
  linarith

private lemma ml_pos_real_tail_lt_quarter
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
  have htail := ml_pos_real_norm_tail_le hC0 h1_le_A hAB hΨ_cont hΨ_env
  have hexp_A : Real.exp (-(5 / 6 : ℝ) * A) ≤ (5 * C_0 + 1)⁻¹ := by
    rw [show -(5 / 6 : ℝ) * A = -((5 / 6 : ℝ) * A) by ring, Real.exp_neg,
      ← Real.exp_log hlog_pos, inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hmain : (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * A) ≤ (6 / 5 : ℝ) * C_0 * (5 * C_0 + 1)⁻¹ := by
    gcongr
  have hlt : (6 / 5 : ℝ) * C_0 * (5 * C_0 + 1)⁻¹ < 1 / 4 := by rw [mul_inv_lt_iff₀ hlog_pos]; linarith
  linarith

private lemma ml_uT_le {Ψ : ℂ → ℂ} {C_0 R u_T δ : ℝ}
    (hC0 : 0 < C_0) (hδ_le : δ ≤ 1 / 4) (huT_le : u_T ≤ R)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc u_T R))
    (hΨ_env : ∀ x : ℝ, 1 ≤ x → x ≤ R → ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ))
    (htail : (1 / 2 : ℝ) - δ ≤ ∫ x in u_T..R, max 0 (-(Ψ (x : ℂ)).re)) :
    u_T ≤ quantC1_U0 C_0 := by
  by_contra hlt
  push Not at hlt
  have hq := ml_pos_real_tail_lt_quarter hC0 hlt.le huT_le hΨ_cont hΨ_env
  linarith

private lemma ml_arzela_ascoli_single_ball
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
    rintro f x ⟨n, hn⟩; subst hn; dsimp [bcf]
    split_ifs with hn
    · rw [mem_closedBall_zero_iff]; exact hBd n hn x.1 (closedBall_subset_closedBall (by linarith) x.2)
    · rw [mem_closedBall_zero_iff, FunLike.coe_zero, Pi.zero_apply, norm_zero]; exact hM
  have heq : Equicontinuous (fun f : Set.range bcf => (f.1 : X → ℂ)) := by
    intro x₀; rw [Metric.equicontinuousAt_iff_pair]; intro ε hε
    refine ⟨ball x₀ (ε / (2 * (M + 1))), Metric.ball_mem_nhds x₀ (div_pos hε (by linarith)),
      fun y hy z hz ⟨f, hf⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hf; dsimp [bcf]
    split_ifs with hn
    · change dist (F n y.1) (F n z.1) < ε; rw [dist_eq_norm]
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
        _ < (M + 1) * (ε / (M + 1)) := by have : 0 < ε / (M + 1) := div_pos hε (by linarith); nlinarith
        _ = ε := by field_simp [(by linarith : M + 1 ≠ 0)]
    · simp only [FunLike.coe_zero, Pi.zero_apply, dist_self]; exact hε
  have hcomp : IsCompact (closure (Set.range bcf)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall 0 M)
      (Set.range bcf) hin_s heq
  obtain ⟨g₀, -, ψ, hψ_mono, hψ_tend⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  let g : ℂ → ℂ := fun z => if hz : z ∈ X then g₀ ⟨z, hz⟩ else 0
  refine ⟨ψ, g, hψ_mono, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  rw [Metric.tendsto_atTop] at hψ_tend
  obtain ⟨K, hK⟩ := hψ_tend ε hε
  filter_upwards [Filter.eventually_ge_atTop (max K N₀)] with k hk z hz
  have hkK : K ≤ k := (le_max_left K N₀).trans hk
  have hψN : N₀ ≤ ψ k := (le_max_right K N₀).trans (hk.trans (hψ_mono.id_le k))
  have hg_eq : g z = g₀ ⟨z, hz⟩ := by dsimp only [g]; split_ifs with h; rfl; exact absurd hz h
  have hbcf_eq : bcf (ψ k) ⟨z, hz⟩ = F (ψ k) z := by dsimp [bcf]; simp [hψN]
  calc dist (g z) (F (ψ k) z) = dist (bcf (ψ k) ⟨z, hz⟩) (g₀ ⟨z, hz⟩) := by rw [hg_eq, hbcf_eq, dist_comm]
    _ ≤ dist (bcf (ψ k)) g₀ := BoundedContinuousFunction.dist_coe_le_dist (x := (⟨z, hz⟩ : X))
    _ < ε := hK k hkK

private lemma ml_arzela_ascoli_diagonal
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
          AnalyticOnNhd ℂ (F (ψ n)) (closedBall (0 : ℂ) ((((m + 1 : ℕ) : ℝ) + 1) + 1)) := fun n hn => by
        rw [show (((m + 1 : ℕ) : ℝ) + 1) + 1 = ((m + 1 : ℕ) : ℝ) + 2 by ring]
        exact hAn (m + 1) (ψ n) (hn.trans (hψ_mono.id_le n))
      have hBd' : ∀ n ≥ K (m + 1),
          ∀ z ∈ closedBall (0 : ℂ) ((((m + 1 : ℕ) : ℝ) + 1) + 1), ‖F (ψ n) z‖ ≤ M (m + 1) :=
        fun n hn z hz => by
          rw [show (((m + 1 : ℕ) : ℝ) + 1) + 1 = ((m + 1 : ℕ) : ℝ) + 2 by ring] at hz
          exact hBd (m + 1) (ψ n) (hn.trans (hψ_mono.id_le n)) z hz
      have hex := ml_arzela_ascoli_single_ball (F := fun n => F (ψ n))
        (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1) (hM (m + 1)) hAn' hBd'
      exact ⟨ψ ∘ Classical.choose hex, ⟨hψ_mono.comp (Classical.choose_spec (Classical.choose_spec hex)).1,
        Classical.choose (Classical.choose_spec hex), (Classical.choose_spec (Classical.choose_spec hex)).2⟩,
        Classical.choose hex, (Classical.choose_spec (Classical.choose_spec hex)).1, rfl⟩
  let ψ0_ex := ml_arzela_ascoli_single_ball (F := F) (r := 1) (M := M 0) (N₀ := K 0) zero_lt_one (hM 0)
    (fun n hn => by rw [show (1 : ℝ) + 1 = ((0 : ℕ) : ℝ) + 2 by norm_num]; exact hAn 0 n hn)
    (fun n hn z hz => by rw [show (1 : ℝ) + 1 = ((0 : ℕ) : ℝ) + 2 by norm_num] at hz; exact hBd 0 n hn z hz)
  let base : { ψ : ℕ → ℕ // PSub 0 ψ } :=
    ⟨Classical.choose ψ0_ex, (Classical.choose_spec (Classical.choose_spec ψ0_ex)).1,
      Classical.choose (Classical.choose_spec ψ0_ex), by
        simpa [Nat.cast_zero, zero_add] using (Classical.choose_spec (Classical.choose_spec ψ0_ex)).2⟩
  let seq : ∀ m : ℕ, { ψ : ℕ → ℕ // PSub m ψ } :=
    Nat.rec base (fun m prev => ⟨(step m prev).1, (step m prev).2.1⟩)
  have hfactor : ∀ m k : ℕ, m ≤ k → ∃ α : ℕ → ℕ, StrictMono α ∧ (seq k).1 = (seq m).1 ∘ α := by
    intro m k hmk; induction hmk with
    | refl => exact ⟨id, strictMono_id, rfl⟩
    | @step k _ ih =>
      rcases ih with ⟨α₁, hα₁, heq₁⟩
      obtain ⟨α₂, hα₂, heq₂⟩ := (step k (seq k)).2.2
      exact ⟨α₁ ∘ α₂, hα₁.comp hα₂, by change (step k (seq k)).1 = _; rw [heq₂, heq₁]; rfl⟩
  let φ : ℕ → ℕ := fun k => (seq k).1 k
  have hφ_mono : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
    obtain ⟨α, hα, heq⟩ := (step k (seq k)).2.2
    have hstep_val : φ (k + 1) = (seq k).1 (α (k + 1)) := by
      dsimp [φ]; change (step k (seq k)).1 (k + 1) = _; rw [heq]; rfl
    rw [hstep_val]
    exact (seq k).2.1 (lt_of_lt_of_le (Nat.lt_succ_self k) (hα.id_le (k + 1)))
  have hG_exists : ∀ m : ℕ, ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (φ k)) g atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)) := fun m => by
    obtain ⟨g, hg⟩ := (seq m).2.2
    refine ⟨g, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff] at hg ⊢; intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hg ε hε)
    refine Filter.eventually_atTop.mpr ⟨max m N, fun k hk z hz => ?_⟩
    obtain ⟨α, hα, heq⟩ := hfactor m k ((le_max_left m N).trans hk)
    have hφk : φ k = (seq m).1 (α k) := by dsimp [φ]; rw [heq]; rfl
    rw [hφk]
    exact hN (α k) (((le_max_right m N).trans hk).trans (hα.id_le k)) z hz
  choose g_m hg_m using hG_exists
  let G : ℂ → ℂ := fun z => g_m ⌈‖z‖⌉₊ z
  have hg_agree : ∀ m : ℕ, ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 1), g_m m z = G z := fun m z hz => by
    let m' := ⌈‖z‖⌉₊
    have hm'_le : ‖z‖ ≤ (m' : ℝ) := Nat.le_ceil _
    have hz_m' : z ∈ closedBall (0 : ℂ) ((m' : ℝ) + 1) := by rw [mem_closedBall_zero_iff]; linarith
    exact tendsto_nhds_unique ((hg_m m).tendsto_at hz) ((hg_m m').tendsto_at hz_m')
  exact ⟨φ, G, hφ_mono, fun m => (hg_m m).congr_right fun z hz => hg_agree m z hz⟩

private lemma ml_integrable_of_symmetric_interval_norm_le {f : ℝ → ℂ} {C : ℝ}
    (hf_cont : Continuous f) (hC : ∀ N : ℕ, ∫ x in (-N : ℝ)..(N : ℝ), ‖f x‖ ≤ C) :
    Integrable f := by
  have hC_nn : 0 ≤ C := by have := hC 0; simpa using this
  have h_lint_le : ∀ N : ℕ, ∫⁻ x : ℝ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x ≤
      ENNReal.ofReal C := fun N => by
    have hle : (-N : ℝ) ≤ (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
    have hint_on : IntegrableOn (fun y => ‖f y‖) (Ioc (-N : ℝ) (N : ℝ)) :=
      (hf_cont.norm.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have h_eq : ∫⁻ x : ℝ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x =
        ENNReal.ofReal (∫ x in (-N : ℝ)..(N : ℝ), ‖f x‖) := by
      rw [lintegral_indicator measurableSet_Ioc,
        show (∫⁻ x in Ioc (-N : ℝ) (N : ℝ), ‖f x‖ₑ) =
            ∫⁻ x in Ioc (-N : ℝ) (N : ℝ), ‖‖f x‖‖ₑ by simp [eNorm_norm],
        ← ofReal_integral_norm_eq_lintegral_eNorm hint_on, intervalIntegral.integral_of_le hle]
      congr 2; ext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [h_eq]; exact ENNReal.ofReal_le_ofReal (hC N)
  have hmono : Monotone (fun (N : ℕ) (x : ℝ) =>
      (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) := fun m n hmn x => by
    by_cases hx : x ∈ Ioc (-m : ℝ) (m : ℝ)
    · have hx' : x ∈ Ioc (-n : ℝ) (n : ℝ) :=
        ⟨by have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn; linarith [hx.1],
          hx.2.trans (Nat.cast_le.mpr hmn)⟩
      simp [hx, hx']
    · simp [hx]
  have hsup : (⨆ N : ℕ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ)) = fun y => ‖f y‖ₑ := by
    ext x; rw [iSup_apply]; apply le_antisymm
    · exact iSup_le fun N => by by_cases hx : x ∈ Ioc (-N : ℝ) (N : ℝ) <;> simp [hx]
    · obtain ⟨N, hN⟩ := exists_nat_gt |x|
      have hx : x ∈ Ioc (-N : ℝ) (N : ℝ) := ⟨by linarith [(abs_lt.mp hN).1], (abs_lt.mp hN).2.le⟩
      have h_eq : (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x = ‖f x‖ₑ := by simp [hx]
      rw [← h_eq]; exact le_iSup (fun N : ℕ => (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) N
  have h_meas : ∀ N : ℕ, Measurable (fun x : ℝ =>
      (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x) := fun N =>
    hf_cont.eNorm.measurable.indicator measurableSet_Ioc
  have hfin : ∫⁻ x : ℝ, ‖f x‖ₑ ≤ ENNReal.ofReal C := by
    have h_eq_sup : ∀ x : ℝ, ‖f x‖ₑ =
        ⨆ N : ℕ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x := fun x => by
      rw [← congrFun hsup x, iSup_apply]
    rw [lintegral_congr h_eq_sup, lintegral_iSup h_meas hmono]
    exact iSup_le h_lint_le
  exact ⟨hf_cont.aestronglyMeasurable, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top⟩

/-! ### Geometric/analytic properties of `D.G` at `D.S` and `D.tm` -/

lemma ShellHBData.deriv_G_tm_re_neg (D : ShellHBData) : (deriv D.G (D.tm : ℂ)).re < 0 := by
  have hG0 : D.G (D.tm : ℂ) = 0 := D.G_eq_zero_on_S D.tm D.tm_mem
  have hd : HasDerivAt (fun x : ℝ => D.G (x : ℂ)) (deriv D.G (D.tm : ℂ)) D.tm :=
    (D.G_diff (D.tm : ℂ)).hasDerivAt.comp_ofReal
  have him : (deriv D.G (D.tm : ℂ)).im = 0 := by
    have hre : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).re) (deriv D.G (D.tm : ℂ)).re D.tm :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm hd
    have hc : HasDerivAt (fun x : ℝ => (((D.G (x : ℂ)).re : ℝ) : ℂ))
        (((deriv D.G (D.tm : ℂ)).re : ℝ) : ℂ) D.tm := hre.ofReal_comp
    have heq : (fun x : ℝ => D.G (x : ℂ)) = fun x : ℝ => (((D.G (x : ℂ)).re : ℝ) : ℂ) := by
      ext x; exact Complex.ext rfl (D.G_real x)
    rw [heq] at hd
    exact (congrArg Complex.im (hd.unique hc)).trans (Complex.ofReal_im _)
  have hre : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).re) (deriv D.G (D.tm : ℂ)).re D.tm :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm hd
  have hslope_le : Tendsto (fun x : ℝ => ((D.G (x : ℂ)).re - (D.G (D.tm : ℂ)).re) / (x - D.tm))
      (𝓝[<] D.tm) (𝓝 (deriv D.G (D.tm : ℂ)).re) := by
    rw [hasDerivAt_iff_tendsto_slope] at hre
    exact (hre.mono_left (nhdsWithin_mono _ fun _ hx => ne_of_lt hx)).congr fun x => by
      simp [slope_def_field]
  have hle0 : (deriv D.G (D.tm : ℂ)).re ≤ 0 := by
    refine le_of_tendsto hslope_le ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < D.tm)
    have hnum : 0 ≤ (D.G (x : ℂ)).re - (D.G (D.tm : ℂ)).re := by
      rw [hG0, Complex.zero_re, sub_zero]; exact D.G_nonneg_left x hx.le
    exact div_nonpos_of_nonneg_of_nonpos hnum (sub_nonpos.2 hx.le)
  refine lt_of_le_of_ne hle0 fun h0 => D.G_deriv_ne_zero D.tm D.tm_mem (Complex.ext h0 him)

lemma shellHBQuantData_exists (D : ShellHBData) :
    ∃ p : ℝ × ℝ × ℝ, 0 < p.1 ∧ p.1 ≤ 1 / 4 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      (∀ t ∈ D.S.erase D.tm, D.tm + p.1 < t) ∧
      (∀ b : ℝ, 1 / (4 * ∫ x : ℝ, ‖D.G (x : ℂ)‖) ≤ b → b ≤ 1 / (∫ x : ℝ, ‖D.G (x : ℂ)‖) →
        (∀ x ∈ Icc (D.tm - p.1) (D.tm + p.1), b * (deriv D.G (x : ℂ)).re ≤ -4 * p.2.1) ∧
        (∀ t ∈ D.S, ∀ x ∈ Icc (t - 1) (t + 1), b * ‖deriv D.G (x : ℂ)‖ ≤ p.2.2 / 2 - 1) ∧
        (∀ h : ℝ, 0 < h → h ≤ p.1 → b * (D.G ((D.tm + h : ℝ) : ℂ)).re < 0)) := by
  let g0 : ℝ := -(deriv D.G (D.tm : ℂ)).re
  have hg0 : 0 < g0 := neg_pos.2 D.deriv_G_tm_re_neg
  have hcont_re : ContinuousAt (fun x : ℝ => (deriv D.G (x : ℂ)).re) D.tm :=
    (Complex.continuous_re.comp ((D.G_diff.deriv).continuous.comp Complex.continuous_ofReal)).continuousAt
  have hnhds : ∀ᶠ x : ℝ in 𝓝 D.tm, (deriv D.G (x : ℂ)).re ≤ -(g0 / 2) := by
    have h0 : (deriv D.G (D.tm : ℂ)).re < -(g0 / 2) := by dsimp [g0]; linarith
    exact hcont_re.eventually (Iic_mem_nhds h0)
  obtain ⟨δ₀, hδ₀_pos, hδ₀_bd⟩ := Metric.eventually_nhds_iff_ball.1 hnhds
  let gap_S : ℝ := if h : (D.S.erase D.tm).Nonempty then (D.S.erase D.tm).min' h - D.tm else 1
  have hgap_pos : 0 < gap_S := by
    dsimp [gap_S]; split_ifs with h
    · have hmem := Finset.min'_mem _ h
      rw [Finset.mem_erase] at hmem
      exact sub_pos.2 (lt_of_le_of_ne (D.tm_min _ hmem.2) hmem.1.symm)
    · exact one_pos
  let δ_star : ℝ := min (min (δ₀ / 2) (1 / 4)) (gap_S / 4)
  have hδ_pos : 0 < δ_star := lt_min (lt_min (half_pos hδ₀_pos) (by norm_num)) (by positivity)
  have hδ_le_quarter : δ_star ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ_lt_δ₀ : δ_star < δ₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hδ₀_pos)
  let massG : ℝ := ∫ x : ℝ, ‖D.G (x : ℂ)‖
  have hmassG : 0 < massG := D.G_l1_pos
  let b_lo : ℝ := 1 / (4 * massG)
  let b_hi : ℝ := 1 / massG
  have hb_lo_pos : 0 < b_lo := by positivity
  let κ_star : ℝ := b_lo * g0 / 8
  have hκ_pos : 0 < κ_star := by positivity
  let R_S : ℝ := (D.S.sup' D.S_nonempty (fun t => |t|)) + 1
  have hR_S : ∀ t ∈ D.S, ∀ x ∈ Icc (t - 1) (t + 1), (x : ℂ) ∈ closedBall (0 : ℂ) R_S := by
    intro t ht x hx
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have htR : |t| ≤ D.S.sup' D.S_nonempty (fun s => |s|) := Finset.le_sup' (fun s => |s|) ht
    exact abs_le.2 ⟨by linarith [hx.1, (abs_le.1 htR).1], by linarith [hx.2, (abs_le.1 htR).2]⟩
  have hder_bdd : BddAbove ((fun z : ℂ => ‖deriv D.G z‖) '' closedBall (0 : ℂ) R_S) :=
    (isCompact_closedBall (0 : ℂ) R_S).image
      (D.G_diff.deriv.continuous.norm) |>.bddAbove
  obtain ⟨M_d, hM_d⟩ := hder_bdd
  let M_d' : ℝ := max M_d 0
  have hM_d' : ∀ z ∈ closedBall (0 : ℂ) R_S, ‖deriv D.G z‖ ≤ M_d' := fun z hz =>
    (hM_d ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  let C1_D : ℝ := max (2 * b_hi * M_d' + 2) 1
  have hC1_pos : 0 < C1_D := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(δ_star, κ_star, C1_D), hδ_pos, hδ_le_quarter, hκ_pos, hC1_pos, ?_, fun b hblo hbhi => ?_⟩
  · intro t ht
    have hne : (D.S.erase D.tm).Nonempty := ⟨t, ht⟩
    have hmin : (D.S.erase D.tm).min' hne ≤ t := Finset.min'_le _ _ ht
    have hgap_eq : gap_S = (D.S.erase D.tm).min' hne - D.tm := by dsimp [gap_S]; split_ifs; rfl
    have hδ_le_gap : δ_star ≤ gap_S / 4 := min_le_right _ _
    linarith
  · have hb_pos : 0 < b := lt_of_lt_of_le hb_lo_pos hblo
    have hslope : ∀ x ∈ Icc (D.tm - δ_star) (D.tm + δ_star),
        b * (deriv D.G (x : ℂ)).re ≤ -4 * κ_star := by
      intro x hx
      have hxb : x ∈ ball D.tm δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq]
        exact (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans_lt hδ_lt_δ₀
      have hre := hδ₀_bd x hxb
      have hneg1 : b * (deriv D.G (x : ℂ)).re ≤ b * -(g0 / 2) :=
        mul_le_mul_of_nonneg_left hre hb_pos.le
      have hneg2 : b * -(g0 / 2) ≤ b_lo * -(g0 / 2) := by
        nlinarith [hg0]
      have hk4 : b_lo * -(g0 / 2) = -4 * κ_star := by dsimp [κ_star]; ring
      linarith
    refine ⟨hslope, fun t ht x hx => ?_, fun h hh0 hhδ => ?_⟩
    · have hnd := hM_d' (x : ℂ) (hR_S t ht x hx)
      have h1 : b * ‖deriv D.G (x : ℂ)‖ ≤ b_hi * M_d' :=
        mul_le_mul hbhi hnd (norm_nonneg _) (by positivity)
      have h2 : 2 * b_hi * M_d' + 2 ≤ C1_D := le_max_left _ _
      linarith
    · have hftc : (D.G ((D.tm + h : ℝ) : ℂ)).re - (D.G (D.tm : ℂ)).re =
          ∫ u in D.tm..(D.tm + h), (deriv D.G (u : ℂ)).re := by
        have hda : ∀ u ∈ uIcc D.tm (D.tm + h),
            HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).re) ((deriv D.G (u : ℂ)).re) u := fun u _ =>
          Complex.reCLM.hasFDerivAt.comp_hasDerivAt u ((D.G_diff (u : ℂ)).hasDerivAt.comp_ofReal)
        have hcont : ContinuousOn (fun u : ℝ => (deriv D.G (u : ℂ)).re) (uIcc D.tm (D.tm + h)) :=
          (Complex.continuous_re.comp (D.G_diff.deriv.continuous.comp Complex.continuous_ofReal)).continuousOn
        exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hda (hcont.intervalIntegrable)).symm
      rw [D.G_eq_zero_on_S D.tm D.tm_mem, Complex.zero_re, sub_zero] at hftc
      have hmono : ∫ u in D.tm..(D.tm + h), (deriv D.G (u : ℂ)).re ≤
          ∫ _ in D.tm..(D.tm + h), -(g0 / 2) := by
        refine intervalIntegral.integral_mono_on (by linarith : D.tm ≤ D.tm + h)
          ((Complex.continuous_re.comp (D.G_diff.deriv.continuous.comp Complex.continuous_ofReal)).intervalIntegrable
            _ _) intervalIntegrable_const fun u hu => ?_
        have hub : u ∈ ball D.tm δ₀ := by
          rw [Metric.mem_ball, Real.dist_eq]
          exact (abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans_lt hδ_lt_δ₀
        exact hδ₀_bd u hub
      rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono
      have hneg_G : (D.G ((D.tm + h : ℝ) : ℂ)).re < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hb_pos hneg_G

/-- Constants `(δ_*, κ_*, C₁)` extracted purely from `D : ShellHBData` for the multilevel
`QuantC1` conclusion. -/
noncomputable def shellHBQuantData (D : ShellHBData) :
    { p : ℝ × ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ 1 / 4 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      (∀ t ∈ D.S.erase D.tm, D.tm + p.1 < t) ∧
      (∀ b : ℝ, 1 / (4 * ∫ x : ℝ, ‖D.G (x : ℂ)‖) ≤ b → b ≤ 1 / (∫ x : ℝ, ‖D.G (x : ℂ)‖) →
        (∀ x ∈ Icc (D.tm - p.1) (D.tm + p.1), b * (deriv D.G (x : ℂ)).re ≤ -4 * p.2.1) ∧
        (∀ t ∈ D.S, ∀ x ∈ Icc (t - 1) (t + 1), b * ‖deriv D.G (x : ℂ)‖ ≤ p.2.2 / 2 - 1) ∧
        (∀ h : ℝ, 0 < h → h ≤ p.1 → b * (D.G ((D.tm + h : ℝ) : ℂ)).re < 0)) } :=
  ⟨Classical.choose (shellHBQuantData_exists D), Classical.choose_spec (shellHBQuantData_exists D)⟩

/-- Conclusion of multilevel `TE.0'` for `D` with constants `(δ_*, κ_*, C₁)`:
`u_T - D.tm ≤ min δ_* (min η_cap 1)`, `‖Ψ'‖ ≤ C₁` on `[t - 1/2, t + 1/2]` for every `t ∈ D.S`,
and `Re Ψ' ≤ -2 κ_*` on `[D.tm - δ_*, D.tm + δ_*]`. -/
structure QuantC1MultilevelB2Holds (D : ShellHBData) (δ_star κ_star C1 η_cap : ℝ)
    (Ψ : ℂ → ℂ) (u_T : ℝ) : Prop where
  uT_sub_le : u_T - D.tm ≤ min δ_star (min η_cap 1)
  deriv_norm_le : ∀ t ∈ D.S, ∀ x ∈ Icc (t - 1 / 2) (t + 1 / 2), ‖deriv Ψ (x : ℂ)‖ ≤ C1
  deriv_re_le : ∀ x ∈ Icc (D.tm - δ_star) (D.tm + δ_star), (deriv Ψ (x : ℂ)).re ≤ -2 * κ_star

/-- **Multilevel `TE.0'` (`teb:quant_c1_hb`, type-(I) envelope)** for `D : ShellHBData`, fixed
site-offset bound `D_1 ≥ 0`, and any upper cap `η_cap > 0` on `u_T - D.tm`. -/
theorem hankel_quant_c1_multilevel_typeI (D : ShellHBData) {C_0 D_1 η_cap : ℝ}
    (hC0 : 0 < C_0) (_hD1 : 0 ≤ D_1) (hη : 0 < η_cap)
    (R_dom δ_lobe : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c)
    (hδ_lim : Tendsto δ_lobe atTop (𝓝 0)) :
    let δ_star := (shellHBQuantData D).1.1
    let κ_star := (shellHBQuantData D).1.2.1
    let C1 := (shellHBQuantData D).1.2.2
    ∃ c₁ : ℝ, 2 ≤ c₁ ∧ ∀ c' : ℝ, c₁ ≤ c' →
      ∀ (Ψ : ℂ → ℂ) (u_T : ℝ) (u_site : ℝ → ℝ),
        AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R_dom c')) →
        (∀ x ∈ Icc (-R_dom c') (R_dom c'), (Ψ (x : ℂ)).im = 0) →
        (∀ u ∈ closedBall (0 : ℂ) (R_dom c'), ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ))) →
        D.tm < u_T → u_T ≤ R_dom c' →
        (∀ t ∈ D.S.erase D.tm, |u_site t - t| ≤ D_1 * c' ^ (-(1 / 3 : ℝ)) ∧
          |u_site t| ≤ R_dom c' ∧ -δ_lobe c' ≤ (Ψ (u_site t : ℂ)).re) →
        (∀ x ∈ Icc (-R_dom c') u_T, -δ_lobe c' ≤ (Ψ (x : ℂ)).re) →
        (∫ x in (-R_dom c')..(R_dom c'), ‖Ψ (x : ℂ)‖ ≤ 1 + δ_lobe c') →
        ((1 / 2 : ℝ) - δ_lobe c' ≤ ∫ x in u_T..(R_dom c'), max 0 (-(Ψ (x : ℂ)).re)) →
        (∀ R' ∈ Icc (0 : ℝ) (R_dom c'), -R' ≤ u_T →
          ∫ x in (-R')..(R_dom c'), (Ψ (x : ℂ)).re ≤ δ_lobe c') →
        QuantC1MultilevelB2Holds D δ_star κ_star C1 η_cap Ψ u_T := by
  intro δ_star κ_star C1
  obtain ⟨hδ_pos, hδ_le_q, hκ_pos, hC1_pos, _, hG_props⟩ := (shellHBQuantData D).2
  by_contra h_none
  push Not at h_none
  have hex : ∀ n : ℕ, ∃ c' : ℝ, max (n : ℝ) 2 ≤ c' ∧
      ∃ (Ψ : ℂ → ℂ) (u_T : ℝ) (u_site : ℝ → ℝ),
        AnalyticOnNhd ℂ Ψ (closedBall (0 : ℂ) (R_dom c')) ∧
        (∀ x ∈ Icc (-R_dom c') (R_dom c'), (Ψ (x : ℂ)).im = 0) ∧
        (∀ u ∈ closedBall (0 : ℂ) (R_dom c'), ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖Ψ u‖ ≤ C_0 * airyEnv u * ((u ^ (1 / 2 : ℂ)).re) ^ (-(1 / 2 : ℝ))) ∧
        D.tm < u_T ∧ u_T ≤ R_dom c' ∧
        (∀ t ∈ D.S.erase D.tm, |u_site t - t| ≤ D_1 * c' ^ (-(1 / 3 : ℝ)) ∧
          |u_site t| ≤ R_dom c' ∧ -δ_lobe c' ≤ (Ψ (u_site t : ℂ)).re) ∧
        (∀ x ∈ Icc (-R_dom c') u_T, -δ_lobe c' ≤ (Ψ (x : ℂ)).re) ∧
        (∫ x in (-R_dom c')..(R_dom c'), ‖Ψ (x : ℂ)‖ ≤ 1 + δ_lobe c') ∧
        ((1 / 2 : ℝ) - δ_lobe c' ≤ ∫ x in u_T..(R_dom c'), max 0 (-(Ψ (x : ℂ)).re)) ∧
        (∀ R' ∈ Icc (0 : ℝ) (R_dom c'), -R' ≤ u_T →
          ∫ x in (-R')..(R_dom c'), (Ψ (x : ℂ)).re ≤ δ_lobe c') ∧
        ¬ QuantC1MultilevelB2Holds D δ_star κ_star C1 η_cap Ψ u_T := fun n => by
    simpa [not_and_or, not_le] using h_none (max (n : ℝ) 2) (le_max_right _ _)
  choose c'_seq hc'_ge Ψ_seq uT_seq usite_seq hspec using hex
  have hc'_atTop : Tendsto c'_seq atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_left (n : ℝ) 2).trans (hc'_ge n)) tendsto_natCast_atTop_atTop
  have hR_seq_lim : Tendsto (fun n => R_dom (c'_seq n)) atTop atTop := hR_lim.comp hc'_atTop
  have hδ_seq_nn : ∀ᶠ n in atTop, 0 ≤ δ_lobe (c'_seq n) := hc'_atTop.eventually hδ_nn
  have hδ_seq_lim : Tendsto (fun n => δ_lobe (c'_seq n)) atTop (𝓝 0) := hδ_lim.comp hc'_atTop
  let U₀ : ℝ := quantC1_U0 C_0
  have hU0_ge1 : 1 ≤ U₀ := one_le_quantC1_U0 C_0
  have hK_ex : ∀ m : ℕ, ∃ K : ℕ, ∀ n ≥ K,
      (m : ℝ) + 4 ≤ R_dom (c'_seq n) ∧ 0 ≤ δ_lobe (c'_seq n) ∧
        δ_lobe (c'_seq n) ≤ 1 / 4 ∧ U₀ ≤ R_dom (c'_seq n) := fun m => by
    have h1 : ∀ᶠ n in atTop, (m : ℝ) + 4 ≤ R_dom (c'_seq n) :=
      hR_seq_lim (eventually_ge_atTop ((m : ℝ) + 4))
    have h2 : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ 1 / 4 :=
      hδ_seq_lim (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    have h3 : ∀ᶠ n in atTop, U₀ ≤ R_dom (c'_seq n) :=
      hR_seq_lim (eventually_ge_atTop U₀)
    obtain ⟨K, hK⟩ := eventually_atTop.mp (h1.and (hδ_seq_nn.and (h2.and h3)))
    exact ⟨K, fun n hn => ⟨(hK n hn).1, (hK n hn).2.1, (hK n hn).2.2.1, (hK n hn).2.2.2⟩⟩
  choose K_seq hK_spec using hK_ex
  let M_seq : ℕ → ℝ := fun m =>
    32 * Real.exp (5 / 2) * C_0 * (1 + ((m : ℝ) + 2)) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * ((m : ℝ) + 2) ^ (3 / 2 : ℝ))
  have hM_nn : ∀ m : ℕ, 0 ≤ M_seq m := fun m => by dsimp [M_seq]; positivity
  have hAn_seq : ∀ m, ∀ n ≥ K_seq m,
      AnalyticOnNhd ℂ (Ψ_seq n) (closedBall (0 : ℂ) ((m : ℝ) + 2)) := fun m n hn =>
    (hspec n).1.mono (closedBall_subset_closedBall (by linarith [(hK_spec m n hn).1]))
  have hBd_seq : ∀ m, ∀ n ≥ K_seq m,
      ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 2), ‖Ψ_seq n z‖ ≤ M_seq m := fun m n hn z hz =>
    hankelI_cut_bound (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2) hC0 (hspec n).1 (hspec n).2.2.1
      (by linarith [(hK_spec m n hn).1]) hz
  obtain ⟨φ, Φ_inf, hφ_mono, hΦ_unif⟩ := ml_arzela_ascoli_diagonal hM_nn hAn_seq hBd_seq
  have hφ_atTop : Tendsto φ atTop atTop := hφ_mono.tendsto_atTop
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
      exact hankelI_disc_bound hC0 (hspec (φ k)).1 (hspec (φ k)).2.2.1 (u₀ := u) hR_dom
    exact le_of_tendsto ht_pt hev_bd
  have hΦ_real : ∀ x : ℝ, (Φ_inf (x : ℂ)).im = 0 := by
    intro x
    let m : ℕ := ⌈|x|⌉₊
    have hx_m : (x : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [Nat.le_ceil |x|]
    have ht_im : Tendsto (fun k => (Ψ_seq (φ k) (x : ℂ)).im) atTop (𝓝 (Φ_inf (x : ℂ)).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp ((hΦ_unif m).tendsto_at hx_m)
    have hev0 : ∀ᶠ k in atTop, (Ψ_seq (φ k) (x : ℂ)).im = 0 := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hR := (hK_spec m (φ k) (hN k hk)).1
      exact (hspec (φ k)).2.1 x (abs_le.mp ((Nat.le_ceil |x|).trans (by linarith)))
    exact tendsto_nhds_unique ht_im (tendsto_const_nhds.congr' (hev0.mono fun _ hk => hk.symm))
  have hΦ_symm_norm : ∀ N : ℕ, ∫ x in (-N : ℝ)..(N : ℝ), ‖Φ_inf (x : ℂ)‖ ≤ 1 := by
    intro N
    refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
    let ε : ℝ := ε₀ / 2
    have hε : 0 < ε := by positivity
    have hε' : 0 < ε / (2 * (N : ℝ) + 1) := div_pos hε (by positivity)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif N) (ε / (2 * (N : ℝ) + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ ε := hδ_seq_lim (Iic_mem_nhds hε)
    obtain ⟨k, hk⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq N))).and (hφ_atTop.eventually hev_δ)))
    obtain ⟨hk_unif, hk_K, hk_δ⟩ := hk k le_rfl
    have hR := (hK_spec N (φ k) hk_K).1
    have hNR : (N : ℝ) ≤ R_dom (c'_seq (φ k)) := by linarith
    have hle : (-N : ℝ) ≤ (N : ℝ) := by linarith [show (0 : ℝ) ≤ N by positivity]
    have h_diff_ball : ∀ x ∈ Icc (-N : ℝ) (N : ℝ), (x : ℂ) ∈ closedBall (0 : ℂ) ((N : ℝ) + 1) :=
      fun x hx => by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [abs_le.mpr hx]
    have h_pt_le : ∀ x ∈ Icc (-N : ℝ) (N : ℝ),
        ‖Φ_inf (x : ℂ)‖ ≤ ‖Ψ_seq (φ k) (x : ℂ)‖ + ε / (2 * (N : ℝ) + 1) := fun x hx => by
      have hd := (hk_unif (x : ℂ) (h_diff_ball x hx)).le
      rw [dist_eq_norm] at hd
      calc ‖Φ_inf (x : ℂ)‖ = ‖(Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)) + Ψ_seq (φ k) (x : ℂ)‖ := by ring_nf
        _ ≤ ‖Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)‖ + ‖Ψ_seq (φ k) (x : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖Ψ_seq (φ k) (x : ℂ)‖ + ε / (2 * (N : ℝ) + 1) := by linarith
    have hcΦ : ContinuousOn (fun x : ℝ => ‖Φ_inf (x : ℂ)‖) (Icc (-N : ℝ) (N : ℝ)) :=
      (hΦ_diff.continuous.comp continuous_ofReal).norm.continuousOn
    have hcΨ : ContinuousOn (fun x : ℝ => ‖Ψ_seq (φ k) (x : ℂ)‖)
        (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
      (((hspec (φ k)).1.continuousOn).comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx).norm
    have hiΦ := hcΦ.intervalIntegrable_of_Icc (μ := volume) hle
    have hiΨ_N := (hcΨ.mono (Icc_subset_Icc (by linarith) hNR)).intervalIntegrable_of_Icc (μ := volume) hle
    have h_int1 := intervalIntegral.integral_mono_on hle hiΦ (hiΨ_N.add intervalIntegrable_const) h_pt_le
    rw [intervalIntegral.integral_add hiΨ_N intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h_int1
    have h_mono_R : ∫ x in (-N : ℝ)..(N : ℝ), ‖Ψ_seq (φ k) (x : ℂ)‖ ≤
        ∫ x in (-R_dom (c'_seq (φ k)))..(R_dom (c'_seq (φ k))), ‖Ψ_seq (φ k) (x : ℂ)‖ := by
      rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le (by linarith : -R_dom (c'_seq (φ k)) ≤ R_dom (c'_seq (φ k)))]
      exact setIntegral_mono_set ((hcΨ.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioc (by linarith) hNR hx)
    have hΨ_L1 := (hspec (φ k)).2.2.2.2.2.2.2.1
    have h_err : ((N : ℝ) - (-N : ℝ)) * (ε / (2 * (N : ℝ) + 1)) ≤ ε := by
      rw [show (N : ℝ) - (-N : ℝ) = 2 * (N : ℝ) by ring, mul_div_assoc',
        div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1)]
      nlinarith
    have hδ_le_half : δ_lobe (c'_seq (φ k)) ≤ ε₀ / 2 := hk_δ
    have hε_eq : ε = ε₀ / 2 := rfl
    linarith
  have hΦ_int : Integrable (fun x : ℝ => Φ_inf (x : ℂ)) :=
    ml_integrable_of_symmetric_interval_norm_le (hΦ_diff.continuous.comp continuous_ofReal) hΦ_symm_norm
  have hΦ_norm_int_le1 : ∫ x : ℝ, ‖Φ_inf (x : ℂ)‖ ≤ 1 := by
    have ht0 : Tendsto (fun t : ℝ => ∫ x in (-t)..t, ‖Φ_inf (x : ℂ)‖)
        atTop (𝓝 (∫ x : ℝ, ‖Φ_inf (x : ℂ)‖)) :=
      intervalIntegral_tendsto_integral hΦ_int.norm tendsto_neg_atTop_atBot tendsto_id
    exact le_of_tendsto (ht0.comp tendsto_natCast_atTop_atTop) (Eventually.of_forall hΦ_symm_norm)
  have hΦ_pos_tm : ∀ x : ℝ, x ≤ D.tm → 0 ≤ (Φ_inf (x : ℂ)).re := by
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
      exact (hspec (φ k)).2.2.2.2.2.2.1 x ⟨hx_lo, hx_hi⟩
    have hδt : Tendsto (fun k => -δ_lobe (c'_seq (φ k))) atTop (𝓝 0) := by
      simpa using (hδ_seq_lim.comp hφ_atTop).neg
    exact le_of_tendsto_of_tendsto hδt ht_re hev
  -- Nonnegativity at the prescribed sites `t ∈ D.S.erase D.tm`
  have hΦ_pos_sites : ∀ t ∈ D.S.erase D.tm, 0 ≤ (Φ_inf (t : ℂ)).re := by
    intro t ht
    let m : ℕ := ⌈|t|⌉₊ + 1
    have ht_ball : (t : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have := Nat.le_ceil |t|
      dsimp [m]; push_cast; linarith
    have hev_usite_ball : ∀ᶠ k in atTop, (usite_seq (φ k) t : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      have hc13 : Tendsto (fun k => D_1 * c'_seq (φ k) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun c : ℝ => c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
        simpa using (h1.comp (hc'_atTop.comp hφ_atTop)).const_mul D_1
      filter_upwards [hc13 (Iic_mem_nhds one_pos)] with k hk
      have hdiff := ((hspec (φ k)).2.2.2.2.2.1 t ht).1
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |usite_seq (φ k) t| ≤ |t| + |usite_seq (φ k) t - t| := by
        calc |usite_seq (φ k) t| = |(usite_seq (φ k) t - t) + t| := by ring_nf
          _ ≤ |usite_seq (φ k) t - t| + |t| := abs_add_le _ _
          _ = |t| + |usite_seq (φ k) t - t| := add_comm _ _
      have hceil : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil |t|
      have hle_m : |t| + 1 ≤ (m : ℝ) := by dsimp [m]; push_cast; linarith
      have hk1 : D_1 * c'_seq (φ k) ^ (-(1 / 3 : ℝ)) ≤ 1 := hk
      have hsub1 : |usite_seq (φ k) t - t| ≤ 1 := hdiff.trans hk1
      linarith
    have h_usite_tend : Tendsto (fun k => (usite_seq (φ k) t : ℂ)) atTop (𝓝 (t : ℂ)) := by
      have hc13 : Tendsto (fun k => D_1 * c'_seq (φ k) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun c : ℝ => c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
        simpa using (h1.comp (hc'_atTop.comp hφ_atTop)).const_mul D_1
      refine Complex.continuous_ofReal.continuousAt.tendsto.comp ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hc13
      simpa [Real.norm_eq_abs] using ((hspec (φ k)).2.2.2.2.2.1 t ht).1
    have ht_site_tend : Tendsto (fun k => (Ψ_seq (φ k) (usite_seq (φ k) t : ℂ)).re)
        atTop (𝓝 (Φ_inf (t : ℂ)).re) := by
      refine Complex.continuous_re.continuousAt.tendsto.comp ?_
      exact TendstoUniformlyOn.tendsto_comp (hΦ_unif m)
        (hΦ_diff (t : ℂ)).continuousAt.continuousWithinAt
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_usite_tend hev_usite_ball)
    have hδt : Tendsto (fun k => -δ_lobe (c'_seq (φ k))) atTop (𝓝 0) := by
      simpa using (hδ_seq_lim.comp hφ_atTop).neg
    have hev : ∀ᶠ k in atTop, -δ_lobe (c'_seq (φ k)) ≤ (Ψ_seq (φ k) (usite_seq (φ k) t : ℂ)).re :=
      Eventually.of_forall fun k => ((hspec (φ k)).2.2.2.2.2.1 t ht).2.2
    exact le_of_tendsto_of_tendsto hδt ht_site_tend hev
  -- Nonpositive total integral `∫_ℝ (Φ_inf x).re ≤ 0`
  have hΦ_total_int_le : ∫ x : ℝ, (Φ_inf (x : ℂ)).re ≤ 0 := by
    have h_symm_re : ∀ N : ℕ, ⌈|D.tm|⌉₊ + 1 ≤ N →
        ∫ x in (-N : ℝ)..(N : ℝ), (Φ_inf (x : ℂ)).re ≤ (6 / 5 : ℝ) * C_0 * Real.exp (-(5 / 6 : ℝ) * N) := by
      intro N hN_ge
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hε' : 0 < (ε / 2) / (2 * (N : ℝ) + 1) := div_pos (half_pos hε) (by positivity)
      have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif N) ((ε / 2) / (2 * (N : ℝ) + 1)) hε'
      have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ ε / 2 :=
        hδ_seq_lim (Iic_mem_nhds (half_pos hε))
      obtain ⟨k, hk⟩ := eventually_atTop.mp
        (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq N))).and (hφ_atTop.eventually hev_δ)))
      obtain ⟨hk_unif, hk_K, hk_δ⟩ := hk k le_rfl
      have hsp := hK_spec N (φ k) hk_K
      have hNR : (N : ℝ) ≤ R_dom (c'_seq (φ k)) := by linarith [hsp.1]
      have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (by omega) hN_ge
      have hNtm : |D.tm| + 1 ≤ (N : ℝ) := by
        have := Nat.le_ceil |D.tm|
        have : (⌈|D.tm|⌉₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN_ge
        linarith
      have hN_uT : -(N : ℝ) ≤ uT_seq (φ k) := by
        have := (abs_le.mp (le_refl |D.tm|)).1
        linarith [(hspec (φ k)).2.2.2.1]
      have h_top := (hspec (φ k)).2.2.2.2.2.2.2.2.2.1 (N : ℝ) ⟨by positivity, hNR⟩ hN_uT
      have hcΨ_dom : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
          (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
        (hspec (φ k)).1.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
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
        hankelI_pos_real_env hC0 (hspec (φ k)).2.2.1 hx1 hxR
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
            fun x _ => by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (Ψ_seq (φ k) (x : ℂ))
        have h_norm_tail := ml_pos_real_norm_tail_le hC0 h1N hNR
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
    exact le_of_tendsto_of_tendsto ht h_exp_tend (eventually_atTop.mpr ⟨⌈|D.tm|⌉₊ + 1, h_symm_re⟩)
  -- Non-vanishing via negative mass on `[D.tm, U₀]`
  have htm_le_a1 : D.tm ≤ airyZero 1 := D.tm_le_airyZero_one
  have htm_le_U0 : D.tm ≤ U₀ := by linarith [airyZero_neg 1, hU0_ge1]
  have hΦ_neg_mass : (1 / 4 : ℝ) ≤ ∫ x in D.tm..U₀, max 0 (-(Φ_inf (x : ℂ)).re) := by
    let m₀ : ℕ := ⌈max |D.tm| U₀⌉₊
    have hm0_ge : max |D.tm| U₀ ≤ (m₀ : ℝ) := Nat.le_ceil _
    have hΦ_m_cont : ContinuousOn (fun x : ℝ => max 0 (-(Φ_inf (x : ℂ)).re)) (Icc D.tm U₀) :=
      ContinuousOn.sup continuousOn_const
        (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal)).neg.continuousOn
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < (ε / 2) / (U₀ - D.tm + 1) := div_pos (half_pos hε) (by linarith)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif m₀) ((ε / 2) / (U₀ - D.tm + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ min (1 / 4) (ε / 2) :=
      hδ_seq_lim (Iic_mem_nhds (lt_min (by norm_num) (half_pos hε)))
    obtain ⟨k, hk⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq m₀))).and (hφ_atTop.eventually hev_δ)))
    obtain ⟨hk_unif, hk_K, hk_δ⟩ := hk k le_rfl
    have hsp := hK_spec m₀ (φ k) hk_K
    have huT_gt_k := (hspec (φ k)).2.2.2.1
    have huT_le_k := (hspec (φ k)).2.2.2.2.1
    have hTail_k := (hspec (φ k)).2.2.2.2.2.2.2.2.1
    have h_env_pos : ∀ x : ℝ, 1 ≤ x → x ≤ R_dom (c'_seq (φ k)) →
        ‖Ψ_seq (φ k) (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) := fun x hx1 hxR =>
      hankelI_pos_real_env hC0 (hspec (φ k)).2.2.1 hx1 hxR
    have huT_le_U0 : uT_seq (φ k) ≤ U₀ := by
      have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
      have htm_le_R : -R_dom (c'_seq (φ k)) ≤ D.tm := by
        linarith [(abs_le.mp ((le_max_left |D.tm| U₀).trans hm0_ge)).1]
      have hcΨ_dom : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
          (Icc (uT_seq (φ k)) (R_dom (c'_seq (φ k)))) :=
        (hspec (φ k)).1.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hx.1, huT_gt_k], hx.2⟩
      exact ml_uT_le hC0 hsp.2.2.1 huT_le_k hcΨ_dom h_env_pos hTail_k
    have hU0_le_R : U₀ ≤ R_dom (c'_seq (φ k)) := hsp.2.2.2
    have hcΨ_tmR : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
        (Icc D.tm (R_dom (c'_seq (φ k)))) :=
      (hspec (φ k)).1.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
        have htm_le_R : -R_dom (c'_seq (φ k)) ≤ D.tm := by
          linarith [(abs_le.mp ((le_max_left |D.tm| U₀).trans hm0_ge)).1]
        exact abs_le.mpr ⟨htm_le_R.trans hx.1, hx.2⟩
    have hcΨ_U0R : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ)) (Icc U₀ (R_dom (c'_seq (φ k)))) :=
      hcΨ_tmR.mono (Icc_subset_Icc_left htm_le_U0)
    have h_tail_q : ∫ x in U₀..(R_dom (c'_seq (φ k))), max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) < 1 / 4 :=
      ml_pos_real_tail_lt_quarter hC0 le_rfl hU0_le_R hcΨ_U0R h_env_pos
    have h_m_cont_all : ContinuousOn (fun x : ℝ => max 0 (-(Ψ_seq (φ k) (x : ℂ)).re))
        (Icc D.tm (R_dom (c'_seq (φ k)))) :=
      ContinuousOn.sup continuousOn_const (Complex.continuous_re.comp_continuousOn hcΨ_tmR).neg
    have h_split := intervalIntegral.integral_add_adjacent_intervals
      ((h_m_cont_all.mono (Icc_subset_Icc huT_gt_k.le hU0_le_R)).intervalIntegrable_of_Icc
        (μ := volume) huT_le_U0)
      ((h_m_cont_all.mono (Icc_subset_Icc_left htm_le_U0)).intervalIntegrable_of_Icc
        (μ := volume) hU0_le_R)
    have h_uT_U0 : ∫ x in (uT_seq (φ k))..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
        ∫ x in D.tm..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      rw [intervalIntegral.integral_of_le huT_le_U0, intervalIntegral.integral_of_le htm_le_U0]
      exact setIntegral_mono_set
        (((h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).integrableOn_Icc (μ := volume)).mono_set
          Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => le_max_left _ _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioc_left huT_gt_k.le hx)
    have h_Ψ_band : 1 / 4 - ε / 2 ≤ ∫ x in D.tm..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      have h2 : δ_lobe (c'_seq (φ k)) ≤ ε / 2 := hk_δ.trans (min_le_right _ _)
      linarith
    have h_pt_m : ∀ x ∈ Icc D.tm U₀,
        max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
          max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - D.tm + 1) := by
      intro x hx
      have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) ((m₀ : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hax : |x| ≤ max |D.tm| U₀ := by
          rcases le_total x 0 with hx0 | hx0
          · rw [abs_of_nonpos hx0]; calc -x ≤ -D.tm := neg_le_neg hx.1
              _ ≤ |D.tm| := neg_le_abs _
              _ ≤ max |D.tm| U₀ := le_max_left _ _
          · rw [abs_of_nonneg hx0]; exact hx.2.trans (le_max_right _ _)
        linarith [hax.trans hm0_ge]
      have hd := (hk_unif (x : ℂ) hx_ball).le
      rw [dist_eq_norm] at hd
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd)).2
      simp only [Complex.sub_re] at hre
      have hneg : -(Ψ_seq (φ k) (x : ℂ)).re ≤ -(Φ_inf (x : ℂ)).re + (ε / 2) / (U₀ - D.tm + 1) := by linarith
      have h0_le : (0 : ℝ) ≤ max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - D.tm + 1) :=
        add_nonneg (le_max_left _ _) (div_nonneg (half_pos hε).le (by linarith))
      exact max_le h0_le (hneg.trans (add_le_add (le_max_right _ _) le_rfl))
    have h_int_m := intervalIntegral.integral_mono_on htm_le_U0
      ((h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).intervalIntegrable_of_Icc (μ := volume) htm_le_U0)
      ((hΦ_m_cont.intervalIntegrable_of_Icc (μ := volume) htm_le_U0).add intervalIntegrable_const) h_pt_m
    rw [intervalIntegral.integral_add (hΦ_m_cont.intervalIntegrable_of_Icc (μ := volume) htm_le_U0)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h_int_m
    have h_err : (U₀ - D.tm) * ((ε / 2) / (U₀ - D.tm + 1)) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hΦ_ne : ∃ z : ℂ, Φ_inf z ≠ 0 := by
    by_contra h_all0; push Not at h_all0
    have h0 : ∫ x in D.tm..U₀, max 0 (-(Φ_inf (x : ℂ)).re) = 0 := by simp [h_all0]
    linarith [hΦ_neg_mass]
  -- Apply `D.uniqueness` to `H = -Φ_inf`
  have hHint_re : 0 ≤ (∫ x : ℝ, (-Φ_inf (x : ℂ))).re := by
    have hre_comm : (∫ x : ℝ, Φ_inf (x : ℂ)).re = ∫ x : ℝ, (Φ_inf (x : ℂ)).re :=
      (Complex.reCLM.integral_comp_comm hΦ_int).symm
    rw [integral_neg, Complex.neg_re, hre_comm]
    linarith [hΦ_total_int_le]
  obtain ⟨b, hb_nn, hH_eq, hb_nz⟩ := D.uniqueness hΦ_diff.neg hΦ_int.neg hC_env_nn
    (fun u => by simpa using hΦ_env u) (fun x => by simp [hΦ_real x]) hHint_re
    (fun t htS htm => by
      change -(Φ_inf (t : ℂ)).re ≤ 0
      linarith [hΦ_pos_sites t (Finset.mem_erase.2 ⟨htm, htS⟩)])
    (fun x hx => by change -(Φ_inf (x : ℂ)).re ≤ 0; linarith [hΦ_pos_tm x hx])
  obtain ⟨z₀, hz₀⟩ := hΦ_ne
  obtain ⟨hb_pos, hb_norm, _⟩ := hb_nz ⟨z₀, neg_ne_zero.mpr hz₀⟩
  have hΦ_eq_G : ∀ z : ℂ, Φ_inf z = (b : ℂ) * D.G z := fun z => by
    have this : (-Φ_inf) z = -((b : ℂ) * D.G z) := hH_eq z
    change -(Φ_inf z) = -((b : ℂ) * D.G z) at this
    exact neg_inj.mp this
  have hb_hi : b ≤ 1 / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
    have hmass_eq : ∫ x : ℝ, ‖Φ_inf (x : ℂ)‖ = b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      have hfn : (fun x : ℝ => ‖Φ_inf (x : ℂ)‖) = fun x : ℝ => b * ‖D.G (x : ℂ)‖ := by
        ext x; rw [hΦ_eq_G (x : ℂ), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb_pos]
      rw [hfn, integral_const_mul]
    rw [hb_norm]
    exact div_le_div_of_nonneg_right (by simpa [norm_neg] using hΦ_norm_int_le1) D.G_l1_pos.le
  have hb_lo : 1 / (4 * ∫ x : ℝ, ‖D.G (x : ℂ)‖) ≤ b := by
    have h_band_le : ∫ x in D.tm..U₀, max 0 (-(Φ_inf (x : ℂ)).re) ≤
        b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      have hpt : ∀ x ∈ Icc D.tm U₀, max 0 (-(Φ_inf (x : ℂ)).re) ≤ b * ‖D.G (x : ℂ)‖ := by
        intro x _
        rw [hΦ_eq_G (x : ℂ), Complex.re_ofReal_mul]
        refine max_le (mul_nonneg hb_pos.le (norm_nonneg _)) ?_
        have h1 : -(D.G (x : ℂ)).re ≤ ‖D.G (x : ℂ)‖ :=
          (neg_le.mp (abs_le.mp (Complex.abs_re_le_norm (D.G (x : ℂ)))).1).trans (le_refl _)
        nlinarith [hb_pos]
      have hint_sub : ∫ x in D.tm..U₀, b * ‖D.G (x : ℂ)‖ ≤ ∫ x : ℝ, b * ‖D.G (x : ℂ)‖ := by
        rw [intervalIntegral.integral_of_le htm_le_U0]
        have hu : ∫ x : ℝ, b * ‖D.G (x : ℂ)‖ =
            ∫ x in (Set.univ : Set ℝ), b * ‖D.G (x : ℂ)‖ := setIntegral_univ.symm
        rw [hu]
        exact setIntegral_mono_set (D.G_int.norm.const_mul b).integrableOn
          (Eventually.of_forall fun _ => mul_nonneg hb_pos.le (norm_nonneg _))
          (Eventually.of_forall fun _ _ => Set.mem_univ _)
      have hΦ_m_cont : ContinuousOn (fun x : ℝ => max 0 (-(Φ_inf (x : ℂ)).re)) (Icc D.tm U₀) :=
        ContinuousOn.sup continuousOn_const
          (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal)).neg.continuousOn
      have hG_int_iu : IntervalIntegrable (fun x : ℝ => b * ‖D.G (x : ℂ)‖) volume D.tm U₀ :=
        ((D.G_diff.continuous.comp continuous_ofReal).norm.const_mul b).intervalIntegrable D.tm U₀
      have h1 := intervalIntegral.integral_mono_on htm_le_U0
        (hΦ_m_cont.intervalIntegrable_of_Icc (μ := volume) htm_le_U0) hG_int_iu hpt
      have h2 : ∫ x : ℝ, b * ‖D.G (x : ℂ)‖ = b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ := integral_const_mul b _
      linarith [h1, hint_sub, h2]
    rw [div_le_iff₀ (mul_pos (by norm_num) D.G_l1_pos)]
    linarith [hΦ_neg_mass, h_band_le]
  -- Extract contradiction with `QuantC1MultilevelB2Holds`
  obtain ⟨hG_slope, hG_norm_bd, hG_right⟩ := hG_props b hb_lo hb_hi
  let η : ℝ := min δ_star (min η_cap 1)
  have hη_pos : 0 < η := lt_min hδ_pos (lt_min hη one_pos)
  have hη_le_δ : η ≤ δ_star := min_le_left _ _
  -- Step A: eventually `uT_seq (φ k) - D.tm ≤ η`
  have hev_uT : ∀ᶠ k in atTop, uT_seq (φ k) - D.tm ≤ η := by
    let x₀ : ℝ := D.tm + η / 2
    have hx0_neg : (Φ_inf (x₀ : ℂ)).re < 0 := by
      rw [hΦ_eq_G (x₀ : ℂ), Complex.re_ofReal_mul]
      exact hG_right (η / 2) (half_pos hη_pos) (by linarith)
    let m₀ : ℕ := ⌈|x₀|⌉₊
    have hx0_m : (x₀ : ℂ) ∈ closedBall (0 : ℂ) ((m₀ : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [Nat.le_ceil |x₀|]
    have ht_pt : Tendsto (fun k => (Ψ_seq (φ k) (x₀ : ℂ)).re) atTop (𝓝 (Φ_inf (x₀ : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp ((hΦ_unif m₀).tendsto_at hx0_m)
    have ht_sum : Tendsto (fun k => (Ψ_seq (φ k) (x₀ : ℂ)).re + δ_lobe (c'_seq (φ k)))
        atTop (𝓝 (Φ_inf (x₀ : ℂ)).re) := by
      simpa using ht_pt.add (hδ_seq_lim.comp hφ_atTop)
    have hev_neg : ∀ᶠ k in atTop, (Ψ_seq (φ k) (x₀ : ℂ)).re + δ_lobe (c'_seq (φ k)) < 0 :=
      ht_sum (Iio_mem_nhds hx0_neg)
    have hev_K : ∀ᶠ k in atTop, K_seq m₀ ≤ φ k := hφ_atTop.eventually (eventually_ge_atTop (K_seq m₀))
    filter_upwards [hev_neg, hev_K] with k hk_neg hk_K
    by_contra h_gt
    push Not at h_gt
    have hx0_uT : x₀ ≤ uT_seq (φ k) := by dsimp [x₀]; linarith
    have hR := (hK_spec m₀ (φ k) hk_K).1
    have hx0_lo : -R_dom (c'_seq (φ k)) ≤ x₀ := by linarith [(abs_le.mp (Nat.le_ceil |x₀|)).1]
    have hp := (hspec (φ k)).2.2.2.2.2.2.1 x₀ ⟨hx0_lo, hx0_uT⟩
    linarith
  -- Step B: eventually `deriv (Ψ_seq (φ k))` obeys `QuantC1MultilevelB2Holds`
  have hev_deriv : ∀ᶠ k in atTop,
      (∀ t ∈ D.S, ∀ x ∈ Icc (t - 1 / 2) (t + 1 / 2), ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖ ≤ C1) ∧
      (∀ x ∈ Icc (D.tm - δ_star) (D.tm + δ_star), (deriv (Ψ_seq (φ k)) (x : ℂ)).re ≤ -2 * κ_star) := by
    let R_max : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
    let m₁ : ℕ := ⌈R_max + 2⌉₊
    have hm1_ge : R_max + 2 ≤ (m₁ : ℝ) := Nat.le_ceil _
    let ε_d : ℝ := min 1 (2 * κ_star)
    have hε_d_pos : 0 < ε_d := lt_min one_pos (mul_pos two_pos hκ_pos)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif m₁) ε_d hε_d_pos
    have hev_K : ∀ᶠ k in atTop, K_seq m₁ ≤ φ k := hφ_atTop.eventually (eventually_ge_atTop (K_seq m₁))
    filter_upwards [h_unif, hev_K] with k hk_unif hk_K
    have hcauchy_pt : ∀ {t : ℝ}, t ∈ D.S → ∀ x ∈ Icc (t - 1 / 2) (t + 1 / 2),
        ‖deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)‖ ≤ ε_d := by
      intro t ht x hx
      have h_ball_sub : closedBall (x : ℂ) 1 ⊆ closedBall (0 : ℂ) ((m₁ : ℝ) + 1) := fun z hz => by
        rw [mem_closedBall_zero_iff]
        rw [mem_closedBall, dist_eq_norm] at hz
        have ht_le : |t| ≤ R_max := Finset.le_sup' (fun s => |s|) ht
        have hx_abs : |x| ≤ R_max + 1 / 2 := by
          have hsub : |x - t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
          calc |x| = |(x - t) + t| := by ring_nf
            _ ≤ |x - t| + |t| := abs_add_le _ _
            _ ≤ R_max + 1 / 2 := by linarith
        calc ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
          _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ ≤ 1 + |x| := add_le_add hz (by rw [Complex.norm_real, Real.norm_eq_abs])
          _ ≤ (m₁ : ℝ) + 1 := by linarith
      have h_diff_holo : DiffContOnCl ℂ (fun z => Ψ_seq (φ k) z - Φ_inf z) (ball (x : ℂ) 1) := by
        have h_Φ_an : AnalyticOnNhd ℂ Φ_inf (closedBall (0 : ℂ) ((m₁ : ℝ) + 1)) :=
          ((analyticOnNhd_iff_differentiableOn isOpen_univ).mpr hΦ_diff.differentiableOn).mono (subset_univ _)
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
      rwa [h_deriv_sub] at h_cauchy
    have hΦ_deriv_eq : ∀ x : ℝ, deriv Φ_inf (x : ℂ) = (b : ℂ) * deriv D.G (x : ℂ) := fun x => by
      have heq_fun : Φ_inf = fun u => (b : ℂ) * D.G u := funext hΦ_eq_G
      rw [heq_fun]
      exact ((D.G_diff (x : ℂ)).hasDerivAt.const_mul (b : ℂ)).deriv
    refine ⟨fun t ht x hx => ?_, fun x hx => ?_⟩
    · have h_cauchy := hcauchy_pt ht x hx
      have hx1 : x ∈ Icc (t - 1) (t + 1) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hΦ_norm : ‖deriv Φ_inf (x : ℂ)‖ ≤ C1 / 2 - 1 := by
        rw [hΦ_deriv_eq x, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb_pos]
        exact hG_norm_bd t ht x hx1
      have h_tri : ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖ ≤ ‖deriv Φ_inf (x : ℂ)‖ + ε_d := by
        calc ‖deriv (Ψ_seq (φ k)) (x : ℂ)‖
            = ‖(deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)) + deriv Φ_inf (x : ℂ)‖ := by ring_nf
          _ ≤ ‖deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)‖ + ‖deriv Φ_inf (x : ℂ)‖ := norm_add_le _ _
          _ ≤ ε_d + ‖deriv Φ_inf (x : ℂ)‖ := add_le_add h_cauchy le_rfl
          _ = ‖deriv Φ_inf (x : ℂ)‖ + ε_d := add_comm _ _
      have hε1 : ε_d ≤ 1 := min_le_left _ _
      linarith
    · have hx_half : x ∈ Icc (D.tm - 1 / 2) (D.tm + 1 / 2) :=
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have h_cauchy := hcauchy_pt D.tm_mem x hx_half
      have hΦ_re : (deriv Φ_inf (x : ℂ)).re ≤ -4 * κ_star := by
        rw [hΦ_deriv_eq x, Complex.re_ofReal_mul]
        exact hG_slope x hx
      have h_re_diff : (deriv (Ψ_seq (φ k)) (x : ℂ) - deriv Φ_inf (x : ℂ)).re ≤ ε_d :=
        (abs_le.mp ((Complex.abs_re_le_norm _).trans h_cauchy)).2
      simp only [Complex.sub_re] at h_re_diff
      have hεk : ε_d ≤ 2 * κ_star := min_le_right _ _
      linarith
  obtain ⟨k, hk⟩ := eventually_atTop.mp (hev_uT.and hev_deriv)
  exact (hspec (φ k)).2.2.2.2.2.2.2.2.2.2 ⟨(hk k le_rfl).1, (hk k le_rfl).2.1, (hk k le_rfl).2.2⟩

/-- info: 'FormalResearch.SignUncertainty.hankel_quant_c1_multilevel_typeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_quant_c1_multilevel_typeI

end FormalResearch.SignUncertainty

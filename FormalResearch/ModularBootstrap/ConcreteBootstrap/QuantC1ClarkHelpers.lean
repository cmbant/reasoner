module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy

/-!
# Helpers for the Clark `TE.0'` stability argument (`QuantC1Clark*`)

Normal-families diagonal extraction on `ℂ`, the type-(II) real-axis tail bounds and the
symmetric-interval criterion for `L¹`, restated for the Clark pairs. These are the helpers of
`QuantC1Airy` (where they are file-private) under `clark*` names.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special

lemma clarkTail_norm_le
    {Ψ : ℂ → ℂ} {C_0 ς A B : ℝ}
    (hC0 : 0 < C_0) (hς : 0 ≤ ς) (hς_half : ς ≤ 1 / 2)
    (h1A : 1 ≤ A) (hAB : A ≤ B)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc A B))
    (hΨ_env : ∀ x : ℝ, 0 < x → x ≤ B →
      ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς * √x) * x⁻¹) :
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
    have hsqrt_le : √x ≤ x := by
      calc √x = √x * 1 := (mul_one _).symm
        _ ≤ √x * √x := mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hx_ge1) (Real.sqrt_nonneg _)
        _ = x := Real.mul_self_sqrt hx_pos.le
    have hx32 : x ≤ x ^ (3 / 2 : ℝ) := by
      simpa [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx_ge1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hcpow32 : ((x : ℂ) ^ (3 / 2 : ℂ)).re = x ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hx_pos.le,
        Complex.ofReal_re]
    have henv : airyEnv (x : ℂ) * Real.exp (ς * √x) ≤ Real.exp (-(5 / 6 : ℝ) * x) := by
      unfold airyEnv
      rw [hcpow32, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hςx : ς * √x ≤ (1 / 2 : ℝ) * x := by nlinarith
      linarith
    have hxinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx_ge1
    have hae_nn : 0 ≤ airyEnv (x : ℂ) * Real.exp (ς * √x) :=
      mul_nonneg (airyEnv_pos (x : ℂ)).le (Real.exp_pos _).le
    calc ‖Ψ (x : ℂ)‖ ≤ C_0 * (airyEnv (x : ℂ) * Real.exp (ς * √x)) * x⁻¹ := by
          simpa [mul_assoc] using hΨ_env x hx_pos hx.2
      _ ≤ C_0 * Real.exp (-(5 / 6 : ℝ) * x) * 1 := by gcongr
      _ = f_env x := by dsimp [f_env]; ring
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

lemma clarkTail_lt_quarter
    {Ψ : ℂ → ℂ} {C_0 ς A B : ℝ}
    (hC0 : 0 < C_0) (hς : 0 ≤ ς) (hς_half : ς ≤ 1 / 2)
    (hA_lo : quantC1_U0 C_0 ≤ A) (hAB : A ≤ B)
    (hΨ_cont : ContinuousOn (fun x : ℝ => Ψ (x : ℂ)) (Icc A B))
    (hΨ_env : ∀ x : ℝ, 0 < x → x ≤ B →
      ‖Ψ (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς * √x) * x⁻¹) :
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
  have htail := clarkTail_norm_le hC0 hς hς_half h1_le_A hAB hΨ_cont hΨ_env
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

lemma clarkArzelaSingleBall
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
    · rw [mem_closedBall_zero_iff, FunLike.coe_zero, Pi.zero_apply, norm_zero]
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
    · simp only [FunLike.coe_zero, Pi.zero_apply, dist_self]
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

lemma clarkArzelaDiagonal
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
        clarkArzelaSingleBall (F := fun n => F (ψ n)) hr_pos (hM (m + 1)) hAn' hBd'
      let α := Classical.choose hex
      let g := Classical.choose (Classical.choose_spec hex)
      have hspec := Classical.choose_spec (Classical.choose_spec hex)
      exact ⟨ψ ∘ α, ⟨hψ_mono.comp hspec.1, g, hspec.2⟩, α, hspec.1, rfl⟩
  let ψ0_ex := clarkArzelaSingleBall (F := F) (r := 1) (M := M 0) (N₀ := K 0) zero_lt_one (hM 0)
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

lemma clarkIntegrable_of_symm_norm_le {f : ℝ → ℂ} {C : ℝ}
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
            ∫⁻ x in Ioc (-N : ℝ) (N : ℝ), ‖‖f x‖‖ₑ by simp [eNorm_norm],
        ← MeasureTheory.ofReal_integral_norm_eq_lintegral_eNorm hint_on, intervalIntegral.integral_of_le hle]
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
    hf_cont.eNorm.measurable.indicator measurableSet_Ioc
  have hfin : ∫⁻ x : ℝ, ‖f x‖ₑ ≤ ENNReal.ofReal C := by
    have h_eq_sup : ∀ x : ℝ, ‖f x‖ₑ =
        ⨆ N : ℕ, (Ioc (-N : ℝ) (N : ℝ)).indicator (fun y => ‖f y‖ₑ) x := fun x => by
      rw [← congrFun hsup x, iSup_apply]
    rw [lintegral_congr h_eq_sup, lintegral_iSup h_meas hmono]
    exact iSup_le h_lint_le
  exact ⟨hf_cont.aestronglyMeasurable, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top⟩

end FormalResearch.ModularBootstrap.ConcreteBootstrap

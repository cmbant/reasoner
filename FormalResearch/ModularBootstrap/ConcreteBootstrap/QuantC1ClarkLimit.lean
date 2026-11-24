module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1ClarkBasic

/-!
# Normal-families limit for the Clark `TE.0'` stability (`teb:quant_c1_hb`, type (II))

For a sequence of type-(II) test functions `Ψ_n` at parameters `c'_n → ∞` with Clark parameters
`γ_n → γ_∞` (`γ = cot α`, zeros of `Ai' - γ Ai`), a subsequence converges locally uniformly on `ℂ`
to an entire `Φ` satisfying every hypothesis of the Clark two-node theorem at `γ_∞`:
`Φ ∈ L¹`, envelope, real on `ℝ`, `∫ Φ ≤ 0`, `Φ(z₁(γ_∞)) ≥ 0`, `Φ ≥ 0` on `(-∞, z₂(γ_∞)]`, `Φ ≢ 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special FormalResearch.SignUncertainty

/-- Uniform convergence on the balls `closedBall 0 (m+1)` and a continuous limit give
`F_{φ k}(w_k) → Φ(w_∞)` along any convergent sequence `w_k → w_∞`. -/
lemma clark_unif_tendsto_comp {F : ℕ → ℂ → ℂ} {Φ : ℂ → ℂ} {φ : ℕ → ℕ}
    (hU : ∀ m : ℕ, TendstoUniformlyOn (fun k => F (φ k)) Φ atTop (closedBall (0 : ℂ) ((m : ℝ) + 1)))
    (hΦ : Continuous Φ) {w : ℕ → ℂ} {wlim : ℂ} (hw : Tendsto w atTop (𝓝 wlim)) :
    Tendsto (fun k => F (φ k) (w k)) atTop (𝓝 (Φ wlim)) := by
  set m : ℕ := ⌈‖wlim‖⌉₊ with hm
  have hmem_ball : wlim ∈ ball (0 : ℂ) ((m : ℝ) + 1) := by
    rw [mem_ball_zero_iff]; linarith [Nat.le_ceil ‖wlim‖]
  have hmem : closedBall (0 : ℂ) ((m : ℝ) + 1) ∈ 𝓝 wlim :=
    mem_of_superset (isOpen_ball.mem_nhds hmem_ball) ball_subset_closedBall
  have hg : Tendsto w atTop (𝓝[closedBall (0 : ℂ) ((m : ℝ) + 1)] wlim) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw, hw hmem⟩
  exact (hU m).tendsto_comp hΦ.continuousWithinAt hg


/-- **Normal-families limit** (Clark `TE.0'`): see the module docstring. -/
theorem clark_limit_extraction {C_0 : ℝ} (hC0 : 0 < C_0)
    (R_dom ς δ_lobe ρ : ℝ → ℝ)
    (hR_lim : Tendsto R_dom atTop atTop)
    (hς_nn : ∀ᶠ c in atTop, 0 ≤ ς c) (hς_lim : Tendsto ς atTop (𝓝 0))
    (hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c) (hδ_lim : Tendsto δ_lobe atTop (𝓝 0))
    (hρ_lim : Tendsto ρ atTop (𝓝 0))
    {c'_seq : ℕ → ℝ} (hc'_atTop : Tendsto c'_seq atTop atTop)
    {γ_seq : ℕ → ℝ} {γlim : ℝ} (hγ : Tendsto γ_seq atTop (𝓝 γlim))
    {Ψ_seq : ℕ → ℂ → ℂ} {uT_seq ũ_seq : ℕ → ℝ}
    (hspec : ∀ n, QuantC1ClarkHyp C_0 (R_dom (c'_seq n)) (ς (c'_seq n)) (δ_lobe (c'_seq n))
      (ρ (c'_seq n)) (γ_seq n) (Ψ_seq n) (uT_seq n) (ũ_seq n)) :
    ∃ (φ : ℕ → ℕ) (Φ_inf : ℂ → ℂ), StrictMono φ ∧
      (∀ m : ℕ, TendstoUniformlyOn (fun k => Ψ_seq (φ k)) Φ_inf atTop
        (closedBall (0 : ℂ) ((m : ℝ) + 1))) ∧
      Differentiable ℂ Φ_inf ∧ Integrable (fun x : ℝ => Φ_inf (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖Φ_inf u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (Φ_inf (x : ℂ)).im = 0) ∧ (∫ x : ℝ, (Φ_inf (x : ℂ)).re) ≤ 0 ∧
      0 ≤ (Φ_inf (airyClarkNode γlim 1 : ℂ)).re ∧
      (∀ x : ℝ, x ≤ airyClarkNode γlim 2 → 0 ≤ (Φ_inf (x : ℂ)).re) ∧ (∃ z : ℂ, Φ_inf z ≠ 0) := by
  have hR_seq : Tendsto (fun n => R_dom (c'_seq n)) atTop atTop := hR_lim.comp hc'_atTop
  have hς_seq_nn : ∀ᶠ n in atTop, 0 ≤ ς (c'_seq n) := hc'_atTop.eventually hς_nn
  have hς_seq_lim : Tendsto (fun n => ς (c'_seq n)) atTop (𝓝 0) := hς_lim.comp hc'_atTop
  have hδ_seq_nn : ∀ᶠ n in atTop, 0 ≤ δ_lobe (c'_seq n) := hc'_atTop.eventually hδ_nn
  have hδ_seq_lim : Tendsto (fun n => δ_lobe (c'_seq n)) atTop (𝓝 0) := hδ_lim.comp hc'_atTop
  let U₀ : ℝ := quantC1_U0 C_0
  have hU0_ge1 : 1 ≤ U₀ := one_le_quantC1_U0 C_0
  -- `xlo = a₂` lies below every `u_T`, since `a₂ < z₂(γ) < u_T`
  let xlo : ℝ := airyZero 2
  have hxlo_neg : xlo < 0 := airyZero_neg 2
  have hxlo_lt : ∀ n, xlo < uT_seq n := fun n =>
    (airyZero_lt_airyClarkNode (n := 2) (by norm_num) (γ_seq n)).trans (hspec n).lt_uT

  let M_seq : ℕ → ℝ := fun m =>
    8 * Real.exp (7 / 2) * C_0 * (1 + ((m : ℝ) + 2)) ^ (1 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * ((m : ℝ) + 2) ^ (3 / 2 : ℝ))
  have hM_nn : ∀ m, 0 ≤ M_seq m := fun m => by dsimp [M_seq]; positivity
  have hK_ex : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ((m : ℝ) + 4) ≤ R_dom (c'_seq n) ∧
      0 ≤ ς (c'_seq n) ∧ ς (c'_seq n) ≤ 1 / 2 ∧
      ς (c'_seq n) * √((m : ℝ) + 4) ≤ 1 ∧
      0 ≤ δ_lobe (c'_seq n) ∧ δ_lobe (c'_seq n) ≤ 1 / 4 ∧
      U₀ ≤ R_dom (c'_seq n) := by
    intro m
    have hev_R : ∀ᶠ n in atTop, max ((m : ℝ) + 4) U₀ ≤ R_dom (c'_seq n) :=
      hR_seq (eventually_ge_atTop _)
    have hev_ςhalf : ∀ᶠ n in atTop, ς (c'_seq n) ≤ 1 / 2 :=
      hς_seq_lim (Iic_mem_nhds (by norm_num))
    have hev_ς1 : ∀ᶠ n in atTop, ς (c'_seq n) * √((m : ℝ) + 4) ≤ 1 := by
      have ht : Tendsto (fun n => ς (c'_seq n) * √((m : ℝ) + 4)) atTop (𝓝 (0 * √((m : ℝ) + 4))) :=
        hς_seq_lim.mul_const _
      rw [zero_mul] at ht
      exact ht (Iic_mem_nhds one_pos)
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ 1 / 4 :=
      hδ_seq_lim (Iic_mem_nhds (by norm_num))
    have hev_all := hev_R.and (hς_seq_nn.and (hev_ςhalf.and (hev_ς1.and (hδ_seq_nn.and hev_δ))))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev_all
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hR1, hς0, hςh, hςs, hδ0, hδq⟩ := hN n hn
    exact ⟨(le_max_left _ _).trans hR1, hς0, hςh, hςs, hδ0, hδq, (le_max_right _ _).trans hR1⟩
  choose K_seq hK_spec using hK_ex
  have hAn_seq : ∀ m, ∀ n ≥ K_seq m,
      AnalyticOnNhd ℂ (Ψ_seq n) (closedBall (0 : ℂ) ((m : ℝ) + 2)) := by
    intro m n hn
    exact (hspec n).analytic.mono (closedBall_subset_closedBall (by linarith [(hK_spec m n hn).1]))
  have hBd_seq : ∀ m, ∀ n ≥ K_seq m,
      ∀ z ∈ closedBall (0 : ℂ) ((m : ℝ) + 2), ‖Ψ_seq n z‖ ≤ M_seq m := by
    intro m n hn z hz
    have hsp := hK_spec m n hn
    have hR1 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have hR_dom : ((m : ℝ) + 2) + 2 ≤ R_dom (c'_seq n) := by linarith [hsp.1]
    have hς_one : ς (c'_seq n) * √(((m : ℝ) + 2) + 2) ≤ 1 := by
      simpa [show ((m : ℝ) + 2) + 2 = (m : ℝ) + 4 by ring] using hsp.2.2.2.1
    exact typeII_cut_bound hR1 hR_dom hC0 hsp.2.1 (hspec n).analytic (hspec n).env hς_one hz
  obtain ⟨φ, Φ_inf, hφ_mono, hΦ_unif⟩ := clarkArzelaDiagonal hM_nn hAn_seq hBd_seq
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
  -- Growth bound on `Φ_inf` from `typeII_disc_avg_bound`
  let C_env : ℝ := 8 * Real.exp (5 / 2) * C_0 * Real.exp 1
  have hC_env_nn : 0 ≤ C_env := by dsimp [C_env]; positivity
  have hΦ_env : ∀ u : ℂ, ‖Φ_inf u‖ ≤ C_env * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
    intro u
    let m : ℕ := ⌈‖u‖⌉₊
    have hu_m : u ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff]; linarith [Nat.le_ceil ‖u‖]
    have ht_pt : Tendsto (fun k => ‖Ψ_seq (φ k) u‖) atTop (𝓝 ‖Φ_inf u‖) :=
      ((hΦ_unif m).tendsto_at hu_m).norm
    have hev_bd : ∀ᶠ k in atTop,
        ‖Ψ_seq (φ k) u‖ ≤ C_env * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
      have hsp := hK_spec m (φ k) (hN k hk)
      have hu_norm : u ∈ closedBall (0 : ℂ) ‖u‖ := mem_closedBall_zero_iff.mpr le_rfl
      have hR_dom : ‖u‖ + 2 ≤ R_dom (c'_seq (φ k)) := by
        have := Nat.le_ceil ‖u‖
        linarith [hsp.1]
      have hdisc := (typeII_disc_avg_bound (norm_nonneg u) hR_dom hC0 hsp.2.1
        (hspec (φ k)).analytic (hspec (φ k)).env hu_norm).1
      have hςu : ς (c'_seq (φ k)) * √(‖u‖ + 2) ≤ 1 := by
        have hsqrt : √(‖u‖ + 2) ≤ √((m : ℝ) + 4) :=
          Real.sqrt_le_sqrt (by linarith [Nat.le_ceil ‖u‖])
        calc ς (c'_seq (φ k)) * √(‖u‖ + 2) ≤ ς (c'_seq (φ k)) * √((m : ℝ) + 4) :=
              mul_le_mul_of_nonneg_left hsqrt hsp.2.1
          _ ≤ 1 := hsp.2.2.2.1
      have hexp1 : Real.exp (ς (c'_seq (φ k)) * √(‖u‖ + 2)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hςu
      have henv_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
      calc ‖Ψ_seq (φ k) u‖
          ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp (ς (c'_seq (φ k)) * √(‖u‖ + 2)) *
              airyEnv u * (1 + ‖u‖) ^ (1 / 2 : ℝ) := hdisc
        _ ≤ 8 * Real.exp (5 / 2) * C_0 * Real.exp 1 * airyEnv u * (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
            gcongr
        _ = C_env * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by dsimp [C_env]; ring
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
      exact (hspec (φ k)).real x hx_dom
    exact tendsto_nhds_unique ht_im (tendsto_const_nhds.congr' (hev0.mono fun _ hk => hk.symm))
  -- `L¹` integrability and symmetric-interval norm ≤ 1 on `ℝ`
  have hΦ_symm_norm : ∀ N : ℕ, ∫ x in (-N : ℝ)..(N : ℝ), ‖Φ_inf (x : ℂ)‖ ≤ 1 := by
    intro N
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < (ε / 2) / (2 * (N : ℝ) + 1) := div_pos (half_pos hε) (by positivity)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif N) ((ε / 2) / (2 * (N : ℝ) + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ ε / 2 :=
      hδ_seq_lim (Iic_mem_nhds (half_pos hε))
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq N))).and
        (hφ_atTop.eventually hev_δ)))
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
        ‖Φ_inf (x : ℂ)‖ ≤ ‖Ψ_seq (φ k) (x : ℂ)‖ + (ε / 2) / (2 * (N : ℝ) + 1) := by
      intro x hx
      have hd := hk_unif (x : ℂ) (h_diff_ball x hx)
      rw [dist_eq_norm] at hd
      calc ‖Φ_inf (x : ℂ)‖ = ‖(Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)) + Ψ_seq (φ k) (x : ℂ)‖ := by ring_nf
        _ ≤ ‖Φ_inf (x : ℂ) - Ψ_seq (φ k) (x : ℂ)‖ + ‖Ψ_seq (φ k) (x : ℂ)‖ := norm_add_le _ _
        _ ≤ (ε / 2) / (2 * (N : ℝ) + 1) + ‖Ψ_seq (φ k) (x : ℂ)‖ := add_le_add hd.le le_rfl
        _ = ‖Ψ_seq (φ k) (x : ℂ)‖ + (ε / 2) / (2 * (N : ℝ) + 1) := add_comm _ _
    have hcΦ : ContinuousOn (fun x : ℝ => ‖Φ_inf (x : ℂ)‖) (Icc (-N : ℝ) (N : ℝ)) :=
      (hΦ_diff.continuous.comp continuous_ofReal).norm.continuousOn
    have hcΨ : ContinuousOn (fun x : ℝ => ‖Ψ_seq (φ k) (x : ℂ)‖)
        (Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k)))) :=
      (((hspec (φ k)).analytic.continuousOn).comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hx).norm
    have hsub_N : Icc (-N : ℝ) (N : ℝ) ⊆ Icc (-R_dom (c'_seq (φ k))) (R_dom (c'_seq (φ k))) :=
      Icc_subset_Icc (by linarith) hNR
    have hiΦ := hcΦ.intervalIntegrable_of_Icc (μ := volume) hle
    have hiΨ_N := (hcΨ.mono hsub_N).intervalIntegrable_of_Icc (μ := volume) hle
    have hi_const : IntervalIntegrable (fun _ : ℝ => (ε / 2) / (2 * (N : ℝ) + 1)) volume (-N : ℝ) (N : ℝ) :=
      intervalIntegrable_const
    have h_int1 : ∫ x in (-N : ℝ)..(N : ℝ), ‖Φ_inf (x : ℂ)‖ ≤
        ∫ x in (-N : ℝ)..(N : ℝ), (‖Ψ_seq (φ k) (x : ℂ)‖ + (ε / 2) / (2 * (N : ℝ) + 1)) :=
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
    have hΨ_L1 := (hspec (φ k)).l1
    have h_err : ((N : ℝ) - (-N : ℝ)) * ((ε / 2) / (2 * (N : ℝ) + 1)) ≤ ε / 2 := by
      have h1 : (N : ℝ) - (-N : ℝ) = 2 * (N : ℝ) := by ring
      rw [h1, mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1)]
      nlinarith
    linarith
  have hΦ_int : Integrable (fun x : ℝ => Φ_inf (x : ℂ)) :=
    clarkIntegrable_of_symm_norm_le (hΦ_diff.continuous.comp continuous_ofReal) hΦ_symm_norm

  -- Nonnegativity on `(-∞, z₂(γ_∞)]`
  have hΦ_pos_lt : ∀ x : ℝ, x < airyClarkNode γlim 2 → 0 ≤ (Φ_inf (x : ℂ)).re := by
    intro x hx
    let m : ℕ := ⌈|x|⌉₊
    have hx_m : (x : ℂ) ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith [Nat.le_ceil |x|]
    have ht_re : Tendsto (fun k => (Ψ_seq (φ k) (x : ℂ)).re) atTop (𝓝 (Φ_inf (x : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp ((hΦ_unif m).tendsto_at hx_m)
    have hz2 : Tendsto (fun k => airyClarkNode (γ_seq (φ k)) 2) atTop
        (𝓝 (airyClarkNode γlim 2)) :=
      ((continuous_airyClarkNode (n := 2) (by norm_num)).tendsto γlim).comp (hγ.comp hφ_atTop)
    have hev : ∀ᶠ k in atTop, 0 ≤ (Ψ_seq (φ k) (x : ℂ)).re := by
      have hlt : ∀ᶠ k in atTop, x < airyClarkNode (γ_seq (φ k)) 2 := hz2 (Ioi_mem_nhds hx)
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hφ_atTop.eventually (eventually_ge_atTop (K_seq m)))
      obtain ⟨N', hN'⟩ := eventually_atTop.mp hlt
      refine eventually_atTop.mpr ⟨max N N', fun k hk => ?_⟩
      have hR := (hK_spec m (φ k) (hN k ((le_max_left _ _).trans hk))).1
      have hx_lo : -R_dom (c'_seq (φ k)) ≤ x := by linarith [(abs_le.mp (Nat.le_ceil |x|)).1]
      have hx_hi : x ≤ uT_seq (φ k) :=
        ((hN' k ((le_max_right _ _).trans hk)).trans (hspec (φ k)).lt_uT).le
      exact (hspec (φ k)).nonneg x ⟨hx_lo, hx_hi⟩
    exact ge_of_tendsto ht_re hev
  have hΦ_pos_z2 : ∀ x : ℝ, x ≤ airyClarkNode γlim 2 → 0 ≤ (Φ_inf (x : ℂ)).re := by
    intro x hx
    have hcl : x ∈ closure (Iio (airyClarkNode γlim 2)) := by rw [closure_Iio]; exact hx
    have hclosed : IsClosed {y : ℝ | 0 ≤ (Φ_inf (y : ℂ)).re} :=
      isClosed_le continuous_const
        (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal))
    exact hclosed.closure_subset_iff.mpr (fun y hy => hΦ_pos_lt y hy) hcl

  -- Nonpositive total integral `∫_ℝ (Φ_inf x).re ≤ 0`
  have hΦ_total_int_le : ∫ x : ℝ, (Φ_inf (x : ℂ)).re ≤ 0 := by
    have h_symm_re : ∀ N : ℕ, ⌈|xlo|⌉₊ + 1 ≤ N →
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
      have hNxlo : |xlo| + 1 ≤ (N : ℝ) := by
        have := Nat.le_ceil |xlo|
        have : (⌈|xlo|⌉₊ + 1 : ℝ) ≤ N := by exact_mod_cast hN_ge
        linarith
      have hN_uT : -(N : ℝ) ≤ uT_seq (φ k) := by
        have := (abs_le.mp (le_refl |xlo|)).1
        linarith [hxlo_lt (φ k)]
      have hAn_k := (hspec (φ k)).analytic
      have hReal_k := (hspec (φ k)).real
      have hEnv_k := (hspec (φ k)).env
      have hxlo_lt_k : xlo < uT_seq (φ k) := hxlo_lt (φ k)
      have huT_le_k := (hspec (φ k)).uT_le
      have hPos_k := (hspec (φ k)).nonneg
      have hL1_k := (hspec (φ k)).l1
      have hTail_k := (hspec (φ k)).tail
      have hTop_k := (hspec (φ k)).top
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
      have h_env_pos : ∀ x : ℝ, 0 < x → x ≤ R_dom (c'_seq (φ k)) →
          ‖Ψ_seq (φ k) (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * √x) * x⁻¹ := by
        intro x hx0 hxR
        have hu : (x : ℂ) ∈ closedBall (0 : ℂ) (R_dom (c'_seq (φ k))) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxR
        have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by
          intro h0; simp only [Complex.ofReal_re] at h0; linarith
        have h1 := hEnv_k (x : ℂ) hu hcut
        have hcp : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
          rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
            ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
        have hnorm_inv : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = x⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hcp,
            Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx0.le]
        calc ‖Ψ_seq (φ k) (x : ℂ)‖
            ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * ((x : ℂ) ^ (1 / 2 : ℂ)).re) *
                (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
              simpa only [mul_assoc] using h1
          _ = C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * √x) * x⁻¹ := by
              rw [hnorm_inv, hcp]
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
        have h_norm_tail := clarkTail_norm_le hC0 hsp.2.1 hsp.2.2.1 h1N hNR
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
    exact le_of_tendsto_of_tendsto ht h_exp_tend (eventually_atTop.mpr ⟨⌈|xlo|⌉₊ + 1, h_symm_re⟩)
  -- Non-vanishing via negative mass `1/4 ≤ ∫_{xlo}^{U₀} max 0 (-(Φ_inf x).re)`
  have hΦ_neg_mass : (1 / 4 : ℝ) ≤ ∫ x in xlo..U₀, max 0 (-(Φ_inf (x : ℂ)).re) := by
    have hxlo_le_U0 : xlo ≤ U₀ := by linarith [hU0_ge1]
    let m₀ : ℕ := ⌈max |xlo| U₀⌉₊
    have hm0_ge : max |xlo| U₀ ≤ (m₀ : ℝ) := Nat.le_ceil _
    have hΦ_m_cont : ContinuousOn (fun x : ℝ => max 0 (-(Φ_inf (x : ℂ)).re)) (Icc xlo U₀) :=
      ContinuousOn.sup continuousOn_const
        (Complex.continuous_re.comp (hΦ_diff.continuous.comp continuous_ofReal)).neg.continuousOn
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < (ε / 2) / (U₀ - xlo + 1) := div_pos (half_pos hε) (by linarith)
    have h_unif := Metric.tendstoUniformlyOn_iff.mp (hΦ_unif m₀) ((ε / 2) / (U₀ - xlo + 1)) hε'
    have hev_δ : ∀ᶠ n in atTop, δ_lobe (c'_seq n) ≤ min (1 / 4) (ε / 2) :=
      hδ_seq_lim (Iic_mem_nhds (lt_min (by norm_num) (half_pos hε)))
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
      (h_unif.and ((hφ_atTop.eventually (eventually_ge_atTop (K_seq m₀))).and (hφ_atTop.eventually hev_δ)))
    let k := K₀
    obtain ⟨hk_unif, hk_K, hk_δ⟩ := hK₀ k le_rfl
    have hsp := hK_spec m₀ (φ k) hk_K
    have hAn_k := (hspec (φ k)).analytic
    have hReal_k := (hspec (φ k)).real
    have hEnv_k := (hspec (φ k)).env
    have hxlo_lt_k : xlo < uT_seq (φ k) := hxlo_lt (φ k)
    have huT_le_k := (hspec (φ k)).uT_le
    have hPos_k := (hspec (φ k)).nonneg
    have hL1_k := (hspec (φ k)).l1
    have hTail_k := (hspec (φ k)).tail
    have hTop_k := (hspec (φ k)).top
    have h_env_pos : ∀ x : ℝ, 0 < x → x ≤ R_dom (c'_seq (φ k)) →
        ‖Ψ_seq (φ k) (x : ℂ)‖ ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * √x) * x⁻¹ := by
      intro x hx0 hxR
      have hu : (x : ℂ) ∈ closedBall (0 : ℂ) (R_dom (c'_seq (φ k))) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxR
      have hcut : ¬ ((x : ℂ).im = 0 ∧ (x : ℂ).re ≤ 0) := by
        intro h0; simp only [Complex.ofReal_re] at h0; linarith
      have h1 := hEnv_k (x : ℂ) hu hcut
      have hcp : ((x : ℂ) ^ (1 / 2 : ℂ)).re = √x := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_cpow hx0.le, Complex.ofReal_re, Real.sqrt_eq_rpow]
      have hnorm_inv : ‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹ = x⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hcp,
          Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, ← mul_inv, Real.mul_self_sqrt hx0.le]
      calc ‖Ψ_seq (φ k) (x : ℂ)‖
          ≤ C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * ((x : ℂ) ^ (1 / 2 : ℂ)).re) *
              (‖(x : ℂ)‖ ^ (-(1 / 2 : ℝ)) * (((x : ℂ) ^ (1 / 2 : ℂ)).re)⁻¹) := by
            simpa only [mul_assoc] using h1
        _ = C_0 * airyEnv (x : ℂ) * Real.exp (ς (c'_seq (φ k)) * √x) * x⁻¹ := by
            rw [hnorm_inv, hcp]
    have huT_le_U0 : uT_seq (φ k) ≤ U₀ := by
      have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
      have hxlo_ge_R : -R_dom (c'_seq (φ k)) ≤ xlo := by
        linarith [(abs_le.mp ((le_max_left |xlo| U₀).trans hm0_ge)).1]
      have hcΨ_dom : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
          (Icc (uT_seq (φ k)) (R_dom (c'_seq (φ k)))) :=
        hAn_k.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [hx.1, hxlo_lt_k], hx.2⟩
      exact quantC1_uT_le hC0 hsp.2.1 hsp.2.2.1 hsp.2.2.2.2.2.1 huT_le_k hcΨ_dom h_env_pos hTail_k
    have hU0_le_R : U₀ ≤ R_dom (c'_seq (φ k)) := hsp.2.2.2.2.2.2
    have hcΨ_a1R : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ))
        (Icc xlo (R_dom (c'_seq (φ k)))) :=
      hAn_k.continuousOn.comp continuous_ofReal.continuousOn fun x hx => by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hmR : (m₀ : ℝ) + 4 ≤ R_dom (c'_seq (φ k)) := hsp.1
        have hxlo_ge_R : -R_dom (c'_seq (φ k)) ≤ xlo := by
          linarith [(abs_le.mp ((le_max_left |xlo| U₀).trans hm0_ge)).1]
        exact abs_le.mpr ⟨hxlo_ge_R.trans hx.1, hx.2⟩
    have hcΨ_U0R : ContinuousOn (fun x : ℝ => Ψ_seq (φ k) (x : ℂ)) (Icc U₀ (R_dom (c'_seq (φ k)))) :=
      hcΨ_a1R.mono (Icc_subset_Icc_left hxlo_le_U0)
    have h_tail_q : ∫ x in U₀..(R_dom (c'_seq (φ k))), max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) < 1 / 4 :=
      clarkTail_lt_quarter hC0 hsp.2.1 hsp.2.2.1 le_rfl hU0_le_R hcΨ_U0R h_env_pos
    have h_m_cont_all : ContinuousOn (fun x : ℝ => max 0 (-(Ψ_seq (φ k) (x : ℂ)).re))
        (Icc xlo (R_dom (c'_seq (φ k)))) :=
      ContinuousOn.sup continuousOn_const (Complex.continuous_re.comp_continuousOn hcΨ_a1R).neg
    have h_split := intervalIntegral.integral_add_adjacent_intervals
      ((h_m_cont_all.mono (Icc_subset_Icc hxlo_lt_k.le hU0_le_R)).intervalIntegrable_of_Icc
        (μ := volume) huT_le_U0)
      ((h_m_cont_all.mono (Icc_subset_Icc_left hxlo_le_U0)).intervalIntegrable_of_Icc
        (μ := volume) hU0_le_R)
    have h_uT_U0 : ∫ x in (uT_seq (φ k))..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
        ∫ x in xlo..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      rw [intervalIntegral.integral_of_le huT_le_U0, intervalIntegral.integral_of_le hxlo_le_U0]
      exact setIntegral_mono_set
        (((h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).integrableOn_Icc (μ := volume)).mono_set
          Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ => le_max_left _ _)
        (Eventually.of_forall fun _ hx => Ioc_subset_Ioc_left hxlo_lt_k.le hx)
    have h_Ψ_band : 1 / 4 - ε / 2 ≤ ∫ x in xlo..U₀, max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) := by
      have h2 : δ_lobe (c'_seq (φ k)) ≤ ε / 2 := hk_δ.trans (min_le_right _ _)
      linarith
    have h_pt_m : ∀ x ∈ Icc xlo U₀,
        max 0 (-(Ψ_seq (φ k) (x : ℂ)).re) ≤
          max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - xlo + 1) := by
      intro x hx
      have hx_ball : (x : ℂ) ∈ closedBall (0 : ℂ) ((m₀ : ℝ) + 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        have hax : |x| ≤ max |xlo| U₀ := by
          rcases le_total x 0 with hx0 | hx0
          · rw [abs_of_nonpos hx0]
            calc -x ≤ -xlo := neg_le_neg hx.1
              _ ≤ |xlo| := neg_le_abs xlo
              _ ≤ max |xlo| U₀ := le_max_left _ _
          · rw [abs_of_nonneg hx0]
            exact hx.2.trans (le_max_right _ _)
        linarith [hax.trans hm0_ge]
      have hd := (hk_unif (x : ℂ) hx_ball).le
      rw [dist_eq_norm] at hd
      have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd)).2
      simp only [Complex.sub_re] at hre
      have hneg : -(Ψ_seq (φ k) (x : ℂ)).re ≤ -(Φ_inf (x : ℂ)).re + (ε / 2) / (U₀ - xlo + 1) := by linarith
      have h0_le : (0 : ℝ) ≤ max 0 (-(Φ_inf (x : ℂ)).re) + (ε / 2) / (U₀ - xlo + 1) :=
        add_nonneg (le_max_left _ _) (div_nonneg (half_pos hε).le (by linarith))
      exact max_le h0_le (hneg.trans (add_le_add (le_max_right _ _) le_rfl))
    have h_m_int_Ψ := (h_m_cont_all.mono (Icc_subset_Icc_right hU0_le_R)).intervalIntegrable_of_Icc
      (μ := volume) hxlo_le_U0
    have h_m_int_Φ := hΦ_m_cont.intervalIntegrable_of_Icc (μ := volume) hxlo_le_U0
    have h_int_m := intervalIntegral.integral_mono_on hxlo_le_U0 h_m_int_Ψ
      (h_m_int_Φ.add intervalIntegrable_const) h_pt_m
    rw [intervalIntegral.integral_add h_m_int_Φ intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at h_int_m
    have h_err : (U₀ - xlo) * ((ε / 2) / (U₀ - xlo + 1)) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hΦ_ne : ∃ z : ℂ, Φ_inf z ≠ 0 := by
    by_contra h_all0
    push Not at h_all0
    have h0 : ∫ x in xlo..U₀, max 0 (-(Φ_inf (x : ℂ)).re) = 0 := by
      simp [h_all0]
    linarith [hΦ_neg_mass]
  -- Nonnegativity at the prescribed node `z₁(γ_∞)`
  have hΦ_node : 0 ≤ (Φ_inf (airyClarkNode γlim 1 : ℂ)).re := by
    have hz1 : Tendsto (fun k => airyClarkNode (γ_seq (φ k)) 1) atTop (𝓝 (airyClarkNode γlim 1)) :=
      ((continuous_airyClarkNode (n := 1) le_rfl).tendsto γlim).comp (hγ.comp hφ_atTop)
    have hρ : Tendsto (fun k => ρ (c'_seq (φ k))) atTop (𝓝 0) :=
      hρ_lim.comp (hc'_atTop.comp hφ_atTop)
    have h0 : Tendsto (fun k => ũ_seq (φ k) - airyClarkNode (γ_seq (φ k)) 1) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by
        simpa [Real.norm_eq_abs] using (hspec (φ k)).node_near) hρ
    have hũ : Tendsto (fun k => ũ_seq (φ k)) atTop (𝓝 (airyClarkNode γlim 1)) := by
      simpa using h0.add hz1
    have hw : Tendsto (fun k => ((ũ_seq (φ k) : ℝ) : ℂ)) atTop (𝓝 ((airyClarkNode γlim 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hũ
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      (clark_unif_tendsto_comp (F := Ψ_seq) hΦ_unif hΦ_diff.continuous hw)
    exact ge_of_tendsto ht (Eventually.of_forall fun k => (hspec (φ k)).node_nonneg)
  refine ⟨φ, Φ_inf, hφ_mono, hΦ_unif, hΦ_diff, hΦ_int, ⟨C_env, 1 / 2, hC_env_nn, hΦ_env⟩, hΦ_real,
    hΦ_total_int_le, hΦ_node, hΦ_pos_z2, hΦ_ne⟩

end FormalResearch.ModularBootstrap.ConcreteBootstrap

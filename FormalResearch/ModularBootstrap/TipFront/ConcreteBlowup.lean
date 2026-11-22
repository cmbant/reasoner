module

public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen
public import FormalResearch.ModularBootstrap.Blowup.PropositionT
public import FormalResearch.ModularBootstrap.ComplexBessel.BesselI0Sector

/-!
# Concrete `BlowupTest`, Unconditional Family Packages, and Concrete Theorems C, R1--R3

Constructs `BlowupTest virasoroStripBootstrapInputs c'` unconditionally from any weakly
feasible concrete test `virasoroProblem.IsWeaklyFeasible (c' / 12) T g` (`c_concrete ≤ c'`),
using the least nonnegative threshold `leastThreshold g := sInf {T ≥ 0 | ∀ t ≥ T, 0 ≤ g t}`,
and builds unconditional family packages and concrete versions of Theorems C and R1--R3:

* `leastThreshold`, `leastThreshold_nonneg`, `leastThreshold_le`, `leastThreshold_tail`:
  properties of the least nonnegative threshold `t₁(g)` (`blowup_limit.tex`, Proposition T).
* `kernelK_one_eq_KalphaC`, `virasoro_cardyV_eq_V_C`: agreement between the real crossing
  kernels `kernelK 1`, `virasoroProblem.cardyV` and the entire complex kernels `KalphaC`, `V_C`.
* `blowupTest_of_concrete`: concrete `BlowupTest virasoroStripBootstrapInputs c'` without any
  per-test analytic hypotheses (and `blowupTest_nonempty` from `virasoroProblem.feasible_nonempty`).
* `blowupFamilyPackage_of_concrete_tests`, `rigidityFamilyPackage_of_concrete_tests`:
  unconditional `BlowupFamilyPackage` and `RigidityFamilyPackage` for any asymptotic family
  of weakly feasible Virasoro tests (no `BesselI0Asymptotic`, no `StripBootstrapInputs`, no
  `hg_t1_zero`).
* `concrete_blowup_theorem_C`, `concrete_blowup_theorem_R1`, `concrete_blowup_theorem_R2`,
  `concrete_blowup_theorem_R3`: unconditional concrete theorems matching `blowup_limit.tex`,
  `local_airy_model.tex`, and `rigidity.tex`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Metric Set
open scoped Interval

namespace FormalResearch.ModularBootstrap.TipFront

open PoissonJensen Crossing Integration ComplexBessel FormalResearch.ArgPrinciple FormalResearch.Special

/-! ### 1. Least nonnegative threshold `t₁(g)` -/

/-- The least nonnegative nonnegativity threshold
`t₁(g) := inf {T ≥ 0 | ∀ t ≥ T, 0 ≤ g t}` (`blowup_limit.tex`, Proposition T). -/
noncomputable def leastThreshold (g : ℝ → ℝ) : ℝ :=
  sInf {T : ℝ | 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → 0 ≤ g t}

lemma leastThreshold_nonneg (g : ℝ → ℝ) : 0 ≤ leastThreshold g :=
  Real.sInf_nonneg fun _ h => h.1

lemma leastThreshold_le {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hg : ∀ t : ℝ, T ≤ t → 0 ≤ g t) :
    leastThreshold g ≤ T :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hT, hg⟩

lemma leastThreshold_tail {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) {T₀ : ℝ}
    (hnonneg₀ : ∀ t : ℝ, T₀ ≤ t → 0 ≤ g t) :
    ∀ t : ℝ, leastThreshold g ≤ t → 0 ≤ g t := by
  let S : Set ℝ := {T : ℝ | 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → 0 ≤ g t}
  have hS_ne : S.Nonempty := ⟨max 0 T₀, le_max_left _ _, fun t ht =>
    hnonneg₀ t ((le_max_right 0 T₀).trans ht)⟩
  have hS_bdd : BddBelow S := ⟨0, fun _ h => h.1⟩
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | hlt
  · have ht_nn : 0 ≤ leastThreshold g := leastThreshold_nonneg g
    let hex : ∀ n : ℕ, ∃ T ∈ S, T < leastThreshold g + 1 / (n + 1 : ℝ) := fun n =>
      exists_lt_of_csInf_lt hS_ne
        (lt_add_of_pos_right (leastThreshold g) (by positivity))
    let seq : ℕ → ℝ := fun n => (hex n).choose
    have hseq_mem : ∀ n : ℕ, seq n ∈ S := fun n => (hex n).choose_spec.1
    have hseq_lt : ∀ n : ℕ, seq n < leastThreshold g + 1 / (n + 1 : ℝ) := fun n =>
      (hex n).choose_spec.2
    have hseq_ge : ∀ n : ℕ, leastThreshold g ≤ seq n := fun n => csInf_le hS_bdd (hseq_mem n)
    have hseq_tendsto : Tendsto seq atTop (𝓝[Ici 0] (leastThreshold g)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (hseq_mem n).1⟩
      have h_upper : Tendsto (fun n : ℕ => leastThreshold g + 1 / (n + 1 : ℝ)) atTop
          (𝓝 (leastThreshold g)) := by
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop (R := ℝ) |>.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
        simpa using tendsto_const_nhds.add hinv
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
        hseq_ge (fun n => (hseq_lt n).le)
    have hg_tendsto : Tendsto (fun n => g (seq n)) atTop (𝓝 (g (leastThreshold g))) :=
      (hg_cont (leastThreshold g) ht_nn).tendsto.comp hseq_tendsto
    exact ge_of_tendsto hg_tendsto (Eventually.of_forall fun n => (hseq_mem n).2 (seq n) le_rfl)
  · obtain ⟨T, hT_mem, hT_lt⟩ := exists_lt_of_csInf_lt hS_ne hlt
    exact hT_mem.2 t hT_lt.le

/-! ### 2. Real-axis compatibility of `virasoroProblem.cardyV` and `V_C` -/

theorem kernelK_one_eq_KalphaC (α t : ℝ) :
    (Crossing.kernelK 1 α t : ℂ) = KalphaC (α : ℂ) (t : ℂ) := by
  unfold KalphaC
  rw [FormalResearch.Special.regularizedHGFun_zero_singleton]
  unfold Crossing.kernelK
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hsum : HasSum (fun k : ℕ => ((Crossing.kernelKTerm 1 α t k : ℝ) : ℂ))
      ((∑' k : ℕ, Crossing.kernelKTerm 1 α t k : ℝ) : ℂ) :=
    Complex.ofRealCLM.hasSum (Crossing.summable_kernelKTerm 1 α t).hasSum
  rw [← hsum.tsum_eq]
  refine tsum_congr fun k => ?_
  unfold Crossing.kernelKTerm
  simp only [Nat.add_sub_cancel]
  rw [add_comm (1 : ℂ) (k : ℂ), Complex.Gamma_nat_eq_factorial]
  push_cast
  ring

theorem virasoro_cardyV_eq_V_C (c' t : ℝ) :
    (virasoroProblem.cardyV (c' / 12) t : ℂ) = V_C (c' : ℂ) (t : ℂ) := by
  have hk0 : (Crossing.kernelK 1 (c' / 12) t : ℂ) = KalphaC ((c' : ℂ) / 12) (t : ℂ) := by
    rw [kernelK_one_eq_KalphaC]; push_cast; rfl
  have hk1 : (Crossing.kernelK 1 (c' / 12 - 1) t : ℂ) = KalphaC ((c' : ℂ) / 12 - 1) (t : ℂ) := by
    rw [kernelK_one_eq_KalphaC]; push_cast; rfl
  have hk2 : (Crossing.kernelK 1 (c' / 12 - 2) t : ℂ) = KalphaC ((c' : ℂ) / 12 - 2) (t : ℂ) := by
    rw [kernelK_one_eq_KalphaC]; push_cast; rfl
  rw [virasoro_cardyV_eq]
  unfold V_C
  rw [← hk0, ← hk1, ← hk2]
  push_cast
  rfl

/-! ### 3. Concrete `BlowupTest` constructor -/

/-- Concrete threshold above which all real and complex strip inputs apply (`≥ 10000`). -/
noncomputable def c_concrete : ℝ :=
  max c_PJ_complex virasoroStripBootstrapInputs.pj.c_PJ

lemma c_PJ_complex_le_c_concrete : c_PJ_complex ≤ c_concrete :=
  le_max_left _ _

lemma pj_c_PJ_le_c_concrete : virasoroStripBootstrapInputs.pj.c_PJ ≤ c_concrete :=
  le_max_right _ _

/-- Construct a `BlowupTest virasoroStripBootstrapInputs c'` unconditionally from any concrete
weakly feasible Virasoro test `virasoroProblem.IsWeaklyFeasible (c' / 12) T g` (`c_concrete ≤ c'`),
using `t₁ = leastThreshold g` (`blowup_limit.tex`, Proposition T). -/
noncomputable def blowupTest_of_concrete {c' T : ℝ} (hc' : c_concrete ≤ c') {g : ℝ → ℝ}
    (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g) :
    BlowupTest virasoroStripBootstrapInputs c' :=
  let a : ℝ := c' / 12
  let t₁ : ℝ := leastThreshold g
  have hcPJ_comp : c_PJ_complex ≤ c' := c_PJ_complex_le_c_concrete.trans hc'
  have hc10000 : 10000 ≤ c' := hcPJ_comp
  have hc1000 : 1000 ≤ c' := by linarith
  have hc24 : 24 ≤ c' := by linarith
  have hc0 : 0 < c' := by linarith
  have hcPJ : virasoroStripBootstrapInputs.pj.c_PJ ≤ c' := pj_c_PJ_le_c_concrete.trans hc'
  have ha : virasoroProblem.totalShift ≤ a := by
    rw [virasoroProblem_totalShift]; dsimp [a]; linarith
  have ha2 : 2 ≤ a := by rwa [← virasoroProblem_totalShift]
  have hM_pos : 0 < virasoroProblem.cardyNorm a g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  have ht₁_nn : 0 ≤ t₁ := leastThreshold_nonneg g
  let x₁ : ℝ := Real.sqrt (3 * t₁ / c')
  have hV_int : IntegrableOn (fun t => g t * virasoroProblem.cardyV a t) (Ioi 0) :=
    hg.1.int_cardy.norm.mono'
      (((hg.1.cont.mul (continuous_cardyV virasoroProblem a).continuousOn).mono Ioi_subset_Ici_self)
        |>.aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
  { g := g
    G := hankelContinuation c' g
    V := virasoroProblem.cardyV a
    K_a := kernelK 1 a
    M := virasoroProblem.cardyNorm a g
    t₁ := t₁
    x₁ := x₁
    gVac := virasoroProblem.gVac a g
    hM_pos := hM_pos
    hx₁_nonneg := Real.sqrt_nonneg _
    ht₁_eq := by
      dsimp [x₁]
      rw [Real.sq_sqrt (by positivity)]
      field_simp [hc0.ne']
    hgVac_nonneg := hg.2.2.1
    hg_cont := hg.1.cont
    hV_cont := (continuous_cardyV virasoroProblem a).continuousOn
    hV_pos := fun t ht => by
      have hge := virasoro_cardyV_ge ha2 ht.le
      have hpos : 0 < 8 * π ^ 4 * t ^ 2 := by positivity
      linarith
    hV_nonneg := fun _ ht => virasoroProblem.cardyV_nonneg ha ht
    hV_eq_C := fun t => virasoro_cardyV_eq_V_C c' t
    hG_holo := differentiableOn_hankelContinuation hc1000 hg.1
    hG_real := fun x => hankelContinuation_ofReal hc0 hg.1 x
    hM_int := hg.1.int_cardy
    hM_eq := rfl
    hg_nonneg_tail := leastThreshold_tail hg.1.cont hg.2.2.2
    ht₁_least := rfl
    hVac_int := hV_int
    hVac_eq := by
      unfold FixedWeightProblem.gVac
      have hpi : π ≠ 0 := Real.pi_pos.ne'
      field_simp
    hV_le_two_Ka := fun _ _ => virasoro_cardyV_le_two_Ka ha2 (by positivity)
    hKa_ub := fun x hx => Crossing.virasoro_Ka_ub hc0 hx
    hPJ_real := fun x hx hne =>
      let hPJ : LemmaPJInput realSliceData
          PoissonJensen.stripPoissonJensen.choose
          PoissonJensen.stripPoissonJensen.choose_spec.choose majorantReal :=
        PoissonJensen.stripPoissonJensen.choose_spec.choose_spec.2
      hPJ hcPJ hg.1 hM_pos x hx hne
    hDeepLobe := fun hcd =>
      let hPJ : LemmaPJInput realSliceData
          PoissonJensen.stripPoissonJensen.choose
          PoissonJensen.stripPoissonJensen.choose_spec.choose majorantReal :=
        PoissonJensen.stripPoissonJensen.choose_spec.choose_spec.2
      (Integration.lemmaGapInput_of_lemmaPJInput realSliceData majorantReal
        (c_PJ := PoissonJensen.stripPoissonJensen.choose)
        (C_PJ := PoissonJensen.stripPoissonJensen.choose_spec.choose)
        PoissonJensen.stripPoissonJensen.choose_spec.choose_spec.1
        (fun _ hx => majorantReal_g_deficit hx) hPJ).choose_spec hcd hg.1
    hPJ_complex := fun _ z hz_im hz_tip hb_im hb_ne => by
      simpa [virasoroStripBootstrapInputs, lemmaGPotentialInput_virasoro_U] using
        stripPoissonJensen_complex hcPJ_comp hg.1 hM_pos hz_im hz_tip hb_im hb_ne }

/-- Non-vacuity of `BlowupTest virasoroStripBootstrapInputs c'` for all `c' ≥ c_concrete`. -/
theorem blowupTest_nonempty {c' : ℝ} (hc' : c_concrete ≤ c') :
    Nonempty (BlowupTest virasoroStripBootstrapInputs c') := by
  have hc10000 : 10000 ≤ c' := (by unfold c_PJ_complex; norm_num : 10000 ≤ c_PJ_complex).trans
    (c_PJ_complex_le_c_concrete.trans hc')
  have hshift : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨T, _, g, hg⟩ := virasoroProblem.feasible_nonempty hshift
  exact ⟨blowupTest_of_concrete hc' hg.isWeaklyFeasible⟩

/-! ### 4. Unconditional `BlowupFamilyPackage`, `RigidityFamilyPackage`, and Concrete Theorems -/

/-- Unconditional **`BlowupFamilyPackage ι p`** for any asymptotic family of weakly feasible
Virasoro tests (`hc' : Tendsto c' p atTop`, `∀ᶠ n in p, ∃ T, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n)`),
with zero unproved hypotheses. -/
noncomputable def blowupFamilyPackage_of_concrete_tests {ι : Type*} {p : Filter ι}
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n)) :
    BlowupFamilyPackage ι p :=
  let t₁_fn : ι → ℝ := fun n => leastThreshold (g n)
  let x₁_fn : ι → ℝ := fun n => Real.sqrt (3 * t₁_fn n / c' n)
  let s₁_fn : ι → ℝ := fun n => (x₁_fn n - xiStar) / tipEps (c' n)
  let Φ_fn : ι → ℂ → ℂ := fun n ζ =>
    W_C (c' n) (bScale (c' n) ζ) * hankelContinuation (c' n) (g n) (bScale (c' n) ζ) /
      (virasoroProblem.cardyNorm (c' n / 12) (g n) : ℂ)
  let γ_fn : ι → ℝ := fun n =>
    virasoroProblem.gVac (c' n / 12) (g n) /
      (2 * π * virasoroProblem.cardyNorm (c' n / 12) (g n))
  { c' := c'
    s₁ := s₁_fn
    t₁ := t₁_fn
    Φ := Φ_fn
    γ := γ_fn
    hc'_tendsto := hc'
    hγ_nonneg := by
      filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg] with n hc'n hgn
      let test := blowupTest_of_concrete hc'n hgn.choose_spec
      have h1 : 0 ≤ test.gVac := test.hgVac_nonneg
      have h2 : 0 < 2 * π * test.M := by have := Real.pi_pos; have := test.hM_pos; positivity
      exact div_nonneg h1 h2.le
    scaling_eq := by
      filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg] with n hc'n hgn
      have hc'0 : 0 < c' n :=
        lt_of_lt_of_le (by unfold c_PJ_complex; norm_num)
          ((c_PJ_complex_le_c_concrete.trans hc'n))
      exact tipS₁_scaling_eq hc'0 (blowupTest_of_concrete hc'n hgn.choose_spec)
    theorem_A_lower := by
      obtain ⟨C₀, c_A, _, _, hA⟩ := tipS₁_theorem_A_lower virasoroStripBootstrapInputs
      refine ⟨C₀, ?_⟩
      filter_upwards [hc'.eventually (eventually_ge_atTop (max c_A c_concrete)), hg] with n hc'n hgn
      exact hA ((le_max_left _ _).trans hc'n)
        (blowupTest_of_concrete ((le_max_right _ _).trans hc'n) hgn.choose_spec)
    propT_subseq := fun ns hns hB => by
      have hev_all : ∀ᶠ k in atTop,
          c_concrete ≤ c' (ns k) ∧ ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' (ns k) / 12) T (g (ns k)) :=
        hns.eventually ((hc'.eventually (eventually_ge_atTop c_concrete)).and hg)
      obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hev_all
      let ns' : ℕ → ι := fun k => ns (k + K₀)
      let c'' : ℕ → ℝ := fun k => c' (ns' k)
      let tests : ∀ k : ℕ, BlowupTest virasoroStripBootstrapInputs (c'' k) := fun k =>
        blowupTest_of_concrete (hK₀ (k + K₀) (Nat.le_add_left K₀ k)).1
          (hK₀ (k + K₀) (Nat.le_add_left K₀ k)).2.choose_spec
      have hc'' : Tendsto c'' atTop atTop :=
        hc'.comp (hns.comp (tendsto_add_atTop_nat K₀))
      have hB' : ∃ B : ℝ, ∀ k : ℕ, tipS₁ (c'' k) (tests k) ≤ B := by
        obtain ⟨B, hB⟩ := hB
        exact ⟨B, fun k => hB (k + K₀)⟩
      obtain ⟨ms, s₁Star, Ψ, γLim, mEsc, C_env, hms, hs₁, hΦ, hγ, hΨd, hCnn, hΨb, _, _, hΨi,
        hΨnorm, hΨim, hΨnn, hγnn, hmEscnn, hΨre, hneg, hΨne, _⟩ :=
        proposition_T ComplexBessel.besselI0Asymptotic virasoroStripBootstrapInputs hc'' tests hB'
      refine ⟨fun j => ms j + K₀, s₁Star, Ψ, γLim, mEsc,
        fun i j hij => Nat.add_lt_add_right (hms hij) K₀, hs₁, hΦ, hγ, hΨd, hΨi,
        ⟨C_env, hCnn, hΨb⟩, hΨne, hΨim, hΨnn, hΨnorm, hγnn, hmEscnn, hΨre, hneg⟩ }

/-- Unconditional **`RigidityFamilyPackage ι p`** for any asymptotic family of weakly feasible
Virasoro tests (deriving `0 < t₁ → g t₁ = 0` automatically from `leastThreshold`). -/
noncomputable def rigidityFamilyPackage_of_concrete_tests {ι : Type*} {p : Filter ι}
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n)) :
    RigidityFamilyPackage ι p where
  toBlowupFamilyPackage := blowupFamilyPackage_of_concrete_tests hc' g hg
  domain_integrable := by
    filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg] with n hc'n hgn
    have hc'0 : 0 < c' n :=
      lt_of_lt_of_le (by unfold c_PJ_complex; norm_num) (c_PJ_complex_le_c_concrete.trans hc'n)
    have h := tipRescale_integrableOn_domain hc'0 (blowupTest_of_concrete hc'n hgn.choose_spec)
    simpa only [blowupFamilyPackage_of_concrete_tests, tipSMin, tipRescale, blowupTest_of_concrete] using h
  domain_norm_integral := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg] with n hc'n hgn
    have hc'0 : 0 < c' n :=
      lt_of_lt_of_le (by unfold c_PJ_complex; norm_num) (c_PJ_complex_le_c_concrete.trans hc'n)
    have h := (tipRescale_norm_integral hc'0 (blowupTest_of_concrete hc'n hgn.choose_spec)).symm
    simpa only [blowupFamilyPackage_of_concrete_tests, tipSMin, tipRescale, blowupTest_of_concrete] using h
  holo_balls := fun R => by
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg,
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n hgn h2R
    have hc'0 : 0 < c' n :=
      lt_of_lt_of_le (by unfold c_PJ_complex; norm_num) (c_PJ_complex_le_c_concrete.trans hc'n)
    dsimp [blowupFamilyPackage_of_concrete_tests]
    exact tipRescale_holo_ball hc'0 h2R (blowupTest_of_concrete hc'n hgn.choose_spec)
  real_symm := fun R => by
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg,
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n hgn h2R z hz
    have hc'0 : 0 < c' n :=
      lt_of_lt_of_le (by unfold c_PJ_complex; norm_num) (c_PJ_complex_le_c_concrete.trans hc'n)
    have hε_pos := tipEps_pos hc'0
    have him : |z.im| < 1 / (2 * tipEps (c' n)) := by
      have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hzr : ‖z‖ < R := mem_ball_zero_iff.mp hz
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    dsimp [blowupFamilyPackage_of_concrete_tests]
    exact tipRescale_real_symm hc'0 (blowupTest_of_concrete hc'n hgn.choose_spec) him
  nonneg_tail := by
    filter_upwards [hc'.eventually (eventually_ge_atTop c_concrete), hg] with n hc'n hgn s hs
    have hc'0 : 0 < c' n :=
      lt_of_lt_of_le (by unfold c_PJ_complex; norm_num) (c_PJ_complex_le_c_concrete.trans hc'n)
    dsimp [blowupFamilyPackage_of_concrete_tests] at hs ⊢
    exact tipRescale_nonneg_tail hc'0 (blowupTest_of_concrete hc'n hgn.choose_spec) s hs
  s1_is_zero := by
    obtain ⟨C_A, c_A, _, hcA_ge1, hA⟩ :=
      theorem_A virasoroStripBootstrapInputs.pj virasoroStripBootstrapInputs.fg
    have hpos_t1 : Tendsto (fun n => xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ)) p atTop := by
      have hsub : ∀ᶠ n in p, 1 ≤ c' n →
          xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ) =
            c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) := by
        filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1 _
        have hc'n : 0 < c' n := by linarith
        have h1 : c' n * c' n ^ (-(2 / 3 : ℝ)) = c' n ^ (1 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (c' n)]
          rw [← Real.rpow_add hc'n]; norm_num
        have h2 : C_A * (c' n * c' n ^ (-(2 / 3 : ℝ))) = C_A * c' n ^ (1 / 3 : ℝ) := by rw [h1]
        linarith [h2]
      have hfac : Tendsto (fun n => c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ)))) p atTop := by
        have hlim : Tendsto (fun n => xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) p (nhds xiBar) := by
          have h0 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc').const_mul C_A
          simpa using tendsto_const_nhds.sub h0
        have hxi_pos : 0 < xiBar := by unfold xiBar; positivity [xiStar_pos]
        exact hc'.atTop_mul_pos hxi_pos hlim
      refine hfac.congr' ?_
      filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ)), hsub] with n hn hs
      exact (hs hn).symm
    filter_upwards [hc'.eventually (eventually_ge_atTop (max c_A c_concrete)), hg,
      hpos_t1.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n hgn hlb
    have hcA_n : c_A ≤ c' n := (le_max_left _ _).trans hc'n
    have hcC_n : c_concrete ≤ c' n := (le_max_right _ _).trans hc'n
    have hc'0 : 0 < c' n := lt_of_lt_of_le (by linarith) hcA_n
    let test := blowupTest_of_concrete hcC_n hgn.choose_spec
    have ht1_pos : 0 < test.t₁ :=
      lt_of_lt_of_le hlb (hA hcA_n (test.toWeaklyFeasibleTest hc'0.le))
    have hg0 : test.g test.t₁ = 0 :=
      isThreshold_imp_g_t1_eq_zero test.hg_cont ht1_pos test.ht₁_least test.hg_nonneg_tail
    have ht_eq : tipTReal (c' n) (tipS₁ (c' n) test) = test.t₁ := by
      unfold tipTReal tipBReal tipS₁
      have hε : tipEps (c' n) ≠ 0 := (tipEps_pos hc'0).ne'
      rw [show xiStar + tipEps (c' n) * ((test.x₁ - xiStar) / tipEps (c' n)) = test.x₁ by
        field_simp [hε]; ring, ← test.ht₁_eq]
    dsimp [blowupFamilyPackage_of_concrete_tests]
    change tipRescale (c' n) test (tipS₁ (c' n) test : ℂ) = 0
    rw [tipRescale_real_on_real, ht_eq, hg0]
    simp

/-- Unconditional **Theorem C** (`local_airy_model.tex`) for concrete weakly feasible Virasoro tests. -/
theorem concrete_blowup_theorem_C {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n)) :
    (Aopt : EReal) ≤
      Filter.liminf (fun n =>
        (((leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p :=
  theorem_C (blowupFamilyPackage_of_concrete_tests hc' g hg)

/-- Unconditional **Theorem R `(R1)`** (`rigidity.tex`) for concrete weakly feasible Virasoro tests. -/
theorem concrete_blowup_theorem_R1 {ι : Type*} {p : Filter ι} [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests hc' g hg)) :
    let F := blowupFamilyPackage_of_concrete_tests hc' g hg
    Tendsto F.s₁ p (nhds s1) ∧
    TendstoLocallyUniformlyOn F.Φ phiStar p univ ∧
    Tendsto F.γ p (nhds 0) :=
  theorem_R1 (blowupFamilyPackage_of_concrete_tests hc' g hg) hAtt

/-- Unconditional **Theorem R `(R2)`** (`rigidity.tex`) for concrete weakly feasible Virasoro tests. -/
theorem concrete_blowup_theorem_R2 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests hc' g hg)) :
    let R := rigidityFamilyPackage_of_concrete_tests hc' g hg
    Tendsto (fun n => ∫ s : ℝ, ‖phiExt R n s - phiStar (s : ℂ)‖) p (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ᶠ n in p, ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖ < ε) ∧
    Tendsto (fun R₀ : ℝ => Filter.limsup (fun n => ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖) p)
      atTop (nhds 0) := by
  have hR := theorem_R2 (rigidityFamilyPackage_of_concrete_tests hc' g hg) hAtt
  exact ⟨hR.1, hR.2.2.1, hR.2.2.2⟩

/-- Unconditional **Theorem R `(R3)`** (`rigidity.tex`) for concrete weakly feasible Virasoro tests. -/
theorem concrete_blowup_theorem_R3 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, virasoroProblem.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests hc' g hg)) :
    let R := rigidityFamilyPackage_of_concrete_tests hc' g hg
    (∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      zeroCount (R.Φ n) (s1 : ℂ) r = 1 ∧ (R.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧
      R.Φ n (R.s₁ n : ℂ) = 0 ∧ analyticOrderNatAt (R.Φ n) (R.s₁ n : ℂ) = 1 ∧
      ∀ z ∈ ball (s1 : ℂ) r, R.Φ n z = 0 → z = (R.s₁ n : ℂ)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ r₀ > 0,
      (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        zeroCount (R.Φ n) (sNode k : ℂ) r = 2 ∧
        ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ R.Φ n (x : ℂ) = 0 ∧
            analyticOrderNatAt (R.Φ n) (x : ℂ) = 2 ∧
            ∀ z ∈ ball (sNode k : ℂ) r, R.Φ n z = 0 → z = (x : ℂ)) ∨
         (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ R.Φ n z = 0 ∧
            R.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (R.Φ n) z = 1 ∧
            analyticOrderNatAt (R.Φ n) (starRingEnd ℂ z) = 1 ∧
            ∀ w ∈ ball (sNode k : ℂ) r, R.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
      (∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0) →
        Tendsto z p (nhds (sNode k : ℂ)) ∧
        Tendsto (fun n => (tScale (R.c' n) (z n) - ((xiBar * R.c' n : ℝ) : ℂ)) /
            (((R.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
          (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
        (k = 2 →
          Tendsto (fun n => (tScale (R.c' n) (z n) - (R.t₁ n : ℂ)) /
              ((((R.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
            (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ))))) ∧
      (∃ z : ι → ℂ, ∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0)) ∧
    (∀ K : Set ℂ, IsCompact K → (∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) →
      ∀ᶠ n in p, ∀ z ∈ K, R.Φ n z ≠ 0) :=
  theorem_R3 _ hAtt

/-! ### Axiom checks -/

/--
info: 'FormalResearch.ModularBootstrap.TipFront.blowupTest_of_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms blowupTest_of_concrete

/--
info: 'FormalResearch.ModularBootstrap.TipFront.blowupTest_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms blowupTest_nonempty

/--
info: 'FormalResearch.ModularBootstrap.TipFront.concrete_blowup_theorem_C' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_C

/--
info: 'FormalResearch.ModularBootstrap.TipFront.concrete_blowup_theorem_R1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R1

/--
info: 'FormalResearch.ModularBootstrap.TipFront.concrete_blowup_theorem_R2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R2

/--
info: 'FormalResearch.ModularBootstrap.TipFront.concrete_blowup_theorem_R3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R3

end FormalResearch.ModularBootstrap.TipFront

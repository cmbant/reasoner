module

public import FormalResearch.ModularBootstrap.FoldTip.Hypotheses
public import FormalResearch.ModularBootstrap.FoldTip.WindowPairing

/-!
# Dual measures: weight recovery (`Lemma WR`) and `ft:C5c` (`fold_dual_measures.tex`)

Formalises Paper I Appendix `ft:dual` (`CFT/sign_uncertainty/paper/fold_dual_measures.tex`) after
`FoldTip.WindowPairing` (`lemma_WP`):

* **`hbQuadMeasure`** and **`lemma_WR`** (`ft:WR` / `sr:WR`, Lemma WR): for any polynomial Hermite–Biehler
  data `D : ShellHBData`, the quadrature measure `∑_n ω_n δ_{z_n}` (`hbQuadMeasure D`, matching
  `Upper.Rigidity.airyMeasure` when `D = ShellHBData.airy`) and uniqueness of any Radon measure carried
  by `hbSupport D` satisfying `∫ R G_N dν ≤ ∫ R G_N` for `R ∈ ℛ_N`.
* **`ft_C5c`** (`ft:C5c`): `FTH4b D X` alone implies `LocallyBounded`, full-sequence vague convergence to
  `hbQuadMeasure D`, and no escape of positive pairing mass for every equality design.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.SignUncertainty
  FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### 2. Hermite–Biehler quadrature measure and test functions `R G_N ∈ 𝒢` -/

/-- The quadrature weight `ω(z) = D(z) / (Re N'(z))²` at a zero `z` of `N = P Ai + Q Ai'`. -/
noncomputable def hbQuadWeight (D : ShellHBData) (z : ℝ) : ℝ :=
  airyPQDr D.P D.Q z / ((airyPQN' D.P D.Q (z : ℂ)).re) ^ 2

lemma hbQuadWeight_pos (D : ShellHBData) (n : ℕ) :
    0 < hbQuadWeight D (hbZeroEnum D n) := by
  have hz : airyPQN D.P D.Q ((hbZeroEnum D n : ℝ) : ℂ) = 0 :=
    (nodeZero_iff D (hbZeroEnum D n)).2 (((hbZeroEnum_spec D).2 (hbZeroEnum D n)).2 ⟨n, rfl⟩)
  obtain ⟨hD, hN'⟩ := hb_zero_weight_pos_all D hz
  unfold hbQuadWeight
  exact div_pos hD (sq_pos_of_ne_zero hN')

/-- The Hermite–Biehler quadrature measure `∑_n ω_n δ_{z_n}` (`ft:WR`, `ft:C5c`). -/
noncomputable def hbQuadMeasure (D : ShellHBData) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (hbQuadWeight D (hbZeroEnum D n)) • Measure.dirac (hbZeroEnum D n)

lemma hbZeroEnum_airy_eq (n : ℕ) : hbZeroEnum ShellHBData.airy n = airyNode n := by
  have hZ : IsHbZeroEnum ShellHBData.airy.P ShellHBData.airy.Q airyNode := by
    refine ⟨fun a b hab => airyZero_lt_of_lt (Nat.succ_le_succ (Nat.zero_le a)) (Nat.succ_lt_succ hab),
      fun x => ?_⟩
    have hNf : at47_Nf ShellHBData.airy.P ShellHBData.airy.Q x = airyAi x := by
      unfold at47_Nf; simp [ShellHBData.airy]
    rw [hNf]
    constructor
    · intro hAi
      have hx0 : x ≤ 0 := by
        by_contra hpos; push Not at hpos
        exact (airyAi_pos hpos.le).ne' hAi
      exact have ⟨k, hk⟩ := exists_airyNode_eq hAi hx0; ⟨k, hk.symm⟩
    · rintro ⟨k, rfl⟩
      exact airyAi_airyZero (k + 1)
  exact congrFun (IsHbZeroEnum.unique (hbZeroEnum_spec ShellHBData.airy) hZ) n

lemma hbQuadWeight_airy_eq (n : ℕ) :
    hbQuadWeight ShellHBData.airy (airyNode n) = airyNodeWeight n := by
  have h1 : airyPQc (Polynomial.C (1 : ℝ)) (airyNode n : ℂ) = 1 := by
    simpa using airyPQc_C (1 : ℝ) (airyNode n : ℂ)
  rw [Polynomial.C_1] at h1
  unfold hbQuadWeight airyNodeWeight airyPQDr airyPQN'
  simp [ShellHBData.airy, airyAiC_ofReal, deriv_airyAiC_ofReal, airyPQc_zero, h1]

/-- For `(P, Q) = (1, 0)` (`ShellHBData.airy`), `hbQuadMeasure ShellHBData.airy` coincides with
`Upper.Rigidity.airyMeasure`. -/
theorem hbQuadMeasure_airy_eq : hbQuadMeasure ShellHBData.airy = airyMeasure := by
  unfold hbQuadMeasure airyMeasure
  congr 1
  ext n
  rw [hbZeroEnum_airy_eq n, hbQuadWeight_airy_eq n]

lemma isCompact_finite_hbZeroEnum (D : ShellHBData) {K : Set ℝ} (hKc : IsCompact K) :
    {n : ℕ | hbZeroEnum D n ∈ K}.Finite := by
  obtain ⟨L, hL⟩ := hKc.bddBelow
  have hanti : StrictAnti (hbZeroEnum D) := (hbZeroEnum_spec D).1
  have hneg : ∀ᶠ n in atTop, hbZeroEnum D n < L := by
    by_cases hQ : D.Q = 0
    · have hZ : ∀ n, hbZeroEnum D n = airyZero (n + 1) := by
        have hZe : IsHbZeroEnum D.P D.Q airyNode := by
          obtain ⟨p₀, hp₀, hP⟩ := airyPQHB_eq_C_of_Q_eq_zero (hQ ▸ D.hHB)
          refine ⟨fun a b hab => airyZero_lt_of_lt (Nat.succ_le_succ (Nat.zero_le a)) (Nat.succ_lt_succ hab),
            fun x => ?_⟩
          have hNf : at47_Nf D.P D.Q x = p₀ * airyAi x := by unfold at47_Nf; rw [hP, hQ]; simp
          rw [hNf, mul_eq_zero, or_iff_right hp₀]
          exact ⟨fun hAi =>
            have ⟨k, hk⟩ := exists_airyNode_eq hAi
              (by by_contra hpos; push Not at hpos; exact (airyAi_pos hpos.le).ne' hAi)
            ⟨k, hk.symm⟩,
            fun ⟨k, hk⟩ => hk ▸ airyAi_airyZero (k + 1)⟩
        exact fun n => congrFun (IsHbZeroEnum.unique (hbZeroEnum_spec D) hZe) n
      filter_upwards [tendsto_airyNode.eventually (eventually_lt_atBot L)] with n hn
      rwa [hZ n]
    · obtain ⟨x, hx0, hxL⟩ := at47_zeros_unbounded (P := D.P) hQ L
      obtain ⟨N, hN⟩ := ((hbZeroEnum_spec D).2 x).1 hx0
      refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
      have hlt := hanti (by omega : N < n)
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hneg
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra hge
  have := hN n (not_lt.mp hge)
  linarith [hL hn]

lemma isLocallyFiniteMeasure_hbQuadMeasure (D : ShellHBData) :
    IsLocallyFiniteMeasure (hbQuadMeasure D) := by
  refine ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  unfold hbQuadMeasure
  rw [Measure.sum_apply _ measurableSet_Icc]
  have hfin : {n : ℕ | hbZeroEnum D n ∈ Icc (x - 1) (x + 1)}.Finite :=
    isCompact_finite_hbZeroEnum D isCompact_Icc
  have hsum : ∑' n : ℕ,
      (ENNReal.ofReal (hbQuadWeight D (hbZeroEnum D n)) • Measure.dirac (hbZeroEnum D n))
        (Icc (x - 1) (x + 1)) =
      ∑ n ∈ hfin.toFinset, ENNReal.ofReal (hbQuadWeight D (hbZeroEnum D n)) := by
    rw [tsum_eq_sum (s := hfin.toFinset)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hnI : hbZeroEnum D n ∈ Icc (x - 1) (x + 1) := hfin.mem_toFinset.mp hn
      simp [Measure.dirac_apply' _ measurableSet_Icc, Set.indicator_of_mem hnI]
    · intro n hn
      have hnI : hbZeroEnum D n ∉ Icc (x - 1) (x + 1) := fun h => hn (hfin.mem_toFinset.mpr h)
      simp [Measure.dirac_apply' _ measurableSet_Icc, Set.indicator_of_notMem hnI]
  rw [hsum]
  exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top

lemma hbQuadMeasure_compl_range (D : ShellHBData) :
    hbQuadMeasure D (Set.range (hbZeroEnum D))ᶜ = 0 := by
  have hm : MeasurableSet (Set.range (hbZeroEnum D)) := (Set.countable_range _).measurableSet
  unfold hbQuadMeasure
  rw [Measure.sum_apply _ hm.compl]
  refine tsum_eq_zero_iff.2 fun n => ?_
  simp [Measure.dirac_apply' _ hm.compl, Set.indicator]

lemma hbQuadMeasure_singleton (D : ShellHBData) (n : ℕ) :
    hbQuadMeasure D {hbZeroEnum D n} = ENNReal.ofReal (hbQuadWeight D (hbZeroEnum D n)) := by
  unfold hbQuadMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single n]
  · simp
  · intro m hm
    have hne : hbZeroEnum D m ≠ hbZeroEnum D n := (hbZeroEnum_spec D).1.injective.ne hm
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator, hne]

lemma measure_eq_sum_hbAtoms (D : ShellHBData) {ν : Measure ℝ}
    (h : ν (Set.range (hbZeroEnum D))ᶜ = 0) :
    ν = Measure.sum fun n => ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n) := by
  have hm : MeasurableSet (Set.range (hbZeroEnum D)) := (Set.countable_range _).measurableSet
  ext s hs
  rw [Measure.sum_apply _ hs]
  have h1 : ν s = ν (s ∩ Set.range (hbZeroEnum D)) := by
    have := measure_inter_add_sdiff s hm (μ := ν)
    have h0 : ν (s \ Set.range (hbZeroEnum D)) = 0 := measure_mono_null (fun _ hx => hx.2) h
    rw [h0, add_zero] at this
    exact this.symm
  have h2 : s ∩ Set.range (hbZeroEnum D) = ⋃ n, (s ∩ {hbZeroEnum D n}) := by
    ext x; simp only [mem_inter_iff, mem_range, mem_iUnion, mem_singleton_iff]
    exact ⟨fun ⟨hx, n, hn⟩ => ⟨n, hx, hn.symm⟩, fun ⟨n, hx, hn⟩ => ⟨hx, n, hn.symm⟩⟩
  rw [h1, h2, measure_iUnion]
  · congr 1; ext n
    rw [smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases hn : hbZeroEnum D n ∈ s
    · have : s ∩ {hbZeroEnum D n} = {hbZeroEnum D n} := by
        ext x; simp only [mem_inter_iff, mem_singleton_iff]
        exact ⟨fun hx => hx.2, by rintro rfl; exact ⟨hn, rfl⟩⟩
      simp [this, Set.indicator_of_mem hn]
    · have : s ∩ {hbZeroEnum D n} = ∅ := by
        ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ h; subst h; exact hn ‹_›
      simp [this, Set.indicator_of_notMem hn]
  · intro i j hij
    exact Set.disjoint_left.2 fun _ hxi hxj =>
      hij ((hbZeroEnum_spec D).1.injective (hxi.2.symm.trans hxj.2))
  · exact fun _ => hs.inter (measurableSet_singleton _)

lemma integral_eq_sum_hbAtoms_finset {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (D : ShellHBData) (h : ν (Set.range (hbZeroEnum D))ᶜ = 0) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (T : Finset ℕ)
    (hg_out : ∀ n ∉ T, g (hbZeroEnum D n) = 0) :
    ∫ u, g u ∂ν = ∑ n ∈ T, g (hbZeroEnum D n) * (ν {hbZeroEnum D n}).toReal := by
  have hsum : ν = Measure.sum fun n => ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n) :=
    measure_eq_sum_hbAtoms D h
  have hfin_meas : ∀ n, ν {hbZeroEnum D n} ≠ ⊤ := fun n =>
    (measure_singleton_lt_top (μ := ν)).ne
  have hint_sum : Integrable g (Measure.sum fun n => ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n)) := by
    refine ⟨hg_cont.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_sum_measure]
    have hterm : ∀ n, ∫⁻ u, ‖g u‖ₑ ∂(ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n)) =
        ν {hbZeroEnum D n} * ENNReal.ofReal |g (hbZeroEnum D n)| := fun n => by
      rw [lintegral_smul_measure, lintegral_dirac' _ hg_cont.measurable.eNorm, smul_eq_mul,
        Real.eNorm_eq_ofReal_abs]
    simp_rw [hterm]
    rw [tsum_eq_sum (s := T)]
    · exact ENNReal.sum_lt_top.2 fun n _ => ENNReal.mul_lt_top (hfin_meas n).lt_top ENNReal.ofReal_lt_top
    · intro n hn; simp [hg_out n hn]
  calc ∫ u, g u ∂ν
      = ∫ u, g u ∂(Measure.sum fun n => ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n)) := by
        congr 1
    _ = ∑' n, ∫ u, g u ∂(ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n)) :=
        integral_sum_measure hint_sum
    _ = ∑' n, g (hbZeroEnum D n) * (ν {hbZeroEnum D n}).toReal := by
        refine tsum_congr fun n => ?_
        rw [integral_smul_measure, integral_dirac, smul_eq_mul, mul_comm]
    _ = ∑ n ∈ T, g (hbZeroEnum D n) * (ν {hbZeroEnum D n}).toReal :=
        tsum_eq_sum fun n hn => by simp [hg_out n hn]

/-- Every `t ∈ D.S` is a real zero of `N`, hence lies in `Set.range (hbZeroEnum D)`. -/
lemma mem_range_hbZeroEnum_of_mem_S (D : ShellHBData) {z : ℝ} (hz : z ∈ D.S) :
    z ∈ Set.range (hbZeroEnum D) := by
  have hp := D.G_prod_eq (z : ℂ)
  rw [D.G_eq_zero_on_S z hz, zero_mul] at hp
  have hsign : (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) ≠ 0 := by
    push_cast; exact pow_ne_zero _ (by norm_num)
  have hNsq : airyPQN D.P D.Q (z : ℂ) ^ 2 = 0 := (mul_eq_zero.mp hp.symm).resolve_left hsign
  have hN0 : airyPQN D.P D.Q (z : ℂ) = 0 := sq_eq_zero_iff.mp hNsq
  have hNf : at47_Nf D.P D.Q z = 0 := (nodeZero_iff D z).1 hN0
  exact ((hbZeroEnum_spec D).2 z).1 hNf

lemma hb_G_eq_zero_at_zero (D : ShellHBData) (n : ℕ) : D.G (hbZeroEnum D n : ℂ) = 0 := by
  by_cases hmem : hbZeroEnum D n ∈ D.S
  · exact D.G_eq_zero_on_S _ hmem
  · have hp := D.G_prod_eq (hbZeroEnum D n : ℂ)
    have hN0 : airyPQN D.P D.Q (hbZeroEnum D n : ℂ) = 0 :=
      (nodeZero_iff D (hbZeroEnum D n)).2 (((hbZeroEnum_spec D).2 (hbZeroEnum D n)).2 ⟨n, rfl⟩)
    rw [hN0, zero_pow two_ne_zero, mul_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_right (at47_pr_ne_zero hmem)

lemma hb_G_pos_on_Iio_compl (D : ShellHBData) {u : ℝ} (hu : u < D.tm)
    (hNz : u ∉ Set.range (hbZeroEnum D)) : 0 < (D.G (u : ℂ)).re := by
  have huS : u ∉ D.S := fun h => not_le.mpr hu (D.tm_min u h)
  have hNf : at47_Nf D.P D.Q u ≠ 0 := fun h0 => hNz (((hbZeroEnum_spec D).2 u).1 h0)
  have hform := at47_F_real_formula D.G_prod_eq huS
  rw [hform, Complex.ofReal_re]
  have hsign : ∀ t ∈ D.S, u - t = -(t - u) := fun _ _ => by ring
  have hprod : ∏ t ∈ D.S, (u - t) = (-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - u) := by
    rw [Finset.prod_congr rfl hsign, Finset.prod_neg]
  rw [hprod]
  have hden : 0 < ∏ t ∈ D.S, (t - u) :=
    Finset.prod_pos fun t ht => sub_pos.mpr (hu.trans_le (D.tm_min t ht))
  have h1 : (-1 : ℝ) ^ D.S.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : (-1 : ℝ) ^ D.S.card * at47_Nf D.P D.Q u ^ 2 /
      ((-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - u)) =
      at47_Nf D.P D.Q u ^ 2 / ∏ t ∈ D.S, (t - u) := by
    field_simp
  rw [heq]
  exact div_pos (sq_pos_of_ne_zero hNf) hden

lemma hb_G_deriv_im_zero (D : ShellHBData) (z : ℝ) : (deriv D.G (z : ℂ)).im = 0 := by
  have hre : HasDerivAt (fun x : ℝ => D.G (x : ℂ)) (deriv D.G (z : ℂ)) z := by
    simpa using (D.G_diff (z : ℂ)).hasDerivAt.comp_ofReal
  have him : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).im) ((deriv D.G (z : ℂ)).im) z :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt z hre
  have h0 : (fun x : ℝ => (D.G (x : ℂ)).im) = fun _ => 0 := funext D.G_real
  rw [h0] at him
  rw [← him.deriv]
  simp

/-- Type (i) test function `hbSimpleTest D z p` is in `InAiryClass`, vanishes at every other zero,
and evaluates to `(z - p) Re G'(z)` at `z`. -/
lemma hb_simple_test_props (D : ShellHBData) {z : ℝ} (hz : z ∈ D.S) (p : ℝ) :
    InAiryClass (hbSimpleTest D z p) ∧
    (∀ u : ℝ, u ≠ z → (hbSimpleTest D z p (u : ℂ)).re = ((u - p) / (u - z)) * (D.G (u : ℂ)).re) ∧
    (∀ n : ℕ, hbZeroEnum D n ≠ z → (hbSimpleTest D z p (hbZeroEnum D n : ℂ)).re = 0) ∧
    (hbSimpleTest D z p (z : ℂ)).re = (z - p) * (deriv D.G (z : ℂ)).re ∧
    (deriv D.G (z : ℂ)).re ≠ 0 := by
  have hGz0 : (D.G (z : ℂ)).re = 0 := by rw [D.G_eq_zero_on_S z hz, Complex.zero_re]
  obtain ⟨hdsl_cl, -, -⟩ := deflation_inAiryClass D.G_inAiryClass hGz0
  have hH_cl : InAiryClass (hbSimpleTest D z p) := D.G_inAiryClass.add (hdsl_cl.smul (z - p))
  have hH_ne : ∀ u : ℝ, u ≠ z →
      (hbSimpleTest D z p (u : ℂ)).re = ((u - p) / (u - z)) * (D.G (u : ℂ)).re := by
    intro u huz
    have hne : (u : ℂ) ≠ (z : ℂ) := fun h => huz (Complex.ofReal_injective h)
    have hGz : D.G (z : ℂ) = 0 := D.G_eq_zero_on_S z hz
    have hGu_re : D.G (u : ℂ) = (((D.G (u : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (D.G_real u)
    have hre : hbSimpleTest D z p (u : ℂ) =
        (((u - p) / (u - z) * (D.G (u : ℂ)).re : ℝ) : ℂ) := by
      unfold hbSimpleTest
      rw [dslope_of_ne _ hne, slope_def_field, hGz, sub_zero, hGu_re]
      have hne' : (u : ℂ) - (z : ℂ) ≠ 0 := sub_ne_zero.mpr hne
      push_cast
      simp only [Complex.ofReal_re]
      field_simp
      ring
    rw [hre, Complex.ofReal_re]
  have hH_other : ∀ n : ℕ, hbZeroEnum D n ≠ z →
      (hbSimpleTest D z p (hbZeroEnum D n : ℂ)).re = 0 := fun n hne => by
    rw [hH_ne _ hne, hb_G_eq_zero_at_zero D n, Complex.zero_re, mul_zero]
  have hH_z : (hbSimpleTest D z p (z : ℂ)).re = (z - p) * (deriv D.G (z : ℂ)).re := by
    unfold hbSimpleTest
    rw [D.G_eq_zero_on_S z hz, zero_add, dslope_same, Complex.re_ofReal_mul]
  have hG'ne : (deriv D.G (z : ℂ)).re ≠ 0 := fun hre0 =>
    D.G_deriv_ne_zero z hz (Complex.ext hre0 (hb_G_deriv_im_zero D z))
  exact ⟨hH_cl, hH_ne, hH_other, hH_z, hG'ne⟩

/-- Type (ii) test function `hbPairedTest D k b q` is in `InAiryClass`, vanishes off `{z_k, t_m}`,
and evaluates to `(z_k - b)^2 * ((z_k - q)/(z_k - t_m)) * C_k` (`C_k > 0`) at `z_k`. -/
lemma hb_paired_test_props (D : ShellHBData) {k : ℕ} (hk : D.S.card ≤ k) (b q : ℝ) :
    let zk := hbZeroEnum D k
    InAiryClass (hbPairedTest D k b q) ∧
    (∀ u : ℝ, u ≠ zk → u ≠ D.tm →
      (hbPairedTest D k b q (u : ℂ)).re =
        ((u - b) / (u - zk)) ^ 2 * ((u - q) / (u - D.tm)) * (D.G (u : ℂ)).re) ∧
    (∀ n : ℕ, hbZeroEnum D n ≠ zk → hbZeroEnum D n ≠ D.tm →
      (hbPairedTest D k b q (hbZeroEnum D n : ℂ)).re = 0) ∧
    ∃ Ck : ℝ, 0 < Ck ∧
      (hbPairedTest D k b q (zk : ℂ)).re = (zk - b) ^ 2 * ((zk - q) / (zk - D.tm)) * Ck := by
  intro zk
  let H1 : ℂ → ℂ := fun v => D.G v + ((D.tm - q : ℝ) : ℂ) * dslope D.G (D.tm : ℂ) v
  let H2 : ℂ → ℂ := fun v => H1 v + ((zk - b : ℝ) : ℂ) * dslope H1 (zk : ℂ) v
  let H3 : ℂ → ℂ := hbPairedTest D k b q
  have hH3_eq : ∀ u : ℂ, H3 u = H2 u + ((zk - b : ℝ) : ℂ) * dslope H2 (zk : ℂ) u := fun _ => rfl
  have ht : IsHbZeroEnum D.P D.Q (hbZeroEnum D) := hbZeroEnum_spec D
  set m0 : ℕ := D.S.card - 1
  have hm0_lt : m0 < k := by
    have hpos : 0 < D.S.card := D.S_nonempty.card_pos
    omega
  have htm_eq : hbZeroEnum D m0 = D.tm := (D.tm_eq_hbNode ht).symm
  have hzk_lt_tm : zk < D.tm := htm_eq ▸ ht.1 hm0_lt
  have hzk_ne_tm : zk ≠ D.tm := hzk_lt_tm.ne
  have hzk_S : zk ∉ D.S := fun h => not_le.mpr hzk_lt_tm (D.tm_min zk h)
  have hGtm0 : (D.G (D.tm : ℂ)).re = 0 := by rw [D.G_eq_zero_on_S D.tm D.tm_mem, Complex.zero_re]
  obtain ⟨hdslG_cl, -, -⟩ := deflation_inAiryClass D.G_inAiryClass hGtm0
  have hH1_cl : InAiryClass H1 := D.G_inAiryClass.add (hdslG_cl.smul (D.tm - q))
  have hH1_ne : ∀ u : ℂ, u ≠ (D.tm : ℂ) → H1 u = ((u - (q : ℂ)) / (u - (D.tm : ℂ))) * D.G u := by
    intro u hu
    dsimp [H1]
    rw [dslope_of_ne _ hu, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, sub_zero]
    have hne : u - (D.tm : ℂ) ≠ 0 := sub_ne_zero.mpr hu
    push_cast; field_simp; ring
  have hN_zk : airyPQN D.P D.Q (zk : ℂ) = 0 :=
    (nodeZero_iff D zk).2 ((ht.2 zk).2 ⟨k, rfl⟩)
  have hG_zk : D.G (zk : ℂ) = 0 := hb_G_eq_zero_at_zero D k
  have hG'_zk : deriv D.G (zk : ℂ) = 0 := by
    have he := fun u => D.G_prod_eq u
    have hd1 : deriv (fun u => D.G u * at47_pr D.S u) (zk : ℂ) =
        deriv D.G (zk : ℂ) * at47_pr D.S (zk : ℂ) + D.G (zk : ℂ) * deriv (at47_pr D.S) (zk : ℂ) :=
      ((D.G_diff (zk : ℂ)).hasDerivAt.mul ((at47_pr_differentiable D.S (zk : ℂ)).hasDerivAt)).deriv
    have hNd := differentiable_airyPQN D.P D.Q
    have hd2 : deriv (fun u => (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * airyPQN D.P D.Q u ^ 2) (zk : ℂ) = 0 := by
      have hsq : HasDerivAt (fun u => airyPQN D.P D.Q u ^ 2)
          (2 * airyPQN D.P D.Q (zk : ℂ) ^ 1 * deriv (airyPQN D.P D.Q) (zk : ℂ)) (zk : ℂ) :=
        (hNd (zk : ℂ)).hasDerivAt.pow 2
      have hcm := (hsq.const_mul ((((-1 : ℝ) ^ D.S.card : ℝ) : ℂ))).deriv
      rw [hN_zk, pow_one, mul_zero, zero_mul, mul_zero] at hcm
      exact hcm
    have hfun : (fun u => D.G u * at47_pr D.S u) =
        fun u => (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * airyPQN D.P D.Q u ^ 2 := funext he
    rw [hfun, hd2, hG_zk, zero_mul, add_zero] at hd1
    exact (mul_eq_zero.mp hd1.symm).resolve_right (at47_pr_ne_zero hzk_S)
  have hH1_zk : H1 (zk : ℂ) = 0 := by
    rw [hH1_ne (zk : ℂ) (Complex.ofReal_injective.ne hzk_ne_tm), hG_zk, mul_zero]
  have hH1'_zk : deriv H1 (zk : ℂ) = 0 := by
    have hzkc : (zk : ℂ) ≠ (D.tm : ℂ) := Complex.ofReal_injective.ne hzk_ne_tm
    have hev : H1 =ᶠ[𝓝 (zk : ℂ)] fun u => ((u - (q : ℂ)) / (u - (D.tm : ℂ))) * D.G u := by
      filter_upwards [isOpen_ne.mem_nhds hzkc] with u hu
      exact hH1_ne u hu
    rw [hev.deriv_eq]
    have hd_rat : HasDerivAt (fun u : ℂ => (u - (q : ℂ)) / (u - (D.tm : ℂ)))
        (((1 : ℂ) * ((zk : ℂ) - (D.tm : ℂ)) - ((zk : ℂ) - (q : ℂ)) * 1) /
          ((zk : ℂ) - (D.tm : ℂ)) ^ 2) (zk : ℂ) :=
      ((hasDerivAt_id (zk : ℂ)).sub_const (q : ℂ)).div
        ((hasDerivAt_id (zk : ℂ)).sub_const (D.tm : ℂ)) (sub_ne_zero.mpr hzkc)
    have hm := (hd_rat.mul (D.G_diff (zk : ℂ)).hasDerivAt).deriv
    change deriv (fun u => (u - ↑q) / (u - ↑D.tm) * D.G u) ↑zk =
      ((1 : ℂ) * (↑zk - ↑D.tm) - (↑zk - ↑q) * 1) / (↑zk - ↑D.tm) ^ 2 * D.G ↑zk +
        (↑zk - ↑q) / (↑zk - ↑D.tm) * deriv D.G ↑zk at hm
    simp [hm, hG_zk, hG'_zk]
  have hH1_zk_re : (H1 (zk : ℂ)).re = 0 := by rw [hH1_zk, Complex.zero_re]
  obtain ⟨hdsl1_cl, -, -⟩ := deflation_inAiryClass hH1_cl hH1_zk_re
  have hH2_cl : InAiryClass H2 := hH1_cl.add (hdsl1_cl.smul (zk - b))
  have hH2_ne : ∀ u : ℂ, u ≠ (zk : ℂ) → H2 u = ((u - (b : ℂ)) / (u - (zk : ℂ))) * H1 u := by
    intro u hu
    dsimp [H2]
    rw [dslope_of_ne _ hu, slope_def_field, hH1_zk, sub_zero]
    have hne : u - (zk : ℂ) ≠ 0 := sub_ne_zero.mpr hu
    push_cast; field_simp; ring
  have hH2_zk : H2 (zk : ℂ) = 0 := by
    dsimp [H2]
    rw [hH1_zk, dslope_same, hH1'_zk, mul_zero, add_zero]
  have hH2_zk_re : (H2 (zk : ℂ)).re = 0 := by rw [hH2_zk, Complex.zero_re]
  obtain ⟨hdsl2_cl, -, -⟩ := deflation_inAiryClass hH2_cl hH2_zk_re
  have hH3_cl : InAiryClass H3 :=
    show InAiryClass (fun u => H2 u + ((zk - b : ℝ) : ℂ) * dslope H2 (zk : ℂ) u) from
      hH2_cl.add (hdsl2_cl.smul (zk - b))
  have hH3_neC : ∀ u : ℂ, u ≠ (zk : ℂ) → u ≠ (D.tm : ℂ) →
      H3 u = ((u - (b : ℂ)) / (u - (zk : ℂ))) ^ 2 * ((u - (q : ℂ)) / (u - (D.tm : ℂ))) * D.G u := by
    intro u huk hum
    have hH3_2 : H3 u = ((u - (b : ℂ)) / (u - (zk : ℂ))) * H2 u := by
      rw [hH3_eq, dslope_of_ne _ huk, slope_def_field, hH2_zk, sub_zero]
      have hne : u - (zk : ℂ) ≠ 0 := sub_ne_zero.mpr huk
      push_cast; field_simp; ring
    rw [hH3_2, hH2_ne u huk, hH1_ne u hum]
    ring
  have hH3_ne : ∀ u : ℝ, u ≠ zk → u ≠ D.tm →
      (H3 (u : ℂ)).re = ((u - b) / (u - zk)) ^ 2 * ((u - q) / (u - D.tm)) * (D.G (u : ℂ)).re := by
    intro u huk hum
    rw [hH3_neC (u : ℂ) (Complex.ofReal_injective.ne huk) (Complex.ofReal_injective.ne hum)]
    have hGu : D.G (u : ℂ) = (((D.G (u : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (D.G_real u)
    rw [hGu]
    simp only [← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hH3_other : ∀ n : ℕ, hbZeroEnum D n ≠ zk → hbZeroEnum D n ≠ D.tm →
      (H3 (hbZeroEnum D n : ℂ)).re = 0 := fun n huk hum => by
    rw [hH3_ne _ huk hum, hb_G_eq_zero_at_zero D n, Complex.zero_re, mul_zero]
  set Ck : ℝ := ((airyPQN' D.P D.Q (zk : ℂ)).re) ^ 2 / ∏ t ∈ D.S, (t - zk) with hCk_def
  have hprod_pos : 0 < ∏ t ∈ D.S, (t - zk) :=
    Finset.prod_pos fun t ht => sub_pos.mpr (hzk_lt_tm.trans_le (D.tm_min t ht))
  have hN'ne : (airyPQN' D.P D.Q (zk : ℂ)).re ≠ 0 := (hb_zero_weight_pos_all D hN_zk).2
  have hCk_pos : 0 < Ck := div_pos (sq_pos_of_ne_zero hN'ne) hprod_pos
  have hH3_zk : (H3 (zk : ℂ)).re = (zk - b) ^ 2 * ((zk - q) / (zk - D.tm)) * Ck := by
    let qN : ℂ → ℂ := dslope (airyPQN D.P D.Q) (zk : ℂ)
    have hqN_cont : Continuous qN :=
      (EntireDiv.differentiable_dslope_entire (differentiable_airyPQN D.P D.Q) (zk : ℂ)).continuous
    let L : ℂ → ℂ := fun u =>
      (((u - (b : ℂ)) ^ 2 * ((u - (q : ℂ)) / (u - (D.tm : ℂ)))) *
        ((((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * qN u ^ 2))
    let R : ℂ → ℂ := fun u => H3 u * at47_pr D.S u
    have hR_cont : Continuous R := hH3_cl.1.continuous.mul (at47_pr_differentiable D.S).continuous
    have hL_cont : ContinuousAt L (zk : ℂ) := by
      refine ContinuousAt.mul ?_ (ContinuousAt.const_mul (hqN_cont.continuousAt.pow 2) _)
      refine ((continuous_id.sub continuous_const).pow 2).continuousAt.mul ?_
      exact ((continuous_id.sub continuous_const).continuousAt.div
        (continuous_id.sub continuous_const).continuousAt
        (sub_ne_zero.mpr (Complex.ofReal_injective.ne hzk_ne_tm)))
    have heq_nhds : ∀ᶠ u : ℝ in 𝓝[≠] zk, R (u : ℂ) = L (u : ℂ) := by
      have ho : {u : ℝ | u ≠ zk ∧ u ≠ D.tm} ∈ 𝓝[≠] zk :=
        inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzk_ne_tm))
      refine Filter.Eventually.mono ho fun u hu => ?_
      have huk : (u : ℂ) ≠ (zk : ℂ) := Complex.ofReal_injective.ne hu.1
      have hum : (u : ℂ) ≠ (D.tm : ℂ) := Complex.ofReal_injective.ne hu.2
      have hq : (u : ℂ) - (zk : ℂ) ≠ 0 := sub_ne_zero.mpr huk
      have hds : ((u : ℂ) - (zk : ℂ)) * qN (u : ℂ) = airyPQN D.P D.Q (u : ℂ) := by
        dsimp [qN]
        have e := sub_smul_dslope (airyPQN D.P D.Q) (zk : ℂ) (u : ℂ)
        rwa [hN_zk, sub_zero, smul_eq_mul] at e
      dsimp [R, L]
      rw [hH3_neC (u : ℂ) huk hum]
      calc (((u : ℂ) - (b : ℂ)) / ((u : ℂ) - (zk : ℂ))) ^ 2 *
              (((u : ℂ) - (q : ℂ)) / ((u : ℂ) - (D.tm : ℂ))) * D.G (u : ℂ) * at47_pr D.S (u : ℂ)
          = (((u : ℂ) - (b : ℂ)) ^ 2 * (((u : ℂ) - (q : ℂ)) / ((u : ℂ) - (D.tm : ℂ)))) /
              ((u : ℂ) - (zk : ℂ)) ^ 2 * (D.G (u : ℂ) * at47_pr D.S (u : ℂ)) := by
              field_simp [hq]
        _ = (((u : ℂ) - (b : ℂ)) ^ 2 * (((u : ℂ) - (q : ℂ)) / ((u : ℂ) - (D.tm : ℂ)))) /
              ((u : ℂ) - (zk : ℂ)) ^ 2 *
                ((((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * airyPQN D.P D.Q (u : ℂ) ^ 2) := by
              rw [D.G_prod_eq]
        _ = (((u : ℂ) - (b : ℂ)) ^ 2 * (((u : ℂ) - (q : ℂ)) / ((u : ℂ) - (D.tm : ℂ)))) *
              ((((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * qN (u : ℂ) ^ 2) := by
              rw [← hds]; field_simp [hq]
    have htR : Tendsto (fun u : ℝ => R (u : ℂ)) (𝓝[≠] zk) (𝓝 (R (zk : ℂ))) :=
      (hR_cont.comp Complex.continuous_ofReal).continuousAt.continuousWithinAt
    have htL : Tendsto (fun u : ℝ => L (u : ℂ)) (𝓝[≠] zk) (𝓝 (L (zk : ℂ))) :=
      (hL_cont.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hRL : R (zk : ℂ) = L (zk : ℂ) :=
      tendsto_nhds_unique htR (htL.congr' (heq_nhds.mono fun _ h => h.symm))
    have hqN_zk : qN (zk : ℂ) = airyPQN' D.P D.Q (zk : ℂ) := by
      dsimp [qN]; rw [dslope_same, deriv_airyPQN]
    have hpr_zk : at47_pr D.S (zk : ℂ) =
        (((-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - zk) : ℝ) : ℂ) := by
      unfold at47_pr
      have hsign : ∀ t ∈ D.S, ((zk : ℂ) - (t : ℂ)) = -((t : ℂ) - (zk : ℂ)) := fun _ _ => by ring
      rw [Finset.prod_congr rfl hsign, Finset.prod_neg]
      push_cast; rfl
    have hH3_c : H3 (zk : ℂ) = (((H3 (zk : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hH3_cl.2.2.2 zk)
    have hN'_c : airyPQN' D.P D.Q (zk : ℂ) = (((airyPQN' D.P D.Q (zk : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl (airyPQN'_im_ofReal D.P D.Q zk)
    dsimp [R, L] at hRL
    rw [hqN_zk, hpr_zk, hH3_c, hN'_c] at hRL
    simp only [← Complex.ofReal_sub, ← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      at hRL
    have hRL_re := congrArg Complex.re hRL
    simp only [Complex.ofReal_re] at hRL_re
    have hsign_ne : (-1 : ℝ) ^ D.S.card ≠ 0 := pow_ne_zero _ (by norm_num)
    have heq_fin : (H3 (zk : ℂ)).re * ((-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - zk)) =
        (zk - b) ^ 2 * ((zk - q) / (zk - D.tm)) *
          ((-1 : ℝ) ^ D.S.card * ((airyPQN' D.P D.Q (zk : ℂ)).re) ^ 2) := by
      linear_combination hRL_re
    have hden_ne : (-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - zk) ≠ 0 :=
      mul_ne_zero hsign_ne hprod_pos.ne'
    calc (H3 (zk : ℂ)).re
        = ((zk - b) ^ 2 * ((zk - q) / (zk - D.tm)) *
            ((-1 : ℝ) ^ D.S.card * ((airyPQN' D.P D.Q (zk : ℂ)).re) ^ 2)) /
            ((-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (t - zk)) :=
            eq_div_of_mul_eq hden_ne heq_fin
      _ = (zk - b) ^ 2 * ((zk - q) / (zk - D.tm)) * Ck := by
            rw [hCk_def]; field_simp [hsign_ne, hprod_pos.ne']
  exact ⟨hH3_cl, hH3_ne, hH3_other, Ck, hCk_pos, hH3_zk⟩

/-! ### 3. Lemma WR (`ft:WR` / `sr:WR`) and `ft:C5c` -/

/-- **Lemma WR (`ft:WR` / `sr:WR`)** at any Hermite–Biehler level `D : ShellHBData` (the paper's general real-entire
`N` form is not stated; integrability of the tests against `ν` is an explicit hypothesis):
a positive Radon measure `ν` carried by `S_N = D.S ∪ (-∞, D.tm]` obeying `∫ R G_N dν ≤ ∫ R G_N du`
for every `R ∈ ℛ_N` coincides with the Hermite–Biehler quadrature measure `hbQuadMeasure D`. -/
theorem lemma_WR (D : ShellHBData) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hsupp : ν (hbSupport D)ᶜ = 0)
    (h_one : Integrable (fun u : ℝ => (D.G (u : ℂ)).re) ν ∧
      ∫ u : ℝ, (D.G (u : ℂ)).re ∂ν ≤ ∫ u : ℝ, (D.G (u : ℂ)).re)
    (h_simple : ∀ z ∈ D.S, ∃ δ : ℝ, 0 < δ ∧
      ∀ p : ℝ, 0 < |p - z| → |p - z| < δ → (z = D.tm → p < 0) →
        Integrable (fun u : ℝ => (hbSimpleTest D z p (u : ℂ)).re) ν ∧
        ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re ∂ν ≤
          ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re)
    (h_paired : ∀ k : ℕ, D.S.card ≤ k → ∀ (b q : ℝ),
      b < 0 → b ≠ hbZeroEnum D k → q < 0 → q ≠ D.tm → q ≠ hbZeroEnum D k →
      (∀ t ∈ D.S, t ≠ D.tm → q < t) →
        Integrable (fun u : ℝ => (hbPairedTest D k b q (u : ℂ)).re) ν ∧
        ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re ∂ν ≤
          ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re) :
    ν = hbQuadMeasure D := by
  have ht : IsHbZeroEnum D.P D.Q (hbZeroEnum D) := hbZeroEnum_spec D
  have hconc : ν (Set.range (hbZeroEnum D))ᶜ = 0 := by
    have hGre_int_zero : ∫ u : ℝ, (D.G (u : ℂ)).re = 0 := by
      change ∫ u : ℝ, RCLike.re (D.G (u : ℂ)) = 0
      rw [integral_re D.G_int, D.G_integral_zero]
      simp
    have hnn : ∀ᵐ (u : ℝ) ∂ν, 0 ≤ (D.G (u : ℂ)).re := by
      refine (measure_eq_zero_iff_ae_notMem.1 hsupp).mono fun u hu => ?_
      simp only [mem_compl_iff, not_not, hbSupport, mem_union, Finset.mem_coe, mem_Iic] at hu
      rcases hu with huS | hutm
      · rw [D.G_eq_zero_on_S u huS, Complex.zero_re]
      · exact D.G_nonneg_left u hutm
    have hle0 : ∫ u : ℝ, (D.G (u : ℂ)).re ∂ν ≤ 0 := h_one.2.trans_eq hGre_int_zero
    have hae0 : ∀ᵐ (u : ℝ) ∂ν, (D.G (u : ℂ)).re = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn h_one.1).1 (le_antisymm hle0 (integral_nonneg_of_ae hnn))
    have hae_mem : ∀ᵐ u ∂ν, u ∈ Set.range (hbZeroEnum D) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp, hae0] with u huS huG
      simp only [mem_compl_iff, not_not, hbSupport, mem_union, Finset.mem_coe, mem_Iic] at huS
      rcases huS with huS | hutm
      · exact mem_range_hbZeroEnum_of_mem_S D huS
      · rcases hutm.eq_or_lt with rfl | hlt
        · exact mem_range_hbZeroEnum_of_mem_S D D.tm_mem
        · by_contra hnot
          exact (hb_G_pos_on_Iio_compl D hlt hnot).ne' huG
    exact measure_eq_zero_iff_ae_notMem.2 (hae_mem.mono fun _ h => not_not.mpr h)
  have hweight_of_le_ge : ∀ (x ω v₁ v₂ : ℝ), v₁ < 0 → 0 < v₂ →
      x * v₁ ≤ ω * v₁ → x * v₂ ≤ ω * v₂ → x = ω := by
    intro x ω v₁ v₂ hv₁ hv₂ h₁ h₂
    have hge : ω ≤ x := by nlinarith
    have hle : x ≤ ω := by nlinarith
    exact le_antisymm hle hge
  have hsimple_wt : ∀ n : ℕ, hbZeroEnum D n ∈ D.S →
      (ν {hbZeroEnum D n}).toReal = hbQuadWeight D (hbZeroEnum D n) := by
    intro n hnS
    set z := hbZeroEnum D n
    obtain ⟨δ, hδ, hp⟩ := h_simple z hnS
    have htm_neg : D.tm < 0 := D.tm_le_airyZero_one.trans_lt (airyZero_neg 1)
    set δ' : ℝ := min δ (|D.tm| / 2)
    have hδ' : 0 < δ' := lt_min hδ (half_pos (abs_pos.mpr htm_neg.ne))
    have hstep : ∀ p : ℝ, 0 < |p - z| → |p - z| < δ' →
        (ν {z}).toReal * ((z - p) * (deriv D.G (z : ℂ)).re) ≤
          hbQuadWeight D z * ((z - p) * (deriv D.G (z : ℂ)).re) := by
      intro p hp0 hpδ
      have hpδ' : |p - z| < δ := hpδ.trans_le (min_le_left _ _)
      have hp_tm : z = D.tm → p < 0 := fun hztm => by
        rw [hztm] at hpδ
        have h1 := (abs_lt.mp (hpδ.trans_le (min_le_right _ _))).2
        rw [abs_of_neg htm_neg] at h1
        linarith
      obtain ⟨_, hineq⟩ := hp p hp0 hpδ' hp_tm
      obtain ⟨hH_cl, _, hH_other, hH_z, _⟩ := hb_simple_test_props D hnS p
      have hcont : Continuous fun u : ℝ => (hbSimpleTest D z p (u : ℂ)).re :=
        Complex.continuous_re.comp (hH_cl.1.continuous.comp Complex.continuous_ofReal)
      have hLHS : ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re ∂ν =
          (hbSimpleTest D z p (z : ℂ)).re * (ν {z}).toReal := by
        rw [integral_eq_sum_hbAtoms_finset D hconc hcont {n} fun m hm => by
          have hm' : m ≠ n := by simpa using hm
          exact hH_other m (ht.1.injective.ne hm')]
        simp [z]
      have hRHS : ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re =
          hbQuadWeight D z * (hbSimpleTest D z p (z : ℂ)).re := by
        have hquad := hb_real_quadrature D ht hH_cl
        have hsing : HasSum (fun m : ℕ =>
            airyPQDr D.P D.Q (hbZeroEnum D m) *
              (hbSimpleTest D z p (hbZeroEnum D m : ℂ)).re /
                ((airyPQN' D.P D.Q (hbZeroEnum D m : ℂ)).re) ^ 2)
            (airyPQDr D.P D.Q z * (hbSimpleTest D z p (z : ℂ)).re /
              ((airyPQN' D.P D.Q (z : ℂ)).re) ^ 2) :=
          hasSum_single n fun m hm => by rw [hH_other m (ht.1.injective.ne hm), mul_zero, zero_div]
        rw [hquad.unique hsing]
        unfold hbQuadWeight
        ring
      rw [hLHS, hRHS, hH_z] at hineq
      linarith
    obtain ⟨_, _, _, _, hG'ne⟩ := hb_simple_test_props D hnS z
    set v_pos := (δ' / 2) * (deriv D.G (z : ℂ)).re
    set v_neg := (-(δ' / 2)) * (deriv D.G (z : ℂ)).re
    have hvneg_eq : v_neg = -v_pos := by dsimp [v_pos, v_neg]; ring
    have hp1_abs : 0 < |(z - δ' / 2) - z| ∧ |(z - δ' / 2) - z| < δ' := by
      rw [show (z - δ' / 2) - z = -(δ' / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      exact ⟨by positivity, by linarith⟩
    have hp2_abs : 0 < |(z + δ' / 2) - z| ∧ |(z + δ' / 2) - z| < δ' := by
      rw [show (z + δ' / 2) - z = δ' / 2 by ring, abs_of_pos (by positivity)]
      exact ⟨by positivity, by linarith⟩
    have hs1 : (ν {z}).toReal * v_pos ≤ hbQuadWeight D z * v_pos := by
      simpa [v_pos, show z - (z - δ' / 2) = δ' / 2 by ring] using hstep (z - δ' / 2) hp1_abs.1 hp1_abs.2
    have hs2 : (ν {z}).toReal * v_neg ≤ hbQuadWeight D z * v_neg := by
      simpa [v_neg, show z - (z + δ' / 2) = -(δ' / 2) by ring] using hstep (z + δ' / 2) hp2_abs.1 hp2_abs.2
    rcases lt_or_gt_of_ne hG'ne with hG'neg | hG'pos
    · have hvp : v_pos < 0 := mul_neg_of_pos_of_neg (by positivity) hG'neg
      exact hweight_of_le_ge _ _ v_pos v_neg hvp (by linarith) hs1 hs2
    · have hvp : 0 < v_pos := mul_pos (by positivity) hG'pos
      exact hweight_of_le_ge _ _ v_neg v_pos (by linarith) hvp hs2 hs1
  set m0 : ℕ := D.S.card - 1
  have htm_eq : hbZeroEnum D m0 = D.tm := (D.tm_eq_hbNode ht).symm
  have htm_wt : (ν {D.tm}).toReal = hbQuadWeight D D.tm := by
    rw [← htm_eq]; exact hsimple_wt m0 (by rw [htm_eq]; exact D.tm_mem)
  have hpaired_wt : ∀ k : ℕ, D.S.card ≤ k →
      (ν {hbZeroEnum D k}).toReal = hbQuadWeight D (hbZeroEnum D k) := by
    intro k hk
    set zk := hbZeroEnum D k
    have hm0_lt : m0 < k := by have := D.S_nonempty.card_pos; omega
    have hzk_lt_tm : zk < D.tm := htm_eq ▸ ht.1 hm0_lt
    have htm_neg : D.tm < 0 := D.tm_le_airyZero_one.trans_lt (airyZero_neg 1)
    have hzk_neg : zk < 0 := hzk_lt_tm.trans htm_neg
    set b : ℝ := zk - 1
    have hb0 : b < 0 := by linarith
    have hbz : b ≠ zk := by linarith
    have hstep : ∀ q : ℝ, q < 0 → q ≠ D.tm → q ≠ zk → (∀ t ∈ D.S, t ≠ D.tm → q < t) →
        (ν {zk}).toReal * (hbPairedTest D k b q (zk : ℂ)).re ≤
          hbQuadWeight D zk * (hbPairedTest D k b q (zk : ℂ)).re := by
      intro q hq0 hqm hqz hq_prev
      obtain ⟨_, hineq⟩ := h_paired k hk b q hb0 hbz hq0 hqm hqz hq_prev
      obtain ⟨hH_cl, _, hH_other, Ck, hCk_pos, hH_zk⟩ := hb_paired_test_props D hk b q
      have hcont : Continuous fun u : ℝ => (hbPairedTest D k b q (u : ℂ)).re :=
        Complex.continuous_re.comp (hH_cl.1.continuous.comp Complex.continuous_ofReal)
      have hLHS : ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re ∂ν =
          (hbPairedTest D k b q (D.tm : ℂ)).re * (ν {D.tm}).toReal +
            (hbPairedTest D k b q (zk : ℂ)).re * (ν {zk}).toReal := by
        rw [integral_eq_sum_hbAtoms_finset D hconc hcont {m0, k} fun m hm => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
          exact hH_other m (ht.1.injective.ne hm.2) (htm_eq ▸ ht.1.injective.ne hm.1)]
        rw [Finset.sum_pair hm0_lt.ne, htm_eq]
      have hRHS : ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re =
          hbQuadWeight D D.tm * (hbPairedTest D k b q (D.tm : ℂ)).re +
            hbQuadWeight D zk * (hbPairedTest D k b q (zk : ℂ)).re := by
        have hquad := hb_real_quadrature D ht hH_cl
        let g : ℕ → ℝ := fun m =>
          airyPQDr D.P D.Q (hbZeroEnum D m) *
            (hbPairedTest D k b q (hbZeroEnum D m : ℂ)).re /
              ((airyPQN' D.P D.Q (hbZeroEnum D m : ℂ)).re) ^ 2
        have hfin_eq : ∑ m ∈ ({m0, k} : Finset ℕ), g m =
            ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re := by
          rw [← hquad.tsum_eq, tsum_eq_sum]
          intro m hm
          have h0 : (hbPairedTest D k b q (hbZeroEnum D m : ℂ)).re = 0 := by
            by_contra hne
            apply hm
            by_cases h1 : m = m0
            · simp [h1]
            · by_cases h2 : m = k
              · simp [h2]
              · exact False.elim (hne (hH_other m (ht.1.injective.ne h2) (htm_eq ▸ ht.1.injective.ne h1)))
          simp [h0]
        rw [← hfin_eq, Finset.sum_pair hm0_lt.ne]
        dsimp [g]; rw [htm_eq]; unfold hbQuadWeight; ring
      rw [hLHS, hRHS, htm_wt] at hineq
      linarith
    set q₁ : ℝ := zk - 1
    set q₂ : ℝ := (zk + D.tm) / 2
    have hq_all : ∀ t ∈ D.S, t ≠ D.tm → q₁ < t ∧ q₂ < t := fun t htS _ => by
      have htm_le : D.tm ≤ t := D.tm_min t htS
      dsimp [q₁, q₂]
      exact ⟨by linarith, by linarith⟩
    have hs1 := hstep q₁ (by dsimp [q₁]; linarith) (by dsimp [q₁]; linarith)
      (by dsimp [q₁]; linarith) fun t htS hne => (hq_all t htS hne).1
    have hs2 := hstep q₂ (by dsimp [q₂]; linarith) (by dsimp [q₂]; linarith)
      (by dsimp [q₂]; linarith) fun t htS hne => (hq_all t htS hne).2
    obtain ⟨_, _, _, Ck1, hCk1, hH_zk1⟩ := hb_paired_test_props D hk b q₁
    obtain ⟨_, _, _, Ck2, hCk2, hH_zk2⟩ := hb_paired_test_props D hk b q₂
    have hv1_neg : (hbPairedTest D k b q₁ (zk : ℂ)).re < 0 := by
      rw [hH_zk1]
      have hqnum : 0 < zk - q₁ := by dsimp [q₁]; linarith
      have hqden : zk - D.tm < 0 := by linarith
      have hratio : (zk - q₁) / (zk - D.tm) < 0 := div_neg_of_pos_of_neg hqnum hqden
      have hsq : 0 < (zk - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hbz.symm)
      nlinarith
    have hv2_pos : 0 < (hbPairedTest D k b q₂ (zk : ℂ)).re := by
      rw [hH_zk2]
      have hqnum : zk - q₂ < 0 := by dsimp [q₂]; linarith
      have hqden : zk - D.tm < 0 := by linarith
      have hratio : 0 < (zk - q₂) / (zk - D.tm) := div_pos_of_neg_of_neg hqnum hqden
      have hsq : 0 < (zk - b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hbz.symm)
      nlinarith
    exact hweight_of_le_ge _ _ _ _ hv1_neg hv2_pos hs1 hs2
  have hall_wt : ∀ n : ℕ, ν {hbZeroEnum D n} = ENNReal.ofReal (hbQuadWeight D (hbZeroEnum D n)) := by
    intro n
    have htoReal : (ν {hbZeroEnum D n}).toReal = hbQuadWeight D (hbZeroEnum D n) := by
      by_cases hn : n < D.S.card
      · have hm0_eq : hbZeroEnum D (D.S.card - 1) = D.tm := (D.tm_eq_hbNode ht).symm
        by_cases hnS : hbZeroEnum D n ∈ D.S
        · exact hsimple_wt n hnS
        · exfalso; apply hnS
          have hlt_tm : hbZeroEnum D n < D.tm :=
            D.S_top (hbZeroEnum D n)
              ((nodeZero_iff D (hbZeroEnum D n)).2 (((hbZeroEnum_spec D).2 _).2 ⟨n, rfl⟩))
              hnS D.tm D.tm_mem
          have hm0_le : D.S.card - 1 < n :=
            ht.1.lt_iff_gt.1 (hm0_eq.symm ▸ hlt_tm : hbZeroEnum D n < hbZeroEnum D (D.S.card - 1))
          omega
      · exact hpaired_wt n (not_lt.mp hn)
    have hne : ν {hbZeroEnum D n} ≠ ⊤ := (measure_singleton_lt_top (μ := ν)).ne
    rw [← ENNReal.ofReal_toReal hne, htoReal]
  calc ν = Measure.sum fun n => ν {hbZeroEnum D n} • Measure.dirac (hbZeroEnum D n) :=
        measure_eq_sum_hbAtoms D hconc
    _ = hbQuadMeasure D := by unfold hbQuadMeasure; congr 1; ext n; rw [hall_wt n]

private noncomputable def FTDesign.toSeqDesign {S : FoldTipSetting} {X : FTCrossingData S}
    {W : ℝ → ℝ} (hdes : FTDesign X W) {cs : ℕ → ℝ} {ν : ℕ → Measure ℝ}
    (hcs : Tendsto cs atTop atTop) (hν : ∀ j, ν j ∈ X.extremal (cs j)) :
    SeqDesign (fun j => X.window (cs j) (ν j)) :=
  let hU := Classical.choose_spec hdes.2.2
  let hc0 := Classical.choose_spec hU.1
  let b := Classical.choose hU.2.1
  let hb := Classical.choose_spec hU.2.1
  let hev : ∀ᶠ j in atTop, Classical.choose hU.1 ≤ cs j :=
    hcs.eventually_ge_atTop (Classical.choose hU.1)
  { U := fun j => Classical.choose hdes.2.2 (cs j)
    W := W
    b := b
    W_cont := hdes.1
    W_int := hdes.2.1
    U_cont := hev.mono fun j hj => (hc0 (cs j) hj).1
    U_int_vol := hev.mono fun j hj => (hc0 (cs j) hj).2.1
    U_int_mu := hev.mono fun j hj => ((hc0 (cs j) hj).2.2 (ν j) (hν j)).1
    pairing := hev.mono fun j hj => ((hc0 (cs j) hj).2.2 (ν j) (hν j)).2
    nonneg_left := hcs.eventually hb
    window_limit := by
      have hU3 := hU.2.2.1
      rw [tendstoLocallyUniformly_iff_forall_isCompact] at hU3 ⊢
      intro K hK ε hε
      exact hcs.eventually (hU3 K hK ε hε)
    limsup_le := fun ε hε => hcs.eventually (hU.2.2.2 ε hε) }

/-- **Conclusion `ft:C5c` of Theorem FT (`fold_dual_measures.tex`)**:
under `FTH4b D X` alone at any polynomial Hermite–Biehler level `D : ShellHBData`, along every sequence
`cs j → ∞` of extremal dual measures `ν j ∈ X.extremal (cs j)`:
1. the rescaled window measures `μ j = X.window (cs j) (ν j)` are locally bounded;
2. `μ j` converges vaguely along the whole sequence to `hbQuadMeasure D` (`∑_n ω_n δ_{t_n}`);
3. no positive pairing mass escapes along any design whose limit `W` satisfies `∫ W dμ_H = ∫ W du`. -/
theorem ft_C5c {S : FoldTipSetting} (D : ShellHBData) (X : FTCrossingData S) (hH4b : FTH4b D X)
    (cs : ℕ → ℝ) (ν : ℕ → Measure ℝ) (hcs : Tendsto cs atTop atTop)
    (hν : ∀ j, ν j ∈ X.extremal (cs j)) :
    let μ : ℕ → Measure ℝ := fun j => X.window (cs j) (ν j)
    ∃ j₀ : ℕ, (∀ j, j₀ ≤ j → IsLocallyFiniteMeasure (μ j)) ∧
      (∀ (μ' : ℕ → Measure ℝ), (∀ j, μ' j = μ (j + j₀)) →
        LocallyBounded μ' ∧
        IsVagueLimit atTop μ' (hbQuadMeasure D) ∧
        ∀ {W : ℝ → ℝ}, FTDesign X W →
          (Integrable W (hbQuadMeasure D) ∧ ∫ u, W u ∂(hbQuadMeasure D) = ∫ u, W u) →
          ∀ (des : SeqDesign μ'), des.W = W →
            ∀ {ε : ℝ}, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
              ∀ᶠ j in atTop, ∫ u in Iio (-R), des.U j u ∂(μ' j) ≤ ε) := by
  intro μ
  obtain ⟨B, hB⟩ := hH4b.support_upper
  obtain ⟨c1, hc1⟩ := eventually_atTop.1 hB
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hcs.eventually_ge_atTop c1)
  have hloc : ∀ j, j₀ ≤ j → IsLocallyFiniteMeasure (μ j) := fun j hj =>
    (hc1 (cs j) (hj₀ j hj) (ν j) (hν j)).1
  refine ⟨j₀, hloc, fun μ' hμ' => ?_⟩
  let cs' : ℕ → ℝ := fun j => cs (j + j₀)
  let ν' : ℕ → Measure ℝ := fun j => ν (j + j₀)
  have hcs' : Tendsto cs' atTop atTop := hcs.comp (tendsto_add_atTop_nat j₀)
  have hν' : ∀ j, ν' j ∈ X.extremal (cs' j) := fun j => hν (j + j₀)
  let : ∀ j, IsLocallyFiniteMeasure (μ' j) := fun j => by
    rw [hμ' j]; exact hloc (j + j₀) (Nat.le_add_left j₀ j)
  have hB' : ∀ᶠ j in atTop, μ' j (Ioi B) = 0 :=
    Eventually.of_forall fun j => by
      rw [hμ' j]; exact (hc1 (cs' j) (hj₀ (j + j₀) (Nat.le_add_left j₀ j)) (ν' j) (hν' j)).2
  have hlim' : ∀ (ns : ℕ → ℕ) (xs : ℕ → ℝ) (x : ℝ), StrictMono ns →
      (∀ k, xs k ∈ (μ' (ns k)).support) → Tendsto xs atTop (𝓝 x) → x ∈ hbSupport D := by
    intro ns xs x hns hxs hx
    have hxs' : ∀ k, xs k ∈ (X.window (cs' (ns k)) (ν' (ns k))).support := fun k => by
      simpa [μ, hμ'] using hxs k
    exact hH4b.support_limit (cs' ∘ ns) (ν' ∘ ns) xs x (hcs'.comp hns.tendsto_atTop)
      (fun k => hν' (ns k)) hxs' hx
  obtain ⟨W₀, hW₀_pos, hdes₀⟩ := hH4b.pos_design
  let seq₀ : SeqDesign μ' :=
    let s := hdes₀.toSeqDesign hcs' hν'
    { s with
      U_int_mu := s.U_int_mu.mono fun j hj => by simpa [μ, hμ'] using hj
      pairing := s.pairing.mono fun j hj => by simpa [μ, hμ'] using hj }
  have hbd : LocallyBounded μ' :=
    wp_locallyBounded μ' (isClosed_hbSupport D) hB' hlim' seq₀ hW₀_pos
  have hvague : IsVagueLimit atTop μ' (hbQuadMeasure D) := by
    intro g hg hcsg
    rw [Filter.tendsto_iff_ultrafilter]
    intro 𝒰 h𝒰
    obtain ⟨ν_lim, hlf, hν_lim⟩ := exists_vagueLimit μ' hbd 𝒰 h𝒰
    have hcar := wp_vagueLimit_carried (isClosed_hbSupport D) hB' hlim' h𝒰 hν_lim
    let hto_seq : ∀ {W : ℝ → ℝ}, FTDesign X W → SeqDesign μ' := fun hdes =>
      let s := hdes.toSeqDesign hcs' hν'
      { s with
        U_int_mu := s.U_int_mu.mono fun j hj => by simpa [μ, hμ'] using hj
        pairing := s.pairing.mono fun j hj => by simpa [μ, hμ'] using hj }
    have h_one : Integrable (fun u : ℝ => (D.G (u : ℂ)).re) ν_lim ∧
        ∫ u : ℝ, (D.G (u : ℂ)).re ∂ν_lim ≤ ∫ u : ℝ, (D.G (u : ℂ)).re := by
      have h := wp_integral_le hbd hB' h𝒰 hν_lim hcar.2 (hto_seq hH4b.test_one)
      exact ⟨h.1, h.2.1⟩
    have h_simple : ∀ z ∈ D.S, ∃ δ : ℝ, 0 < δ ∧
        ∀ p : ℝ, 0 < |p - z| → |p - z| < δ → (z = D.tm → p < 0) →
          Integrable (fun u : ℝ => (hbSimpleTest D z p (u : ℂ)).re) ν_lim ∧
          ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re ∂ν_lim ≤
            ∫ u : ℝ, (hbSimpleTest D z p (u : ℂ)).re := by
      intro z hz
      obtain ⟨δ, hδ, hp⟩ := hH4b.test_simple z hz
      refine ⟨δ, hδ, fun p hp0 hpδ hptm => ?_⟩
      have h := wp_integral_le hbd hB' h𝒰 hν_lim hcar.2 (hto_seq (hp p hp0 hpδ hptm))
      exact ⟨h.1, h.2.1⟩
    have h_paired : ∀ k : ℕ, D.S.card ≤ k → ∀ (b q : ℝ),
        b < 0 → b ≠ hbZeroEnum D k → q < 0 → q ≠ D.tm → q ≠ hbZeroEnum D k →
        (∀ t ∈ D.S, t ≠ D.tm → q < t) →
          Integrable (fun u : ℝ => (hbPairedTest D k b q (u : ℂ)).re) ν_lim ∧
          ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re ∂ν_lim ≤
            ∫ u : ℝ, (hbPairedTest D k b q (u : ℂ)).re := by
      intro k hk b q hb0 hbz hq0 hqm hqz hq_prev
      have h := wp_integral_le hbd hB' h𝒰 hν_lim hcar.2
        (hto_seq (hH4b.test_paired k hk b q hb0 hbz hq0 hqm hqz hq_prev))
      exact ⟨h.1, h.2.1⟩
    have heq_meas : ν_lim = hbQuadMeasure D := lemma_WR D hcar.1 h_one h_simple h_paired
    rw [← heq_meas]
    exact hν_lim g hg hcsg
  let : IsLocallyFiniteMeasure (hbQuadMeasure D) := isLocallyFiniteMeasure_hbQuadMeasure D
  have hνB : hbQuadMeasure D (Ioi B) = 0 :=
    (wp_vagueLimit_carried (isClosed_hbSupport D) hB' hlim' le_rfl hvague).2
  refine ⟨hbd, hvague, fun {W} _ ⟨_, heqW⟩ des hdesW {ε} hε => ?_⟩
  exact wp_no_escape hbd hB' le_rfl hvague hνB des (hdesW ▸ heqW) hε

end FormalResearch.ModularBootstrap.FoldTip

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.hbQuadMeasure_airy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.hbQuadMeasure_airy_eq

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.lemma_WR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.lemma_WR

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ft_C5c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ft_C5c
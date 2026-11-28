module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Core

/-!
# Window pairing (`ft:WP` / `sr:window-pairing`, Paper I Lemma WP)

Measure-theoretic window-pairing engine (`CFT/sign_uncertainty/paper/fold_dual_measures.tex`,
Lemma WP): for positive Radon measures `μ_j` on `ℝ` whose supports are uniformly bounded above by `B`
with all finite limit points in a closed set `S`, and sequential one-sided designs `U_j → W`
satisfying `(D1)–(D4)`:

* **`wp_locallyBounded`**: if one design has `W₀ > 0` on `S`, then `μ_j` is `LocallyBounded`;
* **`wp_vagueLimit_carried`**: every vague limit `ν` is carried by `S` (`ν Sᶜ = 0`) and `(-∞, B]`;
* **`wp_integral_le`**: for every design, `W ∈ L¹(ν)` and `∫ W dν ≤ ∫ W du` (`ft:wp-limit`);
* **`wp_no_escape`**: if equality `∫ W dν = ∫ W du` holds along `l ≤ atTop` with vague limit `ν`,
  then `limsup_{j ∈ l} ∫_{u < -R} U_j dμ_j → 0` as `R → ∞`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- Sequential one-sided design `(D1)–(D4)` for `μ : ℕ → Measure ℝ` and continuous `W ∈ L¹(ℝ)`. -/
structure SeqDesign (μ : ℕ → Measure ℝ) where
  U : ℕ → ℝ → ℝ
  W : ℝ → ℝ
  b : ℝ
  W_cont : Continuous W
  W_int : Integrable W
  U_cont : ∀ᶠ j in atTop, Continuous (U j)
  U_int_vol : ∀ᶠ j in atTop, Integrable (U j)
  U_int_mu : ∀ᶠ j in atTop, Integrable (U j) (μ j)
  pairing : ∀ᶠ j in atTop, ∫ u, U j u ∂(μ j) ≤ ∫ u, U j u
  nonneg_left : ∀ᶠ j in atTop, ∀ u : ℝ, u ≤ b → 0 ≤ U j u
  window_limit : TendstoLocallyUniformly U W atTop
  limsup_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∫ u : ℝ, U j u ≤ (∫ u : ℝ, W u) + ε

lemma SeqDesign.W_nonneg_left {μ : ℕ → Measure ℝ} (des : SeqDesign μ) {u : ℝ} (hu : u ≤ des.b) :
    0 ≤ des.W u := by
  have hlim : Tendsto (fun j => des.U j u) atTop (𝓝 (des.W u)) := by
    have hu_unif := (tendstoLocallyUniformly_iff_forall_isCompact.1 des.window_limit) {u}
      isCompact_singleton
    rw [Metric.tendstoUniformlyOn_iff] at hu_unif
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hu_unif ε hε] with j hj
    rw [dist_comm]
    exact hj u (Set.mem_singleton u)
  exact ge_of_tendsto hlim (des.nonneg_left.mono fun _ hj => hj u hu)

lemma eventually_compl_compact_mem_support {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {S : Set ℝ}
    (hlim : ∀ (ns : ℕ → ℕ) (xs : ℕ → ℝ) (x : ℝ), StrictMono ns →
      (∀ k, xs k ∈ (μ (ns k)).support) → Tendsto xs atTop (𝓝 x) → x ∈ S)
    {K : Set ℝ} (hKc : IsCompact K) (hdisj : Disjoint K S) :
    ∀ᶠ j in atTop, μ j K = 0 := by
  by_contra hnot
  have hfreq : ∀ N : ℕ, ∃ j ≥ N, ∃ x ∈ K, x ∈ (μ j).support := by
    intro N
    obtain ⟨j, hjN, hjpos⟩ := Filter.frequently_atTop.1 (Filter.not_eventually.mp hnot) N
    refine ⟨j, hjN, ?_⟩
    by_contra hemp
    push Not at hemp
    exact hjpos (Measure.measure_eq_zero_of_isCompact_subset_compl_support hKc fun x hx => hemp x hx)
  choose next hnext using fun n : ℕ => hfreq n
  let ns : ℕ → ℕ := Nat.rec (next 0) (fun _ prev => next (prev + 1))
  have hns : StrictMono ns := strictMono_nat_of_lt_succ fun k =>
    Nat.lt_of_succ_le (hnext (ns k + 1)).1
  have hxs : ∀ k, ∃ x ∈ K, x ∈ (μ (ns k)).support := fun k => by
    induction k with
    | zero => exact (hnext 0).2
    | succ k _ => exact (hnext (ns k + 1)).2
  choose xs hxK hxsupp using hxs
  obtain ⟨x, hxK0, φ, hφ, hφlim⟩ := hKc.isSeqCompact hxK
  have hxS : x ∈ S := hlim (ns ∘ φ) (xs ∘ φ) x (hns.comp hφ) (fun k => hxsupp (φ k)) hφlim
  exact hdisj.le_bot ⟨hxK0, hxS⟩

/-- **Local boundedness in Lemma WP (`ft:WP`)**: if one design has `W₀ > 0` on `S`, then `μ_j` is
locally bounded. -/
theorem wp_locallyBounded (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    {S : Set ℝ} (hS_closed : IsClosed S) {B : ℝ}
    (hB : ∀ᶠ j in atTop, μ j (Ioi B) = 0)
    (hlim : ∀ (ns : ℕ → ℕ) (xs : ℕ → ℝ) (x : ℝ), StrictMono ns →
      (∀ k, xs k ∈ (μ (ns k)).support) → Tendsto xs atTop (𝓝 x) → x ∈ S)
    (des0 : SeqDesign μ) (hpos : ∀ u ∈ S, 0 < des0.W u) :
    LocallyBounded μ := by
  intro K hK
  obtain ⟨L, hL⟩ := hK.bddBelow
  set a : ℝ := min L des0.b
  set I : Set ℝ := Icc a B with hI_def
  have hIc : IsCompact I := isCompact_Icc
  have hK_le : ∀ᶠ j in atTop, (μ j K).toReal ≤ (μ j I).toReal := by
    filter_upwards [hB] with j hjB
    have hKI : μ j K ≤ μ j I := by
      have hsub : K ⊆ I ∪ Ioi B := fun u hu =>
        if h : u ≤ B then Or.inl ⟨(min_le_left _ _).trans (hL hu), h⟩ else Or.inr (not_le.mp h)
      calc μ j K ≤ μ j (I ∪ Ioi B) := measure_mono hsub
        _ ≤ μ j I + μ j (Ioi B) := measure_union_le _ _
        _ = μ j I := by rw [hjB, add_zero]
    exact ENNReal.toReal_mono hIc.measure_lt_top.ne hKI
  set IS : Set ℝ := I ∩ S
  have hISc : IsCompact IS := hIc.inter_right hS_closed
  by_cases hne : IS.Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := hISc.exists_isMinOn hne des0.W_cont.continuousOn
    have hm : 0 < des0.W u₀ := hpos u₀ hu₀.2
    set m : ℝ := des0.W u₀
    set I0 : Set ℝ := {u ∈ I | des0.W u ≤ m / 2}
    have hI0c : IsCompact I0 :=
      hIc.of_isClosed_subset (hIc.isClosed.inter (isClosed_le des0.W_cont continuous_const))
        fun _ hu => hu.1
    have hdisj : Disjoint I0 S := by
      rw [Set.disjoint_left]
      intro u hu0 huS
      have hminu : m ≤ des0.W u := hmin ⟨hu0.1, huS⟩
      linarith [hu0.2]
    have hI0_null : ∀ᶠ j in atTop, μ j I0 = 0 :=
      eventually_compl_compact_mem_support hlim hI0c hdisj
    set Ipos : Set ℝ := {u ∈ I | m / 2 ≤ des0.W u}
    have hIpos_c : IsCompact Ipos :=
      hIc.of_isClosed_subset (hIc.isClosed.inter (isClosed_le continuous_const des0.W_cont))
        fun _ hu => hu.1
    have hI_sub : I ⊆ I0 ∪ Ipos := fun u hu =>
      if h : des0.W u ≤ m / 2 then Or.inl ⟨hu, h⟩ else Or.inr ⟨hu, (not_le.mp h).le⟩
    have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 des0.window_limit) Ipos hIpos_c
    have hev_unif : ∀ᶠ j in atTop, ∀ x ∈ Ipos, dist (des0.W x) (des0.U j x) < m / 4 :=
      Metric.tendstoUniformlyOn_iff.1 hunif (m / 4) (by positivity)
    set M_bound : ℝ := 4 * ((∫ u : ℝ, des0.W u) + 1) / m
    refine ⟨max M_bound 0, ?_⟩
    filter_upwards [hK_le, hB, hI0_null, des0.U_int_mu, des0.pairing,
      des0.nonneg_left, des0.limsup_le 1 one_pos, hev_unif]
      with j hj_le hjB hjI0 hj_int_mu hj_pair hj_nn hj_lim hj_unif
    have hI_le_Ipos : (μ j I).toReal ≤ (μ j Ipos).toReal := by
      have h1 : μ j I ≤ μ j Ipos := by
        calc μ j I ≤ μ j (I0 ∪ Ipos) := measure_mono hI_sub
          _ ≤ μ j I0 + μ j Ipos := measure_union_le _ _
          _ = μ j Ipos := by rw [hjI0, zero_add]
      exact ENNReal.toReal_mono hIpos_c.measure_lt_top.ne h1
    have hlow : ∀ u ∈ Ipos, m / 4 ≤ des0.U j u := fun u hu => by
      have hd := hj_unif u hu
      rw [Real.dist_eq] at hd
      have h1 := (abs_lt.mp hd).2
      linarith [hu.2]
    have hoff : ∀ᵐ u ∂(μ j), u ∉ Ipos → 0 ≤ des0.U j u := by
      have haeB : ∀ᵐ u ∂(μ j), u ≤ B := ae_le_of_supp hjB
      have haeI0 : ∀ᵐ u ∂(μ j), u ∉ I0 := measure_eq_zero_iff_ae_notMem.1 hjI0
      filter_upwards [haeB, haeI0] with u huB huI0 hnot
      by_cases huI : u ∈ I
      · rcases hI_sub huI with h0 | h1
        · exact False.elim (huI0 h0)
        · exact False.elim (hnot h1)
      · rw [hI_def, mem_Icc, not_and_or, not_le, not_le] at huI
        rcases huI with hua | hBu
        · exact hj_nn u (hua.le.trans (min_le_right _ _))
        · exact False.elim (not_lt.mpr huB hBu)
    have hmain := const_mul_measure_le_integral hj_int_mu hIpos_c.measurableSet
      hIpos_c.measure_lt_top hlow hoff
    have hbd_pos : (m / 4) * (μ j Ipos).toReal ≤ (∫ u : ℝ, des0.W u) + 1 :=
      hmain.trans (hj_pair.trans hj_lim)
    have hIpos_le : (μ j Ipos).toReal ≤ M_bound := by
      rw [le_div_iff₀ hm]
      linarith
    exact (hj_le.trans (hI_le_Ipos.trans hIpos_le)).trans (le_max_left _ _)
  · have hdisj : Disjoint I S := Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
    have hI_null : ∀ᶠ j in atTop, μ j I = 0 :=
      eventually_compl_compact_mem_support hlim hIc hdisj
    refine ⟨0, ?_⟩
    filter_upwards [hK_le, hI_null] with j hj hj0
    simpa [hj0] using hj

/-- Any vague limit `ν` along `l ≤ atTop` is carried by `S` and `(-∞, B]`. -/
theorem wp_vagueLimit_carried {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {S : Set ℝ} (hS_closed : IsClosed S) {B : ℝ}
    (hB : ∀ᶠ j in atTop, μ j (Ioi B) = 0)
    (hlim : ∀ (ns : ℕ → ℕ) (xs : ℕ → ℝ) (x : ℝ), StrictMono ns →
      (∀ k, xs k ∈ (μ (ns k)).support) → Tendsto xs atTop (𝓝 x) → x ∈ S)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit l μ ν) :
    ν Sᶜ = 0 ∧ ν (Ioi B) = 0 := by
  have hnull_of_compact : ∀ {O : Set ℝ}, IsOpen O →
      (∀ {K : Set ℝ}, IsCompact K → K ⊆ O → ∀ᶠ j in atTop, μ j K = 0) → ν O = 0 := by
    intro O hO hK_null
    rw [hO.measurableSet.measure_eq_iSup_isCompact]
    refine ENNReal.iSup_eq_zero.2 fun K => ENNReal.iSup_eq_zero.2 fun hKO =>
      ENNReal.iSup_eq_zero.2 fun hKc => ?_
    obtain ⟨r, hr_pos, hr_sub⟩ := hKc.exists_cthickening_subset_open hO hKO
    obtain ⟨f, hfK, hfU, hfcs, hf01⟩ :=
      exists_continuous_one_zero_of_isCompact hKc Metric.isOpen_thickening.isClosed_compl
        (Set.disjoint_compl_right_iff_subset.mpr (Metric.self_subset_thickening hr_pos K))
    have hKts : IsCompact (tsupport f) := hfcs
    have hts_U : tsupport f ⊆ Metric.cthickening r K := by
      refine (closure_minimal ?_ Metric.isClosed_cthickening).trans Subset.rfl
      have hsupp_th : Function.support f ⊆ Metric.thickening r K := fun x hx => by
        by_contra hnot; exact hx (hfU hnot)
      exact hsupp_th.trans (Metric.thickening_subset_cthickening r K)
    have htsO : tsupport f ⊆ O := hts_U.trans hr_sub
    have hev0 : ∀ᶠ j in atTop, μ j (tsupport f) = 0 := hK_null hKts htsO
    have hint0 : ∀ᶠ j in l, ∫ u, f u ∂(μ j) = 0 := by
      refine (hev0.filter_mono hl).mono fun j hj => ?_
      refine integral_eq_zero_of_ae ?_
      have hae : ∀ᵐ u ∂(μ j), u ∉ tsupport f := measure_eq_zero_iff_ae_notMem.1 hj
      exact hae.mono fun u hu => image_eq_zero_of_notMem_tsupport hu
    have h0 : ∫ u, f u ∂ν = 0 :=
      tendsto_nhds_unique (hν f f.continuous hfcs)
        (tendsto_const_nhds.congr' (hint0.mono fun _ hj => hj.symm))
    have h1 : ν K ≤ ENNReal.ofReal (∫ u, f u ∂ν) :=
      (integrable_of_cs f.continuous hfcs).measure_le_integral
        (Eventually.of_forall fun x => (hf01 x).1) (fun x hx => by simp [hfK hx])
    rw [h0] at h1
    simpa using h1
  refine ⟨hnull_of_compact hS_closed.isOpen_compl fun {K} hKc hKS => ?_,
    hnull_of_compact isOpen_Ioi fun {K} hKc hKB => ?_⟩
  · exact eventually_compl_compact_mem_support hlim hKc
      (Set.disjoint_left.2 fun _ hxK hxS => hKS hxK hxS)
  · filter_upwards [hB] with j hjB
    exact measure_mono_null hKB hjB

/-- Cutoff inequality for any one-sided design: `∫ cutoff A B₀ · W dν ≤ ∫ W` when `A ≤ b` and
`B ≤ B₀`. -/
theorem wp_cutoff_ineq {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) {B : ℝ} (hB : ∀ᶠ j in atTop, μ j (Ioi B) = 0)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop) {ν : Measure ℝ} (hν : IsVagueLimit l μ ν)
    (des : SeqDesign μ) {A B₀ : ℝ} (hA : A ≤ des.b) (hB₀ : B ≤ B₀) :
    ∫ u, cutoff A B₀ u * des.W u ∂ν ≤ ∫ u, des.W u := by
  set K : Set ℝ := Icc (A - 1) (B₀ + 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hbd K hKc
  set M' : ℝ := max M 0
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 des.window_limit) K hKc
  have key : ∀ ε : ℝ, 0 < ε → ∫ u, cutoff A B₀ u * des.W u ∂ν ≤ (∫ u, des.W u) + ε * (1 + M') := by
    intro ε hε
    have hev : ∀ᶠ j in atTop,
        ∫ u, cutoff A B₀ u * des.W u ∂(μ j) ≤ (∫ u, des.W u) + ε * (1 + M') := by
      have h4 : ∀ᶠ j in atTop, ∀ x ∈ K, dist (des.W x) (des.U j x) < ε :=
        Metric.tendstoUniformlyOn_iff.1 hunif ε hε
      filter_upwards [hB, des.U_int_mu, des.pairing, des.nonneg_left, des.limsup_le ε hε, h4, hM]
        with j hjB hj_int_mu hj_pair hj_nn hj_lim hj4 hj5
      have hint1 : Integrable (fun u => cutoff A B₀ u * des.U j u) (μ j) := by
        refine hj_int_mu.bdd_mul (c := 1) (cutoff_continuous A B₀).aestronglyMeasurable ?_
        exact Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B₀ u)]; exact cutoff_le_one A B₀ u
      have hle1 : ∫ u, cutoff A B₀ u * des.U j u ∂(μ j) ≤ ∫ u, des.U j u ∂(μ j) := by
        refine integral_mono_ae hint1 hj_int_mu ?_
        filter_upwards [ae_le_of_supp hjB] with u huB
        by_cases hcase : A ≤ u
        · rw [cutoff_eq_one hcase (huB.trans hB₀), one_mul]
        · push Not at hcase
          have hnn := hj_nn u (hcase.le.trans hA)
          nlinarith [cutoff_nonneg A B₀ u, cutoff_le_one A B₀ u]
      have hint2 : Integrable (fun u => cutoff A B₀ u * des.W u) (μ j) :=
        integrable_of_cs ((cutoff_continuous A B₀).mul des.W_cont) (HasCompactSupport.mul_cutoff A B₀)
      have hdiff : |∫ u, (cutoff A B₀ u * des.U j u - cutoff A B₀ u * des.W u) ∂(μ j)| ≤
          ε * (μ j K).toReal := by
        refine abs_integral_le_of_zero_outside hKc (fun x hx => ?_) (fun x hx => ?_)
        · have : cutoff A B₀ x = 0 := by
            refine cutoff_eq_zero ?_
            simp only [hKdef, mem_Icc, not_and_or, not_le] at hx
            rcases hx with h | h <;> [exact Or.inl h.le; exact Or.inr h.le]
          simp [this]
        · rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A B₀ x)]
          have hd := hj4 x hx
          rw [Real.dist_eq, abs_sub_comm] at hd
          calc cutoff A B₀ x * |des.U j x - des.W x| ≤ 1 * ε :=
                mul_le_mul (cutoff_le_one A B₀ x) hd.le (abs_nonneg _) zero_le_one
            _ = ε := one_mul ε
      have hmass : ε * (μ j K).toReal ≤ ε * M' :=
        mul_le_mul_of_nonneg_left (hj5.trans (le_max_left _ _)) hε.le
      rw [integral_sub hint1 hint2] at hdiff
      have := (abs_le.mp (hdiff.trans hmass)).1
      linarith
    have hlim := hν (fun u => cutoff A B₀ u * des.W u) ((cutoff_continuous A B₀).mul des.W_cont)
      (HasCompactSupport.mul_cutoff A B₀)
    exact le_of_tendsto hlim (hev.filter_mono hl)
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1M : 0 < 1 + M' := by positivity
  have := key (η / (1 + M')) (by positivity)
  rwa [div_mul_cancel₀ _ h1M.ne'] at this

private lemma cutoff_antitone_left {A₁ A₂ B u : ℝ} (h : A₁ ≤ A₂) :
    cutoff A₂ B u ≤ cutoff A₁ B u := by
  unfold cutoff
  exact max_le_max le_rfl (min_le_min le_rfl (min_le_min (by linarith) le_rfl))

/-- **Limit inequality (`ft:wp-limit`) and monotone cutoff convergence** for any vague limit `ν`. -/
theorem wp_integral_le {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) {B : ℝ} (hB : ∀ᶠ j in atTop, μ j (Ioi B) = 0)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hν : IsVagueLimit l μ ν) (hνB : ν (Ioi B) = 0) (des : SeqDesign μ) :
    Integrable des.W ν ∧ ∫ u, des.W u ∂ν ≤ ∫ u, des.W u ∧
      Tendsto (fun R : ℝ => ∫ u, cutoff (-R) (max B des.b) u * des.W u ∂ν) atTop
        (𝓝 (∫ u, des.W u ∂ν)) := by
  set B₀ : ℝ := max B des.b
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  have hbB₀ : des.b ≤ B₀ := le_max_right _ _
  have hνB₀ : ν (Ioi B₀) = 0 := measure_mono_null (Ioi_subset_Ioi hBB₀) hνB
  have hIoc_fin : IntegrableOn des.W (Ioc des.b B₀) ν :=
    des.W_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIoc_eq : ∀ {R : ℝ}, -R ≤ des.b →
      ∫ u in Ioc des.b B₀, cutoff (-R) B₀ u * des.W u ∂ν = ∫ u in Ioc des.b B₀, des.W u ∂ν := by
    intro R hR
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [cutoff_eq_one (hR.trans hu.1.le) hu.2, one_mul]
  have hIic_part : ∀ {R : ℝ}, -R ≤ des.b →
      ∫ u in Iic des.b, cutoff (-R) B₀ u * des.W u ∂ν =
        (∫ u, cutoff (-R) B₀ u * des.W u ∂ν) - ∫ u in Ioc des.b B₀, des.W u ∂ν := by
    intro R hR
    have hint_cs : Integrable (fun u => cutoff (-R) B₀ u * des.W u) ν :=
      integrable_of_cs ((cutoff_continuous (-R) B₀).mul des.W_cont)
        (HasCompactSupport.mul_cutoff (-R) B₀)
    have hsplit1 : ∫ u, cutoff (-R) B₀ u * des.W u ∂ν =
        ∫ u in Iic B₀, cutoff (-R) B₀ u * des.W u ∂ν := by
      have had := integral_add_compl (μ := ν) (measurableSet_Iic (a := B₀)) hint_cs
      have h0 : ∫ u in (Iic B₀)ᶜ, cutoff (-R) B₀ u * des.W u ∂ν = 0 := by
        rw [compl_Iic, Measure.restrict_eq_zero.2 hνB₀, integral_zero_measure]
      linarith
    have hU : Iic des.b ∪ Ioc des.b B₀ = Iic B₀ := Iic_union_Ioc_eq_Iic hbB₀
    have hadd := setIntegral_union (s := Iic des.b) (t := Ioc des.b B₀)
      (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hint_cs.integrableOn hint_cs.integrableOn
    rw [hU, ← hsplit1, hIoc_eq hR] at hadd
    linarith
  set N₀ : ℕ := ⌈max (-des.b) 0⌉₊
  have hN₀ : -(N₀ : ℝ) ≤ des.b := by
    have := Nat.le_ceil (max (-des.b) 0)
    linarith [le_max_left (-des.b) 0]
  let f : ℕ → ℝ → ℝ := fun n u => cutoff (-(n + N₀ : ℝ)) B₀ u * des.W u
  have hf_bound : ∀ n : ℕ,
      ∫ u in Iic des.b, f n u ∂ν ≤ (∫ u, des.W u) - ∫ u in Ioc des.b B₀, des.W u ∂ν := by
    intro n
    have hn : -(n + N₀ : ℝ) ≤ des.b := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hc := wp_cutoff_ineq hbd hB hl hν des (A := -(n + N₀ : ℝ)) (B₀ := B₀) hn hBB₀
    have heq := hIic_part (R := (n + N₀ : ℝ)) (by linarith)
    dsimp [f]
    linarith
  have hf_nn : ∀ n : ℕ, ∀ u ∈ Iic des.b, 0 ≤ f n u := fun n u hu =>
    mul_nonneg (cutoff_nonneg _ _ u) (des.W_nonneg_left hu)
  have hf_mono : ∀ u ∈ Iic des.b, Monotone fun n => ENNReal.ofReal (f n u) := fun u hu n m hnm =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (cutoff_antitone_left (by
        have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
        linarith))
      (des.W_nonneg_left hu))
  have hf_lim : ∀ u ∈ Iic des.b,
      Tendsto (fun n => ENNReal.ofReal (f n u)) atTop (𝓝 (ENNReal.ofReal (des.W u))) := by
    intro u hu
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (-u)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N₁, fun n hn => ?_⟩)
    have hu_ge : -(n + N₀ : ℝ) ≤ u := by
      have : (-u : ℝ) < N₁ := hN₁
      have : (N₁ : ℝ) ≤ n := Nat.cast_le.mpr hn
      have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
      linarith
    dsimp [f]
    rw [cutoff_eq_one hu_ge (hu.trans hbB₀), one_mul]
  have hlin := lintegral_tendsto_of_tendsto_of_monotone
    (μ := ν.restrict (Iic des.b))
    (f := fun n u => ENNReal.ofReal (f n u)) (F := fun u => ENNReal.ofReal (des.W u))
    (fun n => ((cutoff_continuous _ _).mul des.W_cont).measurable.ennreal_ofReal.aemeasurable)
    (ae_restrict_of_forall_mem measurableSet_Iic fun u hu => hf_mono u hu)
    (ae_restrict_of_forall_mem measurableSet_Iic fun u hu => hf_lim u hu)
  set C_cap : ℝ := (∫ u, des.W u) - ∫ u in Ioc des.b B₀, des.W u ∂ν
  have hC_nn : 0 ≤ C_cap := by
    have h0 := hf_bound 0
    have h0_nn : 0 ≤ ∫ u in Iic des.b, f 0 u ∂ν :=
      setIntegral_nonneg measurableSet_Iic fun u hu => hf_nn 0 u hu
    linarith
  have hlin_le : ∀ n : ℕ, ∫⁻ u in Iic des.b, ENNReal.ofReal (f n u) ∂ν ≤ ENNReal.ofReal C_cap := by
    intro n
    have hintn : IntegrableOn (f n) (Iic des.b) ν :=
      (integrable_of_cs ((cutoff_continuous _ _).mul des.W_cont)
        (HasCompactSupport.mul_cutoff _ _)).integrableOn
    rw [← ofReal_integral_eq_lintegral_ofReal hintn (ae_restrict_of_forall_mem measurableSet_Iic (hf_nn n))]
    exact ENNReal.ofReal_le_ofReal (hf_bound n)
  have hW_lint : ∫⁻ u in Iic des.b, ENNReal.ofReal (des.W u) ∂ν ≤ ENNReal.ofReal C_cap :=
    le_of_tendsto hlin (Eventually.of_forall hlin_le)
  have hIic_int : IntegrableOn des.W (Iic des.b) ν := by
    refine ⟨des.W_cont.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hnorm : ∫⁻ u in Iic des.b, ‖des.W u‖ₑ ∂ν =
        ∫⁻ u in Iic des.b, ENNReal.ofReal (des.W u) ∂ν := by
      refine setLIntegral_congr_fun measurableSet_Iic fun u hu => ?_
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (des.W_nonneg_left hu)]
    rw [hnorm]
    exact hW_lint.trans_lt ENNReal.ofReal_lt_top
  have hW_int : Integrable des.W ν := by
    have hIicB₀ : IntegrableOn des.W (Iic B₀) ν := by
      rw [← Iic_union_Ioc_eq_Iic hbB₀]
      exact hIic_int.union hIoc_fin
    have hres : ν = ν.restrict (Iic B₀) := (Measure.restrict_eq_self_of_ae_mem (ae_le_of_supp hνB₀)).symm
    exact hres ▸ hIicB₀
  have hIic_le : ∫ u in Iic des.b, des.W u ∂ν ≤ C_cap := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIic_int
      (ae_restrict_of_forall_mem measurableSet_Iic fun _ hu => des.W_nonneg_left hu)] at hW_lint
    exact (ENNReal.ofReal_le_ofReal_iff hC_nn).1 hW_lint
  have htot_eq : ∫ u, des.W u ∂ν =
      (∫ u in Iic des.b, des.W u ∂ν) + ∫ u in Ioc des.b B₀, des.W u ∂ν := by
    have hsub := setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hIic_int hIoc_fin
    rw [Iic_union_Ioc_eq_Iic hbB₀] at hsub
    have h2 : ∫ u, des.W u ∂ν = ∫ u in Iic B₀, des.W u ∂ν := by
      have had := integral_add_compl (μ := ν) (measurableSet_Iic (a := B₀)) hW_int
      have h0 : ∫ u in (Iic B₀)ᶜ, des.W u ∂ν = 0 := by
        rw [compl_Iic, Measure.restrict_eq_zero.2 hνB₀, integral_zero_measure]
      linarith
    rw [h2, hsub]
  have hle_tot : ∫ u, des.W u ∂ν ≤ ∫ u, des.W u := by
    dsimp [C_cap] at hIic_le
    linarith
  have htend : Tendsto (fun R : ℝ => ∫ u, cutoff (-R) B₀ u * des.W u ∂ν) atTop (𝓝 (∫ u, des.W u ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := fun u => |des.W u|) ?_ ?_
      hW_int.abs ?_
    · exact Eventually.of_forall fun R =>
        ((cutoff_continuous (-R) B₀).mul des.W_cont).aestronglyMeasurable
    · exact Eventually.of_forall fun R => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ u)]
        exact mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one _ _ u)
    · filter_upwards [ae_le_of_supp hνB₀] with u huB₀
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨-u, fun R hR => ?_⟩)
      dsimp only
      rw [cutoff_eq_one (by linarith) huB₀, one_mul]
  exact ⟨hW_int, hle_tot, htend⟩

/-- **No escape of positive pairing mass at equality in Lemma WP (`ft:WP`)**:
along `l` with vague limit `ν` satisfying `∫ W dν = ∫ W du`, `limsup_{j ∈ l} ∫_{u < -R} U_j dμ_j → 0`
as `R → ∞`. -/
theorem wp_no_escape {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) {B : ℝ} (hB : ∀ᶠ j in atTop, μ j (Ioi B) = 0)
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hν : IsVagueLimit l μ ν) (hνB : ν (Ioi B) = 0) (des : SeqDesign μ)
    (heq : ∫ u, des.W u ∂ν = ∫ u, des.W u) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in l,
      ∫ u in Iio (-R), des.U j u ∂(μ j) ≤ ε := by
  obtain ⟨_, _, htend⟩ := wp_integral_le hbd hB hl hν hνB des
  set B₀ : ℝ := max B des.b
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  have hev_cut : ∀ᶠ R : ℝ in atTop,
      (∫ u, des.W u ∂ν) - ε / 3 < ∫ u, cutoff (-R) B₀ u * des.W u ∂ν :=
    htend.eventually (lt_mem_nhds (by linarith))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hev_cut
  refine ⟨max (R₁ + 1) (-des.b + 2), fun R hR => ?_⟩
  set A : ℝ := -R + 1
  have hA_b : A ≤ des.b := by linarith [le_max_right (R₁ + 1) (-des.b + 2)]
  have hcut_lim : (∫ u, des.W u ∂ν) - ε / 3 < ∫ u, cutoff A B₀ u * des.W u ∂ν := by
    have hR1 : R₁ ≤ R - 1 := by linarith [le_max_left (R₁ + 1) (-des.b + 2)]
    simpa [A, show -(R - 1) = -R + 1 by ring] using hR₁ (R - 1) hR1
  set K : Set ℝ := Icc (A - 1) (B₀ + 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hbd K hKc
  set M' : ℝ := max M 0
  set δ : ℝ := ε / (3 * (M' + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 des.window_limit) K hKc
  have hev_unif : ∀ᶠ j in atTop, ∀ x ∈ K, dist (des.W x) (des.U j x) < δ :=
    Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0
  have hev_vague := (hν (fun u => cutoff A B₀ u * des.W u) ((cutoff_continuous A B₀).mul des.W_cont)
    (HasCompactSupport.mul_cutoff A B₀)).eventually (lt_mem_nhds (by linarith :
      (∫ u, des.W u ∂ν) - ε / 3 < ∫ u, cutoff A B₀ u * des.W u ∂ν))
  have hev_all := hev_vague.and ((hB.and (des.U_int_mu.and (des.pairing.and
    (des.nonneg_left.and ((des.limsup_le (ε / 3) (by positivity)).and (hev_unif.and hM)))))).filter_mono hl)
  refine hev_all.mono fun j hj => ?_
  rcases hj with ⟨hj_vague, hjB, hj_int_mu, hj_pair, hj_nn, hj_lim, hj_unif, hjM⟩
  have hint_cut : Integrable (fun u => cutoff A B₀ u * des.U j u) (μ j) := by
    refine hj_int_mu.bdd_mul (c := 1) (cutoff_continuous A B₀).aestronglyMeasurable ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B₀ u)]; exact cutoff_le_one A B₀ u
  have hind : Integrable ((Iio (-R)).indicator (des.U j)) (μ j) :=
    hj_int_mu.indicator measurableSet_Iio
  have hsum_le : (∫ u in Iio (-R), des.U j u ∂(μ j)) + ∫ u, cutoff A B₀ u * des.U j u ∂(μ j) ≤
      ∫ u, des.U j u ∂(μ j) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_add hind hint_cut]
    refine integral_mono_ae (hind.add hint_cut) hj_int_mu ?_
    filter_upwards [ae_le_of_supp hjB] with u huB
    by_cases h1 : u < -R
    · have hχ0 : cutoff A B₀ u = 0 := cutoff_eq_zero (Or.inl (by dsimp [A]; linarith))
      simp [Set.indicator_of_mem (show u ∈ Iio (-R) from h1), hχ0]
    · push Not at h1
      have hnot : u ∉ Iio (-R) := not_lt.mpr h1
      simp only [Set.indicator_of_notMem hnot, zero_add]
      by_cases h2 : u < A
      · have := hj_nn u (h2.le.trans hA_b)
        nlinarith [cutoff_nonneg A B₀ u, cutoff_le_one A B₀ u]
      · push Not at h2
        rw [cutoff_eq_one h2 (huB.trans hBB₀), one_mul]
  have hintW : Integrable (fun u => cutoff A B₀ u * des.W u) (μ j) :=
    integrable_of_cs ((cutoff_continuous A B₀).mul des.W_cont) (HasCompactSupport.mul_cutoff A B₀)
  have hdiff : |∫ u, (cutoff A B₀ u * des.W u - cutoff A B₀ u * des.U j u) ∂(μ j)| ≤
      δ * (μ j K).toReal := by
    refine abs_integral_le_of_zero_outside hKc (fun x hx => ?_) (fun x hx => ?_)
    · have : cutoff A B₀ x = 0 := by
        refine cutoff_eq_zero ?_
        simp only [hKdef, mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h <;> [exact Or.inl h.le; exact Or.inr h.le]
      simp [this]
    · rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A B₀ x)]
      have hd := hj_unif x hx
      rw [Real.dist_eq] at hd
      calc cutoff A B₀ x * |des.W x - des.U j x| ≤ 1 * δ :=
            mul_le_mul (cutoff_le_one A B₀ x) hd.le (abs_nonneg _) zero_le_one
        _ = δ := one_mul δ
  rw [integral_sub hintW hint_cut] at hdiff
  have hM'1 : (M' + 1 : ℝ) ≠ 0 := by positivity
  have hδM : δ * (μ j K).toReal ≤ ε / 3 := by
    calc δ * (μ j K).toReal ≤ δ * M' :=
          mul_le_mul_of_nonneg_left (hjM.trans (le_max_left _ _)) hδ0.le
      _ ≤ δ * (M' + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
      _ = ε / 3 := by dsimp [δ]; field_simp
  have := (abs_le.mp (hdiff.trans hδM)).2
  linarith

end FormalResearch.ModularBootstrap.FoldTip

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.wp_locallyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.wp_locallyBounded

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.wp_vagueLimit_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.wp_vagueLimit_carried

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.wp_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.wp_integral_le

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.wp_no_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.wp_no_escape
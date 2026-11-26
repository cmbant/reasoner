module

public import FormalResearch.ModularBootstrap.Duality.Primal.PositiveThreshold
public import FormalResearch.ModularBootstrap.Duality.ReserveSeparation

/-!
# Primal attainment and discreteness (Theorem E', `ds:primal`, `dual_spectrum.tex`)

For a compact `F ⊂ (0, ∞)` and `X_τ = F ∪ [τ, ∞)`, at a charge where `FixedChargeStrip` holds
(every `c̃ ≥ c₀(w, Q)`, `fixedChargeStrip_of_large`):

* `primal_extremal_of_sequence`: every normalised strictly feasible minimising sequence has a
  subsequence converging locally uniformly and in `M` to a weak extremal `g_*` (`M[g_*] = 1`,
  `g_{*,vac} = 0`, `g_* ≥ 0` on `X_{T_F}`) whose zero set is locally finite (strip holomorphy);
* `theorem_primal`: (a) existence of `g_*`; (b) every crossing measure on `X_{T_F}` is carried by
  `{g_* = 0}`; (c) every such measure is carried by a locally finite set and has `ν({T_F}) > 0`;
  (d) if `g_* > 0` on a compact `E ⊂ (0, ∞)` then `T_{F ∪ E} = T_F` and every crossing measure on
  `F ∪ E ∪ [T_F, ∞)` gives `E` zero mass.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing WeightAxioms FormalResearch.ModularBootstrap.Duality

variable {prob : FixedWeightProblem} {cTilde : ℝ}

/-- **Weak extremal from a normalised minimising sequence** (`ds:primal`(a)). -/
theorem primal_extremal_of_sequence (S : FixedChargeStrip prob cTilde) {F : Set ℝ}
    (hFc : IsCompact F) (hF : F ⊆ Ioi 0) {τ : ℕ → ℝ} {g : ℕ → ℝ → ℝ}
    (hfeas : ∀ k, prob.IsFeasibleOn (cTilde / 12) (F ∪ Ici (τ k)) (g k))
    (hτ : Tendsto τ atTop (𝓝 (constrainedThreshold prob cTilde F)))
    (hM : ∀ k, prob.cardyNorm (cTilde / 12) (g k) = 1) :
    ∃ (φ : ℕ → ℕ) (gs : ℝ → ℝ), StrictMono φ ∧ TestClass prob (cTilde / 12) gs ∧
      prob.cardyNorm (cTilde / 12) gs = 1 ∧ prob.gVac (cTilde / 12) gs = 0 ∧
      (∀ t ∈ F ∪ Ici (constrainedThreshold prob cTilde F), 0 ≤ gs t) ∧
      (∀ R : ℝ, TendstoUniformlyOn (fun k => g (φ k)) gs atTop (Icc 0 R)) ∧
      Tendsto (fun k => ∫ t in Ioi (0 : ℝ), |g (φ k) t - gs t| * prob.cardyV (cTilde / 12) t)
        atTop (𝓝 0) ∧
      (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧ (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧
      (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
        ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ)) := by
  classical
  set a : ℝ := cTilde / 12 with ha_def
  set TF : ℝ := constrainedThreshold prob cTilde F with hTF
  have hTV := T_V_pos_of_strip S
  obtain ⟨⟨hle, hne⟩, ⟨⟨hTFpos, meas, hν⟩, -⟩, -, -⟩ :=
    theorem_E_b_compact prob S.hc_pos S.hc hFc hF hTV
  have hTF0 : 0 < TF := lt_of_lt_of_le hTV hle
  have hsh : prob.totalShift ≤ a := by linarith [S.hc]
  have ha0 : 0 < a := by linarith [S.hc_pos]
  -- discard finitely many terms
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hτ.eventually (gt_mem_nhds (show TF < TF + 1 by linarith)))
  set g' : ℕ → ℝ → ℝ := fun k => g (k + N) with hg'
  have hg'f : ∀ k, prob.IsFeasibleOn a (F ∪ Ici (τ (k + N))) (g' k) := fun k => hfeas (k + N)
  have hτ' : ∀ k, τ (k + N) ≤ TF + 1 := fun k => (hN (k + N) (by omega)).le
  have hneg : ∀ k, ∀ t ≥ TF + 1, 0 ≤ g' k t := fun k t ht =>
    (hg'f k).2.2 t (Or.inr (le_trans (hτ' k) ht))
  have hv : ∀ k, ∫ t in Ioi (0 : ℝ), g' k t * prob.cardyV a t ≤ 0 := fun k => by
    have h1 := (hg'f k).2.1
    have : prob.gVac a (g' k) = -2 * π * ∫ t in Ioi (0 : ℝ), g' k t * prob.cardyV a t := rfl
    nlinarith [Real.pi_pos]
  obtain ⟨φ, gs, hφ, htc, hnn, hunif, hMle, hvac0, hne0, hzero, hG, himp⟩ :=
    exists_primal_limit S (fun k => (hg'f k).1) (fun k => hM (k + N)) hv (R₀ := TF + 1)
      (by linarith) hneg
  have hgs_cont : ContinuousOn gs (Ici 0) := htc.cont
  have hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k => g' (φ k) t) atTop (𝓝 (gs t)) := fun t ht =>
    (hunif t).tendsto_at ⟨ht, le_rfl⟩
  -- `g_* ≥ 0` on `X_{T_F}`
  have hφN : Tendsto (fun k => φ k + N) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (φ k) N) hφ.tendsto_atTop
  have hτφ : Tendsto (fun k => τ (φ k + N)) atTop (𝓝 TF) := hτ.comp hφN
  have hnn_F : ∀ t ∈ F, 0 ≤ gs t := fun t ht =>
    ge_of_tendsto (hpt t (le_of_lt (hF ht)))
      (Eventually.of_forall fun k => (hg'f (φ k)).2.2 t (Or.inl ht))
  have hnn_gt : ∀ t, TF < t → 0 ≤ gs t := fun t ht =>
    ge_of_tendsto (hpt t (by linarith))
      ((hτφ.eventually (gt_mem_nhds ht)).mono fun k hk =>
        (hg'f (φ k)).2.2 t (Or.inr (le_of_lt hk)))
  have hnn_TF : 0 ≤ gs TF := by
    have hcont : ContinuousAt gs TF := by
      refine (hgs_cont.continuousAt (Ici_mem_nhds hTF0))
    exact ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds : Tendsto gs (𝓝[>] TF) _)
      (eventually_nhdsWithin_of_forall fun t ht => hnn_gt t ht)
  have hnn_X : ∀ t ∈ F ∪ Ici TF, 0 ≤ gs t := fun t ht => by
    rcases ht with ht | ht
    · exact hnn_F t ht
    · rcases (mem_Ici.1 ht).eq_or_lt with h | h
      · rw [← h]; exact hnn_TF
      · exact hnn_gt t h
  -- `g_{*,vac} ≤ 0` by pairing with a crossing measure on `X_{T_F}`
  have hvac_le : prob.gVac a gs ≤ 0 := by
    obtain ⟨hint, hle1⟩ := lemma_fwX_one_sided_unconditional prob hsh ha0 meas htc (T := TF)
      (fun t ht => hnn_X t (Or.inr ht))
    have hae : ∀ᵐ t ∂meas.ν, 0 ≤ gs t := by
      have : ∀ᵐ y ∂meas.ν, y ∉ (F ∪ Ici TF)ᶜ := measure_eq_zero_iff_ae_notMem.1 hν
      filter_upwards [this] with y hy using hnn_X y (Set.notMem_compl_iff.1 hy)
    rw [Duality.restrict_Ici_eq_self meas] at hle1
    have h0 : 0 ≤ ∫ t, gs t ∂meas.ν := integral_nonneg_of_ae hae
    linarith
  have hvac_eq : prob.gVac a gs = 0 := le_antisymm hvac_le hvac0
  obtain ⟨hM1, hconv⟩ := himp hvac_le
  refine ⟨fun k => φ k + N, gs, ?_, htc, hM1, hvac_eq, hnn_X, ?_, ?_, hzero, hne0, hG⟩
  · exact hφ.add_const N
  · exact hunif
  · exact hconv

/-- Cardy norm scales: `M[c g] = c M[g]` for `c ≥ 0`. -/
lemma cardyNorm_smul_of_nonneg {a c : ℝ} (hc : 0 ≤ c) (g : ℝ → ℝ) :
    prob.cardyNorm a (fun t => c * g t) = c * prob.cardyNorm a g := by
  unfold FixedWeightProblem.cardyNorm
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [abs_mul, abs_of_nonneg hc]; ring

/-- A normalised strictly feasible minimising sequence exists. -/
theorem exists_normalised_sequence (S : FixedChargeStrip prob cTilde) {F : Set ℝ}
    (hne : (constrainedGaps prob cTilde F).Nonempty) :
    ∃ (τ : ℕ → ℝ) (g : ℕ → ℝ → ℝ),
      (∀ k, prob.IsFeasibleOn (cTilde / 12) (F ∪ Ici (τ k)) (g k)) ∧
      Tendsto τ atTop (𝓝 (constrainedThreshold prob cTilde F)) ∧
      ∀ k, prob.cardyNorm (cTilde / 12) (g k) = 1 := by
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sInf hne ⟨0, fun t ht => ht.1.le⟩
  choose g0 hg0 using fun k => (hmem k).2
  refine ⟨u, fun k => fun t => (prob.cardyNorm (cTilde / 12) (g0 k))⁻¹ * g0 k t, fun k => ?_, hu,
    fun k => ?_⟩
  · obtain ⟨htc, hvac, hnn⟩ := hg0 k
    have hM := cardyNorm_pos_of_vac_pos S.hc htc hvac
    refine ⟨htc.smul _, ?_, fun t ht => mul_nonneg (inv_nonneg.2 hM.le) (hnn t ht)⟩
    rw [prob.gVac_smul _ htc]; exact mul_pos (inv_pos.2 hM) hvac
  · have hM := cardyNorm_pos_of_vac_pos S.hc (hg0 k).1 (hg0 k).2.1
    rw [cardyNorm_smul_of_nonneg (inv_nonneg.2 hM.le), inv_mul_cancel₀ hM.ne']

/-- A crossing measure carried by a set on which `g_* ≥ 0` is carried by the zero set of `g_*`. -/
lemma crossing_ae_zero {gs : ℝ → ℝ} (htc : TestClass prob (cTilde / 12) gs)
    (hvac : prob.gVac (cTilde / 12) gs = 0) (hsh : prob.totalShift ≤ cTilde / 12)
    (ha0 : 0 < cTilde / 12) {T : ℝ} (hT : ∀ t ≥ T, 0 ≤ gs t)
    (meas : AdmissibleCrossingMeasure prob (cTilde / 12)) {Y : Set ℝ} (hν : meas.ν Yᶜ = 0)
    (hY : ∀ t ∈ Y, 0 ≤ gs t) : ∀ᵐ t ∂meas.ν, t ∈ Y ∧ gs t = 0 := by
  obtain ⟨hint, hle⟩ := lemma_fwX_one_sided_unconditional prob hsh ha0 meas htc (T := T) hT
  rw [IntegrableOn, Duality.restrict_Ici_eq_self meas] at hint
  rw [Duality.restrict_Ici_eq_self meas] at hle
  have hmem : ∀ᵐ t ∂meas.ν, t ∈ Y := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Yᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using Set.notMem_compl_iff.1 hy
  have hae : 0 ≤ᵐ[meas.ν] gs := by
    filter_upwards [hmem] with t ht using hY t ht
  have h0 : ∫ t, gs t ∂meas.ν = 0 :=
    le_antisymm (by linarith) (integral_nonneg_of_ae hae)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hae hint).1 h0
  filter_upwards [hmem, hz] with t h1 h2 using ⟨h1, h2⟩

/-- **Theorem E'** (`ds:primal`) at a charge with `FixedChargeStrip`, for compact `F ⊂ (0, ∞)`:
`0 < T_V ≤ T_F < ∞`, and there is a weak extremal `g_*` such that (a) `g_* ∈ Ā_w`, `M[g_*] = 1`,
`g_{*,vac} = 0`, `g_* ≥ 0` on `X_{T_F}`, `g_*` is the restriction of a function holomorphic in the
strip coordinate and has locally finite zero set; (b) every crossing measure on `X_{T_F}` is carried
by `{g_* = 0}`; (c) it is carried by a locally finite set and `ν({T_F}) > 0`; (d) if `g_* > 0` on a
compact `E ⊂ (0, ∞)` then `T_{F ∪ E} = T_F` and every crossing measure on `F ∪ E ∪ [T_F, ∞)` gives
`E` zero mass. -/
theorem theorem_primal (S : FixedChargeStrip prob cTilde) {F : Set ℝ} (hFc : IsCompact F)
    (hF : F ⊆ Ioi 0) :
    (0 < prob.T_V cTilde ∧ prob.T_V cTilde ≤ constrainedThreshold prob cTilde F ∧
      (constrainedGaps prob cTilde F).Nonempty) ∧
    ∃ gs : ℝ → ℝ,
      (TestClass prob (cTilde / 12) gs ∧ prob.cardyNorm (cTilde / 12) gs = 1 ∧
        prob.gVac (cTilde / 12) gs = 0 ∧
        (∀ t ∈ F ∪ Ici (constrainedThreshold prob cTilde F), 0 ≤ gs t) ∧
        (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧ (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧
        (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
          ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ))) ∧
      (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
          ∀ᵐ t ∂meas.ν, t ∈ F ∪ Ici (constrainedThreshold prob cTilde F) ∧ gs t = 0) ∧
      (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
          (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
          0 < meas.ν {constrainedThreshold prob cTilde F}) ∧
      (∀ E : Set ℝ, IsCompact E → E ⊆ Ioi 0 → (∀ t ∈ E, 0 < gs t) →
        constrainedThreshold prob cTilde (F ∪ E) = constrainedThreshold prob cTilde F ∧
        ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
          meas.ν ((F ∪ E) ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 → meas.ν E = 0) := by
  classical
  set a : ℝ := cTilde / 12 with ha_def
  set TF : ℝ := constrainedThreshold prob cTilde F with hTF
  have hTV := T_V_pos_of_strip S
  have hE := theorem_E_b_compact prob S.hc_pos S.hc hFc hF hTV
  obtain ⟨⟨hle, hne⟩, -, -, -⟩ := hE
  have hTF0 : 0 < TF := lt_of_lt_of_le hTV hle
  have hsh : prob.totalShift ≤ a := by linarith [S.hc]
  have ha0 : 0 < a := by linarith [S.hc_pos]
  obtain ⟨τ, g, hfeas, hτ, hM⟩ := exists_normalised_sequence S hne
  obtain ⟨φ, gs, -, htc, hM1, hvac, hnn, -, -, hzero, hne0, hG⟩ :=
    primal_extremal_of_sequence S hFc hF hfeas hτ hM
  refine ⟨⟨hTV, hle, hne⟩, gs, ⟨htc, hM1, hvac, hnn, hzero, hne0, hG⟩, ?_, ?_, ?_⟩
  · intro meas hν
    exact crossing_ae_zero htc hvac hsh ha0 (T := TF) (fun t ht => hnn t (Or.inr ht)) meas hν hnn
  · intro meas hν
    have hae := crossing_ae_zero htc hvac hsh ha0 (T := TF) (fun t ht => hnn t (Or.inr ht)) meas hν hnn
    have hXpos : F ∪ Ici TF ⊆ Ici 0 := union_subset (fun t ht => (hF ht).le) (fun t ht =>
      le_trans hTF0.le ht)
    refine ⟨⟨{t | 0 ≤ t ∧ gs t = 0}, fun R => ?_, ?_⟩, ?_⟩
    · exact (hzero R).subset fun t ht => ⟨ht.2, ht.1.2⟩
    · refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hae] with t ht
      exact Set.notMem_compl_iff.2 ⟨hXpos ht.1, ht.2⟩
    · -- a positive atom at `T_F`
      by_contra h0
      have h0' : meas.ν {TF} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
      set Zf : Set ℝ := {t | 0 ≤ t ∧ gs t = 0} ∩ Icc 0 (TF + 1) ∩ Ioi TF with hZf
      have hZfin : Zf.Finite := (hzero (TF + 1)).subset fun t ht => ⟨ht.1.2, ht.1.1.2⟩
      have hTFn : TF ∉ Zf := fun h => lt_irrefl _ (mem_Ioi.1 h.2)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hZfin.isClosed.isOpen_compl TF hTFn
      set ε' : ℝ := min ε 1 with hε'
      have hε'pos : 0 < ε' := lt_min hε one_pos
      have hbad : meas.ν {t | ¬ (t ∈ F ∪ Ici TF ∧ gs t = 0)} = 0 := ae_iff.1 hae
      have hIoo : meas.ν (Ioo TF (TF + ε')) = 0 := by
        refine measure_mono_null (fun t ht => ?_) hbad
        rintro ⟨-, hz⟩
        have ht1 : TF < t := ht.1
        have ht2 : t < TF + ε' := ht.2
        have hmemZ : t ∈ Zf := ⟨⟨⟨by linarith, hz⟩, by linarith, by
          have := min_le_right ε 1; linarith⟩, ht1⟩
        have : t ∈ Metric.ball TF ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          have := min_le_left ε 1
          constructor <;> linarith
        exact hball this hmemZ
      have hν2 : meas.ν (F ∪ Ici (TF + ε'))ᶜ = 0 := by
        refine measure_mono_null (fun t ht => ?_)
          (measure_union_null (measure_union_null hν h0') hIoo)
        have hnF : t ∉ F := fun h => ht (Or.inl h)
        have hlt : t < TF + ε' := lt_of_not_ge fun h => ht (Or.inr h)
        rcases lt_trichotomy t TF with h | h | h
        · refine Or.inl (Or.inl fun hh => ?_)
          rcases hh with hh | hh
          · exact hnF hh
          · exact absurd (mem_Ici.1 hh) (not_le.2 h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨h, hlt⟩
      have := le_constrainedThreshold_of_crossingMeasure prob S.hc_pos S.hc hne meas hν2
      linarith
  · intro E hEc hE hEpos
    have hFEc : IsCompact (F ∪ E) := hFc.union hEc
    have hFE : F ∪ E ⊆ Ioi 0 := union_subset hF hE
    obtain ⟨⟨hle2, hne2⟩, ⟨⟨hT'pos, meas', hν'⟩, -⟩, -, -⟩ :=
      theorem_E_b_compact prob S.hc_pos S.hc hFEc hFE hTV
    set T' : ℝ := constrainedThreshold prob cTilde (F ∪ E) with hT'
    have hgap_sub : constrainedGaps prob cTilde (F ∪ E) ⊆ constrainedGaps prob cTilde F :=
      fun τ hτ => ⟨hτ.1, by
        obtain ⟨g, hg1, hg2, hg3⟩ := hτ.2
        exact ⟨g, hg1, hg2, fun t ht => hg3 t (by
          rcases ht with ht | ht
          · exact Or.inl (Or.inl ht)
          · exact Or.inr ht)⟩⟩
    have hTFT' : TF ≤ T' :=
      csInf_le_csInf ⟨0, fun t ht => ht.1.le⟩ hne2 hgap_sub
    have hnnE : ∀ t ∈ (F ∪ E) ∪ Ici TF, 0 ≤ gs t := fun t ht => by
      rcases ht with (ht | ht) | ht
      · exact hnn t (Or.inl ht)
      · exact (hEpos t ht).le
      · exact hnn t (Or.inr ht)
    have hEnull : ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν ((F ∪ E) ∪ Ici TF)ᶜ = 0 → meas.ν E = 0 := fun meas hν => by
      have hae := crossing_ae_zero htc hvac hsh ha0 (T := TF) (fun t ht => hnn t (Or.inr ht)) meas hν
        hnnE
      refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
      rintro ⟨-, hz⟩
      exact (hEpos t ht).ne' hz
    refine ⟨le_antisymm ?_ hTFT', hEnull⟩
    -- the attaining measure for `F ∪ E` at `T'` does not charge `E`
    have hnnE' : ∀ t ∈ (F ∪ E) ∪ Ici T', 0 ≤ gs t := fun t ht => by
      rcases ht with (ht | ht) | ht
      · exact hnn t (Or.inl ht)
      · exact (hEpos t ht).le
      · exact hnn t (Or.inr (le_trans hTFT' ht))
    have hae := crossing_ae_zero htc hvac hsh ha0 (T := TF) (fun t ht => hnn t (Or.inr ht)) meas' hν'
      hnnE'
    have hE0 : meas'.ν E = 0 := by
      refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
      rintro ⟨-, hz⟩
      exact (hEpos t ht).ne' hz
    have hν'' : meas'.ν (F ∪ Ici T')ᶜ = 0 := by
      refine measure_mono_null (fun t ht => ?_) (measure_union_null hν' hE0)
      by_cases hE' : t ∈ E
      · exact Or.inr hE'
      · refine Or.inl fun hh => ht ?_
        rcases hh with (hh | hh) | hh
        · exact Or.inl hh
        · exact absurd hh hE'
        · exact Or.inr hh
    exact le_constrainedThreshold_of_crossingMeasure prob S.hc_pos S.hc hne meas' hν''

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.theorem_primal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.theorem_primal

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.primal_extremal_of_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.primal_extremal_of_sequence

end FormalResearch.ModularBootstrap.FixedWeight

module

public import FormalResearch.ModularBootstrap.Spin.SpinD3V
public import FormalResearch.ModularBootstrap.Spin.SpinDTensorCayley
public import FormalResearch.ModularBootstrap.Crossing.MehlerOddClosure

/-!
# Proposition SD-W (`sd:W`) and Theorem SD (`sd:SD`)

Proves unconditionally for all `a ≥ 2`:
- `spinDW : SpinDW` (`spinning_dual.tex`, Proposition SD-W): weak duality and complementary
  slackness for the full continuous-spin test class `\overline{\mathcal A}_{\rm spin}` on the
  quadrant, using `spinDV` (`SpinD3V.lean`) and `Crossing` Mehler / `L²`-closure machinery
  (no `SpinS24` hypothesis needed).
- `spinDSD : SpinDSD` (`spinning_dual.tex`, Theorem SD): full strong duality, attainment, scalar
  comparison, and quadrant class-infimum equality, assembled via `spinDSD_of_spinDW spinDW`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

/-! ### Section 1: 1D & 2D even Gaussian `L²` density and thermal-difference approximation -/

private noncomputable def wE2ToProd : RadialSpace 1 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma wVolume_preserving_e2ToProd : MeasurePreserving wE2ToProd volume volume :=
  (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp (PiLp.volume_preserving_ofLp (Fin 2))

private lemma wE2ToProd_apply (x : RadialSpace 1) : wE2ToProd x = (x 0, x 1) := rfl
private lemma wE2ToProd_symm_apply_zero (p : ℝ × ℝ) : (wE2ToProd.symm p) 0 = p.1 := rfl
private lemma wE2ToProd_symm_apply_one (p : ℝ × ℝ) : (wE2ToProd.symm p) 1 = p.2 := rfl

private lemma wE2ToProd_continuous : Continuous wE2ToProd :=
  ((continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).prodMk
    ((continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous)

/-- Map `x ↦ exp(-π x²)` into `[0, 1]`. -/
private noncomputable def expSqClamp (x : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-π * x ^ 2), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])⟩

private lemma continuous_expSqClamp : Continuous expSqClamp :=
  Continuous.subtype_mk (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))) _

/-- 1D Weierstrass orthogonality: if `f ∈ L¹(ℝ, ℂ)` is even a.e. and orthogonal to
`exp(-π k x²)` for all `k : ℕ`, then `f = 0` a.e. -/
private lemma ae_eq_zero_of_forall_exp_sq_1D {f : ℝ → ℂ} (hf_int : Integrable f)
    (hf_even : ∀ᵐ x : ℝ, f (-x) = f x)
    (hf_orth : ∀ k : ℕ, ∫ x : ℝ, (Real.exp (-π * x ^ 2)) ^ k • f x = 0) :
    f =ᵐ[volume] 0 := by
  -- Step 1: `∫ ψ(exp(-π x²)) • f x = 0` for every continuous `ψ ∈ C([0, 1], ℝ)`
  have hcont_orth : ∀ ψ : C(Icc (0 : ℝ) 1, ℝ), ∫ x : ℝ, ψ (expSqClamp x) • f x = 0 := by
    intro ψ
    have hpoly : ∀ P : Polynomial ℝ,
        ∫ x : ℝ, (P.eval (expSqClamp x : ℝ)) • f x = 0 := by
      intro P
      refine Polynomial.induction_on' P ?_ ?_
      · intro p q hp hq
        have hpi : ∀ Q : Polynomial ℝ, Integrable (fun x : ℝ => (Q.eval (expSqClamp x : ℝ)) • f x) := by
          intro Q
          obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
            (Q.continuous.continuousOn (s := Icc (0 : ℝ) 1))
          refine (hf_int.norm.const_mul (max M 0)).mono'
            ((Q.continuous.comp (continuous_subtype_val.comp continuous_expSqClamp)).aestronglyMeasurable.smul
              hf_int.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          have hbx : |Q.eval (expSqClamp x : ℝ)| ≤ max M 0 :=
            (hM _ (expSqClamp x).2).trans (le_max_left _ _)
          exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
        have hadd : (fun x : ℝ => ((p + q).eval (expSqClamp x : ℝ)) • f x) =
            fun x => (p.eval (expSqClamp x : ℝ)) • f x + (q.eval (expSqClamp x : ℝ)) • f x := by
          ext x; simp [Polynomial.eval_add, add_smul]
        rw [hadd, integral_add (hpi p) (hpi q), hp, hq, add_zero]
      · intro k a
        have hmon : (fun x : ℝ => ((Polynomial.monomial k a).eval (expSqClamp x : ℝ)) • f x) =
            fun x => a • ((Real.exp (-π * x ^ 2)) ^ k • f x) := by
          ext x; simp [Polynomial.eval_monomial, expSqClamp, mul_smul]
        rw [hmon, integral_smul, hf_orth k, smul_zero]
    have hnorm_le : ∀ ε > 0, ‖∫ x : ℝ, ψ (expSqClamp x) • f x‖ ≤ ε * ∫ x : ℝ, ‖f x‖ := by
      intro ε hε
      have hmem := continuousMap_mem_polynomialFunctions_closure 0 1 ψ
      obtain ⟨g, hg_mem, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
      change g ∈ (polynomialFunctions (Icc (0 : ℝ) 1) : Set _) at hg_mem
      rw [polynomialFunctions_coe] at hg_mem
      obtain ⟨P, rfl⟩ := hg_mem
      have hint_ψ : Integrable (fun x : ℝ => ψ (expSqClamp x) • f x) := by
        obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn ψ.continuous.continuousOn
        refine (hf_int.norm.const_mul (max M 0)).mono'
          ((ψ.continuous.comp continuous_expSqClamp).aestronglyMeasurable.smul
            hf_int.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        have hbx : |ψ (expSqClamp x)| ≤ max M 0 := by
          have := hM (expSqClamp x) trivial
          rw [Real.norm_eq_abs] at this
          exact this.trans (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
      have hint_P : Integrable (fun x : ℝ => (P.eval (expSqClamp x : ℝ)) • f x) := by
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
          (P.continuous.continuousOn (s := Icc (0 : ℝ) 1))
        refine (hf_int.norm.const_mul (max M 0)).mono'
          ((P.continuous.comp (continuous_subtype_val.comp continuous_expSqClamp)).aestronglyMeasurable.smul
            hf_int.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right ((hM _ (expSqClamp x).2).trans (le_max_left _ _)) (norm_nonneg _)
      have hsub_eq : (∫ x : ℝ, ψ (expSqClamp x) • f x) =
          ∫ x : ℝ, (ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)) • f x := by
        have : (fun x : ℝ => (ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)) • f x) =
            fun x => ψ (expSqClamp x) • f x - (P.eval (expSqClamp x : ℝ)) • f x := by
          ext x; rw [sub_smul]
        rw [this, integral_sub hint_ψ hint_P, hpoly P, sub_zero]
      rw [hsub_eq]
      have hpt : ∀ x : ℝ, ‖(ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)) • f x‖ ≤ ε * ‖f x‖ := by
        intro x
        rw [norm_smul, Real.norm_eq_abs]
        have hd : |ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)| < ε := by
          have h1 : dist ((Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) (expSqClamp x))
              (ψ (expSqClamp x)) ≤
              dist (Polynomial.toContinuousMapOnAlgHom (Icc (0 : ℝ) 1) P) ψ :=
            ContinuousMap.dist_apply_le_dist _
          rw [Real.dist_eq, abs_sub_comm] at h1
          exact lt_of_le_of_lt h1 (by rwa [dist_comm] at hdist)
        exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
      calc ‖∫ x : ℝ, (ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)) • f x‖
          ≤ ∫ x : ℝ, ‖(ψ (expSqClamp x) - P.eval (expSqClamp x : ℝ)) • f x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x : ℝ, ε * ‖f x‖ :=
            integral_mono
              ((hint_ψ.sub hint_P).congr (Eventually.of_forall fun x => by
                simp only [Pi.sub_apply, sub_smul]) |>.norm)
              (hf_int.norm.const_mul ε) hpt
        _ = ε * ∫ x : ℝ, ‖f x‖ := integral_const_mul _ _
    have hnorm0 : ‖∫ x : ℝ, ψ (expSqClamp x) • f x‖ ≤ 0 := by
      set J := ‖∫ x : ℝ, ψ (expSqClamp x) • f x‖
      by_contra hpos
      push Not at hpos
      set I := ∫ x : ℝ, ‖f x‖
      have hI_nn : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
      have hle := hnorm_le (J / (2 * (I + 1))) (by positivity)
      have hlt : J / (2 * (I + 1)) * I < J := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    exact norm_le_zero_iff.mp hnorm0
  -- Step 2: `∫ x in Icc a b, f x = 0` for all `0 ≤ a ≤ b`
  have hIcc_pos : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ∫ x in Icc a b, f x = 0 := by
    intro a b ha hab
    set r₁ : ℝ := Real.exp (-π * b ^ 2)
    set r₂ : ℝ := Real.exp (-π * a ^ 2)
    have hr₁₂ : r₁ ≤ r₂ := Real.exp_le_exp.mpr (by
      have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
      nlinarith [Real.pi_pos])
    let K : Set ℝ := Icc r₁ r₂
    let ψ : ℕ → C(Icc (0 : ℝ) 1, ℝ) := fun n =>
      ⟨fun s => max 0 (1 - (n : ℝ) * Metric.infDist (s : ℝ) K),
        continuous_const.max (continuous_const.sub
          (continuous_const.mul (Metric.continuous_infDist_pt K |>.comp continuous_subtype_val)))⟩
    have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => ψ n (expSqClamp x) • f x) atTop
        (𝓝 (({x : ℝ | |x| ∈ Icc a b}).indicator f x)) := by
      intro x
      have hmem : (expSqClamp x : ℝ) ∈ K ↔ |x| ∈ Icc a b := by
        simp only [K, expSqClamp, mem_Icc, r₁, r₂, Real.exp_le_exp]
        constructor
        · rintro ⟨h1, h2⟩
          have hx2_le : x ^ 2 ≤ b ^ 2 := by nlinarith [Real.pi_pos]
          have ha2_le : a ^ 2 ≤ x ^ 2 := by nlinarith [Real.pi_pos]
          rw [← sq_abs x] at hx2_le ha2_le
          exact ⟨by nlinarith [abs_nonneg x], by nlinarith [abs_nonneg x]⟩
        · rintro ⟨h1, h2⟩
          have ha2_le : a ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ ha h1 2
          have hx2_le : |x| ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h2 2
          rw [sq_abs] at ha2_le hx2_le
          exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      by_cases hx : |x| ∈ Icc a b
      · have hx' : x ∈ {x : ℝ | |x| ∈ Icc a b} := hx
        rw [Set.indicator_of_mem hx']
        have hinf0 : Metric.infDist (expSqClamp x : ℝ) K = 0 :=
          Metric.infDist_zero_of_mem (hmem.mpr hx)
        have hconst : ∀ n : ℕ, ψ n (expSqClamp x) • f x = f x := fun n => by
          simp [ψ, hinf0]
        simp_rw [hconst]; exact tendsto_const_nhds
      · have hx' : x ∉ {x : ℝ | |x| ∈ Icc a b} := hx
        rw [Set.indicator_of_notMem hx']
        have hd_pos : 0 < Metric.infDist (expSqClamp x : ℝ) K :=
          (isClosed_Icc.notMem_iff_infDist_pos ⟨r₁, le_rfl, hr₁₂⟩).mp (mt hmem.mp hx)
        refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (Metric.infDist (expSqClamp x : ℝ) K)⁻¹)
          fun n hn => ?_
        have hge1 : 1 ≤ (n : ℝ) * Metric.infDist (expSqClamp x : ℝ) K := by
          have h1 : (Metric.infDist (expSqClamp x : ℝ) K)⁻¹ ≤ n :=
            (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
          have := mul_le_mul_of_nonneg_right h1 hd_pos.le
          rwa [inv_mul_cancel₀ hd_pos.ne'] at this
        have hmax : max 0 (1 - (n : ℝ) * Metric.infDist (expSqClamp x : ℝ) K) = 0 :=
          max_eq_left (by linarith)
        simp [ψ, hmax]
    have hdom_int : Tendsto (fun n : ℕ => ∫ x : ℝ, ψ n (expSqClamp x) • f x) atTop
        (𝓝 (∫ x : ℝ, ({x : ℝ | |x| ∈ Icc a b}).indicator f x)) := by
      refine tendsto_integral_of_dominated_convergence (bound := fun x => ‖f x‖) ?_ hf_int.norm ?_
        (Eventually.of_forall hlim)
      · intro n
        exact ((ψ n).continuous.comp continuous_expSqClamp).aestronglyMeasurable.smul
          hf_int.aestronglyMeasurable
      · intro n; filter_upwards with x
        rw [norm_smul, Real.norm_eq_abs]
        have h0 : 0 ≤ ψ n (expSqClamp x) := le_max_left _ _
        have h1 : ψ n (expSqClamp x) ≤ 1 := by
          refine max_le zero_le_one ?_
          have : 0 ≤ (n : ℝ) * Metric.infDist (expSqClamp x : ℝ) K :=
            mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg
          linarith
        rw [abs_of_nonneg h0]
        exact mul_le_of_le_one_left (norm_nonneg _) h1
    have hzero : ∫ x : ℝ, ({x : ℝ | |x| ∈ Icc a b}).indicator f x = 0 := by
      have h0 : (fun n : ℕ => ∫ x : ℝ, ψ n (expSqClamp x) • f x) = fun _ => 0 :=
        funext fun n => hcont_orth (ψ n)
      rw [h0] at hdom_int
      exact tendsto_nhds_unique hdom_int tendsto_const_nhds
    -- By evenness, `∫_{|x| ∈ [a, b]} f = 2 ∫_{[a, b]} f` (modulo `{0}` of measure 0)
    have hsplit : (∫ x : ℝ, ({x : ℝ | |x| ∈ Icc a b}).indicator f x) =
        2 • ∫ x in Icc a b, f x := by
      have hmeas_abs : MeasurableSet {x : ℝ | |x| ∈ Icc a b} :=
        continuous_abs.measurable measurableSet_Icc
      rw [integral_indicator hmeas_abs]
      have hdecomp : {x : ℝ | |x| ∈ Icc a b} = Icc a b ∪ Icc (-b) (-a) := by
        ext x; simp only [mem_ofPred_eq, mem_Icc, mem_union]
        rcases le_total 0 x with hx | hx
        · rw [abs_of_nonneg hx]; constructor
          · exact Or.inl
          · rintro (h | ⟨h1, h2⟩)
            · exact h
            · exact ⟨by linarith, by linarith⟩
        · rw [abs_of_nonpos hx]; constructor
          · rintro ⟨h1, h2⟩; exact Or.inr ⟨by linarith, by linarith⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨by linarith, by linarith⟩
            · exact ⟨by linarith, by linarith⟩
      have hdisj : volume (Icc a b ∩ Icc (-b) (-a)) = 0 := by
        have hsub : Icc a b ∩ Icc (-b) (-a) ⊆ {0} := by
          intro x ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
          simp only [mem_singleton_iff]; linarith
        exact measure_mono_null hsub (measure_singleton 0)
      have hunion_int : (∫ x in Icc a b ∪ Icc (-b) (-a), f x) =
          (∫ x in Icc a b, f x) + ∫ x in Icc (-b) (-a), f x := by
        rw [← integral_indicator (measurableSet_Icc.union measurableSet_Icc),
            ← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc,
            ← integral_add (hf_int.indicator measurableSet_Icc) (hf_int.indicator measurableSet_Icc)]
        refine integral_congr_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdisj] with x hx
        by_cases h1 : x ∈ Icc a b
        · have h2 : x ∉ Icc (-b) (-a) := fun h2 => hx ⟨h1, h2⟩
          rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1,
              Set.indicator_of_notMem h2, add_zero]
        · by_cases h2 : x ∈ Icc (-b) (-a)
          · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1,
                Set.indicator_of_mem h2, zero_add]
          · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
                Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
      rw [hdecomp, hunion_int]
      have hneg_eq : (∫ x in Icc (-b) (-a), f x) = ∫ x in Icc a b, f x := by
        have h1 : ∫ x in Icc (-b) (-a), f x = ∫ x in Icc (-b) (-a), f (-x) :=
          setIntegral_congr_ae measurableSet_Icc (hf_even.mono fun x hx _ => hx.symm)
        rw [h1, ← integral_indicator measurableSet_Icc, ← integral_neg_eq_self]
        have hind : (fun x : ℝ => (Icc (-b) (-a)).indicator (fun y => f (-y)) (-x)) =
            (Icc a b).indicator f := by
          ext x
          by_cases hx : x ∈ Icc a b
          · have hnx : -x ∈ Icc (-b) (-a) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
            rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx, neg_neg]
          · have hnx : -x ∉ Icc (-b) (-a) := fun ⟨h1, h2⟩ => hx ⟨by linarith, by linarith⟩
            rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]
        rw [hind, integral_indicator measurableSet_Icc]
      rw [hneg_eq, two_smul]
    rw [hsplit, two_smul, ← two_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left two_ne_zero
  -- Step 3: `∫_{Icc a b} f = 0` for all `a ≤ b` by evenness and `VectorMeasure.ext_of_Icc`
  have hIcc_neg : ∀ a b : ℝ, a ≤ b → b ≤ 0 → ∫ x in Icc a b, f x = 0 := by
    intro a b hab hb
    have h1 : ∫ x in Icc a b, f x = ∫ x in Icc a b, f (-x) :=
      setIntegral_congr_ae measurableSet_Icc (hf_even.mono fun x hx _ => hx.symm)
    rw [h1, ← integral_indicator measurableSet_Icc, ← integral_neg_eq_self]
    have hind : (fun x : ℝ => (Icc a b).indicator (fun y => f (-y)) (-x)) =
        (Icc (-b) (-a)).indicator f := by
      ext x
      by_cases hx : x ∈ Icc (-b) (-a)
      · have hnx : -x ∈ Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
        rw [Set.indicator_of_mem hnx, Set.indicator_of_mem hx, neg_neg]
      · have hnx : -x ∉ Icc a b := fun ⟨h1, h2⟩ => hx ⟨by linarith, by linarith⟩
        rw [Set.indicator_of_notMem hnx, Set.indicator_of_notMem hx]
    rw [hind, integral_indicator measurableSet_Icc]
    exact hIcc_pos (-b) (-a) (by linarith) (by linarith)
  have hIcc_all : ∀ a b : ℝ, a ≤ b → ∫ x in Icc a b, f x = 0 := by
    intro a b hab
    rcases le_total 0 a with ha | ha
    · exact hIcc_pos a b ha hab
    · rcases le_total b 0 with hb | hb
      · exact hIcc_neg a b hab hb
      · have hunion : Icc a b = Icc a 0 ∪ Icc 0 b := (Icc_union_Icc_eq_Icc ha hb).symm
        have hdisj : volume (Icc a 0 ∩ Icc 0 b) = 0 := by
          have hsub : Icc a 0 ∩ Icc 0 b ⊆ {0} := by
            intro x ⟨⟨_, h2⟩, ⟨h3, _⟩⟩; simp only [mem_singleton_iff]; linarith
          exact measure_mono_null hsub (measure_singleton 0)
        have hunion_int : (∫ x in Icc a 0 ∪ Icc 0 b, f x) =
            (∫ x in Icc a 0, f x) + ∫ x in Icc 0 b, f x := by
          rw [← integral_indicator (measurableSet_Icc.union measurableSet_Icc),
              ← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc,
              ← integral_add (hf_int.indicator measurableSet_Icc) (hf_int.indicator measurableSet_Icc)]
          refine integral_congr_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdisj] with x hx
          by_cases h1 : x ∈ Icc a 0
          · have h2 : x ∉ Icc 0 b := fun h2 => hx ⟨h1, h2⟩
            rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1,
                Set.indicator_of_notMem h2, add_zero]
          · by_cases h2 : x ∈ Icc 0 b
            · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1,
                  Set.indicator_of_mem h2, zero_add]
            · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
                  Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
        rw [hunion, hunion_int, hIcc_neg a 0 ha le_rfl, hIcc_pos 0 b le_rfl hb, add_zero]
  have hvm : volume.withDensityᵥ f = 0 := by
    refine VectorMeasure.ext_of_Icc _ _ fun a b hab => ?_
    rw [withDensityᵥ_apply hf_int measurableSet_Icc, FunLike.coe_zero, Pi.zero_apply,
        hIcc_all a b hab]
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hf_int.integrableOn) fun s hs _ => ?_
  have hs_eq := congrArg (fun v : VectorMeasure ℝ ℂ => v s) hvm
  rw [withDensityᵥ_apply hf_int hs, FunLike.coe_zero, Pi.zero_apply] at hs_eq
  exact hs_eq

/-- 2D anisotropic Gaussian in `RadialSpace 1`: `x ↦ exp(-π (βL (x 0)² + βR (x 1)²))`. -/
private noncomputable def spinExp2DC (βL βR : ℝ) (x : RadialSpace 1) : ℂ :=
  (Real.exp (-π * (βL * (x 0) ^ 2 + βR * (x 1) ^ 2)) : ℂ)

private lemma memLp_spinExp2DC {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    MemLp (spinExp2DC βL βR) 2 (volume : Measure (RadialSpace 1)) := by
  have hint_sq : Integrable (fun x : RadialSpace 1 => ‖spinExp2DC βL βR x‖ ^ 2) := by
    have hpt : (fun x : RadialSpace 1 => ‖spinExp2DC βL βR x‖ ^ 2) =
        fun x => Real.exp (-(2 * π * βL) * (wE2ToProd x).1 ^ 2) *
          Real.exp (-(2 * π * βR) * (wE2ToProd x).2 ^ 2) := by
      ext x
      simp only [spinExp2DC, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        wE2ToProd_apply]
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hpt]
    refine wVolume_preserving_e2ToProd.integrable_comp_of_integrable
      (g := fun p : ℝ × ℝ => Real.exp (-(2 * π * βL) * p.1 ^ 2) * Real.exp (-(2 * π * βR) * p.2 ^ 2)) ?_
    rw [Measure.volume_eq_prod]
    exact (integrable_exp_neg_mul_sq (by positivity : 0 < 2 * π * βL)).mul_prod
      (integrable_exp_neg_mul_sq (by positivity : 0 < 2 * π * βR))
  have hcont : Continuous (spinExp2DC βL βR) := by
    unfold spinExp2DC
    have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
      (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
    have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
      (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_const.mul (h0.pow 2)).add (continuous_const.mul (h1.pow 2)))))
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hint_sq

private lemma integrable_spinExp2DC {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    Integrable (spinExp2DC βL βR) (volume : Measure (RadialSpace 1)) := by
  have hpt : (fun x : RadialSpace 1 => ‖spinExp2DC βL βR x‖) =
      fun x => Real.exp (-(π * βL) * (wE2ToProd x).1 ^ 2) *
        Real.exp (-(π * βR) * (wE2ToProd x).2 ^ 2) := by
    ext x
    simp only [spinExp2DC, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      wE2ToProd_apply]
    rw [← Real.exp_add]; congr 1; ring
  have hcont : Continuous (spinExp2DC βL βR) := by
    unfold spinExp2DC
    have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
      (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
    have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
      (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_const.mul (h0.pow 2)).add (continuous_const.mul (h1.pow 2)))))
  rw [← integrable_norm_iff hcont.aestronglyMeasurable, hpt]
  refine wVolume_preserving_e2ToProd.integrable_comp_of_integrable
    (g := fun p : ℝ × ℝ => Real.exp (-(π * βL) * p.1 ^ 2) * Real.exp (-(π * βR) * p.2 ^ 2)) ?_
  rw [Measure.volume_eq_prod]
  exact (integrable_exp_neg_mul_sq (by positivity : 0 < π * βL)).mul_prod
    (integrable_exp_neg_mul_sq (by positivity : 0 < π * βR))

/-- 2D Fourier transform of `spinExp2DC βL βR` in `L²(RadialSpace 1)`. -/
private lemma fourier_spinExp2DC_L2 {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR)
    (hmem : MemLp (spinExp2DC βL βR) 2 (volume : Measure (RadialSpace 1))) :
    (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ) (hmem.toLp (spinExp2DC βL βR)) =
      (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        (memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).toLp (spinExp2DC βL⁻¹ βR⁻¹) := by
  have h1 := integrable_spinExp2DC hβL hβR
  have hpt : ∀ ξ : RadialSpace 1, 𝓕 (spinExp2DC βL βR) ξ =
      (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * spinExp2DC βL⁻¹ βR⁻¹ ξ := by
    intro ξ
    rw [Real.fourier_eq]
    have hchg : (∫ x : RadialSpace 1, Real.fourierChar (-⟪x, ξ⟫) • spinExp2DC βL βR x) =
        ∫ p : ℝ × ℝ,
          (Real.fourierChar (-(p.1 * ξ 0)) • (Real.exp (-π * βL * p.1 ^ 2) : ℂ)) *
          (Real.fourierChar (-(p.2 * ξ 1)) • (Real.exp (-π * βR * p.2 ^ 2) : ℂ)) := by
      rw [← wVolume_preserving_e2ToProd.integral_comp'
        (g := fun p : ℝ × ℝ =>
          (Real.fourierChar (-(p.1 * ξ 0)) • (Real.exp (-π * βL * p.1 ^ 2) : ℂ)) *
          (Real.fourierChar (-(p.2 * ξ 1)) • (Real.exp (-π * βR * p.2 ^ 2) : ℂ)))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      have hinner : ⟪x, ξ⟫ = x 0 * ξ 0 + x 1 * ξ 1 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, Fin.sum_univ_two, mul_comm]
      rw [hinner, neg_add]
      have hchar : (Real.fourierChar (-(x 0 * ξ 0) + -(x 1 * ξ 1)) : ℂ) =
          (Real.fourierChar (-(x 0 * ξ 0)) : ℂ) * (Real.fourierChar (-(x 1 * ξ 1)) : ℂ) := by
        rw [AddChar.map_add_eq_mul]; rfl
      have hexp : (Real.exp (-π * (βL * (x 0) ^ 2 + βR * (x 1) ^ 2)) : ℂ) =
          (Real.exp (-π * βL * (x 0) ^ 2) : ℂ) * (Real.exp (-π * βR * (x 1) ^ 2) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
      simp only [Circle.smul_def, smul_eq_mul, spinExp2DC, wE2ToProd_apply]
      rw [hchar, hexp]; ring
    rw [hchg, Measure.volume_eq_prod, integral_prod_mul
      (fun u => Real.fourierChar (-(u * ξ 0)) • (Real.exp (-π * βL * u ^ 2) : ℂ))
      (fun v => Real.fourierChar (-(v * ξ 1)) • (Real.exp (-π * βR * v ^ 2) : ℂ))]
    have h1D : ∀ {β : ℝ}, 0 < β → ∀ ω : ℝ,
        (∫ u : ℝ, Real.fourierChar (-(u * ω)) • (Real.exp (-π * β * u ^ 2) : ℂ)) =
          ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.exp (-π * β⁻¹ * ω ^ 2) : ℂ) := by
      intro β hβ ω
      have h_eq : (∫ u : ℝ, Real.fourierChar (-(u * ω)) • (Real.exp (-π * β * u ^ 2) : ℂ)) =
          𝓕 (fun u : ℝ => (Real.exp (-π * β * u ^ 2) : ℂ)) ω := by
        rw [Real.fourier_eq]; refine integral_congr_ae (Eventually.of_forall fun u => by simp [mul_comm])
      rw [h_eq]
      have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
      have hfn : (fun u : ℝ => (Real.exp (-π * β * u ^ 2) : ℂ)) =
          fun u => Complex.exp (-((π * β : ℝ) : ℂ) * (‖u‖ : ℂ) ^ 2) := by
        ext u; rw [Complex.ofReal_exp]
        have hnu : (‖u‖ : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by
          rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
        rw [hnu]; congr 1; push_cast; ring
      rw [hfn, fourier_gaussian_innerProductSpace hb ω]
      have hdim : (Module.finrank ℝ ℝ / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by simp
      have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
        have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
        push_cast; field_simp
      have hnw : (‖ω‖ : ℂ) ^ 2 = ((ω ^ 2 : ℝ) : ℂ) := by
        rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
      rw [hdim, hpi, ← Complex.ofReal_cpow (inv_nonneg.mpr hβ.le), Real.inv_rpow hβ.le,
          ← Real.rpow_neg hβ.le, Complex.ofReal_exp, hnw]
      congr 2; push_cast
      have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
      field_simp
    rw [h1D hβL (ξ 0), h1D hβR (ξ 1)]
    unfold spinExp2DC
    have hpow : (βL * βR) ^ (-(1 / 2 : ℝ)) = βL ^ (-(1 / 2 : ℝ)) * βR ^ (-(1 / 2 : ℝ)) :=
      Real.mul_rpow hβL.le hβR.le
    have hexp : (Real.exp (-π * (βL⁻¹ * (ξ 0) ^ 2 + βR⁻¹ * (ξ 1) ^ 2)) : ℂ) =
        (Real.exp (-π * βL⁻¹ * (ξ 0) ^ 2) : ℂ) * (Real.exp (-π * βR⁻¹ * (ξ 1) ^ 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [hpow, hexp, Complex.ofReal_mul]; ring
  have hFf2 : MemLp (𝓕 (spinExp2DC βL βR)) 2 (volume : Measure (RadialSpace 1)) := by
    have : 𝓕 (spinExp2DC βL βR) =
        (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • spinExp2DC βL⁻¹ βR⁻¹ := funext hpt
    rw [this]
    exact (memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_smul _
  have hfour_lp : (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ) (hmem.toLp (spinExp2DC βL βR)) =
      hFf2.toLp (𝓕 (spinExp2DC βL βR)) :=
    toLp_fourier_eq_of_integrable h1 hmem hFf2
  rw [hfour_lp]
  ext1
  filter_upwards [hFf2.coeFn_toLp,
    Lp.coeFn_smul (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      ((memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).toLp _),
    (memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).coeFn_toLp] with x hxa hxb hxc
  rw [hxa, hxb, Pi.smul_apply, hxc, hpt x]; rfl

/-- Thermal difference `X_{βL, βR}` in `RadialSpace 1` coordinates. -/
private noncomputable def spinThermalX_euc (βL βR : ℝ) (x : RadialSpace 1) : ℝ :=
  spinThermalX βL βR ((x 0) ^ 2 / 2) ((x 1) ^ 2 / 2)

private lemma memLp_spinThermalX_euc {βL βR : ℝ} (hβL : 0 < βL) (hβR : 0 < βR) :
    MemLp (fun x : RadialSpace 1 => (spinThermalX_euc βL βR x : ℂ)) 2
      (volume : Measure (RadialSpace 1)) := by
  have heq : (fun x : RadialSpace 1 => (spinThermalX_euc βL βR x : ℂ)) =
      spinExp2DC βL βR - (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • spinExp2DC βL⁻¹ βR⁻¹ := by
    ext x
    simp only [spinThermalX_euc, spinThermalX, spinExp2DC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_sub, Complex.ofReal_mul]
    congr 1
    · congr 2; ring
    · congr 2; congr 1; field_simp [hβL.ne', hβR.ne']
  rw [heq]
  exact (memLp_spinExp2DC hβL hβR).sub
    ((memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_smul _)

private lemma continuous_finset_sum_aux {α ι : Type*} [TopologicalSpace α]
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma integrable_finset_sum_aux {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma integral_finset_sum_aux {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    (∫ x, ∑ i ∈ s, f i x ∂μ) = ∑ i ∈ s, ∫ x, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hsum_int : Integrable (fun x => ∑ i ∈ s, f i x) μ :=
      integrable_finset_sum_aux s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [integral_add (hf a (Finset.mem_insert_self a s)) hsum_int,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma memLp_finset_sum_aux {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    MemLp (fun x => ∑ i ∈ s, f i x) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Any even `Φ ∈ SpinTestClass a` lies in the `L²` closure of the complex span of
2D anisotropic Gaussians `spinExp2DC βL βR`. -/
private lemma mem_closure_span_spinExp2DC {a : ℝ} (_ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    (hΦ_memLp : MemLp (spinToEuc Φ) 2 (volume : Measure (RadialSpace 1))) :
    hΦ_memLp.toLp (spinToEuc Φ) ∈
      (Submodule.span ℂ { u : Lp ℂ 2 (volume : Measure (RadialSpace 1)) |
        ∃ βL > 0, ∃ βR > 0,
          ∃ h : MemLp (spinExp2DC βL βR) 2 (volume : Measure (RadialSpace 1)),
            u = h.toLp (spinExp2DC βL βR) }).topologicalClosure := by
  let fLp : Lp ℂ 2 (volume : Measure (RadialSpace 1)) := hΦ_memLp.toLp (spinToEuc Φ)
  let S_exp : Submodule ℂ (Lp ℂ 2 (volume : Measure (RadialSpace 1))) :=
    Submodule.span ℂ { u | ∃ βL > 0, ∃ βR > 0,
      ∃ h : MemLp (spinExp2DC βL βR) 2 (volume : Measure (RadialSpace 1)),
        u = h.toLp (spinExp2DC βL βR) }
  have : CompleteSpace S_exp.topologicalClosure :=
    S_exp.isClosed_topologicalClosure.completeSpace_coe
  let P := Submodule.starProjection S_exp.topologicalClosure
  set u : Lp ℂ 2 (volume : Measure (RadialSpace 1)) := fLp - P fLp
  have hu_orth : ∀ w ∈ S_exp.topologicalClosure, @inner ℂ _ _ w u = 0 := fun w hw =>
    Submodule.inner_right_of_mem_orthogonal hw (Submodule.sub_starProjection_mem_orthogonal fLp)
  let uFn : ℝ × ℝ → ℂ := fun p => (u : RadialSpace 1 → ℂ) (wE2ToProd.symm p)
  let uEv : ℝ × ℝ → ℂ := fun p =>
    (1 / 4 : ℂ) * (uFn (p.1, p.2) + uFn (-p.1, p.2) + uFn (p.1, -p.2) + uFn (-p.1, -p.2))
  have huFn_L2 : MemLp uFn 2 (volume : Measure (ℝ × ℝ)) :=
    (Lp.memLp u).comp_measurePreserving wVolume_preserving_e2ToProd.symm
  let eFlip1 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
  let eFlip2 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  let eFlip12 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hflip1 : MeasurePreserving eFlip1 volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
  have hflip2 : MeasurePreserving eFlip2 volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
  have hflip12 : MeasurePreserving eFlip12 volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)
  have huEv_L2 : MemLp uEv 2 (volume : Measure (ℝ × ℝ)) :=
    (((huFn_L2.add (huFn_L2.comp_measurePreserving hflip1)).add
      (huFn_L2.comp_measurePreserving hflip2)).add
      (huFn_L2.comp_measurePreserving hflip12)).const_mul (1 / 4 : ℂ)
  -- `uEv` is orthogonal to `exp(-π (m+1) x² - π (n+1) y²)` for all `m, n : ℕ`
  have huEv_orth_mn : ∀ m n : ℕ,
      ∫ p : ℝ × ℝ,
        (Real.exp (-π * ((m : ℝ) + 1) * p.1 ^ 2 - π * ((n : ℝ) + 1) * p.2 ^ 2) : ℝ) • uEv p = 0 := by
    intro m n
    set βL : ℝ := (m : ℝ) + 1
    set βR : ℝ := (n : ℝ) + 1
    have hβL : 0 < βL := by positivity
    have hβR : 0 < βR := by positivity
    have hmemG := memLp_spinExp2DC hβL hβR
    have hG_mem : hmemG.toLp (spinExp2DC βL βR) ∈ S_exp.topologicalClosure :=
      S_exp.le_topologicalClosure (Submodule.subset_span ⟨βL, hβL, βR, hβR, hmemG, rfl⟩)
    have h_in0 : @inner ℂ _ _ (hmemG.toLp (spinExp2DC βL βR)) u = 0 := hu_orth _ hG_mem
    rw [L2.inner_def] at h_in0
    have h_uFn0 : ∫ p : ℝ × ℝ,
        (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn p = 0 := by
      rw [← wVolume_preserving_e2ToProd.integral_comp'
        (g := fun p : ℝ × ℝ => (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn p)]
      rw [← h_in0]
      refine integral_congr_ae ?_
      filter_upwards [hmemG.coeFn_toLp] with x hx
      rw [hx]
      dsimp only [uFn]
      rw [MeasurableEquiv.symm_apply_apply]
      simp only [spinExp2DC, wE2ToProd_apply, RCLike.inner_apply, Complex.conj_ofReal,
        Complex.real_smul, mul_comm]
    have hflip_int : ∀ (e : ℝ × ℝ ≃ᵐ ℝ × ℝ), MeasurePreserving e volume volume →
        (∀ p, (e p).1 ^ 2 = p.1 ^ 2 ∧ (e p).2 ^ 2 = p.2 ^ 2) →
        ∫ p : ℝ × ℝ, (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (e p) = 0 := by
      intro e he hsq
      have h1 := he.integral_comp'
        (g := fun p : ℝ × ℝ => (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn p)
      rw [h_uFn0] at h1
      rw [← h1]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [(hsq p).1, (hsq p).2]
    have hint_term : ∀ (e : ℝ × ℝ ≃ᵐ ℝ × ℝ), MeasurePreserving e volume volume →
        Integrable (fun p : ℝ × ℝ => (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (e p)) := by
      intro e he
      have hG_L2 : MemLp (fun p : ℝ × ℝ => (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℂ)) 2 volume :=
        (hmemG.comp_measurePreserving wVolume_preserving_e2ToProd.symm).ae_eq
          (Eventually.of_forall fun p => by
            simp [spinExp2DC, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one])
      refine ((huFn_L2.comp_measurePreserving he).integrable_mul hG_L2).congr (Eventually.of_forall fun p => ?_)
      change uFn (e p) * (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℂ) =
        (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (e p)
      rw [Complex.real_smul, mul_comm]
    have hpt_uEv : (fun p : ℝ × ℝ =>
          (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uEv p) =
        fun p => (1 / 4 : ℂ) *
          ((Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (MeasurableEquiv.refl _ p) +
           (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip1 p) +
           (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip2 p) +
           (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip12 p)) := by
      ext p
      have he0 : MeasurableEquiv.refl (ℝ × ℝ) p = (p.1, p.2) := rfl
      have he1 : eFlip1 p = (-p.1, p.2) := rfl
      have he2 : eFlip2 p = (p.1, -p.2) := rfl
      have he12 : eFlip12 p = (-p.1, -p.2) := rfl
      rw [he0, he1, he2, he12]
      dsimp only [uEv]
      simp only [Complex.real_smul]; ring
    have hrew' : (fun p : ℝ × ℝ =>
          (Real.exp (-π * βL * p.1 ^ 2 - π * βR * p.2 ^ 2) : ℝ) • uEv p) =
        fun p => (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uEv p := by
      ext p; congr 2; ring
    have hI0 := hint_term (MeasurableEquiv.refl _) (MeasurePreserving.id _)
    have hI1 := hint_term eFlip1 hflip1
    have hI2 := hint_term eFlip2 hflip2
    have hI3 := hint_term eFlip12 hflip12
    have hI01 : Integrable (fun p : ℝ × ℝ =>
        (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (MeasurableEquiv.refl _ p) +
        (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip1 p)) := hI0.add hI1
    have hI012 : Integrable (fun p : ℝ × ℝ =>
        ((Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (MeasurableEquiv.refl _ p) +
         (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip1 p)) +
        (Real.exp (-π * (βL * p.1 ^ 2 + βR * p.2 ^ 2)) : ℝ) • uFn (eFlip2 p)) := hI01.add hI2
    rw [hrew', hpt_uEv, integral_const_mul,
        integral_add hI012 hI3, integral_add hI01 hI2, integral_add hI0 hI1]
    simp only [MeasurableEquiv.refl_apply]
    rw [h_uFn0,
        hflip_int eFlip1 hflip1 (fun p => ⟨neg_sq p.1, rfl⟩),
        hflip_int eFlip2 hflip2 (fun p => ⟨rfl, neg_sq p.2⟩),
        hflip_int eFlip12 hflip12 (fun p => ⟨neg_sq p.1, neg_sq p.2⟩)]
    simp
  -- Apply 1D Weierstrass twice (first in `y`, then in `x`) to show `uEv = 0` a.e.
  have huEv_zero : uEv =ᵐ[volume] 0 := by
    have hint_base : ∀ m : ℕ, Integrable (fun p : ℝ × ℝ =>
        (Real.exp (-π * ((m : ℝ) + 1) * p.1 ^ 2 - π * p.2 ^ 2) : ℝ) • uEv p) (volume.prod volume) := by
      intro m
      have hG_L2 : MemLp (fun p : ℝ × ℝ =>
          (Real.exp (-π * (((m : ℝ) + 1) * p.1 ^ 2 + 1 * p.2 ^ 2)) : ℂ)) 2 (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact ((memLp_spinExp2DC (by positivity : (0 : ℝ) < (m : ℝ) + 1) one_pos).comp_measurePreserving
          wVolume_preserving_e2ToProd.symm).ae_eq (Eventually.of_forall fun p => by
            simp [spinExp2DC, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one])
      rw [← Measure.volume_eq_prod] at hG_L2 ⊢
      refine (huEv_L2.integrable_mul hG_L2).congr (Eventually.of_forall fun p => ?_)
      change uEv p * (Real.exp (-π * (((m : ℝ) + 1) * p.1 ^ 2 + 1 * p.2 ^ 2)) : ℂ) =
        (Real.exp (-π * ((m : ℝ) + 1) * p.1 ^ 2 - π * p.2 ^ 2) : ℝ) • uEv p
      rw [Complex.real_smul, mul_comm]; congr 3; ring
    have hslice_zero : ∀ m : ℕ, ∀ᵐ y : ℝ,
        ∫ x : ℝ, (Real.exp (-π * ((m : ℝ) + 1) * x ^ 2) : ℝ) • uEv (x, y) = 0 := by
      intro m
      let g_m : ℝ → ℂ := fun y =>
        (Real.exp (-π * y ^ 2) : ℝ) •
          ∫ x : ℝ, (Real.exp (-π * ((m : ℝ) + 1) * x ^ 2) : ℝ) • uEv (x, y)
      have hg_int : Integrable g_m := by
        have h1 := (hint_base m).integral_prod_right
        refine h1.congr (Eventually.of_forall fun y => ?_)
        dsimp [g_m]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← mul_assoc (Real.exp (-π * y ^ 2) : ℂ), ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3; ring
      have hg_even : ∀ᵐ y : ℝ, g_m (-y) = g_m y := by
        refine Eventually.of_forall fun y => ?_
        dsimp [g_m]; rw [neg_sq]
        congr 1; refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp [uEv]; simp only [neg_neg]; ring
      have hg_orth : ∀ n : ℕ, ∫ y : ℝ, (Real.exp (-π * y ^ 2)) ^ n • g_m y = 0 := by
        intro n
        have h0 := huEv_orth_mn m n
        rw [Measure.volume_eq_prod, integral_prod_symm] at h0
        · rw [← h0]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp [g_m]
          simp only [← mul_assoc, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 3; ring
        · have hG_L2 : MemLp (fun p : ℝ × ℝ =>
              (Real.exp (-π * (((m : ℝ) + 1) * p.1 ^ 2 + ((n : ℝ) + 1) * p.2 ^ 2)) : ℂ)) 2 volume :=
            ((memLp_spinExp2DC (by positivity : (0 : ℝ) < (m : ℝ) + 1)
              (by positivity : (0 : ℝ) < (n : ℝ) + 1)).comp_measurePreserving
              wVolume_preserving_e2ToProd.symm).ae_eq (Eventually.of_forall fun p => by
                simp [spinExp2DC, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one])
          rw [← Measure.volume_eq_prod]
          refine (huEv_L2.integrable_mul hG_L2).congr (Eventually.of_forall fun p => ?_)
          change uEv p * (Real.exp (-π * (((m : ℝ) + 1) * p.1 ^ 2 + ((n : ℝ) + 1) * p.2 ^ 2)) : ℂ) =
            (Real.exp (-π * ((m : ℝ) + 1) * p.1 ^ 2 - π * ((n : ℝ) + 1) * p.2 ^ 2) : ℝ) • uEv p
          rw [Complex.real_smul, mul_comm]; congr 3; ring
      have hg0 := ae_eq_zero_of_forall_exp_sq_1D hg_int hg_even hg_orth
      filter_upwards [hg0] with y hy
      dsimp [g_m] at hy
      have h0 := (mul_eq_zero.mp hy).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
      simpa only [Complex.real_smul] using h0
    have h_all_m : ∀ᵐ y : ℝ, ∀ m : ℕ,
        ∫ x : ℝ, (Real.exp (-π * ((m : ℝ) + 1) * x ^ 2) : ℝ) • uEv (x, y) = 0 :=
      ae_all_iff.mpr hslice_zero
    have h_int_y : ∀ᵐ y : ℝ, Integrable (fun x : ℝ => (Real.exp (-π * x ^ 2) : ℝ) • uEv (x, y)) := by
      have h1 := ((integrable_prod_iff' (hint_base 0).aestronglyMeasurable).mp (hint_base 0)).1
      filter_upwards [h1] with y hy
      have hscale := hy.smul (Real.exp (π * y ^ 2))
      refine hscale.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_smul, ← Real.exp_add]
      congr 2; ring
    have h_ae_xy : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, uEv (x, y) = 0 := by
      filter_upwards [h_all_m, h_int_y] with y hym hinty
      have heven_x : ∀ᵐ x : ℝ, (Real.exp (-π * (-x) ^ 2) : ℝ) • uEv (-x, y) =
          (Real.exp (-π * x ^ 2) : ℝ) • uEv (x, y) := by
        refine Eventually.of_forall fun x => ?_
        rw [neg_sq]; congr 1; dsimp [uEv]; simp only [neg_neg]; ring
      have horth_x : ∀ m : ℕ, ∫ x : ℝ, (Real.exp (-π * x ^ 2)) ^ m •
          ((Real.exp (-π * x ^ 2) : ℝ) • uEv (x, y)) = 0 := by
        intro m
        rw [← hym m]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [smul_smul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2; ring
      have hx0 := ae_eq_zero_of_forall_exp_sq_1D hinty heven_x horth_x
      filter_upwards [hx0] with x hx
      rw [Complex.real_smul] at hx
      exact (mul_eq_zero.mp hx).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    -- Lift `∀ᵐ y, ∀ᵐ x, uEv (x, y) = 0` to `uEv =ᵐ[volume] 0` via measurable representative
    let v : ℝ × ℝ → ℂ := huEv_L2.aestronglyMeasurable.mk uEv
    have hv_ae : uEv =ᵐ[volume.prod volume] v := by
      rw [← Measure.volume_eq_prod]; exact huEv_L2.aestronglyMeasurable.ae_eq_mk
    have hv_swap_ae : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, uEv (p.2, p.1) = v (p.2, p.1) :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hv_ae
    have hv_xy : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, v (x, y) = 0 := by
      have hswap := Measure.ae_ae_of_ae_prod hv_swap_ae
      filter_upwards [h_ae_xy, hswap] with y hy1 hy2
      filter_upwards [hy1, hy2] with x hx1 hx2
      rw [← hx2, hx1]
    have hv_swap_meas : MeasurableSet {p : ℝ × ℝ | v (p.2, p.1) = 0} :=
      (huEv_L2.aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp measurable_swap)
        (measurableSet_singleton 0)
    have hv_swap_zero : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, v (p.2, p.1) = 0 :=
      (Measure.ae_prod_iff_ae_ae hv_swap_meas).mpr hv_xy
    have hv_zero : v =ᵐ[volume.prod volume] 0 :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hv_swap_zero
    rw [Measure.volume_eq_prod]
    exact hv_ae.trans hv_zero
  -- Prove `⟨u, fLp⟩ = 0` using `uEv =ᵐ 0` and evenness of `Φ`, hence `‖u‖² = 0`
  have hu_inner_f : @inner ℂ _ _ u fLp = 0 := by
    rw [L2.inner_def]
    have h1 : (∫ x : RadialSpace 1, @inner ℂ _ _ ((u : RadialSpace 1 → ℂ) x) ((fLp : RadialSpace 1 → ℂ) x)) =
        ∫ p : ℝ × ℝ, starRingEnd ℂ (uFn p) * (Φ p : ℂ) := by
      rw [← wVolume_preserving_e2ToProd.integral_comp'
        (g := fun p : ℝ × ℝ => starRingEnd ℂ (uFn p) * (Φ p : ℂ))]
      refine integral_congr_ae ?_
      filter_upwards [hΦ_memLp.coeFn_toLp] with x hx
      rw [hx]
      dsimp only [uFn]
      rw [MeasurableEquiv.symm_apply_apply]
      simp only [spinToEuc, wE2ToProd_apply, RCLike.inner_apply, mul_comm]
    rw [h1]
    have hint_fl : ∀ (e : ℝ × ℝ ≃ᵐ ℝ × ℝ), MeasurePreserving e volume volume →
        Integrable (fun p : ℝ × ℝ => starRingEnd ℂ (uFn (e p)) * (Φ p : ℂ)) := by
      intro e he
      have hΦ_L2 : MemLp (fun p : ℝ × ℝ => (Φ p : ℂ)) 2 volume :=
        (hΦ_memLp.comp_measurePreserving wVolume_preserving_e2ToProd.symm).ae_eq
          (Eventually.of_forall fun p => by
            simp [spinToEuc, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one])
      have hu_conj : MemLp (fun p : ℝ × ℝ => starRingEnd ℂ (uFn (e p))) 2 volume :=
        (huFn_L2.comp_measurePreserving he).star
      exact hu_conj.integrable_mul hΦ_L2
    have hflip_eq : ∀ (e : ℝ × ℝ ≃ᵐ ℝ × ℝ), MeasurePreserving e volume volume →
        (∀ p, Φ (e p) = Φ p) →
        (∫ p : ℝ × ℝ, starRingEnd ℂ (uFn (e p)) * (Φ p : ℂ)) =
          ∫ p : ℝ × ℝ, starRingEnd ℂ (uFn p) * (Φ p : ℂ) := by
      intro e he hΦf
      rw [← he.integral_comp' (g := fun p : ℝ × ℝ => starRingEnd ℂ (uFn p) * (Φ p : ℂ))]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [hΦf p]
    have havg : (∫ p : ℝ × ℝ, starRingEnd ℂ (uFn p) * (Φ p : ℂ)) =
        ∫ p : ℝ × ℝ, starRingEnd ℂ (uEv p) * (Φ p : ℂ) := by
      have hpt : (fun p : ℝ × ℝ => starRingEnd ℂ (uEv p) * (Φ p : ℂ)) =
          fun p => (1 / 4 : ℂ) *
            (starRingEnd ℂ (uFn (MeasurableEquiv.refl _ p)) * (Φ p : ℂ) +
             starRingEnd ℂ (uFn (eFlip1 p)) * (Φ p : ℂ) +
             starRingEnd ℂ (uFn (eFlip2 p)) * (Φ p : ℂ) +
             starRingEnd ℂ (uFn (eFlip12 p)) * (Φ p : ℂ)) := by
        ext p
        have he0 : MeasurableEquiv.refl (ℝ × ℝ) p = (p.1, p.2) := rfl
        have he1 : eFlip1 p = (-p.1, p.2) := rfl
        have he2 : eFlip2 p = (p.1, -p.2) := rfl
        have he12 : eFlip12 p = (-p.1, -p.2) := rfl
        rw [he0, he1, he2, he12]
        dsimp only [uEv]
        simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]
        ring
      have hJ0 := hint_fl (MeasurableEquiv.refl _) (MeasurePreserving.id _)
      have hJ1 := hint_fl eFlip1 hflip1
      have hJ2 := hint_fl eFlip2 hflip2
      have hJ3 := hint_fl eFlip12 hflip12
      have hJ01 : Integrable (fun p : ℝ × ℝ =>
          starRingEnd ℂ (uFn (MeasurableEquiv.refl _ p)) * (Φ p : ℂ) +
          starRingEnd ℂ (uFn (eFlip1 p)) * (Φ p : ℂ)) := hJ0.add hJ1
      have hJ012 : Integrable (fun p : ℝ × ℝ =>
          (starRingEnd ℂ (uFn (MeasurableEquiv.refl _ p)) * (Φ p : ℂ) +
           starRingEnd ℂ (uFn (eFlip1 p)) * (Φ p : ℂ)) +
          starRingEnd ℂ (uFn (eFlip2 p)) * (Φ p : ℂ)) := hJ01.add hJ2
      rw [hpt, integral_const_mul,
          integral_add hJ012 hJ3, integral_add hJ01 hJ2, integral_add hJ0 hJ1,
          hflip_eq eFlip1 hflip1 (fun p => hΦ.d4_inv.1 p.1 p.2),
          hflip_eq eFlip2 hflip2 (fun p => hΦ.d4_inv.2.1 p.1 p.2),
          hflip_eq eFlip12 hflip12 (fun p => by
            change Φ (-p.1, -p.2) = Φ (p.1, p.2)
            rw [hΦ.d4_inv.1, hΦ.d4_inv.2.1])]
      simp [MeasurableEquiv.refl]; ring
    rw [havg]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [huEv_zero] with p hp
    simp [hp]
  have hu_zero : u = 0 := by
    have h1 : @inner ℂ _ _ u u = 0 := by
      have h2 : @inner ℂ _ _ (P fLp) u = 0 := hu_orth _ (Submodule.starProjection_apply_mem _ fLp)
      have h3 : @inner ℂ _ _ u (P fLp) = 0 := by
        rw [← inner_conj_symm, h2, map_zero]
      calc @inner ℂ _ _ u u = @inner ℂ _ _ u (fLp - P fLp) := rfl
        _ = @inner ℂ _ _ u fLp - @inner ℂ _ _ u (P fLp) := inner_sub_right _ _ _
        _ = 0 := by rw [hu_inner_f, h3, sub_zero]
    exact inner_self_eq_zero.mp h1
  have hfeq : fLp = P fLp := sub_eq_zero.mp hu_zero
  change fLp ∈ S_exp.topologicalClosure
  rw [hfeq]; exact Submodule.starProjection_apply_mem _ fLp

private lemma fourier_toLp_neg_of_odd {f : RadialSpace 1 → ℂ}
    (hf1 : Integrable f (volume : Measure (RadialSpace 1)))
    (hf2 : MemLp f 2 (volume : Measure (RadialSpace 1)))
    (hodd : 𝓕 f = -f) :
    (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ) (hf2.toLp f) = -(hf2.toLp f) := by
  have hFf2 : MemLp (𝓕 f) 2 (volume : Measure (RadialSpace 1)) := by
    rw [hodd]; exact hf2.neg
  have hfour_lp : (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ) (hf2.toLp f) = hFf2.toLp (𝓕 f) :=
    toLp_fourier_eq_of_integrable hf1 hf2 hFf2
  rw [hfour_lp]
  ext1
  filter_upwards [hFf2.coeFn_toLp, Lp.coeFn_neg (hf2.toLp f), hf2.coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3, hodd, Pi.neg_apply]

set_option maxHeartbeats 400000 in
/-- Every `Φ ∈ SpinTestClass a` (`a ≥ 2`) can be approximated in `L²(RadialSpace 1)` by finite
real linear combinations of `spinThermalX_euc βL βR` (`βL, βR > 0`). -/
private theorem exists_spinThermalX_approx_L2 {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (c βL βR : Fin N → ℝ), (∀ i, 0 < βL i) ∧ (∀ i, 0 < βR i) ∧
      (∫ x : RadialSpace 1,
        ((∑ i : Fin N, c i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1)) ^ 2) < ε ^ 2 := by
  -- Step 1: `spinToEuc Φ ∈ L²(RadialSpace 1)`
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  have hΦ_euc_int : Integrable (spinToEuc Φ) (volume : Measure (RadialSpace 1)) :=
    (wVolume_preserving_e2ToProd.integrable_comp_of_integrable hΦ.int).ofReal
  have hΦ_memLp : MemLp (spinToEuc Φ) 2 (volume : Measure (RadialSpace 1)) := by
    have hcont : Continuous (spinToEuc Φ) :=
      Complex.continuous_ofReal.comp (hΦ.cont.comp wE2ToProd_continuous)
    refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
    refine (hΦ_euc_int.norm.const_mul (C₀ * spinM2 a Φ)).mono'
      (hcont.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    have h1 : ‖spinToEuc Φ x‖ ≤ C₀ * spinM2 a Φ := by
      simpa [spinToEuc] using hΦ_inf (x 0, x 1)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  let fLp : Lp ℂ 2 (volume : Measure (RadialSpace 1)) := hΦ_memLp.toLp (spinToEuc Φ)
  -- Step 2: `fLp` lies in the `L²` closure of `S_exp = span_ℂ { spinExp2DC βL βR }`
  let S_exp : Submodule ℂ (Lp ℂ 2 (volume : Measure (RadialSpace 1))) :=
    Submodule.span ℂ { u | ∃ βL > 0, ∃ βR > 0,
      ∃ h : MemLp (spinExp2DC βL βR) 2 (volume : Measure (RadialSpace 1)),
        u = h.toLp (spinExp2DC βL βR) }
  have hfLp_in_exp : fLp ∈ S_exp.topologicalClosure :=
    mem_closure_span_spinExp2DC ha hΦ hΦ_memLp
  -- Step 3: Project onto Fourier-odd thermal differences via `T = (1/2)(I - 𝓕_{L²})`
  let S_odd : Submodule ℂ (Lp ℂ 2 (volume : Measure (RadialSpace 1))) :=
    Submodule.span ℂ { u | ∃ βL > 0, ∃ βR > 0,
      ∃ h : MemLp (fun x => (spinThermalX_euc βL βR x : ℂ)) 2 (volume : Measure (RadialSpace 1)),
        u = h.toLp _ }
  let T : Lp ℂ 2 (volume : Measure (RadialSpace 1)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (RadialSpace 1)) :=
    (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ _ -
      (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ).toContinuousLinearEquiv.toContinuousLinearMap)
  have hT_map : ∀ u ∈ S_exp, T u ∈ S_odd := by
    intro u hu
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ hx hy => by rw [map_add]; exact S_odd.add_mem hx hy)
      (fun c _ _ hx => by rw [map_smul]; exact S_odd.smul_mem c hx) hu
    rintro _ ⟨βL, hβL, βR, hβR, hmem, rfl⟩
    have hF := fourier_spinExp2DC_L2 hβL hβR hmem
    have hmemX := memLp_spinThermalX_euc hβL hβR
    have hT_eq : T (hmem.toLp (spinExp2DC βL βR)) =
        (1 / 2 : ℂ) • hmemX.toLp (fun x => (spinThermalX_euc βL βR x : ℂ)) := by
      simp only [T, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
        Pi.sub_apply, ContinuousLinearMap.id_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, hF]
      congr 1
      ext1
      filter_upwards [Lp.coeFn_sub (hmem.toLp (spinExp2DC βL βR))
          ((((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
            (memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).toLp (spinExp2DC βL⁻¹ βR⁻¹)),
        hmem.coeFn_toLp,
        Lp.coeFn_smul (((βL * βR) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          ((memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).toLp (spinExp2DC βL⁻¹ βR⁻¹)),
        (memLp_spinExp2DC (inv_pos.mpr hβL) (inv_pos.mpr hβR)).coeFn_toLp,
        hmemX.coeFn_toLp] with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4, h5]
      simp only [spinThermalX_euc, spinThermalX, spinExp2DC, smul_eq_mul,
        Complex.ofReal_sub, Complex.ofReal_mul]
      congr 1
      · congr 2; ring
      · congr 2; congr 1; field_simp [hβL.ne', hβR.ne']
    rw [hT_eq]
    exact S_odd.smul_mem _ (Submodule.subset_span ⟨βL, hβL, βR, hβR, hmemX, rfl⟩)
  have hT_fLp : T fLp = fLp := by
    have hF_eq : (Lp.fourierTransformₗᵢ (RadialSpace 1) ℂ) fLp = -fLp :=
      fourier_toLp_neg_of_odd hΦ_euc_int hΦ_memLp hΦ.fourier_odd
    simp only [T, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply,
      Pi.sub_apply, ContinuousLinearMap.id_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, hF_eq, sub_neg_eq_add]
    rw [← two_smul ℂ fLp, smul_smul]
    norm_num
  have hfLp_in_odd : fLp ∈ S_odd.topologicalClosure := by
    rw [← hT_fLp]
    have hfLp_cl : fLp ∈ closure (S_exp : Set _) := hfLp_in_exp
    exact closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hT_map u hu)
      (image_closure_subset_closure_image T.continuous ⟨fLp, hfLp_cl, rfl⟩)
  -- Step 4: Extract finite complex combination within `ε`, take real parts of coefficients!
  obtain ⟨u, hu_span, hu_dist⟩ := Metric.mem_closure_iff.mp hfLp_in_odd ε hε
  have hu_span' : u ∈ S_odd := hu_span
  rw [Submodule.mem_span_set] at hu_span'
  obtain ⟨s, hs_sub, rfl⟩ := hu_span'
  classical
  let e : Fin s.support.card ≃ s.support := (Fintype.equivFinOfCardEq (Fintype.card_coe s.support)).symm
  have hchoice : ∀ i : Fin s.support.card, ∃ (βL βR : ℝ) (hL : 0 < βL) (hR : 0 < βR),
      (e i : Lp ℂ 2 volume) = (memLp_spinThermalX_euc hL hR).toLp _ := by
    intro i
    obtain ⟨βL, hβL, βR, hβR, hmem, heq⟩ := hs_sub (e i).2
    exact ⟨βL, βR, hβL, hβR, heq⟩
  choose βL βR hβL hβR hbasis using hchoice
  let cC : Fin s.support.card → ℂ := fun i => s (e i)
  let cR : Fin s.support.card → ℝ := fun i => (cC i).re
  refine ⟨s.support.card, cR, βL, βR, hβL, hβR, ?_⟩
  -- Compare `∫ (∑ cR_i X_i - Φ)² ≤ ∫ ‖∑ cC_i X_i - Φ‖² = dist(fLp, ∑ cC_i X_i)² < ε²`
  have hsum_ae : ∀ᵐ x : RadialSpace 1,
      ((s.sum fun v c => c • v : Lp ℂ 2 volume) : RadialSpace 1 → ℂ) x =
        ∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ) := by
    have hfin : (s.sum fun v c => c • v : Lp ℂ 2 volume) =
        ∑ i : Fin s.support.card, cC i • (memLp_spinThermalX_euc (hβL i) (hβR i)).toLp _ := by
      rw [Finsupp.sum, ← Finset.sum_coe_sort s.support, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [cC]; rw [hbasis i]
    rw [hfin]
    have hcoe_sum : ∀ (F : Finset (Fin s.support.card)),
        ∀ᵐ x : RadialSpace 1,
          ((∑ i ∈ F, cC i • (memLp_spinThermalX_euc (hβL i) (hβR i)).toLp _ : Lp ℂ 2 volume) :
            RadialSpace 1 → ℂ) x =
          ∑ i ∈ F, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ) := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (RadialSpace 1))] with x hx
        simp
      | insert a F ha ih =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add (cC a • (memLp_spinThermalX_euc (hβL a) (hβR a)).toLp _)
            (∑ i ∈ F, cC i • (memLp_spinThermalX_euc (hβL i) (hβR i)).toLp _),
          Lp.coeFn_smul (cC a) ((memLp_spinThermalX_euc (hβL a) (hβR a)).toLp _),
          (memLp_spinThermalX_euc (hβL a) (hβR a)).coeFn_toLp, ih] with x hadd hsmul hto hih
        rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hto, hih, Finset.sum_insert ha]; rfl
    exact hcoe_sum Finset.univ
  have hnorm_sq : (∫ x : RadialSpace 1,
      ‖(∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
        spinToEuc Φ x‖ ^ 2) = dist fLp (s.sum fun v c => c • v) ^ 2 := by
    rw [dist_comm, dist_eq_norm]
    set d : Lp ℂ 2 (volume : Measure (RadialSpace 1)) := (s.sum fun v c => c • v) - fLp
    have hre : ‖d‖ ^ 2 = (@inner ℂ _ _ d d).re := by
      rw [inner_self_eq_norm_sq_to_K, ← map_pow]; exact (Complex.ofReal_re _).symm
    rw [hre, L2.inner_def]
    have hsub_ae : ∀ᵐ x : RadialSpace 1,
        (d : RadialSpace 1 → ℂ) x =
          (∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
            spinToEuc Φ x := by
      filter_upwards [Lp.coeFn_sub (s.sum fun v c => c • v) fLp, hsum_ae, hΦ_memLp.coeFn_toLp]
        with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have hint_in : Integrable (fun x : RadialSpace 1 =>
        @inner ℂ _ _ ((d : RadialSpace 1 → ℂ) x) ((d : RadialSpace 1 → ℂ) x)) volume :=
      L2.integrable_inner d d
    have hre_int : (∫ x : RadialSpace 1,
        @inner ℂ _ _ ((d : RadialSpace 1 → ℂ) x) ((d : RadialSpace 1 → ℂ) x)).re =
        ∫ x : RadialSpace 1,
          (@inner ℂ _ _ ((d : RadialSpace 1 → ℂ) x) ((d : RadialSpace 1 → ℂ) x)).re :=
      (Complex.reCLM.integral_comp_comm hint_in).symm
    rw [hre_int]
    refine integral_congr_ae ?_
    filter_upwards [hsub_ae] with x hx
    rw [inner_self_eq_norm_sq_to_K, hx, ← map_pow]; exact (Complex.ofReal_re _).symm
  have hre_le : ∀ x : RadialSpace 1,
      ((∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1)) ^ 2 ≤
      ‖(∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
        spinToEuc Φ x‖ ^ 2 := by
    intro x
    have hre_eq : ((∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
        spinToEuc Φ x).re =
        (∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1) := by
      simp [cR, spinToEuc]
    rw [← hre_eq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hint_R : Integrable (fun x : RadialSpace 1 =>
      ((∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1)) ^ 2) := by
    have hmem_R : MemLp (fun x : RadialSpace 1 =>
        (∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1)) 2 volume := by
      have h1 : MemLp (fun x : RadialSpace 1 =>
          ∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) 2 volume := by
        have hterm : ∀ i : Fin s.support.card,
            MemLp (fun x : RadialSpace 1 => cR i * spinThermalX_euc (βL i) (βR i) x) 2 volume := by
          intro i
          have hc := (memLp_spinThermalX_euc (hβL i) (hβR i)).re
          exact hc.const_mul (cR i)
        exact memLp_finset_sum_aux Finset.univ _ fun i _ => hterm i
      have h2 : MemLp (fun x : RadialSpace 1 => Φ (x 0, x 1)) 2 volume := hΦ_memLp.re
      exact h1.sub h2
    simpa [Real.norm_eq_abs, sq_abs] using hmem_R.integrable_sq
  have hint_C : Integrable (fun x : RadialSpace 1 =>
      ‖(∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
        spinToEuc Φ x‖ ^ 2) := by
    have hsub_ae : ∀ᵐ x : RadialSpace 1,
        (((s.sum fun v c => c • v) - fLp : Lp ℂ 2 volume) : RadialSpace 1 → ℂ) x =
          (∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
            spinToEuc Φ x := by
      filter_upwards [Lp.coeFn_sub (s.sum fun v c => c • v) fLp, hsum_ae, hΦ_memLp.coeFn_toLp]
        with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    exact ((Lp.memLp ((s.sum fun v c => c • v) - fLp)).ae_eq hsub_ae).norm.integrable_sq
  calc ∫ x : RadialSpace 1,
        ((∑ i : Fin s.support.card, cR i * spinThermalX_euc (βL i) (βR i) x) - Φ (x 0, x 1)) ^ 2
      ≤ ∫ x : RadialSpace 1,
        ‖(∑ i : Fin s.support.card, cC i * (spinThermalX_euc (βL i) (βR i) x : ℂ)) -
          spinToEuc Φ x‖ ^ 2 := integral_mono hint_R hint_C hre_le
    _ = dist fLp (s.sum fun v c => c • v) ^ 2 := hnorm_sq
    _ < ε ^ 2 := by
        have hd_nn : 0 ≤ dist fLp (s.sum fun v c => c • v) := dist_nonneg
        nlinarith

/-! ### Section 2: Exact Mehler action on `spinThermalX_euc` and Mehler crossing equality -/

/-- Exact 1D Mehler action on `u ↦ exp(-π β u²)`:
`∫ K_r(x, u) exp(-π β u²) du = √(2 / (1 + r + β (1 - r))) exp(-π β'(r, β) x²)`. -/
private lemma spinMehler1D_exp_sq {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 < β) (x : ℝ) :
    (∫ u : ℝ, spinMehlerKernel1D r x u * Real.exp (-π * β * u ^ 2)) =
      Real.sqrt (2 / (1 + r + β * (1 - r))) *
        Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * x ^ 2) := by
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hD : 0 < 1 + r + β * (1 - r) := by positivity
  set A : ℝ := π * (1 + r + β * (1 - r)) / (1 - r)
  have hA_pos : 0 < A := by positivity
  have hpt : ∀ u : ℝ, spinMehlerKernel1D r x u * Real.exp (-π * β * u ^ 2) =
      (Real.sqrt (2 / (1 - r)) *
        Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * x ^ 2)) *
        Real.exp (-A * (u - (2 * Real.sqrt r / (1 + r + β * (1 - r))) * x) ^ 2) := by
    intro u
    unfold spinMehlerKernel1D
    rw [mul_assoc (Real.sqrt _), ← Real.exp_add, mul_assoc (Real.sqrt _), ← Real.exp_add]
    congr 2
    dsimp [A]
    have h1rp : (1 + r) ≠ 0 := by linarith
    have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0
    field_simp [h1r.ne', h1rp, hD.ne']
    ring_nf
    rw [hsq]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub_right_eq_self (fun u => Real.exp (-A * u ^ 2)),
      integral_gaussian A]
  have hsqrt : Real.sqrt (2 / (1 - r)) * Real.sqrt (π / A) =
      Real.sqrt (2 / (1 + r + β * (1 - r))) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; dsimp [A]; field_simp [Real.pi_pos.ne', h1r.ne', hD.ne']
  calc Real.sqrt (2 / (1 - r)) *
        Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * x ^ 2) *
        Real.sqrt (π / A)
      = (Real.sqrt (2 / (1 - r)) * Real.sqrt (π / A)) *
        Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * x ^ 2) := by ring
    _ = Real.sqrt (2 / (1 + r + β * (1 - r))) *
        Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * x ^ 2) := by rw [hsqrt]

/-- Exact 2D Mehler action on `spinThermalX_euc βL βR`:
`mehlerMean 1 r (spinThermalX_euc βL βR) x = c * spinThermalX_euc βL' βR' x`. -/
private lemma mehlerMean_spinThermalX_euc {r βL βR : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hβL : 0 < βL) (hβR : 0 < βR) (x : RadialSpace 1) :
    mehlerMean 1 r (spinThermalX_euc βL βR) x =
      (Real.sqrt (2 / (1 + r + βL * (1 - r))) * Real.sqrt (2 / (1 + r + βR * (1 - r)))) *
        spinThermalX_euc
          ((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r)))
          ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r))) x := by
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hDL : 0 < 1 + r + βL * (1 - r) := by positivity
  have hDR : 0 < 1 + r + βR * (1 - r) := by positivity
  have hNL : 0 < 1 - r + βL * (1 + r) := by positivity
  have hNR : 0 < 1 - r + βR * (1 + r) := by positivity
  -- Helper: `mehlerMean 1 r (fun y => exp(-π (γL (y 0)² + γR (y 1)²))) x`
  have hgauss : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      (∫ y : RadialSpace 1, mehlerKernel 1 r x y *
        Real.exp (-π * (γL * (y 0) ^ 2 + γR * (y 1) ^ 2))) =
      (Real.sqrt (2 / (1 + r + γL * (1 - r))) * Real.sqrt (2 / (1 + r + γR * (1 - r)))) *
        Real.exp (-π * (((1 - r + γL * (1 + r)) / (1 + r + γL * (1 - r))) * (x 0) ^ 2 +
          ((1 - r + γR * (1 + r)) / (1 + r + γR * (1 - r))) * (x 1) ^ 2)) := by
    intro γL γR hγL hγR
    have hchg : (∫ y : RadialSpace 1, mehlerKernel 1 r x y *
          Real.exp (-π * (γL * (y 0) ^ 2 + γR * (y 1) ^ 2))) =
        ∫ q : ℝ × ℝ,
          (spinMehlerKernel1D r (x 0) q.1 * Real.exp (-π * γL * q.1 ^ 2)) *
          (spinMehlerKernel1D r (x 1) q.2 * Real.exp (-π * γR * q.2 ^ 2)) := by
      rw [← wVolume_preserving_e2ToProd.integral_comp'
        (g := fun q : ℝ × ℝ =>
          (spinMehlerKernel1D r (x 0) q.1 * Real.exp (-π * γL * q.1 ^ 2)) *
          (spinMehlerKernel1D r (x 1) q.2 * Real.exp (-π * γR * q.2 ^ 2)))]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only [wE2ToProd_apply]
      have hK := spinMehlerKernel1D_prod_eq_mehlerKernel hr0 hr1 (x 0, x 1) (y 0, y 1)
      have hx_e : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, x 1] = x := by
        ext i; fin_cases i <;> rfl
      have hy_e : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0, y 1] = y := by
        ext i; fin_cases i <;> rfl
      rw [hx_e, hy_e] at hK
      rw [← hK]
      have hexp : Real.exp (-π * (γL * (y 0) ^ 2 + γR * (y 1) ^ 2)) =
          Real.exp (-π * γL * (y 0) ^ 2) * Real.exp (-π * γR * (y 1) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]; ring
    rw [hchg, Measure.volume_eq_prod, integral_prod_mul
      (fun u => spinMehlerKernel1D r (x 0) u * Real.exp (-π * γL * u ^ 2))
      (fun v => spinMehlerKernel1D r (x 1) v * Real.exp (-π * γR * v ^ 2)),
      spinMehler1D_exp_sq hr0 hr1 hγL (x 0), spinMehler1D_exp_sq hr0 hr1 hγR (x 1)]
    have hexp : Real.exp (-π * ((1 - r + γL * (1 + r)) / (1 + r + γL * (1 - r))) * (x 0) ^ 2) *
        Real.exp (-π * ((1 - r + γR * (1 + r)) / (1 + r + γR * (1 - r))) * (x 1) ^ 2) =
        Real.exp (-π * (((1 - r + γL * (1 + r)) / (1 + r + γL * (1 - r))) * (x 0) ^ 2 +
          ((1 - r + γR * (1 + r)) / (1 + r + γR * (1 - r))) * (x 1) ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.sqrt (2 / (1 + r + γL * (1 - r))) *
          Real.exp (-π * ((1 - r + γL * (1 + r)) / (1 + r + γL * (1 - r))) * (x 0) ^ 2) *
          (Real.sqrt (2 / (1 + r + γR * (1 - r))) *
          Real.exp (-π * ((1 - r + γR * (1 + r)) / (1 + r + γR * (1 - r))) * (x 1) ^ 2))
        = (Real.sqrt (2 / (1 + r + γL * (1 - r))) * Real.sqrt (2 / (1 + r + γR * (1 - r)))) *
          (Real.exp (-π * ((1 - r + γL * (1 + r)) / (1 + r + γL * (1 - r))) * (x 0) ^ 2) *
           Real.exp (-π * ((1 - r + γR * (1 + r)) / (1 + r + γR * (1 - r))) * (x 1) ^ 2)) := by ring
      _ = _ := by rw [hexp]
  -- Split `spinThermalX_euc` into its two Gaussian terms
  have hk_int := (integral_mehlerKernel 1 hr0 hr1 x).1
  have hint_g : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR →
      Integrable (fun y : RadialSpace 1 =>
        mehlerKernel 1 r x y * Real.exp (-π * (γL * (y 0) ^ 2 + γR * (y 1) ^ 2))) := by
    intro γL γR hγL hγR
    refine hk_int.mono' ?_ (Eventually.of_forall fun y => ?_)
    · have h0 : Continuous (fun y : RadialSpace 1 => y 0) :=
        (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      have h1 : Continuous (fun y : RadialSpace 1 => y 1) :=
        (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      exact (((continuous_mehlerKernel 1 r).comp (Continuous.prodMk continuous_const continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul
          ((continuous_const.mul (h0.pow 2)).add (continuous_const.mul (h1.pow 2)))))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg 1 hr1 x y) (Real.exp_pos _).le)]
      have hpos_arg : 0 ≤ γL * (y 0) ^ 2 + γR * (y 1) ^ 2 := by positivity
      have he1 : Real.exp (-π * (γL * (y 0) ^ 2 + γR * (y 1) ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      exact mul_le_of_le_one_right (mehlerKernel_nonneg 1 hr1 x y) he1
  have hsplit : (fun y : RadialSpace 1 => mehlerKernel 1 r x y * spinThermalX_euc βL βR y) =
      fun y => mehlerKernel 1 r x y * Real.exp (-π * (βL * (y 0) ^ 2 + βR * (y 1) ^ 2)) -
        (βL * βR) ^ (-(1 / 2 : ℝ)) *
          (mehlerKernel 1 r x y * Real.exp (-π * (βL⁻¹ * (y 0) ^ 2 + βR⁻¹ * (y 1) ^ 2))) := by
    ext y
    unfold spinThermalX_euc spinThermalX
    have h1 : -2 * π * (βL * ((y 0) ^ 2 / 2) + βR * ((y 1) ^ 2 / 2)) =
        -π * (βL * (y 0) ^ 2 + βR * (y 1) ^ 2) := by ring
    have h2 : -2 * π * ((y 0) ^ 2 / 2 / βL + (y 1) ^ 2 / 2 / βR) =
        -π * (βL⁻¹ * (y 0) ^ 2 + βR⁻¹ * (y 1) ^ 2) := by field_simp [hβL.ne', hβR.ne']
    rw [h1, h2]; ring
  unfold mehlerMean
  rw [hsplit, integral_sub (hint_g hβL hβR) ((hint_g (inv_pos.mpr hβL) (inv_pos.mpr hβR)).const_mul _),
      integral_const_mul, hgauss hβL hβR, hgauss (inv_pos.mpr hβL) (inv_pos.mpr hβR)]
  -- Match the second term's prefactor and exponent with `βL'⁻¹, βR'⁻¹`
  have hinv_exp : ∀ {β : ℝ}, 0 < β →
      (1 - r + β⁻¹ * (1 + r)) / (1 + r + β⁻¹ * (1 - r)) =
        ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r)))⁻¹ := by
    intro β hβ
    rw [inv_div]; field_simp [hβ.ne']; ring
  have hinv_pref : (βL * βR) ^ (-(1 / 2 : ℝ)) *
      (Real.sqrt (2 / (1 + r + βL⁻¹ * (1 - r))) * Real.sqrt (2 / (1 + r + βR⁻¹ * (1 - r)))) =
      (Real.sqrt (2 / (1 + r + βL * (1 - r))) * Real.sqrt (2 / (1 + r + βR * (1 - r)))) *
        (((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r))) *
         ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r)))) ^ (-(1 / 2 : ℝ)) := by
    have h1 : ∀ {β : ℝ}, 0 < β →
        β ^ (-(1 / 2 : ℝ)) * Real.sqrt (2 / (1 + r + β⁻¹ * (1 - r))) =
          Real.sqrt (2 / (1 + r + β * (1 - r))) *
            ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) ^ (-(1 / 2 : ℝ)) := by
      intro β hβ
      have hD' : 0 < 1 + r + β * (1 - r) := by positivity
      have hN' : 0 < 1 - r + β * (1 + r) := by positivity
      rw [Real.rpow_neg hβ.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv,
          ← Real.sqrt_mul (inv_nonneg.mpr hβ.le),
          Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv,
          ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp [hβ.ne', hD'.ne', hN'.ne']; ring
    rw [Real.mul_rpow hβL.le hβR.le,
        Real.mul_rpow (div_nonneg hNL.le hDL.le) (div_nonneg hNR.le hDR.le)]
    calc βL ^ (-(1 / 2 : ℝ)) * βR ^ (-(1 / 2 : ℝ)) *
          (Real.sqrt (2 / (1 + r + βL⁻¹ * (1 - r))) * Real.sqrt (2 / (1 + r + βR⁻¹ * (1 - r))))
        = (βL ^ (-(1 / 2 : ℝ)) * Real.sqrt (2 / (1 + r + βL⁻¹ * (1 - r)))) *
          (βR ^ (-(1 / 2 : ℝ)) * Real.sqrt (2 / (1 + r + βR⁻¹ * (1 - r)))) := by ring
      _ = (Real.sqrt (2 / (1 + r + βL * (1 - r))) *
            ((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r))) ^ (-(1 / 2 : ℝ))) *
          (Real.sqrt (2 / (1 + r + βR * (1 - r))) *
            ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r))) ^ (-(1 / 2 : ℝ))) := by
          rw [h1 hβL, h1 hβR]
      _ = _ := by ring
  rw [hinv_exp hβL, hinv_exp hβR, ← mul_assoc, hinv_pref]
  unfold spinThermalX_euc spinThermalX
  have he1 : -2 * π * (((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r))) * ((x 0) ^ 2 / 2) +
      ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r))) * ((x 1) ^ 2 / 2)) =
      -π * (((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r))) * (x 0) ^ 2 +
        ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r))) * (x 1) ^ 2) := by ring
  have he2 : -2 * π * ((x 0) ^ 2 / 2 / ((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r))) +
      (x 1) ^ 2 / 2 / ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r)))) =
      -π * (((1 - r + βL * (1 + r)) / (1 + r + βL * (1 - r)))⁻¹ * (x 0) ^ 2 +
        ((1 - r + βR * (1 + r)) / (1 + r + βR * (1 - r)))⁻¹ * (x 1) ^ 2) := by
    simp only [div_eq_mul_inv]; ring
  rw [he1, he2]; ring

/-- Lift of a quadrant measure `meas.ν` to `RadialSpace 1` via `(t_L, t_R) ↦ (√(2 t_L), √(2 t_R))`. -/
private noncomputable def spinSqrtEucMap (p : ℝ × ℝ) : RadialSpace 1 :=
  wE2ToProd.symm (Real.sqrt (2 * p.1), Real.sqrt (2 * p.2))

private lemma measurable_spinSqrtEucMap : Measurable spinSqrtEucMap :=
  wE2ToProd.symm.measurable.comp
    ((Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)).measurable.prodMk
     (Real.continuous_sqrt.comp (continuous_const.mul continuous_snd)).measurable)

/-- Cardy product measure `ρ_e` on `RadialSpace 1` with density `V_1(x 0) * V_1(x 1)`. -/
private noncomputable def spinCardyEucMeasure (a : ℝ) : Measure (RadialSpace 1) :=
  volume.withDensity (fun x : RadialSpace 1 => ENNReal.ofReal (spinV1 a (x 0) * spinV1 a (x 1)))

private lemma spinCardyEucMeasure_integral {a : ℝ} (ha : 2 ≤ a) (f : RadialSpace 1 → ℝ) :
    ∫ x : RadialSpace 1, f x ∂(spinCardyEucMeasure a) =
      ∫ p : ℝ × ℝ, f (wE2ToProd.symm p) * spinV1 a p.1 * spinV1 a p.2 := by
  unfold spinCardyEucMeasure
  have hmeas_V : Measurable (fun x : RadialSpace 1 =>
      ENNReal.ofReal (spinV1 a (x 0) * spinV1 a (x 1))) := by
    have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact ENNReal.measurable_ofReal.comp
      ((hV.comp ((continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous)).measurable.mul
       (hV.comp ((continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous)).measurable)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas_V
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← wVolume_preserving_e2ToProd.integral_comp'
    (g := fun p : ℝ × ℝ => f (wE2ToProd.symm p) * spinV1 a p.1 * spinV1 a p.2)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (mul_nonneg (spinV1_nonneg ha _) (spinV1_nonneg ha _)),
      smul_eq_mul, MeasurableEquiv.symm_apply_apply, wE2ToProd_apply]
  ring

private lemma spinCardyEucMeasure_integrable_iff {a : ℝ} (ha : 2 ≤ a) {f : RadialSpace 1 → ℝ} :
    Integrable f (spinCardyEucMeasure a) ↔
      Integrable (fun p : ℝ × ℝ => f (wE2ToProd.symm p) * spinV1 a p.1 * spinV1 a p.2) := by
  unfold spinCardyEucMeasure
  have hmeas_V : Measurable (fun x : RadialSpace 1 =>
      ENNReal.ofReal (spinV1 a (x 0) * spinV1 a (x 1))) := by
    have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    exact ENNReal.measurable_ofReal.comp
      ((hV.comp ((continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous)).measurable.mul
       (hV.comp ((continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous)).measurable)
  rw [integrable_withDensity_iff_integrable_smul₀' hmeas_V.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun x : RadialSpace 1 =>
        (ENNReal.ofReal (spinV1 a (x 0) * spinV1 a (x 1))).toReal • f x) =
      (fun p : ℝ × ℝ => f (wE2ToProd.symm p) * spinV1 a p.1 * spinV1 a p.2) ∘ wE2ToProd := by
    ext x; dsimp only [Function.comp]
    rw [ENNReal.toReal_ofReal (mul_nonneg (spinV1_nonneg ha _) (spinV1_nonneg ha _)),
        smul_eq_mul, MeasurableEquiv.symm_apply_apply, wE2ToProd_apply]; ring
  rw [heq]
  exact wVolume_preserving_e2ToProd.integrable_comp_emb wE2ToProd.measurableEmbedding

/-- Mehler crossing equality for every `Φ ∈ SpinTestClass a` (`a ≥ 2`) and `r ∈ (0, 1)`. -/
private theorem spinMehler_crossing_eq {a : ℝ} (ha : 2 ≤ a) (meas : SpinCrossingMeasure a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    let ν_e : Measure (RadialSpace 1) := meas.ν.map spinSqrtEucMap
    let ρ_e : Measure (RadialSpace 1) := spinCardyEucMeasure a
    let f : RadialSpace 1 → ℝ := fun x => Φ (x 0, x 1)
    Integrable (fun x => mehlerMean 1 r f x) ν_e ∧
    Integrable (fun x => mehlerMean 1 r f x) ρ_e ∧
    (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) =
      ∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e := by
  intro ν_e ρ_e f
  -- Gaussian integrability of `ν_e` and `ρ_e`
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace 1 => Real.exp (-ε * ‖x‖ ^ 2)) ν_e := by
    intro ε hε
    rw [integrable_map_measure (by fun_prop : Continuous fun x : RadialSpace 1 =>
      Real.exp (-ε * ‖x‖ ^ 2)).aestronglyMeasurable measurable_spinSqrtEucMap.aemeasurable]
    have hae_q : ∀ᵐ p ∂meas.ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
      have : ∀ᵐ p ∂meas.ν, p ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 meas.supp_quad
      filter_upwards [this] with p hp using not_not.mp hp
    refine (meas.finite_laplace (by positivity : 0 < ε / π)).congr ?_
    filter_upwards [hae_q] with p ⟨hp1, hp2⟩
    dsimp [Function.comp, spinSqrtEucMap]
    have hnorm : ‖wE2ToProd.symm (Real.sqrt (2 * p.1), Real.sqrt (2 * p.2))‖ ^ 2 =
        2 * p.1 + 2 * p.2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, wE2ToProd_symm_apply_zero,
        wE2ToProd_symm_apply_one]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt hp1, Real.sq_sqrt hp2]
    rw [hnorm]; congr 1; field_simp [Real.pi_pos.ne']
  have hρ_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace 1 => Real.exp (-ε * ‖x‖ ^ 2)) ρ_e := by
    intro ε hε
    rw [spinCardyEucMeasure_integrable_iff ha]
    have hdom : Integrable (fun p : ℝ × ℝ =>
        (Real.exp (-ε * p.1 ^ 2 + 2 * π * Real.sqrt a * |p.1|)) *
        (Real.exp (-ε * p.2 ^ 2 + 2 * π * Real.sqrt a * |p.2|))) := by
      rw [Measure.volume_eq_prod]
      have h1D : Integrable (fun u : ℝ => Real.exp (-ε * u ^ 2 + 2 * π * Real.sqrt a * |u|)) := by
        have h1 : Integrable (fun u : ℝ => Real.exp (-ε * u ^ 2 + 2 * π * Real.sqrt a * u)) := by
          have hc : ∀ u, Real.exp (-ε * u ^ 2 + 2 * π * Real.sqrt a * u) =
              Real.exp ((2 * π * Real.sqrt a) ^ 2 / (4 * ε)) *
                Real.exp (-ε * (u - 2 * π * Real.sqrt a / (2 * ε)) ^ 2) := by
            intro u; rw [← Real.exp_add]; congr 1; field_simp [hε.ne']; ring
          simp_rw [hc]; exact ((integrable_exp_neg_mul_sq hε).comp_sub_right _).const_mul _
        have h2 : Integrable (fun u : ℝ => Real.exp (-ε * u ^ 2 - 2 * π * Real.sqrt a * u)) := by
          have hc : ∀ u, Real.exp (-ε * u ^ 2 - 2 * π * Real.sqrt a * u) =
              Real.exp ((2 * π * Real.sqrt a) ^ 2 / (4 * ε)) *
                Real.exp (-ε * (u + 2 * π * Real.sqrt a / (2 * ε)) ^ 2) := by
            intro u; rw [← Real.exp_add]; congr 1; field_simp [hε.ne']; ring
          simp_rw [hc]; exact ((integrable_exp_neg_mul_sq hε).comp_add_right _).const_mul _
        refine (h1.add h2).mono' (by fun_prop : Continuous fun u : ℝ =>
          Real.exp (-ε * u ^ 2 + 2 * π * Real.sqrt a * |u|)).aestronglyMeasurable
          (Eventually.of_forall fun u => ?_)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; dsimp [Pi.add_apply]
        rcases le_total 0 u with hu | hu
        · rw [abs_of_nonneg hu]; linarith [Real.exp_pos (-ε * u ^ 2 - 2 * π * Real.sqrt a * u)]
        · rw [abs_of_nonpos hu]
          have : -ε * u ^ 2 + 2 * π * Real.sqrt a * -u = -ε * u ^ 2 - 2 * π * Real.sqrt a * u := by ring
          rw [this]; linarith [Real.exp_pos (-ε * u ^ 2 + 2 * π * Real.sqrt a * u)]
      exact h1D.mul_prod h1D
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hV : Continuous (spinV1 a) := by unfold spinV1; fun_prop
      have hnorm : Continuous (fun p : ℝ × ℝ => ‖wE2ToProd.symm p‖ ^ 2) := by
        have heq : (fun p : ℝ × ℝ => ‖wE2ToProd.symm p‖ ^ 2) = fun p => p.1 ^ 2 + p.2 ^ 2 := by
          ext p; rw [EuclideanSpace.norm_sq_eq]
          simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one]
        rw [heq]; fun_prop
      exact (((Real.continuous_exp.comp (continuous_const.mul hnorm)).mul
        (hV.comp continuous_fst)).mul (hV.comp continuous_snd)).aestronglyMeasurable
    · have hnorm : ‖wE2ToProd.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one]
      rw [hnorm, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (spinV1_nonneg ha p.1))
        (spinV1_nonneg ha p.2))]
      have hV1 := spinV1_le_exp ha p.1
      have hV2 := spinV1_le_exp ha p.2
      have hle : Real.exp (-ε * (p.1 ^ 2 + p.2 ^ 2)) * spinV1 a p.1 * spinV1 a p.2 ≤
          Real.exp (-ε * (p.1 ^ 2 + p.2 ^ 2)) * Real.exp (2 * π * Real.sqrt a * |p.1|) *
            Real.exp (2 * π * Real.sqrt a * |p.2|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hV1 (Real.exp_pos _).le) hV2 (spinV1_nonneg ha p.2) (by positivity)
      refine hle.trans_eq ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  -- Boundedness and continuity of `f`
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  have hf_cont : Continuous f := hΦ.cont.comp wE2ToProd_continuous
  have hf_bd : ∀ x : RadialSpace 1, |f x| ≤ C₀ * spinM2 a Φ := fun x => hΦ_inf (x 0, x 1)
  have hf_int_ν : Integrable (fun x => mehlerMean 1 r f x) ν_e :=
    integrable_mehlerMean_of_bounded hν_gauss hf_cont hf_bd hr0.le hr1
  have hf_int_ρ : Integrable (fun x => mehlerMean 1 r f x) ρ_e :=
    integrable_mehlerMean_of_bounded hρ_gauss hf_cont hf_bd hr0.le hr1
  refine ⟨hf_int_ν, hf_int_ρ, ?_⟩
  -- Thermal crossing equality `∫ spinThermalX_euc βL βR dν_e = ∫ spinThermalX_euc βL βR dρ_e`
  have h_therm_eq : ∀ {βL βR : ℝ}, 0 < βL → 0 < βR →
      (∫ x : RadialSpace 1, spinThermalX_euc βL βR x ∂ν_e) =
        ∫ x : RadialSpace 1, spinThermalX_euc βL βR x ∂ρ_e := by
    intro βL βR hβL hβR
    have hcont_X : Continuous (spinThermalX_euc βL βR) := by
      unfold spinThermalX_euc spinThermalX
      have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
        (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
        (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      fun_prop
    have hL : (∫ x : RadialSpace 1, spinThermalX_euc βL βR x ∂ν_e) = -spinThermalXVac a βL βR := by
      unfold ν_e
      rw [integral_map measurable_spinSqrtEucMap.aemeasurable hcont_X.aestronglyMeasurable]
      have hae_q : ∀ᵐ p ∂meas.ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
        have : ∀ᵐ p ∂meas.ν, p ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ :=
          measure_eq_zero_iff_ae_notMem.1 meas.supp_quad
        filter_upwards [this] with p hp using not_not.mp hp
      rw [← meas.crossing hβL hβR]
      refine integral_congr_ae ?_
      filter_upwards [hae_q] with p ⟨hp1, hp2⟩
      dsimp [spinThermalX_euc, spinSqrtEucMap]
      rw [wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one,
          Real.sq_sqrt (by linarith : 0 ≤ 2 * p.1), Real.sq_sqrt (by linarith : 0 ≤ 2 * p.2)]
      ring_nf
    have hR : (∫ x : RadialSpace 1, spinThermalX_euc βL βR x ∂ρ_e) = -spinThermalXVac a βL βR := by
      rw [spinCardyEucMeasure_integral ha]
      have hvac := spinVacT_thermalX ha hβL hβR
      unfold spinVacT spinPhiVac spinLiftTToR at hvac
      have heq : (fun p : ℝ × ℝ => spinThermalX_euc βL βR (wE2ToProd.symm p) * spinV1 a p.1 * spinV1 a p.2) =
          fun p => spinThermalX βL βR (p.1 ^ 2 / 2) (p.2 ^ 2 / 2) * spinV1 a p.1 * spinV1 a p.2 := by
        ext p; simp [spinThermalX_euc, wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one]
      rw [heq]; linarith
    rw [hL, hR]
  -- Now prove `|∫ A_r f dν_e - ∫ A_r f dρ_e| = 0` by `L²` approximation!
  have hdiff_le : ∀ ε > 0,
      |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
       (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e)| ≤
        (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) *
          ((∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂ν_e) +
           (∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂ρ_e))) * ε := by
    intro ε hε
    obtain ⟨N, c, βL, βR, hβL, hβR, hL2⟩ := exists_spinThermalX_approx_L2 ha hΦ hε
    let h : RadialSpace 1 → ℝ := fun x => ∑ i : Fin N, c i * spinThermalX_euc (βL i) (βR i) x
    have hh_cont : Continuous h := by
      have h0 : Continuous (fun x : RadialSpace 1 => x 0) :=
        (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      have h1 : Continuous (fun x : RadialSpace 1 => x 1) :=
        (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
      have hX_c : ∀ i : Fin N, Continuous (fun x : RadialSpace 1 => c i * spinThermalX_euc (βL i) (βR i) x) := by
        intro i; unfold spinThermalX_euc spinThermalX; fun_prop
      exact continuous_finset_sum_aux Finset.univ _ (fun i _ => hX_c i)
    have hX_bd : ∀ {γL γR : ℝ}, 0 < γL → 0 < γR → ∀ x : RadialSpace 1,
        |spinThermalX_euc γL γR x| ≤ 1 + (γL * γR) ^ (-(1 / 2 : ℝ)) := by
      intro γL γR hγL hγR x
      unfold spinThermalX_euc spinThermalX
      have hpos1 : 0 ≤ γL * ((x 0) ^ 2 / 2) + γR * ((x 1) ^ 2 / 2) := by positivity
      have he1 : Real.exp (-2 * π * (γL * ((x 0) ^ 2 / 2) + γR * ((x 1) ^ 2 / 2))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      have he2 : Real.exp (-2 * π * ((x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have : 0 ≤ (x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR := by positivity
          nlinarith [Real.pi_pos])
      have htri := abs_sub (Real.exp (-2 * π * (γL * ((x 0) ^ 2 / 2) + γR * ((x 1) ^ 2 / 2))))
        ((γL * γR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * ((x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR)))
      rw [abs_of_pos (Real.exp_pos _), abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (mul_pos hγL hγR).le _),
          abs_of_pos (Real.exp_pos _)] at htri
      have h2 : (γL * γR) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-2 * π * ((x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR)) ≤
          (γL * γR) ^ (-(1 / 2 : ℝ)) :=
        mul_le_of_le_one_right (Real.rpow_nonneg (mul_pos hγL hγR).le _) he2
      linarith
    set Bh : ℝ := ∑ i : Fin N, |c i| * (1 + (βL i * βR i) ^ (-(1 / 2 : ℝ)))
    have hh_bd : ∀ x : RadialSpace 1, |h x| ≤ Bh := by
      intro x
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hX_bd (hβL i) (hβR i) x) (abs_nonneg _)
    have hh_int_ν : Integrable (fun x => mehlerMean 1 r h x) ν_e :=
      integrable_mehlerMean_of_bounded hν_gauss hh_cont hh_bd hr0.le hr1
    have hh_int_ρ : Integrable (fun x => mehlerMean 1 r h x) ρ_e :=
      integrable_mehlerMean_of_bounded hρ_gauss hh_cont hh_bd hr0.le hr1
    -- Exact crossing for `mehlerMean 1 r h`
    have hh_cross : (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ν_e) =
        ∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ρ_e := by
      have hAr_sum : ∀ x : RadialSpace 1, mehlerMean 1 r h x =
          ∑ i : Fin N, (c i *
            (Real.sqrt (2 / (1 + r + βL i * (1 - r))) * Real.sqrt (2 / (1 + r + βR i * (1 - r))))) *
            spinThermalX_euc
              ((1 - r + βL i * (1 + r)) / (1 + r + βL i * (1 - r)))
              ((1 - r + βR i * (1 + r)) / (1 + r + βR i * (1 - r))) x := by
        intro x
        unfold mehlerMean h
        have hmul_sum : (fun y : RadialSpace 1 => mehlerKernel 1 r x y *
              ∑ i : Fin N, c i * spinThermalX_euc (βL i) (βR i) y) =
            fun y => ∑ i : Fin N, c i * (mehlerKernel 1 r x y * spinThermalX_euc (βL i) (βR i) y) := by
          ext y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        rw [hmul_sum, integral_finset_sum_aux]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul, ← mehlerMean,
              mehlerMean_spinThermalX_euc hr0.le hr1 (hβL i) (hβR i) x]; ring
        · intro i _
          have hk := (integral_mehlerKernel 1 hr0.le hr1 x).1
          refine (hk.const_mul (|c i| * (1 + (βL i * βR i) ^ (-(1 / 2 : ℝ))))).mono' ?_
            (Eventually.of_forall fun y => ?_)
          · have hX_c : Continuous (spinThermalX_euc (βL i) (βR i)) := by
              unfold spinThermalX_euc spinThermalX
              have h0 : Continuous (fun y : RadialSpace 1 => y 0) :=
                (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
              have h1 : Continuous (fun y : RadialSpace 1 => y 1) :=
                (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
              fun_prop
            exact (continuous_const.mul
              (((continuous_mehlerKernel 1 r).comp (Continuous.prodMk continuous_const continuous_id)).mul
                hX_c)).aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg 1 hr1 x y)]
            have h1 := mul_le_mul_of_nonneg_left (hX_bd (hβL i) (hβR i) y)
              (mul_nonneg (abs_nonneg (c i)) (mehlerKernel_nonneg 1 hr1 x y))
            linarith
      simp_rw [hAr_sum]
      have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
      have hint_term : ∀ (μ : Measure (RadialSpace 1)),
          (∀ {δ : ℝ}, 0 < δ → Integrable (fun x : RadialSpace 1 => Real.exp (-δ * ‖x‖ ^ 2)) μ) →
          ∀ i : Fin N, Integrable (fun x : RadialSpace 1 =>
            (c i * (Real.sqrt (2 / (1 + r + βL i * (1 - r))) * Real.sqrt (2 / (1 + r + βR i * (1 - r))))) *
              spinThermalX_euc
                ((1 - r + βL i * (1 + r)) / (1 + r + βL i * (1 - r)))
                ((1 - r + βR i * (1 + r)) / (1 + r + βR i * (1 - r))) x) μ := by
        intro μ hμ i
        have hβLi : 0 < βL i := hβL i
        have hβRi : 0 < βR i := hβR i
        set γL : ℝ := (1 - r + βL i * (1 + r)) / (1 + r + βL i * (1 - r))
        set γR : ℝ := (1 - r + βR i * (1 + r)) / (1 + r + βR i * (1 - r))
        have hγL : 0 < γL := div_pos (by positivity) (by positivity)
        have hγR : 0 < γR := div_pos (by positivity) (by positivity)
        set m : ℝ := min (min γL γR) (min γL⁻¹ γR⁻¹)
        have hm : 0 < m := lt_min (lt_min hγL hγR) (lt_min (inv_pos.mpr hγL) (inv_pos.mpr hγR))
        have hX_c : Continuous (spinThermalX_euc γL γR) := by
          unfold spinThermalX_euc spinThermalX
          have h0 : Continuous (fun y : RadialSpace 1 => y 0) :=
            (continuous_apply (0 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
          have h1 : Continuous (fun y : RadialSpace 1 => y 1) :=
            (continuous_apply (1 : Fin 2)).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous
          fun_prop
        refine ((hμ (by positivity : 0 < π * m)).const_mul
          (|c i * (Real.sqrt (2 / (1 + r + βL i * (1 - r))) * Real.sqrt (2 / (1 + r + βR i * (1 - r))))| *
            (1 + (γL * γR) ^ (-(1 / 2 : ℝ))))).mono'
          (continuous_const.mul hX_c).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
        have hX_dec : |spinThermalX_euc γL γR x| ≤
            (1 + (γL * γR) ^ (-(1 / 2 : ℝ))) * Real.exp (-(π * m) * ‖x‖ ^ 2) := by
          unfold spinThermalX_euc spinThermalX
          have hmL : m ≤ γL := (min_le_left _ _).trans (min_le_left _ _)
          have hmR : m ≤ γR := (min_le_left _ _).trans (min_le_right _ _)
          have hmLi : m ≤ γL⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
          have hmRi : m ≤ γR⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
          have he1 : Real.exp (-2 * π * (γL * ((x 0) ^ 2 / 2) + γR * ((x 1) ^ 2 / 2))) ≤
              Real.exp (-(π * m) * ‖x‖ ^ 2) := by
            rw [hnorm]; refine Real.exp_le_exp.mpr ?_
            have h1 : m * (x 0) ^ 2 ≤ γL * (x 0) ^ 2 := mul_le_mul_of_nonneg_right hmL (sq_nonneg _)
            have h2 : m * (x 1) ^ 2 ≤ γR * (x 1) ^ 2 := mul_le_mul_of_nonneg_right hmR (sq_nonneg _)
            nlinarith [Real.pi_pos]
          have he2 : Real.exp (-2 * π * ((x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR)) ≤
              Real.exp (-(π * m) * ‖x‖ ^ 2) := by
            rw [hnorm]; refine Real.exp_le_exp.mpr ?_
            have h1 : m * (x 0) ^ 2 ≤ γL⁻¹ * (x 0) ^ 2 := mul_le_mul_of_nonneg_right hmLi (sq_nonneg _)
            have h2 : m * (x 1) ^ 2 ≤ γR⁻¹ * (x 1) ^ 2 := mul_le_mul_of_nonneg_right hmRi (sq_nonneg _)
            have hdiv1 : (x 0) ^ 2 / 2 / γL = γL⁻¹ * (x 0) ^ 2 / 2 := by simp [div_eq_mul_inv]; ring
            have hdiv2 : (x 1) ^ 2 / 2 / γR = γR⁻¹ * (x 1) ^ 2 / 2 := by simp [div_eq_mul_inv]; ring
            rw [hdiv1, hdiv2]; nlinarith [Real.pi_pos]
          have htri := abs_sub (Real.exp (-2 * π * (γL * ((x 0) ^ 2 / 2) + γR * ((x 1) ^ 2 / 2))))
            ((γL * γR) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * ((x 0) ^ 2 / 2 / γL + (x 1) ^ 2 / 2 / γR)))
          rw [abs_of_pos (Real.exp_pos _), abs_mul,
              abs_of_nonneg (Real.rpow_nonneg (mul_pos hγL hγR).le _),
              abs_of_pos (Real.exp_pos _)] at htri
          have h2 := mul_le_mul_of_nonneg_left he2 (Real.rpow_nonneg (mul_pos hγL hγR).le (-(1 / 2 : ℝ)))
          linarith
        have := mul_le_mul_of_nonneg_left hX_dec
          (abs_nonneg (c i * (Real.sqrt (2 / (1 + r + βL i * (1 - r))) *
            Real.sqrt (2 / (1 + r + βR i * (1 - r))))))
        linarith
      rw [integral_finset_sum_aux _ _ (fun i _ => hint_term ν_e hν_gauss i),
          integral_finset_sum_aux _ _ (fun i _ => hint_term ρ_e hρ_gauss i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hβLi : 0 < βL i := hβL i
      have hβRi : 0 < βR i := hβR i
      rw [integral_const_mul, integral_const_mul,
          h_therm_eq (div_pos (by positivity) (by positivity)) (div_pos (by positivity) (by positivity))]
    -- Bound `|∫ (A_r f - A_r h) dμ|` via `abs_mehlerMean_sub_le_of_L2`
    have hL2_int : Integrable (fun x : RadialSpace 1 => (h x - f x) ^ 2) := by
      have hh_m : MemLp h 2 volume := by
        have ht : ∀ i : Fin N, MemLp (fun x : RadialSpace 1 => c i * spinThermalX_euc (βL i) (βR i) x) 2 volume :=
          fun i => (memLp_spinThermalX_euc (hβL i) (hβR i)).re.const_mul (c i)
        exact memLp_finset_sum_aux Finset.univ _ fun i _ => ht i
      have hf_m : MemLp f 2 volume := by
        have hΦ_euc_int' : Integrable (spinToEuc Φ) :=
          (wVolume_preserving_e2ToProd.integrable_comp_of_integrable hΦ.int).ofReal
        have hΦ_m : MemLp (spinToEuc Φ) 2 volume := by
          refine (memLp_two_iff_integrable_sq_norm (Complex.continuous_ofReal.comp hf_cont).aestronglyMeasurable).mpr ?_
          refine (hΦ_euc_int'.norm.const_mul (C₀ * spinM2 a Φ)).mono'
            ((Complex.continuous_ofReal.comp hf_cont).norm.pow 2).aestronglyMeasurable
            (Eventually.of_forall fun x => ?_)
          rw [Real.norm_of_nonneg (sq_nonneg _), sq]
          exact mul_le_mul_of_nonneg_right (by simpa [spinToEuc] using hf_bd x) (norm_nonneg _)
        exact hΦ_m.re
      simpa [Real.norm_eq_abs, sq_abs] using (hh_m.sub hf_m).integrable_sq
    have hpt_L2 : ∀ x : RadialSpace 1,
        |mehlerMean 1 r h x - mehlerMean 1 r f x| ≤
          (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
      intro x
      have h1 := abs_mehlerMean_sub_le_of_L2 (w := 1) hr0.le hr1 hh_cont hf_cont hh_bd hf_bd hε.le
        hL2_int hL2.le x
      have h3 : (-((1 : ℕ) : ℝ) / 2) = -(1 / 2 : ℝ) := by norm_num
      rw [h3] at h1
      linarith
    have hμ_diff : ∀ (μ : Measure (RadialSpace 1)),
        (∀ {δ : ℝ}, 0 < δ → Integrable (fun x : RadialSpace 1 => Real.exp (-δ * ‖x‖ ^ 2)) μ) →
        Integrable (fun x => mehlerMean 1 r f x) μ → Integrable (fun x => mehlerMean 1 r h x) μ →
        |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂μ) -
         (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂μ)| ≤
          (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) *
            ∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂μ := by
      intro μ hμ hf_i hh_i
      rw [← integral_sub hf_i hh_i]
      have hδ : 0 < π * ((1 - r) / (1 + r)) := mul_pos Real.pi_pos (div_pos (sub_pos.mpr hr1) (by linarith))
      have hint_exp : Integrable (fun x : RadialSpace 1 =>
          (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) *
            Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) μ := by
        convert (hμ hδ).const_mul (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) using 1
        ext x; ring_nf
      calc |∫ x : RadialSpace 1, (mehlerMean 1 r f x - mehlerMean 1 r h x) ∂μ|
          ≤ ∫ x : RadialSpace 1, |mehlerMean 1 r f x - mehlerMean 1 r h x| ∂μ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x : RadialSpace 1, (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) *
              Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂μ := by
            refine integral_mono (hf_i.sub hh_i).abs hint_exp fun x => ?_
            rw [abs_sub_comm]; exact hpt_L2 x
        _ = (((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) * ε) *
              ∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂μ :=
            integral_const_mul _ _
    have h1 := hμ_diff ν_e hν_gauss hf_int_ν hh_int_ν
    have h2 := hμ_diff ρ_e hρ_gauss hf_int_ρ hh_int_ρ
    have htri : |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
        (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e)| ≤
        |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
         (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ν_e)| +
        |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e) -
         (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ρ_e)| := by
      have heq : (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
          (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e) =
          ((∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
           (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ν_e)) -
          ((∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e) -
           (∫ x : RadialSpace 1, mehlerMean 1 r h x ∂ρ_e)) := by linarith [hh_cross]
      rw [heq]; exact abs_sub _ _
    linarith
  -- Conclude equality since `ε > 0` is arbitrary
  set D := |(∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ν_e) -
    (∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e)|
  set K := ((1 - r ^ 2) / 2) ^ (-(1 / 2 : ℝ)) *
    ((∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂ν_e) +
     (∫ x : RadialSpace 1, Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ∂ρ_e))
  have hK_nn : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (by nlinarith) _)
    (add_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)
      (integral_nonneg fun _ => (Real.exp_pos _).le))
  have hD0 : D = 0 := by
    by_contra hne
    have hD_pos : 0 < D := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have hle := hdiff_le (D / (2 * (K + 1))) (by positivity)
    have hlt : K * (D / (2 * (K + 1))) < D := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hD0)

/-! ### Section 3: Proof of `SpinDW` (`sd:W`) and `SpinDSD` (`sd:SD`) -/

/-- **`sd:W`** (Proposition SD-W: weak duality and complementary slackness for the full continuous
class `\overline{\mathcal A}_{\rm spin}` on the quadrant), proved unconditionally for all `a ≥ 2`. -/
theorem spinDW : SpinDW := by
  intro a ha meas Φ hΦ T hT hΦ_nn
  let ν_e : Measure (RadialSpace 1) := meas.ν.map spinSqrtEucMap
  let ρ_e : Measure (RadialSpace 1) := spinCardyEucMeasure a
  let f : RadialSpace 1 → ℝ := fun x => Φ (x 0, x 1)
  have hf_cont : Continuous f := hΦ.cont.comp wE2ToProd_continuous
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := spinTestClass_L1_le_M2 ha
  obtain ⟨hΦ_inf, _⟩ := hC₀ hΦ
  set B : ℝ := C₀ * spinM2 a Φ
  have hB_nn : 0 ≤ B := mul_nonneg hC₀_pos.le (spinM2_nonneg ha Φ)
  have hf_bd : ∀ x : RadialSpace 1, |f x| ≤ B := fun x => hΦ_inf (x 0, x 1)
  -- Gaussian integrability of `ν_e`
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace 1 => Real.exp (-ε * ‖x‖ ^ 2)) ν_e := by
    intro ε hε
    rw [integrable_map_measure (by fun_prop : Continuous fun x : RadialSpace 1 =>
      Real.exp (-ε * ‖x‖ ^ 2)).aestronglyMeasurable measurable_spinSqrtEucMap.aemeasurable]
    have hae_q : ∀ᵐ p ∂meas.ν, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
      have : ∀ᵐ p ∂meas.ν, p ∉ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 meas.supp_quad
      filter_upwards [this] with p hp using not_not.mp hp
    refine (meas.finite_laplace (by positivity : 0 < ε / π)).congr ?_
    filter_upwards [hae_q] with p ⟨hp1, hp2⟩
    dsimp [Function.comp, spinSqrtEucMap]
    have hnorm : ‖wE2ToProd.symm (Real.sqrt (2 * p.1), Real.sqrt (2 * p.2))‖ ^ 2 =
        2 * p.1 + 2 * p.2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, wE2ToProd_symm_apply_zero,
        wE2ToProd_symm_apply_one]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt hp1, Real.sq_sqrt hp2]
    rw [hnorm]; congr 1; field_simp [Real.pi_pos.ne']
  -- Split `f = fPlus - fMinus` with `fMinus` supported on `‖x‖ ≤ √(2 T)`
  let fPlus : RadialSpace 1 → ℝ := fun x => max (f x) 0
  let fMinus : RadialSpace 1 → ℝ := fun x => max (-f x) 0
  have hf_split : ∀ x, f x = fPlus x - fMinus x := fun x => by
    dsimp [fPlus, fMinus]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hfPlus_nn : ∀ x, 0 ≤ fPlus x := fun x => le_max_right _ _
  have hfMinus_nn : ∀ x, 0 ≤ fMinus x := fun x => le_max_right _ _
  have hfPlus_cont : Continuous fPlus := hf_cont.max continuous_const
  have hfMinus_cont : Continuous fMinus := hf_cont.neg.max continuous_const
  have hfMinus_bd : ∀ x, fMinus x ≤ B := fun x =>
    max_le ((neg_le_abs _).trans (hf_bd x)) hB_nn
  have hfMinus_abs_bd : ∀ x, |fMinus x| ≤ B := fun x => by
    rw [abs_of_nonneg (hfMinus_nn x)]; exact hfMinus_bd x
  have hfPlus_abs_bd : ∀ x, |fPlus x| ≤ B := fun x => by
    rw [abs_of_nonneg (hfPlus_nn x)]; exact max_le ((le_abs_self _).trans (hf_bd x)) hB_nn
  set R : ℝ := Real.sqrt (2 * T)
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hneg_supp : ∀ y : RadialSpace 1, R < ‖y‖ → fMinus y = 0 := by
    intro y hy
    have hsq : 2 * T < ‖y‖ ^ 2 := by
      have := pow_lt_pow_left₀ hy hR_nn (by norm_num : 2 ≠ 0)
      rwa [Real.sq_sqrt (by linarith)] at this
    have hnorm : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    have hmem : ((y 0) ^ 2 / 2, (y 1) ^ 2 / 2) ∈ liouvilleCone T :=
      ⟨by positivity, by positivity, by linarith⟩
    have hge := hΦ_nn _ hmem
    unfold spinEvalT at hge
    have heq : Φ (Real.sqrt (2 * ((y 0) ^ 2 / 2)), Real.sqrt (2 * ((y 1) ^ 2 / 2))) = f y := by
      dsimp [f]
      have h0 : Real.sqrt (2 * ((y 0) ^ 2 / 2)) = |y 0| := by
        rw [show 2 * ((y 0) ^ 2 / 2) = (y 0) ^ 2 by ring, Real.sqrt_sq_eq_abs]
      have h1 : Real.sqrt (2 * ((y 1) ^ 2 / 2)) = |y 1| := by
        rw [show 2 * ((y 1) ^ 2 / 2) = (y 1) ^ 2 by ring, Real.sqrt_sq_eq_abs]
      rw [h0, h1]
      rcases le_total 0 (y 0) with hy0 | hy0 <;> rcases le_total 0 (y 1) with hy1 | hy1
      · rw [abs_of_nonneg hy0, abs_of_nonneg hy1]
      · rw [abs_of_nonneg hy0, abs_of_nonpos hy1, hΦ.d4_inv.2.1]
      · rw [abs_of_nonpos hy0, abs_of_nonneg hy1, hΦ.d4_inv.1]
      · rw [abs_of_nonpos hy0, abs_of_nonpos hy1, hΦ.d4_inv.1, hΦ.d4_inv.2.1]
    rw [heq] at hge
    dsimp [fMinus]; exact max_eq_right (by linarith)
  have hfMinus_int_ν : Integrable fMinus ν_e := by
    refine ((hν_gauss one_pos).const_mul (B * Real.exp (R ^ 2))).mono'
      hfMinus_cont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hfMinus_nn x)]
    rcases le_or_gt ‖x‖ R with hx | hx
    · have h1 : 1 ≤ Real.exp (R ^ 2) * Real.exp (-1 * ‖x‖ ^ 2) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by have := pow_le_pow_left₀ (norm_nonneg x) hx 2; linarith)
      calc fMinus x ≤ B := hfMinus_bd x
        _ ≤ B * (Real.exp (R ^ 2) * Real.exp (-1 * ‖x‖ ^ 2)) := le_mul_of_one_le_right hB_nn h1
        _ = (B * Real.exp (R ^ 2)) * Real.exp (-1 * ‖x‖ ^ 2) := by ring
    · rw [hneg_supp x hx]; positivity
  -- DCT for `mehlerMean 1 r fMinus → fMinus` under `ν_e`
  obtain ⟨C_neg, hC_neg_pos, hneg_ub⟩ :=
    mehlerMean_compactSupport_gaussian_ub (w := 1) hfMinus_cont hR_nn hB_nn hfMinus_nn hfMinus_bd hneg_supp
  have htend_neg_ν : Tendsto (fun r => ∫ x : RadialSpace 1, mehlerMean 1 r fMinus x ∂ν_e)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace 1, fMinus x ∂ν_e)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun r x => mehlerMean 1 r fMinus x) (f := fMinus)
      (bound := fun x => C_neg * Real.exp (-π / 8 * ‖x‖ ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
      exact (integrable_mehlerMean_of_bounded hν_gauss hfMinus_cont hfMinus_abs_bd
        (by linarith) hr1).aestronglyMeasurable
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      filter_upwards with x
      have hsub := hneg_ub hr x
      rw [Real.norm_of_nonneg hsub.1]; exact hsub.2
    · convert (hν_gauss (by positivity : 0 < π / 8)).const_mul C_neg using 1
      ext x; ring_nf
    · filter_upwards with x
      refine tendsto_mehlerMean_of_continuous_weight hfMinus_cont (b := 0) (d := 0) hB_nn
        (fun y => by unfold euclideanWeight; simp; exact hfMinus_abs_bd y) x
  -- Vacuum-side limit from `spinDV` (with `h ≡ 1`, `M = 1`)
  have htend_ρ : Tendsto (fun r => ∫ x : RadialSpace 1, mehlerMean 1 r f x ∂ρ_e)
      (𝓝[<] 1) (𝓝 (-spinPhiVac a Φ)) := by
    obtain ⟨_, _, hDV⟩ := spinDV ha
    have h1_d4 : IsD4Invariant (fun _ : ℝ × ℝ => (1 : ℝ)) := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    have ht := (hDV zero_le_one measurable_const h1_d4 (fun _ => by norm_num) hΦ).2
    have hvac_eq : (∫ p : ℝ × ℝ, Φ p * 1 * spinV1 a p.1 * spinV1 a p.2) = -spinPhiVac a Φ := by
      unfold spinPhiVac; simp only [mul_one, neg_neg]
    rw [hvac_eq] at ht
    refine ht.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r ⟨hr0, hr1⟩
    rw [spinCardyEucMeasure_integral ha]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [mul_one]
    congr 2
    unfold spinMehlerOp mehlerMean
    rw [← wVolume_preserving_e2ToProd.integral_comp' (g := fun q : ℝ × ℝ =>
      spinMehlerKernel1D r p.1 q.1 * spinMehlerKernel1D r p.2 q.2 * Φ q)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [f, wE2ToProd_apply]
    have hK := spinMehlerKernel1D_prod_eq_mehlerKernel hr0.le hr1 p (y 0, y 1)
    have hp_e : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2] = wE2ToProd.symm p := by
      ext i; fin_cases i <;> rfl
    have hy_e : (EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0, y 1] = y := by
      ext i; fin_cases i <;> rfl
    rw [hp_e, hy_e] at hK
    rw [hK]
  -- Fatou along `r_n = 1 - 1 / (2 (n + 1))` for `fPlus`
  let rSeq : ℕ → ℝ := fun n => 1 - 1 / (2 * ((n : ℝ) + 1))
  have hrSeq_mem : ∀ n : ℕ, rSeq n ∈ Ico (1 / 2 : ℝ) 1 := fun n => by
    dsimp [rSeq]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    refine ⟨?_, ?_⟩
    · have : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 :=
        div_le_div_of_nonneg_left zero_le_one zero_lt_two (by linarith)
      linarith
    · have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
      linarith
  have hrSeq_tend : Tendsto rSeq atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (hrSeq_mem n).2⟩
    have hinv : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop two_pos)
    simpa [rSeq] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hAr_add : ∀ n : ℕ, ∀ x : RadialSpace 1,
      mehlerMean 1 (rSeq n) fPlus x = mehlerMean 1 (rSeq n) f x + mehlerMean 1 (rSeq n) fMinus x := by
    intro n x
    have hr0 : 0 ≤ rSeq n := by linarith [(hrSeq_mem n).1]
    have hr1 : rSeq n < 1 := (hrSeq_mem n).2
    have hk := (integral_mehlerKernel 1 hr0 hr1 x).1
    have hint1 : Integrable (fun y => mehlerKernel 1 (rSeq n) x y * f y) := by
      refine (hk.const_mul B).mono'
        (((continuous_mehlerKernel 1 (rSeq n)).comp (Continuous.prodMk continuous_const continuous_id)).mul
          hf_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg 1 hr1 x y)]
      linarith [mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg 1 hr1 x y)]
    have hint2 : Integrable (fun y => mehlerKernel 1 (rSeq n) x y * fMinus y) := by
      refine (hk.const_mul B).mono'
        (((continuous_mehlerKernel 1 (rSeq n)).comp (Continuous.prodMk continuous_const continuous_id)).mul
          hfMinus_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg 1 hr1 x y)]
      linarith [mul_le_mul_of_nonneg_left (hfMinus_abs_bd y) (mehlerKernel_nonneg 1 hr1 x y)]
    unfold mehlerMean
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only; rw [hf_split y]; ring
  have hAr_plus_int : ∀ n : ℕ,
      (∫ x : RadialSpace 1, mehlerMean 1 (rSeq n) fPlus x ∂ν_e) =
        (∫ x : RadialSpace 1, mehlerMean 1 (rSeq n) f x ∂ρ_e) +
        (∫ x : RadialSpace 1, mehlerMean 1 (rSeq n) fMinus x ∂ν_e) := by
    intro n
    have hr0 : 0 < rSeq n := by linarith [(hrSeq_mem n).1]
    have hr1 : rSeq n < 1 := (hrSeq_mem n).2
    have hcr := spinMehler_crossing_eq ha meas hΦ hr0 hr1
    have hfm := integrable_mehlerMean_of_bounded hν_gauss hfMinus_cont hfMinus_abs_bd hr0.le hr1
    have hpt : (fun x => mehlerMean 1 (rSeq n) fPlus x) =
        fun x => mehlerMean 1 (rSeq n) f x + mehlerMean 1 (rSeq n) fMinus x := funext (hAr_add n)
    rw [hpt, integral_add hcr.1 hfm, hcr.2.2]
  set L : ℝ := -spinPhiVac a Φ + ∫ x : RadialSpace 1, fMinus x ∂ν_e
  have hplus_tend : Tendsto (fun n : ℕ => ∫ x : RadialSpace 1, mehlerMean 1 (rSeq n) fPlus x ∂ν_e)
      atTop (𝓝 L) := by
    simp_rw [hAr_plus_int]
    exact (htend_ρ.comp hrSeq_tend).add (htend_neg_ν.comp hrSeq_tend)
  have hAr_plus_nn : ∀ n x, 0 ≤ mehlerMean 1 (rSeq n) fPlus x := fun n x =>
    integral_nonneg fun y => mul_nonneg (mehlerKernel_nonneg 1 (hrSeq_mem n).2 x y) (hfPlus_nn y)
  have hfatou : ∫⁻ x : RadialSpace 1, ENNReal.ofReal (fPlus x) ∂ν_e ≤ ENNReal.ofReal L := by
    have hpt_lim : ∀ x : RadialSpace 1,
        Tendsto (fun n : ℕ => ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x)) atTop
          (𝓝 (ENNReal.ofReal (fPlus x))) := fun x =>
      (ENNReal.continuous_ofReal.tendsto (fPlus x)).comp
        ((tendsto_mehlerMean_of_continuous_weight hfPlus_cont (b := 0) (d := 0) hB_nn
          (fun y => by unfold euclideanWeight; simp; exact hfPlus_abs_bd y) x).comp hrSeq_tend)
    have hliminf_eq : ∀ x : RadialSpace 1,
        ENNReal.ofReal (fPlus x) = liminf (fun n : ℕ => ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x)) atTop :=
      fun x => (hpt_lim x).liminf_eq.symm
    have hmeas_n : ∀ n : ℕ, Measurable (fun x : RadialSpace 1 =>
        ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x)) := fun n =>
      ENNReal.measurable_ofReal.comp
        (continuous_mehlerMean_of_bounded hfPlus_cont hfPlus_abs_bd (by linarith [(hrSeq_mem n).1])
          (hrSeq_mem n).2).measurable
    have h_lint_eq : ∀ n : ℕ,
        (∫⁻ x : RadialSpace 1, ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x) ∂ν_e) =
          ENNReal.ofReal (∫ x : RadialSpace 1, mehlerMean 1 (rSeq n) fPlus x ∂ν_e) := fun n =>
      (ofReal_integral_eq_lintegral_ofReal
        (integrable_mehlerMean_of_bounded hν_gauss hfPlus_cont hfPlus_abs_bd
          (by linarith [(hrSeq_mem n).1]) (hrSeq_mem n).2)
        (Eventually.of_forall (hAr_plus_nn n))).symm
    have h_lim_lint : Tendsto (fun n : ℕ =>
        ∫⁻ x : RadialSpace 1, ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x) ∂ν_e)
        atTop (𝓝 (ENNReal.ofReal L)) := by
      simp_rw [h_lint_eq]
      exact (ENNReal.continuous_ofReal.tendsto L).comp hplus_tend
    calc ∫⁻ x : RadialSpace 1, ENNReal.ofReal (fPlus x) ∂ν_e
        = ∫⁻ x : RadialSpace 1,
            liminf (fun n : ℕ => ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x)) atTop ∂ν_e := by
          simp_rw [← hliminf_eq]
      _ ≤ liminf (fun n : ℕ =>
            ∫⁻ x : RadialSpace 1, ENNReal.ofReal (mehlerMean 1 (rSeq n) fPlus x) ∂ν_e) atTop :=
          lintegral_liminf_le hmeas_n
      _ = ENNReal.ofReal L := h_lim_lint.liminf_eq
  have hfPlus_int_ν : Integrable fPlus ν_e := by
    refine ⟨hfPlus_cont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hfPlus_nn)]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hf_int_ν : Integrable f ν_e := by
    have : f = fun x => fPlus x - fMinus x := funext hf_split
    rw [this]; exact hfPlus_int_ν.sub hfMinus_int_ν
  have hfPlus_le_L : ∫ x : RadialSpace 1, fPlus x ∂ν_e ≤ L := by
    have h1 : ENNReal.ofReal (∫ x : RadialSpace 1, fPlus x ∂ν_e) ≤ ENNReal.ofReal L := by
      rw [ofReal_integral_eq_lintegral_ofReal hfPlus_int_ν (Eventually.of_forall hfPlus_nn)]
      exact hfatou
    have hL_nn : 0 ≤ L := ge_of_tendsto' hplus_tend fun n =>
      integral_nonneg (hAr_plus_nn n)
    exact (ENNReal.ofReal_le_ofReal_iff hL_nn).mp h1
  have hf_le_vac : ∫ x : RadialSpace 1, f x ∂ν_e ≤ -spinPhiVac a Φ := by
    have : f = fun x => fPlus x - fMinus x := funext hf_split
    rw [this, integral_sub hfPlus_int_ν hfMinus_int_ν]
    dsimp [L] at hfPlus_le_L; linarith
  -- Transfer `hf_int_ν` and `hf_le_vac` back to `meas.ν` via `spinSqrtEucMap`
  have heval_eq : f ∘ spinSqrtEucMap = spinEvalT Φ := by
    ext p; dsimp [f, spinSqrtEucMap, spinEvalT]
    rw [wE2ToProd_symm_apply_zero, wE2ToProd_symm_apply_one]
  have hint_eval : Integrable (spinEvalT Φ) meas.ν := by
    rw [← heval_eq]
    exact (integrable_map_measure hf_cont.aestronglyMeasurable
      measurable_spinSqrtEucMap.aemeasurable).mp hf_int_ν
  have hle_eval : ∫ p : ℝ × ℝ, spinEvalT Φ p ∂meas.ν ≤ -spinPhiVac a Φ := by
    have h1 : (∫ x : RadialSpace 1, f x ∂ν_e) = ∫ p : ℝ × ℝ, spinEvalT Φ p ∂meas.ν := by
      unfold ν_e
      rw [integral_map measurable_spinSqrtEucMap.aemeasurable hf_cont.aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall fun p => congrFun heval_eq p)
    linarith
  refine ⟨hint_eval, hle_eval, ?_, ?_⟩
  · intro hnn
    have h0 : 0 ≤ ∫ p : ℝ × ℝ, spinEvalT Φ p ∂meas.ν := integral_nonneg_of_ae hnn
    linarith
  · intro hnn hvac_nn
    have h0 : 0 ≤ ∫ p : ℝ × ℝ, spinEvalT Φ p ∂meas.ν := integral_nonneg_of_ae hnn
    have hvac0 : spinPhiVac a Φ = 0 := by linarith
    refine ⟨hvac0, ?_⟩
    have hint0 : ∫ p : ℝ × ℝ, spinEvalT Φ p ∂meas.ν = 0 := by linarith
    exact (integral_eq_zero_iff_of_nonneg_ae hnn hint_eval).mp hint0

/-- **`sd:SD`** (Theorem SD: strong duality, attainment, scalar comparison, and quadrant equality
across all three test classes), proved unconditionally for all `a ≥ 2`. -/
theorem spinDSD : SpinDSD := spinDSD_of_spinDW spinDW

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDW

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDSD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDSD

end FormalResearch.ModularBootstrap.Spin

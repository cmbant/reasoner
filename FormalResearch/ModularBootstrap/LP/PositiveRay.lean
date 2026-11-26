module

public import FormalResearch.ModularBootstrap.LP.PolyCompact
public import FormalResearch.ModularBootstrap.LP.Tilt
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lemma LP-H (`dsl:positive-ray`): a positive odd-polynomial majorant on a positive ray

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-H (line 79).  For every `w > 0` and
`T₀ > 0` there is `p ∈ ⋃_N O_N` (the span of the `P_k`, `k` odd) with `p ≥ 1` on `[T₀, ∞)`.

The proof is the paper's: if not, the functional `L(c + q) = c` on `ℝ + ⋃ O_N` is positive on the
ray, `dsl:poly-compact` (with `μ₀ = 0`, `p₀ = 1`) gives a probability measure on the ray with all odd
moments zero and an `e^{εt}` moment, and `ds:cay` + `ds:cont` (through `tilt_crossing`) force
`Z(b) = b^{-w} Z(1/b)` for all `b > 0`, which contradicts `1 = Z(1) ≤ Z(b) ≤ b^{-w} e^{-2π(1/b-1)T₀}`
as `b → 0`.  The sum `ℝ + ⋃ O_N` need not be shown direct: `1 ∉ ⋃ O_N` is the hypothesis, and a
functional vanishing on `⋃ O_N` with `L 1 = 1` comes from `Submodule.exists_dual_map_eq_bot_of_notMem`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.LP

/-- `O_N = span{P_k : k odd, k ≤ N}` (functions `ℝ → ℝ`). -/
def oddSpan (w : ℝ) (N : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ {f | ∃ k, Odd k ∧ k ≤ N ∧ f = lagP w k}

lemma lagP_mem_oddSpan (w : ℝ) {k N : ℕ} (hk : Odd k) (hkN : k ≤ N) : lagP w k ∈ oddSpan w N :=
  Submodule.subset_span ⟨k, hk, hkN, rfl⟩

lemma oddSpan_mono (w : ℝ) {M N : ℕ} (h : M ≤ N) : oddSpan w M ≤ oddSpan w N :=
  Submodule.span_mono fun _ ⟨k, hk, hkM, hf⟩ => ⟨k, hk, hkM.trans h, hf⟩

/-- The ray lemma has no counterexample in the span of `P_k`: statement of `dsl:positive-ray`. -/
def PositiveRayStatement (w T₀ : ℝ) : Prop :=
  ∃ (N : ℕ) (p : ℝ → ℝ), p ∈ oddSpan w N ∧ ∀ t, T₀ ≤ t → 1 ≤ p t

/-- Core: no probability measure on `[T₀, ∞)` has an `e^{εt}` moment and all odd moments `∫ P_k = 0`. -/
theorem ray_false {w T₀ : ℝ} (hw : 0 < w) (hT₀ : 0 < T₀) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Iio T₀) = 0) {ε : ℝ} (hε : 0 < ε)
    (hexp : Integrable (fun s => Real.exp (ε * s)) μ)
    (hodd : ∀ k, Odd k → ∫ s, lagP w k s ∂μ = 0) : False := by
  have hpi := Real.pi_pos
  have hμ0 : μ (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hT₀.le) hsupp
  obtain ⟨θ, hθ0, hθ1, hf, -, hcr⟩ := tilt_crossing hw (μ' := 0) hμ0 (by simp) hε hexp
    (integrable_zero_measure) (fun k hk => by rw [hodd k hk, integral_zero_measure])
  set ν : Measure ℝ := expTilt μ with hν
  have hs0 := sTheta_pos hθ0 hθ1
  set s : ℝ := sTheta θ with hs
  have hνIio : ν (Iio 0) = 0 := expTilt_apply_eq_zero hμ0
  have hνT : ν (Iio T₀) = 0 := expTilt_apply_eq_zero hsupp
  have hs1 : s < 1 := by
    rw [hs]; unfold sTheta; rw [div_lt_one (by linarith)]; linarith
  have hae0 : ∀ᵐ t ∂ν, 0 ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hνIio
    filter_upwards [this] with t ht using not_lt.1 ht
  have haeT : ∀ᵐ t ∂ν, T₀ ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio T₀ := measure_eq_zero_iff_ae_notMem.1 hνT
    filter_upwards [this] with t ht using not_lt.1 ht
  have hcross : ∀ β, s < β → β < 1 / s →
      lapZ ν β + (fun _ : ℝ => (0 : ℝ)) β =
        β ^ (-w) * (lapZ ν (1 / β) + (fun _ : ℝ => (0 : ℝ)) (1 / β)) := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have hinv : s < 1 / β := by
      rw [lt_div_iff₀ hβ0]; rw [lt_div_iff₀ hs0] at h2; linarith
    have h := hcr β h1 h2
    have hz : ∫ t, xiW w β t ∂expTilt (0 : Measure ℝ) = 0 := by
      rw [integral_expTilt]; simp
    rw [hz, integral_xiW_lapZ (hf.mono hνIio h1.le) (hf.mono hνIio hinv.le)] at h
    simp only [add_zero]
    linarith
  obtain ⟨hall, hid⟩ := ds_cont (v := fun _ : ℝ => (0 : ℝ)) (analyticOnNhd_const) hνIio hs0 hs1 hf hcross
  simp only [add_zero] at hid
  -- `Z(1) = 1`
  have hZ1 : lapZ ν 1 = 1 := by
    unfold lapZ
    rw [hν, integral_expTilt]
    have : ∀ t : ℝ, Real.exp (2 * π * t) * Real.exp (-2 * π * 1 * t) = 1 := fun t => by
      rw [← Real.exp_add]; ring_nf; simp
    simp_rw [this]
    simp
  -- the chain of inequalities, for `b ∈ (0, 1)`
  have hchain : ∀ b : ℝ, 0 < b → b < 1 →
      1 ≤ b ^ (-w) * Real.exp (-2 * π * (1 / b - 1) * T₀) := by
    intro b hb0 hb1
    have hb1' : 1 < 1 / b := by rw [lt_div_iff₀ hb0]; linarith
    have hZb : lapZ ν 1 ≤ lapZ ν b := by
      unfold lapZ
      refine integral_mono_ae (hall 1 one_pos) (hall b hb0) ?_
      filter_upwards [hae0] with t ht
      apply Real.exp_le_exp.2
      nlinarith only [ht, hb1, hpi, mul_nonneg hpi.le ht]
    have hZu : lapZ ν (1 / b) ≤ Real.exp (-2 * π * (1 / b - 1) * T₀) * lapZ ν 1 := by
      unfold lapZ
      rw [← integral_const_mul]
      refine integral_mono_ae (hall _ (by linarith)) ((hall 1 one_pos).const_mul _) ?_
      filter_upwards [haeT] with t ht
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : 0 ≤ 1 / b - 1 := by linarith
      nlinarith only [ht, h1, hpi, mul_nonneg h1 (sub_nonneg.2 ht), mul_pos hpi hT₀]
    have := hid b hb0
    rw [hZ1] at hZb hZu
    have hbpos : 0 < b ^ (-w) := Real.rpow_pos_of_pos hb0 _
    calc (1 : ℝ) ≤ lapZ ν b := hZb
      _ = b ^ (-w) * lapZ ν (1 / b) := this
      _ ≤ b ^ (-w) * (Real.exp (-2 * π * (1 / b - 1) * T₀) * 1) :=
          mul_le_mul_of_nonneg_left hZu hbpos.le
      _ = _ := by ring
  -- contradiction as `b → 0`
  have htend := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero w (2 * π * T₀) (by positivity)
  have hK : 0 < Real.exp (-(2 * π * T₀)) := Real.exp_pos _
  obtain ⟨u, hu1, hu⟩ : ∃ u : ℝ, 1 < u ∧
      u ^ w * Real.exp (-(2 * π * T₀) * u) < Real.exp (-(2 * π * T₀)) := by
    have h1 := (htend.eventually (gt_mem_nhds hK)).and (eventually_gt_atTop (1 : ℝ))
    obtain ⟨u, hu, hu'⟩ := h1.exists
    exact ⟨u, hu', hu⟩
  have hu0 : 0 < u := by linarith
  have := hchain (1 / u) (by positivity) (by rw [div_lt_one hu0]; exact hu1)
  rw [one_div_one_div, one_div, Real.inv_rpow hu0.le, Real.rpow_neg hu0.le, inv_inv] at this
  have e : Real.exp (-2 * π * (u - 1) * T₀) =
      Real.exp (-(2 * π * T₀) * u) * Real.exp (2 * π * T₀) := by
    rw [← Real.exp_add]; ring_nf
  rw [e] at this
  have e2 : Real.exp (-(2 * π * T₀)) * Real.exp (2 * π * T₀) = 1 := by
    rw [← Real.exp_add]; simp
  have hE : 0 < Real.exp (2 * π * T₀) := Real.exp_pos _
  nlinarith only [this, hu, e2, hE, Real.exp_pos (-(2 * π * T₀ * u))]

/-! ### The ray lemma from `dsl:poly-compact` -/

section Ray

variable {w T₀ : ℝ}

/-- The chain `V_N = ℝ + O_N` on the ray `X = [T₀, ∞)`, as spaces of continuous functions. -/
noncomputable def rayV (w : ℝ) (t : C(Ici T₀, ℝ)) (N : ℕ) : Submodule ℝ C(Ici T₀, ℝ) :=
  Submodule.span ℝ ({1} ∪ {f | ∃ k, Odd k ∧ k ≤ N ∧ f = pc (lagPC w) k t})

/-- The odd part `⋃ O_N ∘ t`. -/
noncomputable def rayA (w : ℝ) (t : C(Ici T₀, ℝ)) : Submodule ℝ C(Ici T₀, ℝ) :=
  Submodule.span ℝ {f | ∃ k, Odd k ∧ f = pc (lagPC w) k t}

/-- The `t`-coordinate on the ray. -/
def rayT (T₀ : ℝ) : C(Ici T₀, ℝ) := ⟨fun x => x.1, continuous_subtype_val⟩

lemma rayT_apply (x : Ici T₀) : rayT T₀ x = x.1 := rfl

lemma rayHyp (hw : 0 < w) (hT₀ : 0 < T₀) :
    PolyCompactHyp ((1 + w) / π) (lagPC w) T₀ (rayT T₀) (rayV w (rayT T₀)) where
  fam := lagP_oddFam hw
  T₀_nonneg := hT₀.le
  t_ge := fun x => x.2
  t_proper := (isClosed_Ici.isClosedEmbedding_subtypeVal).isProperMap
  mono := fun M N _ _ h => Submodule.span_mono (by
    rintro f (hf | ⟨k, hk, hkM, rfl⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨k, hk, hkM.trans h, rfl⟩)
  growth := by
    intro N _
    let GB : Submodule ℝ C(Ici T₀, ℝ) :=
      { carrier := {q | ∃ C : ℝ, ∀ x, |q x| ≤ C * (1 + rayT T₀ x) ^ N}
        zero_mem' := ⟨0, fun x => by simp⟩
        add_mem' := by
          rintro f g ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
          refine ⟨C₁ + C₂, fun x => ?_⟩
          calc |(f + g) x| ≤ |f x| + |g x| := abs_add_le _ _
            _ ≤ C₁ * (1 + rayT T₀ x) ^ N + C₂ * (1 + rayT T₀ x) ^ N := add_le_add (h₁ x) (h₂ x)
            _ = (C₁ + C₂) * (1 + rayT T₀ x) ^ N := by ring
        smul_mem' := by
          rintro c f ⟨C, h⟩
          refine ⟨|c| * C, fun x => ?_⟩
          simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul]
          calc |c| * |f x| ≤ |c| * (C * (1 + rayT T₀ x) ^ N) := by gcongr; exact h x
            _ = |c| * C * (1 + rayT T₀ x) ^ N := by ring }
    have hle : rayV w (rayT T₀) N ≤ GB := by
      refine Submodule.span_le.2 ?_
      rintro f (hf | ⟨k, hk, hkN, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hf]
        refine ⟨1, fun x => ?_⟩
        have : (1 : ℝ) ≤ (1 + rayT T₀ x) ^ N :=
          one_le_pow₀ (by have := hT₀.le.trans x.2; simp only [rayT_apply]; linarith)
        simpa using this
      · set m : ℝ := max 1 ((1 + w) / π * k) with hm
        refine ⟨m ^ k, fun x => ?_⟩
        have hx : 0 ≤ rayT T₀ x := hT₀.le.trans x.2
        have h1 := (lagP_oddFam hw).upper k hk (rayT T₀ x) hx
        have hm1 : 1 ≤ m := le_max_left _ _
        have hm2 : (1 + w) / π * k ≤ m := le_max_right _ _
        have h2 : rayT T₀ x + (1 + w) / π * k ≤ (1 + rayT T₀ x) * m := by
          nlinarith only [hx, hm1, hm2]
        have h3 : (rayT T₀ x + (1 + w) / π * k) ^ k ≤ ((1 + rayT T₀ x) * m) ^ k :=
          pow_le_pow_left₀ (by positivity) h2 k
        have h4 : (1 + rayT T₀ x) ^ k ≤ (1 + rayT T₀ x) ^ N :=
          pow_le_pow_right₀ (by linarith) hkN
        calc |pc (lagPC w) k (rayT T₀) x| ≤ (rayT T₀ x + (1 + w) / π * k) ^ k := by
              simpa using h1
          _ ≤ ((1 + rayT T₀ x) * m) ^ k := h3
          _ = m ^ k * (1 + rayT T₀ x) ^ k := by rw [mul_pow]; ring
          _ ≤ m ^ k * (1 + rayT T₀ x) ^ N := by gcongr
    intro q hq
    exact hle hq
  contains := fun N _ j hj hjN => Submodule.subset_span (Or.inr ⟨j, hj, hjN, rfl⟩)
  majorant := ⟨1, 1, 1, odd_one, Submodule.subset_span (Or.inl rfl), one_pos, fun _ => le_rfl⟩

/-- **Lemma LP-H** (`dsl:positive-ray`).  For every `w > 0` and `T₀ > 0` there are `N` and
`p ∈ O_N = span{P_k : k odd ≤ N}` with `p ≥ 1` on `[T₀, ∞)`.  (`dsl:poly-compact` with `μ₀ = 0`,
`p₀ = 1`, then `ds:cay` and `ds:cont`.) -/
theorem positive_ray (hw : 0 < w) (hT₀ : 0 < T₀) : PositiveRayStatement w T₀ := by
  by_contra hneg
  unfold PositiveRayStatement at hneg
  push Not at hneg
  have hT := rayHyp (T₀ := T₀) hw hT₀
  set t := rayT T₀ with ht
  set V := rayV w t with hV
  set A := rayA w t with hA
  -- every element of `A` is `p ∘ t` for `p ∈ O_N`
  have hArep : ∀ a ∈ A, ∃ x, a x < 1 := by
    intro a ha
    have : ∃ N p, p ∈ oddSpan w N ∧ ∀ x, a x = p (t x) := by
      refine Submodule.span_induction (p := fun a _ => ∃ N p, p ∈ oddSpan w N ∧ ∀ x, a x = p (t x))
        ?_ ?_ ?_ ?_ ha
      · rintro f ⟨k, hk, rfl⟩
        exact ⟨k, lagP w k, lagP_mem_oddSpan w hk le_rfl, fun x => rfl⟩
      · exact ⟨0, 0, Submodule.zero_mem _, fun x => by simp⟩
      · rintro f g _ _ ⟨N₁, p₁, hp₁, h₁⟩ ⟨N₂, p₂, hp₂, h₂⟩
        refine ⟨max N₁ N₂, p₁ + p₂, Submodule.add_mem _
          (oddSpan_mono w (le_max_left _ _) hp₁) (oddSpan_mono w (le_max_right _ _) hp₂), fun x => ?_⟩
        simp [h₁ x, h₂ x]
      · rintro c f _ ⟨N, p, hp, h⟩
        exact ⟨N, c • p, Submodule.smul_mem _ _ hp, fun x => by simp [h x]⟩
    obtain ⟨N, p, hp, h⟩ := this
    obtain ⟨s, hs, hlt⟩ := hneg N p hp
    exact ⟨⟨s, hs⟩, by rw [h]; exact hlt⟩
  have h1A : (1 : C(Ici T₀, ℝ)) ∉ A := fun h => by
    obtain ⟨x, hx⟩ := hArep _ h
    simp at hx
  obtain ⟨f, hf1, hfA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h1A inferInstance
  have hfA' : ∀ a ∈ A, f a = 0 := fun a ha => by
    have : f a ∈ A.map f := Submodule.mem_map_of_mem ha
    rw [hfA] at this; simpa using this
  -- `⋃ V_N ≤ ℝ ∙ 1 ⊔ A`
  have hUle : polyUnion V ≤ Submodule.span ℝ {(1 : C(Ici T₀, ℝ))} ⊔ A := by
    refine iSup_le fun N => Submodule.span_le.2 ?_
    rintro g (hg | ⟨k, hk, hkN, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.subset_span hg)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨k, hk, rfl⟩)
  have hfU : ∀ g : C(Ici T₀, ℝ), g ∈ polyUnion V → ∃ c : ℝ, g = c • 1 + (g - c • 1) ∧
      g - c • 1 ∈ A := by
    intro g hg
    obtain ⟨y, hy, a, ha, rfl⟩ := Submodule.mem_sup.1 (hUle hg)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨c, by abel, by simpa using ha⟩
  let L : polyUnion V →ₗ[ℝ] ℝ := (f 1)⁻¹ • (f ∘ₗ (polyUnion V).subtype)
  have hLval : ∀ (g : polyUnion V) (c : ℝ), (g : C(Ici T₀, ℝ)) - c • 1 ∈ A → L g = c := by
    intro g c hc
    have : f g = c * f 1 := by
      have h0 := hfA' _ hc
      rw [map_sub, map_smul, smul_eq_mul] at h0
      linarith
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, smul_eq_mul]
    rw [this]; field_simp
  have hLpos : ∀ g : polyUnion V, (∀ x, 0 ≤ g.1 x) → 0 ≤ L g := by
    intro g hg
    obtain ⟨c, -, hc⟩ := hfU g.1 g.2
    rw [hLval g c hc]
    by_contra hcneg
    push Not at hcneg
    -- `a / (-c) ≥ 1` on the ray, `a = g - c • 1 ∈ A`
    have hcA : (-c)⁻¹ • (g.1 - c • 1) ∈ A := Submodule.smul_mem _ _ hc
    obtain ⟨x, hx⟩ := hArep _ hcA
    simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one] at hx
    have : (-c)⁻¹ * (g.1 x - c) ≥ 1 := by
      rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ (by linarith)]
      nlinarith only [hg x]
    linarith
  have hodd0 : ∀ (j : ℕ), Odd j → ∀ (v : polyUnion V),
      (v : C(Ici T₀, ℝ)) = pc (lagPC w) j t → L v = 0 := by
    intro j hj v hvj
    have : (v : C(Ici T₀, ℝ)) - (0 : ℝ) • 1 ∈ A := by
      rw [hvj, zero_smul, sub_zero]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    exact hLval v 0 this
  have hodd : ∀ j : ℕ, Odd j → ∀ v : polyUnion V,
      (v : C(Ici T₀, ℝ)) = pc (lagPC w) j t → |L v| ≤ ((1 : ℝ) * j) ^ j := by
    intro j hj v hvj
    rw [hodd0 j hj v hvj, abs_zero]
    positivity
  have : LocallyCompactSpace (Ici T₀) := isClosed_Ici.locallyCompactSpace
  obtain ⟨μ, hreg, hpoly, hrep, ε, hε, hexp⟩ := poly_compact hT one_pos L hLpos hodd
  -- the probability measure on `ℝ`
  have h1V : (1 : C(Ici T₀, ℝ)) ∈ polyUnion V :=
    le_polyUnion odd_one (Submodule.subset_span (Or.inl rfl))
  have hL1 : L ⟨1, h1V⟩ = 1 := hLval ⟨1, h1V⟩ 1 (by simp)
  have hint1 : Integrable (fun _ : Ici T₀ => (1 : ℝ)) μ := hpoly 1 (hT.union_le_polyGrowth h1V)
  have hfin : IsFiniteMeasure μ := by
    rw [integrable_const_iff] at hint1
    rcases hint1 with h | h
    · exact absurd h one_ne_zero
    · exact h
  have hmu1 : μ univ = 1 := by
    have := hrep ⟨1, h1V⟩
    rw [hL1] at this
    have h2 : ∫ _ : Ici T₀, (1 : ℝ) ∂μ = 1 := by simpa using this
    rw [integral_const, smul_eq_mul, mul_one] at h2
    exact (ENNReal.toReal_eq_one_iff _).1 h2
  have : IsProbabilityMeasure μ := ⟨hmu1⟩
  have hmeas : Measurable (fun x : Ici T₀ => x.1) := measurable_subtype_coe
  have : IsProbabilityMeasure (μ.map (fun x : Ici T₀ => x.1)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  refine ray_false hw hT₀ (μ := μ.map (fun x : Ici T₀ => x.1)) ?_ hε ?_ ?_
  · rw [Measure.map_apply hmeas measurableSet_Iio]
    have : (fun x : Ici T₀ => x.1) ⁻¹' Iio T₀ = ∅ := by
      ext x; simp [not_lt.2 x.2]
    rw [this, measure_empty]
  · rw [integrable_map_measure (by fun_prop) hmeas.aemeasurable]
    exact hexp
  · intro k hk
    rw [integral_map hmeas.aemeasurable (continuous_lagP w k).aestronglyMeasurable]
    have := hrep ⟨pc (lagPC w) k t, hT.pc_mem hk⟩
    rw [hodd0 k hk ⟨pc (lagPC w) k t, hT.pc_mem hk⟩ rfl] at this
    exact this

end Ray

/-- info: 'FormalResearch.ModularBootstrap.LP.positive_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positive_ray

end FormalResearch.ModularBootstrap.LP

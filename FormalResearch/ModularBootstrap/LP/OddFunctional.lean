module

public import FormalResearch.ModularBootstrap.LP.DerivLimitI

/-!
# The reference functional `𝓛` on `⋃ O_N ∘ t` (the adapter for `dsl:poly-compact`)

For a closed `X ⊂ [T₀, ∞)` and `t = id|_X`, the chain `V_N = O_N ∘ t` of continuous functions on `X`
and the reference functional `𝓛(p ∘ t) = ∫ p dμ_C` of `ds:LP`.  The restriction map `p ↦ p ∘ t` need not
be injective (e.g. for finite `X`); `𝓛` is nevertheless well defined, and positive on `X`, as soon as no
finite odd-Laguerre test is feasible on `X`: if `p ∘ t = 0` then `±p ≥ 0` on `X`, so `g_vac ≤ 0` for both
signs, i.e. `𝓛(p) = 0` (`exists_functional`).  The functional is built on the quotient by the kernel
of the restriction map.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing

namespace FormalResearch.ModularBootstrap.LP

/-- `O_N` inside `C(ℝ, ℝ)`. -/
def OC (w : ℝ) (N : ℕ) : Submodule ℝ C(ℝ, ℝ) :=
  Submodule.span ℝ {f | ∃ k, Odd k ∧ k ≤ N ∧ f = lagPC w k}

/-- `⋃_N O_N` inside `C(ℝ, ℝ)`. -/
def OCall (w : ℝ) : Submodule ℝ C(ℝ, ℝ) :=
  Submodule.span ℝ {f | ∃ k, Odd k ∧ f = lagPC w k}

lemma OC_le_OCall (w : ℝ) (N : ℕ) : OC w N ≤ OCall w :=
  Submodule.span_mono fun _ ⟨k, hk, _, hf⟩ => ⟨k, hk, hf⟩

lemma OC_mono (w : ℝ) {M N : ℕ} (h : M ≤ N) : OC w M ≤ OC w N :=
  Submodule.span_mono fun _ ⟨k, hk, hkM, hf⟩ => ⟨k, hk, hkM.trans h, hf⟩

lemma coe_mem_oddSpan_of_mem_OC {w : ℝ} {N : ℕ} {f : C(ℝ, ℝ)} (hf : f ∈ OC w N) :
    (f : ℝ → ℝ) ∈ oddSpan w N := by
  unfold OC at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨k, hk, hkN, rfl⟩ := hg
    exact lagP_mem_oddSpan w hk hkN
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

lemma exists_mem_OC_of_mem_oddSpan {w : ℝ} {N : ℕ} {p : ℝ → ℝ} (hp : p ∈ oddSpan w N) :
    ∃ f ∈ OC w N, (f : ℝ → ℝ) = p := by
  refine Submodule.span_induction (p := fun p _ => ∃ f ∈ OC w N, (f : ℝ → ℝ) = p) ?_ ?_ ?_ ?_ hp
  · rintro g ⟨k, hk, hkN, rfl⟩
    exact ⟨lagPC w k, Submodule.subset_span ⟨k, hk, hkN, rfl⟩, rfl⟩
  · exact ⟨0, Submodule.zero_mem _, rfl⟩
  · rintro f g _ _ ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨f' + g', Submodule.add_mem _ hf' hg', rfl⟩
  · rintro c f _ ⟨f', hf', rfl⟩
    exact ⟨c • f', Submodule.smul_mem _ c hf', rfl⟩

lemma exists_N_of_mem_OCall {w : ℝ} {f : C(ℝ, ℝ)} (hf : f ∈ OCall w) :
    ∃ N, f ∈ OC w N := by
  unfold OCall at hf
  refine Submodule.span_induction (p := fun f _ => ∃ N, f ∈ OC w N) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨k, hk, rfl⟩
    exact ⟨k, Submodule.subset_span ⟨k, hk, le_rfl, rfl⟩⟩
  · exact ⟨0, Submodule.zero_mem _⟩
  · rintro f g _ _ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, Submodule.add_mem _ (OC_mono w (le_max_left _ _) h₁)
      (OC_mono w (le_max_right _ _) h₂)⟩
  · rintro c f _ ⟨N, h⟩
    exact ⟨N, Submodule.smul_mem _ c h⟩

section Fn

variable {prob : FixedWeightProblem} {a : ℝ}

lemma integrable_OCall_ref (ha : prob.totalShift ≤ a) {f : C(ℝ, ℝ)}
    (hf : f ∈ OCall (prob.w : ℝ)) : Integrable (f : ℝ → ℝ) (refMeas prob a) := by
  obtain ⟨N, hN⟩ := exists_N_of_mem_OCall hf
  exact integrable_oddSpan_ref ha (coe_mem_oddSpan_of_mem_OC hN)

/-- `𝓛(f) = ∫ f dμ_C` on `⋃ O_N`. -/
noncomputable def Lref (prob : FixedWeightProblem) (a : ℝ) (ha : prob.totalShift ≤ a) :
    OCall (prob.w : ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ t, (f.1 : C(ℝ, ℝ)) t ∂refMeas prob a
  map_add' f g := by
    exact integral_add (integrable_OCall_ref ha f.2) (integrable_OCall_ref ha g.2)
  map_smul' c f := by
    exact integral_const_mul c _

end Fn

section Chain

variable {X : Type*} [TopologicalSpace X]

/-- Precomposition with `t`, as a linear map `C(ℝ, ℝ) → C(X, ℝ)`. -/
def compT (t : C(X, ℝ)) : C(ℝ, ℝ) →ₗ[ℝ] C(X, ℝ) where
  toFun f := f.comp t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma compT_apply (t : C(X, ℝ)) (f : C(ℝ, ℝ)) (x : X) : compT t f x = f (t x) := rfl

/-- The chain `V_N = O_N ∘ t`. -/
def oddV (w : ℝ) (t : C(X, ℝ)) (N : ℕ) : Submodule ℝ C(X, ℝ) := (OC w N).map (compT t)

lemma pc_mem_oddV (w : ℝ) (t : C(X, ℝ)) {j N : ℕ} (hj : Odd j) (hjN : j ≤ N) :
    pc (lagPC w) j t ∈ oddV w t N :=
  ⟨lagPC w j, Submodule.subset_span ⟨j, hj, hjN, rfl⟩, rfl⟩

/-- Polynomial growth `|f(s)| ≤ C (1+s)^N` on `[0, ∞)`, as a submodule. -/
def growthSub (N : ℕ) : Submodule ℝ C(ℝ, ℝ) where
  carrier := {f | ∃ C : ℝ, ∀ s : ℝ, 0 ≤ s → |f s| ≤ C * (1 + s) ^ N}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro f g ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    refine ⟨C₁ + C₂, fun s hs => ?_⟩
    calc |(f + g) s| ≤ |f s| + |g s| := abs_add_le _ _
      _ ≤ C₁ * (1 + s) ^ N + C₂ * (1 + s) ^ N := add_le_add (h₁ s hs) (h₂ s hs)
      _ = (C₁ + C₂) * (1 + s) ^ N := by ring
  smul_mem' := by
    rintro c f ⟨C, h⟩
    refine ⟨|c| * C, fun s hs => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul]
    calc |c| * |f s| ≤ |c| * (C * (1 + s) ^ N) := by gcongr; exact h s hs
      _ = |c| * C * (1 + s) ^ N := by ring

lemma OC_le_growthSub {w : ℝ} (hw : 0 < w) (N : ℕ) : OC w N ≤ growthSub N := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨k, hk, hkN, rfl⟩
  set m : ℝ := max 1 ((1 + w) / π * k) with hm
  refine ⟨m ^ k, fun s hs => ?_⟩
  have h1 := (lagP_oddFam hw).upper k hk s hs
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm2 : (1 + w) / π * k ≤ m := le_max_right _ _
  have h2 : s + (1 + w) / π * k ≤ (1 + s) * m := by nlinarith only [hs, hm1, hm2]
  have h3 : (s + (1 + w) / π * k) ^ k ≤ ((1 + s) * m) ^ k :=
    pow_le_pow_left₀ (by positivity) h2 k
  have h4 : (1 + s) ^ k ≤ (1 + s) ^ N := pow_le_pow_right₀ (by linarith) hkN
  calc |lagPC w k s| ≤ (s + (1 + w) / π * k) ^ k := h1
    _ ≤ ((1 + s) * m) ^ k := h3
    _ = m ^ k * (1 + s) ^ k := by rw [mul_pow]; ring
    _ ≤ m ^ k * (1 + s) ^ N := by gcongr

/-- The hypotheses of `dsl:poly-compact` for the chain `O_N ∘ t`, given a positive majorant. -/
lemma oddV_hyp {w T₀ : ℝ} (hw : 0 < w) (hT₀ : 0 ≤ T₀) {t : C(X, ℝ)} (ht : ∀ x, T₀ ≤ t x)
    (hproper : IsProperMap t)
    (hmaj : ∃ (N₀ : ℕ) (f₀ : C(ℝ, ℝ)) (η : ℝ), Odd N₀ ∧ f₀ ∈ OC w N₀ ∧ 0 < η ∧ ∀ x, η ≤ f₀ (t x)) :
    PolyCompactHyp ((1 + w) / π) (lagPC w) T₀ t (oddV w t) where
  fam := lagP_oddFam hw
  T₀_nonneg := hT₀
  t_ge := ht
  t_proper := hproper
  mono := fun M N _ _ h => Submodule.map_mono (OC_mono w h)
  growth := by
    intro N _ q hq
    obtain ⟨f, hf, rfl⟩ := hq
    obtain ⟨C, hC⟩ := OC_le_growthSub hw N hf
    exact ⟨C, fun x => hC (t x) ((hT₀.trans (ht x)))⟩
  contains := fun N _ j hj hjN => pc_mem_oddV w t hj hjN
  majorant := by
    obtain ⟨N₀, f₀, η, hN₀, hf₀, hη, hfη⟩ := hmaj
    exact ⟨N₀, compT t f₀, η, hN₀, ⟨f₀, hf₀, rfl⟩, hη, hfη⟩

lemma compT_mem_polyUnion {w : ℝ} (t : C(X, ℝ)) {f : C(ℝ, ℝ)} (hf : f ∈ OCall w) :
    compT t f ∈ polyUnion (oddV w t) := by
  obtain ⟨N, hN⟩ := exists_N_of_mem_OCall hf
  exact le_polyUnion (N := 2 * N + 1) ⟨N, rfl⟩ ⟨f, OC_mono w (by omega) hN, rfl⟩

lemma polyUnion_oddV_le_range {w : ℝ} (t : C(X, ℝ)) :
    polyUnion (oddV w t) ≤ LinearMap.range ((compT t).comp (OCall w).subtype) := by
  refine iSup_le fun N => ?_
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨⟨f, OC_le_OCall w N.1 hf⟩, rfl⟩

end Chain

section Functional

variable {prob : FixedWeightProblem} {a : ℝ}

/-- `∫ p dμ_C ≥ 0` for `p ∈ O_N` nonnegative on `X`, when no odd test is feasible on `X`. -/
lemma integral_ref_nonneg_of_noFeasible (ha : prob.totalShift ≤ a) {X : Set ℝ}
    (hno : ∀ N p, ¬ OddFeasible prob a N X p) {N : ℕ} {p : ℝ → ℝ}
    (hp : p ∈ oddSpan (prob.w : ℝ) N) (hnn : ∀ t ∈ X, 0 ≤ p t) : 0 ≤ ∫ t, p t ∂refMeas prob a := by
  by_contra hneg
  push Not at hneg
  refine hno N p ⟨hp, fun t ht => mul_nonneg (Real.exp_pos _).le (hnn t ht), ?_⟩
  rw [gVac_expPoly ha]
  linarith

/-- **The reference functional on `⋃ O_N ∘ t`**.  If no finite odd-Laguerre test is feasible on the
closed set `X ⊂ [T₀, ∞)`, then `𝓛(p ∘ t) = ∫ p dμ_C` defines a linear functional on
`⋃_N O_N ∘ t`, well defined although `p ↦ p ∘ t` need not be injective, which is nonnegative on every
element nonnegative on `X`. -/
theorem exists_functional (ha : prob.totalShift ≤ a) {X : Set ℝ}
    (hno : ∀ N p, ¬ OddFeasible prob a N X p) (t : C(X, ℝ)) (htx : ∀ x : X, t x = x.1) :
    ∃ L : polyUnion (oddV (prob.w : ℝ) t) →ₗ[ℝ] ℝ,
      (∀ (f : C(ℝ, ℝ)) (hf : f ∈ OCall (prob.w : ℝ)),
        L ⟨compT t f, compT_mem_polyUnion _ hf⟩ = ∫ t, f t ∂refMeas prob a) ∧
      ∀ v, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v := by
  set ι' : OCall (prob.w : ℝ) →ₗ[ℝ] C(X, ℝ) := (compT t).comp (OCall (prob.w : ℝ)).subtype with hι'
  have hker : LinearMap.ker ι' ≤ LinearMap.ker (Lref prob a ha) := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    obtain ⟨N, hN⟩ := exists_N_of_mem_OCall f.2
    have hzero : ∀ x : X, f.1 x.1 = 0 := fun x => by
      have := congrArg (fun q : C(X, ℝ) => q x) hf
      simpa [hι', htx] using this
    have hp := coe_mem_oddSpan_of_mem_OC hN
    have h1 := integral_ref_nonneg_of_noFeasible ha hno hp (fun s hs => by
      rw [show f.1 s = 0 from hzero ⟨s, hs⟩])
    have h2 := integral_ref_nonneg_of_noFeasible ha hno (Submodule.neg_mem _ hp) (fun s hs => by
      simp only [Pi.neg_apply]; rw [show f.1 s = 0 from hzero ⟨s, hs⟩]; simp)
    simp only [Pi.neg_apply, integral_neg] at h2
    show ∫ t, (f.1 : C(ℝ, ℝ)) t ∂refMeas prob a = 0
    linarith
  let L₀ : LinearMap.range ι' →ₗ[ℝ] ℝ :=
    ((LinearMap.ker ι').liftQ (Lref prob a ha) hker).comp ι'.quotKerEquivRange.symm.toLinearMap
  have hL₀ : ∀ (f : OCall (prob.w : ℝ)) (h : ι' f ∈ LinearMap.range ι'),
      L₀ ⟨ι' f, h⟩ = Lref prob a ha f := by
    intro f h
    simp only [L₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : polyUnion (oddV (prob.w : ℝ) t) →ₗ[ℝ] ℝ :=
    L₀.comp (Submodule.inclusion (polyUnion_oddV_le_range t))
  refine ⟨L, fun f hf => ?_, fun v hv => ?_⟩
  · exact hL₀ ⟨f, hf⟩ _
  · obtain ⟨f, hf⟩ := polyUnion_oddV_le_range t v.2
    obtain ⟨N, hN⟩ := exists_N_of_mem_OCall f.2
    have hLv : L v = Lref prob a ha f := by
      have : (⟨v.1, polyUnion_oddV_le_range t v.2⟩ : LinearMap.range ι') = ⟨ι' f, ⟨f, rfl⟩⟩ :=
        Subtype.ext hf.symm
      show L₀ ⟨v.1, polyUnion_oddV_le_range t v.2⟩ = _
      rw [this]; exact hL₀ f _
    rw [hLv]
    have hp := coe_mem_oddSpan_of_mem_OC hN
    refine integral_ref_nonneg_of_noFeasible ha hno hp (fun s hs => ?_)
    have := hv ⟨s, hs⟩
    rw [← hf] at this
    simpa [hι', htx] using this

end Functional

end FormalResearch.ModularBootstrap.LP

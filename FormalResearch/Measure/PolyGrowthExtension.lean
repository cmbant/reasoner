module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Positive extension to continuous functions of polynomial growth, and Riesz-Markov packaging

Abstract engine of `dsl:poly-compact` (Lemma LP-P of `CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`),
with no reference to Laguerre polynomials.

Data: a locally compact Hausdorff space `X`; a continuous `t : X → ℝ` which is *proper*
(`{|t| ≤ R}` compact for every `R`); a submodule `V` of the continuous functions of polynomial growth
in `t` (`polyGrowth t`) which carries *coercive majorants* (for every `k` an `h ∈ V` with
`(1 + |t|)^k ≤ h`); and a linear functional `L : V → ℝ` which is positive on `X`.

`exists_measure_of_positive_polyGrowth` produces a positive Radon (regular, finite on compacts)
measure `μ` on `X` with `∫ v dμ = L v` for every `v ∈ V`, and `(1 + |t|)^k ∈ L¹(μ)` for every `k`.

The proof is the paper's: the sublinear functional `p(f) = inf {L v : v ≥ f}` on `polyGrowth t`, the
real Hahn-Banach extension `Λ ≤ p` (`exists_extension_of_le_sublinear`), the Riesz-Markov
representation of `Λ|_{C_c}` (`RealRMK.rieszMeasure`), and the cutoff argument with `χ(|t|/R)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported ENNReal Pointwise

namespace FormalResearch.Measure

variable {X : Type*} [TopologicalSpace X]

/-- The continuous real functions on `X` of polynomial growth in `t`:
`|f| ≤ C (1 + |t|)^k` for some `C`, `k`. -/
def polyGrowth (t : X → ℝ) : Submodule ℝ C(X, ℝ) where
  carrier := {f | ∃ (C : ℝ) (k : ℕ), ∀ x, |f x| ≤ C * (1 + |t x|) ^ k}
  zero_mem' := ⟨0, 0, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨C₁, k₁, h₁⟩ ⟨C₂, k₂, h₂⟩
    refine ⟨|C₁| + |C₂|, max k₁ k₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + |t x| := by linarith [abs_nonneg (t x)]
    have e1 : (1 + |t x|) ^ k₁ ≤ (1 + |t x|) ^ max k₁ k₂ := pow_le_pow_right₀ h1 (le_max_left _ _)
    have e2 : (1 + |t x|) ^ k₂ ≤ (1 + |t x|) ^ max k₁ k₂ := pow_le_pow_right₀ h1 (le_max_right _ _)
    have p1 : 0 ≤ (1 + |t x|) ^ k₁ := by positivity
    have p2 : 0 ≤ (1 + |t x|) ^ k₂ := by positivity
    calc |(f + g) x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ C₁ * (1 + |t x|) ^ k₁ + C₂ * (1 + |t x|) ^ k₂ := add_le_add (h₁ x) (h₂ x)
      _ ≤ |C₁| * (1 + |t x|) ^ k₁ + |C₂| * (1 + |t x|) ^ k₂ := by
          gcongr <;> exact le_abs_self _
      _ ≤ (|C₁| + |C₂|) * (1 + |t x|) ^ max k₁ k₂ := by
          rw [add_mul]; gcongr
  smul_mem' := by
    rintro c f ⟨C, k, h⟩
    refine ⟨|c| * C, k, fun x => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul]
    calc |c| * |f x| ≤ |c| * (C * (1 + |t x|) ^ k) := by gcongr; exact h x
      _ = |c| * C * (1 + |t x|) ^ k := by ring

lemma mem_polyGrowth {t : X → ℝ} {f : C(X, ℝ)} :
    f ∈ polyGrowth t ↔ ∃ (C : ℝ) (k : ℕ), ∀ x, |f x| ≤ C * (1 + |t x|) ^ k := Iff.rfl


/-! ### Positive extension (Hahn-Banach) -/

section Extension

variable {t : X → ℝ}

/-- The monomial weight `(1 + |t|)^k` as an element of `polyGrowth t`. -/
noncomputable def wpow (ht : Continuous t) (k : ℕ) : polyGrowth t :=
  ⟨⟨fun x => (1 + |t x|) ^ k, by fun_prop⟩, 1, k, fun x => by
    simp only [ContinuousMap.coe_mk, one_mul]
    exact le_of_eq (abs_of_nonneg (by positivity))⟩

@[simp] lemma wpow_apply (ht : Continuous t) (k : ℕ) (x : X) :
    (wpow ht k).1 x = (1 + |t x|) ^ k := rfl

/-- Upper bound of an element of `polyGrowth t` by a coercive majorant: if `|f| ≤ C (1+|t|)^k`
and `(1+|t|)^k ≤ h` then `|f| ≤ |C| h`. -/
private lemma abs_le_of_majorant {f : C(X, ℝ)} {h : X → ℝ} {C : ℝ} {k : ℕ}
    (hf : ∀ x, |f x| ≤ C * (1 + |t x|) ^ k) (hh : ∀ x, (1 + |t x|) ^ k ≤ h x) (x : X) :
    |f x| ≤ |C| * h x := by
  calc |f x| ≤ C * (1 + |t x|) ^ k := hf x
    _ ≤ |C| * (1 + |t x|) ^ k := by gcongr; exact le_abs_self _
    _ ≤ |C| * h x := by gcongr; exact hh x

/-- **Positive extension** (the Hahn-Banach step of `dsl:poly-compact`). Let `V ≤ polyGrowth t`
carry coercive majorants and let `L : V → ℝ` be linear and positive on `X`. Then `L` extends to a
linear functional `Λ` on `polyGrowth t` which is positive on `X`. -/
theorem exists_positive_extension (V : Submodule ℝ C(X, ℝ)) (hV : V ≤ polyGrowth t)
    (hcoer : ∀ k : ℕ, ∃ h ∈ V, ∀ x, (1 + |t x|) ^ k ≤ h x)
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ v : V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v) :
    ∃ Λ : polyGrowth t →ₗ[ℝ] ℝ, (∀ v : V, Λ ⟨v.1, hV v.2⟩ = L v) ∧
      ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → 0 ≤ Λ f := by
  classical
  -- the upper set of `f`
  let S : polyGrowth t → Set ℝ := fun f => {r | ∃ v : V, (∀ x, f.1 x ≤ v.1 x) ∧ r = L v}
  have hSne : ∀ f, (S f).Nonempty := by
    intro f
    obtain ⟨C, k, hf⟩ := f.2
    obtain ⟨h, hhV, hh⟩ := hcoer k
    refine ⟨L (|C| • ⟨h, hhV⟩), |C| • ⟨h, hhV⟩, fun x => ?_, rfl⟩
    have := abs_le_of_majorant hf hh x
    simp only [Submodule.coe_smul, ContinuousMap.smul_apply, smul_eq_mul]
    exact (le_abs_self _).trans this
  have hSbdd : ∀ f, BddBelow (S f) := by
    intro f
    obtain ⟨C, k, hf⟩ := f.2
    obtain ⟨h, hhV, hh⟩ := hcoer k
    refine ⟨-(|C| * L ⟨h, hhV⟩), ?_⟩
    rintro r ⟨v, hv, rfl⟩
    have hpos : 0 ≤ L (v + |C| • ⟨h, hhV⟩) := by
      refine hL _ fun x => ?_
      have := abs_le_of_majorant hf hh x
      have h2 := hv x
      simp only [Submodule.coe_add, Submodule.coe_smul, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      linarith [neg_abs_le (f.1 x)]
    rw [map_add, map_smul, smul_eq_mul] at hpos
    linarith
  let N : polyGrowth t → ℝ := fun f => sInf (S f)
  have hN_le : ∀ (f : polyGrowth t) (v : V), (∀ x, f.1 x ≤ v.1 x) → N f ≤ L v :=
    fun f v hv => csInf_le (hSbdd f) ⟨v, hv, rfl⟩
  have hN_hom : ∀ c : ℝ, 0 < c → ∀ f, N (c • f) = c * N f := by
    intro c hc f
    have hset : S (c • f) = c • S f := by
      ext r
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨L (c⁻¹ • v), ⟨c⁻¹ • v, fun x => ?_, rfl⟩, ?_⟩
        · have := hv x
          simp only [Submodule.coe_smul, ContinuousMap.smul_apply, smul_eq_mul] at this ⊢
          rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
        · simp only [map_smul, smul_eq_mul]; field_simp
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨c • v, fun x => ?_, ?_⟩
        · have := hv x
          simp only [Submodule.coe_smul, ContinuousMap.smul_apply, smul_eq_mul] at this ⊢
          nlinarith
        · simp only [map_smul, smul_eq_mul]
    show sInf (S (c • f)) = c * sInf (S f)
    rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  have hN_add : ∀ f g, N (f + g) ≤ N f + N g := by
    intro f g
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨_, ⟨v, hv, rfl⟩, hvlt⟩ := exists_lt_of_csInf_lt (hSne f) (show N f < N f + ε / 2 by linarith)
    obtain ⟨_, ⟨u, hu, rfl⟩, hult⟩ := exists_lt_of_csInf_lt (hSne g) (show N g < N g + ε / 2 by linarith)
    have := hN_le (f + g) (v + u) (fun x => by
      simp only [ContinuousMap.add_apply, AddMemClass.coe_add]
      exact add_le_add (hv x) (hu x))
    rw [map_add] at this
    linarith
  -- the partial functional `L` on `V`
  let ι : V →ₗ[ℝ] polyGrowth t :=
    { toFun := fun v => ⟨v.1, hV v.2⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hι_inj : Function.Injective ι := fun a b h => Subtype.ext (congrArg (fun z : polyGrowth t => z.1) h)
  let f₀ : polyGrowth t →ₗ.[ℝ] ℝ :=
    ⟨LinearMap.range ι, L ∘ₗ (LinearEquiv.ofInjective ι hι_inj).symm.toLinearMap⟩
  have hf₀ : ∀ x : f₀.domain, f₀ x ≤ N x := by
    rintro ⟨_, v, rfl⟩
    have h1 : f₀ ⟨ι v, v, rfl⟩ = L v := by
      show L ((LinearEquiv.ofInjective ι hι_inj).symm ⟨ι v, v, rfl⟩) = L v
      congr 1
      exact (LinearEquiv.ofInjective ι hι_inj).symm_apply_eq.2 rfl
    rw [h1]
    refine le_csInf (hSne _) ?_
    rintro r ⟨u, hu, rfl⟩
    have := hL (u - ⟨v.1, v.2⟩) (fun x => by
      have hux : v.1 x ≤ u.1 x := hu x
      simp only [Submodule.coe_sub, ContinuousMap.sub_apply]
      linarith)
    rw [map_sub] at this
    linarith
  obtain ⟨Λ, hΛ_ext, hΛ_le⟩ := exists_extension_of_le_sublinear f₀ N hN_hom hN_add hf₀
  refine ⟨Λ, fun v => ?_, fun f hf => ?_⟩
  · have := hΛ_ext ⟨ι v, v, rfl⟩
    rw [show (⟨v.1, hV v.2⟩ : polyGrowth t) = ι v from rfl, this]
    show L ((LinearEquiv.ofInjective ι hι_inj).symm ⟨ι v, v, rfl⟩) = L v
    congr 1
    exact (LinearEquiv.ofInjective ι hι_inj).symm_apply_eq.2 rfl
  · have h1 : Λ (-f) ≤ N (-f) := hΛ_le (-f)
    have h2 : N (-f) ≤ L 0 := hN_le (-f) 0 (fun x => by
      simp only [Submodule.coe_neg, ContinuousMap.neg_apply, ZeroMemClass.coe_zero,
        ContinuousMap.zero_apply]
      linarith [hf x])
    rw [map_zero] at h2
    rw [map_neg] at h1
    linarith

end Extension


/-! ### Riesz-Markov packaging and the cutoff argument -/

section Riesz

variable [T2Space X] {t : X → ℝ}

/-- Piecewise-linear cutoff: `1` on `(-∞, 1]`, `0` on `[2, ∞)`. -/
private noncomputable def chi (s : ℝ) : ℝ := max 0 (min 1 (2 - s))

private lemma continuous_chi : Continuous chi := by unfold chi; fun_prop

private lemma chi_nonneg (s : ℝ) : 0 ≤ chi s := le_max_left _ _

private lemma chi_le_one (s : ℝ) : chi s ≤ 1 := max_le zero_le_one (min_le_left _ _)

private lemma chi_of_le_one {s : ℝ} (h : s ≤ 1) : chi s = 1 := by
  unfold chi
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

private lemma chi_of_ge_two {s : ℝ} (h : 2 ≤ s) : chi s = 0 := by
  unfold chi
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

/-- The cutoff `χ(|t|/R) · f` as a continuous map. -/
private noncomputable def cutMap (ht : Continuous t) (R : ℝ) (f : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => chi (|t x| / R) * f x,
    (continuous_chi.comp (ht.abs.div_const R)).mul f.continuous⟩

omit [T2Space X] in
private lemma cutMap_apply (ht : Continuous t) (R : ℝ) (f : C(X, ℝ)) (x : X) :
    cutMap ht R f x = chi (|t x| / R) * f x := rfl

private lemma cutMap_hasCompactSupport (ht : Continuous t) (hproper : ∀ R : ℝ, IsCompact {x | |t x| ≤ R})
    {R : ℝ} (hR : 0 < R) (f : C(X, ℝ)) : HasCompactSupport (cutMap ht R f) := by
  refine HasCompactSupport.intro (hproper (2 * R)) fun x hx => ?_
  have hx' : 2 * R < |t x| := not_le.1 hx
  rw [cutMap_apply, chi_of_ge_two, zero_mul]
  rw [le_div_iff₀ hR]; linarith

/-- The cutoff of `f` as a compactly supported continuous map. -/
private noncomputable def cutCc (ht : Continuous t) (hproper : ∀ R : ℝ, IsCompact {x | |t x| ≤ R}) {R : ℝ}
    (hR : 0 < R) (f : C(X, ℝ)) : C_c(X, ℝ) :=
  ⟨cutMap ht R f, cutMap_hasCompactSupport ht hproper hR f⟩

omit [T2Space X] in
private lemma cutMap_mem (ht : Continuous t) {R : ℝ} (_hR : 0 < R) {f : C(X, ℝ)}
    (hf : f ∈ polyGrowth t) : cutMap ht R f ∈ polyGrowth t := by
  obtain ⟨C, k, h⟩ := hf
  refine ⟨C, k, fun x => ?_⟩
  rw [cutMap_apply, abs_mul, abs_of_nonneg (chi_nonneg _)]
  calc chi (|t x| / R) * |f x| ≤ 1 * |f x| := by
        gcongr; exact chi_le_one _
    _ ≤ C * (1 + |t x|) ^ k := by rw [one_mul]; exact h x

omit [T2Space X] in
/-- Every compactly supported continuous map has polynomial growth. -/
private lemma ccMem (g : C_c(X, ℝ)) : (g : C(X, ℝ)) ∈ polyGrowth t := by
  obtain ⟨C, hC⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  exact ⟨C, 0, fun x => by simpa using hC x⟩

variable [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A positive linear functional on `polyGrowth t` restricts to a positive linear functional on
`C_c(X, ℝ)`. -/
private noncomputable def ccFunctional (Λ : polyGrowth t →ₗ[ℝ] ℝ) (hΛ : ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → 0 ≤ Λ f) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g => Λ ⟨(g : C(X, ℝ)), ccMem g⟩
      map_add' := fun a b => by
        rw [← map_add]; rfl
      map_smul' := fun c a => by
        rw [← map_smul]; rfl }
    (fun g hg => hΛ _ fun x => hg x)

/-- The cutoff as an element of `polyGrowth t`. -/
private noncomputable def cutE (ht : Continuous t) {R : ℝ} (hR : 0 < R) (f : polyGrowth t) : polyGrowth t :=
  ⟨cutMap ht R f.1, cutMap_mem ht hR f.2⟩

omit [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
private lemma abs_functional_le (Λ : polyGrowth t →ₗ[ℝ] ℝ)
    (hΛ : ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → 0 ≤ Λ f) {u a : polyGrowth t}
    (h : ∀ x, |u.1 x| ≤ a.1 x) : |Λ u| ≤ Λ a := by
  have h1 : 0 ≤ Λ (a - u) := hΛ _ fun x => by
    simp only [Submodule.coe_sub, ContinuousMap.sub_apply]
    linarith [le_abs_self (u.1 x), h x]
  have h2 : 0 ≤ Λ (a + u) := hΛ _ fun x => by
    simp only [Submodule.coe_add, ContinuousMap.add_apply]
    linarith [neg_abs_le (u.1 x), h x]
  rw [map_sub] at h1
  rw [map_add] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Riesz-Markov packaging.** A positive linear functional on the continuous functions of
polynomial growth in a proper coordinate `t` is integration against a positive Radon measure, and
every function of polynomial growth is integrable. -/
theorem exists_measure_of_positive_functional (ht : Continuous t)
    (hproper : ∀ R : ℝ, IsCompact {x | |t x| ≤ R})
    (Λ : polyGrowth t →ₗ[ℝ] ℝ) (hΛ : ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → 0 ≤ Λ f) :
    ∃ μ : Measure X, μ.Regular ∧
      ∀ f : polyGrowth t, Integrable f.1 μ ∧ ∫ x, f.1 x ∂μ = Λ f := by
  set μ := RealRMK.rieszMeasure (ccFunctional Λ hΛ) with hμ
  -- the cutoff integral is `Λ` of the cutoff
  have hcut : ∀ {R : ℝ} (hR : 0 < R) (f : polyGrowth t),
      ∫ x, (cutE ht hR f).1 x ∂μ = Λ (cutE ht hR f) := by
    intro R hR f
    have := RealRMK.integral_rieszMeasure (ccFunctional Λ hΛ) (cutCc ht hproper hR f.1)
    exact this
  have hcut_int : ∀ {R : ℝ} (hR : 0 < R) (f : polyGrowth t), Integrable (cutE ht hR f).1 μ :=
    fun {R} hR f => (cutCc ht hproper hR f.1).integrable
  -- nonnegative functions: integrable with `∫ f ≤ Λ f`
  have hnonneg : ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → Integrable f.1 μ ∧ ∫ x, f.1 x ∂μ ≤ Λ f := by
    intro f hf
    have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
    let F : ℕ → X → ℝ≥0∞ := fun n x => ENNReal.ofReal ((cutE ht (hRpos n) f).1 x)
    have hFmeas : ∀ n, Measurable (F n) := fun n =>
      ENNReal.measurable_ofReal.comp (cutE ht (hRpos n) f).1.continuous.measurable
    have hFint : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal (Λ f) := by
      intro n
      have hnn : ∀ x, 0 ≤ (cutE ht (hRpos n) f).1 x := fun x => by
        show 0 ≤ chi _ * f.1 x
        exact mul_nonneg (chi_nonneg _) (hf x)
      have h1 : ∫⁻ x, F n x ∂μ = ENNReal.ofReal (∫ x, (cutE ht (hRpos n) f).1 x ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hcut_int (hRpos n) f)
          (Eventually.of_forall hnn)).symm
      rw [h1]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hcut]
      have : 0 ≤ Λ (f - cutE ht (hRpos n) f) := hΛ _ fun x => by
        simp only [Submodule.coe_sub, ContinuousMap.sub_apply]
        show 0 ≤ f.1 x - chi _ * f.1 x
        nlinarith [chi_le_one (|t x| / ((n : ℝ) + 1)), hf x]
      rw [map_sub] at this
      linarith
    have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (f.1 x))) := by
      intro x
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨n₀, hn₀⟩ := exists_nat_ge (|t x|)
      filter_upwards [eventually_ge_atTop n₀] with n hn
      show ENNReal.ofReal (f.1 x) = ENNReal.ofReal (chi _ * f.1 x)
      rw [chi_of_le_one, one_mul]
      rw [div_le_one (hRpos n)]
      have : (n₀ : ℝ) ≤ n := Nat.cast_le.2 hn
      linarith
    have hfat : ∫⁻ x, ENNReal.ofReal (f.1 x) ∂μ ≤ ENNReal.ofReal (Λ f) := by
      calc ∫⁻ x, ENNReal.ofReal (f.1 x) ∂μ = ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
            congr 1; ext x; exact ((hlim x).liminf_eq).symm
        _ ≤ liminf (fun n => ∫⁻ x, F n x ∂μ) atTop := lintegral_liminf_le hFmeas
        _ ≤ ENNReal.ofReal (Λ f) :=
            liminf_le_of_frequently_le' (Frequently.of_forall hFint)
    have hint : Integrable f.1 μ := by
      refine ⟨f.1.continuous.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf)]
      exact lt_of_le_of_lt hfat ENNReal.ofReal_lt_top
    refine ⟨hint, ?_⟩
    have := ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf)
    rw [← this] at hfat
    exact (ENNReal.ofReal_le_ofReal_iff (hΛ f hf)).1 hfat
  refine ⟨μ, inferInstance, fun f => ?_⟩
  obtain ⟨C, k, hCk⟩ := f.2
  set W := wpow ht (k + 1) with hW
  have hWnn : ∀ x, 0 ≤ W.1 x := fun x => by simp [hW]; positivity
  obtain ⟨hWint, hWle⟩ := hnonneg W hWnn
  have hfW : ∀ x, |f.1 x| ≤ |C| * W.1 x := fun x => by
    have h1 : (1 : ℝ) ≤ 1 + |t x| := by linarith [abs_nonneg (t x)]
    calc |f.1 x| ≤ C * (1 + |t x|) ^ k := hCk x
      _ ≤ |C| * (1 + |t x|) ^ k := by gcongr; exact le_abs_self _
      _ ≤ |C| * (1 + |t x|) ^ (k + 1) := by
          gcongr; exact Nat.le_succ k
      _ = |C| * W.1 x := by simp [hW]
  have hfint : Integrable f.1 μ :=
    (hWint.const_mul |C|).mono' f.1.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfW x)
  refine ⟨hfint, ?_⟩
  -- the tail estimate
  have hΛW : 0 ≤ Λ W := hΛ W hWnn
  have htail : ∀ n : ℕ, |Λ f - ∫ x, f.1 x ∂μ| ≤ 2 * (|C| / ((n : ℝ) + 2)) * Λ W := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set g : polyGrowth t := f - cutE ht hR f with hg
    have hgb : ∀ x, |g.1 x| ≤ (|C| / ((n : ℝ) + 2)) * W.1 x := by
      intro x
      have hgx : g.1 x = (1 - chi (|t x| / ((n : ℝ) + 1))) * f.1 x := by
        simp only [hg, Submodule.coe_sub, ContinuousMap.sub_apply]
        show f.1 x - chi _ * f.1 x = _
        ring
      by_cases hx : |t x| ≤ (n : ℝ) + 1
      · rw [hgx, chi_of_le_one ((div_le_one hR).2 hx)]
        simp only [sub_self, zero_mul, abs_zero]
        exact mul_nonneg (by positivity) (hWnn x)
      · push Not at hx
        have h0 : 0 ≤ 1 - chi (|t x| / ((n : ℝ) + 1)) := by linarith [chi_le_one (|t x| / ((n : ℝ) + 1))]
        have h1' : 1 - chi (|t x| / ((n : ℝ) + 1)) ≤ 1 := by linarith [chi_nonneg (|t x| / ((n : ℝ) + 1))]
        have h2 : |g.1 x| ≤ |f.1 x| := by
          rw [hgx, abs_mul, abs_of_nonneg h0]
          calc _ ≤ 1 * |f.1 x| := by gcongr
            _ = _ := one_mul _
        have h3 : (1 + |t x|) ^ (k + 1) = (1 + |t x|) ^ k * (1 + |t x|) := pow_succ _ _
        have h4 : (n : ℝ) + 2 ≤ 1 + |t x| := by linarith
        have h5 : 0 ≤ (1 + |t x|) ^ k := by positivity
        have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        calc |g.1 x| ≤ |f.1 x| := h2
          _ ≤ |C| * (1 + |t x|) ^ k := (hCk x).trans (by gcongr; exact le_abs_self _)
          _ ≤ (|C| / ((n : ℝ) + 2)) * W.1 x := by
              simp only [hW, wpow_apply]
              rw [h3, div_mul_eq_mul_div, le_div_iff₀ hpos]
              calc |C| * (1 + |t x|) ^ k * ((n : ℝ) + 2)
                  ≤ |C| * (1 + |t x|) ^ k * (1 + |t x|) := by gcongr
                _ = |C| * ((1 + |t x|) ^ k * (1 + |t x|)) := by ring
    have hΛg : |Λ g| ≤ (|C| / ((n : ℝ) + 2)) * Λ W := by
      have := abs_functional_le Λ hΛ (u := g) (a := ((|C| / ((n : ℝ) + 2)) • W)) (fun x => by
        simpa using hgb x)
      simpa [map_smul] using this
    have hIg : |∫ x, g.1 x ∂μ| ≤ (|C| / ((n : ℝ) + 2)) * Λ W := by
      have hgi : Integrable g.1 μ := by
        have := hfint.sub (hcut_int hR f)
        exact this
      calc |∫ x, g.1 x ∂μ| = ‖∫ x, g.1 x ∂μ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, (|C| / ((n : ℝ) + 2)) * W.1 x ∂μ :=
            norm_integral_le_of_norm_le (hWint.const_mul _)
              (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x)
        _ = (|C| / ((n : ℝ) + 2)) * ∫ x, W.1 x ∂μ := integral_const_mul _ _
        _ ≤ (|C| / ((n : ℝ) + 2)) * Λ W := by gcongr
    have hsplit : Λ f - ∫ x, f.1 x ∂μ = Λ g - ∫ x, g.1 x ∂μ := by
      have h1 : Λ g = Λ f - Λ (cutE ht hR f) := by rw [hg, map_sub]
      have h2 : ∫ x, g.1 x ∂μ = ∫ x, f.1 x ∂μ - ∫ x, (cutE ht hR f).1 x ∂μ := by
        rw [hg]
        simp only [Submodule.coe_sub, ContinuousMap.coe_sub]
        exact integral_sub hfint (hcut_int hR f)
      rw [h1, h2, hcut]; ring
    rw [hsplit]
    calc |Λ g - ∫ x, g.1 x ∂μ| ≤ |Λ g| + |∫ x, g.1 x ∂μ| := abs_sub _ _
      _ ≤ 2 * (|C| / ((n : ℝ) + 2)) * Λ W := by linarith
  -- conclude
  by_contra hne
  have hd : 0 < |Λ f - ∫ x, f.1 x ∂μ| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |C| * Λ W / |Λ f - ∫ x, f.1 x ∂μ|)
  have := htail n
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [div_lt_iff₀ hd] at hn
  have h3 : 2 * (|C| / ((n : ℝ) + 2)) * Λ W = (2 * |C| * Λ W) / ((n : ℝ) + 2) := by ring
  rw [h3, le_div_iff₀ hpos] at this
  nlinarith [hd]


/-- **Positive Radon measure from a positive extension** (`dsl:poly-compact`, abstract form).
Let `t : X → ℝ` be continuous and proper, `V ≤ polyGrowth t` a submodule carrying coercive
majorants (`(1+|t|)^k ≤ h ∈ V` for every `k`), and `L : V → ℝ` linear and positive on `X`. Then
there is a regular (positive Radon) measure `μ` on `X` for which every continuous function of
polynomial growth in `t` is integrable and `∫ v dμ = L v` for all `v ∈ V`. -/
theorem exists_measure_of_positive_polyGrowth (ht : Continuous t)
    (hproper : ∀ R : ℝ, IsCompact {x | |t x| ≤ R})
    (V : Submodule ℝ C(X, ℝ)) (hV : V ≤ polyGrowth t)
    (hcoer : ∀ k : ℕ, ∃ h ∈ V, ∀ x, (1 + |t x|) ^ k ≤ h x)
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ v : V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v) :
    ∃ μ : Measure X, μ.Regular ∧ (∀ f ∈ polyGrowth t, Integrable f μ) ∧
      ∀ v : V, ∫ x, v.1 x ∂μ = L v := by
  obtain ⟨Λ, hΛL, hΛpos⟩ := exists_positive_extension V hV hcoer L hL
  obtain ⟨μ, hμ, hint⟩ := exists_measure_of_positive_functional ht hproper Λ hΛpos
  refine ⟨μ, hμ, fun f hf => (hint ⟨f, hf⟩).1, fun v => ?_⟩
  rw [(hint ⟨v.1, hV v.2⟩).2, hΛL]

end Riesz

/-! ### Invariance under a finite group -/

section Group

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] {t : X → ℝ}
  {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

/-- Precomposition with the action of `g`. -/
def actComp (g : G) (f : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => f (g • x), f.continuous.comp (continuous_const_smul g)⟩

omit [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma actComp_apply (g : G) (f : C(X, ℝ)) (x : X) : actComp g f x = f (g • x) := rfl

omit [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma actComp_mem {g : G} (htg : ∀ x, t (g • x) = t x) {f : C(X, ℝ)} (hf : f ∈ polyGrowth t) :
    actComp g f ∈ polyGrowth t := by
  obtain ⟨C, k, h⟩ := hf
  exact ⟨C, k, fun x => by rw [actComp_apply, ← htg x]; exact h _⟩

/-- Precomposition with `g` as a linear endomorphism of `polyGrowth t`. -/
def actE (htg : ∀ g : G, ∀ x, t (g • x) = t x) (g : G) : polyGrowth t →ₗ[ℝ] polyGrowth t where
  toFun f := ⟨actComp g f.1, actComp_mem (htg g) f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Invariant version of `exists_measure_of_positive_polyGrowth`** for a finite group `G`
acting continuously on `X`, preserving `t`, `V` and `L`: the measure may be chosen
`G`-invariant. -/
theorem exists_invariant_measure_of_positive_polyGrowth [Finite G]
    (ht : Continuous t) (hproper : ∀ R : ℝ, IsCompact {x | |t x| ≤ R})
    (htg : ∀ g : G, ∀ x, t (g • x) = t x)
    (V : Submodule ℝ C(X, ℝ)) (hV : V ≤ polyGrowth t)
    (hcoer : ∀ k : ℕ, ∃ h ∈ V, ∀ x, (1 + |t x|) ^ k ≤ h x)
    (hVg : ∀ g : G, ∀ v ∈ V, actComp g v ∈ V)
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ v : V, (∀ x, 0 ≤ v.1 x) → 0 ≤ L v)
    (hLg : ∀ (g : G) (v : V), L ⟨actComp g v.1, hVg g v.1 v.2⟩ = L v) :
    ∃ μ : Measure X, μ.Regular ∧ (∀ f ∈ polyGrowth t, Integrable f μ) ∧
      (∀ v : V, ∫ x, v.1 x ∂μ = L v) ∧ ∀ g : G, Measure.map (fun x => g • x) μ = μ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨Λ, hΛL, hΛpos⟩ := exists_positive_extension V hV hcoer L hL
  -- average `Λ` over `G`
  let ΛG : polyGrowth t →ₗ[ℝ] ℝ := (Fintype.card G : ℝ)⁻¹ • ∑ g : G, Λ ∘ₗ actE htg g
  have hcard : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
  have hΛG_apply : ∀ f, ΛG f = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, Λ (actE htg g f) := by
    intro f
    simp [ΛG, LinearMap.sum_apply]
  have hΛG_pos : ∀ f : polyGrowth t, (∀ x, 0 ≤ f.1 x) → 0 ≤ ΛG f := by
    intro f hf
    rw [hΛG_apply]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => hΛpos _ fun x => hf _)
  have hΛG_inv : ∀ (h : G) (f : polyGrowth t), ΛG (actE htg h f) = ΛG f := by
    intro h f
    rw [hΛG_apply, hΛG_apply]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    congr 1
    apply Subtype.ext
    ext x
    show f.1 (h • (g • x)) = f.1 ((h * g) • x)
    rw [mul_smul]
  have hΛG_V : ∀ v : V, ΛG ⟨v.1, hV v.2⟩ = L v := by
    intro v
    rw [hΛG_apply]
    have : ∀ g : G, Λ (actE htg g ⟨v.1, hV v.2⟩) = L v := fun g => by
      have := hΛL ⟨actComp g v.1, hVg g v.1 v.2⟩
      rw [hLg] at this
      exact this
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  obtain ⟨μ, hμ, hint⟩ := exists_measure_of_positive_functional ht hproper ΛG hΛG_pos
  refine ⟨μ, hμ, fun f hf => (hint ⟨f, hf⟩).1, fun v => ?_, fun h => ?_⟩
  · rw [(hint ⟨v.1, hV v.2⟩).2, hΛG_V]
  · have : (Measure.map (fun x => h • x) μ).Regular :=
      Measure.Regular.map (Homeomorph.smul h)
    refine Measure.ext_of_integral_eq_on_compactlySupported (fun g => ?_)
    have hmeas : Measurable (fun x : X => h • x) := (continuous_const_smul h).measurable
    have hmap : ∫ x, g x ∂(Measure.map (fun x => h • x) μ) = ∫ x, g (h • x) ∂μ :=
      integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable
    rw [hmap]
    have h1 := (hint (actE htg h ⟨(g : C(X, ℝ)), ccMem g⟩)).2
    have h2 := (hint ⟨(g : C(X, ℝ)), ccMem g⟩).2
    rw [hΛG_inv] at h1
    exact h1.trans h2.symm

end Group

/-- info: 'FormalResearch.Measure.exists_measure_of_positive_polyGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Measure.exists_measure_of_positive_polyGrowth

/-- info: 'FormalResearch.Measure.exists_invariant_measure_of_positive_polyGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Measure.exists_invariant_measure_of_positive_polyGrowth

end FormalResearch.Measure

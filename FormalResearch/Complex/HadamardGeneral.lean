module

public import FormalResearch.Complex.HadamardMain

/-!
# Hadamard's factorization theorem (general form, zero of order `m` at the origin)

Statement formalised (Hadamard 1893; Boas, *Entire functions*, Thm 2.7.1; Titchmarsh, *The theory of functions*,
8.24; Conway, *Functions of one complex variable I*, VII.5.1; Stein–Shakarchi, *Complex analysis*, V.5.1):

> Let `f` be entire, `f ≢ 0`, of order at most `σ > 0` in the form `‖f z‖ ≤ C exp (C ‖z‖^σ)`.  Let `a` list the nonzero
> zeros of `f` with multiplicity (any `Hadamard.Listing`, e.g. a function `ℕ → ℂ`), let `m` be the order of `f` at `0`, and let
> `p ∈ ℕ` with `σ < p + 1` (for instance `p = ⌊σ⌋`, `Hadamard.hadamard_floor`).  Then `Σ ‖a_i‖^{-(p+1)} < ∞`, the genus-`p`
> canonical product `∏ E_p (z/a_i)` converges locally uniformly, and there are `c ≠ 0` and a polynomial `P` with
> `deg P ≤ p`, `P 0 = 0`, such that `f z = c z^m exp (P z) ∏ E_p (z / a_i)` for all `z`.

(`Hadamard.hadamard`.)  For non-integer `σ` the choice `p = ⌊σ⌋` is the classical one (genus `≤ σ`, degree `≤ σ`); for integer
`σ` it gives the classical theorem with genus/degree `≤ σ` (the theorem as stated needs only `σ < p + 1`, so it covers the
borderline case `p = σ` as well).  **Proved**; not formalised: the converse direction (that every such product has order `≤ σ`),
the identification of the exact order (convergence exponent), and the multiplicity of the zeros of `canonProd` as a
separate statement (it is implied by the identity here).
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical Nat

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- An entire function `f ≢ 0` is `z^m g` with `g` entire, `g 0 ≠ 0`, `m` the order of `f` at `0`. -/
lemma exists_factor_pow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
      ∀ z, f z = z ^ analyticOrderNatAt f 0 * g z := by
  obtain ⟨z₁, hz₁⟩ := hne
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  have hord : analyticOrderAt f 0 ≠ ⊤ := by
    refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ z₁)
      (Set.mem_univ 0) ?_
    have : analyticOrderAt f z₁ = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hz₁
    rw [this]; exact ENat.zero_ne_top
  set m := analyticOrderNatAt f 0 with hm
  obtain ⟨g0, hg0an, hg00, hev⟩ := (hf.analyticAt 0).analyticOrderAt_ne_top.mp hord
  rw [← hm] at hev
  set g : ℂ → ℂ := Function.update (fun z => f z / z ^ m) 0 (g0 0) with hg
  have hgg0 : g =ᶠ[𝓝 0] g0 := by
    filter_upwards [hev] with z hz
    by_cases h : z = 0
    · subst h; simp [hg]
    · simp only [hg, Function.update_of_ne h, hz, sub_zero, smul_eq_mul]
      have : z ^ m ≠ 0 := pow_ne_zero _ h
      field_simp
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : z = 0
    · subst hz
      exact hg0an.differentiableAt.congr_of_eventuallyEq hgg0
    · have hev' : g =ᶠ[𝓝 z] fun w => f w / w ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp [hg, Function.update_of_ne hw]
      have : DifferentiableAt ℂ (fun w => f w / w ^ m) z :=
        (hf z).div (differentiableAt_pow m) (pow_ne_zero _ hz)
      exact this.congr_of_eventuallyEq hev'
  · simpa [hg] using hg00
  · intro z
    by_cases hz : z = 0
    · subst hz
      have h1 := hev.self_of_nhds
      simp only [sub_zero, smul_eq_mul] at h1
      have h2 : g 0 = g0 0 := by simp [hg]
      rw [h2]; exact h1
    · have : z ^ m ≠ 0 := pow_ne_zero _ hz
      simp only [hg, Function.update_of_ne hz]
      field_simp

/-- Dividing out `z^m` keeps the listing. -/
lemma Listing.of_factor {f g : ℂ → ℂ} (hg : Differentiable ℂ g) {m : ℕ}
    (hfg : ∀ z, f z = z ^ m * g z) {a : ι → ℂ} (L : Listing f a) : Listing g a := by
  refine ⟨L.ne_zero, L.finite_fibre, fun w hw => ?_⟩
  rw [L.ncard_fibre w hw]
  have hfun : f = (fun z => z ^ m) * g := funext fun z => by simp [hfg z]
  have hzm : AnalyticAt ℂ (fun z : ℂ => z ^ m) w := by fun_prop
  have h1 : analyticOrderAt (fun z : ℂ => z ^ m) w = 0 := by
    rw [analyticOrderAt_eq_zero]; exact Or.inr (pow_ne_zero _ hw)
  have h2 : analyticOrderAt f w = analyticOrderAt g w := by
    rw [hfun, analyticOrderAt_mul hzm (hg.analyticAt w), h1, zero_add]
  simp [analyticOrderNatAt, h2]

/-- Growth of `g = f / z^m`. -/
lemma GrowthBound.of_factor {f g : ℂ → ℂ} (hg : Differentiable ℂ g) {m : ℕ}
    (hfg : ∀ z, f z = z ^ m * g z) {σ : ℝ} (h : GrowthBound f σ) :
    GrowthBound g σ := by
  obtain ⟨C, hC1, hC⟩ := h.exists_ge_one
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  refine ⟨max C (max B 1), fun z => ?_⟩
  have hx : 0 ≤ ‖z‖ ^ σ := Real.rpow_nonneg (norm_nonneg _) _
  set C' := max C (max B 1) with hC'
  have hCC' : C ≤ C' := le_max_left _ _
  have hBC' : B ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have hC'1 : 1 ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  have hexp : 1 ≤ Real.exp (C' * ‖z‖ ^ σ) := Real.one_le_exp (mul_nonneg (by linarith) hx)
  by_cases hz : ‖z‖ ≤ 1
  · calc ‖g z‖ ≤ B := hB z (by simpa using hz)
      _ ≤ C' * 1 := by linarith
      _ ≤ C' * Real.exp (C' * ‖z‖ ^ σ) := mul_le_mul_of_nonneg_left hexp (by linarith)
  · push Not at hz
    have h1 : ‖g z‖ ≤ ‖f z‖ := by
      rw [hfg z, norm_mul, norm_pow]
      have : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hz.le
      nlinarith [norm_nonneg (g z)]
    calc ‖g z‖ ≤ ‖f z‖ := h1
      _ ≤ C * Real.exp (C * ‖z‖ ^ σ) := hC z
      _ ≤ C' * Real.exp (C * ‖z‖ ^ σ) :=
          mul_le_mul_of_nonneg_right hCC' (Real.exp_pos _).le
      _ ≤ C' * Real.exp (C' * ‖z‖ ^ σ) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
          exact mul_le_mul_of_nonneg_right hCC' hx

/-- **Hadamard's factorization theorem.**  See the module docstring. -/
theorem hadamard {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hgrowth : GrowthBound f σ) {a : ι → ℂ} (L : Listing f a) {p : ℕ} (hp : σ < p + 1) :
    Summable (fun i => (‖a i‖ ^ (p + 1))⁻¹) ∧
    HasProdLocallyUniformlyOn (fun i z => E p (z / a i)) (fun z => ∏' i, E p (z / a i))
      Set.univ ∧
    ∃ (c : ℂ) (P : Polynomial ℂ), c ≠ 0 ∧ P.natDegree ≤ p ∧ P.eval 0 = 0 ∧
      ∀ z : ℂ, f z = c * z ^ analyticOrderNatAt f 0 * cexp (P.eval z) * ∏' i, E p (z / a i) := by
  obtain ⟨g, hgd, hg0, hfg⟩ := exists_factor_pow hf hne
  have Lg : Listing g a := L.of_factor hgd hfg
  obtain ⟨C, hC1, hCb⟩ := (GrowthBound.of_factor hgd hfg hgrowth).exists_ge_one
  have CD : CanonData p a := Lg.canonData hgd hg0 hC1 hCb hσ.le hp
  obtain ⟨c, hc⟩ := hadamard_of_ne_zero hgd hg0 Lg hC1 hCb hσ hp
  refine ⟨CD.summable, hasProd_E CD, g 0, ∑ k ∈ range p, Polynomial.C (c k / ((k : ℂ) + 1)) *
    Polynomial.X ^ (k + 1), hg0, ?_, ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Finset.mem_range.mp hk
  · simp [Polynomial.eval_finsetSum]
  · have := hc z
    rw [hfg z, this]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have e : canonProd p a z = ∏' i, E p (z / a i) := rfl
    rw [e]
    ring

/-- The classical form: genus `p = ⌊σ⌋`. -/
theorem hadamard_floor {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {σ : ℝ}
    (hσ : 0 < σ) (hgrowth : GrowthBound f σ) {a : ι → ℂ} (L : Listing f a) :
    Summable (fun i => (‖a i‖ ^ (⌊σ⌋₊ + 1))⁻¹) ∧
    ∃ (c : ℂ) (P : Polynomial ℂ), c ≠ 0 ∧ P.natDegree ≤ ⌊σ⌋₊ ∧ P.eval 0 = 0 ∧
      ∀ z : ℂ, f z = c * z ^ analyticOrderNatAt f 0 * cexp (P.eval z) *
        ∏' i, E ⌊σ⌋₊ (z / a i) := by
  obtain ⟨h1, -, h3⟩ := hadamard hf hne hσ hgrowth L (Nat.lt_floor_add_one σ)
  exact ⟨h1, h3⟩

/-- Existence of a listing (e.g. an enumeration of the zeros): `Hadamard.hadamard` applies to the canonical one. -/
theorem hadamard_exists {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {σ : ℝ}
    (hσ : 0 < σ) (hgrowth : GrowthBound f σ) :
    ∃ (a : ZeroIdx f → ℂ), Listing f a ∧ Summable (fun i => (‖a i‖ ^ (⌊σ⌋₊ + 1))⁻¹) ∧
    ∃ (c : ℂ) (P : Polynomial ℂ), c ≠ 0 ∧ P.natDegree ≤ ⌊σ⌋₊ ∧ P.eval 0 = 0 ∧
      ∀ z : ℂ, f z = c * z ^ analyticOrderNatAt f 0 * cexp (P.eval z) *
        ∏' i, E ⌊σ⌋₊ (z / a i) :=
  ⟨ZeroIdx.a f, exists_listing f, hadamard_floor hf hne hσ hgrowth (exists_listing f)⟩

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.exists_factor_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.exists_factor_pow

/-- info: 'FormalResearch.Hadamard.hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.hadamard

/-- info: 'FormalResearch.Hadamard.hadamard_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.hadamard_floor

/-- info: 'FormalResearch.Hadamard.hadamard_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.hadamard_exists

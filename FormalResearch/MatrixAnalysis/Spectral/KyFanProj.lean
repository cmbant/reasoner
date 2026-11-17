module

public import FormalResearch.MatrixAnalysis.Spectral.SpecMap

/-!
# Ky Fan's maximum principle in trace-of-projection form (abstract layer)

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For a symmetric operator `T` on an `N`-dimensional inner product space `E` over `ℝ` or `ℂ` and `k ≤ N`:

* `kyFan_projection_le`: for every orthogonal projection `P` (`P` symmetric, `P ∘ P = P`) of trace `k`,
  `Re tr(P T) ≤ Σ_{i<k} μ_i(T)`.
* `kyFan_projection_isGreatest`: **Ky Fan maximum principle**, `Σ_{i<k} μ_i(T) = max_P Re tr(P T)` over rank-`k`
  orthogonal projections, attained at the spectral projection `dop b 1_{i<k}`.

The proof expands `tr(P T) = Σ_j μ_j ⟨b_j, P b_j⟩` in the eigenbasis `b` of `T`; the weights
`w_j = ⟨b_j, P b_j⟩ ∈ [0,1]` sum to `tr P = k`, and `Spectral.KyFan.weighted_sum_le` closes.  Matrix form:
`Spectral.WeylMatrix.herm_kyFan_projection_le`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {N : ℕ} (hN : finrank 𝕜 E = N)

section DopCalculus

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional 𝕜 E] in
theorem inner_basis_self (b : OrthonormalBasis ι 𝕜 E) (i : ι) : inner 𝕜 (b i) (b i) = (1 : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

omit [FiniteDimensional 𝕜 E] in
theorem inner_dop (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) (i : ι) (x : E) :
    inner 𝕜 (b i) (dop b f x) = (f i : 𝕜) * inner 𝕜 (b i) x := by
  classical
  rw [dop_apply, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_basis_self, mul_one]
  · intro j _ hji
    rw [inner_smul_right, b.orthonormal.inner_eq_zero (Ne.symm hji)]
    simp
  · simp

omit [FiniteDimensional 𝕜 E] in
theorem dop_comp_dop (b : OrthonormalBasis ι 𝕜 E) (f g : ι → ℝ) :
    dop b f ∘ₗ dop b g = dop b (fun i => f i * g i) := by
  ext x
  simp only [LinearMap.comp_apply, dop_apply (b := b) (f := f) (dop b g x), inner_dop]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  ring

omit [FiniteDimensional 𝕜 E] in
theorem trace_dop (b : OrthonormalBasis ι 𝕜 E) (f : ι → ℝ) :
    LinearMap.trace 𝕜 E (dop b f) = ((∑ i, f i : ℝ) : 𝕜) := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp_rw [inner_dop, inner_basis_self, mul_one]
  push_cast
  rfl

end DopCalculus

section Projection

variable {P : E →ₗ[𝕜] E}

include hT in
/-- **Ky Fan inequality, projection form.** -/
theorem kyFan_projection_le (hP : P.IsSymmetric) (hPP : P ∘ₗ P = P) {k : ℕ}
    (hk : LinearMap.trace 𝕜 E P = (k : 𝕜)) :
    RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ T)) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hT.eigenvalues hN i := by
  set b := hT.eigenvectorBasis hN with hb
  set w : Fin N → ℝ := fun j => RCLike.re (inner 𝕜 (b j) (P (b j))) with hw
  have hPb : ∀ x, RCLike.re (inner 𝕜 x (P x)) = ‖P x‖ ^ 2 := by
    intro x
    have : inner 𝕜 x (P x) = inner 𝕜 (P x) (P x) := by
      conv_lhs => rw [← LinearMap.congr_fun hPP x]
      exact (hP x (P x)).symm
    rw [this, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hw0 : ∀ j, 0 ≤ w j := fun j => by rw [hw]; simp only; rw [hPb]; positivity
  have hw1 : ∀ j, w j ≤ 1 := by
    intro j
    simp only [hw]
    rw [hPb]
    have h1 : ‖P (b j)‖ ^ 2 ≤ ‖P (b j)‖ := by
      have := hPb (b j)
      calc ‖P (b j)‖ ^ 2 = RCLike.re (inner 𝕜 (b j) (P (b j))) := this.symm
        _ ≤ ‖inner 𝕜 (b j) (P (b j))‖ := RCLike.re_le_norm _
        _ ≤ ‖b j‖ * ‖P (b j)‖ := norm_inner_le_norm _ _
        _ = ‖P (b j)‖ := by rw [hb, (hT.eigenvectorBasis hN).orthonormal.1 j, one_mul]
    nlinarith [norm_nonneg (P (b j))]
  have hws : ∑ j, w j = k := by
    have := LinearMap.trace_eq_sum_inner P b
    rw [hk] at this
    have h2 := congrArg RCLike.re this
    rw [map_sum] at h2
    simpa using h2.symm
  have htr : RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ T)) = ∑ j, hT.eigenvalues hN j * w j := by
    rw [LinearMap.trace_eq_sum_inner _ b, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.comp_apply, hb, hT.apply_eigenvectorBasis hN j, map_smul, inner_smul_right,
      RCLike.re_ofReal_mul]
  rw [htr]
  exact weighted_sum_le _ (hT.eigenvalues_antitone hN) w hw0 hw1 hws

include hT in
/-- **Ky Fan maximum principle (projection form).**  For `k ≤ N`,
`Σ_{i<k} μ_i = max { Re tr(P T) : P orthogonal projection of trace k }`. -/
theorem kyFan_projection_isGreatest {k : ℕ} (hk : k ≤ N) :
    IsGreatest {s : ℝ | ∃ P : E →ₗ[𝕜] E, P.IsSymmetric ∧ P ∘ₗ P = P ∧
        LinearMap.trace 𝕜 E P = (k : 𝕜) ∧ s = RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ T))}
      (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), hT.eigenvalues hN i) := by
  set b := hT.eigenvectorBasis hN with hb
  set f : Fin N → ℝ := fun i => if (i : ℕ) < k then 1 else 0 with hf
  refine ⟨⟨dop b f, isSymmetric_dop b f, ?_, ?_, ?_⟩, ?_⟩
  · rw [dop_comp_dop]
    congr 1
    funext i
    simp only [hf]
    split_ifs <;> simp
  · rw [trace_dop]
    have : ∑ i, f i = k := by
      simp only [hf]
      rw [← Finset.sum_filter, Finset.sum_const, card_filter_lt_fin hk]
      simp
    rw [this]
    simp
  · rw [LinearMap.trace_eq_sum_inner _ b, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.comp_apply, hb, hT.apply_eigenvectorBasis hN j, map_smul, inner_smul_right,
      RCLike.re_ofReal_mul, inner_dop]
    simp only [hf]
    split_ifs
    · simp
    · simp
  · rintro s ⟨P, hP, hPP, hk', rfl⟩
    exact kyFan_projection_le hT hN hP hPP hk'

end Projection

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.kyFan_projection_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.kyFan_projection_le

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.kyFan_projection_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.kyFan_projection_isGreatest

end FormalResearch.MatrixAnalysis.Spectral

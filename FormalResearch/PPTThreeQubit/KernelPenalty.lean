module

public import FormalResearch.PPTThreeQubit.ExtremeCriterion
public import FormalResearch.PPTThreeQubit.CurveParam
public import FormalResearch.GurvitsBarnum.Closed

/-!
# The kernel-penalty witness lift (`lem:ppt3-kernel-penalty`)

Source: `QI/hidden_entanglement/ppt_three_qubit/kernel_penalty_lemma.tex`,
`lem:ppt3-kernel-penalty`.

Let `C` be a compact set of vectors, `K` a matrix and `W₀` a matrix whose quadratic form
`qf W₀ v = Re (v† W₀ v)` is strictly positive on `C ∩ ker K`.  Then `W₀ + λ K†K` has nonnegative
quadratic form on all of `C` for some `λ ≥ 0` (`exists_kernel_penalty`); with `W₀ + ε I` in place of
`W₀` the nonstrict version follows for every `ε > 0` (`exists_kernel_penalty_eps`), and the penalty
does not change the expectation on a state supported on `ker K`
(`trace_penalty`).  For biseparability, `C` is the set of normalised cut-product vectors:
`exists_kernel_penalty_cutProduct` is the statement for all cut-product vectors, via the compactness of
`C₈` (the Euclidean-unit cut-product vectors of the three cuts).
Not formalised: the quantitative form `prop:ppt3-kernel-quant` (explicit `λ`, distance bound), which
uses operator-norm bounds and a trace-distance bound from `eq:ppt3-stability`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

open ExtremeCriterion

section Generic

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

theorem qf_penalty_eq (K : Matrix m ι ℂ) (v : ι → ℂ) :
    qf (Kᴴ * K) v = (star (K *ᵥ v) ⬝ᵥ (K *ᵥ v)).re := by
  unfold qf
  congr 1
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem qf_penalty_nonneg (K : Matrix m ι ℂ) (v : ι → ℂ) : 0 ≤ qf (Kᴴ * K) v := by
  rw [qf_penalty_eq]
  have := (Matrix.posSemidef_conjTranspose_mul_self K).dotProduct_mulVec_nonneg v
  simp only [← mulVec_mulVec, dotProduct_mulVec, star_mulVec] at this
  exact (Complex.nonneg_iff.mp (by simpa [dotProduct_mulVec, star_mulVec] using this)).1

theorem mulVec_eq_zero_of_qf_penalty {K : Matrix m ι ℂ} {v : ι → ℂ} (h : qf (Kᴴ * K) v = 0) :
    K *ᵥ v = 0 := by
  rw [qf_penalty_eq] at h
  have him : (star (K *ᵥ v) ⬝ᵥ (K *ᵥ v)).im = 0 := by
    simp [dotProduct, Complex.mul_im, mul_comm]
  have : star (K *ᵥ v) ⬝ᵥ (K *ᵥ v) = 0 := Complex.ext h (by simpa using him)
  exact dotProduct_star_self_eq_zero.mp (by simpa [dotProduct_comm] using this)

/-- **Kernel-penalty witness lift** (`lem:ppt3-kernel-penalty`, strict form).  If `qf W₀` is positive
on `C ∩ ker K` for a compact `C`, then `W₀ + λ K†K` is nonnegative on `C` for some `λ ≥ 0`. -/
theorem exists_kernel_penalty {C : Set (ι → ℂ)} (hC : IsCompact C) (K : Matrix m ι ℂ)
    (W₀ : Matrix ι ι ℂ) (hpos : ∀ v ∈ C, K *ᵥ v = 0 → 0 < qf W₀ v) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v ∈ C, 0 ≤ qf (W₀ + lam • (Kᴴ * K)) v := by
  set B : Set (ι → ℂ) := C ∩ {v | qf W₀ v ≤ 0} with hBdef
  have hB : IsCompact B := hC.inter_right (isClosed_le (qf_continuous W₀) continuous_const)
  by_cases hne : B.Nonempty
  · obtain ⟨v0, hv0B, hv0⟩ := hB.exists_isMinOn hne (qf_continuous (Kᴴ * K)).continuousOn
    obtain ⟨v1, hv1B, hv1⟩ := hB.exists_isMinOn hne (qf_continuous W₀).continuousOn
    have hη : 0 < qf (Kᴴ * K) v0 := by
      rcases (qf_penalty_nonneg K v0).lt_or_eq with h | h
      · exact h
      · exfalso
        have := hpos v0 hv0B.1 (mulVec_eq_zero_of_qf_penalty h.symm)
        exact absurd hv0B.2 (not_le.2 this)
    have hm : qf W₀ v1 ≤ 0 := hv1B.2
    refine ⟨-qf W₀ v1 / qf (Kᴴ * K) v0, div_nonneg (by linarith) hη.le, fun v hv => ?_⟩
    rw [qf_add_smul]
    by_cases hvB : qf W₀ v ≤ 0
    · have h1 : qf W₀ v1 ≤ qf W₀ v := hv1 ⟨hv, hvB⟩
      have h2 : qf (Kᴴ * K) v0 ≤ qf (Kᴴ * K) v := hv0 ⟨hv, hvB⟩
      have h3 : -qf W₀ v1 / qf (Kᴴ * K) v0 * qf (Kᴴ * K) v0 = -qf W₀ v1 := by
        field_simp
      have h4 : 0 ≤ -qf W₀ v1 / qf (Kᴴ * K) v0 := div_nonneg (by linarith) hη.le
      nlinarith [mul_le_mul_of_nonneg_left h2 h4]
    · have h1 : 0 < qf W₀ v := not_le.1 hvB
      have h4 : 0 ≤ -qf W₀ v1 / qf (Kᴴ * K) v0 := div_nonneg (by linarith) hη.le
      nlinarith [mul_nonneg h4 (qf_penalty_nonneg K v)]
  · refine ⟨0, le_rfl, fun v hv => ?_⟩
    rw [qf_add_smul, zero_mul, add_zero]
    by_contra hcon
    exact hne ⟨v, hv, (not_le.1 hcon).le⟩

/-- Nonstrict form: if `qf W₀ ≥ 0` on `C ∩ ker K` (all vectors of `C` nonzero), then for every
`ε > 0` the matrix `W₀ + ε I + λ K†K` is nonnegative on `C` for some `λ ≥ 0`. -/
theorem exists_kernel_penalty_eps {C : Set (ι → ℂ)} (hC : IsCompact C) (hne : ∀ v ∈ C, v ≠ 0)
    (K : Matrix m ι ℂ) (W₀ : Matrix ι ι ℂ) (hW : ∀ v ∈ C, K *ᵥ v = 0 → 0 ≤ qf W₀ v) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v ∈ C, 0 ≤ qf (W₀ + ε • (1 : Matrix ι ι ℂ) + lam • (Kᴴ * K)) v := by
  have hq1 : ∀ v : ι → ℂ, v ≠ 0 → 0 < qf (1 : Matrix ι ι ℂ) v := fun v hv => by
    unfold qf
    have := (Matrix.PosDef.one (n := ι) (R := ℂ)).dotProduct_mulVec_pos hv
    simpa using (Complex.pos_iff.mp this).1
  obtain ⟨lam, hl, h⟩ := exists_kernel_penalty hC K (W₀ + ε • (1 : Matrix ι ι ℂ)) (fun v hv hk => by
    rw [qf_add_smul]
    have := hW v hv hk
    have := hq1 v (hne v hv)
    nlinarith)
  exact ⟨lam, hl, h⟩

/-- The kernel penalty does not change the expectation on a state supported on `ker K`
(`K ρ = 0`): `tr((W₀ + ε I + λ K†K) ρ) = tr(W₀ ρ) + ε tr ρ`. -/
theorem trace_penalty (K : Matrix m ι ℂ) (W₀ ρ : Matrix ι ι ℂ) (hρ : K * ρ = 0) (ε lam : ℝ) :
    trace ((W₀ + ε • (1 : Matrix ι ι ℂ) + lam • (Kᴴ * K)) * ρ) =
      trace (W₀ * ρ) + ε * trace ρ := by
  rw [Matrix.add_mul, Matrix.add_mul, trace_add, trace_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, trace_smul, trace_smul, Matrix.mul_assoc, hρ]
  simp

end Generic

/-! ### The free set of biseparability: cut-product vectors -/

/-- The Euclidean-unit cut-product vectors `α ⊗ μ` of the three cuts. -/
def C8 : Set (Fin 8 → ℂ) :=
  ⋃ c : Fin 3, (fun p : EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 4) =>
      fun i : Fin 8 => p.1.ofLp ((cutEquiv c) i).1 * p.2.ofLp ((cutEquiv c) i).2) ''
    (Metric.sphere 0 1 ×ˢ Metric.sphere 0 1)

theorem isCompact_C8 : IsCompact C8 :=
  isCompact_iUnion fun c => ((isCompact_sphere _ _).prod (isCompact_sphere _ _)).image
    (continuous_pi fun i =>
      ((continuous_apply _).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)).mul
        ((continuous_apply _).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)))

theorem isCutProduct_of_mem_C8 {y : Fin 8 → ℂ} (hy : y ∈ C8) : IsCutProduct y := by
  obtain ⟨c, h⟩ := Set.mem_iUnion.1 hy
  obtain ⟨⟨α, μ⟩, -, rfl⟩ := h
  rw [isCutProduct_iff]
  exact ⟨c, (isCutProdAt_iff c _).2 ⟨α.ofLp, μ.ofLp, fun i => rfl⟩⟩

theorem ne_zero_of_mem_C8 {y : Fin 8 → ℂ} (hy : y ∈ C8) : y ≠ 0 := by
  obtain ⟨c, h⟩ := Set.mem_iUnion.1 hy
  obtain ⟨⟨α, μ⟩, ⟨hα, hμ⟩, rfl⟩ := h
  have key : ∀ {n : ℕ} (v : EuclideanSpace ℂ (Fin n)), v ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 →
      ∃ i, v.ofLp i ≠ 0 := by
    intro n v hv
    by_contra hcon
    push Not at hcon
    have : v = 0 := by ext i; simpa using hcon i
    simp [this] at hv
  obtain ⟨i, hi⟩ := key α hα
  obtain ⟨k, hk⟩ := key μ hμ
  intro h0
  have := congrFun h0 ((cutEquiv c).symm (i, k))
  simp only [Equiv.apply_symm_apply, Pi.zero_apply] at this
  exact mul_ne_zero hi hk this

/-- Every cut-product vector is zero or a real multiple of an element of `C8`. -/
theorem cutProduct_eq_smul {x : Fin 8 → ℂ} (h : IsCutProduct x) :
    x = 0 ∨ ∃ r : ℝ, ∃ y ∈ C8, x = r • y := by
  obtain ⟨c, hc⟩ := (isCutProduct_iff x).1 h
  obtain ⟨α, μ, hxe⟩ := (isCutProdAt_iff c x).1 hc
  by_cases hα : α = 0
  · left; ext i; simp [hxe, hα]
  by_cases hμ : μ = 0
  · left; ext i; simp [hxe, hμ]
  right
  set a : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 α with ha
  set b : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 μ with hb
  have hna : 0 < ‖a‖ := norm_pos_iff.2 (by simpa [ha] using hα)
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 (by simpa [hb] using hμ)
  refine ⟨‖a‖ * ‖b‖, fun i => (‖a‖⁻¹ • a).ofLp ((cutEquiv c) i).1 *
    (‖b‖⁻¹ • b).ofLp ((cutEquiv c) i).2, Set.mem_iUnion.2 ⟨c, ((‖a‖⁻¹ • a, ‖b‖⁻¹ • b)), ⟨?_, ?_⟩,
    rfl⟩, ?_⟩
  · simp [norm_smul, hna.ne']
  · simp [norm_smul, hnb.ne']
  · ext i
    have hA : ∀ j, (‖a‖⁻¹ • a).ofLp j = ‖a‖⁻¹ * α j := fun j => by simp [ha, Complex.real_smul]
    have hB : ∀ j, (‖b‖⁻¹ • b).ofLp j = ‖b‖⁻¹ * μ j := fun j => by simp [hb, Complex.real_smul]
    have h1 : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hna.ne'
    have h2 : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hnb.ne'
    simp only [hxe, Pi.smul_apply, smul_eq_mul, hA, hB, Complex.real_smul]
    push_cast
    field_simp

/-- **Kernel-penalty lift for biseparability** (`lem:ppt3-kernel-penalty`, `C` the cut-product
vectors): if `qf W₀` is positive on the nonzero cut-product vectors in `ker K`, then
`W₀ + λ K†K` has nonnegative quadratic form on every cut-product vector, for some `λ ≥ 0`. -/
theorem exists_kernel_penalty_cutProduct {m : Type*} [Fintype m] [DecidableEq m]
    (K : Matrix m (Fin 8) ℂ) (W₀ : Matrix (Fin 8) (Fin 8) ℂ)
    (hpos : ∀ x, IsCutProduct x → x ≠ 0 → K *ᵥ x = 0 → 0 < qf W₀ x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x, IsCutProduct x → 0 ≤ qf (W₀ + lam • (Kᴴ * K)) x := by
  obtain ⟨lam, hl, h⟩ := exists_kernel_penalty isCompact_C8 K W₀ fun y hy hk =>
    hpos y (isCutProduct_of_mem_C8 hy) (ne_zero_of_mem_C8 hy) hk
  refine ⟨lam, hl, fun x hx => ?_⟩
  rcases cutProduct_eq_smul hx with rfl | ⟨r, y, hy, rfl⟩
  · simp [qf]
  · rw [qf_smul]
    exact mul_nonneg (sq_nonneg r) (h y hy)


/-- **Kernel-penalty witness lift, nonstrict form** (`lem:ppt3-kernel-penalty`, second sentence, for
the free set of biseparability).  If `qf W₀ ≥ 0` on the cut-product vectors of `ker K` and `ρ` is
supported on `ker K` (`K ρ = 0`), then for every `ε > 0` there is `λ ≥ 0` such that
`W = W₀ + ε I + λ K†K` is nonnegative on every cut-product vector (a global biseparability witness)
and `tr(W ρ) = tr(W₀ ρ) + ε tr ρ`. -/
theorem kernel_penalty_witness {m : Type*} [Fintype m] [DecidableEq m]
    (K : Matrix m (Fin 8) ℂ) (W₀ ρ : Matrix (Fin 8) (Fin 8) ℂ)
    (hW : ∀ x, IsCutProduct x → K *ᵥ x = 0 → 0 ≤ qf W₀ x) (hρ : K * ρ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (∀ x, IsCutProduct x → 0 ≤ qf (W₀ + ε • (1 : Matrix (Fin 8) (Fin 8) ℂ) + lam • (Kᴴ * K)) x) ∧
      trace ((W₀ + ε • (1 : Matrix (Fin 8) (Fin 8) ℂ) + lam • (Kᴴ * K)) * ρ) =
        trace (W₀ * ρ) + ε * trace ρ := by
  have hq1 : ∀ v : Fin 8 → ℂ, v ≠ 0 → 0 < qf (1 : Matrix (Fin 8) (Fin 8) ℂ) v := fun v hv => by
    unfold qf
    have := (Matrix.PosDef.one (n := Fin 8) (R := ℂ)).dotProduct_mulVec_pos hv
    simpa using (Complex.pos_iff.mp this).1
  obtain ⟨lam, hl, h⟩ := exists_kernel_penalty_cutProduct K (W₀ + ε • (1 : Matrix (Fin 8) (Fin 8) ℂ))
    (fun x hx hx0 hk => by
      rw [qf_add_smul]
      have := hW x hx hk
      have := hq1 x hx0
      nlinarith)
  exact ⟨lam, hl, h, trace_penalty K W₀ ρ hρ ε lam⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.exists_kernel_penalty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.exists_kernel_penalty

/-- info: 'FormalResearch.PPTThreeQubit.kernel_penalty_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.kernel_penalty_witness

end FormalResearch.PPTThreeQubit

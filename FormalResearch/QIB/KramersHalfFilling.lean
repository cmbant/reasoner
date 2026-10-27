import Mathlib

namespace FormalResearch.QIB

/-!
# Kramers half-filling (`lem:halffilling`)

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `lem:halffilling`.

Let `Θ` be an antiunitary map on a finite-dimensional Hermitian space `E` with `Θ² = -1`,
let `Q` be a two-plane with `Θ Q ⊆ Q`, and let `V` be a subspace with `Θ V ⊥ V`.
Then `Tr(P_Q P_V) ≤ 1`.

Formulation.  `Θ : E → E` is unbundled; the only properties used are the antiunitary
inner-product identity `⟪Θ u, Θ v⟫ = conj ⟪u, v⟫` and `Θ (Θ v) = -v`.  The hypotheses on `Q`
and `V` are the weaker `Θ Q ⊆ Q` and `∀ v w ∈ V, ⟪Θ v, w⟫ = 0`.  The matrix form
`Θ v = conj (J v)` with `J` a skew unitary matrix (the Kramers form of the paper) is a corollary.
-/

open scoped InnerProductSpace ComplexConjugate Matrix

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Antiunitary inner-product identity. -/
def IsAntiunitary (Θ : E → E) : Prop := ∀ u v, ⟪Θ u, Θ v⟫_ℂ = conj ⟪u, v⟫_ℂ

/-- `Θ² = -1`. -/
def IsKramers (Θ : E → E) : Prop := ∀ v, Θ (Θ v) = -v

variable {Θ : E → E}

lemma IsAntiunitary.norm_eq (hΘ : IsAntiunitary Θ) (v : E) : ‖Θ v‖ = ‖v‖ := by
  have h := hΘ v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h' := congrArg Complex.re h
    simpa [← Complex.ofReal_pow, Complex.conj_re] using h'
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Every vector is orthogonal to its Kramers partner. -/
lemma kramers_inner_self (hΘ : IsAntiunitary Θ) (hK : IsKramers Θ) (q : E) :
    ⟪q, Θ q⟫_ℂ = 0 := by
  have h1 := hΘ q (Θ q)
  rw [hK q, inner_neg_right] at h1
  have h3 : ⟪Θ q, q⟫_ℂ = conj ⟪q, Θ q⟫_ℂ := (inner_conj_symm (Θ q) q).symm
  rw [h3] at h1
  have h4 : conj ⟪q, Θ q⟫_ℂ = 0 := by
    have : (2 : ℂ) * conj ⟪q, Θ q⟫_ℂ = 0 := by linear_combination -h1
    simpa using this
  exact (map_eq_zero (starRingEnd ℂ)).mp h4

/-- Core inequality: if `a ∈ V` is the projection of a unit `q` onto `V` and `c ∈ V` is the
projection of `Θ q`, then `‖a‖² + ‖c‖² ≤ 1`. -/
lemma kramers_core (hΘ : IsAntiunitary Θ) (hK : IsKramers Θ) {V : Submodule ℂ E}
    (hV : ∀ v ∈ V, ∀ w ∈ V, ⟪Θ v, w⟫_ℂ = 0) {q a c : E} (hq : ‖q‖ = 1)
    (ha : a ∈ V) (hc : c ∈ V)
    (hqa : ⟪q, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ)) (hqc : ⟪Θ q, c⟫_ℂ = ((‖c‖ ^ 2 : ℝ) : ℂ)) :
    ‖a‖ ^ 2 + ‖c‖ ^ 2 ≤ 1 := by
  have hac : ⟪a, Θ c⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hV c hc a ha]; simp
  have hn : ‖a - Θ c‖ ^ 2 = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hac, hΘ.norm_eq]; simp
  have hqΘ : ⟪q, Θ c⟫_ℂ = -((‖c‖ ^ 2 : ℝ) : ℂ) := by
    have h1 := hΘ q (Θ c)
    rw [hK c, inner_neg_right, hqc] at h1
    have h2 : conj (⟪q, Θ c⟫_ℂ) = -((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [← h1]
    have h3 := congrArg conj h2
    simpa using h3
  have hqw : ⟪q, a - Θ c⟫_ℂ = (((‖a‖ ^ 2 + ‖c‖ ^ 2 : ℝ)) : ℂ) := by
    rw [inner_sub_right, hqa, hqΘ]; push_cast; ring
  have hcs := norm_inner_le_norm (𝕜 := ℂ) q (a - Θ c)
  rw [hqw, hq, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hcs
  set T := ‖a‖ ^ 2 + ‖c‖ ^ 2 with hT
  set w := ‖a - Θ c‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  have : w ^ 2 ≤ w := by nlinarith
  have hw1 : w ≤ 1 := by nlinarith
  nlinarith

end Abstract

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {Θ : E → E}

lemma inner_proj_self (V : Submodule ℂ E) (x : E) :
    ⟪x, V.starProjection x⟫_ℂ = ((‖V.starProjection x‖ ^ 2 : ℝ) : ℂ) := by
  have h : V.starProjection (V.starProjection x) = V.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem V x)
  have h2 := V.inner_starProjection_left_eq_right (V.starProjection x) x
  rw [h] at h2
  rw [← inner_conj_symm, h2, inner_self_eq_norm_sq_to_K]
  simp

/-- **Kramers half-filling** (`lem:halffilling`).  Let `Θ` be antiunitary with `Θ² = -1` on a
finite-dimensional complex inner-product space `E`, `Q` a two-plane with `Θ Q ⊆ Q`, and `V` a
subspace with `Θ V ⊥ V`.  Then `Tr(P_Q P_V)` is a real number `≤ 1`. -/
theorem kramers_halffilling (hΘ : IsAntiunitary Θ) (hK : IsKramers Θ)
    (Q V : Submodule ℂ E) (hQ : Module.finrank ℂ Q = 2) (hΘQ : ∀ q ∈ Q, Θ q ∈ Q)
    (hV : ∀ v ∈ V, ∀ w ∈ V, ⟪Θ v, w⟫_ℂ = 0) :
    ∃ r : ℝ, LinearMap.trace ℂ E
      ((Q.starProjection ∘L V.starProjection : E →L[ℂ] E) : E →ₗ[ℂ] E) = (r : ℂ) ∧ r ≤ 1 := by
  classical
  -- a unit vector `q` in `Q`
  obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Q, ‖q‖ = 1 := by
    obtain ⟨x, hxQ, hx0⟩ : ∃ x ∈ Q, x ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot (by rintro rfl; simp at hQ)
    refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, Q.smul_mem _ hxQ, ?_⟩
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
  have hq'Q : Θ q ∈ Q := hΘQ q hqQ
  have hq' : ‖Θ q‖ = 1 := by rw [hΘ.norm_eq]; exact hq
  have hperp : ⟪q, Θ q⟫_ℂ = 0 := kramers_inner_self hΘ hK q
  have hperp' : ⟪Θ q, q⟫_ℂ = 0 := by rw [← inner_conj_symm, hperp]; simp
  have hne : q ≠ Θ q := by
    intro h
    rw [← h] at hperp
    simp [inner_self_eq_norm_sq_to_K, hq] at hperp
  have hs : Orthonormal ℂ ((↑) : ({q, Θ q} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    intro v hv w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with h | h <;> rcases hw with h' | h' <;> subst h <;> subst h'
    · simp [inner_self_eq_norm_sq_to_K, hq]
    · simp [hne, hperp]
    · simp [hne.symm, hperp']
    · simp [inner_self_eq_norm_sq_to_K, hq']
  -- `Q = span {q, Θ q}`
  have hQeq : Q = Submodule.span ℂ {q, Θ q} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with h | h
      · rw [h]; exact hqQ
      · rw [Set.mem_singleton_iff.mp h]; exact hq'Q
    · rw [hQ]
      have := finrank_span_set_eq_card (R := ℂ)
        (s := ({q, Θ q} : Set E)) (hs.linearIndependent : LinearIndepOn ℂ id ({q, Θ q} : Set E))
      rw [this]
      simp [Set.toFinset_insert, Finset.card_pair hne]
  -- extend to an orthonormal basis of `E`
  obtain ⟨u, b, hsu, hb⟩ := hs.exists_orthonormalBasis_extension
  have hqu : q ∈ u := hsu (by simp)
  have hq'u : Θ q ∈ u := hsu (by simp)
  have hon : Orthonormal ℂ ((↑) : u → E) := hb ▸ b.orthonormal
  have hconj : ∀ x ∈ u, x ≠ q → x ≠ Θ q → x ∈ Qᗮ := by
    intro x hx h1 h2
    have e1 : ⟪x, q⟫_ℂ = 0 :=
      hon.2 (i := ⟨x, hx⟩) (j := ⟨q, hqu⟩) (by simpa using h1)
    have e2 : ⟪x, Θ q⟫_ℂ = 0 :=
      hon.2 (i := ⟨x, hx⟩) (j := ⟨Θ q, hq'u⟩) (by simpa using h2)
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [hQeq, Submodule.mem_span_pair] at hz
    obtain ⟨α, β, rfl⟩ := hz
    rw [inner_add_left, inner_smul_left, inner_smul_left, ← inner_conj_symm q x,
      ← inner_conj_symm (Θ q) x, e1, e2]
    simp
  set T : E →ₗ[ℂ] E :=
    ((Q.starProjection ∘L V.starProjection : E →L[ℂ] E) : E →ₗ[ℂ] E) with hT
  set f : E → ℂ := fun x => ⟪x, T x⟫_ℂ with hf
  have hfQ : ∀ x ∈ Q, f x = ((‖V.starProjection x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    simp only [hf, hT]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    rw [← Q.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hx]
    exact inner_proj_self V x
  have hf0 : ∀ x ∈ u, x ≠ q → x ≠ Θ q → f x = 0 := by
    intro x hx h1 h2
    simp only [hf, hT]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    rw [← Q.inner_starProjection_left_eq_right,
      Q.starProjection_apply_eq_zero_iff.mpr (hconj x hx h1 h2)]
    simp
  have hsum : LinearMap.trace ℂ E T = f q + f (Θ q) := by
    rw [LinearMap.trace_eq_sum_inner T b]
    have h1 : ∑ i : u, ⟪b i, T (b i)⟫_ℂ = ∑ i : u, f ((i : u) : E) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb]
    rw [h1, Finset.sum_coe_sort u f]
    have hsub : ({q, Θ q} : Finset E) ⊆ u := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hqu
      · exact hq'u
    rw [← Finset.sum_subset hsub, Finset.sum_pair hne]
    intro x hx hxn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxn
    exact hf0 x hx hxn.1 hxn.2
  have ha := Submodule.starProjection_apply_mem V q
  have hc := Submodule.starProjection_apply_mem V (Θ q)
  have hcore := kramers_core hΘ hK hV hq ha hc (inner_proj_self V q) (inner_proj_self V (Θ q))
  refine ⟨‖V.starProjection q‖ ^ 2 + ‖V.starProjection (Θ q)‖ ^ 2, ?_, hcore⟩
  rw [hsum, hfQ q hqQ, hfQ (Θ q) hq'Q]
  push_cast
  rfl

end Projection

section MatrixForm

variable {n : ℕ}

/-- The matrix form of the Kramers antiunitary, `Θ v = conj (J v)` (complex conjugation of
the vector `J v`), on `EuclideanSpace ℂ (Fin n)`.  The paper's `Θ_x = conj(J_x) ∘ conj` is the
same map. -/
noncomputable def kramersMap (J : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => conj ((J.mulVec v.ofLp) i))

lemma inner_toLp_toLp (f g : Fin n → ℂ) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 g⟫_ℂ = ∑ i, conj (f i) * g i := by
  simp [PiLp.inner_apply, mul_comm]

lemma inner_eq_sum (u v : EuclideanSpace ℂ (Fin n)) :
    ⟪u, v⟫_ℂ = ∑ i, conj (u.ofLp i) * v.ofLp i := by
  simp [PiLp.inner_apply, mul_comm]

lemma unitary_inner_eq (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ * J = 1) (u v : Fin n → ℂ) :
    ∑ i, conj ((J.mulVec u) i) * (J.mulVec v) i = ∑ k, conj (u k) * v k := by
  have h : star (J.mulVec u) ⬝ᵥ J.mulVec v = star u ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJ,
      Matrix.one_mulVec]
  simpa [dotProduct] using h

/-- `Θ v = conj (J v)` is antiunitary when `J` is unitary. -/
theorem kramersMap_isAntiunitary (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ * J = 1) :
    IsAntiunitary (kramersMap J) := by
  intro u v
  simp only [kramersMap, inner_toLp_toLp, Complex.conj_conj]
  rw [inner_conj_symm v u, inner_eq_sum, ← unitary_inner_eq J hJ v.ofLp u.ofLp]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A skew unitary `J` gives a Kramers antiunitary `Θ v = conj (J v)` with `Θ² = -1`. -/
theorem kramersMap_isKramers (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ * J = 1)
    (hskew : Jᵀ = -J) : IsKramers (kramersMap J) := by
  intro v
  have hc : ∀ i k, conj (J i k) = -(Jᴴ i k) := by
    intro i k
    have h := congrFun (congrFun hskew i) k
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.conjTranspose_apply, h]
  ext i
  simp only [kramersMap, PiLp.neg_apply, WithLp.ofLp_toLp]
  calc conj ((J.mulVec fun k => conj ((J.mulVec v.ofLp) k)) i)
      = ∑ k, conj (J i k) * (J.mulVec v.ofLp) k := by
        simp [Matrix.mulVec, dotProduct, map_sum]
    _ = ∑ k, -(Jᴴ i k) * (J.mulVec v.ofLp) k := by simp only [hc]
    _ = -((Jᴴ.mulVec (J.mulVec v.ofLp)) i) := by
        simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
    _ = -(v.ofLp i) := by rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]

/-- Matrix form of Kramers half-filling: `Θ v = conj (J v)` with `J` a skew unitary matrix on
`ℂⁿ`, `Q` a two-plane with `Θ Q ⊆ Q`, `V` a subspace with `Θ V ⊥ V`.  Then `Tr(P_Q P_V) ≤ 1`. -/
theorem kramers_halffilling_matrix (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Jᴴ * J = 1)
    (hskew : Jᵀ = -J) (Q V : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hQ : Module.finrank ℂ Q = 2) (hΘQ : ∀ q ∈ Q, kramersMap J q ∈ Q)
    (hV : ∀ v ∈ V, ∀ w ∈ V, ⟪kramersMap J v, w⟫_ℂ = 0) :
    ∃ r : ℝ, LinearMap.trace ℂ (EuclideanSpace ℂ (Fin n))
      ((Q.starProjection ∘L V.starProjection :
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = (r : ℂ) ∧ r ≤ 1 :=
  kramers_halffilling (kramersMap_isAntiunitary J hJ) (kramersMap_isKramers J hJ hskew)
    Q V hQ hΘQ hV

end MatrixForm

end FormalResearch.QIB

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Polar factor of an invertible finite-dimensional map (Weyl P2, `lem:polarintertwiner`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:polarintertwiner` and the definition
`𝖴 = 𝖳 (𝖳^*𝖳)^{-1/2}` of `prop:betabinomialpolar`.

For finite-dimensional real inner-product spaces `V`, `W` and `T : V →ₗ W` injective:

* `exists_posRoot`: `T^*T` has a positive square root (spectral theorem);
* `posRoot_eigen`: any positive `R` with `R² = A` acts as `c` on every `A`-eigenvector with eigenvalue
  `c² > 0` (hence the root is unique, and no functional calculus is needed);
* `polarRoot T` is the chosen positive root `(T^*T)^{1/2}` (injective, `posRoot_injective`) and
  `polarFactor T = T (T^*T)^{-1/2}`, with `polarFactor_comp_root : U R = T`;
* `inner_polarFactor`: `U` is isometric; `polarFactor_bijective`: bijective when `T` is
  (**unitary**, `lem:polarintertwiner` first half);
* `polarFactor_basis`: if `j`, `h` are orthonormal bases and `T j_i = s_i h_i`, `s_i > 0`, then `U j_i = h_i`;
* `polar_intertwine`: `H₁ T = T H₀` with `H₀, H₁` symmetric implies `T^*T H₀ = H₀ T^*T` and
  `U H₀ = H₁ U` (`lem:polarintertwiner`).

Everything is proved here; nothing is assumed.
-/

@[expose] public section

namespace FormalResearch.Racah.Polar

open scoped InnerProductSpace
open LinearMap

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `A = T^*T` is positive. -/
lemma isPositive_adjoint_comp (T : V →ₗ[ℝ] W) : (adjoint T ∘ₗ T).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [coe_comp, Function.comp_apply, adjoint_inner_left, adjoint_inner_right]
  · simp only [coe_comp, Function.comp_apply, RCLike.re_to_real]
    rw [adjoint_inner_left]
    exact real_inner_self_nonneg

/-- **Existence of the positive square root** (spectral theorem). -/
theorem exists_posRoot (A : V →ₗ[ℝ] V) (hA : A.IsPositive) :
    ∃ R : V →ₗ[ℝ] V, R.IsPositive ∧ R ∘ₗ R = A := by
  classical
  set n := Module.finrank ℝ V with hn
  set b := hA.isSymmetric.eigenvectorBasis hn.symm with hb
  set μ := hA.isSymmetric.eigenvalues hn.symm with hμ
  have hAb : ∀ i, A (b i) = μ i • b i := fun i => by
    have := hA.isSymmetric.apply_eigenvectorBasis hn.symm i
    exact this
  have hμnn : ∀ i, 0 ≤ μ i := fun i => hA.nonneg_eigenvalues hn.symm i
  let R : V →ₗ[ℝ] V := b.toBasis.constr ℝ (fun i => Real.sqrt (μ i) • (b i : V))
  have hRb : ∀ i, R (b i) = Real.sqrt (μ i) • b i := fun i => by
    have := b.toBasis.constr_basis ℝ (fun i => Real.sqrt (μ i) • (b i : V)) i
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  have hRx : ∀ x, R x = ∑ i, (Real.sqrt (μ i) * ⟪b i, x⟫_ℝ) • (b i : V) := fun x => by
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hRb, smul_smul, mul_comm]
  have hq : ∀ x y, ⟪R x, y⟫_ℝ = ∑ i, Real.sqrt (μ i) * ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ := by
    intro x y
    rw [hRx x, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    simp
  refine ⟨R, ⟨fun x y => ?_, fun x => ?_⟩, ?_⟩
  · rw [hq x y, real_inner_comm, hq y x]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [hq x x]
    simp only [RCLike.re_to_real]
    exact Finset.sum_nonneg fun i _ => by
      have := Real.sqrt_nonneg (μ i)
      have := mul_self_nonneg ⟪b i, x⟫_ℝ
      nlinarith
  · refine b.toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis]
    simp only [coe_comp, Function.comp_apply]
    rw [hRb, map_smul, hRb, smul_smul, hAb, Real.mul_self_sqrt (hμnn i)]

omit [FiniteDimensional ℝ V] in
/-- **A positive square root acts as `c` on every eigenvector of its square with eigenvalue `c²`,
`c > 0`.**  In particular the positive root is unique. -/
theorem posRoot_eigen {R : V →ₗ[ℝ] V} (hR : R.IsPositive) {c : ℝ} (hc : 0 < c) {v : V}
    (hv : R (R v) = (c ^ 2) • v) : R v = c • v := by
  set w := R v - c • v with hw
  have h0 : R w + c • w = 0 := by
    simp only [hw, map_sub, map_smul, smul_sub, hv]
    module
  have h1 : ⟪R w + c • w, w⟫_ℝ = 0 := by rw [h0]; simp
  rw [inner_add_left, inner_smul_left] at h1
  have h2 : 0 ≤ ⟪R w, w⟫_ℝ := by simpa using hR.2 w
  have h3 := real_inner_self_nonneg (x := w)
  have h4 : ⟪w, w⟫_ℝ = 0 := by
    simp only [RCLike.conj_to_real] at h1
    by_contra h
    have : 0 < ⟪w, w⟫_ℝ := lt_of_le_of_ne h3 (Ne.symm h)
    nlinarith
  rw [inner_self_eq_zero] at h4
  exact sub_eq_zero.1 h4

/-- The root of `T^*T` is injective when `T` is. -/
lemma posRoot_injective {T : V →ₗ[ℝ] W} (hT : Function.Injective T) {R : V →ₗ[ℝ] V}
    (hRR : R ∘ₗ R = adjoint T ∘ₗ T) : Function.Injective R := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : adjoint T (T x) = 0 := by
    have := congrArg (fun F : V →ₗ[ℝ] V => F x) hRR
    simpa [hx] using this.symm
  have h2 : ⟪T x, T x⟫_ℝ = 0 := by
    rw [← adjoint_inner_left, h1]; simp
  rw [inner_self_eq_zero] at h2
  exact (injective_iff_map_eq_zero T).1 hT x h2

/-- The positive square root `(T^*T)^{1/2}` (the unique positive `R` with `R² = T^*T`). -/
noncomputable def polarRoot (T : V →ₗ[ℝ] W) : V →ₗ[ℝ] V :=
  Classical.choose (exists_posRoot _ (isPositive_adjoint_comp T))

lemma polarRoot_pos (T : V →ₗ[ℝ] W) : (polarRoot T).IsPositive :=
  (Classical.choose_spec (exists_posRoot _ (isPositive_adjoint_comp T))).1

lemma polarRoot_sq (T : V →ₗ[ℝ] W) : polarRoot T ∘ₗ polarRoot T = adjoint T ∘ₗ T :=
  (Classical.choose_spec (exists_posRoot _ (isPositive_adjoint_comp T))).2

/-- `(T^*T)^{1/2}` as a linear equivalence (`T` injective). -/
noncomputable def rootEquiv (T : V →ₗ[ℝ] W) (hT : Function.Injective T) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofInjectiveEndo (polarRoot T) (posRoot_injective hT (polarRoot_sq T))

lemma rootEquiv_apply (T : V →ₗ[ℝ] W) (hT : Function.Injective T) (x : V) :
    rootEquiv T hT x = polarRoot T x := by
  simp [rootEquiv, LinearEquiv.coe_ofInjectiveEndo]

/-- **The polar factor** `U = T (T^*T)^{-1/2}`. -/
noncomputable def polarFactor (T : V →ₗ[ℝ] W) (hT : Function.Injective T) : V →ₗ[ℝ] W :=
  T ∘ₗ (rootEquiv T hT).symm.toLinearMap

/-- `U (T^*T)^{1/2} = T`. -/
theorem polarFactor_root (T : V →ₗ[ℝ] W) (hT : Function.Injective T) (x : V) :
    polarFactor T hT (polarRoot T x) = T x := by
  unfold polarFactor
  simp only [coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [← rootEquiv_apply T hT x, LinearEquiv.symm_apply_apply]

/-- **The polar factor is isometric**: `⟪U x, U y⟫ = ⟪x, y⟫`. -/
theorem inner_polarFactor (T : V →ₗ[ℝ] W) (hT : Function.Injective T) (x y : V) :
    ⟪polarFactor T hT x, polarFactor T hT y⟫_ℝ = ⟪x, y⟫_ℝ := by
  obtain ⟨x', rfl⟩ : ∃ x', polarRoot T x' = x :=
    ⟨(rootEquiv T hT).symm x, by rw [← rootEquiv_apply T hT, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨y', rfl⟩ : ∃ y', polarRoot T y' = y :=
    ⟨(rootEquiv T hT).symm y, by rw [← rootEquiv_apply T hT, LinearEquiv.apply_symm_apply]⟩
  rw [polarFactor_root T hT, polarFactor_root T hT, ← adjoint_inner_left]
  have h := congrArg (fun F : V →ₗ[ℝ] V => F x') (polarRoot_sq T)
  simp only [coe_comp, Function.comp_apply] at h
  rw [← h]
  exact (polarRoot_pos T).isSymmetric (polarRoot T x') y'

/-- `U` is bijective when `T` is: **`U` is unitary** (`lem:polarintertwiner`). -/
theorem polarFactor_bijective (T : V →ₗ[ℝ] W) (hT : Function.Bijective T) :
    Function.Bijective (polarFactor T hT.1) := by
  unfold polarFactor
  rw [coe_comp]
  exact hT.comp (rootEquiv T hT.1).symm.bijective

/-! ### Singular pairs -/

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ V] [DecidableEq ι] in
/-- Vectors are determined by their pairings with an orthonormal basis. -/
lemma ext_of_inner_basis (jb : OrthonormalBasis ι ℝ V) {X Y : V}
    (h : ∀ k, ⟪jb k, X⟫_ℝ = ⟪jb k, Y⟫_ℝ) : X = Y := by
  refine ext_inner_left ℝ fun v => ?_
  rw [← jb.sum_repr' v]
  simp only [sum_inner, inner_smul_left, h]

variable (jb : OrthonormalBasis ι ℝ V) (hb : OrthonormalBasis ι ℝ W) {s : ι → ℝ}
  {T : V →ₗ[ℝ] W}

lemma adjoint_apply_basis (hT : ∀ i, T (jb i) = s i • hb i) (i : ι) :
    adjoint T (hb i) = s i • jb i := by
  refine ext_of_inner_basis jb fun k => ?_
  rw [LinearMap.adjoint_inner_right, hT, inner_smul_left, inner_smul_right, hb.inner_eq_ite,
    jb.inner_eq_ite]
  simp only [RCLike.conj_to_real]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

lemma injective_of_basis (hs : ∀ i, 0 < s i) (hT : ∀ i, T (jb i) = s i • hb i) :
    Function.Injective T := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine ext_of_inner_basis jb fun k => ?_
  have h1 : ⟪hb k, T x⟫_ℝ = s k * ⟪jb k, x⟫_ℝ := by
    rw [← adjoint_inner_left, adjoint_apply_basis jb hb hT, inner_smul_left]
    simp
  rw [hx, inner_zero_right] at h1
  rw [inner_zero_right]
  rcases mul_eq_zero.1 h1.symm with h | h
  · exact absurd h (hs k).ne'
  · exact h

/-- **`U j_i = h_i`**: if `T j_i = s_i h_i` with `s_i > 0` for orthonormal bases `j`, `h`, then the
polar factor `T (T^*T)^{-1/2}` maps `j_i` to `h_i`. -/
theorem polarFactor_basis (hs : ∀ i, 0 < s i) (hT : ∀ i, T (jb i) = s i • hb i) (i : ι) :
    polarFactor T (injective_of_basis jb hb hs hT) (jb i) = hb i := by
  have hA : ∀ i, polarRoot T (polarRoot T (jb i)) = (s i ^ 2) • jb i := by
    intro i
    have := congrArg (fun F : V →ₗ[ℝ] V => F (jb i)) (polarRoot_sq T)
    simp only [coe_comp, Function.comp_apply] at this
    rw [this, hT, map_smul, adjoint_apply_basis jb hb hT, smul_smul, sq]
  have hR : polarRoot T (jb i) = s i • jb i := posRoot_eigen (polarRoot_pos T) (hs i) (hA i)
  have : polarRoot T ((s i)⁻¹ • jb i) = jb i := by
    rw [map_smul, hR, smul_smul, inv_mul_cancel₀ (hs i).ne', one_smul]
  conv_lhs => rw [← this]
  rw [polarFactor_root _ (injective_of_basis jb hb hs hT), map_smul, hT, smul_smul,
    inv_mul_cancel₀ (hs i).ne', one_smul]

/-- In the situation of `polarFactor_basis`, `T` and `U` are bijective. -/
theorem bijective_of_basis (hs : ∀ i, 0 < s i) (hT : ∀ i, T (jb i) = s i • hb i) :
    Function.Bijective T ∧
      Function.Bijective (polarFactor T (injective_of_basis jb hb hs hT)) := by
  have hinj := injective_of_basis jb hb hs hT
  have hsurj : Function.Surjective T := by
    intro w
    refine ⟨∑ i, (⟪hb i, w⟫_ℝ * (s i)⁻¹) • jb i, ?_⟩
    conv_rhs => rw [← hb.sum_repr' w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT, smul_smul, mul_assoc, inv_mul_cancel₀ (hs i).ne', mul_one]
  have hb' : Function.Bijective T := ⟨hinj, hsurj⟩
  exact ⟨hb', polarFactor_bijective T hb'⟩

end Basis

/-! ### Intertwining (`lem:polarintertwiner`) -/

section Intertwine

variable {T : V →ₗ[ℝ] W} {H₀ : V →ₗ[ℝ] V} {H₁ : W →ₗ[ℝ] W}

/-- `T^* H₁ = H₀ T^*` from `H₁ T = T H₀` with `H₀, H₁` symmetric. -/
lemma adjoint_intertwine (hH₀ : H₀.IsSymmetric) (hH₁ : H₁.IsSymmetric)
    (hint : ∀ x, H₁ (T x) = T (H₀ x)) (y : W) : adjoint T (H₁ y) = H₀ (adjoint T y) := by
  refine ext_inner_left ℝ fun z => ?_
  rw [adjoint_inner_right, ← hH₁ (T z) y, hint, ← hH₀ z, adjoint_inner_right]

/-- **`T^*T` commutes with `H₀`.** -/
lemma adjoint_comp_comm (hH₀ : H₀.IsSymmetric) (hH₁ : H₁.IsSymmetric)
    (hint : ∀ x, H₁ (T x) = T (H₀ x)) (x : V) :
    adjoint T (T (H₀ x)) = H₀ (adjoint T (T x)) := by
  rw [← hint, adjoint_intertwine hH₀ hH₁ hint]

/-- **`(T^*T)^{1/2}` commutes with `H₀`** (`T` injective). -/
theorem polarRoot_comm (hT : Function.Injective T) (hH₀ : H₀.IsSymmetric) (hH₁ : H₁.IsSymmetric)
    (hint : ∀ x, H₁ (T x) = T (H₀ x)) (x : V) :
    polarRoot T (H₀ x) = H₀ (polarRoot T x) := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : V →ₗ[ℝ] V, A = adjoint T ∘ₗ T := ⟨_, rfl⟩
  have hA : A.IsPositive := hAdef ▸ isPositive_adjoint_comp T
  set n := Module.finrank ℝ V with hn
  set b := hA.isSymmetric.eigenvectorBasis hn.symm with hb
  set μ := hA.isSymmetric.eigenvalues hn.symm with hμ
  have hAb : ∀ i, A (b i) = μ i • b i := fun i => hA.isSymmetric.apply_eigenvectorBasis hn.symm i
  have hAx : ∀ x, polarRoot T (polarRoot T x) = A x := fun x => by
    have := congrArg (fun F : V →ₗ[ℝ] V => F x) (polarRoot_sq T)
    rw [hAdef]; simpa using this
  have hμpos : ∀ i, 0 < μ i := fun i => by
    have h0 := hA.nonneg_eigenvalues hn.symm i
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : μ i = 0 := h.symm
      have h1 : A (b i) = 0 := by rw [hAb, h', zero_smul]
      have h2 : ⟪T (b i), T (b i)⟫_ℝ = 0 := by
        rw [← adjoint_inner_left]
        simpa [hAdef] using congrArg (fun z => ⟪z, b i⟫_ℝ) h1
      have : T (b i) = 0 := inner_self_eq_zero.1 h2
      have : b i = 0 := (injective_iff_map_eq_zero T).1 hT _ this
      exact b.orthonormal.ne_zero i this
  have hbi : ∀ i, ∀ v, A v = μ i • v → polarRoot T v = Real.sqrt (μ i) • v := by
    intro i v hv
    refine posRoot_eigen (polarRoot_pos T) (Real.sqrt_pos.2 (hμpos i)) ?_
    rw [hAx, hv, Real.sq_sqrt (hμpos i).le]
  have key : ∀ i, polarRoot T (H₀ (b i)) = H₀ (polarRoot T (b i)) := by
    intro i
    have h1 : A (H₀ (b i)) = μ i • H₀ (b i) := by
      simp only [hAdef, coe_comp, Function.comp_apply]
      rw [adjoint_comp_comm hH₀ hH₁ hint]
      have := hAb i
      simp only [hAdef, coe_comp, Function.comp_apply] at this
      rw [this, map_smul]
    rw [hbi i _ h1, hbi i (b i) (hAb i), map_smul]
  have : polarRoot T ∘ₗ H₀ = H₀ ∘ₗ polarRoot T :=
    b.toBasis.ext fun i => by
      rw [OrthonormalBasis.coe_toBasis]; exact key i
  exact congrArg (fun F : V →ₗ[ℝ] V => F x) this

/-- **`lem:polarintertwiner`**: if `H₁ T = T H₀` with `H₀`, `H₁` symmetric and `T` bijective, then
`T^*T` commutes with `H₀`, the polar factor `U = T (T^*T)^{-1/2}` is unitary and still intertwines. -/
theorem polarFactor_intertwine (hT : Function.Bijective T) (hH₀ : H₀.IsSymmetric)
    (hH₁ : H₁.IsSymmetric) (hint : ∀ x, H₁ (T x) = T (H₀ x)) :
    (∀ x, adjoint T (T (H₀ x)) = H₀ (adjoint T (T x))) ∧
    Function.Bijective (polarFactor T hT.1) ∧
    (∀ x y, ⟪polarFactor T hT.1 x, polarFactor T hT.1 y⟫_ℝ = ⟪x, y⟫_ℝ) ∧
    ∀ x, H₁ (polarFactor T hT.1 x) = polarFactor T hT.1 (H₀ x) := by
  refine ⟨adjoint_comp_comm hH₀ hH₁ hint, polarFactor_bijective T hT, inner_polarFactor T hT.1,
    fun x => ?_⟩
  obtain ⟨x', rfl⟩ : ∃ x', polarRoot T x' = x :=
    ⟨(rootEquiv T hT.1).symm x, by rw [← rootEquiv_apply T hT.1, LinearEquiv.apply_symm_apply]⟩
  rw [polarFactor_root T hT.1, hint, ← polarRoot_comm hT.1 hH₀ hH₁ hint, polarFactor_root T hT.1]

end Intertwine

end FormalResearch.Racah.Polar

/-- info: 'FormalResearch.Racah.Polar.exists_posRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Polar.exists_posRoot

/-- info: 'FormalResearch.Racah.Polar.polarFactor_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Polar.polarFactor_basis

/-- info: 'FormalResearch.Racah.Polar.bijective_of_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Polar.bijective_of_basis

/-- info: 'FormalResearch.Racah.Polar.inner_polarFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Polar.inner_polarFactor

/-- info: 'FormalResearch.Racah.Polar.polarFactor_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Polar.polarFactor_intertwine

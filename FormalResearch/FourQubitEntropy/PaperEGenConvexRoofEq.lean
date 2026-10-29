import FormalResearch.FourQubitEntropy.ConvexRoof
import FormalResearch.FourQubitEntropy.EqualityMain
import FormalResearch.FourQubitEntropy.Tsallis
import FormalResearch.FourQubitEntropy.Renyi

/-!
# Pure-only equality for the mixed-state ceiling (`cor:fqe-convex-roof`)

`ConvexRoof.lean` proves the ceiling `⅓ Σ_j E_{g_j}(ρ) ≤ C` for every mixed state.  Here we prove the
equality half of `cor:fqe-convex-roof`: **no mixed state attains the ceiling**.

The paper's argument: every pure maximiser has full Schmidt rank on the `12|34` cut (it is a local
unitary image of `M₄` or `conj M₄`), whereas two independent vectors in the support of a mixed state
span a pencil of `4 × 4` flattenings with a singular nonzero member `χ`.  Some ensemble of `ρ`
contains `χ` with positive weight; `χ` is not a pure maximiser, so averaging the (non-strict) pure
bound over that one ensemble gives a strict inequality.

* `exists_singular_pencil`: `A, B` complex `4 × 4` ⟹ a unit pair `(α, β)` with `det (αA + βB) = 0`.
* `ensemble_with_singular`: a two-vector rotation of an ensemble puts a prescribed combination
  `αu + βv` into the ensemble with positive weight.
* `convexRoof_mean_lt`: the abstract strictness theorem.
* `convexRoof_vn_lt`, `convexRoof_tsallis_lt`, `convexRoof_renyi_lt`: the three ceilings of
  `ConvexRoof.lean` are strict on non-pure states (Rényi in the Lean range `0 < q < 1`).
* `ensemble_of_pure`, `convexRoof_pure`: the convex roof of a pure state is the value of the
  functional (every ensemble of `|ψ⟩⟨ψ|` consists of phases of `ψ`).
* `convexRoof_vn_eq_iff`, `convexRoof_tsallis_eq_iff`, `convexRoof_renyi_eq_iff`: the mean of the
  three roofs equals the ceiling iff `ρ = |ψ⟩⟨ψ|` with `ψ` in an `M₄` local-unitary orbit.

Trust: no `native_decide`, no placeholder proof and no new axiom here.  The sextic axiom of `Identity.lean` is
inherited exactly where `ConvexRoof.lean` already inherits it (through the pure-state ceilings).
-/

open scoped ComplexConjugate Matrix Kronecker ComplexOrder

namespace FormalResearch.FourQubitEntropy

/-! ### A singular member of a pencil -/

theorem exists_singular_pencil (A B : Mat4) :
    ∃ α β : ℂ, Complex.normSq α + Complex.normSq β = 1 ∧ (α • A + β • B).det = 0 := by
  classical
  suffices h : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ (α • A + β • B).det = 0 by
    obtain ⟨α, β, hne, hdet⟩ := h
    have hr : 0 < Complex.normSq α + Complex.normSq β := by
      rcases hne with h | h
      · have := Complex.normSq_pos.2 h
        have := Complex.normSq_nonneg β
        linarith
      · have := Complex.normSq_pos.2 h
        have := Complex.normSq_nonneg α
        linarith
    set r : ℝ := Real.sqrt (Complex.normSq α + Complex.normSq β) with hr_def
    have hrpos : 0 < r := Real.sqrt_pos.2 hr
    have hr2 : r ^ 2 = Complex.normSq α + Complex.normSq β := Real.sq_sqrt hr.le
    set c : ℂ := ((r⁻¹ : ℝ) : ℂ) with hc
    refine ⟨c * α, c * β, ?_, ?_⟩
    · rw [Complex.normSq_mul, Complex.normSq_mul, ← mul_add, hc, Complex.normSq_ofReal, ← hr2]
      field_simp
    · have : (c * α) • A + (c * β) • B = c • (α • A + β • B) := by
        rw [smul_add, smul_smul, smul_smul]
      rw [this, Matrix.det_smul, hdet, mul_zero]
  by_cases hB : B.det = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using hB⟩
  · have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (B⁻¹ * A))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have h1 : (B⁻¹ * A) *ᵥ v = μ • v := by
      have := hv.apply_eq_smul
      simpa [Matrix.toLin'_apply] using this
    have h2 : (A - μ • B) *ᵥ v = 0 := by
      have hA : A = B * (B⁻¹ * A) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
      have : A *ᵥ v = B *ᵥ ((B⁻¹ * A) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← hA]
      rw [Matrix.sub_mulVec, this, h1, Matrix.mulVec_smul, Matrix.smul_mulVec, sub_self]
    refine ⟨1, -μ, Or.inl one_ne_zero, ?_⟩
    have : (1 : ℂ) • A + (-μ) • B = A - μ • B := by
      rw [one_smul, neg_smul, sub_eq_add_neg]
    rw [this]
    exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv.2, h2⟩

/-! ### Pure maximisers have a non-singular flattening -/

theorem det_kron_ne_zero {a b : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    (kron a b).det ≠ 0 := by
  have h := congrArg Matrix.det (kron_unitary ha hb)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro h0
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem det_of_quadratic {Z R : Mat4} (hR : R = Z * Zᴴ)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) : Z.det ≠ 0 := by
  have h1 : R * R = (2 / 3 : ℂ) • R - (1 / 12 : ℂ) • 1 := by
    have e : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1)
        = R * R - (2 / 3 : ℂ) • R + (1 / 12 : ℂ) • 1 := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [e] at h
    rw [← sub_eq_zero]
    rw [← h]
    abel
  have h2 : R * ((12 : ℂ) • ((2 / 3 : ℂ) • (1 : Mat4) - R)) = 1 := by
    rw [mul_smul_comm, mul_sub, mul_smul_comm, mul_one, h1]
    module
  have hd : R.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h2
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  intro hz
  apply hd
  rw [hR, Matrix.det_mul, hz, zero_mul]

theorem det_zmat_M4_ne_zero : (zmat M4).det ≠ 0 :=
  det_of_quadratic (red12_zmat M4) red12_M4

theorem det_zmat_conj_M4_ne_zero : (zmat (Psi.conj M4)).det ≠ 0 := by
  intro h
  have hz : zmat (Psi.conj M4) = (zmat M4).map (starRingEnd ℂ) := by
    ext i j
    simp [zmat, Psi.conj]
  rw [hz, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_eq_zero] at h
  exact det_zmat_M4_ne_zero h

/-- A local-unitary image of `M₄` or `conj M₄` has a non-singular `12|34` flattening. -/
theorem det_zmat_ne_zero_of_LU {ψ : Psi} (h : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) :
    (zmat ψ).det ≠ 0 := by
  have key : ∀ {φ ψ : Psi}, (zmat φ).det ≠ 0 → LUEquiv φ ψ → (zmat ψ).det ≠ 0 := by
    rintro φ ψ hφ ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
    rw [zmat_localApply, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero (det_kron_ne_zero ha hb) hφ) (det_kron_ne_zero hc hd)
  rcases h with h | h
  · exact key det_zmat_M4_ne_zero h
  · exact key det_zmat_conj_M4_ne_zero h

/-! ### Rotating two members of an ensemble -/

theorem normSqPsi_smul (c : ℂ) (ψ : Psi) : normSqPsi (c • ψ) = Complex.normSq c * normSqPsi ψ := by
  simp [normSqPsi, Complex.normSq_mul]
  ring

theorem normSqPsi_eq_sum (ψ : Psi) : normSqPsi ψ = ∑ x, Complex.normSq (vecOf ψ x) :=
  normSqPsi_psiOf (vecOf ψ)

theorem eq_zero_of_normSqPsi_eq_zero {ψ : Psi} (h : normSqPsi ψ = 0) : ψ = 0 := by
  rw [normSqPsi_eq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)).1 h
  funext a b c d
  have h1 := this (a, b, c, d) (Finset.mem_univ _)
  simpa [vecOf] using h1

theorem normSqPsi_pos_of_ne {ψ : Psi} (h : ψ ≠ 0) : 0 < normSqPsi ψ :=
  lt_of_le_of_ne (normSqPsi_nonneg ψ) fun h0 => h (eq_zero_of_normSqPsi_eq_zero h0.symm)

theorem projPsi_smul (c : ℂ) (ψ : Psi) :
    projPsi (c • ψ) = (Complex.normSq c : ℂ) • projPsi ψ := by
  ext x y
  simp only [projPsi, vecOf, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    Matrix.smul_apply]
  rw [← Complex.mul_conj c]
  ring

theorem zmat_smul (c : ℂ) (ψ : Psi) : zmat (c • ψ) = c • zmat ψ := by
  ext i j
  simp [zmat]

theorem zmat_add (ψ φ : Psi) : zmat (ψ + φ) = zmat ψ + zmat φ := by
  ext i j
  simp [zmat]

/-- The unitary rotation `(u, v) ↦ (αu + βv, -β̄u + ᾱv)` preserves `|u⟩⟨u| + |v⟩⟨v|`. -/
theorem projPsi_rotate {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) (u v : Psi) :
    projPsi (α • u + β • v) + projPsi ((-conj β) • u + conj α • v) = projPsi u + projPsi v := by
  have h' : α * conj α + β * conj β = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj]
    exact_mod_cast h
  ext x y
  simp only [projPsi, vecOf, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    map_add, map_neg, Complex.conj_conj, Matrix.add_apply]
  linear_combination (u x.1 x.2.1 x.2.2.1 x.2.2.2 * conj (u y.1 y.2.1 y.2.2.1 y.2.2.2)
    + v x.1 x.2.1 x.2.2.1 x.2.2.2 * conj (v y.1 y.2.1 y.2.2.1 y.2.2.2)) * h'

theorem normSqPsi_rotate {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) (u v : Psi) :
    normSqPsi (α • u + β • v) + normSqPsi ((-conj β) • u + conj α • v)
      = normSqPsi u + normSqPsi v := by
  simp only [normSqPsi_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [vecOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  generalize u x.1 x.2.1 x.2.2.1 x.2.2.2 = p
  generalize v x.1 x.2.1 x.2.2.1 x.2.2.2 = q
  have : Complex.normSq (α * p + β * q) + Complex.normSq (-conj β * p + conj α * q)
      = (Complex.normSq α + Complex.normSq β) * (Complex.normSq p + Complex.normSq q) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [this, h, one_mul]

/-- Two members `a ≠ b` of an ensemble with positive weights and independent vectors can be
rotated so that the new ensemble contains a prescribed singular combination, with positive weight. -/
theorem ensemble_with_singular {ρ : Mat16} {n : ℕ} {p : Fin n → ℝ} {ψ : Fin n → Psi}
    (hp : ∀ l, 0 ≤ p l) (hs : ∑ l, p l = 1) (hu : ∀ l, normSqPsi (ψ l) = 1)
    (he : ρ = ∑ l, (p l : ℂ) • projPsi (ψ l)) {a b : Fin n} (hab : a ≠ b)
    (hpa : 0 < p a) (hpb : 0 < p b)
    (hind : ∀ s t : ℂ, s • ψ a + t • ψ b = 0 → s = 0 ∧ t = 0) :
    ∃ (p' : Fin n → ℝ) (ψ' : Fin n → Psi) (c : Fin n), (∀ l, 0 ≤ p' l) ∧ ∑ l, p' l = 1 ∧
      (∀ l, normSqPsi (ψ' l) = 1) ∧ ρ = ∑ l, (p' l : ℂ) • projPsi (ψ' l) ∧ 0 < p' c ∧
      (zmat (ψ' c)).det = 0 := by
  classical
  set u : Psi := ((Real.sqrt (p a) : ℝ) : ℂ) • ψ a with hu_def
  set v : Psi := ((Real.sqrt (p b) : ℝ) : ℂ) • ψ b with hv_def
  have hu_n : normSqPsi u = p a := by
    rw [hu_def, normSqPsi_smul, hu, mul_one, Complex.normSq_ofReal, Real.mul_self_sqrt hpa.le]
  have hv_n : normSqPsi v = p b := by
    rw [hv_def, normSqPsi_smul, hu, mul_one, Complex.normSq_ofReal, Real.mul_self_sqrt hpb.le]
  have hpu : projPsi u = (p a : ℂ) • projPsi (ψ a) := by
    rw [hu_def, projPsi_smul, Complex.normSq_ofReal, Real.mul_self_sqrt hpa.le]
  have hpv : projPsi v = (p b : ℂ) • projPsi (ψ b) := by
    rw [hv_def, projPsi_smul, Complex.normSq_ofReal, Real.mul_self_sqrt hpb.le]
  have hsa : (Real.sqrt (p a) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpa).ne'
  have hsb : (Real.sqrt (p b) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpb).ne'
  have hind' : ∀ s t : ℂ, s • u + t • v = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h' : (s * (Real.sqrt (p a) : ℂ)) • ψ a + (t * (Real.sqrt (p b) : ℂ)) • ψ b = 0 := by
      rw [hu_def, hv_def, smul_smul, smul_smul] at h
      exact h
    obtain ⟨h1, h2⟩ := hind _ _ h'
    exact ⟨(mul_eq_zero.1 h1).resolve_right hsa, (mul_eq_zero.1 h2).resolve_right hsb⟩
  obtain ⟨α, β, hαβ, hdet⟩ := exists_singular_pencil (zmat u) (zmat v)
  set φ₁ : Psi := α • u + β • v with hφ₁
  set φ₂ : Psi := (-conj β) • u + conj α • v with hφ₂
  have hne : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [hcon.1, hcon.2] at hαβ
    simp at hαβ
  have hφ₁ne : φ₁ ≠ 0 := fun h => by
    obtain ⟨h1, h2⟩ := hind' α β h
    rcases hne with h3 | h3
    · exact h3 h1
    · exact h3 h2
  have hφ₂ne : φ₂ ≠ 0 := fun h => by
    obtain ⟨h1, h2⟩ := hind' _ _ h
    rcases hne with h3 | h3
    · exact h3 (by simpa using h2)
    · exact h3 (by simpa using h1)
  have hN₁ : 0 < normSqPsi φ₁ := normSqPsi_pos_of_ne hφ₁ne
  have hN₂ : 0 < normSqPsi φ₂ := normSqPsi_pos_of_ne hφ₂ne
  have hN : normSqPsi φ₁ + normSqPsi φ₂ = p a + p b := by
    rw [hφ₁, hφ₂, normSqPsi_rotate hαβ, hu_n, hv_n]
  have hP : projPsi φ₁ + projPsi φ₂ = (p a : ℂ) • projPsi (ψ a) + (p b : ℂ) • projPsi (ψ b) := by
    rw [hφ₁, hφ₂, projPsi_rotate hαβ, hpu, hpv]
  set N₁ := normSqPsi φ₁ with hN₁def
  set N₂ := normSqPsi φ₂ with hN₂def
  set c₁ : ℂ := (((Real.sqrt N₁)⁻¹ : ℝ) : ℂ) with hc₁
  set c₂ : ℂ := (((Real.sqrt N₂)⁻¹ : ℝ) : ℂ) with hc₂
  have hc₁n : Complex.normSq c₁ * N₁ = 1 := by
    rw [hc₁, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hN₁.le,
      inv_mul_cancel₀ hN₁.ne']
  have hc₂n : Complex.normSq c₂ * N₂ = 1 := by
    rw [hc₂, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hN₂.le,
      inv_mul_cancel₀ hN₂.ne']
  let p' : Fin n → ℝ := fun l => if l = a then N₁ else if l = b then N₂ else p l
  let ψ' : Fin n → Psi := fun l => if l = a then c₁ • φ₁ else if l = b then c₂ • φ₂ else ψ l
  have hp'a : p' a = N₁ := by simp [p']
  have hp'b : p' b = N₂ := by simp [p', hab.symm]
  have hψ'a : ψ' a = c₁ • φ₁ := by simp [ψ']
  have hψ'b : ψ' b = c₂ • φ₂ := by simp [ψ', hab.symm]
  have hoff : ∀ l, l ≠ a → l ≠ b → p' l = p l ∧ ψ' l = ψ l := fun l h1 h2 => by
    simp [p', ψ', h1, h2]
  refine ⟨p', ψ', a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    by_cases h1 : l = a
    · subst h1; rw [hp'a]; exact hN₁.le
    by_cases h2 : l = b
    · subst h2; rw [hp'b]; exact hN₂.le
    rw [(hoff l h1 h2).1]; exact hp l
  · have h0 : ∑ l, (p' l - p l) = 0 := by
      rw [Finset.sum_eq_add a b hab (fun l _ hl => by rw [(hoff l hl.1 hl.2).1, sub_self])
        (by simp) (by simp), hp'a, hp'b]
      linarith
    rw [Finset.sum_sub_distrib] at h0
    linarith
  · intro l
    by_cases h1 : l = a
    · subst h1; rw [hψ'a, normSqPsi_smul, hc₁n]
    by_cases h2 : l = b
    · subst h2; rw [hψ'b, normSqPsi_smul, hc₂n]
    rw [(hoff l h1 h2).2]; exact hu l
  · have h0 : ∑ l, ((p' l : ℂ) • projPsi (ψ' l) - (p l : ℂ) • projPsi (ψ l)) = 0 := by
      rw [Finset.sum_eq_add a b hab (fun l _ hl => by
          rw [(hoff l hl.1 hl.2).1, (hoff l hl.1 hl.2).2, sub_self]) (by simp) (by simp)]
      rw [hp'a, hp'b, hψ'a, hψ'b, projPsi_smul, projPsi_smul, smul_smul, smul_smul]
      have e1 : (N₁ : ℂ) * (Complex.normSq c₁ : ℂ) = 1 := by
        rw [mul_comm]; exact_mod_cast hc₁n
      have e2 : (N₂ : ℂ) * (Complex.normSq c₂ : ℂ) = 1 := by
        rw [mul_comm]; exact_mod_cast hc₂n
      rw [e1, e2, one_smul, one_smul, sub_add_sub_comm, hP, sub_self]
    rw [Finset.sum_sub_distrib, sub_eq_zero] at h0
    rw [he, h0]
  · rw [hp'a]; exact hN₁
  · have hz : zmat φ₁ = α • zmat u + β • zmat v := by
      rw [hφ₁, zmat_add, zmat_smul α u, zmat_smul β v]
    rw [hψ'a, zmat_smul, Matrix.det_smul, hz, hdet, mul_zero]

/-! ### Strictness for non-pure states -/

/-- A non-pure ensemble contains two members of positive weight with independent vectors. -/
theorem exists_independent_pair {ρ : Mat16} {n : ℕ} {p : Fin n → ℝ} {ψ : Fin n → Psi}
    (hp : ∀ l, 0 ≤ p l) (hs : ∑ l, p l = 1) (hu : ∀ l, normSqPsi (ψ l) = 1)
    (he : ρ = ∑ l, (p l : ℂ) • projPsi (ψ l))
    (hmixed : ¬ ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ) :
    ∃ a b : Fin n, a ≠ b ∧ 0 < p a ∧ 0 < p b ∧
      ∀ s t : ℂ, s • ψ a + t • ψ b = 0 → s = 0 ∧ t = 0 := by
  by_contra H
  push Not at H
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, 0 < p a₀ := by
    by_contra h0
    push Not at h0
    have : ∑ l, p l = 0 := Finset.sum_eq_zero fun l _ => le_antisymm (h0 l) (hp l)
    rw [this] at hs
    exact zero_ne_one hs
  apply hmixed
  refine ⟨ψ a₀, hu a₀, ?_⟩
  have hterm : ∀ l, (p l : ℂ) • projPsi (ψ l) = (p l : ℂ) • projPsi (ψ a₀) := by
    intro l
    rcases (hp l).eq_or_lt with h0 | hl
    · rw [← h0]; simp
    by_cases hla : l = a₀
    · rw [hla]
    obtain ⟨s, t, h1, h2⟩ := H a₀ l (Ne.symm hla) ha₀ hl
    have e : t • ψ l = (-s) • ψ a₀ := by
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_right h1
    have hn := congrArg normSqPsi e
    rw [normSqPsi_smul, normSqPsi_smul, hu, hu, Complex.normSq_neg] at hn
    have hpr := congrArg projPsi e
    rw [projPsi_smul, projPsi_smul, Complex.normSq_neg] at hpr
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0] at hn
      simp only [map_zero, mul_one] at hn
      have hs0 : s = 0 := Complex.normSq_eq_zero.1 hn.symm
      exact h2 hs0 ht0
    have ht' : (Complex.normSq t : ℂ) ≠ 0 := by
      exact_mod_cast (Complex.normSq_pos.2 ht).ne'
    have hts : Complex.normSq s = Complex.normSq t := by simpa using hn.symm
    rw [hts] at hpr
    rw [(smul_right_inj ht').1 hpr]
  rw [he, Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_smul]
  have : ∑ l, (p l : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hs]; simp
  rw [this, one_smul]

/-- **Strictness for non-pure states** (`cor:fqe-convex-roof`, abstract form).  Suppose the cut
functionals are nonnegative with mean at most `C` on unit vectors, and that the mean is strictly below
`C` on every unit vector with a singular `12|34` flattening.  Then the mean of the three convex roofs
of every non-pure state is strictly below `C`. -/
theorem convexRoof_mean_lt {g₂ g₃ g₄ : Psi → ℝ} (h₂ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₂ ψ)
    (h₃ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₃ ψ) (h₄ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₄ ψ) {C : ℝ}
    (hC : ∀ ψ, normSqPsi ψ = 1 → (g₂ ψ + g₃ ψ + g₄ ψ) / 3 ≤ C)
    (hsing : ∀ ψ, normSqPsi ψ = 1 → (zmat ψ).det = 0 → (g₂ ψ + g₃ ψ + g₄ ψ) / 3 < C)
    {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1)
    (hmixed : ¬ ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ) :
    (convexRoof g₂ ρ + convexRoof g₃ ρ + convexRoof g₄ ρ) / 3 < C := by
  obtain ⟨n, p, ψ, hp, hs, hu, he⟩ := exists_ensemble hρ htr
  obtain ⟨a, b, hab, hpa, hpb, hind⟩ := exists_independent_pair hp hs hu he hmixed
  obtain ⟨p', ψ', c, hp', hs', hu', he', hpc, hdet⟩ :=
    ensemble_with_singular hp hs hu he hab hpa hpb hind
  have a2 := convexRoof_le_ensemble h₂ hp' hs' hu' he'
  have a3 := convexRoof_le_ensemble h₃ hp' hs' hu' he'
  have a4 := convexRoof_le_ensemble h₄ hp' hs' hu' he'
  have key : ∑ l, p' l * g₂ (ψ' l) + ∑ l, p' l * g₃ (ψ' l) + ∑ l, p' l * g₄ (ψ' l) < 3 * C := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc ∑ l, (p' l * g₂ (ψ' l) + p' l * g₃ (ψ' l) + p' l * g₄ (ψ' l))
        < ∑ l, p' l * (3 * C) := by
          refine Finset.sum_lt_sum (fun l _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
          · have := hC (ψ' l) (hu' l)
            nlinarith [hp' l]
          · have := hsing (ψ' c) (hu' c) hdet
            nlinarith [hpc]
      _ = 3 * C := by rw [← Finset.sum_mul, hs']; ring
  linarith

/-- **Von Neumann case:** no non-pure four-qubit state attains `1 + ½ log₂ 3` as the mean of the
three bipartite entanglements of formation. -/
theorem convexRoof_vn_lt {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1)
    (hmixed : ¬ ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ) :
    (convexRoof (fun ψ => vnEntropy (red12_herm ψ)) ρ + convexRoof (fun ψ => vnEntropy (red13_herm ψ)) ρ
      + convexRoof (fun ψ => vnEntropy (red14_herm ψ)) ρ) / 3 < 1 + Real.log 3 / (2 * Real.log 2) :=
  convexRoof_mean_lt (fun _ h => vnEntropy12_nonneg h) (fun _ h => vnEntropy13_nonneg h)
    (fun _ h => vnEntropy14_nonneg h) (fun ψ h => meanEntropy_le ψ h)
    (fun ψ h hd => lt_of_le_of_ne (meanEntropy_le ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((meanEntropy_eq_max_iff ψ h).1 heq) hd) hρ htr hmixed

/-- **Tsallis case** (`0 < q < 2`, `q ≠ 1`). -/
theorem convexRoof_tsallis_lt {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ρ : Mat16}
    (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1)
    (hmixed : ¬ ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ) :
    (convexRoof (fun ψ => tsallisCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => tsallisCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => tsallisCut q (red14_herm ψ)) ρ) / 3 < tsallisCeiling q :=
  convexRoof_mean_lt
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => tsallis_le h0 h2 h1 ψ h)
    (fun ψ h hd => lt_of_le_of_ne (tsallis_le h0 h2 h1 ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((tsallis_eq_iff h0 h2 h1 ψ h).1 heq) hd) hρ htr hmixed

/-- **Rényi case** (`0 < q < 1`). -/
theorem convexRoof_renyi_lt {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {ρ : Mat16} (hρ : ρ.PosSemidef)
    (htr : (Matrix.trace ρ).re = 1) (hmixed : ¬ ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ) :
    (convexRoof (fun ψ => renyiCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => renyiCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => renyiCut q (red14_herm ψ)) ρ) / 3 <
      Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q) :=
  convexRoof_mean_lt
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => renyi_le h0 h1 ψ h)
    (fun ψ h hd => lt_of_le_of_ne (renyi_le h0 h1 ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((renyi_eq_iff h0 h1 ψ h).1 heq) hd) hρ htr hmixed

/-! ### Pure states: the convex roof is the value -/

/-- The inner product `⟨φ, χ⟩ = Σ_x conj (φ x) χ x`. -/
def ip (φ χ : Psi) : ℂ := ∑ x, conj (vecOf φ x) * vecOf χ x

theorem ip_comm (φ χ : Psi) : ip φ χ = conj (ip χ φ) := by
  simp [ip, map_sum, mul_comm]

theorem ip_self (φ : Psi) : ip φ φ = (normSqPsi φ : ℂ) := by
  rw [normSqPsi_eq_sum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => Complex.normSq_eq_conj_mul_self.symm

theorem ip_sub_smul_right (φ a b : Psi) (c : ℂ) : ip φ (a - c • b) = ip φ a - c * ip φ b := by
  simp only [ip, vecOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => by ring

theorem ip_sub_smul_left (a b χ : Psi) (c : ℂ) :
    ip (a - c • b) χ = ip a χ - conj c * ip b χ := by
  simp only [ip, vecOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => by ring

/-- `⟨φ|M|φ⟩` for a matrix `M`. -/
def quadForm (φ : Psi) (M : Mat16) : ℂ := ∑ x, ∑ y, conj (vecOf φ x) * M x y * vecOf φ y

theorem quadForm_projPsi (φ χ : Psi) : quadForm φ (projPsi χ) = ip φ χ * conj (ip φ χ) := by
  unfold quadForm ip
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [projPsi, Matrix.of_apply, map_mul, Complex.conj_conj]
  ring

theorem quadForm_sum {n : ℕ} (φ : Psi) (c : Fin n → ℂ) (M : Fin n → Mat16) :
    quadForm φ (∑ l, c l • M l) = ∑ l, c l * quadForm φ (M l) := by
  simp only [quadForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun l _ => by ring

theorem normSq_ip_ensemble {ψ : Psi} {n : ℕ} {p : Fin n → ℝ} {ψ' : Fin n → Psi}
    (he : projPsi ψ = ∑ l, (p l : ℂ) • projPsi (ψ' l)) (φ : Psi) :
    Complex.normSq (ip φ ψ) = ∑ l, p l * Complex.normSq (ip φ (ψ' l)) := by
  have h := congrArg (quadForm φ) he
  rw [quadForm_sum, quadForm_projPsi] at h
  simp only [quadForm_projPsi] at h
  rw [Complex.mul_conj] at h
  have h' : ∀ l, (p l : ℂ) * (ip φ (ψ' l) * conj (ip φ (ψ' l))) = ((p l * Complex.normSq (ip φ (ψ' l)) : ℝ) : ℂ) := by
    intro l; rw [Complex.mul_conj]; push_cast; ring
  simp only [h'] at h
  rw [← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Every member of positive weight of an ensemble of a pure state is a phase times that state. -/
theorem ensemble_of_pure {ψ : Psi} (hψ : normSqPsi ψ = 1) {n : ℕ} {p : Fin n → ℝ}
    {ψ' : Fin n → Psi} (hp : ∀ l, 0 ≤ p l) (hu : ∀ l, normSqPsi (ψ' l) = 1)
    (he : projPsi ψ = ∑ l, (p l : ℂ) • projPsi (ψ' l)) {l : Fin n} (hl : 0 < p l) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧ ψ' l = c • ψ := by
  set s : ℂ := ip ψ (ψ' l) with hs
  set φ : Psi := ψ' l - s • ψ with hφ
  have hψψ : ip ψ ψ = 1 := by rw [ip_self, hψ]; simp
  have hll : ip (ψ' l) (ψ' l) = 1 := by rw [ip_self, hu]; simp
  have hφψ : ip φ ψ = 0 := by
    rw [hφ, ip_sub_smul_left, hψψ, ip_comm (ψ' l) ψ, ← hs]; ring
  have hφl : ip φ (ψ' l) = 1 - (Complex.normSq s : ℂ) := by
    rw [hφ, ip_sub_smul_left, hll, Complex.normSq_eq_conj_mul_self]
  have hsum := normSq_ip_ensemble he φ
  rw [hφψ, map_zero] at hsum
  have hnn : ∀ k, 0 ≤ p k * Complex.normSq (ip φ (ψ' k)) := fun k =>
    mul_nonneg (hp k) (Complex.normSq_nonneg _)
  have hle : p l * Complex.normSq (ip φ (ψ' l)) ≤ 0 := by
    rw [hsum]
    exact Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ l)
  have h0 : Complex.normSq (ip φ (ψ' l)) = 0 := by
    have := Complex.normSq_nonneg (ip φ (ψ' l))
    by_contra hne
    have hpos : 0 < Complex.normSq (ip φ (ψ' l)) := lt_of_le_of_ne this (Ne.symm hne)
    nlinarith
  have hs1 : Complex.normSq s = 1 := by
    have := Complex.normSq_eq_zero.1 h0
    rw [hφl] at this
    have h2 : (Complex.normSq s : ℂ) = 1 := by linear_combination -this
    exact_mod_cast h2
  have hφφ : ip φ φ = 0 := by
    have : φ = ψ' l - s • ψ := rfl
    conv_lhs => rw [this, ip_sub_smul_right, hφψ, hφl]
    rw [hs1]; simp
  rw [ip_self] at hφφ
  have hφ0 : φ = 0 := eq_zero_of_normSqPsi_eq_zero (by exact_mod_cast hφφ)
  exact ⟨s, hs1, sub_eq_zero.1 hφ0⟩

theorem convexRoof_pure {g : Psi → ℝ} (hg : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g ψ)
    (hph : ∀ (ψ : Psi) (c : ℂ), normSqPsi ψ = 1 → Complex.normSq c = 1 → g (c • ψ) = g ψ)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) : convexRoof g (projPsi ψ) = g ψ := by
  have h1 : (projPsi ψ) = ∑ l : Fin 1, ((fun _ => (1 : ℝ)) l : ℂ) • projPsi ((fun _ => ψ) l) := by
    simp
  apply le_antisymm
  · have := convexRoof_le_ensemble (g := g) (ρ := projPsi ψ) (n := 1) (p := fun _ => 1)
      (ψ := fun _ => ψ) hg (fun _ => zero_le_one) (by simp) (fun _ => hψ) h1
    simpa using this
  · refine le_csInf ⟨_, 1, fun _ => 1, fun _ => ψ, fun _ => zero_le_one, by simp, fun _ => hψ, h1,
      rfl⟩ ?_
    rintro v ⟨n, p, ψ', hp, hs, hu, he, rfl⟩
    have : ∀ l, p l * g ψ ≤ p l * g (ψ' l) := by
      intro l
      rcases (hp l).eq_or_lt with h0 | hl
      · rw [← h0]; simp
      · obtain ⟨c, hc, hcl⟩ := ensemble_of_pure hψ hp hu he hl
        rw [hcl, hph ψ c hψ hc]
    calc g ψ = ∑ l, p l * g ψ := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ ∑ l, p l * g (ψ' l) := Finset.sum_le_sum fun l _ => this l

/-- **Equality case, abstract form.** Under the hypotheses of `convexRoof_mean_lt` and phase
invariance of the cut functionals, the mean of the three convex roofs equals `C` exactly at the pure
states `|ψ⟩⟨ψ|` whose own mean equals `C`. -/
theorem convexRoof_mean_eq_iff {g₂ g₃ g₄ : Psi → ℝ} (h₂ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₂ ψ)
    (h₃ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₃ ψ) (h₄ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₄ ψ) {C : ℝ}
    (hC : ∀ ψ, normSqPsi ψ = 1 → (g₂ ψ + g₃ ψ + g₄ ψ) / 3 ≤ C)
    (hsing : ∀ ψ, normSqPsi ψ = 1 → (zmat ψ).det = 0 → (g₂ ψ + g₃ ψ + g₄ ψ) / 3 < C)
    (hph₂ : ∀ (ψ : Psi) (c : ℂ), normSqPsi ψ = 1 → Complex.normSq c = 1 → g₂ (c • ψ) = g₂ ψ)
    (hph₃ : ∀ (ψ : Psi) (c : ℂ), normSqPsi ψ = 1 → Complex.normSq c = 1 → g₃ (c • ψ) = g₃ ψ)
    (hph₄ : ∀ (ψ : Psi) (c : ℂ), normSqPsi ψ = 1 → Complex.normSq c = 1 → g₄ (c • ψ) = g₄ ψ)
    {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof g₂ ρ + convexRoof g₃ ρ + convexRoof g₄ ρ) / 3 = C ↔
      ∃ ψ, normSqPsi ψ = 1 ∧ ρ = projPsi ψ ∧ (g₂ ψ + g₃ ψ + g₄ ψ) / 3 = C := by
  constructor
  · intro h
    by_cases hmixed : ∃ φ, normSqPsi φ = 1 ∧ ρ = projPsi φ
    · obtain ⟨φ, hφ, rfl⟩ := hmixed
      refine ⟨φ, hφ, rfl, ?_⟩
      rw [convexRoof_pure h₂ hph₂ hφ, convexRoof_pure h₃ hph₃ hφ, convexRoof_pure h₄ hph₄ hφ] at h
      exact h
    · exact absurd h (convexRoof_mean_lt h₂ h₃ h₄ hC hsing hρ htr hmixed).ne
  · rintro ⟨φ, hφ, rfl, hv⟩
    rw [convexRoof_pure h₂ hph₂ hφ, convexRoof_pure h₃ hph₃ hφ, convexRoof_pure h₄ hph₄ hφ]
    exact hv

/-! ### Phase invariance and the three equality statements -/

theorem red12_phase {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Psi) : red12 (c • ψ) = red12 ψ := by
  have hc' : c * conj c = 1 := by rw [Complex.mul_conj, hc]; simp
  ext i j
  simp only [red12, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (ψ i.1 i.2 a b * conj (ψ j.1 j.2 a b)) * hc'

theorem red13_phase {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Psi) : red13 (c • ψ) = red13 ψ := by
  have hc' : c * conj c = 1 := by rw [Complex.mul_conj, hc]; simp
  ext i j
  simp only [red13, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (ψ i.1 a i.2 b * conj (ψ j.1 a j.2 b)) * hc'

theorem red14_phase {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Psi) : red14 (c • ψ) = red14 ψ := by
  have hc' : c * conj c = 1 := by rw [Complex.mul_conj, hc]; simp
  ext i j
  simp only [red14, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (ψ i.1 a b i.2 * conj (ψ j.1 a b j.2)) * hc'

theorem vnEntropy_congr {R S : Mat4} (h : R = S) (hR : R.IsHermitian) (hS : S.IsHermitian) :
    vnEntropy hR = vnEntropy hS := by
  subst h; rfl

theorem tsallisCut_congr (q : ℝ) {R S : Mat4} (h : R = S) (hR : R.IsHermitian)
    (hS : S.IsHermitian) : tsallisCut q hR = tsallisCut q hS := by
  subst h; rfl

theorem renyiCut_congr (q : ℝ) {R S : Mat4} (h : R = S) (hR : R.IsHermitian)
    (hS : S.IsHermitian) : renyiCut q hR = renyiCut q hS := by
  subst h; rfl

/-- **No mixed maximiser, and the pure maximisers** (von Neumann case of `cor:fqe-convex-roof`): the
mean of the three bipartite entanglements of formation of `ρ` equals `1 + ½ log₂ 3` if and only if
`ρ = |ψ⟩⟨ψ|` for a unit vector `ψ` in one of the two `M₄` local-unitary orbits. -/
theorem convexRoof_vn_eq_iff {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => vnEntropy (red12_herm ψ)) ρ + convexRoof (fun ψ => vnEntropy (red13_herm ψ)) ρ
      + convexRoof (fun ψ => vnEntropy (red14_herm ψ)) ρ) / 3 = 1 + Real.log 3 / (2 * Real.log 2) ↔
    ∃ ψ, normSqPsi ψ = 1 ∧ ρ = projPsi ψ ∧ (LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) := by
  rw [convexRoof_mean_eq_iff (fun _ h => vnEntropy12_nonneg h) (fun _ h => vnEntropy13_nonneg h)
    (fun _ h => vnEntropy14_nonneg h) (fun ψ h => meanEntropy_le ψ h)
    (fun ψ h hd => lt_of_le_of_ne (meanEntropy_le ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((meanEntropy_eq_max_iff ψ h).1 heq) hd)
    (fun ψ c _ hc => vnEntropy_congr (red12_phase hc ψ) _ _)
    (fun ψ c _ hc => vnEntropy_congr (red13_phase hc ψ) _ _)
    (fun ψ c _ hc => vnEntropy_congr (red14_phase hc ψ) _ _) hρ htr]
  constructor
  · rintro ⟨ψ, h1, h2, h3⟩
    exact ⟨ψ, h1, h2, (meanEntropy_eq_max_iff ψ h1).1 h3⟩
  · rintro ⟨ψ, h1, h2, h3⟩
    exact ⟨ψ, h1, h2, (meanEntropy_eq_max_iff ψ h1).2 h3⟩

/-- **Tsallis case** of the equality classification (`0 < q < 2`, `q ≠ 1`). -/
theorem convexRoof_tsallis_eq_iff {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ρ : Mat16}
    (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => tsallisCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => tsallisCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => tsallisCut q (red14_herm ψ)) ρ) / 3 = tsallisCeiling q ↔
    ∃ ψ, normSqPsi ψ = 1 ∧ ρ = projPsi ψ ∧ (LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) := by
  rw [convexRoof_mean_eq_iff
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => tsallis_le h0 h2 h1 ψ h)
    (fun ψ h hd => lt_of_le_of_ne (tsallis_le h0 h2 h1 ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((tsallis_eq_iff h0 h2 h1 ψ h).1 heq) hd)
    (fun ψ c _ hc => tsallisCut_congr q (red12_phase hc ψ) _ _)
    (fun ψ c _ hc => tsallisCut_congr q (red13_phase hc ψ) _ _)
    (fun ψ c _ hc => tsallisCut_congr q (red14_phase hc ψ) _ _) hρ htr]
  constructor
  · rintro ⟨ψ, h1', h2', h3⟩
    exact ⟨ψ, h1', h2', (tsallis_eq_iff h0 h2 h1 ψ h1').1 h3⟩
  · rintro ⟨ψ, h1', h2', h3⟩
    exact ⟨ψ, h1', h2', (tsallis_eq_iff h0 h2 h1 ψ h1').2 h3⟩

/-- **Rényi case** of the equality classification (`0 < q < 1`). -/
theorem convexRoof_renyi_eq_iff {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {ρ : Mat16}
    (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => renyiCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => renyiCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => renyiCut q (red14_herm ψ)) ρ) / 3 =
      Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q) ↔
    ∃ ψ, normSqPsi ψ = 1 ∧ ρ = projPsi ψ ∧ (LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ) := by
  rw [convexRoof_mean_eq_iff
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => renyi_le h0 h1 ψ h)
    (fun ψ h hd => lt_of_le_of_ne (renyi_le h0 h1 ψ h) fun heq =>
      det_zmat_ne_zero_of_LU ((renyi_eq_iff h0 h1 ψ h).1 heq) hd)
    (fun ψ c _ hc => renyiCut_congr q (red12_phase hc ψ) _ _)
    (fun ψ c _ hc => renyiCut_congr q (red13_phase hc ψ) _ _)
    (fun ψ c _ hc => renyiCut_congr q (red14_phase hc ψ) _ _) hρ htr]
  constructor
  · rintro ⟨ψ, h1', h2', h3⟩
    exact ⟨ψ, h1', h2', (renyi_eq_iff h0 h1 ψ h1').1 h3⟩
  · rintro ⟨ψ, h1', h2', h3⟩
    exact ⟨ψ, h1', h2', (renyi_eq_iff h0 h1 ψ h1').2 h3⟩

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_mean_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convexRoof_mean_lt

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_vn_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_vn_lt
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_tsallis_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_tsallis_lt
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_renyi_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_renyi_lt
/-- info: 'FormalResearch.FourQubitEntropy.det_zmat_ne_zero_of_LU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_zmat_ne_zero_of_LU

/-- info: 'FormalResearch.FourQubitEntropy.exists_singular_pencil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_singular_pencil
/-- info: 'FormalResearch.FourQubitEntropy.ensemble_with_singular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ensemble_with_singular
/-- info: 'FormalResearch.FourQubitEntropy.ensemble_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ensemble_of_pure
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convexRoof_pure
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_mean_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convexRoof_mean_eq_iff
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_vn_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_vn_eq_iff
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_tsallis_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_tsallis_eq_iff
/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_renyi_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_renyi_eq_iff

end FormalResearch.FourQubitEntropy

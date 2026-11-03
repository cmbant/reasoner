import FormalResearch.PPTThreeQubit.Basic

/-!
# The quartic moment cone of a five-dimensional support (general part)

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/relaxations_and_scope.tex`,
`thm:ppt3-universal-moments` and its proof in `appendix_moment_cone.tex`.

This file formalises the part of the theorem that is independent of how the matrices `T_c` arise:
given a full-column-rank `B : 8 × 5` and, for each cut `c`, a `5 × 5` matrix `T_c` such that the cut-`c`
product vectors of `range B` are exactly the multiples of `B T_c ν(a)` (hypothesis `CutCurve`),

* `biseparable_iff_mem_cone`: `B X Bᴴ` is biseparable iff `X` lies in `∑_c T_c 𝓜₄ T_cᴴ`
  (eq. `eq:ppt3-universal-bs`), where `𝓜₄` is the cone on `ν(a)ν(a)ᴴ`;
* `dual_iff`: `Re tr(H X) ≥ 0` for every biseparable `B X Bᴴ` iff the three quartic forms
  `ν(a)ᴴ T_cᴴ H T_c ν(a)` are nonnegative (eq. `eq:ppt3-universal-dual`).

`mem_range_of_sum_eq` is the paper's remark that a positive decomposition of an operator supported on
`range B` uses only vectors of `range B`.  Invertibility of `T_c` is not needed for these equivalences.
Not formalised here: the Carathéodory bound "at most 25 terms" and closedness of the cone.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Positive decompositions of an operator supported on `range B` -/

section Support

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- A full-column-rank matrix has a left inverse. -/
theorem exists_left_inverse (B : Matrix m k ℂ) (hB : Function.Injective B.mulVec) :
    ∃ L : Matrix k m ℂ, L * B = 1 := by
  have hG : IsUnit (Bᴴ * B) := (Matrix.PosDef.conjTranspose_mul_self B hB).isUnit
  have hd : IsUnit (Bᴴ * B).det := (Matrix.isUnit_iff_isUnit_det _).1 hG
  refine ⟨(Bᴴ * B)⁻¹ * Bᴴ, ?_⟩
  rw [Matrix.mul_assoc, nonsing_inv_mul _ hd]

/-- A positive decomposition `∑ᵢ |φᵢ⟩⟨φᵢ| = B X Bᴴ` of an operator supported on `range B` uses only
vectors in `range B`. -/
theorem mem_range_of_sum_eq (B : Matrix m k ℂ) (hB : Function.Injective B.mulVec) {n : ℕ}
    (φ : Fin n → m → ℂ) (X : Matrix k k ℂ)
    (h : ∑ i, vecMulVec (φ i) (star (φ i)) = B * X * Bᴴ) (i : Fin n) : ∃ y, φ i = B *ᵥ y := by
  have hG : IsUnit (Bᴴ * B) := (Matrix.PosDef.conjTranspose_mul_self B hB).isUnit
  have hd : IsUnit (Bᴴ * B).det := (Matrix.isUnit_iff_isUnit_det _).1 hG
  set Gi := (Bᴴ * B)⁻¹ with hGi
  have hGG : (Bᴴ * B) * Gi = 1 := mul_nonsing_inv _ hd
  set u : k → ℂ := Gi *ᵥ (Bᴴ *ᵥ φ i) with hu
  set v : m → ℂ := φ i - B *ᵥ u with hv
  have hBv : Bᴴ *ᵥ v = 0 := by
    rw [hv, mulVec_sub, hu, mulVec_mulVec, mulVec_mulVec, hGG, one_mulVec,
      sub_self]
  -- the quadratic form of the decomposition on `v` vanishes
  have hq : star v ⬝ᵥ (∑ j, vecMulVec (φ j) (star (φ j))) *ᵥ v = 0 := by
    rw [h, ← mulVec_mulVec, ← mulVec_mulVec, hBv, mulVec_zero, mulVec_zero, dotProduct_zero]
  have hterm : ∀ j, star v ⬝ᵥ (vecMulVec (φ j) (star (φ j))) *ᵥ v =
      ((Complex.normSq (star (φ j) ⬝ᵥ v) : ℝ) : ℂ) := by
    intro j
    have e1 : vecMulVec (φ j) (star (φ j)) *ᵥ v = (star (φ j) ⬝ᵥ v) • φ j := by
      ext i; simp [vecMulVec_mulVec, mul_comm]
    rw [e1, dotProduct_smul, smul_eq_mul]
    have e2 : star v ⬝ᵥ φ j = star (star (φ j) ⬝ᵥ v) := by
      simp [dotProduct, mul_comm]
    rw [e2, mul_comm, Complex.normSq_eq_conj_mul_self]
    simp
  have hsum : ∑ j, ((Complex.normSq (star (φ j) ⬝ᵥ v) : ℝ) : ℂ) = 0 := by
    rw [← hq, Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun j _ => (hterm j).symm
  have hsumR : ∑ j, Complex.normSq (star (φ j) ⬝ᵥ v) = 0 := by exact_mod_cast hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hsumR i
    (Finset.mem_univ i)
  have hz' : star (φ i) ⬝ᵥ v = 0 := Complex.normSq_eq_zero.1 hz
  have e2 : star v ⬝ᵥ φ i = 0 := by
    have : star v ⬝ᵥ φ i = star (star (φ i) ⬝ᵥ v) := by simp [dotProduct, mul_comm]
    rw [this, hz', star_zero]
  have e4 : star v ⬝ᵥ (B *ᵥ u) = 0 := by
    rw [dotProduct_mulVec]
    have : star v ᵥ* B = star (Bᴴ *ᵥ v) := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [this, hBv]; simp
  have e3 : star v ⬝ᵥ v = 0 := by
    have hφ : φ i = v + B *ᵥ u := by rw [hv]; abel
    rw [hφ, dotProduct_add, e4, add_zero] at e2
    exact e2
  have hv0 : v = 0 := dotProduct_star_self_eq_zero.1 e3
  exact ⟨u, sub_eq_zero.1 (hv.symm.trans hv0)⟩

end Support

/-! ### The cone -/

/-- The quartic monomial vector `ν(a) = (a₀⁴, a₀³a₁, a₀²a₁², a₀a₁³, a₁⁴)`. -/
def nuVec (a : Fin 2 → ℂ) : Fin 5 → ℂ :=
  ![a 0 ^ 4, a 0 ^ 3 * a 1, a 0 ^ 2 * a 1 ^ 2, a 0 * a 1 ^ 3, a 1 ^ 4]

theorem nuVec_zero : nuVec (0 : Fin 2 → ℂ) = 0 := by
  ext i; fin_cases i <;> simp [nuVec]

/-- Product across the cut `c`, where `0, 1, 2` stand for `A|BC`, `B|AC`, `C|AB`. -/
def IsCutProdAt : Fin 3 → (Fin 8 → ℂ) → Prop
  | 0 => IsProdA
  | 1 => IsProdB
  | 2 => IsProdC

theorem isCutProduct_iff (x : Fin 8 → ℂ) : IsCutProduct x ↔ ∃ c, IsCutProdAt c x := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨c, h⟩
    fin_cases c
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem isCutProdAt_zero (c : Fin 3) : IsCutProdAt c (0 : Fin 8 → ℂ) := by
  fin_cases c
  · exact ⟨0, 0, fun i => by simp⟩
  · exact ⟨0, 0, fun i => by simp⟩
  · exact ⟨0, 0, fun i => by simp⟩

/-- **Hypothesis of `thm:ppt3-universal-moments`.**  For each cut `c`, the cut-`c` product vectors in
`range B` are exactly the multiples of `B T_c ν(a)`, `a ≠ 0`. -/
def CutCurve (B : Matrix (Fin 8) (Fin 5) ℂ) (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ) : Prop :=
  ∀ (c : Fin 3) (y : Fin 5 → ℂ), IsCutProdAt c (B *ᵥ y) ↔
    ∃ (a : Fin 2 → ℂ) (s : ℂ), a ≠ 0 ∧ B *ᵥ y = s • (B *ᵥ (T c *ᵥ nuVec a))

/-- Membership in `∑_c T_c 𝓜₄ T_cᴴ`: a finite sum of `w · T_c ν(a) ν(a)ᴴ T_cᴴ` with `w ≥ 0`. -/
def InMomentCone (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ) (X : Matrix (Fin 5) (Fin 5) ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → Fin 3) (a : Fin n → Fin 2 → ℂ) (w : Fin n → ℝ), (∀ i, 0 ≤ w i) ∧
    X = ∑ i, (w i : ℂ) • (T (c i) * vecMulVec (nuVec (a i)) (star (nuVec (a i))) * (T (c i))ᴴ)

theorem vecMulVec_mulVec_star {l n : Type*} [Fintype l] [Fintype n] (M : Matrix l n ℂ)
    (u : n → ℂ) : vecMulVec (M *ᵥ u) (star (M *ᵥ u)) = M * vecMulVec u (star u) * Mᴴ := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

theorem vecMulVec_smul_star {n : Type*} (s : ℂ) (u : n → ℂ) :
    vecMulVec (s • u) (star (s • u)) = (Complex.normSq s : ℂ) • vecMulVec u (star u) := by
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul',
    Matrix.smul_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem vecMulVec_curve (B : Matrix (Fin 8) (Fin 5) ℂ) (t : Matrix (Fin 5) (Fin 5) ℂ)
    (a : Fin 2 → ℂ) (s : ℂ) :
    vecMulVec (B *ᵥ (s • (t *ᵥ nuVec a))) (star (B *ᵥ (s • (t *ᵥ nuVec a)))) =
      B * ((Complex.normSq s : ℂ) • (t * vecMulVec (nuVec a) (star (nuVec a)) * tᴴ)) * Bᴴ := by
  rw [vecMulVec_mulVec_star, vecMulVec_smul_star, vecMulVec_mulVec_star, Matrix.mul_smul,
    Matrix.smul_mul]

section Cone

variable (B : Matrix (Fin 8) (Fin 5) ℂ) (T : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ)

/-- `eq:ppt3-universal-bs`: with `B` of full column rank and the cut curves `B T_c ν(a)`, the operator
`B X Bᴴ` is biseparable iff `X ∈ ∑_c T_c 𝓜₄ T_cᴴ`. -/
theorem biseparable_iff_mem_cone (hB : Function.Injective B.mulVec) (hT : CutCurve B T)
    (X : Matrix (Fin 5) (Fin 5) ℂ) : IsBiseparable (B * X * Bᴴ) ↔ InMomentCone T X := by
  obtain ⟨L, hL⟩ := exists_left_inverse B hB
  have hcancel : ∀ X Y : Matrix (Fin 5) (Fin 5) ℂ, B * X * Bᴴ = B * Y * Bᴴ → X = Y := by
    intro X Y h
    have := congrArg (fun Z => L * Z * Lᴴ) h
    simp only [← Matrix.mul_assoc, hL] at this
    have h2 : Bᴴ * Lᴴ = 1 := by rw [← conjTranspose_mul, hL, conjTranspose_one]
    simpa [Matrix.mul_assoc, h2] using this
  constructor
  · rintro ⟨n, φ, hφ, hsum⟩
    choose y hy using mem_range_of_sum_eq B hB φ X hsum.symm
    have hcut : ∀ i, ∃ (c : Fin 3) (a : Fin 2 → ℂ) (s : ℂ), a ≠ 0 ∧ y i = s • (T c *ᵥ nuVec a) := by
      intro i
      obtain ⟨c, hc⟩ := (isCutProduct_iff _).1 (hφ i)
      rw [hy i] at hc
      obtain ⟨a, s, ha, hs⟩ := (hT c (y i)).1 hc
      refine ⟨c, a, s, ha, hB ?_⟩
      rw [mulVec_smul]
      exact hs
    choose c a s ha hs using hcut
    refine ⟨n, c, a, fun i => Complex.normSq (s i), fun i => Complex.normSq_nonneg _, ?_⟩
    apply hcancel
    rw [hsum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy i, hs i, vecMulVec_curve, Matrix.mul_smul, Matrix.smul_mul]
  · rintro ⟨n, c, a, w, hw, hX⟩
    refine ⟨n, fun i => ((Real.sqrt (w i) : ℝ) : ℂ) • (B *ᵥ (T (c i) *ᵥ nuVec (a i))), ?_, ?_⟩
    · intro i
      rw [isCutProduct_iff]
      refine ⟨c i, ?_⟩
      show IsCutProdAt (c i) (((Real.sqrt (w i) : ℝ) : ℂ) • (B *ᵥ (T (c i) *ᵥ nuVec (a i))))
      by_cases ha : a i = 0
      · rw [ha, nuVec_zero, mulVec_zero, mulVec_zero, smul_zero]
        exact isCutProdAt_zero _
      · have := (hT (c i) (((Real.sqrt (w i) : ℝ) : ℂ) • (T (c i) *ᵥ nuVec (a i)))).2
          ⟨a i, ((Real.sqrt (w i) : ℝ) : ℂ), ha, by rw [mulVec_smul]⟩
        rwa [mulVec_smul] at this
    · rw [hX, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = vecMulVec (((Real.sqrt (w i) : ℝ) : ℂ) • (B *ᵥ (T (c i) *ᵥ nuVec (a i))))
        (star (((Real.sqrt (w i) : ℝ) : ℂ) • (B *ᵥ (T (c i) *ᵥ nuVec (a i)))))
      rw [← mulVec_smul, vecMulVec_curve, Complex.normSq_ofReal, Real.mul_self_sqrt (hw i),
        Matrix.mul_smul, Matrix.smul_mul]

theorem trace_mul_curve (H t : Matrix (Fin 5) (Fin 5) ℂ) (u : Fin 5 → ℂ) :
    trace (H * (t * vecMulVec u (star u) * tᴴ)) = star u ⬝ᵥ (tᴴ * H * t) *ᵥ u := by
  calc trace (H * (t * vecMulVec u (star u) * tᴴ))
      = trace ((H * (t * vecMulVec u (star u))) * tᴴ) := by rw [← Matrix.mul_assoc _ _ tᴴ]
    _ = trace (tᴴ * (H * (t * vecMulVec u (star u)))) := trace_mul_comm _ _
    _ = trace ((tᴴ * H * t) * vecMulVec u (star u)) := by simp only [Matrix.mul_assoc]
    _ = star u ⬝ᵥ (tᴴ * H * t) *ᵥ u := by
      rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- `eq:ppt3-universal-dual`: the dual cone.  `Re tr(H X) ≥ 0` for every biseparable `B X Bᴴ` iff the
three quartic forms `ν(a)ᴴ T_cᴴ H T_c ν(a)` are nonnegative (real part, so no Hermiticity assumption on
`H` is needed; for Hermitian `H` the forms are real). -/
theorem dual_iff (hB : Function.Injective B.mulVec) (hT : CutCurve B T)
    (H : Matrix (Fin 5) (Fin 5) ℂ) :
    (∀ X : Matrix (Fin 5) (Fin 5) ℂ, IsBiseparable (B * X * Bᴴ) → 0 ≤ (trace (H * X)).re) ↔
      ∀ (c : Fin 3) (a : Fin 2 → ℂ),
        0 ≤ (star (nuVec a) ⬝ᵥ ((T c)ᴴ * H * T c) *ᵥ nuVec a).re := by
  constructor
  · intro h c a
    have hmem : InMomentCone T (T c * vecMulVec (nuVec a) (star (nuVec a)) * (T c)ᴴ) :=
      ⟨1, fun _ => c, fun _ => a, fun _ => 1, fun _ => zero_le_one, by simp⟩
    have := h _ ((biseparable_iff_mem_cone B T hB hT _).2 hmem)
    rwa [trace_mul_curve] at this
  · intro h X hX
    obtain ⟨n, c, a, w, hw, rfl⟩ := (biseparable_iff_mem_cone B T hB hT X).1 hX
    rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, trace_mul_curve]
    exact mul_nonneg (hw i) (h _ _)

end Cone

end
end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.mem_range_of_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.mem_range_of_sum_eq

/-- info: 'FormalResearch.PPTThreeQubit.biseparable_iff_mem_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.biseparable_iff_mem_cone

/-- info: 'FormalResearch.PPTThreeQubit.dual_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.dual_iff

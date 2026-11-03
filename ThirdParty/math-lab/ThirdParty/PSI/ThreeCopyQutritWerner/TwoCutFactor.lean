module

public import ThreeCopyQutritWerner.TwoCutRotate
public import ThreeCopyQutritWerner.RankTwo

@[expose] public section


/-!
# Balanced factors of an operator of rank at most two

Appendix A: an operator `C` of rank at most two has balanced factors, `C = X Y†` with
`X†X = Y†Y`.  In vector form: `C = x₁ y₁† + x₂ y₂†` with `‖x₁‖ = ‖y₁‖`, `‖x₂‖ = ‖y₂‖`
and `⟨x₁, x₂⟩ = ⟨y₁, y₂⟩` (`exists_balanced_ketBra`).

Route: an orthonormal rank factorisation gives `C = e₁ f₁† + e₂ f₂†` with orthonormal
(or zero) `e`'s; a common unitary makes the `f`'s orthogonal and keeps the `e`'s
orthogonal (`exists_rotate_orthogonal`); a real rescaling `(s e, s⁻¹ f)` of each pair
balances the norms (`exists_balance_pair`, `exists_balanced_of_orthogonal`).
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

section Scalar

/-- Real scalings `s t = 1` with `s² A = t² B`, for positive `A`, `B`. -/
theorem exists_real_balance (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ s t : ℝ, s * t = 1 ∧ s * s * A = t * t * B := by
  have hw2 : Real.sqrt (Real.sqrt A) * Real.sqrt (Real.sqrt A) = Real.sqrt A :=
    Real.mul_self_sqrt (Real.sqrt_nonneg A)
  have hz2 : Real.sqrt (Real.sqrt B) * Real.sqrt (Real.sqrt B) = Real.sqrt B :=
    Real.mul_self_sqrt (Real.sqrt_nonneg B)
  have hA2 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hB2 : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB.le
  obtain ⟨w, hw, hw0⟩ : ∃ w : ℝ, w * w * (w * w) = A ∧ w ≠ 0 :=
    ⟨Real.sqrt (Real.sqrt A), hw2.symm ▸ hA2,
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hA)).ne'⟩
  obtain ⟨z, hz, hz0⟩ : ∃ z : ℝ, z * z * (z * z) = B ∧ z ≠ 0 :=
    ⟨Real.sqrt (Real.sqrt B), hz2.symm ▸ hB2,
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hB)).ne'⟩
  have hwi : w⁻¹ * w = 1 := inv_mul_cancel₀ hw0
  have hzi : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  refine ⟨z * w⁻¹, w * z⁻¹, ?_, ?_⟩
  · linear_combination (z⁻¹ * z) * hwi + hzi
  · linear_combination (-(z * z * (w⁻¹ * w⁻¹))) * hw + (w * w * (z⁻¹ * z⁻¹)) * hz
      + z * z * (w * w) * (w⁻¹ * w + 1) * hwi - z * z * (w * w) * (z⁻¹ * z + 1) * hzi

/-- Coefficients of a `2 × 2` unitary `[[α, -conj β], [β, conj α]]` that removes the
off-diagonal entry of the Hermitian matrix `[[a, g], [conj g, b]]`. -/
theorem exists_offdiag_coeffs (a b : ℝ) (g : ℂ) :
    ∃ α β : ℂ, α * conj α + β * conj β = 1 ∧
      conj α * conj β * ((b : ℂ) - (a : ℂ)) + conj α * conj α * g
        - conj β * conj β * conj g = 0 := by
  obtain ⟨u, hu, him⟩ := exists_unit_mul_real g
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u * g = (r : ℂ) :=
    ⟨(u * g).re, Complex.ext (Complex.ofReal_re _).symm
      (him.trans (Complex.ofReal_im _).symm)⟩
  have hr' : conj u * conj g = (r : ℂ) := by
    have h := congrArg (starRingEnd ℂ) hr
    rwa [map_mul, Complex.conj_ofReal] at h
  obtain ⟨C, S, hCS, hkey⟩ : ∃ C S : ℝ, C * C + S * S = 1 ∧
      C * S * (b - a) + (C * C - S * S) * r = 0 := by
    by_cases hr0 : r = 0
    · exact ⟨1, 0, by norm_num, by simp [hr0]⟩
    · obtain ⟨C, S, hCS, hκ⟩ := exists_real_rotation ((b - a) * r⁻¹ / 2)
      have hrr : r⁻¹ * r = 1 := inv_mul_cancel₀ hr0
      exact ⟨C, S, hCS, by linear_combination r * hκ - C * S * (b - a) * hrr⟩
  have hCS' : (C : ℂ) * C + (S : ℂ) * S = 1 := by exact_mod_cast hCS
  have hkey' : (C : ℂ) * S * ((b : ℂ) - (a : ℂ)) + ((C : ℂ) * C - (S : ℂ) * S) * (r : ℂ) = 0 := by
    exact_mod_cast hkey
  refine ⟨(C : ℂ), (S : ℂ) * u, ?_, ?_⟩
  · simp only [map_mul, Complex.conj_ofReal]
    linear_combination hCS' + (S : ℂ) * S * hu
  · simp only [map_mul, Complex.conj_ofReal]
    linear_combination (conj u) * hkey' - (C : ℂ) * C * g * hu + (C : ℂ) * C * conj u * hr
      - (S : ℂ) * S * conj u * hr'

end Scalar

section Vectors

variable {ι : Type*} [Fintype ι]

theorem vecNormSq_nonneg (u : ι → ℂ) : 0 ≤ vecNormSq u :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)

theorem eq_zero_of_vecNormSq_eq_zero (u : ι → ℂ) (h : vecNormSq u = 0) (i : ι) : u i = 0 := by
  have h' : ∑ j, Complex.normSq (u j) = 0 := h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (u j))).mp h' i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp h0

/-- `‖c u‖² = c² ‖u‖²` for real `c`. -/
theorem vecNormSq_real_smul (c : ℝ) (u : ι → ℂ) :
    vecNormSq (fun i => (c : ℂ) * u i) = c * c * vecNormSq u := by
  unfold vecNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]

/-- `⟨c u, d v⟩ = c d ⟨u, v⟩` for real `c`, `d`. -/
theorem braket_real_smul (c d : ℝ) (u v : ι → ℂ) :
    braket (fun i => (c : ℂ) * u i) (fun i => (d : ℂ) * v i) = (c : ℂ) * d * braket u v := by
  unfold braket
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- A real rescaling of a pair `(e, f)` keeps `e f†` and balances the norms. -/
theorem exists_balance_pair (e f : ι → ℂ) :
    ∃ s t : ℝ, ketBra (fun i => (s : ℂ) * e i) (fun i => (t : ℂ) * f i) = ketBra e f ∧
      vecNormSq (fun i => (s : ℂ) * e i) = vecNormSq (fun i => (t : ℂ) * f i) := by
  by_cases hA : vecNormSq e = 0
  · refine ⟨0, 0, ?_, ?_⟩
    · ext i j
      have he := eq_zero_of_vecNormSq_eq_zero e hA i
      simp [ketBra, he]
    · exact (vecNormSq_real_smul 0 e).trans
        ((by ring : (0 : ℝ) * 0 * vecNormSq e = 0 * 0 * vecNormSq f).trans
          (vecNormSq_real_smul 0 f).symm)
  · by_cases hB : vecNormSq f = 0
    · refine ⟨0, 0, ?_, ?_⟩
      · ext i j
        have hf := eq_zero_of_vecNormSq_eq_zero f hB j
        simp [ketBra, hf]
      · exact (vecNormSq_real_smul 0 e).trans
          ((by ring : (0 : ℝ) * 0 * vecNormSq e = 0 * 0 * vecNormSq f).trans
            (vecNormSq_real_smul 0 f).symm)
    · have hA0 : 0 < vecNormSq e := lt_of_le_of_ne (vecNormSq_nonneg e) (Ne.symm hA)
      have hB0 : 0 < vecNormSq f := lt_of_le_of_ne (vecNormSq_nonneg f) (Ne.symm hB)
      obtain ⟨s, t, hst, hbal⟩ := exists_real_balance (vecNormSq e) (vecNormSq f) hA0 hB0
      have hst' : (s : ℂ) * (t : ℂ) = 1 := by exact_mod_cast hst
      refine ⟨s, t, ?_, ?_⟩
      · ext i j
        simp only [ketBra, map_mul, Complex.conj_ofReal]
        linear_combination (e i * conj (f j)) * hst'
      · exact (vecNormSq_real_smul s e).trans (hbal.trans (vecNormSq_real_smul t f).symm)

/-- Orthogonal pairs can be rescaled to balanced factors. -/
theorem exists_balanced_of_orthogonal (e₁ e₂ f₁ f₂ : ι → ℂ) (he : braket e₁ e₂ = 0)
    (hf : braket f₁ f₂ = 0) :
    ∃ x₁ x₂ y₁ y₂ : ι → ℂ, ketBra e₁ f₁ + ketBra e₂ f₂ = ketBra x₁ y₁ + ketBra x₂ y₂ ∧
      vecNormSq x₁ = vecNormSq y₁ ∧ vecNormSq x₂ = vecNormSq y₂ ∧
      braket x₁ x₂ = braket y₁ y₂ := by
  obtain ⟨s₁, t₁, hk₁, hn₁⟩ := exists_balance_pair e₁ f₁
  obtain ⟨s₂, t₂, hk₂, hn₂⟩ := exists_balance_pair e₂ f₂
  refine ⟨fun i => (s₁ : ℂ) * e₁ i, fun i => (s₂ : ℂ) * e₂ i, fun i => (t₁ : ℂ) * f₁ i,
    fun i => (t₂ : ℂ) * f₂ i, ?_, hn₁, hn₂, ?_⟩
  · exact (congrArg₂ (fun P Q : Matrix ι ι ℂ => P + Q) hk₁ hk₂).symm
  · exact (braket_real_smul s₁ s₂ e₁ e₂).trans
      ((by rw [he, hf, mul_zero, mul_zero] :
          (s₁ : ℂ) * s₂ * braket e₁ e₂ = (t₁ : ℂ) * t₂ * braket f₁ f₂).trans
        (braket_real_smul t₁ t₂ f₁ f₂).symm)

/-- A common unitary makes the `f`'s orthogonal and keeps orthogonal `e`'s of equal norm
orthogonal, without changing `e₁ f₁† + e₂ f₂†`. -/
theorem exists_rotate_orthogonal (e₁ e₂ f₁ f₂ : ι → ℂ) (he : braket e₁ e₂ = 0)
    (hn : vecNormSq e₁ = vecNormSq e₂) :
    ∃ e₁' e₂' f₁' f₂' : ι → ℂ,
      ketBra e₁' f₁' + ketBra e₂' f₂' = ketBra e₁ f₁ + ketBra e₂ f₂ ∧
      braket e₁' e₂' = 0 ∧ braket f₁' f₂' = 0 := by
  have he' : braket e₂ e₁ = 0 := by
    have h := conj_braket e₁ e₂
    rw [he, map_zero] at h
    exact h.symm
  have h11 : braket e₁ e₁ = braket e₂ e₂ := by rw [braket_self, braket_self, hn]
  obtain ⟨α, β, hαβ, hzero⟩ :=
    exists_offdiag_coeffs (vecNormSq f₁) (vecNormSq f₂) (braket f₁ f₂)
  refine ⟨fun i => α * e₁ i + β * e₂ i, fun i => -conj β * e₁ i + conj α * e₂ i,
    fun i => α * f₁ i + β * f₂ i, fun i => -conj β * f₁ i + conj α * f₂ i,
    ketBra_rotate e₁ e₂ f₁ f₂ α β hαβ, ?_, ?_⟩
  · rw [braket_comb, he, he', h11]
    ring
  · rw [braket_comb, braket_self f₁, braket_self f₂, ← conj_braket f₁ f₂]
    linear_combination hzero

/-- Factorisation through `Fin 0`: the zero operator. -/
theorem exists_orthogonal_ketBra_fin_zero (U : Matrix ι (Fin 0) ℂ) (B : Matrix (Fin 0) ι ℂ) :
    ∃ e₁ e₂ f₁ f₂ : ι → ℂ, U * B = ketBra e₁ f₁ + ketBra e₂ f₂ ∧
      braket e₁ e₂ = 0 ∧ braket f₁ f₂ = 0 := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, ketBra]
  · simp [braket]
  · simp [braket]

/-- Factorisation through `Fin 1`: one rank-one term. -/
theorem exists_orthogonal_ketBra_fin_one (U : Matrix ι (Fin 1) ℂ) (B : Matrix (Fin 1) ι ℂ) :
    ∃ e₁ e₂ f₁ f₂ : ι → ℂ, U * B = ketBra e₁ f₁ + ketBra e₂ f₂ ∧
      braket e₁ e₂ = 0 ∧ braket f₁ f₂ = 0 := by
  refine ⟨fun i => U i 0, fun _ => 0, fun j => conj (B 0 j), fun _ => 0, ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, ketBra]
  · simp [braket]
  · simp [braket]

/-- Factorisation through `Fin 2` with orthonormal columns: rotate to orthogonal `f`'s. -/
theorem exists_orthogonal_ketBra_fin_two (U : Matrix ι (Fin 2) ℂ) (B : Matrix (Fin 2) ι ℂ)
    (hU : U.conjTranspose * U = 1) :
    ∃ e₁ e₂ f₁ f₂ : ι → ℂ, U * B = ketBra e₁ f₁ + ketBra e₂ f₂ ∧
      braket e₁ e₂ = 0 ∧ braket f₁ f₂ = 0 := by
  have hcol : ∀ k l : Fin 2, braket (fun i => U i k) (fun i => U i l) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) k l := by
    intro k l
    have h := congrFun (congrFun hU k) l
    rw [Matrix.mul_apply] at h
    refine Eq.trans ?_ h
    unfold braket
    exact Finset.sum_congr rfl fun i _ => rfl
  have h01 : braket (fun i => U i 0) (fun i => U i 1) = 0 :=
    (hcol 0 1).trans (Matrix.one_apply_ne (by decide))
  have h00 : braket (fun i => U i 0) (fun i => U i 0) = 1 :=
    (hcol 0 0).trans (Matrix.one_apply_eq 0)
  have h11 : braket (fun i => U i 1) (fun i => U i 1) = 1 :=
    (hcol 1 1).trans (Matrix.one_apply_eq 1)
  have hn : vecNormSq (fun i => U i 0) = vecNormSq (fun i => U i 1) := by
    apply Complex.ofReal_injective
    rw [← braket_self, ← braket_self, h00, h11]
  have hdecomp : U * B = ketBra (fun i => U i 0) (fun j => conj (B 0 j)) +
      ketBra (fun i => U i 1) (fun j => conj (B 1 j)) := by
    ext i j
    simp [Matrix.mul_apply, ketBra, Fin.sum_univ_two]
  obtain ⟨e₁, e₂, f₁, f₂, hk, he, hf⟩ := exists_rotate_orthogonal (fun i => U i 0)
    (fun i => U i 1) (fun j => conj (B 0 j)) (fun j => conj (B 1 j)) h01 hn
  exact ⟨e₁, e₂, f₁, f₂, hdecomp.trans hk.symm, he, hf⟩

/-- An orthonormal factorisation through at most two columns gives two rank-one terms
with orthogonal `e`'s and orthogonal `f`'s. -/
theorem exists_orthogonal_ketBra_of_mul :
    ∀ (d : ℕ) (U : Matrix ι (Fin d) ℂ) (B : Matrix (Fin d) ι ℂ), d ≤ 2 →
      U.conjTranspose * U = 1 →
      ∃ e₁ e₂ f₁ f₂ : ι → ℂ, U * B = ketBra e₁ f₁ + ketBra e₂ f₂ ∧
        braket e₁ e₂ = 0 ∧ braket f₁ f₂ = 0
  | 0, U, B, _, _ => exists_orthogonal_ketBra_fin_zero U B
  | 1, U, B, _, _ => exists_orthogonal_ketBra_fin_one U B
  | 2, U, B, _, hU => exists_orthogonal_ketBra_fin_two U B hU
  | (n + 3), _, _, h, _ => absurd h (by omega)

end Vectors

/-- Appendix A: an operator of rank at most two has balanced factors
`X = x₁ y₁† + x₂ y₂†` with `‖x₁‖ = ‖y₁‖`, `‖x₂‖ = ‖y₂‖`, `⟨x₁, x₂⟩ = ⟨y₁, y₂⟩`. -/
theorem exists_balanced_ketBra {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ)
    (h : X.rank ≤ 2) :
    ∃ x₁ x₂ y₁ y₂ : ι → ℂ, X = ketBra x₁ y₁ + ketBra x₂ y₂ ∧
      vecNormSq x₁ = vecNormSq y₁ ∧ vecNormSq x₂ = vecNormSq y₂ ∧
      braket x₁ x₂ = braket y₁ y₂ := by
  obtain ⟨d, U, B, hd, hU, hX⟩ := exists_orthonormal_mul X
  obtain ⟨e₁, e₂, f₁, f₂, hk, he, hf⟩ :=
    exists_orthogonal_ketBra_of_mul d U B (hd.trans_le h) hU
  obtain ⟨x₁, x₂, y₁, y₂, hk', h1, h2, h3⟩ := exists_balanced_of_orthogonal e₁ e₂ f₁ f₂ he hf
  exact ⟨x₁, x₂, y₁, y₂, hX.trans (hk.trans hk'), h1, h2, h3⟩

end ThreeCopyQutritWerner

end

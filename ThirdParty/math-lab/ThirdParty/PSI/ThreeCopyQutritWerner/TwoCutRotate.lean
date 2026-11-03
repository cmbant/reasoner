module

public import ThreeCopyQutritWerner.TwoCutSOS

@[expose] public section


/-!
# The common logical unitary of Appendix A

Appendix A: a common logical unitary makes the two pairings `y₁† x₁` and `y₂† x₂` equal and
changes neither `C` nor the balance.  For factors `x₁, x₂, y₁, y₂` with equal Gram matrices, the
unitary `W = [[α, -conj β], [β, conj α]]`, `|α|² + |β|² = 1`, applied to both pairs
keeps `x₁ y₁† + x₂ y₂†` and the equality of Gram matrices, and changes
`⟨y₁, x₁⟩ - ⟨y₂, x₂⟩` into
`(|α|² - |β|²)(⟨y₁,x₁⟩ - ⟨y₂,x₂⟩) + 2 conj(α) β ⟨y₁,x₂⟩ + 2 α conj(β) ⟨y₂,x₁⟩`.
`exists_unitary_coeffs` shows that this vanishes for suitable `α`, `β`: a phase `u`
makes the mixed term a real multiple of the first, and a real rotation finishes.
-/

noncomputable section

open scoped ComplexConjugate

namespace ThreeCopyQutritWerner

section Scalar

/-- A unit complex number `u` with `u z` real. -/
theorem exists_unit_mul_real (z : ℂ) : ∃ u : ℂ, u * conj u = 1 ∧ (u * z).im = 0 := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hNne : ((Complex.normSq z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
    have hrr : ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ) * ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ)
        = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hn.le]
    have hzz : conj z * z = ((Complex.normSq z : ℝ) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    refine ⟨conj z * ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ)⁻¹, ?_, ?_⟩
    · rw [map_mul, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
      calc conj z * ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ)⁻¹ *
              (z * ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ)⁻¹)
          = conj z * z * (((Real.sqrt (Complex.normSq z) : ℝ) : ℂ) *
              ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ))⁻¹ := by
            rw [mul_inv]
            ring
        _ = 1 := by rw [hzz, hrr, mul_inv_cancel₀ hNne]
    · have h : conj z * ((Real.sqrt (Complex.normSq z) : ℝ) : ℂ)⁻¹ * z =
          ((Complex.normSq z * (Real.sqrt (Complex.normSq z))⁻¹ : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_inv, ← hzz]
        ring
      rw [h]
      exact Complex.ofReal_im _

/-- A real rotation `(C, S)` with `cos 2θ + κ sin 2θ = 0`. -/
theorem exists_real_rotation (κ : ℝ) :
    ∃ C S : ℝ, C * C + S * S = 1 ∧ C * C - S * S + 2 * C * S * κ = 0 := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = κ ^ 2 + 1 :=
    ⟨Real.sqrt (κ ^ 2 + 1), Real.mul_self_sqrt (by positivity)⟩
  have ht : (κ + s) ^ 2 - 2 * κ * (κ + s) - 1 = 0 := by linear_combination hs
  obtain ⟨q, hq, hqne⟩ : ∃ q : ℝ, q * q = 1 + (κ + s) ^ 2 ∧ q ≠ 0 :=
    ⟨Real.sqrt (1 + (κ + s) ^ 2), Real.mul_self_sqrt (by positivity),
      (Real.sqrt_pos.mpr (by positivity)).ne'⟩
  have hqq : q⁻¹ * q⁻¹ * (q * q) = 1 := by
    calc q⁻¹ * q⁻¹ * (q * q) = (q⁻¹ * q) * (q⁻¹ * q) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hqne, mul_one]
  refine ⟨q⁻¹, (κ + s) * q⁻¹, ?_, ?_⟩
  · calc q⁻¹ * q⁻¹ + (κ + s) * q⁻¹ * ((κ + s) * q⁻¹)
        = q⁻¹ * q⁻¹ * (1 + (κ + s) ^ 2) := by ring
      _ = q⁻¹ * q⁻¹ * (q * q) := by rw [hq]
      _ = 1 := hqq
  · linear_combination (-(q⁻¹ * q⁻¹)) * ht

/-- A phase `u` making `conj a * (u b + conj u c)` real. -/
theorem exists_phase (a b c : ℂ) :
    ∃ u : ℂ, u * conj u = 1 ∧ (conj a * (u * b + conj u * c)).im = 0 := by
  obtain ⟨u, hu, hre⟩ := exists_unit_mul_real (conj a * b - a * conj c)
  refine ⟨u, hu, ?_⟩
  have h : conj a * (u * b + conj u * c) =
      u * (conj a * b - a * conj c) + (u * a * conj c + conj (u * a * conj c)) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  have hw : (u * a * conj c + conj (u * a * conj c)).im = 0 := by
    rw [Complex.add_conj]
    exact Complex.ofReal_im _
  rw [h, Complex.add_im, hw, hre, add_zero]

/-- If `conj a * w` is real, a real rotation kills `(C² - S²) a + 2 C S w`. -/
theorem exists_rotation (a w : ℂ) (h : (conj a * w).im = 0) :
    ∃ C S : ℝ, C * C + S * S = 1 ∧
      ((C * C - S * S : ℝ) : ℂ) * a + ((2 * C * S : ℝ) : ℂ) * w = 0 := by
  by_cases ha : a = 0
  · refine ⟨1, 0, by norm_num, ?_⟩
    rw [ha]
    simp
  · have hn : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    have hNne : ((Complex.normSq a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, conj a * w = (ρ : ℂ) :=
      ⟨(conj a * w).re, Complex.ext (Complex.ofReal_re _).symm
        (h.trans (Complex.ofReal_im _).symm)⟩
    have h1 : ((Complex.normSq a : ℝ) : ℂ) * w = (ρ : ℂ) * a := by
      rw [← Complex.mul_conj, mul_assoc, hρ]
      exact mul_comm _ _
    have hw : w = ((ρ / Complex.normSq a : ℝ) : ℂ) * a := by
      calc w = ((Complex.normSq a : ℝ) : ℂ)⁻¹ * (((Complex.normSq a : ℝ) : ℂ) * w) := by
            rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
        _ = ((Complex.normSq a : ℝ) : ℂ)⁻¹ * ((ρ : ℂ) * a) := by rw [h1]
        _ = ((ρ / Complex.normSq a : ℝ) : ℂ) * a := by
            rw [Complex.ofReal_div]
            ring
    obtain ⟨C, S, hCS, hκ⟩ := exists_real_rotation (ρ / Complex.normSq a)
    refine ⟨C, S, hCS, ?_⟩
    have e : ((C * C - S * S : ℝ) : ℂ) * a +
        ((2 * C * S : ℝ) : ℂ) * (((ρ / Complex.normSq a : ℝ) : ℂ) * a) =
        ((C * C - S * S + 2 * C * S * (ρ / Complex.normSq a) : ℝ) : ℂ) * a := by
      push_cast
      ring
    rw [hw, e, hκ, Complex.ofReal_zero, zero_mul]

/-- Coefficients of a `2 × 2` unitary equalizing the diagonal: `a` is the difference of
the diagonal entries and `b`, `c` the off-diagonal entries. -/
theorem exists_unitary_coeffs (a b c : ℂ) :
    ∃ α β : ℂ, α * conj α + β * conj β = 1 ∧
      (α * conj α - β * conj β) * a + 2 * (conj α * β * b + α * conj β * c) = 0 := by
  obtain ⟨u, hu, him⟩ := exists_phase a b c
  obtain ⟨C, S, hCS, hrot⟩ := exists_rotation a (u * b + conj u * c) him
  have hCS' : (C : ℂ) * C + (S : ℂ) * S = 1 := by exact_mod_cast hCS
  have hrot' : ((C : ℂ) * C - (S : ℂ) * S) * a + 2 * (C : ℂ) * S * (u * b + conj u * c) = 0 := by
    have h := hrot
    push_cast at h
    linear_combination h
  refine ⟨(C : ℂ), (S : ℂ) * u, ?_, ?_⟩
  · simp only [map_mul, Complex.conj_ofReal]
    linear_combination hCS' + (S : ℂ) * S * hu
  · simp only [map_mul, Complex.conj_ofReal]
    linear_combination hrot' - (S : ℂ) * S * a * hu

end Scalar

section Vectors

variable {ι : Type*} [Fintype ι]

/-- `⟨u, u⟩ = ‖u‖²`. -/
theorem braket_self (u : ι → ℂ) : braket u u = ((vecNormSq u : ℝ) : ℂ) :=
  (ofReal_vecNormSq u).symm

/-- Sesquilinear expansion of `⟨p a + q b, r c + s d⟩`. -/
theorem braket_comb (p q r s : ℂ) (a b c d : ι → ℂ) :
    braket (fun i => p * a i + q * b i) (fun i => r * c i + s * d i) =
      conj p * r * braket a c + conj p * s * braket a d + conj q * r * braket b c
        + conj q * s * braket b d := by
  unfold braket
  calc ∑ i, conj (p * a i + q * b i) * (r * c i + s * d i)
      = ∑ i, (conj p * r * (conj (a i) * c i) + conj p * s * (conj (a i) * d i)
          + conj q * r * (conj (b i) * c i) + conj q * s * (conj (b i) * d i)) :=
        Finset.sum_congr rfl fun i _ => by
          simp only [map_add, map_mul]
          ring
    _ = conj p * r * (∑ i, conj (a i) * c i) + conj p * s * (∑ i, conj (a i) * d i)
          + conj q * r * (∑ i, conj (b i) * c i) + conj q * s * (∑ i, conj (b i) * d i) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Equal Gram matrices give equal inner products of equal linear combinations. -/
theorem braket_comb_congr (x₁ x₂ y₁ y₂ : ι → ℂ)
    (h11 : braket x₁ x₁ = braket y₁ y₁) (h22 : braket x₂ x₂ = braket y₂ y₂)
    (h12 : braket x₁ x₂ = braket y₁ y₂) (h21 : braket x₂ x₁ = braket y₂ y₁) (p q r s : ℂ) :
    braket (fun i => p * x₁ i + q * x₂ i) (fun i => r * x₁ i + s * x₂ i) =
      braket (fun i => p * y₁ i + q * y₂ i) (fun i => r * y₁ i + s * y₂ i) := by
  rw [braket_comb, braket_comb, h11, h22, h12, h21]

omit [Fintype ι] in
/-- A common unitary on both factor pairs does not change `x₁ y₁† + x₂ y₂†`. -/
theorem ketBra_rotate (x₁ x₂ y₁ y₂ : ι → ℂ) (α β : ℂ) (h : α * conj α + β * conj β = 1) :
    ketBra (fun i => α * x₁ i + β * x₂ i) (fun i => α * y₁ i + β * y₂ i) +
        ketBra (fun i => -conj β * x₁ i + conj α * x₂ i)
          (fun i => -conj β * y₁ i + conj α * y₂ i) =
      ketBra x₁ y₁ + ketBra x₂ y₂ := by
  ext i j
  simp only [Matrix.add_apply, ketBra, map_add, map_mul, map_neg, Complex.conj_conj]
  linear_combination (x₁ i * conj (y₁ j) + x₂ i * conj (y₂ j)) * h

/-- Appendix A: balanced factors can be rotated by a common unitary so that
`⟨y₁, x₁⟩ = ⟨y₂, x₂⟩`, without changing `x₁ y₁† + x₂ y₂†` or balance. -/
theorem exists_equal_diagonal (x₁ x₂ y₁ y₂ : ι → ℂ)
    (h1 : vecNormSq x₁ = vecNormSq y₁) (h2 : vecNormSq x₂ = vecNormSq y₂)
    (hg : braket x₁ x₂ = braket y₁ y₂) :
    ∃ x₁' x₂' y₁' y₂' : ι → ℂ,
      ketBra x₁' y₁' + ketBra x₂' y₂' = ketBra x₁ y₁ + ketBra x₂ y₂ ∧
      vecNormSq x₁' = vecNormSq y₁' ∧ vecNormSq x₂' = vecNormSq y₂' ∧
      braket x₁' x₂' = braket y₁' y₂' ∧ braket y₁' x₁' = braket y₂' x₂' := by
  have h11 : braket x₁ x₁ = braket y₁ y₁ := by rw [braket_self, braket_self, h1]
  have h22 : braket x₂ x₂ = braket y₂ y₂ := by rw [braket_self, braket_self, h2]
  have h21 : braket x₂ x₁ = braket y₂ y₁ := by
    rw [← conj_braket x₁ x₂, ← conj_braket y₁ y₂, hg]
  obtain ⟨α, β, hαβ, hzero⟩ :=
    exists_unitary_coeffs (braket y₁ x₁ - braket y₂ x₂) (braket y₁ x₂) (braket y₂ x₁)
  refine ⟨fun i => α * x₁ i + β * x₂ i, fun i => -conj β * x₁ i + conj α * x₂ i,
    fun i => α * y₁ i + β * y₂ i, fun i => -conj β * y₁ i + conj α * y₂ i,
    ketBra_rotate x₁ x₂ y₁ y₂ α β hαβ, ?_, ?_, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [← braket_self, ← braket_self]
    exact braket_comb_congr x₁ x₂ y₁ y₂ h11 h22 hg h21 α β α β
  · apply Complex.ofReal_injective
    rw [← braket_self, ← braket_self]
    exact braket_comb_congr x₁ x₂ y₁ y₂ h11 h22 hg h21 (-conj β) (conj α) (-conj β) (conj α)
  · exact braket_comb_congr x₁ x₂ y₁ y₂ h11 h22 hg h21 α β (-conj β) (conj α)
  · rw [braket_comb, braket_comb]
    simp only [map_neg, Complex.conj_conj]
    linear_combination hzero

end Vectors

end ThreeCopyQutritWerner

end

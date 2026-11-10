module

public import FormalResearch.PPTThreeQubit.ChiralityBasics

/-!
# The fully product rays of `R_s` (`cor:ppt3-chirality` (b), first half)

Source: `appendix_family.tex`, proof of `cor:ppt3-chirality` (b).

`R_s` contains exactly three fully product rays: `P_∞ = [|1⟩^{⊗3}]` and
`P_± = [(|0⟩ ± i √s |1⟩)^{⊗3}]`.  `fullProd_mem_Rs` is the classification (every nonzero fully
product vector of `R_s` lies on one of the three rays, with the explicit determinant formula
`det_phiS : det φ_s(z) = -3 (z² + s)²`); `tri_mem_Rs_of_ptS` is the converse; the same statements
for the conjugate range `conj(R_s)` are `fullProd_mem_Rsbar`.  `tri_eq_smul_tri` extracts the single
qubit factors of a product vector lying on a ray.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- The three points of `ℂP¹` (as vectors) underlying the three fully product rays of `R_s`:
`|1⟩` and `|0⟩ ± i √s |1⟩`. -/
def PtS (s : ℝ) (χ : Fin 2 → ℂ) : Prop :=
  χ = ![0, 1] ∨ χ = ![1, Complex.I * (Real.sqrt s : ℂ)] ∨ χ = ![1, -(Complex.I * (Real.sqrt s : ℂ))]

theorem sqrt_sq_cast {s : ℝ} (hs : 0 < s) : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]

theorem I_mul_sqrt_sq {s : ℝ} (hs : 0 < s) : (Complex.I * (Real.sqrt s : ℂ)) ^ 2 = -(s : ℂ) := by
  rw [mul_pow, sqrt_sq_cast hs, Complex.I_sq]; ring

theorem phiS_of_sq {s : ℝ} {z : ℂ} (h : z ^ 2 = -(s : ℂ)) (b c : Fin 2) :
    phiS s z b c = 2 * z * chi z b * chi z c := by
  have hs' : (s : ℂ) = -z ^ 2 := by rw [h]; ring
  fin_cases b <;> fin_cases c <;> simp [phiS, chi, hs'] <;> ring

theorem Bs_qs_of_sq {s : ℝ} {z : ℂ} (h : z ^ 2 = -(s : ℂ)) :
    Bs s *ᵥ qs s z = (2 * z) • tri (chi z) (chi z) (chi z) := by
  rw [Bs_qs_eq]
  ext i
  simp only [phiS_of_sq h, tri_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bs_single_v (s : ℝ) : Bs s *ᵥ (Pi.single 1 1 : Fin 5 → ℂ) = tri ![0, 1] ![0, 1] ![0, 1] := by
  rw [Bs_mulVec]
  ext i
  fin_cases i <;> simp [tri_apply, bitA, bitB, bitC]

/-- The three product vectors lie in `R_s`. -/
theorem tri_mem_Rs_of_ptS {s : ℝ} (hs : 0 < s) {χ : Fin 2 → ℂ} (h : PtS s χ) :
    tri χ χ χ ∈ Rs s := by
  rcases h with rfl | rfl | rfl
  · exact ⟨Pi.single 1 1, Bs_single_v s⟩
  · have hz := I_mul_sqrt_sq hs
    have hz0 : (2 * (Complex.I * (Real.sqrt s : ℂ))) ≠ 0 := by
      have : Complex.I * (Real.sqrt s : ℂ) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hs).ne')
      simpa using this
    refine ⟨(2 * (Complex.I * (Real.sqrt s : ℂ)))⁻¹ • qs s (Complex.I * (Real.sqrt s : ℂ)), ?_⟩
    rw [mulVec_smul, Bs_qs_of_sq hz, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rfl
  · have hz : (-(Complex.I * (Real.sqrt s : ℂ))) ^ 2 = -(s : ℂ) := by
      rw [neg_sq]; exact I_mul_sqrt_sq hs
    have hz0 : (2 * (-(Complex.I * (Real.sqrt s : ℂ)))) ≠ 0 := by
      have : Complex.I * (Real.sqrt s : ℂ) ≠ 0 :=
        mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hs).ne')
      simpa using this
    refine ⟨(2 * (-(Complex.I * (Real.sqrt s : ℂ))))⁻¹ • qs s (-(Complex.I * (Real.sqrt s : ℂ))),
      ?_⟩
    rw [mulVec_smul, Bs_qs_of_sq hz, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rfl

/-- **Classification of fully product vectors in `R_s`** (`cor:ppt3-chirality` (b)): every nonzero
fully product vector of `R_s` is a multiple of `|1⟩^{⊗3}` or of `(|0⟩ ± i√s |1⟩)^{⊗3}`. -/
theorem fullProd_mem_Rs {s : ℝ} (hs : 0 < s) {x : Fin 8 → ℂ} (hx : x ∈ Rs s)
    (hp : IsFullProd x) (h0 : x ≠ 0) :
    ∃ l : ℂ, l ≠ 0 ∧ ∃ χ, PtS s χ ∧ x = l • tri χ χ χ := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨a, b, c', hxe⟩ := hp
  have hA : IsProdA (Bs s *ᵥ c) := by
    refine ⟨a, fun j => b ⟨j.val / 2, by omega⟩ * c' ⟨j.val % 2, by omega⟩, fun i => ?_⟩
    rw [hxe]
    fin_cases i <;> simp [tri_apply, bitA, bitB, bitC] <;> ring
  have hdet : (Bs s *ᵥ c) 0 * (Bs s *ᵥ c) 3 = (Bs s *ᵥ c) 1 * (Bs s *ᵥ c) 2 := by
    rw [hxe]
    simp [tri_apply, bitA, bitB, bitC]
    ring
  rcases prodA_classification hs c hA with ⟨z, l, hc⟩ | ⟨l, hc⟩
  · subst hc
    rw [mulVec_smul] at hdet h0 ⊢
    have hl : l ≠ 0 := by
      rintro rfl; apply h0; simp
    have e : ∀ i : Fin 8, (l • (Bs s *ᵥ qs s z)) i =
        l * (chi z (bitA i) * phiS s z (bitB i) (bitC i)) := fun i => by
      rw [Bs_qs_eq]; rfl
    rw [e 0, e 1, e 2, e 3] at hdet
    have key : l ^ 2 * (phiS s z).det = 0 := by
      rw [det_fin_two]
      simp [chi, bitA, bitB, bitC] at hdet
      linear_combination hdet
    rw [det_phiS] at key
    have hz2 : z ^ 2 = -(s : ℂ) := by
      have h1 : l ^ 2 * (-3) ≠ 0 := by
        have : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
        exact mul_ne_zero this (by norm_num)
      have h3 : (z ^ 2 + s) ^ 2 = 0 := by
        have : (l ^ 2 * (-3)) * (z ^ 2 + s) ^ 2 = 0 := by linear_combination key
        exact (mul_eq_zero.mp this).resolve_left h1
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h3
      linear_combination this
    have hz0 : z ≠ 0 := by
      rintro rfl
      have : (s : ℂ) = 0 := by simpa using hz2
      exact hs.ne' (by exact_mod_cast this)
    refine ⟨l * (2 * z), mul_ne_zero hl (mul_ne_zero two_ne_zero hz0), chi z, ?_, ?_⟩
    · have hfac : (z - Complex.I * (Real.sqrt s : ℂ)) * (z + Complex.I * (Real.sqrt s : ℂ)) = 0 := by
        have := I_mul_sqrt_sq hs
        linear_combination hz2 - this
      rcases mul_eq_zero.mp hfac with h | h
      · right; left
        have : z = Complex.I * (Real.sqrt s : ℂ) := by linear_combination h
        rw [this]; rfl
      · right; right
        have : z = -(Complex.I * (Real.sqrt s : ℂ)) := by linear_combination h
        rw [this]; rfl
    · rw [Bs_qs_of_sq hz2, smul_smul]
  · subst hc
    refine ⟨l, ?_, ![0, 1], Or.inl rfl, ?_⟩
    · rintro rfl; apply h0; simp
    · rw [mulVec_smul, Bs_single_v]

theorem star_chi_ptS {s : ℝ} {χ : Fin 2 → ℂ} (h : PtS s χ) : PtS s (star χ) := by
  have h1 : star (![0, 1] : Fin 2 → ℂ) = ![0, 1] := by
    ext j; fin_cases j <;> simp
  have h2 : ∀ z : ℂ, star (![1, z] : Fin 2 → ℂ) = ![1, star z] := by
    intro z; ext j; fin_cases j <;> simp
  rcases h with rfl | rfl | rfl
  · left; exact h1
  · right; right; rw [h2]; simp
  · right; left; rw [h2]; simp

/-- The same classification for the complex conjugate `conj(R_s)`. -/
theorem fullProd_mem_Rsbar {s : ℝ} (hs : 0 < s) {y : Fin 8 → ℂ} (hy : y ∈ Rsbar s)
    (hp : IsFullProd y) (h0 : y ≠ 0) :
    ∃ l : ℂ, l ≠ 0 ∧ ∃ χ, PtS s χ ∧ y = l • tri χ χ χ := by
  obtain ⟨a, b, c, rfl⟩ := hp
  have hp' : IsFullProd (star (tri a b c)) := ⟨star a, star b, star c, star_tri a b c⟩
  have h0' : star (tri a b c) ≠ 0 := fun h => h0 (by simpa using congrArg star h)
  obtain ⟨l, hl, χ, hχ, hx⟩ := fullProd_mem_Rs hs hy hp' h0'
  refine ⟨star l, by simpa using hl, star χ, star_chi_ptS hχ, ?_⟩
  have := congrArg star hx
  rw [star_star, star_smul, star_tri] at this
  rw [this]

theorem tri_eq_smul_tri_one {a b c : Fin 2 → ℂ} {l : ℂ} (hl : l ≠ 0)
    (h : tri a b c = l • tri ![0, 1] ![0, 1] ![0, 1]) :
    (∃ α : ℂ, a = α • (![0, 1] : Fin 2 → ℂ)) ∧ (∃ β : ℂ, b = β • (![0, 1] : Fin 2 → ℂ)) ∧
      ∃ γ : ℂ, c = γ • (![0, 1] : Fin 2 → ℂ) := by
  have h7 := congrFun h 7
  have h3 := congrFun h 3
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp [tri_apply, bitA, bitB, bitC] at h7 h3 h5 h6
  have ha1 : a 1 ≠ 0 := fun h' => hl (by rw [← h7, h']; ring)
  have hb1 : b 1 ≠ 0 := fun h' => hl (by rw [← h7, h']; ring)
  have hc1 : c 1 ≠ 0 := fun h' => hl (by rw [← h7, h']; ring)
  have ha0 : a 0 = 0 := by
    rcases h3 with (h | h) | h
    exacts [h, absurd h hb1, absurd h hc1]
  have hb0 : b 0 = 0 := by
    rcases h5 with (h | h) | h
    exacts [absurd h ha1, h, absurd h hc1]
  have hc0 : c 0 = 0 := by
    rcases h6 with (h | h) | h
    exacts [absurd h ha1, absurd h hb1, h]
  refine ⟨⟨a 1, ?_⟩, ⟨b 1, ?_⟩, ⟨c 1, ?_⟩⟩ <;> ext j <;> fin_cases j <;> simp [*]

theorem tri_eq_smul_tri_chi {a b c : Fin 2 → ℂ} {l z : ℂ} (hl : l ≠ 0)
    (h : tri a b c = l • tri (chi z) (chi z) (chi z)) :
    (∃ α : ℂ, a = α • chi z) ∧ (∃ β : ℂ, b = β • chi z) ∧ ∃ γ : ℂ, c = γ • chi z := by
  have h0 := congrFun h 0
  have h4 := congrFun h 4
  have h2 := congrFun h 2
  have h1 := congrFun h 1
  simp [tri_apply, bitA, bitB, bitC, chi] at h0 h4 h2 h1
  have ha0 : a 0 ≠ 0 := fun h' => hl (by rw [← h0, h']; ring)
  have hb0 : b 0 ≠ 0 := fun h' => hl (by rw [← h0, h']; ring)
  have hc0 : c 0 ≠ 0 := fun h' => hl (by rw [← h0, h']; ring)
  have ha1 : a 1 = z * a 0 := by
    apply mul_right_cancel₀ (mul_ne_zero hb0 hc0)
    linear_combination h4 - z * h0
  have hb1 : b 1 = z * b 0 := by
    apply mul_right_cancel₀ (mul_ne_zero ha0 hc0)
    linear_combination h2 - z * h0
  have hc1 : c 1 = z * c 0 := by
    apply mul_right_cancel₀ (mul_ne_zero ha0 hb0)
    linear_combination h1 - z * h0
  refine ⟨⟨a 0, ?_⟩, ⟨b 0, ?_⟩, ⟨c 0, ?_⟩⟩ <;> ext j <;> fin_cases j <;> simp [chi, *, mul_comm]

/-- A product vector on a ray `[χ ⊗ χ ⊗ χ]` has all three single-qubit factors proportional
to `χ`. -/
theorem tri_eq_smul_tri {s : ℝ} {a b c χ : Fin 2 → ℂ} {l : ℂ} (hl : l ≠ 0) (hχ : PtS s χ)
    (h : tri a b c = l • tri χ χ χ) :
    (∃ α : ℂ, a = α • χ) ∧ (∃ β : ℂ, b = β • χ) ∧ ∃ γ : ℂ, c = γ • χ := by
  rcases hχ with rfl | rfl | rfl
  · exact tri_eq_smul_tri_one hl h
  · exact tri_eq_smul_tri_chi (z := Complex.I * (Real.sqrt s : ℂ)) hl h
  · exact tri_eq_smul_tri_chi (z := -(Complex.I * (Real.sqrt s : ℂ))) hl h

/-- **`R_s` contains exactly three fully product rays** (`cor:ppt3-chirality` (b)): a nonzero vector
is a fully product vector of `R_s` iff it is a nonzero multiple of `|1⟩^{⊗3}` or of
`(|0⟩ ± i√s |1⟩)^{⊗3}`. -/
theorem fullProd_mem_Rs_iff {s : ℝ} (hs : 0 < s) {x : Fin 8 → ℂ} (h0 : x ≠ 0) :
    (x ∈ Rs s ∧ IsFullProd x) ↔ ∃ l : ℂ, l ≠ 0 ∧ ∃ χ, PtS s χ ∧ x = l • tri χ χ χ := by
  constructor
  · rintro ⟨hx, hp⟩
    exact fullProd_mem_Rs hs hx hp h0
  · rintro ⟨l, -, χ, hχ, rfl⟩
    exact ⟨Rs_smul l (tri_mem_Rs_of_ptS hs hχ), ⟨l • χ, χ, χ, (tri_smul_left l χ χ χ).symm⟩⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.fullProd_mem_Rs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullProd_mem_Rs

/-- info: 'FormalResearch.PPTThreeQubit.fullProd_mem_Rs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullProd_mem_Rs_iff

/-- info: 'FormalResearch.PPTThreeQubit.fullProd_mem_Rsbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullProd_mem_Rsbar

/-- info: 'FormalResearch.PPTThreeQubit.tri_eq_smul_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tri_eq_smul_tri

end FormalResearch.PPTThreeQubit

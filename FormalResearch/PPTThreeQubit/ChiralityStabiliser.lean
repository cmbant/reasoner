module

public import FormalResearch.PPTThreeQubit.Chirality

/-!
# The stabiliser of `R_s` among local filters (`cor:ppt3-chirality` (b), last sentence)

Source: `appendix_family.tex`, proof of `cor:ppt3-chirality` (b), the stabiliser paragraph.

`stabiliser_iff`: an invertible local filter `F_A ⊗ F_B ⊗ F_C` maps `R_s` into itself iff
`F_B, F_C` are multiples of `F_A` and `F_A` permutes the three points `|1⟩`, `|0⟩ ± i√s|1⟩` of `ℂP¹`
(up to scalars).  Together with `eq_smul_of_agree` (a Möbius map is determined by its action on
three points) this identifies the stabiliser, modulo scalars, with the group of Möbius maps
permuting the three points, which is `S₃`.  Existence of a Möbius map for each of the six
permutations is `exists_filter_perm`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

theorem shiftVec_add (x y : Fin 8 → ℂ) : shiftVec (x + y) = shiftVec x + shiftVec y := rfl

theorem shiftVec_smul (l : ℂ) (x : Fin 8 → ℂ) : shiftVec (l • x) = l • shiftVec x := rfl

theorem shiftVec_oVec : shiftVec oVec = ω ^ 2 • oVec := by
  ext i
  fin_cases i <;> simp [shiftVec, cycShift, oVec] <;>
    first | ring1 | linear_combination ω_cube | linear_combination (-1 : ℂ) * ω_cube |
      linear_combination ω * ω_cube | linear_combination (-ω) * ω_cube

theorem oVec_mem_Rs (s : ℝ) : oVec ∈ Rs s := by
  refine ⟨Pi.single 4 1, ?_⟩
  rw [Bs_mulVec]
  ext i
  fin_cases i <;> simp [oVec]

/-- Every `ω²`-eigenvector of the cyclic shift lies in `R_s` (it is in `span(e, o)`). -/
theorem mem_Rs_of_shift_eigen (s : ℝ) {y : Fin 8 → ℂ} (h : shiftVec y = ω ^ 2 • y) : y ∈ Rs s := by
  have E : ∀ i : Fin 8, y (cycShift i) = ω ^ 2 * y i := fun i => congrFun h i
  have E0 := E 0
  have E7 := E 7
  have E1 := E 1
  have E2 := E 2
  have E3 := E 3
  have E5 := E 5
  have E6 := E 6
  simp only [cycShift] at E0 E7 E1 E2 E3 E5 E6
  simp at E0 E7 E1 E2 E3 E5 E6
  have hω2 : ω ^ 2 - 1 ≠ 0 := by
    intro h'
    have : (ω - 1) * (ω + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact ω_ne_one h1
    · have : ω = -1 := by linear_combination h1
      have h3 := ω_sq_add_ω_add_one
      rw [this] at h3
      norm_num at h3
  have y0 : y 0 = 0 := by
    apply mul_left_cancel₀ hω2
    linear_combination -E0
  have y7 : y 7 = 0 := by
    apply mul_left_cancel₀ hω2
    linear_combination -E7
  refine ⟨![0, 0, 0, y 3, ω * y 1], ?_⟩
  rw [Bs_mulVec]
  ext i
  fin_cases i <;> simp
  · exact y0.symm
  · linear_combination y 1 * ω_cube
  · linear_combination -E1
  · linear_combination -E2 - ω ^ 2 * E1 - ω * y 1 * ω_cube
  · linear_combination -E6 - ω ^ 2 * E3 - ω * y 3 * ω_cube
  · linear_combination -E3
  · exact y7.symm

/-- Decomposition of `R_s` into the three fully product rays and the `ω²`-eigenspace of `Π`:
`B_s c = a₁ P_∞ + a₂ P₊ + a₃ P₋ + c₃ e + c₄ o`. -/
theorem Bs_decomp {s : ℝ} (hs : 0 < s) (c : Fin 5 → ℂ) :
    ∃ a₁ a₂ a₃ : ℂ, Bs s *ᵥ c =
      a₁ • tri ![0, 1] ![0, 1] ![0, 1] +
        a₂ • tri ![1, Complex.I * (Real.sqrt s : ℂ)] ![1, Complex.I * (Real.sqrt s : ℂ)]
          ![1, Complex.I * (Real.sqrt s : ℂ)] +
        a₃ • tri ![1, -(Complex.I * (Real.sqrt s : ℂ))] ![1, -(Complex.I * (Real.sqrt s : ℂ))]
          ![1, -(Complex.I * (Real.sqrt s : ℂ))] + (c 3 • eVec + c 4 • oVec) := by
  set z : ℂ := Complex.I * (Real.sqrt s : ℂ) with hzdef
  have hz2 : z ^ 2 = -(s : ℂ) := I_mul_sqrt_sq hs
  have hs' : (s : ℂ) = -z ^ 2 := by rw [hz2]; ring
  have hz0 : z ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hs).ne')
  obtain ⟨b, hb⟩ : ∃ b : ℂ, c 2 = 2 * z * b := ⟨c 2 / (2 * z), by field_simp⟩
  refine ⟨c 1 + s * c 2, c 0 / 2 + b, c 0 / 2 - b, ?_⟩
  rw [Bs_mulVec]
  ext i
  fin_cases i <;> simp [tri_apply, bitA, bitB, bitC, eVec, oVec, hb, hs'] <;> ring

theorem locMat_tri_mem {s : ℝ} (hs : 0 < s) {FA : Matrix (Fin 2) (Fin 2) ℂ} (μ ν : ℂ)
    {χ χ' : Fin 2 → ℂ} {α : ℂ} (hχ' : PtS s χ') (h : FA *ᵥ χ = α • χ') :
    locMat FA (μ • FA) (ν • FA) *ᵥ tri χ χ χ ∈ Rs s := by
  rw [locMat_mulVec_tri, smul_mulVec, smul_mulVec, h, smul_smul, smul_smul,
    tri_smul_left, tri_smul_mid, tri_smul_right]
  exact Rs_smul _ (Rs_smul _ (Rs_smul _ (tri_mem_Rs_of_ptS hs hχ')))

/-- **The stabiliser of `R_s` among invertible local filters** (`cor:ppt3-chirality` (b)).  A local
filter maps `R_s` into itself iff it is `c F₀ ⊗ F₀ ⊗ F₀` (`F_B`, `F_C` proportional to `F_A`) with `F₀`
permuting the three points `|1⟩`, `|0⟩ ± i√s|1⟩`. -/
theorem stabiliser_iff {s : ℝ} (hs : 0 < s) {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : IsUnit FA.det) (hB : IsUnit FB.det) (hC : IsUnit FC.det) :
    (∀ x ∈ Rs s, locMat FA FB FC *ᵥ x ∈ Rs s) ↔
      (((∃ μ : ℂ, FB = μ • FA) ∧ ∃ ν : ℂ, FC = ν • FA) ∧
        ∀ χ, PtS s χ → ∃ (χ' : Fin 2 → ℂ) (α : ℂ), PtS s χ' ∧ FA *ᵥ χ = α • χ') := by
  constructor
  · intro hF
    refine ⟨filter_proportional hs (R := Rs s)
      (fun x hx hp h0 => fullProd_mem_Rs hs hx hp h0) hA hB hC hF, fun χ hχ => ?_⟩
    obtain ⟨α, β, γ, χ', hχ', -, hα, -, -⟩ := filter_key hs (R := Rs s)
      (fun x hx hp h0 => fullProd_mem_Rs hs hx hp h0) hA hB hC hF hχ
    exact ⟨χ', α, hχ', hα⟩
  · rintro ⟨⟨⟨μ, rfl⟩, ν, rfl⟩, hperm⟩ x ⟨c, rfl⟩
    obtain ⟨a₁, a₂, a₃, hdec⟩ := Bs_decomp hs c
    rw [hdec]
    have hP : ∀ χ, PtS s χ → locMat FA (μ • FA) (ν • FA) *ᵥ tri χ χ χ ∈ Rs s := by
      intro χ hχ
      obtain ⟨χ', α, hχ', h⟩ := hperm χ hχ
      exact locMat_tri_mem hs μ ν hχ' h
    have hE : locMat FA (μ • FA) (ν • FA) *ᵥ (c 3 • eVec + c 4 • oVec) ∈ Rs s := by
      apply mem_Rs_of_shift_eigen
      rw [locMat_shift]
      have : shiftVec (c 3 • eVec + c 4 • oVec) = ω ^ 2 • (c 3 • eVec + c 4 • oVec) := by
        rw [shiftVec_add, shiftVec_smul, shiftVec_smul, shiftVec_eVec, shiftVec_oVec, smul_add,
          smul_comm (ω ^ 2) (c 3), smul_comm (ω ^ 2) (c 4)]
      rw [this, mulVec_smul]
    simp only [mulVec_add, mulVec_smul]
    refine Rs_add (Rs_add (Rs_add (Rs_smul _ (hP _ (Or.inl rfl))) (Rs_smul _ (hP _ (Or.inr (Or.inl rfl)))))
      (Rs_smul _ (hP _ (Or.inr (Or.inr rfl))))) ?_
    simpa only [mulVec_add, mulVec_smul] using hE

/-- **Three-transitivity of Möbius maps.**  For two triples of pairwise non-proportional vectors of
`ℂ²` there is an invertible `2 × 2` matrix sending each `p j` to a nonzero multiple of `q j`. -/
theorem exists_mobius (p q : Fin 3 → Fin 2 → ℂ)
    (hp : ∀ i j, i ≠ j → p i 0 * p j 1 - p i 1 * p j 0 ≠ 0)
    (hq : ∀ i j, i ≠ j → q i 0 * q j 1 - q i 1 * q j 0 ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℂ, IsUnit M.det ∧ ∀ j, ∃ α : ℂ, α ≠ 0 ∧ M *ᵥ p j = α • q j := by
  set D : ℂ := p 0 0 * p 1 1 - p 0 1 * p 1 0 with hD
  set D' : ℂ := q 0 0 * q 1 1 - q 0 1 * q 1 0 with hD'
  set a : ℂ := p 2 0 * p 1 1 - p 2 1 * p 1 0 with ha
  set b : ℂ := p 0 0 * p 2 1 - p 0 1 * p 2 0 with hb
  set a' : ℂ := q 2 0 * q 1 1 - q 2 1 * q 1 0 with ha'
  set b' : ℂ := q 0 0 * q 2 1 - q 0 1 * q 2 0 with hb'
  have hD0 : D ≠ 0 := hp 0 1 (by decide)
  have hD'0 : D' ≠ 0 := hq 0 1 (by decide)
  have ha0 : a ≠ 0 := hp 2 1 (by decide)
  have hb0 : b ≠ 0 := hp 0 2 (by decide)
  have ha'0 : a' ≠ 0 := hq 2 1 (by decide)
  have hb'0 : b' ≠ 0 := hq 0 2 (by decide)
  set L0 : ℂ := a' / (a * D') with hL0
  set L1 : ℂ := b' / (b * D') with hL1
  have hL00 : L0 ≠ 0 := div_ne_zero ha'0 (mul_ne_zero ha0 hD'0)
  have hL10 : L1 ≠ 0 := div_ne_zero hb'0 (mul_ne_zero hb0 hD'0)
  refine ⟨!![L0 * q 0 0, L1 * q 1 0; L0 * q 0 1, L1 * q 1 1] *
    !![p 1 1, -p 1 0; -p 0 1, p 0 0], ?_, ?_⟩
  · rw [det_mul, det_fin_two, det_fin_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    refine (IsUnit.mul ?_ ?_)
    · rw [isUnit_iff_ne_zero]
      have : L0 * q 0 0 * (L1 * q 1 1) - L1 * q 1 0 * (L0 * q 0 1) = L0 * L1 * D' := by
        rw [hD']; ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero hL00 hL10) hD'0
    · rw [isUnit_iff_ne_zero]
      have : p 1 1 * p 0 0 - -p 1 0 * -p 0 1 = D := by rw [hD]; ring
      rw [this]; exact hD0
  · intro j
    fin_cases j
    · refine ⟨D * L0, mul_ne_zero hD0 hL00, ?_⟩
      ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, hD] <;> ring
    · refine ⟨D * L1, mul_ne_zero hD0 hL10, ?_⟩
      ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, hD] <;> ring
    · refine ⟨1, one_ne_zero, ?_⟩
      have cr : ∀ i : Fin 2, D' * q 2 i = a' * q 0 i + b' * q 1 i := by
        intro i; fin_cases i <;> simp [hD', ha', hb'] <;> ring
      have e1 : a * L0 = a' / D' := by rw [hL0]; field_simp
      have e2 : b * L1 = b' / D' := by rw [hL1]; field_simp
      have hi : ∀ i : Fin 2, a * (L0 * q 0 i) + b * (L1 * q 1 i) = q 2 i := by
        intro i
        rw [← mul_assoc, ← mul_assoc, e1, e2]
        field_simp
        linear_combination -cr i
      ext i
      have := hi i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        linear_combination this

/-- Each of the six permutations of the three points is induced by an invertible `2 × 2` matrix
`F_π`, and `F_π ⊗ F_π ⊗ F_π` stabilises `R_s`. -/
theorem exists_filter_perm {s : ℝ} (hs : 0 < s) (π : Equiv.Perm (Fin 3)) :
    ∃ F : Matrix (Fin 2) (Fin 2) ℂ, IsUnit F.det ∧
      (∀ j, ∃ α : ℂ, α ≠ 0 ∧ F *ᵥ ptsS s j = α • ptsS s (π j)) ∧
      ∀ x ∈ Rs s, locMat F F F *ᵥ x ∈ Rs s := by
  obtain ⟨F, hF, hFj⟩ := exists_mobius (ptsS s) (fun j => ptsS s (π j)) (ptsS_ind hs)
    (fun i j hij => ptsS_ind hs (π i) (π j) (fun h => hij (π.injective h)))
  refine ⟨F, hF, hFj, ?_⟩
  have hF3 := (stabiliser_iff hs hF hF hF).mpr
  refine hF3 ⟨⟨⟨1, (one_smul ℂ F).symm⟩, ⟨1, (one_smul ℂ F).symm⟩⟩, fun χ hχ => ?_⟩
  have : ∃ j, ptsS s j = χ := by
    rcases hχ with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨j, rfl⟩ := this
  obtain ⟨α, -, hα⟩ := hFj j
  exact ⟨ptsS s (π j), α, ptsS_ptS s _, hα⟩

/-- Uniqueness up to a scalar of the Möbius map inducing a given permutation of the three points. -/
theorem eq_smul_of_perm {s : ℝ} (hs : 0 < s) {F F' : Matrix (Fin 2) (Fin 2) ℂ}
    (hF : IsUnit F.det) (π : Equiv.Perm (Fin 3))
    (h : ∀ j, ∃ α : ℂ, α ≠ 0 ∧ F *ᵥ ptsS s j = α • ptsS s (π j))
    (h' : ∀ j, ∃ α : ℂ, F' *ᵥ ptsS s j = α • ptsS s (π j)) : ∃ μ : ℂ, F' = μ • F := by
  refine eq_smul_of_agree hF (ptsS_ind hs) fun j => ?_
  obtain ⟨α, hα0, hα⟩ := h j
  obtain ⟨β, hβ⟩ := h' j
  exact ⟨β / α, by rw [hα, hβ, smul_smul, div_mul_cancel₀ _ hα0]⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.stabiliser_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stabiliser_iff

/-- info: 'FormalResearch.PPTThreeQubit.exists_mobius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_mobius

/-- info: 'FormalResearch.PPTThreeQubit.exists_filter_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_filter_perm

/-- info: 'FormalResearch.PPTThreeQubit.eq_smul_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_smul_of_perm

end FormalResearch.PPTThreeQubit

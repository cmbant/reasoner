module

public import FormalResearch.PPTThreeQubit.ChiralityRays

/-!
# Intrinsic local chirality of `R_s` (`cor:ppt3-chirality` (b))

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex` (`cor:ppt3-chirality`) and
`appendix_family.tex` (proof of `cor:ppt3-chirality` (b)).

For every `s > 0`, no invertible local filter `F_A ⊗ F_B ⊗ F_C` maps `R_s = ran B_s` onto (or even
into) its complex conjugate (`no_local_filter_conj`, `no_local_filter_conj_onto`), and no state with
range `R_s` is `F ρ̄ F†` for an invertible local filter `F` (`no_local_filter_state`).
Proof as in the paper: the three fully product rays of `R_s` (`ChiralityRays.lean`) are permuted
by a filter, a Möbius map is determined by its action on three points (`eq_smul_one_of_eigen`), so
the filter is `c F₀ ⊗ F₀ ⊗ F₀`, which commutes with the cyclic shift `Π`, while `Π` has eigenvalue
`ω²` on `e ∈ R_s` and has no nonzero `ω²`-eigenvector in `conj(R_s)`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-! ### A Möbius map is determined by its action on three points -/

/-- A `2 × 2` matrix with three pairwise non-proportional eigenvectors is a scalar matrix
(a Möbius map fixing three points is the identity). -/
theorem eq_smul_one_of_eigen {M : Matrix (Fin 2) (Fin 2) ℂ} {χ : Fin 3 → Fin 2 → ℂ}
    (hind : ∀ i j, i ≠ j → χ i 0 * χ j 1 - χ i 1 * χ j 0 ≠ 0)
    (h : ∀ j, ∃ μ : ℂ, M *ᵥ χ j = μ • χ j) : ∃ μ : ℂ, M = μ • 1 := by
  have hQ : ∀ j, M 1 0 * (χ j 0) ^ 2 + (M 1 1 - M 0 0) * (χ j 0 * χ j 1) +
      (-M 0 1) * (χ j 1) ^ 2 = 0 := by
    intro j
    obtain ⟨μ, hμ⟩ := h j
    have e0 := congrFun hμ 0
    have e1 := congrFun hμ 1
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at e0 e1
    linear_combination (χ j 0) * e1 - (χ j 1) * e0
  set N : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.of fun j k => ![(χ j 0) ^ 2, χ j 0 * χ j 1, (χ j 1) ^ 2] k with hN
  have hdet : N.det = (χ 0 0 * χ 1 1 - χ 0 1 * χ 1 0) * (χ 0 0 * χ 2 1 - χ 0 1 * χ 2 0) *
      (χ 1 0 * χ 2 1 - χ 1 1 * χ 2 0) := by
    rw [det_fin_three]
    simp [hN]
    ring
  have hdet0 : N.det ≠ 0 := by
    rw [hdet]
    have h01 := hind 0 1 (by decide)
    have h02 := hind 0 2 (by decide)
    have h12 := hind 1 2 (by decide)
    exact mul_ne_zero (mul_ne_zero h01 h02) h12
  have hv : N *ᵥ ![M 1 0, M 1 1 - M 0 0, -M 0 1] = 0 := by
    ext j
    have := hQ j
    simp only [hN, mulVec, dotProduct, Fin.sum_univ_three, of_apply, Pi.zero_apply]
    simp
    linear_combination this
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet0 hv
  have h10 : M 1 0 = 0 := by simpa using congrFun hz 0
  have h11 : M 1 1 - M 0 0 = 0 := by simpa using congrFun hz 1
  have h01 : M 0 1 = 0 := by simpa using congrFun hz 2
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01]
  linear_combination h11

/-- Two invertible `2 × 2` matrices that send three pairwise non-proportional vectors to
proportional vectors are proportional. -/
theorem eq_smul_of_agree {FA FB : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit FA.det)
    {χ : Fin 3 → Fin 2 → ℂ} (hind : ∀ i j, i ≠ j → χ i 0 * χ j 1 - χ i 1 * χ j 0 ≠ 0)
    (h : ∀ j, ∃ μ : ℂ, FB *ᵥ χ j = μ • (FA *ᵥ χ j)) : ∃ μ : ℂ, FB = μ • FA := by
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigen (M := FA⁻¹ * FB) hind (fun j => by
    obtain ⟨μ, hμ⟩ := h j
    refine ⟨μ, ?_⟩
    rw [← mulVec_mulVec, hμ, mulVec_smul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
      one_mulVec])
  refine ⟨μ, ?_⟩
  have := congrArg (FA * ·) hμ
  simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_smul] using this

/-! ### The three points and the permutation argument -/

/-- The three points `|1⟩`, `|0⟩ + i√s |1⟩`, `|0⟩ - i√s |1⟩`, in this order. -/
def ptsS (s : ℝ) : Fin 3 → Fin 2 → ℂ :=
  ![![0, 1], ![1, Complex.I * (Real.sqrt s : ℂ)], ![1, -(Complex.I * (Real.sqrt s : ℂ))]]

theorem ptsS_ptS (s : ℝ) (j : Fin 3) : PtS s (ptsS s j) := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem ptsS_ind {s : ℝ} (hs : 0 < s) (i j : Fin 3) (hij : i ≠ j) :
    ptsS s i 0 * ptsS s j 1 - ptsS s i 1 * ptsS s j 0 ≠ 0 := by
  have hr : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  have hIr : Complex.I * (Real.sqrt s : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hr
  have hr0 : ¬ Real.sqrt s = 0 := (Real.sqrt_pos.mpr hs).ne'
  fin_cases i <;> fin_cases j <;> simp [ptsS, hr0] at hij ⊢
  · intro h; apply hIr; linear_combination (-1 / 2 : ℂ) * h

theorem tri_ne_zero {a b c : Fin 2 → ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    tri a b c ≠ 0 := by
  have key : ∀ v : Fin 2 → ℂ, v ≠ 0 → ∃ i, v i ≠ 0 := by
    intro v hv
    by_contra hcon
    exact hv (funext fun i => by_contra fun h' => hcon ⟨i, h'⟩)
  obtain ⟨i, hi⟩ := key a ha
  obtain ⟨j, hj⟩ := key b hb
  obtain ⟨k, hk⟩ := key c hc
  intro h0
  have := congrFun h0 ⟨4 * i.val + 2 * j.val + k.val, by omega⟩
  simp only [tri_apply, Pi.zero_apply] at this
  have e1 : bitA ⟨4 * i.val + 2 * j.val + k.val, by omega⟩ = i := by
    ext; simp [bitA]; omega
  have e2 : bitB ⟨4 * i.val + 2 * j.val + k.val, by omega⟩ = j := by
    ext; simp [bitB]; omega
  have e3 : bitC ⟨4 * i.val + 2 * j.val + k.val, by omega⟩ = k := by
    ext; simp [bitC]; omega
  rw [e1, e2, e3] at this
  exact mul_ne_zero (mul_ne_zero hi hj) hk this

theorem mulVec_ne_zero {F : Matrix (Fin 2) (Fin 2) ℂ} (hF : IsUnit F.det) {v : Fin 2 → ℂ}
    (hv : v ≠ 0) : F *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (F⁻¹ *ᵥ ·) h
  rwa [mulVec_mulVec, Matrix.nonsing_inv_mul _ hF, one_mulVec, mulVec_zero] at this

theorem ptS_ne_zero {s : ℝ} {χ : Fin 2 → ℂ} (h : PtS s χ) : χ ≠ 0 := by
  intro h0
  have h0' := congrFun h0 0
  have h1' := congrFun h0 1
  rcases h with rfl | rfl | rfl <;> simp at h0' h1'

/-- **A filter sending `R_s` into `R` permutes the three points.**  If an invertible local filter
maps `R_s` into a set `R` whose fully product vectors lie on the three rays, it sends each of the
three points `χ` to a common point `χ'` under all of `F_A, F_B, F_C` (up to scalars). -/
theorem filter_key {s : ℝ} (hs : 0 < s) {R : Set (Fin 8 → ℂ)}
    (hR : ∀ x ∈ R, IsFullProd x → x ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ ∃ χ, PtS s χ ∧ x = l • tri χ χ χ)
    {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit FA.det) (hB : IsUnit FB.det)
    (hC : IsUnit FC.det) (hF : ∀ x ∈ Rs s, locMat FA FB FC *ᵥ x ∈ R) {χ : Fin 2 → ℂ}
    (hχ : PtS s χ) :
    ∃ α β γ : ℂ, ∃ χ', PtS s χ' ∧ α ≠ 0 ∧
      FA *ᵥ χ = α • χ' ∧ FB *ᵥ χ = β • χ' ∧ FC *ᵥ χ = γ • χ' := by
  have hχ0 := ptS_ne_zero hχ
  have hmem := hF _ (tri_mem_Rs_of_ptS hs hχ)
  rw [locMat_mulVec_tri] at hmem
  have h0 : tri (FA *ᵥ χ) (FB *ᵥ χ) (FC *ᵥ χ) ≠ 0 :=
    tri_ne_zero (mulVec_ne_zero hA hχ0) (mulVec_ne_zero hB hχ0) (mulVec_ne_zero hC hχ0)
  obtain ⟨l, hl, χ', hχ', hx⟩ := hR _ hmem ⟨_, _, _, rfl⟩ h0
  obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩⟩ := tri_eq_smul_tri hl hχ' hx
  refine ⟨α, β, γ, χ', hχ', ?_, hα, hβ, hγ⟩
  rintro rfl
  exact mulVec_ne_zero hA hχ0 (by rw [hα]; simp)

/-- **Permutation of the three rays forces `F = c F₀ ⊗ F₀ ⊗ F₀`.**  If an invertible local filter
maps `R_s` into a set `R` whose fully product vectors lie on the three rays, then `F_B` and `F_C`
are multiples of `F_A` (a Möbius map is determined by its action on three points). -/
theorem filter_proportional {s : ℝ} (hs : 0 < s) {R : Set (Fin 8 → ℂ)}
    (hR : ∀ x ∈ R, IsFullProd x → x ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ ∃ χ, PtS s χ ∧ x = l • tri χ χ χ)
    {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit FA.det) (hB : IsUnit FB.det)
    (hC : IsUnit FC.det) (hF : ∀ x ∈ Rs s, locMat FA FB FC *ᵥ x ∈ R) :
    (∃ μ : ℂ, FB = μ • FA) ∧ ∃ ν : ℂ, FC = ν • FA := by
  have key := fun j : Fin 3 => filter_key hs hR hA hB hC hF (ptsS_ptS s j)
  constructor
  · refine eq_smul_of_agree hA (ptsS_ind hs) fun j => ?_
    obtain ⟨α, β, γ, χ', -, hα0, hα, hβ, -⟩ := key j
    exact ⟨β / α, by rw [hα, hβ, smul_smul, div_mul_cancel₀ _ hα0]⟩
  · refine eq_smul_of_agree hA (ptsS_ind hs) fun j => ?_
    obtain ⟨α, β, γ, χ', -, hα0, hα, -, hγ⟩ := key j
    exact ⟨γ / α, by rw [hα, hγ, smul_smul, div_mul_cancel₀ _ hα0]⟩

/-! ### The shift eigenvalue obstruction -/

theorem ω_ne_one : ω - 1 ≠ 0 := by
  intro h
  have h1 : ω = 1 := by linear_combination h
  have := ω_sq_add_ω_add_one
  rw [h1] at this
  norm_num at this

theorem shiftVec_eVec : shiftVec eVec = ω ^ 2 • eVec := by
  ext i
  fin_cases i <;> simp [shiftVec, cycShift, eVec] <;>
    first | ring1 | linear_combination ω_cube | linear_combination (-1 : ℂ) * ω_cube |
      linear_combination ω * ω_cube | linear_combination (-ω) * ω_cube

theorem eVec_mem_Rs (s : ℝ) : eVec ∈ Rs s := by
  refine ⟨Pi.single 3 1, ?_⟩
  rw [Bs_mulVec]
  ext i
  fin_cases i <;> simp [eVec]

/-- `conj(R_s)` contains no nonzero `ω²`-eigenvector of the cyclic shift `Π`. -/
theorem eq_zero_of_shift_eigen_Rsbar {s : ℝ} {y : Fin 8 → ℂ} (hy : y ∈ Rsbar s)
    (h : shiftVec y = ω ^ 2 • y) : y = 0 := by
  obtain ⟨c, hc⟩ := hy
  have hu : shiftVec (star y) = ω • star y := by
    ext i
    have := congrFun h i
    simp only [shiftVec, Pi.smul_apply, smul_eq_mul] at this ⊢
    have h2 : star (y (cycShift i)) = star (ω ^ 2 * y i) := by rw [this]
    rw [star_mul', star_pow, star_ω] at h2
    simp only [Pi.star_apply]
    rw [h2]
    have : ((ω ^ 2) ^ 2 : ℂ) = ω := by linear_combination ω * ω_cube
    rw [this]
  rw [← hc] at hu
  have E : ∀ i : Fin 8, (Bs s *ᵥ c) (cycShift i) = ω * (Bs s *ᵥ c) i := fun i => congrFun hu i
  have E0 := E 0
  have E7 := E 7
  have E1 := E 1
  have E2 := E 2
  have E3 := E 3
  have E5 := E 5
  simp only [Bs_mulVec, cycShift] at E0 E7 E1 E2 E3 E5
  simp at E0 E7 E1 E2 E3 E5
  have hω := ω_ne_one
  have hω2 := ω_sq_sub_ne
  have c0 : c 0 = 0 := by
    apply mul_left_cancel₀ hω
    linear_combination -E0
  have c1 : c 1 = 0 := by
    apply mul_left_cancel₀ hω
    linear_combination -E7
  have c3 : c 3 = 0 := by
    apply mul_left_cancel₀ hω2
    linear_combination E3 - (s : ℂ) * (ω - 1) * c0
  have c24 : c 2 = c 4 := by
    apply mul_left_cancel₀ hω
    linear_combination -E1 - c 4 * ω_cube
  have c2 : c 2 = 0 := by
    have : (3 : ℂ) * c 2 = 0 := by
      linear_combination E2 + (1 - ω ^ 2) * c24 + c 2 * ω_sq_add_ω_add_one
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have hc0 : c = 0 := by
    funext a
    fin_cases a
    · exact c0
    · exact c1
    · exact c2
    · exact c3
    · exact c24 ▸ c2
  rw [hc0, mulVec_zero] at hc
  simpa using congrArg star hc.symm

theorem eVec_ne_zero : eVec ≠ 0 := by
  intro h
  have := congrFun h 3
  simp [eVec] at this

/-- **`cor:ppt3-chirality` (b), range version.**  For every `s > 0`, no invertible local filter
`F_A ⊗ F_B ⊗ F_C` maps `R_s` into its complex conjugate `conj(R_s)` (so in particular not onto it). -/
theorem no_local_filter_conj {s : ℝ} (hs : 0 < s) {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : IsUnit FA.det) (hB : IsUnit FB.det) (hC : IsUnit FC.det) :
    ¬ ∀ x ∈ Rs s, locMat FA FB FC *ᵥ x ∈ Rsbar s := by
  intro hF
  obtain ⟨⟨μ, hμ⟩, ν, hν⟩ := filter_proportional hs (R := Rsbar s)
    (fun x hx hp h0 => fullProd_mem_Rsbar hs hx hp h0) hA hB hC hF
  subst hμ hν
  have h1 := hF eVec (eVec_mem_Rs s)
  have h2 : shiftVec (locMat FA (μ • FA) (ν • FA) *ᵥ eVec) =
      ω ^ 2 • (locMat FA (μ • FA) (ν • FA) *ᵥ eVec) := by
    rw [locMat_shift, shiftVec_eVec, mulVec_smul]
  have h3 := eq_zero_of_shift_eigen_Rsbar h1 h2
  exact eVec_ne_zero (locMat_injective hA hB hC (h3.trans (mulVec_zero _).symm))

/-- The image of `R_s` under an invertible local filter is never `conj(R_s)`. -/
theorem no_local_filter_conj_onto {s : ℝ} (hs : 0 < s) {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : IsUnit FA.det) (hB : IsUnit FB.det) (hC : IsUnit FC.det) :
    (fun x => locMat FA FB FC *ᵥ x) '' Rs s ≠ Rsbar s := fun h =>
  no_local_filter_conj hs hA hB hC fun x hx => h ▸ ⟨x, hx, rfl⟩

theorem star_mulVec_map_star (ρ : Matrix (Fin 8) (Fin 8) ℂ) (w : Fin 8 → ℂ) :
    star (ρ.map star *ᵥ w) = ρ *ᵥ star w := by
  ext i
  simp [mulVec, dotProduct, star_sum]

/-- **`cor:ppt3-chirality` (b), state version.**  No state `ρ` with range `R_s` equals
`F ρ̄ F†` for an invertible local filter `F = F_A ⊗ F_B ⊗ F_C` (in particular not for a local
unitary: `ρ` is not related to its complex conjugate or its spin time reversal by local filters). -/
theorem no_local_filter_state {s : ℝ} (hs : 0 < s) {ρ : Matrix (Fin 8) (Fin 8) ℂ}
    (hρ : Set.range ρ.mulVec = Rs s) {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : IsUnit FA.det) (hB : IsUnit FB.det) (hC : IsUnit FC.det) :
    ρ ≠ locMat FA FB FC * ρ.map star * (locMat FA FB FC)ᴴ := by
  intro hρF
  refine no_local_filter_conj hs (FA := FA⁻¹) (FB := FB⁻¹) (FC := FC⁻¹)
    (Matrix.isUnit_nonsing_inv_det _ hA) (Matrix.isUnit_nonsing_inv_det _ hB)
    (Matrix.isUnit_nonsing_inv_det _ hC) fun x hx => ?_
  have hx' : x ∈ Set.range ρ.mulVec := hρ ▸ hx
  obtain ⟨v, rfl⟩ := hx'
  have hinv : locMat FA⁻¹ FB⁻¹ FC⁻¹ * locMat FA FB FC = 1 := by
    rw [locMat_mul, Matrix.nonsing_inv_mul _ hA, Matrix.nonsing_inv_mul _ hB,
      Matrix.nonsing_inv_mul _ hC, locMat_one]
  have h1 : locMat FA⁻¹ FB⁻¹ FC⁻¹ *ᵥ (ρ *ᵥ v) = ρ.map star *ᵥ ((locMat FA FB FC)ᴴ *ᵥ v) := by
    conv_lhs => rw [hρF]
    rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      ← mulVec_mulVec]
  show star _ ∈ Rs s
  rw [h1, star_mulVec_map_star, ← hρ]
  exact ⟨_, rfl⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.eq_smul_one_of_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_smul_one_of_eigen

/-- info: 'FormalResearch.PPTThreeQubit.eq_smul_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_smul_of_agree

/-- info: 'FormalResearch.PPTThreeQubit.filter_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filter_proportional

/-- info: 'FormalResearch.PPTThreeQubit.no_local_filter_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_local_filter_conj

/-- info: 'FormalResearch.PPTThreeQubit.no_local_filter_conj_onto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_local_filter_conj_onto

/-- info: 'FormalResearch.PPTThreeQubit.no_local_filter_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_local_filter_state

end FormalResearch.PPTThreeQubit

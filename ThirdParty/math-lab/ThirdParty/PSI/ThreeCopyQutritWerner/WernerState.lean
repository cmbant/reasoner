module

public import ThreeCopyQutritWerner.Physical
public import ThreeCopyQutritWerner.Distillation
public import ThreeCopyQutritWerner.TwoCutMain

@[expose] public section


/-!
# The Werner state and its partial-transpose threshold

Manuscript Section 1, eq. (1): for `-1 ≤ α ≤ 1` the operator
`ρ_{d,α} = (I - α F_d) / (d (d - α))` is a state (Hermitian, positive semidefinite,
trace one), and it has negative partial transpose exactly when `α > 1/d`.

The last section restates the qutrit thresholds of `Physical.lean` for the operational
local-filter predicates of `Distillation.lean`.
-/

noncomputable section

open scoped ComplexOrder Matrix

namespace ThreeCopyQutritWerner

section Entries

/-- Entries of the flip on a product index type. -/
theorem swapOp_apply_prod {a : Type*} [DecidableEq a] (i j k l : a) :
    swapOp a (i, j) (k, l) = (if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0) := by
  by_cases h1 : i = l <;> by_cases h2 : j = k <;> simp [swapOp, h1, h2]

/-- For real `α` the Werner normalization is the cast of a real number. -/
theorem werner_scalar (d : ℕ) (α : ℝ) :
    (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) = ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) := by
  first
    | (push_cast; done)
    | (push_cast; ring)
    | norm_num

/-- Entries of the Werner state. -/
theorem werner_apply_prod (d : ℕ) (α : ℝ) (i j k l : Fin d) :
    werner d α (i, j) (k, l) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
          (α : ℂ) * ((if i = l then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0))) := by
  simp only [werner, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, one_apply_prod,
    swapOp_apply_prod]

theorem star_ite_one_zero (p : Prop) [Decidable p] :
    star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem ite_comm_eq {a : Type*} [DecidableEq a] (x y : a) :
    (if x = y then (1 : ℂ) else 0) = if y = x then 1 else 0 := by
  by_cases h : x = y
  · subst h
    rfl
  · simp [h, Ne.symm h]

end Entries

/-- The Werner operator is Hermitian for every real `α`. -/
theorem werner_isHermitian (d : ℕ) (α : ℝ) : (werner d α).IsHermitian := by
  refine Matrix.IsHermitian.ext fun x y => ?_
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  have hr : star ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) = ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  have ha : star (α : ℂ) = (α : ℂ) := Complex.conj_ofReal _
  rw [werner_apply_prod, werner_apply_prod, werner_scalar]
  simp only [star_mul', star_sub, star_ite_one_zero, hr, ha]
  rw [ite_comm_eq k i, ite_comm_eq l j, ite_comm_eq k j, ite_comm_eq l i]
  ring

/-- `Tr F_d = d`. -/
theorem trace_swapOp (a : Type*) [Fintype a] [DecidableEq a] :
    (swapOp a).trace = Fintype.card a := by
  have h : ∀ i : a, ∑ j : a, swapOp a (i, j) (i, j) = 1 := by
    intro i
    simp only [swapOp_apply_prod]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

/-- Manuscript eq. (1): the Werner state has trace one (for `d ≠ 0`, `α ≠ d`). -/
theorem trace_werner (d : ℕ) (α : ℝ) (hd : d ≠ 0) (hα : α ≠ d) : (werner d α).trace = 1 := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hα' : (d : ℂ) - (α : ℂ) ≠ 0 := by
    intro h
    apply hα
    have h2 : ((d : ℝ) : ℂ) = (α : ℂ) := by
      rw [Complex.ofReal_natCast]
      linear_combination h
    exact (Complex.ofReal_injective h2).symm
  have key : (werner d α).trace =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * ((d : ℂ) * ((d : ℂ) - (α : ℂ))) := by
    unfold werner
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, trace_swapOp]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  rw [key, inv_mul_cancel₀ (mul_ne_zero hd' hα')]

section Expectation

/-- The flip acts on vectors by exchanging the two tensor factors. -/
theorem swapOp_mulVec {a : Type*} [Fintype a] [DecidableEq a] (φ : a × a → ℂ) :
    swapOp a *ᵥ φ = fun x => φ (x.2, x.1) := by
  funext x
  obtain ⟨i, j⟩ := x
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, swapOp_apply_prod]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `⟨φ, ρ_{d,α} φ⟩ = (‖φ‖² - α ⟨φ, F φ⟩) / (d (d - α))`. -/
theorem expectation_werner (d : ℕ) (α : ℝ) (φ : Fin d × Fin d → ℂ) :
    expectation (werner d α) φ =
      ((((d : ℝ) * ((d : ℝ) - α))⁻¹ : ℝ) : ℂ) *
        ((∑ x, star (φ x) * φ x) - (α : ℂ) * ∑ x : Fin d × Fin d, star (φ x) * φ (x.2, x.1)) := by
  rw [expectation_eq_dotProduct]
  unfold werner
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    swapOp_mulVec, dotProduct_smul, dotProduct_sub, dotProduct_smul, werner_scalar]
  simp only [dotProduct, Pi.star_apply, smul_eq_mul]

theorem re_sum_star_mul_self {ι : Type*} [Fintype ι] (φ : ι → ℂ) :
    (∑ x, star (φ x) * φ x).re = vecNormSq φ := by
  rw [Complex.re_sum]
  unfold vecNormSq
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show star (φ x) * φ x = ((Complex.normSq (φ x) : ℝ) : ℂ) from
    Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re]

theorem re_expectation_werner (d : ℕ) (α : ℝ) (φ : Fin d × Fin d → ℂ) :
    (expectation (werner d α) φ).re =
      ((d : ℝ) * ((d : ℝ) - α))⁻¹ *
        (vecNormSq φ - α * (∑ x : Fin d × Fin d, star (φ x) * φ (x.2, x.1)).re) := by
  rw [expectation_werner, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_ofReal_mul,
    re_sum_star_mul_self]

theorem re_star_mul_le (a b : ℂ) :
    (star a * b).re ≤ (Complex.normSq a + Complex.normSq b) / 2 := by
  have h : (star a * b).re = a.re * b.re + a.im * b.im := by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im - b.im)]

theorem neg_re_star_mul_le (a b : ℂ) :
    -(star a * b).re ≤ (Complex.normSq a + Complex.normSq b) / 2 := by
  have h : (star a * b).re = a.re * b.re + a.im * b.im := by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [h, Complex.normSq_apply, Complex.normSq_apply]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

theorem sum_normSq_swap {a : Type*} [Fintype a] (φ : a × a → ℂ) :
    ∑ x : a × a, Complex.normSq (φ (x.2, x.1)) = ∑ x : a × a, Complex.normSq (φ x) :=
  Fintype.sum_equiv (Equiv.prodComm a a) _ _ (fun _ => rfl)

/-- `|Re ⟨φ, F φ⟩| ≤ ‖φ‖²`. -/
theorem abs_re_sum_swap_le {a : Type*} [Fintype a] (φ : a × a → ℂ) :
    |(∑ x : a × a, star (φ x) * φ (x.2, x.1)).re| ≤ vecNormSq φ := by
  have e : ∑ x : a × a, (Complex.normSq (φ x) + Complex.normSq (φ (x.2, x.1))) / 2 =
      vecNormSq φ := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, sum_normSq_swap]
    unfold vecNormSq
    ring
  rw [Complex.re_sum, abs_le]
  constructor
  · have h := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset (a × a))) =>
      neg_re_star_mul_le (φ x) (φ (x.2, x.1))
    rw [e, Finset.sum_neg_distrib] at h
    linarith
  · have h := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset (a × a))) =>
      re_star_mul_le (φ x) (φ (x.2, x.1))
    rw [e] at h
    exact h

end Expectation

/-- Manuscript eq. (1): for `-1 ≤ α ≤ 1` the Werner operator is positive semidefinite. -/
theorem werner_posSemidef (d : ℕ) (α : ℝ) (hm : -1 ≤ α) (h1 : α ≤ 1) :
    (werner d α).PosSemidef := by
  by_contra h
  obtain ⟨φ, hφ⟩ :=
    (not_posSemidef_iff_exists_expectation_re_neg _ (werner_isHermitian d α)).mp h
  rw [re_expectation_werner] at hφ
  have hb := abs_le.mp (abs_re_sum_swap_le φ)
  have hr : 0 ≤ ((d : ℝ) * ((d : ℝ) - α))⁻¹ := by
    apply inv_nonneg.mpr
    rcases Nat.eq_zero_or_pos d with hd | hd
    · simp [hd]
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
  have hk : 0 ≤ vecNormSq φ - α * (∑ x : Fin d × Fin d, star (φ x) * φ (x.2, x.1)).re := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + α)
        (by linarith [hb.2] : (0 : ℝ) ≤ vecNormSq φ -
          (∑ x : Fin d × Fin d, star (φ x) * φ (x.2, x.1)).re),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α)
        (by linarith [hb.1] : (0 : ℝ) ≤ vecNormSq φ +
          (∑ x : Fin d × Fin d, star (φ x) * φ (x.2, x.1)).re)]
  linarith [mul_nonneg hr hk]

/-- Manuscript eq. (1): for `d ≥ 2` and `-1 ≤ α ≤ 1`, `ρ_{d,α}` is a density operator. -/
theorem werner_isState (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (hm : -1 ≤ α) (h1 : α ≤ 1) :
    (werner d α).PosSemidef ∧ (werner d α).trace = 1 := by
  refine ⟨werner_posSemidef d α hm h1, trace_werner d α (by omega) ?_⟩
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  intro h
  linarith

section Threshold

theorem frobSq_one (n : Type*) [Fintype n] [DecidableEq n] :
    frobSq (1 : Matrix n n ℂ) = Fintype.card n := by
  unfold frobSq
  have h : ∀ i : n, ∑ j : n, Complex.normSq ((1 : Matrix n n ℂ) i j) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Matrix.one_apply_ne (Ne.symm hj)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

/-- Manuscript Section 1: for `d ≥ 2` and `α ≤ 1`, `ρ_{d,α}` is NPT exactly when `α > 1/d`. -/
theorem isNPT_werner_iff (d : ℕ) (hd : 2 ≤ d) (α : ℝ) (h1 : α ≤ 1) :
    IsNPT (werner d α) ↔ 1 / (d : ℝ) < α := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hr : 0 < ((d : ℝ) * ((d : ℝ) - α))⁻¹ := by
    apply inv_pos.mpr
    nlinarith
  have hre : ∀ C : Matrix (Fin d) (Fin d) ℂ,
      (expectation (partialTranspose (werner d α)) (vec C)).re =
        ((d : ℝ) * ((d : ℝ) - α))⁻¹ * (frobSq C - α * Complex.normSq C.trace) := by
    intro C
    rw [expectation_partialTranspose_werner, werner_scalar, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [isNPT_iff_exists_expectation_re_neg _ (werner_isHermitian d α)]
  constructor
  · rintro ⟨ψ, hψ⟩
    by_contra hα
    have hα' : α ≤ 1 / (d : ℝ) := not_lt.mp hα
    obtain ⟨C, rfl⟩ : ∃ C : Matrix (Fin d) (Fin d) ℂ, ψ = vec C := ⟨_, eq_vec_of ψ⟩
    rw [hre] at hψ
    have hT : Complex.normSq C.trace ≤ (d : ℝ) * frobSq C := by
      have hrank : C.rank ≤ d := by
        have h := C.rank_le_card_width
        rwa [Fintype.card_fin] at h
      have h := normSq_trace_le_mul_of_rank_le C d hrank
      unfold frobSq
      exact h
    have hF : 0 ≤ frobSq C := frobSq_nonneg C
    have hT0 : 0 ≤ Complex.normSq C.trace := Complex.normSq_nonneg _
    have hαd : α * d ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hα' hdpos.le
      rwa [one_div, inv_mul_cancel₀ hdpos.ne'] at h
    have key : 0 ≤ frobSq C - α * Complex.normSq C.trace := by
      rcases le_or_gt 0 α with h0 | h0
      · nlinarith [mul_le_mul_of_nonneg_left hT h0]
      · nlinarith [mul_nonneg (neg_nonneg.mpr h0.le) hT0]
    have := mul_nonneg hr.le key
    linarith
  · intro hα
    refine ⟨vec (1 : Matrix (Fin d) (Fin d) ℂ), ?_⟩
    rw [hre, frobSq_one, Fintype.card_fin, Matrix.trace_one, Fintype.card_fin,
      ← Complex.ofReal_natCast, Complex.normSq_ofReal]
    have h' : 1 < α * d := by
      have h := mul_lt_mul_of_pos_right hα hdpos
      rwa [one_div, inv_mul_cancel₀ hdpos.ne'] at h
    have hneg : (d : ℝ) - α * ((d : ℝ) * (d : ℝ)) < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hr hneg

/-- The qutrit case: `ρ_{3,α}` is NPT exactly when `α > 1/3` (for `α ≤ 1`). -/
theorem isNPT_werner_three_iff (α : ℝ) (h1 : α ≤ 1) :
    IsNPT (werner 3 α) ↔ 1 / 3 < α := by
  rw [isNPT_werner_iff 3 (by norm_num) α h1]
  norm_num

end Threshold

section Operational

/-- Section 1 at `d = 3`, operational form: one copy of `ρ_{3,α}` can be filtered to an NPT
two-qubit operator exactly when `α > 1/2` (for `α ≤ 1`). -/
theorem isOneCopyFilterDistillable_werner_three_iff {α : ℝ} (hm : -1 ≤ α) (h1 : α ≤ 1) :
    IsOneCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α := by
  rw [isOneCopyFilterDistillable_iff _ (werner_isHermitian 3 α)]
  exact isOneCopyRankTwoDetectable_werner_three_iff hm h1

/-- Corollary 2.2 at `d = 3`, operational form, `1/2 < α ≤ 1`: three copies are distillable. -/
theorem isThreeCopyFilterDistillable_werner_three {α : ℝ} (h : 1 / 2 < α) (h1 : α ≤ 1) :
    IsThreeCopyFilterDistillable (werner 3 α) :=
  (isThreeCopyFilterDistillable_iff _ (werner_isHermitian 3 α)).mpr
    (isThreeCopyRankTwoDetectable_werner_three h h1)

/-- Corollary 2.2 at `d = 3`, operational form, `α ≤ 0`: three copies are not distillable. -/
theorem not_isThreeCopyFilterDistillable_werner_three_of_nonpos {α : ℝ} (h0 : α ≤ 0) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  rw [isThreeCopyFilterDistillable_iff _ (werner_isHermitian 3 α)]
  exact not_isThreeCopyRankTwoDetectable_werner_three_of_nonpos h0

/-- CONDITIONAL on the qutrit endpoint inequality `hq` (open claim T2.1a): three copies of
`ρ_{3,α}` are not distillable for `0 ≤ α ≤ 1/2`. -/
theorem not_isThreeCopyFilterDistillable_werner_three_of_endpoint {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  rw [isThreeCopyFilterDistillable_iff _ (werner_isHermitian 3 α)]
  exact not_isThreeCopyRankTwoDetectable_werner_three_of_endpoint h0 h1 hq

/-- Corollary 2.2 at `d = 3`, operational form, CONDITIONAL on the qutrit endpoint
inequality `hq` (open claim T2.1a): for `α ≤ 1`, three copies of `ρ_{3,α}` are
distillable exactly when `α > 1/2`. -/
theorem isThreeCopyFilterDistillable_werner_three_iff_of_endpoint {α : ℝ} (h1 : α ≤ 1)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C) :
    IsThreeCopyFilterDistillable (werner 3 α) ↔ 1 / 2 < α := by
  constructor
  · intro h
    by_contra hα
    push_neg at hα
    rcases le_or_gt α 0 with h0 | h0
    · exact not_isThreeCopyFilterDistillable_werner_three_of_nonpos h0 h
    · exact not_isThreeCopyFilterDistillable_werner_three_of_endpoint h0.le hα hq h
  · intro h
    exact isThreeCopyFilterDistillable_werner_three h h1

/-- Corollary 2.2 at `d = 3`, CONDITIONAL on the qutrit endpoint
inequality `hq`: for `1/3 < α ≤ 1/2`, `ρ_{3,α}` is NPT and three-copy nondistillable. -/
theorem werner_three_isNPT_and_not_distillable_of_endpoint {α : ℝ} (h0 : 1 / 3 < α)
    (h1 : α ≤ 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C) :
    IsNPT (werner 3 α) ∧ ¬ IsThreeCopyFilterDistillable (werner 3 α) :=
  ⟨(isNPT_werner_three_iff α (by linarith)).mpr h0,
    not_isThreeCopyFilterDistillable_werner_three_of_endpoint (by linarith) h1 hq⟩

end Operational

end ThreeCopyQutritWerner

end

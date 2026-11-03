import FormalResearch.PPTThreeQubit.FamilyPPTFactor

/-!
# The rank-five family `ρ_t`: the fully-PPT interval

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/family.tex`,
`thm:ppt3-family` (proof "PPT and rank claims"), with `eq:ppt3-interval` and `eq:ppt3-minors`.

Setting (conventions of `Basic.lean`, `FamilyGME.lean`): `ρ_t = B X_t B†` is `rhoT t`, the partial
transposes `ptA`, `ptB`, `ptC` are those of `PartialTranspose.lean`, `tMinus = (15 + 9√17)/16`
(`FamilyGME.lean`) and `tPlus = 2(√37 - 1)/3`.

Covered (all proved, no numerical input):
* `ρ_t` is positive semidefinite for `t > 0` (`rhoT_posSemidef`);
* for `t_- ≤ t ≤ t_+` all three partial transposes are positive semidefinite
  (`ppt3_family_ppt`), and such `ρ_t` is also GME (`ppt3_family_ppt_gme`);
* conversely, for `t > 0` the partial transpose on `A` fails to be positive semidefinite when
  `t < t_-` or `t > t_+`, so `ρ_t` is fully PPT exactly on `[t_-, t_+]` (`ppt3_family_ppt_iff`);
* the numerical ordering `3 < t_- < 10/3 < t_+ < 2√3` and the explicit member `t = 10/3`.

Method.  The cyclic qubit shift fixes `ρ_t` (`rhoT_cycShift`), so `ρ_t^{T_B}`, `ρ_t^{T_C}` are
index permutations of `ρ_t^{T_A}`.  The numerator of `ρ_t^{T_A}` is block diagonal in the parity of
`(abc)`, with the even block (`blockEven`, order `(000,011,101,110)`) and the odd block
(`blockOdd`, order `(001,010,100,111)`) of the proof of `thm:ppt3-family`.  The positive
semidefiniteness is an explicit `LDL*` factorization `ρ_t^{T_A} = (7(t+3))⁻¹ ∑ₖ dₖ |lₖ⟩⟨lₖ|`
(`ptA_rhoT_eq`), where the pivots `dₖ` (`dpiv`) are the ratios of consecutive leading minors of
`eq:ppt3-minors` and are nonnegative on `[t_-, t_+]`.  The converse uses `det ≥ 0` for a
positive semidefinite principal block together with the two fourth minors
`3(8t² - 15t - 36)` and `-3(t - 3)(3t² + 4t - 48)` of `eq:ppt3-minors`
(`det_blockEven`, `det_blockOdd`).

Not covered here: the rank profile `(5, 8, 8, 8)` / `(5, 7, 7, 7)`, rank five of `ρ_t`, and
minimality of rank five (low-rank PPT theorem).  The leading `1 × 1`, `2 × 2`, `3 × 3` minors of
`eq:ppt3-minors` are not stated separately: they appear as the pivot ratios `dpiv`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix ComplexOrder

noncomputable section

/-- `8 t² - 15 t - 36 ≥ 0` for `t ≥ t_-` (the fourth even pivot is nonnegative). -/
theorem tMinus_nonneg_facts (t : ℝ) (h : tMinus ≤ t) : 0 ≤ 8 * t ^ 2 - 15 * t - 36 := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  unfold tMinus at h
  nlinarith

/-! ### The PPT interval -/

/-- The upper end `t_+ = 2(√37 - 1)/3` of the PPT interval `eq:ppt3-interval`: the root in
`(3, 2√3)` of `3t² + 4t - 48` (`tPlus_root`). -/
def tPlus : ℝ := 2 * (Real.sqrt 37 - 1) / 3

/-- `3t² + 4t - 48 ≤ 0` for `3 < t ≤ t_+`. -/
theorem tPlus_facts (t : ℝ) (h3 : 3 < t) (h : t ≤ tPlus) : 3 * t ^ 2 + 4 * t - 48 ≤ 0 := by
  have h37 : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg _
  unfold tPlus at h
  nlinarith

/-- `3 < t_-`. -/
theorem three_lt_tMinus : 3 < tMinus := lt_trans (by norm_num) tMinus_gt

/-- The pivots of the factorization are nonnegative on the PPT interval. -/
theorem dpiv_nonneg (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) (k : Fin 8) : 0 ≤ dpiv t k := by
  have h3 : 3 < t := lt_of_lt_of_le three_lt_tMinus h1
  have hp := tPlus_facts t h3 h2
  have hm := tMinus_nonneg_facts t h1
  have h12 : t ^ 2 < 12 := by nlinarith
  have h7 : 0 < 3 * t - 7 := by linarith
  fin_cases k <;> simp only [dpiv] <;> simp
  · linarith
  · positivity
  · exact div_nonneg (by positivity) (by positivity)
  · exact div_nonneg (by nlinarith) (by positivity)
  · linarith
  · exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) hp) (by linarith)

/-- `ρ_t^{T_A}` is positive semidefinite for `t_- ≤ t ≤ t_+`. -/
theorem posSemidef_ptA_rhoT (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    (ptA (rhoT t)).PosSemidef := by
  have h3 : 3 < t := lt_of_lt_of_le three_lt_tMinus h1
  have hp := tPlus_facts t h3 h2
  have h12 : t ^ 2 ≠ 12 := by intro h; nlinarith
  rw [ptA_rhoT_eq t h3 h12]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun k _ => ?_) (by positivity)
  exact (posSemidef_vecMulVec_self_star _).smul (dpiv_nonneg t h1 h2 k)


/-- `ρ_t^{T_B}` is positive semidefinite for `t_- ≤ t ≤ t_+` (cyclic symmetry). -/
theorem posSemidef_ptB_rhoT (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    (ptB (rhoT t)).PosSemidef := by
  rw [ptB_eq_of_shift_invariant _ (rhoT_cycShift t)]
  exact (posSemidef_ptA_rhoT t h1 h2).submatrix _

/-- `ρ_t^{T_C}` is positive semidefinite for `t_- ≤ t ≤ t_+` (cyclic symmetry). -/
theorem posSemidef_ptC_rhoT (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    (ptC (rhoT t)).PosSemidef := by
  rw [ptC_eq_of_shift_invariant _ (rhoT_cycShift t)]
  exact (posSemidef_ptA_rhoT t h1 h2).submatrix _

/-- The coefficient matrix `X_t` is positive semidefinite for `t > 0`. -/
theorem Xt_posSemidef (t : ℝ) (ht : 0 < t) : (Xt t).PosSemidef := by
  unfold Xt
  apply Matrix.PosSemidef.diagonal
  intro a
  have h : (0 : ℝ) ≤ ![t, 3 * t, 3, 3, 1] a / (7 * (t + 3)) := by
    apply div_nonneg _ (by positivity)
    fin_cases a <;> simp <;> positivity
  exact Complex.zero_le_real.mpr h

/-- `ρ_t = B X_t B†` is positive semidefinite for every `t > 0` (`eq:ppt3-rho`). -/
theorem rhoT_posSemidef (t : ℝ) (ht : 0 < t) : (rhoT t).PosSemidef := by
  unfold rhoT
  exact (Xt_posSemidef t ht).mul_mul_conjTranspose_same _

/-- The even-parity block `(000, 011, 101, 110)` of the numerator of `ρ_t^{T_A}`
(`7(t+3) ρ_t^{T_A}`), written with `ω² = star ω`. -/
def blockEven (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(t : ℂ), -t, 3 + ω, 3 + ω ^ 2;
     -t, t + 3, 0, 0;
     3 + ω ^ 2, 0, t + 3, t + 3 * ω ^ 2;
     3 + ω, 0, t + 3 * ω, t + 3]

/-- The odd-parity block `(001, 010, 100, 111)`. -/
def blockOdd (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![4, 3 + ω, -t, t + 3 * ω;
     3 + ω ^ 2, 4, -t, t + 3 * ω ^ 2;
     -t, -t, 4, 0;
     t + 3 * ω ^ 2, t + 3 * ω, 0, 3 * t]

/-- The even determinant of `eq:ppt3-minors`: `3(8t² - 15t - 36)`. -/
theorem det_blockEven (t : ℝ) : (blockEven t).det = ((3 * (8 * t ^ 2 - 15 * t - 36) : ℝ) : ℂ) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  simp [blockEven, det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  simp only [ω_cube, ω_pow4, ω_pow5, h2]
  ring_nf

/-- The odd determinant of `eq:ppt3-minors`: `-3(t - 3)(3t² + 4t - 48)`. -/
theorem det_blockOdd (t : ℝ) : (blockOdd t).det = ((-3 * (t - 3) * (3 * t ^ 2 + 4 * t - 48) : ℝ) : ℂ) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  simp [blockOdd, det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  simp only [ω_cube, ω_pow4, ω_pow5, h2]
  ring_nf

/-- The even parity block of `ρ_t^{T_A}` is `(7(t+3))⁻¹` times `blockEven t`. -/
theorem ptA_block_even (t : ℝ) :
    (ptA (rhoT t)).submatrix ![0, 3, 5, 6] ![0, 3, 5, 6] =
      ((1 / (7 * (t + 3)) : ℝ) : ℂ) • blockEven t := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptA, rhoT_apply, blockEven, uVec, vVec, wVec, eVec, oVec, conj_ω, -mul_eq_mul_left_iff]
  all_goals
    try ring_nf
    try simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, h2]
    try ring_nf

/-- The odd parity block of `ρ_t^{T_A}` is `(7(t+3))⁻¹` times `blockOdd t`. -/
theorem ptA_block_odd (t : ℝ) :
    (ptA (rhoT t)).submatrix ![1, 2, 4, 7] ![1, 2, 4, 7] =
      ((1 / (7 * (t + 3)) : ℝ) : ℂ) • blockOdd t := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptA, rhoT_apply, blockOdd, uVec, vVec, wVec, eVec, oVec, conj_ω, -mul_eq_mul_left_iff]
  all_goals
    try ring_nf
    try simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, h2]
    try ring_nf


/-- `3 < t_+`. -/
theorem three_lt_tPlus : 3 < tPlus := by
  have h37 : (11 / 2 : ℝ) < Real.sqrt 37 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold tPlus; linarith

/-- `8t² - 15t - 36 < 0` for `0 < t < t_-`. -/
theorem lt_tMinus_of_not (t : ℝ) (ht : 0 < t) (h : t < tMinus) : 8 * t ^ 2 - 15 * t - 36 < 0 := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h0 : (4 : ℝ) < Real.sqrt 17 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold tMinus at h
  nlinarith

/-- `3t² + 4t - 48 > 0` for `t > t_+`. -/
theorem tPlus_lt_of (t : ℝ) (h3 : 3 < t) (h : tPlus < t) : 0 < 3 * t ^ 2 + 4 * t - 48 := by
  have h37 : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 37 := Real.sqrt_nonneg _
  unfold tPlus at h
  nlinarith

/-- Below the PPT interval the even block of `ρ_t^{T_A}` has negative determinant. -/
theorem not_posSemidef_ptA_of_lt (t : ℝ) (ht : 0 < t) (h : t < tMinus) :
    ¬ (ptA (rhoT t)).PosSemidef := by
  intro hP
  have hd := (hP.submatrix ![0, 3, 5, 6]).det_nonneg
  rw [ptA_block_even, det_smul, det_blockEven] at hd
  simp only [Fintype.card_fin] at hd
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real] at hd
  have h1 := lt_tMinus_of_not t ht h
  have h2 : 0 < (1 / (7 * (t + 3))) ^ 4 := by positivity
  nlinarith

/-- Above the PPT interval the odd block of `ρ_t^{T_A}` has negative determinant. -/
theorem not_posSemidef_ptA_of_gt (t : ℝ) (ht : 0 < t) (h : tPlus < t) :
    ¬ (ptA (rhoT t)).PosSemidef := by
  intro hP
  have h3 : 3 < t := lt_trans three_lt_tPlus h
  have hd := (hP.submatrix ![1, 2, 4, 7]).det_nonneg
  rw [ptA_block_odd, det_smul, det_blockOdd] at hd
  simp only [Fintype.card_fin] at hd
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real] at hd
  have h1 := tPlus_lt_of t h3 h
  have h2 : 0 < (1 / (7 * (t + 3))) ^ 4 := by positivity
  have h4 : 0 < (t - 3) * (3 * t ^ 2 + 4 * t - 48) := mul_pos (by linarith) h1
  nlinarith


/-- The fully-PPT condition: the partial transposes on each of the three qubits are positive
semidefinite. -/
def IsPPT3 (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  (ptA ρ).PosSemidef ∧ (ptB ρ).PosSemidef ∧ (ptC ρ).PosSemidef

/-- **`thm:ppt3-family`, PPT part (sufficiency).**  For `t_- ≤ t ≤ t_+` the state `ρ_t` is fully
PPT.  Proved by the `LDL*` factorization `ptA_rhoT_eq` and cyclic symmetry. -/
theorem ppt3_family_ppt (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) : IsPPT3 (rhoT t) :=
  ⟨posSemidef_ptA_rhoT t h1 h2, posSemidef_ptB_rhoT t h1 h2, posSemidef_ptC_rhoT t h1 h2⟩

/-- **`thm:ppt3-family`, PPT interval `eq:ppt3-interval`.**  For `t > 0`, `ρ_t` is PPT at all three
single-qubit cuts exactly when `t_- ≤ t ≤ t_+`.  (Outside the interval already the partial
transpose on `A` fails to be positive semidefinite.) -/
theorem ppt3_family_ppt_iff (t : ℝ) (ht : 0 < t) :
    IsPPT3 (rhoT t) ↔ tMinus ≤ t ∧ t ≤ tPlus := by
  refine ⟨fun h => ?_, fun h => ppt3_family_ppt t h.1 h.2⟩
  constructor
  · by_contra hc
    exact not_posSemidef_ptA_of_lt t ht (not_le.mp hc) h.1
  · by_contra hc
    exact not_posSemidef_ptA_of_gt t ht (not_le.mp hc) h.1

/-- **`thm:ppt3-family`, PPT and GME on the interval.**  For `t_- ≤ t ≤ t_+` the state `ρ_t` is a
(positive semidefinite) state which is fully PPT and genuinely multipartite entangled. -/
theorem ppt3_family_ppt_gme (t : ℝ) (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    (rhoT t).PosSemidef ∧ IsPPT3 (rhoT t) ∧ IsGME (rhoT t) :=
  ⟨rhoT_posSemidef t (lt_of_lt_of_le (by norm_num) (three_lt_tMinus.le.trans h1)),
    ppt3_family_ppt t h1 h2, ppt3_family_gme_of_tMinus_le t h1⟩

/-- `t_-` is the root `(15 + 9√17)/16` of `8t² - 15t - 36`. -/
theorem tMinus_root : 8 * tMinus ^ 2 - 15 * tMinus - 36 = 0 := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  unfold tMinus; nlinarith

/-- `t_+` is the root of `3t² + 4t - 48`. -/
theorem tPlus_root : 3 * tPlus ^ 2 + 4 * tPlus - 48 = 0 := by
  have h37 : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  unfold tPlus; nlinarith

/-- `t_- < 10/3`. -/
theorem tMinus_lt_ten_thirds : tMinus < 10 / 3 := by
  have h17 : Real.sqrt 17 < 115 / 27 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold tMinus; linarith

/-- `10/3 < t_+`. -/
theorem ten_thirds_lt_tPlus : 10 / 3 < tPlus := by
  have h : (6 : ℝ) < Real.sqrt 37 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold tPlus; linarith

/-- `t_+ < 2√3`. -/
theorem tPlus_lt_two_sqrt_three : tPlus < 2 * Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : (3 / 2 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h : Real.sqrt 37 < 1 + 3 * Real.sqrt 3 := by
    rw [Real.sqrt_lt' (by positivity)]; nlinarith
  unfold tPlus; linarith

/-- The ordering `3 < t_- < 10/3 < t_+ < 2√3` of the proof of `thm:ppt3-family`. -/
theorem tInterval_order :
    3 < tMinus ∧ tMinus < 10 / 3 ∧ 10 / 3 < tPlus ∧ tPlus < 2 * Real.sqrt 3 :=
  ⟨three_lt_tMinus, tMinus_lt_ten_thirds, ten_thirds_lt_tPlus, tPlus_lt_two_sqrt_three⟩

/-- The explicit member `t = 10/3` is a fully-PPT GME state. -/
theorem ppt3_family_explicit_member_ppt :
    (rhoT (10 / 3)).PosSemidef ∧ IsPPT3 (rhoT (10 / 3)) ∧ IsGME (rhoT (10 / 3)) :=
  ppt3_family_ppt_gme _ tMinus_lt_ten_thirds.le ten_thirds_lt_tPlus.le

end

/-- info: 'FormalResearch.PPTThreeQubit.rhoT_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoT_posSemidef

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_ppt

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_ppt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_ppt_iff

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_ppt_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_ppt_gme

/-- info: 'FormalResearch.PPTThreeQubit.tInterval_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tInterval_order

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_family_explicit_member_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_family_explicit_member_ppt

end FormalResearch.PPTThreeQubit

import FormalResearch.FourQubitEntropy.EnvelopePermReal

/-!
# Equality in the permanent bound, from the Gram data of `Θ`

`perm_class` is the matrix-level core of the equality classification of `prop:fqe-critical-envelope`
(`sextic_identity.tex`): for `Θ` with `Θᵀ Θ = κ² I + b bᵀ`, `|b|² = 1 - κ²`, `det Θ = -κ²`
(that is, singular values `(1, κ, κ)` and negative determinant), `0 ≤ κ ≤ 1`:

* `perm Θ ≥ -(2 + 3κ² + 4κ³)/9`, and
* equality holds iff `CritForm κ Θ`: `Θ = O (κ I + (1-κ) s sᵀ)` with `O` one of the twelve signed cyclic
  permutation matrices whose three signs have product `-1` (`IsSignedCyclic`) and `s ∈ {±1}³/√3`
  (`CubeDiag`).

The cases `κ > 0` (polar decomposition `Θ = O D`, `perm_class_pos`) and `κ = 0` (`Θ = r sᵀ`,
AM–GM, `perm_class_zero`) are treated separately, as in the paper.
-/
namespace FormalResearch.FourQubitEntropy
open Matrix

/-- The equality family in matrix form: `Θ = O (κ I + (1-κ) s sᵀ)` with `O` a signed cyclic permutation
matrix with sign product `-1` and `s ∈ {±1}³/√3`. -/
def CritForm (κ : ℝ) (Θ : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ (O : Matrix (Fin 3) (Fin 3) ℝ) (s : Fin 3 → ℝ), IsSignedCyclic O ∧ CubeDiag s ∧ Θ = O * Dmat κ s

theorem exists_unit_smul (b : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : b ⬝ᵥ b = c ^ 2) :
    ∃ s : Fin 3 → ℝ, s ⬝ᵥ s = 1 ∧ b = c • s := by
  by_cases h0 : c = 0
  · subst h0
    have : b = 0 := by
      funext i
      simp only [dotProduct, Fin.sum_univ_three] at h
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (b 0), sq_nonneg (b 1), sq_nonneg (b 2)]
    exact ⟨![1, 0, 0], by simp [dotProduct, Fin.sum_univ_three], by simp [this]⟩
  · refine ⟨c⁻¹ • b, ?_, ?_⟩
    · simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, h]
      field_simp
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem det_Dmat (κ : ℝ) (s : Fin 3 → ℝ) (hs : s ⬝ᵥ s = 1) : (Dmat κ s).det = κ ^ 2 := by
  have hs' : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1 := by simpa [dotProduct, Fin.sum_univ_three, sq] using hs
  simp only [Dmat, Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul]
  simp
  linear_combination (κ ^ 2 * (1 - κ)) * hs'


/-- `κ = 0`: `Θᵀ Θ = b bᵀ` with `b` a unit vector forces `Θ = r bᵀ`, `r = Θ b`. -/
theorem rank_one_of_gram (Θ : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hb : b ⬝ᵥ b = 1)
    (h : Θᵀ * Θ = Matrix.vecMulVec b b) : Θ = Matrix.vecMulVec (Θ.mulVec b) b := by
  have hPP : Matrix.vecMulVec b b * Matrix.vecMulVec b b = Matrix.vecMulVec b b := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hb, one_smul]
  have hPt : (Matrix.vecMulVec b b)ᵀ = Matrix.vecMulVec b b := by
    ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
  set P := Matrix.vecMulVec b b with hP
  set Z := Θ * (1 - P) with hZ
  have hZ0 : Zᵀ * Z = 0 := by
    rw [hZ, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hPt]
    calc (1 - P) * Θᵀ * (Θ * (1 - P)) = (1 - P) * (Θᵀ * Θ) * (1 - P) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
          rw [h]
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
          abel
  have hZ' : Z = 0 := by
    have h3 : Zᴴ * Z = 0 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hZ0
    exact Matrix.conjTranspose_mul_self_eq_zero.1 h3
  have : Θ * P = Θ := by
    have h2 : Θ * (1 - P) = 0 := hZ'
    rw [Matrix.mul_sub, Matrix.mul_one] at h2
    exact (sub_eq_zero.1 h2).symm
  conv_lhs => rw [← this]
  rw [hP, Matrix.mul_vecMulVec]


theorem perm_of_CritForm {κ : ℝ} {Θ : Matrix (Fin 3) (Fin 3) ℝ} (h : CritForm κ Θ) :
    perm3 Θ = -pmax κ := by
  obtain ⟨O, s, hO, hs, rfl⟩ := h
  exact perm_of_signedCyclic κ O s hO hs

theorem perm_class_zero (Θ : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hb : b ⬝ᵥ b = 1)
    (h : Θᵀ * Θ = Matrix.vecMulVec b b) :
    -pmax 0 ≤ perm3 Θ ∧ (perm3 Θ = -pmax 0 → CritForm 0 Θ) := by
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 → ℝ, Θ = Matrix.vecMulVec r b := ⟨_, rank_one_of_gram Θ b hb h⟩
  subst hr
  have hb' : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1 := by simpa [dotProduct, Fin.sum_univ_three, sq] using hb
  have e : ∀ j, (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2) * b j ^ 2 = b j ^ 2 := by
    intro j
    have := congrFun (congrFun h j) j
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, Fin.sum_univ_three] at this
    linear_combination this
  have hr' : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 := by
    linear_combination e 0 + e 1 + e 2 - (r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 - 1) * hb'
  have hp : perm3 (Matrix.vecMulVec r b) = 6 * (r 0 * r 1 * r 2) * (b 0 * b 1 * b 2) := by
    simp [perm3, Matrix.vecMulVec_apply]; ring
  have pr := amgm3 (sq_nonneg (r 0)) (sq_nonneg (r 1)) (sq_nonneg (r 2)) hr'
  have pb := amgm3 (sq_nonneg (b 0)) (sq_nonneg (b 1)) (sq_nonneg (b 2)) hb'
  set A := (r 0 * r 1 * r 2) ^ 2 with hA
  set B := (b 0 * b 1 * b 2) ^ 2 with hB
  have hA' : 27 * A ≤ 1 := by
    have : A = r 0 ^ 2 * r 1 ^ 2 * r 2 ^ 2 := by rw [hA]; ring
    linarith
  have hB' : 27 * B ≤ 1 := by
    have : B = b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 2 := by rw [hB]; ring
    linarith
  have hA0 : 0 ≤ A := sq_nonneg _
  have hB0 : 0 ≤ B := sq_nonneg _
  have hAB : ((r 0 * r 1 * r 2) * (b 0 * b 1 * b 2)) ^ 2 = A * B := by rw [hA, hB]; ring
  have hAle : A ≤ 1 / 27 := by linarith
  have hBle : B ≤ 1 / 27 := by linarith
  have hle : ((r 0 * r 1 * r 2) * (b 0 * b 1 * b 2)) ^ 2 ≤ (1 / 27) ^ 2 := by
    rw [hAB, sq]; exact mul_le_mul hAle hBle hB0 (by norm_num)
  have habs := abs_le_of_sq_le_sq' hle (by norm_num)
  have hpm : pmax 0 = 2 / 9 := by norm_num [pmax]
  refine ⟨by rw [hp, hpm]; nlinarith [habs.1], fun heq => ?_⟩
  rw [hp, hpm] at heq
  have hprod : (r 0 * r 1 * r 2) * (b 0 * b 1 * b 2) = -(1 / 27) := by linarith
  have hAB' : A * B = 1 / 729 := by rw [← hAB, hprod]; norm_num
  have hA1 : 27 * A = 1 := by
    have := mul_le_mul_of_nonneg_left hBle hA0
    linarith
  have hB1 : 27 * B = 1 := by
    have := mul_le_mul_of_nonneg_left hAle hB0
    linarith
  obtain ⟨r0, r1, r2⟩ := amgm3_eq (sq_nonneg (r 0)) (sq_nonneg (r 1)) (sq_nonneg (r 2)) hr'
    (by rw [hA] at hA1; linarith [show (r 0 * r 1 * r 2) ^ 2 = r 0 ^ 2 * r 1 ^ 2 * r 2 ^ 2 by ring])
  obtain ⟨b0, b1, b2⟩ := amgm3_eq (sq_nonneg (b 0)) (sq_nonneg (b 1)) (sq_nonneg (b 2)) hb'
    (by rw [hB] at hB1; linarith [show (b 0 * b 1 * b 2) ^ 2 = b 0 ^ 2 * b 1 ^ 2 * b 2 ^ 2 by ring])
  have hbq : ∀ i, b i ^ 2 = 1 / 3 := by intro i; fin_cases i <;> simp [b0, b1, b2]
  have hrq : ∀ i, r i ^ 2 = 1 / 3 := by intro i; fin_cases i <;> simp [r0, r1, r2]
  have hbcube : CubeDiag b := by
    intro i
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have : (b i * Real.sqrt 3) ^ 2 = 1 := by rw [mul_pow, hbq, h3]; norm_num
    exact pm1 this
  refine ⟨Matrix.diagonal (fun i => 3 * r i * b i), b, ⟨0, fun i => 3 * r i * b i, ?_, ?_, ?_⟩, hbcube, ?_⟩
  · intro i
    apply pm1
    have : (3 * r i * b i) ^ 2 = 9 * (r i ^ 2 * b i ^ 2) := by ring
    rw [this, hrq, hbq]; norm_num
  · have : (3 * r 0 * b 0) * (3 * r 1 * b 1) * (3 * r 2 * b 2) = 27 * ((r 0 * r 1 * r 2) * (b 0 * b 1 * b 2)) := by ring
    rw [this, hprod]; norm_num
  · intro i j
    simp only [Matrix.diagonal_apply, add_zero]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    simp [Dmat, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
    have := hbq i
    linear_combination (-(r i * b j) * 3) * this


theorem perm_class_pos (Θ : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (κ : ℝ) (hk0 : 0 < κ) (hk1 : κ ≤ 1)
    (h1 : Θᵀ * Θ = (κ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.vecMulVec b b)
    (h2 : b ⬝ᵥ b = 1 - κ ^ 2) (h3 : Θ.det = -κ ^ 2) :
    -pmax κ ≤ perm3 Θ ∧ (perm3 Θ = -pmax κ → CritForm κ Θ) := by
  obtain ⟨s, hs, hbs⟩ := exists_unit_smul b (Real.sqrt (1 - κ ^ 2)) (Real.sqrt_nonneg _)
    (by rw [h2, Real.sq_sqrt (by nlinarith)])
  have hbb : Matrix.vecMulVec b b = (1 - κ ^ 2) • Matrix.vecMulVec s s := by
    rw [hbs]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
    have : Real.sqrt (1 - κ ^ 2) ^ 2 = 1 - κ ^ 2 := Real.sq_sqrt (by nlinarith)
    linear_combination (s i * s j) * this
  have hD2 : Dmat κ s * Dmat κ s = Θᵀ * Θ := by
    rw [h1, hbb]
    unfold Dmat
    rw [sc_mul _ _ _ _ s hs]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set Di : Matrix (Fin 3) (Fin 3) ℝ := κ⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ⁻¹) • Matrix.vecMulVec s s with hDi
  have hDDi : Dmat κ s * Di = 1 := by
    unfold Dmat
    rw [hDi, sc_mul _ _ _ _ s hs]
    have e1 : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hk0.ne'
    have e2 : κ * (1 - κ⁻¹) + κ⁻¹ * (1 - κ) + (1 - κ) * (1 - κ⁻¹) = 0 := by field_simp; ring
    rw [e1, e2]; simp
  have hDiD : Di * Dmat κ s = 1 := mul_eq_one_comm.1 hDDi
  have hDit : Diᵀ = Di := sc_transpose _ _ s
  set O := Θ * Di with hO
  have hΘO : Θ = O * Dmat κ s := by rw [hO, Matrix.mul_assoc, hDiD, Matrix.mul_one]
  have hOO : Oᵀ * O = 1 := by
    rw [hO, Matrix.transpose_mul, hDit]
    calc Di * Θᵀ * (Θ * Di) = Di * (Θᵀ * Θ) * Di := by simp only [Matrix.mul_assoc]
      _ = (Di * Dmat κ s) * (Dmat κ s * Di) := by rw [← hD2]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDiD, hDDi, Matrix.one_mul]

  have hOO' : O * Oᵀ = 1 := mul_eq_one_comm.1 hOO
  have hdetO : O.det = -1 := by
    have := congrArg Matrix.det hΘO
    rw [Matrix.det_mul, det_Dmat κ s hs, h3] at this
    have hk2 : κ ^ 2 ≠ 0 := by positivity
    have : (O.det + 1) * κ ^ 2 = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hk2
    linarith
  obtain ⟨hineq, heq⟩ := main_Os O s κ hOO' hs hdetO hk0 hk1
  rw [← hΘO] at hineq heq
  refine ⟨hineq, fun hp => ?_⟩
  obtain ⟨hcyc, hsq⟩ := heq hp
  rcases lt_or_eq_of_le hk1 with hlt | hone
  · refine ⟨O, s, hcyc, ?_, hΘO⟩
    intro i
    have h3' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have : (s i * Real.sqrt 3) ^ 2 = 1 := by rw [mul_pow, hsq hlt i, h3']; norm_num
    exact pm1 this
  · refine ⟨O, fun _ => (Real.sqrt 3)⁻¹, hcyc, ?_, ?_⟩
    · intro i
      have : Real.sqrt 3 ≠ 0 := by positivity
      left; simp [this]
    · rw [hΘO]
      subst hone
      unfold Dmat
      simp

theorem perm_class (Θ : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (κ : ℝ) (hk0 : 0 ≤ κ) (hk1 : κ ≤ 1)
    (h1 : Θᵀ * Θ = (κ ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.vecMulVec b b)
    (h2 : b ⬝ᵥ b = 1 - κ ^ 2) (h3 : Θ.det = -κ ^ 2) :
    -pmax κ ≤ perm3 Θ ∧ (perm3 Θ = -pmax κ ↔ CritForm κ Θ) := by
  have key : -pmax κ ≤ perm3 Θ ∧ (perm3 Θ = -pmax κ → CritForm κ Θ) := by
    rcases lt_or_eq_of_le hk0 with hpos | hz
    · exact perm_class_pos Θ b κ hpos hk1 h1 h2 h3
    · subst hz
      have h1' : Θᵀ * Θ = Matrix.vecMulVec b b := by simpa using h1
      exact perm_class_zero Θ b (by simpa using h2) h1'
  exact ⟨key.1, ⟨key.2, perm_of_CritForm⟩⟩

end FormalResearch.FourQubitEntropy

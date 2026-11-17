module

public import FormalResearch.MatrixAnalysis.MaskedFrobenius

/-!
# Spectral-residual certificate (Weyl P5/M7, Theorem 1 of `m7_m1_global_criteria.md`)

Source: `Weyl/P5/notes/m7_m1_global_criteria.md`, Theorem 1 (eqs. (2.2), (2.3)) (PR 250, head
`cfad461d2`).  Let `H` be a real symmetric `n × n` matrix, `U` a real orthogonal matrix whose columns
`u_d` satisfy `H u_d = λ_d u_d`, `gap_d > 0` with `gap_d ≤ |λ_ℓ - λ_d|` for `ℓ ≠ d` (so the spectrum
is simple), and `G` any real matrix with nonzero columns `g_d`.  Put `t_d = ‖g_d‖`, `v_d = g_d/t_d`,
`r_d = (H - λ_d) v_d`, `η² = ∑_d ‖r_d‖²/gap_d²` and let `ε ≥ |t_d - 1|` for all `d`.  With the sign
`σ_d = +1` if `⟨u_d, v_d⟩ ≥ 0` and `-1` otherwise,

`‖G - U diag σ‖_{2→2} ≤ (1 + ε) √2 η + ε`        (2.3)

(`spectral_residual_certificate`, with `‖·‖` the Mathlib `L2` operator norm), and the Frobenius form
`‖V - U diag σ‖_F² ≤ 2 η²` (`spectral_residual_frobenius`).

Note on the statement: the hypothesis `η < 1` of the note is needed only to make `σ_d` the sign of a
*nonzero* overlap (`⟨u_d, v_d⟩ ≠ 0`); the inequality holds as stated with the convention for
`σ_d` above, with no hypothesis on `η`.  Claim class: proved.

Not formalised: (2.4), the Racah instantiation (`gap_d ≥ h²(d+1)` from the exact quadratic spectrum),
Proposition 2 (certification of physical signs from a bulk anchor; the single-anchor statement of
Theorem 2 is `sign_anchor` in `SignLocking`).  Theorem 2 itself (dual-Egorov sign locking) is
`FormalResearch.MatrixAnalysis.signLocking`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sqrt_sum_sq_add_le' (x y : ι → ℝ) :
    √(∑ i, (x i + y i) ^ 2) ≤ √(∑ i, x i ^ 2) + √(∑ i, y i ^ 2) := by
  have := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simpa [EuclideanSpace.norm_eq] using this

/-- Orthogonal matrices preserve the Euclidean norm (`Uᵀ U = 1`). -/
theorem sq_sum_mulVec_of_orth {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1) (x : ι → ℝ) :
    ∑ i, (U *ᵥ x) i ^ 2 = ∑ j, x j ^ 2 := by
  have h1 : ∑ i, (U *ᵥ x) i ^ 2 = (U *ᵥ x) ⬝ᵥ (U *ᵥ x) := by
    simp [dotProduct, sq]
  have h2 : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ ((Uᵀ * U) *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec x Uᵀ, vecMul_transpose]
  have h3 : x ⬝ᵥ ((Uᵀ * U) *ᵥ x) = ∑ j, x j ^ 2 := by
    rw [hU, one_mulVec]; simp [dotProduct, sq]
  rw [h1, h2, h3]

theorem transpose_mul_eq_one_of_orth {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1) : U * Uᵀ = 1 :=
  mul_eq_one_comm.mp hU

section Column

variable {H U : Matrix ι ι ℝ} {lam : ι → ℝ}

omit [DecidableEq ι] in
/-- `Uᵀ H x = Λ Uᵀ x` for symmetric `H` and eigen-columns `U`. -/
theorem transpose_mulVec_apply (hH : Hᵀ = H)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) (x : ι → ℝ) (l : ι) :
    (Uᵀ *ᵥ (H *ᵥ x)) l = lam l * (Uᵀ *ᵥ x) l := by
  have h1 : ∀ y : ι → ℝ, (Uᵀ *ᵥ y) l = (fun i => U i l) ⬝ᵥ y := fun y => by
    simp [mulVec, dotProduct]
  have h2 : (fun i => U i l) ᵥ* H = H *ᵥ (fun i => U i l) := by
    conv_lhs => rw [← hH]
    exact vecMul_transpose _ _
  rw [h1, h1, dotProduct_mulVec, h2, heig l, smul_dotProduct, smul_eq_mul]

/-- Parseval for the coordinates `Uᵀ x`. -/
theorem sum_sq_transpose_mulVec (hU : Uᵀ * U = 1) (x : ι → ℝ) :
    ∑ l, (Uᵀ *ᵥ x) l ^ 2 = ∑ i, x i ^ 2 :=
  sq_sum_mulVec_of_orth (U := Uᵀ) (by rw [transpose_transpose]; exact mul_eq_one_comm.mp hU) x

/-- The residual in spectral coordinates. -/
theorem residual_coords (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) (x : ι → ℝ) (d : ι) :
    ∑ i, ((H *ᵥ x) i - lam d * x i) ^ 2 = ∑ l, ((lam l - lam d) * (Uᵀ *ᵥ x) l) ^ 2 := by
  have h : ∀ l, (Uᵀ *ᵥ (fun i => (H *ᵥ x) i - lam d * x i)) l = (lam l - lam d) * (Uᵀ *ᵥ x) l := by
    intro l
    have e : (fun i => (H *ᵥ x) i - lam d * x i) = (H *ᵥ x) - lam d • x := by
      funext i; simp
    rw [e, mulVec_sub, mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [transpose_mulVec_apply hH heig]; ring
  rw [← sum_sq_transpose_mulVec hU]
  exact sum_congr rfl fun l _ => by rw [h l]

/-- **Column estimate.**  For a unit vector `v`, `σ = ±1` with `σ ⟨u_d, v⟩ ≥ 0` and a gap
`g ≤ |λ_ℓ - λ_d|` (`ℓ ≠ d`): `g² ‖v - σ u_d‖² ≤ 2 ‖(H - λ_d) v‖²`. -/
theorem column_estimate (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) {d : ι} {g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ l, l ≠ d → g ≤ |lam l - lam d|) {v : ι → ℝ} (hv : ∑ i, v i ^ 2 = 1) {σ : ℝ}
    (hσ : σ ^ 2 = 1) (hσc : 0 ≤ σ * (Uᵀ *ᵥ v) d) :
    g ^ 2 * ∑ i, (v i - σ * U i d) ^ 2 ≤ 2 * ∑ i, ((H *ᵥ v) i - lam d * v i) ^ 2 := by
  set c : ι → ℝ := Uᵀ *ᵥ v with hc
  have hsum : ∑ l, c l ^ 2 = 1 := by rw [hc, sum_sq_transpose_mulVec hU, hv]
  have hud : ∑ i, U i d ^ 2 = 1 := by
    have := congrFun (congrFun hU d) d
    simpa [Matrix.mul_apply, sq] using this
  have hcd : c d = ∑ i, U i d * v i := by simp [hc, mulVec, dotProduct]
  have hexp : ∑ i, (v i - σ * U i d) ^ 2 = 2 - 2 * (σ * c d) := by
    have : ∀ i, (v i - σ * U i d) ^ 2 = v i ^ 2 - 2 * σ * (U i d * v i) + σ ^ 2 * U i d ^ 2 := by
      intro i; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hv, hud, hσ, hcd]
    ring
  set W := ∑ l ∈ univ.erase d, c l ^ 2 with hW
  have hsplit : c d ^ 2 + W = 1 := by
    have := add_sum_erase univ (fun l => c l ^ 2) (mem_univ d)
    rw [hW]; linarith
  have hcd2 : (σ * c d) ^ 2 = c d ^ 2 := by rw [mul_pow, hσ, one_mul]
  have hle1 : σ * c d ≤ 1 := by
    have : (σ * c d) ^ 2 ≤ 1 := by rw [hcd2]; nlinarith [sq_nonneg W, hW ▸ sum_nonneg (fun l (_ : l ∈ univ.erase d) => sq_nonneg (c l))]
    nlinarith
  have hW0 : 0 ≤ W := sum_nonneg fun l _ => sq_nonneg _
  have hclose : ∑ i, (v i - σ * U i d) ^ 2 ≤ 2 * W := by
    rw [hexp]
    nlinarith
  have hres : g ^ 2 * W ≤ ∑ i, ((H *ᵥ v) i - lam d * v i) ^ 2 := by
    rw [residual_coords hH hU heig v d, hW, mul_sum]
    calc ∑ l ∈ univ.erase d, g ^ 2 * c l ^ 2
        ≤ ∑ l ∈ univ.erase d, ((lam l - lam d) * c l) ^ 2 := by
          refine sum_le_sum fun l hl => ?_
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (by
            rw [← sq_abs (lam l - lam d)]
            exact pow_le_pow_left₀ hg (hgap l (mem_erase.mp hl).1) 2) (sq_nonneg _)
      _ ≤ ∑ l, ((lam l - lam d) * c l) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => sq_nonneg _
  calc g ^ 2 * ∑ i, (v i - σ * U i d) ^ 2 ≤ g ^ 2 * (2 * W) :=
        mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
    _ = 2 * (g ^ 2 * W) := by ring
    _ ≤ _ := by linarith

end Column

section Certificate

variable {H U : Matrix ι ι ℝ} {lam : ι → ℝ}

/-- The Euclidean norm `t_d` of the `d`-th column of `G`. -/
noncomputable def colNorm (G : Matrix ι ι ℝ) (d : ι) : ℝ := √(∑ i, G i d ^ 2)

/-- The normalised column `v_d = g_d / t_d`. -/
noncomputable def unitCol (G : Matrix ι ι ℝ) (d : ι) : ι → ℝ := fun i => G i d / colNorm G d

/-- The sign `σ_d` of the overlap `⟨u_d, v_d⟩` (`+1` when it is nonnegative). -/
noncomputable def overlapSign (U G : Matrix ι ι ℝ) (d : ι) : ℝ :=
  if 0 ≤ (Uᵀ *ᵥ unitCol G d) d then 1 else -1

/-- The squared residual budget `η² = ∑_d ‖(H - λ_d) v_d‖² / gap_d²`. -/
noncomputable def residualBudget (H : Matrix ι ι ℝ) (lam g : ι → ℝ) (G : Matrix ι ι ℝ) : ℝ :=
  ∑ d, (∑ i, ((H *ᵥ unitCol G d) i - lam d * unitCol G d i) ^ 2) / g d ^ 2

omit [DecidableEq ι] in
theorem overlapSign_sq (U G : Matrix ι ι ℝ) (d : ι) : overlapSign U G d ^ 2 = 1 := by
  unfold overlapSign; split_ifs <;> norm_num

omit [DecidableEq ι] in
theorem overlapSign_overlap (U G : Matrix ι ι ℝ) (d : ι) :
    0 ≤ overlapSign U G d * (Uᵀ *ᵥ unitCol G d) d := by
  unfold overlapSign; split_ifs with h
  · simpa using h
  · have := not_le.mp h; linarith

omit [DecidableEq ι] in
theorem unitCol_sq (G : Matrix ι ι ℝ) {d : ι} (h : 0 < ∑ i, G i d ^ 2) :
    ∑ i, unitCol G d i ^ 2 = 1 := by
  unfold unitCol colNorm
  have h2 : (√(∑ i, G i d ^ 2)) ^ 2 = ∑ i, G i d ^ 2 := Real.sq_sqrt h.le
  have h3 : 0 < √(∑ i, G i d ^ 2) := Real.sqrt_pos.mpr h
  simp only [div_pow, ← sum_div, h2]
  exact div_self h.ne'

/-- Frobenius form of Theorem 1: `‖V - U diag σ‖_F² ≤ 2 η²`. -/
theorem spectral_residual_frobenius (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) {g : ι → ℝ}
    (hg0 : ∀ d, 0 < g d) (hgap : ∀ d l, l ≠ d → g d ≤ |lam l - lam d|) (G : Matrix ι ι ℝ)
    (ht : ∀ d, 0 < ∑ i, G i d ^ 2) :
    ∑ d, ∑ i, (unitCol G d i - overlapSign U G d * U i d) ^ 2 ≤ 2 * residualBudget H lam g G := by
  unfold residualBudget
  rw [mul_sum]
  refine sum_le_sum fun d _ => ?_
  have := column_estimate hH hU heig (hg0 d).le (hgap d) (unitCol_sq G (ht d))
    (overlapSign_sq U G d) (overlapSign_overlap U G d)
  have hg2 := sq_pos_of_pos (hg0 d)
  rw [← mul_div_assoc, le_div_iff₀ hg2]
  linarith

/-- **Theorem 1** (spectral-residual certificate), eq. (2.3): with `σ_d` the overlap signs,
`‖G - U diag σ‖_{2→2} ≤ (1 + ε) √2 η + ε`, `η² = ∑_d ‖(H - λ_d) v_d‖²/gap_d²`, `ε ≥ |t_d - 1|`. -/
theorem spectral_residual_certificate (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) {g : ι → ℝ}
    (hg0 : ∀ d, 0 < g d) (hgap : ∀ d l, l ≠ d → g d ≤ |lam l - lam d|) (G : Matrix ι ι ℝ)
    (ht : ∀ d, 0 < ∑ i, G i d ^ 2) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ d, |colNorm G d - 1| ≤ ε) :
    ‖G - U * diagonal (overlapSign U G)‖ ≤
      (1 + ε) * √2 * √(residualBudget H lam g G) + ε := by
  set η := √(residualBudget H lam g G) with hη
  have hbud : 0 ≤ residualBudget H lam g G :=
    sum_nonneg fun d _ => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη2 : η ^ 2 = residualBudget H lam g G := Real.sq_sqrt hbud
  set σ := overlapSign U G with hσ
  set t := colNorm G with ht'
  have ht0 : ∀ d, 0 ≤ t d := fun d => Real.sqrt_nonneg _
  have ht1 : ∀ d, t d ≤ 1 + ε := fun d => by have := (abs_le.mp (hε d)).2; linarith
  set Dm : Matrix ι ι ℝ := Matrix.of fun i d => unitCol G d i - σ d * U i d with hDm
  have hfrob : frobSq Dm ≤ 2 * η ^ 2 := by
    rw [hη2]
    have := spectral_residual_frobenius hH hU heig hg0 hgap G ht
    unfold frobSq
    rw [sum_comm]
    simpa [hDm] using this
  have hC : 0 ≤ (1 + ε) * √2 * η + ε := by positivity
  apply l2_opNorm_le_of_sq _ hC
  intro x
  -- decomposition
  have hdecomp : ∀ i, ((G - U * diagonal σ) *ᵥ x) i =
      (Dm *ᵥ (fun d => t d * x d)) i + (U *ᵥ (fun d => σ d * (t d - 1) * x d)) i := by
    intro i
    simp only [mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_diagonal, hDm, Matrix.of_apply,
      ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    have hGd : G i d = unitCol G d i * t d := by
      unfold unitCol
      have : colNorm G d ≠ 0 := (Real.sqrt_pos.mpr (ht d)).ne'
      field_simp
      rfl
    rw [hGd]; ring
  set X := √(∑ j, x j ^ 2) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  -- first term
  have hA : √(∑ i, (Dm *ᵥ (fun d => t d * x d)) i ^ 2) ≤ √2 * η * ((1 + ε) * X) := by
    have h1 := sq_mulVec_le_frobSq Dm (fun d => t d * x d)
    have h2 : ∑ d, (t d * x d) ^ 2 ≤ ((1 + ε) * X) ^ 2 := by
      rw [mul_pow, hX2, mul_sum]
      refine sum_le_sum fun d _ => ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht0 d) (ht1 d) 2) (sq_nonneg _)
    calc √(∑ i, (Dm *ᵥ (fun d => t d * x d)) i ^ 2)
        ≤ √(frobSq Dm * ∑ d, (t d * x d) ^ 2) := Real.sqrt_le_sqrt h1
      _ ≤ √((2 * η ^ 2) * ((1 + ε) * X) ^ 2) := Real.sqrt_le_sqrt
          (mul_le_mul hfrob h2 (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
      _ = √2 * η * ((1 + ε) * X) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq hη0, Real.sqrt_sq (by positivity)]
  -- second term
  have hB : √(∑ i, (U *ᵥ (fun d => σ d * (t d - 1) * x d)) i ^ 2) ≤ ε * X := by
    rw [sq_sum_mulVec_of_orth hU]
    have : ∑ d, (σ d * (t d - 1) * x d) ^ 2 ≤ (ε * X) ^ 2 := by
      rw [mul_pow, hX2, mul_sum]
      refine sum_le_sum fun d _ => ?_
      have : (σ d * (t d - 1) * x d) ^ 2 = (t d - 1) ^ 2 * x d ^ 2 := by
        rw [mul_pow, mul_pow, overlapSign_sq U G d]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by
        rw [← sq_abs (t d - 1)]; exact pow_le_pow_left₀ (abs_nonneg _) (hε d) 2) (sq_nonneg _)
    calc _ ≤ √((ε * X) ^ 2) := Real.sqrt_le_sqrt this
      _ = ε * X := Real.sqrt_sq (by positivity)
  have hmink := sqrt_sum_sq_add_le' (fun i => (Dm *ᵥ (fun d => t d * x d)) i)
    (fun i => (U *ᵥ (fun d => σ d * (t d - 1) * x d)) i)
  have hsq : ∑ i, ((G - U * diagonal σ) *ᵥ x) i ^ 2 ≤ (((1 + ε) * √2 * η + ε) * X) ^ 2 := by
    have e : ∑ i, ((G - U * diagonal σ) *ᵥ x) i ^ 2 = ∑ i, ((Dm *ᵥ (fun d => t d * x d)) i +
        (U *ᵥ (fun d => σ d * (t d - 1) * x d)) i) ^ 2 := sum_congr rfl fun i _ => by rw [hdecomp i]
    rw [e]
    have hle : √(∑ i, ((Dm *ᵥ (fun d => t d * x d)) i +
        (U *ᵥ (fun d => σ d * (t d - 1) * x d)) i) ^ 2) ≤ ((1 + ε) * √2 * η + ε) * X := by
      calc _ ≤ _ := hmink
        _ ≤ √2 * η * ((1 + ε) * X) + ε * X := add_le_add hA hB
        _ = _ := by ring
    exact (Real.sqrt_le_iff.mp hle).2
  rw [mul_pow, hX2] at hsq
  exact hsq

/-- info: 'FormalResearch.MatrixAnalysis.spectral_residual_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spectral_residual_certificate

/-- info: 'FormalResearch.MatrixAnalysis.spectral_residual_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spectral_residual_frobenius

end Certificate

end FormalResearch.MatrixAnalysis

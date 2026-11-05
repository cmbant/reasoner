module

public import FormalResearch.PPTThreeQubit.Coexistence
public import FormalResearch.PPTThreeQubit.FamilyPPT
public import FormalResearch.PPTThreeQubit.CoexistencePPTData

/-!
# Strict PPT for `thm:ppt3-phase-coexistence` and `prop:ppt3-exposed-transition`

Source: `QI/hidden_entanglement/ppt_three_qubit/phase_coexistence.tex`
(`thm:ppt3-phase-coexistence`, `prop:ppt3-exposed-transition`; the exact data are those of
`QI/hidden_entanglement/code/verify_ppt3_support_geometry.py`, PG-2, PG-4).
Complements `Coexistence.lean`, which has the biseparable/GME clauses.

Method (exact algebra, no numerics, no Sylvester minors).  Elements `a + bω` of `ℚ(ω)` are the pairs
`(a, b) : ℚ × ℚ` (`QW`), with the explicit product `qmul` and conjugation `qconj`; `cwq` embeds them
in `ℂ` and respects sums, products and `star`.  The matrices `σ_BS = B X_BS B†`, `σ_∂ = B X_∂ B†`
(and `ρ_{10/3}`, and `σ(-1/200)`) are tabulated in `ℚ(ω)` (`sigq`), their partial transposes
`ptq`; for each of them an explicit `LDL*` factorization with positive pivots of `M - c I`
(generated data in `CoexistencePPTData.lean` by `gen_coex_ppt.py`, re-checked here by
`decide +kernel`) shows
`M ⪰ c I` (`Dominates`).  The cyclic shift fixes the states, so one cut suffices
(`PartialTranspose.lean`).  The line is handled by convexity: `ptA σ(t)` is affine in `t`, so
`σ(t)` is a convex combination of the three tabulated endpoints `σ(-1/200)`, `σ(0) = σ_∂`,
`σ(1) = σ_BS`, all `⪰ I/400` — no `‖Δ‖₂` bound is needed.

Covered (all proved):
* `σ_BS`, `σ_∂`, every `σ(t)` and `ρ_{10/3}` are invariant under the cyclic shift
  (`sigmaBS_cycShift`, `sigmaD_cycShift`, `sigmaLine_cycShift`);
* `σ_BS^{T_c} ⪰ I/400`, `σ_∂^{T_c} ⪰ I/300`, `ρ_{10/3}^{T_c} ⪰ I/2000`, hence all three partial
  transposes are positive definite (`sigmaBS_strict_ppt`, `sigmaD_strict_ppt`,
  `rhoT_ten_thirds_strict_ppt`);
* for `-1/200 ≤ t ≤ 1`: `σ(t)^{T_c} ⪰ I/400` for `c ∈ {A, B, C}` (`exposed_line_fully_ppt`), and
  `X_∂ + tX_Δ ⪰ I/400`, so `σ(t) = B (X_∂ + tX_Δ) B†` is positive semidefinite
  (`exposed_line_coefficient`).  `X_BS ≻ 0`, `X_∂ ⪰ I/100`.
* `ppt3_phase_coexistence_full`, `ppt3_exposed_transition_full`: the clauses of the two
  statements together with the biseparable/GME clauses of `Coexistence.lean`.

Deviations / not covered.  The paper bounds `σ(t)^{T_c} ≻ I/1200` for `t ≤ 0` through
`‖Δ‖₂² < 1/4`; here the stronger `⪰ I/400` on the whole line comes from convexity, and `‖Δ‖₂` is
not used.  The rank-five and rank-profile `(5,8,8,8)` statements and the "same cut-product curves"
clause are not formalised (positive definiteness of the coefficient matrices, with `B†B = diag(4,1,3,3,3)`
of `Coexistence.lean`, is the algebraic content of rank five, but a rank statement is not made).
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix ComplexOrder

/-! ### Arithmetic in `ℚ(ω)` -/

/-- Product in `ℚ(ω)` of `a + bω` and `c + dω`, using `ω² = -1 - ω`. -/
def qmul (p q : QW) : QW := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1 - p.2 * q.2)

/-- Complex conjugation in `ℚ(ω)`: `conj (a + bω) = a + bω² = (a - b) - bω`. -/
def qconj (p : QW) : QW := (p.1 - p.2, -p.2)

/-- Multiplication of `a + bω` by a rational. -/
def qsmul (d : ℚ) (p : QW) : QW := (d * p.1, d * p.2)

noncomputable section

/-- The embedding `ℚ(ω) → ℂ`, `(a, b) ↦ a + bω`, as an additive homomorphism. -/
def cwq : QW →+ ℂ where
  toFun p := (p.1 : ℂ) + (p.2 : ℂ) * ω
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring

theorem cwq_apply (p : QW) : cwq p = (p.1 : ℂ) + (p.2 : ℂ) * ω := rfl

theorem cwq_mul (p q : QW) : cwq (qmul p q) = cwq p * cwq q := by
  simp only [cwq_apply, qmul]
  push_cast
  linear_combination (-((p.2 : ℂ) * q.2)) * ω_sq_add_ω_add_one

theorem cwq_conj (p : QW) : cwq (qconj p) = star (cwq p) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have hs : star (p.1 : ℂ) = p.1 := Complex.conj_ofReal _
  have hs2 : star (p.2 : ℂ) = p.2 := Complex.conj_ofReal _
  simp only [cwq_apply, qconj, star_add, star_mul', hs, hs2, star_ω, h2]
  push_cast
  ring

theorem cwq_smul (d : ℚ) (p : QW) : cwq (qsmul d p) = (d : ℂ) * cwq p := by
  simp only [cwq_apply, qsmul]; push_cast; ring

theorem cwq_rat (r : ℚ) : cwq ((r, 0) : QW) = (r : ℂ) := by simp [cwq_apply]

/-! ### Tabulated matrices -/

/-- The table of `B X B†` for a table `X` of a `5 × 5` matrix. -/
def sigq (X : Fin 5 → Fin 5 → QW) (i j : Fin 8) : QW :=
  ∑ b, qmul (∑ a, qmul (Bq i a) (X a b)) (qconj (Bq j b))

/-- The partial transpose on `A` of a table (same index formula as `ptA`). -/
def ptq (T : Fin 8 → Fin 8 → QW) (i j : Fin 8) : QW :=
  T ⟨4 * (j.val / 4) + i.val % 4, by omega⟩ ⟨4 * (i.val / 4) + j.val % 4, by omega⟩

theorem Bs_apply (i : Fin 8) (a : Fin 5) : Bs 1 i a = cwq (Bq i a) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  fin_cases i <;> fin_cases a <;>
    simp [Bs, bCols, uVec, vVec, wVec, eVec, oVec, Bq, cwq_apply] <;> exact h2


theorem Bs_apply' : Bs 1 = Matrix.of fun i a => cwq (Bq i a) := by
  ext i a; exact Bs_apply i a

/-- `B X B†` computed entrywise in `ℚ(ω)`. -/
theorem BXBH_apply (X : Fin 5 → Fin 5 → QW) (Xm : Matrix (Fin 5) (Fin 5) ℂ)
    (h : ∀ a b, Xm a b = cwq (X a b)) (i j : Fin 8) :
    (Bs 1 * Xm * (Bs 1)ᴴ) i j = cwq (sigq X i j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Bs_apply, h, sigq, map_sum, cwq_mul,
    cwq_conj]

theorem XBS_apply (a b : Fin 5) : XBS a b = cwq (XBq a b) := by
  fin_cases a <;> fin_cases b <;> simp [XBS, XBq, cwq_apply] <;> norm_num

theorem Xd_apply (a b : Fin 5) : Xd a b = cwq (XDq a b) := by
  fin_cases a <;> fin_cases b <;> simp [Xd, XDq, cwq_apply] <;> norm_num

theorem Xt_ten_thirds_apply (a b : Fin 5) : Xt (10 / 3) a b = cwq (XGq a b) := by
  fin_cases a <;> fin_cases b <;> simp [Xt, XGq, cwq_apply] <;> norm_num

theorem sigmaBS_apply (i j : Fin 8) : sigmaBS i j = cwq (sigq XBq i j) :=
  BXBH_apply XBq XBS XBS_apply i j

theorem sigmaD_apply (i j : Fin 8) : sigmaD i j = cwq (sigq XDq i j) :=
  BXBH_apply XDq Xd Xd_apply i j

theorem rhoG_apply (i j : Fin 8) : rhoT (10 / 3) i j = cwq (sigq XGq i j) :=
  BXBH_apply XGq (Xt (10 / 3)) Xt_ten_thirds_apply i j

/-! ### `LDL*` certificates: `M ⪰ c I` -/

/-- `M ⪰ c I`, i.e. `M - c I` is positive semidefinite. -/
def Dominates {n : ℕ} (c : ℚ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (M - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef

/-- An explicit `LDL*` factorization `T - c I = ∑ₖ dₖ |lₖ⟩⟨lₖ|` with `dₖ ≥ 0`, in `ℚ(ω)`, gives
`T ⪰ c I`. -/
theorem dominates_of_ldl {n : ℕ} (T : Fin n → Fin n → QW) (c : ℚ) (d : Fin n → ℚ)
    (L : Fin n → Fin n → QW) (hd : ∀ k, 0 ≤ d k)
    (h : ∀ i j, T i j = (if i = j then ((c : ℚ), (0 : ℚ)) else ((0 : ℚ), (0 : ℚ))) +
      ∑ k, qsmul (d k) (qmul (L k i) (qconj (L k j)))) :
    Dominates c (Matrix.of fun i j => cwq (T i j)) := by
  have key : (Matrix.of fun i j => cwq (T i j)) - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ∑ k, ((d k : ℝ) : ℂ) • vecMulVec (fun i => cwq (L k i)) (star fun i => cwq (L k i)) := by
    ext i j
    rw [Matrix.sub_apply, of_apply, h i j, map_add, map_sum, Matrix.sum_apply]
    simp only [cwq_smul, cwq_mul, cwq_conj, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Matrix.one_apply, Complex.ofReal_ratCast]
    by_cases hij : i = j <;> simp [hij, cwq_rat]
  unfold Dominates
  rw [key]
  refine posSemidef_sum _ fun k _ => (posSemidef_vecMulVec_self_star _).smul ?_
  exact Complex.zero_le_real.mpr (by exact_mod_cast hd k)

theorem posDef_cSmul_one (n : ℕ) {c : ℚ} (hc : 0 < c) :
    ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  rw [Matrix.smul_one_eq_diagonal]
  refine Matrix.PosDef.diagonal fun _ => ?_
  rw [← Complex.ofReal_ratCast]
  exact Complex.zero_lt_real.mpr (by exact_mod_cast hc)

theorem Dominates.posDef {n : ℕ} {c : ℚ} {M : Matrix (Fin n) (Fin n) ℂ} (hc : 0 < c)
    (h : Dominates c M) : M.PosDef := by
  simpa using Matrix.PosDef.posSemidef_add h (posDef_cSmul_one n hc)

theorem Dominates.mono {n : ℕ} {c c' : ℚ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Dominates c M)
    (hc : c' ≤ c) : Dominates c' M := by
  have h1 : (((c - c' : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal]
    refine Matrix.PosSemidef.diagonal fun _ => ?_
    simp only [Pi.zero_apply]
    rw [← Complex.ofReal_ratCast]
    exact Complex.zero_le_real.mpr (by exact_mod_cast sub_nonneg.mpr hc)
  have e : M - (c' : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      (M - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((c - c' : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  unfold Dominates
  rw [e]
  exact h.add h1

theorem Dominates.submatrix {n : ℕ} {c : ℚ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Dominates c M)
    {f : Fin n → Fin n} (hf : Function.Injective f) : Dominates c (M.submatrix f f) := by
  have := Matrix.PosSemidef.submatrix (show (M - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef from h) f
  have e : (M - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix f f =
      M.submatrix f f - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    have h1 := congrFun (congrFun (Matrix.submatrix_one (α := ℂ) f hf) i) j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply] at h1 ⊢
    rw [h1]
  rw [e] at this
  exact this

/-- Convex combinations of two matrices `⪰ c I` are `⪰ c I`. -/
theorem Dominates.combo {n : ℕ} {c : ℚ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Dominates c A)
    (hB : Dominates c B) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Dominates c ((a : ℂ) • A + (b : ℂ) • B) := by
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have e : (a : ℂ) • A + (b : ℂ) • B - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      (a : ℂ) • (A - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        (b : ℂ) • (B - (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination ((c : ℂ) * (1 : Matrix (Fin n) (Fin n) ℂ) i j) * hab'
  unfold Dominates
  rw [e]
  exact (hA.smul (Complex.zero_le_real.mpr ha)).add (hB.smul (Complex.zero_le_real.mpr hb))

/-! ### Cyclic reduction of the three cuts -/

theorem cycShift_injective : Function.Injective cycShift :=
  Function.LeftInverse.injective (g := cycShift ∘ cycShift) fun i => cycShift_cube i

/-- `M ⪰ c I` on each of the three partial transposes. -/
def DominatesPPT3 (c : ℚ) (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  Dominates c (ptA ρ) ∧ Dominates c (ptB ρ) ∧ Dominates c (ptC ρ)

/-- Strict fully-PPT: all three partial transposes are positive definite. -/
def IsStrictPPT3 (ρ : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  (ptA ρ).PosDef ∧ (ptB ρ).PosDef ∧ (ptC ρ).PosDef

/-- For a cyclically invariant `ρ`, the bound on the cut `A` gives the bound on all cuts. -/
theorem dominatesPPT3_of_shift {c : ℚ} {ρ : Matrix (Fin 8) (Fin 8) ℂ}
    (hs : ρ.submatrix cycShift cycShift = ρ) (h : Dominates c (ptA ρ)) : DominatesPPT3 c ρ := by
  refine ⟨h, ?_, ?_⟩
  · rw [ptB_eq_of_shift_invariant ρ hs]; exact h.submatrix cycShift_injective
  · rw [ptC_eq_of_shift_invariant ρ hs]
    exact h.submatrix (cycShift_injective.comp cycShift_injective)

theorem DominatesPPT3.strict {c : ℚ} {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hc : 0 < c)
    (h : DominatesPPT3 c ρ) : IsStrictPPT3 ρ :=
  ⟨h.1.posDef hc, h.2.1.posDef hc, h.2.2.posDef hc⟩

theorem IsStrictPPT3.isPPT3 {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsStrictPPT3 ρ) : IsPPT3 ρ :=
  ⟨h.1.posSemidef, h.2.1.posSemidef, h.2.2.posSemidef⟩

theorem DominatesPPT3.mono {c c' : ℚ} {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : DominatesPPT3 c ρ)
    (hc : c' ≤ c) : DominatesPPT3 c' ρ :=
  ⟨h.1.mono hc, h.2.1.mono hc, h.2.2.mono hc⟩

theorem ptA_eq_table (M : Matrix (Fin 8) (Fin 8) ℂ) (T : Fin 8 → Fin 8 → QW)
    (h : ∀ i j, M i j = cwq (T i j)) : ptA M = Matrix.of fun i j => cwq (ptq T i j) := by
  ext i j
  simp only [ptA, ptq, of_apply, h]

/-- A biseparable operator is positive semidefinite. -/
theorem IsBiseparable.posSemidef {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable ρ) :
    ρ.PosSemidef := by
  obtain ⟨n, φ, -, rfl⟩ := h
  exact posSemidef_sum _ fun i _ => posSemidef_vecMulVec_self_star _

/-! ### Cyclic invariance -/

theorem sigmaBS_cycShift : sigmaBS.submatrix cycShift cycShift = sigmaBS := by
  ext i j
  have : sigq XBq (cycShift i) (cycShift j) = sigq XBq i j := by
    revert i j; decide +kernel
  simp only [Matrix.submatrix_apply, sigmaBS_apply, this]

theorem sigmaD_cycShift : sigmaD.submatrix cycShift cycShift = sigmaD := by
  ext i j
  have : sigq XDq (cycShift i) (cycShift j) = sigq XDq i j := by
    revert i j; decide +kernel
  simp only [Matrix.submatrix_apply, sigmaD_apply, this]

theorem sigmaLine_cycShift (t : ℝ) : (sigmaLine t).submatrix cycShift cycShift = sigmaLine t := by
  ext i j
  have h1 := congrFun (congrFun sigmaBS_cycShift i) j
  have h2 := congrFun (congrFun sigmaD_cycShift i) j
  simp only [Matrix.submatrix_apply] at h1 h2
  simp only [sigmaLine, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, h1, h2]

/-! ### The three endpoints of the line -/

/-- `X(-1/200) = (201/200) X_∂ - (1/200) X_BS` as a table. -/
def XEq (a b : Fin 5) : QW := qsmul (201 / 200) (XDq a b) + qsmul (-1 / 200) (XBq a b)

/-- `σ(-1/200) = (201/200) σ_∂ - (1/200) σ_BS` as a table. -/
def SEq (i j : Fin 8) : QW :=
  qsmul (201 / 200) (sigq XDq i j) + qsmul (-1 / 200) (sigq XBq i j)

theorem sigmaLine_neg_apply (i j : Fin 8) : sigmaLine (-1 / 200) i j = cwq (SEq i j) := by
  simp only [sigmaLine, SEq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, cwq_smul,
    sigmaD_apply, sigmaBS_apply]
  push_cast
  norm_num

theorem Xline_neg_apply (a b : Fin 5) : Xline (-1 / 200) a b = cwq (XEq a b) := by
  simp only [Xline, XEq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, cwq_smul,
    Xd_apply, XBS_apply]
  push_cast
  norm_num

theorem Xline_zero : Xline 0 = Xd := by simp [Xline]
theorem Xline_one : Xline 1 = XBS := by simp [Xline]
theorem sigmaLine_zero : sigmaLine 0 = sigmaD := by simp [sigmaLine]
theorem sigmaLine_one : sigmaLine 1 = sigmaBS := by simp [sigmaLine]

theorem ptA_BS_dominates : Dominates (1 / 400) (ptA sigmaBS) := by
  rw [ptA_eq_table _ _ sigmaBS_apply]
  exact dominates_of_ldl _ _ ldlBSd ldlBSL (by decide +kernel) (by decide +kernel)

theorem ptA_D_dominates : Dominates (1 / 300) (ptA sigmaD) := by
  rw [ptA_eq_table _ _ sigmaD_apply]
  exact dominates_of_ldl _ _ ldlDd ldlDL (by decide +kernel) (by decide +kernel)

theorem ptA_E_dominates : Dominates (1 / 400) (ptA (sigmaLine (-1 / 200))) := by
  rw [ptA_eq_table _ _ sigmaLine_neg_apply]
  exact dominates_of_ldl _ _ ldlEd ldlEL (by decide +kernel) (by decide +kernel)

theorem ptA_G_dominates : Dominates (1 / 2000) (ptA (rhoT (10 / 3))) := by
  rw [ptA_eq_table _ _ rhoG_apply]
  exact dominates_of_ldl _ _ ldlGd ldlGL (by decide +kernel) (by decide +kernel)

theorem XBS_dominates : Dominates (1 / 400) XBS := by
  have : XBS = Matrix.of fun a b => cwq (XBq a b) := by ext a b; exact XBS_apply a b
  rw [this]
  exact dominates_of_ldl _ _ ldlXBd ldlXBL (by decide +kernel) (by decide +kernel)

theorem Xd_dominates : Dominates (1 / 100) Xd := by
  have : Xd = Matrix.of fun a b => cwq (XDq a b) := by ext a b; exact Xd_apply a b
  rw [this]
  exact dominates_of_ldl _ _ ldlXDd ldlXDL (by decide +kernel) (by decide +kernel)

theorem Xline_neg_dominates : Dominates (1 / 400) (Xline (-1 / 200)) := by
  have : Xline (-1 / 200) = Matrix.of fun a b => cwq (XEq a b) := by
    ext a b; exact Xline_neg_apply a b
  rw [this]
  exact dominates_of_ldl _ _ ldlXEd ldlXEL (by decide +kernel) (by decide +kernel)

/-! ### Convexity along the line -/

theorem sigmaLine_combo (t₁ t₂ a b : ℝ) (hab : a + b = 1) :
    sigmaLine (a * t₁ + b * t₂) = (a : ℂ) • sigmaLine t₁ + (b : ℂ) • sigmaLine t₂ := by
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  ext i j
  simp only [sigmaLine, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  linear_combination (-(sigmaD i j)) * hab'

theorem Xline_combo (t₁ t₂ a b : ℝ) (hab : a + b = 1) :
    Xline (a * t₁ + b * t₂) = (a : ℂ) • Xline t₁ + (b : ℂ) • Xline t₂ := by
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  ext i j
  simp only [Xline, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  linear_combination (-(Xd i j)) * hab'

theorem ptA_add (M N : Matrix (Fin 8) (Fin 8) ℂ) : ptA (M + N) = ptA M + ptA N := by
  ext i j; rfl

theorem ptA_smul (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) : ptA (c • M) = c • ptA M := by
  ext i j; rfl

/-- Along the whole line `-1/200 ≤ t ≤ 1`, `σ(t)^{T_A} ⪰ I/400`. -/
theorem ptA_line_dominates (t : ℝ) (h1 : -1 / 200 ≤ t) (h2 : t ≤ 1) :
    Dominates (1 / 400) (ptA (sigmaLine t)) := by
  rcases le_total 0 t with h0 | h0
  · have e := sigmaLine_combo 0 1 (1 - t) t (by ring)
    rw [show (1 - t) * 0 + t * 1 = t by ring, sigmaLine_zero, sigmaLine_one] at e
    rw [e, ptA_add, ptA_smul, ptA_smul]
    exact Dominates.combo (ptA_D_dominates.mono (by norm_num)) ptA_BS_dominates (by linarith) h0
      (by ring)
  · have e := sigmaLine_combo (-1 / 200) 0 (-200 * t) (1 + 200 * t) (by ring)
    rw [show (-200 * t) * (-1 / 200) + (1 + 200 * t) * 0 = t by ring, sigmaLine_zero] at e
    rw [e, ptA_add, ptA_smul, ptA_smul]
    exact Dominates.combo ptA_E_dominates (ptA_D_dominates.mono (by norm_num)) (by linarith)
      (by linarith) (by ring)

/-- Along the whole line `-1/200 ≤ t ≤ 1`, the coefficient matrix is `⪰ I/400`. -/
theorem Xline_dominates (t : ℝ) (h1 : -1 / 200 ≤ t) (h2 : t ≤ 1) : Dominates (1 / 400) (Xline t) := by
  rcases le_total 0 t with h0 | h0
  · have e := Xline_combo 0 1 (1 - t) t (by ring)
    rw [show (1 - t) * 0 + t * 1 = t by ring, Xline_zero, Xline_one] at e
    rw [e]
    exact Dominates.combo (Xd_dominates.mono (by norm_num)) XBS_dominates (by linarith) h0 (by ring)
  · have e := Xline_combo (-1 / 200) 0 (-200 * t) (1 + 200 * t) (by ring)
    rw [show (-200 * t) * (-1 / 200) + (1 + 200 * t) * 0 = t by ring, Xline_zero] at e
    rw [e]
    exact Dominates.combo Xline_neg_dominates (Xd_dominates.mono (by norm_num)) (by linarith)
      (by linarith) (by ring)

/-! ### Headlines -/

/-- `σ_BS` (`eq:ppt3-bs-same-support`) is a positive semidefinite operator, invariant under the
cyclic shift, with `σ_BS^{T_c} ⪰ I/400` and in particular all three partial transposes positive
definite (`thm:ppt3-phase-coexistence`, strict PPT clause for the biseparable member). -/
theorem sigmaBS_strict_ppt :
    sigmaBS.PosSemidef ∧ sigmaBS.submatrix cycShift cycShift = sigmaBS ∧
      DominatesPPT3 (1 / 400) sigmaBS ∧ IsStrictPPT3 sigmaBS := by
  have h := dominatesPPT3_of_shift sigmaBS_cycShift ptA_BS_dominates
  exact ⟨sigmaBS_biseparable.posSemidef, sigmaBS_cycShift, h, h.strict (by norm_num)⟩

/-- `σ_∂` (`eq:ppt3-exposed-state`) is positive semidefinite, cyclically invariant, with
`σ_∂^{T_c} ⪰ I/300` at each cut (`prop:ppt3-exposed-transition`), hence strictly PPT. -/
theorem sigmaD_strict_ppt :
    sigmaD.PosSemidef ∧ sigmaD.submatrix cycShift cycShift = sigmaD ∧
      DominatesPPT3 (1 / 300) sigmaD ∧ IsStrictPPT3 sigmaD := by
  have h := dominatesPPT3_of_shift sigmaD_cycShift ptA_D_dominates
  exact ⟨sigmaD_biseparable.posSemidef, sigmaD_cycShift, h, h.strict (by norm_num)⟩

/-- The GME member `ρ_{10/3}` is strictly fully PPT: `ρ_{10/3}^{T_c} ⪰ I/2000` for each cut
(`thm:ppt3-phase-coexistence`, strict PPT clause for the GME member). -/
theorem rhoT_ten_thirds_strict_ppt :
    DominatesPPT3 (1 / 2000) (rhoT (10 / 3)) ∧ IsStrictPPT3 (rhoT (10 / 3)) := by
  have h := dominatesPPT3_of_shift (rhoT_cycShift (10 / 3)) ptA_G_dominates
  exact ⟨h, h.strict (by norm_num)⟩

theorem sigmaLine_eq_BXB (t : ℝ) (h1 : -1 / 200 ≤ t) (h2 : t ≤ 1) :
    sigmaLine t = Bs 1 * Xline t * (Bs 1)ᴴ ∧ (Xline t).PosDef ∧ (sigmaLine t).PosSemidef := by
  have hX := (Xline_dominates t h1 h2).posDef (by norm_num)
  refine ⟨sigmaLine_eq t, hX, ?_⟩
  rw [sigmaLine_eq]
  exact hX.posSemidef.mul_mul_conjTranspose_same _

/-- **`prop:ppt3-exposed-transition`, strict-PPT clause.**  Every `σ(t) = (1-t)σ_∂ + tσ_BS` with
`-1/200 ≤ t ≤ 1` is a positive semidefinite state `B (X_∂ + tX_Δ) B†` with positive definite
coefficient matrix `X_∂ + tX_Δ ⪰ I/400`, cyclically invariant, with `σ(t)^{T_c} ⪰ I/400` at each
cut, hence strictly fully PPT. -/
theorem exposed_line_fully_ppt (t : ℝ) (h1 : -1 / 200 ≤ t) (h2 : t ≤ 1) :
    (sigmaLine t).PosSemidef ∧ (sigmaLine t).trace = 1 ∧
      Dominates (1 / 400) (Xline t) ∧ (Xline t).PosDef ∧
      (sigmaLine t).submatrix cycShift cycShift = sigmaLine t ∧
      DominatesPPT3 (1 / 400) (sigmaLine t) ∧ IsStrictPPT3 (sigmaLine t) := by
  have h := dominatesPPT3_of_shift (sigmaLine_cycShift t) (ptA_line_dominates t h1 h2)
  obtain ⟨-, hX, hP⟩ := sigmaLine_eq_BXB t h1 h2
  exact ⟨hP, trace_sigmaLine t, Xline_dominates t h1 h2, hX, sigmaLine_cycShift t, h,
    h.strict (by norm_num)⟩

/-- **`thm:ppt3-phase-coexistence`** (full statement of the formalised clauses).  On the support
`ran B` there are two trace-one states, the biseparable `σ_BS = B X_BS B†` and the GME
`ρ_{10/3} = B X_{10/3} B†` (so `ρ_{10/3}` and `σ_BS` have the same support `ran B`), both positive
semidefinite and each with all three partial transposes positive definite (`⪰ I/400`,
resp. `⪰ I/2000`); the coefficient matrices are positive definite.  Not covered: the rank
statements and the cut-product-curve clause. -/
theorem ppt3_phase_coexistence_full :
    (sigmaBS = Bs 1 * XBS * (Bs 1)ᴴ ∧ rhoT (10 / 3) = Bs 1 * Xt (10 / 3) * (Bs 1)ᴴ ∧
      sigmaBS = (1 / 3 : ℂ) • (vecMulVec vVec (star vVec) + Gam 2 + Gam (2 * Complex.I)) ∧
      sigmaBS.trace = 1 ∧ (rhoT (10 / 3)).trace = 1 ∧
      IsBiseparable sigmaBS ∧ IsGME (rhoT (10 / 3))) ∧
    (sigmaBS.PosSemidef ∧ (rhoT (10 / 3)).PosSemidef) ∧
    (IsStrictPPT3 sigmaBS ∧ IsStrictPPT3 (rhoT (10 / 3))) ∧
    (DominatesPPT3 (1 / 400) sigmaBS ∧ DominatesPPT3 (1 / 2000) (rhoT (10 / 3))) ∧
    (XBS.PosDef ∧ (Xt (10 / 3)).PosDef) := by
  refine ⟨ppt3_phase_coexistence, ⟨sigmaBS_biseparable.posSemidef,
    rhoT_posSemidef _ (by norm_num)⟩, ⟨sigmaBS_strict_ppt.2.2.2, rhoT_ten_thirds_strict_ppt.2⟩,
    ⟨sigmaBS_strict_ppt.2.2.1, rhoT_ten_thirds_strict_ppt.1⟩,
    XBS_dominates.posDef (by norm_num), ?_⟩
  unfold Xt
  refine Matrix.PosDef.diagonal fun a => ?_
  have h : (0 : ℝ) < ![10 / 3, 3 * (10 / 3), 3, 3, 1] a / (7 * (10 / 3 + 3)) := by
    apply div_pos _ (by norm_num)
    fin_cases a <;> simp
  exact Complex.zero_lt_real.mpr h

/-- **`prop:ppt3-exposed-transition`** (full statement of the formalised clauses).
`σ_∂ = B X_∂ B†` is a trace-one biseparable state with `tr(H_5 X_∂) = 0` and
`σ_∂^{T_c} ⪰ I/300`; the line `σ(t) = (1-t)σ_∂ + tσ_BS`, `-1/200 ≤ t ≤ 1`, consists of
positive semidefinite trace-one operators `B (X_∂ + tX_Δ) B†` with positive definite coefficient
matrix and all three partial transposes positive definite (`⪰ I/400`), with
`tr(H_5(X_∂ + tX_Δ)) = t·25082/54375`; `σ(t)` is biseparable for `0 ≤ t ≤ 1` and GME for
`-1/200 ≤ t < 0`.  Not covered: rank five, and the paper's `⪰ I/1200` margin for `t ≤ 0` (here
the stronger `⪰ I/400` holds on the whole line, by convexity). -/
theorem ppt3_exposed_transition_full :
    (sigmaD = Bs 1 * Xd * (Bs 1)ᴴ ∧
      sigmaD = (1 / 5 : ℂ) • Gam 1 + (1 / 2 : ℂ) • Gam Complex.I + (3 / 10 : ℂ) • Gam z5 ∧
      sigmaD.trace = 1 ∧ IsBiseparable sigmaD ∧ (Hs 1 * Xd).trace = 0) ∧
    DominatesPPT3 (1 / 300) sigmaD ∧ IsStrictPPT3 sigmaD ∧
    (∀ t : ℝ, (sigmaLine t).trace = 1 ∧ sigmaLine t = Bs 1 * Xline t * (Bs 1)ᴴ ∧
      (Hs 1 * Xline t).trace = ((t * (25082 / 54375) : ℝ) : ℂ)) ∧
    (∀ t : ℝ, -1 / 200 ≤ t → t ≤ 1 →
      (sigmaLine t).PosSemidef ∧ (Xline t).PosDef ∧ DominatesPPT3 (1 / 400) (sigmaLine t) ∧
        IsStrictPPT3 (sigmaLine t)) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsBiseparable (sigmaLine t)) ∧
    (∀ t : ℝ, -1 / 200 ≤ t → t < 0 → IsGME (sigmaLine t)) := by
  have ht := ppt3_exposed_transition
  refine ⟨ppt3_exposed_state, sigmaD_strict_ppt.2.2.1, sigmaD_strict_ppt.2.2.2, ht.1, ?_,
    ht.2.1, ht.2.2⟩
  intro t h1 h2
  obtain ⟨hP, -, -, hX, -, hD, hS⟩ := exposed_line_fully_ppt t h1 h2
  exact ⟨hP, hX, hD, hS⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.sigmaBS_strict_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigmaBS_strict_ppt

/-- info: 'FormalResearch.PPTThreeQubit.sigmaD_strict_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigmaD_strict_ppt

/-- info: 'FormalResearch.PPTThreeQubit.rhoT_ten_thirds_strict_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoT_ten_thirds_strict_ppt

/-- info: 'FormalResearch.PPTThreeQubit.exposed_line_fully_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exposed_line_fully_ppt

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_phase_coexistence_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_phase_coexistence_full

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_exposed_transition_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_exposed_transition_full

end FormalResearch.PPTThreeQubit

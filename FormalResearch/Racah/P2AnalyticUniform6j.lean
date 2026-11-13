module

public import FormalResearch.Racah.P2AnalyticBulk6j
public import FormalResearch.Racah.P2AnalyticCore

/-!
# The edge factor and the uniform `6j` expansion (Weyl P2, `thm:uniformedge`(b), `eq:edgefactoroverlap`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, "The edge factor" (`eq:universalEdgeFactor`,
`eq:edgefactoroverlap`, `eq:6jEdgeFactors`), `thm:uniformedge`(b) (`eq:6juniformedge`) and the
sentence after it ("`0 < c ≤ E ≤ 1` on the physical lattice").

## Results

* `edgeR p X = R_p(X) = √(𝔠_p(X)/X^p)`; `edgeR_eq`: `R_p(X)² = Ct p 1 (X⁻²)`, a polynomial in `X⁻²`
  (evenness in `X⁻¹`); `edgeR_pos_le_one`: `edgeRlow p ≤ R_p(X) ≤ 1` for `X ≥ (p+1)/2`
  (`edgeRlow p > 0` depends on `p` only); `edgeR_expansion`:
  `|R_p(X) - (1 - p(p²-1)/(48X²))| ≤ C_p X⁻⁴`.
* `edgeE`, `edgeW`, `edgeEW`: `E_{A,B}(C)`, `W_{6j}(x)` and `E W`; `edgeEW_eq_sqrt`,
  `edgeEW_eq_edgeFac`: `E W = edgeFac` (the carrier's `√edgeSq`); `phys_edge_args`: all four
  edge arguments are `≥ (p+1)/2` on the physical lattice (every chamber, `p = ⌊|m-n|⌋₊`,
  `q = ⌊|m+n|⌋₊`); `edgeE_bounds`: `0 < c ≤ E ≤ 1`.
* `Hc`, `DomH`, `analyticAt_Hc`: the uniform germ (carrier without edge factor, `τ`, `δ`, `t = S⁻²`
  independent), analytic jointly on `|δ| < 1`; `Hall`, `s6`: all chambers; `Phi6_edge_factor`:
  the exact identity `Φ_f = E W · Hall(τ, δ, (A+B)⁻²)`.
* `Phi6_uniform_edge` (**`thm:uniformedge`(b)**): the expansion `Φ = E W [∑ s_r (A+B)^{-2r} + O]`,
  uniform on the physical `c`-lattice for `λ ≤ A/B ≤ λ⁻¹`; `s6c_eq_sum`, `analyticOnNhd_cKc`: `s_r`
  is a polynomial of degree `≤ d` in `τ` with coefficients analytic in `δ ∈ (-1,1)`;
  `edgeW_mul_s6_zero`: `W s_0 = dZero6`.
  Not proved here: that the coefficients of `s_r` are *rational* in `δ` with poles only at `±1`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ Set Filter Topology

/-! ### The universal edge factor `R_p(X)` -/

/-- `R_p(X) = √(𝔠_p(X)/X^p)` (`eq:universalEdgeFactor`). -/
noncomputable def edgeR (p : ℕ) (X : ℝ) : ℝ := Real.sqrt (cenProd p X / X ^ p)

lemma edgeR_arg (p : ℕ) {X : ℝ} (hX : X ≠ 0) : cenProd p X / X ^ p = Ct p 1 (1 / X ^ 2) := by
  have h := cenProd_scale p X 1 hX
  rw [mul_one] at h
  rw [h]
  exact mul_div_cancel_left₀ _ (pow_ne_zero p hX)

/-- `R_p(X)² = Ct p 1 (X⁻²)` (`lem:centeredshift`): a polynomial in `X⁻²`, hence even in `X⁻¹`. -/
theorem edgeR_eq (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    edgeR p X = Real.sqrt (Ct p 1 (1 / X ^ 2)) := by
  unfold edgeR; rw [edgeR_arg p hX]

lemma Ct_one_pos_le (p : ℕ) {t : ℝ} (ht : 0 ≤ t) (hp : ((p : ℝ) + 1) ^ 2 * t ≤ 4) :
    0 < Ct p 1 t ∧ Ct p 1 t ≤ 1 := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | p + 2, ih =>
      rw [Ct_succ_succ]
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hp' : (((p : ℝ) + 2) + 1) ^ 2 * t ≤ 4 := by push_cast at hp; exact hp
      have hc : ((p : ℝ) + 1) ^ 2 * t < 4 := by
        rcases ht.eq_or_lt with h | h
        · rw [← h]; norm_num
        · nlinarith
      have hle : ((p : ℝ) + 1) ^ 2 * t ≤ 4 := hc.le
      obtain ⟨i1, i2⟩ := ih p (by omega) hle
      have f1 : 0 < 1 ^ 2 - ((p : ℝ) + 1) ^ 2 / 4 * t := by nlinarith
      have f2 : 1 ^ 2 - ((p : ℝ) + 1) ^ 2 / 4 * t ≤ 1 := by nlinarith [sq_nonneg ((p : ℝ) + 1)]
      exact ⟨mul_pos f1 i1, (mul_le_of_le_one_left i1.le f2).trans i2⟩

lemma Ct_one_anti (p : ℕ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') (hp : ((p : ℝ) + 1) ^ 2 * t' ≤ 4) :
    Ct p 1 t' ≤ Ct p 1 t := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | p + 2, ih =>
      rw [Ct_succ_succ]
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      have hp' : (((p : ℝ) + 2) + 1) ^ 2 * t' ≤ 4 := by push_cast at hp; exact hp
      have ht' : 0 ≤ t' := ht.trans htt
      have hc : ((p : ℝ) + 1) ^ 2 * t' < 4 := by
        rcases ht'.eq_or_lt with h | h
        · rw [← h]; norm_num
        · nlinarith
      have hle : ((p : ℝ) + 1) ^ 2 * t' ≤ 4 := hc.le
      obtain ⟨i1, i2⟩ := Ct_one_pos_le p ht' hle
      have f1 : 0 < 1 ^ 2 - ((p : ℝ) + 1) ^ 2 / 4 * t' := by nlinarith
      have f2 : 1 ^ 2 - ((p : ℝ) + 1) ^ 2 / 4 * t' ≤ 1 ^ 2 - ((p : ℝ) + 1) ^ 2 / 4 * t := by
        nlinarith [sq_nonneg ((p : ℝ) + 1)]
      exact mul_le_mul f2 (ih p (by omega) hle) i1.le (by linarith)

/-- The explicit lower constant `c_p = √(Ct p 1 (4/(p+1)²)) > 0`. -/
noncomputable def edgeRlow (p : ℕ) : ℝ := Real.sqrt (Ct p 1 (4 / ((p : ℝ) + 1) ^ 2))

lemma edgeRlow_pos (p : ℕ) : 0 < edgeRlow p := by
  have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  have := (Ct_one_pos_le p (t := 4 / ((p : ℝ) + 1) ^ 2) (by positivity)
    (by rw [mul_div_cancel₀ _ hp.ne'])).1
  exact Real.sqrt_pos.mpr this

lemma inv_sq_le {p : ℕ} {X : ℝ} (hX : ((p : ℝ) + 1) / 2 ≤ X) :
    0 < X ∧ 1 / X ^ 2 ≤ 4 / ((p : ℝ) + 1) ^ 2 := by
  have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  refine ⟨hX0, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Edge-factor bounds** (`0 < c ≤ E ≤ 1`, row 46): `c_p ≤ R_p(X) ≤ 1` for `X ≥ (p+1)/2`. -/
theorem edgeR_pos_le_one (p : ℕ) {X : ℝ} (hX : ((p : ℝ) + 1) / 2 ≤ X) :
    edgeRlow p ≤ edgeR p X ∧ edgeR p X ≤ 1 := by
  obtain ⟨hX0, hT⟩ := inv_sq_le hX
  rw [edgeR_eq p hX0.ne']
  have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  have ht0 : (0 : ℝ) ≤ 1 / X ^ 2 := by positivity
  have hb : ((p : ℝ) + 1) ^ 2 * (1 / X ^ 2) ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hT hp.le
    rwa [mul_div_cancel₀ _ hp.ne'] at this
  refine ⟨Real.sqrt_le_sqrt ?_, ?_⟩
  · exact Ct_one_anti p ht0 hT (by rw [mul_div_cancel₀ _ hp.ne'])
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using (Ct_one_pos_le p ht0 hb).2⟩

lemma edgeR_pos (p : ℕ) {X : ℝ} (hX : ((p : ℝ) + 1) / 2 ≤ X) : 0 < edgeR p X :=
  lt_of_lt_of_le (edgeRlow_pos p) (edgeR_pos_le_one p hX).1

lemma edgeR_sq (p : ℕ) {X : ℝ} (hX : ((p : ℝ) + 1) / 2 ≤ X) :
    edgeR p X ^ 2 = cenProd p X / X ^ p := by
  unfold edgeR
  refine Real.sq_sqrt ?_
  obtain ⟨hX0, hT⟩ := inv_sq_le hX
  rw [edgeR_arg p hX0.ne']
  have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  have hb : ((p : ℝ) + 1) ^ 2 * (1 / X ^ 2) ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hT hp.le
    rwa [mul_div_cancel₀ _ hp.ne'] at this
  exact (Ct_one_pos_le p (by positivity) hb).1.le

/-! ### The `X⁻²` expansion of `R_p(X)` -/

lemma Ct_one_expand (p : ℕ) :
    ∃ Q : Polynomial ℝ, ∀ t : ℝ,
      Ct p 1 t = 1 - ((p : ℝ) * ((p : ℝ) ^ 2 - 1) / 24) * t + t ^ 2 * Q.eval t := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p, ih with
    | 0, _ => exact ⟨0, fun t => by simp [Ct_zero]⟩
    | 1, _ => exact ⟨0, fun t => by simp [Ct_one]⟩
    | p + 2, ih =>
      obtain ⟨Q, hQ⟩ := ih p (by omega)
      refine ⟨Polynomial.C ((((p : ℝ) + 1) ^ 2 / 4) * ((p : ℝ) * ((p : ℝ) ^ 2 - 1) / 24)) + Q -
        Polynomial.C (((p : ℝ) + 1) ^ 2 / 4) * Polynomial.X * Q, fun t => ?_⟩
      rw [Ct_succ_succ, hQ t]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      push_cast
      ring

/-- **`eq:edgefactoroverlap`**: `R_p(X) = 1 - p(p²-1)/(48 X²) + O(X⁻⁴)`, uniformly for
`X ≥ (p+1)/2`. -/
theorem edgeR_expansion (p : ℕ) :
    ∃ C : ℝ, ∀ X : ℝ, ((p : ℝ) + 1) / 2 ≤ X →
      |edgeR p X - (1 - ((p : ℝ) * ((p : ℝ) ^ 2 - 1) / 48) / X ^ 2)| ≤ C / X ^ 4 := by
  obtain ⟨Q, hQ⟩ := Ct_one_expand p
  set κ : ℝ := (p : ℝ) * ((p : ℝ) ^ 2 - 1) / 24 with hκ
  set T : ℝ := 4 / ((p : ℝ) + 1) ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (Polynomial.continuous Q).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl _, hT0⟩)
  refine ⟨M / 2 + (|κ| + M * T) ^ 2 / 2, fun X hX => ?_⟩
  obtain ⟨hX0, hTX⟩ := inv_sq_le hX
  set t : ℝ := 1 / X ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hQt : |Q.eval t| ≤ M := by
    have := hM t ⟨ht0, hTX⟩
    simpa using this
  have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
  have hb : ((p : ℝ) + 1) ^ 2 * t ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hTX hp.le
    rwa [mul_div_cancel₀ _ hp.ne'] at this
  have hpos := (Ct_one_pos_le p ht0 hb).1
  rw [edgeR_eq p hX0.ne']
  set y : ℝ := -κ * t + t ^ 2 * Q.eval t with hy
  have hCt : Ct p 1 t = 1 + y := by rw [hQ t]; ring
  rw [hCt] at hpos ⊢
  -- √(1+y) = 1 + y/2 - (√(1+y) - 1)²/2
  have hs : Real.sqrt (1 + y) = 1 + y / 2 - (Real.sqrt (1 + y) - 1) ^ 2 / 2 := by
    have := Real.sq_sqrt hpos.le
    nlinarith
  have hsd : |Real.sqrt (1 + y) - 1| ≤ |y| := by
    have h1 : 0 ≤ Real.sqrt (1 + y) := Real.sqrt_nonneg _
    have h2 : (Real.sqrt (1 + y) - 1) * (Real.sqrt (1 + y) + 1) = y := by
      have := Real.sq_sqrt hpos.le; nlinarith
    have h3 : 1 ≤ Real.sqrt (1 + y) + 1 := by linarith
    have : |Real.sqrt (1 + y) - 1| * |Real.sqrt (1 + y) + 1| = |y| := by
      rw [← abs_mul, h2]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt (1 + y) + 1)] at this
    nlinarith [abs_nonneg (Real.sqrt (1 + y) - 1)]
  have hyb : |y| ≤ (|κ| + M * T) * t := by
    have e1 : |t ^ 2 * Q.eval t| ≤ t ^ 2 * M := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hQt (by positivity)
    have e2 : |-κ * t| = |κ| * t := by rw [abs_mul, abs_neg, abs_of_nonneg ht0]
    have e3 : t ^ 2 * M ≤ M * T * t := by
      have : t * M ≤ T * M := mul_le_mul_of_nonneg_right hTX hM0
      nlinarith
    calc |y| ≤ |-κ * t| + |t ^ 2 * Q.eval t| := abs_add_le _ _
      _ ≤ |κ| * t + M * T * t := by rw [e2]; linarith
      _ = (|κ| + M * T) * t := by ring
  have key : Real.sqrt (1 + y) - (1 - (p * (p ^ 2 - 1) / 48) / X ^ 2) =
      t ^ 2 * Q.eval t / 2 - (Real.sqrt (1 + y) - 1) ^ 2 / 2 := by
    have : (p * (p ^ 2 - 1) / 48 : ℝ) / X ^ 2 = κ * t / 2 := by
      rw [hκ, ht]; ring
    rw [this]
    nlinarith [hs, hy]
  rw [key]
  have e4 : |t ^ 2 * Q.eval t / 2| ≤ t ^ 2 * M / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQt (by positivity)) (by norm_num)
  have e5 : |(Real.sqrt (1 + y) - 1) ^ 2 / 2| ≤ ((|κ| + M * T) * t) ^ 2 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    exact pow_le_pow_left₀ (abs_nonneg _) (hsd.trans hyb) 2
  have hX4 : t ^ 2 = 1 / X ^ 4 := by rw [ht]; ring
  calc _ ≤ |t ^ 2 * Q.eval t / 2| + |(Real.sqrt (1 + y) - 1) ^ 2 / 2| := abs_sub _ _
    _ ≤ t ^ 2 * M / 2 + ((|κ| + M * T) * t) ^ 2 / 2 := add_le_add e4 e5
    _ = (M / 2 + (|κ| + M * T) ^ 2 / 2) / X ^ 4 := by
      rw [mul_pow, hX4]; ring

/-! ### The edge factors `E_{A,B}(C)`, `W_{6j}(x)` -/

/-- `E_{A,B}(C) = R_p(A-B+C) R_p(-A+B+C) R_q(A+B-C) R_q(A+B+C)` with `p = p_min`, `q = p_max`
(`eq:6jEdgeFactors`). -/
noncomputable def edgeE (p q : ℕ) (A B C : ℝ) : ℝ :=
  edgeR p (A - B + C) * edgeR p (-A + B + C) * edgeR q (A + B - C) * edgeR q (A + B + C)

/-- `W_{6j}(x) = ((1-x)/2)^{p/2} ((1+x)/2)^{q/2}` (`eq:6jEdgeFactors`), as a positive square root. -/
noncomputable def edgeW (p q : ℕ) (x : ℝ) : ℝ := Real.sqrt (((1 - x) / 2) ^ p * ((1 + x) / 2) ^ q)

/-- The product `E_{A,B}(C) W_{6j}(x)`, `x = cosA A B C`. -/
noncomputable def edgeEW (p q : ℕ) (A B C : ℝ) : ℝ := edgeE p q A B C * edgeW p q (cosA A B C)

/-- The radicand of `E W` with explicit integer exponents (`edgeSq` with `⌊m ∓ n⌋₊ = p, q`). -/
noncomputable def edgeSqP (p q : ℕ) (A B C : ℝ) : ℝ :=
  cenProd p (A - B + C) * cenProd p (-A + B + C) * cenProd q (A + B - C) * cenProd q (A + B + C) /
    (4 * A * B) ^ (p + q)

lemma edgeSq_eq_edgeSqP (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (A B C : ℝ) :
    edgeSq m n A B C = edgeSqP p q A B C := by
  obtain ⟨h1, h2, h3⟩ := floor_labels m n p q hp hq
  unfold edgeSq edgeSqP
  rw [h1, h2, h3]

lemma edgeSqP_eq (p q : ℕ) (A B C : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (h1 : A - B + C ≠ 0)
    (h2 : -A + B + C ≠ 0) (h3 : A + B - C ≠ 0) (h4 : A + B + C ≠ 0) :
    edgeSqP p q A B C =
      (cenProd p (A - B + C) / (A - B + C) ^ p) * (cenProd p (-A + B + C) / (-A + B + C) ^ p) *
        (cenProd q (A + B - C) / (A + B - C) ^ q) * (cenProd q (A + B + C) / (A + B + C) ^ q) *
        (((1 - cosA A B C) / 2) ^ p * ((1 + cosA A B C) / 2) ^ q) := by
  have := edgeSq_eq_EW_sq (((p : ℚ) + q) / 2) (((q : ℚ) - p) / 2) p q (by ring) (by ring)
    A B C hA hB h1 h2 h3 h4
  rw [← this]
  exact (edgeSq_eq_edgeSqP _ _ p q (by ring) (by ring) A B C).symm

/-- **`E W = √edgeSq`**: on the physical range (all four arguments `≥ (p+1)/2`, resp. `(q+1)/2`)
the product `E_{A,B}(C) W_{6j}(x)` of `eq:6jEdgeFactors` is the square root of the radicand
`edgeSqP p q A B C` (so `edgeEW = edgeFac` of the carrier, `edgeEW_eq_edgeFac`). -/
theorem edgeEW_eq_sqrt (p q : ℕ) {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : ((p : ℝ) + 1) / 2 ≤ A - B + C) (h2 : ((p : ℝ) + 1) / 2 ≤ -A + B + C)
    (h3 : ((q : ℝ) + 1) / 2 ≤ A + B - C) (h4 : ((q : ℝ) + 1) / 2 ≤ A + B + C) :
    edgeEW p q A B C = Real.sqrt (edgeSqP p q A B C) := by
  have hp : (0 : ℝ) < ((p : ℝ) + 1) / 2 := by positivity
  have hq : (0 : ℝ) < ((q : ℝ) + 1) / 2 := by positivity
  rw [edgeSqP_eq p q A B C hA hB (by linarith) (by linarith) (by linarith) (by linarith)]
  rw [← edgeR_sq p h1, ← edgeR_sq p h2, ← edgeR_sq q h3, ← edgeR_sq q h4]
  have hE : 0 ≤ edgeE p q A B C := by unfold edgeE edgeR; positivity
  have : edgeR p (A - B + C) ^ 2 * edgeR p (-A + B + C) ^ 2 * edgeR q (A + B - C) ^ 2 *
      edgeR q (A + B + C) ^ 2 = edgeE p q A B C ^ 2 := by unfold edgeE; ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hE]
  rfl

lemma edgeEW_eq_edgeFac (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) {A B C : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : ((p : ℝ) + 1) / 2 ≤ A - B + C) (h2 : ((p : ℝ) + 1) / 2 ≤ -A + B + C)
    (h3 : ((q : ℝ) + 1) / 2 ≤ A + B - C) (h4 : ((q : ℝ) + 1) / 2 ≤ A + B + C) :
    edgeFac m n A B C = edgeEW p q A B C := by
  rw [edgeEW_eq_sqrt p q hA hB h1 h2 h3 h4, edgeFac, edgeSq_eq_edgeSqP m n p q hp hq]

/-! ### The physical range of the four edge arguments -/

lemma natAbs_cast_rat (k : ℤ) : ((k.natAbs : ℕ) : ℚ) = |(k : ℚ)| := by
  rw [Nat.cast_natAbs]; push_cast; rfl

/-- If `x` is an integer, `⌊|x|⌋₊` is its absolute value, in `ℝ`. -/
lemma cast_floor_abs {x : ℚ} {k : ℤ} (hx : x = k) : ((⌊|x|⌋₊ : ℕ) : ℝ) = |(x : ℝ)| := by
  subst hx
  rw [← natAbs_cast_rat, Nat.floor_natCast]
  have : ((|(k : ℚ)| : ℚ) : ℝ) = |((k : ℚ) : ℝ)| := by push_cast; rfl
  rw [← this, ← natAbs_cast_rat]; push_cast; rfl

lemma exists_int_add {a b f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    ∃ k : ℤ, m + n = k := by
  obtain ⟨n1, -, -, n4⟩ := four_nat h1 h2
  obtain ⟨p, hp⟩ := n1
  obtain ⟨q, hq⟩ := n4
  exact ⟨(p : ℤ) - q, by push_cast; linarith⟩

lemma isTri_real_nonneg {x y z : ℚ} (h : IsTri x y z) :
    (0 : ℝ) ≤ (x : ℝ) + y - z ∧ (0 : ℝ) ≤ (x : ℝ) - y + z ∧ (0 : ℝ) ≤ -(x : ℝ) + y + z := by
  have e1 := isNat_nonneg' h.1
  have e2 := isNat_nonneg' h.2.1
  have e3 := isNat_nonneg' h.2.2
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℚ) ≤ x + y - z := e1
    exact_mod_cast this
  · have : (0 : ℚ) ≤ x - y + z := e2
    exact_mod_cast this
  · have : (0 : ℚ) ≤ -x + y + z := e3
    exact_mod_cast this

/-- **All four edge arguments are `≥ (p+1)/2` resp. `(q+1)/2`** on the physical lattice (paper:
"all four arguments in `eq:6jEdgeFactors` are at least `(p+1)/2` on the physical lattice"), with
`p = p_min = |m-n|`, `q = p_max = |m+n|`, in every chamber. -/
theorem phys_edge_args {a b c f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    ((⌊|m - n|⌋₊ : ℝ) + 1) / 2 ≤ wA a n - wB b m + wC c ∧
    ((⌊|m - n|⌋₊ : ℝ) + 1) / 2 ≤ -wA a n + wB b m + wC c ∧
    ((⌊|m + n|⌋₊ : ℝ) + 1) / 2 ≤ wA a n + wB b m - wC c ∧
    ((⌊|m + n|⌋₊ : ℝ) + 1) / 2 ≤ wA a n + wB b m + wC c := by
  obtain ⟨k, hk⟩ := exists_int_sub h1 h2
  obtain ⟨l, hl⟩ := exists_int_add h1 h2
  rw [cast_floor_abs hk, cast_floor_abs hl]
  push_cast
  obtain ⟨t1, t2, t3⟩ := isTri_real_nonneg h3
  obtain ⟨u1, u2, u3⟩ := isTri_real_nonneg h4
  push_cast at u1 u2 u3
  have hC : 0 < wC c := by
    unfold wC; linarith
  unfold wA wB wC at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases abs_cases ((m : ℝ) - n) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  · rcases abs_cases ((m : ℝ) - n) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  · rcases abs_cases ((m : ℝ) + n) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  · rcases abs_cases ((m : ℝ) + n) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-! ### The uniform germ `Hc` (edge factor and the sign removed) -/

lemma analyticAt_mvEval {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}
    {u v w : X → ℝ} (hu : AnalyticAt ℝ u x) (hv : AnalyticAt ℝ v x) (hw : AnalyticAt ℝ w x)
    (P : MvPolynomial (Fin 3) ℝ) :
    AnalyticAt ℝ (fun y => MvPolynomial.eval ![u y, v y, w y] P) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    fin_cases i
    · exact hp.mul (by simpa using hu)
    · exact hp.mul (by simpa using hv)
    · exact hp.mul (by simpa using hw)

lemma analyticAt_piSixT_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : ℚ)
    {α β t : X → ℝ} {x : X} (hα : AnalyticAt ℝ α x) (hβ : AnalyticAt ℝ β x)
    (ht : AnalyticAt ℝ t x) (hα0 : α x ≠ 0) (hβ0 : β x ≠ 0) :
    AnalyticAt ℝ (fun y => piSixT f (α y) (β y) (t y)) x := by
  unfold piSixT
  refine Finset.analyticAt_fun_prod _ (fun k _ => ?_)
  have e1 : AnalyticAt ℝ (fun y => (1 - ((f : ℝ) - k) ^ 2 * t y / (4 * α y ^ 2))) x :=
    analyticAt_const.sub (AnalyticAt.div (analyticAt_const.mul ht)
      (analyticAt_const.mul (hα.pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hα0)))
  have e2 : AnalyticAt ℝ (fun y => (1 - ((f : ℝ) - k) ^ 2 * t y / (4 * β y ^ 2))) x :=
    analyticAt_const.sub (AnalyticAt.div (analyticAt_const.mul ht)
      (analyticAt_const.mul (hβ.pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hβ0)))
  exact e1.mul e2

/-- The uniform germ: `G6c` without the edge factor, with the angle `τ` and the asymmetry
`δ = (A-B)/(A+B)` as independent variables: `α = (1+δ)/2`, `β = (1-δ)/2`, `t = (A+B)⁻²`. -/
noncomputable def Hc (m n : ℚ) (d : ℕ) (τ δ t : ℝ) : ℝ :=
  (Real.sqrt (piSixT (m + d) ((1 + δ) / 2) ((1 - δ) / 2) t))⁻¹ *
    ptilde6 m n τ (t / ((1 + δ) / 2) ^ 2) (t / ((1 - δ) / 2) ^ 2)
      (t / (((1 + δ) / 2) * ((1 - δ) / 2))) d

/-- Domain of analyticity of `Hc`: `|δ| < 1` and `Π > 0`; points are `((τ, δ), t)`. -/
def DomH (m : ℚ) (d : ℕ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | |p.1.2| < 1 ∧ 0 < piSixT (m + d) ((1 + p.1.2) / 2) ((1 - p.1.2) / 2) p.2}

lemma aH_tau (p : (ℝ × ℝ) × ℝ) : AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => q.1.1) p :=
  (analyticAt_fst (𝕜 := ℝ) (p := p.1)).comp (analyticAt_fst (𝕜 := ℝ) (p := p))

lemma aH_delta (p : (ℝ × ℝ) × ℝ) : AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => q.1.2) p :=
  (analyticAt_snd (𝕜 := ℝ) (p := p.1)).comp (analyticAt_fst (𝕜 := ℝ) (p := p))

lemma aH_t (p : (ℝ × ℝ) × ℝ) : AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => q.2) p :=
  analyticAt_snd

lemma aH_alpha (p : (ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => (1 + q.1.2) / 2) p :=
  (analyticAt_const.add (aH_delta p)).div_const

lemma aH_beta (p : (ℝ × ℝ) × ℝ) :
    AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => (1 - q.1.2) / 2) p :=
  (analyticAt_const.sub (aH_delta p)).div_const

lemma abs_lt_one_alpha {δ : ℝ} (h : |δ| < 1) : 0 < (1 + δ) / 2 ∧ 0 < (1 - δ) / 2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  constructor <;> linarith

theorem DomH_isOpen (m : ℚ) (d : ℕ) : IsOpen (DomH m d) := by
  have hV : IsOpen {p : (ℝ × ℝ) × ℝ | |p.1.2| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hg : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ => piSixT (m + d) ((1 + q.1.2) / 2) ((1 - q.1.2) / 2) q.2)
      {p : (ℝ × ℝ) × ℝ | |p.1.2| < 1} := by
    intro p hp
    have := abs_lt_one_alpha hp
    exact (analyticAt_piSixT_comp (m + d) (aH_alpha p) (aH_beta p) (aH_t p) this.1.ne'
      this.2.ne').continuousAt.continuousWithinAt
  have := hg.isOpen_inter_preimage hV (isOpen_Ioi (a := (0 : ℝ)))
  convert this using 1
  ext p
  simp only [DomH, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]

/-- `Hc` is real analytic jointly in `(τ, δ, t)` on `DomH`. -/
theorem analyticAt_Hc (m n : ℚ) (d : ℕ) {p : (ℝ × ℝ) × ℝ} (hp : p ∈ DomH m d) :
    AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ => Hc m n d q.1.1 q.1.2 q.2) p := by
  obtain ⟨hδ, hP⟩ := hp
  obtain ⟨hα, hβ⟩ := abs_lt_one_alpha hδ
  have hsP := analyticAt_sqrt_comp
    (analyticAt_piSixT_comp (m + d) (aH_alpha p) (aH_beta p) (aH_t p) hα.ne' hβ.ne') hP
  have hsP' : AnalyticAt ℝ (fun q : (ℝ × ℝ) × ℝ =>
      (Real.sqrt (piSixT (m + d) ((1 + q.1.2) / 2) ((1 - q.1.2) / 2) q.2))⁻¹) p :=
    hsP.inv (Real.sqrt_pos.mpr hP).ne'
  have hpt := analyticAt_ptilde6 m n d (x := p) (τ := fun q : (ℝ × ℝ) × ℝ => q.1.1)
    (u := fun q : (ℝ × ℝ) × ℝ => q.2 / ((1 + q.1.2) / 2) ^ 2)
    (v := fun q : (ℝ × ℝ) × ℝ => q.2 / ((1 - q.1.2) / 2) ^ 2)
    (w := fun q : (ℝ × ℝ) × ℝ => q.2 / (((1 + q.1.2) / 2) * ((1 - q.1.2) / 2)))
    (aH_tau p)
    (AnalyticAt.div (aH_t p) ((aH_alpha p).pow 2) (pow_ne_zero 2 hα.ne'))
    (AnalyticAt.div (aH_t p) ((aH_beta p).pow 2) (pow_ne_zero 2 hβ.ne'))
    (AnalyticAt.div (aH_t p) ((aH_alpha p).mul (aH_beta p)) (mul_ne_zero hα.ne' hβ.ne'))
  exact hsP'.mul hpt

theorem analyticOnNhd_Hc (m n : ℚ) (d : ℕ) :
    AnalyticOnNhd ℝ (fun q : (ℝ × ℝ) × ℝ => Hc m n d q.1.1 q.1.2 q.2) (DomH m d) :=
  fun _ hp => analyticAt_Hc m n d hp

lemma mem_DomH_zero (m : ℚ) (d : ℕ) {τ δ : ℝ} (hδ : |δ| < 1) :
    ((τ, δ), (0 : ℝ)) ∈ DomH m d := by
  refine ⟨hδ, ?_⟩
  simp [piSixT_zero]

/-- The Taylor coefficient `s_r(τ; δ)` of `thm:uniformedge`(b) (canonical sector): the `t^r`
coefficient at `t = 0` of `t ↦ Hc m n d τ δ t`. -/
noncomputable def s6c (m n : ℚ) (d r : ℕ) (τ δ : ℝ) : ℝ :=
  taylorCoeff (fun (z : ℝ × ℝ) t => Hc m n d z.1 z.2 t) r (τ, δ)

/-- **Uniform Taylor remainder for `Hc`** on `τ ∈ [0,1]`, `|δ| ≤ δ₀ < 1`. -/
theorem Hc_taylor_uniform (m n : ℚ) (d : ℕ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ δ : ℝ, |δ| ≤ δ₀ → ∀ t : ℝ, |t| ≤ ρ →
      |Hc m n d τ δ t - ∑ r ∈ Finset.range R, s6c m n d r τ δ * t ^ r| ≤ C * |t| ^ R := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (-δ₀) δ₀) := isCompact_Icc.prod isCompact_Icc
  have hKU : (Icc (0 : ℝ) 1 ×ˢ Icc (-δ₀) δ₀) ×ˢ ({0} : Set ℝ) ⊆ DomH m d := by
    rintro ⟨⟨τ, δ⟩, t⟩ ⟨⟨hτ, hδ⟩, ht⟩
    have : t = 0 := ht
    subst this
    refine mem_DomH_zero m d ?_
    obtain ⟨h1, h2⟩ := hδ
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic (DomH_isOpen m d)
    (analyticOnNhd_Hc m n d) hK hKU R
  refine ⟨ρ, hρ, C, fun τ hτ δ hδ t ht => ?_⟩
  exact hC (τ, δ) ⟨hτ, abs_le.mp hδ⟩ t ht

/-! ### Polynomiality in `τ` of the Taylor coefficients -/

/-- The `i`-th `τ`-coefficient of the uniform germ (coefficient of `τ^i` in `Hc`). -/
noncomputable def Kc (m n : ℚ) (d i : ℕ) (δ t : ℝ) : ℝ :=
  (Real.sqrt (piSixT (m + d) ((1 + δ) / 2) ((1 - δ) / 2) t))⁻¹ *
    MvPolynomial.eval ![t / ((1 + δ) / 2) ^ 2, t / ((1 - δ) / 2) ^ 2,
      t / (((1 + δ) / 2) * ((1 - δ) / 2))] ((ptPoly m n d).coeff i)

lemma Hc_eq_sum (m n : ℚ) (d : ℕ) (τ δ t : ℝ) :
    Hc m n d τ δ t = ∑ i ∈ Finset.range (d + 1), τ ^ i * Kc m n d i δ t := by
  unfold Hc
  rw [ptilde6_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Kc
  ring

/-- The domain of `Kc` in `(δ, t)`. -/
def DomK (m : ℚ) (d : ℕ) : Set (ℝ × ℝ) :=
  {p | |p.1| < 1 ∧ 0 < piSixT (m + d) ((1 + p.1) / 2) ((1 - p.1) / 2) p.2}

lemma DomK_isOpen (m : ℚ) (d : ℕ) : IsOpen (DomK m d) := by
  have hV : IsOpen {p : ℝ × ℝ | |p.1| < 1} := isOpen_lt (by fun_prop) continuous_const
  have hg : ContinuousOn (fun q : ℝ × ℝ => piSixT (m + d) ((1 + q.1) / 2) ((1 - q.1) / 2) q.2)
      {p : ℝ × ℝ | |p.1| < 1} := by
    intro p hp
    have := abs_lt_one_alpha hp
    have a1 : AnalyticAt ℝ (fun q : ℝ × ℝ => (1 + q.1) / 2) p :=
      (analyticAt_const.add analyticAt_fst).div_const
    have a2 : AnalyticAt ℝ (fun q : ℝ × ℝ => (1 - q.1) / 2) p :=
      (analyticAt_const.sub analyticAt_fst).div_const
    exact (analyticAt_piSixT_comp (m + d) a1 a2 analyticAt_snd this.1.ne'
      this.2.ne').continuousAt.continuousWithinAt
  have := hg.isOpen_inter_preimage hV (isOpen_Ioi (a := (0 : ℝ)))
  convert this using 1
  ext p
  simp only [DomK, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]

theorem analyticAt_Kc (m n : ℚ) (d i : ℕ) {p : ℝ × ℝ} (hp : p ∈ DomK m d) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Kc m n d i q.1 q.2) p := by
  obtain ⟨hδ, hP⟩ := hp
  obtain ⟨hα, hβ⟩ := abs_lt_one_alpha hδ
  have a1 : AnalyticAt ℝ (fun q : ℝ × ℝ => (1 + q.1) / 2) p :=
    (analyticAt_const.add analyticAt_fst).div_const
  have a2 : AnalyticAt ℝ (fun q : ℝ × ℝ => (1 - q.1) / 2) p :=
    (analyticAt_const.sub analyticAt_fst).div_const
  have at_ : AnalyticAt ℝ (fun q : ℝ × ℝ => q.2) p := analyticAt_snd
  have hsP := analyticAt_sqrt_comp
    (analyticAt_piSixT_comp (m + d) a1 a2 at_ hα.ne' hβ.ne') hP
  have hsP' : AnalyticAt ℝ (fun q : ℝ × ℝ =>
      (Real.sqrt (piSixT (m + d) ((1 + q.1) / 2) ((1 - q.1) / 2) q.2))⁻¹) p :=
    hsP.inv (Real.sqrt_pos.mpr hP).ne'
  have hev := analyticAt_mvEval (x := p) (u := fun q : ℝ × ℝ => q.2 / ((1 + q.1) / 2) ^ 2)
    (v := fun q : ℝ × ℝ => q.2 / ((1 - q.1) / 2) ^ 2)
    (w := fun q : ℝ × ℝ => q.2 / (((1 + q.1) / 2) * ((1 - q.1) / 2)))
    (AnalyticAt.div at_ (a1.pow 2) (pow_ne_zero 2 hα.ne'))
    (AnalyticAt.div at_ (a2.pow 2) (pow_ne_zero 2 hβ.ne'))
    (AnalyticAt.div at_ (a1.mul a2) (mul_ne_zero hα.ne' hβ.ne')) ((ptPoly m n d).coeff i)
  exact hsP'.mul hev

theorem analyticOnNhd_Kc (m n : ℚ) (d i : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ × ℝ => Kc m n d i q.1 q.2) (DomK m d) :=
  fun _ hp => analyticAt_Kc m n d i hp

/-- The coefficient of `τ^i` in `s_r(τ; δ)`: the `t^r` Taylor coefficient of `Kc`. -/
noncomputable def cKc (m n : ℚ) (d i r : ℕ) (δ : ℝ) : ℝ :=
  taylorCoeff (fun (δ t : ℝ) => Kc m n d i δ t) r δ

/-- The `τ`-coefficients of `s_r` are real analytic in `δ ∈ (-1,1)` (the paper: "coefficients
rational in `δ` with poles only at `δ = ±1`"; Lean proves analyticity on `(-1,1)` only, see the
report). -/
theorem analyticOnNhd_cKc (m n : ℚ) (d i r : ℕ) :
    AnalyticOnNhd ℝ (cKc m n d i r) (Ioo (-1 : ℝ) 1) := by
  have h := analyticOnNhd_taylorCoeff (DomK_isOpen m d) (analyticOnNhd_Kc m n d i) r
  refine h.mono (fun δ hδ => ?_)
  refine ⟨abs_lt.mpr hδ, ?_⟩
  simp [piSixT_zero]

/-- **`s_r(τ; δ)` is a polynomial of degree at most `d` in `τ`** whose coefficients are the
analytic functions `cKc … i r δ` of `δ ∈ (-1,1)`. -/
theorem s6c_eq_sum (m n : ℚ) (d r : ℕ) (τ : ℝ) {δ : ℝ} (hδ : |δ| < 1) :
    s6c m n d r τ δ = ∑ i ∈ Finset.range (d + 1), cKc m n d i r δ * τ ^ i := by
  have hslice : ∀ i : ℕ, ContDiffAt ℝ r (fun t : ℝ => Kc m n d i δ t) 0 := by
    intro i
    have h1 := analyticAt_Kc m n d i (p := (δ, 0)) (by
      refine ⟨hδ, ?_⟩; simp [piSixT_zero])
    have h2 : AnalyticAt ℝ (fun t : ℝ => ((δ, t) : ℝ × ℝ)) 0 :=
      analyticAt_const.prod analyticAt_id
    have h3 := h1.comp_of_eq h2 rfl
    exact h3.contDiffAt
  unfold s6c taylorCoeff
  have e : (fun t : ℝ => Hc m n d τ δ t) =
      fun t : ℝ => ∑ i ∈ Finset.range (d + 1), τ ^ i * Kc m n d i δ t := by
    funext t; exact Hc_eq_sum m n d τ δ t
  show iteratedDeriv r (fun t : ℝ => Hc m n d τ δ t) 0 / (r.factorial : ℝ) = _
  rw [e, iteratedDeriv_fun_sum (f := fun i t => τ ^ i * Kc m n d i δ t)
    (I := Finset.range (d + 1)) (fun i _ => contDiffAt_const.mul (hslice i)), Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul (τ ^ i) (hslice i)]
  unfold cKc taylorCoeff
  ring

/-! ### The exact identity `Phi6 = E W · Hall` in every chamber -/

lemma cosA_comm' (A B C : ℝ) : cosA B A C = cosA A B C := by
  unfold cosA; ring

/-- The carrier with the edge factor extracted, shape variables `(τ, δ, t)`, `δ = (A-B)/(A+B)`,
`t = (A+B)⁻²`. -/
theorem carrierV_edge (m n : ℚ) (d : ℕ) (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) :
    carrierV m n A B C (m + d) d =
      edgeFac m n A B C * Hc m n d ((1 - cosA A B C) / 2) ((A - B) / (A + B)) (1 / (A + B) ^ 2) := by
  have hS : 0 < A + B := by linarith
  have ea : (1 + (A - B) / (A + B)) / 2 = A / (A + B) := by field_simp; ring
  have eb : (1 - (A - B) / (A + B)) / 2 = B / (A + B) := by field_simp; ring
  unfold carrierV Hc
  rw [ea, eb, piSix_shape _ A B (A + B) hA.ne' hB.ne' hS.ne']
  have e1 : 1 / A ^ 2 = 1 / (A + B) ^ 2 / (A / (A + B)) ^ 2 := by field_simp
  have e2 : 1 / B ^ 2 = 1 / (A + B) ^ 2 / (B / (A + B)) ^ 2 := by field_simp
  have e3 : 1 / (A * B) = 1 / (A + B) ^ 2 / (A / (A + B) * (B / (A + B))) := by field_simp
  rw [e1, e2, e3]
  ring

lemma cast_floor_abs_Q {x : ℚ} {k : ℤ} (hx : x = k) : ((⌊|x|⌋₊ : ℕ) : ℚ) = |x| := by
  subst hx
  rw [← natAbs_cast_rat, Nat.floor_natCast]

lemma edgeFac_chamber (m' n' : ℚ) (p q : ℕ) (hp : m' - n' = p) (hq : m' + n' = q) {A B C : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : ((p : ℝ) + 1) / 2 ≤ A - B + C) (h2 : ((p : ℝ) + 1) / 2 ≤ -A + B + C)
    (h3 : ((q : ℝ) + 1) / 2 ≤ A + B - C) (h4 : ((q : ℝ) + 1) / 2 ≤ A + B + C) :
    edgeFac m' n' A B C = edgeEW p q A B C :=
  edgeEW_eq_edgeFac m' n' p q hp hq hA hB h1 h2 h3 h4

/-- Swapped-order version: `edgeFac m' n' B A C = E W (A,B,C)`. -/
lemma edgeFac_chamber_swap (m' n' : ℚ) (p q : ℕ) (hp : m' - n' = p) (hq : m' + n' = q) {A B C : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : ((p : ℝ) + 1) / 2 ≤ A - B + C) (h2 : ((p : ℝ) + 1) / 2 ≤ -A + B + C)
    (h3 : ((q : ℝ) + 1) / 2 ≤ A + B - C) (h4 : ((q : ℝ) + 1) / 2 ≤ A + B + C) :
    edgeFac m' n' B A C = edgeEW p q A B C := by
  rw [edgeEW_eq_edgeFac m' n' p q hp hq hB hA (by linarith) (by linarith) (by linarith)
    (by linarith)]
  unfold edgeEW edgeE edgeW
  rw [cosA_comm']
  have e1 : B - A + C = -A + B + C := by ring
  have e2 : -B + A + C = A - B + C := by ring
  have e3 : B + A - C = A + B - C := by ring
  have e4 : B + A + C = A + B + C := by ring
  rw [e1, e2, e3, e4]
  ring

/-- The chamber-reduced uniform germ (signs and `α ↔ β` swaps of `carrierAll`; the swap sends
`δ ↦ -δ`). -/
noncomputable def Hall (f m n : ℚ) (τ δ t : ℝ) : ℝ :=
  if |n| ≤ m then Hc m n ⌊f - m⌋₊ τ δ t
  else if |n| ≤ -m then (-1 : ℝ) ^ ⌊m - n⌋ * Hc (-m) (-n) ⌊f + m⌋₊ τ δ t
  else if |m| ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ * Hc n m ⌊f - n⌋₊ τ (-δ) t
  else Hc (-n) (-m) ⌊f + n⌋₊ τ (-δ) t

/-- The coefficients `s_r(τ; δ)` of `thm:uniformedge`(b), every chamber. -/
noncomputable def s6 (f m n : ℚ) (r : ℕ) (τ δ : ℝ) : ℝ :=
  if |n| ≤ m then s6c m n ⌊f - m⌋₊ r τ δ
  else if |n| ≤ -m then (-1 : ℝ) ^ ⌊m - n⌋ * s6c (-m) (-n) ⌊f + m⌋₊ r τ δ
  else if |m| ≤ n then (-1 : ℝ) ^ ⌊m - n⌋ * s6c n m ⌊f - n⌋₊ r τ (-δ)
  else s6c (-n) (-m) ⌊f + n⌋₊ r τ (-δ)

/-- **Edge-factorised exact identity** (`lem:sqrtfreecarrier` + `eq:6jEdgeFactors`): at every
physical point and in every chamber,
`Φ_f = E_{A,B}(C) W_{6j}(x) · Hall f m n τ δ t`, with `p_min = ⌊|m-n|⌋₊`, `p_max = ⌊|m+n|⌋₊`,
`τ = (1-x)/2`, `δ = (A-B)/(A+B)`, `t = (A+B)⁻²`. -/
theorem Phi6_edge_factor (a b c f m n : ℚ) (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n =
      edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
        Hall f m n ((1 - cosA (wA a n) (wB b m) (wC c)) / 2)
          ((wA a n - wB b m) / (wA a n + wB b m)) (1 / (wA a n + wB b m) ^ 2) := by
  obtain ⟨hA, hB, hC, -⟩ := physical_scale_pos h1 h2 h3
  obtain ⟨e1, e2, e3, e4⟩ := phys_edge_args h1 h2 h3 h4
  obtain ⟨k, hk⟩ := exists_int_sub h1 h2
  obtain ⟨l, hl⟩ := exists_int_add h1 h2
  have hpQ := cast_floor_abs_Q hk
  have hqQ := cast_floor_abs_Q hl
  obtain ⟨n1, n2, n3, n4⟩ := four_nat h1 h2
  rw [Phi6_carrier_all a b c f m n h1 h2 h3 h4]
  unfold carrierAll Hall
  set A := wA a n
  set B := wB b m
  set C := wC c
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    obtain ⟨-, hfd⟩ := canon_labels c1 n2 n3 n4
    have := carrierV_edge m n ⌊f - m⌋₊ A B C hA hB
    rw [← hfd] at this
    rw [this, edgeFac_chamber m n _ _ (by rw [hpQ, abs_of_nonneg (by linarith [(abs_le.mp c1).2,
      (abs_le.mp c1).1])]) (by rw [hqQ, abs_of_nonneg (by linarith [(abs_le.mp c1).2,
      (abs_le.mp c1).1])]) hA.ne' hB.ne' e1 e2 e3 e4]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    have c2' : |-n| ≤ -m := by simpa using c2
    obtain ⟨-, hfd⟩ := canon_labels (f := f) (m := -m) (n := -n) c2' (by simpa using n1)
      (by simpa [sub_eq_add_neg] using n4) (by simpa using n3)
    have hfd' : f = -m + ((⌊f + m⌋₊ : ℕ) : ℚ) := by simpa only [sub_neg_eq_add] using hfd
    have := carrierV_edge (-m) (-n) ⌊f + m⌋₊ A B C hA hB
    rw [← hfd'] at this
    have hb := abs_le.mp c2
    rw [this, edgeFac_chamber (-m) (-n) _ _ (by rw [hpQ, abs_of_nonpos (by linarith [hb.1, hb.2])]; ring)
      (by rw [hqQ, abs_of_nonpos (by linarith [hb.1, hb.2])]; ring) hA.ne' hB.ne' e1 e2 e3 e4]
    ring
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨-, hfd⟩ := canon_labels (f := f) (m := n) (n := m) c3 n4 n1 n2
    have := carrierV_edge n m ⌊f - n⌋₊ B A C hB hA
    rw [← hfd] at this
    have hb := abs_le.mp c3
    rw [this, edgeFac_chamber_swap n m _ _ (by rw [hpQ, abs_of_nonpos (by linarith [hb.1, hb.2])]; ring)
      (by rw [hqQ, abs_of_nonneg (by linarith [hb.1, hb.2])]; ring) hA.ne' hB.ne' e1 e2 e3 e4,
      cosA_comm']
    have : (B - A) / (B + A) = -((A - B) / (A + B)) := by rw [add_comm B A]; ring
    rw [this, add_comm B A]
    ring
  · have c4 : |m| ≤ -n := by
      rcases le_total 0 n with hn | hn
      · rw [abs_of_nonneg hn] at c1 c2
        exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
      · rw [abs_of_nonpos hn] at c1 c2
        rw [abs_le]; push Not at c1 c2; constructor <;> linarith
    simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨-, hfd⟩ := canon_labels (f := f) (m := -n) (n := -m) (by simpa using c4)
      (by simpa using n3) (by simpa [sub_eq_add_neg] using n2) (by simpa using n1)
    have hfd' : f = -n + ((⌊f + n⌋₊ : ℕ) : ℚ) := by simpa only [sub_neg_eq_add] using hfd
    have := carrierV_edge (-n) (-m) ⌊f + n⌋₊ B A C hB hA
    rw [← hfd'] at this
    have hb := abs_le.mp c4
    rw [this, edgeFac_chamber_swap (-n) (-m) _ _ (by rw [hpQ, abs_of_nonneg (by linarith [hb.1, hb.2])]; ring)
      (by rw [hqQ, abs_of_nonpos (by linarith [hb.1, hb.2])]; ring) hA.ne' hB.ne' e1 e2 e3 e4,
      cosA_comm']
    have : (B - A) / (B + A) = -((A - B) / (A + B)) := by rw [add_comm B A]; ring
    rw [this, add_comm B A]

/-! ### `thm:uniformedge`(b) -/

lemma sign_bound (σ : ℝ) (hσ : |σ| = 1) (H : ℝ) (S : ℕ → ℝ) (R : ℕ) (t B : ℝ)
    (h : |H - ∑ r ∈ Finset.range R, S r * t ^ r| ≤ B) :
    |σ * H - ∑ r ∈ Finset.range R, (σ * S r) * t ^ r| ≤ B := by
  have : σ * H - ∑ r ∈ Finset.range R, (σ * S r) * t ^ r =
      σ * (H - ∑ r ∈ Finset.range R, S r * t ^ r) := by
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_assoc]
  rw [this, abs_mul, hσ, one_mul]
  exact h

lemma abs_neg_one_zpow' (k : ℤ) : |(-1 : ℝ) ^ k| = 1 := by
  rw [abs_zpow, abs_neg, abs_one, one_zpow]

/-- **Uniform Taylor remainder for the chamber-reduced germ** on `τ ∈ [0,1]`, `|δ| ≤ δ₀ < 1`. -/
theorem Hall_taylor_uniform (f m n : ℚ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (R : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) 1, ∀ δ : ℝ, |δ| ≤ δ₀ → ∀ t : ℝ, |t| ≤ ρ →
      |Hall f m n τ δ t - ∑ r ∈ Finset.range R, s6 f m n r τ δ * t ^ r| ≤ C * |t| ^ R := by
  unfold Hall s6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    exact Hc_taylor_uniform m n _ hδ₀ R
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    obtain ⟨ρ, hρ, C, hC⟩ := Hc_taylor_uniform (-m) (-n) ⌊f + m⌋₊ hδ₀ R
    exact ⟨ρ, hρ, C, fun τ hτ δ hδ t ht =>
      sign_bound _ (abs_neg_one_zpow' _) _ _ R t _ (hC τ hτ δ hδ t ht)⟩
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨ρ, hρ, C, hC⟩ := Hc_taylor_uniform n m ⌊f - n⌋₊ hδ₀ R
    exact ⟨ρ, hρ, C, fun τ hτ δ hδ t ht =>
      sign_bound _ (abs_neg_one_zpow' _) _ _ R t _ (hC τ hτ (-δ) (by rwa [abs_neg]) t ht)⟩
  · simp only [c1, c2, c3, ↓reduceIte]
    obtain ⟨ρ, hρ, C, hC⟩ := Hc_taylor_uniform (-n) (-m) ⌊f + n⌋₊ hδ₀ R
    exact ⟨ρ, hρ, C, fun τ hτ δ hδ t ht => hC τ hτ (-δ) (by rwa [abs_neg]) t ht⟩

lemma tau_mem_Icc {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) {p q : ℕ}
    (h1 : ((p : ℝ) + 1) / 2 ≤ A - B + C) (h2 : ((p : ℝ) + 1) / 2 ≤ -A + B + C)
    (h3 : ((q : ℝ) + 1) / 2 ≤ A + B - C) (_h4 : ((q : ℝ) + 1) / 2 ≤ A + B + C) :
    (1 - cosA A B C) / 2 ∈ Icc (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < ((p : ℝ) + 1) / 2 := by positivity
  have hq : (0 : ℝ) < ((q : ℝ) + 1) / 2 := by positivity
  have e1 : (1 - cosA A B C) / 2 = (A - B + C) * (-A + B + C) / (4 * A * B) := by
    unfold cosA; field_simp; ring
  have e2 : (1 + cosA A B C) / 2 = (A + B - C) * (A + B + C) / (4 * A * B) := by
    unfold cosA; field_simp; ring
  have hAB : 0 < 4 * A * B := by positivity
  constructor
  · rw [e1]; exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hAB.le
  · have : 0 ≤ (1 + cosA A B C) / 2 := by
      rw [e2]; exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hAB.le
    linarith

lemma delta_abs_le {A B lam : ℝ} (hlam : 0 < lam) (hA : 0 < A) (hB : 0 < B)
    (h1 : lam * B ≤ A) (h2 : A ≤ B / lam) : |(A - B) / (A + B)| ≤ (1 - lam) / (1 + lam) := by
  have h2' : lam * A ≤ B := by rwa [le_div_iff₀ hlam, mul_comm] at h2
  have hS : 0 < A + B := by linarith
  rw [abs_div, abs_of_pos hS, div_le_div_iff₀ hS (by linarith)]
  rcases abs_cases (A - B) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith

/-- **`thm:uniformedge`(b), `eq:6juniformedge`** (proved, Lean form; all chambers).  Fix `f, m, n`,
`0 < λ < 1` and `R`.  There are `C, S₀` such that for every physical admissible point
(the four triads of the `6j` family) with `λ ≤ A/B ≤ λ⁻¹` and `S = A + B ≥ S₀`, writing
`τ = (1 - cosA A B C)/2`, `δ = (A-B)/(A+B)`, `p_min = ⌊|m-n|⌋₊`, `p_max = ⌊|m+n|⌋₊`,
`|Φ_f - E_{A,B}(C) W_{6j}(x) ∑_{r<R} s_r(τ;δ) S^{-2r}| ≤ C · E W · S^{-2R}`.
The remainder is relative to `E W`, uniformly on the whole physical `c`-lattice (`τ ∈ [0,1]`
is proved from the physical triads: no separation from the edges is assumed).  The coefficients
`s_r = s6 f m n r` are polynomials of degree at most `d` in `τ` with coefficients analytic in
`δ ∈ (-1,1)` (`s6c_eq_sum`, `analyticOnNhd_cKc`); that they are rational in `δ` with poles only
at `±1` is *not* proved here.  `E W = edgeFac` of the carrier (`edgeEW_eq_edgeFac`), and
`0 < c ≤ E ≤ 1` is `edgeE_bounds`. -/
theorem Phi6_uniform_edge (f m n : ℚ) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (R : ℕ) :
    ∃ C S₀ : ℝ, ∀ a b c : ℚ, IsTri f (b + m) b → IsTri f a (a + n) → IsTri c a b →
      IsTri c (b + m) (a + n) → lam * wB b m ≤ wA a n → wA a n ≤ wB b m / lam →
      S₀ ≤ wA a n + wB b m →
      |Phi6 a b c f m n - edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) *
          ∑ r ∈ Finset.range R,
            s6 f m n r ((1 - cosA (wA a n) (wB b m) (wC c)) / 2)
              ((wA a n - wB b m) / (wA a n + wB b m)) / (wA a n + wB b m) ^ (2 * r)| ≤
        C * edgeEW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) /
          (wA a n + wB b m) ^ (2 * R) := by
  have hδ₀ : (1 - lam) / (1 + lam) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  obtain ⟨ρ, hρ, C, hC⟩ := Hall_taylor_uniform f m n hδ₀ R
  refine ⟨C, max 1 (1 / ρ), ?_⟩
  intro a b c h1 h2 h3 h4 hl1 hl2 hS0
  obtain ⟨hA, hB, hC', hSpos⟩ := physical_scale_pos h1 h2 h3
  obtain ⟨e1, e2, e3, e4⟩ := phys_edge_args h1 h2 h3 h4
  set A := wA a n
  set B := wB b m
  set Cc := wC c
  set p := ⌊|m - n|⌋₊
  set q := ⌊|m + n|⌋₊
  have hS : 0 < A + B := by linarith
  have hS1 : 1 ≤ A + B := le_trans (le_max_left _ _) hS0
  have hS2 : 1 / ρ ≤ A + B := le_trans (le_max_right _ _) hS0
  have ht : |1 / (A + B) ^ 2| ≤ ρ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h3' : A + B ≤ (A + B) ^ 2 := by nlinarith
    have h4' : 1 / ρ ≤ (A + B) ^ 2 := le_trans hS2 h3'
    rw [div_le_iff₀ hρ] at h4'
    linarith
  have hτ := tau_mem_Icc hA hB e1 e2 e3 e4
  have hδ := delta_abs_le hlam0 hA hB hl1 hl2
  have key := hC _ hτ _ hδ _ ht
  rw [Phi6_edge_factor a b c f m n h1 h2 h3 h4]
  have hE : 0 ≤ edgeEW p q A B Cc := by
    unfold edgeEW edgeE edgeW
    have := edgeR_pos p e1; have := edgeR_pos p e2; have := edgeR_pos q e3; have := edgeR_pos q e4
    positivity
  have e5 : ∀ r : ℕ, s6 f m n r ((1 - cosA A B Cc) / 2) ((A - B) / (A + B)) / (A + B) ^ (2 * r) =
      s6 f m n r ((1 - cosA A B Cc) / 2) ((A - B) / (A + B)) * (1 / (A + B) ^ 2) ^ r := by
    intro r
    rw [one_div, inv_pow, ← pow_mul, div_eq_mul_inv]
  simp only [e5]
  have e6 : |1 / (A + B) ^ 2| ^ R = 1 / (A + B) ^ (2 * R) := by
    rw [abs_of_nonneg (by positivity), one_div, inv_pow, ← pow_mul, one_div]
  rw [e6] at key
  rw [← mul_sub, abs_mul, abs_of_nonneg hE]
  calc edgeEW p q A B Cc * _ ≤ edgeEW p q A B Cc * (C * (1 / (A + B) ^ (2 * R))) :=
        mul_le_mul_of_nonneg_left key hE
    _ = C * edgeEW p q A B Cc / (A + B) ^ (2 * R) := by ring

/-- **`0 < c ≤ E ≤ 1` on the physical lattice** (the remark after `thm:uniformedge`): with
`c = c_{p_min}² c_{p_max}² > 0` depending only on `p_min, p_max`. -/
theorem edgeE_bounds (f m n : ℚ) {a b c : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    0 < edgeRlow ⌊|m - n|⌋₊ ^ 2 * edgeRlow ⌊|m + n|⌋₊ ^ 2 ∧
    edgeRlow ⌊|m - n|⌋₊ ^ 2 * edgeRlow ⌊|m + n|⌋₊ ^ 2 ≤
      edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) ∧
    edgeE ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ (wA a n) (wB b m) (wC c) ≤ 1 := by
  obtain ⟨e1, e2, e3, e4⟩ := phys_edge_args h1 h2 h3 h4
  obtain ⟨l1, u1⟩ := edgeR_pos_le_one _ e1
  obtain ⟨l2, u2⟩ := edgeR_pos_le_one _ e2
  obtain ⟨l3, u3⟩ := edgeR_pos_le_one _ e3
  obtain ⟨l4, u4⟩ := edgeR_pos_le_one _ e4
  have p1 := edgeRlow_pos ⌊|m - n|⌋₊
  have p2 := edgeRlow_pos ⌊|m + n|⌋₊
  have q1 := edgeR_pos ⌊|m - n|⌋₊ e1
  have q2 := edgeR_pos ⌊|m - n|⌋₊ e2
  have q3 := edgeR_pos ⌊|m + n|⌋₊ e3
  have q4 := edgeR_pos ⌊|m + n|⌋₊ e4
  refine ⟨by positivity, ?_, ?_⟩
  · unfold edgeE
    calc edgeRlow ⌊|m - n|⌋₊ ^ 2 * edgeRlow ⌊|m + n|⌋₊ ^ 2
        = edgeRlow ⌊|m - n|⌋₊ * edgeRlow ⌊|m - n|⌋₊ * edgeRlow ⌊|m + n|⌋₊ *
          edgeRlow ⌊|m + n|⌋₊ := by ring
      _ ≤ _ := by gcongr
  · unfold edgeE
    exact le_trans (b := 1 * 1 * 1 * 1) (by gcongr) (by norm_num)

/-- At `r = 0` the uniform coefficient is the `t = 0` value of the carrier. -/
lemma s6c_zero (m n : ℚ) (d : ℕ) (τ δ : ℝ) : s6c m n d 0 τ δ = ptilde6 m n τ 0 0 0 d := by
  simp [s6c, taylorCoeff, Hc, piSixT_zero]

lemma dZero6c_eq (m n : ℚ) (d : ℕ) (x : ℝ) :
    dZero6c m n d x = edgeW ⌊m - n⌋₊ ⌊m + n⌋₊ x * ptilde6 m n ((1 - x) / 2) 0 0 0 d := rfl

/-- **`W_{6j} s_0 = d`** (`thm:uniformedge`(b)): `W_{6j}(x) · s_0(τ; δ) = dZero6 f m n x` for
`τ = (1-x)/2`, every `δ`, in every chamber (`dZero6` is the `t = 0` carrier; its identification
with the Wigner `d`-function is a separate statement). -/
theorem edgeW_mul_s6_zero (f m n : ℚ) (x δ : ℝ) :
    edgeW ⌊|m - n|⌋₊ ⌊|m + n|⌋₊ x * s6 f m n 0 ((1 - x) / 2) δ = dZero6 f m n x := by
  unfold s6 dZero6
  by_cases c1 : |n| ≤ m
  · simp only [c1, ↓reduceIte]
    have hb := abs_le.mp c1
    rw [s6c_zero, dZero6c_eq, abs_of_nonneg (by linarith : 0 ≤ m - n),
      abs_of_nonneg (by linarith : 0 ≤ m + n)]
  by_cases c2 : |n| ≤ -m
  · simp only [c1, c2, ↓reduceIte]
    have hb := abs_le.mp c2
    rw [s6c_zero, dZero6c_eq, abs_of_nonpos (by linarith : m - n ≤ 0),
      abs_of_nonpos (by linarith : m + n ≤ 0), neg_sub_neg, ← neg_add]
    ring_nf
  by_cases c3 : |m| ≤ n
  · simp only [c1, c2, c3, ↓reduceIte]
    have hb := abs_le.mp c3
    rw [s6c_zero, dZero6c_eq, abs_of_nonpos (by linarith : m - n ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ m + n), add_comm n m, neg_sub]
    ring_nf
  · have c4 : |m| ≤ -n := by
      rcases le_total 0 n with hn | hn
      · rw [abs_of_nonneg hn] at c1 c2
        exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
      · rw [abs_of_nonpos hn] at c1 c2
        rw [abs_le]; push Not at c1 c2; constructor <;> linarith
    simp only [c1, c2, c3, ↓reduceIte]
    have hb := abs_le.mp c4
    rw [s6c_zero, dZero6c_eq, abs_of_nonneg (by linarith : 0 ≤ m - n),
      abs_of_nonpos (by linarith : m + n ≤ 0), neg_sub_neg, ← neg_add, add_comm n m]

/-- info: 'FormalResearch.Racah.edgeR_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeR_expansion

/-- info: 'FormalResearch.Racah.edgeE_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeE_bounds

/-- info: 'FormalResearch.Racah.Phi6_edge_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_edge_factor

/-- info: 'FormalResearch.Racah.Phi6_uniform_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_uniform_edge

/-- info: 'FormalResearch.Racah.s6c_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms s6c_eq_sum

/-- info: 'FormalResearch.Racah.edgeW_mul_s6_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeW_mul_s6_zero

end FormalResearch.Racah

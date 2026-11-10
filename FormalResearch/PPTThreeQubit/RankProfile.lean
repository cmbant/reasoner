module

public import FormalResearch.PPTThreeQubit.FamilyPPT
public import FormalResearch.PPTThreeQubit.SurfacePPT
public import FormalResearch.PPTThreeQubit.ChiralityUnitary

/-!
# Rank profiles of the first family and of the surface

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex` (`thm:ppt3-family`: rank five, profile
`(5,8,8,8)` in the interior of the PPT window and `(5,7,7,7)` at the endpoints;
`cor:ppt3-extreme6`: `σ_6` has profile `(5,6,6,6)`) and `rank_five_surface.tex`
(`thm:ppt3-orbit`: profile `(5,5,5,5)`).

The rank profile is `(rank ρ, rank ρ^{T_A}, rank ρ^{T_B}, rank ρ^{T_C})` (`rankProfile`), with
`Matrix.rank` over `ℂ`.

Method.  `rank_sandwich_of_leftInv`: `rank (B X B†) = rank X` for `B` with a left inverse.
`rank_unitriangular_diag`: `rank (L D L†) = #{k | d_k ≠ 0}` for `D = diag d ≥ 0` and `L` with a
unit-determinant square submatrix of rows (the `LDL*` factors of `FamilyPPTFactor.lean` and
`SurfacePPTFactor.lean` are unitriangular in a suitable row order).  The cyclic symmetry
(`rhoT_cycShift`, `rhoSurface_cycShift`) transfers the rank of `ρ^{T_A}` to `ρ^{T_B}`, `ρ^{T_C}`; the
local filter reduces `ρ_{τ,a}` to `a = 1`.

Statements.  `ρ_t`, `ρ_{τ,a} = rhoSurface 1 τ a` are the unnormalised operators of the library
(ranks are unaffected by the normalisation).
Headlines: `rank_rhoT`, `rankProfile_rhoT_interior` (`(5,8,8,8)` for `t_- < t < t_+`),
`rankProfile_rhoT_tMinus`, `rankProfile_rhoT_tPlus` (`(5,7,7,7)`), `rankProfile_rhoSurface`
(`(5,5,5,5)` for every `1/√3 < τ < 1`, `a > 0`), `rankProfile_sigma5`, `rankProfile_sigma6`
(`σ_6` of `eq:ppt3-sigma6`, defined here as `sigma6`; `(5,6,6,6)`).  Since the kernel dimension of an
`8 × 8` operator is `8 - rank`, the kernel dimensions at the cuts are `0` (interior), `1` (endpoints),
`2` (`σ_6`) and `3` (surface).

Not covered: minimality of rank five among fully-PPT GME states (low-rank PPT theorem of
Kraus--Cirac--Karnas--Lewenstein / Horodecki--Lewenstein--Vidal--Cirac), which is quoted in the paper.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix ComplexOrder

noncomputable section

/-- The rank profile `(rank ρ, rank ρ^{T_A}, rank ρ^{T_B}, rank ρ^{T_C})` of a three-qubit
operator. -/
def rankProfile (ρ : Matrix (Fin 8) (Fin 8) ℂ) : ℕ × ℕ × ℕ × ℕ :=
  (ρ.rank, (ptA ρ).rank, (ptB ρ).rank, (ptC ρ).rank)

/-! ### General rank lemmas -/

theorem rank_sandwich_of_leftInv {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℂ)
    (hB : ∃ P : Matrix (Fin r) (Fin m) ℂ, P * B = 1) (X : Matrix (Fin r) (Fin r) ℂ) :
    (B * X * Bᴴ).rank = X.rank := by
  obtain ⟨P, hP⟩ := hB
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · have h : X = P * (B * X * Bᴴ) * Pᴴ := by
      have h1 : Bᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hP, conjTranspose_one]
      calc X = (P * B) * X * (Bᴴ * Pᴴ) := by rw [hP, h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    calc X.rank = (P * (B * X * Bᴴ) * Pᴴ).rank := by rw [← h]
      _ ≤ _ := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- A diagonal matrix with nonzero entries (a nonzero scalar times it) does not change the rank
in a sandwich. -/
theorem rank_diag_sandwich {n : ℕ} (f : Fin n → ℂ) (hf : ∀ i, f i ≠ 0) {k : ℕ}
    (M : Matrix (Fin n) (Fin k) ℂ) : (diagonal f * M).rank = M.rank :=
  rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr (by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hf i))

theorem rank_diag_sandwich' {n : ℕ} (f : Fin n → ℂ) (hf : ∀ i, f i ≠ 0) {k : ℕ}
    (M : Matrix (Fin k) (Fin n) ℂ) : (M * diagonal f).rank = M.rank :=
  rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr (by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hf i))

theorem rank_filter_conj (f : Fin 8 → ℂ) (hf : ∀ i, f i ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (M : Matrix (Fin 8) (Fin 8) ℂ) :
    (c • (diagonal f * M * (diagonal f)ᴴ)).rank = M.rank := by
  have hf' : ∀ i, (star f) i ≠ 0 := fun i => by simpa using hf i
  rw [rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc), diagonal_conjTranspose,
    rank_diag_sandwich' _ hf', rank_diag_sandwich _ hf]

/-- `rank (L D L†) = #{k | d_k ≠ 0}` for `D = diag d` with `d ≥ 0` and `L` an `m × r` matrix with a
square submatrix of `r` rows of nonzero determinant. -/
theorem rank_factor_diag {m r : ℕ} (L : Matrix (Fin m) (Fin r) ℂ) (rows : Fin r → Fin m)
    (hdet : (L.submatrix rows id).det ≠ 0) (d : Fin r → ℝ) (hd : ∀ k, 0 ≤ d k) :
    (L * diagonal (fun k => (d k : ℂ)) * Lᴴ).rank = Fintype.card {k // d k ≠ 0} := by
  classical
  set S : Matrix (Fin r) (Fin r) ℂ := diagonal (fun k => ((Real.sqrt (d k) : ℝ) : ℂ)) with hS
  have hD : diagonal (fun k => (d k : ℂ)) = S * Sᴴ := by
    rw [hS, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext k
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd k)]
  have h1 : L * diagonal (fun k => (d k : ℂ)) * Lᴴ = (L * S) * (L * S)ᴴ := by
    rw [hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (L * S).rank = S.rank := by
    apply le_antisymm (rank_mul_le_right _ _)
    have : (L.submatrix rows id * S) = (L * S).submatrix rows id := by
      ext i j; simp [Matrix.mul_apply]
    calc S.rank = (L.submatrix rows id * S).rank :=
          (rank_mul_eq_right_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hdet)).symm
      _ = ((L * S).submatrix rows id).rank := by rw [this]
      _ ≤ _ := rank_submatrix_le _ _ _
  rw [h1, rank_self_mul_conjTranspose, h2, hS, rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by
    simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (hd k)])

/-- `Σ_k d_k |l_k⟩⟨l_k| = L D L†` for the columns `l_k` of `L`. -/
theorem sum_vecMulVec_eq_mul {m r : ℕ} (L : Matrix (Fin m) (Fin r) ℂ) (d : Fin r → ℝ) :
    ∑ k, (d k : ℂ) • vecMulVec (fun i => L i k) (star fun i => L i k) =
      L * diagonal (fun k => (d k : ℂ)) * Lᴴ := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, conjTranspose_apply]
  ring

/-- The cyclic shift of the qubits as a permutation of the indices. -/
def cycEquiv : Fin 8 ≃ Fin 8 where
  toFun := cycShift
  invFun := cycShift ∘ cycShift
  left_inv i := cycShift_cube i
  right_inv i := by
    show cycShift (cycShift (cycShift i)) = i
    exact cycShift_cube i

/-- For a cyclically invariant operator the three partial transposes have the same rank. -/
theorem rank_ptB_eq_ptA (M : Matrix (Fin 8) (Fin 8) ℂ) (h : M.submatrix cycShift cycShift = M) :
    (ptB M).rank = (ptA M).rank := by
  rw [ptB_eq_of_shift_invariant M h]
  exact rank_submatrix (ptA M) cycEquiv cycEquiv

theorem rank_ptC_eq_ptA (M : Matrix (Fin 8) (Fin 8) ℂ) (h : M.submatrix cycShift cycShift = M) :
    (ptC M).rank = (ptA M).rank := by
  rw [ptC_eq_of_shift_invariant M h]
  exact rank_submatrix (ptA M) (cycEquiv.trans cycEquiv) (cycEquiv.trans cycEquiv)

/-- The profile of a cyclically invariant operator is determined by its rank and the rank of
`ρ^{T_A}`. -/
theorem rankProfile_of_cyc {M : Matrix (Fin 8) (Fin 8) ℂ} (h : M.submatrix cycShift cycShift = M)
    {r s : ℕ} (hr : M.rank = r) (hs : (ptA M).rank = s) : rankProfile M = (r, s, s, s) := by
  simp only [rankProfile, hr, hs, rank_ptB_eq_ptA M h, rank_ptC_eq_ptA M h]

/-! ### The first family -/

/-- `ρ_t` has rank five for every `t > 0` (`thm:ppt3-family`). -/
theorem rank_rhoT {t : ℝ} (ht : 0 < t) : (rhoT t).rank = 5 := by
  classical
  have h7 : 0 < 7 * (t + 3) := by positivity
  have hxt : ∀ a : Fin 5, (![t, 3 * t, 3, 3, 1] a / (7 * (t + 3)) : ℝ) ≠ 0 := by
    intro a
    refine (div_pos ?_ h7).ne'
    fin_cases a <;> simp <;> positivity
  unfold rhoT
  rw [rank_sandwich_of_leftInv _ ⟨Lmat, Lmat_mul_Bs 1⟩, Xt, rank_diagonal]
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun a : Fin 5 =>
    Complex.ofReal_ne_zero.mpr (hxt a)))]
  simp

/-- The factor `L_t` of `ρ_t^{T_A}`: its columns are the vectors `lvec t k`. -/
def Lt (t : ℝ) : Matrix (Fin 8) (Fin 8) ℂ := Matrix.of fun i k => lvec t k i

/-- The row order in which `L_t` is unit lower triangular. -/
def rowsT : Fin 8 → Fin 8 := ![0, 3, 5, 6, 1, 2, 4, 7]

theorem det_Lt_rows (t : ℝ) : ((Lt t).submatrix rowsT id).det = 1 := by
  have hlow : ((Lt t).submatrix rowsT id).IsLowerTriangular := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    fin_cases i <;> fin_cases j <;> simp [Lt, rowsT, lvec] at hij' ⊢
  rw [det_of_isLowerTriangular _ hlow]
  simp [Fin.prod_univ_succ, Lt, rowsT, lvec]

/-- The pivots of `ρ_t^{T_A}`: for `3 < t`, `t² < 12` all are nonzero except possibly the fourth
(zero iff `8t² - 15t - 36 = 0`) and the eighth (zero iff `3t² + 4t - 48 = 0`). -/
theorem dpiv_ne_zero {t : ℝ} (h3 : 3 < t) (h12 : t ^ 2 < 12) (k : Fin 8)
    (h4 : k = 3 → 8 * t ^ 2 - 15 * t - 36 ≠ 0) (h8 : k = 7 → 3 * t ^ 2 + 4 * t - 48 ≠ 0) :
    dpiv t k ≠ 0 := by
  have h7 : 0 < 3 * t - 7 := by linarith
  have ht : 0 < t := by linarith
  fin_cases k <;> simp only [dpiv] <;> simp
  · exact ht.ne'
  · exact ⟨⟨(by linarith : t + 3 ≠ 0), h7.ne'⟩, ht.ne'⟩
  · exact ⟨h4 rfl, (by linarith : t + 3 ≠ 0), h7.ne'⟩
  · intro h; nlinarith
  · exact ⟨⟨(by linarith : t - 3 ≠ 0), h8 rfl⟩, by intro h; nlinarith⟩

theorem ptA_rhoT_eq_mul {t : ℝ} (h3 : 3 < t) (h12 : t ^ 2 ≠ 12) :
    ptA (rhoT t) = Lt t * diagonal (fun k => ((1 / (7 * (t + 3)) * dpiv t k : ℝ) : ℂ)) * (Lt t)ᴴ := by
  rw [ptA_rhoT_eq t h3 h12, ← sum_vecMulVec_eq_mul]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-- The rank of `ρ_t^{T_A}` on the PPT interval is the number of nonzero pivots. -/
theorem rank_ptA_rhoT {t : ℝ} (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) :
    (ptA (rhoT t)).rank = Fintype.card {k // dpiv t k ≠ 0} := by
  have h3 : 3 < t := lt_of_lt_of_le three_lt_tMinus h1
  have hp := tPlus_facts t h3 h2
  have h12 : t ^ 2 ≠ 12 := by intro h; nlinarith
  have hc : 0 < 1 / (7 * (t + 3)) := by positivity
  rw [ptA_rhoT_eq_mul h3 h12,
    rank_factor_diag _ rowsT (by rw [det_Lt_rows]; exact one_ne_zero) _
      (fun k => mul_nonneg hc.le (dpiv_nonneg t h1 h2 k))]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => by
    simp only [ne_eq, mul_eq_zero, hc.ne', false_or])

theorem card_ne_seven {k₀ : Fin 8} : Fintype.card {k : Fin 8 // k ≠ k₀} = 7 := by
  simp [Fintype.card_subtype_compl]

/-- **`thm:ppt3-family`, rank profile in the interior of the PPT window:** `(5, 8, 8, 8)`. -/
theorem rankProfile_rhoT_interior {t : ℝ} (h1 : tMinus < t) (h2 : t < tPlus) :
    rankProfile (rhoT t) = (5, 8, 8, 8) := by
  have h3 : 3 < t := lt_trans three_lt_tMinus h1
  have hp := tPlus_facts t h3 h2.le
  have h12 : t ^ 2 < 12 := by nlinarith
  have hm : 0 < 8 * t ^ 2 - 15 * t - 36 := by
    have e : 8 * t ^ 2 - 15 * t - 36 = (t - tMinus) * (8 * t + 8 * tMinus - 15) := by
      linear_combination tMinus_root
    rw [e]
    exact mul_pos (sub_pos.2 h1) (by linarith [three_lt_tMinus])
  have hq : 3 * t ^ 2 + 4 * t - 48 < 0 := by nlinarith [tPlus_root]
  have hr : (ptA (rhoT t)).rank = 8 := by
    rw [rank_ptA_rhoT h1.le h2.le]
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun k : Fin 8 =>
      dpiv_ne_zero h3 h12 k (fun _ => hm.ne') (fun _ => hq.ne)))]
    simp
  exact rankProfile_of_cyc (rhoT_cycShift t) (rank_rhoT (by linarith)) hr

/-- **`thm:ppt3-family`, rank profile at the lower endpoint `t_-`:** `(5, 7, 7, 7)`. -/
theorem rankProfile_rhoT_tMinus : rankProfile (rhoT tMinus) = (5, 7, 7, 7) := by
  have h2 : tMinus ≤ tPlus := (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
  have h3 := three_lt_tMinus
  have hp := tPlus_facts tMinus h3 h2
  have h12 : tMinus ^ 2 < 12 := by nlinarith
  have hq : 3 * tMinus ^ 2 + 4 * tMinus - 48 < 0 := by
    have := tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus
    nlinarith [tPlus_root]
  have hr : (ptA (rhoT tMinus)).rank = 7 := by
    rw [rank_ptA_rhoT le_rfl h2]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun k : Fin 8 => k ≠ 3) (fun k => ?_)),
      card_ne_seven]
    constructor
    · intro h hk
      subst hk
      apply h
      simp [dpiv, tMinus_root]
    · intro hk
      exact dpiv_ne_zero h3 h12 k (fun h => absurd h hk) (fun _ => hq.ne)
  exact rankProfile_of_cyc (rhoT_cycShift tMinus) (rank_rhoT (by linarith)) hr

/-- **`thm:ppt3-family`, rank profile at the upper endpoint `t_+`:** `(5, 7, 7, 7)`. -/
theorem rankProfile_rhoT_tPlus : rankProfile (rhoT tPlus) = (5, 7, 7, 7) := by
  have h1 : tMinus ≤ tPlus := (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
  have h3 := three_lt_tPlus
  have hp := tPlus_facts tPlus h3 le_rfl
  have h12 : tPlus ^ 2 < 12 := by nlinarith
  have hm : 0 < 8 * tPlus ^ 2 - 15 * tPlus - 36 := by
    have e : 8 * tPlus ^ 2 - 15 * tPlus - 36 = (tPlus - tMinus) * (8 * tPlus + 8 * tMinus - 15) := by
      linear_combination tMinus_root
    rw [e]
    exact mul_pos (sub_pos.2 (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus))
      (by linarith [three_lt_tMinus])
  have hr : (ptA (rhoT tPlus)).rank = 7 := by
    rw [rank_ptA_rhoT h1 le_rfl]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun k : Fin 8 => k ≠ 7) (fun k => ?_)),
      card_ne_seven]
    constructor
    · intro h hk
      subst hk
      apply h
      simp only [dpiv]
      simp [tPlus_root]
    · intro hk
      exact dpiv_ne_zero h3 h12 k (fun _ => hm.ne') (fun h => absurd h hk)
  exact rankProfile_of_cyc (rhoT_cycShift tPlus) (rank_rhoT (by linarith)) hr

/-! ### The surface -/

theorem det_surfXw (A V G W E O : ℝ) :
    (surfXw A V G W E O).det = ((A * ((V * W - G ^ 2) * E * O) : ℝ) : ℂ) := by
  simp [surfXw, det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, -mul_eq_mul_left_iff,
    -mul_eq_mul_right_iff]
  ring

theorem rhoQ_eq_sandwich (Q : ℝ) :
    rhoQ Q = Bs 1 * surfXw 1 (qV Q) (qG Q) (qT Q) (qE Q) (qO Q) * (Bs 1)ᴴ := by
  rw [Bs_surfXw_Bs]
  simp [rhoQ]

/-- Strict positivity of the weights in the window `Q > 1`, `Q² > 3`, `k(Q) < 0`. -/
theorem rank_rhoQ {Q : ℝ} (hQ : 1 < Q) (h3 : 3 < Q ^ 2) (hk : qk Q < 0) : (rhoQ Q).rank = 5 := by
  classical
  have hT := qT_pos hQ
  have hN : 0 < Q ^ 2 - 1 := by nlinarith
  have hE : 0 < qE Q := by unfold qE; linarith
  have hO : 0 < qO Q := by
    unfold qO
    exact div_pos (by linarith) (by have : 0 < Q := by linarith
                                    positivity)
  have hVG : 0 < qT Q * qV Q - qG Q ^ 2 := by
    rw [qT_mul_qV_sub (by linarith)]
    have : 0 < (Q ^ 2 - 3) * (-qk Q) := mul_pos (by linarith) (by linarith)
    linarith
  rw [rhoQ_eq_sandwich, rank_sandwich_of_leftInv _ ⟨Lmat, Lmat_mul_Bs 1⟩]
  apply rank_of_det_ne_zero
  rw [det_surfXw]
  have : (1 : ℝ) * ((qV Q * qT Q - qG Q ^ 2) * qE Q * qO Q) ≠ 0 := by
    have : qV Q * qT Q - qG Q ^ 2 = qT Q * qV Q - qG Q ^ 2 := by ring
    rw [this]
    positivity
  exact_mod_cast this

/-- The factor `L_Q` of `ρ_Q^{T_A}`: its columns are the vectors `lq Q k`. -/
def Lq (Q : ℝ) : Matrix (Fin 8) (Fin 5) ℂ := Matrix.of fun i k => lq Q k i

/-- The row order in which `L_Q` is unit lower triangular. -/
def rowsQ : Fin 5 → Fin 8 := ![0, 3, 5, 1, 2]

theorem det_Lq_rows (Q : ℝ) : ((Lq Q).submatrix rowsQ id).det = 1 := by
  have hlow : ((Lq Q).submatrix rowsQ id).IsLowerTriangular := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    fin_cases i <;> fin_cases j <;> simp [Lq, rowsQ, lq] at hij' ⊢
  rw [det_of_isLowerTriangular _ hlow]
  simp [Fin.prod_univ_succ, Lq, rowsQ, lq]

theorem ptA_rhoQ_eq_mul {Q : ℝ} (hQ : 1 < Q) (h3 : 3 ≤ Q ^ 2) :
    ptA (rhoQ Q) = Lq Q * diagonal (fun k => (dpivQ Q k : ℂ)) * (Lq Q)ᴴ := by
  have hQ0 : Q ≠ 0 := by positivity
  have hN : Q ^ 2 - 1 ≠ 0 := by nlinarith
  rw [← sum_vecMulVec_eq_mul]
  ext i j
  rw [ptA_rhoQ_entry Q hQ0 hN i j]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Lq, of_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem dpivQ_ne_zero {Q : ℝ} (hQ : 1 < Q) (h3 : 3 < Q ^ 2) (hk : qk Q < 0) (k : Fin 5) :
    dpivQ Q k ≠ 0 := by
  have hN : 0 < Q ^ 2 - 1 := by nlinarith
  have hQ0 : 0 < Q := by linarith
  have hk' : 0 < -qk Q := by linarith
  have hpos : 0 < dpivQ Q k := by
    fin_cases k <;> simp only [dpivQ]
    · simp
    · show 0 < -qk Q / 4
      exact div_pos hk' (by norm_num)
    · show 0 < -((Q ^ 2 - 3) * (Q ^ 4 + 3) * qk Q) / (4 * Q ^ 2 * (Q ^ 2 - 1) ^ 2)
      have : 0 < (Q ^ 2 - 3) * (Q ^ 4 + 3) * (-qk Q) :=
        mul_pos (mul_pos (by linarith) (by positivity)) hk'
      exact div_pos (by linarith) (by positivity)
    · show 0 < 2 * Q / (Q ^ 2 - 1)
      positivity
    · show 0 < -3 * (Q ^ 2 - 1) * qk Q / (8 * Q ^ 3)
      have : 0 < 3 * (Q ^ 2 - 1) * (-qk Q) := by positivity
      exact div_pos (by linarith) (by positivity)
  exact hpos.ne'

/-- `rank ρ_Q^{T_A} = 5` in the window. -/
theorem rank_ptA_rhoQ {Q : ℝ} (hQ : 1 < Q) (h3 : 3 < Q ^ 2) (hk : qk Q < 0) :
    (ptA (rhoQ Q)).rank = 5 := by
  rw [ptA_rhoQ_eq_mul hQ h3.le,
    rank_factor_diag _ rowsQ (by rw [det_Lq_rows]; exact one_ne_zero) _
      (fun k => dpivQ_nonneg hQ h3.le hk.le k)]
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun k : Fin 5 => dpivQ_ne_zero hQ h3 hk k))]
  simp

/-- **`thm:ppt3-orbit`, rank profile.**  For `1/√3 < τ < 1` and every `a > 0` the operator
`ρ_{τ,a} = ρ(1, τ, a)` (unnormalised) has rank profile `(5, 5, 5, 5)`. -/
theorem rankProfile_rhoSurface {τ : ℝ} (a : ℝ) (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1)
    (ha : 0 < a) : rankProfile (rhoSurface 1 τ a) = (5, 5, 5, 5) := by
  obtain ⟨Q, hQ, h3, hk, hr⟩ := window_Q h1 h2
  have hτ0 : 0 < τ := lt_trans (by positivity) h1
  have hl : (Real.sqrt a⁻¹) ^ 2 = a⁻¹ := Real.sq_sqrt (inv_nonneg.mpr ha.le)
  have hf := rhoSurface_filter one_pos hτ0 h2 ha hl
  rw [mul_one] at hf
  have hl0 : Real.sqrt a⁻¹ ≠ 0 := by
    have : 0 < a⁻¹ := inv_pos.mpr ha
    exact (Real.sqrt_pos.mpr this).ne'
  have hfne := filterDiag_ne_zero hl0
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have r0 : (rhoSurface 1 τ a).rank = 5 := by
    rw [hf, rank_filter_conj _ hfne _ ha', hr]
    exact rank_rhoQ hQ h3 hk
  have r1 : (ptA (rhoSurface 1 τ a)).rank = 5 := by
    rw [hf, ptA_smul, ptA_conj_filterDiag, rank_filter_conj _ hfne _ ha', hr]
    exact rank_ptA_rhoQ hQ h3 hk
  exact rankProfile_of_cyc (rhoSurface_cycShift 1 τ a) r0 r1

theorem rankProfile_smul {c : ℂ} (hc : c ≠ 0) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    rankProfile (c • M) = rankProfile M := by
  have h := mem_nonZeroDivisors_of_ne_zero hc
  simp only [rankProfile, ptA_smul, ptB_smul, ptC_smul, rank_smul_of_mem_nonZeroDivisors _ h]

/-- **`cor:ppt3-extreme5`, rank profile.**  The rational state `σ` has profile `(5, 5, 5, 5)`. -/
theorem rankProfile_sigma5 : rankProfile sigma5 = (5, 5, 5, 5) := by
  rw [sigma5_eq_orbit, rankProfile_smul (by norm_num)]
  exact rankProfile_rhoSurface 2 window_48_55 (by norm_num) (by norm_num)

/-! ### The extreme state `σ_6` of profile `(5, 6, 6, 6)` -/

/-- `a = t_-` in `eq:ppt3-sigma6`. -/
def sigma6A : ℝ := tMinus

/-- `b = 8(9 - a)/5` in `eq:ppt3-sigma6`. -/
def sigma6B : ℝ := 8 * (9 - tMinus) / 5

/-- The normalising denominator `4a + b + 21` of `eq:ppt3-sigma6`. -/
def sigma6N : ℝ := 4 * sigma6A + sigma6B + 21

/-- The coefficient matrix `X_6 = diag(a, b, 3, 3, 1)/(4a + b + 21)` of `σ_6` in the basis
`(u, v, w, e, o)`. -/
def X6 : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal fun k => ((![sigma6A, sigma6B, 3, 3, 1] k / sigma6N : ℝ) : ℂ)

/-- `σ_6 = (a uu† + b vv† + 3 ww† + 3 ee† + oo†)/(4a + b + 21) = B X_6 B†`
(`eq:ppt3-sigma6`, `cor:ppt3-extreme6`). -/
def sigma6 : Matrix (Fin 8) (Fin 8) ℂ := Bs 1 * X6 * (Bs 1)ᴴ

theorem Bs_diag_Bs (d : Fin 5 → ℝ) :
    Bs 1 * diagonal (fun k => (d k : ℂ)) * (Bs 1)ᴴ =
      (d 0 : ℂ) • vecMulVec (uVec 1) (star (uVec 1)) + (d 1 : ℂ) • vecMulVec vVec (star vVec) +
      (d 2 : ℂ) • vecMulVec wVec (star wVec) + (d 3 : ℂ) • vecMulVec eVec (star eVec) +
      (d 4 : ℂ) • vecMulVec oVec (star oVec) := by
  ext i j
  simp only [Bs, bCols, mul_apply, Fin.sum_univ_five, diagonal_apply, conjTranspose_apply, of_apply,
    Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  simp
  ring

theorem sigma6_pos : 0 < sigma6N ∧ 0 < sigma6A ∧ 0 < sigma6B := by
  have h1 := three_lt_tMinus
  have h2 := tMinus_lt_ten_thirds
  refine ⟨?_, ?_, ?_⟩ <;> simp only [sigma6N, sigma6A, sigma6B] <;> linarith

theorem rank_sigma6 : sigma6.rank = 5 := by
  classical
  obtain ⟨hN, hA, hB⟩ := sigma6_pos
  unfold sigma6
  rw [rank_sandwich_of_leftInv _ ⟨Lmat, Lmat_mul_Bs 1⟩, X6, rank_diagonal]
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun a : Fin 5 =>
    Complex.ofReal_ne_zero.mpr ((div_pos (by fin_cases a <;> simp <;> positivity) hN).ne')))]
  simp

/-- The pivots of `σ_6^{T_A}`: those of `ρ_{t_-}^{T_A}`, with the eighth one shifted by the change
`b - 3a` of the weight of `vv†`, which makes it vanish. -/
def pivot6 (k : Fin 8) : ℝ :=
  (dpiv sigma6A k + if k = 7 then sigma6B - 3 * sigma6A else 0) / sigma6N

theorem dpiv_seven_sigma6 : dpiv sigma6A 7 + (sigma6B - 3 * sigma6A) = 0 := by
  have h3 := three_lt_tMinus
  have h12 : tMinus ^ 2 < 12 := by
    have := tPlus_facts tMinus h3 (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
    nlinarith
  have hne : tMinus ^ 2 - 12 ≠ 0 := by intro h; nlinarith
  unfold dpiv sigma6A sigma6B
  simp only [Fin.isValue, Matrix.cons_val]
  field_simp
  linear_combination (4 - tMinus) * tMinus_root

theorem ptA_vecMulVec_vVec :
    ptA (vecMulVec vVec (star vVec)) = vecMulVec vVec (star vVec) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ptA, vecMulVec_apply, vVec]

theorem ptA_add_matrix (M N : Matrix (Fin 8) (Fin 8) ℂ) : ptA (M + N) = ptA M + ptA N := by
  ext i j; simp [ptA]

theorem lvec_seven (t : ℝ) : lvec t 7 = vVec := by
  funext i; fin_cases i <;> rfl

theorem sigma6_eq (hN : sigma6N ≠ 0) :
    sigma6 = ((7 * (sigma6A + 3) / sigma6N : ℝ) : ℂ) • rhoT sigma6A +
      (((sigma6B - 3 * sigma6A) / sigma6N : ℝ) : ℂ) • vecMulVec vVec (star vVec) := by
  have h3 : (sigma6A : ℂ) + 3 ≠ 0 := by
    have := sigma6_pos.2.1
    exact_mod_cast (by linarith : sigma6A + 3 ≠ 0)
  have hN' : (sigma6N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [sigma6, X6, Bs_diag_Bs, rhoT_eq]
  simp only [Fin.isValue, Matrix.cons_val]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem ptA_sigma6_eq_mul :
    ptA sigma6 = Lt sigma6A * diagonal (fun k => (pivot6 k : ℂ)) * (Lt sigma6A)ᴴ := by
  have hN : sigma6N ≠ 0 := sigma6_pos.1.ne'
  have h3' : 3 < tMinus := three_lt_tMinus
  have h3 : 3 < sigma6A := h3'
  have h12 : sigma6A ^ 2 ≠ 12 := by
    have := tPlus_facts tMinus h3' (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
    show tMinus ^ 2 ≠ 12
    intro h; nlinarith
  rw [← sum_vecMulVec_eq_mul, sigma6_eq hN, ptA_add_matrix, ptA_smul, ptA_smul, ptA_vecMulVec_vVec,
    ptA_rhoT_eq sigma6A h3 h12]
  have hpiv : ∀ k, (pivot6 k : ℂ) = ((1 / sigma6N : ℝ) : ℂ) * (dpiv sigma6A k : ℂ) +
      (if k = 7 then (((sigma6B - 3 * sigma6A) / sigma6N : ℝ) : ℂ) else 0) := by
    intro k
    unfold pivot6
    split_ifs <;> push_cast <;> ring
  have h73 : (7 * ((sigma6A : ℂ) + 3)) ≠ 0 := by
    have := sigma6_pos.2.1
    exact_mod_cast (by positivity : (7 * (sigma6A + 3) : ℝ) ≠ 0)
  have hN' : (sigma6N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [hpiv, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_smul, ← Finset.smul_sum]
  have hl7 : (fun i => Lt sigma6A i 7) = vVec := lvec_seven sigma6A
  simp only [hl7]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp
  rfl

theorem pivot6_nonneg (k : Fin 8) : 0 ≤ pivot6 k := by
  have h1 : tMinus ≤ tMinus := le_rfl
  have h2 : tMinus ≤ tPlus := (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
  unfold pivot6
  refine div_nonneg ?_ sigma6_pos.1.le
  by_cases hk : k = 7
  · subst hk
    simp only [ite_true]
    rw [dpiv_seven_sigma6]
  · simp only [hk, ite_false, add_zero]
    exact dpiv_nonneg tMinus h1 h2 k

theorem pivot6_ne_zero_iff (k : Fin 8) : pivot6 k ≠ 0 ↔ k ≠ 3 ∧ k ≠ 7 := by
  have h3 := three_lt_tMinus
  have h2 : tMinus ≤ tPlus := (tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus).le
  have h12 : tMinus ^ 2 < 12 := by
    have := tPlus_facts tMinus h3 h2
    nlinarith
  have hq : 3 * tMinus ^ 2 + 4 * tMinus - 48 < 0 := by
    have := tMinus_lt_ten_thirds.trans ten_thirds_lt_tPlus
    nlinarith [tPlus_root]
  have hN := sigma6_pos.1
  unfold pivot6
  by_cases h7 : k = 7
  · subst h7
    simp [dpiv_seven_sigma6]
  by_cases h3k : k = 3
  · subst h3k
    have : dpiv sigma6A 3 = 0 := by simp [dpiv, sigma6A, tMinus_root]
    simp [this]
  · simp only [h7, ite_false, add_zero, ne_eq, div_eq_zero_iff, hN.ne', or_false, h3k, not_false_eq_true,
      and_self, iff_true]
    exact dpiv_ne_zero h3 h12 k (fun h => absurd h h3k) (fun h => absurd h h7)

/-- **`cor:ppt3-extreme6`, rank profile.**  `σ_6` has rank profile `(5, 6, 6, 6)`. -/
theorem rankProfile_sigma6 : rankProfile sigma6 = (5, 6, 6, 6) := by
  have hcyc : sigma6.submatrix cycShift cycShift = sigma6 := by
    have hN : sigma6N ≠ 0 := sigma6_pos.1.ne'
    rw [sigma6_eq hN]
    ext i j
    have h := congrFun (congrFun (rhoT_cycShift sigma6A) i) j
    have h' : vecMulVec vVec (star vVec) (cycShift i) (cycShift j) = vecMulVec vVec (star vVec) i j := by
      fin_cases i <;> fin_cases j <;> simp [cycShift, vecMulVec_apply, vVec]
    simp only [submatrix_apply, Matrix.add_apply, Matrix.smul_apply] at h ⊢
    rw [h, h']
  have hr : (ptA sigma6).rank = 6 := by
    rw [ptA_sigma6_eq_mul,
      rank_factor_diag _ rowsT (by rw [det_Lt_rows]; exact one_ne_zero) _ pivot6_nonneg]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun k : Fin 8 => k ≠ 3 ∧ k ≠ 7)
      pivot6_ne_zero_iff)]
    decide
  exact rankProfile_of_cyc hcyc rank_sigma6 hr

/-- The explicit member `t = 10/3` has profile `(5, 8, 8, 8)`. -/
theorem rankProfile_rhoT_ten_thirds : rankProfile (rhoT (10 / 3)) = (5, 8, 8, 8) :=
  rankProfile_rhoT_interior tMinus_lt_ten_thirds ten_thirds_lt_tPlus

end

/-- info: 'FormalResearch.PPTThreeQubit.rank_rhoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_rhoT

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_rhoT_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_rhoT_interior

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_rhoT_tMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_rhoT_tMinus

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_rhoT_tPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_rhoT_tPlus

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_rhoT_ten_thirds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_rhoT_ten_thirds

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_rhoSurface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_rhoSurface

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_sigma5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_sigma5

/-- info: 'FormalResearch.PPTThreeQubit.rankProfile_sigma6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankProfile_sigma6

end FormalResearch.PPTThreeQubit

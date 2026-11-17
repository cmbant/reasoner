module

public import FormalResearch.MatrixAnalysis.SpectralResidual

/-!
# Dual-Egorov sign locking (Weyl P5/M7, Theorem 2 of `m7_m1_global_criteria.md`)

Source: `Weyl/P5/notes/m7_m1_global_criteria.md`, Theorem 2, eqs. (2.9)–(2.11) (PR 250, head
`cfad461d2`).

Let `U` be orthogonal with `H U = U Λ` (simple spectrum, gaps `g_d`), `D U = U K` with `K` symmetric
and `|K_{j,j+1}| ≥ k_* > 0`, and `G` any matrix with nonzero columns of norms `t_j ∈ [t_min, t_max]`.
With `η² = ∑_j ‖(HG - GΛ)_{·j}‖²/(t_j² g_j²)`, `ρ = t_max η < t_min`, `η₂ = ‖DG - GK‖_F`, `κ ≥ ‖K‖_{2→2}`
and the sign-locking condition `η₂ + 2κρ < 2√2 k_* √(t_min² - ρ²)`:

* `signLocking` : all diagonal entries of `Uᵀ G` have one common sign `σ` and
  `‖G - σ U‖_{2→2} ≤ (1 + ε)√2 η + ε`   (2.11);
* `sign_anchor` : one entry `G_{i₀j₀}` with the sign of `U_{i₀j₀}` and `ε < |U_{i₀j₀}|` forces `σ = 1`;
* building blocks `offDiag_frobSq_le` (2.13), `diag_sq_ge` (2.14), `commutator_upper` (2.15),
  `no_sign_flip` (the step (2.16)), `common_sign`.

Claim class: proved.  Differences from the note: tridiagonality of `K` is not used (only the lower
bound on the superdiagonal links, since `‖[K,T]‖_F² ≥ 2 K_{j,j+1}² (c_{j+1} - c_j)²` holds for any `K`);
the hypothesis `ε < 1` and the polar-factor bound (2.12) `‖Q - σU‖ ≤ 2ε` are NOT formalised (they need
Weyl's singular-value perturbation inequality, which now exists as
`FormalResearch.MatrixAnalysis.Spectral.singularValues_add_le` / `abs_singularValues_sub_le`, and the
operator-norm polar-factor statement `Spectral.fanHoffman_polar`, but neither (2.12) nor the `ε < 1` form
of Theorem 2 has been derived from them here); the Racah instantiation (`H = h²J^{(a)}`,
`D`, `K = h²J^{(d)}` and the exact bispectral identities) is not formalised.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Frobenius norm `√(∑ M_ij²)`. -/
noncomputable def fnorm (M : Matrix ι ι ℝ) : ℝ := √(frobSq M)

omit [DecidableEq ι] in
theorem frobSq_eq_sum_prod (M : Matrix ι ι ℝ) : frobSq M = ∑ p : ι × ι, M p.1 p.2 ^ 2 := by
  unfold frobSq
  rw [Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem frobSq_transpose (M : Matrix ι ι ℝ) : frobSq Mᵀ = frobSq M := by
  unfold frobSq
  rw [sum_comm]
  rfl

omit [DecidableEq ι] in
theorem fnorm_nonneg (M : Matrix ι ι ℝ) : 0 ≤ fnorm M := Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem fnorm_sub_le (A B : Matrix ι ι ℝ) : fnorm (A - B) ≤ fnorm A + fnorm B := by
  unfold fnorm
  have h1 : frobSq (A - B) = ∑ p : ι × ι, (A p.1 p.2 + (-B) p.1 p.2) ^ 2 := by
    rw [frobSq_eq_sum_prod]; refine sum_congr rfl fun p _ => ?_; simp [sub_eq_add_neg]
  have h2 : frobSq A = ∑ p : ι × ι, A p.1 p.2 ^ 2 := frobSq_eq_sum_prod A
  have h3 : frobSq B = ∑ p : ι × ι, B p.1 p.2 ^ 2 := frobSq_eq_sum_prod B
  rw [h1, h2, h3]
  have := sqrt_sum_sq_add_le' (fun p : ι × ι => A p.1 p.2) (fun p : ι × ι => -B p.1 p.2)
  simpa using this

omit [DecidableEq ι] in
theorem fnorm_add_le (A B : Matrix ι ι ℝ) : fnorm (A + B) ≤ fnorm A + fnorm B := by
  have := fnorm_sub_le A (-B)
  rw [sub_neg_eq_add] at this
  have h : fnorm (-B) = fnorm B := by
    unfold fnorm frobSq; simp
  rwa [h] at this

/-- Orthogonal invariance of the Frobenius norm. -/
theorem fnorm_transpose_mul {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1) (M : Matrix ι ι ℝ) :
    fnorm (Uᵀ * M) = fnorm M := by
  unfold fnorm frobSq
  congr 1
  rw [sum_comm, sum_comm (f := fun i j => M i j ^ 2)]
  refine sum_congr rfl fun j _ => ?_
  have := sum_sq_transpose_mulVec hU (fun i => M i j)
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

omit [DecidableEq ι] in
/-- `‖K O‖_F ≤ κ ‖O‖_F` when `‖K x‖ ≤ κ ‖x‖`. -/
theorem fnorm_mul_le {K : Matrix ι ι ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ x : ι → ℝ, ∑ i, (K *ᵥ x) i ^ 2 ≤ κ ^ 2 * ∑ j, x j ^ 2) (O : Matrix ι ι ℝ) :
    fnorm (K * O) ≤ κ * fnorm O := by
  unfold fnorm
  calc √(frobSq (K * O)) ≤ √(κ ^ 2 * frobSq O) := by
        apply Real.sqrt_le_sqrt
        unfold frobSq
        rw [sum_comm, sum_comm (f := fun i j => O i j ^ 2), mul_sum]
        refine sum_le_sum fun j _ => ?_
        have := hK (fun i => O i j)
        simpa [mulVec, dotProduct, Matrix.mul_apply] using this
    _ = κ * √(frobSq O) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ]

omit [DecidableEq ι] in
/-- `‖O K‖_F ≤ κ ‖O‖_F` for symmetric `K` with `‖K x‖ ≤ κ ‖x‖`. -/
theorem fnorm_mul_le' {K : Matrix ι ι ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hKs : Kᵀ = K)
    (hK : ∀ x : ι → ℝ, ∑ i, (K *ᵥ x) i ^ 2 ≤ κ ^ 2 * ∑ j, x j ^ 2) (O : Matrix ι ι ℝ) :
    fnorm (O * K) ≤ κ * fnorm O := by
  have h1 : fnorm (O * K) = fnorm (K * Oᵀ) := by
    have : (O * K)ᵀ = K * Oᵀ := by rw [transpose_mul, hKs]
    rw [← this]; unfold fnorm; rw [frobSq_transpose]
  have h2 : fnorm Oᵀ = fnorm O := by unfold fnorm; rw [frobSq_transpose]
  rw [h1, ← h2]
  exact fnorm_mul_le hκ hK Oᵀ

section Locking

variable {H U G : Matrix ι ι ℝ} {lam : ι → ℝ}

/-- Spectral coordinates of the columns of the residual `R₁ = H G - G Λ`. -/
theorem resid1_coords (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) (j : ι) :
    ∑ i, ((H * G - G * diagonal lam) i j) ^ 2 = ∑ l, ((lam l - lam j) * (Uᵀ * G) l j) ^ 2 := by
  have := residual_coords hH hU heig (fun i => G i j) j
  have e1 : ∀ i, (H * G - G * diagonal lam) i j = (H *ᵥ (fun i => G i j)) i - lam j * G i j := by
    intro i
    rw [Matrix.sub_apply, Matrix.mul_diagonal]
    simp only [mulVec, dotProduct, Matrix.mul_apply]
    ring
  have e2 : ∀ l, (Uᵀ * G) l j = (Uᵀ *ᵥ (fun i => G i j)) l := by
    intro l; simp [mulVec, dotProduct, Matrix.mul_apply]
  simp only [e1, e2]
  exact this

theorem sum_sq_transpose_mul_col (hU : Uᵀ * U = 1) (j : ι) :
    ∑ l, ((Uᵀ * G) l j) ^ 2 = ∑ i, G i j ^ 2 := by
  have := sum_sq_transpose_mulVec hU (fun i => G i j)
  simpa [mulVec, dotProduct, Matrix.mul_apply] using this

theorem budget_term (j : ι) (ht : 0 < ∑ i, G i j ^ 2) :
    (∑ i, ((H *ᵥ unitCol G j) i - lam j * unitCol G j i) ^ 2) * colNorm G j ^ 2 =
      ∑ i, ((H * G - G * diagonal lam) i j) ^ 2 := by
  have hpos : colNorm G j ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  rw [sum_mul]
  refine sum_congr rfl fun i _ => ?_
  have e : (H *ᵥ unitCol G j) i - lam j * unitCol G j i =
      (H * G - G * diagonal lam) i j / colNorm G j := by
    rw [Matrix.sub_apply, Matrix.mul_diagonal]
    simp only [mulVec, dotProduct, unitCol, Matrix.mul_apply]
    rw [sub_div, sum_div]
    congr 1
    · exact sum_congr rfl fun k _ => by ring
    · ring
  rw [e, div_pow]
  field_simp

/-- The off-diagonal part of a square matrix. -/
def offDiag (C : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.of fun l j => if l = j then 0 else C l j

omit [Fintype ι] in
theorem offDiag_add_diagonal (C : Matrix ι ι ℝ) : C = diagonal (fun j => C j j) + offDiag C := by
  ext l j
  by_cases h : l = j
  · subst h; simp [offDiag]
  · simp [offDiag, h]

/-- The off-diagonal part of `Uᵀ G` is small: `‖O‖_F² ≤ t_max² η²` (eq. (2.13)). -/
theorem offDiag_frobSq_le (hH : Hᵀ = H) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d)) {g : ι → ℝ}
    (hg0 : ∀ d, 0 < g d) (hgap : ∀ d l, l ≠ d → g d ≤ |lam l - lam d|)
    (ht : ∀ d, 0 < ∑ i, G i d ^ 2) {tmax : ℝ} (hmax : ∀ d, colNorm G d ≤ tmax) :
    frobSq (offDiag (Uᵀ * G)) ≤ tmax ^ 2 * residualBudget H lam g G := by
  set Cm := Uᵀ * G with hCm
  have hcolO : ∀ j, ∑ l, offDiag Cm l j ^ 2 ≤
      (∑ i, ((H * G - G * diagonal lam) i j) ^ 2) / g j ^ 2 := by
    intro j
    rw [le_div_iff₀ (sq_pos_of_pos (hg0 j))]
    have h1 := resid1_coords (G := G) hH hU heig j
    rw [h1, sum_mul]
    refine sum_le_sum fun l _ => ?_
    by_cases hl : l = j
    · subst hl; simp [offDiag]
    · simp only [offDiag, Matrix.of_apply, hl, ite_false]
      rw [mul_pow]
      have := hgap j l hl
      have h2 : g j ^ 2 ≤ (lam l - lam j) ^ 2 := by
        rw [← sq_abs (lam l - lam j)]; exact pow_le_pow_left₀ (hg0 j).le this 2
      nlinarith [sq_nonneg (Cm l j)]
  have hb : ∀ j, (∑ i, ((H * G - G * diagonal lam) i j) ^ 2) / g j ^ 2 ≤
      tmax ^ 2 * ((∑ i, ((H *ᵥ unitCol G j) i - lam j * unitCol G j i) ^ 2) / g j ^ 2) := by
    intro j
    rw [← budget_term j (ht j)]
    have : colNorm G j ^ 2 ≤ tmax ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hmax j) 2
    set X := ∑ i, ((H *ᵥ unitCol G j) i - lam j * unitCol G j i) ^ 2 with hX
    have hX0 : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
    have hg2 := sq_pos_of_pos (hg0 j)
    calc X * colNorm G j ^ 2 / g j ^ 2 = (X / g j ^ 2) * colNorm G j ^ 2 := by ring
      _ ≤ (X / g j ^ 2) * tmax ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  unfold frobSq
  rw [sum_comm]
  calc ∑ j, ∑ l, offDiag Cm l j ^ 2 ≤ ∑ j, (∑ i, ((H * G - G * diagonal lam) i j) ^ 2) / g j ^ 2 :=
        sum_le_sum fun j _ => hcolO j
    _ ≤ ∑ j, tmax ^ 2 * ((∑ i, ((H *ᵥ unitCol G j) i - lam j * unitCol G j i) ^ 2) / g j ^ 2) :=
        sum_le_sum fun j _ => hb j
    _ = tmax ^ 2 * residualBudget H lam g G := by rw [← mul_sum]; rfl

/-- Diagonal entries of `Uᵀ G` are bounded below: `c_j² ≥ t_min² - ‖O‖_F²` (eq. (2.14)). -/
theorem diag_sq_ge (hU : Uᵀ * U = 1) (ht : ∀ d, 0 < ∑ i, G i d ^ 2) {tmin : ℝ} (htmin : 0 ≤ tmin)
    (hmin : ∀ d, tmin ≤ colNorm G d) (j : ι) :
    tmin ^ 2 - frobSq (offDiag (Uᵀ * G)) ≤ ((Uᵀ * G) j j) ^ 2 := by
  set Cm := Uᵀ * G with hCm
  have h1 : ∑ l, Cm l j ^ 2 = colNorm G j ^ 2 := by
    rw [hCm, sum_sq_transpose_mul_col hU j]
    exact (Real.sq_sqrt (ht j).le).symm
  have h2 : Cm j j ^ 2 + ∑ l ∈ univ.erase j, Cm l j ^ 2 = ∑ l, Cm l j ^ 2 :=
    add_sum_erase univ (fun l => Cm l j ^ 2) (mem_univ j)
  have h3 : ∑ l ∈ univ.erase j, Cm l j ^ 2 ≤ frobSq (offDiag Cm) := by
    have : ∑ l ∈ univ.erase j, Cm l j ^ 2 = ∑ l, offDiag Cm l j ^ 2 := by
      rw [← sum_erase_add univ (fun l => offDiag Cm l j ^ 2) (mem_univ j)]
      simp only [offDiag, Matrix.of_apply, ite_true]
      simp only [zero_pow two_ne_zero, add_zero]
      refine sum_congr rfl fun l hl => ?_
      have : l ≠ j := (mem_erase.mp hl).1
      simp [this]
    rw [this]
    unfold frobSq
    rw [sum_comm]
    exact single_le_sum (f := fun j' => ∑ l, offDiag Cm l j' ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ j)
  have h4 : tmin ^ 2 ≤ colNorm G j ^ 2 := pow_le_pow_left₀ htmin (hmin j) 2
  nlinarith

/-- The commutator `[K, diag c]` is controlled by the second residual (eq. (2.15)). -/
theorem commutator_upper (hD : Dᵀ = D) (hK : Kᵀ = K) (hU : Uᵀ * U = 1) (hDU : D * U = U * K)
    {κ : ℝ} (hκ : 0 ≤ κ) (hKop : ∀ x : ι → ℝ, ∑ i, (K *ᵥ x) i ^ 2 ≤ κ ^ 2 * ∑ j, x j ^ 2)
    {ρ : ℝ} (hO : fnorm (offDiag (Uᵀ * G)) ≤ ρ) :
    fnorm (K * diagonal (fun j => (Uᵀ * G) j j) - diagonal (fun j => (Uᵀ * G) j j) * K) ≤
      fnorm (D * G - G * K) + 2 * κ * ρ := by
  set Cm := Uᵀ * G with hCm
  set O := offDiag Cm with hO'
  set Tm : Matrix ι ι ℝ := diagonal (fun j => Cm j j) with hTm
  have hUD : Uᵀ * D = K * Uᵀ := by
    have := congrArg Matrix.transpose hDU
    rw [transpose_mul, transpose_mul, hD, hK] at this
    exact this
  have hcomm : K * Cm - Cm * K = Uᵀ * (D * G - G * K) := by
    rw [mul_sub, ← Matrix.mul_assoc Uᵀ D G, ← Matrix.mul_assoc Uᵀ G K, hUD,
      Matrix.mul_assoc K Uᵀ G]
  have hKT : K * Tm - Tm * K = (K * Cm - Cm * K) - (K * O - O * K) := by
    have e : Cm = Tm + O := offDiag_add_diagonal Cm
    rw [e]
    noncomm_ring
  have hnorm1 : fnorm (K * Cm - Cm * K) = fnorm (D * G - G * K) := by
    rw [hcomm]; exact fnorm_transpose_mul hU _
  have hnorm2 : fnorm (K * O - O * K) ≤ 2 * κ * ρ := by
    calc fnorm (K * O - O * K) ≤ fnorm (K * O) + fnorm (O * K) := fnorm_sub_le _ _
      _ ≤ κ * fnorm O + κ * fnorm O :=
          add_le_add (fnorm_mul_le hκ hKop O) (fnorm_mul_le' hκ hK hKop O)
      _ ≤ κ * ρ + κ * ρ := add_le_add (mul_le_mul_of_nonneg_left hO hκ)
          (mul_le_mul_of_nonneg_left hO hκ)
      _ = 2 * κ * ρ := by ring
  rw [hKT]
  calc _ ≤ fnorm (K * Cm - Cm * K) + fnorm (K * O - O * K) := fnorm_sub_le _ _
    _ ≤ _ := by rw [hnorm1]; exact add_le_add le_rfl hnorm2

end Locking

section Signs

variable {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}

/-- Entries of a commutator with a diagonal matrix: a sign flip across a link costs `‖[K,T]‖_F`. -/
theorem comm_diag_lower (hK : Kᵀ = K) (c : Fin n → ℝ) {j l : Fin n} (hjl : j ≠ l) :
    2 * (K j l ^ 2 * (c l - c j) ^ 2) ≤ frobSq (K * diagonal c - diagonal c * K) := by
  have hent : ∀ a b, (K * diagonal c - diagonal c * K) a b = K a b * (c b - c a) := by
    intro a b
    rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring
  rw [frobSq_eq_sum_prod]
  have hne : ((j, l) : Fin n × Fin n) ≠ (l, j) := fun h => hjl (Prod.mk.inj h).1
  calc 2 * (K j l ^ 2 * (c l - c j) ^ 2)
      = (K * diagonal c - diagonal c * K) j l ^ 2 + (K * diagonal c - diagonal c * K) l j ^ 2 := by
        have hs : K l j = K j l := by
          have := congrFun (congrFun hK j) l
          simpa using this
        rw [hent, hent, hs]; ring
    _ = ∑ p ∈ ({(j, l), (l, j)} : Finset (Fin n × Fin n)),
          (K * diagonal c - diagonal c * K) p.1 p.2 ^ 2 := by rw [sum_pair hne]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _

/-- No sign flip across a link: if `|c_j| ≥ γ'` for all `j`, `|K_{j,j+1}| ≥ k_*` and
`‖[K, diag c]‖_F < 2√2 k_* γ'`, then `c_j c_{j+1} > 0`. -/
theorem no_sign_flip (hK : Kᵀ = K) {kstar : ℝ} (hk : 0 < kstar)
    (hklink : ∀ j l : Fin n, (j : ℕ) + 1 = l → kstar ≤ |K j l|) (c : Fin n → ℝ) {γ' : ℝ}
    (hγ' : 0 ≤ γ') (habs : ∀ j, γ' ≤ |c j|)
    (hup : fnorm (K * diagonal c - diagonal c * K) < 2 * √2 * kstar * γ') :
    ∀ j l : Fin n, (j : ℕ) + 1 = l → 0 < c j * c l := by
  intro j l hjl
  by_contra hle
  have hle := not_lt.mp hle
  have hjl' : j ≠ l := fun h => by rw [h] at hjl; omega
  have hfr := comm_diag_lower hK c hjl'
  have hK2 : kstar ^ 2 ≤ K j l ^ 2 := by
    have := hklink j l hjl
    rw [← sq_abs (K j l)]; exact pow_le_pow_left₀ hk.le this 2
  have hd2 : 4 * γ' ^ 2 ≤ (c l - c j) ^ 2 := by
    have hj := habs j
    have hl := habs l
    have : (c l - c j) ^ 2 = (|c l| + |c j|) ^ 2 := by
      have h1 : |c l * c j| = -(c l * c j) :=
        abs_of_nonpos (by linarith [mul_comm (c j) (c l)])
      rw [abs_mul] at h1
      nlinarith [sq_abs (c l), sq_abs (c j)]
    rw [this]
    nlinarith
  have hlow : 8 * kstar ^ 2 * γ' ^ 2 ≤ fnorm (K * diagonal c - diagonal c * K) ^ 2 := by
    unfold fnorm
    rw [Real.sq_sqrt (frobSq_nonneg _)]
    calc 8 * kstar ^ 2 * γ' ^ 2 = 2 * (kstar ^ 2 * (4 * γ' ^ 2)) := by ring
      _ ≤ 2 * (K j l ^ 2 * (c l - c j) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hK2 hd2 (by positivity) (sq_nonneg _)
      _ ≤ _ := hfr
  have h8 : (2 * √2 * kstar * γ') ^ 2 = 8 * kstar ^ 2 * γ' ^ 2 := by
    have : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc (2 * √2 * kstar * γ') ^ 2 = 4 * (√2) ^ 2 * kstar ^ 2 * γ' ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have := pow_lt_pow_left₀ hup (fnorm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
  rw [h8] at this
  linarith

/-- A sequence of nonzero reals whose neighbours have the same sign has one common sign. -/
theorem common_sign (c : Fin n → ℝ) (hne0 : ∀ j, c j ≠ 0)
    (hadj : ∀ j l : Fin n, (j : ℕ) + 1 = l → 0 < c j * c l) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ j, 0 < σ * c j := by
  rcases Nat.eq_zero_or_pos n with h0 | hnpos
  · subst h0; exact ⟨1, by norm_num, fun j => j.elim0⟩
  · set j0 : Fin n := ⟨0, hnpos⟩ with hj0
    have hprod : ∀ k (hk : k < n), 0 < c j0 * c ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro hk; exact mul_self_pos.mpr (hne0 j0)
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hadj ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
        have hck : c ⟨k, by omega⟩ ≠ 0 := hne0 _
        have hck2 : 0 < c ⟨k, by omega⟩ ^ 2 := by positivity
        have h3 := mul_pos h1 h2
        have h4 : c j0 * c ⟨k, by omega⟩ * (c ⟨k, by omega⟩ * c ⟨k + 1, hk⟩) =
            (c j0 * c ⟨k + 1, hk⟩) * c ⟨k, by omega⟩ ^ 2 := by ring
        rw [h4] at h3
        exact (mul_pos_iff_of_pos_right hck2).mp h3
    refine ⟨if 0 < c j0 then 1 else -1, by split_ifs <;> norm_num, fun j => ?_⟩
    have hj := hprod j.1 j.2
    by_cases hc : 0 < c j0
    · simp only [hc, ite_true, one_mul]
      exact (mul_pos_iff_of_pos_left hc).mp hj
    · have hc' : c j0 < 0 := lt_of_le_of_ne (not_lt.mp hc) (hne0 j0)
      simp only [hc, ite_false]
      have : c j < 0 := by
        by_contra hcon
        have := not_lt.mp hcon
        nlinarith
      linarith

end Signs

section Final

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {U G : Matrix ι ι ℝ}

omit [DecidableEq ι] in
theorem overlapSign_eq (ht : ∀ d, 0 < ∑ i, G i d ^ 2) {σ : ℝ} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ d, 0 < σ * (Uᵀ * G) d d) (d : ι) : overlapSign U G d = σ := by
  have hσ' : σ = 1 ∨ σ = -1 := by
    have : σ * σ = 1 := by rw [← sq]; exact hσ2
    exact mul_self_eq_one_iff.mp this
  have htd : 0 < colNorm G d := Real.sqrt_pos.mpr (ht d)
  have hcd : (Uᵀ *ᵥ unitCol G d) d = (Uᵀ * G) d d / colNorm G d := by
    simp only [mulVec, dotProduct, unitCol, Matrix.mul_apply, Matrix.transpose_apply]
    rw [sum_div]
    exact sum_congr rfl fun i _ => by ring
  unfold overlapSign
  rw [hcd]
  rcases hσ' with h | h
  · have := hσ d
    rw [h, one_mul] at this
    have h0 : 0 ≤ (Uᵀ * G) d d / colNorm G d := by positivity
    simp [h0, h]
  · have := hσ d
    rw [h] at this
    have hneg : (Uᵀ * G) d d < 0 := by linarith
    have h0 : ¬ 0 ≤ (Uᵀ * G) d d / colNorm G d := by
      rw [not_le]; exact div_neg_of_neg_of_pos hneg htd
    simp [h0, h]

end Final

open scoped Matrix.Norms.L2Operator

/-- **Theorem 2** (dual-Egorov sign locking), eqs. (2.9)–(2.11) of the note, for a symmetric `K`
with `|K_{j,j+1}| ≥ k_* > 0` (tridiagonality of `K` is not needed for this inequality).
Hypotheses: `H U = U Λ`, `D U = U K`, `U` orthogonal; `t_j = ‖g_j‖ ∈ [t_min, t_max]`,
`η² = residualBudget` (= `∑_j ‖(R₁)_{·j}‖²/(t_j² gap_j²)`, `R₁ = H G - G Λ`, see `budget_term`),
`ρ = t_max η < t_min`, `η₂ = ‖D G - G K‖_F`, `κ ≥ ‖K‖_{2→2}` and the sign-locking condition
`η₂ + 2κρ < 2√2 k_* √(t_min² - ρ²)` (2.10).  Then all diagonal entries of `Uᵀ G` have one common sign
`σ` and `‖G - σ U‖_{2→2} ≤ (1 + ε)√2 η + ε` (2.11), `ε ≥ max_j |t_j - 1|`. -/
theorem signLocking {n : ℕ} {H D K U G : Matrix (Fin n) (Fin n) ℝ} {lam g : Fin n → ℝ}
    (hH : Hᵀ = H) (hD : Dᵀ = D) (hK : Kᵀ = K) (hU : Uᵀ * U = 1)
    (heig : ∀ d, H *ᵥ (fun i => U i d) = lam d • (fun i => U i d))
    (hDU : D * U = U * K) {kstar : ℝ} (hk : 0 < kstar)
    (hklink : ∀ j l : Fin n, (j : ℕ) + 1 = l → kstar ≤ |K j l|)
    {κ : ℝ} (hκ : 0 ≤ κ) (hKop : ∀ x : Fin n → ℝ, ∑ i, (K *ᵥ x) i ^ 2 ≤ κ ^ 2 * ∑ j, x j ^ 2)
    (hg0 : ∀ d, 0 < g d) (hgap : ∀ d l, l ≠ d → g d ≤ |lam l - lam d|)
    (ht : ∀ d, 0 < ∑ i, G i d ^ 2) {tmin tmax : ℝ} (htmax : 0 ≤ tmax)
    (hmin : ∀ d, tmin ≤ colNorm G d) (hmax : ∀ d, colNorm G d ≤ tmax)
    (hρ : tmax * √(residualBudget H lam g G) < tmin)
    (h210 : fnorm (D * G - G * K) + 2 * κ * (tmax * √(residualBudget H lam g G)) <
      2 * √2 * kstar * √(tmin ^ 2 - (tmax * √(residualBudget H lam g G)) ^ 2))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ d, |colNorm G d - 1| ≤ ε) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ (∀ j, 0 < σ * (Uᵀ * G) j j) ∧
      ‖G - σ • U‖ ≤ (1 + ε) * √2 * √(residualBudget H lam g G) + ε := by
  set η := √(residualBudget H lam g G) with hη
  have hbud : 0 ≤ residualBudget H lam g G :=
    sum_nonneg fun d _ => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη2 : η ^ 2 = residualBudget H lam g G := Real.sq_sqrt hbud
  set ρ := tmax * η with hρdef
  have hρ0 : 0 ≤ ρ := mul_nonneg htmax hη0
  have htmin : 0 < tmin := lt_of_le_of_lt hρ0 hρ
  have hfrobO : frobSq (offDiag (Uᵀ * G)) ≤ ρ ^ 2 := by
    have := offDiag_frobSq_le hH hU heig hg0 hgap ht hmax
    rw [hρdef, mul_pow, hη2]; exact this
  have hfnO : fnorm (offDiag (Uᵀ * G)) ≤ ρ := by
    unfold fnorm
    calc √(frobSq (offDiag (Uᵀ * G))) ≤ √(ρ ^ 2) := Real.sqrt_le_sqrt hfrobO
      _ = ρ := Real.sqrt_sq hρ0
  have hdiag : ∀ j, tmin ^ 2 - ρ ^ 2 ≤ ((Uᵀ * G) j j) ^ 2 := fun j =>
    le_trans (by linarith) (diag_sq_ge hU ht htmin.le hmin j)
  have hnormT := commutator_upper (G := G) hD hK hU hDU hκ hKop hfnO
  set γ' := √(tmin ^ 2 - ρ ^ 2) with hγ'
  have hγ'0 : 0 ≤ γ' := Real.sqrt_nonneg _
  have habs : ∀ j, γ' ≤ |(Uᵀ * G) j j| := by
    intro j
    calc γ' ≤ √((Uᵀ * G) j j ^ 2) := Real.sqrt_le_sqrt (hdiag j)
      _ = |(Uᵀ * G) j j| := Real.sqrt_sq_eq_abs _
  have hpos : 0 < tmin ^ 2 - ρ ^ 2 := by nlinarith
  have hγ'pos : 0 < γ' := Real.sqrt_pos.mpr hpos
  have hadj := no_sign_flip hK hk hklink (fun j => (Uᵀ * G) j j) hγ'0 habs
    (lt_of_le_of_lt hnormT h210)
  have hne0 : ∀ j, (Uᵀ * G) j j ≠ 0 := fun j h => by
    have := habs j; rw [h, abs_zero] at this; linarith
  obtain ⟨σ, hσ2, hσ⟩ := common_sign (fun j => (Uᵀ * G) j j) hne0 hadj
  refine ⟨σ, hσ2, hσ, ?_⟩
  have hov : ∀ d, overlapSign U G d = σ := overlapSign_eq ht hσ2 hσ
  have hfin := spectral_residual_certificate hH hU heig hg0 hgap G ht hε0 hε
  have hdU : U * diagonal (overlapSign U G) = σ • U := by
    ext i j
    simp [Matrix.mul_diagonal, hov j, mul_comm]
  rw [hdU] at hfin
  exact hfin

/-- info: 'FormalResearch.MatrixAnalysis.signLocking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signLocking


theorem abs_apply_le_l2_opNorm (M : Matrix ι ι ℝ) (i j : ι) : |M i j| ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℝ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm
    (M *ᵥ (EuclideanSpace.single j (1 : ℝ)).ofLp)) i
  refine le_trans (le_of_eq ?_) this
  simp

/-- **A single sign anchor forces `σ = +1`** (last sentence of Theorem 2): if
`‖G - σ U‖ ≤ ε`, `ε < |U_{i₀ j₀}|` and `G_{i₀ j₀}` has the sign of `U_{i₀ j₀}`, then `σ = 1`. -/
theorem sign_anchor {σ ε : ℝ} (hσ : σ ^ 2 = 1) {G U : Matrix ι ι ℝ} (i₀ j₀ : ι)
    (hε : ‖G - σ • U‖ ≤ ε) (hU : ε < |U i₀ j₀|) (hG : 0 < G i₀ j₀ * U i₀ j₀) : σ = 1 := by
  have hσ' : σ = 1 ∨ σ = -1 := by
    have : σ * σ = 1 := by rw [← sq]; exact hσ
    exact mul_self_eq_one_iff.mp this
  rcases hσ' with h | h
  · exact h
  · exfalso
    have h1 := abs_apply_le_l2_opNorm (G - σ • U) i₀ j₀
    rw [h] at h1 hε
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, neg_mul, one_mul,
      sub_neg_eq_add] at h1
    have h2 : |U i₀ j₀| ≤ |G i₀ j₀ + U i₀ j₀| := by
      rcases lt_trichotomy (U i₀ j₀) 0 with hu | hu | hu
      · have hg : G i₀ j₀ < 0 := by nlinarith
        rw [abs_of_neg hu, abs_of_neg (by linarith : G i₀ j₀ + U i₀ j₀ < 0)]; linarith
      · rw [hu] at hG; simp at hG
      · have hg : 0 < G i₀ j₀ := by nlinarith
        rw [abs_of_pos hu, abs_of_pos (by linarith : 0 < G i₀ j₀ + U i₀ j₀)]; linarith
    linarith

/-- info: 'FormalResearch.MatrixAnalysis.sign_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_anchor

end FormalResearch.MatrixAnalysis

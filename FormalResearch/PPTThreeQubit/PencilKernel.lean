module

public import Mathlib

/-!
# Kernels of `3 × 4` matrices and constant-rank pencils

Elementary linear algebra for the proof of `thm:ppt3-universal-moments` (`appendix_moment_cone.tex`):
the `3 × 4` pencil `M(a) = a₀ M₀ + a₁ M₁` of constant rank three has a one-dimensional kernel spanned
by its cofactor vector, which is a cubic in `a`, and the five quartic coefficient vectors of `a ⊗ b(a)`
are linearly independent.  The paper uses the Kronecker canonical form for the last point; here it is
proved elementarily (Bezout for polynomials in one variable plus a degree count).
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-- The cofactor vector of a `3 × 4` matrix: the signed `3 × 3` minors obtained by deleting a column. -/
def cof3 (M : Matrix (Fin 3) (Fin 4) ℂ) : Fin 4 → ℂ :=
  fun j => (-1) ^ (j : ℕ) * (M.submatrix id j.succAbove).det

/-- The `4 × 4` matrix with first row `z` and the rows of `M` below it. -/
def consRow (z : Fin 4 → ℂ) (M : Matrix (Fin 3) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of (Fin.cons z (fun i => M i))

theorem det_consRow (z : Fin 4 → ℂ) (M : Matrix (Fin 3) (Fin 4) ℂ) :
    (consRow z M).det = z ⬝ᵥ cof3 M := by
  rw [det_succ_row_zero, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (consRow z M).submatrix Fin.succ j.succAbove = M.submatrix id j.succAbove := by
    ext r c; simp [consRow]
  rw [this]
  simp [consRow, cof3]
  ring

theorem mulVec_cof3 (M : Matrix (Fin 3) (Fin 4) ℂ) : M *ᵥ cof3 M = 0 := by
  ext r
  have h := det_consRow (M r) M
  have h0 : (consRow (M r) M).det = 0 :=
    det_zero_of_row_eq (i := 0) (j := r.succ) (Fin.succ_ne_zero r).symm (by ext c; simp [consRow])
  rw [h0] at h
  simpa [mulVec, dotProduct_comm] using h.symm

/-- The rows of `M` are linearly independent: `y M = 0` forces `y = 0`. -/
def RowsIndep (M : Matrix (Fin 3) (Fin 4) ℂ) : Prop := ∀ y : Fin 3 → ℂ, y ᵥ* M = 0 → y = 0

theorem cof3_ne_zero {M : Matrix (Fin 3) (Fin 4) ℂ} (hM : RowsIndep M) : cof3 M ≠ 0 := by
  have hli : LinearIndependent ℂ (fun i : Fin 3 => M i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hM g (by ext c; simpa [vecMul, dotProduct] using congrFun hg c)
    exact fun i => congrFun this i
  obtain ⟨z, hz⟩ := exists_linearIndependent_cons_of_lt_finrank hli (by simp)
  have hu : IsUnit (consRow z M) := by
    rw [← linearIndependent_row_iff_isUnit]
    exact hz
  have hd : (consRow z M).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 hu).ne_zero
  rw [det_consRow] at hd
  intro h
  exact hd (by rw [h, dotProduct_zero])

theorem exists_smul_cof3_of_mulVec_eq_zero {M : Matrix (Fin 3) (Fin 4) ℂ} (hM : RowsIndep M)
    (b : Fin 4 → ℂ) (hb : M *ᵥ b = 0) : ∃ s : ℂ, b = s • cof3 M := by
  obtain ⟨j, hj⟩ : ∃ j, cof3 M j ≠ 0 := by
    by_contra h; exact cof3_ne_zero hM (funext fun j => by_contra fun h' => h ⟨j, h'⟩)
  have key : ∀ z : Fin 4 → ℂ, (z ⬝ᵥ cof3 M) • b = (z ⬝ᵥ b) • cof3 M := by
    intro z
    have h1 : consRow z M *ᵥ b = (z ⬝ᵥ b) • Pi.single 0 1 := by
      ext i
      refine Fin.cases ?_ (fun r => ?_) i
      · simp [consRow, mulVec, dotProduct]
      · have := congrFun hb r
        simpa [consRow, mulVec, dotProduct] using this
    have hadj : adjugate (consRow z M) *ᵥ (Pi.single 0 1 : Fin 4 → ℂ) = cof3 M := by
      ext j
      rw [mulVec_single_one]
      simp only [col_apply, adjugate_apply]
      have : (consRow z M).updateRow 0 (Pi.single j 1) = consRow (Pi.single j 1) M := by
        ext r c
        refine Fin.cases ?_ (fun r' => ?_) r
        · simp [consRow]
        · simp [consRow]
      rw [this, det_consRow]
      simp
    have h2 := congrArg (fun v => adjugate (consRow z M) *ᵥ v) h1
    simp only [mulVec_mulVec, adjugate_mul, mulVec_smul, hadj, smul_mulVec, one_mulVec] at h2
    rw [det_consRow] at h2
    exact h2
  have hj' := key (Pi.single j 1)
  simp only [single_dotProduct, one_mul] at hj'
  exact ⟨b j / cof3 M j, by
    rw [div_eq_inv_mul, mul_smul, ← hj', smul_smul, inv_mul_cancel₀ hj, one_smul]⟩

/-! ### The cubic expansion of the cofactor vector of a pencil -/

/-- The four coefficients of `a₀³, a₀²a₁, a₀a₁², a₁³` in `det (a₀ P + a₁ Q)` for `3 × 3` matrices
(sums of determinants of the mixed matrices whose rows come from `P` or `Q`). -/
def cubicCoeff (P Q : Matrix (Fin 3) (Fin 3) ℂ) : Fin 4 → ℂ :=
  ![P.det,
    (Matrix.of ![Q 0, P 1, P 2]).det + (Matrix.of ![P 0, Q 1, P 2]).det +
      (Matrix.of ![P 0, P 1, Q 2]).det,
    (Matrix.of ![P 0, Q 1, Q 2]).det + (Matrix.of ![Q 0, P 1, Q 2]).det +
      (Matrix.of ![Q 0, Q 1, P 2]).det,
    Q.det]

theorem det_pencil3 (P Q : Matrix (Fin 3) (Fin 3) ℂ) (a0 a1 : ℂ) :
    (a0 • P + a1 • Q).det = ∑ m : Fin 4, a0 ^ (3 - (m : ℕ)) * a1 ^ (m : ℕ) * cubicCoeff P Q m := by
  simp [det_fin_three, cubicCoeff, Fin.sum_univ_four]
  ring

/-- The `m`-th coefficient vector of the cofactor vector of the pencil `a₀ M₀ + a₁ M₁`. -/
def cofCoeff (M₀ M₁ : Matrix (Fin 3) (Fin 4) ℂ) (m : Fin 4) : Fin 4 → ℂ := fun j =>
  (-1) ^ (j : ℕ) * cubicCoeff (M₀.submatrix id j.succAbove) (M₁.submatrix id j.succAbove) m

/-- The cofactor vector of `a₀ M₀ + a₁ M₁` is the cubic `∑ₘ a₀^{3-m} a₁^m βₘ`. -/
theorem cof3_pencil (M₀ M₁ : Matrix (Fin 3) (Fin 4) ℂ) (a0 a1 : ℂ) :
    cof3 (a0 • M₀ + a1 • M₁) = ∑ m : Fin 4, (a0 ^ (3 - (m : ℕ)) * a1 ^ (m : ℕ)) • cofCoeff M₀ M₁ m := by
  ext j
  simp only [cof3, cofCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have : (a0 • M₀ + a1 • M₁).submatrix id j.succAbove =
      a0 • M₀.submatrix id j.succAbove + a1 • M₁.submatrix id j.succAbove := by
    ext r c; simp
  rw [this, det_pencil3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ### Independence of the cubic coefficient vectors -/

/-- If the rows of `M` are independent and `λ · cof M = 0`, then `λ` is in the row space of `M`. -/
theorem exists_vecMul_eq_of_dot_cof {M : Matrix (Fin 3) (Fin 4) ℂ} (hM : RowsIndep M)
    (lam : Fin 4 → ℂ) (h : lam ⬝ᵥ cof3 M = 0) : ∃ y : Fin 3 → ℂ, y ᵥ* M = lam := by
  have hd : (consRow lam M).det = 0 := by rw [det_consRow, h]
  obtain ⟨v, hv, hvA⟩ := (exists_vecMul_eq_zero_iff).2 hd
  have hv0 : v 0 ≠ 0 := by
    intro h0
    apply hv
    have : (fun i : Fin 3 => v i.succ) ᵥ* M = 0 := by
      ext c
      have := congrFun hvA c
      simp [vecMul, dotProduct, Fin.sum_univ_succ, consRow, h0] at this ⊢
      exact this
    have h1 := hM _ this
    ext i
    refine Fin.cases h0 (fun r => ?_) i
    exact congrFun h1 r
  refine ⟨fun i => -(v i.succ) / v 0, ?_⟩
  ext c
  have := congrFun hvA c
  simp only [vecMul, dotProduct, Fin.sum_univ_succ, consRow, of_apply, Fin.cons_zero,
    Fin.cons_succ, Pi.zero_apply] at this ⊢
  field_simp
  linear_combination -this

/-- Bezout for a finite family of complex polynomials without a common root. -/
theorem exists_bezout (Q : Fin 4 → Polynomial ℂ) (h : ∀ t : ℂ, ∃ r, (Q r).eval t ≠ 0) :
    ∃ e : Fin 4 → Polynomial ℂ, ∑ r, e r * Q r = 1 := by
  set I : Ideal (Polynomial ℂ) := Ideal.span (Set.range Q) with hI
  have hI1 : I = ⊤ := by
    by_contra hne
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
    have hgu : ¬ IsUnit g := by
      intro hu
      apply hne
      rw [hg]
      exact Ideal.span_singleton_eq_top.2 hu
    have hQg : ∀ r, g ∣ Q r := fun r => by
      have : Q r ∈ I := Ideal.subset_span ⟨r, rfl⟩
      rw [hg, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
    have hg0 : g ≠ 0 := by
      rintro rfl
      obtain ⟨r, hr⟩ := h 0
      have := hQg r
      rw [zero_dvd_iff] at this
      exact hr (by rw [this]; simp)
    have hdeg : g.degree ≠ 0 := fun hd => hgu (Polynomial.isUnit_iff_degree_eq_zero.2 hd)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root g hdeg
    obtain ⟨r, hr⟩ := h t
    obtain ⟨c, hc⟩ := hQg r
    exact hr (by rw [hc, Polynomial.eval_mul, ht.eq_zero, zero_mul])
  have h1 : (1 : Polynomial ℂ) ∈ I := by rw [hI1]; exact Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (Polynomial ℂ)).1 h1
  exact ⟨e, by simpa [smul_eq_mul] using he⟩

open Polynomial in
theorem eval_det3 (A : Matrix (Fin 3) (Fin 3) ℂ[X]) (t : ℂ) :
    A.det.eval t = (A.map (Polynomial.eval t)).det := by
  have := RingHom.map_det (Polynomial.evalRingHom t) A
  simpa using this

open Polynomial in
/-- **Independence of the cubic coefficient vectors.**  If the pencil `a₀ M₀ + a₁ M₁` has independent
rows for every `a ≠ 0`, then the four coefficient vectors `βₘ` of its cofactor cubic are linearly
independent: a functional killing all of them is zero.  (The paper obtains this from the Kronecker
canonical form; here: Bezout for the four cubic minors in the chart `a = (1, t)`, which shows that the
row-space coefficient `y(t)` with `y(t) M(1,t) = λ` is a polynomial, and a degree count at `a = (0, 1)`.) -/
theorem cofCoeff_indep (M₀ M₁ : Matrix (Fin 3) (Fin 4) ℂ)
    (h : ∀ a0 a1 : ℂ, ¬ (a0 = 0 ∧ a1 = 0) → RowsIndep (a0 • M₀ + a1 • M₁))
    (lam : Fin 4 → ℂ) (hl : ∀ m, lam ⬝ᵥ cofCoeff M₀ M₁ m = 0) : lam = 0 := by
  by_contra hne
  -- polynomial matrices
  let Mp : Matrix (Fin 3) (Fin 4) ℂ[X] := Matrix.of fun i k => C (M₀ i k) + X * C (M₁ i k)
  let Mpr : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ[X] := fun r => Mp.submatrix id r.succAbove
  let Qp : Fin 4 → ℂ[X] := fun r => (Mpr r).det
  let Np : Fin 4 → Fin 3 → ℂ[X] := fun r i =>
    ((Mpr r).updateRow i (fun c => C (lam (r.succAbove c)))).det
  have hMpr : ∀ (t : ℂ) (r : Fin 4), (Mpr r).map (Polynomial.eval t) =
      (((1 : ℂ) • M₀ + t • M₁).submatrix id r.succAbove) := by
    intro t r; ext i c; simp [Mpr, Mp]; ring
  have hQ : ∀ (t : ℂ) (r : Fin 4), (Qp r).eval t =
      (((1 : ℂ) • M₀ + t • M₁).submatrix id r.succAbove).det := by
    intro t r; rw [← hMpr, ← eval_det3]
  have hN : ∀ (t : ℂ) (r : Fin 4) (i : Fin 3), (Np r i).eval t =
      ((((1 : ℂ) • M₀ + t • M₁).submatrix id r.succAbove).updateRow i
        (fun c => lam (r.succAbove c))).det := by
    intro t r i
    rw [← hMpr t r]
    show eval t (((Mpr r).updateRow i (fun c => C (lam (r.succAbove c)))).det) = _
    rw [eval_det3]
    congr 1
    ext a c
    by_cases ha : a = i
    · subst ha; simp
    · simp [updateRow_ne ha]
  -- for each `t` the row-space coefficient
  have hy : ∀ t : ℂ, ∃ y : Fin 3 → ℂ, y ᵥ* ((1 : ℂ) • M₀ + t • M₁) = lam := by
    intro t
    have hr := h 1 t (by simp)
    have hcof : lam ⬝ᵥ cof3 ((1 : ℂ) • M₀ + t • M₁) = 0 := by
      rw [cof3_pencil, dotProduct_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [dotProduct_smul, hl, smul_zero]
    exact exists_vecMul_eq_of_dot_cof hr lam hcof
  choose y hy using hy
  -- Cramer
  have hcr : ∀ (t : ℂ) (r : Fin 4) (i : Fin 3), y t i * (Qp r).eval t = (Np r i).eval t := by
    intro t r i
    rw [hQ, hN]
    have := det_updateRow_sum (((1 : ℂ) • M₀ + t • M₁).submatrix id r.succAbove) i (y t)
    rw [smul_eq_mul] at this
    rw [← this]
    congr 2
    ext c
    have := congrFun (hy t) (r.succAbove c)
    simpa [vecMul, dotProduct, Finset.sum_apply] using this
  -- no common root
  have hroot : ∀ t : ℂ, ∃ r, (Qp r).eval t ≠ 0 := by
    intro t
    have hr := h 1 t (by simp)
    have := cof3_ne_zero hr
    by_contra hall
    push Not at hall
    apply this
    ext r
    have h0 := hall r
    rw [hQ] at h0
    simp only [cof3, Pi.zero_apply]
    rw [h0, mul_zero]
  obtain ⟨e, he⟩ := exists_bezout Qp hroot
  set π : Fin 3 → ℂ[X] := fun i => ∑ r, e r * Np r i with hπ
  have hyπ : ∀ t i, y t i = (π i).eval t := by
    intro t i
    have h1 : (∑ r, (e r).eval t * (Qp r).eval t) = 1 := by
      have := congrArg (Polynomial.eval t) he
      simpa [Polynomial.eval_finsetSum] using this
    calc y t i = y t i * ∑ r, (e r).eval t * (Qp r).eval t := by rw [h1, mul_one]
      _ = ∑ r, (e r).eval t * (y t i * (Qp r).eval t) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = (π i).eval t := by
        simp only [hπ, Polynomial.eval_finsetSum, Polynomial.eval_mul]
        exact Finset.sum_congr rfl fun r _ => by rw [hcr]
  -- polynomial identity
  have hid : ∀ k : Fin 4, ∑ i, π i * (C (M₀ i k) + X * C (M₁ i k)) = C (lam k) := by
    intro k
    apply Polynomial.funext
    intro t
    have := congrFun (hy t) k
    simp only [vecMul, dotProduct, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [← hyπ]
  -- degree count
  have hπne : ∃ i, π i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    ext k
    have := hid k
    simp only [hall, zero_mul, Finset.sum_const_zero] at this
    exact (Polynomial.C_eq_zero.1 this.symm)
  set S : Finset (Fin 3) := Finset.univ.filter (fun i => π i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hπne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hi0⟩ := Finset.exists_mem_eq_sup S hSne (fun i => (π i).natDegree)
  set d := S.sup (fun i => (π i).natDegree) with hd
  have hle : ∀ i, (π i).natDegree ≤ d := by
    intro i
    by_cases hi : π i = 0
    · simp [hi]
    · exact Finset.le_sup (f := fun i => (π i).natDegree) (by simp [hS, hi])
  have hco : ∀ k, ∑ i, (π i).coeff d * M₁ i k = 0 := by
    intro k
    have := congrArg (fun p => p.coeff (d + 1)) (hid k)
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C] at this
    have e : ∀ i, (π i * (C (M₀ i k) + X * C (M₁ i k))).coeff (d + 1) = (π i).coeff d * M₁ i k := by
      intro i
      rw [mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_C, ← mul_assoc, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_X, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le (hle i))]
      simp
    simp only [e] at this
    simpa using this
  have hrow : (fun i => (π i).coeff d) ᵥ* M₁ = 0 := by
    ext k; simpa [vecMul, dotProduct] using hco k
  have h01 := h 0 1 (by simp)
  simp only [zero_smul, one_smul, zero_add] at h01
  have hc0 := h01 _ hrow
  have := congrFun hc0 i0
  have hne0 : (π i0).coeff d ≠ 0 := by
    rw [hi0]
    exact Polynomial.leadingCoeff_ne_zero.2 (by simpa [hS] using hi0S)
  exact hne0 this

end

end FormalResearch.PPTThreeQubit

/-- info: 'FormalResearch.PPTThreeQubit.cofCoeff_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.cofCoeff_indep

/-- info: 'FormalResearch.PPTThreeQubit.exists_smul_cof3_of_mulVec_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.PPTThreeQubit.exists_smul_cof3_of_mulVec_eq_zero

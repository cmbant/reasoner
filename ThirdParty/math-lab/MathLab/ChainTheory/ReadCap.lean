module

/-
ReadCap.lean

The read cap reduced to one classical theorem.

The alpha Letter's Lean file (ChainAlpha.lean) carries the read cap as a hypothesis on a readability
predicate,

  ReadCap Readable := ∀ d₁ d₂, 2 ≤ d₁ → 2 ≤ d₂ → (Readable d₁ d₂ ↔ d₁ d₂ ≤ 6),

citing Størmer, Woronowicz and Choi. With `Readable` taken to be the Letter's own definition (every
positive linear map between the ends, in either direction, is decomposable; `ChoiDark.Readable`), this
file proves

  `readcap_iff_woronowicz : ReadCap Readable ↔ Woronowicz23`,

where `Woronowicz23` says that every positive linear map M₂(ℂ) → M₃(ℂ) is decomposable (Woronowicz,
Rep. Math. Phys. 10, 165 (1976)). So the whole read cap rests on that single theorem, which is not
formalized here. The dark direction comes from `ChoiDark.readable_imp_le_six`; the rest is proved here:

  Part 1  Compression: decomposability of all positive maps M_n → M_m passes to M_{n'} → M_{m'} for
          n' ≤ n, m' ≤ m. In particular Woronowicz's theorem implies Størmer's (M₂ → M₂).
  Part 2  Adjoints for the Hilbert–Schmidt pairing: the adjoint of a positive map is positive, and a
          map is decomposable when its adjoint is. So M_n → M_m and M_m → M_n stand or fall together.
  Part 3  The read cap is equivalent to Woronowicz's theorem.
  Part 4  Regression guards for the 26 Oct correction of the definitions: the readable predicate is
          satisfiable (`readable_one_one`), and the map X ↦ (1 + i) X is not positive.

Check: compile ChoiDark.lean to an .olean first (scripts/check_lean.py does this), then
`lake env lean ReadCap.lean` with that directory on LEAN_PATH.
-/
public import MathLab.ChainTheory.ChoiDark
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open Matrix

namespace ChainReadCap

open ChoiDark

/-- The Letter's read cap, verbatim from `ChainAlpha.lean`: a hypothesis on a readability predicate. -/
def ReadCap (Readable : ℕ → ℕ → Prop) : Prop :=
  ∀ d1 d2, 2 ≤ d1 → 2 ≤ d2 → (Readable d1 d2 ↔ d1 * d2 ≤ 6)

/-- Every positive linear map `M_n(ℂ) → M_m(ℂ)` is decomposable. -/
def AllDecomposable (n m : ℕ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ, IsPositive Φ → IsDecomposable Φ

/-- **Woronowicz's theorem** for `M₂ → M₃` (1976), the one classical input of the read cap. -/
def Woronowicz23 : Prop := AllDecomposable 2 3

/-! ## Part 1. Compression -/

theorem inclN_transpose (n d : ℕ) : (inclN n d)ᵀ = (inclN n d)ᴴ := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, inclN]
  split_ifs <;> simp

/-- The extension `X ↦ J_m Φ(J_nᴴ X J_n) J_mᴴ` of a map `M_{n'} → M_{m'}` to `M_n → M_m`. -/
noncomputable def extendLin {n' m' : ℕ} (n m : ℕ)
    (Φ : Matrix (Fin n') (Fin n') ℂ →ₗ[ℂ] Matrix (Fin m') (Fin m') ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun X := inclN m' m * Φ ((inclN n' n)ᴴ * X * inclN n' n) * (inclN m' m)ᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

/-- **Compression.** If every positive map `M_n → M_m` is decomposable, so is every positive map
`M_{n'} → M_{m'}` with `n' ≤ n` and `m' ≤ m`. -/
theorem allDecomposable_mono {n m n' m' : ℕ} (hn : n' ≤ n) (hm : m' ≤ m) (h : AllDecomposable n m) :
    AllDecomposable n' m' := by
  intro Φ hΦ
  have hΨ : IsPositive (extendLin n m Φ) := by
    intro r B w
    show 0 ≤ (star w ⬝ᵥ ((inclN m' m * Φ ((inclN n' n)ᴴ * (Bᴴ * B) * inclN n' n) * (inclN m' m)ᴴ) *ᵥ w)).re ∧
      (star w ⬝ᵥ ((inclN m' m * Φ ((inclN n' n)ᴴ * (Bᴴ * B) * inclN n' n) * (inclN m' m)ᴴ) *ᵥ w)).im = 0
    rw [quad_conj]
    have hB : (inclN n' n)ᴴ * (Bᴴ * B) * inclN n' n = (B * inclN n' n)ᴴ * (B * inclN n' n) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hB]
    exact hΦ r (B * inclN n' n) ((inclN m' m)ᴴ *ᵥ w)
  obtain ⟨p, q, K, L, hKL⟩ := h (extendLin n m Φ) hΨ
  refine ⟨p, q, fun k => (inclN m' m)ᴴ * K k * inclN n' n, fun l => (inclN m' m)ᴴ * L l * inclN n' n,
    fun Y => ?_⟩
  have hc : Φ Y = (inclN m' m)ᴴ * extendLin n m Φ (inclN n' n * Y * (inclN n' n)ᴴ) * inclN m' m := by
    show Φ Y = (inclN m' m)ᴴ * (inclN m' m * Φ ((inclN n' n)ᴴ * (inclN n' n * Y * (inclN n' n)ᴴ) * inclN n' n)
      * (inclN m' m)ᴴ) * inclN m' m
    rw [show (inclN n' n)ᴴ * (inclN n' n * Y * (inclN n' n)ᴴ) * inclN n' n
        = ((inclN n' n)ᴴ * inclN n' n) * Y * ((inclN n' n)ᴴ * inclN n' n) by simp only [Matrix.mul_assoc],
      inclN_conjTranspose_mul hn, Matrix.one_mul, Matrix.mul_one]
    rw [show (inclN m' m)ᴴ * (inclN m' m * Φ Y * (inclN m' m)ᴴ) * inclN m' m
        = ((inclN m' m)ᴴ * inclN m' m) * Φ Y * ((inclN m' m)ᴴ * inclN m' m) by simp only [Matrix.mul_assoc],
      inclN_conjTranspose_mul hm, Matrix.one_mul, Matrix.mul_one]
  rw [hc, hKL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have hreal : ((inclN n' n)ᴴ)ᵀ = inclN n' n := by
      rw [← inclN_transpose, Matrix.transpose_transpose]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hreal, inclN_transpose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **Woronowicz implies Størmer**: every positive map `M₂ → M₂` is then decomposable. -/
theorem stormer_of_woronowicz (hW : Woronowicz23) : AllDecomposable 2 2 :=
  allDecomposable_mono le_rfl (by norm_num) hW

/-! ## Part 2. Adjoints -/

/-- A linear map is determined by its values on matrix units. -/
theorem linear_expand {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin n) :
    Ψ X a b = ∑ i, ∑ j, X i j * Ψ (single i j 1) a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, Matrix.smul_apply, smul_eq_mul]

/-- The adjoint for the Hilbert–Schmidt pairing: `Ψ†(Y)_ij = Σ_ab conj(Ψ(E_ij)_ab) Y_ab`. -/
noncomputable def adj {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ where
  toFun Y := Matrix.of fun i j => ∑ a, ∑ b, star (Ψ (single i j 1) a b) * Y a b
  map_add' Y Z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem adj_apply {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin m) :
    adj Ψ Y i j = ∑ a, ∑ b, star (Ψ (single i j 1) a b) * Y a b := rfl

/-- On matrix units the adjoint is the conjugate transpose of coefficients. -/
theorem adj_single {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) (i j : Fin m) : adj Ψ (single a b 1) i j = star (Ψ (single i j 1) a b) := by
  rw [adj_apply, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hc)]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Matrix.single_apply_of_row_ne (Ne.symm hc)]
  · simp

/-- The rank-one identity behind positivity of the adjoint:
`w† Ψ†(u u†) w = conj(u† Ψ(w w†) u)`. -/
theorem adj_rank_one {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) (w : Fin m → ℂ) :
    star w ⬝ᵥ (adj Ψ (vecMulVec u (star u)) *ᵥ w)
      = star (star u ⬝ᵥ (Ψ (vecMulVec w (star w)) *ᵥ u)) := by
  simp only [dotProduct, mulVec, adj_apply, linear_expand Ψ (vecMulVec w (star w)), vecMulVec_apply,
    Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ a, ∑ b, star (w i) * (star (Ψ (single i j 1) a b) * (u a * star (u b)) * w j)
      = ∑ i, ∑ a, ∑ j, ∑ b, star (w i) * (star (Ψ (single i j 1) a b) * (u a * star (u b)) * w j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, star (w i) * (star (Ψ (single i j 1) a b) * (u a * star (u b)) * w j) :=
        Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, star (w i) * (star (Ψ (single i j 1) a b) * (u a * star (u b)) * w j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, star (w i) * (star (Ψ (single i j 1) a b) * (u a * star (u b)) * w j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-- **The adjoint of a positive map is positive.** -/
theorem adj_positive {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hΨ : IsPositive Ψ) : IsPositive (adj Ψ) := by
  intro r B w
  have hB : Bᴴ * B = ∑ s, vecMulVec (fun i => star (B s i)) (star fun i => star (B s i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply]
  have hW : (Matrix.of fun (_ : Fin 1) (i : Fin m) => star (w i))ᴴ * Matrix.of (fun (_ : Fin 1) i => star (w i))
      = vecMulVec w (star w) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, vecMulVec_apply]
  rw [hB, map_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, Complex.im_sum]
  have each := fun s : Fin r => hΨ 1 (Matrix.of fun _ i => star (w i)) (fun i => star (B s i))
  simp only [hW] at each
  have hre : ∀ z : ℂ, (star z).re = z.re := fun z => Complex.conj_re z
  have him : ∀ z : ℂ, (star z).im = -z.im := fun z => Complex.conj_im z
  refine ⟨Finset.sum_nonneg fun s _ => ?_, Finset.sum_eq_zero fun s _ => ?_⟩
  · rw [adj_rank_one, hre]
    exact (each s).1
  · rw [adj_rank_one, him, (each s).2, neg_zero]

theorem kEK_apply {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℂ) (a b : Fin n) (i j : Fin m) :
    (K * single a b (1 : ℂ) * Kᴴ) i j = K i a * star (K j b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
  · intro c _ hc
    rw [Matrix.mul_single_apply_of_ne (hbj := hc), zero_mul]
  · simp

theorem LEtL_apply {m n : ℕ} (L : Matrix (Fin m) (Fin n) ℂ) (a b : Fin n) (i j : Fin m) :
    (L * (single a b (1 : ℂ))ᵀ * Lᴴ) i j = L i b * star (L j a) := by
  rw [Matrix.transpose_single, kEK_apply]

/-- **A map is decomposable when its adjoint is.** If `Ψ† = Σ K · Kᴴ + Σ L ·ᵀ Lᴴ`, then
`Ψ = Σ Kᴴ · K + Σ Lᵀ ·ᵀ (Lᵀ)ᴴ`. -/
theorem decomposable_of_adj {m n : ℕ} (Ψ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (h : IsDecomposable (adj Ψ)) : IsDecomposable Ψ := by
  obtain ⟨p, q, K, L, hKL⟩ := h
  refine ⟨p, q, fun k => (K k)ᴴ, fun l => (L l)ᵀ, fun X => ?_⟩
  ext a b
  have e : ∀ i j, Ψ (single i j 1) a b = star (adj Ψ (single a b 1) i j) := fun i j => by
    rw [adj_single, star_star]
  rw [linear_expand Ψ X a b]
  simp only [e, hKL, Matrix.add_apply, Matrix.sum_apply, kEK_apply, LEtL_apply, star_add, star_sum,
    star_mul', star_star, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_star,
    Finset.sum_mul]
  congr 1
  · calc ∑ i, ∑ j, ∑ k, X i j * (star (K k i a) * K k j b)
        = ∑ i, ∑ k, ∑ j, X i j * (star (K k i a) * K k j b) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, X i j * (star (K k i a) * K k j b) := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, X i j * (star (K k i a) * K k j b) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring
  · calc ∑ i, ∑ j, ∑ l, X i j * (star (L l i b) * L l j a)
        = ∑ i, ∑ l, ∑ j, X i j * (star (L l i b) * L l j a) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, X i j * (star (L l i b) * L l j a) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring

/-- **Both directions stand or fall together**: if every positive map `M_n → M_m` is decomposable, so is
every positive map `M_m → M_n`. -/
theorem allDecomposable_symm {n m : ℕ} (h : AllDecomposable n m) : AllDecomposable m n :=
  fun Ψ hΨ => decomposable_of_adj Ψ (h (adj Ψ) (adj_positive Ψ hΨ))

/-- Readability is decomposability of all positive maps in one direction. -/
theorem readable_iff_allDecomposable {d₁ d₂ : ℕ} : Readable d₁ d₂ ↔ AllDecomposable d₁ d₂ :=
  ⟨fun h => h.1, fun h => ⟨h, allDecomposable_symm h⟩⟩

/-! ## Part 3. The read cap is equivalent to Woronowicz's theorem -/

/-- **Woronowicz's theorem gives the whole read cap.** -/
theorem readcap_of_woronowicz (hW : Woronowicz23) : ReadCap Readable := by
  intro d₁ d₂ h₁ h₂
  refine ⟨readable_imp_le_six h₁ h₂, fun h6 => ?_⟩
  have hd₁ : d₁ ≤ 3 := by
    by_contra h
    have : 4 * 2 ≤ d₁ * d₂ := Nat.mul_le_mul (by omega) h₂
    omega
  have hd₂ : d₂ ≤ 3 := by
    by_contra h
    have : 2 * 4 ≤ d₁ * d₂ := Nat.mul_le_mul h₁ (by omega)
    omega
  rw [readable_iff_allDecomposable]
  interval_cases d₁ <;> interval_cases d₂
  · exact stormer_of_woronowicz hW
  · exact hW
  · exact allDecomposable_symm hW
  · omega

/-- **The read cap gives Woronowicz's theorem.** -/
theorem woronowicz_of_readcap (h : ReadCap Readable) : Woronowicz23 :=
  readable_iff_allDecomposable.1 ((h 2 3 le_rfl (by norm_num)).2 (by norm_num))

/-- **The read cap, for the Letter's own notion of readability, is equivalent to Woronowicz's theorem
for `M₂ → M₃`.** -/
theorem readcap_iff_woronowicz : ReadCap Readable ↔ Woronowicz23 :=
  ⟨woronowicz_of_readcap, readcap_of_woronowicz⟩

/-! ## Part 4. Regression guards for the corrected definitions -/

/-- **The readable predicate is satisfiable**: every positive linear map on `M₁(ℂ) = ℂ` is decomposable
(it is multiplication by a nonnegative real). Under the definitions published at commit 3b95151 no type
was readable. -/
theorem readable_one_one : Readable 1 1 := by
  rw [readable_iff_allDecomposable]
  intro Φ hΦ
  have hp := hΦ 1 1 (fun _ => 1)
  set c := Φ 1 0 0 with hc
  have hq : star (fun _ : Fin 1 => (1 : ℂ)) ⬝ᵥ (Φ ((1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * 1) *ᵥ fun _ => 1) = c := by
    simp [dotProduct, mulVec, hc]
  rw [hq] at hp
  refine ⟨1, 0, fun _ => Matrix.of fun _ _ => ((Real.sqrt c.re : ℝ) : ℂ), Fin.elim0, fun X => ?_⟩
  ext a b
  fin_cases a; fin_cases b
  have hX : X = X 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j; simp
  have hcre : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hp.2])
  have hs : ((Real.sqrt c.re : ℝ) : ℂ) * ((Real.sqrt c.re : ℝ) : ℂ) = c := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.1, ← hcre]
  conv_lhs => rw [hX, map_smul]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ← hc]
  linear_combination (-X 0 0) * hs

/-- **The twisted map is no longer positive**: `X ↦ (1 + i) X` sends `1` to a matrix whose quadratic
form is not real. It counted as positive under the definitions published at commit 3b95151. -/
theorem twist_not_positive :
    ¬ IsPositive (fun X : Matrix (Fin 2) (Fin 2) ℂ => (1 + Complex.I) • X) := by
  intro h
  have := (h 2 1 (fun i => if i = 0 then 1 else 0)).2
  simp [dotProduct, mulVec, Matrix.one_apply] at this

end ChainReadCap

end -- public section

#print axioms ChainReadCap.allDecomposable_mono
#print axioms ChainReadCap.adj_positive
#print axioms ChainReadCap.decomposable_of_adj
#print axioms ChainReadCap.readcap_iff_woronowicz
#print axioms ChainReadCap.readable_one_one
#print axioms ChainReadCap.twist_not_positive

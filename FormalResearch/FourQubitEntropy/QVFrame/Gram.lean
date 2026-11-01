import FormalResearch.FourQubitEntropy.QVFrame.Twist
import FormalResearch.FourQubitEntropy.QVCert.Positivity

/-!
# T1: the weighted covariant norm as a quadratic form in the six-copy vector

For a block `b` and a covariant `i`, `‖Φ_{ki}(z)‖²_w = ⟨w_a(z), A_{ki} w_a(z)⟩` with
`w_a(z) = z^{⊗a} ⊗ z̃^{⊗(6-a)}` (`wvec`, a function on `Cfg 6`), where
`A = gramOp p v = Σ_{σ ∈ S₄} Σ_{(c,x),(c',x') ∈ v} x x' ⊗_q E^{p_{σ⁻¹q}}_{μ_c(σ⁻¹q), μ_{c'}(σ⁻¹q)}`
and `E^j_{μμ'} = Σ_{m ≤ j} ω_{j,m} (C6 row (j,m,μ))ᵀ (C6 row (j,m,μ'))` (`Eop`).

Nothing here refers to the numbers of `Data.lean`: `gramOp` takes a spin tuple and a sparse multiplicity vector,
and `normSqPhi_eq_qf` holds for every `QVCert.Block`.
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

/-! ### Finite list sums -/

/-- `Σ_{s ∈ L} f s` as a list sum. -/
def lsum {α M : Type*} [AddCommMonoid M] (L : List α) (f : α → M) : M := (L.map f).sum

section lsum
variable {α M : Type*}

theorem lsum_nil [AddCommMonoid M] (f : α → M) : lsum [] f = 0 := rfl

theorem lsum_cons [AddCommMonoid M] (a : α) (L : List α) (f : α → M) :
    lsum (a :: L) f = f a + lsum L f := by simp [lsum]

theorem lsum_add [AddCommMonoid M] (L : List α) (f g : α → M) :
    lsum L (fun s => f s + g s) = lsum L f + lsum L g := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp only [lsum_cons, ih]; abel

theorem lsum_mul_left [NonUnitalNonAssocSemiring M] (L : List α) (c : M) (f : α → M) :
    c * lsum L f = lsum L (fun s => c * f s) := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp only [lsum_cons, mul_add, ih]

theorem lsum_mul_right [NonUnitalNonAssocSemiring M] (L : List α) (c : M) (f : α → M) :
    lsum L f * c = lsum L (fun s => f s * c) := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp only [lsum_cons, add_mul, ih]

theorem lsum_mul_lsum [NonUnitalNonAssocSemiring M] (L : List α) (f g : α → M) :
    lsum L f * lsum L g = lsum L (fun s => lsum L (fun s' => f s * g s')) := by
  rw [lsum_mul_right]
  refine congrArg (lsum L) (funext fun s => ?_)
  rw [lsum_mul_left]

theorem lsum_congr [AddCommMonoid M] (L : List α) {f g : α → M} (h : ∀ s ∈ L, f s = g s) :
    lsum L f = lsum L g := by
  unfold lsum
  rw [List.map_congr_left h]

theorem sum_lsum_comm {β : Type*} [AddCommMonoid M] (S : Finset β) (L : List α) (f : β → α → M) :
    ∑ m ∈ S, lsum L (f m) = lsum L (fun s => ∑ m ∈ S, f m s) := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp only [lsum_cons, Finset.sum_add_distrib, ih]

theorem lsum_sum_comm {β : Type*} [AddCommMonoid M] (S : Finset β) (L : List α) (f : α → β → M) :
    lsum L (fun s => ∑ m ∈ S, f s m) = ∑ m ∈ S, lsum L (fun s => f s m) :=
  (sum_lsum_comm S L (fun m s => f s m)).symm

theorem lsum_map_hom {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] {F : Type*}
    [FunLike F M N] [AddMonoidHomClass F M N] (φ : F) (L : List α) (f : α → M) :
    φ (lsum L f) = lsum L (fun s => φ (f s)) := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp [lsum_cons, ih]

end lsum

/-! ### The `E` operators and `gramOp` -/

/-- The row `(j, m, μ)` of `C6` as a function of a six-copy word. -/
def rowW (j m μ : ℕ) (w : Wd 6) : ℤ := QVCert.rowC j m μ (numOf w)

/-- `E^j_{μμ'} = Σ_{m ≤ j} ω_{j,m} C[(j,m,μ)]ᵀ C[(j,m,μ')]`, a `64 × 64` integer matrix. -/
def Eop (j μ μ' : ℕ) : Matrix (Wd 6) (Wd 6) ℤ :=
  Matrix.of fun w w' => ∑ m ∈ range (j + 1), (QVCert.weight j m : ℤ) * rowW j m μ w * rowW j m μ' w'

/-- `A = Σ_{σ} Σ_{(c,x),(c',x')} x x' ⊗_q E^{p_{σ⁻¹ q}}_{μ_c(σ⁻¹ q), μ_{c'}(σ⁻¹ q)}`: the operator of the
weighted squared norm of `W_{a,p} v` for the sparse multiplicity vector `v`. -/
def gramOp (p : Fin 4 → ℕ) (v : List (ℕ × ℤ)) : Matrix (Cfg 6) (Cfg 6) ℤ :=
  ∑ σ : Equiv.Perm (Fin 4), lsum v fun s => lsum v fun s' =>
    (s.2 * s'.2) • kronPi (fun q => Eop (p (σ.symm q)) (QVCert.muDigit p s.1 (σ.symm q))
      (QVCert.muDigit p s'.1 (σ.symm q)))

/-! ### The vector `w_a(z)` -/

/-- `w_a(z) = z^{⊗a} ⊗ z̃^{⊗(6-a)}` on `Cfg 6`. -/
def wvec (a : ℕ) (z : Psi) : Cfg 6 → ℂ := pw a (zf z) (fun c => conj (zf z c))

/-- `conj w_a(z)`. -/
def wvecBar (a : ℕ) (z : Psi) : Cfg 6 → ℂ := pw a (fun c => conj (zf z c)) (zf z)

theorem conj_wvec (a : ℕ) (z : Psi) (β : Cfg 6) : conj (wvec a z β) = wvecBar a z β := by
  unfold wvec wvecBar
  rw [conj_pw]
  congr 1
  funext c; simp

theorem ztilde_eq (z : Psi) (c : Site) :
    QVCert.ztilde z (c 0) (c 1) (c 2) (c 3) = Jv (fun c => conj (zf z c)) c := by
  simp [QVCert.ztilde, Jv, eps, Fin.prod_univ_four, rev', zf, pow_add]

theorem numOf_wordEquiv (x : Fin 64) : numOf (wordEquiv x) = x.val := numOf_bitsOf x

theorem sixCopy_eq (a : ℕ) (z : Psi) (b : Fin 4 → Fin 64) :
    QVCert.sixCopy a z b = wvec a z (fun q => wordEquiv (b q)) := by
  unfold QVCert.sixCopy wvec pw
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold QVCert.copyVec
  by_cases h : k.val < a
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false]
    exact ztilde_eq z (fun q => QVCert.bitF (b q).val (5 - k.val))

/-! ### `Φ` as a bilinear expression -/

/-- The integer coefficient vector `r_{σ,m}` with `Φ(σ, m) = Σ_β r_{σ,m}(β) w(β)`. -/
def rowCoef (p : Fin 4 → ℕ) (v : List (ℕ × ℤ)) (σ : Equiv.Perm (Fin 4)) (m : Fin 4 → ℕ) (β : Cfg 6) : ℤ :=
  lsum v fun s => s.2 * ∏ k : Fin 4, rowW (p k) (m k) (QVCert.muDigit p s.1 k) (β (σ k))

theorem sectorW_eq (a : ℕ) (p : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) (m μ : Fin 4 → ℕ) (z : Psi) :
    QVCert.sectorW a p σ m μ z =
      ∑ β : Cfg 6, (∏ k : Fin 4, (rowW (p k) (m k) (μ k) (β (σ k)) : ℂ)) * wvec a z β := by
  unfold QVCert.sectorW
  let e : (Fin 4 → Fin 64) ≃ Cfg 6 := Equiv.piCongrRight fun _ => wordEquiv
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : ∏ k : Fin 4, ((QVCert.rowC (p k) (m k) (μ k) (b (σ k)).val : ℤ) : ℂ) =
      ∏ k : Fin 4, ((rowW (p k) (m k) (μ k) ((e b) (σ k)) : ℤ) : ℂ) :=
    Finset.prod_congr rfl fun k _ => by simp [rowW, e, numOf_wordEquiv]
  rw [h1, sixCopy_eq]
  rfl

theorem Phi_eq (b : QVCert.Block) (z : Psi) (i : ℕ) (x : Equiv.Perm (Fin 4) × (Fin 4 → ℕ)) :
    b.Phi z i x = ∑ β : Cfg 6, ((rowCoef b.spins (b.vecs.getD i []) x.1 x.2 β : ℤ) : ℂ) * wvec b.a z β := by
  have hL : b.Phi z i x = lsum (b.vecs.getD i []) (fun t => (t.2 : ℂ) *
      QVCert.sectorW b.a b.spins x.1 x.2 (QVCert.muDigit b.spins t.1) z) := rfl
  rw [hL]
  simp only [sectorW_eq, Finset.mul_sum]
  rw [lsum_sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hc : ((rowCoef b.spins (b.vecs.getD i []) x.1 x.2 β : ℤ) : ℂ) =
      lsum (b.vecs.getD i []) (fun t => (t.2 : ℂ) * ∏ k : Fin 4,
        ((rowW (b.spins k) (x.2 k) (QVCert.muDigit b.spins t.1 k) (β (x.1 k)) : ℤ) : ℂ)) := by
    have := lsum_map_hom (Int.castRingHom ℂ) (b.vecs.getD i [])
      (fun t => t.2 * ∏ k : Fin 4, rowW (b.spins k) (x.2 k) (QVCert.muDigit b.spins t.1 k) (β (x.1 k)))
    unfold rowCoef
    simpa using this
  rw [hc, lsum_mul_right]
  refine lsum_congr _ fun t _ => ?_
  ring

/-! ### The Gram operator, entrywise -/

/-- The entries `Σ_{σ,m} w_p(m) r_{σ,m}(α) r_{σ,m}(β)` of the Gram operator (integer valued). -/
def gramInt (p : Fin 4 → ℕ) (v : List (ℕ × ℤ)) (α β : Cfg 6) : ℤ :=
  ∑ x ∈ QVCert.rowIdx p, (∏ k : Fin 4, (QVCert.weight (p k) (x.2 k) : ℤ)) *
    rowCoef p v x.1 x.2 α * rowCoef p v x.1 x.2 β

theorem lsum_matrix_apply {α : Type*} {m n : Type*} (L : List α) (f : α → Matrix m n ℤ) (i : m) (j : n) :
    lsum L f i j = lsum L (fun s => f s i j) := by
  induction L with
  | nil => simp [lsum]
  | cons a L ih => simp [lsum_cons, ih]

theorem inner_sum (p : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) (α β : Cfg 6) (μ μ' : Fin 4 → ℕ) :
    ∑ m ∈ Fintype.piFinset (fun k => range (p k + 1)),
        (∏ k : Fin 4, (QVCert.weight (p k) (m k) : ℤ)) *
          ((∏ k : Fin 4, rowW (p k) (m k) (μ k) (α (σ k))) *
            ∏ k : Fin 4, rowW (p k) (m k) (μ' k) (β (σ k))) =
      ∏ q : Fin 4, Eop (p (σ.symm q)) (μ (σ.symm q)) (μ' (σ.symm q)) (α q) (β q) := by
  have h1 : ∀ m : Fin 4 → ℕ, (∏ k : Fin 4, (QVCert.weight (p k) (m k) : ℤ)) *
          ((∏ k : Fin 4, rowW (p k) (m k) (μ k) (α (σ k))) *
            ∏ k : Fin 4, rowW (p k) (m k) (μ' k) (β (σ k))) =
      ∏ k : Fin 4, ((QVCert.weight (p k) (m k) : ℤ) *
        (rowW (p k) (m k) (μ k) (α (σ k)) * rowW (p k) (m k) (μ' k) (β (σ k)))) := by
    intro m
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [h1]
  rw [← Finset.prod_univ_sum (fun k => range (p k + 1))
    (fun k m => ((QVCert.weight (p k) m : ℤ) *
        (rowW (p k) m (μ k) (α (σ k)) * rowW (p k) m (μ' k) (β (σ k)))))]
  have h2 : ∀ k : Fin 4, ∑ m ∈ range (p k + 1), ((QVCert.weight (p k) m : ℤ) *
        (rowW (p k) m (μ k) (α (σ k)) * rowW (p k) m (μ' k) (β (σ k)))) =
      Eop (p k) (μ k) (μ' k) (α (σ k)) (β (σ k)) := by
    intro k
    simp only [Eop, Matrix.of_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp only [h2]
  have := Equiv.prod_comp σ (fun q : Fin 4 => Eop (p (σ.symm q)) (μ (σ.symm q)) (μ' (σ.symm q)) (α q) (β q))
  simpa using this

theorem gramInt_eq (p : Fin 4 → ℕ) (v : List (ℕ × ℤ)) (α β : Cfg 6) :
    gramInt p v α β = gramOp p v α β := by
  unfold gramInt gramOp QVCert.rowIdx
  rw [Finset.sum_product, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key : ∀ m : Fin 4 → ℕ, (∏ k : Fin 4, (QVCert.weight (p k) (m k) : ℤ)) *
      rowCoef p v σ m α * rowCoef p v σ m β =
      lsum v fun s => lsum v fun s' => (s.2 * s'.2) *
        ((∏ k : Fin 4, (QVCert.weight (p k) (m k) : ℤ)) *
          ((∏ k : Fin 4, rowW (p k) (m k) (QVCert.muDigit p s.1 k) (α (σ k))) *
            ∏ k : Fin 4, rowW (p k) (m k) (QVCert.muDigit p s'.1 k) (β (σ k)))) := by
    intro m
    unfold rowCoef
    rw [mul_assoc, lsum_mul_lsum, lsum_mul_left]
    refine lsum_congr _ fun s _ => ?_
    rw [lsum_mul_left]
    refine lsum_congr _ fun s' _ => ?_
    ring
  simp only [key]
  rw [sum_lsum_comm, lsum_matrix_apply]
  refine lsum_congr _ fun s _ => ?_
  rw [sum_lsum_comm, lsum_matrix_apply]
  refine lsum_congr _ fun s' _ => ?_
  rw [← Finset.mul_sum, inner_sum p σ α β (QVCert.muDigit p s.1) (QVCert.muDigit p s'.1)]
  simp [kronPi_apply]

/-- **T1.** For every block `b` and covariant `i`,
`‖Φ_{ki}(z)‖²_w = ⟨w_a(z), A_{ki} w_a(z)⟩` with `A = gramOp` and `⟨·,·⟩` the Hermitian form
(`qf (conj w) A w`). -/
theorem normSqPhi_eq_qf (b : QVCert.Block) (z : Psi) (i : ℕ) :
    ((b.normSqPhi z i : ℝ) : ℂ) =
      qf (wvecBar b.a z) ((gramOp b.spins (b.vecs.getD i [])).map (Int.castRingHom ℂ))
        (wvec b.a z) := by
  set v := b.vecs.getD i [] with hv
  have hx : ∀ x : Equiv.Perm (Fin 4) × (Fin 4 → ℕ),
      ((QVCert.wp b.spins x.2 : ℝ) : ℂ) * (conj (b.Phi z i x) * b.Phi z i x) =
      ∑ α : Cfg 6, ∑ β : Cfg 6, wvecBar b.a z α *
        (((∏ k : Fin 4, (QVCert.weight (b.spins k) (x.2 k) : ℤ)) * rowCoef b.spins v x.1 x.2 α *
          rowCoef b.spins v x.1 x.2 β : ℤ) : ℂ) * wvec b.a z β := by
    intro x
    have h1 : conj (b.Phi z i x) = ∑ α : Cfg 6, ((rowCoef b.spins v x.1 x.2 α : ℤ) : ℂ) * wvecBar b.a z α := by
      rw [Phi_eq, map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_mul, map_intCast, conj_wvec]
    rw [h1, Phi_eq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hw : ((QVCert.wp b.spins x.2 : ℝ) : ℂ) =
        (((∏ k : Fin 4, (QVCert.weight (b.spins k) (x.2 k) : ℤ)) : ℤ) : ℂ) := by
      unfold QVCert.wp; push_cast; rfl
    rw [hw]; push_cast; ring
  unfold QVCert.Block.normSqPhi QVCert.wnormSq
  rw [Complex.ofReal_sum]
  have h2 : ∀ x : Equiv.Perm (Fin 4) × (Fin 4 → ℕ), ((QVCert.wp b.spins x.2 * Complex.normSq (b.Phi z i x) : ℝ) : ℂ) =
      ((QVCert.wp b.spins x.2 : ℝ) : ℂ) * (conj (b.Phi z i x) * b.Phi z i x) := by
    intro x
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  simp only [h2, hx]
  rw [Finset.sum_comm]
  unfold qf
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have := gramInt_eq b.spins v α β
  rw [Matrix.map_apply, ← this]
  unfold gramInt
  simp

end FormalResearch.FourQubitEntropy.QVFrame

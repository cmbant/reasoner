module

public import ThreeCopyQutritWerner.Elementary
public import ThreeCopyQutritWerner.WernerPT

@[expose] public section


/-!
# The physical expectation value (manuscript eq. (6), the expectation identity)

For the model definitions of `Basic`, the expectation of the partially transposed
Werner state in a vectorized coefficient matrix is the one-factor form
`‖C‖_F² - α |Tr C|²` divided by `d (d - α)`.
-/

namespace ThreeCopyQutritWerner

section Helpers

/-- Collapse of a Kronecker delta in a finite sum. -/
theorem sum_mul_delta {a : Type*} [Fintype a] [DecidableEq a] (i : a) (g : a → ℂ) :
    ∑ k, g k * (if i = k then (1 : ℂ) else 0) = g i := by
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb
    simp only [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- One-site contraction: the kernel `δδ - t Ω` against an arbitrary four-index array. -/
theorem site_contract {a : Type*} [Fintype a] [DecidableEq a] (F : a → a → a → a → ℂ) (t : ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
          t * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))) =
      (∑ i, ∑ j, F i j i j) - t * ∑ i, ∑ k, F i i k k := by
  have hA : ∀ i j, ∑ k, ∑ l, F i j k l *
      ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)) = F i j i j := by
    intro i j
    have hl : ∀ k, ∑ l, F i j k l *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)) =
        F i j k j * (if i = k then (1 : ℂ) else 0) := by
      intro k
      have h1 : ∑ l, F i j k l * (if i = k then (1 : ℂ) else 0) *
          (if j = l then (1 : ℂ) else 0) = F i j k j * (if i = k then (1 : ℂ) else 0) :=
        sum_mul_delta j (fun l => F i j k l * (if i = k then (1 : ℂ) else 0))
      rw [← h1]
      exact Finset.sum_congr rfl fun l _ => by ring
    have h2 : ∑ k, F i j k j * (if i = k then (1 : ℂ) else 0) = F i j i j :=
      sum_mul_delta i (fun k => F i j k j)
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => hl k
  have hB : ∀ i j, ∑ k, ∑ l, F i j k l *
      ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0)) =
      (∑ k, F i j k k) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ∑ l, F i j k l * (if i = j then (1 : ℂ) else 0) *
        (if k = l then (1 : ℂ) else 0) = F i j k k * (if i = j then (1 : ℂ) else 0) :=
      sum_mul_delta k (fun l => F i j k l * (if i = j then (1 : ℂ) else 0))
    rw [← h1]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hsplit : ∀ i j, ∑ k, ∑ l, F i j k l *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
          t * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))) =
      F i j i j - t * ((∑ k, F i j k k) * (if i = j then (1 : ℂ) else 0)) := by
    intro i j
    rw [← hA i j, ← hB i j, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hi : ∀ i, ∑ j, (F i j i j - t * ((∑ k, F i j k k) * (if i = j then (1 : ℂ) else 0))) =
      (∑ j, F i j i j) - t * ∑ k, F i i k k := by
    intro i
    have h3 : ∑ j, (∑ k, F i j k k) * (if i = j then (1 : ℂ) else 0) = ∑ k, F i i k k :=
      sum_mul_delta i (fun j => ∑ k, F i j k k)
    rw [Finset.sum_sub_distrib, ← h3, Finset.mul_sum]
  have h1 : ∑ i, ∑ j, ∑ k, ∑ l, F i j k l *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
          t * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))) =
      ∑ i, ((∑ j, F i j i j) - t * ∑ k, F i i k k) :=
    Finset.sum_congr rfl fun i _ => (Finset.sum_congr rfl fun j _ => hsplit i j).trans (hi i)
  rw [h1, Finset.sum_sub_distrib, Finset.mul_sum]

/-- A constant factor comes out of a fourfold sum. -/
theorem mul_sum₄ {a : Type*} [Fintype a] (c : ℂ) (G : a → a → a → a → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, c * G i j k l = c * ∑ i, ∑ j, ∑ k, ∑ l, G i j k l := by
  simp only [Finset.mul_sum]

/-- The squared Frobenius norm as a complex sum. -/
theorem ofReal_frobSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ((frobSq M : ℝ) : ℂ) = ∑ i, ∑ j, star (M i j) * M i j := by
  unfold frobSq
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => Complex.normSq_eq_conj_mul_self

/-- The squared modulus of the trace as a complex double sum. -/
theorem ofReal_normSq_trace {n : Type*} [Fintype n] (M : Matrix n n ℂ) :
    ((Complex.normSq M.trace : ℝ) : ℂ) = ∑ i, ∑ k, star (M i i) * M k k := by
  have h : ((Complex.normSq M.trace : ℝ) : ℂ) = star M.trace * M.trace :=
    Complex.normSq_eq_conj_mul_self
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [star_sum, Finset.sum_mul_sum]

/-- Entries of the identity on a product index type. -/
theorem one_apply_prod {a : Type*} [DecidableEq a] (i j k l : a) :
    (1 : Matrix (a × a) (a × a) ℂ) (i, j) (k, l) =
      (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) := by
  by_cases h1 : i = k <;> by_cases h2 : j = l <;>
    simp [Matrix.one_apply, Prod.mk.injEq, h1, h2]

/-- Entries of `Ω`. -/
theorem omegaOp_apply_prod {a : Type*} [DecidableEq a] (i j k l : a) :
    omegaOp a (i, j) (k, l) =
      (if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0) := by
  by_cases h1 : i = j <;> by_cases h2 : k = l <;> simp [omegaOp, h1, h2]

end Helpers

/-- Entries of the partially transposed Werner state. -/
theorem partialTranspose_werner_apply (d : ℕ) (α : ℝ) (i j k l : Fin d) :
    partialTranspose (werner d α) (i, j) (k, l) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) *
        ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
          (α : ℂ) * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))) := by
  rw [partialTranspose_werner]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, one_apply_prod,
    omegaOp_apply_prod]
  first | done | ring

/-- One-copy form of manuscript eq. (6):
`⟨vec C, ρ_{d,α}^Γ vec C⟩ = (‖C‖_F² - α |Tr C|²) / (d (d - α))`. -/
theorem expectation_partialTranspose_werner (d : ℕ) (α : ℝ) (C : Matrix (Fin d) (Fin d) ℂ) :
    expectation (partialTranspose (werner d α)) (vec C) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * ((frobSq C - α * Complex.normSq C.trace : ℝ) : ℂ) := by
  have hkey : ∀ i j k l : Fin d,
      star (C i j) * partialTranspose (werner d α) (i, j) (k, l) * C k l =
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * (star (C i j) * C k l *
          ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
            (α : ℂ) * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0)))) := by
    intro i j k l
    rw [partialTranspose_werner_apply]
    ring
  have hsum : expectation (partialTranspose (werner d α)) (vec C) =
      ∑ i, ∑ j, ∑ k, ∑ l, (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * (star (C i j) * C k l *
          ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
            (α : ℂ) * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0)))) := by
    unfold expectation
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hkey i j k l
  have hpull := mul_sum₄ (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹)
    (fun i j k l : Fin d => star (C i j) * C k l *
      ((if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
        (α : ℂ) * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))))
  have hc := site_contract (fun i j k l : Fin d => star (C i j) * C k l) (α : ℂ)
  have hfin : (∑ i, ∑ j, star (C i j) * C i j) - (α : ℂ) * ∑ i, ∑ k, star (C i i) * C k k =
      ((frobSq C - α * Complex.normSq C.trace : ℝ) : ℂ) := by
    rw [← ofReal_frobSq C, ← ofReal_normSq_trace C, Complex.ofReal_sub, Complex.ofReal_mul]
  rw [hsum]
  exact hpull.trans
    (congrArg (fun z => (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * z) (hc.trans hfin))

/-! ## Three copies -/

/-- The one-site kernel `δδ - t Ω` (the entries of `1 - t Ω`). -/
noncomputable def siteKer {a : Type*} [DecidableEq a] (t : ℂ) (i j k l : a) : ℂ :=
  (if i = k then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0) -
    t * ((if i = j then (1 : ℂ) else 0) * (if k = l then (1 : ℂ) else 0))

theorem partialTranspose_werner_apply' (d : ℕ) (α : ℝ) (i j k l : Fin d) :
    partialTranspose (werner d α) (i, j) (k, l) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) * siteKer (α : ℂ) i j k l :=
  partialTranspose_werner_apply d α i j k l

theorem site_contract' {a : Type*} [Fintype a] [DecidableEq a] (F : a → a → a → a → ℂ)
    (t : ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l * siteKer t i j k l =
      (∑ i, ∑ j, F i j i j) - t * ∑ i, ∑ k, F i i k k :=
  site_contract F t

section Reorder

theorem sum_comm₂₂ {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    ∑ p, ∑ q, ∑ u, ∑ v, F p q u v = ∑ u, ∑ v, ∑ p, ∑ q, F p q u v := by
  calc ∑ p, ∑ q, ∑ u, ∑ v, F p q u v
      = ∑ p, ∑ u, ∑ q, ∑ v, F p q u v := Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ u, ∑ p, ∑ q, ∑ v, F p q u v := Finset.sum_comm
    _ = ∑ u, ∑ p, ∑ v, ∑ q, F p q u v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ u, ∑ v, ∑ p, ∑ q, F p q u v := Finset.sum_congr rfl fun u _ => Finset.sum_comm

theorem sum_interleave₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (G : α → β → γ → α → β → γ → ℂ) :
    ∑ x, ∑ i, ∑ p, ∑ y, ∑ j, ∑ q, G x i p y j q =
      ∑ x, ∑ y, ∑ i, ∑ j, ∑ p, ∑ q, G x i p y j q := by
  calc ∑ x, ∑ i, ∑ p, ∑ y, ∑ j, ∑ q, G x i p y j q
      = ∑ x, ∑ i, ∑ y, ∑ p, ∑ j, ∑ q, G x i p y j q :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ p, ∑ j, ∑ q, G x i p y j q :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ i, ∑ j, ∑ p, ∑ q, G x i p y j q :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem sum_regroup₈ {a b : Type*} [Fintype a] [Fintype b]
    (G : a → b → a → b → a → b → a → b → ℂ) :
    ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, G i I j J k K l L =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ I, ∑ J, ∑ K, ∑ L, G i I j J k K l L := by
  calc ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, G i I j J k K l L
      = ∑ i, ∑ j, ∑ I, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ I, ∑ k, ∑ J, ∑ K, ∑ l, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ I, ∑ J, ∑ K, ∑ l, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ I, ∑ J, ∑ l, ∑ K, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun I _ =>
            Finset.sum_congr rfl fun J _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ I, ∑ l, ∑ J, ∑ K, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun I _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, ∑ I, ∑ J, ∑ K, ∑ L, G i I j J k K l L :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem mul_sum₈ {a b : Type*} [Fintype a] [Fintype b] (c : ℂ)
    (G : a → b → a → b → a → b → a → b → ℂ) :
    ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, c * G i I j J k K l L =
      c * ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, G i I j J k K l L := by
  simp only [Finset.mul_sum]

theorem sum₂_sub_mul {a b : Type*} [Fintype a] [Fintype b] (X Y : a → b → ℂ) (t : ℂ) :
    ∑ i, ∑ j, (X i j - t * Y i j) = (∑ i, ∑ j, X i j) - t * ∑ i, ∑ j, Y i j := by
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

theorem sum₂_four {a b : Type*} [Fintype a] [Fintype b] (X1 X2 X3 X4 : a → b → ℂ) (t : ℂ) :
    ∑ i, ∑ j, (X1 i j - t * X2 i j - t * (X3 i j - t * X4 i j)) =
      (∑ i, ∑ j, X1 i j) - t * (∑ i, ∑ j, X2 i j) -
        t * ((∑ i, ∑ j, X3 i j) - t * ∑ i, ∑ j, X4 i j) := by
  rw [← sum₂_sub_mul X1 X2 t, ← sum₂_sub_mul X3 X4 t]
  exact sum₂_sub_mul (fun i j => X1 i j - t * X2 i j) (fun i j => X3 i j - t * X4 i j) t

end Reorder

/-- Contract one site of a two-part system: the site sums `i j k l` against `siteKer`,
with the remaining indices `I J K L` left summed. -/
theorem site_peel {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    (H : a → b → a → b → a → b → a → b → ℂ) (t : ℂ) :
    ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, H i I j J k K l L * siteKer t i j k l =
      (∑ i, ∑ j, ∑ I, ∑ J, ∑ K, ∑ L, H i I j J i K j L) -
        t * ∑ i, ∑ k, ∑ I, ∑ J, ∑ K, ∑ L, H i I i J k K k L := by
  have h1 : ∑ i, ∑ I, ∑ j, ∑ J, ∑ k, ∑ K, ∑ l, ∑ L, H i I j J k K l L * siteKer t i j k l =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ I, ∑ J, ∑ K, ∑ L, H i I j J k K l L * siteKer t i j k l :=
    sum_regroup₈ (fun i I j J k K l L => H i I j J k K l L * siteKer t i j k l)
  have h2 : ∀ i j k l, ∑ I, ∑ J, ∑ K, ∑ L, H i I j J k K l L * siteKer t i j k l =
      (∑ I, ∑ J, ∑ K, ∑ L, H i I j J k K l L) * siteKer t i j k l := by
    intro i j k l
    simp only [Finset.sum_mul]
  have h3 : ∑ i, ∑ j, ∑ k, ∑ l,
        (∑ I, ∑ J, ∑ K, ∑ L, H i I j J k K l L) * siteKer t i j k l =
      (∑ i, ∑ j, ∑ I, ∑ J, ∑ K, ∑ L, H i I j J i K j L) -
        t * ∑ i, ∑ k, ∑ I, ∑ J, ∑ K, ∑ L, H i I i J k K k L :=
    site_contract' (fun i j k l => ∑ I, ∑ J, ∑ K, ∑ L, H i I j J k K l L) t
  rw [h1]
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h2 i j k l).trans h3

/-- Contract both sites of a two-site system against the product kernel. -/
theorem pair_contract {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ : a × b → a × b → a × b → a × b → ℂ) (t : ℂ) :
    ∑ I, ∑ J, ∑ K, ∑ L,
        Φ I J K L * (siteKer t I.1 J.1 K.1 L.1 * siteKer t I.2 J.2 K.2 L.2) =
      (∑ i, ∑ j, ∑ p, ∑ q, Φ (i, p) (j, q) (i, p) (j, q)) -
          t * (∑ i, ∑ j, ∑ p, ∑ r, Φ (i, p) (j, p) (i, r) (j, r)) -
        t * ((∑ i, ∑ k, ∑ p, ∑ q, Φ (i, p) (i, q) (k, p) (k, q)) -
          t * ∑ i, ∑ k, ∑ p, ∑ r, Φ (i, p) (i, p) (k, r) (k, r)) := by
  have hflat : ∑ I, ∑ J, ∑ K, ∑ L,
        Φ I J K L * (siteKer t I.1 J.1 K.1 L.1 * siteKer t I.2 J.2 K.2 L.2) =
      ∑ i, ∑ p, ∑ j, ∑ q, ∑ k, ∑ r, ∑ l, ∑ s,
        Φ (i, p) (j, q) (k, r) (l, s) * siteKer t p q r s * siteKer t i j k l := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  have hpeel : ∑ i, ∑ p, ∑ j, ∑ q, ∑ k, ∑ r, ∑ l, ∑ s,
        Φ (i, p) (j, q) (k, r) (l, s) * siteKer t p q r s * siteKer t i j k l =
      (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, ∑ s, Φ (i, p) (j, q) (i, r) (j, s) * siteKer t p q r s) -
        t * ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
          Φ (i, p) (i, q) (k, r) (k, s) * siteKer t p q r s :=
    site_peel (fun i p j q k r l s => Φ (i, p) (j, q) (k, r) (l, s) * siteKer t p q r s) t
  have h1 : ∑ i, ∑ j, ∑ p, ∑ q, ∑ r, ∑ s,
        Φ (i, p) (j, q) (i, r) (j, s) * siteKer t p q r s =
      (∑ i, ∑ j, ∑ p, ∑ q, Φ (i, p) (j, q) (i, p) (j, q)) -
        t * ∑ i, ∑ j, ∑ p, ∑ r, Φ (i, p) (j, p) (i, r) (j, r) :=
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      site_contract' (fun p q r s => Φ (i, p) (j, q) (i, r) (j, s)) t).trans
      (sum₂_sub_mul (fun i j => ∑ p, ∑ q, Φ (i, p) (j, q) (i, p) (j, q))
        (fun i j => ∑ p, ∑ r, Φ (i, p) (j, p) (i, r) (j, r)) t)
  have h2 : ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        Φ (i, p) (i, q) (k, r) (k, s) * siteKer t p q r s =
      (∑ i, ∑ k, ∑ p, ∑ q, Φ (i, p) (i, q) (k, p) (k, q)) -
        t * ∑ i, ∑ k, ∑ p, ∑ r, Φ (i, p) (i, p) (k, r) (k, r) :=
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      site_contract' (fun p q r s => Φ (i, p) (i, q) (k, r) (k, s)) t).trans
      (sum₂_sub_mul (fun i k => ∑ p, ∑ q, Φ (i, p) (i, q) (k, p) (k, q))
        (fun i k => ∑ p, ∑ r, Φ (i, p) (i, p) (k, r) (k, r)) t)
  rw [hflat, hpeel, h1, h2]

section Identify

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

theorem ofReal_frobSq_three (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq C : ℝ) : ℂ) =
      ∑ x, ∑ y, ∑ i, ∑ j, ∑ p, ∑ q,
        star (C (x, i, p) (y, j, q)) * C (x, i, p) (y, j, q) := by
  rw [ofReal_frobSq]
  simp only [Fintype.sum_prod_type]
  exact sum_interleave₃
    (fun x i p y j q => star (C (x, i, p) (y, j, q)) * C (x, i, p) (y, j, q))

theorem ofReal_frobSq_ptrace₃ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₃ C) : ℝ) : ℂ) =
      ∑ x, ∑ y, ∑ i, ∑ j, ∑ p, ∑ r,
        star (C (x, i, p) (y, j, p)) * C (x, i, r) (y, j, r) := by
  rw [ofReal_frobSq]
  simp only [ptrace₃, Fintype.sum_prod_type, star_sum, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

theorem ofReal_frobSq_ptrace₂ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₂ C) : ℝ) : ℂ) =
      ∑ x, ∑ y, ∑ i, ∑ k, ∑ p, ∑ q,
        star (C (x, i, p) (y, i, q)) * C (x, k, p) (y, k, q) := by
  rw [ofReal_frobSq]
  simp only [ptrace₂, Fintype.sum_prod_type, star_sum, Finset.sum_mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun x _ => Finset.sum_comm) ?_
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => sum_comm₂₂ _

theorem ofReal_frobSq_ptrace₂₃ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₂₃ C) : ℝ) : ℂ) =
      ∑ x, ∑ y, ∑ i, ∑ k, ∑ p, ∑ r,
        star (C (x, i, p) (y, i, p)) * C (x, k, r) (y, k, r) := by
  rw [ofReal_frobSq]
  simp only [ptrace₂₃, star_sum, Finset.sum_mul_sum]
  first
    | done
    | rfl
    | exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem ofReal_frobSq_ptrace₁ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₁ C) : ℝ) : ℂ) =
      ∑ x, ∑ z, ∑ i, ∑ j, ∑ p, ∑ q,
        star (C (x, i, p) (x, j, q)) * C (z, i, p) (z, j, q) := by
  rw [ofReal_frobSq]
  simp only [ptrace₁, Fintype.sum_prod_type, star_sum, Finset.sum_mul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm) ?_
  refine Eq.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sum_comm₂₂ _) ?_
  exact sum_comm₂₂ _

theorem ofReal_frobSq_ptrace₁₃ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₁₃ C) : ℝ) : ℂ) =
      ∑ x, ∑ z, ∑ i, ∑ j, ∑ p, ∑ r,
        star (C (x, i, p) (x, j, p)) * C (z, i, r) (z, j, r) := by
  rw [ofReal_frobSq]
  simp only [ptrace₁₃, star_sum, Finset.sum_mul_sum]
  exact sum_comm₂₂ _

theorem ofReal_frobSq_ptrace₁₂ (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((frobSq (ptrace₁₂ C) : ℝ) : ℂ) =
      ∑ x, ∑ z, ∑ i, ∑ k, ∑ p, ∑ q,
        star (C (x, i, p) (x, i, q)) * C (z, k, p) (z, k, q) := by
  rw [ofReal_frobSq]
  simp only [ptrace₁₂, star_sum, Finset.sum_mul_sum]
  refine Eq.trans (sum_comm₂₂ _) ?_
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => sum_comm₂₂ _

theorem ofReal_normSq_trace_three (C : Matrix (a × b × c) (a × b × c) ℂ) :
    ((Complex.normSq C.trace : ℝ) : ℂ) =
      ∑ x, ∑ z, ∑ i, ∑ k, ∑ p, ∑ r,
        star (C (x, i, p) (x, i, p)) * C (z, k, r) (z, k, r) := by
  rw [ofReal_normSq_trace]
  simp only [Fintype.sum_prod_type]
  exact sum_interleave₃
    (fun x i p z k r => star (C (x, i, p) (x, i, p)) * C (z, k, r) (z, k, r))

end Identify

/-- Manuscript eq. (6), the expectation identity, for three copies:
`⟨vec C, (ρ_{d,α}^{⊗3})^Γ vec C⟩ = q_α(C) / (d (d - α))³`. -/
theorem expectation_partialTranspose_tripleCopy_werner (d : ℕ) (α : ℝ)
    (C : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ) :
    expectation (partialTranspose (tripleCopy (werner d α))) (vec C) =
      (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 * ((energy α C : ℝ) : ℂ) := by
  have hkey : ∀ (i : Fin d) (I : Fin d × Fin d) (j : Fin d) (J : Fin d × Fin d)
      (k : Fin d) (K : Fin d × Fin d) (l : Fin d) (L : Fin d × Fin d),
      star (vec C ((i, I), (j, J))) *
          partialTranspose (tripleCopy (werner d α)) ((i, I), (j, J)) ((k, K), (l, L)) *
          vec C ((k, K), (l, L)) =
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 *
          (star (C (i, I) (j, J)) * C (k, K) (l, L) *
            (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2) *
            siteKer (α : ℂ) i j k l) := by
    intro i I j J k K l L
    show star (C (i, I) (j, J)) *
        (partialTranspose (werner d α) (i, j) (k, l) *
          partialTranspose (werner d α) (I.1, J.1) (K.1, L.1) *
          partialTranspose (werner d α) (I.2, J.2) (K.2, L.2)) * C (k, K) (l, L) = _
    simp only [partialTranspose_werner_apply']
    ring
  have hsum : expectation (partialTranspose (tripleCopy (werner d α))) (vec C) =
      ∑ i : Fin d, ∑ I : Fin d × Fin d, ∑ j : Fin d, ∑ J : Fin d × Fin d,
        ∑ k : Fin d, ∑ K : Fin d × Fin d, ∑ l : Fin d, ∑ L : Fin d × Fin d,
        (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 *
          (star (C (i, I) (j, J)) * C (k, K) (l, L) *
            (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2) *
            siteKer (α : ℂ) i j k l) := by
    unfold expectation
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun K _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun L _ =>
      hkey i I j J k K l L
  have hpull := mul_sum₈ ((((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3)
    (fun (i : Fin d) (I : Fin d × Fin d) (j : Fin d) (J : Fin d × Fin d)
        (k : Fin d) (K : Fin d × Fin d) (l : Fin d) (L : Fin d × Fin d) =>
      star (C (i, I) (j, J)) * C (k, K) (l, L) *
        (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2) *
        siteKer (α : ℂ) i j k l)
  have hpeel := site_peel
    (fun (i : Fin d) (I : Fin d × Fin d) (j : Fin d) (J : Fin d × Fin d)
        (k : Fin d) (K : Fin d × Fin d) (l : Fin d) (L : Fin d × Fin d) =>
      star (C (i, I) (j, J)) * C (k, K) (l, L) *
        (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2)) (α : ℂ)
  have hTa : ∑ x : Fin d, ∑ y : Fin d, ∑ I : Fin d × Fin d, ∑ J : Fin d × Fin d,
        ∑ K : Fin d × Fin d, ∑ L : Fin d × Fin d,
        star (C (x, I) (y, J)) * C (x, K) (y, L) *
          (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2) =
      ((frobSq C : ℝ) : ℂ) - (α : ℂ) * ((frobSq (ptrace₃ C) : ℝ) : ℂ) -
        (α : ℂ) * (((frobSq (ptrace₂ C) : ℝ) : ℂ) -
          (α : ℂ) * ((frobSq (ptrace₂₃ C) : ℝ) : ℂ)) := by
    rw [ofReal_frobSq_three C, ofReal_frobSq_ptrace₃ C, ofReal_frobSq_ptrace₂ C,
      ofReal_frobSq_ptrace₂₃ C, ← sum₂_four]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      pair_contract (fun I J K L => star (C (x, I) (y, J)) * C (x, K) (y, L)) (α : ℂ)
  have hTb : ∑ x : Fin d, ∑ z : Fin d, ∑ I : Fin d × Fin d, ∑ J : Fin d × Fin d,
        ∑ K : Fin d × Fin d, ∑ L : Fin d × Fin d,
        star (C (x, I) (x, J)) * C (z, K) (z, L) *
          (siteKer (α : ℂ) I.1 J.1 K.1 L.1 * siteKer (α : ℂ) I.2 J.2 K.2 L.2) =
      ((frobSq (ptrace₁ C) : ℝ) : ℂ) - (α : ℂ) * ((frobSq (ptrace₁₃ C) : ℝ) : ℂ) -
        (α : ℂ) * (((frobSq (ptrace₁₂ C) : ℝ) : ℂ) -
          (α : ℂ) * ((Complex.normSq C.trace : ℝ) : ℂ)) := by
    rw [ofReal_frobSq_ptrace₁ C, ofReal_frobSq_ptrace₁₃ C, ofReal_frobSq_ptrace₁₂ C,
      ofReal_normSq_trace_three C, ← sum₂_four]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ =>
      pair_contract (fun I J K L => star (C (x, I) (x, J)) * C (z, K) (z, L)) (α : ℂ)
  rw [hsum]
  refine Eq.trans hpull ?_
  refine congrArg (fun w => (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) ^ 3 * w) ?_
  refine Eq.trans hpeel ?_
  rw [hTa, hTb]
  simp only [energy, invN, invA, invB, invT]
  push_cast
  ring

/-! ## Thresholds in the Schmidt-rank-two criterion form (`d = 3`) -/

/-- Every vector on `A × B` is the vectorization of its coefficient matrix. -/
theorem eq_vec_of {A B : Type*} (ψ : A × B → ℂ) :
    ψ = vec (Matrix.of fun x y => ψ (x, y)) := by
  funext ⟨x, y⟩
  rfl

/-- For `d = 3` the normalization `1 / (d (d - α))` is the cast of a real number. -/
theorem werner_three_scalar (α : ℝ) :
    (((3 : ℕ) : ℂ) * (((3 : ℕ) : ℂ) - (α : ℂ)))⁻¹ = (((3 * (3 - α))⁻¹ : ℝ) : ℂ) := by
  first
    | (push_cast; done)
    | (push_cast; ring)
    | norm_num

theorem re_expectation_partialTranspose_werner_three (α : ℝ) (C : Matrix (Fin 3) (Fin 3) ℂ) :
    (expectation (partialTranspose (werner 3 α)) (vec C)).re =
      (3 * (3 - α))⁻¹ * (frobSq C - α * Complex.normSq C.trace) := by
  rw [expectation_partialTranspose_werner, werner_three_scalar, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem re_expectation_partialTranspose_tripleCopy_werner_three (α : ℝ)
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    (expectation (partialTranspose (tripleCopy (werner 3 α))) (vec C)).re =
      ((3 * (3 - α))⁻¹) ^ 3 * energy α C := by
  rw [expectation_partialTranspose_tripleCopy_werner, werner_three_scalar,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- One-copy threshold in the Schmidt-rank-two criterion form: for `-1 ≤ α ≤ 1` the qutrit
Werner state satisfies the one-copy criterion exactly when `α > 1/2`. -/
theorem isOneCopyRankTwoDetectable_werner_three_iff {α : ℝ} (hm : -1 ≤ α) (h1 : α ≤ 1) :
    IsOneCopyRankTwoDetectable (werner 3 α) ↔ 1 / 2 < α := by
  have hpos : (0 : ℝ) < (3 * (3 - α))⁻¹ := inv_pos.mpr (by linarith)
  constructor
  · rintro ⟨ψ, hψ, hneg⟩
    by_contra hα
    have hα' : α ≤ 1 / 2 := not_lt.mp hα
    obtain ⟨C, rfl⟩ : ∃ C : Matrix (Fin 3) (Fin 3) ℂ, ψ = vec C := ⟨_, eq_vec_of ψ⟩
    have hrank : C.rank ≤ 2 := (schmidtRankLE_vec_iff C 2).mp hψ
    have hnn := frobSq_sub_mul_normSq_trace_nonneg C hrank hα'
    rw [re_expectation_partialTranspose_werner_three] at hneg
    have hprod := mul_nonneg hpos.le hnn
    linarith
  · intro hα
    refine ⟨vec scaledPlaneProj, (schmidtRankLE_vec_iff scaledPlaneProj 2).mpr ?_, ?_⟩
    · exact rank_le_two_of_eq_mul scaledPlaneProj
        (Matrix.of fun (i : Fin 3) (k : Fin 2) => halfPhase * planeVec k i)
        (Matrix.of fun (k : Fin 2) (j : Fin 3) => planeVec k j) (by
          ext i j
          simp only [scaledPlaneProj, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two]
          ring)
    · rw [re_expectation_partialTranspose_werner_three, frobSq_scaledPlaneProj,
        normSq_trace_scaledPlaneProj]
      exact mul_neg_of_pos_of_neg hpos (by linarith)

/-- Three-copy criterion for `1/2 < α ≤ 1` (manuscript Corollary 2.2, `α > 1/2`). -/
theorem isThreeCopyRankTwoDetectable_werner_three {α : ℝ} (h : 1 / 2 < α) (h1 : α ≤ 1) :
    IsThreeCopyRankTwoDetectable (werner 3 α) := by
  have hpos : (0 : ℝ) < ((3 * (3 - α))⁻¹) ^ 3 := pow_pos (inv_pos.mpr (by linarith)) 3
  refine ⟨vec distillWitness,
    (schmidtRankLE_vec_iff distillWitness 2).mpr rank_distillWitness, ?_⟩
  rw [re_expectation_partialTranspose_tripleCopy_werner_three, energy_distillWitness]
  exact mul_neg_of_pos_of_neg hpos (by linarith)

/-- For `α ≤ 0` no vector at all has negative expectation, so the three-copy criterion
fails. -/
theorem not_isThreeCopyRankTwoDetectable_werner_three_of_nonpos {α : ℝ} (h0 : α ≤ 0) :
    ¬ IsThreeCopyRankTwoDetectable (werner 3 α) := by
  rintro ⟨ψ, _, hneg⟩
  obtain ⟨C, rfl⟩ : ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      ψ = vec C := ⟨_, eq_vec_of ψ⟩
  have hpos : (0 : ℝ) ≤ ((3 * (3 - α))⁻¹) ^ 3 :=
    pow_nonneg (inv_nonneg.mpr (by linarith)) 3
  rw [re_expectation_partialTranspose_tripleCopy_werner_three] at hneg
  have hprod := mul_nonneg hpos (energy_nonneg_of_nonpos C h0)
  linarith

/-- CONDITIONAL: the two hypotheses are open claims of the project. -/
theorem not_isThreeCopyRankTwoDetectable_werner_three_of_forms {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2)
    (hq : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ endpointEnergy C)
    (hS : ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      C.rank ≤ 2 → 0 ≤ formS C) :
    ¬ IsThreeCopyRankTwoDetectable (werner 3 α) := by
  rintro ⟨ψ, hψ, hneg⟩
  obtain ⟨C, rfl⟩ : ∃ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
      ψ = vec C := ⟨_, eq_vec_of ψ⟩
  have hrank : C.rank ≤ 2 := (schmidtRankLE_vec_iff C 2).mp hψ
  have hpos : (0 : ℝ) ≤ ((3 * (3 - α))⁻¹) ^ 3 :=
    pow_nonneg (inv_nonneg.mpr (by linarith)) 3
  have hE : 0 ≤ energy α C :=
    le_trans (mul_nonneg (sharpCurve_nonneg h1) (invN_nonneg C))
      (sharpCurve_mul_invN_le_energy_of_rank_le_two C hrank h0 h1 (hq C hrank) (hS C hrank))
  rw [re_expectation_partialTranspose_tripleCopy_werner_three] at hneg
  have hprod := mul_nonneg hpos hE
  linarith

end ThreeCopyQutritWerner

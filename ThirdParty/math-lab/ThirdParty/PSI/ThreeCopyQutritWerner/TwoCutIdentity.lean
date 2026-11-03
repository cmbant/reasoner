module

public import ThreeCopyQutritWerner.TwoCutDefs

@[expose] public section


/-!
# The two-factor cut form on a sum of two rank-one operators

The algebraic identity behind manuscript eq. (29) (Appendix A).  For
`X = |x₁⟩⟨y₁| + |x₂⟩⟨y₂|` on `L ⊗ R` with `‖x₁‖² = ‖y₁‖² = d₁`, `‖x₂‖² = ‖y₂‖² = d₂`,
`⟨x₁, x₂⟩ = ⟨y₁, y₂⟩ = g` and `⟨y₁, x₁⟩ = ⟨y₂, x₂⟩ = τ`, the grouped two-factor form
`cutForm X` equals

`(d₁ - d₂)² / 2 + |g|² + (e(x₁, y₁) + e(x₂, y₂) + e(x₂, x₁) + e(y₂, y₁) + ‖P(x₂ x₁† - y₂ y₁†)‖²) / 2`

(`cutForm_ketBra_add`), where `e = biDefect` and `P(X) = (Tr_L X, Tr_R X)`.

The supporting lemmas are the polarization identities for `frobSq` and `ptraceNormSq`,
the Hilbert–Schmidt inner product and trace of rank-one operators, and the cross identity
`⟨P(x₁ y₁†), P(x₂ y₂†)⟩ = ⟨P(y₂ y₁†), P(x₂ x₁†)⟩` (`ptraceInner_ketBra_cross`), which pairs
each traced subsystem with its complement.
-/

noncomputable section

namespace ThreeCopyQutritWerner

section Helpers

theorem normSq_add_conj_mul (a b : ℂ) :
    Complex.normSq (a + b) =
      Complex.normSq a + Complex.normSq b + 2 * ((starRingEnd ℂ) a * b).re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem normSq_sub_conj_mul (a b : ℂ) :
    Complex.normSq (a - b) =
      Complex.normSq a + Complex.normSq b - 2 * ((starRingEnd ℂ) a * b).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem conj_mul_re_comm (a b : ℂ) :
    ((starRingEnd ℂ) a * b).re = ((starRingEnd ℂ) b * a).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem normSq_add_self (z : ℂ) : Complex.normSq (z + z) = 4 * Complex.normSq z := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem conj_sum_mul_sum {X Y : Type*} [Fintype X] [Fintype Y] (a : X → ℂ) (b : Y → ℂ) :
    (starRingEnd ℂ) (∑ x, a x) * (∑ y, b y) = ∑ x, ∑ y, (starRingEnd ℂ) (a x) * b y := by
  rw [map_sum, Finset.sum_mul_sum]

/-- Reverse both index pairs and exchange them in a four-fold sum. -/
theorem sum_swap_22 {X P : Type*} [Fintype X] [Fintype P] (F : X → X → P → P → ℂ) :
    ∑ x, ∑ y, ∑ p, ∑ q, F x y p q = ∑ q, ∑ p, ∑ y, ∑ x, F x y p q := by
  calc ∑ x, ∑ y, ∑ p, ∑ q, F x y p q
      = ∑ y, ∑ x, ∑ p, ∑ q, F x y p q := Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ q, ∑ p, F x y p q :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ y, ∑ q, ∑ x, ∑ p, F x y p q := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ q, ∑ y, ∑ x, ∑ p, F x y p q := Finset.sum_comm
    _ = ∑ q, ∑ y, ∑ p, ∑ x, F x y p q :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ y, ∑ x, F x y p q := Finset.sum_congr rfl fun q _ => Finset.sum_comm

end Helpers

section HilbertSchmidt

variable {m n : Type*} [Fintype m] [Fintype n]

theorem hsInner_re (A B : Matrix m n ℂ) :
    (hsInner A B).re = ∑ i, ∑ j, ((starRingEnd ℂ) (A i j) * B i j).re := by
  unfold hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]

/-- `Re ⟨A, B⟩ = Re ⟨B, A⟩`. -/
theorem hsInner_re_comm (A B : Matrix m n ℂ) : (hsInner A B).re = (hsInner B A).re := by
  rw [hsInner_re, hsInner_re]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    conj_mul_re_comm (A i j) (B i j)

/-- Polarization: `‖A + B‖_F² = ‖A‖_F² + ‖B‖_F² + 2 Re ⟨A, B⟩`. -/
theorem frobSq_add (A B : Matrix m n ℂ) :
    frobSq (A + B) = frobSq A + frobSq B + 2 * (hsInner A B).re := by
  rw [hsInner_re]
  unfold frobSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => normSq_add_conj_mul (A i j) (B i j)

/-- Polarization: `‖A - B‖_F² = ‖A‖_F² + ‖B‖_F² - 2 Re ⟨A, B⟩`. -/
theorem frobSq_sub (A B : Matrix m n ℂ) :
    frobSq (A - B) = frobSq A + frobSq B - 2 * (hsInner A B).re := by
  rw [hsInner_re]
  unfold frobSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => normSq_sub_conj_mul (A i j) (B i j)

end HilbertSchmidt

section KetBra

variable {ι : Type*} [Fintype ι]

/-- `⟨u v†, u' v'†⟩ = ⟨u, u'⟩ · conj ⟨v, v'⟩`. -/
theorem hsInner_ketBra (u v u' v' : ι → ℂ) :
    hsInner (ketBra u v) (ketBra u' v') = braket u u' * (starRingEnd ℂ) (braket v v') := by
  show (∑ i : ι, ∑ j : ι,
      (starRingEnd ℂ) (u i * (starRingEnd ℂ) (v j)) * (u' i * (starRingEnd ℂ) (v' j))) =
    (∑ i : ι, (starRingEnd ℂ) (u i) * u' i) *
      (starRingEnd ℂ) (∑ j : ι, (starRingEnd ℂ) (v j) * v' j)
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- `Tr (u v†) = ⟨v, u⟩`. -/
theorem trace_ketBra (u v : ι → ℂ) : (ketBra u v).trace = braket v u := by
  show (∑ i : ι, u i * (starRingEnd ℂ) (v i)) = ∑ i : ι, (starRingEnd ℂ) (v i) * u i
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `‖u v†‖_F² = ‖u‖² ‖v‖²`. -/
theorem frobSq_ketBra_vecNormSq (u v : ι → ℂ) :
    frobSq (ketBra u v) = vecNormSq u * vecNormSq v := by
  unfold vecNormSq
  exact frobSq_ketBra u v

end KetBra

section TwoSite

variable {L R : Type*} [Fintype L] [Fintype R]

theorem ptraceL_add (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceL (A + B) = ptraceL A + ptraceL B := by
  ext k k'
  show (∑ j : L, (A + B) (j, k) (j, k')) =
    (∑ j : L, A (j, k) (j, k')) + ∑ j : L, B (j, k) (j, k')
  rw [← Finset.sum_add_distrib]
  first | done | exact Finset.sum_congr rfl fun j _ => rfl

theorem ptraceR_add (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceR (A + B) = ptraceR A + ptraceR B := by
  ext j j'
  show (∑ k : R, (A + B) (j, k) (j', k)) =
    (∑ k : R, A (j, k) (j', k)) + ∑ k : R, B (j, k) (j', k)
  rw [← Finset.sum_add_distrib]
  first | done | exact Finset.sum_congr rfl fun k _ => rfl

theorem ptraceL_sub (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceL (A - B) = ptraceL A - ptraceL B := by
  ext k k'
  show (∑ j : L, (A - B) (j, k) (j, k')) =
    (∑ j : L, A (j, k) (j, k')) - ∑ j : L, B (j, k) (j, k')
  rw [← Finset.sum_sub_distrib]
  first | done | exact Finset.sum_congr rfl fun j _ => rfl

theorem ptraceR_sub (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceR (A - B) = ptraceR A - ptraceR B := by
  ext j j'
  show (∑ k : R, (A - B) (j, k) (j', k)) =
    (∑ k : R, A (j, k) (j', k)) - ∑ k : R, B (j, k) (j', k)
  rw [← Finset.sum_sub_distrib]
  first | done | exact Finset.sum_congr rfl fun k _ => rfl

/-- `Re ⟨P(A), P(B)⟩ = Re ⟨P(B), P(A)⟩`. -/
theorem ptraceInner_re_comm (A B : Matrix (L × R) (L × R) ℂ) :
    (ptraceInner A B).re = (ptraceInner B A).re := by
  unfold ptraceInner
  rw [Complex.add_re, Complex.add_re, hsInner_re_comm (ptraceL A) (ptraceL B),
    hsInner_re_comm (ptraceR A) (ptraceR B)]

/-- Polarization: `‖P(A + B)‖² = ‖P(A)‖² + ‖P(B)‖² + 2 Re ⟨P(A), P(B)⟩`. -/
theorem ptraceNormSq_add (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceNormSq (A + B) = ptraceNormSq A + ptraceNormSq B + 2 * (ptraceInner A B).re := by
  unfold ptraceNormSq ptraceInner
  rw [ptraceL_add, ptraceR_add, frobSq_add, frobSq_add, Complex.add_re]
  ring

/-- Polarization: `‖P(A - B)‖² = ‖P(A)‖² + ‖P(B)‖² - 2 Re ⟨P(A), P(B)⟩`. -/
theorem ptraceNormSq_sub (A B : Matrix (L × R) (L × R) ℂ) :
    ptraceNormSq (A - B) = ptraceNormSq A + ptraceNormSq B - 2 * (ptraceInner A B).re := by
  unfold ptraceNormSq ptraceInner
  rw [ptraceL_sub, ptraceR_sub, frobSq_sub, frobSq_sub, Complex.add_re]
  ring

/-- `⟨Tr_L (x₁ y₁†), Tr_L (x₂ y₂†)⟩` as a four-fold sum. -/
theorem hsInner_ptraceL_ketBra (x₁ y₁ x₂ y₂ : L × R → ℂ) :
    hsInner (ptraceL (ketBra x₁ y₁)) (ptraceL (ketBra x₂ y₂)) =
      ∑ r : R, ∑ r' : R, ∑ l : L, ∑ l' : L,
        (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l, r') * x₂ (l', r) * (starRingEnd ℂ) (y₂ (l', r')) := by
  show (∑ r : R, ∑ r' : R,
      (starRingEnd ℂ) (∑ l : L, x₁ (l, r) * (starRingEnd ℂ) (y₁ (l, r'))) *
        (∑ l' : L, x₂ (l', r) * (starRingEnd ℂ) (y₂ (l', r')))) =
    ∑ r : R, ∑ r' : R, ∑ l : L, ∑ l' : L,
      (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l, r') * x₂ (l', r) * (starRingEnd ℂ) (y₂ (l', r'))
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  rw [conj_sum_mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- `⟨Tr_R (x₁ y₁†), Tr_R (x₂ y₂†)⟩` as a four-fold sum. -/
theorem hsInner_ptraceR_ketBra (x₁ y₁ x₂ y₂ : L × R → ℂ) :
    hsInner (ptraceR (ketBra x₁ y₁)) (ptraceR (ketBra x₂ y₂)) =
      ∑ l : L, ∑ l' : L, ∑ r : R, ∑ r' : R,
        (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l', r) * x₂ (l, r') * (starRingEnd ℂ) (y₂ (l', r')) := by
  show (∑ l : L, ∑ l' : L,
      (starRingEnd ℂ) (∑ r : R, x₁ (l, r) * (starRingEnd ℂ) (y₁ (l', r))) *
        (∑ r' : R, x₂ (l, r') * (starRingEnd ℂ) (y₂ (l', r')))) =
    ∑ l : L, ∑ l' : L, ∑ r : R, ∑ r' : R,
      (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l', r) * x₂ (l, r') * (starRingEnd ℂ) (y₂ (l', r'))
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [conj_sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- Cross identity, first half: the `Tr_L` pairing of `(x₁ y₁†, x₂ y₂†)` is the `Tr_R`
pairing of `(y₂ y₁†, x₂ x₁†)`. -/
theorem hsInner_ptraceL_ketBra_cross (x₁ y₁ x₂ y₂ : L × R → ℂ) :
    hsInner (ptraceL (ketBra x₁ y₁)) (ptraceL (ketBra x₂ y₂)) =
      hsInner (ptraceR (ketBra y₂ y₁)) (ptraceR (ketBra x₂ x₁)) := by
  rw [hsInner_ptraceL_ketBra, hsInner_ptraceR_ketBra]
  refine (sum_swap_22 (fun (r r' : R) (l l' : L) =>
    (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l, r') * x₂ (l', r) *
      (starRingEnd ℂ) (y₂ (l', r')))).trans ?_
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  show (starRingEnd ℂ) (x₁ (p, x)) * y₁ (p, y) * x₂ (q, x) * (starRingEnd ℂ) (y₂ (q, y)) =
    (starRingEnd ℂ) (y₂ (q, y)) * y₁ (p, y) * x₂ (q, x) * (starRingEnd ℂ) (x₁ (p, x))
  ring

/-- Cross identity, second half: the `Tr_R` pairing of `(x₁ y₁†, x₂ y₂†)` is the `Tr_L`
pairing of `(y₂ y₁†, x₂ x₁†)`. -/
theorem hsInner_ptraceR_ketBra_cross (x₁ y₁ x₂ y₂ : L × R → ℂ) :
    hsInner (ptraceR (ketBra x₁ y₁)) (ptraceR (ketBra x₂ y₂)) =
      hsInner (ptraceL (ketBra y₂ y₁)) (ptraceL (ketBra x₂ x₁)) := by
  rw [hsInner_ptraceR_ketBra, hsInner_ptraceL_ketBra]
  refine (sum_swap_22 (fun (l l' : L) (r r' : R) =>
    (starRingEnd ℂ) (x₁ (l, r)) * y₁ (l', r) * x₂ (l, r') *
      (starRingEnd ℂ) (y₂ (l', r')))).trans ?_
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  show (starRingEnd ℂ) (x₁ (x, p)) * y₁ (y, p) * x₂ (x, q) * (starRingEnd ℂ) (y₂ (y, q)) =
    (starRingEnd ℂ) (y₂ (y, q)) * y₁ (y, p) * x₂ (x, q) * (starRingEnd ℂ) (x₁ (x, p))
  ring

/-- Cross identity of Appendix A: `⟨P(x₁ y₁†), P(x₂ y₂†)⟩ = ⟨P(y₂ y₁†), P(x₂ x₁†)⟩`; the two
summands of `ptraceInner` are exchanged. -/
theorem ptraceInner_ketBra_cross (x₁ y₁ x₂ y₂ : L × R → ℂ) :
    ptraceInner (ketBra x₁ y₁) (ketBra x₂ y₂) = ptraceInner (ketBra y₂ y₁) (ketBra x₂ x₁) := by
  unfold ptraceInner
  rw [hsInner_ptraceL_ketBra_cross x₁ y₁ x₂ y₂, hsInner_ptraceR_ketBra_cross x₁ y₁ x₂ y₂]
  exact add_comm _ _

/-- The algebraic identity behind manuscript eq. (29): the two-factor cut form on a sum of
two rank-one operators with matched norms, overlaps and traces. -/
theorem cutForm_ketBra_add (x₁ x₂ y₁ y₂ : L × R → ℂ) (d₁ d₂ : ℝ) (g τ : ℂ)
    (hx1 : vecNormSq x₁ = d₁) (hy1 : vecNormSq y₁ = d₁)
    (hx2 : vecNormSq x₂ = d₂) (hy2 : vecNormSq y₂ = d₂)
    (hxg : braket x₁ x₂ = g) (hyg : braket y₁ y₂ = g)
    (hτ1 : braket y₁ x₁ = τ) (hτ2 : braket y₂ x₂ = τ) :
    cutForm (ketBra x₁ y₁ + ketBra x₂ y₂) =
      (d₁ - d₂) ^ 2 / 2 + Complex.normSq g +
        (biDefect x₁ y₁ + biDefect x₂ y₂ + biDefect x₂ x₁ + biDefect y₂ y₁ +
          ptraceNormSq (ketBra x₂ x₁ - ketBra y₂ y₁)) / 2 := by
  have hcut : cutForm (ketBra x₁ y₁ + ketBra x₂ y₂) =
      frobSq (ketBra x₁ y₁ + ketBra x₂ y₂) -
        ptraceNormSq (ketBra x₁ y₁ + ketBra x₂ y₂) / 2 +
        Complex.normSq (ketBra x₁ y₁ + ketBra x₂ y₂).trace / 4 := rfl
  have hF : frobSq (ketBra x₁ y₁ + ketBra x₂ y₂) =
      d₁ * d₁ + d₂ * d₂ + 2 * Complex.normSq g := by
    rw [frobSq_add, frobSq_ketBra_vecNormSq, frobSq_ketBra_vecNormSq, hsInner_ketBra,
      hx1, hy1, hx2, hy2, hxg, hyg, Complex.mul_conj, Complex.ofReal_re]
  have hT : Complex.normSq (ketBra x₁ y₁ + ketBra x₂ y₂).trace = 4 * Complex.normSq τ := by
    rw [Matrix.trace_add, trace_ketBra, trace_ketBra, hτ1, hτ2, normSq_add_self]
  have hP := ptraceNormSq_add (ketBra x₁ y₁) (ketBra x₂ y₂)
  have hS := ptraceNormSq_sub (ketBra x₂ x₁) (ketBra y₂ y₁)
  have hc : (ptraceInner (ketBra x₂ x₁) (ketBra y₂ y₁)).re =
      (ptraceInner (ketBra x₁ y₁) (ketBra x₂ y₂)).re := by
    rw [ptraceInner_ketBra_cross x₁ y₁ x₂ y₂]
    exact ptraceInner_re_comm _ _
  have e1 : biDefect x₁ y₁ =
      d₁ * d₁ + Complex.normSq τ - ptraceNormSq (ketBra x₁ y₁) := by
    unfold biDefect
    rw [hx1, hy1, hτ1]
  have e2 : biDefect x₂ y₂ =
      d₂ * d₂ + Complex.normSq τ - ptraceNormSq (ketBra x₂ y₂) := by
    unfold biDefect
    rw [hx2, hy2, hτ2]
  have e3 : biDefect x₂ x₁ =
      d₂ * d₁ + Complex.normSq g - ptraceNormSq (ketBra x₂ x₁) := by
    unfold biDefect
    rw [hx2, hx1, hxg]
  have e4 : biDefect y₂ y₁ =
      d₂ * d₁ + Complex.normSq g - ptraceNormSq (ketBra y₂ y₁) := by
    unfold biDefect
    rw [hy2, hy1, hyg]
  rw [hcut, hF, hT, hP, hS, hc, e1, e2, e3, e4]
  ring

end TwoSite

end ThreeCopyQutritWerner

end

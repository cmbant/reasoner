import FormalResearch.FourQubitEntropy.EnvelopeProduct

/-!
# Zeros of the sharp polarisation remainder at `τ = 0` (`lem:fqe-polarization-remainder-zeros`)

Paper: `sextic_identity.tex`, Lemma `lem:fqe-polarization-remainder-zeros` and the proof of
`thm:fqe-general-envelope` (equality at `τ = 0`). `H_zero_product`: a unit vector with
`ψᵀ ε^{⊗4} ψ = 0`, `F = (3/4) W₁` and `W₁ > 0` is a fully product state (`IsProduct`).

Route (the paper's, with the local frames made explicit):

* `sextic_identity_pairs`: the identity (S) with its pair sum `Σ_{i<j} ‖(R_i^{(i)} - R_j^{(j)}) ψ‖²` in
  coordinates (`pairReal`); equality `F = (3/4) W₁` forces `(R_i^{(i)} - R_j^{(j)}) ψ = 0`
  (`pairVec_zero_of_eq`).
* Local frames (`rhoSite_actOn_same`, `rhoSite_actOn_ne`, `rhoSite_localApply`, `exists_diag_unitary`):
  one local unitary per qubit makes every one-qubit marginal `R_i` diagonal, and the hypotheses are
  invariant (`sexticF_LUEquiv`, `blochSq_LUEquiv`, `normSq_spinFlip_LUEquiv`).
* `diag_gauge_product`: with diagonal marginals `p_i`, `(p_0(x_0) - p_j(x_j)) ψ_x = 0`; the weighted sums
  force all `|p_i(0) - p_i(1)|` equal, hence nonzero since `W₁ = Σ_i (p_i(0) - p_i(1))² > 0`; so the support
  of `ψ` is at most two complementary computational strings (`dich`), and `s = 0` leaves one
  (`product_of_support`): `ψ` is a basis state in the diagonal frame, hence a product state.
-/

open scoped ComplexConjugate Matrix Kronecker
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

open FormalResearch.FourQubitEntropy.PaperECritical

/-- `Σ_{i<j} ‖(R_i^{(i)} - R_j^{(j)}) ψ‖²`, in coordinates. -/
noncomputable def pairReal (ψ : Psi) : ℝ :=
  ∑ ij ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)),
    ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (pairVec ij.1 ij.2 ψ ψ.conj a b c d)

theorem pairNorm_eq (i j : Fin 4) (ψ : Psi) :
    pairNorm i j ψ ψ.conj =
      ((∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (pairVec i j ψ ψ.conj a b c d) : ℝ) : ℂ) := by
  simp only [pairNorm, sum4, sum2, toAdd_complex, pairVec_conj, Fin.sum_univ_two]
  push_cast
  simp only [Complex.mul_conj]

theorem pairSum_eq (ψ : Psi) : pairSum ψ ψ.conj = (pairReal ψ : ℂ) := by
  simp only [pairSum, toAdd_complex, pairNorm_eq, pairReal]
  rw [show ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)) =
    {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} from rfl]
  simp [Finset.sum_insert]
  ring


theorem pairReal_nonneg (ψ : Psi) : 0 ≤ pairReal ψ := by
  unfold pairReal
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The identity (S) with the pair sum written in coordinates. -/
theorem sextic_identity_pairs (ψ : Psi) :
    ∃ r : ℝ, 0 ≤ r ∧
      96 * sexticF ψ = 72 * (normSqPsi ψ * blochSq ψ) + r + 144 * pairReal ψ := by
  have hd := sexticDefect_zero ψ ψ.conj
  obtain ⟨r0, h0, e0⟩ := resNorm0_nonneg ψ
  obtain ⟨r1, h1, e1⟩ := resNorm0_nonneg (siteSwap 1 ψ)
  obtain ⟨r2, h2, e2⟩ := resNorm0_nonneg (siteSwap 2 ψ)
  obtain ⟨r3, h3, e3⟩ := resNorm0_nonneg (siteSwap 3 ψ)
  refine ⟨r0 + r1 + r2 + r3, by positivity, ?_⟩
  simp only [sexticDefect, defectG, siteSwap_conj, toAdd_complex, toMul_complex, toSub_complex,
    lit_complex] at hd
  rw [Fgen_eq, W1gen_eq, normG_eq, e0, e1, e2, e3, pairSum_eq] at hd
  have hr : (96 * sexticF ψ - 72 * (normSqPsi ψ * blochSq ψ) - (r0 + r1 + r2 + r3) - 144 * pairReal ψ : ℝ)
      = 0 := by
    exact_mod_cast hd
  linarith

/-- Equality `F = (3/4) W₁` for a unit vector forces `(R_i^{(i)} - R_j^{(j)}) ψ = 0` for every pair. -/
theorem pairVec_zero_of_eq (ψ : Psi) (hn : normSqPsi ψ = 1) (hF : sexticF ψ = 3 / 4 * blochSq ψ)
    (i j : Fin 4) (hij : (i, j) ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)))
    (a b c d : Fin 2) : pairVec i j ψ ψ.conj a b c d = 0 := by
  obtain ⟨r, hr, h⟩ := sextic_identity_pairs ψ
  rw [hn, hF] at h
  have hp := pairReal_nonneg ψ
  have hp0 : pairReal ψ = 0 := by linarith
  unfold pairReal at hp0
  have hnn : ∀ ij ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)),
      0 ≤ ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (pairVec ij.1 ij.2 ψ ψ.conj a b c d) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hp0 (i, j) hij
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => Complex.normSq_nonneg _)).1 h1 a
    (Finset.mem_univ a)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Finset.sum_nonneg fun c _ =>
    Finset.sum_nonneg fun d _ => Complex.normSq_nonneg _)).1 h2 b (Finset.mem_univ b)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Finset.sum_nonneg fun d _ =>
    Complex.normSq_nonneg _)).1 h3 c (Finset.mem_univ c)
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => Complex.normSq_nonneg _)).1 h4 d
    (Finset.mem_univ d)
  exact Complex.normSq_eq_zero.1 h5


section DiagGauge

variable (ψ : Psi) (hdiag : ∀ i, rhoSite i ψ 0 1 = 0)

omit hdiag in
theorem rhoSite_diag_real (i : Fin 4) (a : Fin 2) : ((rhoSite i ψ a a).re : ℂ) = rhoSite i ψ a a := by
  have := rhoSite_conj i ψ a a
  exact (Complex.conj_eq_iff_re.1 this)

include hdiag in
theorem rhoSite_diag_10 (i : Fin 4) : rhoSite i ψ 1 0 = 0 := by
  have := rhoSite_conj i ψ 0 1
  rw [hdiag i] at this
  simpa using this.symm

omit hdiag in
theorem actSite_eq (s : Fin 4) (a b c d : Fin 2) :
    actSite s ψ ψ.conj a b c d =
      match s with
      | 0 => rhoSite 0 ψ a 0 * ψ 0 b c d + rhoSite 0 ψ a 1 * ψ 1 b c d
      | 1 => rhoSite 1 ψ b 0 * ψ a 0 c d + rhoSite 1 ψ b 1 * ψ a 1 c d
      | 2 => rhoSite 2 ψ c 0 * ψ a b 0 d + rhoSite 2 ψ c 1 * ψ a b 1 d
      | 3 => rhoSite 3 ψ d 0 * ψ a b c 0 + rhoSite 3 ψ d 1 * ψ a b c 1 := by
  fin_cases s <;> simp [actSite, rhoSite, siteSwap_conj, sum2] <;> rfl

end DiagGauge


theorem diag_E (ψ : Psi) (hn : normSqPsi ψ = 1) (hF : sexticF ψ = 3 / 4 * blochSq ψ)
    (hdiag : ∀ i, rhoSite i ψ 0 1 = 0) (j : Fin 4) (hj : j ≠ 0) (a b c d : Fin 2) :
    (rhoSite 0 ψ a a - rhoSite j ψ (![a, b, c, d] j) (![a, b, c, d] j)) * ψ a b c d = 0 := by
  have h10 := rhoSite_diag_10 ψ hdiag
  have hj3 : j = 1 ∨ j = 2 ∨ j = 3 := by
    fin_cases j <;> simp at hj ⊢
  have hj' : (0, j) ∈ ({(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4)) := by
    rcases hj3 with rfl | rfl | rfl <;> simp
  have := pairVec_zero_of_eq ψ hn hF 0 j hj' a b c d
  simp only [pairVec, actSite_eq] at this
  rcases hj3 with rfl | rfl | rfl <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [hdiag 0, h10 0, hdiag 1, h10 1, hdiag 2, h10 2, hdiag 3, h10 3, zero_mul, add_zero,
      zero_add, mul_zero, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_three] at this ⊢ <;>
    linear_combination this


/-- The diagonal entry `p_i(a) = ⟨a|R_i|a⟩` is the weight of `a` at qubit `i`. -/
theorem rhoSite_diag_weight (ψ : Psi) (a : Fin 2) :
    (rhoSite 0 ψ a a = ((∑ b, ∑ c, ∑ d, Complex.normSq (ψ a b c d) : ℝ) : ℂ)) ∧
    (rhoSite 1 ψ a a = ((∑ x, ∑ c, ∑ d, Complex.normSq (ψ x a c d) : ℝ) : ℂ)) ∧
    (rhoSite 2 ψ a a = ((∑ x, ∑ b, ∑ d, Complex.normSq (ψ x b a d) : ℝ) : ℂ)) ∧
    (rhoSite 3 ψ a a = ((∑ x, ∑ b, ∑ c, Complex.normSq (ψ x b c a) : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [rhoSite, rho0, siteSwap, sum2, Psi.conj, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self]
    ring


/-- Bit strings of four qubits. -/
abbrev Str := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Complementary string. -/
def Str.flip (y : Str) : Str := (1 - y.1, 1 - y.2.1, 1 - y.2.2.1, 1 - y.2.2.2)

/-- amplitude of a string -/
def psiS (ψ : Psi) (y : Str) : ℂ := ψ y.1 y.2.1 y.2.2.1 y.2.2.2

theorem Fin2_one_sub (a : Fin 2) : 1 - (1 - a) = a := by fin_cases a <;> decide

theorem Str.flip_flip (y : Str) : y.flip.flip = y := by
  obtain ⟨a, b, c, d⟩ := y
  simp only [Str.flip]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [Fin2_one_sub]

theorem Str.flip_ne (y : Str) : y.flip ≠ y := by
  intro h
  have := congrArg Prod.fst h
  simp only [Str.flip] at this
  revert this
  fin_cases y <;> decide

theorem spinFlipForm_sum (ψ : Psi) :
    spinFlipForm ψ = ∑ y : Str, ((sgn y.1 * sgn y.2.1 * sgn y.2.2.1 * sgn y.2.2.2 : ℤ) : ℂ) *
      (psiS ψ y * psiS ψ y.flip) := by
  simp only [spinFlipForm, sum4, sum2, toAdd_complex, toMul_complex, lit_complex, Fintype.sum_prod_type,
    Fin.sum_univ_two, psiS, Str.flip]


theorem sgn_flip (a : Fin 2) : sgn (1 - a) = -sgn a := by
  fin_cases a <;> simp [sgn]

theorem isProduct_of_single (ψ : Psi) (x : Str) (h : ∀ y, y ≠ x → psiS ψ y = 0) : IsProduct ψ := by
  refine ⟨fun a => if a = x.1 then psiS ψ x else 0, fun b => if b = x.2.1 then 1 else 0,
    fun c => if c = x.2.2.1 then 1 else 0, fun d => if d = x.2.2.2 then 1 else 0, ?_⟩
  intro a b c d
  by_cases hx : a = x.1 ∧ b = x.2.1 ∧ c = x.2.2.1 ∧ d = x.2.2.2
  · obtain ⟨h1, h2, h3, h4⟩ := hx
    have : ψ a b c d = psiS ψ x := by subst h1 h2 h3 h4; rfl
    simp [this, h1, h2, h3, h4]
    rfl
  · have hne : ((a, b, c, d) : Str) ≠ x := by
      intro hh
      apply hx
      obtain ⟨x1, x2, x3, x4⟩ := x
      simp only [Prod.mk.injEq] at hh
      exact hh
    have := h _ hne
    simp only [psiS] at this
    rw [this]
    by_cases h1 : a = x.1
    · by_cases h2 : b = x.2.1
      · by_cases h3 : c = x.2.2.1
        · have h4 : d ≠ x.2.2.2 := fun h4 => hx ⟨h1, h2, h3, h4⟩
          simp [h4]
        · simp [h3]
      · simp [h2]
    · simp [h1]

theorem product_of_support (ψ : Psi) (hn : normSqPsi ψ = 1) (hτ : spinFlipForm ψ = 0)
    (hA : ∀ y z : Str, psiS ψ y ≠ 0 → psiS ψ z ≠ 0 → z = y ∨ z = y.flip) : IsProduct ψ := by
  -- a string in the support
  obtain ⟨x, hx⟩ : ∃ x : Str, psiS ψ x ≠ 0 := by
    by_contra hcon0
    have hcon : ∀ x : Str, psiS ψ x = 0 := fun x => by
      by_contra h; exact hcon0 ⟨x, h⟩
    have : normSqPsi ψ = 0 := by
      simp only [normSqPsi, Fin.sum_univ_two]
      have h0 : ∀ a b c d : Fin 2, ψ a b c d = 0 := fun a b c d => hcon (a, b, c, d)
      simp [h0]
    linarith
  have hzero : ∀ y : Str, y ≠ x → y ≠ x.flip → psiS ψ y = 0 := by
    intro y h1 h2
    by_contra hy
    rcases hA x y hx hy with h | h
    · exact h1 h
    · exact h2 h
  have hs := spinFlipForm_sum ψ
  rw [hτ] at hs
  have hsum : ∑ y : Str, ((sgn y.1 * sgn y.2.1 * sgn y.2.2.1 * sgn y.2.2.2 : ℤ) : ℂ) *
      (psiS ψ y * psiS ψ y.flip) =
      ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) * (psiS ψ x * psiS ψ x.flip) +
      ((sgn x.flip.1 * sgn x.flip.2.1 * sgn x.flip.2.2.1 * sgn x.flip.2.2.2 : ℤ) : ℂ) *
        (psiS ψ x.flip * psiS ψ x.flip.flip) := by
    refine Finset.sum_eq_add x x.flip (Str.flip_ne x).symm ?_ (by simp) (by simp)
    intro y _ ⟨h1, h2⟩
    rw [hzero y h1 h2]; simp
  rw [hsum, Str.flip_flip] at hs
  have hsg : ((sgn x.flip.1 * sgn x.flip.2.1 * sgn x.flip.2.2.1 * sgn x.flip.2.2.2 : ℤ) : ℂ) =
      ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) := by
    simp only [Str.flip, sgn_flip]
    push_cast; ring
  rw [hsg] at hs
  have hc : ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) ≠ 0 := by
    have : ∀ a : Fin 2, sgn a = 1 ∨ sgn a = -1 := fun a => by fin_cases a <;> simp [sgn]
    rcases this x.1 with h1 | h1 <;> rcases this x.2.1 with h2 | h2 <;>
      rcases this x.2.2.1 with h3 | h3 <;> rcases this x.2.2.2 with h4 | h4 <;> simp [h1, h2, h3, h4]
  have hxx : psiS ψ x * psiS ψ x.flip = 0 := by
    have : ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) *
        (psiS ψ x * psiS ψ x.flip) = 0 := by
      have h2 : ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) *
          (psiS ψ x * psiS ψ x.flip) + ((sgn x.1 * sgn x.2.1 * sgn x.2.2.1 * sgn x.2.2.2 : ℤ) : ℂ) *
          (psiS ψ x.flip * psiS ψ x) = 0 := hs.symm
      linear_combination (1 / 2 : ℂ) * h2
    exact (mul_eq_zero.1 this).resolve_left hc
  have hflip : psiS ψ x.flip = 0 := (mul_eq_zero.1 hxx).resolve_left hx
  refine isProduct_of_single ψ x fun y hy => ?_
  by_contra hyne
  rcases hA x y hx hyne with h | h
  · exact hy h
  · rw [h] at hyne; exact hyne hflip


theorem dich (p : Fin 4 → Fin 2 → ℝ) (hsum : ∀ i, p i 0 + p i 1 = 1) (hne : ∀ i, p i 0 ≠ p i 1)
    (y z : Str)
    (hy : p 1 y.2.1 = p 0 y.1 ∧ p 2 y.2.2.1 = p 0 y.1 ∧ p 3 y.2.2.2 = p 0 y.1)
    (hz : p 1 z.2.1 = p 0 z.1 ∧ p 2 z.2.2.1 = p 0 z.1 ∧ p 3 z.2.2.2 = p 0 z.1) :
    z = y ∨ z = y.flip := by
  have inj : ∀ i (a b : Fin 2), p i a = p i b → a = b := by
    intro i a b h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (hne i) | exact absurd h.symm (hne i)
  have flp : ∀ i (a : Fin 2), p i (1 - a) = 1 - p i a := by
    intro i a
    fin_cases a
    · have := hsum i; simp; linarith
    · have := hsum i; simp; linarith
  obtain ⟨y0, y1, y2, y3⟩ := y
  obtain ⟨z0, z1, z2, z3⟩ := z
  simp only at hy hz
  by_cases h0 : p 0 z0 = p 0 y0
  · left
    have e0 : z0 = y0 := inj 0 _ _ h0
    have e1 : z1 = y1 := inj 1 _ _ (by rw [hz.1, hy.1, h0])
    have e2 : z2 = y2 := inj 2 _ _ (by rw [hz.2.1, hy.2.1, h0])
    have e3 : z3 = y3 := inj 3 _ _ (by rw [hz.2.2, hy.2.2, h0])
    rw [e0, e1, e2, e3]
  · right
    have e0 : z0 = 1 - y0 := by
      by_cases h : z0 = y0
      · exact absurd (by rw [h]) h0
      · have key : ∀ a b : Fin 2, a ≠ b → a = 1 - b := by decide
        exact key _ _ h
    have hq : p 0 z0 = 1 - p 0 y0 := by rw [e0]; exact flp 0 y0
    have e1 : z1 = 1 - y1 := inj 1 _ _ (by rw [flp, hz.1, hy.1, hq])
    have e2 : z2 = 1 - y2 := inj 2 _ _ (by rw [flp, hz.2.1, hy.2.1, hq])
    have e3 : z3 = 1 - y3 := inj 3 _ _ (by rw [flp, hz.2.2, hy.2.2, hq])
    simp only [Str.flip]
    rw [e0, e1, e2, e3]


theorem bloch_diag (ψ : Psi) (hdiag : ∀ i, rhoSite i ψ 0 1 = 0) (p : Fin 4 → Fin 2 → ℝ)
    (hR : ∀ i a, rhoSite i ψ a a = (p i a : ℂ)) :
    blochSq ψ = ∑ i : Fin 4, (p i 0 - p i 1) ^ 2 := by
  have h10 := rhoSite_diag_10 ψ hdiag
  unfold blochSq
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [expectation_eq, Fin.sum_univ_two, pauliX, pauliY, pauliZ, hdiag i, h10 i, hR i]
  ring


set_option maxHeartbeats 1000000 in
theorem diag_gauge_product (ψ : Psi) (hn : normSqPsi ψ = 1) (hτ : spinFlipForm ψ = 0)
    (hF : sexticF ψ = 3 / 4 * blochSq ψ) (hW : 0 < blochSq ψ)
    (hdiag : ∀ i, rhoSite i ψ 0 1 = 0) : IsProduct ψ := by
  have h10 := rhoSite_diag_10 ψ hdiag
  set p : Fin 4 → Fin 2 → ℝ := fun i a => (rhoSite i ψ a a).re with hp
  have hR : ∀ i a, rhoSite i ψ a a = (p i a : ℂ) := fun i a => (rhoSite_diag_real ψ i a).symm
  have hpsum : ∀ i, p i 0 + p i 1 = 1 := by
    intro i
    have h := normG_rho i ψ
    rw [normG_eq, hn, hR i 0, hR i 1] at h
    exact_mod_cast h.symm
  have hw0 : ∀ a, p 0 a = ∑ b, ∑ c, ∑ d, Complex.normSq (ψ a b c d) := fun a => by
    have := (rhoSite_diag_weight ψ a).1; rw [hR] at this; exact_mod_cast this
  have hw1 : ∀ a, p 1 a = ∑ x, ∑ c, ∑ d, Complex.normSq (ψ x a c d) := fun a => by
    have := (rhoSite_diag_weight ψ a).2.1; rw [hR] at this; exact_mod_cast this
  have hw2 : ∀ a, p 2 a = ∑ x, ∑ b, ∑ d, Complex.normSq (ψ x b a d) := fun a => by
    have := (rhoSite_diag_weight ψ a).2.2.1; rw [hR] at this; exact_mod_cast this
  have hw3 : ∀ a, p 3 a = ∑ x, ∑ b, ∑ c, Complex.normSq (ψ x b c a) := fun a => by
    have := (rhoSite_diag_weight ψ a).2.2.2; rw [hR] at this; exact_mod_cast this
  have hE : ∀ j : Fin 4, j ≠ 0 → ∀ a b c d : Fin 2,
      (p 0 a - p j (![a, b, c, d] j)) * Complex.normSq (ψ a b c d) = 0 := by
    intro j hj a b c d
    have := diag_E ψ hn hF hdiag j hj a b c d
    rw [hR, hR] at this
    rcases mul_eq_zero.1 this with h | h
    · have h' : p 0 a - p j (![a, b, c, d] j) = 0 := by exact_mod_cast h
      rw [h', zero_mul]
    · rw [h]; simp
  have hE1 : ∀ a b c d, (p 0 a - p 1 b) * Complex.normSq (ψ a b c d) = 0 := fun a b c d => by
    simpa using hE 1 (by decide) a b c d
  have hE2 : ∀ a b c d, (p 0 a - p 2 c) * Complex.normSq (ψ a b c d) = 0 := fun a b c d => by
    simpa using hE 2 (by decide) a b c d
  have hE3 : ∀ a b c d, (p 0 a - p 3 d) * Complex.normSq (ψ a b c d) = 0 := fun a b c d => by
    simpa using hE 3 (by decide) a b c d
  -- weighted sums
  have hT0 : ∑ a, ∑ b, ∑ c, ∑ d, p 0 a * Complex.normSq (ψ a b c d) = p 0 0 ^ 2 + p 0 1 ^ 2 := by
    have h0 := hw0 0; have h1 := hw0 1
    simp only [Fin.sum_univ_two] at h0 h1 ⊢
    linear_combination (-(p 0 0)) * h0 + (-(p 0 1)) * h1
  have hT1 : ∑ a, ∑ b, ∑ c, ∑ d, p 1 b * Complex.normSq (ψ a b c d) = p 1 0 ^ 2 + p 1 1 ^ 2 := by
    have h0 := hw1 0; have h1 := hw1 1
    simp only [Fin.sum_univ_two] at h0 h1 ⊢
    linear_combination (-(p 1 0)) * h0 + (-(p 1 1)) * h1
  have hT2 : ∑ a, ∑ b, ∑ c, ∑ d, p 2 c * Complex.normSq (ψ a b c d) = p 2 0 ^ 2 + p 2 1 ^ 2 := by
    have h0 := hw2 0; have h1 := hw2 1
    simp only [Fin.sum_univ_two] at h0 h1 ⊢
    linear_combination (-(p 2 0)) * h0 + (-(p 2 1)) * h1
  have hT3 : ∑ a, ∑ b, ∑ c, ∑ d, p 3 d * Complex.normSq (ψ a b c d) = p 3 0 ^ 2 + p 3 1 ^ 2 := by
    have h0 := hw3 0; have h1 := hw3 1
    simp only [Fin.sum_univ_two] at h0 h1 ⊢
    linear_combination (-(p 3 0)) * h0 + (-(p 3 1)) * h1
  have hS1 : p 0 0 ^ 2 + p 0 1 ^ 2 = p 1 0 ^ 2 + p 1 1 ^ 2 := by
    rw [← hT0, ← hT1]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    have := hE1 a b c d; linarith
  have hS2 : p 0 0 ^ 2 + p 0 1 ^ 2 = p 2 0 ^ 2 + p 2 1 ^ 2 := by
    rw [← hT0, ← hT2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    have := hE2 a b c d; linarith
  have hS3 : p 0 0 ^ 2 + p 0 1 ^ 2 = p 3 0 ^ 2 + p 3 1 ^ 2 := by
    rw [← hT0, ← hT3]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    have := hE3 a b c d; linarith
  have hz1 : (p 1 0 - p 1 1) ^ 2 = (p 0 0 - p 0 1) ^ 2 := by
    nlinarith [hS1, hpsum 1, hpsum 0]
  have hz2 : (p 2 0 - p 2 1) ^ 2 = (p 0 0 - p 0 1) ^ 2 := by
    nlinarith [hS2, hpsum 2, hpsum 0]
  have hz3 : (p 3 0 - p 3 1) ^ 2 = (p 0 0 - p 0 1) ^ 2 := by
    nlinarith [hS3, hpsum 3, hpsum 0]
  have hz : ∀ i, (p i 0 - p i 1) ^ 2 = (p 0 0 - p 0 1) ^ 2 := by
    intro i
    fin_cases i
    · rfl
    · exact hz1
    · exact hz2
    · exact hz3
  have hbl := bloch_diag ψ hdiag p hR
  have hζ : 0 < (p 0 0 - p 0 1) ^ 2 := by
    rw [hbl, Fin.sum_univ_four, hz1, hz2, hz3] at hW
    linarith
  have hne : ∀ i, p i 0 ≠ p i 1 := by
    intro i h
    have h0 : (0 : ℝ) ^ 2 = (p 0 0 - p 0 1) ^ 2 := by
      have := hz i
      rwa [h, sub_self] at this
    rw [← h0] at hζ
    norm_num at hζ
  refine product_of_support ψ hn hτ ?_
  intro y z hy hz'
  have hsupp : ∀ w : Str, psiS ψ w ≠ 0 →
      (p 1 w.2.1 = p 0 w.1 ∧ p 2 w.2.2.1 = p 0 w.1 ∧ p 3 w.2.2.2 = p 0 w.1) := by
    intro w hw
    have hq : Complex.normSq (ψ w.1 w.2.1 w.2.2.1 w.2.2.2) ≠ 0 := by
      intro h; exact hw (Complex.normSq_eq_zero.1 h)
    refine ⟨?_, ?_, ?_⟩
    · have := (mul_eq_zero.1 (hE1 w.1 w.2.1 w.2.2.1 w.2.2.2)).resolve_right hq; linarith
    · have := (mul_eq_zero.1 (hE2 w.1 w.2.1 w.2.2.1 w.2.2.2)).resolve_right hq; linarith
    · have := (mul_eq_zero.1 (hE3 w.1 w.2.1 w.2.2.1 w.2.2.2)).resolve_right hq; linarith
  exact dich p hpsum hne y z (hsupp y hy) (hsupp z hz')




theorem rhoSite_actOn_same (i : Fin 4) (u : Op1) (ψ : Psi) (a a' : Fin 2) :
    rhoSite i (actOn i u ψ) a a' = ∑ p, ∑ p', u a p * rhoSite i ψ p p' * conj (u a' p') := by
  fin_cases i <;>
  simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two] <;> ring

theorem rhoSite_actOn_ne (i j : Fin 4) (hij : i ≠ j) (u : Op1) (hu : uᴴ * u = 1) (ψ : Psi)
    (a a' : Fin 2) : rhoSite j (actOn i u ψ) a a' = rhoSite j ψ a a' := by
  have h00 := congrFun (congrFun hu 0) 0
  have h01 := congrFun (congrFun hu 0) 1
  have h10 := congrFun (congrFun hu 1) 0
  have h11 := congrFun (congrFun hu 1) 1
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 1 1)) * h00 + (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 0 1) + ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 1 0) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h10 + (ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 1 1)) * h01 + (ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 0 1) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 1 0) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 1)) * h00 + (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 1) + ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 0) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h10 + (ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 1)) * h01 + (ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 1) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 0) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 0 0 1 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 0 1 0 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 0 1 1 a')) * h00 + (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 0 0 1 a * (starRingEnd ℂ) (ψ 1 0 1 a') + ψ 0 1 0 a * (starRingEnd ℂ) (ψ 1 1 0 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h10 + (ψ 1 0 0 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 0 1 1 a')) * h01 + (ψ 1 0 0 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 1 0 1 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 1 1 0 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 0 1 1)) * h00 + (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 1 0 1) + ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 1 1 0) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h10 + (ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 0 1 1)) * h01 + (ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 1 0 1) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 1 1 0) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 1)) * h00 + (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 1) + ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 0) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h10 + (ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 1)) * h01 + (ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 1) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 0) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 0 0 1 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 1 0 0 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 1 0 1 a')) * h00 + (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 0 0 1 a * (starRingEnd ℂ) (ψ 0 1 1 a') + ψ 1 0 0 a * (starRingEnd ℂ) (ψ 1 1 0 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h10 + (ψ 0 1 0 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 1 0 1 a')) * h01 + (ψ 0 1 0 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 0 1 1 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 1 1 0 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 1 0 1)) * h00 + (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 0 1 1) + ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 1 1 0) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h10 + (ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 1 0 1)) * h01 + (ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 0 1 1) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 1 1 0) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 0 1)) * h00 + (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 1 1) + ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 1 0) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h10 + (ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 0 1)) * h01 + (ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 1 1) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 1 0) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 0 1 0 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 1 0 0 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 1 1 0 a')) * h00 + (ψ 0 0 0 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 0 1 0 a * (starRingEnd ℂ) (ψ 0 1 1 a') + ψ 1 0 0 a * (starRingEnd ℂ) (ψ 1 0 1 a') + ψ 1 1 0 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h10 + (ψ 0 0 1 a * (starRingEnd ℂ) (ψ 0 0 0 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 0 1 0 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 1 0 0 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 1 1 0 a')) * h01 + (ψ 0 0 1 a * (starRingEnd ℂ) (ψ 0 0 1 a') + ψ 0 1 1 a * (starRingEnd ℂ) (ψ 0 1 1 a') + ψ 1 0 1 a * (starRingEnd ℂ) (ψ 1 0 1 a') + ψ 1 1 1 a * (starRingEnd ℂ) (ψ 1 1 1 a')) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 1 1 0)) * h00 + (ψ a 0 0 0 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 0 1 0 * (starRingEnd ℂ) (ψ a' 0 1 1) + ψ a 1 0 0 * (starRingEnd ℂ) (ψ a' 1 0 1) + ψ a 1 1 0 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h10 + (ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 0 0 0) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 0 1 0) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 1 0 0) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 1 1 0)) * h01 + (ψ a 0 0 1 * (starRingEnd ℂ) (ψ a' 0 0 1) + ψ a 0 1 1 * (starRingEnd ℂ) (ψ a' 0 1 1) + ψ a 1 0 1 * (starRingEnd ℂ) (ψ a' 1 0 1) + ψ a 1 1 1 * (starRingEnd ℂ) (ψ a' 1 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 1 0)) * h00 + (ψ 0 a 0 0 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 0 a 1 0 * (starRingEnd ℂ) (ψ 0 a' 1 1) + ψ 1 a 0 0 * (starRingEnd ℂ) (ψ 1 a' 0 1) + ψ 1 a 1 0 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h10 + (ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 0 0) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 1 0) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 0 0) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 1 0)) * h01 + (ψ 0 a 0 1 * (starRingEnd ℂ) (ψ 0 a' 0 1) + ψ 0 a 1 1 * (starRingEnd ℂ) (ψ 0 a' 1 1) + ψ 1 a 0 1 * (starRingEnd ℂ) (ψ 1 a' 0 1) + ψ 1 a 1 1 * (starRingEnd ℂ) (ψ 1 a' 1 1)) * h11
  · simp [rhoSite, rho0, siteSwap, actOn, sum2, Psi.conj, Fin.sum_univ_two]
    linear_combination (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 0)) * h00 + (ψ 0 0 a 0 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 0 1 a 0 * (starRingEnd ℂ) (ψ 0 1 a' 1) + ψ 1 0 a 0 * (starRingEnd ℂ) (ψ 1 0 a' 1) + ψ 1 1 a 0 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h10 + (ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 0) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 0) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 0) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 0)) * h01 + (ψ 0 0 a 1 * (starRingEnd ℂ) (ψ 0 0 a' 1) + ψ 0 1 a 1 * (starRingEnd ℂ) (ψ 0 1 a' 1) + ψ 1 0 a 1 * (starRingEnd ℂ) (ψ 1 0 a' 1) + ψ 1 1 a 1 * (starRingEnd ℂ) (ψ 1 1 a' 1)) * h11


theorem exists_diag_unitary (R : Fin 2 → Fin 2 → ℂ) (hR : ∀ a a', (starRingEnd ℂ) (R a a') = R a' a) :
    ∃ u : Matrix (Fin 2) (Fin 2) ℂ, uᴴ * u = 1 ∧
      ∑ p, ∑ p', u 0 p * R p p' * (starRingEnd ℂ) (u 1 p') = 0 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of R with hAdef
  have hA : A.IsHermitian := by
    ext i j
    simp [hAdef, Matrix.conjTranspose_apply, hR]
  have hUU' : (hA.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) * star (hA.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2
  have hdiag := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hdiag
  generalize (hA.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) = U at hdiag hUU'
  refine ⟨star U, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.star_eq_conjTranspose] at hUU'
    exact hUU'
  · have := congrFun (congrFun hdiag 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hAdef] at this
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    linear_combination this

theorem localApply_eq_actOn (a b c d : Op1) (ψ : Psi) :
    localApply a b c d ψ = actOn 0 a (actOn 1 b (actOn 2 c (actOn 3 d ψ))) := by
  funext p q r s
  simp only [localApply_apply, actOn, Fin.sum_univ_two]
  ring

theorem isProduct_localApply {ψ : Psi} (h : IsProduct ψ) (a b c d : Op1) :
    IsProduct (localApply a b c d ψ) := by
  obtain ⟨α, β, γ, δ, hψ⟩ := h
  refine ⟨fun x => ∑ p, a x p * α p, fun x => ∑ p, b x p * β p, fun x => ∑ p, c x p * γ p,
    fun x => ∑ p, d x p * δ p, ?_⟩
  intro p q r s
  simp only [localApply_apply, hψ, Fin.sum_univ_two]
  ring

/-- Marginals of a local unitary image: site `i` is conjugated by the `i`-th unitary. -/
theorem rhoSite_localApply (a b c d : Op1) (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (ψ : Psi) (x x' : Fin 2) :
    (rhoSite 0 (localApply a b c d ψ) x x' = ∑ p, ∑ p', a x p * rhoSite 0 ψ p p' * conj (a x' p')) ∧
    (rhoSite 1 (localApply a b c d ψ) x x' = ∑ p, ∑ p', b x p * rhoSite 1 ψ p p' * conj (b x' p')) ∧
    (rhoSite 2 (localApply a b c d ψ) x x' = ∑ p, ∑ p', c x p * rhoSite 2 ψ p p' * conj (c x' p')) ∧
    (rhoSite 3 (localApply a b c d ψ) x x' = ∑ p, ∑ p', d x p * rhoSite 3 ψ p p' * conj (d x' p')) := by
  rw [localApply_eq_actOn]
  have n10 := rhoSite_actOn_ne 1 0 (by decide) b hb
  have n20 := rhoSite_actOn_ne 2 0 (by decide) c hc
  have n30 := rhoSite_actOn_ne 3 0 (by decide) d hd
  have n01 := rhoSite_actOn_ne 0 1 (by decide) a ha
  have n21 := rhoSite_actOn_ne 2 1 (by decide) c hc
  have n31 := rhoSite_actOn_ne 3 1 (by decide) d hd
  have n02 := rhoSite_actOn_ne 0 2 (by decide) a ha
  have n12 := rhoSite_actOn_ne 1 2 (by decide) b hb
  have n32 := rhoSite_actOn_ne 3 2 (by decide) d hd
  have n03 := rhoSite_actOn_ne 0 3 (by decide) a ha
  have n13 := rhoSite_actOn_ne 1 3 (by decide) b hb
  have n23 := rhoSite_actOn_ne 2 3 (by decide) c hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rhoSite_actOn_same]; simp only [n10, n20, n30]
  · rw [n01, rhoSite_actOn_same]; simp only [n21, n31]
  · rw [n02, n12, rhoSite_actOn_same]; simp only [n32]
  · rw [n03, n13, n23, rhoSite_actOn_same]


/-- **Zeros of the sharp polarisation remainder with `τ = 0`** (`lem:fqe-polarization-remainder-zeros`,
non-critical case): a unit vector with `s = 0`, `F = (3/4) W₁` and `W₁ > 0` is a fully product state. -/
theorem H_zero_product (ψ : Psi) (hψ : normSqPsi ψ = 1) (hτ : spinFlipForm ψ = 0)
    (hF : sexticF ψ = 3 / 4 * blochSq ψ) (hW : 0 < blochSq ψ) : IsProduct ψ := by
  obtain ⟨u0, hu0, hd0⟩ := exists_diag_unitary (fun a a' => rhoSite 0 ψ a a') (rhoSite_conj 0 ψ)
  obtain ⟨u1, hu1, hd1⟩ := exists_diag_unitary (fun a a' => rhoSite 1 ψ a a') (rhoSite_conj 1 ψ)
  obtain ⟨u2, hu2, hd2⟩ := exists_diag_unitary (fun a a' => rhoSite 2 ψ a a') (rhoSite_conj 2 ψ)
  obtain ⟨u3, hu3, hd3⟩ := exists_diag_unitary (fun a a' => rhoSite 3 ψ a a') (rhoSite_conj 3 ψ)
  have hLU : LUEquiv ψ (localApply u0 u1 u2 u3 ψ) := ⟨u0, u1, u2, u3, hu0, hu1, hu2, hu3, rfl⟩
  have hn' := normSqPsi_LUEquiv hLU
  have hF' := sexticF_LUEquiv hLU
  have hW' := blochSq_LUEquiv hLU
  have hτ' := normSq_spinFlip_LUEquiv hLU
  have hmarg := rhoSite_localApply u0 u1 u2 u3 hu0 hu1 hu2 hu3 ψ 0 1
  have hdiag : ∀ i, rhoSite i (localApply u0 u1 u2 u3 ψ) 0 1 = 0 := by
    intro i
    fin_cases i
    · exact hmarg.1.trans hd0
    · exact hmarg.2.1.trans hd1
    · exact hmarg.2.2.1.trans hd2
    · exact hmarg.2.2.2.trans hd3
  have hprod := diag_gauge_product (localApply u0 u1 u2 u3 ψ) (by rw [hn', hψ])
    (by
      have : Complex.normSq (spinFlipForm (localApply u0 u1 u2 u3 ψ)) = 0 := by rw [hτ', hτ]; simp
      exact Complex.normSq_eq_zero.1 this)
    (by rw [hF', hW', hF]) (by rw [hW']; exact hW) hdiag
  obtain ⟨a, b, c, d, -, -, -, -, hback⟩ := hLU.symm
  rw [← hback]
  exact isProduct_localApply hprod a b c d

/-- info: 'FormalResearch.FourQubitEntropy.H_zero_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms H_zero_product

end FormalResearch.FourQubitEntropy

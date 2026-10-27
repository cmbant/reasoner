import Mathlib
import FormalResearch.FrameFree.OddWordsCopies

/-!
# Polarization on the symmetric subspace (Paper P, `prop:oddwords` (i))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`eq_zero_of_ev_kronVec`: a matrix `B` on the slots `α × γ` that is invariant under permuting the rows'
copies and the columns' copies and satisfies `⟨ψ^{⊗γ}|B|ψ^{⊗γ}⟩ = 0` for every `ψ` is zero.  This is the
fact that a Hermitian operator on `Sym^k V` is determined by its values on the product vectors.

Route.  (1) `Fn B w z = Σ_{x,y} B x y ∏_g w(col_g x) ∏_g z(col_g y)` vanishes for all complex `w, z`:
it is a polynomial `Q` in `(a, b)` with `w = a - i b`, `z = a + i b`, which vanishes on real points
(`MvPolynomial.funext_set`), hence identically.  (2) Hence the polynomial with variables `w, z` is zero
(`MvPolynomial.funext`), and its coefficient at the monomial of the type of `(x₀, y₀)` is
`(#orbit x₀)(#orbit y₀) B x₀ y₀` by the invariance, so `B x₀ y₀ = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

variable {α γ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ]

/-- The bilinearised expectation `Σ_{x,y} B_{xy} w^{⊗γ}(x) z^{⊗γ}(y)`. -/
def Fn (B : OpS (α × γ)) (w z : (α → Fin 2) → ℂ) : ℂ :=
  ∑ x, ∑ y, B x y * kronVec γ w x * kronVec γ z y

theorem ev_kronVec_eq_Fn (B : OpS (α × γ)) (ψ : (α → Fin 2) → ℂ) :
    ev B (kronVec γ ψ) = Fn B (fun d => conj (ψ d)) ψ := by
  rw [ev_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [kronVec, map_prod]
  ring

/-- The polynomial `Q` in real/imaginary coordinates `(a, b)`: `w = a - i b`, `z = a + i b`. -/
noncomputable def polyQ (B : OpS (α × γ)) : MvPolynomial ((α → Fin 2) ⊕ (α → Fin 2)) ℂ :=
  ∑ x, ∑ y, MvPolynomial.C (B x y) *
    (∏ g, (MvPolynomial.X (Sum.inl (fun a => x (a, g))) -
      MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr (fun a => x (a, g))))) *
    (∏ g, (MvPolynomial.X (Sum.inl (fun a => y (a, g))) +
      MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inr (fun a => y (a, g)))))

theorem eval_polyQ (B : OpS (α × γ)) (v : (α → Fin 2) ⊕ (α → Fin 2) → ℂ) :
    MvPolynomial.eval v (polyQ B) =
      Fn B (fun d => v (Sum.inl d) - Complex.I * v (Sum.inr d))
        (fun d => v (Sum.inl d) + Complex.I * v (Sum.inr d)) := by
  simp [polyQ, Fn, kronVec, map_sum, map_prod, mul_assoc]

theorem Fn_eq_zero (B : OpS (α × γ)) (h : ∀ ψ : (α → Fin 2) → ℂ, ev B (kronVec γ ψ) = 0)
    (w z : (α → Fin 2) → ℂ) : Fn B w z = 0 := by
  have hQ : polyQ B = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal)) (fun _ => ?_) ?_
    · exact Set.infinite_range_of_injective Complex.ofReal_injective
    · intro v hv
      have hreal : ∀ i, ∃ r : ℝ, (r : ℂ) = v i := fun i => hv i (Set.mem_univ i)
      choose r hr using hreal
      have hv' : v = fun i => (r i : ℂ) := (funext hr).symm
      rw [eval_polyQ, map_zero]
      have := h (fun d => (r (Sum.inl d) : ℂ) + Complex.I * r (Sum.inr d))
      rw [ev_kronVec_eq_Fn] at this
      convert this using 2
      · funext d; rw [hv']; simp [Complex.conj_ofReal]; ring
      · funext d; rw [hv']
  have := eval_polyQ B (Sum.elim (fun d => (z d + w d) / 2) (fun d => (z d - w d) / (2 * Complex.I)))
  rw [hQ, map_zero] at this
  rw [this]
  congr 1
  · funext d; simp only [Sum.elim_inl, Sum.elim_inr]; field_simp; ring
  · funext d; simp only [Sum.elim_inl, Sum.elim_inr]; field_simp; ring

/-- Column `g` of a slot configuration. -/
def col (x : α × γ → Fin 2) (g : γ) : α → Fin 2 := fun a => x (a, g)

/-- The exponent of the monomial `∏_g W_{col_g x}`. -/
noncomputable def tw (x : α × γ → Fin 2) : ((α → Fin 2) ⊕ (α → Fin 2)) →₀ ℕ :=
  ∑ g, Finsupp.single (Sum.inl (col x g)) 1

/-- The exponent of the monomial `∏_g Z_{col_g y}`. -/
noncomputable def tz (y : α × γ → Fin 2) : ((α → Fin 2) ⊕ (α → Fin 2)) →₀ ℕ :=
  ∑ g, Finsupp.single (Sum.inr (col y g)) 1

/-- The polynomial in the variables `(w, z)`. -/
noncomputable def polyP (B : OpS (α × γ)) : MvPolynomial ((α → Fin 2) ⊕ (α → Fin 2)) ℂ :=
  ∑ x, ∑ y, MvPolynomial.monomial (tw x + tz y) (B x y)

theorem monomial_tw_tz (x y : α × γ → Fin 2) (c : ℂ) :
    MvPolynomial.monomial (tw x + tz y) c =
      MvPolynomial.C c * (∏ g, MvPolynomial.X (Sum.inl (col x g))) *
        ∏ g, MvPolynomial.X (Sum.inr (col y g)) := by
  have h1 : (∏ g, (MvPolynomial.X (Sum.inl (col x g)) : MvPolynomial _ ℂ)) =
      MvPolynomial.monomial (tw x) 1 := by
    rw [tw, MvPolynomial.monomial_sum_one]; rfl
  have h2 : (∏ g, (MvPolynomial.X (Sum.inr (col y g)) : MvPolynomial _ ℂ)) =
      MvPolynomial.monomial (tz y) 1 := by
    rw [tz, MvPolynomial.monomial_sum_one]; rfl
  rw [h1, h2, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial]
  simp

theorem eval_polyP (B : OpS (α × γ)) (v : (α → Fin 2) ⊕ (α → Fin 2) → ℂ) :
    MvPolynomial.eval v (polyP B) = Fn B (fun d => v (Sum.inl d)) (fun d => v (Sum.inr d)) := by
  simp only [polyP, monomial_tw_tz, Fn, kronVec, map_sum, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  rfl

theorem polyP_eq_zero (B : OpS (α × γ)) (h : ∀ w z : (α → Fin 2) → ℂ, Fn B w z = 0) : polyP B = 0 := by
  refine MvPolynomial.funext fun v => ?_
  rw [eval_polyP, h, map_zero]

theorem tw_inl (x : α × γ → Fin 2) (d : α → Fin 2) :
    tw x (Sum.inl d) = (Finset.univ.filter fun g => col x g = d).card := by
  simp [tw, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole]

theorem tw_inr (x : α × γ → Fin 2) (d : α → Fin 2) : tw x (Sum.inr d) = 0 := by
  simp [tw, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem tz_inl (x : α × γ → Fin 2) (d : α → Fin 2) : tz x (Sum.inl d) = 0 := by
  simp [tz, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem tz_inr (x : α × γ → Fin 2) (d : α → Fin 2) :
    tz x (Sum.inr d) = (Finset.univ.filter fun g => col x g = d).card := by
  simp [tz, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole]

theorem exists_copyPerm_of_tw_eq {x x0 : α × γ → Fin 2} (h : tw x = tw x0) :
    ∃ c : Equiv.Perm γ, x = x0 ∘ ⇑(copyPerm (α := α) c) := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_fiber_eq (col x0) (col x) (fun d => by
    rw [← tw_inl, ← tw_inl, h])
  refine ⟨σ, funext fun q => ?_⟩
  have := congrFun (hσ q.2) q.1
  simp only [col] at this
  exact this

theorem exists_copyPerm_of_tz_eq {y y0 : α × γ → Fin 2} (h : tz y = tz y0) :
    ∃ c : Equiv.Perm γ, y = y0 ∘ ⇑(copyPerm (α := α) c) := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_fiber_eq (col y0) (col y) (fun d => by
    rw [← tz_inr, ← tz_inr, h])
  refine ⟨σ, funext fun q => ?_⟩
  have := congrFun (hσ q.2) q.1
  simp only [col] at this
  exact this

theorem coeff_polyP (B : OpS (α × γ)) (m : ((α → Fin 2) ⊕ (α → Fin 2)) →₀ ℕ) :
    (polyP B).coeff m = ∑ x, ∑ y, if tw x + tz y = m then B x y else 0 := by
  simp only [polyP, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem add_eq_iff {x y x0 y0 : α × γ → Fin 2} :
    tw x + tz y = tw x0 + tz y0 ↔ tw x = tw x0 ∧ tz y = tz y0 := by
  constructor
  · intro h
    constructor
    · refine Finsupp.ext fun i => ?_
      rcases i with d | d
      · have := congrArg (fun f => f (Sum.inl d)) h
        simpa [tz_inl] using this
      · rw [tw_inr, tw_inr]
    · refine Finsupp.ext fun i => ?_
      rcases i with d | d
      · rw [tz_inl, tz_inl]
      · have := congrArg (fun f => f (Sum.inr d)) h
        simpa [tw_inr] using this
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- **Polarization on `Sym^k`.**  A matrix invariant under permuting the copies of its row and of its
column index and with vanishing expectation on every product vector `ψ^{⊗γ}` is zero. -/
theorem eq_zero_of_ev_kronVec (B : OpS (α × γ))
    (hrow : ∀ (x y : α × γ → Fin 2) (c : Equiv.Perm γ), B (x ∘ ⇑(copyPerm (α := α) c)) y = B x y)
    (hcol : ∀ (x y : α × γ → Fin 2) (c : Equiv.Perm γ), B x (y ∘ ⇑(copyPerm (α := α) c)) = B x y)
    (h : ∀ ψ : (α → Fin 2) → ℂ, ev B (kronVec γ ψ) = 0) : B = 0 := by
  classical
  ext x0 y0
  have hP := polyP_eq_zero B (Fn_eq_zero B h)
  have hc := congrArg (fun p : MvPolynomial _ ℂ => p.coeff (tw x0 + tz y0)) hP
  simp only [coeff_polyP] at hc
  have hz : (0 : MvPolynomial ((α → Fin 2) ⊕ (α → Fin 2)) ℂ).coeff (tw x0 + tz y0) = 0 := by simp
  rw [hz] at hc
  have hterm : ∀ x y, (if tw x + tz y = tw x0 + tz y0 then B x y else 0) =
      (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℂ) else 0) * B x0 y0 := by
    intro x y
    simp only [add_eq_iff]
    by_cases hxy : tw x = tw x0 ∧ tz y = tz y0
    · rw [if_pos hxy, if_pos hxy, one_mul]
      obtain ⟨c, rfl⟩ := exists_copyPerm_of_tw_eq hxy.1
      obtain ⟨c', rfl⟩ := exists_copyPerm_of_tz_eq hxy.2
      rw [hrow, hcol]
    · rw [if_neg hxy, if_neg hxy, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y] at hc
  simp_rw [← Finset.sum_mul] at hc
  have hN : (∑ x : α × γ → Fin 2, ∑ y : α × γ → Fin 2,
      (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℂ) else 0)) ≠ 0 := by
    have h1 : ((∑ x : α × γ → Fin 2, ∑ y : α × γ → Fin 2,
        (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℕ) else 0) : ℕ) : ℂ) =
        ∑ x : α × γ → Fin 2, ∑ y : α × γ → Fin 2,
          (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℂ) else 0) := by
      push_cast; rfl
    rw [← h1]
    have h2 : 0 < ∑ x : α × γ → Fin 2, ∑ y : α × γ → Fin 2,
        (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℕ) else 0) := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun x : α × γ → Fin 2 =>
        ∑ y : α × γ → Fin 2, (if tw x = tw x0 ∧ tz y = tz y0 then (1 : ℕ) else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x0))
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun y : α × γ → Fin 2 =>
        (if tw x0 = tw x0 ∧ tz y = tz y0 then (1 : ℕ) else 0))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ y0))
      simp
    exact_mod_cast h2.ne'
  exact (mul_eq_zero.1 hc).resolve_left hN

end FormalResearch.FrameFree.OddWords

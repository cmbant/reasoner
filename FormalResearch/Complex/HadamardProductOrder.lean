module

public import FormalResearch.Complex.HadamardProduct

/-!
# Zeros of the canonical product with multiplicity (Hadamard factorization, milestone H1, complement)

For `CanonData p a` (no zero entry, `Σ ‖a_i‖^{-(p+1)} < ∞`) the canonical product `Φ = canonProd p a` is entire (H1) and
**its order of vanishing at `w` is the number of `i` with `a i = w`**:
`analyticOrderNatAt (canonProd p a) w = (a ⁻¹' {w}).ncard` (`Hadamard.analyticOrderNatAt_canonProd`), the fibre being
finite (`Hadamard.CanonData.finite_fibre`).  In particular the zero set of `Φ` is exactly the range of `a` with the
prescribed multiplicities.  **Proved.**
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators Classical

namespace FormalResearch.Hadamard

variable {ι : Type*}

lemma CanonData.finite_fibre {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (w : ℂ) :
    (a ⁻¹' {w}).Finite := by
  have hev := h.eventually_ge (‖w‖ + 1)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun i hi => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
  simp only [Set.mem_ofPred_eq, not_le]
  rw [hi]; linarith

/-- Splitting off a finite set of factors. -/
lemma canonProd_split {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (s : Finset ι) (z : ℂ) :
    canonProd p a z = (∏ i ∈ s, E p (z / a i)) *
      canonProd p (fun i : ↑((s : Set ι)ᶜ) => a i) z := by
  have hCD : CanonData p (fun i : ↑((s : Set ι)ᶜ) => a i) :=
    ⟨fun i => h.ne_zero _, h.summable.subtype _⟩
  have h1 : HasProd (fun i : (s : Set ι) => E p (z / a i)) (∏ i ∈ s, E p (z / a i)) :=
    s.hasProd (fun i => E p (z / a i))
  have h2 := canonProd_hasProd_at hCD z
  exact (h1.mul_compl h2).tprod_eq

/-- A single elementary factor has a simple zero at `w ≠ 0`. -/
lemma analyticOrderAt_E_comp (p : ℕ) {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun z => E p (z / w)) w = 1 := by
  have han : AnalyticAt ℂ (fun z => E p (z / w)) w :=
    ((differentiable_E p).comp (differentiable_id.div_const w)).analyticAt w
  have h1 : (fun z : ℂ => E p (z / w)) w = 0 := by simp [E, div_self hw]
  have h2 : deriv (fun z : ℂ => E p (z / w)) w ≠ 0 := by
    have hd : HasDerivAt (fun z : ℂ => z / w) (1 / w) w := by
      simpa using (hasDerivAt_id w).div_const w
    have hE : HasDerivAt (E p) _ ((fun z : ℂ => z / w) w) := hasDerivAt_E p ((fun z : ℂ => z / w) w)
    have := HasDerivAt.comp (h := fun z : ℂ => z / w) w hE hd
    have h3 : deriv (fun z : ℂ => E p (z / w)) w = _ := this.deriv
    rw [h3]
    simp only [div_self hw]
    simp [hw, Complex.exp_ne_zero]
  exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h1 h2

/-- **Multiplicity of the zeros of the canonical product.** -/
theorem analyticOrderNatAt_canonProd {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (w : ℂ) :
    analyticOrderNatAt (canonProd p a) w = (a ⁻¹' {w}).ncard := by
  have hfin := h.finite_fibre w
  set s : Finset ι := hfin.toFinset with hs
  have hCD : CanonData p (fun i : ↑((s : Set ι)ᶜ) => a i) :=
    ⟨fun i => h.ne_zero _, h.summable.subtype _⟩
  set Ψ := canonProd p (fun i : ↑((s : Set ι)ᶜ) => a i) with hΨ
  have hΨd : Differentiable ℂ Ψ := differentiable_canonProd hCD
  have hΨw : Ψ w ≠ 0 := by
    refine canonProd_ne_zero hCD fun i h' => ?_
    have hi := i.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hs, Set.Finite.mem_toFinset,
      Set.mem_preimage, Set.mem_singleton_iff] at hi
    exact hi h'.symm
  have hfun : canonProd p a = fun z => (fun z => E p (z / w)) z ^ s.card * Ψ z := by
    funext z
    rw [canonProd_split h s z]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => E p (z / w))]
    · simp
    · intro i hi
      have : a i = w := by simpa [hs] using hi
      rw [this]
  have hEan : AnalyticAt ℂ (fun z => E p (z / w)) w :=
    ((differentiable_E p).comp (differentiable_id.div_const w)).analyticAt w
  have hord : analyticOrderAt (canonProd p a) w = (s.card : ℕ∞) := by
    rw [hfun]
    have h1 : analyticOrderAt (fun z => (fun z => E p (z / w)) z ^ s.card * Ψ z) w =
        analyticOrderAt ((fun z => E p (z / w)) ^ s.card) w + analyticOrderAt Ψ w := by
      exact analyticOrderAt_mul (hEan.pow s.card) (hΨd.analyticAt w)
    rw [h1, analyticOrderAt_pow hEan]
    have h2 : analyticOrderAt Ψ w = 0 := by
      rw [analyticOrderAt_eq_zero]; exact Or.inr hΨw
    rw [h2, add_zero]
    by_cases hc : s.card = 0
    · simp [hc]
    · have hw : w ≠ 0 := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
        have : a i = w := by simpa [hs] using hi
        rw [← this]; exact h.ne_zero i
      rw [analyticOrderAt_E_comp p hw]; simp
  simp only [analyticOrderNatAt, hord, ENat.toNat_natCast]
  rw [Set.ncard_eq_toFinset_card _ hfin]

/-- info: 'FormalResearch.Hadamard.analyticOrderNatAt_canonProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.analyticOrderNatAt_canonProd

end FormalResearch.Hadamard

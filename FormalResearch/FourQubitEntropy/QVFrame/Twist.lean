module

public import FormalResearch.FourQubitEntropy.QVFrame.Basic

/-!
# T2: the J-twisted partial transpose (frame change)

For `a ≤ n` copies of `z` followed by `n - a` copies of `z̃ = J^{⊗4} z̄`, the quadratic form
`⟨w_a(z), A w_a(z)⟩` of a per-qubit Kronecker operator `A = ⊗_q X_q` equals `⟨z^{⊗n}, τ_a(A) z^{⊗n}⟩`,
where `τ_a(A) = ⊗_q τ_a(X_q)` and `τ_a` is the signed permutation of matrix entries

`τ_a(X)[β, α] = (-1)^{Σ_{t ≥ a} (α_t + β_t)} X[(β_{<a}, ᾱ_{≥a}), (α_{<a}, β̄_{≥a})]`.

In Lean `tau` is defined by this signed permutation; the equivalent expanded form is
`τ_a(X)[β,α] = Σ_{i,j} X[(β_{<a}, i_{≥a}), (α_{<a}, j_{≥a})] ∏_{t ≥ a} J[i_t,α_t] J[j_t,β_t]`
(`J` the real antisymmetric `2 × 2` matrix; not used below).  The statement is proved in a polarised form with independent vectors `u` (standing for `z̄`)
and `v` (standing for `z`), which is what the symmetriser argument needs.

* `pw a x y β = ∏_t (x or J y)(col β t)`: `x^{⊗a} ⊗ (J y)^{⊗(n-a)}`.
* `conj_pw`: conjugating `pw a x y` conjugates `x` and `y`; for the six-copy vector `w_a(z) = pw a z z̄`
  one gets `conj w_a(z) = pw a z̄ z` (`conj_wvec`, `sixCopy_eq` in `QVFrame/Gram.lean`).
* `twist_pol`: the polarised identity; `twist_qf`: the same as a statement about `qf` (the Hermitian form).
-/

@[expose] public section


open scoped ComplexConjugate
open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

variable {n : ℕ}

/-- `x^{⊗a} ⊗ (J y)^{⊗(n-a)}` as a function of the configuration. -/
def pw (a : ℕ) (x y : Site → ℂ) (β : Cfg n) : ℂ :=
  ∏ t : Fin n, (if t.val < a then x else Jv y) (col β t)

/-- First `a` slots from `u`, the others from `v`. -/
def mixW (a : ℕ) (u v : Wd n) : Wd n := fun t => if t.val < a then u t else v t

/-- The sign `(-1)^{Σ_{t ≥ a} (α_t + β_t)}`. -/
def tauSgn (a : ℕ) (α β : Wd n) : ℤ :=
  ∏ t : Fin n, if a ≤ t.val then (-1) ^ ((α t).val + (β t).val) else 1

/-- The `J`-twisted partial transpose of the copies `a, …, n-1` of one qubit:
`τ_a(X)[β, α] = (-1)^{Σ_{t ≥ a}(α_t+β_t)} X[(β_{<a}, ᾱ_{≥a}), (α_{<a}, β̄_{≥a})]`. -/
def tau {R : Type*} [CommRing R] (a : ℕ) (X : Matrix (Wd n) (Wd n) R) : Matrix (Wd n) (Wd n) R :=
  Matrix.of fun β α => (tauSgn a α β : R) * X (mixW a β (revW α)) (mixW a α (revW β))

theorem tau_apply {R : Type*} [CommRing R] (a : ℕ) (X : Matrix (Wd n) (Wd n) R) (β α : Wd n) :
    tau a X β α = (tauSgn a α β : R) * X (mixW a β (revW α)) (mixW a α (revW β)) := rfl

/-- `τ_a` commutes with ring homomorphisms of the entries. -/
theorem tau_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ)
    (X : Matrix (Wd n) (Wd n) R) : (tau a X).map f = tau a (X.map f) := by
  ext β α; simp [tau_apply]

/-! ### The involution on pairs of configurations -/

/-- `(α, β) ↦ ((α_{<a}, β̄_{≥a}), (β_{<a}, ᾱ_{≥a}))` on pairs of configurations. -/
def swapMap (a : ℕ) (p : Cfg n × Cfg n) : Cfg n × Cfg n :=
  (fun q => mixW a (p.1 q) (revW (p.2 q)), fun q => mixW a (p.2 q) (revW (p.1 q)))

theorem swapMap_invol (a : ℕ) : Function.Involutive (swapMap (n := n) a) := by
  intro p
  ext q t <;> by_cases h : t.val < a <;> simp [swapMap, mixW, revW, h]

/-- The involution as an equivalence. -/
def swapPerm (a : ℕ) : Equiv.Perm (Cfg n × Cfg n) := (swapMap_invol (n := n) a).toPerm _

/-- The sign of the `4` qubits together. -/
theorem prod_tauSgn (a : ℕ) (α' β' : Cfg n) :
    ∏ q : Fin 4, ((tauSgn a (α' q) (β' q) : ℤ) : ℂ) =
      ∏ t : Fin n, if a ≤ t.val then ((eps (col α' t) * eps (col β' t) : ℤ) : ℂ) else 1 := by
  unfold tauSgn
  push_cast
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h : a ≤ t.val
  · simp only [h, ite_true]
    simp only [pow_add, Finset.prod_mul_distrib, eps, col]
    push_cast
    rfl
  · simp [h]

theorem pw_swap (a : ℕ) (u v : Site → ℂ) (β' α' : Cfg n) :
    pw a u v (swapMap a (β', α')).1 * pw a v u (swapMap a (β', α')).2 =
      copyPower u n β' * copyPower v n α' *
        ∏ q : Fin 4, ((tauSgn a (α' q) (β' q) : ℤ) : ℂ) := by
  rw [prod_tauSgn, copyPower_eq_prod, copyPower_eq_prod]
  unfold pw
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h : t.val < a
  · have h' : ¬ a ≤ t.val := by omega
    have e1 : col (swapMap a (β', α')).1 t = col β' t := by
      funext q; simp [swapMap, col, mixW, h]
    have e2 : col (swapMap a (β', α')).2 t = col α' t := by
      funext q; simp [swapMap, col, mixW, h]
    simp [h, h', e1, e2, mul_comm]
  · have h' : a ≤ t.val := by omega
    have e1 : col (swapMap a (β', α')).1 t = rev' (col α' t) := by
      funext q; simp [swapMap, col, mixW, h, rev', revW]
    have e2 : col (swapMap a (β', α')).2 t = rev' (col β' t) := by
      funext q; simp [swapMap, col, mixW, h, rev', revW]
    simp only [h, h', ite_false, ite_true, e1, e2, Jv, rev'_rev', eps_rev']
    push_cast
    ring

/-- **T2, polarised.** With `u` standing for `z̄` and `v` for `z`:
`Σ_{α,β} (u^{a} ⊗ (Jv)^{n-a})(α) (⊗_q X_q)(α,β) (v^{a} ⊗ (Ju)^{n-a})(β) =
Σ_{β',α'} u^{⊗n}(β') (⊗_q τ_a X_q)(β',α') v^{⊗n}(α')`. -/
theorem twist_pol (a : ℕ) (u v : Site → ℂ) (X : Fin 4 → Matrix (Wd n) (Wd n) ℂ) :
    ∑ α : Cfg n, ∑ β : Cfg n, pw a u v α * (∏ q, X q (α q) (β q)) * pw a v u β =
      ∑ β' : Cfg n, ∑ α' : Cfg n,
        copyPower u n β' * (∏ q, tau a (X q) (β' q) (α' q)) * copyPower v n α' := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (swapPerm (n := n) a)]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨β', α'⟩ := p
  show _ = _
  have hp : swapPerm (n := n) a (β', α') = swapMap a (β', α') := rfl
  rw [hp]
  have hX : (∏ q, X q ((swapMap a (β', α')).1 q) ((swapMap a (β', α')).2 q)) *
      (∏ q : Fin 4, ((tauSgn a (α' q) (β' q) : ℤ) : ℂ)) = ∏ q, tau a (X q) (β' q) (α' q) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    simp [tau_apply, swapMap, mul_comm]
  calc pw a u v (swapMap a (β', α')).1 * (∏ q, X q ((swapMap a (β', α')).1 q) ((swapMap a (β', α')).2 q)) *
        pw a v u (swapMap a (β', α')).2
      = (pw a u v (swapMap a (β', α')).1 * pw a v u (swapMap a (β', α')).2) *
          ∏ q, X q ((swapMap a (β', α')).1 q) ((swapMap a (β', α')).2 q) := by ring
    _ = copyPower u n β' * copyPower v n α' *
          ((∏ q, X q ((swapMap a (β', α')).1 q) ((swapMap a (β', α')).2 q)) *
            ∏ q : Fin 4, ((tauSgn a (α' q) (β' q) : ℤ) : ℂ)) := by
        rw [pw_swap]; ring
    _ = _ := by rw [hX]; ring

/-- `conj` of a polarised power: the roles of `x, y` are conjugated (`J` is real). -/
theorem conj_pw (a : ℕ) (x y : Site → ℂ) (β : Cfg n) :
    conj (pw a x y β) = pw a (fun c => conj (x c)) (fun c => conj (y c)) β := by
  unfold pw
  rw [map_prod]
  refine Finset.prod_congr rfl fun t _ => ?_
  by_cases h : t.val < a <;> simp [h, Jv]

/-- **T2 as a statement about `qf`.** `⟨w, (⊗_q X_q) w'⟩ = ⟨ψ, (⊗_q τ_a X_q) ψ'⟩` with
`w = u^{a} ⊗ (J v)^{n-a}`, `w' = v^{a} ⊗ (J u)^{n-a}`, `ψ = u^{⊗n}`, `ψ' = v^{⊗n}`. -/
theorem twist_qf (a : ℕ) (u v : Site → ℂ) (X : Fin 4 → Matrix (Wd n) (Wd n) ℂ) :
    qf (pw a u v) (kronPi X) (pw a v u) =
      qf (copyPower u n) (kronPi fun q => tau a (X q)) (copyPower v n) :=
  twist_pol a u v X

end FormalResearch.FourQubitEntropy.QVFrame

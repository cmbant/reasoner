import FormalResearch.FourQubitEntropy.Transfer

/-!
# Dual numbers and jets: differentiating a generic polynomial expression

A generic expression `E` of `Generic.lean` is evaluated in any `RingOps` type. Here two more
`RingOps` types are provided.

* `Dual α`: pairs `(a, b)` standing for `a + b ε`, `ε² = 0`. Evaluating `E` at `(zᵢ, uᵢ)` returns
  `(E z, dE_z[u])`, the directional derivative. This is the *polarization*: the kernel computes the
  `ε`-part of a polynomial identity (`FlipGradientCert*.lean`), and it is the whole content of the
  derivative.
* `Jet`: complex functions differentiable at `0`. Evaluating `E` at the jets `σ ↦ zᵢ + σ uᵢ` gives a
  function of `σ` which is differentiable at `0`, and the map `f ↦ (f 0, f'(0))` is an `OpsHom` into
  `Dual ℂ`. Hence `σ ↦ E(z + σ u)` has derivative `(E (z + ε u)).b` at `0`.

`hasDerivAt_generic` is the only analytic statement; everything else is bookkeeping for `OpsHom`.
No `native_decide`, no axioms.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- Dual numbers `a + b ε` over a `RingOps` type. -/
structure Dual (α : Type) where
  a : α
  b : α

namespace Dual

instance {α : Type} [RingOps α] : RingOps (Dual α) where
  zero := ⟨RingOps.zero, RingOps.zero⟩
  one := ⟨RingOps.one, RingOps.zero⟩
  add p q := ⟨RingOps.add p.a q.a, RingOps.add p.b q.b⟩
  mul p q := ⟨RingOps.mul p.a q.a, RingOps.add (RingOps.mul p.a q.b) (RingOps.mul p.b q.a)⟩
  neg p := ⟨RingOps.neg p.a, RingOps.neg p.b⟩
  ofInt k := ⟨RingOps.ofInt k, RingOps.zero⟩

/-- Apply an `OpsHom` to both components. -/
def map {α β : Type} (f : α → β) (p : Dual α) : Dual β := ⟨f p.a, f p.b⟩

theorem opsHom_map {α β : Type} [RingOps α] [RingOps β] {f : α → β} (hf : OpsHom f) :
    OpsHom (Dual.map f) where
  map_zero := by
    show Dual.mk (f RingOps.zero) (f RingOps.zero) = Dual.mk RingOps.zero RingOps.zero
    rw [hf.map_zero]
  map_one := by
    show Dual.mk (f RingOps.one) (f RingOps.zero) = Dual.mk RingOps.one RingOps.zero
    rw [hf.map_one, hf.map_zero]
  map_add p q := by
    show Dual.mk (f (RingOps.add p.a q.a)) (f (RingOps.add p.b q.b)) =
      Dual.mk (RingOps.add (f p.a) (f q.a)) (RingOps.add (f p.b) (f q.b))
    rw [hf.map_add, hf.map_add]
  map_mul p q := by
    show Dual.mk (f (RingOps.mul p.a q.a))
        (f (RingOps.add (RingOps.mul p.a q.b) (RingOps.mul p.b q.a))) =
      Dual.mk (RingOps.mul (f p.a) (f q.a))
        (RingOps.add (RingOps.mul (f p.a) (f q.b)) (RingOps.mul (f p.b) (f q.a)))
    rw [hf.map_mul, hf.map_add, hf.map_mul, hf.map_mul]
  map_neg p := by
    show Dual.mk (f (RingOps.neg p.a)) (f (RingOps.neg p.b)) =
      Dual.mk (RingOps.neg (f p.a)) (RingOps.neg (f p.b))
    rw [hf.map_neg, hf.map_neg]
  map_ofInt k := by
    show Dual.mk (f (RingOps.ofInt k)) (f RingOps.zero) = Dual.mk (RingOps.ofInt k) RingOps.zero
    rw [hf.map_ofInt, hf.map_zero]

end Dual

/-- The dual state `z + ε u`. -/
def dualState {α : Type} (z u : State α) : State (Dual α) := fun a b c d => ⟨z a b c d, u a b c d⟩

/-! ### Jets -/

/-- Complex functions differentiable at `0`. -/
abbrev Jet := {f : ℂ → ℂ // DifferentiableAt ℂ f 0}

namespace Jet

instance : RingOps Jet where
  zero := ⟨fun _ => 0, differentiableAt_const _⟩
  one := ⟨fun _ => 1, differentiableAt_const _⟩
  add f g := ⟨fun t => f.1 t + g.1 t, f.2.add g.2⟩
  mul f g := ⟨fun t => f.1 t * g.1 t, f.2.mul g.2⟩
  neg f := ⟨fun t => -f.1 t, f.2.neg⟩
  ofInt k := ⟨fun _ => (k : ℂ), differentiableAt_const _⟩

/-- Value at a point. -/
def ev (σ : ℂ) (f : Jet) : ℂ := f.1 σ

/-- Value and derivative at `0`. -/
noncomputable def jet0 (f : Jet) : Dual ℂ := ⟨f.1 0, deriv f.1 0⟩

theorem opsHom_ev (σ : ℂ) : OpsHom (ev σ) where
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  map_neg _ := rfl
  map_ofInt _ := rfl

theorem opsHom_jet0 : OpsHom jet0 where
  map_zero := by
    show Dual.mk _ _ = Dual.mk _ _
    simp [RingOps.zero]
  map_one := by
    show Dual.mk _ _ = Dual.mk _ _
    simp [RingOps.one, RingOps.zero]
  map_add f g := by
    show Dual.mk _ _ = Dual.mk _ _
    simp only [jet0, RingOps.add]
    rw [deriv_fun_add f.2 g.2]
  map_mul f g := by
    show Dual.mk _ _ = Dual.mk _ _
    simp only [jet0, RingOps.add, RingOps.mul]
    rw [deriv_fun_mul f.2 g.2]
    ring_nf
  map_neg f := by
    show Dual.mk _ _ = Dual.mk _ _
    simp only [jet0, RingOps.neg]
    rw [deriv.fun_neg]
  map_ofInt k := by
    show Dual.mk _ _ = Dual.mk _ _
    simp [RingOps.ofInt, RingOps.zero]

end Jet

/-- The jet `σ ↦ z + σ u` of a state. -/
def pathJet (z u : State ℂ) : State Jet := fun a b c d =>
  ⟨fun σ => z a b c d + σ * u a b c d, by fun_prop⟩

theorem pathJet_ev (z u : State ℂ) (σ : ℂ) (a b c d : Fin 2) :
    Jet.ev σ (pathJet z u a b c d) = z a b c d + σ * u a b c d := rfl

theorem pathJet_jet0 (z u : State ℂ) (a b c d : Fin 2) :
    Jet.jet0 (pathJet z u a b c d) = ⟨z a b c d, u a b c d⟩ := by
  simp only [Jet.jet0, pathJet]
  refine congrArg₂ Dual.mk (by simp) ?_
  have : HasDerivAt (fun σ : ℂ => z a b c d + σ * u a b c d) (u a b c d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (u a b c d)).const_add (z a b c d)
  exact this.deriv

/-- **Directional derivative of a generic expression.** If `E` commutes with `OpsHom`s (as every
expression of `Generic.lean` does, by `Transfer.lean`), then `σ ↦ E (z + σ u) (w + σ u')` has
derivative `(E (z + ε u) (w + ε u')).b` at `0`. -/
theorem hasDerivAt_generic
    (E : {α : Type} → [RingOps α] → State α → State α → α)
    (hE : ∀ {α β : Type} [RingOps α] [RingOps β] {f : α → β}, OpsHom f →
      ∀ z w : State α, f (E z w) = E (z.map f) (w.map f))
    (z w u u' : State ℂ) :
    HasDerivAt (fun σ : ℂ => E (fun a b c d => z a b c d + σ * u a b c d)
        (fun a b c d => w a b c d + σ * u' a b c d)) (E (dualState z u) (dualState w u')).b 0 := by
  have h1 : ∀ σ : ℂ, E (fun a b c d => z a b c d + σ * u a b c d)
      (fun a b c d => w a b c d + σ * u' a b c d) = Jet.ev σ (E (pathJet z u) (pathJet w u')) := by
    intro σ
    rw [hE (Jet.opsHom_ev σ)]
    rfl
  have h2 : Jet.jet0 (E (pathJet z u) (pathJet w u')) = E (dualState z u) (dualState w u') := by
    rw [hE Jet.opsHom_jet0]
    congr 1 <;> funext a b c d <;> simp [State.map, pathJet_jet0, dualState]
  have h3 := (E (pathJet z u) (pathJet w u')).2.hasDerivAt
  have h4 : deriv (E (pathJet z u) (pathJet w u')).1 0 = (E (dualState z u) (dualState w u')).b := by
    rw [← h2]; rfl
  rw [h4] at h3
  have h5 : (fun σ : ℂ => E (fun a b c d => z a b c d + σ * u a b c d)
        (fun a b c d => w a b c d + σ * u' a b c d)) = (E (pathJet z u) (pathJet w u')).1 :=
    funext fun σ => h1 σ
  rw [h5]
  exact h3

end FormalResearch.FourQubitEntropy

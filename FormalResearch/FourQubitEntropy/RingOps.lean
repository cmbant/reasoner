import Mathlib

/-!
# Generic ring expressions

A polynomial identity in many variables is checked by writing the expression once, for any type
`α` carrying the operations `RingOps α`, and evaluating it in two ways: in `ℂ`, where it is the
actual expression about a state vector and its conjugate; and in `SparsePoly.lean`'s polynomial
type, where the kernel computes the normal form. `OpsHom` is what lets the normal form be
carried back: an operation-preserving map commutes with every expression built from the
operations.
-/

namespace FormalResearch.FourQubitEntropy

/-- The ring operations a generic expression is built from. -/
class RingOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  neg : α → α
  ofInt : ℤ → α

/-- An operation-preserving map between two `RingOps` types. -/
structure OpsHom {α β : Type} [RingOps α] [RingOps β] (f : α → β) : Prop where
  map_zero : f RingOps.zero = RingOps.zero
  map_one : f RingOps.one = RingOps.one
  map_add : ∀ a b, f (RingOps.add a b) = RingOps.add (f a) (f b)
  map_mul : ∀ a b, f (RingOps.mul a b) = RingOps.mul (f a) (f b)
  map_neg : ∀ a, f (RingOps.neg a) = RingOps.neg (f a)
  map_ofInt : ∀ k, f (RingOps.ofInt k) = RingOps.ofInt k

-- Operator notation for generic expressions: open this namespace to use `+ * -` on `RingOps` types.
namespace GenericOps
scoped instance (priority := 10) toAdd {α : Type} [RingOps α] : Add α := ⟨RingOps.add⟩
scoped instance (priority := 10) toMul {α : Type} [RingOps α] : Mul α := ⟨RingOps.mul⟩
scoped instance (priority := 10) toNeg {α : Type} [RingOps α] : Neg α := ⟨RingOps.neg⟩
scoped instance (priority := 10) toSub {α : Type} [RingOps α] : Sub α :=
  ⟨fun a b => RingOps.add a (RingOps.neg b)⟩
end GenericOps

instance : RingOps ℂ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  ofInt := (↑)

end FormalResearch.FourQubitEntropy

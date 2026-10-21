import FormalResearch.FourQubitEntropy.RingOps

/-!
# The sextic moment expression and its residual tensors, written generically

Everything here is built from `RingOps` only, so that it can be evaluated in `ℂ` (statement) and
in the reflected polynomial type (proof). `z` is a four-qubit vector and `w` its conjugate; they
are independent variables here, since the identity is polynomial.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- A four-qubit vector, indexed by the qubit values `a b c d`. -/
abbrev State (α : Type) := Fin 2 → Fin 2 → Fin 2 → Fin 2 → α

section Generic

variable {α : Type} [RingOps α]

/-- The integer `k` as an element of `α`. -/
def lit (k : ℤ) : α := RingOps.ofInt k

def sum2 (f : Fin 2 → α) : α := f 0 + f 1

def sum4 (f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → α) : α :=
  sum2 fun a => sum2 fun b => sum2 fun c => sum2 fun d => f a b c d

/-- The squared norm `n = ⟨z|w⟩`. -/
def normG (z w : State α) : α := sum4 fun a b c d => z a b c d * w a b c d

/-- A two-qubit matrix, `M a b a' b'`. -/
abbrev Mat2 (α : Type) := Fin 2 → Fin 2 → Fin 2 → Fin 2 → α

/-- Unnormalised reduced matrices on qubits `{1,2}`, `{1,3}`, `{1,4}`. -/
def marg12 (z w : State α) : Mat2 α := fun a b a' b' =>
  sum2 fun c => sum2 fun d => z a b c d * w a' b' c d
def marg13 (z w : State α) : Mat2 α := fun a c a' c' =>
  sum2 fun b => sum2 fun d => z a b c d * w a' b c' d
def marg14 (z w : State α) : Mat2 α := fun a d a' d' =>
  sum2 fun b => sum2 fun c => z a b c d * w a' b c d'

def tr2 (M : Mat2 α) : α :=
  sum2 fun a => sum2 fun b => sum2 fun a' => sum2 fun b' => M a b a' b' * M a' b' a b

def tr3 (M : Mat2 α) : α :=
  sum2 fun a => sum2 fun b => sum2 fun a' => sum2 fun b' => sum2 fun a'' => sum2 fun b'' =>
    M a b a' b' * M a' b' a'' b'' * M a'' b'' a b

/-- `F = 17 n P - 12 T - 12 n³` with `P = Σ tr R_{1j}²` and `T = Σ tr R_{1j}³`. -/
def Fgen (z w : State α) : α :=
  let n := normG z w
  let P := tr2 (marg12 z w) + tr2 (marg13 z w) + tr2 (marg14 z w)
  let T := tr3 (marg12 z w) + tr3 (marg13 z w) + tr3 (marg14 z w)
  lit 17 * n * P - lit 12 * T - lit 12 * n * n * n

/-- Relabel the qubits so that qubit `i` comes first. -/
def siteSwap (i : Fin 4) (z : State α) : State α :=
  match i with
  | 0 => z
  | 1 => fun a b c d => z b a c d
  | 2 => fun a b c d => z c b a d
  | 3 => fun a b c d => z d b c a

/-- Unnormalised one-qubit reduced matrix of the first qubit. -/
def rho0 (z w : State α) (a a' : Fin 2) : α :=
  sum2 fun b => sum2 fun c => sum2 fun d => z a b c d * w a' b c d

def trRho2 (z w : State α) : α :=
  sum2 fun a => sum2 fun a' => rho0 z w a a' * rho0 z w a' a

/-- `W₁ = Σ_i (2 tr R_i² - n²)`: the squared unnormalised Bloch vectors, summed over qubits. -/
def W1gen (z w : State α) : α :=
  let n := normG z w
  (lit 2 * trRho2 z w - n * n) + (lit 2 * trRho2 (siteSwap 1 z) (siteSwap 1 w) - n * n)
    + (lit 2 * trRho2 (siteSwap 2 z) (siteSwap 2 w) - n * n)
    + (lit 2 * trRho2 (siteSwap 3 z) (siteSwap 3 w) - n * n)

/-! ### The residual tensors

These are a certificate for the identity below, so they are written for cheap evaluation: the
`ε` contractions keep only their two nonzero entries, and the norm uses one representative of each
symmetry class of the three slots of the focused qubit.
-/

/-- `Σ_{a,t} ε(a,t) f a t` with `ε = [[0,1],[-1,0]]`. -/
def epsSum (f : Fin 2 → Fin 2 → α) : α := f 0 1 - f 1 0

/-- Sign of `ε(t, 1 - t)`. -/
def sgn (t : Fin 2) : ℤ := if t = 0 then 1 else -1

/-- `z̃ = ε^{⊗4} w`, with `w` the conjugate. -/
def ztil (w : State α) (t0 t1 t2 t3 : Fin 2) : α :=
  lit (sgn t0 * sgn t1 * sgn t2 * sgn t3) * w (1 - t0) (1 - t1) (1 - t2) (1 - t3)

/-- One component of the unsymmetrised tensor for the focused qubit `0`: the other three qubits are
contracted with `L` or, for `V`, with `L + M`. `x0 y0 t0` are the three slots of the focused qubit
and `o1 o2 o3` the output qubits of the others. -/
def resRaw (L : Bool) (z w : State α) (x0 y0 t0 o1 o2 o3 : Fin 2) : α :=
  let pick (c o a : Fin 2) : Fin 2 := if c = 0 then o else a
  let cs : List (Fin 2 × Fin 2 × Fin 2) :=
    if L then [(0, 0, 0)] else
    [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
  cs.foldr (fun c acc =>
    (epsSum fun a1 t1 => epsSum fun a2 t2 => epsSum fun a3 t3 =>
        z x0 (pick c.1 o1 a1) (pick c.2.1 o2 a2) (pick c.2.2 o3 a3) *
         z y0 (pick (1 - c.1) o1 a1) (pick (1 - c.2.1) o2 a2) (pick (1 - c.2.2) o3 a3) *
         ztil w t0 t1 t2 t3) + acc) (lit 0)

/-- Sum over the six placements of the three slots of the focused qubit. -/
def resSym (L : Bool) (z w : State α) (x y t o1 o2 o3 : Fin 2) : α :=
  resRaw L z w x y t o1 o2 o3 + resRaw L z w x t y o1 o2 o3 + resRaw L z w y x t o1 o2 o3
    + resRaw L z w y t x o1 o2 o3 + resRaw L z w t x y o1 o2 o3 + resRaw L z w t y x o1 o2 o3

/-- Six times the residual tensor, `6 (2 V - 19 U)`. -/
def resTensor (z w : State α) (x y t o1 o2 o3 : Fin 2) : α :=
  lit 2 * resSym false z w x y t o1 o2 o3 - lit 19 * resSym true z w x y t o1 o2 o3

/-- `Σ_{o} 36 |R_{xyt,o}|²` for one triple of slot values; the conjugate tensor is the one with
`z` and `w` exchanged. -/
def resSlot (z w : State α) (x y t : Fin 2) : α :=
  sum2 fun o1 => sum2 fun o2 => sum2 fun o3 =>
    resTensor z w x y t o1 o2 o3 * resTensor w z x y t o1 o2 o3

/-- `36 ‖R‖²` for the focused qubit `0`. The tensor is symmetric in its three slots, so the eight
slot triples fall into the classes `000`, `001`, `011`, `111` of sizes `1, 3, 3, 1`. -/
def resNorm0 (z w : State α) : α :=
  resSlot z w 0 0 0 + lit 3 * resSlot z w 0 0 1 + lit 3 * resSlot z w 0 1 1 + resSlot z w 1 1 1

/-- `1152 F - 540 n W₁ - 3 (n₀ + n₁ + n₂ + n₃)`, where `nᵢ = 36 ‖Rᵢ‖²`. -/
def defectG (z w : State α) (n0 n1 n2 n3 : α) : α :=
  lit 1152 * Fgen z w - lit 540 * (normG z w * W1gen z w) - lit 3 * (n0 + n1 + n2 + n3)

/-- The defect with the residual norms of the four qubits. It is identically zero. -/
def sexticDefect (z w : State α) : α :=
  defectG z w (resNorm0 z w) (resNorm0 (siteSwap 1 z) (siteSwap 1 w))
    (resNorm0 (siteSwap 2 z) (siteSwap 2 w)) (resNorm0 (siteSwap 3 z) (siteSwap 3 w))

end Generic

end FormalResearch.FourQubitEntropy

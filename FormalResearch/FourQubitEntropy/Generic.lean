import FormalResearch.FourQubitEntropy.RingOps

/-!
# The sextic moment expression and its residual vectors, written generically

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

/-- Six times the residual tensor, `6 (V - 8 U)`, where `U = S ∏_{j≠i} L_j w` (`L` only) and
`V = S ∏_{j≠i} (L_j + M_j) w`. -/
def resTensor (z w : State α) (x y t o1 o2 o3 : Fin 2) : α :=
  resSym false z w x y t o1 o2 o3 - lit 8 * resSym true z w x y t o1 o2 o3

/-- `Σ_{o} 36 |(V - 8U)_{xyt,o}|²` for one triple of slot values; the conjugate tensor is the one with
`z` and `w` exchanged. -/
def resSlot (z w : State α) (x y t : Fin 2) : α :=
  sum2 fun o1 => sum2 fun o2 => sum2 fun o3 =>
    resTensor z w x y t o1 o2 o3 * resTensor w z x y t o1 o2 o3

/-- `36 ‖V - 8U‖²` for the focused qubit `0`. The tensor is symmetric in its three slots, so the eight
slot triples fall into the classes `000`, `001`, `011`, `111` of sizes `1, 3, 3, 1`. -/
def resNorm0 (z w : State α) : α :=
  resSlot z w 0 0 0 + lit 3 * resSlot z w 0 0 1 + lit 3 * resSlot z w 0 1 1 + resSlot z w 1 1 1

/-! ### The pair vectors

`actSite s z w` is the vector `R_s^{(s)} z`: the unnormalised one-qubit marginal `R_s` of qubit `s`
acting on qubit `s` of `z`. The pair vectors are `(R_i^{(i)} - R_j^{(j)}) z`.
-/

/-- Component `(a, b, c, d)` of `R_s^{(s)} z`. -/
def actSite (s : Fin 4) (z w : State α) (a b c d : Fin 2) : α :=
  match s with
  | 0 => sum2 fun t => rho0 z w a t * z t b c d
  | 1 => sum2 fun t => rho0 (siteSwap 1 z) (siteSwap 1 w) b t * z a t c d
  | 2 => sum2 fun t => rho0 (siteSwap 2 z) (siteSwap 2 w) c t * z a b t d
  | 3 => sum2 fun t => rho0 (siteSwap 3 z) (siteSwap 3 w) d t * z a b c t

/-- Component of `(R_i^{(i)} - R_j^{(j)}) z`. -/
def pairVec (i j : Fin 4) (z w : State α) (a b c d : Fin 2) : α :=
  actSite i z w a b c d - actSite j z w a b c d

/-- `‖(R_i^{(i)} - R_j^{(j)}) z‖²`; the conjugate vector is the one with `z` and `w` exchanged. -/
def pairNorm (i j : Fin 4) (z w : State α) : α :=
  sum4 fun a b c d => pairVec i j z w a b c d * pairVec i j w z a b c d

/-- `Σ_{i<j} ‖(R_i^{(i)} - R_j^{(j)}) z‖²`. -/
def pairSum (z w : State α) : α :=
  pairNorm 0 1 z w + pairNorm 0 2 z w + pairNorm 0 3 z w + pairNorm 1 2 z w + pairNorm 1 3 z w
    + pairNorm 2 3 z w

/-- `96 F - 72 n W₁ - (n₀ + n₁ + n₂ + n₃) - 144 Σ_{i<j} ‖(R_i^{(i)} - R_j^{(j)}) z‖²`, where
`nᵢ = 36 ‖Vᵢ - 8Uᵢ‖²`; twelve times `8F - 6 n W₁ - 3 Σᵢ ‖Vᵢ - 8Uᵢ‖² - 12 Σ_{i<j} ‖…‖²`. -/
def defectG (z w : State α) (n0 n1 n2 n3 : α) : α :=
  lit 96 * Fgen z w - lit 72 * (normG z w * W1gen z w) - (n0 + n1 + n2 + n3)
    - lit 144 * pairSum z w

/-- The defect with the residual norms of the four qubits. It is identically zero. -/
def sexticDefect (z w : State α) : α :=
  defectG z w (resNorm0 z w) (resNorm0 (siteSwap 1 z) (siteSwap 1 w))
    (resNorm0 (siteSwap 2 z) (siteSwap 2 w)) (resNorm0 (siteSwap 3 z) (siteSwap 3 w))

end Generic

end FormalResearch.FourQubitEntropy

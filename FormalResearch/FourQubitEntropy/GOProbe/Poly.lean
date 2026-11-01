/-!
# GO certificate: sparse polynomials in 19 variables with packed keys (definitions, no Mathlib)

A monomial is a `Nat` key whose base-256 digit `i` (for `i < 19`) is the exponent of variable `i`; as long as
all exponents stay `< 256` (the checker verifies total degrees `≤ 48`), monomial multiplication is `Nat.add`.
A polynomial is a list of `(key, coefficient)`; sortedness is only needed for the final list comparison, never
for soundness.  Everything is ordinary structural recursion (or a `Nat` fuel), so the same definitions run in
the kernel and compiled (`native_decide`).  Semantics and soundness: `PolySound.lean`.
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

abbrev SP := List (Nat × Int)

/-- Merge two sorted polynomials (tail recursive, reversed accumulator); fuel `p.length + q.length + 1`. -/
def addGo : Nat → SP → SP → SP → SP
  | 0, acc, p, q => acc.reverseAux (p ++ q)
  | _ + 1, acc, [], q => acc.reverseAux q
  | _ + 1, acc, a :: p, [] => acc.reverseAux (a :: p)
  | f + 1, acc, a :: p, b :: q =>
    if a.1 < b.1 then addGo f (a :: acc) p (b :: q)
    else if b.1 < a.1 then addGo f (b :: acc) (a :: p) q
    else
      let c := a.2 + b.2
      if c = 0 then addGo f acc p q else addGo f ((a.1, c) :: acc) p q

def addSP (p q : SP) : SP := addGo (p.length + q.length + 1) [] p q

def pairUp : List SP → List SP
  | [] => []
  | [a] => [a]
  | a :: b :: t => addSP a b :: pairUp t

/-- Sum a list of polynomials by repeated pairwise addition. -/
def sumFuel : Nat → List SP → SP
  | 0, l => l.foldr addSP []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | f + 1, a :: b :: t => sumFuel f (pairUp (a :: b :: t))

def sumSP (l : List SP) : SP := sumFuel 64 l

def mulTerm (k : Nat) (c : Int) (q : SP) : SP := q.map fun s => (k + s.1, c * s.2)

def mulSP (p q : SP) : SP := sumSP (p.map fun t => mulTerm t.1 t.2 q)

def scaleSP (c : Int) (p : SP) : SP := if c = 0 then [] else p.map fun t => (t.1, c * t.2)

/-- Sort and combine an arbitrary list of terms. -/
def normSP (l : List (Nat × Int)) : SP := sumSP (l.map fun t => if t.2 = 0 then [] else [t])

def eqSP : SP → SP → Bool
  | [], [] => true
  | a :: p, b :: q => a.1 == b.1 && a.2 == b.2 && eqSP p q
  | _, _ => false

/-! ### Digits, degrees -/

/-- Exponent digit `i` of a key. -/
def dig (i k : Nat) : Nat := k / 256 ^ i % 256

/-- Total degree of a key (sum of the 19 digits). -/
def dsum (k : Nat) : Nat := ((List.range 19).map fun i => dig i k).sum

/-- All keys have total degree `≤ d`. -/
def dgOK (d : Nat) (p : SP) : Bool := p.all fun t => decide (dsum t.1 ≤ d)

/-! ### Signed coordinate maps -/

/-- Key of the monomial `∏ x_{mi i}^{e_i}` for the monomial `∏ x_i^{e_i}`. -/
def actKey (mi : List Nat) (k : Nat) : Nat :=
  ((List.range 19).map fun i => dig i k * 256 ^ (mi.getD i 0)).sum

/-- Sign `∏ sg_i^{e_i}`. -/
def actCoef (sg : List Int) (k : Nat) : Int :=
  ((List.range 19).map fun i => (sg.getD i 1) ^ (dig i k)).prod

/-- Substitute `x_i ↦ sg_i x_{mi i}`. -/
def actSP (g : List Nat × List Int) (p : SP) : SP :=
  normSP (p.map fun t => (actKey g.1 t.1, actCoef g.2 t.1 * t.2))

end FormalResearch.FourQubitEntropy.GOProbe

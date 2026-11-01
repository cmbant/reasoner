import QVCheckImpl.Impl4b

/-!
# The QV checker, part 5: quotient, placements, right-hand side, final comparison (K5, K6, K7)
-/
namespace QVCheck

opaque placeArr : Array Int := parseInts DataStr.placeS

/-- the 24 permutations of `{0,1,2,3}` in lexicographic order -/
def perms4 : Array (Array Nat) :=
  (List.range 4).toArray.flatMap fun a => (List.range 4).toArray.flatMap fun b => (List.range 4).toArray.flatMap fun c =>
    (List.range 4).toArray.filterMap fun d =>
      if a != b && a != c && a != d && b != c && b != d && c != d then some #[a, b, c, d] else none

/-- offset of the placement data of `(code, π)`: sector rank times `24 * (1 + 2 n²)` plus `π`-index times `(1 + 2n²)` -/
@[irreducible] def placeOffArr : Array Nat :=
  ((List.range 256).foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + (if nn c > 0 then 24 * (1 + 2 * nn c * nn c) else 0))) (#[], 0)).1
def placeOff (code pi : Nat) : Nat := placeOffArr.getD code 0 + pi * (1 + 2 * nn code * nn code)
def pden (code pi : Nat) : Int := gt placeArr (placeOff code pi)
def pSW (code pi a a' : Nat) : Int := gt placeArr (placeOff code pi + 1 + a * nn code + a')
def pSV (code pi a a' : Nat) : Int := gt placeArr (placeOff code pi + 1 + nn code * nn code + a * nn code + a')

def spinCode (s : Array Nat) : Nat := ((s.getD 0 0 * 4 + s.getD 1 0) * 4 + s.getD 2 0) * 4 + s.getD 3 0

/-- `qq = (pp[π[t]])_t` -/
def placedCode (code : Nat) (pi : Array Nat) : Nat :=
  spinCode (pi.map fun t => spinDigit code t)

/-- `perm_π` of a flat tensor of sector `code`: new axis `q` is old axis `π[q]` -/
def permFlatIdx (code : Nat) (pi : Array Nat) (f : Nat) : Nat :=
  -- new index digits i_q in radices of qq; old index j_{pi[q]} = i_q
  let qq := placedCode code pi
  let dig := fun q => f / stride qq q % mult (spinDigit qq q)
  (List.range 4).foldl (fun acc q => acc + (List.range 4).foldl (fun a2 q' => if pi.getD q' 0 == q then a2 + dig q' * stride code q else a2) 0) 0

/-- K5: `den · perm_π(V_a(pp)) = Σ SV[a][a'] V_{a'}(qq)` and the same for `W` -/
def checkPlacements (u : Unit) : Bool :=
  allTo (hide u 256) fun code => allTo 24 fun pii =>
    let pi := perms4.getD pii #[]
    nn code == 0 ||
    (let qq := placedCode code pi
     nn qq == nn code && pden code pii != 0 &&
     allTo (nn code) fun a => allTo (sdim qq) fun f =>
       let old := permFlatIdx code pi f
       pden code pii * vAt code a old == sumTo (nn code) (fun a' => pSV code pii a a' * vAt qq a' f) &&
       pden code pii * wAt code a old == sumTo (nn code) (fun a' => pSW code pii a a' * wAt qq a' f))

/-- `Qtot[code] = Ω (Σ_t q_t Ctil_t) Ξ^T / Z`, with exact division checked -/
def qtotOf (acc : Array (Array Int)) (code : Nat) : Array Int × Bool :=
  let n := nn code
  let Z := delta (pA code) ^ 2 * delta (pB code) ^ 2 * DataStr.lc ^ 2
  let C := acc.getD code #[]
  let om := slice omArr (nnOff code) (n * n); let xi := slice xiArr (nnOff code) (n * n)
  let M1 := tab (n * n) fun e => sumTo n fun u => gt om (e / n * n + u) * gt C (u * n + e % n)   -- (Ω C)[a][u']
  let Qs := tab (n * n) fun e => sumTo n fun u' => gt M1 (e / n * n + u') * gt xi (e % n * n + u')
  let Q := Qs.map fun x => x / Z
  (Q, Z != 0 && allTo (n * n) fun i => Z * gt Q i == gt Qs i)

def qtotAll (acc : Array (Array Int)) : Array (Array Int) × Bool :=
  (List.range 256).foldl (fun (r : Array (Array Int) × Bool) code =>
    if nn code == 0 then (r.1.push #[], r.2) else
    let (Q, ok) := qtotOf acc code
    (r.1.push Q, r.2 && ok)) (#[], true)

/-! ### Right-hand side (K6) -/

def swIdx (i x : Nat) : Nat := if x == i then i + 1 else if x == i + 1 then i else x
def wordImg (l : List Nat) : Array Nat :=
  l.foldl (fun old i => (List.range 6).toArray.map fun x => old.getD (swIdx i x) 0) ((List.range 6).toArray)
def wordImgs : Array (Array Nat) := words.toArray.map wordImg
def repCache : Array (Array Int) := Id.run do
  let mut r : Array (Array Int) := #[]
  for j in [0:4] do
    for l in words do
      r := r.push (repProd j l)
  return r
def repOf (j : Nat) (img : Array Nat) : Array Int :=
  match wordImgs.findIdx? (fun x => x == img) with
  | some w => repCache.getD (j * 720 + w) #[]
  | none => #[]

/-- a term of the right-hand side: coefficient and the four slot permutations (as image arrays) -/
abbrev RhsTerm := Int × Array (Array Nat)

def kronRep (code : Nat) (imgs : Array (Array Nat)) (X : Array Int) : Array Int :=
  (List.range 4).foldl (fun acc q =>
    modeProd (repOf (spinDigit code q) (imgs.getD q #[])) (mult (spinDigit code q)) (stride code q) false acc) X

def rhsCoords (terms : Array RhsTerm) (code : Nat) : Array Int :=
  let n := nn code; let D := sdim code
  terms.foldl (fun (acc : Array Int) (t : RhsTerm) =>
    let Xs := (List.range n).toArray.map fun b => kronRep code t.2 (slice vArr (vOff code + b * D) D)
    tab (n * n) fun e => gt acc e + t.1 * sumTo D (fun x => wAt code (e / n) x * gt (Xs.getD (e % n) #[]) x))
    (Array.replicate (n * n) 0)

/-! ### Final comparison (K7) -/

def lcmAll (xs : List Nat) : Nat := xs.foldl Nat.lcm 1

def checkFinal (rhs : Array RhsTerm) (Q : Array (Array Int)) (Dnum : Int) : Bool :=
  allTo 256 fun code => nn code == 0 ||
    (let n := nn code
     let Dn : Int := lcmAll ((List.range 24).map fun pii => (pden code pii * pden code pii).toNat)
     let R := rhsCoords rhs code
     allTo (n * n) fun e =>
       let a := e / n; let b := e % n
       (List.range 24).foldl (fun acc pii =>
         let qq := placedCode code (perms4.getD pii #[])
         let d2 := pden code pii * pden code pii
         acc + (Dn / d2) * sumTo n (fun a' => sumTo n fun b' =>
           pSW code pii a a' * gt (Q.getD qq #[]) (a' * n + b') * pSV code pii b b')) 0
       == Dn * 2 * Dnum * gt R e)

end QVCheck

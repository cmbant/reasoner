/-!
# GO certificate probe: reflective checker core (no Mathlib)

Sparse polynomials in 19 variables with the paper's packed monomial keys (variable `i` has exponent digit at
bits `3i`; total degree `≤ 6` makes products carry free, so monomial multiplication is `Nat.add`).
A polynomial is a list of `(key, coefficient)` sorted by key with no zero coefficients.

The check is `gramOK` on every block plus `identityOK`.  All definitions are ordinary structural recursion (on lists or on a `Nat` fuel), so they run both in the kernel
(`decide +kernel`) and compiled (`native_decide`).
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

abbrev SP := List (Nat × Int)

/-- Merge two sorted polynomials (tail recursive, reversed accumulator). -/
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
  | a :: b :: t => addSP a b :: pairUp t
  | l => l

/-- Sum a list of polynomials by repeated pairwise addition. -/
def sumFuel : Nat → List SP → SP
  | 0, l => l.foldr addSP []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | f + 1, l => sumFuel f (pairUp l)

def sumSP (l : List SP) : SP := sumFuel 64 l

def mulTerm (k : Nat) (c : Int) (q : SP) : SP := q.map fun s => (k + s.1, c * s.2)

def mulSP (p q : SP) : SP := sumSP (p.map fun t => mulTerm t.1 t.2 q)

def negSP (p : SP) : SP := p.map fun t => (t.1, -t.2)

def scaleSP (c : Int) (p : SP) : SP := if c = 0 then [] else p.map fun t => (t.1, c * t.2)

/-- Sort and combine an arbitrary list of terms. -/
def normSP (l : List (Nat × Int)) : SP := sumSP (l.map fun t => if t.2 = 0 then [] else [t])

/-! ### Certificate data -/

/-- One Gram block. `basis i` lists the atoms `(component, packed monomial, coefficient)` of the polynomial vector
entry `p_i`; `factor` is the compact factor `A`, `resid` the columns `Δ` (column `j` has `j+1` entries) and `corr`
the sparse columns `C`. -/
structure GBlock where
  cid : Nat
  ncomp : Nat
  size : Nat
  basis : List (List (Nat × Nat × Int))
  factor : List (List Int)
  resid : List (List Int)
  corr : List (List (Nat × Int))

/-! ### Gram positivity test (`eq:fqe-compact-gram-test`) -/

def corrAt (c : List (Nat × Int)) (i : Nat) : Int :=
  match c.find? (fun t => t.1 == i) with
  | some t => t.2
  | none => 0

/-- `D_ij = cd * Δ_ij + C_ij` for `i < j` (as absolute values) and the diagonal entry, for column `j`:
`(diagonal, absolute off-diagonal entries (i < j), their sum)`. -/
def colD (cd : Int) (rcol : List Int) (ccol : List (Nat × Int)) (j : Nat) : Int × List Int × Int :=
  let ds := (List.range rcol.length).zip rcol |>.map fun ic => cd * ic.2 + corrAt ccol ic.1
  let dj := ds.getD j 0
  let off := (ds.take j).map Int.natAbs |>.map Int.ofNat
  (dj, off, off.foldl (· + ·) 0)

def addLong : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addLong p q

/-- Fold over columns: (row accumulator, diagonals, column sums). -/
def gramScan (cd : Int) : Nat → List (List Int) → List (List (Nat × Int)) → List Int → List Int → List Int →
    List Int × List Int × List Int
  | _, [], _, acc, dg, cs => (acc, dg.reverse, cs.reverse)
  | j, r :: rs, cs', acc, dg, csum =>
    let (c, rest) := match cs' with | [] => ([], []) | x :: xs => (x, xs)
    let (d, off, s) := colD cd r c j
    gramScan cd (j + 1) rs rest (addLong acc off) (d :: dg) (s :: csum)

def gramOK (cd : Nat) (b : GBlock) : Bool :=
  let (acc, dg, cs) := gramScan cd 0 b.resid b.corr [] [] []
  let m : Int := b.size
  (b.resid.length == b.size) &&
  ((dg.zip (addLong acc cs)).all fun p => decide (2 * (p.1 - p.2) > m * cd)) &&
  (dg.length == b.size)

/-! ### Gram weights and the block expansion -/

def dot : List Int → List Int → Int
  | a :: p, b :: q => a * b + dot p q
  | _, _ => 0

/-- `round(grid * <F_i, F_j> / s^2)` with `s^2 = 2^(2 bits)`. -/
def hval (grid s2 : Int) (fi fj : List Int) : Int := (grid * dot fi fj + s2 / 2) / s2

/-- Weights of column `j`: base weights `(H + Δ)` and correction weights `C`, doubled off diagonal. -/
def colWeights (grid s2 : Int) (rows : List (List Int)) (fj : List Int) (rcol : List Int)
    (ccol : List (Nat × Int)) (j : Nat) : List Int × List Int :=
  let idx := List.range rcol.length
  let base := (rows.zip rcol).zip idx |>.map fun x =>
    (hval grid s2 x.1.1 fj + x.1.2) * (if x.2 == j then 1 else 2)
  let cor := idx.map fun i => corrAt ccol i * (if i == j then 1 else 2)
  (base, cor)

/-- Left combination `r_j[a] = Σ_{i ≤ j} w_ij p_i[a]` for component `a`. -/
def leftComb (a : Nat) (basis : List (List (Nat × Nat × Int))) (w : List Int) : SP :=
  normSP ((basis.zip w).foldr (fun x acc =>
    x.1.foldr (fun t acc' => if t.1 == a ∧ x.2 ≠ 0 then (t.2.1, x.2 * t.2.2) :: acc' else acc') acc) [])

def rowComp (b : Nat) (row : List (Nat × Nat × Int)) : SP :=
  normSP (row.foldr (fun t acc => if t.1 == b then (t.2.1, t.2.2) :: acc else acc) [])

/-- The `k × k` matrix of polynomials `γ[a][b]` of one column (flattened, index `a * k + b`). -/
def colGamma (k : Nat) (basis : List (List (Nat × Nat × Int))) (w : List Int) (rowj : List (Nat × Nat × Int)) :
    List SP :=
  let L := (List.range k).map fun a => leftComb a basis w
  let Rj := (List.range k).map fun b => rowComp b rowj
  L.foldr (fun l acc => Rj.foldr (fun r acc' => mulSP l r :: acc') acc) []

def getSP (l : List SP) (t : Nat) : SP := l.getD t []

def sumCols (k : Nat) (cols : List (List SP)) : List SP :=
  (List.range (k * k)).map fun t => sumSP (cols.map fun c => getSP c t)

/-- The per-column `γ` lists for base and correction weights. -/
def blockCols (grid s2 : Int) (b : GBlock) : List (List SP × List SP) :=
  let recs := ((((List.range b.size).zip b.factor).zip b.basis).zip b.resid).zip b.corr
  recs.map fun x =>
    let j := x.1.1.1.1
    let fj := x.1.1.1.2
    let rowj := x.1.1.2
    let rc := x.1.2
    let cc := x.2
    let w := colWeights grid s2 b.factor fj rc cc j
    (colGamma b.ncomp b.basis w.1 rowj, colGamma b.ncomp b.basis w.2 rowj)

def blockGamma (grid s2 : Int) (b : GBlock) : List SP × List SP :=
  let cols := blockCols grid s2 b
  (sumCols b.ncomp (cols.map Prod.fst), sumCols b.ncomp (cols.map Prod.snd))

/-- Gamma of all blocks with constraint `c`, summed. -/
def conGamma (grid s2 : Int) (k : Nat) (blocks : List GBlock) (c : Nat) : List SP × List SP :=
  let gs := (blocks.filter fun b => b.cid == c).map (blockGamma grid s2)
  ((List.range (k * k)).map fun t => sumSP (gs.map fun g => getSP g.1 t),
   (List.range (k * k)).map fun t => sumSP (gs.map fun g => getSP g.2 t))

def flat (M : List (List SP)) : List SP := M.foldr (· ++ ·) []

/-- `Σ_{a,b} Γ[a][b] M[a][b]`. -/
def pairProd (M : List (List SP)) (g : List SP) : SP :=
  sumSP ((g.zip (flat M)).map fun x => mulSP x.1 x.2)

def projGo : Nat → List (Nat × Int) → SP → List (Nat × Nat × Int) → List (Nat × Int)
  | 0, acc, _, _ => acc
  | _ + 1, acc, [], _ => acc
  | _ + 1, acc, _ :: _, [] => acc
  | f + 1, acc, a :: p, t :: tl =>
    if a.1 < t.1 then projGo f acc p (t :: tl)
    else if t.1 < a.1 then projGo f acc (a :: p) tl
    else projGo f ((t.2.1, t.2.2 * a.2) :: acc) p tl

/-- Signed Reynolds projection onto orbit representatives. -/
def projSP (tbl : List (Nat × Nat × Int)) (p : SP) : SP :=
  normSP (projGo (p.length + tbl.length + 1) [] p tbl)

def eqSP : SP → SP → Bool
  | [], [] => true
  | a :: p, b :: q => a.1 == b.1 && a.2 == b.2 && eqSP p q
  | _, _ => false

/-- The projected total expansion of the blocks (base part, correction part). -/
def totals (cons : List (List (List SP))) (tbl : List (Nat × Nat × Int)) (grid s2 : Int)
    (blocks : List GBlock) : SP × SP :=
  let per := ((List.range cons.length).zip cons).map fun x =>
    let k := x.2.length
    let g := conGamma grid s2 k blocks x.1
    (pairProd x.2 g.1, pairProd x.2 g.2)
  (projSP tbl (sumSP (per.map Prod.fst)), projSP tbl (sumSP (per.map Prod.snd)))

/-- The full identity: after the signed Reynolds projection the correction part equals
`corrDen * (expected - base part)` (the integer form of `eq:fqe-global-overlap-sos`). -/
def identityOK (cons : List (List (List SP))) (tbl : List (Nat × Nat × Int)) (expected : SP)
    (grid s2 cd : Int) (blocks : List GBlock) : Bool :=
  let t := totals cons tbl grid s2 blocks
  eqSP (sumSP [scaleSP cd expected, scaleSP (-cd) t.1, negSP t.2]) []

end FormalResearch.FourQubitEntropy.GOProbe

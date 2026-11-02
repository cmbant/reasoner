import QVCheckImpl.Impl2

/-!
# The QV checker, part 3: pair transforms and the coupled structure of the invariants (K3)

For a pair of spins `(j0, j1)` the matrices `T`, `Tinv` (`T Tinv = δ I`) are the coupling transforms of the diagonal `S_6`-module
`M_{j0} ⊗ M_{j1}`; only `T Tinv = δ I` is used.  For a sector `(A, B)` the coupled bases `V' = T_A V T_B^T`,
`W' = Tinv_A^T W Tinv_B` are expressed in the sparse family `Ŵ_u`, `V̂_u`, `u = (λ, s, t)`, by the coordinate arrays
`Ω`, `Ξ` (`n × n`).
-/
namespace QVCheck

opaque tArr : Array Int := parseInts DataStr.tS
opaque tinvArr : Array Int := parseInts DataStr.tinvS
opaque deltaArr : Array Int := parseInts DataStr.deltaS
opaque omArr : Array Int := parseInts DataStr.omS
opaque xiArr : Array Int := parseInts DataStr.xiS
opaque wcArr : Array Int := parseInts DataStr.wcS
opaque vcArr : Array Int := parseInts DataStr.vcS

def pairIdx (j0 j1 : Nat) : Nat := j0 * 4 + j1
def pairDim (pj : Nat) : Nat := mult (pj / 4) * mult (pj % 4)
@[irreducible] def tOffArr : Array Nat :=
  ((List.range 16).foldl (fun (acc : Array Nat × Nat) pj => (acc.1.push acc.2, acc.2 + pairDim pj * pairDim pj)) (#[], 0)).1
def tOff (pj : Nat) : Nat := tOffArr.getD pj 0
@[inline] def tAt (pj r c : Nat) : Int := gt tArr (tOff pj + r * pairDim pj + c)
@[inline] def tiAt (pj r c : Nat) : Int := gt tinvArr (tOff pj + r * pairDim pj + c)
def delta (pj : Nat) : Int := gt deltaArr pj

/-- `T Tinv = Tinv T = δ I` for all 16 pairs, `δ ≠ 0` -/
def checkT (u : Unit) : Bool :=
  allTo (hide u 16) fun pj => delta pj != 0 && allTo (pairDim pj) fun i => allTo (pairDim pj) fun j =>
    sumTo (pairDim pj) (fun k => tAt pj i k * tiAt pj k j) == (if i == j then delta pj else 0) &&
    sumTo (pairDim pj) (fun k => tiAt pj i k * tAt pj k j) == (if i == j then delta pj else 0)

/-- layouts: `(label, d, g, offset)` of the isotypic blocks of each pair -/
def layoutRaw : Array Int := parseInts DataStr.layoutS

def layouts : Array (Array (Nat × Nat × Nat × Nat)) := Id.run do
  let mut res : Array (Array (Nat × Nat × Nat × Nat)) := #[]
  let mut pos := 0
  for _ in [0:16] do
    let cnt := (gt layoutRaw pos).toNat
    pos := pos + 1
    let mut o := 0
    let mut arr : Array (Nat × Nat × Nat × Nat) := #[]
    for _ in [0:cnt] do
      let l := (gt layoutRaw pos).toNat; let d := (gt layoutRaw (pos + 1)).toNat; let g := (gt layoutRaw (pos + 2)).toNat
      arr := arr.push (l, d, g, o)
      o := o + d * g
      pos := pos + 3
    res := res.push arr
  return res

opaque labDimsArr : Array Nat := DataStr.labelDims.toArray
@[irreducible] def labOffArr : Array Nat :=
  ((List.range 11).foldl (fun (acc : Array Nat × Nat) l => (acc.1.push acc.2, acc.2 + labDimsArr.getD l 0)) (#[], 0)).1
def wc (l x : Nat) : Int := gt wcArr (labOffArr.getD l 0 + x)
def vc (l x : Nat) : Int := gt vcArr (labOffArr.getD l 0 + x)

/-- the family index `u = (λ, s, t)` of a sector -/
structure UInfo where
  lab : Nat
  d : Nat
  gA : Nat
  gB : Nat
  oA : Nat
  oB : Nat
  s : Nat
  t : Nat
deriving Inhabited

/-- the list of `u` for the sector `code`: common labels of the two pair layouts, in the order of the first layout -/
def uList (code : Nat) : Array UInfo := Id.run do
  let la := layouts.getD (pairIdx (spinDigit code 0) (spinDigit code 1)) #[]
  let lb := layouts.getD (pairIdx (spinDigit code 2) (spinDigit code 3)) #[]
  let mut res : Array UInfo := #[]
  for (l, d, gA, oA) in la do
    match lb.find? (fun e => e.1 == l) with
    | none => pure ()
    | some (_, _, gB, oB) =>
      for s in [0:gA] do
        for t in [0:gB] do
          res := res.push { lab := l, d := d, gA := gA, gB := gB, oA := oA, oB := oB, s := s, t := t }
  return res

def uCache : Array (Array UInfo) := (List.range 256).toArray.map uList
def uInfo (code : Nat) : Array UInfo := uCache.getD code #[]

def pA (code : Nat) : Nat := pairIdx (spinDigit code 0) (spinDigit code 1)
def pB (code : Nat) : Nat := pairIdx (spinDigit code 2) (spinDigit code 3)

/-- coupled `V'_b = T_A V_b T_B^T` and `W'_b = Tinv_A^T W_b Tinv_B` (flat `D_A × D_B`) -/
def coupledV (code b : Nat) : Array Int :=
  let pa := pA code; let pb := pB code; let DA := pairDim pa; let DB := pairDim pb
  let M1 := tab (DA * DB) fun idx => sumTo DA fun k => tAt pa (idx / DB) k * vAt code b (k * DB + idx % DB)
  tab (DA * DB) fun idx => sumTo DB fun l => gt M1 (idx / DB * DB + l) * tAt pb (idx % DB) l

def coupledW (code b : Nat) : Array Int :=
  let pa := pA code; let pb := pB code; let DA := pairDim pa; let DB := pairDim pb
  let M1 := tab (DA * DB) fun idx => sumTo DA fun k => tiAt pa k (idx / DB) * wAt code b (k * DB + idx % DB)
  tab (DA * DB) fun idx => sumTo DB fun l => gt M1 (idx / DB * DB + l) * tiAt pb l (idx % DB)

/-- `Ŵ_u[i][j] = Σ_x wc[λ][x] [i = oA + x gA + s ∧ j = oB + x gB + t]` (resp. `V̂_u` with `vc`) -/
def hatEntry (isW : Bool) (code u i j : Nat) : Int :=
  let e := (uInfo code).getD u default
  sumTo e.d fun x =>
    if i == e.oA + x * e.gA + e.s && j == e.oB + x * e.gB + e.t then (if isW then wc e.lab x else vc e.lab x) else 0

/-- `Σ_u c_u Ŵ_u[i][j]` -/
def reconEntry (isW : Bool) (code : Nat) (coef : Array Int) (i j : Nat) : Int :=
  sumTo (uInfo code).size fun u => gt coef u * hatEntry isW code u i j

/-- the index maps of the family `u` stay inside the pair spaces -/
def checkU (u : Unit) : Bool :=
  allTo (hide u 256) fun code => allTo (uInfo code).size fun k =>
    let e := (uInfo code).getD k default
    e.s < e.gA && e.t < e.gB &&
    allTo e.d fun x => e.oA + x * e.gA + e.s < pairDim (pA code) && e.oB + x * e.gB + e.t < pairDim (pB code)

def checkStructure (u : Unit) : Bool :=
  allTo (hide u 256) fun code => allTo (nn code) fun b =>
    (uInfo code).size == nn code &&
    let pa := pA code; let pb := pB code; let DA := pairDim pa; let DB := pairDim pb
    let Vp := coupledV code b; let Wp := coupledW code b
    let om := slice omArr (nnOff code + b * nn code) (nn code)
    let xi := slice xiArr (nnOff code + b * nn code) (nn code)
    allTo (DA * DB) fun idx =>
      DataStr.lc * gt Wp idx == reconEntry true code om (idx / DB) (idx % DB) &&
      DataStr.lc * gt Vp idx == reconEntry false code xi (idx / DB) (idx % DB)

end QVCheck

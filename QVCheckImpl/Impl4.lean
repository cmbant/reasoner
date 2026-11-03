module

public import QVCheckImpl.Impl3
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The QV checker, part 4: the coupled contraction and its accumulation over the blocks (K4)

For a covariant `t = (a, p, q, v)` and a sector `code = (A, B)` the checker computes the integer matrix `Ctil_t[u][u']` of
`Σ_{l01} Σ_{x,y} wc vc Π^A[l01] YR[l01]` and the weighted sum `Σ_t q_t Ctil_t`; then `Ω · (Σ q_t Ctil_t) · Ξ^T = Z · Qtot`.
-/

@[expose] public section

namespace QVCheck

abbrev Letter := Nat × Nat × Nat × Nat

/-- a block of the certificate: `(a, twice the spins, weights, sparse multiplicity vectors)` (the shape of `QVCert.Block`) -/
abbrev BlockD := Nat × List Nat × List Int × List (List (Nat × Int))

/-- spin indices `j/2` of a block -/
def blkSp (b : BlockD) : Array Nat := (b.2.1.map (· / 2)).toArray

/-- digit `q` of the flat multiplicity index `c` of spin tuple `sp` (digit `0` most significant) -/
def muDig (sp : Array Nat) (c q : Nat) : Nat :=
  let m := fun l => mult (sp.getD l 0)
  let st := (List.range 4).foldl (fun acc l => if q < l then acc * m l else acc) 1
  c / st % m q

/-- the letter `(μ_e0, μ_e'0, μ_e1, μ_e'1)` of the pair `(e, e')` on qubits `0, 1` -/
def letter01 (sp : Array Nat) (e e' : Nat × Int) : Letter :=
  (muDig sp e.1 0, muDig sp e'.1 0, muDig sp e.1 1, muDig sp e'.1 1)

/-- the letter on qubits `2, 3` -/
def letter23 (sp : Array Nat) (e e' : Nat × Int) : Letter :=
  (muDig sp e.1 2, muDig sp e'.1 2, muDig sp e.1 3, muDig sp e'.1 3)

/-- all ordered pairs of entries of a sparse vector, in the order `lsum v (fun s => lsum v (fun s' => ..))` -/
def pairsList (v : List (Nat × Int)) : List ((Nat × Int) × (Nat × Int)) :=
  v.flatMap fun e => v.map fun e' => (e, e')

/-- untrusted: distinct elements (the checker only uses that every needed letter is found, see `rowsOk`) -/
def dedup (xs : List Letter) : Array Letter := Id.run do
  let mut seen : Std.HashSet Letter := {}
  let mut out : Array Letter := #[]
  for x in xs do
    if !seen.contains x then
      seen := seen.insert x
      out := out.push x
  return out

def allPairs (b : BlockD) : List ((Nat × Int) × (Nat × Int)) := b.2.2.2.flatMap pairsList

def letters01Of (b : BlockD) : Array Letter := dedup ((allPairs b).map fun p => letter01 (blkSp b) p.1 p.2)
def letters23Of (b : BlockD) : Array Letter := dedup ((allPairs b).map fun p => letter23 (blkSp b) p.1 p.2)

/-- row of a letter in an (untrusted) letter table -/
def rowOf (L : Array Letter) (l : Letter) : Nat := (L.findIdx? (· == l)).getD L.size

/-- the pair data `(row01, row23, coefficient)` of a sparse vector -/
def pairsOf (L01 L23 : Array Letter) (sp : Array Nat) (v : List (Nat × Int)) : Array (Nat × Nat × Int) :=
  ((pairsList v).map fun p =>
    (rowOf L01 (letter01 sp p.1 p.2), rowOf L23 (letter23 sp p.1 p.2), p.1.2 * p.2.2)).toArray

/-- every needed letter is found in the letter tables -/
def rowsOk (b : BlockD) : Bool :=
  (allPairs b).all fun p =>
    rowOf (letters01Of b) (letter01 (blkSp b) p.1 p.2) < (letters01Of b).size &&
    rowOf (letters23Of b) (letter23 (blkSp b) p.1 p.2) < (letters23Of b).size &&
    (letters01Of b).getD (rowOf (letters01Of b) (letter01 (blkSp b) p.1 p.2)) (0, 0, 0, 0) == letter01 (blkSp b) p.1 p.2 &&
    (letters23Of b).getD (rowOf (letters23Of b) (letter23 (blkSp b) p.1 p.2)) (0, 0, 0, 0) == letter23 (blkSp b) p.1 p.2

/-- stage arrays of `tableLetter` -/
def tlQ0 (ai sp0 pj : Nat) (l : Letter) : Array Int :=
  tab (mult (pj / 4) * mult (pj / 4)) fun e => psiAt ai sp0 (pj / 4) l.1 l.2.1 (e / mult (pj / 4)) (e % mult (pj / 4))
def tlQ1 (ai sp1 pj : Nat) (l : Letter) : Array Int :=
  tab (mult (pj % 4) * mult (pj % 4)) fun e => psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 (e / mult (pj % 4)) (e % mult (pj % 4))
def tlS (ai sp1 pj : Nat) (l : Letter) : Array Int :=
  let m0 := mult (pj / 4); let m1 := mult (pj % 4); let D := m0 * m1
  let Q1 := tlQ1 ai sp1 pj l
  tab (m0 * m1 * D) fun e =>
    let c := e % D; let i1 := e / D % m1; let k0 := e / D / m1
    sumTo m1 fun k1 => gt Q1 (i1 * m1 + k1) * tiAt pj (k0 * m1 + k1) c
def tlM1 (ai sp0 sp1 pj : Nat) (l : Letter) : Array Int :=
  let m0 := mult (pj / 4); let m1 := mult (pj % 4); let D := m0 * m1
  let Q0 := tlQ0 ai sp0 pj l
  let S := tlS ai sp1 pj l
  tab (D * D) fun e =>
    let c := e % D; let i1 := e / D % m1; let i0 := e / D / m1
    sumTo m0 fun k0 => gt Q0 (i0 * m0 + k0) * gt S ((k0 * m1 + i1) * D + c)

/-- the table entry array of one letter: `Π[l] = T (Q0 ⊗ Q1) Tinv` (flat `D × D`) for source spins `(sp0, sp1)` and target pair
index `pj` -/
def tableLetter (ai sp0 sp1 : Nat) (pj : Nat) (l : Letter) : Array Int :=
  let D := mult (pj / 4) * mult (pj % 4)
  let M1 := tlM1 ai sp0 sp1 pj l
  tab (D * D) fun e => sumTo D fun k => tAt pj (e / D) k * gt M1 (k * D + e % D)

/-- the tables of all letters -/
def mkTable (ai sp0 sp1 : Nat) (pj : Nat) (letters : Array Letter) : Array (Array Int) :=
  letters.map (tableLetter ai sp0 sp1 pj)

/-- the contribution `Σ_{x,y} wc vc Π^A Π^B` of one pair of letters (tables `T01`, `T23`) to the entry `(u, u')` of `Ctil` -/
def ctPair (code : Nat) (T01 T23 : Array Int) (u u' : UInfo) : Int :=
  let DA := pairDim (pA code); let DB := pairDim (pB code)
  sumTo u.d fun x => sumTo u'.d fun y =>
    wc u.lab x * vc u'.lab y *
      gt T01 ((u.oA + x * u.gA + u.s) * DA + (u'.oA + y * u'.gA + u'.s)) *
      gt T23 ((u.oB + x * u.gB + u.t) * DB + (u'.oB + y * u'.gB + u'.t))

/-- `Ctil_t` (flat `n × n`) for one term and sector, given the tables and the pair data -/
def ctil (code : Nat) (T01 T23 : Array (Array Int)) (pairs : Array (Nat × Nat × Int)) : Array Int :=
  let us := uInfo code; let n := us.size
  tab (n * n) fun e =>
    let u := us.getD (e / n) default; let u' := us.getD (e % n) default
    sumTo pairs.size fun pi =>
      let r := pairs.getD pi (0, 0, 0)
      r.2.2 * ctPair code (T01.getD r.1 #[]) (T23.getD r.2.1 #[]) u u'

/-! ### Accumulation over the blocks -/

/-- add `q • x` into the accumulator of sector `code` (all arrays have size `n²`) -/
def accAdd (acc : Array (Array Int)) (code : Nat) (q : Int) (x : Array Int) : Array (Array Int) :=
  acc.modify code fun a => tab a.size (fun i => gt a i + q * gt x i)

/-- zero accumulators -/
def accZero : Array (Array Int) := (List.range 256).toArray.map fun code => Array.replicate (nn code * nn code) 0

/-- the pair data of the terms of a block -/
def blockPairs (b : BlockD) : Array (Array (Nat × Nat × Int)) :=
  let L01 := letters01Of b; let L23 := letters23Of b; let sp := blkSp b
  (List.range b.2.2.1.length).toArray.map fun ti => pairsOf L01 L23 sp (b.2.2.2.getD ti [])

/-- the tables of a block: `01` side for source spins `(0,1)` and `23` side for source spins `(2,3)`, by target pair -/
def blockTab01 (b : BlockD) (pj : Nat) : Array (Array Int) :=
  mkTable (b.1 - 3) ((blkSp b).getD 0 0) ((blkSp b).getD 1 0) pj (letters01Of b)
def blockTab23 (b : BlockD) (pj : Nat) : Array (Array Int) :=
  mkTable (b.1 - 3) ((blkSp b).getD 2 0) ((blkSp b).getD 3 0) pj (letters23Of b)

/-- one sector `code` for target pair `pjA` with the `01` tables `T01` -/
def blockStep1 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : Nat) (T01 : Array (Array Int)) (code : Nat) (acc : Array (Array Int)) : Array (Array Int) :=
  if nn code > 0 && pA code == pjA then
    (List.range b.2.2.1.length).foldl (fun acc ti =>
      accAdd acc code (b.2.2.1.getD ti 0) (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[]))) acc
  else acc

/-- all sectors for the target pair `pjA` -/
def blockStep2 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : Nat) (acc : Array (Array Int)) : Array (Array Int) :=
  let T01 := blockTab01 b pjA
  (List.range 256).foldl (fun acc code => blockStep1 b pairs tabs23 pjA T01 code acc) acc

/-- add the contribution of one block to the accumulators -/
def runBlock (b : BlockD) (acc : Array (Array Int)) : Array (Array Int) :=
  let pairs := blockPairs b
  let tabs23 : Array (Array (Array Int)) := (List.range 16).toArray.map (blockTab23 b)
  (List.range 16).foldl (fun acc pjA => blockStep2 b pairs tabs23 pjA acc) acc

/-- all blocks -/
def runAll (blocks : List BlockD) : Array (Array Int) := blocks.foldl (fun acc b => runBlock b acc) accZero

end QVCheck

import QVCheckImpl.Impl1

/-!
# The QV checker, part 2: `S_6` representations, characters, sector dimensions, invariant bases (K2)
-/
namespace QVCheck

/-- Coset representatives `[k-1, k-2, ..., k-l]`. -/
def cosetRep (k l : Nat) : List Nat := (List.range l).map fun t => k - 1 - t

/-- The 720 words `c_1 c_2 c_3 c_4 c_5`, `c_k` a coset representative of length `0..k`. -/
def words : List (List Nat) :=
  (List.range 2).flatMap fun l1 => (List.range 3).flatMap fun l2 => (List.range 4).flatMap fun l3 =>
    (List.range 5).flatMap fun l4 => (List.range 6).map fun l5 =>
      cosetRep 1 l1 ++ cosetRep 2 l2 ++ cosetRep 3 l3 ++ cosetRep 4 l4 ++ cosetRep 5 l5

/-- square matrix product of flat `m × m` arrays -/
def mmul (m : Nat) (A B : Array Int) : Array Int :=
  tab (m * m) fun idx => sumTo m fun k => gt A (idx / m * m + k) * gt B (k * m + idx % m)

def idMat (m : Nat) : Array Int := tab (m * m) fun idx => if idx / m == idx % m then 1 else 0

def genMat (j i : Nat) : Array Int := tab (mult j * mult j) fun idx => gt rhoArr (rhoOff j i + idx)

/-- `ρ_j(l) = ρ_j(s_{l_0}) ρ_j(s_{l_1}) ⋯` -/
def repProd (j : Nat) (l : List Nat) : Array Int :=
  l.foldl (fun acc i => mmul (mult j) acc (genMat j i)) (idMat (mult j))

def traceMat (m : Nat) (A : Array Int) : Int := sumTo m fun i => gt A (i * m + i)

/-- characters: `charArr[j * 720 + w] = tr ρ_j(words[w])` -/
@[irreducible] def charArr : Array Int :=
  tab 2880 fun idx => traceMat (mult (idx / 720)) (repProd (idx / 720) (words.getD (idx % 720) []))

def spinDigit (code q : Nat) : Nat := code / (4 ^ (3 - q)) % 4

/-- `Σ_g ∏_q χ_{p_q}(g)` for the sector code `code` -/
def charSum (code : Nat) : Int :=
  sumTo 720 fun w => (List.range 4).foldl (fun acc q => acc * gt charArr (spinDigit code q * 720 + w)) 1

/-- `n_p = (1/720) Σ_g ∏_q χ_{p_q}(g)` -/
@[irreducible] def nnArr : Array Nat := (List.range 256).toArray.map fun code => (charSum code / 720).toNat

def checkChars (u : Unit) : Bool :=
  allTo (hide u 256) fun code => charSum code == 720 * ((nnArr.getD code 0 : Nat) : Int)

def sdim (code : Nat) : Nat := mult (spinDigit code 0) * mult (spinDigit code 1) * mult (spinDigit code 2) * mult (spinDigit code 3)
def nn (code : Nat) : Nat := nnArr.getD code 0

/-- offsets of the sector bases in `vS`, `wS` (prefix sums of `n * D`) -/
@[irreducible] def vOffArr : Array Nat :=
  ((List.range 256).foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + nn c * sdim c)) (#[], 0)).1
/-- offsets in the per-sector `n` / `n²` arrays -/
@[irreducible] def nOffArr : Array Nat :=
  ((List.range 256).foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + nn c)) (#[], 0)).1
@[irreducible] def nnOffArr : Array Nat :=
  ((List.range 256).foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + nn c * nn c)) (#[], 0)).1
/-- rank of a sector among those with `n > 0` -/
@[irreducible] def rankArr : Array Nat :=
  ((List.range 256).foldl (fun (acc : Array Nat × Nat) c => (acc.1.push acc.2, acc.2 + (if nn c > 0 then 1 else 0))) (#[], 0)).1
def secRank (code : Nat) : Nat := rankArr.getD code 0
def vOff (code : Nat) : Nat := vOffArr.getD code 0
def nOff (code : Nat) : Nat := nOffArr.getD code 0
def nnOff (code : Nat) : Nat := nnOffArr.getD code 0

opaque vArr : Array Int := parseInts DataStr.vS
opaque wArr : Array Int := parseInts DataStr.wS
opaque pivVArr : Array Int := parseInts DataStr.pivVS
opaque pivWArr : Array Int := parseInts DataStr.pivWS
opaque uVArr : Array Int := parseInts DataStr.uVS
opaque uWArr : Array Int := parseInts DataStr.uWS
opaque cVArr : Array Int := parseInts DataStr.cVS
opaque cWArr : Array Int := parseInts DataStr.cWS

/-- `b`-th basis vector of sector `code`, entry `x` -/
@[inline] def vAt (code b x : Nat) : Int := gt vArr (vOff code + b * sdim code + x)
@[inline] def wAt (code b x : Nat) : Int := gt wArr (vOff code + b * sdim code + x)

/-- one mode product of a flat tensor: `out = (1 ⊗ M ⊗ 1) X` (or `M^T`) with mode of size `m` and stride `s` -/
def modeProd (M : Array Int) (m s : Nat) (tr : Bool) (X : Array Int) : Array Int :=
  tab X.size fun idx =>
    let r := idx / s % m
    let base := idx / (s * m) * (s * m) + idx % s
    sumTo m fun k => (if tr then gt M (k * m + r) else gt M (r * m + k)) * gt X (base + k * s)

def stride (code q : Nat) : Nat :=
  (List.range 4).foldl (fun acc l => if q < l then acc * mult (spinDigit code l) else acc) 1

/-- `(⊗_q ρ_{p_q}(s_i)) X` -/
def kronGen (code i : Nat) (tr : Bool) (X : Array Int) : Array Int :=
  (List.range 4).foldl (fun acc q => modeProd (genMat (spinDigit code q) i) (mult (spinDigit code q)) (stride code q) tr acc) X

def slice (A : Array Int) (o n : Nat) : Array Int := tab n fun i => gt A (o + i)

/-- invariance of `V_b`, `W_b` under the five generators -/
def checkInvariant (u : Unit) : Bool :=
  allTo (hide u 256) fun code => allTo (nn code) fun b => allTo 5 fun i =>
    let v := slice vArr (vOff code + b * sdim code) (sdim code)
    let w := slice wArr (vOff code + b * sdim code) (sdim code)
    kronGen code i false v == v && kronGen code i true w == w

/-- left-inverse certificates for the basis array `X` with pivots `piv`: `U Vpiv = c I`, `c ≠ 0`, pivots in range -/
def pivCheck (X piv U cs : Array Int) : Bool :=
  allTo 256 fun code => allTo (nn code) fun i => allTo (nn code) fun b =>
    gt cs (secRank code) != 0 &&
    allTo (nn code) (fun r => 0 ≤ gt piv (nOff code + r) && (gt piv (nOff code + r)).toNat < sdim code) &&
    sumTo (nn code) (fun r =>
      gt U (nnOff code + i * nn code + r) * gt X (vOff code + b * sdim code + (gt piv (nOff code + r)).toNat)) ==
      (if i == b then gt cs (secRank code) else 0)

def checkPivots (isV : Bool) : Bool :=
  if isV then pivCheck vArr pivVArr uVArr cVArr else pivCheck wArr pivWArr uWArr cWArr

end QVCheck

import FormalResearch.FourQubitEntropy.GOProbe.GOConst
import FormalResearch.FourQubitEntropy.GOProbe.GOData

/-! Kernel timing of the Gram weights `H + Δ` of block 0 with Kronecker-packed dot products: 17.4 s, 1.95 GB
(the naive `dot` was killed at 10 GB after 107 s). -/
namespace FormalResearch.FourQubitEntropy.GOProbe
set_option maxRecDepth 100000

/-! Kronecker-packed dot products: `P_i = Σ_k (a_k + off) B^k`, `Q_j = Σ_k (b_{r-1-k} + off) B^k`;
the coefficient of `B^(r-1)` in `P_i Q_j` is `Σ_k (a_k+off)(b_k+off)`. -/
def wB : Nat := 128
def offN : Nat := 2 ^ 52
def packF : List Int → Nat
  | [] => 0
  | x :: t => ((x + (offN : Int)).toNat) + 2 ^ wB * packF t
def sumI : List Int → Int
  | [] => 0
  | x :: t => x + sumI t

def hvalP (grid s2 : Int) (r : Nat) (p q : Nat) (si sj : Int) : Int :=
  let c : Nat := (p * q) / 2 ^ (wB * (r - 1)) % 2 ^ wB
  let d : Int := (c : Int) - (offN : Int) * (si + sj) - (r : Int) * (offN : Int) * (offN : Int)
  (grid * d + s2 / 2) / s2

def wsumP (b : GBlock) (s2 : Int) : Int :=
  let r := (b.factor.headD []).length
  let P := b.factor.map packF
  let Q := b.factor.map fun f => packF f.reverse
  let S := b.factor.map sumI
  let cols := (((List.range b.size).zip Q).zip S).zip b.resid
  cols.foldl (fun acc x =>
    let j := x.1.1.1
    let qj := x.1.1.2
    let sj := x.1.2
    let rc := x.2
    acc + (((P.zip S).zip rc).foldl (fun a y =>
      a + (hvalP (gridC : Int) s2 r y.1.1 qj y.1.2 sj + y.2) * (if (j = j) then 1 else 1)) 0)) 0

def s2 : Int := (2 : Int) ^ (2 * factorBits)
-- plain sum of (H + Δ) over the upper triangle, unweighted (diagonal and off-diagonal both once)
def wsumRef (b : GBlock) : Int :=
  ((((List.range b.size).zip b.factor).zip b.resid).foldl (fun a x =>
      a + ((b.factor.zip x.2).foldl (fun a2 y => a2 + hval (gridC : Int) s2 y.1 x.1.2 + y.2) 0)) 0)

theorem kp : (dataBlocks.map fun b => wsumP b s2) = [4513827450570645] := by decide +kernel
end FormalResearch.FourQubitEntropy.GOProbe

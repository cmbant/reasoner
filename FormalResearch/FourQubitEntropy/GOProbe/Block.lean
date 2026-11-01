import FormalResearch.FourQubitEntropy.GOProbe.Poly

/-!
# GO certificate: block data and the reflective checker (definitions, no Mathlib)

A block is a Gram matrix `G` positive semidefinite by the compact integer test of
`eq:fqe-compact-gram-test`, a polynomial vector basis `p_i = ∑ atoms` and a constraint matrix `M_c`
(`cons`).  The checker computes the polynomial `U = ∑_B ∑_{i,j} (W_ij) p_iᵀ M_{c(B)} p_j` (with the integer
weights `W = grid·G` split into the base part `H + Δ` and the sparse correction `C/cd`), symmetrises it over
the coordinate maps `acts` and compares with `|acts|·cd·lit`.  All lookups use `getD` with default `0`, so
that the semantics is defined for arbitrary data (soundness needs no shape assumptions).
Soundness: `BlockSound.lean`, `Final.lean`.
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

def corrAt (c : List (Nat × Int)) (i : Nat) : Int :=
  match c.find? (fun t => t.1 == i) with
  | some t => t.2
  | none => 0

def dot : List Int → List Int → Int
  | a :: p, b :: q => a * b + dot p q
  | _, _ => 0

/-- `⌊(grid ⟨F_i, F_j⟩ + s2/2) / s2⌋` (the rounded Gram entry `H`). -/
def hval (grid s2 : Int) (fi fj : List Int) : Int := (grid * dot fi fj + s2 / 2) / s2

/-- One Gram block. `basis i` lists the atoms `(component, packed monomial, coefficient)` of the polynomial
vector entry `p_i`; `factor` is the compact factor `A`, `resid` the columns `Δ` (column `j` has `j+1` entries,
the upper triangle) and `corr` the sparse columns `C`. -/
structure GBlock where
  cid : Nat
  basis : List (List (Nat × Nat × Int))
  factor : List (List Int)
  resid : List (List Int)
  corr : List (List (Nat × Int))

namespace GBlock

def m (b : GBlock) : Nat := b.basis.length

/-- Symmetric completion of the upper triangle `Δ`. -/
def Rs (b : GBlock) (i j : Nat) : Int :=
  if i ≤ j then (b.resid.getD j []).getD i 0 else (b.resid.getD i []).getD j 0

/-- Symmetric completion of the sparse corrections `C`. -/
def Cs (b : GBlock) (i j : Nat) : Int :=
  if i ≤ j then corrAt (b.corr.getD j []) i else corrAt (b.corr.getD i []) j

/-- Base weight `H_ij + Δ_ij`. -/
def Wb (grid s2 : Int) (b : GBlock) (i j : Nat) : Int :=
  hval grid s2 (b.factor.getD i []) (b.factor.getD j []) + b.Rs i j

/-- Correction weight `C_ij` (the true weight is `Wb + Wc / cd`). -/
def Wc (b : GBlock) (i j : Nat) : Int := b.Cs i j

/-- `D = cd Δ + C`. -/
def Dm (cd : Int) (b : GBlock) (i j : Nat) : Int := cd * b.Rs i j + b.Cs i j

/-- The integer diagonal-dominance test `m·cd < 2 (D_ii − ∑_{j≠i} |D_ij|)`. -/
def gramOK (cd : Int) (b : GBlock) : Bool :=
  (List.range b.m).all fun i =>
    decide ((b.m : Int) * cd < 2 * (b.Dm cd i i -
      ((List.range b.m).map fun j => if i = j then (0 : Int) else ((b.Dm cd i j).natAbs : Int)).sum))

/-- All basis atoms have total degree `≤ d`. -/
def atomsDg (d : Nat) (b : GBlock) : Bool :=
  b.basis.all fun row => row.all fun t => decide (dsum t.2.1 ≤ d)

end GBlock

/-! ### The polynomial `U` -/

def rowComp (c : Nat) (row : List (Nat × Nat × Int)) : SP :=
  normSP (row.filterMap fun t => if t.1 == c then some (t.2.1, t.2.2) else none)

/-- `pre i a = rowComp a (basis i)`. -/
def preOf (k : Nat) (bas : List (List (Nat × Nat × Int))) : List (List SP) :=
  bas.map fun row => (List.range k).map fun a => rowComp a row

def entry (l : List (List SP)) (i a : Nat) : SP := (l.getD i []).getD a []

/-- `L_j[a] = ∑_i W_ij p_i[a]`. -/
def lcomb (W : Nat → Nat → Int) (m : Nat) (pre : List (List SP)) (j a : Nat) : SP :=
  sumSP ((List.range m).map fun i => scaleSP (W i j) (entry pre i a))

/-- The `k × k` matrix of polynomials `γ[a][c] = ∑_j L_j[a] p_j[c]` of one block. -/
def blockSlots (W : Nat → Nat → Int) (k : Nat) (b : GBlock) : List (List SP) :=
  let pre := preOf k b.basis
  let Ls := (List.range b.m).map fun j => (List.range k).map fun a => lcomb W b.m pre j a
  (List.range k).map fun a => (List.range k).map fun c =>
    sumSP ((List.range b.m).map fun j => mulSP (entry Ls j a) (entry pre j c))

/-- Sum of the slots of the blocks of one constraint. -/
def conSlots (wf : GBlock → Nat → Nat → Int) (k : Nat) (bs : List GBlock) : List (List SP) :=
  let sl := bs.map fun b => blockSlots (wf b) k b
  (List.range k).map fun a => (List.range k).map fun c => sumSP (sl.map fun s => entry s a c)

/-- `∑_{a,c} G[a][c] M[a][c]`. -/
def pairProd (k : Nat) (M G : List (List SP)) : SP :=
  sumSP ((List.range k).map fun a => sumSP ((List.range k).map fun c => mulSP (entry G a c) (entry M a c)))

def uPart (wf : GBlock → Nat → Nat → Int) (cons : List (List (List SP))) (blocks : List GBlock) : SP :=
  sumSP ((List.range cons.length).map fun c =>
    let M := cons.getD c []
    pairProd M.length M (conSlots wf M.length (blocks.filter fun b => b.cid == c)))

/-- `U = cd · U_base + U_corr`. -/
def uTotal (grid s2 cd : Int) (cons : List (List (List SP))) (blocks : List GBlock) : SP :=
  sumSP [scaleSP cd (uPart (fun b => b.Wb grid s2) cons blocks), uPart (fun b => b.Wc) cons blocks]

/-! ### The check -/

def consDg (d : Nat) (cons : List (List (List SP))) : Bool :=
  cons.all fun M => M.all fun row => row.all fun p => dgOK d p

/-- The complete reflective check. -/
def check (cons : List (List (List SP))) (acts : List (List Nat × List Int)) (lit : SP)
    (grid s2 cd : Int) (blocks : List GBlock) : Bool :=
  decide (0 < cd) && decide (0 < grid) && decide (0 < s2) && (s2 % 2 == 0) && decide (0 < acts.length) &&
  acts.all (fun g => (List.range 19).all fun i => decide (g.1.getD i 0 < 19)) &&
  consDg 16 cons && blocks.all (GBlock.atomsDg 16) && blocks.all (GBlock.gramOK cd) &&
  eqSP (sumSP [sumSP (acts.map fun g => actSP g (uTotal grid s2 cd cons blocks)),
               scaleSP (-((acts.length : Int) * cd)) lit]) []

end FormalResearch.FourQubitEntropy.GOProbe

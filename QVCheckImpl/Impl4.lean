import QVCheckImpl.Impl3
import Std.Data.HashMap

/-!
# The QV checker, part 4: the coupled contraction (K4)

For a covariant `t = (a, p, q, v)` and a sector `code = (A, B)` the checker computes the integer matrix `Ctil_t[u][u']` of
`Σ_{l01} Σ_{x,y} wc vc Π^A[l01] YR[l01]` and the weighted sum `Σ_t q_t Ctil_t`; then `Ω · (Σ q_t Ctil_t) · Ξ^T = Z · Qtot`.
-/
namespace QVCheck

/-- a block of the certificate: `(a, spin indices, weights, flat sparse vectors)` -/
abbrev BlockD := Nat × List Nat × List Int × List (List Int)

/-- digit `q` of the flat multiplicity index `c` of spin tuple `sp` -/
def muDig (sp : Array Nat) (c q : Nat) : Nat :=
  let m := fun l => mult (sp.getD l 0)
  let st := (List.range 4).foldl (fun acc l => if q < l then acc * m l else acc) 1
  c / st % m q

/-- one covariant: support digits and coefficients -/
structure TermD where
  a : Nat
  sp : Array Nat
  q : Int
  mu : Array (Array Nat)
  co : Array Int
deriving Inhabited

def termsOf (b : BlockD) : Array TermD :=
  let (a, sp, ws, vs) := b
  let spA := sp.toArray
  (ws.zip vs).toArray.map fun (w, v) =>
    let ent := (List.range (v.length / 2)).toArray
    { a := a, sp := spA, q := w,
      mu := ent.map fun e => (List.range 4).toArray.map fun q => muDig spA (v.getD (2 * e) 0).toNat q,
      co := ent.map fun e => v.getD (2 * e + 1) 0 }

/-- letter code `((μ_i0 m0 + μ_j0) m1 + μ_i1) m1 + μ_j1` of the pair `(i, j)` on qubits `q0, q1` -/
def letterCode (sp mu_i mu_j : Array Nat) (q0 q1 : Nat) : Nat :=
  ((mu_i.getD q0 0 * mult (sp.getD q0 0) + mu_j.getD q0 0) * mult (sp.getD q1 0) + mu_i.getD q1 0) * mult (sp.getD q1 0) + mu_j.getD q1 0

def decodeLetter (sp : Array Nat) (q0 q1 : Nat) (c : Nat) : Nat × Nat × Nat × Nat :=
  let m1 := mult (sp.getD q1 0); let m0 := mult (sp.getD q0 0)
  let mj1 := c % m1; let c := c / m1
  let mi1 := c % m1; let c := c / m1
  let mj0 := c % m0; let c := c / m0
  (c, mj0, mi1, mj1)

/-- the table `Π[l] = T (Q0 ⊗ Q1) Tinv` (flat `L × D²`) for source spins `(sp0, sp1)`, target pair index `pj` -/
def mkTable (ai sp0 sp1 : Nat) (pj : Nat) (letters : Array (Nat × Nat × Nat × Nat)) : Array Int := Id.run do
  let tp0 := pj / 4; let tp1 := pj % 4
  let m0 := mult tp0; let m1 := mult tp1; let D := m0 * m1
  let mut out : Array Int := Array.mkEmpty (letters.size * D * D)
  for (u0, u0', u1, u1') in letters do
    let Q0 := tab (m0 * m0) fun e => psiAt ai sp0 tp0 u0 u0' (e / m0) (e % m0)
    let Q1 := tab (m1 * m1) fun e => psiAt ai sp1 tp1 u1 u1' (e / m1) (e % m1)
    let S := tab (m0 * m1 * D) fun e =>
      let c := e % D; let i1 := e / D % m1; let k0 := e / D / m1
      sumTo m1 fun k1 => gt Q1 (i1 * m1 + k1) * tiAt pj (k0 * m1 + k1) c
    let M1 := tab (D * D) fun e =>
      let c := e % D; let i1 := e / D % m1; let i0 := e / D / m1
      sumTo m0 fun k0 => gt Q0 (i0 * m0 + k0) * gt S ((k0 * m1 + i1) * D + c)
    let P := tab (D * D) fun e => sumTo D fun k => tAt pj (e / D) k * gt M1 (k * D + e % D)
    out := out ++ P
  return out

/-- the pair data of a term: groups by `l01` row; each group = (row in the 01 table, array of (row in the 23 table, coefficient)) -/
structure Prep where
  letters01 : Array (Nat × Nat × Nat × Nat)
  letters23 : Array (Nat × Nat × Nat × Nat)
  /-- per term: groups -/
  groups : Array (Array (Nat × Array (Nat × Int)))

def prepare (ts : Array TermD) : Prep := Id.run do
  let t0 := ts.getD 0 { a := 0, sp := #[], q := 0, mu := #[], co := #[] }
  let sp := t0.sp
  let mut h01 : Std.HashMap Nat Nat := {}
  let mut h23 : Std.HashMap Nat Nat := {}
  let mut l01 : Array Nat := #[]
  let mut l23 : Array Nat := #[]
  let mut groups : Array (Array (Nat × Array (Nat × Int))) := #[]
  for t in ts do
    let n := t.co.size
    let mut gm : Std.HashMap Nat Nat := {}   -- row01 -> index in grp
    let mut grp : Array (Nat × Array (Nat × Int)) := #[]
    for i in [0:n] do
      for j in [0:n] do
        let c01 := letterCode sp (t.mu.getD i #[]) (t.mu.getD j #[]) 0 1
        let c23 := letterCode sp (t.mu.getD i #[]) (t.mu.getD j #[]) 2 3
        let r01 := (h01[c01]?).getD l01.size
        if h01[c01]?.isNone then
          h01 := h01.insert c01 l01.size
          l01 := l01.push c01
        let r23 := (h23[c23]?).getD l23.size
        if h23[c23]?.isNone then
          h23 := h23.insert c23 l23.size
          l23 := l23.push c23
        let cc := t.co.getD i 0 * t.co.getD j 0
        match gm[r01]? with
        | some g => grp := grp.modify g fun (r, arr) => (r, arr.push (r23, cc))
        | none => gm := gm.insert r01 grp.size; grp := grp.push (r01, #[(r23, cc)])
    groups := groups.push grp
  return { letters01 := l01.map (decodeLetter sp 0 1), letters23 := l23.map (decodeLetter sp 2 3), groups := groups }

/-- `Ctil_t` (flat `n × n`) for one term and sector, given the tables -/
def ctil (code : Nat) (T01 T23 : Array Int) (grp : Array (Nat × Array (Nat × Int))) : Array Int :=
  let DA := pairDim (pA code); let DB := pairDim (pB code)
  let us := uInfo code; let n := us.size
  let YRs : Array (Array Int) := grp.map fun (_, prs) =>
    tab (DB * DB) fun e => prs.foldl (fun acc (r23, c) => acc + c * gt T23 (r23 * DB * DB + e)) 0
  tab (n * n) fun e =>
    let u := us.getD (e / n) default; let u' := us.getD (e % n) default
    (List.range grp.size).foldl (fun acc g =>
      let r01 := (grp.getD g (0, #[])).1
      let YR := YRs.getD g #[]
      acc + sumTo u.d fun x => sumTo u'.d fun y =>
        wc u.lab x * vc u'.lab y *
          gt T01 (r01 * DA * DA + (u.oA + x * u.gA + u.s) * DA + (u'.oA + y * u'.gA + u'.s)) *
          gt YR ((u.oB + x * u.gB + u.t) * DB + (u'.oB + y * u'.gB + u'.t))) 0

end QVCheck

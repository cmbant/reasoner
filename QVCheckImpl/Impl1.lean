module

public import QVCheckImpl.Basic
public import QVCheckImpl.DataStr

/-!
# The QV checker, part 1: constants, `C`, the representations of `S_6`, block-form checks (K0, K1)

Spins are indexed by `j/2 ∈ {0,1,2,3}`; `mult = (5, 9, 5, 1)`; the row of `C` for `(j, k, μ)` is `off j + k * mult j + μ`.
-/

@[expose] public section

namespace QVCheck

def mult (j : Nat) : Nat := if j == 0 then 5 else if j == 1 then 9 else if j == 2 then 5 else if j == 3 then 1 else 0
def off (j : Nat) : Nat := if j == 0 then 0 else if j == 1 then 5 else if j == 2 then 32 else 57
/-- spin index of a row of `C` -/
def rowSpin (r : Nat) : Nat := if r < 5 then 0 else if r < 32 then 1 else if r < 57 then 2 else 3
/-- multiplicity index of a row of `C` -/
def rowMu (r : Nat) : Nat := (r - off (rowSpin r)) % mult (rowSpin r)

opaque cArr : Array Int := parseInts DataStr.cS
opaque cinvArr : Array Int := parseInts DataStr.cinvS
opaque rhoArr : Array Int := parseInts DataStr.rhoS
opaque psiArr : Array Int := parseInts DataStr.psiS

/-- `rho_j(s_i)` starts at `rhoOff j i` in `rhoArr`. -/
@[irreducible] def rhoOffArr : Array Nat :=
  ((List.range 20).foldl (fun (acc : Array Nat × Nat) t => (acc.1.push acc.2, acc.2 + mult (t / 5) * mult (t / 5))) (#[], 0)).1
def rhoOff (j i : Nat) : Nat := rhoOffArr.getD (j * 5 + i) 0

def rhoAt (j i a b : Nat) : Int := gt rhoArr (rhoOff j i + a * mult j + b)

/-- exchange of copies `i`, `i+1` on a basis index (copy `t` is bit `5 - t`) -/
def swapIdx (i b : Nat) : Nat :=
  let x := (b >>> (5 - i)) &&& 1
  let y := (b >>> (4 - i)) &&& 1
  (b ^^^ ((x ^^^ y) <<< (5 - i))) ^^^ ((x ^^^ y) <<< (4 - i))

/-- `C Pi_{s_i} = Blk(rho(s_i)) C` -/
def checkSlots (u : Unit) : Bool :=
  allTo (hide u 5) fun i => allTo 64 fun r => allTo 64 fun c =>
    gt cArr (r * 64 + swapIdx i c) ==
      sumTo (mult (rowSpin r)) (fun m' => rhoAt (rowSpin r) i (rowMu r) m' * gt cArr ((r - rowMu r + m') * 64 + c))

/-- `C * Cinv = cDen * 1` and `Cinv * C = cDen * 1` -/
def checkInv (u : Unit) : Bool :=
  DataStr.cDen != 0 && allTo (hide u 64) fun i => allTo 64 fun j =>
    sumTo 64 (fun k => gt cArr (i * 64 + k) * gt cinvArr (k * 64 + j)) == (if i == j then DataStr.cDen else 0) &&
    sumTo 64 (fun k => gt cinvArr (i * 64 + k) * gt cArr (k * 64 + j)) == (if i == j then DataStr.cDen else 0)

/-- binomial coefficients -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => choose n k + choose n (k+1)

/-- weight `ω_{j,k}` -/
def omegaW (j k : Nat) : Int :=
  let l := (List.range (2 * j + 1)).foldl (fun acc r => Nat.lcm acc (choose (2 * j) r)) 1
  (l / choose (2 * j) k : Nat)
@[irreducible] def omegaArr : Array Int := tab 28 fun t => omegaW (t / 7) (t % 7)
def omegaT (j k : Nat) : Int := gt omegaArr (j * 7 + k)

def psiSize (j jp : Nat) : Nat := mult j * mult j * mult jp * mult jp
@[irreducible] def psiOffArr : Array Nat :=
  ((List.range 32).foldl (fun (acc : Array Nat × Nat) t => (acc.1.push acc.2, acc.2 + psiSize ((t % 16) / 4) (t % 4))) (#[], 0)).1
def psiOff (ai j jp : Nat) : Nat := psiOffArr.getD (ai * 16 + j * 4 + jp) 0
def psiAt (ai j jp mu mup nu nup : Nat) : Int :=
  gt psiArr (psiOff ai j jp + ((mu * mult j + mup) * mult jp + nu) * mult jp + nup)

/-- `τ_a` entry: `τ_a(E)[β][α] = ± E[mix(β, ᾱ)][mix(α, β̄)]` -/
def mixIdx (a u v : Nat) : Nat := (u >>> (6 - a)) <<< (6 - a) ||| (v &&& ((1 <<< (6 - a)) - 1))
def popPar (x : Nat) : Nat := (List.range 6).foldl (fun acc t => acc + ((x >>> t) &&& 1)) 0 % 2

def tauMat (a : Nat) (E : Array Int) : Array Int :=
  tab 4096 fun idx =>
    let β := idx / 64; let α := idx % 64
    let lo := (1 <<< (6 - a)) - 1
    let s := popPar (α &&& lo) + popPar (β &&& lo)
    (if s % 2 == 0 then 1 else -1) * gt E (mixIdx a β (63 - α) * 64 + mixIdx a α (63 - β))

def eMat (j mu mup : Nat) : Array Int :=
  tab 4096 fun idx =>
    sumTo (2 * j + 1) fun k => omegaT j k * gt cArr ((off j + k * mult j + mu) * 64 + idx / 64) *
      gt cArr ((off j + k * mult j + mup) * 64 + idx % 64)

/-- `C τ_a(E^j_{μμ'}) = Blk(Ψ^{(a)}_{j,·}[μ][μ']) C` for one `(a, j, μ, μ')` -/
def checkPsiOne (ai j mu mup : Nat) : Bool :=
  let tE := tauMat (3 + ai) (eMat j mu mup)
  allTo 64 fun r => allTo 64 fun c =>
    sumTo 64 (fun w => gt cArr (r * 64 + w) * gt tE (w * 64 + c)) ==
      sumTo (mult (rowSpin r)) (fun nup => psiAt ai j (rowSpin r) mu mup (rowMu r) nup *
        gt cArr ((r - rowMu r + nup) * 64 + c))

def checkPsi (u : Unit) : Bool :=
  allTo (hide u 2) fun ai => allTo 4 fun j => allTo (mult j) fun mu => allTo (mult j) fun mup => checkPsiOne ai j mu mup

end QVCheck

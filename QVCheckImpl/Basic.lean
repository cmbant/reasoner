/-!
# Loop combinators and parsing for the QV checker (core Lean only)
-/
namespace QVCheck

/-- Identity that the compiler cannot see through: used to make top-level checks depend on their `Unit` argument, so that
they are not evaluated at module initialisation (nullary definitions and closed terms are initialised eagerly). -/
@[noinline] def hide (_ : Unit) (n : Nat) : Nat := n

/-- `Σ_{i<n} f i`, as a specialised loop. -/
@[specialize] def sumAux (f : Nat → Int) : Nat → Int → Int
  | 0, acc => acc
  | k+1, acc => sumAux f k (acc + f k)

@[inline] def sumTo (n : Nat) (f : Nat → Int) : Int := sumAux f n 0

/-- `#[f 0, ..., f (n-1)]`. -/
@[specialize] def tabAux (f : Nat → Int) (n : Nat) : Nat → Array Int → Array Int
  | 0, acc => acc
  | k+1, acc => tabAux f n k (acc.push (f (n - 1 - k)))

@[inline] def tab (n : Nat) (f : Nat → Int) : Array Int := tabAux f n n (Array.mkEmpty n)

@[inline] def gt (a : Array Int) (i : Nat) : Int := a.getD i 0

/-- `∀ i < n, p i` as a specialised loop. -/
@[specialize] def allAux (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | k+1 => p k && allAux p k

@[inline] def allTo (n : Nat) (p : Nat → Bool) : Bool := allAux p n

/-- Parse a comma separated list of integers. -/
def parseInts (s : String) : Array Int := Id.run do
  let mut out : Array Int := #[]
  let mut cur : Nat := 0
  let mut neg := false
  let mut has := false
  for b in s.toUTF8 do
    if b == 44 then
      if has then out := out.push (if neg then -(cur : Int) else (cur : Int))
      cur := 0; neg := false; has := false
    else if b == 45 then neg := true
    else
      cur := cur * 10 + (b.toNat - 48); has := true
  if has then out := out.push (if neg then -(cur : Int) else (cur : Int))
  return out

end QVCheck

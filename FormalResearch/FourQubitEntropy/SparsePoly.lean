import FormalResearch.FourQubitEntropy.RingOps

/-!
# Sparse polynomials in 32 variables with prime-product monomials

A monomial is the product of the primes attached to its variables, so monomial multiplication is
multiplication of natural numbers and monomial comparison is comparison of natural numbers. Both
are fast in the kernel, which is the point: the kernel evaluates these polynomials, and the
identity of `Identity.lean` is checked by that evaluation.

A polynomial is a list of `(monomial, coefficient)` pairs, sorted by monomial. Sortedness is not
needed for soundness (`evSP_add` etc. hold for any lists); it makes the zero polynomial the empty
list, so that a polynomial identity can be checked by `== []`.
-/

namespace FormalResearch.FourQubitEntropy

/-- Sparse polynomial: `(monomial key, coefficient)` pairs. -/
abbrev SP := List (Nat × Int)

/-- The primes attached to the 32 variables. -/
def primeList : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131]

def primeAt (i : Fin 32) : Nat := primeList.getD i 1

theorem primeAt_prime : ∀ i : Fin 32, (primeAt i).Prime := by
  decide +kernel

theorem primeAt_inj : ∀ i j : Fin 32, primeAt i = primeAt j → i = j := by
  decide +kernel

/-! ### Semantics -/

/-- Value of a monomial key at the variable values `v`. -/
noncomputable def evK (v : Fin 32 → ℂ) (key : Nat) : ℂ :=
  if key = 0 then 0 else ∏ i : Fin 32, v i ^ key.factorization (primeAt i)

theorem evK_mul (v : Fin 32 → ℂ) (a b : Nat) : evK v (a * b) = evK v a * evK v b := by
  by_cases ha : a = 0
  · simp [evK, ha]
  by_cases hb : b = 0
  · simp [evK, hb]
  simp only [evK, ha, hb, Nat.mul_eq_zero, or_self, if_false]
  rw [Nat.factorization_mul ha hb, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, pow_add]

theorem evK_one (v : Fin 32 → ℂ) : evK v 1 = 1 := by simp [evK]

theorem evK_prime (v : Fin 32 → ℂ) (j : Fin 32) : evK v (primeAt j) = v j := by
  have hp := primeAt_prime j
  simp only [evK, hp.ne_zero, if_false, hp.factorization, Finsupp.single_apply]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    have : primeAt j ≠ primeAt i := fun h => hij (primeAt_inj _ _ h).symm
    simp [this]
  · simp

/-- Value of a sparse polynomial. -/
noncomputable def evSP (v : Fin 32 → ℂ) (p : SP) : ℂ :=
  (p.map fun t => (t.2 : ℂ) * evK v t.1).sum

/-! ### Operations -/

/-- Merge two sorted polynomials; the fuel is the sum of the lengths. -/
def addSPAux : Nat → SP → SP → SP
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, a :: p, [] => a :: p
  | n + 1, (k₁, c₁) :: p, (k₂, c₂) :: q =>
    if k₁ < k₂ then (k₁, c₁) :: addSPAux n p ((k₂, c₂) :: q)
    else if k₂ < k₁ then (k₂, c₂) :: addSPAux n ((k₁, c₁) :: p) q
    else if c₁ + c₂ = 0 then addSPAux n p q
    else (k₁, c₁ + c₂) :: addSPAux n p q

def addSP (p q : SP) : SP := addSPAux (p.length + q.length) p q

/-- Add neighbouring pairs of a list of polynomials. -/
def pairUp : Nat → List SP → List SP
  | 0, l => l
  | n + 1, a :: b :: t => addSP a b :: pairUp n t
  | _ + 1, l => l

/-- Sum a list of polynomials by repeated pairwise addition. This keeps intermediate sizes small,
which matters because the kernel evaluates lazily and retains what it computes. -/
def treeSum : Nat → List SP → SP
  | 0, l => l.foldr addSP []
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | n + 1, a :: b :: t => treeSum n (pairUp (t.length + 2) (a :: b :: t))

/-- The monomial times coefficient times polynomial `q`. -/
def mulTerm (t : Nat × Int) (q : SP) : SP := q.map fun s => (t.1 * s.1, t.2 * s.2)

def mulSP (p q : SP) : SP := treeSum 24 (p.map fun t => mulTerm t q)

def negSP (p : SP) : SP := p.map fun t => (t.1, -t.2)

def ofIntSP (k : Int) : SP := if k = 0 then [] else [(1, k)]

/-- The variable number `i`. -/
def varSP (i : Fin 32) : SP := [(primeAt i, 1)]

theorem evSP_nil (v : Fin 32 → ℂ) : evSP v [] = 0 := rfl

theorem evSP_cons (v : Fin 32 → ℂ) (t : Nat × Int) (p : SP) :
    evSP v (t :: p) = (t.2 : ℂ) * evK v t.1 + evSP v p := by
  simp [evSP]

theorem evSP_append (v : Fin 32 → ℂ) (p q : SP) : evSP v (p ++ q) = evSP v p + evSP v q := by
  simp [evSP]

theorem evSP_addSPAux (v : Fin 32 → ℂ) (n : Nat) :
    ∀ p q : SP, evSP v (addSPAux n p q) = evSP v p + evSP v q := by
  induction n with
  | zero => intro p q; exact evSP_append v p q
  | succ n ih =>
    intro p q
    match p, q with
    | [], q => simp [addSPAux, evSP_nil]
    | a :: p, [] => simp [addSPAux, evSP_nil]
    | (k₁, c₁) :: p, (k₂, c₂) :: q =>
      simp only [addSPAux]
      split_ifs with h1 h2 h3
      · rw [evSP_cons, ih, evSP_cons, evSP_cons]; ring
      · rw [evSP_cons, ih, evSP_cons, evSP_cons]; ring
      · have : k₁ = k₂ := by omega
        subst this
        rw [ih, evSP_cons, evSP_cons]
        have : (c₁ : ℂ) + c₂ = 0 := by exact_mod_cast h3
        linear_combination (-(evK v k₁)) * this
      · have : k₁ = k₂ := by omega
        subst this
        rw [evSP_cons, ih, evSP_cons, evSP_cons]
        push_cast
        ring

theorem evSP_addSP (v : Fin 32 → ℂ) (p q : SP) : evSP v (addSP p q) = evSP v p + evSP v q :=
  evSP_addSPAux v _ p q

theorem evSP_pairUp (v : Fin 32 → ℂ) (n : Nat) (l : List SP) :
    ((pairUp n l).map (evSP v)).sum = (l.map (evSP v)).sum := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | [a] => rfl
    | a :: b :: t =>
      simp only [pairUp, List.map_cons, List.sum_cons, ih, evSP_addSP]
      rw [add_assoc]

theorem evSP_treeSum (v : Fin 32 → ℂ) (n : Nat) (l : List SP) :
    evSP v (treeSum n l) = (l.map (evSP v)).sum := by
  induction n generalizing l with
  | zero =>
    induction l with
    | nil => simp [treeSum, evSP_nil]
    | cons a t ih =>
      simp only [treeSum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
      rw [evSP_addSP, ih]
  | succ n ih =>
    match l with
    | [] => simp [treeSum, evSP_nil]
    | [a] => simp [treeSum]
    | a :: b :: t =>
      simp only [treeSum]
      rw [ih, evSP_pairUp]

theorem evSP_mulTerm (v : Fin 32 → ℂ) (t : Nat × Int) (q : SP) :
    evSP v (mulTerm t q) = (t.2 : ℂ) * evK v t.1 * evSP v q := by
  induction q with
  | nil => simp [mulTerm, evSP_nil]
  | cons s q ih =>
    simp only [mulTerm, List.map_cons] at ih ⊢
    rw [evSP_cons, ih, evSP_cons, evK_mul]
    push_cast
    ring

theorem evSP_mulSP (v : Fin 32 → ℂ) (p q : SP) : evSP v (mulSP p q) = evSP v p * evSP v q := by
  unfold mulSP
  rw [evSP_treeSum, List.map_map]
  induction p with
  | nil => simp [evSP_nil]
  | cons t p ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp, evSP_mulTerm] at ih ⊢
    rw [ih, evSP_cons]
    ring

theorem evSP_negSP (v : Fin 32 → ℂ) (p : SP) : evSP v (negSP p) = -evSP v p := by
  induction p with
  | nil => simp [negSP, evSP_nil]
  | cons t p ih =>
    simp only [negSP, List.map_cons] at ih ⊢
    rw [evSP_cons, ih, evSP_cons]
    push_cast
    ring

theorem evSP_ofIntSP (v : Fin 32 → ℂ) (k : Int) : evSP v (ofIntSP k) = k := by
  unfold ofIntSP
  split_ifs with h
  · subst h; simp [evSP_nil]
  · simp [evSP_cons, evSP_nil, evK_one]

theorem evSP_varSP (v : Fin 32 → ℂ) (i : Fin 32) : evSP v (varSP i) = v i := by
  simp [varSP, evSP_cons, evSP_nil, evK_prime]

instance : RingOps SP where
  zero := []
  one := [(1, 1)]
  add := addSP
  mul := mulSP
  neg := negSP
  ofInt := ofIntSP

theorem opsHom_evSP (v : Fin 32 → ℂ) : OpsHom (evSP v) where
  map_zero := rfl
  map_one := by simp [RingOps.one, evSP_cons, evSP_nil, evK_one]
  map_add := evSP_addSP v
  map_mul := evSP_mulSP v
  map_neg := evSP_negSP v
  map_ofInt := evSP_ofIntSP v

end FormalResearch.FourQubitEntropy

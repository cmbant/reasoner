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

/-! ### Operations

The operations are written directly with recursors (`List.rec`, `Nat.rec`) and `cond` on
`Nat.blt`, without fuel, `ite`/`Decidable` or structural-recursion compilation, because that is
the form the kernel evaluates fastest and with the least memory. They are `noncomputable`: they
are only ever run by the kernel, never by compiled code. -/

/-- Merge two sorted polynomials, adding the coefficients of equal monomials and dropping zero
coefficients. -/
noncomputable def addSP : SP → SP → SP :=
  @List.rec (Nat × Int) (fun _ => SP → SP) (fun q => q)
    (fun a p ih q => @List.rec (Nat × Int) (fun _ => SP) (a :: p)
      (fun b q' rec => cond (Nat.blt a.1 b.1) (a :: ih (b :: q'))
        (cond (Nat.blt b.1 a.1) (b :: rec)
          (let c := a.2 + b.2; cond (c == 0) (ih q') ((a.1, c) :: ih q')))) q)

/-- Add neighbouring pairs of a list of polynomials (an unpaired last one is kept). -/
noncomputable def pairUpAux : List SP → Option SP → List SP :=
  @List.rec SP (fun _ => (Option SP → List SP)) (fun o => o.elim [] (fun x => [x]))
    (fun a _ ih o => o.elim (ih (some a)) (fun x => addSP x a :: ih none))

noncomputable def pairUp (l : List SP) : List SP := pairUpAux l none

/-- Sum a list of polynomials by repeated pairwise addition (`n` rounds, then a plain fold). This
keeps intermediate sizes small, which matters because the kernel evaluates lazily and retains what
it computes. -/
noncomputable def treeSum : Nat → List SP → SP :=
  fun n => @Nat.rec (fun _ => List SP → SP) (fun l => l.foldr addSP [])
    (fun _ ih l => @List.rec SP (fun _ => SP) []
      (fun a t _ => @List.rec SP (fun _ => SP) a (fun _ _ _ => ih (pairUp l)) t) l) n

/-- The monomial times coefficient times polynomial `q`. -/
noncomputable def mulTerm (t : Nat × Int) (q : SP) : SP :=
  @List.rec (Nat × Int) (fun _ => SP) [] (fun s _ r => (t.1 * s.1, t.2 * s.2) :: r) q

noncomputable def mulSP (p q : SP) : SP :=
  treeSum 24 (@List.rec (Nat × Int) (fun _ => List SP) [] (fun t _ r => mulTerm t q :: r) p)

noncomputable def negSP (p : SP) : SP :=
  @List.rec (Nat × Int) (fun _ => SP) [] (fun t _ r => (t.1, -t.2) :: r) p

noncomputable def ofIntSP (k : Int) : SP := cond (k == 0) [] [(1, k)]

/-- Equality test. Written so that the kernel evaluates it iteratively: the recursive call is in
tail position, whereas the `DecidableEq (List _)` instance nests one level per element and exceeds
the kernel's recursion depth on lists of several thousand terms. -/
noncomputable def eqSP : SP → SP → Bool :=
  @List.rec (Nat × Int) (fun _ => SP → Bool)
    (fun q => @List.rec (Nat × Int) (fun _ => Bool) true (fun _ _ _ => false) q)
    (fun a _ ih q => @List.rec (Nat × Int) (fun _ => Bool) false
      (fun b q' _ => cond (Nat.beq a.1 b.1) (cond (a.2 == b.2) (ih q') false) false) q)

/-- Concatenation and concatenation of a list of polynomials, written with recursors for fast kernel
evaluation. Only the certificate data of `IdentityCert*.lean` is assembled with them. -/
noncomputable def appSP : SP → SP → SP :=
  @List.rec (Nat × Int) (fun _ => SP → SP) (fun q => q) (fun a _ ih q => a :: ih q)

noncomputable def catSP : List SP → SP :=
  @List.rec SP (fun _ => SP) [] (fun c _ r => appSP c r)

/-- The variable number `i`. -/
def varSP (i : Fin 32) : SP := [(primeAt i, 1)]

theorem evSP_nil (v : Fin 32 → ℂ) : evSP v [] = 0 := rfl

theorem evSP_cons (v : Fin 32 → ℂ) (t : Nat × Int) (p : SP) :
    evSP v (t :: p) = (t.2 : ℂ) * evK v t.1 + evSP v p := by
  simp [evSP]

theorem blt_false_of_not_lt {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]; intro h'; exact h (by simpa using h')

theorem addSP_nil (q : SP) : addSP [] q = q := rfl

theorem addSP_cons_nil (a : Nat × Int) (p : SP) : addSP (a :: p) [] = a :: p := rfl

theorem addSP_cons_cons (a b : Nat × Int) (p q : SP) :
    addSP (a :: p) (b :: q) =
      cond (Nat.blt a.1 b.1) (a :: addSP p (b :: q))
        (cond (Nat.blt b.1 a.1) (b :: addSP (a :: p) q)
          (cond (a.2 + b.2 == 0) (addSP p q) ((a.1, a.2 + b.2) :: addSP p q))) := rfl

theorem evSP_addSP (v : Fin 32 → ℂ) (p q : SP) : evSP v (addSP p q) = evSP v p + evSP v q := by
  induction p generalizing q with
  | nil => rw [addSP_nil, evSP_nil, zero_add]
  | cons a p ih =>
    induction q with
    | nil => rw [addSP_cons_nil, evSP_nil, add_zero]
    | cons b q ih2 =>
      rw [addSP_cons_cons]
      by_cases h1 : a.1 < b.1
      · have : Nat.blt a.1 b.1 = true := by simpa using h1
        rw [this, Bool.cond_true, evSP_cons, ih, evSP_cons, evSP_cons]; ring
      · have h1' : Nat.blt a.1 b.1 = false := blt_false_of_not_lt h1
        rw [h1', Bool.cond_false]
        by_cases h2 : b.1 < a.1
        · have : Nat.blt b.1 a.1 = true := by simpa using h2
          rw [this, Bool.cond_true, evSP_cons, ih2, evSP_cons, evSP_cons]; ring
        · have h2' : Nat.blt b.1 a.1 = false := blt_false_of_not_lt h2
          rw [h2', Bool.cond_false]
          have hk : a.1 = b.1 := by omega
          by_cases h3 : a.2 + b.2 = 0
          · have : (a.2 + b.2 == 0) = true := by simpa using h3
            rw [this, Bool.cond_true, ih, evSP_cons, evSP_cons, ← hk]
            have : (a.2 : ℂ) + b.2 = 0 := by exact_mod_cast h3
            linear_combination (-(evK v a.1)) * this
          · have : (a.2 + b.2 == 0) = false := by simpa using h3
            rw [this, Bool.cond_false, evSP_cons, ih, evSP_cons, evSP_cons, ← hk]
            push_cast
            ring

theorem evSP_pairUpAux (v : Fin 32 → ℂ) (l : List SP) (o : Option SP) :
    ((pairUpAux l o).map (evSP v)).sum = (o.elim 0 (evSP v)) + (l.map (evSP v)).sum := by
  induction l generalizing o with
  | nil => cases o <;> simp [pairUpAux]
  | cons a t ih =>
    cases o with
    | none =>
      have h : pairUpAux (a :: t) none = pairUpAux t (some a) := rfl
      rw [h, ih]; simp
    | some x =>
      have h : pairUpAux (a :: t) (some x) = addSP x a :: pairUpAux t none := rfl
      rw [h, List.map_cons, List.sum_cons, ih, evSP_addSP]; simp; ring

theorem evSP_pairUp (v : Fin 32 → ℂ) (l : List SP) :
    ((pairUp l).map (evSP v)).sum = (l.map (evSP v)).sum := by
  have := evSP_pairUpAux v l none
  simpa [pairUp] using this

theorem treeSum_zero (l : List SP) : treeSum 0 l = l.foldr addSP [] := rfl

theorem treeSum_succ_nil (n : Nat) : treeSum (n + 1) [] = [] := rfl

theorem treeSum_succ_single (n : Nat) (a : SP) : treeSum (n + 1) [a] = a := rfl

theorem treeSum_succ_cons2 (n : Nat) (a b : SP) (t : List SP) :
    treeSum (n + 1) (a :: b :: t) = treeSum n (pairUp (a :: b :: t)) := rfl

theorem evSP_treeSum (v : Fin 32 → ℂ) (n : Nat) (l : List SP) :
    evSP v (treeSum n l) = (l.map (evSP v)).sum := by
  induction n generalizing l with
  | zero =>
    induction l with
    | nil => simp [treeSum_zero, evSP_nil]
    | cons a t ih =>
      rw [treeSum_zero, List.foldr_cons, evSP_addSP, ← treeSum_zero, ih]; simp
  | succ n ih =>
    match l with
    | [] => rw [treeSum_succ_nil]; simp [evSP_nil]
    | [a] => rw [treeSum_succ_single]; simp
    | a :: b :: t => rw [treeSum_succ_cons2, ih, evSP_pairUp]

theorem evSP_mulTerm (v : Fin 32 → ℂ) (t : Nat × Int) (q : SP) :
    evSP v (mulTerm t q) = (t.2 : ℂ) * evK v t.1 * evSP v q := by
  induction q with
  | nil => simp [mulTerm, evSP_nil]
  | cons s q ih =>
    have h : mulTerm t (s :: q) = (t.1 * s.1, t.2 * s.2) :: mulTerm t q := rfl
    rw [h, evSP_cons, ih, evSP_cons, evK_mul]
    push_cast
    ring

theorem evSP_mulSP (v : Fin 32 → ℂ) (p q : SP) : evSP v (mulSP p q) = evSP v p * evSP v q := by
  unfold mulSP
  rw [evSP_treeSum]
  induction p with
  | nil => simp [evSP_nil]
  | cons t p ih =>
    have h : (@List.rec (Nat × Int) (fun _ => List SP) [] (fun t _ r => mulTerm t q :: r)
        (t :: p) : List SP) = mulTerm t q :: @List.rec (Nat × Int) (fun _ => List SP) []
          (fun t _ r => mulTerm t q :: r) p := rfl
    rw [h, List.map_cons, List.sum_cons, ih, evSP_mulTerm, evSP_cons]
    ring

theorem evSP_negSP (v : Fin 32 → ℂ) (p : SP) : evSP v (negSP p) = -evSP v p := by
  induction p with
  | nil => simp [negSP, evSP_nil]
  | cons t p ih =>
    have h : negSP (t :: p) = (t.1, -t.2) :: negSP p := rfl
    rw [h, evSP_cons, ih, evSP_cons]
    push_cast
    ring

theorem evSP_ofIntSP (v : Fin 32 → ℂ) (k : Int) : evSP v (ofIntSP k) = k := by
  by_cases h : k = 0
  · have : (k == 0) = true := by simpa using h
    have h2 : ofIntSP k = [] := by unfold ofIntSP; rw [this]; rfl
    rw [h2, evSP_nil, h]; simp
  · have : (k == 0) = false := by simpa using h
    have h2 : ofIntSP k = [(1, k)] := by unfold ofIntSP; rw [this]; rfl
    rw [h2, evSP_cons, evSP_nil, evK_one]; simp

theorem eqSP_sound : ∀ p q : SP, eqSP p q = true → p = q := by
  intro p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons b q => exact absurd (show false = true from h) (by decide)
  | cons a p ih =>
    intro q h
    cases q with
    | nil => exact absurd (show false = true from h) (by decide)
    | cons b q =>
      have h' : cond (Nat.beq a.1 b.1) (cond (a.2 == b.2) (eqSP p q) false) false = true := h
      cases h1 : Nat.beq a.1 b.1 <;> rw [h1] at h' <;> simp only [Bool.cond_true, Bool.cond_false] at h'
      · exact absurd h' (by decide)
      cases h2 : (a.2 == b.2) <;> rw [h2] at h' <;> simp only [Bool.cond_true, Bool.cond_false] at h'
      · exact absurd h' (by decide)
      have e1 : a.1 = b.1 := Nat.eq_of_beq_eq_true h1
      have e2 : a.2 = b.2 := by simpa using h2
      rw [ih q h', Prod.ext e1 e2]

theorem evSP_varSP (v : Fin 32 → ℂ) (i : Fin 32) : evSP v (varSP i) = v i := by
  simp [varSP, evSP_cons, evSP_nil, evK_prime]

noncomputable instance : RingOps SP where
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

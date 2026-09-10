import Mathlib

/-!
# QI-A T39 sparse-witness Haar second moment

Source authority: `cmbant/QIprojects@ec8d5c5210e6837992ace8fcf63da77c5f8a557e`.
The QI-A T39 verifier is unchanged at blob
`d058c7650a6a75466eb47945c3948685d13f0533`:
`QI-A/scripts/verify_operational_fingerprint.py`.

This module isolates the finite `S₆` cycle enumeration used by the canonical
three-copy sparse chirality witness and the exact rational/binomial closed
form that follows from it.  The finite 720-permutation enumeration is checked
with `native_decide`; accordingly that particular finite table has the same
`Lean.ofReduceBool` trust boundary as other repository `native_decide`
certificates.  The all-party algebraic reduction from that table to the closed
formula is proved symbolically in Lean.

The module does not formalize the analytic Haar/symmetric-subspace moment
identity that identifies the symmetrized trace with an expectation, and it
does not promote the resulting `8^m` inverse-square scale to a minimax lower
bound, settings count, observable count, or circuit-size statement.
-/

namespace FormalResearch.QIA

/-- The four local copy permutations in the source sparse word. -/
inductive SparseLocalPerm3 where
  | e
  | s13
  | s12
  | c132
deriving DecidableEq, Repr

/-- Action of the source `S₃` permutations, optionally inverted.  Only inputs
`0,1,2` are used; the fallback keeps this total as a function on `Nat`. -/
def sparseLocalPerm3Apply (p : SparseLocalPerm3) (inverse : Bool) (i : Nat) : Nat :=
  match p with
  | .e => i
  | .s13 =>
      match i with
      | 0 => 2
      | 1 => 1
      | 2 => 0
      | n => n
  | .s12 =>
      match i with
      | 0 => 1
      | 1 => 0
      | 2 => 2
      | n => n
  | .c132 =>
      if inverse then
        match i with
        | 0 => 2
        | 1 => 0
        | 2 => 1
        | n => n
      else
        match i with
        | 0 => 1
        | 1 => 2
        | 2 => 0
        | n => n

/-- `X₃` uses identity, `(13)`, `(12)`, `(132)` on the four parties. -/
def sparseWord : List SparseLocalPerm3 :=
  [.e, .s13, .s12, .c132]

/-- Read a six-point permutation represented as the image list of `0,...,5`. -/
def sparsePermGet (π : List Nat) (i : Nat) : Nat :=
  π.getD i i

/-- Apply `p` separately on the first and second three-copy blocks, using the
inverse according to the two signs in the `W×W` expansion. -/
def sparseLocal6Apply (p : SparseLocalPerm3) (inverseA inverseB : Bool)
    (i : Nat) : Nat :=
  if i < 3 then
    sparseLocalPerm3Apply p inverseA i
  else
    3 + sparseLocalPerm3Apply p inverseB (i - 3)

/-- Source composition convention: local permutation after the global `π`. -/
def sparseComposeLocal (p : SparseLocalPerm3) (inverseA inverseB : Bool)
    (π : List Nat) : List Nat :=
  (List.range 6).map fun i =>
    sparseLocal6Apply p inverseA inverseB (sparsePermGet π i)

/-- Iterate a six-point image list. -/
def sparsePermIterate (π : List Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => sparsePermGet π (sparsePermIterate π n i)

/-- For an actual permutation of six points, `i` represents its cycle exactly
when it is the least point in that cycle.  Six iterates suffice to test this. -/
def sparseIsCycleRepresentative (π : List Nat) (i : Nat) : Bool :=
  (List.range 6).all fun k => decide (i ≤ sparsePermIterate π k i)

/-- Number of cycles of a six-point permutation, computed by least-cycle
representatives. -/
def sparseCycleCount (π : List Nat) : Nat :=
  ((List.range 6).filter fun i => sparseIsCycleRepresentative π i).length

/-- The 720 image lists of `S₆`. -/
def sparsePermutations6 : List (List Nat) :=
  (List.range 6).permutations

/-- Boolean encoding of the two signs: `false ↦ +1`, `true ↦ -1`. -/
def sparseSign (inverse : Bool) : Int :=
  if inverse then -1 else 1

/-- Product of local two-dimensional trace factors for one pair of signs. -/
def sparseTraceProduct (π : List Nat) (inverseA inverseB : Bool) : Int :=
  (sparseWord.map fun p =>
    (2 : Int) ^ sparseCycleCount (sparseComposeLocal p inverseA inverseB π)).prod

/-- Four times the source `W×W` trace contribution of one global permutation.
The factor four clears the `(2i)^{-2}` denominator. -/
def sparseFourTrace (π : List Nat) : Int :=
  (([false, true].flatMap fun inverseA =>
    [false, true].map fun inverseB =>
      -(sparseSign inverseA * sparseSign inverseB) *
        sparseTraceProduct π inverseA inverseB)).sum

/-- Four times the trace contribution grouped by cycle count of the global
`S₆` permutation. -/
def sparseGroupedFourTrace (cycles : Nat) : Int :=
  (((sparsePermutations6.filter fun π => sparseCycleCount π == cycles).map
    sparseFourTrace).sum)

/-- Exact executable `S₆` certificate.  Dividing by four gives precisely the
source grouped coefficients `{1 : -216, 3 : 864}`. -/
theorem sparse_s6_grouped_four_trace_certificate :
    sparseGroupedFourTrace 0 = 0 ∧
    sparseGroupedFourTrace 1 = -864 ∧
    sparseGroupedFourTrace 2 = 0 ∧
    sparseGroupedFourTrace 3 = 3456 ∧
    sparseGroupedFourTrace 4 = 0 ∧
    sparseGroupedFourTrace 5 = 0 ∧
    sparseGroupedFourTrace 6 = 0 := by
  native_decide

/-- Source grouped coefficient after restoring the factor `1/4`. -/
def sparseGroupedTrace (cycles : Nat) : ℚ :=
  (sparseGroupedFourTrace cycles : ℚ) / 4

/-- The exact grouped coefficients printed by the T39 verifier. -/
theorem sparse_s6_grouped_trace_certificate :
    sparseGroupedTrace 1 = -216 ∧ sparseGroupedTrace 3 = 864 := by
  rcases sparse_s6_grouped_four_trace_certificate with
    ⟨_, h1, _, h3, _, _, _⟩
  constructor
  · unfold sparseGroupedTrace
    rw [h1]
    norm_num
  · unfold sparseGroupedTrace
    rw [h3]
    norm_num

/-- Symmetrized trace after extending the four-party sparse word by identities
on `t` additional qubit parties.  Each extra party contributes `2^c` for a
global permutation with `c` cycles, and `|S₆|=720`. -/
def sparseSymmetrizedTrace (t : Nat) : ℚ :=
  (((List.range 7).map fun c =>
    sparseGroupedTrace c * (2 : ℚ) ^ (c * t)).sum) / 720

/-- The finite `S₆` table reduces the all-party symmetrized trace to two terms. -/
theorem sparseSymmetrizedTrace_two_term (t : Nat) :
    sparseSymmetrizedTrace t =
      ((-216 : ℚ) * (2 : ℚ)^t + 864 * (2 : ℚ)^(3*t)) / 720 := by
  rcases sparse_s6_grouped_four_trace_certificate with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hrange : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := by decide
  unfold sparseSymmetrizedTrace
  rw [hrange]
  norm_num [sparseGroupedTrace, h0, h1, h2, h3, h4, h5, h6]

/-- Total Hilbert dimension `N=2^m` with `m=t+4` qubit parties. -/
def sparseQubitDimensionQ (t : Nat) : ℚ :=
  (2 : ℚ)^(t+4)

/-- Exact closed form behind the T39 Haar second-moment numerator. -/
theorem sparseSymmetrizedTrace_closed (t : Nat) :
    sparseSymmetrizedTrace t =
      3 * sparseQubitDimensionQ t * (sparseQubitDimensionQ t ^ 2 - 64) / 10240 := by
  rw [sparseSymmetrizedTrace_two_term]
  unfold sparseQubitDimensionQ
  rw [pow_add]
  norm_num
  have hpow : (2 : ℚ)^(3*t) = ((2 : ℚ)^t)^3 := by
    rw [show 3*t = t*3 by omega, pow_mul]
  rw [hpow]
  ring

/-- Nat-valued version of the same total Hilbert dimension, used in the
symmetric-power binomial denominator. -/
def sparseQubitDimensionNat (t : Nat) : Nat :=
  2^(t+4)

/-- Exact rational quantity obtained after dividing the symmetrized trace by
`dim Sym^6(ℂ^N)=binom(N+5,6)`.  The analytic Haar identity identifying this
quantity with `E[f_m^2]` remains an explicit external semantic bridge. -/
def sparseHaarSecondMomentCertificate (t : Nat) : ℚ :=
  sparseSymmetrizedTrace t /
    (Nat.choose (sparseQubitDimensionNat t + 5) 6 : ℚ)

/-- Source closed form
`[3 N (N^2-64)/10240] / binom(N+5,6)`, with `N=2^(t+4)`. -/
theorem sparseHaarSecondMomentCertificate_closed (t : Nat) :
    sparseHaarSecondMomentCertificate t =
      (3 * sparseQubitDimensionQ t * (sparseQubitDimensionQ t ^ 2 - 64) / 10240) /
        (Nat.choose (sparseQubitDimensionNat t + 5) 6 : ℚ) := by
  unfold sparseHaarSecondMomentCertificate
  rw [sparseSymmetrizedTrace_closed]

/-- Four-qubit regression retained by the source verifier. -/
theorem sparseHaarSecondMomentCertificate_four :
    sparseHaarSecondMomentCertificate 0 = (3 : ℚ) / 180880 := by
  rw [sparseHaarSecondMomentCertificate_closed]
  norm_num [sparseQubitDimensionQ, sparseQubitDimensionNat, Nat.choose]

end FormalResearch.QIA

module

public import FormalResearch.SignUncertainty.O4CertBall

/-!
# The box evaluator of the `O4QuotientBound` certificate, written once for any arithmetic

The numerator and denominator of the paper's quotient
`F(θ) = ((L s - a) θ - (π²/36)(s³ - 1) θ³ + ρ(s θ)) / (θ (θ² - θ₀²)²)`, `θ₀² = 12 a/π²`, at the point `θ = (1/4)(1 - t² + 2 i t)/(1 + t²)` of the
first-quadrant arc `|θ| = 1/4`, with `ρ` replaced by its degree-27 truncation `ρ₁₃(τ) = (1/π) w x² P(x)` (`w = π τ`, `x = w²`, `P` a Horner polynomial with the
signed rational coefficients `(-1)^k r_{k+2}`) plus an error term `e = (er, ei)`, are computed by `boxEval`, a function that is generic in the arithmetic
(`ℝ` for the analytic statement, `Ball` for the kernel check; same pattern as `FormalResearch/FourQubitEntropy/AH6Model.lean`).  Complex numbers are pairs `CP α`.
`boxEval_enc`: if the inputs are enclosed then so are numerator and denominator.

Status: proved.  Not formalised here: the grid data and the check (`O4CertCheck.lean`, `gen_o4_boxes.py`).
-/

@[expose] public section

namespace FormalResearch.SignUncertainty.O4Cert

section Generic

variable {α : Type} [Add α] [Mul α] [Neg α] [IntCast α]

/-- The integer constant `n`. -/
def ic (n : ℤ) : α := (n : α)

/-- A complex number as a pair of components. -/
structure CP (α : Type) where
  re : α
  im : α

def CP.add (a b : CP α) : CP α := ⟨a.re + b.re, a.im + b.im⟩
def CP.neg (a : CP α) : CP α := ⟨-a.re, -a.im⟩
def CP.sub (a b : CP α) : CP α := CP.add a (CP.neg b)
def CP.mul (a b : CP α) : CP α := ⟨a.re * b.re + -(a.im * b.im), a.re * b.im + a.im * b.re⟩
def CP.smul (k : α) (a : CP α) : CP α := ⟨k * a.re, k * a.im⟩
def CP.ofRe (x : α) : CP α := ⟨x, ic 0⟩

/-- Horner evaluation of `acc ↦ acc · x + c` along the list of coefficients (highest first). -/
def horner (x : CP α) : List α → CP α → CP α
  | [], acc => acc
  | c :: cs, acc => horner x cs (CP.add (CP.mul acc x) (CP.ofRe c))

/-- The inputs of a box. -/
structure Inp (α : Type) where
  L : α
  s : α
  a : α
  t : α
  u : α
  pi : α
  ipi : α
  ipi2 : α
  q14 : α
  q136 : α
  er : α
  ei : α
  cs : List α

/-- The point `θ = (1/4)(1 - t² + 2 i t)/(1 + t²)` (with `u = 1/(1 + t²)`). -/
def thV (I : Inp α) : CP α := ⟨((ic 1 + -(I.t * I.t)) * I.u) * I.q14, ((ic 2 * I.t) * I.u) * I.q14⟩

def th2V (I : Inp α) : CP α := CP.mul (thV I) (thV I)
def th3V (I : Inp α) : CP α := CP.mul (th2V I) (thV I)

/-- `θ₀² = 12 a/π²`. -/
def th02V (I : Inp α) : α := (ic 12 * I.a) * I.ipi2

def k1V (I : Inp α) : α := I.L * I.s + -I.a
def k2V (I : Inp α) : α := ((I.pi * I.pi) * I.q136) * (((I.s * I.s) * I.s) + -ic 1)

/-- `w = π s θ`. -/
def wV (I : Inp α) : CP α := CP.smul I.pi (CP.smul I.s (thV I))
def xV (I : Inp α) : CP α := CP.mul (wV I) (wV I)
def accV (I : Inp α) : CP α := horner (xV I) I.cs ⟨ic 0, ic 0⟩
def rho0V (I : Inp α) : CP α := CP.smul I.ipi (CP.mul (CP.mul (wV I) (CP.mul (xV I) (xV I))) (accV I))
def rhoV (I : Inp α) : CP α := ⟨(rho0V I).re + I.er, (rho0V I).im + I.ei⟩

def numV (I : Inp α) : CP α := CP.add (CP.sub (CP.smul (k1V I) (thV I)) (CP.smul (k2V I) (th3V I))) (rhoV I)
def d1V (I : Inp α) : CP α := CP.sub (th2V I) ⟨th02V I, ic 0⟩
def denV (I : Inp α) : CP α := CP.mul (thV I) (CP.mul (d1V I) (d1V I))

/-- Numerator and denominator of the quotient at the box. -/
def boxEval (I : Inp α) : CP α × CP α := (numV I, denV I)

/-! The stage definitions are irreducible for the elaborator (so that the enclosure tactic never unfolds one stage into the next); the kernel
check `decide +kernel` ignores this attribute. -/
attribute [irreducible] thV th2V th3V th02V k1V k2V wV xV accV rho0V rhoV numV d1V denV

/-- `10000 |num|²` and `169 |den|²`, as in the box test `|F| ≤ 0.13`. -/
def boxSq (z : CP α) (k : ℤ) : α := (z.re * z.re + z.im * z.im) * ic k

end Generic

/-! ### Enclosure -/

theorem Enc.ic (n : ℤ) : Enc (ic n : ℝ) (ic n : Ball) := Enc.intCast n

/-- Enclosure of a complex pair. -/
structure CEnc (z : CP ℝ) (b : CP Ball) : Prop where
  re : Enc z.re b.re
  im : Enc z.im b.im

theorem CEnc.add {a b : CP ℝ} {A B : CP Ball} (ha : CEnc a A) (hb : CEnc b B) : CEnc (CP.add a b) (CP.add A B) :=
  ⟨Enc.add ha.re hb.re, Enc.add ha.im hb.im⟩

theorem CEnc.neg {a : CP ℝ} {A : CP Ball} (ha : CEnc a A) : CEnc (CP.neg a) (CP.neg A) :=
  ⟨Enc.neg ha.re, Enc.neg ha.im⟩

theorem CEnc.sub {a b : CP ℝ} {A B : CP Ball} (ha : CEnc a A) (hb : CEnc b B) : CEnc (CP.sub a b) (CP.sub A B) :=
  CEnc.add ha (CEnc.neg hb)

theorem CEnc.mul {a b : CP ℝ} {A B : CP Ball} (ha : CEnc a A) (hb : CEnc b B) : CEnc (CP.mul a b) (CP.mul A B) :=
  ⟨Enc.add (Enc.mul ha.re hb.re) (Enc.neg (Enc.mul ha.im hb.im)),
    Enc.add (Enc.mul ha.re hb.im) (Enc.mul ha.im hb.re)⟩

theorem CEnc.smul {k : ℝ} {K : Ball} {a : CP ℝ} {A : CP Ball} (hk : Enc k K) (ha : CEnc a A) :
    CEnc (CP.smul k a) (CP.smul K A) :=
  ⟨Enc.mul hk ha.re, Enc.mul hk ha.im⟩

theorem CEnc.ofRe {x : ℝ} {X : Ball} (hx : Enc x X) : CEnc (CP.ofRe x) (CP.ofRe X) :=
  ⟨hx, Enc.ic 0⟩

/-- Enclosure of a list. -/
inductive EncL : List ℝ → List Ball → Prop
  | nil : EncL [] []
  | cons {x : ℝ} {b : Ball} {xs : List ℝ} {bs : List Ball} : Enc x b → EncL xs bs → EncL (x :: xs) (b :: bs)

theorem horner_enc {x : CP ℝ} {X : CP Ball} (hx : CEnc x X) :
    ∀ {cs : List ℝ} {Cs : List Ball} {acc : CP ℝ} {Acc : CP Ball}, EncL cs Cs → CEnc acc Acc →
      CEnc (horner x cs acc) (horner X Cs Acc) := by
  intro cs Cs acc Acc hc
  induction hc generalizing acc Acc with
  | nil => intro h; exact h
  | cons hb _ ih => intro h; exact ih (CEnc.add (CEnc.mul h hx) (CEnc.ofRe hb))

structure InpEnc (I : Inp ℝ) (J : Inp Ball) : Prop where
  L : Enc I.L J.L
  s : Enc I.s J.s
  a : Enc I.a J.a
  t : Enc I.t J.t
  u : Enc I.u J.u
  pi : Enc I.pi J.pi
  ipi : Enc I.ipi J.ipi
  ipi2 : Enc I.ipi2 J.ipi2
  q14 : Enc I.q14 J.q14
  q136 : Enc I.q136 J.q136
  er : Enc I.er J.er
  ei : Enc I.ei J.ei
  cs : EncL I.cs J.cs

theorem CEnc.pair {x y : ℝ} {X Y : Ball} (hx : Enc x X) (hy : Enc y Y) : CEnc (⟨x, y⟩ : CP ℝ) (⟨X, Y⟩ : CP Ball) := ⟨hx, hy⟩

theorem CEnc.zero : CEnc (⟨ic 0, ic 0⟩ : CP ℝ) (⟨ic 0, ic 0⟩ : CP Ball) := ⟨Enc.ic 0, Enc.ic 0⟩

/-- Closing tactic for enclosure goals. -/
macro "enc" : tactic =>
  `(tactic| repeat (first
    | assumption
    | apply CEnc.add | apply CEnc.mul | apply CEnc.sub | apply CEnc.smul | apply CEnc.pair | apply CEnc.ofRe
    | apply CEnc.zero | apply horner_enc
    | apply CEnc.re | apply CEnc.im | apply Enc.add | apply Enc.mul | apply Enc.neg | apply Enc.ic))

theorem thV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (thV I) (thV J) := by
  obtain ⟨hL, hs, ha, ht, hu, hpi, hipi, hipi2, hq14, hq136, her, hei, hcs⟩ := h
  simp only [thV]; enc

theorem th2V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (th2V I) (th2V J) := by
  have := thV_enc h
  simp only [th2V]; enc

theorem th3V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (th3V I) (th3V J) := by
  have := thV_enc h
  have := th2V_enc h
  simp only [th3V]; enc

theorem th02V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : Enc (th02V I) (th02V J) := by
  obtain ⟨hL, hs, ha, ht, hu, hpi, hipi, hipi2, hq14, hq136, her, hei, hcs⟩ := h
  simp only [th02V]; enc

theorem k1V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : Enc (k1V I) (k1V J) := by
  obtain ⟨hL, hs, ha, ht, hu, hpi, hipi, hipi2, hq14, hq136, her, hei, hcs⟩ := h
  simp only [k1V]; enc

theorem k2V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : Enc (k2V I) (k2V J) := by
  obtain ⟨hL, hs, ha, ht, hu, hpi, hipi, hipi2, hq14, hq136, her, hei, hcs⟩ := h
  simp only [k2V]; enc

theorem wV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (wV I) (wV J) := by
  have := thV_enc h
  obtain ⟨hL, hs, ha, ht, hu, hpi, hipi, hipi2, hq14, hq136, her, hei, hcs⟩ := h
  simp only [wV]; enc

theorem xV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (xV I) (xV J) := by
  have := wV_enc h
  simp only [xV]; enc

theorem accV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (accV I) (accV J) := by
  have := xV_enc h
  simp only [accV]
  exact horner_enc this h.cs CEnc.zero

theorem rho0V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (rho0V I) (rho0V J) := by
  have := wV_enc h
  have := xV_enc h
  have := accV_enc h
  have := h.ipi
  simp only [rho0V]; enc

theorem rhoV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (rhoV I) (rhoV J) := by
  have := rho0V_enc h
  have := h.er
  have := h.ei
  simp only [rhoV]; enc

theorem numV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (numV I) (numV J) := by
  have := thV_enc h
  have := th3V_enc h
  have := k1V_enc h
  have := k2V_enc h
  have := rhoV_enc h
  simp only [numV]; enc

theorem d1V_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (d1V I) (d1V J) := by
  have := th2V_enc h
  have := th02V_enc h
  simp only [d1V]; enc

theorem denV_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) : CEnc (denV I) (denV J) := by
  have := thV_enc h
  have := d1V_enc h
  simp only [denV]; enc

theorem boxEval_enc {I : Inp ℝ} {J : Inp Ball} (h : InpEnc I J) :
    CEnc (boxEval I).1 (boxEval J).1 ∧ CEnc (boxEval I).2 (boxEval J).2 :=
  ⟨numV_enc h, denV_enc h⟩

theorem boxSq_enc {z : CP ℝ} {Z : CP Ball} (h : CEnc z Z) (k : ℤ) : Enc (boxSq z k) (boxSq Z k) := by
  obtain ⟨hr, hi⟩ := h
  simp only [boxSq]
  enc

end FormalResearch.SignUncertainty.O4Cert

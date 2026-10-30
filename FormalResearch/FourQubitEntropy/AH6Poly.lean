import FormalResearch.FourQubitEntropy.AH6Ball

/-!
# Coefficient-list polynomials over an arbitrary arithmetic, with enclosure lemmas

The operations of this file are written once, for any type with `+`, `*`, `-` and integer constants, by structural
recursion on lists (no well-founded recursion), so they can be run in two ways:

* at `ℝ`, giving the real polynomials of the analytic proof (`evalL`, `derL`, synthetic division `dl`, Taylor shift
  `taylorL`, and the Möbius/Bernstein transform `mob`), with their semantic lemmas;
* at `Ball`, giving the enclosures that the kernel evaluates (`EncL` lemmas: each operation maps enclosures to
  enclosures).

A list `[a₀, a₁, …]` is the polynomial `a₀ + a₁ x + …`.

Positivity certificates (`pos_on_interval`, `pos_on_tail`): `mob (scalePow (h-l) (taylorL p l))` is the list of the
Bernstein coefficients of `p` on `[l,h]` times binomial coefficients; if all of them are positive then `p > 0` on
`[l,h)` (the endpoint `h` is covered by the next interval).
-/

namespace FormalResearch.FourQubitEntropy.AH6

section Generic

variable {α : Type} [Add α] [Mul α] [Neg α] [IntCast α]

/-- Integer constant of the arithmetic. -/
def ic (k : ℤ) : α := (k : α)

def addL : List α → List α → List α
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

def scaleL (c : α) (p : List α) : List α := p.map (c * ·)

def mulL : List α → List α → List α
  | [], _ => []
  | a :: p, q => addL (scaleL a q) (ic 0 :: mulL p q)

def powL (p : List α) : ℕ → List α
  | 0 => [ic 1]
  | n + 1 => mulL p (powL p n)

def evalL : List α → α → α
  | [], _ => ic 0
  | a :: p, x => a + x * evalL p x

/-- Derivative: `(a + x p)' = p + x p'`. -/
def derL : List α → List α
  | [] => []
  | _ :: p => addL p (ic 0 :: derL p)

/-- Synthetic division by `x - r`: `p = (x - r) q + rem`. -/
def dl : List α → α → List α × α
  | [], _ => ([], ic 0)
  | [a], _ => ([], a)
  | a :: b :: t, r => ((dl (b :: t) r).2 :: (dl (b :: t) r).1, a + r * (dl (b :: t) r).2)

/-- Taylor shift: the coefficients of `p(l + w)` in `w`. -/
def taylorL : List α → α → List α
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: p, l => addL [a] (mulL [l, ic 1] (taylorL (b :: p) l))

/-- Multiply the `i`-th coefficient by `d^i` (the substitution `x ↦ d x`). -/
def scalePow (d : α) : List α → List α
  | [] => []
  | a :: p => a :: scaleL d (scalePow d p)

/-- `∑ᵢ pᵢ sⁱ (1+s)^(n-i)`, `n = length - 1`. -/
def mob : List α → List α
  | [] => []
  | a :: p => addL (scaleL a (powL [ic 1, ic 1] p.length)) (ic 0 :: mob p)

end Generic

/-! ### Enclosure lemmas -/

/-- Pointwise enclosure of a list of reals by a list of balls. -/
def EncL (p : List ℝ) (P : List Ball) : Prop := List.Forall₂ Enc p P

theorem Enc.ic (k : ℤ) : Enc (ic k : ℝ) (ic k : Ball) := Enc.intCast k

theorem EncL.nil : EncL [] [] := List.Forall₂.nil

theorem EncL.cons {x : ℝ} {a : Ball} {p : List ℝ} {P : List Ball} (h : Enc x a) (hp : EncL p P) :
    EncL (x :: p) (a :: P) := List.Forall₂.cons h hp

theorem addL_enc {p q : List ℝ} {P Q : List Ball} (hp : EncL p P) (hq : EncL q Q) :
    EncL (addL p q) (addL P Q) := by
  induction hp generalizing q Q with
  | nil => simpa [addL] using hq
  | cons h hp ih =>
    cases hq with
    | nil => simpa [addL] using EncL.cons h hp
    | cons h' hq => exact EncL.cons (Enc.add h h') (ih hq)

theorem scaleL_enc {c : ℝ} {C : Ball} (hc : Enc c C) {p : List ℝ} {P : List Ball} (hp : EncL p P) :
    EncL (scaleL c p) (scaleL C P) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih => exact EncL.cons (Enc.mul hc h) ih

theorem mulL_enc {p q : List ℝ} {P Q : List Ball} (hp : EncL p P) (hq : EncL q Q) :
    EncL (mulL p q) (mulL P Q) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih =>
    exact addL_enc (scaleL_enc h hq) (EncL.cons (Enc.ic 0) ih)

theorem powL_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) (n : ℕ) :
    EncL (powL p n) (powL P n) := by
  induction n with
  | zero => exact EncL.cons (Enc.ic 1) EncL.nil
  | succ n ih => exact mulL_enc hp ih

theorem evalL_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) {x : ℝ} {X : Ball} (hx : Enc x X) :
    Enc (evalL p x) (evalL P X) := by
  induction hp with
  | nil => exact Enc.ic 0
  | cons h hp ih => exact Enc.add h (Enc.mul hx ih)

theorem derL_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) : EncL (derL p) (derL P) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih => exact addL_enc hp (EncL.cons (Enc.ic 0) ih)

theorem dl_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) {r : ℝ} {R : Ball} (hr : Enc r R) :
    EncL (dl p r).1 (dl P R).1 ∧ Enc (dl p r).2 (dl P R).2 := by
  induction hp with
  | nil => exact ⟨EncL.nil, Enc.ic 0⟩
  | cons h hp ih =>
    rename_i a A p P
    cases hp with
    | nil => exact ⟨EncL.nil, h⟩
    | cons h2 hp2 =>
      rename_i b B t T
      have ih' := ih
      simp only [FormalResearch.FourQubitEntropy.AH6.dl]
      exact ⟨EncL.cons ih'.2 ih'.1, Enc.add h (Enc.mul hr ih'.2)⟩

theorem taylorL_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) {l : ℝ} {L : Ball} (hl : Enc l L) :
    EncL (taylorL p l) (taylorL P L) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih =>
    cases hp with
    | nil => exact EncL.cons h EncL.nil
    | cons h2 hp2 =>
      exact addL_enc (EncL.cons h EncL.nil)
        (mulL_enc (EncL.cons hl (EncL.cons (Enc.ic 1) EncL.nil)) ih)

theorem scalePow_enc {d : ℝ} {D : Ball} (hd : Enc d D) {p : List ℝ} {P : List Ball} (hp : EncL p P) :
    EncL (scalePow d p) (scalePow D P) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih => exact EncL.cons h (scaleL_enc hd ih)

theorem mob_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) : EncL (mob p) (mob P) := by
  induction hp with
  | nil => exact EncL.nil
  | cons h hp ih =>
    rename_i a A p P
    have hlen : p.length = P.length := List.Forall₂.length_eq hp
    simp only [FormalResearch.FourQubitEntropy.AH6.mob]
    rw [hlen]
    exact addL_enc
      (scaleL_enc h (powL_enc (EncL.cons (Enc.ic 1) (EncL.cons (Enc.ic 1) EncL.nil)) _))
      (EncL.cons (Enc.ic 0) ih)

/-- Check that a list of balls is nonempty with all entries valid and enclosing positive numbers. -/
def allPos : List Ball → Bool
  | [] => true
  | a :: p => a.pos && allPos p

theorem allPos_enc {p : List ℝ} {P : List Ball} (hp : EncL p P) (h : allPos P = true) :
    ∀ a ∈ p, 0 < a := by
  induction hp with
  | nil => simp
  | cons h1 hp ih =>
    rename_i x a p P
    have h' : a.pos = true ∧ allPos P = true := by
      have h0 : (a.pos && allPos P) = true := h
      exact Bool.and_eq_true_iff.mp h0
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Enc.pos h1 h'.1
    · exact ih h'.2 y hy


/-! ### Semantics at `ℝ` -/

section RealSemantics

@[simp] theorem ic_real (k : ℤ) : (ic k : ℝ) = (k : ℝ) := rfl

theorem evalL_addL (p q : List ℝ) (x : ℝ) : evalL (addL p q) x = evalL p x + evalL q x := by
  induction p generalizing q with
  | nil => simp [addL, evalL]
  | cons a p ih =>
    cases q with
    | nil => simp [addL, evalL]
    | cons b q => simp only [addL, evalL, ih]; ring

theorem evalL_scaleL (c : ℝ) (p : List ℝ) (x : ℝ) : evalL (scaleL c p) x = c * evalL p x := by
  induction p with
  | nil => simp [scaleL, evalL]
  | cons a p ih =>
    simp only [scaleL, List.map_cons, evalL] at ih ⊢
    rw [ih]; ring

theorem evalL_mulL (p q : List ℝ) (x : ℝ) : evalL (mulL p q) x = evalL p x * evalL q x := by
  induction p with
  | nil => simp [mulL, evalL]
  | cons a p ih =>
    simp only [mulL, evalL_addL, evalL_scaleL, evalL, ih, ic_real]
    push_cast; ring

theorem evalL_powL (p : List ℝ) (n : ℕ) (x : ℝ) : evalL (powL p n) x = (evalL p x) ^ n := by
  induction n with
  | zero => simp [powL, evalL]
  | succ n ih => simp only [powL, evalL_mulL, ih]; ring

theorem hasDerivAt_evalL (p : List ℝ) (x : ℝ) : HasDerivAt (evalL p) (evalL (derL p) x) x := by
  induction p with
  | nil =>
    have : evalL ([] : List ℝ) = fun _ => (0 : ℝ) := by funext y; simp [evalL]
    rw [this]; simpa [derL, evalL] using hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    have e1 : evalL (a :: p) = fun y => a + y * evalL p y := by funext y; rfl
    rw [e1]
    have := (hasDerivAt_const x a).add ((hasDerivAt_id x).mul ih)
    have hd : evalL (derL (a :: p)) x = evalL p x + x * evalL (derL p) x := by
      simp [derL, evalL_addL, evalL]
    rw [hd]
    convert this using 1
    · funext y; simp
    · simp

theorem dl_spec (p : List ℝ) (r e : ℝ) :
    evalL p e = (e - r) * evalL (dl p r).1 e + (dl p r).2 := by
  induction p with
  | nil => simp [dl, evalL]
  | cons a p ih =>
    cases p with
    | nil => simp [dl, evalL]
    | cons b t =>
      have ih' := ih
      simp only [dl, evalL] at ih' ⊢
      rw [ih']; ring

theorem evalL_taylorL (p : List ℝ) (l w : ℝ) : evalL (taylorL p l) w = evalL p (l + w) := by
  induction p with
  | nil => simp [taylorL, evalL]
  | cons a p ih =>
    cases p with
    | nil => simp [taylorL, evalL]
    | cons b t =>
      simp only [taylorL, evalL_addL, evalL_mulL, ih, evalL, ic_real]
      push_cast; ring

theorem evalL_scalePow (d : ℝ) (p : List ℝ) (t : ℝ) : evalL (scalePow d p) t = evalL p (d * t) := by
  induction p with
  | nil => simp [scalePow, evalL]
  | cons a p ih =>
    simp only [scalePow, evalL, evalL_scaleL, ih]; ring

theorem evalL_mob (a : ℝ) (p : List ℝ) (s : ℝ) (hs : 1 + s ≠ 0) :
    (1 + s) ^ p.length * evalL (a :: p) (s / (1 + s)) = evalL (mob (a :: p)) s := by
  induction p generalizing a with
  | nil => simp [mob, evalL, addL, scaleL, powL]
  | cons b p ih =>
    have ih' := ih b
    have hm : evalL (mob (a :: b :: p)) s =
        a * (1 + s) ^ (p.length + 1) + s * evalL (mob (b :: p)) s := by
      rw [mob, evalL_addL, evalL_scaleL, evalL_powL]
      simp only [evalL, List.length_cons, ic_real]
      push_cast; ring
    rw [hm, ← ih']
    simp only [evalL, List.length_cons]
    field_simp
    ring

theorem evalL_nonneg {p : List ℝ} (hp : ∀ a ∈ p, 0 ≤ a) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ evalL p s := by
  induction p with
  | nil => simp [evalL]
  | cons a p ih =>
    simp only [evalL]
    have h1 := hp a (by simp)
    have h2 := ih (fun b hb => hp b (by simp [hb]))
    exact add_nonneg h1 (mul_nonneg hs h2)

theorem evalL_pos {a : ℝ} {p : List ℝ} (hp : ∀ b ∈ a :: p, 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    0 < evalL (a :: p) s := by
  simp only [evalL]
  have h1 := hp a (by simp)
  have h2 := evalL_nonneg (p := p) (fun b hb => (hp b (by simp [hb])).le) hs
  exact add_pos_of_pos_of_nonneg h1 (mul_nonneg hs h2)

theorem evalL_pos' {L : List ℝ} (hne : L ≠ []) (hp : ∀ b ∈ L, 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    0 < evalL L s := by
  cases L with
  | nil => exact absurd rfl hne
  | cons a p => exact evalL_pos hp hs

/-- **Bernstein certificate.** If every entry of `mob (scalePow (h-l) (taylorL p l))` is positive (and the
list is nonempty), then `p > 0` on `[l, h)`. -/
theorem pos_on_interval (p : List ℝ) {l h : ℝ} (hlh : l < h)
    (hpos : ∀ c ∈ mob (scalePow (h - l) (taylorL p l)), 0 < c)
    (hne : mob (scalePow (h - l) (taylorL p l)) ≠ []) :
    ∀ e, l ≤ e → e < h → 0 < evalL p e := by
  intro e hle hlt
  generalize hP : scalePow (h - l) (taylorL p l) = P at hpos hne
  have hPe : ∀ t, evalL P t = evalL p (l + (h - l) * t) := by
    intro t
    rw [← hP, evalL_scalePow, evalL_taylorL]
  rcases P with _ | ⟨a, P'⟩
  · simp [mob] at hne
  · set s : ℝ := (e - l) / (h - e) with hs
    have hhe : 0 < h - e := by linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hhe.le
    have h1s : 1 + s = (h - l) / (h - e) := by rw [hs]; field_simp; ring
    have h1s0 : 0 < 1 + s := by rw [h1s]; exact div_pos (by linarith) hhe
    have ht : s / (1 + s) = (e - l) / (h - l) := by
      rw [h1s, hs]; field_simp
    have hm := evalL_mob a P' s h1s0.ne'
    have hmpos : 0 < evalL (mob (a :: P')) s := by
      exact evalL_pos' hne hpos hs0
    rw [← hm] at hmpos
    have hpowpos : 0 < (1 + s) ^ P'.length := pow_pos h1s0 _
    have hE : 0 < evalL (a :: P') (s / (1 + s)) := by
      by_contra hcon; push Not at hcon
      have := mul_nonpos_of_nonneg_of_nonpos hpowpos.le hcon
      linarith
    rw [hPe, ht] at hE
    have hhl : h - l ≠ 0 := by linarith
    have : l + (h - l) * ((e - l) / (h - l)) = e := by field_simp; ring
    rwa [this] at hE

theorem pos_on_interval' (p : List ℝ) {l h d : ℝ} (hlh : l < h) (hd : d = h - l)
    (hpos : ∀ c ∈ mob (scalePow d (taylorL p l)), 0 < c)
    (hne : mob (scalePow d (taylorL p l)) ≠ []) :
    ∀ e, l ≤ e → e < h → 0 < evalL p e := by
  subst hd; exact pos_on_interval p hlh hpos hne

/-- Positive Taylor coefficients at `l` give positivity on `[l, ∞)`. -/
theorem pos_on_tail (p : List ℝ) (l : ℝ)
    (hpos : ∀ c ∈ taylorL p l, 0 < c) (hne : taylorL p l ≠ []) :
    ∀ e, l ≤ e → 0 < evalL p e := by
  intro e hle
  have := evalL_pos' hne hpos (sub_nonneg.2 hle : 0 ≤ e - l)
  rwa [evalL_taylorL, add_sub_cancel] at this

end RealSemantics

end FormalResearch.FourQubitEntropy.AH6

module

public import Mathlib
public import FormalResearch.Wigner.OrthogRec
public import FormalResearch.Wigner.Symmetry

/-!
# Racah Egorov relations, entrywise form

Source: Weyl/P5 `prop:racah-egorov`, together with DLMF 34.5.11-13.  With
`R(a,d) = √((2a+1)(2d+1)) {a b c; d e f}`, the library theorem `sixJ_recurrence_ext` (DLMF
34.5.11, valid for every rational entry with zero extension) is rewritten as the entrywise
Jacobi relation `link(a) R(a+1,d) + link(a-1) R(a-1,d) + diag(a) R(a,d) = d(d+1) R(a,d)`
(`p5a_racah_egorov_first`), the first identity `J^{(a)} R = R D_d` of the paper read at row `a`
and column `d`; and, through the tetrahedral symmetry `sixJ_exch12`, the same relation in the
opposite edge (`p5a_racah_egorov_second`), the second identity `D_a R = R J^{(d)}` read at
`(a, d)`.  The link and diagonal are identified with the paper's `α_h²` and `β_h` at `h = 1`
(`p5a_link_sq_eq_alphaSq`, `p5a_diag_eq_beta`), and the printed Weyl-coordinate coefficients are
shown to be even in `h` (a one-line polynomial identity, `p5a_alphaSq_even`, `p5a_beta_even`).
The general-`h` scaling of the coefficients is not proved beyond that parity.

Not formalised: the packaging into finite matrices (the admissible ladders and the vanishing of
the boundary terms there), the case `a = 0` (where `diag` is a `0/0` with a continuous
extension), orthogonality of `R` as a matrix (the entries' orthogonality is
`sixJ_orthogonality`), the translation of the coefficients to Weyl coordinates beyond their
parity, and the operator discriminant formula.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open FormalResearch.Wigner

/-- The polynomial `T_h` from the Weyl-coordinate Jacobi diagonal coefficient. -/
noncomputable def p5a_T (h X B C E F : ℝ) : ℝ :=
  (X ^ 2 - h ^ 2 / 4) * (-X ^ 2 + B ^ 2 + C ^ 2 - h ^ 2 / 4) +
    (E ^ 2 - h ^ 2 / 4) * (X ^ 2 + B ^ 2 - C ^ 2 - h ^ 2 / 4) +
    (F ^ 2 - h ^ 2 / 4) * (X ^ 2 - B ^ 2 + C ^ 2 - h ^ 2 / 4)

/-- The squared off-diagonal Jacobi coefficient from `prop:racah-egorov`. -/
noncomputable def p5a_alphaSq (h X B C E F : ℝ) : ℝ :=
  ((X ^ 2 - (B - C) ^ 2) * ((B + C) ^ 2 - X ^ 2) *
    (X ^ 2 - (E - F) ^ 2) * ((E + F) ^ 2 - X ^ 2)) /
      (4 * X ^ 2 * (4 * X ^ 2 - h ^ 2))

/-- The diagonal Jacobi coefficient from `prop:racah-egorov`. -/
noncomputable def p5a_beta (h X B C E F : ℝ) : ℝ :=
  p5a_T h X B C E F / (2 * (X ^ 2 - h ^ 2 / 4))

/-- The Weyl-coordinate off-diagonal coefficient is even in the lattice spacing. -/
theorem p5a_alphaSq_even (h X B C E F : ℝ) :
    p5a_alphaSq (-h) X B C E F = p5a_alphaSq h X B C E F := by
  simp [p5a_alphaSq]

/-- The Weyl-coordinate diagonal coefficient is even in the lattice spacing. -/
theorem p5a_beta_even (h X B C E F : ℝ) :
    p5a_beta (-h) X B C E F = p5a_beta h X B C E F := by
  simp [p5a_beta, p5a_T]

/-- info: 'FormalResearch.EuclTet.p5a_alphaSq_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_alphaSq_even

/-- info: 'FormalResearch.EuclTet.p5a_beta_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_beta_even


/-- The Racah matrix entry `√((2a+1)(2d+1)) {a b c; d e f}`. -/
noncomputable def p5a_R (a b c d e f : ℚ) : ℝ :=
  Real.sqrt ((2 * (a : ℝ) + 1) * (2 * (d : ℝ) + 1)) * sixJ a b c d e f

/-- The symmetrised Jacobi link between rows `a` and `a+1`. -/
noncomputable def p5a_link (b c e f a : ℝ) : ℝ :=
  E6 b c e f (a + 1) / (2 * (a + 1) * Real.sqrt ((2 * a + 1) * (2 * a + 3)))

/-- The Jacobi diagonal (with the `d(d+1)` term of the recurrence separated off). -/
noncomputable def p5a_diag (b c e f a : ℝ) : ℝ :=
  -(((c * (c + 1) + b * (b + 1) - a * (a + 1)) * (f * (f + 1) + e * (e + 1) - a * (a + 1))) -
      2 * (c * (c + 1) * (f * (f + 1)) + b * (b + 1) * (e * (e + 1)))) / (2 * a * (a + 1))

lemma p5a_sixJ_pred_zero (a b c d e f : ℚ) (ha : a < 1) : sixJ (a - 1) b c d e f = 0 := by
  apply sixJ_eq_zero_of_not_tri12
  rintro ⟨⟨⟨n1, h1⟩, ⟨n2, h2⟩, _⟩, _⟩
  have : (0 : ℚ) ≤ (n1 : ℚ) + n2 := by positivity
  linarith

lemma p5a_sqrt_pair (x y : ℝ) (hx : 0 < x) : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y :=
  Real.sqrt_mul hx.le y

/-- **First Egorov relation, entrywise** (`prop:racah-egorov`, `J^{(a)} R = R D_d`): for every
rational `a > 0` and all rational labels, including those outside the physical ladder (where the
zero-extended symbols vanish and no boundary term arises). -/
theorem p5a_racah_egorov_first (a b c d e f : ℚ) (ha : 0 < a) :
    p5a_link b c e f a * p5a_R (a + 1) b c d e f +
        p5a_link b c e f ((a : ℝ) - 1) * p5a_R (a - 1) b c d e f +
        p5a_diag b c e f a * p5a_R a b c d e f =
      (d : ℝ) * (d + 1) * p5a_R a b c d e f := by
  have hrec := sixJ_recurrence_ext a b c d e f
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hs : 0 < Real.sqrt (2 * (a : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have ht : 0 < Real.sqrt (2 * (a : ℝ) + 3) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (2 * (a : ℝ) + 1) ^ 2 = 2 * a + 1 := Real.sq_sqrt (by linarith)
  set s := Real.sqrt (2 * (a : ℝ) + 1) with hsdef
  set t := Real.sqrt (2 * (a : ℝ) + 3) with htdef
  set q := Real.sqrt (2 * (d : ℝ) + 1) with hqdef
  have hqR (x : ℝ) (hx : 0 ≤ 2 * x + 1) :
      Real.sqrt ((2 * x + 1) * (2 * (d : ℝ) + 1)) = Real.sqrt (2 * x + 1) * q := by
    rw [Real.sqrt_mul hx]
  have hRa : p5a_R a b c d e f = s * q * sixJ a b c d e f := by
    unfold p5a_R; rw [hqR _ (by linarith)]
  have hRp : p5a_R (a + 1) b c d e f = t * q * sixJ (a + 1) b c d e f := by
    unfold p5a_R; push_cast
    rw [show 2 * ((a : ℝ) + 1) + 1 = 2 * a + 3 by ring,
      Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * a + 3)]
  have hlp : p5a_link b c e f a = E6 b c e f ((a : ℝ) + 1) / (2 * (a + 1) * (s * t)) := by
    unfold p5a_link
    rw [Real.sqrt_mul (by linarith)]
  have hlow : p5a_link b c e f ((a : ℝ) - 1) * p5a_R (a - 1) b c d e f =
      E6 b c e f a / (2 * a * s) * q * sixJ (a - 1) b c d e f := by
    rcases lt_or_ge a 1 with h1 | h1
    · rw [p5a_sixJ_pred_zero a b c d e f h1]
      unfold p5a_R
      rw [p5a_sixJ_pred_zero a b c d e f h1]; simp
    · have h1R : (1 : ℝ) ≤ a := by exact_mod_cast h1
      have hu : 0 < Real.sqrt (2 * (a : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
      unfold p5a_link p5a_R
      push_cast
      rw [sub_add_cancel, show 2 * ((a : ℝ) - 1) + 1 = 2 * a - 1 by ring,
        show 2 * ((a : ℝ) - 1) + 3 = 2 * a + 1 by ring,
        Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * a - 1),
        Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * a - 1)]
      field_simp
      simp only [hsdef, hqdef]; ring
  rw [hlow, hlp, hRp, hRa]
  unfold p5a_diag
  have hrec' := hrec
  rw [← hs2] at hrec'
  generalize sixJ a b c d e f = S0 at *
  generalize sixJ (a + 1) b c d e f = Sp at *
  generalize sixJ (a - 1) b c d e f = Sm at *
  generalize E6 b c e f ((a : ℝ) + 1) = E1 at *
  generalize E6 b c e f (a : ℝ) = E0 at *
  field_simp
  linear_combination (-q) * hrec'


/-- `R` is symmetric under the exchange of upper and lower entries in columns 1 and 2. -/
lemma p5a_R_exch (a b c d e f : ℚ) : p5a_R d e c a b f = p5a_R a b c d e f := by
  unfold p5a_R
  rw [sixJ_exch12 a b c d e f, mul_comm (2 * (d : ℝ) + 1)]

/-- info: 'FormalResearch.EuclTet.p5a_racah_egorov_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_racah_egorov_first

/-- **Second Egorov relation, entrywise** (`prop:racah-egorov`, `D_a R = R J^{(d)}`): the
first relation in the opposite edge `d`, whose Jacobi data are those of the labels
`(e, c, b, f)`; by the symmetry `sixJ_exch12` the matrix entries `R(a, d')` are the same. -/
theorem p5a_racah_egorov_second (a b c d e f : ℚ) (hd : 0 < d) :
    p5a_link e c b f d * p5a_R a b c (d + 1) e f +
        p5a_link e c b f ((d : ℝ) - 1) * p5a_R a b c (d - 1) e f +
        p5a_diag e c b f d * p5a_R a b c d e f =
      (a : ℝ) * (a + 1) * p5a_R a b c d e f := by
  have h := p5a_racah_egorov_first d e c a b f hd
  rw [p5a_R_exch a b c (d + 1) e f, p5a_R_exch a b c (d - 1) e f, p5a_R_exch a b c d e f] at h
  exact h

/-- info: 'FormalResearch.EuclTet.p5a_racah_egorov_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_racah_egorov_second


/-- The diagonal of the entrywise relation is the paper's `β_h` at `h = 1`, in the Weyl
coordinates `X = a + 1/2` and `B = b + 1/2`, etc. -/
theorem p5a_diag_eq_beta (a b c e f : ℚ) (ha : 0 < a) :
    p5a_diag b c e f a =
      p5a_beta 1 ((a : ℝ) + 1 / 2) ((b : ℝ) + 1 / 2) ((c : ℝ) + 1 / 2) ((e : ℝ) + 1 / 2)
        ((f : ℝ) + 1 / 2) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  unfold p5a_diag p5a_beta p5a_T
  have h1 : (a : ℝ) * (a + 1) ≠ 0 := by positivity
  have h2 : 2 * (((a : ℝ) + 1 / 2) ^ 2 - 1 ^ 2 / 4) = 2 * a * (a + 1) := by ring
  rw [h2]
  congr 1
  ring

/-- The squared link is the paper's `α_h²` at `h = 1`, `X = a + 1` (the link midpoint), `B = b + 1/2`,
etc., whenever the radicand of `E6` is nonnegative (the physical range). -/
theorem p5a_link_sq_eq_alphaSq (a b c e f : ℚ) (ha : 0 ≤ a)
    (hE : 0 ≤ (((a : ℝ) + 1) ^ 2 - ((b : ℝ) - c) ^ 2) * (((b : ℝ) + c + 1) ^ 2 - ((a : ℝ) + 1) ^ 2) *
      (((a : ℝ) + 1) ^ 2 - ((e : ℝ) - f) ^ 2) * (((e : ℝ) + f + 1) ^ 2 - ((a : ℝ) + 1) ^ 2)) :
    p5a_link b c e f a ^ 2 =
      p5a_alphaSq 1 ((a : ℝ) + 1) ((b : ℝ) + 1 / 2) ((c : ℝ) + 1 / 2) ((e : ℝ) + 1 / 2)
        ((f : ℝ) + 1 / 2) := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  unfold p5a_link p5a_alphaSq E6
  rw [div_pow, mul_pow, Real.sq_sqrt hE, Real.sq_sqrt (by positivity)]
  have h1 : (2 * ((a : ℝ) + 1)) ^ 2 * ((2 * (a : ℝ) + 1) * (2 * a + 3)) ≠ 0 := by positivity
  have h3 : 4 * ((a : ℝ) + 1) ^ 2 * (4 * ((a : ℝ) + 1) ^ 2 - 1 ^ 2) ≠ 0 := by
    have : 0 < 4 * ((a : ℝ) + 1) ^ 2 - 1 ^ 2 := by nlinarith
    positivity
  rw [div_eq_div_iff h1 h3]
  ring

/-- info: 'FormalResearch.EuclTet.p5a_diag_eq_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_diag_eq_beta

/-- info: 'FormalResearch.EuclTet.p5a_link_sq_eq_alphaSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_link_sq_eq_alphaSq

end FormalResearch.EuclTet

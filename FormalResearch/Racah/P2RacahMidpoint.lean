module

public import FormalResearch.Racah.P2RacahRec
public import FormalResearch.Wigner.Regge
public import FormalResearch.Wigner.ThreeJSym

/-!
# The Weyl-midpoint `6j` family and its exact rank recurrence (Weyl P2, `lem:6jrec`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, sections *Setup and the canonical midpoint*,
*Regge plus Weyl shift explains the midpoint*, *Exact centered Racah recurrence*.

## Dictionary (paper symbol -> Lean symbol)

All labels are rational numbers (integer and half-integer spins alike); real quantities are casts.

| paper | Lean |
|---|---|
| `W_f(a,b,c;m,n) = {a b c; b+m a+n f}` (`eq:6jfamily`) | `W6 a b c f m n` |
| `A = a+(n+1)/2`, `B = b+(m+1)/2`, `C = c+1/2` (`eq:ABC`) | `wA a n`, `wB b m`, `wC c` |
| `x = (A²+B²-C²)/(2AB)` (`eq:centerangle`) | `cosA A B C` |
| `ξ = a+b+c+f+n`, `Φ_f = (-1)^ξ 2√(AB) W_f` (`eq:6jPhi`) | `Phi6 a b c f m n` (the sign is the zero-extended `sgn ξ`) |
| `R_k = √((k²-m²)(k²-n²))` (`eq:6jR`) | `rootR m n k` |
| `η_k = √((1-k²/4A²)(1-k²/4B²))` (`eq:etak`) | `etaK A B k` |
| `q_f = (2f(f+1)+1-m²-n²)/(8AB)` (`eq:qf`) | `qf f m n A B` |

`sgn ξ` is `(-1)^ξ` when `ξ` is an integer (which every admissible point has) and `0` otherwise.

## Results

* `W6_swap_ab`, `W6_exch_ab`, `Phi6_swap_ab`, `Phi6_exch_ab`: the two exact symmetry reductions to the
  canonical sector `m ≥ |n|`, `m ≥ 0` (`eq:canonicalsector` and the text after it), with the phase
  `(-1)^(m-n)`.
* `weyl_shift_pairs`: `eq:symmetricpairs`.
* `W6_eq_rank_form`, `W6_eq_regge_form`, `W6_regge_midpoint`: the column-permutation bridge from the
  paper's `W_f` to `{f b+m b; c a a+n}` (the form to which DLMF 34.5.11 is applied) and to
  `{c a b; f b+m a+n}` (the form to which Regge 34.5.9 is applied); `W6_regge_midpoint` is `eq:6jRegge`.
* `E6_midpoint`: `eq:Ek`, `E(k) = 4AB R_k η_k`.
* `diag_identity`: `eq:diagidentity`.
* `Phi6_midpoint_recurrence`: `lem:6jrec` (`eq:6jrec`), for every `f` for which the two triads
  `(f, b+m, b)` and `(f, a, a+n)` are admissible, i.e. on the whole physical `f`-range including its
  two boundary rows (where `Φ_{f-1}` resp. `Φ_{f+1}` is the zero extension and its coefficient
  vanishes).
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-- `W_f(a,b,c;m,n) = {a b c; b+m a+n f}` (`eq:6jfamily`). -/
noncomputable def W6 (a b c f m n : ℚ) : ℝ := sixJ a b c (b + m) (a + n) f

/-- `A = a + (n+1)/2` (`eq:ABC`). -/
noncomputable def wA (a n : ℚ) : ℝ := (a : ℝ) + ((n : ℝ) + 1) / 2

/-- `B = b + (m+1)/2` (`eq:ABC`). -/
noncomputable def wB (b m : ℚ) : ℝ := (b : ℝ) + ((m : ℝ) + 1) / 2

/-- `C = c + 1/2` (`eq:ABC`). -/
noncomputable def wC (c : ℚ) : ℝ := (c : ℝ) + 1 / 2

/-- The centered angle `x = (A²+B²-C²)/(2AB)` (`eq:centerangle`). -/
noncomputable def cosA (A B C : ℝ) : ℝ := (A ^ 2 + B ^ 2 - C ^ 2) / (2 * A * B)

/-- `q_f = (2f(f+1)+1-m²-n²)/(8AB)` (`eq:qf`). -/
noncomputable def qf (f m n A B : ℝ) : ℝ := (2 * f * (f + 1) + 1 - m ^ 2 - n ^ 2) / (8 * A * B)

/-- `R_k = √((k²-m²)(k²-n²))` (`eq:6jR`). -/
noncomputable def rootR (m n k : ℝ) : ℝ := Real.sqrt ((k ^ 2 - m ^ 2) * (k ^ 2 - n ^ 2))

/-- `η_k = √((1-k²/(4A²))(1-k²/(4B²)))` (`eq:etak`). -/
noncomputable def etaK (A B k : ℝ) : ℝ :=
  Real.sqrt ((1 - k ^ 2 / (4 * A ^ 2)) * (1 - k ^ 2 / (4 * B ^ 2)))

/-- The normalised kernel `Φ_f = (-1)^ξ 2√(AB) W_f`, `ξ = a+b+c+f+n` (`eq:6jPhi`). -/
noncomputable def Phi6 (a b c f m n : ℚ) : ℝ :=
  sgn (a + b + c + f + n) * (2 * Real.sqrt (wA a n * wB b m)) * W6 a b c f m n

/-! ### Column-permutation bridge and `eq:6jRegge` -/

/-- Cyclic column permutation `{j₁ j₂ j₃; l₁ l₂ l₃} = {j₃ j₁ j₂; l₃ l₁ l₂}`. -/
lemma sixJ_cyc (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₃ j₁ j₂ l₃ l₁ l₂ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  rw [← sixJ_swap23 j₁ j₂ j₃ l₁ l₂ l₃, sixJ_swap12 j₁ j₃ j₂ l₁ l₃ l₂]

/-- `W_f = {c a b; f b+m a+n}`: the paper's "permute the columns" before `eq:6jRegge`. -/
theorem W6_eq_regge_form (a b c f m n : ℚ) :
    W6 a b c f m n = sixJ c a b f (b + m) (a + n) := by
  unfold W6
  rw [sixJ_cyc a b c (b + m) (a + n) f]

/-- `W_f = {f b+m b; c a a+n}`: the form to which DLMF 34.5.11 is applied in the rank `f`. -/
theorem W6_eq_rank_form (a b c f m n : ℚ) :
    W6 a b c f m n = sixJ f (b + m) b c a (a + n) := by
  rw [W6_eq_regge_form, sixJ_exch12 c a b f (b + m) (a + n)]

/-- **`eq:6jRegge`** (Regge symmetry DLMF 34.5.9 after the column permutation). -/
theorem W6_regge_midpoint (a b c f m n : ℚ) :
    W6 a b c f m n =
      sixJ c (b + (m - n) / 2) (a + (n - m) / 2) f (a + (m + n) / 2) (b + (m + n) / 2) := by
  rw [W6_eq_regge_form]
  exact sixJ_regge1_shifted a b c f m n

/-- `eq:symmetricpairs`: after the Weyl shift `j ↦ j + 1/2`, the five large entries of `eq:6jRegge`
become `C`, `B - n/2`, `A - m/2`, `A + m/2`, `B + n/2` (`A = wA a n`, `B = wB b m`, `C = wC c`). -/
theorem weyl_shift_pairs (a b c m n : ℚ) :
    (((c : ℝ) + 1 / 2) = wC c) ∧
    (((b + (m - n) / 2 : ℚ) : ℝ) + 1 / 2 = wB b m - n / 2) ∧
    (((a + (n - m) / 2 : ℚ) : ℝ) + 1 / 2 = wA a n - m / 2) ∧
    (((a + (m + n) / 2 : ℚ) : ℝ) + 1 / 2 = wA a n + m / 2) ∧
    (((b + (m + n) / 2 : ℚ) : ℝ) + 1 / 2 = wB b m + n / 2) := by
  unfold wA wB wC
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> ring

/-! ### The two symmetry reductions to the canonical sector (`eq:canonicalsector`) -/

/-- Interchanging the first two columns: `(a,b;m,n;A,B) ↦ (b,a;n,m;B,A)`. -/
theorem W6_swap_ab (a b c f m n : ℚ) : W6 b a c f n m = W6 a b c f m n := by
  unfold W6
  exact sixJ_swap12 a b c (b + m) (a + n) f

/-- Interchanging upper and lower entries in the first two columns and then swapping those
columns: `(a,b;m,n) ↦ (a+n, b+m; -m, -n)`. -/
theorem W6_exch_ab (a b c f m n : ℚ) : W6 (a + n) (b + m) c f (-m) (-n) = W6 a b c f m n := by
  unfold W6
  rw [show b + m + -m = b by ring, show a + n + -n = a by ring]
  rw [sixJ_swap12 (b + m) (a + n) c a b f]
  exact sixJ_exch12 a b c (b + m) (a + n) f

/-- The centered variables are invariant under the second reduction. -/
theorem wA_exch (a n : ℚ) : wA (a + n) (-n) = wA a n := by
  unfold wA; push_cast; ring

theorem wB_exch (b m : ℚ) : wB (b + m) (-m) = wB b m := by
  unfold wB; push_cast; ring

/-- The first reduction exchanges `A` and `B`, and `Φ` changes by the phase `(-1)^(m-n)`
(`m - n = k ∈ ℤ`). -/
theorem Phi6_swap_ab (a b c f m n : ℚ) (k : ℤ) (hk : m - n = k) :
    Phi6 b a c f n m = (-1 : ℝ) ^ k * Phi6 a b c f m n := by
  unfold Phi6
  rw [W6_swap_ab, show b + a + c + f + m = (a + b + c + f + n) + k by linarith, sgn_add_int]
  have : wA b m * wB a n = wA a n * wB b m := by unfold wA wB; ring
  rw [this]
  ring

/-- The second reduction: `Φ` changes by the phase `(-1)^(m-n)` (`m - n = k ∈ ℤ`), `A`, `B` fixed. -/
theorem Phi6_exch_ab (a b c f m n : ℚ) (k : ℤ) (hk : m - n = k) :
    Phi6 (a + n) (b + m) c f (-m) (-n) = (-1 : ℝ) ^ k * Phi6 a b c f m n := by
  unfold Phi6
  rw [W6_exch_ab, show a + n + (b + m) + c + f + -n = (a + b + c + f + n) + k by linarith,
    sgn_add_int, wA_exch, wB_exch]
  ring

/-! ### The exact algebra of the recurrence -/

lemma E_alg (A B k m n : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    (k ^ 2 - m ^ 2) * ((2 * B) ^ 2 - k ^ 2) * (k ^ 2 - n ^ 2) * ((2 * A) ^ 2 - k ^ 2) =
      ((k ^ 2 - m ^ 2) * (k ^ 2 - n ^ 2)) *
        ((4 * A * B) ^ 2 * ((1 - k ^ 2 / (4 * A ^ 2)) * (1 - k ^ 2 / (4 * B ^ 2)))) := by
  field_simp
  ring

/-- **`eq:Ek`**: `E(k) = 4AB R_k η_k`, with `E` of DLMF 34.5.13 for the entries `(b+m, b; a, a+n)`
(`2B = 2b+m+1`, `2A = 2a+n+1`), when `(k²-m²)(k²-n²) ≥ 0` and `A, B > 0`. -/
theorem E6_midpoint (a b m n k : ℝ) (hP : 0 ≤ (k ^ 2 - m ^ 2) * (k ^ 2 - n ^ 2))
    (hA : 0 < a + (n + 1) / 2) (hB : 0 < b + (m + 1) / 2) :
    E6 (b + m) b a (a + n) k =
      4 * (a + (n + 1) / 2) * (b + (m + 1) / 2) *
        (rootR m n k * etaK (a + (n + 1) / 2) (b + (m + 1) / 2) k) := by
  unfold E6 rootR etaK
  have e : (k ^ 2 - (b + m - b) ^ 2) * ((b + m + b + 1) ^ 2 - k ^ 2) *
      (k ^ 2 - (a - (a + n)) ^ 2) * ((a + (a + n) + 1) ^ 2 - k ^ 2) =
      (k ^ 2 - m ^ 2) * ((2 * (b + (m + 1) / 2)) ^ 2 - k ^ 2) * (k ^ 2 - n ^ 2) *
        ((2 * (a + (n + 1) / 2)) ^ 2 - k ^ 2) := by ring
  rw [e, E_alg _ _ _ _ _ hA.ne' hB.ne', Real.sqrt_mul hP, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]
  ring

lemma diag_alg (A B c f m n : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    (((B - (m + 1) / 2) * ((B - (m + 1) / 2) + 1) +
          ((B - (m + 1) / 2) + m) * ((B - (m + 1) / 2) + m + 1) - f * (f + 1)) *
        ((((A - (n + 1) / 2) + n) * ((A - (n + 1) / 2) + n + 1)) +
          (A - (n + 1) / 2) * ((A - (n + 1) / 2) + 1) - f * (f + 1)) -
      2 * ((B - (m + 1) / 2) * ((B - (m + 1) / 2) + 1) *
          (((A - (n + 1) / 2) + n) * ((A - (n + 1) / 2) + n + 1)) +
        ((B - (m + 1) / 2) + m) * ((B - (m + 1) / 2) + m + 1) *
          ((A - (n + 1) / 2) * ((A - (n + 1) / 2) + 1)) - f * (f + 1) * (c * (c + 1)))) =
      -4 * A * B * (f * (f + 1) * (cosA A B (c + 1 / 2) - qf f m n A B) - m * n) := by
  unfold cosA qf
  field_simp
  ring

/-- **`eq:diagidentity`**: the diagonal coefficient of DLMF 34.5.11 for `{f b+m b; c a a+n}` equals
`-4AB {f(f+1)[x-q_f] - mn}`, `x = cosA A B C`, `C = c + 1/2`. -/
theorem diag_identity (a b c f m n : ℝ) (hA : a + (n + 1) / 2 ≠ 0) (hB : b + (m + 1) / 2 ≠ 0) :
    ((b * (b + 1) + (b + m) * (b + m + 1) - f * (f + 1)) *
        (((a + n) * (a + n + 1)) + a * (a + 1) - f * (f + 1)) -
      2 * (b * (b + 1) * ((a + n) * (a + n + 1)) + (b + m) * (b + m + 1) * (a * (a + 1)) -
        f * (f + 1) * (c * (c + 1)))) =
      -4 * (a + (n + 1) / 2) * (b + (m + 1) / 2) *
        (f * (f + 1) * (cosA (a + (n + 1) / 2) (b + (m + 1) / 2) (c + 1 / 2) -
          qf f m n (a + (n + 1) / 2) (b + (m + 1) / 2)) - m * n) := by
  have := diag_alg (a + (n + 1) / 2) (b + (m + 1) / 2) c f m n hA hB
  simpa only [add_sub_cancel_right] using this

lemma sgn_sub_one (x : ℚ) : sgn (x - 1) = - sgn x := by
  have := sgn_add_one (x - 1)
  rw [sub_add_cancel] at this
  linarith

/-- Admissibility of the two triads at `f` gives the sign and size facts used below. -/
lemma admissible_facts {a b f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    0 < wA a n ∧ 0 < wB b m ∧ 0 ≤ (f : ℝ) ^ 2 - (m : ℝ) ^ 2 ∧ 0 ≤ (f : ℝ) ^ 2 - (n : ℝ) ^ 2 ∧
      0 ≤ (f : ℝ) := by
  have a1 := h1.1.nonneg_real
  have a2 := h1.2.1.nonneg_real
  have a3 := h1.2.2.nonneg_real
  have b1 := h2.1.nonneg_real
  have b2 := h2.2.1.nonneg_real
  have b3 := h2.2.2.nonneg_real
  push_cast at a1 a2 a3 b1 b2 b3
  have hf : (0 : ℝ) ≤ f := by linarith
  refine ⟨?_, ?_, ?_, ?_, hf⟩
  · unfold wA; linarith
  · unfold wB; linarith
  · nlinarith
  · nlinarith

/-- **`lem:6jrec`, `eq:6jrec`** (Exact midpoint Racah recurrence).
`(2f+1){f(f+1)[x-q_f] - mn} Φ_f = f R_{f+1} η_{f+1} Φ_{f+1} + (f+1) R_f η_f Φ_{f-1}`
with `A = wA a n`, `B = wB b m`, `x = cosA A B (wC c)`.

Valid whenever the two triads containing `f` are admissible, `IsTri f (b+m) b` and
`IsTri f a (a+n)`, i.e. on the whole physical `f`-range including its boundary rows; for the
neighbours `f ± 1`, `Phi6` is the zero extension, and the corresponding coefficient
(`R_f` at `f = max(|m|,|n|)`, `η_{f+1}` at `f+1 = 2 min(A,B)`) vanishes.  No hypothesis on `c` is
needed: if `c` is not physical, every `Φ` vanishes. -/
theorem Phi6_midpoint_recurrence (a b c f m n : ℚ)
    (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    (2 * (f : ℝ) + 1) *
        ((f : ℝ) * (f + 1) * (cosA (wA a n) (wB b m) (wC c) - qf f m n (wA a n) (wB b m)) -
          m * n) * Phi6 a b c f m n =
      (f : ℝ) * (rootR m n (f + 1) * etaK (wA a n) (wB b m) (f + 1)) * Phi6 a b c (f + 1) m n +
        ((f : ℝ) + 1) * (rootR m n f * etaK (wA a n) (wB b m) f) * Phi6 a b c (f - 1) m n := by
  obtain ⟨hA, hB, hfm, hfn, hf⟩ := admissible_facts h1 h2
  have hrec := sixJ_recurrence_of_tri f (b + m) b c a (a + n) h1 h2
  have hdiag := diag_identity (a : ℝ) b c f m n hA.ne' hB.ne'
  have hE1 := E6_midpoint (a : ℝ) b m n ((f : ℝ) + 1)
    (by nlinarith) hA hB
  have hE0 := E6_midpoint (a : ℝ) b m n (f : ℝ) (mul_nonneg hfm hfn) hA hB
  rw [← W6_eq_rank_form, ← W6_eq_rank_form, ← W6_eq_rank_form] at hrec
  unfold Phi6
  rw [show a + b + c + (f + 1) + n = (a + b + c + f + n) + 1 by ring, sgn_add_one,
    show a + b + c + (f - 1) + n = (a + b + c + f + n) - 1 by ring, sgn_sub_one]
  push_cast at hrec hE1 hE0
  unfold wA wB wC at *
  have hAB : 4 * ((a : ℝ) + (n + 1) / 2) * ((b : ℝ) + (m + 1) / 2) ≠ 0 := by positivity
  apply mul_left_cancel₀ hAB
  rw [hE1, hE0] at hrec
  rw [hdiag] at hrec
  linear_combination (-(sgn (a + b + c + f + n) * (2 * Real.sqrt (((a : ℝ) + (n + 1) / 2) *
    ((b : ℝ) + (m + 1) / 2))))) * hrec

/-- info: 'FormalResearch.Racah.SixJ.Phi6_midpoint_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_midpoint_recurrence

/-- info: 'FormalResearch.Racah.SixJ.W6_regge_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms W6_regge_midpoint

end FormalResearch.Racah.SixJ

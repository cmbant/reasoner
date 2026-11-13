module

public import FormalResearch.Racah.P2RacahMidpoint
public import FormalResearch.Racah.AbsLatticeIdentity
public import FormalResearch.Racah.WeylCellWidth

/-!
# The finite Racah system on the physical `c`-lattice: the exact algebra (Weyl P2, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, section *Exact finite Racah spectral system on
the physical `c`-lattice* (`sec:6jcspectral`).  This file contains the parts of the proof of
`thm:6jfiniteRacah` that do not use the orthogonality DLMF 34.5.14: the finite lattice
(`eq:cminRacah`-`eq:Racahdimension`), the edge factor and its closure at the two ends, the
detailed-balance identity (`eq:RacahDetailedBalance`), the diagonal coefficient
(`eq:RacahD0factor`), and the eigenvalue equation `H_R Φ_f = f(f+1) Φ_f` of the Hamiltonian
`eq:RacahHamiltonian` for every row with `c > 0`.

## Dictionary (paper symbol -> Lean symbol); `A = wA a n`, `B = wB b m` as in `P2RacahMidpoint`

| paper | Lean |
|---|---|
| `c_min`, `c_max`, `f_0`, `f_1` (`eq:cminRacah`, `eq:cmaxRacah`, `eq:frangeRacah`) | `cMin a b m n`, `cMax a b m n`, `fMin m n`, `fMax a b m n` (rationals) |
| `𝒜(c)²` (`eq:Racahcedgefactor`) | `edgeA2 a b m n c` |
| `𝒜(c)` (nonnegative root) | `edgeA a b m n c` |
| `z_c = c(c+1)` | `zc c` |
| `κ_R`, `Ω_R` (`eq:Racahkappa`, `eq:RacahOmega`) | `kapR A B m n`, `omegaR A B m n` |
| `a_c^±`, `b_c` (`eq:Racahoffdiag`, `eq:Racahdiag`) | `aPlus a b m n c`, `aMinus a b m n c`, `bDiag A B m n c` |
| `ω_c = (2c+1)/(2AB)` (`eq:Racahweightcell`) | `omegaW A B c` |

## Results

* `cMin_centered`, `cMax_centered`, `fMax_centered`, `cMax_sub_cMin` (`eq:Racahdimension`).
* `edgeA_cMin`, `edgeA_cMax_succ`: `𝒜(c_min) = 0 = 𝒜(c_max+1)`.
* `omegaW_aPlus`, `omegaW_succ_aMinus`: `eq:RacahDetailedBalance`.
* `D0_factor`: `eq:RacahD0factor`.
* `Phi6_lattice_eigen`: the row of `H_R Φ_f = f(f+1) Φ_f` for `c > 0`, any `f`, in the
  zero-extended sense (`Φ_f(c) = 0` off the physical lattice); it uses the whole `c`-lattice
  recurrence including the two end rows.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-! ### The finite lattice -/

/-- `c_min = max{|a-b|, |b+m-a-n|}` (`eq:cminRacah`). -/
def cMin (a b m n : ℚ) : ℚ := max |a - b| |b + m - a - n|

/-- `c_max = min{a+b, a+b+m+n}` (`eq:cmaxRacah`). -/
def cMax (a b m n : ℚ) : ℚ := min (a + b) (a + b + m + n)

/-- `f_0 = max(|m|,|n|)` (`eq:frangeRacah`). -/
def fMin (m n : ℚ) : ℚ := max |m| |n|

/-- `f_1 = min(2a+n, 2b+m)` (`eq:frangeRacah`). -/
def fMax (a b m n : ℚ) : ℚ := min (2 * a + n) (2 * b + m)

/-- `c_min = |A-B| + |m-n|/2` with `A = a+(n+1)/2`, `B = b+(m+1)/2`. -/
theorem cMin_centered (a b m n : ℚ) :
    cMin a b m n = |(a + (n + 1) / 2) - (b + (m + 1) / 2)| + |m - n| / 2 := by
  unfold cMin
  have e : (a + (n + 1) / 2) - (b + (m + 1) / 2) = (a - b) - (m - n) / 2 := by ring
  rw [e]
  rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases (b + m - a - n) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rcases abs_cases (a - b - (m - n) / 2) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
  rcases abs_cases (m - n) with ⟨h7, h8⟩ | ⟨h7, h8⟩ <;>
  simp only [max_def] <;> split_ifs <;> linarith

/-- `c_max = A+B-1-|m+n|/2`. -/
theorem cMax_centered (a b m n : ℚ) :
    cMax a b m n = (a + (n + 1) / 2) + (b + (m + 1) / 2) - 1 - |m + n| / 2 := by
  unfold cMax
  rcases abs_cases (m + n) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  simp only [min_def] <;> split_ifs <;> linarith

/-- `f_1 = 2 min(A,B) - 1`. -/
theorem fMax_centered (a b m n : ℚ) :
    fMax a b m n = 2 * min (a + (n + 1) / 2) (b + (m + 1) / 2) - 1 := by
  unfold fMax
  simp only [min_def]
  split_ifs <;> linarith

/-- **`eq:Racahdimension`**: `c_max - c_min = f_1 - f_0`. -/
theorem cMax_sub_cMin (a b m n : ℚ) :
    cMax a b m n - cMin a b m n = fMax a b m n - fMin m n := by
  have h := abs_sub_add_abs_add_eq_two_max m n
  unfold fMin
  rw [cMax_centered, cMin_centered, fMax_centered]
  have e : 2 * min (a + (n + 1) / 2) (b + (m + 1) / 2) =
      (a + (n + 1) / 2) + (b + (m + 1) / 2) - |(a + (n + 1) / 2) - (b + (m + 1) / 2)| := by
    rcases abs_cases ((a + (n + 1) / 2) - (b + (m + 1) / 2)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [min_def] <;> split_ifs <;> linarith
  rw [e]
  linarith

/-! ### The edge factor and the closure of the lattice -/

/-- `𝒜(c)²` (`eq:Racahcedgefactor`). -/
noncomputable def edgeA2 (a b m n c : ℝ) : ℝ :=
  (c ^ 2 - (a - b) ^ 2) * ((a + b + 1) ^ 2 - c ^ 2) * (c ^ 2 - (b + m - a - n) ^ 2) *
    ((a + b + m + n + 1) ^ 2 - c ^ 2)

/-- The nonnegative root `𝒜(c)`. -/
noncomputable def edgeA (a b m n c : ℝ) : ℝ := Real.sqrt (edgeA2 a b m n c)

/-- `E(c)` of DLMF 34.5.13 for the entries `(a, b; b+m, a+n)` is the edge factor `𝒜(c)`. -/
theorem E6_edgeA (a b m n x : ℝ) : E6 a b (b + m) (a + n) x = edgeA a b m n x := by
  unfold E6 edgeA edgeA2
  congr 1
  ring

/-- `𝒜(c_min) = 0`. -/
theorem edgeA_cMin (a b m n : ℚ) : edgeA a b m n ((cMin a b m n : ℚ) : ℝ) = 0 := by
  unfold edgeA edgeA2 cMin
  rcases max_choice |a - b| |b + m - a - n| with h | h <;> rw [h]
  · have : (((|a - b| : ℚ)) : ℝ) ^ 2 = ((a : ℝ) - b) ^ 2 := by
      rw [Rat.cast_abs]; push_cast; exact sq_abs _
    rw [this]; simp
  · have : (((|b + m - a - n| : ℚ)) : ℝ) ^ 2 = ((b : ℝ) + m - a - n) ^ 2 := by
      rw [Rat.cast_abs]; push_cast; exact sq_abs _
    rw [this]; simp

/-- `𝒜(c_max + 1) = 0`. -/
theorem edgeA_cMax_succ (a b m n : ℚ) :
    edgeA a b m n (((cMax a b m n : ℚ) : ℝ) + 1) = 0 := by
  unfold edgeA edgeA2 cMax
  rcases min_choice (a + b) (a + b + m + n) with h | h <;> rw [h]
  · have : (((a + b : ℚ) : ℝ) + 1) ^ 2 = ((a : ℝ) + b + 1) ^ 2 := by push_cast; ring
    rw [this]; simp
  · have : (((a + b + m + n : ℚ) : ℝ) + 1) ^ 2 = ((a : ℝ) + b + m + n + 1) ^ 2 := by
      push_cast; ring
    rw [this]; simp

/-! ### Detailed balance -/

/-- `ω_c = (2c+1)/(2AB)` (`eq:Racahweightcell`). -/
noncomputable def omegaW (A B c : ℝ) : ℝ := (2 * c + 1) / (2 * A * B)

/-- `a_c^+ = 𝒜(c+1) / (2(2c+1)(c+1))` (`eq:Racahoffdiag`). -/
noncomputable def aPlus (a b m n c : ℝ) : ℝ := edgeA a b m n (c + 1) / (2 * (2 * c + 1) * (c + 1))

/-- `a_c^- = 𝒜(c) / (2(2c+1)c)` (`eq:Racahoffdiag`). -/
noncomputable def aMinus (a b m n c : ℝ) : ℝ := edgeA a b m n c / (2 * (2 * c + 1) * c)

/-- **`eq:RacahDetailedBalance`**, first equality: `ω_c a_c^+ = 𝒜(c+1) / (4AB(c+1))`. -/
theorem omegaW_aPlus (a b m n A B c : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (hc : 0 ≤ c) :
    omegaW A B c * aPlus a b m n c = edgeA a b m n (c + 1) / (4 * A * B * (c + 1)) := by
  unfold omegaW aPlus
  have h1 : 2 * c + 1 ≠ 0 := by positivity
  have h2 : c + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **`eq:RacahDetailedBalance`**, second equality: `ω_{c+1} a_{c+1}^- = 𝒜(c+1) / (4AB(c+1))`. -/
theorem omegaW_succ_aMinus (a b m n A B c : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) (hc : 0 ≤ c) :
    omegaW A B (c + 1) * aMinus a b m n (c + 1) = edgeA a b m n (c + 1) / (4 * A * B * (c + 1)) := by
  unfold omegaW aMinus
  have h1 : 2 * (c + 1) + 1 ≠ 0 := by positivity
  have h2 : c + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **`eq:Racahcellwidth`**: `ω_c = x̂(c) - x̂(c+1)` with `x̂(s) = (A²+B²-s²)/(2AB)`
(real-valued form of `lawCosines_cell_width`). -/
theorem omegaW_eq_cell_width (A B c : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    omegaW A B c = cosA A B c - cosA A B (c + 1) := by
  unfold omegaW cosA
  field_simp
  ring

/-- `cosA` agrees with the rational law-of-cosines coordinate `lawCosinesX` of `WeylCellWidth`. -/
theorem cosA_eq_lawCosinesX (A B s : ℚ) : cosA A B s = ((lawCosinesX A B s : ℚ) : ℝ) := by
  unfold cosA lawCosinesX
  push_cast
  rfl

/-! ### The diagonal coefficient -/

/-- `z_c = c(c+1)`. -/
noncomputable def zc (c : ℝ) : ℝ := c * (c + 1)

/-- `κ_R = 1 - 2(A²+B²) - (m²+n²)/2` (`eq:Racahkappa`). -/
noncomputable def kapR (A B m n : ℝ) : ℝ := 1 - 2 * (A ^ 2 + B ^ 2) - (m ^ 2 + n ^ 2) / 2

/-- `Ω_R = ((m+n)²-4(A+B)²)((m-n)²-4(A-B)²)/16` (`eq:RacahOmega`). -/
noncomputable def omegaR (A B m n : ℝ) : ℝ :=
  1 / 16 * (((m + n) ^ 2 - 4 * (A + B) ^ 2) * ((m - n) ^ 2 - 4 * (A - B) ^ 2))

/-- `b_c = -(z_c² + κ_R z_c + Ω_R)/(2 z_c)` (`eq:Racahdiag`). -/
noncomputable def bDiag (A B m n c : ℝ) : ℝ :=
  -(zc c ^ 2 + kapR A B m n * zc c + omegaR A B m n) / (2 * zc c)

/-- The part of the DLMF 34.5.11 diagonal coefficient of `{c a b; f b+m a+n}` independent of
`f(f+1)` is `z² + κ_R z + Ω_R` (`eq:RacahD0factor`); the `f(f+1)`-part is `2 z f(f+1)`. -/
theorem D0_factor (A B c f m n : ℝ) :
    (((B - (m + 1) / 2) * ((B - (m + 1) / 2) + 1) + (A - (n + 1) / 2) * ((A - (n + 1) / 2) + 1) -
          c * (c + 1)) *
        (((A - (n + 1) / 2) + n) * ((A - (n + 1) / 2) + n + 1) +
          ((B - (m + 1) / 2) + m) * ((B - (m + 1) / 2) + m + 1) - c * (c + 1)) -
      2 * ((B - (m + 1) / 2) * ((B - (m + 1) / 2) + 1) *
          (((A - (n + 1) / 2) + n) * ((A - (n + 1) / 2) + n + 1)) +
        (A - (n + 1) / 2) * ((A - (n + 1) / 2) + 1) *
          (((B - (m + 1) / 2) + m) * ((B - (m + 1) / 2) + m + 1)) - c * (c + 1) * (f * (f + 1)))) =
      zc c ^ 2 + kapR A B m n * zc c + omegaR A B m n + 2 * zc c * (f * (f + 1)) := by
  unfold zc kapR omegaR
  ring

lemma lattice_alg (c lam D0 P Pp Pm E Ep : ℝ) (hc : 0 < c)
    (K : (2 * c + 1) * (D0 + 2 * (c * (c + 1)) * lam) * P = -(c * Ep * Pp) - (c + 1) * E * Pm) :
    lam * P = -(Ep / (2 * (2 * c + 1) * (c + 1))) * Pp + (-D0 / (2 * (c * (c + 1)))) * P -
      (E / (2 * (2 * c + 1) * c)) * Pm := by
  have h1 : 2 * c + 1 ≠ 0 := by positivity
  have h2 : c + 1 ≠ 0 := by positivity
  have h3 : c ≠ 0 := hc.ne'
  have key : lam * P - (-(Ep / (2 * (2 * c + 1) * (c + 1))) * Pp + (-D0 / (2 * (c * (c + 1)))) * P -
      (E / (2 * (2 * c + 1) * c)) * Pm) =
      ((2 * c + 1) * (D0 + 2 * (c * (c + 1)) * lam) * P + (c * Ep * Pp) + (c + 1) * E * Pm) /
        (2 * c * (c + 1) * (2 * c + 1)) := by
    field_simp
    ring
  have : lam * P - (-(Ep / (2 * (2 * c + 1) * (c + 1))) * Pp + (-D0 / (2 * (c * (c + 1)))) * P -
      (E / (2 * (2 * c + 1) * c)) * Pm) = 0 := by
    rw [key, K]; ring
  linarith

/-- **`thm:6jfiniteRacah`, eigenvalue equation `eq:RacahEigenvectors` for the rows `c > 0`**:
`f(f+1) Φ_f(c) = -a_c^+ Φ_f(c+1) + b_c Φ_f(c) - a_c^- Φ_f(c-1)`, where `Φ_f(c) = Phi6 a b c f m n`,
for `c` physical (`IsTri c a b`, `IsTri c (b+m) (a+n)`).  The end rows are included: at `c_min`
the coefficient `a_c^- ∝ 𝒜(c_min)` vanishes and at `c_max` the coefficient `a_c^+ ∝ 𝒜(c_max+1)`
vanishes, so the zero extension of `Φ_f` outside the lattice is consistent.  Orthogonality
(DLMF 34.5.14) is not used. -/
theorem Phi6_lattice_eigen (a b c f m n : ℚ) (hc : 0 < c)
    (h1 : IsTri c a b) (h2 : IsTri c (b + m) (a + n)) :
    (f : ℝ) * (f + 1) * Phi6 a b c f m n =
      -(aPlus a b m n c * Phi6 a b (c + 1) f m n) + bDiag (wA a n) (wB b m) m n c * Phi6 a b c f m n
        - aMinus a b m n c * Phi6 a b (c - 1) f m n := by
  have hrec := sixJ_recurrence_of_tri c a b f (b + m) (a + n) h1 h2
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hD := D0_factor (wA a n) (wB b m) c f m n
  have hA : wA a n = (a : ℝ) + (n + 1) / 2 := rfl
  have hB : wB b m = (b : ℝ) + (m + 1) / 2 := rfl
  simp only [hA, hB, add_sub_cancel_right] at hD
  rw [← W6_eq_regge_form, ← W6_eq_regge_form, ← W6_eq_regge_form] at hrec
  have hE1 := E6_edgeA a b m n ((c : ℝ) + 1)
  have hE0 := E6_edgeA a b m n (c : ℝ)
  push_cast at hrec hE1 hE0
  rw [hE1, hE0] at hrec
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℝ, D0 = zc c ^ 2 + kapR ((a : ℝ) + (n + 1) / 2) ((b : ℝ) + (m + 1) / 2) m n * zc c +
      omegaR ((a : ℝ) + (n + 1) / 2) ((b : ℝ) + (m + 1) / 2) m n := ⟨_, rfl⟩
  have hrec2 : (2 * (c : ℝ) + 1) * (D0 + 2 * ((c : ℝ) * (c + 1)) * ((f : ℝ) * (f + 1))) *
      W6 a b c f m n = (c : ℝ) * edgeA a b m n ((c : ℝ) + 1) * W6 a b (c + 1) f m n +
        ((c : ℝ) + 1) * edgeA a b m n (c : ℝ) * W6 a b (c - 1) f m n := by
    simp only [zc] at hD0 hD
    linear_combination hrec - ((2 * (c : ℝ) + 1) * W6 a b c f m n) * hD +
      ((2 * (c : ℝ) + 1) * W6 a b c f m n) * hD0
  unfold Phi6
  rw [show a + b + (c + 1) + f + n = (a + b + c + f + n) + 1 by ring, sgn_add_one,
    show a + b + (c - 1) + f + n = (a + b + c + f + n) - 1 by ring, sgn_sub_one]
  set s := sgn (a + b + c + f + n) with hs
  set T := 2 * Real.sqrt (wA a n * wB b m) with hT
  have K : (2 * (c : ℝ) + 1) * (D0 + 2 * ((c : ℝ) * (c + 1)) * ((f : ℝ) * (f + 1))) *
        (s * T * W6 a b c f m n) =
      -((c : ℝ) * edgeA a b m n ((c : ℝ) + 1) * (-s * T * W6 a b (c + 1) f m n)) -
        ((c : ℝ) + 1) * edgeA a b m n (c : ℝ) * (-s * T * W6 a b (c - 1) f m n) := by
    linear_combination (s * T) * hrec2
  have := lattice_alg (c : ℝ) ((f : ℝ) * (f + 1)) D0 (s * T * W6 a b c f m n)
    (-s * T * W6 a b (c + 1) f m n) (-s * T * W6 a b (c - 1) f m n) (edgeA a b m n (c : ℝ))
    (edgeA a b m n ((c : ℝ) + 1)) hc' K
  unfold aPlus aMinus bDiag
  simp only [hA, hB, zc] at hD0 ⊢
  rw [← hD0]
  linear_combination this

/-- info: 'FormalResearch.Racah.SixJ.cMax_sub_cMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cMax_sub_cMin

/-- info: 'FormalResearch.Racah.SixJ.edgeA_cMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeA_cMin

/-- info: 'FormalResearch.Racah.SixJ.edgeA_cMax_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeA_cMax_succ

/-- info: 'FormalResearch.Racah.SixJ.omegaW_aPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omegaW_aPlus

/-- info: 'FormalResearch.Racah.SixJ.D0_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms D0_factor

/-- info: 'FormalResearch.Racah.SixJ.Phi6_lattice_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_lattice_eigen

end FormalResearch.Racah.SixJ

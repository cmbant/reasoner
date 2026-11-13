module

public import FormalResearch.Racah.P2ThreeJRec

/-!
# The exact finite-difference operator and the affine-midpoint uniqueness core (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, section *Exact finite-difference equation and
the first correction* (`eq:3jdiff`, `prop:3junique`, `rem:discreteWeyl`) and the first half of
*Exact finite spectral system* (`eq:physicalgrid`, `eq:3jHh`, `thm:3jspectral`).

Dictionary: `aH M σ h y` is `a_h(y)` of `eq:ah3` (real `h`; `aMid M σ N y = aH M σ (1/N) y`);
`Dop M σ h ψ x` is the left side of `eq:3jdiff` without its constant term; `Hh M σ N ψ x` is
`(𝖧_h ψ)(x)` of `eq:3jHh` with `h = 1/N` (rational lattice functions); `xLat M σ N n` is the
`n`-th point of `eq:physicalgrid`.

## What is proved

* `Dop_neg_h`: the operator of `eq:3jdiff` is exactly invariant under `h ↦ -h`.
* `Hh_Phi`: `𝖧_h Φ_L = L(L+1) Φ_L` at every lattice point (the eigen-equation in the proof of
  `thm:3jspectral`, from `PhiX_midpoint_diff`).
* `Hh_lattice_symmetric`: `𝖧_h` is symmetric on the physical lattice, using only the two
  boundary zeros `a_h(x_max+h) = a_h(x_min-h) = 0` (`xLat_top`, `xLat_bottom`).
* `wigner_principal_affine`, `principal_coeffs`: the exact coefficients of the Wigner operator
  after the affine re-centering `x = (X-ηε)/(1-δε)` (`ε = 1/Ñ`): `∂_X²` has coefficient
  `(1-δε)² - (X-ηε)² = (1-X²) + ε(2Xη-2δ) + ε²(δ²-η²)` and `∂_X` has `-2(X-ηε) = -2X + 2ηε`.
* `affine_midpoint_unique`: the algebraic core of `prop:3junique`.

Not covered (analytic): the expansion of the *discrete* recurrence into a continuum operator
(`O(ε)` bookkeeping of the difference operator), which the proposition takes as given.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-! ### `a_h` and the operator of `eq:3jdiff` -/

/-- `a_h(y) = √([(1-y)²-h²(σ-M)²][(1+y)²-h²(σ+M)²])` (`eq:ah3`), real `h`. -/
noncomputable def aH (M σ h y : ℝ) : ℝ :=
  Real.sqrt (((1 - y) ^ 2 - h ^ 2 * (σ - M) ^ 2) * ((1 + y) ^ 2 - h ^ 2 * (σ + M) ^ 2))

lemma aMid_eq_aH (M σ N : ℚ) (y : ℝ) : aMid M σ N y = aH M σ (1 / (N : ℝ)) y := rfl

lemma aH_neg (M σ h y : ℝ) : aH M σ (-h) y = aH M σ h y := by
  unfold aH; rw [neg_sq]

/-- The operator `ψ ↦ a_h(x+h)ψ(x+2h) + a_h(x-h)ψ(x-2h) - 2(1-x²)ψ(x)` of `eq:3jdiff`. -/
noncomputable def Dop (M σ h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  aH M σ h (x + h) * ψ (x + 2 * h) + aH M σ h (x - h) * ψ (x - 2 * h) - 2 * (1 - x ^ 2) * ψ x

/-- The operator of `eq:3jdiff` is exactly invariant under `h ↦ -h`: the two shifted terms
exchange (`a_h` is even in `h`). -/
theorem Dop_neg_h (M σ h : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : Dop M σ (-h) ψ x = Dop M σ h ψ x := by
  unfold Dop
  rw [aH_neg, aH_neg, show x + -h = x - h by ring, show x - -h = x + h by ring,
    show x + 2 * -h = x - 2 * h by ring, show x - 2 * -h = x + 2 * h by ring]
  ring

/-! ### The operator `𝖧_h` on rational lattice functions -/

/-- `(𝖧_h ψ)(x)` of `eq:3jHh` with `h = 1/N`, for `ψ` a function on the rational lattice. -/
noncomputable def Hh (M σ N : ℚ) (ψ : ℚ → ℝ) (x : ℚ) : ℝ :=
  -(aMid M σ N ((x : ℝ) + 1 / N) * ψ (x + 2 / N) + aMid M σ N ((x : ℝ) - 1 / N) * ψ (x - 2 / N)
      - 2 * (1 - (x : ℝ) ^ 2) * ψ x) / (4 * (1 / (N : ℝ)) ^ 2)
    + ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2 - 1) / 2 * ψ x

/-- `𝖧_h ψ = J ψ` at `x` is exactly the finite-difference equation `eq:3jdiff` with
`J = L(L+1)`. -/
theorem Hh_eq_iff (M σ N : ℚ) (hN : N ≠ 0) (ψ : ℚ → ℝ) (x : ℚ) (J : ℝ) :
    Hh M σ N ψ x = J * ψ x ↔
      aMid M σ N ((x : ℝ) + 1 / N) * ψ (x + 2 / N) + aMid M σ N ((x : ℝ) - 1 / N) * ψ (x - 2 / N)
        - 2 * (1 - (x : ℝ) ^ 2) * ψ x
        + 2 * (1 / (N : ℝ)) ^ 2 * (2 * J - (M : ℝ) ^ 2 - (σ : ℝ) ^ 2 + 1) * ψ x = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold Hh
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination (-1/2 : ℝ) * h
  · intro h
    field_simp at h ⊢
    linear_combination (-2 : ℝ) * h

/-- **Eigen-equation of `thm:3jspectral`** at every lattice point:
`𝖧_h Φ_L^{M,σ} = L(L+1) Φ_L^{M,σ}` (hypotheses as in `PhiX_midpoint_diff`: `x` is a lattice
point; the values of `Φ` off the lattice are irrelevant because the corresponding coefficients
vanish). -/
theorem Hh_Phi (L M σ N x : ℚ) (hN : 0 < N)
    (a1 : IsNat (jMinus N σ + mMinus M (N * x / 2)))
    (a4 : IsNat (jPlus N σ - mPlus M (N * x / 2)))
    (b1 : IsNat (jMinus N σ - mMinus M (N * x / 2)))
    (b3 : IsNat (jPlus N σ + mPlus M (N * x / 2))) :
    Hh M σ N (PhiX L M σ N) x = ((L : ℝ) * (L + 1)) * PhiX L M σ N x := by
  rw [Hh_eq_iff M σ N hN.ne']
  have := PhiX_midpoint_diff L M σ N x hN a1 a4 b1 b3
  linear_combination this

/-! ### The physical lattice and symmetry of `𝖧_h` -/

/-- The `n`-th point `x_n = -1 + (1+|M+σ|)h + 2nh` (`h = 1/N`) of `eq:physicalgrid`. -/
def xLat (M σ N : ℚ) (n : ℕ) : ℚ := -1 + (1 + |M + σ|) / N + 2 * n / N

lemma xLat_succ (M σ N : ℚ) (n : ℕ) : xLat M σ N (n + 1) = xLat M σ N n + 2 / N := by
  unfold xLat; push_cast; ring

lemma two_max_abs (M σ : ℚ) : 2 * max |M| |σ| = |M + σ| + |M - σ| := by
  rcases abs_cases M with ⟨hM, _⟩ | ⟨hM, _⟩ <;> rcases abs_cases σ with ⟨hs, _⟩ | ⟨hs, _⟩ <;>
    rcases abs_cases (M + σ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (M - σ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases max_cases |M| |σ| with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> linarith

/-- The bottom closing zero: `a_h(x_0 - h) = 0`, where `x_0 - h = -1 + |M+σ| h`. -/
lemma xLat_bottom (M σ N : ℚ) (hN : N ≠ 0) :
    aMid M σ N ((xLat M σ N 0 : ℚ) - 1 / (N : ℝ)) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have : ((xLat M σ N 0 : ℚ) : ℝ) - 1 / (N : ℝ) = -1 + |(σ : ℝ) + M| / N := by
    unfold xLat
    push_cast
    rw [show (σ : ℝ) + M = M + σ by ring, ← Rat.cast_add, ← Rat.cast_abs]
    field_simp
    ring
  rw [this]
  exact aMid_zero_bottom M σ N hN

/-- The top closing zero: `a_h(x_{K-1} + h) = 0` for the last lattice point, where
`K = N - L₀`, `L₀ = max(|M|,|σ|)`. -/
lemma xLat_top (M σ N : ℚ) (hN : N ≠ 0) (K : ℕ) (hK : (K : ℚ) = N - max |M| |σ|) (hK1 : 1 ≤ K) :
    aMid M σ N ((xLat M σ N (K - 1) : ℚ) + 1 / (N : ℝ)) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h2 := two_max_abs M σ
  have hKr : (K : ℝ) = N - ((max |M| |σ| : ℚ) : ℝ) := by exact_mod_cast hK
  have h2r : 2 * ((max |M| |σ| : ℚ) : ℝ) = |(M : ℝ) + σ| + |(M : ℝ) - σ| := by
    have := congrArg (Rat.cast : ℚ → ℝ) h2
    push_cast at this ⊢
    exact this
  have : ((xLat M σ N (K - 1) : ℚ) : ℝ) + 1 / (N : ℝ) = 1 - |(σ : ℝ) - M| / N := by
    unfold xLat
    push_cast
    rw [Nat.cast_sub hK1, abs_sub_comm (σ : ℝ) M]
    have hMs : ((M + σ : ℚ) : ℝ) = (M : ℝ) + σ := by push_cast; ring
    rw [show ((M : ℝ) + σ) = (M : ℝ) + σ from rfl]
    field_simp
    push_cast
    rw [hKr]
    have : |(M : ℝ) + σ| = |(M : ℝ) + σ| := rfl
    nlinarith [h2r]
  rw [this]
  exact aMid_zero_top M σ N hN

lemma aMid_shift_lat (M σ N : ℚ) (n : ℕ) :
    aMid M σ N (((xLat M σ N (n + 1) : ℚ) : ℝ) - 1 / (N : ℝ)) =
      aMid M σ N (((xLat M σ N n : ℚ) : ℝ) + 1 / (N : ℝ)) := by
  rw [xLat_succ]; push_cast; congr 1; ring

/-- The two hopping sums of `𝖧_h` over the physical lattice are transposes of each other. -/
lemma lattice_shift_sum (M σ N : ℚ) (hN : N ≠ 0) (K : ℕ)
    (hK : (K : ℚ) = N - max |M| |σ|) (f g : ℚ → ℝ) :
    ∑ n ∈ Finset.range K, f (xLat M σ N n) *
        aMid M σ N (((xLat M σ N n : ℚ) : ℝ) - 1 / (N : ℝ)) * g (xLat M σ N n - 2 / N) =
      ∑ n ∈ Finset.range K, g (xLat M σ N n) *
        aMid M σ N (((xLat M σ N n : ℚ) : ℝ) + 1 / (N : ℝ)) * f (xLat M σ N n + 2 / N) := by
  cases K with
  | zero => simp
  | succ k =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ, xLat_bottom M σ N hN]
    have hk : aMid M σ N (((xLat M σ N k : ℚ) : ℝ) + 1 / (N : ℝ)) = 0 := by
      have := xLat_top M σ N hN (k + 1) hK (by omega)
      simpa using this
    rw [hk]
    simp only [mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [aMid_shift_lat, show xLat M σ N (n + 1) - 2 / N = xLat M σ N n by rw [xLat_succ]; ring,
      ← xLat_succ]
    ring

/-- **`𝖧_h` is symmetric on the physical lattice** (`thm:3jspectral`, first sentence; the
weight `2h` is constant and irrelevant).  `K = N - L₀` is the number of lattice points of
`eq:physicalgrid`; only the two boundary zeros `a_h(x_max+h) = a_h(x_min-h) = 0` are used, so no
value of `ψ, φ` outside the lattice enters. -/
theorem Hh_lattice_symmetric (M σ N : ℚ) (hN : N ≠ 0) (K : ℕ)
    (hK : (K : ℚ) = N - max |M| |σ|) (φ ψ : ℚ → ℝ) :
    ∑ n ∈ Finset.range K, φ (xLat M σ N n) * Hh M σ N ψ (xLat M σ N n) =
      ∑ n ∈ Finset.range K, ψ (xLat M σ N n) * Hh M σ N φ (xLat M σ N n) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h1 := lattice_shift_sum M σ N hN K hK φ ψ
  have h2 := lattice_shift_sum M σ N hN K hK ψ φ
  have hexp : ∀ (f g : ℚ → ℝ),
      ∑ n ∈ Finset.range K, f (xLat M σ N n) * Hh M σ N g (xLat M σ N n) =
        -(∑ n ∈ Finset.range K, f (xLat M σ N n) *
            aMid M σ N (((xLat M σ N n : ℚ) : ℝ) + 1 / (N : ℝ)) * g (xLat M σ N n + 2 / N)
          + ∑ n ∈ Finset.range K, f (xLat M σ N n) *
            aMid M σ N (((xLat M σ N n : ℚ) : ℝ) - 1 / (N : ℝ)) * g (xLat M σ N n - 2 / N)
          - ∑ n ∈ Finset.range K, 2 * (1 - ((xLat M σ N n : ℚ) : ℝ) ^ 2) *
              (f (xLat M σ N n) * g (xLat M σ N n))) / (4 * (1 / (N : ℝ)) ^ 2)
        + ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2 - 1) / 2 *
            ∑ n ∈ Finset.range K, f (xLat M σ N n) * g (xLat M σ N n) := by
    intro f g
    unfold Hh
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hexp, hexp]
  have hc : ∀ n, ψ (xLat M σ N n) * φ (xLat M σ N n) = φ (xLat M σ N n) * ψ (xLat M σ N n) :=
    fun n => mul_comm _ _
  simp only [hc]
  rw [h1, h2]
  ring

/-- info: 'FormalResearch.Racah.Hh_lattice_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hh_lattice_symmetric

/-- info: 'FormalResearch.Racah.Hh_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hh_Phi

/-- info: 'FormalResearch.Racah.Dop_neg_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dop_neg_h

end FormalResearch.Racah

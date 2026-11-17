module

public import FormalResearch.Special.DiscreteAiryKappaInvariant

/-!
# The second-order adiabatic invariant of a three-term recurrence: the Ermakov (Milne) form (Airy-free)

`DiscreteAiryKappaInvariant` has the first-order invariant `F_k = a_k(Y_k² + Y_{k-1}²) - c_k Y_k Y_{k-1}`, whose step identity
`F_{k+1} - F_k = O(Δa + Δc)·F_k` only gives `e^{O(1)}` invariance over a macroscopic band (the sum of `N` first-order terms does not cancel).
This module replaces it by the **Ermakov–Milne form** attached to an arbitrary positive *profile* `P_k = ρ_k²` (the squared amplitude of a
pair of solutions), for which the one-step defect is the **Ermakov defect** `E_k` of the profile — second order in `h` for the WKB profile.

For the Jacobi rows `a_{k+1}Y_{k+1} + a_k Y_{k-1} = c_k Y_k` (`jac a c Y k = 0`) and `P > 0` with `a_k² P_k P_{k-1} ≥ 1`, put
`s_k = √(a_k² P_k P_{k-1} - 1)` (`kermS`; this is `a_k ρ_kρ_{k-1} cos θ_k` when `a_kρ_kρ_{k-1} sin θ_k = 1`) and

* `I_k(Y) = a_k² P_{k-1} Y_k² + a_k² P_k Y_{k-1}² - 2 a_k s_k Y_k Y_{k-1}`                  (`kermI`),
* `E_k = s_{k+1} + s_k - c_k P_k`                                          (`kermE`; zero iff `P` is an exact Ermakov profile).

**Exact step identity** (`kerm_step`, from the row `k` and the two radicand identities):
`P_k (I_{k+1} - I_k) = E_k [ (c_k P_k + s_{k+1} - s_k) Y_k² - 2 P_k · a_{k+1}Y_{k+1} · Y_k ]`.

* `kermI_lower`: `I_k ≥ ½ (Y_k²/P_k + Y_{k-1}²/P_{k-1})` (positive definite; the discriminant of the form is `-a_k²`, no hypothesis);
* `kermI_nonneg`, `kermI_cross`: `I_k ≥ 0` and `|Y_k Y_{k-1}| ≤ (P_k + P_{k-1}) I_k`;
* `kerm_step_bound`: `|I_{k+1} - I_k| ≤ |E_k| B_k I_k`, `B_k = 2|c_kP_k + s_{k+1} - s_k| + 4 P_k |c_k| + 2 a_k (P_k + P_{k-1})`;
* `kerm_chain`: from one-step relative bounds `|G_{j+1} - G_j| ≤ ε_j G_j` (`0 ≤ ε_j ≤ ½`) over `n` steps:
  `G_{k₀+n} ≤ e^{Σε} G_{k₀}`, `G_{k₀} ≤ e^{2Σε} G_{k₀+n}`; `kerm_invariant` specialises to `G = I`.

For a profile with `E_k = O(h²)` and `B_k = O(1)` on a band of `O(1/h)` sites the total `Σ ε = O(h)`, i.e. **`1 + O(h)` invariance of the
amplitude** `I_k` (the first-order `F_k` loses `e^{O(1)}`).  Numerics (mpmath 40 digits, scratch `r29_num/erm.py`, `erm2.py`): for the
Hahn chain with `P_k = 2/√(q_*² - q_k²)`, `q_k = (k+½)h`, `E_k N² ∈ [-330, 120]` on `0.2q_*N ≤ k ≤ 0.9q_*N` (`N = 1366..1600`,
`(M,σ,x) = (0,0,½), (1,1,0.65), (2,1,0.3)`), and the actual chain has `I_k = 2/π (1 ± 2.6·10⁻⁴)` there.

**Claim class: proved** (real algebra).  **Not formalised** here: the profile defect for the Hahn coefficients and the Airy matching (see
`DiscreteAiryKappaMassId` for the mass identity).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `s_k = √(a_k² P_k P_{k-1} - 1)`: `a_k ρ_k ρ_{k-1} cos θ_k` for the profile `P = ρ²`. -/
noncomputable def kermS (a P : ℤ → ℝ) (k : ℤ) : ℝ := Real.sqrt (a k ^ 2 * P k * P (k - 1) - 1)

/-- The Ermakov–Milne form `I_k(Y) = a_k² P_{k-1} Y_k² + a_k² P_k Y_{k-1}² - 2 a_k s_k Y_k Y_{k-1}`. -/
noncomputable def kermI (a P Y : ℤ → ℝ) (k : ℤ) : ℝ :=
  a k ^ 2 * P (k - 1) * Y k ^ 2 + a k ^ 2 * P k * Y (k - 1) ^ 2 - 2 * a k * kermS a P k * Y k * Y (k - 1)

/-- The Ermakov defect `E_k = s_{k+1} + s_k - c_k P_k` of the profile `P`. -/
noncomputable def kermE (a c P : ℤ → ℝ) (k : ℤ) : ℝ := kermS a P (k + 1) + kermS a P k - c k * P k

lemma kermS_sq {a P : ℤ → ℝ} {k : ℤ} (h : 1 ≤ a k ^ 2 * P k * P (k - 1)) :
    kermS a P k ^ 2 = a k ^ 2 * P k * P (k - 1) - 1 := by
  unfold kermS; exact Real.sq_sqrt (by linarith)

lemma kermS_nonneg (a P : ℤ → ℝ) (k : ℤ) : 0 ≤ kermS a P k := Real.sqrt_nonneg _

/-- **The exact step identity** of the Ermakov form (uses the row `k` and the radicand identities at `k, k+1`). -/
lemma kerm_step {a c P Y : ℤ → ℝ} {k : ℤ} (hrow : jac a c Y k = 0) (h0 : 1 ≤ a k ^ 2 * P k * P (k - 1))
    (h1 : 1 ≤ a (k + 1) ^ 2 * P (k + 1) * P k) :
    P k * (kermI a P Y (k + 1) - kermI a P Y k) =
      kermE a c P k * ((c k * P k + kermS a P (k + 1) - kermS a P k) * Y k ^ 2 -
        2 * P k * (a (k + 1) * Y (k + 1)) * Y k) := by
  have hs0 := kermS_sq h0
  have hs1 : kermS a P (k + 1) ^ 2 = a (k + 1) ^ 2 * P (k + 1) * P k - 1 := by
    have := kermS_sq (a := a) (P := P) (k := k + 1) (by simpa using h1)
    simpa using this
  unfold kermI kermE jac at *
  simp only [add_sub_cancel_right] at *
  have hz : a (k + 1) * Y (k + 1) = c k * Y k - a k * Y (k - 1) := by linarith
  have e1 : a (k + 1) ^ 2 * Y (k + 1) ^ 2 = (c k * Y k - a k * Y (k - 1)) ^ 2 := by
    rw [← hz]; ring
  set s0 := kermS a P k
  set s1 := kermS a P (k + 1)
  rw [hz]
  have e2 : a (k + 1) ^ 2 * P k * Y (k + 1) ^ 2 = P k * (c k * Y k - a k * Y (k - 1)) ^ 2 := by
    calc a (k + 1) ^ 2 * P k * Y (k + 1) ^ 2 = P k * (a (k + 1) ^ 2 * Y (k + 1) ^ 2) := by ring
      _ = _ := by rw [e1]
  have e3 : 2 * a (k + 1) * s1 * Y (k + 1) * Y k = 2 * s1 * (c k * Y k - a k * Y (k - 1)) * Y k := by
    rw [← hz]; ring
  rw [show a (k + 1) ^ 2 * P k * Y (k + 1) ^ 2 = _ from e2, show 2 * a (k + 1) * s1 * Y (k + 1) * Y k = _ from e3]
  linear_combination (Y k ^ 2) * hs0 - (Y k ^ 2) * hs1

/-- **Positive definiteness** (no hypothesis on the coefficients beyond the radicand): `Y_k² ≤ 2 P_k I_k` and `Y_{k-1}² ≤ 2 P_{k-1} I_k`
(equivalently `I_k ≥ ½(Y_k²/P_k + Y_{k-1}²/P_{k-1})`). -/
lemma kermI_lower {a P Y : ℤ → ℝ} {k : ℤ} (hp : 0 < P k) (hp' : 0 < P (k - 1))
    (h0 : 1 ≤ a k ^ 2 * P k * P (k - 1)) :
    Y k ^ 2 ≤ 2 * P k * kermI a P Y k ∧ Y (k - 1) ^ 2 ≤ 2 * P (k - 1) * kermI a P Y k := by
  have hs := kermS_sq h0
  have hs0 := kermS_nonneg a P k
  unfold kermI
  set s := kermS a P k
  set p := P k
  set p' := P (k - 1)
  set y := Y k
  set w := Y (k - 1)
  set a0 := a k
  have ht : 0 < 2 * s ^ 2 + 1 := by positivity
  have hsq : a0 ^ 2 * p * p' = s ^ 2 + 1 := by linarith
  have key : p' * ((2 * s ^ 2 + 1) * ((2 * s ^ 2 + 1) * (p' * y ^ 2 + p * w ^ 2) - 4 * a0 * p * p' * s * y * w)) =
      ((2 * s ^ 2 + 1) * p' * y - 2 * a0 * p * p' * s * w) ^ 2 + p * p' * w ^ 2 := by
    linear_combination (-4 * s ^ 2 * w ^ 2 * p * p') * hsq
  have hX : 0 ≤ (2 * s ^ 2 + 1) * (p' * y ^ 2 + p * w ^ 2) - 4 * a0 * p * p' * s * y * w := by
    have h1 : 0 ≤ p' * ((2 * s ^ 2 + 1) * ((2 * s ^ 2 + 1) * (p' * y ^ 2 + p * w ^ 2) - 4 * a0 * p * p' * s * y * w)) := by
      rw [key]; positivity
    have h2 := (mul_nonneg_iff_of_pos_left hp').1 h1
    exact (mul_nonneg_iff_of_pos_left ht).1 h2
  have e : 2 * p * p' * (a0 ^ 2 * p' * y ^ 2 + a0 ^ 2 * p * w ^ 2 - 2 * a0 * s * y * w) =
      ((2 * s ^ 2 + 1) * (p' * y ^ 2 + p * w ^ 2) - 4 * a0 * p * p' * s * y * w) + (p' * y ^ 2 + p * w ^ 2) := by
    linear_combination (2 * (p' * y ^ 2 + p * w ^ 2)) * hsq
  have hpp : 0 < p * p' := mul_pos hp hp'
  constructor
  · have : p' * y ^ 2 ≤ 2 * p * p' * (a0 ^ 2 * p' * y ^ 2 + a0 ^ 2 * p * w ^ 2 - 2 * a0 * s * y * w) := by
      rw [e]; nlinarith [mul_nonneg hp.le (sq_nonneg w)]
    have h3 : p' * y ^ 2 ≤ p' * (2 * p * (a0 ^ 2 * p' * y ^ 2 + a0 ^ 2 * p * w ^ 2 - 2 * a0 * s * y * w)) := by
      nlinarith [this]
    exact le_of_mul_le_mul_left h3 hp'
  · have : p * w ^ 2 ≤ 2 * p * p' * (a0 ^ 2 * p' * y ^ 2 + a0 ^ 2 * p * w ^ 2 - 2 * a0 * s * y * w) := by
      rw [e]; nlinarith [mul_nonneg hp'.le (sq_nonneg y)]
    have h3 : p * w ^ 2 ≤ p * (2 * p' * (a0 ^ 2 * p' * y ^ 2 + a0 ^ 2 * p * w ^ 2 - 2 * a0 * s * y * w)) := by
      nlinarith [this]
    exact le_of_mul_le_mul_left h3 hp

lemma kermI_nonneg {a P Y : ℤ → ℝ} {k : ℤ} (hp : 0 < P k) (hp' : 0 < P (k - 1))
    (h0 : 1 ≤ a k ^ 2 * P k * P (k - 1)) : 0 ≤ kermI a P Y k := by
  have := (kermI_lower (Y := Y) hp hp' h0).1
  have h2 : 0 ≤ 2 * P k * kermI a P Y k := le_trans (sq_nonneg _) this
  have h3 : 0 < 2 * P k := by positivity
  exact (mul_nonneg_iff_of_pos_left h3).1 h2

/-- The mixed term is controlled by the pair: `|Y_k Y_{k-1}| ≤ (P_k + P_{k-1}) I_k`. -/
lemma kermI_cross {a P Y : ℤ → ℝ} {k : ℤ} (hp : 0 < P k) (hp' : 0 < P (k - 1))
    (h0 : 1 ≤ a k ^ 2 * P k * P (k - 1)) : |Y k * Y (k - 1)| ≤ (P k + P (k - 1)) * kermI a P Y k := by
  obtain ⟨l1, l2⟩ := kermI_lower (Y := Y) hp hp' h0
  have hI := kermI_nonneg (Y := Y) hp hp' h0
  set I := kermI a P Y k
  apply abs_le_of_sq_le_sq _ (by positivity)
  calc (Y k * Y (k - 1)) ^ 2 = Y k ^ 2 * Y (k - 1) ^ 2 := by ring
    _ ≤ (2 * P k * I) * (2 * P (k - 1) * I) := mul_le_mul l1 l2 (sq_nonneg _) (by positivity)
    _ ≤ ((P k + P (k - 1)) * I) ^ 2 := by nlinarith [sq_nonneg (P k - P (k - 1)), sq_nonneg I, mul_nonneg (sq_nonneg (P k - P (k - 1))) (sq_nonneg I)]

/-- **One-step bound** `|I_{k+1} - I_k| ≤ |E_k| B_k I_k`. -/
lemma kerm_step_bound {a c P Y : ℤ → ℝ} {k : ℤ} (hrow : jac a c Y k = 0) (ha : 0 < a k) (hp : 0 < P k)
    (hp' : 0 < P (k - 1)) (h0 : 1 ≤ a k ^ 2 * P k * P (k - 1)) (h1 : 1 ≤ a (k + 1) ^ 2 * P (k + 1) * P k) :
    |kermI a P Y (k + 1) - kermI a P Y k| ≤
      |kermE a c P k| * (2 * |c k * P k + kermS a P (k + 1) - kermS a P k| + 4 * P k * |c k| +
        2 * a k * (P k + P (k - 1))) * kermI a P Y k := by
  have hst := kerm_step (Y := Y) hrow h0 h1
  obtain ⟨l1, l2⟩ := kermI_lower (Y := Y) hp hp' h0
  have hcr := kermI_cross (Y := Y) hp hp' h0
  have hI := kermI_nonneg (Y := Y) hp hp' h0
  set I := kermI a P Y k
  set E := kermE a c P k
  set C := c k * P k + kermS a P (k + 1) - kermS a P k
  set Z := a (k + 1) * Y (k + 1)
  have hz : Z = c k * Y k - a k * Y (k - 1) := by
    unfold jac at hrow; linarith
  have t1 : |C * Y k ^ 2| ≤ |C| * (2 * P k * I) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Y k))]
    exact mul_le_mul_of_nonneg_left l1 (abs_nonneg _)
  have t2 : |Z * Y k| ≤ |c k| * (2 * P k * I) + a k * ((P k + P (k - 1)) * I) := by
    rw [hz]
    calc |(c k * Y k - a k * Y (k - 1)) * Y k| = |c k * Y k ^ 2 - a k * (Y k * Y (k - 1))| := by ring_nf
      _ ≤ |c k * Y k ^ 2| + |a k * (Y k * Y (k - 1))| := abs_sub _ _
      _ = |c k| * Y k ^ 2 + a k * |Y k * Y (k - 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Y k)), abs_of_pos ha]
      _ ≤ _ := by
          gcongr
  have hmain : |C * Y k ^ 2 - 2 * P k * Z * Y k| ≤
      P k * ((2 * |C| + 4 * P k * |c k| + 2 * a k * (P k + P (k - 1))) * I) := by
    calc |C * Y k ^ 2 - 2 * P k * Z * Y k| ≤ |C * Y k ^ 2| + |2 * P k * (Z * Y k)| := by
          rw [show 2 * P k * Z * Y k = 2 * P k * (Z * Y k) by ring]; exact abs_sub _ _
      _ = |C * Y k ^ 2| + 2 * P k * |Z * Y k| := by
          rw [abs_mul (2 * P k), abs_of_pos (by positivity : (0:ℝ) < 2 * P k)]
      _ ≤ |C| * (2 * P k * I) + 2 * P k * (|c k| * (2 * P k * I) + a k * ((P k + P (k - 1)) * I)) := by
          gcongr
      _ = _ := by ring
  have hdiv : |kermI a P Y (k + 1) - kermI a P Y k| * P k = |E| * |C * Y k ^ 2 - 2 * P k * Z * Y k| := by
    calc |kermI a P Y (k + 1) - kermI a P Y k| * P k = |P k * (kermI a P Y (k + 1) - kermI a P Y k)| := by
          rw [abs_mul, abs_of_pos hp]; ring
      _ = |E * (C * Y k ^ 2 - 2 * P k * Z * Y k)| := by rw [hst]
      _ = _ := abs_mul _ _
  have hfin : |kermI a P Y (k + 1) - kermI a P Y k| * P k ≤
      P k * (|E| * (2 * |C| + 4 * P k * |c k| + 2 * a k * (P k + P (k - 1))) * I) := by
    rw [hdiv]
    calc |E| * |C * Y k ^ 2 - 2 * P k * Z * Y k| ≤ |E| * (P k * ((2 * |C| + 4 * P k * |c k| + 2 * a k * (P k + P (k - 1))) * I)) :=
          mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
      _ = _ := by ring
  have := le_of_mul_le_mul_right (by linarith [hfin] : |kermI a P Y (k + 1) - kermI a P Y k| * P k ≤
      (|E| * (2 * |C| + 4 * P k * |c k| + 2 * a k * (P k + P (k - 1))) * I) * P k) hp
  exact this

/-- **Chaining one-step relative bounds** (generic).  If `|G_{j+1} - G_j| ≤ ε_j G_j`, `G ≥ 0`, `0 ≤ ε_j ≤ ½` for `j = k₀, …, k₀+n-1`, then
`G_{k₀+n} ≤ e^{Σε} G_{k₀}` and `G_{k₀} ≤ e^{2Σε} G_{k₀+n}`. -/
theorem kerm_chain {G ε : ℤ → ℝ} {k0 : ℤ} (n : ℕ) (hG : ∀ i : ℕ, i ≤ n → 0 ≤ G (k0 + (i : ℤ)))
    (hstep : ∀ i : ℕ, i < n → |G (k0 + (i : ℤ) + 1) - G (k0 + (i : ℤ))| ≤ ε (k0 + (i : ℤ)) * G (k0 + (i : ℤ)))
    (hε0 : ∀ i : ℕ, i < n → 0 ≤ ε (k0 + (i : ℤ))) (hε1 : ∀ i : ℕ, i < n → ε (k0 + (i : ℤ)) ≤ 1 / 2) :
    G (k0 + (n : ℤ)) ≤ Real.exp (∑ i ∈ range n, ε (k0 + (i : ℤ))) * G k0 ∧
      G k0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) * G (k0 + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi => hG i (by omega)) (fun i hi => hstep i (by omega)) (fun i hi => hε0 i (by omega))
      (fun i hi => hε1 i (by omega))
    have hk : k0 + ((n + 1 : ℕ) : ℤ) = k0 + (n : ℤ) + 1 := by push_cast; ring
    obtain ⟨s1, s2⟩ := ki_step_exp (hG n (by omega)) (hε0 n (by omega)) (hε1 n (by omega)) (hstep n (by omega))
    rw [hk, Finset.sum_range_succ, Real.exp_add, mul_add, Real.exp_add]
    constructor
    · calc G (k0 + (n : ℤ) + 1) ≤ Real.exp (ε (k0 + (n : ℤ))) * G (k0 + (n : ℤ)) := s1
        _ ≤ Real.exp (ε (k0 + (n : ℤ))) * (Real.exp (∑ i ∈ range n, ε (k0 + (i : ℤ))) * G k0) :=
            mul_le_mul_of_nonneg_left ih'.1 (Real.exp_pos _).le
        _ = _ := by ring
    · have hE0 : 0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) := (Real.exp_pos _).le
      calc G k0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) * G (k0 + (n : ℤ)) := ih'.2
        _ ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) *
            (Real.exp (2 * ε (k0 + (n : ℤ))) * G (k0 + (n : ℤ) + 1)) :=
            mul_le_mul_of_nonneg_left s2 hE0
        _ = _ := by ring

/-- **The second-order invariant over a band.**  Hypotheses on the sites `k₀, …, k₀+n` (rows `jac = 0`, `a > 0`, `P > 0` on `k₀-1..k₀+n`, radicands `≥ 1` at `k₀..k₀+n`)
and `|E_k| B_k ≤ ε_k ≤ ½`: `I_{k₀+n} ≤ e^{Σε} I_{k₀}` and `I_{k₀} ≤ e^{2Σε} I_{k₀+n}`.  Here `Σ ε = O(Σ |E_k|)` is `O(h)` for a profile of
Ermakov defect `E_k = O(h²)` on a band of `O(1/h)` sites. -/
theorem kerm_invariant {a c P Y ε : ℤ → ℝ} {k0 : ℤ} (n : ℕ)
    (hrow : ∀ i : ℕ, i < n → jac a c Y (k0 + (i : ℤ)) = 0)
    (ha : ∀ i : ℕ, i < n → 0 < a (k0 + (i : ℤ)))
    (hp : ∀ i : ℕ, i ≤ n → 0 < P (k0 + (i : ℤ))) (hp0 : 0 < P (k0 - 1))
    (h0 : ∀ i : ℕ, i ≤ n → 1 ≤ a (k0 + (i : ℤ)) ^ 2 * P (k0 + (i : ℤ)) * P (k0 + (i : ℤ) - 1))
    (hε : ∀ i : ℕ, i < n → |kermE a c P (k0 + (i : ℤ))| * (2 * |c (k0 + (i : ℤ)) * P (k0 + (i : ℤ)) +
        kermS a P (k0 + (i : ℤ) + 1) - kermS a P (k0 + (i : ℤ))| + 4 * P (k0 + (i : ℤ)) * |c (k0 + (i : ℤ))| +
        2 * a (k0 + (i : ℤ)) * (P (k0 + (i : ℤ)) + P (k0 + (i : ℤ) - 1))) ≤ ε (k0 + (i : ℤ)))
    (hε0 : ∀ i : ℕ, i < n → 0 ≤ ε (k0 + (i : ℤ))) (hε1 : ∀ i : ℕ, i < n → ε (k0 + (i : ℤ)) ≤ 1 / 2) :
    kermI a P Y (k0 + (n : ℤ)) ≤ Real.exp (∑ i ∈ range n, ε (k0 + (i : ℤ))) * kermI a P Y k0 ∧
      kermI a P Y k0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) * kermI a P Y (k0 + (n : ℤ)) := by
  have hpm : ∀ i : ℕ, i ≤ n → 0 < P (k0 + (i : ℤ) - 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hp0
    · have := hp (i - 1) (by omega)
      rwa [show k0 + ((i - 1 : ℕ) : ℤ) = k0 + (i : ℤ) - 1 by push_cast [Nat.cast_sub hi0]; ring] at this
  have h1 : ∀ i : ℕ, i < n → 1 ≤ a (k0 + (i : ℤ) + 1) ^ 2 * P (k0 + (i : ℤ) + 1) * P (k0 + (i : ℤ)) := by
    intro i hi
    have := h0 (i + 1) (by omega)
    rwa [show k0 + ((i + 1 : ℕ) : ℤ) = k0 + (i : ℤ) + 1 by push_cast; ring,
      show k0 + (i : ℤ) + 1 - 1 = k0 + (i : ℤ) by ring] at this
  refine kerm_chain (G := kermI a P Y) n (fun i hi => ?_) (fun i hi => ?_) hε0 hε1
  · exact kermI_nonneg (hp i hi) (hpm i hi) (h0 i hi)
  · exact (kerm_step_bound (hrow i hi) (ha i hi) (hp i hi.le) (hpm i hi.le) (h0 i hi.le) (h1 i hi)).trans
      (by have := hε i hi; have hI := kermI_nonneg (a := a) (Y := Y) (hp i hi.le) (hpm i hi.le) (h0 i hi.le)
          exact mul_le_mul_of_nonneg_right this hI)

/-- info: 'FormalResearch.Special.kerm_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kerm_invariant

/-- info: 'FormalResearch.Special.kerm_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kerm_step

/-- info: 'FormalResearch.Special.kerm_step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kerm_step_bound

/-- info: 'FormalResearch.Special.kermI_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kermI_lower

end FormalResearch.Special

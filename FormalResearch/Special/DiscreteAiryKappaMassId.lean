module

public import FormalResearch.Special.DiscreteAiryKappaErmakov

/-!
# The exact mass identity for the Ermakov form (Airy-free)

For a solution `Y` of the Jacobi rows `a_{k+1}Y_{k+1} + a_k Y_{k-1} = c_k Y_k`, a profile `P` and weights `v_k`, the sum of the *amplitude
forms* `I_k` (`DiscreteAiryKappaErmakov`) over a band is, **exactly**, a weighted sum of `Y_k²` plus a summation-by-parts remainder:

`Σ_{k=p}^{n} v_k I_k = Σ_{k=p}^{n} Ω_k Y_k² + (boundary) - Σ_{k=p}^{n} (u_{k+1} - u_k) T_{k+1}`,

with `u_k = v_k s_k`, `T_k = a_k Y_k Y_{k-1}` and `Ω_k = v_k a_k² P_{k-1} + v_{k+1} a_{k+1}² P_{k+1} - v_k s_k c_k`
(`kerm_mass_id`).  The only input is the row identity `c_k Y_k² = T_{k+1} + T_k`; there is no oscillatory averaging, which is
replaced by the cancellation `Σ (T_{k+1} + T_k) u_k = Σ u_k c_k Y_k²`.  If the weights are chosen with `Ω_k = 1 + r_k` (`v = 1/w`,
`w_k = a_k² P_{k-1} + a_{k+1}² P_{k+1} - s_k c_k`) and `u` varies slowly, then `Σ_k Y_k² = Σ_k v_k I_k` up to `O(h) Σ Y_k²`
plus boundary terms: **the mass of an oscillating solution is read off from its (slowly varying) amplitude form**.  For the Hahn
chain `Ω = 1` means `v_k ≈ 1/(2 a_k sin θ_k)`.

* `kerm_mass_id`: the exact identity (`kerm_mass_site` is its one-site form, `kmBd` the boundary term);
* `kerm_mass_bound`: with `|Ω_k - 1| ≤ r`, `|u_{k+1} - u_k| a_{k+1} ≤ τ` the two-sided estimate
  `|Σ v_k I_k - Σ Y_k²| ≤ (r + τ) Σ Y_k² + (τ/2) Y_{p+m+1}² + |Bd(p+m)| + |Bd(p-1)|`.

**Claim class: proved** (real algebra).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The boundary expression `Bd(t)` of the mass identity (what is left of the pair `(Y_t, Y_{t+1})` after summation by parts). -/
noncomputable def kmBd (a P Y v : ℤ → ℝ) (t : ℤ) : ℝ :=
  -(v (t + 1) * a (t + 1) ^ 2 * P (t + 1) * Y t ^ 2) +
    v (t + 1) * kermS a P (t + 1) * (a (t + 1) * Y (t + 1) * Y t)

/-- **The one-site identity** `v_t I_t = Ω_t Y_t² + Bd(t) - Bd(t-1) - (u_{t+1} - u_t) T_{t+1}` (uses the row `t`). -/
lemma kerm_mass_site {a c P Y v : ℤ → ℝ} {t : ℤ} (hr : jac a c Y t = 0) :
    v t * kermI a P Y t =
      (v t * a t ^ 2 * P (t - 1) + v (t + 1) * a (t + 1) ^ 2 * P (t + 1) - v t * kermS a P t * c t) * Y t ^ 2 +
        kmBd a P Y v t - kmBd a P Y v (t - 1) -
        (v (t + 1) * kermS a P (t + 1) - v t * kermS a P t) * (a (t + 1) * Y (t + 1) * Y t) := by
  unfold jac at hr
  unfold kmBd kermI
  simp only [sub_add_cancel]
  linear_combination (-(v t * kermS a P t * Y t)) * hr

/-- **The exact mass identity** (see the module docstring), for the sites `p, …, p + m` (`m + 1` sites):
`Σ v_k I_k = Σ Ω_k Y_k² + Bd(p+m) - Bd(p-1) - Σ (u_{k+1} - u_k) T_{k+1}`. -/
theorem kerm_mass_id {a c P Y v : ℤ → ℝ} (p : ℤ) (m : ℕ) (hrow : ∀ i : ℕ, i ≤ m → jac a c Y (p + (i : ℤ)) = 0) :
    ∑ i ∈ range (m + 1), v (p + (i : ℤ)) * kermI a P Y (p + (i : ℤ)) =
      ∑ i ∈ range (m + 1), (v (p + (i : ℤ)) * a (p + (i : ℤ)) ^ 2 * P (p + (i : ℤ) - 1) +
          v (p + (i : ℤ) + 1) * a (p + (i : ℤ) + 1) ^ 2 * P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ)) * c (p + (i : ℤ))) * Y (p + (i : ℤ)) ^ 2 +
        kmBd a P Y v (p + (m : ℤ)) - kmBd a P Y v (p - 1) -
      ∑ i ∈ range (m + 1), (v (p + (i : ℤ) + 1) * kermS a P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ))) *
        (a (p + (i : ℤ) + 1) * Y (p + (i : ℤ) + 1) * Y (p + (i : ℤ))) := by
  induction m with
  | zero =>
    have := kerm_mass_site (a := a) (c := c) (P := P) (Y := Y) (v := v) (hrow 0 le_rfl)
    simpa using this
  | succ m ih =>
    have h := kerm_mass_site (a := a) (c := c) (P := P) (Y := Y) (v := v) (hrow (m + 1) le_rfl)
    have hk : p + ((m + 1 : ℕ) : ℤ) = (p + (m : ℤ)) + 1 := by push_cast; ring
    rw [hk] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := m + 1), Finset.sum_range_succ (n := m + 1),
      ih (fun i hi => hrow i (by omega))]
    rw [hk]
    simp only [add_sub_cancel_right] at h ⊢
    linarith [h]

/-- The coefficient `Ω_k = v_k a_k² P_{k-1} + v_{k+1} a_{k+1}² P_{k+1} - v_k s_k c_k` of `Y_k²` in the mass identity. -/
noncomputable def kmOmega (a c P v : ℤ → ℝ) (k : ℤ) : ℝ :=
  v k * a k ^ 2 * P (k - 1) + v (k + 1) * a (k + 1) ^ 2 * P (k + 1) - v k * kermS a P k * c k

/-- Summation of the pair averages: `Σ_{i≤m} (Y_{i+1}² + Y_i²)/2 = Σ_{i≤m} Y_i² + (Y_{m+1}² - Y_0²)/2`. -/
lemma km_pair_sum (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (f (i + 1) + f i) / 2 = ∑ i ∈ range (m + 1), f i + (f (m + 1) - f 0) / 2 := by
  induction m with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := n + 1)]
    ring

lemma km_term_bound {d w y z τ : ℝ} (hw : 0 < w) (hτ : 0 ≤ τ) (hD : |d| * w ≤ τ) :
    |d * (w * y * z)| ≤ τ * ((y ^ 2 + z ^ 2) / 2) := by
  have h1 : |d * (w * y * z)| = |d| * w * |y * z| := by
    rw [abs_mul, show w * y * z = w * (y * z) by ring, abs_mul, abs_of_pos hw]; ring
  rw [h1]
  have h3 : |y * z| ≤ (y ^ 2 + z ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y + z), sq_nonneg (y - z)]
  exact mul_le_mul hD h3 (abs_nonneg _) hτ

/-- **The mass estimate.**  If `|Ω_k - 1| ≤ r` and `|u_{k+1} - u_k| a_{k+1} ≤ τ` (`u = v s`) on the sites `p, …, p + m`, then
`|Σ v_k I_k - Σ Y_k²| ≤ (r + τ) Σ Y_k² + (τ/2) Y_{p+m+1}² + |Bd(p+m)| + |Bd(p-1)|` (sums over `p, …, p+m`). -/
theorem kerm_mass_bound {a c P Y v : ℤ → ℝ} (p : ℤ) (m : ℕ) {r τ : ℝ} (hτ0 : 0 ≤ τ)
    (hrow : ∀ i : ℕ, i ≤ m → jac a c Y (p + (i : ℤ)) = 0)
    (hΩ : ∀ i : ℕ, i ≤ m → |kmOmega a c P v (p + (i : ℤ)) - 1| ≤ r)
    (hD : ∀ i : ℕ, i ≤ m → |v (p + (i : ℤ) + 1) * kermS a P (p + (i : ℤ) + 1) - v (p + (i : ℤ)) * kermS a P (p + (i : ℤ))| *
      a (p + (i : ℤ) + 1) ≤ τ) (ha : ∀ i : ℕ, i ≤ m → 0 < a (p + (i : ℤ) + 1)) :
    |∑ i ∈ range (m + 1), v (p + (i : ℤ)) * kermI a P Y (p + (i : ℤ)) - ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2| ≤
      (r + τ) * ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 + τ / 2 * Y (p + (m : ℤ) + 1) ^ 2 +
        |kmBd a P Y v (p + (m : ℤ))| + |kmBd a P Y v (p - 1)| := by
  rw [kerm_mass_id p m hrow]
  set S := ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 with hS
  set A1 := ∑ i ∈ range (m + 1), (kmOmega a c P v (p + (i : ℤ)) - 1) * Y (p + (i : ℤ)) ^ 2 with hA1
  set A2 := ∑ i ∈ range (m + 1), (v (p + (i : ℤ) + 1) * kermS a P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ))) * (a (p + (i : ℤ) + 1) * Y (p + (i : ℤ) + 1) * Y (p + (i : ℤ))) with hA2
  have e1 : ∑ i ∈ range (m + 1), (v (p + (i : ℤ)) * a (p + (i : ℤ)) ^ 2 * P (p + (i : ℤ) - 1) +
          v (p + (i : ℤ) + 1) * a (p + (i : ℤ) + 1) ^ 2 * P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ)) * c (p + (i : ℤ))) * Y (p + (i : ℤ)) ^ 2 =
      A1 + S := by
    rw [hS, hA1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold kmOmega; ring
  have b1 : |A1| ≤ r * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Y (p + (i : ℤ))))]
    exact mul_le_mul_of_nonneg_right (hΩ i (Finset.mem_range_succ_iff.1 hi)) (sq_nonneg _)
  have b2 : |A2| ≤ τ * (S + Y (p + (m : ℤ) + 1) ^ 2 / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have key : ∀ i ∈ range (m + 1), |(v (p + (i : ℤ) + 1) * kermS a P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ))) * (a (p + (i : ℤ) + 1) * Y (p + (i : ℤ) + 1) * Y (p + (i : ℤ)))| ≤
        τ * ((Y (p + (i : ℤ) + 1) ^ 2 + Y (p + (i : ℤ)) ^ 2) / 2) := by
      intro i hi
      have hi' := Finset.mem_range_succ_iff.1 hi
      exact km_term_bound (d := v (p + (i : ℤ) + 1) * kermS a P (p + (i : ℤ) + 1) -
          v (p + (i : ℤ)) * kermS a P (p + (i : ℤ))) (y := Y (p + (i : ℤ) + 1)) (z := Y (p + (i : ℤ)))
          (ha i hi') hτ0 (hD i hi')
    refine (Finset.sum_le_sum key).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hτ0
    have hsum := km_pair_sum (fun i : ℕ => Y (p + (i : ℤ)) ^ 2) m
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at hsum
    rw [hsum]
    simp only [Nat.cast_zero, add_zero]
    nlinarith [sq_nonneg (Y p)]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : |A1 + S + kmBd a P Y v (p + (m : ℤ)) - kmBd a P Y v (p - 1) - A2 - S| ≤
      |A1| + |kmBd a P Y v (p + (m : ℤ))| + |kmBd a P Y v (p - 1)| + |A2| := by
    have : A1 + S + kmBd a P Y v (p + (m : ℤ)) - kmBd a P Y v (p - 1) - A2 - S =
        A1 + kmBd a P Y v (p + (m : ℤ)) - kmBd a P Y v (p - 1) - A2 := by ring
    rw [this]
    calc _ ≤ |A1 + kmBd a P Y v (p + (m : ℤ)) - kmBd a P Y v (p - 1)| + |A2| := abs_sub _ _
      _ ≤ |A1 + kmBd a P Y v (p + (m : ℤ))| + |kmBd a P Y v (p - 1)| + |A2| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  rw [e1]
  nlinarith [h3, b1, b2]

/-- info: 'FormalResearch.Special.kerm_mass_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kerm_mass_id

/-- info: 'FormalResearch.Special.kerm_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kerm_mass_bound

end FormalResearch.Special

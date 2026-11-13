module

public import FormalResearch.Wigner.WignerDJacobi
public import FormalResearch.Special.JacobiOrth
public import FormalResearch.Special.JacobiInt
public import FormalResearch.Wigner.Defs

/-!
# Orthogonality and normalisation of Wigner's small `d`-function

For fixed `m', m`, the functions `θ ↦ d^j_{m'm}(θ)` are orthogonal on `[0, π]` with respect to
`sin θ dθ`, and have squared norm `2/(2j+1)` (Varshalovich 4.10.1(1); Edmonds 4.6.1):

  `∫_0^π d^j_{m'm}(θ) d^{j'}_{m'm}(θ) sin θ dθ = 2/(2j+1) · δ_{jj'}`

whenever `j ± m`, `j ± m'`, `j' ± m`, `j' ± m'` are natural numbers.

The proof is the Jacobi form of `d^j_{m'm}` (`wignerSmallD_chamber_A`–`D`): in each of the four
chambers both `d`-functions have the same `(μ, ν)` and degrees `k, k'` with `j - k = j' - k'`
and `2(j-k) = μ + ν`.  The change of variables `x = cos θ` turns the integral into
`√(N_k N_{k'}) · 2^{-(μ+ν)} ∫_{-1}^1 (1-x)^μ (1+x)^ν P_k P_{k'} dx`, which vanishes for `k ≠ k'`
(`jacobi_orthogonal`) and equals `2/(2k+μ+ν+1) = 2/(2j+1)` for `k = k'` (`jacobi_norm_cos`),
the normalisation `N_k = k!(k+μ+ν)!/((k+μ)!(k+ν)!)` cancelling the Jacobi norm exactly.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Polynomial FormalResearch.Special

/-- `∫_0^π sin(θ/2)^{2a} cos(θ/2)^{2b} P_m(cos θ) P_n(cos θ) sin θ dθ = 0` for `m ≠ n`
(Jacobi orthogonality after `x = cos θ`). -/
lemma jacobi_cos_orth (a b m n : ℕ) (h : m ≠ n) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin (θ / 2) ^ (2 * a) * Real.cos (θ / 2) ^ (2 * b) *
        (jacobi (a : ℝ) (b : ℝ) m).eval (Real.cos θ) *
        (jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ) * Real.sin θ = 0 := by
  have hf : Continuous (fun x : ℝ => (1 / 2 ^ (a + b)) * ((1 - x) ^ a * (1 + x) ^ b *
      (jacobi (a : ℝ) (b : ℝ) m).eval x * (jacobi (a : ℝ) (b : ℝ) n).eval x)) := by fun_prop
  have h1 := integral_cos_substitution _ hf
  have hc : ∀ θ : ℝ, 1 + Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 := by
    intro θ
    rw [Real.cos_sq (θ / 2)]
    rw [show 2 * (θ / 2) = θ by ring]; ring
  have hs : ∀ θ : ℝ, 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    intro θ
    have h := Real.cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    rw [Real.sin_sq]; linarith
  have e : ∀ θ : ℝ, (1 / 2 ^ (a + b)) * ((1 - Real.cos θ) ^ a * (1 + Real.cos θ) ^ b *
        (jacobi (a : ℝ) (b : ℝ) m).eval (Real.cos θ) *
        (jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ)) * Real.sin θ =
      Real.sin (θ / 2) ^ (2 * a) * Real.cos (θ / 2) ^ (2 * b) *
        (jacobi (a : ℝ) (b : ℝ) m).eval (Real.cos θ) *
        (jacobi (a : ℝ) (b : ℝ) n).eval (Real.cos θ) * Real.sin θ := by
    intro θ
    rw [hs, hc, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
    have h2 : (2 : ℝ) ^ a ≠ 0 := by positivity
    have h3 : (2 : ℝ) ^ b ≠ 0 := by positivity
    field_simp
  simp only [e] at h1
  rw [h1, intervalIntegral.integral_const_mul, jacobi_orthogonal a b m n h, mul_zero]

/-- Orthonormality of the Jacobi form `wignerJacobiForm μ ν k` for the weight `sin θ dθ`:
the integral is `2/(2k+μ+ν+1)` for `k = k'` and `0` otherwise. -/
theorem wignerJacobiForm_orth (μ ν k k' : ℕ) :
    ∫ θ in (0 : ℝ)..Real.pi, wignerJacobiForm μ ν k θ * wignerJacobiForm μ ν k' θ * Real.sin θ =
      if k = k' then 2 / (2 * (k : ℝ) + μ + ν + 1) else 0 := by
  unfold wignerJacobiForm
  by_cases hkk : k = k'
  · subst hkk
    simp only [↓reduceIte]
    set Q : ℝ := (k.factorial : ℝ) * (k + μ + ν).factorial /
        (((k + μ).factorial : ℝ) * (k + ν).factorial) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have e : ∀ θ : ℝ, Real.sqrt Q * Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
          (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ) *
        (Real.sqrt Q * Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
          (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ)) * Real.sin θ =
        Q * (Real.sin (θ / 2) ^ (2 * μ) * Real.cos (θ / 2) ^ (2 * ν) *
          ((jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ)) ^ 2 * Real.sin θ) := by
      intro θ
      have := Real.mul_self_sqrt hQ0
      calc _ = (Real.sqrt Q * Real.sqrt Q) * (Real.sin (θ / 2) ^ (2 * μ) *
            Real.cos (θ / 2) ^ (2 * ν) *
            ((jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ)) ^ 2 * Real.sin θ) := by ring
        _ = _ := by rw [this]
    simp only [e]
    rw [intervalIntegral.integral_const_mul, jacobi_norm_cos, hQ]
    have h1 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have h2 : (0 : ℝ) < ((k + μ).factorial : ℝ) := by positivity
    have h3 : (0 : ℝ) < ((k + ν).factorial : ℝ) := by positivity
    have h4 : (0 : ℝ) < ((k + μ + ν).factorial : ℝ) := by positivity
    have h5 : (0 : ℝ) < 2 * (k : ℝ) + μ + ν + 1 := by positivity
    field_simp
  · simp only [hkk, ↓reduceIte]
    have e : ∀ θ : ℝ, Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
          (((k + μ).factorial : ℝ) * (k + ν).factorial)) * Real.sin (θ / 2) ^ μ *
          Real.cos (θ / 2) ^ ν * (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ) *
        (Real.sqrt ((k'.factorial : ℝ) * (k' + μ + ν).factorial /
          (((k' + μ).factorial : ℝ) * (k' + ν).factorial)) * Real.sin (θ / 2) ^ μ *
          Real.cos (θ / 2) ^ ν * (jacobi (μ : ℝ) (ν : ℝ) k').eval (Real.cos θ)) *
        Real.sin θ =
        (Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
          (((k + μ).factorial : ℝ) * (k + ν).factorial)) *
         Real.sqrt ((k'.factorial : ℝ) * (k' + μ + ν).factorial /
          (((k' + μ).factorial : ℝ) * (k' + ν).factorial))) *
        (Real.sin (θ / 2) ^ (2 * μ) * Real.cos (θ / 2) ^ (2 * ν) *
          (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ) *
          (jacobi (μ : ℝ) (ν : ℝ) k').eval (Real.cos θ) * Real.sin θ) := by
      intro θ; ring
    simp only [e]
    rw [intervalIntegral.integral_const_mul, jacobi_cos_orth μ ν k k' hkk, mul_zero]

/-! ### Orthogonality in a chamber -/

lemma neg_one_pow_mul_self (μ : ℕ) : (-1 : ℝ) ^ μ * (-1 : ℝ) ^ μ = 1 := by
  rw [← mul_pow]; norm_num

/-- Common core: if both `d^j_{m'm}` and `d^{j'}_{m'm}` are `s · wignerJacobiForm μ ν ·` with the
same `μ, ν`, a sign `s² = 1`, degrees `k, k'`, `j - k = j' - k'` and `2(j-k) = μ+ν`, then the
orthogonality relation holds. -/
lemma wignerSmallD_orth_of_form {j j' m' m : ℚ} {μ ν k k' : ℕ} (s : ℝ) (hs : s * s = 1)
    (hd : ∀ θ, wignerSmallD j m' m θ = s * wignerJacobiForm μ ν k θ)
    (hd' : ∀ θ, wignerSmallD j' m' m θ = s * wignerJacobiForm μ ν k' θ)
    (hk : j - k = j' - k') (hc : 2 * (j - k) = μ + ν) :
    ∫ θ in (0 : ℝ)..Real.pi, wignerSmallD j m' m θ * wignerSmallD j' m' m θ * Real.sin θ =
      if j = j' then 2 / (2 * (j : ℝ) + 1) else 0 := by
  have e : ∀ θ : ℝ, wignerSmallD j m' m θ * wignerSmallD j' m' m θ * Real.sin θ =
      wignerJacobiForm μ ν k θ * wignerJacobiForm μ ν k' θ * Real.sin θ := by
    intro θ
    rw [hd, hd']
    calc _ = (s * s) * (wignerJacobiForm μ ν k θ * wignerJacobiForm μ ν k' θ * Real.sin θ) := by
          ring
      _ = _ := by rw [hs, one_mul]
  simp only [e]
  rw [wignerJacobiForm_orth]
  by_cases hjj : j = j'
  · have hkk : k = k' := by
      have : (k : ℚ) = k' := by rw [hjj] at hk; linarith
      exact_mod_cast this
    have : (2 * (k : ℝ) + μ + ν + 1) = 2 * (j : ℝ) + 1 := by
      have h' : (2 * (k : ℚ) + μ + ν + 1) = 2 * j + 1 := by linarith
      exact_mod_cast h'
    subst hkk
    subst hjj
    simp only [↓reduceIte]
    rw [this]
  · have hkk : k ≠ k' := by
      intro h; apply hjj
      have : (k : ℚ) = k' := by exact_mod_cast h
      linarith
    simp only [hkk, hjj, ↓reduceIte]

lemma isNat_sub' {a b : ℚ} (ha : IsNat a) (hb : IsNat b) (h : b ≤ a) : IsNat (a - b) := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have : q ≤ p := by exact_mod_cast h
  exact ⟨p - q, by push_cast [this]; ring⟩

/-- **Orthogonality and normalisation of Wigner's small `d`-function** (Varshalovich 4.10.1(1),
Edmonds 4.6.1): for `j ± m`, `j ± m'`, `j' ± m`, `j' ± m'` natural,
`∫_0^π d^j_{m'm}(θ) d^{j'}_{m'm}(θ) sin θ dθ = 2/(2j+1) · δ_{jj'}`. -/
theorem wignerSmallD_orthogonal {j j' m' m : ℚ}
    (h1 : IsNat (j + m')) (h2 : IsNat (j - m')) (h3 : IsNat (j + m)) (h4 : IsNat (j - m))
    (h1' : IsNat (j' + m')) (h2' : IsNat (j' - m')) (h3' : IsNat (j' + m))
    (h4' : IsNat (j' - m)) :
    ∫ θ in (0 : ℝ)..Real.pi, wignerSmallD j m' m θ * wignerSmallD j' m' m θ * Real.sin θ =
      if j = j' then 2 / (2 * (j : ℝ) + 1) else 0 := by
  rcases le_total m m' with hmm | hmm <;> rcases le_total 0 (m' + m) with hs | hs
  · -- chamber A: m ≤ m', m' + m ≥ 0
    obtain ⟨μ, hμ⟩ : IsNat (m' - m) := by
      convert isNat_sub' h1 h3 (by linarith) using 1; ring
    obtain ⟨ν, hν⟩ : IsNat (m' + m) := by
      convert isNat_sub' h1 h4 (by linarith) using 1; ring
    obtain ⟨k, hk⟩ := h2
    obtain ⟨k', hk'⟩ := h2'
    refine wignerSmallD_orth_of_form ((-1 : ℝ) ^ μ) (neg_one_pow_mul_self μ)
      (fun θ => wignerSmallD_chamber_A hμ hν hk θ)
      (fun θ => wignerSmallD_chamber_A hμ hν hk' θ) (by linarith) (by linarith)
  · -- chamber B: m ≤ m', m' + m ≤ 0
    obtain ⟨μ, hμ⟩ : IsNat (m' - m) := by
      convert isNat_sub' h1 h3 (by linarith) using 1; ring
    obtain ⟨ν, hν⟩ : IsNat (-(m' + m)) := by
      convert isNat_sub' h2 h3 (by linarith) using 1; ring
    obtain ⟨k, hk⟩ := h3
    obtain ⟨k', hk'⟩ := h3'
    refine wignerSmallD_orth_of_form ((-1 : ℝ) ^ μ) (neg_one_pow_mul_self μ)
      (fun θ => wignerSmallD_chamber_B hμ hν hk θ)
      (fun θ => wignerSmallD_chamber_B hμ hν hk' θ) (by linarith) (by linarith)
  · -- chamber C: m' ≤ m, m' + m ≥ 0
    obtain ⟨μ, hμ⟩ : IsNat (m - m') := by
      convert isNat_sub' h3 h1 (by linarith) using 1; ring
    obtain ⟨ν, hν⟩ : IsNat (m + m') := by
      convert isNat_sub' h3 h2 (by linarith) using 1; ring
    obtain ⟨k, hk⟩ := h4
    obtain ⟨k', hk'⟩ := h4'
    refine wignerSmallD_orth_of_form (1 : ℝ) (by norm_num)
      (fun θ => by rw [wignerSmallD_chamber_C hμ hν hk θ, one_mul])
      (fun θ => by rw [wignerSmallD_chamber_C hμ hν hk' θ, one_mul]) (by linarith) (by linarith)
  · -- chamber D: m' ≤ m, m' + m ≤ 0
    obtain ⟨μ, hμ⟩ : IsNat (m - m') := by
      convert isNat_sub' h2 h4 (by linarith) using 1; ring
    obtain ⟨ν, hν⟩ : IsNat (-(m + m')) := by
      convert isNat_sub' h2 h3 (by linarith) using 1; ring
    obtain ⟨k, hk⟩ := h1
    obtain ⟨k', hk'⟩ := h1'
    refine wignerSmallD_orth_of_form (1 : ℝ) (by norm_num)
      (fun θ => by rw [wignerSmallD_chamber_D hμ hν hk θ, one_mul])
      (fun θ => by rw [wignerSmallD_chamber_D hμ hν hk' θ, one_mul]) (by linarith) (by linarith)

/-- **Normalisation** `∫_0^π (d^j_{m'm}(θ))² sin θ dθ = 2/(2j+1)` for `j ± m`, `j ± m'` natural. -/
theorem wignerSmallD_norm {j m' m : ℚ}
    (h1 : IsNat (j + m')) (h2 : IsNat (j - m')) (h3 : IsNat (j + m)) (h4 : IsNat (j - m)) :
    ∫ θ in (0 : ℝ)..Real.pi, (wignerSmallD j m' m θ) ^ 2 * Real.sin θ = 2 / (2 * (j : ℝ) + 1) := by
  have := wignerSmallD_orthogonal h1 h2 h3 h4 h1 h2 h3 h4
  simpa only [↓reduceIte, sq] using this

/-- info: 'FormalResearch.Wigner.wignerJacobiForm_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerJacobiForm_orth

/-- info: 'FormalResearch.Wigner.wignerSmallD_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_orthogonal

/-- info: 'FormalResearch.Wigner.wignerSmallD_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_norm

end FormalResearch.Wigner

module

public import FormalResearch.FreeFermion.W1Heun

/-!
# The Krawtchouk chain is a Leonard pair; its Heun operator (Weyl W1, `prop:bisp`(i))

Source: `Weyl/free_fermion/paper/parts/model.tex`, Proposition `prop:bisp`(i) ("Krawtchouk chain
`a_n = √(pq(n+1)(N-n))/N`, `b_n = (p(N-n)+qn)/N` on `0 ≤ n ≤ N`, spectrum `{k/N}` ... by
self-duality `(X, Y)` is a Leonard pair, so the Heun operator commutes with `P` exactly
(Theorem `thm:heun`)"), together with `thm:heun` (`W1Heun`).

## Statements formalised (all `N ≥ 1`, `0 < p < 1`, `q = 1 - p`, for arbitrary `N`)

* `krawChain p N` : the symmetric tridiagonal matrix with the paper's `a_n`, `b_n`;
  `krawY` the operator, `krawX = diag(n/N)`.
* `krawY_hasEigenvalue_iff` : the spectrum of `Y` is exactly `{k/N : 0 ≤ k ≤ N}`.
* `krawBasis` (an eigenbasis `f_k`, `Y f_k = (k/N) f_k`; `f_k` is the coefficient vector of the
  polynomial `(r t + s)^k (s t - r)^(N-k)`, `s = √p`, `r = √q`, divided by `√C(N,n)`; generating
  function of the Krawtchouk polynomials) and `krawX_matrix`: the matrix of `X` in `f` is explicit
  tridiagonal with diagonal `(k q + (N-k) p)/N` and links `√(pq)(N-k)/N`, `√(pq) k/N`
  (self-duality, `p ↔ q` and a diagonal rescaling of the chain); `krawX_irreducible`,
  `krawChain_irreducible`: both are irreducible tridiagonal.
* `krawtchouk_heun` : the instance of `W1Heun.heun_commutant`: `H = {X - μ_X, Y - μ_Y}` commutes with
  the spectral projections of `X` and `Y` at any cut, with simple-spectrum Jacobi blocks.

## Method (no Krawtchouk polynomial theory in the library)

Both the eigen-equation `Y f_k = (k/N) f_k` and the duality `X f_k = α f_k + β f_{k+1} + γ f_{k-1}`
come from the generating polynomials `g_k = u^k v^{N-k}`, `u = r t + s`, `v = s t - r`
(`u' = r`, `v' = s`, `t = s v + r u`, `s u - r v = 1`): `Y` is the differential operator
`L = N s u - u v d/dt` on polynomials of degree `≤ N` (acting on coefficients divided by `√C(N,n)`),
and `L g_k = k g_k` (`kL_kG`); `X = t d/dt` gives `t g_k' = (k r² + (N-k) s²) g_k + s r (k g_{k-1} +
(N-k) g_{k+1})` (`X_mul_derivative_kG`).  Eigenvectors for distinct eigenvalues are independent,
so `f` is a basis.

## Not formalised / remarks

The paper says only "by self-duality"; here the explicit duality is proved.  The Krawtchouk
*orthogonality* (that `f` is orthogonal, i.e. `X` self-adjoint in `f`) is not needed for
`thm:heun` and is not proved; the real-symmetric form of `Y` is by definition.  The travel-time
statements of `prop:bisp` (continuum travel time, `O(e^{-cN})` commutator bounds, the global class)
are analysis and are not formalised; the exact algebra around `eq:bispD`, `eq:bispF` is in
`W1Bispectral`.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Polynomial Matrix Module

section Poly

variable (s r : ℝ)

/-- `u = r X + s`. -/
noncomputable def kU : ℝ[X] := C r * X + C s
/-- `v = s X - r`. -/
noncomputable def kV : ℝ[X] := C s * X - C r
/-- `g_k = u^k v^(N-k)`. -/
noncomputable def kG (N k : ℕ) : ℝ[X] := kU s r ^ k * kV s r ^ (N - k)

/-- The differential operator whose coefficient form is the Krawtchouk chain. -/
noncomputable def kL (N : ℕ) (Q : ℝ[X]) : ℝ[X] :=
  C (s ^ 2) * (N : ℝ[X]) * Q + C (r ^ 2 - s ^ 2) * (X * derivative Q) +
    C (s * r) * (derivative Q + (N : ℝ[X]) * X * Q - X ^ 2 * derivative Q)

theorem derivative_kU : derivative (kU s r) = C r := by simp [kU]
theorem derivative_kV : derivative (kV s r) = C s := by simp [kV]

theorem derivative_kUV (k l : ℕ) :
    derivative (kU s r ^ k * kV s r ^ l) =
      (k : ℝ[X]) * C r * kU s r ^ (k - 1) * kV s r ^ l +
        (l : ℝ[X]) * C s * kU s r ^ k * kV s r ^ (l - 1) := by
  simp only [derivative_mul, derivative_pow, derivative_kU, derivative_kV, ← C_eq_natCast]
  ring

theorem kUV_mul_deriv (k l : ℕ) :
    kU s r * kV s r * derivative (kU s r ^ k * kV s r ^ l) =
      ((k : ℝ[X]) * C r * kV s r + (l : ℝ[X]) * C s * kU s r) * (kU s r ^ k * kV s r ^ l) := by
  rw [derivative_kUV]
  rcases k with _ | k <;> rcases l with _ | l <;> simp [pow_succ] <;> ring

theorem kL_kG (hs : s ^ 2 + r ^ 2 = 1) (N k : ℕ) (hk : k ≤ N) :
    kL s r N (kG s r N k) = (k : ℝ[X]) * kG s r N k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hl : k + l - k = l := by omega
  have hmain : kL s r (k + l) (kU s r ^ k * kV s r ^ l) = (k : ℝ[X]) * (kU s r ^ k * kV s r ^ l) := by
    have hs' : C s ^ 2 + C r ^ 2 = (1 : ℝ[X]) := by
      rw [← C_pow, ← C_pow, ← C_add, hs, C_1]
    have hbr : C (r ^ 2 - s ^ 2) * X + C (s * r) * (1 - X ^ 2) = -(kU s r * kV s r) := by
      simp only [kU, kV, map_sub, map_mul, map_pow]; ring
    have hal : C (s ^ 2) * ((k + l : ℕ) : ℝ[X]) + C (s * r) * ((k + l : ℕ) : ℝ[X]) * X =
        ((k + l : ℕ) : ℝ[X]) * C s * kU s r := by
      simp only [kU, map_mul, map_pow]; ring
    have h1 : kL s r (k + l) (kU s r ^ k * kV s r ^ l) =
        ((k + l : ℕ) : ℝ[X]) * C s * kU s r * (kU s r ^ k * kV s r ^ l) -
          kU s r * kV s r * derivative (kU s r ^ k * kV s r ^ l) := by
      unfold kL
      have := hbr
      linear_combination (derivative (kU s r ^ k * kV s r ^ l)) * hbr +
        (kU s r ^ k * kV s r ^ l) * hal
    rw [h1, kUV_mul_deriv]
    have h2 : C s * kU s r - C r * kV s r = 1 := by
      simp only [kU, kV]; linear_combination hs'
    push_cast
    linear_combination ((k : ℝ[X]) * (kU s r ^ k * kV s r ^ l)) * h2
  simpa [kG, hl] using hmain

theorem X_eq_kUV (hs : s ^ 2 + r ^ 2 = 1) : (X : ℝ[X]) = C s * kV s r + C r * kU s r := by
  have hs' : C s ^ 2 + C r ^ 2 = (1 : ℝ[X]) := by
    rw [← C_pow, ← C_pow, ← C_add, hs, C_1]
  simp only [kU, kV]
  linear_combination (-(X : ℝ[X])) * hs'

theorem X_mul_derivative_kUV (hs : s ^ 2 + r ^ 2 = 1) (k l : ℕ) :
    X * derivative (kU s r ^ k * kV s r ^ l) =
      ((k : ℝ[X]) * C r ^ 2 + (l : ℝ[X]) * C s ^ 2) * (kU s r ^ k * kV s r ^ l) +
        C s * C r * ((k : ℝ[X]) * (kU s r ^ (k - 1) * kV s r ^ (l + 1)) +
          (l : ℝ[X]) * (kU s r ^ (k + 1) * kV s r ^ (l - 1))) := by
  rw [derivative_kUV, X_eq_kUV s r hs]
  rcases k with _ | k <;> rcases l with _ | l <;> simp [pow_succ] <;> ring

theorem X_mul_derivative_kG (hs : s ^ 2 + r ^ 2 = 1) (k l : ℕ) :
    X * derivative (kG s r (k + l) k) =
      C ((k : ℝ) * r ^ 2 + l * s ^ 2) * kG s r (k + l) k +
        C (s * r * l) * kG s r (k + l) (k + 1) + C (s * r * k) * kG s r (k + l) (k - 1) := by
  have h := X_mul_derivative_kUV s r hs k l
  have e1 : k + l - k = l := by omega
  have e2 : k + l - (k + 1) = l - 1 := by omega
  unfold kG
  rw [e1, e2, h]
  simp only [map_add, map_mul, map_pow, map_natCast]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; ring
  · have e3 : k + l - (k - 1) = l + 1 := by omega
    rw [e3]; ring

end Poly
section Chain

variable (p : ℝ) (N : ℕ)

/-- Off-diagonal chain coefficient `a_n = √(p q (n+1)(N-n)) / N`, `q = 1 - p` (paper `prop:bisp`(i)). -/
noncomputable def krawA (n : ℕ) : ℝ := √(p * (1 - p) * (((n : ℝ) + 1) * ((N : ℝ) - n))) / N

/-- Diagonal chain coefficient `b_n = (p (N-n) + q n) / N`. -/
noncomputable def krawB (n : ℕ) : ℝ := (p * ((N : ℝ) - n) + (1 - p) * n) / N

/-- The Krawtchouk chain as a symmetric tridiagonal matrix on `{0, …, N}`. -/
noncomputable def krawChain : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if i = j then krawB p N i else if (j : ℕ) = i + 1 then krawA p N i
    else if (i : ℕ) = j + 1 then krawA p N j else 0

theorem krawChain_mulVec (v : ℕ → ℝ) (hv : ∀ m, N < m → v m = 0) (n : Fin (N + 1)) :
    (krawChain p N *ᵥ (fun j : Fin (N + 1) => v j)) n =
      krawB p N n * v n + krawA p N n * v (n + 1) +
        (if (n : ℕ) = 0 then 0 else krawA p N (n - 1) * v (n - 1)) := by
  have hrow : ∀ j : Fin (N + 1), krawChain p N n j = (if n = j then krawB p N n else 0) +
      (if (j : ℕ) = n + 1 then krawA p N n else 0) +
        (if (n : ℕ) = j + 1 then krawA p N j else 0) := by
    intro j
    unfold krawChain
    simp only [Matrix.of_apply]
    by_cases h1 : n = j
    · subst h1; simp
    · have h1' : (n : ℕ) ≠ j := fun h => h1 (Fin.ext h)
      by_cases h2 : (j : ℕ) = n + 1
      · have : ¬ (n : ℕ) = j + 1 := by omega
        have h2' : ((j : ℕ) = n + 1) = True := eq_true h2
        simp only [h1, h2', this, ↓reduceIte]; simp
      · by_cases h3 : (n : ℕ) = j + 1
        · have h3' : ((n : ℕ) = j + 1) = True := eq_true h3
          simp only [h1, h2, h3', ↓reduceIte]; simp
        · simp only [h1, h2, h3, ↓reduceIte]; simp
  simp only [Matrix.mulVec, dotProduct, hrow, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  congr 1
  · simp
  · rw [Fin.sum_univ_eq_sum_range (fun m => if m = (n : ℕ) + 1 then krawA p N n * v m else 0) (N + 1)]
    rw [Finset.sum_ite_eq']
    by_cases h : (n : ℕ) + 1 ∈ Finset.range (N + 1)
    · simp [h]
    · simp only [h, ite_false]
      rw [hv _ (by simp at h; omega)]; simp
  · rw [Fin.sum_univ_eq_sum_range (fun m => if (n : ℕ) = m + 1 then krawA p N m * v m else 0) (N + 1)]
    by_cases h0 : (n : ℕ) = 0
    · simp [h0]
    · rw [Finset.sum_eq_single ((n : ℕ) - 1)]
      · have : (n : ℕ) = (n - 1 : ℕ) + 1 := by omega
        simp [h0, ← this]
      · intro m _ hm
        have : ¬ (n : ℕ) = m + 1 := by omega
        simp [this]
      · intro h
        exfalso; apply h
        simp

theorem coeff_natCast_mul' (N : ℕ) (Q : ℝ[X]) (m : ℕ) :
    ((N : ℝ[X]) * Q).coeff m = N * Q.coeff m := by
  rw [← C_eq_natCast, coeff_C_mul]

theorem coeff_kL_zero (N : ℕ) (Q : ℝ[X]) :
    (kL s r N Q).coeff 0 = N * s ^ 2 * Q.coeff 0 + s * r * Q.coeff 1 := by
  unfold kL
  simp only [coeff_add, coeff_sub, coeff_C_mul, pow_two, mul_assoc, coeff_natCast_mul',
    coeff_X_mul_zero, coeff_derivative]
  simp
  ring

theorem coeff_kL_succ (N : ℕ) (Q : ℝ[X]) (m : ℕ) :
    (kL s r N Q).coeff (m + 1) = (N * s ^ 2 + (r ^ 2 - s ^ 2) * (m + 1)) * Q.coeff (m + 1) +
      s * r * (m + 2) * Q.coeff (m + 2) + s * r * (N - m) * Q.coeff m := by
  unfold kL
  simp only [coeff_add, coeff_sub, coeff_C_mul, pow_two, mul_assoc, coeff_natCast_mul',
    coeff_X_mul]
  rcases m with _ | m
  · simp [coeff_derivative]
    ring
  · simp only [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- Coefficient vector `Q_m / √C(N,m)` of a polynomial (the orthonormalising weight of the chain). -/
noncomputable def kc (N : ℕ) (Q : ℝ[X]) (m : ℕ) : ℝ := Q.coeff m / √(N.choose m : ℝ)

theorem kc_eq_zero (N : ℕ) (Q : ℝ[X]) (m : ℕ) (hm : N < m) : kc N Q m = 0 := by
  simp [kc, Nat.choose_eq_zero_of_lt hm]

theorem choose_rel (N m : ℕ) (hm : m < N) :
    ((N.choose (m + 1) : ℕ) : ℝ) * (m + 1) = (N.choose m : ℝ) * (N - m) := by
  have := Nat.choose_succ_right_eq N m
  have h2 : ((N.choose (m + 1) * (m + 1) : ℕ) : ℝ) = ((N.choose m * (N - m) : ℕ) : ℝ) := by
    rw [this]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hm.le] at h2
  push_cast at h2
  exact h2

theorem sqrt_id_A (N m : ℕ) (hm : m < N) :
    √(((m : ℝ) + 1) * ((N : ℝ) - m)) * √(N.choose m : ℝ) =
      (m + 1) * √(N.choose (m + 1) : ℝ) := by
  have h := choose_rel N m hm
  have hNm : (0 : ℝ) ≤ (N : ℝ) - m := by
    have : (m : ℝ) < N := by exact_mod_cast hm
    linarith
  rw [← Real.sqrt_mul (by positivity)]
  have : (((m : ℝ) + 1) * ((N : ℝ) - m)) * (N.choose m : ℝ) =
      ((m : ℝ) + 1) ^ 2 * (N.choose (m + 1) : ℝ) := by
    linear_combination (-((m : ℝ) + 1)) * h
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem sqrt_id_B (N m : ℕ) (hm : m < N) :
    √(((m : ℝ) + 1) * ((N : ℝ) - m)) * √(N.choose (m + 1) : ℝ) =
      ((N : ℝ) - m) * √(N.choose m : ℝ) := by
  have h := choose_rel N m hm
  have hNm : (0 : ℝ) ≤ (N : ℝ) - m := by
    have : (m : ℝ) < N := by exact_mod_cast hm
    linarith
  rw [← Real.sqrt_mul (by positivity)]
  have : (((m : ℝ) + 1) * ((N : ℝ) - m)) * (N.choose (m + 1) : ℝ) =
      ((N : ℝ) - m) ^ 2 * (N.choose m : ℝ) := by
    linear_combination ((N : ℝ) - m) * h
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hNm]

theorem krawA_eq (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : m < N) :
    krawA p N m = √p * √(1 - p) * √(((m : ℝ) + 1) * ((N : ℝ) - m)) / N := by
  have hNm : (0 : ℝ) ≤ (N : ℝ) - m := by
    have : (m : ℝ) < N := by exact_mod_cast hm
    linarith
  unfold krawA
  rw [Real.sqrt_mul (by nlinarith), Real.sqrt_mul hp.le]

theorem krawA_top : krawA p N N = 0 := by
  simp [krawA]

theorem key1 (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (Q : ℝ[X]) (m : ℕ) (hm : m < N) :
    (N : ℝ) * (krawA p N m * kc N Q (m + 1)) =
      √p * √(1 - p) * ((m : ℝ) + 1) * Q.coeff (m + 1) / √(N.choose m : ℝ) := by
  have hA := sqrt_id_A N m hm
  have h0 : 0 < √(N.choose m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hm.le)
  have h1 : 0 < √(N.choose (m + 1) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hm)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [krawA_eq p N hp hp1 m hm]
  unfold kc
  field_simp
  linear_combination (Q.coeff (m + 1)) * hA

theorem key2 (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (Q : ℝ[X]) (m : ℕ) (hm : m < N) :
    (N : ℝ) * (krawA p N m * kc N Q m) =
      √p * √(1 - p) * ((N : ℝ) - m) * Q.coeff m / √(N.choose (m + 1) : ℝ) := by
  have hB := sqrt_id_B N m hm
  have h0 : 0 < √(N.choose m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hm.le)
  have h1 : 0 < √(N.choose (m + 1) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hm)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [krawA_eq p N hp hp1 m hm]
  unfold kc
  field_simp
  linear_combination (Q.coeff m) * hB

theorem krawChain_kc (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (Q : ℝ[X])
    (hQ : Q.coeff (N + 1) = 0) (n : Fin (N + 1)) :
    (N : ℝ) * (krawChain p N *ᵥ (fun j : Fin (N + 1) => kc N Q j)) n =
      kc N (kL (√p) (√(1 - p)) N Q) n := by
  rw [krawChain_mulVec p N (kc N Q) (fun m hm => kc_eq_zero N Q m hm) n]
  have hs2 : √p ^ 2 = p := Real.sq_sqrt hp.le
  have hr2 : √(1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hb : (N : ℝ) * (krawB p N n * kc N Q n) =
      (p * ((N : ℝ) - n) + (1 - p) * n) * Q.coeff n / √(N.choose n : ℝ) := by
    unfold krawB kc; field_simp
  have hn := n.2
  have hnN : (n : ℕ) ≤ N := by omega
  have hc1 : (N : ℝ) * (krawA p N n * kc N Q (n + 1)) =
      √p * √(1 - p) * ((n : ℝ) + 1) * Q.coeff (n + 1) / √(N.choose n : ℝ) := by
    rcases hnN.lt_or_eq with h | h
    · exact key1 p N hp hp1 hN Q n h
    · rw [h, krawA_top p N]; simp [hQ]
  have hmain : ∀ m : ℕ, (n : ℕ) = m + 1 → (N : ℝ) * (krawA p N m * kc N Q m) =
      √p * √(1 - p) * ((N : ℝ) - m) * Q.coeff m / √(N.choose (m + 1) : ℝ) := by
    intro m hm
    exact key2 p N hp hp1 hN Q m (by omega)
  rcases hz : (n : ℕ) with _ | m
  · rw [hz] at hb hc1
    simp only [ite_true, mul_add, add_zero]
    rw [hb, hc1]
    simp only [kc, coeff_kL_zero, hs2, Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one,
      Nat.cast_zero]
    ring
  · rw [hz] at hb hc1
    have h2 := hmain m hz
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, mul_add]
    rw [hb, hc1, Nat.add_sub_cancel, h2]
    simp only [kc, coeff_kL_succ, hs2, hr2]
    have hc : √(N.choose (m + 1) : ℝ) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.choose_pos (by omega)
    push_cast
    ring

theorem natDegree_kG_le (s r : ℝ) (N k : ℕ) (hk : k ≤ N) : (kG s r N k).natDegree ≤ N := by
  have hu : (kU s r).natDegree ≤ 1 := by
    unfold kU; exact natDegree_linear_le
  have hv : (kV s r).natDegree ≤ 1 := by
    have : kV s r = C s * X + C (-r) := by simp [kV, sub_eq_add_neg]
    rw [this]; exact natDegree_linear_le
  unfold kG
  calc (kU s r ^ k * kV s r ^ (N - k)).natDegree
      ≤ (kU s r ^ k).natDegree + (kV s r ^ (N - k)).natDegree := natDegree_mul_le
    _ ≤ k * 1 + (N - k) * 1 := by
        gcongr
        · exact natDegree_pow_le.trans (by gcongr)
        · exact natDegree_pow_le.trans (by gcongr)
    _ = N := by omega

theorem coeff_kG_succ (s r : ℝ) (N k : ℕ) (hk : k ≤ N) : (kG s r N k).coeff (N + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (by have := natDegree_kG_le s r N k hk; omega)

/-- The `k`-th eigenvector of the Krawtchouk chain: the coefficient vector of `u^k v^(N-k)`. -/
noncomputable def krawF (N k : ℕ) : Fin (N + 1) → ℝ :=
  fun n => kc N (kG (√p) (√(1 - p)) N k) n

theorem krawF_eigen (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (k : ℕ) (hk : k ≤ N) :
    krawChain p N *ᵥ krawF p N k = ((k : ℝ) / N) • krawF p N k := by
  have hs : √p ^ 2 + √(1 - p) ^ 2 = 1 := by
    rw [Real.sq_sqrt hp.le, Real.sq_sqrt (by linarith)]; ring
  ext n
  have h := krawChain_kc p N hp hp1 hN (kG (√p) (√(1 - p)) N k) (coeff_kG_succ _ _ N k hk) n
  rw [kL_kG _ _ hs N k hk] at h
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h2 : kc N ((k : ℝ[X]) * kG (√p) (√(1 - p)) N k) n =
      k * kc N (kG (√p) (√(1 - p)) N k) n := by
    unfold kc; rw [coeff_natCast_mul']; ring
  rw [h2] at h
  simp only [Pi.smul_apply, smul_eq_mul, krawF]
  change (krawChain p N *ᵥ fun j : Fin (N + 1) => kc N (kG (√p) (√(1 - p)) N k) j) n = _
  field_simp
  linarith

theorem krawF_ne_zero (hp : 0 < p) (hp1 : p < 1) (k : ℕ) : krawF p N k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hr : 0 < √(1 - p) := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < √p := Real.sqrt_pos.mpr hp
  simp only [krawF, Pi.zero_apply, kc, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one,
    Real.sqrt_one, div_one, coeff_zero_eq_eval_zero] at h0
  simp [kG, kU, kV] at h0
  rcases h0 with h0 | h0
  · exact hs.ne' h0.1
  · exact hr.ne' h0.1

theorem krawX_eigen (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (k : ℕ) (hk : k ≤ N) :
    Matrix.diagonal (fun n : Fin (N + 1) => (n : ℝ) / N) *ᵥ krawF p N k =
      ((k * (1 - p) + (N - k) * p) / N) • krawF p N k +
        (√p * √(1 - p) * (N - k) / N) • krawF p N (k + 1) +
        (√p * √(1 - p) * k / N) • krawF p N (k - 1) := by
  have hs2 : √p ^ 2 = p := Real.sq_sqrt hp.le
  have hr2 : √(1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hs : √p ^ 2 + √(1 - p) ^ 2 = 1 := by rw [hs2, hr2]; ring
  have hN' : (N : ℝ) ≠ 0 := by positivity
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := X_mul_derivative_kG (√p) (√(1 - p)) hs k l
  ext n
  simp only [Matrix.mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, krawF]
  have hc : (n : ℝ) * kc (k + l) (kG (√p) (√(1 - p)) (k + l) k) n =
      kc (k + l) (X * derivative (kG (√p) (√(1 - p)) (k + l) k)) n := by
    unfold kc
    rcases hn : (n : ℕ) with _ | m
    · simp
    · rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  rw [h] at hc
  simp only [kc, coeff_add, coeff_C_mul, hs2, hr2] at hc ⊢
  push_cast
  linear_combination (1 / ((k : ℝ) + l)) * hc

end Chain

section Pair

variable (p : ℝ) (N : ℕ)

/-- The chain operator `Y` on `ℝ^{N+1}`. -/
noncomputable def krawY : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) := Matrix.toLin' (krawChain p N)

/-- The position operator `X = diag(n/N)` on `ℝ^{N+1}`. -/
noncomputable def krawX : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
  Matrix.toLin' (Matrix.diagonal fun n : Fin (N + 1) => (n : ℝ) / N)

theorem krawF_linearIndependent (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    LinearIndependent ℝ (fun k : Fin (N + 1) => krawF p N k) := by
  refine Module.End.eigenvectors_linearIndependent' (krawY p N) (fun k : Fin (N + 1) => (k : ℝ) / N) ?_
    (fun k => krawF p N k) (fun k => ⟨?_, krawF_ne_zero p N hp hp1 k⟩)
  · intro a b hab
    have hN' : (N : ℝ) ≠ 0 := by positivity
    have : (a : ℝ) = b := by
      have := hab; field_simp at this; exact this
    exact Fin.ext (by exact_mod_cast this)
  · rw [Module.End.mem_eigenspace_iff]
    exact krawF_eigen p N hp hp1 hN k (by omega)

/-- The eigenbasis `f_k` of the chain `Y`: `f_k` is the coefficient vector of `u^k v^(N-k)`. -/
noncomputable def krawBasis (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    Basis (Fin (N + 1)) ℝ (Fin (N + 1) → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (krawF_linearIndependent p N hp hp1 hN) (by simp)

theorem krawBasis_apply (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (k : Fin (N + 1)) :
    krawBasis p N hp hp1 hN k = krawF p N k := by
  simp [krawBasis]

theorem krawY_basis (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (k : Fin (N + 1)) :
    krawY p N (krawBasis p N hp hp1 hN k) = ((k : ℝ) / N) • krawBasis p N hp hp1 hN k := by
  rw [krawBasis_apply]
  exact krawF_eigen p N hp hp1 hN k (by omega)

theorem krawX_basis_e (n : Fin (N + 1)) :
    krawX N (Pi.basisFun ℝ (Fin (N + 1)) n) = ((n : ℝ) / N) • Pi.basisFun ℝ (Fin (N + 1)) n := by
  ext j
  by_cases h : j = n <;> simp [krawX, Matrix.toLin'_apply, Matrix.mulVec_diagonal, h]

/-- `f_m` for every natural `m` (zero beyond the range), to state the three-term action uniformly. -/
noncomputable def krawBasisN (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (m : ℕ) :
    Fin (N + 1) → ℝ :=
  if h : m < N + 1 then krawBasis p N hp hp1 hN ⟨m, h⟩ else 0

theorem repr_krawBasisN (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (m : ℕ) (j : Fin (N + 1)) :
    (krawBasis p N hp hp1 hN).repr (krawBasisN p N hp hp1 hN m) j =
      if (j : ℕ) = m then 1 else 0 := by
  unfold krawBasisN
  by_cases h : m < N + 1
  · simp only [h, ↓reduceDIte]
    rw [Basis.repr_self, Finsupp.single_apply]
    by_cases hj : (j : ℕ) = m
    · have : (⟨m, h⟩ : Fin (N + 1)) = j := Fin.ext hj.symm
      simp [this, hj]
    · have : ¬ (⟨m, h⟩ : Fin (N + 1)) = j := fun e => hj (by rw [← e])
      simp [this, hj]
  · simp only [h, ↓reduceDIte]
    have : (j : ℕ) ≠ m := by have := j.2; omega
    simp [this]

/-- Matrix of the position operator `X` in the eigenbasis `f` of the chain (self-duality). -/
theorem krawX_matrix (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (j k : Fin (N + 1)) :
    LinearMap.toMatrixAlgEquiv (krawBasis p N hp hp1 hN) (krawX N) j k =
      (if j = k then ((k : ℝ) * (1 - p) + (N - k) * p) / N else 0) +
        (if (j : ℕ) = k + 1 then √p * √(1 - p) * (N - k) / N else 0) +
        (if (j : ℕ) + 1 = k then √p * √(1 - p) * k / N else 0) := by
  rw [LinearMap.toMatrixAlgEquiv_apply]
  have hX : krawX N (krawBasis p N hp hp1 hN k) =
      (((k : ℝ) * (1 - p) + (N - k) * p) / N) • krawBasis p N hp hp1 hN k +
        (√p * √(1 - p) * (N - k) / N) • krawBasisN p N hp hp1 hN (k + 1) +
        (√p * √(1 - p) * k / N) • krawBasisN p N hp hp1 hN (k - 1) := by
    rw [krawBasis_apply]
    have h := krawX_eigen p N hp hp1 hN k (by omega)
    have e : krawX N (krawF p N k) = Matrix.diagonal (fun n : Fin (N + 1) => (n : ℝ) / N) *ᵥ
        krawF p N k := by simp [krawX, Matrix.toLin'_apply]
    have hf : ∀ m : ℕ, m ≤ N → krawF p N m = krawBasisN p N hp hp1 hN m := by
      intro m hm
      unfold krawBasisN
      have hm' : m < N + 1 := by omega
      simp only [hm', ↓reduceDIte, krawBasis_apply]
    have hB : (√p * √(1 - p) * (N - k) / N) • krawF p N (k + 1) =
        (√p * √(1 - p) * (N - k) / N) • krawBasisN p N hp hp1 hN (k + 1) := by
      rcases (show (k : ℕ) < N ∨ (k : ℕ) = N by omega) with h1 | h1
      · rw [hf (k + 1) (by omega)]
      · simp [h1]
    have hC : (√p * √(1 - p) * k / N) • krawF p N (k - 1) =
        (√p * √(1 - p) * k / N) • krawBasisN p N hp hp1 hN (k - 1) := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
      · simp [h0]
      · rw [hf (k - 1) (by omega)]
    rw [e, h, hB, hC]
  rw [hX]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_krawBasisN,
    Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  have h3 : (√p * √(1 - p) * (k : ℕ) / N) * (if (j : ℕ) = k - 1 then (1 : ℝ) else 0) =
      if (j : ℕ) + 1 = k then √p * √(1 - p) * (k : ℕ) / N else 0 := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
    · simp [h0]
    · have : ((j : ℕ) = k - 1) ↔ ((j : ℕ) + 1 = k) := by omega
      simp only [this]; split_ifs <;> simp
  rw [h3]
  simp only [eq_comm (a := k)]
  simp

theorem krawX_irreducible (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv (krawBasis p N hp hp1 hN) (krawX N)) := by
  have hs : 0 < √p := Real.sqrt_pos.mpr hp
  have hr : 0 < √(1 - p) := Real.sqrt_pos.mpr (by linarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · rw [krawX_matrix] at hij
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h2 h3
    apply hij
    have a1 : ¬ i = j := h1
    have a2 : ¬ (i : ℕ) = j + 1 := fun h => h3 h.symm
    have a3 : ¬ (i : ℕ) + 1 = j := h2
    simp [a1, a2, a3]
  · simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hij
    have hj : (j : ℕ) ≤ N := by have := j.2; omega
    have hij' : i ≠ j := fun h => by rw [h] at hij; omega
    have hji' : j ≠ i := fun h => hij' h.symm
    constructor
    · rw [krawX_matrix]
      have a2 : ¬ (i : ℕ) = j + 1 := by omega
      have a3 : (i : ℕ) + 1 = j := hij
      simp only [hij', a2, ↓reduceIte, a3, add_zero, zero_add]
      have : (0 : ℝ) < j := by
        have : 0 < (j : ℕ) := by omega
        exact_mod_cast this
      positivity
    · rw [krawX_matrix]
      have a2 : (j : ℕ) = i + 1 := hij.symm
      have a3 : ¬ (j : ℕ) + 1 = i := by omega
      simp only [hji', a2, ↓reduceIte, zero_add]
      have : (0 : ℝ) < N - i := by
        have : (i : ℕ) < N := by omega
        have : (i : ℝ) < N := by exact_mod_cast this
        linarith
      positivity

theorem krawChain_irreducible (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    IsIrreducibleTridiag (krawChain p N) := by
  have hq : 0 < 1 - p := by linarith
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h2 h3
    apply hij
    have a2 : ¬ (j : ℕ) = i + 1 := fun h => h2 h.symm
    have a3 : ¬ (i : ℕ) = j + 1 := fun h => h3 h.symm
    simp [krawChain, h1, a2, a3]
  · simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hij
    have hj : (j : ℕ) ≤ N := by have := j.2; omega
    have hij' : i ≠ j := fun h => by rw [h] at hij; omega
    have hapos : ∀ m : ℕ, m < N → krawA p N m ≠ 0 := by
      intro m hm
      rw [krawA_eq p N hp hp1 m hm]
      have : (m : ℝ) < N := by exact_mod_cast hm
      have : 0 < √(((m : ℝ) + 1) * ((N : ℝ) - m)) := Real.sqrt_pos.mpr (by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith)
      have hs : 0 < √p := Real.sqrt_pos.mpr hp
      have hr : 0 < √(1 - p) := Real.sqrt_pos.mpr hq
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    constructor
    · simp only [krawChain, Matrix.of_apply, hij', ↓reduceIte, hij.symm]
      exact hapos i (by omega)
    · have a3 : ¬ (j : ℕ) = i + 1 → False := fun h => h hij.symm
      have : ¬ j = i := fun h => hij' h.symm
      have a4 : ¬ (j : ℕ) + 1 = i := by omega
      simp only [krawChain, Matrix.of_apply, this, ↓reduceIte]
      have a6 : (j : ℕ) = i + 1 := hij.symm
      simp only [↓reduceIte, a6]
      have a7 : ¬ (i : ℕ) = (i : ℕ) + 1 + 1 := by omega
      simp only [a7, ↓reduceIte]
      exact hapos i (by omega)

theorem krawY_matrix_e : LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (N + 1))) (krawY p N) =
    krawChain p N := by
  ext i j
  simp [LinearMap.toMatrixAlgEquiv_apply, krawY, Matrix.toLin'_apply, Matrix.mulVec_single]

/-- **Krawtchouk chain is a Leonard pair; its Heun operator commutes with both spectral projections
exactly** (paper `prop:bisp`(i), via `thm:heun`).

For `0 < p < 1`, `N ≥ 1`, `Y` the Krawtchouk chain of the paper (`a_n = √(pq(n+1)(N-n))/N`,
`b_n = (p(N-n)+qn)/N`) and `X = diag(n/N)`: `X` has eigenbasis `e` (standard basis) and `Y` has the
eigenbasis `f_k` (`krawBasis`), both with spectrum `{k/N}`, `Y` is irreducible tridiagonal in `e` and
`X` irreducible tridiagonal in `f` (self-duality), and for every pair of cuts the Heun operator
`H = {X - μ_X, Y - μ_Y}` (midgaps) commutes with the spectral projections `W` (of `X`, on
`n ≤ K`) and `P` (of `Y`, on `k ≤ M`) and restricts to simple-spectrum Jacobi blocks. -/
theorem krawtchouk_heun (p : ℝ) (N : ℕ) (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N)
    {K K' M M' : Fin (N + 1)} (hK : K ⋖ K') (hM : M ⋖ M')
    (W P : (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ))
    (hW : ∀ n, W (Pi.basisFun ℝ (Fin (N + 1)) n) =
      if n ≤ K then Pi.basisFun ℝ (Fin (N + 1)) n else 0)
    (hP : ∀ n, P (krawBasis p N hp hp1 hN n) =
      if n ≤ M then krawBasis p N hp hp1 hN n else 0) :
    let H := heun ℝ (krawX N) (krawY p N) ((((K : ℕ) : ℝ) / N + ((K' : ℕ) : ℝ) / N) / 2)
      ((((M : ℕ) : ℝ) / N + ((M' : ℕ) : ℝ) / N) / 2)
    H * W = W * H ∧ H * P = P * H ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin (N + 1))) H) K ∧
      IsJacobiWithCut (LinearMap.toMatrixAlgEquiv (krawBasis p N hp hp1 hN) H) M ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker W) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.range P) ≤ 1) ∧
      (∀ lam : ℝ, finrank ℝ ↥(Module.End.eigenspace H lam ⊓ LinearMap.ker P) ≤ 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : StrictMono (fun n : Fin (N + 1) => ((n : ℕ) : ℝ) / N) := by
    intro a b hab
    have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab
    exact div_lt_div_of_pos_right this hNpos
  exact heun_commutant (Pi.basisFun ℝ (Fin (N + 1))) (krawBasis p N hp hp1 hN) (krawX N)
    (krawY p N) W P (fun n => ((n : ℕ) : ℝ) / N) (fun n => ((n : ℕ) : ℝ) / N) hmono hmono
    (krawX_basis_e N) (krawY_basis p N hp hp1 hN)
    (by rw [krawY_matrix_e]; exact krawChain_irreducible p N hp hp1 hN)
    (krawX_irreducible p N hp hp1 hN) hK hM hW hP

/-- The spectrum of the Krawtchouk chain is exactly `{k/N : 0 ≤ k ≤ N}` (paper `prop:bisp`(i)). -/
theorem krawY_hasEigenvalue_iff (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) (lam : ℝ) :
    Module.End.HasEigenvalue (krawY p N) lam ↔ ∃ k : Fin (N + 1), lam = (k : ℝ) / N := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    set f := krawBasis p N hp hp1 hN with hf
    obtain ⟨hvE, hv0⟩ := hv
    have hvE' : krawY p N v = lam • v := Module.End.mem_eigenspace_iff.mp hvE
    obtain ⟨k, hk⟩ : ∃ k, f.repr v k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hv0
      apply f.repr.injective
      ext k; simp [hcon k]
    have hY : f.repr (krawY p N v) k = ((k : ℝ) / N) * f.repr v k := by
      conv_lhs => rw [← f.sum_repr v]
      simp only [map_sum, map_smul, hf, krawY_basis, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
      simp
      ring
    rw [hvE'] at hY
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hY
    exact ⟨k, mul_right_cancel₀ hk (by linarith)⟩
  · rintro ⟨k, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (krawY_basis p N hp hp1 hN k),
        by rw [krawBasis_apply]; exact krawF_ne_zero p N hp hp1 k⟩

/-- info: 'FormalResearch.FreeFermion.krawtchouk_heun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawtchouk_heun

/-- info: 'FormalResearch.FreeFermion.krawY_hasEigenvalue_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawY_hasEigenvalue_iff

end Pair

end FormalResearch.FreeFermion

module

public import Mathlib
public import FormalResearch.Racah.P2MomentPolynomial

/-!
# Local calculus for centered Wigner rank recurrences: the exact algebra (Weyl P2, `app:localgeneral`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:3j-allorder`, subsection
`app:localgeneral` (the general construction), namely `eq:3jmastercommutator`, `eq:3jNsOperator`,
`eq:3jneighbormomentidentity`, `eq:3jJoperator`, `eq:3jB2r`/`eq:3jD2rrecursive`,
`prop:localcalculus` (a) and (c).

The paper's objects are differential operators `𝖠` in `x` acting on the Wigner functions `d_k`.  The
algebra used does not depend on that: everything below is stated for an arbitrary `K`-module `M`
(`K` a field of characteristic zero), endomorphisms `x, H, A ∈ End_K(M)` (`x` multiplication by the
cosine, `H = 𝖧₀` the Wigner operator, `A` the `k`-independent operator), and three vectors
`D₀, D₁, D₂ ∈ M` standing for `d_{k-1}, d_k, d_{k+1}` at one fixed rank `k ∈ K` (so half-integer ranks
and all `k` are covered, and no index bookkeeping occurs).  The hypotheses are exactly the two facts the
paper uses about `d`: the Wigner rank recurrence `ℒ_W d = 0` at `k`, and the eigen-equations
`H d_j = λ_j d_j`, `λ_j = j(j+1)`.

* `master_commutator`: `eq:3jmastercommutator`, `ℒ_W(𝖠d)_k = -(2k+1)λ_k [x,𝖠] d_k`;
* `Ns`, `neighbor_moment_identity`: the operator `𝒩_s[𝖠]` of `eq:3jNsOperator` and the identity
  `eq:3jneighbormomentidentity`, for `π_s` of `lem:momentpolynomial` (`P2MomentPolynomial`);
* `local_calculus_order` (`prop:localcalculus` (a)): if operators `G_r` (`= 𝒢_{2r}`, `G_0 = 1`) satisfy
  `[x, G_r] = B_r` with `B_r` as in `eq:3jB2r`, then the order-`2r` coefficient of the deformed
  recurrence `eq:generalrankrec` vanishes; this is the whole algebraic content of `(a)`;
* `commutator_J` (`eq:3jJoperator`): `[x, 𝒥(𝖡)] = 𝖡` for left-normal operators in any ring with a
  derivation `∂`, `[∂, x] = 1`, so that the hypothesis `[x,G_r] = B_r` is solvable;
* `Ns_apply_one`, `scalar_start_recursion` (`prop:localcalculus` (c), `eq:3jscalarNsone`).

Formalised in the later modules of this family (`P2LocalCalculusSeries`, `P2LocalCalculusLeftNormal`,
`P2LocalCalculusFun`, `P2LocalCalculusWigner`, `P2AnalyticTaylorSeries`, `P2AnalyticAllOrder3j*`): the
identification with functions on `(-1,1)`, part (b) and the one-start uniqueness, and the `3j` instance
(`threeJ_allorder_local`, pointwise, with smooth multipliers); rationality of the multipliers `ψ_{2r}`
(`P2SeedRational`, `P2SeedZeroPsi`) and the `6j` instance in the canonical sector `m ≥ n`
(`P2AnalyticAllOrder6jSeries`, `P2AnalyticAllOrder6j`). Not formalised: the pole statement of the `6j`
coefficients and the `6j` sectors other than `m ≥ n`, the explicit `D̂_2`, `D̂_4` (`thm:3jNNLO`). The abstract
algebra here does not need any of this.
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus

open Polynomial Module

section Calculus

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- `λ_k = k(k+1)`. -/
def lam (k : K) : K := k * (k + 1)

/-- The commutator `[x, A]`. -/
def comm (x A : End K M) : End K M := x * A - A * x

/-- A polynomial in an operator acts on an eigenvector by the polynomial value at the eigenvalue. -/
theorem aeval_apply_of_eigen (H : End K M) {v : M} {c : K} (hv : H v = c • v) (p : K[X]) :
    aeval H p v = p.eval c • v := by
  have hpow : ∀ n : ℕ, (H ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a =>
    simp [hpow, aeval_monomial, smul_smul, mul_comm]

/-- **`eq:3jmastercommutator`.**  The recurrence operator `ℒ_W` at rank `k` applied to `𝖠d`:
if `d_{k-1}, d_k, d_{k+1}` satisfy the Wigner rank recurrence
`kR_{k+1}d_{k+1} + (k+1)R_kd_{k-1} = (2k+1)(λ_kx - τ)d_k`, then for every operator `A`,
`kR_{k+1}Ad_{k+1} + (k+1)R_kAd_{k-1} - (2k+1)(λ_kx-τ)Ad_k = -(2k+1)λ_k[x,A]d_k`. -/
theorem master_commutator (x A : End K M) (k R0 R1 τ : K) (D0 D1 D2 : M)
    (hW : (k * R1) • D2 + ((k + 1) * R0) • D0 = (2 * k + 1) • (lam k • x D1 - τ • D1)) :
    (k * R1) • A D2 + ((k + 1) * R0) • A D0 -
        (2 * k + 1) • (lam k • x (A D1) - τ • A D1) = -((2 * k + 1) * lam k) • comm x A D1 := by
  have h := congrArg A hW
  simp only [map_add, map_smul, map_sub] at h
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, smul_sub]
  linear_combination (norm := module) h

/-- **`eq:3jNsOperator`**: `𝒩_s[𝖠] = x𝖠π_s(𝖧₀) - τ𝖠π̃_s(𝖧₀)
 - ½([x, 𝖠π_s(𝖧₀)] + [x, 𝖠]π_s(𝖧₀))`, for a polynomial `π` (the paper's `π_s`) and `πt` (`π̃_s = π_s/z`). -/
noncomputable def Ns (x H A : End K M) (τ : K) (π πt : K[X]) : End K M :=
  x * A * aeval H π - τ • (A * aeval H πt) -
    (1 / 2 : K) • (comm x (A * aeval H π) + comm x A * aeval H π)

/-- **`eq:3jneighbormomentidentity`**, for an arbitrary polynomial `π` with the two neighboring-moment
relations `π(λ_k) + π(λ_{k+1}) = 2(k+1)^{2s}`, `π(λ_{k-1}) + π(λ_k) = 2k^{2s}` (the value of
`lem:momentpolynomial`, see `neighbor_moment_identity`) and `π = z π̃`:
`kR_{k+1}(k+1)^{2s}Ad_{k+1} + (k+1)R_kk^{2s}Ad_{k-1} = (2k+1)λ_k 𝒩_s[𝖠]d_k`. -/
theorem neighbor_moment_identity_of (x H A : End K M) (s : ℕ) (k R0 R1 τ : K) (D0 D1 D2 : M)
    (π πt : K[X])
    (hW : (k * R1) • D2 + ((k + 1) * R0) • D0 = (2 * k + 1) • (lam k • x D1 - τ • D1))
    (h0 : H D0 = lam (k - 1) • D0) (h1 : H D1 = lam k • D1) (h2 : H D2 = lam (k + 1) • D2)
    (hπ : π = X * πt)
    (hm1 : π.eval (lam k) + π.eval (lam (k + 1)) = 2 * (k + 1) ^ (2 * s))
    (hm0 : π.eval (lam (k - 1)) + π.eval (lam k) = 2 * k ^ (2 * s)) [CharZero K] :
    (k * R1 * (k + 1) ^ (2 * s)) • A D2 + ((k + 1) * R0 * k ^ (2 * s)) • A D0 =
      ((2 * k + 1) * lam k) • Ns x H A τ π πt D1 := by
  have two : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨Pi, hPi⟩ : ∃ Pi, Pi = aeval H π := ⟨_, rfl⟩
  have E1 := master_commutator x A k R0 R1 τ D0 D1 D2 hW
  have E2 := master_commutator x (A * Pi) k R0 R1 τ D0 D1 D2 hW
  have p0 : Pi D0 = π.eval (lam (k - 1)) • D0 := hPi ▸ aeval_apply_of_eigen H h0 π
  have p1 : Pi D1 = π.eval (lam k) • D1 := hPi ▸ aeval_apply_of_eigen H h1 π
  have p2 : Pi D2 = π.eval (lam (k + 1)) • D2 := hPi ▸ aeval_apply_of_eigen H h2 π
  have pt1 : aeval H πt D1 = πt.eval (lam k) • D1 := aeval_apply_of_eigen H h1 πt
  have hlam : lam k * πt.eval (lam k) = π.eval (lam k) := by rw [hπ]; simp
  have key : (lam k * πt.eval (lam k)) • A D1 = π.eval (lam k) • A D1 := by rw [hlam]
  have e1 : (k + 1) ^ (2 * s) = (π.eval (lam k) + π.eval (lam (k + 1))) / 2 := by
    linear_combination (-1 / 2 : K) * hm1
  have e2 : k ^ (2 * s) = (π.eval (lam (k - 1)) + π.eval (lam k)) / 2 := by
    linear_combination (-1 / 2 : K) * hm0
  simp only [Module.End.mul_apply, map_smul, p0, p2, p1] at E2
  simp only [Ns, comm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_smul, ← hPi, p1, pt1, smul_sub, smul_add]
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, smul_sub] at E1 E2
  simp only [p1, map_smul] at E2
  rw [e1, e2]
  linear_combination (norm := module) (π.eval (lam k) / 2) • E1 + (1 / 2 : K) • E2 +
    ((2 * k + 1) * τ) • key

/-- `π̃_s = π_s / z` (`π_s(0) = 0`, `lem:momentpolynomial`). -/
noncomputable def momentPolyTilde (K : Type*) [Field K] [CharZero K] (s : ℕ) : K[X] :=
  momentPoly K s /ₘ X

theorem momentPoly_eq_X_mul_tilde [CharZero K] {s : ℕ} (hs : 1 ≤ s) :
    momentPoly K s = X * momentPolyTilde K s := by
  have h := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := momentPoly K s) (a := (0 : K))).mpr
    (by simpa [IsRoot] using momentPoly_eval_zero hs)
  simpa [momentPolyTilde] using h.symm

theorem momentPoly_spec_lam [CharZero K] (s : ℕ) (k : K) :
    (momentPoly K s).eval (lam k) + (momentPoly K s).eval (lam (k + 1)) = 2 * (k + 1) ^ (2 * s) := by
  have e : lam (k + 1) = (k + 1) * (k + 2) := by unfold lam; ring
  rw [e]; exact momentPoly_spec s k

theorem momentPoly_spec_pred_lam [CharZero K] (s : ℕ) (k : K) :
    (momentPoly K s).eval (lam (k - 1)) + (momentPoly K s).eval (lam k) = 2 * k ^ (2 * s) := by
  have e : lam (k - 1) = (k - 1) * k := by unfold lam; ring
  rw [e]; exact momentPoly_spec_pred s k

/-- **`eq:3jneighbormomentidentity`** (the neighboring-moment identity of `app:localgeneral`) for the
moment polynomial `π_s` of `lem:momentpolynomial`, `s ≥ 1`:
`kR_{k+1}(k+1)^{2s}Ad_{k+1} + (k+1)R_kk^{2s}Ad_{k-1} = (2k+1)λ_k 𝒩_s[𝖠]d_k`, from the Wigner
recurrence at `k` and the eigen-equations `Hd_j = λ_jd_j` (`j = k-1,k,k+1`). -/
theorem neighbor_moment_identity [CharZero K] (x H A : End K M) {s : ℕ} (hs : 1 ≤ s)
    (k R0 R1 τ : K) (D0 D1 D2 : M)
    (hW : (k * R1) • D2 + ((k + 1) * R0) • D0 = (2 * k + 1) • (lam k • x D1 - τ • D1))
    (h0 : H D0 = lam (k - 1) • D0) (h1 : H D1 = lam k • D1) (h2 : H D2 = lam (k + 1) • D2) :
    (k * R1 * (k + 1) ^ (2 * s)) • A D2 + ((k + 1) * R0 * k ^ (2 * s)) • A D0 =
      ((2 * k + 1) * lam k) • Ns x H A τ (momentPoly K s) (momentPolyTilde K s) D1 :=
  neighbor_moment_identity_of x H A s k R0 R1 τ D0 D1 D2 _ _ hW h0 h1 h2
    (momentPoly_eq_X_mul_tilde hs) (momentPoly_spec_lam s k) (momentPoly_spec_pred_lam s k)

/-- **`prop:localcalculus` (a)**, order by order (`eq:generalrankrec`, `eq:3jB2r`,
`eq:3jD2rrecursive`).  Let `G r = 𝒢_{2r}` (`G 0 = 1`) be operators with
`[x, G (r+1)] = G r q(H) + ∑_{s ≤ r} e_{s+1} 𝒩_{s+1}[G (r-s)]`, which is `[x,𝒢_{2r+2}] = 𝖡_{2r+2}` of
`eq:3jB2r` (`e_0 = 1`); then the coefficient of order `2(r+1)` of the formal series solution
`Φ = ∑ 𝒢_{2r} d` inserted into the deformed rank recurrence
`(2k+1)[λ_k(x - q(λ_k)) - τ]Φ_k = kR_{k+1}η(k+1)Φ_{k+1} + (k+1)R_kη(k)Φ_{k-1}`,
`η(k) = ∑ e_s k^{2s}`, vanishes.  (For order `0` this is the Wigner recurrence itself.)  The solvability of
`[x,G] = 𝖡` is `commutator_J`. -/
theorem local_calculus_order [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1)
    (G : ℕ → End K M) (k R0 R1 τ : K) (D0 D1 D2 : M)
    (hW : (k * R1) • D2 + ((k + 1) * R0) • D0 = (2 * k + 1) • (lam k • x D1 - τ • D1))
    (h0 : H D0 = lam (k - 1) • D0) (h1 : H D1 = lam k • D1) (h2 : H D2 = lam (k + 1) • D2) (r : ℕ)
    (hB : comm x (G (r + 1)) = G r * aeval H q +
      ∑ s ∈ Finset.range (r + 1), e (s + 1) • Ns x H (G (r - s)) τ (momentPoly K (s + 1))
        (momentPolyTilde K (s + 1))) :
    (2 * k + 1) • (lam k • x (G (r + 1) D1) - τ • G (r + 1) D1) -
        ((2 * k + 1) * lam k * q.eval (lam k)) • G r D1 -
      ∑ s ∈ Finset.range (r + 2), e s • ((k * R1 * (k + 1) ^ (2 * s)) • G (r + 1 - s) D2 +
        ((k + 1) * R0 * k ^ (2 * s)) • G (r + 1 - s) D0) = 0 := by
  have hnb : ∀ s ∈ Finset.range (r + 1),
      e (s + 1) • ((k * R1 * (k + 1) ^ (2 * (s + 1))) • G (r - s) D2 +
        ((k + 1) * R0 * k ^ (2 * (s + 1))) • G (r - s) D0) =
      ((2 * k + 1) * lam k) • (e (s + 1) • Ns x H (G (r - s)) τ (momentPoly K (s + 1))
        (momentPolyTilde K (s + 1))) D1 := by
    intro s _
    rw [neighbor_moment_identity x H (G (r - s)) (Nat.succ_le_succ (Nat.zero_le s)) k R0 R1 τ D0 D1
      D2 hW h0 h1 h2]
    simp only [LinearMap.smul_apply, smul_comm (e (s + 1))]
  have hsum : ∑ s ∈ Finset.range (r + 2), e s • ((k * R1 * (k + 1) ^ (2 * s)) • G (r + 1 - s) D2 +
        ((k + 1) * R0 * k ^ (2 * s)) • G (r + 1 - s) D0) =
      e 0 • ((k * R1) • G (r + 1) D2 + ((k + 1) * R0) • G (r + 1) D0) +
        ((2 * k + 1) * lam k) • (∑ s ∈ Finset.range (r + 1), e (s + 1) •
          Ns x H (G (r - s)) τ (momentPoly K (s + 1)) (momentPolyTilde K (s + 1))) D1 := by
    rw [Finset.sum_range_succ', LinearMap.sum_apply, Finset.smul_sum]
    simp only [Nat.add_sub_add_right, mul_zero, pow_zero, mul_one, Nat.sub_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← hnb s hs]
  have hM := master_commutator x (G (r + 1)) k R0 R1 τ D0 D1 D2 hW
  have hq : (G r * aeval H q) D1 = q.eval (lam k) • G r D1 := by
    rw [Module.End.mul_apply, aeval_apply_of_eigen H h1 q, map_smul]
  rw [hB, LinearMap.add_apply, hq] at hM
  rw [hsum, he0, one_smul]
  linear_combination (norm := module) (-1 : K) • hM

/-- **`eq:3jscalarNsone`** (`prop:localcalculus` (c)): at `a = b = 0` (`τ = 0`), if `H d₀ = 0`,
`H(x d₀) = 2 x d₀` (`d_0 = 1`, `d_1 = x`) and `π(0) = 0`, `π(2) = 2`, then `𝒩_s[𝖠] d₀ = 𝖠 x d₀`. -/
theorem Ns_apply_one [CharZero K] (x H A : End K M) (π πt : K[X]) (d0 : M) (hd0 : H d0 = 0)
    (hd1 : H (x d0) = (2 : K) • x d0) (hπ0 : π.eval 0 = 0) (hπ2 : π.eval 2 = 2) :
    Ns x H A 0 π πt d0 = A (x d0) := by
  have p0 : aeval H π d0 = 0 := by
    have := aeval_apply_of_eigen H (v := d0) (c := (0 : K)) (by simp [hd0]) π
    rw [this, hπ0, zero_smul]
  have p1 : aeval H π (x d0) = (2 : K) • x d0 := by
    rw [aeval_apply_of_eigen H hd1 π, hπ2]
  simp only [Ns, comm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_smul, zero_smul, p0, p1, map_zero, sub_zero, zero_sub,
    smul_neg, add_zero]
  module

/-- `eq:3jscalarNsone` for the moment polynomial (`π_s(0) = 0`, `π_s(2) = 2` from
`eq:3jpimoment` at `k = 0`). -/
theorem Ns_apply_one_momentPoly [CharZero K] (x H A : End K M) {s : ℕ} (hs : 1 ≤ s) (d0 : M)
    (hd0 : H d0 = 0) (hd1 : H (x d0) = (2 : K) • x d0) :
    Ns x H A 0 (momentPoly K s) (momentPolyTilde K s) d0 = A (x d0) := by
  refine Ns_apply_one x H A _ _ d0 hd0 hd1 (momentPoly_eval_zero hs) ?_
  have := momentPoly_spec (K := K) s 0
  norm_num [momentPoly_eval_zero hs] at this
  exact this

/-- **`prop:localcalculus` (c)**, the order recursion of the second start.  For `a = b = 0`
(`d_0 = 1`, `d_1 = x d_0`; `H d₀ = 0`, `H(x d₀) = 2x d₀`), if `𝒢_{2r} d₀ = 0` for `r ≥ 1`, then
`a_r := G_r(x d₀)` satisfies `a_{r+1} = -q(0)G_r d₀ - ∑_{s ≤ r} e_{s+1} a_{r-s}`; with `G_0 d₀ = d₀` this
is the paper's `a_r = -q(0)δ_{r1} - ∑_{s=1}^r e_sa_{r-s}` (the identity of the sums
`η(1)∑a_r = x - q(0)` is its formal-series resummation, not formalised). -/
theorem scalar_start_recursion [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K)
    (G : ℕ → End K M) (d0 : M) (hd0 : H d0 = 0) (hd1 : H (x d0) = (2 : K) • x d0)
    (hG : ∀ r, G (r + 1) d0 = 0) (r : ℕ)
    (hB : comm x (G (r + 1)) = G r * aeval H q +
      ∑ s ∈ Finset.range (r + 1), e (s + 1) • Ns x H (G (r - s)) 0 (momentPoly K (s + 1))
        (momentPolyTilde K (s + 1))) :
    G (r + 1) (x d0) = -(q.eval 0 • G r d0) - ∑ s ∈ Finset.range (r + 1), e (s + 1) • G (r - s) (x d0) := by
  have h := congrArg (fun T => T d0) hB
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, hG, map_zero, zero_sub] at h
  rw [aeval_apply_of_eigen H (v := d0) (c := (0 : K)) (by simp [hd0]) q, map_smul] at h
  have hs : ∀ s ∈ Finset.range (r + 1), e (s + 1) • (Ns x H (G (r - s)) 0 (momentPoly K (s + 1))
        (momentPolyTilde K (s + 1))) d0 = e (s + 1) • G (r - s) (x d0) := by
    intro s _
    rw [Ns_apply_one_momentPoly x H _ (Nat.succ_le_succ (Nat.zero_le s)) d0 hd0 hd1]
  rw [Finset.sum_congr rfl hs] at h
  linear_combination (norm := module) (-1 : K) • h

/-- `∂^{n+1} x = x ∂^{n+1} + (n+1) ∂^n` when `∂x - x∂ = 1`, so `[x, ∂^{n+1}] = -(n+1)∂^n`. -/
theorem derivPow_mul_x (x D : End K M) (hD : D * x - x * D = 1) (n : ℕ) :
    D ^ (n + 1) * x = x * D ^ (n + 1) + ((n : K) + 1) • D ^ n := by
  have hD' : D * x = x * D + 1 := by rw [← hD]; abel
  induction n with
  | zero => simpa using hD'
  | succ n ih =>
    calc D ^ (n + 1 + 1) * x = D * (D ^ (n + 1) * x) := by rw [pow_succ', mul_assoc]
      _ = D * (x * D ^ (n + 1) + ((n : K) + 1) • D ^ n) := by rw [ih]
      _ = (D * x) * D ^ (n + 1) + ((n : K) + 1) • D ^ (n + 1) := by
        rw [mul_add, ← mul_assoc, mul_smul_comm, ← pow_succ']
      _ = x * D ^ (n + 1 + 1) + (((n + 1 : ℕ) : K) + 1) • D ^ (n + 1) := by
        rw [hD', add_mul, one_mul, mul_assoc, ← pow_succ']
        push_cast
        module

/-- **`eq:3jJoperator`**: for a left-normal operator `𝖡 = ∑_{j ≤ J} b_j ∂^j` with coefficients
commuting with `x`, `𝒥(𝖡) = -∑ b_j/(j+1) ∂^{j+1}`. -/
noncomputable def Jop (D : End K M) (b : ℕ → End K M) (J : ℕ) : End K M :=
  -∑ j ∈ Finset.range (J + 1), (1 / ((j : K) + 1)) • (b j * D ^ (j + 1))

/-- The left-normal operator `∑_{j ≤ J} b_j ∂^j`. -/
def leftNormal (D : End K M) (b : ℕ → End K M) (J : ℕ) : End K M :=
  ∑ j ∈ Finset.range (J + 1), b j * D ^ j

/-- **`eq:3jJoperator`**: `[x, 𝒥(𝖡)] = 𝖡`, in any ring of operators with `[∂, x] = 1` and
coefficients commuting with `x` (the multiplication operators). -/
theorem commutator_J [CharZero K] (x D : End K M) (hD : D * x - x * D = 1) (b : ℕ → End K M)
    (hb : ∀ j, x * b j = b j * x) (J : ℕ) :
    comm x (Jop D b J) = leftNormal D b J := by
  have hterm : ∀ j : ℕ, comm x ((1 / ((j : K) + 1)) • (b j * D ^ (j + 1))) = -(b j * D ^ j) := by
    intro j
    have hj : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have h := derivPow_mul_x x D hD j
    have e1 : x * (b j * D ^ (j + 1)) = b j * (x * D ^ (j + 1)) := by rw [← mul_assoc, hb j, mul_assoc]
    have e2 : b j * D ^ (j + 1) * x = b j * (x * D ^ (j + 1)) + ((j : K) + 1) • (b j * D ^ j) := by
      rw [mul_assoc, h, mul_add, mul_smul_comm]
    unfold comm
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e1, e2]
    simp [smul_smul, hj]
  have hsum : comm x (∑ j ∈ Finset.range (J + 1), (1 / ((j : K) + 1)) • (b j * D ^ (j + 1))) =
      ∑ j ∈ Finset.range (J + 1), comm x ((1 / ((j : K) + 1)) • (b j * D ^ (j + 1))) := by
    simp only [comm, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  have hneg : ∀ T : End K M, comm x (-T) = -comm x T := by
    intro T; simp [comm, mul_neg, neg_mul]; abel
  unfold Jop leftNormal
  rw [hneg, hsum, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib, neg_neg]

end Calculus

end FormalResearch.Racah.LocalCalculus

/-- info: 'FormalResearch.Racah.LocalCalculus.master_commutator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.master_commutator

/-- info: 'FormalResearch.Racah.LocalCalculus.neighbor_moment_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.neighbor_moment_identity

/-- info: 'FormalResearch.Racah.LocalCalculus.local_calculus_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.local_calculus_order

/-- info: 'FormalResearch.Racah.LocalCalculus.commutator_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.commutator_J

/-- info: 'FormalResearch.Racah.LocalCalculus.Ns_apply_one_momentPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Ns_apply_one_momentPoly

/-- info: 'FormalResearch.Racah.LocalCalculus.scalar_start_recursion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.scalar_start_recursion

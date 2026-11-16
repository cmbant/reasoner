module

public import Mathlib
public import FormalResearch.Racah.P2LocalCalculus

/-!
# Local calculus, all orders as formal series (Weyl P2, `prop:localcalculus`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:localgeneral`,
`eq:generalrankrec`, `eq:3jeseries`, `prop:localcalculus` (a), (b) (its forward-uniqueness half) and (c).

`P2LocalCalculus` proves the algebra order by order (`local_calculus_order`).  Here the orders are
assembled into the statements about the formal series `Φ_k = ∑_r t^r 𝒢_r d_k` of the paper.  A formal
series with coefficients in a `K`-module `M` is a function `ℕ → M` (the coefficient of `t^r`); a scalar
formal series is a `PowerSeries K` acting by convolution (`smulS`), and `η(k) = ∑_s e_s k^{2s} t^s`
is `eta e k` (the order of `e_s` is carried by the power of `t`).  Everything is abstract: `M` is any
`K`-module, `x, H` and the `𝒢_r` are endomorphisms (as in `P2LocalCalculus`).

* `local_calculus_series` (**`prop:localcalculus` (a)**, all orders): if `𝒢_0 = 1` and
  `[x, 𝒢_{r+1}] = 𝖡_{r+1}` for every `r` (`eq:3jB2r`), then the formal series
  `Φ_j = ∑_r t^r 𝒢_r d_j` satisfies the deformed rank recurrence `eq:generalrankrec` at rank `k`
  as an identity of formal series (the `t^r` coefficient is `local_calculus_order`);
* `rank_unique_of_start`, `rank_unique_of_two_starts`: forward uniqueness of the formal rank recurrence
  (the sentence "the one-sided recurrence determines `Φ_k` for `k > k₀` from `Φ_{k₀}`" in the proof of
  `prop:localcalculus` (b), and the two-start version used in (c));
* `scalar_start_series` (**`prop:localcalculus` (c)**): the formal-series resummation
  `η(1) ∑_r 𝒢_r(x d₀) = x d₀ - t q(0) d₀`, i.e. `Φ_1 = (x - t q(0)) Φ_0 / η(1)`.

Not formalised here: the identification of the abstract data with Wigner functions (see
`P2LocalCalculusLeftNormal`, `P2LocalCalculusWigner`), and any analytic convergence of the series (the
paper's statement is a formal one).
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus

open Polynomial Module

section Series

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- Multiplication of a formal series `v = ∑ v_r t^r` with coefficients in `M` by a scalar formal power
series `c`. -/
noncomputable def smulS (c : PowerSeries K) (v : ℕ → M) : ℕ → M := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 c • v p.2

/-- Multiplication by `t`. -/
def shiftS (v : ℕ → M) : ℕ → M
  | 0 => 0
  | r + 1 => v r

/-- `η(k) = ∑_s e_s k^{2s} t^s` (`eq:3jeseries`; the pure order `2s` of `e_s` is the power `t^s`). -/
noncomputable def eta (e : ℕ → K) (k : K) : PowerSeries K :=
  PowerSeries.mk fun s => e s * k ^ (2 * s)

lemma coeff_eta (e : ℕ → K) (k : K) (s : ℕ) :
    PowerSeries.coeff s (eta e k) = e s * k ^ (2 * s) := by
  simp [eta, PowerSeries.coeff_mk]

lemma smulS_sub (c : PowerSeries K) (v w : ℕ → M) : smulS c (v - w) = smulS c v - smulS c w := by
  funext n
  simp [smulS, smul_sub, Finset.sum_sub_distrib]

lemma smulS_zero (c : PowerSeries K) : smulS c (0 : ℕ → M) = 0 := by
  funext n; simp [smulS]

lemma shiftS_zero : shiftS (0 : ℕ → M) = 0 := by
  funext n; cases n <;> simp [shiftS]

/-- Multiplication by a scalar series with nonzero constant term is injective. -/
theorem smulS_cancel (c : PowerSeries K) (hc : PowerSeries.constantCoeff c ≠ 0) {v w : ℕ → M}
    (h : smulS c v = smulS c w) : v = w := by
  have h0 : smulS c (v - w) = 0 := by rw [smulS_sub, h, sub_self]
  suffices hz : v - w = 0 from sub_eq_zero.mp hz
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congrFun h0 n
    simp only [smulS, Pi.zero_apply] at hn
    rw [Finset.sum_eq_single (0, n)] at hn
    · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hn
      have := (smul_eq_zero.mp hn).resolve_left hc
      simpa using this
    · intro p hp hne
      have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hlt : p.2 < n := by
        rcases p with ⟨a, b⟩
        have : a ≠ 0 := fun h => hne (by simp [h] at hp' ⊢; omega)
        simp only at hp' this ⊢; omega
      have := ih p.2 hlt
      simp only [Pi.zero_apply] at this
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h

lemma constantCoeff_eta (e : ℕ → K) (he0 : e 0 = 1) (k : K) :
    PowerSeries.constantCoeff (eta e k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_eta]; simp [he0]

/-- The formal series `Φ_v = ∑_r t^r 𝒢_r v` of an operator family `G` applied to `v`. -/
def serG (G : ℕ → End K M) (v : M) : ℕ → M := fun r => G r v

/-- `𝖡_{r+1}` of `eq:3jB2r` for the operator sequence `g` (`g r = 𝒢_r`, `g 0 = 1`), the right side of
`[x, 𝒢_{r+1}] = 𝖡_{r+1}` (the paper's `𝖡_{2r+2} = 𝒢_{2r} q(𝖧₀) + ∑_{s ≤ r} e_{s+1} 𝒩_{s+1}[𝒢_{2(r-s)}]`). -/
noncomputable def Bop [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K)
    (g : ℕ → End K M) (r : ℕ) : End K M :=
  g r * aeval H q + ∑ s ∈ Finset.range (r + 1), e (s + 1) • Ns x H (g (r - s)) τ
    (momentPoly K (s + 1)) (momentPolyTilde K (s + 1))

lemma Bop_congr [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (τ : K) {g g' : ℕ → End K M}
    {r : ℕ} (h : ∀ n ≤ r, g n = g' n) : Bop x H q e τ g r = Bop x H q e τ g' r := by
  unfold Bop
  rw [h r le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h (r - s) (Nat.sub_le _ _)]

/-- Left minus right side of the deformed rank recurrence `eq:generalrankrec` at rank `k`,
`(2k+1)[λ_k(x - t q(λ_k)) - τ]Φ_k - kR_{k+1}η(k+1)Φ_{k+1} - (k+1)R_kη(k)Φ_{k-1}`, for formal series
`P0 = Φ_{k-1}`, `P1 = Φ_k`, `P2 = Φ_{k+1}` (`R0 = R_k`, `R1 = R_{k+1}`). -/
noncomputable def defectS (x : End K M) (q : K[X]) (e : ℕ → K) (k R0 R1 τ : K)
    (P0 P1 P2 : ℕ → M) : ℕ → M := fun r =>
  (2 * k + 1) • (lam k • x (P1 r) - (lam k * q.eval (lam k)) • shiftS P1 r - τ • P1 r) -
    (k * R1) • smulS (eta e (k + 1)) P2 r - ((k + 1) * R0) • smulS (eta e k) P0 r

/-- **`prop:localcalculus` (a), all orders** (`eq:generalrankrec`, `eq:3jB2r`, `eq:3jD2rrecursive`).
Let `𝒢_0 = 1` and `[x, 𝒢_{r+1}] = 𝒢_r q(𝖧₀) + ∑_{s ≤ r} e_{s+1} 𝒩_{s+1}[𝒢_{r-s}]` for every `r`
(the paper's `[x, 𝒢_{2r}] = 𝖡_{2r}`, for any multipliers `ψ`).  If `d_{k-1}, d_k, d_{k+1}` satisfy the
Wigner rank recurrence and `𝖧₀d_j = λ_jd_j`, then the formal series `Φ_j = ∑_r t^r 𝒢_r d_j`
satisfy the deformed rank recurrence at rank `k` exactly, as an identity of formal power series. -/
theorem local_calculus_series [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1)
    (G : ℕ → End K M) (hG0 : G 0 = 1) (k R0 R1 τ : K) (D0 D1 D2 : M)
    (hW : (k * R1) • D2 + ((k + 1) * R0) • D0 = (2 * k + 1) • (lam k • x D1 - τ • D1))
    (h0 : H D0 = lam (k - 1) • D0) (h1 : H D1 = lam k • D1) (h2 : H D2 = lam (k + 1) • D2)
    (hB : ∀ r, comm x (G (r + 1)) = Bop x H q e τ G r) :
    defectS x q e k R0 R1 τ (serG G D0) (serG G D1) (serG G D2) = 0 := by
  funext r
  have e0 : ∀ y : K, PowerSeries.coeff 0 (eta e y) = 1 := fun y => by rw [coeff_eta]; simp [he0]
  cases r with
  | zero =>
    simp only [defectS, serG, smulS, shiftS, hG0, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
      e0, one_smul, Module.End.one_apply, smul_zero, sub_zero, Pi.zero_apply]
    linear_combination (norm := module) (-1 : K) • hW
  | succ r =>
    have key := local_calculus_order x H q e he0 G k R0 R1 τ D0 D1 D2 hW h0 h1 h2 r (hB r)
    simp only [defectS, serG, smulS, shiftS, Pi.zero_apply,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_eta]
    simp only [Nat.succ_eq_add_one]
    have e1 : (k * R1) • ∑ s ∈ Finset.range (r + 1 + 1), (e s * (k + 1) ^ (2 * s)) • G (r + 1 - s) D2 =
        ∑ s ∈ Finset.range (r + 1 + 1), e s • ((k * R1 * (k + 1) ^ (2 * s)) • G (r + 1 - s) D2) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_smul, smul_smul]; congr 1; ring
    have e2 : ((k + 1) * R0) • ∑ s ∈ Finset.range (r + 1 + 1), (e s * k ^ (2 * s)) • G (r + 1 - s) D0 =
        ∑ s ∈ Finset.range (r + 1 + 1), e s • (((k + 1) * R0 * k ^ (2 * s)) • G (r + 1 - s) D0) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e1, e2]
    simp only [smul_add, Finset.sum_add_distrib] at key
    linear_combination (norm := module) key


/-- `Φ_{n-1}` for the rank index `n` (`Φ_{-1} = 0`). -/
def prevS (Φ : ℕ → ℕ → M) : ℕ → ℕ → M
  | 0 => 0
  | n + 1 => Φ n

/-- Rank-`n` defect of a family of formal series `Φ n` (rank `k₀ + n`, `R n = R_{k₀+n}`, `Φ_{-1} = 0`):
`rankDefect … n = defectS … (Φ_{n-1}) (Φ_n) (Φ_{n+1})` at rank `k₀ + n`. -/
noncomputable def rankDefect (x : End K M) (q : K[X]) (e : ℕ → K) (τ k0 : K) (R : ℕ → K)
    (Φ : ℕ → ℕ → M) (n : ℕ) : ℕ → M :=
  defectS x q e (k0 + n) (R n) (R (n + 1)) τ (prevS Φ n) (Φ n) (Φ (n + 1))

/-- One forward step of uniqueness: two solutions of the rank recurrence at rank `k₀+n` with the same
`Φ_n`, the same backward contribution and `(k₀+n) R_{n+1} ≠ 0` have the same `Φ_{n+1}`. -/
theorem step_unique (x : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1) (τ k0 : K) (R : ℕ → K)
    (n : ℕ) (hfwd : (k0 + n) * R (n + 1) ≠ 0) {Φ Φ' : ℕ → ℕ → M}
    (h : rankDefect x q e τ k0 R Φ n = 0) (h' : rankDefect x q e τ k0 R Φ' n = 0)
    (hn : Φ n = Φ' n)
    (hp : ((k0 + n + 1) * R n) • smulS (eta e (k0 + n)) (prevS Φ n) =
      ((k0 + n + 1) * R n) • smulS (eta e (k0 + n)) (prevS Φ' n)) :
    Φ (n + 1) = Φ' (n + 1) := by
  have key : smulS (eta e (k0 + n + 1)) (Φ (n + 1)) = smulS (eta e (k0 + n + 1)) (Φ' (n + 1)) := by
    funext r
    have h1 := congrFun h r
    have h2 := congrFun h' r
    have h3 := congrFun hp r
    simp only [rankDefect, defectS, Pi.zero_apply, Pi.smul_apply, hn] at h1 h2 h3
    have h4 : ((k0 + n) * R (n + 1)) • smulS (eta e (k0 + n + 1)) (Φ (n + 1)) r =
        ((k0 + n) * R (n + 1)) • smulS (eta e (k0 + n + 1)) (Φ' (n + 1)) r := by
      linear_combination (norm := module) h2 - h1 - h3
    exact smul_right_injective M hfwd h4
  exact smulS_cancel _ (by rw [constantCoeff_eta e he0]; exact one_ne_zero) key

/-- Linear maps commute with the formal-series operations. -/
theorem rankDefect_map {N : Type*} [AddCommGroup N] [Module K N] (ℓ : M →ₗ[K] N) (x : End K M)
    (x' : End K N) (hx : ∀ v, ℓ (x v) = x' (ℓ v)) (q : K[X]) (e : ℕ → K) (τ k0 : K) (R : ℕ → K)
    (Φ : ℕ → ℕ → M) (n r : ℕ) :
    ℓ (rankDefect x q e τ k0 R Φ n r) =
      rankDefect x' q e τ k0 R (fun m s => ℓ (Φ m s)) n r := by
  have hs : ∀ (c : PowerSeries K) (v : ℕ → M) (m : ℕ), ℓ (smulS c v m) = smulS c (fun s => ℓ (v s)) m := by
    intro c v m; simp [smulS, map_sum]
  have hsh : ∀ (v : ℕ → M) (m : ℕ), ℓ (shiftS v m) = shiftS (fun s => ℓ (v s)) m := by
    intro v m; cases m <;> simp [shiftS]
  have hp : ∀ m s, ℓ (prevS Φ m s) = prevS (fun m s => ℓ (Φ m s)) m s := by
    intro m s; cases m <;> simp [prevS]
  unfold rankDefect defectS
  simp only [map_sub, map_smul, hx, hsh, hs]
  have : (fun s => ℓ (prevS Φ n s)) = prevS (fun m s => ℓ (Φ m s)) n := funext (hp n)
  rw [this]

/-- **Forward uniqueness, one start** (`prop:localcalculus` (b)): if `R_{k₀} = 0` (the recurrence is
one-sided at the minimal rank) and all forward coefficients `(k₀+n)R_{n+1}` are nonzero, then a family of
formal solutions of the rank recurrence is determined by `Φ_0`. -/
theorem rank_unique_of_start (x : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1) (τ k0 : K)
    (R : ℕ → K) (hR0 : R 0 = 0) (hfwd : ∀ n : ℕ, (k0 + n) * R (n + 1) ≠ 0) {Φ Φ' : ℕ → ℕ → M}
    (h : ∀ n, rankDefect x q e τ k0 R Φ n = 0) (h' : ∀ n, rankDefect x q e τ k0 R Φ' n = 0)
    (h0 : Φ 0 = Φ' 0) : Φ = Φ' := by
  have main : ∀ n, Φ n = Φ' n ∧ Φ (n + 1) = Φ' (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨h0, step_unique x q e he0 τ k0 R 0 (by simpa using hfwd 0) (h 0) (h' 0) h0 ?_⟩
      rw [hR0]; simp
    | succ n ih =>
      refine ⟨ih.2, step_unique x q e he0 τ k0 R (n + 1) (hfwd (n + 1)) (h (n + 1)) (h' (n + 1)) ih.2 ?_⟩
      simp only [prevS, ih.1]
  funext n
  exact (main n).1

/-- **Forward uniqueness, two starts** (the scalar start `a = b = 0`, `prop:localcalculus` (c)): a family of
formal solutions of the rank recurrence at ranks `n ≥ 1` with nonzero forward coefficients is determined by
`Φ_0` and `Φ_1`. -/
theorem rank_unique_of_two_starts (x : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1) (τ k0 : K)
    (R : ℕ → K) (hfwd : ∀ n : ℕ, (k0 + ((n + 1 : ℕ) : K)) * R (n + 2) ≠ 0) {Φ Φ' : ℕ → ℕ → M}
    (h : ∀ n, rankDefect x q e τ k0 R Φ (n + 1) = 0) (h' : ∀ n, rankDefect x q e τ k0 R Φ' (n + 1) = 0)
    (h0 : Φ 0 = Φ' 0) (h1 : Φ 1 = Φ' 1) : Φ = Φ' := by
  have main : ∀ n, Φ n = Φ' n ∧ Φ (n + 1) = Φ' (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, step_unique x q e he0 τ k0 R (n + 1) (hfwd n) (h n) (h' n) ih.2 ?_⟩
      simp only [prevS, ih.1]
  funext n
  exact (main n).1

/-- **`prop:localcalculus` (c)**, resummed (`eq:3jscalarNsone`).  For `a = b = 0` (`τ = 0`, `d_0 = 1`,
`d_1 = x d_0`: `H d₀ = 0`, `H(x d₀) = 2 x d₀`) and `𝒢_r d₀ = 0` for `r ≥ 1`, the formal series
`Φ_1 = ∑_r t^r 𝒢_r (x d₀)` satisfies `η(1) Φ_1 = (x - t q(0)) d₀`: this is the paper's
`η(1) ∑_r a_r = x - q(0)` with the order of `q(0)` carried by `t`. -/
theorem scalar_start_series [CharZero K] (x H : End K M) (q : K[X]) (e : ℕ → K) (he0 : e 0 = 1)
    (G : ℕ → End K M) (hG0 : G 0 = 1) (d0 : M) (hd0 : H d0 = 0)
    (hd1 : H (x d0) = (2 : K) • x d0) (hG : ∀ r, G (r + 1) d0 = 0)
    (hB : ∀ r, comm x (G (r + 1)) = Bop x H q e 0 G r) :
    smulS (eta e 1) (serG G (x d0)) = fun r => if r = 0 then x d0 else if r = 1 then
      -(q.eval 0 • d0) else 0 := by
  funext n
  cases n with
  | zero =>
    simp [smulS, serG, coeff_eta, he0, hG0]
  | succ r =>
    have h := scalar_start_recursion x H q e G d0 hd0 hd1 hG r (hB r)
    simp only [smulS, serG, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_eta, one_pow,
      mul_one]
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.add_sub_add_right, he0, one_smul]
    have key : G (r + 1) (x d0) + ∑ s ∈ Finset.range (r + 1), e (s + 1) • G (r - s) (x d0) =
        -(q.eval 0 • G r d0) := by rw [h]; abel
    rw [add_comm, key]
    cases r with
    | zero => simp [hG0]
    | succ r => simp [hG r]

end Series

end FormalResearch.Racah.LocalCalculus

/-- info: 'FormalResearch.Racah.LocalCalculus.local_calculus_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.local_calculus_series

/-- info: 'FormalResearch.Racah.LocalCalculus.rank_unique_of_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.rank_unique_of_start

/-- info: 'FormalResearch.Racah.LocalCalculus.rank_unique_of_two_starts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.rank_unique_of_two_starts

/-- info: 'FormalResearch.Racah.LocalCalculus.scalar_start_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.scalar_start_series

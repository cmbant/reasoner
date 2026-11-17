module

public import FormalResearch.Special.DiscreteAiryLimitChainsHahnAiry

/-!
# Lattice nodes of the Wigner `3j` chain: existence for every rational `x`, and the exact parity obstruction

The theorem `hahn_chain_airy` (Weyl P3, `thm:hahnAiryConnection`, integer case) is stated for the nodes `x_n = x` of the
`3j` lattice `xLat M σ N n = -1 + (1 + |M+σ|)/N + 2n/N`.  Which `N` realise a given rational `x = p/q` is a congruence
question; here it is settled completely (integer `M, σ, N`).

## Results (proved)

Write `s = 1 + |M+σ|` and `x = p/q` with `-q < p < q` (any integers, so also `x < 0`; `gcd(p,q) = 1` is only needed for the obstruction).

* `hahn_node_exists` (**sufficient family**).  If `p + q` is odd or `s` is even, then for every `N₀` there are `N > N₀` and
  `n` with `max(|M|,|σ|) < N`, `n < N - max(|M|,|σ|)` (an admissible physical node) and `x_n = x`.  The explicit family is
  `N = q(2u+s)`, `n = u(p+q) + s(p+q-1)/2`, `u ≥ u₀`.
* `hahn_node_obstruction` (**exact obstruction**).  If `gcd(p,q) = 1`, `p + q` is even and `s` is odd, then `x_n ≠ p/q` for
  every integer `N ≠ 0` and every `n`.  (Both `p, q` odd and `M + σ` even; e.g. `M = σ = 0`, `x = 1/3`.)
  Hence for a reduced rational `x ∈ (0,1)` the lattice has nodes `x_n = x` for infinitely many `N` iff `p + q` is odd or
  `M + σ` is odd, and for no `N` otherwise (`hahn_node_iff`).
* `hahn_chain_airy_infinite`: composition with `hahn_chain_airy`.  For every integer `M, σ`, every rational `x ∈ (0,1)` with
  `Odd (num + den) ∨ Even (1 + |M+σ|)` and `A₀ > 0` there are constants (`r, δ₀, C, …`, depending on `M, σ, x, A₀` only)
  such that for **every** `N₀` there is an actual `3j` system `(N, n)`, `N > N₀`, with node `x_n = x` for which the
  conclusion of `hahn_chain_airy` holds.  I.e. the Airy asymptotics of the actual natural-gauge Wigner `3j` chain holds along an
  infinite sequence `N → ∞` (all `N = q(2u+s)`, `u` large).

Claim class: **proved** (exact integer arithmetic; checked with exact rationals for `(M,σ,x) = (0,0,1/2), (1,0,1/3),
(2,1,1/5)` (nodes exist, e.g. `(N,n) = (2,1), (6,4), (10,7)` for `(0,0,1/2)`) and `(0,0,1/3), (1,1,3/5), (0,0,3/5)` (none, for
`N < 200`)).

## Not formalised

Uniformity of the constants over compact sets of `x` (the lattice values `x_n` for a *fixed* `N` accumulate at every real
`x ∈ (-1,1)`, but the constants of `hahn_chain_airy` are for one fixed rational `x`; the paper's compact families need
`discrete_airy_limit` uniform in the Langer data; for the full unified statement this is now `hahn_chain_airy_full_unif`, `DiscreteAiryUnifHahn`, for `x ∈ [x₀, x₁]`); irrational `x` (no exact node); half-integer `M, σ, N` (see
`DiscreteAiryLimitChains2Half*`).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma xLat_int (M σ N : ℤ) (hN : 0 < N) (n : ℕ) :
    xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = ((2 * (n : ℤ) + (1 + |M + σ|) - N : ℤ) : ℚ) / (N : ℚ) := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold xLat
  push_cast
  field_simp
  ring

/-- **Sufficient family of `3j` nodes**: `x = p/q ∈ (-1,1)` is a node `x_n` for infinitely many admissible `(N, n)` as soon as
`p + q` is odd or `1 + |M+σ|` is even. -/
theorem hahn_node_exists (M σ p q : ℤ) (hp : -q < p) (hpq : p < q)
    (hpar : Odd (p + q) ∨ Even (1 + |M + σ|)) (N0 : ℕ) :
    ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
      xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = (p : ℚ) / (q : ℚ) := by
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = 1 + |M + σ| := ⟨_, rfl⟩
  set L0 : ℤ := max |M| |σ| with hL0
  have hs1 : 1 ≤ s := by have := abs_nonneg (M + σ); omega
  have hL0n : 0 ≤ L0 := le_trans (abs_nonneg M) (le_max_left _ _)
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℤ, 0 ≤ K ∧ 2 * K = s * (p + q - 1) := by
    rw [← hs] at hpar
    rcases hpar with ⟨w, hw⟩ | ⟨w, hw⟩
    · refine ⟨s * w, ?_, ?_⟩
      · have : 0 ≤ w := by omega
        positivity
      · rw [show p + q - 1 = 2 * w by omega]; ring
    · refine ⟨w * (p + q - 1), ?_, ?_⟩
      · have : 0 ≤ w := by omega
        have : 0 ≤ p + q - 1 := by omega
        positivity
      · rw [hw]; ring
  set u : ℤ := N0 + K + L0 + 1 with hu
  have hu1 : 0 < u := by omega
  refine ⟨q * (2 * u + s), (u * (p + q) + K).toNat, ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ q := by omega
    nlinarith
  · have : 1 ≤ q := by omega
    nlinarith
  · have hn : (((u * (p + q) + K).toNat : ℕ) : ℤ) = u * (p + q) + K :=
      Int.toNat_of_nonneg (by have : 0 ≤ p + q := by omega
                              positivity)
    rw [hn]
    have h1 : 1 ≤ q - p := by omega
    have h2 : u ≤ u * (q - p) := by nlinarith
    nlinarith
  · have hN : 0 < q * (2 * u + s) := by
      have : 0 < q := by omega
      positivity
    rw [xLat_int M σ _ hN]
    have hn : (((u * (p + q) + K).toNat : ℕ) : ℤ) = u * (p + q) + K :=
      Int.toNat_of_nonneg (by have : 0 ≤ p + q := by omega
                              positivity)
    rw [hn, ← hs]
    have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hN0 : ((q * (2 * u + s) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hK' : (2 : ℚ) * K = s * (p + q - 1) := by exact_mod_cast hK
    rw [div_eq_div_iff hN0 hq]
    push_cast
    have e : 2 * ((u : ℚ) * (p + q) + K) + s - q * (2 * u + s) = p * (2 * u + s) := by
      linear_combination hK'
    rw [e]; ring

/-- **Exact obstruction**: for a reduced fraction `x = p/q` with `p + q` even and `1 + |M+σ|` odd, no integer `N` has a
node `x_n = p/q`. -/
theorem hahn_node_obstruction (M σ p q : ℤ) (hq : 0 < q) (hcop : IsCoprime p q)
    (hpar : Even (p + q)) (hs : Odd (1 + |M + σ|)) (N : ℤ) (hN : 0 < N) (n : ℕ) :
    xLat (M : ℚ) (σ : ℚ) (N : ℚ) n ≠ (p : ℚ) / (q : ℚ) := by
  intro h
  rw [xLat_int M σ N hN] at h
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_eq_div_iff hN' hq'] at h
  have hz : (2 * (n : ℤ) + (1 + |M + σ|) - N) * q = p * N := by exact_mod_cast h
  generalize hsdef : 1 + |M + σ| = s at hz hs
  have hdvd : q ∣ p * N := ⟨2 * (n : ℤ) + s - N, by linarith⟩
  have hqN : q ∣ N := (hcop.symm).dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hqN
  subst ht
  have h2 : 2 * (n : ℤ) + s - q * t = p * t := by
    have hq0 : q ≠ 0 := hq.ne'
    apply mul_left_cancel₀ hq0
    linarith
  obtain ⟨w, hw⟩ := hpar
  obtain ⟨v, hv⟩ := hs
  have h3 : 2 * (n : ℤ) + s = t * (p + q) := by linear_combination h2
  have h4 : t * (p + q) = 2 * (t * w) := by rw [hw]; ring
  omega

/-- **Complete answer** for a reduced rational `x ∈ (0,1)`: nodes exist for some admissible `N` iff `p + q` is odd or
`1 + |M+σ|` is even (and then for infinitely many `N`). -/
theorem hahn_node_iff (M σ p q : ℤ) (hp : -q < p) (hpq : p < q) (hcop : IsCoprime p q) :
    (∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧
        xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = (p : ℚ) / (q : ℚ)) ↔
      (Odd (p + q) ∨ Even (1 + |M + σ|)) := by
  constructor
  · intro H
    by_contra hcon
    push Not at hcon
    obtain ⟨hpe, hso⟩ := hcon
    obtain ⟨N, n, hN0, -, -, hx⟩ := H 0
    exact hahn_node_obstruction M σ p q (by omega) hcop (by simpa using hpe)
      (by simpa using hso) N (by omega) n hx
  · intro h N0
    exact hahn_node_exists M σ p q hp hpq h N0

/-- info: 'FormalResearch.Special.hahn_node_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_node_exists

/-- info: 'FormalResearch.Special.hahn_node_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_node_obstruction

/-- The conclusion of `hahn_chain_airy` for the node `x_n = x` of the system `(N, n)` (the position data of the window and the
two-sided approximation of the natural-gauge `3j` chain by `κ ψ_k`). -/
def HahnAiryOut (M σ N : ℤ) (x : ℚ) (A0 r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = 1 / (N : ℝ) ∧ ∃ J m Nw : ℤ, 1 ≤ J ∧ J ≤ m ∧ m ≤ Nw ∧
    (∀ k ∈ Finset.Icc J (Nw + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - Real.sqrt (1 - (x : ℝ) ^ 2)| ≤ r) ∧
    Real.sqrt (1 - (x : ℝ) ^ 2) - D * δ ^ 2 ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧
    ((J : ℝ) + 1 / 2) * δ ^ 3 ≤ Real.sqrt (1 - (x : ℝ) ^ 2) ∧
    Real.sqrt (1 - (x : ℝ) ^ 2) ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧
    ((m : ℝ) + 1 / 2) * δ ^ 3 < Real.sqrt (1 - (x : ℝ) ^ 2) + δ ^ 3 ∧
    turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ J ≤ -A0 ∧
    ξ0 / δ ^ 3 ≤ airyXi (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ Nw) ∧
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Real.sqrt (N : ℝ) *
        Real.exp (-airyXi (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ Nw)) ∧
      (∀ k ∈ Finset.Icc J m, |hahn3jY M σ N x k -
          κ * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k| ≤
        C * δ ^ 3 * |κ| * W + Cosc * (|μ| / δ)) ∧
      (∀ k ∈ Finset.Icc m (Nw + 1), |hahn3jY M σ N x k -
          κ * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k| ≤
        C * δ ^ 3 * |κ| * turnPsi (hrU 1 0 1 (x : ℝ)) (hrA1 1 0) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k +
          Ctop * |μ| / δ / airyWt (turnX (hrU 1 0 1 (x : ℝ)) (Real.sqrt (1 - (x : ℝ) ^ 2)) (δ ^ 3 / 2) δ k))

/-- **Airy asymptotics of the actual `3j` chain along an infinite sequence `N → ∞`** (`thm:hahnAiryConnection`, integer
case; `hahn_chain_airy` + `hahn_node_exists`).  For integer `M, σ`, a rational `x ∈ (0,1)` with
`Odd (num + den) ∨ Even (1 + |M+σ|)` (exactly the `x` that occur as nodes, `hahn_node_iff`), and `A₀ > 0`, with the constants
of `hahn_chain_airy`: for every `N₀` there is an admissible `3j` system `(N, n)`, `N > N₀`, with node `x_n = x`, for which
the conclusion `HahnAiryOut` (= that of `hahn_chain_airy`) holds. -/
theorem hahn_chain_airy_infinite (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1)
    (hpar : Odd (x.num + (x.den : ℤ)) ∨ Even (1 + |M + σ|)) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ max |M| |σ| < N ∧
        (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x ∧ 1 / (N : ℝ) ≤ δ0 ^ 3 ∧
        HahnAiryOut M σ N x A0 r δ0 C Cosc Ctop W Cmu ξ0 D := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    hahn_chain_airy M σ x hx0 hx1 A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N0
  have hnum : 0 < x.num := Rat.num_pos.2 hx0
  have hlt : x.num < (x.den : ℤ) := by
    have h1 : (x.num : ℚ) / (x.den : ℚ) < 1 := by rwa [Rat.num_div_den]
    have h2 : (x.num : ℚ) < (x.den : ℚ) := by
      rwa [div_lt_one (by exact_mod_cast x.den_pos)] at h1
    exact_mod_cast h2
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / δ0 ^ 3)
  obtain ⟨N, n, hN0, hN1, hN2, hxn⟩ :=
    hahn_node_exists M σ x.num x.den (by omega) hlt hpar (max N0 T)
  have hxn' : xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x := by
    rw [hxn]; exact_mod_cast Rat.num_div_den x
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℤ) < N := by have := le_max_left N0 T; omega
    exact_mod_cast this
  have hNT : (T : ℝ) < N := by
    have : (T : ℤ) < N := by have := le_max_right N0 T; omega
    exact_mod_cast this
  have hδ : 1 / (N : ℝ) ≤ δ0 ^ 3 := by
    have h3 : 0 < δ0 ^ 3 := by positivity
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ h3).1 hT
    nlinarith
  exact ⟨N, n, by have := le_max_left N0 T; omega, hN1, hN2, hxn', hδ, H N n hN1 hN2 hxn' hδ⟩

/-- info: 'FormalResearch.Special.hahn_chain_airy_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy_infinite

end FormalResearch.Special

module

public import FormalResearch.Special.BulkIndexSteps
public import FormalResearch.Special.BulkKappaHahnZeros
public import FormalResearch.Special.ChainOscHahn

/-!
# Bulk index for the actual `3j` chain: nodes in the bulk equal the drop of `⌊Φ(q)/(πh) + 1/4⌋`

Composition of the explicit bulk theorem `hahn_chain_bulk_explicit` (`BulkKappaHahnInst`) with the abstract counting
theorem `bix_count` (`BulkIndexCount`) and the phase steps `bix_phase_step` (`BulkIndexSteps`).  Notation: `h = 1/N`,
`q_k = (k + 1/2) h` (`bixQ`), `Φ(q) = ∫_q^{q_*} arccos(x/√(1-t²)) dt` (`bkPhase`), `θ_k = Φ(q_k)/h - π/4` (`bixTheta`),
`q_* = √(1 - x²)`, and `u_i = Ŷ_{kmin+i}` (`bixU`, the natural-gauge `3j` chain `hahn3jY M σ N x` from its first site
`kmin = max |M| |σ|`, as in `cho_hahn_nodes`).

* **`bix_hahn_window`**: for `[a, b] ⊂ (0, q_*)` there are `η ∈ (0, π/6)` and `ε > 0` such that at every lattice node with
  `h ≤ ε` and every site window `[kmin + i₁, kmin + i₂]` with `q ∈ [a, b]` the chain is in the amplitude-phase form of
  `BixWin` (tolerance `sin η`, a sign `s = ±1`, amplitude `bkAmp`, steps in `(2η, π - 2η)`).
* **`bix_hahn_count`** (step (i) of the zero index; every bulk Bohr-Sommerfeld window carries exactly one node):
  with `t₀ = sin η < 1/2` (so `|cos θ| > 1/2` suffices; see `BulkWindowIndex.bwn_bulk_count`), for every pair of sites `i₁ ≤ i₂` of the window with `|cos θ| > t₀` there, the number of nodes
  (sign changes `u_j u_{j+1} < 0` and interior zeros, `bix_c`) in the bonds `i₁, …, i₂ - 1` is exactly
  `⌊Φ(q_{i₁})/(π h) + 1/4⌋ - ⌊Φ(q_{i₂})/(π h) + 1/4⌋`, the number of integers `m` with `Φ(q_{i₂})/h < π (m - 1/4) ≤ Φ(q_{i₁})/h`,
  i.e. of Bohr-Sommerfeld points of `hahn_chain_bulk_zeros` in the window.  The value of `u` at a site with `|cos θ| ≤ t₀` is
  irrelevant (such sites are isolated).

**Numerics (mpmath, 40 digits, exact `3j` symbols from the Racah sum; numerical evidence only, throw-away script).**  Chains
`(M, σ, N, n) = (1,0,60,40), (2,1,100,70), (1,-1,150,110), (2,-2,200,150), (3,1,300,220), (1,0,400,300), (2,1,400,260), (1,1,400,330)`
(`x_n > 0`): the node count of the chain is `m - n` (`cho_hahn_nodes`) in all eight; the number `R_k` of sign changes in the bonds `j ≥ k` equals
`⌊Φ(q_k)/(πh) + 1/4⌋` at every bulk site `0.15 q_* ≤ q_k < q_*` with `|cos(Φ/h - π/4)| ≥ 0.05` (offset `0`, `1500` sites in total; `3` exceptions
for `(2,-2,200,150)` at `q ≈ 0.18, 0.19, 0.21` with `|cos| ∈ (0.05, 0.16)`, where the `O(h)` second-order phase correction exceeds the margin), while the offsets `±1` fail at every site (negative control),
and there is no sign change at a bond with `q_k ≥ q_*` in any of the eight chains.

**Claim class: proved** (composition of proved results; axiom guards pinned).  **Not formalised:** `τ = -1`, the half-integer lattice and the
Racah chains (the same proof with the corresponding explicit theorems); the identification of the right-end count (see `BulkIndexRight`).
-/

@[expose] public section

open Finset Real FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The lattice point `q_k = (k + 1/2) h`, `h = 1/N`. -/
noncomputable def bixQ (N k : ℤ) : ℝ := ((k : ℝ) + 1 / 2) * (1 / (N : ℝ))

/-- The phase `θ_k = Φ(q_k)/h - π/4` (`τ = +1`, integer lattice). -/
noncomputable def bixTheta (x : ℝ) (N k : ℤ) : ℝ :=
  bkPhase 1 0 1 x (√(1 - x ^ 2)) (bixQ N k) / (1 / (N : ℝ)) - π / 4

/-- The natural-gauge `3j` chain from its first site `kmin = max |M| |σ|`. -/
noncomputable def bixU (M σ N : ℤ) (x : ℚ) (i : ℕ) : ℝ := hahn3jY M σ N x (max |M| |σ| + (i : ℤ))

theorem bixQ_succ (N k : ℤ) : bixQ N (k + 1) = bixQ N k + 1 / (N : ℝ) := by
  unfold bixQ; push_cast; ring

theorem bixQ_mono {N k k' : ℤ} (hN : 0 < N) (h : k ≤ k') : bixQ N k ≤ bixQ N k' := by
  unfold bixQ
  have : (k : ℝ) ≤ k' := by exact_mod_cast h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  gcongr

theorem bix_amp_pos {x q : ℝ} (hq : q < √(1 - x ^ 2)) (hq0 : 0 ≤ q) : 0 < bkAmp 1 0 x (√(1 - x ^ 2)) q := by
  have hqs : 0 < √(1 - x ^ 2) := lt_of_le_of_lt hq0 hq
  have hS : rkS 1 0 x = 1 := by simp [rkS]
  have h1 : 0 < √(1 - x ^ 2) ^ 2 - q ^ 2 := by nlinarith
  unfold bkAmp
  rw [hS, one_mul]
  have := Real.sqrt_pos.2 (Real.sqrt_pos.2 h1)
  positivity

theorem bixN_theta (Φ h : ℝ) (hh : 0 < h) : bixN (Φ / h - π / 4) = ⌊Φ / (π * h) + 1 / 4⌋ := by
  unfold bixN
  congr 1
  have hπ := Real.pi_pos
  field_simp
  ring

theorem bix_def_iff {θ : ℕ → ℝ} {η : ℝ} {j : ℕ} : BixDef θ η j ↔ Real.sin η < |Real.cos (θ j)| := by
  unfold BixDef
  rw [bix_cos_eq, abs_mul]
  have h1 : |(-1 : ℝ) ^ bixN (θ j)| = 1 := by
    have := bix_neg_one_zpow_sq (bixN (θ j))
    have h2 : |(-1 : ℝ) ^ bixN (θ j)| * |(-1 : ℝ) ^ bixN (θ j)| = 1 := by rw [← abs_mul, this]; simp
    nlinarith [abs_nonneg ((-1 : ℝ) ^ bixN (θ j))]
  rw [h1, one_mul, abs_of_nonneg (bix_sin_nonneg _)]

/-- **The `3j` chain is in the amplitude-phase form `BixWin`** on every site window with `q ∈ [a, b] ⊂ (0, q_*)`. -/
theorem bix_hahn_window (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ η ε : ℝ, 0 < η ∧ η < π / 6 ∧ 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        1 / (N : ℝ) ≤ ε → ∀ i₁ i₂ : ℕ, i₁ ≤ i₂ → a ≤ bixQ N (max |M| |σ| + (i₁ : ℤ)) →
          bixQ N (max |M| |σ| + (i₂ : ℤ)) ≤ b →
          ∃ (s : ℝ) (A : ℕ → ℝ), BixWin (bixU M σ N x) (fun i => bixTheta (x : ℝ) N (max |M| |σ| + (i : ℤ))) A s η i₁ i₂ := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqs
  have hδ1 : 0 < Real.arccos ((x : ℝ) / √(1 - b ^ 2)) :=
    Real.arccos_pos.2 (bix_lt_one (by linarith) hb)
  have hδ1' : Real.arccos ((x : ℝ) / √(1 - b ^ 2)) < π / 2 := by
    rw [Real.arccos_lt_pi_div_two]
    have : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 (by
      have h1 : 0 < 1 - (x : ℝ) ^ 2 := by nlinarith
      have : b ^ 2 < 1 - (x : ℝ) ^ 2 := by
        have := pow_lt_pow_left₀ hb (by linarith) (two_ne_zero)
        rwa [Real.sq_sqrt h1.le] at this
      nlinarith)
    positivity
  have hδ2 : Real.arccos (x : ℝ) < π / 2 := Real.arccos_lt_pi_div_two.2 hx0'
  set η : ℝ := Real.arccos ((x : ℝ) / √(1 - b ^ 2)) / 3 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < π / 6 := by rw [hη]; linarith
  have ht : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  obtain ⟨ε, hε, H⟩ := hahn_chain_bulk_explicit M σ x hx0 hx1 a b ha hab hb (Real.sin η) ht
  refine ⟨η, ε, hη0, hη1, hε, ?_⟩
  intro N n hnode hNε i₁ i₂ hi hlo hhi
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : 0 < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨s, hs, Hs⟩ := H N n ⟨hN, hn, hxn⟩ hNε
  have hin : ∀ j : ℕ, i₁ ≤ j → j ≤ i₂ → a ≤ bixQ N (max |M| |σ| + (j : ℤ)) ∧ bixQ N (max |M| |σ| + (j : ℤ)) ≤ b := by
    intro j h1 h2
    exact ⟨hlo.trans (bixQ_mono hNpos (by omega)), (bixQ_mono hNpos (by omega)).trans hhi⟩
  refine ⟨s, fun i => bkAmp 1 0 (x : ℝ) qs (bixQ N (max |M| |σ| + (i : ℤ))), ?_⟩
  refine ⟨hs, hη0, by linarith, ?_, ?_, ?_⟩
  · intro j h1 h2
    obtain ⟨l, u⟩ := hin j h1 h2
    exact bix_amp_pos (lt_of_le_of_lt u hb) (by linarith)
  · intro j h1 h2
    obtain ⟨l, u⟩ := hin j h1 h2
    exact Hs _ l u
  · intro j h1 h2
    obtain ⟨l, u⟩ := hin j h1 (by omega)
    obtain ⟨l', u'⟩ := hin (j + 1) (by omega) h2
    have hq1 : bixQ N (max |M| |σ| + ((j + 1 : ℕ) : ℤ)) = bixQ N (max |M| |σ| + (j : ℤ)) + 1 / (N : ℝ) := by
      rw [← bixQ_succ]; congr 1; push_cast; ring
    have hstep := bix_phase_step (x := (x : ℝ)) (b := b) (q := bixQ N (max |M| |σ| + (j : ℤ)))
      (q' := bixQ N (max |M| |σ| + ((j + 1 : ℕ) : ℤ))) hx0' hx1' hb (by linarith)
      (by rw [hq1]; have : (0 : ℝ) < 1 / N := by positivity
          linarith) u'
    rw [hq1] at hstep
    have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hdiff : bixTheta (x : ℝ) N (max |M| |σ| + (j : ℤ)) - bixTheta (x : ℝ) N (max |M| |σ| + ((j + 1 : ℕ) : ℤ)) =
        (bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ))) -
          bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ)) + 1 / (N : ℝ))) / (1 / (N : ℝ)) := by
      unfold bixTheta; rw [hq1]; ring
    simp only [hdiff]
    have e1 : bixQ N (max |M| |σ| + (j : ℤ)) + 1 / (N : ℝ) - bixQ N (max |M| |σ| + (j : ℤ)) = 1 / (N : ℝ) := by ring
    rw [e1] at hstep
    obtain ⟨hs1, hs2⟩ := hstep
    constructor
    · have : Real.arccos ((x : ℝ) / √(1 - b ^ 2)) ≤
          (bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ))) -
            bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ)) + 1 / (N : ℝ))) / (1 / (N : ℝ)) := by
        rw [le_div_iff₀ hh]; exact hs1
      rw [hη]; linarith
    · have : (bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ))) -
            bkPhase 1 0 1 (x : ℝ) qs (bixQ N (max |M| |σ| + (j : ℤ)) + 1 / (N : ℝ))) / (1 / (N : ℝ)) ≤ Real.arccos (x : ℝ) := by
        rw [div_le_iff₀ hh]; exact hs2
      rw [hη]; linarith [Real.pi_pos]

/-- **Step (i): one node per Bohr-Sommerfeld window in the bulk.**  For definite sites `i₁ ≤ i₂` (`|cos θ| > t₀`) of a bulk window of the
`3j` chain, the nodes in the bonds `i₁, …, i₂ - 1` number exactly `⌊Φ(q_{i₁})/(π h) + 1/4⌋ - ⌊Φ(q_{i₂})/(π h) + 1/4⌋`. -/
theorem bix_hahn_count (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hb : b < √(1 - (x : ℝ) ^ 2)) :
    ∃ t₀ ε : ℝ, 0 < t₀ ∧ 0 < ε ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        1 / (N : ℝ) ≤ ε → ∀ i₁ i₂ : ℕ, i₁ ≤ i₂ → a ≤ bixQ N (max |M| |σ| + (i₁ : ℤ)) →
          bixQ N (max |M| |σ| + (i₂ : ℤ)) ≤ b →
          t₀ < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (i₁ : ℤ)))| →
          t₀ < |Real.cos (bixTheta (x : ℝ) N (max |M| |σ| + (i₂ : ℤ)))| →
          ((∑ j ∈ Ico i₁ i₂, bix_c (bixU M σ N x) j : ℕ) : ℤ) =
            ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i₁ : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋ -
            ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ N (max |M| |σ| + (i₂ : ℤ))) / (π * (1 / (N : ℝ))) + 1 / 4⌋ := by
  obtain ⟨η, ε, hη0, hη1, hε, H⟩ := bix_hahn_window M σ x hx0 hx1 a b ha hab hb
  refine ⟨Real.sin η, ε, Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos]), hε, ?_⟩
  intro N n hnode hNε i₁ i₂ hi hlo hhi hd1 hd2
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : 0 < N := lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨s, A, W⟩ := H N n ⟨hN, hn, hxn⟩ hNε i₁ i₂ hi hlo hhi
  have key := bix_count W (i₂ - i₁) i₁ le_rfl (by omega) (bix_def_iff.2 hd1)
    (by rw [Nat.add_sub_cancel' hi]; exact bix_def_iff.2 hd2)
  rw [Nat.add_sub_cancel' hi] at key
  rw [key]
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  unfold bixTheta
  rw [bixN_theta _ _ hh, bixN_theta _ _ hh]

/-- info: 'FormalResearch.Special.bix_hahn_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_hahn_count

end FormalResearch.Special

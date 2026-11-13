module

public import FormalResearch.Racah.P2ThreeJSystem

/-!
# The simple spectrum `{L(L+1)}` of the finite operator `𝖧_h` (Weyl P2, `thm:3jspectral`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jspectral`:
`spec(𝖧_h) = {L(L+1) : L = L₀,…,N-1}`, eigenfunctions `Φ_L^{M,σ}`.

`𝖧_h` acts on functions on the physical lattice `𝒳_N = {x_n : n < K}`; `Hh M σ N ψ (x_n)` involves
`ψ` at `x_{n±1}` only with the coefficients `a_h(x_n ± h)`, which vanish at the two ends, so values
of `ψ` off the lattice never matter.  `LatEigen lam ψ` says that the lattice function `ψ|_{𝒳_N}` is a
nonzero eigenvector of `𝖧_h` with eigenvalue `lam` (the extension of `ψ` to `ℚ` is arbitrary).

* `Phi_latEigen`: `Φ_L` (`L = L₀ + i`, `i < K`) is such an eigenvector with eigenvalue `L(L+1)`.
* `Hh_spectrum_iff`: `lam` is an eigenvalue of `𝖧_h` on `ℓ²(𝒳_N)` iff `lam = L(L+1)` for some
  `L = L₀,…,N-1` (so `spec(𝖧_h) = {L(L+1)}`).
* `rankEig_strictMono`: these `K = N - L₀` numbers are pairwise distinct, so the spectrum has exactly
  `K = |𝒳_N|` points (the grid dimension) and is simple.
* `Hh_eigen_simple`: every eigenvector for `L(L+1)` is a multiple of `Φ_L` (the eigenspace is a line).

Proof: eigenvectors for different eigenvalues are orthogonal (symmetry `Hh_lattice_symmetric`), and
`{Φ_L}` is a basis by the completeness relation `Phi_disccomplete`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- `ψ` restricted to the lattice `{x_n : n < K}` is a nonzero eigenvector of `𝖧_h` with
eigenvalue `lam`. -/
def LatEigen (M σ N : ℚ) (K : ℕ) (lam : ℝ) (ψ : ℚ → ℝ) : Prop :=
  (∃ n < K, ψ (xLat M σ N n) ≠ 0) ∧
    ∀ n < K, Hh M σ N ψ (xLat M σ N n) = lam * ψ (xLat M σ N n)

/-- The eigenvalue `L(L+1)` of the `i`-th rank `L = L₀ + i`. -/
noncomputable def rankEig (M σ : ℚ) (i : ℕ) : ℝ :=
  ((max |M| |σ| + i : ℚ) : ℝ) * (((max |M| |σ| + i : ℚ) : ℝ) + 1)

/-- The eigenvalues `L(L+1)` are strictly increasing in the rank. -/
theorem rankEig_strictMono (M σ : ℚ) {i j : ℕ} (hij : i < j) : rankEig M σ i < rankEig M σ j := by
  unfold rankEig
  push_cast
  have hc : 0 ≤ max |(M : ℝ)| |(σ : ℝ)| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have : 0 < ((j : ℝ) - i) * (2 * max |(M : ℝ)| |(σ : ℝ)| + i + j + 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [this]

/-- `Φ_L` is an eigenvector of `𝖧_h` with eigenvalue `L(L+1)`, `L = L₀ + i`, `i < K`. -/
theorem Phi_latEigen {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {i : ℕ} (hi : i < K) :
    LatEigen M σ N K (rankEig M σ i) (PhiX (max |M| |σ| + i) M σ N) := by
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hL := rank_adm hA hK hi
    have h := Phi_discorth hA hN hK hL.1 hL.2.1 hL.2.2 hL.1 hL.2.1 hL.2.2
    have hz : ∑ n ∈ Finset.range K, PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
        PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [hcon n (Finset.mem_range.mp hn)]; ring
    rw [hz] at h
    simp only [↓reduceIte] at h
    have hpos : (0 : ℝ) < 2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1 := by
      have : (0 : ℚ) ≤ max |M| |σ| + i := by
        have := le_trans (abs_nonneg M) (le_max_left |M| |σ|)
        positivity
      have : (0 : ℝ) ≤ ((max |M| |σ| + i : ℚ) : ℝ) := by exact_mod_cast this
      linarith
    have : (0 : ℝ) < 2 / (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) := by positivity
    rw [mul_zero] at h
    linarith
  · intro n hn
    obtain ⟨a1, a4, b1, b3⟩ := lat_adm hA hN hK hn
    exact Hh_Phi _ M σ N _ hN a1 a4 b1 b3

/-- Expansion of a lattice function in the basis `{Φ_L}` (completeness). -/
lemma lat_expansion {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) (ψ : ℚ → ℝ) {n : ℕ} (hn : n < K) :
    ψ (xLat M σ N n) = (1 / (N : ℝ)) * ∑ i ∈ Finset.range K,
      (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) * PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
        ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
          PhiX (max |M| |σ| + i) M σ N (xLat M σ N n') := by
  have h1 : ∀ i ∈ Finset.range K,
      (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) * PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
        ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
          PhiX (max |M| |σ| + i) M σ N (xLat M σ N n') =
      ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
        ((2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
          (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
            PhiX (max |M| |σ| + i) M σ N (xLat M σ N n'))) := by
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n' _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  have h2 : ∀ n' ∈ Finset.range K, (1 / (N : ℝ)) * ∑ i ∈ Finset.range K, ψ (xLat M σ N n') *
        ((2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
          (PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
            PhiX (max |M| |σ| + i) M σ N (xLat M σ N n'))) =
      ψ (xLat M σ N n') * (if n = n' then 1 else 0) := by
    intro n' hn'
    have hc := Phi_disccomplete hA hN hK hn (Finset.mem_range.mp hn')
    rw [← Finset.mul_sum] at *
    rw [← hc]
    ring
  rw [Finset.sum_congr rfl h2]
  simp [Finset.sum_ite_eq, hn]

/-- Eigenvectors are orthogonal to `Φ_L` unless the eigenvalues agree. -/
lemma eigen_orth {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {lam : ℝ} {ψ : ℚ → ℝ} (hψ : LatEigen M σ N K lam ψ)
    {i : ℕ} (hi : i < K) :
    (lam - rankEig M σ i) * ∑ n ∈ Finset.range K, ψ (xLat M σ N n) *
      PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) = 0 := by
  have hΦ := Phi_latEigen hA hN hK hi
  have hsym := Hh_lattice_symmetric M σ N hN.ne' K hK (PhiX (max |M| |σ| + i) M σ N) ψ
  have e1 : ∑ n ∈ Finset.range K, PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
      Hh M σ N ψ (xLat M σ N n) =
      lam * ∑ n ∈ Finset.range K, ψ (xLat M σ N n) *
        PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hψ.2 n (Finset.mem_range.mp hn)]; ring
  have e2 : ∑ n ∈ Finset.range K, ψ (xLat M σ N n) *
      Hh M σ N (PhiX (max |M| |σ| + i) M σ N) (xLat M σ N n) =
      rankEig M σ i * ∑ n ∈ Finset.range K, ψ (xLat M σ N n) *
        PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hΦ.2 n (Finset.mem_range.mp hn)]; ring
  rw [e1, e2] at hsym
  linarith

/-- **`spec(𝖧_h) = {L(L+1) : L = L₀,…,N-1}`** (`thm:3jspectral`): `lam` is an eigenvalue of `𝖧_h`
on `ℓ²(𝒳_N)` iff `lam = L(L+1)` for a rank `L = L₀ + i`, `i < K = N - L₀`. -/
theorem Hh_spectrum_iff {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) (lam : ℝ) :
    (∃ ψ : ℚ → ℝ, LatEigen M σ N K lam ψ) ↔ ∃ i < K, lam = rankEig M σ i := by
  constructor
  · rintro ⟨ψ, hψ⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn, hne⟩ := hψ.1
    apply hne
    rw [lat_expansion hA hN hK ψ hn]
    have : ∀ i ∈ Finset.range K, (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
        PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) *
          ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
            PhiX (max |M| |σ| + i) M σ N (xLat M σ N n') = 0 := by
      intro i hi
      have h := eigen_orth hA hN hK hψ (Finset.mem_range.mp hi)
      have hne' : lam - rankEig M σ i ≠ 0 := sub_ne_zero.mpr (hcon i (Finset.mem_range.mp hi))
      have h0 := (mul_eq_zero.mp h).resolve_left hne'
      rw [h0]; ring
    rw [Finset.sum_eq_zero this]; ring
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, Phi_latEigen hA hN hK hi⟩

/-- **Simplicity**: an eigenvector for `L(L+1)` (`L = L₀ + i`) is a multiple of `Φ_L` on the
lattice. -/
theorem Hh_eigen_simple {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {i : ℕ} (hi : i < K) {ψ : ℚ → ℝ}
    (hψ : LatEigen M σ N K (rankEig M σ i) ψ) :
    ∃ c : ℝ, ∀ n < K, ψ (xLat M σ N n) = c * PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) := by
  refine ⟨(1 / (N : ℝ)) * ((2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
    ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
      PhiX (max |M| |σ| + i) M σ N (xLat M σ N n')), ?_⟩
  intro n hn
  rw [lat_expansion hA hN hK ψ hn]
  have hz : ∀ j ∈ Finset.range K, j ≠ i → (2 * ((max |M| |σ| + j : ℚ) : ℝ) + 1) *
        PhiX (max |M| |σ| + j) M σ N (xLat M σ N n) *
          ∑ n' ∈ Finset.range K, ψ (xLat M σ N n') *
            PhiX (max |M| |σ| + j) M σ N (xLat M σ N n') = 0 := by
    intro j hj hji
    have h := eigen_orth hA hN hK hψ (Finset.mem_range.mp hj)
    have hne' : rankEig M σ i - rankEig M σ j ≠ 0 := by
      rcases lt_or_gt_of_ne hji with h1 | h1
      · exact (sub_pos.mpr (rankEig_strictMono M σ h1)).ne'
      · exact (sub_neg.mpr (rankEig_strictMono M σ h1)).ne
    have h0 := (mul_eq_zero.mp h).resolve_left hne'
    rw [h0]; ring
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) hz]
  ring

/-- info: 'FormalResearch.Racah.Phi_latEigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi_latEigen

/-- info: 'FormalResearch.Racah.Hh_spectrum_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hh_spectrum_iff

/-- info: 'FormalResearch.Racah.Hh_eigen_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hh_eigen_simple

/-- info: 'FormalResearch.Racah.rankEig_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankEig_strictMono

end FormalResearch.Racah

module

public import FormalResearch.Special.BulkKappaZeros
public import FormalResearch.Special.BulkKappaHahnInst

/-!
# Bulk zero localisation for the actual `3j` chain (integer and half-integer data, `τ = ±1`)

Instances of `bk_zeros_of_out` (`BulkKappaZeros`) for the families of `BulkKappaHahn`, `BulkKappaHahnH` (see `BulkKappaHahnInst` for the table of chains).  For every compact `[a, b] ⊂ (0, q_*)`,
`q_* = √(1 - x²)`, there are `ε, C₀ > 0` such that at every lattice node with `h ≤ ε` and every bond `(k, k+1)` with `q_k, q_{k+1} ∈ [a, b]` across which the chain changes sign (`Y_k Y_{k+1} ≤ 0`) there is an
integer `m` with

`Φ(q_{k+1})/h - C₀ h ≤ π (m - 1/4) ≤ Φ(q_k)/h + C₀ h`,  `Φ(q) = ∫_q^{q_*} arccos(|x|/√(1-t²)) dt` (`bkPhase`):

the bond contains, up to `O(h)` in the phase, a point `Φ(q) = π h (m - 1/4)` of the Bohr-Sommerfeld lattice, i.e. a zero `(2j+1)π/2` of `cos(Φ(q)/h - π/4)`.  This is a leading-order (error `O(h)` in the phase) counterpart of the
bulk-zero quantisation `thm:general-bulk-zeros` (`Weyl/P3/paper/weyl_midpoint_semiclassics.tex`): the phase is anchored at the turning point `q_*` (the paper's action `N S(q, x)` and offset `p_{ab}π/2` are anchored at
`q = 0`; the relation between the two anchorings is not formalised), and the second-order term `h Γ̃` (with the Darboux term), the `O(N^{-3})` error and the identification of the index `ν_j` are not part of the Lean statement.

**Claim class: proved.**  **Not formalised:** the converse (a sign change in every bond that contains a Bohr-Sommerfeld point, equivalently the count of sign changes in `[a, b]`), the conversion of the phase window into
a window in `q` (needs `arccos u ≥ θ_min > 0` on `[a, b]`), constants uniform in `(a, b)` or in the data, the regions near the turning point and near `q = 0`.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Bulk zero localisation for the integer `3j` chain** (generic twist). -/
theorem bk_hahn_int_zeros (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 < N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (hrCk 1 0 τ (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (fun j => u j * hahn3jY M σ N x j) k = 0) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x →
        Y = (fun j => u j * hahn3jY M σ N x j) → 1 / (N : ℝ) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ)) ≤ b → Y k * Y (k + 1) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - C0 * (1 / (N : ℝ)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) +
              C0 * (1 / (N : ℝ)) := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_hahn_int M σ x τ u hxτ hx1 hu hrowsAll
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  have hS1 : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hS : 0 < rkS 1 0 (x : ℝ) := by rw [hS1]; norm_num
  have hE := bk_zeros_of_out (zero_le_one : (0 : ℝ) ≤ 1) (le_rfl : (0 : ℝ) ≤ 0) hτ (bkh_turn_id hx1) hS hqs hα hβ
    (θ := 1 / 2) (q₀ := fun δ => δ ^ 3 / 2) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, HE⟩ := hE a b ha hab hbq
  refine ⟨min ε hm, C0, lt_min hε hmpos, hC0, ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_le_of_lt (le_trans (abs_nonneg M) (le_max_left _ _)) hN
  have hmem : bkFamHahn M σ x u hm (1 / (N : ℝ)) Y (N : ℝ) :=
    ⟨by positivity, hNε.trans (min_le_right _ _), N, n, hN, hn, hxn, rfl, hY, rfl⟩
  exact HE _ _ _ hmem (by positivity) (hNε.trans (min_le_left _ _))

/-- **Bulk zero localisation for the half-integer `3j` chain** (generic twist). -/
theorem bk_hahn_half_zeros (M σ : ℤ) (x : ℚ) (τ : ℝ) (u : ℤ → ℝ) (hxτ : (τ = 1 ∧ 0 < (x : ℝ)) ∨ (τ = -1 ∧ (x : ℝ) < 0))
    (hx1 : |(x : ℝ)| < 1) (hu : ∀ k, u k ^ 2 = 1)
    (hrowsAll : ∀ N : ℤ, 0 ≤ N → ∀ k : ℤ, 1 ≤ k →
      jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (hrCkH 1 0 τ (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
        (fun j => u j * hahn3jYH M σ N x j) k = 0) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ) (Y : ℤ → ℝ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x →
        Y = (fun j => u j * hahn3jYH M σ N x j) → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b → Y k * Y (k + 1) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - C0 * (1 / ((N : ℝ) + 1 / 2)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 τ (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) +
              C0 * (1 / ((N : ℝ) + 1 / 2)) := by
  obtain ⟨r, Cmu, ξ0, gmax, gmin, c1, c2, CA, δA, hm, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hmpos, Hout⟩ :=
    bk_hahn_half M σ x τ u hxτ hx1 hu hrowsAll
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom hxτ hx1
  have hS1 : rkS 1 0 (x : ℝ) = 1 := by simp [rkS]
  have hS : 0 < rkS 1 0 (x : ℝ) := by rw [hS1]; norm_num
  have hE := bk_zeros_of_out (zero_le_one : (0 : ℝ) ≤ 1) (le_rfl : (0 : ℝ) ≤ 0) hτ (bkh_turn_id hx1) hS hqs hα hβ
    (θ := 1) (q₀ := fun δ => δ ^ 3) (fun δ k => by unfold dlgQ; ring) h1 h2 h4 h5 Hout h11
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, HE⟩ := hE a b ha hab hbq
  refine ⟨min ε hm, C0, lt_min hε hmpos, hC0, ?_⟩
  intro N n Y hnode hY hNε
  obtain ⟨hN, hn, hxn⟩ := hnode
  have hNpos : (0 : ℝ) < ((N : ℝ) + 1 / 2) := by have h0 : (0 : ℝ) ≤ N := (by exact_mod_cast (le_trans (halfLo_nonneg M σ) hN.le)); linarith
  have hmem : bkFamHahnH M σ x u hm (1 / ((N : ℝ) + 1 / 2)) Y ((N : ℝ) + 1 / 2) :=
    ⟨by positivity, hNε.trans (min_le_right _ _), N, n, hN, hn, hxn, rfl, hY, rfl⟩
  exact HE _ _ _ hmem (by positivity) (hNε.trans (min_le_left _ _))

/-- **Bulk zero localisation for the integer `3j` chain, `τ = +1`** (see the module docstring). -/
theorem hahn_chain_bulk_zeros (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ)) ≤ b →
          hahn3jY M σ N x k * hahn3jY M σ N x (k + 1) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - C0 * (1 / (N : ℝ)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) +
              C0 * (1 / (N : ℝ)) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_hahn_int_zeros M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_int_pos M σ x) a b ha hab hbq
  exact ⟨ε, C0, hε, hC0, fun N n hnode hNε k hk1 hk2 hch => H N n _ hnode (by funext j; simp) hNε k hk1 hk2 hch⟩

/-- **Bulk zero localisation for the twisted integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem hahn_chain_bulk_zeros_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ), max |M| |σ| < N ∧ (n : ℤ) < N - max |M| |σ| ∧ xLat (M : ℚ) (σ : ℚ) (N : ℚ) n = x → 1 / (N : ℝ) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1 / 2) * (1 / (N : ℝ)) → ((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ)) ≤ b →
          ((-1 : ℝ) ^ k * hahn3jY M σ N x k) * ((-1 : ℝ) ^ (k + 1) * hahn3jY M σ N x (k + 1)) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) - C0 * (1 / (N : ℝ)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 / 2) * (1 / (N : ℝ))) / (1 / (N : ℝ)) +
              C0 * (1 / (N : ℝ)) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_hahn_int_zeros M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_int_neg M σ x) a b ha hab hbq
  exact ⟨ε, C0, hε, hC0, fun N n hnode hNε k hk1 hk2 hch => H N n _ hnode rfl hNε k hk1 hk2 hch⟩

/-- **Bulk zero localisation for the half-integer `3j` chain, `τ = +1`** (see the module docstring). -/
theorem hahn_chain_bulk_zeros_half (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b →
          hahn3jYH M σ N x k * hahn3jYH M σ N x (k + 1) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - C0 * (1 / ((N : ℝ) + 1 / 2)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) +
              C0 * (1 / ((N : ℝ) + 1 / 2)) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by have h0 : (0 : ℝ) < x := (by exact_mod_cast hx0); linarith, by exact_mod_cast hx1⟩
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_hahn_half_zeros M σ x 1 (fun _ => 1) (Or.inl ⟨rfl, by exact_mod_cast hx0⟩) hx (fun _ => by norm_num) (bkh_rows_half_pos M σ x) a b ha hab hbq
  exact ⟨ε, C0, hε, hC0, fun N n hnode hNε k hk1 hk2 hch => H N n _ hnode (by funext j; simp) hNε k hk1 hk2 hch⟩

/-- **Bulk zero localisation for the twisted half-integer `3j` chain `(-1)^k Ŷ_k`, `τ = -1`** (see the module docstring). -/
theorem hahn_chain_bulk_zeros_half_neg (M σ : ℤ) (x : ℚ) (hx0 : x < 0) (hx1 : -1 < x) :
    ∀ a b : ℝ, 0 < a → a < b → b < √(1 - (x : ℝ) ^ 2) → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧
      ∀ (N : ℤ) (n : ℕ), halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ ε →
        ∀ k : ℤ, a ≤ ((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2)) → ((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2)) ≤ b →
          ((-1 : ℝ) ^ k * hahn3jYH M σ N x k) * ((-1 : ℝ) ^ (k + 1) * hahn3jYH M σ N x (k + 1)) ≤ 0 →
          ∃ m : ℤ, bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1 + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) - C0 * (1 / ((N : ℝ) + 1 / 2)) ≤
              π * ((m : ℝ) - 1 / 4) ∧
            π * ((m : ℝ) - 1 / 4) ≤ bkPhase 1 0 (-1) (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (((k : ℝ) + 1) * (1 / ((N : ℝ) + 1 / 2))) / (1 / ((N : ℝ) + 1 / 2)) +
              C0 * (1 / ((N : ℝ) + 1 / 2)) := by
  have hx : |(x : ℝ)| < 1 := abs_lt.2 ⟨by exact_mod_cast hx1, by have h0 : (x : ℝ) < 0 := (by exact_mod_cast hx0); linarith⟩
  intro a b ha hab hbq
  obtain ⟨ε, C0, hε, hC0, H⟩ := bk_hahn_half_zeros M σ x (-1) (fun j => (-1 : ℝ) ^ j) (Or.inr ⟨rfl, by exact_mod_cast hx0⟩) hx bkh_neg_sq (bkh_rows_half_neg M σ x) a b ha hab hbq
  exact ⟨ε, C0, hε, hC0, fun N n hnode hNε k hk1 hk2 hch => H N n _ hnode rfl hNε k hk1 hk2 hch⟩

/-- info: 'FormalResearch.Special.hahn_chain_bulk_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_zeros

/-- info: 'FormalResearch.Special.hahn_chain_bulk_zeros_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_zeros_neg

/-- info: 'FormalResearch.Special.hahn_chain_bulk_zeros_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_zeros_half

/-- info: 'FormalResearch.Special.hahn_chain_bulk_zeros_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn_chain_bulk_zeros_half_neg

end FormalResearch.Special

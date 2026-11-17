module

public import FormalResearch.Special.DiscreteAiryLimitHyperDecay
public import FormalResearch.Special.BulkIndexZero

/-!
# Bulk index, part 5: no nodes beyond the turning point (sign constancy of the recessive tail)

Step (b) of the right-end count.  The `3j` chain at a node `x_n` is exactly hyperbolic beyond the turn
(`A_k + A_{k+1} ≤ c_k`, `exact_hyperbolicity_hahn_racah`) and satisfies the hard-edge row `A_N = 0`; the backward ratio argument
(`backward_ratio`, `Racah/P3JacobiComparison`) then gives not only the monotone decay `|Y_{k+1}| ≤ |Y_k|` of `hr_hardedge_decay`
but the **constancy of sign**.

* `bix_tail_sign`: abstract (closed-form Hahn/Racah rows, as `hr_hardedge_decay`): if `Y_{k_max} ≠ 0` then `0 < Y_k Y_{k_max}` for
  `k₁ ≤ k ≤ k_max` (`q_* ≤ (k₁+½)h`, `2 M h ≤ q_*`, `h (ρ₁+ρ₂) ≤ 2κ q_*`).
* `bix_hahn_tail`: for the integer `3j` chain (`kmin ≥ 1`, `N = kmin + m + 1`, `x = x_n`) there is `ε > 0` such that for `h ≤ ε` and every
  site `kmin + i₁` with `q_* ≤ q`, the bonds `i₁, …, m-1` carry no node: `∑_{j=i₁}^{m-1} bix_c u j = 0` (all `Ŷ_j`, `j ≥ kmin + i₁`, are nonzero of one sign).
* `bix_rightcount_of_window`: hence the node count of the bonds `i_R, …, m-1` equals that of `i_R, …, i₁ - 1` for any `i_R ≤ i₁`, `q_{i₁} ≥ q_*`, and `BixRightCount` follows from the Airy-window count (NOT proved).

**Claim class: proved.**  The nonvanishing `Ŷ_{N-1} ≠ 0` is derived (not assumed) from the zero propagation `hd_zero_backward` and
`cho_vec_ne_zero`.  Numerics: in 8 mpmath chains (see `BulkIndexHahn`) there is no sign change at any bond with `q_k ≥ q_*`.
**Not formalised:** `τ = -1`, half-integer lattice, Racah chains.  The node count of the region between the bulk and `q_*` (the Airy window) is
not part of this module.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- **Sign constancy of the recessive tail** (closed-form Hahn / centred Racah rows; same hypotheses as `hr_hardedge_decay`, with
`Y_{k_max} ≠ 0`): `0 < Y_k Y_{k_max}` for `k₁ ≤ k ≤ k_max`. -/
theorem bix_tail_sign {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs h : ℝ) (hqs : 0 < qs)
    (hh : 0 < h) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hhM : h * (2 * hrM a b) ≤ qs)
    (hhC : h * hrRho P Q a b qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (kmax k1 : ℕ) (hedge : (((kmax : ℝ) + 1) * h) ^ 2 ∈ Dom P Q)
    (hedge0 : etilde P Q ((((kmax : ℝ) + 1) * h) ^ 2) = 0)
    (hk1 : qs ≤ ((k1 : ℝ) + 1 / 2) * h) (hk1k : k1 ≤ kmax) (Y : ℤ → ℝ)
    (hY : ∀ k ∈ Finset.Icc ((k1 : ℤ) + 1) (kmax : ℤ),
      jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) (hYN : Y (kmax : ℤ) ≠ 0) :
    ∀ k : ℕ, k1 ≤ k → k ≤ kmax → 0 < Y (k : ℤ) * Y (kmax : ℤ) := by
  rcases hk1k.eq_or_lt with hEq | hlt
  · intro k hk1' hk2
    have : k = kmax := by omega
    subst this
    exact mul_self_pos.2 hYN
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMa : |a| ≤ hrM a b := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : |b| ≤ hrM a b := (le_max_right _ _).trans (le_max_right _ _)
  -- the facts at every row site `i ∈ [k₁+1, k_max]`
  have hfacts : ∀ i : ℕ, k1 + 1 ≤ i → 1 ≤ (i : ℝ) ∧ a ^ 2 < (i : ℝ) ^ 2 ∧ b ^ 2 < (i : ℝ) ^ 2 ∧
      qs + h ≤ ((i : ℝ) + 1 / 2) * h := by
    intro i hi
    have hik : ((k1 : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hi
    have hqh : qs + h ≤ ((i : ℝ) + 1 / 2) * h := by
      nlinarith [mul_le_mul_of_nonneg_right hik hh.le]
    have h2M : 2 * hrM a b ≤ (i : ℝ) + 1 / 2 := by
      have : 2 * hrM a b * h ≤ ((i : ℝ) + 1 / 2) * h := by nlinarith
      exact le_of_mul_le_mul_right this hh
    have hiM : hrM a b < (i : ℝ) := by linarith
    refine ⟨by linarith, ?_, ?_, hqh⟩
    · have : |a| < (i : ℝ) := lt_of_le_of_lt hMa hiM
      have := pow_lt_pow_left₀ this (abs_nonneg a) two_ne_zero
      rwa [sq_abs] at this
    · have : |b| < (i : ℝ) := lt_of_le_of_lt hMb hiM
      have := pow_lt_pow_left₀ this (abs_nonneg b) two_ne_zero
      rwa [sq_abs] at this
  have hA : ∀ i, k1 + 1 ≤ i → i ≤ kmax → 0 < (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, -⟩ := hfacts i hi1
    exact hr_Ak_pos hP hQ hh hi2 f1 f2 f3 hedge
  have hend : (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (kmax + 1) = 0 := by
    show hrAk P Q a b h (((kmax + 1 : ℕ) : ℤ)) = 0
    unfold hrAk
    push_cast
    rw [hedge0]; simp
  have hsup : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (i + 1) + (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i ≤
        (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, f4⟩ := hfacts i hi1
    have hik' : (i : ℝ) ≤ kmax := Nat.cast_le.2 hi2
    have hD : (((i : ℝ) + 1) * h) ^ 2 ∈ Dom P Q :=
      Dom_mono hP hQ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hh.le) 2) hedge
    have hkq : qs ≤ 2 * (i : ℝ) * h := by nlinarith
    have hK : 0 ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hκ.le (sq_nonneg _))) hqs.le
    have hgap : hrRho P Q a b qs * h ^ 2 ≤
        2 * ((1 - τ * x) / qs ^ 2) * qs * (((i : ℝ) + 1 / 2) * h - qs) := by
      calc hrRho P Q a b qs * h ^ 2 = (h * hrRho P Q a b qs) * h := by ring
        _ ≤ (2 * ((1 - τ * x) / qs ^ 2) * qs) * h := mul_le_mul_of_nonneg_right hhC hh.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
    have := exact_hyperbolicity_hahn_racah hP hQ a b τ x qs h (i : ℝ) hh hqs hτ hκ hturn f1
      f2.le f3.le hkq hD hgap
    simp only [hrAk, hrCk]
    push_cast
    linarith
  have hrow : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAk P Q a b h (n : ℤ)) (i + 1) * (fun n : ℕ => Y (n : ℤ)) (i + 1) +
        (fun n : ℕ => hrAk P Q a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) (i - 1) =
      (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) i := by
    intro i hi1 hi2
    have h0 := hY (i : ℤ) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    unfold jac at h0
    show hrAk P Q a b h ((i + 1 : ℕ) : ℤ) * Y ((i + 1 : ℕ) : ℤ) +
      hrAk P Q a b h (i : ℤ) * Y ((i - 1 : ℕ) : ℤ) = hrCk P Q τ x a b h (i : ℤ) * Y (i : ℤ)
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring,
      show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega]
    linarith
  have H := backward_ratio (fun n : ℕ => hrAk P Q a b h (n : ℤ))
    (fun n : ℕ => hrCk P Q τ x a b h (n : ℤ)) (fun n : ℕ => Y (n : ℤ)) (k1 + 1) kmax 1 one_pos (by omega)
    (by omega) hA hend (fun i h1 h2 => by simpa using hsup i h1 h2) hrow (by simpa using hYN)
  intro k hk1' hk2
  have := (H k (by omega) (by omega)).1
  simpa using this

/-- The last site of the `3j` chain is nonzero: otherwise the zero propagation from the hard edge kills the whole chain vector. -/
theorem bix_last_ne_zero (M σ : ℤ) (x : ℚ) {m n : ℕ} (hlo : 1 ≤ max |M| |σ|) (hnm : n ≤ m)
    (hxn : xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x) :
    hahn3jY M σ (max |M| |σ| + (m : ℤ) + 1) x (max |M| |σ| + (m : ℤ)) ≠ 0 := by
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hNdef
  intro h0
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hY := cho_vec_ne_zero (M := M) (σ := σ) (N := N) hlo (m := m) hNdef (n := n) hnm
  rw [hxn] at hY
  apply hY
  have key := hd_zero_backward (fun i : ℕ => hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + (i : ℤ)))
    (fun i : ℕ => hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + (i : ℤ)))
    (fun i : ℕ => hahn3jY M σ N x (max |M| |σ| + (i : ℤ))) 1 m le_rfl
    (by
      intro i hi1 hi2
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := cho_aJ_pos (M := M) (σ := σ) (N := N) hlo (m := m) hNdef (i := i') (by omega)
      unfold cho_aJ at this
      simpa [add_assoc] using this)
    (by
      show hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + ((m + 1 : ℕ) : ℤ)) = 0
      unfold hrAk
      have e : ((max |M| |σ| + ((m + 1 : ℕ) : ℤ) : ℤ) : ℝ) = (N : ℝ) := by
        rw [hNdef]; push_cast; ring
      rw [e]
      have : ((N : ℝ) * (1 / (N : ℝ))) ^ 2 = 1 := by field_simp
      rw [this, etilde_hahn]; simp)
    (by
      intro i hi1 hi2
      have hk := bkh_rows_int_pos M σ x N hNpos (max |M| |σ| + (i : ℤ)) (by omega)
      unfold jac at hk
      have e1 : max |M| |σ| + (i : ℤ) + 1 = max |M| |σ| + ((i + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : max |M| |σ| + (i : ℤ) - 1 = max |M| |σ| + ((i - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hi1]; push_cast; ring
      rw [e1, e2] at hk
      simp only [one_mul] at hk
      show hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + ((i + 1 : ℕ) : ℤ)) *
          hahn3jY M σ N x (max |M| |σ| + ((i + 1 : ℕ) : ℤ)) +
        hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + (i : ℤ)) * hahn3jY M σ N x (max |M| |σ| + ((i - 1 : ℕ) : ℤ)) =
        hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + (i : ℤ)) * hahn3jY M σ N x (max |M| |σ| + (i : ℤ))
      linarith)
    h0
  funext i
  have := key (i : ℕ) (by omega) (by have := i.2; omega)
  simpa [cho_vec] using this

/-- **No nodes beyond the turning point.**  For the integer `3j` chain at a lattice node there is `ε > 0` such that for `h ≤ ε` and every
site `kmin + i₁` with `q_* ≤ q`, the bonds `i₁, …, m - 1` carry no node (all `Ŷ_j`, `j ≥ kmin + i₁`, are nonzero of one sign). -/
theorem bix_hahn_tail (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m →
      xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
      1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i₁ : ℕ,
        √(1 - (x : ℝ) ^ 2) ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i₁ : ℤ)) →
        ∑ j ∈ Ico i₁ m, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j = 0 := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : |(x : ℝ)| < 1 := abs_lt.2 ⟨by linarith, by exact_mod_cast hx1⟩
  obtain ⟨hqs, hτ, hκ, hα, hβ, hturn⟩ := bkh_geom (τ := 1) (x := (x : ℝ)) (Or.inl ⟨rfl, hx0'⟩) hx1'
  set qs : ℝ := √(1 - (x : ℝ) ^ 2) with hqsdef
  have hM0 : 0 < hrM (M : ℝ) (σ : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρ0 : 0 ≤ hrRho 1 0 (M : ℝ) (σ : ℝ) qs := by unfold hrRho; positivity
  have hK : 0 < 2 * ((1 - 1 * (x : ℝ)) / qs ^ 2) * qs := by positivity
  refine ⟨min (qs / (2 * hrM (M : ℝ) (σ : ℝ))) ((2 * ((1 - 1 * (x : ℝ)) / qs ^ 2) * qs) / (hrRho 1 0 (M : ℝ) (σ : ℝ) qs + 1)),
    lt_min (by positivity) (by positivity), ?_⟩
  intro m n hlo hnm hxn hNε i₁ hi₁
  set N : ℤ := max |M| |σ| + (m : ℤ) + 1 with hNdef
  have hkpos : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hh : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  by_cases hmi : m ≤ i₁
  · simp [Finset.Ico_eq_empty_of_le hmi]
  push Not at hmi
  obtain ⟨κ0, hκ0⟩ : ∃ κ0 : ℕ, (κ0 : ℤ) = max |M| |σ| := ⟨(max |M| |σ|).toNat, Int.toNat_of_nonneg hkpos⟩
  have hNk : ((κ0 + m : ℕ) : ℝ) + 1 = (N : ℝ) := by
    have : ((κ0 + m : ℕ) : ℤ) + 1 = N := by rw [hNdef]; push_cast; omega
    have h2 : (((κ0 + m : ℕ) : ℤ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast this
    simpa using h2
  have hNk1 : (((κ0 + m : ℕ) : ℝ) + 1) * (1 / (N : ℝ)) = 1 := by rw [hNk]; field_simp
  have hedge : ((((κ0 + m : ℕ) : ℝ) + 1) * (1 / (N : ℝ))) ^ 2 ∈ Dom 1 0 := by
    rw [hNk1]; exact ⟨by norm_num, by norm_num, by norm_num⟩
  have hedge0 : etilde 1 0 (((((κ0 + m : ℕ) : ℝ) + 1) * (1 / (N : ℝ))) ^ 2) = 0 := by
    rw [hNk1, etilde_hahn]; simp
  have hεM : 1 / (N : ℝ) ≤ qs / (2 * hrM (M : ℝ) (σ : ℝ)) := hNε.trans (min_le_left _ _)
  have hεC : 1 / (N : ℝ) ≤ (2 * ((1 - 1 * (x : ℝ)) / qs ^ 2) * qs) / (hrRho 1 0 (M : ℝ) (σ : ℝ) qs + 1) :=
    hNε.trans (min_le_right _ _)
  have hhM : 1 / (N : ℝ) * (2 * hrM (M : ℝ) (σ : ℝ)) ≤ qs := by
    rwa [le_div_iff₀ (by positivity)] at hεM
  have hhC : 1 / (N : ℝ) * hrRho 1 0 (M : ℝ) (σ : ℝ) qs ≤ 2 * ((1 - 1 * (x : ℝ)) / qs ^ 2) * qs := by
    rw [le_div_iff₀ (by positivity)] at hεC
    nlinarith
  have hk1 : qs ≤ (((κ0 + i₁ : ℕ) : ℝ) + 1 / 2) * (1 / (N : ℝ)) := by
    have : (((κ0 + i₁ : ℕ) : ℝ)) = ((max |M| |σ| + (i₁ : ℤ) : ℤ) : ℝ) := by
      rw [← hκ0]; push_cast; ring
    rw [this]; exact hi₁
  have hrows : ∀ k ∈ Finset.Icc (((κ0 + i₁ : ℕ) : ℤ) + 1) ((κ0 + m : ℕ) : ℤ),
      jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
        (hahn3jY M σ N x) k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact hahn_class_chain M σ N x hNpos k (by omega)
  have hYN : hahn3jY M σ N x ((κ0 + m : ℕ) : ℤ) ≠ 0 := by
    have := bix_last_ne_zero M σ x hlo hnm hxn
    have e : ((κ0 + m : ℕ) : ℤ) = max |M| |σ| + (m : ℤ) := by push_cast; omega
    rw [e]; exact this
  have H := bix_tail_sign (P := 1) (Q := 0) zero_le_one le_rfl (M : ℝ) (σ : ℝ) 1 (x : ℝ) qs (1 / (N : ℝ)) hqs hh hτ hκ hturn
    hhM hhC (κ0 + m) (κ0 + i₁) hedge hedge0 hk1 (by omega) (hahn3jY M σ N x) hrows hYN
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  have p1 := H (κ0 + j) (by omega) (by omega)
  have p2 := H (κ0 + (j + 1)) (by omega) (by omega)
  have e1 : ((κ0 + j : ℕ) : ℤ) = max |M| |σ| + (j : ℤ) := by push_cast; omega
  have e2 : ((κ0 + (j + 1) : ℕ) : ℤ) = max |M| |σ| + ((j + 1 : ℕ) : ℤ) := by push_cast; omega
  rw [e1] at p1
  rw [e2] at p2
  have hne : hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) ≠ 0 := by
    intro h; rw [h] at p1; simp at p1
  have hpos : 0 < hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) * hahn3jY M σ N x (max |M| |σ| + ((j + 1 : ℕ) : ℤ)) := by
    have := mul_pos p1 p2
    have h2 : 0 < hahn3jY M σ N x ((κ0 + m : ℕ) : ℤ) ^ 2 := by positivity
    have e : (hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) * hahn3jY M σ N x ((κ0 + m : ℕ) : ℤ)) *
        (hahn3jY M σ N x (max |M| |σ| + ((j + 1 : ℕ) : ℤ)) * hahn3jY M σ N x ((κ0 + m : ℕ) : ℤ)) =
        (hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) * hahn3jY M σ N x (max |M| |σ| + ((j + 1 : ℕ) : ℤ))) *
          hahn3jY M σ N x ((κ0 + m : ℕ) : ℤ) ^ 2 := by ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_right h2).1 this
  unfold bix_c bixU
  have h0 : ¬ (hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) * hahn3jY M σ N x (max |M| |σ| + ((j + 1 : ℕ) : ℤ)) < 0) :=
    not_lt.2 hpos.le
  have h1 : ¬ (0 < j ∧ hahn3jY M σ N x (max |M| |σ| + (j : ℤ)) = 0) := fun h => hne h.2
  simp only [h0, h1, ↓reduceIte]
  rfl

/-- info: 'FormalResearch.Special.bix_hahn_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_hahn_tail

/-- info: 'FormalResearch.Special.bix_tail_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_tail_sign

/-- info: 'FormalResearch.Special.bix_last_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_last_ne_zero

/-- **Reduction of the right-end count to the Airy window.**  With `ε` of `bix_hahn_tail`: if the bonds `i_R, …, i₁ - 1` (up to a site `i₁ ≤ m` with
`q_{i₁} ≥ q_*`) carry `⌊Φ(q_{i_R})/(π h) + 1/4⌋` nodes, then `BixRightCount` holds at `i_R`.  The hypothesis is the node count of the Airy window,
not proved here. -/
theorem bix_rightcount_of_window (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m n : ℕ), 1 ≤ max |M| |σ| → n ≤ m →
      xLat (M : ℚ) (σ : ℚ) ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℚ) n = x →
      1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ) ≤ ε → ∀ i₁ iR : ℕ, iR ≤ i₁ → i₁ ≤ m →
        √(1 - (x : ℝ) ^ 2) ≤ bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (i₁ : ℤ)) →
        ((∑ j ∈ Ico iR i₁, bix_c (bixU M σ (max |M| |σ| + (m : ℤ) + 1) x) j : ℕ) : ℤ) =
          ⌊bkPhase 1 0 1 (x : ℝ) (√(1 - (x : ℝ) ^ 2)) (bixQ (max |M| |σ| + (m : ℤ) + 1) (max |M| |σ| + (iR : ℤ))) /
            (π * (1 / ((max |M| |σ| + (m : ℤ) + 1 : ℤ) : ℝ))) + 1 / 4⌋ →
        BixRightCount M σ (max |M| |σ| + (m : ℤ) + 1) x iR m := by
  obtain ⟨ε, hε, H⟩ := bix_hahn_tail M σ x hx0 hx1
  refine ⟨ε, hε, ?_⟩
  intro m n hlo hnm hxn hNε i₁ iR hle him hq hcnt
  have h0 := H m n hlo hnm hxn hNε i₁ hq
  unfold BixRightCount
  rw [← hcnt, ← Finset.sum_Ico_consecutive _ hle him, h0]
  simp

/-- info: 'FormalResearch.Special.bix_rightcount_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bix_rightcount_of_window

end FormalResearch.Special

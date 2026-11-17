module

public import FormalResearch.Special.HermiteKappaEdge

/-!
# Lattice bookkeeping for the lower bound on `κ`

From the data of `HkEdge` (window `[J, N]`, turn site `m`, lattice gaps `c₁δ ≤ X_{k+1} - X_k ≤ c₂δ`) this module locates the site
`k₀ = m - L`, `L = ⌈100/δ⌉`, at which the Hermite index `n = -k₀` sits at the edge of the `x`-bulk (`hk_sites`):

* `x² + 2L - 2 < 2n + 1 ≤ x² + 2L` (so `d = 2n+1 - x² ∈ (200/δ - 2, 200/δ + 2]`, comparable to `100 (2n+1)^{1/3}`),
* `-102 c₂ ≤ X_{k₀-1} ≤ X_{k₀} ≤ X_{k₀+1} ≤ 0`, `X_{k₀+1} - X_{k₀-1} ≤ 2 c₂ δ`,
* `J ≤ k₀ - 1`, `k₀ + 1 ≤ m`.

**Claim class: proved** (elementary lattice arithmetic).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma hk_tele {X : ℤ → ℝ} {J N : ℤ} {lo hi : ℝ}
    (h : ∀ k ∈ Finset.Icc J N, lo ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ hi) :
    ∀ (j : ℕ) (k : ℤ), J ≤ k → k + (j : ℤ) ≤ N + 1 →
      (j : ℝ) * lo ≤ X (k + j) - X k ∧ X (k + j) - X k ≤ (j : ℝ) * hi := by
  intro j
  induction j with
  | zero => intro k _ _; simp
  | succ j ih =>
    intro k hk hkj
    have h1 := ih k hk (by push_cast at hkj; omega)
    have h2 := h (k + (j : ℤ)) (by rw [Finset.mem_Icc]; push_cast at hkj; omega)
    rw [show k + ((j + 1 : ℕ) : ℤ) = k + (j : ℤ) + 1 by push_cast; ring]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma dalQ_sub_dalQ (q₀ δ : ℝ) (a b : ℤ) : dalQ q₀ δ a - dalQ q₀ δ b = ((a : ℝ) - b) * δ ^ 3 := by
  simp only [dalQ]; ring

/-- **The site `k₀ = m - L`, `L = ⌈100/δ⌉`**: see the module docstring. -/
lemma hk_sites {r c1 c2 x δ : ℝ} {J m N : ℤ} {X : ℤ → ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsm : 103 * δ ^ 2 < r) (hc1 : 0 < c1) (hcc : c2 * δ ≤ c1)
    (hδx : δ ^ 3 = 2 / x ^ 2) (hJm : J ≤ m) (hmN : m ≤ N)
    (hqJ : dalQ (-δ ^ 3 / 2) δ J < -1 - r + δ ^ 3) (hqm1 : -1 ≤ dalQ (-δ ^ 3 / 2) δ m)
    (hqm2 : dalQ (-δ ^ 3 / 2) δ m < -1 + δ ^ 3)
    (hgap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) :
    ∃ L : ℕ, 100 / δ ≤ (L : ℝ) ∧ (L : ℝ) ≤ 100 / δ + 1 ∧ J + 1 ≤ m - L - 1 ∧
      x ^ 2 + 2 * (L : ℝ) - 2 < -2 * ((m - L : ℤ) : ℝ) + 1 ∧ -2 * ((m - L : ℤ) : ℝ) + 1 ≤ x ^ 2 + 2 * (L : ℝ) ∧
      X (m - L + 1) ≤ 0 ∧ -(102 * c2) ≤ X (m - L - 1) ∧ X (m - L + 1) - X (m - L - 1) ≤ 2 * c2 * δ ∧
      X (m - L - 1) ≤ X (m - L) ∧ X (m - L) ≤ X (m - L + 1) := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hx2' : δ ^ 3 * x ^ 2 = 2 := by
    have : x ^ 2 ≠ 0 := by positivity
    rw [hδx]; field_simp
  have hc2 : 0 ≤ c2 := by
    by_contra h
    push_neg at h
    nlinarith [mul_neg_of_neg_of_pos h hδ]
  set L : ℕ := ⌈100 / δ⌉₊ with hL
  have hL1 : 100 / δ ≤ (L : ℝ) := Nat.le_ceil _
  have hL2 : (L : ℝ) < 100 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLd : (100 : ℝ) ≤ 100 / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hLδ : 100 ≤ (L : ℝ) * δ := by
    have := mul_le_mul_of_nonneg_right hL1 hδ.le
    have e : 100 / δ * δ = 100 := by field_simp
    linarith
  have hLδ2 : (L : ℝ) * δ ≤ 100 + δ := by
    have := mul_le_mul_of_nonneg_right hL2.le hδ.le
    have e : (100 / δ + 1) * δ = 100 + δ := by field_simp
    linarith
  have hL100 : (100 : ℝ) ≤ L := hLd.trans hL1
  have hL100' : (100 : ℤ) ≤ L := by exact_mod_cast hL100
  -- `J < m - L - 1`
  have hJL : J + 1 ≤ m - L - 1 := by
    by_contra hcon
    have hle : m - (L : ℤ) - 1 ≤ J := by omega
    have h1 : dalQ (-δ ^ 3 / 2) δ J - dalQ (-δ ^ 3 / 2) δ (m - L - 1) = ((J : ℝ) - ((m - L - 1 : ℤ) : ℝ)) * δ ^ 3 :=
      dalQ_sub_dalQ _ _ _ _
    have h2 : dalQ (-δ ^ 3 / 2) δ m - dalQ (-δ ^ 3 / 2) δ (m - L - 1) = ((L : ℝ) + 1) * δ ^ 3 := by
      rw [dalQ_sub_dalQ]; push_cast; ring
    have h3 : (0 : ℝ) ≤ (J : ℝ) - ((m - L - 1 : ℤ) : ℝ) := by
      have : ((m - L - 1 : ℤ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hle
      linarith
    have h4 : 0 ≤ ((J : ℝ) - ((m - L - 1 : ℤ) : ℝ)) * δ ^ 3 := mul_nonneg h3 hδ3.le
    have h5 : (L : ℝ) * δ ^ 3 ≤ 100 * δ ^ 2 + δ ^ 3 := by
      have := mul_le_mul_of_nonneg_right hLδ2 (sq_nonneg δ)
      nlinarith [this]
    have h6 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [sq_nonneg δ]
    nlinarith
  -- the Hermite index
  have hlam1 : -2 * (m : ℝ) + 1 ≤ x ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hqm1 (sq_nonneg x)
    simp only [dalQ] at h
    nlinarith [h, hx2']
  have hlam2 : x ^ 2 - 2 < -2 * (m : ℝ) + 1 := by
    have h := mul_lt_mul_of_pos_right hqm2 (by positivity : 0 < x ^ 2)
    simp only [dalQ] at h
    nlinarith [h, hx2']
  -- the `X` data
  have hT := hk_tele (X := X) (J := J) (N := N) (lo := c1 * δ) (hi := c2 * δ) hgap
  have hT1 := hT (L - 1) (m - L + 1) (by omega) (by push_cast; omega)
  have hT2 := hT (L + 1) (m - L - 1) (by omega) (by push_cast; omega)
  have hT3 := hT 2 (m - L - 1) (by omega) (by push_cast; omega)
  have e1 : m - (L : ℤ) + 1 + ((L - 1 : ℕ) : ℤ) = m := by omega
  have e2 : m - (L : ℤ) - 1 + ((L + 1 : ℕ) : ℤ) = m := by push_cast; ring
  have e3 : m - (L : ℤ) - 1 + ((2 : ℕ) : ℤ) = m - L + 1 := by push_cast; ring
  rw [e1] at hT1
  rw [e2] at hT2
  rw [e3] at hT3
  have hL1c : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hg1 := hgap (m - L - 1) (by rw [Finset.mem_Icc]; omega)
  have hg2 := hgap (m - L) (by rw [Finset.mem_Icc]; omega)
  have e4 : m - (L : ℤ) - 1 + 1 = m - L := by ring
  rw [e4] at hg1
  have hcδ1 : 0 < c1 * δ := by positivity
  refine ⟨L, hL1, hL2.le, hJL, ?_, ?_, ?_, ?_, ?_, (by linarith [hg1.1]), ?_⟩
  · push_cast; linarith
  · push_cast; linarith
  · rw [hL1c] at hT1
    have hq : c1 ≤ ((L : ℝ) - 1) * (c1 * δ) := by
      have : 0 ≤ c1 * (((L : ℝ) - 1) * δ - 1) := mul_nonneg hc1.le (by linarith)
      linarith
    linarith [hT1.1]
  · push_cast at hT2
    have hq : ((L : ℝ) + 1) * (c2 * δ) ≤ 102 * c2 := by
      have : 0 ≤ c2 * (102 - ((L : ℝ) + 1) * δ) := mul_nonneg hc2 (by linarith)
      linarith
    linarith [hT2.2]
  · push_cast at hT3
    linarith [hT3.2]
  · linarith [hg2.1]

end FormalResearch.Special

module

public import FormalResearch.SignUncertainty.HankelPhaseSeries

/-!
# The connector margin `(C)` of `gt:7.7c`

For `ζ = σ + iτ` with `0 ≤ σ ≤ 0.1`, `τ² = 1/9` and `0 < η_j ≤ 1`, `η_0 = π²/12`:
`Re g(ζ) ≤ -(π²/12)(91/900) + 1/162 + (1/3) a³/(1-a)`, `a = 109/900`, hence `Re g(ζ) < -0.0755`
(`re_gSer_conn_le`); `(C)` of the paper (`Re g + log|π²ξ| ≤ -0.07`) follows for `|π²ξ| ≤ 1 + 10⁻³`.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

section Conn

variable {η : ℕ → ℝ}

lemma gSer_eq_tsum (η : ℕ → ℝ) (ζ : ℂ) :
    gSer η ζ = ∑' j : ℕ, ((η j / ((j : ℝ) + 1) : ℝ) : ℂ) * ζ ^ (2 * j + 2) := by
  unfold gSer psW
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [show 2 * j + 2 = 2 + 2 * j by ring, pow_add, pow_mul]; ring

theorem re_gSer_conn_le (h : LangerEta η) {σ τ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 0.1) (hτ : τ ^ 2 = 1 / 9) :
    (gSer η ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ -0.0755 := by
  set ζ : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hζ
  set a : ℝ := ‖ζ‖ ^ 2 with ha
  have hnsq : a = σ ^ 2 + τ ^ 2 := by
    rw [ha, ← Complex.normSq_eq_norm_sq, hζ, Complex.normSq_apply]; simp; ring
  have haB : a ≤ 109 / 900 := by rw [hnsq, hτ]; nlinarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by linarith
  have hn1 : ‖ζ‖ < 1 := by by_contra hc; push Not at hc; nlinarith [norm_nonneg ζ]
  set T : ℕ → ℂ := fun j => ((η j / ((j : ℝ) + 1) : ℝ) : ℂ) * ζ ^ (2 * j + 2) with hT
  have hTn : ∀ j, ‖T j‖ ≤ a ^ (j + 1) := by
    intro j
    rw [hT]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    have := abs_eta_div_le h j
    calc |η j / ((j : ℝ) + 1)| * ‖ζ‖ ^ (2 * j + 2) ≤ 1 * ‖ζ‖ ^ (2 * j + 2) := by gcongr
      _ = a ^ (j + 1) := by rw [ha, ← pow_mul, one_mul]; ring_nf
  have hsum : Summable (fun j => ‖T j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hTn
      (((summable_geometric_of_lt_one ha0 ha1).mul_left a).congr fun j => by ring)
  rw [gSer_eq_tsum]
  have hre := Complex.reCLM.map_tsum hsum.of_norm
  simp only [Complex.reCLM_apply] at hre
  change (∑' j, T j).re ≤ _
  rw [hre]
  have hRs : Summable (fun j => (T j).re) :=
    Summable.of_norm_bounded
      (((summable_geometric_of_lt_one ha0 ha1).mul_left a).congr fun j => by ring)
      (fun j => (Complex.abs_re_le_norm _).trans (hTn j))
  rw [hRs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hRs).tsum_eq_zero_add]
  -- j = 0 term
  have hb0 : η 0 / (((0 : ℕ) : ℝ) + 1) = π ^ 2 / 12 := by simp [h.zero]
  have hre2 : (ζ ^ 2).re = σ ^ 2 - τ ^ 2 := by
    rw [hζ, sq, Complex.mul_re]; simp; ring
  have hT0 : (T 0).re = π ^ 2 / 12 * (σ ^ 2 - τ ^ 2) := by
    rw [hT]; simp only []
    rw [Complex.re_ofReal_mul, hb0]; simp [hre2]
  -- j = 1 term
  have hre4 : (ζ ^ 4).re ≤ 1 / 81 := by
    have : ζ ^ 4 = (ζ ^ 2) ^ 2 := by ring
    rw [this, sq, Complex.mul_re]
    have him : (ζ ^ 2).im = 2 * σ * τ := by rw [hζ, sq, Complex.mul_im]; simp; ring
    rw [hre2, him]
    nlinarith [sq_nonneg (σ * τ), sq_nonneg σ, hτ]
  have hT1 : (T 1).re ≤ 1 / 162 := by
    rw [hT]; simp only []
    rw [Complex.re_ofReal_mul]
    have hb1 : η 1 / (((1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
      have := h.le_one 1
      rw [div_le_iff₀ (by norm_num)]; norm_num; linarith
    have hb1p : 0 < η 1 / (((1 : ℕ) : ℝ) + 1) := div_pos (h.pos 1) (by norm_num)
    have h4 : (ζ ^ (2 * 1 + 2)).re ≤ 1 / 81 := by simpa using hre4
    rcases le_or_gt 0 (ζ ^ (2 * 1 + 2)).re with hpos | hneg
    · calc η 1 / (((1 : ℕ) : ℝ) + 1) * (ζ ^ (2 * 1 + 2)).re ≤ (1 / 2) * (1 / 81) := by
            exact mul_le_mul hb1 h4 hpos (by norm_num)
        _ = 1 / 162 := by norm_num
    · have : η 1 / (((1 : ℕ) : ℝ) + 1) * (ζ ^ (2 * 1 + 2)).re ≤ 0 := by nlinarith
      linarith
  -- tail j ≥ 2
  have htail : |∑' j : ℕ, (T (j + 1 + 1)).re| ≤ (1 / 3) * (a ^ 3 / (1 - a)) := by
    have hs3 : HasSum (fun j : ℕ => (1 / 3 : ℝ) * (a ^ 3 * a ^ j)) ((1 / 3) * (a ^ 3 * (1 - a)⁻¹)) :=
      ((hasSum_geometric_of_lt_one ha0 ha1).mul_left (a ^ 3)).mul_left (1 / 3)
    have hb : ∀ j : ℕ, ‖(T (j + 1 + 1)).re‖ ≤ (1 / 3 : ℝ) * (a ^ 3 * a ^ j) := by
      intro j
      rw [Real.norm_eq_abs]
      have hco : η (j + 1 + 1) / (((j + 1 + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
        have := h.le_one (j + 1 + 1)
        rw [div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        push_cast; nlinarith
      have hn : ‖T (j + 1 + 1)‖ ≤ (1 / 3 : ℝ) * a ^ (j + 1 + 1 + 1) := by
        rw [hT]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
        rw [abs_of_pos (div_pos (h.pos _) (by positivity))]
        calc η (j + 1 + 1) / (((j + 1 + 1 : ℕ) : ℝ) + 1) * ‖ζ‖ ^ (2 * (j + 1 + 1) + 2)
            ≤ (1 / 3) * ‖ζ‖ ^ (2 * (j + 1 + 1) + 2) := by gcongr
          _ = (1 / 3) * a ^ (j + 1 + 1 + 1) := by rw [ha, ← pow_mul]; ring_nf
      exact (Complex.abs_re_le_norm _).trans (hn.trans (le_of_eq (by ring)))
    have := tsum_of_norm_bounded hs3 hb
    rw [← Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  have hab := abs_le.1 htail
  rw [hT0]
  have hpi : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hτ' : τ ^ 2 = 1 / 9 := hτ
  have h1 : π ^ 2 / 12 * (σ ^ 2 - τ ^ 2) ≤ π ^ 2 / 12 * (-91 / 900) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have h2 : (1 / 3) * (a ^ 3 / (1 - a)) ≤ (1 / 3) * ((109 / 900) ^ 3 / (1 - 109 / 900)) := by
    gcongr
  have h3 : (1 / 3 : ℝ) * ((109 / 900) ^ 3 / (1 - 109 / 900)) ≤ 0.0007 := by norm_num
  nlinarith

end Conn

/-- info: 'FormalResearch.SignUncertainty.re_gSer_conn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_gSer_conn_le

end FormalResearch.SignUncertainty

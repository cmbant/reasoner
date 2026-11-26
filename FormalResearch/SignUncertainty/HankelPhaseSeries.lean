module

public import FormalResearch.SignUncertainty.HankelLangerChart

/-!
# The strip function `g` as a power series and its curvature `Re g'` (`gt:7.7c` (b), inequality `(V)`)

`g(ζ) = ∑ η_j/(j+1) ζ^{2j+2}` (`gSer`, `gt:7.7b` (0)); `g'(ζ) = 2 ζ ∑ η_j ζ^{2j}`.  For `0 < σ ≤ 0.04`, `|τ| ≤ 1/3`
we prove `Re g'(σ+iτ) ≥ (4/5) σ` (`re_gSerD_ge`), a slightly weaker constant than the paper's `π²/12` (inequality
`(V)`, proved there by Leibniz' bound on the partial fractions); only positivity of the constant is used downstream.
The proof uses `|Re ζ^{2j+1}| ≤ (2j+1) σ |ζ|^{2j}` (the power `(iτ)^{2j+1}` is purely imaginary) and `0 < η_j ≤ 1`.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `‖z^n - w^n‖ ≤ n R^{n-1} ‖z - w‖` when `‖z‖, ‖w‖ ≤ R`. -/
lemma hankel_norm_pow_sub_pow_le {z w : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ n * R ^ (n - 1) * ‖z - w‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have egs := geom_sum₂_mul z w n
  rw [← egs, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (z - w))
  refine (norm_sum_le (Finset.range n) (fun i => z ^ i * w ^ (n - 1 - i))).trans ?_
  calc ∑ i ∈ Finset.range n, ‖z ^ i * w ^ (n - 1 - i)‖ ≤ ∑ i ∈ Finset.range n, R ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow, norm_pow]
        have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
        calc ‖z‖ ^ i * ‖w‖ ^ (n - 1 - i) ≤ R ^ i * R ^ (n - 1 - i) := by gcongr
          _ = R ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    _ = n * R ^ (n - 1) := by simp

/-- `|Re ζ^{2j+1}| ≤ (2j+1) σ ‖ζ‖^{2j}` for `ζ = σ + iτ`, `σ ≥ 0`. -/
lemma abs_re_pow_odd_le {σ τ : ℝ} (hσ : 0 ≤ σ) (j : ℕ) :
    |(((σ : ℂ) + (τ : ℂ) * Complex.I) ^ (2 * j + 1)).re| ≤
      (2 * j + 1) * ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ (2 * j) * σ := by
  set ζ : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hsq : ((τ : ℂ) * Complex.I) ^ 2 = ((-(τ ^ 2) : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  have hre : (((τ : ℂ) * Complex.I) ^ (2 * j + 1)).re = 0 := by
    have e : ((τ : ℂ) * Complex.I) ^ (2 * j + 1) = Complex.I * ((τ * (-(τ ^ 2)) ^ j : ℝ) : ℂ) := by
      rw [pow_succ, pow_mul, hsq]; push_cast; ring
    rw [e]; simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]; ring
  have hdiff : ‖ζ ^ (2 * j + 1) - ((τ : ℂ) * Complex.I) ^ (2 * j + 1)‖ ≤
      (2 * j + 1 : ℕ) * ‖ζ‖ ^ (2 * j) * σ := by
    have hz : ‖ζ‖ ≤ ‖ζ‖ := le_rfl
    have hw : ‖(τ : ℂ) * Complex.I‖ ≤ ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, hζ]
      have : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + τ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      nlinarith [sq_nonneg σ, sq_abs τ, norm_nonneg ((σ : ℂ) + (τ : ℂ) * Complex.I), abs_nonneg τ]
    have := hankel_norm_pow_sub_pow_le hz hw (2 * j + 1)
    have hsub : ζ - (τ : ℂ) * Complex.I = (σ : ℂ) := by rw [hζ]; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ] at this
    simpa using this
  have : (ζ ^ (2 * j + 1)).re = (ζ ^ (2 * j + 1) - ((τ : ℂ) * Complex.I) ^ (2 * j + 1)).re := by
    simp [hre]
  rw [this]
  refine (Complex.abs_re_le_norm _).trans ?_
  have := hdiff
  push_cast at this
  exact this

section GSer

variable {η : ℕ → ℝ}

/-- `g(ζ) = ∑ η_j/(j+1) ζ^{2j+2}`. -/
noncomputable def gSer (η : ℕ → ℝ) (ζ : ℂ) : ℂ :=
  ζ ^ 2 * psW (fun j => η j / ((j : ℝ) + 1)) (ζ ^ 2)

/-- `g'(ζ) = 2 ζ ∑ η_j ζ^{2j}`. -/
noncomputable def gSerD (η : ℕ → ℝ) (ζ : ℂ) : ℂ := 2 * ζ * psW η (ζ ^ 2)

lemma abs_eta_div_le (h : LangerEta η) (j : ℕ) : |η j / ((j : ℝ) + 1)| ≤ 1 := by
  rw [abs_of_pos (div_pos (h.pos j) (by positivity))]
  rw [div_le_one (by positivity)]
  have := h.le_one j
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma abs_eta_le (h : LangerEta η) (j : ℕ) : |η j| ≤ 1 := by
  rw [abs_of_pos (h.pos j)]; exact h.le_one j

lemma psW_add_mul_psWD (h : LangerEta η) {u : ℂ} (hu : ‖u‖ < 1) :
    psW (fun j => η j / ((j : ℝ) + 1)) u + u * psWD (fun j => η j / ((j : ℝ) + 1)) u = psW η u := by
  set b : ℕ → ℝ := fun j => η j / ((j : ℝ) + 1) with hb
  have s1 := summable_psW (a := b) (B := 1) (abs_eta_div_le h) hu
  have s2 := summable_psW (a := η) (B := 1) (abs_eta_le h) hu
  have hP : psW b u = (b 0 : ℂ) + ∑' j : ℕ, (b (j + 1) : ℂ) * u ^ (j + 1) := by
    unfold psW
    rw [(s1.of_norm).tsum_eq_zero_add]; simp
  have hE : psW η u = (η 0 : ℂ) + ∑' j : ℕ, (η (j + 1) : ℂ) * u ^ (j + 1) := by
    unfold psW
    rw [(s2.of_norm).tsum_eq_zero_add]; simp
  have hD : u * psWD b u = ∑' j : ℕ, ((b (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1) := by
    unfold psWD
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have hs3 : Summable (fun j : ℕ => (b (j + 1) : ℂ) * u ^ (j + 1)) := by
    have := s1.of_norm
    exact (summable_nat_add_iff 1).2 this
  have hbj : ∀ j : ℕ, (b (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ) + (b (j + 1) : ℂ) = (η (j + 1) : ℂ) := by
    intro j
    simp only [hb]; push_cast
    have h2 : ((j : ℂ) + 1 + 1) ≠ 0 := by norm_cast
    have h3 : (2 + (j : ℂ)) ≠ 0 := by norm_cast; omega
    field_simp
  have hs4 : Summable (fun j : ℕ => ((b (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1)) := by
    have h5 : Summable (fun j : ℕ => (η (j + 1) : ℂ) * u ^ (j + 1)) :=
      (summable_nat_add_iff 1).2 (s2.of_norm)
    have h6 := h5.sub hs3
    refine h6.congr fun j => ?_
    rw [← hbj j]; ring
  rw [hP, hD, hE]
  have h7 : ∑' j : ℕ, ((η (j + 1) : ℂ) * u ^ (j + 1)) =
      ∑' j : ℕ, ((b (j + 1) : ℂ) * ((j + 1 : ℕ) : ℂ)) * u ^ (j + 1) +
        ∑' j : ℕ, (b (j + 1) : ℂ) * u ^ (j + 1) := by
    rw [← Summable.tsum_add hs4 hs3]
    refine tsum_congr fun j => ?_
    rw [← hbj j]; ring
  have hb0 : (b 0 : ℂ) = (η 0 : ℂ) := by simp [hb]
  rw [h7, hb0]; ring

lemma hasDerivAt_gSer (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt (gSer η) (gSerD η ζ) ζ := by
  have hu : ‖ζ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg ζ]
  have hP := hasDerivAt_psW (a := fun j => η j / ((j : ℝ) + 1)) (B := 1) (abs_eta_div_le h) hu
  have h2 : HasDerivAt (fun ζ : ℂ => ζ ^ 2) (2 * ζ) ζ := by simpa using hasDerivAt_pow 2 ζ
  have hP' : HasDerivAt (psW (fun j => η j / ((j : ℝ) + 1))) (psWD (fun j => η j / ((j : ℝ) + 1)) (ζ ^ 2))
      ((fun ζ : ℂ => ζ ^ 2) ζ) := hP
  have hc := HasDerivAt.comp (h₂ := psW (fun j => η j / ((j : ℝ) + 1))) (h := fun ζ : ℂ => ζ ^ 2) ζ hP' h2
  have hm := h2.mul hc
  have hfun : gSer η = (fun ζ : ℂ => ζ ^ 2) * (psW (fun j => η j / ((j : ℝ) + 1)) ∘ fun ζ : ℂ => ζ ^ 2) := by
    funext x; simp [gSer]
  rw [hfun]
  convert hm using 1
  have := psW_add_mul_psWD h hu
  unfold gSerD
  simp only [Function.comp_apply]
  rw [← this]; ring

lemma hasSum_odd_weight {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun j : ℕ => (2 * (j : ℝ) + 3) * a ^ j) (2 * a / (1 - a) ^ 2 + 3 / (1 - a)) := by
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := a)
    (by rwa [Real.norm_eq_abs, abs_of_nonneg ha0])).mul_left 2
  have h2 := (hasSum_geometric_of_lt_one ha0 ha1).mul_left 3
  have := h1.add h2
  convert this using 1
  · ext j; ring
  · have : (1 - a) ≠ 0 := by linarith
    field_simp

/-- `Re g'(σ + iτ) ≥ (4/5) σ` for `0 < σ ≤ 0.04`, `|τ| ≤ 1/3`. -/
theorem re_gSerD_ge (h : LangerEta η) {σ τ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 0.04) (hτ : |τ| ≤ 1 / 3) :
    (4 / 5) * σ ≤ (gSerD η ((σ : ℂ) + (τ : ℂ) * Complex.I)).re := by
  set ζ : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hζ
  set a : ℝ := ‖ζ‖ ^ 2 with ha
  have hnsq : a = σ ^ 2 + τ ^ 2 := by
    rw [ha, ← Complex.normSq_eq_norm_sq, hζ, Complex.normSq_apply]; simp; ring
  have hτ2 : τ ^ 2 ≤ 1 / 9 := by nlinarith [abs_nonneg τ, sq_abs τ]
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haB : a ≤ 0.1128 := by rw [hnsq]; nlinarith
  have ha1 : a < 1 := by linarith
  have hnorm1 : ‖ζ‖ < 1 := by
    by_contra hc; push Not at hc; nlinarith [norm_nonneg ζ]
  -- terms
  set Z : ℕ → ℂ := fun j => (η j : ℂ) * ζ ^ (2 * j + 1) with hZ
  have hZn : ∀ j, ‖Z j‖ ≤ ‖ζ‖ * a ^ j := by
    intro j
    rw [hZ]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    have := abs_eta_le h j
    calc |η j| * ‖ζ‖ ^ (2 * j + 1) ≤ 1 * ‖ζ‖ ^ (2 * j + 1) := by gcongr
      _ = ‖ζ‖ * a ^ j := by rw [ha, ← pow_mul, one_mul, pow_succ]; ring
  have hZs : Summable (fun j => ‖Z j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hZn
      ((summable_geometric_of_lt_one ha0 ha1).mul_left ‖ζ‖)
  have hg : gSerD η ζ = 2 * ∑' j, Z j := by
    unfold gSerD psW
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hZ]; simp only []; ring_nf
  have hre : (gSerD η ζ).re = 2 * ∑' j, (Z j).re := by
    have hm := Complex.reCLM.map_tsum hZs.of_norm
    simp only [Complex.reCLM_apply] at hm
    rw [hg, show ((2 : ℂ) * ∑' j, Z j).re = 2 * (∑' j, Z j).re by simp, hm]
  have hRn : ∀ j, |(Z j).re| ≤ ‖ζ‖ * a ^ j := fun j => (Complex.abs_re_le_norm _).trans (hZn j)
  have hRs : Summable (fun j => (Z j).re) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left ‖ζ‖) hRn
  rw [hre, hRs.tsum_eq_zero_add]
  have hZ0 : (Z 0).re = (π ^ 2 / 12) * σ := by
    rw [hZ]
    show ((η 0 : ℂ) * ζ ^ (2 * 0 + 1)).re = _
    rw [Nat.mul_zero, zero_add, pow_one, Complex.re_ofReal_mul, h.zero]
    simp [hζ]
  -- tail
  have htail : ∀ j, |(Z (j + 1)).re| ≤ σ * (a * ((2 * (j : ℝ) + 3) * a ^ j)) := by
    intro j
    have hZ1 : (Z (j + 1)).re = η (j + 1) * (ζ ^ (2 * (j + 1) + 1)).re := by
      rw [hZ]; simp only []
      rw [Complex.re_ofReal_mul]
    rw [hZ1, abs_mul, abs_of_pos (h.pos _)]
    have := abs_re_pow_odd_le hσ0.le (τ := τ) (j + 1)
    rw [← hζ] at this
    have h1 := h.le_one (j + 1)
    calc η (j + 1) * |(ζ ^ (2 * (j + 1) + 1)).re| ≤ 1 * |(ζ ^ (2 * (j + 1) + 1)).re| := by
          gcongr
      _ ≤ (2 * ((j + 1 : ℕ) : ℝ) + 1) * ‖ζ‖ ^ (2 * (j + 1)) * σ := by rw [one_mul]; exact this
      _ = σ * (a * ((2 * (j : ℝ) + 3) * a ^ j)) := by
          rw [ha, ← pow_mul, show ‖ζ‖ ^ (2 * (j + 1)) = (‖ζ‖ ^ 2) ^ (j + 1) by rw [← pow_mul]]
          push_cast; ring
  have hTs : Summable (fun j : ℕ => (Z (j + 1)).re) := (summable_nat_add_iff 1).2 hRs
  have hsumM : HasSum (fun j : ℕ => σ * (a * ((2 * (j : ℝ) + 3) * a ^ j)))
      (σ * (a * (2 * a / (1 - a) ^ 2 + 3 / (1 - a)))) :=
    ((hasSum_odd_weight ha0 ha1).mul_left a).mul_left σ
  have htailb : |∑' j : ℕ, (Z (j + 1)).re| ≤ σ * (a * (2 * a / (1 - a) ^ 2 + 3 / (1 - a))) := by
    have := tsum_of_norm_bounded (f := fun j : ℕ => (Z (j + 1)).re) hsumM
      (fun j => by rw [Real.norm_eq_abs]; exact htail j)
    simpa [Real.norm_eq_abs] using this
  have hL : a * (2 * a / (1 - a) ^ 2 + 3 / (1 - a)) ≤ 0.1128 * (2 * 0.1128 / (1 - 0.1128) ^ 2 + 3 / (1 - 0.1128)) := by
    gcongr
  have hLn : (0.1128 : ℝ) * (2 * 0.1128 / (1 - 0.1128) ^ 2 + 3 / (1 - 0.1128)) ≤ 0.4139 := by norm_num
  have hpi : (0.8224 : ℝ) ≤ π ^ 2 / 12 := by nlinarith [Real.pi_gt_d4]
  have hab := abs_le.1 htailb
  have : σ * (a * (2 * a / (1 - a) ^ 2 + 3 / (1 - a))) ≤ σ * 0.4139 :=
    mul_le_mul_of_nonneg_left (hL.trans hLn) hσ0.le
  rw [hZ0]
  nlinarith

end GSer

/-- info: 'FormalResearch.SignUncertainty.re_gSerD_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_gSerD_ge

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_gSer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_gSer

end FormalResearch.SignUncertainty

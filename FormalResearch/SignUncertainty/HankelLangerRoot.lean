module

public import FormalResearch.SignUncertainty.HankelLangerMu
public import FormalResearch.SignUncertainty.HankelStripSeries

/-!
# The saddle `ζ_+ = u^{1/2}` and the phase at the saddle (`gt:7.7b`, `gt:7.7c`)

For `‖ζ‖ < 1` and `u = ζ²`: `g(ζ) = (π²/12) K(u)` (so `K(u) = 12 s/π²` means `g(ζ) = s`), and
`S̃(ζ) - ζ g(ζ) = -(π²/18) ζ³ E(u)` (`V = S̃ - ζ g`, `gt:7.7b` (0)); with `𝗆(ζ)³ = ζ³ E(u)`.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

section Root

variable {η : ℕ → ℝ}

lemma psW_sub_of_bdd {a b : ℕ → ℝ} {B : ℝ} (ha : ∀ j, |a j| ≤ B) (hb : ∀ j, |b j| ≤ B) {u : ℂ}
    (hu : ‖u‖ < 1) : psW (fun j => a j - b j) u = psW a u - psW b u := by
  unfold psW
  rw [← Summable.tsum_sub (summable_psW ha hu).of_norm (summable_psW hb hu).of_norm]
  refine tsum_congr fun j => ?_
  push_cast; ring

lemma psW_const_mul (a : ℕ → ℝ) (k : ℝ) (u : ℂ) : psW (fun j => k * a j) u = (k : ℂ) * psW a u := by
  unfold psW
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  push_cast; ring

lemma psW_b_eq (η : ℕ → ℝ) (u : ℂ) :
    psW (fun j => η j / ((j : ℝ) + 1)) u = ((π ^ 2 / 12 : ℝ) : ℂ) * psW (aG η) u := by
  rw [← psW_const_mul]
  unfold psW
  refine tsum_congr fun j => ?_
  unfold aG
  have : (π : ℝ) ^ 2 ≠ 0 := by positivity
  congr 2
  field_simp

/-- `g(ζ) = (π²/12) K(ζ²)`. -/
lemma gSer_eq_chartK (η : ℕ → ℝ) (ζ : ℂ) : gSer η ζ = ((π ^ 2 / 12 : ℝ) : ℂ) * chartK η (ζ ^ 2) := by
  unfold gSer chartK
  rw [psW_b_eq]; ring

/-- `S̃(ζ) - ζ g(ζ) = -(π²/18) ζ³ E(ζ²)`. -/
theorem SSer_sub_mul_gSer (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    SSer η ζ - ζ * gSer η ζ = -(((π ^ 2 / 18 : ℝ) : ℂ)) * ζ ^ 3 * chartE η (ζ ^ 2) := by
  have hu : ‖ζ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ζ]
  set c : ℕ → ℝ := fun j => η j / (((j : ℝ) + 1) * (2 * (j : ℝ) + 3)) with hc
  set b : ℕ → ℝ := fun j => η j / ((j : ℝ) + 1) with hb
  have hcd : (fun j => c j - b j) = fun j => (-(π ^ 2 / 18)) * aE η j := by
    funext j
    simp only [hc, hb, aE]
    have : (π : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have h1 := psW_sub_of_bdd (a := c) (b := b) (B := 1) (abs_eta_div2_le h) (abs_eta_div_le h) hu
  rw [hcd, psW_const_mul] at h1
  unfold SSer gSer chartE
  have : ζ ^ 3 * psW c (ζ ^ 2) - ζ * (ζ ^ 2 * psW b (ζ ^ 2)) = ζ ^ 3 * (psW c (ζ ^ 2) - psW b (ζ ^ 2)) := by ring
  rw [this, ← h1]; push_cast; ring

/-- `(x^{1/3})³ = x`, `(x^{1/3})² = x^{2/3}`. -/
lemma cpow_third_cube (x : ℂ) : (x ^ ((1 / 3 : ℝ) : ℂ)) ^ 3 = x := by
  have := Complex.cpow_nat_inv_pow x (n := 3) (by norm_num)
  rw [show ((1 / 3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ)⁻¹ by push_cast; norm_num]
  exact this

lemma cpow_third_sq (x : ℂ) : (x ^ ((1 / 3 : ℝ) : ℂ)) ^ 2 = x ^ ((2 / 3 : ℝ) : ℂ) := by
  rw [← Complex.cpow_nat_mul]; congr 1; push_cast; norm_num

/-- `𝗆(ζ)² = M(ζ²)`. -/
lemma mMap_sq (η : ℕ → ℝ) (ζ : ℂ) : mMap η ζ ^ 2 = chartM η (ζ ^ 2) := by
  unfold mMap powMap chartM powMapU
  rw [mul_pow, cpow_third_sq]

/-- `𝗆(ζ)³ = ζ³ E(ζ²)`. -/
lemma mMap_cube (η : ℕ → ℝ) (ζ : ℂ) : mMap η ζ ^ 3 = ζ ^ 3 * chartE η (ζ ^ 2) := by
  unfold mMap powMap chartE
  rw [mul_pow, cpow_third_cube]

/-- The principal square root of `w²` is `w` when `Re w > 0`. -/
lemma cpow_half_sq_of_re_pos {w : ℂ} (hw : 0 < w.re) : (w ^ 2) ^ (1 / 2 : ℂ) = w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have harg : |w.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have h2 := abs_lt.1 harg
  have hcm := Complex.cpow_mul (x := w) (y := (2 : ℂ)) (z := (1 / 2 : ℂ)) (by
      rw [Complex.mul_im, Complex.log_re, Complex.log_im]; simp; linarith [Real.pi_pos])
    (by rw [Complex.mul_im, Complex.log_im]; simp; linarith [Real.pi_pos])
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one] at hcm
  rw [Complex.cpow_two] at hcm
  exact hcm.symm

lemma psW_ofReal (a : ℕ → ℝ) (x : ℝ) : psW a (x : ℂ) = ((∑' j : ℕ, a j * x ^ j : ℝ) : ℂ) := by
  unfold psW
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  push_cast; ring

lemma re_mMap_imag (h : LangerEta η) {τ : ℝ} (hτ : |τ| ≤ 0.035) :
    (mMap η ((τ : ℂ) * Complex.I)).re = 0 := by
  set ζ : ℂ := (τ : ℂ) * Complex.I with hζ
  have hn : ‖ζ‖ ≤ 0.035 := by
    rw [hζ, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]; exact hτ
  have hsq : ζ ^ 2 = ((-(τ ^ 2) : ℝ) : ℂ) := by
    rw [hζ, mul_pow, Complex.I_sq]; push_cast; ring
  set e : ℝ := ∑' j : ℕ, aE η j * (-(τ ^ 2)) ^ j with he
  have hE : psW (aE η) (ζ ^ 2) = (e : ℂ) := by rw [hsq, psW_ofReal]
  have hx := norm_psWaE_sub_one_le h hn
  rw [hE] at hx
  have hepos : 0 < e := by
    have h1 : |((e : ℂ) - 1).re| ≤ ‖(e : ℂ) - 1‖ := Complex.abs_re_le_norm _
    have h2 := abs_le.1 (h1.trans hx)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at h2
    linarith [h2.1]
  unfold mMap powMap
  rw [hE, ← Complex.ofReal_cpow hepos.le, Complex.re_mul_ofReal]
  simp [hζ]

lemma abs_im_le_norm_ζ {σ τ : ℝ} : |τ| ≤ ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ := by
  have : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = σ ^ 2 + τ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  nlinarith [norm_nonneg ((σ : ℂ) + (τ : ℂ) * Complex.I), sq_abs τ, abs_nonneg τ, sq_nonneg σ]

/-- `(1 - 9·10⁻⁴) σ ≤ Re 𝗆(σ + iτ) ≤ (1 + 9·10⁻⁴) σ` for `σ ≥ 0`, `‖σ + iτ‖ ≤ 0.035`. -/
theorem re_mMap_bounds (h : LangerEta η) {σ τ : ℝ} (hσ : 0 ≤ σ)
    (hζ : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 0.035) :
    (1 - 9e-4) * σ ≤ (mMap η ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ∧
      (mMap η ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ (1 + 9e-4) * σ := by
  set a : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with ha
  set b : ℂ := (τ : ℂ) * Complex.I with hb
  have hτ : |τ| ≤ 0.035 := (abs_im_le_norm_ζ (σ := σ) (τ := τ)).trans hζ
  have hbn : ‖b‖ ≤ 0.035 := by
    rw [hb, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]; exact hτ
  have hd : ∀ z ∈ closedBall (0 : ℂ) 0.035,
      HasDerivAt (fun z => mMap η z - z) (powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) z - 1) z := by
    intro z hz
    exact (hasDerivAt_mMap h (by simpa using mem_closedBall_zero_iff.1 hz)).sub (hasDerivAt_id z)
  have hbd : ∀ z ∈ closedBall (0 : ℂ) 0.035,
      ‖powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) z - 1‖ ≤ 9e-4 := fun z hz =>
    norm_mMapD_sub_one_le h (by simpa using mem_closedBall_zero_iff.1 hz)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun z => mMap η z - z)
    (s := closedBall (0 : ℂ) 0.035) (x := b) (y := a) (fun z hz => (hd z hz).hasDerivWithinAt) hbd
    (convex_closedBall _ _) (mem_closedBall_zero_iff.2 hbn) (mem_closedBall_zero_iff.2 hζ)
  have hab : a - b = (σ : ℂ) := by rw [ha, hb]; ring
  have hre0 := re_mMap_imag h hτ
  rw [← hb] at hre0
  have e : mMap η a - a - (mMap η b - b) = (mMap η a - mMap η b) - (σ : ℂ) := by
    rw [← hab]; ring
  rw [e, hab, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ] at hmv
  have h1 : |((mMap η a - mMap η b) - (σ : ℂ)).re| ≤ 9e-4 * σ :=
    (Complex.abs_re_le_norm _).trans hmv
  have h2 := abs_le.1 h1
  simp only [Complex.sub_re, Complex.ofReal_re, hre0, sub_zero] at h2
  constructor <;> linarith [h2.1, h2.2]

/-- The saddle `ζ_+ = u^{1/2}` (principal root). -/
noncomputable def saddleRoot (u : ℂ) : ℂ := u ^ (1 / 2 : ℂ)

lemma saddleRoot_sq (u : ℂ) : saddleRoot u ^ 2 = u := by
  unfold saddleRoot
  have := Complex.cpow_nat_inv_pow u (n := 2) (by norm_num)
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact this

lemma norm_saddleRoot (u : ℂ) : ‖saddleRoot u‖ = ‖u‖ ^ (1 / 2 : ℝ) := by
  unfold saddleRoot
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; norm_num, Complex.norm_cpow_real]

lemma norm_saddleRoot_le {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) : ‖saddleRoot u‖ ≤ 0.035 := by
  rw [norm_saddleRoot]
  calc ‖u‖ ^ (1 / 2 : ℝ) ≤ (0.035 ^ 2 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hu (by norm_num)
    _ = 0.035 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]

lemma re_saddleRoot_pos {u : ℂ} (hu : u ∈ slitPlane) : 0 < (saddleRoot u).re := by
  have hu0 : u ≠ 0 := Complex.slitPlane_ne_zero hu
  have harg : u.arg ≠ π := (Complex.mem_slitPlane_iff_arg.1 hu).1
  unfold saddleRoot
  rw [Complex.cpow_def_of_ne_zero hu0, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have him : (Complex.log u * (1 / 2 : ℂ)).im = u.arg / 2 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re]; simp; ring
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  have := Complex.neg_pi_lt_arg u
  have := Complex.arg_le_pi u
  have : u.arg < π := lt_of_le_of_ne (Complex.arg_le_pi u) harg
  constructor <;> linarith

/-- The Langer constant `μ = (π²/24)^{1/3}`, `μ³ = π²/24`. -/
noncomputable def langerMu : ℝ := (π ^ 2 / 24) ^ (1 / 3 : ℝ)

lemma langerMu_pos : 0 < langerMu := Real.rpow_pos_of_pos (by positivity) _

lemma langerMu_cube : langerMu ^ 3 = π ^ 2 / 24 := by
  unfold langerMu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

/-- The Langer coordinate `ũ = c^{2/3} μ² M(u)`. -/
noncomputable def langerUtilde (η : ℕ → ℝ) (c : ℝ) (u : ℂ) : ℂ :=
  ((c ^ (2 / 3 : ℝ) * langerMu ^ 2 : ℝ) : ℂ) * chartM η u

/-- `√ũ = c^{1/3} μ 𝗆(ζ_+)` off the cut, and `c (S̃ - ζ g) = -(4/3) ũ^{3/2}` at the saddle. -/
theorem langerUtilde_sqrt (h : LangerEta η) {c : ℝ} (hc : 0 < c) {u : ℂ} (hu : u ∈ slitPlane)
    (hun : ‖u‖ ≤ 0.035 ^ 2) :
    (langerUtilde η c u) ^ (1 / 2 : ℂ) = ((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ) * mMap η (saddleRoot u) := by
  set ζ := saddleRoot u with hζ
  have hre : 0 < ζ.re := re_saddleRoot_pos hu
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hun
  have hm := re_mMap_bounds h (σ := ζ.re) (τ := ζ.im) hre.le (by
    have : (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I = ζ := by apply Complex.ext <;> simp
    rw [this]; exact hζn)
  have hmre : 0 < (mMap η ζ).re := by
    have : (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I = ζ := by apply Complex.ext <;> simp
    rw [this] at hm
    nlinarith [hm.1]
  have hsq : langerUtilde η c u = (((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ) * mMap η ζ) ^ 2 := by
    rw [mul_pow, mMap_sq, hζ, saddleRoot_sq]
    unfold langerUtilde
    congr 1
    push_cast
    have : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) ^ 2 = ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
    rw [mul_pow, this]
  rw [hsq]
  apply cpow_half_sq_of_re_pos
  rw [Complex.re_ofReal_mul]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) langerMu_pos) hmre

/-- **`gt:7.7b` (iv)**: `c (S̃(ζ_+) - ζ_+ g(ζ_+)) = -(4/3) ũ^{3/2}` (`Φ(ζ_+) = S̃ - ζ g`, `g(ζ_+) = s`). -/
theorem phase_at_saddle (h : LangerEta η) {c : ℝ} (hc : 0 < c) {u : ℂ} (hu : u ∈ slitPlane)
    (hun : ‖u‖ ≤ 0.035 ^ 2) :
    (c : ℂ) * (SSer η (saddleRoot u) - saddleRoot u * gSer η (saddleRoot u)) =
      -(4 / 3 : ℂ) * (langerUtilde η c u) ^ (3 / 2 : ℂ) := by
  set ζ := saddleRoot u with hζ
  have hζn : ‖ζ‖ < 1 := lt_of_le_of_lt (norm_saddleRoot_le hun) (by norm_num)
  rw [SSer_sub_mul_gSer h hζn]
  have h32 : (langerUtilde η c u) ^ (3 / 2 : ℂ) = ((langerUtilde η c u) ^ (1 / 2 : ℂ)) ^ 3 := by
    rw [← Complex.cpow_nat_mul]; norm_num
  rw [h32, langerUtilde_sqrt h hc hu hun, mul_pow, ← hζ, mMap_cube, hζ, saddleRoot_sq]
  have hc3 : (((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ)) ^ 3 = (c : ℂ) * ((π ^ 2 / 24 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, langerMu_cube]
    push_cast; norm_num
  rw [hc3]; push_cast; ring

/-- info: 'FormalResearch.SignUncertainty.phase_at_saddle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_at_saddle

/-- info: 'FormalResearch.SignUncertainty.langerUtilde_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerUtilde_sqrt

end Root

end FormalResearch.SignUncertainty

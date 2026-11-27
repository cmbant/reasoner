module

public import FormalResearch.SignUncertainty.UctEnv2
public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.UctSeedAdmiss
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Edge-trace calculus for the warp summand of `fct:main-hankel` (graded `C²` envelopes)

`EJ f a N b M`: `f : ℝ → ℂ` is `C²` on `{τ ≠ 0}` and `‖f^{(j)}(τ)‖ ≤ M |τ|^{a-j} (1+|τ|)^{N+j} e^{-π b |τ|}` there (`j = 0,1,2`).
The class is closed under products (Leibniz, `EJ.mul`) and constant multiples, contains the `Env2` functions (`EJ.of_env2`, `a = 0`)
and the powers `(τ i)^{-5/2}` (`edgeS_EJ`) and `(1 - τ i)^{-5/2}` (`edgeR_EJ`); `edge0_of_EJ` turns an `EJ` bound with
`a = 1/2`, `b = 1` for the left-edge trace of `W` into `StripEdge0 (1/2) W` (hypothesis (M3) of `uct:admiss`).

Class: proved (calculus).
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The weight `|τ|^{a-j} (1+|τ|)^{N+j} e^{-π b |τ|}`. -/
noncomputable def ejW (a : ℝ) (N : ℕ) (b : ℝ) (j : ℕ) (τ : ℝ) : ℝ :=
  |τ| ^ (a - (j : ℝ)) * (1 + |τ|) ^ (N + j) * Real.exp (-(π * b * |τ|))

lemma ejW_pos {a b : ℝ} {N j : ℕ} {τ : ℝ} (hτ : τ ≠ 0) : 0 < ejW a N b j τ := by
  have h0 : 0 < |τ| := abs_pos.mpr hτ
  unfold ejW
  positivity

lemma ejW_mul {a a' b b' : ℝ} {N N' j k : ℕ} {τ : ℝ} (hτ : τ ≠ 0) :
    ejW a N b j τ * ejW a' N' b' k τ = ejW (a + a') (N + N') (b + b') (j + k) τ := by
  have h0 : 0 < |τ| := abs_pos.mpr hτ
  unfold ejW
  have e1 : |τ| ^ (a - (j : ℝ)) * |τ| ^ (a' - (k : ℝ)) = |τ| ^ (a + a' - ((j + k : ℕ) : ℝ)) := by
    rw [← Real.rpow_add h0]; congr 1; push_cast; ring
  have e2 : (1 + |τ|) ^ (N + j) * (1 + |τ|) ^ (N' + k) = (1 + |τ|) ^ (N + N' + (j + k)) := by
    rw [← pow_add]; congr 1; ring
  have e3 : Real.exp (-(π * b * |τ|)) * Real.exp (-(π * b' * |τ|)) = Real.exp (-(π * (b + b') * |τ|)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = (|τ| ^ (a - (j : ℝ)) * |τ| ^ (a' - (k : ℝ))) * ((1 + |τ|) ^ (N + j) * (1 + |τ|) ^ (N' + k)) *
        (Real.exp (-(π * b * |τ|)) * Real.exp (-(π * b' * |τ|))) := by ring
    _ = _ := by rw [e1, e2, e3]

/-- Graded `C²` envelope of the trace `f` on `{τ ≠ 0}`. -/
structure EJ (f : ℝ → ℂ) (a : ℝ) (N : ℕ) (b M : ℝ) : Prop where
  hM : 0 ≤ M
  c2 : ContDiffOn ℝ 2 f {τ : ℝ | τ ≠ 0}
  b0 : ∀ τ : ℝ, τ ≠ 0 → ‖f τ‖ ≤ M * ejW a N b 0 τ
  b1 : ∀ τ : ℝ, τ ≠ 0 → ‖deriv f τ‖ ≤ M * ejW a N b 1 τ
  b2 : ∀ τ : ℝ, τ ≠ 0 → ‖deriv (deriv f) τ‖ ≤ M * ejW a N b 2 τ

/-- Leibniz formulas for `f * g` at points of an open set `S` where both are `C²`. -/
lemma prod_deriv_on {f g : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S) (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    {τ : ℝ} (hτ : τ ∈ S) :
    deriv (fun t => f t * g t) τ = deriv f τ * g τ + f τ * deriv g τ ∧
    deriv (deriv (fun t => f t * g t)) τ =
      deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ := by
  have hd : ∀ (h : ℝ → ℂ), ContDiffOn ℝ 2 h S → ∀ t ∈ S, DifferentiableAt ℝ h t := fun h hh t ht =>
    (hh.differentiableOn (by norm_num) t ht).differentiableAt (hS.mem_nhds ht)
  have hd1 : ∀ (h : ℝ → ℂ), ContDiffOn ℝ 2 h S → ∀ t ∈ S, DifferentiableAt ℝ (deriv h) t := fun h hh t ht =>
    ((hh.deriv_of_isOpen hS (by norm_num) : ContDiffOn ℝ 1 (deriv h) S).differentiableOn (by norm_num) t ht).differentiableAt
      (hS.mem_nhds ht)
  have hform : ∀ t ∈ S, deriv (fun t => f t * g t) t = deriv f t * g t + f t * deriv g t := fun t ht =>
    deriv_mul (hd f hf t ht) (hd g hg t ht)
  refine ⟨hform τ hτ, ?_⟩
  have hev : deriv (fun t => f t * g t) =ᶠ[𝓝 τ] fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hS.mem_nhds hτ] with t ht using hform t ht
  rw [hev.deriv_eq]
  have e2 : deriv (fun t => deriv f t * g t) τ = deriv (deriv f) τ * g τ + deriv f τ * deriv g τ :=
    (HasDerivAt.mul (hd1 f hf τ hτ).hasDerivAt (hd g hg τ hτ).hasDerivAt).deriv
  have e3 : deriv (fun t => f t * deriv g t) τ = deriv f τ * deriv g τ + f τ * deriv (deriv g) τ :=
    (HasDerivAt.mul (hd f hf τ hτ).hasDerivAt (hd1 g hg τ hτ).hasDerivAt).deriv
  have e : deriv (fun t => deriv f t * g t + f t * deriv g t) τ =
      deriv (fun t => deriv f t * g t) τ + deriv (fun t => f t * deriv g t) τ :=
    (HasDerivAt.add ((hd1 f hf τ hτ).mul (hd g hg τ hτ)).hasDerivAt ((hd f hf τ hτ).mul (hd1 g hg τ hτ)).hasDerivAt).deriv
  rw [e, e2, e3]
  ring

theorem EJ.mul {f g : ℝ → ℂ} {a a' b b' M M' : ℝ} {N N' : ℕ} (hf : EJ f a N b M) (hg : EJ g a' N' b' M') :
    EJ (fun t => f t * g t) (a + a') (N + N') (b + b') (4 * M * M') where
  hM := by have := hf.hM; have := hg.hM; positivity
  c2 := hf.c2.mul hg.c2
  b0 τ hτ := by
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 0) hτ
    have w := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 0) hτ
    have w0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have w0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have hM := hf.hM; have hM' := hg.hM
    simp only [norm_mul]
    calc ‖f τ‖ * ‖g τ‖ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 0 τ) :=
          mul_le_mul (hf.b0 τ hτ) (hg.b0 τ hτ) (norm_nonneg _) (by positivity)
      _ = M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by rw [← w]; ring
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by
          have : 0 ≤ M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by positivity
          nlinarith
  b1 τ hτ := by
    have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
    obtain ⟨h1, -⟩ := prod_deriv_on hS hf.c2 hg.c2 (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)
    rw [h1]
    have w01 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 1) hτ
    have w10 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 1) (k := 0) hτ
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 1) hτ
    have e0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have e0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have e1 := ejW_pos (a := a) (b := b) (N := N) (j := 1) hτ
    have e1' := ejW_pos (a := a') (b := b') (N := N') (j := 1) hτ
    have hM := hf.hM; have hM' := hg.hM
    have t1 : ‖deriv f τ * g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 1 τ) * (M' * ejW a' N' b' 0 τ) :=
            mul_le_mul (hf.b1 τ hτ) (hg.b0 τ hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w10]; ring
    have t2 : ‖f τ * deriv g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 1 τ) :=
            mul_le_mul (hf.b0 τ hτ) (hg.b1 τ hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w01]; ring
    calc _ ≤ ‖deriv f τ * g τ‖ + ‖f τ * deriv g τ‖ := norm_add_le _ _
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
          have : 0 ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by positivity
          nlinarith
  b2 τ hτ := by
    have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
    obtain ⟨-, h2⟩ := prod_deriv_on hS hf.c2 hg.c2 (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)
    rw [h2]
    have w02 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 2) hτ
    have w11 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 1) (k := 1) hτ
    have w20 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 2) (k := 0) hτ
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 2) hτ
    have e0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have e0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have e1 := ejW_pos (a := a) (b := b) (N := N) (j := 1) hτ
    have e1' := ejW_pos (a := a') (b := b') (N := N') (j := 1) hτ
    have e2 := ejW_pos (a := a) (b := b) (N := N) (j := 2) hτ
    have e2' := ejW_pos (a := a') (b := b') (N := N') (j := 2) hτ
    have hM := hf.hM; have hM' := hg.hM
    have t1 : ‖deriv (deriv f) τ * g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 2 τ) * (M' * ejW a' N' b' 0 τ) :=
            mul_le_mul (hf.b2 τ hτ) (hg.b0 τ hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w20]; ring
    have t2 : ‖deriv f τ * deriv g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 1 τ) * (M' * ejW a' N' b' 1 τ) :=
            mul_le_mul (hf.b1 τ hτ) (hg.b1 τ hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w11]; ring
    have t3 : ‖f τ * deriv (deriv g) τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 2 τ) :=
            mul_le_mul (hf.b0 τ hτ) (hg.b2 τ hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w02]; ring
    calc _ ≤ ‖deriv (deriv f) τ * g τ‖ + ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ + ‖f τ * deriv (deriv g) τ‖ :=
          norm_add₃_le
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
          have h2 : ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ ≤ 2 * (M * M' * ejW (a + a') (N + N') (b + b') 2 τ) := by
            have : ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ = 2 * ‖deriv f τ * deriv g τ‖ := by
              rw [norm_mul]; simp
            rw [this]; linarith
          have h3 : ‖deriv (deriv f) τ * g τ‖ + ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ + ‖f τ * deriv (deriv g) τ‖ ≤
              4 * (M * M' * ejW (a + a') (N + N') (b + b') 2 τ) := by linarith
          linarith

theorem EJ.const_mul {f : ℝ → ℂ} {a b M : ℝ} {N : ℕ} (hf : EJ f a N b M) (k : ℂ) :
    EJ (fun t => k * f t) a N b (‖k‖ * M) where
  hM := mul_nonneg (norm_nonneg _) hf.hM
  c2 := contDiffOn_const.mul hf.c2
  b0 τ hτ := by
    rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b0 τ hτ) (norm_nonneg _)
  b1 τ hτ := by
    have : deriv (fun t => k * f t) τ = k * deriv f τ := deriv_const_mul_field k
    rw [this, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b1 τ hτ) (norm_nonneg _)
  b2 τ hτ := by
    have h1 : deriv (fun t => k * f t) = fun t => k * deriv f t := funext fun t => deriv_const_mul_field k
    rw [h1]
    have : deriv (fun t => k * deriv f t) τ = k * deriv (deriv f) τ := deriv_const_mul_field k
    rw [this, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b2 τ hτ) (norm_nonneg _)

lemma ejW_ge {b : ℝ} {N : ℕ} (j : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    (1 + |τ|) ^ N * Real.exp (-(π * b * |τ|)) ≤ ejW 0 N b j τ := by
  have h0 : 0 < |τ| := abs_pos.mpr hτ
  unfold ejW
  have e : |τ| ^ ((0 : ℝ) - (j : ℝ)) = (|τ| ^ j)⁻¹ := by
    rw [zero_sub, Real.rpow_neg h0.le, Real.rpow_natCast]
  rw [e, pow_add]
  have key : 1 ≤ (|τ| ^ j)⁻¹ * (1 + |τ|) ^ j := by
    rw [← div_eq_inv_mul, one_le_div (by positivity)]
    exact pow_le_pow_left₀ h0.le (by linarith) j
  have hE := (Real.exp_pos (-(π * b * |τ|))).le
  have hP : 0 ≤ (1 + |τ|) ^ N := by positivity
  calc (1 + |τ|) ^ N * Real.exp (-(π * b * |τ|)) = (1 + |τ|) ^ N * 1 * Real.exp (-(π * b * |τ|)) := by ring
    _ ≤ (1 + |τ|) ^ N * ((|τ| ^ j)⁻¹ * (1 + |τ|) ^ j) * Real.exp (-(π * b * |τ|)) := by gcongr
    _ = _ := by ring

theorem EJ.of_env2 {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) {M b : ℝ} (hM : 0 ≤ M) (N : ℕ)
    (hP : ∀ τ : ℝ, P τ ≤ M * ((1 + |τ|) ^ N * Real.exp (-(π * b * |τ|)))) : EJ f 0 N b M where
  hM := hM
  c2 := h.1.contDiffOn
  b0 τ hτ := ((h.2 τ).1.trans (hP τ)).trans (mul_le_mul_of_nonneg_left (ejW_ge 0 hτ) hM)
  b1 τ hτ := ((h.2 τ).2.1.trans (hP τ)).trans (mul_le_mul_of_nonneg_left (ejW_ge 1 hτ) hM)
  b2 τ hτ := ((h.2 τ).2.2.trans (hP τ)).trans (mul_le_mul_of_nonneg_left (ejW_ge 2 hτ) hM)

/-! ### Powers of linear functions of `τ` -/

lemma cpow_line_contDiffOn (z0 d s : ℂ) {S : Set ℝ} (hz : ∀ τ ∈ S, z0 + d * (τ : ℂ) ∈ Complex.slitPlane) :
    ContDiffOn ℝ 2 (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s) S := by
  have hUo : IsOpen {w : ℂ | z0 + d * w ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  have hd : DifferentiableOn ℂ (fun w : ℂ => (z0 + d * w) ^ s) {w : ℂ | z0 + d * w ∈ Complex.slitPlane} :=
    DifferentiableOn.cpow (by fun_prop) (differentiableOn_const _) (fun w hw => hw)
  have h1 : ContDiffOn ℂ 2 (fun w : ℂ => (z0 + d * w) ^ s) {w : ℂ | z0 + d * w ∈ Complex.slitPlane} := hd.contDiffOn hUo
  have h2 : ContDiffOn ℝ 2 (fun w : ℂ => (z0 + d * w) ^ s) {w : ℂ | z0 + d * w ∈ Complex.slitPlane} :=
    h1.restrict_scalars ℝ
  exact h2.comp Complex.ofRealCLM.contDiff.contDiffOn (fun τ hτ => hz τ hτ)

lemma cpow_line_hasDerivAt (z0 d s : ℂ) {τ : ℝ} (hz : z0 + d * (τ : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s) (s * d * (z0 + d * (τ : ℂ)) ^ (s - 1)) τ := by
  have hu : HasDerivAt (fun w : ℂ => z0 + d * w) d (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul d).const_add z0
  have h : HasDerivAt (fun w : ℂ => (z0 + d * w) ^ s) (s * (z0 + d * (τ : ℂ)) ^ (s - 1) * d) (τ : ℂ) :=
    hu.cpow_const hz
  have := h.comp_ofReal
  convert this using 1; ring

lemma cpow_line_deriv (z0 d s : ℂ) {S : Set ℝ} (hS : IsOpen S) (hz : ∀ τ ∈ S, z0 + d * (τ : ℂ) ∈ Complex.slitPlane)
    {τ : ℝ} (hτ : τ ∈ S) :
    deriv (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s) τ = s * d * (z0 + d * (τ : ℂ)) ^ (s - 1) ∧
    deriv (deriv (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s)) τ = s * (s - 1) * d ^ 2 * (z0 + d * (τ : ℂ)) ^ (s - 1 - 1) := by
  have h1 : ∀ t ∈ S, deriv (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s) t = s * d * (z0 + d * (t : ℂ)) ^ (s - 1) :=
    fun t ht => (cpow_line_hasDerivAt z0 d s (hz t ht)).deriv
  refine ⟨h1 τ hτ, ?_⟩
  have hev : deriv (fun τ : ℝ => (z0 + d * (τ : ℂ)) ^ s) =ᶠ[𝓝 τ] fun t => s * d * (z0 + d * (t : ℂ)) ^ (s - 1) := by
    filter_upwards [hS.mem_nhds hτ] with t ht using h1 t ht
  rw [hev.deriv_eq]
  have := ((cpow_line_hasDerivAt z0 d (s - 1) (hz τ hτ)).const_mul (s * d)).deriv
  rw [this]; ring

/-- `‖(i τ)^r‖ = |τ|^r` for real `r`, `τ ≠ 0`. -/
lemma norm_cpow_line_I {τ : ℝ} (hτ : τ ≠ 0) (r : ℝ) :
    ‖((0 : ℂ) + Complex.I * (τ : ℂ)) ^ ((r : ℝ) : ℂ)‖ = |τ| ^ r := by
  have hz : (0 : ℂ) + Complex.I * (τ : ℂ) ≠ 0 := by simpa using hτ
  rw [Complex.norm_cpow_of_ne_zero hz]
  simp

lemma slit_I {τ : ℝ} (hτ : τ ≠ 0) : (0 : ℂ) + Complex.I * (τ : ℂ) ∈ Complex.slitPlane := by
  right; simpa using hτ

lemma slit_one_sub (τ : ℝ) : (1 : ℂ) + (-Complex.I) * (τ : ℂ) ∈ Complex.slitPlane := by
  left; simp

/-- `τ ↦ (iτ)^{-5/2}`. -/
noncomputable def edgeS (τ : ℝ) : ℂ := ((0 : ℂ) + Complex.I * (τ : ℂ)) ^ (((-(5 / 2) : ℝ)) : ℂ)

/-- `τ ↦ (1 - iτ)^{-5/2}`. -/
noncomputable def edgeR (τ : ℝ) : ℂ := ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) ^ (((-(5 / 2) : ℝ)) : ℂ)

lemma ejW_ge_rpow {a : ℝ} {N : ℕ} (j : ℕ) {τ : ℝ} (hτ : τ ≠ 0) : |τ| ^ (a - (j : ℝ)) ≤ ejW a N 0 j τ := by
  unfold ejW
  have h0 : 0 < |τ| := abs_pos.mpr hτ
  have h1 : (1 : ℝ) ≤ (1 + |τ|) ^ (N + j) := one_le_pow₀ (by linarith [abs_nonneg τ])
  simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
  have hp : 0 < |τ| ^ (a - (j : ℝ)) := Real.rpow_pos_of_pos h0 _
  nlinarith

theorem edgeS_EJ : EJ edgeS (-(5 / 2)) 0 0 9 := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hz : ∀ τ ∈ {τ : ℝ | τ ≠ 0}, (0 : ℂ) + Complex.I * (τ : ℂ) ∈ Complex.slitPlane := fun τ hτ => slit_I hτ
  refine ⟨by norm_num, cpow_line_contDiffOn _ _ _ hz, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · have := ejW_ge_rpow (a := -(5 / 2)) (N := 0) 0 hτ
    have e : ‖edgeS τ‖ = |τ| ^ (-(5 / 2) : ℝ) := norm_cpow_line_I hτ _
    rw [e]; simp only [Nat.cast_zero, sub_zero] at this
    nlinarith [Real.rpow_pos_of_pos (abs_pos.mpr hτ) (-(5 / 2) : ℝ)]
  · have hd := (cpow_line_deriv (0 : ℂ) Complex.I (((-(5 / 2) : ℝ)) : ℂ) hS hz (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)).1
    have h2 := ejW_ge_rpow (a := -(5 / 2)) (N := 0) 1 hτ
    have e : (((-(5 / 2) : ℝ) : ℂ) - 1) = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
    show ‖deriv edgeS τ‖ ≤ _
    unfold edgeS
    rw [hd, e, norm_mul, norm_mul, norm_cpow_line_I hτ]
    have hn : ‖(((-(5 / 2) : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    rw [hn, Complex.norm_I]
    have e2 : -(5 / 2 : ℝ) - ((1 : ℕ) : ℝ) = -(7 / 2) := by norm_num
    rw [e2] at h2
    have := Real.rpow_pos_of_pos (abs_pos.mpr hτ) (-(7 / 2) : ℝ)
    nlinarith
  · have hd := (cpow_line_deriv (0 : ℂ) Complex.I (((-(5 / 2) : ℝ)) : ℂ) hS hz (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)).2
    have h2 := ejW_ge_rpow (a := -(5 / 2)) (N := 0) 2 hτ
    have e : (((-(5 / 2) : ℝ) : ℂ) - 1 - 1) = (((-(9 / 2) : ℝ)) : ℂ) := by push_cast; ring
    show ‖deriv (deriv edgeS) τ‖ ≤ _
    unfold edgeS
    rw [hd, e, norm_mul, norm_mul, norm_mul, norm_cpow_line_I hτ]
    have hn : ‖(((-(5 / 2) : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    have hn1 : ‖(((-(5 / 2) : ℝ)) : ℂ) - 1‖ = 7 / 2 := by
      have : (((-(5 / 2) : ℝ)) : ℂ) - 1 = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
      rw [this]; simp
    rw [hn, hn1, norm_pow, Complex.norm_I]
    have e2 : -(5 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(9 / 2) := by norm_num
    rw [e2] at h2
    have := Real.rpow_pos_of_pos (abs_pos.mpr hτ) (-(9 / 2) : ℝ)
    nlinarith

theorem edgeR_EJ : EJ edgeR 0 0 0 9 := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hz : ∀ τ ∈ {τ : ℝ | τ ≠ 0}, (1 : ℂ) + (-Complex.I) * (τ : ℂ) ∈ Complex.slitPlane := fun τ _ => slit_one_sub τ
  have hnorm : ∀ (r : ℝ), r ≤ 0 → ∀ τ : ℝ, ‖((1 : ℂ) + (-Complex.I) * (τ : ℂ)) ^ ((r : ℝ) : ℂ)‖ ≤ 1 := by
    intro r hr τ
    have hz0 : (1 : ℂ) + (-Complex.I) * (τ : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    rw [Complex.norm_cpow_of_ne_zero hz0]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]
    refine Real.rpow_le_one_of_one_le_of_nonpos ?_ hr
    have := Complex.abs_re_le_norm ((1 : ℂ) + (-Complex.I) * (τ : ℂ))
    simpa using this
  have hge : ∀ j : ℕ, ∀ τ : ℝ, τ ≠ 0 → (1 : ℝ) ≤ ejW 0 0 0 j τ := fun j τ hτ => by
    have := ejW_ge (b := 0) (N := 0) j hτ
    simpa using this
  refine ⟨by norm_num, cpow_line_contDiffOn _ _ _ hz, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · have := hnorm (-(5 / 2)) (by norm_num) τ
    have h1 := hge 0 τ hτ
    show ‖edgeR τ‖ ≤ _
    unfold edgeR; nlinarith
  · have hd := (cpow_line_deriv (1 : ℂ) (-Complex.I) (((-(5 / 2) : ℝ)) : ℂ) hS hz (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)).1
    have e : (((-(5 / 2) : ℝ) : ℂ) - 1) = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
    have h1 := hge 1 τ hτ
    have hb := hnorm (-(7 / 2)) (by norm_num) τ
    show ‖deriv edgeR τ‖ ≤ _
    unfold edgeR
    rw [hd, e, norm_mul, norm_mul]
    have hn : ‖(((-(5 / 2) : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    rw [hn, norm_neg, Complex.norm_I]
    nlinarith [norm_nonneg (((1 : ℂ) + (-Complex.I) * (τ : ℂ)) ^ (((-(7 / 2) : ℝ)) : ℂ))]
  · have hd := (cpow_line_deriv (1 : ℂ) (-Complex.I) (((-(5 / 2) : ℝ)) : ℂ) hS hz (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)).2
    have e : (((-(5 / 2) : ℝ) : ℂ) - 1 - 1) = (((-(9 / 2) : ℝ)) : ℂ) := by push_cast; ring
    have h1 := hge 2 τ hτ
    have hb := hnorm (-(9 / 2)) (by norm_num) τ
    show ‖deriv (deriv edgeR) τ‖ ≤ _
    unfold edgeR
    rw [hd, e, norm_mul, norm_mul, norm_mul]
    have hn : ‖(((-(5 / 2) : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    have hn1 : ‖(((-(5 / 2) : ℝ)) : ℂ) - 1‖ = 7 / 2 := by
      have : (((-(5 / 2) : ℝ)) : ℂ) - 1 = (((-(7 / 2) : ℝ)) : ℂ) := by push_cast; ring
      rw [this]; simp
    rw [hn, hn1, norm_pow, norm_neg, Complex.norm_I]
    nlinarith [norm_nonneg (((1 : ℂ) + (-Complex.I) * (τ : ℂ)) ^ (((-(9 / 2) : ℝ)) : ℂ))]

/-! ### From an `EJ` bound to hypothesis (M3) -/

lemma rpow_half_sub_le {x : ℝ} (hx : 1 / 2 ≤ x) {j : ℕ} (hj : j ≤ 2) : x ^ ((1 / 2 : ℝ) - (j : ℝ)) ≤ 4 * (1 + x) := by
  have hx0 : 0 < x := by linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [Nat.cast_zero, sub_zero]
    rcases le_or_gt x 1 with h | h
    · have := Real.rpow_le_one hx0.le h (by norm_num : (0 : ℝ) ≤ 1 / 2)
      linarith
    · have : x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
      rw [Real.rpow_one] at this
      linarith
  · have he : (1 / 2 : ℝ) - (j : ℝ) ≤ 0 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      linarith
    have he2 : -2 ≤ (1 / 2 : ℝ) - (j : ℝ) := by
      have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      linarith
    have h1 : x ^ ((1 / 2 : ℝ) - (j : ℝ)) ≤ (1 / 2 : ℝ) ^ ((1 / 2 : ℝ) - (j : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx he
    have h2 : (1 / 2 : ℝ) ^ ((1 / 2 : ℝ) - (j : ℝ)) ≤ (1 / 2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he2
    have h3 : (1 / 2 : ℝ) ^ (-2 : ℝ) = 4 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    nlinarith

lemma ejW_far_le (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| → ∀ j : ℕ, j ≤ 2 →
    ejW (1 / 2) N 1 j τ ≤ K * (1 + |τ|) ^ (-(2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_n (N + 5)
  refine ⟨4 * K, by positivity, fun τ hτ j hj => ?_⟩
  set x : ℝ := |τ| with hx
  have hx0 : 0 ≤ x := abs_nonneg _
  have hp : 0 < (1 + x) := by linarith
  have h1 := rpow_half_sub_le hτ hj
  have h2 : (1 + x) ^ (N + j) ≤ (1 + x) ^ (N + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 := hK x hx0
  unfold ejW
  rw [rpow_neg_two_eq hp.le, mul_one_div]
  rw [le_div_iff₀ (by positivity)]
  have he : 0 ≤ Real.exp (-(π * 1 * x)) := (Real.exp_pos _).le
  have hxx : Real.exp (-(π * 1 * x)) = Real.exp (-(π * x)) := by ring_nf
  rw [hxx]
  calc x ^ ((1 / 2 : ℝ) - (j : ℝ)) * (1 + x) ^ (N + j) * Real.exp (-(π * x)) * (1 + x) ^ 2
      ≤ (4 * (1 + x)) * (1 + x) ^ (N + 2) * Real.exp (-(π * x)) * (1 + x) ^ 2 := by gcongr
    _ = 4 * ((1 + x) ^ (N + 5) * Real.exp (-(π * x))) := by ring
    _ ≤ 4 * K := by gcongr

/-- The left-edge trace of `W` is `f` off `0`, `W 0 = 0`, and `f` has the graded bound with `a = 1/2`, `b = 1`: then `W` satisfies (M3)
at the left edge with `α = 1/2`. -/
theorem edge0_of_EJ {W : ℂ → ℂ} {f : ℝ → ℂ} {N : ℕ} {M : ℝ} (hf : EJ f (1 / 2) N 1 M)
    (heq : ∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = f τ) (h0 : W 0 = 0) : StripEdge0 (1 / 2 : ℝ) W := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hd1 : ∀ τ : ℝ, τ ≠ 0 → deriv (stripEdge0 W) τ = deriv f τ := fun τ hτ => by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hS.mem_nhds hτ] with t ht using heq t ht
  have hd2 : ∀ τ : ℝ, τ ≠ 0 → deriv (deriv (stripEdge0 W)) τ = deriv (deriv f) τ := fun τ hτ => by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hS.mem_nhds hτ] with t ht using hd1 t ht
  have hW0 : stripEdge0 W 0 = 0 := by simp [stripEdge0, h0]
  obtain ⟨K, hK0, hK⟩ := ejW_far_le N
  have hM := hf.hM
  refine ⟨hf.c2.congr heq, ⟨M * 2 ^ (N + 2), fun τ hτ hτ1 => ?_⟩, ⟨4 * M * K, fun τ hτ => ?_⟩⟩
  · have h0' : 0 < |τ| := abs_pos.mpr hτ
    have hone : (1 + |τ|) ≤ 2 := by linarith
    have hexp : Real.exp (-(π * 1 * |τ|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have key : ∀ j : ℕ, j ≤ 2 → M * ejW (1 / 2) N 1 j τ ≤ M * 2 ^ (N + 2) * |τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) := by
      intro j hj
      unfold ejW
      have hp : 0 < |τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) := Real.rpow_pos_of_pos h0' _
      have h1 : (1 + |τ|) ^ (N + j) ≤ 2 ^ (N + 2) := by
        calc (1 + |τ|) ^ (N + j) ≤ 2 ^ (N + j) := pow_le_pow_left₀ (by linarith) hone _
          _ ≤ 2 ^ (N + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc M * (|τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) * (1 + |τ|) ^ (N + j) * Real.exp (-(π * 1 * |τ|)))
          ≤ M * (|τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) * 2 ^ (N + 2) * 1) := by gcongr
        _ = _ := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hW0, sub_zero, heq τ hτ]
      have := (hf.b0 τ hτ).trans (key 0 (by norm_num))
      simpa using this
    · rw [hd1 τ hτ]
      have := (hf.b1 τ hτ).trans (key 1 (by norm_num))
      simpa using this
    · rw [hd2 τ hτ]
      have := (hf.b2 τ hτ).trans (key 2 (by norm_num))
      simpa using this
  · have hτ' : τ ≠ 0 := by
      intro h; rw [h] at hτ; simp at hτ; linarith
    have hw := fun j (hj : j ≤ 2) => hK τ hτ j hj
    have hneg : 0 ≤ (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [heq τ hτ']
      calc _ ≤ M * ejW (1 / 2) N 1 0 τ := hf.b0 τ hτ'
        _ ≤ M * (K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 0 (by norm_num)
        _ ≤ _ := by nlinarith [mul_nonneg hM (mul_nonneg hK0 hneg)]
    · rw [hd1 τ hτ']
      calc _ ≤ M * ejW (1 / 2) N 1 1 τ := hf.b1 τ hτ'
        _ ≤ M * (K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 1 (by norm_num)
        _ ≤ _ := by nlinarith [mul_nonneg hM (mul_nonneg hK0 hneg)]
    · rw [hd2 τ hτ']
      calc _ ≤ M * ejW (1 / 2) N 1 2 τ := hf.b2 τ hτ'
        _ ≤ M * (K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 2 (by norm_num)
        _ ≤ _ := by nlinarith [mul_nonneg hM (mul_nonneg hK0 hneg)]

theorem EJ.cast {f : ℝ → ℂ} {a a' b b' M : ℝ} {N : ℕ} (h : EJ f a N b M) (ha : a = a') (hb : b = b') :
    EJ f a' N b' M := by
  subst ha; subst hb; exact h

/-! ### Graded `C²` envelopes restricted to a subset `S ⊆ {τ ≠ 0}` (`near` `0 < |τ| ≤ 1` vs `far` `1/2 ≤ |τ|`) -/

/-- Graded `C²` envelope of `f` (`C²` on `{τ ≠ 0}`) with bounds holding on a subset `S ⊆ {τ ≠ 0}`. -/
structure EJOn (S : Set ℝ) (f : ℝ → ℂ) (a : ℝ) (N : ℕ) (b M : ℝ) : Prop where
  hM : 0 ≤ M
  c2 : ContDiffOn ℝ 2 f {τ : ℝ | τ ≠ 0}
  b0 : ∀ τ ∈ S, τ ≠ 0 → ‖f τ‖ ≤ M * ejW a N b 0 τ
  b1 : ∀ τ ∈ S, τ ≠ 0 → ‖deriv f τ‖ ≤ M * ejW a N b 1 τ
  b2 : ∀ τ ∈ S, τ ≠ 0 → ‖deriv (deriv f) τ‖ ≤ M * ejW a N b 2 τ

lemma EJ.to_on {S : Set ℝ} {f : ℝ → ℂ} {a b M : ℝ} {N : ℕ} (hf : EJ f a N b M) : EJOn S f a N b M where
  hM := hf.hM
  c2 := hf.c2
  b0 τ _ hτ := hf.b0 τ hτ
  b1 τ _ hτ := hf.b1 τ hτ
  b2 τ _ hτ := hf.b2 τ hτ

theorem EJOn.mul {S : Set ℝ} {f g : ℝ → ℂ} {a a' b b' M M' : ℝ} {N N' : ℕ}
    (hf : EJOn S f a N b M) (hg : EJOn S g a' N' b' M') :
    EJOn S (fun t => f t * g t) (a + a') (N + N') (b + b') (4 * M * M') where
  hM := by have := hf.hM; have := hg.hM; positivity
  c2 := hf.c2.mul hg.c2
  b0 τ hS hτ := by
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 0) hτ
    have e0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have e0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have w := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 0) hτ
    have hM := hf.hM; have hM' := hg.hM
    simp only [norm_mul]
    calc ‖f τ‖ * ‖g τ‖ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 0 τ) :=
          mul_le_mul (hf.b0 τ hS hτ) (hg.b0 τ hS hτ) (norm_nonneg _) (by positivity)
      _ = M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by rw [← w]; ring
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by
          have : 0 ≤ M * M' * ejW (a + a') (N + N') (b + b') 0 τ := by positivity
          nlinarith
  b1 τ hS hτ := by
    have hO : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
    obtain ⟨h1, -⟩ := prod_deriv_on hO hf.c2 hg.c2 (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)
    rw [h1]
    have w01 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 1) hτ
    have w10 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 1) (k := 0) hτ
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 1) hτ
    have e0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have e0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have e1 := ejW_pos (a := a) (b := b) (N := N) (j := 1) hτ
    have e1' := ejW_pos (a := a') (b := b') (N := N') (j := 1) hτ
    have hM := hf.hM; have hM' := hg.hM
    have t1 : ‖deriv f τ * g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 1 τ) * (M' * ejW a' N' b' 0 τ) :=
            mul_le_mul (hf.b1 τ hS hτ) (hg.b0 τ hS hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w10]; ring
    have t2 : ‖f τ * deriv g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 1 τ) :=
            mul_le_mul (hf.b0 τ hS hτ) (hg.b1 τ hS hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w01]; ring
    calc _ ≤ ‖deriv f τ * g τ‖ + ‖f τ * deriv g τ‖ := norm_add_le _ _
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by
          have : 0 ≤ M * M' * ejW (a + a') (N + N') (b + b') 1 τ := by positivity
          nlinarith
  b2 τ hS hτ := by
    have hO : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
    obtain ⟨-, h2⟩ := prod_deriv_on hO hf.c2 hg.c2 (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ)
    rw [h2]
    have w20 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 2) (k := 0) hτ
    have w11 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 1) (k := 1) hτ
    have w02 := ejW_mul (a := a) (a' := a') (b := b) (b' := b') (N := N) (N' := N') (j := 0) (k := 2) hτ
    have hp := ejW_pos (a := a + a') (b := b + b') (N := N + N') (j := 2) hτ
    have e0 := ejW_pos (a := a) (b := b) (N := N) (j := 0) hτ
    have e0' := ejW_pos (a := a') (b := b') (N := N') (j := 0) hτ
    have e1 := ejW_pos (a := a) (b := b) (N := N) (j := 1) hτ
    have e1' := ejW_pos (a := a') (b := b') (N := N') (j := 1) hτ
    have e2 := ejW_pos (a := a) (b := b) (N := N) (j := 2) hτ
    have e2' := ejW_pos (a := a') (b := b') (N := N') (j := 2) hτ
    have hM := hf.hM; have hM' := hg.hM
    have t1 : ‖deriv (deriv f) τ * g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 2 τ) * (M' * ejW a' N' b' 0 τ) :=
            mul_le_mul (hf.b2 τ hS hτ) (hg.b0 τ hS hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w20]; ring
    have t2 : ‖deriv f τ * deriv g τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 1 τ) * (M' * ejW a' N' b' 1 τ) :=
            mul_le_mul (hf.b1 τ hS hτ) (hg.b1 τ hS hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w11]; ring
    have t3 : ‖f τ * deriv (deriv g) τ‖ ≤ M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
      rw [norm_mul]
      calc _ ≤ (M * ejW a N b 0 τ) * (M' * ejW a' N' b' 2 τ) :=
            mul_le_mul (hf.b0 τ hS hτ) (hg.b2 τ hS hτ) (norm_nonneg _) (by positivity)
        _ = _ := by rw [← w02]; ring
    calc ‖deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ‖
        ≤ ‖deriv (deriv f) τ * g τ‖ + ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ + ‖f τ * deriv (deriv g) τ‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 4 * M * M' * ejW (a + a') (N + N') (b + b') 2 τ := by
          have : ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ = 2 * ‖deriv f τ * deriv g τ‖ := by
            rw [norm_mul]; simp
          linarith

theorem EJOn.const_mul {S : Set ℝ} {f : ℝ → ℂ} {a b M : ℝ} {N : ℕ} (hf : EJOn S f a N b M) (k : ℂ) :
    EJOn S (fun t => k * f t) a N b (‖k‖ * M) where
  hM := mul_nonneg (norm_nonneg _) hf.hM
  c2 := contDiffOn_const.mul hf.c2
  b0 τ hS hτ := by
    rw [norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b0 τ hS hτ) (norm_nonneg _)
  b1 τ hS hτ := by
    have : deriv (fun t => k * f t) τ = k * deriv f τ := deriv_const_mul_field k
    rw [this, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b1 τ hS hτ) (norm_nonneg _)
  b2 τ hS hτ := by
    have h1 : deriv (fun t => k * f t) = fun t => k * deriv f t := funext fun t => deriv_const_mul_field k
    rw [h1]
    have : deriv (fun t => k * deriv f t) τ = k * deriv (deriv f) τ := deriv_const_mul_field k
    rw [this, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hf.b2 τ hS hτ) (norm_nonneg _)

theorem EJOn.cast {S : Set ℝ} {f : ℝ → ℂ} {a a' b b' M : ℝ} {N : ℕ}
    (h : EJOn S f a N b M) (ha : a = a') (hb : b = b') : EJOn S f a' N b' M := by
  subst ha; subst hb; exact h

theorem EJOn.of_far_poly_exp {f : ℝ → ℂ} {N : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hc2 : ContDiffOn ℝ 2 f {τ : ℝ | τ ≠ 0})
    (hb : ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖f τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) ∧
      ‖deriv f τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) ∧
      ‖deriv (deriv f) τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|))) :
    EJOn {τ : ℝ | 1 / 2 ≤ |τ|} f 0 N 1 M where
  hM := hM
  c2 := hc2
  b0 τ hS hτ := by
    have h := (hb τ hS).1
    have hg := ejW_ge (b := 1) (N := N) 0 hτ
    rw [show π * (1 : ℝ) * |τ| = π * |τ| from by ring] at hg
    calc ‖f τ‖ ≤ M * ((1 + |τ|) ^ N * Real.exp (-(π * |τ|))) := by linarith
      _ ≤ M * ejW 0 N 1 0 τ := mul_le_mul_of_nonneg_left hg hM
  b1 τ hS hτ := by
    have h := (hb τ hS).2.1
    have hg := ejW_ge (b := 1) (N := N) 1 hτ
    rw [show π * (1 : ℝ) * |τ| = π * |τ| from by ring] at hg
    calc ‖deriv f τ‖ ≤ M * ((1 + |τ|) ^ N * Real.exp (-(π * |τ|))) := by linarith
      _ ≤ M * ejW 0 N 1 1 τ := mul_le_mul_of_nonneg_left hg hM
  b2 τ hS hτ := by
    have h := (hb τ hS).2.2
    have hg := ejW_ge (b := 1) (N := N) 2 hτ
    rw [show π * (1 : ℝ) * |τ| = π * |τ| from by ring] at hg
    calc ‖deriv (deriv f) τ‖ ≤ M * ((1 + |τ|) ^ N * Real.exp (-(π * |τ|))) := by linarith
      _ ≤ M * ejW 0 N 1 2 τ := mul_le_mul_of_nonneg_left hg hM

lemma ejW_zero_far_le (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| → ∀ j : ℕ, j ≤ 2 →
    ejW 0 N 1 j τ ≤ 4 * K * (1 + |τ|) ^ (-(2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := poly_exp_le_n (N + 4)
  refine ⟨K, hK0, fun τ hτ j hj => ?_⟩
  set x : ℝ := |τ|
  have hx0 : 0 < x := by positivity
  have hp : 0 < 1 + x := by linarith
  have h1 : x ^ ((0 : ℝ) - (j : ℝ)) ≤ 4 := by
    rw [zero_sub, Real.rpow_neg hx0.le, Real.rpow_natCast]
    have hpow : (1 / 4 : ℝ) ≤ x ^ j := by
      rcases le_or_gt x 1 with h | h
      · calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
          _ ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
          _ ≤ x ^ j := pow_le_pow_left₀ (by norm_num) hτ j
      · have : 1 ≤ x ^ j := one_le_pow₀ h.le
        linarith
    exact inv_le_of_inv_le₀ (by norm_num : (0 : ℝ) < 4) (by norm_num; exact hpow)
  have h2 : (1 + x) ^ (N + j) ≤ (1 + x) ^ (N + 2) := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 := hK x hx0.le
  unfold ejW
  rw [rpow_neg_two_eq hp.le, mul_one_div, le_div_iff₀ (by positivity)]
  have he : 0 ≤ Real.exp (-(π * 1 * x)) := (Real.exp_pos _).le
  have hxx : Real.exp (-(π * 1 * x)) = Real.exp (-(π * x)) := by ring_nf
  rw [hxx]
  calc x ^ ((0 : ℝ) - (j : ℝ)) * (1 + x) ^ (N + j) * Real.exp (-(π * x)) * (1 + x) ^ 2
      ≤ 4 * (1 + x) ^ (N + 2) * Real.exp (-(π * x)) * (1 + x) ^ 2 := by gcongr
    _ = 4 * ((1 + x) ^ (N + 4) * Real.exp (-(π * x))) := by ring
    _ ≤ 4 * K := by gcongr

/-- Combined near (`0 < |τ| ≤ 1`, `a = 1/2`) and far (`1/2 ≤ |τ|`, `a = 0`) `EJOn` envelopes yield `StripEdge0 (1/2)`. -/
theorem edge0_of_EJOn_near_far {W : ℂ → ℂ} {fnear ffar : ℝ → ℂ} {Nn Nf : ℕ} {Mn Mf : ℝ}
    (hf_near : EJOn {τ : ℝ | τ ≠ 0 ∧ |τ| ≤ 1} fnear (1 / 2) Nn 1 Mn)
    (hf_far : EJOn {τ : ℝ | 1 / 2 ≤ |τ|} ffar 0 Nf 1 Mf)
    (hc2 : ContDiffOn ℝ 2 (stripEdge0 W) {τ : ℝ | τ ≠ 0})
    (heq_near : ∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = fnear τ)
    (heq_far : ∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = ffar τ)
    (h0 : W 0 = 0) : StripEdge0 (1 / 2 : ℝ) W := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hd_eq : ∀ {g : ℝ → ℂ}, (∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = g τ) →
      (∀ τ : ℝ, τ ≠ 0 → deriv (stripEdge0 W) τ = deriv g τ) ∧
      (∀ τ : ℝ, τ ≠ 0 → deriv (deriv (stripEdge0 W)) τ = deriv (deriv g) τ) := by
    intro g hg
    have hd1 : ∀ τ : ℝ, τ ≠ 0 → deriv (stripEdge0 W) τ = deriv g τ := fun τ hτ =>
      Filter.EventuallyEq.deriv_eq (by filter_upwards [hS.mem_nhds hτ] with t ht using hg t ht)
    refine ⟨hd1, fun τ hτ => Filter.EventuallyEq.deriv_eq (by filter_upwards [hS.mem_nhds hτ] with t ht using hd1 t ht)⟩
  obtain ⟨hd1_n, hd2_n⟩ := hd_eq heq_near
  obtain ⟨hd1_f, hd2_f⟩ := hd_eq heq_far
  have hW0 : stripEdge0 W 0 = 0 := by simp [stripEdge0, h0]
  obtain ⟨K, hK0, hK⟩ := ejW_zero_far_le Nf
  have hMn := hf_near.hM
  have hMf := hf_far.hM
  refine ⟨hc2, ⟨Mn * 2 ^ (Nn + 2), fun τ hτ hτ1 => ?_⟩, ⟨4 * Mf * K, fun τ hτ => ?_⟩⟩
  · have h0' : 0 < |τ| := abs_pos.mpr hτ
    have hone : (1 + |τ|) ≤ 2 := by linarith
    have hexp : Real.exp (-(π * 1 * |τ|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have key : ∀ j : ℕ, j ≤ 2 → Mn * ejW (1 / 2) Nn 1 j τ ≤ Mn * 2 ^ (Nn + 2) * |τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) := by
      intro j hj
      unfold ejW
      have hp : 0 < |τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) := Real.rpow_pos_of_pos h0' _
      have h1 : (1 + |τ|) ^ (Nn + j) ≤ 2 ^ (Nn + 2) := by
        calc (1 + |τ|) ^ (Nn + j) ≤ 2 ^ (Nn + j) := pow_le_pow_left₀ (by linarith) hone _
          _ ≤ 2 ^ (Nn + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc Mn * (|τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) * (1 + |τ|) ^ (Nn + j) * Real.exp (-(π * 1 * |τ|)))
          ≤ Mn * (|τ| ^ ((1 / 2 : ℝ) - (j : ℝ)) * 2 ^ (Nn + 2) * 1) := by gcongr
        _ = _ := by ring
    have hmem : τ ∈ {τ : ℝ | τ ≠ 0 ∧ |τ| ≤ 1} := ⟨hτ, hτ1⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hW0, sub_zero, heq_near τ hτ]
      have := (hf_near.b0 τ hmem hτ).trans (key 0 (by norm_num))
      simpa using this
    · rw [hd1_n τ hτ]
      have := (hf_near.b1 τ hmem hτ).trans (key 1 (by norm_num))
      simpa using this
    · rw [hd2_n τ hτ]
      have := (hf_near.b2 τ hmem hτ).trans (key 2 (by norm_num))
      simpa using this
  · have hτ' : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
    have hw := fun j (hj : j ≤ 2) => hK τ hτ j hj
    refine ⟨?_, ?_, ?_⟩
    · rw [heq_far τ hτ']
      calc _ ≤ Mf * ejW 0 Nf 1 0 τ := hf_far.b0 τ hτ hτ'
        _ ≤ Mf * (4 * K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 0 (by norm_num)
        _ = _ := by ring
    · rw [hd1_f τ hτ']
      calc _ ≤ Mf * ejW 0 Nf 1 1 τ := hf_far.b1 τ hτ hτ'
        _ ≤ Mf * (4 * K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 1 (by norm_num)
        _ = _ := by ring
    · rw [hd2_f τ hτ']
      calc _ ≤ Mf * ejW 0 Nf 1 2 τ := hf_far.b2 τ hτ hτ'
        _ ≤ Mf * (4 * K * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr; exact hw 2 (by norm_num)
        _ = _ := by ring

end FormalResearch.SignUncertainty

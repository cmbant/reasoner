module

public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.CohnElkies.ParametricIterated

/-!
# `y`-derivative bounds of the Gaussian transforms of the seeds, large `|y|` (`u1c:U1`, `(e27)`)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, the symbol bounds `(e27)` for the cancelled-origin
seeds `f₁`, `g₁`, `g₁'`.  Each seed has a Gaussian transform
`airyTwistedLaplaceC X y = ceK (4π y)^{-1/2} J(y)` on `Re y > 0`, with `J` a one- or two-dimensional integral of
`e^{-y(t+s)/2 - (t-s)²/(4y)}` against rapidly decaying smooth functions.

Method (polynomial weights, no heat equation).  Since `∂_y e^{-y(t+s)/2 - (t-s)²/(4y)} = (-(t+s)/2 + (t-s)²/(4y²)) e^{...}`,
every `y`-derivative of `J` is a linear combination, with coefficients `c y^{-m}`, of the same integrals with `f, g`
replaced by `t^a f, s^b g`.  The generic IBP expansion `gaussian_2d_ibp_general` (resp. `gaussian_1d_ibp_general`)
then gives `J^{(r)} = O(|y|^{-2-r})`, because `(t^a f)(0) = 0` for `a ≥ 1` and `(t^a f)'(0) = 0` for `a ≥ 2`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### The decay class `ExpDec` and multiplication by `t` -/

/-- Smooth functions all of whose derivatives decay like `(1+t)^{-k} e^{-t/4}` on `[0, ∞)`. -/
structure ExpDec (φ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ φ
  dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t →
    (1 + t) ^ k * ‖iteratedDeriv n φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t)

/-- Multiplication by the coordinate. -/
def tmul (φ : ℝ → ℝ) : ℝ → ℝ := fun t => t * φ t

lemma iteratedDeriv_tmul {φ : ℝ → ℝ} (hφ : ContDiff ℝ ⊤ φ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (tmul φ) t = t * iteratedDeriv n φ t + n * iteratedDeriv (n - 1) φ t := by
  induction n generalizing t with
  | zero => simp [tmul]
  | succ k ih =>
    have hfun : iteratedDeriv k (tmul φ) = fun t => t * iteratedDeriv k φ t + k * iteratedDeriv (k - 1) φ t :=
      funext ih
    rw [iteratedDeriv_succ, hfun]
    have hd : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m φ) := fun m => hφ.differentiable_iteratedDeriv m (by simp)
    have h1 : HasDerivAt (fun x => x * iteratedDeriv k φ x) (1 * iteratedDeriv k φ t + t * iteratedDeriv (k + 1) φ t) t := by
      have := (hasDerivAt_id' t).mul ((hd k t).hasDerivAt)
      rwa [← iteratedDeriv_succ] at this
    have h2 : HasDerivAt (fun x => (k : ℝ) * iteratedDeriv (k - 1) φ x) ((k : ℝ) * iteratedDeriv k φ t) t := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hasDerivAt_const t (0 : ℝ)
      · have := ((hd (k - 1) t).hasDerivAt).const_mul (k : ℝ)
        rwa [← iteratedDeriv_succ, Nat.sub_add_cancel hk] at this
    have h3 : HasDerivAt (fun x => x * iteratedDeriv k φ x + (k : ℝ) * iteratedDeriv (k - 1) φ x)
        (1 * iteratedDeriv k φ t + t * iteratedDeriv (k + 1) φ t + (k : ℝ) * iteratedDeriv k φ t) t := h1.add h2
    rw [h3.deriv]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; ring

lemma ExpDec.mulT {φ : ℝ → ℝ} (h : ExpDec φ) : ExpDec (tmul φ) := by
  refine ⟨contDiff_id.mul h.smooth, fun n k => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := h.dec n (k + 1)
  obtain ⟨C₂, hC₂, h₂⟩ := h.dec (n - 1) k
  refine ⟨C₁ + n * C₂ + 1, by positivity, fun t ht => ?_⟩
  rw [iteratedDeriv_tmul h.smooth, Real.norm_eq_abs] at *
  have e1 := h₁ t ht; have e2 := h₂ t ht
  simp only [Real.norm_eq_abs] at e1 e2
  have hp : 0 ≤ Real.exp (-(1 / 4 : ℝ) * t) := (Real.exp_pos _).le
  calc (1 + t) ^ k * |t * iteratedDeriv n φ t + n * iteratedDeriv (n - 1) φ t|
      ≤ (1 + t) ^ k * (t * |iteratedDeriv n φ t| + n * |iteratedDeriv (n - 1) φ t|) := by
        gcongr
        calc _ ≤ |t * iteratedDeriv n φ t| + |(n : ℝ) * iteratedDeriv (n - 1) φ t| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ht, Nat.abs_cast]
    _ = t * ((1 + t) ^ k * |iteratedDeriv n φ t|) + n * ((1 + t) ^ k * |iteratedDeriv (n - 1) φ t|) := by ring
    _ ≤ (1 + t) * ((1 + t) ^ k * |iteratedDeriv n φ t|) + n * (C₂ * Real.exp (-(1 / 4 : ℝ) * t)) := by
        gcongr
        · linarith
    _ = (1 + t) ^ (k + 1) * |iteratedDeriv n φ t| + n * (C₂ * Real.exp (-(1 / 4 : ℝ) * t)) := by ring
    _ ≤ C₁ * Real.exp (-(1 / 4 : ℝ) * t) + n * (C₂ * Real.exp (-(1 / 4 : ℝ) * t)) := by gcongr
    _ ≤ (C₁ + n * C₂ + 1) * Real.exp (-(1 / 4 : ℝ) * t) := by nlinarith

lemma ExpDec.integrable_pow_mul {φ : ℝ → ℝ} (h : ExpDec φ) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ k * |φ t|) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := h.dec 0 k
  refine (integrableOn_Ioi_exp_neg_quarter C).mono' ?_ ?_
  · exact (((continuous_const.add continuous_id).pow k).mul (h.smooth.continuous.abs)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have := hb t (le_of_lt (mem_Ioi.mp ht))
    rw [iteratedDeriv_zero, Real.norm_eq_abs] at this
    rw [Real.norm_of_nonneg (by have := mem_Ioi.mp ht; positivity)]
    exact this

/-! ### Decay on the right half-plane -/

/-- `h = O(‖y‖^{-k})` on `{Re y > 0, ‖y‖ ≥ 1}`. -/
def DecayOn (k : ℝ) (h : ℂ → ℂ) : Prop :=
  ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖h y‖ ≤ C * ‖y‖ ^ (-k)

lemma DecayOn.mono {k k' : ℝ} (hk : k' ≤ k) {h : ℂ → ℂ} (hh : DecayOn k h) : DecayOn k' h := by
  obtain ⟨C, hC, hb⟩ := hh
  refine ⟨C, hC, fun {y} hy hy1 => (hb hy hy1).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)) hC.le

lemma DecayOn.add {k : ℝ} {h₁ h₂ : ℂ → ℂ} (h1 : DecayOn k h₁) (h2 : DecayOn k h₂) :
    DecayOn k (fun y => h₁ y + h₂ y) := by
  obtain ⟨C₁, hC₁, b₁⟩ := h1; obtain ⟨C₂, hC₂, b₂⟩ := h2
  refine ⟨C₁ + C₂, by positivity, fun {y} hy hy1 => (norm_add_le _ _).trans ?_⟩
  linarith [b₁ hy hy1, b₂ hy hy1]

lemma DecayOn.const_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) (c : ℂ) :
    DecayOn k (fun y => c * h y) := by
  obtain ⟨C, hC, b⟩ := hh
  refine ⟨(‖c‖ + 1) * C, by positivity, fun {y} hy hy1 => ?_⟩
  rw [norm_mul]
  calc ‖c‖ * ‖h y‖ ≤ ‖c‖ * (C * ‖y‖ ^ (-k)) := mul_le_mul_of_nonneg_left (b hy hy1) (norm_nonneg _)
    _ ≤ (‖c‖ + 1) * C * ‖y‖ ^ (-k) := by
      have : 0 ≤ C * ‖y‖ ^ (-k) := mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
      nlinarith

lemma DecayOn.congr {k : ℝ} {h h' : ℂ → ℂ} (hh : DecayOn k h) (he : ∀ {y : ℂ}, 0 < y.re → h y = h' y) :
    DecayOn k h' := by
  obtain ⟨C, hC, b⟩ := hh
  exact ⟨C, hC, fun {y} hy hy1 => by rw [← he hy]; exact b hy hy1⟩

/-- Dividing by `y^m` gains `m` powers of decay. -/
lemma DecayOn.div_pow {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) (m : ℕ) :
    DecayOn (k + m) (fun y => h y / y ^ m) := by
  obtain ⟨C, hC, b⟩ := hh
  refine ⟨C, hC, fun {y} hy hy1 => ?_⟩
  have hy0 : 0 < ‖y‖ := by linarith
  rw [norm_div, norm_pow, neg_add, Real.rpow_add hy0, ← mul_assoc, Real.rpow_neg hy0.le (m : ℝ), Real.rpow_natCast,
    ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (b hy hy1) (by positivity)

/-- Multiplying by `y^{-a}` (complex power, `a` real) gains `a` powers of decay. -/
lemma DecayOn.cpow_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) (a : ℝ) :
    DecayOn (k + a) (fun y => y ^ (-(a : ℂ)) * h y) := by
  obtain ⟨C, hC, b⟩ := hh
  refine ⟨C, hC, fun {y} hy hy1 => ?_⟩
  have hy0 : 0 < ‖y‖ := by linarith
  have hyne : y ≠ 0 := fun h0 => by simp [h0] at hy0
  rw [norm_mul, show (-(a : ℂ)) = ((-a : ℝ) : ℂ) by push_cast; rfl, norm_cpow_ofReal_exponent hyne, neg_add,
    Real.rpow_add hy0]
  calc ‖y‖ ^ (-a) * ‖h y‖ ≤ ‖y‖ ^ (-a) * (C * ‖y‖ ^ (-k)) :=
        mul_le_mul_of_nonneg_left (b hy hy1) (Real.rpow_nonneg hy0.le _)
    _ = C * (‖y‖ ^ (-k) * ‖y‖ ^ (-a)) := by ring

/-! ### The two-dimensional family `Jp f g` -/

/-- The Gaussian exponential `e^{-y(t+s)/2 - (t-s)²/(4y)}`. -/
noncomputable def gexp (y : ℂ) (t s : ℝ) : ℂ :=
  Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))

lemma gexp_eq (y : ℂ) (t s : ℝ) :
    gexp y t s = Complex.exp (-y * (t : ℂ) / 2) * Complex.exp (-y * (s : ℂ) / 2) * gaussKern y (t - s) := by
  unfold gexp gaussKern
  rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_gexp_le {y : ℂ} (hy : 0 < y.re) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : ‖gexp y t s‖ ≤ 1 := by
  rw [gexp_eq, norm_mul, norm_mul]
  have h12 := mul_le_mul (norm_exp_neg_mul_half_le hy ht) (norm_exp_neg_mul_half_le hy hs) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1)
  exact (mul_le_mul h12 (norm_gaussKern_le hy _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq
    (by norm_num)

lemma continuous_gexp (y : ℂ) : Continuous fun p : ℝ × ℝ => gexp y p.1 p.2 := by
  unfold gexp
  fun_prop

/-- Product measure on `(0,∞)²`. -/
noncomputable abbrev μ2 : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

/-- `J(f,g)(y) = ∫∫_{(0,∞)²} f(t) g(s) e^{-y(t+s)/2 - (t-s)²/(4y)}`, as an integral over the product measure. -/
noncomputable def Jp (f g : ℝ → ℝ) (y : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, ((f p.1 * g p.2 : ℝ) : ℂ) * gexp y p.1 p.2 ∂μ2

lemma integrable_abs_mul {f g : ℝ → ℝ} (hf : ExpDec f) (hg : ExpDec g) {a b : ℕ} :
    Integrable (fun p : ℝ × ℝ => ((1 + p.1) ^ a * |f p.1|) * ((1 + p.2) ^ b * |g p.2|)) μ2 :=
  Integrable.mul_prod (hf.integrable_pow_mul a) (hg.integrable_pow_mul b)

lemma integrable_Jp {f g : ℝ → ℝ} (hf : ExpDec f) (hg : ExpDec g) {y : ℂ} (hy : 0 < y.re) :
    Integrable (fun p : ℝ × ℝ => ((f p.1 * g p.2 : ℝ) : ℂ) * gexp y p.1 p.2) μ2 := by
  have hI := integrable_abs_mul hf hg (a := 0) (b := 0)
  refine hI.mono' ?_ ?_
  · exact (((Complex.continuous_ofReal.comp ((hf.smooth.continuous.comp continuous_fst).mul
      (hg.smooth.continuous.comp continuous_snd)))).mul (continuous_gexp y)).aestronglyMeasurable
  · refine paramIt_ae_prod_Ioi (P := fun p => ‖((f p.1 * g p.2 : ℝ) : ℂ) * gexp y p.1 p.2‖ ≤
      ((1 + p.1) ^ 0 * |f p.1|) * ((1 + p.2) ^ 0 * |g p.2|)) fun t ht s hs => ?_
    simp only [pow_zero, one_mul]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |f t| * |g s| * ‖gexp y t s‖ ≤ |f t| * |g s| * 1 :=
          mul_le_mul_of_nonneg_left (norm_gexp_le hy (le_of_lt ht) (le_of_lt hs)) (by positivity)
      _ = _ := mul_one _

lemma Jp_eq_iterated (f g : ℝ → ℝ) (hf : ExpDec f) (hg : ExpDec g) {y : ℂ} (hy : 0 < y.re) :
    Jp f g y = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) *
      Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) :=
  integral_prod _ (integrable_Jp hf hg hy)

lemma hasDerivAt_gexp {y : ℂ} (hy : y ≠ 0) (t s : ℝ) :
    HasDerivAt (fun y : ℂ => gexp y t s)
      (gexp y t s * (-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))) y := by
  unfold gexp
  have h1 : HasDerivAt (fun y : ℂ => -y * ((t + s : ℝ) : ℂ) / 2) (-((t + s : ℝ) : ℂ) / 2) y := by
    have := ((hasDerivAt_id y).neg.mul_const (((t + s : ℝ) : ℂ))).div_const 2
    simpa using this
  have h2 : HasDerivAt (fun y : ℂ => ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))
      (-(((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))) y := by
    have h4 : HasDerivAt (fun y : ℂ => 4 * y) 4 y := by simpa using (hasDerivAt_id y).const_mul (4 : ℂ)
    have h4ne : (4 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy
    have := (hasDerivAt_const y (((t - s : ℝ) : ℂ) ^ 2)).div h4 h4ne
    convert this using 1
    field_simp
    ring
  have h3 : HasDerivAt (fun y : ℂ => -y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))
      (-((t + s : ℝ) : ℂ) / 2 - -(((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))) y := h1.sub h2
  have h5 := h3.cexp
  convert h5 using 1
  ring

/-- **Differentiation under the integral** (complex parameter `y`, `Re y > 0`):
`∂_y J(f,g) = -½ (J(tf,g) + J(f,sg)) + (4y²)⁻¹ (J(t²f,g) - 2 J(tf,sg) + J(f,s²g))`. -/
theorem hasDerivAt_Jp {f g : ℝ → ℝ} (hf : ExpDec f) (hg : ExpDec g) {y₀ : ℂ} (hy₀ : 0 < y₀.re) :
    HasDerivAt (Jp f g)
      (-(1 / 2 : ℂ) * (Jp (tmul f) g y₀ + Jp f (tmul g) y₀) +
        (1 / (4 * y₀ ^ 2)) * (Jp (tmul (tmul f)) g y₀ - 2 * Jp (tmul f) (tmul g) y₀ + Jp f (tmul (tmul g)) y₀)) y₀ := by
  have hy0 : y₀ ≠ 0 := fun h => by simp [h] at hy₀
  set r : ℝ := ‖y₀‖ / 2 with hr
  have hrpos : 0 < r := by have : 0 < ‖y₀‖ := norm_pos_iff.mpr hy0; positivity
  set S : Set ℂ := {y | 0 < y.re} ∩ {y | r < ‖y‖} with hS
  have hSnhds : S ∈ 𝓝 y₀ := by
    refine Filter.inter_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hy₀)
      ((isOpen_lt continuous_const continuous_norm).mem_nhds ?_)
    have : 0 < ‖y₀‖ := norm_pos_iff.mpr hy0
    show r < ‖y₀‖; rw [hr]; linarith
  let F : ℂ → ℝ × ℝ → ℂ := fun y p => ((f p.1 * g p.2 : ℝ) : ℂ) * gexp y p.1 p.2
  let F' : ℂ → ℝ × ℝ → ℂ := fun y p => F y p * (-((p.1 + p.2 : ℝ) : ℂ) / 2 + ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))
  let K : ℝ := 1 / 2 + 1 / (4 * r ^ 2)
  let bound : ℝ × ℝ → ℝ := fun p => K * (((1 + p.1) ^ 2 * |f p.1|) * ((1 + p.2) ^ 2 * |g p.2|))
  have hfc : Continuous fun p : ℝ × ℝ => ((f p.1 * g p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hf.smooth.continuous.comp continuous_fst).mul (hg.smooth.continuous.comp continuous_snd))
  have hF'c : Continuous (F' y₀) := by
    show Continuous fun p : ℝ × ℝ => ((f p.1 * g p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2 *
      (-((p.1 + p.2 : ℝ) : ℂ) / 2 + ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y₀ ^ 2))
    refine (hfc.mul (continuous_gexp y₀)).mul ?_
    fun_prop
  have hbi : Integrable bound μ2 := (integrable_abs_mul hf hg (a := 2) (b := 2)).const_mul K
  have hbd : ∀ᵐ p ∂μ2, ∀ y ∈ S, ‖F' y p‖ ≤ bound p := by
    refine paramIt_ae_prod_Ioi (P := fun p => ∀ y ∈ S, ‖F' y p‖ ≤ bound p) fun t ht s hs y hyS => ?_
    have ht0 : 0 ≤ t := le_of_lt ht
    have hs0 : 0 ≤ s := le_of_lt hs
    obtain ⟨hyre, hyr⟩ := hyS
    have hynorm : r < ‖y‖ := hyr
    show ‖((f t * g s : ℝ) : ℂ) * gexp y t s * (-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2))‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hW : ‖-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)‖ ≤ K * ((1 + t) ^ 2 * (1 + s) ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖-((t + s : ℝ) : ℂ) / 2‖ = (t + s) / 2 := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; norm_num
      have e2 : ‖((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)‖ = (t - s) ^ 2 / (4 * ‖y‖ ^ 2) := by
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_mul, norm_pow]; norm_num
      rw [e1, e2]
      have hyr2 : r ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hrpos.le hynorm.le 2
      have h3 : (t - s) ^ 2 / (4 * ‖y‖ ^ 2) ≤ (t + s) ^ 2 / (4 * r ^ 2) := by
        apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by nlinarith)
      have h4 : t + s ≤ (1 + t) ^ 2 * (1 + s) ^ 2 := by nlinarith [mul_nonneg ht0 hs0]
      have h5 : (t + s) ^ 2 ≤ (1 + t) ^ 2 * (1 + s) ^ 2 := by nlinarith [mul_nonneg ht0 hs0]
      calc (t + s) / 2 + (t - s) ^ 2 / (4 * ‖y‖ ^ 2) ≤ (t + s) / 2 + (t + s) ^ 2 / (4 * r ^ 2) := by linarith
        _ = 1 / 2 * (t + s) + 1 / (4 * r ^ 2) * (t + s) ^ 2 := by ring
        _ ≤ K * ((1 + t) ^ 2 * (1 + s) ^ 2) := by
          have hc : 0 ≤ 1 / (4 * r ^ 2) := by positivity
          have hKP : K * ((1 + t) ^ 2 * (1 + s) ^ 2) = 1 / 2 * ((1 + t) ^ 2 * (1 + s) ^ 2) +
              1 / (4 * r ^ 2) * ((1 + t) ^ 2 * (1 + s) ^ 2) := by simp only [K]; ring
          have := mul_le_mul_of_nonneg_left h5 hc
          linarith
    calc |f t| * |g s| * ‖gexp y t s‖ * ‖-((t + s : ℝ) : ℂ) / 2 + ((t - s : ℝ) : ℂ) ^ 2 / (4 * y ^ 2)‖
        ≤ |f t| * |g s| * 1 * (K * ((1 + t) ^ 2 * (1 + s) ^ 2)) := by
          gcongr
          exact norm_gexp_le hyre ht0 hs0
      _ = bound (t, s) := by simp only [bound]; ring
  have hd : ∀ᵐ p ∂μ2, ∀ y ∈ S, HasDerivAt (fun y => F y p) (F' y p) y :=
    Filter.Eventually.of_forall fun p y hyS => by
      have hyne : y ≠ 0 := fun h => by have := hyS.1; simp [h] at this
      exact (hasDerivAt_gexp hyne p.1 p.2).const_mul _ |>.congr_deriv (by simp only [F']; ring)
  have hmeas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (F y) μ2 :=
    Filter.Eventually.of_forall fun y => (hfc.mul (continuous_gexp y)).aestronglyMeasurable
  obtain ⟨hint', hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hSnhds hmeas
    (integrable_Jp hf hg hy₀) hF'c.aestronglyMeasurable hbd hbi hd
  refine (hD.congr_deriv ?_)
  -- linearity
  have hI : ∀ (a b : ℕ), Integrable (fun p : ℝ × ℝ => (((Nat.iterate tmul a f) p.1 * (Nat.iterate tmul b g) p.2 : ℝ) : ℂ) *
      gexp y₀ p.1 p.2) μ2 := fun a b => by
    have hfa : ∀ a : ℕ, ExpDec (Nat.iterate tmul a f) := fun a => by
      induction a with
      | zero => exact hf
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.mulT
    have hga : ∀ b : ℕ, ExpDec (Nat.iterate tmul b g) := fun b => by
      induction b with
      | zero => exact hg
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.mulT
    exact integrable_Jp (hfa a) (hga b) hy₀
  have h10 := hI 1 0; have h01 := hI 0 1; have h20 := hI 2 0; have h11 := hI 1 1; have h02 := hI 0 2
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at h10 h01 h20 h11 h02
  unfold Jp
  let A : ℝ × ℝ → ℂ := fun p => (((tmul f) p.1 * g p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2
  let B : ℝ × ℝ → ℂ := fun p => ((f p.1 * (tmul g) p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2
  let C : ℝ × ℝ → ℂ := fun p => (((tmul (tmul f)) p.1 * g p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2
  let D : ℝ × ℝ → ℂ := fun p => (((tmul f) p.1 * (tmul g) p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2
  let E : ℝ × ℝ → ℂ := fun p => ((f p.1 * (tmul (tmul g)) p.2 : ℝ) : ℂ) * gexp y₀ p.1 p.2
  have hA : Integrable A μ2 := h10
  have hB : Integrable B μ2 := h01
  have hC : Integrable C μ2 := h20
  have hD : Integrable D μ2 := h11
  have hE : Integrable E μ2 := h02
  have hpt : ∀ p : ℝ × ℝ, F' y₀ p =
      -(1 / 2 : ℂ) * (A p + B p) + (1 / (4 * y₀ ^ 2)) * (C p - 2 * D p + E p) := fun p => by
    simp only [F', F, tmul, A, B, C, D, E]; push_cast; ring
  have hAB : Integrable (fun p => A p + B p) μ2 := hA.add hB
  have hCDE : Integrable (fun p => C p - 2 * D p + E p) μ2 := (hC.sub (hD.const_mul 2)).add hE
  have hCD : Integrable (fun p => C p - 2 * D p) μ2 := hC.sub (hD.const_mul 2)
  have hfun : (fun p => F' y₀ p) = fun p => -(1 / 2 : ℂ) * (A p + B p) + (1 / (4 * y₀ ^ 2)) * (C p - 2 * D p + E p) :=
    funext hpt
  rw [hfun, integral_add (hAB.const_mul _) (hCDE.const_mul _), integral_const_mul, integral_const_mul,
    integral_add hA hB, integral_add hCD hE, integral_sub hC (hD.const_mul 2), integral_const_mul]

/-! ### The weighted family `Ja f g a b = J(tᵃ f, sᵇ g)` -/

lemma ExpDec.iterate_tmul {f : ℝ → ℝ} (hf : ExpDec f) (a : ℕ) : ExpDec (tmul^[a] f) := by
  induction a with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.mulT

lemma iterate_tmul_eq (f : ℝ → ℝ) (a : ℕ) : tmul^[a] f = fun t => t ^ a * f t := by
  induction a with
  | zero => funext t; simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; funext t; simp only [tmul]; ring

/-- `J(tᵃ f, sᵇ g)`. -/
noncomputable def Ja (f g : ℝ → ℝ) (a b : ℕ) (y : ℂ) : ℂ := Jp (tmul^[a] f) (tmul^[b] g) y

/-- The `y`-derivative of `Ja f g a b`, in terms of `Ja f g` with larger weights. -/
noncomputable def Ja' (f g : ℝ → ℝ) (a b : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (Ja f g (a + 1) b y + Ja f g a (b + 1) y) +
    (1 / (4 * y ^ 2)) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y)

theorem hasDerivAt_Ja {f g : ℝ → ℝ} (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (Ja f g a b) (Ja' f g a b y) y := by
  have h := hasDerivAt_Jp (hf.iterate_tmul a) (hg.iterate_tmul b) hy
  simp only [Ja', Ja, Function.iterate_succ_apply']
  exact h

/-- Values at `0` of `tᵃ f`. -/
lemma iterate_tmul_zero {f : ℝ → ℝ} (a : ℕ) (ha : 1 ≤ a) : (tmul^[a] f) 0 = 0 := by
  rw [iterate_tmul_eq]; simp [zero_pow (by omega : a ≠ 0)]

lemma iterate_tmul_deriv_zero_ge2 {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (a : ℕ) (ha : 2 ≤ a) :
    deriv (tmul^[a] f) 0 = 0 := by
  rw [iterate_tmul_eq]
  have hd : HasDerivAt (fun t : ℝ => t ^ a * f t) ((a : ℝ) * 0 ^ (a - 1) * f 0 + 0 ^ a * deriv f 0) 0 :=
    (hasDerivAt_pow a (0 : ℝ)).mul ((hf.differentiable (by simp) 0).hasDerivAt)
  rw [hd.deriv, zero_pow (by omega : a - 1 ≠ 0), zero_pow (by omega : a ≠ 0)]; simp

lemma tmul_deriv_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) : deriv (tmul f) 0 = f 0 := by
  have hd : HasDerivAt (tmul f) (1 * f 0 + 0 * deriv f 0) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul ((hf.differentiable (by simp) 0).hasDerivAt)
  rw [hd.deriv]; ring

lemma deriv_zero_iterate_zero {f : ℝ → ℝ} : (tmul^[0] f) = f := rfl

lemma rpow_neg_natCast {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ^ (-(m : ℝ)) = (x ^ m)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- Expansion with leading term `4X/y² + 8Z/y³`: gives `O(‖y‖⁻²)`. -/
lemma decayOn_two_of {J : ℂ → ℂ} (X Z : ℂ) {C : ℝ} (hC : 0 < C)
    (h : ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖J y - (4 / y ^ 2 * X + 8 / y ^ 3 * Z)‖ ≤ C * ‖y‖ ^ (-4 : ℝ)) :
    DecayOn 2 J := by
  refine ⟨4 * ‖X‖ + 8 * ‖Z‖ + C, by positivity, fun {y} hy hy1 => ?_⟩
  have hy0 : 0 < ‖y‖ := by linarith
  have e2 : ‖y‖ ^ (-(2 : ℝ)) = (‖y‖ ^ 2)⁻¹ := by simp
  have e3 : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by simp
  have e4 : ‖y‖ ^ (-(4 : ℝ)) = (‖y‖ ^ 4)⁻¹ := by simp
  have h1 := h hy hy1
  have n2 : ‖4 / y ^ 2 * X‖ = 4 * ‖X‖ * ‖y‖ ^ (-(2 : ℝ)) := by
    rw [e2, norm_mul, norm_div, norm_pow]; norm_num; ring
  have n3 : ‖8 / y ^ 3 * Z‖ = 8 * ‖Z‖ * ‖y‖ ^ (-(3 : ℝ)) := by
    rw [e3, norm_mul, norm_div, norm_pow]; norm_num; ring
  have hm3 : ‖y‖ ^ (-(3 : ℝ)) ≤ ‖y‖ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have hm4 : ‖y‖ ^ (-(4 : ℝ)) ≤ ‖y‖ ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  calc ‖J y‖ = ‖(J y - (4 / y ^ 2 * X + 8 / y ^ 3 * Z)) + (4 / y ^ 2 * X + 8 / y ^ 3 * Z)‖ := by ring_nf
    _ ≤ ‖J y - (4 / y ^ 2 * X + 8 / y ^ 3 * Z)‖ + (‖4 / y ^ 2 * X‖ + ‖8 / y ^ 3 * Z‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ C * ‖y‖ ^ (-4 : ℝ) + (4 * ‖X‖ * ‖y‖ ^ (-(2 : ℝ)) + 8 * ‖Z‖ * ‖y‖ ^ (-(3 : ℝ))) := by
        rw [n2, n3]; linarith
    _ ≤ (4 * ‖X‖ + 8 * ‖Z‖ + C) * ‖y‖ ^ (-(2 : ℝ)) := by
        have := norm_nonneg X; have := norm_nonneg Z
        nlinarith [mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ 8 * ‖Z‖),
          mul_le_mul_of_nonneg_left hm4 hC.le]

/-- Expansion with leading term `8Z/y³` only: gives `O(‖y‖⁻³)`. -/
lemma decayOn_three_of {J : ℂ → ℂ} (Z : ℂ) {C : ℝ} (hC : 0 < C)
    (h : ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖J y - 8 / y ^ 3 * Z‖ ≤ C * ‖y‖ ^ (-4 : ℝ)) :
    DecayOn 3 J := by
  refine ⟨8 * ‖Z‖ + C, by positivity, fun {y} hy hy1 => ?_⟩
  have hy0 : 0 < ‖y‖ := by linarith
  have e3 : ‖y‖ ^ (-(3 : ℝ)) = (‖y‖ ^ 3)⁻¹ := by simp
  have h1 := h hy hy1
  have n3 : ‖8 / y ^ 3 * Z‖ = 8 * ‖Z‖ * ‖y‖ ^ (-(3 : ℝ)) := by
    rw [e3, norm_mul, norm_div, norm_pow]; norm_num; ring
  have hm4 : ‖y‖ ^ (-(4 : ℝ)) ≤ ‖y‖ ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  calc ‖J y‖ = ‖(J y - 8 / y ^ 3 * Z) + 8 / y ^ 3 * Z‖ := by ring_nf
    _ ≤ ‖J y - 8 / y ^ 3 * Z‖ + ‖8 / y ^ 3 * Z‖ := norm_add_le _ _
    _ ≤ C * ‖y‖ ^ (-4 : ℝ) + 8 * ‖Z‖ * ‖y‖ ^ (-(3 : ℝ)) := by rw [n3]; linarith
    _ ≤ (8 * ‖Z‖ + C) * ‖y‖ ^ (-(3 : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hm4 hC.le, norm_nonneg Z]

section decay

variable {f g : ℝ → ℝ}

/-- The generic IBP expansion for `Ja f g a b`, with its leading coefficients at `0`. -/
lemma Ja_expansion (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ →
      ‖Ja f g a b y - (4 / y ^ 2 * (((tmul^[a] f) 0 * (tmul^[b] g) 0 : ℝ) : ℂ) +
        8 / y ^ 3 * (((tmul^[a] f) 0 * deriv (tmul^[b] g) 0 + deriv (tmul^[a] f) 0 * (tmul^[b] g) 0 : ℝ) : ℂ))‖ ≤
        C * ‖y‖ ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := gaussian_2d_ibp_general (hf.iterate_tmul a).smooth (hg.iterate_tmul b).smooth
    (hf.iterate_tmul a).dec (hg.iterate_tmul b).dec
  refine ⟨C, hC, fun {y} hy hy1 => ?_⟩
  have := hb hy hy1
  rwa [← Jp_eq_iterated _ _ (hf.iterate_tmul a) (hg.iterate_tmul b) hy] at this

/-- `J(tᵃ f, sᵇ g) = O(‖y‖⁻⁴)` whenever `a + b ≥ 2`. -/
lemma Ja_decay_ge2 (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) (hab : 2 ≤ a + b) :
    DecayOn 4 (Ja f g a b) := by
  obtain ⟨C, hC, hb⟩ := Ja_expansion hf hg a b
  refine ⟨C, hC, fun {y} hy hy1 => ?_⟩
  have h := hb hy hy1
  have hz : (tmul^[a] f) 0 * deriv (tmul^[b] g) 0 + deriv (tmul^[a] f) 0 * (tmul^[b] g) 0 = 0 ∧
      (tmul^[a] f) 0 * (tmul^[b] g) 0 = 0 := by
    by_cases ha : 2 ≤ a
    · rw [iterate_tmul_zero a (by omega), iterate_tmul_deriv_zero_ge2 hf.smooth a ha]; simp
    · by_cases hb' : 2 ≤ b
      · rw [iterate_tmul_zero b (by omega), iterate_tmul_deriv_zero_ge2 hg.smooth b hb']; simp
      · rw [iterate_tmul_zero a (by omega), iterate_tmul_zero b (by omega)]; simp
  rw [hz.1, hz.2] at h
  simpa using h

/-- `J(t f, g) = 8 f(0) g(0)/y³ + O(‖y‖⁻⁴)`. -/
lemma Ja_decay_10 (hf : ExpDec f) (hg : ExpDec g) : DecayOn 3 (Ja f g 1 0) := by
  obtain ⟨C, hC, hb⟩ := Ja_expansion hf hg 1 0
  refine decayOn_three_of (((f 0 * g 0 : ℝ)) : ℂ) hC fun {y} hy hy1 => ?_
  have h := hb hy hy1
  have e1 : (tmul^[1] f) 0 = 0 := iterate_tmul_zero 1 le_rfl
  have e2 : deriv (tmul^[1] f) 0 = f 0 := by
    simpa using tmul_deriv_zero hf.smooth
  simp only [Function.iterate_zero, id_eq, e1, e2, zero_mul, zero_add, Complex.ofReal_zero, mul_zero] at h
  simpa using h

lemma Ja_decay_01 (hf : ExpDec f) (hg : ExpDec g) : DecayOn 3 (Ja f g 0 1) := by
  obtain ⟨C, hC, hb⟩ := Ja_expansion hf hg 0 1
  refine decayOn_three_of (((f 0 * g 0 : ℝ)) : ℂ) hC fun {y} hy hy1 => ?_
  have h := hb hy hy1
  have e1 : (tmul^[1] g) 0 = 0 := iterate_tmul_zero 1 le_rfl
  have e2 : deriv (tmul^[1] g) 0 = g 0 := by
    simpa using tmul_deriv_zero hg.smooth
  simp only [Function.iterate_zero, id_eq, e1, e2, mul_zero, zero_add, Complex.ofReal_zero, add_zero] at h
  simpa using h

lemma Ja_decay_00 (hf : ExpDec f) (hg : ExpDec g) : DecayOn 2 (Ja f g 0 0) := by
  obtain ⟨C, hC, hb⟩ := Ja_expansion hf hg 0 0
  exact decayOn_two_of _ _ hC fun {y} hy hy1 => hb hy hy1

end decay

/-! ### Second-order assembly for `J(f,g)` -/

lemma DecayOn.lin2 {k : ℝ} {A B : ℂ → ℂ} (hA : DecayOn k A) (hB : DecayOn k B) (c d : ℂ) :
    DecayOn k (fun y => c * A y + d * B y) := (hA.const_mul c).add (hB.const_mul d)

lemma DecayOn.lin3 {k : ℝ} {A B C : ℂ → ℂ} (hA : DecayOn k A) (hB : DecayOn k B) (hC : DecayOn k C) (c d e : ℂ) :
    DecayOn k (fun y => c * A y + d * B y + e * C y) := (hA.lin2 hB c d).add (hC.const_mul e)

/-- Multiplying by `(4y²)⁻¹` gains two powers of decay. -/
lemma DecayOn.inv_sq_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) :
    DecayOn (k + 2) (fun y => (1 / (4 * y ^ 2)) * h y) := by
  have := (hh.div_pow 2).const_mul (1 / 4 : ℂ)
  refine (this.congr fun {y} _ => ?_)
  ring

/-- Multiplying by `(2y³)⁻¹` gains three powers of decay. -/
lemma DecayOn.inv_cube_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) :
    DecayOn (k + 3) (fun y => (1 / (2 * y ^ 3)) * h y) := by
  have := (hh.div_pow 3).const_mul (1 / 2 : ℂ)
  refine (this.congr fun {y} _ => ?_)
  ring

section assembly

variable {f g : ℝ → ℝ}

lemma Ja'_decay_ge1 (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) (hab : 1 ≤ a + b) : DecayOn 4 (Ja' f g a b) := by
  have d1 := Ja_decay_ge2 hf hg (a + 1) b (by omega)
  have d2 := Ja_decay_ge2 hf hg a (b + 1) (by omega)
  have d3 := Ja_decay_ge2 hf hg (a + 2) b (by omega)
  have d4 := Ja_decay_ge2 hf hg (a + 1) (b + 1) (by omega)
  have d5 := Ja_decay_ge2 hf hg a (b + 2) (by omega)
  have hA := d1.lin2 d2 (-(1 / 2 : ℂ)) (-(1 / 2 : ℂ))
  have hB := (d3.lin3 d4 d5 1 (-2) 1).inv_sq_mul.mono (k' := 4) (by norm_num)
  refine (hA.add hB).congr fun {y} _ => ?_
  simp only [Ja']; ring

lemma Ja'_decay_00 (hf : ExpDec f) (hg : ExpDec g) : DecayOn 3 (Ja' f g 0 0) := by
  have d1 := Ja_decay_10 hf hg
  have d2 := Ja_decay_01 hf hg
  have d3 := Ja_decay_ge2 hf hg 2 0 (by omega)
  have d4 := Ja_decay_ge2 hf hg 1 1 (by omega)
  have d5 := Ja_decay_ge2 hf hg 0 2 (by omega)
  have hA := d1.lin2 d2 (-(1 / 2 : ℂ)) (-(1 / 2 : ℂ))
  have hB := (d3.lin3 d4 d5 1 (-2) 1).inv_sq_mul.mono (k' := 3) (by norm_num)
  refine (hA.add hB).congr fun {y} _ => ?_
  simp only [Ja']; ring

/-- The derivative of `Ja' f g a b` (the second `y`-derivative of `Ja f g a b`). -/
noncomputable def Ja2 (f g : ℝ → ℝ) (a b : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (Ja' f g (a + 1) b y + Ja' f g a (b + 1) y) +
    (-(1 / (2 * y ^ 3))) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) +
    (1 / (4 * y ^ 2)) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y)

/-- The third `y`-derivative of `Ja f g a b`. -/
noncomputable def Ja3 (f g : ℝ → ℝ) (a b : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * (Ja2 f g (a + 1) b y + Ja2 f g a (b + 1) y) +
    (3 / (2 * y ^ 4)) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) +
    (-(1 / y ^ 3)) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y) +
    (1 / (4 * y ^ 2)) * (Ja2 f g (a + 2) b y - 2 * Ja2 f g (a + 1) (b + 1) y + Ja2 f g a (b + 2) y)

/-- The second `y`-derivative of `J(f,g)`. -/
noncomputable abbrev Ja'' (f g : ℝ → ℝ) (y : ℂ) : ℂ := Ja2 f g 0 0 y

lemma hasDerivAt_inv_four_sq {y : ℂ} (hy0 : y ≠ 0) :
    HasDerivAt (fun y : ℂ => 1 / (4 * y ^ 2)) (-(1 / (2 * y ^ 3))) y := by
  have h4 : HasDerivAt (fun y : ℂ => 4 * y ^ 2) (4 * (2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_mul (4 : ℂ))
  have h4ne : (4 : ℂ) * y ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hy0)
  have := (hasDerivAt_const y (1 : ℂ)).div h4 h4ne
  convert this using 1
  field_simp
  ring

lemma hasDerivAt_neg_inv_two_cube {y : ℂ} (hy0 : y ≠ 0) :
    HasDerivAt (fun y : ℂ => -(1 / (2 * y ^ 3))) (3 / (2 * y ^ 4)) y := by
  have h4 : HasDerivAt (fun y : ℂ => 2 * y ^ 3) (2 * (3 * y ^ 2)) y := by
    simpa using ((hasDerivAt_pow 3 y).const_mul (2 : ℂ))
  have h4ne : (2 : ℂ) * y ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hy0)
  have := ((hasDerivAt_const y (1 : ℂ)).div h4 h4ne).neg
  convert this using 1
  field_simp
  ring

lemma hasDerivAt_Ja' (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (Ja' f g a b) (Ja2 f g a b y) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h10 := hasDerivAt_Ja hf hg (a + 1) b hy
  have h01 := hasDerivAt_Ja hf hg a (b + 1) hy
  have h20 := hasDerivAt_Ja hf hg (a + 2) b hy
  have h11 := hasDerivAt_Ja hf hg (a + 1) (b + 1) hy
  have h02 := hasDerivAt_Ja hf hg a (b + 2) hy
  have hc := hasDerivAt_inv_four_sq hy0
  have hfun : Ja' f g a b = fun y => -(1 / 2 : ℂ) * (Ja f g (a + 1) b y + Ja f g a (b + 1) y) +
      (1 / (4 * y ^ 2)) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) := by
    funext y; simp only [Ja']
  rw [hfun]
  have hA : HasDerivAt (fun y => -(1 / 2 : ℂ) * (Ja f g (a + 1) b y + Ja f g a (b + 1) y))
      (-(1 / 2 : ℂ) * (Ja' f g (a + 1) b y + Ja' f g a (b + 1) y)) y := (h10.add h01).const_mul _
  have hB : HasDerivAt (fun y => (1 / (4 * y ^ 2)) *
        (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y))
      (-(1 / (2 * y ^ 3)) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) +
        (1 / (4 * y ^ 2)) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y)) y :=
    hc.mul ((h20.sub (h11.const_mul 2)).add h02)
  refine (hA.add hB).congr_deriv ?_
  simp only [Ja2]; ring

lemma hasDerivAt_Ja2 (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (Ja2 f g a b) (Ja3 f g a b y) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h10 := hasDerivAt_Ja' hf hg (a + 1) b hy
  have h01 := hasDerivAt_Ja' hf hg a (b + 1) hy
  have h20 := hasDerivAt_Ja' hf hg (a + 2) b hy
  have h11 := hasDerivAt_Ja' hf hg (a + 1) (b + 1) hy
  have h02 := hasDerivAt_Ja' hf hg a (b + 2) hy
  have g20 := hasDerivAt_Ja hf hg (a + 2) b hy
  have g11 := hasDerivAt_Ja hf hg (a + 1) (b + 1) hy
  have g02 := hasDerivAt_Ja hf hg a (b + 2) hy
  have hc2 := hasDerivAt_inv_four_sq hy0
  have hc3 := hasDerivAt_neg_inv_two_cube hy0
  have hA : HasDerivAt (fun y => -(1 / 2 : ℂ) * (Ja' f g (a + 1) b y + Ja' f g a (b + 1) y))
      (-(1 / 2 : ℂ) * (Ja2 f g (a + 1) b y + Ja2 f g a (b + 1) y)) y := (h10.add h01).const_mul _
  have hB : HasDerivAt (fun y => (-(1 / (2 * y ^ 3))) *
        (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y))
      (3 / (2 * y ^ 4) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) +
        (-(1 / (2 * y ^ 3))) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y)) y :=
    hc3.mul ((g20.sub (g11.const_mul 2)).add g02)
  have hC : HasDerivAt (fun y => (1 / (4 * y ^ 2)) *
        (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y))
      (-(1 / (2 * y ^ 3)) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y) +
        (1 / (4 * y ^ 2)) * (Ja2 f g (a + 2) b y - 2 * Ja2 f g (a + 1) (b + 1) y + Ja2 f g a (b + 2) y)) y :=
    hc2.mul ((h20.sub (h11.const_mul 2)).add h02)
  have hfun : Ja2 f g a b = fun y => -(1 / 2 : ℂ) * (Ja' f g (a + 1) b y + Ja' f g a (b + 1) y) +
      (-(1 / (2 * y ^ 3))) * (Ja f g (a + 2) b y - 2 * Ja f g (a + 1) (b + 1) y + Ja f g a (b + 2) y) +
      (1 / (4 * y ^ 2)) * (Ja' f g (a + 2) b y - 2 * Ja' f g (a + 1) (b + 1) y + Ja' f g a (b + 2) y) := by
    funext y; simp only [Ja2]
  rw [hfun]
  refine ((hA.add hB).add hC).congr_deriv ?_
  simp only [Ja3]; ring

lemma Ja2_decay (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) : DecayOn 4 (Ja2 f g a b) := by
  have a1 := Ja'_decay_ge1 hf hg (a + 1) b (by omega)
  have a2 := Ja'_decay_ge1 hf hg a (b + 1) (by omega)
  have a3 := Ja'_decay_ge1 hf hg (a + 2) b (by omega)
  have a4 := Ja'_decay_ge1 hf hg (a + 1) (b + 1) (by omega)
  have a5 := Ja'_decay_ge1 hf hg a (b + 2) (by omega)
  have d3 := Ja_decay_ge2 hf hg (a + 2) b (by omega)
  have d4 := Ja_decay_ge2 hf hg (a + 1) (b + 1) (by omega)
  have d5 := Ja_decay_ge2 hf hg a (b + 2) (by omega)
  have hA := a1.lin2 a2 (-(1 / 2 : ℂ)) (-(1 / 2 : ℂ))
  have hB := ((d3.lin3 d4 d5 1 (-2) 1).inv_cube_mul.mono (k' := 4) (by norm_num)).const_mul (-1 : ℂ)
  have hC := ((a3.lin3 a4 a5 1 (-2) 1).inv_sq_mul.mono (k' := 4) (by norm_num))
  refine ((hA.add hB).add hC).congr fun {y} _ => ?_
  simp only [Ja2]; ring

/-- Dividing by `y⁴` gains four powers of decay. -/
lemma DecayOn.inv_four_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) (c : ℂ) :
    DecayOn (k + 4) (fun y => (c / y ^ 4) * h y) := by
  have := (hh.div_pow 4).const_mul c
  refine (this.congr fun {y} _ => ?_)
  ring

lemma DecayOn.inv_three_mul {k : ℝ} {h : ℂ → ℂ} (hh : DecayOn k h) (c : ℂ) :
    DecayOn (k + 3) (fun y => (c / y ^ 3) * h y) := by
  have := (hh.div_pow 3).const_mul c
  refine (this.congr fun {y} _ => ?_)
  ring

lemma Ja3_decay (hf : ExpDec f) (hg : ExpDec g) (a b : ℕ) : DecayOn 4 (Ja3 f g a b) := by
  have a1 := Ja2_decay hf hg (a + 1) b
  have a2 := Ja2_decay hf hg a (b + 1)
  have a3 := Ja2_decay hf hg (a + 2) b
  have a4 := Ja2_decay hf hg (a + 1) (b + 1)
  have a5 := Ja2_decay hf hg a (b + 2)
  have b3 := Ja'_decay_ge1 hf hg (a + 2) b (by omega)
  have b4 := Ja'_decay_ge1 hf hg (a + 1) (b + 1) (by omega)
  have b5 := Ja'_decay_ge1 hf hg a (b + 2) (by omega)
  have d3 := Ja_decay_ge2 hf hg (a + 2) b (by omega)
  have d4 := Ja_decay_ge2 hf hg (a + 1) (b + 1) (by omega)
  have d5 := Ja_decay_ge2 hf hg a (b + 2) (by omega)
  have hA := a1.lin2 a2 (-(1 / 2 : ℂ)) (-(1 / 2 : ℂ))
  have hB := ((d3.lin3 d4 d5 1 (-2) 1).inv_four_mul (3 / 2)).mono (k' := 4) (by norm_num)
  have hC := ((b3.lin3 b4 b5 1 (-2) 1).inv_three_mul (-1)).mono (k' := 4) (by norm_num)
  have hD := (a3.lin3 a4 a5 1 (-2) 1).inv_sq_mul.mono (k' := 4) (by norm_num)
  refine (((hA.add hB).add hC).add hD).congr fun {y} _ => ?_
  simp only [Ja3]; ring

end assembly

/-! ### Multiplying by `y^{-1/2}` -/

/-- The complex power `y^{-a}` for real `a`. -/
noncomputable def sqf (a : ℝ) (y : ℂ) : ℂ := y ^ (-(a : ℂ))

lemma hasDerivAt_sqf (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (sqf a) (-(a : ℂ) * sqf (a + 1) y) y := by
  have hslit : y ∈ Complex.slitPlane := Or.inl hy
  have h := (hasDerivAt_id' y).cpow_const (c := -(a : ℂ)) hslit
  refine h.congr_deriv ?_
  unfold sqf
  push_cast
  rw [show (-(a : ℂ) - 1) = -((a : ℂ) + 1) by ring, mul_one]

lemma norm_sqf {a : ℝ} {y : ℂ} (hy : y ≠ 0) : ‖sqf a y‖ = ‖y‖ ^ (-a) := by
  unfold sqf
  rw [show (-(a : ℂ)) = ((-a : ℝ) : ℂ) by push_cast; rfl, norm_cpow_ofReal_exponent hy]

/-- Seed-symbol calculus: `T = c y^{-1/2} J` with `J, J', J''` of order `‖y‖⁻², ‖y‖⁻³, ‖y‖⁻⁴`. -/
noncomputable def sT0 (c : ℂ) (J : ℂ → ℂ) (y : ℂ) : ℂ := c * (sqf (1 / 2) y * J y)

noncomputable def sT1 (c : ℂ) (J J1 : ℂ → ℂ) (y : ℂ) : ℂ :=
  c * (-(1 / 2 : ℂ) * (sqf (3 / 2) y * J y) + sqf (1 / 2) y * J1 y)

noncomputable def sT2 (c : ℂ) (J J1 J2 : ℂ → ℂ) (y : ℂ) : ℂ :=
  c * ((3 / 4 : ℂ) * (sqf (5 / 2) y * J y) - sqf (3 / 2) y * J1 y + sqf (1 / 2) y * J2 y)

noncomputable def sT3 (c : ℂ) (J J1 J2 J3 : ℂ → ℂ) (y : ℂ) : ℂ :=
  c * (-(15 / 8 : ℂ) * (sqf (7 / 2) y * J y) + (9 / 4 : ℂ) * (sqf (5 / 2) y * J1 y) -
    (3 / 2 : ℂ) * (sqf (3 / 2) y * J2 y) + sqf (1 / 2) y * J3 y)

theorem sT_calculus {J J1 J2 J3 : ℂ → ℂ} (c : ℂ)
    (h0 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J (J1 y) y) (h1 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J1 (J2 y) y)
    (h2 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J2 (J3 y) y)
    (d0 : DecayOn 2 J) (d1 : DecayOn 3 J1) (d2 : DecayOn 4 J2) (d3 : DecayOn 4 J3) :
    (∀ {y : ℂ}, 0 < y.re → HasDerivAt (sT0 c J) (sT1 c J J1 y) y) ∧
    (∀ {y : ℂ}, 0 < y.re → HasDerivAt (sT1 c J J1) (sT2 c J J1 J2 y) y) ∧
    (∀ {y : ℂ}, 0 < y.re → HasDerivAt (sT2 c J J1 J2) (sT3 c J J1 J2 J3 y) y) ∧
    DecayOn (5 / 2) (sT0 c J) ∧ DecayOn (7 / 2) (sT1 c J J1) ∧ DecayOn (9 / 2) (sT2 c J J1 J2) ∧
    DecayOn (9 / 2) (sT3 c J J1 J2 J3) := by
  refine ⟨fun {y} hy => ?_, fun {y} hy => ?_, fun {y} hy => ?_, ?_, ?_, ?_, ?_⟩
  · have hq := hasDerivAt_sqf (1 / 2) hy
    have := ((hq.mul (h0 hy)).const_mul c)
    refine this.congr_deriv ?_
    simp only [sT1]; push_cast
    have e : ((1 / 2 : ℝ) + 1 : ℝ) = 3 / 2 := by norm_num
    rw [e]; push_cast; try ring
  · have hq1 := hasDerivAt_sqf (3 / 2) hy
    have hq2 := hasDerivAt_sqf (1 / 2) hy
    have := ((((hq1.mul (h0 hy)).const_mul (-(1 / 2 : ℂ))).add (hq2.mul (h1 hy))).const_mul c)
    refine this.congr_deriv ?_
    simp only [sT2]
    have e1 : ((3 / 2 : ℝ) + 1 : ℝ) = 5 / 2 := by norm_num
    have e2 : ((1 / 2 : ℝ) + 1 : ℝ) = 3 / 2 := by norm_num
    rw [e1, e2]; push_cast; try ring
  · have hq1 := hasDerivAt_sqf (5 / 2) hy
    have hq2 := hasDerivAt_sqf (3 / 2) hy
    have hq3 := hasDerivAt_sqf (1 / 2) hy
    have := (((((hq1.mul (h0 hy)).const_mul (3 / 4 : ℂ)).sub (hq2.mul (h1 hy))).add (hq3.mul (h2 hy))).const_mul c)
    refine this.congr_deriv ?_
    simp only [sT3]
    have e1 : ((5 / 2 : ℝ) + 1 : ℝ) = 7 / 2 := by norm_num
    have e2 : ((3 / 2 : ℝ) + 1 : ℝ) = 5 / 2 := by norm_num
    have e3 : ((1 / 2 : ℝ) + 1 : ℝ) = 3 / 2 := by norm_num
    rw [e1, e2, e3]; push_cast; try ring
  · have := ((d0.cpow_mul (1 / 2)).const_mul c).mono (k' := 5 / 2) (by norm_num)
    exact this.congr fun {y} _ => by simp only [sT0, sqf]
  · have a := ((d0.cpow_mul (3 / 2)).const_mul (-(1 / 2 : ℂ))).mono (k' := 7 / 2) (by norm_num)
    have b := (d1.cpow_mul (1 / 2)).mono (k' := 7 / 2) (by norm_num)
    exact ((a.add b).const_mul c).congr fun {y} _ => by simp only [sT1, sqf]; try ring
  · have a := ((d0.cpow_mul (5 / 2)).const_mul (3 / 4 : ℂ)).mono (k' := 9 / 2) (by norm_num)
    have b := ((d1.cpow_mul (3 / 2)).const_mul (-1 : ℂ)).mono (k' := 9 / 2) (by norm_num)
    have e := (d2.cpow_mul (1 / 2)).mono (k' := 9 / 2) (by norm_num)
    exact (((a.add b).add e).const_mul c).congr fun {y} _ => by simp only [sT2, sqf]; try ring
  · have a := ((d0.cpow_mul (7 / 2)).const_mul (-(15 / 8 : ℂ))).mono (k' := 9 / 2) (by norm_num)
    have b := ((d1.cpow_mul (5 / 2)).const_mul (9 / 4 : ℂ)).mono (k' := 9 / 2) (by norm_num)
    have e := ((d2.cpow_mul (3 / 2)).const_mul (-(3 / 2) : ℂ)).mono (k' := 9 / 2) (by norm_num)
    have f := (d3.cpow_mul (1 / 2)).mono (k' := 9 / 2) (by norm_num)
    exact (((((a.add b).add e).add f)).const_mul c).congr fun {y} _ => by simp only [sT3, sqf]; try ring

/-! ### The one-dimensional family `J1p φ` (for `ceF1`) -/

/-- `e^{-yt/2 - t²/(4y)}`. -/
noncomputable def gexp1 (y : ℂ) (t : ℝ) : ℂ := Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y))

lemma gexp1_eq (y : ℂ) (t : ℝ) : gexp1 y t = Complex.exp (-y * (t : ℂ) / 2) * gaussKern y t := by
  unfold gexp1 gaussKern; rw [← Complex.exp_add]; congr 1; ring

lemma norm_gexp1_le {y : ℂ} (hy : 0 < y.re) {t : ℝ} (ht : 0 ≤ t) : ‖gexp1 y t‖ ≤ 1 := by
  rw [gexp1_eq, norm_mul]
  exact (mul_le_mul (norm_exp_neg_mul_half_le hy ht) (norm_gaussKern_le hy _) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)

lemma continuous_gexp1 (y : ℂ) : Continuous fun t : ℝ => gexp1 y t := by
  unfold gexp1; fun_prop

/-- `J1(φ)(y) = ∫_0^∞ φ(t) e^{-yt/2 - t²/(4y)} dt`. -/
noncomputable def J1p (φ : ℝ → ℝ) (y : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), (φ t : ℂ) * gexp1 y t

lemma integrable_J1p {φ : ℝ → ℝ} (hφ : ExpDec φ) {y : ℂ} (hy : 0 < y.re) :
    IntegrableOn (fun t : ℝ => (φ t : ℂ) * gexp1 y t) (Ioi 0) := by
  have hI := hφ.integrable_pow_mul 0
  refine hI.mono' ((Complex.continuous_ofReal.comp hφ.smooth.continuous |>.mul (continuous_gexp1 y)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [pow_zero, one_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |φ t| * ‖gexp1 y t‖ ≤ |φ t| * 1 := mul_le_mul_of_nonneg_left (norm_gexp1_le hy (le_of_lt (mem_Ioi.mp ht))) (abs_nonneg _)
    _ = _ := mul_one _

lemma hasDerivAt_gexp1 {y : ℂ} (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (fun y : ℂ => gexp1 y t) (gexp1 y t * (-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y ^ 2))) y := by
  unfold gexp1
  have h1 : HasDerivAt (fun y : ℂ => -y * (t : ℂ) / 2) (-(t : ℂ) / 2) y := by
    have := ((hasDerivAt_id y).neg.mul_const (t : ℂ)).div_const 2
    simpa using this
  have h2 : HasDerivAt (fun y : ℂ => (t : ℂ) ^ 2 / (4 * y)) (-((t : ℂ) ^ 2 / (4 * y ^ 2))) y := by
    have h4 : HasDerivAt (fun y : ℂ => 4 * y) 4 y := by simpa using (hasDerivAt_id y).const_mul (4 : ℂ)
    have h4ne : (4 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy
    have := (hasDerivAt_const y ((t : ℂ) ^ 2)).div h4 h4ne
    convert this using 1
    field_simp
    ring
  have h3 : HasDerivAt (fun y : ℂ => -y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y))
      (-(t : ℂ) / 2 - -((t : ℂ) ^ 2 / (4 * y ^ 2))) y := h1.sub h2
  have h5 := h3.cexp
  convert h5 using 1
  ring

theorem hasDerivAt_J1p {φ : ℝ → ℝ} (hφ : ExpDec φ) {y₀ : ℂ} (hy₀ : 0 < y₀.re) :
    HasDerivAt (J1p φ) (-(1 / 2 : ℂ) * J1p (tmul φ) y₀ + (1 / (4 * y₀ ^ 2)) * J1p (tmul (tmul φ)) y₀) y₀ := by
  have hy0 : y₀ ≠ 0 := fun h => by simp [h] at hy₀
  set r : ℝ := ‖y₀‖ / 2 with hr
  have hrpos : 0 < r := by have : 0 < ‖y₀‖ := norm_pos_iff.mpr hy0; positivity
  set S : Set ℂ := {y | 0 < y.re} ∩ {y | r < ‖y‖} with hS
  have hSnhds : S ∈ 𝓝 y₀ := by
    refine Filter.inter_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hy₀)
      ((isOpen_lt continuous_const continuous_norm).mem_nhds ?_)
    have : 0 < ‖y₀‖ := norm_pos_iff.mpr hy0
    show r < ‖y₀‖; rw [hr]; linarith
  let F : ℂ → ℝ → ℂ := fun y t => (φ t : ℂ) * gexp1 y t
  let F' : ℂ → ℝ → ℂ := fun y t => F y t * (-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y ^ 2))
  let K : ℝ := 1 / 2 + 1 / (4 * r ^ 2)
  let bound : ℝ → ℝ := fun t => K * ((1 + t) ^ 2 * |φ t|)
  have hφc : Continuous fun t : ℝ => (φ t : ℂ) := Complex.continuous_ofReal.comp hφ.smooth.continuous
  have hF'c : Continuous (F' y₀) := by
    show Continuous fun t : ℝ => (φ t : ℂ) * gexp1 y₀ t * (-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y₀ ^ 2))
    refine (hφc.mul (continuous_gexp1 y₀)).mul ?_
    fun_prop
  have hbi : IntegrableOn bound (Ioi 0) := (hφ.integrable_pow_mul 2).const_mul K
  have hbd : ∀ t ∈ Ioi (0 : ℝ), ∀ y ∈ S, ‖F' y t‖ ≤ bound t := by
    intro t ht y hyS
    have ht0 : 0 ≤ t := le_of_lt ht
    obtain ⟨hyre, hyr⟩ := hyS
    have hynorm : r < ‖y‖ := hyr
    show ‖(φ t : ℂ) * gexp1 y t * (-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y ^ 2))‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hW : ‖-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y ^ 2)‖ ≤ K * (1 + t) ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      have e1 : ‖-(t : ℂ) / 2‖ = t / 2 := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; norm_num
      have e2 : ‖(t : ℂ) ^ 2 / (4 * y ^ 2)‖ = t ^ 2 / (4 * ‖y‖ ^ 2) := by
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_mul, norm_pow]; norm_num
      rw [e1, e2]
      have hyr2 : r ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hrpos.le hynorm.le 2
      have h3 : t ^ 2 / (4 * ‖y‖ ^ 2) ≤ t ^ 2 / (4 * r ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      have hKP : K * (1 + t) ^ 2 = 1 / 2 * (1 + t) ^ 2 + 1 / (4 * r ^ 2) * (1 + t) ^ 2 := by simp only [K]; ring
      have hc : 0 ≤ 1 / (4 * r ^ 2) := by positivity
      have h4 : t ≤ (1 + t) ^ 2 := by nlinarith
      have h5 : t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
      have h6 : 1 / (4 * r ^ 2) * t ^ 2 ≤ 1 / (4 * r ^ 2) * (1 + t) ^ 2 := mul_le_mul_of_nonneg_left h5 hc
      calc t / 2 + t ^ 2 / (4 * ‖y‖ ^ 2) ≤ t / 2 + t ^ 2 / (4 * r ^ 2) := by linarith
        _ = t / 2 + 1 / (4 * r ^ 2) * t ^ 2 := by ring
        _ ≤ K * (1 + t) ^ 2 := by linarith
    calc |φ t| * ‖gexp1 y t‖ * ‖-(t : ℂ) / 2 + (t : ℂ) ^ 2 / (4 * y ^ 2)‖
        ≤ |φ t| * 1 * (K * (1 + t) ^ 2) := by
          gcongr
          exact norm_gexp1_le hyre ht0
      _ = bound t := by simp only [bound]; ring
  have hd : ∀ t ∈ Ioi (0 : ℝ), ∀ y ∈ S, HasDerivAt (fun y => F y t) (F' y t) y := fun t _ y hyS => by
    have hyne : y ≠ 0 := fun h => by have := hyS.1; simp [h] at this
    exact (hasDerivAt_gexp1 hyne t).const_mul _ |>.congr_deriv (by simp only [F']; ring)
  have hmeas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (F y) (volume.restrict (Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall fun y => (hφc.mul (continuous_gexp1 y)).aestronglyMeasurable
  obtain ⟨hint', hD⟩ := hasDerivAt_integral_Ioi hSnhds hmeas (integrable_J1p hφ hy₀)
    hF'c.aestronglyMeasurable hbd hbi hd
  refine hD.congr_deriv ?_
  have h1 := integrable_J1p (hφ.mulT) hy₀
  have h2 := integrable_J1p (hφ.mulT.mulT) hy₀
  have hpt : ∀ t : ℝ, F' y₀ t = -(1 / 2 : ℂ) * (((tmul φ t : ℝ) : ℂ) * gexp1 y₀ t) +
      (1 / (4 * y₀ ^ 2)) * (((tmul (tmul φ) t : ℝ) : ℂ) * gexp1 y₀ t) := fun t => by
    simp only [F', F, tmul]; push_cast; ring
  unfold J1p
  rw [show (fun t => F' y₀ t) = _ from funext hpt, integral_add (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- `J1(tᵃ φ)`. -/
noncomputable def J1a (φ : ℝ → ℝ) (a : ℕ) (y : ℂ) : ℂ := J1p (tmul^[a] φ) y

/-- Its `y`-derivative. -/
noncomputable def J1a' (φ : ℝ → ℝ) (a : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * J1a φ (a + 1) y + (1 / (4 * y ^ 2)) * J1a φ (a + 2) y

theorem hasDerivAt_J1a {φ : ℝ → ℝ} (hφ : ExpDec φ) (a : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (J1a φ a) (J1a' φ a y) y := by
  have h := hasDerivAt_J1p (hφ.iterate_tmul a) hy
  simp only [J1a', J1a, Function.iterate_succ_apply']
  exact h

section oneD

variable {φ : ℝ → ℝ}

lemma J1a_expansion (hφ : ExpDec φ) (a : ℕ) :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ →
      ‖J1a φ a y - (2 / y * (((tmul^[a] φ) 0 : ℝ) : ℂ) + 4 / y ^ 2 * ((iteratedDeriv 1 (tmul^[a] φ) 0 : ℝ) : ℂ) +
        8 / y ^ 3 * ((iteratedDeriv 2 (tmul^[a] φ) 0 : ℝ) : ℂ))‖ ≤ C * ‖y‖ ^ (-4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := gaussian_1d_ibp_general (hφ.iterate_tmul a).smooth (hφ.iterate_tmul a).dec
  exact ⟨C, hC, fun {y} hy hy1 => hb hy hy1⟩

lemma iterate_tmul_iteratedDeriv_vals (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (a : ℕ) (ha : 2 ≤ a) :
    iteratedDeriv 1 (tmul^[a] φ) 0 = 0 ∧ iteratedDeriv 2 (tmul^[a] φ) 0 = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have hG : tmul^[b + 2] φ = tmul (tmul^[b + 1] φ) := Function.iterate_succ_apply' _ _ _
  have hH : tmul^[b + 1] φ = tmul (tmul^[b] φ) := Function.iterate_succ_apply' _ _ _
  have s1 := (hφ.iterate_tmul (b + 1)).smooth
  have s0 := (hφ.iterate_tmul b).smooth
  have hb0 : (tmul^[b] φ) 0 = 0 := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simpa using hφ0
    · exact iterate_tmul_zero b hb
  have hb1 : (tmul^[b + 1] φ) 0 = 0 := iterate_tmul_zero (b + 1) (by omega)
  have g1 : iteratedDeriv 1 (tmul^[b + 1] φ) 0 = 0 := by
    rw [hH, iteratedDeriv_tmul s0]
    simp only [zero_mul, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero, zero_add]
    exact hb0
  constructor
  · rw [hG, iteratedDeriv_tmul s1]
    simp only [zero_mul, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero, zero_add]
    exact hb1
  · rw [hG, iteratedDeriv_tmul s1]
    simp only [zero_mul, zero_add, Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, g1, mul_zero]

lemma J1a_decay_0 (hφ : ExpDec φ) (hφ0 : φ 0 = 0) : DecayOn 2 (J1a φ 0) := by
  obtain ⟨C, hC, hb⟩ := J1a_expansion hφ 0
  refine decayOn_two_of ((iteratedDeriv 1 φ 0 : ℝ) : ℂ) ((iteratedDeriv 2 φ 0 : ℝ) : ℂ) hC fun {y} hy hy1 => ?_
  have h := hb hy hy1
  simpa [hφ0] using h

lemma J1a_decay_1 (hφ : ExpDec φ) (hφ0 : φ 0 = 0) : DecayOn 3 (J1a φ 1) := by
  obtain ⟨C, hC, hb⟩ := J1a_expansion hφ 1
  refine decayOn_three_of ((2 * iteratedDeriv 1 φ 0 : ℝ) : ℂ) hC fun {y} hy hy1 => ?_
  have h := hb hy hy1
  have e0 : (tmul^[1] φ) 0 = 0 := iterate_tmul_zero 1 le_rfl
  have e1 : iteratedDeriv 1 (tmul^[1] φ) 0 = 0 := by
    rw [Function.iterate_one, iteratedDeriv_tmul hφ.smooth 1]
    simp [hφ0]
  have e2 : iteratedDeriv 2 (tmul^[1] φ) 0 = 2 * iteratedDeriv 1 φ 0 := by
    rw [Function.iterate_one, iteratedDeriv_tmul hφ.smooth 2]
    simp
  rw [e0, e1, e2] at h
  simpa using h

lemma J1a_decay_ge2 (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (a : ℕ) (ha : 2 ≤ a) : DecayOn 4 (J1a φ a) := by
  obtain ⟨C, hC, hb⟩ := J1a_expansion hφ a
  refine ⟨C, hC, fun {y} hy hy1 => ?_⟩
  have h := hb hy hy1
  obtain ⟨v1, v2⟩ := iterate_tmul_iteratedDeriv_vals hφ hφ0 a ha
  rw [iterate_tmul_zero a (by omega), v1, v2] at h
  simpa using h

lemma J1a'_decay_0 (hφ : ExpDec φ) (hφ0 : φ 0 = 0) : DecayOn 3 (J1a' φ 0) := by
  have d1 := J1a_decay_1 hφ hφ0
  have d2 := J1a_decay_ge2 hφ hφ0 2 le_rfl
  have hA := d1.const_mul (-(1 / 2 : ℂ))
  have hB := d2.inv_sq_mul.mono (k' := 3) (by norm_num)
  exact (hA.add hB).congr fun {y} _ => by simp only [J1a']

lemma J1a'_decay_ge1 (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (a : ℕ) (ha : 1 ≤ a) : DecayOn 4 (J1a' φ a) := by
  have d1 := J1a_decay_ge2 hφ hφ0 (a + 1) (by omega)
  have d2 := J1a_decay_ge2 hφ hφ0 (a + 2) (by omega)
  have hA := d1.const_mul (-(1 / 2 : ℂ))
  have hB := d2.inv_sq_mul.mono (k' := 4) (by norm_num)
  exact (hA.add hB).congr fun {y} _ => by simp only [J1a']

/-- The derivative of `J1a' φ a` (the second `y`-derivative of `J1a φ a`). -/
noncomputable def J1a2 (φ : ℝ → ℝ) (a : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * J1a' φ (a + 1) y + (-(1 / (2 * y ^ 3))) * J1a φ (a + 2) y + (1 / (4 * y ^ 2)) * J1a' φ (a + 2) y

/-- The third `y`-derivative of `J1a φ a`. -/
noncomputable def J1a3 (φ : ℝ → ℝ) (a : ℕ) (y : ℂ) : ℂ :=
  -(1 / 2 : ℂ) * J1a2 φ (a + 1) y + (3 / (2 * y ^ 4)) * J1a φ (a + 2) y + (-(1 / y ^ 3)) * J1a' φ (a + 2) y +
    (1 / (4 * y ^ 2)) * J1a2 φ (a + 2) y

/-- The second `y`-derivative of `J1(φ)`. -/
noncomputable abbrev J1a'' (φ : ℝ → ℝ) (y : ℂ) : ℂ := J1a2 φ 0 y

lemma hasDerivAt_J1a' (hφ : ExpDec φ) (a : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (J1a' φ a) (J1a2 φ a y) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h1 := hasDerivAt_J1a hφ (a + 1) hy
  have h2 := hasDerivAt_J1a hφ (a + 2) hy
  have hc := hasDerivAt_inv_four_sq hy0
  have hfun : J1a' φ a = fun y => -(1 / 2 : ℂ) * J1a φ (a + 1) y + (1 / (4 * y ^ 2)) * J1a φ (a + 2) y := by
    funext y; simp only [J1a']
  rw [hfun]
  have hA : HasDerivAt (fun y => -(1 / 2 : ℂ) * J1a φ (a + 1) y) (-(1 / 2 : ℂ) * J1a' φ (a + 1) y) y := h1.const_mul _
  have hB : HasDerivAt (fun y => (1 / (4 * y ^ 2)) * J1a φ (a + 2) y)
      (-(1 / (2 * y ^ 3)) * J1a φ (a + 2) y + (1 / (4 * y ^ 2)) * J1a' φ (a + 2) y) y := hc.mul h2
  refine (hA.add hB).congr_deriv ?_
  simp only [J1a2]; ring

lemma hasDerivAt_J1a2 (hφ : ExpDec φ) (a : ℕ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (J1a2 φ a) (J1a3 φ a y) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h1 := hasDerivAt_J1a' hφ (a + 1) hy
  have h2 := hasDerivAt_J1a' hφ (a + 2) hy
  have g2 := hasDerivAt_J1a hφ (a + 2) hy
  have hc2 := hasDerivAt_inv_four_sq hy0
  have hc3 := hasDerivAt_neg_inv_two_cube hy0
  have hA : HasDerivAt (fun y => -(1 / 2 : ℂ) * J1a' φ (a + 1) y) (-(1 / 2 : ℂ) * J1a2 φ (a + 1) y) y := h1.const_mul _
  have hB : HasDerivAt (fun y => (-(1 / (2 * y ^ 3))) * J1a φ (a + 2) y)
      (3 / (2 * y ^ 4) * J1a φ (a + 2) y + (-(1 / (2 * y ^ 3))) * J1a' φ (a + 2) y) y := hc3.mul g2
  have hC : HasDerivAt (fun y => (1 / (4 * y ^ 2)) * J1a' φ (a + 2) y)
      (-(1 / (2 * y ^ 3)) * J1a' φ (a + 2) y + (1 / (4 * y ^ 2)) * J1a2 φ (a + 2) y) y := hc2.mul h2
  have hfun : J1a2 φ a = fun y => -(1 / 2 : ℂ) * J1a' φ (a + 1) y + (-(1 / (2 * y ^ 3))) * J1a φ (a + 2) y +
      (1 / (4 * y ^ 2)) * J1a' φ (a + 2) y := by
    funext y; simp only [J1a2]
  rw [hfun]
  refine ((hA.add hB).add hC).congr_deriv ?_
  simp only [J1a3]; ring

lemma J1a2_decay (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (a : ℕ) : DecayOn 4 (J1a2 φ a) := by
  have a1 := J1a'_decay_ge1 hφ hφ0 (a + 1) (by omega)
  have a2 := J1a'_decay_ge1 hφ hφ0 (a + 2) (by omega)
  have d2 := J1a_decay_ge2 hφ hφ0 (a + 2) (by omega)
  have hA := a1.const_mul (-(1 / 2 : ℂ))
  have hB := (d2.inv_cube_mul.mono (k' := 4) (by norm_num)).const_mul (-1 : ℂ)
  have hC := a2.inv_sq_mul.mono (k' := 4) (by norm_num)
  refine ((hA.add hB).add hC).congr fun {y} _ => ?_
  simp only [J1a2]; ring

lemma J1a3_decay (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (a : ℕ) : DecayOn 4 (J1a3 φ a) := by
  have a1 := J1a2_decay hφ hφ0 (a + 1)
  have a2 := J1a2_decay hφ hφ0 (a + 2)
  have b2 := J1a'_decay_ge1 hφ hφ0 (a + 2) (by omega)
  have d2 := J1a_decay_ge2 hφ hφ0 (a + 2) (by omega)
  have hA := a1.const_mul (-(1 / 2 : ℂ))
  have hB := (d2.inv_four_mul (3 / 2)).mono (k' := 4) (by norm_num)
  have hC := (b2.inv_three_mul (-1)).mono (k' := 4) (by norm_num)
  have hD := a2.inv_sq_mul.mono (k' := 4) (by norm_num)
  refine (((hA.add hB).add hC).add hD).congr fun {y} _ => ?_
  simp only [J1a3]; ring

end oneD

/-! ### Symbol bounds on the right half-plane -/

/-- `T` is three times complex-differentiable on `Re y > 0` with `T = O(‖y‖^{-5/2})`, `T' = O(‖y‖^{-7/2})`,
`T'' = O(‖y‖^{-9/2})` and `T''' = O(‖y‖^{-9/2})` on `{Re y > 0, ‖y‖ ≥ 1}` (the half-plane form of `(e27)`, `r ≤ 2`; the
third derivative is only needed bounded, to pass to the boundary `Re y = 0`). -/
def SymbolBounds (T : ℂ → ℂ) : Prop :=
  ∃ T1 T2 T3 : ℂ → ℂ, (∀ {y : ℂ}, 0 < y.re → HasDerivAt T (T1 y) y) ∧
    (∀ {y : ℂ}, 0 < y.re → HasDerivAt T1 (T2 y) y) ∧ (∀ {y : ℂ}, 0 < y.re → HasDerivAt T2 (T3 y) y) ∧
    DecayOn (5 / 2) T ∧ DecayOn (7 / 2) T1 ∧ DecayOn (9 / 2) T2 ∧ DecayOn (9 / 2) T3

lemma symbolBounds_of_form {T J J1 J2 J3 : ℂ → ℂ} (c : ℂ) (hT : ∀ {y : ℂ}, 0 < y.re → T y = sT0 c J y)
    (h0 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J (J1 y) y) (h1 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J1 (J2 y) y)
    (h2 : ∀ {y : ℂ}, 0 < y.re → HasDerivAt J2 (J3 y) y)
    (d0 : DecayOn 2 J) (d1 : DecayOn 3 J1) (d2 : DecayOn 4 J2) (d3 : DecayOn 4 J3) : SymbolBounds T := by
  obtain ⟨e0, e1, e2, f0, f1, f2, f3⟩ := sT_calculus c h0 h1 h2 d0 d1 d2 d3
  refine ⟨sT1 c J J1, sT2 c J J1 J2, sT3 c J J1 J2 J3, fun {y} hy => ?_, fun {y} hy => e1 hy, fun {y} hy => e2 hy,
    f0.congr fun {y} hy => (hT hy).symm, f1, f2, f3⟩
  refine (e0 hy).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hy] with z hz using hT hz

lemma symbolBounds_two_dim {f g : ℝ → ℝ} (hf : ExpDec f) (hg : ExpDec g) (c : ℂ) {T : ℂ → ℂ}
    (hT : ∀ {y : ℂ}, 0 < y.re → T y = sT0 c (Jp f g) y) : SymbolBounds T :=
  symbolBounds_of_form c hT (J1 := Ja' f g 0 0) (J2 := Ja2 f g 0 0) (J3 := Ja3 f g 0 0)
    (fun {y} hy => hasDerivAt_Ja hf hg 0 0 hy) (fun {y} hy => hasDerivAt_Ja' hf hg 0 0 hy)
    (fun {y} hy => hasDerivAt_Ja2 hf hg 0 0 hy)
    (Ja_decay_00 hf hg) (Ja'_decay_00 hf hg) (Ja2_decay hf hg 0 0) (Ja3_decay hf hg 0 0)

lemma symbolBounds_one_dim {φ : ℝ → ℝ} (hφ : ExpDec φ) (hφ0 : φ 0 = 0) (c : ℂ) {T : ℂ → ℂ}
    (hT : ∀ {y : ℂ}, 0 < y.re → T y = sT0 c (J1p φ) y) : SymbolBounds T :=
  symbolBounds_of_form c hT (J1 := J1a' φ 0) (J2 := J1a2 φ 0) (J3 := J1a3 φ 0)
    (fun {y} hy => hasDerivAt_J1a hφ 0 hy) (fun {y} hy => hasDerivAt_J1a' hφ 0 hy)
    (fun {y} hy => hasDerivAt_J1a2 hφ 0 hy)
    (J1a_decay_0 hφ hφ0) (J1a'_decay_0 hφ hφ0) (J1a2_decay hφ hφ0 0) (J1a3_decay hφ hφ0 0)

/-! ### The seeds -/

lemma expDec_dirichletPhi0 : ExpDec (dirichletPhi 0) := by
  have hfn : (fun s => airyAi (airyZero 1 + s) / airyAi' (airyZero 1)) = dirichletPhi 0 :=
    funext fun s => by unfold dirichletPhi; ring_nf
  refine ⟨contDiff_dirichletPhi0, fun n k => ?_⟩
  obtain ⟨C, hC, hbd⟩ := airyAi_shift_div_decay (airyZero 1) airyAi'_first_pos.ne' n k (by norm_num : (0 : ℝ) < 1 / 4)
  exact ⟨C, hC, fun t ht => by simpa [hfn] using hbd t ht⟩

lemma expDec_airyRatio : ExpDec (airyRatio airyDerivFirstZero) :=
  ⟨contDiff_airyRatio _, fun n k => airyAi_shift_div_decay airyDerivFirstZero
    (airyAi_pos_of_gt airyDerivFirstZero_spec.1).ne' n k (by norm_num)⟩

/-- The prefactor constant of the Gaussian transforms of the seeds. -/
noncomputable def seedConst : ℂ := (ceK : ℂ) * (((2 * Real.sqrt π)⁻¹ : ℝ) : ℂ)

lemma seed_prefactor {y : ℂ} (hy : 0 < y.re) :
    (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) = seedConst * sqf (1 / 2) y := by
  rw [rpow_neg_half_mul_four_pi hy]
  unfold seedConst sqf
  push_cast
  ring

theorem ceF1_symbolBounds : SymbolBounds (airyTwistedLaplaceC ceF1) := by
  refine symbolBounds_one_dim expDec_dirichletPhi0 dirichletPhi0_vals_at_zero.1 seedConst fun {y} hy => ?_
  rw [airyTwistedLaplaceC_ceF1_eq hy, seed_prefactor hy]
  simp only [sT0, J1p, gexp1]; ring

theorem ceG1_symbolBounds : SymbolBounds (airyTwistedLaplaceC (ceG1 (airyZero 1))) := by
  refine symbolBounds_two_dim expDec_dirichletPhi0 expDec_dirichletPhi0 seedConst fun {y} hy => ?_
  rw [airyTwistedLaplaceC_ceG1_eq hy, seed_prefactor hy,
    ← Jp_eq_iterated _ _ expDec_dirichletPhi0 expDec_dirichletPhi0 hy]
  simp only [sT0]; ring

theorem ceG1Deriv_symbolBounds : SymbolBounds (airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero)) := by
  refine symbolBounds_two_dim expDec_airyRatio expDec_airyRatio seedConst fun {y} hy => ?_
  rw [airyTwistedLaplaceC_ceG1Deriv_eq hy, seed_prefactor hy,
    ← Jp_eq_iterated _ _ expDec_airyRatio expDec_airyRatio hy]
  simp only [sT0]; ring

/-! ### The boundary `Re y = 0` -/

/-- The point `1/(n+1) + ω i` approaching the imaginary axis. -/
noncomputable def bpt (n : ℕ) (ω : ℝ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + (ω : ℂ) * Complex.I

lemma bpt_re (n : ℕ) (ω : ℝ) : (bpt n ω).re = 1 / ((n : ℝ) + 1) := by
  simp only [bpt, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
  ring

lemma bpt_im (n : ℕ) (ω : ℝ) : (bpt n ω).im = ω := by
  simp only [bpt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
  ring

lemma bpt_norm_ge (n : ℕ) (ω : ℝ) : |ω| ≤ ‖bpt n ω‖ := by
  calc |ω| = |(bpt n ω).im| := by rw [bpt_im]
    _ ≤ ‖bpt n ω‖ := Complex.abs_im_le_norm _

lemma hasDerivAt_bpt (n : ℕ) (ω : ℝ) : HasDerivAt (fun ω : ℝ => bpt n ω) Complex.I ω := by
  unfold bpt
  have := (((hasDerivAt_id ω).ofReal_comp).mul_const Complex.I).const_add (((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
  simpa using this

/-- **One step of the boundary passage**: if `F` has derivative `F1` and `F1` has a bounded derivative `F2` on the
part of the open right half-plane lying over an open set `s` of heights, and `F(1/(n+1) + ω i) → g(ω)`, then
`F1(1/(n+1) + ω i)` converges to some `h(ω)` and `g` has derivative `i h` on `s`. -/
lemma boundary_step {F F1 F2 : ℂ → ℂ} {s : Set ℝ} (hs : IsOpen s) {M : ℝ} (hM0 : 0 ≤ M)
    (hF : ∀ y : ℂ, 0 < y.re → y.im ∈ s → HasDerivAt F (F1 y) y)
    (hF1 : ∀ y : ℂ, 0 < y.re → y.im ∈ s → HasDerivAt F1 (F2 y) y)
    (hM : ∀ y : ℂ, 0 < y.re → y.im ∈ s → ‖F2 y‖ ≤ M)
    {g : ℝ → ℂ} (hg : ∀ ω ∈ s, Tendsto (fun n : ℕ => F (bpt n ω)) atTop (𝓝 (g ω))) :
    ∃ h : ℝ → ℂ, (∀ ω ∈ s, Tendsto (fun n : ℕ => F1 (bpt n ω)) atTop (𝓝 (h ω))) ∧
      ∀ ω ∈ s, HasDerivAt g (Complex.I * h ω) ω := by
  -- Lipschitz in the horizontal direction
  have hlip : ∀ ω ∈ s, ∀ e e' : ℝ, 0 < e → 0 < e' →
      ‖F1 ((e' : ℂ) + (ω : ℂ) * Complex.I) - F1 ((e : ℂ) + (ω : ℂ) * Complex.I)‖ ≤ M * ‖e' - e‖ := by
    intro ω hω e e' he he'
    have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => F1 ((x : ℂ) + (ω : ℂ) * Complex.I))
        (F2 ((x : ℂ) + (ω : ℂ) * Complex.I)) (Set.Ioi 0) x := by
      intro x hx
      have hre : 0 < (((x : ℝ) : ℂ) + (ω : ℂ) * Complex.I).re := by simpa using hx
      have him : (((x : ℝ) : ℂ) + (ω : ℂ) * Complex.I).im ∈ s := by simpa using hω
      have h1 := hF1 _ hre him
      have h2 : HasDerivAt (fun z : ℂ => F1 (z + (ω : ℂ) * Complex.I)) (F2 ((x : ℂ) + (ω : ℂ) * Complex.I)) (x : ℂ) :=
        h1.comp_add_const (x : ℂ) _
      exact (h2.comp_ofReal).hasDerivWithinAt
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun x hx => hM _ (by simpa using hx) (by simpa using hω)) (convex_Ioi 0) he he'
  -- uniform Cauchy
  have hUC : UniformCauchySeqOn (fun (n : ℕ) (ω : ℝ) => F1 (bpt n ω)) atTop s := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((M + 1) / ε)
    refine ⟨N, fun m hm n hn ω hω => ?_⟩
    rw [dist_eq_norm]
    have hm1 : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hn1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h := hlip ω hω _ _ hn1 hm1
    have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt (by positivity) hN
    have hle : ‖1 / ((m : ℝ) + 1) - 1 / ((n : ℝ) + 1)‖ ≤ 1 / ((N : ℝ) + 1) := by
      rw [Real.norm_eq_abs, abs_le]
      have a1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
      have a2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
      constructor <;> linarith
    calc ‖F1 (bpt m ω) - F1 (bpt n ω)‖ ≤ M * ‖1 / ((m : ℝ) + 1) - 1 / ((n : ℝ) + 1)‖ := by
          have := hlip ω hω _ _ hn1 hm1
          simpa [bpt, norm_sub_rev] using (by simpa [bpt] using this : ‖F1 (bpt m ω) - F1 (bpt n ω)‖ ≤ M * ‖1 / ((m : ℝ) + 1) - 1 / ((n : ℝ) + 1)‖)
      _ ≤ M * (1 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hle hM0
      _ < ε := by
          rw [mul_one_div, div_lt_iff₀ (by positivity)]
          have : (M + 1) / ε < N := hN
          rw [div_lt_iff₀ hε] at this
          nlinarith
  classical
  have hlim : ∀ ω ∈ s, ∃ a, Tendsto (fun n : ℕ => F1 (bpt n ω)) atTop (𝓝 a) := fun ω hω =>
    cauchySeq_tendsto_of_complete (hUC.cauchySeq hω)
  let h : ℝ → ℂ := fun ω => if hω : ω ∈ s then Classical.choose (hlim ω hω) else 0
  have hh : ∀ ω ∈ s, Tendsto (fun n : ℕ => F1 (bpt n ω)) atTop (𝓝 (h ω)) := by
    intro ω hω
    simp only [h, dif_pos hω]
    exact Classical.choose_spec (hlim ω hω)
  refine ⟨h, hh, fun ω hω => ?_⟩
  have hU : TendstoUniformlyOn (fun (n : ℕ) (ω : ℝ) => F1 (bpt n ω)) h atTop s :=
    hUC.tendstoUniformlyOn_of_tendsto hh
  have hU' : TendstoUniformlyOn (fun (n : ℕ) (ω : ℝ) => Complex.I * F1 (bpt n ω)) (fun ω => Complex.I * h ω) atTop s := by
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with n hn ω hω'
    have := hn ω hω'
    rw [dist_eq_norm] at this ⊢
    rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
    exact this
  have hderiv : ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, x ∈ s →
      HasDerivAt (fun ω : ℝ => F (bpt n ω)) (Complex.I * F1 (bpt n x)) x := by
    refine Filter.Eventually.of_forall fun n x hx => ?_
    have h1 := hF (bpt n x) (by rw [bpt_re]; positivity) (by rw [bpt_im]; exact hx)
    have := h1.scomp x (hasDerivAt_bpt n x)
    simpa [Function.comp_def, smul_eq_mul] using this
  exact hasDerivAt_of_tendstoUniformlyOn hs hU' hderiv hg hω

lemma DecayOn.along_bpt {k : ℝ} (hk : 0 ≤ k) {h : ℂ → ℂ} (hd : DecayOn k h) :
    ∃ C > 0, ∀ (n : ℕ) (ω : ℝ), 1 < |ω| → ‖h (bpt n ω)‖ ≤ C * |ω| ^ (-k) := by
  obtain ⟨C, hC, hb⟩ := hd
  refine ⟨C, hC, fun n ω hω => ?_⟩
  have hre : 0 < (bpt n ω).re := by rw [bpt_re]; positivity
  have hge := bpt_norm_ge n ω
  refine (hb hre (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hge (by linarith)

lemma tendsto_bpt (ω : ℝ) : Tendsto (fun n : ℕ => bpt n ω) atTop (𝓝 ((ω : ℂ) * Complex.I)) := by
  unfold bpt
  have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  simpa using h0.add_const ((ω : ℂ) * Complex.I)

/-- The `(e27)` conclusion for `r ≤ 2` on the imaginary axis: `ω ↦ T(i ω)` is twice differentiable for `|ω| > 1`
with `|T(iω)| ≲ |ω|^{-5/2}`, `|∂_ω T(iω)| ≲ |ω|^{-7/2}`, `|∂_ω² T(iω)| ≲ |ω|^{-9/2}`. -/
def ImagAxisBounds (T : ℂ → ℂ) : Prop :=
  ∃ g1 g2 : ℝ → ℂ, (∀ ω : ℝ, 1 < |ω| → HasDerivAt (fun ω : ℝ => T ((ω : ℂ) * Complex.I)) (g1 ω) ω) ∧
    (∀ ω : ℝ, 1 < |ω| → HasDerivAt g1 (g2 ω) ω) ∧
    ∃ C > 0, ∀ ω : ℝ, 1 < |ω| → ‖T ((ω : ℂ) * Complex.I)‖ ≤ C * |ω| ^ (-(5 / 2 : ℝ)) ∧
      ‖g1 ω‖ ≤ C * |ω| ^ (-(7 / 2 : ℝ)) ∧ ‖g2 ω‖ ≤ C * |ω| ^ (-(9 / 2 : ℝ))

/-- **The symbol bounds on the imaginary axis** (`(e27)` for `r ≤ 2`, `|ω| > 1`): if `T` satisfies the half-plane
`SymbolBounds` and is continuous on `Re y ≥ 0`, then `ω ↦ T(i ω)` is twice differentiable on `|ω| > 1`, with
`|T(iω)| ≲ |ω|^{-5/2}`, `|∂_ω T(iω)| ≲ |ω|^{-7/2}`, `|∂_ω² T(iω)| ≲ |ω|^{-9/2}`. -/
theorem SymbolBounds.imagAxis {T : ℂ → ℂ} (hT : SymbolBounds T) (hcont : ContinuousOn T {y : ℂ | 0 ≤ y.re}) :
    ImagAxisBounds T := by
  unfold ImagAxisBounds
  obtain ⟨T1, T2, T3, h1, h2, h3, d0, d1, d2, d3⟩ := hT
  set s : Set ℝ := {ω | 1 < |ω|} with hs_def
  have hs : IsOpen s := isOpen_lt continuous_const continuous_abs
  have hnorm : ∀ y : ℂ, y.im ∈ s → 1 ≤ ‖y‖ := fun y hy => by
    have : 1 < |y.im| := hy
    exact (this.trans_le (Complex.abs_im_le_norm y)).le
  have hbd : ∀ {k : ℝ} {h : ℂ → ℂ}, 0 ≤ k → DecayOn k h →
      ∃ M ≥ 0, ∀ y : ℂ, 0 < y.re → y.im ∈ s → ‖h y‖ ≤ M := fun {k h} hk hd => by
    obtain ⟨C, hC, hb⟩ := hd
    refine ⟨C, hC.le, fun y hy hys => (hb hy (hnorm y hys)).trans ?_⟩
    have : ‖y‖ ^ (-k) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hnorm y hys) (by linarith)
    nlinarith
  obtain ⟨M2, hM2, hb2⟩ := hbd (k := 9 / 2) (by norm_num) d2
  obtain ⟨M3, hM3, hb3⟩ := hbd (k := 9 / 2) (by norm_num) d3
  have hg0 : ∀ ω ∈ s, Tendsto (fun n : ℕ => T (bpt n ω)) atTop (𝓝 (T ((ω : ℂ) * Complex.I))) := by
    intro ω hω
    have hmem : ((ω : ℂ) * Complex.I) ∈ {y : ℂ | 0 ≤ y.re} := by simp
    have ht := (hcont _ hmem).tendsto
    refine ht.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_bpt ω, Filter.Eventually.of_forall fun n => ?_⟩
    show 0 ≤ (bpt n ω).re
    rw [bpt_re]; positivity
  obtain ⟨hA, hhA, hdA⟩ := boundary_step hs hM2 (fun y hy _ => h1 hy) (fun y hy _ => h2 hy) hb2 hg0
  obtain ⟨hB, hhB, hdB⟩ := boundary_step hs hM3 (fun y hy _ => h2 hy) (fun y hy _ => h3 hy) hb3 hhA
  refine ⟨fun ω => Complex.I * hA ω, fun ω => Complex.I * (Complex.I * hB ω), fun ω hω => hdA ω hω,
    fun ω hω => (hdB ω hω).const_mul Complex.I, ?_⟩
  obtain ⟨C0, hC0, b0⟩ := d0.along_bpt (by norm_num)
  obtain ⟨C1, hC1, b1⟩ := d1.along_bpt (by norm_num)
  obtain ⟨C2, hC2, b2⟩ := d2.along_bpt (by norm_num)
  refine ⟨C0 + C1 + C2, by positivity, fun ω hω => ?_⟩
  have hp : ∀ k : ℝ, 0 ≤ |ω| ^ (-k) := fun k => Real.rpow_nonneg (abs_nonneg ω) _
  have lim : ∀ {u : ℕ → ℂ} {a : ℂ} {B : ℝ}, Tendsto u atTop (𝓝 a) → (∀ n, ‖u n‖ ≤ B) → ‖a‖ ≤ B :=
    fun {u a B} hu hb => le_of_tendsto (hu.norm) (Filter.Eventually.of_forall hb)
  have e0 : ‖T ((ω : ℂ) * Complex.I)‖ ≤ C0 * |ω| ^ (-(5 / 2 : ℝ)) := lim (hg0 ω hω) fun n => b0 n ω hω
  have e1 : ‖hA ω‖ ≤ C1 * |ω| ^ (-(7 / 2 : ℝ)) := lim (hhA ω hω) fun n => b1 n ω hω
  have e2 : ‖hB ω‖ ≤ C2 * |ω| ^ (-(9 / 2 : ℝ)) := lim (hhB ω hω) fun n => b2 n ω hω
  refine ⟨?_, ?_, ?_⟩
  · refine e0.trans ?_
    nlinarith [hp (5 / 2), hC1, hC2]
  · rw [norm_mul, Complex.norm_I, one_mul]
    refine e1.trans ?_
    nlinarith [hp (7 / 2), hC0, hC2]
  · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    refine e2.trans ?_
    nlinarith [hp (9 / 2), hC0, hC1]

/-- **`(e27)` for `f₁`** on the imaginary axis, `r ≤ 2`, `|ω| > 1`. -/
theorem ceF1_imagAxisBounds : ImagAxisBounds (airyTwistedLaplaceC ceF1) :=
  ceF1_symbolBounds.imagAxis ceF1_regularity.2.1

/-- **`(e27)` for `g₁`** on the imaginary axis, `r ≤ 2`, `|ω| > 1`. -/
theorem ceG1_imagAxisBounds : ImagAxisBounds (airyTwistedLaplaceC (ceG1 (airyZero 1))) := by
  obtain ⟨C1, hC1, hG1_t⟩ := ceG1_tail_exp_rpow32
  have hreg := airyTwistedLaplaceC_regularity (continuous_ceG1 _) ceG1_integrable hC1 hG1_t
  exact ceG1_symbolBounds.imagAxis hreg.2.1

/-- **`(e27)` for `g₁'`** on the imaginary axis, `r ≤ 2`, `|ω| > 1`. -/
theorem ceG1Deriv_imagAxisBounds : ImagAxisBounds (airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero)) := by
  obtain ⟨C1, hC1, hG_t⟩ := ceG1Deriv_tail_exp_rpow32
  have hreg := airyTwistedLaplaceC_regularity (continuous_ceG1Deriv _) ceG1Deriv_integral_eq_M.1 hC1 hG_t
  exact ceG1Deriv_symbolBounds.imagAxis hreg.2.1

/-! ### Linear combinations of seeds -/

lemma ImagAxisBounds.congr_imag {T U : ℂ → ℂ} (h : ImagAxisBounds T) (hTU : ∀ ω : ℝ, T ((ω : ℂ) * Complex.I) = U ((ω : ℂ) * Complex.I)) :
    ImagAxisBounds U := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := h
  have hfun : (fun ω : ℝ => T ((ω : ℂ) * Complex.I)) = fun ω : ℝ => U ((ω : ℂ) * Complex.I) := funext hTU
  refine ⟨g1, g2, fun ω hω => hfun ▸ h1 ω hω, h2, C, hC, fun ω hω => ?_⟩
  rw [← hTU ω]; exact hb ω hω

lemma ImagAxisBounds.const_mul {T : ℂ → ℂ} (h : ImagAxisBounds T) (c : ℂ) :
    ImagAxisBounds (fun y => c * T y) := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := h
  refine ⟨fun ω => c * g1 ω, fun ω => c * g2 ω, fun ω hω => (h1 ω hω).const_mul c, fun ω hω => (h2 ω hω).const_mul c,
    (‖c‖ + 1) * C, by positivity, fun ω hω => ?_⟩
  obtain ⟨b0, b1, b2⟩ := hb ω hω
  have hp : ∀ k : ℝ, 0 ≤ C * |ω| ^ (-k) := fun k => mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg ω) _)
  have key : ∀ {x : ℂ} {k : ℝ}, ‖x‖ ≤ C * |ω| ^ (-k) → ‖c * x‖ ≤ (‖c‖ + 1) * C * |ω| ^ (-k) := fun {x k} hx => by
    rw [norm_mul]
    have := hp k
    nlinarith [norm_nonneg c, norm_nonneg x]
  exact ⟨key b0, key b1, key b2⟩

lemma ImagAxisBounds.add {T U : ℂ → ℂ} (h : ImagAxisBounds T) (h' : ImagAxisBounds U) :
    ImagAxisBounds (fun y => T y + U y) := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := h
  obtain ⟨g1', g2', h1', h2', C', hC', hb'⟩ := h'
  refine ⟨fun ω => g1 ω + g1' ω, fun ω => g2 ω + g2' ω, fun ω hω => (h1 ω hω).add (h1' ω hω),
    fun ω hω => (h2 ω hω).add (h2' ω hω), C + C', by positivity, fun ω hω => ?_⟩
  obtain ⟨b0, b1, b2⟩ := hb ω hω
  obtain ⟨c0, c1, c2⟩ := hb' ω hω
  have hp : ∀ k : ℝ, 0 ≤ |ω| ^ (-k) := fun k => Real.rpow_nonneg (abs_nonneg ω) _
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_add_le _ _).trans (by nlinarith [hp (5 / 2)])
  · exact (norm_add_le _ _).trans (by nlinarith [hp (7 / 2)])
  · exact (norm_add_le _ _).trans (by nlinarith [hp (9 / 2)])

lemma airySeedU2_transform (a b c : ℝ) {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (airySeedU2 a b c) y = (a : ℂ) * airyTwistedLaplaceC ceF1 y +
      (b : ℂ) * airyTwistedLaplaceC (ceG1 (airyZero 1)) y + (c : ℂ) * airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero) y := by
  have i1 := (hasU2_ceF1.smul a).integrable y hy
  have i2 := (hasU2_ceG1.smul b).integrable y hy
  have i3 := (hasU2_ceG1Deriv.smul c).integrable y hy
  have i12 := ((hasU2_ceF1.smul a).add (hasU2_ceG1.smul b)).integrable y hy
  unfold airySeedU2
  rw [airyTwistedLaplaceC_add i12 i3, airyTwistedLaplaceC_add i1 i2, airyTwistedLaplaceC_const_mul,
    airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_const_mul]

/-- **`(e27)` for the one-level seeds `a f₁ + b g₁ + c g₁'`** (`r ≤ 2`, imaginary axis, `|ω| > 1`). -/
theorem airySeedU2_imagAxisBounds (a b c : ℝ) : ImagAxisBounds (airyTwistedLaplaceC (airySeedU2 a b c)) := by
  have h := ((ceF1_imagAxisBounds.const_mul (a : ℂ)).add (ceG1_imagAxisBounds.const_mul (b : ℂ))).add
    (ceG1Deriv_imagAxisBounds.const_mul (c : ℂ))
  refine h.congr_imag fun ω => ?_
  rw [airySeedU2_transform a b c (by simp)]

/-- **`(e27)` for the `m₀ = 1` Hermite–Biehler seed** `-f₁ - γ₁δ g₁ + γ₂δ S_b + r g₁`. -/
theorem hbSeed_m1_imagAxisBounds (γ₁ γ₂ δ r : ℝ) :
    ImagAxisBounds (airyTwistedLaplaceC
      (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u)) := by
  rw [hbSeed_m1_eq_airySeedU2]; exact airySeedU2_imagAxisBounds _ _ _


/-- info: 'FormalResearch.CohnElkies.hasDerivAt_Jp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasDerivAt_Jp
/-- info: 'FormalResearch.CohnElkies.hasDerivAt_J1p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasDerivAt_J1p
/-- info: 'FormalResearch.CohnElkies.sT_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sT_calculus
/-- info: 'FormalResearch.CohnElkies.ceF1_symbolBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceF1_symbolBounds
/-- info: 'FormalResearch.CohnElkies.ceG1_symbolBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceG1_symbolBounds
/-- info: 'FormalResearch.CohnElkies.ceG1Deriv_symbolBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceG1Deriv_symbolBounds

/-- info: 'FormalResearch.CohnElkies.boundary_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_step

/-- info: 'FormalResearch.CohnElkies.SymbolBounds.imagAxis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SymbolBounds.imagAxis

/-- info: 'FormalResearch.CohnElkies.ceF1_imagAxisBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceF1_imagAxisBounds
/-- info: 'FormalResearch.CohnElkies.ceG1_imagAxisBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceG1_imagAxisBounds
/-- info: 'FormalResearch.CohnElkies.ceG1Deriv_imagAxisBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ceG1Deriv_imagAxisBounds

/-- info: 'FormalResearch.CohnElkies.airySeedU2_imagAxisBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airySeedU2_imagAxisBounds
/-- info: 'FormalResearch.CohnElkies.hbSeed_m1_imagAxisBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hbSeed_m1_imagAxisBounds

end FormalResearch.CohnElkies

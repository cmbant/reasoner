module

public import FormalResearch.SignUncertainty.UctBumpSymbolAdmiss
public import FormalResearch.SignUncertainty.StripAdmiss

/-!
# `uct:bump-symbol`: admissibility of `ΔW_c(ζ) = c^{-1/3} B̂(cζ)` in the sense of `uct:admiss` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol` ("`ΔW_c` satisfies the admissibility conditions of Lemma `uct:admiss` with Hölder exponent `1/2`").
With `BumpProfile` (`b δ M α β K B`) of `UctBumpSymbol` and `UctBumpSymbolAdmiss` (`bump_stripM1`, `bump_holder_one`):

* `bump_stripEdge0`: (M3) at `ζ = 0`: `StripEdge0 (1/2) ΔW_c`: the edge trace `g_0(τ) = c^{-1/3} B̂(icτ)` is `C²` off `0`, `|g_0 - g_0(0)| ≤ C|τ|^{1/2}`, `|g_0'| ≤ C|τ|^{-1/2}`,
  `|g_0''| ≤ C|τ|^{-3/2}` on `0 < |τ| ≤ 1`, and `|g_0^{(j)}| ≤ C(1+|τ|)^{-2}` for `|τ| ≥ 1/2`.  Needs `β ≥ 3/2` and `bδ ≤ 1`.
* `bump_stripEdge1`: (M3) at `ζ = 1` (`StripEdge1`): the right-edge trace `c^{-1/3} B̂(c - icτ)` (absolutely convergent).
* `bump_holder_zero`: (M2) at `ζ = 0`.  `bump_stripAdmissFull`: `StripAdmissFullData (1/2)`, the full target of `uct:admiss` (parts (1)-(3)).
* Method for the edge at `0`.  The boundary derivatives of `B̂(icτ)` are conditionally convergent (`x B`, `x² B` are not integrable for `β = 3/2`), so the edge trace is represented through
  absolutely convergent integrals `g(τ) = κ s^{-4} P_0[B^{(4)}](s)`, `s = icτ` (four integrations by parts, `edgeE0_eq`) and differentiated twice in the real parameter `τ`
  (`hasDerivAt_bumpLapW_param`, `hasDerivAt_edgeE`).  The bounds near `0` come from the damped transform `s = icτ + η`, `η ↓ 0`: for `Re s > 0`, `|s| ≤ 1`,
  `|P_j[B](s)| ≤ C|s|^{1/2-j}` (`bumpLapW_bound`: split at `x = 1/|s|`, `j+1` integrations by parts on the tail `tail_iter`, `tail_bound`, `head_bound`), and `η → 0` is taken through the continuity of the
  explicit representation (`hlimit` inside the proof of `bump_stripEdge0`); `holder_zero` is `|B̂(s) - B̂(0)| ≤ C|s|^{1/2}`.

Class: proved, no hypotheses.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty


lemma norm_mul_exp (a b : ℝ) : ‖a * Real.exp b‖ = Real.exp b * ‖a‖ := by
  rw [norm_mul, Real.norm_eq_abs (Real.exp b), abs_of_pos (Real.exp_pos _)]; ring

/-- The weighted Laplace integral `P_m[f](s) = ∫ e^{-sx} x^m f(x) dx`. -/
noncomputable def bumpLapW (f : ℝ → ℝ) (m : ℕ) (s : ℂ) : ℂ := ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * (((x ^ m * f x : ℝ)) : ℂ)

lemma bump_norm_exp_neg_mul (s : ℂ) (x : ℝ) : ‖Complex.exp (-s * (x : ℂ))‖ = Real.exp (-(s.re * x)) := by
  rw [Complex.norm_exp]; congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

/-- `s ↦ P_m[f](s)` is continuous on `Re s ≥ 0` when `x^m f` is integrable and `f` is supported in `[0,∞)`. -/
lemma continuousOn_bumpLapW {f : ℝ → ℝ} (hf : Continuous f) (hz : ∀ x : ℝ, x < 0 → f x = 0) {m : ℕ}
    (hI : Integrable (fun x : ℝ => x ^ m * f x)) : ContinuousOn (bumpLapW f m) {s : ℂ | 0 ≤ s.re} := by
  unfold bumpLapW
  refine continuousOn_of_dominated (bound := fun x => ‖x ^ m * f x‖) (fun s _ => ?_) (fun s hs => ?_) hI.norm (ae_of_all _ fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).mul
      (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => x ^ m * f x))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real]
    rcases lt_or_ge x 0 with hx | hx
    · rw [hz x hx]; simp
    · have : Real.exp (-(s.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs hx])
      calc Real.exp (-(s.re * x)) * ‖x ^ m * f x‖ ≤ 1 * ‖x ^ m * f x‖ := by gcongr
        _ = _ := one_mul _
  · exact (by fun_prop : Continuous fun s : ℂ => Complex.exp (-s * (x : ℂ)) * (((x ^ m * f x : ℝ)) : ℂ)).continuousOn

/-- Differentiation in the real parameter `τ` along the line `Re s = η ≥ 0`. -/
lemma hasDerivAt_bumpLapW_param {f : ℝ → ℝ} (hf : Continuous f) (_hz : ∀ x : ℝ, x < 0 → f x = 0) {m : ℕ} {η : ℝ} (_hη : 0 ≤ η) (c τ : ℝ)
    (hI0 : Integrable (fun x : ℝ => x ^ m * f x * Real.exp (-(η * x))))
    (hI1 : Integrable (fun x : ℝ => x ^ (m + 1) * f x * Real.exp (-(η * x)))) :
    HasDerivAt (fun τ : ℝ => bumpLapW f m (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)))
      (-((c : ℂ) * Complex.I) * bumpLapW f (m + 1) (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) τ := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := τ) (s := Set.univ)
    (F := fun τ x => Complex.exp (-(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ)) * (((x ^ m * f x : ℝ)) : ℂ))
    (F' := fun τ x => -((c : ℂ) * Complex.I) * (Complex.exp (-(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ)) * (((x ^ (m + 1) * f x : ℝ)) : ℂ)))
    (bound := fun x => |c| * ‖x ^ (m + 1) * f x * Real.exp (-(η * x))‖) Filter.univ_mem
    (Eventually.of_forall fun τ => ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ))).mul
      (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => x ^ m * f x))).aestronglyMeasurable)
    (by
      refine (hI0.norm.mono' ?_ (ae_of_all _ fun x => ?_))
      · exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ))).mul
          (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => x ^ m * f x))).aestronglyMeasurable
      · rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          zero_add, mul_one, sub_self]
        rw [norm_mul_exp])
    ((by fun_prop : Continuous fun x : ℝ => -((c : ℂ) * Complex.I) * (Complex.exp (-(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ)) *
        (((x ^ (m + 1) * f x : ℝ)) : ℂ))).aestronglyMeasurable)
    (ae_of_all _ fun x τ' _ => by
      rw [norm_mul, norm_mul, bump_norm_exp_neg_mul, Complex.norm_real, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_add, mul_one, sub_self]
      rw [norm_mul_exp])
    (hI1.norm.const_mul _)
    (ae_of_all _ fun x τ' _ => by
      have h1 : HasDerivAt (fun τ : ℝ => -(((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) * (x : ℂ)) (-((c : ℂ) * Complex.I) * (x : ℂ)) τ' := by
        have := ((hasDerivAt_id τ').const_mul c).ofReal_comp
        simpa using ((this.mul_const Complex.I).add_const (η : ℂ)).neg.mul_const (x : ℂ)
      refine (h1.cexp.mul_const _).congr_deriv ?_
      push_cast; ring)
  have h2 := hd.2
  rw [integral_const_mul] at h2
  exact h2


namespace BumpProfile
variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma integrable_pow_mul (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (k n : ℕ) (hn : (n : ℝ) < β + k - 1) :
    Integrable (fun x : ℝ => x ^ n * iteratedDeriv k B x) := by
  have hcont : Continuous (fun x : ℝ => x ^ n * iteratedDeriv k B x) := by
    have := (h.contDiff_iteratedDeriv k).continuous
    fun_prop
  have hind : (fun x : ℝ => x ^ n * iteratedDeriv k B x) = (Ici (b * δ)).indicator (fun x : ℝ => x ^ n * iteratedDeriv k B x) := by
    funext x
    by_cases hx : b * δ ≤ x
    · rw [indicator_of_mem (mem_Ici.mpr hx)]
    · rw [indicator_of_notMem (by simpa using hx), h.zero_of_lt k (not_le.mp hx), mul_zero]
  rw [hind, integrable_indicator_iff measurableSet_Ici, ← Icc_union_Ioi_eq_Ici hbδ]
  refine IntegrableOn.union (hcont.integrableOn_Icc) ?_
  have hint : IntegrableOn (fun x : ℝ => x ^ (n - β - k : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine (hint.const_mul (K k * M)).mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hx0 n)]
  have := h.far k x hx1.le
  calc x ^ n * |iteratedDeriv k B x| ≤ x ^ n * (K k * M * x ^ (-β - (k : ℝ))) := by gcongr
    _ = K k * M * x ^ ((n : ℝ) - β - k) := by
        rw [show ((n : ℝ) - β - k) = (n : ℝ) + (-β - k) by ring, Real.rpow_add hx0, Real.rpow_natCast]; ring

end BumpProfile

lemma integrable_mul_exp {g : ℝ → ℝ} (hg : Integrable g) (hz : ∀ x : ℝ, x < 0 → g x = 0) {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun x : ℝ => g x * Real.exp (-(η * x))) := by
  refine hg.norm.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (-(η * x))).aestronglyMeasurable
  · rcases lt_or_ge x 0 with hx | hx
    · rw [hz x hx]; simp
    · rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-(η * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hη hx])
      calc ‖g x‖ * Real.exp (-(η * x)) ≤ ‖g x‖ * 1 := by gcongr
        _ = _ := mul_one _


/-- `E₀ = κ s^{-4} P_0[f]`, `E₁ = E₀'`, `E₂ = E₁'` in the variable `s`, with `s = icτ + η`. -/
noncomputable def edgeE0 (f : ℝ → ℝ) (κ : ℂ) (s : ℂ) : ℂ := κ * s ^ (-4 : ℤ) * bumpLapW f 0 s
noncomputable def edgeE1 (f : ℝ → ℝ) (κ : ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  -(κ * ((c : ℂ) * Complex.I)) * (4 * s ^ (-5 : ℤ) * bumpLapW f 0 s + s ^ (-4 : ℤ) * bumpLapW f 1 s)
noncomputable def edgeE2 (f : ℝ → ℝ) (κ : ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  -(κ * (c : ℂ) ^ 2) * (20 * s ^ (-6 : ℤ) * bumpLapW f 0 s + 8 * s ^ (-5 : ℤ) * bumpLapW f 1 s + s ^ (-4 : ℤ) * bumpLapW f 2 s)

lemma hasDerivAt_edgeE {f : ℝ → ℝ} (hf : Continuous f) (hz : ∀ x : ℝ, x < 0 → f x = 0)
    (hI : ∀ m : ℕ, m ≤ 2 → Integrable (fun x : ℝ => x ^ m * f x)) {η : ℝ} (hη : 0 ≤ η) (κ : ℂ) (c τ : ℝ)
    (hne : ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ) ≠ 0) :
    HasDerivAt (fun τ : ℝ => edgeE0 f κ (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)))
        (edgeE1 f κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) τ ∧
      HasDerivAt (fun τ : ℝ => edgeE1 f κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)))
        (edgeE2 f κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) τ := by
  set p : ℝ → ℂ := fun τ => ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ) with hp
  have hpd : HasDerivAt p ((c : ℂ) * Complex.I) τ := by
    have := ((hasDerivAt_id τ).const_mul c).ofReal_comp
    exact ((this.mul_const Complex.I).add_const (η : ℂ)).congr_deriv (by simp)
  have hz' : ∀ n : ℤ, HasDerivAt (fun τ : ℝ => (p τ) ^ n) ((n : ℂ) * (p τ) ^ (n - 1) * ((c : ℂ) * Complex.I)) τ := fun n =>
    (hasDerivAt_zpow n (p τ) (Or.inl hne)).comp τ hpd
  have hQ : ∀ m : ℕ, m ≤ 1 → HasDerivAt (fun τ : ℝ => bumpLapW f m (p τ)) (-((c : ℂ) * Complex.I) * bumpLapW f (m + 1) (p τ)) τ := fun m hm =>
    hasDerivAt_bumpLapW_param hf hz hη c τ (integrable_mul_exp (hI m (by omega)) (fun x hx => by rw [hz x hx, mul_zero]) hη)
      (integrable_mul_exp (hI (m + 1) (by omega)) (fun x hx => by rw [hz x hx, mul_zero]) hη)
  have h4 := hz' (-4)
  have h5 := hz' (-5)
  have h0 := hQ 0 (by omega)
  have h1 := hQ 1 (by omega)
  refine ⟨?_, ?_⟩
  · have := ((h4.const_mul κ).mul h0)
    refine this.congr_deriv ?_
    simp only [edgeE1, p]
    norm_num
    ring
  · have e := ((h5.const_mul 4).mul h0).add (h4.mul h1)
    have := e.const_mul (-(κ * ((c : ℂ) * Complex.I)))
    refine this.congr_deriv ?_
    have hb1 := hQ 1 (by omega)
    simp only [edgeE2, p]
    norm_num
    ring_nf
    simp only [Complex.I_sq]
    ring


namespace BumpProfile
variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma bumpLapW_zero_B (s : ℂ) : bumpLapW B 0 s = bumpLaplace B s := by
  unfold bumpLapW bumpLaplace; simp

/-- Representation `F(s) = s^{-4} P_0[B^{(4)}](s)` on `Re s ≥ 0`, `s ≠ 0`. -/
lemma edgeE0_eq (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (κ : ℂ) {s : ℂ} (hs : 0 ≤ s.re) (hs0 : s ≠ 0) :
    edgeE0 (iteratedDeriv 4 B) κ s = κ * bumpLaplace B s := by
  have h4 := h.laplace_pow hb0 hbδ hβ hs 4
  have : bumpLapW (iteratedDeriv 4 B) 0 s = s ^ 4 * bumpLaplace B s := by
    rw [← h4]; unfold bumpLapW; simp
  unfold edgeE0
  rw [this, zpow_neg, zpow_ofNat]
  field_simp

lemma integrable_pow_B_exp (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (m : ℕ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ => x ^ m * B x * Real.exp (-(η * x))) := by
  have hB := h.integrable_self hbδ hβ
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  refine (hB.norm.const_mul ((m.factorial : ℝ) / η ^ m)).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => x ^ m).mul hBc |>.mul (by fun_prop : Continuous fun x : ℝ => Real.exp (-(η * x)))).aestronglyMeasurable
  · rcases lt_or_ge x 0 with hx | hx
    · rw [h.support x (by linarith)]; simp
    · rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), norm_mul, Real.norm_eq_abs (x ^ m), abs_of_nonneg (pow_nonneg hx m)]
      have h1 := Real.pow_div_factorial_le_exp (η * x) (by positivity) m
      have h2 : x ^ m * Real.exp (-(η * x)) ≤ (m.factorial : ℝ) / η ^ m := by
        have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
        have hηm : 0 < η ^ m := by positivity
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hηm]
        rw [mul_pow, div_le_iff₀ hfac] at h1
        nlinarith [h1]
      calc x ^ m * ‖B x‖ * Real.exp (-(η * x)) = (x ^ m * Real.exp (-(η * x))) * ‖B x‖ := by ring
        _ ≤ (m.factorial : ℝ) / η ^ m * ‖B x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)


lemma f4_data (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (hb0 : 0 ≤ b * δ) (hβ : 1 < β) :
    Continuous (iteratedDeriv 4 B) ∧ (∀ x : ℝ, x < 0 → iteratedDeriv 4 B x = 0) ∧
      ∀ m : ℕ, m ≤ 2 → Integrable (fun x : ℝ => x ^ m * iteratedDeriv 4 B x) := by
  refine ⟨(h.contDiff_iteratedDeriv 4).continuous, fun x hx => h.zero_of_lt 4 (by linarith), fun m hm => ?_⟩
  have : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  exact h.integrable_pow_mul hbδ 4 m (by push_cast; linarith)

lemma edgeE_eq_laplace (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) {η : ℝ} (hη : 0 < η)
    (κ : ℂ) (c τ : ℝ) :
    edgeE1 (iteratedDeriv 4 B) κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) =
        -(κ * ((c : ℂ) * Complex.I)) * bumpLapW B 1 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) ∧
      edgeE2 (iteratedDeriv 4 B) κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) =
        κ * ((c : ℂ) * Complex.I) ^ 2 * bumpLapW B 2 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := by
  obtain ⟨hf, hz, hI⟩ := h.f4_data hbδ hb0 hβ
  have hz0 : ∀ x : ℝ, x < 0 → B x = 0 := fun x hx => h.support x (by linarith)
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  have hpre : ∀ τ : ℝ, (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)).re = η := fun τ => by simp
  have hpne : ∀ τ : ℝ, ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ) ≠ 0 := fun τ h0 => by
    have := congrArg Complex.re h0; rw [hpre] at this; simp at this; linarith
  have e0 : ∀ τ : ℝ, edgeE0 (iteratedDeriv 4 B) κ (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) =
      κ * bumpLapW B 0 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := fun τ => by
    rw [bumpLapW_zero_B]; exact h.edgeE0_eq hb0 hbδ hβ κ (by rw [hpre]; exact hη.le) (hpne τ)
  have hB0 := hasDerivAt_bumpLapW_param hBc hz0 (m := 0) hη.le c τ (h.integrable_pow_B_exp hb0 hbδ hβ 0 hη) (h.integrable_pow_B_exp hb0 hbδ hβ 1 hη)
  have hB1 := hasDerivAt_bumpLapW_param hBc hz0 (m := 1) hη.le c τ (h.integrable_pow_B_exp hb0 hbδ hβ 1 hη) (h.integrable_pow_B_exp hb0 hbδ hβ 2 hη)
  obtain ⟨hA1, hA2⟩ := hasDerivAt_edgeE hf hz hI hη.le κ c τ (hpne τ)
  have u1 : edgeE1 (iteratedDeriv 4 B) κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) =
      -(κ * ((c : ℂ) * Complex.I)) * bumpLapW B 1 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := by
    have hfun : (fun τ : ℝ => edgeE0 (iteratedDeriv 4 B) κ (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) =
        fun τ : ℝ => κ * bumpLapW B 0 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := funext e0
    rw [hfun] at hA1
    have := hA1.unique (hB0.const_mul κ)
    rw [this]; ring
  refine ⟨u1, ?_⟩
  have hfun : (fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) κ c (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) =
      fun τ : ℝ => -(κ * ((c : ℂ) * Complex.I)) * bumpLapW B 1 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := by
    funext τ'
    have hB0' := hasDerivAt_bumpLapW_param hBc hz0 (m := 0) hη.le c τ' (h.integrable_pow_B_exp hb0 hbδ hβ 0 hη) (h.integrable_pow_B_exp hb0 hbδ hβ 1 hη)
    obtain ⟨hA1', -⟩ := hasDerivAt_edgeE hf hz hI hη.le κ c τ' (hpne τ')
    have hfun0 : (fun τ : ℝ => edgeE0 (iteratedDeriv 4 B) κ (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) =
        fun τ : ℝ => κ * bumpLapW B 0 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) := funext e0
    rw [hfun0] at hA1'
    have := hA1'.unique (hB0'.const_mul κ)
    rw [this]; ring
  rw [hfun] at hA2
  have := hA2.unique ((hB1.const_mul (-(κ * ((c : ℂ) * Complex.I)))))
  rw [this]; ring

end BumpProfile


lemma bump_norm_exp_neg_mul' (s : ℂ) (x : ℝ) : ‖Complex.exp (-s * (x : ℂ))‖ = Real.exp (-(s.re * x)) := by
  rw [Complex.norm_exp]; congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

lemma int_exp_poly {a : ℝ} (ha : 0 < a) (p : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    IntegrableOn (fun x : ℝ => x ^ p * Real.exp (-(a * x))) (Ioi R) := by
  set n : ℕ := ⌈p⌉₊ with hn
  have hpn : p ≤ (n : ℝ) := Nat.le_ceil p
  have hint : IntegrableOn (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-a * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) one_pos ha
  have hint' : IntegrableOn (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-(a * x))) (Ioi R) := by
    refine (hint.mono_set (Ioi_subset_Ioi (by linarith))).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  refine hint'.mono' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x : ℝ => x ^ p * Real.exp (-(a * x)))).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := by have : R < x := hx; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

/-- Integration by parts on `(R, ∞)` against `e^{-sx}`, `Re s > 0`, for functions of polynomial growth. -/
lemma ibp_tail {u u' : ℝ → ℝ} {R : ℝ} (hR : 1 ≤ R) (hu : ∀ x ∈ Ici R, HasDerivAt u (u' x) x) (hcu' : ContinuousOn u' (Ici R)) {s : ℂ} (hs : 0 < s.re)
    (A p : ℝ) (hA : ∀ x ≥ R, |u x| ≤ A * x ^ p) (A' p' : ℝ) (hA' : ∀ x ≥ R, |u' x| ≤ A' * x ^ p') :
    s * ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u x : ℂ) =
      Complex.exp (-s * (R : ℂ)) * (u R : ℂ) + ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u' x : ℂ) := by
  have hR0 : 0 < R := by linarith
  have hcu : ContinuousOn u (Ici R) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hv : ∀ x ∈ Ioi R, HasDerivAt (fun x : ℝ => Complex.exp (-s * (x : ℂ))) (-s * Complex.exp (-s * (x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -s * (x : ℂ)) (-s) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-s)
    exact (h1.cexp).congr_deriv (by ring)
  have hu_c : ∀ x ∈ Ioi R, HasDerivAt (fun x : ℝ => (u x : ℂ)) (u' x : ℂ) x := fun x hx => (hu x (Ioi_subset_Ici_self hx)).ofReal_comp
  set a := s.re with ha
  have hbd : ∀ (w : ℝ → ℝ) (A p : ℝ), (∀ x ≥ R, |w x| ≤ A * x ^ p) → ∀ x ∈ Ioi R,
      ‖Complex.exp (-s * (x : ℂ)) * (w x : ℂ)‖ ≤ |A| * (x ^ p * Real.exp (-(a * x))) := by
    intro w A p hw x hx
    have hx' : R ≤ x := le_of_lt hx
    rw [norm_mul, bump_norm_exp_neg_mul', Complex.norm_real, Real.norm_eq_abs]
    calc Real.exp (-(s.re * x)) * |w x| ≤ Real.exp (-(s.re * x)) * (A * x ^ p) := by gcongr; exact hw x hx'
      _ ≤ Real.exp (-(s.re * x)) * (|A| * x ^ p) := by
          have : 0 ≤ x ^ p := Real.rpow_nonneg (by linarith) _
          gcongr; exact le_abs_self A
      _ = _ := by rw [ha]; ring
  have hmeas : ∀ (w : ℝ → ℝ), ContinuousOn w (Ici R) → AEStronglyMeasurable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (w x : ℂ)) (volume.restrict (Ioi R)) := by
    intro w hw
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).continuousOn).mul
      ((Complex.continuous_ofReal.comp_continuousOn (hw.mono Ioi_subset_Ici_self)))
  have hint : ∀ (w : ℝ → ℝ) (A p : ℝ), ContinuousOn w (Ici R) → (∀ x ≥ R, |w x| ≤ A * x ^ p) →
      IntegrableOn (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (w x : ℂ)) (Ioi R) := by
    intro w A p hw hbw
    refine ((int_exp_poly hs p hR).const_mul |A|).mono' (hmeas w hw) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbd w A p hbw x hx
  have i0 := hint u A p hcu hA
  have i1 := hint u' A' p' hcu' hA'
  have hkey := integral_Ioi_mul_deriv_eq_deriv_mul (u := fun x : ℝ => (u x : ℂ)) (v := fun x : ℝ => Complex.exp (-s * (x : ℂ)))
    (u' := fun x => (u' x : ℂ)) (v' := fun x => -s * Complex.exp (-s * (x : ℂ))) (a := R) (a' := (u R : ℂ) * Complex.exp (-s * (R : ℂ))) (b' := 0)
    hu_c hv
    (by
      refine IntegrableOn.congr_fun (i0.const_mul (-s)) (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    (by
      refine IntegrableOn.congr_fun i1 (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    (by
      have h1 : ContinuousAt (fun x : ℝ => (u x : ℂ) * Complex.exp (-s * (x : ℂ))) R :=
        (Complex.continuous_ofReal.continuousAt.comp (hu R (le_refl R)).continuousAt).mul (by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).continuousAt
      exact h1.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      refine squeeze_zero_norm' (a := fun x : ℝ => |A| * (x ^ p * Real.exp (-(a * x)))) ?_ ?_
      · filter_upwards [eventually_gt_atTop R] with x hx
        have := hbd u A p hA x hx
        rw [Pi.mul_apply, norm_mul, mul_comm, ← norm_mul]
        exact this
      · have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a hs).const_mul |A|
        simpa only [mul_zero, neg_mul] using this)
  have e1 : ∫ x in Ioi R, (u x : ℂ) * (-s * Complex.exp (-s * (x : ℂ))) = -s * ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u x : ℂ) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in Ioi R, (u' x : ℂ) * Complex.exp (-s * (x : ℂ)) = ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u' x : ℂ) := by
    congr 1; funext x; ring
  rw [e1, e2] at hkey
  linear_combination -hkey


/-- Repeated integration by parts on the tail `(R, ∞)`. -/
lemma tail_iter {R : ℝ} (hR : 1 ≤ R) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → (∀ k : ℕ, k ≤ N → ∃ A p : ℝ, ∀ x ≥ R, |iteratedDeriv k u x| ≤ A * x ^ p) →
      IntegrableOn (iteratedDeriv N u) (Ioi R) →
      ‖∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u x : ℂ)‖ ≤
        (∑ m ∈ Finset.range N, (‖s‖⁻¹) ^ (m + 1) * |iteratedDeriv m u R|) + (‖s‖⁻¹) ^ N * ∫ x in Ioi R, |iteratedDeriv N u x| := by
  induction N with
  | zero =>
    intro u hu hb hi
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul, iteratedDeriv_zero] at hi ⊢
    have hR0 : 0 < R := by linarith
    have := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi R)) (f := fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (u x : ℂ))
      (g := fun x => ‖u x‖) hi.norm (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := lt_trans hR0 hx
        rw [norm_mul, bump_norm_exp_neg_mul', Complex.norm_real]
        have : Real.exp (-(s.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hs hx0])
        calc Real.exp (-(s.re * x)) * ‖u x‖ ≤ 1 * ‖u x‖ := by gcongr
          _ = _ := one_mul _)
    simpa only [Real.norm_eq_abs] using this
  | succ N ih =>
    intro u hu hb hi
    have hR0 : 0 < R := by linarith
    have hud : ContDiff ℝ (⊤ : ℕ∞) (deriv u) := by
      have := hu.iterate_deriv 1
      simpa using this
    have hdu : ∀ x : ℝ, HasDerivAt u (deriv u x) x := fun x =>
      ((hu.differentiable (by simp)) x).hasDerivAt
    have hit : ∀ k : ℕ, iteratedDeriv k (deriv u) = iteratedDeriv (k + 1) u := fun k => by
      rw [iteratedDeriv_succ']
    obtain ⟨A0, p0, h0⟩ := hb 0 (by omega)
    obtain ⟨A1, p1, h1⟩ := hb 1 (by omega)
    simp only [iteratedDeriv_zero] at h0
    simp only [iteratedDeriv_one] at h1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have key := ibp_tail hR (fun x _ => hdu x) (hu.continuous_deriv (by simp)).continuousOn hs A0 p0 h0 A1 p1 h1
    have hih := ih (deriv u) hud (fun k hk => by rw [hit k]; exact hb (k + 1) (by omega)) (by rw [hit N]; exact hi)
    have hI : ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * (u x : ℂ) =
        s⁻¹ * (Complex.exp (-s * (R : ℂ)) * (u R : ℂ) + ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * ((deriv u x : ℝ) : ℂ)) := by
      rw [← key]; field_simp
    rw [hI, norm_mul, norm_inv]
    have hexp : ‖Complex.exp (-s * (R : ℂ)) * (u R : ℂ)‖ ≤ |u R| := by
      rw [norm_mul, bump_norm_exp_neg_mul', Complex.norm_real, Real.norm_eq_abs]
      have : Real.exp (-(s.re * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hs hR0])
      calc Real.exp (-(s.re * R)) * |u R| ≤ 1 * |u R| := by gcongr
        _ = _ := one_mul _
    have h2 : ‖Complex.exp (-s * (R : ℂ)) * (u R : ℂ) + ∫ x in Ioi R, Complex.exp (-s * (x : ℂ)) * ((deriv u x : ℝ) : ℂ)‖ ≤
        |u R| + ((∑ m ∈ Finset.range N, (‖s‖⁻¹) ^ (m + 1) * |iteratedDeriv m (deriv u) R|) +
          (‖s‖⁻¹) ^ N * ∫ x in Ioi R, |iteratedDeriv N (deriv u) x|) :=
      (norm_add_le _ _).trans (add_le_add hexp hih)
    have h3 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hsn.le)
    refine h3.trans (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    simp only [hit, iteratedDeriv_zero, pow_succ]
    rw [mul_add, mul_add, Finset.mul_sum]
    have e : ∀ x ∈ Finset.range N, ‖s‖⁻¹ * (‖s‖⁻¹ ^ x * ‖s‖⁻¹ * |iteratedDeriv (x + 1) u R|) =
        ‖s‖⁻¹ ^ x * ‖s‖⁻¹ * ‖s‖⁻¹ * |iteratedDeriv (x + 1) u R| := fun x _ => by ring
    rw [Finset.sum_congr rfl e]
    ring


namespace BumpProfile
variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

/-- The derivatives of `x^j B` obey `|(x^j B)^{(k)}(x)| ≤ D x^{j-β-k}` for `x ≥ 1`. -/
lemma pow_mul_deriv_bound (h : BumpProfile b δ M α β K B) (j k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x → |iteratedDeriv k (fun y : ℝ => y ^ j * B y) x| ≤ D * x ^ ((j : ℝ) - β - k) := by
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (j.descFactorial i : ℝ) * (|K (k - i)| * |M|), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hBc : ContDiff ℝ (⊤ : ℕ∞) B := h.smooth
  have hpow : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ j) := by fun_prop
  rw [iteratedDeriv_fun_mul (hpow.contDiffAt.of_le (by exact_mod_cast le_top)) (hBc.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_mul, iteratedDeriv_pow]
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  rcases le_or_gt i j with hij | hij
  · have hfar := h.far (k - i) x hx
    have hxp : x ^ (j - i) = x ^ (((j : ℝ) - i)) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hij]
    have e : x ^ ((j : ℝ) - β - k) = x ^ (((j : ℝ) - i)) * x ^ (-β - ((k - i : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hx0, Nat.cast_sub hik]; congr 1; ring
    rw [e]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose i : ℝ)), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.descFactorial i : ℝ) * x ^ (j - i))]
    calc (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * |iteratedDeriv (k - i) B x|
        ≤ (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * (K (k - i) * M * x ^ (-β - ((k - i : ℕ) : ℝ))) := by gcongr
      _ ≤ (k.choose i : ℝ) * ((j.descFactorial i : ℝ) * x ^ (j - i)) * (|K (k - i)| * |M| * x ^ (-β - ((k - i : ℕ) : ℝ))) := by
          have hKM : K (k - i) * M ≤ |K (k - i)| * |M| := by
            calc K (k - i) * M ≤ |K (k - i) * M| := le_abs_self _
              _ = _ := abs_mul _ _
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg hx0.le _)) (by positivity)
      _ = (k.choose i : ℝ) * (j.descFactorial i : ℝ) * (|K (k - i)| * |M|) * (x ^ (((j : ℝ) - i)) * x ^ (-β - ((k - i : ℕ) : ℝ))) := by
          rw [hxp]; ring
  · have : j.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hij
    rw [this]; simp only [Nat.cast_zero, zero_mul, mul_zero, abs_zero, zero_mul]
    positivity


lemma tail_bound (h : BumpProfile b δ M α β K B) (hβ : 3 / 2 ≤ β) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → ‖s‖ ≤ 1 →
      ‖∫ x in Ioi ‖s‖⁻¹, Complex.exp (-s * (x : ℂ)) * (((x ^ j * B x : ℝ)) : ℂ)‖ ≤ C * (‖s‖⁻¹) ^ ((j : ℝ) - 1 / 2) := by
  choose D hD0 hD using fun k => h.pow_mul_deriv_bound j k
  have hβ0 : 0 < β := by linarith
  refine ⟨(∑ m ∈ Finset.range (j + 1), D m) + D (j + 1) / β, by
    have : 0 ≤ ∑ m ∈ Finset.range (j + 1), D m := Finset.sum_nonneg fun m _ => hD0 m
    have := hD0 (j + 1)
    positivity, fun s hs hs1 => ?_⟩
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs; simp at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set R : ℝ := ‖s‖⁻¹ with hRdef
  have hR : 1 ≤ R := by rw [hRdef]; exact one_le_inv₀ hsn |>.mpr hs1
  have hR0 : 0 < R := by linarith
  set u : ℝ → ℝ := fun y => y ^ j * B y with hu
  have hucd : ContDiff ℝ (⊤ : ℕ∞) u := by
    have hpow : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ j) := by fun_prop
    exact hpow.mul h.smooth
  have hb : ∀ k : ℕ, k ≤ j + 1 → ∃ A p : ℝ, ∀ x ≥ R, |iteratedDeriv k u x| ≤ A * x ^ p :=
    fun k _ => ⟨D k, (j : ℝ) - β - k, fun x hx => hD k x (by linarith)⟩
  have hint : IntegrableOn (fun x : ℝ => x ^ ((j : ℝ) - β - ((j + 1 : ℕ) : ℝ))) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by push_cast; linarith) hR0
  have hI : IntegrableOn (iteratedDeriv (j + 1) u) (Ioi R) := by
    refine (hint.const_mul (D (j + 1))).mono' ?_ ?_
    · exact ((hucd.continuous_iteratedDeriv (j + 1) (by exact_mod_cast le_top)).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs]; exact hD (j + 1) x (by have : R < x := hx; linarith)
  have ht := tail_iter hR hs (j + 1) u hucd hb hI
  refine ht.trans ?_
  have hexp : ∀ q : ℝ, q ≤ (j : ℝ) - 1 / 2 → R ^ q ≤ R ^ ((j : ℝ) - 1 / 2) := fun q hq => Real.rpow_le_rpow_of_exponent_le hR hq
  have hq1 : (j : ℝ) + 1 - β ≤ (j : ℝ) - 1 / 2 := by linarith
  have hsum : ∑ m ∈ Finset.range (j + 1), R ^ (m + 1) * |iteratedDeriv m u R| ≤ (∑ m ∈ Finset.range (j + 1), D m) * R ^ ((j : ℝ) - 1 / 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have h1 := hD m R hR
    have h2 : R ^ (m + 1) * (D m * R ^ ((j : ℝ) - β - m)) = D m * R ^ ((j : ℝ) + 1 - β) := by
      rw [← Real.rpow_natCast, show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring]
      have : R ^ ((m : ℝ) + 1) * R ^ ((j : ℝ) - β - m) = R ^ ((j : ℝ) + 1 - β) := by
        rw [← Real.rpow_add hR0]; congr 1; ring
      calc R ^ ((m : ℝ) + 1) * (D m * R ^ ((j : ℝ) - β - m)) = D m * (R ^ ((m : ℝ) + 1) * R ^ ((j : ℝ) - β - m)) := by ring
        _ = _ := by rw [this]
    calc R ^ (m + 1) * |iteratedDeriv m u R| ≤ R ^ (m + 1) * (D m * R ^ ((j : ℝ) - β - m)) := by gcongr
      _ = D m * R ^ ((j : ℝ) + 1 - β) := h2
      _ ≤ D m * R ^ ((j : ℝ) - 1 / 2) := by gcongr; exact hD0 m |> fun _ => hD0 m
  have hrem : R ^ (j + 1) * ∫ x in Ioi R, |iteratedDeriv (j + 1) u x| ≤ D (j + 1) / β * R ^ ((j : ℝ) - 1 / 2) := by
    have h1 : ∫ x in Ioi R, |iteratedDeriv (j + 1) u x| ≤ ∫ x in Ioi R, D (j + 1) * x ^ ((j : ℝ) - β - ((j + 1 : ℕ) : ℝ)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _) measurableSet_Ioi fun x hx => hD (j + 1) x (by have : R < x := hx; linarith)
      exact hI.norm
    have h2 : ∫ x in Ioi R, D (j + 1) * x ^ ((j : ℝ) - β - ((j + 1 : ℕ) : ℝ)) = D (j + 1) / β * R ^ (-β) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by push_cast; linarith) hR0]
      have : (j : ℝ) - β - ((j + 1 : ℕ) : ℝ) + 1 = -β := by push_cast; ring
      rw [this]
      field_simp
    have h3 : R ^ (j + 1) * (D (j + 1) / β * R ^ (-β)) = D (j + 1) / β * R ^ ((j : ℝ) + 1 - β) := by
      rw [← Real.rpow_natCast]
      have : R ^ (((j + 1 : ℕ) : ℝ)) * R ^ (-β) = R ^ ((j : ℝ) + 1 - β) := by
        rw [← Real.rpow_add hR0]; congr 1; push_cast; ring
      calc R ^ (((j + 1 : ℕ) : ℝ)) * (D (j + 1) / β * R ^ (-β)) = D (j + 1) / β * (R ^ (((j + 1 : ℕ) : ℝ)) * R ^ (-β)) := by ring
        _ = _ := by rw [this]
    calc R ^ (j + 1) * ∫ x in Ioi R, |iteratedDeriv (j + 1) u x| ≤ R ^ (j + 1) * (D (j + 1) / β * R ^ (-β)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = D (j + 1) / β * R ^ ((j : ℝ) + 1 - β) := h3
      _ ≤ D (j + 1) / β * R ^ ((j : ℝ) - 1 / 2) := by
          have := hD0 (j + 1)
          gcongr
  have hRs : (‖s‖⁻¹) = R := rfl
  rw [hRs]
  calc (∑ m ∈ Finset.range (j + 1), R ^ (m + 1) * |iteratedDeriv m u R|) + R ^ (j + 1) * ∫ x in Ioi R, |iteratedDeriv (j + 1) u x|
      ≤ (∑ m ∈ Finset.range (j + 1), D m) * R ^ ((j : ℝ) - 1 / 2) + D (j + 1) / β * R ^ ((j : ℝ) - 1 / 2) := add_le_add hsum hrem
    _ = _ := by ring


lemma integrableOn_Iic_pow (h : BumpProfile b δ M α β K B) (_hb0 : 0 ≤ b * δ) (j : ℕ) {R : ℝ} (hR : b * δ ≤ R) :
    IntegrableOn (fun x : ℝ => x ^ j * B x) (Iic R) := by
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  have hc : Continuous (fun x : ℝ => x ^ j * B x) := by fun_prop
  have : Iic R = Iio (b * δ) ∪ Icc (b * δ) R := by
    ext x; simp only [mem_Iic, mem_union, mem_Iio, mem_Icc]
    constructor
    · intro hx; by_cases hx' : x < b * δ
      · exact Or.inl hx'
      · exact Or.inr ⟨not_lt.mp hx', hx⟩
    · rintro (hx | ⟨_, hx⟩) <;> linarith
  rw [this]
  refine IntegrableOn.union ?_ hc.integrableOn_Icc
  refine (integrableOn_zero (s := Iio (b * δ))).congr_fun (fun x hx => ?_) measurableSet_Iio
  simp only
  rw [h.support x hx, mul_zero]

lemma head_bound (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (j : ℕ) (hj : 1 ≤ j)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ x in Iic R, ‖x ^ j * B x‖ ≤ ((∫ x : ℝ, ‖B x‖) + 2 * |K 0| * M) * R ^ ((j : ℝ) - 1 / 2) := by
  have hR0 : 0 < R := by linarith
  have hβ1 : 1 < β := by linarith
  have hB := h.integrable_self hbδ hβ1
  have hint : IntegrableOn (fun x : ℝ => ‖x ^ j * B x‖) (Iic R) := (h.integrableOn_Iic_pow hb0 j (by linarith)).norm
  have hdisj : Disjoint (Iic (1 : ℝ)) (Ioc 1 R) := Set.disjoint_left.mpr fun x hx hx' => absurd hx (not_le.mpr hx'.1)
  rw [← Iic_union_Ioc_eq_Iic hR, setIntegral_union hdisj measurableSet_Ioc (hint.mono_set (by intro x hx; exact le_trans (mem_Iic.mp hx) (by linarith)))
    (hint.mono_set (by intro x hx; exact hx.2))]
  have hA : ∫ x in Iic (1 : ℝ), ‖x ^ j * B x‖ ≤ ∫ x : ℝ, ‖B x‖ := by
    refine le_trans (setIntegral_mono_on (hint.mono_set (by intro x hx; exact le_trans (mem_Iic.mp hx) hR)) hB.norm.integrableOn measurableSet_Iic fun x hx => ?_)
      (setIntegral_le_integral hB.norm (ae_of_all _ fun x => norm_nonneg _))
    rcases lt_or_ge x (b * δ) with hx' | hx'
    · rw [h.support x hx']; simp
    · have hx0 : 0 ≤ x := hb0.trans hx'
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0]
      have : x ^ j ≤ 1 := pow_le_one₀ hx0 hx
      calc x ^ j * ‖B x‖ ≤ 1 * ‖B x‖ := by gcongr
        _ = _ := one_mul _
  have hJ : ∫ x in (1 : ℝ)..R, x ^ ((j : ℝ) - 3 / 2) = (R ^ ((j : ℝ) - 1 / 2) - 1) / ((j : ℝ) - 1 / 2) := by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [integral_rpow (Or.inl (by linarith))]
    rw [Real.one_rpow, show (j : ℝ) - 3 / 2 + 1 = (j : ℝ) - 1 / 2 by ring]
  have hB2 : ∫ x in Ioc (1 : ℝ) R, ‖x ^ j * B x‖ ≤ |K 0| * M * ∫ x in (1 : ℝ)..R, x ^ ((j : ℝ) - 3 / 2) := by
    rw [intervalIntegral.integral_of_le hR, ← integral_const_mul]
    have hcI : IntegrableOn (fun x : ℝ => x ^ ((j : ℝ) - 3 / 2)) (Ioc 1 R) := by
      refine (ContinuousOn.integrableOn_Icc (a := 1) (b := R) ?_).mono_set Ioc_subset_Icc_self
      exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
    refine setIntegral_mono_on (hint.mono_set (by intro x hx; exact hx.2)) (hcI.const_mul _) measurableSet_Ioc fun x hx => ?_
    have hx1 : 1 < x := hx.1
    have hx0 : 0 < x := by linarith
    have hfar := h.far 0 x hx1.le
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hfar
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hx0, Real.norm_eq_abs]
    have h1 : x ^ (-β) ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    calc x ^ j * |B x| ≤ x ^ j * (K 0 * M * x ^ (-β)) := by gcongr
      _ ≤ x ^ j * (|K 0| * M * x ^ (-(3 / 2 : ℝ))) := by
          have : K 0 * M ≤ |K 0| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
          gcongr
      _ = |K 0| * M * x ^ ((j : ℝ) - 3 / 2) := by
          rw [show ((j : ℝ) - 3 / 2) = (j : ℝ) + (-(3 / 2 : ℝ)) by ring, Real.rpow_add hx0, Real.rpow_natCast]; ring
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hX : 1 ≤ R ^ ((j : ℝ) - 1 / 2) := Real.one_le_rpow hR (by linarith)
  have hB0 : 0 ≤ ∫ x : ℝ, ‖B x‖ := integral_nonneg fun x => norm_nonneg _
  have hc : 0 < (j : ℝ) - 1 / 2 := by linarith
  have hJ2 : (R ^ ((j : ℝ) - 1 / 2) - 1) / ((j : ℝ) - 1 / 2) ≤ 2 * R ^ ((j : ℝ) - 1 / 2) := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hK : 0 ≤ |K 0| * M := by positivity
  calc (∫ x in Iic (1 : ℝ), ‖x ^ j * B x‖) + ∫ x in Ioc (1 : ℝ) R, ‖x ^ j * B x‖
      ≤ (∫ x : ℝ, ‖B x‖) + |K 0| * M * ∫ x in (1 : ℝ)..R, x ^ ((j : ℝ) - 3 / 2) := add_le_add hA hB2
    _ ≤ (∫ x : ℝ, ‖B x‖) + |K 0| * M * (2 * R ^ ((j : ℝ) - 1 / 2)) := by
        rw [hJ]; gcongr
    _ ≤ (∫ x : ℝ, ‖B x‖) * R ^ ((j : ℝ) - 1 / 2) + 2 * |K 0| * M * R ^ ((j : ℝ) - 1 / 2) := by
        nlinarith
    _ = _ := by ring

lemma bumpLapW_bound (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → ‖s‖ ≤ 1 → ‖bumpLapW B j s‖ ≤ C * (‖s‖⁻¹) ^ ((j : ℝ) - 1 / 2) := by
  obtain ⟨Ct, hCt0, hCt⟩ := h.tail_bound hβ j
  have hβ1 : 1 < β := by linarith
  refine ⟨(∫ x : ℝ, ‖B x‖) + 2 * |K 0| * M + Ct, by
    have : 0 ≤ ∫ x : ℝ, ‖B x‖ := integral_nonneg fun x => norm_nonneg _
    positivity, fun s hs hs1 => ?_⟩
  have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hs; simp at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set R : ℝ := ‖s‖⁻¹ with hRdef
  have hR : 1 ≤ R := by rw [hRdef]; exact one_le_inv₀ hsn |>.mpr hs1
  have hfull : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (((x ^ j * B x : ℝ)) : ℂ)) := by
    have hi := (h.integrable_pow_B_exp hb0 hbδ hβ1 j hs).norm
    refine hi.mono' ?_ (ae_of_all _ fun x => ?_)
    · have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
      exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).mul
        (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => x ^ j * B x))).aestronglyMeasurable
    · rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real, norm_mul_exp]
  unfold bumpLapW
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := R), setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => absurd hx (not_le.mpr hx'))
    measurableSet_Ioi hfull.integrableOn hfull.integrableOn]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∫ x in Iic R, Complex.exp (-s * (x : ℂ)) * (((x ^ j * B x : ℝ)) : ℂ)‖ ≤ ∫ x in Iic R, ‖x ^ j * B x‖ := by
    refine norm_integral_le_of_norm_le ((h.integrableOn_Iic_pow hb0 j (by linarith)).norm) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rcases lt_or_ge x (b * δ) with hx' | hx'
    · rw [h.support x hx']; simp
    · rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real]
      have : Real.exp (-(s.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs.le (hb0.trans hx')])
      calc Real.exp (-(s.re * x)) * ‖x ^ j * B x‖ ≤ 1 * ‖x ^ j * B x‖ := by gcongr
        _ = _ := one_mul _
  have h2 := h.head_bound hb0 hbδ hβ hM j hj hR
  have h3 := hCt s hs hs1
  calc _ ≤ ((∫ x : ℝ, ‖B x‖) + 2 * |K 0| * M) * R ^ ((j : ℝ) - 1 / 2) + Ct * R ^ ((j : ℝ) - 1 / 2) :=
        add_le_add (h1.trans h2) h3
    _ = _ := by ring


lemma norm_exp_sub_one_le_lin {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-s * (x : ℂ)) - 1‖ ≤ 2 * (‖s‖ * x) ∧ ‖Complex.exp (-s * (x : ℂ)) - 1‖ ≤ 2 := by
  have hn : ‖Complex.exp (-s * (x : ℂ))‖ ≤ 1 := by
    rw [bump_norm_exp_neg_mul]; exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs hx])
  have h2 : ‖Complex.exp (-s * (x : ℂ)) - 1‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (-s * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by simp only [norm_one]; linarith
      _ = 2 := by norm_num
  refine ⟨?_, h2⟩
  have hz : ‖-s * (x : ℂ)‖ = ‖s‖ * x := by rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  rcases le_or_gt (‖s‖ * x) 1 with h1 | h1
  · have := Complex.norm_exp_sub_one_le (x := -s * (x : ℂ)) (by rw [hz]; exact h1)
    rw [hz] at this; exact this
  · nlinarith

lemma holder_zero (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → ‖s‖ ≤ 1 → ‖bumpLaplace B s - bumpLaplace B 0‖ ≤ C * ‖s‖ ^ (1 / 2 : ℝ) := by
  have hβ1 : 1 < β := by linarith
  have hB := h.integrable_self hbδ hβ1
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  have hI0 : 0 ≤ ∫ x : ℝ, ‖B x‖ := integral_nonneg fun x => norm_nonneg _
  set Ch : ℝ := (∫ x : ℝ, ‖B x‖) + 2 * |K 0| * M with hCh
  set Ct : ℝ := 2 * |K 0| * M / (β - 1) with hCt
  have hCh0 : 0 ≤ Ch := by rw [hCh]; positivity
  have hβ' : 0 < β - 1 := by linarith
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  refine ⟨2 * Ch + Ct, by positivity, fun s hs hs1 => ?_⟩
  by_cases hs0 : s = 0
  · subst hs0; simp
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set R : ℝ := ‖s‖⁻¹ with hRdef
  have hR : 1 ≤ R := by rw [hRdef]; exact one_le_inv₀ hsn |>.mpr hs1
  have hR0 : 0 < R := by linarith
  have hFs : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (B x : ℂ)) := by
    refine hB.norm.mono' ?_ (ae_of_all _ fun x => h.norm_exp_mul_le hb0 hs x)
    exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).mul (Complex.continuous_ofReal.comp hBc)).aestronglyMeasurable
  have hF0 : Integrable (fun x : ℝ => (B x : ℂ)) := hB.ofReal
  have hdiff : bumpLaplace B s - bumpLaplace B 0 = ∫ x : ℝ, (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ) := by
    unfold bumpLaplace
    rw [← integral_sub hFs (by simpa using hF0)]
    congr 1; funext x; simp; ring
  have hG : Integrable (fun x : ℝ => (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ)) := by
    refine (hFs.sub hF0).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]; ring
  rw [hdiff, ← setIntegral_univ, ← Iic_union_Ioi (a := R), setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => absurd hx (not_le.mpr hx'))
    measurableSet_Ioi hG.integrableOn hG.integrableOn]
  refine (norm_add_le _ _).trans ?_
  -- head
  have hhead : ‖∫ x in Iic R, (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ)‖ ≤ 2 * Ch * ‖s‖ ^ (1 / 2 : ℝ) := by
    have h1 : ‖∫ x in Iic R, (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ)‖ ≤ ∫ x in Iic R, 2 * ‖s‖ * ‖x ^ 1 * B x‖ := by
      refine norm_integral_le_of_norm_le (((h.integrableOn_Iic_pow hb0 1 (by linarith)).norm).const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      rcases lt_or_ge x (b * δ) with hx' | hx'
      · rw [h.support x hx']; simp
      · have hx0 : 0 ≤ x := hb0.trans hx'
        rw [norm_mul, Complex.norm_real, pow_one, norm_mul, Real.norm_eq_abs x, abs_of_nonneg hx0]
        have := (norm_exp_sub_one_le_lin hs hx0).1
        calc ‖Complex.exp (-s * (x : ℂ)) - 1‖ * ‖B x‖ ≤ 2 * (‖s‖ * x) * ‖B x‖ := by gcongr
          _ = 2 * ‖s‖ * (x * ‖B x‖) := by ring
    rw [integral_const_mul] at h1
    have h2 := h.head_bound hb0 hbδ hβ hM 1 le_rfl hR
    simp only [Nat.cast_one] at h2
    have h3 : ‖s‖ * R ^ ((1 : ℝ) - 1 / 2) = ‖s‖ ^ (1 / 2 : ℝ) := by
      rw [hRdef, Real.inv_rpow hsn.le, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      have hp : 0 < ‖s‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hsn _
      have e : ‖s‖ = ‖s‖ ^ (1 / 2 : ℝ) * ‖s‖ ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hsn]; norm_num
      calc ‖s‖ * (‖s‖ ^ (1 / 2 : ℝ))⁻¹ = (‖s‖ ^ (1 / 2 : ℝ) * ‖s‖ ^ (1 / 2 : ℝ)) * (‖s‖ ^ (1 / 2 : ℝ))⁻¹ := by rw [← e]
        _ = ‖s‖ ^ (1 / 2 : ℝ) := by field_simp
    calc _ ≤ 2 * ‖s‖ * ∫ x in Iic R, ‖x ^ 1 * B x‖ := h1
      _ ≤ 2 * ‖s‖ * (Ch * R ^ ((1 : ℝ) - 1 / 2)) := by gcongr
      _ = 2 * Ch * (‖s‖ * R ^ ((1 : ℝ) - 1 / 2)) := by ring
      _ = _ := by rw [h3]
  -- tail
  have htail : ‖∫ x in Ioi R, (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ)‖ ≤ Ct * ‖s‖ ^ (1 / 2 : ℝ) := by
    have hint : IntegrableOn (fun x : ℝ => x ^ (-β)) (Ioi R) := integrableOn_Ioi_rpow_of_lt (by linarith) hR0
    have h1 : ‖∫ x in Ioi R, (Complex.exp (-s * (x : ℂ)) - 1) * (B x : ℂ)‖ ≤ ∫ x in Ioi R, 2 * (|K 0| * M) * x ^ (-β) := by
      refine norm_integral_le_of_norm_le ((hint.const_mul _)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 < x := by have : R < x := hx; linarith
      have hx0 : 0 < x := by linarith
      rw [norm_mul, Complex.norm_real]
      have h2 := (norm_exp_sub_one_le_lin hs hx0.le).2
      have hfar := h.far 0 x hx1.le
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hfar
      have : ‖B x‖ ≤ |K 0| * M * x ^ (-β) := by
        rw [Real.norm_eq_abs]
        refine hfar.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM) (Real.rpow_nonneg hx0.le _)
      calc ‖Complex.exp (-s * (x : ℂ)) - 1‖ * ‖B x‖ ≤ 2 * (|K 0| * M * x ^ (-β)) := by
            exact mul_le_mul h2 this (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hR0] at h1
    have h2 : -R ^ (-β + 1) / (-β + 1) = R ^ (1 - β) / (β - 1) := by
      have hne : β - 1 ≠ 0 := by linarith
      have hne' : -β + 1 ≠ 0 := by linarith
      rw [show -β + 1 = 1 - β by ring]
      have hne'' : 1 - β ≠ 0 := by linarith
      field_simp
      ring
    rw [h2] at h1
    have h3 : R ^ (1 - β) ≤ R ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    have h4 : R ^ (-(1 / 2 : ℝ)) = ‖s‖ ^ (1 / 2 : ℝ) := by
      rw [hRdef, Real.inv_rpow hsn.le, Real.rpow_neg hsn.le, inv_inv]
    have hβ' : 0 < β - 1 := by linarith
    calc _ ≤ 2 * (|K 0| * M) * (R ^ (1 - β) / (β - 1)) := h1
      _ ≤ 2 * (|K 0| * M) * (R ^ (-(1 / 2 : ℝ)) / (β - 1)) := by gcongr
      _ = Ct * ‖s‖ ^ (1 / 2 : ℝ) := by rw [h4, hCt]; ring
  calc _ ≤ 2 * Ch * ‖s‖ ^ (1 / 2 : ℝ) + Ct * ‖s‖ ^ (1 / 2 : ℝ) := add_le_add hhead htail
    _ = _ := by ring

end BumpProfile

lemma norm_bumpLapW_le {f : ℝ → ℝ} (hz : ∀ x : ℝ, x < 0 → f x = 0) {s : ℂ} (hs : 0 ≤ s.re) (m : ℕ)
    (hi : Integrable (fun x : ℝ => x ^ m * f x)) : ‖bumpLapW f m s‖ ≤ ∫ x : ℝ, ‖x ^ m * f x‖ := by
  unfold bumpLapW
  refine norm_integral_le_of_norm_le hi.norm (ae_of_all _ fun x => ?_)
  rw [norm_mul, bump_norm_exp_neg_mul, Complex.norm_real]
  rcases lt_or_ge x 0 with hx | hx
  · rw [hz x hx]; simp
  · have : Real.exp (-(s.re * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hs hx])
    calc Real.exp (-(s.re * x)) * ‖x ^ m * f x‖ ≤ 1 * ‖x ^ m * f x‖ := by gcongr
      _ = _ := one_mul _

/-- Crude bounds on `E₀, E₁, E₂` for `Re s ≥ 0`, `s ≠ 0`, in terms of `t = ‖s‖⁻¹`. -/
lemma edgeE_norm_le {f : ℝ → ℝ} (hz : ∀ x : ℝ, x < 0 → f x = 0) (hI : ∀ m : ℕ, m ≤ 2 → Integrable (fun x : ℝ => x ^ m * f x))
    (κ c : ℝ) (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s ≠ 0 →
      ‖edgeE0 f (κ : ℂ) s‖ ≤ A * ((‖s‖⁻¹) ^ 4 + (‖s‖⁻¹) ^ 5 + (‖s‖⁻¹) ^ 6) ∧
      ‖edgeE1 f (κ : ℂ) c s‖ ≤ A * ((‖s‖⁻¹) ^ 4 + (‖s‖⁻¹) ^ 5 + (‖s‖⁻¹) ^ 6) ∧
      ‖edgeE2 f (κ : ℂ) c s‖ ≤ A * ((‖s‖⁻¹) ^ 4 + (‖s‖⁻¹) ^ 5 + (‖s‖⁻¹) ^ 6) := by
  set Q0 := ∫ x : ℝ, ‖x ^ 0 * f x‖ with hQ0
  set Q1 := ∫ x : ℝ, ‖x ^ 1 * f x‖ with hQ1
  set Q2 := ∫ x : ℝ, ‖x ^ 2 * f x‖ with hQ2
  have hQ00 : 0 ≤ Q0 := integral_nonneg fun x => norm_nonneg _
  have hQ10 : 0 ≤ Q1 := integral_nonneg fun x => norm_nonneg _
  have hQ20 : 0 ≤ Q2 := integral_nonneg fun x => norm_nonneg _
  refine ⟨20 * κ * (1 + c) ^ 2 * (Q0 + Q1 + Q2), by positivity, fun s hs hs0 => ?_⟩
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  set t : ℝ := ‖s‖⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hsn
  have hz4 : ∀ n : ℕ, ‖s ^ (-(n : ℤ))‖ = t ^ n := fun n => by
    rw [norm_zpow, zpow_neg, zpow_natCast, ← inv_pow, ht]
  have e4 : ‖s ^ (-4 : ℤ)‖ = t ^ 4 := by simpa using hz4 4
  have e5 : ‖s ^ (-5 : ℤ)‖ = t ^ 5 := by simpa using hz4 5
  have e6 : ‖s ^ (-6 : ℤ)‖ = t ^ 6 := by simpa using hz4 6
  have q0 : ‖bumpLapW f 0 s‖ ≤ Q0 := norm_bumpLapW_le hz hs 0 (hI 0 (by norm_num))
  have q1 : ‖bumpLapW f 1 s‖ ≤ Q1 := norm_bumpLapW_le hz hs 1 (hI 1 (by norm_num))
  have q2 : ‖bumpLapW f 2 s‖ ≤ Q2 := norm_bumpLapW_le hz hs 2 (hI 2 (by norm_num))
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hκn : ‖(κ : ℂ)‖ = κ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  have hT4 : 0 ≤ t ^ 4 := by positivity
  have hT5 : 0 ≤ t ^ 5 := by positivity
  have hT6 : 0 ≤ t ^ 6 := by positivity
  have hA : 0 ≤ κ * (1 + c) ^ 2 * (Q0 + Q1 + Q2) := by positivity
  set S := Q0 + Q1 + Q2 with hS
  set Y := κ * (1 + c) ^ 2 * S with hY
  have hY0 : 0 ≤ Y := by positivity
  have hkc : ∀ Q : ℝ, 0 ≤ Q → Q ≤ S → κ * c * Q ≤ Y := fun Q hQ hQS => by
    rw [hY]
    have : c ≤ (1 + c) ^ 2 := by nlinarith
    calc κ * c * Q ≤ κ * (1 + c) ^ 2 * Q := by gcongr
      _ ≤ κ * (1 + c) ^ 2 * S := by gcongr
  have hkc2 : ∀ Q : ℝ, 0 ≤ Q → Q ≤ S → κ * c ^ 2 * Q ≤ Y := fun Q hQ hQS => by
    rw [hY]
    have : c ^ 2 ≤ (1 + c) ^ 2 := by nlinarith
    calc κ * c ^ 2 * Q ≤ κ * (1 + c) ^ 2 * Q := by gcongr
      _ ≤ κ * (1 + c) ^ 2 * S := by gcongr
  have hk0 : ∀ Q : ℝ, 0 ≤ Q → Q ≤ S → κ * Q ≤ Y := fun Q hQ hQS => by
    rw [hY]
    have : (1 : ℝ) ≤ (1 + c) ^ 2 := by nlinarith
    calc κ * Q ≤ κ * (1 + c) ^ 2 * Q := by nlinarith [mul_nonneg hκ hQ]
      _ ≤ κ * (1 + c) ^ 2 * S := by gcongr
  have hQ0S : Q0 ≤ S := by rw [hS]; linarith
  have hQ1S : Q1 ≤ S := by rw [hS]; linarith
  have hQ2S : Q2 ≤ S := by rw [hS]; linarith
  have hAeq : 20 * κ * (1 + c) ^ 2 * (Q0 + Q1 + Q2) = 20 * Y := by rw [hY, hS]; ring
  rw [hAeq]
  refine ⟨?_, ?_, ?_⟩
  · unfold edgeE0
    rw [norm_mul, norm_mul, hκn, e4]
    calc κ * t ^ 4 * ‖bumpLapW f 0 s‖ ≤ κ * t ^ 4 * Q0 := by gcongr
      _ = t ^ 4 * (κ * Q0) := by ring
      _ ≤ t ^ 4 * Y := by gcongr; exact hk0 Q0 hQ00 hQ0S
      _ ≤ 20 * Y * (t ^ 4 + t ^ 5 + t ^ 6) := by linarith [mul_nonneg hY0 hT4, mul_nonneg hY0 hT5, mul_nonneg hY0 hT6]
  · unfold edgeE1
    rw [norm_mul, norm_neg, norm_mul, hκn, norm_mul, hcn, Complex.norm_I, mul_one]
    have hin : ‖4 * s ^ (-5 : ℤ) * bumpLapW f 0 s + s ^ (-4 : ℤ) * bumpLapW f 1 s‖ ≤ 4 * t ^ 5 * Q0 + t ^ 4 * Q1 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_mul, e5]
        have : ‖(4 : ℂ)‖ = 4 := by simp
        rw [this]; gcongr
      · rw [norm_mul, e4]; gcongr
    calc κ * c * ‖4 * s ^ (-5 : ℤ) * bumpLapW f 0 s + s ^ (-4 : ℤ) * bumpLapW f 1 s‖ ≤ κ * c * (4 * t ^ 5 * Q0 + t ^ 4 * Q1) := by gcongr
      _ = 4 * t ^ 5 * (κ * c * Q0) + t ^ 4 * (κ * c * Q1) := by ring
      _ ≤ 4 * t ^ 5 * Y + t ^ 4 * Y := by
          have a := hkc Q0 hQ00 hQ0S
          have b := hkc Q1 hQ10 hQ1S
          gcongr
      _ ≤ 20 * Y * (t ^ 4 + t ^ 5 + t ^ 6) := by linarith [mul_nonneg hY0 hT4, mul_nonneg hY0 hT5, mul_nonneg hY0 hT6]
  · unfold edgeE2
    rw [norm_mul, norm_neg, norm_mul, hκn, norm_pow, hcn]
    have hin : ‖20 * s ^ (-6 : ℤ) * bumpLapW f 0 s + 8 * s ^ (-5 : ℤ) * bumpLapW f 1 s + s ^ (-4 : ℤ) * bumpLapW f 2 s‖ ≤
        20 * t ^ 6 * Q0 + 8 * t ^ 5 * Q1 + t ^ 4 * Q2 := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul, norm_mul, e6]
        have : ‖(20 : ℂ)‖ = 20 := by simp
        rw [this]; gcongr
      · rw [norm_mul, norm_mul, e5]
        have : ‖(8 : ℂ)‖ = 8 := by simp
        rw [this]; gcongr
      · rw [norm_mul, e4]; gcongr
    calc κ * c ^ 2 * ‖20 * s ^ (-6 : ℤ) * bumpLapW f 0 s + 8 * s ^ (-5 : ℤ) * bumpLapW f 1 s + s ^ (-4 : ℤ) * bumpLapW f 2 s‖
        ≤ κ * c ^ 2 * (20 * t ^ 6 * Q0 + 8 * t ^ 5 * Q1 + t ^ 4 * Q2) := by gcongr
      _ = 20 * t ^ 6 * (κ * c ^ 2 * Q0) + 8 * t ^ 5 * (κ * c ^ 2 * Q1) + t ^ 4 * (κ * c ^ 2 * Q2) := by ring
      _ ≤ 20 * t ^ 6 * Y + 8 * t ^ 5 * Y + t ^ 4 * Y := by
          have a := hkc2 Q0 hQ00 hQ0S
          have b := hkc2 Q1 hQ10 hQ1S
          have c' := hkc2 Q2 hQ20 hQ2S
          gcongr
      _ ≤ 20 * Y * (t ^ 4 + t ^ 5 + t ^ 6) := by linarith [mul_nonneg hY0 hT4, mul_nonneg hY0 hT5, mul_nonneg hY0 hT6]

lemma continuousOn_edgeE {f : ℝ → ℝ} (hf : Continuous f) (hz : ∀ x : ℝ, x < 0 → f x = 0)
    (hI : ∀ m : ℕ, m ≤ 2 → Integrable (fun x : ℝ => x ^ m * f x)) (κ : ℂ) (c : ℝ) :
    ContinuousOn (edgeE0 f κ) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} ∧ ContinuousOn (edgeE1 f κ c) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} ∧
      ContinuousOn (edgeE2 f κ c) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := by
  have hl : ∀ m : ℕ, m ≤ 2 → ContinuousOn (bumpLapW f m) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := fun m hm =>
    (continuousOn_bumpLapW hf hz (hI m hm)).mono fun s hs => hs.1
  have hzp : ∀ n : ℤ, ContinuousOn (fun s : ℂ => s ^ n) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := fun n =>
    (continuousOn_zpow₀ n).mono fun s hs => hs.2
  have t4 : ContinuousOn (fun s : ℂ => s ^ (-4 : ℤ) * bumpLapW f 1 s) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := (hzp _).mul (hl 1 (by norm_num))
  have t4' : ContinuousOn (fun s : ℂ => s ^ (-4 : ℤ) * bumpLapW f 2 s) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := (hzp _).mul (hl 2 (by norm_num))
  have t5 : ContinuousOn (fun s : ℂ => 4 * s ^ (-5 : ℤ) * bumpLapW f 0 s) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} :=
    (continuousOn_const.mul (hzp _)).mul (hl 0 (by norm_num))
  have t5' : ContinuousOn (fun s : ℂ => 8 * s ^ (-5 : ℤ) * bumpLapW f 1 s) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} :=
    (continuousOn_const.mul (hzp _)).mul (hl 1 (by norm_num))
  have t6 : ContinuousOn (fun s : ℂ => 20 * s ^ (-6 : ℤ) * bumpLapW f 0 s) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} :=
    (continuousOn_const.mul (hzp _)).mul (hl 0 (by norm_num))
  refine ⟨?_, ?_, ?_⟩
  · unfold edgeE0
    exact (continuousOn_const.mul (hzp _)).mul (hl 0 (by norm_num))
  · unfold edgeE1
    exact (continuousOn_const (c := -(κ * ((c : ℂ) * Complex.I)))).mul (t5.add t4)
  · unfold edgeE2
    exact (continuousOn_const (c := -(κ * (c : ℂ) ^ 2))).mul ((t6.add t5').add t4')

lemma pnorm (c τ η : ℝ) : ‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖ = Real.sqrt ((c * τ) ^ 2 + η ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, mul_one, zero_add, Complex.add_im, Complex.mul_im]
  congr 1; ring

/-- The edge trace of `ΔW_c` on `τ ≠ 0`, with its first two derivatives. -/
lemma bump_edge_calculus {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ)
    (hbδ : b * δ ≤ 1) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    let κ : ℝ := c ^ (-(1 / 3 : ℝ))
    let W : ℂ → ℂ := fun ζ => (κ : ℂ) * bumpLaplace B ((c : ℂ) * ζ)
    (∀ τ : ℝ, τ ≠ 0 → HasDerivAt (stripEdge0 W) (edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))) τ) ∧
    (∀ τ : ℝ, τ ≠ 0 → HasDerivAt (fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)))
        (edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))) τ) ∧
    (∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = edgeE0 (iteratedDeriv 4 B) (κ : ℂ) (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))) := by
  intro κ W
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  obtain ⟨hf, hz, hI⟩ := h.f4_data hbδ hb0 hβ1
  have hp : ∀ τ : ℝ, τ ≠ 0 → ((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ) ≠ 0 := fun τ hτ h0 => by
    have := congrArg Complex.im h0
    simp at this
    rcases this with h1 | h1
    · linarith
    · exact hτ h1
  have hpre : ∀ τ : ℝ, (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)).re = 0 := fun τ => by simp
  have hg : ∀ τ : ℝ, τ ≠ 0 → stripEdge0 W τ = edgeE0 (iteratedDeriv 4 B) (κ : ℂ) (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) := by
    intro τ hτ
    rw [h.edgeE0_eq hb0 hbδ hβ1 (κ : ℂ) (by rw [hpre]) (hp τ hτ)]
    unfold stripEdge0
    show (κ : ℂ) * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) = _
    congr 2
    push_cast; ring
  have hD : ∀ τ : ℝ, τ ≠ 0 → HasDerivAt (fun τ : ℝ => edgeE0 (iteratedDeriv 4 B) (κ : ℂ) (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)))
      (edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))) τ ∧
      HasDerivAt (fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)))
        (edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))) τ :=
    fun τ hτ => hasDerivAt_edgeE hf hz hI le_rfl (κ : ℂ) c τ (hp τ hτ)
  refine ⟨fun τ hτ => ?_, fun τ hτ => (hD τ hτ).2, hg⟩
  have hev : (stripEdge0 W) =ᶠ[nhds τ] fun τ : ℝ => edgeE0 (iteratedDeriv 4 B) (κ : ℂ) (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) := by
    filter_upwards [isOpen_ne.mem_nhds hτ] with τ' hτ' using hg τ' hτ'
  exact ((hD τ hτ).1).congr_of_eventuallyEq hev

set_option maxHeartbeats 1600000 in
/-- **`uct:bump-symbol`, (M3) at `ζ = 0`** (`StripEdge0` with `α = 1/2`) for `ΔW_c(ζ) = c^{-1/3} B̂(cζ)`. -/
theorem bump_stripEdge0 {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ)
    (hbδ : b * δ ≤ 1) (hM : 0 ≤ M) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    StripEdge0 (1 / 2) (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  set κ : ℝ := c ^ (-(1 / 3 : ℝ)) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hc _
  set W : ℂ → ℂ := fun ζ => (κ : ℂ) * bumpLaplace B ((c : ℂ) * ζ) with hW
  obtain ⟨hd1, hd2, hg⟩ := bump_edge_calculus hb hβ K hδ0 hbδ hc h
  obtain ⟨hf, hz, hI⟩ := h.f4_data hbδ hb0 hβ1
  obtain ⟨hC0, hC1, hC2⟩ := continuousOn_edgeE hf hz hI (κ : ℂ) c
  obtain ⟨A, hA0, hAb⟩ := edgeE_norm_le hz hI κ c hκ0.le hc.le
  obtain ⟨CH, hCH0, hCH⟩ := h.holder_zero hb0 hbδ hβ hM
  obtain ⟨C1, hC10, hL1⟩ := h.bumpLapW_bound hb0 hbδ hβ hM 1 le_rfl
  obtain ⟨C2, hC20, hL2⟩ := h.bumpLapW_bound hb0 hbδ hβ hM 2 (by norm_num)
  set p : ℝ → ℂ := fun τ => ((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ) with hp
  have hpn : ∀ τ : ℝ, ‖p τ‖ = c * |τ| := fun τ => by
    rw [hp]; dsimp only; rw [pnorm]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hc]
  have hpne : ∀ τ : ℝ, τ ≠ 0 → p τ ≠ 0 := fun τ hτ h0 => by
    have := hpn τ; rw [h0, norm_zero] at this
    have : 0 < c * |τ| := mul_pos hc (abs_pos.mpr hτ)
    linarith
  have hpre : ∀ τ : ℝ, (p τ).re = 0 := fun τ => by simp [hp]
  have hder1 : ∀ τ : ℝ, τ ≠ 0 → deriv (stripEdge0 W) τ = edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (p τ) := fun τ hτ => (hd1 τ hτ).deriv
  have hder2 : ∀ τ : ℝ, τ ≠ 0 → deriv (deriv (stripEdge0 W)) τ = edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (p τ) := by
    intro τ hτ
    have hev : deriv (stripEdge0 W) =ᶠ[nhds τ] fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (p τ) := by
      filter_upwards [isOpen_ne.mem_nhds hτ] with τ' hτ' using hder1 τ' hτ'
    rw [hev.deriv_eq]; exact (hd2 τ hτ).deriv
  have hopen : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hmaps : ∀ τ : ℝ, τ ≠ 0 → p τ ∈ {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := fun τ hτ => ⟨by rw [hpre], hpne τ hτ⟩
  have hpcont : Continuous p := by
    rw [hp]; fun_prop
  have hE1c : ContinuousOn (fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (p τ)) {τ : ℝ | τ ≠ 0} :=
    hC1.comp hpcont.continuousOn fun τ hτ => hmaps τ hτ
  have hE2c : ContinuousOn (fun τ : ℝ => edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (p τ)) {τ : ℝ | τ ≠ 0} :=
    hC2.comp hpcont.continuousOn fun τ hτ => hmaps τ hτ
  have hlimit : ∀ (E : ℂ → ℂ), ContinuousOn E {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} → ∀ τ : ℝ, τ ≠ 0 → ∀ Bd : ℝ,
      (∀ η : ℝ, 0 < η → η < 1 / 2 → ‖E (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))‖ ≤ Bd) → ‖E (p τ)‖ ≤ Bd := by
    intro E hE τ hτ Bd hbd
    have hcw : ContinuousWithinAt (fun η : ℝ => E (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) (Set.Ici 0) 0 := by
      have h1 : ContinuousWithinAt E {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) :=
        hE _ (by
          refine ⟨by simp, ?_⟩
          have := hpne τ hτ
          simpa [hp] using this)
      have hfc : ContinuousWithinAt (fun η : ℝ => ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) (Set.Ici 0) 0 :=
        (by fun_prop : Continuous fun η : ℝ => ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)).continuousWithinAt
      have hmap : Set.MapsTo (fun η : ℝ => ((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)) (Set.Ici 0) {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := by
        intro η hη
        refine ⟨by simp; exact hη, ?_⟩
        intro h0
        have := congrArg Complex.im h0
        simp at this
        rcases this with h1 | h1
        · linarith
        · exact hτ h1
      exact ContinuousWithinAt.comp h1 hfc hmap
    have ht : Filter.Tendsto (fun η : ℝ => E (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (E (p τ))) := by
      have := (hcw.mono Set.Ioi_subset_Ici_self).tendsto
      simpa [hp] using this
    refine le_of_tendsto (ht.norm) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with η hη using hbd η hη.1 hη.2
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h2, contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨fun τ hτ => (hd1 τ hτ).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [h1, contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨?_, fun h => absurd h (by simp), ?_⟩
    · intro τ hτ
      refine (((hd2 τ hτ).differentiableAt).differentiableWithinAt).congr (fun τ' hτ' => hder1 τ' hτ') (hder1 τ hτ)
    · rw [contDiffOn_zero]
      exact hE2c.congr fun τ hτ => hder2 τ hτ
  · -- near region
    have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
    have hz0 : ∀ x : ℝ, x < 0 → B x = 0 := fun x hx => h.support x (by linarith)
    set nB : ℝ := ∫ x : ℝ, ‖B x‖ with hnB
    have hnB0 : 0 ≤ nB := integral_nonneg fun x => norm_nonneg _
    have hF0 : ‖bumpLaplace B 0‖ ≤ nB := by
      have := norm_bumpLapW_le hz0 (s := 0) (by simp) 0 (by simpa using h.integrable_self hbδ hβ1)
      rw [BumpProfile.bumpLapW_zero_B] at this
      simpa [hnB] using this
    have hg0 : ‖stripEdge0 W 0‖ ≤ κ * nB := by
      unfold stripEdge0
      show ‖(κ : ℂ) * bumpLaplace B ((c : ℂ) * (((0 : ℝ) : ℂ) * Complex.I))‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ0]
      simp only [Complex.ofReal_zero, zero_mul, mul_zero]
      exact mul_le_mul_of_nonneg_left hF0 hκ0.le
    set Cn0 : ℝ := κ * CH * c ^ (1 / 2 : ℝ) with hCn0
    set Cn0' : ℝ := (112 * A + κ * nB) * (2 * c) ^ (1 / 2 : ℝ) with hCn0'
    set Cn1 : ℝ := κ * c * C1 * (c ^ (-(1 / 2 : ℝ))) with hCn1
    set Cn2 : ℝ := κ * c ^ 2 * C2 * (c ^ (-(3 / 2 : ℝ))) with hCn2
    have hc12 : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc.le _
    have hCn0n : 0 ≤ Cn0 := by rw [hCn0]; positivity
    have h2c : 0 ≤ (2 * c) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hCn0'n : 0 ≤ Cn0' := by rw [hCn0']; positivity
    have hCn1n : 0 ≤ Cn1 := by rw [hCn1]; have := Real.rpow_nonneg hc.le (-(1 / 2 : ℝ)); positivity
    have hCn2n : 0 ≤ Cn2 := by rw [hCn2]; have := Real.rpow_nonneg hc.le (-(3 / 2 : ℝ)); positivity
    refine ⟨Cn0 + Cn0' + Cn1 + Cn2 + 112 * A, fun τ hτ0 hτ1 => ?_⟩
    have hu0 : 0 < |τ| := abs_pos.mpr hτ0
    have hnegpow : ∀ q : ℝ, q ≤ 0 → 1 ≤ |τ| ^ q := fun q hq => Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hτ1 hq
    have hpow0 : ∀ q : ℝ, 0 ≤ |τ| ^ q := fun q => Real.rpow_nonneg hu0.le q
    have hCsum : ∀ x : ℝ, 0 ≤ x → x ≤ Cn0 + Cn0' + Cn1 + Cn2 + 112 * A → ∀ y : ℝ, 0 ≤ y → x * y ≤ (Cn0 + Cn0' + Cn1 + Cn2 + 112 * A) * y :=
      fun x _ hx y hy => mul_le_mul_of_nonneg_right hx hy
    have hmulinv : ∀ q : ℝ, ((c * |τ|)⁻¹) ^ q = c ^ (-q) * |τ| ^ (-q) := fun q => by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), Real.mul_rpow hc.le hu0.le]
    rcases lt_or_ge (c * |τ|) (1 / 2) with hsmall | hbig
    · -- cut region
      have hq : ∀ η : ℝ, 0 < η → η < 1 / 2 → c * |τ| ≤ ‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖ ∧
          ‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖ ≤ 1 := by
        intro η hη hη1
        rw [pnorm]
        refine ⟨?_, ?_⟩
        · calc c * |τ| = Real.sqrt ((c * τ) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hc]
            _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg η])
        · rw [Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          have : (c * τ) ^ 2 = (c * |τ|) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
          rw [this]
          nlinarith [mul_pos hc hu0]
      have hqre : ∀ η : ℝ, 0 < η → (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)).re = η := fun η _ => by simp
      have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      have hκn : ‖(κ : ℂ)‖ = κ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ0]
      have hinvle : ∀ η : ℝ, 0 < η → η < 1 / 2 → ∀ e : ℝ, 0 ≤ e →
          (‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖⁻¹) ^ e ≤ ((c * |τ|)⁻¹) ^ e := by
        intro η hη hη1 e he
        exact Real.rpow_le_rpow (by positivity) (inv_anti₀ (by positivity) (hq η hη hη1).1) he
      refine ⟨?_, ?_, ?_⟩
      · set s0 : ℂ := (c : ℂ) * ((τ : ℂ) * Complex.I) with hs0def
        have hsn : ‖s0‖ = c * |τ| := by
          rw [hs0def, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hc]
        have hsre : s0.re = 0 := by simp [hs0def]
        have hh := hCH s0 (by rw [hsre]) (by rw [hsn]; linarith)
        have e1 : stripEdge0 W τ - stripEdge0 W 0 = (κ : ℂ) * (bumpLaplace B s0 - bumpLaplace B 0) := by
          unfold stripEdge0
          show (κ : ℂ) * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) - (κ : ℂ) * bumpLaplace B ((c : ℂ) * (((0 : ℝ) : ℂ) * Complex.I)) = _
          simp only [Complex.ofReal_zero, zero_mul, mul_zero]
          rw [← mul_sub]
        rw [e1, norm_mul, hκn]
        rw [hsn] at hh
        calc κ * ‖bumpLaplace B s0 - bumpLaplace B 0‖ ≤ κ * (CH * (c * |τ|) ^ (1 / 2 : ℝ)) := by gcongr
          _ = Cn0 * |τ| ^ (1 / 2 : ℝ) := by rw [Real.mul_rpow hc.le hu0.le, hCn0]; ring
          _ ≤ (Cn0 + Cn0' + Cn1 + Cn2 + 112 * A) * |τ| ^ (1 / 2 : ℝ) := by
              have := hpow0 (1 / 2); gcongr; linarith [hCn0'n, hCn1n, hCn2n, mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
      · rw [hder1 τ hτ0]
        have hb1 := hlimit (edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c) hC1 τ hτ0 (κ * c * (C1 * ((c * |τ|)⁻¹) ^ ((1 : ℝ) - 1 / 2))) (by
          intro η hη hη1
          rw [(h.edgeE_eq_laplace hb0 hbδ hβ1 hη (κ : ℂ) c τ).1, norm_mul, norm_neg, norm_mul, hκn, norm_mul, hcn, Complex.norm_I, mul_one]
          have hL := hL1 _ (by rw [hqre η hη]; exact hη) (hq η hη hη1).2
          simp only [Nat.cast_one] at hL
          calc κ * c * ‖bumpLapW B 1 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))‖ ≤ κ * c * (C1 * (‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖⁻¹) ^ ((1 : ℝ) - 1 / 2)) := by gcongr
            _ ≤ κ * c * (C1 * ((c * |τ|)⁻¹) ^ ((1 : ℝ) - 1 / 2)) := by
                have := hinvle η hη hη1 ((1 : ℝ) - 1 / 2) (by norm_num)
                gcongr)
        refine hb1.trans ?_
        have e2 : κ * c * (C1 * ((c * |τ|)⁻¹) ^ ((1 : ℝ) - 1 / 2)) = Cn1 * |τ| ^ ((1 / 2 : ℝ) - 1) := by
          rw [hmulinv, hCn1]
          have : -((1 : ℝ) - 1 / 2) = (1 / 2 : ℝ) - 1 := by ring
          rw [this, show (-(1 / 2 : ℝ)) = (1 / 2 : ℝ) - 1 by ring]
          have h5 : c ^ ((1 / 2 : ℝ) - 1) = c ^ (-(1 / 2 : ℝ)) := by congr 1; ring
          rw [h5]; ring
        rw [e2]
        have := hpow0 ((1 / 2 : ℝ) - 1)
        gcongr
        linarith [hCn0n, hCn0'n, hCn2n, mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
      · rw [hder2 τ hτ0]
        have hb1 := hlimit (edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c) hC2 τ hτ0 (κ * c ^ 2 * (C2 * ((c * |τ|)⁻¹) ^ ((2 : ℝ) - 1 / 2))) (by
          intro η hη hη1
          rw [(h.edgeE_eq_laplace hb0 hbδ hβ1 hη (κ : ℂ) c τ).2, norm_mul, norm_mul, hκn, norm_pow, norm_mul, hcn, Complex.norm_I, mul_one]
          have hL := hL2 _ (by rw [hqre η hη]; exact hη) (hq η hη hη1).2
          simp only [Nat.cast_ofNat] at hL
          calc κ * c ^ 2 * ‖bumpLapW B 2 (((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ))‖ ≤ κ * c ^ 2 * (C2 * (‖((c * τ : ℝ) : ℂ) * Complex.I + (η : ℂ)‖⁻¹) ^ ((2 : ℝ) - 1 / 2)) := by gcongr
            _ ≤ κ * c ^ 2 * (C2 * ((c * |τ|)⁻¹) ^ ((2 : ℝ) - 1 / 2)) := by
                have := hinvle η hη hη1 ((2 : ℝ) - 1 / 2) (by norm_num)
                gcongr)
        refine hb1.trans ?_
        have e2 : κ * c ^ 2 * (C2 * ((c * |τ|)⁻¹) ^ ((2 : ℝ) - 1 / 2)) = Cn2 * |τ| ^ ((1 / 2 : ℝ) - 2) := by
          rw [hmulinv, hCn2]
          have : -((2 : ℝ) - 1 / 2) = (1 / 2 : ℝ) - 2 := by ring
          rw [this]
          have h5 : c ^ ((1 / 2 : ℝ) - 2) = c ^ (-(3 / 2 : ℝ)) := by congr 1; ring
          rw [h5]; ring
        rw [e2]
        have := hpow0 ((1 / 2 : ℝ) - 2)
        gcongr
        linarith [hCn0n, hCn0'n, hCn1n, mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
    · -- bounded region
      have ht2 : (c * |τ|)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
      have ht0 : 0 < (c * |τ|)⁻¹ := by positivity
      have hΘ : ((c * |τ|)⁻¹) ^ 4 + ((c * |τ|)⁻¹) ^ 5 + ((c * |τ|)⁻¹) ^ 6 ≤ 112 := by
        have h4 : ((c * |τ|)⁻¹) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ ht0.le ht2 4
        have h5 : ((c * |τ|)⁻¹) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ ht0.le ht2 5
        have h6 : ((c * |τ|)⁻¹) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ ht0.le ht2 6
        linarith [h4, h5, h6, (by norm_num : (2 : ℝ) ^ 4 + 2 ^ 5 + 2 ^ 6 = 112)]
      have hbd := hAb (p τ) (by rw [hpre]) (hpne τ hτ0)
      rw [hpn] at hbd
      obtain ⟨b0, b1, b2⟩ := hbd
      have hb : ∀ x : ℝ, x ≤ A * (((c * |τ|)⁻¹) ^ 4 + ((c * |τ|)⁻¹) ^ 5 + ((c * |τ|)⁻¹) ^ 6) → x ≤ 112 * A := fun x hx =>
        hx.trans (by nlinarith [hΘ, hA0])
      have b0' : ‖stripEdge0 W τ‖ ≤ 112 * A := by rw [hg τ hτ0]; exact hb _ b0
      have b1' : ‖deriv (stripEdge0 W) τ‖ ≤ 112 * A := by rw [hder1 τ hτ0]; exact hb _ b1
      have b2' : ‖deriv (deriv (stripEdge0 W)) τ‖ ≤ 112 * A := by rw [hder2 τ hτ0]; exact hb _ b2
      refine ⟨?_, ?_, ?_⟩
      · have h1 : ‖stripEdge0 W τ - stripEdge0 W 0‖ ≤ 112 * A + κ * nB :=
          (norm_sub_le _ _).trans (add_le_add b0' hg0)
        have h2 : 1 ≤ (2 * c) ^ (1 / 2 : ℝ) * |τ| ^ (1 / 2 : ℝ) := by
          rw [← Real.mul_rpow (by positivity) hu0.le]
          exact Real.one_le_rpow (by nlinarith) (by norm_num)
        have h3 : 112 * A + κ * nB ≤ Cn0' * |τ| ^ (1 / 2 : ℝ) := by
          rw [hCn0', mul_assoc]
          nlinarith [mul_nonneg (by positivity : 0 ≤ 112 * A + κ * nB) (sub_nonneg.mpr h2)]
        have h4 : Cn0' * |τ| ^ (1 / 2 : ℝ) ≤ (Cn0 + Cn0' + Cn1 + Cn2 + 112 * A) * |τ| ^ (1 / 2 : ℝ) := by
          have := hpow0 (1 / 2); gcongr; linarith [hCn0n, hCn1n, hCn2n, mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
        linarith
      · have h1 := b1'
        have h2 := hnegpow ((1 / 2 : ℝ) - 1) (by norm_num)
        calc ‖deriv (stripEdge0 W) τ‖ ≤ 112 * A := h1
          _ ≤ (112 * A) * |τ| ^ ((1 / 2 : ℝ) - 1) := by nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
          _ ≤ (Cn0 + Cn0' + Cn1 + Cn2 + 112 * A) * |τ| ^ ((1 / 2 : ℝ) - 1) := by
              have := hpow0 ((1 / 2 : ℝ) - 1); gcongr; linarith [hCn0n, hCn0'n, hCn1n, hCn2n]
      · have h1 := b2'
        have h2 := hnegpow ((1 / 2 : ℝ) - 2) (by norm_num)
        calc ‖deriv (deriv (stripEdge0 W)) τ‖ ≤ 112 * A := h1
          _ ≤ (112 * A) * |τ| ^ ((1 / 2 : ℝ) - 2) := by nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 112) hA0]
          _ ≤ (Cn0 + Cn0' + Cn1 + Cn2 + 112 * A) * |τ| ^ ((1 / 2 : ℝ) - 2) := by
              have := hpow0 ((1 / 2 : ℝ) - 2); gcongr; linarith [hCn0n, hCn0'n, hCn1n, hCn2n]
  · -- far region
    set Kf : ℝ := 36 * (c⁻¹) ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) with hKf
    have hKf0 : 0 ≤ Kf := by rw [hKf]; positivity
    refine ⟨A * Kf, fun τ hτ => ?_⟩
    have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ; linarith
    have hu : (1 : ℝ) / 2 ≤ |τ| := hτ
    set u := |τ| with hudef
    have hu0 : 0 < u := by linarith
    set t : ℝ := (c * u)⁻¹ with htdef
    have ht0 : 0 < t := by positivity
    have hT : t ≤ 2 * c⁻¹ := by
      rw [htdef, mul_inv]
      have : u⁻¹ ≤ 2 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
      calc c⁻¹ * u⁻¹ ≤ c⁻¹ * 2 := by gcongr
        _ = 2 * c⁻¹ := by ring
    have hΘ : t ^ 4 + t ^ 5 + t ^ 6 ≤ t ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) := by
      have h5 : t ^ 5 ≤ t ^ 4 * (2 * c⁻¹) := by
        calc t ^ 5 = t ^ 4 * t := by ring
          _ ≤ t ^ 4 * (2 * c⁻¹) := by gcongr
      have h6 : t ^ 6 ≤ t ^ 4 * (2 * c⁻¹) ^ 2 := by
        calc t ^ 6 = t ^ 4 * t ^ 2 := by ring
          _ ≤ t ^ 4 * (2 * c⁻¹) ^ 2 := by gcongr
      nlinarith [h5, h6]
    have ht4 : t ^ 4 ≤ (c⁻¹) ^ 4 * (36 * (1 + u) ^ (-(2 : ℝ))) := by
      rw [htdef, mul_inv, mul_pow, Real.rpow_neg (by linarith), Real.rpow_two]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [inv_pow, show 36 * ((1 + u) ^ 2)⁻¹ = 36 / (1 + u) ^ 2 by rw [div_eq_mul_inv], ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (1 + u) ^ 2 ≤ 9 * u ^ 2 := by nlinarith
      have hu2 : (1 : ℝ) / 4 ≤ u ^ 2 := by nlinarith
      have h2 : 0 ≤ u ^ 2 * (u ^ 2 - 1 / 4) := mul_nonneg (sq_nonneg u) (by linarith)
      nlinarith [h1, h2]
    have hΘ2 : t ^ 4 + t ^ 5 + t ^ 6 ≤ Kf * (1 + u) ^ (-(2 : ℝ)) := by
      refine hΘ.trans ?_
      calc t ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) ≤ ((c⁻¹) ^ 4 * (36 * (1 + u) ^ (-(2 : ℝ)))) * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) := by gcongr
        _ = Kf * (1 + u) ^ (-(2 : ℝ)) := by rw [hKf]; ring
    have hbd := hAb (p τ) (by rw [hpre]) (hpne τ hτ0)
    have htn : (‖p τ‖)⁻¹ = t := by rw [hpn, htdef]
    rw [htn] at hbd
    have hq : 0 ≤ (1 + u) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    rw [hg τ hτ0, hder1 τ hτ0, hder2 τ hτ0]
    obtain ⟨b0, b1, b2⟩ := hbd
    have hbound : ∀ x : ℝ, x ≤ A * (t ^ 4 + t ^ 5 + t ^ 6) → x ≤ A * Kf * (1 + u) ^ (-(2 : ℝ)) := fun x hx =>
      hx.trans (by calc A * (t ^ 4 + t ^ 5 + t ^ 6) ≤ A * (Kf * (1 + u) ^ (-(2 : ℝ))) := by gcongr
                      _ = _ := by ring)
    exact ⟨hbound _ b0, hbound _ b1, hbound _ b2⟩

lemma theta_far {c u t : ℝ} (hc : 0 < c) (hu : 1 / 2 ≤ u) (ht0 : 0 < t) (htle : t ≤ (c * u)⁻¹) :
    t ^ 4 + t ^ 5 + t ^ 6 ≤ 36 * (c⁻¹) ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) * (1 + u) ^ (-(2 : ℝ)) := by
  have hu0 : 0 < u := by linarith
  set t0 : ℝ := (c * u)⁻¹ with htdef
  have ht00 : 0 < t0 := by positivity
  have hT : t0 ≤ 2 * c⁻¹ := by
    rw [htdef, mul_inv]
    have : u⁻¹ ≤ 2 := by rw [inv_le_comm₀ hu0 (by norm_num)]; linarith
    calc c⁻¹ * u⁻¹ ≤ c⁻¹ * 2 := by gcongr
      _ = 2 * c⁻¹ := by ring
  have hΘ : t0 ^ 4 + t0 ^ 5 + t0 ^ 6 ≤ t0 ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) := by
    have h5 : t0 ^ 5 ≤ t0 ^ 4 * (2 * c⁻¹) := by
      calc t0 ^ 5 = t0 ^ 4 * t0 := by ring
        _ ≤ t0 ^ 4 * (2 * c⁻¹) := by gcongr
    have h6 : t0 ^ 6 ≤ t0 ^ 4 * (2 * c⁻¹) ^ 2 := by
      calc t0 ^ 6 = t0 ^ 4 * t0 ^ 2 := by ring
        _ ≤ t0 ^ 4 * (2 * c⁻¹) ^ 2 := by gcongr
    nlinarith [h5, h6]
  have ht4 : t0 ^ 4 ≤ (c⁻¹) ^ 4 * (36 * (1 + u) ^ (-(2 : ℝ))) := by
    rw [htdef, mul_inv, mul_pow, Real.rpow_neg (by linarith), Real.rpow_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [inv_pow, show 36 * ((1 + u) ^ 2)⁻¹ = 36 / (1 + u) ^ 2 by rw [div_eq_mul_inv], ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 + u) ^ 2 ≤ 9 * u ^ 2 := by nlinarith
    have hu2 : (1 : ℝ) / 4 ≤ u ^ 2 := by nlinarith
    have h2 : 0 ≤ u ^ 2 * (u ^ 2 - 1 / 4) := mul_nonneg (sq_nonneg u) (by linarith)
    nlinarith [h1, h2]
  have hmono : t ^ 4 + t ^ 5 + t ^ 6 ≤ t0 ^ 4 + t0 ^ 5 + t0 ^ 6 := by
    have := pow_le_pow_left₀ ht0.le htle 4
    have := pow_le_pow_left₀ ht0.le htle 5
    have := pow_le_pow_left₀ ht0.le htle 6
    linarith
  refine hmono.trans (hΘ.trans ?_)
  calc t0 ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) ≤ ((c⁻¹) ^ 4 * (36 * (1 + u) ^ (-(2 : ℝ)))) * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) := by gcongr
    _ = _ := by ring

/-- **(M2) at `ζ = 0`** (Hölder exponent `1/2`) for `ΔW_c`. -/
theorem bump_holder_zero {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ}
    (hbδ : b * δ ≤ 1) (hδ0 : 0 < δ) (hM : 0 ≤ M) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖ζ‖ ≤ 1 / 2 →
      ‖(fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) ζ -
        (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) 0‖ ≤ CH * ‖ζ‖ ^ (1 / 2 : ℝ) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  have hκ0 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  obtain ⟨CH, hCH0, hCH⟩ := h.holder_zero hb0 hbδ hβ hM
  have hz0 : ∀ x : ℝ, x < 0 → B x = 0 := fun x hx => h.support x (by linarith)
  set nB : ℝ := ∫ x : ℝ, ‖B x‖ with hnB
  have hnB0 : 0 ≤ nB := integral_nonneg fun x => norm_nonneg _
  have hFn : ∀ s : ℂ, 0 ≤ s.re → ‖bumpLaplace B s‖ ≤ nB := fun s hs => by
    have := norm_bumpLapW_le hz0 hs 0 (by simpa using h.integrable_self hbδ hβ1)
    rw [BumpProfile.bumpLapW_zero_B] at this
    simpa [hnB] using this
  set κ : ℝ := c ^ (-(1 / 3 : ℝ)) with hκ
  refine ⟨κ * CH * c ^ (1 / 2 : ℝ) + 2 * κ * nB * c ^ (1 / 2 : ℝ), fun ζ hζ0 hζ1 hζ => ?_⟩
  have hκn : ‖(κ : ℂ)‖ = κ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ0]
  have hcn : ‖(c : ℂ) * ζ‖ = c * ‖ζ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have hre : 0 ≤ ((c : ℂ) * ζ).re := by simp only [Complex.re_ofReal_mul]; positivity
  show ‖(κ : ℂ) * bumpLaplace B ((c : ℂ) * ζ) - (κ : ℂ) * bumpLaplace B ((c : ℂ) * 0)‖ ≤ _
  rw [mul_zero, ← mul_sub, norm_mul, hκn]
  have hc12 : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc.le _
  have hζp : 0 ≤ ‖ζ‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  rcases le_or_gt (c * ‖ζ‖) 1 with h1 | h1
  · have := hCH ((c : ℂ) * ζ) hre (by rw [hcn]; exact h1)
    rw [hcn, Real.mul_rpow hc.le (norm_nonneg _)] at this
    calc κ * ‖bumpLaplace B ((c : ℂ) * ζ) - bumpLaplace B 0‖ ≤ κ * (CH * (c ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ))) := by gcongr
      _ = κ * CH * c ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ (κ * CH * c ^ (1 / 2 : ℝ) + 2 * κ * nB * c ^ (1 / 2 : ℝ)) * ‖ζ‖ ^ (1 / 2 : ℝ) := by
          have : 0 ≤ 2 * κ * nB * c ^ (1 / 2 : ℝ) := by positivity
          nlinarith [mul_nonneg this hζp]
  · have h2 : 1 ≤ c ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow hc.le (norm_nonneg _)]
      exact Real.one_le_rpow h1.le (by norm_num)
    have h3 : ‖bumpLaplace B ((c : ℂ) * ζ) - bumpLaplace B 0‖ ≤ 2 * nB :=
      (norm_sub_le _ _).trans (by linarith [hFn _ hre, hFn 0 (by simp)])
    calc κ * ‖bumpLaplace B ((c : ℂ) * ζ) - bumpLaplace B 0‖ ≤ κ * (2 * nB) := by gcongr
      _ ≤ κ * (2 * nB) * (c ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ)) := by
          have : 0 ≤ κ * (2 * nB) := by positivity
          nlinarith [mul_nonneg this (sub_nonneg.mpr h2)]
      _ = 2 * κ * nB * c ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ) := by ring
      _ ≤ (κ * CH * c ^ (1 / 2 : ℝ) + 2 * κ * nB * c ^ (1 / 2 : ℝ)) * ‖ζ‖ ^ (1 / 2 : ℝ) := by
          have : 0 ≤ κ * CH * c ^ (1 / 2 : ℝ) := by positivity
          nlinarith [mul_nonneg this hζp]

set_option maxHeartbeats 1600000 in
/-- **(M3) at `ζ = 1`** (`StripEdge1`, exponent `1/2`) for `ΔW_c`: the right-edge trace `τ ↦ c^{-1/3} B̂(c - icτ)` (here `Re s = c > 0`, so everything converges absolutely). -/
theorem bump_stripEdge1 {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ)
    (hbδ : b * δ ≤ 1) (_hM : 0 ≤ M) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    StripEdge1 (1 / 2) (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  set κ : ℝ := c ^ (-(1 / 3 : ℝ)) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hc _
  obtain ⟨hf, hz, hI⟩ := h.f4_data hbδ hb0 hβ1
  obtain ⟨hC0, hC1, hC2⟩ := continuousOn_edgeE hf hz hI (κ : ℂ) c
  obtain ⟨A, hA0, hAb⟩ := edgeE_norm_le hz hI κ c hκ0.le hc.le
  unfold StripEdge1
  set q : ℝ → ℂ := fun τ => ((c * (-τ) : ℝ) : ℂ) * Complex.I + ((c : ℝ) : ℂ) with hq
  have hqre : ∀ τ : ℝ, (q τ).re = c := fun τ => by simp [hq]
  have hqne : ∀ τ : ℝ, q τ ≠ 0 := fun τ h0 => by
    have := congrArg Complex.re h0; rw [hqre] at this; simp at this; linarith
  have hqn : ∀ τ : ℝ, c * |τ| ≤ ‖q τ‖ ∧ c ≤ ‖q τ‖ := fun τ => by
    rw [hq]; dsimp only; rw [pnorm]
    refine ⟨?_, ?_⟩
    · calc c * |τ| = Real.sqrt ((c * (-τ)) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_mul, abs_neg, abs_of_pos hc]
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
    · calc c = Real.sqrt (c ^ 2) := by rw [Real.sqrt_sq hc.le]
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (c * (-τ))])
  have hmaps : ∀ τ : ℝ, q τ ∈ {s : ℂ | 0 ≤ s.re ∧ s ≠ 0} := fun τ => ⟨by rw [hqre]; exact hc.le, hqne τ⟩
  set G : ℝ → ℂ := fun τ => edgeE0 (iteratedDeriv 4 B) (κ : ℂ) (q τ) with hG
  have hg : ∀ τ : ℝ, stripEdge0 (fun ζ : ℂ => (fun ζ : ℂ => (κ : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) (1 - ζ)) τ = G τ := by
    intro τ
    rw [hG]; dsimp only
    rw [h.edgeE0_eq hb0 hbδ hβ1 (κ : ℂ) (by rw [hqre]; exact hc.le) (hqne τ)]
    unfold stripEdge0
    have e : (c : ℂ) * (1 - ((τ : ℂ) * Complex.I)) = q τ := by rw [hq]; push_cast; ring
    show (κ : ℂ) * bumpLaplace B ((c : ℂ) * (1 - ((τ : ℂ) * Complex.I))) = (κ : ℂ) * bumpLaplace B (q τ)
    rw [e]
  have hD : ∀ τ : ℝ, HasDerivAt G (-edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ)) τ ∧
      HasDerivAt (fun τ : ℝ => -edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ)) (edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (q τ)) τ := by
    intro τ
    obtain ⟨d1, d2⟩ := hasDerivAt_edgeE hf hz hI hc.le (κ : ℂ) c (-τ) (hqne τ)
    have hn : HasDerivAt (fun τ : ℝ => -τ) (-1) τ := hasDerivAt_neg τ
    refine ⟨?_, ?_⟩
    · have := HasDerivAt.scomp (h := fun τ : ℝ => -τ) τ d1 hn
      refine this.congr_deriv ?_
      simp [hq]
    · have := (HasDerivAt.scomp (h := fun τ : ℝ => -τ) τ d2 hn).neg
      refine this.congr_deriv ?_
      simp [hq]
  have hder1 : ∀ τ : ℝ, deriv G τ = -edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ) := fun τ => (hD τ).1.deriv
  have hder2 : ∀ τ : ℝ, deriv (deriv G) τ = edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (q τ) := fun τ => by
    rw [show deriv G = fun τ => -edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ) from funext hder1]
    exact (hD τ).2.deriv
  have hgfun : stripEdge0 (fun ζ : ℂ => (fun ζ : ℂ => (κ : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) (1 - ζ)) = G := funext hg
  have hpc : Continuous q := by rw [hq]; fun_prop
  have hE1c : Continuous (fun τ : ℝ => edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ)) := by
    exact continuousOn_univ.mp (hC1.comp hpc.continuousOn fun τ _ => hmaps τ)
  have hE2c : Continuous (fun τ : ℝ => edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (q τ)) := by
    exact continuousOn_univ.mp (hC2.comp hpc.continuousOn fun τ _ => hmaps τ)
  have hopen : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  -- constants
  set Θ0 : ℝ := (c⁻¹) ^ 4 + (c⁻¹) ^ 5 + (c⁻¹) ^ 6 with hΘ0
  have hΘ0n : 0 ≤ Θ0 := by rw [hΘ0]; positivity
  have hbd : ∀ τ : ℝ, ‖G τ‖ ≤ A * (((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6) ∧
      ‖deriv G τ‖ ≤ A * (((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6) ∧
      ‖deriv (deriv G) τ‖ ≤ A * (((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6) := by
    intro τ
    obtain ⟨b0, b1, b2⟩ := hAb (q τ) (by rw [hqre]; exact hc.le) (hqne τ)
    refine ⟨b0, ?_, ?_⟩
    · rw [hder1, norm_neg]; exact b1
    · rw [hder2]; exact b2
  have hbdc : ∀ τ : ℝ, ‖G τ‖ ≤ A * Θ0 ∧ ‖deriv G τ‖ ≤ A * Θ0 ∧ ‖deriv (deriv G) τ‖ ≤ A * Θ0 := by
    intro τ
    obtain ⟨b0, b1, b2⟩ := hbd τ
    have hn : ‖q τ‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hqn τ).2
    have ht0 : 0 ≤ (‖q τ‖)⁻¹ := by positivity
    have hΘ : ((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6 ≤ Θ0 := by
      have := pow_le_pow_left₀ ht0 hn 4
      have := pow_le_pow_left₀ ht0 hn 5
      have := pow_le_pow_left₀ ht0 hn 6
      rw [hΘ0]; linarith
    exact ⟨b0.trans (by gcongr), b1.trans (by gcongr), b2.trans (by gcongr)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hgfun]
    have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h2, contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨fun τ _ => (hD τ).1.differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [h1, contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨?_, fun h => absurd h (by simp), ?_⟩
    · intro τ _
      have : deriv G = fun τ => -edgeE1 (iteratedDeriv 4 B) (κ : ℂ) c (q τ) := funext hder1
      rw [this]
      exact (hD τ).2.differentiableAt.differentiableWithinAt
    · rw [contDiffOn_zero]
      have : deriv (deriv G) = fun τ => edgeE2 (iteratedDeriv 4 B) (κ : ℂ) c (q τ) := funext hder2
      rw [this]
      exact hE2c.continuousOn
  · refine ⟨A * Θ0, fun τ hτ0 hτ1 => ?_⟩
    rw [hgfun]
    have hu0 : 0 < |τ| := abs_pos.mpr hτ0
    obtain ⟨b0, b1, b2⟩ := hbdc τ
    have hmv : ‖G τ - G 0‖ ≤ A * Θ0 * ‖τ - 0‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun x _ => (hD x).1.differentiableAt) (fun x _ => (hbdc x).2.1)
        convex_univ (mem_univ 0) (mem_univ τ) |> fun h => ?_
      simpa [norm_sub_rev] using h
    rw [sub_zero, Real.norm_eq_abs] at hmv
    have hp1 : |τ| ≤ |τ| ^ (1 / 2 : ℝ) := by
      calc |τ| = |τ| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |τ| ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hu0 hτ1 (by norm_num)
    have hn1 : 1 ≤ |τ| ^ ((1 / 2 : ℝ) - 1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hτ1 (by norm_num)
    have hn2 : 1 ≤ |τ| ^ ((1 / 2 : ℝ) - 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hτ1 (by norm_num)
    have hAΘ : 0 ≤ A * Θ0 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · calc ‖G τ - G 0‖ ≤ A * Θ0 * |τ| := hmv
        _ ≤ A * Θ0 * |τ| ^ (1 / 2 : ℝ) := by gcongr
    · calc ‖deriv G τ‖ ≤ A * Θ0 := b1
        _ ≤ A * Θ0 * |τ| ^ ((1 / 2 : ℝ) - 1) := by nlinarith [mul_nonneg hAΘ (sub_nonneg.mpr hn1)]
    · calc ‖deriv (deriv G) τ‖ ≤ A * Θ0 := b2
        _ ≤ A * Θ0 * |τ| ^ ((1 / 2 : ℝ) - 2) := by nlinarith [mul_nonneg hAΘ (sub_nonneg.mpr hn2)]
  · set Kf : ℝ := 36 * (c⁻¹) ^ 4 * (1 + 2 * c⁻¹ + (2 * c⁻¹) ^ 2) with hKf
    have hKf0 : 0 ≤ Kf := by rw [hKf]; positivity
    refine ⟨A * Kf, fun τ hτ => ?_⟩
    rw [hgfun]
    have hu : (1 : ℝ) / 2 ≤ |τ| := hτ
    obtain ⟨b0, b1, b2⟩ := hbd τ
    have hnq : 0 < ‖q τ‖ := lt_of_lt_of_le (by positivity) (hqn τ).2
    have hΘ := theta_far (c := c) (u := |τ|) (t := (‖q τ‖)⁻¹) hc hu (inv_pos.mpr hnq)
      (inv_anti₀ (by positivity) (hqn τ).1)
    have hq0 : 0 ≤ (1 + |τ|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hbound : ∀ x : ℝ, x ≤ A * (((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6) → x ≤ A * Kf * (1 + |τ|) ^ (-(2 : ℝ)) := fun x hx =>
      hx.trans (by calc A * (((‖q τ‖)⁻¹) ^ 4 + ((‖q τ‖)⁻¹) ^ 5 + ((‖q τ‖)⁻¹) ^ 6) ≤ A * (Kf * (1 + |τ|) ^ (-(2 : ℝ))) := by gcongr
                      _ = _ := by ring)
    exact ⟨hbound _ b0, hbound _ b1, hbound _ b2⟩

/-- **`uct:bump-symbol`, admissibility of `ΔW_c`**: all hypotheses (M1), (M2) at `ζ = 0, 1`, (M3) at both edges of `uct:admiss` (with Hölder exponent `1/2`), i.e.
`StripAdmissFullData (1/2)`, for `ΔW_c(ζ) = c^{-1/3} B̂(cζ)` and a bump profile `B` (`BumpProfile`). -/
theorem bump_stripAdmissFull {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbδ : b * δ ≤ 1) (hM : 0 ≤ M) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    StripAdmissFullData (1 / 2) (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) where
  toStripM1 := bump_stripM1 hb hβ K hδ0 hδ1 hbδ hM hc h
  holder1 := bump_holder_one hb hβ K hδ0 hbδ hc h
  edge0 := bump_stripEdge0 hb hβ K hδ0 hbδ hM hc h
  holder0 := bump_holder_zero hb hβ K hbδ hδ0 hM hc h
  edge1 := bump_stripEdge1 hb hβ K hδ0 hbδ hM hc h

/-- info: 'FormalResearch.SignUncertainty.bump_stripEdge0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_stripEdge0

/-- info: 'FormalResearch.SignUncertainty.bump_stripEdge1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_stripEdge1

/-- info: 'FormalResearch.SignUncertainty.bump_holder_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_holder_zero

/-- info: 'FormalResearch.SignUncertainty.bump_stripAdmissFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_stripAdmissFull

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.holder_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.holder_zero

/-- info: 'FormalResearch.SignUncertainty.BumpProfile.bumpLapW_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BumpProfile.bumpLapW_bound

end FormalResearch.SignUncertainty

module

public import FormalResearch.CohnElkies.SeedSqrtForm
public import FormalResearch.CohnElkies.MainOuterBound

/-!
# The outer amplitude of `I_main` (`O.3(2)`, the `(1 - χ_ξ)`-part): the `(e27)` bounds for `h`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1co:O3`(2), the `(1-χ_ξ)`-part, item *Amplitude bounds*:
`b(τ) = (1-χ_ξ)(κτ)^{-m} (1-iτ)^{-1/2} e^{B_c(iτ)} F̃(-c_s τ/ε)` satisfies `|∂_τ^r b| ≲ K^{-m} ε^{5/2} |τ|^{-m-5/2-r}` for `r ≤ 1`, by `(e27)`
since `|c_s τ/ε| ≥ c_s`.

* `SymbolTail G C`: the large-`|v|` data of a symbol `G(v) = X̃(c_s i v)`: `G` is `C²` off the origin and
  `|G| ≲ |v|^{-5/2}`, `|G'| ≲ |v|^{-7/2}`, `|G''| ≲ |v|^{-9/2}` for `|v| > 1`; `symbolTail_of_sqData` proves it from `ImagAxisBounds` and the
  square-root form, so it holds for every one-level seed and the `m₀ = 1` HB seed.
* `outer_amplitude`: for a cut-off `χ_o` vanishing on `|τ| < τ₁` (`τ₁ > ε`) with `|χ_o^{(r)}| ≤ K_χ |τ|^{-r}`, the amplitude
  `h = (iκτ)^{-m} χ_o(τ) G(τ/ε)` is `C²`, vanishes on `|τ| < τ₁`, satisfies the relation `χ_o X̃ = (iκτ)^m h` of `iMain_outer_bound` and
  `‖h^{(r)}(τ)‖ ≤ Q |τ|^{-(m + 5/2 + r)}` for `|τ| ≥ τ₁`, `r ≤ 2`, with `Q = 4 (m+2)² κ^{-m} K_χ C ε^{5/2}`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### The large-`|v|` data of a symbol -/

/-- Large-`|v|` data of a symbol `G` (`(e27)` for `r ≤ 2` after `v = ω / c_s`): `G` is `C²` off the origin, and for `|v| > 1`
`|G| ≤ C |v|^{-5/2}`, `|G'| ≤ C |v|^{-7/2}`, `|G''| ≤ C |v|^{-9/2}`. -/
structure SymbolTail (G : ℝ → ℂ) (C : ℝ) : Prop where
  contDiff : ContDiffOn ℝ 2 G {v : ℝ | v ≠ 0}
  b0 : ∀ v : ℝ, 1 < |v| → ‖G v‖ ≤ C * |v| ^ (-(5 / 2 : ℝ))
  b1 : ∀ v : ℝ, 1 < |v| → ‖deriv G v‖ ≤ C * |v| ^ (-(7 / 2 : ℝ))
  b2 : ∀ v : ℝ, 1 < |v| → ‖deriv (deriv G) v‖ ≤ C * |v| ^ (-(9 / 2 : ℝ))

lemma symbolTail_of_sqData {T A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hT : ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y) (himag : ImagAxisBounds T) :
    ∃ C : ℝ, 0 < C ∧ SymbolTail (fun v : ℝ => T (yv v)) C := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := himag
  let c : ℝ := ceCs
  have hc1 : 1 < c := ceCs_one_lt
  have hc0 : 0 < c := by linarith
  have hω : ∀ v : ℝ, 1 < |v| → 1 < |c * v| := fun v hv => by
    rw [abs_mul, abs_of_pos hc0]; nlinarith [abs_nonneg v]
  have hyv : ∀ w : ℝ, yv w = ((c * w : ℝ) : ℂ) * Complex.I := fun w => by unfold yv; push_cast; ring
  have hopen : IsOpen {w : ℝ | 1 < |w|} := isOpen_lt continuous_const continuous_abs
  have hlin : ∀ v : ℝ, HasDerivAt (fun w : ℝ => c * w) c v := fun v => by simpa using (hasDerivAt_id v).const_mul c
  have hd1 : ∀ v : ℝ, 1 < |v| → HasDerivAt (fun w : ℝ => T (yv w)) ((c : ℂ) * g1 (c * v)) v := fun v hv => by
    have h := (h1 (c * v) (hω v hv)).scomp v (hlin v)
    have h' : HasDerivAt (fun w : ℝ => T (((c * w : ℝ) : ℂ) * Complex.I)) ((c : ℂ) * g1 (c * v)) v :=
      h.congr_deriv (by simp [Complex.real_smul])
    simpa only [hyv] using h'
  have hderiv1 : ∀ v : ℝ, 1 < |v| → deriv (fun w : ℝ => T (yv w)) v = (c : ℂ) * g1 (c * v) := fun v hv => (hd1 v hv).deriv
  have hd2 : ∀ v : ℝ, 1 < |v| → deriv (deriv (fun w : ℝ => T (yv w))) v = (c : ℂ) * ((c : ℂ) * g2 (c * v)) := fun v hv => by
    have hev2 : deriv (fun w : ℝ => T (yv w)) =ᶠ[𝓝 v] fun w => (c : ℂ) * g1 (c * w) := by
      filter_upwards [hopen.mem_nhds hv] with w hw using hderiv1 w hw
    rw [hev2.deriv_eq]
    have h := (h2 (c * v) (hω v hv)).scomp v (hlin v)
    have h' : HasDerivAt (fun w : ℝ => g1 (c * w)) ((c : ℂ) * g2 (c * v)) v :=
      h.congr_deriv (by simp [Complex.real_smul])
    exact (h'.const_mul (c : ℂ)).deriv
  refine ⟨C, hC, ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · -- smoothness off the origin, via `Gsm` with the trivial cut-off
    intro v hv
    have h0 := Gsm_contDiffAt hA hB 0 (χ₁ := fun _ => 0) contDiff_const hv
    have heq : Gsm A B 0 (fun _ => 0) = fun w : ℝ => T (yv w) := funext fun w => by
      unfold Gsm
      rw [hT _ (by rw [yv_re])]; simp [sq]
    rw [heq] at h0
    exact h0.contDiffWithinAt
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    have := (hb (c * v) (hω v hv)).1
    rw [← hyv v] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    rw [habs]; exact rpow_cmul_le (abs_nonneg v) (by norm_num)
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    rw [hderiv1 v hv]
    have := (hb (c * v) (hω v hv)).2.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    rw [habs, Real.mul_rpow hc0.le (abs_nonneg v)] at this
    have hcr : c * c ^ (-(7 / 2 : ℝ)) ≤ 1 := by
      have : c * c ^ (-(7 / 2 : ℝ)) = c ^ (-(5 / 2 : ℝ)) := by
        rw [show c * c ^ (-(7 / 2 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(7 / 2 : ℝ)) by rw [Real.rpow_one], ← Real.rpow_add hc0]; norm_num
      rw [this]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
    calc c * ‖g1 (c * v)‖ ≤ c * (C * (c ^ (-(7 / 2 : ℝ)) * |v| ^ (-(7 / 2 : ℝ)))) := mul_le_mul_of_nonneg_left this hc0.le
      _ = C * (c * c ^ (-(7 / 2 : ℝ))) * |v| ^ (-(7 / 2 : ℝ)) := by ring
      _ ≤ C * 1 * |v| ^ (-(7 / 2 : ℝ)) := by gcongr
      _ = _ := by ring
  · have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
    rw [hd2 v hv]
    have := (hb (c * v) (hω v hv)).2.2
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    rw [habs, Real.mul_rpow hc0.le (abs_nonneg v)] at this
    have hcr : c * (c * c ^ (-(9 / 2 : ℝ))) ≤ 1 := by
      have : c * (c * c ^ (-(9 / 2 : ℝ))) = c ^ (-(5 / 2 : ℝ)) := by
        rw [show c * (c * c ^ (-(9 / 2 : ℝ))) = c ^ (1 : ℝ) * (c ^ (1 : ℝ) * c ^ (-(9 / 2 : ℝ))) by rw [Real.rpow_one],
          ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      rw [this]; exact Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
    calc c * (c * ‖g2 (c * v)‖) ≤ c * (c * (C * (c ^ (-(9 / 2 : ℝ)) * |v| ^ (-(9 / 2 : ℝ))))) := by gcongr
      _ = C * (c * (c * c ^ (-(9 / 2 : ℝ)))) * |v| ^ (-(9 / 2 : ℝ)) := by ring
      _ ≤ C * 1 * |v| ^ (-(9 / 2 : ℝ)) := by gcongr
      _ = _ := by ring

/-! ### A global `C²` extension of the symbol, and its scaled bounds -/

lemma symbolTail_ext {G : ℝ → ℂ} {C : ℝ} (hG : SymbolTail G C) {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁)
    (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1) (hχs : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ Gt : ℝ → ℂ, ContDiff ℝ 2 Gt ∧ (∀ v : ℝ, 1 < |v| → ‖Gt v‖ ≤ C * |v| ^ (-(5 / 2 : ℝ))) ∧
      (∀ v : ℝ, 1 < |v| → ‖deriv Gt v‖ ≤ C * |v| ^ (-(7 / 2 : ℝ))) ∧
      (∀ v : ℝ, 1 < |v| → ‖deriv (deriv Gt) v‖ ≤ C * |v| ^ (-(9 / 2 : ℝ))) ∧
      (∀ v : ℝ, 1 < |v| → ∀ᶠ w in 𝓝 v, Gt w = G w) := by
  let Gt : ℝ → ℂ := fun v => ((1 - χ₁ v : ℝ) : ℂ) * G v
  have hopen : IsOpen {w : ℝ | 1 < |w|} := isOpen_lt continuous_const continuous_abs
  have hev : ∀ v : ℝ, 1 < |v| → ∀ᶠ w in 𝓝 v, Gt w = G w := fun v hv => by
    filter_upwards [hopen.mem_nhds hv] with w hw
    simp only [Gt, hχs w hw]; simp
  have hcd : ContDiff ℝ 2 Gt := by
    refine contDiff_iff_contDiffAt.mpr fun v => ?_
    by_cases hv : v = 0
    · subst hv
      have hopen0 : IsOpen {w : ℝ | |w| < 1 / 2} := isOpen_lt continuous_abs continuous_const
      have h0 : Gt =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
        filter_upwards [hopen0.mem_nhds (by simp : (0 : ℝ) ∈ {w : ℝ | |w| < 1 / 2})] with w hw
        simp only [Gt, hχ1 w (le_of_lt hw)]; simp
      exact (contDiffAt_const).congr_of_eventuallyEq h0
    · have h1 : ContDiffAt ℝ 2 (fun v => ((1 - χ₁ v : ℝ) : ℂ)) v :=
        (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hχ)).contDiffAt
      exact h1.mul ((hG.contDiff v hv).contDiffAt (isOpen_ne.mem_nhds hv))
  have hd1 : ∀ v : ℝ, 1 < |v| → deriv Gt v = deriv G v := fun v hv => Filter.EventuallyEq.deriv_eq (hev v hv)
  have hd2 : ∀ v : ℝ, 1 < |v| → deriv (deriv Gt) v = deriv (deriv G) v := fun v hv => by
    have : deriv Gt =ᶠ[𝓝 v] deriv G := by
      filter_upwards [hopen.mem_nhds hv] with w hw using hd1 w hw
    exact this.deriv_eq
  refine ⟨Gt, hcd, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, hev⟩
  · rw [Filter.EventuallyEq.eq_of_nhds (hev v hv)]; exact hG.b0 v hv
  · rw [hd1 v hv]; exact hG.b1 v hv
  · rw [hd2 v hv]; exact hG.b2 v hv

lemma rpow_div_neg {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (s : ℝ) : (t / ε) ^ (-s) = t ^ (-s) * ε ^ s := by
  rw [Real.div_rpow ht hε.le, Real.rpow_neg hε.le, div_inv_eq_mul]

lemma scaled_bounds {Gt : ℝ → ℂ} {C : ℝ} (hcd : ContDiff ℝ 2 Gt)
    (b0 : ∀ v : ℝ, 1 < |v| → ‖Gt v‖ ≤ C * |v| ^ (-(5 / 2 : ℝ)))
    (b1 : ∀ v : ℝ, 1 < |v| → ‖deriv Gt v‖ ≤ C * |v| ^ (-(7 / 2 : ℝ)))
    (b2 : ∀ v : ℝ, 1 < |v| → ‖deriv (deriv Gt) v‖ ≤ C * |v| ^ (-(9 / 2 : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (fun τ : ℝ => Gt (τ / ε)) ∧
    (∀ τ : ℝ, ε < |τ| → ‖Gt (τ / ε)‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) ∧
    (∀ τ : ℝ, ε < |τ| → ‖deriv (fun x => Gt (x / ε)) τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ))) ∧
    (∀ τ : ℝ, ε < |τ| → ‖deriv (deriv (fun x => Gt (x / ε))) τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(9 / 2 : ℝ))) := by
  have hε0 : ε ≠ 0 := hε.ne'
  have hdf : ContDiff ℝ 1 (deriv Gt) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hcd) |>.2.2
  have hd1 : deriv (fun v => Gt (v / ε)) = fun v => (1 / ε : ℝ) • deriv Gt (v / ε) := funext fun v => deriv_comp_div hcd hε0 v
  have hd2 : ∀ v, deriv (deriv (fun v => Gt (v / ε))) v = (1 / ε : ℝ) • ((1 / ε : ℝ) • deriv (deriv Gt) (v / ε)) := fun v => by
    rw [hd1]
    have h1 : HasDerivAt (fun x : ℝ => x / ε) (1 / ε) v := by simpa using (hasDerivAt_id v).div_const ε
    have := (((hdf.differentiable one_ne_zero (v / ε)).hasDerivAt).scomp v h1).const_smul (1 / ε : ℝ)
    exact this.deriv
  have hv1 : ∀ τ : ℝ, ε < |τ| → 1 < |τ / ε| := fun τ hτ => by
    rw [abs_div, abs_of_pos hε, lt_div_iff₀ hε]; linarith
  have hε5 : ∀ a b : ℝ, ε ^ (a : ℝ) * ε ^ (b : ℝ) = ε ^ (a + b) := fun a b => (Real.rpow_add hε a b).symm
  refine ⟨hcd.comp (contDiff_id.div_const ε), fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · refine (b0 _ (hv1 τ hτ)).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hε, ← neg_neg (5 / 2 : ℝ), rpow_div_neg (abs_nonneg τ) hε]; ring
  · rw [hd1]; dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine (mul_le_mul_of_nonneg_left (b1 _ (hv1 τ hτ)) (by positivity)).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hε, rpow_div_neg (abs_nonneg τ) hε]
    have : ε ^ (7 / 2 : ℝ) = ε * ε ^ (5 / 2 : ℝ) := by
      rw [show (7 / 2 : ℝ) = 1 + 5 / 2 by norm_num, Real.rpow_add hε, Real.rpow_one]
    rw [this]; field_simp
  · rw [hd2, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (b2 _ (hv1 τ hτ)) (by positivity)) (by positivity)).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hε, rpow_div_neg (abs_nonneg τ) hε]
    have : ε ^ (9 / 2 : ℝ) = ε * ε * ε ^ (5 / 2 : ℝ) := by
      rw [show (9 / 2 : ℝ) = 2 + 5 / 2 by norm_num, Real.rpow_add hε, Real.rpow_two]; ring
    rw [this]; field_simp

/-! ### The cut-off power weight `U(τ) = τ^{-m} χ_o(τ)` -/

lemma abs_zpow_neg_eq_rpow {t : ℝ} (_ht : t ≠ 0) (k : ℤ) : |t ^ k| = |t| ^ ((k : ℤ) : ℝ) := by
  rw [abs_zpow, Real.rpow_intCast]

lemma hasDerivAt_negPow (m : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ (-(m : ℤ))) (-(m : ℝ) * τ ^ (-(m : ℤ) - 1)) τ := by
  have := hasDerivAt_zpow (-(m : ℤ)) τ (Or.inl hτ)
  simpa using this

lemma hasDerivAt_negPow1 (m : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun x : ℝ => -(m : ℝ) * x ^ (-(m : ℤ) - 1)) ((m : ℝ) * ((m : ℝ) + 1) * τ ^ (-(m : ℤ) - 2)) τ := by
  have := (hasDerivAt_zpow (-(m : ℤ) - 1) τ (Or.inl hτ)).const_mul (-(m : ℝ))
  convert this using 1
  rw [show -(m : ℤ) - 1 - 1 = -(m : ℤ) - 2 by ring]
  push_cast; ring

lemma powCut_contDiff (m : ℕ) {τ₁ : ℝ} {χo : ℝ → ℝ} (hχ : ContDiff ℝ 2 χo) (hvan : ∀ τ : ℝ, |τ| < τ₁ → χo τ = 0)
    (hτ₁ : 0 < τ₁) : ContDiff ℝ 2 (fun τ : ℝ => τ ^ (-(m : ℤ)) * χo τ) := by
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  by_cases hτ : τ = 0
  · subst hτ
    have hopen : IsOpen {w : ℝ | |w| < τ₁} := isOpen_lt continuous_abs continuous_const
    have h0 : (fun τ : ℝ => τ ^ (-(m : ℤ)) * χo τ) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds (by simpa using hτ₁ : (0 : ℝ) ∈ {w : ℝ | |w| < τ₁})] with w hw
      simp [hvan w hw]
    exact contDiffAt_const.congr_of_eventuallyEq h0
  · have h1 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ (-(m : ℤ))) τ := by
      have h2 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ m) τ := (contDiff_id.pow m).contDiffAt
      have := h2.inv (pow_ne_zero m hτ)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
      simp [zpow_neg]
    exact h1.mul hχ.contDiffAt

lemma powCut_bounds (m : ℕ) {τ₁ Kχ : ℝ} {χo : ℝ → ℝ} (hχ : ContDiff ℝ 2 χo) (hτ₁ : 0 < τ₁)
    (k0 : ∀ τ : ℝ, τ₁ ≤ |τ| → |χo τ| ≤ Kχ) (k1 : ∀ τ : ℝ, τ₁ ≤ |τ| → |deriv χo τ| ≤ Kχ * |τ| ^ (-(1 : ℝ)))
    (k2 : ∀ τ : ℝ, τ₁ ≤ |τ| → |deriv (deriv χo) τ| ≤ Kχ * |τ| ^ (-(2 : ℝ))) {τ : ℝ} (hτ : τ₁ ≤ |τ|) :
    |τ ^ (-(m : ℤ)) * χo τ| ≤ Kχ * |τ| ^ (-(m : ℝ)) ∧
    |deriv (fun x : ℝ => x ^ (-(m : ℤ)) * χo x) τ| ≤ ((m : ℝ) + 1) * Kχ * |τ| ^ (-((m : ℝ) + 1)) ∧
    |deriv (deriv (fun x : ℝ => x ^ (-(m : ℤ)) * χo x)) τ| ≤ ((m : ℝ) + 2) ^ 2 * Kχ * |τ| ^ (-((m : ℝ) + 2)) := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ; linarith
  have ht : 0 < |τ| := abs_pos.mpr hτ0
  have hK : 0 ≤ Kχ := (abs_nonneg _).trans (k0 τ hτ)
  have hdχ : ContDiff ℝ 1 (deriv χo) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hχ) |>.2.2
  have hnz : ∀ x : ℝ, x ≠ 0 → deriv (fun x : ℝ => x ^ (-(m : ℤ)) * χo x) x =
      -(m : ℝ) * x ^ (-(m : ℤ) - 1) * χo x + x ^ (-(m : ℤ)) * deriv χo x := fun x hx =>
    ((hasDerivAt_negPow m hx).mul (hχ.differentiable (by norm_num) x).hasDerivAt).deriv
  have hev : deriv (fun x : ℝ => x ^ (-(m : ℤ)) * χo x) =ᶠ[𝓝 τ] fun x => -(m : ℝ) * x ^ (-(m : ℤ) - 1) * χo x +
      x ^ (-(m : ℤ)) * deriv χo x := by
    filter_upwards [isOpen_ne.mem_nhds hτ0] with x hx using hnz x hx
  have hU2 : deriv (deriv (fun x : ℝ => x ^ (-(m : ℤ)) * χo x)) τ =
      (m : ℝ) * ((m : ℝ) + 1) * τ ^ (-(m : ℤ) - 2) * χo τ + 2 * (-(m : ℝ) * τ ^ (-(m : ℤ) - 1) * deriv χo τ) +
        τ ^ (-(m : ℤ)) * deriv (deriv χo) τ := by
    rw [hev.deriv_eq]
    have := (((hasDerivAt_negPow1 m hτ0).mul (hχ.differentiable (by norm_num) τ).hasDerivAt).add
      ((hasDerivAt_negPow m hτ0).mul ((hdχ.differentiable one_ne_zero τ).hasDerivAt)))
    exact this.deriv.trans (by ring)
  have hp0 : |τ ^ (-(m : ℤ))| = |τ| ^ (-(m : ℝ)) := by
    rw [abs_zpow_neg_eq_rpow hτ0]; push_cast; rfl
  have hp1 : |τ ^ (-(m : ℤ) - 1)| = |τ| ^ (-((m : ℝ) + 1)) := by
    rw [abs_zpow_neg_eq_rpow hτ0]; push_cast; ring_nf
  have hp2 : |τ ^ (-(m : ℤ) - 2)| = |τ| ^ (-((m : ℝ) + 2)) := by
    rw [abs_zpow_neg_eq_rpow hτ0]; push_cast; ring_nf
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : |τ| ^ (-(m : ℝ)) * |τ| ^ (-(1 : ℝ)) = |τ| ^ (-((m : ℝ) + 1)) := by
    rw [← Real.rpow_add ht]; ring_nf
  have e2 : |τ| ^ (-(m : ℝ)) * |τ| ^ (-(2 : ℝ)) = |τ| ^ (-((m : ℝ) + 2)) := by
    rw [← Real.rpow_add ht]; ring_nf
  have e11 : |τ| ^ (-((m : ℝ) + 1)) * |τ| ^ (-(1 : ℝ)) = |τ| ^ (-((m : ℝ) + 2)) := by
    rw [← Real.rpow_add ht]; ring_nf
  have P0 : 0 ≤ |τ| ^ (-(m : ℝ)) := by positivity
  have P1 : 0 ≤ |τ| ^ (-((m : ℝ) + 1)) := by positivity
  have P2 : 0 ≤ |τ| ^ (-((m : ℝ) + 2)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, hp0]; exact mul_le_mul_of_nonneg_left (k0 τ hτ) P0 |>.trans_eq (by ring)
  · rw [hnz τ hτ0]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_neg, Nat.abs_cast]
    rw [hp1, hp0]
    have a1 := k0 τ hτ
    have a2 := k1 τ hτ
    calc (m : ℝ) * |τ| ^ (-((m : ℝ) + 1)) * |χo τ| + |τ| ^ (-(m : ℝ)) * |deriv χo τ|
        ≤ (m : ℝ) * |τ| ^ (-((m : ℝ) + 1)) * Kχ + |τ| ^ (-(m : ℝ)) * (Kχ * |τ| ^ (-(1 : ℝ))) := by gcongr
      _ = ((m : ℝ) + 1) * Kχ * |τ| ^ (-((m : ℝ) + 1)) := by rw [← e1]; ring
  · rw [hU2]
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    simp only [abs_mul, abs_neg, Nat.abs_cast, abs_two]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1), hp2, hp1, hp0]
    have a1 := k0 τ hτ
    have a2 := k1 τ hτ
    have a3 := k2 τ hτ
    calc (m : ℝ) * ((m : ℝ) + 1) * |τ| ^ (-((m : ℝ) + 2)) * |χo τ| + 2 * ((m : ℝ) * |τ| ^ (-((m : ℝ) + 1)) * |deriv χo τ|) +
          |τ| ^ (-(m : ℝ)) * |deriv (deriv χo) τ|
        ≤ (m : ℝ) * ((m : ℝ) + 1) * |τ| ^ (-((m : ℝ) + 2)) * Kχ + 2 * ((m : ℝ) * |τ| ^ (-((m : ℝ) + 1)) * (Kχ * |τ| ^ (-(1 : ℝ)))) +
          |τ| ^ (-(m : ℝ)) * (Kχ * |τ| ^ (-(2 : ℝ))) := by gcongr
      _ = ((m : ℝ) * ((m : ℝ) + 1) + 2 * m + 1) * Kχ * |τ| ^ (-((m : ℝ) + 2)) := by
          linear_combination (2 * (m : ℝ) * Kχ) * e11 + Kχ * e2
      _ ≤ ((m : ℝ) + 2) ^ 2 * Kχ * |τ| ^ (-((m : ℝ) + 2)) := by
          have : (m : ℝ) * ((m : ℝ) + 1) + 2 * m + 1 ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith
          have h3 : 0 ≤ Kχ * |τ| ^ (-((m : ℝ) + 2)) := by positivity
          nlinarith

/-! ### The outer amplitude -/

lemma deriv_ofReal_fun {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (fun y : ℝ => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) :=
  (((hf.differentiable (by norm_num) x).hasDerivAt).ofReal_comp).deriv

lemma deriv2_ofReal_fun {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (fun y : ℝ => (f y : ℂ))) x = ((deriv (deriv f) x : ℝ) : ℂ) := by
  have hdf : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf) |>.2.2
  have : deriv (fun y : ℝ => (f y : ℂ)) = fun y => ((deriv f y : ℝ) : ℂ) := funext fun y => deriv_ofReal_fun hf y
  rw [this]
  exact (((hdf.differentiable one_ne_zero x).hasDerivAt).ofReal_comp).deriv

/-- **The outer amplitude of `I_main`.** `G` a symbol with `SymbolTail G C`, `m ≥ 1`, `κ, ε > 0`, `τ₁ > ε`, and a cut-off `χ_o` that is `C²`,
vanishes on `|τ| < τ₁` and has `|χ_o| ≤ K_χ`, `|χ_o'| ≤ K_χ |τ|⁻¹`, `|χ_o''| ≤ K_χ |τ|⁻²` on `|τ| ≥ τ₁`.  Then
`h(τ) = (iκτ)^{-m} χ_o(τ) G(τ/ε)` is `C²`, vanishes on `|τ| < τ₁`, satisfies `χ_o(τ) G(τ/ε) = (iκτ)^m h(τ)`, and for `|τ| ≥ τ₁`, `r ≤ 2`:
`‖h^{(r)}(τ)‖ ≤ 4 (m+2)² K_χ C ε^{5/2} κ^{-m} |τ|^{-(m + 5/2 + r)}`. -/
theorem outer_amplitude {G : ℝ → ℂ} {C : ℝ} (hG : SymbolTail G C) (hC : 0 ≤ C) {m : ℕ} {κ ε τ₁ Kχ : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hτ₁ : ε < τ₁) {χo : ℝ → ℝ} (hχ : ContDiff ℝ 2 χo)
    (hvan : ∀ τ : ℝ, |τ| < τ₁ → χo τ = 0) (k0 : ∀ τ : ℝ, τ₁ ≤ |τ| → |χo τ| ≤ Kχ)
    (k1 : ∀ τ : ℝ, τ₁ ≤ |τ| → |deriv χo τ| ≤ Kχ * |τ| ^ (-(1 : ℝ)))
    (k2 : ∀ τ : ℝ, τ₁ ≤ |τ| → |deriv (deriv χo) τ| ≤ Kχ * |τ| ^ (-(2 : ℝ))) :
    ∃ h : ℝ → ℂ, ContDiff ℝ 2 h ∧ (∀ τ : ℝ, |τ| < τ₁ → h τ = 0) ∧
      (∀ τ : ℝ, (χo τ : ℂ) * G (τ / ε) = (Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ) ∧
      ∀ r ≤ 2, ∀ τ : ℝ, τ₁ ≤ |τ| → ‖iteratedDeriv r h τ‖ ≤
        4 * ((m : ℝ) + 2) ^ 2 * Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ * |τ| ^ (-((m : ℝ) + 5 / 2 + r)) := by
  have hτ₁0 : 0 < τ₁ := hε.trans hτ₁
  obtain ⟨χ₁, hχ₁, hχ1, hχs⟩ := exists_cutoff_chi1
  obtain ⟨Gt, hGt, b0, b1, b2, hev⟩ := symbolTail_ext hG (hχ₁ 2) hχ1 hχs
  obtain ⟨hΦ, c0b, c1b, c2b⟩ := scaled_bounds hGt b0 b1 b2 hε
  let U : ℝ → ℝ := fun τ => τ ^ (-(m : ℤ)) * χo τ
  have hU : ContDiff ℝ 2 U := powCut_contDiff m hχ hvan hτ₁0
  let Φ : ℝ → ℂ := fun τ => Gt (τ / ε)
  let c₀ : ℂ := ((Complex.I * (κ : ℂ)) ^ m)⁻¹
  let Uc : ℝ → ℂ := fun τ => (U τ : ℂ)
  have hUc : ContDiff ℝ 2 Uc := Complex.ofRealCLM.contDiff.comp hU
  let h : ℝ → ℂ := fun τ => c₀ * (Uc τ * Φ τ)
  have hnc : ‖c₀‖ = (κ ^ m)⁻¹ := by
    simp [c₀, norm_inv, norm_pow, abs_of_pos hκ]
  have hKχ : 0 ≤ Kχ := (abs_nonneg _).trans (k0 (τ₁) (by rw [abs_of_pos hτ₁0]))
  refine ⟨h, (contDiff_const.mul (hUc.mul hΦ)), fun τ hτ => ?_, fun τ => ?_, ?_⟩
  · simp [h, Uc, U, hvan τ hτ]
  · by_cases hτ : |τ| < τ₁
    · simp [h, Uc, U, hvan τ hτ]
    · have hτ' : τ₁ ≤ |τ| := not_lt.mp hτ
      have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ'; simp at hτ'; linarith
      have hv1 : 1 < |τ / ε| := by rw [abs_div, abs_of_pos hε, lt_div_iff₀ hε]; linarith
      have hGeq : Gt (τ / ε) = G (τ / ε) := Filter.EventuallyEq.eq_of_nhds (hev _ hv1)
      simp only [h, Uc, U, Φ, hGeq]
      have hIκ : (Complex.I * (κ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hκ.ne'))
      have hκc : (κ : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hκ.ne')
      have hτc : ((τ : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hτ0)
      simp only [c₀, mul_pow, zpow_neg, zpow_natCast, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      field_simp
  · intro r hr τ hτ
    have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ; simp at hτ; linarith
    have ht : 0 < |τ| := abs_pos.mpr hτ0
    have hετ : ε < |τ| := hτ₁.trans_le hτ
    obtain ⟨u0, u1, u2⟩ := powCut_bounds m hχ hτ₁0 k0 k1 k2 hτ
    have φ0 := c0b τ hετ
    have φ1 := c1b τ hετ
    have φ2 := c2b τ hετ
    have hdU : deriv Uc τ = ((deriv U τ : ℝ) : ℂ) := deriv_ofReal_fun hU τ
    have hdU2 : deriv (deriv Uc) τ = ((deriv (deriv U) τ : ℝ) : ℂ) := deriv2_ofReal_fun hU τ
    have hmul1 := deriv_mul_of_contDiff hUc hΦ τ
    have hmul2 := deriv2_mul_of_contDiff hUc hΦ τ
    have hdh : deriv h = fun x => c₀ * deriv (fun x => Uc x * Φ x) x := deriv_const_mul_field' c₀
    have hdh2 : deriv (deriv h) τ = c₀ * deriv (deriv (fun x => Uc x * Φ x)) τ := by
      rw [hdh]; exact congrFun (deriv_const_mul_field' (v := deriv fun x => Uc x * Φ x) c₀) τ
    have hE : 0 ≤ ε ^ (5 / 2 : ℝ) := by positivity
    have hX : 0 ≤ Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ := by positivity
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have q : ∀ a b : ℝ, |τ| ^ (-a) * |τ| ^ (-b) = |τ| ^ (-(a + b)) := fun a b => by
      rw [← Real.rpow_add ht]; ring_nf
    have P : ∀ a : ℝ, 0 ≤ |τ| ^ (-a) := fun a => by positivity
    have hU0 : ‖Uc τ‖ ≤ Kχ * |τ| ^ (-(m : ℝ)) := by
      simp only [Uc, Complex.norm_real, Real.norm_eq_abs]; exact u0
    have hU1 : ‖deriv Uc τ‖ ≤ ((m : ℝ) + 1) * Kχ * |τ| ^ (-((m : ℝ) + 1)) := by
      rw [hdU, Complex.norm_real, Real.norm_eq_abs]; exact u1
    have hU2 : ‖deriv (deriv Uc) τ‖ ≤ ((m : ℝ) + 2) ^ 2 * Kχ * |τ| ^ (-((m : ℝ) + 2)) := by
      rw [hdU2, Complex.norm_real, Real.norm_eq_abs]; exact u2
    have hΦ0 : ‖Φ τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := φ0
    have hΦ1 : ‖deriv Φ τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ)) := φ1
    have hΦ2 : ‖deriv (deriv Φ) τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(9 / 2 : ℝ)) := φ2
    have n0 : ‖Uc τ * Φ τ‖ ≤ Kχ * C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-((m : ℝ) + 5 / 2)) := by
      rw [norm_mul, ← q]
      calc ‖Uc τ‖ * ‖Φ τ‖ ≤ (Kχ * |τ| ^ (-(m : ℝ))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    have n1 : ‖deriv Uc τ * Φ τ + Uc τ * deriv Φ τ‖ ≤ ((m : ℝ) + 2) * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 1)) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have e1 := q ((m : ℝ) + 1) (5 / 2)
      have e2 := q (m : ℝ) (7 / 2)
      have f1 : (m : ℝ) + 1 + 5 / 2 = (m : ℝ) + 5 / 2 + 1 := by ring
      have f2 : (m : ℝ) + 7 / 2 = (m : ℝ) + 5 / 2 + 1 := by ring
      rw [f1] at e1; rw [f2] at e2
      calc ‖deriv Uc τ‖ * ‖Φ τ‖ + ‖Uc τ‖ * ‖deriv Φ τ‖
          ≤ (((m : ℝ) + 1) * Kχ * |τ| ^ (-((m : ℝ) + 1))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) +
            (Kχ * |τ| ^ (-(m : ℝ))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ))) := by gcongr
        _ = ((m : ℝ) + 2) * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 1)) := by
            linear_combination (((m : ℝ) + 1) * Kχ * C * ε ^ (5 / 2 : ℝ)) * e1 + (Kχ * C * ε ^ (5 / 2 : ℝ)) * e2
    have n2 : ‖deriv (deriv Uc) τ * Φ τ + 2 * (deriv Uc τ * deriv Φ τ) + Uc τ * deriv (deriv Φ) τ‖ ≤
        4 * ((m : ℝ) + 2) ^ 2 * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 2)) := by
      refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      have e1 := q ((m : ℝ) + 2) (5 / 2)
      have e2 := q ((m : ℝ) + 1) (7 / 2)
      have e3 := q (m : ℝ) (9 / 2)
      have f1 : (m : ℝ) + 2 + 5 / 2 = (m : ℝ) + 5 / 2 + 2 := by ring
      have f2 : (m : ℝ) + 1 + 7 / 2 = (m : ℝ) + 5 / 2 + 2 := by ring
      have f3 : (m : ℝ) + 9 / 2 = (m : ℝ) + 5 / 2 + 2 := by ring
      rw [f1] at e1; rw [f2] at e2; rw [f3] at e3
      have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [hn2]
      calc ‖deriv (deriv Uc) τ‖ * ‖Φ τ‖ + 2 * (‖deriv Uc τ‖ * ‖deriv Φ τ‖) + ‖Uc τ‖ * ‖deriv (deriv Φ) τ‖
          ≤ (((m : ℝ) + 2) ^ 2 * Kχ * |τ| ^ (-((m : ℝ) + 2))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) +
            2 * ((((m : ℝ) + 1) * Kχ * |τ| ^ (-((m : ℝ) + 1))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(7 / 2 : ℝ)))) +
            (Kχ * |τ| ^ (-(m : ℝ))) * (C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(9 / 2 : ℝ))) := by gcongr
        _ = (((m : ℝ) + 2) ^ 2 + 2 * ((m : ℝ) + 1) + 1) * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 2)) := by
            linear_combination (((m : ℝ) + 2) ^ 2 * Kχ * C * ε ^ (5 / 2 : ℝ)) * e1 + (2 * ((m : ℝ) + 1) * Kχ * C * ε ^ (5 / 2 : ℝ)) * e2 +
              (Kχ * C * ε ^ (5 / 2 : ℝ)) * e3
        _ ≤ _ := by
            have hc : ((m : ℝ) + 2) ^ 2 + 2 * ((m : ℝ) + 1) + 1 ≤ 4 * ((m : ℝ) + 2) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    have hh1 : deriv h τ = c₀ * (deriv Uc τ * Φ τ + Uc τ * deriv Φ τ) := by
      rw [congrFun hdh τ, hmul1]
    have hh2 : deriv (deriv h) τ = c₀ * (deriv (deriv Uc) τ * Φ τ + 2 * (deriv Uc τ * deriv Φ τ) + Uc τ * deriv (deriv Φ) τ) := by
      rw [hdh2, hmul2]
    interval_cases r
    · rw [iteratedDeriv_zero]
      simp only [h]
      rw [norm_mul, hnc]
      have h1 : (1 : ℝ) ≤ 4 * ((m : ℝ) + 2) ^ 2 := by nlinarith
      calc (κ ^ m)⁻¹ * ‖Uc τ * Φ τ‖ ≤ (κ ^ m)⁻¹ * (Kχ * C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-((m : ℝ) + 5 / 2))) := by gcongr
        _ = 1 * (Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ * |τ| ^ (-((m : ℝ) + 5 / 2))) := by ring
        _ ≤ (4 * ((m : ℝ) + 2) ^ 2) * (Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ * |τ| ^ (-((m : ℝ) + 5 / 2))) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by push_cast; ring_nf
    · rw [iteratedDeriv_one, hh1, norm_mul, hnc]
      have h1 : ((m : ℝ) + 2) ≤ 4 * ((m : ℝ) + 2) ^ 2 := by nlinarith
      calc (κ ^ m)⁻¹ * ‖deriv Uc τ * Φ τ + Uc τ * deriv Φ τ‖
          ≤ (κ ^ m)⁻¹ * (((m : ℝ) + 2) * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 1))) := by gcongr
        _ = ((m : ℝ) + 2) * (Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ * |τ| ^ (-((m : ℝ) + 5 / 2 + 1))) := by ring
        _ ≤ (4 * ((m : ℝ) + 2) ^ 2) * (Kχ * C * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ * |τ| ^ (-((m : ℝ) + 5 / 2 + 1))) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = _ := by push_cast; ring_nf
    · have : iteratedDeriv 2 h τ = deriv (deriv h) τ := by rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [this, hh2, norm_mul, hnc]
      calc (κ ^ m)⁻¹ * ‖deriv (deriv Uc) τ * Φ τ + 2 * (deriv Uc τ * deriv Φ τ) + Uc τ * deriv (deriv Φ) τ‖
          ≤ (κ ^ m)⁻¹ * (4 * ((m : ℝ) + 2) ^ 2 * (Kχ * C * ε ^ (5 / 2 : ℝ)) * |τ| ^ (-((m : ℝ) + 5 / 2 + 2))) := by gcongr
        _ = _ := by push_cast; ring_nf

/-- info: 'FormalResearch.CohnElkies.symbolTail_of_sqData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.symbolTail_of_sqData
/-- info: 'FormalResearch.CohnElkies.outer_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.outer_amplitude

end FormalResearch.CohnElkies

module

public import FormalResearch.SignUncertainty.MiddleBandGeneralTail
public import FormalResearch.SignUncertainty.MiddleBandSmall
public import FormalResearch.CohnElkies.MainOuterBound
public import FormalResearch.CohnElkies.MellinPhaseBounds

/-!
# GT.2a: the main outer piece on the `τ`-line

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Outer pieces", first bullet.

The piece `∫ (1 - ϑ(τ/0.08)) k_c(τ) W(τ/ε) e^{icΦ(τ; L)} dτ` (`k_c = outerK c`, `W(v) = W_F(iv)`, `Φ = edgePhi L`) is bounded by
`C ε^{5/2} c^{-2}` for `0 < L ≤ 0.002`, by two integrations by parts on `|τ| ≥ 0.08`: there `-Φ' ≥ 6.4·10⁻⁵`, `|Φ''| ≤ 1/|τ|`, `|Φ'''| ≤ 7`
(`neg_edgePhiDeriv_ge_quad` with the saddle `τ₀(L) < 0.05`, `edgePhiDeriv2_abs_le`, `edgeR_deriv_bounds`), and `|∂^r (k_c W(·/ε))| ≲ ε^{5/2}|τ|^{-5/2}` (`r ≤ 2`).

* `edgePhi_phase_facts`: the phase facts above for `ψ = c Φ`;
* `main_outer_amp`: the amplitude `A = (1 - ϑ(·/0.08)) k_c W(·/ε)` is `C²` with `‖A^{(r)}(τ)‖ ≤ B |τ|^{-5/2}`, `B = C ε^{5/2}`, for `|τ| ≥ 0.08`;
* `main_outer_bound`: the bound `C ε^{5/2} c^{-2}`.

Status: proved, unconditional (pointwise symbol hypotheses on `W`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- `∂^j W` at points `v ≠ 0` for a symbol with a derivative chain. -/
lemma iterDeriv_chain {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) {v : ℝ} (hv : v ≠ 0) :
    iteratedDeriv 1 W v = W1 v ∧ iteratedDeriv 2 W v = W2 v := by
  have h1 : deriv W =ᶠ[nhds v] W1 := by
    filter_upwards [isOpen_ne.mem_nhds hv] with y hy using (hWd y hy).1.deriv
  refine ⟨by rw [iteratedDeriv_one]; exact (hWd v hv).1.deriv, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1.deriv_eq]
  exact (hWd v hv).2.1.deriv

/-- The symbol with a cutoff at the origin, `W_c(v) = (1 - ϑ(8v)) W(v)`: `C²` everywhere, `= W` for `|v| ≥ 1/4`. -/
noncomputable def cutSymbol (ϑ : ℝ → ℝ) (W : ℝ → ℂ) (v : ℝ) : ℂ := ((1 - ϑ (8 * v) : ℝ) : ℂ) * W v

lemma cutSymbol_eq {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (W : ℝ → ℂ) {v : ℝ} (hv : 1 / 4 ≤ |v|) :
    cutSymbol ϑ W v = W v := by
  have : ϑ (8 * v) = 0 := by
    apply hϑ.zero
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; linarith
  simp [cutSymbol, this]

lemma cutSymbol_contDiff {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) :
    ContDiff ℝ 2 (cutSymbol ϑ W) := by
  have hf : ContDiff ℝ 2 (fun v : ℝ => ((1 - ϑ (8 * v) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub ((hϑ.contDiff.of_le (by norm_num)).comp
      (contDiff_const.mul contDiff_id)))
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst hv
    have : cutSymbol ϑ W =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (by simp : |(0 : ℝ)| < 1 / 8)] with y hy
      have : ϑ (8 * y) = 1 := by
        apply hϑ.one
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
        have : |y| < 1 / 8 := hy
        linarith
      simp [cutSymbol, this]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf.contDiffAt.mul (contDiffAt_two_of_chain hv hWd)

/-- The cut symbol has the same derivatives as `W` for `|v| > 1/4`. -/
lemma cutSymbol_iterDeriv {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) {v : ℝ}
    (hv : 1 / 4 < |v|) :
    iteratedDeriv 0 (cutSymbol ϑ W) v = W v ∧ iteratedDeriv 1 (cutSymbol ϑ W) v = W1 v ∧
      iteratedDeriv 2 (cutSymbol ϑ W) v = W2 v := by
  have hev : cutSymbol ϑ W =ᶠ[nhds v] W := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hv] with y hy using cutSymbol_eq hϑ W hy.le
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv; linarith
  obtain ⟨c1, c2⟩ := iterDeriv_chain hWd hv0
  refine ⟨by simpa using (hev.eq_of_nhds), ?_, ?_⟩
  · rw [hev.iteratedDeriv_eq 1, c1]
  · rw [hev.iteratedDeriv_eq 2, c2]

/-- Phase facts for `Φ = edgePhi L`: `|Φ'| ≥ p₀` and `|Φ''| ≤ 12.5` on `|τ| ≥ 0.08`, `|Φ'''| ≤ 7` everywhere (`0 < L ≤ 0.002`). -/
lemma edgePhi_phase_facts : ∃ p0 : ℝ, 0 < p0 ∧ ∀ {L : ℝ}, 0 < L → L ≤ 0.002 →
    ContDiff ℝ 3 (edgePhi L) ∧ (∀ τ : ℝ, 0.08 ≤ |τ| → p0 ≤ |deriv (edgePhi L) τ|) ∧
    (∀ τ : ℝ, 0.08 ≤ |τ| → |deriv (deriv (edgePhi L)) τ| ≤ 12.5) ∧
    (∀ τ : ℝ, |deriv (deriv (deriv (edgePhi L))) τ| ≤ 7) := by
  obtain ⟨c3, hc3, hq⟩ := neg_edgePhiDeriv_ge_quad
  refine ⟨c3 * 0.0064, by positivity, ?_⟩
  intro L hL0 hL2
  have hcd : ContDiff ℝ 3 (edgePhi L) := by
    rw [show edgePhi L = fun τ => L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ from funext (edgePhi_eq_cubic_add_ceHth L)]
    exact (((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add edgeR_contDiff)
  have hd1 : deriv (edgePhi L) = edgePhiDeriv L := funext fun t => (hasDerivAt_edgePhi L t).deriv
  have hd2 : deriv (edgePhiDeriv L) = edgePhiDeriv2 := funext fun t => (hasDerivAt_edgePhiDeriv L t).deriv
  refine ⟨hcd, ?_, ?_, ?_⟩
  · intro τ hτ
    rw [hd1]
    have h0 := tau0_pos hL0
    have h1 := ceEll_tau0 hL0
    have h2 := (tau0_bounds hL0 hL2).1
    have h3 := hq L hL0 (tau0 L) h0 h1 τ (by linarith)
    have hmin : (0.0064 : ℝ) ≤ min (τ ^ 2) 1 := by
      refine le_min ?_ (by norm_num)
      have : (0.08 : ℝ) ^ 2 ≤ |τ| ^ 2 := pow_le_pow_left₀ (by norm_num) hτ 2
      rw [sq_abs] at this; linarith
    calc c3 * 0.0064 ≤ c3 * min (τ ^ 2) 1 := mul_le_mul_of_nonneg_left hmin hc3.le
      _ ≤ -edgePhiDeriv L τ := h3
      _ ≤ |edgePhiDeriv L τ| := neg_le_abs _
  · intro τ hτ
    rw [hd1, hd2]
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
    have := (edgePhiDeriv2_abs_le hτ0).trans (min_le_right _ _)
    refine this.trans ?_
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  · intro τ
    have e3 : deriv (deriv (deriv (edgePhi L))) τ = iteratedDeriv 3 (edgePhi L) τ := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e3]
    set p : ℝ → ℝ := fun s => L * s - Real.pi ^ 2 / 36 * s ^ 3 with hp
    have hp_cd : ContDiff ℝ 3 p := by rw [hp]; fun_prop
    have hdecomp : edgePhi L = fun s => p s + edgeR s := funext fun s => by
      rw [edgePhi_eq_cubic_add_ceHth]; rfl
    have hd1p : deriv p = fun s => L - Real.pi ^ 2 / 12 * s ^ 2 := funext fun s =>
      (((hasDerivAt_id s).const_mul L).sub (((hasDerivAt_pow 3 s).const_mul (Real.pi ^ 2 / 36)))).congr_deriv (by simp; ring) |>.deriv
    have hd2p : deriv (deriv p) = fun s => -(Real.pi ^ 2 / 6) * s := by
      rw [hd1p]
      exact funext fun s => ((((hasDerivAt_pow 2 s).const_mul (Real.pi ^ 2 / 12)).const_sub L)).congr_deriv (by ring) |>.deriv
    have hp3 : iteratedDeriv 3 p τ = -(Real.pi ^ 2 / 6) := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hd2p]
      exact (((hasDerivAt_id τ).const_mul (-(Real.pi ^ 2 / 6))).congr_deriv (by ring)).deriv
    have hadd3 : iteratedDeriv 3 (edgePhi L) τ = -(Real.pi ^ 2 / 6) + iteratedDeriv 3 edgeR τ := by
      rw [hdecomp, iteratedDeriv_fun_add hp_cd.contDiffAt edgeR_contDiff.contDiffAt, hp3]
    rw [hadd3]
    have htri : |-(Real.pi ^ 2 / 6) + iteratedDeriv 3 edgeR τ| ≤ Real.pi ^ 2 / 6 + Real.pi ^ 2 / 2 :=
      (abs_add_le _ _).trans (by
        rw [abs_neg, abs_of_pos (by positivity)]; gcongr; exact (edgeR_deriv_bounds τ).2.2.2)
    exact htri.trans (by nlinarith [Real.pi_pos, Real.pi_lt_d2])

/-- Derivatives of `t ↦ (g t : ℂ)` for real `g ∈ C²`. -/
lemma iterDeriv_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (x : ℝ) :
    iteratedDeriv 1 (fun t => (g t : ℂ)) x = ((deriv g x : ℝ) : ℂ) ∧
    iteratedDeriv 2 (fun t => (g t : ℂ)) x = ((deriv (deriv g) x : ℝ) : ℂ) := by
  have hgD : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (deriv g) := (hg.deriv' : ContDiff ℝ 1 (deriv g)).differentiable (by norm_num)
  have h1 : deriv (fun t => (g t : ℂ)) = fun t => ((deriv g t : ℝ) : ℂ) :=
    funext fun t => (hgD t).hasDerivAt.ofReal_comp.deriv
  refine ⟨by rw [iteratedDeriv_one, h1], ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  exact (hdg x).hasDerivAt.ofReal_comp.deriv

/-- `(t/ε)^{-p} = t^{-p} ε^p`. -/
lemma div_rpow_neg_aux {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (p : ℝ) : (t / ε) ^ (-p) = t ^ (-p) * ε ^ p := by
  rw [Real.div_rpow ht.le hε.le, Real.rpow_neg hε.le, div_inv_eq_mul]

set_option maxHeartbeats 3200000 in
/-- The amplitude `A = (1 - ϑ(·/0.08)) k_c W_c(·/ε)` of the main outer piece: `C²`, vanishing on `|τ| < 0.08`, with
`‖A^{(r)}(τ)‖ ≤ C ε^{5/2}|τ|^{-5/2}` (`r ≤ 2`, `|τ| ≥ 0.08`). -/
theorem main_outer_amp {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 0 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c ε : ℝ} {W W1 W2 W3 : ℝ → ℂ}, 2 ≤ c → 0 < ε → ε ≤ 0.16 →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      let A : ℝ → ℂ := fun τ => (((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ) * cutSymbol ϑ W (ε⁻¹ * τ)
      ContDiff ℝ 2 A ∧ (∀ τ, |τ| < 0.08 → A τ = 0) ∧
        (∀ τ, 0.08 ≤ |τ| → A τ = ((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ * W (τ / ε)) ∧
        (∀ τ, 0.08 ≤ |τ| → ‖A τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) ∧
          ‖deriv A τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) ∧
          ‖deriv (deriv A) τ‖ ≤ C * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨CK, hCK, hKb⟩ := outerK_bounds
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  set A1 : ℝ := 1 + 2 * K1 / 0.08 + 4 * K2 / 0.08 ^ 2 with hA1
  have hA1n : 1 ≤ A1 := by
    have : 0 ≤ 2 * K1 / 0.08 := by positivity
    have : 0 ≤ 4 * K2 / 0.08 ^ 2 := by positivity
    linarith
  refine ⟨4 * (4 * A1 * CK) * (AW * (1 / 0.08) ^ 2), by positivity, ?_⟩
  intro c ε W W1 W2 W3 hc hε hε16 hWd hWb A
  have hcut := hϑ.cut (R := 0.08) (by norm_num)
  have hc2 : ContDiff ℝ 2 (outerK c) := (hKb (c := c) hc).1
  have hf1 : ContDiff ℝ 2 (fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hcut.contDiff)
  have hf3 : ContDiff ℝ 2 (fun t : ℝ => cutSymbol ϑ W (ε⁻¹ * t)) :=
    (cutSymbol_contDiff hϑ hWd).comp (contDiff_const.mul contDiff_id)
  have hAC : ContDiff ℝ 2 A := (hf1.mul hc2).mul hf3
  have hAsupp : ∀ τ, |τ| < 0.08 → A τ = 0 := by
    intro τ hτ
    have : ϑ (τ / 0.08) = 1 := by
      apply hϑ.one
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), div_le_one (by norm_num)]; exact hτ.le
    simp [A, this]
  have hAeq : ∀ τ, 0.08 ≤ |τ| → A τ = ((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ * W (τ / ε) := by
    intro τ hτ
    have hv : 1 / 4 ≤ |ε⁻¹ * τ| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hε)]
      have : 0.5 ≤ ε⁻¹ * |τ| := by
        rw [← div_eq_inv_mul, le_div_iff₀ hε]; nlinarith
      linarith
    simp only [A]
    rw [cutSymbol_eq hϑ W hv, ← div_eq_inv_mul]
  refine ⟨hAC, hAsupp, hAeq, ?_⟩
  intro τ hτ
  have hτp : 0 < |τ| := by linarith
  have hτ0 : τ ≠ 0 := abs_pos.mp hτp
  -- bounds for the three factors
  have hB1 : ∀ i ≤ 2, ‖iteratedDeriv i (fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ)) τ‖ ≤ A1 := by
    have hg : ContDiff ℝ 2 (fun t : ℝ => 1 - ϑ (t / 0.08)) := contDiff_const.sub hcut.contDiff
    obtain ⟨d1, d2⟩ := iterDeriv_ofReal hg τ
    have e1 : deriv (fun t : ℝ => 1 - ϑ (t / 0.08)) τ = -deriv (fun t : ℝ => ϑ (t / 0.08)) τ := by
      rw [deriv_const_sub]
    have e2 : deriv (deriv (fun t : ℝ => 1 - ϑ (t / 0.08))) τ = -deriv (deriv (fun t : ℝ => ϑ (t / 0.08))) τ := by
      have : deriv (fun t : ℝ => 1 - ϑ (t / 0.08)) = fun t => -deriv (fun t : ℝ => ϑ (t / 0.08)) t :=
        funext fun t => by rw [deriv_const_sub]
      rw [this, deriv.fun_neg]
    have hb1 : |deriv (fun t : ℝ => ϑ (t / 0.08)) τ| ≤ 2 * K1 / 0.08 := by
      have := hcut.bound1 τ hτ0
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [abs_nonneg (deriv (fun t : ℝ => ϑ (t / 0.08)) τ)]
    have hb2 : |deriv (deriv (fun t : ℝ => ϑ (t / 0.08))) τ| ≤ 4 * K2 / 0.08 ^ 2 := by
      have := hcut.bound2 τ hτ0
      rw [le_div_iff₀ (by norm_num)]
      have hxx : (0.08 : ℝ) ^ 2 ≤ τ ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num) hτ 2
        rwa [sq_abs] at this
      nlinarith [abs_nonneg (deriv (deriv (fun t : ℝ => ϑ (t / 0.08))) τ)]
    intro i hi
    interval_cases i
    · simp only [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]
      have hr := hϑ.range (τ / 0.08)
      rw [abs_of_nonneg (by linarith [hr.2])]
      have hp1 : 0 ≤ 2 * K1 / 0.08 := by positivity
      have hp2 : 0 ≤ 4 * K2 / 0.08 ^ 2 := by positivity
      linarith [hr.1]
    · rw [d1, Complex.norm_real, Real.norm_eq_abs, e1, abs_neg]
      have : 0 ≤ 4 * K2 / 0.08 ^ 2 := by positivity
      linarith
    · rw [d2, Complex.norm_real, Real.norm_eq_abs, e2, abs_neg]
      have : 0 ≤ 2 * K1 / 0.08 := by positivity
      linarith
  have hB2 : ∀ i ≤ 2, ‖iteratedDeriv i (outerK c) τ‖ ≤ CK := by
    intro i hi
    refine ((hKb (c := c) hc).2 i hi τ).trans ?_
    have : (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num)
    nlinarith
  have hv : 0.5 ≤ ε⁻¹ * |τ| := by
    rw [← div_eq_inv_mul, le_div_iff₀ hε]; nlinarith
  have hv4 : 1 / 4 < |ε⁻¹ * τ| := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hε)]; linarith
  obtain ⟨hs0, hs1, hs2⟩ := cutSymbol_iterDeriv hϑ hWd hv4
  have hWbv := hWb (ε⁻¹ * τ) (by rw [abs_mul, abs_of_pos (inv_pos.2 hε)]; linarith)
  have hxs : |ε⁻¹ * τ| = |τ| / ε := by rw [abs_mul, abs_of_pos (inv_pos.2 hε), ← div_eq_inv_mul]
  obtain ⟨hsh1, hsh2⟩ := mbt_rpow_shift hτp
  have hαx : |τ|⁻¹ ≤ 1 / 0.08 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hτ
  have hε5 : 0 ≤ ε ^ (5 / 2 : ℝ) := Real.rpow_nonneg hε.le _
  have hxp : 0 ≤ |τ| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hτp.le _
  have hinv0 : 0 ≤ |τ|⁻¹ := inv_nonneg.2 hτp.le
  have hB3 : ∀ i ≤ 2, ‖iteratedDeriv i (fun t : ℝ => cutSymbol ϑ W (ε⁻¹ * t)) τ‖ ≤
      AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by
    intro i hi
    have hcdi : ContDiff ℝ (i : WithTop ℕ∞) (cutSymbol ϑ W) :=
      (cutSymbol_contDiff hϑ hWd).of_le (by exact_mod_cast hi)
    rw [iteratedDeriv_comp_const_smul hcdi]
    show ‖ε⁻¹ ^ i • iteratedDeriv i (cutSymbol ϑ W) (ε⁻¹ * τ)‖ ≤ _
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
    interval_cases i
    · rw [hs0, pow_zero, one_mul]
      have := hWbv.1
      rw [hxs, div_rpow_neg_aux hτp hε (5 / 2)] at this
      calc ‖W (ε⁻¹ * τ)‖ ≤ AW * (|τ| ^ (-(5 / 2 : ℝ)) * ε ^ (5 / 2 : ℝ)) := this
        _ ≤ AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by
          have : (1 : ℝ) ≤ (1 / 0.08) ^ 2 := by norm_num
          nlinarith [mul_nonneg hAW (mul_nonneg hε5 hxp)]
    · rw [hs1, pow_one]
      have := hWbv.2.1
      rw [hxs, div_rpow_neg_aux hτp hε (7 / 2), hsh1] at this
      have hε' : ε ^ (7 / 2 : ℝ) = ε ^ (5 / 2 : ℝ) * ε := by
        rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add hε, Real.rpow_one]
      rw [hε'] at this
      calc ε⁻¹ * ‖W1 (ε⁻¹ * τ)‖ ≤ ε⁻¹ * (AW * (|τ| ^ (-(5 / 2 : ℝ)) * |τ|⁻¹ * (ε ^ (5 / 2 : ℝ) * ε))) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hε.le)
        _ = AW * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) * |τ|⁻¹ := by field_simp
        _ ≤ AW * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) * (1 / 0.08) :=
            mul_le_mul_of_nonneg_left hαx (mul_nonneg hAW (mul_nonneg hε5 hxp))
        _ ≤ AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by
          have : 1 / 0.08 ≤ ((1 : ℝ) / 0.08) ^ 2 := by norm_num
          nlinarith [mul_nonneg hAW (mul_nonneg hε5 hxp)]
    · rw [hs2]
      have := hWbv.2.2.1
      rw [hxs, div_rpow_neg_aux hτp hε (9 / 2), hsh2] at this
      have hε' : ε ^ (9 / 2 : ℝ) = ε ^ (5 / 2 : ℝ) * ε ^ 2 := by
        rw [show (9 / 2 : ℝ) = 5 / 2 + (2 : ℕ) by norm_num, Real.rpow_add hε, Real.rpow_natCast]
      rw [hε'] at this
      calc ε⁻¹ ^ 2 * ‖W2 (ε⁻¹ * τ)‖ ≤ ε⁻¹ ^ 2 * (AW * (|τ| ^ (-(5 / 2 : ℝ)) * |τ|⁻¹ * |τ|⁻¹ * (ε ^ (5 / 2 : ℝ) * ε ^ 2))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = AW * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) * (|τ|⁻¹ * |τ|⁻¹) := by field_simp
        _ ≤ AW * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) * ((1 / 0.08) * (1 / 0.08)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hαx hαx hinv0 (by norm_num)) (mul_nonneg hAW (mul_nonneg hε5 hxp))
        _ = AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ))) := by ring
  -- product bounds
  have hf12 : ContDiff ℝ 2 (fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ) * outerK c t) := hf1.mul hc2
  have hB12 : ∀ i ≤ 2, ‖iteratedDeriv i (fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ) * outerK c t) τ‖ ≤ 4 * (A1 * CK) := by
    intro i hi
    have := norm_iteratedDeriv_mul_le (N := 2) (j := i) (τ := τ) (f := fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ))
      (g := outerK c) (by linarith) hCK.le hi hf1 hc2 (fun k hk => hB1 k (hk.trans hi)) (fun k hk => hB2 k (hk.trans hi))
    have hh : ‖iteratedDeriv i (fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ) * outerK c t) τ‖ ≤ (2 : ℝ) ^ 2 * A1 * CK := this
    exact hh.trans_eq (by ring)
  have hmain : ∀ j ≤ 2, ‖iteratedDeriv j A τ‖ ≤
      4 * (4 * (A1 * CK)) * (AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)))) := by
    intro j hj
    have := norm_iteratedDeriv_mul_le (N := 2) (j := j) (τ := τ)
      (f := fun t : ℝ => ((1 - ϑ (t / 0.08) : ℝ) : ℂ) * outerK c t) (g := fun t : ℝ => cutSymbol ϑ W (ε⁻¹ * t))
      (by positivity) (by positivity) hj hf12 hf3 (fun k hk => hB12 k (hk.trans hj)) (fun k hk => hB3 k (hk.trans hj))
    have hh : ‖iteratedDeriv j A τ‖ ≤ (2 : ℝ) ^ 2 * (4 * (A1 * CK)) *
        (AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)))) := this
    exact hh.trans_eq (by ring)
  have hfinal : 4 * (4 * (A1 * CK)) * (AW * (1 / 0.08) ^ 2 * (ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)))) =
      (4 * (4 * A1 * CK) * (AW * (1 / 0.08) ^ 2)) * ε ^ (5 / 2 : ℝ) * |τ| ^ (-(5 / 2 : ℝ)) := by ring
  rw [← hfinal]
  refine ⟨?_, ?_, ?_⟩
  · simpa using hmain 0 (by norm_num)
  · have := hmain 1 (by norm_num); rwa [iteratedDeriv_one] at this
  · have := hmain 2 (by norm_num); rwa [iteratedDeriv_succ, iteratedDeriv_one] at this

/-- **The main outer piece.** For `0 < L ≤ 0.002`, `c ≥ 2`, `0 < ε ≤ 0.16` and a symbol `W` with `|W^{(j)}(s)| ≤ A_W |s|^{-5/2-j}`
(`|s| ≥ 1/2`, `j ≤ 3`), `‖∫ (1 - ϑ(τ/0.08)) k_c(τ) W(τ/ε) e^{icΦ(τ;L)} dτ‖ ≤ C ε^{5/2} c^{-2}`, `C` depending only on `A_W` and `ϑ`. -/
theorem main_outer_bound {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 0 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L c ε : ℝ} {W W1 W2 W3 : ℝ → ℂ}, 0 < L → L ≤ 0.002 → 2 ≤ c → 0 < ε → ε ≤ 0.16 →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      ‖∫ τ : ℝ, (((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ * W (τ / ε)) *
          Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))‖ ≤ C * ε ^ (5 / 2 : ℝ) / c ^ 2 := by
  obtain ⟨CA, hCA, hA⟩ := main_outer_amp hϑ AW hAW
  obtain ⟨p0, hp0, hph⟩ := edgePhi_phase_facts
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  set Kt : ℝ := 1 + 4 * K1 / 0.08 + 4 * K2 / 0.08 ^ 2 with hKt
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  refine ⟨2 * (Kt * CA * ((0.08 : ℝ) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1)) * ibpLam p0 12.5 7), by
    have := ibpLam_nonneg hp0 (by norm_num : (0 : ℝ) ≤ 12.5) (by norm_num : (0 : ℝ) ≤ 7)
    positivity, ?_⟩
  intro L c ε W W1 W2 W3 hL0 hL2 hc hε hε16 hWd hWb
  obtain ⟨hAC, hAsupp, hAeq, hAb⟩ := hA hc hε hε16 hWd hWb
  obtain ⟨hcd, hd1, hd2, hd3⟩ := hph hL0 hL2
  have hc0 : 0 < c := by linarith
  set A : ℝ → ℂ := fun τ => (((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ) * cutSymbol ϑ W (ε⁻¹ * τ) with hAdef
  set ψ : ℝ → ℝ := fun τ => c * edgePhi L τ with hψ
  have hψC : ContDiff ℝ 3 ψ := contDiff_const.mul hcd
  have hψ1' : deriv ψ = fun τ => c * deriv (edgePhi L) τ := funext fun τ => by
    simp only [hψ]; exact deriv_const_mul_field c
  have hψ2' : deriv (deriv ψ) = fun τ => c * deriv (deriv (edgePhi L)) τ := by
    rw [hψ1']; funext τ; exact deriv_const_mul_field c
  have hψ3' : deriv (deriv (deriv ψ)) = fun τ => c * deriv (deriv (deriv (edgePhi L))) τ := by
    rw [hψ2']; funext τ; exact deriv_const_mul_field c
  set B : ℝ := CA * ε ^ (5 / 2 : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hint : (∫ τ : ℝ, (((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ * W (τ / ε)) *
      Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))) = ∫ τ : ℝ, A τ * Complex.exp (Complex.I * ψ τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    show _ = A τ * Complex.exp (Complex.I * ψ τ)
    by_cases hτ : 0.08 ≤ |τ|
    · rw [hAeq τ hτ]
    · have : A τ = 0 := hAsupp τ (not_le.1 hτ)
      have h1 : ϑ (τ / 0.08) = 1 := by
        apply hϑ.one
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), div_le_one (by norm_num)]; exact (not_le.1 hτ).le
      simp [this, h1]
  rw [hint]
  have habs : ∀ τ : ℝ, 0.08 ≤ |τ| → ‖A τ‖ ≤ B * |τ| ^ (-(5 / 2 : ℝ)) ∧ ‖deriv A τ‖ ≤ B * |τ| ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (deriv A) τ‖ ≤ B * |τ| ^ (-(5 / 2 : ℝ)) := by
    intro τ hτ
    obtain ⟨a0, a1, a2⟩ := hAb τ hτ
    rw [hB]
    exact ⟨by linarith [a0], by linarith [a1], by linarith [a2]⟩
  have hmain := two_ibp_phase_line hϑ (a := A) (ψ := ψ) (α := 0.08) (B := B) (p := c * p0) (M2 := c * 12.5) (M3 := c * 7)
    (s := 5 / 2) (by norm_num) (by norm_num) hB0 (by positivity) (by positivity) (by positivity) hAC hψC hAsupp
    (fun τ hτ => (habs τ hτ).1) (fun τ hτ => (habs τ hτ).2.1) (fun τ hτ => (habs τ hτ).2.2)
    (fun τ hτ => by rw [hψ1']; simp only [abs_mul, abs_of_pos hc0]; exact mul_le_mul_of_nonneg_left (hd1 τ hτ) hc0.le)
    (fun τ hτ => by rw [hψ2']; simp only [abs_mul, abs_of_pos hc0]; exact mul_le_mul_of_nonneg_left (hd2 τ hτ) hc0.le)
    (fun τ hτ => by
      rw [hψ3']; simp only [abs_mul, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_left (by simpa using hd3 τ) hc0.le)
  refine hmain.trans ?_
  have hlam : ibpLam (c * p0) (c * 12.5) (c * 7) = ibpLam p0 12.5 7 / c ^ 2 := by
    unfold ibpLam
    field_simp
  rw [hlam, hB]
  have hnn : 0 ≤ ibpLam p0 12.5 7 := ibpLam_nonneg hp0 (by norm_num) (by norm_num)
  have hε5 : 0 ≤ ε ^ (5 / 2 : ℝ) := Real.rpow_nonneg hε.le _
  have e : 2 * ((1 + 4 * K1 / 0.08 + 4 * K2 / 0.08 ^ 2) * (CA * ε ^ (5 / 2 : ℝ)) * ((0.08 : ℝ) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1)) *
      (ibpLam p0 12.5 7 / c ^ 2)) =
      2 * (Kt * CA * ((0.08 : ℝ) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1)) * ibpLam p0 12.5 7) * ε ^ (5 / 2 : ℝ) / c ^ 2 := by
    rw [hKt]; ring
  rw [e]

/-- info: 'FormalResearch.SignUncertainty.main_outer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main_outer_bound

/-- info: 'FormalResearch.SignUncertainty.edgePhi_phase_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.edgePhi_phase_facts

/-- info: 'FormalResearch.SignUncertainty.main_outer_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.main_outer_amp

end FormalResearch.SignUncertainty

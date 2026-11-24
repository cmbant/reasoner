module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GT.2a `(e8)`: derivative bounds for the symbol difference `𝒟`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, inner difference, bound `(e8)`.

For the symbol `W̃(v) = W(iv)` (with derivatives `W1, W2, W3`, each of size `|v|^{-5/2-j}` for `|v| ≥ 1/2`), a reparametrisation
`w` with `w(u) ≈ u`, and the amplitude difference `Q = P - E`, the function `𝒟 = Q · W̃(w) + E · (W̃(w) - W̃)` satisfies
`|𝒟^{(r)}(u)| ≤ C δ(u) |u|^{-5/2-r}` (`r ≤ 2`, `|u| ≥ 1`), where `δ(u) = L + ε²u²` is the size of
`w - u`, `w' - 1`, `Q` etc. relative to `|u|` and its derivatives.  The proof is the third-order mean value step on the segment `[u, w(u)]`
(the `r = 2` bound differentiates `W̃(w) - W̃` to `W̃'''`).

* `symbol_diff_local`: the three bounds at one point `u` in terms of a local symbol size `ρ` (`|W^{(j)}(x)| ≲ ρ|u|^{-j}` for `|x|` between
  `|u|/2` and `R`), valid for any exponent regime (used with `ρ = |u|^{-5/2}` for `|u| ≥ 1` and with `ρ = |u|^{1/2}`, `W - W(0)`, near zero);
* `symbol_diff_bounds`: the large-`|u|` case `ρ = |u|^{-5/2}`, with `C` depending only on the constant `A` of the hypotheses.

Status: proved, unconditional (pointwise bounds from pointwise hypotheses).  Not formalised here: the verification of the hypotheses for the
normal form `τ` (`O.4`), which is the content of the later modules.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty

/-- `|x|^{-p} ≤ 64 m^{-p}` for `m/2 ≤ |x|`, `0 < p ≤ 6`. -/
lemma mbd_rpow_le {m x p : ℝ} (hm : 0 < m) (hx : m / 2 ≤ |x|) (hp : 0 < p) (hp6 : p ≤ 6) :
    |x| ^ (-p) ≤ 64 * m ^ (-p) := by
  have hm2 : 0 < m / 2 := by positivity
  have h1 : |x| ^ (-p) ≤ (m / 2) ^ (-p) := Real.rpow_le_rpow_of_nonpos hm2 hx (by linarith)
  have h2 : (m / 2) ^ (-p) = 2 ^ p * m ^ (-p) := by
    rw [div_eq_mul_inv, Real.mul_rpow hm.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]
  have h3 : (2 : ℝ) ^ p ≤ 64 := by
    calc (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp6
      _ = 64 := by norm_num
  have h4 : 0 ≤ m ^ (-p) := Real.rpow_nonneg hm.le _
  rw [h2] at h1
  nlinarith

/-- Points of the segment `[u, w]` have `|x| ≥ |u|/2` when `u, w` have the same sign and `|w| ≥ |u|/2`. -/
lemma mbd_seg_ge {u w x : ℝ} (hs : 0 < w * u) (hw : |u| / 2 ≤ |w|) (hx : x ∈ uIcc u w) : |u| / 2 ≤ |x| := by
  rw [mem_uIcc] at hx
  rcases lt_or_gt_of_ne (show u ≠ 0 from fun h => by simp [h] at hs) with hu | hu
  · have hw0 : w < 0 := by nlinarith
    rw [abs_of_neg hu, abs_of_neg hw0] at hw
    rw [abs_of_neg hu]
    have hx0 : x ≤ 0 := by rcases hx with h | h <;> linarith [h.2]
    rw [abs_of_nonpos hx0]
    rcases hx with h | h <;> linarith [h.1, h.2]
  · have hw0 : 0 < w := by nlinarith
    rw [abs_of_pos hu, abs_of_pos hw0] at hw
    rw [abs_of_pos hu]
    have hx0 : 0 ≤ x := by rcases hx with h | h <;> linarith [h.1]
    rw [abs_of_nonneg hx0]
    rcases hx with h | h <;> linarith [h.1, h.2]

/-- Mean value bound for a symbol derivative along the segment `[u, w]`. -/
lemma mbd_mvt {f f' : ℝ → ℂ} {u w B : ℝ}
    (hf : ∀ x ∈ uIcc u w, HasDerivAt f (f' x) x) (hB : ∀ x ∈ uIcc u w, ‖f' x‖ ≤ B) :
    ‖f w - f u‖ ≤ B * |w - u| := by
  have := (convex_uIcc u w).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := B)
    (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => hB x hx)
    (left_mem_uIcc) (right_mem_uIcc)
  simpa [Real.norm_eq_abs] using this

/-- Points of the segment `[u, w]` have `|x| ≤ R` when `|u|, |w| ≤ R`. -/
lemma mbd_seg_le {u w x R : ℝ} (hu : |u| ≤ R) (hw : |w| ≤ R) (hx : x ∈ uIcc u w) : |x| ≤ R := by
  rw [mem_uIcc] at hx
  have h1 := abs_le.mp hu
  have h2 := abs_le.mp hw
  rw [abs_le]
  rcases hx with h | h <;> constructor <;> linarith [h.1, h.2]

/-- **`(e8)` at a point.**  Hypotheses (all pointwise at `u`, `|u| ≥ 1`, with `δ ∈ [0,1]` the size `L + ε²u²`): the symbol `W` has derivatives
`W1, W2, W3` with `‖W^{(j)}(s)‖ ≤ A|s|^{-5/2-j}` for `|s| ≥ 1/2`; the reparametrisation `w` has `|w - u| ≤ Aδ|u|`, `|w' - 1| ≤ Aδ`,
`|w''| ≤ Aδ/|u|`, `|w| ≥ |u|/2` and the sign of `u`; `Q = P - E` has `‖Q^{(j)}‖ ≤ Aδ|u|^{-j}` and `E` has `‖E^{(j)}‖ ≤ A|u|^{-j}`.
Then `𝒟 = Q W(w) + E (W(w) - W)` has `‖𝒟^{(r)}(u)‖ ≤ C δ |u|^{-5/2-r}` for `r ≤ 2`, with `C = 4096 A⁴`. -/
theorem symbol_diff_local (A : ℝ) (hA : 1 ≤ A) :
    ∀ {U : Set ℝ}, IsOpen U →
    ∀ {W W1 W2 W3 : ℝ → ℂ} {w w1 w2 : ℝ → ℝ} {Q Q1 Q2 E E1 E2 : ℝ → ℂ} {δ u ρ R : ℝ},
      u ∈ U → 0 < |u| → 0 ≤ δ → δ ≤ 1 → 0 < ρ → |u| ≤ R → |w u| ≤ R →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ x, |u| / 2 ≤ |x| → |x| ≤ R → ‖W x‖ ≤ 64 * A * ρ ∧ ‖W1 x‖ ≤ 64 * A * (ρ * |u|⁻¹) ∧
        ‖W2 x‖ ≤ 64 * A * (ρ * (|u|⁻¹) ^ 2) ∧ ‖W3 x‖ ≤ 64 * A * (ρ * (|u|⁻¹) ^ 3)) →
      (∀ s ∈ U, HasDerivAt w (w1 s) s ∧ HasDerivAt w1 (w2 s) s) →
      (∀ s ∈ U, HasDerivAt Q (Q1 s) s ∧ HasDerivAt Q1 (Q2 s) s) →
      (∀ s ∈ U, HasDerivAt E (E1 s) s ∧ HasDerivAt E1 (E2 s) s) →
      0 < w u * u → |u| / 2 ≤ |w u| → |w u - u| ≤ A * δ * |u| → |w1 u - 1| ≤ A * δ → |w2 u| ≤ A * δ / |u| →
      ‖Q u‖ ≤ A * δ → ‖Q1 u‖ ≤ A * δ / |u| → ‖Q2 u‖ ≤ A * δ / |u| ^ 2 →
      ‖E u‖ ≤ A → ‖E1 u‖ ≤ A / |u| → ‖E2 u‖ ≤ A / |u| ^ 2 →
      ‖Q u * W (w u) + E u * (W (w u) - W u)‖ ≤ 4096 * A ^ 4 * (δ * ρ) ∧
      ‖deriv (fun s => Q s * W (w s) + E s * (W (w s) - W s)) u‖ ≤ 4096 * A ^ 4 * (δ * (ρ * |u|⁻¹)) ∧
      ‖deriv (deriv (fun s => Q s * W (w s) + E s * (W (w s) - W s))) u‖ ≤ 4096 * A ^ 4 * (δ * (ρ * (|u|⁻¹) ^ 2)) := by
  intro U hU W W1 W2 W3 w w1 w2 Q Q1 Q2 E E1 E2 δ u ρ R huU hu1 hδ0 hδ1 hρ huR hwR hWd hSbl hwd hQd hEd hsg hw0 hw hw1 hw2 hQ0 hQ1 hQ2 hE0 hE1 hE2
  set m : ℝ := |u| with hm
  have hm0 : 0 < m := hu1
  set q : ℝ := m⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr hm0
  have hρ0 : 0 < ρ := hρ
  have hmq : m * q = 1 := mul_inv_cancel₀ hm0.ne'
  have hwm : m / 2 ≤ |w u| := hw0
  have hSb : ∀ x : ℝ, x ∈ uIcc u (w u) → ‖W x‖ ≤ 64 * A * ρ ∧ ‖W1 x‖ ≤ 64 * A * (ρ * q) ∧
      ‖W2 x‖ ≤ 64 * A * (ρ * q ^ 2) ∧ ‖W3 x‖ ≤ 64 * A * (ρ * q ^ 3) := fun x hx =>
    hSbl x (mbd_seg_ge hsg hwm hx) (mbd_seg_le huR hwR hx)
  obtain ⟨hB0, hB1, hB2, -⟩ := hSbl (w u) hwm hwR
  obtain ⟨hU0, hU1, hU2, -⟩ := hSbl u (by linarith) huR
  -- mean value bounds
  have hAδ : 0 ≤ A * δ := by positivity
  have hwu : |w u - u| ≤ A * δ * m := hw
  have mvt : ∀ (f f' : ℝ → ℂ) (B : ℝ), (∀ x ∈ uIcc u (w u), HasDerivAt f (f' x) x) →
      (∀ x ∈ uIcc u (w u), ‖f' x‖ ≤ B) → ‖f (w u) - f u‖ ≤ B * (A * δ * m) := by
    intro f f' B hf hB
    exact (mbd_mvt hf hB).trans (mul_le_mul_of_nonneg_left hwu (by
      have := hB u left_mem_uIcc; exact (norm_nonneg _).trans this))
  have hne : ∀ x : ℝ, m / 2 ≤ |x| → x ≠ 0 := fun x hx h => by simp [h] at hx; linarith
  have hΔ0 : ‖W (w u) - W u‖ ≤ 64 * A ^ 2 * δ * ρ := by
    have := mvt W W1 (64 * A * (ρ * q)) (fun x hx => (hWd x (hne x (mbd_seg_ge hsg hwm hx))).1) (fun x hx => (hSb x hx).2.1)
    calc _ ≤ _ := this
      _ = 64 * A ^ 2 * δ * ρ * (m * q) := by ring
      _ = _ := by rw [hmq]; ring
  have hΔ1 : ‖W1 (w u) - W1 u‖ ≤ 64 * A ^ 2 * δ * (ρ * q) := by
    have := mvt W1 W2 (64 * A * (ρ * q ^ 2)) (fun x hx => (hWd x (hne x (mbd_seg_ge hsg hwm hx))).2.1) (fun x hx => (hSb x hx).2.2.1)
    calc _ ≤ _ := this
      _ = 64 * A ^ 2 * δ * (ρ * q) * (m * q) := by ring
      _ = _ := by rw [hmq]; ring
  have hΔ2 : ‖W2 (w u) - W2 u‖ ≤ 64 * A ^ 2 * δ * (ρ * q ^ 2) := by
    have := mvt W2 W3 (64 * A * (ρ * q ^ 3)) (fun x hx => (hWd x (hne x (mbd_seg_ge hsg hwm hx))).2.2) (fun x hx => (hSb x hx).2.2.2)
    calc _ ≤ _ := this
      _ = 64 * A ^ 2 * δ * (ρ * q ^ 2) * (m * q) := by ring
      _ = _ := by rw [hmq]; ring
  -- derivative facts near `u`
  have hev : ∀ᶠ s in 𝓝 u, s ∈ U ∧ w s ≠ 0 ∧ s ≠ 0 := by
    have h1 : U ∈ 𝓝 u := hU.mem_nhds huU
    have hwc : ContinuousAt w u := (hwd u huU).1.continuousAt
    have hwu0 : w u ≠ 0 := hne _ hwm
    have h2 : ∀ᶠ s in 𝓝 u, w s ≠ 0 := hwc.eventually_ne hwu0
    have h3 : ∀ᶠ s in 𝓝 u, s ≠ 0 := eventually_ne_nhds (hne u (by linarith))
    filter_upwards [h1, h2, h3] with s a b c using ⟨a, b, c⟩
  set G : ℝ → ℂ := fun s => W (w s) with hG
  set G1 : ℝ → ℂ := fun s => ((w1 s : ℝ) : ℂ) * W1 (w s) with hG1
  set G2 : ℝ → ℂ := fun s => ((w2 s : ℝ) : ℂ) * W1 (w s) + ((w1 s : ℝ) : ℂ) * (((w1 s : ℝ) : ℂ) * W2 (w s)) with hG2
  set D : ℝ → ℂ := fun s => Q s * G s + E s * (G s - W s) with hD
  set D1 : ℝ → ℂ := fun s => Q1 s * G s + Q s * G1 s + (E1 s * (G s - W s) + E s * (G1 s - W1 s)) with hD1
  set D2 : ℝ → ℂ := fun s => (Q2 s * G s + Q1 s * G1 s) + (Q1 s * G1 s + Q s * G2 s) +
      ((E2 s * (G s - W s) + E1 s * (G1 s - W1 s)) + (E1 s * (G1 s - W1 s) + E s * (G2 s - W2 s))) with hD2
  have hGd : ∀ s, s ∈ U → w s ≠ 0 → s ≠ 0 → HasDerivAt G (G1 s) s ∧ HasDerivAt G1 (G2 s) s := by
    intro s hs hws hs0
    obtain ⟨hw1, hw2'⟩ := hwd s hs
    obtain ⟨a0, a1, a2⟩ := hWd (w s) hws
    have h0 : HasDerivAt G (G1 s) s := by
      have := a0.scomp s hw1
      simpa [hG, hG1, Function.comp_def, Complex.real_smul, mul_comm] using this
    refine ⟨h0, ?_⟩
    have hA1 : HasDerivAt (fun x => W1 (w x)) (((w1 s : ℝ) : ℂ) * W2 (w s)) s := by
      have := a1.scomp s hw1
      simpa [Function.comp_def, Complex.real_smul] using this
    have hw1c : HasDerivAt (fun x => ((w1 x : ℝ) : ℂ)) ((w2 s : ℝ) : ℂ) s := HasDerivAt.ofReal_comp hw2'
    have := hw1c.mul hA1
    convert this using 1
  have hDd : ∀ s, s ∈ U → w s ≠ 0 → s ≠ 0 → HasDerivAt D (D1 s) s ∧ HasDerivAt D1 (D2 s) s := by
    intro s hs hws hs0
    obtain ⟨g0, g1⟩ := hGd s hs hws hs0
    obtain ⟨q0, q1⟩ := hQd s hs
    obtain ⟨e0, e1⟩ := hEd s hs
    obtain ⟨a0, a1, a2⟩ := hWd s hs0
    have h0 : HasDerivAt (fun x => G x - W x) (G1 s - W1 s) s := g0.sub a0
    have h1 : HasDerivAt (fun x => G1 x - W1 x) (G2 s - W2 s) s := g1.sub a1
    refine ⟨(q0.mul g0).add (e0.mul h0), ?_⟩
    exact (((q1.mul g0).add (q0.mul g1)).add ((e1.mul h0).add (e0.mul h1))).congr_deriv (by simp only [hD2])
  have hDder : deriv D u = D1 u := (hDd u huU (hne _ hwm) (hne u (by linarith))).1.deriv
  have hDder2 : deriv (deriv D) u = D2 u := by
    have hevD : deriv D =ᶠ[𝓝 u] D1 := by
      filter_upwards [hev] with s hs
      exact (hDd s hs.1 hs.2.1 hs.2.2).1.deriv
    rw [hevD.deriv_eq]
    exact (hDd u huU (hne _ hwm) (hne u (by linarith))).2.deriv
  -- bounds of the pieces
  have hA0 : 0 < A := by linarith
  have hδA : A * δ ≤ A := by nlinarith
  have hw1b : |w1 u| ≤ 2 * A := by
    have h2 : |w1 u| ≤ 1 + A * δ := by
      have := abs_le.mp hw1
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    linarith
  have hY0 : 0 ≤ δ * ρ := by positivity
  have hY1 : 0 ≤ δ * (ρ * q) := by positivity
  have hY2 : 0 ≤ δ * (ρ * q ^ 2) := by positivity
  have nG : ‖G u‖ ≤ 64 * A * ρ := hB0
  have nG1 : ‖G1 u‖ ≤ 128 * A ^ 2 * (ρ * q) := by
    simp only [hG1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |w1 u| * ‖W1 (w u)‖ ≤ (2 * A) * (64 * A * (ρ * q)) := by gcongr
      _ = _ := by ring
  have nG2 : ‖G2 u‖ ≤ (256 * A ^ 3 + 64 * A ^ 2) * (ρ * q ^ 2) := by
    simp only [hG2]
    have a : ‖((w2 u : ℝ) : ℂ) * W1 (w u)‖ ≤ (A * q) * (64 * A * (ρ * q)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |w2 u| ≤ A * q := by
        calc |w2 u| ≤ A * δ / m := hw2
          _ ≤ A / m := by gcongr
          _ = A * q := by rw [hq, div_eq_mul_inv]
      gcongr
    have b : ‖((w1 u : ℝ) : ℂ) * (((w1 u : ℝ) : ℂ) * W2 (w u))‖ ≤ (2 * A) * ((2 * A) * (64 * A * (ρ * q ^ 2))) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (A * q) * (64 * A * (ρ * q)) + (2 * A) * ((2 * A) * (64 * A * (ρ * q ^ 2))) := add_le_add a b
      _ = (256 * A ^ 3 + 64 * A ^ 2) * (ρ * q ^ 2) := by ring
  have nH : ‖G u - W u‖ ≤ 64 * A ^ 2 * (δ * ρ) := by
    have : G u - W u = W (w u) - W u := rfl
    rw [this]; calc _ ≤ _ := hΔ0
      _ = _ := by ring
  have nH1 : ‖G1 u - W1 u‖ ≤ 128 * A ^ 2 * (δ * (ρ * q)) := by
    have eq : G1 u - W1 u = ((w1 u - 1 : ℝ) : ℂ) * W1 (w u) + (W1 (w u) - W1 u) := by
      simp only [hG1]; push_cast; ring
    rw [eq]
    calc _ ≤ ‖((w1 u - 1 : ℝ) : ℂ) * W1 (w u)‖ + ‖W1 (w u) - W1 u‖ := norm_add_le _ _
      _ ≤ (A * δ) * (64 * A * (ρ * q)) + 64 * A ^ 2 * δ * (ρ * q) := by
        refine add_le_add ?_ hΔ1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr
      _ = _ := by ring
  have nH2 : ‖G2 u - W2 u‖ ≤ (192 * A ^ 3 + 128 * A ^ 2) * (δ * (ρ * q ^ 2)) := by
    have eq : G2 u - W2 u = ((w2 u : ℝ) : ℂ) * W1 (w u) + ((w1 u - 1 : ℝ) : ℂ) * (((w1 u + 1 : ℝ) : ℂ) * W2 (w u)) +
        (W2 (w u) - W2 u) := by
      simp only [hG2]; push_cast; ring
    rw [eq]
    have a : ‖((w2 u : ℝ) : ℂ) * W1 (w u)‖ ≤ (A * δ * q) * (64 * A * (ρ * q)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |w2 u| ≤ A * δ * q := by rw [hq, ← div_eq_mul_inv]; exact hw2
      gcongr
    have hw1p : |w1 u + 1| ≤ 3 * A := by
      have h2 : |w1 u + 1| ≤ |w1 u| + 1 := by
        calc |w1 u + 1| ≤ |w1 u| + |(1 : ℝ)| := abs_add_le _ _
          _ = |w1 u| + 1 := by simp
      linarith
    have b : ‖((w1 u - 1 : ℝ) : ℂ) * (((w1 u + 1 : ℝ) : ℂ) * W2 (w u))‖ ≤
        (A * δ) * ((3 * A) * (64 * A * (ρ * q ^ 2))) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      gcongr
    calc _ ≤ ‖((w2 u : ℝ) : ℂ) * W1 (w u) + ((w1 u - 1 : ℝ) : ℂ) * (((w1 u + 1 : ℝ) : ℂ) * W2 (w u))‖ + ‖W2 (w u) - W2 u‖ :=
          norm_add_le _ _
      _ ≤ (‖((w2 u : ℝ) : ℂ) * W1 (w u)‖ + ‖((w1 u - 1 : ℝ) : ℂ) * (((w1 u + 1 : ℝ) : ℂ) * W2 (w u))‖) + ‖W2 (w u) - W2 u‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ ((A * δ * q) * (64 * A * (ρ * q)) + (A * δ) * ((3 * A) * (64 * A * (ρ * q ^ 2)))) +
          64 * A ^ 2 * δ * (ρ * q ^ 2) := add_le_add (add_le_add a b) hΔ2
      _ = _ := by ring
  -- the three bounds
  have hCA2 : A ^ 2 ≤ A ^ 4 := pow_le_pow_right₀ hA (by norm_num)
  have hCA3 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA (by norm_num)
  have hA4 : 0 ≤ A ^ 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- r = 0
    have hD0 : ‖Q u * G u + E u * (G u - W u)‖ ≤ (A * δ) * (64 * A * ρ) + A * (64 * A ^ 2 * (δ * ρ)) := by
      calc _ ≤ ‖Q u * G u‖ + ‖E u * (G u - W u)‖ := norm_add_le _ _
        _ ≤ _ := by
          refine add_le_add ?_ ?_
          · rw [norm_mul]; gcongr
          · rw [norm_mul]; gcongr
    calc ‖Q u * W (w u) + E u * (W (w u) - W u)‖ = ‖Q u * G u + E u * (G u - W u)‖ := rfl
      _ ≤ _ := hD0
      _ = (64 * A ^ 2 + 64 * A ^ 3) * (δ * ρ) := by ring
      _ ≤ (4096 * A ^ 4) * (δ * ρ) := by gcongr; linarith
      _ = _ := by ring
  · -- r = 1
    rw [hDder]
    have hD1b : ‖D1 u‖ ≤ (A * δ * q) * (64 * A * ρ) + (A * δ) * (128 * A ^ 2 * (ρ * q)) +
        ((A * q) * (64 * A ^ 2 * (δ * ρ)) + A * (128 * A ^ 2 * (δ * (ρ * q)))) := by
      simp only [hD1]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ((norm_add_le _ _).trans (add_le_add ?_ ?_)))
      · rw [norm_mul]; gcongr; calc ‖Q1 u‖ ≤ A * δ / m := hQ1
          _ = A * δ * q := by rw [hq, div_eq_mul_inv]
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr; calc ‖E1 u‖ ≤ A / m := hE1
          _ = A * q := by rw [hq, div_eq_mul_inv]
      · rw [norm_mul]; gcongr
    calc _ ≤ _ := hD1b
      _ = (64 * A ^ 2 + 320 * A ^ 3) * (δ * (ρ * q)) := by ring
      _ ≤ (4096 * A ^ 4) * (δ * (ρ * q)) := by gcongr; linarith
      _ = _ := by ring
  · -- r = 2
    rw [hDder2]
    have hq2 : ‖Q2 u‖ ≤ A * δ * q ^ 2 := by
      calc ‖Q2 u‖ ≤ A * δ / m ^ 2 := hQ2
        _ = A * δ * q ^ 2 := by rw [hq, div_eq_mul_inv, inv_pow]
    have hq1 : ‖Q1 u‖ ≤ A * δ * q := by
      calc ‖Q1 u‖ ≤ A * δ / m := hQ1
        _ = A * δ * q := by rw [hq, div_eq_mul_inv]
    have he2 : ‖E2 u‖ ≤ A * q ^ 2 := by
      calc ‖E2 u‖ ≤ A / m ^ 2 := hE2
        _ = A * q ^ 2 := by rw [hq, div_eq_mul_inv, inv_pow]
    have he1 : ‖E1 u‖ ≤ A * q := by
      calc ‖E1 u‖ ≤ A / m := hE1
        _ = A * q := by rw [hq, div_eq_mul_inv]
    have hD2b : ‖D2 u‖ ≤ ((A * δ * q ^ 2) * (64 * A * ρ) + (A * δ * q) * (128 * A ^ 2 * (ρ * q))) +
        ((A * δ * q) * (128 * A ^ 2 * (ρ * q)) + (A * δ) * ((256 * A ^ 3 + 64 * A ^ 2) * (ρ * q ^ 2))) +
        (((A * q ^ 2) * (64 * A ^ 2 * (δ * ρ)) + (A * q) * (128 * A ^ 2 * (δ * (ρ * q)))) +
          ((A * q) * (128 * A ^ 2 * (δ * (ρ * q))) + A * ((192 * A ^ 3 + 128 * A ^ 2) * (δ * (ρ * q ^ 2))))) := by
      simp only [hD2]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ((norm_add_le _ _).trans (add_le_add ?_ ?_))))
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ((norm_add_le _ _).trans (add_le_add ?_ ?_)))))
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
      · rw [norm_mul]; gcongr
    calc _ ≤ _ := hD2b
      _ = (64 * A ^ 2 + 768 * A ^ 3 + 448 * A ^ 4) * (δ * (ρ * q ^ 2)) := by ring
      _ ≤ (4096 * A ^ 4) * (δ * (ρ * q ^ 2)) := by gcongr; linarith
      _ = _ := by ring


/-- **`(e8)` at a point.**  Hypotheses (all pointwise at `u`, `|u| ≥ 1`, with `δ ∈ [0,1]` the size `L + ε²u²`): the symbol `W` has derivatives
`W1, W2, W3` with `‖W^{(j)}(s)‖ ≤ A|s|^{-5/2-j}` for `|s| ≥ 1/2`; the reparametrisation `w` has `|w - u| ≤ Aδ|u|`, `|w' - 1| ≤ Aδ`,
`|w''| ≤ Aδ/|u|`, `|w| ≥ |u|/2` and the sign of `u`; `Q = P - E` has `‖Q^{(j)}‖ ≤ Aδ|u|^{-j}` and `E` has `‖E^{(j)}‖ ≤ A|u|^{-j}`.
Then `𝒟 = Q W(w) + E (W(w) - W)` has `‖𝒟^{(r)}(u)‖ ≤ C δ |u|^{-5/2-r}` for `r ≤ 2`, with `C = 4096 A⁴`. -/
theorem symbol_diff_bounds (A : ℝ) (hA : 1 ≤ A) :
    ∀ {U : Set ℝ}, IsOpen U →
    ∀ {W W1 W2 W3 : ℝ → ℂ} {w w1 w2 : ℝ → ℝ} {Q Q1 Q2 E E1 E2 : ℝ → ℂ} {δ u : ℝ},
      u ∈ U → 1 ≤ |u| → 0 ≤ δ → δ ≤ 1 →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ A * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ A * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ A * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ A * |s| ^ (-(11 / 2 : ℝ))) →
      (∀ s ∈ U, HasDerivAt w (w1 s) s ∧ HasDerivAt w1 (w2 s) s) →
      (∀ s ∈ U, HasDerivAt Q (Q1 s) s ∧ HasDerivAt Q1 (Q2 s) s) →
      (∀ s ∈ U, HasDerivAt E (E1 s) s ∧ HasDerivAt E1 (E2 s) s) →
      0 < w u * u → |u| / 2 ≤ |w u| → |w u - u| ≤ A * δ * |u| → |w1 u - 1| ≤ A * δ → |w2 u| ≤ A * δ / |u| →
      ‖Q u‖ ≤ A * δ → ‖Q1 u‖ ≤ A * δ / |u| → ‖Q2 u‖ ≤ A * δ / |u| ^ 2 →
      ‖E u‖ ≤ A → ‖E1 u‖ ≤ A / |u| → ‖E2 u‖ ≤ A / |u| ^ 2 →
      ‖Q u * W (w u) + E u * (W (w u) - W u)‖ ≤ 4096 * A ^ 4 * δ * |u| ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (fun s => Q s * W (w s) + E s * (W (w s) - W s)) u‖ ≤ 4096 * A ^ 4 * δ * |u| ^ (-(7 / 2 : ℝ)) ∧
      ‖deriv (deriv (fun s => Q s * W (w s) + E s * (W (w s) - W s))) u‖ ≤ 4096 * A ^ 4 * δ * |u| ^ (-(9 / 2 : ℝ)) := by
  intro U hU W W1 W2 W3 w w1 w2 Q Q1 Q2 E E1 E2 δ u huU hu1 hδ0 hδ1 hWd hWb hwd hQd hEd hsg hw0 hw hw1 hw2 hQ0 hQ1 hQ2 hE0 hE1 hE2
  set m : ℝ := |u| with hm
  have hm0 : 0 < m := by linarith
  set ρ : ℝ := m ^ (-(5 / 2 : ℝ)) with hρ
  set q : ℝ := m⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr hm0
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ hu1
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hm0 _
  have hmq : m * q = 1 := mul_inv_cancel₀ hm0.ne'
  have e7 : m ^ (-(7 / 2 : ℝ)) = ρ * q := by
    rw [hρ, hq, show (-(7 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-1 : ℝ) by norm_num, Real.rpow_add hm0, Real.rpow_neg_one]
  have e9 : m ^ (-(9 / 2 : ℝ)) = ρ * q ^ 2 := by
    rw [hρ, hq, show (-(9 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-2 : ℝ) by norm_num, Real.rpow_add hm0]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]
  have e11 : m ^ (-(11 / 2 : ℝ)) = ρ * q ^ 3 := by
    rw [hρ, hq, show (-(11 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-3 : ℝ) by norm_num, Real.rpow_add hm0]
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]
  -- symbol bounds at points `|x| ≥ m/2`
  have hSb : ∀ x : ℝ, m / 2 ≤ |x| → ‖W x‖ ≤ 64 * A * ρ ∧ ‖W1 x‖ ≤ 64 * A * (ρ * q) ∧
      ‖W2 x‖ ≤ 64 * A * (ρ * q ^ 2) ∧ ‖W3 x‖ ≤ 64 * A * (ρ * q ^ 3) := by
    intro x hx
    have hx' : 1 / 2 ≤ |x| := by linarith
    obtain ⟨b0, b1, b2, b3⟩ := hWb x hx'
    have r0 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num)
    have r1 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num)
    have r2 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 9 / 2) (by norm_num)
    have r3 := mbd_rpow_le hm0 hx (by norm_num : (0 : ℝ) < 11 / 2) (by norm_num)
    rw [e7] at r1; rw [e9] at r2; rw [e11] at r3
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc ‖W x‖ ≤ A * |x| ^ (-(5 / 2 : ℝ)) := b0
        _ ≤ A * (64 * ρ) := by gcongr
        _ = 64 * A * ρ := by ring
    · calc ‖W1 x‖ ≤ A * |x| ^ (-(7 / 2 : ℝ)) := b1
        _ ≤ A * (64 * (ρ * q)) := by gcongr
        _ = 64 * A * (ρ * q) := by ring
    · calc ‖W2 x‖ ≤ A * |x| ^ (-(9 / 2 : ℝ)) := b2
        _ ≤ A * (64 * (ρ * q ^ 2)) := by gcongr
        _ = 64 * A * (ρ * q ^ 2) := by ring
    · calc ‖W3 x‖ ≤ A * |x| ^ (-(11 / 2 : ℝ)) := b3
        _ ≤ A * (64 * (ρ * q ^ 3)) := by gcongr
        _ = 64 * A * (ρ * q ^ 3) := by ring
  have hwm : m / 2 ≤ |w u| := hw0
  have hloc := symbol_diff_local A hA hU (W := W) (W1 := W1) (W2 := W2) (W3 := W3) (w := w) (w1 := w1) (w2 := w2)
    (Q := Q) (Q1 := Q1) (Q2 := Q2) (E := E) (E1 := E1) (E2 := E2) (δ := δ) (u := u) (ρ := ρ) (R := |u| + |w u|)
    huU (by linarith) hδ0 hδ1 hρ0 (by linarith [abs_nonneg (w u)]) (by linarith [abs_nonneg u]) hWd
    (fun x hx _ => hSb x hx) hwd hQd hEd hsg hw0 hw hw1 hw2 hQ0 hQ1 hQ2 hE0 hE1 hE2
  obtain ⟨c0, c1, c2⟩ := hloc
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ _ := c0
      _ = _ := by ring
  · calc _ ≤ _ := c1
      _ = _ := by rw [e7]; ring
  · calc _ ≤ _ := c2
      _ = _ := by rw [e9]; ring

/-- info: 'FormalResearch.SignUncertainty.symbol_diff_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.symbol_diff_local

/-- info: 'FormalResearch.SignUncertainty.symbol_diff_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.symbol_diff_bounds

end FormalResearch.SignUncertainty

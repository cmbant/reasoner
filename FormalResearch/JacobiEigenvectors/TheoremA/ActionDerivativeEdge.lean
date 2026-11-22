module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeStable

/-!
# Paper J, Layer 2: the edge limit of the action derivative (L2.E, `eq:cp-edgelim`, analytic core)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(i): `-S_0'(X_s^+) = lim_{X -> X_s^+} int_{u_-}^{u_+} du / sqrt(T) = pi sqrt(2/(kappa_+ d_+))`.  Nothing here mentions Jacobi matrices; the use is
`TheoremA/ActionDerivativeEdgeS0.lean` (`InvS0` edge values).

## Proved here

For a function `f` with a unique nondegenerate maximum `Xs = f(uc)` at an interior point (`kappa = -f''(uc) > 0`, `f` `C^2` near `uc`) and a continuous `f_m` with `f_m(uc) < f(uc)`:

* `peano2`: `f(uc + w) = Xs - (kappa/2) w^2 + o(w^2)` (two mean value theorems; `C^2` with `f''` continuous at `uc`).
* `chord_lower`, `T_lower`: for the turning points `f(a) = f(b) = X`, `f(u) - X >= (c/2)(u - a)(b - u)` when `f'' <= -c` on `[a, b]`; hence `(f - X)(X - f_m) >= (kappa d/8)(u - a)(b - u)`.
* `alg_core`, `pointwise_limit`: `(f(a + (b - a) s) - X)/(b - a)^2 -> (kappa/2) s (1 - s)` as the turning points collapse (the symmetry `(uc - a)/(b - a) -> 1/2` is derived from `f(a) = f(b)`).
* `edge_integral_tendsto`: `int_a^b du / sqrt((f - X)(X - f_m)) -> pi sqrt(2/(kappa d))` (substitution `u = a + (b - a) s`, dominated convergence with the bound `C/sqrt(s (1 - s))`, `int_0^1 ds/sqrt(s(1-s)) = pi`, `integral_inv_sqrt_unit`).
* `far_gap`, `edge_structure`, `edge_wrapper`: from the structure `(H2)` of the allowed set (an interval `[a, b]` whose interior end points are simple zeros of `T`) to the turning points `a(X) < uc < b(X)`, `f(a) = f(b) = X`, `a, b -> uc`, and the limit of `int_{u_-}^{u_+} T^{-1/2} du` with `u_pm = inf/sup` of the allowed set.

## Differences from the paper

The paper substitutes `tau = sqrt(alpha) s` in the original variable with the dominating function `C/sqrt(1 - s^2)`; here the turning-point substitution `u = a + (b - a) s` gives the dominating function directly from the chord bound, and only `f in C^2`
near `uc` is used (no Morse coordinate).

## Not formalised

Rates (the paper does not need them).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv

open Set Filter Topology MeasureTheory
open scoped Interval

section Peano

variable {f f1 f2 : ℝ → ℝ} {uc Xs κ r0 : ℝ}

/-- Second-order Taylor (Peano) at a nondegenerate maximum: `f(uc + w) = Xs - (kappa/2) w^2 + o(w^2)`. -/
lemma peano2 (hr0 : 0 < r0) (hf : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f (f1 u) u)
    (hf1 : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f1 (f2 u) u) (hf2 : ContinuousAt f2 uc)
    (h0 : f uc = Xs) (h1 : f1 uc = 0) (h2 : f2 uc = -κ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (0 : ℝ), |f (uc + w) - Xs + (κ / 2) * w ^ 2| ≤ ε * w ^ 2 := by
  have hc : ∀ᶠ w in 𝓝 (0 : ℝ), |f2 (uc + w) + κ| ≤ ε := by
    have : Tendsto (fun w : ℝ => f2 (uc + w) + κ) (𝓝 0) (𝓝 0) := by
      have hu : Tendsto (fun w : ℝ => uc + w) (𝓝 0) (𝓝 uc) := by
        simpa using (tendsto_const_nhds (x := uc)).add (tendsto_id (α := ℝ) (x := 𝓝 (0 : ℝ)))
      have h := (hf2.tendsto.comp hu).add_const κ
      simpa [h2] using h
    exact (Metric.tendsto_nhds.1 this ε hε).mono fun w hw => by simpa using hw.le
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.and (Metric.ball_mem_nhds (0 : ℝ) hr0))
  -- on the ball of radius `ρ' = min ρ r0`
  refine Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun w hw => ?_⟩
  have hw' : |w| < ρ := by simpa using hw
  have hmem : ∀ v ∈ uIcc (0 : ℝ) w, |v| ≤ |w| := by
    intro v hv
    rcases le_total 0 w with h | h
    · rw [uIcc_of_le h] at hv; rw [abs_of_nonneg hv.1, abs_of_nonneg h]; exact hv.2
    · rw [uIcc_of_ge h] at hv; rw [abs_of_nonpos hv.2, abs_of_nonpos h]; linarith [hv.1]
  have hbd : ∀ v : ℝ, |v| < ρ → |f2 (uc + v) + κ| ≤ ε ∧ v ∈ Icc (-r0) r0 := by
    intro v hv
    have := hball (y := v) (by simpa using hv)
    exact ⟨this.1, by have := this.2; rw [Real.dist_eq, sub_zero] at this; exact abs_le.1 this.le⟩
  -- derivative of `g v = f1 (uc + v) + kappa * v`
  have hg : ∀ v ∈ uIcc (0 : ℝ) w, HasDerivWithinAt (fun v => f1 (uc + v) + κ * v) (f2 (uc + v) + κ) (uIcc (0 : ℝ) w) v := by
    intro v hv
    have hv' := (hbd v ((hmem v hv).trans_lt hw')).2
    have h := (hf1 (uc + v) ⟨by linarith [hv'.1], by linarith [hv'.2]⟩)
    have h' : HasDerivAt (fun v => f1 (uc + v) + κ * v) (f2 (uc + v) + κ) v := by
      have := (h.comp_const_add uc v).add ((hasDerivAt_id v).const_mul κ)
      convert this using 1
      · ext x; simp
      · simp
    exact h'.hasDerivWithinAt
  have hgb : ∀ v ∈ uIcc (0 : ℝ) w, |f1 (uc + v) + κ * v| ≤ ε * |w| := by
    intro v hv
    have hsub : uIcc (0 : ℝ) v ⊆ uIcc (0 : ℝ) w := by
      refine uIcc_subset_uIcc (left_mem_uIcc) hv
    have hgv : ∀ x ∈ uIcc (0 : ℝ) v, HasDerivWithinAt (fun v => f1 (uc + v) + κ * v) (f2 (uc + x) + κ) (uIcc (0 : ℝ) v) x :=
      fun x hx => (hg x (hsub hx)).mono hsub
    have hbound : ∀ x ∈ uIcc (0 : ℝ) v, ‖f2 (uc + x) + κ‖ ≤ ε := fun x hx =>
      (hbd x ((hmem x (hsub hx)).trans_lt hw')).1
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hgv hbound (convex_uIcc 0 v) left_mem_uIcc right_mem_uIcc
    simp only [add_zero, mul_zero, h1, sub_zero, Real.norm_eq_abs] at this
    calc |f1 (uc + v) + κ * v| ≤ ε * |v| := by simpa [h1] using this
      _ ≤ ε * |w| := mul_le_mul_of_nonneg_left (hmem v hv) hε.le
  have hψ : ∀ v ∈ uIcc (0 : ℝ) w, HasDerivWithinAt (fun v => f (uc + v) - Xs + (κ / 2) * v ^ 2) (f1 (uc + v) + κ * v) (uIcc (0 : ℝ) w) v := by
    intro v hv
    have hv' := (hbd v ((hmem v hv).trans_lt hw')).2
    have h := (hf (uc + v) ⟨by linarith [hv'.1], by linarith [hv'.2]⟩).comp_const_add uc v
    have h' : HasDerivAt (fun v => f (uc + v) - Xs + (κ / 2) * v ^ 2) (f1 (uc + v) + κ * v) v := by
      have := (h.sub_const Xs).add (((hasDerivAt_pow 2 v).const_mul (κ / 2)))
      convert this using 1
      push_cast; ring
    exact h'.hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hψ (fun v hv => by simpa [Real.norm_eq_abs] using hgb v hv)
    (convex_uIcc 0 w) left_mem_uIcc right_mem_uIcc
  simp only [add_zero, h0, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
    Real.norm_eq_abs] at this
  calc |f (uc + w) - Xs + (κ / 2) * w ^ 2| ≤ ε * |w| * |w| := by simpa using this
    _ = ε * w ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end Peano

section Concave

variable {f f1 f2 : ℝ → ℝ} {c : ℝ}

/-- Chord bound for a function with `f'' <= -c` on `[a, b]` and `f a = f b = X`: `f u - X >= (c/2)(u - a)(b - u)`. -/
lemma chord_lower {a b X : ℝ} (hab : a < b)
    (hf : ∀ u ∈ Icc a b, HasDerivAt f (f1 u) u) (hf1 : ∀ u ∈ Icc a b, HasDerivAt f1 (f2 u) u) (hf2 : ∀ u ∈ Icc a b, f2 u ≤ -c)
    (hfa : f a = X) (hfb : f b = X) {u : ℝ} (hu : u ∈ Icc a b) : (c / 2) * ((u - a) * (b - u)) ≤ f u - X := by
  have hψ : ConcaveOn ℝ (Icc a b) (fun u => f u + (c / 2) * u ^ 2) := by
    have hderiv : ∀ x ∈ Icc a b, HasDerivAt (fun u => f u + (c / 2) * u ^ 2) (f1 x + c * x) x := by
      intro x hx
      have := (hf x hx).add (((hasDerivAt_pow 2 x).const_mul (c / 2)))
      convert this using 1
      push_cast; ring
    have hanti : AntitoneOn (fun x => f1 x + c * x) (Ioo a b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioo a b) ?_ ?_ ?_
      · intro x hx
        exact (((hf1 x (Ioo_subset_Icc_self hx)).add ((hasDerivAt_id x).const_mul c)).continuousAt).continuousWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        exact (((hf1 x (Ioo_subset_Icc_self hx)).add ((hasDerivAt_id x).const_mul c)).differentiableAt).differentiableWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        have h : HasDerivAt (fun x => f1 x + c * x) (f2 x + c) x := by
          have := ((hf1 x (Ioo_subset_Icc_self hx)).add ((hasDerivAt_id x).const_mul c))
          convert this using 1
          · ext y; simp
          · simp
        rw [h.deriv]
        have := hf2 x (Ioo_subset_Icc_self hx)
        linarith
    refine AntitoneOn.concaveOn_of_deriv (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      rw [interior_Icc] at hx hy
      show deriv _ y ≤ deriv _ x
      rw [(hderiv x (Ioo_subset_Icc_self hx)).deriv, (hderiv y (Ioo_subset_Icc_self hy)).deriv]
      exact hanti hx hy hxy
  have hba : 0 < b - a := sub_pos.2 hab
  set s := (u - a) / (b - a) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith [hu.1]) hba.le
  have hs1 : s ≤ 1 := (div_le_one hba).2 (by linarith [hu.2])
  have hu' : u = (1 - s) * a + s * b := by
    rw [hs]; field_simp; ring
  have h := hψ.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) (by linarith : 0 ≤ 1 - s) hs0 (by ring)
  simp only [smul_eq_mul] at h
  rw [← hu', hfa, hfb] at h
  have e : (1 - s) * (a ^ 2) + s * (b ^ 2) - u ^ 2 = (u - a) * (b - u) := by
    rw [hu']; ring
  have e2 := congrArg (fun t => c / 2 * t) e
  nlinarith [e2, h]

end Concave

section Pointwise

/-- The real-number core of the edge asymptotics. -/
lemma alg_core {κ ε Xs fa fb fu σ τ s δ w : ℝ} (hδ : δ = σ + τ) (hw : w = δ * s - σ) (hκ : 0 < κ) (hε : 0 < ε) (hσ : 0 < σ) (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (Pa : |fa - Xs + (κ / 2) * σ ^ 2| ≤ ε * σ ^ 2) (Pb : |fb - Xs + (κ / 2) * τ ^ 2| ≤ ε * τ ^ 2) (hab : fa = fb)
    (Pu : |fu - Xs + (κ / 2) * w ^ 2| ≤ ε * w ^ 2) :
    |(fu - fa) / δ ^ 2 - (κ / 2) * (s * (1 - s))| ≤ 3 * ε := by
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hw1 : -σ ≤ w := by rw [hw]; nlinarith
  have hw2 : w ≤ τ := by rw [hw, hδ]; nlinarith
  have hwδ : w ^ 2 ≤ δ ^ 2 := by nlinarith
  have hσδ : σ ^ 2 ≤ δ ^ 2 := by nlinarith
  have hτδ : τ ^ 2 ≤ δ ^ 2 := by nlinarith
  obtain ⟨ea, hea⟩ : ∃ ea, ea = fa - Xs + (κ / 2) * σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨eb, heb⟩ : ∃ eb, eb = fb - Xs + (κ / 2) * τ ^ 2 := ⟨_, rfl⟩
  obtain ⟨eu, heu⟩ : ∃ eu, eu = fu - Xs + (κ / 2) * w ^ 2 := ⟨_, rfl⟩
  rw [← hea] at Pa
  rw [← heb] at Pb
  rw [← heu] at Pu
  have h1 : (κ / 2) * (τ ^ 2 - σ ^ 2) = eb - ea := by
    have : fa = fb := hab
    rw [hea, heb, this]; ring
  have h2 : |eb - ea| ≤ ε * δ ^ 2 := by
    have := abs_sub (eb) (ea)
    have h3 : |eb| + |ea| ≤ ε * τ ^ 2 + ε * σ ^ 2 := add_le_add Pb Pa
    calc |eb - ea| ≤ |eb| + |ea| := abs_sub _ _
      _ ≤ ε * τ ^ 2 + ε * σ ^ 2 := h3
      _ ≤ ε * δ ^ 2 := by
          have : τ ^ 2 + σ ^ 2 ≤ δ ^ 2 := by rw [hδ]; nlinarith [mul_pos hσ hτ]
          nlinarith [mul_le_mul_of_nonneg_left this hε.le]
  have h4 : (κ / 2) * (|τ - σ| * δ) ≤ ε * δ ^ 2 := by
    have : τ ^ 2 - σ ^ 2 = (τ - σ) * δ := by rw [hδ]; ring
    rw [this] at h1
    have h5 : |(κ / 2) * ((τ - σ) * δ)| = (κ / 2) * (|τ - σ| * δ) := by
      rw [abs_mul, abs_mul, abs_of_pos hδp, abs_of_pos (by positivity : 0 < κ / 2)]
    rw [← h5, h1]
    exact h2
  have h6 : |τ - σ| ≤ 2 * ε / κ * δ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith [mul_pos hδp hκ]
  have key : (fu - fa) - (κ / 2) * (s * (1 - s)) * δ ^ 2 = (κ / 2) * s * δ * (σ - τ) + (eu - ea) := by
    have e1 : fu = eu + Xs - (κ / 2) * w ^ 2 := by rw [heu]; ring
    have e2 : fa = ea + Xs - (κ / 2) * σ ^ 2 := by rw [hea]; ring
    rw [e1, e2, hw]
    have : τ = δ - σ := by rw [hδ]; ring
    rw [this]; ring
  have h7 : |(κ / 2) * s * δ * (σ - τ)| ≤ ε * δ ^ 2 := by
    have : |σ - τ| = |τ - σ| := abs_sub_comm _ _
    rw [abs_mul, this, abs_of_nonneg (by positivity : 0 ≤ (κ / 2) * s * δ)]
    calc (κ / 2) * s * δ * |τ - σ| ≤ (κ / 2) * 1 * δ * (2 * ε / κ * δ) := by
          apply mul_le_mul (by nlinarith [hδp, hκ]) h6 (abs_nonneg _) (by positivity)
      _ = ε * δ ^ 2 := by field_simp
  have h8 : |eu - ea| ≤ 2 * ε * δ ^ 2 := by
    calc |eu - ea| ≤ |eu| + |ea| := abs_sub _ _
      _ ≤ ε * w ^ 2 + ε * σ ^ 2 := add_le_add Pu Pa
      _ ≤ 2 * ε * δ ^ 2 := by
          have := add_le_add (mul_le_mul_of_nonneg_left hwδ hε.le) (mul_le_mul_of_nonneg_left hσδ hε.le)
          linarith
  have h9 : |(fu - fa) - (κ / 2) * (s * (1 - s)) * δ ^ 2| ≤ 3 * ε * δ ^ 2 := by
    rw [key]
    calc |(κ / 2) * s * δ * (σ - τ) + (eu - ea)| ≤ |(κ / 2) * s * δ * (σ - τ)| + |eu - ea| := abs_add_le _ _
      _ ≤ 3 * ε * δ ^ 2 := by linarith
  have h10 : (fu - fa) / δ ^ 2 - (κ / 2) * (s * (1 - s)) = ((fu - fa) - (κ / 2) * (s * (1 - s)) * δ ^ 2) / δ ^ 2 := by
    field_simp
  rw [h10, abs_div, abs_of_pos (by positivity : 0 < δ ^ 2), div_le_iff₀ (by positivity)]
  exact h9

end Pointwise

section PointwiseLimit

variable {f f1 f2 : ℝ → ℝ} {uc Xs κ r0 : ℝ} {l : Filter ℝ}

/-- For the turning points `a(X) < uc < b(X)` of `f = X` collapsing to `uc`, `(f(a + (b - a) s) - X)/(b - a)^2 -> (kappa/2) s (1 - s)`. -/
lemma pointwise_limit (hr0 : 0 < r0) (hf : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f (f1 u) u)
    (hf1 : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f1 (f2 u) u) (hf2 : ContinuousAt f2 uc)
    (h0 : f uc = Xs) (h1 : f1 uc = 0) (h2 : f2 uc = -κ) (hκ : 0 < κ) {a b : ℝ → ℝ}
    (hev : ∀ᶠ X in l, a X < uc ∧ uc < b X ∧ f (a X) = X ∧ f (b X) = X)
    (ha : Tendsto a l (𝓝 uc)) (hb : Tendsto b l (𝓝 uc)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Tendsto (fun X => (f (a X + (b X - a X) * s) - X) / (b X - a X) ^ 2) l (𝓝 ((κ / 2) * (s * (1 - s)))) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  have hε : 0 < ε' / 4 := by positivity
  have hP := peano2 hr0 hf hf1 hf2 h0 h1 h2 hε
  have ta : Tendsto (fun X => a X - uc) l (𝓝 0) := by simpa using ha.sub_const uc
  have tb : Tendsto (fun X => b X - uc) l (𝓝 0) := by simpa using hb.sub_const uc
  have tu : Tendsto (fun X => a X + (b X - a X) * s - uc) l (𝓝 0) := by
    have := (ha.add ((hb.sub ha).mul_const s)).sub_const uc
    simpa using this
  filter_upwards [hev, ta.eventually hP, tb.eventually hP, tu.eventually hP] with X ⟨hau, hub, hfa, hfb⟩ Pa Pb Pu
  have hσ : 0 < uc - a X := by linarith
  have hτ : 0 < b X - uc := by linarith
  rw [Real.dist_eq]
  have e1 : uc + (a X - uc) = a X := by ring
  have e2 : uc + (b X - uc) = b X := by ring
  have e3 : uc + (a X + (b X - a X) * s - uc) = a X + (b X - a X) * s := by ring
  rw [e1, hfa] at Pa
  rw [e2, hfb] at Pb
  rw [e3] at Pu
  have hmain := alg_core (κ := κ) (ε := ε' / 4) (Xs := Xs) (fa := X) (fb := X) (fu := f (a X + (b X - a X) * s))
    (σ := uc - a X) (τ := b X - uc) (s := s) (δ := b X - a X) (w := a X + (b X - a X) * s - uc) (by ring) (by ring) hκ hε hσ hτ hs0 hs1
    (by rw [show (uc - a X) ^ 2 = (a X - uc) ^ 2 by ring]; exact Pa) Pb rfl Pu
  calc |(f (a X + (b X - a X) * s) - X) / (b X - a X) ^ 2 - (κ / 2) * (s * (1 - s))| ≤ 3 * (ε' / 4) := hmain
    _ < ε' := by linarith

end PointwiseLimit

/-- `int_0^1 ds / sqrt(s (1 - s)) = pi`. -/
lemma integral_inv_sqrt_unit : ∫ s in (0 : ℝ)..1, (Real.sqrt (s * (1 - s)))⁻¹ = Real.pi := by
  have hcont : ContinuousOn (fun u : ℝ => Real.arcsin (2 * u - 1)) (Icc 0 1) :=
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
  have hint : IntervalIntegrable (fun s : ℝ => (Real.sqrt (s * (1 - s)))⁻¹) volume 0 1 := by
    have := intervalIntegrable_inv_sqrt (a := 0) (b := 1) zero_lt_one
    simpa using this
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun u : ℝ => Real.arcsin (2 * u - 1))
    (f' := fun s : ℝ => (Real.sqrt (s * (1 - s)))⁻¹) zero_le_one hcont ?_ hint
  · rw [h]
    have e1 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
    have e0 : (2 : ℝ) * 0 - 1 = -1 := by norm_num
    rw [e1, e0, Real.arcsin_one, Real.arcsin_neg_one]
    ring
  · intro u hu
    have hw : HasDerivAt (fun u : ℝ => 2 * u - 1) 2 u := by
      simpa using (((hasDerivAt_id u).const_mul 2).sub_const 1)
    have h1 : 2 * u - 1 ≠ -1 := by intro h; linarith [hu.1]
    have h2 : 2 * u - 1 ≠ 1 := by intro h; linarith [hu.2]
    have := (Real.hasDerivAt_arcsin h1 h2).comp u hw
    refine this.congr_deriv ?_
    have hpos : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
    have e : 1 - (2 * u - 1) ^ 2 = 4 * (u * (1 - u)) := by ring
    rw [e, Real.sqrt_mul (by norm_num)]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [h4]
    have hs : 0 < Real.sqrt (u * (1 - u)) := Real.sqrt_pos.2 hpos
    field_simp

section Edge0

variable {f f1 f2 fm : ℝ → ℝ} {uc κ r0 d : ℝ}

/-- The Hadamard lower bound `T >= (kappa d/8)(u - a)(b - u)` on `[a, b]`. -/
lemma T_lower (hf : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f (f1 u) u)
    (hf1 : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f1 (f2 u) u)
    (hf2le : ∀ u ∈ Icc (uc - r0) (uc + r0), f2 u ≤ -(κ / 2)) (hκ : 0 < κ) (hd : 0 < d)
    {a b X : ℝ} (hab : a < b) (hfa : f a = X) (hfb : f b = X) (hball : Icc a b ⊆ Icc (uc - r0) (uc + r0))
    (hQ : ∀ u ∈ Icc a b, d / 2 ≤ X - fm u) {u : ℝ} (hu : u ∈ Icc a b) :
    (κ * d / 8) * ((u - a) * (b - u)) ≤ (f u - X) * (X - fm u) := by
  have h := chord_lower (c := κ / 2) hab (fun v hv => hf v (hball hv)) (fun v hv => hf1 v (hball hv))
    (fun v hv => hf2le v (hball hv)) hfa hfb hu
  have hP : 0 ≤ (u - a) * (b - u) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
  have hq := hQ u hu
  have h1 : κ / 2 / 2 * ((u - a) * (b - u)) = κ / 4 * ((u - a) * (b - u)) := by ring
  have h2 : 0 ≤ κ / 4 * ((u - a) * (b - u)) := by positivity
  calc (κ * d / 8) * ((u - a) * (b - u)) = (κ / 4 * ((u - a) * (b - u))) * (d / 2) := by ring
    _ ≤ (f u - X) * (X - fm u) := mul_le_mul (by linarith) hq (by linarith) (by linarith)

end Edge0

section Edge

variable {f f1 f2 fm : ℝ → ℝ} {uc Xs κ r0 : ℝ}

/-- **The edge limit** `int_{a(X)}^{b(X)} du / sqrt((f - X)(X - f_-)) -> pi sqrt(2/(kappa d))` as `X` increases to `X_s = f(uc)` (`kappa = -f''(uc)`, `d = X_s - f_-(uc)`), for the
turning points `a(X) < uc < b(X)` of `f = X`.  Substitution `u = a + (b - a) s`; the pointwise limit of `T/(b - a)^2` is `(kappa d/2) s (1 - s)` (`pointwise_limit`) and the
dominating function `C / sqrt(s (1 - s))` comes from the chord bound `chord_lower`. -/
theorem edge_integral_tendsto {l : Filter ℝ} [l.IsCountablyGenerated] (hr0 : 0 < r0)
    (hf : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f (f1 u) u)
    (hf1 : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f1 (f2 u) u) (hf2c : ContinuousAt f2 uc)
    (hf2le : ∀ u ∈ Icc (uc - r0) (uc + r0), f2 u ≤ -(κ / 2))
    (h0 : f uc = Xs) (h1 : f1 uc = 0) (h2 : f2 uc = -κ) (hκ : 0 < κ)
    (hfm : ContinuousOn fm (Icc (uc - r0) (uc + r0))) (hd : 0 < Xs - fm uc) (hl : Tendsto (fun X : ℝ => X) l (𝓝 Xs))
    {a b : ℝ → ℝ} (hev : ∀ᶠ X in l, a X < uc ∧ uc < b X ∧ f (a X) = X ∧ f (b X) = X)
    (ha : Tendsto a l (𝓝 uc)) (hb : Tendsto b l (𝓝 uc)) :
    Tendsto (fun X => ∫ u in (a X)..(b X), 1 / Real.sqrt ((f u - X) * (X - fm u))) l
      (𝓝 (Real.pi * Real.sqrt (2 / (κ * (Xs - fm uc))))) := by
  set d := Xs - fm uc with hdd
  have hfmc : ContinuousAt fm uc := hfm.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  -- uniform facts on `[a, b]`
  have hQ : ∀ᶠ X in l, ∀ u ∈ Icc (a X) (b X), d / 2 ≤ X - fm u ∧ u ∈ Icc (uc - r0) (uc + r0) := by
    obtain ⟨r1, hr1, hfr⟩ := Metric.eventually_nhds_iff.1 (hfmc.eventually (eventually_lt_nhds (show fm uc < fm uc + d / 4 by linarith)))
    have hrr : 0 < min r1 r0 := lt_min hr1 hr0
    filter_upwards [ha.eventually (Metric.ball_mem_nhds uc hrr), hb.eventually (Metric.ball_mem_nhds uc hrr),
      hl.eventually (eventually_ge_nhds (show Xs - d / 4 < Xs by linarith))] with X hXa hXb hXs u hu
    rw [Real.dist_eq, abs_lt] at hXa hXb
    have hm1 := min_le_left r1 r0
    have hm2 := min_le_right r1 r0
    have hu1 : dist u uc < r1 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2, hXa.1, hXb.2]
    have := hfr hu1
    refine ⟨by linarith, by linarith [hu.1, hXa.1], by linarith [hu.2, hXb.2]⟩
  have hδ : ∀ᶠ X in l, 0 < b X - a X := by
    filter_upwards [hev] with X hX using by linarith [hX.1, hX.2.1]
  -- representation
  have hrep : ∀ X, a X ≤ b X → ∫ u in (a X)..(b X), 1 / Real.sqrt ((f u - X) * (X - fm u)) =
      ∫ s in (0 : ℝ)..1, (b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)))) := by
    intro X hX
    have := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (f := fun u => 1 / Real.sqrt ((f u - X) * (X - fm u))) (b X - a X) (a X)
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at this
    rw [← this, intervalIntegral.integral_const_mul]
  -- the limit integral
  have hKpos : 0 < κ * d / 2 := by positivity
  have hlimint : ∫ s in (0 : ℝ)..1, (Real.sqrt (κ * d / 2 * (s * (1 - s))))⁻¹ = Real.pi * Real.sqrt (2 / (κ * d)) := by
    have h1 : ∀ s : ℝ, (Real.sqrt (κ * d / 2 * (s * (1 - s))))⁻¹ = (Real.sqrt (κ * d / 2))⁻¹ * (Real.sqrt (s * (1 - s)))⁻¹ := by
      intro s
      rw [Real.sqrt_mul hKpos.le, mul_inv]
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_unit]
    have : 2 / (κ * d) = (κ * d / 2)⁻¹ := by field_simp
    rw [this, Real.sqrt_inv]
    ring
  rw [← hlimint]
  have hall : ∀ᶠ X in l, (a X < uc ∧ uc < b X ∧ f (a X) = X ∧ f (b X) = X) ∧
      (∀ u ∈ Icc (a X) (b X), d / 2 ≤ X - fm u ∧ u ∈ Icc (uc - r0) (uc + r0)) ∧ 0 < b X - a X := by
    filter_upwards [hev, hQ, hδ] with X h1 h2 h3 using ⟨h1, h2, h3⟩
  -- pointwise bound for each good `X`
  have hTb : ∀ X, (a X < uc ∧ uc < b X ∧ f (a X) = X ∧ f (b X) = X) →
      (∀ u ∈ Icc (a X) (b X), d / 2 ≤ X - fm u ∧ u ∈ Icc (uc - r0) (uc + r0)) →
      ∀ s ∈ Ioo (0 : ℝ) 1, (κ * d / 8) * ((b X - a X) ^ 2 * (s * (1 - s))) ≤
        (f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)) := by
    intro X ⟨hau, hub, hfa, hfb⟩ hQX s hs
    have hw : 0 < b X - a X := by linarith
    have huI : (b X - a X) * s + a X ∈ Icc (a X) (b X) := ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have := T_lower hf hf1 hf2le hκ hd (a := a X) (b := b X) (X := X) (by linarith) hfa hfb
      (fun u hu => (hQX u hu).2) (fun u hu => (hQX u hu).1) huI
    have e : ((b X - a X) * s + a X - a X) * (b X - ((b X - a X) * s + a X)) = (b X - a X) ^ 2 * (s * (1 - s)) := by ring
    rwa [e] at this
  have hmeas : ∀ᶠ X in l, AEStronglyMeasurable
      (fun s => (b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)))))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [hall] with X ⟨h1, hQX, hw⟩
    have hmaps : MapsTo (fun s : ℝ => (b X - a X) * s + a X) (Ioo 0 1) (Icc (a X) (b X)) := by
      intro s hs
      exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have hcf : ContinuousOn (fun u => f u) (Icc (a X) (b X)) := fun u hu =>
      (hf u (hQX u hu).2).continuousAt.continuousWithinAt
    have hcm : ContinuousOn fm (Icc (a X) (b X)) := hfm.mono (fun u hu => (hQX u hu).2)
    have hcon : ContinuousOn (fun s : ℝ => (b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) *
        (X - fm ((b X - a X) * s + a X))))) (Ioo 0 1) := by
      refine continuousOn_const.mul ?_
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · refine Real.continuous_sqrt.comp_continuousOn ?_
        exact ((hcf.comp (by fun_prop) hmaps).sub continuousOn_const).mul (continuousOn_const.sub (hcm.comp (by fun_prop) hmaps))
      · intro s hs
        have := hTb X h1 hQX s hs
        have hp : 0 < (κ * d / 8) * ((b X - a X) ^ 2 * (s * (1 - s))) := by
          have := mul_pos hs.1 (by linarith [hs.2] : 0 < 1 - s)
          positivity
        exact (Real.sqrt_pos.2 (lt_of_lt_of_le hp this)).ne'
    have h1 := hcon.aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← Set.uIoc_of_le zero_le_one] at h1
  have hbd : ∀ᶠ X in l, ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 →
      ‖(b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X))))‖ ≤
        (Real.sqrt (κ * d / 8))⁻¹ * (Real.sqrt ((s - 0) * (1 - s)))⁻¹ := by
    filter_upwards [hall] with X ⟨h1, hQX, hw⟩
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs1' : s < 1 := lt_of_le_of_ne hsI.2 (fun h => hs1 (by simp [h]))
    have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hsI.1, hs1'⟩
    have hT := hTb X h1 hQX s hs'
    have hsP : 0 < s * (1 - s) := mul_pos hs'.1 (by linarith)
    have hK : 0 < κ * d / 8 := by positivity
    set w := b X - a X with hwdef
    have hsq1 : Real.sqrt (κ * d / 8) * (w * Real.sqrt (s * (1 - s))) ≤ Real.sqrt ((f ((b X - a X) * s + a X) - X) *
        (X - fm ((b X - a X) * s + a X))) := by
      have : Real.sqrt ((κ * d / 8) * (w ^ 2 * (s * (1 - s)))) = Real.sqrt (κ * d / 8) * (w * Real.sqrt (s * (1 - s))) := by
        rw [Real.sqrt_mul hK.le, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw.le]
      rw [← this]
      exact Real.sqrt_le_sqrt hT
    have hss : 0 < Real.sqrt (s * (1 - s)) := Real.sqrt_pos.2 hsP
    have hsk : 0 < Real.sqrt (κ * d / 8) := Real.sqrt_pos.2 hK
    have hpos : 0 < Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X))) :=
      lt_of_lt_of_le (by positivity) hsq1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sub_zero]
    calc w * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X))))
        ≤ w * (1 / (Real.sqrt (κ * d / 8) * (w * Real.sqrt (s * (1 - s))))) := by
          apply mul_le_mul_of_nonneg_left _ hw.le
          exact one_div_le_one_div_of_le (by positivity) hsq1
      _ = (Real.sqrt (κ * d / 8))⁻¹ * (Real.sqrt (s * (1 - s)))⁻¹ := by field_simp
  have hbint : IntervalIntegrable (fun s : ℝ => (Real.sqrt (κ * d / 8))⁻¹ * (Real.sqrt ((s - 0) * (1 - s)))⁻¹) volume 0 1 :=
    (intervalIntegrable_inv_sqrt zero_lt_one).const_mul _
  have hlim : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 → Tendsto (fun X => (b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) *
      (X - fm ((b X - a X) * s + a X))))) l (𝓝 ((Real.sqrt (κ * d / 2 * (s * (1 - s))))⁻¹)) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with s hs1 hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs1' : s < 1 := lt_of_le_of_ne hsI.2 (fun h => hs1 (by simp [h]))
    have hsP : 0 < s * (1 - s) := mul_pos hsI.1 (by linarith)
    have hpt := pointwise_limit hr0 hf hf1 hf2c h0 h1 h2 hκ hev ha hb hsI.1.le hs1'.le
    have hu : Tendsto (fun X => (b X - a X) * s + a X) l (𝓝 uc) := by
      have := ((hb.sub ha).mul_const s).add ha
      simpa using this
    have hq : Tendsto (fun X => X - fm ((b X - a X) * s + a X)) l (𝓝 d) :=
      hl.sub (hfmc.tendsto.comp hu)
    have hprod := hpt.mul hq
    have hlimval : (κ / 2) * (s * (1 - s)) * d = κ * d / 2 * (s * (1 - s)) := by ring
    rw [hlimval] at hprod
    have hne : 0 < κ * d / 2 * (s * (1 - s)) := by positivity
    have hsqrt := (hprod.sqrt).inv₀ (Real.sqrt_pos.2 hne).ne'
    refine hsqrt.congr' ?_
    filter_upwards [hall] with X ⟨h1, hQX, hw⟩
    have e1 : (b X - a X) * s + a X - a X = (b X - a X) * s := by ring
    have hT : 0 ≤ (f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)) := by
      have := hTb X h1 hQX s ⟨hsI.1, hs1'⟩
      have hp : 0 ≤ (κ * d / 8) * ((b X - a X) ^ 2 * (s * (1 - s))) := by positivity
      linarith
    have : (f ((b X - a X) * s + a X) - X) / (b X - a X) ^ 2 * (X - fm ((b X - a X) * s + a X)) =
        (f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)) / (b X - a X) ^ 2 := by ring
    rw [show a X + (b X - a X) * s = (b X - a X) * s + a X by ring, this, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hw.le]
    have hpos : 0 < Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X))) := by
      have := hTb X h1 hQX s ⟨hsI.1, hs1'⟩
      have hp : 0 < (κ * d / 8) * ((b X - a X) ^ 2 * (s * (1 - s))) := by positivity
      exact Real.sqrt_pos.2 (lt_of_lt_of_le hp this)
    field_simp
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := l) (a := 0) (b := 1)
    (F := fun X s => (b X - a X) * (1 / Real.sqrt ((f ((b X - a X) * s + a X) - X) * (X - fm ((b X - a X) * s + a X)))))
    (f := fun s => (Real.sqrt (κ * d / 2 * (s * (1 - s))))⁻¹)
    (fun s : ℝ => (Real.sqrt (κ * d / 8))⁻¹ * (Real.sqrt ((s - 0) * (1 - s)))⁻¹) hmeas hbd hbint hlim
  refine hDCT.congr' ?_
  filter_upwards [hδ] with X hX
  exact (hrep X (by linarith)).symm

end Edge

section Wrapper

/-- Compactness: away from the unique maximiser `uc` the function stays a definite amount below its maximum. -/
lemma far_gap {L : ℝ} {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 L)) {uc Xs : ℝ}
    (hmax : ∀ u ∈ Icc 0 L, f u ≤ Xs) (huniq : ∀ u ∈ Icc 0 L, f u = Xs → u = uc) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ u ∈ Icc 0 L, ρ ≤ |u - uc| → f u ≤ Xs - ν := by
  set C := Icc 0 L ∩ {u | ρ ≤ |u - uc|} with hC
  have hCc : IsCompact C := isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  rcases C.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, fun u hu hu' => by
      have : u ∈ C := ⟨hu, hu'⟩
      rw [hE] at this
      exact absurd this (notMem_empty u)⟩
  · obtain ⟨u0, hu0, hmaxC⟩ := hCc.exists_isMaxOn hne (hc.mono inter_subset_left)
    have hlt : f u0 < Xs := by
      refine lt_of_le_of_ne (hmax u0 hu0.1) (fun h => ?_)
      have := huniq u0 hu0.1 h
      have h2 : ρ ≤ |u0 - uc| := hu0.2
      rw [this, sub_self, abs_zero] at h2
      linarith
    refine ⟨Xs - f u0, by linarith, fun u hu hu' => ?_⟩
    have : f u ≤ f u0 := hmaxC (show u ∈ C from ⟨hu, hu'⟩)
    linarith

end Wrapper

section Structure

variable {L : ℝ} {f fm : ℝ → ℝ} {T : ℝ → ℝ → ℝ} {uc Xs : ℝ}

/-- The allowed set `[a, b]` near the fold: for `X < Xs` close to `Xs` its end points are the turning points of `f = X` on both sides of `uc`, within `rho` of `uc`. -/
lemma edge_structure (hT : ∀ X, ∀ u ∈ Icc 0 L, T X u = (f u - X) * (X - fm u))
    (hfmf : ∀ u ∈ Icc 0 L, fm u ≤ f u) (hfc : ContinuousOn f (Icc 0 L)) (huc : uc ∈ Ioo 0 L)
    (hmax : ∀ u ∈ Icc 0 L, f u ≤ Xs) (hfuc : f uc = Xs) (huniq : ∀ u ∈ Icc 0 L, f u = Xs → u = uc)
    {d : ℝ} (hd : d = f uc - fm uc) (hdp : 0 < d) {r1 : ℝ} (hfr : ∀ u, dist u uc < r1 → fm u < fm uc + d / 4)
    {ε0 : ℝ} (hε0 : 0 < ε0)
    (hband : ∀ X, Xs - ε0 < X → X < Xs → ∃ a b, a ≤ b ∧ (Icc 0 L ∩ {u | 0 ≤ T X u}) = Icc a b ∧
      (0 < a → T X a = 0) ∧ (b < L → T X b = 0))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ r1) (hρ2 : ρ ≤ uc) (hρ3 : ρ ≤ L - uc) :
    ∀ᶠ X in 𝓝[<] Xs, (sInf (Icc 0 L ∩ {u | 0 ≤ T X u}) < uc ∧ uc < sSup (Icc 0 L ∩ {u | 0 ≤ T X u}) ∧
      f (sInf (Icc 0 L ∩ {u | 0 ≤ T X u})) = X ∧ f (sSup (Icc 0 L ∩ {u | 0 ≤ T X u})) = X) ∧
      |sInf (Icc 0 L ∩ {u | 0 ≤ T X u}) - uc| < ρ ∧ |sSup (Icc 0 L ∩ {u | 0 ≤ T X u}) - uc| < ρ ∧
      0 ≤ sInf (Icc 0 L ∩ {u | 0 ≤ T X u}) ∧ sSup (Icc 0 L ∩ {u | 0 ≤ T X u}) ≤ L := by
  obtain ⟨ν, hν, hgap⟩ := far_gap hfc hmax huniq hρ
  have hm : 0 < min ν (min ε0 (d / 4)) := lt_min hν (lt_min hε0 (by linarith))
  filter_upwards [Ioo_mem_nhdsLT (show Xs - min ν (min ε0 (d / 4)) < Xs by linarith)] with X hX
  have hX1 : Xs - ν < X := by linarith [hX.1, min_le_left ν (min ε0 (d / 4))]
  have hX2 : Xs - ε0 < X := by linarith [hX.1, min_le_right ν (min ε0 (d / 4)), min_le_left ε0 (d / 4)]
  have hX3 : Xs - d / 4 < X := by linarith [hX.1, min_le_right ν (min ε0 (d / 4)), min_le_right ε0 (d / 4)]
  obtain ⟨a0, b0, hab, hset, hTa, hTb⟩ := hband X hX2 hX.2
  have hucI : uc ∈ Icc 0 L := ⟨huc.1.le, huc.2.le⟩
  have hfmuc : fm uc = Xs - d := by rw [hd, hfuc]; ring
  -- `uc` is allowed
  have hucS : uc ∈ Icc 0 L ∩ {u | 0 ≤ T X u} := by
    refine ⟨hucI, ?_⟩
    show 0 ≤ T X uc
    rw [hT X uc hucI, hfuc, hfmuc]
    exact mul_nonneg (by linarith [hX.2]) (by linarith)
  rw [hset] at hucS
  -- every allowed point is within `rho` of `uc`
  have hnear : ∀ u ∈ Icc a0 b0, |u - uc| < ρ := by
    intro u hu
    rw [← hset] at hu
    by_contra hcon
    rw [not_lt] at hcon
    have h1 := hgap u hu.1 hcon
    have h2 : 0 ≤ T X u := hu.2
    rw [hT X u hu.1] at h2
    have h3 : f u < X := by linarith
    have h4 : 0 < X - fm u := by linarith [hfmf u hu.1]
    nlinarith [mul_neg_of_neg_of_pos (sub_neg.2 h3) h4]
  have hamem : a0 ∈ Icc a0 b0 := ⟨le_rfl, hab⟩
  have hbmem : b0 ∈ Icc a0 b0 := ⟨hab, le_rfl⟩
  have ha := hnear a0 hamem
  have hb := hnear b0 hbmem
  have ha' := abs_lt.1 ha
  have hb' := abs_lt.1 hb
  have haS : a0 ∈ Icc 0 L ∩ {u | 0 ≤ T X u} := by rw [hset]; exact hamem
  have hbS : b0 ∈ Icc 0 L ∩ {u | 0 ≤ T X u} := by rw [hset]; exact hbmem
  have ha0 : 0 < a0 := by linarith
  have hb0 : b0 < L := by linarith
  have hfma : fm a0 < X := by
    have := hfr a0 (by rw [Real.dist_eq]; exact lt_of_lt_of_le ha hρ1)
    linarith
  have hfmb : fm b0 < X := by
    have := hfr b0 (by rw [Real.dist_eq]; exact lt_of_lt_of_le hb hρ1)
    linarith
  have hfa : f a0 = X := by
    have h := hTa ha0
    rw [hT X a0 haS.1] at h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  have hfb : f b0 = X := by
    have h := hTb hb0
    rw [hT X b0 hbS.1] at h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  rw [hset, csInf_Icc hab, csSup_Icc hab]
  have hXlt : X < Xs := hX.2
  refine ⟨⟨?_, ?_, hfa, hfb⟩, ha, hb, haS.1.1, hbS.1.2⟩
  · rcases lt_or_eq_of_le hucS.1 with h | h
    · exact h
    · exfalso; rw [← h] at hfuc; linarith
  · rcases lt_or_eq_of_le hucS.2 with h | h
    · exact h
    · exfalso; rw [h] at hfuc; linarith

end Structure

section EdgeWrapper

variable {L : ℝ} {f fm : ℝ → ℝ} {T : ℝ → ℝ → ℝ} {uc Xs : ℝ}

/-- **The edge limit for the action's derivative** (abstract form): for the pair `(f, f_-)` with `T = (f - X)(X - f_-)` on `[0, L]` and `f` having the unique nondegenerate interior maximum `Xs` at `uc`,
`int_{u_-}^{u_+} T^{-1/2} du -> pi sqrt(2/(kappa d))` as `X -> Xs-` (`kappa = -f''(uc)`, `d = f(uc) - f_-(uc)`). -/
theorem edge_wrapper (hT : ∀ X, ∀ u ∈ Icc 0 L, T X u = (f u - X) * (X - fm u))
    (hfmf : ∀ u ∈ Icc 0 L, fm u ≤ f u) (hfc : ContinuousOn f (Icc 0 L)) (hfmc : ContinuousOn fm (Icc 0 L))
    (hf2 : ContDiffOn ℝ 2 f (Ioo 0 L)) (huc : uc ∈ Ioo 0 L) (hmax : ∀ u ∈ Icc 0 L, f u ≤ Xs) (hfuc : f uc = Xs)
    (huniq : ∀ u ∈ Icc 0 L, f u = Xs → u = uc) (hcurv : deriv (deriv f) uc < 0) (hdp : fm uc < f uc)
    {ε0 : ℝ} (hε0 : 0 < ε0)
    (hband : ∀ X, Xs - ε0 < X → X < Xs → ∃ a b, a ≤ b ∧ (Icc 0 L ∩ {u | 0 ≤ T X u}) = Icc a b ∧
      (0 < a → T X a = 0) ∧ (b < L → T X b = 0)) :
    Tendsto (fun X => ∫ u in (sInf (Icc 0 L ∩ {u | 0 ≤ T X u}))..(sSup (Icc 0 L ∩ {u | 0 ≤ T X u})), 1 / Real.sqrt (T X u))
      (𝓝[<] Xs) (𝓝 (Real.pi * Real.sqrt (2 / ((-deriv (deriv f) uc) * (f uc - fm uc))))) := by
  set κ := -deriv (deriv f) uc with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  set d := f uc - fm uc with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  -- smoothness of `f` at `uc`
  have hO : IsOpen (Ioo (0 : ℝ) L) := isOpen_Ioo
  have hdf : ContDiffOn ℝ 1 (deriv f) (Ioo 0 L) := hf2.deriv_of_isOpen hO (by norm_num)
  have hdf0 : ContDiffOn ℝ 0 (deriv (deriv f)) (Ioo 0 L) := hdf.deriv_of_isOpen hO (by norm_num)
  have hHf : ∀ u ∈ Ioo 0 L, HasDerivAt f (deriv f u) u := fun u hu =>
    ((hf2.differentiableOn (by norm_num)) u hu |>.differentiableAt (hO.mem_nhds hu)).hasDerivAt
  have hHf1 : ∀ u ∈ Ioo 0 L, HasDerivAt (deriv f) (deriv (deriv f) u) u := fun u hu =>
    ((hdf.differentiableOn (by norm_num)) u hu |>.differentiableAt (hO.mem_nhds hu)).hasDerivAt
  have hf2c : ContinuousAt (deriv (deriv f)) uc := hdf0.continuousOn.continuousAt (hO.mem_nhds huc)
  have hf1uc : deriv f uc = 0 := by
    apply IsLocalMax.deriv_eq_zero
    filter_upwards [Icc_mem_nhds huc.1 huc.2] with y hy
    rw [hfuc]
    exact hmax y hy
  -- the radius `r0`
  obtain ⟨r, hr, hfr2⟩ := Metric.eventually_nhds_iff.1 (hf2c.eventually (eventually_lt_nhds
    (show deriv (deriv f) uc < -(κ / 2) by rw [hκdef]; linarith)))
  set r0 := min (r / 2) (min (uc / 2) ((L - uc) / 2)) with hr0def
  have hr0 : 0 < r0 := lt_min (by linarith) (lt_min (by linarith [huc.1]) (by linarith [huc.2]))
  have hr0a : r0 ≤ r / 2 := min_le_left _ _
  have hr0b : r0 ≤ uc / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr0c : r0 ≤ (L - uc) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hball : Icc (uc - r0) (uc + r0) ⊆ Ioo 0 L := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hHf' : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt f (deriv f u) u := fun u hu => hHf u (hball hu)
  have hHf1' : ∀ u ∈ Icc (uc - r0) (uc + r0), HasDerivAt (deriv f) (deriv (deriv f) u) u := fun u hu => hHf1 u (hball hu)
  have hf2le : ∀ u ∈ Icc (uc - r0) (uc + r0), deriv (deriv f) u ≤ -(κ / 2) := by
    intro u hu
    refine (hfr2 (y := u) ?_).le
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2]
  -- continuity of `fm`
  have hfmI : ContinuousOn fm (Icc (uc - r0) (uc + r0)) := hfmc.mono (fun u hu => Ioo_subset_Icc_self (hball hu))
  have hfmat : ContinuousAt fm uc := hfmc.continuousAt (Icc_mem_nhds huc.1 huc.2)
  obtain ⟨r1, hr1, hfr⟩ := Metric.eventually_nhds_iff.1 (hfmat.eventually (eventually_lt_nhds (show fm uc < fm uc + d / 4 by linarith)))
  set ρ0 := min r1 (min uc (L - uc)) with hρ0def
  have hρ0 : 0 < ρ0 := lt_min hr1 (lt_min huc.1 (by linarith [huc.2]))
  have hρ01 : ρ0 ≤ r1 := min_le_left _ _
  have hρ02 : ρ0 ≤ uc := (min_le_right _ _).trans (min_le_left _ _)
  have hρ03 : ρ0 ≤ L - uc := (min_le_right _ _).trans (min_le_right _ _)
  have hstruct : ∀ ρ, 0 < ρ → ρ ≤ ρ0 → _ := fun ρ hρ hρρ => edge_structure (T := T) hT hfmf hfc huc hmax hfuc huniq hd hdpos hfr hε0 hband
    hρ (hρρ.trans hρ01) (hρρ.trans hρ02) (hρρ.trans hρ03)
  set a : ℝ → ℝ := fun X => sInf (Icc 0 L ∩ {u | 0 ≤ T X u}) with hadef
  set b : ℝ → ℝ := fun X => sSup (Icc 0 L ∩ {u | 0 ≤ T X u}) with hbdef
  have hev := (hstruct ρ0 hρ0 le_rfl).mono fun X h => h.1
  have hta : Tendsto a (𝓝[<] Xs) (𝓝 uc) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hstruct (min ε ρ0) (lt_min hε hρ0) (min_le_right _ _)] with X h
    rw [Real.dist_eq]
    exact lt_of_lt_of_le h.2.1 (min_le_left _ _)
  have htb : Tendsto b (𝓝[<] Xs) (𝓝 uc) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hstruct (min ε ρ0) (lt_min hε hρ0) (min_le_right _ _)] with X h
    rw [Real.dist_eq]
    exact lt_of_lt_of_le h.2.2.1 (min_le_left _ _)
  have hcore := edge_integral_tendsto (l := 𝓝[<] Xs) (f := f) (f1 := deriv f) (f2 := deriv (deriv f)) (fm := fm) (uc := uc) (Xs := Xs) (κ := κ)
    (r0 := r0) hr0 hHf' hHf1' hf2c hf2le hfuc hf1uc (by rw [hκdef]; ring) hκ hfmI (by linarith [hfuc, hd, hdpos])
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) hev hta htb
  have eXd : Xs - fm uc = d := by rw [hd, hfuc]
  rw [eXd] at hcore
  refine hcore.congr' ?_
  filter_upwards [hstruct ρ0 hρ0 le_rfl] with X h
  refine intervalIntegral.integral_congr (fun u hu => ?_)
  have hsub : uIcc (a X) (b X) ⊆ Icc 0 L := by
    rw [uIcc_of_le (by linarith [h.1.1, h.1.2.1])]
    exact Icc_subset_Icc h.2.2.2.1 h.2.2.2.2
  show 1 / Real.sqrt ((f u - X) * (X - fm u)) = 1 / Real.sqrt (T X u)
  rw [hT X u (hsub hu)]

end EdgeWrapper

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.peano2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.peano2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.chord_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.chord_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.alg_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.alg_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.pointwise_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.pointwise_limit

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.integral_inv_sqrt_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.integral_inv_sqrt_unit

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.T_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.T_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_integral_tendsto

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.far_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.far_gap

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_structure

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.edge_wrapper

end FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv

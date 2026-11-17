module

public import FormalResearch.Special.LatticePhaseProps

/-!
# Abstract calibrated phase: hypotheses and slope facts

The generic part of `lem:latticesum` (`constants.tex`) uses the phase `τ₀ = G/π` only through the
following properties, collected in `CalPhase τ₀ X y₀ m M K` (window `|Re s| ≤ X+1`, `|Im s| ≤ y₀`):

* `τ₀` is complex differentiable (twice) on the window, real on `ℝ`;
* `Re τ₀' ≥ m` on the window and `Re τ₀' ≤ M` on the real window;
* `|τ₀''| ≤ K` on the window.

The concrete Gamma phase satisfies this with `m ≍ (ϰ/2π) log L`, `M ≍ (2ϰ/π) log L` (`LatticeGamma`).

* `CalPhase.real_slope_ge/le` : real mean-value bounds `m (y-x) ≤ t₀(y)-t₀(x) ≤ M (y-x)`;
* `CalPhase.im_ge` : `Im τ₀(u + iy) ≥ m y` for `0 ≤ y ≤ y₀` (and the mirror image);
  this is the estimate `|e^{2πikτ₀}| ≤ e^{-2πkmy}` of the contour shift.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- The window `|Re s| ≤ X+1`, `|Im s| ≤ y₀`. -/
def InWin (X y0 : ℝ) (s : ℂ) : Prop := |s.re| ≤ X + 1 ∧ |s.im| ≤ y0

/-- Hypotheses on the complexified phase `τ₀` (see the module docstring). -/
structure CalPhase (τ0 : ℂ → ℂ) (X y0 m M K : ℝ) : Prop where
  hX : 0 < X
  hy0 : 0 < y0
  hm : 0 < m
  diff : ∀ s, InWin X y0 s → DifferentiableAt ℂ τ0 s
  ddiff : ∀ s, InWin X y0 s → DifferentiableAt ℂ (deriv τ0) s
  real : ∀ x : ℝ, (τ0 x).im = 0
  ge : ∀ s, InWin X y0 s → m ≤ (deriv τ0 s).re
  le : ∀ x : ℝ, |x| ≤ X + 1 → (deriv τ0 x).re ≤ M
  dd : ∀ s, InWin X y0 s → ‖deriv (deriv τ0) s‖ ≤ K

/-- The real phase. -/
noncomputable def realPhase (τ0 : ℂ → ℂ) (x : ℝ) : ℝ := (τ0 x).re

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K : ℝ}

lemma inWin_real {x : ℝ} (hx : |x| ≤ X + 1) (hy : 0 ≤ y0) : InWin X y0 (x : ℂ) := by
  refine ⟨by simpa using hx, by simpa using hy⟩

lemma mono (h : CalPhase τ0 X y0 m M K) {y1 : ℝ} (hy1 : 0 < y1) (hle : y1 ≤ y0) :
    CalPhase τ0 X y1 m M K where
  hX := h.hX
  hy0 := hy1
  hm := h.hm
  diff s hs := h.diff s ⟨hs.1, hs.2.trans hle⟩
  ddiff s hs := h.ddiff s ⟨hs.1, hs.2.trans hle⟩
  real := h.real
  ge s hs := h.ge s ⟨hs.1, hs.2.trans hle⟩
  le := h.le
  dd s hs := h.dd s ⟨hs.1, hs.2.trans hle⟩

lemma hasDerivAt_real (h : CalPhase τ0 X y0 m M K) {x : ℝ} (hx : |x| ≤ X + 1) :
    HasDerivAt (realPhase τ0) (deriv τ0 x).re x := by
  have := (h.diff x (inWin_real hx h.hy0.le)).hasDerivAt
  exact this.real_of_complex

lemma real_slope_ge (h : CalPhase τ0 X y0 m M K) {x y : ℝ} (hx : |x| ≤ X + 1) (hy : |y| ≤ X + 1)
    (hxy : x ≤ y) : m * (y - x) ≤ realPhase τ0 y - realPhase τ0 x := by
  have hD : Convex ℝ (Icc (-(X + 1)) (X + 1)) := convex_Icc _ _
  have hmem : ∀ z : ℝ, |z| ≤ X + 1 → z ∈ Icc (-(X + 1)) (X + 1) := fun z hz => abs_le.mp hz
  refine hD.mul_sub_le_image_sub_of_le_deriv (f := realPhase τ0) (C := m) ?_ ?_ ?_ x (hmem x hx) y
    (hmem y hy) hxy
  · intro z hz
    exact (h.hasDerivAt_real (abs_le.mpr hz)).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact (h.hasDerivAt_real (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    rw [(h.hasDerivAt_real (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).deriv]
    exact h.ge z (inWin_real (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) h.hy0.le)

lemma real_slope_le (h : CalPhase τ0 X y0 m M K) {x y : ℝ} (hx : |x| ≤ X + 1) (hy : |y| ≤ X + 1)
    (hxy : x ≤ y) : realPhase τ0 y - realPhase τ0 x ≤ M * (y - x) := by
  have hD : Convex ℝ (Icc (-(X + 1)) (X + 1)) := convex_Icc _ _
  have hmem : ∀ z : ℝ, |z| ≤ X + 1 → z ∈ Icc (-(X + 1)) (X + 1) := fun z hz => abs_le.mp hz
  refine hD.image_sub_le_mul_sub_of_deriv_le (f := realPhase τ0) (C := M) ?_ ?_ ?_ x (hmem x hx) y
    (hmem y hy) hxy
  · intro z hz
    exact (h.hasDerivAt_real (abs_le.mpr hz)).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact (h.hasDerivAt_real (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    rw [(h.hasDerivAt_real (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).deriv]
    exact h.le z (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)

lemma realPhase_strictMono (h : CalPhase τ0 X y0 m M K) {x y : ℝ} (hx : |x| ≤ X + 1)
    (hy : |y| ≤ X + 1) (hxy : x < y) : realPhase τ0 x < realPhase τ0 y := by
  have := h.real_slope_ge hx hy hxy.le
  nlinarith [h.hm]

/-- `Im τ₀(u + iy) ≥ m y` for `0 ≤ y ≤ y₀`, `|u| ≤ X+1`; the imaginary part has the sign of `y`. -/
lemma im_ge (h : CalPhase τ0 X y0 m M K) {u : ℝ} (hu : |u| ≤ X + 1) {a b : ℝ}
    (ha : |a| ≤ y0) (hb : |b| ≤ y0) (hab : a ≤ b) :
    m * (b - a) ≤ (τ0 (u + b * I)).im - (τ0 (u + a * I)).im := by
  have hD : Convex ℝ (Icc (-y0) y0) := convex_Icc _ _
  have hmem : ∀ z : ℝ, |z| ≤ y0 → z ∈ Icc (-y0) y0 := fun z hz => abs_le.mp hz
  let g : ℝ → ℝ := fun y => (τ0 (u + y * I)).im
  have hg : ∀ y : ℝ, |y| ≤ y0 → HasDerivAt g (deriv τ0 (u + y * I)).re y := by
    intro y hy
    have hw : InWin X y0 (u + y * I) := ⟨by simpa using hu, by simpa using hy⟩
    have h1 : HasDerivAt (fun y : ℝ => ((u : ℂ) + (y : ℂ) * I)) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (u : ℂ)
      simpa using this
    have h2 := HasDerivAt.scomp y (h.diff _ hw).hasDerivAt h1
    have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h2
    refine h3.congr_deriv ?_
    simp
  refine hD.mul_sub_le_image_sub_of_le_deriv (f := g) (C := m) ?_ ?_ ?_ a (hmem a ha) b (hmem b hb) hab
  · intro z hz
    exact (hg z (abs_le.mpr hz)).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    exact (hg z (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    have hz' : |z| ≤ y0 := abs_le.mpr ⟨hz.1.le, hz.2.le⟩
    rw [(hg z hz').deriv]
    exact h.ge _ ⟨by simpa using hu, by simpa using hz'⟩

end CalPhase

end FormalResearch.Special.Lattice

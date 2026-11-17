module

public import FormalResearch.Complex.Rouche
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Hurwitz's theorem

Generic complex analysis (no application content).  **Proved**, for a net of holomorphic functions `F n` converging
locally uniformly on an open set `U` (`TendstoLocallyUniformlyOn F f p U`, along any filter `p`, in particular sequences).

Statements formalised (Hurwitz 1889; Conway, *Functions of One Complex Variable*, VII.2.5; Stein–Shakarchi, Ch. 3 Prop. 4.2
for the non-vanishing form):

* `hurwitz_zeroCount`: if `f` has no zero on the circle `sphere c r` (`r < R`, `ball c R ⊆ U`) then eventually
  `F n` and `f` have the same number of zeros, with multiplicity, in `ball c r` (Rouché applied to `F n` and `f`);
* `hurwitz_zeroCount_small`: if `f` has a zero of order `m` at `z₀` and `f` is not identically zero near `z₀`, there is
  `r₀ > 0` such that for **every** `r ∈ (0, r₀]`, eventually `F n` has exactly `m` zeros (with multiplicity) in
  `ball z₀ r`; they therefore converge to `z₀` (`hurwitz_exists_zero_near`: every zero of `f`, not identically zero near
  it, is a limit of zeros of `F n`);
* `hurwitz_nonvanishing`: if `U` is open and connected, the `F n` are zero-free on `U` and `f ≢ 0` then `f` has no zero in `U`;
* `hurwitz_no_zeros_off`: on a compact `K ⊆ U` and an open `W` containing the zeros of `f` in `K`, eventually `F n` has no zero
  in `K \ W` (this is uniform convergence only; `f` need not be holomorphic).

**Not formalised.** Hurwitz for univalent limits (injectivity), the meromorphic version, a quantitative rate.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ArgPrinciple

variable {ι : Type*} {p : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r R : ℝ}

/-- **Hurwitz, counting form.** -/
theorem hurwitz_zeroCount (hU : IsOpen U) (hF : TendstoLocallyUniformlyOn F f p U)
    (hFd : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hrR : r < R) (hball : ball c R ⊆ U) (hne : ∀ z ∈ sphere c r, f z ≠ 0) :
    ∀ᶠ n in p, zeroCount (F n) c r = zeroCount f c r := by
  have hsphU : sphere c r ⊆ U := sphere_subset_closedBall.trans ((closedBall_subset_ball hrR).trans hball)
  have hne' : (sphere c r).Nonempty := ⟨c + r, by simp [abs_of_pos hr]⟩
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hne'
    (hf.continuousOn.mono hsphU).norm
  have hm : 0 < ‖f z0‖ := norm_pos_iff.mpr (hne z0 hz0)
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hF (sphere c r) hsphU (isCompact_sphere c r)
  have h1 := Metric.tendstoUniformlyOn_iff.mp hunif ‖f z0‖ hm
  filter_upwards [h1, hFd] with n hn hd
  refine rouche hr hrR (hd.mono hball) (hf.mono hball) fun z hz => ?_
  have := hn z hz
  rw [dist_eq_norm] at this
  calc ‖F n z - f z‖ = ‖f z - F n z‖ := norm_sub_rev _ _
    _ < ‖f z0‖ := this
    _ ≤ ‖f z‖ := isMinOn_iff.mp hmin z hz

end FormalResearch.ArgPrinciple

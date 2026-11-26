module

public import FormalResearch.SignUncertainty.UctBumpFarNear
public import FormalResearch.SignUncertainty.UctBumpFarTail
public import FormalResearch.SignUncertainty.UctBumpE0

/-!
# `uct:bump-weighted`, the far-band estimate (F2a)

`bump_weighted_far`: for `B` a `BumpProfile b δ M α β K` with `α ≤ 4`, `β ≥ 3/2`, `δ ≥ a₀ c^{-1/2}`, `c ≥ 64`, and `L = log(π²ξ) ≥ 2`,
`|Δh_main(L) - c⁻¹ B(L)| ≤ C M c⁻² L⁻²` with `C` depending only on `b, α, K, a₀`.

Proof: `bump_E0_identity` gives `Δh_main - c⁻¹B(L) = (1/2π)∫ E₀ e^{icLτ} B̂(icτ)dτ`.  Split `B = B_near + B_tail` with the fixed cutoff of `UctBumpFarSplit`; the compactly
supported part is `bump_near_bound` (polynomial subtraction and two integrations by parts at the scale `h = c^{-1/2}`) and the smooth tail is `bump_tail_bound`
(two integrations by parts in `s = cτ`, damped transforms).  This is the far estimate of `uct:bump-weighted` (`L ≥ ¼ log c`; here stated for `L ≥ 2`, which contains it as soon as `c ≥ e⁸`) and
item (3) of `fct:bump-5` (its `δ_L^{3-α}` correction is absorbed for `α ≤ 4`, `δ ≥ a₀ c^{-1/2}`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open FormalResearch.Asymptotics
open scoped Real

namespace FormalResearch.SignUncertainty

lemma bumpLaplace_add_of_integrable {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) {s : ℂ} (hs : s.re = 0) :
    bumpLaplace (fun x => f x + g x) s = bumpLaplace f s + bumpLaplace g s := by
  unfold bumpLaplace
  have hb : ∀ x : ℝ, ‖Complex.exp (-s * (x : ℂ))‖ = 1 := fun x => by
    rw [bump_norm_exp_neg_mul, hs]; simp
  have hcexp : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ)) := by fun_prop
  have h1 : Integrable fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (f x : ℂ) := by
    refine hf.norm.mono' (hcexp.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [norm_mul, hb, Complex.norm_real, one_mul]
  have h2 : Integrable fun x : ℝ => Complex.exp (-s * (x : ℂ)) * (g x : ℂ) := by
    refine hg.norm.mono' (hcexp.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [norm_mul, hb, Complex.norm_real, one_mul]
  rw [← integral_add h1 h2]
  congr 1
  funext x
  push_cast
  ring

theorem bump_weighted_far {b α β : ℝ} (hb : 0 < b) (hα : α ≤ 4) (K : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 64 ≤ c → 0 < ξ →
      2 ≤ Real.log (Real.pi ^ 2 * ξ) → 3 / 2 ≤ β → a0 ≤ Real.sqrt c * δ → BumpProfile b δ M α β K B →
      ‖bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
        C * M * (c ^ 2)⁻¹ * ((Real.log (Real.pi ^ 2 * ξ)) ^ 2)⁻¹ := by
  obtain ⟨Cn, hCn0, hn⟩ := bump_near_bound (b := b) (α := α) hb hα K ha0
  obtain ⟨Ct, hCt0, ht⟩ := bump_tail_bound (α := α) (β := β) (tailK K)
  refine ⟨(1 / (2 * Real.pi)) * (Cn + Ct), by positivity, ?_⟩
  intro B δ M c ξ hδ0 hδ1 hbδ hM hc hξ hL hβ ha hB
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hc2 : 2 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hid := bump_E0_identity (α := α) hb hβ K B δ M c ξ hδ0 hδ1 hbδ hM hc2 hξ hB
  rw [← hLdef] at hid
  have hno := hn B δ M c L β hδ0 hδ1 hbδ hM (by linarith) hL hβ ha hB
  have hTp := hB.tail_profile hM
  have hnp := hB.near_profile hb hδ0 hM hβ
  have hto := ht (bumpTail B) M c L hM hc (by linarith) hβ hTp
  have hβ1 : 1 < β := by linarith
  have hsplit : ∀ τ : ℝ, bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) =
      bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) +
        bumpLaplace (bumpTail B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
    intro τ
    have hre : ((c : ℂ) * ((τ : ℂ) * Complex.I)).re = 0 := by simp
    have := bumpLaplace_add_of_integrable (hnp.integrable_self hbδ (by norm_num)) (hTp.integrable_self (by norm_num) hβ1) hre
    have e : (fun x => bumpNear B x + bumpTail B x) = B := funext fun x => bumpNear_add_bumpTail B x
    rw [e] at this
    exact this
  have hint : ∀ τ : ℝ, bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) =
      bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) +
      bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace (bumpTail B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) := fun τ => by
    rw [hsplit τ]; ring
  rw [hid]
  simp_rw [hint]
  rw [integral_add hno.1 hto.1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have := (norm_add_le _ _).trans (add_le_add hno.2 hto.2)
  calc 1 / (2 * Real.pi) * ‖(∫ τ : ℝ, _) + ∫ τ : ℝ, _‖ ≤ 1 / (2 * Real.pi) * (Cn * M * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ + Ct * M * (c ^ 2)⁻¹ * (L ^ 2)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.bump_weighted_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_weighted_far

end FormalResearch.SignUncertainty

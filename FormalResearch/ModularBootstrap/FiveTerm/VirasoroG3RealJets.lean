module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Tip
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Poisson

/-!
# Cubic jets of the pieces of `log Gout` on `(0, 1/4)` (FIVE-0b, `ctu:jets`, `g₃`, step 5)

Along `𝓝[>] 0`: the jets of `log tip` (`jet_log_tipR`), of `log(1 ± x)`, of the edge point `ε(x) = (4/π) arctan x`,
and, from `poisson_third`, of `ε ↦ Re h̄_a(ε)` (`jet_re_hbarA`).  Composition with `ε(x)` kills the quadratic coefficient
of `Re h̄_a` in the cubic coefficient, because `ε` has no quadratic term.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory Asymptotics
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma nhdsGT_le_nhds0 : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 := nhdsWithin_le_nhds

/-- Jets only depend on the function eventually. -/
lemma Jet.congr_ev {l : Filter ℝ} {f g : ℝ → ℝ} {c0 c1 c2 c3 : ℝ} (hf : Jet l f c0 c1 c2 c3)
    (h : f =ᶠ[l] g) : Jet l g c0 c1 c2 c3 := by
  unfold Jet at *
  exact hf.congr' (by filter_upwards [h] with x hx; rw [hx]) (Eventually.of_forall fun _ => rfl)

/-- The jet of the logarithm of a positive-valued jet. -/
lemma Jet.log {l : Filter ℝ} (hl : l ≤ 𝓝 0) {f : ℝ → ℝ} {c0 c1 c2 c3 : ℝ} (hc : 0 < c0)
    (hf : Jet l f c0 c1 c2 c3) :
    Jet l (fun x => Real.log (f x)) (Real.log c0) (c1 / c0)
      (c2 / c0 - c1 ^ 2 / (2 * c0 ^ 2)) (c3 / c0 - c1 * c2 / c0 ^ 2 + c1 ^ 3 / (3 * c0 ^ 3)) := by
  have hg : Jet l (fun x => f x - c0) 0 c1 c2 c3 :=
    (hf.sub (Jet.const (l := l) c0)).of_eq (by ring) (by ring) (by ring) (by ring)
  have ht : Tendsto (fun x => f x - c0) l (𝓝 0) := hg.tendsto_zero hl
  have h := Jet.comp hl (jet_log_add hc) hg ht
  refine (h.of_eq rfl ?_ ?_ ?_).congr (fun x => ?_)
  · ring
  · field_simp; ring
  · field_simp; ring
  · simp only [add_sub_cancel]

/-- `log(1+x)` and `log(1-x)`. -/
lemma jet_log_one_add : Jet (𝓝[>] (0 : ℝ)) (fun x => Real.log (1 + x)) 0 1 (-1 / 2) (1 / 3) := by
  have h := Jet.comp nhdsGT_le_nhds0 ((jet_log_add one_pos).mono (l' := 𝓝 0) le_rfl) (Jet.id (l := 𝓝[>] (0 : ℝ)) 1)
    (tendsto_id.mono_left nhdsWithin_le_nhds |>.congr (fun x => by simp))
  refine (h.of_eq (by simp) (by norm_num) (by norm_num) (by norm_num)).congr (fun x => ?_)
  simp

lemma jet_log_one_sub : Jet (𝓝[>] (0 : ℝ)) (fun x => Real.log (1 - x)) 0 (-1) (-1 / 2) (-1 / 3) := by
  have h := Jet.comp nhdsGT_le_nhds0 (jet_log_add one_pos) (Jet.id (l := 𝓝[>] (0 : ℝ)) (-1))
    (by
      have : Tendsto (fun x : ℝ => -1 * x) (𝓝 0) (𝓝 (-1 * 0)) := (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
  refine (h.of_eq (by simp) (by norm_num) (by norm_num) (by norm_num)).congr (fun x => ?_)
  simp [sub_eq_add_neg]


lemma sqrt2_sq' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma tendsto_mR_nhdsGT : Tendsto mR (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous mR := by
    unfold mR
    refine Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have := hc.tendsto 0
  simp only [mR] at this ⊢
  simpa using this.mono_left nhdsWithin_le_nhds

lemma jet_arccos_mR : Jet (𝓝[>] (0 : ℝ)) (fun x => Real.arccos (mR x)) (π / 2) (-(2 * √2)) 0 (-(2 * √2) / 3) := by
  have h := Jet.comp (nhdsGT_le_nhds0) jet_arccos (jet_mR (nhdsGT_le_nhds0)) tendsto_mR_nhdsGT
  refine h.of_eq rfl (by ring) (by ring) ?_
  linear_combination (-(4 / 3) * √2) * sqrt2_sq'

lemma jet_phi_mR : Jet (𝓝[>] (0 : ℝ)) (fun x => phiR (mR x)) (Real.arsinh 1) 0 (-(2 * √2)) 0 := by
  have h := Jet.comp (nhdsGT_le_nhds0) jet_phi (jet_mR (nhdsGT_le_nhds0)) tendsto_mR_nhdsGT
  have h2 : (√2) ≠ 0 := by positivity
  refine h.of_eq rfl (by ring) ?_ (by ring)
  field_simp
  norm_num

/-- **The jet of `log tip`**: `log tip(x) = c₀ - (4√2/π) x + c₂ x² + (-4√2/(3π) - 128√2/(3π³)) x³ + o(x³)`. -/
lemma jet_log_tipR : ∃ c0 c2 : ℝ, Jet (𝓝[>] (0 : ℝ)) (fun x => Real.log (tipR x)) c0 (-(4 * √2 / π)) c2
    (-(4 * √2) / (3 * π) - 128 * √2 / (3 * π ^ 3)) := by
  have hpi := Real.pi_pos
  have hA := Jet.log (nhdsGT_le_nhds0) (by positivity : 0 < π / 2) jet_arccos_mR
  have hP := Jet.log (nhdsGT_le_nhds0) arsinh_one_pos jet_phi_mR
  have hd := hA.sub hP
  refine ⟨_, _, (hd.congr_ev ?_).of_eq rfl ?_ rfl ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
    have ht := tipR_pos hx.1 hx.2
    have hm := mR_lt_one hx.1 hx.2
    have hm0 := mR_pos hx.1
    have h1 : 0 < Real.arccos (mR x) := Real.arccos_pos.mpr hm
    have h2 : 0 < 1 - mR x ^ 2 := by nlinarith only [hm, hm0]
    have h3 : 0 < phiR (mR x) := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr h2)
    show Real.log (Real.arccos (mR x)) - Real.log (phiR (mR x)) = Real.log (tipR x)
    unfold tipR
    rw [Real.log_div h1.ne' h3.ne']
  · ring
  · have hA0 := arsinh_one_pos.ne'
    field_simp
    linear_combination (-64 * √2 * Real.arsinh 1 ^ 3) * sqrt2_sq'


lemma jet_epsR : Jet (𝓝[>] (0 : ℝ)) epsR 0 (4 / π) 0 (-4 / (3 * π)) := by
  have hpi := Real.pi_pos
  have h := ((jet_arctan.mono (l' := 𝓝[>] (0 : ℝ)) nhdsGT_le_nhds0).const_mul (4 / π))
  refine h.of_eq (by ring) (by ring) (by ring) (by field_simp)

lemma tendsto_epsR : Tendsto epsR (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
  have hc : Continuous epsR := by unfold epsR; fun_prop
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := hc.tendsto 0
    simp only [epsR, Real.arctan_zero, mul_zero] at this ⊢
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hpi := Real.pi_pos
    show 0 < epsR x
    unfold epsR
    have := Real.arctan_pos.mpr hx0
    positivity

/-- **The cubic jet of `Re h̄_a` at the edge point `0`**, from `poisson_third`. -/
lemma jet_re_hbarA {a b : ℝ → ℝ} (ha : Amp a) (hb : Amp b)
    (hab : ∀ t : ℝ, t ≠ 0 → b t = (a t - a 0) / Real.sinh (π * t) ^ 2) :
    Jet (𝓝[>] (0 : ℝ)) (fun ε : ℝ => (hbarA a (ε : ℂ)).re) (a 0) (∫ t : ℝ, (a t - a 0) * (π * kern t))
      (-(π ^ 2 * b 0)) (-(π ^ 2) * ((∫ t : ℝ, (a t - a 0) * (π * kern t)) / 6 +
        ∫ t : ℝ, (b t - b 0) * (π * kern t))) := by
  have hq := poisson_third ha hb hab
  set S1 := ∫ t : ℝ, (a t - a 0) * (π * kern t)
  set L := -(π ^ 2) * (S1 / 6 + ∫ t : ℝ, (b t - b 0) * (π * kern t))
  have hq0 := hq.sub_const L
  rw [sub_self] at hq0
  have h1 := ((isLittleO_one_iff ℝ).mpr hq0).mul_isBigO
    (isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝[>] (0 : ℝ)))
  unfold Jet
  refine h1.congr' ?_ (Eventually.of_forall fun x => by simp)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := (ne_of_gt hx)
  field_simp
  ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.jet_log_tipR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.jet_log_tipR

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.jet_re_hbarA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.jet_re_hbarA

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.Jet.log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.Jet.log

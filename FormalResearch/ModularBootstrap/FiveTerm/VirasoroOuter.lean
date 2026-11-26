module

public import FormalResearch.ModularBootstrap.FiveTerm.StripInverse
public import FormalResearch.ModularBootstrap.FiveTerm.CombData
public import FormalResearch.ModularBootstrap.FiveTerm.CombClass
public import FormalResearch.ModularBootstrap.FiveTerm.BoundaryExt
public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterPoisson

/-!
# The Virasoro outer function `G_outer` (FIVE-0 slice 4, definition and soft properties)

`G_outer(z) = exp(h̄_a(s(z))) · (1-z)^{1/2} (1+z)^{-2} · Q̂(z)^{-1/4}`, `s(z) = (4/π) arctan z`, `Q̂ = Ŝ ∘ u`,
`a = aAmp` the slit-matched amplitude of `CombData` (`h̄_a` the strip Schwarz integral of `a`, so that
`Re h̄_a(iτ) = a(τ)`).  The first factor is `σ`-invariant (`h̄_a(1-s) = h̄_a(s)`), the second factor is the
explicit part, and the third makes `G(σ z)/G(z) = R(z)` of `cts:R-id` hold *by construction*
(`ρ(σz)/ρ(z) = R(z)` for `ρ = (1-z)^{1/2}(1+z)^{-2} Q̂^{-1/4}`).  This file: the definition, boundary values of the
factors, and the soft `OuterDatum` fields `diff`, `cont`, `conj`, `ne_zero`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The boundary extension of `Q̂ = Ŝ ∘ u` to `closure Ω ∖ {±i}`. -/
noncomputable def qBd (z : ℂ) : ℂ := extLim halfDisc qHat z

/-- The Virasoro outer function (see the module docstring). -/
noncomputable def Gout (z : ℂ) : ℂ :=
  Complex.exp (hbarA aAmp (sInv z)) * (1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2 * (qBd z) ^ (-(1 / 4 : ℂ))

lemma qBd_of_mem {z : ℂ} (hz : z ∈ halfDisc) : qBd z = qHat z :=
  extLim_of_mem hz
    (differentiableOn_qHat.continuousOn.continuousAt (isOpen_halfDisc.mem_nhds hz)).continuousWithinAt

lemma exists_qBd {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) :
    qBd z ∈ Complex.slitPlane ∧ Tendsto qHat (𝓝[halfDisc] z) (𝓝 (qBd z)) := by
  obtain ⟨L, hL, ht⟩ := exists_limit_qHat hz h1 h2
  have : qBd z = L := extLim_eq_of_tendsto hz ht
  rw [this]; exact ⟨hL, ht⟩

lemma ne_of_mem_diff {z : ℂ} (hz : z ∈ closure halfDisc \ {Complex.I, -Complex.I}) :
    z ≠ Complex.I ∧ z ≠ -Complex.I :=
  ⟨fun h => hz.2 (by simp [h]), fun h => hz.2 (by simp [h])⟩

lemma continuousOn_qBd : ContinuousOn qBd (closure halfDisc \ {Complex.I, -Complex.I}) :=
  continuousOn_extLim (fun z hz =>
    ⟨_, (exists_qBd hz.1 (ne_of_mem_diff hz).1 (ne_of_mem_diff hz).2).2⟩)

lemma ne_of_mem_sing {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) :
    z ≠ Complex.I ∧ z ≠ -Complex.I ∧ z ≠ 1 := by
  refine ⟨fun h => hz.2 ?_, fun h => hz.2 ?_, fun h => hz.2 ?_⟩ <;> simp [h, singPts]

lemma sing_subset : closure halfDisc \ singPts ⊆ closure halfDisc \ {Complex.I, -Complex.I} := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  obtain ⟨h1, h2, _⟩ := ne_of_mem_sing hz
  simp [h1, h2]

lemma qBd_mem_slit {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) : qBd z ∈ Complex.slitPlane :=
  (exists_qBd hz.1 (ne_of_mem_sing hz).1 (ne_of_mem_sing hz).2.1).1

lemma qBd_ne_zero {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) : qBd z ≠ 0 :=
  Complex.slitPlane_ne_zero (qBd_mem_slit hz)

lemma re_one_sub_pos_cl {z : ℂ} (hz : z ∈ closure halfDisc) (h : z ≠ 1) : 0 < 1 - z.re := by
  obtain ⟨hn, hr⟩ := closure_halfDisc_subset hz
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  by_contra hcon
  push Not at hcon
  have hre : z.re = 1 := by nlinarith [sq_nonneg z.im]
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact h (Complex.ext (by simpa using hre) (by simpa using him))

lemma one_sub_mem_slit {z : ℂ} (hz : z ∈ closure halfDisc) (h : z ≠ 1) : 1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using re_one_sub_pos_cl hz h

lemma one_add_mem_slit {z : ℂ} (hz : z ∈ closure halfDisc) : 1 + z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have := (closure_halfDisc_subset hz).2
  simp; linarith

lemma one_add_ne_zero' {z : ℂ} (hz : z ∈ closure halfDisc) : 1 + z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_add_mem_slit hz)

lemma continuousOn_one_sub_cpow : ContinuousOn (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) (closure halfDisc) := by
  intro z hz
  have hre : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  have h0 : 0 ≤ (1 - z).re := by
    have := (closure_halfDisc_subset hz)
    obtain ⟨hn, _⟩ := this
    have : z.re ≤ ‖z‖ := Complex.re_le_norm z
    simp; linarith
  have : ContinuousAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) (1 - z) :=
    continuousAt_cpow_const_of_re_pos (Or.inl h0) hre
  exact (this.comp (f := fun z : ℂ => 1 - z) (by fun_prop)).continuousWithinAt

lemma conj_cpow_slit {x : ℂ} (hx : x ∈ Complex.slitPlane) (n : ℂ) :
    starRingEnd ℂ (x ^ n) = starRingEnd ℂ x ^ starRingEnd ℂ n := by
  have := Complex.conj_cpow x (starRingEnd ℂ n) (Complex.slitPlane_arg_ne_pi hx)
  rw [Complex.conj_conj] at this
  exact this.symm

lemma differentiableAt_hbarA_aAmp {s : ℂ} (hs : s ∈ strip) : DifferentiableAt ℂ (hbarA aAmp) s := by
  have h : DifferentiableAt ℂ (genH aAmp) s :=
    (differentiableOn_genH amp_aAmp).differentiableAt (isOpen_strip.mem_nhds hs)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_strip.mem_nhds hs] with w hw using hbarA_of_mem_strip amp_aAmp hw

lemma gout_diff : DifferentiableOn ℂ Gout halfDisc := by
  intro z hz
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hcl : z ∈ closure halfDisc := subset_closure hz
  have hz1 : z ≠ 1 := (halfDisc_ne_special hz).2.2
  have hsInv : DifferentiableAt ℂ sInv z := differentiableAt_sInv hcl h1 h2
  have hA : DifferentiableAt ℂ (fun w => hbarA aAmp (sInv w)) z :=
    (differentiableAt_hbarA_aAmp (sInv_mem_strip hz)).comp z hsInv
  have hE : DifferentiableAt ℂ (fun w => Complex.exp (hbarA aAmp (sInv w))) z := hA.cexp
  have hP : DifferentiableAt ℂ (fun w : ℂ => (1 - w) ^ (1 / 2 : ℂ)) z :=
    DifferentiableAt.cpow_const (by fun_prop) (one_sub_mem_slit hcl hz1)
  have hD : DifferentiableAt ℂ (fun w : ℂ => (1 + w) ^ 2) z := by fun_prop
  have hq : DifferentiableAt ℂ qHat z :=
    differentiableOn_qHat.differentiableAt (isOpen_halfDisc.mem_nhds hz)
  have hqB : DifferentiableAt ℂ qBd z := by
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_halfDisc.mem_nhds hz] with w hw using qBd_of_mem hw
  have hQ : DifferentiableAt ℂ (fun w => (qBd w) ^ (-(1 / 4 : ℂ))) z :=
    DifferentiableAt.cpow_const hqB (by rw [qBd_of_mem hz]; exact qHat_mem_slit hz)
  have hDne : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (one_add_ne_zero' hcl)
  exact ((hE.mul hP).div hD hDne |>.mul hQ).differentiableWithinAt

lemma sInv_mem_closedStrip' {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) : sInv z ∈ closedStrip :=
  sInv_mem_closedStrip hz.1 (ne_of_mem_sing hz).1 (ne_of_mem_sing hz).2.1

lemma gout_cont : ContinuousOn Gout (closure halfDisc \ singPts) := by
  have hsub := sing_subset
  have hS : ContinuousOn sInv (closure halfDisc \ singPts) := continuousOn_sInv.mono hsub
  have hH : ContinuousOn (fun z => hbarA aAmp (sInv z)) (closure halfDisc \ singPts) :=
    (continuousOn_hbarA amp_aAmp).comp hS (fun z hz => sInv_mem_closedStrip' hz)
  have hE : ContinuousOn (fun z => Complex.exp (hbarA aAmp (sInv z))) (closure halfDisc \ singPts) :=
    hH.cexp
  have hP : ContinuousOn (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) (closure halfDisc \ singPts) :=
    continuousOn_one_sub_cpow.mono (fun z hz => hz.1)
  have hD : ContinuousOn (fun z : ℂ => (1 + z) ^ 2) (closure halfDisc \ singPts) := by fun_prop
  have hQ : ContinuousOn (fun z => (qBd z) ^ (-(1 / 4 : ℂ))) (closure halfDisc \ singPts) :=
    (continuousOn_qBd.mono hsub).cpow_const (fun z hz => qBd_mem_slit hz)
  exact ((hE.mul hP).div hD (fun z hz => pow_ne_zero 2 (one_add_ne_zero' hz.1))).mul hQ

lemma gout_conj {z : ℂ} (hz : z ∈ halfDisc) : Gout (starRingEnd ℂ z) = starRingEnd ℂ (Gout z) := by
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hz1 : z ≠ 1 := (halfDisc_ne_special hz).2.2
  have hcl : z ∈ closure halfDisc := subset_closure hz
  have hs : sInv z ∈ closedStrip := (strip_subset_closedStrip (sInv_mem_strip hz))
  unfold Gout
  rw [sInv_conj hz, hbarA_conj amp_aAmp hs, qBd_of_mem hz, qBd_of_mem (halfDisc_conj hz), qHat_conj hz]
  simp only [map_mul, map_div₀, map_pow, map_add, map_sub, map_one]
  rw [Complex.exp_conj, conj_cpow_slit (one_sub_mem_slit hcl hz1), conj_cpow_slit (qHat_mem_slit hz)]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have h4 : (starRingEnd ℂ) (4 : ℂ) = 4 := map_ofNat _ 4
  have e1 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, h2]
  have e4 : (starRingEnd ℂ) (1 / 4 : ℂ) = 1 / 4 := by rw [map_div₀, map_one, h4]
  rw [e1, map_neg, e4]
  simp only [map_sub, map_one]

lemma gout_ne_zero {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) : Gout z ≠ 0 := by
  have hz1 := (ne_of_mem_sing hz).2.2
  have h1 : (1 - z) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro h; exact absurd (sub_eq_zero.mp h).symm hz1
  unfold Gout
  have hq : (qBd z) ^ (-(1 / 4 : ℂ)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro h; exact absurd h (qBd_ne_zero hz)
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) h1)
    (pow_ne_zero 2 (one_add_ne_zero' hz.1))) hq

end FormalResearch.ModularBootstrap.FiveTerm

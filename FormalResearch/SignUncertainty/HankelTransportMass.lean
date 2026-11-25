module

public import FormalResearch.SignUncertainty.HankelTransportInt

/-!
# The mass hypotheses `(Q2)` for the Langer-disc density (`gt:7.7p` (b), (c), first half of (d); Step 2)

For a feasible `f` (`IsHankelFeasible c ε T f`, `M[f] = 1`) and `c` large, with `A = langerRadius c`,
`r_∞ = hankelRinf c`, `φ(x) = c ξ(x)`:
* sign: `Re Ψ̃(x) ≥ -r_∞` where `φ(x) ≥ T`;
* total mass: `∫_{-A}^A |Re Ψ̃| ≤ 1 + 2 A r_∞`;
* negative mass above `x_T`: `∫_{x_T}^A (Re Ψ̃)_- ≥ 1/2 - lobe(c) - 2 A r_∞` when `φ(x_T) ≥ T`;
* truncated total: `∫_{-R'}^A Re Ψ̃ ≤ lobe(c) + 2 A r_∞` when `φ(-R') ≥ T`,
with `lobe(c) = 8(e^{-5 (4.9·10⁻⁵ c^{2/3})^{3/2}} + e^{-c/25})` from `deep_lobe_mass_thm`.

Not formalised from `gt:7.7p` (d): the uniform bound across the cut `|Ψ̃| ≤ 3e^{1.5R₁+1.37R₁²}` on `|ũ| ≤ R₁`, the derivative
bound `|Ψ̃'| ≤ C₁(R₁)`, and the effective `C¹` stability conclusions (one- and two-level violators; they run through
`teb:quant_c1`).  The Lean `c`-thresholds (`5000`, and `3·10⁶` for the lobe statements, from `R ≥ 1` in `deep_lobe_mass_thm`)
are explicit where the paper's `c₁` is not.
-/

@[expose] public section

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty

/-- The deep-lobe mass bound at the edge of the Langer disc. -/
noncomputable def hankelLobe (c : ℝ) : ℝ :=
  8 * (Real.exp (-5 * (4.9e-5 * c ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c))

lemma hankelXi_radius_le {c : ℝ} (hc : 0 < c) :
    hankelXi c (langerRadius c) ≤ (1 - 4.9e-4) / π ^ 2 := by
  have hK0 := langerScale_pos hc
  have hx : |langerRadius c| ≤ langerScale c * 4.94e-4 := by
    rw [abs_of_pos (langerRadius_pos hc)]; rfl
  obtain ⟨hwc, hwre⟩ := chartYinv_real_point hc hx
  have hy0 : langerRadius c / langerScale c = 4.94e-4 := by
    unfold langerRadius; field_simp
  have hyn : ‖((4.94e-4 : ℝ) : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  unfold hankelXi
  rw [hy0] at hwc hwre ⊢
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  generalize chartYinv etaC ((4.94e-4 : ℝ) : ℂ) = w at hwc hwre hw hY ⊢
  have hwn : ‖w‖ ≤ 1e-3 := (mem_ball_zero_iff.1 hw).le
  have h1 := norm_chartY_add_le langerEta_etaC hwn
  rw [hY] at h1
  set wr := w.re with hwr
  have e : (((4.94e-4 : ℝ) : ℂ)) + w = ((4.94e-4 + wr : ℝ) : ℂ) := by rw [hwc]; push_cast; ring
  have e2 : ‖w‖ = |wr| := by rw [hwc, Complex.norm_real, Real.norm_eq_abs]
  rw [e, Complex.norm_real, Real.norm_eq_abs, e2] at h1
  have h3 := abs_le.1 (h1.trans (by nlinarith [abs_le.1 hwre, abs_nonneg wr] : 1.9e-3 * |wr| ≤ 1e-6))
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith [h3.1]

lemma rpow_two_thirds_ge {c : ℝ} (hc : 3e6 ≤ c) : 2.05e4 ≤ c ^ (2 / 3 : ℝ) := by
  have hc0 : 0 < c := by linarith
  have h3 : (c ^ (2 / 3 : ℝ)) ^ 3 = c ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  by_contra h
  push Not at h
  have hpos : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
  have := pow_lt_pow_left₀ h hpos (by norm_num : (3 : ℕ) ≠ 0)
  rw [h3] at this
  nlinarith

/-- The lobe below the Langer disc carries mass `≤ hankelLobe c` (`M = 1`). -/
lemma hankel_lobe_small {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) :
    ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u ≤ hankelLobe c := by
  have hc0 : 0 < c := by linarith
  have hpi : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpipos : 0 < π := Real.pi_pos
  set R : ℝ := 4.9e-5 * c ^ (2 / 3 : ℝ) with hR
  have hR1 : 1 ≤ R := by have := rpow_two_thirds_ge hc; rw [hR]; nlinarith
  have hRc : R * c ^ (1 / 3 : ℝ) = 4.9e-5 * c := by
    rw [hR, mul_assoc, ← Real.rpow_add hc0]; norm_num
  have hU : c * hankelXi c (langerRadius c) ≤ c / π ^ 2 - R * c ^ (1 / 3 : ℝ) := by
    have h1 := hankelXi_radius_le hc0
    have h2 := mul_le_mul_of_nonneg_left h1 hc0.le
    rw [hRc]
    have h3 : c * ((1 - 4.9e-4) / π ^ 2) = c / π ^ 2 - 4.9e-4 * c / π ^ 2 := by ring
    have h4 : 4.9e-5 * c ≤ 4.9e-4 * c / π ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hdeep := deep_lobe_mass_thm (by linarith : 56 ≤ c) hf hε hR1
  rw [hM] at hdeep
  have hint := abs_mul_rho0_integrableOn hc0 hf.int
  have hmono : ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u ≤
      ∫ u in Ioo (0 : ℝ) (c / π ^ 2 - R * c ^ (1 / 3 : ℝ)), |f u| * hankelRho0 c u := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_set (hint.mono_set (fun u hu => hu.1)) ?_
      (Filter.Eventually.of_forall fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 hU⟩)
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun u hu =>
      mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 (le_of_lt hu.1))
  refine hmono.trans (hdeep.trans ?_)
  unfold hankelLobe
  rw [hR, mul_one]

/-- Leading term of `Re Ψ̃` on the real axis: `-(c ξ') (ρ₀ f)(cξ)`. -/
noncomputable def hankelPsiLead (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(c * hankelXiD c x) * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))

lemma hankelPsiR_sub_Q_le {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x : ℝ} (hx : |x| ≤ langerRadius c) :
    |hankelPsiR c f x - hankelPsiLead c f x| ≤ hankelRinf c := by
  have := hankel_transport_pointwise hc hf hε hM (x := x) hx
  unfold hankelPsiR hankelPsiLead hankelRinf
  convert this using 2; ring

lemma continuousOn_hankelQ {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (hankelPsiLead c f) (Icc (-(langerRadius c)) (langerRadius c)) := by
  have := (continuousOn_hankel_term hc hf).neg
  refine this.congr fun x _ => ?_
  simp only [Pi.neg_apply]; unfold hankelPsiLead; ring

/-- Transfer of a positively homogeneous 1-Lipschitz function `G` (`|·|`, `max 0 (-·)`, `id`):
`|∫_a^b G(Re Ψ̃) - ∫_{cξ(b)}^{cξ(a)} ρ₀ G(f)| ≤ (b-a) r_∞`. -/
theorem hankel_transport_G {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {G : ℝ → ℝ} (hGc : Continuous G)
    (hGl : ∀ s t, |G s - G t| ≤ |s - t|) (hGh : ∀ l v : ℝ, 0 ≤ l → G (l * v) = l * G v)
    {a b : ℝ} (ha : |a| ≤ langerRadius c) (hb : |b| ≤ langerRadius c) (hab : a ≤ b) :
    |(∫ x in a..b, G (hankelPsiR c f x)) -
        ∫ u in (c * hankelXi c b)..(c * hankelXi c a), hankelRho0 c u * G (f u)| ≤
      (b - a) * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hmem : ∀ x ∈ Icc a b, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith [abs_le.1 ha |>.1, hx.1], by linarith [abs_le.1 hb |>.2, hx.2]⟩
  have hsub : Icc a b ⊆ Icc (-(langerRadius c)) (langerRadius c) := fun x hx => abs_le.1 (hmem x hx)
  have hP : ContinuousOn (fun x => G (hankelPsiR c f x)) (Icc a b) :=
    hGc.comp_continuousOn ((continuousOn_hankelPsiR hc0 hf).mono hsub)
  have hQ : ContinuousOn (fun x => G (hankelPsiLead c f x)) (Icc a b) :=
    hGc.comp_continuousOn ((continuousOn_hankelQ hc0 hf).mono hsub)
  have hQeq : ∀ x ∈ Icc a b, G (hankelPsiLead c f x) =
      -((hankelRho0 c (c * hankelXi c x) * G (f (c * hankelXi c x))) * (c * hankelXiD c x)) := by
    intro x hx
    have hxa := hmem x hx
    have hxi : 0 < c * hankelXi c x := mul_pos hc0 (hankelXi_pos hc0 hxa)
    have hD := hankelXiD_neg hc0 hxa
    have hl : 0 ≤ -(c * hankelXiD c x) * hankelRho0 c (c * hankelXi c x) :=
      mul_nonneg (by nlinarith) (hankelRho0_nonneg hc0 hxi.le)
    unfold hankelPsiLead
    rw [← mul_assoc, hGh _ _ hl]; ring
  have hsubst := hankel_subst hc0 ha hb hab (fun u => hankelRho0 c u * G (f u))
  have hint2 : ∫ x in a..b, G (hankelPsiLead c f x) =
      ∫ u in (c * hankelXi c b)..(c * hankelXi c a), hankelRho0 c u * G (f u) := by
    rw [intervalIntegral.integral_congr (g := fun x => -((hankelRho0 c (c * hankelXi c x) * G (f (c * hankelXi c x))) * (c * hankelXiD c x)))
      (fun x hx => hQeq x (by rwa [uIcc_of_le hab] at hx)), intervalIntegral.integral_neg, hsubst,
      intervalIntegral.integral_symm, neg_neg]
  rw [← hint2, ← intervalIntegral.integral_sub (hP.intervalIntegrable_of_Icc hab)
    (hQ.intervalIntegrable_of_Icc hab)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x => G (hankelPsiR c f x) - G (hankelPsiLead c f x)) (C := hankelRinf c) (fun x hx => by
      rw [uIoc_of_le hab] at hx
      have hx' : |x| ≤ langerRadius c := hmem x ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs]
      exact (hGl _ _).trans (hankelPsiR_sub_Q_le hc hf hε hM hx'))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
  linarith

lemma hankelG_abs (s t : ℝ) : abs (|s| - |t|) ≤ |s - t| := abs_abs_sub_abs_le_abs_sub s t

lemma hankelG_neg (s t : ℝ) : |max 0 (-s) - max 0 (-t)| ≤ |s - t| := by
  rw [max_comm 0 (-s), max_comm 0 (-t)]
  refine (abs_max_sub_max_le_abs (-s) (-t) 0).trans ?_
  rw [← abs_neg]; ring_nf; exact le_rfl

lemma hankelG_neg_hom (l v : ℝ) (hl : 0 ≤ l) : max 0 (-(l * v)) = l * max 0 (-v) := by
  have := mul_max_of_nonneg 0 (-v) hl
  rw [this]; simp

lemma hankelRinf_nonneg {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) : 0 ≤ hankelRinf c :=
  (abs_nonneg _).trans (hankelPsiR_sub_Q_le hc hf hε hM (x := 0)
    (by rw [abs_zero]; exact (langerRadius_pos (by linarith)).le))

/-- Sign: where `f ≥ 0` at the Hankel point, `Re Ψ̃ ≥ -r_∞`. -/
theorem hankel_psi_sign {c ε T : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x : ℝ} (hx : |x| ≤ langerRadius c)
    (hT : T ≤ c * hankelXi c x) : -hankelRinf c ≤ hankelPsiR c f x := by
  have hc0 : 0 < c := by linarith
  have h1 := (abs_le.1 (hankelPsiR_sub_Q_le hc hf.toIsHankelEigenfn hε hM hx)).1
  have hQ : 0 ≤ hankelPsiLead c f x := by
    unfold hankelPsiLead
    refine mul_nonneg (by have := hankelXiD_neg hc0 hx; nlinarith) (mul_nonneg ?_ (hf.tail_nonneg _ hT))
    exact hankelRho0_nonneg hc0 (mul_pos hc0 (hankelXi_pos hc0 hx)).le
  linarith

/-- `∫_p^q g ≤ ∫_{Ioi 0} g` for nonnegative `g` and `0 ≤ p ≤ q`. -/
lemma hankel_ii_le_set {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hnn : ∀ u, 0 < u → 0 ≤ g u)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) : ∫ u in p..q, g u ≤ ∫ u in Ioi (0 : ℝ), g u := by
  rw [intervalIntegral.integral_of_le hpq]
  refine setIntegral_mono_set hg ?_ (Filter.Eventually.of_forall fun u hu => ?_)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi hnn
  · exact lt_of_le_of_lt hp hu.1

/-- `∫_{Ioi 0} g = ∫_{Ioc 0 p} g + ∫_p^q g + ∫_{Ioi q} g`. -/
lemma hankel_split3 {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    ∫ u in Ioi (0 : ℝ), g u =
      (∫ u in Ioc (0 : ℝ) p, g u) + (∫ u in p..q, g u) + ∫ u in Ioi q, g u := by
  have h1 : Ioi (0 : ℝ) = Ioc 0 p ∪ Ioi p := (Set.Ioc_union_Ioi_eq_Ioi hp).symm
  have h2 : Ioi p = Ioc p q ∪ Ioi q := (Set.Ioc_union_Ioi_eq_Ioi hpq).symm
  have hI1 : IntegrableOn g (Ioc 0 p) := hg.mono_set (fun u hu => hu.1)
  have hIp : IntegrableOn g (Ioi p) := hg.mono_set (Ioi_subset_Ioi hp)
  have hI2 : IntegrableOn g (Ioc p q) := hIp.mono_set (fun u hu => hu.1)
  have hI3 : IntegrableOn g (Ioi q) := hIp.mono_set (Ioi_subset_Ioi hpq)
  conv_lhs => rw [h1]
  rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hIp, h2,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI2 hI3,
    intervalIntegral.integral_of_le hpq]
  ring

lemma hankel_gA_int {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IntegrableOn (fun u => hankelRho0 c u * |f u|) (Ioi 0) := by
  simpa only [mul_comm] using abs_mul_rho0_integrableOn hc hf.int

lemma hankel_gF_int {c ε : ℝ} {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IntegrableOn (fun u => hankelRho0 c u * f u) (Ioi 0) := by
  simpa only [mul_comm] using hf.int

lemma hankel_gA_integral {c : ℝ} {f : ℝ → ℝ} (hM : hankelMass c f = 1) :
    ∫ u in Ioi (0 : ℝ), hankelRho0 c u * |f u| = 1 := by
  rw [← hM]; unfold hankelMass; simp only [mul_comm]

lemma hankel_gF_integral {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ∫ u in Ioi (0 : ℝ), hankelRho0 c u * f u = ε * f 0 := by
  have := hf.eigen 0 (mem_Ici.2 le_rfl)
  rw [besselHankelTransform_zero hc] at this
  rw [← this]; simp only [mul_comm]

lemma hankel_gN_eq (c : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    hankelRho0 c u * max 0 (-f u) = (hankelRho0 c u * |f u| - hankelRho0 c u * f u) / 2 := by
  rcases le_total 0 (f u) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring

lemma hankel_gN_int {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    IntegrableOn (fun u => hankelRho0 c u * max 0 (-f u)) (Ioi 0) := by
  simp only [hankel_gN_eq]
  exact ((hankel_gA_int hc hf).sub (hankel_gF_int hf)).div_const 2

lemma hankel_gN_integral {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hM : hankelMass c f = 1) :
    ∫ u in Ioi (0 : ℝ), hankelRho0 c u * max 0 (-f u) = (1 - ε * f 0) / 2 := by
  simp only [hankel_gN_eq]
  rw [integral_div, integral_sub (hankel_gA_int hc hf) (hankel_gF_int hf), hankel_gA_integral hM,
    hankel_gF_integral hc hf]

/-- `c ξ` is decreasing on the Langer disc. -/
lemma hankel_phi_anti {c : ℝ} (hc0 : 0 < c) {a b : ℝ} (ha : |a| ≤ langerRadius c)
    (hb : |b| ≤ langerRadius c) (hab : a ≤ b) : c * hankelXi c b ≤ c * hankelXi c a := by
  have hdec := hankel_subst hc0 ha hb hab (fun _ => 1)
  have hneg : ∀ x ∈ Icc a b, c * hankelXiD c x ≤ 0 := fun x hx =>
    mul_nonpos_of_nonneg_of_nonpos hc0.le
      (hankelXiD_neg hc0 (abs_le.2 ⟨by linarith [(abs_le.1 ha).1, hx.1], by linarith [(abs_le.1 hb).2, hx.2]⟩)).le
  have : ∫ x in a..b, (1 : ℝ) * (c * hankelXiD c x) ≤ 0 := by
    have h0 := intervalIntegral.integral_nonneg (μ := volume) (a := a) (b := b)
      (f := fun x => -((1 : ℝ) * (c * hankelXiD c x))) hab (fun x hx => by simpa using hneg x hx)
    rw [intervalIntegral.integral_neg] at h0
    linarith
  rw [hdec] at this
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  linarith

/-- Negative mass of the Langer-disc density above `x₀` (the `(Q2)` lower bound). -/
theorem hankel_psi_neg_mass {c ε T : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x₀ : ℝ} (hx₀ : |x₀| ≤ langerRadius c)
    (hT : T ≤ c * hankelXi c x₀) :
    1 / 2 - hankelLobe c - 2 * langerRadius c * hankelRinf c ≤
      ∫ x in x₀..(langerRadius c), max 0 (-hankelPsiR c f x) := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have hx0A : x₀ ≤ langerRadius c := (abs_le.1 hx₀).2
  have hr := hankelRinf_nonneg hc5 hfe hε hM
  have hG := hankel_transport_G hc5 hfe hε hM (G := fun v => max 0 (-v))
    (continuous_const.max continuous_neg) hankelG_neg hankelG_neg_hom hx₀ hAA hx0A
  have hpA : 0 < c * hankelXi c (langerRadius c) := mul_pos hc0 (hankelXi_pos hc0 hAA)
  have hmono : c * hankelXi c (langerRadius c) ≤ c * hankelXi c x₀ :=
    hankel_phi_anti hc0 hx₀ hAA hx0A
  have hgN := hankel_gN_int hc0 hfe
  have hsplit := hankel_split3 hgN hpA.le hmono
  have hzero : ∫ u in Ioi (c * hankelXi c x₀), hankelRho0 c u * max 0 (-f u) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [max_eq_left (by linarith [hf.tail_nonneg u (hT.trans (le_of_lt hu))]), mul_zero]
  have hlobe : ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * max 0 (-f u) ≤
      hankelLobe c := by
    refine le_trans ?_ (hankel_lobe_small hc hfe hε hM)
    have hcomm : (∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u) =
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| := by
      simp only [mul_comm]
    rw [hcomm]
    exact setIntegral_mono_on (hgN.mono_set (fun u hu => hu.1))
      ((hankel_gA_int hc0 hfe).mono_set (fun u hu => hu.1)) measurableSet_Ioc fun u hu =>
      mul_le_mul_of_nonneg_left (max_le (abs_nonneg _) (neg_le_abs _)) (hankelRho0_nonneg hc0 hu.1.le)
  have hhalf := hankel_gN_integral hc0 hfe hM
  have horig : ε * f 0 ≤ 0 := hf.origin_sign
  beta_reduce at hG
  rw [abs_le] at hG
  have h2 : (langerRadius c - x₀) * hankelRinf c ≤ 2 * langerRadius c * hankelRinf c :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 hx₀).1]) hr
  linarith [hG.1, hG.2]

/-- Total mass of `Re Ψ̃` over the Langer disc (`(Q2)` upper bound). -/
theorem hankel_psi_abs_mass {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) :
    ∫ x in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f x| ≤
      1 + 2 * langerRadius c * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have hmA : |-(langerRadius c)| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hA]
  have hG := hankel_transport_G hc hf hε hM (G := fun v => |v|) continuous_abs hankelG_abs
    (fun l v hl => by rw [abs_mul, abs_of_nonneg hl]) hmA hAA (by linarith)
  beta_reduce at hG
  rw [abs_le] at hG
  have hpA : 0 < c * hankelXi c (langerRadius c) := mul_pos hc0 (hankelXi_pos hc0 hAA)
  have hle := hankel_ii_le_set (hankel_gA_int hc0 hf) (fun u hu => mul_nonneg
    (hankelRho0_nonneg hc0 hu.le) (abs_nonneg _)) hpA.le
    (hankel_phi_anti hc0 hmA hAA (by linarith))
  rw [hankel_gA_integral hM] at hle
  linarith [hG.1, hG.2]

/-- Upper bound for the total mass of `Re Ψ̃` on `[a, A]` where `f ≥ 0` at the Hankel point of `a`. -/
theorem hankel_psi_total_upper {c ε T : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {a : ℝ} (ha : |a| ≤ langerRadius c)
    (hT : T ≤ c * hankelXi c a) :
    ∫ x in a..(langerRadius c), hankelPsiR c f x ≤ hankelLobe c + 2 * langerRadius c * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have haA : a ≤ langerRadius c := (abs_le.1 ha).2
  have hr := hankelRinf_nonneg hc5 hfe hε hM
  have hG := hankel_transport_G hc5 hfe hε hM (G := fun v => v) continuous_id
    (fun s t => le_rfl) (fun l v hl => rfl) ha hAA haA
  beta_reduce at hG
  rw [abs_le] at hG
  have hpA : 0 < c * hankelXi c (langerRadius c) := mul_pos hc0 (hankelXi_pos hc0 hAA)
  have hmono := hankel_phi_anti hc0 ha hAA haA
  have hgF := hankel_gF_int hfe
  have hsplit := hankel_split3 hgF hpA.le hmono
  have hpos : 0 ≤ ∫ u in Ioi (c * hankelXi c a), hankelRho0 c u * f u := by
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => mul_nonneg
      (hankelRho0_nonneg hc0 (le_trans (mul_pos hc0 (hankelXi_pos hc0 ha)).le (le_of_lt hu)))
      (hf.tail_nonneg u (hT.trans (le_of_lt hu)))
  have hlobe : -hankelLobe c ≤ ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * f u := by
    have hcomm : (∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), |f u| * hankelRho0 c u) =
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| := by
      simp only [mul_comm]
    have h1 := hankel_lobe_small hc hfe hε hM
    rw [hcomm] at h1
    have h2 : -∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * |f u| ≤
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c (langerRadius c)), hankelRho0 c u * f u := by
      rw [← integral_neg]
      exact setIntegral_mono_on ((hankel_gA_int hc0 hfe).mono_set (fun u (hu : u ∈ Ioc (0 : ℝ) _) => hu.1) |>.neg)
        (hgF.mono_set (fun u hu => hu.1)) measurableSet_Ioc fun u hu => by
          have := mul_le_mul_of_nonneg_left (neg_abs_le (f u)) (hankelRho0_nonneg hc0 hu.1.le)
          linarith
    linarith
  rw [hankel_gF_integral hc0 hfe] at hsplit
  have horig : ε * f 0 ≤ 0 := hf.origin_sign
  have h2 : (langerRadius c - a) * hankelRinf c ≤ 2 * langerRadius c * hankelRinf c :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_le.1 ha).1]) hr
  linarith [hG.1, hG.2]

/-- info: 'FormalResearch.SignUncertainty.hankelXi_radius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelXi_radius_le

/-- info: 'FormalResearch.SignUncertainty.hankel_lobe_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_lobe_small

/-- info: 'FormalResearch.SignUncertainty.hankel_transport_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_transport_G

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_sign

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_abs_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_abs_mass

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_neg_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_neg_mass

/-- info: 'FormalResearch.SignUncertainty.hankel_psi_total_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_psi_total_upper

end FormalResearch.SignUncertainty

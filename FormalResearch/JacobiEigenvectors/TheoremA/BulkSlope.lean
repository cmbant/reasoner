module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkWindows
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero

/-!
# Paper J, Layer 2: the slope of the action on a bulk block (`hslope` of the assembly, L2.S6)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`, paragraph "Density" ("`S^I_0` is `C^1` with `partial_X S^I_0 <= -c < 0`, on `J_nu` because `S_0' = -int_{u_-}^{u_+} T^{-1/2} du`"),
and `lem:smo-bulkphase` (3) ("`Phi := S_0`, strictly decreasing with `|S_0'| ~ 1`"); `lem:tha-geom` (c) (the oscillatory overlap `[c', c]`), `theta_margin` of `BulkWeberChart`.

## Proved here (axiom-pinned)

* `sub_le_arccos_sub`: `arccos` decreases at least as fast as the identity on `[-1, 1]` (`arccos' <= -1`; from `arcsin = (sin)^{-1}` and `sin` 1-Lipschitz).
* `actInt_mono_X`: the action integrand is nonincreasing in `X` for every `u` (`E_0 <= 0` gives a constant, else `arccos` is antitone).
* `action_decrease_on_overlap`: `S_0(X_2) <= S_0(X_1) - (c - c') (X_2 - X_1) / (2 S)` for `X_1 <= X_2` when the margin `|X - B_0| <= (1 - eps) 2 sqrt E_0` holds on `[c', c]` and `sqrt E_0 <= S` there.
* `bulk_slope` (**`WindowPhase.slope` of a bulk block**): from the standing assumptions `StdAssump` of the frozen family on `P` (compactness of `P`, `G_0` bounded, `(H1)`), the `C^1` regularity of `Sigma_0` in `X` (`Sigma_reg`),
  `Sigma_0 = S_0` at `t = 0` and `theta_margin`: `deriv_X Sigma_0(mu; X, 0) <= -c` on the open block, with `c = (c - c') / (2 S) > 0` uniform in `mu in K`.

## Differences from the paper

The paper obtains `S_0' = -int T^{-1/2}` by differentiating under the integral through the turning points; here only the one-sided bound `S_0' <= -c` is needed and it is obtained from monotonicity of the integrand plus the
margin on the overlap (so no differentiation under the integral); differentiability of `S_0` in `X` is that of `Sigma_0` (`BulkPhaseInputs.Sigma_reg`, `C^{2M+1}` with `2M+1 >= 1`).

## Not formalised

The equality `S_0' = -int T^{-1/2}`; the slope of the soft windows (`I_+-`: `partial_alpha mu_0(0,0) > 0`, `SoftPhaseInputs`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set Filter Topology MeasureTheory FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

/-- `arccos' <= -1` on `[-1, 1]`: `b - a <= arccos a - arccos b` for `-1 <= a <= b <= 1`. -/
lemma sub_le_arccos_sub {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    b - a ≤ Real.arccos a - Real.arccos b := by
  have h1 : Real.arccos a - Real.arccos b = Real.arcsin b - Real.arcsin a := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]; ring
  rw [h1]
  have hsa := Real.sin_arcsin ha (hab.trans hb)
  have hsb := Real.sin_arcsin (ha.trans hab) hb
  have hmono : Real.arcsin a ≤ Real.arcsin b := Real.arcsin_le_arcsin hab
  have := Real.abs_sin_sub_sin_le (Real.arcsin b) (Real.arcsin a)
  rw [hsb, hsa, abs_of_nonneg (by linarith : 0 ≤ b - a), abs_of_nonneg (by linarith : 0 ≤ Real.arcsin b - Real.arcsin a)] at this
  exact this

/-- The action integrand is nonincreasing in `X`. -/
lemma actInt_mono_X (L : ℝ) (G0 B0 : ℝ → ℝ) {X1 X2 : ℝ} (h : X1 ≤ X2) (u : ℝ) :
    actInt L G0 B0 X2 u ≤ actInt L G0 B0 X1 u := by
  unfold actInt
  apply Real.arccos_le_arccos
  by_cases hd : Real.sqrt (E0 L G0 u) = 0
  · simp [hd]
  · have hpos : 0 < 2 * Real.sqrt (E0 L G0 u) := by
      have := lt_of_le_of_ne (Real.sqrt_nonneg (E0 L G0 u)) (Ne.symm hd)
      positivity
    exact div_le_div_of_nonneg_right (by linarith) hpos.le

/-- **Decrease of the action over an interval of energies with the margin on `[c', c]`.** -/
lemma action_decrease_on_overlap {L : ℝ} {G0 B0 : ℝ → ℝ} {g : ℝ} (hL : 0 < L) (hyp : Hyp L G0 B0 g)
    (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L))
    {c' c ε S : ℝ} (hε0 : 0 < ε) (hc' : 0 < c') (hcc : c' < c) (hcL : c < L) (hS : 0 < S)
    (hSb : ∀ u ∈ Icc c' c, Real.sqrt (E0 L G0 u) ≤ S)
    {X1 X2 : ℝ} (h12 : X1 ≤ X2)
    (hm1 : ∀ v ∈ Icc c' c, |X1 - B0 v| ≤ (1 - ε) * (2 * Real.sqrt (E0 L G0 v)))
    (hm2 : ∀ v ∈ Icc c' c, |X2 - B0 v| ≤ (1 - ε) * (2 * Real.sqrt (E0 L G0 v))) :
    (∫ u in (0 : ℝ)..L, actInt L G0 B0 X2 u) ≤
      (∫ u in (0 : ℝ)..L, actInt L G0 B0 X1 u) - (c - c') * ((X2 - X1) / (2 * S)) := by
  have hi1 := intervalIntegrable_arccos_action hL hyp hG2 hB2 X1
  have hi2 := intervalIntegrable_arccos_action hL hyp hG2 hB2 X2
  have hgi : IntervalIntegrable (fun u => actInt L G0 B0 X1 u - actInt L G0 B0 X2 u) volume 0 L := hi1.sub hi2
  have hdiff : (∫ u in (0 : ℝ)..L, actInt L G0 B0 X1 u) - (∫ u in (0 : ℝ)..L, actInt L G0 B0 X2 u) =
      ∫ u in (0 : ℝ)..L, (actInt L G0 B0 X1 u - actInt L G0 B0 X2 u) := (intervalIntegral.integral_sub hi1 hi2).symm
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc (0 : ℝ) L)] (fun u => actInt L G0 B0 X1 u - actInt L G0 B0 X2 u) :=
    Filter.Eventually.of_forall (fun u => sub_nonneg.mpr (actInt_mono_X L G0 B0 h12 u))
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) (a := c') (b := c) (c := 0) (d := L)
    hc'.le hcc.le hcL.le hnn hgi
  have hpt : ∀ v ∈ Icc c' c, (X2 - X1) / (2 * S) ≤ actInt L G0 B0 X1 v - actInt L G0 B0 X2 v := by
    intro v hv
    have hvmem : v ∈ Ioo 0 L := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hE := HypMorse.E0_pos hyp.G0_lb hyp.gstar_pos hvmem
    have hs := Real.sqrt_pos.mpr hE
    have hden : 0 < 2 * Real.sqrt (E0 L G0 v) := by positivity
    have hle : 2 * Real.sqrt (E0 L G0 v) ≤ 2 * S := by linarith [hSb v hv]
    have ha1 := abs_le.mp (hm1 v hv)
    have ha2 := abs_le.mp (hm2 v hv)
    unfold actInt
    set d := 2 * Real.sqrt (E0 L G0 v) with hd
    have hm2le : (X2 - B0 v) / d ≤ 1 := by
      rw [div_le_iff₀ hden]
      nlinarith [ha2.2, mul_pos hε0 hden]
    have hm1ge : -1 ≤ (X1 - B0 v) / d := by
      rw [le_div_iff₀ hden]
      nlinarith [ha1.1, mul_pos hε0 hden]
    have hle12 : (X1 - B0 v) / d ≤ (X2 - B0 v) / d := div_le_div_of_nonneg_right (by linarith) hden.le
    have key := sub_le_arccos_sub hm1ge hle12 hm2le
    have e : (X2 - B0 v) / d - (X1 - B0 v) / d = (X2 - X1) / d := by field_simp; ring
    have hq : (X2 - X1) / (2 * S) ≤ (X2 - X1) / d :=
      div_le_div_of_nonneg_left (by linarith) hden hle
    linarith
  have hconst : (c - c') * ((X2 - X1) / (2 * S)) ≤ ∫ u in c'..c, (actInt L G0 B0 X1 u - actInt L G0 B0 X2 u) := by
    have hci : IntervalIntegrable (fun u => actInt L G0 B0 X1 u - actInt L G0 B0 X2 u) volume c' c :=
      hgi.mono_set (by rw [uIcc_of_le hcc.le, uIcc_of_le hL.le]; exact Icc_subset_Icc hc'.le hcL.le)
    have := intervalIntegral.integral_mono_on hcc.le (intervalIntegrable_const (c := (X2 - X1) / (2 * S))) hci hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    exact this
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.action_decrease_on_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.action_decrease_on_overlap

/-- **`WindowPhase.slope` of a bulk block** (see the module docstring): `deriv_X Sigma_0(mu; X, 0) <= -c` on the open block `(Jlo, Jhi)`, uniformly in `mu in K`. -/
theorem bulk_slope {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ}
    {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ} {CL : BulkWeberChart F P Jlo Jhi (max M 1) U V}
    {CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V}
    (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) (ht0 : 0 < t0) (hP : ∀ μ ∈ K, (μ, (0 : ℝ)) ∈ P)
    {Kd r : ℕ} (hs : StdAssump F P Kd r) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo Jlo Jhi, deriv (fun X' => PI.Sigma μ 0 X' 0) X ≤ -c := by
  obtain ⟨hPc, hEK, g, hg⟩ := hs
  obtain ⟨ε, hε0, hε1, hmarg⟩ := CL.theta_margin
  obtain ⟨hc'0, hc'c, hσ, hcL, -⟩ := CL.consts_pos
  have hbud := hEK.budget
  have hr22 : 14 ≤ r := by unfold regBudget at hbud; omega
  have hG0 := hEK.reg 0 (Nat.zero_le _)
  simp only [mul_zero, Nat.sub_zero] at hG0
  obtain ⟨MG, hMG⟩ := jet_bound hPc hG0.1 (k := 0) (Nat.zero_le _)
  set S : ℝ := Real.sqrt (F.L ^ 2 * (|MG| + 1)) with hSdef
  have hL := F.L_pos
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hSb : ∀ μ ∈ K, ∀ u ∈ Icc CL.c' CL.c, Real.sqrt (E0 F.L (F.G 0 (μ, 0)) u) ≤ S := by
    intro μ hμ u hu
    have hu0 : 0 ≤ u := by linarith [hu.1]
    have huL : u ≤ F.L := by linarith [hu.2]
    have hG : |F.G 0 (μ, 0) u| ≤ MG := by
      simpa [iteratedDerivWithin_zero] using hMG (μ, 0) (hP μ hμ) u ⟨hu0, huL⟩
    refine Real.sqrt_le_sqrt ?_
    unfold E0
    have h1 : u * (F.L - u) ≤ F.L ^ 2 := by nlinarith
    have h2 : 0 ≤ u * (F.L - u) := mul_nonneg hu0 (by linarith)
    calc u * (F.L - u) * F.G 0 (μ, 0) u ≤ u * (F.L - u) * |F.G 0 (μ, 0) u| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h2
      _ ≤ F.L ^ 2 * (|MG| + 1) := by
          have : |F.G 0 (μ, 0) u| ≤ |MG| + 1 := by linarith [le_abs_self MG]
          exact mul_le_mul h1 this (abs_nonneg _) (by positivity)
  refine ⟨(CL.c - CL.c') / (2 * S), by have := sub_pos.mpr hc'c; positivity, ?_⟩
  intro μ hμ X hX
  have hμ0 := hP μ hμ
  have hyp := hg _ hμ0
  have hG2 : ContDiffOn ℝ 2 (F.G 0 (μ, 0)) (Icc 0 F.L) := by
    refine (hG0.1.1 _ hμ0).of_le ?_
    exact_mod_cast (by omega : 2 ≤ r)
  have hB2 : ContDiffOn ℝ 2 (F.B 0 (μ, 0)) (Icc 0 F.L) := by
    refine (hG0.2.1 _ hμ0).of_le ?_
    exact_mod_cast (by omega : 2 ≤ r)
  -- Sigma_0 is the action on the block
  have hmem : ∀ X' ∈ Icc Jlo Jhi, PI.Sigma μ 0 X' 0 = ∫ u in (0 : ℝ)..F.L, actInt F.L (F.G 0 (μ, 0)) (F.B 0 (μ, 0)) X' u := by
    intro X' hX'
    have := PI.Sigma_zero μ hμ X' hX' 0 ⟨by linarith, ht0.le⟩
    rw [this]
    rfl
  -- the decrease inequality
  have hdec : ∀ X1 ∈ Icc Jlo Jhi, ∀ X2 ∈ Icc Jlo Jhi, X1 ≤ X2 →
      PI.Sigma μ 0 X2 0 ≤ PI.Sigma μ 0 X1 0 - (CL.c - CL.c') * ((X2 - X1) / (2 * S)) := by
    intro X1 h1 X2 h2 h12
    rw [hmem X1 h1, hmem X2 h2]
    exact action_decrease_on_overlap F.L_pos hyp hG2 hB2 hε0 hc'0 hc'c (by linarith) hS (hSb μ hμ) h12
      (fun v hv => hmarg _ hμ0 X1 h1 v hv) (fun v hv => hmarg _ hμ0 X2 h2 v hv)
  -- differentiability of X' ↦ Sigma_0(X', 0) at X
  have hdiffAt : DifferentiableAt ℝ (fun X' => PI.Sigma μ 0 X' 0) X := by
    have hreg := PI.Sigma_reg μ hμ 0 (Nat.zero_le _)
    have hnhds : Icc Jlo Jhi ×ˢ Icc (-t0) t0 ∈ 𝓝 (X, (0 : ℝ)) :=
      prod_mem_nhds (Icc_mem_nhds hX.1 hX.2) (Icc_mem_nhds (by linarith) ht0)
    have hca : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) (X, 0) :=
      (hreg.contDiffAt hnhds).of_le (by exact_mod_cast (by omega : 1 ≤ 2 * M + 1))
    have hda : DifferentiableAt ℝ (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) (X, 0) :=
      hca.differentiableAt (by norm_num)
    have hemb : DifferentiableAt ℝ (fun x : ℝ => (x, (0 : ℝ))) X := by fun_prop
    exact DifferentiableAt.comp (𝕜 := ℝ) X (g := fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) hda hemb
  have hder := hdiffAt.hasDerivAt
  have hlim := hder.tendsto_slope_zero_right
  refine le_of_tendsto hlim ?_
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < Jhi - X ∧ 0 < s := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), s < Jhi - X := Iio_mem_nhds (by linarith [hX.2])
    exact (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  filter_upwards [hev] with s hs
  obtain ⟨hs1, hs0⟩ := hs
  have hX2 : X + s ∈ Icc Jlo Jhi := ⟨by linarith [hX.1], by linarith⟩
  have := hdec X ⟨hX.1.le, hX.2.le⟩ (X + s) hX2 (by linarith)
  have hq : (PI.Sigma μ 0 (X + s) 0 - PI.Sigma μ 0 X 0) ≤ -((CL.c - CL.c') / (2 * S)) * s := by
    have e : (CL.c - CL.c') * ((X + s - X) / (2 * S)) = (CL.c - CL.c') / (2 * S) * s := by field_simp; ring
    linarith
  simp only [smul_eq_mul]
  rw [inv_mul_le_iff₀ hs0]
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_slope

end FormalResearch.JacobiEigenvectors.TheoremA

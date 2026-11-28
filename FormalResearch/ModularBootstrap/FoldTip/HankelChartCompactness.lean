module

public import FormalResearch.ModularBootstrap.FoldTip.ChartCompactness
public import FormalResearch.SignUncertainty.CEShellReduction
public import FormalResearch.SignUncertainty.HbMultilevelDefs
public import FormalResearch.SignUncertainty.RadialCompactnessProof

/-!
# Hankel Chart Compactness and All-Level Rigidity (`FT-CC` Hankel Instance)

Instantiates `ChartCompactness` (`FoldTip/ChartCompactness.lean`) for Paper I's Hankel
multilevel problem (`SignUncertainty`), importing the Paper I definitions and proved
compactness (`radial_compactness`, `deep_lobe_mass_thm`) without modifying any file in
`FormalResearch/SignUncertainty/`.

## Main results
- `shellHBToHermiteBiehlerData`: projection from Paper I's `ShellHBData` to the
  neutral `HermiteBiehlerData` interface.
- `radialRigidity_to_chartCompactness`: converts any `RadialRigidityPackage ι p D` into
  `ChartCompactness ι p D`.
- `hankelPrescribed_radialRigidityPackage`, `hankelPrescribed_chartCompactness`:
  instantiates `RadialRigidityPackage` and `ChartCompactness` for any Hermite–Biehler
  configuration `D : ShellHBData`, either Fourier eigenvalue `ε = ±1`, any sequence
  `c n → ∞`, and any `IsHankelPrescribed D r (c n) ε (T n) (f n)` with `o(c^{1/3})`
  offsets (in particular bounded offsets `|r t c'| ≤ R_off`).
- `hankelPrescribed_liminf_lower`: `gt:7.5` / `ft:C5d` lower coefficient at all levels
  `(P, Q)` and both eigenvalues `ε = ±1`, uniformly over bounded offsets.
- `hankelPrescribed_profile_rigidity`: locally uniform and `L¹(ℝ)` convergence to
  `D.normG` and origin vanishing `f_n(0)/M[f_n] → 0` at equality.
- `shellAdmissible_isHankelPrescribed`, `shellReduction_littleO`: lifts `IsShellAdmissible`
  to `IsHankelPrescribed` and deduces the `o(d^{1/3})` shell reduction at all levels `(P, Q)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real FourierTransform RealInnerProductSpace Classical

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.SignUncertainty
open FormalResearch.Special
open FormalResearch.CohnElkies

/-! ### Projection from `ShellHBData` to `HermiteBiehlerData` -/

/-- Project `ShellHBData` to the neutral `HermiteBiehlerData` interface. -/
noncomputable def shellHBToHermiteBiehlerData (D : ShellHBData) : HermiteBiehlerData where
  P := D.P
  Q := D.Q
  hHB := D.hHB
  S := D.S
  tm := D.tm
  G := D.G
  S_nonempty := D.S_nonempty
  tm_mem := D.tm_mem
  tm_min := D.tm_min
  G_diff := D.G_diff
  G_int := D.G_int
  G_env := D.G_env
  G_real := D.G_real
  G_integral_zero := D.G_integral_zero
  G_l1_pos := D.G_l1_pos
  G_nonneg_left := D.G_nonneg_left
  G_eq_zero_on_S := D.G_eq_zero_on_S
  G_deriv_ne_zero := D.G_deriv_ne_zero
  uniqueness := D.uniqueness

@[simp]
lemma shellHBToHermiteBiehlerData_tm (D : ShellHBData) :
    (shellHBToHermiteBiehlerData D).tm = D.tm := rfl

@[simp]
lemma shellHBToHermiteBiehlerData_S (D : ShellHBData) :
    (shellHBToHermiteBiehlerData D).S = D.S := rfl

@[simp]
lemma shellHBToHermiteBiehlerData_normG (D : ShellHBData) :
    (shellHBToHermiteBiehlerData D).normG = D.normG := rfl

/-! ### Converter `RadialRigidityPackage → ChartCompactness` -/

private lemma rpow_neg_third_mul_third {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 3 : ℝ)) * x ^ (1 / 3 : ℝ) = 1 := by
  rw [← Real.rpow_add hx]; norm_num

private lemma hankel_psi_nonneg_of_le {c T u : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (htail : ∀ Δ : ℝ, T ≤ Δ → 0 ≤ f Δ) (hmass : 0 < hankelMass c f)
    (hu : u ≤ -hankelBeta1 * (c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2))) :
    0 ≤ hankelWindowProfile c f u / hankelMass c f := by
  unfold hankelWindowProfile; dsimp only
  split_ifs with hΔ
  · refine div_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le)
      (mul_nonneg (htail _ ?_) (hankelRho0_nonneg hc hΔ.le))) hmass.le
    have h1 : (-c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) * c ^ (1 / 3 : ℝ) = -(T - c / π ^ 2) := by
      rw [show (-c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) * c ^ (1 / 3 : ℝ) =
        -(c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) * (T - c / π ^ 2) by ring,
        rpow_neg_third_mul_third hc]; ring
    have h' : u / hankelBeta1 ≤ -(c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) :=
      (div_le_iff₀ hankelBeta1_pos).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right h' (Real.rpow_nonneg hc.le (1 / 3 : ℝ))
    linarith [h1]
  · simp

/-- Convert a `RadialRigidityPackage ι p D` into the abstract `ChartCompactness ι p D`
interface (`FT-CC`), mapping `u = -β₁ c^{-1/3} (Δ - c/π²)`. -/
noncomputable def radialRigidity_to_chartCompactness {ι : Type*} {p : Filter ι}
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D) :
    ChartCompactness ι p D where
  ψ n u := hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)
  uT n := -hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2))
  uSite t n := hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n))
  ψ_int := by
    filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_int] with n hc0 hint
    exact ((integrable_hankelWindowProfile_iff hc0 _).mpr hint).div_const _
  ψ_l1_eq_one := by
    filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne] with
      n hc0 hck hink hnek
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have heq : (fun u => |hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)|) =
        fun u => |hankelWindowProfile (R.c n) (R.f n) u| / hankelMass (R.c n) (R.f n) := by
      ext u; rw [abs_div, abs_of_pos hmass]
    rw [heq, integral_div, integral_abs_hankelWindowProfile hc0 (R.f n), div_self hmass.ne']
  ψ_integral_le_zero := by
    filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne,
      R.f_origin_eq, R.f_origin_le] with n hc0 hck hink hnek horg horg_le
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    rw [integral_div, integral_hankelWindowProfile hc0 (R.f n), ← horg]
    exact div_nonpos_of_nonpos_of_nonneg horg_le hmass.le
  ψ_tail_nonneg := by
    filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne,
      R.f_tail_nonneg] with n hc0 hck hink hnek htail u hu
    exact hankel_psi_nonneg_of_le hc0 htail (hankelMass_pos_of_continuousOn hc0 hck hink hnek) hu
  ψ_site_nonneg t ht := by
    have hβ := hankelBeta1_pos
    have hasymp : Tendsto (fun n => hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)))
        p (𝓝 (t : ℝ)) := by
      have h1 := (R.Tsite_asymp t ht).neg.const_mul hankelBeta1
      have hlim : hankelBeta1 * -(-(t : ℝ) / hankelBeta1) = (t : ℝ) := by field_simp [hβ.ne']
      rw [hlim] at h1
      exact h1.congr' (Eventually.of_forall fun n => by ring)
    have hc_pos : ∀ᶠ n in p, 0 < R.c n := R.c_tendsto.eventually (eventually_gt_atTop 0)
    have hc23 : Tendsto (fun n => (R.c n) ^ (2 / 3 : ℝ) / π ^ 2) p atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp R.c_tendsto).atTop_div_const
        (sq_pos_of_pos Real.pi_pos)
    have hbd : ∀ᶠ n in p,
        hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1 ≤
          (t : ℝ) / hankelBeta1 + 1 :=
      (hasymp.div_const hankelBeta1).eventually (eventually_le_nhds (by linarith))
    have hsub : Tendsto (fun n => (R.c n) ^ (2 / 3 : ℝ) / π ^ 2 -
        hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1)
        p atTop :=
      tendsto_atTop_mono' p (hbd.mono fun _ hk => sub_le_sub_left hk _)
        (hc23.atTop_add tendsto_const_nhds)
    have hdom : Tendsto (fun n => (R.c n) ^ (1 / 3 : ℝ) * ((R.c n) ^ (2 / 3 : ℝ) / π ^ 2 -
        hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1))
        p atTop :=
      Tendsto.atTop_mul_atTop₀
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp R.c_tendsto) hsub
    filter_upwards [hc_pos, hdom.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne,
      R.f_site_nonneg t ht] with n hc0 hsite_pos hck hink hnek hsnn
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have hr := rpow_neg_third_mul_third hc0
    have hΔ_eq : R.c n / π ^ 2 -
        hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1 *
          (R.c n) ^ (1 / 3 : ℝ) = R.Tsite t n := by
      calc R.c n / π ^ 2 -
          hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1 *
            (R.c n) ^ (1 / 3 : ℝ)
          = R.c n / π ^ 2 - (R.c n ^ (-(1 / 3 : ℝ)) * R.c n ^ (1 / 3 : ℝ)) *
              (R.c n / π ^ 2 - R.Tsite t n) := by field_simp [hβ.ne']
        _ = R.Tsite t n := by rw [hr]; ring
    have hTpos : 0 < R.Tsite t n := by
      have hmul : (R.c n) ^ (1 / 3 : ℝ) * ((R.c n) ^ (2 / 3 : ℝ) / π ^ 2) = R.c n / π ^ 2 := by
        rw [mul_div_assoc', ← Real.rpow_add hc0, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
      have hrewrite : (R.c n) ^ (1 / 3 : ℝ) * ((R.c n) ^ (2 / 3 : ℝ) / π ^ 2 -
          hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.c n / π ^ 2 - R.Tsite t n)) / hankelBeta1) =
          R.Tsite t n := by
        rw [mul_sub, hmul]; linarith [hΔ_eq]
      rwa [hrewrite] at hsite_pos
    unfold hankelWindowProfile
    dsimp only
    rw [hΔ_eq]
    split_ifs
    exact div_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hc0.le _) hβ.le)
      (mul_nonneg hsnn (hankelRho0_nonneg hc0 hTpos.le))) hmass.le
  uSite_tendsto t ht := by
    have hβ := hankelBeta1_pos
    have h1 := (R.Tsite_asymp t ht).neg.const_mul hankelBeta1
    have hlim : hankelBeta1 * -(-(t : ℝ) / hankelBeta1) = (t : ℝ) := by field_simp [hβ.ne']
    rw [hlim] at h1
    exact h1.congr' (Eventually.of_forall fun n => by ring)
  tail_tight ε hε := by
    obtain ⟨C_l, κ_l, hCl, hκl, hlobe⟩ := R.deep_lobe_mass
    have hβ := hankelBeta1_pos
    have ht_exp : Tendsto (fun r : ℝ => C_l * Real.exp (-5 * r ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa using ((Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop
        (neg_lt_zero.mpr (by norm_num : (0 : ℝ) < 5))
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)))).const_mul C_l)
    obtain ⟨r₀', hr₀'⟩ := eventually_atTop.mp (ht_exp.eventually (Iic_mem_nhds (half_pos hε)))
    let r₀ : ℝ := max r₀' 1
    have hr₀_ge1 : 1 ≤ r₀ := le_max_right _ _
    have hr₀_bd : C_l * Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) ≤ ε / 2 := hr₀' r₀ (le_max_left _ _)
    refine ⟨r₀ * hankelBeta1, fun R' hR' => ?_⟩
    set r : ℝ := R' / hankelBeta1 with hrdef
    have hrr0 : r₀ ≤ r := (le_div_iff₀ hβ).mpr hR'
    have hr1 : 1 ≤ r := hr₀_ge1.trans hrr0
    have hrβ : r * hankelBeta1 = R' := div_mul_cancel₀ _ hβ.ne'
    have hrexp : C_l * Real.exp (-5 * r ^ (3 / 2 : ℝ)) ≤ ε / 2 := by
      have hpow : r₀ ^ (3 / 2 : ℝ) ≤ r ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hrr0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
      have hexp : Real.exp (-5 * r ^ (3 / 2 : ℝ)) ≤ Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      calc C_l * Real.exp (-5 * r ^ (3 / 2 : ℝ))
          ≤ C_l * Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hexp hCl.le
        _ ≤ ε / 2 := hr₀_bd
    have hc_pos : ∀ᶠ n in p, 0 < R.c n := R.c_tendsto.eventually (eventually_gt_atTop 0)
    have hq : Tendsto (fun n => (R.c n) ^ (2 / 3 : ℝ)) p atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp R.c_tendsto
    have hc_dom : ∀ᶠ n in p, r * (R.c n) ^ (1 / 3 : ℝ) < R.c n / π ^ 2 := by
      filter_upwards [hc_pos, hq.eventually (eventually_gt_atTop (r * π ^ 2))] with n hc0 hqgt
      have hmul := mul_lt_mul_of_pos_right hqgt (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ))
      rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one] at hmul
      rw [lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
      linarith
    have hexp_c : ∀ᶠ n in p, C_l * Real.exp (-κ_l * R.c n) ≤ ε / 2 := by
      have ht : Tendsto (fun n => C_l * Real.exp (-κ_l * R.c n)) p (𝓝 0) := by
        simpa using ((Real.tendsto_exp_atBot.comp
          (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hκl) R.c_tendsto)).const_mul C_l)
      exact ht.eventually (Iic_mem_nhds (half_pos hε))
    filter_upwards [hc_pos, R.f_cont, R.f_int, R.f_ne, hc_dom, hexp_c, hlobe r hr1] with
      n hc0 hck hink hnek hRlt hcexp hlobe_n
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have heq : ∫ u in Ioi R', |hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)| =
        (∫ Δ in Ioo (0 : ℝ) (R.c n / π ^ 2 - r * (R.c n) ^ (1 / 3 : ℝ)),
          |R.f n Δ| * hankelRho0 (R.c n) Δ) / hankelMass (R.c n) (R.f n) := by
      have hp : (fun u => |hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)|) =
          fun u => |hankelWindowProfile (R.c n) (R.f n) u| / hankelMass (R.c n) (R.f n) := by
        ext u; rw [abs_div, abs_of_pos hmass]
      rw [hp, integral_div, ← hrβ, integral_tail_abs_hankelWindowProfile hc0 (R.f n) r]
    rw [heq, div_le_iff₀ hmass]
    have h1 := hlobe_n hRlt
    have h2 : C_l * (Real.exp (-5 * r ^ (3 / 2 : ℝ)) + Real.exp (-κ_l * R.c n)) ≤ ε := by
      calc C_l * (Real.exp (-5 * r ^ (3 / 2 : ℝ)) + Real.exp (-κ_l * R.c n))
          = C_l * Real.exp (-5 * r ^ (3 / 2 : ℝ)) + C_l * Real.exp (-κ_l * R.c n) := by ring
        _ ≤ ε / 2 + ε / 2 := add_le_add hrexp hcexp
        _ = ε := add_halves ε
    calc ∫ Δ in Ioo (0 : ℝ) (R.c n / π ^ 2 - r * (R.c n) ^ (1 / 3 : ℝ)),
          |R.f n Δ| * hankelRho0 (R.c n) Δ
        ≤ C_l * hankelMass (R.c n) (R.f n) *
            (Real.exp (-5 * r ^ (3 / 2 : ℝ)) + Real.exp (-κ_l * R.c n)) := h1
      _ = hankelMass (R.c n) (R.f n) *
            (C_l * (Real.exp (-5 * r ^ (3 / 2 : ℝ)) + Real.exp (-κ_l * R.c n))) := by ring
      _ ≤ hankelMass (R.c n) (R.f n) * ε := mul_le_mul_of_nonneg_left h2 hmass.le
      _ = ε * hankelMass (R.c n) (R.f n) := by ring
  compactness_subseq ns hns hB := by
    obtain ⟨B, hB⟩ := hB
    have hB' : ∃ B' : ℝ, ∀ k : ℕ, (R.c (ns k)) ^ (-(1 / 3 : ℝ)) * (R.T (ns k) - R.c (ns k) / π ^ 2) ≤ B' := by
      refine ⟨-B / hankelBeta1, fun k => ?_⟩
      have h1 := hB k
      rw [le_div_iff₀ hankelBeta1_pos]
      linarith
    obtain ⟨ms, sLim, F, C, ν, hms, hs_lim, hΨ_lim, hFd, hFi, hC, hFb, hFreal⟩ :=
      R.compactness_subseq ns hns hB'
    refine ⟨ms, -hankelBeta1 * sLim, F, C, ν, hms, ?_, hΨ_lim, hFd, hFi, hC, hFb, hFreal⟩
    exact (tendsto_const_nhds.mul hs_lim).congr' (Eventually.of_forall fun k => rfl)

/-! ### Concrete Hankel multilevel instance for general `(P, Q)` and `ε = ±1` -/

/-- Build a `RadialRigidityPackage` for ANY Hermite–Biehler configuration `D : ShellHBData`,
either Fourier eigenvalue `ε = ±1`, any sequence `c n → ∞`, and any prescribed-site Hankel
feasible sequence `IsHankelPrescribed D r (c n) ε (T n) (f n)` with `o(c^{1/3})` offsets. -/
theorem exists_hankelPrescribed_package (D : ShellHBData) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (c : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    (r : ℝ → ℝ → ℝ)
    (hr : ∀ t ∈ D.S, t ≠ D.tm → Tendsto (fun n => r t (c n) / (c n) ^ (1 / 3 : ℝ)) atTop (𝓝 0))
    (T : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hfeas : ∀ n, IsHankelPrescribed D r (c n) ε (T n) (f n)) :
    ∃ R : RadialRigidityPackage ℕ atTop (shellHBToHermiteBiehlerData D),
      R.c = c ∧ R.T = T ∧ R.f = f := by
  have hc_pos : ∀ᶠ n in atTop, 0 < c n := hc.eventually (eventually_gt_atTop 0)
  have h_origin : ∀ᶠ n in atTop, ε * f n 0 = ∫ Δ in Ioi 0, f n Δ * hankelRho0 (c n) Δ := by
    filter_upwards [hc_pos] with n hn
    have h := (hfeas n).eigen 0 Set.self_mem_Ici
    rw [besselHankelTransform_zero hn] at h
    exact h.symm
  have h_deep : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ R : ℝ, 1 ≤ R → ∀ᶠ n in atTop, R * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 →
        ∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)),
          |f n Δ| * hankelRho0 (c n) Δ ≤
            C * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ * c n)) := by
    refine ⟨8, 1 / 25, by norm_num, by norm_num, fun R hR => ?_⟩
    filter_upwards [hc.eventually (eventually_ge_atTop 56)] with n hn _
    exact deep_lobe_mass_thm hn (hfeas n).toIsHankelEigenfn hε hR
  have h_nonneg_f : ∀ᶠ n in atTop, ∃ Δ : ℝ, 0 ≤ Δ ∧ f n Δ ≠ 0 :=
    Eventually.of_forall fun n => by
      obtain ⟨Δ, hΔ, hne⟩ := (hfeas n).nonzero
      exact ⟨Δ, hΔ, hne⟩
  have h_lower := scaled_threshold_bddBelow_raw c ε f T hc
    (Eventually.of_forall fun n => (hfeas n).cont) (Eventually.of_forall fun n => (hfeas n).int)
    h_nonneg_f h_origin (Eventually.of_forall fun n => (hfeas n).origin_sign)
    (Eventually.of_forall fun n => (hfeas n).tail_nonneg) h_deep
  obtain ⟨B₀, hB₀⟩ := h_lower
  refine ⟨⟨c, ε, hε, f, T, fun t n => hankelLevel (t : ℝ) (c n) (r (t : ℝ) (c n)), hc,
    Eventually.of_forall fun n => (hfeas n).cont,
    Eventually.of_forall fun n => (hfeas n).int,
    h_nonneg_f, h_origin,
    Eventually.of_forall fun n => (hfeas n).origin_sign,
    Eventually.of_forall fun n => (hfeas n).tail_nonneg,
    fun t ht => Eventually.of_forall fun n => by
      apply (hfeas n).sites_nonneg
      unfold hankelSites
      exact Finset.mem_image.mpr ⟨(t : ℝ), Finset.mem_erase.mpr ⟨ht, t.2⟩, rfl⟩,
    fun t ht => by
      have hlim : Tendsto (fun n => -((t : ℝ) / hankelBeta1) + r (t : ℝ) (c n) / (c n) ^ (1 / 3 : ℝ))
          atTop (𝓝 (-((t : ℝ) / hankelBeta1) + 0)) :=
        tendsto_const_nhds.add (hr (t : ℝ) t.2 ht)
      rw [add_zero, ← neg_div] at hlim
      refine hlim.congr' ?_
      filter_upwards [hc_pos] with n hc0
      unfold hankelLevel
      have hc13 : (c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ) = 1 := rpow_neg_third_mul_third hc0
      calc -(t : ℝ) / hankelBeta1 + r (t : ℝ) (c n) / (c n) ^ (1 / 3 : ℝ)
          = -((t : ℝ) / hankelBeta1) * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) +
              r (t : ℝ) (c n) * (c n) ^ (-(1 / 3 : ℝ)) := by
            rw [hc13, Real.rpow_neg hc0.le, div_eq_mul_inv]; ring
        _ = (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - (t : ℝ) / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) +
              r (t : ℝ) (c n) - c n / π ^ 2) := by ring,
    h_deep, ?_⟩, rfl, rfl, rfl⟩
  intro ns hns hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨ms1, F, C, ν, hms1, hloc, -, -, hFd, hFi, hC, hFb, hFreal⟩ :=
    radial_compactness.normalized_compactness ε hε (fun k => c (ns k)) (fun k => f (ns k))
      (hc.comp hns) (fun k => (hfeas (ns k)).toIsHankelEigenfn)
  have hlow : ∀ᶠ k in atTop, B₀ ≤ c (ns (ms1 k)) ^ (-(1 / 3 : ℝ)) *
      (T (ns (ms1 k)) - c (ns (ms1 k)) / π ^ 2) :=
    (hns.comp hms1.tendsto_atTop).eventually hB₀
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hlow
  obtain ⟨a, -, φ, hφ, hφlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc B₀ B)
    (x := fun j => c (ns (ms1 (j + k0))) ^ (-(1 / 3 : ℝ)) *
      (T (ns (ms1 (j + k0))) - c (ns (ms1 (j + k0))) / π ^ 2))
    (fun j => ⟨hk0 _ (by omega), hB _⟩)
  have hgi : Tendsto (fun j => φ j + k0) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right _ _) hφ.tendsto_atTop
  refine ⟨fun j => ms1 (φ j + k0), a, F, C, ν, hms1.comp (hφ.add_const k0), hφlim, ?_, hFd, hFi,
    hC, hFb, hFreal⟩
  intro u hu x hx
  obtain ⟨t, ht, h'⟩ := hloc u hu x hx
  exact ⟨t, ht, hgi.eventually h'⟩

/-- **Instantiation of `ChartCompactness` (`FT-CC`) for the Paper I Hankel multilevel problem**
at any Hermite–Biehler configuration `D : ShellHBData`, either Fourier eigenvalue `ε = ±1`,
any sequence `c n → ∞`, and any `IsHankelPrescribed D r (c n) ε (T n) (f n)` with
`o(c^{1/3})` offsets. -/
theorem hankelPrescribed_chartCompactness (D : ShellHBData) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (c : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    (r : ℝ → ℝ → ℝ)
    (hr : ∀ t ∈ D.S, t ≠ D.tm → Tendsto (fun n => r t (c n) / (c n) ^ (1 / 3 : ℝ)) atTop (𝓝 0))
    (T : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hfeas : ∀ n, IsHankelPrescribed D r (c n) ε (T n) (f n)) :
    ∃ C : ChartCompactness ℕ atTop (shellHBToHermiteBiehlerData D),
      (∀ n, C.ψ n = fun u => hankelWindowProfile (c n) (f n) u / hankelMass (c n) (f n)) ∧
      (∀ n, C.uT n = -hankelBeta1 * ((c n) ^ (-(1 / 3 : ℝ)) * (T n - c n / π ^ 2))) := by
  obtain ⟨R, hRc, hRT, hRf⟩ :=
    exists_hankelPrescribed_package D ε hε c hc r hr T f hfeas
  refine ⟨radialRigidity_to_chartCompactness R, fun n => ?_, fun n => ?_⟩
  · show (fun u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)) = _
    rw [hRc, hRf]
  · show -hankelBeta1 * ((R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) = _
    rw [hRc, hRT]

/-! ### All-level `gt:7.5` lower bound, profile rigidity, and `o(d^{1/3})` shell reduction -/

private lemma strictMono_subseq_of_tendsto_atTop {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (fun k => c (φ k)) := by
  have step : ∀ k : ℕ, ∃ m : ℕ, k < m ∧ c k < c m := fun k => by
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hc.eventually_gt_atTop (c k))
    refine ⟨max (k + 1) M, by omega, hM _ (le_max_right _ _)⟩
  choose nxt hnxt_lt hnxt_c using step
  let φ : ℕ → ℕ := Nat.rec 0 (fun _ prev => nxt prev)
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n => hnxt_lt (φ n)
  have hcφ : StrictMono (fun k => c (φ k)) := strictMono_nat_of_lt_succ fun n => hnxt_c (φ n)
  exact ⟨φ, hφ, hcφ⟩

private lemma bounded_offsets_div_rpow_tendsto {c : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    {R_off : ℝ} {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ R_off) :
    Tendsto (fun n => r n / (c n) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => R_off / (c n) ^ (1 / 3 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc)
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [hc.eventually (eventually_gt_atTop 0)] with n hc0
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
  exact div_le_div_of_nonneg_right (hr n) (Real.rpow_nonneg hc0.le _)

/-- **Theorem 7.5 (`gt:7.5`), lower half for any Hermite–Biehler configuration `D : ShellHBData`**,
both Fourier eigenvalues `ε = ±1`, and prescribed-site Hankel competitors with bounded offsets
`|r t c'| ≤ R_off`: for every `δ > 0`, eventually in `c`, every prescribed threshold satisfies
`hbModel D c - δ * c^{1/3} ≤ T`. -/
theorem hankelPrescribed_liminf_lower (D : ShellHBData) (R_off : ℝ) (_hR : 0 ≤ R_off) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ c : ℝ in atTop, ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
        ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelPrescribed D r c ε T f →
          hbModel D c - δ * c ^ (1 / 3 : ℝ) ≤ T := by
  intro δ hδ
  by_contra hcon
  have hfreq : ∃ᶠ c : ℝ in atTop, ∃ (ε : ℝ) (r : ℝ → ℝ → ℝ) (T : ℝ) (f : ℝ → ℝ),
      (ε = 1 ∨ ε = -1) ∧ (∀ t c', |r t c'| ≤ R_off) ∧ IsHankelPrescribed D r c ε T f ∧
      T < hbModel D c - δ * c ^ (1 / 3 : ℝ) := by
    rw [Filter.not_eventually] at hcon
    refine hcon.mono fun c hc => ?_
    push Not at hc
    obtain ⟨ε, hε, r, hr, T, f, hf, hT⟩ := hc
    exact ⟨ε, r, T, f, hε, hr, hf, hT⟩
  obtain ⟨ns, hns, hns_prop⟩ := exists_seq_forall_of_frequently hfreq
  choose εs rs Ts fs hεs hrs hfeas hT using hns_prop
  have hsign_inf : (∃ᶠ n in atTop, εs n = 1) ∨ (∃ᶠ n in atTop, εs n = -1) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp hnone.1
    obtain ⟨N2, hN2⟩ := eventually_atTop.mp hnone.2
    rcases hεs (max N1 N2) with h1 | h2
    · exact hN1 _ (le_max_left _ _) h1
    · exact hN2 _ (le_max_right _ _) h2
  have hconst_sub : ∃ (φ : ℕ → ℕ) (ε₀ : ℝ), StrictMono φ ∧ (ε₀ = 1 ∨ ε₀ = -1) ∧
      ∀ k, εs (φ k) = ε₀ := by
    rcases hsign_inf with h1 | h2
    · obtain ⟨φ, hφ, hφ1⟩ := extraction_of_frequently_atTop h1
      exact ⟨φ, 1, hφ, Or.inl rfl, hφ1⟩
    · obtain ⟨φ, hφ, hφ2⟩ := extraction_of_frequently_atTop h2
      exact ⟨φ, -1, hφ, Or.inr rfl, hφ2⟩
  obtain ⟨φ, ε₀, hφ, hε₀, hε_eq⟩ := hconst_sub
  obtain ⟨ψ, hψ, hψ_strict⟩ := strictMono_subseq_of_tendsto_atTop (hns.comp hφ.tendsto_atTop)
  let idx : ℕ → ℕ := fun k => φ (ψ k)
  let c' : ℕ → ℝ := fun k => ns (idx k)
  let r' : ℝ → ℝ → ℝ := fun t cval =>
    if h : ∃ k, c' k = cval then rs (idx (Classical.choose h)) t cval else 0
  have hc' : Tendsto c' atTop atTop := (hns.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hr'_eq : ∀ k t, r' t (c' k) = rs (idx k) t (c' k) := fun k t => by
    dsimp [r']
    split_ifs with hex
    · rw [hψ_strict.injective (Classical.choose_spec hex)]
    · exact absurd ⟨k, rfl⟩ hex
  have hr'_bdd : ∀ k t, |r' t (c' k)| ≤ R_off := fun k t => by
    rw [hr'_eq]; exact hrs (idx k) t (c' k)
  have hfeas' : ∀ k, IsHankelPrescribed D r' (c' k) ε₀ (Ts (idx k)) (fs (idx k)) := by
    intro k
    have h0 := hfeas (idx k)
    rw [hε_eq (ψ k)] at h0
    refine ⟨h0.toIsHankelFeasible, fun s hs => ?_⟩
    apply h0.sites_nonneg
    unfold hankelSites at hs ⊢
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨t, ht, by simp only [hankelLevel, hr'_eq k t]; rfl⟩
  obtain ⟨C, hCψ, hCuT⟩ := hankelPrescribed_chartCompactness D ε₀ hε₀ c' hc' r'
    (fun t _ _ => bounded_offsets_div_rpow_tendsto hc' fun k => hr'_bdd k t)
    (fun k => Ts (idx k)) (fun k => fs (idx k)) hfeas'
  have hlim := chartCompactness_limsup_ereal C
  have hu_ge : ∀ᶠ k in atTop,
      ((D.tm + hankelBeta1 * δ : ℝ) : EReal) ≤ (C.uT k : EReal) := by
    filter_upwards [hc'.eventually (eventually_gt_atTop 0)] with k hc0
    rw [EReal.coe_le_coe_iff, hCuT k]
    have hTk : Ts (idx k) < hbModel D (c' k) - δ * (c' k) ^ (1 / 3 : ℝ) := hT (idx k)
    unfold hbModel at hTk
    have h1 : (c' k) ^ (-(1 / 3 : ℝ)) * (Ts (idx k) - c' k / π ^ 2) <
        -(D.tm / hankelBeta1) - δ := by
      have hpos : 0 < (c' k) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
      have hmul := mul_lt_mul_of_pos_left (show Ts (idx k) - c' k / π ^ 2 <
        -(D.tm / hankelBeta1 + δ) * (c' k) ^ (1 / 3 : ℝ) by linarith) hpos
      have h3 : (c' k) ^ (-(1 / 3 : ℝ)) * (-(D.tm / hankelBeta1 + δ) * (c' k) ^ (1 / 3 : ℝ)) =
          -(D.tm / hankelBeta1) - δ := by
        rw [show (c' k) ^ (-(1 / 3 : ℝ)) * (-(D.tm / hankelBeta1 + δ) * (c' k) ^ (1 / 3 : ℝ)) =
          -(D.tm / hankelBeta1 + δ) * ((c' k) ^ (-(1 / 3 : ℝ)) * (c' k) ^ (1 / 3 : ℝ)) by ring,
          rpow_neg_third_mul_third hc0]
        ring
      linarith
    have h2 := mul_le_mul_of_nonpos_left h1.le (neg_nonpos.mpr hankelBeta1_pos.le)
    have h3 : -hankelBeta1 * (-(D.tm / hankelBeta1) - δ) = D.tm + hankelBeta1 * δ := by
      field_simp [hankelBeta1_pos.ne']; ring
    linarith
  have hle_lim : ((D.tm + hankelBeta1 * δ : ℝ) : EReal) ≤ Filter.limsup (fun k => (C.uT k : EReal)) atTop :=
    Filter.le_limsup_of_frequently_le (hu_ge.frequently) (by isBoundedDefault)
  have hbad := EReal.coe_le_coe_iff.mp (hle_lim.trans hlim)
  dsimp at hbad
  nlinarith [hankelBeta1_pos]

/-- **Profile rigidity and origin vanishing (`gt:7.5` / `ft:C5d`)** for the Paper I Hankel
multilevel problem at any Hermite–Biehler configuration `D : ShellHBData`: when
`c_n^{-1/3} (T_n - c_n / π²) → -D.tm / β₁`, the normalized window profiles converge locally
uniformly and in `L¹(ℝ)` to `D.normG`, and `f_n(0) / M[f_n] → 0`. -/
theorem hankelPrescribed_profile_rigidity (D : ShellHBData) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (c : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    (r : ℝ → ℝ → ℝ)
    (hr : ∀ t ∈ D.S, t ≠ D.tm → Tendsto (fun n => r t (c n) / (c n) ^ (1 / 3 : ℝ)) atTop (𝓝 0))
    (T : ℕ → ℝ) (f : ℕ → ℝ → ℝ)
    (hfeas : ∀ n, IsHankelPrescribed D r (c n) ε (T n) (f n))
    (hAtt : Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * (T n - c n / π ^ 2)) atTop
      (𝓝 (-(D.tm / hankelBeta1)))) :
    TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (c n) (f n) u / hankelMass (c n) (f n))
      D.normG atTop univ ∧
    Tendsto (fun n => ∫ u : ℝ,
      |hankelWindowProfile (c n) (f n) u / hankelMass (c n) (f n) - D.normG u|) atTop (𝓝 0) ∧
    Tendsto (fun n => f n 0 / hankelMass (c n) (f n)) atTop (𝓝 0) := by
  obtain ⟨R, hRc, hRT, hRf⟩ :=
    exists_hankelPrescribed_package D ε hε c hc r hr T f hfeas
  have hAttR : Tendsto (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) atTop
      (𝓝 (-((shellHBToHermiteBiehlerData D).tm / hankelBeta1))) := by
    simpa [hRc, hRT] using hAtt
  obtain ⟨hloc, hL1⟩ := radial_rigidity_profile R hAttR
  have horg := radial_rigidity_origin R hAttR
  refine ⟨?_, ?_, ?_⟩
  · simpa [hRc, hRf] using hloc
  · simpa [hRc, hRf] using hL1
  · simpa [hRc, hRf] using horg

/-! ### Lift of `IsShellAdmissible` to `IsHankelPrescribed` and `o(d^{1/3})` shell reduction -/

/-- A radial `IsShellAdmissible D r d R h` pair lifts to an `IsHankelPrescribed` profile
for `c = d / 2`, `ε = -1`, at threshold `R² / 2` with `G(0) = 0`, provided all prescribed
shell sites `shellSite t (r t) d` are nonnegative. -/
theorem shellAdmissible_isHankelPrescribed {D : ShellHBData} {r : ℝ → ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    {R : ℝ} {h : Euc d → ℝ} (hadm : IsShellAdmissible D r d R h)
    (hsites : ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) d) :
    ∃ G : ℝ → ℝ, IsHankelPrescribed D (fun t _ => r t d) ((d : ℝ) / 2) (-1) (R ^ 2 / 2) G ∧
      G 0 = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  set F : Euc (n + 1) → ℂ := 𝓕 (fun x : Euc (n + 1) => (h x : ℂ)) with hFdef
  have hI : Integrable (fun x : Euc (n + 1) => (h x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hadm.integrable
  have hC : Continuous (fun x : Euc (n + 1) => (h x : ℂ)) :=
    Complex.continuous_ofReal.comp hadm.continuous
  have hFint : Integrable F := hadm.fourier_integrable
  have hFre : ∀ y, F y = ((F y).re : ℂ) :=
    fun y => Complex.ext rfl (by simpa using (hadm.fourier_nonneg y).1)
  have hFcont : Continuous F := continuous_fourier_of_integrable hI
  have hFF : ∀ y, 𝓕 F y = (h (-y) : ℂ) := fun y => by
    have := congrFun (hC.fourierInv_fourier_eq hI hFint) (-y)
    rwa [Real.fourierInv_eq_fourier_neg, neg_neg] at this
  have hneg : ∀ y, 𝓕 (fun x : Euc (n + 1) => (h (-x) : ℂ)) y = F y := fun y => by
    rw [fourier_comp_neg_real hadm.integrable, ← hFdef]
    calc star (F y) = star ((F y).re : ℂ) := by rw [← hFre y]
      _ = ((F y).re : ℂ) := by simp
      _ = F y := (hFre y).symm
  have hhI : Integrable (fun x : Euc (n + 1) => h (-x)) := hadm.integrable.comp_neg
  have hhIC : Integrable (fun x : Euc (n + 1) => (h (-x) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hhI
  set g : Euc (n + 1) → ℝ := fun x => (F x).re - h (-x) with hg
  have hgC : (fun x : Euc (n + 1) => (g x : ℂ)) = fun x => F x - (h (-x) : ℂ) := by
    funext x; simp only [hg]; push_cast; rw [← hFre x]
  have hgI : Integrable g := hFint.re.sub hhI
  have hW : IsSignWitness (-1) (n + 1) R g := by
    refine ⟨hgI, ?_, ?_, ?_⟩
    · intro y
      rw [hgC]
      have h1 : 𝓕 (fun x => F x - (h (-x) : ℂ)) y =
          𝓕 F y - 𝓕 (fun x => (h (-x) : ℂ)) y := by
        rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
        · congr 1; funext x; rw [smul_sub]
        · exact (Real.fourierIntegral_convergent_iff y).mpr hFint
        · exact (Real.fourierIntegral_convergent_iff y).mpr hhIC
      rw [h1, hFF, hneg]
      have : (g y : ℂ) = F y - (h (-y) : ℂ) := congrFun hgC y
      rw [this]; push_cast; ring
    · by_contra hall
      push Not at hall
      have hzero : ∀ y : Euc (n + 1), R ≤ ‖y‖ → F y = 0 := fun y hy => by
        have h1 := hall y
        have h2 := hadm.nonpos_outside (-y) (by rw [norm_neg]; exact hy)
        have h3 := (hadm.fourier_nonneg y).2
        simp only [hg] at h1
        have : (F y).re = 0 := by linarith
        rw [hFre y, this]; simp
      have hsupp : HasCompactSupport F := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc (n + 1)) R) fun x hx => ?_
        rw [mem_closedBall_zero_iff, not_le] at hx
        exact hzero x hx.le
      have hR : ∀ y : Euc (n + 1), R ≤ ‖y‖ → 𝓕 F y = 0 := fun y hy => by
        rw [hFF]
        have h4 : h (-y) = 0 := by
          have h5 := hall y
          simp only [hg] at h5
          rw [hzero y hy] at h5; simpa using h5.symm
        simp [h4]
      have hF0 := fourier_compact_support_eq_zero (n := n) hFcont hsupp R hR
      have := hadm.fourier_origin_pos
      have h00 : F 0 = 0 := congrFun hF0 0
      rw [hFdef] at h00
      rw [h00] at this
      simp at this
    · intro x hx
      have h1 := (hadm.fourier_nonneg x).2
      have h2 := hadm.nonpos_outside (-x) (by rw [norm_neg]; exact hx)
      simp only [hg]; linarith
  have hg0 : g 0 = 0 := by
    simp only [hg, neg_zero]
    linarith [hadm.origin_eq]
  have hRpos : 0 < R := hW.pos_radius (Or.inr rfl) (by simp [hg0])
  -- Radial average `G(Δ) = realAvg n g (√(2Δ))`
  set fc : Euc (n + 1) → ℂ := fun x => (g x : ℂ) with hfc
  have hfint : Integrable fc := hW.integrable.ofReal
  have hW' : ∀ y : Euc (n + 1), 𝓕 fc y = (-1 : ℂ) * fc y := fun y => by
    simpa [hfc] using hW.fourier_eq y
  set G : ℝ → ℝ := fun Δ => realAvg n g (√(2 * Δ)) with hG
  have hFG : ∀ x : Euc (n + 1), radialAvg fc x = ((G (‖x‖ ^ 2 / 2) : ℝ) : ℂ) := fun x => by
    have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
      rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg x)
    rw [hfc, radialAvg_ofReal]; simp only [hG, e]
  have hFour : ∀ y, 𝓕 (radialAvg fc) y = (-1 : ℂ) * radialAvg fc y := fun y => by
    rw [fourier_radialAvg hfint y]
    unfold radialAvg sphMean
    simp_rw [hW']
    rw [integral_const_mul]; ring
  have hFcont_rad : Continuous (radialAvg fc) := by
    have : radialAvg fc = fun y => (-1 : ℂ)⁻¹ * 𝓕 (radialAvg fc) y := by
      ext y; rw [hFour y]; ring
    rw [this]
    exact continuous_const.mul (continuous_fourier_of_integrable (integrable_radialAvg hfint))
  set e₀ : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with he₀
  have hne : ‖e₀‖ = 1 := by rw [he₀, PiLp.norm_single]; simp
  have hGe : ∀ Δ, G Δ = (radialAvg fc (√(2 * Δ) • e₀)).re := fun Δ => by
    rw [radialAvg_ofReal, norm_smul, hne, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
    simp [hG]
  have hGcont : ContinuousOn G (Ici 0) := by
    have : Continuous G := by
      have h1 : Continuous fun Δ : ℝ => (radialAvg fc (√(2 * Δ) • e₀)).re :=
        Complex.continuous_re.comp (hFcont_rad.comp
          ((Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).smul continuous_const))
      exact h1.congr fun Δ => (hGe Δ).symm
    exact this.continuousOn
  have hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) :=
    (integrable_radialAvg hfint).congr (Eventually.of_forall hFG)
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  have hGint : IntegrableOn (fun Δ => G Δ * hankelRho0 (((n + 1 : ℕ) : ℝ) / 2) Δ) (Ioi 0) := by
    rw [hc]; exact (integrable_radialLift_iff n hn G).1 hint
  have heigen : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform (((n + 1 : ℕ) : ℝ) / 2) G Δ = (-1) * G Δ := by
    intro Δ hΔ
    have hΔ0 : 0 ≤ Δ := hΔ
    rw [hc]
    set y : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ) with hy
    have hy2 : ‖y‖ ^ 2 / 2 = Δ := by
      rw [hy, PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]; ring
    have h1 := fourier_radial_hankel n hn hGcont hint y
    have h2 : (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) = radialAvg fc :=
      funext fun x => (hFG x).symm
    rw [h2, hFour y, hFG y, hy2] at h1
    exact_mod_cast h1.symm
  have hG0 : G 0 = 0 := by simp [hG, realAvg_zero, hg0]
  have htail : ∀ Δ ≥ R ^ 2 / 2, 0 ≤ G Δ := fun Δ hΔ =>
    realAvg_nonneg n (Real.sqrt_nonneg _)
      ((Real.le_sqrt hRpos.le (by have := sq_nonneg R; linarith)).2 (by linarith)) hW.tail_nonneg
  have hnz : ∃ Δ ∈ Ici (0 : ℝ), G Δ ≠ 0 := by
    by_contra hz
    push Not at hz
    have hfcont : Continuous g := by
      have := Complex.continuous_re.comp (hW.continuous_ofReal (by norm_num : (-1 : ℝ) ≠ 0))
      exact this.congr (fun x => by simp)
    have hvan : ∀ x : EuclSp (n + 1), R ≤ ‖x‖ → g x = 0 := fun x hx => by
      have hx0 : x ≠ 0 := by intro h0; rw [h0, norm_zero] at hx; linarith
      have hr : realAvg n g ‖x‖ = 0 := by
        have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
          rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg x)
        have hGx : G (‖x‖ ^ 2 / 2) = realAvg n g ‖x‖ := by
          show realAvg n g (√(2 * (‖x‖ ^ 2 / 2))) = _; rw [e]
        rw [← hGx]
        exact hz _ (mem_Ici.2 (by positivity))
      have hnn : ∀ ω : USph (n + 1), 0 ≤ g (‖x‖ • (ω : EuclSp (n + 1))) := fun ω =>
        hW.tail_nonneg _ (by rw [norm_smul_sphere _ (norm_nonneg x)]; exact hx)
      let ω : USph (n + 1) := ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]⟩
      have := eq_zero_of_realAvg_zero n hfcont hnn hr ω
      simpa [ω, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0)] using this
    have hzero : fc = 0 := by
      refine fourier_compact_support_eq_zero (hW.continuous_ofReal (by norm_num)) ?_ R (fun y hy => ?_)
      · refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclSp (n + 1)) R) fun x hx => ?_
        have : R ≤ ‖x‖ := by rw [mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le
        simp [hfc, hvan x this]
      · rw [hW' y]; simp [hfc, hvan y hy]
    obtain ⟨x, hx⟩ := hW.nonzero
    exact hx (by simpa [hfc] using congrFun hzero x)
  refine ⟨G, ⟨⟨⟨hGcont, hGint, heigen⟩, hnz, by rw [hG0]; norm_num, htail⟩, ?_⟩, hG0⟩
  intro s hs
  unfold hankelSites at hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨htne, htS⟩ := Finset.mem_erase.mp ht
  have hsite_nn := hsites t htS htne
  have hsite_eq : hankelLevel t (((n + 1 : ℕ) : ℝ) / 2) (r t (n + 1)) = shellSite t (r t) (n + 1) := by
    unfold hankelLevel shellSite
    rw [div_div]
  rw [hsite_eq]
  unfold G realAvg
  refine mul_nonneg (inv_nonneg.2 (sphTotal_pos n).le) (integral_nonneg fun ω => ?_)
  have hnorm : ‖√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1))‖ =
      √(2 * shellSite t (r t) (n + 1)) :=
    norm_smul_sphere _ (Real.sqrt_nonneg _) ω
  have hnorm_neg : ‖-(√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1)))‖ ^ 2 / 2 =
      shellSite t (r t) (n + 1) := by
    rw [norm_neg, hnorm, Real.sq_sqrt (mul_nonneg (by norm_num) hsite_nn)]; ring
  have hfourier : 0 ≤ (F (√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1)))).re :=
    (hadm.fourier_nonneg _).2
  have hshell : h (-(√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1)))) ≤ 0 :=
    hadm.shells t htS htne _ hnorm_neg
  show 0 ≤ (F (√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1)))).re -
      h (-(√(2 * shellSite t (r t) (n + 1)) • (ω : EuclSp (n + 1))))
  linarith

private lemma hankelSites_pos_of_large (D : ShellHBData) (R_off : ℝ) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
      ∀ s ∈ hankelSites D r c, 0 < s := by
  let A : ℝ := ∑ t ∈ D.S, |t| / hankelBeta1
  have hA : 0 ≤ A := Finset.sum_nonneg fun t _ => div_nonneg (abs_nonneg _) hankelBeta1_pos.le
  let c₀ : ℝ := max 1 (π ^ 2 * (A + max R_off 0 + 1)) ^ 3
  refine ⟨max 1 c₀, le_max_left _ _, fun c hc r hr s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have htS : t ∈ D.S := (Finset.mem_erase.mp ht).2
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc_ge : c₀ ≤ c := (le_max_right _ _).trans hc
  have hc13 : max 1 (π ^ 2 * (A + max R_off 0 + 1)) ≤ c ^ (1 / 3 : ℝ) := by
    have h1 : (max 1 (π ^ 2 * (A + max R_off 0 + 1))) ^ (3 : ℝ) ≤ c := by
      exact_mod_cast hc_ge
    calc max 1 (π ^ 2 * (A + max R_off 0 + 1))
        = ((max 1 (π ^ 2 * (A + max R_off 0 + 1))) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h1c : 1 ≤ c ^ (1 / 3 : ℝ) := (le_max_left _ _).trans hc13
  have hpi : π ^ 2 * (A + max R_off 0 + 1) ≤ c ^ (1 / 3 : ℝ) := (le_max_right _ _).trans hc13
  have hle : |t| / hankelBeta1 ≤ A :=
    Finset.single_le_sum (f := fun t => |t| / hankelBeta1)
      (fun _ _ => div_nonneg (abs_nonneg _) hankelBeta1_pos.le) htS
  have h2 : t / hankelBeta1 ≤ A := (div_le_div_of_nonneg_right (le_abs_self t) hankelBeta1_pos.le).trans hle
  have h5 := (abs_le.mp (hr t c)).1
  have hpow : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
  have h4 : (t / hankelBeta1) * c ^ (1 / 3 : ℝ) ≤ A * c ^ (1 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hpow
  have hc_eq : c = (c ^ (1 / 3 : ℝ)) ^ 2 * c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]
    norm_num
  have hpi2 : A + max R_off 0 + 1 ≤ (c ^ (1 / 3 : ℝ)) ^ 2 / π ^ 2 := by
    have h_sq : π ^ 2 * (A + max R_off 0 + 1) ≤ (c ^ (1 / 3 : ℝ)) ^ 2 := by
      calc π ^ 2 * (A + max R_off 0 + 1) ≤ c ^ (1 / 3 : ℝ) := hpi
        _ ≤ c ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := le_mul_of_one_le_right hpow h1c
        _ = (c ^ (1 / 3 : ℝ)) ^ 2 := by ring
    rwa [le_div_iff₀ (sq_pos_of_pos Real.pi_pos), mul_comm]
  unfold hankelLevel
  have h_r : -max R_off 0 ≤ r t c := by linarith [le_max_left R_off 0]
  have h_r2 : -max R_off 0 * c ^ (1 / 3 : ℝ) ≤ -max R_off 0 := by
    nlinarith [le_max_right R_off 0]
  have hmul : (A + max R_off 0 + 1) * c ^ (1 / 3 : ℝ) ≤ c / π ^ 2 := by
    calc (A + max R_off 0 + 1) * c ^ (1 / 3 : ℝ)
        ≤ (c ^ (1 / 3 : ℝ)) ^ 2 / π ^ 2 * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right hpi2 hpow
      _ = ((c ^ (1 / 3 : ℝ)) ^ 2 * c ^ (1 / 3 : ℝ)) / π ^ 2 := by ring
      _ = c / π ^ 2 := by rw [← hc_eq]
  nlinarith

/-- **`thm:ce-shell-reduction` (`o(d^{1/3})` form, every Hermite–Biehler level `D : ShellHBData`)**:
for every `R_off ≥ 0` and `δ > 0`, eventually for all `d ≥ d₀`, every admissible shell radius
`R ∈ ceShellRadiusSet D r d` with `|r t d'| ≤ R_off` satisfies
`d/(2π²) - (D.tm / β₁)(d/2)^{1/3} - δ (d/2)^{1/3} ≤ R²/2`. -/
theorem shellReduction_littleO (D : ShellHBData) (R_off : ℝ) (hR : 0 ≤ R_off) :
    ∀ δ : ℝ, 0 < δ → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ r : ℝ → ℕ → ℝ, (∀ t d', |r t d'| ≤ R_off) →
        ∀ R ∈ ceShellRadiusSet D r d,
          (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) -
            δ * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) ≤ R ^ 2 / 2 := by
  intro δ hδ
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp (hankelPrescribed_liminf_lower D R_off hR δ hδ)
  obtain ⟨c₁, _, hsites_pos⟩ := hankelSites_pos_of_large D R_off
  let c₀' := max c₀ (max c₁ 1)
  refine ⟨max 2 ⌈2 * c₀'⌉₊, fun d hd r hr R ⟨h, hadm⟩ => ?_⟩
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hc_ge : c₀' ≤ (d : ℝ) / 2 := by
    have h1 : ⌈2 * c₀'⌉₊ ≤ d := (le_max_right _ _).trans hd
    have h2 : 2 * c₀' ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    linarith
  have hc0 : c₀ ≤ (d : ℝ) / 2 := (le_max_left _ _).trans hc_ge
  have hc1 : c₁ ≤ (d : ℝ) / 2 := ((le_max_left _ _).trans (le_max_right _ _)).trans hc_ge
  let r' : ℝ → ℝ → ℝ := fun t _ => r t d
  have hsites : ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) d := fun t htS htne => by
    have hmem : hankelLevel t ((d : ℝ) / 2) (r' t ((d : ℝ) / 2)) ∈ hankelSites D r' ((d : ℝ) / 2) :=
      Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨htne, htS⟩, rfl⟩
    have hpos := hsites_pos ((d : ℝ) / 2) hc1 r' (fun t' _ => hr t' d) _ hmem
    have heq : hankelLevel t ((d : ℝ) / 2) (r' t ((d : ℝ) / 2)) = shellSite t (r t) d := by
      unfold hankelLevel shellSite r'; rw [div_div]
    rw [heq] at hpos
    exact hpos.le
  obtain ⟨G, hG, -⟩ := shellAdmissible_isHankelPrescribed hd2 hadm hsites
  have hbd := hc₀ ((d : ℝ) / 2) hc0 (-1) (Or.inr rfl) r' (fun t' _ => hr t' d) (R ^ 2 / 2) G hG
  unfold hbModel at hbd
  rwa [div_div] at hbd

/-! ### Axiom guards -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.radialRigidity_to_chartCompactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialRigidity_to_chartCompactness

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.exists_hankelPrescribed_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelPrescribed_package

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.hankelPrescribed_chartCompactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrescribed_chartCompactness

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.hankelPrescribed_liminf_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrescribed_liminf_lower

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.hankelPrescribed_profile_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPrescribed_profile_rigidity

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.shellAdmissible_isHankelPrescribed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellAdmissible_isHankelPrescribed

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.shellReduction_littleO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellReduction_littleO

end FormalResearch.ModularBootstrap.FoldTip

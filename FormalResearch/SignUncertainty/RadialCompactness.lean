module

public import FormalResearch.SignUncertainty.Radii

/-!
# `lem:radial-compactness` as an input structure, and `gt:7.5` (lower half) from it

`RadialCompactness` states `lem:radial-compactness` (`fourier_mellin.tex`; proof in
`fourier_mellin_proofs.tex`: Mellin inversion, the deep lobe, Airy rescaling with domination, the
limiting entire function) for the concrete Hankel problem (`IsHankelEigenfn`, `hankelWindowProfile`).
Its two fields are open (not proved here):

* `deep_lobe_mass`: the absolute mass of `f ρ₀` below `c/π² - R c^{1/3}` is
  `≤ C M[f] (e^{-5 R^{3/2}} + e^{-κ c})` (Step 2; the pointwise form `eq:deep-lobe` is the
  intermediate bound and is not needed downstream);
* `profile_compactness`: on every sequence `c_n → ∞` with `M[f_n] ≤ M₀`, a subsequence of the window
  profiles converges locally uniformly, together with its first derivative, to the restriction of a
  real entire `F` of the Airy class (`‖F(z)‖ ≤ C (1+|z|)^ν e(z)`, `F ∈ L¹`); the `C¹` clause
  includes that the profiles are `C¹` on each window eventually (Steps 3-4). The bound
  `‖F‖₁ ≤ liminf M[f_n]` of the TeX statement is Fatou and is recovered downstream.

`radial_rigidity_lower_of_compactness` derives the lower half of `gt:7.5` at one level, `ε = -1`:
for every `δ > 0` and all large `c`, every `(-1)`-feasible threshold satisfies
`T ≥ c/π² + (A - δ) c^{1/3}`, `A = |a₁|/β₁`, from `radial_rigidity_liminf_ereal` with the
Hermite–Biehler data `HermiteBiehlerData.airy`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Scaling lemmas -/

lemma IsHankelEigenfn.smul {c ε : ℝ} {f : ℝ → ℝ} (a : ℝ) (hf : IsHankelEigenfn c ε f) :
    IsHankelEigenfn c ε (fun Δ => a * f Δ) where
  cont := continuousOn_const.mul hf.cont
  int := by
    have h : IntegrableOn (fun Δ => a * (f Δ * hankelRho0 c Δ)) (Ioi 0) := hf.int.const_mul a
    refine h.congr_fun (fun Δ _ => ?_) measurableSet_Ioi
    simp only
    ring
  eigen Δ hΔ := by
    have h := hf.eigen Δ hΔ
    unfold besselHankelTransform at h ⊢
    have e : (fun s => a * f s * hankelRho0 c s * hankelKernel c Δ s) =
        fun s => a * (f s * hankelRho0 c s * hankelKernel c Δ s) := by
      funext s; ring
    rw [e, integral_const_mul, h]
    ring

lemma hankelWindowProfile_smul (c a : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    hankelWindowProfile c (fun Δ => a * f Δ) u = a * hankelWindowProfile c f u := by
  unfold hankelWindowProfile
  dsimp only
  split_ifs <;> ring

lemma hankelMass_smul (c a : ℝ) (f : ℝ → ℝ) :
    hankelMass c (fun Δ => a * f Δ) = |a| * hankelMass c f := by
  unfold hankelMass
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun Δ _ => ?_
  simp only [abs_mul]
  ring

/-! ### The input structure -/

/-- **`lem:radial-compactness`** (`fourier_mellin.tex`) for the concrete Hankel problem; both fields
are open theorems. See the module docstring for the form of each. -/
structure RadialCompactness : Prop where
  deep_lobe_mass : ∃ C κ c₀ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → ∀ R : ℝ, 1 ≤ R → R * c ^ (1 / 3 : ℝ) < c / π ^ 2 →
      ∫ Δ in Ioo (0 : ℝ) (c / π ^ 2 - R * c ^ (1 / 3 : ℝ)), |f Δ| * hankelRho0 c Δ ≤
        C * hankelMass c f * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ * c))
  profile_compactness : ∀ (M₀ ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ),
    Tendsto c atTop atTop → (∀ n, IsHankelEigenfn (c n) ε (f n)) →
    (∀ n, hankelMass (c n) (f n) ≤ M₀) →
    ∃ (ms : ℕ → ℕ) (F : ℂ → ℂ) (C ν : ℝ),
      StrictMono ms ∧
      TendstoLocallyUniformlyOn (fun k u => hankelWindowProfile (c (ms k)) (f (ms k)) u)
        (fun u : ℝ => (F (u : ℂ)).re) atTop univ ∧
      (∀ R : ℝ, ∀ᶠ k in atTop,
        ContDiffOn ℝ 1 (hankelWindowProfile (c (ms k)) (f (ms k))) (Ioo (-R) R)) ∧
      TendstoLocallyUniformlyOn (fun k u => deriv (hankelWindowProfile (c (ms k)) (f (ms k))) u)
        (fun u : ℝ => deriv (fun x : ℝ => (F (x : ℂ)).re) u) atTop univ ∧
      Differentiable ℂ F ∧
      Integrable (fun u : ℝ => F (u : ℂ)) ∧
      0 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) ∧
      (∀ u : ℝ, (F (u : ℂ)).im = 0)


/-- `profile_compactness` for the mass-normalised profiles `Ψ_{f_n,c_n}/M[f_n]` of any sequence of
eigenfunctions (rescale `f_n ↦ f_n/M[f_n]` and take `M₀ = 1`). -/
theorem RadialCompactness.normalized_compactness (H : RadialCompactness) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (hc : Tendsto c atTop atTop)
    (hf : ∀ n, IsHankelEigenfn (c n) ε (f n)) :
    ∃ (ms : ℕ → ℕ) (F : ℂ → ℂ) (C ν : ℝ),
      StrictMono ms ∧
      TendstoLocallyUniformlyOn (fun k u => hankelWindowProfile (c (ms k)) (f (ms k)) u /
          hankelMass (c (ms k)) (f (ms k))) (fun u : ℝ => (F (u : ℂ)).re) atTop univ ∧
      (∀ R : ℝ, ∀ᶠ k in atTop, ContDiffOn ℝ 1 (fun u => hankelWindowProfile (c (ms k)) (f (ms k)) u /
          hankelMass (c (ms k)) (f (ms k))) (Ioo (-R) R)) ∧
      TendstoLocallyUniformlyOn (fun k u => deriv (fun v => hankelWindowProfile (c (ms k)) (f (ms k)) v /
          hankelMass (c (ms k)) (f (ms k))) u)
        (fun u : ℝ => deriv (fun x : ℝ => (F (x : ℂ)).re) u) atTop univ ∧
      Differentiable ℂ F ∧ Integrable (fun u : ℝ => F (u : ℂ)) ∧ 0 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) ∧ (∀ u : ℝ, (F (u : ℂ)).im = 0) := by
  let g : ℕ → ℝ → ℝ := fun k Δ => (hankelMass (c k) (f k))⁻¹ * f k Δ
  have hg_eig : ∀ k, IsHankelEigenfn (c k) ε (g k) := fun k => (hf k).smul _
  have hg_mass : ∀ k, hankelMass (c k) (g k) ≤ 1 := by
    intro k
    show hankelMass _ (fun Δ => (hankelMass (c k) (f k))⁻¹ * f k Δ) ≤ 1
    rw [hankelMass_smul]
    calc |(hankelMass (c k) (f k))⁻¹| * hankelMass (c k) (f k)
        ≤ |(hankelMass (c k) (f k))⁻¹| * |hankelMass (c k) (f k)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
      _ = |(hankelMass (c k) (f k))⁻¹ * hankelMass (c k) (f k)| := (abs_mul _ _).symm
      _ ≤ 1 := by
          by_cases h0 : hankelMass (c k) (f k) = 0
          · simp [h0]
          · simp [h0]
  have hΨ : ∀ k, hankelWindowProfile (c k) (g k) = fun u => hankelWindowProfile (c k) (f k) u /
      hankelMass (c k) (f k) := fun k => by
    funext u
    show hankelWindowProfile (c k) (fun Δ => (hankelMass (c k) (f k))⁻¹ * f k Δ) u = _
    rw [hankelWindowProfile_smul, div_eq_inv_mul]
  obtain ⟨ms, F, C, ν, hms, hloc, hC1, hder, hFd, hFi, hC, hFb, hFreal⟩ :=
    H.profile_compactness 1 ε hε c g hc hg_eig hg_mass
  refine ⟨ms, F, C, ν, hms, ?_, ?_, ?_, hFd, hFi, hC, hFb, hFreal⟩
  · simpa only [hΨ] using hloc
  · intro R
    simpa only [hΨ] using hC1 R
  · simpa only [hΨ] using hder

/-! ### `gt:7.5`, lower half at one level, from `RadialCompactness` -/

/-- A sequence of `(-1)`-feasible pairs along `c_n → ∞` fits the Airy `RadialRigidityPackage`
once `RadialCompactness` supplies the compactness field. -/
theorem exists_airy_package (H : RadialCompactness) (c : ℕ → ℝ) (hc : Tendsto c atTop atTop)
    (T : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (hfeas : ∀ n, IsHankelFeasible (c n) (-1) (T n) (f n)) :
    ∃ R : RadialRigidityPackage ℕ atTop HermiteBiehlerData.airy,
      R.c = c ∧ R.T = T ∧ R.f = f := by
  have hc_pos : ∀ᶠ n in atTop, 0 < c n := hc.eventually (eventually_gt_atTop 0)
  have h_origin : ∀ᶠ n in atTop, (-1 : ℝ) * f n 0 = ∫ Δ in Ioi 0, f n Δ * hankelRho0 (c n) Δ := by
    filter_upwards [hc_pos] with n hn
    have h := (hfeas n).eigen 0 Set.self_mem_Ici
    rw [besselHankelTransform_zero hn] at h
    exact h.symm
  have h_deep : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ R : ℝ, 1 ≤ R → ∀ᶠ n in atTop, R * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 →
        ∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)),
          |f n Δ| * hankelRho0 (c n) Δ ≤
            C * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ * c n)) := by
    obtain ⟨C, κ, c₀, hC, hκ, hlobe⟩ := H.deep_lobe_mass
    refine ⟨C, κ, hC, hκ, fun R hR => ?_⟩
    filter_upwards [hc.eventually (eventually_ge_atTop c₀)] with n hn hlt
    exact hlobe (c n) hn (-1) (Or.inr rfl) (f n) (hfeas n).toIsHankelEigenfn R hR hlt
  have h_nonneg_f : ∀ᶠ n in atTop, ∃ Δ : ℝ, 0 ≤ Δ ∧ f n Δ ≠ 0 :=
    Eventually.of_forall fun n => by
      obtain ⟨Δ, hΔ, hne⟩ := (hfeas n).nonzero
      exact ⟨Δ, hΔ, hne⟩
  have h_lower := scaled_threshold_bddBelow_raw c (-1) f T hc
    (Eventually.of_forall fun n => (hfeas n).cont) (Eventually.of_forall fun n => (hfeas n).int)
    h_nonneg_f h_origin (Eventually.of_forall fun n => (hfeas n).origin_sign)
    (Eventually.of_forall fun n => (hfeas n).tail_nonneg) h_deep
  obtain ⟨B₀, hB₀⟩ := h_lower
  refine ⟨⟨c, -1, Or.inr rfl, f, T, fun _ _ => 0, hc,
    Eventually.of_forall fun n => (hfeas n).cont,
    Eventually.of_forall fun n => (hfeas n).int,
    h_nonneg_f, h_origin,
    Eventually.of_forall fun n => (hfeas n).origin_sign,
    Eventually.of_forall fun n => (hfeas n).tail_nonneg,
    fun t ht => absurd (by simpa [HermiteBiehlerData.airy] using t.2) ht,
    fun t ht => absurd (by simpa [HermiteBiehlerData.airy] using t.2) ht,
    h_deep, ?_⟩, rfl, rfl, rfl⟩
  intro ns hns hB
  obtain ⟨B, hB⟩ := hB
  obtain ⟨ms1, F, C, ν, hms1, hloc, -, -, hFd, hFi, hC, hFb, hFreal⟩ :=
    H.normalized_compactness (-1) (Or.inr rfl) (fun k => c (ns k)) (fun k => f (ns k))
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

/-- **`gt:7.5`, lower half, one level, `ε = -1`** (`radial_rigidity_lower` of `SeparationInputs`), from
`lem:radial-compactness`: `liminf c^{-1/3}(T_c - c/π²) ≥ A = |a₁|/β₁`, in the form
"for all large `c` every feasible `T` is `≥ c/π² + (A - δ) c^{1/3}`". -/
theorem radial_rigidity_lower_of_compactness (H : RadialCompactness) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
      IsHankelFeasible c (-1) T f → c / π ^ 2 + (airyOrderCoeff - δ) * c ^ (1 / 3 : ℝ) ≤ T := by
  intro δ hδ
  by_contra hcon
  have hfreq : ∃ᶠ c : ℝ in atTop, ∃ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c (-1) T f ∧
      T < c / π ^ 2 + (airyOrderCoeff - δ) * c ^ (1 / 3 : ℝ) := by
    rw [Filter.not_eventually] at hcon
    refine hcon.mono fun c hc => ?_
    push Not at hc
    obtain ⟨T, f, hf, hT⟩ := hc
    exact ⟨T, f, hf, hT⟩
  obtain ⟨ns, hns, hns_prop⟩ := exists_seq_forall_of_frequently hfreq
  choose T f hfeas hT using hns_prop
  obtain ⟨R, hRc, hRT, -⟩ := exists_airy_package H ns hns T f hfeas
  have hge := radial_rigidity_liminf_ereal R
  have hD : -(HermiteBiehlerData.airy.tm / hankelBeta1) = airyOrderCoeff := by
    show -(airyZero 1 / hankelBeta1) = |airyZero 1| / hankelBeta1
    rw [abs_of_neg (airyZero_neg 1), neg_div]
  have hcoe : (-(HermiteBiehlerData.airy.tm / hankelBeta1) : EReal) =
      ((-(HermiteBiehlerData.airy.tm / hankelBeta1) : ℝ) : EReal) := by
    rw [EReal.coe_neg, EReal.coe_div]
  rw [hcoe, hD] at hge
  have hlt : ∀ᶠ n in atTop, (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) ≤ airyOrderCoeff - δ := by
    filter_upwards [hns.eventually (eventually_gt_atTop 0)] with n hn
    rw [hRc, hRT]
    have h1 : T n - ns n / π ^ 2 < (airyOrderCoeff - δ) * (ns n) ^ (1 / 3 : ℝ) := by linarith [hT n]
    have h2 := mul_lt_mul_of_pos_left h1 (Real.rpow_pos_of_pos hn (-(1 / 3 : ℝ)))
    have h3 : (ns n) ^ (-(1 / 3 : ℝ)) * ((airyOrderCoeff - δ) * (ns n) ^ (1 / 3 : ℝ)) =
        airyOrderCoeff - δ := by
      rw [← mul_assoc, mul_comm _ (airyOrderCoeff - δ), mul_assoc, ← Real.rpow_add hn]
      norm_num
    linarith
  have hle : Filter.liminf (fun n => (((R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) : ℝ) : EReal))
      atTop ≤ ((airyOrderCoeff - δ : ℝ) : EReal) :=
    Filter.liminf_le_of_frequently_le' (hlt.frequently.mono fun n hn => EReal.coe_le_coe_iff.mpr hn)
  have := hge.trans hle
  have h2 : airyOrderCoeff ≤ airyOrderCoeff - δ := EReal.coe_le_coe_iff.mp this
  linarith

/-- info: 'FormalResearch.SignUncertainty.radial_rigidity_lower_of_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radial_rigidity_lower_of_compactness

end FormalResearch.SignUncertainty

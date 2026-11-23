module

public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.HankelInversion

/-!
# `thm:ce-shell-gap` (Theorem H.14): the Euclidean statement and its Hankel-level form

* `ShellGapLimit D`: the extraction and constraint system `eq:ce-laplace-constraint` for radial
  Cohn-Elkies pairs on `ℝ^d` (statement of `thm:ce-shell-gap`, first half).
* `HankelShellGapLimit D`: the same statement for Hankel profiles (`HankelShellProfile`): `G` is the profile of
  `h`, `𝓗_c G` that of `ĥ`, with `ĥ ≥ 0`, `h(0) = ĥ(0) > 0`, `h ≤ 0` beyond `T` and at the shells.
* `shellGapLimit_of_hankel : HankelShellGapLimit D → ShellGapLimit D`: the Euclidean statement from the
  Hankel one, via the radial Fourier transform (`fourier_radial_hankel`) in every dimension `d ≥ 2`.
  This is the only Euclidean input of `thm:ce-shell-gap`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `thm:ce-shell-gap` (Theorem H.14), extraction and constraint system `eq:ce-laplace-constraint`:
along any sequence of dimensions `d_k → ∞` and admissible pairs (shell offsets `o(c^{1/3})`) whose
thresholds satisfy `R_k²/2 ≤ d_k/(2π²) - (u_*/β₁) c_k^{1/3} + o(c_k^{1/3})` for a fixed real `u_*`,
the window profiles of `p_k = (ĥ+h)/2`, `q_k = (ĥ-h)/2`, normalised by `M[2q_k]`, have limits
`P_∞, Q_∞ ∈ 𝒢` satisfying the two-profile system at `u_*` (`TwoProfileFeasible D u_*`). -/
def ShellGapLimit (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, (∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) →
    ∀ (u_star : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop →
      ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
        ∀ (R : ℕ → ℝ), (∀ k, R k ∈ ceShellRadiusSet D r (dk k)) →
          (∀ k, R k ^ 2 / 2 ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          TwoProfileFeasible D u_star

/-! ### The Hankel-level statement -/

/-- A Cohn-Elkies profile in Hankel form: `G` is the radial profile of `h` (`h(x) = G(‖x‖²/2)`), its
Hankel transform that of `ĥ`; `ĥ ≥ 0`, `h(0) = ĥ(0) > 0`, `h ≤ 0` on `Δ ≥ T`. -/
structure HankelShellProfile (c T : ℝ) (G : ℝ → ℝ) : Prop where
  cont : ContinuousOn G (Ici 0)
  int : IntegrableOn (fun s => G s * hankelRho0 c s) (Ioi 0)
  cont_hat : ContinuousOn (besselHankelTransform c G) (Ici 0)
  int_hat : IntegrableOn (fun s => besselHankelTransform c G s * hankelRho0 c s) (Ioi 0)
  nonneg_hat : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ besselHankelTransform c G Δ
  origin : G 0 = besselHankelTransform c G 0
  origin_pos : 0 < G 0
  tail : ∀ Δ : ℝ, T ≤ Δ → G Δ ≤ 0

/-- **`thm:ce-shell-gap`, Hankel form** (dimensions `d_k ≥ 2`, `c_k = d_k/2`): the Hankel profiles `G_k`
with thresholds `T_k ≤ c_k/π² - (u_*/β₁) c_k^{1/3} + o(c_k^{1/3})`, `G_k ≤ 0` at the (nonnegative) shell
sites, have window profiles of `p_k = (G_k + 𝓗 G_k)/2`, `q_k = (𝓗 G_k - G_k)/2` converging to a solution of
the two-profile system at `u_*`. -/
def HankelShellGapLimit (D : ShellHBData) : Prop :=
  ∀ r : ℝ → ℕ → ℝ, (∀ t : ℝ, Tendsto (fun d : ℕ => r t d / ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) atTop (𝓝 0)) →
    ∀ (u_star : ℝ) (dk : ℕ → ℕ), Tendsto dk atTop atTop → (∀ k, 2 ≤ dk k) →
      ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
        ∀ (G : ℕ → ℝ → ℝ) (T : ℕ → ℝ), (∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k)) →
          (∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
            G k (shellSite t (r t) (dk k)) ≤ 0) →
          (∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (u_star / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
            + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) →
          TwoProfileFeasible D u_star

/-! ### From a Euclidean shell-admissible `h` to a Hankel profile -/

/-- A shell-admissible pair on `ℝ^{n+1}`, `n ≥ 1`, gives a Hankel profile at `R²/2` with `G ≤ 0` at the
nonnegative shell sites. -/
theorem exists_hankelShellProfile (D : ShellHBData) (r : ℝ → ℕ → ℝ) {d : ℕ} (hd : 2 ≤ d) {R : ℝ}
    {h : Euc d → ℝ} (hh : IsShellAdmissible D r d R h) :
    ∃ G : ℝ → ℝ, HankelShellProfile ((d : ℝ) / 2) (R ^ 2 / 2) G ∧
      ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) d → G (shellSite t (r t) d) ≤ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc]
  set e₀ : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with he₀
  have hne : ‖e₀‖ = 1 := by rw [he₀, PiLp.norm_single]; simp
  set G : ℝ → ℝ := fun Δ => h (√(2 * Δ) • e₀) with hG
  have hnorm : ∀ Δ : ℝ, ‖√(2 * Δ) • e₀‖ = √(2 * Δ) := fun Δ => by
    rw [norm_smul, hne, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hlift : ∀ x : EuclSp (n + 1), G (‖x‖ ^ 2 / 2) = h x := by
    intro x
    have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
      rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg x)
    simp only [hG, e]
    exact hh.radial _ _ (by rw [norm_smul, hne, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), mul_one])
  have hGc : Continuous G := hh.continuous.comp
    ((Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).smul continuous_const)
  have hg : (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) = fun x => (h x : ℂ) :=
    funext fun x => by rw [hlift]
  have hgi : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) := by
    rw [hg]; exact hh.integrable.ofReal
  have hF : ∀ y : EuclSp (n + 1), 𝓕 (fun x : EuclSp (n + 1) => (h x : ℂ)) y =
      ((besselHankelTransform (((n : ℝ) + 1) / 2) G (‖y‖ ^ 2 / 2) : ℝ) : ℂ) := fun y => by
    rw [← hg]; exact fourier_radial_hankel n hn hGc.continuousOn hgi y
  have hFc : Continuous (𝓕 (fun x : EuclSp (n + 1) => (h x : ℂ))) :=
    continuous_fourier_of_integrable hh.integrable.ofReal
  have hy : ∀ Δ : ℝ, 0 ≤ Δ → ‖√(2 * Δ) • e₀‖ ^ 2 / 2 = Δ := fun Δ hΔ => by
    rw [hnorm, Real.sq_sqrt (by positivity)]; ring
  have hĜ : ∀ Δ : ℝ, 0 ≤ Δ → besselHankelTransform (((n : ℝ) + 1) / 2) G Δ =
      (𝓕 (fun x : EuclSp (n + 1) => (h x : ℂ)) (√(2 * Δ) • e₀)).re := fun Δ hΔ => by
    rw [hF, hy Δ hΔ, Complex.ofReal_re]
  have hĜc : ContinuousOn (besselHankelTransform (((n : ℝ) + 1) / 2) G) (Ici 0) := by
    have : Continuous fun Δ : ℝ => (𝓕 (fun x : EuclSp (n + 1) => (h x : ℂ)) (√(2 * Δ) • e₀)).re :=
      Complex.continuous_re.comp (hFc.comp
        ((Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).smul continuous_const))
    exact this.continuousOn.congr fun Δ hΔ => hĜ Δ hΔ
  refine ⟨G, ⟨hGc.continuousOn, ?_, hĜc, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (integrable_radialLift_iff n hn G).1 hgi
  · refine (integrable_radialLift_iff n hn _).1 ?_
    have : (fun x : EuclSp (n + 1) => ((besselHankelTransform (((n : ℝ) + 1) / 2) G (‖x‖ ^ 2 / 2) : ℝ) : ℂ)) =
        𝓕 (fun x : EuclSp (n + 1) => (h x : ℂ)) := funext fun x => (hF x).symm
    rw [this]; exact hh.fourier_integrable
  · intro Δ hΔ
    rw [hĜ Δ hΔ]; exact (hh.fourier_nonneg _).2
  · have h0 : ‖(0 : EuclSp (n + 1))‖ ^ 2 / 2 = 0 := by simp
    have := hF 0
    rw [h0] at this
    have e0 : G 0 = h 0 := by simp [hG]
    rw [e0, hh.origin_eq, this]
    simp
  · have : G 0 = h 0 := by simp [hG]
    rw [this]; exact hh.origin_pos
  · intro Δ hΔ
    have hR : 0 < R := hh.r_pos
    have hΔ0 : 0 ≤ Δ := le_trans (by positivity) hΔ
    refine hh.nonpos_outside _ ?_
    rw [hnorm]
    exact (Real.le_sqrt hR.le (by positivity)).2 (by linarith)
  · intro t ht htm hsite
    have := hh.shells t ht htm (√(2 * shellSite t (r t) (n + 1)) • e₀)
      (by rw [hy _ hsite])
    exact this

/-- `thm:ce-shell-gap`, Euclidean form, from the Hankel form. -/
theorem shellGapLimit_of_hankel {D : ShellHBData} (H : HankelShellGapLimit D) : ShellGapLimit D := by
  intro r hr u dk hdk ε hε R hR hbound
  obtain ⟨k₀, hk₀⟩ := (hdk.eventually_ge_atTop 2).exists_forall_of_atTop
  have hsh : ∀ k, ∃ h, IsShellAdmissible D r (dk k) (R k) h := hR
  choose h hh using hsh
  have hex : ∀ k, ∃ G : ℝ → ℝ, 2 ≤ dk (k + k₀) →
      HankelShellProfile ((dk (k + k₀) : ℝ) / 2) (R (k + k₀) ^ 2 / 2) G ∧
      ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk (k + k₀)) →
        G (shellSite t (r t) (dk (k + k₀))) ≤ 0 := fun k => by
    by_cases h2 : 2 ≤ dk (k + k₀)
    · obtain ⟨G, hG⟩ := exists_hankelShellProfile D r h2 (hh (k + k₀))
      exact ⟨G, fun _ => hG⟩
    · exact ⟨fun _ => 0, fun h => absurd h h2⟩
  choose G hG using hex
  have h2 : ∀ k, 2 ≤ dk (k + k₀) := fun k => hk₀ _ (Nat.le_add_left _ _)
  exact H r hr u (fun k => dk (k + k₀)) (hdk.comp (tendsto_add_atTop_nat k₀)) h2
    (fun k => ε (k + k₀)) (hε.comp (tendsto_add_atTop_nat k₀)) G (fun k => R (k + k₀) ^ 2 / 2)
    (fun k => (hG k (h2 k)).1) (fun k => (hG k (h2 k)).2) (fun k => hbound (k + k₀))

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.exists_hankelShellProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelShellProfile

/-- info: 'FormalResearch.SignUncertainty.shellGapLimit_of_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellGapLimit_of_hankel

end FormalResearch.SignUncertainty

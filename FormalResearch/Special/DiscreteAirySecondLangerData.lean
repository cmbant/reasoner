module

public import FormalResearch.Special.AiryParametrixLanger

/-!
# Second-order Langer data from `u`: the `C⁷` version of `langer_hrel` (S4, part 2)

`airy2_turn_full` (`DiscreteAirySecondTurn`) needs Langer-form data `(ζ, A, g)` with `ζ ∈ C⁷`, `A, g ∈ C⁶` on a ball, the
amplitude relation `g² A ζ' Sh(ζ ζ'²) = 1`, and the eikonal `Ch(ζ ζ'²) = u` (so that the diagonal `2 A Ch(ζ ζ'²)` is `2 A u`).
The first-order `langer_hrel` produces this at `ζ ∈ C³`, `A, g ∈ C²` from `u ∈ C³`; the regularity theorems it uses
(`langerZeta_spec`, `langerAmp_of_coeff`) are already stated for every `m ≥ 1` (`u ∈ C^{m+1}` gives `ζ ∈ C^{m+1}` and
`g ∈ C^m`: the Hadamard quotients lose one derivative, `ζ' = √G/(3M/2)^{1/3}` does not), so the route from `u` to second-order
Langer data costs no new analysis: `langer_hrel_seven` is `langer_hrel` with `m = 6`, the proof unchanged.

* `langer_hrel_seven`: `u ∈ C⁷` at `c`, `u c = 1`, `u'(c) > 0`, `A ∈ C⁶` at `c`, `A c > 0` give an open `U ∋ c` with
  `ζ = langerZeta u c ∈ C⁷(U)`, `A ∈ C⁶(U)`, `g = langerAmp u A c ∈ C⁶(U)`, `A, g, ζ' > 0`,
  `g² A ζ' Sh(ζ ζ'²) = 1` and `Ch(ζ ζ'²) = u` on `U`.

**Claim class: proved.**  Not formalised: analyticity of `ζ` for analytic `u` (see `LangerCoordinate`), a global chart.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.Special

/-- **`langer_hrel` at regularity `(C⁷, C⁶)`.**  See the module docstring. -/
theorem langer_hrel_seven {u A : ℝ → ℝ} {c : ℝ} (hu : ContDiffAt ℝ 7 u c) (h1 : u c = 1)
    (h2 : 0 < deriv u c) (hA : ContDiffAt ℝ 6 A c) (hA0 : 0 < A c) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧ ContDiffOn ℝ 7 (langerZeta u c) U ∧ ContDiffOn ℝ 6 A U ∧
      ContDiffOn ℝ 6 (langerAmp u A c) U ∧
      ∀ q ∈ U, 0 < A q ∧ 0 < langerAmp u A c q ∧ 0 < deriv (langerZeta u c) q ∧
        langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
          (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1 ∧
        langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2) = u q := by
  have hu' : ContDiffAt ℝ ((6 + 1 : ℕ) : WithTop ℕ∞) u c := by exact_mod_cast hu
  have hA' : ContDiffAt ℝ ((6 : ℕ) : WithTop ℕ∞) A c := by exact_mod_cast hA
  obtain ⟨hζ, -, hζev, -, -⟩ := langerZeta_spec (m := 6) (by norm_num) hu' h1 h2
  obtain ⟨hg, hgpos, hg4⟩ := langerAmp_of_coeff (m := 6) (by norm_num) hu' h1 h2 hA' hA0
  have hζ3 : ContDiffAt ℝ 7 (langerZeta u c) c := by exact_mod_cast hζ
  have hg2 : ContDiffAt ℝ 6 (langerAmp u A c) c := by exact_mod_cast hg
  have hcontu : ContinuousAt u c := hu.continuousAt
  have hF : ContinuousAt (langerF u) c := (contDiffAt_langerF (n := 7) hu h1).continuousAt
  have hSh : ∀ᶠ q in 𝓝 c, 0 < langerSinhc (langerPhi (u q - 1)) := by
    have := hF.tendsto
    rw [langerF_self h1] at this
    exact this.eventually langerSinhc_pos_nhds
  have hCh : ∀ᶠ q in 𝓝 c, langerCosh (langerPhi (u q - 1)) = u q := by
    filter_upwards [hcontu.eventually (lt_mem_nhds (show (-1 : ℝ) < u c by rw [h1]; norm_num))]
      with q hq
    have := langerP_langerPhi (z := u q - 1) (by linarith)
    unfold langerP at this; linarith
  have hApos : ∀ᶠ q in 𝓝 c, 0 < A q := hA.continuousAt.eventually (lt_mem_nhds hA0)
  have hmain : ∀ᶠ q in 𝓝 c, q ≠ c →
      langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
        (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1 := by
    filter_upwards [hζev, hg4, hgpos, hSh, hCh, hApos] with q hq4 h4 hgp hS hC hAp hqc
    obtain ⟨-, hdpos, hzz, hsign⟩ := hq4
    have hz0 : langerZeta u c q ≠ 0 := by
      rcases lt_or_gt_of_ne hqc with hlt | hgt
      · exact (hsign.2.2 hlt).ne
      · exact (hsign.1.2 hgt).ne'
    set z := langerZeta u c q with hz
    set d := deriv (langerZeta u c) q with hd
    have hF : z * d ^ 2 = langerPhi (u q - 1) := hzz
    have hSh' : 0 < langerSinhc (z * d ^ 2) := by rw [hF]; exact hS
    have hCh' : langerCosh (z * d ^ 2) = u q := by rw [hF]; exact hC
    have hid := langerCosh_sq_sub_one (z * d ^ 2)
    rw [hCh'] at hid
    have h4' : langerAmp u A c q ^ 4 = 4 * |z| / |4 * A q ^ 2 * (1 - u q ^ 2)| := h4 hqc
    have e1 : 4 * A q ^ 2 * (1 - u q ^ 2) = -(4 * A q ^ 2 * (z * d ^ 2 * langerSinhc (z * d ^ 2) ^ 2)) := by
      linear_combination (-(4 * A q ^ 2)) * hid
    have e2 : |4 * A q ^ 2 * (1 - u q ^ 2)| = 4 * A q ^ 2 * (|z| * (d ^ 2 * langerSinhc (z * d ^ 2) ^ 2)) := by
      have : 4 * A q ^ 2 * (z * d ^ 2 * langerSinhc (z * d ^ 2) ^ 2) =
          (4 * A q ^ 2 * (d ^ 2 * langerSinhc (z * d ^ 2) ^ 2)) * z := by ring
      rw [e1, abs_neg, this, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤
        4 * A q ^ 2 * (d ^ 2 * langerSinhc (z * d ^ 2) ^ 2))]
      ring
    have hzabs : 0 < |z| := abs_pos.2 hz0
    set Sh := langerSinhc (z * d ^ 2) with hShdef
    have hP : (langerAmp u A c q ^ 2 * A q * d * Sh) ^ 2 = 1 := by
      have : (langerAmp u A c q ^ 2 * A q * d * Sh) ^ 2 =
          langerAmp u A c q ^ 4 * (A q ^ 2 * d ^ 2 * Sh ^ 2) := by ring
      rw [this, h4', e2]
      field_simp
    have hgp' : 0 < langerAmp u A c q := hgp
    have hPpos : 0 < langerAmp u A c q ^ 2 * A q * d * Sh :=
      mul_pos (mul_pos (mul_pos (pow_pos hgp' 2) hAp) hdpos) hSh'
    show langerAmp u A c q ^ 2 * A q * d * Sh = 1
    nlinarith [hP, hPpos]
  have hev : ∀ᶠ q in 𝓝 c, ContDiffAt ℝ 7 (langerZeta u c) q ∧ ContDiffAt ℝ 6 A q ∧
      ContDiffAt ℝ 6 (langerAmp u A c) q ∧ 0 < A q ∧ 0 < langerAmp u A c q ∧
      0 < deriv (langerZeta u c) q ∧
      langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2) = u q ∧
      (q ≠ c → langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
        (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1) := by
    filter_upwards [hζ3.eventually (by simp), hA.eventually (by simp), hg2.eventually (by simp),
      hApos, hgpos, hζev, hCh, hmain] with q a1 a2 a3 a4 a5 a6 a7 a8
    obtain ⟨-, hdpos, hzz, -⟩ := a6
    exact ⟨a1, a2, a3, a4, a5, hdpos, by rw [hzz]; exact a7, a8⟩
  obtain ⟨V, hVsub, hVopen, hcV⟩ := mem_nhds_iff.1 hev
  have hζV : ContDiffOn ℝ 7 (langerZeta u c) V := fun q hq => (hVsub hq).1.contDiffWithinAt
  have hAV : ContDiffOn ℝ 6 A V := fun q hq => (hVsub hq).2.1.contDiffWithinAt
  have hgV : ContDiffOn ℝ 6 (langerAmp u A c) V := fun q hq => (hVsub hq).2.2.1.contDiffWithinAt
  -- the relation at `q = c` by continuity
  have hdc : ContinuousAt (deriv (langerZeta u c)) c :=
    (hζV.continuousOn_deriv_of_isOpen hVopen (by norm_num)).continuousAt (hVopen.mem_nhds hcV)
  have hfc : ContinuousAt (fun q => langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
      langerSinhc (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) c := by
    have hz : ContinuousAt (langerZeta u c) c := hζ3.continuousAt
    have hS : ContinuousAt (fun q => langerSinhc (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) c :=
      continuous_langerSinhc.continuousAt.comp (hz.mul (hdc.pow 2))
    exact (((hg2.continuousAt.pow 2).mul hA.continuousAt).mul hdc).mul hS
  have hpunct : ∀ᶠ q in 𝓝[≠] c, langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
      langerSinhc (langerZeta u c q * deriv (langerZeta u c) q ^ 2) = 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hVopen.mem_nhds hcV] with q hq hqne
    exact (hVsub hq).2.2.2.2.2.2.2 hqne
  have hcc : langerAmp u A c c ^ 2 * A c * deriv (langerZeta u c) c *
      langerSinhc (langerZeta u c c * deriv (langerZeta u c) c ^ 2) = 1 :=
    tendsto_nhds_unique (hfc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hpunct.mono fun q hq => hq.symm))
  refine ⟨V, hVopen, hcV, hζV, hAV, hgV, fun q hq => ?_⟩
  obtain ⟨-, -, -, h4, h5, h6, h7, h8⟩ := hVsub hq
  refine ⟨h4, h5, h6, ?_, h7⟩
  by_cases hqc : q = c
  · subst hqc; exact hcc
  · exact h8 hqc

/-- info: 'FormalResearch.Special.langer_hrel_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langer_hrel_seven

end FormalResearch.Special

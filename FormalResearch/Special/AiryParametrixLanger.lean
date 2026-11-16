module

public import FormalResearch.Special.AiryParametrixTaylor
public import FormalResearch.Special.AiryParametrixLattice
public import FormalResearch.Special.LangerCoordinate

/-!
# The Langer amplitude relation `g² A ζ' Sh(ζ ζ'²) = 1` for M3's coordinate, and the combined parametrix defect

This is the bridge between M3 (`LangerCoordinate`: Langer coordinate `ζ = langerZeta u c` and amplitude `g`) and
M4 (`AiryParametrixDefect`, which assumes the amplitude relation `hrel` and the diagonal `2 A Ch(ζ ζ'²)`).

* `langerCosh_sq_sub_one`: `Ch(w)² - 1 = w · Sh(w)²` for all real `w` (`sinh² √w = w (sinh √w/√w)²`;
  `Ch = langerCosh`, `Sh = langerSinhc = 2 Ch'`); proved for `w > 0` from the closed forms and extended to `ℝ`
  by the identity theorem for the two entire (real-analytic) sides.  `langerSinhc_zero`: `Sh 0 = 1`;
  `langerSinhc_pos_nhds`: `Sh > 0` near `0`.
* `langerAmp u A c = (langerAmpRatio u c / A²)^{1/4}`: the amplitude `g = (4|ζ|/|D̄|)^{1/4}` of
  `langerAmp_of_coeff`, `D̄ = 4 A² (1 - u²)`.
* `langer_hrel`: for `u ∈ C³` at `c`, `u c = 1`, `u'(c) > 0`, `A ∈ C²` at `c`, `A c > 0`, there is an open `U ∋ c`
  with `ζ ∈ C³(U)`, `A, g ∈ C²(U)`, `A, g, ζ' > 0` and, on `U`, `g² A ζ' Sh(ζ ζ'²) = 1` and
  `Ch(ζ ζ'²) = u` (eikonal; hence the diagonal `2 A Ch(ζ ζ'²) = 2 A u`).  For `q ≠ c`: `u² - 1 = F Sh(F)²`,
  `F = ζ ζ'²`, so `g⁴ = 1/(A² ζ'² Sh²)`; at `q = c` by continuity.
* `airyParametrix_defect_langer_window`, `airyParametrix_defect_langer`: M4's `airyParametrix_defect` /
  `airyParametrix_defect_lattice` with `hrel` discharged and the diagonal written `2 A u`: for every compact
  `J ⊆ U`, `|jac a d ψ k| ≤ K h² (1+|X_k|)³ airyWt X_k` on the lattice `q_k = q₀ + k h ∈ J`, for
  `a k = A(q_k - h/2)`, `d k = 2 A(q_k) u(q_k)` (only required at `q_k ∈ J`), `ψ k = g(q_k) Ai(h^{-2/3} ζ(q_k))`.

Numerical sanity check (mpmath, 30 digits, not a Lean claim): `A = 1 + 0.3q + 0.2q²`, `u = cosh √(q + 0.4q²)`,
`c = 0`, `ζ = ±(3/2 ∫₀^q √|F|)^{2/3}`, `g = (ζ/(A²(u²-1)))^{1/4}`: at `q ∈ {-0.3,-0.1,0.05,0.2,0.4}` the
quantities `g² A ζ' Sh(ζ ζ'²)` equal `1` and `Ch(ζ ζ'²) - u`, `Ch²-1-F Sh²` vanish to `10⁻³⁰`; the lattice defect over
`q ∈ {-0.3,…,0.3}` normalised by `h²(1+|X|)³ airyWt X` is about `0.015–0.018` for `h = 0.1, 0.05, 0.025`
(bounded, as the lemma asserts).

Proved.  Not formalised: the uniform `O(h²) ψ` bound for `|X| ~ h^{-2/3}` (see `AiryParametrixDefect`); the
statement is local (an open `U ∋ c` is produced, not made explicit); the `A > 0`, `C²` hypotheses are at the point `c`
only.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.Special

lemma langerSinhc_zero : langerSinhc 0 = 1 := by
  unfold langerSinhc
  have h := iteratedDeriv_langerCosh_zero 1
  simp only [iteratedDeriv_one] at h
  rw [h]; norm_num [Nat.factorial]

lemma deriv_langerCosh_of_pos {w : ℝ} (hw : 0 < w) :
    deriv langerCosh w = Real.sinh (√w) / (2 * √w) := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  have h1 : HasDerivAt (fun x : ℝ => Real.cosh (√x)) (Real.sinh (√w) * (1 / (2 * √w))) w :=
    (Real.hasDerivAt_cosh (√w)).comp w (Real.hasDerivAt_sqrt hw.ne')
  have h2 : (fun x : ℝ => Real.cosh (√x)) =ᶠ[𝓝 w] langerCosh := by
    filter_upwards [Ioi_mem_nhds hw] with x hx
    exact (langerCosh_nonneg (le_of_lt hx)).symm
  have := (h1.congr_of_eventuallyEq h2.symm).deriv
  rw [this]; ring

lemma analyticAt_langerSinhc (w : ℝ) : AnalyticAt ℝ langerSinhc w :=
  analyticAt_const.mul (analyticAt_langerCosh w).deriv

lemma langerCosh_sq_sub_one_of_pos {w : ℝ} (hw : 0 < w) :
    langerCosh w ^ 2 - 1 = w * langerSinhc w ^ 2 := by
  have hs : 0 < √w := Real.sqrt_pos.2 hw
  have hss : √w ^ 2 = w := Real.sq_sqrt hw.le
  rw [langerSinhc, deriv_langerCosh_of_pos hw, langerCosh_nonneg hw.le]
  have : 2 * (Real.sinh (√w) / (2 * √w)) = Real.sinh (√w) / √w := by field_simp
  rw [this, div_pow, hss]
  have h := Real.cosh_sq (√w)
  field_simp
  nlinarith [h]

/-- **`Ch² - 1 = w Sh²`** (`sinh² √w = w (sinh √w / √w)²`), for all real `w`. -/
theorem langerCosh_sq_sub_one (w : ℝ) : langerCosh w ^ 2 - 1 = w * langerSinhc w ^ 2 := by
  have hA : AnalyticOnNhd ℝ (fun x => langerCosh x ^ 2 - 1 - x * langerSinhc x ^ 2) univ := fun x _ =>
    (((analyticAt_langerCosh x).pow 2).sub analyticAt_const).sub
      (analyticAt_id.mul ((analyticAt_langerSinhc x).pow 2))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℝ), (fun x => langerCosh x ^ 2 - 1 - x * langerSinhc x ^ 2) z = 0 := by
    have : ∀ᶠ z in 𝓝[>] (0 : ℝ), (fun x => langerCosh x ^ 2 - 1 - x * langerSinhc x ^ 2) z = 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have := langerCosh_sq_sub_one_of_pos (show (0 : ℝ) < z from hz)
      linarith
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono _ (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0))
    exact this.frequently.filter_mono hle
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ 0) hfreq
  have h := this (mem_univ w)
  simp only [Pi.zero_apply] at h
  linarith

lemma continuous_langerSinhc : Continuous langerSinhc :=
  continuous_iff_continuousAt.2 fun w => (analyticAt_langerSinhc w).continuousAt

lemma langerSinhc_pos_nhds : ∀ᶠ w in 𝓝 (0 : ℝ), 0 < langerSinhc w :=
  continuous_langerSinhc.continuousAt.eventually (lt_mem_nhds (by rw [langerSinhc_zero]; norm_num))

/-- The amplitude `g = (4|ζ|/|D̄|)^{1/4} = (ratio/A²)^{1/4}` of `langerAmp_of_coeff` for the positive coefficient
`A` (`D̄ = 4 A² (1 - u²)`, `ratio = langerAmpRatio u c = ζ/(u² - 1)`). -/
noncomputable def langerAmp (u A : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun q => (langerAmpRatio u c q / A q ^ 2) ^ (1 / 4 : ℝ)

/-- **The Langer amplitude relation** (the gap between M3 and M4).  Let `u ∈ C³` at `c` with `u c = 1`,
`u'(c) > 0` and `A ∈ C²` at `c` with `A c > 0`.  Then for `ζ = langerZeta u c` and `g = langerAmp u A c`
there is an open `U ∋ c` on which `ζ ∈ C³`, `A, g ∈ C²`, `A, g, ζ' > 0`,
`g² A ζ' Sh(ζ ζ'²) = 1` (`Sh = 2 Ch'`; the amplitude relation assumed by `airyParametrix_defect`) and the
eikonal relation `Ch(ζ ζ'²) = u` (so the diagonal `2 A Ch(ζ ζ'²)` is `2 A u`).
Proof: `ζ ζ'² = F = Φ(u - 1)` (M3), `Ch(F) = u` (`langerP_langerPhi`), `u² - 1 = F Sh(F)²`
(`langerCosh_sq_sub_one`), so for `q ≠ c`, `g⁴ = 4|ζ|/|4A²(1 - u²)| = 1/(A² ζ'² Sh²)` (`langerAmp_of_coeff`)
and `(g² A ζ' Sh)² = 1` with positive base; at `q = c` by continuity. -/
theorem langer_hrel {u A : ℝ → ℝ} {c : ℝ} (hu : ContDiffAt ℝ 3 u c) (h1 : u c = 1)
    (h2 : 0 < deriv u c) (hA : ContDiffAt ℝ 2 A c) (hA0 : 0 < A c) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧ ContDiffOn ℝ 3 (langerZeta u c) U ∧ ContDiffOn ℝ 2 A U ∧
      ContDiffOn ℝ 2 (langerAmp u A c) U ∧
      ∀ q ∈ U, 0 < A q ∧ 0 < langerAmp u A c q ∧ 0 < deriv (langerZeta u c) q ∧
        langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
          (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1 ∧
        langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2) = u q := by
  have hu' : ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) u c := by exact_mod_cast hu
  have hA' : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) A c := by exact_mod_cast hA
  obtain ⟨hζ, -, hζev, -, -⟩ := langerZeta_spec (m := 2) (by norm_num) hu' h1 h2
  obtain ⟨hg, hgpos, hg4⟩ := langerAmp_of_coeff (m := 2) (by norm_num) hu' h1 h2 hA' hA0
  have hζ3 : ContDiffAt ℝ 3 (langerZeta u c) c := by exact_mod_cast hζ
  have hg2 : ContDiffAt ℝ 2 (langerAmp u A c) c := by exact_mod_cast hg
  have hcontu : ContinuousAt u c := hu.continuousAt
  have hF : ContinuousAt (langerF u) c := (contDiffAt_langerF (n := 3) hu h1).continuousAt
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
  have hev : ∀ᶠ q in 𝓝 c, ContDiffAt ℝ 3 (langerZeta u c) q ∧ ContDiffAt ℝ 2 A q ∧
      ContDiffAt ℝ 2 (langerAmp u A c) q ∧ 0 < A q ∧ 0 < langerAmp u A c q ∧
      0 < deriv (langerZeta u c) q ∧
      langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2) = u q ∧
      (q ≠ c → langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
        (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1) := by
    filter_upwards [hζ3.eventually (by simp), hA.eventually (by simp), hg2.eventually (by simp),
      hApos, hgpos, hζev, hCh, hmain] with q a1 a2 a3 a4 a5 a6 a7 a8
    obtain ⟨-, hdpos, hzz, -⟩ := a6
    exact ⟨a1, a2, a3, a4, a5, hdpos, by rw [hzz]; exact a7, a8⟩
  obtain ⟨V, hVsub, hVopen, hcV⟩ := mem_nhds_iff.1 hev
  have hζV : ContDiffOn ℝ 3 (langerZeta u c) V := fun q hq => (hVsub hq).1.contDiffWithinAt
  have hAV : ContDiffOn ℝ 2 A V := fun q hq => (hVsub hq).2.1.contDiffWithinAt
  have hgV : ContDiffOn ℝ 2 (langerAmp u A c) V := fun q hq => (hVsub hq).2.2.1.contDiffWithinAt
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

/-- info: 'FormalResearch.Special.langer_hrel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langer_hrel

/-- **The parametrix defect for M3's Langer data (no assumed amplitude relation): window form.**
For `u ∈ C³` at `c`, `u c = 1`, `u'(c) > 0`, `A ∈ C²` at `c`, `A c > 0`, there is an open `U ∋ c` such that
for every compact `J ⊆ U` there are `K, h₀` with, for `0 < h ≤ h₀`, `q ∈ J`, `X = h^{-2/3} ζ(q)`
(`ζ = langerZeta u c`, `g = langerAmp u A c`, `ψ = g · Ai(h^{-2/3} ζ)`):
`|A(q+h/2) ψ(q+h) + A(q-h/2) ψ(q-h) - 2 A(q) u(q) ψ(q)| ≤ K h² (1+|X|)³ airyWt X`.
Combines `langer_hrel` with `airyParametrix_defect`; the diagonal is `2 A u` since `Ch(ζ ζ'²) = u`. -/
theorem airyParametrix_defect_langer_window {u A : ℝ → ℝ} {c : ℝ} (hu : ContDiffAt ℝ 3 u c)
    (h1 : u c = 1) (h2 : 0 < deriv u c) (hA : ContDiffAt ℝ 2 A c) (hA0 : 0 < A c) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧ ∀ J : Set ℝ, IsCompact J → J ⊆ U →
      ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
        |A (q + h / 2) * (langerAmp u A c (q + h) *
              airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q + h))) +
          A (q - h / 2) * (langerAmp u A c (q - h) *
              airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q - h))) -
          2 * A q * u q * (langerAmp u A c q * airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c q))| ≤
        K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * langerZeta u c q|) ^ 3 *
          airyWt (h ^ (-(2 / 3 : ℝ)) * langerZeta u c q) := by
  obtain ⟨U, hU, hcU, hζ, hAU, hgU, hall⟩ := langer_hrel hu h1 h2 hA hA0
  refine ⟨U, hU, hcU, fun J hJ hJU => ?_⟩
  obtain ⟨K, h0, hK, hh0, H⟩ := airyParametrix_defect hU hJ hJU hζ hAU hgU
    (fun q hq => (hall q hq).2.2.2.1)
  refine ⟨K, h0, hK, hh0, fun h hh hh' q hq => ?_⟩
  have := H h hh hh' q hq
  rwa [(hall q (hJU hq)).2.2.2.2] at this

/-- **The parametrix defect for M3's Langer data on a lattice (no assumed amplitude relation).**
Same hypotheses as `airyParametrix_defect_langer_window`.  For the Jacobi data `a k = A(q₀ + k h - h/2)`,
`d k = 2 A(q_k) u(q_k)` (`q_k = q₀ + k h`), `ψ k = g(q_k) Ai(h^{-2/3} ζ(q_k))` with `ζ = langerZeta u c`,
`g = langerAmp u A c`, the lattice defect satisfies
`|jac a d ψ k| ≤ K h² (1 + |X_k|)³ airyWt X_k` whenever `q_k ∈ J` (compact `J ⊆ U`), `X_k = h^{-2/3} ζ(q_k)`,
with `K, h₀` independent of `q₀, k`.  (This is `airyParametrix_defect_lattice` with its hypothesis `hrel`
discharged by `langer_hrel`.)  Not formalised: the uniform `O(h²) ψ` bound for `|X| ~ h^{-2/3}` (see
`AiryParametrixDefect`). -/
theorem airyParametrix_defect_langer {u A : ℝ → ℝ} {c : ℝ} (hu : ContDiffAt ℝ 3 u c)
    (h1 : u c = 1) (h2 : 0 < deriv u c) (hA : ContDiffAt ℝ 2 A c) (hA0 : 0 < A c) :
    ∃ U : Set ℝ, IsOpen U ∧ c ∈ U ∧ ∀ J : Set ℝ, IsCompact J → J ⊆ U →
      ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a d ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
        (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
        (∀ k : ℤ, q₀ + k * h ∈ J → d k = 2 * A (q₀ + k * h) * u (q₀ + k * h)) →
        (∀ k : ℤ, ψ k = langerAmp u A c (q₀ + k * h) *
          airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q₀ + k * h))) →
        ∀ k : ℤ, q₀ + k * h ∈ J →
          |FormalResearch.DiscreteAiry.jac a d ψ k| ≤
            K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q₀ + k * h)|) ^ 3 *
              airyWt (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q₀ + k * h)) := by
  obtain ⟨U, hU, hcU, W⟩ := airyParametrix_defect_langer_window hu h1 h2 hA hA0
  refine ⟨U, hU, hcU, fun J hJ hJU => ?_⟩
  obtain ⟨K, h0, hK, hh0, H⟩ := W J hJ hJU
  refine ⟨K, h0, hK, hh0, fun h q₀ a d ψ hh hh' ha hd hψ k hk => ?_⟩
  have := H h hh hh' (q₀ + k * h) hk
  have q1 : q₀ + ((k + 1 : ℤ) : ℝ) * h = q₀ + k * h + h := by push_cast; ring
  have q2 : q₀ + ((k - 1 : ℤ) : ℝ) * h = q₀ + k * h - h := by push_cast; ring
  have e1 : a (k + 1) = A (q₀ + k * h + h / 2) := by
    rw [ha]; congr 1; push_cast; ring
  have e3 : ψ (k + 1) = langerAmp u A c (q₀ + k * h + h) *
      airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q₀ + k * h + h)) := by rw [hψ, q1]
  have e4 : ψ (k - 1) = langerAmp u A c (q₀ + k * h - h) *
      airyAi (h ^ (-(2 / 3 : ℝ)) * langerZeta u c (q₀ + k * h - h)) := by rw [hψ, q2]
  unfold FormalResearch.DiscreteAiry.jac
  rw [e1, ha k, e3, e4, hd k hk, hψ]
  convert this using 2

/-- info: 'FormalResearch.Special.airyParametrix_defect_langer_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_langer_window

/-- info: 'FormalResearch.Special.airyParametrix_defect_langer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_langer

/-- info: 'FormalResearch.Special.langerCosh_sq_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerCosh_sq_sub_one

end FormalResearch.Special

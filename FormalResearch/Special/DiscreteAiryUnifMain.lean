module

public import FormalResearch.Special.DiscreteAiryUnifFull
public import FormalResearch.Special.DiscreteAiryUnifAmp

/-!
# Uniform discrete-to-Airy, step 7: the quantitative theorem `discrete_airy_full_unif`

**The datum class.**  `DunDatum u A c ρ Ku m aLo aHi KA`: on the ball `B = ball c ρ`,
`u ∈ C³(B)`, `u(c) = 1`, `u'(c) ≥ m`, `|u'|, |u''|, |u'''| ≤ Ku`; `A ∈ C²(B)`, `aLo ≤ A ≤ aHi`, `|A'|, |A''| ≤ KA`.

**Theorem** (`discrete_airy_full_unif`).  For fixed `ρ, Ku, m, aLo, aHi, KA, E` (`ρ, Ku, m, aLo > 0`, `aLo ≤ aHi`, `KA, E ≥ 0`) there are
`r ≤ ρ`, `δ₀, C, C_μ, ξ₀ > 0`, depending **only** on these, such that for **every** `(u, A, c)` in the datum class the conclusion of
`discrete_airy_full` holds (canonical `langerZeta`, `langerAmp`): for `δ ≤ δ₀` and every `q₀` there *exist* indices `J < N`, `J ≤ m' ≤ N`
with `q_J ∈ [c - r, c - r + δ³)`, `q_{m'} ∈ [c, c + δ³)`, `q_N ≥ c + r/4`, `q_{N+1} ≤ c + r/2`, and for all `a, c'` within `Eδ⁶` of the exact
coefficients on the rows, the unified conclusion `DaiFull` (unique recessive `f`, unique dominant `F₂`, `|f - gAi| ≤ Cδ³ airyWt`,
`|F₂ - gBi| ≤ Cδ³ airyBiWt`, Casoratian `≥ δ/C`, every solution `κf + μF₂` with `|μ| ≤ Cmu Y_max e^{-ξ(X_N)}/δ`).

Hence uniformity over any family `(u_s, A_s, c_s)_{s ∈ S}` whose datum-class constants are uniform (e.g. a continuous family over a compact
`S`: the jets, `u'(c_s) ≥ m`, `a_±` are uniform by compactness; this general compactness remark is **not formalised**, only the Hahn family
is verified to lie in the datum class, `hahn_datum_unif`).  Mechanism: `discrete_airy_full_win` (constants explicit in the window
data and jet bounds), `dun_chart` (the Langer coordinate on an explicit ball with explicit jets), `dun_amp`, `langerAmp_eq_rel`; the
only absolute (data-free) inputs are existential constants of the analytic functions `Φ = langerPhi` (analytic at `0`) and `Sh`.

**Claim class: proved.**  The constants are *explicit expressions* in the data constants and in these absolute constants (they are not
numerically evaluated here).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The datum class (see the module docstring). -/
structure DunDatum (u A : ℝ → ℝ) (c ρ Ku m aLo aHi KA : ℝ) : Prop where
  u3 : ContDiffOn ℝ 3 u (ball c ρ)
  u0 : u c = 1
  um : m ≤ deriv u c
  ub : ∀ x ∈ ball c ρ, |deriv u x| ≤ Ku ∧ |deriv (deriv u) x| ≤ Ku ∧ |deriv (deriv (deriv u)) x| ≤ Ku
  A2 : ContDiffOn ℝ 2 A (ball c ρ)
  Ab : ∀ x ∈ ball c ρ, aLo ≤ A x ∧ A x ≤ aHi
  Aj : ∀ x ∈ ball c ρ, |deriv A x| ≤ KA ∧ |deriv (deriv A) x| ≤ KA

/-- Absolute constants of `Φ = langerPhi` (analytic at `0`). -/
lemma dun_phi_abs : ∃ ε1 B0 B1 B2 : ℝ, 0 < ε1 ∧ ε1 ≤ 1 ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧
    ContDiffOn ℝ 2 (deriv langerPhi) (ball 0 ε1) ∧
    (∀ y ∈ ball (0 : ℝ) ε1, HasDerivAt langerPhi (deriv langerPhi y) y) ∧
    ∀ y ∈ ball (0 : ℝ) ε1, |deriv langerPhi y| ≤ B0 ∧ |deriv (deriv langerPhi) y| ≤ B1 ∧
      |deriv (deriv (deriv langerPhi)) y| ≤ B2 := by
  obtain ⟨ε0, hε0, hAn⟩ := analyticAt_langerPhi.exists_ball_analyticOnNhd
  have h1 : AnalyticOnNhd ℝ (deriv langerPhi) (ball 0 ε0) := hAn.deriv
  have h2 : AnalyticOnNhd ℝ (deriv (deriv langerPhi)) (ball 0 ε0) := h1.deriv
  have h3 : AnalyticOnNhd ℝ (deriv (deriv (deriv langerPhi))) (ball 0 ε0) := h2.deriv
  have hsub : closedBall (0 : ℝ) (min (ε0 / 2) 1) ⊆ ball 0 ε0 := fun y hy => by
    rw [mem_closedBall] at hy
    rw [mem_ball]
    have := min_le_left (ε0 / 2) 1
    linarith
  have hcpt : IsCompact (closedBall (0 : ℝ) (min (ε0 / 2) 1)) := isCompact_closedBall _ _
  obtain ⟨C0, hC0⟩ := hcpt.exists_bound_of_continuousOn (h1.continuousOn.mono hsub)
  obtain ⟨C1, hC1⟩ := hcpt.exists_bound_of_continuousOn (h2.continuousOn.mono hsub)
  obtain ⟨C2, hC2⟩ := hcpt.exists_bound_of_continuousOn (h3.continuousOn.mono hsub)
  have hε1 : 0 < min (ε0 / 2) 1 := lt_min (by positivity) one_pos
  refine ⟨min (ε0 / 2) 1, |C0|, |C1|, |C2|, hε1, min_le_right _ _, abs_nonneg _, abs_nonneg _, abs_nonneg _, ?_, ?_, ?_⟩
  · exact (h1.contDiffOn_of_completeSpace).mono (ball_subset_ball ((min_le_left _ _).trans (by linarith)))
  · intro y hy
    have hy' : y ∈ ball 0 ε0 := hsub (ball_subset_closedBall hy)
    exact (hAn y hy').differentiableAt.hasDerivAt
  · intro y hy
    have hy' := ball_subset_closedBall hy
    refine ⟨?_, ?_, ?_⟩
    · have := hC0 y hy'; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
    · have := hC1 y hy'; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
    · have := hC2 y hy'; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)


/-- Third-order Taylor remainder on a window inside the ball. -/
lemma dun_taylor3 {f : ℝ → ℝ} {c ρ1 r δJ B : ℝ} (_hr : 0 ≤ r) (_hδJ : 0 ≤ δJ) (hrδ : r + δJ < ρ1)
    (hf : ContDiffOn ℝ 3 f (ball c ρ1)) (hB : ∀ x ∈ ball c ρ1, |deriv (deriv (deriv f)) x| ≤ B) :
    ∀ q ∈ Icc (c - r) (c + r), ∀ s : ℝ, |s| ≤ δJ →
      |f (q + s) - (f q + deriv f q * s + deriv (deriv f) q * s ^ 2 / 2)| ≤ B * |s| ^ 3 := by
  intro q hq s hs
  have hqc : |q - c| ≤ r := abs_le.2 ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hmem : ∀ t ∈ uIcc 0 s, q + t ∈ ball c ρ1 := by
    intro t ht
    have hts : |t| ≤ |s| := by
      rcases le_total 0 s with h0 | h0
      · rw [uIcc_of_le h0] at ht
        rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
      · rw [uIcc_of_ge h0] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
    rw [mem_ball, Real.dist_eq]
    have : |q + t - c| ≤ |q - c| + |t| := by
      have := abs_add_le (q - c) t
      rwa [show q - c + t = q + t - c by ring] at this
    linarith
  have it3 : ∀ x, deriv^[3] f x = deriv (deriv (deriv f)) x := by
    intro x; simp [Function.iterate_succ_apply']
  have it2 : ∀ x, deriv^[2] f x = deriv (deriv f) x := by
    intro x; simp [Function.iterate_succ_apply']
  have h := apx_taylor_chain 3 (fun k => deriv^[k] f) q s B
    (fun k hk t ht => apx_hasDerivAt_iterate isOpen_ball hf k hk (q + t) (hmem t ht))
    (fun t ht => by simpa [it3] using hB _ (hmem t ht)) s (by simp)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, it2, Nat.factorial, pow_zero, pow_one] at h
  convert h using 3; norm_num

/-- Second-order Taylor remainder on a window inside the ball. -/
lemma dun_taylor2 {f : ℝ → ℝ} {c ρ1 r δJ B : ℝ} (_hr : 0 ≤ r) (_hδJ : 0 ≤ δJ) (hrδ : r + δJ < ρ1)
    (hf : ContDiffOn ℝ 2 f (ball c ρ1)) (hB : ∀ x ∈ ball c ρ1, |deriv (deriv f) x| ≤ B) :
    ∀ q ∈ Icc (c - r) (c + r), ∀ s : ℝ, |s| ≤ δJ → |f (q + s) - (f q + deriv f q * s)| ≤ B * s ^ 2 := by
  intro q hq s hs
  have hqc : |q - c| ≤ r := abs_le.2 ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hmem : ∀ t ∈ uIcc 0 s, q + t ∈ ball c ρ1 := by
    intro t ht
    have hts : |t| ≤ |s| := by
      rcases le_total 0 s with h0 | h0
      · rw [uIcc_of_le h0] at ht
        rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
      · rw [uIcc_of_ge h0] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
    rw [mem_ball, Real.dist_eq]
    have : |q + t - c| ≤ |q - c| + |t| := by
      have := abs_add_le (q - c) t
      rwa [show q - c + t = q + t - c by ring] at this
    linarith
  have it2 : ∀ x, deriv^[2] f x = deriv (deriv f) x := by
    intro x; simp [Function.iterate_succ_apply']
  have h := apx_taylor_chain 2 (fun k => deriv^[k] f) q s B
    (fun k hk t ht => apx_hasDerivAt_iterate isOpen_ball hf k hk (q + t) (hmem t ht))
    (fun t ht => by simpa [it2] using hB _ (hmem t ht)) s (by simp)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, Nat.factorial, pow_zero, pow_one] at h
  rw [sq_abs] at h
  convert h using 3; norm_num

/-- `DunJets` from bounds of the derivatives on the whole ball (window `[c - r, c + r]`, increments `≤ δJ`, `r + δJ < ρ1`). -/
lemma dunJets_of_ball {ζ A g : ℝ → ℝ} {c ρ1 r δJ Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 : ℝ} (hr : 0 ≤ r)
    (hδJ : 0 ≤ δJ) (hrδ : r + δJ < ρ1) (hζ : ContDiffOn ℝ 3 ζ (ball c ρ1)) (hA : ContDiffOn ℝ 2 A (ball c ρ1))
    (hg : ContDiffOn ℝ 2 g (ball c ρ1))
    (hζb : ∀ x ∈ ball c ρ1, |ζ x| ≤ Z0 ∧ |deriv ζ x| ≤ Z1 ∧ |deriv (deriv ζ) x| ≤ Z2 ∧
      |deriv (deriv (deriv ζ)) x| ≤ Z3)
    (hAb : ∀ x ∈ ball c ρ1, |A x| ≤ A0 ∧ |deriv A x| ≤ A1 ∧ |deriv (deriv A) x| ≤ A2)
    (hgb : ∀ x ∈ ball c ρ1, |g x| ≤ g0 ∧ |deriv g x| ≤ g1 ∧ |deriv (deriv g) x| ≤ g2) :
    DunJets ζ A g (Icc (c - r) (c + r)) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ := by
  have hmemB : ∀ q ∈ Icc (c - r) (c + r), q ∈ ball c ρ1 := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hq.1, hq.2]
  exact ⟨fun q hq => (hζb q (hmemB q hq)).1, fun q hq => (hζb q (hmemB q hq)).2.1,
    fun q hq => (hζb q (hmemB q hq)).2.2.1,
    dun_taylor3 hr hδJ hrδ hζ (fun x hx => (hζb x hx).2.2.2),
    fun q hq => (hAb q (hmemB q hq)).1, fun q hq => (hAb q (hmemB q hq)).2.1,
    dun_taylor2 hr hδJ hrδ hA (fun x hx => (hAb x hx).2.2),
    fun q hq => (hgb q (hmemB q hq)).1, fun q hq => (hgb q (hmemB q hq)).2.1,
    dun_taylor2 hr hδJ hrδ hg (fun x hx => (hgb x hx).2.2)⟩


/-- Jets of `P = Φ'(u - 1) u'` (`P = F'`, `F = Φ(u-1)`) from those of `u`. -/
lemma dun_P_jets {u : ℝ → ℝ} {c ρ0 Ku ε1 B0 B1 B2 : ℝ} (hε1 : ε1 ≤ 1)
    (hΦ2 : ContDiffOn ℝ 2 (deriv langerPhi) (ball 0 ε1))
    (hΦb : ∀ y ∈ ball (0 : ℝ) ε1, |deriv langerPhi y| ≤ B0 ∧ |deriv (deriv langerPhi) y| ≤ B1 ∧
      |deriv (deriv (deriv langerPhi)) y| ≤ B2)
    (hu3 : ContDiffOn ℝ 3 u (ball c ρ0))
    (hub : ∀ x ∈ ball c ρ0, |deriv u x| ≤ Ku ∧ |deriv (deriv u) x| ≤ Ku ∧ |deriv (deriv (deriv u)) x| ≤ Ku)
    (hmap : ∀ x ∈ ball c ρ0, u x - 1 ∈ ball (0 : ℝ) ε1) :
    J2 (fun x => deriv langerPhi (u x - 1) * deriv u x) (ball c ρ0) (B0 * Ku) ((B1 * Ku) * Ku + B0 * Ku)
      ((B2 * (Ku * Ku) + B1 * Ku) * Ku + 2 * ((B1 * Ku) * Ku) + B0 * Ku) := by
  have hu2 : ContDiffOn ℝ 2 u (ball c ρ0) := hu3.of_le (by norm_num)
  have hub0 : ∀ x ∈ ball c ρ0, |u x| ≤ 2 := by
    intro x hx
    have := hmap x hx
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at this
    have h2 : |u x| ≤ |u x - 1| + 1 := by
      have := abs_add_le (u x - 1) 1
      simpa using this
    linarith
  have Ju : J2 u (ball c ρ0) 2 Ku Ku := ⟨hu2, fun x hx => ⟨hub0 x hx, (hub x hx).1, (hub x hx).2.1⟩⟩
  have Jum := J2.add isOpen_ball Ju (J2.const (S := ball c ρ0) (-1))
  have Jum' : J2 (fun x => u x - 1) (ball c ρ0) (2 + |(-1 : ℝ)|) (Ku + 0) (Ku + 0) :=
    Jum.congr isOpen_ball (fun x _ => by ring)
  have Jphi := J2.comp (φ := deriv langerPhi) (T := ball 0 ε1) isOpen_ball isOpen_ball Jum' hΦ2 hmap hΦb
  have Jdu : J2 (deriv u) (ball c ρ0) Ku Ku Ku :=
    ⟨hu3.deriv_of_isOpen isOpen_ball (by norm_num), fun x hx => ⟨(hub x hx).1, (hub x hx).2.1, (hub x hx).2.2⟩⟩
  have := J2.mul isOpen_ball Jphi Jdu
  refine this.weaken (by simp) ?_ ?_
  · simp
  · simp

/-- info: 'FormalResearch.Special.dun_phi_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dun_phi_abs

/-- info: 'FormalResearch.Special.dun_P_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dun_P_jets

end FormalResearch.Special

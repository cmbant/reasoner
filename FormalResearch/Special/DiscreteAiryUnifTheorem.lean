module

public import FormalResearch.Special.DiscreteAiryUnifMain

/-!
# Uniform discrete-to-Airy, step 8: the proof of `discrete_airy_full_unif`

See `DiscreteAiryUnifMain` for the statement of the datum class and the discussion.  Proof outline: absolute constants (`Φ`, `Sh`) →
jets of `P = F'` → `dun_chart` on `ball c ρ₀` → shrink to `ball c ρ₁` so that `|ζζ'²| < ε_S` → `dun_amp` (jets of `g̃`) →
`langerAmp = g̃` → `DalTurnWin`, `DunJets`, `hrel`, `heik` on the window `[c - ρ₁/2, c + ρ₁/2]` →
`discrete_airy_full_win`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **The quantitative unified discrete-to-Airy theorem.**  See `DiscreteAiryUnifMain`. -/
theorem discrete_airy_full_unif (ρ Ku m aLo aHi KA E : ℝ) (hρ : 0 < ρ) (hKu : 0 < Ku) (hm : 0 < m)
    (haLo : 0 < aLo) (haLH : aLo ≤ aHi) (hKA : 0 ≤ KA) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ r ≤ ρ ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ {u A : ℝ → ℝ} {c : ℝ}, DunDatum u A c ρ Ku m aLo aHi KA →
        ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m' N : ℤ, J < N ∧ J ≤ m' ∧ m' ≤ N ∧
          (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c - r) (c + r)) ∧
          c - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c - r + δ ^ 3 ∧ c ≤ dalQ q₀ δ m' ∧
          dalQ q₀ δ m' < c + δ ^ 3 ∧ c + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c + r / 2 ∧
          ∀ a cc : ℤ → ℝ,
            (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
            (∀ k ∈ Finset.Icc (J + 1) N, |cc k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
            DaiFull a cc (turnX u c q₀ δ) (fun k => langerAmp u A c (dalQ q₀ δ k)) J m' N δ C Cmu ξ0 := by
  obtain ⟨ε1, B0, B1, B2, hε1, hε11, hB0, hB1, hB2, hΦ2, hΦd, hΦb⟩ := dun_phi_abs
  obtain ⟨εS, Msh, hεS, hMsh, hShpos, hShb⟩ := dun_sh_abs
  set Kf0 : ℝ := B0 * Ku with hKf0
  set Kf1 : ℝ := (B1 * Ku) * Ku + B0 * Ku with hKf1
  set Kf2 : ℝ := (B2 * (Ku * Ku) + B1 * Ku) * Ku + 2 * ((B1 * Ku) * Ku) + B0 * Ku with hKf2
  have hKf1n : 0 ≤ Kf1 := by rw [hKf1]; positivity
  set ρ0 : ℝ := min ρ (min (ε1 / (2 * (Ku + 1))) (m / (Kf1 + 1))) with hρ0
  have hρ0p : 0 < ρ0 := lt_min hρ (lt_min (by positivity) (by positivity))
  have hρ0ρ : ρ0 ≤ ρ := min_le_left _ _
  have hρ0ε : Ku * ρ0 < ε1 := by
    have h1 : ρ0 ≤ ε1 / (2 * (Ku + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : Ku * (ε1 / (2 * (Ku + 1))) < ε1 := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hKu.le) h2
  have hρ0m : Kf1 * ρ0 ≤ m := by
    have h1 : ρ0 ≤ m / (Kf1 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc Kf1 * ρ0 ≤ Kf1 * (m / (Kf1 + 1)) := mul_le_mul_of_nonneg_left h1 hKf1n
      _ = (Kf1 / (Kf1 + 1)) * m := by ring
      _ ≤ 1 * m := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).2 (by linarith)) hm.le
      _ = m := one_mul m
  obtain ⟨c1, d0, d1, d2, hc1, Hchart⟩ := dun_chart m ρ0 Kf0 Kf1 Kf2 hm
  set D0 : ℝ := max d0 c1 with hD0
  set D1 : ℝ := max d1 0 with hD1
  set D2 : ℝ := max d2 0 with hD2
  have hD0c : c1 ≤ D0 := le_max_right _ _
  have hD0p : 0 < D0 := lt_of_lt_of_le hc1 hD0c
  set ρ1 : ℝ := min ρ0 (εS / (2 * (D0 ^ 3 + 1))) with hρ1
  have hρ1p : 0 < ρ1 := lt_min hρ0p (by positivity)
  have hρ1ρ0 : ρ1 ≤ ρ0 := min_le_left _ _
  have hρ1ε : D0 ^ 3 * ρ1 < εS := by
    have h1 : ρ1 ≤ εS / (2 * (D0 ^ 3 + 1)) := min_le_right _ _
    have h2 : D0 ^ 3 * (εS / (2 * (D0 ^ 3 + 1))) < εS := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith [pow_pos hD0p 3]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
  obtain ⟨gmin, g0, g1, g2, hgmin, hgle, Hamp⟩ := dun_amp aLo aHi KA c1 D0 D1 D2 εS Msh ρ1 haLo haLH hc1 hD0c
    hρ1p hShpos hεS hShb
  set G1 : ℝ := max g1 0 with hG1
  set G2 : ℝ := max g2 0 with hG2
  have hg0p : 0 < g0 := lt_of_lt_of_le hgmin hgle
  set r : ℝ := ρ1 / 2 with hr
  set δJ : ℝ := ρ1 / 4 with hδJ
  have hrp : 0 < r := by positivity
  have hδJp : 0 < δJ := by positivity
  have hrδ : r + δJ < ρ1 := by rw [hr, hδJ]; linarith
  obtain ⟨δ0, C, Cmu, ξ0, hδ0, hδ01, hC, hCmu, hξ0, Hwin⟩ := discrete_airy_full_win r c1 D0 gmin g0 aLo aHi Ku E
    (D0 * ρ1) D0 D1 D2 aHi KA KA g0 G1 G2 δJ hrp hc1 hD0c hgmin hgle haLo haLH hKu.le hE (by positivity)
    hD0p.le (le_max_right _ _) (le_max_right _ _) (haLo.le.trans haLH) hKA hKA hg0p.le (le_max_right _ _)
    (le_max_right _ _) hδJp
  refine ⟨r, δ0, C, Cmu, ξ0, hrp, by rw [hr]; linarith [hρ1ρ0, hρ0ρ], hδ0, hδ01, hC, hCmu, hξ0, ?_⟩
  intro u A c hD δ q₀ hδ hδδ0
  have hB1 : ball c ρ1 ⊆ ball c ρ0 := ball_subset_ball hρ1ρ0
  have hB0 : ball c ρ0 ⊆ ball c ρ := ball_subset_ball hρ0ρ
  have hB10 : ball c ρ1 ⊆ ball c ρ := hB1.trans hB0
  have hcb0 : c ∈ ball c ρ0 := mem_ball_self hρ0p
  have hcb1 : c ∈ ball c ρ1 := mem_ball_self hρ1p
  have hu3_0 : ContDiffOn ℝ 3 u (ball c ρ0) := hD.u3.mono hB0
  have hub0 : ∀ x ∈ ball c ρ0, |deriv u x| ≤ Ku ∧ |deriv (deriv u) x| ≤ Ku ∧
      |deriv (deriv (deriv u)) x| ≤ Ku := fun x hx => hD.ub x (hB0 hx)
  have hu1 : ContDiffOn ℝ 1 u (ball c ρ0) := hu3_0.of_le (by norm_num)
  have hmap : ∀ x ∈ ball c ρ0, u x - 1 ∈ ball (0 : ℝ) ε1 := by
    intro x hx
    have := lip_of_deriv_bound hu1 (fun z hz => (hub0 z hz).1) hx hcb0
    rw [hD.u0] at this
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    have hxc : |x - c| < ρ0 := by simpa [Real.dist_eq] using hx
    calc |u x - 1| ≤ Ku * |x - c| := this
      _ < Ku * ρ0 := mul_lt_mul_of_pos_left hxc hKu
      _ < ε1 := hρ0ε
  have hJP := dun_P_jets hε11 hΦ2 hΦb hu3_0 hub0 hmap
  have hFd : ∀ x ∈ ball c ρ0, HasDerivAt (langerF u) (deriv langerPhi (u x - 1) * deriv u x) x := by
    intro x hx
    have hux : HasDerivAt u (deriv u x) x := j2_d1 isOpen_ball (hu3_0.of_le (by norm_num)) hx
    exact (hΦd _ (hmap x hx)).comp x (hux.sub_const 1)
  have hF0 : langerF u c = 0 := langerF_self hD.u0
  have hPm : ∀ x ∈ ball c ρ0, m ≤ deriv langerPhi (u x - 1) * deriv u x := by
    intro x hx
    have hl : |deriv langerPhi (u x - 1) * deriv u x - deriv langerPhi (u c - 1) * deriv u c| ≤
        Kf1 * |x - c| := lip_of_j2 hJP hx hcb0
    have hxc : |x - c| < ρ0 := by simpa [Real.dist_eq] using hx
    have hPc : deriv langerPhi (u c - 1) * deriv u c = 2 * deriv u c := by
      rw [hD.u0, sub_self, deriv_langerPhi_zero]
    have h2 : Kf1 * |x - c| ≤ Kf1 * ρ0 := mul_le_mul_of_nonneg_left hxc.le hKf1n
    have h1 := (abs_le.1 hl).1
    rw [hPc] at h1
    linarith [hD.um]
  obtain ⟨hζ3, hDj, hDl, hzz, hzne⟩ := Hchart hJP hFd hF0 hPm
  have hζ3' : ContDiffOn ℝ 3 (langerZeta u c) (ball c ρ0) := hζ3
  have hζ3_1 : ContDiffOn ℝ 3 (langerZeta u c) (ball c ρ1) := hζ3'.mono hB1
  have hDj1 : J2 (deriv (langerZeta u c)) (ball c ρ1) D0 D1 D2 :=
    (hDj.mono hB1).weaken (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
  have hDl1 : ∀ x ∈ ball c ρ1, c1 ≤ deriv (langerZeta u c) x := fun x hx => hDl x (hB1 hx)
  have hζ0 : langerZeta u c c = 0 := langerZetaOf_zero _ _
  have hζbound : ∀ x ∈ ball c ρ1, |langerZeta u c x| ≤ D0 * |x - c| := fun x hx => by
    have := lip_of_deriv_bound (hζ3_1.of_le (by norm_num)) (fun z hz => (hDj1.2 z hz).1) hx hcb1
    rwa [hζ0, sub_zero] at this
  have hFs : ∀ x ∈ ball c ρ1, |langerZeta u c x * deriv (langerZeta u c) x ^ 2| < εS := by
    intro x hx
    have hxc : |x - c| < ρ1 := by simpa [Real.dist_eq] using hx
    have h1 := hζbound x hx
    have h2 : |deriv (langerZeta u c) x| ≤ D0 := (hDj1.2 x hx).1
    rw [abs_mul, abs_pow]
    calc |langerZeta u c x| * |deriv (langerZeta u c) x| ^ 2 ≤ (D0 * |x - c|) * D0 ^ 2 :=
          mul_le_mul h1 (pow_le_pow_left₀ (abs_nonneg _) h2 2) (by positivity) (by positivity)
      _ ≤ (D0 * ρ1) * D0 ^ 2 := by gcongr
      _ = D0 ^ 3 * ρ1 := by ring
      _ < εS := hρ1ε
  have hzz1 : ∀ x ∈ ball c ρ1, langerZeta u c x * deriv (langerZeta u c) x ^ 2 = langerPhi (u x - 1) :=
    fun x hx => hzz x (hB1 hx)
  have heik : ∀ x ∈ ball c ρ1, langerCosh (langerZeta u c x * deriv (langerZeta u c) x ^ 2) = u x := by
    intro x hx
    have hu1' : |u x - 1| < ε1 := by
      have := hmap x (hB1 hx); rwa [mem_ball_zero_iff, Real.norm_eq_abs] at this
    have h := langerP_langerPhi (z := u x - 1) (by linarith [(abs_lt.1 hu1').1, hε11])
    unfold langerP at h
    rw [hzz1 x hx]; linarith
  have hA2' : ContDiffOn ℝ 2 A (ball c ρ1) := hD.A2.mono hB10
  have hApos : ∀ x ∈ ball c ρ1, 0 < A x := fun x hx => lt_of_lt_of_le haLo (hD.Ab x (hB10 hx)).1
  have hAJ : J2 A (ball c ρ1) aHi KA KA :=
    ⟨hA2', fun x hx => ⟨by rw [abs_of_pos (hApos x hx)]; exact (hD.Ab x (hB10 hx)).2,
      (hD.Aj x (hB10 hx)).1, (hD.Aj x (hB10 hx)).2⟩⟩
  have hShp : ∀ x ∈ ball c ρ1,
      0 < langerSinhc (langerZeta u c x * deriv (langerZeta u c) x ^ 2) :=
    fun x hx => lt_trans (by norm_num) (hShpos _ (hFs x hx))
  obtain ⟨hJg, hglow⟩ := Hamp hAJ (fun x hx => (hD.Ab x (hB10 hx)).1) hζ3_1 hDj1 hDl1 hζ0 hFs
  have hu3_1 : ContDiffOn ℝ 3 u (ball c ρ1) := hD.u3.mono hB10
  have hident := langerAmp_eq_rel hρ1p hu3_1 hD.u0 (lt_of_lt_of_le hm hD.um)
    (fun x hx => lt_of_lt_of_le hc1 (hDl1 x hx)) (fun x hx hxc => hzne x (hB1 hx) hxc) hShp hApos heik
  have hJg2 : J2 (langerAmp u A c) (ball c ρ1) g0 G1 G2 :=
    (hJg.congr isOpen_ball (fun x hx => hident x hx)).weaken le_rfl (le_max_left _ _) (le_max_left _ _)
  have hglow' : ∀ x ∈ ball c ρ1, gmin ≤ langerAmp u A c x := fun x hx => by
    rw [hident x hx]; exact hglow x hx
  have hrel : ∀ q ∈ ball c ρ1, langerAmp u A c q ^ 2 * A q * deriv (langerZeta u c) q *
      (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = 1 := by
    intro q hq
    rw [hident q hq]
    set R : ℝ := A q * deriv (langerZeta u c) q *
      langerSinhc (langerZeta u c q * deriv (langerZeta u c) q ^ 2) with hR
    have hRp : 0 < R := mul_pos (mul_pos (hApos q hq) (lt_of_lt_of_le hc1 (hDl1 q hq))) (hShp q hq)
    have e1 : (R ^ (-(1 / 2 : ℝ))) ^ 2 = R⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
      norm_num
      exact Real.rpow_neg_one R
    have e2 : A q * deriv (langerZeta u c) q *
        (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2)) = R := rfl
    calc (R ^ (-(1 / 2 : ℝ))) ^ 2 * A q * deriv (langerZeta u c) q *
          (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2))
        = (R ^ (-(1 / 2 : ℝ))) ^ 2 * (A q * deriv (langerZeta u c) q *
          (2 * deriv langerCosh (langerZeta u c q * deriv (langerZeta u c) q ^ 2))) := by ring
      _ = 1 := by rw [e2, e1]; exact inv_mul_cancel₀ hRp.ne'
  have hsub : Icc (c - r) (c + r) ⊆ ball c ρ1 := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt]
    have : r < ρ1 := by linarith
    constructor <;> linarith [hq.1, hq.2]
  have hT : DalTurnWin (langerZeta u c) (langerAmp u A c) A u c r c1 D0 gmin g0 aLo aHi KA G1 Ku :=
    { r_pos := hrp, c1_pos := hc1, c1_le := hD0c, gmin_pos := hgmin, gmin_le := hgle, Amin_pos := haLo,
      Amin_le := haLH, LA_nonneg := hKA, Lg_nonneg := le_max_right _ _, Lu_nonneg := hKu.le, zeta0 := hζ0,
      u0 := hD.u0,
      der := fun q hq => ⟨j2_d1 isOpen_ball (hζ3_1.of_le (by norm_num)) (hsub hq), hDl1 q (hsub hq),
        (le_abs_self _).trans (hDj1.2 q (hsub hq)).1⟩,
      gb := fun q hq => ⟨hglow' q (hsub hq), (le_abs_self _).trans (hJg2.2 q (hsub hq)).1⟩,
      Ab := fun q hq => hD.Ab q (hB10 (hsub hq)),
      lip := fun x hx y hy =>
        ⟨lip_of_deriv_bound (hA2'.of_le (by norm_num)) (fun z hz => (hD.Aj z (hB10 hz)).1) (hsub hx) (hsub hy),
         lip_of_deriv_bound (hJg2.1.of_le (by norm_num)) (fun z hz => (hJg2.2 z hz).2.1) (hsub hx) (hsub hy),
         lip_of_deriv_bound (hu3_1.of_le (by norm_num)) (fun z hz => (hD.ub z (hB10 hz)).1) (hsub hx)
           (hsub hy)⟩ }
  have hjets := dunJets_of_ball (c := c) (ρ1 := ρ1) hrp.le hδJp.le hrδ hζ3_1 hA2' hJg2.1
    (Z0 := D0 * ρ1) (Z1 := D0) (Z2 := D1) (Z3 := D2) (A0 := aHi) (A1 := KA) (A2 := KA) (g0 := g0)
    (g1 := G1) (g2 := G2)
    (fun x hx => ⟨(hζbound x hx).trans (mul_le_mul_of_nonneg_left (by
        have : |x - c| < ρ1 := by simpa [Real.dist_eq] using hx
        exact this.le) hD0p.le), (hDj1.2 x hx).1, (hDj1.2 x hx).2.1, (hDj1.2 x hx).2.2⟩)
    hAJ.2 hJg2.2
  exact Hwin isOpen_ball hsub hζ3_1 hA2' hJg2.1 hrel heik hT hjets δ q₀ hδ hδδ0

/-- info: 'FormalResearch.Special.discrete_airy_full_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_full_unif

end FormalResearch.Special

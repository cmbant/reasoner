module

public import FormalResearch.Special.DiscreteAiryPhysChains
public import FormalResearch.Special.DiscreteAiryPhysHahn

/-!
# The Airy window of the actual `3j` chain with the chart data exported (plan K1, step M-d, part 2)

`hahn_chain_airy_full` (`DiscreteAiryPhysChains`) gives `Ŷ_k = κ g Ai(X_k) + μ g Bi(X_k) + O(δ³)` on the macroscopic window but does
not export the chart data (the Langer-chart radius `r` is existential in `dal_turn_data`, so a bound on `g` cannot be recovered
afterwards).  This module re-runs the proof of `discrete_airy_full` with extra conclusions, independent of the coefficients:

* `kc_turn_full`: `discrete_airy_full` with `g_min ≤ |g| ≤ g_max` on the whole window `[J, N+1]`, `X_k ≤ 1/4` for `J ≤ k ≤ m+1` (the sites up to one
  past the turn, `q_m ∈ [q_*, q_*+h)`), the lattice gaps `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ`, `0 ≤ X_m ≤ c₂ δ`, `c₁ r/(4δ²) ≤ X_N` and the Lipschitz bound
  `|g(q_{k+1}) - g(q_k)| ≤ L_g δ³` (the single proof; used for the Hermite chain, `HermiteKappaEdge`);
* `kc_turn`: the weaker statement (`g ≤ g_max` and `X_k ≤ 1/4` only), a projection of `kc_turn_full`; `DiscreteAiryKappaChart2.kc2_turn` is the projection with
  `g_min`, the gaps and `X_N` but without `L_g`;
* `kc_hahn_full`: `discrete_airy_hahn_racah_full` (closed-form Hahn / centred Racah recurrence) with the `kc_turn` extras; `DiscreteAiryKappaMain`
  composes it with `hahn_class_chain` and `hahn_chain_abs_le` for the actual `3j` chain (`τ = +1`, integer `M, σ`, rational `x ∈ (0,1)`).

**Claim class: proved** (the proof of `discrete_airy_full` is repeated once, with the extra conjuncts; nothing else changes).  The extra conjuncts could be
folded into `discrete_airy_full` itself (`DiscreteAiryPhysTurn`), which would make this theorem a one-line restatement.

**Not formalised here.**  The value of `κ` (it is `hahn_chain_kappa_sharp`, `DiscreteAiryKappaSharpFinal`); `τ = -1`; Racah (the `6j` value of `κ` is `racah_chain_kappa_sharp`, `RacahKappa*`, built on its own window data `RkWinAt`, not on `kc_hahn_full`).
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma kc_mono {X : ℤ → ℝ} {J N : ℤ} (h : ∀ k ∈ Finset.Icc J N, X k ≤ X (k + 1)) :
    ∀ k k' : ℤ, J ≤ k → k ≤ k' → k' ≤ N + 1 → X k ≤ X k' := by
  intro k k' hk hkk' hk'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k' - k := ⟨(k' - k).toNat, Int.toNat_of_nonneg (by omega)⟩
  have : ∀ n : ℕ, k + (n : ℤ) ≤ N + 1 → X k ≤ X (k + (n : ℤ)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn'
      have h1 := ih (by push_cast at hn'; omega)
      have h2 := h (k + (n : ℤ)) (by rw [Finset.mem_Icc]; push_cast at hn'; omega)
      rw [show k + ((n + 1 : ℕ) : ℤ) = k + (n : ℤ) + 1 by push_cast; ring]
      linarith
  have := this n (by omega)
  rwa [show k + (n : ℤ) = k' by omega] at this

/-- **`discrete_airy_full` with the full chart data exported** (the single proof behind `kc_turn`, `kc2_turn` (`DiscreteAiryKappaChart2`) and `hermite_kappa_edge`
(`HermiteKappaEdge`)): the statement of `discrete_airy_full` (`DiscreteAiryPhysTurn`) with, in addition, `g_min ≤ g ≤ g_max` on the window `[J, N+1]`, `X_k ≤ 1/4` for
`k ≤ m+1`, the lattice gaps `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ`, `0 ≤ X_m ≤ c₂ δ`, `c₁ r/(4δ²) ≤ X_N`, `c₂ δ ≤ 1/8` and the Lipschitz bound `|g(q_{k+1}) - g(q_k)| ≤ L_g δ³`
(the data of the chart are not exported by `discrete_airy_full`, whose radius `r` is existential). -/
theorem kc_turn_full {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu ξ0 gmax gmin c1 c2 Lg : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ Lg ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        (∀ k ∈ Finset.Icc J (N + 1), |langerAmp u A c0 (dalQ q₀ δ k)| ≤ gmax) ∧
        (∀ k ∈ Finset.Icc J (m + 1), turnX u c0 q₀ δ k ≤ 1 / 4) ∧
        (∀ k ∈ Finset.Icc J (N + 1), gmin ≤ langerAmp u A c0 (dalQ q₀ δ k)) ∧
        (∀ k ∈ Finset.Icc J N, c1 * δ ≤ turnX u c0 q₀ δ (k + 1) - turnX u c0 q₀ δ k ∧
          turnX u c0 q₀ δ (k + 1) - turnX u c0 q₀ δ k ≤ c2 * δ) ∧
        (0 ≤ turnX u c0 q₀ δ m ∧ turnX u c0 q₀ δ m ≤ c2 * δ) ∧
        c1 * (r / 4) / δ ^ 2 ≤ turnX u c0 q₀ δ N ∧
        (∀ k ∈ Finset.Icc J N, |langerAmp u A c0 (dalQ q₀ δ (k + 1)) - langerAmp u A c0 (dalQ q₀ δ k)| ≤ Lg * δ ^ 3) ∧
        c2 * δ ≤ 1 / 8 ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DaiFull a c (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r, c1, c2, gmin, gmax, Amin, Amax, LA, Lg, Lu, U, T, hrr0, hU, hsub, hζ, hAU, hgU, hrel, heik⟩ :=
    dal_turn_data hu h1 h2 hA hA0 hr0
  obtain ⟨δL, hδL, hδL1, HL⟩ := dao_lattice T.r_pos T.c1_pos T.c1_le T.zeta0 T.der
  obtain ⟨KA, KA', δ1, hKA, -, hδ1, hδ11, HA⟩ := dal_exact_defect hU hsub hζ hAU hgU hrel heik
  obtain ⟨KB, δ2, hKB, hδ2, hδ21, HB⟩ := dao_exact_defect_bi hU hsub hζ hAU hgU hrel heik
  have hc1 := T.c1_pos
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 T.c1_le
  have hr := T.r_pos
  have hAmin := T.Amin_pos
  have hgmin := T.gmin_pos
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin T.gmin_le
  have hπ := Real.pi_pos
  set K0 : ℝ := max KA KB with hK0
  set M : ℝ := c2 * r with hM
  have hM0 : 0 ≤ M := by positivity
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  set K : ℝ := K0 + E * (450 * gmax * (2 * Cn + 1)) with hK
  have hKnn : 0 ≤ K := by
    have : 0 ≤ K0 := (hKA.le.trans (le_max_left _ _))
    have : 0 ≤ Cn := by positivity
    rw [hK]; positivity
  set ca : ℝ := Amin / 2 with hca
  have hcap : 0 < ca := by positivity
  set Cl : ℝ := 475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) with hCl
  have hCl0 : 0 ≤ Cl := by
    have := Real.sqrt_nonneg (2 + M)
    rw [hCl]; positivity
  set Q : ℝ := 4 * Real.pi / (ca * gmin ^ 2 * c1) with hQ
  have hQp : 0 < Q := by rw [hQ]; positivity
  set Cd : ℝ := 7200 * gmax * Cl + Q with hCd
  set Cmu : ℝ := 50 * gmax * (Amax + E) * Q with hCmu
  have hAmax : 0 < Amax := lt_of_lt_of_le hAmin T.Amin_le
  have hCdp : 0 < Cd := by rw [hCd]; positivity
  set Aa : ℝ := Amax + E with hAa
  set Cc : ℝ := 2 * Amax * (1 + Lu * r) + E with hCc
  have hLu := T.Lu_nonneg
  have hAmin := T.Amin_pos
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hAa0 : 0 ≤ Aa := by rw [hAa]; positivity
  have hCn0 : 0 < Cn := by rw [hCn]; positivity
  set C : ℝ := Cd + Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca with hC
  have hCpos : 0 < C := by
    have : 0 ≤ Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca := by positivity
    rw [hC]; linarith
  have hξ0 : 0 < 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) := by positivity
  refine ⟨r, min δL (min δ1 (min δ2 (min (1 / (8 * c2)) (min (1 / (4 * (Cl + 1))) (min (Amin / (2 * (E + 1))) (r / 8)))))),
    C, Cmu, 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ), gmax, gmin, c1, c2, Lg, hr, hrr0, ?_, ?_, hCpos, by positivity, hξ0, hgmax,
    hgmin, T.gmin_le, hc1, T.c1_le, T.Lg_nonneg, ?_⟩
  · refine lt_min hδL (lt_min hδ1 (lt_min hδ2 (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))))
  · exact (min_le_left _ _).trans hδL1
  intro δ q₀ hδ hδ0
  obtain ⟨hδL', hrest⟩ := le_min_iff.1 hδ0
  obtain ⟨hδ1', hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδ2', hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδc2, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδCl, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδE, hδr⟩ := le_min_iff.1 hrest
  have hδ11 : δ ≤ 1 := hδL'.trans hδL1
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hXN⟩ := HL δ q₀ hδ hδL'
  have hδ3r : δ ^ 3 ≤ r / 8 := (dap_cube_le hδ hδ11).trans hδr
  have hJN : J < N := dap_JN hδ hδ3r hqJ2 hqN
  have hc2δ : c2 * δ ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hδc2
    nlinarith only [hδc2]
  have hg : ∀ k ∈ Finset.Icc J (N + 1), |langerAmp u A c0 (dalQ q₀ δ k)| ≤ gmax := fun k hk => by
    have := T.gb _ (hwin k hk)
    rw [abs_of_pos (lt_of_lt_of_le hgmin this.1)]
    exact this.2
  have hXm : ∀ k ∈ Finset.Icc J (m + 1), turnX u c0 q₀ δ k ≤ 1 / 4 := fun k hk => by
    rw [Finset.mem_Icc] at hk
    have hmono : ∀ k ∈ Finset.Icc J N, turnX u c0 q₀ δ k ≤ turnX u c0 q₀ δ (k + 1) := fun k hk => by
      have := (hgap k hk).1
      have h3 : 0 ≤ c1 * δ := by positivity
      linarith only [this, h3]
    have h1 := kc_mono hmono k (m + 1) hk.1 hk.2 (by omega)
    have h2 := (hgap m (by rw [Finset.mem_Icc]; omega)).2
    linarith only [h1, h2, hX1, hc2δ]
  have hLgb : ∀ k ∈ Finset.Icc J N, |langerAmp u A c0 (dalQ q₀ δ (k + 1)) - langerAmp u A c0 (dalQ q₀ δ k)| ≤ Lg * δ ^ 3 := by
    intro k hk
    have hk1 : k + 1 ≤ N + 1 := by rw [Finset.mem_Icc] at hk; omega
    have h := (T.lip _ (hwin (k + 1) (by rw [Finset.mem_Icc] at hk ⊢; omega)) _ (hwin k (by rw [Finset.mem_Icc] at hk ⊢; omega))).2.1
    have e : |dalQ q₀ δ (k + 1) - dalQ q₀ δ k| = δ ^ 3 := by
      simp only [dalQ]; push_cast
      rw [show q₀ + ((k : ℝ) + 1) * δ ^ 3 - (q₀ + (k : ℝ) * δ ^ 3) = δ ^ 3 by ring]
      exact abs_of_pos (by positivity)
    rw [e] at h
    exact h
  have hgl : ∀ k ∈ Finset.Icc J (N + 1), gmin ≤ langerAmp u A c0 (dalQ q₀ δ k) := fun k hk => (T.gb _ (hwin k hk)).1
  refine ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hg, hXm, hgl, hgap, ⟨hX0, hX1⟩, hXN, hLgb, hc2δ, ?_⟩
  intro a c ha hc
  have hEδ : E * δ ^ 6 ≤ Amin / 2 := dao_E_arith hE hδ hδ11 hδE
  have hsmall : Cl * δ ^ 3 ≤ 1 / 4 := dao_small_arith hCl0 hδ hδ11 hδCl
  have hmid := dal_mid (q₀ := q₀) (δ := δ) (c0 := c0) (r := r) hwin hδ
  have halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k :=
    dao_turn_alow (A := fun k => A (dalQ q₀ δ k - δ ^ 3 / 2)) (a := a)
      (fun k hk => (T.Ab _ (hmid k hk)).1) ha hEδ
  have hE6 : E * δ ^ 6 ≤ E := mul_le_of_le_one_right hE (pow_le_one₀ hδ.le hδ11)
  have haNk : ∀ k ∈ Icc (J + 1) (N + 1), a k ≤ Aa := by
    intro k hk
    have h5 := (abs_le.1 (ha k hk)).2
    have h6 := (T.Ab _ (hmid k hk)).2
    rw [hAa]
    linarith only [h5, h6, hE6]
  have haN : a (N + 1) ≤ Aa := haNk (N + 1) (by rw [mem_Icc]; omega)
  have haN' : a N ≤ Aa := haNk N (by rw [mem_Icc]; omega)
  have hcN : |c N| ≤ Cc :=
    dap_cN_bound (hwin N (by rw [mem_Icc]; omega)) (T.Ab _ (hwin N (by rw [mem_Icc]; omega))) hAmin
      (by simpa using (T.lip _ (hwin N (by rw [mem_Icc]; omega)) c0 ⟨by linarith, by linarith⟩).2.2) T.u0 hLu
      (hc N (by rw [mem_Icc]; omega)) hE6
  have hxi : 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) / δ ^ 3 ≤ airyXi (turnX u c0 q₀ δ N) :=
    dal_xi_large (by positivity) hδ hXN
  have hK0n : 0 ≤ K0 := hKA.le.trans (le_max_left _ _)
  have hmemJ : ∀ k ∈ Icc (J + 1) N, k ∈ Icc J (N + 1) := fun k hk => by
    rw [mem_Icc] at hk ⊢; omega
  have hδ1'' : δ ≤ δ1 := hδ1'
  have hδ2'' : δ ≤ δ2 := hδ2'
  have hdA : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPhi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := (HA δ q₀ hδ hδ1'' k (hwin k (hmemJ k hk))).1
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (airyWt_pos _).le)
  have hdB : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPsi (fun k => langerAmp u A c0 (dalQ q₀ δ k)) (turnX u c0 q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyBiWt (turnX u c0 q₀ δ k) := fun k hk => by
    have := HB δ q₀ hδ hδ2'' k (hwin k (hmemJ k hk))
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (airyBiWt_pos _).le)
  have hP : DaoPair (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) a c J N δ c1 c2 gmin gmax ca K M :=
    dao_pair_of_defects (a0 := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
      (c0 := fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) (by omega) hδ hδ11 hc1 (by linarith only [hc2δ]) hM0 hc2.le
      hgap hXabs hgmin (fun k hk => T.gb _ (hwin k hk)) hcap halow hK0n hE ha hc hdA hdB
  exact dai_extend hP hJN hJm hmN hc2.le hM0 haN' hcN hCdp hxi
    (dao_conclusion hP (mem_Icc.2 ⟨hJm, hmN⟩) hX0 hX1 hc2δ haN hsmall)

/-- info: 'FormalResearch.Special.kc_turn_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kc_turn_full

/-- **`discrete_airy_full` with the chart data**: `kc_turn_full` without the lower bound on `g`, the lattice gaps, the Lipschitz bound and `c₂ δ ≤ 1/8`
(`g ≤ g_max` on the window `[J, N+1]` and `X_k ≤ 1/4` for `k ≤ m+1` only). -/
theorem kc_turn {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0)
    (E : ℝ) (hE : 0 ≤ E) :
    ∃ (r δ0 C Cmu ξ0 gmax : ℝ), 0 < r ∧ r ≤ r0 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        (∀ k ∈ Finset.Icc J (N + 1), |langerAmp u A c0 (dalQ q₀ δ k)| ≤ gmax) ∧
        (∀ k ∈ Finset.Icc J (m + 1), turnX u c0 q₀ δ k ≤ 1 / 4) ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          DaiFull a c (turnX u c0 q₀ δ) (fun k => langerAmp u A c0 (dalQ q₀ δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, hr, hrr0, hδ0, hδ01, hC, hCmu, hξ0, hgmax, -, -, -, -, -, H⟩ :=
    kc_turn_full hu h1 h2 hA hA0 hr0 E hE
  refine ⟨r, δ0, C, Cmu, ξ0, gmax, hr, hrr0, hδ0, hδ01, hC, hCmu, hξ0, hgmax, fun δ q₀ hδ hδδ0 => ?_⟩
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, h3, h4, h5, h6, h7, h8, hg, hX, -, -, -, -, -, -, Hc⟩ := H δ q₀ hδ hδδ0
  exact ⟨J, m, N, hJN, hJm, hmN, hwin, h3, h4, h5, h6, h7, h8, hg, hX, Hc⟩

/-- info: 'FormalResearch.Special.kc_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kc_turn

/-- **`discrete_airy_hahn_racah_full` with the chart data** (`g ≤ g_max` on the window, `X_k ≤ 1/4` for `k ≤ m+1`). -/
theorem kc_hahn_full {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (r δ0 C Cmu ξ0 gmax : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmax ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3 ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        qs + r / 4 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + r / 2 ∧
        (∀ k ∈ Finset.Icc J (N + 1), |langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)| ≤ gmax) ∧
        (∀ k ∈ Finset.Icc J (m + 1), turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k ≤ 1 / 4) ∧
        DaiFull (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
          (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cmu, ξ0, gmax, hr, hrr0, hδ0', hδ01, hC, hCmu, hξ0, hgmax, H⟩ :=
    kc_turn (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) hr0 (hrE P Q a b qs)
      (hrE_nonneg P Q a b qs)
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cmu, ξ0, gmax, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCmu, hξ0, hgmax, ?_⟩
  intro δ hδ hδδ0
  have hδ1' : δ ≤ δ0' := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hg, hXm, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  refine ⟨J, m, N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJN, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    by rw [← e2]; exact hqN, by have := hqN1; rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by
      unfold dalQ; push_cast; ring]; exact this, hg, hXm, Hc _ _ hpa hpc⟩
  have h1 := hwin k hk
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- info: 'FormalResearch.Special.kc_hahn_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kc_hahn_full

end FormalResearch.Special

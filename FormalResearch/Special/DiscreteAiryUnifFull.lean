module

public import FormalResearch.Special.DiscreteAiryPhysTurn
public import FormalResearch.Special.DiscreteAiryUnifDefect
public import FormalResearch.Special.DiscreteAiryUnifLattice

/-!
# Uniform discrete-to-Airy, step 3: `discrete_airy_full` with constants depending only on window data

`discrete_airy_full` (`DiscreteAiryPhysTurn`) is proved by composing `dal_turn_data` (the window data `DalTurnWin` of a Langer chart),
the lattice window `dao_lattice`, and the two exact-coefficient defect lemmas.  All its constants are explicit expressions in
`(r, c₁, c₂, g_min, g_max, A_min, A_max, L_u, E)` and in the defect constant `K` and its range `δ₁`; only the *obtaining* of these
from one fixed datum was existential.  `discrete_airy_full_win` is the same theorem in hypothesis form:

For fixed reals `r, c₁, c₂, g_min, g_max, A_min, A_max, L_u, E` and jet bounds `Z₀ … g₂, δ_J` there are `δ₀, C, C_μ, ξ₀ > 0` such that
**for every** chart `(ζ, g)`, coefficient `A`, `u`, point `c₀` and open `U ⊇ [c₀ - r, c₀ + r]` with `ζ ∈ C³(U)`, `A, g ∈ C²(U)`, the
amplitude and eikonal relations `g²Aζ'Sh(ζζ'²) = 1`, `Ch(ζζ'²) = u` on `U`, the window data `DalTurnWin` and the jet bounds `DunJets` on the
window: for `δ ≤ δ₀` and every `q₀` the conclusion `DaiFull` of `discrete_airy_full` holds, for **all** `a, c` within `Eδ⁶` of the
exact coefficients.

**Claim class: proved.**  This is the quantitative form (U1, abstract level): uniformity over any family of charts with the same window
constants.  The window data and the jet bounds are *hypotheses* here; they are produced from a datum class in `DiscreteAiryUnifMain`.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **`discrete_airy_full` in hypothesis form: constants depend only on the window constants and jet bounds.** -/
theorem discrete_airy_full_win (r c1 c2 gmin gmax Amin Amax Lu E Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ : ℝ)
    (hr : 0 < r) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hgmin : 0 < gmin) (hgminmax : gmin ≤ gmax)
    (hAmin : 0 < Amin) (hAminmax : Amin ≤ Amax) (hLu : 0 ≤ Lu) (hE : 0 ≤ E)
    (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hδJ : 0 < δJ) :
    ∃ (δ0 C Cmu ξ0 : ℝ), 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ {ζ g A u : ℝ → ℝ} {c0 LA Lg : ℝ} {U : Set ℝ}, IsOpen U → Set.Icc (c0 - r) (c0 + r) ⊆ U →
        ContDiffOn ℝ 3 ζ U → ContDiffOn ℝ 2 A U → ContDiffOn ℝ 2 g U →
        (∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) →
        (∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) →
        DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu →
        DunJets ζ A g (Set.Icc (c0 - r) (c0 + r)) Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ →
        ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J < N ∧ J ≤ m ∧ m ≤ N ∧
          (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
          c0 - r ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J < c0 - r + δ ^ 3 ∧ c0 ≤ dalQ q₀ δ m ∧
          dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
          ∀ a c : ℤ → ℝ,
            (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
            (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
            DaiFull a c (dalX ζ q₀ δ) (fun k => g (dalQ q₀ δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨δL, hδL, hδL1, HL⟩ := dun_lattice r c1 c2 hr hc1 hc12
  obtain ⟨K0, δ1, hK0, hδ1, hδ11, HD⟩ := dun_exact_defect Z0 Z1 Z2 Z3 A0 A1 A2 g0 g1 g2 δJ hZ0 hZ1 hZ2 hZ3 hA0
    hA1 hA2 hg0 hg1 hg2 hδJ
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin hgminmax
  have hAmax : 0 < Amax := lt_of_lt_of_le hAmin hAminmax
  have hπ := Real.pi_pos
  set M : ℝ := c2 * r with hM
  have hM0 : 0 ≤ M := by positivity
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  set K : ℝ := K0 + E * (450 * gmax * (2 * Cn + 1)) with hK
  have hKnn : 0 ≤ K := by
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
  have hCdp : 0 < Cd := by rw [hCd]; positivity
  set Aa : ℝ := Amax + E with hAa
  set Cc : ℝ := 2 * Amax * (1 + Lu * r) + E with hCc
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hAa0 : 0 ≤ Aa := by rw [hAa]; positivity
  have hCn0 : 0 < Cn := by rw [hCn]; positivity
  set C : ℝ := Cd + Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca with hC
  have hCpos : 0 < C := by
    have : 0 ≤ Cn * (Cc * Cd + Aa * Cd * Cn + K) / ca := by positivity
    rw [hC]; linarith
  have hξ0 : 0 < 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) := by positivity
  refine ⟨min δL (min δ1 (min (1 / (8 * c2)) (min (1 / (4 * (Cl + 1))) (min (Amin / (2 * (E + 1))) (r / 8))))),
    C, Cmu, 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ), ?_, ?_, hCpos, by positivity, hξ0, ?_⟩
  · refine lt_min hδL (lt_min hδ1 (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  · exact (min_le_left _ _).trans hδL1
  intro ζ g A u c0 LA Lg U hU hsub hζ hAU hgU hrel heik T hjets δ q₀ hδ hδ0
  obtain ⟨hδL', hrest⟩ := le_min_iff.1 hδ0
  obtain ⟨hδ1', hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδc2, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδCl, hrest⟩ := le_min_iff.1 hrest
  obtain ⟨hδE, hδr⟩ := le_min_iff.1 hrest
  have hδ11 : δ ≤ 1 := hδL'.trans hδL1
  obtain ⟨J, m, N, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, hgap, hXabs, hX0, hX1, hXN⟩ :=
    HL T.zeta0 T.der δ q₀ hδ hδL'
  have hδ3r : δ ^ 3 ≤ r / 8 := (dap_cube_le hδ hδ11).trans hδr
  have hJN : J < N := dap_JN hδ hδ3r hqJ2 hqN
  refine ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ1, hqJ2, hqm1, hqm2, hqN, hqN1, ?_⟩
  intro a c ha hc
  have hc2δ : c2 * δ ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hδc2
    nlinarith only [hδc2]
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
  have hxi : 2 / 3 * (c1 * (r / 4)) ^ (3 / 2 : ℝ) / δ ^ 3 ≤ airyXi (dalX ζ q₀ δ N) :=
    dal_xi_large (by positivity) hδ hXN
  have hmemJ : ∀ k ∈ Icc (J + 1) N, k ∈ Icc J (N + 1) := fun k hk => by
    rw [mem_Icc] at hk ⊢; omega
  have hD := fun k hk => HD hU hsub hζ hAU hgU hrel heik hjets δ q₀ hδ hδ1' k (hwin k hk)
  have hdA : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPhi (fun k => g (dalQ q₀ δ k)) (dalX ζ q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyWt (dalX ζ q₀ δ k) := fun k hk => (hD k (hmemJ k hk)).1
  have hdB : ∀ k ∈ Icc (J + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (daoPsi (fun k => g (dalQ q₀ δ k)) (dalX ζ q₀ δ)) k| ≤
      K0 * δ ^ 6 * airyBiWt (dalX ζ q₀ δ k) := fun k hk => (hD k (hmemJ k hk)).2
  have hP : DaoPair (dalX ζ q₀ δ) (fun k => g (dalQ q₀ δ k)) a c J N δ c1 c2 gmin gmax ca K M :=
    dao_pair_of_defects (a0 := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
      (c0 := fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) (by omega) hδ hδ11 hc1 (by linarith only [hc2δ]) hM0 hc2.le
      hgap hXabs hgmin (fun k hk => T.gb _ (hwin k hk)) hcap halow hK0.le hE ha hc hdA hdB
  exact dai_extend hP hJN hJm hmN hc2.le hM0 haN' hcN hCdp hxi
    (dao_conclusion hP (mem_Icc.2 ⟨hJm, hmN⟩) hX0 hX1 hc2δ haN hsmall)

/-- info: 'FormalResearch.Special.discrete_airy_full_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_full_win

end FormalResearch.Special

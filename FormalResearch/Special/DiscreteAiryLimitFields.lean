module

public import FormalResearch.Special.DiscreteAiryLimitHyp

/-!
# Discrete-to-Airy limit, step 5: the fields of `AiryWindowHyp` for perturbed simple-turn coefficients

Part of the wiring module `DiscreteAiryLimit*`.  Each lemma verifies one field of `AiryWindowHyp` (the hypotheses of the
window theorems of M5/M6) for the lattice data `X = dalX ζ q₀ δ`, `ψ = dalPsi g ζ q₀ δ` and coefficient sequences
`a, c` with

`|a_k - A(q_k - h/2)| ≤ E h²` (`k ∈ [J+1, N+1]`),  `|c_k - 2A(q_k)u(q_k)| ≤ E h²` (`k ∈ [J+1, N]`),  `h = δ³`,

from the window data `DalTurnWin` of a simple turn and the window indices `DalLat` of `dal_lattice_window`:

`dal_f_lat`, `dal_f_cmp`, `dal_f_alow`, `dal_f_hyp` (near-hyperbolicity `Sg`), `dal_f_lipa` (`Qq`), `dal_f_defT`
(relative defect), `dal_f_defW` (absolute defect), `dal_f_psim`, `dal_f_junc`, `dal_f_low`.  They are composed in
`dal_window_hyp` (`DiscreteAiryLimitSetup`).  Proved; the constants are explicit.
-/

@[expose] public section

open FormalResearch.DiscreteAiry

namespace FormalResearch.Special

section Fields

variable {ζ g A u : ℝ → ℝ} {c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu : ℝ} {q₀ δ A0 : ℝ} {J m N : ℤ}

lemma dal_mid (hwin : ∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r))
    (hδ : 0 < δ) : ∀ k ∈ Finset.Icc (J + 1) (N + 1),
      dalQ q₀ δ k - δ ^ 3 / 2 ∈ Set.Icc (c0 - r) (c0 + r) := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  have h1 := hwin (k - 1) (by rw [Finset.mem_Icc]; omega)
  have h2 := hwin k (by rw [Finset.mem_Icc]; omega)
  have e : dalQ q₀ δ (k - 1) = dalQ q₀ δ k - δ ^ 3 := by unfold dalQ; push_cast; ring
  rw [e] at h1
  have : 0 < δ ^ 3 := by positivity
  exact ⟨by linarith [h1.1], by linarith [h2.2]⟩

lemma dal_f_lat (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    AiryLattice (dalX ζ q₀ δ) m N c1 (c2 * (r / 2)) δ := by
  have hc2 : 0 < c2 := lt_of_lt_of_le T.c1_pos T.c1_le
  refine ⟨T.c1_pos, by have := T.r_pos; positivity, hδ, hδ1, fun k hk => ?_, fun k hk => ?_,
    fun k hk => L.XB k hk⟩
  · have := L.X0 k hk; linarith
  · rw [Finset.mem_Icc] at hk
    exact (L.gap k (by rw [Finset.mem_Icc]; have := L.J_le; omega)).1

lemma dal_f_cmp (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) :
    AiryComparison (dalPsi g ζ q₀ δ) (dalX ζ q₀ δ) m N (gmin / 20) (6 * gmax) := by
  have hgmin := T.gmin_pos
  have hJm := L.J_le
  have hkk : ∀ k ∈ Finset.Icc m (N + 1), (gmin / 20 * airyWt (dalX ζ q₀ δ k) ≤ dalPsi g ζ q₀ δ k ∧
      dalPsi g ζ q₀ δ k ≤ 6 * gmax * airyWt (dalX ζ q₀ δ k)) := by
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    have hw := L.win k (by rw [Finset.mem_Icc]; omega)
    have hg := T.gb _ hw
    exact dal_psi_cmp hg.1 hg.2 hgmin (by have := L.X0 k hk; linarith)
  exact ⟨by positivity, by linarith [T.gmin_le], fun k hk => (hkk k hk).1, fun k hk => (hkk k hk).2⟩

lemma dal_f_alow (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) {a : ℤ → ℝ} {E : ℝ}
    (ha : ∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6)
    (hE : E * δ ^ 6 ≤ Amin / 2) : ∀ k ∈ Finset.Icc (J + 1) (N + 1), Amin / 2 ≤ a k := by
  intro k hk
  have h1 := ha k hk
  have h2 := (T.Ab _ (dal_mid L.win hδ k hk)).1
  rw [abs_le] at h1
  linarith [h1.1]

/-- Real-variable core of the near-hyperbolicity estimate. -/
lemma dal_hyp_real {ck ak ak1 Aq Ax1 Ax2 uq E6 LAh Z Amax : ℝ} (h1 : |ck - 2 * Aq * uq| ≤ E6)
    (h2 : |ak - Ax1| ≤ E6) (h3 : |ak1 - Ax2| ≤ E6) (h4 : |Aq - Ax1| ≤ LAh) (h5 : |Aq - Ax2| ≤ LAh)
    (h6 : |uq - 1| ≤ Z) (hA0 : 0 ≤ Aq) (hA : Aq ≤ Amax) :
    |ck - ak - ak1| ≤ 3 * E6 + 2 * (Amax * Z) + 2 * LAh := by
  have hprod : |Aq * (uq - 1)| ≤ Amax * Z := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul hA h6 (abs_nonneg _) (hA0.trans hA)
  rw [abs_le] at *
  obtain ⟨a1, a2⟩ := h1; obtain ⟨b1, b2⟩ := h2; obtain ⟨c1, c2⟩ := h3
  obtain ⟨d1, d2⟩ := h4; obtain ⟨e1, e2⟩ := h5; obtain ⟨f1, f2⟩ := hprod
  have e : 2 * Aq * uq = 2 * (Aq * (uq - 1)) + 2 * Aq := by ring
  constructor <;> nlinarith

lemma dal_f_hyp (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a c : ℤ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6)
    (hc : ∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) :
    ∀ k ∈ Finset.Ioc J m, |c k - a k - a (k + 1)| ≤
      (2 * Amax * Lu * (A0 / c2 + 1) + LA + 3 * E) * δ ^ 2 := by
  have hc2 : 0 < c2 := lt_of_lt_of_le T.c1_pos T.c1_le
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
  have h6δ : δ ^ 6 ≤ δ ^ 2 := by
    have : δ ^ 6 = δ ^ 2 * δ ^ 4 := by ring
    rw [this]
    nlinarith [pow_pos hδ 2, pow_le_one₀ hδ.le hδ1 (n := 4)]
  intro k hk
  have hk' := Finset.mem_Ioc.1 hk
  have hJm := L.J_le
  have hmN := L.m_le
  have hk1 : k ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
  have hk2 : k + 1 ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
  have hkc : k ∈ Finset.Icc (J + 1) N := by rw [Finset.mem_Icc]; omega
  have hqk := L.win k (by rw [Finset.mem_Icc]; omega)
  have e2 : dalQ q₀ δ (k + 1) - δ ^ 3 / 2 = dalQ q₀ δ k + δ ^ 3 / 2 := by unfold dalQ; push_cast; ring
  have l1 := (T.lip _ hqk _ (dal_mid L.win hδ k hk1)).1
  have l2 := (T.lip _ hqk _ (dal_mid L.win hδ (k + 1) hk2)).1
  have e3 : |dalQ q₀ δ k - (dalQ q₀ δ k - δ ^ 3 / 2)| = δ ^ 3 / 2 := by
    rw [show dalQ q₀ δ k - (dalQ q₀ δ k - δ ^ 3 / 2) = δ ^ 3 / 2 by ring, abs_of_pos (by positivity)]
  have e4 : |dalQ q₀ δ k - (dalQ q₀ δ (k + 1) - δ ^ 3 / 2)| = δ ^ 3 / 2 := by
    rw [e2, show dalQ q₀ δ k - (dalQ q₀ δ k + δ ^ 3 / 2) = -(δ ^ 3 / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  rw [e3] at l1
  rw [e4] at l2
  have hr0 := T.r_pos
  have hu1 := (T.lip _ hqk c0 ⟨by linarith, by linarith⟩).2.2
  rw [T.u0] at hu1
  have hdk := L.dist k (by rw [Finset.mem_Icc]; omega)
  have hu2 : |u (dalQ q₀ δ k) - 1| ≤ Lu * ((A0 / c2 + 1) * δ ^ 2) :=
    hu1.trans (mul_le_mul_of_nonneg_left hdk T.Lu_nonneg)
  have key := dal_hyp_real (hc k hkc) (ha k hk1) (ha (k + 1) hk2) l1 l2 hu2 (lt_of_lt_of_le T.Amin_pos (T.Ab _ hqk).1).le (T.Ab _ hqk).2
  have t1 : E * δ ^ 6 ≤ E * δ ^ 2 := mul_le_mul_of_nonneg_left h6δ hE
  have t2 : LA * δ ^ 3 ≤ LA * δ ^ 2 := mul_le_mul_of_nonneg_left h3δ T.LA_nonneg
  refine key.trans ?_
  nlinarith [t1, t2]

lemma dal_f_lipa (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a : ℤ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) :
    ∀ k ∈ Finset.Ioc J m, |a (k + 1) - a k| ≤ (LA + 2 * E) * δ ^ 2 := by
  have h3 : 0 < δ ^ 3 := by positivity
  have h3δ : δ ^ 3 ≤ δ ^ 2 := by nlinarith [pow_pos hδ 2]
  have h6δ : δ ^ 6 ≤ δ ^ 2 := by
    have : δ ^ 6 = δ ^ 2 * δ ^ 4 := by ring
    rw [this]
    nlinarith [pow_pos hδ 2, pow_le_one₀ hδ.le hδ1 (n := 4)]
  intro k hk
  have hk' := Finset.mem_Ioc.1 hk
  have hJm := L.J_le
  have hmN := L.m_le
  have hk1 : k ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
  have hk2 : k + 1 ∈ Finset.Icc (J + 1) (N + 1) := by rw [Finset.mem_Icc]; omega
  have e2 : dalQ q₀ δ (k + 1) - δ ^ 3 / 2 = dalQ q₀ δ k + δ ^ 3 / 2 := by unfold dalQ; push_cast; ring
  have l := (T.lip _ (dal_mid L.win hδ (k + 1) hk2) _ (dal_mid L.win hδ k hk1)).1
  have e3 : |dalQ q₀ δ (k + 1) - δ ^ 3 / 2 - (dalQ q₀ δ k - δ ^ 3 / 2)| = δ ^ 3 := by
    rw [e2, show dalQ q₀ δ k + δ ^ 3 / 2 - (dalQ q₀ δ k - δ ^ 3 / 2) = δ ^ 3 by ring, abs_of_pos h3]
  rw [e3] at l
  have p1 := abs_le.1 (ha k hk1)
  have p2 := abs_le.1 (ha (k + 1) hk2)
  have l' := abs_le.1 l
  have t1 : E * δ ^ 6 ≤ E * δ ^ 2 := mul_le_mul_of_nonneg_left h6δ hE
  have t2 : LA * δ ^ 3 ≤ LA * δ ^ 2 := mul_le_mul_of_nonneg_left h3δ T.LA_nonneg
  rw [abs_le]
  constructor <;> nlinarith [t1, t2]

lemma dal_f_psim (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) {k : ℤ} (hk : k ∈ Finset.Icc J (N + 1)) :
    |dalPsi g ζ q₀ δ k| ≤ 25 * gmax :=
  dal_psi_abs_le (lt_of_lt_of_le T.gmin_pos (T.gb _ (L.win k hk)).1).le (T.gb _ (L.win k hk)).2

lemma dal_f_low (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hc2δ : c2 * δ ≤ 1 / 2) :
    gmin / 20 * (2 / 9) ≤ dalPsi g ζ q₀ δ m := by
  have hmm : m ∈ Finset.Icc m (N + 1) := by rw [Finset.mem_Icc]; have := L.m_le; omega
  have h1 := (dal_f_cmp T L).lower m hmm
  have h2 := dal_airyWt_ge (L.X0 m hmm) (by linarith [L.Xm])
  have := mul_le_mul_of_nonneg_left h2 (by have := T.gmin_pos; positivity : (0 : ℝ) ≤ gmin / 20)
  linarith

lemma dal_f_junc (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc2δ : c2 * δ ≤ 1 / 2) :
    |dalPsi g ζ q₀ δ m - dalPsi g ζ q₀ δ (m + 1)| ≤ (25 * Lg + 265000 * gmax * c2) * δ := by
  have hJm := L.J_le
  have hmN := L.m_le
  have h3 : 0 < δ ^ 3 := by positivity
  have hmem : m ∈ Finset.Icc J N := by rw [Finset.mem_Icc]; omega
  have hgap := L.gap m hmem
  have hX0 := L.X0 m (by rw [Finset.mem_Icc]; omega)
  have hg1 := T.gb _ (L.win (m + 1) (by rw [Finset.mem_Icc]; omega))
  have hq1 := L.win m (by rw [Finset.mem_Icc]; omega)
  have hq2 := L.win (m + 1) (by rw [Finset.mem_Icc]; omega)
  have lg := (T.lip _ hq1 _ hq2).2.1
  have e3 : |dalQ q₀ δ m - dalQ q₀ δ (m + 1)| = δ ^ 3 := by
    rw [show dalQ q₀ δ m - dalQ q₀ δ (m + 1) = -(δ ^ 3) by unfold dalQ; push_cast; ring, abs_neg,
      abs_of_pos h3]
  rw [e3] at lg
  have hc1p := T.c1_pos
  have hc2p : 0 < c2 := lt_of_lt_of_le hc1p T.c1_le
  have s1 : 0 ≤ dalX ζ q₀ δ (m + 1) - dalX ζ q₀ δ m := by nlinarith [hgap.1]
  exact dal_junction (g := g (dalQ q₀ δ m)) (g' := g (dalQ q₀ δ (m + 1))) (X := dalX ζ q₀ δ m)
    (X' := dalX ζ q₀ δ (m + 1)) hδ hδ1 (lt_of_lt_of_le T.gmin_pos hg1.1).le hg1.2 T.Lg_nonneg
    ⟨hX0, by linarith [L.Xm]⟩ ⟨by linarith, by linarith [hgap.2, L.Xm]⟩
    (by rw [abs_of_nonneg s1]; exact hgap.2) lg

/-- Relative defect on the top window, for perturbed coefficients. -/
lemma dal_f_defT (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc2δ : c2 * δ ≤ 1 / 2)
    {a c : ℤ → ℝ} {E K' : ℝ} (hE : 0 ≤ E)
    (ha : ∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6)
    (hc : ∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6)
    (hex : ∀ k ∈ Finset.Icc J (N + 1), -1 ≤ dalX ζ q₀ δ k →
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (dalPsi g ζ q₀ δ) k| ≤ K' * δ ^ 6 * |dalPsi g ζ q₀ δ k|) :
    ∀ i ∈ Finset.Icc (m + 1) N, |jac a c (dalPsi g ζ q₀ δ) i| ≤
      (K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20))) *
        δ ^ 6 * dalPsi g ζ q₀ δ i := by
  have hc2 : 0 < c2 := lt_of_lt_of_le T.c1_pos T.c1_le
  have hJm := L.J_le
  have hmN := L.m_le
  have hcmp := dal_f_cmp T L
  have hB0 : 0 ≤ c2 * (r / 2) := by have := T.r_pos; positivity
  have hpa : ∀ i ∈ Finset.Icc (m + 1) N,
      |a (i + 1) - (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (i + 1)| ≤ E * δ ^ 6 ∧
      |a i - (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) i| ≤ E * δ ^ 6 ∧
      |c i - (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) i| ≤ E * δ ^ 6 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact ⟨ha (i + 1) (by rw [Finset.mem_Icc]; omega), ha i (by rw [Finset.mem_Icc]; omega),
      hc i (by rw [Finset.mem_Icc]; omega)⟩
  have hex' : ∀ i ∈ Finset.Icc (m + 1) N,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (dalPsi g ζ q₀ δ) i| ≤ K' * δ ^ 6 * dalPsi g ζ q₀ δ i := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have hmi : i ∈ Finset.Icc m (N + 1) := by rw [Finset.mem_Icc]; omega
    have := hex i (by rw [Finset.mem_Icc]; omega) (by have := L.X0 i hmi; linarith)
    rwa [abs_of_pos (hcmp.pos hmi)] at this
  have hnbr : ∀ i ∈ Finset.Icc (m + 1) N,
      airyWt (dalX ζ q₀ δ (i + 1)) ≤ 6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2))) * airyWt (dalX ζ q₀ δ i) ∧
      airyWt (dalX ζ q₀ δ (i - 1)) ≤ 6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2))) * airyWt (dalX ζ q₀ δ i) := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    have hmi : i ∈ Finset.Icc m (N + 1) := by rw [Finset.mem_Icc]; omega
    have hXi : |dalX ζ q₀ δ i| ≤ c2 * (r / 2) / δ ^ 2 := by
      rw [abs_of_nonneg (L.X0 i hmi)]; exact L.XB i hmi
    have s1 := L.gap i (by rw [Finset.mem_Icc]; omega)
    have s2 := L.gap (i - 1) (by rw [Finset.mem_Icc]; omega)
    rw [sub_add_cancel] at s2
    have p1 : 0 ≤ dalX ζ q₀ δ (i + 1) - dalX ζ q₀ δ i := by nlinarith [s1.1, T.c1_pos]
    have p2 : 0 ≤ dalX ζ q₀ δ i - dalX ζ q₀ δ (i - 1) := by nlinarith [s2.1, T.c1_pos]
    constructor
    · refine dal_airyWt_nbr hδ hδ1 hc2.le (by linarith) hXi hB0 ?_
      rw [abs_of_nonneg p1]; exact s1.2
    · refine dal_airyWt_nbr hδ hδ1 hc2.le (by linarith) hXi hB0 ?_
      rw [abs_sub_comm, abs_of_nonneg p2]; exact s2.2
  have key := dal_defT_abs (a := a) (c := c) (a' := fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
    (c' := fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) hE hex' hpa hcmp hnbr (by positivity)
  exact key

/-- Absolute defect on the oscillatory window, for perturbed coefficients. -/
lemma dal_f_defW (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (L : DalLat ζ q₀ δ c0 r c1 c2 A0 J m N) {a c : ℤ → ℝ} {E K : ℝ} (hE : 0 ≤ E)
    (ha : ∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6)
    (hc : ∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6)
    (hex : ∀ k ∈ Finset.Icc J (N + 1),
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (dalPsi g ζ q₀ δ) k| ≤ K * δ ^ 6 * airyWt (dalX ζ q₀ δ k)) :
    ∀ i ∈ Finset.Ioc J m, |jac a c (dalPsi g ζ q₀ δ) i| ≤ (K / (25 * gmax) + 3 * E) * δ ^ 6 * (25 * gmax) := by
  have hJm := L.J_le
  have hmN := L.m_le
  have hgmax : 0 < gmax := lt_of_lt_of_le T.gmin_pos T.gmin_le
  have hpa : ∀ i ∈ Finset.Ioc J m,
      |a (i + 1) - (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (i + 1)| ≤ E * δ ^ 6 ∧
      |a i - (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) i| ≤ E * δ ^ 6 ∧
      |c i - (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) i| ≤ E * δ ^ 6 := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    exact ⟨ha (i + 1) (by rw [Finset.mem_Icc]; omega), ha i (by rw [Finset.mem_Icc]; omega),
      hc i (by rw [Finset.mem_Icc]; omega)⟩
  have hex' : ∀ i ∈ Finset.Ioc J m,
      |jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2)) (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j))
        (dalPsi g ζ q₀ δ) i| ≤ K * δ ^ 6 := by
    intro i hi
    have hi' := Finset.mem_Ioc.1 hi
    have := hex i (by rw [Finset.mem_Icc]; omega)
    refine this.trans ?_
    have h1 := airyWt_le_one (dalX ζ q₀ δ i)
    have h0 := abs_nonneg (jac (fun j => A (dalQ q₀ δ j - δ ^ 3 / 2))
      (fun j => 2 * A (dalQ q₀ δ j) * u (dalQ q₀ δ j)) (dalPsi g ζ q₀ δ) i)
    have h2 := airyWt_pos (dalX ζ q₀ δ i)
    have hK : 0 ≤ K * δ ^ 6 := (mul_nonneg_iff_of_pos_right h2).1 (h0.trans this)
    nlinarith
  exact dal_defW_abs hE (by positivity) hex' hpa (fun i hi => by
    have hi' := Finset.mem_Ioc.1 hi
    exact ⟨dal_f_psim T L (k := i + 1) (by rw [Finset.mem_Icc]; omega),
      dal_f_psim T L (k := i - 1) (by rw [Finset.mem_Icc]; omega),
      dal_f_psim T L (k := i) (by rw [Finset.mem_Icc]; omega)⟩)

end Fields

end FormalResearch.Special

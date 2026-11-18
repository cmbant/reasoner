module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkConj1

/-!
# Paper J, Theorem B, L3.1 bulk, input (iii): positive bonds for small steps and the window lower bounds

Source: Paper J `app_thmA.tex`, "The bulk: proof of Proposition prop:tha-W", Step 2 (overlap sums, `cas_lb`, `M_osc`, `W_osc`),
and `app_thmB.tex`, proof of `prop:tha-splice` (`eq:tha-spl2`).

## Proved here

* `bondA_pos_small`: for compact `P`, `(E_K)` and `(H1)--(H3)` on `P`, there is `h0 > 0` such that every bond `a_n`, `0 <= n < N`,
  is positive when `h = L/(N+1) <= h0` and `mu in P`.  Proof: `|G_h - G_0| <= D h^2` on `[0,L]` from the remainder of `EK` and the
  bound on the even jets on the compact `P x [0,L]`; `G_0 >= g_*` from `Hyp`.

## Not formalised here

* The window lower bound of `bulk_conj1` (`hΩℓ`, `hΩr`) for a general chart, and the mirror transport of the window, are in the
  following sections (added in later commits of this file).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

/-- **Positive bonds for small steps** (`(E_K)` and `(H1)`): uniformly in `mu in P`, `|G_h - G_0| <= D h^2` on `[0,L]` for `h <= 1`,
hence `G_h >= g_*/2 > 0` for `h` small, and every bond `a_n = bondA mu N n` with `0 <= n < N` is positive. -/
theorem bondA_pos_small {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (P : Set Par) (Kidx r : ℕ)
    (hP : IsCompact P) (hEK : EK F P Kidx r) (hH : HypOn F P) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ h0 → ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n := by
  -- the even jets are bounded on P x [0, L]
  have hjet : ∀ j ∈ range (Kidx + 1), ∃ B : ℝ, ∀ μ ∈ P, ∀ s ∈ Icc 0 F.L, |F.G (2 * j) μ s| ≤ B := by
    intro j hj
    have hjK : j ≤ Kidx := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨-, hcont⟩ := (hEK.reg j hjK).1
    have hc : ContinuousOn (fun p : Par × ℝ => F.G (2 * j) p.1 p.2) (P ×ˢ Icc 0 F.L) := by
      simpa [iteratedDerivWithin_zero] using hcont 0 (Nat.zero_le _)
    obtain ⟨B, hB⟩ := (hP.prod isCompact_Icc).exists_bound_of_continuousOn hc
    exact ⟨B, fun μ hμ s hs => hB (μ, s) ⟨hμ, hs⟩⟩
  choose! B hB using hjet
  obtain ⟨C, hC⟩ := hEK.rem
  set Dc : ℝ := |C| + ∑ j ∈ range Kidx, |B (j + 1)| with hDc
  have hDc0 : 0 ≤ Dc := by
    rw [hDc]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  -- |G_h - G_0| <= Dc h^2 on [0, L] for h <= 1
  have hdiff : ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ 1 → ∀ s ∈ Icc 0 F.L,
      |F.Gh μ (F.step N) s - F.G 0 μ s| ≤ Dc * F.step N ^ 2 := by
    intro μ hμ N hh1 s hs
    have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hst0 := hst.le
    obtain ⟨hC1, -⟩ := hC μ hμ N s hs
    have hsum : ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s =
        F.G 0 μ s + ∑ j ∈ range Kidx, F.step N ^ (2 * (j + 1)) * F.G (2 * (j + 1)) μ s := by
      rw [Finset.sum_range_succ']
      simp only [mul_zero, pow_zero, one_mul]
      ring
    have hrest : |∑ j ∈ range Kidx, F.step N ^ (2 * (j + 1)) * F.G (2 * (j + 1)) μ s| ≤
        (∑ j ∈ range Kidx, |B (j + 1)|) * F.step N ^ 2 := by
      rw [Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hj' : j < Kidx := Finset.mem_range.mp hj
      have hBj : |F.G (2 * (j + 1)) μ s| ≤ |B (j + 1)| :=
        (hB (j + 1) (Finset.mem_range.mpr (by omega)) μ hμ s hs).trans (le_abs_self _)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hst0 _)]
      have hpow : F.step N ^ (2 * (j + 1)) ≤ F.step N ^ 2 :=
        pow_le_pow_of_le_one hst0 hh1 (by omega)
      exact (mul_le_mul hpow hBj (abs_nonneg _) (sq_nonneg _)).trans (le_of_eq (mul_comm _ _))
    have hpowC : |F.step N ^ (2 * Kidx + 2)| ≤ F.step N ^ 2 := by
      rw [abs_of_nonneg (pow_nonneg hst0 _)]
      exact pow_le_pow_of_le_one hst0 hh1 (by omega)
    have hCp : C * F.step N ^ (2 * Kidx + 2) ≤ |C| * F.step N ^ 2 :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hpowC (abs_nonneg _))
    have hsplit : F.Gh μ (F.step N) s - F.G 0 μ s =
        (F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s) +
        ∑ j ∈ range Kidx, F.step N ^ (2 * (j + 1)) * F.G (2 * (j + 1)) μ s := by
      rw [hsum]; ring
    have hfin : |F.Gh μ (F.step N) s - F.G 0 μ s| ≤
        |F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s| +
        |∑ j ∈ range Kidx, F.step N ^ (2 * (j + 1)) * F.G (2 * (j + 1)) μ s| := by
      rw [hsplit]; exact abs_add_le _ _
    have hDeq : Dc * F.step N ^ 2 = |C| * F.step N ^ 2 + (∑ j ∈ range Kidx, |B (j + 1)|) * F.step N ^ 2 := by
      rw [hDc]; ring
    have hA : |F.Gh μ (F.step N) s - ∑ j ∈ range (Kidx + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s| ≤
        C * F.step N ^ (2 * Kidx + 2) := hC1
    linarith [hfin, hA, hCp, hrest, hDeq]
  -- the positive lower bound and the bonds
  rcases P.eq_empty_or_nonempty with hPe | ⟨μ0, hμ0⟩
  · exact ⟨1, one_pos, fun μ hμ => by simp [hPe] at hμ⟩
  obtain ⟨g, hg⟩ := hH
  have hgpos : 0 < g := (hg μ0 hμ0).gstar_pos
  have hden : 0 < 2 * (Dc + 1) := by positivity
  refine ⟨min 1 (Real.sqrt (g / (2 * (Dc + 1)))), lt_min one_pos (Real.sqrt_pos.mpr (div_pos hgpos hden)), ?_⟩
  intro μ hμ N hN n hn0 hnN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hh1 : F.step N ≤ 1 := hN.trans (min_le_left _ _)
  have hsq : F.step N ^ 2 ≤ g / (2 * (Dc + 1)) := by
    have h1 := pow_le_pow_left₀ hst.le (hN.trans (min_le_right _ _)) 2
    rw [Real.sq_sqrt (div_pos hgpos hden).le] at h1
    exact h1
  have hgap : Dc * F.step N ^ 2 ≤ g / 2 := by
    have h2 : (Dc + 1) * F.step N ^ 2 ≤ g / 2 := by
      have : (Dc + 1) * F.step N ^ 2 ≤ (Dc + 1) * (g / (2 * (Dc + 1))) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have e : (Dc + 1) * (g / (2 * (Dc + 1))) = g / 2 := by field_simp
      linarith
    nlinarith [sq_nonneg (F.step N), hDc0]
  have hstL : F.step N * ((N : ℝ) + 1) = F.L := FormalResearch.JacobiEigenvectors.TheoremA.step_mul_succ F N
  have hG : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.Gh μ (F.step N) (sNode (F.step N) n) := by
    intro n hn0' hnN'
    have hs0 : 0 < sNode (F.step N) n := by
      unfold sNode
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0'
      positivity
    have hsL : sNode (F.step N) n ≤ F.L := by
      unfold sNode
      have hnN2 : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hnN'
      have : ((n : ℝ) + 1) * F.step N ≤ ((N : ℝ) + 1) * F.step N :=
        mul_le_mul_of_nonneg_right (by linarith) hst.le
      linarith
    have hmem : sNode (F.step N) n ∈ Icc 0 F.L := ⟨hs0.le, hsL⟩
    have hd := hdiff μ hμ N hh1 _ hmem
    have hG0 := (hg μ hμ).G0_lb _ hmem
    obtain ⟨h3, -⟩ := abs_le.mp hd
    linarith
  exact bondA_pos F μ N hG n hn0 hnN

/-- The window constant of one bulk chart: `c_Omega = (c - c') c_m^2 / (8 K_3^2)`, with `K_3 = (CA+1) K_g (CM+1)`, `K_g = K_A+K_B+...`. -/
def windowConst {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {Jlo Jhi : ℝ}
    {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (CA : ℝ) : ℝ :=
  (C.c - C.c') * C.cs.cm ^ 2 / (8 * ((CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1)) ^ 2)

/-- **Window lower bound of one bulk chart** (`bulk_conj1`, `hΩℓ`, re-derived for a general chart): if the bonds are bounded by `CA`
and the step is small, then `c_Omega / sqrt h <= sum_{Omega} (psihat^L_n)^2` over the overlap window `Omega = bulkWindow C N`. -/
theorem window_sum_lower {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (CA : ℝ) (hCA0 : 0 ≤ CA)
    (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N)
    (hhd : G.step N ≤ (C.c - C.c') / 6) (hhσ : G.step N ≤ C.σ)
    (hA : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CA) :
    windowConst C CA / Real.sqrt (G.step N) ≤ ∑ n ∈ bulkWindow C N, (C.psiHatL p X N n) ^ 2 := by
  obtain ⟨hc'L, hcc'L, -, hcσL, -, hcM, hcMCM, -, hCsumL, -⟩ := C.consts_pos
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hLs : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  have hD0 : 0 < C.c - C.c' := by linarith
  have hhc : G.step N ≤ C.c - C.c' := by linarith [hhd]
  have hcL : C.c + G.step N ≤ G.L := by linarith
  -- chart facts with the constants of `windowConst`
  have hKg0 : 0 < (C.cs.KA + C.cs.KB) * C.cs.Kw + 1 := by
    have := mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
    linarith
  have hCEg0 : 0 < |C.cs.CE| + 1 := by linarith [abs_nonneg C.cs.CE]
  have hCMg0 : 0 < C.CM + 1 := by linarith
  have hCAg0 : 0 < CA + 1 := by linarith
  have hCsg0 : 0 < C.Csum + 1 := by linarith
  have hA' : ∀ j : ℤ, 0 ≤ j → j ≤ (C.chain p X N).NR - 1 → |(C.chain p X N).A j| ≤ CA + 1 :=
    fun j h1 h2 => (hA j h1 h2).trans (by linarith)
  obtain ⟨-, -, -, -, hpair⟩ := chart_side_facts C p hp X hX N hN hhc ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1)
    (|C.cs.CE| + 1) (C.CM + 1) C.cs.cm (C.Csum + 1) (CA + 1) hKg0 hCEg0 hCMg0 C.cs.cm_pos hCAg0
    (by linarith) (by linarith [le_abs_self C.cs.CE]) (by linarith) le_rfl (by linarith) hA'
  set K3 : ℝ := (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) with hK3
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  set q : ℝ := G.step N ^ ((1 : ℝ) / 4) with hq
  obtain ⟨hq2, hq0⟩ := fourth_root_sq (G.step N) hst
  rw [← hq] at hq2
  set c1 : ℝ := C.cs.cm * q / K3 with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; exact div_nonneg (mul_nonneg C.cs.cm_pos.le hq0.le) hK3pos.le
  -- the pairs of the overlap
  obtain ⟨S, hSprop, hScard⟩ := count_pairs (G.step N) G.L C.c' C.c N hst hLs hc'L hcc'L hcL
  have hPpair : ∀ n ∈ S, c1 ≤ |C.psiHatL p X N n| + |C.psiHatL p X N (n + 1)| := by
    intro n hn
    obtain ⟨hn0, hn1, hc1', hc2'⟩ := hSprop n hn
    have hk := hpair n hn0 (le_NR_of C p hp X hX N hN hst (n + 1) hc2') hc1' hc2'
    rw [hc1, div_le_iff₀ hK3pos]
    have e : K3 = (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) := hK3
    rw [e]
    linarith [hk]
  have hmem : ∀ n : ℤ, n ∈ bulkWindow C N ↔ (n ∈ rowsOf N ∧ C.c' ≤ uNode (G.step N) n ∧ uNode (G.step N) n ≤ C.c) := by
    intro n
    unfold bulkWindow
    exact Finset.mem_filter
  have hS : ∀ n ∈ S, n ∈ bulkWindow C N ∧ n + 1 ∈ bulkWindow C N := by
    intro n hn
    obtain ⟨hn0, hn1, hc1', hc2'⟩ := hSprop n hn
    have hle : uNode (G.step N) n ≤ uNode (G.step N) (n + 1) := uNode_le_of_le hst.le (by omega)
    refine ⟨(hmem n).mpr ⟨?_, hc1', by linarith⟩, (hmem (n + 1)).mpr ⟨?_, by linarith, hc2'⟩⟩
    · unfold rowsOf; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · unfold rowsOf; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hov := overlap_sum_lower (fun n => C.psiHatL p X N n) (bulkWindow C N) S c1 hc10 hS hPpair
  have hov' : (S.card : ℝ) * c1 ^ 2 ≤ 4 * ∑ n ∈ bulkWindow C N, C.psiHatL p X N n ^ 2 := hov
  -- the cardinality of the pairs
  have h6 : 6 ≤ (C.c - C.c') / G.step N := by
    rw [le_div_iff₀ hst]; linarith [hhd]
  have hSmall : (C.c - C.c') / (2 * G.step N) ≤ (S.card : ℝ) := by
    have e : (C.c - C.c') / (2 * G.step N) = ((C.c - C.c') / G.step N) / 2 := by rw [div_div, mul_comm]
    rw [e]; linarith
  have hk1 : (C.c - C.c') / (2 * G.step N) * c1 ^ 2 ≤ (S.card : ℝ) * c1 ^ 2 :=
    mul_le_mul_of_nonneg_right hSmall (sq_nonneg _)
  -- the algebra: c1^2 = cm^2 sqrt h / K3^2 and windowConst / sqrt h = (c - c') / (2 h) * c1^2 / 4
  have hsq : Real.sqrt (G.step N) ^ 2 = G.step N := Real.sq_sqrt hst.le
  have hs0 : 0 < Real.sqrt (G.step N) := Real.sqrt_pos.mpr hst
  have hc1sq : c1 ^ 2 = C.cs.cm ^ 2 * Real.sqrt (G.step N) / K3 ^ 2 := by
    rw [hc1, div_pow, mul_pow, hq2]
  have hw : windowConst C CA = (C.c - C.c') * C.cs.cm ^ 2 / (8 * K3 ^ 2) := rfl
  have heq : windowConst C CA / Real.sqrt (G.step N) =
      (C.c - C.c') / (2 * G.step N) * c1 ^ 2 / 4 := by
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (G.step N) := ⟨_, rfl⟩
    have hG : G.step N = s ^ 2 := by rw [hs, Real.sq_sqrt hst.le]
    have hs0' : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hst
    rw [hc1sq, hw, ← hs, hG]
    field_simp
    ring
  rw [heq]
  linarith [hk1, hov']

/-- **Mirror reindexing of a window sum**: with the overlap of the right chart the mirror of the left one (`hcoup`), the right
window sum of `CR.psiHatL` over the left window `n |-> N - n` is the window sum of `CR` over its own window. -/
theorem window_mirror_sum {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (p : Par × ℝ) (X : ℝ) (N : ℕ)
    (hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L) :
    ∑ n ∈ bulkWindow CL N, (CR.psiHatL p X N ((N : ℤ) - n)) ^ 2 = ∑ j ∈ bulkWindow CR N, (CR.psiHatL p X N j) ^ 2 := by
  have hms : (mirrorFamily Fz).step N = Fz.step N := rfl
  have hmemR : ∀ n : ℤ, n ∈ rowsOf N ↔ 0 ≤ n ∧ n ≤ (N : ℤ) := fun n => by unfold rowsOf; exact Finset.mem_Icc
  refine Finset.sum_nbij' (fun n : ℤ => (N : ℤ) - n) (fun j : ℤ => (N : ℤ) - j) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    unfold bulkWindow at hn ⊢
    rw [Finset.mem_filter] at hn ⊢
    obtain ⟨hr, h1, h2⟩ := hn
    rw [hmemR] at hr
    rw [hms, uNode_mirror Fz.L (Fz.step N) N n hLs] at *
    refine ⟨(hmemR _).mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · linarith [hcoup.1, hcoup.2]
    · linarith [hcoup.1, hcoup.2]
  · intro j hj
    unfold bulkWindow at hj ⊢
    rw [Finset.mem_filter] at hj ⊢
    obtain ⟨hr, h1, h2⟩ := hj
    rw [hmemR] at hr
    rw [hms] at h1 h2
    refine ⟨(hmemR _).mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · rw [uNode_mirror Fz.L (Fz.step N) N j hLs]
      linarith [hcoup.1, hcoup.2]
    · rw [uNode_mirror Fz.L (Fz.step N) N j hLs]
      linarith [hcoup.1, hcoup.2]
  · intro n _; ring
  · intro j _; ring
  · intro n _; rfl

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bondA_pos_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bondA_pos_small

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.window_sum_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.window_sum_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.window_mirror_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.window_mirror_sum

end FormalResearch.JacobiEigenvectors.TheoremB

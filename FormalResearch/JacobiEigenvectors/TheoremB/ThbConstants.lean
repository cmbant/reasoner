module

public import Mathlib
public import FormalResearch.JB.JBOneStepDef

/-!
# Paper J, Theorem B, L3.5c (assembly of `PropThbInputs`), part 2: uniform constants over the finitely many blocks

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs` ("the constants are the maximum / minimum over the finitely many charts"), `def:thb-inputs`.

## Proved here

* `OneStepConsts.Le`, `Chart.Ok.mono`: `JB.Chart.Ok` is monotone in the constants (`C, K, omega_max, C_4, C_E` up, `c_T, c_alpha, c_0` down), for `0 < h <= 1`.
* `exists_consts_join`: finitely many constants have a common upper bound (`cs.nb` arbitrary: it plays no role in `Chart.Ok`).
* `ThbBlock`: the data of one block of `OneStepInputs` (two charts with `Chart.Ok`, `match0/1` on the used rows, and the bound of the entries of `G0, G1, U` on the columns of the block outside the used rows,
  which becomes `OneStepInputs.outside`), `ThbBlock.mono`.
* `exists_uniform_blocks`: for a finite family of blocks, each realised with its own constants for `N >= N0`, `h <= h0`, there are common constants.
* `oneStepInputs_of_blocks`: **the assembly of `JB.OneStepInputs` from the blocks**: `cols_disjoint`, `chart_ok`, `match0/1`, `outside` from `ThbBlock`, `G1_col` and `U_orth` as hypotheses.

## Differences from the paper

None: the maxima and minima over the blocks are finite (`Finite`), the constants are chosen before `mu`, `N`.

## Not formalised

The blocks themselves (bulk: `ThbBulk`, soft: `ThbSoft`, `ThbLower`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JB

/-- `a ≤ b` for the constants of the one-step criterion (the block count `nb` is ignored: it does not occur in `Chart.Ok`). -/
def OneStepConsts.Le (a b : OneStepConsts) : Prop :=
  a.C ≤ b.C ∧ a.K ≤ b.K ∧ a.ωmax ≤ b.ωmax ∧ b.cT ≤ a.cT ∧ b.cα ≤ a.cα ∧ b.c0 ≤ a.c0 ∧ a.C4 ≤ b.C4 ∧ a.CE ≤ b.CE

theorem OneStepConsts.Le.refl (a : OneStepConsts) : a.Le a :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem OneStepConsts.Le.trans {a b c : OneStepConsts} (h1 : a.Le b) (h2 : b.Le c) : a.Le c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1.trans h2.2.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2⟩

section Mono

variable {D R : ℕ} {cols : Finset (Fin D)}

/-- `Chart.Ok` is monotone in the constants (for `0 < h ≤ 1`: the `log(1/h)` of `host1_col` is nonnegative). -/
theorem Chart.Ok.mono {cs cs' : OneStepConsts} (hle : cs.Le cs') {m : ℕ} {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    {U : Matrix (Fin D) (Fin D) ℝ} {c : Chart D R cols} (hok : c.Ok cs m h U) : c.Ok cs' m h U := by
  obtain ⟨hC, hK, hω, hT, hα, hc0, hC4, hCE⟩ := hle
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  have hp : 0 ≤ h ^ m := pow_nonneg h0.le _
  have hp1 : 0 ≤ h ^ (m + 1) * Real.log (1 / h) := mul_nonneg (pow_nonneg h0.le _) hlog
  exact
    { host0_eq := hok.host0_eq
      host1_eq := hok.host1_eq
      host0_col := fun j => (hok.host0_col j).trans (mul_le_mul_of_nonneg_right hC hp)
      host1_col := fun j => by
        refine (hok.host1_col j).trans ?_
        have := mul_le_mul_of_nonneg_right hC hp1
        linarith
      parity_A := hok.parity_A
      parity_B := hok.parity_B
      ω_pos := fun n => ⟨(hok.ω_pos n).1, (hok.ω_pos n).2.trans hω⟩
      transfer := hok.transfer
      t12_lb := fun n k => hT.trans (hok.t12_lb n k)
      α_lb := fun n k => hα.trans (hok.α_lb n k)
      schur_inv_α := hok.schur_inv_α.mono hK
      schur_B := hok.schur_B.mono hK
      schur_inv_t12 := hok.schur_inv_t12.mono hK
      schur_t11 := hok.schur_t11.mono hK
      schur_κ := hok.schur_κ.mono hK
      ext_row := fun n h1' h2' => (hok.ext_row n h1' h2').trans hCE
      overlap_lb := fun k => hc0.trans (hok.overlap_lb k)
      overlap_ub := fun k => (hok.overlap_ub k).trans (mul_le_mul_of_nonneg_right hC4 (by unfold jbL2; exact Real.sqrt_nonneg _)) }

end Mono

end FormalResearch.JB

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JB
open scoped Matrix

/-- `1 / (1 + ∑ 1/c_i) ≤ c_i`, positive: a common positive lower bound of finitely many positive reals. -/
theorem exists_pos_lower {ι : Type*} [Finite ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) : ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ c i := by
  have := Fintype.ofFinite ι
  refine ⟨1 / (1 + ∑ i, 1 / c i), by
    have : 0 ≤ ∑ i, 1 / c i := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hc i)).le)
    positivity, fun i => ?_⟩
  have h1 : 1 / c i ≤ ∑ i, 1 / c i :=
    Finset.single_le_sum (f := fun i => 1 / c i) (fun j _ => (one_div_pos.mpr (hc j)).le) (Finset.mem_univ i)
  rw [div_le_iff₀ (by have : 0 ≤ ∑ i, 1 / c i := Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hc i)).le); positivity)]
  have := hc i
  have h2 : 1 ≤ c i * (1 / c i) := by rw [mul_one_div_cancel this.ne']
  nlinarith [mul_le_mul_of_nonneg_left h1 this.le]

/-- A common upper bound of finitely many nonnegative reals. -/
theorem exists_nonneg_upper {ι : Type*} [Finite ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) : ∃ d : ℝ, 0 ≤ d ∧ ∀ i, c i ≤ d := by
  have := Fintype.ofFinite ι
  exact ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => hc i), fun i =>
    Finset.single_le_sum (f := c) (fun j _ => hc j) (Finset.mem_univ i)⟩

/-- **Finitely many constants have a common bound.** -/
theorem exists_consts_join {ι : Type*} [Finite ι] (f : ι → OneStepConsts) : ∃ cs : OneStepConsts, ∀ i, (f i).Le cs := by
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_upper (fun i => (f i).C) (fun i => (f i).C_nonneg)
  obtain ⟨K, hK0, hK⟩ := exists_nonneg_upper (fun i => (f i).K) (fun i => (f i).K_nonneg)
  obtain ⟨ω, hω0, hω⟩ := exists_nonneg_upper (fun i => (f i).ωmax) (fun i => (f i).ωmax_pos.le)
  obtain ⟨C4, hC40, hC4⟩ := exists_nonneg_upper (fun i => (f i).C4) (fun i => (f i).C4_nonneg)
  obtain ⟨CE, hCE0, hCE⟩ := exists_nonneg_upper (fun i => (f i).CE) (fun i => (f i).CE_nonneg)
  obtain ⟨cT, hcT0, hcT⟩ := exists_pos_lower (fun i => (f i).cT) (fun i => (f i).cT_pos)
  obtain ⟨cα, hcα0, hcα⟩ := exists_pos_lower (fun i => (f i).cα) (fun i => (f i).cα_pos)
  obtain ⟨c0, hc00, hc0⟩ := exists_pos_lower (fun i => (f i).c0) (fun i => (f i).c0_pos)
  refine ⟨⟨0, C, K, ω + 1, cT, cα, c0, C4, CE, hC0, hK0, by linarith, hcT0, hcα0, hc00, hC40, hCE0⟩, fun i => ?_⟩
  exact ⟨hC i, hK i, (hω i).trans (by simp), hcT i, hcα i, hc0 i, hC4 i, hCE i⟩

/-- One block of `OneStepInputs` for the columns `cols`: its two charts (left/right) with `Chart.Ok`, `match0/1` on the used rows, and the entries of `G0`, `G1`, `U` on the columns of the block outside all used
rows of its two charts bounded by `Cε exp(-cε/h)` (this becomes `OneStepInputs.outside`). -/
structure ThbBlock (cs : OneStepConsts) (N m : ℕ) (h : ℝ) (Um G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (cols : Finset (Fin (N + 1))) (Cε cε : ℝ) where
  RL : ℕ
  RR : ℕ
  chL : Chart (N + 1) RL cols
  chR : Chart (N + 1) RR cols
  okL : chL.Ok cs m h Um
  okR : chR.Ok cs m h Um
  match0L : ∀ n : Fin RL, n ∈ chL.used → ∀ k : cols, G0 (chL.row n) k = chL.H0 h n k
  match0R : ∀ n : Fin RR, n ∈ chR.used → ∀ k : cols, G0 (chR.row n) k = chR.H0 h n k
  match1L : ∀ n : Fin RL, n ∈ chL.used → ∀ k : cols, G1 (chL.row n) k = chL.H1 h n k
  match1R : ∀ n : Fin RR, n ∈ chR.used → ∀ k : cols, G1 (chR.row n) k = chR.H1 h n k
  cover : ∀ k ∈ cols, ∀ i : Fin (N + 1), (¬ ∃ n : Fin RL, n ∈ chL.used ∧ chL.row n = i) → (¬ ∃ n : Fin RR, n ∈ chR.used ∧ chR.row n = i) →
    |G0 i k| ≤ Cε * Real.exp (-cε / h) ∧ |G1 i k| ≤ Cε * Real.exp (-cε / h) ∧ |Um i k| ≤ Cε * Real.exp (-cε / h)

/-- `ThbBlock` is monotone in the constants (`0 ≤ Cε`, `cε' ≤ cε`, `0 < h ≤ 1`). -/
def ThbBlock.mono {cs cs' : OneStepConsts} (hle : cs.Le cs') {N m : ℕ} {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    {Um G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {cols : Finset (Fin (N + 1))} {Cε cε Cε' cε' : ℝ}
    (hC0 : 0 ≤ Cε) (hC : Cε ≤ Cε') (hc : cε' ≤ cε) (B : ThbBlock cs N m h Um G0 G1 cols Cε cε) :
    ThbBlock cs' N m h Um G0 G1 cols Cε' cε' where
  RL := B.RL
  RR := B.RR
  chL := B.chL
  chR := B.chR
  okL := B.okL.mono hle h0 h1
  okR := B.okR.mono hle h0 h1
  match0L := B.match0L
  match0R := B.match0R
  match1L := B.match1L
  match1R := B.match1R
  cover := fun k hk i hi1 hi2 => by
    have hexp : Real.exp (-cε / h) ≤ Real.exp (-cε' / h) := by
      apply Real.exp_le_exp.mpr
      have : cε' / h ≤ cε / h := div_le_div_of_nonneg_right hc h0.le
      linarith [neg_div h cε, neg_div h cε']
    have hexp0 : 0 ≤ Real.exp (-cε / h) := (Real.exp_pos _).le
    have key : Cε * Real.exp (-cε / h) ≤ Cε' * Real.exp (-cε' / h) :=
      mul_le_mul hC hexp hexp0 (hC0.trans hC)
    obtain ⟨a, b, c⟩ := B.cover k hk i hi1 hi2
    exact ⟨a.trans key, b.trans key, c.trans key⟩

/-- **Uniform constants over a finite family of blocks.**  If for every index `i` the family of blocks exists with its own constants for `N ≥ N0`, `h ≤ h0`, then there are common constants. -/
theorem exists_uniform_blocks {ι : Type*} [Finite ι] {Par : Type*} (K : Set Par) (step : ℕ → ℝ) (m : ℕ)
    (Gm : Par → (N : ℕ) → (Fin (N + 1) → ℝ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ → Prop)
    (G0 G1 : Par → (N : ℕ) → (Fin (N + 1) → ℝ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (colsf : ι → (N : ℕ) → (Fin (N + 1) → ℝ) → Finset (Fin (N + 1)))
    (H : ∀ i, ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → step N ≤ h0 → ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), Gm μ N Xs Um →
        Nonempty (ThbBlock cs N m (step N) Um (G0 μ N Xs) (G1 μ N Xs) (colsf i N Xs) Cε cε))
    (hstep : ∀ N, 0 < step N) :
    ∃ (cs : OneStepConsts) (Cε cε : ℝ) (N0 : ℕ) (h0 : ℝ), 0 ≤ Cε ∧ 0 < cε ∧ 0 < h0 ∧ h0 ≤ 1 ∧
      ∀ i, ∀ μ ∈ K, ∀ N : ℕ, N0 ≤ N → step N ≤ h0 → ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), Gm μ N Xs Um →
        Nonempty (ThbBlock cs N m (step N) Um (G0 μ N Xs) (G1 μ N Xs) (colsf i N Xs) Cε cε) := by
  classical
  choose cs Cε cε N0 h0 hC0 hc0 hh0 hh1 Hi using H
  have := Fintype.ofFinite ι
  obtain ⟨csJ, hcsJ⟩ := exists_consts_join cs
  obtain ⟨Cm, hCm0, hCm⟩ := exists_nonneg_upper Cε hC0
  obtain ⟨cm, hcm0, hcm⟩ := exists_pos_lower cε hc0
  obtain ⟨hm0, hmpos, hmle⟩ : ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ h0 i := exists_pos_lower h0 hh0
  refine ⟨csJ, Cm, cm, Finset.univ.sup N0, min hm0 1, hCm0, hcm0, lt_min hmpos one_pos, min_le_right _ _, ?_⟩
  intro i μ hμ N hN hs Xs Um hG
  have hN' : N0 i ≤ N := (Finset.le_sup (f := N0) (Finset.mem_univ i)).trans hN
  have hs' : step N ≤ h0 i := hs.trans ((min_le_left _ _).trans (hmle i))
  obtain ⟨B⟩ := Hi i μ hμ N hN' hs' Xs Um hG
  exact ⟨B.mono (hcsJ i) (hstep N) (hs.trans (min_le_right _ _)) (hC0 i) (hCm i) (hcm i)⟩

section Assembly

variable {N m : ℕ} {h : ℝ}

/-- **The assembly of `JB.OneStepInputs` from the blocks.**  `colsf ν` are the column sets of the blocks (pairwise disjoint, covering all columns); the blocks give `chart_ok`, `match0/1`, and `outside`
(a column lies in some block, whose charts either use the row or bound the entry); `G1_col`, `U_orth`, `1 ≤ m`, `0 < h` are the remaining fields. -/
def oneStepInputs_of_blocks (cs : OneStepConsts) (Um G0 G1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (colsf : Fin cs.nb → Finset (Fin (N + 1))) (hdisj : ∀ ν ν', ν ≠ ν' → Disjoint (colsf ν) (colsf ν'))
    (hcov : ∀ k : Fin (N + 1), ∃ ν, k ∈ colsf ν) (Cε cε : ℝ) (hC0 : 0 ≤ Cε)
    (B : ∀ ν, ThbBlock cs N m h Um G0 G1 (colsf ν) Cε cε) (hh : 0 < h) (hm : 1 ≤ m) (horth : Umᵀ * Um = 1)
    (hG1 : ∀ j : Fin (N + 1), jbL2 Finset.univ (fun i => G1 i j - Um i j) ≤ cs.C * h ^ (m + 1) * Real.log (1 / h)) :
    OneStepInputs cs (N + 1) m h where
  U := Um
  G0 := G0
  G1 := G1
  cols := colsf
  R := fun ν j => match j with | 0 => (B ν).RL | 1 => (B ν).RR
  ch := fun ν j => match j with | 0 => (B ν).chL | 1 => (B ν).chR
  ε5 := Cε * Real.exp (-cε / h)
  h_pos := hh
  one_le_m := hm
  U_orth := horth
  cols_disjoint := hdisj
  chart_ok := fun ν j => by
    fin_cases j
    · exact (B ν).okL
    · exact (B ν).okR
  G1_col := hG1
  match0 := fun ν j => by
    fin_cases j
    · exact fun n hn k => (B ν).match0L n hn k
    · exact fun n hn k => (B ν).match0R n hn k
  match1 := fun ν j => by
    fin_cases j
    · exact fun n hn k => (B ν).match1L n hn k
    · exact fun n hn k => (B ν).match1R n hn k
  ε5_nonneg := mul_nonneg hC0 (Real.exp_pos _).le
  outside := fun i k hnot => by
    obtain ⟨ν, hν⟩ := hcov k
    refine (B ν).cover k hν i ?_ ?_
    · rintro ⟨n, hn, hr⟩
      exact hnot ⟨ν, 0, n, hn, hr, hν⟩
    · rintro ⟨n, hn, hr⟩
      exact hnot ⟨ν, 1, n, hn, hr, hν⟩

end Assembly

end FormalResearch.JacobiEigenvectors.TheoremB

end

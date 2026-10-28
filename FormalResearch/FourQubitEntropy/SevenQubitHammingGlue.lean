import Mathlib
import FormalResearch.FourQubitEntropy.SevenQubitIcoXHamming
import FormalResearch.FourQubitEntropy.SevenQubitHammingBlockPurityC
import FormalResearch.FourQubitEntropy.SpinFlipReduced

/-!
# Hamming-ball block purity: state-level glue (`thm:hamming-ball-schmidt`, `thm:low-excitation-exclusion`)

Source: `ResearchNotes/QI/seven_qubit_entanglement/hamming_ball_schmidt.tex`.

**Proved here.** `hamming_rank_le_C` (complex version of the vertex-cover rank bound by `hammingRank`),
`purity_bound_matrix` (matrix-level robust purity bound), and the state-level statements for
`ψ : Ψ n` (complex amplitudes), any cut `S` with `|S| = k`: `hamming_ball_cut_purity`
(`(1-η)²/R + η²/(2^k-R) ≤ tr ρ_S²` with `η = leak ψ r`, the mass outside the ball of radius `r`),
`hamming_ball_support_purity` (`η = 0`: `1/R ≤ tr ρ_S²`), `hamming_ball_mean_purity` (the same for the mean
over cuts). Seven-qubit specializations: `low_excitation_cut`, `low_excitation_exclusion`,
`low_excitation_exclusion_form`, `low_excitation_two_fifteenths`.

**Not proved here.** Invariance of `tr ρ_S²` under local unitaries, so "every local product basis" is
obtained by applying these theorems to the rotated vector, not stated; the lower bound of the exact rank
formula for general `(n, k, r)`; the entropy inequality `eq:hamming-ball-robust-entropy`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco.HammingGlue

open Finset Matrix
open FormalResearch.FourQubitEntropy.SevenQubitIco.Hermitian

/-! ### Weights of configurations on an arbitrary finite site set -/

/-- Hamming weight of a configuration `x : α → Fin 2` (number of sites in state `1`). -/
def wf {α : Type*} [Fintype α] (x : α → Fin 2) : ℕ := (univ.filter fun i => x i ≠ 0).card

/-- Transport of configurations along `α ≃ Fin (card α)` and `Fin 2 ≃ Bool`. -/
noncomputable def cfgEquiv (α : Type*) [Fintype α] [DecidableEq α] : (α → Fin 2) ≃ (Fin (Fintype.card α) → Bool) :=
  Equiv.arrowCongr (Fintype.equivFin α) finTwoEquiv

theorem wt_cfgEquiv {α : Type*} [Fintype α] [DecidableEq α] (a : α → Fin 2) : wt (cfgEquiv α a) = wf a := by
  unfold wt wf
  rw [Finset.card_filter]
  refine (Fintype.sum_equiv (Fintype.equivFin α).symm _ _ fun j => ?_)
  simp only [cfgEquiv, Equiv.arrowCongr_apply, Function.comp_apply]
  generalize a ((Fintype.equivFin α).symm j) = i
  by_cases h : i = 0
  · simp [h, finTwoEquiv]
  · have : i = 1 := by omega
    simp [this, finTwoEquiv]

/-- Strings of weight `< t` on an arbitrary finite site set are counted by `ballCount`. -/
theorem card_wf_lt (α : Type*) [Fintype α] [DecidableEq α] (t : ℕ) :
    (univ.filter fun a : α → Fin 2 => wf a < t).card = ballCount (Fintype.card α) t := by
  rw [← card_wt_lt]
  refine Finset.card_bij (fun a _ => cfgEquiv α a) ?_ (fun a _ b _ h => (cfgEquiv α).injective h) ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    rwa [wt_cfgEquiv]
  · intro b hb
    refine ⟨(cfgEquiv α).symm b, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rwa [← wt_cfgEquiv, Equiv.apply_symm_apply] 


/-! ### The rank bound for complex matrices -/

theorem matrix_rank_add_le_C {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have h : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, by simp⟩
  calc Module.finrank ℂ (LinearMap.range (A + B).mulVecLin)
      ≤ Module.finrank ℂ (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
        Submodule.finrank_mono h
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Complex version of `SevenQubitIco.rank_le_cover`: if every nonzero entry has its row in `S` or its
column in `T`, then `rank M ≤ |S| + |T|`. -/
theorem rank_le_cover_C {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℂ) (S : Finset ι) (T : Finset κ)
    (h : ∀ a b, a ∉ S → b ∉ T → M a b = 0) : M.rank ≤ S.card + T.card := by
  classical
  let DS : Matrix ι ι ℂ := diagonal fun a => if a ∈ S then 1 else 0
  let E : Matrix ι ι ℂ := diagonal fun a => if a ∈ S then 0 else 1
  let DT : Matrix κ κ ℂ := diagonal fun b => if b ∈ T then 1 else 0
  have hM : M = DS * M + E * M * DT := by
    ext a b
    simp only [DS, E, DT, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases ha : a ∈ S
    · simp [ha]
    · by_cases hb : b ∈ T
      · simp [ha, hb]
      · simp [ha, hb, h a b ha hb]
  have h1 : (DS * M).rank ≤ S.card := by
    refine (Matrix.rank_mul_le_left DS M).trans ?_
    simp only [DS, Matrix.rank_diagonal]
    rw [Fintype.card_subtype]
    simp
  have h2 : (E * M * DT).rank ≤ T.card := by
    refine (Matrix.rank_mul_le_right (E * M) DT).trans ?_
    simp only [DT, Matrix.rank_diagonal]
    rw [Fintype.card_subtype]
    simp
  calc M.rank = (DS * M + E * M * DT).rank := by rw [← hM]
    _ ≤ _ := matrix_rank_add_le_C _ _
    _ ≤ _ := Nat.add_le_add h1 h2

/-- **Upper bound of `eq:hamming-ball-rank`, complex matrices on arbitrary site sets.**
A complex matrix with rows `α → Fin 2` and columns `β → Fin 2` (`|α| = k`, `|β| = m`) that vanishes on
`wf a + wf b > r` has rank at most `R_{k+m,k,r} = hammingRank k m r`. -/
theorem hamming_rank_le_C {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (k m r : ℕ) (hk : Fintype.card α = k) (hm : Fintype.card β = m)
    (M : Matrix (α → Fin 2) (β → Fin 2) ℂ)
    (h : ∀ a b, r < wf a + wf b → M a b = 0) : M.rank ≤ hammingRank k m r := by
  subst hk hm
  unfold hammingRank
  refine le_min ?_ ?_
  · calc M.rank ≤ Fintype.card (α → Fin 2) := M.rank_le_card_height
      _ = 2 ^ Fintype.card α := by simp
  · refine Finset.le_inf' _ _ fun t _ => ?_
    classical
    have := rank_le_cover_C M (univ.filter fun a : α → Fin 2 => wf a < t)
      (univ.filter fun b : β → Fin 2 => wf b < r + 1 - t) (by
        intro a b ha hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha hb
        exact h a b (by omega))
    rwa [card_wf_lt, card_wf_lt] at this


/-! ### The matrix-level glue -/

/-- Monotonicity in the rank bound. -/
theorem rank_mono_bound (a b d q : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbd : b < d) (hbq : b ≤ q * d)
    (hq1 : q ≤ 1) :
    q ^ 2 / b + (1 - q) ^ 2 / (d - b) ≤ q ^ 2 / a + (1 - q) ^ 2 / (d - a) := by
  have hb : 0 < b := ha.trans_le hab
  have hda : 0 < d - a := by linarith
  have hdb : 0 < d - b := by linarith
  have hq0 : 0 ≤ q := by
    have : 0 < d := by linarith
    by_contra h; have h' := not_le.mp h; nlinarith
  have h1 : (1 - q) * a ≤ q * (d - a) := by nlinarith
  have h2 : (1 - q) * b ≤ q * (d - b) := by nlinarith
  have h0a : 0 ≤ (1 - q) * a := mul_nonneg (by linarith) ha.le
  have h0b : 0 ≤ (1 - q) * b := mul_nonneg (by linarith) hb.le
  have key : (1 - q) * a * ((1 - q) * b) ≤ q * (d - a) * (q * (d - b)) :=
    mul_le_mul h1 h2 h0b (h0a.trans h1)
  have : q ^ 2 / a + (1 - q) ^ 2 / (d - a) - (q ^ 2 / b + (1 - q) ^ 2 / (d - b)) =
      (b - a) * (q * (d - a) * (q * (d - b)) - (1 - q) * a * ((1 - q) * b)) /
        (a * b * (d - a) * (d - b)) := by
    field_simp
    ring
  have hnn : 0 ≤ (b - a) * (q * (d - a) * (q * (d - b)) - (1 - q) * a * ((1 - q) * b)) /
        (a * b * (d - a) * (d - b)) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  linarith


section MatrixLevel

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **State-level glue for one cut, matrix form** (`eq:hamming-ball-robust-purity`).
`M` is the `2^k × 2^m` coefficient matrix of a unit vector across a `k | m` cut; `η` is its squared
weight on `wf a + wf b > r`. -/
theorem purity_bound_matrix (r k m : ℕ) (hk : Fintype.card α = k) (hm : Fintype.card β = m)
    (M : Matrix (α → Fin 2) (β → Fin 2) ℂ)
    (hnorm : ∑ a, ∑ b, Complex.normSq (M a b) = 1) (η : ℝ)
    (hη : η = ∑ a, ∑ b, if r < wf a + wf b then Complex.normSq (M a b) else 0)
    (hR1 : 1 ≤ hammingRank k m r) (hRd : hammingRank k m r < 2 ^ k)
    (hle : η ≤ 1 - (hammingRank k m r : ℝ) / 2 ^ k) :
    (1 - η) ^ 2 / (hammingRank k m r : ℝ) + η ^ 2 / ((2 : ℝ) ^ k - hammingRank k m r) ≤
      (trace ((M * Mᴴ) * (M * Mᴴ))).re := by
  set R : ℝ := (hammingRank k m r : ℝ) with hRdef
  let MP : Matrix (α → Fin 2) (β → Fin 2) ℂ := Matrix.of fun a b =>
    if wf a + wf b ≤ r then M a b else 0
  let MN : Matrix (α → Fin 2) (β → Fin 2) ℂ := Matrix.of fun a b =>
    if r < wf a + wf b then M a b else 0
  have hsplit : M = MP + MN := by
    ext a b
    simp only [MP, MN, Matrix.add_apply, Matrix.of_apply]
    by_cases h : wf a + wf b ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have hrank : MP.rank ≤ hammingRank k m r := by
    refine hamming_rank_le_C k m r hk hm MP fun a b hab => ?_
    simp only [MP, Matrix.of_apply]
    simp [show ¬ (wf a + wf b ≤ r) by omega]
  obtain ⟨Q, hQh, hQi, hQtr, hQMP⟩ := exists_projector MP
  have hQ' : ∀ X : Matrix (α → Fin 2) (β → Fin 2) ℂ, Q * (Q * X) = Q * X :=
    fun X => by rw [← Matrix.mul_assoc, hQi]
  have hcard : Fintype.card (α → Fin 2) = 2 ^ k := by simp [hk]
  -- disjoint supports
  have hcrossPN : trace (MPᴴ * MN) = 0 := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
    simp only [MP, MN, Matrix.of_apply]
    by_cases h : wf a + wf b ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have hcrossNP : trace (MNᴴ * MP) = 0 := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
    simp only [MP, MN, Matrix.of_apply]
    by_cases h : wf a + wf b ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have hPnorm : (trace (MPᴴ * MP)).re = 1 - η := by
    rw [re_trace_conjTranspose_mul_self, ← hnorm, hη, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [MP, Matrix.of_apply]
    by_cases h : wf a + wf b ≤ r
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  -- the density matrix
  set ρ : Matrix (α → Fin 2) (α → Fin 2) ℂ := M * Mᴴ with hρdef
  have hρ : ρᴴ = ρ := by simp [hρdef, conjTranspose_mul]
  have htr : trace ρ = 1 := by
    have : trace ρ = ((∑ a, ∑ b, Complex.normSq (M a b) : ℝ) : ℂ) := by
      simp only [hρdef, trace, diag_apply, mul_apply, conjTranspose_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      exact Complex.mul_conj _
    rw [this, hnorm]; simp
  -- tr(Qρ) = tr(NᴴN), N = Q M
  have hNN : trace (Q * ρ) = trace ((Q * M)ᴴ * (Q * M)) := by
    have : (Q * M)ᴴ * (Q * M) = Mᴴ * (Q * M) := by
      rw [conjTranspose_mul, hQh, Matrix.mul_assoc, hQ']
    rw [this, trace_mul_comm Mᴴ (Q * M), hρdef, Matrix.mul_assoc]
  have hq : 1 - η ≤ (trace (Q * ρ)).re := by
    rw [hNN]
    have hN : Q * M = MP + Q * MN := by
      rw [hsplit, Matrix.mul_add, hQMP]
    have hMPQ : MPᴴ * Q = MPᴴ := by
      have := congrArg conjTranspose hQMP
      simpa [conjTranspose_mul, hQh] using this
    have e1 : trace (MPᴴ * (Q * MN)) = 0 := by
      rw [← Matrix.mul_assoc, hMPQ, hcrossPN]
    have e2 : trace ((Q * MN)ᴴ * MP) = 0 := by
      rw [conjTranspose_mul, hQh, Matrix.mul_assoc, hQMP, hcrossNP]
    have hexp : trace ((MP + Q * MN)ᴴ * (MP + Q * MN)) =
        trace (MPᴴ * MP) + trace ((Q * MN)ᴴ * (Q * MN)) := by
      simp only [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, trace_add, e1, e2]
      ring
    rw [hN, hexp, Complex.add_re, hPnorm]
    have := re_trace_conjTranspose_mul_self_nonneg (Q * MN)
    linarith
  -- positivity of the rank
  have hdpos : (0 : ℝ) < 2 ^ k := by positivity
  have hR1' : (1 : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hR1
  have hRd' : R < (2 : ℝ) ^ k := by rw [hRdef]; exact_mod_cast hRd
  have hcardR : (Fintype.card (α → Fin 2) : ℝ) = 2 ^ k := by exact_mod_cast hcard
  have hη0 : 0 ≤ η := by
    rw [hη]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
      split_ifs <;> simp [Complex.normSq_nonneg]
  have hRq : R / 2 ^ k ≤ 1 - η := by linarith
  have hR0le : (MP.rank : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hrank
  have hQtr' : (trace Q).re = (MP.rank : ℝ) := by rw [hQtr]; simp
  have hR0pos : 0 < (MP.rank : ℝ) := by
    rcases Nat.eq_zero_or_pos MP.rank with h0 | h0
    · exfalso
      have hc := Hermitian.compress_bound ρ Q hρ hQh hQi
      rw [hQtr', h0] at hc
      simp at hc
      have hqpos : 0 < 1 - η := by
        have : 0 < R / 2 ^ k := by positivity
        linarith
      linarith
    · exact_mod_cast h0
  have hRQ : ((MP.rank : ℝ)) < (Fintype.card (α → Fin 2) : ℝ) := by rw [hcardR]; linarith
  have hmain := robust_purity_bound_herm hρ hQh hQi (MP.rank : ℝ) (by rw [hQtr]; simp) hR0pos
    (by exact_mod_cast (show MP.rank < Fintype.card (α → Fin 2) by exact_mod_cast hRQ)) htr η hq
    (by rw [hcardR]; exact (div_le_div_of_nonneg_right hR0le hdpos.le).trans hRq)
  rw [hcardR] at hmain
  have hmono := rank_mono_bound (MP.rank : ℝ) R ((2 : ℝ) ^ k) (1 - η) hR0pos hR0le hRd'
    (by rw [div_le_iff₀ hdpos] at hRq; linarith) (by linarith)
  have e : (1 - (1 - η)) = η := by ring
  rw [e] at hmono
  exact hmono.trans hmain

end MatrixLevel


/-! ### State level: configurations of `n` qubits and the cuts `S | Sᶜ` -/

section StateLevel

open FormalResearch.FrameFree.NQubit (Ψ nsq)
open FormalResearch.FourQubitEntropy.SpinFlip (CfgOn CfgOff)

variable {n : ℕ}

theorem wf_glue (S : Finset (Fin n)) (x : CfgOn S) (t : CfgOff S) :
    wf (SpinFlip.glue S x t) = wf x + wf t := by
  unfold wf
  simp only [Finset.card_filter]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ S)]
  congr 1
  · refine Finset.sum_congr (by ext; simp) fun i _ => ?_
    simp [SpinFlip.glue, i.2]
  · refine Finset.sum_congr (by ext; simp) fun i _ => ?_
    simp [SpinFlip.glue, i.2]

theorem sum_glue_real (S : Finset (Fin n)) (F : (Fin n → Fin 2) → ℝ) :
    ∑ X, F X = ∑ x : CfgOn S, ∑ t : CfgOff S, F (SpinFlip.glue S x t) := by
  rw [← (SpinFlip.glueEquiv S).sum_comp, Fintype.sum_prod_type]; rfl

theorem card_cfgOn (S : Finset (Fin n)) : Fintype.card (CfgOn S) = 2 ^ S.card := by
  simp [CfgOn]

theorem card_site_off (S : Finset (Fin n)) : Fintype.card {i // i ∉ S} = n - S.card := by
  rw [Fintype.card_subtype_compl]; simp


/-- The `2^{|S|} × 2^{n-|S|}` coefficient matrix of `ψ` across the cut `S | Sᶜ`
(`ψ` on the configuration obtained by gluing a row configuration on `S` to a column configuration off `S`). -/
def cutM (ψ : Ψ n) (S : Finset (Fin n)) :
    Matrix (SpinFlip.CfgOn S) (SpinFlip.CfgOff S) ℂ := fun x t => ψ (SpinFlip.glue S x t)

/-- The reduced density matrix `ρ_S` of `SpinFlip.rdm` is `M Mᴴ` for the cut matrix `M`. -/
theorem rdm_eq_cutM (ψ : Ψ n) (S : Finset (Fin n)) :
    SpinFlip.rdm ψ S = cutM ψ S * (cutM ψ S)ᴴ := by
  ext x y
  simp [SpinFlip.rdm, cutM, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- `η_B`: the squared weight of `ψ` on computational-basis strings of Hamming weight `> r`, i.e.
`‖(I - P_{≤ r}) ψ‖²`. -/
noncomputable def leak (ψ : Ψ n) (r : ℕ) : ℝ :=
  ∑ X : Fin n → Fin 2, if r < wf X then Complex.normSq (ψ X) else 0

theorem leak_nonneg (ψ : Ψ n) (r : ℕ) : 0 ≤ leak ψ r :=
  Finset.sum_nonneg fun X _ => by split_ifs <;> simp [Complex.normSq_nonneg]

/-- **State-level glue for one cut** (`thm:hamming-ball-schmidt`, `eq:hamming-ball-robust-purity`,
purity half). Let `ψ` be a unit vector of `n` qubits, `S` a set of `k` sites and `η = leak ψ r` its
squared weight on strings of excitation weight `> r` (computational basis). With
`R = hammingRank k (n-k) r` (the rank bound `R_{n,k,r}` of `eq:hamming-ball-rank`),
`1 ≤ R < 2^k` and `η ≤ 1 - R/2^k`,
`tr ρ_S(ψ)² ≥ (1-η)²/R + η²/(2^k - R)`.
Proved for complex `ψ` and the honest reduced density matrix `SpinFlip.rdm`; the ingredients are the
cover rank bound `hamming_rank_le_C`, the projector `exists_projector` onto the column space of the ball
component, and the block bound `robust_purity_bound_herm`.
Not included: the equality statement `R_{n,k,r}` = maximal rank for general `(n,k,r)` (lower bound),
the entropy inequality `eq:hamming-ball-robust-entropy`, and basis independence (apply to the rotated
state; invariance of `tr ρ_S²` under local unitaries is not proved here). -/
theorem hamming_ball_cut_purity (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) (r k m : ℕ)
    (hk : S.card = k) (hm : n - k = m)
    (hR1 : 1 ≤ hammingRank k m r) (hRd : hammingRank k m r < 2 ^ k)
    (hle : leak ψ r ≤ 1 - (hammingRank k m r : ℝ) / 2 ^ k) :
    (1 - leak ψ r) ^ 2 / (hammingRank k m r : ℝ) +
        leak ψ r ^ 2 / ((2 : ℝ) ^ k - hammingRank k m r) ≤ SpinFlip.purity ψ S := by
  have hα : Fintype.card {i // i ∈ S} = k := by simp [hk]
  have hβ : Fintype.card {i // i ∉ S} = m := by rw [card_site_off, hk, hm]
  have hnorm : ∑ x : SpinFlip.CfgOn S, ∑ t : SpinFlip.CfgOff S,
      Complex.normSq (cutM ψ S x t) = 1 := by
    rw [← hψ, nsq, sum_glue_real S (fun X => Complex.normSq (ψ X))]
    rfl
  have hη : leak ψ r = ∑ x : SpinFlip.CfgOn S, ∑ t : SpinFlip.CfgOff S,
      if r < wf x + wf t then Complex.normSq (cutM ψ S x t) else 0 := by
    rw [leak, sum_glue_real S]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
    rw [wf_glue]; rfl
  have h := purity_bound_matrix (α := {i // i ∈ S}) (β := {i // i ∉ S}) r k m hα hβ (cutM ψ S)
    hnorm (leak ψ r) hη hR1 hRd hle
  have e : SpinFlip.purity ψ S = ((cutM ψ S * (cutM ψ S)ᴴ) * (cutM ψ S * (cutM ψ S)ᴴ)).trace.re := by
    rw [← rdm_eq_cutM]
    have := congrArg Complex.re (SpinFlip.purity_eq_trace ψ S)
    simpa using this
  rw [e]
  exact h



/-- **Ball-supported vectors** (`η = 0` of `thm:hamming-ball-schmidt`): a unit vector supported on strings
of excitation weight `≤ r` has `tr ρ_S² ≥ 1/R` across every `k`-site cut, `R = hammingRank k (n-k) r`,
whenever `1 ≤ R < 2^k`. -/
theorem hamming_ball_support_purity (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) (r k m : ℕ)
    (hk : S.card = k) (hm : n - k = m) (hsupp : ∀ X : Fin n → Fin 2, r < wf X → ψ X = 0)
    (hR1 : 1 ≤ hammingRank k m r) (hRd : hammingRank k m r < 2 ^ k) :
    1 / (hammingRank k m r : ℝ) ≤ SpinFlip.purity ψ S := by
  have h0 : leak ψ r = 0 := by
    refine Finset.sum_eq_zero fun X _ => ?_
    by_cases h : r < wf X
    · simp [h, hsupp X h]
    · simp [h]
  have hRpos : (0 : ℝ) < (hammingRank k m r : ℝ) := by exact_mod_cast hR1
  have hd : (0 : ℝ) < 2 ^ k := by positivity
  have := hamming_ball_cut_purity ψ hψ S r k m hk hm hR1 hRd (by
    rw [h0]; have : (hammingRank k m r : ℝ) / 2 ^ k ≤ 1 := by
      rw [div_le_one hd]; exact_mod_cast hRd.le
    linarith)
  rw [h0] at this
  simpa using this

/-- **Mean over all `k`-subsets** (`π_k(ψ) = Pur ψ k / C(n,k)`; "the same bounds apply to the averages"
of `thm:hamming-ball-schmidt`, purity half): under the hypotheses of `hamming_ball_cut_purity`,
`π_k(ψ) ≥ (1-η)²/R + η²/(2^k - R)`. -/
theorem hamming_ball_mean_purity (ψ : Ψ n) (hψ : nsq ψ = 1) (r k : ℕ) (hkn : k ≤ n)
    (hR1 : 1 ≤ hammingRank k (n - k) r) (hRd : hammingRank k (n - k) r < 2 ^ k)
    (hle : leak ψ r ≤ 1 - (hammingRank k (n - k) r : ℝ) / 2 ^ k) :
    (1 - leak ψ r) ^ 2 / (hammingRank k (n - k) r : ℝ) +
        leak ψ r ^ 2 / ((2 : ℝ) ^ k - hammingRank k (n - k) r) ≤
      SpinFlip.Pur ψ k / (n.choose k : ℝ) := by
  have hc : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkn
  rw [le_div_iff₀ hc]
  unfold SpinFlip.Pur SpinFlip.PurU
  have hcard : (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card = n.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_nsmul_le_sum (Finset.univ.powersetCard k : Finset (Finset (Fin n)))
    (fun S => SpinFlip.purity ψ S)
    ((1 - leak ψ r) ^ 2 / (hammingRank k (n - k) r : ℝ) +
        leak ψ r ^ 2 / ((2 : ℝ) ^ k - hammingRank k (n - k) r)) (by
      intro S hS
      exact hamming_ball_cut_purity ψ hψ S r k (n - k) (Finset.mem_powersetCard.1 hS).2 rfl hR1
        hRd hle)
  rw [hcard, nsmul_eq_mul] at this
  linarith

end StateLevel

/-! ### `(n, k, r) = (7, 3, 2)`: `thm:low-excitation-exclusion` -/

section SevenQubit

open FormalResearch.FrameFree.NQubit (Ψ nsq)

/-- **`thm:low-excitation-exclusion`, one cut, computational basis.** For every normalized seven-qubit
vector `ψ` with squared weight `η = leak ψ 2 ≤ 3/8` on strings of excitation weight `≥ 3`, every
`3 | 4` cut has `tr ρ_S² ≥ (1-η)²/5 + η²/3`. (`R_{7,3,2} = 5` is `hammingRank_732`.) -/
theorem low_excitation_cut (ψ : Ψ 7) (hψ : nsq ψ = 1) (S : Finset (Fin 7)) (hS : S.card = 3)
    (hη : leak ψ 2 ≤ 3 / 8) :
    (1 - leak ψ 2) ^ 2 / 5 + leak ψ 2 ^ 2 / 3 ≤ SpinFlip.purity ψ S := by
  have h := hamming_ball_cut_purity ψ hψ S 2 3 4 hS rfl (by rw [hammingRank_732]; norm_num)
    (by rw [hammingRank_732]; norm_num) (by rw [hammingRank_732]; norm_num; linarith)
  rw [hammingRank_732] at h
  norm_num at h
  exact h

/-- **`thm:low-excitation-exclusion` (`eq:low-excitation-robust`).** For every normalized seven-qubit
vector `ψ` and `0 ≤ η = leak ψ 2 ≤ 3/8`, the mean three-body purity
`π₃(ψ) = Pur ψ 3 / 35` satisfies `π₃ ≥ (1-η)²/5 + η²/3 = 1/8 + (8/15)(η - 3/8)²`.
This is the statement in the fixed computational basis; the paper's "every local product basis" is this
statement applied to the locally rotated vector (invariance of the cut purities under local unitaries
is not proved here). -/
theorem low_excitation_exclusion (ψ : Ψ 7) (hψ : nsq ψ = 1) (hη : leak ψ 2 ≤ 3 / 8) :
    (1 - leak ψ 2) ^ 2 / 5 + leak ψ 2 ^ 2 / 3 ≤ SpinFlip.Pur ψ 3 / 35 := by
  have hrk : hammingRank 3 (7 - 3) 2 = 5 := hammingRank_732
  have h := hamming_ball_mean_purity ψ hψ 2 3 (by norm_num) (by rw [hrk]; norm_num)
    (by rw [hrk]; norm_num) (by rw [hrk]; norm_num; linarith)
  rw [hrk] at h
  norm_num [Nat.choose] at h
  exact h

/-- The closed form of the lower bound: `(1-η)²/5 + η²/3 = 1/8 + (8/15)(η - 3/8)²`. -/
theorem low_excitation_exclusion_form (ψ : Ψ 7) (hψ : nsq ψ = 1) (hη : leak ψ 2 ≤ 3 / 8) :
    1 / 8 + 8 / 15 * (leak ψ 2 - 3 / 8) ^ 2 ≤ SpinFlip.Pur ψ 3 / 35 := by
  have := low_excitation_exclusion ψ hψ hη
  rwa [robust_quadratic] at this

/-- `η_B ≤ 1/4` forces `π₃ ≥ 2/15` (`thm:low-excitation-exclusion`). -/
theorem low_excitation_two_fifteenths (ψ : Ψ 7) (hψ : nsq ψ = 1) (hη : leak ψ 2 ≤ 1 / 4) :
    2 / 15 ≤ SpinFlip.Pur ψ 3 / 35 :=
  (robust_quadratic_ge_two_fifteenths _ hη).trans (low_excitation_exclusion ψ hψ (by linarith))

end SevenQubit

end FormalResearch.FourQubitEntropy.SevenQubitIco.HammingGlue

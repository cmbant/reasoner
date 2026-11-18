module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountLink
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountOrder

/-!
# Paper J, Layer 2 (L2.C7): `lem:tha-count` plus the order argument, abstractly (`count_label`)

Source: app_thmA, proof of prop:tha-W2, Step 6 (counting, *Order*).

`count_label` applies `propThaCount` (`TheoremA/Count.lean`) with `I = [c - delta, c + delta]`, `Phi = pi M` (`M` a continuous strictly
decreasing function on `I`, in the application `M = mu_0(bandHi - .)`) and `eps = pi h / 8`, then runs the order argument
(`order_label_real`) with the window label `lab x = floor (M x / h)`.  Hypotheses: the sign facts (ii), (iii) of `lem:tha-count`
(as `SoftCountHyps` provides them), the eigen-system with `X_i <= c + delta` for all `i`, and the *label* hypothesis (i): every
eigenvalue in `I` lies within `h/8` of a window centre `(j + 1/2) h` of `M`.

Proved here (axiom-pinned):
* `count_label` (A): an eigenvalue `X_i` in `I` whose window `|M(X_i) - (j + 1/2) h| <= h/8` has index `i = j`;
  (B): for every `k` whose bracketing interval `[pi h k, pi h (k + 1)]` lies in `Phi(I)` there is an eigenvalue `X_k` in `I` of index `k`
  (and in the window `k`).

Differences from the paper: windows of fixed half-width `pi h / 8` in `Phi` (see `SoftCountHyps`); `I` is a closed interval around `c`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*}

lemma floor_label_eq {M h : ℝ} (hh : 0 < h) {j : ℕ} (hw : |M - ((j : ℝ) + 1 / 2) * h| ≤ h / 8) :
    ⌊M / h⌋₊ = j := by
  obtain ⟨h1, h2⟩ := abs_le.mp hw
  have hM : 0 ≤ M / h := by
    apply div_nonneg _ hh.le
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  rw [Nat.floor_eq_iff hM]
  constructor
  · rw [le_div_iff₀ hh]; nlinarith
  · rw [div_lt_iff₀ hh]; nlinarith

theorem count_label (F : SymbolFamily Par) (μ : Par) (N : ℕ) (hN1 : 1 ≤ N)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (c δ : ℝ) (M : ℝ → ℝ)
    (hMc : ContinuousOn M (Set.Icc (c - δ) (c + δ))) (hMs : StrictAntiOn M (Set.Icc (c - δ) (c + δ)))
    (hMend : M (c + δ) ≤ 0)
    (hsgn : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ X ∈ Set.Icc (c - δ) (c + δ), ∀ k : ℕ,
      Real.pi * M X = Real.pi * F.step N * k → SignType.sign (casD F μ N X) = SignType.sign (σ * (-1) ^ k))
    (hsgn' : ∃ σ' : ℝ, (σ' = 1 ∨ σ' = -1) ∧ ∀ X ∈ Set.Icc (c - δ) (c + δ), ∀ k : ℕ, casD F μ N X = 0 →
      |Real.pi * M X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ Real.pi * F.step N / 8 →
        ∀ κ' : ℝ, (∀ n ≤ N, pSol F μ N X n = κ' * qSol F μ N X (N - n)) →
          SignType.sign κ' = SignType.sign (σ' * (-1) ^ k))
    (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um)
    (hcap : ∀ i, Xs i ≤ c + δ)
    (hlab : ∀ i, Xs i ∈ Set.Icc (c - δ) (c + δ) → ∃ j : ℕ, |M (Xs i) - ((j : ℝ) + 1 / 2) * F.step N| ≤ F.step N / 8) :
    (∀ i, Xs i ∈ Set.Icc (c - δ) (c + δ) → ∀ j : ℕ, |M (Xs i) - ((j : ℝ) + 1 / 2) * F.step N| ≤ F.step N / 8 → (i : ℕ) = j) ∧
    (∀ k : ℕ, Set.Icc (Real.pi * F.step N * k) (Real.pi * F.step N * (k + 1)) ⊆
        (fun X => Real.pi * M X) '' Set.Icc (c - δ) (c + δ) →
      ∃ i, Xs i ∈ Set.Icc (c - δ) (c + δ) ∧ (i : ℕ) = k ∧ |M (Xs i) - ((k : ℝ) + 1 / 2) * F.step N| ≤ F.step N / 8) := by
  set h := F.step N with hhdef
  have hh : 0 < h := FormalResearch.JB.stepSize_pos F.L_pos N
  have hpi := Real.pi_pos
  set I := Set.Icc (c - δ) (c + δ) with hI
  have hwindow : ∀ x j, |Real.pi * M x - Real.pi * h * ((j : ℝ) + 1 / 2)| ≤ Real.pi * h / 8 ↔
      |M x - ((j : ℝ) + 1 / 2) * h| ≤ h / 8 := by
    intro x j
    have : Real.pi * M x - Real.pi * h * ((j : ℝ) + 1 / 2) = Real.pi * (M x - ((j : ℝ) + 1 / 2) * h) := by ring
    rw [this, abs_mul, abs_of_pos hpi, show Real.pi * h / 8 = Real.pi * (h / 8) by ring]
    exact mul_le_mul_iff_right₀ hpi
  have hΦc : ContinuousOn (fun X => Real.pi * M X) I := continuousOn_const.mul hMc
  have hΦs : StrictAntiOn (fun X => Real.pi * M X) I := fun x hx y hy hxy => by
    have := hMs hx hy hxy
    show Real.pi * M y < Real.pi * M x
    nlinarith
  have hwin : ∀ X ∈ I, casD F μ N X = 0 → ∃ k : ℕ, |Real.pi * M X - Real.pi * h * ((k : ℝ) + 1 / 2)| ≤ Real.pi * h / 8 := by
    intro X hX h0
    obtain ⟨i, hi⟩ := casD_zero_exists_eig hpos hN1 h0 Xs Um hE
    subst hi
    obtain ⟨j, hj⟩ := hlab i hX
    exact ⟨j, (hwindow _ j).mpr hj⟩
  obtain ⟨hu, hex⟩ := propThaCount F μ N hN1 hpos I (fun X => Real.pi * M X) (Real.pi * h / 8) Set.ordConnected_Icc hΦc
    (Or.inr hΦs) (by positivity) (by nlinarith) hwin hsgn hsgn'
  -- the window label
  have hmono' : ∀ x y, x ∈ I → y ∈ I → y ≤ x → M x ≤ M y := fun x y hx hy hyx => by
    rcases eq_or_lt_of_le hyx with e | e
    · rw [e]
    · exact (hMs hy hx e).le
  have key : ∀ i, Xs i ∈ I → ∀ j : ℕ, |M (Xs i) - ((j : ℝ) + 1 / 2) * h| ≤ h / 8 → (i : ℕ) = j := by
    intro i hi j hj
    have hlabj : ⌊M (Xs i) / h⌋₊ = j := floor_label_eq hh hj
    have hord := order_label_real Xs hE.anti {x | x ∈ I ∧ ∃ i', Xs i' = x} (fun x => ⌊M x / h⌋₊) i ⟨hi, i, rfl⟩
      (by
        intro i' hi'
        refine ⟨⟨?_, hcap i'⟩, i', rfl⟩
        have := hE.anti hi'
        exact (hi.1.trans this.le))
      (by
        intro x y hx hy hyx
        exact Nat.floor_mono (div_le_div_of_nonneg_right (hmono' x y hx.1 hy.1 hyx) hh.le))
      (by
        intro x y hx hy hxy
        obtain ⟨a, rfl⟩ := hx.2
        obtain ⟨b, rfl⟩ := hy.2
        obtain ⟨ja, hja⟩ := hlab a hx.1
        obtain ⟨jb, hjb⟩ := hlab b hy.1
        have e1 : ⌊M (Xs a) / h⌋₊ = ja := floor_label_eq hh hja
        have e2 : ⌊M (Xs b) / h⌋₊ = jb := floor_label_eq hh hjb
        have hj : ja = jb := by rw [← e1, ← e2]; exact hxy
        subst hj
        exact hu ja (Xs a) hx.1 (Xs b) hy.1 (casD_eig_zero hpos hN1 Xs Um hE a) (casD_eig_zero hpos hN1 Xs Um hE b)
          ((hwindow _ ja).mpr hja) ((hwindow _ ja).mpr hjb))
      (by
        intro j hj
        have hbr : Set.Icc (Real.pi * h * j) (Real.pi * h * (j + 1)) ⊆ (fun X => Real.pi * M X) '' I := by
          have hab : c - δ ≤ c + δ := le_trans hi.1 hi.2
          have hivt := intermediate_value_Icc' hab hΦc
          refine Set.Subset.trans ?_ hivt
          apply Set.Icc_subset_Icc
          · have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
            have h1 : Real.pi * M (c + δ) ≤ 0 := by nlinarith
            have h2 : 0 ≤ Real.pi * h * j := by positivity
            linarith
          · have hj1 : ((j : ℝ) + 1) ≤ M (Xs i) / h := by
              rw [hlabj] at hj
              have : j + 1 ≤ ⌊M (Xs i) / h⌋₊ := by rw [hlabj]; omega
              rw [Nat.le_floor_iff' (by omega)] at this
              exact_mod_cast this
            have hMi : M (Xs i) ≤ M (c - δ) := hmono' (Xs i) (c - δ) hi ⟨le_refl _, by linarith [hi.1, hi.2]⟩ hi.1
            have : h * ((j : ℝ) + 1) ≤ M (Xs i) := by
              rw [le_div_iff₀ hh] at hj1; linarith
            show Real.pi * h * (j + 1) ≤ Real.pi * M (c - δ)
            nlinarith
        obtain ⟨X, hX, h0, hXw⟩ := hex j hbr
        obtain ⟨i', hi'⟩ := casD_zero_exists_eig hpos hN1 h0 Xs Um hE
        subst hi'
        exact ⟨i', ⟨hX, i', rfl⟩, floor_label_eq hh ((hwindow _ j).mp hXw)⟩)
    rw [hlabj] at hord
    exact hord.symm
  refine ⟨key, ?_⟩
  intro k hk
  obtain ⟨X, hX, h0, hXw⟩ := hex k hk
  obtain ⟨i, hi⟩ := casD_zero_exists_eig hpos hN1 h0 Xs Um hE
  subst hi
  have hw := (hwindow _ k).mp hXw
  exact ⟨i, hX, key i hX k hw, hw⟩

end FormalResearch.JacobiEigenvectors.TheoremA

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.count_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.count_label

end

module

public import FormalResearch.JacobiEigenvectors.TheoremA.BulkProof
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation

/-!
# Paper J, Layer 2: the bulk eigenvector statement `PropThaW` (L2.C2, all three conjuncts)

Source: Paper J `thmA.tex` `prop:tha-W` (1), (2), `app_thmA.tex` "The bulk: proof of Proposition prop:tha-W", Steps 1--3.
Conjunct 1 is `bulk_conj1`; conjunct 2 (the collar) is `bulk_collar_bound` (`BulkProof.lean`); `propThaW` assembles them.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-- A row `k` whose mirror-or-left position lies below the chart's `c` is a row of the chain. -/
lemma le_NR_of {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hst : 0 < G.step N) (k : ℤ)
    (hk : uNode (G.step N) k ≤ C.c) : k ≤ (C.chain p X N).NR := by
  obtain ⟨-, -, -, -, hc2⟩ := C.shape p hp X hX N hN
  by_contra hcon
  rw [not_le] at hcon
  have := uNode_le_of_le hst.le (show (C.chain p X N).NR + 1 ≤ k by omega)
  linarith

/-- The eigen-column facts: the recurrence on all rows, the positive first entry, and unit norm. -/
lemma eigen_col_facts {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (Xs : Fin (N + 1) → ℝ)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um) (k : Fin (N + 1)) :
    JacSol F μ N (Xs k) ((N : ℤ) + 1) (eigVec Um k) ∧ 0 < eigVec Um k 0 ∧
      ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = 1 := by
  refine ⟨eigVec_JacSol F μ N Xs Um hE k, ?_, eigVec_sq_sum N Um hE.orth k⟩
  have h0 : extV (fun j => Um j k) ((((0 : Fin (N + 1)) : ℕ) : ℤ)) = Um 0 k := extV_fin (fun j => Um j k) 0
  have e : eigVec Um k 0 = Um 0 k := by
    have := h0
    simp only [Fin.val_zero, Nat.cast_zero] at this
    exact this
  rw [e]
  exact hE.pos k

/-- Summed squared envelopes: from `Sigma <= C_E^2 (C_sum/q^2 + C_M^2 q^2)` and `q^4 <= 1` we get `Sigma <= C_E^2 (C_sum + C_M^2)/q^2`. -/
lemma sum_env_CE2 (Sg CEg Csg CMg q : ℝ) (hq : 0 < q) (hq2sq : q ^ 2 * q ^ 2 ≤ 1)
    (hS : Sg ≤ CEg ^ 2 * (Csg / q ^ 2 + CMg ^ 2 * q ^ 2)) :
    Sg ≤ CEg ^ 2 * (Csg + CMg ^ 2) / q ^ 2 := by
  have h1 : CMg ^ 2 * q ^ 2 ≤ CMg ^ 2 / q ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hq2sq (sq_nonneg CMg)
    nlinarith
  have h2 : CEg ^ 2 * (Csg / q ^ 2 + CMg ^ 2 * q ^ 2) ≤ CEg ^ 2 * (Csg + CMg ^ 2) / q ^ 2 := by
    have e : CEg ^ 2 * (Csg + CMg ^ 2) / q ^ 2 = CEg ^ 2 * (Csg / q ^ 2 + CMg ^ 2 / q ^ 2) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith
  exact hS.trans h2

/-- **Squared perturbation**: if `|u - t v| <= |t| e E`, `|v| <= K E`, `e <= eps <= 1`, then `|u^2 - t^2 v^2| <= t^2 (eps (2K+1)) E^2`. -/
lemma sq_perturb (u v t e E K ε : ℝ) (he0 : 0 ≤ e) (he : e ≤ ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hv : |v| ≤ K * E) (hu : |u - t * v| ≤ |t| * e * E) :
    |u ^ 2 - t ^ 2 * v ^ 2| ≤ t ^ 2 * (ε * (2 * K + 1)) * E ^ 2 := by
  set d := u - t * v with hd
  have e1 : u ^ 2 - t ^ 2 * v ^ 2 = d * (d + 2 * t * v) := by rw [hd]; ring
  have hd2 : |d + 2 * t * v| ≤ |t| * E * (e + 2 * K) := by
    calc |d + 2 * t * v| ≤ |d| + |2 * t * v| := abs_add_le _ _
      _ ≤ |t| * e * E + 2 * |t| * (K * E) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have := mul_le_mul_of_nonneg_left hv (abs_nonneg t)
          linarith
      _ = |t| * E * (e + 2 * K) := by ring
  rw [e1, abs_mul]
  have ht := abs_nonneg t
  calc |d| * |d + 2 * t * v| ≤ (|t| * e * E) * (|t| * E * (e + 2 * K)) :=
        mul_le_mul hu (hd2.trans le_rfl) (abs_nonneg _) (by positivity)
    _ = t ^ 2 * (e * (e + 2 * K)) * E ^ 2 := by
        rw [← sq_abs t]; ring
    _ ≤ t ^ 2 * (ε * (2 * K + 1)) * E ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
        have h1 : e * (e + 2 * K) ≤ ε * (ε + 2 * K) :=
          mul_le_mul he (by linarith) (by positivity) (le_trans he0 he)
        have h2 : ε * (ε + 2 * K) ≤ ε * (2 * K + 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith

/-- **Bounds of the ratio `Kt`** from one overlap pair (pure real inequalities). -/
lemma kt_bounds_pure (q ε Kg CMg cl L0 L1 R0 R1 K : ℝ) (hq : 0 < q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hKg : 0 ≤ Kg)
    (hCM : 0 < CMg) (hcl : 0 < cl) (h4 : 4 * ε * CMg ≤ cl) (hK : 0 ≤ K)
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1)
    (hpL : cl * q ≤ L0 + L1) (hpR : cl * q ≤ R0 + R1)
    (hLR0 : L0 ≤ K * R0 + ε * (1 + K) * (CMg * q)) (hLR1 : L1 ≤ K * R1 + ε * (1 + K) * (CMg * q))
    (hKR0 : K * R0 ≤ L0 + ε * (1 + K) * (CMg * q)) (hKR1 : K * R1 ≤ L1 + ε * (1 + K) * (CMg * q))
    (hR0b : R0 ≤ Kg * (CMg * q)) (hR1b : R1 ≤ Kg * (CMg * q))
    (hL0b : L0 ≤ Kg * (CMg * q)) (hL1b : L1 ≤ Kg * (CMg * q)) :
    cl / (4 * (Kg + 1) * CMg) ≤ K ∧ K ≤ (4 * Kg * CMg + cl) / cl := by
  have hQ : 0 ≤ CMg * q := by positivity
  have hA : 2 * ε * (CMg * q) ≤ (cl / 2) * q := by
    have := mul_le_mul_of_nonneg_right h4 hq.le
    linarith
  have hB : ε * K * (CMg * q) ≤ K * (CMg * q) := by
    have := mul_le_mul_of_nonneg_right hε1 (mul_nonneg hK hQ)
    linarith
  have hKA : K * (2 * ε * (CMg * q)) ≤ K * ((cl / 2) * q) := mul_le_mul_of_nonneg_left hA hK
  constructor
  · -- the lower bound
    have hlow1 : K * R0 + K * R1 ≤ K * (2 * (Kg * (CMg * q))) := by
      have e1 := mul_le_mul_of_nonneg_left hR0b hK
      have e2 := mul_le_mul_of_nonneg_left hR1b hK
      linarith
    have hcl1 : cl * q ≤ K * (2 * (Kg * (CMg * q))) + 2 * ε * (CMg * q) + 2 * (ε * K * (CMg * q)) := by
      linarith
    have hcl2 : cl * q ≤ K * (2 * (Kg * (CMg * q))) + (cl / 2) * q + 2 * (K * (CMg * q)) := by
      linarith
    have hcl3 : (cl / 2) * q ≤ (K * (2 * (Kg + 1) * CMg)) * q := by
      linarith
    have hcl4 : cl / 2 ≤ K * (2 * (Kg + 1) * CMg) := le_of_mul_le_mul_right hcl3 hq
    rw [div_le_iff₀ (by positivity)]
    linarith
  · -- the upper bound
    have hu1 : K * (cl * q) ≤ K * (R0 + R1) := mul_le_mul_of_nonneg_left hpR hK
    have hu2 : K * R0 + K * R1 ≤ 2 * (Kg * (CMg * q)) + 2 * (ε * (1 + K) * (CMg * q)) := by
      linarith
    have hu3 : K * (cl / 2) * q ≤ 2 * Kg * CMg * q + (cl / 2) * q := by
      have e3 : K * (cl * q) = 2 * (K * (cl / 2) * q) := by ring
      have e4 : 2 * (ε * (1 + K) * (CMg * q)) = 2 * ε * (CMg * q) + 2 * (ε * K * (CMg * q)) := by ring
      have e5 : ε * K * (CMg * q) ≤ K * (CMg * q) := hB
      linarith
    have hu4 : K * (cl / 2) ≤ 2 * Kg * CMg + cl / 2 := by
      have : K * (cl / 2) * q ≤ (2 * Kg * CMg + cl / 2) * q := by linarith
      exact le_of_mul_le_mul_right this hq
    rw [le_div_iff₀ hcl]
    linarith

/-- **Left comparison** (pointwise, pure): `psi - ell/nn` against the envelope. -/
lemma left_comp_pure (ψ ℓ a nn EL ε εL Kg Ca : ℝ) (hnn : 0 < nn) (ha : 0 < a) (hε : 0 ≤ ε) (hεL : 0 ≤ εL)
    (hεLe : εL ≤ ε) (hEL : 0 ≤ EL) (hKg : 0 ≤ Kg) (hCa : 0 ≤ Ca)
    (hA : |a * nn - 1| ≤ Ca * ε) (hCaε : Ca * ε ≤ 1) (hψ : |ψ - a * ℓ| ≤ a * (εL * EL))
    (hℓ : |ℓ| ≤ Kg * EL) :
    |ψ - ℓ / nn| ≤ (2 + Kg * Ca) * ε * (EL / nn) := by
  have hAbs := (abs_le.mp hA).2
  have ha2 : a * nn ≤ 2 := by linarith
  have ha2' : a ≤ 2 / nn := by rw [le_div_iff₀ hnn]; linarith
  have h1 : |ψ - a * ℓ| ≤ 2 * ε * (EL / nn) := by
    have e1 : a * (εL * EL) ≤ a * (ε * EL) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεLe hEL) ha.le
    have e2 : a * (ε * EL) ≤ (2 / nn) * (ε * EL) := mul_le_mul_of_nonneg_right ha2' (by positivity)
    have e3 : (2 / nn) * (ε * EL) = 2 * ε * (EL / nn) := by ring
    linarith
  have h2 : |ℓ * ((a * nn - 1) / nn)| ≤ Kg * EL * (Ca * ε) / nn := by
    have e0 : |ℓ * ((a * nn - 1) / nn)| = (|ℓ| * |a * nn - 1|) / nn := by
      rw [abs_mul, abs_div, abs_of_pos hnn]
      ring
    rw [e0]
    apply div_le_div_of_nonneg_right _ hnn.le
    exact mul_le_mul hℓ hA (abs_nonneg _) (by positivity)
  have e : ψ - ℓ / nn = (ψ - a * ℓ) + ℓ * ((a * nn - 1) / nn) := by
    field_simp
    ring
  have e4 : (2 + Kg * Ca) * ε * (EL / nn) = 2 * ε * (EL / nn) + Kg * EL * (Ca * ε) / nn := by
    field_simp
  rw [e]
  calc |(ψ - a * ℓ) + ℓ * ((a * nn - 1) / nn)| ≤ |ψ - a * ℓ| + |ℓ * ((a * nn - 1) / nn)| := abs_add_le _ _
    _ ≤ 2 * ε * (EL / nn) + Kg * EL * (Ca * ε) / nn := add_le_add h1 h2
    _ = (2 + Kg * Ca) * ε * (EL / nn) := e4.symm

/-- Right comparison, pure real form: the eigenvector `psi` against `(kk / nn) * r`, where `kk` is the glued ratio,
`Kt = b / a` is the ratio of the two scales, and `nn` is the glued normaliser. -/
lemma right_comp_pure (ψ r a Kt kk nn ER ε εR Kg Ca CKu Cκe Cr : ℝ) (hnn : 0 < nn) (ha : 0 < a)
    (hε : 0 ≤ ε) (hεR : 0 ≤ εR) (hεRe : εR ≤ ε) (hER : 0 ≤ ER) (hKg : 0 ≤ Kg) (hCa : 0 ≤ Ca)
    (hCKu : 0 ≤ CKu) (hCκe : 0 ≤ Cκe) (hKt : |Kt| ≤ CKu) (hCaε : Ca * ε ≤ 1)
    (hA : |a * nn - 1| ≤ Ca * ε) (hκ : |kk - Kt| ≤ Cκe * ε * (1 + |Kt|))
    (hψ : |ψ - Kt * a * r| ≤ |Kt * a| * (εR * ER)) (hr : |r| ≤ Kg * ER)
    (hCr : Cr = 2 * CKu + Kg * (CKu * Ca + Cκe * (1 + CKu))) :
    |ψ - kk * r / nn| ≤ Cr * ε * (ER / nn) := by
  have hnz : nn ≠ 0 := hnn.ne'
  have ha2 : a * nn ≤ 2 := by linarith [(abs_le.mp hA).2]
  have ha2' : a ≤ 2 / nn := by rw [le_div_iff₀ hnn]; exact ha2
  have e1 : Kt * a - kk / nn = Kt * (a * nn - 1) / nn - (kk - Kt) / nn := by
    field_simp <;> ring
  have hA1 : |Kt * (a * nn - 1) / nn| ≤ CKu * (Ca * ε) / nn := by
    rw [abs_div, abs_mul, abs_of_pos hnn]
    apply div_le_div_of_nonneg_right _ hnn.le
    exact mul_le_mul hKt hA (abs_nonneg _) hCKu
  have hB1 : |(kk - Kt) / nn| ≤ Cκe * ε * (1 + CKu) / nn := by
    rw [abs_div, abs_of_pos hnn]
    apply div_le_div_of_nonneg_right _ hnn.le
    have h1 : 1 + |Kt| ≤ 1 + CKu := by linarith
    exact hκ.trans (mul_le_mul_of_nonneg_left h1 (mul_nonneg hCκe hε))
  have hdiff : |Kt * a - kk / nn| ≤ CKu * (Ca * ε) / nn + Cκe * ε * (1 + CKu) / nn := by
    rw [e1]
    have h := abs_add_le (Kt * (a * nn - 1) / nn) (-((kk - Kt) / nn))
    rw [abs_neg, ← sub_eq_add_neg] at h
    linarith [h, hA1, hB1]
  have hψ1 : |Kt * a| * (εR * ER) ≤ CKu * a * (ε * ER) := by
    have h1 : |Kt * a| * (εR * ER) ≤ |Kt * a| * (ε * ER) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεRe hER) (abs_nonneg _)
    have h2 : |Kt * a| = |Kt| * a := by rw [abs_mul, abs_of_pos ha]
    have h3 : |Kt| * a ≤ CKu * a := mul_le_mul_of_nonneg_right hKt ha.le
    have h4 : |Kt * a| * (ε * ER) ≤ CKu * a * (ε * ER) := by
      rw [h2]; exact mul_le_mul_of_nonneg_right h3 (mul_nonneg hε hER)
    linarith [h1, h4]
  have hψ2 : |ψ - Kt * a * r| ≤ 2 * CKu * ε * (ER / nn) := by
    have h5 : CKu * a * (ε * ER) ≤ CKu * (2 / nn) * (ε * ER) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha2' hCKu) (mul_nonneg hε hER)
    have e5 : CKu * (2 / nn) * (ε * ER) = 2 * CKu * ε * (ER / nn) := by ring
    linarith [hψ, hψ1, h5, e5]
  have hterm : |Kt * a - kk / nn| * |r| ≤ Kg * (CKu * Ca + Cκe * (1 + CKu)) * ε * (ER / nn) := by
    have hnonneg : 0 ≤ CKu * (Ca * ε) / nn + Cκe * ε * (1 + CKu) / nn :=
      add_nonneg (div_nonneg (mul_nonneg hCKu (mul_nonneg hCa hε)) hnn.le)
        (div_nonneg (mul_nonneg (mul_nonneg hCκe hε) (by linarith)) hnn.le)
    have h6 := mul_le_mul hdiff hr (abs_nonneg _) hnonneg
    have e6 : (CKu * (Ca * ε) / nn + Cκe * ε * (1 + CKu) / nn) * (Kg * ER)
        = Kg * (CKu * Ca + Cκe * (1 + CKu)) * ε * (ER / nn) := by ring
    linarith [h6, e6]
  have e2 : ψ - kk * r / nn = (ψ - Kt * a * r) + (Kt * a - kk / nn) * r := by ring
  have hsplit : |ψ - kk * r / nn| ≤ |ψ - Kt * a * r| + |Kt * a - kk / nn| * |r| := by
    have h7 := abs_add_le (ψ - Kt * a * r) ((Kt * a - kk / nn) * r)
    rw [abs_mul] at h7
    rw [e2]; exact h7
  have e7 : Cr * ε * (ER / nn)
      = 2 * CKu * ε * (ER / nn) + Kg * (CKu * Ca + Cκe * (1 + CKu)) * ε * (ER / nn) := by
    rw [hCr]; ring
  linarith [hsplit, hψ2, hterm, e7]

/-- Final comparison on the left rows: a bound `d <= (2 + Kg Ca) eps W` with `eps = Cε h^m` gives `d <= Cc h^m W`. -/
lemma final_left (d Kg Ca Cr cK Cε hm ε W Cc : ℝ) (hε : ε = Cε * hm)
    (hcc : Cc = (2 + Kg * Ca + 2 * Cr / cK) * Cε) (hW : 0 ≤ W) (hCε : 0 ≤ Cε) (hhm : 0 ≤ hm)
    (hCr : 0 ≤ Cr) (hcK : 0 < cK) (hKg : 0 ≤ Kg) (hCa : 0 ≤ Ca)
    (hd : d ≤ (2 + Kg * Ca) * ε * W) : d ≤ Cc * hm * W := by
  have hX : 0 ≤ Cε * hm * W := mul_nonneg (mul_nonneg hCε hhm) hW
  have h2 : 0 ≤ 2 * Cr / cK := div_nonneg (by linarith) hcK.le
  have hR : Cc * hm * W = (2 + Kg * Ca) * (Cε * hm * W) + (2 * Cr / cK) * (Cε * hm * W) := by
    rw [hcc]; ring
  have hL : (2 + Kg * Ca) * ε * W = (2 + Kg * Ca) * (Cε * hm * W) := by rw [hε]; ring
  have h3 : 0 ≤ (2 * Cr / cK) * (Cε * hm * W) := mul_nonneg h2 hX
  linarith [hd, hL, hR, h3]

/-- Final comparison on the right rows: a bound `d <= Cr eps W` with `eps = Cε h^m` and `cK/2 <= K`
gives `d <= Cc h^m (K W)`. -/
lemma final_right (d Cr cK Cε hm Kg Ca Cc K W ε : ℝ) (hCr : 0 ≤ Cr) (hcK : 0 < cK) (hK : cK / 2 ≤ K)
    (hW : 0 ≤ W) (hε : ε = Cε * hm) (hCε : 0 ≤ Cε) (hhm : 0 ≤ hm)
    (hcc : Cc = (2 + Kg * Ca + 2 * Cr / cK) * Cε) (hKg : 0 ≤ Kg) (hCa : 0 ≤ Ca)
    (hd : d ≤ Cr * ε * W) : d ≤ Cc * hm * (K * W) := by
  have hK0 : 0 ≤ K := by linarith
  have hX : 0 ≤ Cε * hm * W := mul_nonneg (mul_nonneg hCε hhm) hW
  have h2 : 0 ≤ 2 * Cr / cK := div_nonneg (by linarith) hcK.le
  have e : 2 * Cr / cK * (cK / 2) = Cr * (cK / cK) := by ring
  rw [div_self hcK.ne', mul_one] at e
  have h1 : Cr ≤ 2 * Cr / cK * K := by
    have := mul_le_mul_of_nonneg_left hK h2
    linarith [e]
  have hR : Cc * hm * (K * W) = (2 + Kg * Ca) * K * (Cε * hm * W) + (2 * Cr / cK) * K * (Cε * hm * W) := by
    rw [hcc]; ring
  have hL : Cr * ε * W = Cr * (Cε * hm * W) := by rw [hε]; ring
  have h2' : Cr * (Cε * hm * W) ≤ (2 * Cr / cK * K) * (Cε * hm * W) :=
    mul_le_mul_of_nonneg_right h1 hX
  have h3 : 0 ≤ (2 + Kg * Ca) * K * (Cε * hm * W) :=
    mul_nonneg (mul_nonneg (by linarith [mul_nonneg hKg hCa]) hK0) hX
  linarith [hd, hL, hR, h2', h3]

/-- **Conjunct 1 of `PropThaW`** (bulk normalisation, the kappa bounds, and the eigenvector comparison). -/
theorem bulk_conj1 {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ Cc h0 cN CN cκ Cκ : ℝ, 0 < h0 ∧ 0 < cN ∧ 0 < cκ ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ,
      max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      0 < bulkNorm CL CR p X N ∧
      cN * Fz.step N ^ (-(1 : ℝ) / 4) ≤ bulkNorm CL CR p X N ∧ bulkNorm CL CR p X N ≤ CN * Fz.step N ^ (-(1 : ℝ) / 4) ∧
      |bulkKappa CL CR p X N| ≤ Cκ ∧
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → cκ ≤ |bulkKappa CL CR p X N| ∧ ∀ n ∈ rowsOf N,
          |eigVec Um k n - bulkVec CL CR p X N n| ≤ Cc * Fz.step N ^ m * bulkEnv CL CR p X N n := by
  obtain ⟨hPc, hEK, -⟩ := hr
  obtain ⟨CAe, hCAe0, hCAe⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
  have hBL' := bulkSolutionBound_of_one_le CL hm
  have hBR' := bulkSolutionBound_of_one_le CR hm
  unfold BulkSolutionBound at hBL' hBR'
  obtain ⟨CcL, h0L, hh0L, hBL⟩ := hBL'
  obtain ⟨CcR, h0R, hh0R, hBR⟩ := hBR'
  obtain ⟨hc'L, hc'cL, hσL, hcσL, -, hcML, hcMCML, hc3L, hCsumL, -⟩ := CL.consts_pos
  obtain ⟨hc'R, hc'cR, hσR, hcσR, -, hcMR, hcMCMR, hc3R, hCsumR, -⟩ := CR.consts_pos
  have hcoupc : CR.c - CR.c' = CL.c - CL.c' := by rw [hcoup.1, hcoup.2]; ring
  -- constants
  obtain ⟨KL, hKL⟩ : ∃ x : ℝ, x = (CL.cs.KA + CL.cs.KB) * CL.cs.Kw := ⟨_, rfl⟩
  obtain ⟨KR, hKR⟩ : ∃ x : ℝ, x = (CR.cs.KA + CR.cs.KB) * CR.cs.Kw := ⟨_, rfl⟩
  have hKL0 : 0 ≤ KL := by
    rw [hKL]; exact mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg
  have hKR0 : 0 ≤ KR := by
    rw [hKR]; exact mul_nonneg (add_nonneg CR.cs.KA_nonneg CR.cs.KB_nonneg) CR.cs.Kw_nonneg
  obtain ⟨Kg, hKg⟩ : ∃ x : ℝ, x = KL + KR + 1 := ⟨_, rfl⟩
  have hKg0 : 0 < Kg := by rw [hKg]; linarith
  have hKgL : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw ≤ Kg := by rw [hKg, ← hKL]; linarith
  have hKgR : (CR.cs.KA + CR.cs.KB) * CR.cs.Kw ≤ Kg := by rw [hKg, ← hKR]; linarith
  obtain ⟨CEg, hCEg⟩ : ∃ x : ℝ, x = |CL.cs.CE| + |CR.cs.CE| + 1 := ⟨_, rfl⟩
  have hCEg0 : 0 < CEg := by
    rw [hCEg]; have := abs_nonneg CL.cs.CE; have := abs_nonneg CR.cs.CE; linarith
  have hCEgL : CL.cs.CE ≤ CEg := by rw [hCEg]; linarith [le_abs_self CL.cs.CE, abs_nonneg CR.cs.CE]
  have hCEgR : CR.cs.CE ≤ CEg := by rw [hCEg]; linarith [le_abs_self CR.cs.CE, abs_nonneg CL.cs.CE]
  obtain ⟨CMg, hCMg⟩ : ∃ x : ℝ, x = CL.CM + CR.CM + 1 := ⟨_, rfl⟩
  have hCMg0 : 0 < CMg := by rw [hCMg]; linarith [hcMCML, hcMCMR, hcML, hcMR]
  have hCMgL : CL.CM ≤ CMg := by rw [hCMg]; linarith [hcMCML, hcMCMR, hcML, hcMR]
  have hCMgR : CR.CM ≤ CMg := by rw [hCMg]; linarith [hcMCML, hcMCMR, hcML, hcMR]
  obtain ⟨cmg, hcmg⟩ : ∃ x : ℝ, x = min CL.cs.cm CR.cs.cm := ⟨_, rfl⟩
  have hcmg0 : 0 < cmg := by rw [hcmg]; exact lt_min CL.cs.cm_pos CR.cs.cm_pos
  have hcmgL : cmg ≤ CL.cs.cm := by rw [hcmg]; exact min_le_left _ _
  have hcmgR : cmg ≤ CR.cs.cm := by rw [hcmg]; exact min_le_right _ _
  obtain ⟨Csg, hCsg⟩ : ∃ x : ℝ, x = CL.Csum + CR.Csum + 1 := ⟨_, rfl⟩
  have hCsg0 : 0 < Csg := by rw [hCsg]; linarith
  have hCsgL : CL.Csum ≤ Csg := by rw [hCsg]; linarith
  have hCsgR : CR.Csum ≤ Csg := by rw [hCsg]; linarith
  obtain ⟨CAg, hCAg⟩ : ∃ x : ℝ, x = CAe + 1 := ⟨_, rfl⟩
  have hCAg0 : 0 < CAg := by rw [hCAg]; linarith
  obtain ⟨cl, hcl⟩ : ∃ x : ℝ, x = cmg / (CAg * Kg * CMg) := ⟨_, rfl⟩
  have hcl0 : 0 < cl := by rw [hcl]; positivity
  obtain ⟨CE2, hCE2⟩ : ∃ x : ℝ, x = CEg ^ 2 * (Csg + CMg ^ 2) := ⟨_, rfl⟩
  have hCE20 : 0 < CE2 := by rw [hCE2]; positivity
  obtain ⟨CT, hCT⟩ : ∃ x : ℝ, x = Kg ^ 2 * CE2 := ⟨_, rfl⟩
  have hCT0 : 0 < CT := by rw [hCT]; positivity
  obtain ⟨Cenv, hCenv⟩ : ∃ x : ℝ, x = (2 * Kg + 1) * CE2 := ⟨_, rfl⟩
  have hCenv0 : 0 < Cenv := by rw [hCenv]; positivity
  obtain ⟨cΩ, hcΩ⟩ : ∃ x : ℝ, x = (CL.c - CL.c') * cl ^ 2 / 8 := ⟨_, rfl⟩
  have hD0 : 0 < CL.c - CL.c' := by linarith
  have hcΩ0 : 0 < cΩ := by rw [hcΩ]; positivity
  obtain ⟨CKu, hCKu⟩ : ∃ x : ℝ, x = (4 * Kg * CMg + cl) / cl := ⟨_, rfl⟩
  have hCKu0 : 0 < CKu := by rw [hCKu]; positivity
  obtain ⟨cK, hcK⟩ : ∃ x : ℝ, x = cl / (4 * (Kg + 1) * CMg) := ⟨_, rfl⟩
  have hcK0 : 0 < cK := by rw [hcK]; positivity
  obtain ⟨Cκe, hCκe⟩ : ∃ x : ℝ, x = Fz.L * Kg * CMg ^ 2 / cΩ := ⟨_, rfl⟩
  have hFL0 : 0 < Fz.L := Fz.L_pos
  have hCκe0 : 0 < Cκe := by rw [hCκe]; positivity
  obtain ⟨Cκall, hCκall⟩ : ∃ x : ℝ, x = Fz.L * Kg ^ 2 * CMg ^ 2 / cΩ := ⟨_, rfl⟩
  have hCκall0 : 0 < Cκall := by rw [hCκall]; positivity
  obtain ⟨Ca, hCa⟩ : ∃ x : ℝ, x = (2 / cΩ) * (Cκe * (1 + CKu) * ((CKu + Cκe * (1 + CKu)) + CKu) * CT
      + (1 + CKu ^ 2) * Cenv) := ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  obtain ⟨Cε, hCε⟩ : ∃ x : ℝ, x = |CcL| + |CcR| + 1 := ⟨_, rfl⟩
  have hCε0 : 0 < Cε := by rw [hCε]; positivity
  obtain ⟨εs, hεs⟩ : ∃ x : ℝ, x = min (min 1 (cl / (4 * CMg)))
      (min (min (cΩ / (2 * (1 + CKu ^ 2) * Cenv)) (cK / (2 * Cκe * (1 + CKu)))) (1 / (Ca + 1))) := ⟨_, rfl⟩
  have hεs0 : 0 < εs := by
    rw [hεs]
    exact lt_min (lt_min one_pos (by positivity))
      (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  have hεs1 : εs ≤ 1 := by rw [hεs]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hεs_pair : εs ≤ cl / (4 * CMg) := by rw [hεs]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεs_Ω : εs ≤ cΩ / (2 * (1 + CKu ^ 2) * Cenv) := by
    rw [hεs]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεs_K : εs ≤ cK / (2 * Cκe * (1 + CKu)) := by
    rw [hεs]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεs_Ca : εs ≤ 1 / (Ca + 1) := by rw [hεs]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hdiv : ∀ x y z : ℝ, 0 < z → x ≤ y / z → x * z ≤ y := fun x y z hz hx => (le_div_iff₀ hz).mp hx
  have hsm_pair : εs * (4 * CMg) ≤ cl := hdiv _ _ _ (by positivity) hεs_pair
  have hsm_Ω : εs * (2 * (1 + CKu ^ 2) * Cenv) ≤ cΩ := hdiv _ _ _ (by positivity) hεs_Ω
  have hsm_K : εs * (2 * Cκe * (1 + CKu)) ≤ cK := hdiv _ _ _ (by positivity) hεs_K
  have hsm_Ca : εs * (Ca + 1) ≤ 1 := hdiv _ _ _ (by positivity) hεs_Ca
  have hsm1 : (1 + CKu ^ 2) * Cenv * εs ≤ cΩ / 2 := by
    have e : (1 + CKu ^ 2) * Cenv * εs = (εs * (2 * (1 + CKu ^ 2) * Cenv)) / 2 := by ring
    rw [e]; linarith
  have hsm2 : Cκe * εs * (1 + CKu) ≤ cK / 2 := by
    have e : Cκe * εs * (1 + CKu) = (εs * (2 * Cκe * (1 + CKu))) / 2 := by ring
    rw [e]; linarith
  obtain ⟨h1, hh1⟩ : ∃ x : ℝ, x = min (min (min h0L h0R) (min ((CL.c - CL.c') / 6) CL.σ)) (min 1 (εs / Cε)) :=
    ⟨_, rfl⟩
  have hh10 : 0 < h1 := by
    rw [hh1]
    exact lt_min (lt_min (lt_min hh0L hh0R) (lt_min (by positivity) hσL)) (lt_min one_pos (by positivity))
  have hh1_L : h1 ≤ h0L := by rw [hh1]; exact ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hh1_R : h1 ≤ h0R := by rw [hh1]; exact ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hh1_d : h1 ≤ (CL.c - CL.c') / 6 := by
    rw [hh1]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1_σ : h1 ≤ CL.σ := by
    rw [hh1]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh1_one : h1 ≤ 1 := by rw [hh1]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hh1_ε : h1 ≤ εs / Cε := by rw [hh1]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cr, hCr⟩ : ∃ x : ℝ, x = 2 * CKu + Kg * (CKu * Ca + Cκe * (1 + CKu)) := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ x : ℝ, x = (2 + Kg * Ca + 2 * Cr / cK) * Cε := ⟨_, rfl⟩
  refine ⟨Cc, h1, Real.sqrt cΩ, Real.sqrt (CT + Cκall ^ 2 * CT), cK / 2, Cκall, hh10,
    Real.sqrt_pos.mpr hcΩ0, by positivity, ?_⟩
  intro p hp X hX N hN hstepN
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  set h := Fz.step N with hhdef
  have hst : 0 < h := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : h * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hh_le1 : h ≤ 1 := hstepN.trans hh1_one
  have hhcL : h ≤ CL.c - CL.c' := by linarith only [hstepN, hh1_d, hD0]
  have hhcR : h ≤ CR.c - CR.c' := by rw [hcoupc]; exact hhcL
  have hcL : CL.c + h ≤ Fz.L := by linarith only [hstepN, hh1_σ, hcσL]
  -- the bond bound
  have hA_L : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CAg := by
    intro j hj0 hjN
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact (hCAe p hp N j).trans (by rw [hCAg]; exact le_add_of_nonneg_right zero_le_one)
  have hA_R : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CAg := by
    intro j hj0 hjN
    rw [CR.A_bond p hp X hX N hN2 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), bondA_mirror]
    exact (hCAe p hp N _).trans (by rw [hCAg]; exact le_add_of_nonneg_right zero_le_one)
  -- the chart facts of both charts
  obtain ⟨LA, LB, LC, LD, LE⟩ := chart_side_facts CL p hp X hX N hN1 hhcL Kg CEg CMg cmg Csg CAg hKg0 hCEg0 hCMg0
    hcmg0 hCAg0 hKgL hCEgL hCMgL hcmgL hCsgL hA_L
  obtain ⟨RA, RB, RC, RD, RE⟩ := chart_side_facts CR p hp X hX N hN2 hhcR Kg CEg CMg cmg Csg CAg hKg0 hCEg0 hCMg0
    hcmg0 hCAg0 hKgR hCEgR hCMgR hcmgR hCsgR hA_R
  obtain ⟨hq2, hq0⟩ := fourth_root_sq h hst
  set q : ℝ := h ^ ((1 : ℝ) / 4) with hqdef
  have hq4 : q ^ 4 = h := by
    have e : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [e, hq2, Real.sq_sqrt hst.le]
  have hq2sq : q ^ 2 * q ^ 2 ≤ 1 := by
    have e : q ^ 2 * q ^ 2 = q ^ 4 := by ring
    rw [e, hq4]; exact hh_le1
  -- the overlap pairs
  obtain ⟨S, hSprop, hScard⟩ := count_pairs h Fz.L CL.c' CL.c N hst hLs hc'L hc'cL hcL
  have hSmall : (CL.c - CL.c') / (2 * h) ≤ (S.card : ℝ) := by
    have h6 : 6 ≤ (CL.c - CL.c') / h := by rw [le_div_iff₀ hst]; linarith only [hh1_d, hstepN]
    have e : (CL.c - CL.c') / (2 * h) = ((CL.c - CL.c') / h) / 2 := by rw [div_div, mul_comm]
    rw [e]; linarith only [hScard, h6]
  have hPL : ∀ n ∈ S, cl * q ≤ |CL.psiHatL p X N n| + |CL.psiHatL p X N (n + 1)| := by
    intro n hn
    obtain ⟨hn0, hn1, hc1, hc2⟩ := hSprop n hn
    have hk := LE n hn0 (le_NR_of CL p hp X hX N hN1 hst (n + 1) hc2) hc1 hc2
    rw [hcl, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith only [hk]
  have hPR : ∀ n ∈ S, cl * q ≤ |CR.psiHatL p X N ((N : ℤ) - (n + 1))| + |CR.psiHatL p X N ((N : ℤ) - n)| := by
    intro n hn
    obtain ⟨hn0, hn1, hc1, hc2⟩ := hSprop n hn
    have hm1 : uNode h ((N : ℤ) - n) = Fz.L - uNode h n := uNode_mirror Fz.L h N n hLs
    have hm2 : uNode h ((N : ℤ) - (n + 1)) = Fz.L - uNode h (n + 1) := uNode_mirror Fz.L h N (n + 1) hLs
    have e : (N : ℤ) - (n + 1) + 1 = (N : ℤ) - n := by ring
    have hj1 : (N : ℤ) - n ≤ (CR.chain p X N).NR :=
      le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) (show uNode h ((N : ℤ) - n) ≤ CR.c by
        rw [hm1]; linarith only [hcoup.1, hc1])
    have hRE' := RE ((N : ℤ) - (n + 1)) (by omega) (by omega)
      (show CR.c' ≤ uNode h ((N : ℤ) - (n + 1)) by rw [hm2]; linarith only [hcoup.2, hc2])
      (show uNode h ((N : ℤ) - (n + 1) + 1) ≤ CR.c by rw [e, hm1]; linarith only [hcoup.1, hc1])
    rw [e] at hRE'
    have hRE2 : cmg * q ≤ CAg * Kg * CMg * (|CR.psiHatL p X N ((N : ℤ) - (n + 1))| + |CR.psiHatL p X N ((N : ℤ) - n)|) :=
      hRE'
    rw [hcl, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith only [hRE2]
  -- the overlap window
  have hmemΩ : ∀ n : ℤ, n ∈ bulkWindow CL N ↔ (n ∈ rowsOf N ∧ CL.c' ≤ uNode h n ∧ uNode h n ≤ CL.c) := by
    intro n
    unfold bulkWindow
    exact Finset.mem_filter
  have hmemR : ∀ n : ℤ, n ∈ rowsOf N ↔ 0 ≤ n ∧ n ≤ (N : ℤ) := by
    intro n
    unfold rowsOf
    exact Finset.mem_Icc
  have hSΩ : ∀ n ∈ S, n ∈ bulkWindow CL N ∧ n + 1 ∈ bulkWindow CL N := by
    intro n hn
    obtain ⟨hn0, hn1, hc1, hc2⟩ := hSprop n hn
    have hle : uNode h n ≤ uNode h (n + 1) := uNode_le_of_le hst.le (by omega)
    exact ⟨(hmemΩ n).mpr ⟨(hmemR n).mpr ⟨hn0, by omega⟩, hc1, by linarith only [hle, hc2]⟩,
      (hmemΩ (n + 1)).mpr ⟨(hmemR (n + 1)).mpr ⟨by omega, hn1⟩, by linarith only [hle, hc1], hc2⟩⟩
  -- the left overlap sum
  have hΩℓ : cΩ / q ^ 2 ≤ ∑ m ∈ bulkWindow CL N, CL.psiHatL p X N m ^ 2 := by
    have hov := overlap_sum_lower (fun n => CL.psiHatL p X N n) (bulkWindow CL N) S (cl * q)
      (by positivity) hSΩ hPL
    have hov' : (S.card : ℝ) * (cl * q) ^ 2 ≤ 4 * ∑ m ∈ bulkWindow CL N, CL.psiHatL p X N m ^ 2 := hov
    have hk1 : (CL.c - CL.c') / (2 * h) * (cl * q) ^ 2 ≤ (S.card : ℝ) * (cl * q) ^ 2 :=
      mul_le_mul_of_nonneg_right hSmall (sq_nonneg _)
    have e : (CL.c - CL.c') / (2 * h) * (cl * q) ^ 2 = (CL.c - CL.c') * cl ^ 2 / (2 * q ^ 2) := by
      rw [← hq4]; field_simp
    have e2 : cΩ / q ^ 2 = (CL.c - CL.c') * cl ^ 2 / (2 * q ^ 2) / 4 := by
      rw [hcΩ]; field_simp; ring
    rw [e2]
    linarith only [hk1, e, hov']
  -- the right overlap sum
  have hΩr : cΩ / q ^ 2 ≤ ∑ m ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - m) ^ 2 := by
    have hpair' : ∀ n ∈ S, cl * q ≤ |(fun n : ℤ => CR.psiHatL p X N ((N : ℤ) - n)) n|
        + |(fun n : ℤ => CR.psiHatL p X N ((N : ℤ) - n)) (n + 1)| := by
      intro n hn
      have := hPR n hn
      simp only
      linarith only [this]

    have hov := overlap_sum_lower (fun n : ℤ => CR.psiHatL p X N ((N : ℤ) - n)) (bulkWindow CL N) S (cl * q)
      (by positivity) hSΩ hpair'
    have hov' : (S.card : ℝ) * (cl * q) ^ 2 ≤ 4 * ∑ m ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - m) ^ 2 := hov
    have hk1 : (CL.c - CL.c') / (2 * h) * (cl * q) ^ 2 ≤ (S.card : ℝ) * (cl * q) ^ 2 :=
      mul_le_mul_of_nonneg_right hSmall (sq_nonneg _)
    have e : (CL.c - CL.c') / (2 * h) * (cl * q) ^ 2 = (CL.c - CL.c') * cl ^ 2 / (2 * q ^ 2) := by
      rw [← hq4]; field_simp
    have e2 : cΩ / q ^ 2 = (CL.c - CL.c') * cl ^ 2 / (2 * q ^ 2) / 4 := by
      rw [hcΩ]; field_simp; ring
    rw [e2]
    linarith only [hk1, e, hov']
  -- the envelope sums on the rows of each chart
  have hELsum : ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, CL.envL p X N j ^ 2 ≤ CE2 / q ^ 2 := by
    have hh := LC
    rw [← hq2] at hh
    rw [hCE2]
    exact sum_env_CE2 _ CEg Csg CMg q hq0 hq2sq hh
  have hERsum : ∑ j ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, CR.envL p X N j ^ 2 ≤ CE2 / q ^ 2 := by
    have hh := RC
    rw [show (mirrorFamily Fz).step N = h from rfl, ← hq2] at hh
    rw [hCE2]
    exact sum_env_CE2 _ CEg Csg CMg q hq0 hq2sq hh
  -- the left and right sums of the normaliser
  have hTLup : ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.psiHatL p X N n ^ 2 ≤ CT / q ^ 2 := by
    have h1 : ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.psiHatL p X N n ^ 2
        ≤ ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), (Kg * CL.envL p X N n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, -⟩ := (hmemR n).mp hnr
      have hle := LA n hn0 (le_NR_of CL p hp X hX N hN1 hst n hc)
      calc CL.psiHatL p X N n ^ 2 = |CL.psiHatL p X N n| ^ 2 := (sq_abs _).symm
        _ ≤ (Kg * CL.envL p X N n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    have h2 : ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), (Kg * CL.envL p X N n) ^ 2
        ≤ ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, (Kg * CL.envL p X N j) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn0, -⟩ := (hmemR n).mp hnr
        exact Finset.mem_Icc.mpr ⟨hn0, le_NR_of CL p hp X hX N hN1 hst n hc⟩
      · intro j _ _
        positivity
    have h3 : ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, (Kg * CL.envL p X N j) ^ 2
        = Kg ^ 2 * ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, CL.envL p X N j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h4 : Kg ^ 2 * ∑ j ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR, CL.envL p X N j ^ 2 ≤ Kg ^ 2 * (CE2 / q ^ 2) :=
      mul_le_mul_of_nonneg_left hELsum (sq_nonneg _)
    have e : CT / q ^ 2 = Kg ^ 2 * (CE2 / q ^ 2) := by rw [hCT]; ring
    linarith only [h1, h2, h3, h4, e]
  have hSRup : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), CR.psiHatL p X N ((N : ℤ) - n) ^ 2
      ≤ CT / q ^ 2 := by
    have h1 : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), CR.psiHatL p X N ((N : ℤ) - n) ^ 2
        ≤ ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            (fun k : ℤ => Kg ^ 2 * CR.envL p X N k ^ 2) ((N : ℤ) - n) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, hnN⟩ := (hmemR n).mp hnr
      have hcn : CL.c < uNode h n := lt_of_not_ge hc
      have hlow : uNode h ((N : ℤ) - n) ≤ CR.c := by
        rw [uNode_mirror Fz.L h N n hLs, hcoup.1]
        linarith only [hc'cL, hcn]
      have hle := RA ((N : ℤ) - n) (by omega) (le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hlow)
      show CR.psiHatL p X N ((N : ℤ) - n) ^ 2 ≤ Kg ^ 2 * CR.envL p X N ((N : ℤ) - n) ^ 2
      calc CR.psiHatL p X N ((N : ℤ) - n) ^ 2 = |CR.psiHatL p X N ((N : ℤ) - n)| ^ 2 := (sq_abs _).symm
        _ ≤ (Kg * CR.envL p X N ((N : ℤ) - n)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
        _ = Kg ^ 2 * CR.envL p X N ((N : ℤ) - n) ^ 2 := by ring
    have hS' : ∀ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
        (N : ℤ) - n ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR := by
      intro n hn
      obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, hnN⟩ := (hmemR n).mp hnr
      have hcn : CL.c < uNode h n := lt_of_not_ge hc
      have hlow : uNode h ((N : ℤ) - n) ≤ CR.c := by
        rw [uNode_mirror Fz.L h N n hLs, hcoup.1]
        linarith only [hc'cL, hcn]
      exact Finset.mem_Icc.mpr ⟨by omega, le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hlow⟩
    have hinj' : Set.InjOn (fun n : ℤ => (N : ℤ) - n) ↑((rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c)) := by
      intro a _ b _ hab
      simp only at hab
      omega
    have h2 : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            (fun k : ℤ => Kg ^ 2 * CR.envL p X N k ^ 2) ((N : ℤ) - n)
        ≤ ∑ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, (fun k : ℤ => Kg ^ 2 * CR.envL p X N k ^ 2) k :=
      sum_reflect_le N _ _ (fun k : ℤ => Kg ^ 2 * CR.envL p X N k ^ 2) (fun k => by positivity) hS' hinj'
    have h3 : ∑ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, (fun k : ℤ => Kg ^ 2 * CR.envL p X N k ^ 2) k
        = Kg ^ 2 * ∑ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, CR.envL p X N k ^ 2 := by
      rw [Finset.mul_sum]
    have h4 : Kg ^ 2 * ∑ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, CR.envL p X N k ^ 2 ≤ Kg ^ 2 * (CE2 / q ^ 2) :=
      mul_le_mul_of_nonneg_left hERsum (sq_nonneg _)
    have e : CT / q ^ 2 = Kg ^ 2 * (CE2 / q ^ 2) := by rw [hCT]; ring
    linarith only [h1, h2, h3, h4, e]
  -- the bulk normaliser as a function of the glued coefficient
  have hκdef : bulkKappa CL CR p X N = (∑ n ∈ bulkWindow CL N, CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n))
      / (∑ n ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - n) ^ 2) := rfl
  have hnorm : bulkNorm CL CR p X N = Real.sqrt ((∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.psiHatL p X N n ^ 2)
      + bulkKappa CL CR p X N ^ 2 * (∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
          CR.psiHatL p X N ((N : ℤ) - n) ^ 2)) := by
    unfold bulkNorm glueNorm
    rfl
  have hTLlow : cΩ / q ^ 2 ≤ ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.psiHatL p X N n ^ 2 := by
    refine hΩℓ.trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hmem, -, hc⟩ := (hmemΩ n).mp hn
      exact Finset.mem_filter.mpr ⟨hmem, hc⟩
    · intro j _ _
      positivity
  have hSRnn : 0 ≤ ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), CR.psiHatL p X N ((N : ℤ) - n) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN1' : ((N : ℝ) + 1) * q ^ 4 = Fz.L := by
    rw [hq4, mul_comm]
    exact hLs
  -- the glued coefficient is bounded uniformly in `X`
  have hΩbd : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n| ≤ Kg * (CMg * q) ∧
      |CR.psiHatL p X N ((N : ℤ) - n)| ≤ Kg * (CMg * q) := by
    intro n hn
    obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ n).mp hn
    obtain ⟨hn0, hnN⟩ := (hmemR n).mp hmem
    have hL := LA n hn0 (le_NR_of CL p hp X hX N hN1 hst n hc2)
    have hD := LD n hn0 (le_NR_of CL p hp X hX N hN1 hst n hc2) hc1
    have hlowR : uNode h ((N : ℤ) - n) ≤ CR.c := by
      rw [uNode_mirror Fz.L h N n hLs, hcoup.1]
      linarith only [hc1]
    have hhigh : CR.c' ≤ uNode h ((N : ℤ) - n) := by
      rw [uNode_mirror Fz.L h N n hLs, hcoup.2]
      linarith only [hc2]
    have hj := le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hlowR
    have hRA' := RA ((N : ℤ) - n) (by omega) hj
    have hRD' := RD ((N : ℤ) - n) (by omega) hj hhigh
    exact ⟨(hL.trans (mul_le_mul_of_nonneg_left hD hKg0.le)), hRA'.trans (mul_le_mul_of_nonneg_left hRD' hKg0.le)⟩
  have hκ_all : |bulkKappa CL CR p X N| ≤ Cκall := by
    rw [hκdef]
    have hSΩpos : 0 < cΩ / q ^ 2 := by positivity
    have hSΩ' := hΩr
    have hXbd : |∑ n ∈ bulkWindow CL N, CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n)|
        ≤ ((N : ℝ) + 1) * (Kg * (CMg * q)) ^ 2 := by
      have h1 := Finset.abs_sum_le_sum_abs (fun n => CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n))
        (bulkWindow CL N)
      have h2 : ∑ n ∈ bulkWindow CL N, |CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n)|
          ≤ ∑ n ∈ bulkWindow CL N, (Kg * (CMg * q)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨h1', h2'⟩ := hΩbd n hn
        rw [abs_mul]
        calc |CL.psiHatL p X N n| * |CR.psiHatL p X N ((N : ℤ) - n)|
            ≤ (Kg * (CMg * q)) * (Kg * (CMg * q)) :=
              mul_le_mul h1' h2' (abs_nonneg _) (by positivity)
          _ = (Kg * (CMg * q)) ^ 2 := by ring
      have h3 : ∑ n ∈ bulkWindow CL N, (Kg * (CMg * q)) ^ 2 = ((bulkWindow CL N).card : ℝ) * (Kg * (CMg * q)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hcardN : (bulkWindow CL N).card ≤ N + 1 := by
        have hr : (rowsOf N).card = N + 1 := by
          unfold rowsOf
          simp
        rw [← hr]
        exact Finset.card_le_card (fun n hn => ((hmemΩ n).mp hn).1)
      have hcardR : ((bulkWindow CL N).card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcardN
      have h4 : ((bulkWindow CL N).card : ℝ) * (Kg * (CMg * q)) ^ 2 ≤ ((N : ℝ) + 1) * (Kg * (CMg * q)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcardR (sq_nonneg _)
      linarith only [h1, h2, h3, h4]
    have hSpos : 0 < ∑ n ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - n) ^ 2 := lt_of_lt_of_le hSΩpos hSΩ'
    rw [abs_div, abs_of_pos hSpos, div_le_iff₀ hSpos]
    have e1 : ((N : ℝ) + 1) * (Kg * (CMg * q)) ^ 2 = Fz.L * Kg ^ 2 * CMg ^ 2 / q ^ 2 := by
      rw [← hN1']
      field_simp
    have e2 : Cκall * (cΩ / q ^ 2) = Fz.L * Kg ^ 2 * CMg ^ 2 / q ^ 2 := by
      rw [hCκall]
      field_simp
    calc |∑ n ∈ bulkWindow CL N, CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n)|
        ≤ ((N : ℝ) + 1) * (Kg * (CMg * q)) ^ 2 := hXbd
      _ = Cκall * (cΩ / q ^ 2) := by rw [e1, e2]
      _ ≤ Cκall * ∑ n ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - n) ^ 2 :=
          mul_le_mul_of_nonneg_left hSΩ' hCκall0.le
  have hnn_lo : Real.sqrt cΩ / q ≤ bulkNorm CL CR p X N := by
    rw [hnorm, show Real.sqrt cΩ / q = Real.sqrt (cΩ / q ^ 2) by
      rw [Real.sqrt_div hcΩ0.le, Real.sqrt_sq hq0.le]]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ bulkKappa CL CR p X N ^ 2 * (∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
          CR.psiHatL p X N ((N : ℤ) - n) ^ 2) := mul_nonneg (sq_nonneg _) hSRnn
    linarith only [hTLlow, this]
  have hnn_hi : bulkNorm CL CR p X N ≤ Real.sqrt (CT + Cκall ^ 2 * CT) / q := by
    rw [hnorm, show Real.sqrt (CT + Cκall ^ 2 * CT) / q = Real.sqrt ((CT + Cκall ^ 2 * CT) / q ^ 2) by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq hq0.le]]
    apply Real.sqrt_le_sqrt
    have hk2 : bulkKappa CL CR p X N ^ 2 ≤ Cκall ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hκ_all 2
      rwa [sq_abs] at this
    have h5 : bulkKappa CL CR p X N ^ 2 * (∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
          CR.psiHatL p X N ((N : ℤ) - n) ^ 2) ≤ Cκall ^ 2 * (CT / q ^ 2) :=
      mul_le_mul hk2 hSRup hSRnn (sq_nonneg _)
    have e : (CT + Cκall ^ 2 * CT) / q ^ 2 = CT / q ^ 2 + Cκall ^ 2 * (CT / q ^ 2) := by ring
    rw [e]
    linarith only [hTLup, h5]
  have hpow'
 : h ^ (-(1 : ℝ) / 4) = q⁻¹ := by
    rw [hqdef, show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.rpow_neg hst.le, one_div]
  refine ⟨?_, ?_, ?_, hκ_all, ?_⟩
  · exact lt_of_lt_of_le (div_pos (Real.sqrt_pos.mpr hcΩ0) hq0) hnn_lo
  · rw [hpow', ← div_eq_mul_inv]
    exact hnn_lo
  · rw [hpow', ← div_eq_mul_inv]
    exact hnn_hi
  intro Xs Um hE k hk
  obtain ⟨hJ0, hψ0, hψn⟩ := eigen_col_facts Fz p N Xs Um hE k
  rw [hk] at hJ0
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℤ → ℝ, ψ = eigVec Um k := ⟨_, rfl⟩
  rw [← hψ] at hJ0 hψ0 hψn
  have hJm : JacSol (mirrorFamily Fz) p N X ((N : ℤ) + 1) (fun i => ψ ((N : ℤ) - i)) := by
    intro n hn0 hnN
    exact lop_mirror Fz p N X ψ (fun j h0 h1 => hJ0 j h0 h1) n hn0 hnN
  have hℓ0 : 0 < CL.psiHatL p X N 0 := by
    rw [show CL.psiHatL p X N 0 = (CL.chain p X N).phi h 0 1 0 from
      psiHat_one_eq (CL.chain p X N) h 0]
    exact CL.seed_pos p hp X hX N hN1
  have hr0 : 0 < CR.psiHatL p X N 0 := by
    rw [show CR.psiHatL p X N 0 = (CR.chain p X N).phi h 0 1 0 from
      psiHat_one_eq (CR.chain p X N) h 0]
    exact CR.seed_pos p hp X hX N hN2
  -- the left scale `a = psi_0 / psihat_0`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ψ 0 / CL.psiHatL p X N 0 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact div_pos hψ0 hℓ0
  have ha' : a ≠ 0 := ha0.ne'
  have hstepL : h ≤ h0L := hstepN.trans hh1_L
  have hstepR : h ≤ h0R := hstepN.trans hh1_R
  have hseedL : (fun n => (1 / a) * ψ n) 0 = CL.psiHatL p X N 0 := by
    show (1 / a) * ψ 0 = CL.psiHatL p X N 0
    rw [ha]
    field_simp
  have hJL : JacSol Fz p N X (CL.chain p X N).NR (fun n => (1 / a) * ψ n) :=
    jacSol_mono (jacSol_smul hJ0 (1 / a)) (chain_NR_le CL p hp X hX N hN1)
  have hLeft : ∀ n : ℤ, 0 ≤ n → n ≤ (CL.chain p X N).NR →
      |ψ n - a * CL.psiHatL p X N n| ≤ a * (|CcL| * h ^ m * CL.envL p X N n) := by
    intro n hn0 hnN
    have hb := hBL p hp X hX N hN1 hstepL (fun n => (1 / a) * ψ n) hJL hseedL n
      (Finset.mem_Icc.mpr ⟨hn0, hnN⟩)
    have e : ψ n - a * CL.psiHatL p X N n = a * ((1 / a) * ψ n - CL.psiHatL p X N n) := by
      field_simp
    rw [e, abs_mul, abs_of_pos ha0]
    have hE0 : 0 ≤ CL.envL p X N n := (LB n hn0 hnN).1
    have hh : |(1 / a) * ψ n - CL.psiHatL p X N n| ≤ |CcL| * h ^ m * CL.envL p X N n := by
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ hE0
      exact mul_le_mul_of_nonneg_right (le_abs_self CcL) (pow_nonneg hst.le m)
    exact mul_le_mul_of_nonneg_left hh ha0.le
  -- the error parameter `eps = C_eps h^m`
  obtain ⟨ε, hε⟩ : ∃ x : ℝ, x = Cε * h ^ m := ⟨_, rfl⟩
  have hhm : h ^ m ≤ h := pow_le_of_le_one hst.le hh_le1 (by omega)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεs' : ε ≤ εs := by
    rw [hε]
    have h1' : h * Cε ≤ εs := (le_div_iff₀ hCε0).mp (hstepN.trans hh1_ε)
    calc Cε * h ^ m ≤ Cε * h := mul_le_mul_of_nonneg_left hhm hCε0.le
      _ = h * Cε := by ring
      _ ≤ εs := h1'
  have hε1 : ε ≤ 1 := le_trans hεs' hεs1
  have hεL : |CcL| * h ^ m ≤ ε := by
    rw [hε]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hst.le m)
    rw [hCε]
    linarith only [abs_nonneg CcR]
  have hεR : |CcR| * h ^ m ≤ ε := by
    rw [hε]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hst.le m)
    rw [hCε]
    linarith only [abs_nonneg CcL]
  have hsmP : 4 * ε * CMg ≤ cl := by
    have := mul_le_mul_of_nonneg_right hεs' (by positivity : (0 : ℝ) ≤ 4 * CMg)
    linarith only [this, hsm_pair]
  have hsm1' : (1 + CKu ^ 2) * Cenv * ε ≤ cΩ / 2 := by
    have := mul_le_mul_of_nonneg_left hεs' (by positivity : (0 : ℝ) ≤ (1 + CKu ^ 2) * Cenv)
    linarith only [this, hsm1]
  have hsm2' : Cκe * ε * (1 + CKu) ≤ cK / 2 := by
    have := mul_le_mul_of_nonneg_left hεs' (by positivity : (0 : ℝ) ≤ Cκe * (1 + CKu))
    linarith only [this, hsm2]
  have hCaε : Ca * ε ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hεs' (by positivity : (0 : ℝ) ≤ Ca + 1)
    linarith only [this, hsm_Ca, hε0]
  -- the sign of psi_N and the right scale `b = psi_N / psihat^R_0`
  have hψN : ψ (N : ℤ) ≠ 0 := by
    intro hN0
    have hA : ∀ k : ℤ, 0 ≤ k → k < (CR.chain p X N).NR → (mirrorFamily Fz).bondA p N k ≠ 0 := by
      intro k hk0 hkN hbz
      have hcas := ladder_cas_lower (CR.chain p X N) CR.cs ((mirrorFamily Fz).step N) m
        (CR.valid p hp X hX N hN2) (CR.shape p hp X hX N hN2).1 k hk0 (by omega)
      rw [CR.omega_sqrt p hp X hX N hN2, abs_of_nonneg (Real.sqrt_nonneg _)] at hcas
      have hA0 : (CR.chain p X N).A k = 0 := by
        rw [CR.A_bond p hp X hX N hN2 k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), hbz]
      unfold cas at hcas
      rw [hA0, zero_mul, abs_zero] at hcas
      have hpos : 0 < CR.cs.cm * Real.sqrt ((mirrorFamily Fz).step N) :=
        mul_pos CR.cs.cm_pos (Real.sqrt_pos.mpr hst)
      linarith only [hcas, hpos]
    have hJmR := jacSol_mono hJm (chain_NR_le CR p hp X hX N hN2)
    have hz := seed_zero_eq_zero hJmR hA (by
      show ψ ((N : ℤ) - 0) = 0
      rw [sub_zero]
      exact hN0)
    -- the mirror solution vanishes on the rows `N - k`, `k <= NR^R`
    have hzero : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → (N : ℤ) - n ≤ (CR.chain p X N).NR → ψ n = 0 := by
      intro n hn0 hnN hkN
      have hk : (((N : ℤ) - n).toNat : ℤ) = (N : ℤ) - n := Int.toNat_of_nonneg (by omega)
      have := hz ((N : ℤ) - n).toNat (by rw [hk]; exact hkN)
      rw [hk, sub_sub_cancel] at this
      exact this
    -- the overlap pair of the window
    have h3 : (3 : ℝ) ≤ (CL.c - CL.c') / (2 * h) := by
      have h6 : 6 ≤ (CL.c - CL.c') / h := by rw [le_div_iff₀ hst]; linarith only [hh1_d, hstepN]
      have e : (CL.c - CL.c') / (2 * h) = ((CL.c - CL.c') / h) / 2 := by rw [div_div, mul_comm]
      rw [e]; linarith only [hScard, h6]
    have hSne : S.Nonempty := by
      apply Finset.card_pos.mp
      have : (0 : ℝ) < (S.card : ℝ) := by linarith only [hSmall, h3]
      exact_mod_cast this
    obtain ⟨n0, hn0S⟩ := hSne
    obtain ⟨hΩ0, hΩ1⟩ := hSΩ n0 hn0S
    obtain ⟨hn0', hn1', hc1', hc2'⟩ := hSprop n0 hn0S
    have hzl : ∀ j : ℤ, j ∈ bulkWindow CL N → ψ j = 0 := by
      intro j hj
      obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ j).mp hj
      obtain ⟨hj0, hjN⟩ := (hmemR j).mp hmem
      apply hzero j hj0 hjN
      have hlow : uNode h ((N : ℤ) - j) ≤ CR.c := by
        rw [uNode_mirror Fz.L h N j hLs, hcoup.1]
        linarith only [hc1]

      exact le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - j) hlow
    -- the left comparison then bounds `|psihat|` on the window by the envelope
    have hleft_small : ∀ j : ℤ, j ∈ bulkWindow CL N →
        |CL.psiHatL p X N j| ≤ |CcL| * h ^ m * CL.envL p X N j := by
      intro j hj
      obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ j).mp hj
      obtain ⟨hj0, -⟩ := (hmemR j).mp hmem
      have hL := hLeft j hj0 (le_NR_of CL p hp X hX N hN1 hst j hc2)
      rw [hzl j hj, zero_sub, abs_neg, abs_mul, abs_of_pos ha0] at hL
      have h' : a * |CL.psiHatL p X N j| ≤ a * (|CcL| * h ^ m * CL.envL p X N j) := hL
      exact le_of_mul_le_mul_left h' ha0
    have hEmax : ∀ j : ℤ, j ∈ bulkWindow CL N → CL.envL p X N j ≤ CMg * q := by
      intro j hj
      obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ j).mp hj
      obtain ⟨hj0, -⟩ := (hmemR j).mp hmem
      exact LD j hj0 (le_NR_of CL p hp X hX N hN1 hst j hc2) hc1
    have hpair := hPL n0 hn0S
    have hNR1 : n0 + 1 ≤ (CL.chain p X N).NR := le_NR_of CL p hp X hX N hN1 hst (n0 + 1) hc2'
    have hE0 := (LB n0 (by omega) (by omega)).1
    have hE1 := (LB (n0 + 1) (by omega) hNR1).1
    have hsmall0 := hleft_small n0 hΩ0
    have hsmall1 := hleft_small (n0 + 1) hΩ1
    have hEn0 := hEmax n0 hΩ0
    have hEn1 := hEmax (n0 + 1) hΩ1
    have hsum : cl * q ≤ 2 * ε * CMg * q := by
      have h1 : |CL.psiHatL p X N n0| + |CL.psiHatL p X N (n0 + 1)|
          ≤ |CcL| * h ^ m * CL.envL p X N n0 + |CcL| * h ^ m * CL.envL p X N (n0 + 1) :=
        add_le_add hsmall0 hsmall1
      have k0 : |CcL| * h ^ m * CL.envL p X N n0 ≤ ε * (CMg * q) :=
        mul_le_mul hεL hEn0 hE0 hε0
      have k1 : |CcL| * h ^ m * CL.envL p X N (n0 + 1) ≤ ε * (CMg * q) :=
        mul_le_mul hεL hEn1 hE1 hε0
      linarith only [hpair, h1, k0, k1]
    have hcl_le : cl ≤ 2 * ε * CMg :=
      le_of_mul_le_mul_right (by linarith only [hsum] : cl * q ≤ 2 * ε * CMg * q) hq0
    linarith only [hsmP, hcl_le, hcl0]
  -- the right scale `b = psi_N / psihat^R_0` and the right comparison
  obtain ⟨r0, hr0def⟩ : ∃ x : ℝ, x = CR.psiHatL p X N 0 := ⟨_, rfl⟩
  have hr0' : 0 < r0 := by rw [hr0def]; exact hr0
  obtain ⟨b, hb⟩ : ∃ x : ℝ, x = ψ (N : ℤ) / r0 := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := by rw [hb]; exact div_ne_zero hψN hr0'.ne'
  have hJR : JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR (fun i => (1 / b) * ψ ((N : ℤ) - i)) :=
    jacSol_mono (jacSol_smul hJm (1 / b)) (chain_NR_le CR p hp X hX N hN2)
  have hseedR : (fun i => (1 / b) * ψ ((N : ℤ) - i)) 0 = CR.psiHatL p X N 0 := by
    show (1 / b) * ψ ((N : ℤ) - 0) = CR.psiHatL p X N 0
    rw [sub_zero, ← hr0def, hb]
    field_simp
  have hRight : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → (N : ℤ) - n ≤ (CR.chain p X N).NR →
      |ψ n - b * CR.psiHatL p X N ((N : ℤ) - n)| ≤ |b| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n)) := by
    intro n hn0 hnN hkN
    have hb' := hBR p hp X hX N hN2 hstepR (fun i => (1 / b) * ψ ((N : ℤ) - i)) hJR hseedR ((N : ℤ) - n)
      (Finset.mem_Icc.mpr ⟨by omega, hkN⟩)
    have hb2 : |(1 / b) * ψ ((N : ℤ) - ((N : ℤ) - n)) - CR.psiHatL p X N ((N : ℤ) - n)|
        ≤ CcR * h ^ m * CR.envL p X N ((N : ℤ) - n) := hb'
    rw [sub_sub_cancel] at hb2
    have e : ψ n - b * CR.psiHatL p X N ((N : ℤ) - n)
        = b * ((1 / b) * ψ n - CR.psiHatL p X N ((N : ℤ) - n)) := by
      rw [mul_sub, ← mul_assoc, mul_one_div_cancel hb0, one_mul]
    have hE0 := (RB ((N : ℤ) - n) (by omega) hkN).1
    rw [e, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hb2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CcR) (pow_nonneg hst.le m)) hE0)
  -- the ratio `Kt = b / a`
  obtain ⟨Kt, hKt⟩ : ∃ x : ℝ, x = b / a := ⟨_, rfl⟩
  have hbKt : b = Kt * a := by rw [hKt]; field_simp
  have hKtabs : |b| = |Kt| * a := by rw [hbKt, abs_mul, abs_of_pos ha0]
  -- the sums of the eigenvector column over the left and right parts
  obtain ⟨TL, hTL⟩ : ∃ x : ℝ, x = ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.psiHatL p X N n ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨SR, hSR⟩ : ∃ x : ℝ,
      x = ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), CR.psiHatL p X N ((N : ℤ) - n) ^ 2 := ⟨_, rfl⟩
  obtain ⟨SΩr, hSΩr⟩ : ∃ x : ℝ, x = ∑ n ∈ bulkWindow CL N, CR.psiHatL p X N ((N : ℤ) - n) ^ 2 := ⟨_, rfl⟩
  obtain ⟨XΩ, hXΩ⟩ : ∃ x : ℝ,
      x = ∑ n ∈ bulkWindow CL N, CL.psiHatL p X N n * CR.psiHatL p X N ((N : ℤ) - n) := ⟨_, rfl⟩
  obtain ⟨NL, hNL⟩ : ∃ x : ℝ, x = ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), ψ n ^ 2 := ⟨_, rfl⟩
  obtain ⟨NRp, hNRp⟩ : ∃ x : ℝ, x = ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), ψ n ^ 2 := ⟨_, rfl⟩
  have hNLNR : 1 = NL + NRp := by
    rw [hNL, hNRp, Finset.sum_filter_add_sum_filter_not, hψn]
  have hLftSub : (rowsOf N).filter (fun n => uNode h n ≤ CL.c) ⊆ Finset.Icc (0 : ℤ) (CL.chain p X N).NR := by
    intro n hn
    obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, -⟩ := (hmemR n).mp hnr
    exact Finset.mem_Icc.mpr ⟨hn0, le_NR_of CL p hp X hX N hN1 hst n hc⟩
  have hinjR : Set.InjOn (fun n : ℤ => (N : ℤ) - n) ↑((rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c)) := by
    intro a' _ b' _ hab
    simp only at hab
    omega
  have hRgtSub : ∀ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
      (N : ℤ) - n ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR := by
    intro n hn
    obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := (hmemR n).mp hnr
    have hcn : CL.c < uNode h n := lt_of_not_ge hc
    have hlow : uNode h ((N : ℤ) - n) ≤ CR.c := by
      rw [uNode_mirror Fz.L h N n hLs, hcoup.1]
      linarith only [hc'cL, hcn]
    exact Finset.mem_Icc.mpr ⟨by omega, le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hlow⟩
  have hELsum' : ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), CL.envL p X N n ^ 2 ≤ CE2 / q ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hLftSub (fun j _ _ => sq_nonneg _)).trans hELsum
  have hERgt : ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c), CR.envL p X N ((N : ℤ) - n) ^ 2
      ≤ CE2 / q ^ 2 :=
    (sum_reflect_le N _ _ (fun k : ℤ => CR.envL p X N k ^ 2) (fun k => sq_nonneg _) hRgtSub hinjR).trans hERsum
  -- the normalisation identity with errors
  have hNL1 : |NL - a ^ 2 * TL| ≤ a ^ 2 * (Cenv * ε) / q ^ 2 := by
    have eq1 : NL - a ^ 2 * TL = ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c),
        (ψ n ^ 2 - a ^ 2 * CL.psiHatL p X N n ^ 2) := by
      rw [hNL, hTL, Finset.mul_sum, Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c),
        |ψ n ^ 2 - a ^ 2 * CL.psiHatL p X N n ^ 2| ≤ a ^ 2 * (ε * (2 * Kg + 1)) * CL.envL p X N n ^ 2 := by
      intro n hn
      obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, -⟩ := (hmemR n).mp hnr
      have hnN := le_NR_of CL p hp X hX N hN1 hst n hc
      have hu := hLeft n hn0 hnN
      have hv := LA n hn0 hnN
      have hE := (LB n hn0 hnN).1
      exact sq_perturb (ψ n) (CL.psiHatL p X N n) a (|CcL| * h ^ m) (CL.envL p X N n) Kg ε
        (by positivity) hεL hε1 hE hKg0.le hv (by rw [abs_of_pos ha0]; linarith only [hu])

    rw [eq1]
    calc |∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c), (ψ n ^ 2 - a ^ 2 * CL.psiHatL p X N n ^ 2)|
        ≤ ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c),
            |ψ n ^ 2 - a ^ 2 * CL.psiHatL p X N n ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c),
            a ^ 2 * (ε * (2 * Kg + 1)) * CL.envL p X N n ^ 2 := Finset.sum_le_sum hterm
      _ = a ^ 2 * (ε * (2 * Kg + 1)) * ∑ n ∈ (rowsOf N).filter (fun n => uNode h n ≤ CL.c),
            CL.envL p X N n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ a ^ 2 * (ε * (2 * Kg + 1)) * (CE2 / q ^ 2) :=
            mul_le_mul_of_nonneg_left hELsum' (by positivity)
      _ = a ^ 2 * (Cenv * ε) / q ^ 2 := by rw [hCenv]; ring
  have hNR1 : |NRp - b ^ 2 * SR| ≤ b ^ 2 * (Cenv * ε) / q ^ 2 := by
    have eq2 : NRp - b ^ 2 * SR = ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
        (ψ n ^ 2 - b ^ 2 * CR.psiHatL p X N ((N : ℤ) - n) ^ 2) := by
      rw [hNRp, hSR, Finset.mul_sum, Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
        |ψ n ^ 2 - b ^ 2 * CR.psiHatL p X N ((N : ℤ) - n) ^ 2|
          ≤ b ^ 2 * (ε * (2 * Kg + 1)) * CR.envL p X N ((N : ℤ) - n) ^ 2 := by
      intro n hn
      obtain ⟨hnr, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn0, hnN⟩ := (hmemR n).mp hnr
      have hj := hRgtSub n hn
      have hj' := Finset.mem_Icc.mp hj
      have hv := RA ((N : ℤ) - n) hj'.1 hj'.2
      have hE := (RB ((N : ℤ) - n) hj'.1 hj'.2).1
      have hu := hRight n hn0 hnN hj'.2
      exact sq_perturb (ψ n) (CR.psiHatL p X N ((N : ℤ) - n)) b (|CcR| * h ^ m) (CR.envL p X N ((N : ℤ) - n)) Kg ε
        (by positivity) hεR hε1 hE hKg0.le hv (by rw [mul_assoc]; exact hu)
    rw [eq2]
    calc |∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            (ψ n ^ 2 - b ^ 2 * CR.psiHatL p X N ((N : ℤ) - n) ^ 2)|
        ≤ ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            |ψ n ^ 2 - b ^ 2 * CR.psiHatL p X N ((N : ℤ) - n) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            b ^ 2 * (ε * (2 * Kg + 1)) * CR.envL p X N ((N : ℤ) - n) ^ 2 := Finset.sum_le_sum hterm
      _ = b ^ 2 * (ε * (2 * Kg + 1)) * ∑ n ∈ (rowsOf N).filter (fun n => ¬ uNode h n ≤ CL.c),
            CR.envL p X N ((N : ℤ) - n) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ b ^ 2 * (ε * (2 * Kg + 1)) * (CE2 / q ^ 2) :=
            mul_le_mul_of_nonneg_left hERgt (by positivity)
      _ = b ^ 2 * (Cenv * ε) / q ^ 2 := by rw [hCenv]; ring
  have hEmax : ∀ j : ℤ, j ∈ bulkWindow CL N → CL.envL p X N j ≤ CMg * q := by
    intro j hj
    obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ j).mp hj
    obtain ⟨hj0, -⟩ := (hmemR j).mp hmem
    exact LD j hj0 (le_NR_of CL p hp X hX N hN1 hst j hc2) hc1
  -- the pointwise difference of the left and the (scaled) right comparison on the window
  have hptκ : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n)|
      ≤ ε * (1 + |Kt|) * (CMg * q) := by
    intro n hn
    obtain ⟨hmem, hc1, hc2⟩ := (hmemΩ n).mp hn
    obtain ⟨hn0, hnN⟩ := (hmemR n).mp hmem
    have hlN := le_NR_of CL p hp X hX N hN1 hst n hc2
    have hu := hLeft n hn0 hlN
    have hlowR : uNode h ((N : ℤ) - n) ≤ CR.c := by
      rw [uNode_mirror Fz.L h N n hLs, hcoup.1]
      linarith only [hc1]
    have hhigh : CR.c' ≤ uNode h ((N : ℤ) - n) := by
      rw [uNode_mirror Fz.L h N n hLs, hcoup.2]
      linarith only [hc2]
    have hj := le_NR_of CR p hp X hX N hN2 hst ((N : ℤ) - n) hlowR
    have hv := hRight n hn0 hnN hj
    have hEL := hEmax n hn
    have hER := RD ((N : ℤ) - n) (by omega) hj hhigh
    have hEL0 := (LB n hn0 hlN).1
    have hER0 := (RB ((N : ℤ) - n) (by omega) hj).1
    have key : a * (CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n))
        = -(ψ n - a * CL.psiHatL p X N n) + (ψ n - b * CR.psiHatL p X N ((N : ℤ) - n)) := by
      rw [hbKt]; ring
    have hA1 : |a * (CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n))|
        ≤ a * (|CcL| * h ^ m * CL.envL p X N n) + |b| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n)) := by
      rw [key]
      calc |-(ψ n - a * CL.psiHatL p X N n) + (ψ n - b * CR.psiHatL p X N ((N : ℤ) - n))|
          ≤ |-(ψ n - a * CL.psiHatL p X N n)| + |ψ n - b * CR.psiHatL p X N ((N : ℤ) - n)| := abs_add_le _ _
        _ = |ψ n - a * CL.psiHatL p X N n| + |ψ n - b * CR.psiHatL p X N ((N : ℤ) - n)| := by rw [abs_neg]
        _ ≤ _ := add_le_add hu hv
    have hbabs : |b| = |Kt| * a := hKtabs
    rw [hbabs, abs_mul, abs_of_pos ha0] at hA1
    have hL' : |CcL| * h ^ m * CL.envL p X N n ≤ ε * (CMg * q) := mul_le_mul hεL hEL hEL0 hε0
    have hR' : |CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n) ≤ ε * (CMg * q) := mul_le_mul hεR hER hER0 hε0
    have hK' : |Kt| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n)) ≤ |Kt| * (ε * (CMg * q)) :=
      mul_le_mul_of_nonneg_left hR' (abs_nonneg _)
    have hfin : a * |CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n)|
        ≤ a * (ε * (1 + |Kt|) * (CMg * q)) := by
      have e : a * (ε * (1 + |Kt|) * (CMg * q)) = a * (ε * (CMg * q)) + a * (|Kt| * (ε * (CMg * q))) := by ring
      rw [e]
      have h1 : a * (|CcL| * h ^ m * CL.envL p X N n) ≤ a * (ε * (CMg * q)) :=
        mul_le_mul_of_nonneg_left hL' ha0.le
      have h2 : |Kt| * a * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n))
          = a * (|Kt| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n))) := by ring
      rw [h2] at hA1
      have h3 : a * (|Kt| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n)))
          ≤ a * (|Kt| * (ε * (CMg * q))) := mul_le_mul_of_nonneg_left hK' ha0.le
      linarith only [hA1, h1, h3]
    exact le_of_mul_le_mul_left hfin ha0
  -- the glued coefficient is close to `Kt`
  have hΩr' : cΩ / q ^ 2 ≤ SΩr := by rw [hSΩr]; exact hΩr
  have hSΩpos : 0 < SΩr := lt_of_lt_of_le (by positivity) hΩr'
  have hκerr : |XΩ / SΩr - Kt| ≤ Cκe * ε * (1 + |Kt|) := by
    have eX : XΩ - Kt * SΩr = ∑ n ∈ bulkWindow CL N,
        (CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n)) * CR.psiHatL p X N ((N : ℤ) - n) := by
      rw [hXΩ, hSΩr, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hterm : ∀ n ∈ bulkWindow CL N,
        |(CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n)) * CR.psiHatL p X N ((N : ℤ) - n)|
          ≤ ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2) := by
      intro n hn
      obtain ⟨h1', h2'⟩ := hΩbd n hn
      rw [abs_mul]
      have hp := hptκ n hn
      calc |CL.psiHatL p X N n - Kt * CR.psiHatL p X N ((N : ℤ) - n)| * |CR.psiHatL p X N ((N : ℤ) - n)|
          ≤ (ε * (1 + |Kt|) * (CMg * q)) * (Kg * (CMg * q)) :=
            mul_le_mul hp h2' (abs_nonneg _) (by positivity)
        _ = ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2) := by ring
    have hsumb : |XΩ - Kt * SΩr| ≤ ((bulkWindow CL N).card : ℝ) * (ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2)) := by
      rw [eX]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have hcardN : ((bulkWindow CL N).card : ℝ) ≤ (N : ℝ) + 1 := by
      have hr : (rowsOf N).card = N + 1 := by
        unfold rowsOf
        simp
      have hc : (bulkWindow CL N).card ≤ N + 1 := by
        rw [← hr]
        exact Finset.card_le_card (fun n hn => ((hmemΩ n).mp hn).1)
      exact_mod_cast hc
    have hTbd : ((bulkWindow CL N).card : ℝ) * (ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2))
        ≤ ((N : ℝ) + 1) * (ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2)) :=
      mul_le_mul_of_nonneg_right hcardN (by positivity)
    have hN1q : ((N : ℝ) + 1) * q ^ 4 = Fz.L := hN1'
    have e : XΩ / SΩr - Kt = (XΩ - Kt * SΩr) / SΩr := by field_simp
    have hbig : |XΩ - Kt * SΩr| ≤ Cκe * ε * (1 + |Kt|) * SΩr := by
      have hA : |XΩ - Kt * SΩr| ≤ ((N : ℝ) + 1) * (ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2)) :=
        hsumb.trans hTbd
      have hB : Cκe * ε * (1 + |Kt|) * (cΩ / q ^ 2) = ((N : ℝ) + 1) * (ε * (1 + |Kt|) * (Kg * CMg ^ 2 * q ^ 2)) := by
        rw [hCκe]
        field_simp
        rw [← hN1q]
        ring
      have hC : Cκe * ε * (1 + |Kt|) * (cΩ / q ^ 2) ≤ Cκe * ε * (1 + |Kt|) * SΩr :=
        mul_le_mul_of_nonneg_left hΩr' (by positivity)
      linarith only [hA, hB, hC]
    rw [e, abs_div, abs_of_pos hSΩpos, div_le_iff₀ hSΩpos]
    exact hbig
  -- the ratio `Kt` is bounded above and below, through one overlap pair
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have h3 : (3 : ℝ) ≤ (CL.c - CL.c') / (2 * h) := by
      have h6 : 6 ≤ (CL.c - CL.c') / h := by rw [le_div_iff₀ hst]; linarith only [hh1_d, hstepN]
      have e : (CL.c - CL.c') / (2 * h) = ((CL.c - CL.c') / h) / 2 := by rw [div_div, mul_comm]
      rw [e]; linarith only [hScard, h6]
    have : (0 : ℝ) < (S.card : ℝ) := by linarith only [hSmall, h3]
    exact_mod_cast this
  obtain ⟨n0, hn0S⟩ := hSne
  obtain ⟨hΩ0, hΩ1⟩ := hSΩ n0 hn0S
  have hpL := hPL n0 hn0S
  have hpR := hPR n0 hn0S
  have hb0 := hΩbd n0 hΩ0
  have hb1 := hΩbd (n0 + 1) hΩ1
  have hup : ∀ j : ℤ, j ∈ bulkWindow CL N →
      |CL.psiHatL p X N j| ≤ |Kt| * |CR.psiHatL p X N ((N : ℤ) - j)| + ε * (1 + |Kt|) * (CMg * q) := by
    intro j hj
    have hd := hptκ j hj
    have h1 := abs_add_le (CL.psiHatL p X N j - Kt * CR.psiHatL p X N ((N : ℤ) - j))
      (Kt * CR.psiHatL p X N ((N : ℤ) - j))
    rw [sub_add_cancel, abs_mul] at h1
    linarith only [h1, hd]
  have hdown : ∀ j : ℤ, j ∈ bulkWindow CL N →
      |Kt| * |CR.psiHatL p X N ((N : ℤ) - j)| ≤ |CL.psiHatL p X N j| + ε * (1 + |Kt|) * (CMg * q) := by
    intro j hj
    have hd := hptκ j hj
    have h1 := abs_add_le (CL.psiHatL p X N j)
      (-(CL.psiHatL p X N j - Kt * CR.psiHatL p X N ((N : ℤ) - j)))
    rw [abs_neg] at h1
    have e2 : CL.psiHatL p X N j + -(CL.psiHatL p X N j - Kt * CR.psiHatL p X N ((N : ℤ) - j))
        = Kt * CR.psiHatL p X N ((N : ℤ) - j) := by ring
    rw [e2, abs_mul] at h1
    linarith only [h1, hd]
  have hKtB := kt_bounds_pure q ε Kg CMg cl |CL.psiHatL p X N n0| |CL.psiHatL p X N (n0 + 1)|
    |CR.psiHatL p X N ((N : ℤ) - n0)| |CR.psiHatL p X N ((N : ℤ) - (n0 + 1))| |Kt| hq0 hε0 hε1 hKg0.le
    hCMg0 hcl0 hsmP (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    hpL (by rw [add_comm]; exact hpR)
    (hup n0 hΩ0) (hup (n0 + 1) hΩ1) (hdown n0 hΩ0) (hdown (n0 + 1) hΩ1)
    hb0.2 hb1.2 hb0.1 hb1.1
  have hKt1 : cK ≤ |Kt| := by rw [hcK]; exact hKtB.1
  have hKt2 : |Kt| ≤ CKu := by rw [hCKu]; exact hKtB.2
  -- the normalisation algebra: the glued normaliser `nn` and the glued ratio `kk = XΩ/SΩr`
  have hNR1' : |NRp - (Kt * a) ^ 2 * SR| ≤ (Kt * a) ^ 2 * (Cenv * ε) / q ^ 2 := by
    rw [← hbKt]; exact hNR1
  have hNA := normalisation_algebra q ε a Kt TL SR SΩr XΩ NL NRp cΩ CT Cenv Cκe CKu cK hq0 hε0 hε1 ha0
    hcΩ0 hCT0 hcK0 hCenv0 hCκe0.le hCKu0.le hNLNR hNL1 hNR1'
    (by rw [hTL]; exact hTLlow) (by rw [hTL]; exact hTLup) (by rw [hSR]; exact hSRnn) (by rw [hSR]; exact hSRup)
    hSΩpos hκerr hKt1 hKt2 hsm1' hsm2'
  obtain ⟨⟨hnn_lo, -⟩, ⟨hk1, -⟩, hAa⟩ := hNA
  obtain ⟨nn, hnn⟩ : ∃ x : ℝ, x = Real.sqrt (TL + (XΩ / SΩr) ^ 2 * SR) := ⟨_, rfl⟩
  rw [← hnn] at hnn_lo hAa
  have hnnpos : 0 < nn := lt_of_lt_of_le (div_pos (Real.sqrt_pos.mpr hcΩ0) hq0) hnn_lo
  have hκeq : bulkKappa CL CR p X N = XΩ / SΩr := by rw [hκdef, ← hXΩ, ← hSΩr]
  have hbN : bulkNorm CL CR p X N = nn := by
    rw [hnorm, hnn, ← hTL, ← hSR, hκeq]
  have hkb : cK / 2 ≤ |bulkKappa CL CR p X N| := by rw [hκeq]; exact hk1
  have hAa' : |a * nn - 1| ≤ Ca * ε := by rw [hCa]; exact hAa
  have hCaε : Ca * ε ≤ 1 := by
    have h1 : ε * (Ca + 1) ≤ εs * (Ca + 1) := mul_le_mul_of_nonneg_right hεs' (by linarith only [hCa0])
    have e : ε * (Ca + 1) = Ca * ε + ε := by ring
    linarith only [h1, e, hsm_Ca, hε0]
  have hCr0 : 0 ≤ Cr := by
    rw [hCr]
    have h1 := mul_nonneg hKg0.le (add_nonneg (mul_nonneg hCKu0.le hCa0)
      (mul_nonneg hCκe0.le (by linarith only [hCKu0] : (0 : ℝ) ≤ 1 + CKu)))
    linarith only [h1, hCKu0]

  rw [← hψ]
  refine ⟨hkb, fun n hn => ?_⟩
  obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp hn
  by_cases hc : uNode (Fz.step N) n ≤ CL.c
  · -- left rows
    have hnL : n ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR :=
      hLftSub (Finset.mem_filter.mpr ⟨hn, hc⟩)
    obtain ⟨hnL0, hnL1⟩ := Finset.mem_Icc.mp hnL
    have hVL : bulkVec CL CR p X N n = CL.psiHatL p X N n / nn := by
      simp only [bulkVec, glueVec, ite_eq_left hc]
      exact congrArg (fun t => CL.psiHatL p X N n / t) hbN
    have hEnvL : bulkEnv CL CR p X N n = CL.envL p X N n / nn := by
      unfold bulkEnv
      rw [ite_eq_left hc, hbN]
    have hcomp := left_comp_pure (ψ n) (CL.psiHatL p X N n) a nn (CL.envL p X N n) ε (|CcL| * h ^ m) Kg Ca
      hnnpos ha0 hε0 (mul_nonneg (abs_nonneg _) (pow_nonneg hst.le m)) hεL (LB n hnL0 hnL1).1 hKg0.le hCa0
      hAa' hCaε (hLeft n hnL0 hnL1) (LA n hnL0 hnL1)
    rw [hVL, hEnvL]
    exact final_left _ Kg Ca Cr cK Cε (h ^ m) ε (CL.envL p X N n / nn) Cc hε hCc
      (div_nonneg (LB n hnL0 hnL1).1 hnnpos.le) hCε0.le (pow_nonneg hst.le m) hCr0 hcK0 hKg0.le hCa0 hcomp
  · -- right rows
    have hnR : (N : ℤ) - n ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR :=
      hRgtSub n (Finset.mem_filter.mpr ⟨hn, hc⟩)
    obtain ⟨hnR0, hnR1⟩ := Finset.mem_Icc.mp hnR
    have hVR : bulkVec CL CR p X N n = XΩ / SΩr * CR.psiHatL p X N ((N : ℤ) - n) / nn := by
      simp only [bulkVec, glueVec, ite_eq_right hc]
      change bulkKappa CL CR p X N * CR.psiHatL p X N ((N : ℤ) - n) / bulkNorm CL CR p X N = _
      rw [hκeq, hbN]
    have hEnvR : bulkEnv CL CR p X N n = |XΩ / SΩr| * CR.envL p X N ((N : ℤ) - n) / nn := by
      unfold bulkEnv
      rw [ite_eq_right hc, hbN, hκeq]
    have hRt : |ψ n - Kt * a * CR.psiHatL p X N ((N : ℤ) - n)|
        ≤ |Kt * a| * (|CcR| * h ^ m * CR.envL p X N ((N : ℤ) - n)) := by
      rw [← hbKt]; exact hRight n hn0 hnN hnR1
    have hcomp := right_comp_pure (ψ n) (CR.psiHatL p X N ((N : ℤ) - n)) a Kt (XΩ / SΩr) nn
      (CR.envL p X N ((N : ℤ) - n)) ε (|CcR| * h ^ m) Kg Ca CKu Cκe Cr hnnpos ha0 hε0
      (mul_nonneg (abs_nonneg _) (pow_nonneg hst.le m)) hεR (RB ((N : ℤ) - n) hnR0 hnR1).1 hKg0.le hCa0
      hCKu0.le hCκe0.le hKt2 hCaε hAa' hκerr hRt (RA ((N : ℤ) - n) hnR0 hnR1) hCr
    rw [hVR, hEnvR]
    have e8 : |XΩ / SΩr| * CR.envL p X N ((N : ℤ) - n) / nn
        = |XΩ / SΩr| * (CR.envL p X N ((N : ℤ) - n) / nn) := mul_div_assoc _ _ _
    rw [e8]
    exact final_right _ Cr cK Cε (h ^ m) Kg Ca Cc |XΩ / SΩr| (CR.envL p X N ((N : ℤ) - n) / nn) ε hCr0 hcK0 hk1
      (div_nonneg (RB ((N : ℤ) - n) hnR0 hnR1).1 hnnpos.le) hε hCε0.le (pow_nonneg hst.le m) hCc hKg0.le hCa0 hcomp


/-- **`PropThaW`** (prop:tha-W, all three conjuncts): the two solution bounds, the bulk normalisation with the kappa bounds
and the eigenvector comparison (`bulk_conj1`), and the collar relative accuracy (`bulk_collar_bound`). -/
theorem propThaW {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) :
    PropThaW Fz P Jlo Jhi m U V CL CR := by
  intro hm hcoup r hr
  exact ⟨bulkSolutionBound_of_one_le CL hm, bulkSolutionBound_of_one_le CR hm,
    bulk_conj1 CL CR hm hcoup r hr, bulk_collar_bound CL CR⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_conj1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_conj1

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.propThaW

end FormalResearch.JacobiEigenvectors.TheoremA

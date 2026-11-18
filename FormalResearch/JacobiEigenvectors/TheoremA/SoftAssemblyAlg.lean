module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftEigen

/-!
# Paper J, Layer 2 (L2.C7): the `l^2` algebra of the matching (chain step E5), `app_thmA` Step 4 (b)

Source: `app_thmA.tex` Step 4 (b).  Proved (axiom-pinned): `match_alg`: for `psi^L = kappa psi^R` on a finite set `Omega` and the four `l^2` facts on `Omega`
(`sum (uL - aL)^2 <= (e TL)^2 m`, the same for the right sequence, `sum aL^2 <= (K TL)^2 m`, `(c TL)^2 m <= sum aL^2`, the same for `bR`), with `e <= c/2`:
`|kappa| TR <= 2 (K + c/2)/c TL`, `TL <= 2 (K + c/2)/c |kappa| TR`, `|glueKappa aL bR Omega - kappa| <= e (1 + 2(K + c/2)/c)/c |kappa|`.
Not formalised: nothing (abstract lemma).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

/-- l2 norm over a finite set -/
def nrm (S : Finset ℤ) (f : ℤ → ℝ) : ℝ := Real.sqrt (∑ n ∈ S, f n ^ 2)

lemma nrm_nonneg (S : Finset ℤ) (f : ℤ → ℝ) : 0 ≤ nrm S f := Real.sqrt_nonneg _

lemma nrm_smul (S : Finset ℤ) (f : ℤ → ℝ) (κ : ℝ) : nrm S (fun n => κ * f n) = |κ| * nrm S f := by
  unfold nrm
  have : ∑ n ∈ S, (κ * f n) ^ 2 = κ ^ 2 * ∑ n ∈ S, f n ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

lemma nrm_congr (S : Finset ℤ) (f g : ℤ → ℝ) (h : ∀ n ∈ S, f n = g n) : nrm S f = nrm S g := by
  unfold nrm
  congr 1
  exact Finset.sum_congr rfl (fun n hn => by rw [h n hn])

lemma nrm_add_le (S : Finset ℤ) (a b : ℤ → ℝ) : nrm S (fun n => a n + b n) ≤ nrm S a + nrm S b :=
  sqrt_sum_add_le S a b

lemma nrm_mono (S : Finset ℤ) (f g : ℤ → ℝ) (h : ∀ n ∈ S, |f n| ≤ |g n|) : nrm S f ≤ nrm S g := by
  unfold nrm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum (fun n hn => ?_))
  rw [← sq_abs (f n), ← sq_abs (g n)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h n hn) 2

/-- from a bound on the sum of squares to a bound on the norm -/
lemma nrm_le_of_sq (S : Finset ℤ) (f : ℤ → ℝ) (B m : ℝ) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (h : ∑ n ∈ S, f n ^ 2 ≤ B ^ 2 * m) : nrm S f ≤ B * Real.sqrt m := by
  unfold nrm
  calc Real.sqrt (∑ n ∈ S, f n ^ 2) ≤ Real.sqrt (B ^ 2 * m) := Real.sqrt_le_sqrt h
    _ = B * Real.sqrt m := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]

lemma le_nrm_of_sq (S : Finset ℤ) (f : ℤ → ℝ) (B m : ℝ) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (h : B ^ 2 * m ≤ ∑ n ∈ S, f n ^ 2) : B * Real.sqrt m ≤ nrm S f := by
  unfold nrm
  calc B * Real.sqrt m = Real.sqrt (B ^ 2 * m) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
    _ ≤ _ := Real.sqrt_le_sqrt h

lemma nrm_sub_le (S : Finset ℤ) (a b : ℤ → ℝ) : |nrm S a - nrm S b| ≤ nrm S (fun n => a n - b n) :=
  abs_sqrt_sub_le S a b

/-- **E5 (the algebra of the matching)** (app_thmA Step 4 (b)). -/
theorem match_alg (Ω : Finset ℤ) (aL bR uL uR : ℤ → ℝ) (κ TL TR m K c e : ℝ)
    (hm : 0 < m) (hTL : 0 ≤ TL) (hTR : 0 < TR) (hc : 0 < c) (he : 0 ≤ e) (hK : 0 ≤ K) (hec : e ≤ c / 2)
    (hrel : ∀ n ∈ Ω, uL n = κ * uR n)
    (hA : ∑ n ∈ Ω, (uL n - aL n) ^ 2 ≤ (e * TL) ^ 2 * m)
    (hB : ∑ n ∈ Ω, (uR n - bR n) ^ 2 ≤ (e * TR) ^ 2 * m)
    (hL1 : ∑ n ∈ Ω, aL n ^ 2 ≤ (K * TL) ^ 2 * m) (hL0 : (c * TL) ^ 2 * m ≤ ∑ n ∈ Ω, aL n ^ 2)
    (hR1 : ∑ n ∈ Ω, bR n ^ 2 ≤ (K * TR) ^ 2 * m) (hR0 : (c * TR) ^ 2 * m ≤ ∑ n ∈ Ω, bR n ^ 2) :
    |κ| * TR ≤ (2 * (K + c / 2) / c) * TL ∧ TL ≤ (2 * (K + c / 2) / c) * (|κ| * TR) ∧
      |glueKappa aL bR Ω - κ| ≤ e * ((1 + 2 * (K + c / 2) / c) / c) * |κ| := by
  set S := Real.sqrt m with hS
  have hSp : 0 < S := Real.sqrt_pos.mpr hm
  have hK' : 0 ≤ K + c / 2 := by linarith
  -- norms
  have nA := nrm_le_of_sq Ω (fun n => uL n - aL n) (e * TL) m (by positivity) hm.le hA
  have nB := nrm_le_of_sq Ω (fun n => uR n - bR n) (e * TR) m (by positivity) hm.le hB
  have nL1 := nrm_le_of_sq Ω aL (K * TL) m (by positivity) hm.le hL1
  have nR1 := nrm_le_of_sq Ω bR (K * TR) m (by positivity) hm.le hR1
  have nL0 := le_nrm_of_sq Ω aL (c * TL) m (by positivity) hm.le hL0
  have nR0 := le_nrm_of_sq Ω bR (c * TR) m (by positivity) hm.le hR0
  have hdL := nrm_sub_le Ω uL aL
  have hdR := nrm_sub_le Ω uR bR
  have hrel' : nrm Ω uL = |κ| * nrm Ω uR := by
    rw [← nrm_smul]; exact nrm_congr Ω _ _ hrel
  -- bounds for the norms of uL, uR
  have uL_up : nrm Ω uL ≤ (K + e) * TL * S := by
    have := (abs_le.mp hdL).2
    have e1 : (K + e) * TL * S = K * TL * S + e * TL * S := by ring
    linarith
  have uL_lo : (c - e) * TL * S ≤ nrm Ω uL := by
    have := (abs_le.mp hdL).1
    have e1 : (c - e) * TL * S = c * TL * S - e * TL * S := by ring
    linarith
  have uR_up : nrm Ω uR ≤ (K + e) * TR * S := by
    have := (abs_le.mp hdR).2
    have e1 : (K + e) * TR * S = K * TR * S + e * TR * S := by ring
    linarith
  have uR_lo : (c - e) * TR * S ≤ nrm Ω uR := by
    have := (abs_le.mp hdR).1
    have e1 : (c - e) * TR * S = c * TR * S - e * TR * S := by ring
    linarith
  have hce : c / 2 ≤ c - e := by linarith
  have hKe : K + e ≤ K + c / 2 := by linarith
  -- (1)
  have h1 : |κ| * TR ≤ (2 * (K + c / 2) / c) * TL := by
    have e2 : ((|κ| * TR) * (c / 2)) * S ≤ ((K + c / 2) * TL) * S := by
      calc ((|κ| * TR) * (c / 2)) * S = |κ| * ((c / 2) * TR * S) := by ring
        _ ≤ |κ| * ((c - e) * TR * S) := by gcongr
        _ ≤ |κ| * nrm Ω uR := mul_le_mul_of_nonneg_left uR_lo (abs_nonneg _)
        _ = nrm Ω uL := hrel'.symm
        _ ≤ (K + e) * TL * S := uL_up
        _ ≤ ((K + c / 2) * TL) * S := by gcongr
    have e3 : (|κ| * TR) * (c / 2) ≤ (K + c / 2) * TL := le_of_mul_le_mul_right e2 hSp
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  -- (2)
  have h2 : TL ≤ (2 * (K + c / 2) / c) * (|κ| * TR) := by
    have e2 : (TL * (c / 2)) * S ≤ ((|κ| * TR) * (K + c / 2)) * S := by
      calc (TL * (c / 2)) * S = (c / 2) * TL * S := by ring
        _ ≤ (c - e) * TL * S := by gcongr
        _ ≤ nrm Ω uL := uL_lo
        _ = |κ| * nrm Ω uR := hrel'
        _ ≤ |κ| * ((K + e) * TR * S) := mul_le_mul_of_nonneg_left uR_up (abs_nonneg _)
        _ ≤ |κ| * ((K + c / 2) * TR * S) := by gcongr
        _ = ((|κ| * TR) * (K + c / 2)) * S := by ring
    have e3 : TL * (c / 2) ≤ (|κ| * TR) * (K + c / 2) := le_of_mul_le_mul_right e2 hSp
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  refine ⟨h1, h2, ?_⟩
  -- (3)
  have hbpos : 0 < ∑ n ∈ Ω, bR n ^ 2 := by
    have : 0 < (c * TR) ^ 2 * m := by positivity
    linarith
  have hg := glueKappa_sub_le aL bR Ω κ hbpos
  have hnum : Real.sqrt (∑ n ∈ Ω, (aL n - κ * bR n) ^ 2) ≤ (e * TL + |κ| * (e * TR)) * S := by
    have hd : nrm Ω (fun n => aL n - κ * bR n) ≤ nrm Ω (fun n => aL n - uL n) + nrm Ω (fun n => κ * (uR n - bR n)) := by
      have := sqrt_sum_add_le Ω (fun n => aL n - uL n) (fun n => κ * (uR n - bR n))
      unfold nrm
      refine le_trans (le_of_eq ?_) this
      congr 1
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [hrel n hn]; ring_nf
    have hd1 : nrm Ω (fun n => aL n - uL n) ≤ e * TL * S := by
      have : nrm Ω (fun n => aL n - uL n) = nrm Ω (fun n => uL n - aL n) := by
        unfold nrm; congr 1; exact Finset.sum_congr rfl (fun n _ => by ring)
      rw [this]; exact nA
    have hd2 : nrm Ω (fun n => κ * (uR n - bR n)) ≤ |κ| * (e * TR * S) := by
      rw [nrm_smul]; exact mul_le_mul_of_nonneg_left nB (abs_nonneg _)
    show nrm Ω (fun n => aL n - κ * bR n) ≤ _
    linarith
  have hden : c * TR * S ≤ Real.sqrt (∑ n ∈ Ω, bR n ^ 2) := nR0
  have hpos : 0 < c * TR * S := by positivity
  refine hg.trans ?_
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hden)]
  have hfin : (e * TL + |κ| * (e * TR)) * S ≤
      (e * ((1 + 2 * (K + c / 2) / c) / c) * |κ|) * (c * TR * S) := by
    have hTL2 : TL ≤ (2 * (K + c / 2) / c) * (|κ| * TR) := h2
    have : (e * TL + |κ| * (e * TR)) ≤ e * (1 + 2 * (K + c / 2) / c) * (|κ| * TR) := by
      nlinarith [mul_le_mul_of_nonneg_left hTL2 he]
    calc (e * TL + |κ| * (e * TR)) * S ≤ (e * (1 + 2 * (K + c / 2) / c) * (|κ| * TR)) * S :=
          mul_le_mul_of_nonneg_right this hSp.le
      _ = (e * ((1 + 2 * (K + c / 2) / c) / c) * |κ|) * (c * TR * S) := by field_simp
  calc Real.sqrt (∑ n ∈ Ω, (aL n - κ * bR n) ^ 2) ≤ (e * TL + |κ| * (e * TR)) * S := hnum
    _ ≤ _ := hfin
    _ ≤ (e * ((1 + 2 * (K + c / 2) / c) / c) * |κ|) * Real.sqrt (∑ n ∈ Ω, bR n ^ 2) := by
        apply mul_le_mul_of_nonneg_left hden
        have : 0 ≤ (1 + 2 * (K + c / 2) / c) / c := by positivity
        positivity

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.match_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms match_alg

end FormalResearch.JacobiEigenvectors.TheoremA

end

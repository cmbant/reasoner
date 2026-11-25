module

public import FormalResearch.JacobiEigenvectors.Engine.Defect
public import FormalResearch.JacobiEigenvectors.Engine.VolterraMulti

/-!
# Paper J engine, JE6: ladder pairs and the stability theorem (`thm:eng-volterra`(b))

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, `thm:eng-volterra`(b) (ladder pairs), with the
identities of `thm:eng-defect` (`Defect`) and the multi-patch theorem `volterra_multi` (`VolterraMulti`).

## Dictionary
* The comparison pair of patch `p` is `φ^{(α)}_p = ladderPairFun AA BB wf γ h α p`, the sequence
  `k ↦ v(u_k,h)·𝐰^{(α)}_p(u_k)` at `u_k = (k+γ)h` with `v = (A, hB)` (`ladderSeq`); `ladderA`, `ladderQ` are the
  bond and diagonal coefficients `𝒜_h(s_k)`, `𝒬_h(u_k)` of the sequence operator.
* `ω_* = |ω_mod(h)|`, `c₋ = cm`, `K = (K_A + K_B) K_w`, `ε = 2 K_𝔇 K_w h^m`, and `Θ_h = (h/ω_*) ∑ ρ_k M_k²` is the
  `volTheta` of `VolterraMulti`, so `εΘ = 2K_𝔇K_w h^m Θ_h` as in the paper.

## Statements formalised
* `ladder_S1` (S1): `c₋ |ω_mod(h)| ≤ |𝒲_k(φ¹,φ²)|` from the ladder identity `𝒲_j = ω_mod 𝓕_cas` (`casSite_eq_omega_Fcas`)
  and `|𝓕_cas| ≥ c₋` (no bond hypothesis: the lower shift at `k+1 ≥ 1` is in the ladder).
* `ladder_S2` (S2): `|ψ̂^{(α)}_k| ≤ (K_A + K_B) K_w W^{±1}_k M_k`, from `|A| ≤ K_A`, `|hBρ/ρ̃| ≤ K_B` and the envelopes
  `|𝐰^{(α)}| ≤ K_w W^{±1} M`, `ρ̃|𝐰̃^{(α)}| ≤ K_w ρ W^{±1} M`.
* `residual_of_defect`, `ladder_residual_interior`, `ladder_residual_hard` (R): `|(L_h ψ̂^{(α)})_k| ≤ ε ρ_k W^{±1}_k M_k`,
  from `thm:eng-defect`(1) (`defect_identity_interior` for `k ≥ 1`, both `α`; `defect_identity_hard` for `k = 0` and `α = 1`
  under `𝒟₋(u₀,h) = 0` and `Π₋ 𝐰⁽¹⁾₀ = 0`).
* `ladder_pair_data`: the bounds (S1), (S2), (R) for the ladder pairs of all patches, proved from the hypotheses
  (eq:eng-UC1) and the envelopes of `𝐰_p` (the part of the stability theorem that does not involve (S3)).
* `ladder_pair_stability`: `volterra_multi` for the ladder pairs, with (S1), (S2), (R) from `ladder_pair_data` and the
  transfer condition (S3) a hypothesis `hT` (bounded-overlap case); the conclusions are those of `volterra_multi` with the
  constants above.
* `ladder_pair_stability_forbidden`: the same with `hT` replaced by the forbidden-overlap conditions (`𝒜_{j_p} > 0`,
  `W_{j_p+1} ≤ C_w W_{j_p}`, `𝒜_{j_p} M_{j_p} M_{j_p+1} ≤ C_ω |ω_mod|`), from which (S3) is derived
  (`transfer_of_forbidden_overlap` in `VolterraMulti`).

## Differences from the paper (all stated in the report)
1. (eq:eng-UC1) and the lower bound `|𝓕_cas| ≥ c₋` are assumed at every lattice site `k ≥ 0` (the paper: interior sites);
   at the hard-edge site they are needed for the first pair.
2. The sup norms `‖A‖_∞`, `‖hBρ/ρ̃‖_∞` are replaced by explicit bounds `K_A, K_B` on the sites `k ≥ 0`.
3. The transfer condition (S3) of the ladder-pair transfer matrices is a hypothesis `hT` in `ladder_pair_stability`
   (derived from the charts in the paper's bounded-overlap case, which is not formalised) and is derived from
   comparability conditions at forbidden overlaps in `ladder_pair_stability_forbidden`.
4. The model ladders `𝐰_p` enter through `SymplecticLadder γ dd d2 pp qq PiP PiM (wf p) ω`: the same `Π±`, `𝒟`, `ω_mod` for all
   patches, with the relations (SM1), (SM2) for `h > 0` only (see `Defect`).  No instance of
   `ladder_pair_stability(_forbidden)` is formalised: the hypotheses are not shown to be jointly satisfiable by a
   concrete ladder (`constant_ladder` of `Defect` has `𝒟 = 1` and no hard edge).
5. The residual at the hard-edge site is claimed for `α = 1` only (the paper: `r²_{1,0}` not required).
6. The defect bounds and envelopes are hypotheses: the charts of Section 3 (which supply the envelopes for the Weber and
   parabolic-cylinder ladders) are not formalised.  The defect order of the correctors (`thm:eng-corr`) is formalised in
   `Engine/Corrector.lean` (`eng_corr`, `eng_corr_full`, `eng_corr_site`), but the link from its conclusion
   (`O(h^{m+1})` for `defectRow`) to the sitewise bounds `|𝔄^tot| ≤ K_D h^{m+1} ρ_k` with the chart weights `ρ_k` is not formalised.

No new analysis: the corollary is `volterra_multi` with the three bounds discharged.
-/

@[expose] public section

open Finset

namespace FormalResearch.JacobiEigenvectors.Engine

/-- The comparison sequence of a ladder pair: `ψ̂^{(α)}_k = v(u_k,h)·𝐰^{(α)}(u_k)` at `u_k = (k+γ)h`. -/
noncomputable def ladderSeq (AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (γ h : ℝ) (α : Fin 2) (k : ℤ) : ℝ :=
  dot (vrow AA BB (((k : ℝ) + γ) * h) h) (w α (((k : ℝ) + γ) * h) h)

/-- The bond coefficient `𝒜_h(s_k)` of the sequence operator at `u_k = (k+γ)h`. -/
noncomputable def ladderA (dd pp : ℝ → ℝ → ℝ) (γ h : ℝ) (k : ℤ) : ℝ :=
  bondUp dd pp (((k : ℝ) + γ) * h) h

/-- The diagonal coefficient `𝒬_h(u_k)` of the sequence operator at `u_k = (k+γ)h`. -/
noncomputable def ladderQ (qq : ℝ → ℝ → ℝ) (γ h : ℝ) (k : ℤ) : ℝ :=
  qq (((k : ℝ) + γ) * h) h

lemma isSite_of_nonneg {γ h : ℝ} (k : ℤ) (hk : 0 ≤ k) : IsSite γ h (((k : ℝ) + γ) * h) := by
  refine ⟨k.toNat, ?_⟩
  have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  rw [this]

lemma isSitePos_of_pos {γ h : ℝ} (k : ℤ) (hk : 1 ≤ k) : IsSitePos γ h (((k : ℝ) + γ) * h) := by
  refine ⟨k.toNat, by omega, ?_⟩
  have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [this]

/-- The Casoratian of a ladder pair is the site Casoratian `casSite` (`thm:eng-defect`(3a) left side). -/
lemma ladder_cas_eq (dd pp AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (γ h : ℝ) (k : ℤ) :
    cas (ladderA dd pp γ h) (ladderSeq AA BB w γ h 0) (ladderSeq AA BB w γ h 1) k
      = casSite dd pp AA BB w (((k : ℝ) + γ) * h) h := by
  have e1 : (((k + 1 : ℤ) : ℝ) + γ) * h = ((k : ℝ) + γ) * h + h := by push_cast; ring
  unfold cas casSite ladderA ladderSeq
  rw [e1]

/-- **(S1)** of `thm:eng-volterra`(b): the lower Casoratian bound `|𝒲_k(φ¹,φ²)| ≥ c_- |ω_mod|` from the
ladder identity `𝒲 = ω_mod 𝓕_cas` (`casSite_eq_omega_Fcas`) and `|𝓕_cas| ≥ c_-`. -/
theorem ladder_S1 {γ h c : ℝ} {ω : ℝ → ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2} {w : Fin 2 → ℝ → ℝ → V2}
    (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (AA BB : ℝ → ℝ → ℝ) (hh : 0 < h) (k : ℤ) (hk : 0 ≤ k)
    (hF : c ≤ |Fcas pp AA BB PiM (((k : ℝ) + γ) * h + h / 2) h|) :
    |ω h| * c ≤ |cas (ladderA dd pp γ h) (ladderSeq AA BB w γ h 0) (ladderSeq AA BB w γ h 1) k| := by
  rw [ladder_cas_eq, casSite_eq_omega_Fcas L _ _ hh (isSite_of_nonneg k hk), abs_mul]
  exact mul_le_mul_of_nonneg_left hF (abs_nonneg _)

/-- **(S2)** envelope of a ladder pair: `|ψ̂^{(α)}_k| ≤ (K_A + K_B) K_w W^{±} M` from `|A| ≤ K_A`,
`|h B ρ/ρ̃| ≤ K_B`, and the envelopes `|𝐰^{(α)}| ≤ K_w W^{±} M`, `ρ̃|𝐰̃^{(α)}| ≤ K_w ρ W^{±} M`. -/
theorem ladder_S2 (AA BB : ℝ → ℝ → ℝ) (w : Fin 2 → ℝ → ℝ → V2) (γ h : ℝ) (α : Fin 2) (k : ℤ)
    (KA KB Kw Wα Mk ρk ρtk : ℝ) (hKw : 0 ≤ Kw) (hWα : 0 ≤ Wα) (hMk : 0 ≤ Mk) (hρk : 0 ≤ ρk)
    (hρtk : 0 < ρtk)
    (hA : |AA (((k : ℝ) + γ) * h) h| ≤ KA)
    (hB : |h * BB (((k : ℝ) + γ) * h) h| * (ρk / ρtk) ≤ KB)
    (hw0 : |w α (((k : ℝ) + γ) * h) h 0| ≤ Kw * Wα * Mk)
    (hw1 : ρtk * |w α (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρk * Wα * Mk) :
    |ladderSeq AA BB w γ h α k| ≤ (KA + KB) * Kw * Wα * Mk := by
  simp only [ladderSeq, dot, vrow, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hKA : 0 ≤ KA := (abs_nonneg _).trans hA
  have hKB : 0 ≤ KB := (mul_nonneg (abs_nonneg _) (div_nonneg hρk hρtk.le)).trans hB
  have hZ : 0 ≤ Kw * Wα * Mk := mul_nonneg (mul_nonneg hKw hWα) hMk
  have hw1' : |w α (((k : ℝ) + γ) * h) h 1| ≤ (Kw * ρk * Wα * Mk) / ρtk := by
    rw [le_div_iff₀ hρtk]
    linarith [hw1]
  have t0 : |AA (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 0|
      ≤ KA * (Kw * Wα * Mk) := by
    rw [abs_mul]
    exact mul_le_mul hA hw0 (abs_nonneg _) hKA
  have t1 : |h * BB (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 1|
      ≤ KB * (Kw * Wα * Mk) := by
    rw [abs_mul]
    calc |h * BB (((k : ℝ) + γ) * h) h| * |w α (((k : ℝ) + γ) * h) h 1|
        ≤ |h * BB (((k : ℝ) + γ) * h) h| * ((Kw * ρk * Wα * Mk) / ρtk) :=
          mul_le_mul_of_nonneg_left hw1' (abs_nonneg _)
      _ = (|h * BB (((k : ℝ) + γ) * h) h| * (ρk / ρtk)) * (Kw * Wα * Mk) := by ring
      _ ≤ KB * (Kw * Wα * Mk) := mul_le_mul_of_nonneg_right hB hZ
  calc |AA (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 0
        + h * BB (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 1|
      ≤ |AA (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 0|
        + |h * BB (((k : ℝ) + γ) * h) h * w α (((k : ℝ) + γ) * h) h 1| := abs_add_le _ _
    _ ≤ KA * (Kw * Wα * Mk) + KB * (Kw * Wα * Mk) := add_le_add t0 t1
    _ = (KA + KB) * Kw * Wα * Mk := by ring

/-- **Residual of a ladder pair** from the defect identity: if `L_h ψ̂ = (𝔄 w₀ + 𝔅 w̃₀)/h` with `|𝔄| ≤ K_𝔇 h^{m+1} ρ`,
`|𝔅| ≤ K_𝔇 h^{m+1} ρ̃`, `|w₀| ≤ K_w W^{±} M`, `ρ̃|w̃| ≤ K_w ρ W^{±} M`, then `|(L_h ψ̂)_k| ≤ ε ρ W^{±} M` with
`ε = 2 K_𝔇 K_w h^m` (the paper's `ε` of `thm:eng-volterra`(b)). -/
theorem residual_of_defect (h : ℝ) (m : ℕ) (KD Kw Lval D0 D1 w0 w1 ρk ρtk Wα Mk : ℝ) (hh : 0 < h)
    (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw) (hρk : 0 ≤ ρk) (hWα : 0 ≤ Wα) (hMk : 0 ≤ Mk)
    (hid : Lval = D0 * w0 + D1 * w1)
    (hD0 : |D0| ≤ KD * h ^ (m + 1) * ρk) (hD1 : |D1| ≤ KD * h ^ (m + 1) * ρtk)
    (hw0 : |w0| ≤ Kw * Wα * Mk) (hw1 : ρtk * |w1| ≤ Kw * ρk * Wα * Mk) :
    |h⁻¹ * Lval| ≤ 2 * KD * Kw * h ^ m * (ρk * Wα * Mk) := by
  have hP : 0 ≤ KD * h ^ (m + 1) := mul_nonneg hKD (pow_nonneg hh.le _)
  have t0 : |D0| * |w0| ≤ (KD * h ^ (m + 1) * ρk) * (Kw * Wα * Mk) :=
    mul_le_mul hD0 hw0 (abs_nonneg _) (mul_nonneg hP hρk)
  have t1 : |D1| * |w1| ≤ (KD * h ^ (m + 1)) * (Kw * ρk * Wα * Mk) := by
    calc |D1| * |w1| ≤ (KD * h ^ (m + 1) * ρtk) * |w1| := mul_le_mul_of_nonneg_right hD1 (abs_nonneg _)
      _ = (KD * h ^ (m + 1)) * (ρtk * |w1|) := by ring
      _ ≤ (KD * h ^ (m + 1)) * (Kw * ρk * Wα * Mk) := mul_le_mul_of_nonneg_left hw1 hP
  have hsum : |D0 * w0 + D1 * w1| ≤ |D0| * |w0| + |D1| * |w1| := by
    have := abs_add_le (D0 * w0) (D1 * w1)
    rw [abs_mul, abs_mul] at this
    exact this
  have key : |D0| * |w0| + |D1| * |w1| ≤ 2 * ((KD * h ^ (m + 1)) * (Kw * ρk * Wα * Mk)) := by
    have e1 : (KD * h ^ (m + 1) * ρk) * (Kw * Wα * Mk) = (KD * h ^ (m + 1)) * (Kw * ρk * Wα * Mk) := by ring
    rw [e1] at t0
    linarith [t0, t1]
  have hinv : 0 ≤ h⁻¹ := (inv_pos.mpr hh).le
  rw [hid, abs_mul, abs_of_nonneg hinv]
  calc h⁻¹ * |D0 * w0 + D1 * w1|
      ≤ h⁻¹ * (2 * ((KD * h ^ (m + 1)) * (Kw * ρk * Wα * Mk))) :=
        mul_le_mul_of_nonneg_left (le_trans hsum key) hinv
    _ = 2 * KD * Kw * h ^ m * (ρk * Wα * Mk) := by
        rw [pow_succ]
        field_simp

/-- **(R)** the residual of a ladder pair at an interior site `k ≥ 1` (`thm:eng-defect`(1) and `residual_of_defect`). -/
theorem ladder_residual_interior {γ h : ℝ} {ω : ℝ → ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    {w : Fin 2 → ℝ → ℝ → V2} (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (AA BB : ℝ → ℝ → ℝ)
    (α : Fin 2) (k : ℤ) (hk : 1 ≤ k) (hh : 0 < h) (m : ℕ) (KD Kw ρk ρtk Wα Mk : ℝ)
    (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw) (hρk : 0 ≤ ρk) (hWα : 0 ≤ Wα) (hMk : 0 ≤ Mk)
    (hD0 : |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 0| ≤ KD * h ^ (m + 1) * ρk)
    (hD1 : |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 1| ≤ KD * h ^ (m + 1) * ρtk)
    (hw0 : |w α (((k : ℝ) + γ) * h) h 0| ≤ Kw * Wα * Mk)
    (hw1 : ρtk * |w α (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρk * Wα * Mk) :
    |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderSeq AA BB w γ h α) k|
      ≤ 2 * KD * Kw * h ^ m * (ρk * Wα * Mk) := by
  have hLop : Lop (ladderA dd pp γ h) (ladderQ qq γ h) (ladderSeq AA BB w γ h α) k
      = siteLop dd pp qq AA BB w α (((k : ℝ) + γ) * h) h :=
    Lop_seq_eq_siteLop dd pp qq AA BB w α γ h k
  have hid := defect_identity_interior L AA BB α (((k : ℝ) + γ) * h) h hh (isSitePos_of_pos k hk)
  unfold Lh
  rw [hLop]
  exact residual_of_defect h m KD Kw _ _ _ _ _ ρk ρtk Wα Mk hh hKD hKw hρk hWα hMk hid hD0 hD1 hw0 hw1

/-- **(R)** the residual of the first pair at the hard-edge site `k = 0` (`defect_identity_hard`, with the hard-edge
annihilation `Π₋ 𝐰⁽¹⁾₀ = 0` and `𝒟₋(u₀,h) = 0`). -/
theorem ladder_residual_hard {γ h : ℝ} {ω : ℝ → ℝ} {dd d2 pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
    {w : Fin 2 → ℝ → ℝ → V2} (L : SymplecticLadder γ dd d2 pp qq PiP PiM w ω) (AA BB : ℝ → ℝ → ℝ)
    (hh : 0 < h) (m : ℕ) (KD Kw ρk ρtk Wα Mk : ℝ)
    (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw) (hρk : 0 ≤ ρk) (hWα : 0 ≤ Wα) (hMk : 0 ≤ Mk)
    (hD : Dm dd (γ * h) h = 0) (hann : colMul (PiM (γ * h) h) (w 0 (γ * h) h) = 0)
    (hD0 : |defectRow pp qq AA BB PiP PiM (γ * h) h 0| ≤ KD * h ^ (m + 1) * ρk)
    (hD1 : |defectRow pp qq AA BB PiP PiM (γ * h) h 1| ≤ KD * h ^ (m + 1) * ρtk)
    (hw0 : |w 0 (γ * h) h 0| ≤ Kw * Wα * Mk)
    (hw1 : ρtk * |w 0 (γ * h) h 1| ≤ Kw * ρk * Wα * Mk) :
    |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderSeq AA BB w γ h 0) 0|
      ≤ 2 * KD * Kw * h ^ m * (ρk * Wα * Mk) := by
  have hLop0 : Lop (ladderA dd pp γ h) (ladderQ qq γ h) (ladderSeq AA BB w γ h 0) 0
      = siteLop dd pp qq AA BB w 0 ((((0 : ℤ) : ℝ) + γ) * h) h :=
    Lop_seq_eq_siteLop dd pp qq AA BB w 0 γ h 0
  have e0 : (((0 : ℤ) : ℝ) + γ) * h = γ * h := by simp
  have hLop : Lop (ladderA dd pp γ h) (ladderQ qq γ h) (ladderSeq AA BB w γ h 0) 0
      = siteLop dd pp qq AA BB w 0 (γ * h) h := by
    rw [hLop0, e0]
  have hid := defect_identity_hard L AA BB 0 (γ * h) h hh (by simp) hD hann
  unfold Lh
  rw [hLop]
  exact residual_of_defect h m KD Kw _ _ _ _ _ ρk ρtk Wα Mk hh hKD hKw hρk hWα hMk hid hD0 hD1 hw0 hw1

/-- The comparison pairs of a family of ladder pairs, one per patch: `φ^{(α)}_p = ψ̂^{(α)}` built from `𝐰_p`. -/
noncomputable def ladderPairFun (AA BB : ℝ → ℝ → ℝ) (wf : ℕ → Fin 2 → ℝ → ℝ → V2) (γ h : ℝ) (α : Fin 2) :
    ℕ → ℤ → ℝ :=
  fun p k => ladderSeq AA BB (wf p) γ h α k

lemma eqLo_nonneg_of (s0 : ℤ) (jj : ℕ → ℤ) (p : ℕ) (hs0 : 0 ≤ s0) (hj : 0 ≤ jj (p - 1)) :
    0 ≤ eqLo s0 jj p := by
  unfold eqLo
  split_ifs
  · exact hs0
  · omega

lemma eqLo_ge_jj_of (s0 : ℤ) (jj : ℕ → ℤ) (p : ℕ) (hs0 : 0 ≤ s0) (hj0 : jj 0 = 0) (hjp : 0 ≤ jj (p - 1)) :
    jj (p - 1) ≤ eqLo s0 jj p := by
  unfold eqLo
  split_ifs with h1
  · subst h1
    simp only [Nat.sub_self, hj0]
    exact hs0
  · omega

lemma eqLo_ge_one_of (s0 : ℤ) (jj : ℕ → ℤ) (p : ℕ) (hp : p ≠ 1) (hj : 0 ≤ jj (p - 1)) :
    1 ≤ eqLo s0 jj p := by
  unfold eqLo
  rw [ite_eq_right hp]
  omega

/-- **The bounds (S1), (S2), (R) of a family of ladder pairs** (`thm:eng-volterra`(b)): for the pairs
`φ^{(α)}_p = v·𝐰^{(α)}_p` of one row `v = (A,hB)` and the model ladders `𝐰_p`, the lower Casoratian bound with
`ω_* = |ω_mod(h)|`, `c₋ = cm`; the envelopes with `K = (K_A+K_B)K_w`; and the residuals with `ε = 2K_𝔇K_w h^m`, from the
defect bounds (eq:eng-UC1) and the envelopes of `𝐰_p`.  This is the part of `ladder_pair_stability` that does not
involve the transfer condition (S3). -/
theorem ladder_pair_data (γ h cm KD Kw KA KB : ℝ) (m : ℕ) (dd pp qq : ℝ → ℝ → ℝ) {d2 : ℝ → ℝ → ℝ}
    (PiP PiM : ℝ → ℝ → M2) (ω : ℝ → ℝ) (AA BB : ℝ → ℝ → ℝ) (wf : ℕ → Fin 2 → ℝ → ℝ → V2)
    (ρ ρt W M : ℤ → ℝ) (s0 NR : ℤ) (P : ℕ) (jj : ℕ → ℤ)
    (hh : 0 < h) (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw)
    (hL : ∀ p, SymplecticLadder γ dd d2 pp qq PiP PiM (wf p) ω)
    (hjj0 : jj 0 = 0) (hjjmono : ∀ p < P, jj p < jj (p + 1)) (hjjP : jj P = NR - 1)
    (hs0 : s0 = 0 ∨ s0 = 1)
    (hρ : ∀ k, 0 ≤ ρ k) (hρt : ∀ k : ℤ, 0 ≤ k → 0 < ρt k)
    (hMpos : ∀ j ∈ Icc 0 NR, 0 < M j) (hWpos : ∀ j ∈ Icc 0 NR, 0 < W j)
    (hUCa : ∀ k : ℤ, 0 ≤ k → cm ≤ |Fcas pp AA BB PiM (((k : ℝ) + γ) * h + h / 2) h|)
    (hUCb : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 0| ≤ KD * h ^ (m + 1) * ρ k)
    (hUCc : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 1| ≤ KD * h ^ (m + 1) * ρt k)
    (hKa : ∀ k : ℤ, 0 ≤ k → |AA (((k : ℝ) + γ) * h) h| ≤ KA)
    (hKb : ∀ k : ℤ, 0 ≤ k → |h * BB (((k : ℝ) + γ) * h) h| * (ρ k / ρt k) ≤ KB)
    (henv : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (jj (p - 1)) (jj p + 1),
      |wf p 0 (((k : ℝ) + γ) * h) h 0| ≤ Kw * W k * M k ∧
      |wf p 1 (((k : ℝ) + γ) * h) h 0| ≤ Kw * (W k)⁻¹ * M k ∧
      ρt k * |wf p 0 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * W k * M k ∧
      ρt k * |wf p 1 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * (W k)⁻¹ * M k)
    (hDhard : s0 = 0 → Dm dd (γ * h) h = 0)
    (hannih : s0 = 0 → colMul (PiM (γ * h) h) (wf 1 0 (γ * h) h) = 0) :
    0 < |ω h| ∧ (s0 = 0 → ladderA dd pp γ h (-1) = 0) ∧
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p),
      cm * |ω h| ≤ |cas (ladderA dd pp γ h) (ladderPairFun AA BB wf γ h 0 p) (ladderPairFun AA BB wf γ h 1 p) j|) ∧
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1),
      |ladderPairFun AA BB wf γ h 0 p j| ≤ (KA + KB) * Kw * W j * M j) ∧
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1),
      |ladderPairFun AA BB wf γ h 1 p j| ≤ (KA + KB) * Kw * (W j)⁻¹ * M j) ∧
    (∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p),
      |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderPairFun AA BB wf γ h 0 p) k|
        ≤ 2 * KD * Kw * h ^ m * ρ k * W k * M k) ∧
    (∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k ≠ 0 →
      |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderPairFun AA BB wf γ h 1 p) k|
        ≤ 2 * KD * Kw * h ^ m * ρ k * (W k)⁻¹ * M k) := by
  have hjjge : ∀ p, p ≤ P → 0 ≤ jj p := fun p hp => by
    have := jj_mono_le jj P hjjmono 0 p (Nat.zero_le _) hp
    rw [hjj0] at this
    exact this
  have hjjle : ∀ p, p ≤ P → jj p ≤ NR - 1 := fun p hp => by
    have := jj_mono_le jj P hjjmono p P hp le_rfl
    rw [hjjP] at this
    exact this
  have hs0nn : 0 ≤ s0 := by rcases hs0 with h0 | h0 <;> omega
  have hsiteNR : ∀ p, p ≤ P → 0 ≤ jj p ∧ jj p + 1 ≤ NR := fun p hp =>
    ⟨hjjge p hp, by have := hjjle p hp; omega⟩
  have hsite0 : ∀ p, 1 ≤ p → p ≤ P → 0 ≤ jj (p - 1) := fun p hp1 hpP => hjjge (p - 1) (by omega)
  have hNR1 : 1 ≤ NR := by
    have h1 := hjjge P le_rfl
    rw [hjjP] at h1
    omega
  have hωpos : 0 < |ω h| := abs_pos.mpr ((hL 1).wronsk_ne h hh)
  have hA : s0 = 0 → ladderA dd pp γ h (-1) = 0 := by
    intro h0
    have e : ((((-1 : ℤ) : ℝ) + γ) * h) = γ * h - h := by push_cast; ring
    unfold ladderA
    rw [e, bondUp_sub]
    unfold bondDn
    rw [hDhard h0, mul_zero]
  have hS1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p),
      cm * |ω h| ≤ |cas (ladderA dd pp γ h) (ladderPairFun AA BB wf γ h 0 p) (ladderPairFun AA BB wf γ h 1 p) j| := by
    intro p hp j hj
    have hpP := (mem_Icc.mp hp)
    have hj0 : 0 ≤ j := le_trans (hsite0 p hpP.1 hpP.2) (mem_Icc.mp hj).1
    have := ladder_S1 (hL p) AA BB hh j hj0 (hUCa j hj0)
    rw [mul_comm] at this
    exact this
  have hφ1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1),
      |ladderPairFun AA BB wf γ h 0 p j| ≤ (KA + KB) * Kw * W j * M j := by
    intro p hp j hj
    have hj0 : 0 ≤ j := le_trans (hsite0 p (mem_Icc.mp hp).1 (mem_Icc.mp hp).2) (mem_Icc.mp hj).1
    have hWj := hWpos j (mem_Icc.mpr ⟨hj0, by have := (mem_Icc.mp hj).2; have := hsiteNR p (mem_Icc.mp hp).2; omega⟩)
    have hMj := hMpos j (mem_Icc.mpr ⟨hj0, by have := (mem_Icc.mp hj).2; have := hsiteNR p (mem_Icc.mp hp).2; omega⟩)
    obtain ⟨e0, _, e2, _⟩ := henv p hp j hj
    exact ladder_S2 AA BB (wf p) γ h 0 j KA KB Kw (W j) (M j) (ρ j) (ρt j) hKw hWj.le hMj.le (hρ j)
      (hρt j hj0) (hKa j hj0) (hKb j hj0) e0 e2
  have hwin : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k ∈ Icc (jj (p - 1)) (jj p + 1) := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    have hlow := eqLo_ge_jj_of s0 jj p hs0nn hjj0 (hsite0 p hpP.1 hpP.2)
    exact mem_Icc.mpr ⟨le_trans hlow (mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩
  have hφ2 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1),
      |ladderPairFun AA BB wf γ h 1 p j| ≤ (KA + KB) * Kw * (W j)⁻¹ * M j := by
    intro p hp j hj
    have hj0 : 0 ≤ j := le_trans (hsite0 p (mem_Icc.mp hp).1 (mem_Icc.mp hp).2) (mem_Icc.mp hj).1
    have hWj := hWpos j (mem_Icc.mpr ⟨hj0, by have := (mem_Icc.mp hj).2; have := hsiteNR p (mem_Icc.mp hp).2; omega⟩)
    have hMj := hMpos j (mem_Icc.mpr ⟨hj0, by have := (mem_Icc.mp hj).2; have := hsiteNR p (mem_Icc.mp hp).2; omega⟩)
    obtain ⟨_, e1, _, e3⟩ := henv p hp j hj
    exact ladder_S2 AA BB (wf p) γ h 1 j KA KB Kw ((W j)⁻¹) (M j) (ρ j) (ρt j) hKw
      (inv_nonneg.mpr hWj.le) hMj.le (hρ j) (hρt j hj0) (hKa j hj0) (hKb j hj0) e1 e3
  have hr1 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p),
      |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderPairFun AA BB wf γ h 0 p) k|
        ≤ 2 * KD * Kw * h ^ m * ρ k * W k * M k := by
    intro p hp k hk
    have hpP := mem_Icc.mp hp
    have hk0 : 0 ≤ k := le_trans (eqLo_nonneg_of s0 jj p hs0nn (hsite0 p hpP.1 hpP.2)) (mem_Icc.mp hk).1
    have hkw := hwin p hp k hk
    have hWk := hWpos k (mem_Icc.mpr ⟨hk0, by have := (mem_Icc.mp hkw).2; have := hsiteNR p hpP.2; omega⟩)
    have hMk := hMpos k (mem_Icc.mpr ⟨hk0, by have := (mem_Icc.mp hkw).2; have := hsiteNR p hpP.2; omega⟩)
    obtain ⟨e0, _, e2, _⟩ := henv p hp k hkw
    by_cases hk1 : 1 ≤ k
    · have hpart := ladder_residual_interior (hL p) AA BB 0 k hk1 hh m KD Kw (ρ k) (ρt k) (W k) (M k)
        hKD hKw (hρ k) hWk.le hMk.le (hUCb k hk0) (hUCc k hk0) e0 e2
      calc _ ≤ _ := hpart
        _ = _ := by ring
    · have hk00 : k = 0 := by omega
      subst hk00
      have hp1 : p = 1 := by
        by_contra hne
        have := eqLo_ge_one_of s0 jj p hne (hsite0 p hpP.1 hpP.2)
        have := (mem_Icc.mp hk).1
        omega
      subst hp1
      have hs0z : s0 = 0 := by
        have := (mem_Icc.mp hk).1
        rw [eqLo_one] at this
        omega
      have e00 : (((0 : ℤ) : ℝ) + γ) * h = γ * h := by simp
      have hD0 := hUCb 0 le_rfl
      rw [e00] at hD0
      have hD1 := hUCc 0 le_rfl
      rw [e00] at hD1
      have hw0 := e0
      rw [e00] at hw0
      have hw1 := e2
      rw [e00] at hw1
      have hpart := ladder_residual_hard (hL 1) AA BB hh m KD Kw (ρ 0) (ρt 0) (W 0) (M 0) hKD hKw (hρ 0)
        (hWpos 0 (mem_Icc.mpr ⟨le_rfl, by omega⟩)).le (hMpos 0 (mem_Icc.mpr ⟨le_rfl, by omega⟩)).le
        (hDhard hs0z) (hannih hs0z) hD0 hD1 hw0 hw1
      calc _ ≤ _ := hpart
        _ = _ := by ring
  have hr2 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k ≠ 0 →
      |Lh h (ladderA dd pp γ h) (ladderQ qq γ h) (ladderPairFun AA BB wf γ h 1 p) k|
        ≤ 2 * KD * Kw * h ^ m * ρ k * (W k)⁻¹ * M k := by
    intro p hp k hk hk0'
    have hpP := mem_Icc.mp hp
    have hk0 : 0 ≤ k := le_trans (eqLo_nonneg_of s0 jj p hs0nn (hsite0 p hpP.1 hpP.2)) (mem_Icc.mp hk).1
    have hkw := hwin p hp k hk
    have hWk := hWpos k (mem_Icc.mpr ⟨hk0, by have := (mem_Icc.mp hkw).2; have := hsiteNR p hpP.2; omega⟩)
    have hMk := hMpos k (mem_Icc.mpr ⟨hk0, by have := (mem_Icc.mp hkw).2; have := hsiteNR p hpP.2; omega⟩)
    obtain ⟨_, e1, _, e3⟩ := henv p hp k hkw
    have hk1 : 1 ≤ k := by
      have := (mem_Icc.mp hk).1
      have := eqLo_nonneg_of s0 jj p hs0nn (hsite0 p hpP.1 hpP.2)
      omega
    have hpart := ladder_residual_interior (hL p) AA BB 1 k hk1 hh m KD Kw (ρ k) (ρt k) ((W k)⁻¹) (M k)
      hKD hKw (hρ k) (inv_nonneg.mpr hWk.le) hMk.le (hUCb k hk0) (hUCc k hk0) e1 e3
    calc _ ≤ _ := hpart
      _ = _ := by ring
  exact ⟨hωpos, hA, hS1, hφ1, hφ2, hr1, hr2⟩

/-- **Ladder-pair stability** (`thm:eng-volterra`(b) combined with `thm:eng-volterra`(a), no new analysis).

The comparison pairs of patch `p` are the ladder pairs `φ^{(α)}_p = v(u_k,h)·𝐰^{(α)}_p(u_k)` of one row `v = (A, hB)`
and of the model ladders `𝐰_p` (one symplectic ladder structure per patch, `hL`, with the same `Π±`, `ω_mod`).  The
defect bounds (eq:eng-UC1) and the envelopes of `𝐰_p` give (S1) with `ω_* = |ω_mod(h)|`, `c₋ = cm`, (S2) with
`K = (K_A + K_B) K_w` and the residuals with `ε = 2 K_𝔇 K_w h^m`; then `volterra_multi` applies. -/
theorem ladder_pair_stability (γ h Λ CE cm KD Kw KA KB : ℝ) (m : ℕ) (dd pp qq : ℝ → ℝ → ℝ) {d2 : ℝ → ℝ → ℝ}
    (PiP PiM : ℝ → ℝ → M2) (ω : ℝ → ℝ) (AA BB : ℝ → ℝ → ℝ) (wf : ℕ → Fin 2 → ℝ → ℝ → V2)
    (ρ ρt W M ψ : ℤ → ℝ) (s0 NR : ℤ) (P : ℕ) (jj : ℕ → ℤ)
    (hh : 0 < h) (hcm : 0 < cm) (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) (hΛ : 1 ≤ Λ)
    (hL : ∀ p, SymplecticLadder γ dd d2 pp qq PiP PiM (wf p) ω)
    (hP : 1 ≤ P) (hjj0 : jj 0 = 0) (hjjmono : ∀ p < P, jj p < jj (p + 1)) (hjjP : jj P = NR - 1)
    (hs0 : s0 = 0 ∨ s0 = 1)
    (hρ : ∀ k, 0 ≤ ρ k) (hρt : ∀ k : ℤ, 0 ≤ k → 0 < ρt k)
    (hMpos : ∀ j ∈ Icc 0 NR, 0 < M j) (hWpos : ∀ j ∈ Icc 0 NR, 0 < W j)
    (hmono : ∀ k ∈ Icc 0 NR, ∀ j ∈ Icc 0 NR, k ≤ j → W k ≤ CE * W j)
    (hUCa : ∀ k : ℤ, 0 ≤ k → cm ≤ |Fcas pp AA BB PiM (((k : ℝ) + γ) * h + h / 2) h|)
    (hUCb : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 0| ≤ KD * h ^ (m + 1) * ρ k)
    (hUCc : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 1| ≤ KD * h ^ (m + 1) * ρt k)
    (hKa : ∀ k : ℤ, 0 ≤ k → |AA (((k : ℝ) + γ) * h) h| ≤ KA)
    (hKb : ∀ k : ℤ, 0 ≤ k → |h * BB (((k : ℝ) + γ) * h) h| * (ρ k / ρt k) ≤ KB)
    (henv : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (jj (p - 1)) (jj p + 1),
      |wf p 0 (((k : ℝ) + γ) * h) h 0| ≤ Kw * W k * M k ∧
      |wf p 1 (((k : ℝ) + γ) * h) h 0| ≤ Kw * (W k)⁻¹ * M k ∧
      ρt k * |wf p 0 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * W k * M k ∧
      ρt k * |wf p 1 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * (W k)⁻¹ * M k)
    (hDhard : s0 = 0 → Dm dd (γ * h) h = 0)
    (hannih : s0 = 0 → colMul (PiM (γ * h) h) (wf 1 0 (γ * h) h) = 0)
    (hT : ∀ p, 1 ≤ p → p < P → Λ⁻¹ ≤ |(transMat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p).det| ∧
      |transMat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p 0 0| ≤ Λ ∧
      |transMat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p 1 1| ≤ Λ ∧
      |transMat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p 0 1| ≤ Λ * (W (jj p) ^ 2)⁻¹ ∧
      |transMat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p 1 0| ≤ Λ * W (jj p) ^ 2)
    (hsol : ∀ k ∈ Icc s0 (NR - 1), Lh h (ladderA dd pp γ h) (ladderQ qq γ h) ψ k = 0)
    (hseed : ∀ j ∈ Icc 0 s0, ψ j = ladderPairFun AA BB wf γ h 0 1 j)
    (hsmall : 2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M
      ≤ mvCstar cm CE ((KA + KB) * Kw)) :
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |ψ j - psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j|
        ≤ mvC cm CE ((KA + KB) * Kw) Λ P * (2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M) * W j * M j) ∧
    (∀ p, 1 ≤ p → p < P → ∀ j ∈ Icc (jj p) (jj p + 1),
      psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j
        = psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj (p + 1) j) ∧
    (∀ j ∈ Icc 0 NR, ∃ p ∈ Icc 1 P,
      |ψ j - psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j|
        ≤ mvC cm CE ((KA + KB) * Kw) Λ P * (2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M) * W j * M j) := by
  obtain ⟨hωpos, hA, hS1, hφ1, hφ2, hr1, hr2⟩ := ladder_pair_data γ h cm KD Kw KA KB m dd pp qq PiP PiM ω AA BB
    wf ρ ρt W M s0 NR P jj hh hKD hKw hL hjj0 hjjmono hjjP hs0 hρ hρt hMpos hWpos hUCa hUCb hUCc hKa hKb henv
    hDhard hannih
  exact volterra_multi h (|ω h|) cm CE ((KA + KB) * Kw) (2 * KD * Kw * h ^ m) Λ (ladderA dd pp γ h)
    (ladderQ qq γ h) ψ ρ M W s0 NR P jj (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1)
    hh hωpos hcm (by positivity) (by positivity) hΛ hP hjj0 hjjmono hjjP hs0 hA hS1 hMpos hWpos hmono
    hφ1 hφ2 hρ hr1 hr2 hT hsol hseed hsmall

/-- **Ladder-pair stability with the transfer condition derived at forbidden overlaps** (`thm:eng-volterra`(b) with (a),
case (ii) of the remark after (S3)).  As `ladder_pair_stability`, but the transfer hypothesis `hT` is replaced by the
overlap conditions at each `j_p` (`p < P`): `𝒜_h(s_{j_p}) > 0`, `W_{j_p+1} ≤ C_w W_{j_p}`, and
`𝒜_h(s_{j_p}) M_{j_p} M_{j_p+1} ≤ C_ω |ω_mod(h)|` (the paper's `𝒜_h(s_{j_p}) 𝖬 𝖬 ≍ ω_*`); (S3) then holds with
`Λ = max 1 (2K² max(C_w,C_E) C_ω/c₋)`, `K = (K_A+K_B)K_w`, by `transfer_of_forbidden_overlap`.  The case of a bounded
(oscillatory) overlap, where (S3) is assumed, is `ladder_pair_stability`. -/
theorem ladder_pair_stability_forbidden (γ h CE Cw Cω cm KD Kw KA KB : ℝ) (m : ℕ) (dd pp qq : ℝ → ℝ → ℝ) {d2 : ℝ → ℝ → ℝ}
    (PiP PiM : ℝ → ℝ → M2) (ω : ℝ → ℝ) (AA BB : ℝ → ℝ → ℝ) (wf : ℕ → Fin 2 → ℝ → ℝ → V2)
    (ρ ρt W M ψ : ℤ → ℝ) (s0 NR : ℤ) (P : ℕ) (jj : ℕ → ℤ)
    (hh : 0 < h) (hcm : 0 < cm) (hKD : 0 ≤ KD) (hKw : 0 ≤ Kw) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hL : ∀ p, SymplecticLadder γ dd d2 pp qq PiP PiM (wf p) ω)
    (hP : 1 ≤ P) (hjj0 : jj 0 = 0) (hjjmono : ∀ p < P, jj p < jj (p + 1)) (hjjP : jj P = NR - 1)
    (hs0 : s0 = 0 ∨ s0 = 1)
    (hρ : ∀ k, 0 ≤ ρ k) (hρt : ∀ k : ℤ, 0 ≤ k → 0 < ρt k)
    (hMpos : ∀ j ∈ Icc 0 NR, 0 < M j) (hWpos : ∀ j ∈ Icc 0 NR, 0 < W j)
    (hmono : ∀ k ∈ Icc 0 NR, ∀ j ∈ Icc 0 NR, k ≤ j → W k ≤ CE * W j)
    (hUCa : ∀ k : ℤ, 0 ≤ k → cm ≤ |Fcas pp AA BB PiM (((k : ℝ) + γ) * h + h / 2) h|)
    (hUCb : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 0| ≤ KD * h ^ (m + 1) * ρ k)
    (hUCc : ∀ k : ℤ, 0 ≤ k → |defectRow pp qq AA BB PiP PiM (((k : ℝ) + γ) * h) h 1| ≤ KD * h ^ (m + 1) * ρt k)
    (hKa : ∀ k : ℤ, 0 ≤ k → |AA (((k : ℝ) + γ) * h) h| ≤ KA)
    (hKb : ∀ k : ℤ, 0 ≤ k → |h * BB (((k : ℝ) + γ) * h) h| * (ρ k / ρt k) ≤ KB)
    (henv : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (jj (p - 1)) (jj p + 1),
      |wf p 0 (((k : ℝ) + γ) * h) h 0| ≤ Kw * W k * M k ∧
      |wf p 1 (((k : ℝ) + γ) * h) h 0| ≤ Kw * (W k)⁻¹ * M k ∧
      ρt k * |wf p 0 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * W k * M k ∧
      ρt k * |wf p 1 (((k : ℝ) + γ) * h) h 1| ≤ Kw * ρ k * (W k)⁻¹ * M k)
    (hDhard : s0 = 0 → Dm dd (γ * h) h = 0)
    (hannih : s0 = 0 → colMul (PiM (γ * h) h) (wf 1 0 (γ * h) h) = 0)
    (hover : ∀ p, 1 ≤ p → p < P → 0 < ladderA dd pp γ h (jj p) ∧ W (jj p + 1) ≤ Cw * W (jj p) ∧
      ladderA dd pp γ h (jj p) * (M (jj p) * M (jj p + 1)) ≤ Cω * |ω h|)
    (hsol : ∀ k ∈ Icc s0 (NR - 1), Lh h (ladderA dd pp γ h) (ladderQ qq γ h) ψ k = 0)
    (hseed : ∀ j ∈ Icc 0 s0, ψ j = ladderPairFun AA BB wf γ h 0 1 j)
    (hsmall : 2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M
      ≤ mvCstar cm CE ((KA + KB) * Kw)) :
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |ψ j - psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j|
        ≤ mvC cm CE ((KA + KB) * Kw) (max 1 (2 * ((KA + KB) * Kw) ^ 2 * max Cw CE * Cω / cm)) P
          * (2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M) * W j * M j) ∧
    (∀ p, 1 ≤ p → p < P → ∀ j ∈ Icc (jj p) (jj p + 1),
      psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j
        = psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj (p + 1) j) ∧
    (∀ j ∈ Icc 0 NR, ∃ p ∈ Icc 1 P,
      |ψ j - psiHat (ladderPairFun AA BB wf γ h 0) (ladderPairFun AA BB wf γ h 1) jj p j|
        ≤ mvC cm CE ((KA + KB) * Kw) (max 1 (2 * ((KA + KB) * Kw) ^ 2 * max Cw CE * Cω / cm)) P
          * (2 * KD * Kw * h ^ m * volTheta h |ω h| s0 jj P ρ M) * W j * M j) := by
  obtain ⟨hωpos, hA, hS1, hφ1, hφ2, hr1, hr2⟩ := ladder_pair_data γ h cm KD Kw KA KB m dd pp qq PiP PiM ω AA BB
    wf ρ ρt W M s0 NR P jj hh hKD hKw hL hjj0 hjjmono hjjP hs0 hρ hρt hMpos hWpos hUCa hUCb hUCc hKa hKb henv
    hDhard hannih
  exact volterra_multi_forbidden h (|ω h|) cm CE ((KA + KB) * Kw) (2 * KD * Kw * h ^ m) Cw Cω
    (ladderA dd pp γ h) (ladderQ qq γ h) ψ ρ M W s0 NR P jj (ladderPairFun AA BB wf γ h 0)
    (ladderPairFun AA BB wf γ h 1)
    hh hωpos hcm (by positivity) (by positivity) hP hjj0 hjjmono hjjP hs0 hA hS1 hMpos hWpos hmono
    hφ1 hφ2 hρ hr1 hr2 hover hsol hseed hsmall

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_S1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_S1

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_S2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_S2

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.residual_of_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.residual_of_defect

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_residual_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_residual_interior

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_residual_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_residual_hard

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_pair_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_pair_data

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_pair_stability_forbidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_pair_stability_forbidden

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.ladder_pair_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.ladder_pair_stability

end FormalResearch.JacobiEigenvectors.Engine

end

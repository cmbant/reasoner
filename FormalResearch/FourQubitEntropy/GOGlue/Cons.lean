import FormalResearch.FourQubitEntropy.GOGlue.Hess
import FormalResearch.FourQubitEntropy.GOGlue.Ray
import FormalResearch.FourQubitEntropy.GOProbe.Final

/-!
# GO glue: the 64 constraint matrices of the certificate and their positivity

`CSpec` names a constraint (the tags of `gen_go_cert.py`: `sos`, `fidelity` (a ray `(a,b)`), `lead`,
`height`, `imaginary`, `height_quadratic`, `imaginary_quadratic`, `procrustes`, `fidelity_floor`, `excess`,
`lower_quadratic`).  `CSpec.mat cs = (k, L, S)` is the corresponding `k × k` matrix of polynomials
(the slice-side expression of `PaperEGoSlice.lean`, transcribed in `PQ`, times `L`), and `spec_psd` shows
that at a slice point with `SliceConstraints` the matrix `S(y)` is positive semidefinite
(`CSpec.okB`: the rational ray conditions of `RayOK`, and `c² + 3 s² = 1`, `σ₀, σ = ±1` for the lower
frames).  The generated `cons` equals `CSpec.mat` up to a positive factor: `GOGlue/DataCheck`.
Claim class: proved.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe GOProbe.PQ

/-! ### Rays -/

def rM (a b : Fin 4 → Fin 4 → ℚ) (i j : Fin 4) : ℚ := a i j + b i j
def rPi (a b : Fin 4 → Fin 4 → ℚ) (i j : Fin 4) : ℚ := ∑ k, rM a b k i * a k j

/-- `M = a + b` orthogonal, `Π = Mᵀ a` a symmetric idempotent of trace one and rank one, `a = M Π`. -/
def RayOK (a b : Fin 4 → Fin 4 → ℚ) : Prop :=
  (∀ i j, ∑ k, rM a b k i * rM a b k j = if i = j then 1 else 0) ∧
  (∀ i j, rPi a b j i = rPi a b i j) ∧
  (∀ i j, ∑ k, rPi a b i k * rPi a b k j = rPi a b i j) ∧
  (∑ i, rPi a b i i = 1) ∧
  (∀ i j k l, rPi a b i j * rPi a b k l = rPi a b i l * rPi a b k j) ∧
  (∀ i j, ∑ l, rM a b i l * rPi a b l j = a i j)

instance (a b : Fin 4 → Fin 4 → ℚ) : Decidable (RayOK a b) := by unfold RayOK; infer_instance

noncomputable section

theorem RayOK.real {a b : Fin 4 → Fin 4 → ℚ} (h : RayOK a b) :
    ∃ P Q : M4R, Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ (∀ i j, P i 0 * Q j 0 = (a i j : ℝ)) ∧
      ∀ i j, ∑ k, P i k * Q j k = (a i j : ℝ) + (b i j : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  set M : M4R := Matrix.of fun i j => ((rM a b i j : ℚ) : ℝ) with hMdef
  set Pi : M4R := Matrix.of fun i j => ((rPi a b i j : ℚ) : ℝ) with hPidef
  have hM : Mᵀ * M = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hMdef, Matrix.of_apply, Matrix.one_apply]
    have := h1 i j
    split_ifs at this ⊢ <;> exact_mod_cast this
  have hs : Piᵀ = Pi := by
    ext i j
    simp only [Matrix.transpose_apply, hPidef, Matrix.of_apply]
    exact_mod_cast h2 i j
  have hi : Pi * Pi = Pi := by
    ext i j
    simp only [Matrix.mul_apply, hPidef, Matrix.of_apply]
    exact_mod_cast h3 i j
  have ht : Matrix.trace Pi = 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, hPidef, Matrix.of_apply]
    exact_mod_cast h4
  have hr : ∀ i j k l, Pi i j * Pi k l = Pi i l * Pi k j := by
    intro i j k l
    simp only [hPidef, Matrix.of_apply]
    exact_mod_cast h5 i j k l
  obtain ⟨P, Q, hP, hQ, hPQ, hPe⟩ := ray_exists M Pi hM hs hi ht hr
  have hMPi : ∀ i j, (M * Pi) i j = (a i j : ℝ) := by
    intro i j
    simp only [Matrix.mul_apply, hMdef, hPidef, Matrix.of_apply]
    exact_mod_cast h6 i j
  refine ⟨P, Q, hP, hQ, fun i j => ?_, fun i j => ?_⟩
  · rw [hPe, hMPi]
  · rw [hPQ]
    simp only [hMdef, Matrix.of_apply, rM]
    push_cast; rfl

end

/-! ### The specifications -/

inductive CSpec
  | sos
  | fid (a b : Fin 4 → Fin 4 → ℚ)
  | lead
  | height
  | imag
  | hq
  | iq
  | proc (k : Fin 2)
  | ff
  | excess
  | lq (σ₀ σ c s : ℚ)

def CSpec.ok : CSpec → Prop
  | .fid a b => RayOK a b
  | .lq σ₀ σ c s => (σ₀ = 1 ∨ σ₀ = -1) ∧ (σ = 1 ∨ σ = -1) ∧ c ^ 2 + 3 * s ^ 2 = 1
  | _ => True

instance (cs : CSpec) : Decidable cs.ok := by
  cases cs <;> simp only [CSpec.ok] <;> infer_instance

def pRe (a b : Fin 4 → Fin 4 → ℚ) : PQ 1 :=
  add (smul 3 (sumF fun i => sumF fun j => smul (a i j) (pX i j)))
    (sumF fun i => sumF fun j => smul (b i j) (pY i j))

def pIm (a b : Fin 4 → Fin 4 → ℚ) : PQ 1 :=
  sub (sumF fun i => sumF fun j => smul (a i j) (pY i j))
    (sumF fun i => sumF fun j => smul (b i j) (pX i j))

def sosMat : PM 0 1 1 := fun _ _ => ofRat 1
def fidMat (a b : Fin 4 → Fin 4 → ℚ) : PM 2 1 1 := fun _ _ =>
  smul (1 / 36) (sub (mul pH0 pH0) (add (mul (pRe a b) (pRe a b)) (smul 3 (mul (pIm a b) (pIm a b)))))
def leadMat : PM 2 1 1 := fun _ _ => smul (1 / 6) (mul pH0 (pX 0 0))
def heightMat : PM 4 10 10 := fun i j => smul (1 / 216) (mul (mul pN pH0) (pHess i j))
def imagMat : PM 4 3 3 := fun i j => smul (1 / 36) (mul (mul pN pH0) (pY3 i j))
def hqMat : PM 2 10 10 := fun i j => smul (1 / 216) (mul pH0 (pHess i j))
def iqMat : PM 2 3 3 := fun i j => smul (1 / 36) (mul pH0 (pY3 i j))
def procMat (k : Fin 2) : PM 2 4 4 := fun i j =>
  smul (1 / 216) (mul pH0 (if (k = 0 ∧ j = 0) ∨ (k = 1 ∧ i = 0) then smul 3 (pX i j) else pY i j))
def ffMat : PM 2 2 2 := ![![smul (1 / 36) (add (sub (mul pH0 pH0) pN) pR), smul (1 / 36) pI],
  ![smul (1 / 36) pI, smul (1 / 108) (sub (sub (mul pH0 pH0) pN) pR)]]
def excessMat : PM 2 1 1 := fun _ _ => smul (1 / 6) pE
def lqMat (σ₀ σ c s : ℚ) : PM 2 3 3 := fun i j => smul (1 / 216) (mul pH0 (pL σ₀ σ c s i j))

/-- Common denominator of the entries. -/
def pmDen {d k : ℕ} (A : PM d k k) : ℕ :=
  (List.ofFn fun i => (List.ofFn fun j => (A i j).den).foldr Nat.lcm 1).foldr Nat.lcm 1

/-- The integer polynomial matrix `L · A`. -/
def pmToSP {d k : ℕ} (A : PM d k k) (L : ℕ) : List (List SP) :=
  List.ofFn fun i => List.ofFn fun j => scaleSP ((L / (A i j).den : ℕ) : ℤ) (A i j).p

def specOf {d k : ℕ} (A : PM d k k) : ℕ × ℕ × List (List SP) := (k, pmDen A, pmToSP A (pmDen A))

def CSpec.mat : CSpec → ℕ × ℕ × List (List SP)
  | .sos => specOf sosMat
  | .fid a b => specOf (fidMat a b)
  | .lead => specOf leadMat
  | .height => specOf heightMat
  | .imag => specOf imagMat
  | .hq => specOf hqMat
  | .iq => specOf iqMat
  | .proc k => specOf (procMat k)
  | .ff => specOf ffMat
  | .excess => specOf excessMat
  | .lq σ₀ σ c s => specOf (lqMat σ₀ σ c s)

/-! ### Soundness of `toSP` -/

theorem dvd_foldr_lcm : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ∣ l.foldr Nat.lcm 1
  | [], a, h => by simp at h
  | b :: l, a, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (dvd_foldr_lcm l a h).trans (Nat.dvd_lcm_right _ _)

theorem foldr_lcm_pos : ∀ l : List ℕ, (∀ a ∈ l, 0 < a) → 0 < l.foldr Nat.lcm 1
  | [], _ => by simp
  | b :: l, h => by
    rw [List.foldr_cons]
    exact Nat.lcm_pos (h b (by simp)) (foldr_lcm_pos l fun a ha => h a (by simp [ha]))

theorem pmDen_dvd {d k : ℕ} (A : PM d k k) (i j : Fin k) : (A i j).den ∣ pmDen A := by
  unfold pmDen
  have h1 : (A i j).den ∣ (List.ofFn fun j => (A i j).den).foldr Nat.lcm 1 :=
    dvd_foldr_lcm _ _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  have h2 : (List.ofFn fun j => (A i j).den).foldr Nat.lcm 1 ∣
      (List.ofFn fun i => (List.ofFn fun j => (A i j).den).foldr Nat.lcm 1).foldr Nat.lcm 1 :=
    dvd_foldr_lcm _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  exact h1.trans h2

theorem pmDen_pos {d k : ℕ} (A : PM d k k) : 0 < pmDen A := by
  unfold pmDen
  refine foldr_lcm_pos _ fun a ha => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact foldr_lcm_pos _ fun b hb => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
    exact (A i j).hden

theorem CSpec.den_pos (cs : CSpec) : 0 < cs.mat.2.1 := by
  cases cs <;> exact pmDen_pos _

theorem entry_toSP {d k : ℕ} (A : PM d k k) (L : ℕ) (i j : Fin k) :
    entry (pmToSP A L) i j = scaleSP ((L / (A i j).den : ℕ) : ℤ) (A i j).p := by
  simp [entry, pmToSP, List.getD_eq_getElem?_getD]

theorem ev_entry_toSP {d k : ℕ} (A : PM d k k) (y : ℕ → ℝ) (i j : Fin k) :
    ev y (entry (pmToSP A (pmDen A)) i j) = (pmDen A : ℝ) * (A i j).val y := by
  rw [entry_toSP, ev_scaleSP]
  have hd : ((A i j).den : ℝ) ≠ 0 := by exact_mod_cast (A i j).hden.ne'
  have h1 : ((pmDen A / (A i j).den : ℕ) : ℝ) * (A i j).den = pmDen A := by
    exact_mod_cast Nat.div_mul_cancel (pmDen_dvd A i j)
  unfold PQ.val
  simp only [Int.cast_natCast]
  field_simp
  rw [← h1]; ring

theorem psd_mk {d k : ℕ} (A : PM d k k) (y : ℕ → ℝ) (s : ℝ) (K : Fin k → Fin k → ℝ) (hs : 0 ≤ s)
    (hK : QF K) (hA : ∀ i j, (A i j).val y = s * K i j) (w : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range k, ∑ c ∈ range k, w a * ev y (entry (pmToSP A (pmDen A)) a c) * w c := by
  rw [Finset.sum_range]
  have : ∀ i : Fin k, ∑ c ∈ range k, w i * ev y (entry (pmToSP A (pmDen A)) i c) * w c =
      ∑ j : Fin k, w i * ((pmDen A : ℝ) * (s * K i j)) * w j := by
    intro i
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ev_entry_toSP, hA]
  simp only [this]
  have h2 : ∑ i : Fin k, ∑ j : Fin k, w i * ((pmDen A : ℝ) * (s * K i j)) * w j =
      (pmDen A : ℝ) * s * ∑ i : Fin k, ∑ j : Fin k, w i * K i j * w j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hs) (hK fun i => w i)

/-! ### Positivity of the specifications -/

theorem qf_one (c : ℝ) (hc : 0 ≤ c) : QF (fun _ _ : Fin 1 => c) := by
  intro w
  simp [Fin.sum_univ_one]
  nlinarith [sq_nonneg (w 0)]

section Pos
variable (y : ℕ → ℝ)

theorem pRe_val (a b : Fin 4 → Fin 4 → ℚ) : (pRe a b).val y =
    3 * (∑ i, ∑ j, (a i j : ℝ) * sX (restr y) i j) + ∑ i, ∑ j, (b i j : ℝ) * sY (restr y) i j := by
  simp only [pRe, val_add, val_smul, val_sumF, rel_pX y _ _, rel_pY y _ _]
  push_cast; ring

theorem pIm_val (a b : Fin 4 → Fin 4 → ℚ) : (pIm a b).val y =
    (∑ i, ∑ j, (a i j : ℝ) * sY (restr y) i j) - ∑ i, ∑ j, (b i j : ℝ) * sX (restr y) i j := by
  simp only [pIm, val_sub, val_smul, val_sumF, rel_pX y _ _, rel_pY y _ _]

theorem pY3_val (i j : Fin 3) : (pY3 i j).val y = sY3 (restr y) i j := by
  simp [pY3, sY3, rel_pY y _ _]

theorem sN_nonneg (v : SV) : 0 ≤ sN v := by
  unfold sN fn4
  have h1 : 0 ≤ ∑ i, ∑ j, sX v i j ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, sY v i j ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

theorem CSpec.psd (cs : CSpec) (hok : cs.ok) (hc : SliceConstraints (restr y)) (w : ℕ → ℝ) :
    0 ≤ ∑ a ∈ range cs.mat.1, ∑ c ∈ range cs.mat.1, w a * ev y (entry cs.mat.2.2 a c) * w c := by
  have h0n : 0 ≤ sH0 (restr y) := hc.h0_nonneg
  have hNn : 0 ≤ sN (restr y) := sN_nonneg _
  have hX := rel_pX y
  have hY := rel_pY y
  cases cs with
  | sos =>
    exact psd_mk sosMat y 1 (fun _ _ => 1) zero_le_one (qf_one 1 zero_le_one)
      (fun i j => by simp [sosMat, val_ofRat]) w
  | fid a b =>
    obtain ⟨P, Q, hP, hQ, ha, hab⟩ := RayOK.real hok
    obtain ⟨χ, hχ, hn⟩ := ray_mem (restr y) P Q (Matrix.of fun i j => (a i j : ℝ))
      (Matrix.of fun i j => (b i j : ℝ)) hP hQ ha hab
    have hle := hc.rays χ hχ
    rw [hn] at hle
    simp only [Matrix.of_apply] at hle
    refine psd_mk (fidMat a b) y 1 (fun _ _ => (sH0 (restr y) ^ 2 - ((3 * (∑ i, ∑ j, (a i j : ℝ) * sX (restr y) i j) +
        ∑ i, ∑ j, (b i j : ℝ) * sY (restr y) i j) ^ 2 + 3 * ((∑ i, ∑ j, (a i j : ℝ) * sY (restr y) i j) -
        ∑ i, ∑ j, (b i j : ℝ) * sX (restr y) i j) ^ 2)) / 36) zero_le_one
      (qf_one _ (by linarith)) (fun i j => ?_) w
    simp only [fidMat, val_smul, val_sub, val_add, val_mul, pRe_val, pIm_val, pH0_val]
    push_cast; ring
  | lead =>
    exact psd_mk leadMat y (sH0 (restr y) / 6) (fun _ _ => restr y 0) (by positivity)
      (qf_one _ hc.t_nonneg) (fun i j => by
        simp [leadMat, val_smul, val_mul, pH0_val, rel_pX y 0 0, sX]; ring) w
  | height =>
    exact psd_mk heightMat y (sN (restr y) * sH0 (restr y) / 216) (sHess (restr y)) (by positivity)
      hc.Hess (fun i j => by
        have := pHess_rel y i j
        simp only [heightMat, val_smul, val_mul, pN_val, pH0_val, this, Matrix.of_apply]
        push_cast; ring) w
  | imag =>
    exact psd_mk imagMat y (sN (restr y) * sH0 (restr y) / 36) (sY3 (restr y)) (by positivity)
      hc.Y3 (fun i j => by
        simp only [imagMat, val_smul, val_mul, pN_val, pH0_val, pY3_val]
        push_cast; ring) w
  | hq =>
    exact psd_mk hqMat y (sH0 (restr y) / 216) (sHess (restr y)) (by positivity)
      hc.Hess (fun i j => by
        have := pHess_rel y i j
        simp only [hqMat, val_smul, val_mul, pH0_val, this, Matrix.of_apply]
        push_cast; ring) w
  | iq =>
    exact psd_mk iqMat y (sH0 (restr y) / 36) (sY3 (restr y)) (by positivity)
      hc.Y3 (fun i j => by
        simp only [iqMat, val_smul, val_mul, pH0_val, pY3_val]
        push_cast; ring) w
  | proc k =>
    fin_cases k
    · exact psd_mk (procMat 0) y (sH0 (restr y) / 216) (sK0 (restr y)) (by positivity) hc.K0
        (fun i j => by
          by_cases h : j = 0
          · subst h; simp [procMat, sK0, val_smul, val_mul, pH0_val, hX i 0]; ring
          · simp [procMat, sK0, h, val_smul, val_mul, pH0_val, hY i j]; ring) w
    · exact psd_mk (procMat 1) y (sH0 (restr y) / 216) (sK1 (restr y)) (by positivity) hc.K1
        (fun i j => by
          by_cases h : i = 0
          · subst h; simp [procMat, sK1, val_smul, val_mul, pH0_val, hX 0 j]; ring
          · simp [procMat, sK1, h, val_smul, val_mul, pH0_val, hY i j]; ring) w
  | ff =>
    exact psd_mk ffMat y (1 / 36) (sB0 (restr y)) (by norm_num) hc.B0 (fun i j => by
      have hR := pR_val y
      have hI := pI_val y
      fin_cases i <;> fin_cases j <;>
        simp [ffMat, sB0, val_smul, val_sub, val_add, val_mul, pH0_val, pN_val, hR, hI] <;> ring) w
  | excess =>
    exact psd_mk excessMat y (1 / 6) (fun _ _ => sE (restr y)) (by norm_num)
      (qf_one _ hc.e_nonneg) (fun i j => by simp [excessMat, val_smul, pE_val]) w
  | lq σ₀ σ c s =>
    obtain ⟨h1, h2, h3⟩ := hok
    have g1 : ((σ₀ : ℚ) : ℝ) = 1 ∨ ((σ₀ : ℚ) : ℝ) = -1 := by
      rcases h1 with h | h <;> simp [h]
    have g2 : ((σ : ℚ) : ℝ) = 1 ∨ ((σ : ℚ) : ℝ) = -1 := by
      rcases h2 with h | h <;> simp [h]
    have g3 : ((c : ℚ) : ℝ) ^ 2 + 3 * ((s : ℚ) : ℝ) ^ 2 = 1 := by exact_mod_cast h3
    exact psd_mk (lqMat σ₀ σ c s) y (sH0 (restr y) / 216) (sL (restr y) σ₀ σ c s) (by positivity)
      (hc.lower _ _ _ _ g1 g2 g3) (fun i j => by
        have := pL_rel y σ₀ σ c s i j
        simp only [lqMat, val_smul, val_mul, pH0_val, this, Matrix.of_apply]
        push_cast; ring) w

end Pos

end FormalResearch.FourQubitEntropy.GO

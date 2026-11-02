import FormalResearch.FourQubitEntropy.QVCheck.Coupled2

/-!
# The generic coupled identity for one pair of letters (K4)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem coupled_generic (DA DB n : ℕ) (tA tiA tB tiB w v P R : ℕ → ℕ → ℤ) (dA dB Lc : ℤ)
    (Om Xi : ℕ → ℤ) (dU : ℕ → ℕ) (iA jB : ℕ → ℕ → ℕ) (wcf vcf : ℕ → ℕ → ℤ)
    (hA2 : ∀ i < DA, ∀ j < DA, ∑ k ∈ range DA, tiA i k * tA k j = if i = j then dA else 0)
    (hB2 : ∀ i < DB, ∀ j < DB, ∑ k ∈ range DB, tiB i k * tB k j = if i = j then dB else 0)
    (hbd : ∀ u < n, ∀ x < dU u, iA u x < DA ∧ jB u x < DB)
    (hW : ∀ i < DA, ∀ j < DB, Lc * (∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j) =
      ∑ u ∈ range n, Om u * ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then wcf u x else 0)
    (hV : ∀ i < DA, ∀ j < DB, Lc * (∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l) =
      ∑ u ∈ range n, Xi u * ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then vcf u x else 0) :
    dA ^ 2 * dB ^ 2 * Lc ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R) =
      ∑ u ∈ range n, ∑ u' ∈ range n, Om u * Xi u' * ∑ x ∈ range (dU u), ∑ y ∈ range (dU u'),
        wcf u x * vcf u' y *
          (∑ e ∈ range DA, ∑ e' ∈ range DA, tA (iA u x) e * P e e' * tiA e' (iA u' y)) *
          (∑ e ∈ range DB, ∑ e' ∈ range DB, tB (jB u x) e * R e e' * tiB e' (jB u' y)) := by
  have hA2m : nm DA DA tiA * nm DA DA tA = dA • (1 : Matrix (Fin DA) (Fin DA) ℤ) := by
    rw [mul_nm]
    refine Matrix.ext fun i j => ?_
    rw [nm_apply, hA2 i.val i.2 j.val j.2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  have hB2m : nm DB DB tiB * nm DB DB tB = dB • (1 : Matrix (Fin DB) (Fin DB) ℤ) := by
    rw [mul_nm]
    refine Matrix.ext fun i j => ?_
    rw [nm_apply, hB2 i.val i.2 j.val j.2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · have : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [hij, this]
  have h1 := S4_coupled (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R) (nm DA DA tA) (nm DA DA tiA)
    (nm DB DB tB) (nm DB DB tiB) dA dB hA2m hB2m
  have eP : nm DA DA tA * nm DA DA P * nm DA DA tiA =
      nm DA DA (fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, tA i e * P e e' * tiA e' k) := tri_nm DA tA P tiA
  have eR : nm DB DB tB * nm DB DB R * nm DB DB tiB =
      nm DB DB (fun i k => ∑ e ∈ range DB, ∑ e' ∈ range DB, tB i e * R e e' * tiB e' k) := tri_nm DB tB R tiB
  have eW : (nm DA DA tiA)ᵀ * nm DA DB w * nm DB DB tiB =
      nm DA DB (fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j) := by
    rw [transpose_nm, mul_nm, mul_nm]
  have eV : nm DA DA tA * nm DA DB v * (nm DB DB tB)ᵀ =
      nm DA DB (fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l) := by
    rw [transpose_nm, mul_nm, mul_nm]
  rw [eP, eR, eW, eV] at h1
  set Wc : ℕ → ℕ → ℤ := fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tiA k i * w k l) * tiB l j with hWc
  set Vc : ℕ → ℕ → ℤ := fun i j => ∑ l ∈ range DB, (∑ k ∈ range DA, tA i k * v k l) * tB j l with hVc
  set Pt : ℕ → ℕ → ℤ := fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, tA i e * P e e' * tiA e' k with hPt
  set Rt : ℕ → ℕ → ℤ := fun i k => ∑ e ∈ range DB, ∑ e' ∈ range DB, tB i e * R e e' * tiB e' k with hRt
  have hWm : Lc • nm DA DB Wc = ∑ u ∈ range n, Om u • nm DA DB (fun i j =>
      ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then wcf u x else 0) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, nm_apply, Matrix.sum_apply, smul_eq_mul]
    exact hW i.val i.2 j.val j.2
  have hVm : Lc • nm DA DB Vc = ∑ u ∈ range n, Xi u • nm DA DB (fun i j =>
      ∑ x ∈ range (dU u), if i = iA u x ∧ j = jB u x then vcf u x else 0) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, nm_apply, Matrix.sum_apply, smul_eq_mul]
    exact hV i.val i.2 j.val j.2
  have key : Lc ^ 2 * S4 (nm DA DB Wc) (nm DA DA Pt) (nm DA DB Vc) (nm DB DB Rt) =
      S4 (Lc • nm DA DB Wc) (nm DA DA Pt) (Lc • nm DA DB Vc) (nm DB DB Rt) := by
    rw [S4_smul_left, S4_smul_right]; ring
  have qe_nm : ∀ (D : ℕ) (f : ℕ → ℕ → ℤ) (i k : ℕ), i < D → k < D → qe (nm D D f) i k = f i k := by
    intro D f i k hi hk; unfold qe; rw [dif_pos ⟨hi, hk⟩]; rfl
  calc dA ^ 2 * dB ^ 2 * Lc ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R)
      = Lc ^ 2 * (dA ^ 2 * dB ^ 2 * S4 (nm DA DB w) (nm DA DA P) (nm DA DB v) (nm DB DB R)) := by ring
    _ = Lc ^ 2 * S4 (nm DA DB Wc) (nm DA DA Pt) (nm DA DB Vc) (nm DB DB Rt) := by rw [h1]
    _ = S4 (Lc • nm DA DB Wc) (nm DA DA Pt) (Lc • nm DA DB Vc) (nm DB DB Rt) := key
    _ = _ := by
      rw [hWm, hVm, S4_sum_left]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [S4_smul_left, S4_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u' hu' => ?_
      rw [S4_smul_right]
      have hu1 := Finset.mem_range.1 hu
      have hu2 := Finset.mem_range.1 hu'
      rw [S4_hat DA DB (dU u) (dU u') (iA u) (jB u) (iA u') (jB u')
        (fun x hx => (hbd u hu1 x hx).1) (fun x hx => (hbd u hu1 x hx).2)
        (fun x hx => (hbd u' hu2 x hx).1) (fun x hx => (hbd u' hu2 x hx).2) (wcf u) (vcf u')]
      rw [mul_assoc]
      refine congrArg (fun z => Om u * (Xi u' * z)) ?_
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      have hx' := Finset.mem_range.1 hx
      have hy' := Finset.mem_range.1 hy
      rw [qe_nm DA Pt _ _ (hbd u hu1 x hx').1 (hbd u' hu2 y hy').1,
        qe_nm DB Rt _ _ (hbd u hu1 x hx').2 (hbd u' hu2 y hy').2]

end QVCheck

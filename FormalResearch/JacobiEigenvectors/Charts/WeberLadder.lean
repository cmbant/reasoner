module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ODEFlow
public import FormalResearch.JacobiEigenvectors.Charts.PCActual
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvelopeAssembled
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Engine.Defect

/-!
# Paper J, charts (WP1a): the Weber symplectic model ladder and envelopes

Formalises:
* `charts.tex` `lem:cha-weber-ladder` (`eq:cha-shifts`, `eq:cha-annih`): `weber_symplecticLadder`
  and `weber_annih` for arbitrary `Y : ℝ → ℝ` with `γ = 1/2`, `dd s _ = √s`, `d2 s _ = s`, `ω h = √h`.
* `charts.tex` `lem:cha-weber-env` (1): pointwise two-sided envelope bounds `weber_env_well` on all
  `z : ℝ` via reflection parity at half-integers `a = -(j + 1/2)`, plus `weber_k2_le`.
* `charts.tex` `lem:cha-W0`: lower bound `weber_W0` on `|z| ≥ 2 √(j + 1/2)`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Engine

/-! ### Weber ladder definitions (`lem:cha-weber-ladder`) -/

def ddWeb (s _ : ℝ) : ℝ := Real.sqrt s
def d2Web (s _ : ℝ) : ℝ := s
def omegaWeb (h : ℝ) : ℝ := Real.sqrt h

def weberM_up (u h Z : ℝ) : M2 :=
  !![Z / 2, -1; -(Z ^ 2 / 4 - u) + h / 2, Z / 2]

def weberM_dn (u h Z : ℝ) : M2 :=
  !![Z / 2, 1; (Z ^ 2 / 4 - u) + h / 2, Z / 2]

def qWeb (Z₀ v h s : ℝ) : ℝ := (Z₀ + h * s) ^ 2 / 4 - v

lemma continuous_qWeb (Z₀ v h : ℝ) : Continuous (qWeb Z₀ v h) := by
  unfold qWeb; fun_prop

def weberStepUp (Y : ℝ → ℝ) (u h : ℝ) : ℝ := if h = 0 then deriv Y u else (Y (u + h) - Y u) / h
def weberStepDn (Y : ℝ → ℝ) (u h : ℝ) : ℝ := if h = 0 then -deriv Y u else (Y (u - h) - Y u) / h

def weberPhiP (Y : ℝ → ℝ) (u h : ℝ) : M2 :=
  odeFund (qWeb (Y u) (u + h) h) (continuous_qWeb _ _ _) 0 (weberStepUp Y u h)

def weberPhiM (Y : ℝ → ℝ) (u h : ℝ) : M2 :=
  odeFund (qWeb (Y u) (u - h) h) (continuous_qWeb _ _ _) 0 (weberStepDn Y u h)

def weberPiP (Y : ℝ → ℝ) (u h : ℝ) : M2 :=
  weberPhiP Y u h * weberM_up u h (Y u)

def weberPiM (Y : ℝ → ℝ) (u h : ℝ) : M2 :=
  weberPhiM Y u h * weberM_dn u h (Y u)

/-- Balanced Weber vector at coordinate `u` (`a = -(u / h)` hits `-j - 1/2` at `u = (j + 1/2) h`). -/
def wWeb (Y : ℝ → ℝ) : Fin 2 → ℝ → ℝ → V2
  | 0 => fun u h => if h ≤ 0 then ![0, 0] else
      ![ut pcU (-(u / h)) (Y u / Real.sqrt h),
        Real.sqrt h * deriv (ut pcU (-(u / h))) (Y u / Real.sqrt h)]
  | 1 => fun u h => if h ≤ 0 then ![0, 0] else
      ![vt pcV (-(u / h)) (Y u / Real.sqrt h),
        Real.sqrt h * deriv (vt pcV (-(u / h))) (Y u / Real.sqrt h)]

/-! ### Algebraic & ODE identities for `weberPiP`, `weberPiM` -/

lemma weberM_up_det (u h Z : ℝ) : (weberM_up u h Z).det = u + h / 2 := by
  simp [weberM_up, Matrix.det_fin_two]; ring

lemma weberM_dn_det (u h Z : ℝ) : (weberM_dn u h Z).det = u - h / 2 := by
  simp [weberM_dn, Matrix.det_fin_two]; ring

lemma weberM_dn_mul_up (u h Z : ℝ) :
    weberM_dn (u + h) h Z * weberM_up u h Z = (u + h / 2) • (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [weberM_dn, weberM_up, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

lemma weberM_conj_sg (u h Z : ℝ) :
    Sg * weberM_dn u h Z * Sg = weberM_up u (-h) Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Sg, weberM_dn, weberM_up, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

private lemma colMul_assoc_mat (A B : M2) (x : V2) :
    colMul (A * B) x = colMul A (colMul B x) := by
  ext i; fin_cases i <;>
    (simp [colMul, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

private lemma weberPhiP_conj_sg (Y : ℝ → ℝ) (u h : ℝ) :
    Sg * weberPhiM Y u h * Sg = weberPhiP Y u (-h) := by
  have heq : ∀ s, qWeb (Y u) (u + (-h)) (-h) (-s) = qWeb (Y u) (u - h) h s := fun s => by
    dsimp [qWeb]; ring
  have hode := odeFund_conj_sg (q₁ := qWeb (Y u) (u + (-h)) (-h))
    (q₂ := qWeb (Y u) (u - h) h) (continuous_qWeb _ _ _) (continuous_qWeb _ _ _)
    heq (weberStepDn Y u h)
  have hstep : -weberStepDn Y u h = weberStepUp Y u (-h) := by
    dsimp [weberStepDn, weberStepUp]
    by_cases hh : h = 0
    · simp [hh]
    · have hh' : -h ≠ 0 := neg_ne_zero.mpr hh
      simp only [hh, hh', ↓reduceIte]
      rw [← sub_eq_add_neg]; ring
  dsimp [weberPhiP, weberPhiM]
  rw [← hstep]
  exact hode

/-- Intertwining identity `M_-(u + h, h; Z₀ + h s) Φ_+(u, h; s) = Φ_0(u, h; s) M_-(u + h, h; Z₀)`. -/
private lemma weberM_dn_mul_odeFund (u h Z₀ s : ℝ) :
    weberM_dn (u + h) h (Z₀ + h * s) * odeFund (qWeb Z₀ (u + h) h) (continuous_qWeb _ _ _) 0 s =
      odeFund (qWeb Z₀ u h) (continuous_qWeb _ _ _) 0 s * weberM_dn (u + h) h Z₀ := by
  let Φ : ℝ → M2 := fun t => odeFund (qWeb Z₀ (u + h) h) (continuous_qWeb _ _ _) 0 t
  let M : ℝ → M2 := fun t => weberM_dn (u + h) h (Z₀ + h * t) * Φ t
  have hZ : ∀ t, HasDerivAt (fun x => Z₀ + h * x) h t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul h).const_add Z₀
  have hM : ∀ (j : Fin 2) (t : ℝ),
      HasDerivAt (fun x => M x 0 j) (M t 1 j) t ∧
      HasDerivAt (fun x => M x 1 j) (qWeb Z₀ u h t * M t 0 j) t := by
    intro j t
    obtain ⟨d0, d1⟩ := odeFund_hasDerivAt (qWeb Z₀ (u + h) h) (continuous_qWeb _ _ _) 0 j t
    have hZ0 : HasDerivAt (fun x => (Z₀ + h * x) / 2) (h / 2) t := (hZ t).div_const 2
    have hZ2 : HasDerivAt (fun x => (Z₀ + h * x) ^ 2 / 4 - (u + h) + h / 2)
        (h * (Z₀ + h * t) / 2) t := by
      have hd := (((hZ t).pow 2).div_const 4).sub_const (u + h) |>.add_const (h / 2)
      refine hd.congr_deriv ?_
      ring
    have e0 : (fun x => M x 0 j) = fun x => (Z₀ + h * x) / 2 * Φ x 0 j + Φ x 1 j :=
      funext fun x => by
        fin_cases j <;> simp [M, Φ, weberM_dn, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have e1 : (fun x => M x 1 j) = fun x =>
        ((Z₀ + h * x) ^ 2 / 4 - (u + h) + h / 2) * Φ x 0 j + (Z₀ + h * x) / 2 * Φ x 1 j :=
      funext fun x => by
        fin_cases j <;> simp [M, Φ, weberM_dn, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e0, e1]
    refine ⟨?_, ?_⟩
    · refine ((hZ0.mul d0).add d1).congr_deriv ?_
      change h / 2 * Φ t 0 j + (Z₀ + h * t) / 2 * Φ t 1 j +
          qWeb Z₀ (u + h) h t * Φ t 0 j = M t 1 j
      fin_cases j <;>
        (simp only [qWeb, M, Φ, weberM_dn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]; ring)
    · refine ((hZ2.mul d0).add (hZ0.mul d1)).congr_deriv ?_
      change h * (Z₀ + h * t) / 2 * Φ t 0 j +
          ((Z₀ + h * t) ^ 2 / 4 - (u + h) + h / 2) * Φ t 1 j +
          (h / 2 * Φ t 1 j + (Z₀ + h * t) / 2 * (qWeb Z₀ (u + h) h t * Φ t 0 j)) =
          qWeb Z₀ u h t * M t 0 j
      fin_cases j <;>
        (simp only [qWeb, M, Φ, weberM_dn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]; ring)
  have hM0 : M 0 = weberM_dn (u + h) h Z₀ := by
    simp [M, Φ, odeFund_self]
  simpa [M, Φ, hM0] using odeFund_right_mul (continuous_qWeb Z₀ u h) 0 hM s

/-! ### Exact Weber shifts at half-integer parameters -/

lemma kappaBal_neg_half (j : ℕ) :
    kappaBal (-((j : ℝ) + 1 / 2)) = (Real.sqrt (j.factorial : ℝ))⁻¹ := by
  have hle : -((j : ℝ) + 1 / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
  rw [kappaBal, if_pos hle]
  have harg : (1 : ℝ) / 2 - (-((j : ℝ) + 1 / 2)) = (j : ℝ) + 1 := by ring
  rw [harg, Real.Gamma_nat_eq_factorial, show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]

lemma kappaBal_neg_half_succ (j : ℕ) :
    kappaBal (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) =
      kappaBal (-((j : ℝ) + 1 / 2)) / Real.sqrt ((j : ℝ) + 1) := by
  rw [kappaBal_neg_half (j + 1), kappaBal_neg_half j, Nat.factorial_succ]
  push_cast
  have hf : 0 < (j.factorial : ℝ) := by positivity
  rw [mul_comm ((j : ℝ) + 1), Real.sqrt_mul hf.le, mul_inv]
  ring

private lemma diff_ut_at (a z : ℝ) : DifferentiableAt ℝ (ut pcU a) z :=
  ((hasDerivAt_pcU a z).const_mul (kappaBal a)).differentiableAt

private lemma diff_vt_at (a z : ℝ) : DifferentiableAt ℝ (vt pcV a) z :=
  ((hasDerivAt_pcV a z).const_mul _).differentiableAt

lemma ut_pcU_ode (a z : ℝ) :
    HasDerivAt (deriv (ut pcU a)) ((z ^ 2 / 4 + a) * ut pcU a z) z := by
  have heq : deriv (ut pcU a) = fun t => kappaBal a * pcUD a t := funext fun t => by
    change deriv (fun s => kappaBal a * pcU a s) t = kappaBal a * pcUD a t
    rw [deriv_const_mul _ (hasDerivAt_pcU a t).differentiableAt, (hasDerivAt_pcU a t).deriv]
  rw [heq]
  have h1 := (hasDerivAt_pcUD a z).const_mul (kappaBal a)
  refine h1.congr_deriv ?_
  change kappaBal a * ((z ^ 2 / 4 + a) * pcU a z) = (z ^ 2 / 4 + a) * (kappaBal a * pcU a z)
  ring

lemma vt_pcV_ode (a z : ℝ) :
    HasDerivAt (deriv (vt pcV a)) ((z ^ 2 / 4 + a) * vt pcV a z) z := by
  have heq : deriv (vt pcV a) = fun t => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcVD a t :=
    funext fun t => by
      change deriv (fun s => Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a s) t = _
      rw [deriv_const_mul _ (hasDerivAt_pcV a t).differentiableAt, (hasDerivAt_pcV a t).deriv]
  rw [heq]
  have h1 := (hasDerivAt_pcVD a z).const_mul (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹)
  refine h1.congr_deriv ?_
  change Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * ((z ^ 2 / 4 + a) * pcV a z) =
    (z ^ 2 / 4 + a) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a z)
  ring

private lemma deriv_eq_of_shift {a : ℝ} {f f' : ℝ → ℝ}
    (hf' : ∀ z, HasDerivAt f' (deriv f' z) z)
    (hode : ∀ z, HasDerivAt (deriv f') ((z ^ 2 / 4 + a) * f' z) z)
    {c : ℝ} (hc : 0 < c) (h0 : ∀ z, c * f z = z / 2 * f' z - deriv f' z) (z : ℝ) :
    c * deriv f z = -(z ^ 2 / 4 + a - 1 / 2) * f' z + z / 2 * deriv f' z := by
  have hd : HasDerivAt (fun w => w / 2 * f' w - deriv f' w)
      ((1 / 2 * f' z + z / 2 * deriv f' z) - (z ^ 2 / 4 + a) * f' z) z := by
    have h1 := ((hasDerivAt_id z).div_const 2).mul (hf' z)
    exact (h1.sub (hode z)).congr_deriv (by simp only [id_eq])
  have hdf : DifferentiableAt ℝ f z := by
    have hfn : (fun w => (w / 2 * f' w - deriv f' w) / c) = f := funext fun w => by
      rw [← h0 w]; field_simp [hc.ne']
    exact hfn ▸ (hd.differentiableAt.div_const c)
  have hdL : HasDerivAt (fun w => c * f w) (c * deriv f z) z := hdf.hasDerivAt.const_mul c
  have heq := hdL.unique (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall h0))
  linarith

private lemma deriv_eq_of_shift_dn {a : ℝ} {f f' : ℝ → ℝ}
    (hf' : ∀ z, HasDerivAt f' (deriv f' z) z)
    (hode : ∀ z, HasDerivAt (deriv f') ((z ^ 2 / 4 + a) * f' z) z)
    {c : ℝ} (hc : 0 < c) (h0 : ∀ z, c * f z = z / 2 * f' z + deriv f' z) (z : ℝ) :
    c * deriv f z = (z ^ 2 / 4 + a + 1 / 2) * f' z + z / 2 * deriv f' z := by
  have hd : HasDerivAt (fun w => w / 2 * f' w + deriv f' w)
      ((1 / 2 * f' z + z / 2 * deriv f' z) + (z ^ 2 / 4 + a) * f' z) z := by
    have h1 := ((hasDerivAt_id z).div_const 2).mul (hf' z)
    exact (h1.add (hode z)).congr_deriv (by simp only [id_eq])
  have hdf : DifferentiableAt ℝ f z := by
    have hfn : (fun w => (w / 2 * f' w + deriv f' w) / c) = f := funext fun w => by
      rw [← h0 w]; field_simp [hc.ne']
    exact hfn ▸ (hd.differentiableAt.div_const c)
  have hdL : HasDerivAt (fun w => c * f w) (c * deriv f z) z := hdf.hasDerivAt.const_mul c
  have heq := hdL.unique (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall h0))
  linarith

private lemma weber_shift_step {h a' v Z₀ Z₁ c : ℝ} (hh : 0 < h) (hv : v = -a' * h)
    {f f' : ℝ → ℝ} (hf' : ∀ z, HasDerivAt f' (deriv f' z) z)
    (hode : ∀ z, HasDerivAt (deriv f') ((z ^ 2 / 4 + a') * f' z) z)
    {M : M2}
    (hM : colMul M ![f (Z₀ / Real.sqrt h), Real.sqrt h * deriv f (Z₀ / Real.sqrt h)] =
      c • ![f' (Z₀ / Real.sqrt h), Real.sqrt h * deriv f' (Z₀ / Real.sqrt h)]) :
    c • ![f' (Z₁ / Real.sqrt h), Real.sqrt h * deriv f' (Z₁ / Real.sqrt h)] =
      colMul (odeFund (fun t => (Z₀ + h * t) ^ 2 / 4 - v) (by fun_prop) 0 ((Z₁ - Z₀) / h) * M)
        ![f (Z₀ / Real.sqrt h), Real.sqrt h * deriv f (Z₀ / Real.sqrt h)] := by
  rw [colMul_assoc_mat, hM]
  have hcol := odeFund_pc_step hh hv hf' hode (Z₀ := Z₀) (Z₁ := Z₁)
  calc c • ![f' (Z₁ / Real.sqrt h), Real.sqrt h * deriv f' (Z₁ / Real.sqrt h)]
      = c • colMul (odeFund (fun t => (Z₀ + h * t) ^ 2 / 4 - v) (by fun_prop) 0 ((Z₁ - Z₀) / h))
          ![f' (Z₀ / Real.sqrt h), Real.sqrt h * deriv f' (Z₀ / Real.sqrt h)] := by rw [hcol]
    _ = colMul (odeFund (fun t => (Z₀ + h * t) ^ 2 / 4 - v) (by fun_prop) 0 ((Z₁ - Z₀) / h))
          (c • ![f' (Z₀ / Real.sqrt h), Real.sqrt h * deriv f' (Z₀ / Real.sqrt h)]) := by
        ext i; fin_cases i <;> (simp [colMul]; try ring)

private lemma colMul_weberM_up_apply {h Z c : ℝ} (u : ℝ) (hh : 0 < h) {f f' : ℝ → ℝ}
    (h0 : c * f' (Z / Real.sqrt h) =
      (Z / Real.sqrt h) / 2 * f (Z / Real.sqrt h) - deriv f (Z / Real.sqrt h))
    (h1 : c * deriv f' (Z / Real.sqrt h) =
      -((Z / Real.sqrt h) ^ 2 / 4 - u / h - 1 / 2) * f (Z / Real.sqrt h) +
        (Z / Real.sqrt h) / 2 * deriv f (Z / Real.sqrt h)) :
    colMul (weberM_up u h Z) ![f (Z / Real.sqrt h), Real.sqrt h * deriv f (Z / Real.sqrt h)] =
      (Real.sqrt h * c) • ![f' (Z / Real.sqrt h), Real.sqrt h * deriv f' (Z / Real.sqrt h)] := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  ext i; fin_cases i
  · simp only [colMul, weberM_up, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_cons, Matrix.mulVec_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    calc Z / 2 * f (Z / Real.sqrt h) + -1 * (Real.sqrt h * deriv f (Z / Real.sqrt h))
        = Real.sqrt h * ((Z / Real.sqrt h) / 2 * f (Z / Real.sqrt h) - deriv f (Z / Real.sqrt h)) := by
          field_simp [hs.ne']; ring
      _ = Real.sqrt h * (c * f' (Z / Real.sqrt h)) := by rw [← h0]
      _ = Real.sqrt h * c * f' (Z / Real.sqrt h) := by ring
  · simp only [colMul, weberM_up, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_cons, Matrix.mulVec_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    calc (-(Z ^ 2 / 4 - u) + h / 2) * f (Z / Real.sqrt h) +
          Z / 2 * (Real.sqrt h * deriv f (Z / Real.sqrt h))
        = h * (-((Z / Real.sqrt h) ^ 2 / 4 - u / h - 1 / 2) * f (Z / Real.sqrt h) +
            (Z / Real.sqrt h) / 2 * deriv f (Z / Real.sqrt h)) := by
          field_simp [hs.ne', hh.ne']; rw [hsq]; ring
      _ = h * (c * deriv f' (Z / Real.sqrt h)) := by rw [← h1]
      _ = Real.sqrt h * c * (Real.sqrt h * deriv f' (Z / Real.sqrt h)) := by
          calc h * (c * deriv f' (Z / Real.sqrt h))
              = Real.sqrt h ^ 2 * (c * deriv f' (Z / Real.sqrt h)) := by rw [hsq]
            _ = _ := by ring

private lemma colMul_weberM_dn_apply {h Z c : ℝ} (u : ℝ) (hh : 0 < h) {f f' : ℝ → ℝ}
    (h0 : c * f' (Z / Real.sqrt h) =
      (Z / Real.sqrt h) / 2 * f (Z / Real.sqrt h) + deriv f (Z / Real.sqrt h))
    (h1 : c * deriv f' (Z / Real.sqrt h) =
      ((Z / Real.sqrt h) ^ 2 / 4 - u / h + 1 / 2) * f (Z / Real.sqrt h) +
        (Z / Real.sqrt h) / 2 * deriv f (Z / Real.sqrt h)) :
    colMul (weberM_dn u h Z) ![f (Z / Real.sqrt h), Real.sqrt h * deriv f (Z / Real.sqrt h)] =
      (Real.sqrt h * c) • ![f' (Z / Real.sqrt h), Real.sqrt h * deriv f' (Z / Real.sqrt h)] := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  ext i; fin_cases i
  · simp only [colMul, weberM_dn, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_cons, Matrix.mulVec_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    calc Z / 2 * f (Z / Real.sqrt h) + 1 * (Real.sqrt h * deriv f (Z / Real.sqrt h))
        = Real.sqrt h * ((Z / Real.sqrt h) / 2 * f (Z / Real.sqrt h) + deriv f (Z / Real.sqrt h)) := by
          field_simp [hs.ne']
      _ = Real.sqrt h * (c * f' (Z / Real.sqrt h)) := by rw [← h0]
      _ = Real.sqrt h * c * f' (Z / Real.sqrt h) := by ring
  · simp only [colMul, weberM_dn, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_cons, Matrix.mulVec_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    calc ((Z ^ 2 / 4 - u) + h / 2) * f (Z / Real.sqrt h) +
          Z / 2 * (Real.sqrt h * deriv f (Z / Real.sqrt h))
        = h * (((Z / Real.sqrt h) ^ 2 / 4 - u / h + 1 / 2) * f (Z / Real.sqrt h) +
            (Z / Real.sqrt h) / 2 * deriv f (Z / Real.sqrt h)) := by
          field_simp [hs.ne', hh.ne']; rw [hsq]; ring
      _ = h * (c * deriv f' (Z / Real.sqrt h)) := by rw [← h1]
      _ = Real.sqrt h * c * (Real.sqrt h * deriv f' (Z / Real.sqrt h)) := by
          calc h * (c * deriv f' (Z / Real.sqrt h))
              = Real.sqrt h ^ 2 * (c * deriv f' (Z / Real.sqrt h)) := by rw [hsq]
            _ = _ := by ring

private lemma ut_pcU_shift_up (j : ℕ) (z : ℝ) :
    Real.sqrt ((j : ℝ) + 1) * ut pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) z =
      z / 2 * ut pcU (-((j : ℝ) + 1 / 2)) z - deriv (ut pcU (-((j : ℝ) + 1 / 2))) z ∧
    Real.sqrt ((j : ℝ) + 1) * deriv (ut pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2))) z =
      -(z ^ 2 / 4 - ((j : ℝ) + 1 / 2) - 1 / 2) * ut pcU (-((j : ℝ) + 1 / 2)) z +
        z / 2 * deriv (ut pcU (-((j : ℝ) + 1 / 2))) z := by
  have h0 : ∀ w, Real.sqrt ((j : ℝ) + 1) * ut pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w =
      w / 2 * ut pcU (-((j : ℝ) + 1 / 2)) w - deriv (ut pcU (-((j : ℝ) + 1 / 2))) w := by
    intro w
    have hrec := pc_shift_U_dn (-((j : ℝ) + 1 / 2)) w
    have hsub : -((j : ℝ) + 1 / 2) - 1 = -(((j + 1 : ℕ) : ℝ) + 1 / 2) := by push_cast; ring
    rw [hsub] at hrec
    have hd : deriv (ut pcU (-((j : ℝ) + 1 / 2))) w =
        kappaBal (-((j : ℝ) + 1 / 2)) * deriv (pcU (-((j : ℝ) + 1 / 2))) w := by
      change deriv (fun s => kappaBal _ * pcU _ s) w = _
      exact deriv_const_mul _ (hasDerivAt_pcU _ w).differentiableAt
    have hs : 0 < Real.sqrt ((j : ℝ) + 1) := by positivity
    change Real.sqrt ((j : ℝ) + 1) * (kappaBal _ * pcU _ w) = _
    rw [kappaBal_neg_half_succ j, hd]
    calc Real.sqrt ((j : ℝ) + 1) * ((kappaBal (-((j : ℝ) + 1 / 2)) / Real.sqrt ((j : ℝ) + 1)) *
          pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w)
        = kappaBal (-((j : ℝ) + 1 / 2)) * pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w := by
            field_simp [hs.ne']
      _ = kappaBal (-((j : ℝ) + 1 / 2)) * (w / 2 * pcU (-((j : ℝ) + 1 / 2)) w -
            deriv (pcU (-((j : ℝ) + 1 / 2))) w) := by congr 1; linarith
      _ = w / 2 * ut pcU (-((j : ℝ) + 1 / 2)) w -
            kappaBal (-((j : ℝ) + 1 / 2)) * deriv (pcU (-((j : ℝ) + 1 / 2))) w := by
            change _ = w / 2 * (kappaBal _ * pcU _ w) - _; ring
  refine ⟨h0 z, ?_⟩
  have h1 := deriv_eq_of_shift (fun w => ((diff_ut_at _ w).hasDerivAt)) (ut_pcU_ode _) (by positivity) h0 z
  convert h1 using 2

private lemma ut_pcU_shift_dn {j : ℕ} (hj : 1 ≤ j) (z : ℝ) :
    Real.sqrt (j : ℝ) * ut pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) z =
      z / 2 * ut pcU (-((j : ℝ) + 1 / 2)) z + deriv (ut pcU (-((j : ℝ) + 1 / 2))) z ∧
    Real.sqrt (j : ℝ) * deriv (ut pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2))) z =
      (z ^ 2 / 4 - ((j : ℝ) + 1 / 2) + 1 / 2) * ut pcU (-((j : ℝ) + 1 / 2)) z +
        z / 2 * deriv (ut pcU (-((j : ℝ) + 1 / 2))) z := by
  have h0 : ∀ w, Real.sqrt (j : ℝ) * ut pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w =
      w / 2 * ut pcU (-((j : ℝ) + 1 / 2)) w + deriv (ut pcU (-((j : ℝ) + 1 / 2))) w := by
    intro w
    have hrec := pc_shift_U_up (-((j : ℝ) + 1 / 2)) w
    have hadd : -((j : ℝ) + 1 / 2) + 1 = -(((j - 1 : ℕ) : ℝ) + 1 / 2) := by
      have : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj]; norm_num
      rw [this]; ring
    rw [hadd] at hrec
    have hd : deriv (ut pcU (-((j : ℝ) + 1 / 2))) w =
        kappaBal (-((j : ℝ) + 1 / 2)) * deriv (pcU (-((j : ℝ) + 1 / 2))) w := by
      change deriv (fun s => kappaBal _ * pcU _ s) w = _
      exact deriv_const_mul _ (hasDerivAt_pcU _ w).differentiableAt
    have hjm : j = (j - 1) + 1 := by omega
    have hκ : kappaBal (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) =
        Real.sqrt (j : ℝ) * kappaBal (-((j : ℝ) + 1 / 2)) := by
      have hκs := kappaBal_neg_half_succ (j - 1)
      have hjr : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by exact_mod_cast hjm.symm
      rw [← hjm, hjr] at hκs
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      have hs : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hjpos).ne'
      rw [hκs]
      field_simp [hs]
    change Real.sqrt (j : ℝ) * (kappaBal _ * pcU _ w) = _
    rw [hκ, hd]
    have hsq : Real.sqrt (j : ℝ) * Real.sqrt (j : ℝ) = (j : ℝ) := Real.mul_self_sqrt (by positivity)
    have hjmul : (j : ℝ) * pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w =
        deriv (pcU (-((j : ℝ) + 1 / 2))) w + w / 2 * pcU (-((j : ℝ) + 1 / 2)) w := by
      linarith
    calc Real.sqrt (j : ℝ) * (Real.sqrt (j : ℝ) * kappaBal (-((j : ℝ) + 1 / 2)) *
          pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w)
        = (Real.sqrt (j : ℝ) * Real.sqrt (j : ℝ)) * kappaBal (-((j : ℝ) + 1 / 2)) *
            pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w := by ring
      _ = kappaBal (-((j : ℝ) + 1 / 2)) * ((j : ℝ) * pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w) := by
            rw [hsq]; ring
      _ = kappaBal (-((j : ℝ) + 1 / 2)) * (deriv (pcU (-((j : ℝ) + 1 / 2))) w +
            w / 2 * pcU (-((j : ℝ) + 1 / 2)) w) := by rw [hjmul]
      _ = w / 2 * ut pcU (-((j : ℝ) + 1 / 2)) w +
            kappaBal (-((j : ℝ) + 1 / 2)) * deriv (pcU (-((j : ℝ) + 1 / 2))) w := by
            change _ = w / 2 * (kappaBal _ * pcU _ w) + _; ring
  refine ⟨h0 z, ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hs0 : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hjpos
  have h1 := deriv_eq_of_shift_dn (fun w => ((diff_ut_at _ w).hasDerivAt)) (ut_pcU_ode _) hs0 h0 z
  convert h1 using 2

private lemma vt_pcV_shift_up (j : ℕ) (z : ℝ) :
    Real.sqrt ((j : ℝ) + 1) * vt pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) z =
      z / 2 * vt pcV (-((j : ℝ) + 1 / 2)) z - deriv (vt pcV (-((j : ℝ) + 1 / 2))) z ∧
    Real.sqrt ((j : ℝ) + 1) * deriv (vt pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2))) z =
      -(z ^ 2 / 4 - ((j : ℝ) + 1 / 2) - 1 / 2) * vt pcV (-((j : ℝ) + 1 / 2)) z +
        z / 2 * deriv (vt pcV (-((j : ℝ) + 1 / 2))) z := by
  have h0 : ∀ w, Real.sqrt ((j : ℝ) + 1) * vt pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w =
      w / 2 * vt pcV (-((j : ℝ) + 1 / 2)) w - deriv (vt pcV (-((j : ℝ) + 1 / 2))) w := by
    intro w
    have hrec := pc_shift_V_dn (-((j : ℝ) + 1 / 2)) w
    have hsub : -((j : ℝ) + 1 / 2) - 1 = -(((j + 1 : ℕ) : ℝ) + 1 / 2) := by push_cast; ring
    rw [hsub] at hrec
    have hd : deriv (vt pcV (-((j : ℝ) + 1 / 2))) w =
        Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ * deriv (pcV (-((j : ℝ) + 1 / 2))) w := by
      change deriv (fun s => _ * pcV _ s) w = _
      exact deriv_const_mul _ (hasDerivAt_pcV _ w).differentiableAt
    have hsq : Real.sqrt ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) = (j : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hj1 : ((j : ℝ) + 1) * pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w =
        w / 2 * pcV (-((j : ℝ) + 1 / 2)) w - deriv (pcV (-((j : ℝ) + 1 / 2))) w := by linarith
    change Real.sqrt ((j : ℝ) + 1) * (Real.sqrt (Real.pi / 2) * _ * pcV _ w) = _
    rw [kappaBal_neg_half_succ j, inv_div, hd]
    calc Real.sqrt ((j : ℝ) + 1) * (Real.sqrt (Real.pi / 2) *
          (Real.sqrt ((j : ℝ) + 1) / kappaBal (-((j : ℝ) + 1 / 2))) *
          pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w)
        = Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ *
            ((Real.sqrt ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1)) * pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)) w) := by
          ring
      _ = Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ *
            (w / 2 * pcV (-((j : ℝ) + 1 / 2)) w - deriv (pcV (-((j : ℝ) + 1 / 2))) w) := by
          rw [hsq, hj1]
      _ = w / 2 * vt pcV (-((j : ℝ) + 1 / 2)) w -
          Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ * deriv (pcV (-((j : ℝ) + 1 / 2))) w := by
          change _ = w / 2 * (Real.sqrt (Real.pi / 2) * _ * pcV _ w) - _; ring
  refine ⟨h0 z, ?_⟩
  have h1 := deriv_eq_of_shift (fun w => ((diff_vt_at _ w).hasDerivAt)) (vt_pcV_ode _) (by positivity) h0 z
  convert h1 using 2

private lemma vt_pcV_shift_dn {j : ℕ} (hj : 1 ≤ j) (z : ℝ) :
    Real.sqrt (j : ℝ) * vt pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) z =
      z / 2 * vt pcV (-((j : ℝ) + 1 / 2)) z + deriv (vt pcV (-((j : ℝ) + 1 / 2))) z ∧
    Real.sqrt (j : ℝ) * deriv (vt pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2))) z =
      (z ^ 2 / 4 - ((j : ℝ) + 1 / 2) + 1 / 2) * vt pcV (-((j : ℝ) + 1 / 2)) z +
        z / 2 * deriv (vt pcV (-((j : ℝ) + 1 / 2))) z := by
  have h0 : ∀ w, Real.sqrt (j : ℝ) * vt pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w =
      w / 2 * vt pcV (-((j : ℝ) + 1 / 2)) w + deriv (vt pcV (-((j : ℝ) + 1 / 2))) w := by
    intro w
    have hrec := pc_shift_V_up (-((j : ℝ) + 1 / 2)) w
    have hadd : -((j : ℝ) + 1 / 2) + 1 = -(((j - 1 : ℕ) : ℝ) + 1 / 2) := by
      have : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj]; norm_num
      rw [this]; ring
    rw [hadd] at hrec
    have hd : deriv (vt pcV (-((j : ℝ) + 1 / 2))) w =
        Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ * deriv (pcV (-((j : ℝ) + 1 / 2))) w := by
      change deriv (fun s => _ * pcV _ s) w = _
      exact deriv_const_mul _ (hasDerivAt_pcV _ w).differentiableAt
    have hjm : j = (j - 1) + 1 := by omega
    have hκinv : (kappaBal (-(((j - 1 : ℕ) : ℝ) + 1 / 2)))⁻¹ =
        (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ / Real.sqrt (j : ℝ) := by
      have hκs := kappaBal_neg_half_succ (j - 1)
      have hjr : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by exact_mod_cast hjm.symm
      rw [← hjm, hjr] at hκs
      rw [hκs, inv_div]; field_simp
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have hs : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hjpos).ne'
    change Real.sqrt (j : ℝ) * (Real.sqrt (Real.pi / 2) * _ * pcV _ w) = _
    rw [hκinv, hd]
    calc Real.sqrt (j : ℝ) * (Real.sqrt (Real.pi / 2) *
          ((kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ / Real.sqrt (j : ℝ)) *
          pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w)
        = Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ *
            pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2)) w := by field_simp [hs]
      _ = Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ *
            (w / 2 * pcV (-((j : ℝ) + 1 / 2)) w + deriv (pcV (-((j : ℝ) + 1 / 2))) w) := by
          congr 1; linarith
      _ = w / 2 * vt pcV (-((j : ℝ) + 1 / 2)) w +
          Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ * deriv (pcV (-((j : ℝ) + 1 / 2))) w := by
          change _ = w / 2 * (Real.sqrt (Real.pi / 2) * _ * pcV _ w) + _; ring
  refine ⟨h0 z, ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hs0 : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hjpos
  have h1 := deriv_eq_of_shift_dn (fun w => ((diff_vt_at _ w).hasDerivAt)) (vt_pcV_ode _) hs0 h0 z
  convert h1 using 2

/-- **Weber ladder is a `SymplecticLadder` (`charts.tex`, `lem:cha-weber-ladder`)** for any `Y : ℝ → ℝ`. -/
theorem weber_symplecticLadder (Y : ℝ → ℝ) {pp qq : ℝ → ℝ → ℝ} :
    SymplecticLadder (1 / 2) ddWeb d2Web pp qq (weberPiP Y) (weberPiM Y) (wWeb Y) omegaWeb where
  wronsk := fun h hh j => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    let u := ((j : ℝ) + 1 / 2) * h
    let a := -(u / h)
    let z := Y u / Real.sqrt h
    have hud : deriv (ut pcU a) z = kappaBal a * deriv (pcU a) z := by
      change deriv (fun s => kappaBal a * pcU a s) z = _; exact deriv_const_mul _ (hasDerivAt_pcU a z).differentiableAt
    have hvd : deriv (vt pcV a) z = Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z := by
      change deriv (fun s => _ * pcV a s) z = _; exact deriv_const_mul _ (hasDerivAt_pcV a z).differentiableAt
    have hwr := pc_wronsk a z
    have hκ := (kappaBal_pos a).ne'
    have hpi : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      norm_num
    simp only [wWeb, hn, ↓reduceIte, colDet, Matrix.cons_val_zero, Matrix.cons_val_one, omegaWeb]
    change ut pcU a z * (Real.sqrt h * deriv (vt pcV a) z) -
      (Real.sqrt h * deriv (ut pcU a) z) * vt pcV a z = Real.sqrt h
    change kappaBal a * pcU a z * (Real.sqrt h * deriv (vt pcV a) z) -
      Real.sqrt h * deriv (ut pcU a) z * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a z) = Real.sqrt h
    rw [hud, hvd]
    calc kappaBal a * pcU a z * (Real.sqrt h * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z)) -
          Real.sqrt h * (kappaBal a * deriv (pcU a) z) * (Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹ * pcV a z)
        = Real.sqrt h * Real.sqrt (Real.pi / 2) * (kappaBal a * (kappaBal a)⁻¹) *
            (pcU a z * deriv (pcV a) z - deriv (pcU a) z * pcV a z) := by ring
      _ = Real.sqrt h * (Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi)) := by
            rw [mul_inv_cancel₀ hκ, hwr]; ring
      _ = Real.sqrt h := by rw [hpi, mul_one]
  wronsk_ne := fun h hh => (Real.sqrt_pos.mpr hh).ne'
  shift_up := fun α h hh j => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    set u := ((j : ℝ) + 1 / 2) * h with hu_def
    have hj1 : (((j + 1 : ℕ) : ℝ) + 1 / 2) * h = u + h := by dsimp [u]; push_cast; ring
    have ha0 : -(u / h) = -((j : ℝ) + 1 / 2) := by dsimp [u]; field_simp [hh.ne']
    have ha1 : -((u + h) / h) = -(((j + 1 : ℕ) : ℝ) + 1 / 2) := by
      dsimp [u]; push_cast; field_simp [hh.ne']; ring
    have hv : u + h = -(-(((j + 1 : ℕ) : ℝ) + 1 / 2)) * h := by dsimp [u]; push_cast; ring
    have hDp : Dp ddWeb u h = Real.sqrt h * Real.sqrt ((j : ℝ) + 1) := by
      dsimp [Dp, ddWeb, u]
      rw [show ((j : ℝ) + 1 / 2) * h + h / 2 = h * ((j : ℝ) + 1) by ring, Real.sqrt_mul hh.le]
    have hs : weberStepUp Y u h = (Y (u + h) - Y u) / h := by simp [weberStepUp, hh.ne']
    have hu_div : u / h = (j : ℝ) + 1 / 2 := by dsimp [u]; field_simp [hh.ne']
    match α with
    | 0 =>
      have hsh := ut_pcU_shift_up j (Y u / Real.sqrt h)
      have hM := colMul_weberM_up_apply u hh
        (f := ut pcU (-((j : ℝ) + 1 / 2))) (f' := ut pcU (-(((j + 1 : ℕ) : ℝ) + 1 / 2)))
        hsh.1 (by rw [hu_div]; convert hsh.2 using 2 <;> ring)
      have hst := weber_shift_step hh hv (Z₀ := Y u) (Z₁ := Y (u + h))
        (fun z => (diff_ut_at _ z).hasDerivAt) (ut_pcU_ode _) hM
      dsimp only [weberPiP, weberPhiP, wWeb]
      rw [if_neg hn, if_neg hn, ha0, ha1, hDp, hs]
      exact hst
    | 1 =>
      have hsh := vt_pcV_shift_up j (Y u / Real.sqrt h)
      have hM := colMul_weberM_up_apply u hh
        (f := vt pcV (-((j : ℝ) + 1 / 2))) (f' := vt pcV (-(((j + 1 : ℕ) : ℝ) + 1 / 2)))
        hsh.1 (by rw [hu_div]; convert hsh.2 using 2 <;> ring)
      have hst := weber_shift_step hh hv (Z₀ := Y u) (Z₁ := Y (u + h))
        (fun z => (diff_vt_at _ z).hasDerivAt) (vt_pcV_ode _) hM
      dsimp only [weberPiP, weberPhiP, wWeb]
      rw [if_neg hn, if_neg hn, ha0, ha1, hDp, hs]
      exact hst
  shift_dn := fun α h hh j hj => by
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    set u := ((j : ℝ) + 1 / 2) * h with hu_def
    have hjm : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj]; norm_num
    have hj1 : (((j - 1 : ℕ) : ℝ) + 1 / 2) * h = u - h := by dsimp [u]; rw [hjm]; ring
    have ha0 : -(u / h) = -((j : ℝ) + 1 / 2) := by dsimp [u]; field_simp [hh.ne']
    have ha1 : -((u - h) / h) = -(((j - 1 : ℕ) : ℝ) + 1 / 2) := by
      dsimp [u]; rw [hjm]; field_simp [hh.ne']; ring
    have hv : u - h = -(-(((j - 1 : ℕ) : ℝ) + 1 / 2)) * h := by dsimp [u]; rw [hjm]; ring
    have hDm : Dm ddWeb u h = Real.sqrt h * Real.sqrt (j : ℝ) := by
      dsimp [Dm, ddWeb, u]
      rw [show ((j : ℝ) + 1 / 2) * h - h / 2 = h * (j : ℝ) by ring, Real.sqrt_mul hh.le]
    have hs : weberStepDn Y u h = (Y (u - h) - Y u) / h := by simp [weberStepDn, hh.ne']
    have hu_div : u / h = (j : ℝ) + 1 / 2 := by dsimp [u]; field_simp [hh.ne']
    match α with
    | 0 =>
      have hsh := ut_pcU_shift_dn hj (Y u / Real.sqrt h)
      have hM := colMul_weberM_dn_apply u hh
        (f := ut pcU (-((j : ℝ) + 1 / 2))) (f' := ut pcU (-(((j - 1 : ℕ) : ℝ) + 1 / 2)))
        hsh.1 (by rw [hu_div]; convert hsh.2 using 2 <;> ring)
      have hst := weber_shift_step hh hv (Z₀ := Y u) (Z₁ := Y (u - h))
        (fun z => (diff_ut_at _ z).hasDerivAt) (ut_pcU_ode _) hM
      dsimp only [weberPiM, weberPhiM, wWeb]
      rw [if_neg hn, if_neg hn, ha0, ha1, hDm, hs]
      exact hst
    | 1 =>
      have hsh := vt_pcV_shift_dn hj (Y u / Real.sqrt h)
      have hM := colMul_weberM_dn_apply u hh
        (f := vt pcV (-((j : ℝ) + 1 / 2))) (f' := vt pcV (-(((j - 1 : ℕ) : ℝ) + 1 / 2)))
        hsh.1 (by rw [hu_div]; convert hsh.2 using 2 <;> ring)
      have hst := weber_shift_step hh hv (Z₀ := Y u) (Z₁ := Y (u - h))
        (fun z => (diff_vt_at _ z).hasDerivAt) (vt_pcV_ode _) hM
      dsimp only [weberPiM, weberPhiM, wWeb]
      rw [if_neg hn, if_neg hn, ha0, ha1, hDm, hs]
      exact hst
  d2_up := fun h hh j => by
    dsimp [Dp, d2Web, ddWeb]
    rw [Real.sq_sqrt]
    nlinarith
  d2_dn := fun h hh j hj => by
    dsimp [Dm, d2Web, ddWeb]
    rw [Real.sq_sqrt]
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  det_up := fun u h => by
    dsimp [weberPiP, weberPhiP]
    rw [Matrix.det_mul, odeFund_det, one_mul, weberM_up_det]; rfl
  det_dn := fun u h => by
    dsimp [weberPiM, weberPhiM]
    rw [Matrix.det_mul, odeFund_det, one_mul, weberM_dn_det]; rfl
  prod := fun u h => by
    let sP := weberStepUp Y u h
    have hZ : Y u + h * sP = Y (u + h) := by
      dsimp [sP, weberStepUp]
      by_cases hh : h = 0
      · simp [hh]
      · simp only [hh, ↓reduceIte]; field_simp [hh]; ring
    have heq : ∀ t, qWeb (Y (u + h)) u h t = qWeb (Y u) u h (t + sP) := fun t => by
      dsimp [qWeb]; rw [← hZ]; ring_nf
    have hstep : weberStepDn Y (u + h) h = -sP := by
      dsimp [weberStepDn, sP, weberStepUp]
      by_cases hh : h = 0
      · simp [hh]
      · simp [hh, add_sub_cancel_right]; ring
    have hcancel := odeFund_shift_mul_cancel
      (continuous_qWeb (Y u) u h) (continuous_qWeb (Y (u + h)) u h) sP heq
    have hintw := weberM_dn_mul_odeFund u h (Y u) sP
    rw [hZ] at hintw
    calc weberPiM Y (u + h) h * weberPiP Y u h
        = weberPhiM Y (u + h) h * (weberM_dn (u + h) h (Y (u + h)) * weberPhiP Y u h) * weberM_up u h (Y u) := by
            simp only [weberPiM, weberPiP, Matrix.mul_assoc]
      _ = (weberPhiM Y (u + h) h * odeFund (qWeb (Y u) u h) (continuous_qWeb _ _ _) 0 sP) *
            (weberM_dn (u + h) h (Y u) * weberM_up u h (Y u)) := by
            dsimp [weberPhiP]; rw [hintw]; simp only [Matrix.mul_assoc]
      _ = (1 : M2) * ((u + h / 2) • (1 : M2)) := by
            have hpm : weberPhiM Y (u + h) h =
                odeFund (qWeb (Y (u + h)) u h) (continuous_qWeb _ _ _) 0 (-sP) := by
              dsimp [weberPhiM]; rw [hstep]
              exact congrArg (fun v => odeFund (qWeb (Y (u + h)) v h) (continuous_qWeb _ v h) 0 (-sP))
                (add_sub_cancel_right u h)
            rw [hpm, hcancel, weberM_dn_mul_up]
      _ = Dp d2Web u h • (1 : M2) := by simp [Dp, d2Web]
  par_D := fun u h => by simp [Dp, Dm, d2Web]; ring
  par_Pi := fun u h => by
    calc weberPiP Y u (-h) = weberPhiP Y u (-h) * weberM_up u (-h) (Y u) := rfl
      _ = (Sg * weberPhiM Y u h * Sg) * (Sg * weberM_dn u h (Y u) * Sg) := by
            rw [weberPhiP_conj_sg, weberM_conj_sg]
      _ = Sg * (weberPhiM Y u h * (Sg * Sg) * weberM_dn u h (Y u)) * Sg := by
            simp only [Matrix.mul_assoc]
      _ = Sg * weberPiM Y u h * Sg := by
            have hSg : Sg * Sg = (1 : M2) := by
              ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two]
            rw [hSg, Matrix.mul_one, weberPiM]

/-- **Hard-edge annihilation (`eq:cha-annih`)** at `j = 0`, `u₀ = h / 2`. -/
theorem weber_annih (Y : ℝ → ℝ) {h : ℝ} (hh : 0 < h) :
    colMul (weberPiM Y ((0 + 1 / 2 : ℝ) * h) h) (wWeb Y 0 ((0 + 1 / 2 : ℝ) * h) h) = 0 := by
  have hn : ¬ h ≤ 0 := not_le.mpr hh
  have hu0 : (0 + 1 / 2 : ℝ) * h = h / 2 := by ring
  have ha : -(h / 2 / h) = -(1 / 2 : ℝ) := by field_simp [hh.ne']
  have h1 : deriv (ut pcU (-(1 / 2 : ℝ))) (Y (h / 2) / Real.sqrt h) =
      -((Y (h / 2) / Real.sqrt h) / 2) * ut pcU (-(1 / 2 : ℝ)) (Y (h / 2) / Real.sqrt h) := by
    have hrec := pc_shift_U_up (-(1 / 2 : ℝ)) (Y (h / 2) / Real.sqrt h)
    have h0 : (-(1 / 2 : ℝ) + 1 / 2) = 0 := by ring
    rw [h0, zero_mul, add_zero] at hrec
    have hd : deriv (ut pcU (-(1 / 2 : ℝ))) (Y (h / 2) / Real.sqrt h) =
        kappaBal (-(1 / 2 : ℝ)) * deriv (pcU (-(1 / 2 : ℝ))) (Y (h / 2) / Real.sqrt h) := by
      change deriv (fun s => kappaBal _ * pcU _ s) _ = _
      exact deriv_const_mul _ (hasDerivAt_pcU _ _).differentiableAt
    change _ = -((Y (h / 2) / Real.sqrt h) / 2) * (kappaBal (-(1 / 2 : ℝ)) * pcU _ _)
    rw [hd]
    linear_combination kappaBal (-(1 / 2 : ℝ)) * hrec
  have hM : colMul (weberM_dn (h / 2) h (Y (h / 2))) (wWeb Y 0 (h / 2) h) = 0 := by
    have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
    have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
    ext i; fin_cases i
    · dsimp
      simp only [colMul, weberM_dn, wWeb, hn, ↓reduceIte, ha, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [h1]; field_simp [hs, hh.ne']; ring
    · dsimp
      simp only [colMul, weberM_dn, wWeb, hn, ↓reduceIte, ha, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [h1]; field_simp [hs, hh.ne']; ring
  rw [hu0, weberPiM, colMul_assoc_mat, hM]
  ext i; fin_cases i <;> simp [colMul]

/-! ### Weber envelopes and `W0` lower bound (`lem:cha-weber-env` (1), `lem:cha-W0`) -/

private lemma ut_neg_half_parity (j : ℕ) (z : ℝ) :
    ut pcU (-((j : ℝ) + 1 / 2)) (-z) = (-1 : ℝ) ^ j * ut pcU (-((j : ℝ) + 1 / 2)) z := by
  have ha : -((j : ℝ) + 1 / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
  have href := pc_reflect (-((j : ℝ) + 1 / 2)) ha z
  have hpi : Real.pi * -((j : ℝ) + 1 / 2) = -((j : ℝ) * Real.pi + Real.pi / 2) := by ring
  have hcos : Real.cos (Real.pi * -((j : ℝ) + 1 / 2)) = 0 := by
    rw [hpi, Real.cos_neg, Real.cos_add_pi_div_two]; simp [Real.sin_nat_mul_pi]
  have hsin : -Real.sin (Real.pi * -((j : ℝ) + 1 / 2)) = (-1 : ℝ) ^ j := by
    rw [hpi, Real.sin_neg, neg_neg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  rw [hcos, zero_mul, zero_mul, add_zero, hsin] at href
  dsimp [ut]; rw [href]; ring

private lemma vt_neg_half_parity (j : ℕ) (z : ℝ) :
    vt pcV (-((j : ℝ) + 1 / 2)) (-z) = -((-1 : ℝ) ^ j) * vt pcV (-((j : ℝ) + 1 / 2)) z := by
  have href := pc_reflect_V (-((j : ℝ) + 1 / 2)) z
  have hpi : Real.pi * -((j : ℝ) + 1 / 2) = -((j : ℝ) * Real.pi + Real.pi / 2) := by ring
  have hcos : Real.cos (Real.pi * -((j : ℝ) + 1 / 2)) = 0 := by
    rw [hpi, Real.cos_neg, Real.cos_add_pi_div_two]; simp [Real.sin_nat_mul_pi]
  have hsin : Real.sin (Real.pi * -((j : ℝ) + 1 / 2)) = -((-1 : ℝ) ^ j) := by
    rw [hpi, Real.sin_neg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  rw [hcos, zero_div, zero_mul, zero_add, hsin] at href
  dsimp [vt]; rw [href]; ring

lemma weber_k2_le (j : ℕ) (z : ℝ) :
    k2 (-((j : ℝ) + 1 / 2)) z ≤ (1 + |z| + Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 := by
  unfold k2
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 / 2 := by positivity
  have hs : 0 ≤ Real.sqrt (2 * ((j : ℝ) + 1 / 2)) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * ((j : ℝ) + 1 / 2)) ^ 2 = 2 * ((j : ℝ) + 1 / 2) :=
    Real.sq_sqrt (by positivity)
  have hsqz : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  refine max_le ?_ ?_
  · calc |z ^ 2 / 4 + -((j : ℝ) + 1 / 2)| ≤ z ^ 2 / 4 + ((j : ℝ) + 1 / 2) := by
          rw [← sub_eq_add_neg]; exact (abs_sub _ _).trans (by
            rw [abs_of_nonneg (by positivity), abs_of_nonneg hj])
      _ = (|z| / 2) ^ 2 + (Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 / 2 := by
          rw [hsqz, hsq]; ring
      _ ≤ (1 + |z| + Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 := by nlinarith [abs_nonneg z]
  · have hmax : max |-((j : ℝ) + 1 / 2)| 1 ≤ (1 + Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 := by
      refine max_le ?_ (by nlinarith)
      rw [abs_neg, abs_of_nonneg hj]
      nlinarith [hsq]
    have hm1 : (1 : ℝ) ≤ max |-((j : ℝ) + 1 / 2)| 1 := le_max_right _ _
    calc (max |-((j : ℝ) + 1 / 2)| 1) ^ ((1 : ℝ) / 3)
        ≤ (max |-((j : ℝ) + 1 / 2)| 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = max |-((j : ℝ) + 1 / 2)| 1 := Real.rpow_one _
      _ ≤ (1 + Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 := hmax
      _ ≤ (1 + |z| + Real.sqrt (2 * ((j : ℝ) + 1 / 2))) ^ 2 := by nlinarith [abs_nonneg z]

/-- **Weber envelopes (`lem:cha-weber-env` (1))**: two-sided bounds on all `z : ℝ`. -/
theorem weber_env_well : ∃ CW : ℝ, 0 < CW ∧ ∀ (j : ℕ) (z : ℝ),
    |ut pcU (-((j : ℝ) + 1 / 2)) z| +
        (k2 (-((j : ℝ) + 1 / 2)) z) ^ (-(1 : ℝ) / 2) * |deriv (ut pcU (-((j : ℝ) + 1 / 2))) z| ≤
      2 * CW * Ewell (-((j : ℝ) + 1 / 2)) |z| * Mbal (-((j : ℝ) + 1 / 2)) z ∧
    |vt pcV (-((j : ℝ) + 1 / 2)) z| +
        (k2 (-((j : ℝ) + 1 / 2)) z) ^ (-(1 : ℝ) / 2) * |deriv (vt pcV (-((j : ℝ) + 1 / 2))) z| ≤
      2 * CW * (Ewell (-((j : ℝ) + 1 / 2)) |z|)⁻¹ * Mbal (-((j : ℝ) + 1 / 2)) z := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  refine ⟨CPC, lt_of_lt_of_le env.cPC_pos env.cPC_le, fun j z => ?_⟩
  have ha : -((j : ℝ) + 1 / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hk_pos : 0 < k2 (-((j : ℝ) + 1 / 2)) |z| := k2_pos _ _
  have hev_k2 : k2 (-((j : ℝ) + 1 / 2)) z = k2 (-((j : ℝ) + 1 / 2)) |z| := by
    unfold k2; rw [sq_abs]
  have hev_M : Mbal (-((j : ℝ) + 1 / 2)) z = Mbal (-((j : ℝ) + 1 / 2)) |z| := by
    unfold Mbal; rw [hev_k2]
  have hwell := env.env_well _ ha |z| (abs_nonneg z)
  have hlhs_le : ∀ (x y C' : ℝ), Real.sqrt (x ^ 2 + y ^ 2 / k2 (-((j : ℝ) + 1 / 2)) |z|) ≤ C' →
      |x| + (k2 (-((j : ℝ) + 1 / 2)) |z|) ^ (-(1 : ℝ) / 2) * |y| ≤ 2 * C' := by
    intro x y C' hxy
    have h1 : |x| ≤ Real.sqrt (x ^ 2 + y ^ 2 / k2 (-((j : ℝ) + 1 / 2)) |z|) := by
      rw [← Real.sqrt_sq_eq_abs x]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hk_pos.le))
    have h2 : (k2 (-((j : ℝ) + 1 / 2)) |z|) ^ (-(1 : ℝ) / 2) * |y| ≤
        Real.sqrt (x ^ 2 + y ^ 2 / k2 (-((j : ℝ) + 1 / 2)) |z|) := by
      rw [show (-(1 : ℝ) / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hk_pos.le,
        ← Real.sqrt_eq_rpow, ← abs_of_pos (Real.sqrt_pos.mpr hk_pos), ← div_eq_inv_mul,
        ← abs_div, ← Real.sqrt_sq_eq_abs (y / Real.sqrt _), div_pow, Real.sq_sqrt hk_pos.le]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg x))
    linarith
  have hu_abs : |ut pcU (-((j : ℝ) + 1 / 2)) z| = abs (ut pcU (-((j : ℝ) + 1 / 2)) |z|) := by
    rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg hz, ← neg_neg z, ut_neg_half_parity, neg_neg, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hdu_abs : |deriv (ut pcU (-((j : ℝ) + 1 / 2))) z| =
      abs (deriv (ut pcU (-((j : ℝ) + 1 / 2))) |z|) := by
    rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg hz]
      have hfn : (fun w => ut pcU (-((j : ℝ) + 1 / 2)) (-w)) =
          fun w => (-1 : ℝ) ^ j * ut pcU (-((j : ℝ) + 1 / 2)) w := funext (ut_neg_half_parity j)
      have hd1 : deriv (fun w => ut pcU (-((j : ℝ) + 1 / 2)) (-w)) (-z) =
          -deriv (ut pcU (-((j : ℝ) + 1 / 2))) z := by
        have h := ((diff_ut_at (-((j : ℝ) + 1 / 2)) (-(-z))).hasDerivAt.comp (-z) (hasDerivAt_neg (-z)))
        rw [neg_neg] at h
        exact h.deriv.trans (by ring)
      have hd2 : deriv (fun w => (-1 : ℝ) ^ j * ut pcU (-((j : ℝ) + 1 / 2)) w) (-z) =
          (-1 : ℝ) ^ j * deriv (ut pcU (-((j : ℝ) + 1 / 2))) (-z) :=
        deriv_const_mul _ (diff_ut_at (-((j : ℝ) + 1 / 2)) _)
      rw [hfn] at hd1
      have hdv : -deriv (ut pcU (-((j : ℝ) + 1 / 2))) z =
          (-1 : ℝ) ^ j * deriv (ut pcU (-((j : ℝ) + 1 / 2))) (-z) := hd1.symm.trans hd2
      have hdv' : deriv (ut pcU (-((j : ℝ) + 1 / 2))) z =
          -((-1 : ℝ) ^ j) * deriv (ut pcU (-((j : ℝ) + 1 / 2))) (-z) := by linarith
      rw [hdv', abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hv_abs : |vt pcV (-((j : ℝ) + 1 / 2)) z| = abs (vt pcV (-((j : ℝ) + 1 / 2)) |z|) := by
    rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg hz, ← neg_neg z, vt_neg_half_parity, neg_neg, abs_mul,
        abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hdv_abs : |deriv (vt pcV (-((j : ℝ) + 1 / 2))) z| =
      abs (deriv (vt pcV (-((j : ℝ) + 1 / 2))) |z|) := by
    rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz]
    · rw [abs_of_neg hz]
      have hfn : (fun w => vt pcV (-((j : ℝ) + 1 / 2)) (-w)) =
          fun w => -((-1 : ℝ) ^ j) * vt pcV (-((j : ℝ) + 1 / 2)) w := funext (vt_neg_half_parity j)
      have hd1 : deriv (fun w => vt pcV (-((j : ℝ) + 1 / 2)) (-w)) (-z) =
          -deriv (vt pcV (-((j : ℝ) + 1 / 2))) z := by
        have h := ((diff_vt_at (-((j : ℝ) + 1 / 2)) (-(-z))).hasDerivAt.comp (-z) (hasDerivAt_neg (-z)))
        rw [neg_neg] at h
        exact h.deriv.trans (by ring)
      have hd2 : deriv (fun w => -((-1 : ℝ) ^ j) * vt pcV (-((j : ℝ) + 1 / 2)) w) (-z) =
          -((-1 : ℝ) ^ j) * deriv (vt pcV (-((j : ℝ) + 1 / 2))) (-z) :=
        deriv_const_mul _ (diff_vt_at (-((j : ℝ) + 1 / 2)) _)
      rw [hfn] at hd1
      have hdv : -deriv (vt pcV (-((j : ℝ) + 1 / 2))) z =
          -((-1 : ℝ) ^ j) * deriv (vt pcV (-((j : ℝ) + 1 / 2))) (-z) := hd1.symm.trans hd2
      have hdv' : deriv (vt pcV (-((j : ℝ) + 1 / 2))) z =
          ((-1 : ℝ) ^ j) * deriv (vt pcV (-((j : ℝ) + 1 / 2))) (-z) := by linarith
      rw [hdv', abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [hev_k2, hev_M, hu_abs, hdu_abs, hv_abs, hdv_abs]
  have hu_bound : Real.sqrt (ut pcU (-((j : ℝ) + 1 / 2)) |z| ^ 2 +
      (deriv (ut pcU (-((j : ℝ) + 1 / 2))) |z|) ^ 2 / k2 (-((j : ℝ) + 1 / 2)) |z|) ≤
      CPC * Ewell (-((j : ℝ) + 1 / 2)) |z| * Mbal (-((j : ℝ) + 1 / 2)) |z| := by
    have hd : deriv (ut pcU (-((j : ℝ) + 1 / 2))) |z| =
        kappaBal (-((j : ℝ) + 1 / 2)) * deriv (pcU (-((j : ℝ) + 1 / 2))) |z| := by
      change deriv (fun s => kappaBal _ * pcU _ s) |z| = _
      exact deriv_const_mul _ (hasDerivAt_pcU _ _).differentiableAt
    rw [hd]; exact hwell.1
  have hv_bound : Real.sqrt (vt pcV (-((j : ℝ) + 1 / 2)) |z| ^ 2 +
      (deriv (vt pcV (-((j : ℝ) + 1 / 2))) |z|) ^ 2 / k2 (-((j : ℝ) + 1 / 2)) |z|) ≤
      CPC * (Ewell (-((j : ℝ) + 1 / 2)) |z|)⁻¹ * Mbal (-((j : ℝ) + 1 / 2)) |z| := by
    have hd : deriv (vt pcV (-((j : ℝ) + 1 / 2))) |z| =
        Real.sqrt (Real.pi / 2) * (kappaBal (-((j : ℝ) + 1 / 2)))⁻¹ *
          deriv (pcV (-((j : ℝ) + 1 / 2))) |z| := by
      change deriv (fun s => _ * pcV _ s) |z| = _
      exact deriv_const_mul _ (hasDerivAt_pcV _ _).differentiableAt
    rw [hd]; exact hwell.2
  exact ⟨(hlhs_le _ _ _ hu_bound).trans_eq (by ring), (hlhs_le _ _ _ hv_bound).trans_eq (by ring)⟩

/-- **First Weber branch off the turning point (`lem:cha-W0`)**:
`|ut pcU (-(j + 1/2)) z| ≥ (c₃) E_well(-(j+1/2), |z|) M_bal(-(j+1/2), z)` for `|z| ≥ 2 √(j + 1/2)`. -/
theorem weber_W0 : ∃ c3 : ℝ, 0 < c3 ∧ ∀ (j : ℕ) (z : ℝ),
    2 * Real.sqrt ((j : ℝ) + 1 / 2) ≤ |z| →
    c3 * Ewell (-((j : ℝ) + 1 / 2)) |z| * Mbal (-((j : ℝ) + 1 / 2)) z ≤
      |ut pcU (-((j : ℝ) + 1 / 2)) z| := by
  obtain ⟨cPC, CPC, env⟩ := pcEnvelopeFacts
  refine ⟨cPC / Real.sqrt 17, div_pos env.cPC_pos (Real.sqrt_pos.mpr (by norm_num)), fun j z hz => ?_⟩
  have ha : max (-(-((j : ℝ) + 1 / 2))) (0 : ℝ) = (j : ℝ) + 1 / 2 := by
    rw [neg_neg]; exact max_eq_left (by positivity)
  have hb := (env.beyond (-((j : ℝ) + 1 / 2)) |z| (by rw [ha]; exact hz)).2
  have hev_M : Mbal (-((j : ℝ) + 1 / 2)) z = Mbal (-((j : ℝ) + 1 / 2)) |z| := by
    unfold Mbal k2; rw [sq_abs]
  have hE : Erec (-((j : ℝ) + 1 / 2)) |z| = Ewell (-((j : ℝ) + 1 / 2)) |z| := by
    unfold Erec
    have hn : -((j : ℝ) + 1 / 2) ≤ 0 := neg_nonpos.mpr (by positivity)
    rw [if_pos hn, abs_abs]
  have hu_abs : |ut pcU (-((j : ℝ) + 1 / 2)) z| =
      abs (kappaBal (-((j : ℝ) + 1 / 2)) * pcU (-((j : ℝ) + 1 / 2)) |z|) := by
    rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0]; rfl
    · rw [abs_of_neg hz0, ← neg_neg z, ut_neg_half_parity, neg_neg, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul]; rfl
  rw [hev_M, hu_abs, ← hE]
  exact hb

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_symplecticLadder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_symplecticLadder

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_annih' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_annih

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_env_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_env_well

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.weber_W0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.weber_W0

end FormalResearch.JacobiEigenvectors.Charts

module

public import FormalResearch.SignUncertainty.CtSdHead
public import FormalResearch.SignUncertainty.CtOscIBP

/-!
# Cancellation of the boundary terms at the join `τ₁ = T(s₁)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("at the join `τ = τ₁`, `A` and `Φ_Ph` are
holomorphic across `τ₁`, so the boundary terms of orders `c^{-1}` and `c^{-2}` cancel identically").  **Proved.**
The two first-order boundary quantities `B/ϕ'` and `(B/ϕ')'/ϕ'` of the real tail (`τ`-variable) equal those of the
segment (`w`-variable) because both are the same function of `s` (reparametrisation invariance).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtOsc

/-- Tail side: the boundary quantities `B/ϕ'` and `ibpH/ϕ'` at `T(s₁)` are the `s`-quantities `ρ` and `ρ'/(a+s²)`. -/
theorem tail_bdry {a sl s1 s1' : ℝ} {T T1 : ℝ → ℝ} {B B1 Φ ρ : ℝ → ℂ} {ϕ ϕ1 ϕ2 : ℝ → ℝ} {ρ' : ℂ}
    (hs1 : s1 ∈ Ioo sl s1')
    (hT : ∀ s ∈ Ioo sl s1', HasDerivAt T (T1 s) s) (hT1 : ∀ s ∈ Ioo sl s1', 0 < T1 s)
    (hTpos : ∀ s ∈ Ioo sl s1', 0 < T s)
    (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (ϕ1 τ) τ) (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hϕ1 : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ1 (ϕ2 τ) τ)
    (hBT : ∀ s ∈ Ioo sl s1', B (T s) * ((T1 s : ℝ) : ℂ) = Φ s)
    (hϕT : ∀ s ∈ Ioo sl s1', ϕ (T s) = a * s + s ^ 3 / 3)
    (hne : ∀ s ∈ Ioo sl s1', a + s ^ 2 ≠ 0)
    (hρ : ∀ s ∈ Ioo sl s1', Φ s = ρ s * ((a + s ^ 2 : ℝ) : ℂ))
    (hρd : HasDerivAt ρ ρ' s1) :
    B (T s1) / ((ϕ1 (T s1) : ℝ) : ℂ) = ρ s1 ∧
      ibpH B B1 ϕ1 ϕ2 (T s1) / ((ϕ1 (T s1) : ℝ) : ℂ) = ρ' / ((a + s1 ^ 2 : ℝ) : ℂ) := by
  have hIoo : Ioo sl s1' ∈ 𝓝 s1 := Ioo_mem_nhds hs1.1 hs1.2
  -- derivative of the phase identity
  have hphase : ∀ s ∈ Ioo sl s1', ϕ1 (T s) * T1 s = a + s ^ 2 := by
    intro s hs
    have h1 : HasDerivAt (fun s => ϕ (T s)) (ϕ1 (T s) * T1 s) s := by
      exact (hϕ (T s) (hTpos s hs)).comp s (hT s hs)
    have h2 : HasDerivAt (fun s : ℝ => a * s + s ^ 3 / 3) (a + s ^ 2) s := by
      have := ((hasDerivAt_id' s).const_mul a).add (((hasDerivAt_pow 3 s).div_const 3))
      convert this using 1
      norm_num
    have h3 : HasDerivAt (fun s => ϕ (T s)) (a + s ^ 2) s := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx using hϕT x hx
    exact h1.unique h3
  have hϕ1ne : ∀ s ∈ Ioo sl s1', ϕ1 (T s) ≠ 0 := by
    intro s hs h0
    have := hphase s hs
    rw [h0, zero_mul] at this
    exact hne s hs this.symm
  have hrel : ∀ s ∈ Ioo sl s1', B (T s) / ((ϕ1 (T s) : ℝ) : ℂ) = ρ s := by
    intro s hs
    have hTT : ((T1 s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT1 s hs).ne'
    have hpp : ((ϕ1 (T s) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hϕ1ne s hs
    have e1 := hBT s hs
    rw [hρ s hs] at e1
    have e2 : ((a + s ^ 2 : ℝ) : ℂ) = ((ϕ1 (T s) : ℝ) : ℂ) * ((T1 s : ℝ) : ℂ) := by
      rw [← hphase s hs]; push_cast; ring
    rw [e2] at e1
    field_simp
    field_simp at e1
    linear_combination e1
  refine ⟨hrel s1 hs1, ?_⟩
  -- derivative of `B/ϕ1` along `T`
  have hτ1 : 0 < T s1 := hTpos s1 hs1
  have hϕne : ((ϕ1 (T s1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hϕ1ne s1 hs1
  have hq : HasDerivAt (fun τ => B τ / ((ϕ1 τ : ℝ) : ℂ)) (ibpH B B1 ϕ1 ϕ2 (T s1)) (T s1) := by
    have := (hB (T s1) hτ1).div (hϕ1 (T s1) hτ1).ofReal_comp hϕne
    unfold ibpH
    exact this
  have hcomp : HasDerivAt ((fun τ => B τ / ((ϕ1 τ : ℝ) : ℂ)) ∘ T) (((T1 s1 : ℝ) : ℂ) * ibpH B B1 ϕ1 ϕ2 (T s1)) s1 := by
    have := hq.scomp s1 (hT s1 hs1)
    simpa [Complex.real_smul] using this
  have hρ2 : HasDerivAt ρ (((T1 s1 : ℝ) : ℂ) * ibpH B B1 ϕ1 ϕ2 (T s1)) s1 := by
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hIoo] with x hx using (hrel x hx).symm
  have hu := hρd.unique hρ2
  have hTT : ((T1 s1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hT1 s1 hs1).ne'
  have e2 : ((a + s1 ^ 2 : ℝ) : ℂ) = ((ϕ1 (T s1) : ℝ) : ℂ) * ((T1 s1 : ℝ) : ℂ) := by
    rw [← hphase s1 hs1]; push_cast; ring
  rw [hu, e2]
  field_simp

/-- The `s`-ratio `ρ(s) = N_c s^{1/2} g_s(s)/(a + s²)`. -/
noncomputable def rhoS (Nc : ℂ) (gs : ℂ → ℂ) (a : ℝ) (s : ℝ) : ℂ := Nc * csr (s : ℂ) * gs (s : ℂ) / ((a + s ^ 2 : ℝ) : ℂ)

/-- Derivative of `rhoS` at `s₁ > 0`. -/
noncomputable def rhoS' (Nc : ℂ) (gs : ℂ → ℂ) (g' : ℂ) (a s1 : ℝ) : ℂ :=
  ((Nc * (csr (s1 : ℂ) / (2 * (s1 : ℂ))) * gs (s1 : ℂ) + Nc * csr (s1 : ℂ) * g') * ((a + s1 ^ 2 : ℝ) : ℂ) -
    Nc * csr (s1 : ℂ) * gs (s1 : ℂ) * ((2 * s1 : ℝ) : ℂ)) / ((a + s1 ^ 2 : ℝ) : ℂ) ^ 2

lemma hasDerivAt_rhoS {Nc : ℂ} {gs : ℂ → ℂ} {g' : ℂ} {a s1 : ℝ} (hs1 : 0 < s1) (hne : a + s1 ^ 2 ≠ 0)
    (hg : HasDerivAt gs g' (s1 : ℂ)) : HasDerivAt (rhoS Nc gs a) (rhoS' Nc gs g' a s1) s1 := by
  have hsl : (s1 : ℂ) ∈ slitPlane := mem_slit_of_re_nonneg (by simpa using hs1.le) (by exact_mod_cast hs1.ne')
  have h1 : HasDerivAt (fun s : ℝ => csr (s : ℂ)) (csr (s1 : ℂ) / (2 * (s1 : ℂ))) s1 :=
    (hasDerivAt_csr hsl).comp_ofReal
  have h2 : HasDerivAt (fun s : ℝ => gs (s : ℂ)) g' s1 := hg.comp_ofReal
  have h3 : HasDerivAt (fun s : ℝ => ((a + s ^ 2 : ℝ) : ℂ)) ((2 * s1 : ℝ) : ℂ) s1 := by
    have : HasDerivAt (fun s : ℝ => a + s ^ 2) (2 * s1) s1 := by
      have := (hasDerivAt_pow 2 s1).const_add a
      convert this using 1; norm_num
    exact this.ofReal_comp
  have hne' : ((a + s1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have := (((h1.const_mul Nc).mul h2).div h3 hne')
  unfold rhoS rhoS'
  convert this using 1

/-- Segment side: the `w`-boundary quantities at `R` equal the `s`-quantities. -/
theorem head_bdry {c lam R s1 a U : ℝ} {Nc N1 g' : ℂ} {gs : ℂ → ℂ} {gW gW1 : ℂ → ℂ}
    (hc : 0 < c) (hlam : 0 < lam) (hlc : c * lam ^ 3 = 1) (hR : 0 < R) (hsR : s1 = lam * R)
    (hU : a = kap * U * lam ^ 2) (hNc : Nc * ((lam * Real.sqrt lam : ℝ) : ℂ) = N1)
    (hne : a + s1 ^ 2 ≠ 0) (hgW : gW (R : ℂ) = gs (s1 : ℂ)) (hgW1 : gW1 (R : ℂ) = (lam : ℂ) * g') :
    N1 * (csrF gW (R : ℂ) / (Complex.I * GG U (R : ℂ))) = (1 / (Complex.I * c)) * rhoS Nc gs a s1 ∧
    N1 * ((1 / Complex.I) * (segH (csrF gW) (csrF1 gW gW1) (GG U) GG1 (R : ℂ) /
        (Complex.I * GG U (R : ℂ)))) = (1 / (Complex.I * c)) ^ 2 * (rhoS' Nc gs g' a s1 / ((a + s1 ^ 2 : ℝ) : ℂ)) := by
  have hlcC : (c : ℂ) * (lam : ℂ) ^ 3 = 1 := by exact_mod_cast hlc
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hsqrt : ((Real.sqrt lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hlam).ne'
  have hsq2 : ((Real.sqrt lam : ℝ) : ℂ) ^ 2 = (lam : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hlam.le]
  -- csr at `s₁ = lam R`
  have hq : csr (s1 : ℂ) = ((Real.sqrt lam : ℝ) : ℂ) * csr (R : ℂ) := by
    rw [hsR, csr_mul_ofReal hlam.le hR.le]
  have hGdef : GG U (R : ℂ) = (kap : ℂ) * U + (R : ℂ) ^ 2 := rfl
  have hGa : ((a + s1 ^ 2 : ℝ) : ℂ) = (lam : ℂ) ^ 2 * GG U (R : ℂ) := by
    rw [hGdef, hU, hsR]; push_cast; ring
  have hGne : GG U (R : ℂ) ≠ 0 := by
    intro h0
    apply hne
    have : ((a + s1 ^ 2 : ℝ) : ℂ) = 0 := by rw [hGa, h0, mul_zero]
    exact_mod_cast this
  have hN1 : N1 = Nc * (lam : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) := by rw [← hNc]; push_cast; ring
  have hs1C : (s1 : ℂ) = (lam : ℂ) * (R : ℂ) := by rw [hsR]; push_cast; ring
  refine ⟨?_, ?_⟩
  · unfold csrF rhoS
    rw [hgW, hGa, hq, hN1]
    have hcinv : (c : ℂ) = 1 / (lam : ℂ) ^ 3 := by field_simp; linear_combination hlcC
    rw [hcinv]
    field_simp
  · unfold csrF1 rhoS' segH csrF GG1
    beta_reduce
    rw [hgW, hgW1, hGa, hq, hN1, hs1C]
    have hcinv : (c : ℂ) = 1 / (lam : ℂ) ^ 3 := by field_simp; linear_combination hlcC
    rw [hcinv]
    have h2s : ((2 * s1 : ℝ) : ℂ) = 2 * ((lam : ℂ) * (R : ℂ)) := by rw [hsR]; push_cast; ring
    rw [h2s]
    field_simp

/-- info: 'FormalResearch.SignUncertainty.CtSd.tail_bdry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_bdry

/-- info: 'FormalResearch.SignUncertainty.CtSd.head_bdry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_bdry

end FormalResearch.SignUncertainty.CtSd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# QI-A continuity of finite-dimensional symmetric-power coordinates

The algebraic `SymmetricPower` quotient in Mathlib has no canonical norm or topology.
Nevertheless, after composing its canonical pure-tensor multilinear map with any linear
coordinate map into a normed target, the resulting map is continuous whenever the one-copy
space is finite-dimensional.  No topology on `SymmetricPower` itself is needed.

The key input is elementary: every algebraic multilinear map on finitely many copies of a
finite-dimensional normed complex vector space has a unique continuous multilinear lift.
We prove this by currying one variable at a time.  At the induction step, the continuous lifts
of the lower-arity slices assemble to a linear map out of the finite-dimensional first factor,
and such a linear map is automatically continuous.
-/

namespace FormalResearch.QIA

open scoped TensorProduct

noncomputable section

/-- An algebraic multilinear map on finitely many copies of a finite-dimensional complex
normed space admits a continuous multilinear lift with the same underlying algebraic map. -/
theorem exists_continuousMultilinearMap_of_finiteDimensional
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => E) F) :
    ∃ g : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F,
      g.toMultilinearMap = f := by
  induction n with
  | zero =>
      let g : ContinuousMultilinearMap ℂ (fun _ : Fin 0 => E) F :=
        ContinuousMultilinearMap.uncurry0 ℂ E (f 0)
      refine ⟨g, ?_⟩
      apply MultilinearMap.ext
      intro v
      change f 0 = f v
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      let chooseContinuous :
          MultilinearMap ℂ (fun _ : Fin n => E) F →
            ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F :=
        fun h => Classical.choose (ih h)
      have hchoose (h : MultilinearMap ℂ (fun _ : Fin n => E) F) :
          (chooseContinuous h).toMultilinearMap = h :=
        Classical.choose_spec (ih h)
      let L : E →ₗ[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F :=
        { toFun := fun x => chooseContinuous (f.curryLeft x)
          map_add' := by
            intro x y
            apply ContinuousMultilinearMap.toMultilinearMap_injective
            change
              (chooseContinuous (f.curryLeft (x + y))).toMultilinearMap =
                (chooseContinuous (f.curryLeft x)).toMultilinearMap +
                  (chooseContinuous (f.curryLeft y)).toMultilinearMap
            rw [hchoose, hchoose, hchoose]
            exact (f.curryLeft).map_add x y
          map_smul' := by
            intro c x
            apply ContinuousMultilinearMap.toMultilinearMap_injective
            change
              (chooseContinuous (f.curryLeft (c • x))).toMultilinearMap =
                c • (chooseContinuous (f.curryLeft x)).toMultilinearMap
            rw [hchoose, hchoose]
            exact (f.curryLeft).map_smul c x }
      let Lc : E →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F :=
        L.toContinuousLinearMap
      let g : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E) F :=
        Lc.uncurryLeft
      refine ⟨g, ?_⟩
      apply MultilinearMap.ext
      intro v
      change chooseContinuous (f.curryLeft (v 0)) (Fin.tail v) = f v
      calc
        chooseContinuous (f.curryLeft (v 0)) (Fin.tail v) =
            f.curryLeft (v 0) (Fin.tail v) := by
              exact congrArg
                (fun h : MultilinearMap ℂ (fun _ : Fin n => E) F => h (Fin.tail v))
                (hchoose (f.curryLeft (v 0)))
        _ = f (Fin.cons (v 0) (Fin.tail v)) := rfl
        _ = f v := by rw [Fin.cons_self_tail]

/-- Every algebraic multilinear map on finitely many copies of a finite-dimensional complex
normed space is continuous as a function on the product. -/
theorem multilinearMap_continuous_of_finiteDimensional
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => E) F) :
    Continuous f := by
  obtain ⟨g, hg⟩ :=
    exists_continuousMultilinearMap_of_finiteDimensional (f := f)
  rw [← hg]
  exact g.cont

/-- After any linear realization of algebraic symmetric power in a normed complex space,
the pure symmetric-tensor coordinate map is continuous when the one-copy space is
finite-dimensional.  This discharges the `hreal`-style continuity premise without assigning
any topology to `SymmetricPower` itself. -/
theorem symmetricPower_tprod_linearEquiv_continuous
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {n : ℕ}
    (ι : SymmetricPower ℂ (Fin n) E ≃ₗ[ℂ] H) :
    Continuous fun v : Fin n → E =>
      ι (SymmetricPower.tprod ℂ v) := by
  let f : MultilinearMap ℂ (fun _ : Fin n => E) H :=
    ι.toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ)
  simpa [f] using
    (multilinearMap_continuous_of_finiteDimensional (f := f))

end

end FormalResearch.QIA

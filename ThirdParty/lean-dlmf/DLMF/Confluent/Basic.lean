/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Confluent.Basic.TricomiLogarithmic

public import DLMF.Confluent.Basic.KummerM
public import DLMF.Confluent.Basic.Tricomi
public import DLMF.Confluent.Basic.IncompleteGamma
public import DLMF.Confluent.Basic.ExponentialIntegrals
public import DLMF.Confluent.Basic.ExponentialIntegralSeries
public import DLMF.Confluent.Basic.ErrorFunctions
public import DLMF.Confluent.Basic.ExpansionData
public import DLMF.Confluent.Basic.Buchholz
public import DLMF.Confluent.Basic.KummerProperties
public import DLMF.Confluent.Basic.KummerContiguous
public import DLMF.Confluent.Basic.Whittaker
public import DLMF.Confluent.Basic.WhittakerLogarithmic

/-!
# Confluent hypergeometric functions: foundational definitions

Canonical definitions and normalizations for the confluent area: Kummer's `M`, Tricomi's `U`,
the incomplete gamma functions, exponential integrals, error, Fresnel and Dawson functions,
expansion coefficients, and the coefficients of the Whittaker–Buchholz expansion; Whittaker's
functions; and the basic properties of Kummer's function (series, Kummer's equation, Kummer's
transformation, derivative, contiguous relations), the series of the real exponential, sine and
cosine integrals, and Whittaker's equation.
-/

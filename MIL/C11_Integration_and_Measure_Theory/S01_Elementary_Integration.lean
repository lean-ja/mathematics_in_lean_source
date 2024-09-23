import MIL.Common
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter

open Topology Filter

noncomputable section

/- OMIT:
Elementary Integration
----------------------

OMIT. -/
/- TEXT:
.. index:: integration

.. _elementary_integration:

初等的な積分
----------------------

TEXT. -/
/- OMIT:
We first focus on integration of functions on finite intervals in ``ℝ``. We can integrate
elementary functions.
OMIT. -/
/- TEXT:
ここではまず， ``ℝ`` の有限区間上の関数の積分に焦点を当てます．Mathlibでは初等関数を積分できます．
EXAMPLES: -/
-- QUOTE:
open MeasureTheory intervalIntegral

open Interval
-- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
-- QUOTE.

/- OMIT:
The fundamental theorem of calculus relates integration and differentiation.
Below we give simplified statements of the two parts of this theorem. The first part
says that integration provides an inverse to differentiation and the second one
specifies how to compute integrals of derivatives.
(These two parts are very closely related, but their optimal versions,
which are not shown here, are not equivalent.)
OMIT. -/
/- TEXT:
微積分の基本定理は積分と微分に関するものです．以下では，この定理の２つの部分を簡単に説明します．最初の部分は，積分が微分の逆を提供するということを，２番目では微分の積分を計算する方法を与えるものです．（この２つの部分は非常に密接に関連していますが，ここでは示していない最適版では等価になりません．）
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- QUOTE.

/- OMIT:
Convolution is also defined in Mathlib and its basic properties are proved.
OMIT. -/
/- TEXT:
畳み込みもまたMathlibで定義されており，その基本的な性質が証明されています．
EXAMPLES: -/
-- QUOTE:
open Convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl
-- QUOTE.

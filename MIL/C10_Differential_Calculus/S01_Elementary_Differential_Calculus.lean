import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable section

/- OMIT:
Elementary Differential Calculus
--------------------------------

OMIT. -/
/- TEXT:
.. index:: elementary calculus

.. _elementary_differential_calculus:

初等的な微分法
--------------------------------

TEXT. -/
/- OMIT:
Let ``f`` be a function from the reals to the reals. There is a difference
between talking about the derivative of ``f`` at a single point and
talking about the derivative function.
In Mathlib, the first notion is represented as follows.
OMIT. -/
/- TEXT:
``f`` を実数から実数への関数としたとき，ある1点における ``f`` の微分係数について話すのと導関数について話すのとでは違いがあります．Mathlibでは，前者の概念は次のように表現されます．
EXAMPLES: -/
-- QUOTE:
open Real

/-- The sin function has derivative 1 at 0. -/
example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0
-- QUOTE.

/- OMIT:
We can also express that ``f`` is differentiable at a point without
specifying its derivative there
by writing ``DifferentiableAt ℝ``.
We specify ``ℝ`` explicitly because in a slightly more general context,
when talking about functions from ``ℂ`` to ``ℂ``,
we want to be able to distinguish between being differentiable in the real sense
and being differentiable in the sense of the complex derivative.
OMIT. -/
/- TEXT:
また，特定の点での微分を指定せずに ``f`` が微分可能であることも表現でき， ``DifferentiableAt ℝ`` と書きます．ここで， ``ℝ`` を明示的に指定しているのは，もう少し一般的な文脈において ``ℂ`` から ``ℂ`` までの関数について話す時に，実数的な意味で微分可能であることと，複素微分の意味で微分可能であることを区別できるようにしたいからです．
EXAMPLES: -/
-- QUOTE:
example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt
-- QUOTE.

/- OMIT:
It would be inconvenient to have to provide a proof of differentiability
every time we want to refer to a derivative.
So Mathlib provides a function ``deriv f : ℝ → ℝ`` that is defined for any
function ``f : ℝ → ℝ``
but is defined to take the value ``0`` at any point where ``f`` is not differentiable.
OMIT. -/
/- TEXT:
微分について言及するたびに微分可能性の証明をしなければならないのは不便です．そこで，Mathlibは関数 ``deriv f : ℝ → ℝ`` を提供しています．これは任意の関数 ``f : ℝ → ℝ`` に対して定義されますが， ``f`` が微分不可能な点では ``0`` をとるように定義されています．
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h
-- QUOTE.

/- OMIT:
Of course there are many lemmas about ``deriv`` that do require differentiability assumptions.
For instance, you should think about a counterexample to the next lemma without the
differentiability assumptions.
OMIT. -/
/- TEXT:
もちろん ``deriv`` に関する補題で微分可能性の仮定を必要とするものはたくさんあります．例えば，微分可能性の仮定がない場合の次の補題の反例を考えてみるといいでしょう．
EXAMPLES: -/
-- QUOTE:
example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- QUOTE.

/- OMIT:
Interestingly, however, there are statements that can avoid differentiability
assumptions by taking advantage
of the fact that the value of ``deriv`` defaults to zero when the function is
not differentiable.
So making sense of the following statement requires knowing the precise
definition of ``deriv``.
OMIT. -/
/- TEXT:
しかし興味深いことに，関数が微分可能でない場合， ``deriv`` の値がデフォルトで0になるという事実を利用することで，微分可能性の仮定を回避できる文が存在します．そのため，以下の文の意味を理解するには ``deriv`` の正確な定義を知る必要があります．
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero
-- QUOTE.

/- OMIT:
We can even state Rolle's theorem without any differentiability assumptions, which
seems even weirder.
OMIT. -/
/- TEXT:
より奇妙に見えるでしょうが，微分可能性の仮定なしにロルの定理を示すことさえできます．
EXAMPLES: -/
-- QUOTE:
open Set

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI
-- QUOTE.

/- OMIT:
Of course, this trick does not work for the general mean value theorem.
OMIT. -/
/- TEXT:
もちろん，この技法は一般的な平均値の定理には通用しません．
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'
-- QUOTE.

/- OMIT:
Lean can automatically compute some simple derivatives using the ``simp`` tactic.
OMIT. -/
/- TEXT:
Leanは ``simp`` タクティクを使って簡単な微分係数を自動的に計算することができます．
EXAMPLES: -/
-- QUOTE:
example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp
-- QUOTE.

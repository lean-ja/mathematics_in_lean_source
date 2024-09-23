import MIL.Common
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

/- OMIT:
Measure Theory
--------------

OMIT. -/
/- TEXT:
.. index:: measure theory

.. _measure_theory:

測度論
--------------

TEXT. -/
/- OMIT:
The general context for integration in Mathlib is measure theory. Even the elementary
integrals of the previous section are in fact Bochner integrals. Bochner integration is
a generalization of Lebesgue integration where the target space can be any Banach space,
not necessarily finite dimensional.

OMIT. -/
/- TEXT:
Mathlibにおける積分の一般的な文脈は測度論です．前節の初等積分でさえも，実際にはボホナー積分です．ボホナー積分はルベーグ積分の一般化で，対象の空間はバナッハ空間であれば何でもよく，必ずしも有限次元である必要はありません．

TEXT. -/
/- OMIT:
The first component in the development of measure theory
is the notion of a :math:`\sigma`-algebra of sets, which are called the
*measurable* sets.
The type class ``MeasurableSpace`` serves to equip a type with such a structure.
The sets ``empty`` and ``univ`` are measurable,
the complement of a measurable set is measurable,
and a countable union or intersection of measurable sets is measurable.
Note that these axioms are redundant; if you ``#print MeasurableSpace``,
you will see the ones that Mathlib uses.
As the examples below show, countability assumptions can be expressed using the
``Encodable`` type class.
OMIT. -/
/- TEXT:
測度論の発展における最初の要素は **可測** （measurable）集合と呼ばれる集合の :math:`\sigma`-代数の概念です．型クラス ``MeasurableSpace`` はこのような構造を持つ型を備えるためのものです．まず集合 ``empty`` と ``univ`` は可測です．可測集合の補集合も可測であり，可測集合の可算和または可算交差も可測です．これらの公理が冗長であることに注意してください; ``#print MeasurableSpace`` とタイプすると，Mathlibが使っている公理が表示されます．以下の例で示すように，可算性の仮定は ``Encodable`` 型クラスを使って表現することができます．
BOTH: -/
-- QUOTE:
variable {α : Type*} [MeasurableSpace α]

-- EXAMPLES:
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

-- BOTH:
variable {ι : Type*} [Encodable ι]

-- EXAMPLES:
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
-- QUOTE.

/- OMIT:
Once a type is measurable, we can measure it. On paper, a measure on a set
(or type) equipped with a
:math:`\sigma`-algebra is a function from the measurable sets to
the extended non-negative reals that is
additive on countable disjoint unions.
In Mathlib, we don't want to carry around measurability assumptions
every time we write an application of the measure to a set.
So we extend the measure to any set ``s``
as the infimum of measures of measurable sets containing ``s``.
Of course, many lemmas still require
measurability assumptions, but not all.
OMIT. -/
/- TEXT:
ある型が可測であれば，その型を測ることができます．書籍などにおいては， :math:`\sigma`-代数を備えた集合（または型）に対する測度とは，可測集合から拡張非負実数への関数であり，可算非交和上で加法的とされています．Mathlibでは，ある集合への測度の適用を記述するたびに可測の仮定を持ち出したくはありません．そこで， ``s`` を含む可測な集合の測度を最小値として，任意の集合 ``s`` に測度を拡張しています．もちろん，多くの補題では依然として可測の仮定を必要としますが，すべてではありません．
BOTH: -/
-- QUOTE:
open MeasureTheory
variable {μ : Measure α}

-- EXAMPLES:
example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis
-- QUOTE.

/- OMIT:
Once a type has a measure associated with it, we say that a property ``P``
holds *almost everywhere* if the set of elements where the property fails
has measure 0.
The collection of properties that hold almost everywhere form a filter,
but Mathlib introduces special notation for saying that a property holds
almost everywhere.
OMIT. -/
/- TEXT:
ある型に測度が紐づけられると，ある特性 ``P`` が **ほとんどいたるところ** （almost everywhere）で保持されるとは，その特性が失敗する要素の集合が測度0であることを指します．ほとんどいたるところで保持される特性の集合はフィルタを形成しますが，Mathlibはある特性がほとんどいたるところで保持されることを言うための特別な記法を導入しています．
EXAMPLES: -/
-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
  Iff.rfl
-- QUOTE.

import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

open Set Filter Topology

/- OMIT:
Topological spaces
------------------

OMIT. -/
/- TEXT:

.. index:: topological space

.. _topological_spaces:

位相空間
-----------

TEXT. -/
/- OMIT:
Fundamentals
^^^^^^^^^^^^

OMIT. -/
/- TEXT:
基礎
^^^^^

TEXT. -/
/- OMIT:
We now go up in generality and introduce topological spaces. We will review the two main ways to define
topological spaces and then explain how the category of topological spaces is much better behaved than
the category of metric spaces. Note that we won't be using Mathlib category theory here, only having
a somewhat categorical point of view.

OMIT. -/
/- TEXT:
ここでは一般性を高めて、位相空間を紹介しましょう。まず位相空間を定義する主な方法のうち2つを復習し、位相空間の圏が距離空間の圏よりもずっと良い振る舞いをしていることを説明します。ここでは、Mathlibの圏論ライブラリを使うのではなく、圏論的な視点を持つだけにとどまることに注意してください。

TEXT. -/
/- OMIT:
The first way to think about the transition from metric spaces to topological spaces is that we only
remember the notion of open sets (or equivalently the notion of closed sets). From this point of view,
a topological space is a type equipped with a collection of sets that are called open sets. This collection
has to satisfy a number of axioms presented below (this collection is slightly redundant but we will ignore that).
OMIT. -/
/- TEXT:
距離空間から位相空間への移行を考え方の1つ目は、開集合の概念（あるいはそれに準ずる閉集合の概念）だけを覚えておくことです。この観点から、位相空間は開集合と呼ばれる集合の集まりを備えた型です。この集合は、以下に示すいくつかの公理を満たす必要があります（これらは若干冗長ですが、置いておくこととします）。
BOTH: -/
-- QUOTE:
section
variable {X : Type*} [TopologicalSpace X]

example : IsOpen (univ : Set X) :=
  isOpen_univ

example : IsOpen (∅ : Set X) :=
  isOpen_empty

example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter hs
-- QUOTE.

/- OMIT:

Closed sets are then defined as sets whose complement  is open. A function between topological spaces
is (globally) continuous if all preimages of open sets are open.
OMIT. -/
/- TEXT:
また、閉集合はその補集合が開である集合として定義されます。位相空間の間の関数は開集合の逆像がずべて開であれば（大域的に）連続です。
BOTH: -/
-- QUOTE:
variable {Y : Type*} [TopologicalSpace Y]

example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
-- QUOTE.

/- OMIT:
With this definition we already see that, compared to metric spaces, topological spaces only remember
enough information to talk about continuous functions: two topological structures on a type are
the same if and only if they have the same continuous functions (indeed the identity function will
be continuous in both direction if and only if the two structures have the same open sets).

OMIT. -/
/- TEXT:
この定義から、距離空間と比較して位相空間は連続関数について議論するのに十分な情報しか保有していないことがわかるでしょう。つまり、ある型上の2つの位相構造が同じであるのは、それらが同じ連続関数を持つ場合に限ります（実際、恒等関数は2つの構造が同じ開集合を持つ場合に限り両方向に連続です）。

TEXT. -/
/- OMIT:
However as soon as we move on to continuity at a point we see the limitations of the approach based
on open sets. In Mathlib we frequently think of topological spaces as types equipped
with a neighborhood filter ``𝓝 x`` attached to each point ``x`` (the corresponding function
``X → Filter X`` satisfies certain conditions explained further down). Remember from the filters section that
these gadget play two related roles. First ``𝓝 x`` is seen as the generalized set of points of ``X``
that are close to ``x``. And then it is seen as giving a way to say, for any predicate ``P : X → Prop``,
that this predicates holds for points that are close enough to ``x``. Let us state
that ``f : X → Y`` is continuous at ``x``. The purely filtery way is to say that the direct image under
``f`` of the generalized set of points that are close to ``x`` is contained in the generalized set of
points that are close to ``f x``. Recall this spelled either ``map f (𝓝 x) ≤ 𝓝 (f x)``
or ``Tendsto f (𝓝 x) (𝓝 (f x))``.

OMIT. -/
/- TEXT:
しかし、ある点での連続性について考えると、すぐに開集合に基づくアプローチの限界が見えてきます。Mathlibでは、位相空間を、各点 ``x`` に対応する近傍フィルタ ``𝓝 x`` を備えた型として考えることが多いです（対応する関数 ``X → Filter X`` はこの後で説明するある条件を満たします）。フィルタのセクションで、これらの道具が2つの関連した役割を果たしていたことを思い出してください。まず、 ``𝓝 x`` は ``x`` に近い ``X`` の点の一般化された集合だとみなされます。また、任意の述語 ``P : X → Prop`` に対して、この述語が ``x`` に十分近い点に対して成り立つことを示す方法を与えるものともみなされます。これらを用いて ``f : X → Y`` が ``x`` で連続であることを定義しましょう。純粋にフィルタ的な言い方をすれば、 ``x`` に近い点からなる一般化された集合に対する ``f`` の順像が、 ``f x`` に近い点からなる一般化された集合に含まれるということです。これは ``map f (𝓝 x) ≤ 𝓝 (f x)`` 、または ``Tendsto f (𝓝 x) (𝓝 (f x))`` と表記されたことを思い出してください。
BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl
-- QUOTE.

/- OMIT:
One can also spell it using both neighborhoods seen as ordinary sets and a neighborhood filter
seen as a generalized set: "for any neighborhood ``U`` of ``f x``, all points close to ``x``
are sent to ``U``". Note that the proof is again ``iff.rfl``, this point of view is definitionally
equivalent to the previous one.

OMIT. -/
/- TEXT:
また近傍を通常の集合、近傍フィルタを一般化された集合としてみなすことを両方もちいて、次のように記述することもできます。「 ``f x`` の任意の近傍 ``U`` に対して、 ``x`` に近い点はすべて ``U`` に送られる」。この証明も ``iff.rfl`` で与えられ、この観点は前のものと定義上等価であることに注意してください。

BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl
-- QUOTE.

/- OMIT:
We now explain how to go from one point of view to the other. In terms of open sets, we can
simply define members of ``𝓝 x`` as sets that contain an open set containing ``x``.


OMIT. -/
/- TEXT:
ここで上記の2つの観点について、一方の視点から他方の視点に移る方法を説明しましょう。開集合の観点からは、単純に ``x`` を含む開集合を含む集合を ``𝓝 x`` の要素と定義することができます。
BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff
-- QUOTE.

/- OMIT:
To go in the other direction we need to discuss the condition that ``𝓝 : X → Filter X`` must satisfy
in order to be the neighborhood function of a topology.

OMIT. -/
/- TEXT:
上記の反対方向へ行くにあたって、位相の近傍関数であるためには、 ``𝓝 : X → Filter X`` が満たすべき条件について議論する必要があります。

TEXT. -/
/- OMIT:
The first constraint is that ``𝓝 x``, seen as a generalized set, contains the set ``{x}`` seen as the generalized set
``pure x`` (explaining this weird name would be too much of a digression, so we simply accept it for now).
Another way to say it is that if a predicate holds for points close to ``x`` then it holds at ``x``.

OMIT. -/
/- TEXT:
最初の制約は、一般化された集合としてみた ``𝓝 x`` は、集合 ``{x}`` を一般化された集合としてみた ``pure x`` を含むということです（この奇妙な名前を説明すると余談が多くなるため、今はただそういうものなんだと思ってください）。別の言い方をすれば、ある述語 ``x`` に近い点で成り立つなら、それは ``x`` で成り立つということです。
BOTH: -/
-- QUOTE:
example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds
-- QUOTE.

/- OMIT:
Then a more subtle requirement is that, for any predicate ``P : X → Prop`` and any ``x``, if ``P y`` holds for ``y`` close
to ``x`` then for ``y`` close to ``x`` and ``z`` close to ``y``, ``P z`` holds. More precisely we have:
OMIT. -/
/- TEXT:
そして、より微妙な要件は、任意の述語 ``P : X → Prop`` と任意の ``x`` について、 ``x`` に近い ``y`` に対して ``P y`` が成り立つなら、 ``x`` に近い ``y`` と ``y`` に近い ``z`` に対して ``P z`` が成り立つということです。より正確には次のように成ります：
BOTH: -/
-- QUOTE:
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h
-- QUOTE.

/- OMIT:
Those two results characterize the functions ``X → Filter X`` that are neighborhood functions for a topological space
structure on ``X``. There is a still a function ``TopologicalSpace.mkOfNhds : (X → Filter X) → TopologicalSpace X``
but it will give back its input as a neighborhood function only if it satisfies the above two constraints.
More precisely we have a lemma ``TopologicalSpace.nhds_mkOfNhds`` saying that in a different way and our
next exercise deduces this different way from how we stated it above.
OMIT. -/
/- TEXT:
この2つの結果から ``X → Filter X`` の型をもつ関数が ``X`` 上の位相空間構造の近傍関数であることが特徴づけられます。これ以外に ``TopologicalSpace.mkOfNhds : (X → Filter X) → TopologicalSpace X`` という関数も存在しますが、これは上記の2つの制約を満たす場合にのみ入力を近傍関数として返します。より正確にはこのことを別の方法で述べている ``TopologicalSpace.nhds_mkOfNhds`` があり、次の演習ではこの方法を導きます。
BOTH: -/
#check TopologicalSpace.mkOfNhds

#check TopologicalSpace.nhds_mkOfNhds

-- QUOTE:
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
  intro a s s_in
  refine' ⟨{ y | s ∈ n y }, H a (fun x ↦ x ∈ s) s_in, _, by tauto⟩
  rintro y (hy : s ∈ n y)
  exact H₀ y hy

-- BOTH:
end

-- BOTH.
/- OMIT:
Note that ``TopologicalSpace.mkOfNhds`` is not so frequently used, but it still good to know in what
precise sense the neighborhood filters is all there is in a topological space structure.

OMIT. -/
/- TEXT:
``TopologicalSpace.mkOfNhds`` はそれほど頻繁に使われるものではありませんが、位相空間の構造において近傍フィルタの正確な意味での定義を知っておくことは良いことでしょう。

TEXT. -/
/- OMIT:
The next thing to know in order to efficiently use topological spaces in Mathlib is that we use a lot
of formal properties of ``TopologicalSpace : Type u → Type u``. From a purely mathematical point of view,
those formal properties are a very clean way to explain how topological spaces solve issues that metric spaces
have. From this point of view, the issues solved by topological spaces is that metric spaces enjoy very
little functoriality, and have very bad categorical properties in general. This comes on top of the fact
already discussed that metric spaces contain a lot of geometrical information that is not topologically relevant.

OMIT. -/
/- TEXT:
Mathlibで位相空間を効率的に使うために知っておくべきことの2番目は、 ``TopologicalSpace : Type u → Type u`` の形式的性質をたくさん使うということです。純粋数学の観点から見ると、これらの形式的特性は位相空間による距離空間が持つ問題の解決策を説明する非常に綺麗な方法です。この観点からすると、距離空間が関手性ほとんど満たしておらず、一般に圏としての性質が非常に悪いという問題が位相空間によって解決されます。このことは、既に述べたように距離空間には位相には関係ない幾何学的な情報がたくさん含まれている事実の上に成り立っています。

TEXT. -/
/- OMIT:
Let us focus on functoriality first. A metric space structure can be induced on a subset or,
equivalently, it can be pulled back by an injective map. But that's pretty much everything.
They cannot be pulled back by general map or pushed forward, even by surjective maps.

OMIT. -/
/- TEXT:
まず関手性に着目しましょう。距離空間の構造は部分集合に誘導することができ、また同様に単射な写像によって引き戻すこともできます。しかし、これらの条件がほぼ全てになります。一般的な写像によって引き戻されることはなく、またたとえ全射な写像であっても押し出されることもありません。

TEXT. -/
/- OMIT:
In particular there is no sensible distance to put on a quotient of a metric space or on an uncountable
products of metric spaces. Consider for instance the type ``ℝ → ℝ``, seen as
a product of copies of ``ℝ`` indexed by ``ℝ``. We would like to say that pointwise convergence of
sequences of functions is a respectable notion of convergence. But there is no distance on
``ℝ → ℝ`` that gives this notion of convergence. Relatedly, there is no distance ensuring that
a map ``f : X → (ℝ → ℝ)`` is continuous if and only ``fun x ↦ f x t`` is continuous for every ``t : ℝ``.

OMIT. -/
/- TEXT:
特に、距離空間の商や、距離空間の不可算積上の実用的な距離は存在しません。例えば ``ℝ → ℝ`` という型を考えてみましょう。これは ``ℝ`` をインデックスとする ``ℝ`` のコピーの積として見ることができます。関数列の点ごとの収束は、立派に収束の概念であると言いたいところです。しかし、 ``ℝ → ℝ`` 上にはこの収束の概念を与える距離は存在しません。これに関連して、写像 ``f : X → (ℝ → ℝ)`` がすべての ``t : ℝ`` に対して ``fun x ↦ f x t`` が連続である場合だけ連続であることを保証する距離は存在しません。

TEXT. -/
/- OMIT:
We now review the data used to solve all those issues. First we can use any map ``f : X → Y`` to
push or pull topologies from one side to the other. Those two operations form a Galois connection.

OMIT. -/
/- TEXT:
ここでこれらの問題を解決するための情報を見直しましょう。まず、任意の写像 ``f : X → Y`` をつかって位相を一方から他方へ押し出したり引き戻したりすることができます。この2つの操作はガロア接続を形成します。
BOTH: -/
-- QUOTE:
variable {X Y : Type*}

example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced
-- QUOTE.

/- OMIT:
Those operations are compactible with composition of functions.
As usual, pushing forward is covariant and pulling back is contravariant, see ``coinduced_compose`` and ``induced_compose``.
On paper we will use notations :math:`f_*T` for ``TopologicalSpace.coinduced f T`` and
:math:`f^*T` for ``TopologicalSpace.induced f T``.
OMIT. -/
/- TEXT:
これらの操作は関数の合成でコンパクトにできます。例によって押し出しは共編であり、引き戻しは反変です（ ``coinduced_compose`` と ``induced_compose`` を参照）。本書では、 ``TopologicalSpace.coinduced f T`` に対して :math:`f_*T` 、 ``TopologicalSpace.induced f T`` に対して :math:`f^*T` という表記を使用します。
BOTH: -/
#check coinduced_compose

#check induced_compose

/- OMIT:

Then the next big piece is a complete lattice structure on ``TopologicalSpace X``
for any given structure. If you think of topologies are being primarily the data of open sets then you expect
the order relation on ``TopologicalSpace X`` to come from ``Set (Set X)``, ie you expect ``t ≤ t'``
if a set ``u`` is open for ``t'`` as soon as it is open for ``t``. However we already know that Mathlib focuses
on neighborhoods more than open sets so, for any ``x : X`` we want the map from topological spaces to neighborhoods
``fun T : TopologicalSpace X ↦ @nhds X T x`` to be order preserving.
And we know the order relation on ``Filter X`` is designed to ensure an order
preserving ``principal : Set X → Filter X``, allowing to see filters as generalized sets.
So the order relation we do use on  ``TopologicalSpace X`` is opposite to the one coming from ``Set (Set X)``.

OMIT. -/
/- TEXT:
次の大きなピースは、任意の構造に対する ``TopologicalSpace X`` 上の完備束構造です。位相が主に開集合のあつまりであると考えるなら、 ``TopologicalSpace X`` 上の順序関係は ``Set (Set X)`` から導かれると予想されます。つまり、集合 ``u`` が ``t'`` に対して開であれば、 ``t`` に対して開である時に ``t ≤ t'`` になると予想するでしょう。しかし、Mathlibは開集合よりも近傍に重点を置いているので、任意の ``x : X`` に対して、位相空間から近傍への写像 ``fun T : TopologicalSpace X ↦ @nhds X T x`` は順序を保存してほしいです。そして、 ``Filter X`` の順序関係は ``principal : Set X → Filter X`` が順序を保存するように設計されており、またフィルタを一般化した集合と見ることができることは既に見ました。つまり、  ``TopologicalSpace X`` の順序関係は ``Set (Set X)`` の順序関係とは逆向きになります。
BOTH: -/
-- QUOTE:
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl
-- QUOTE.

/- OMIT:

Now we can recover continuity by combining the push-forward (or pull-back) operation with the order relation.

OMIT. -/
/- TEXT:
ここで押し出し（もしくは引き戻し）操作と順序関係を組み合わせることで、連続性を再度示すことができます。
BOTH: -/
-- QUOTE:
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le
-- QUOTE.

/- OMIT:
With this definition and the compatibility of push-forward and composition, we
get for free the universal property that, for any topological space :math:`Z`,
a function :math:`g : Y → Z` is continuous for the topology :math:`f_*T_X` if and only if
:math:`g ∘ f` is continuous.
OMIT. -/
/- TEXT:
この定義と、押し出しと合成の互換性によって、任意の位相空間 :math:`Z` に対して、関数 :math:`g : Y → Z` が :math:`f_*T_X` において連続であるのは :math:`g ∘ f` が連続である場合に限るという普遍的な性質をただで手に入れることができます。

.. math::
  g \text{ continuous } &⇔ g_*(f_*T_X) ≤ T_Z \\
  &⇔ (g ∘ f)_* T_X ≤ T_Z \\
  &⇔ g ∘ f \text{ continuous}

BOTH: -/
-- QUOTE:
example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
      (g : Y → Z) :
    @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
      @Continuous X Z T_X T_Z (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]
-- QUOTE.

/- OMIT:
So we already get quotient topologies (using the projection map as ``f``). This wasn't using that
``TopologicalSpace X`` is a complete lattice for all ``X``. Let's now see how all this structure
proves the existence of the product topology by abstract non-sense.
We considered the case of ``ℝ → ℝ`` above, but let's now consider the general case of ``Π i, X i`` for
some ``ι : Type*`` and ``X : ι → Type*``. We want, for any topological space ``Z`` and any function
``f : Z → Π i, X i``, that ``f`` is continuous if and only if ``(fun x ↦ x i) ∘ f`` is continuous for all ``i``.
Let us explore that constraint "on paper" using notation :math:`p_i` for the projection
``(fun (x : Π i, X i) ↦ x i)``:

OMIT. -/
/- TEXT:
つまり、すでに（射影写像として ``f`` を使うことで）商位相を得ているのです。これは ``TopologicalSpace X`` がすべての ``X`` に対して完備束であるという事実を利用したものではありません。ではこのような構造によって抽象的な無意味から積位相の存在がどのように証明されるか見てみましょう。上では ``ℝ → ℝ`` の場合だけを考えましたが、ここでは ``ι : Type*`` と ``X : ι → Type*`` に対する ``Π i, X i`` の一般的な場合を考えてみましょう。任意の位相空間 ``Z`` と任意の関数 ``f : Z → Π i, X i`` に対して、 ``f`` が連続であるのは、すべての ``ι`` に対して ``(fun x ↦ x i) ∘ f`` が連続である場合に限ってほしいです。ここでは射影 ``(fun (x : Π i, X i) ↦ x i)`` の表記 :math:`p_i` を用いて、その制約を「紙の上で」調べてみましょう：

TEXT. -/
/- OMIT:
.. math::
  (∀ i, p_i ∘ f \text{ continuous}) &⇔ ∀ i, (p_i ∘ f)_* T_Z ≤ T_{X_i} \\
  &⇔ ∀ i, (p_i)_* f_* T_Z ≤ T_{X_i}\\
  &⇔ ∀ i, f_* T_Z ≤ (p_i)^*T_{X_i}\\
  &⇔  f_* T_Z ≤ \inf \left[(p_i)^*T_{X_i}\right]

So we see that what is the topology we want on ``Π i, X i``:
OMIT. -/
/- TEXT:
したがって、 ``Π i, X i`` の位相が求まります。
BOTH: -/
-- QUOTE:
example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
  rfl
-- QUOTE.

/- OMIT:

This ends our tour of how Mathlib thinks that topological spaces fix defects of the theory of metric spaces
by being a more functorial theory and having a complete lattice structure for any fixed type.

OMIT. -/
/- TEXT:
以上でMathlibが位相空間をより関手的な理論であり、任意の固定された型に対して完備束構造を持つことで、距離空間の理論の欠点を埋めようとする思想についてのツアーを終了します。

TEXT. -/
/- OMIT:
Separation and countability
^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
分離公理と可算公理
^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We saw that the category of topological spaces have very nice properties. The price to pay for
this is existence of rather pathological topological spaces.
There are a number of assumptions you can make on a topological space to ensure its behavior
is closer to what metric spaces do. The most important is ``T2Space``, also called "Hausdorff",
that will ensure that limits are unique.
A stronger separation property is ``T3Space`` that ensures in addition the `RegularSpace` property:
each point has a basis of closed neighborhoods.

OMIT. -/
/- TEXT:
位相空間の圏には非常に優れた性質があることを見てきました。その代償として、かなり病的な位相空間が存在します。位相空間には、その振る舞いが距離空間の振る舞いに近くなるようにするための仮定がいくつか存在します。最も重要なものは ``T2Space`` で、これは「ハウスドルフ性」とも呼ばれ、極限が一意であることを保証します。より強力な分離特性は ``T3Space`` で、これは `RegularSpace` の特性に加えて、各店が閉近傍の基底を持つことを保証します。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a
-- QUOTE.

/- OMIT:
Note that, in every topological space, each point has a basis of open neighborhood, by definition.

OMIT. -/
/- TEXT:
どの位相空間においても、定義上、各点は開近傍の基底を持つことに注意してください。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x
-- QUOTE.

/- OMIT:
Our main goal is now to prove the basic theorem which allows extension by continuity.
From Bourbaki's general topology book, I.8.5, Theorem 1 (taking only the non-trivial implication):

OMIT. -/
/- TEXT:
ここでの主な目的は、連続性による拡張を可能にする基本定理を証明することです。ブルバキのgeneral topologyの本、1.8.5、定理1より（自明でない含意のみをとります）：

TEXT. -/
/- OMIT:
Let :math:`X` be a topological space, :math:`A` a dense subset of :math:`X`, :math:`f : A → Y`
a continuous mapping of :math:`A` into a :math:`T_3` space :math:`Y`. If, for each :math:`x` in
:math:`X`, :math:`f(y)` tends to a limit in :math:`Y` when :math:`y` tends to :math:`x`
while remaining in :math:`A` then there exists a continuous extension :math:`φ` of :math:`f` to
:math:`X`.

OMIT. -/
/- TEXT:
:math:`X` を位相空間、 :math:`A` を :math:`X` の稠密部分集合、 :math:`f : A → Y` を :math:`A` から :math:`T_3` 空間 :math:`Y` への連続写像とする。もし、 :math:`X` 内の各 :math:`x` に対して、 :math:`y` が :math:`A` に留まりながら :math:`x` に限りなく近づく時に :math:`f(y)` が :math:`Y` 内の極限に収束するならば、 :math:`f` を :math:`X` に連続に拡張した :math:`φ` が存在する。

TEXT. -/
/- OMIT:
Actually Mathlib contains a more general version of the above lemma, ``DenseInducing.continuousAt_extend``,
but we'll stick to Bourbaki's version here.

OMIT. -/
/- TEXT:
実際には、Mathlibには上記の補題のより一般的なバージョンである ``DenseInducing.continuousAt_extend`` が含まれていますが、ここではブルバキのバージョンにこだわることにします。

TEXT. -/
/- OMIT:
Remember that, given ``A : Set X``, ``↥A`` is the subtype associated to ``A``, and Lean will automatically
insert that funny up arrow when needed. And the (inclusion) coercion map is ``(↑) : A → X``.
The assumption "tends to :math:`x` while remaining in :math:`A`" corresponds to the pull-back filter
``comap (↑) (𝓝 x)``.

OMIT. -/
/- TEXT:
``A : Set X`` が与えられると、 ``↥A`` は ``A`` に関連する部分型であり、Leanは必要な時は自動的にこのちょっと変な上向き矢印を挿入することを覚えておいてください。そして、この（包含な）型強制の対応は ``(↑) : A → X`` です。「 :math:`A` に留まりながら :math:`x` に限りなく近づく」という仮定は引き戻しのフィルタ ``comap (↑) (𝓝 x)`` に対応します。

TEXT. -/
/- OMIT:
Let's prove first an auxiliary lemma, extracted to simplify the context
(in particular we don't need Y to be a topological space here).

OMIT. -/
/- TEXT:
まず文脈を簡単にするために抽出した補助的な補題を証明しましょう。（特にここではYが位相空間である必要はありません）。
BOTH: -/
-- QUOTE:
theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
/- EXAMPLES:
  sorry

SOLUTIONS: -/
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
-- QUOTE.

/- OMIT:
Let's now turn to the main proof of the extension by continuity theorem.

OMIT. -/
/- TEXT:
それでは、連続性定理による拡張のメインの証明に移りましょう。

TEXT. -/
/- OMIT:
When Lean needs a topology on ``↥A`` it will automatically use the induced topology.
The only relevant lemma is
``nhds_induced (↑) : ∀ a : ↥A, 𝓝 a = comap (↑) (𝓝 ↑a)``
(this is actually a general lemma about induced topologies).

OMIT. -/
/- TEXT:
Leanが ``↥A`` 上の位相を必要とする場合、自動的に誘導位相を使用します。関連する唯一の補題は、 ``nhds_induced (↑) : ∀ a : ↥A, 𝓝 a = comap (↑) (𝓝 ↑a)`` です（これは実際には誘導位相に関する一般的な補題です）。

TEXT. -/
/- OMIT:
The proof outline is:

OMIT. -/
/- TEXT:
証明の概要は以下のようになります：

TEXT. -/
/- OMIT:
The main assumption and the axiom of choice give a function ``φ`` such that
``∀ x, Tendsto f (comap (↑) (𝓝 x)) (𝓝 (φ x))``
(because ``Y`` is Hausdorff, ``φ`` is entirely determined, but we won't need that until we try to
prove that ``φ`` indeed extends ``f``).

OMIT. -/
/- TEXT:
メインの仮定と選択公理から、 ``∀ x, Tendsto f (comap (↑) (𝓝 x)) (𝓝 (φ x))`` となる関数 ``φ`` が与えられます。（ ``Y`` はハウスドルフであるため、 ``φ`` は完全に決定されますが、 ``φ`` が実際に ``f`` を拡張することを証明するまではこの性質は必要ありません）。

TEXT. -/
/- OMIT:
Let's first prove ``φ`` is continuous. Fix any ``x : X``.
Since ``Y`` is regular, it suffices to check that for every *closed* neighborhood
``V'`` of ``φ x``, ``φ ⁻¹' V' ∈ 𝓝 x``.
The limit assumption gives (through the auxiliary lemma above)
some ``V ∈ 𝓝 x`` such ``IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V'``.
Since ``V ∈ 𝓝 x``, it suffices to prove ``V ⊆ φ ⁻¹' V'``, ie  ``∀ y ∈ V, φ y ∈ V'``.
Let's fix ``y`` in ``V``. Because ``V`` is *open*, it is a neighborhood of ``y``.
In particular ``(↑) ⁻¹' V ∈ comap (↑) (𝓝 y)`` and a fortiori ``f ⁻¹' V' ∈ comap (↑) (𝓝 y)``.
In addition ``comap (↑) (𝓝 y) ≠ ⊥`` because ``A`` is dense.
Because we know ``Tendsto f (comap (↑) (𝓝 y)) (𝓝 (φ y))`` this implies
``φ y ∈ closure V'`` and, since ``V'`` is closed, we have proved ``φ y ∈ V'``.

OMIT. -/
/- TEXT:
まず ``φ`` が連続であることを証明しましょう。任意の ``x : X`` を固定します。 ``Y`` は正則であるので、 ``φ x`` の *閉* 近傍 ``V'`` に対して、 ``φ ⁻¹' V' ∈ 𝓝 x`` が成り立つことを確認すれば十分です。極限の仮定は（上の補助的な補題によって） ``IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V'`` を満たす ``V ∈ 𝓝 x`` を与えます。 ``V ∈ 𝓝 x`` であるため、 ``V ⊆ φ ⁻¹' V'`` 、すなわち  ``∀ y ∈ V, φ y ∈ V'`` を証明すれば十分です。ここで ``V`` の要素 ``y`` を固定しましょう。 ``V`` は *開* であるため、 ``y`` の近傍です。特に ``(↑) ⁻¹' V ∈ comap (↑) (𝓝 y)`` となり、また ``f ⁻¹' V' ∈ comap (↑) (𝓝 y)`` となります。さらに ``A`` は稠密であるため、 ``comap (↑) (𝓝 y) ≠ ⊥`` です。そして ``Tendsto f (comap (↑) (𝓝 y)) (𝓝 (φ y))`` は既知であるため、 ``φ y ∈ closure V'`` が導かれ、 ``V'`` が閉じていることから ``φ y ∈ V'`` が証明されたことになります。

TEXT. -/
/- OMIT:
It remains to prove that ``φ`` extends ``f``. This is were continuity of ``f`` enters the discussion,
together with the fact that ``Y`` is Hausdorff.
OMIT. -/
/- TEXT:
あとは ``φ`` が ``f`` から拡張されていることを証明するだけです。これは ``Y`` がハウスドルフであるという事実とともに、 ``f`` の連続性が議論に出てきます。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
/- EXAMPLES:
  sorry

#check HasBasis.tendsto_right_iff

SOLUTIONS: -/
  choose φ hφ using hf
  use φ
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 x by
      simpa [ContinuousAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
    intro V' V'_in V'_closed
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V' := aux (hφ x) V'_in
    suffices : ∀ y ∈ V, φ y ∈ V'
    exact mem_of_superset V_in this
    intro y y_in
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in
    haveI : (comap ((↑) : A → X) (𝓝 y)).NeBot := by simpa [mem_closure_iff_comap_neBot] using hA y
    apply V'_closed.mem_of_tendsto (hφ y)
    exact mem_of_superset (preimage_mem_comap hVx) hV
  · intro a
    have lim : Tendsto f (𝓝 a) (𝓝 (φ a)) := by simpa [nhds_induced] using hφ a
    exact tendsto_nhds_unique lim f_cont.continuousAt
-- QUOTE.

/- OMIT:
In addition to separation property, the main kind of assumption you can make on a topological
space to bring it closer to metric spaces is countability assumption. The main one is first countability
asking that every point has a countable neighborhood basic. In particular this ensures that closure
of sets can be understood using sequences.

OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [TopologicalSpace.FirstCountableTopology X]
      {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
  mem_closure_iff_seq_limit
-- QUOTE.

/- OMIT:
Compactness
^^^^^^^^^^^

OMIT. -/
/- TEXT:

TEXT. -/
/- OMIT:
Let us now discuss how compactness is defined for topological spaces. As usual there are several ways
to think about it and Mathlib goes for the filter version.

OMIT. -/
/- TEXT:

TEXT. -/
/- OMIT:
We first need to define cluster points of filters. Given a filter ``F`` on a topological space ``X``,
a point ``x : X`` is a cluster point of ``F`` if ``F``, seen as a generalized set, has non-empty intersection
with the generalized set of points that are close to ``x``.

OMIT. -/
/- TEXT:

TEXT. -/
/- OMIT:
Then we can say that a set ``s`` is compact if every nonempty generalized set ``F`` contained in ``s``,
ie such that ``F ≤ 𝓟 s``, has a cluster point in ``s``.

OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl
-- QUOTE.

/- OMIT:
For instance if ``F`` is ``map u atTop``, the image under ``u : ℕ → X`` of ``atTop``, the generalized set
of very large natural numbers, then the assumption ``F ≤ 𝓟 s`` means that ``u n`` belongs to ``s`` for ``n``
large enough. Saying that ``x`` is a cluster point of ``map u atTop`` says the image of very large numbers
intersects the set of points that are close to ``x``. In case ``𝓝 x`` has a countable basis, we can
interpret this as saying that ``u`` has a subsequence converging to ``x``, and we get back what compactness
looks like in metric spaces.
OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
example [TopologicalSpace.FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu
-- QUOTE.

/- OMIT:
Cluster points behave nicely with continuous functions.

OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf
-- QUOTE.

/- OMIT:
As an exercise, we will prove that the image of a compact set under a continuous map is
compact. In addition to what we saw already, you should use ``Filter.push_pull`` and
``NeBot.of_map``.
OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
-- EXAMPLES:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by sorry
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by sorry
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  sorry
-- QUOTE.

-- SOLUTIONS:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by rw [Filter.push_pull, map_principal]
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by
    apply NeBot.of_map
    rwa [map_eq, inf_of_le_right F_le]
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  rcases hs Hle with ⟨x, x_in, hx⟩
  refine' ⟨f x, mem_image_of_mem f x_in, _⟩
  apply hx.map hf.continuousAt
  rw [Tendsto, map_eq]
  exact inf_le_right

/- OMIT:
One can also express compactness in terms of open covers: ``s`` is compact if every family of open sets that
cover ``s`` has a finite covering sub-family.

OMIT. -/
/- TEXT:

BOTH: -/
-- QUOTE:
example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU
-- QUOTE.

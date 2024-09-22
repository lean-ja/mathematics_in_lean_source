import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

open Set Filter
open Topology Filter

/- OMIT:
Metric spaces
--------------

OMIT. -/
/- TEXT:
.. index:: metric space

.. _metric_spaces:

距離空間
---------

TEXT. -/
/- OMIT:
Examples in the previous section focus on sequences of real numbers. In this section we will go up a bit in generality and focus on
metric spaces. A metric space is a type ``X`` equipped with a distance function ``dist : X → X → ℝ`` which is a generalization of
the function ``fun x y ↦ |x - y|`` from the case where ``X = ℝ``.

OMIT. -/
/- TEXT:
前節の例題は実数の数列に焦点をあてました．このセクションでは一般性を少し上げて距離空間(metric space)に焦点をあてます．距離空間とは距離関数 ``dist : X → X → ℝ`` を持つ ``X`` 型のことで， ``fun x y ↦ |x - y|`` を ``X = ℝ`` の場合から一般化したものです．

TEXT. -/
/- OMIT:
Introducing such a space is easy and we will check all properties required from the distance function.
OMIT. -/
/- TEXT:
このような空間の導入は簡単で，距離関数から必要な特性をすべて確認できます．
BOTH: -/
-- QUOTE:
variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)
-- QUOTE.

/- OMIT:
Note we also have variants where the distance can be infinite or where ``dist a b`` can be zero without having ``a = b`` or both.
They are called ``EMetricSpace``, ``PseudoMetricSpace`` and ``PseudoEMetricSpace`` respectively (here "e" stands for "extended").

OMIT. -/
/- TEXT:
また，距離が無限大になるものや， ``a = b`` でなくとも ``dist a b`` が0になるもの，あるいはその両方が存在するものもあります．これらはそれぞれ ``EMetricSpace`` ， ``PseudoMetricSpace`` ， ``PseudoEMetricSpace`` と呼ばれます（ここで"e"は"extends"を表します）．
BOTH: -/
-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

/- OMIT:
Note that our journey from ``ℝ`` to metric spaces jumped over the special case of normed spaces that also require linear algebra and
will be explained as part of the calculus chapter.

OMIT. -/
/- TEXT:
``ℝ`` から距離空間への旅は線形代数を必要とするノルム空間の特殊なケースを飛び越えたことに注意してください．ノルム空間については微積分の章で説明します．

TEXT. -/
/- OMIT:
Convergence and continuity
^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
収束と連続性
^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Using distance functions, we can already define convergent sequences and continuous functions between metric spaces.
They are actually defined in a more general setting covered in the next section,
but we have lemmas recasting the definition is terms of distances.
OMIT. -/
/- TEXT:
距離関数を使えば，収束列と距離空間のあいだの連続関数を定義できます．これらの関数は実際には次節で説明する，より一般的な設定で定義されています．しかし，この定義を距離の用語に置き換えた補題があります．
BOTH: -/
-- QUOTE:
example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff
-- QUOTE.

/- OMIT:
A *lot* of lemmas have some continuity assumptions, so we end up proving a lot of continuity results and there
is a ``continuity`` tactic devoted to this task. Let's prove a continuity statement that will be needed
in an exercise below. Notice that Lean knows how to treat a product of two metric spaces as a metric space, so
it makes sense to consider continuous functions from ``X × X`` to ``ℝ``.
In particular the (uncurried version of the) distance function is such a function.

OMIT. -/
/- TEXT:
.. index:: continuity, tactics ; continuity

*多く* の補題が連続性を仮定しているため，たくさんの連続性の結果を証明するはめになります．このタスクのために ``continuity`` タクティクが用意されています．以下の演習問題で必要と成る連続性を証明してみましょう．Leanは2つの距離空間の積を距離空間として扱う方法を知っているため， ``X × X`` から ``ℝ`` への連続関数を考えることは理にかなっています．特に（非カリー化された）距離関数がそのような関数です．

BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity
-- QUOTE.

/- OMIT:
This tactic is a bit slow, so it is also useful to know
how to do it by hand. We first need to use that ``fun p : X × X ↦ f p.1`` is continuous because it
is the composition of ``f``, which is continuous by assumption ``hf``, and the projection ``prod.fst`` whose continuity
is the content of the lemma ``continuous_fst``. The composition property is ``Continuous.comp`` which is
in the ``Continuous`` namespace so we can use dot notation to compress
``Continuous.comp hf continuous_fst`` into ``hf.comp continuous_fst`` which is actually more readable
since it really reads as composing our assumption and our lemma.
We can do the same for the second component to get continuity of ``fun p : X × X ↦ f p.2``. We then assemble
those two continuities using ``Continuous.prod_mk`` to get
``(hf.comp continuous_fst).prod_mk (hf.comp continuous_snd) : Continuous (fun p : X × X ↦ (f p.1, f p.2))``
and compose once more to get our full proof.
OMIT. -/
/- TEXT:
このタクティクは少し挙動が遅いため，これと同等の内容を手作業で行う方法を知っておくと良いでしょう．まず ``fun p : X × X ↦ f p.1`` が連続であるという事実を使う必要があります．この事実は仮定 ``hf`` によって連続である ``f`` と補題 ``continuous_fst`` の内容から連続性を持つ ``prod.fst`` との合成から成り立ちます．この合成の性質は ``Continuous.comp`` によるものです．これは ``Continuous`` 名前空間にあるため， ``Continuous.comp hf continuous_fst`` という書き方はドットによる表記法で ``hf.comp continuous_fst`` に短縮することができます．こうすることでまさに仮定と補題を合成しているというように読めるため，より可読性が上がります．2つ目の構成要素についても同じようにして ``fun p : X × X ↦ f p.2`` の連続性が得られます．次にこの2つの連続性を ``Continuous.prod_mk`` を使って ``(hf.comp continuous_fst).prod_mk (hf.comp continuous_snd) : Continuous (fun p : X × X ↦ (f p.1, f p.2))`` となり，またもう一回合成することで完全な証明になります．
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))
-- QUOTE.

/- OMIT:
The combination of ``Continuous.prod_mk`` and ``continuous_dist`` via ``Continuous.comp`` feels clunky,
even when heavily using dot notation as above. A more serious issue is that this nice proof requires a lot of
planning. Lean accepts the above proof term because it is a full term proving a statement which is
definitionally equivalent to our goal, the crucial definition to unfold being that of a composition of functions.
Indeed our target function ``fun p : X × X ↦ dist (f p.1) (f p.2)`` is not presented as a composition.
The proof term we provided proves continuity of ``dist ∘ (fun p : X × X ↦ (f p.1, f p.2))`` which happens
to be definitionally equal to our target function. But if we try to build this proof gradually using
tactics starting with ``apply continuous_dist.comp`` then Lean's elaborator will fail to recognize a
composition and refuse to apply this lemma. It is especially bad at this when products of types are involved.

OMIT. -/
/- TEXT:
``Continuous.prod_mk`` と ``Continuous.comp`` を介した ``continuous_dist`` の組み合わせは，仮に上記のようなドット表記を多用したとしても不格好になってしまいます．しかしより重要な問題はこの綺麗な証明を構築するには事前に多くの計画をする必要があるということです．Leanが上記の証明項を受け入れるのは，それがゴールと定義的に等価な文を証明する完全な項だからです．実際，ゴールの関数 ``fun p : X × X ↦ dist (f p.1) (f p.2)`` は合成として提示されていません．上記の証明項は ``dist ∘ (fun p : X × X ↦ (f p.1, f p.2))`` の連続性を目標の関数とたまたま定義的に等しいことから証明しています．しかし，この証明を ``apply continuous_dist.comp`` から始まるタクティクスタイルで逐次的に構築しようとすると，Leanのエラボレータは合成を認識できず，この補題の適用を拒否します．特に型の積が関係する場合を苦手としています．

TEXT. -/
/- OMIT:
A better lemma to apply here is
``Continuous.dist {f g : X → Y} : Continuous f → Continuous g → Continuous (fun x ↦ dist (f x) (g x))``
which is nicer to Lean's elaborator and also provides a shorter proof when directly providing a full
proof term, as can be seen from the following two new proofs of the above statement:
OMIT. -/
/- TEXT:
ここではむしろ補題 ``Continuous.dist {f g : X → Y} : Continuous f → Continuous g → Continuous (fun x ↦ dist (f x) (g x))`` を適用するのがよいでしょう．これはLeanのエラボレータにとってより良いものであり，また先程の文に対する以下の2つの新しい証明からわかるように，完全な証明項がより短くなります：
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)
-- QUOTE.

/- OMIT:
Note that, without the elaboration issue coming from composition, another way to compress
our proof would be to use ``Continuous.prod_map`` which is sometimes useful and gives
as an alternate proof term ``continuous_dist.comp (hf.prod_map hf)`` which even shorter to type.

OMIT. -/
/- TEXT:
合成から生じるエラボレータの問題を除けば，証明を圧縮する別の方法は ``Continuous.prod_map`` を使うことです．これは時に便利で，これによってより短い証明項 ``continuous_dist.comp (hf.prod_map hf)`` を与えます．

TEXT. -/
/- OMIT:
Since it is sad to decide between a version which is better for elaboration and a version which is shorter
to type, let us wrap this discussion with a last bit of compression offered
by ``Continuous.fst'`` which allows to compress ``hf.comp continuous_fst`` to ``hf.fst'`` (and the same with ``snd``)
and get our final proof, now bordering obfuscation.

OMIT. -/
/- TEXT:
エラボレータに都合の良いバージョンと型に対して短くなるバージョンの間を決めるのはツライため，この議論は ``Continuous.fst'`` が提供する圧縮の最後のひと手間を加えることで， ``hf.comp continuous_fst`` を ``hf.fst'`` に（ ``snd`` も同様）圧縮することができ，難読化との境界を超えた最終的な証明を得ることができます．
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'
-- QUOTE.

/- OMIT:
It's your turn now to prove some continuity lemma. After trying the continuity tactic, you will need
``Continuous.add``, ``continuous_pow`` and ``continuous_id`` to do it by hand.

OMIT. -/
/- TEXT:
今度は読者が連続性の補題を証明する番です．continuityタクティクを使った後に，手作業で ``Continuous.add`` ，  ``continuous_pow`` ， ``continuous_id`` を使う必要があります．
BOTH: -/
-- QUOTE:
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  hf.comp <| (continuous_pow 2).add continuous_id

/- OMIT:
So far we saw continuity as a global notion, but one can also define continuity at a point.
OMIT. -/
/- TEXT:
ここまではグローバルな概念としての連続性を見てきましたが，ある点での連続性を定義することもできます．
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff
-- QUOTE.

/- OMIT:

Balls, open sets and closed sets
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:

球体，開集合，閉集合
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Once we have a distance function, the most important geometric definitions are (open) balls and closed balls.

OMIT. -/
/- TEXT:
距離関数を得たので，次は最も重要な幾何学的定義である（開）球体と閉球体です．
BOTH: -/
-- QUOTE:
variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl
-- QUOTE.

/- OMIT:
Note that `r` is any real number here, there is no sign restriction. Of course some statements do require a radius condition.
OMIT. -/
/- TEXT:
ここで `r` は任意の実数であり，符号の制限が無いことに注目してください．もちろん，半径の条件が必要な文も存在します．
BOTH: -/
-- QUOTE:
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr
-- QUOTE.

/- OMIT:
Once we have balls, we can define open sets. They are actually defined in a more general setting covered in the next section,
but we have lemmas recasting the definition is terms of balls.

OMIT. -/
/- TEXT:
球体があれば，開集合を定義することができます．実際には，開集合は次の節で説明するより一般的な設定で定義されますが，ここでは球体による定義に変更した補題を使います．
BOTH: -/
-- QUOTE:
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff
-- QUOTE.

/- OMIT:
Then closed sets are sets whose complement is open. Their important property is they are closed under limits. The closure of a set is the smallest closed set containing it.
OMIT. -/
/- TEXT:
また閉集合とは，補集合が開である集合のことです．この集合についての重要な性質は，極限のもとで閉じていることです．ある集合の閉包は，その集合を含む最小の閉集合です．
BOTH: -/
-- QUOTE:
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (eventually_of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff
-- QUOTE.

/- OMIT:
Do the next exercise without using `mem_closure_iff_seq_limit`
OMIT. -/
/- TEXT:
次の演習問題を `mem_closure_iff_seq_limit` を使わずに証明してみましょう．
BOTH: -/
-- QUOTE:
example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  refine' ⟨u N, hs _, _⟩
  rw [dist_comm]
  exact hN N le_rfl

/- OMIT:

Remember from the filters sections that neighborhood filters play a big role in Mathlib.
In the metric space context, the crucial point is that balls provide bases for those filters.
The main lemmas here are ``Metric.nhds_basis_ball`` and ``Metric.nhds_basis_closedBall``
that claim this for open and closed balls with positive radius. The center point is an implicit
argument so we can invoke ``Filter.HasBasis.mem_iff`` as in the following example.

OMIT. -/
/- TEXT:
フィルタについての節で，Mathlibでは近傍のフィルタが大きな役割を果たしていたことを思い出してください．距離空間の文脈での重要なポイントは，球体がこれらのフィルタの基底となることです．ここでの主な補題は ``Metric.nhds_basis_ball`` と ``Metric.nhds_basis_closedBall`` で，正の半径を持つ開球と閉球に対して主張されるものです．中心点は暗黙の引数であるため，次の例のように ``Filter.HasBasis.mem_iff`` を呼び出すことができます．
BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff
-- QUOTE.

/- OMIT:

Compactness
^^^^^^^^^^^

OMIT. -/
/- TEXT:

コンパクト性
^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Compactness is an important topological notion. It distinguishes subsets of a metric space
that enjoy the same kind of properties as segments in reals compared to other intervals:

OMIT. -/
/- TEXT:
コンパクト性は位相幾何学的に重要な概念です．これは他の区間と比べて実数の線分に近い性質を満足する距離空間の部分集合を識別するものです：

TEXT. -/
/- OMIT:
* Any sequence taking value in a compact set has a subsequence that converges in this set
* Any continuous function on a nonempty compact set with values in real numbers is bounded and
  achieves its bounds somewhere (this is called the extreme values theorem).
* Compact sets are closed sets.

OMIT. -/
/- TEXT:
* コンパクトな集合から値を取る数列はこの集合内に収束する部分列を持つ
* 実数値を持つ空でないコンパクトな集合上の連続関数はすべて境界を持ち，どこかでその境界に到達する（これを極値の定理と呼びます）
* コンパクトな集合は閉集合である

TEXT. -/
/- OMIT:
Let us first check that the unit interval in reals is indeed a compact set, and then check the above
claims for compact sets in general metric spaces. In the second statement we only
need continuity on the given set so we will use ``ContinuousOn`` instead of ``Continuous``, and
we will give separate statements for the minimum and the maximum. Of course all these results
are deduced from more general versions, some of which will be discussed in later sections.

OMIT. -/
/- TEXT:
まず，実数の単位区間が実際にコンパクト集合であることを確認し，次に一般的な距離空間のコンパクト集合について上記の主張を確認してみましょう．2つ目の文では，与えられた集合の連続性だけが必要であるため， ``Continuous`` の代わりに ``ContinuousOn`` を使い，最小値と最大値について別々の命題を与えます．もちろん，これらの結果はすべてより一般的なものから導かれます．そのうちのいくつかはこの後の節で議論します．
BOTH: -/
-- QUOTE:
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_forall_le hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_forall_ge hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
-- QUOTE.

/- OMIT:

We can also specify that a metric spaces is globally compact, using an extra ``Prop``-valued type class:

OMIT. -/
/- TEXT:
また， ``Prop``-値の型クラスを追加することで，距離空間が大域的にコンパクトであることを指定することもできます：
BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
-- QUOTE.

/- OMIT:

In a compact metric space any closed set is compact, this is ``IsClosed.isCompact``.

OMIT. -/
/- TEXT:
コンパクトな距離空間において，すべての閉集合はコンパクトです．これが ``IsClosed.isCompact`` です．
BOTH: -/
#check IsCompact.isClosed

/- OMIT:
Uniformly continuous functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:

一様連続関数
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We now turn to uniformity notions on metric spaces : uniformly continuous functions, Cauchy sequences and completeness.
Again those are defined in a more general context but we have lemmas in the metric name space to access their elementary definitions.
We start with uniform continuity.

OMIT. -/
/- TEXT:
ここで距離空間の一様性に立ち入りましょう：例えば一様連続関数，コーシー列，完全性などです．これらもまたより一般的な文脈で定義されますが，それらの初歩的な定義に触れるために距離の名前空間での補題を作りましょう．まず一様連続性から始めましょう．
BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff
-- QUOTE.

/- OMIT:
In order to practice manipulating all those definitions, we will prove that continuous
functions from a compact metric space to a metric space are uniformly continuous
(we will see a more general version in a later section).

OMIT. -/
/- TEXT:
これらの定義をすべて扱う練習として，コンパクトな距離空間から距離空間への連続関数が一様に連続であることを証明します．（後の節でより一般的なバージョンを見ます）

TEXT. -/
/- OMIT:
We will first give an informal sketch. Let ``f : X → Y`` be a continuous function from
a compact metric space to a metric space.
We fix ``ε > 0`` and start looking for some ``δ``.

OMIT. -/
/- TEXT:
まず非形式的な証明のあらすじを説明しましょう． ``f : X → Y`` をコンパクトな距離空間から距離空間への連続関数とします．ここで， ``ε > 0`` を固定し，ある ``δ`` を探し始めます．

TEXT. -/
/- OMIT:
Let ``φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)`` and let ``K := { p : X × X | ε ≤ φ p }``.
Observe ``φ`` is continuous since ``f`` and distance are continuous.
And ``K`` is clearly closed (use ``isClosed_le``) hence compact since ``X`` is compact.

OMIT. -/
/- TEXT:
``φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)`` と ``K := { p : X × X | ε ≤ φ p }`` を仮定します． ``f`` と距離は連続であるため， ``φ`` は連続です．また， ``K`` は明らかに閉じている（ ``isClosed_le`` を使います）ので， ``X`` はコンパクトであることから ``K`` はコンパクトになります．

TEXT. -/
/- OMIT:
Then we discuss two possibilities using ``eq_empty_or_nonempty``.
If ``K`` is empty then we are clearly done (we can set ``δ = 1`` for instance).
So let's assume ``K`` is not empty, and use the extreme value theorem to choose ``(x₀, x₁)`` attaining the infimum
of the distance function on ``K``. We can then set ``δ = dist x₀ x₁`` and check everything works.

OMIT. -/
/- TEXT:
ここで ``eq_empty_or_nonempty`` を使って2つの可能性を議論します．もし， ``K`` が空であれば，明らかに成り立ちます（例えば ``δ = 1`` と設定できます）．そこで， ``K`` が空でないと仮定し，極値の定理を使って ``(x₀, x₁)`` を選択し， ``K`` 上の距離関数の下限を求めます．そして ``δ = dist x₀ x₁`` と設定し，これがうまくいくことを確認します．
BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    simpa using this
  · rcases K_cpct.exists_forall_le hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · change _ < _
      rw [dist_pos]
      intro h
      have : ε ≤ 0 := by simpa [*] using xx_in
      linarith
    · intro x x'
      contrapose!
      intro hxx'
      exact H (x, x') hxx'

/- OMIT:
Completeness
^^^^^^^^^^^^

OMIT. -/
/- TEXT:
完全性
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
A Cauchy sequence in a metric space is a sequence whose terms get closer and closer to each other.
There are a couple of equivalent ways to state that idea.
In particular converging sequences are Cauchy. The converse is true only in so-called *complete*
spaces.


OMIT. -/
/- TEXT:
距離空間におけるコーシー列とは，各項がどんどん互いに近づいていく数列のことです．この考え方にはいくつかの等価な言い方があります．特に収束する数列はコーシー列です．その逆はいわゆる **完全** （complete）空間においてのみ成り立ちます．
BOTH: -/
-- QUOTE:
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu
-- QUOTE.

/- OMIT:

We'll practice using this definition by proving a convenient criterion which is a special case of a
criterion appearing in Mathlib. This is also a good opportunity to practice using big sums in
a geometric context. In addition to the explanations from the filters section, you will probably need
``tendsto_pow_atTop_nhds_0_of_lt_1``, ``Tendsto.mul`` and ``dist_le_range_sum_dist``.
OMIT. -/
/- TEXT:
この定義を使う練習として以下の便利な条件を証明しましょう．これはMathlibに登場する条件の特殊なケースです．また，これは幾何学的な文脈で大きな和を使う練習をする良い機会でもあります．フィルタのセクションの説明に加えて，おそらく ``tendsto_pow_atTop_nhds_0_of_lt_1`` と ``Tendsto.mul`` ， ``dist_le_range_sum_dist`` が必要になるでしょう．
BOTH: -/
open BigOperators

open Finset

-- QUOTE:
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry

-- QUOTE.

-- SOLUTIONS:
example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun N : ℕ ↦ (1 / 2 ^ N * 2 : ℝ)) atTop (𝓝 0) := by
      rw [← zero_mul (2 : ℝ)]
      apply Tendsto.mul
      simp_rw [← one_div_pow (2 : ℝ)]
      apply tendsto_pow_atTop_nhds_0_of_lt_1 <;> linarith
      exact tendsto_const_nhds
    rcases(atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, _, hN⟩
    exact ⟨N, by simpa using (hN N left_mem_Ici).2⟩
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by rw [dist_comm, add_zero]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) :=
      (dist_le_range_sum_dist (fun i ↦ u (N + i)) k)
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := (sum_le_sum fun i _ ↦ hu <| N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by simp_rw [← one_div_pow, pow_add, ← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 :=
      (mul_le_mul_of_nonneg_left (sum_geometric_two_le _)
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) _)))
    _ < ε := hN


/- OMIT:

We are ready for the final boss of this section: Baire's theorem for complete metric spaces!
The proof skeleton below shows interesting techniques. It uses the ``choose`` tactic in its exclamation
mark variant (you should experiment with removing this exclamation mark) and it shows how to
define something inductively in the middle of a proof using ``Nat.rec_on``.

OMIT. -/
/- TEXT:
本節のラスボスへ挑む準備が整いました：完全距離空間に対するベールの定理です！以下の証明の骨組みでは興味深いテクニックを駆使しています．これは ``choose`` タクティクを使っており（このビックリマークを削除してみることをおすすめします）， ``Nat.rec_on`` を使って証明の途中で帰納的に何かを定義する方法を示しています．
BOTH: -/
-- QUOTE:
open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦ pow_pos sorry n
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases Metric.mem_closure_iff.1 this (δ / 2) (half_pos δpos) with ⟨y, ys, xy⟩
    rw [dist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedBall y r ⊆ f n :=
      nhds_basis_closedBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine' ⟨y, min (min (δ / 2) r) (B (n + 1)), _, _, fun z hz ↦ ⟨_, _⟩⟩
    show 0 < min (min (δ / 2) r) (B (n + 1))
    exact lt_min (lt_min (half_pos δpos) rpos) (Bpos (n + 1))
    show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
    exact min_le_right _ _
    show z ∈ closedBall x δ
    exact
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := (add_le_add hz xy.le)
        _ ≤ δ / 2 + δ / 2 := (add_le_add_right ((min_le_left _ _).trans (min_le_left _ _)) _)
        _ = δ := add_halves δ

    show z ∈ f n
    exact
      hr
        (calc
          dist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
          _ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
          )
  choose! center radius Hpos HB Hball using this
  refine' fun x ↦ (mem_closure_iff_nhds_basis nhds_basis_closedBall).2 fun ε εpos ↦ _
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
    `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
    `closedBall (c n) (r n)` is included in the previous ball and in `f n`, and such that
    `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
    limit which belongs to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    exact min_le_right _ _
    exact HB n (c n) (r n) (rpos n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := fun n ↦
    Hball n (c n) (r n) (rpos n)
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [dist_comm]
    have A : c (n + 1) ∈ closedBall (c (n + 1)) (r (n + 1)) :=
      mem_closedBall_self (rpos <| n + 1).le
    have I :=
      calc
        closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
          (incl n).trans (inter_subset_left _ _)
        _ ⊆ closedBall (c n) (B n) := closedBall_subset_closedBall (rB n)

    exact I A
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine' Nat.le_induction _ fun m hnm h ↦ _
    · exact Subset.rfl
    · exact (incl m).trans ((Set.inter_subset_left _ _).trans h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    refine' isClosed_ball.mem_of_tendsto ylim _
    refine' (Filter.eventually_ge_atTop n).mono fun m hm ↦ _
    exact I n m hm (mem_closedBall_self (rpos _).le)
  constructor
  · suffices ∀ n, y ∈ f n by rwa [Set.mem_iInter]
    intro n
    have : closedBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) (inter_subset_right _ _)
    exact this (yball (n + 1))
  calc
    dist y x ≤ r 0 := yball 0
    _ ≤ ε := min_le_left _ _


/- OMIT:

BOTH: -/

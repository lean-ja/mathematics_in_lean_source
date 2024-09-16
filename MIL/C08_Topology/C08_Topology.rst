.. _topology:

.. index:: topology

位相
========

.. Topology
.. ========

.. Calculus is based on the concept of a function, which is used to model
.. quantities that depend on one another.
.. For example, it is common to study quantities that change over time.
.. The notion of a *limit* is also fundamental.
.. We may say that the limit of a function :math:`f(x)` is a value :math:`b`
.. as :math:`x` approaches a value :math:`a`,
.. or that :math:`f(x)` *converges to* :math:`b` as :math:`x` approaches :math:`a`.
.. Equivalently, we may say that a :math:`f(x)` approaches :math:`a` as :math:`x`
.. approaches a value :math:`b`, or that it *tends to* :math:`b`
.. as :math:`x` tends to :math:`a`.
.. We have already begun to consider such notions in :numref:`sequences_and_convergence`.

微積分は関数の概念に基づいており，互いに依存しあう量をモデル化するのに用いられます．例えば，時間とともに変化する量についての研究は一般的です．また **極限** （limit）という概念も基本的なものです．関数 :math:`f(x)` の極限は :math:`x` の値が :math:`a` に近づくにつれて :math:`b` になる，あるいは :math:`f(x)` は :math:`x` が :math:`a` に近づくにつれて :math:`b` に **収束する** （converges to）と言うことができます．同様に， :math:`f(x)` は :math:`x` が :math:`a` に近づくにつれて :math:`b` に近づく，あるいは :math:`x` が :math:`a` に近づくにつれて :math:`b` に **限りなく近づく** （tends to）と言うこともできます．このような概念について :numref:`sequences_and_convergence` で既に考察しています．

.. *Topology* is the abstract study of limits and continuity.
.. Having covered the essentials of formalization in Chapters :numref:`%s <basics>`
.. to :numref:`%s <structures>`,
.. in this chapter, we will explain how topological notions are formalized in Mathlib.
.. Not only do topological abstractions apply in much greater generality,
.. but that also, somewhat paradoxically, make it easier to reason about limits
.. and continuity in concrete instances.

**位相** （Topology）は極限と連続性についての抽象的な研究です． :numref:`%s <basics>` 章から :numref:`%s <structures>` 章までで形式化の要点を説明しましたが，この章ではMathlibで位相的な概念がそのように形式化されているかを説明します．位相的な抽象化は，より一般的に適用できるだけでなく，逆説的ではありますが，具体的な事例における極限や連続性についての推論を容易にします．

.. Topological notions build on quite a few layers of mathematical structure.
.. The first layer is naive set theory,
.. as described in :numref:`Chapter %s <sets_and_functions>`.
.. The next layer is the theory of *filters*, which we will describe in :numref:`filters`.
.. On top of that, we layer
.. the theories of *topological spaces*, *metric spaces*, and a slightly more exotic
.. intermediate notion called a *uniform space*.

位相的な概念は，数学的な構造のかなり多くのレイヤーの上に成り立っています．最初の層は素朴な集合論で， :numref:`Chapter %s <sets_and_functions>` で説明しています．次の層は :numref:`filters` で説明する **フィルタ** （filter）の理論です．その上に **位相空間** （topological spaces）， **距離空間** （metric spaces），そして少し独特的な中間概念である **一様空間** （uniform space）の理論を重ねます．

.. Whereas previous chapters relied on mathematical notions that were likely
.. familiar to you,
.. the notion of a filter less well known,
.. even to many working mathematicians.
.. The notion is essential, however, for formalizing mathematics effectively.
.. Let us explain why.
.. Let ``f : ℝ → ℝ`` be any function. We can consider
.. the limit of ``f x`` as ``x`` approaches some value ``x₀``,
.. but we can also consider the limit of ``f x`` as ``x`` approaches infinity
.. or negative infinity.
.. We can moreover consider the limit of ``f x`` as ``x`` approaches ``x₀`` from
.. the right, conventionally written ``x₀⁺``, or from the left,
.. written  ``x₀⁻``. There are variations where ``x`` approaches ``x₀`` or ``x₀⁺``
.. or ``x₀⁻`` but
.. is not allowed to take on the value ``x₀`` itself.
.. This results in at least eight ways that ``x`` can approach something.
.. We can also restrict to rational values of ``x``
.. or place other constraints on the domain, but let's stick to those 8 cases.

これまでの章では，読者にとってなじみ深い数学的概念に頼っていましたが，フィルタの概念は現役の数学者であってもあまり知られていません．しかし，この概念は数学を効果的に形式化するためには不可欠です．その理由を説明しましょう． ``f : ℝ → ℝ`` を任意の関数とします．ここで ``x`` がある値 ``x₀`` に近づいたときの ``f x`` の極限を考えることができますが， ``x`` が無限大や負の無限大に近づいたときの ``f x`` の極限を考えることもできます．さらに， ``x`` が右から ``x₀`` に近づいた時（これは慣習的に ``x₀⁺`` と書かれます），また左側から近づいたとき（ ``x₀⁻`` と書かれます）の ``f x`` の極限を考えることもできます． ``x`` が ``x₀`` や ``x₀⁺`` ， ``x₀⁻`` に近づく方法はさまざまである一方， ``x₀`` の値自体を取ることは許可されていないとします．この結果，少なくとも8つの方法で ``x`` が何らかの値に近づくことができます． ``x`` を有理数の値に制限したり，始域にほかの制約を加えることもできますが，この8つのケースに限定することにしましょう．

.. We have a similar variety of options on the codomain:
.. we can specify that ``f x`` approaches a value from the left or right,
.. or that it approaches positive or negative infinity, and so on.
.. For example, we may wish to say that ``f x`` tends to ``+∞``
.. when ``x`` tends to ``x₀`` from the right without
.. being equal to ``x₀``.
.. This results in 64 different kinds of limit statements,
.. and we haven't even begun to deal with limits of sequences,
.. as we did in :numref:`sequences_and_convergence`.

また終域に同じようにいくつかのオプションを設けることができます: ``f x`` が左か右，もしくは正・負の無限などから近づくことを指定できます．例えば， ``x`` が右から ``x₀`` にならないように限りなく ``x₀`` に近づくとき， ``f x`` は ``+∞`` に限りなく近づくということができます．この結果， :numref:`sequences_and_convergence` で行った数列の極限を扱い始めてないにもかかわらず，もうすでに64種類の極限に関する文が存在することになります．

.. The problem is compounded even further when it comes to the supporting lemmas.
.. For instance, limits compose: if
.. ``f x`` tends to ``y₀`` when ``x`` tends to ``x₀`` and
.. ``g y`` tends to ``z₀`` when ``y`` tends to ``y₀`` then
.. ``g ∘ f x`` tends to ``z₀`` when ``x`` tends to ``x₀``.
.. There are three notions of "tends to" at play here,
.. each of which can be instantiated in any of the eight ways described
.. in the previous paragraph.
.. This results in 512 lemmas, a lot to have to add to a library!
.. Informally, mathematicians generally prove two or three of these
.. and simply note that the rest can be proved "in the same way."
.. Formalizing mathematics requires making the relevant notion of "sameness"
.. fully explicit, and that is exactly what Bourbaki's theory of filters
.. manages to do.

極限にかかわる補題となると問題はさらに複雑になります．例えば，極限は次のように合成されます: ``x`` が ``x₀`` に限りなく近づくときに ``f x`` が ``y₀`` に限りなく近づき，また ``y`` が ``y₀`` に限りなく近づくとき ``g y`` が ``z₀`` に限りなく近づくならば， ``g ∘ f x`` は ``x`` が ``x₀`` に限りなく近づくとき ``z₀`` に限りなく近づきます．ここでは3つの「限りなく近づく」概念が働いており，それぞれ前の段落で説明した8つの方法のいずれかでインスタンス化することができます．この結果，512の補題が生まれ，ライブラリに追加しなければならなくなります！非形式的には，数学者は一般的にこれらのうち2つか3つを証明し，残りは「同様の方法で」証明できることを示すだけです．数学を形式化するには，この「同じ」という概念を完全に明示する必要があり，これこそブルバキのフィルタ理論が取り扱うことです．

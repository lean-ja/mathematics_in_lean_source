import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

/- OMIT:
Filters
-------

OMIT. -/
/- TEXT:
.. index:: Filter

.. _filters:

フィルタ
------------

TEXT. -/
/- OMIT:
A *filter* on a type ``X`` is a collection of sets of ``X`` that satisfies three
conditions that we will spell out below. The notion
supports two related ideas:

OMIT. -/
/- TEXT:
型 ``X`` に対する **フィルタ** は，以下に述べる3つの条件を満たす ``X`` の元からなる集合のあつまりです．この概念から2つのアイデアが提供されます．

TEXT. -/
/- OMIT:
* *limits*, including all the kinds of limits discussed above: finite and infinite limits of sequences, finite and infinite limits of functions at a point or at infinity, and so on.

OMIT. -/
/- TEXT:
* **極限** （limit），数列の有限・無限極限，ある点，もしくは無限大における関数の有限・無限極限など今まで議論してきたすべての極限を含んだもの

TEXT. -/
/- OMIT:
* *things happening eventually*, including things happening for large enough ``n : ℕ``, or sufficiently near a point ``x``, or for sufficiently close pairs of points, or almost everywhere in the sense of measure theory. Dually, filters can also express the idea of *things happening often*: for arbitrarily large ``n``, at a point in any neighborhood of a given point, etc.

OMIT. -/
/- TEXT:
* **やがて起こりうること** （things happening eventually），これは十分大きい ``n : ℕ`` ，もしくはある点 ``x`` の十分近傍について，あるいは十分近い点のペアや測度論の意味でのほぼすべての場所で起こることを含みます．また，それと対をなすようにフィルタは任意の大きさの点 ``n`` や，任意の近傍の点などについて， **頻繁に起こること** （things happening often）を表現することもできます．

TEXT. -/
/- OMIT:
The filters that correspond to these descriptions will be defined later in this section, but we can already name them:

OMIT. -/
/- TEXT:
上記の記述に対応するフィルタはこの節の後半で定義しますが，先に名称を出しておきましょう．

TEXT. -/
/- OMIT:
* ``(atTop : Filter ℕ)``, made of sets of ``ℕ`` containing ``{n | n ≥ N}`` for some ``N``
* ``𝓝 x``, made of neighborhoods of ``x`` in a topological space
* ``𝓤 X``, made of entourages of a uniform space (uniform spaces generalize metric spaces and topological groups)
* ``μ.ae`` , made of sets whose complement has zero measure with respect to a measure ``μ``.

OMIT. -/
/- TEXT:
* ``(atTop : Filter ℕ)`` ，ある ``N`` について ``{n | n ≥ N}`` を含む ``ℕ`` の集合のあつまり
* ``𝓝 x`` ，位相空間の ``x`` の近傍のあつまり
* ``𝓤 X`` ，一様空間（一様空間とは距離空間と位相群を一般化したものです）の近縁のあつまり
* ``μ.ae`` ，集合のあつまりで，各集合の補集合が測度 ``μ`` に対して零測度をもつもの

TEXT. -/
/- OMIT:
The general definition is as follows: a filter ``F : Filter X`` is a
collection of sets ``F.sets : Set (Set X)`` satisfying the following:

OMIT. -/
/- TEXT:
一般的な定義は以下のとおりです: フィルタ ``F : Filter X`` は以下の条件を満たす集合のあつまり ``F.sets : Set (Set X)`` です:

* ``F.univ_sets : univ ∈ F.sets``
* ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
* ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``.

TEXT. -/
/- OMIT:
The first condition says that the set of all elements of ``X`` belongs to ``F.sets``.
The second condition says that if ``U`` belongs to ``F.sets`` then anything
containing ``U`` also belongs to ``F.sets``.
The third condition says that ``F.sets`` is closed under finite intersections.
In Mathlib, a filter ``F`` is defined to be a structure bundling ``F.sets`` and its
three properties, but the properties carry no additional data,
and it is convenient to blur the distinction between ``F`` and ``F.sets``. We
therefore define ``U ∈ F`` to mean ``U ∈ F.sets``.
This explains why the word ``sets`` appears in the names of some lemmas that
that mention ``U ∈ F``.

OMIT. -/
/- TEXT:
最初の条件は ``X`` のすべての要素の集合は ``F.sets`` に属するというものです．2つ目の条件は ``U`` が ``F.sets`` に属する場合， ``U`` を含むものはすべて ``F.sets`` に属するということです．3つ目の条件は， ``F.sets`` は有限な共通集合で閉じているということです．Mathlibでは，フィルタ ``F`` は ``F.sets`` とその3つのプロパティをまとめた構造体として定義されていますが，プロパティはデータを追加で持つことはないため， ``F`` と ``F.sets`` の区別を曖昧にするのに便利です．したがって， ``U ∈ F`` を ``U ∈ F.sets`` の意味として定義します．これが， ``U ∈ F`` に言及する補題の名前に ``sets`` という単語が登場するものが散見される理由です．

TEXT. -/
/- OMIT:
It may help to think of a filter as defining a notion of a "sufficiently large" set. The first
condition then says that ``univ`` is sufficiently large, the second one says that a set containing a sufficiently
large set is sufficiently large and the third one says that the intersection of two sufficiently large sets
is sufficiently large.

OMIT. -/
/- TEXT:
フィルタとは，「十分大きい」集合の概念を定義するものだと考えると良いでしょう．最初の条件は ``univ`` が十分に大きいことを言い，2番めの条件は十分に大きい集合を含む集合も十分大きいことを，そして3番目の条件は十分に大きい2つの集合の共通集合が十分に大きいことを言っています．

TEXT. -/
/- OMIT:
It may be even  more useful to think of a filter on a type ``X``
as a generalized element of ``Set X``. For instance, ``atTop`` is the
"set of very large numbers" and ``𝓝 x₀`` is the "set of points very close to ``x₀``."
One manifestation of this view is that we can associate to any ``s : Set X`` the so-called *principal filter*
consisting of all sets that contain ``s``.
This definition is already in Mathlib and has a notation ``𝓟`` (localized in the ``Filter`` namespace).
For the purpose of demonstration, we ask you to take this opportunity to work out the definition here.
OMIT. -/
/- TEXT:
型 ``X`` のフィルタを ``Set X`` の一般化された要素と考えるとさらに便利かもしれません．例えば， ``atTop`` は「非常に大きな数の集合」であり， ``𝓝 x₀`` は「 ``x₀`` に非常に近い点の集合」です．この考え方が現れている例の1つとして，任意の ``s : Set X`` に対して ``s`` を含むすべての集合からなるいわゆる **主フィルタ** （principal filter）を関連付けることができる，というものがあります．この定義はすでにMathlibに存在しており， ``𝓟`` という表記が与えられています．（ ``Filter`` 名前空間にローカライズされています）フィルタの定義の体験するちょうど良い機会なので，この定義に取り組んでみましょう．
EXAMPLES: -/
-- QUOTE:
def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry
-- QUOTE.

-- SOLUTIONS:
-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }

/- OMIT:
For our second example, we ask you to define the filter ``atTop : Filter ℕ``.
(We could use any type with a preorder instead of ``ℕ``.)
OMIT. -/
/- TEXT:
2つ目の例題として， ``atTop : Filter ℕ`` を定義してみましょう．（ ``ℕ`` の代わりに前順序を持つ任意の型を使うことができます．）
EXAMPLES: -/
-- QUOTE:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := sorry
    sets_of_superset := sorry
    inter_sets := sorry }
-- QUOTE.

-- SOLUTIONS:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use 42
      simp
    sets_of_superset := by
      rintro U V ⟨N, hN⟩ hUV
      use N
      tauto
    inter_sets := by
      rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
      use max N N'
      intro b hb
      rw [max_le_iff] at hb
      constructor <;> tauto }

/- OMIT:
We can also directly define the filter ``𝓝 x`` of neighborhoods of any ``x : ℝ``.
In the real numbers, a neighborhood of ``x`` is a set containing an open interval
:math:`(x_0 - \varepsilon, x_0 + \varepsilon)`,
defined in Mathlib as ``Ioo (x₀ - ε) (x₀ + ε)``.
(This is notion of a neighborhood is only a special case of a more general construction in Mathlib.)

OMIT. -/
/- TEXT:
また，任意の ``x : ℝ`` の近傍のフィルタ ``𝓝 x`` を直接定義することもできます．実数において ``x`` の近傍とは開区間 :math:`(x_0 - \varepsilon, x_0 + \varepsilon)` を含む集合のことで，Mathlibでは ``Ioo (x₀ - ε) (x₀ + ε)`` と定義されています．（この近傍の概念は，Mathlibにおけるより一般的な構造の特殊なケースにすぎません．）

TEXT. -/
/- OMIT:
With these examples, we can already define what is means for a function ``f : X → Y``
to converge to some ``G : Filter Y`` along some ``F : Filter X``,
as follows:
OMIT. -/
/- TEXT:
これらの例から，関数 ``f : X → Y`` がある ``F : Filter X`` に沿って ``G : Filter Y`` に収束するとはどういうことかを以下のように定義できます．
BOTH: -/
-- QUOTE:
def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- OMIT:
When ``X`` is ``ℕ`` and ``Y`` is ``ℝ``, ``Tendsto₁ u atTop (𝓝 x)`` is equivalent to saying that the sequence ``u : ℕ → ℝ``
converges to the real number ``x``. When both ``X`` and ``Y`` are ``ℝ``, ``Tendsto f (𝓝 x₀) (𝓝 y₀)``
is equivalent to the familiar notion :math:`\lim_{x \to x₀} f(x) = y₀`.
All of the other kinds of limits mentioned in the introduction are
also equivalent to instances of ``Tendsto₁`` for suitable choices of filters on the source and target.

OMIT. -/
/- TEXT:
``X`` が ``ℕ`` で ``Y`` が ``ℝ`` であるとき， ``Tendsto₁ u atTop (𝓝 x)`` は数列 ``u : ℕ → ℝ`` が実数 ``x`` に収束するということと等価です． ``X`` と ``Y`` の両方が ``ℝ`` であるとき， ``Tendsto f (𝓝 x₀) (𝓝 y₀)`` はおなじみの :math:`\lim_{x \to x₀} f(x) = y₀` と等価です．冒頭で述べた他の種類の極限も，入力と出力のフィルタを適切に選択すれば，すべて ``Tendsto₁`` のインスタンスと等価です．

TEXT. -/
/- OMIT:
The notion ``Tendsto₁`` above is definitionally equivalent to the notion ``Tendsto`` that is defined in Mathlib,
but the latter is defined more abstractly.
The problem with the definition of ``Tendsto₁`` is that it exposes a quantifier and elements of ``G``,
and it hides the intuition that we get by viewing filters as generalized sets. We can
hide the quantifier ``∀ V`` and make the intuition more salient by using more algebraic and set-theoretic machinery.
The first ingredient is the *pushforward* operation :math:`f_*` associated to any map ``f : X → Y``,
denoted ``Filter.map f`` in Mathlib. Given a filter ``F`` on ``X``, ``Filter.map f F : Filter Y`` is defined so that
``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F`` holds definitionally.
In this examples file we've opened the ``Filter`` namespace so that
``Filter.map`` can be written as ``map``. This means that we can rewrite the definition of ``Tendsto`` using
the order relation on ``Filter Y``, which is reversed inclusion of the set of members.
In other words, given ``G H : Filter Y``, we have ``G ≤ H ↔ ∀ V : Set Y, V ∈ H → V ∈ G``.
OMIT. -/
/- TEXT:
上記の ``Tendsto₁`` の概念はMathlibで定義されている ``Tendsto`` と定義上等価ですが，後者のほうがより抽象的に定義されています． ``Tendsto₁`` の定義の問題点は，量化子と ``G`` の要素を公開してしまう点にあり，これによってフィルタを一般化された集合としてみなすことで得られる直感的なイメージをうすめてしまっています．量化子 ``∀ V`` を隠し，より代数的・集合論的な仕組みを使うことで直感的なイメージをよりはっきりさせることができます．そのための最初の要素は，任意の写像 ``f : X → Y`` に関連した **押し出し** （pushforward）演算子 :math:`f_*` で，これはMathlibでは ``Filter.map f`` と表記されています． ``X`` 上のフィルタ ``F`` が与えられた時， ``Filter.map f F : Filter Y`` は ``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F`` が定義上成り立つように定義されています．本書のサンプルファイルでは， ``Filter.map`` を ``map`` と書けるように ``Filter`` 名前空間をオープンしています．このことは ``Filter Y`` の集合の要素の包含を逆にした順序関係を使って ``Tendsto`` の定義を書き直すことができることを意味します．つまり， ``G H : Filter Y`` が与えられると， ``G ≤ H ↔ ∀ V : Set Y, V ∈ H → V ∈ G`` が成り立ちます．
EXAMPLES: -/
-- QUOTE:
def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl
-- QUOTE.

/- OMIT:
It may seem that the order relation on filters is backward. But recall that we can view filters on ``X`` as
generalized elements of ``Set X``, via the inclusion of ``𝓟 : Set X → Filter X`` which maps any set ``s`` to the corresponding principal filter.
This inclusion is order preserving, so the order relation on ``Filter`` can indeed be seen as the natural inclusion relation
between generalized sets. In this analogy, pushforward is analogous to the direct image.
And, indeed, ``map f (𝓟 s) = 𝓟 (f '' s)``.

OMIT. -/
/- TEXT:
フィルタの順序関係が逆だと思われるかもしれません．しかし，任意の集合 ``s`` を対応する主フィルタに写す包含 ``𝓟 : Set X → Filter X`` によって， ``X`` 上のフィルタを ``Set X`` の一般化された要素としてみなすことが出来ることを思い出してください．この包含写像は順序を保存するため， ``Filter`` の順序関係は一般化された集合間の自然な包含関係とみなすことができます．この類推において，押し出しは順像に類似しています．そして実際に ``map f (𝓟 s) = 𝓟 (f '' s)`` となります．

TEXT. -/
/- OMIT:
We can now understand intuitively why a sequence ``u : ℕ → ℝ`` converges to
a point ``x₀`` if and only if we have ``map u atTop ≤ 𝓝 x₀``.
The inequality means the "direct image under ``u``" of
"the set of very big natural numbers" is "included" in "the set of points very close to ``x₀``."

OMIT. -/
/- TEXT:
以上から数列 ``u : ℕ → ℝ`` が点 ``x₀`` に収束するのは ``map u atTop ≤ 𝓝 x₀`` である場合に限る理由を直観的に理解できます．この不等式は「非常に大きな自然数の集合」の「 ``u`` の下の順像」が「 ``x₀`` に非常に近い点の集合」に「含まれる」ことを意味します．

TEXT. -/
/- OMIT:
As promised, the definition of ``Tendsto₂`` does not exhibit any quantifiers or sets.
It also leverages the algebraic properties of the pushforward operation.
First, each ``Filter.map f`` is monotone. And, second, ``Filter.map`` is compatible with
composition.
OMIT. -/
/- TEXT:
約束通り， ``Tendsto₂`` の定義は量化子や集合を明示しません．また押し出し演算の代数的特性を活用しています．まず各 ``Filter.map f`` は単調です．そして第二に， ``Filter.map`` は合成と互換性があります．
EXAMPLES: -/
-- QUOTE:
#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)
-- QUOTE.

/- OMIT:
Together these two properties allow us to prove that limits compose, yielding in one shot all 256 variants
of the composition lemma described in the introduction, and lots more.
You can practice proving the following statement using either the definition
of ``Tendsto₁`` in terms of the
universal quantifier or the algebraic definition,
together with the two lemmas above.
OMIT. -/
/- TEXT:
この2つの性質を組み合わせると，極限の合成を証明することができ，冒頭で述べた合成の256個の補題とそれ以上のものが一発で得られます．演習として上の2つの補題と一緒に普遍量化子か代数的定義による ``Tendsto₁`` を使って以下の文を証明してみましょう．
EXAMPLES: -/
-- QUOTE:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg


example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  intro V hV
  rw [preimage_comp]
  apply hf
  apply hg
  exact hV

/- OMIT:
The pushforward construction uses a map to push filters from the map source to the map target.
There also a *pullback* operation, ``Filter.comap``, going in the other direction.
This generalizes the
preimage operation on sets. For any map ``f``,
``Filter.map f`` and ``Filter.comap f`` form what is known as a *Galois connection*,
which is to say, they satisfy

  ``Filter.map_le_iff_le_comap : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G``

for every ``F`` and ``G``.
This operation could be used to provided another formulation of ``Tendsto`` that would be provably
(but not definitionally) equivalent to the one in Mathlib.

OMIT. -/
/- TEXT:
押し出しによる構成は写像を使用して写像の入力から出力にフィルタを押し出します．また **引き戻し** （pullback） ``Filter.comap`` という反対方向の演算もあります．これは集合上の逆像に対する操作を一般化したものです．任意の写像 ``f`` に対して， ``Filter.map f`` と ``Filter.comap f`` は各 ``F`` と ``G`` に対して以下を満たす **ガロア接続** （Galois connection）として知られるものを形成します．

  ``Filter.map_le_iff_le_comap : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G``

この操作を使ってMathlibのものと等価なことを証明できる（しかし定義的には等しくない） ``Tendsto`` の別の定式化ができます．

TEXT. -/
/- OMIT:
The ``comap`` operation can be used to restrict filters to a subtype. For instance, suppose we have ``f : ℝ → ℝ``,
``x₀ : ℝ`` and ``y₀ : ℝ``, and suppose we want to state that ``f x`` approaches ``y₀`` when ``x`` approaches ``x₀`` within the rational numbers.
We can pull the filter ``𝓝 x₀`` back to ``ℚ`` using the coercion map
``(↑) : ℚ → ℝ`` and state ``Tendsto (f ∘ (↑) : ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)``.
OMIT. -/
/- TEXT:
``comap`` 演算はフィルタを部分型に制限するために使うことができます．例えば， ``f : ℝ → ℝ`` と ``x₀ : ℝ`` ， ``y₀ : ℝ`` があり， 有理数の範囲内で ``x`` が ``x₀`` に近づくと ``f x`` が ``y₀`` に近づくとします．ここで強制の写像 ``(↑) : ℚ → ℝ`` を使って ``𝓝 x₀`` を ``ℚ`` に引き戻すことで ``Tendsto (f ∘ (↑) : ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)`` とすることができます．
EXAMPLES: -/
-- QUOTE:
variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- OMIT:
The pullback operation is also compatible with composition, but it is *contravariant*,
which is to say, it reverses the order of the arguments.
OMIT. -/
/- TEXT:
引き戻し演算も合成と互換性がありますが，こちらは **反変** （contravariant），つまり引数の順序を逆にします．
EXAMPLES: -/
-- QUOTE:
section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end
-- QUOTE.

/- OMIT:
Let's now shift attention to the plane ``ℝ × ℝ`` and try to understand how the neighborhoods of a point
``(x₀, y₀)`` are related to ``𝓝 x₀`` and ``𝓝 y₀``. There is a product operation
``Filter.prod : Filter X → Filter Y → Filter (X × Y)``, denoted by ``×ˢ``, which answers this question:
OMIT. -/
/- TEXT:
ここで平面 ``ℝ × ℝ`` に目を向けて，点 ``(x₀, y₀)`` の近傍が ``𝓝 x₀`` と ``𝓝 y₀`` にどのように関係しているか考えてみましょう．この問いの答えは ``×ˢ`` と表記される積の演算 ``Filter.prod : Filter X → Filter Y → Filter (X × Y)`` です:
EXAMPLES: -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq
-- QUOTE.

/- OMIT:
The product operation is defined in terms of the pullback operation and the ``inf`` operation:

  ``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``.

Here the ``inf`` operation refers to the lattice structure on ``Filter X`` for any type ``X``, whereby
``F ⊓ G`` is the greatest filter that is smaller than both ``F`` and ``G``.
Thus the ``inf`` operation generalizes the notion of the intersection of sets.

OMIT. -/
/- TEXT:
積演算は引き戻し演算と ``inf`` 演算で定義されています．

  ``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``.

ここで ``inf`` 演算は任意の型 ``X`` に対する ``Filter X`` 上の束構造を指し， ``F ⊓ G`` は ``F`` と ``G`` の両方よりも小さい最大のフィルターです．このように， ``inf`` 演算は集合の共通部分の概念を一般化したものです．

TEXT. -/
/- OMIT:
A lot of proofs in Mathlib use all of the aforementioned structure (``map``, ``comap``, ``inf``, ``sup``, and ``prod``)
to give algebraic proofs about convergence without ever referring to members of filters.
You can practice doing this in a proof of the following lemma, unfolding the definition of ``Tendsto``
and ``Filter.prod`` if needed.
OMIT. -/
/- TEXT:
Mathlibの多くの証明では，前述の構造（ ``map`` ， ``comap`` ， ``inf`` ， ``sup`` ， ``prod`` ）をすべて使用して，フィルタのメンバを参照することなく収束に関する代数的な証明を行っています．このスタイルの練習として，以下の補題を ``Tendsto`` と ``Filter.prod`` の定義を展開しながら証明してみましょう．
EXAMPLES: -/
-- QUOTE:
#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  calc
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔ map f atTop ≤ 𝓝 (x₀, y₀) := Iff.rfl
    _ ↔ map f atTop ≤ 𝓝 x₀ ×ˢ 𝓝 y₀ := by rw [nhds_prod_eq]
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ⊓ comap Prod.snd (𝓝 y₀) := Iff.rfl
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ∧ map f atTop ≤ comap Prod.snd (𝓝 y₀) := le_inf_iff
    _ ↔ map Prod.fst (map f atTop) ≤ 𝓝 x₀ ∧ map Prod.snd (map f atTop) ≤ 𝓝 y₀ := by
      rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
    _ ↔ map (Prod.fst ∘ f) atTop ≤ 𝓝 x₀ ∧ map (Prod.snd ∘ f) atTop ≤ 𝓝 y₀ := by
      rw [map_map, map_map]


-- an alternative solution
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  rw [nhds_prod_eq]
  unfold Tendsto SProd.sprod Filter.instSProd Filter.prod
  erw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]

/- OMIT:
The ordered type ``Filter X`` is actually a *complete* lattice,
which is to say, there is a bottom element, there is a top element, and
every set of filters on ``X`` has an ``Inf`` and a ``Sup``.

OMIT. -/
/- TEXT:
順序型として ``Filter X`` は実際に **完備** （complete）な束です．つまり，ボトムの要素とトップの要素があり， ``X`` 上のフィルタのすべての集合は ``Inf`` と ``Sup`` を持ちます．

TEXT. -/
/- OMIT:
Note that given the second property in the definition of a filter
(if ``U`` belongs to ``F`` then anything larger than ``U`` also belongs to ``F``),
the first property
(the set of all inhabitants of ``X`` belongs to ``F``) is
equivalent to the property that ``F`` is not the empty collection of sets.
This shouldn't be confused with the more subtle question as to whether
the empty set is an *element* of ``F``. The
definition of a filter does not prohibit ``∅ ∈ F``,
but if the empty set is in ``F`` then
every set is in ``F``, which is to say, ``∀ U : Set X, U ∈ F``.
In this case, ``F`` is a rather trivial filter, which is precisely the
bottom element of the complete lattice ``Filter X``.
This contrasts with the definition of filters in
Bourbaki, which doesn't allow filters containing the empty set.

OMIT. -/
/- TEXT:
フィルタの定義中の2つ目の性質（ ``U`` が ``F`` に属するのであれば， ``U`` より大きいものすべてが ``F`` に属する）を考えると，1つ目の性質（ ``X`` のすべての要素からなる集合は ``F`` に属する）は ``F`` が集合の集まりとして空ではないという性質と等価であることに注意してください．これは空集合が ``F`` の **要素** であるかどうかという，より微妙な問題と混同してはいけません．フィルタの定義は ``∅ ∈ F`` を禁止していませんが，もし空集合が ``F`` に含まれるなら，すべての集合は ``F`` に含まれることに成ります．この場合， ``F`` は完備束 ``Filter X`` のボトムの要素であるとても自明なものになります．これはブルバキにおける空集合を含むフィルタは許さないとしてフィルタの定義とは対照的です．

TEXT. -/
/- OMIT:
Because we include the trivial filter in our definition, we sometimes need to explicitly assume
nontriviality in some lemmas.
In return, however, the theory has nicer global properties.
We have already seen that including the trivial filter gives us a
bottom element. It also allows us to define ``principal : Set X → Filter X``,
which maps  ``∅`` to ``⊥``, without adding a precondition to rule out the empty set.
And it allows us to define the pullback operation without a precondition as well.
Indeed, it can happen that ``comap f F = ⊥`` although ``F ≠ ⊥``. For instance,
given ``x₀ : ℝ`` and ``s : Set ℝ``, the pullback of ``𝓝 x₀`` under the coercion
from the subtype corresponding to ``s`` is nontrivial if and only if ``x₀`` belongs to the
closure of ``s``.

OMIT. -/
/- TEXT:
本書の定義には自明なフィルタが含まれているため，いくつかの補題では非自明性を明示的に仮定する必要があります．しかし，その代わりに理論はより良い大域的な性質を持ちます．自明なフィルタを含めるとボトムの要素が得られることは既に見ました．また空集合を除外する前提条件なしに， ``∅`` を ``⊥`` に写す ``principal : Set X → Filter X`` を定義することもできます．さらに引き戻し演算も同様に前提条件なしで定義できます．実際， ``F ≠ ⊥`` であるにもかかわらず， ``comap f F = ⊥`` が成り立つことがあります．例えば， ``x₀ : ℝ`` と ``s : Set ℝ`` が与えられた時， ``x₀`` が ``s`` の閉包に属する場合に限り， ``s`` に対応する部分型からの強制下での ``𝓝 x₀`` の引き戻しは自明ではありません．

TEXT. -/
/- OMIT:
In order to manage lemmas that do need to assume some filter is nontrivial, Mathlib has
a type class ``Filter.NeBot``, and the library has lemmas that assume
``(F : Filter X) [F.NeBot]``. The instance database knows, for example, that ``(atTop : Filter ℕ).NeBot``,
and it knows that pushing forward a nontrivial filter gives a nontrivial filter.
As a result, a lemma assuming ``[F.NeBot]`` will automatically apply to ``map u atTop`` for any sequence ``u``.

OMIT. -/
/- TEXT:
自明でないフィルタがあることを仮定する補題を管理するために，Mathlibには ``Filter.NeBot`` という型クラスがあり，ライブラリ中の補題では ``(F : Filter X) [F.NeBot]`` というように利用しています．インスタンスのデータベースは，例えば ``(atTop : Filter ℕ).NeBot`` があること，また自明でないフィルタを押し出すと自明でないフィルタが得られることを知っています．その結果， ``[F.NeBot]`` を仮定した補題は任意の数列 ``u`` の ``map u atTop`` に対して自動的に適用されます．

TEXT. -/
/- OMIT:
Our tour of the algebraic properties of filters and their relation to limits is essentially done,
but we have not yet justified our claim to have recaptured the usual limit notions.
Superficially, it may seem that ``Tendsto u atTop (𝓝 x₀)``
is stronger than the notion of convergence defined in :numref:`sequences_and_convergence` because we ask that *every* neighborhood of ``x₀``
has a preimage belonging to ``atTop``, whereas the usual definition only requires
this for the standard neighborhoods ``Ioo (x₀ - ε) (x₀ + ε)``.
The key is that, by definition, every neighborhood contains such a standard one.
This observation leads to the notion of a *filter basis*.

OMIT. -/
/- TEXT:
フィルタの代数的な性質と極限との関係についての基本的な紹介は終了しましたが，通常の極限の概念を再現したという主張を正当化するには至っていません．表面的には ``Tendsto u atTop (𝓝 x₀)`` は :numref:`sequences_and_convergence` で定義されている収束の概念よりも強いです．なぜなら，上記の定義では ``x₀`` の **すべて** の近傍に ``atTop`` に属する逆像があることを求めているのに対し，通常の定義では，標準的な近傍 ``Ioo (x₀ - ε) (x₀ + ε)`` に対してのみ求めているからです．重要なのは，定義上すべての近傍はこのような標準的な近傍をすべて含むということです．この観察は **フィルタ基底** （filter basis）という概念に繋がります．

TEXT. -/
/- OMIT:
Given ``F : Filter X``,
a family of sets ``s : ι → Set X`` is a basis for ``F`` if for every set ``U``,
we have ``U ∈ F`` if and only if it contains some ``s i``. In other words, formally speaking,
``s`` is a basis if it satisfies
``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U``. It is even more flexible to consider
a predicate on ``ι`` that selects only some of the values ``i`` in the indexing type.
In the case of ``𝓝 x₀``, we want ``ι`` to be ``ℝ``, we write ``ε`` for ``i``, and the predicate should select the positive values of ``ε``.
So the fact that the sets ``Ioo  (x₀ - ε) (x₀ + ε)`` form a basis for the
neighborhood topology on ``ℝ`` is stated as follows:
OMIT. -/
/- TEXT:
``F : Filter X`` が与えられた時，集合の族 ``s : ι → Set X`` が ``F`` の基底であるとは，すべての集合 ``U`` に対して，ある ``s i`` を含む場合に限り ``U ∈ F`` が成り立つことを言います．形式的に言い換えると， ``s`` は ``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U`` を満たす場合に基底となります．添字型の値 ``i`` の一部のみを取るような ``ι`` に対する述語として考えるとさらに柔軟です．例えば ``𝓝 x₀`` の場合， ``ι`` を ``ℝ`` ， ``i`` を ``ε`` とし， ``ε`` が正の値を取るという述語になります．そこで，集合 ``Ioo  (x₀ - ε) (x₀ + ε)`` が ``ℝ`` 上の近傍位相の基底を形成するという事実は以下のように述べられます．
EXAMPLES: -/
-- QUOTE:
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀
-- QUOTE.

/- OMIT:
There is also a nice basis for the filter ``atTop``. The lemma
``Filter.HasBasis.tendsto_iff`` allows
us to reformulate a statement of the form ``Tendsto f F G``
given bases for ``F`` and ``G``.
Putting these pieces together gives us essentially the notion of convergence
that we used in :numref:`sequences_and_convergence`.
OMIT. -/
/- TEXT:
またフィルタ ``atTop`` に対する良い基底もあります．補題 ``Filter.HasBasis.tendsto_iff`` を使えば， ``F`` と ``G`` の基底が与えられたときに， ``Tendsto f F G`` という形の文を再形式化することができます．これらをまとめると， :numref:`sequences_and_convergence` で取り扱った収束の本質的な概念が得られます．
EXAMPLES: -/
-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
-- QUOTE.

/- OMIT:
We now show how filters facilitate working with properties that hold for sufficiently large numbers
or for points that are sufficiently close to a given point. In :numref:`sequences_and_convergence`, we were often faced with the situation where
we knew that some property ``P n`` holds for sufficiently large ``n`` and that some
other property ``Q n`` holds for sufficiently large ``n``.
Using ``cases`` twice gave us ``N_P`` and ``N_Q`` satisfying
``∀ n ≥ N_P, P n`` and ``∀ n ≥ N_Q, Q n``. Using ``set N := max N_P N_Q``, we could
eventually prove ``∀ n ≥ N, P n ∧ Q n``.
Doing this repeatedly becomes tiresome.

OMIT. -/
/- TEXT:
ここからは，十分に大きな数や与えられた点に十分近い点に対して成り立つ性質をフィルタによって容易に扱える方法を示します． :numref:`sequences_and_convergence` では，ある性質 ``P n`` が十分に大きい ``n`` に対して成り立ち，他の性質 ``Q n`` が十分に大きい ``n`` に対して成り立つという状況によく直面しました．この場合 ``cases`` を2回使うと， ``∀ n ≥ N_P, P n`` と ``∀ n ≥ N_Q, Q n`` を満たす ``N_P`` と ``N_Q`` が得られます．そして ``set N := max N_P N_Q`` を使うことでようやく ``∀ n ≥ N, P n ∧ Q n`` を証明することができます．これを繰り返すのは面倒です．

TEXT. -/
/- OMIT:
We can do better by noting that the statement "``P n`` and ``Q n`` hold for large enough ``n``" means
that we have ``{n | P n} ∈ atTop`` and ``{n | Q n} ∈ atTop``.
The fact that ``atTop`` is a filter implies that the intersection of two elements of ``atTop``
is again in ``atTop``, so we have ``{n | P n ∧ Q n} ∈ atTop``.
Writing ``{n | P n} ∈ atTop`` is unpleasant,
but we can use the more suggestive notation ``∀ᶠ n in atTop, P n``.
Here the superscripted ``f`` stands for "Filter."
You can think of the notation as saying that for all ``n`` in the "set of very large numbers," ``P n`` holds. The ``∀ᶠ``
notation stands for ``Filter.Eventually``, and the lemma ``Filter.Eventually.and`` uses the intersection property of filters to do what we just described:
OMIT. -/
/- TEXT:
「 ``P n`` と ``Q n`` は十分な大きさの ``n`` に対して成り立つ」という文が ``{n | P n} ∈ atTop`` と ``{n | Q n} ∈ atTop`` が成り立つことを意味する点に注意すればうまくいきます． ``atTop`` がフィルタであるということは， ``atTop`` の2つの要素の共通部分もまた ``atTop`` の中にあることを意味するので， ``{n | P n ∧ Q n} ∈ atTop`` となります． ``{n | P n} ∈ atTop`` と書くのは好ましくないため，より示唆的な表記として ``∀ᶠ n in atTop, P n`` を使うことができます．ここで上付き文字の ``f`` は ``Filter`` を表しています．この表記は「非常に大きな数の集合」に含まれるすべての ``n`` に対して ``P n`` が成り立つということだと考えることができます． ``∀ᶠ`` という表記は ``Filter.Eventually`` を意味し，また補題 ``Filter.Eventually.and`` は先程説明したフィルタの共通部分の性質を使っています:
EXAMPLES: -/
-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ
-- QUOTE.

/- OMIT:
This notation is so convenient and intuitive that we also have specializations
when ``P`` is an equality or inequality statement. For example, let ``u`` and ``v`` be
two sequences of real numbers, and let us show that if
``u n`` and ``v n`` coincide for sufficiently large ``n`` then
``u`` tends to ``x₀`` if and only if ``v`` tends to ``x₀``.
First we'll use the generic ``Eventually`` and then the one
specialized for the equality predicate, ``EventuallyEq``. The two statements are
definitionally equivalent so the same proof work in both cases.
OMIT. -/
/- TEXT:
この表記法は非常に便利で直感的であるため， ``P`` が等式または不等式である場合の特殊版も存在します．例えば， ``u`` と ``v`` を2つの実数の列とします．そして ``u n`` と ``v n`` が十分に大きい ``n`` で一致する場合， ``v`` が ``x₀`` に収束する場合に限り ``u`` が ``x₀`` に収束することを示しましょう．以下の1つ目では一般的な ``Eventually`` を使い，次の例では等式の述語に特化した ``EventuallyEq`` を用います．この2つの文は定義上等しいため，どちらの場合でも同じ証明が通ります．
EXAMPLES: -/
-- QUOTE:
example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h
-- QUOTE.

/- OMIT:
It is instructive to review the definition of filters in terms of ``Eventually``.
Given ``F : Filter X``, for any predicates ``P`` and ``Q`` on ``X``,

OMIT. -/
/- TEXT:
フィルタの定義を ``Eventually`` の観点から復習することは有益です． ``X`` 上の任意の述語 ``P`` と ``Q`` に対して ``F : Filter X`` が与えられたとしたとき，
TEXT. -/
/- OMIT:
* the condition ``univ ∈ F`` ensures ``(∀ x, P x) → ∀ᶠ x in F, P x``,
* the condition ``U ∈ F → U ⊆ V → V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``, and
* the condition ``U ∈ F → V ∈ F → U ∩ V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``.
OMIT. -/
/- TEXT:

* 条件 ``univ ∈ F`` は ``(∀ x, P x) → ∀ᶠ x in F, P x`` を，
* 条件 ``U ∈ F → U ⊆ V → V ∈ F`` は ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x`` を，
* 条件 ``U ∈ F → V ∈ F → U ∩ V ∈ F`` は ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x`` を保証します．
EXAMPLES: -/
-- QUOTE:
#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and
-- QUOTE.

/- OMIT:
The second item, corresponding to ``Eventually.mono``, supports nice ways
of using filters, especially when combined
with ``Eventually.and``. The ``filter_upwards`` tactic allows us to combine them.
Compare:
OMIT. -/
/- TEXT:
2つ目の項目は ``Eventually.mono`` に対応し，特に ``Eventually.and`` と組み合わせることでフィルタの良い扱い方をサポートします． ``filter_upwards`` タクティクはこの組み合わせを行ってくれます．比較してみましょう：
EXAMPLES: -/
-- QUOTE:
example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩
-- QUOTE.

/- OMIT:
Readers who know about measure theory will note that the filter ``μ.ae`` of sets whose complement has measure zero
(aka "the set consisting of almost every point") is not very useful as the source or target of ``Tendsto``, but it can be conveniently
used with ``Eventually`` to say that a property holds for almost every point.

OMIT. -/
/- TEXT:
測度論を知っている読者なら，補集合が測度0である集合のフィルタ ``μ.ae`` （いわゆる「ほとんどすべての点からなる集合」）は ``Tendsto`` の入力や出力としてはあまり役に立たないことに気づくでしょう．しかし， ``Eventually`` と一緒に使ってほとんどすべての点で成り立つ性質について言及する場合には便利です．

TEXT. -/
/- OMIT:
There is a dual version of ``∀ᶠ x in F, P x``, which is occasionally useful:
``∃ᶠ x in F, P x`` means
``{x | ¬P x} ∉ F``. For example, ``∃ᶠ n in atTop, P n`` means there are arbitrarily large ``n`` such that ``P n`` holds.
The ``∃ᶠ`` notation stands for ``Filter.Frequently``.

OMIT. -/
/- TEXT:
``∀ᶠ x in F, P x`` には ``{x | ¬P x} ∉ F`` を意味する双対バージョン ``∃ᶠ x in F, P x`` があり，これは時折役立ちます．例えば， ``∃ᶠ n in atTop, P n`` は ``P n`` が成り立つような任意の大きさの ``n`` が存在することを意味します． ``∃ᶠ`` は ``Filter.Frequently`` を表します．

TEXT. -/
/- OMIT:
For a more sophisticated example, consider the following statement about a sequence
``u``, a set ``M``, and a value ``x``:

  If ``u`` converges to ``x`` and ``u n`` belongs to ``M`` for
  sufficiently large ``n`` then ``x`` is in the closure of ``M``.

OMIT. -/
/- TEXT:
より複雑な例として，数列 ``u`` ，集合 ``M`` ，値 ``x`` についての以下の文を考えてみましょう．

  もし ``u`` が ``x`` に収束し，十分大きい ``n`` について ``u n`` が ``M`` に属するならば， ``x`` は ``M`` の閉包の中にある．

TEXT. -/
/- OMIT:
This can be formalized as follows:

  ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``.

This is a special case of the theorem ``mem_closure_of_tendsto`` from the
topology library.
See if you can prove it using the quoted lemmas,
using the fact that ``ClusterPt x F`` means ``(𝓝 x ⊓ F).NeBot`` and that,
by definition, the assumption ``∀ᶠ n in atTop, u n ∈ M`` means  ``M ∈ map u atTop``.
OMIT. -/
/- TEXT:
これは以下のように形式化されます：

  ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``.

これは位相についてのライブラリの定理 ``mem_closure_of_tendsto`` の特殊な場合です．以下に掲げた補題と ``ClusterPt x F`` が ``(𝓝 x ⊓ F).NeBot`` を，仮定 ``∀ᶠ n in atTop, u n ∈ M`` が定義上 ``M ∈ map u atTop`` を意味するという事実を用いて証明してみましょう．
EXAMPLES: -/
-- QUOTE:
#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  mem_closure_iff_clusterPt.mpr (neBot_of_le <| le_inf hux <| le_principal_iff.mpr huM)

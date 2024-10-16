-- BOTH:
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

/- TEXT:
.. _groups:

TEXT. -/
/- OMIT:
Monoids and Groups
------------------

OMIT. -/
/- TEXT:
モノイドと群
------------------

.. index:: monoid
.. index:: group (algebraic structure)

TEXT. -/
/- OMIT:
Monoids and their morphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
モノイドとその射
^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
Courses in abstract algebra often start with groups and
then progress to rings, fields, and vector spaces. This involves some contortions when discussing
multiplication on rings since the multiplication operation does not come from a group structure
but many of the proofs carry over verbatim from group theory to this new setting.
The most common fix, when doing mathematics with pen and paper,
is to leave those proofs as exercises. A less efficient but safer and
more formalization-friendly way of proceeding is to use monoids. A *monoid* structure on a type `M`
is an internal composition law that is associative and has a neutral element.
Monoids are used primarily to accommodate both groups and the multiplicative structure of
rings. But there are also a number of natural examples; for instance, the set of natural numbers
equipped with addition forms a monoid.

OMIT. -/
/- TEXT:
抽象代数の講義は群から始まり，環，体，ベクトル空間へと進んでいくことが多いです．環上の乗算を論じる際には乗算の演算が群構造に由来しないため若干のゆがみが生じますが，証明の多くは群論からこの新しい設定にそのまま引き継がれます．この歪みについてペンと紙を使って数学をする場合の最も一般的な修正は，これらの証明を演習問題として残すことです．効率は悪いですが，より安全で形式化しやすい方法はモノイドを使うことです．型 `M` 上の **モノイド** （monoid）構造とは，結合的であり，中立的な要素を持つ内部合成法則のことです．モノイドは主に群と環の情報構造の両方に対応するために使われます．しかし，自然な例も数多くあります；例えば，加算を備えた自然数の集合はモノイドを形成します．

TEXT. -/
/- OMIT:
From a practical point of view, you can mostly ignore monoids when using Mathlib. But you need
to know they exist when you are looking for a lemma by browsing Mathlib files. Otherwise, you
might end up looking for a statement in the group theory files when it is actually in the found
with monoids because it does not require elements to be invertible.

OMIT. -/
/- TEXT:
Mathlibを使う際には実用的な観点としてモノイドはほとんど無視できます．しかし，Mathlibのファイルを眺めて補題を探す際にはモノイドの存在を知っておく必要があります．そうでなければ，探しているある文について元が可逆である必要が無い場合，本当はモノイドのファイルで見つかるはずであるのに，群論のファイルを探してしまう事態になりかねません．

TEXT. -/
/- OMIT:
The type of monoid structures on a type ``M`` is written ``Monoid M``.
The function ``Monoid`` is a type class so it will almost always appear as an instance implicit
argument (in other words, in square brackets).
By default, ``Monoid`` uses multiplicative notation for the operation; for additive notation
use ``AddMonoid`` instead.
The commutative versions of these structures add the prefix ``Comm`` before ``Monoid``.
OMIT. -/
/- TEXT:
型 ``M`` 上のモノイド構造の型は ``Monoid M`` と表記します．関数 ``Monoid`` は型クラスであるため，ほとんどの場合インスタンスの暗黙の引数として（つまり角括弧の中）現れます．デフォルトでは ``Monoid`` は乗法で演算を行います；加法で演算を行う場合は ``AddMonoid`` を使用してください．これらの構造体の可換バージョンは ``Monoid`` の前に接頭辞 ``Comm`` をつけます．
EXAMPLES: -/
-- QUOTE:
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
-- QUOTE.

/- OMIT:
Note that although ``AddMonoid`` is found in the library,
it is generally confusing to use additive notation with a non-commutative operation.

OMIT. -/
/- TEXT:
``AddMonoid`` はライブラリにありはしますが，可換ではない演算で加法表記を使うのは一般的に混乱を招く点に留意してください．

TEXT. -/
/- OMIT:
The type of morphisms between monoids ``M`` and ``N`` is called ``MonoidHom M N`` and written
``M →* N``. Lean will automatically see such a morphism as a function from ``M`` to ``N`` when
we apply it to elements of ``M``. The additive version is called ``AddMonoidHom`` and written
``M →+ N``.
OMIT. -/
/- TEXT:
モノイド ``M`` と ``N`` の間の射の型を ``MonoidHom M N`` と呼び， ``M →* N`` と書きます．Leanはこのような射を ``M`` の要素に適用すると，自動的に ``M`` から ``N`` への関数として見るようになります．これの加法バージョンは ``AddMonoidHom`` と呼ばれ， ``M →+ N`` と書かれます．
EXAMPLES: -/
-- QUOTE:
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
-- QUOTE.

/- OMIT:
These morphisms are bundled maps, i.e. they package together a map and some of its properties.
Remember that :numref:`section_hierarchies_morphisms` explains bundled maps;
here we simply note the slightly unfortunate consequence that we cannot use ordinary function
composition to compose maps. Instead, we need to use ``MonoidHom.comp`` and ``AddMonoidHom.comp``.
OMIT. -/
/- TEXT:
これらの射は束縛写像，つまり写像とその性質をパッケージしたものです．束縛写像については :numref:`section_hierarchies_morphisms` にて説明しています；ここでは，写像を合成するにあたって通常の関数合成を使うことができないという少し残念な結果を記させていただきます．この代わりに， ``MonoidHom.comp`` と ``AddMonoidHom.comp`` を使う必要があります．
EXAMPLES: -/
-- QUOTE:
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
-- QUOTE.

/- OMIT:
Groups and their morphisms
^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
群とその射
^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We will have much more to say about groups, which are monoids with the extra
property that every element has an inverse.
OMIT. -/
/- TEXT:
すべての元が逆元を持つという特別な性質を有するモノイドである群について，さらに多くのことを語ることになるでしょう．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x
-- QUOTE.

/- TEXT:

.. index:: group (tactic), tactics ; group

TEXT. -/
/- OMIT:
Similar to the ``ring`` tactic that we saw earlier, there is a ``group`` tactic that proves
any identity that holds in any group. (Equivalently, it proves the identities that hold in
free groups.)

OMIT. -/
/- TEXT:
以前見た ``ring`` タクティクと同様に，任意の群で成り立つあらゆる等式を証明する ``group`` タクティクが存在します．（これは同様に，自由群成り立つ等式も証明します．）
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group
-- QUOTE.

/- TEXT:
.. index:: abel, tactics ; abel

TEXT. -/
/- OMIT:
There is also a tactic for identities in commutative additive groups called ``abel``.

OMIT. -/
/- TEXT:
また可換加法群の等式用として ``abel`` というタクティクがあります．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel
-- QUOTE.

/- OMIT:
Interestingly, a group
morphism is nothing more than a monoid morphism between groups. So we can copy and paste one of our
earlier examples, replacing ``Monoid`` with ``Group``.
OMIT. -/
/- TEXT:
興味深いことに，群の射は群の間におけるモノイドの射にほかなりません．そのため，先ほどの例の1つをコピペして ``Monoid`` を ``Group`` に置き換えることができます．
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y
-- QUOTE.

/- OMIT:
Of course we do get some new properties, such as this one:
OMIT. -/
/- TEXT:
もちろん群の射について，次のような新しい性質もあります：
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x
-- QUOTE.

/- OMIT:
You may be worried that constructing group morphisms will require us to do unnecessary work since
the definition of monoid morphism enforces that neutral elements are sent to neutral elements
while this is automatic in the case of group morphisms. In practice the extra work is not hard,
but, to avoid it, there is a function building a group morphism from a function
between groups that is compatible with the composition laws.
OMIT. -/
/- TEXT:
もしかしたら群の射を構成するにあたって不要な作業が必要になることを憂慮するかもしれません．というのも，モノイドの射の定義では，中立元は中立元に送られることを要求しますが，群の射の場合は自動的に満たされるからです．実際にはこの余分な作業は難しくはありませんが，これを避けるために群の間の関数から，合成法則を保ちつつ群の射を作る関数があります．
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h
-- QUOTE.

/- OMIT:
There is also a type ``MulEquiv`` of group (or monoid) isomorphisms denoted by ``≃*`` (and
``AddEquiv`` denoted by ``≃+`` in additive notation).
The inverse of ``f : G ≃* H`` is ``MulEquiv.symm f : H ≃* G``,
composition of ``f`` and ``g`` is ``MulEquiv.trans f g``, and
the identity isomorphism of ``G`` is ``M̀ulEquiv.refl G``.
Using anonymous projector notation, the first two can be written ``f.symm`` and
``f.trans g`` respectively.
Elements of this type are automatically coerced to morphisms and functions when necessary.
OMIT. -/
/- TEXT:
また，群（またはモノイド）の同型についての型 ``MulEquiv`` が用意されており， ``≃*`` と表記されます（そして加法表記については ``AddEquiv`` にて ``≃+`` と表記します）． ``f : G ≃* H`` の逆射は ``MulEquiv.symm f : H ≃* G`` ， ``f`` と ``g`` の合成は ``MulEquiv.trans f g`` ，そして ``G`` についての恒等な同型は ``M̀ulEquiv.refl G`` をそれぞれ用います．匿名の射影記法を用いると，最初の2つはそれぞれ ``f.symm`` と ``f.trans g`` と書くことができます．この型の要素は必要に応じて自動的に射や関数に強制されます．
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm
-- QUOTE.

/- OMIT:
One can use ``MulEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.
OMIT. -/
/- TEXT:
``MulEquiv.ofBijective`` を使うことで，全単射の射から同型を作ることができます．これにより逆関数は計算不可能になります．
EXAMPLES: -/
-- QUOTE:
noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h
-- QUOTE.

/- OMIT:
Subgroups
^^^^^^^^^

OMIT. -/
/- TEXT:
部分群
^^^^^^^^^

TEXT. -/
/- OMIT:
Just as group morphisms are bundled, a subgroup of ``G`` is also a bundled structure consisting of
a set in ``G`` with the relevant closure properties.
OMIT. -/
/- TEXT:
群の射が束縛されるように， ``G`` の部分群も ``G`` の集合とそれに関連する閉性を束縛した構造です．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx
-- QUOTE.

/- OMIT:
In the example above, it is important to understand that ``Subgroup G`` is the type of subgroups
of ``G``, rather than a predicate ``IsSubgroup H`` where ``H`` is an element of ``Set G``.
``Subgroup G`` is endowed with a coercion to ``Set G`` and a membership predicate on ``G``.
See :numref:`section_hierarchies_subobjects` for an explanation of how and why this is done.

OMIT. -/
/- TEXT:
上の例では， ``Subgroup G`` は ``G`` の部分群の型であり， ``IsSubgroup H`` という述語（ここで ``H`` は ``Set G`` の要素）ではないことを理解することが重要です． ``Subgroup G`` は ``Set G`` に対する強制子と ``G`` に対する帰属についての述語を持ちます．この方法と理由については :numref:`section_hierarchies_subobjects` を参照してください．

TEXT. -/
/- OMIT:
Of course, two subgroups are the same if and only if they have the same elements. This fact
is registered for use with the ``ext`` tactic, which can be used to prove two subgroups are
equal in the same way it is used to prove that two sets are equal.

OMIT. -/
/- TEXT:
もちろん，2つの部分群が同じであるのは，それらが同じ要素を持つ場合だけです．この事実は ``ext`` タクティクで使用するために登録されており，2つの集合が等しいことを証明するためと同じ使用方法で，2つの部分群が等しいことを証明するために用いることができます．

TEXT. -/
/- OMIT:
To state and prove, for example, that ``ℤ`` is an additive subgroup of ``ℚ``,
what we really want is to construct a term of type ``AddSubgroup ℚ`` whose projection to
``Set ℚ`` is ``ℤ``, or, more precisely, the image of ``ℤ`` in ``ℚ``.
OMIT. -/
/- TEXT:
例えば， ``ℤ`` が ``ℚ`` の加法部分群であることを記述・証明するには， ``Set ℚ`` への射影が ``ℤ`` （より正確には ``ℚ`` での ``ℤ`` の像）である ``AddSubGroup ℚ`` 型の項を作る必要があります．
EXAMPLES: -/
-- QUOTE:
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp
-- QUOTE.

/- OMIT:
Using type classes, Mathlib knows that a subgroup of a group inherits a group structure.
OMIT. -/
/- TEXT:
型クラスを使って，Mathlibは群の部分群が群構造を継承することを知っています．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance
-- QUOTE.

/- OMIT:
This example is subtle. The object ``H`` is not a type, but Lean automatically coerces it to
a type by interpreting it as a subtype of ``G``.
So the above example can be restated more explicitly as:
OMIT. -/
/- TEXT:
この例は微妙です．オブジェクト ``H`` は型ではありませんが，Leanはこれを ``G`` の部分型と解釈することで自動的に型に強制します．つまり，上の例はより明確には次のように言い換えることができます：
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
-- QUOTE.

/- OMIT:
An important benefit of having a type ``Subgroup G`` instead of a predicate
``IsSubgroup : Set G → Prop`` is that one can easily endow ``Subgroup G`` with additional structure.
Importantly, it has the structure of a complete lattice structure with respect to
inclusion. For instance, instead of having a lemma stating that an intersection of
two subgroups of ``G`` is again a subgroup, we
have used the lattice operation ``⊓`` to construct the intersection. We can then apply arbitrary
lemmas about lattices to the construction.

OMIT. -/
/- TEXT:
述語 ``IsSubgroup : Set G → Prop`` の代わりに ``Subgroup G`` 型を持つことの重要な利点は， ``Subgroup G`` に追加の構造を簡単に付与できることです．重要なのは，包含に関して完備束の構造を持つことです．例えば， ``G`` の2つの部分群の共通部分が再び部分群であるという補題を持つ代わりに，束の演算 ``⊓`` を使って共通部分を構成しました．そして，束に関する任意の補題をこの構成に適用することができます．

TEXT. -/
/- OMIT:
Let us check that the set underlying the infimum of two subgroups is indeed, by definition,
their intersection.
OMIT. -/
/- TEXT:
ここで，2つの部分群の下限の台集合が定義上，本当にそれらの共通部分であることを確認しましょう．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl
-- QUOTE.

/- OMIT:
It may look strange to have a different notation for what amounts to the intersection of the
underlying sets, but the correspondence does not carry over to the supremum operation and set
union, since a union of subgroups is not, in general, a subgroup.
Instead one needs to use the subgroup generated by the union, which is done
using ``Subgroup.closure``.
OMIT. -/
/- TEXT:
台集合の共通部分に相当するものに対して，異なる表記をするのは奇妙に見えるかもしれませんが，部分群の和は一般的に部分群ではないため，この対応は上限の演算や集合の合併には引き継がれません．その代わりに，合併から生成される部分群を使用する必要があり，これは ``Subgroup.closure`` を使用して得られます．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]
-- QUOTE.

/- OMIT:
Another subtlety is that ``G`` itself does not have type ``Subgroup G``,
so we need a way to talk about ``G`` seen as a subgroup of ``G``.
This is also provided by the lattice structure: the full subgroup is the top element of
this lattice.
OMIT. -/
/- TEXT:
もう一つの微妙な点は， ``G`` 自身は ``Subgroup G`` という型を持たないため， ``G`` の部分群として見た ``G`` について語る方法が必要だということです．これもまた束の構造から得られます：完全部分群はこの束の一番上の要素です．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
-- QUOTE.

/- OMIT:
Similarly the bottom element of this lattice is the subgroup whose only element is the
neutral element.
OMIT. -/
/- TEXT:
同様に，この束の一番下の要素は中立元のみを持つ部分群です．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot
-- QUOTE.

/- OMIT:
As an exercise in manipulating groups and subgroups, you can define the conjugate of a subgroup
by an element of the ambient group.
OMIT. -/
/- TEXT:
群や部分群の操作についての演習問題として，ベースの群の元による部分群の共役を定義してみましょう．
BOTH: -/
-- QUOTE:
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
-- BOTH:
  inv_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
-- BOTH:
  mul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group
-- BOTH:
-- QUOTE.

/- OMIT:
Tying the previous two topics together, one can push forward and pull back subgroups using
group morphisms. The naming convention in Mathlib is to call those operations ``map``
and ``comap``.
These are not the common mathematical terms, but they have the advantage of being
shorter than "pushforward" and "direct image."
OMIT. -/
/- TEXT:
以前の2つのトピックを結び付けると，群の射を使って部分群を押し出したり引き戻したりすることができます．Mathlibの命名規則では，これらの操作を ``map`` と ``comap`` と呼んでいます．これらは一般的な数学用語ではありませんが，「押し出し（pushforward）」や「順像（direct image）」よりも短いという利点があります．
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap
-- QUOTE.

/- OMIT:
In particular, the preimage of the bottom subgroup under a morphism ``f`` is a subgroup called
the *kernel* of ``f``, and the range of ``f`` is also a subgroup.
OMIT. -/
/- TEXT:
特に，射 ``f`` のもとでのボトムの部分群による逆像は ``f`` の **核** （kernel）と呼ばれる部分群であり， ``f`` のrangeも部分群となります．
EXAMPLES: -/
-- QUOTE:
example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range
-- QUOTE.

/- OMIT:
As exercises in manipulating group morphisms and subgroups, let us prove some elementary properties.
They are already proved in Mathlib, so do not use ``exact?`` too quickly if you want to benefit
from these exercises.
OMIT. -/
/- TEXT:
群の射と部分群の操作についての演習問題として，いくつかの初歩的な性質を証明しましょう．これらの性質はMathlibですでに証明されているため，演習の効能を得たいのであれば， ``exact?`` に頼るのはなるべく後にしましょう．
BOTH: -/
-- QUOTE:
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_comap] at * -- Lean does not need this line
  exact hST hx
-- BOTH:

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro x hx
  rw [mem_map] at * -- Lean does not need this line
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy
-- BOTH:

variable {K : Type*} [Group K]

-- OMIT: Remember you can use the `ext` tactic to prove an equality of subgroups.
-- 部分群の同値を証明するために `ext` タクティクを使えることを覚えておいてください．
-- BOTH:
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  -- The whole proof could be ``rfl``, but let's decompose it a bit.
  ext x
  simp only [mem_comap]
  rfl
-- BOTH:

-- OMIT: Pushing a subgroup along one homomorphism and then another is equal to
-- OMIT: pushing it forward along the composite of the homomorphisms.
-- ある部分群をある準同型に沿って押し出し，さらに別の準同型に沿って押し出すことは
-- その準同型の合成に沿って押し出すことと同じである
-- BOTH:
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    calc ψ.comp φ z = ψ (φ z) := rfl
    _               = ψ y := by congr
    _               = x := hy
-- BOTH:

end exercises
-- QUOTE.

/- OMIT:
Let us finish this introduction to subgroups in Mathlib with two very classical results.
Lagrange theorem states the cardinality of a subgroup of a finite group divides the cardinality of
the group. Sylow's first theorem is a famous partial converse to Lagrange's theorem.

OMIT. -/
/- TEXT:
Mathlibでの部分群の紹介の締めくくりとして，2つの非常に古典的な結果を紹介しましょう．Lagrangeの定理はある有限群の濃度をその部分群の濃度が割り切るというものです．Sylowの第一定理は，Lagrangeの定理の部分的な逆として有名です．

TEXT. -/
/- OMIT:
While this corner of Mathlib is partly set up to allow computation, we can tell
Lean to use nonconstructive logic anyway using the following ``open scoped`` command.
OMIT. -/
/- TEXT:
Mathlibのこのコーナーでは計算可能なように部分的に設定されていますが，次の ``open scoped`` コマンドを使えば，Leanに非構造的な論理を使うように指示することができます．
BOTH: -/
-- QUOTE:
open scoped Classical

-- EXAMPLES:

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

-- BOTH:
open Subgroup

-- EXAMPLES:
example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd
-- QUOTE.

/- OMIT:
The next two exercises derive a corollary of Lagrange's lemma. (This is also already in Mathlib,
so do not use ``exact?`` too quickly.)
OMIT. -/
/- TEXT:
次の2つの演習問題はLagrangeの補題の系を導くものです．（これもすでにMathlibにあるので，すぐには ``exact?`` を使わないこと．）
BOTH: -/
-- QUOTE:
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨y, -, hy'⟩ x hx
    calc x = y := hy' x hx
    _      = 1 := (hy' 1 H.one_mem).symm
-- EXAMPLES:

#check card_dvd_of_le
-- BOTH:

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have D₁ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  exact eq_bot_iff_card.2 (Nat.eq_one_of_dvd_coprimes h D₁ D₂)
-- QUOTE.

/- OMIT:
Concrete groups
^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
具体的な群
^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
One can also manipulate concrete groups in Mathlib, although this is typically more complicated
than working with the abstract theory.
For instance, given any type ``X``, the group of permutations of ``X`` is ``Equiv.Perm X``.
In particular the symmetric group :math:`\mathfrak{S}_n` is ``Equiv.Perm (Fin n)``.
One can state abstract results about this group, for instance saying that ``Equiv.Perm X`` is
generated by cycles if ``X`` is finite.
OMIT. -/
/- TEXT:
Mathlibでは具体的な群を走査することもできますが，これは抽象的な理論を扱うよりも複雑です．例えば，任意の型 ``X`` が与えられた時， ``X`` の置換群は ``Equiv.Perm X`` です．特に，対称群 :math:`\mathfrak{S}_n` は ``Equiv.Perm (Fin n)`` となります．この群について抽象的な結果を述べることができます．例えば， ``X`` が有限である場合， ``Equiv.Perm X`` は巡回置換によって生成されます．
EXAMPLES: -/
-- QUOTE:
open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle
-- QUOTE.

/- OMIT:
One can be fully concrete and compute actual products of cycles. Below we use the ``#simp`` command,
which calls the ``simp`` tactic on a given expression. The notation ``c[]`` is used to define a
cyclic permutation. In the example, the result is a permutation of ``ℕ``. One could use a type
ascription such as ``(1 : Fin 5)`` on the first number appearing to make it a computation in
``Perm (Fin 5)``.
OMIT. -/
/- TEXT:
完全に具体化して巡回置換の実際の積を計算することもできます．以下では与えらえた式に ``simp`` タクティクを呼び出す ``#simp`` コマンドを使用します． ``c[]`` という記法を用いて巡回置換を定義しています．この例では，結果は ``ℕ`` の置換です．最初に現れる数に ``(1 : Fin 5)`` のような型アスクリプションを使用することで， ``Perm (Fin 5)`` の計算が可能になります．
EXAMPLES: -/
-- QUOTE:
#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]
-- QUOTE.

/- OMIT:
Another way to work with concrete groups is to use free groups and group presentations.
The free group on a type ``α`` is ``FreeGroup α`` and the inclusion map is
``FreeGroup.of : α → FreeGroup α``. For instance let us define a type ``S`` with three elements denoted
by ``a``, ``b`` and ``c``, and the element ``ab⁻¹`` of the corresponding free group.
OMIT. -/
/- TEXT:
具体的な群を扱うもう一つの方法は，自由群と群の表示を用いることです．型 ``α`` の自由群は ``FreeGroup α`` であり，包含写像は ``FreeGroup.of : α → FreeGroup α`` です．例えば， ``a`` ， ``b`` ， ``c`` と書かれる3つの元からなる型 ``S`` と，これに対応する自由群に含まれる元 ``ab⁻¹`` を定義しましょう．
EXAMPLES: -/
-- QUOTE:
section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹
-- QUOTE.

/- OMIT:
Note that we gave the expected type of the definition so that Lean knows that ``.of`` means
``FreeGroup.of``.

OMIT. -/
/- TEXT:
Leanが ``.of`` が ``FreeGroup.of`` を意味することが分かるように，定義に期待される型を与えていることに注意してください．

TEXT. -/
/- OMIT:
The universal property of free groups is embodied as the equivalence ``FreeGroup.lift``.
For example, let us define the group morphism from ``FreeGroup S`` to ``Perm (Fin 5)`` that
sends ``a`` to ``c[1, 2, 3]``, ``b`` to ``c[2, 3, 1]``, and ``c`` to ``c[2, 3]``,
OMIT. -/
/- TEXT:
自由群の普遍性は同値 ``FreeGroup.lift`` として具現化されます．例えば， ``a`` を ``c[1, 2, 3]`` に， ``b`` を ``c[2, 3, 1]`` に， ``c`` を ``c[2, 3]`` に送る ``FreeGroup S`` から ``Perm (Fin 5)`` への群の射を定義しましょう．
EXAMPLES: -/
-- QUOTE:
def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]

-- QUOTE.

/- OMIT:
As a last concrete example, let us see how to define a group generated by a single element whose
cube is one (so that group will be isomorphic to :math:`\mathbb{Z}/3`) and build a morphism
from that group to ``Perm (Fin 5)``.

OMIT. -/
/- TEXT:
最後の具体例として，3乗すると1になる単一の元から生成された群（このためこの群は :math:`\mathbb{Z}/3` と同型になります）を定義し，この群から ``Perm (Fin 5)`` への射を構築する方法を見てみましょう．

TEXT. -/
/- OMIT:
As a type with exactly one element, we will use ``Unit`` whose
only element is denoted by ``()``. The function ``PresentedGroup`` takes a set of relations,
i.e. a set of elements of some free group, and returns a group that is this free group quotiented
by a normal subgroup generated by relations. (We will see how to handle more general quotients
in :numref:`quotient_groups`.) Since we somehow hide this behind a definition, we use ``deriving Group`` to force creation
of a group instance on ``myGroup``.
OMIT. -/
/- TEXT:
要素を1つだけ持つ型として，ここでは唯一の要素を ``()`` で表す ``Unit`` を使用します．関数 ``PresentedGroup`` は関係の集合（つまりある自由群の元の集合）を受け取り，この自由群の関係によって生成される正規部分群による商群を返します．（より一般的な商の扱い方は :numref:`quotient_groups` で説明します．）これは定義に隠れてしまうため， ``deriving Group`` を使って ``myGroup`` に群のインスタンスを作成します．
EXAMPLES: -/
-- QUOTE:
def myGroup := PresentedGroup {.of () ^ 3} deriving Group
-- QUOTE.

/- OMIT:
The universal property of presented groups ensures that morphisms out of this group can be built
from functions that send the relations to the neutral element of the target group.
So we need such a function and a proof that the condition holds. Then we can feed this proof
to ``PresentedGroup.toGroup`` to get the desired group morphism.
OMIT. -/
/- TEXT:
群の表示の普遍性から，この群からの射が関係を対象の群の中立元に送る関数から構築できることを保証します．そこで，そのような関数とその条件が成り立つことの証明が必要になります．そしてこの証明を ``PresentedGroup.toGroup`` に与えることで，目的の群の射を得ることができます．
EXAMPLES: -/
-- QUOTE:
def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup
-- QUOTE.

/- OMIT:
Group actions
^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
群作用
^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
One important way that group theory interacts with the rest of mathematics is through
the use of group actions.
An action of a group ``G`` on some type ``X`` is nothing more than a morphism from ``G`` to
``Equiv.Perm X``. So in a sense group actions are already covered by the previous discussion.
But we don't want to carry this morphism around; instead, we want it to be inferred automatically
by Lean as much as possible. So we have a type class for this, which is ``MulAction G X``.
The downside of this setup is that having multiple actions of the same group on the same type
requires some contortions, such as defining type synonyms, each of which carries different
type class instances.

OMIT. -/
/- TEXT:
群論が数学の他の分野と相互作用する重要な方法の一つに群作用があります．ある型 ``X`` に対する群 ``G`` の作用は ``G`` から ``Equiv.Perm X`` への射にほかなりません．したがってある意味において，群作用はすでに以前の議論で網羅されています．しかし，この射を持ち歩きたくはありません；その代わりにできるだけLeanによって自動的に推論されるようにしたいです．そこで，このために ``MulAction G X`` という型クラスが用意されています．この構成の欠点は，同じ型に同じ群の複数の作用を持つ場合，それぞれを異なる型クラスのインスタンスが割り当てられるよう型シノニムを定義するなどの工夫が必要になることです．

TEXT. -/
/- OMIT:
This allows us in particular to use ``g • x`` to denote the action of a group element ``g`` on
a point ``x``.
OMIT. -/
/- TEXT:
これによって特に，ある点 ``x`` に対する群の元の作用を表すのに ``g • x`` を使うことができます．
BOTH: -/
-- QUOTE:
noncomputable section GroupActions

-- EXAMPLES:
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
-- QUOTE.

/- OMIT:
There is also a version for additive group called ``AddAction``, where the action is denoted by
``+ᵥ``. This is used for instance in the definition of affine spaces.
OMIT. -/
/- TEXT:
これには ``AddAction`` という加法群版もあり，この作用は ``+ᵥ`` で表されます．これは例えばアフィン空間の定義で使われます．
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm
-- QUOTE.

/- OMIT:
The underlying group morphism is called ``MulAction.toPermHom``.
OMIT. -/
/- TEXT:
この作用に対応する群の射は ``MulAction.toPermHom`` と呼ばれます．
EXAMPLES: -/
-- QUOTE:
open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X
-- QUOTE.

/- OMIT:
As an illustration let us see how to define the Cayley isomorphism embedding of any group ``G`` into
a permutation group, namely ``Perm G``.
OMIT. -/
/- TEXT:
例として，任意の群 ``G`` の置換群，すなわち ``Perm G`` への埋め込みをケイリー同型に定義する方法を見てみましょう．
EXAMPLES: -/
-- QUOTE:
def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G
-- QUOTE.

/- OMIT:
Note that nothing before the above definition required having a group rather than a monoid (or any
type endowed with a multiplication operation really).

OMIT. -/
/- TEXT:
以前とは異なり，上記の定義おいてはモノイド（あるいは乗算演算を持つ任意の型）ではなく，群であることを要求していることに注意してください．

TEXT. -/
/- OMIT:
The group condition really enters the picture when we will want to partition ``X`` into orbits.
The corresponding equivalence relation on ``X`` is called ``MulAction.orbitRel``.
It is not declared as a global instance.
OMIT. -/
/- TEXT:
群の条件は ``X`` を軌道に類別したいときに本当に重要になります．これに対応する ``X`` 上の同値関係は ``MulAction.orbitRel`` と呼ばれます．これはグローバルのインスタンスとして宣言されていません．
EXAMPLES: -/
/- OMIT:
TODO: We need to explain `Setoid` somewhere.
EXAMPLES. -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X
-- QUOTE.

/- OMIT:
Using this we can state that ``X`` is partitioned into orbits under the action of ``G``.
More precisely, we get a bijection between ``X`` and the dependent product
``(ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω))``
where ``Quotient.out' ω`` simply chooses an element that projects to ``ω``.
Recall that elements of this dependent product are pairs ``⟨ω, x⟩`` where the type
``orbit G (Quotient.out' ω)`` of ``x`` depends on ``ω``.
OMIT. -/
/- TEXT:
これを用いて ``X`` は ``G`` の作用の下で軌道に類別されます．より正確には， ``X`` と依存積 ``(ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω))`` の間の全単射を得ることができます．ここで ``Quotient.out' ω`` は単に ``ω`` に射影する要素を選ぶだけです．この依存積の要素はペア ``⟨ω, x⟩`` であり，ここで ``x`` の ``orbit G (Quotient.out' ω)`` 型は ``ω`` に依存することを思い出してください．
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X
-- QUOTE.

/- OMIT:
In particular, when X is finite, this can be combined with ``Fintype.card_congr`` and
``Fintype.card_sigma`` to deduce that the cardinality of ``X`` is the sum of the cardinalities
of the orbits.
Furthermore, the orbits are in bijection with the quotient of ``G`` under the action of the
stabilizers by left translation.
This action of a subgroup by left-translation is used to define quotients of a group by a
subgroup with notation `/` so we can use the following concise statement.
OMIT. -/
/- TEXT:
特にXが有限である場合， ``Fintype.card_congr`` と ``Fintype.card_sigma`` を組み合わせることで， ``X`` の濃度は軌道の濃度の和であることを導くことができます．さらに，軌道は左移動作用による固定部分群の作用の下での ``G`` の商と全単射となります．この左移動作用による部分群の作用は， `/` という表記の部分群による商を定義するのに用いられるため，以下の簡潔な文を使うことができます．
EXAMPLES: -/
-- QUOTE:
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x
-- QUOTE.

/- OMIT:
An important special case of combining the above two results is when ``X`` is a group ``G``
equipped with the action of a subgroup ``H`` by translation.
In this case all stabilizers are trivial so every orbit is in bijection with ``H`` and we get:
OMIT. -/
/- TEXT:
上記の2つの結果を組み合わせた重要な特殊ケースは， ``X`` が移動作用による部分群 ``H`` の作用を備えた群 ``G`` である場合です．この場合，すべての固定部分群は自明であるため，すべての軌道は ``H`` と全単射になり，次を得ます：
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup
-- QUOTE.

/- OMIT:
This is the conceptual variant of the version of Lagrange theorem that we saw above.
Note this version makes no finiteness assumption.

OMIT. -/
/- TEXT:
これは上で見たLagrangeの定理の概念上の別バージョンです．このバージョンでは有限性の仮定が無いことに注意してください．

TEXT. -/
/- OMIT:
As an exercise for this section, let us build the action of a group on its subgroup by
conjugation, using our definition of ``conjugate`` from a previous exercise.
OMIT. -/
/- TEXT:
この節の演習問題として，前の演習問題の ``conjugate`` の定義を使って，共役による部分群への群作用を構築してみましょう．
BOTH: -/
-- QUOTE:
variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  simp [conjugate]
-- BOTH:

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact conjugate_one
-- BOTH:
  mul_smul := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro x y H
    ext z
    constructor
    · rintro ⟨h, h_in, rfl⟩
      use y*h*y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
      use h, h_in
      group
-- BOTH:

end GroupActions
-- QUOTE.

/- TEXT:
.. _quotient_groups:

TEXT. -/
/- OMIT:
Quotient groups
^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
商群
^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
In the above discussion of subgroups acting on groups, we saw the quotient ``G ⧸ H`` appear.
In general this is only a type. It can be endowed with a group structure such that the quotient
map is a group morphism if and only if ``H`` is a normal subgroup (and this group structure is
then unique).

OMIT. -/
/- TEXT:
上記の群に作用する部分群の議論では，商 ``G ⧸ H`` が登場しました．一般的にはこれは単なる型です． ``H`` が正規部分群である場合に限り，商写像が群の射となるような群構造を与えることができます（そしてこの群構造は一意です）．

TEXT. -/
/- OMIT:
The normality assumption is a type class ``Subgroup.Normal`` so that type class inference can use it
to derive the group structure on the quotient.
OMIT. -/
/- TEXT:
正規性の仮定は型クラス ``Subgroup.Normal`` であり，これによって型クラス推論が商の群構造を導き出すことができます．
BOTH: -/
-- QUOTE:
noncomputable section QuotientGroup

-- EXAMPLES:
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
-- QUOTE.

/- OMIT:
The universal property of quotient groups is accessed through ``QuotientGroup.lift``:
a group morphism ``φ`` descends to ``G ⧸ N`` as soon as its kernel contains ``N``.
OMIT. -/
/- TEXT:
商群の普遍性には ``QuotientGroup.lift`` を使ってアクセスすることができます：群の射 ``φ`` はその核が ``N`` を含むとすぐに ``G ⧸ N`` に誘導されます．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h
-- QUOTE.

/- OMIT:
The fact that the target group is called ``M`` is the above snippet is a clue that having a
monoid structure on ``M`` would be enough.

OMIT. -/
/- TEXT:
上記のコード片で対象の群が ``M`` と呼ばれているのは， ``M`` にモノイド構造があれば十分であることを示唆しています．

TEXT. -/
/- OMIT:
An important special case is when ``N = ker φ``. In that case the descended morphism is
injective and we get a group isomorphism onto its image. This result is often called
the first isomorphism theorem.
OMIT. -/
/- TEXT:
重要な特殊ケースは ``N = ker φ`` の場合です．この場合，誘導された射は単射であり，その像に対して群同型を得ます．この結果はしばしば第一同型定理と呼ばれます．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ
-- QUOTE.

/- OMIT:
Applying the universal property to a composition of a morphism ``φ : G →* G'``
with a quotient group projection ``Quotient.mk' N'``,
we can also aim for a morphism from ``G ⧸ N`` to ``G' ⧸ N'``.
The condition required on ``φ`` is usually formulated by saying "``φ`` should send ``N`` inside
``N'``." But this is equivalent to asking that ``φ`` should pull ``N'`` back over
``N``, and the latter condition is nicer to work with since the definition of pullback does not
involve an existential quantifier.
OMIT. -/
/- TEXT:
射 ``φ : G →* G'`` と商群の射影 ``Quotient.mk' N'`` との合成に普遍性を適用すると， ``G ⧸ N`` から ``G' ⧸ N'`` への射を求めることもできます．通常， ``φ`` に要求される条件は，「 ``φ`` は ``N`` の中に ``N`` を送るべきである」という形で形式化されます．しかし，これは ``φ`` が ``N`` を ``N`` の上に引き戻すべきであるということと等価であり，引き戻しの定義には存在量化子が含まれないため後者の条件の方が扱いやすいです．
EXAMPLES: -/
-- QUOTE:
example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h
-- QUOTE.

/- OMIT:
One subtle point to keep in mind is that the type ``G ⧸ N`` really depends on ``N``
(up to definitional equality), so having a proof that two normal subgroups ``N`` and ``M`` are equal
is not enough to make the corresponding quotients equal. However the universal properties does give
an isomorphism in this case.
OMIT. -/
/- TEXT:
1つ気に留めるべき微妙な点は型 ``G ⧸ N`` は ``N`` に（定義上の同値を除いて）本当に依存しているということであり，そのため2つの正規部分群 ``N`` と ``M`` が等しいことを証明するだけでは対応する商を等しくすることができません．しかし，普遍性はこの場合に同型を与えます．
EXAMPLES: -/
-- QUOTE:
example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
-- QUOTE.

/- OMIT:
As a final series of exercises for this section, we will prove that if ``H`` and ``K`` are disjoint
normal subgroups of a finite group ``G`` such that the product of their cardinalities is equal to
the cardinality of ``G``
then ``G`` is isomorphic to ``H × K``. Recall that disjoint in this context means ``H ⊓ K = ⊥``.

OMIT. -/
/- TEXT:
本節の最後の演習問題として，もし ``H`` と ``K`` が有限群 ``G`` のdisjointな正規部分群であり，それらの濃度の積が ``G`` の濃度と等しい場合， ``G`` は ``H × K`` と同型であることを証明します．この文脈でのdisjointとは ``H ⊓ K = ⊥`` を意味します．

TEXT. -/
/- OMIT:
We start with playing a bit with Lagrange's lemma, without assuming the subgroups are normal
or disjoint.
OMIT. -/
/- TEXT:
まずは部分群について正規であることとdisjointであることを仮定せずにLagrangeの補題を少し使ってみましょう．
BOTH: -/
-- QUOTE:
section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := calc
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by rw [← H.index_eq_card, H.index_mul_card]
    _                             = Nat.card K * Nat.card H := by rw [h', mul_comm]

  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
-- QUOTE.

/- OMIT:
From now on, we assume that our subgroups are normal and disjoint, and we assume the cardinality
condition. Now we construct the first building block of the desired isomorphism.
OMIT. -/
/- TEXT:
これ以降，部分群は正規かつdisjointであると仮定し，濃度の条件を仮定します．ここで，目的の同型の最初の構成要素を構築します．
BOTH: -/
-- QUOTE:
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ [Fintype G] (h : Disjoint H K) (h' : Nat.card G = Nat.card H * Nat.card K) : K ≃* G ⧸ H := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp [h]
  · symm
    exact aux_card_eq h'
-- QUOTE.

/- OMIT:
Now we can define our second building block.
We will need ``MonoidHom.prod``, which builds a morphism from ``G₀`` to ``G₁ × G₂`` out of
morphisms from ``G₀`` to ``G₁`` and ``G₂``.
OMIT. -/
/- TEXT:
これで2つ目の構成要素を定義できます．ここでは ``MonoidHom.prod`` が必要であり，これは ``G₀`` から ``G₁ × G₂`` への射を ``G₀`` から ``G₁`` と ``G₂`` への射に変換します．
BOTH: -/
-- QUOTE:
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' H)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H) _▸ h'), h']
-- QUOTE.

/- OMIT:
We are ready to put all pieces together.
OMIT. -/
/- TEXT:
これですべてをまとめる準備ができました．
EXAMPLES: -/
-- QUOTE:
#check MulEquiv.prodCongr

-- BOTH:
def finalIso : G ≃* H × K :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm

end
end QuotientGroup
-- QUOTE.

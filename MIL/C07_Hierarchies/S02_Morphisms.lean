import MIL.Common
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

/- OMIT:
Morphisms
---------

OMIT. -/
/- TEXT:
.. _section_hierarchies_morphisms:

射
---

TEXT. -/
/- OMIT:
So far in this chapter, we discussed how to create a hierarchy of mathematical structures.
But defining structures is not really completed until we have morphisms. There are two
main approaches here. The most obvious one is to define a predicate on functions.
OMIT. -/
/- TEXT:
この章ではここまで，数学的構造の階層を作る方法について述べてきました．しかし，構造を定義するには射が必要です．射の定義には2つのアプローチがあります．最も明白なのは，関数に対しての述語を定義することです．
BOTH: -/

-- QUOTE:
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- OMIT:
In this definition, it is a bit unpleasant to use a conjunction. In particular users
will need to remember the ordering we chose when they want to access the two conditions.
So we could use a structure instead.

OMIT. -/
/- TEXT:
この定義では，連言を使うことは少々好ましくありません．特に使う側にとっては，2つの条件にアクセスしたいときに条件の並び順を覚えておかなければなりません．そこで，上記の代わりに構造体を使うことができます．
BOTH: -/
-- QUOTE:
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- OMIT:
Once we are here, it is even tempting to make it a class and use the type class instance resolution
procedure to automatically infer ``isMonoidHom₂`` for complicated functions out of instances for
simpler functions. For instance a composition of monoid morphisms is a monoid morphism and this
seems like a useful instance. However such an instance would be very tricky for the resolution
procedure since it would need to hunt down ``g ∘ f`` everywhere. Seeing it failing in ``g (f x)``
would be very frustrating. More generally one must always keep in mind that recognizing which
function is applied in a given expression is a very difficult problem, called the "higher-order
unification problem". So Mathlib does not use this class approach.

OMIT. -/
/- TEXT:
ここまで来ると，上記をクラスにして，型クラスのインスタンス解決プロセスを使って，単純な関数のインスタンスから複雑な関数の ``isMonoidHom₂`` を自動的に推論できるようにしたくなるでしょう．例えばモノイドの射の合成はモノイドの射となり，これは上記クラスの有用なインスタンスのように思えるでしょう．しかし，このようなインスタンスは ``g ∘ f`` を至るところで探し出す必要があるので，解決プロセスにとっては非常に厄介です． ``g (f x)`` でさえも失敗してしまうので，使う人にとってはとてもイライラすることでしょう．より一般的には，与えられた式の中でどの関数が適用されているかを認識することは「高階ユニフィケーション問題」と呼ばれる非常に難しい問題であることを常に念頭に置く必要があります．そのため，Mathlibではこのようなクラスの使い方はされていません．

TEXT. -/
/- OMIT:
A more fundamental question is whether we use predicates as above (using either a ``def`` or a
``structure``) or use structures bundling a function and predicates. This is partly a psychological
issue. It is extremely rare to consider a function between monoids that is not a morphism.
It really feels like "monoid morphism" is not an adjective you can assign to a bare function,
it is a noun. On the other hand one can argue that a continuous function between topological spaces
is really a function that happens to be continuous. This is one reason why Mathlib has a
``Continuous`` predicate. For instance you can write:

OMIT. -/
/- TEXT:
より根本的な問題として，上記のように述語を使うか（ ``def`` か ``structure`` のどちらでも），それとも関数と述語を束ねた構造体を使うのかということです．これは気持ちの問題でもあります．射ではないモノイド間の関数を考えることは非常にまれです．「モノイドの射」は普通の関数につけられる形容詞ではなく，名詞なのです．一方で位相空間の間の連続関数は，考えていた対象の関数がたまたま連続だったと主張することもできます．これがMathlibに ``Continuous`` という述語がある理由です．例えば次のように書くことができます:
BOTH: -/
-- QUOTE:
example : Continuous (id : ℝ → ℝ) := continuous_id
-- QUOTE.
/- OMIT:
We still have bundles continuous functions, which are convenient for instance to put a topology
on a space of continuous functions, but they are not the primary tool to work with continuity.

OMIT. -/
/- TEXT:
連続関数のあつまりは，例えば連続関数の空間に位相を置くのに便利ですが，連続性を扱う主要な道具ではありません．

TEXT. -/
/- OMIT:
By contrast, morphisms between monoids (or other algebraic structures) are bundled as in:

OMIT. -/
/- TEXT:
これとは対照的に，モノイド（あるいは他の代数的構造）間の射は以下のようにまとめられます:
BOTH: -/
-- QUOTE:
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- OMIT:
Of course we don't want to type ``toFun`` everywhere so we register a coercion using
the ``CoeFun`` type class. Its first argument is the type we want to coerce to a function.
The second argument describes the target function type. In our case it is always ``G → H``
for every ``f : MonoidHom₁ G H``. We also tag ``MonoidHom₁.toFun`` with the ``coe`` attribute to
make sure it is displayed almost invisibly in the tactic state, simply by a ``↑`` prefix.

OMIT. -/
/- TEXT:
もちろん，どこでも ``toFun`` を打ち込みたいわけではないので， ``CoeFun`` タイプクラスを使って型強制を登録します．最初の引数は関数に強制したい型です．第2引数には対照となる関数の型を指定します．この場合，すべての ``f : MonoidHom₁ G H`` に対して常に ``G → H`` とします．また， ``MonoidHom₁.toFun`` には ``coe`` 属性のタグを付け， ``↑`` 接頭辞をつけるだけでタクティクモードではほとんど ``toFun`` の存在が見えないようになるようにしています．
BOTH: -/
-- QUOTE:
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
-- QUOTE.

/- OMIT:
Let us check we can indeed apply a bundled monoid morphism to an element.

OMIT. -/
/- TEXT:
モノイドの射のあつまりを要素に適用できることを確認してみましょう．
BOTH: -/

-- QUOTE:
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one
-- QUOTE.
/- OMIT:
We can do the same with other kind of morphisms until we reach ring morphisms.

OMIT. -/
/- TEXT:
他の射についても環の射についてまでは同じことができます．
BOTH: -/

-- QUOTE:
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

-- QUOTE.

/- OMIT:
There are a couple of issues about this approach. A minor one is we don't quite know where to put
the ``coe`` attribute since the ``RingHom₁.toFun`` does not exist, the relevant function is
``MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁`` which is not a declaration that can be tagged with an
attribute (but we could still define a ``CoeFun  (RingHom₁ R S) (fun _ ↦ R → S)`` instance).
A much more important one is that lemmas about monoid morphisms won't directly apply
to ring morphisms. This leaves the alternative of either juggling with ``RingHom₁.toMonoidHom₁``
each time we want to apply a monoid morphism lemma or restate every such lemmas for ring morphisms.
Neither option is appealing so Mathlib uses a new hierarchy trick here. The idea is to define
a type class for objects that are at least monoid morphisms, instantiate that class with both monoid
morphisms and ring morphisms and use it to state every lemma. In the definition below,
``F`` could be ``MonoidHom₁ M N``, or ``RingHom₁ M N`` if ``M`` and ``N`` have a ring structure.

OMIT. -/
/- TEXT:
この方法にはいくつか問題があります．そのうちの些細なものとして， ``RingHom₁.toFun`` が存在しないため， ``coe`` 属性をどこに置けばいいのかよくわからないことです．対応する関数は ``MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁`` ですが，これは属性タグを付けられる宣言ではありません．（ただ ``CoeFun  (RingHom₁ R S) (fun _ ↦ R → S)`` インスタンスを定義することはできます．）もっと重要なのは，モノイドの射に関する補題は環の射には直接適用できないということです．このため，モノイドの射の補題を適用しようとするたびに， ``RingHom₁.toMonoidHom₁`` と格闘するか，環の射の補題をすべて書き直すかのどちらかしかありません．どちらの選択肢も魅力的ではないため，Mathlibはここで新しい階層の技法を使います．そのアイデアは，少なくともモノイド射であるオブジェクトのための型クラスを定義し，そのクラスをモノイドの射と環の射の両方でインスタンス化し，すべての補題を記述するために使うというものです．以下の定義では， ``F`` は ``MonoidHom₁ M N`` であり，また ``M`` と ``N`` が環構造を持つ場合は ``RingHom₁ M N`` でもあります．
BOTH: -/

-- QUOTE:
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
-- QUOTE.

/- OMIT:
However there is a problem with the above implementation. We haven't registered a coercion to
function instance yet. Let us try to do it now.

OMIT. -/
/- TEXT:
しかし，上記の実装には問題があります．まだ関数インスタンスへの型強制が登録されていません．これをやってみましょう．
BOTH: -/

-- QUOTE:
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- QUOTE.

/- OMIT:
Making the an instance would be bad. When faced with something like ``f x`` where the type of ``f``
is not a function type, Lean will try to find a ``CoeFun`` instance to coerce ``f`` into a function.
The above function has type:
``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)``
so, when it trying to apply it, it wouldn't be a priori clear to Lean in which order the unknown
types ``M``, ``N`` and ``F`` should be inferred. This is a kind of bad instance that is slightly
different from the one we saw already, but it boils down to the same issue: without knowing ``M``,
Lean would have to search for a monoid instance on an unknown type, hence hopelessly try *every*
monoid instance in the database. If you are curious to see the effect of such an instance you
can type ``set_option synthInstance.checkSynthOrder false in`` on top of the above declaration,
replace ``def badInst`` with ``instance``, and look for random failures in this file.

OMIT. -/
/- TEXT:
このようなインスタンスの作成はよくありません． ``f`` が関数の型ではない場合に ``f x`` という式に遭遇した時，Leanは ``f`` を関数に変換するために ``CoeFun`` インスタンスを探そうとします．上記の関数の型は ``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)`` となり，したがってこれを適用しようとすると，未知の型 ``M`` と ``N`` ， ``F`` がどの順番で推論されるべきかLeanにとっては先験的に明らかではありません．これは前節で見た悪いインスタンスの種類とはまた少し違うものですが，同じ問題に帰着します． ``M`` のインスタンスがわからないと，Leanは未知の型のモノイドインスタンスを探さなければならず，データベース内の **すべての** モノイドインスタンスを試すことになります．このようなインスタンスの効果を見たい場合は，上記の宣言の上に ``set_option synthInstance.checkSynthOrder false in`` と入力し， ``def badInst`` を ``instance`` に置き換えると，このファイル中であちこち失敗することを確認できるでしょう．

TEXT. -/
/- OMIT:
Here the solution is easy, we need to tell Lean to first search what is ``F`` and then deduce ``M``
and ``N``. This is done using the ``outParam`` function. This function is defined as the identity
function, but is still recognized by the type class machinery and triggers the desired behavior.
Hence we can retry defining our class, paying attention to the ``outParam`` function:
OMIT. -/
/- TEXT:
この問題の解決は簡単です．まず ``F`` がなんであるかを検索し，次に ``M`` と ``N`` を推論するようにLeanに指示すればよいのです．これは ``outParam`` 関数を使って行います．この関数は恒等関数として定義されていますが，型クラスの仕組みによって認識され，目的の動作を引き起こします．したがって， ``outParam`` 関数に注意しながら，クラスの定義をやり直すことができます．
BOTH: -/

-- QUOTE:
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
-- QUOTE.

/- OMIT:
Now we can proceed with our plan to instantiate this class.

OMIT. -/
/- TEXT:
これでこのクラスをインスタンス化する方針を進めることができます．
BOTH: -/

-- QUOTE:
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.

/- OMIT:
As promised every lemma we prove about ``f : F`` assuming an instance of ``MonoidHomClass₁ F`` will
apply both to monoid morphisms and ring morphisms.
Let us see an example lemma and check it applies to both situations.
OMIT. -/
/- TEXT:
お約束したように， ``MonoidHomClass₁ F`` のインスタンスを仮定して， ``f : F`` について証明するすべての補題は，モノイドの射と環の射の両方に適用できます．補題の例を見て，両方の状況に当てはまることを確認してみましょう．
BOTH: -/

-- QUOTE:
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- QUOTE.

/- OMIT:
At first sight, it may look like we got back to our old bad idea of making ``MonoidHom₁`` a class.
But we haven't. Everything is shifted one level of abstraction up. The type class resolution
procedure won't be looking for functions, it will be looking for either
``MonoidHom₁`` or ``RingHom₁``.

OMIT. -/
/- TEXT:
一見すると， ``MonoidHom₁`` をクラスにするという昔の悪いアイデアに戻ったように見えるかもしれません．しかしそうではありません．すべて抽象度が1つ上がっているのです．型クラス解決プロセスは関数を探すのではなく， ``MonoidHom₁`` か ``RingHom₁`` のどちらかを探すことに成ります．

TEXT. -/
/- OMIT:
One remaining issue with our approach is the presence of repetitive code around the ``toFun``
field and the corresponding ``CoeFun`` instance and ``coe`` attribute. It would also be better
to record that this pattern is used only for function with extra properties, meaning that the
coercion to functions should be injective. So Mathlib adds one more layer of abstraction with
the base class ``FunLike``. Let us redefine our ``MonoidHomClass`` on top of this base layer.

OMIT. -/
/- TEXT:
本書でのアプローチで残っている問題は， ``toFun`` フィールドとそれに対応する ``CoeFun`` インスタンスと ``coe`` 属性の周りに繰り返しコードが存在することです．また，このパターンは余分なプロパティを持つ関数にのみ使用され，関数への型強制は単射的であるべきだということを記録しておいたほうが良いでしょう．このために，Mathlibは基底クラス ``FunLike`` で抽象化のレイヤーを1つ増やしています．この基底クラスの上に ``MonoidHomClass`` を再定義してみましょう．
BOTH: -/

-- QUOTE:
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul
-- QUOTE.

/- OMIT:
Of course the hierarchy of morphisms does not stop here. We could go on and define a class
``RingHomClass₃`` extending ``MonoidHomClass₃`` and instantiate it on ``RingHom`` and
then later on ``AlgebraHom`` (algebras are rings with some extra structure). But we've
covered the main formalization ideas used in Mathlib for morphisms and you should be ready
to understand how morphisms are defined in Mathlib.

OMIT. -/
/- TEXT:
もちろん射の階層はここで終わりません．さらに続けて ``MonoidHomClass₃`` を特殊化した ``RingHomClass₃`` クラスを定義し，それを ``RingHom`` にインスタンス化し，さらに ``AlgebraHom`` にインスタンス化することもできます．（代数環は環に特別な構造を加えたものです．）しかし，Mathlibで使用される射の主な形式化のアイデアをカバーしたので，Mathlibで射がどのように定義されるかを理解する準備はできているはずです．

TEXT. -/
/- OMIT:
As an exercise, you should try to define your class of bundled order-preserving function between
ordered types, and then order preserving monoid morphisms. This is for training purposes only.
Like continuous functions, order preserving functions are primarily unbundled in Mathlib where
they are defined by the ``Monotone`` predicate. Of course you need to complete the class
definitions below.
OMIT. -/
/- TEXT:
演習問題として，順序型の間の順序を保つ関数を集めたクラスと，順序を保つモノイドの射を定義してみましょう．これは練習のためだけのものです．連続関数と同様に，順序を保つ関数はMathlibではとくにまとめられておらず， ``Monotone`` 述語によって定義されています．この演習を達成するにはもちろん，以下のクラス定義を完成させる必要があります．
BOTH: -/

-- QUOTE:
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]
-- SOLUTIONS:
extends FunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'
-- BOTH:

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
-- SOLUTIONS:
  coe := OrderPresHom.toFun
  coe_injective' := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
-- SOLUTIONS:
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' := OrderPresMonoidHom.ext
  le_of_le := fun f ↦ f.toOrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
/- EXAMPLES:
  := sorry
SOLUTIONS: -/
where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.

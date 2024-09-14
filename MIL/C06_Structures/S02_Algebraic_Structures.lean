import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

/- OMIT:
Algebraic Structures
--------------------

OMIT. -/
/- TEXT:
.. _section_algebraic_structures:

代数構造
---------

TEXT. -/
/- OMIT:
To clarify what we mean by the phrase *algebraic structure*,
it will help to consider some examples.

OMIT. -/
/- TEXT:
一口に「代数構造」といっても本書に置いて何を意味するかということを明確にするために，ここでいくつか例を挙げましょう．

TEXT. -/
/- OMIT:
#. A *partially ordered set* consists of a set :math:`P` and
   a binary relation :math:`\le` on :math:`P` that is transitive
   and reflexive.

OMIT. -/
/- TEXT:
#. **半順序集合** （partially ordered set）は集合 :math:`P` と推移律と反対称律を持った :math:`P` 上の二項演算子 :math:`\le` からなります．

TEXT. -/
/- OMIT:
#. A *group* consists of a set :math:`G` with an associative
   binary operation, an identity element
   :math:`1`, and a function :math:`g \mapsto g^{-1}` that returns
   an inverse for each :math:`g` in :math:`G`.
   A group is *abelian* or *commutative* if the operation is commutative.

OMIT. -/
/- TEXT:
#. **群** （group）は集合 :math:`G` に結合的な二項演算子と単位元 :math:`1` ， :math:`G` の各 :math:`g` の逆元を返す関数 :math:`g \mapsto g^{-1}` を加えたものから成ります．群が **アーベル** （abelian）もしくは **可換** （commutative）であるとは二項演算子が可換であることを指します．

TEXT. -/
/- OMIT:
#. A *lattice* is a partially ordered set with meets and joins.

OMIT. -/
/- TEXT:
#. **束** （lattice）は交わりと結びを備えた半順序集合です．

TEXT. -/
/- OMIT:
#. A *ring* consists of an (additively written) abelian group
   :math:`(R, +, 0, x \mapsto -x)`
   together with an associative multiplication operation
   :math:`\cdot` and an identity :math:`1`,
   such that multiplication distributes over addition.
   A ring is *commutative* if the multiplication is commutative.

OMIT. -/
/- TEXT:
#. **環** （ring）は（加法的と言われる）アーベル群 :math:`(R, +, 0, x \mapsto -x)` に加法上に分配される結合的な乗法の演算子 :math:`\cdot` と単位元 :math:`1` を加えたものから成ります．環が **可換** であるとは乗法が可換であることを指します．

TEXT. -/
/- OMIT:
#. An *ordered ring* :math:`(R, +, 0, -, \cdot, 1, \le)` consists of a ring
   together with a partial order on its elements, such that :math:`a \le b` implies
   :math:`a + c \le b + c` for every :math:`a`, :math:`b`, and :math:`c` in :math:`R`,
   and :math:`0 \le a` and :math:`0 \le b` implies :math:`0 \le a b` for
   every :math:`a` and :math:`b` in :math:`R`.

OMIT. -/
/- TEXT:
#. **順序環** （ordered ring） :math:`(R, +, 0, -, \cdot, 1, \le)` は環に， :math:`a + c \le b + c` が :math:`R` のすべての元 :math:`a` ， :math:`b` ， :math:`c` に対して成り立ち，また :math:`R` のすべての元 :math:`a` と :math:`b` が :math:`0 \le a` と :math:`0 \le b` を満たすときに :math:`0 \le a b` を成り立たせるような半順序を備えたものです．

TEXT. -/
/- OMIT:
#. A *metric space* consists of a set :math:`X` and a function
   :math:`d : X \times X \to \mathbb{R}` such that the following hold:

   - :math:`d(x, y) \ge 0` for every :math:`x` and :math:`y` in :math:`X`.
   - :math:`d(x, y) = 0` if and only if :math:`x = y`.
   - :math:`d(x, y) = d(y, x)` for every :math:`x` and :math:`y` in :math:`X`.
   - :math:`d(x, z) \le d(x, y) + d(y, z)` for every :math:`x`, :math:`y`, and
     :math:`z` in :math:`X`.

OMIT. -/
/- TEXT:
#. **距離空間** （metric space）は集合 :math:`X` と以下を満たすような関数 :math:`d : X \times X \to \mathbb{R}` から構成されます．

   - :math:`X` の各 :math:`x` と :math:`y` に対して :math:`d(x, y) \ge 0` となる．
   - :math:`d(x, y) = 0` となるのは :math:`x = y` かつそのときに限る．
   - :math:`X` の各 :math:`x` と :math:`y` に対して :math:`d(x, y) = d(y, x)` が成り立つ．
   - :math:`X` の各 :math:`x` と :math:`y` ， :math:`z` に対して :math:`d(x, z) \le d(x, y) + d(y, z)` が成り立つ．

TEXT. -/
/- OMIT:
#. A *topological space* consists of a set :math:`X` and a collection :math:`\mathcal T`
   of subsets of :math:`X`, called the *open subsets of* :math:`X`, such that
   the following hold:

   - The empty set and :math:`X` are open.
   - The intersection of two open sets is open.
   - An arbitrary union of open sets is open.

OMIT. -/
/- TEXT:
#. **位相空間** （topological space）は集合 :math:`X` と， :math:`X` の **開集合** （open subsets）と呼ばれる以下を満たすような :math:`X` の部分集合のあつまり :math:`\mathcal T` から構成されます．

   - 空集合と :math:`X` は開集合である．
   - 2つの開集合の交わりは開集合である．
   - 任意の数の開集合の合併は開集合である．

TEXT. -/
/- OMIT:
In each of these examples, the elements of the structure belong to a
set, the *carrier set*,
that sometimes stands proxy for the entire structure.
For example, when we say "let :math:`G` be a group" and then
"let :math:`g \in G`," we are using :math:`G` to stand for both
the structure and its carrier.
Not every algebraic structure is associated with a single carrier set in this way.
For example, a *bipartite graph* involves a relation between two sets,
as does a *Galois connection*,
A *category* also involves two sets of interest, commonly called the *objects*
and the *morphisms*.

OMIT. -/
/- TEXT:
これらの例では，各構造の元は **台集合** （carrier set）と呼ばれる集合に属し，この集合でその構造全体のことを指す場合もあります．例えば「 :math:`G` が群である」と言ってから「 :math:`g \in G` 」と言う時，私達は :math:`G` をそれぞれ構造と台集合の意味として使っています．すべての代数構造がこのように1つの台集合に関連付けられるわけではありません．例えば **2部グラフ** （bipartite graph）には **ガロア接続** （Galois connection）のように2つの集合間の関係がふくまれます． **圏** （category）も一般に **対象** （object）と **射** （morphism）と呼ばれる2つの集合を中心として構成されます．

TEXT. -/
/- OMIT:
The examples indicate some of the things that a proof assistant has to do
in order to support algebraic reasoning.
First, it needs to recognize concrete instances of structures.
The number systems :math:`\mathbb{Z}`, :math:`\mathbb{Q}`,
and :math:`\mathbb{R}` are all ordered rings,
and we should be able to apply a generic theorem about ordered rings
in any of these instances.
Sometimes a concrete set may be an instance of a structure in more than one way.
For example, in addition to the usual topology on :math:`\mathbb{R}`,
which forms the basis for real analysis,
we can also consider the *discrete* topology on :math:`\mathbb{R}`,
in which every set is open.

OMIT. -/
/- TEXT:
これらの例は代数的推論について証明支援系がサポートするにあたって必要なポイントをいくつか示しています．まず，構造の具体例を認識している必要があります．数体系 :math:`\mathbb{Z}` と :math:`\mathbb{Q}` ， :math:`\mathbb{R}` はすべて順序環であり，順序環に関する一般的な定理をこれらのインスタンスに適用出来なければなりません．ある集合を何かしらの構造のインスタンスにする場合，複数の方法が存在する場合があります．例えば，実解析の基礎となる :math:`\mathbb{R}` 上の通常の位相構造に加え，すべての集合が開である :math:`\mathbb{R}` 上の **離散** （discrete）位相構造を考えることができます．

TEXT. -/
/- OMIT:
Second, a proof assistant needs to support generic notation on structures.
In Lean, the notation ``*``
is used for multiplication in all the usual number systems,
as well as for multiplication in generic groups and rings.
When we use an expression like ``f x * y``,
Lean has to use information about the types of ``f``, ``x``, and ``y``
to determine which multiplication we have in mind.

OMIT. -/
/- TEXT:
第二に，証明支援系は構造上の一般的な表記法をサポートする必要があります．Leanでは ``*`` という記法は通常の数体系での乗算に使われるだけでなく，一般的な群や環での乗算にも使われます．例えば ``f x * y`` のような式を取り扱う際には，Leanは ``f`` と ``x`` ， ``y`` の型に関する情報を用いて，どの乗法を考えているかを判断しなければなりません．

TEXT. -/
/- OMIT:
Third, it needs to deal with the fact that structures can inherit
definitions, theorems, and notation from other structures in various ways.
Some structures extend others by adding more axioms.
A commutative ring is still a ring, so any definition
that makes sense in a ring also makes sense in a commutative ring,
and any theorem that holds in a ring also holds in a commutative ring.
Some structures extend others by adding more data.
For example, the additive part of any ring is an additive group.
The ring structure adds a multiplication and an identity,
as well as axioms that govern them and relate them to the additive part.
Sometimes we can define one structure in terms of another.
Any metric space has a canonical topology associated with it,
the *metric space topology*, and there are various topologies that can be
associated with any linear ordering.

OMIT. -/
/- TEXT:
第三に，構造が他の構造から定義と定理，表記法を様々な方法で継承できるという事実に対処出来る必要があります．構造によっては公理を追加することで他の構造を拡張するものもあります．可換環は環でもあるので，環で成り立つ定義は可換環でも成り立ち，環で成り立つ定理は可換環でも成り立ちます．構造によってはデータを追加することで他の構造を拡張することもあります．例えば環の加法についての部分は加法群です．環の構造はこの加法的な部分に乗法とその単位元，およびそれらを支配・関連する公理を追加します．ある構造を別の構造で定義出来ることもあります．任意の距離空間にはそれに関連する正準位相である **距離空間位相** （metric space topology）があり，任意の線形順序に関連付けることができる様々な位相があります．

TEXT. -/
/- OMIT:
Finally, it is important to keep in mind that mathematics allows us to
use functions and operations to define structures in the same way we
use functions and operations to define numbers.
Products and powers of groups are again groups.
For every :math:`n`, the integers modulo :math:`n` form a ring,
and for every :math:`k > 0`, the :math:`k \times k` matrices of polynomials
with coefficients in that ring again form a ring.
Thus we can calculate with structures just as easily as we can calculate
with their elements.
This means that algebraic structures lead dual lives in mathematics,
as containers for collections of objects and as objects in their own right.
A proof assistant has to accommodate this dual role.

OMIT. -/
/- TEXT:
最後に，数学において数を定義するために関数や演算を使うのと同じように，構造を定義するために関数や演算を使うことができるということを覚えておくことが重要です．群の積と累乗もまた群です．すべての :math:`n` に対して， :math:`n` を法として合同な整数は環を形成し，すべての :math:`k > 0` に対して，その環に係数を持つ多項式の :math:`k \times k` 行列もまた環を形成します．このように，構造を使って計算することは，その要素を使って計算することと同じくらい簡単です．このことは代数的構造が数学に置いて対象のあつまりのためのコンテナとしてと，またそれ自身の対象としてとの二重の生活を送っていることを意味します．証明支援系はこの二重の役割に対応しなければなりません．

TEXT. -/
/- OMIT:
When dealing with elements of a type that has an algebraic structure
associated with it,
a proof assistant needs to recognize the structure and find the relevant
definitions, theorems, and notation.
All this should sound like a lot of work, and it is.
But Lean uses a small collection of fundamental mechanisms to
carry out these tasks.
The goal of this section is to explain these mechanisms and show you
how to use them.

OMIT. -/
/- TEXT:
代数的構造を持つ型の要素を扱う時，証明支援系はその構造を認識し，関連する定義と定理・記法を見つける必要があります．この一連の流れはとても大変な作業のように聞こえるでしょう．しかし，Leanはこれらのタスクを実行するためには基本的な仕組みのうちのわずかなものしか使用しません．この節の目標はこれらのメカニズムを説明し，それらの使い方を紹介することです．

TEXT. -/
/- OMIT:
The first ingredient is almost too obvious to mention:
formally speaking, algebraic structures are structures in the sense
of :numref:`section_structures`.
An algebraic structure is a specification of a bundle of data satisfying
some axiomatic hypotheses, and we saw in :numref:`section_structures` that
this is exactly what the ``structure`` command is designed to accommodate.
It's a marriage made in heaven!

OMIT. -/
/- TEXT:
最初の素材はわざわざ言うほどではないほど明白なものです:形式的に言えば，代数構造は :numref:`section_structures` の意味での構造です．代数構造はいくつかの公理的な仮説を満たすデータを束ねたものの仕様であり，これこそが ``structure`` コマンドが対応するように設計されていることを :numref:`section_structures` で見ました．まさにこれ以上無いほどのお似合いの関係です！

TEXT. -/
/- OMIT:
Given a data type ``α``, we can define the group structure on ``α``
as follows.
OMIT. -/
/- TEXT:
与えられた ``α`` 型について，群の構造を以下のように ``α`` 上に定義することができます．
EXAMPLES: -/
-- QUOTE:
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
-- QUOTE.

-- OMIT: TODO: explain the extends command later, and also redundant inheritance
/- OMIT:
Notice that the type ``α`` is a *parameter* in the definition of ``group₁``.
So you should think of an object ``struc : Group₁ α`` as being
a group structure on ``α``.
We saw in :numref:`proving_identities_in_algebraic_structures`
that the counterpart ``mul_inv_cancel`` to ``inv_mul_cancel``
follows from the other group axioms, so there is no need
to add it to the definition.

OMIT. -/
/- TEXT:
ここで型 ``α`` は ``group₁`` の定義における **パラメータ** （parameter）であることに注意してください．したがってオブジェクト ``struc : Group₁ α`` は ``α`` 上の群構造であると考えると良いでしょう．他の群の公理から ``mul_left_inv`` と対になる ``mul_right_inv`` が成り立つことは :numref:`proving_identities_in_algebraic_structures` で見たため，定義に追加する必要はありません．

TEXT. -/
/- OMIT:
This definition of a group is similar to the definition of ``Group`` in
Mathlib,
and we have chosen the name ``Group₁`` to distinguish our version.
If you write ``#check Group`` and ctrl-click on the definition,
you will see that the Mathlib version of ``Group`` is defined to
extend another structure; we will explain how to do that later.
If you type ``#print Group`` you will also see that the Mathlib
version of ``Group`` has a number of extra fields.
For reasons we will explain later, sometimes it is useful to add
redundant information to a structure,
so that there are additional fields for objects and functions
that can be defined from the core
data. Don't worry about that for now.
Rest assured that our simplified version ``Group₁`` is
morally the same as the definition of a group that Mathlib uses.

OMIT. -/
/- TEXT:
この群の定義はMathlibの ``Group`` の定義と似ているため，区別するために本書のバージョンは ``Group₁`` という名前にしました．もし ``#check Group`` と書いてその定義をctrlを押しながらクリックすると，Mathlib版の ``Group`` が別の構造体を拡張するように定義されていることがわかります．また， ``#print Group`` と入力すると，Mathlibバージョンの ``Group`` にはいくつかのフィールドが追加されていることがわかります．あとで説明しますが，構造体に冗長な情報を追加して，コアデータから定義できるオブジェクトや関数のフィールドを追加しておくと便利な場合があります．今は気にしないでください．本書の簡略版 ``Group₁`` はMathlibが使用している群の定義と概念上は同じですのでご安心ください．

TEXT. -/
/- OMIT:
It is sometimes useful to bundle
the type together with the structure, and Mathlib also
contains a definition of a ``GroupCat`` structure that is equivalent to
the following:
OMIT. -/
/- TEXT:
構造体に型を組み合わせることが便利である場合がときどきあるため，Mathlibは以下のような ``GroupCat`` 構造体の定義を有しています:
EXAMPLES: -/
-- QUOTE:
structure Group₁Cat where
  α : Type*
  str : Group₁ α
-- QUOTE.

/- OMIT:
The Mathlib version is found in ``Mathlib.Algebra.Category.GroupCat.Basic``,
and you can ``#check`` it if you add this to the imports at the
beginning of the examples file.

OMIT. -/
/- TEXT:
Mathlib版は ``Mathlib.Algebra.Category.GroupCat.Basic`` にあり，これをサンプルファイルの最初のimportに追加すれば ``#check`` することができます．

TEXT. -/
/- OMIT:
For reasons that will become clearer below, it is more often
useful to keep the type ``α`` separate from the structure ``Group α``.
We refer to the two objects together as a *partially bundled structure*,
since the representation combines most, but not all, of the components
into one structure. It is common in Mathlib
to use capital roman letters like ``G`` for a type
when it is used as the carrier type for a group.

OMIT. -/
/- TEXT:
理由は後ほど明らかに成りますが，型 ``α`` と構造体 ``Group α`` を分けておいたほうが便利なことが多いです．このような2つの対象を合わせて **部分的に束ねられた構造体** （partially bundled structure）と呼びます．これは全てではないですが，多くの部分の成分を一つの構造に組み込む表現になっているからです．Mathlibでは群の台の型として使用する場合，型名としては大文字のアルファベット ``G`` を使用するのが一般的です．

TEXT. -/
/- OMIT:
Let's construct a group, which is to say, an element of the ``Group₁`` type.
For any pair of types ``α`` and ``β``, Mathlib defines the type ``Equiv α β``
of *equivalences* between ``α`` and ``β``.
Mathlib also defines the suggestive notation ``α ≃ β`` for this type.
An element ``f : α ≃ β`` is a bijection between ``α`` and ``β``
represented by four components:
a function ``f.toFun`` from ``α`` to ``β``,
the inverse function ``f.invFun`` from ``β`` to ``α``,
and two properties that specify these functions are indeed inverse
to one another.
OMIT. -/
/- TEXT:
さて，群を，つまり ``Group₁`` 型の元を構成してみましょう．型 ``α`` と ``β`` の任意のペアに対して，Mathlibは ``α`` と ``β`` の間の **同値** （equivalences）を示す型 ``Equiv α β`` を定義しています．また，Mathlibはこの型に対して ``α ≃ β`` という示唆的な記法を定義しています．この型の要素 ``f : α ≃ β`` は ``α`` と ``β`` の間の全単射で，4つの要素で表現されます: ``α`` から ``β`` への関数 ``f.toFun`` ， ``β`` から ``α`` への逆関数 ``f.invFun`` ，そしてこれらの関数が互いに逆であることを示す2つの性質です．
EXAMPLES: -/
section
-- QUOTE:
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)
-- QUOTE.

/- OMIT:
Notice the creative naming of the last three constructions. We think of the
identity function ``Equiv.refl``, the inverse operation ``Equiv.symm``,
and the composition operation ``Equiv.trans`` as explicit evidence
that the property of being in bijective correspondence is an equivalence relation.

OMIT. -/
/- TEXT:
最後の3つの構文の特徴的な命名に注目してください．恒等関数 ``Equiv.refl`` ，逆演算 ``Equiv.symm`` ，合成演算 ``Equiv.trans`` は全単射という性質が同値関係であることの明示的な証拠であると考えられます．

TEXT. -/
/- OMIT:
Notice also that ``f.trans g`` requires composing the forward functions
in reverse order. Mathlib has declared a *coercion* from ``Equiv α β``
to the function type ``α → β``, so we can omit writing ``.toFun``
and have Lean insert it for us.
OMIT. -/
/- TEXT:
また， ``f.tans g`` は逆順に前方の関数を合成する必要があることにも注意してください．Mathlibは ``Equiv α β`` から関数型 ``α → β`` への **型の強制** （coercion）を宣言しているため， ``.toFun`` を書くのを省略して，代わりにLeanに入れてもらうことができます．
EXAMPLES: -/
-- QUOTE:
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl
-- QUOTE.

end

/- OMIT:
Mathlib also defines the type ``perm α`` of equivalences between
``α`` and itself.
OMIT. -/
/- TEXT:
また，Mathlibは ``α`` とそれ自身との間の同値性を示す ``perm α`` 型も定義しています．
EXAMPLES: -/
-- QUOTE:
example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl
-- QUOTE.

/- OMIT:
It should be clear that ``Equiv.Perm α`` forms a group under composition
of equivalences. We orient things so that ``mul f g`` is
equal to ``g.trans f``, whose forward function is ``f ∘ g``.
In other words, multiplication is what we ordinarily think of as
composition of the bijections. Here we define this group:
OMIT. -/
/- TEXT:
この ``Equiv.Perm α`` が同値の合成で群を形成することは明らかでしょう． ``mul f g`` は ``g.trans f`` と等しく，これで導かれる関数は ``f ∘ g`` です．言い換えれば，乗法は通常，全単射の合成と考えられているもののことです．ここでこの群を定義します:
EXAMPLES: -/
-- QUOTE:
def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- OMIT:
In fact, Mathlib defines exactly this ``Group`` structure on ``Equiv.Perm α``
in the file ``GroupTheory.Perm.Basic``.
As always, you can hover over the theorems used in the definition of
``permGroup`` to see their statements,
and you can jump to their definitions in the original file to learn
more about how they are implemented.

OMIT. -/
/- TEXT:
実際，Mathlibは ``GroupTheory.Perm.Basic`` というファイルの ``Equiv.Perm α`` でまさにこの ``Group`` 構造を定義しています．いつものように， ``permGroup`` の定義で使用されている定理にカーソルを合わせるとその命題を見ることができ，その元ファイルの定義元に飛んでどのように実装されているか見ることができます．

TEXT. -/
/- OMIT:
In ordinary mathematics, we generally think of notation as
independent of structure.
For example, we can consider groups :math:`(G_1, \cdot, 1, \cdot^{-1})`,
:math:`(G_2, \circ, e, i(\cdot))`, and :math:`(G_3, +, 0, -)`.
In the first case, we write the binary operation as :math:`\cdot`,
the identity at :math:`1`, and the inverse function as :math:`x \mapsto x^{-1}`.
In the second and third cases, we use the notational alternatives shown.
When we formalize the notion of a group in Lean, however,
the notation is more tightly linked to the structure.
In Lean, the components of any ``Group`` are named
``mul``, ``one``, and ``inv``,
and in a moment we will see how multiplicative notation is
set up to refer to them.
If we want to use additive notation, we instead use an isomorphic structure
``AddGroup`` (the structure underlying additive groups). Its components are named ``add``, ``zero``,
and ``neg``, and the associated notation is what you would expect it to be.

OMIT. -/
/- TEXT:
通常の数学では，表記法は構造に依存しないと考えるのが一般的です．例えば，群として :math:`(G_1, \cdot, 1, \cdot^{-1})` と :math:`(G_2, \circ, e, i(\cdot))` ， :math:`(G_3, +, 0, -)` を考えることが出来ます．最初のケースでは，二項演算を :math:`\cdot` と，単位元を :math:`1` ，逆関数を :math:`x \mapsto x^{-1}` と書きます．2番目と3番目のケースでは，同様にそれぞれ先程示した表記法を使用します．しかし，Leanで群の概念を形式化する場合，表記法は構造とより密接に結びつきます．Leanでは任意の ``Group`` の構成要素は ``mul`` と ``one`` ， ``inv`` という名付けられます．これらを参照するために乗法の表記がどのように設定されているかはこの後すぐ見ていきます．もし加法の表記を使いたい場合は，代わりに同型な構造体 ``AddGroup`` （加法群の基礎となる構造体）を使います．この構成要素は ``add`` と ``zero`` ， ``neg`` という名前で，関連する記法も加法に対して想像される通りのものです．

TEXT. -/
/- OMIT:
Recall the type ``Point`` that we defined in :numref:`section_structures`,
and the addition function that we defined there.
These definitions are reproduced in the examples file that accompanies
this section.
As an exercise, define an ``AddGroup₁`` structure that is similar
to the ``Group₁`` structure we defined above, except that it uses the
additive naming scheme just described.
Define negation and a zero on the ``Point`` data type,
and define the ``AddGroup₁`` structure on ``Point``.
OMIT. -/
/- TEXT:
:numref:`section_structures` で定義した ``Point`` 型とそこで定義した加算関数を思い出してください．これらの定義はこの節に紐付いているサンプルファイルで再定義しています．演習として，上で定義した ``Group₁`` 構造体に似た ``AddGroup₁`` 構造体を定義してみましょう．続いて ``Point`` データ型に逆元と0を定義し， ``Point`` に ``AddGroup₁`` 構造体を定義しましょう．
BOTH: -/
-- QUOTE:
structure AddGroup₁ (α : Type*) where
/- EXAMPLES:
  (add : α → α → α)
  -- fill in the rest
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

-- BOTH:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/- EXAMPLES:
def neg (a : Point) : Point := sorry

def zero : Point := sorry

def addGroupPoint : AddGroup₁ Point := sorry

SOLUTIONS: -/
def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

-- BOTH:
end Point
-- QUOTE.

/- OMIT:
We are making progress.
Now we know how to define algebraic structures in Lean,
and we know how to define instances of those structures.
But we also want to associate notation with structures
so that we can use it with each instance.
Moreover, we want to arrange it so that we can define an operation
on a structure and use it with any particular instance,
and we want to arrange it so that we can prove a theorem about
a structure and use it with any instance.

OMIT. -/
/- TEXT:
さて，だいぶLeanにおいての代数構造について習熟してきました．Leanで代数的構造を定義する方法とそれらの構造のインスタンスを定義する方法も学びました．しかし，それらのインスタンスで使用できるように，表記法を構造に関連付けたいでしょう．さらに，構造に対する演算を定義し，それを特定のインスタンスで使えるようにもしたいです．また，同様に構造に関する定理を証明し，それを任意のインスタンスで使えるようにもしたいです．

TEXT. -/
/- OMIT:
In fact, Mathlib is already set up to use generic group notation,
definitions, and theorems for ``Equiv.Perm α``.
OMIT. -/
/- TEXT:
実は，Mathlibはすでに ``Equiv.Perm α`` に対して一般的な群の表記，定義，定理を使うことができるように設定しています．
EXAMPLES: -/
section
-- QUOTE:
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g
-- QUOTE.

end

/- OMIT:
You can check that this is not the case for the additive group structure
on ``Point`` that we asked you to define above.
Our task now is to understand that magic that goes on under the hood
in order to make the examples for ``Equiv.Perm α`` work the way they do.

OMIT. -/
/- TEXT:
上で定義した ``Point`` 上の加法群構造ではこれらが使えないことを確認してみましょう．ここからの課題は ``Equiv.Perm α`` の例を同じように動作させるために，その背後で行われている仕組みを理解することです．

TEXT. -/
/- OMIT:
The issue is that Lean needs to be able to *find* the relevant
notation and the implicit group structure,
using the information that is found in the expressions that we type.
Similarly, when we write ``x + y`` with expressions ``x`` and ``y``
that have type ``ℝ``, Lean needs to interpret the ``+``
symbol as the relevant addition function on the reals.
It also has to recognize the type ``ℝ`` as an instance of a commutative ring,
so that all the definitions and theorems for a commutative ring are available.
For another example,
continuity is defined in Lean relative to any two topological spaces.
When we have ``f : ℝ → ℂ`` and we write ``Continuous f``, Lean has to find the
relevant topologies on ``ℝ`` and ``ℂ``.

OMIT. -/
/- TEXT:
問題は，Leanは私達が入力する式の中にある情報を使って関連する表記と暗黙の群構造を **見つける** ことが出来る必要がある，ということです．例えば， ``ℝ`` 型の ``x`` と ``y`` で ``x + y`` という式を書く時，Leanは ``+`` という記号を実数上の加算関数として解釈する必要があります．また，可換環の定義や定理をすべて利用できるように， ``ℝ`` 型を可換環のインスタンスとして認識する必要があります．別の例として，Leanにおいて連続性は2つの位相空間の関係として定義されます． ``f : ℝ → ℂ`` があり， ``Continuous f`` と書く時，Leanは ``ℝ`` と ``ℂ`` 上の関連する位相を見つけなければなりません．

TEXT. -/
/- OMIT:
The magic is achieved with a combination of three things.

OMIT. -/
/- TEXT:
この魔法は以下の3つのものの組み合わせで実現されています．

TEXT. -/
/- OMIT:
#. *Logic.* A definition that should be interpreted in any group takes, as
   arguments, the type of the group and the group structure as arguments.
   Similarly, a theorem about the elements of an arbitrary group
   begins with universal quantifiers over
   the type of the group and the group structure.

OMIT. -/
/- TEXT:
#. **論理** （Logic）．任意の群で解釈されるべき定義は，群の型と群構造を引数として取ります．同様に，任意の群の要素に関する定理は，群の型と群構造に対する普遍量化子から始まります．

TEXT. -/
/- OMIT:
#. *Implicit arguments.* The arguments for the type and the structure
   are generally left implicit, so that we do not have to write them
   or see them in the Lean information window. Lean fills the
   information in for us silently.

OMIT. -/
/- TEXT:
#. **暗黙的な引数** （Implicit arguments）．型と構造の引数は一般的には暗黙的なままにしておき，私達が書いたり，Leanの情報ウィンドウで見たりする必要がないようにします．Leanがこっそり情報を埋めてくれます．

TEXT. -/
/- OMIT:
#. *Type class inference.* Also known as *class inference*,
   this is a simple but powerful mechanism
   that enables us to register information for Lean to use later on.
   When Lean is called on to fill in implicit arguments to a
   definition, theorem, or piece of notation,
   it can make use of information that has been registered.

OMIT. -/
/- TEXT:
#. **型クラスの推論** （Type class inference）．もしくは **クラス推論** （class inference）とも呼ばれるこのメカニズムは，Leanが後で使用する情報を登録できるシンプルで強力な仕組みです．Leanが定義，定理，表記法の一部に対する暗黙の引数を埋めるために呼び出された時，この登録された情報を利用することができます．

TEXT. -/
/- OMIT:
Whereas an annotation ``(grp : Group G)`` tells Lean that it should
expect to be given that argument explicitly and the annotation
``{grp : Group G}`` tells Lean that it should try to figure it out
from contextual cues in the expression,
the annotation ``[grp : Group G]`` tells Lean that the corresponding
argument should be synthesized using type class inference.
Since the whole point to the use of such arguments is that
we generally do not need to refer to them explicitly,
Lean allows us to write ``[Group G]`` and leave the name anonymous.
You have probably already noticed that Lean chooses names like ``_inst_1``
automatically.
When we use the anonymous square-bracket annotation with the ``variables`` command,
then as long as the variables are still in scope,
Lean automatically adds the argument ``[Group G]`` to any definition or
theorem that mentions ``G``.

OMIT. -/
/- TEXT:
``(grp : Group G)`` という注釈はLeanにその引数が明示的に与えられることを期待するように指示するのに対し， ``{grp : Group G}`` という注釈は，Leanにその引数を式の文脈から理解するように指示し， ``[grp : Group G]`` はLeanが型クラス推論を用いて対応する引数が統合されるべきであることを示します．このような引数を使うことの要点は，一般的に明示的に参照する必要がないということなので，Leanは ``[Group G]`` と書いて引数の名前を匿名にしておくことができます．このようにした場合，Leanが ``_inst_1`` のような名前を自動的に選択することはすでにお気づきでしょう． ``variables`` コマンドで匿名の角括弧注釈を使用すると，変数がスコープ内にある限り，Leanは自動的に ``G`` に言及する定義や定理に引数 ``[Group G]`` を追加します．

TEXT. -/
/- OMIT:
How do we register the information that Lean needs to use to carry
out the search?
Returning to our group example, we need only make two changes.
First, instead of using the ``structure`` command to define the group structure,
we use the keyword ``class`` to indicate that it is a candidate
for class inference.
Second, instead of defining particular instances with ``def``,
we use the keyword ``instance`` to register the particular instance with
Lean. As with the names of class variables, we are allowed to leave the
name of an instance definition anonymous,
since in general we intend Lean to find it and put it to use
without troubling us with the details.
OMIT. -/
/- TEXT:
Leanがこのような情報を検索するために必要な情報はどのように登録すれば良いでしょうか？群の例に戻ると，必要な変更は2つだけです．まず，群構造を定義するために ``structure`` コマンドを使用する代わりに，クラス推論の候補であることを示すキーワード ``class`` を使用します．次に，特定のインスタンスを ``def`` で定義する代わりに，キーワード ``instance`` を使用して特定のインスタンスをLeanに登録します．クラス変数の名前と同様に，一般的にLeanは細かいことで私達を悩ませることなく，これらの定義を見つけて使ってもらうことを意図しているため，インスタンス定義の名前を無名にすることが許されています．
EXAMPLES: -/
-- QUOTE:
class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- OMIT:
The following illustrates their use.
OMIT. -/
/- TEXT:
これらの使い方は以下のようになります．
EXAMPLES: -/
-- QUOTE:
#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end
-- QUOTE.

/- OMIT:
The ``#check`` command shows that ``Group₂.mul`` has an implicit argument
``[Group₂ α]`` that we expect to be found by class inference,
where ``α`` is the type of the arguments to ``Group₂.mul``.
In other words, ``{α : Type*}`` is the implicit argument for the type
of the group elements and ``[Group₂ α]`` is the implicit argument for the
group structure on ``α``.
Similarly, when we define a generic squaring function ``my_square``
for ``Group₂``, we use an implicit argument ``{α : Type*}`` for
the type of the elements and an implicit argument ``[Group₂ α]`` for
the ``Group₂`` structure.

OMIT. -/
/- TEXT:
``#check`` コマンドは ``Group₂.mul`` がクラス推論で見つかること期待される暗黙の引数 ``[Group₂ α]`` を持っていることを示しています．ここで ``α`` は ``Group₂.mul`` の引数の型です．言い換えると， ``{α : Type*}`` は群要素の型を表す暗黙の引数であり， ``[Group₂ α]`` は ``α`` 上の群構造を表す暗黙の引数です．同様に，一般的な二乗関数 ``my_square`` を ``Group₂`` に対して定義する場合，要素の型には暗黙の引数 ``{α : Type*}`` を， ``Group₂`` 構造には暗黙の引数 ``[Group₂ α]`` を用います．

TEXT. -/
/- OMIT:
In the first example,
when we write ``Group₂.mul f g``, the type of ``f`` and ``g``
tells Lean that in the argument ``α`` to ``Group₂.mul``
has to be instantiated to ``Equiv.Perm β``.
That means that Lean has to find an element of ``Group₂ (Equiv.Perm β)``.
The previous ``instance`` declaration tells Lean exactly how to do that.
Problem solved!

OMIT. -/
/- TEXT:
最初の例では， ``Group₂.mul f g`` とかくと， ``f`` と ``g`` の型は ``Group₂.mul`` の引数 ``α`` として， ``Equiv.Perm β`` をインスタンス化しなければならないことをLeanに伝えます．つまりLeanは ``Group₂ (Equiv.Perm β)`` の要素を見つけなければならないということです．これにあたって上記の ``instance`` 宣言はLeanにその方法を正確に伝えています．これで問題は解決しました！

TEXT. -/
/- OMIT:
This simple mechanism for registering information so that Lean can find it
when it needs it is remarkably useful.
Here is one way it comes up.
In Lean's foundation, a data type ``α`` may be empty.
In a number of applications, however, it is useful to know that a
type has at least one element.
For example, the function ``List.headI``, which returns the first
element of a list, can return the default value when the list is empty.
To make that work, the Lean library defines a class ``Inhabited α``,
which does nothing more than store a default value.
We can show that the ``Point`` type is an instance:
OMIT. -/
/- TEXT:
Leanが必要なときに見つけられるように情報を登録するこのシンプルな仕組みは驚くほど便利です．ここで一つの方法を紹介しましょう．Leanの基礎では，データ型 ``α`` は空であることがあります．しかし，実用にあたって多くの場合には型に少なくとも1つの要素があることを知っておくと便利です．例えば，リストの最初の要素を返す関数 ``List.headl`` はリストが空の場合にデフォルト値を返すことができます．これを実現するために，Leanのライブラリでは ``Inhabited α`` クラスを定義しています． ``Point`` 型がこのインスタンスであることを示すことができます:
EXAMPLES: -/
-- QUOTE:
instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl
-- QUOTE.

/- OMIT:
The class inference mechanism is also used for generic notation.
The expression ``x + y`` is an abbreviation for ``Add.add x y``
where---you guessed it---``Add α`` is a class that stores
a binary function on ``α``.
Writing ``x + y`` tells Lean to find a registered instance of ``[Add.add α]``
and use the corresponding function.
Below, we register the addition function for ``Point``.
OMIT. -/
/- TEXT:
クラス推論のメカニズムは，一般的な表記法にも使用されます．式 ``x + y`` は ``Add.add x y`` の省略形であり， ``Add α`` は ---予想がつくでしょうが，--- ``α`` 上の二項関数を格納するクラスです． ``x + y`` と書くと，Leanは ``[Add.add α]`` の登録されたインスタンスを見つけて，対応する関数を使うように指示します．以下では， ``Potin`` の加算関数を登録しています．
EXAMPLES: -/
-- QUOTE:
instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end
-- QUOTE.

/- OMIT:
In this way, we can assign the notation ``+`` to binary operations on other
types as well.

OMIT. -/
/- TEXT:
このようにして，他の型に対する二項演算にも ``+`` という表記を割り当てることができます．

TEXT. -/
/- OMIT:
But we can do even better. We have seen that ``*`` can be used in any
group, ``+`` can be used in any additive group, and both can be used in
any ring.
When we define a new instance of a ring in Lean,
we don't have to define ``+`` and ``*`` for that instance,
because Lean knows that these are defined for every ring.
We can use this method to specify notation for our ``Group₂`` class:
OMIT. -/
/- TEXT:
しかしこれはさらに推し進めることができます．これまで， ``*`` はどんな群でも， ``+`` はどんな加法群でも，そしてどちらもどんな環でも使えていたことを見てきました．Leanで環の新しいインスタンスを定義するとき，そのインスタンスに対して ``+`` と ``*`` を定義する必要はありません．なぜならLeanはこれらがすべての環に対して定義されていることを知っているからです．この方法を使って ``Group₂`` クラスの記法を指定することができます:
EXAMPLES: -/
-- QUOTE:
instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
-- QUOTE.

/- OMIT:
In this case, we have to supply names for the instances, because
Lean has a hard time coming up with good defaults.
What makes this approach work is that Lean carries out a recursive search.
According to the instances we have declared, Lean can find an instance of
``Mul (Equiv.Perm α)`` by finding an
instance of ``Group₂ (Equiv.Perm α)``, and it can find an instance of
``Group₂ (Equiv.Perm α)`` because we have provided one.
Lean is capable of finding these two facts and chaining them together.

OMIT. -/
/- TEXT:
この場合，インスタンスの名前を指定しなければなりません．というのもLeanは既定のものとして適切なものを見つけるのが難しいからです．この方法が機能するのはLeanが再帰的な検索を行うからです．ここで宣言したインスタンスによると，Leanは ``Group₂ (Equiv.Perm α)`` のインスタンスを見つけることで ``Mul (Equiv.Perm α)`` のインスタンスを見つけることができます．そしてこの ``Group₂ (Equiv.Perm α)`` はその前に私達がインスタンスを提供しているためLeanはこれを見つけることができます．Leanはこれら2つの事実を見つけ，連鎖させることができます．

TEXT. -/
/- OMIT:
The example we have just given is dangerous, because Lean's
library also has an instance of ``Group (Equiv.Perm α)``, and
multiplication is defined on any group.
So it is ambiguous as to which instance is found.
In fact, Lean favors more recent declarations unless you explicitly
specify a different priority.
Also, there is another way to tell Lean that one structure is an
instance of another, using the ``extends`` keyword.
This is how Mathlib specifies that, for example,
every commutative ring is a ring.
You can find more information in :numref:`hierarchies` and in a
`section on class inference <https://leanprover.github.io/theorem_proving_in_lean4/type_classes.html#managing-type-class-inference>`_ in *Theorem Proving in Lean*.

OMIT. -/
/- TEXT:
ここで挙げた例は危険です．なぜなら，Leanのライブラリには ``Group (Equiv.Perm α)`` のインスタンスもあり，乗算は任意の群で定義されているからです．そのため，どちらのインスタンスが見つかるかは曖昧です．実際，Leanは明示的に優先順位を指定しない限り，より新しい宣言を優先します．また，ある構造体が別の構造体のインスタンスであることをLeanに伝えるには， ``extends`` キーワードを使う方法もあります．これは例えばMathlibにおいてすべての可換環が環であることの指定に使われています．より詳しい情報は *Theorem Proving in Lean* のクラス推論に関する節 `section on class inference <https://leanprover.github.io/theorem_proving_in_lean4/type_classes.html#managing-type-class-inference>`_ にあります． [#f21]_

TEXT. -/
/- OMIT:
In general, it is a bad idea to specify a value of
``*`` for an instance of an algebraic structure that already has
the notation defined.
Redefining the notion of ``Group`` in Lean is an artificial example.
In this case, however, both interpretations of the group notation unfold to
``Equiv.trans``, ``Equiv.refl``, and ``Equiv.symm``, in the same way.

OMIT. -/
/- TEXT:
一般的に，すでに記法が定義されている代数構造のインスタンスに ``*`` の値を指定するのは良くない考えです．Leanで ``Group`` の概念を再定義するのは人為的な例です．しかし，この場合群の表記法の解釈はどちらも ``Equiv.trans`` と ``Equiv.refl`` ， ``Equiv.symm`` に同じように展開されます．

TEXT. -/
/- OMIT:
As a similarly artificial exercise,
define a class ``AddGroup₂`` in analogy to ``Group₂``.
Define the usual notation for addition, negation, and zero
on any ``AddGroup₂``
using the classes ``Add``, ``Neg``, and ``Zero``.
Then show ``Point`` is an instance of ``AddGroup₂``.
Try it out and make sure that the additive group notation works for
elements of ``Point``.
OMIT. -/
/- TEXT:
同様に人工的な演習として， ``Group₂`` に類似したクラス ``AddGroup₂`` を定義しましょう．クラス ``Add`` と ``Neg`` ， ``Zero`` を使って任意の ``AddGroup₂`` 上の加算，否定，0の通常の記法を定義してください．そして， ``Point`` が ``AddGroup₂`` のインスタンスであることを示してください．出来たら試しに加法群表記が ``Point`` の要素に対して機能することを確認しましょう．
BOTH: -/
-- QUOTE:
class AddGroup₂ (α : Type*) where
/- EXAMPLES:
  add : α → α → α
  -- fill in the rest
-- QUOTE.
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α :=
  ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α :=
  ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α :=
  ⟨AddGroup₂.neg⟩

instance : AddGroup₂ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

section
variable (x y : Point)

#check x + -y + 0

end

/- OMIT:
It is not a big problem that we have already declared instances
``Add``, ``Neg``, and ``Zero`` for ``Point`` above.
Once again, the two ways of synthesizing the notation should come up
with the same answer.

OMIT. -/
/- TEXT:
上記の ``Point`` に対して ``Add`` と ``Neg`` ， ``Zero`` のインスタンスをすでに宣言していることは大して問題ではありません．繰り返しになりますが，表記法を合成する2つの方法は同じ答えになるはずだからです．

TEXT. -/
/- OMIT:
Class inference is subtle, and you have to be careful when using it,
because it configures automation that invisibly governs the interpretation of
the expressions we type.
When used wisely, however, class inference is a powerful tool.
It is what makes algebraic reasoning possible in Lean.
OMIT. -/
/- TEXT:
クラス推論は微妙なものであり，使用する際には注意しなければなりません．というのも私達が入力した式に対する解釈を目に見えない形で支配する自動化を設定しているからです．しかし，賢く使えばクラス推論は強力なツールとなり，Leanで代数的推論を可能にしてくれます．

.. [#f21] 訳注：日本語訳は `こちら <https://aconite-ac.github.io/theorem_proving_in_lean4_ja/type_classes.html#managing-type-class-inference-%E5%9E%8B%E3%82%AF%E3%83%A9%E3%82%B9%E6%8E%A8%E8%AB%96%E3%81%AE%E7%AE%A1%E7%90%86>`_
TEXT. -/

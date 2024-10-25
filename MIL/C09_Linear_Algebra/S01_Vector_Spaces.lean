-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- OMIT:

Vector spaces and linear maps
-----------------------------

OMIT. -/
/- TEXT:
ベクトル空間と線形写像
-----------------------------

TEXT. -/
/- OMIT:
Vector spaces
^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
ベクトル空間
^^^^^^^^^^^^^

.. index:: vector space

TEXT. -/
/- OMIT:
We will start directly abstract linear algebra, taking place in a vector space over any field.
However you can find information about matrices in
:numref:`Section %s <matrices>` which does not logically depend on this abstract theory.
Mathlib actually deals with a more general version of linear algebra involving the word module,
but for now we will pretend this is only an eccentric spelling habit.

OMIT. -/
/- TEXT:
本書では任意の体上のベクトル空間を取り扱う抽象線形代数を直接始めます．しかし，行列はこの抽象的な理論には依存していません．これに関する情報は :numref:`Section %s <matrices>` で取り扱っています．Mathlibは実際には加群という用語による線形代数のより一般的なバージョンを扱っていますが，今のところ，これは風変わりな言い換えに過ぎないということにしておきます．

TEXT. -/
/- OMIT:
The way to say “let :math:`K` be a field and let :math:`V` be a vector space over :math:`K`”
(and make them implicit arguments to later results) is:

OMIT. -/
/- TEXT:
「 :math:`K` を体とし， :math:`V` を :math:`K` 上のベクトル空間とする」（そして後続の結果への暗黙の引数とする）ということを述べるには次のようにします：
EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- OMIT:
We explained in :numref:`Chapter %s <hierarchies>` why we need two separate
typeclasses ``[AddCommGroup V] [Module K V]``.
The short version is the following.
Mathematically we want to say that having a :math:`K`-vector space structure
implies having an additive commutative group structure.
We could tell this to Lean. But then whenever Lean would need to find such a
group structure on a type :math:`V`, it would go hunting for vector space
structures using a *completely unspecified* field :math:`K` that cannot be inferred
from :math:`V`.
This would be very bad for the type class synthesis system.

OMIT. -/
/- TEXT:
なぜ ``[AddCommGroup V] [Module K V]`` と2つの別々の型クラスが必要であるかについては :numref:`Chapter %s <hierarchies>` にて説明しました．簡単に説明すると次のようになります．数学的には :math:`K` 上のベクトル空間構造を持つことは加法可換群構造を持つことを意味すると述べたいです．これをLeanに伝えることも可能です．しかし，Leanが :math:`V` 型についてそのような群構造を見つけるにあたって必ず :math:`V` から推論することができない **完全に未指定の** 体 :math:`K` を使ったベクトル空間構造を探しに行くことになります．これは型クラスの合成システムにとって非常に悪いことです．

TEXT. -/
/- OMIT:
The multiplication of a vector `v` by a scalar `a` is denoted by
`a • v`. We list a couple of algebraic rules about the interaction of this
operation with addition in the following examples. Of course `simp` or `apply?`
would find those proofs. There is also a `module` tactic that solves goals
following from the axioms of vector spaces and fields, in the same way the
`ring` tactic is used in commutative rings or the `group` tactic is used in
groups. But it is still useful to remember that scalar
multiplication is abbreviated `smul` in lemma names.


OMIT. -/
/- TEXT:
ベクトル `v` とスカラー `a` の掛け算は `a • v` と表記されます．以下の例にて，この演算と足し算の相互作用に関する代数的なルールをいくつか挙げます．もちろん， `simp` や `apply?` でもこれらの証明を見つけてくれるでしょう．また，ベクトル空間や体の公理から導かれるゴールを解決するための `module` タクティクが存在し，可換環に対しての `ring` や 群に対しての `group` と同じように用いられます．しかし，スカラー倍が補題の名前で `smul` と略されることを覚えておくことも有益です．
EXAMPLES: -/

-- QUOTE:
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- QUOTE.
/- OMIT:
As a quick note for more advanced readers, let us point out that, as suggested by
terminology, Mathlib’s linear algebra also covers modules over (not necessarily commutative)
rings.
In fact it even covers semi-modules over semi-rings. If you think you do not need
this level of generality, you can meditate the following example that nicely captures
a lot of algebraic rules about ideals acting on submodules:
OMIT. -/
/- TEXT:
より専門的な読者のために補足しておくと，Mathlibの線形代数は用語から示唆されるように，（必ずしも可換である必要はない）環上の加群も扱っています．実は，半環上の半加群さえもカバーしています．このようなレベルの一般性は必要ないと思われる方は，部分加群に作用するイデアルに関する多くの代数的ルールをうまく捉えた次の例について熟考するとよいでしょう：
EXAMPLES: -/
-- QUOTE:
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module (Ideal R) (Submodule R M) :=
  inferInstance


-- QUOTE.
/- OMIT:
Linear maps
^^^^^^^^^^^

OMIT. -/
/- TEXT:
線形写像
^^^^^^^^^^^

.. index:: linear map

TEXT. -/
/- OMIT:
Next we need linear maps. Like group morphisms, linear maps in Mathlib are bundled maps, i.e. packages
made of a map and proofs of its linearity properties.
Those bundled maps are converted to ordinary functions when applied.
See :numref:`Chapter %s <hierarchies>` for more information about this design.

OMIT. -/
/- TEXT:
次に必要なものは線形写像です．群の射と同様に，Mathlibの線形写像は束縛写像，つまり写像とその線形性の証明を詰め込んだものです．これらの束縛写像は適用されると普通の関数に変換されます．この設計の詳細については :numref:`Chapter %s <hierarchies>` を参照してください．

TEXT. -/
/- OMIT:
The type of linear maps between two ``K``-vector spaces
``V`` and ``W`` is denoted by ``V →ₗ[K] W``. The subscript `l` stands for linear.
At first it may feel odd to specify ``K`` in this notation.
But this is crucial when several fields come into play.
For instance real-linear maps from :math:`ℂ` to :math:`ℂ` are every map :math:`z ↦ az + b\bar{z}`
while only the maps :math:`z ↦ az` are complex linear, and this difference is crucial in
complex analysis.

OMIT. -/
/- TEXT:
2つの ``K`` 上のベクトル空間 ``V`` と ``W`` の間の線形写像の型は ``V →ₗ[K] W`` で表されます．添字の `l` は線形（linear）を表します． ``K`` をこのように表記するのは奇妙に感じるかもしれません．しかし，これは複数の体が登場するときに真価を発揮します．例えば， :math:`ℂ` から :math:`ℂ` への実線形写像はすべて写像 :math:`z ↦ az + b\bar{z}` ですが，写像 :math:`z ↦ az` だけが複素直線であり，この違いは複素解析において非常に重要です．
EXAMPLES: -/
-- QUOTE:

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- QUOTE.

/- OMIT:
Note that ``V →ₗ[K] W`` itself carries interesting algebraic structures (this
is part of the motivation for bundling those maps).
It is a ``K``-vector space so we can add linear maps and multiply them by scalars.

OMIT. -/
/- TEXT:
``V →ₗ[K] W`` 自体が興味深い代数的構造を持つことに注意してください（これがこれらの写像を束ねる動機のひとつです）．これは ``K`` 上のベクトル空間であり，そのため線形写像を足したりスカラーを掛けたりすることができます．
EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- OMIT:
One downside of using bundled maps is that we cannot use ordinary function composition.
We need to use ``LinearMap.comp`` or the notation ``∘ₗ``.

OMIT. -/
/- TEXT:
束縛写像を使うことの1つの欠点は，通常の関数合成が使えないことです．合成するには ``LinearMap.comp`` か ``∘ₗ`` という記法を使う必要があります．
EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- OMIT:
There are two main ways to construct linear maps.
First we can build the structure by providing the function and the linearity proof.
As usual, this is facilitated by the structure code action: you can type
``example : V →ₗ[K] V := _`` and use the code action “Generate a skeleton” attached to the
underscore.
OMIT. -/
/- TEXT:
線形写像を構築するには主に2つの方法があります．まず関数とその線形性の証明を提供することで構造体を構築することです．いつものように，これは構造体のコードアクションによって容易になります： ``example : V →ₗ[K] V := _`` と入力し，アンダースコアについているコードアクション「Generate a skeleton」を使用します．
EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- OMIT:
You may wonder why the proof fields of ``LinearMap`` have names ending with a prime.
This is because they are defined before the coercion to functions is defined, hence they are
phrased in terms of ``LinearMap.toFun``. Then they are restated as ``LinearMap.map_add``
and ``LinearMap.map_smul`` in terms of the coercion to function.
This is not yet the end of the story. One also wants a version of ``map_add`` that applies to
any (bundled) map preserving addition, such as additive group morphisms, linear maps, continuous
linear maps, ``K``-algebra maps etc… This one is ``map_add`` (in the root namespace).
The intermediate version, ``LinearMap.map_add`` is a bit redundant but allows to use dot notation, which
can be nice sometimes. A similar story exists for ``map_smul``, and the general framework
is explained in :numref:`Chapter %s <hierarchies>`.
OMIT. -/
/- TEXT:
なぜ ``LinearMap`` の証明についてのフィールドの名前はプライムで終わるのか不思議に思われるかもしれません．これは関数への強制が定義される前に定義されているためで，そのためこれらのフィールドは ``LinearMap.toFun`` という表現で記述されています．これらが関数に強制された表現で ``LinearMap.map_add`` と ``LinearMap.map_smul`` として再表現されるのはその後になります．まだこれで話は終わりではありません． ``map_add`` について，加法群の射，線形写像，連続線形写像， ``K`` 上の代数の写像など（束縛）写像を保存する足し算に適用するバージョンも必要になるかもしれません．これは（ルートの名前空間の） ``map_add`` です．中間バージョンの ``LinearMap.map_add`` は少し冗長ですが，ドット記法を使うことができ，時としてうまく機能します．同様の話は ``map_smul`` にもあり，一般的なフレームワークは :numref:`Chapter %s <hierarchies>` で説明されています．
EXAMPLES: -/
-- QUOTE:

#check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
#check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
#check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

-- QUOTE.

/- OMIT:
One can also build linear maps from the ones that are already defined in Mathlib
using various combinators.
For instance the above example is already known as ``LinearMap.lsmul K V 3``.
There are several reason why ``K`` and ``V`` are explicit arguments here.
The most pressing one is that from a bare ``LinearMap.lsmul 3`` there would be no way
for Lean to infer ``V`` or even ``K``.
But also ``LinearMap.lsmul K V`` is an interesting object by itself: it has type
``K →ₗ[K] V →ₗ[K] V``, meaning it is a ``K``-linear map from ``K``
—seen as a vector space over itself— to the space of ``K``-linear maps from ``V`` to ``V``.
OMIT. -/
/- TEXT:
また，Mathlibですでに定義されている線形写像を様々に組み合わせることで線形写像を作ることもできます．例えば，上記の例はすでに ``LinearMap.lsmul K V 3`` として知られているものです．ここで ``K`` と ``V`` が明示的な引数である理由はいくつかあります．最も直接的な理由は，ただの ``LinearMap.lsmul 3`` ではLeanが ``V`` や ``K`` を推論する方法がないからです．ただ， ``LinearMap.lsmul K V`` もそれ自体興味深いものです：これは ``K →ₗ[K] V →ₗ[K] V`` という型をもち， ``K`` （それ自体の上へのベクトル空間と見ています）から ``V`` から ``V`` への ``K`` 線型写像の空間への ``K`` 上の線形写像を意味します．
EXAMPLES: -/
-- QUOTE:

#check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

-- QUOTE.

/- OMIT:
There is also a type ``LinearEquiv`` of linear isomorphisms denoted by ``V ≃ₗ[K] W``.
The inverse of ``f : V ≃ₗ[K] W`` is ``f.symm : W ≃ₗ[K] V``,
composition of ``f`` and ``g`` is ``f.trans g`` also denoted by ``f ≪≫ₗ g``, and
the identity isomorphism of ``V`` is ``LinearEquiv.refl K V``.
Elements of this type are automatically coerced to morphisms and functions when necessary.
OMIT. -/
/- TEXT:
線形同型の型 ``LinearEquiv`` も存在し， ``V ≃ₗ[K] W`` で表されます． ``f : V ≃ₗ[K] W`` の逆は ``f.symm : W ≃ₗ[K] V`` ， ``f`` と ``g`` の合成は ``f.trans g`` であり ``f ≪≫ₗ g`` と表記され， ``V`` での自己同型は ``LinearEquiv.refl K V`` です．この型の要素は必要に応じて射や関数に強制されます．
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- OMIT:
One can use ``LinearEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.
OMIT. -/
/- TEXT:
``LinearEquiv.ofBijective`` を使えば，全単射から同型を作ることができます．これによって逆関数は計算不可能になります．
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.

/- OMIT:
Note that in the above example, Lean uses the announced type to understand that ``.ofBijective``
refers to ``LinearEquiv.ofBijective`` (without needing to open any namespace).

OMIT. -/
/- TEXT:
上記の例では，宣言された型を使用して， ``.ofBijective`` が ``LinearEquiv.ofBijective`` を（名前空間を開くことなく）指していることをLeanが理解していることに注意してください．

TEXT. -/
/- OMIT:
Sums and products of vector spaces
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OMIT. -/
/- TEXT:
ベクトル空間の直和と直積
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

TEXT. -/
/- OMIT:
We can build new vector spaces out of old ones using direct sums and direct
products.
Let us start with two vectors spaces. In this case there is no difference between sum and product,
and we can simply use the product type.
In the following snippet of code we simply show how to get all the structure maps (inclusions
and projections) as linear maps, as well as the universal properties constructing linear maps
into products and out of sums (if you are not familiar with the category-theoretic distinction
between sums and products, you can simply ignore the universal property vocabulary and focus
on the types of the following examples).
OMIT. -/
/- TEXT:
直和と直積を使って，古いベクトル空間から新しいベクトル空間を作ることができます．まず2つのベクトル空間から始めましょう．この場合，直和と直積に違いはなく，単純に直積型を使うことができます．以下のコード片では，すべての構造写像（包含と射影）を線形写像として得る方法と，線形写像について直積へ入るものと直和から出るものを構築する際の普遍性を示しています（直和と直積の圏論的な区別に慣れていない場合は，普遍性の語彙を無視して以下の例に出てくる型に着目するとよいでしょう）．
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- OMIT: First projection map
-- 1つ目への射影写像
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- OMIT: Second projection map
-- 2つ目への射影写像
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- OMIT: Universal property of the product
-- 直積の普遍性
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- OMIT: The product map does the expected thing, first component
-- 写像の直積が1つ目の要素について期待されたものであること
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- OMIT: The product map does the expected thing, second component
-- 写像の直積が2つ目の要素について期待されたものであること
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- OMIT: We can also combine maps in parallel
-- 写像を並列に組み合わせることもできます
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- OMIT: This is simply done by combining the projections with the universal property
--- 以下は直積の普遍性を組み合わせるだけで得られます
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

-- OMIT: First inclusion map
-- 1つ目の包含写像
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- OMIT: Second inclusion map
-- 2つ目の包含写像
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- OMIT: Universal property of the sum (aka coproduct)
-- 直和（いわゆる余積）の普遍性
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- OMIT: The coproduct map does the expected thing, first component
-- 余積の写像が1つ目の要素について期待されたものであること
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- OMIT: The coproduct map does the expected thing, second component
-- 余積の写像が2つ目の要素について期待されたものであること
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ

-- OMIT: The coproduct map is defined in the expected way
-- 余積の写像が期待されるように定義されていること
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
    φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl

end binary_product

-- QUOTE.
/- OMIT:
Let us now turn to sums and products of arbitrary families of vector spaces.
Here we will simply see how to define a family of vector spaces and access the universal
properties of sums and products.
Note that the direct sum notation is scoped to the ``DirectSum`` namespace, and
that the universal property of direct sums requires decidable equality on the
indexing type (this is somehow an implementation accident).
OMIT. -/
/- TEXT:
次に任意のベクトル空間の族の直和と直積について考えましょう．ここでは，ベクトル空間の族を定義し，直和と直積の普遍性にアクセスする方法を簡単に説明します．直和の表記は ``DirectSum`` 名前空間にスコープされ，直和の普遍性は添字型に決定可能な等式を要求することに注意してください（これは実装上の偶然です）．
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

-- OMIT: The universal property of the direct sum assembles maps from the summands to build
-- OMIT: a map from the direct sum
-- 直和の普遍性によって直和からの写像の構築は総和からの写像をまとめます
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

-- OMIT: The universal property of the direct product assembles maps into the factors
-- OMIT: to build a map into the direct product
-- 直積の普遍性によって直積への写像の構築は直積の因子への写像をまとめます
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

-- OMIT: The projection maps from the product
-- 直積からの射影写像
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

-- OMIT: The inclusion maps into the sum
-- 直和への包含写像
example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

-- OMIT: The inclusion maps into the product
-- 直積への包含写像
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

-- OMIT: In case `ι` is a finite type, there is an isomorphism between the sum and product.
-- `ι` が有限型の場合，直和と直積の間には同型があります．
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.

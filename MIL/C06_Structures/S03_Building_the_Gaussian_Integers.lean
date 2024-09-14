import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MIL.Common

/- OMIT:
Building the Gaussian Integers
------------------------------

OMIT. -/
/- TEXT:
.. _section_building_the_gaussian_integers:

ガウス整数の構築
-----------------

TEXT. -/
/- OMIT:
We will now illustrate the use of the algebraic hierarchy in Lean by
building an important mathematical object, the *Gaussian integers*,
and showing that it is a Euclidean domain. In other words, according to
the terminology we have been using, we will define the Gaussian integers
and show that they are an instance of the Euclidean domain structure.

OMIT. -/
/- TEXT:
ここで重要な数学的対象である **ガウス整数** （Gaussian integers）を構成し，そしてこれがユークリッド整域であることを示すことでLeanにおける代数的な階層の使い方を説明しましょう．これまで使ってきた用語に従って言い換えると，ガウス整数を定義し，それがユークリッド整域構造のインスタンスであることを示します．

TEXT. -/
/- OMIT:
In ordinary mathematical terms, the set of Gaussian integers :math:`\Bbb{Z}[i]`
is the set of complex numbers :math:`\{ a + b i \mid a, b \in \Bbb{Z}\}`.
But rather than define them as a subset of the complex numbers, our goal
here is to define them as a data type in their own right. We do this by
representing a Gaussian integer as a pair of integers, which we think of as the
*real* and *imaginary* parts.
OMIT. -/
/- TEXT:
通常の数学用語では，ガウス整数の集合 :math:`\Bbb{Z}[i]` は複素数の集合 :math:`\{ a + b i \mid a, b \in \Bbb{Z}\}` のことです．しかしこの集合を複素数の部分集合として定義するのではなく，複素数をそれ自体のデータ型として定義することがここでの目標です．これにあたってガウス整数を2つの整数の組をそれぞれ **実部** （real）と **虚部** （imaginary）と考えることで表現します．
BOTH: -/
-- QUOTE:
@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ
-- QUOTE.

/- OMIT:
We first show that the Gaussian integers have the structure of a ring,
with ``0`` defined to be ``⟨0, 0⟩``, ``1`` defined to be ``⟨1, 0⟩``, and
addition defined pointwise. To work out the definition of multiplication,
remember that we want the element :math:`i`, represented by ``⟨0, 1⟩``, to
be a square root of :math:`-1`. Thus we want

OMIT. -/
/- TEXT:
まずガウス整数が環の構造を持ち， ``0`` は ``⟨0, 0⟩`` で， ``1`` は ``⟨1, 0⟩`` と定義され，加法が実部と虚部それぞれにおいて定義されることを示します．乗法の定義を考えるには， ``⟨0, 1⟩`` で表される要素 :math:`i` を :math:`-1` の平方根としたいことを思い出してください．したがって次のように定義したいわけです．

.. math::

   (a + bi) (c + di) & = ac + bci + adi + bd i^2 \\
     & = (ac - bd) + (bc + ad)i.

TEXT. -/
/- OMIT:
This explains the definition of ``Mul`` below.
OMIT. -/
/- TEXT:
これは以下の ``Mul`` の定義を説明するものです．
BOTH: -/
namespace GaussInt

-- QUOTE:
instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
-- QUOTE.

/- OMIT:
As noted in :numref:`section_structures`, it is a good idea to put all the definitions
related to a data type in a namespace with the same name. Thus in the Lean
files associated with this chapter, these definitions are made in the
``GaussInt`` namespace.

OMIT. -/
/- TEXT:
:numref:`section_structures` で述べたように，データ型に関連するすべての定義を同じ名前の名前空間に置くと良いでしょう．これに従い，この章に対応するLeanファイルではこれらの定義は ``GaussInt`` 名前空間内で行われています．

TEXT. -/
/- OMIT:
Notice that here we are defining the interpretations of the notation ``0``,
``1``, ``+``, ``-``, and ``*`` directly, rather than naming them
``GaussInt.zero`` and the like and assigning the notation to those.
It is often useful to have an explicit name for the definitions, for example,
to use with ``simp`` and ``rewrite``.
OMIT. -/
/- TEXT:
ここで ``0`` と ``1`` ， ``+`` ， ``-`` ， ``*`` の記法の解釈について， ``GaussInt.zero`` などの名前をつけてそれらに記法を割り当てるのではなく，直接定義していることに注意してください．この方法は，例えば ``simp`` や ``rewrite`` で使用する際に定義に明示的な名前をつけたい際にしばしば便利です．
BOTH: -/
-- QUOTE:
theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl
-- QUOTE.

/- OMIT:
It is also useful to name the rules that compute the real and imaginary
parts, and to declare them to the simplifier.
OMIT. -/
/- TEXT:
また実部と虚部を計算する規則に名前をつけ，単純化で用いるよう宣言することも有益です．
BOTH: -/
-- QUOTE:
@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl
-- QUOTE.

/- OMIT:
It is now surprisingly easy to show that the Gaussian integers are an instance
of a commutative ring. We are putting the structure concept to good use.
Each particular Gaussian integer is an instance of the ``GaussInt`` structure,
whereas the type ``GaussInt`` itself, together with the relevant operations, is an
instance of the ``CommRing`` structure. The ``CommRing`` structure, in turn,
extends the notational structures ``Zero``, ``One``, ``Add``,
``Neg``, and ``Mul``.

OMIT. -/
/- TEXT:
ガウス整数が可換環のインスタンスであることを示すのは驚くほど簡単です．秘訣は構造体の概念にあります．それぞれのガウス整数は ``gaussInt`` 構造体のインスタンスであり， ``gaussInt`` 型自体と関連する演算は ``CommRing`` 構造体のインスタンスです．この ``CommRing`` 構造体は ``Zero`` と ``One`` ， ``Add`` ， ``Neg`` ， ``Mul`` という表記構造を拡張したものです．

TEXT. -/
/- OMIT:
If you type ``instance : CommRing GaussInt := _``, click on the light bulb
that appears in VS Code, and then ask Lean to fill in a skeleton for the
structure definition, you will see a scary number of entries.
Jumping to the definition of the structure, however, shows that many of the
fields have default definitions that Lean will fill in for you automatically.
The essential ones appear in the definition below.
A special case are ``nsmul`` and ``zsmul`` which should be ignored for now
and will be explained in the next chapter.
In each case, the relevant
identity is proved by unfolding definitions, using the ``ext`` tactic
to reduce the identities to their real and imaginary components,
simplifying, and, if necessary, carrying out the relevant ring calculation in
the integers. Note that we could easily avoid repeating all this code, but
this is not the topic of the current discussion.
OMIT. -/
/- TEXT:
もし ``instance : CommRing GaussInt := _`` と入力してvscodeに表示される電球マークをクリックし，Leanに構造体定義のスケルトンを埋めてもらうと，おびただしい数の項目が表示されます．しかし，構造体の定義に飛ぶと，多くのフィールドにはデフォルトの定義があり，これらはLeanが自動的に埋めてくれます．重要なものは以下の定義にあります．それぞれの場合に置いて，関連する恒等式は定義を展開し， ``ext`` を使って恒等式を実部と虚部に戻し，単純化し，必要であれば整数で関連する環の計算を行うことで証明されます．このコードをすべて繰り返さないようにすることは簡単ですが，これは現在の議論のテーマではないことに注意してください．
BOTH: -/
-- QUOTE:
instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp
-- QUOTE.

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

/- OMIT:
Lean's library defines the class of *nontrivial* types to be types with at
least two distinct elements. In the context of a ring, this is equivalent
to saying that the zero is not equal to the one. Since some common theorems
depend on that fact, we may as well establish it now.
OMIT. -/
/- TEXT:
Leanのライブラリでは少なくとも2つの異なる要素を持つ型を *nontrivial* 型のクラスとして定義しています．環の文脈においては，これは0が1に等しくないということと同じです．いくつかの一般的な定理はこの事実に依存しているため，これは今確立したほうがよいでしょう．
BOTH: -/
-- QUOTE:
instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp
-- QUOTE.

end GaussInt

/- OMIT:
We will now show that the Gaussian integers have an important additional
property. A *Euclidean domain* is a ring :math:`R` equipped with a *norm*
function :math:`N : R \to \mathbb{N}` with the following two properties:

OMIT. -/
/- TEXT:
ここでガウス整数が追加で重要な性質を持つことを示します． **ユークリッド整域** （Euclidean domain）とは以下の2つの性質を持つ **ノルム** （norm）関数 :math:`N : R \to \mathbb{N}` を備えた環 :math:`R` のことです:

TEXT. -/
/- OMIT:
- For every :math:`a` and :math:`b \ne 0` in :math:`R`, there are
  :math:`q` and :math:`r` in :math:`R` such that :math:`a = bq + r` and
  either :math:`r = 0` or `N(r) < N(b)`.
OMIT. -/
/- TEXT:
- :math:`R` の各 :math:`a` と :math:`b \ne 0` に対して， :math:`a = bq + r` と :math:`r = 0` または `N(r) < N(b)` のどちらかを満たす :math:`R` の :math:`q` と :math:`r` が存在する．

TEXT. -/
/- OMIT:
- For every :math:`a` and :math:`b \ne 0`, :math:`N(a) \le N(ab)`.

OMIT. -/
/- TEXT:
- すべての :math:`a` と :math:`b \ne 0` について， :math:`N(a) \le N(ab)` ．

TEXT. -/
/- OMIT:
The ring of integers :math:`\Bbb{Z}` with :math:`N(a) = |a|` is an
archetypal example of a Euclidean domain.
In that case, we can take :math:`q` to be the
result of integer division of :math:`a` by :math:`b` and :math:`r`
to be the remainder. These functions are defined in Lean so that the
satisfy the following:
TEXT. -/
/- OMIT:
:math:`N(a) = |a|` となる整数の環 :math:`\Bbb{Z}` はユークリッド整域の典型的な例です．この場合， :math:`a` を :math:`b` で整除した商を :math:`q` ，その余りを :math:`r` とすることができます．これらの関数は以下を満たすようにLeanで定義されています:
EXAMPLES: -/
-- QUOTE:
example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt a
-- QUOTE.

/- OMIT:
In an arbitrary ring, an element :math:`a` is said to be a *unit* if it divides
:math:`1`. A nonzero element :math:`a` is said to be *irreducible* if it cannot
be written in the form :math:`a = bc`
where neither :math:`b` nor :math:`c` is a unit. In the integers, every
irreducible element :math:`a` is *prime*, which is to say, whenever :math:`a`
divides a product :math:`bc`, it divides either :math:`b` or :math:`c`. But
in other rings this property can fail. In the ring
:math:`\Bbb{Z}[\sqrt{-5}]`, we have

OMIT. -/
/- TEXT:
任意の環において，元 :math:`a` が :math:`1` を割る場合，その元は **単元** （unit）であると言います．0ではない元 :math:`a` がどちらも単元ではない :math:`b` と :math:`c` を用いて :math:`a = bc` の形で書けない場合， :math:`a` は **既約** （irreducible）であるといいます．つまり，整数においては :math:`a` が積 :math:`bc` を割るときは必ず :math:`b` か :math:`c` のどちらかを割ることになるため，すべての既約元 :math:`a` は **素元** （prime）のことです．しかし他の環ではこの性質が破綻することがあります．環 :math:`\Bbb{Z}[\sqrt{-5}]` では次のようになります．

.. math::

  6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}),

TEXT. -/
/- OMIT:
and the elements :math:`2`, :math:`3`, :math:`1 + \sqrt{-5}`, and
:math:`1 - \sqrt{-5}` are all irreducible, but they are not prime. For example,
:math:`2` divides the product :math:`(1 + \sqrt{-5})(1 - \sqrt{-5})`,
but it does not divide either factor. In particular, we no longer have
unique factorization: the number :math:`6` can be factored into irreducible
elements in more than one way.

OMIT. -/
/- TEXT:
そして元 :math:`2` と :math:`3` ， :math:`1 + \sqrt{-5}` ， :math:`1 - \sqrt{-5}` はすべて既約元ですが，素元ではありません．例えば :math:`2` は積 :math:`(1 + \sqrt{-5})(1 - \sqrt{-5})` を割りますが，どちらの因数も割ることができません．もっと言うなら数 :math:`6` が複数の方法で既約元の因数に分解できることから，もはや一意な因数分解もできません．

TEXT. -/
/- OMIT:
In contrast, every Euclidean domain is a unique factorization domain, which
implies that every irreducible element is prime.
The axioms for a Euclidean domain imply that one can write any nonzero element
as a finite product of irreducible elements. They also imply that one can use
the Euclidean algorithm to find a greatest common divisor of any two
nonzero elements ``a`` and ``b``, i.e.~an element that is divisible by any
other common divisor. This, in turn, implies that factorization
into irreducible elements is unique up to multiplication by units.

OMIT. -/
/- TEXT:
これと対照的に，すべてのユークリッド整域は一意に因数分解ができる領域です．これはすべての既約元が素元であることを意味します．ユークリッド整域の公理はどんな0でない元も既約元の有限積として書けることを課します．またユークリッドの互助法を使って任意の2つの非零元 ``a`` と ``b`` の最大公約数，つまり他の公約数すべてを割り切れる元を求められることも要求します．このことは既約元への因数分解は単元の冪まで一意であることを意味します．

TEXT. -/
/- OMIT:
We now show that the Gaussian integers are a Euclidean domain with
the norm defined by :math:`N(a + bi) = (a + bi)(a - bi) = a^2 + b^2`.
The Gaussian integer :math:`a - bi` is called the *conjugate* of :math:`a + bi`.
It is not hard to check that for any complex numbers :math:`x` and :math:`y`,
we have :math:`N(xy) = N(x)N(y)`.

OMIT. -/
/- TEXT:
ここでガウス整数は :math:`N(a + bi) = (a + bi)(a - bi) = a^2 + b^2` で定義されるノルムを持つユークリッド整域であることを示します．ガウス整数 :math:`a - bi` は :math:`a + bi` の **共役** （conjugate）と呼ばれます．任意の複素数 :math:`x` と :math:`y` に対して :math:`N(xy) = N(x)N(y)` が成り立つことを確認するのは難しくありません．

TEXT. -/
/- OMIT:
To see that this definition of the norm makes the Gaussian integers a Euclidean
domain, only the first property is challenging. Suppose
we want to write :math:`a + bi = (c + di) q + r` for suitable :math:`q`
and :math:`r`. Treating :math:`a + bi` and :math:`c + di` are complex
numbers, carry out the division

OMIT. -/
/- TEXT:
このノルムの定義でガウス整数がユークリッド整域となることを見るにあたっては，最初の性質だけが難しいです．例えば適当な :math:`q` と :math:`r` に対して :math:`a + bi = (c + di)q + r` と書きたいとしましょう． :math:`a + bi` と :math:`c + di` は複素数であるとして次の除算を行います．

.. math::

  \frac{a + bi}{c + di} = \frac{(a + bi)(c - di)}{(c + di)(c-di)} =
    \frac{ac + bd}{c^2 + d^2} + \frac{bc -ad}{c^2+d^2} i.

TEXT. -/
/- OMIT:
The real and imaginary parts might not be integers, but we can round
them to the nearest integers :math:`u` and :math:`v`. We can then express the
right-hand side as :math:`(u + vi) + (u' + v'i)`, where
:math:`u' + v'i` is the part left over. Note that we have
:math:`|u'| \le 1/2` and :math:`|v'| \le 1/2`, and hence

OMIT. -/
/- TEXT:
実部と虚部は整数ではないかもしれませんが，最も近い整数 :math:`u` と :math:`v` に丸めることが出来ます．丸めた際の余った部分を :math:`u'+v'i` として，右辺の大きさを :math:`(u + vi) + (u' + v'i)` と表現できます．ここで :math:`|u'| \le 1/2` と :math:`|v'| \le 1/2` という条件があることに注意すると以下のようになります．

.. math::

  N(u' + v' i) = (u')^2 + (v')^2 \le 1/4 + 1/4 \le 1/2.

TEXT. -/
/- OMIT:
Multiplying through by :math:`c + di`, we have

OMIT. -/
/- TEXT:
:math:`c + di` を掛けると次のようになります．

.. math::

  a + bi = (c + di) (u + vi) + (c + di) (u' + v'i).

TEXT. -/
/- OMIT:
Setting :math:`q = u + vi` and :math:`r = (c + di) (u' + v'i)`, we have
:math:`a + bi = (c + di) q + r`, and we only need to
bound :math:`N(r)`:

OMIT. -/
/- TEXT:
:math:`q = u + vi` と :math:`r = (c + di) (u' + v'i)` を設定すると， :math:`a + bi = (c + di) q + r` となり， :math:`N(r)` を束縛するだけで良いことになります．

.. math::

  N(r) = N(c + di)N(u' + v'i) \le N(c + di) \cdot 1/2 < N(c + di).

TEXT. -/
/- OMIT:
The argument we just carried out requires viewing the Gaussian integers
as a subset of the complex numbers. One option for formalizing it in Lean
is therefore to embed the Gaussian integers in the complex numbers, embed
the integers in the Gaussian integers, define the rounding function from the
real numbers to the integers, and take great care to pass back and forth
between these number systems appropriately.
In fact, this is exactly the approach that is followed in Mathlib,
where the Gaussian integers themselves are constructed as a special case
of a ring of *quadratic integers*.
See the file `GaussianInt.lean
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean>`_.

OMIT. -/
/- TEXT:
ここまでの議論はガウス整数を複素数の部分集合としてみることを要求しています．したがって，これをLeanで形式化する1つの選択肢は，ガウス整数を複素数の中に埋め込み，整数をガウス整数の中に埋め込み，実数から整数への丸め関数を定義し，これらの数系の間を適切に行き来するよう細心の注意を払うことです．実際，これはMathlibで行われているアプローチと全く同じで，ガウス整数そのものは **二次体の整数** （quadratic integers）の環の特殊な場合として構成されています．詳しくはファイル `GaussianInt.lean <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean>`_ を見てください．

TEXT. -/
/- OMIT:
Here we will instead carry out an argument that stays in the integers.
This illustrates an choice one commonly faces when formalizing mathematics.
Given an argument that requires concepts or machinery that is not already
in the library, one has two choices: either formalizes the concepts or machinery
needed, or adapt the argument to make use of concepts and machinery you
already have.
The first choice is generally a good investment of time when the results
can be used in other contexts.
Pragmatically speaking, however, sometimes seeking a more elementary proof
is more efficient.

OMIT. -/
/- TEXT:
ただ，ここでは上記の選択肢の代わりに整数に留める議論を行います．この選択は数学を形式化する際によく直面するものです．ライブラリにない概念や機構を必要とする論題が与えられた時，それらを形式化するか，すでに持っている概念や機構を利用するように論題を適応させるかの2つの選択肢があります．最初の選択肢は，その結果が他の文脈でも使えるのであれば，一般的に見て時間を費やす価値があるでしょう．しかし実用的に言えば，より初歩的な証明を求めるほうが効率的な場合もあります．

TEXT. -/
/- OMIT:
The usual quotient-remainder theorem for the integers says that for
every :math:`a` and nonzero :math:`b`, there are :math:`q` and :math:`r`
such that :math:`a = b q + r` and :math:`0 \le r < b`.
Here we will make use of the following variation, which says that there
are :math:`q'` and :math:`r'` such that
:math:`a = b q' + r'` and :math:`|r'| \le b/2`.
You can check that if the value of :math:`r` in the first statement
satisfies :math:`r \le b/2`, we can take :math:`q' = q` and :math:`r' = r`,
and otherwise we can take :math:`q' = q + 1` and :math:`r' = r - b`.
We are grateful to Heather Macbeth for suggesting the following more
elegant approach, which avoids definition by cases.
We simply add ``b / 2`` to ``a`` before dividing and then subtract it
from the remainder.
OMIT. -/
/- TEXT:
整数の通常の商と剰余の定理はすべての :math:`a` と0ではない :math:`b` に対して， :math:`a = b q + r` と :math:`0 \le r < b` を満たす :math:`q` と :math:`r` が存在するというものです．ここでは， :math:`a = bq' + r'` かつ :math:`|r'| \le b/2` となるような :math:`q'` と :math:`r'` が存在するという以下の変種を利用します．最初の文の :math:`r` の値が :math:`r \le b/2` を満たす場合， :math:`q' = q` と :math:`r' = r` とすることができ，そうでない場合は :math:`q' = q + 1` と :math:`r' = r - b` とすることができることを確認できます．この形式化にあたってHeather Macbeth氏にはケース分割による定義を避けた，よりエレガントなアプローチを提案してもらい感謝しています．単純に割る前に ``a`` に ``b / 2`` を加え，余りから引くのです．
BOTH: -/
namespace Int

-- QUOTE:
def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  revert this; intro this -- FIXME, this should not be needed
  linarith
-- QUOTE.

/- OMIT:
Note the use of our old friend, ``linarith``. We will also need to express
``mod'`` in terms of ``div'``.
OMIT. -/
/- TEXT:
ここでおなじみの ``linarith`` を使っていることに注意してください．また， ``mod'`` を ``div'`` で表現する必要があります．
BOTH: -/
-- QUOTE:
theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]
-- QUOTE.

end Int

/- OMIT:
We will use the fact that :math:`x^2 + y^2` is equal to zero if and only if
:math:`x` and :math:`y` are both zero. As an exercise, we ask you to prove
that this holds in any ordered ring.
OMIT. -/
/- TEXT:
ここでは :math:`x^2 + y^2` が0に等しいのは， :math:`x` と :math:`y` の両方が0である場合だけであるという事実を用いています．演習としてこれが任意の順序環で成り立つことを証明してみましょう．
SOLUTIONS: -/
private theorem aux {α : Type*} [LinearOrderedRing α] {x y : α} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  haveI h' : x ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  pow_eq_zero h'

-- QUOTE:
-- BOTH:
theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num
-- QUOTE.

-- BOTH:
/- OMIT:
We will put all the remaining definitions and theorems in this section
in the ``GaussInt`` namespace.
First, we define the ``norm`` function and ask you to establish
some of its properties.
The proofs are all short.
OMIT. -/
/- TEXT:
この節の残りの定義と定理はすべて ``gaussInt`` 名前空間に置くことにします．まず， ``norm`` 関数を定義し，その性質をいくつか定義してみましょう．これらの証明はすべて短く済みます．
BOTH: -/
namespace GaussInt

-- QUOTE:
def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply add_nonneg <;>
  apply sq_nonneg

-- BOTH:
theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [norm, sq_add_sq_eq_zero, GaussInt.ext_iff]
  rfl

-- BOTH:
theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [lt_iff_le_and_ne, ne_comm, Ne, norm_eq_zero]
  simp [norm_nonneg]

-- BOTH:
theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [norm]
  ring

-- BOTH:
-- QUOTE.
/- OMIT:
Next we define the conjugate function:
OMIT. -/
/- TEXT:
次に共役を取る関数を定義します．
BOTH: -/
-- QUOTE:
def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]
-- QUOTE.

/- OMIT:
Finally, we define division for the Gaussian integers
with the notation ``x / y``, that rounds the complex quotient to the nearest
Gaussian integer. We use our bespoke ``Int.div'`` for that purpose.
As we calculated above, if ``x`` is :math:`a + bi` and ``y`` is :math:`c + di`,
then the real and imaginary parts of ``x / y`` are the nearest integers to

OMIT. -/
/- TEXT:
最後に，複素数の商を最も近いガウス整数に丸めるガウス整数の除算を ``x / y`` という記法で定義します．そのために， ``Int.div`` を今回のためにこしらえて用います．上で計算したように， ``x`` が :math:`a + bi` で ``y`` が :math:`c + di` の場合， ``x / y`` の実部と虚部はそれぞれ最も近い整数となります．

TEXT. -/
/- OMIT:
.. math::

  \frac{ac + bd}{c^2 + d^2} \quad \text{and} \quad \frac{bc -ad}{c^2+d^2},

respectively. Here the numerators are the real and imaginary parts of
:math:`(a + bi) (c - di)`, and the denominators are both equal to the norm
of :math:`c + di`.
OMIT. -/
/- TEXT:
ここで，分子は :math:`(a + bi)(c + di)` の実部と虚部であり，分母はどちらも :math:`c + di` のノルムに等しくなります．
BOTH: -/
-- QUOTE:
instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩
-- QUOTE.

/- OMIT:
Having defined ``x / y``, We define ``x % y`` to be the remainder,
``x - (x / y) * y``. As above, we record the definitions in the
theorems ``div_def`` and
``mod_def`` so that we can use them with ``simp`` and ``rewrite``.
OMIT. -/
/- TEXT:
``x / y`` を定義した後， ``x % y`` を ``x - (x / y) * y`` の余りとして定義します．上記のように，定義の ``div_def`` と ``mod_def`` に定義を記録し， ``simp`` と ``rewrite`` で使用できるようにします．
BOTH: -/
-- QUOTE:
instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl
-- QUOTE.

/- OMIT:
These definitions immediately yield ``x = y * (x / y) + x % y`` for every
``x`` and ``y``, so all we need to do is show that the norm of ``x % y`` is
less than the norm of ``y`` when ``y`` is not zero.

OMIT. -/
/- TEXT:
これらの定義から，すべての ``x`` と ``y`` に対して， ``x = y * (x / y) + x % y`` がすぐに得られるため，あとは ``y`` が0ではない時， ``x % y`` のノルムが ``y`` のノルムより小さいことを示せば良いです．

TEXT. -/
/- OMIT:
We just defined the real and imaginary parts of ``x / y`` to be
``div' (x * conj y).re (norm y)`` and ``div' (x * conj y).im (norm y)``,
respectively.
Calculating, we have

OMIT. -/
/- TEXT:
先程 ``x / y`` の実部と虚部をそれぞれ ``div' (x * conj y).re (norm y)`` と ``div' (x * conj y).im (norm y)`` と定義しました．これを用いて計算すると以下のようになります．

  ``(x % y) * conj y = (x - x / y * y) * conj y = x * conj y - x / y * (y * conj y)``

TEXT. -/
/- OMIT:
The real and imaginary parts of the right-hand side are exactly ``mod' (x * conj y).re (norm y)`` and ``mod' (x * conj y).im (norm y)``.
By the properties of ``div'`` and ``mod'``,
these are guaranteed to be less than or equal to ``norm y / 2``.
So we have

OMIT. -/
/- TEXT:
右辺の実部と虚部は ``mod' (x * conj y).re (norm y)`` と ``mod' (x * conj y).im (norm y)`` です． ``div'`` と ``mod'`` の性質により，これらは ``norm y / 2`` 以下であることが保証されています．従って以下のようになります．

  ``norm ((x % y) * conj y) ≤ (norm y / 2)^2 + (norm y / 2)^2 ≤ (norm y / 2) * norm y``.

TEXT. -/
/- OMIT:
On the other hand, we have

OMIT. -/
/- TEXT:
また一方で以下を得ます．

  ``norm ((x % y) * conj y) = norm (x % y) * norm (conj y) = norm (x % y) * norm y``.

TEXT. -/
/- OMIT:
Dividing through by ``norm y`` we have ``norm (x % y) ≤ (norm y) / 2 < norm y``,
as required.

OMIT. -/
/- TEXT:
``norm y`` で割ることで求めていた``norm (x % y) ≤ (norm y) / 2 < norm y`` を得ます．

TEXT. -/
/- OMIT:
This messy calculation is carried out in the next proof. We encourage you
to step through the details and see if you can find a nicer argument.
OMIT. -/
/- TEXT:
この面倒な計算は次にお証明で行われます．証明をたどってみて，もっとすっきりした証明を見つけられるかどうか試してみることをお勧めします．
BOTH: -/
-- QUOTE:
theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith
-- QUOTE.

/- OMIT:
We are in the home stretch. Our ``norm`` function maps Gaussian integers to
nonnegative integers. We need a function that maps Gaussian integers to natural
numbers, and we obtain that by composing ``norm`` with the function
``Int.natAbs``, which maps integers to the natural numbers.
The first of the next two lemmas establishes that mapping the norm to the
natural numbers and back to the integers does not change the value.
The second one re-expresses the fact that the norm is decreasing.
OMIT. -/
/- TEXT:
いよいよ本番です．上記で定義した ``norm`` 関数はガウス整数を非負整数に写します．ここでさらにガウス整数を自然数に移す関数が必要であり，これは整数を自然数に移す関数 ``Int.natAbs`` と ``norm`` 関数を組み合わせることで実現できます．次の2つの補題のうち，最初の補題はノルムを自然数に写し，整数に戻しても値が変わらないことを証明するものです．2番めの定理はノルムが減少するという事実を再表現しています．
BOTH: -/
-- QUOTE:
theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy
-- QUOTE.

/- OMIT:
We also need to establish the second key property of the norm function
on a Euclidean domain.
OMIT. -/
/- TEXT:
またユークリッド整域上のノルム関数の2つ目の重要な性質を確立する必要があります．
BOTH: -/
-- QUOTE:
theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)
-- QUOTE.

/- OMIT:
We can now put it together to show that the Gaussian integers are an
instance of a Euclidean domain. We use the quotient and remainder function we
have defined.
The Mathlib definition of a Euclidean domain is more general than the one
above in that it allows us to show that remainder decreases with respect
to any well-founded measure.
Comparing the values of a norm function that returns natural numbers is
just one instance of such a measure,
and in that case, the required properties are the theorems
``natAbs_norm_mod_lt`` and ``not_norm_mul_left_lt_norm``.
OMIT. -/
/- TEXT:
これをまとめて，ガウス整数がユークリッド整域のインスタンスであることを示しましょう．ここでは定義した商と剰余の関数を使います．Mathlibのユークリッド整域の定義は上の定義よりも一般的で，剰余が任意の整礎関係の測度に関しても減少することを示すことができます．自然数を返すノルム関数の値を比較することはそのような測度の一例にすぎず，その場合に必要な性質は定理 ``natAbs_norm_mod_lt`` と ``not_norm_mul_left_lt_norm`` になります．
BOTH: -/
-- QUOTE:
instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm] ; ring
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }
-- QUOTE.

/- OMIT:
An immediate payoff is that we now know that, in the Gaussian integers,
the notions of being prime and being irreducible coincide.
OMIT. -/
/- TEXT:
これらのことから直ちに得られる成果は，ガウス整数に置いて素元であることと既約元であることが一致するということです．
BOTH: -/
-- QUOTE:
example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime
-- QUOTE.

end GaussInt

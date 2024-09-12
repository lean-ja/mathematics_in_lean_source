import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

/- OMIT:
Defining structures
-------------------

OMIT. -/
/- TEXT:
.. _section_structures:

構造体の定義
-------------------

TEXT. -/
/- OMIT:
In the broadest sense of the term, a *structure* is a specification
of a collection of data, possibly with constraints that the
data is required to satisfy.
An *instance* of the structure is a particular bundle of data satisfying
the constraints. For example, we can specify that a point is
a tuple of three real numbers:
OMIT. -/
/- TEXT:
広義の意味において， **構造体** （structure）はあるデータの集まりについての仕様であり，場合によってはデータが満たすべき制約を伴います．構造体の **インスタンス** （instance）はこの制約を満たすような特定のデータを束ねたものです．例えば，点とは次のように3つの実数からなるタプルであると指定できます：
BOTH: -/
-- QUOTE:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
-- QUOTE.

/- OMIT:
The ``@[ext]`` annotation tells Lean to automatically generate theorems
that can be used to prove that two instances of a structure are equal
when their components are equal, a property known as *extensionality*.
OMIT. -/
/- TEXT:
``@[ext]`` 注釈によって **外延性** （extensionality）として知られている，構造体の2つのインスタンスが等しいことを証明する定理が自動的に生成されます．
EXAMPLES: -/
-- QUOTE:
#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption
-- QUOTE.

/- OMIT:
We can then define particular instances of the ``Point`` structure.
Lean provides multiple ways of doing that.
OMIT. -/
/- TEXT:
``Point`` 構造体の具体的なインスタンスを定義することもできます．Leanではいくつかの方法で定義することができます．
EXAMPLES: -/
-- QUOTE:
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4
-- QUOTE.

/- OMIT:
..
  Because Lean knows that the expected type of
  ``myPoint1`` is a ``Point``, you can start the definition by
  writing an underscore, ``_``. Clicking on the light bulb
  that appears nearby in VS Code will then
  give you the option of inserting a template definition
  with the field names listed for you.

In the first example, the fields of the structure are named
explicitly.
The function ``Point.mk`` referred to in the definition of ``myPoint3``
is known as the *constructor* for the ``Point`` structure, because
it serves to construct elements.
You can specify a different name if you want, like ``build``.
OMIT. -/
/- TEXT:
最初の例では，構造体のフィールドには明示的に名前が付けられています． ``myPoint3`` の定義で参照されている関数 ``Point.mk`` は ``Point`` 構造体の **コンストラクタ** （constructor）として知られているものです．この名前は要素を構築するためのものであることから来ています．必要であれば ``build`` など別の名前を指定することもできます．
EXAMPLES: -/
-- QUOTE:
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4
-- QUOTE.

/- OMIT:
The next two examples show how to define functions on structures.
Whereas the second example makes the ``Point.mk``
constructor explicit, the first example uses an anonymous constructor
for brevity.
Lean can infer the relevant constructor from the indicated type of
``add``.
It is conventional to put definitions and theorems associated
with a structure like ``Point`` in a namespace with the same name.
In the example below, because we have opened the ``Point``
namespace, the full name of ``add`` is ``Point.add``.
When the namespace is not open, we have to use the full name.
But remember that it is often convenient to use
anonymous projection notation,
which allows us to write ``a.add b`` instead of ``Point.add a b``.
Lean interprets the former as the latter because ``a`` has type ``Point``.
OMIT. -/
/- TEXT:
次の2つの例では構造体上の関数を定義する方法を示しています．2つ目の例では ``Point.mk`` コンストラクタを明示的に用いていますが，1つ目の例では簡潔にするために無名コンストラクタを使用しています．Leanは ``add`` の型から関連するコンストラクタを推測することができます．``Point`` のような構造体に関連する定義や定理は，同じ名前の名前空間に置くことが通例です．以下の例では， ``Point`` 名前空間を開いているため， ``add`` の完全な名前は ``Point.add`` となります．名前空間が開かれていない場合，フルネームを使用する必要があります．しかし，無名の射影記法を使用すると便利な場合が多いことを思い出してください．無名の射影記法を使用すると， ``Point.add a b`` の代わりに ``a.add b`` と書くことができます．Leanは前者を後者として解釈しますが，これは ``a`` が ``Point`` 型を持っているからです．
BOTH: -/
-- QUOTE:
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

-- EXAMPLES:
def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2
-- QUOTE.

/- OMIT:
Below we will continue to put definitions in the relevant
namespace, but we will leave the namespacing commands out of the quoted
snippets. To prove properties of the addition function,
we can use ``rw`` to expand the definition and ``ext`` to
reduce an equation between two elements of the structure to equations
between the components.
Below we use the ``protected`` keyword so that the name of the
theorem is ``Point.add_comm``, even when the namespace is open.
This is helpful when we want to avoid ambiguity with a generic
theorem like ``add_comm``.
OMIT. -/
/- TEXT:
以下のコードスニペットからは名前空間コマンドが除外されていますが，関連する名前空間に定義を置いていっています．足し算関数の性質を証明するために， ``rw`` を使って定義を展開し， ``ext`` を使って構造体の2つの要素間の等式をその構成要素間の等式に落とし込むことができます．以下では ``protected`` キーワードを使用して，名前空間が開いていても定理の名前が ``Point.add_comm`` になるようにしています．これは ``add_comm`` のような一般的な定理とのあいまいさを避けたいときに便利です．
EXAMPLES: -/
namespace Point

-- QUOTE:
protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
-- QUOTE.

/- OMIT:
Because Lean can unfold definitions and simplify projections
internally, sometimes the equations we want hold definitionally.
OMIT. -/
/- TEXT:
Leanは内部的に定義を展開し，射影を単純化することができるため，欲しい等式が定義的に成立することもあります．
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl
-- QUOTE.

/- OMIT:
It is also possible to define functions on structures using
pattern matching,
in a manner similar to the way we defined recursive functions in
:numref:`section_induction_and_recursion`.
The definitions ``addAlt`` and ``addAlt'`` below are essentially the
same; the only difference is that we use anonymous constructor notation
in the second.
Although it is sometimes convenient to define functions this way, and structural eta-reduction makes
this alternative definitionally equivalent, it can make things less convenient in later proofs.
In particular, `rw [addAlt]` leaves us with a messier goal view containing a `match` statement.
OMIT. -/
/- TEXT:
:numref:`section_induction_and_recursion` で再帰関数を定義した時と同じように，パターンマッチを使って構造体に対する関数を定義することもできます．以下の ``addAlt`` と ``addAlt'`` の定義は本質的には同じです；唯一の違いは，後者では無名コンストラクタを使用している点です．このような関数の定義方法は便利な場合もありますし，構造的にはη簡約によってこの代替的な定義と等価になりますが，この後の証明では使い勝手が悪くなります．特に， `rw [addAlt]` は `match` 文を含んだより面倒なゴールをinfoviewに残します．
EXAMPLES: -/
-- QUOTE:
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm
-- QUOTE.

/- OMIT:
Mathematical constructions often involve taking apart bundled information and
putting it together again in different ways.
It therefore makes sense that Lean and Mathlib offer so many ways
of doing this efficiently.
As an exercise, try proving that ``Point.add`` is associative.
Then define scalar multiplication for a point and show that it
distributes over addition.
OMIT. -/
/- TEXT:
数学的な構成ではまとまった情報をバラバラにして，それをまた別の方法で組み立てることが多いです．そのためLeanとMathlibがこれを効率的に行う方法を数多く提供しているのは理にかなっています．演習として， ``Point.add`` が結合的であることを証明してみましょう．その後に点のスカラー倍を定義し，それが加算に対して分配することを示します．
BOTH: -/
-- QUOTE:
protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, add_assoc]
-- BOTH:

def smul (r : ℝ) (a : Point) : Point :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ⟨r * a.x, r * a.y, r * a.z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, smul, mul_add]
-- BOTH:
-- QUOTE.

end Point

/- OMIT:
Using structures is only the first step on the road to
algebraic abstraction.
We don't yet have a way to link ``Point.add`` to the generic ``+`` symbol,
or to connect ``Point.add_comm`` and ``Point.add_assoc`` to
the generic ``add_comm`` and ``add_assoc`` theorems.
These tasks belong to the *algebraic* aspect of using structures,
and we will explain how to carry them out in the next section.
For now, just think of a structure as a way of bundling together objects
and information.

OMIT. -/
/- TEXT:
構造体を使用することは代数的抽象化への第一歩にすぎません．まだ ``Point.add`` を一般的な ``+`` 記号に結び付けたり， ``Point.add_comm`` と ``Point.add_assoc`` を一般的な ``add_comm`` と ``add_assoc`` の定理に結び付けたりする方法がありません．これらのタスクは，構造体を使用する際の **代数的な** 側面に属しており，この実行方法については次節で説明します．今のところは構造体はオブジェクトと情報を束ねる方法だと考えてください．

TEXT. -/
/- OMIT:
It is especially useful that a structure can specify not only
data types but also constraints that the data must satisfy.
In Lean, the latter are represented as fields of type ``Prop``.
For example, the *standard 2-simplex* is defined to be the set of
points :math:`(x, y, z)` satisfying :math:`x ≥ 0`, :math:`y ≥ 0`, :math:`z ≥ 0`,
and :math:`x + y + z = 1`.
If you are not familiar with the notion, you should draw a picture,
and convince yourself that this set is
the equilateral triangle in three-space with vertices
:math:`(1, 0, 0)`, :math:`(0, 1, 0)`, and :math:`(0, 0, 1)`,
together with its interior.
We can represent it in Lean as follows:
OMIT. -/
/- TEXT:
構造体においてはデータ型だけでなく，データが満たすべき制約も指定できる点が特に便利です．Leanでは後者は ``Prop`` 型のフィールドとして表現されます．例えば， **標準2単体** （standard 2-simplex）は :math:`x ≥ 0` ， :math:`y ≥ 0` ， :math:`z ≥ 0` および :math:`x + y + z = 1` を満たす点 :math:`(x, y, z)` の集合として定義されます．もしこの概念に馴染みがなければ，絵を描いみてこの集合が :math:`(1, 0, 0)` ， :math:`(0, 1, 0)` ， and :math:`(0, 0, 1)` を頂点とする3空間の二等辺三角形とその内部であることを確かめてください．これをLeanで表すと次のようになります：
BOTH: -/
-- QUOTE:
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1
-- QUOTE.

/- OMIT:
Notice that the last four fields refer to ``x``, ``y``, and ``z``,
that is, the first three fields.
We can define a map from the two-simplex to itself that swaps ``x`` and ``y``:
OMIT. -/
/- TEXT:
最後の4つのフィールドはその前にある3つのフィールド ``x`` と ``y`` ， ``z`` を参照している点に注目してください．この2単体について ``x`` と ``y`` を入れ替える2単体からそれ自身への写像を定義することができます：
BOTH: -/
namespace StandardTwoSimplex

-- EXAMPLES:
-- QUOTE:
def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]
-- QUOTE.

-- OMIT: (TODO) add a link when we have a good explanation of noncomputable section.
/- OMIT:
More interestingly, we can compute the midpoint of two points on
the simplex. We have added the phrase ``noncomputable section``
at the beginning of this file in order to use division on the real numbers.
OMIT. -/
/- TEXT:
さらに興味深いことに，単体上の2点の中点を計算することができます．ここで実数上の除算を使うためにこのファイルの冒頭に ``noncomputable section`` というフレーズを追加しています．
BOTH: -/
-- QUOTE:
noncomputable section

-- EXAMPLES:
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]
-- QUOTE.

/- OMIT:
Here we have established ``x_nonneg``, ``y_nonneg``, and ``z_nonneg``
with concise proof terms, but establish ``sum_eq`` in tactic mode,
using ``by``.

OMIT. -/
/- TEXT:
ここでは ``x_nonneg`` と ``y_nonneg`` ， ``z_nonneg`` を簡潔な証明項で確立しましたが， ``sum_eq`` は ``by`` を使ってタクティクモードで証明しています．

TEXT. -/
/- OMIT:
Given a parameter :math:`\lambda` satisfying :math:`0 \le \lambda \le 1`,
we can take the weighted average :math:`\lambda a + (1 - \lambda) b`
of two points :math:`a` and :math:`b` in the standard 2-simplex.
We challenge you to define that function, in analogy to the ``midpoint``
function above.
OMIT. -/
/- TEXT:
あるパラメータ :math:`\lambda` が :math:`0 \le \lambda \le 1` を満たす場合，標準2単体の2点 :math:`a` と :math:`b` の加重平均 :math:`\lambda a + (1 - \lambda) b` を取ることができます．上記の ``midpoint`` 関数になぞらえて，その関数の定義に挑戦してみましょう．
BOTH: -/
-- QUOTE:
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
/- EXAMPLES:
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  sorry
SOLUTIONS: -/
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)
  sum_eq := by
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    · ring
    simp [a.sum_eq, b.sum_eq]
-- QUOTE.
-- BOTH:

end

end StandardTwoSimplex

/- OMIT:
Structures can depend on parameters.
For example, we can generalize the standard 2-simplex to the standard
:math:`n`-simplex for any :math:`n`.
At this stage, you don't have to know anything about the type ``Fin n``
except that it has :math:`n` elements, and that Lean knows
how to sum over it.
OMIT. -/
/- TEXT:
構造体はパラメータに依存することができます．例えば，任意の :math:`n` に対して標準2単体を標準 :math:`n` 単体に一般化することができます．現時点では型 ``Fin n`` が :math:`n` 個の要素を持つことと，Leanがその和の取り方を知っていること以外は何も知る必要はありません．
BOTH: -/
-- QUOTE:
open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex
-- QUOTE.

/- OMIT:
As an exercise, see if you can define the weighted average of
two points in the standard :math:`n`-simplex.
You can use ``Finset.sum_add_distrib``
and ``Finset.mul_sum`` to manipulate the relevant sums.
OMIT. -/
/- TEXT:
演習問題として，2点の加重平均を標準 :math:`n` 単体に対して定義できるか試してみましょう．ここで関連する合計の操作として ``Finset.sum_add_distrib`` と ``Finset.mul_sum`` を使うことができます．
SOLUTIONS: -/
namespace StandardSimplex

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := lambda * a.V i + (1 - lambda) * b.V i
  NonNeg i :=
    add_nonneg (mul_nonneg lambda_nonneg (a.NonNeg i)) (mul_nonneg (by linarith) (b.NonNeg i))
  sum_eq_one := by
    trans (lambda * ∑ i, a.V i) + (1 - lambda) * ∑ i, b.V i
    · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp [a.sum_eq_one, b.sum_eq_one]

end StandardSimplex

/- OMIT:
We have seen that structures can be used to bundle together data
and properties.
Interestingly, they can also be used to bundle together properties
without the data.
For example, the next structure, ``IsLinear``, bundles together
the two components of linearity.
OMIT. -/
/- TEXT:
構造体は，データとその性質を束ねるために使用できることを見てきました．興味深いことに，構造体はデータなしで性質を束ねることもできます．例えば，次の構造体 ``IsLinear`` は線形性についての2つの要素を束ねたものです．
EXAMPLES: -/
-- QUOTE:
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
-- QUOTE.

/- OMIT:
It is worth pointing out that structures are not the only way to bundle
together data.
The ``Point`` data structure can be defined using the generic type product,
and ``IsLinear`` can be defined with a simple ``and``.
OMIT. -/
/- TEXT:
構造体だけがデータを束ねる唯一の方法ではないことは指摘しておくべきことでしょう．データ構造 ``Point`` は一般的な型の積で定義することができ， ``IsLinear`` は単純な ``and`` で定義することができます．
EXAMPLES: -/
-- QUOTE:
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x
-- QUOTE.

/- OMIT:
Generic type constructions can even be used in place of structures
with dependencies between their components.
For example, the *subtype* construction combines a piece of data with
a property.
You can think of the type ``PReal`` in the next example as being
the type of positive real numbers.
Any ``x : PReal`` has two components: the value, and the property of being
positive.
You can access these components as ``x.val``, which has type ``ℝ``,
and ``x.property``, which represents the fact ``0 < x.val``.
OMIT. -/
/- TEXT:
一般的な型の構築においては，構成要素間の依存関係を持つ構造体の代わりに使うこともできます．例えば **部分型** （subtype）構成はあるデータの一部とその性質を結合します．次の例の ``PReal`` 型は正の実数の型であると考えることができます．任意の ``x : PReal`` は2つの要素をもちます：すなわちその値とそれが正であることの性質です．これらのコンポーネントにアクセスすることができ， ``x.val`` は ``ℝ`` 型を持ち， ``x.property`` は ``0 < x.val`` を表します．
EXAMPLES: -/
-- QUOTE:
def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end
-- QUOTE.

/- OMIT:
We could have used subtypes to define the standard 2-simplex,
as well as the standard :math:`n`-simplex for an arbitrary :math:`n`.
OMIT. -/
/- TEXT:
標準2単体を定義するために部分型を使うこともでき，また同じように任意の :math:`n` に対する標準 :math:`n` 単体も定義することができます．
EXAMPLES: -/
-- QUOTE:
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }
-- QUOTE.

/- OMIT:
Similarly, *Sigma types* are generalizations of ordered pairs,
whereby the type of the second component depends on the type of
the first.
OMIT. -/
/- TEXT:
同様に， **シグマ型** （Sigma type）は順序対の一般化であり，2番目の要素の型は1番目の要素の型に依存します．
EXAMPLES: -/
-- QUOTE:
def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
-- QUOTE.

/- OMIT:
Given ``s : StdSimplex``, the first component ``s.fst`` is a natural
number, and the second component is an element of the corresponding
simplex ``StandardSimplex s.fst``.
The difference between a Sigma type and a subtype is that
the second component of a Sigma type is data rather than a proposition.

OMIT. -/
/- TEXT:
``s : StdSimplex`` が与えられた時，第一成分 ``s.fst`` は自然数であり，第二成分は対応する単体 ``StandardSimplex s.fst`` の要素です．シグマ型と部分型の違いは，シグマ型の第二成分が命題ではなくデータであることです．

TEXT. -/
/- OMIT:
But even though we can use products, subtypes, and Sigma types
instead of structures, using structures has a number of advantages.
Defining a structure abstracts away the underlying representation
and provides custom names for the functions that access the components.
This makes proofs more robust:
proofs that rely only on the interface to a structure
will generally continue to work when we change the definition,
as long as we redefine the old accessors in terms of the new definition.
Moreover, as we are about to see, Lean provides support for
weaving structures together into a rich, interconnected hierarchy,
and for managing the interactions between them.
OMIT. -/
/- TEXT:
しかし，構造体の代わりに積，部分型，シグマ型を使うことができるとしても，構造体を使うことには多くの利点があります．構造体を定義することで，基礎となる表現が抽象化され，構成要素にアクセスする関数名をカスタムできます．これは証明をより頑強にします：構造体へのインタフェースにのみ依存する証明では一般的に，古いアクセサを新しい定義に基づいて再定義する限り，定義を変更しても機能し続けます．さらに，これから説明するように，Leanは構造体を豊かで相互接続された階層に編み上げることができ，それらの間の相互作用を管理するためのサポートを提供します．
TEXT. -/
/- OMIT: (TODO)
Comments from Patrick:
We could make this paragraph much less abstract by showing how to access the components of a point with the definition def point'' := ℝ × ℝ × ℝ. However if we do that it would probably be honest to also mention the possibility of using fin 3 → ℝ as the definition. This interesting anyhow, because I think very few mathematician realize that defining ℝ^n as an iterated cartesian product is a polite lie that would be a nightmare if taken seriously.

By the way, should be include some comment about similarities and differences with object-oriented programming? All the examples from that page would clearly fit very well with classes in python say. And we'll have to face the name-clash between classes in Lean and classes in C++ or python sooner or later. Life would be so much simpler if classes in Lean could use another name...
OMIT. -/

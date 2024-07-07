-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

/- OMIT:
The Existential Quantifier
--------------------------

OMIT. -/
/- TEXT:
.. _the_existential_quantifier:

存在量化子
-----------

TEXT. -/
/- OMIT:
The existential quantifier, which can be entered as ``\ex`` in VS Code,
is used to represent the phrase "there exists."
The formal expression ``∃ x : ℝ, 2 < x ∧ x < 3`` in Lean says
that there is a real number between 2 and 3.
(We will discuss the conjunction symbol, ``∧``, in :numref:`conjunction_and_biimplication`.)
The canonical way to prove such a statement is to exhibit a real number
and show that it has the stated property.
The number 2.5, which we can enter as ``5 / 2``
or ``(5 : ℝ) / 2`` when Lean cannot infer from context that we have
the real numbers in mind, has the required property,
and the ``norm_num`` tactic can prove that it meets the description.

OMIT. -/
/- TEXT:
VSCodeで ``\ex`` で入力できる存在量化子は「存在する」というフレーズを表現するために使用されます．Leanにおいて ``∃ x : ℝ, 2 < x ∧ x < 3`` という形式的な式は2と3の間に実数が存在するということを表しています．（連言の記号 ``∧`` については :numref:`conjunction_and_biimplication` にて説明します．）このような命題を証明する標準的な方法は一つ実数を示し，その実数が指定された性質を持つことを示すことです．ここでその実数として2.5を指定し， ``norm_num`` タクティクによってこの数が必要な性質を満たしていることを証明できます．ところでこの2.5は実数のつもりで書いていますが，Leanがこれを文脈から推測できない場合は ``5 / 2`` または ``(5 : ℝ) / 2`` と入力することもできます．

.. index:: use, tactics ; use

TEXT. -/
/- OMIT:
There are a few ways we can put the information together.
Given a goal that begins with an existential quantifier,
the ``use`` tactic is used to provide the object,
leaving the goal of proving the property.
OMIT. -/
/- TEXT:
この実際の値とその性質の証明の2つをまとめる方法はいくつかあります．まず1つ目として，存在量化子で始まるゴールがある場合， ``use`` タクティクを用いてその対象を提示することで，後はその性質を証明すればいいだけにすることができます．
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
-- QUOTE.

/- OMIT:
You can give the ``use`` tactic proofs as well as data:
OMIT. -/
/- TEXT:
``use`` タクティクには値と一緒に証明を渡すこともできます:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
-- QUOTE.

/- OMIT:
In fact, the ``use`` tactic automatically tries to use available assumptions as well.
OMIT. -/
/- TEXT:
実は， ``use`` タクティクは利用可能な補題があればそれも自動的に使おうとします．
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
-- QUOTE.

/- OMIT:
Alternatively, we can use Lean's *anonymous constructor* notation
to construct a proof of an existential quantifier.
OMIT. -/
/- TEXT:
.. index:: anonymous constructor

あるいは，Leanの *無名コンストラクタ* の記法を用いて，存在命題の証明を構成することもできます．
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
-- QUOTE.

/- OMIT:
Notice that there is no ``by``; here we are giving an explicit proof term.
The left and right angle brackets,
which can be entered as ``\<`` and ``\>`` respectively,
tell Lean to put together the given data using
whatever construction is appropriate
for the current goal.
We can use the notation without going first into tactic mode:
OMIT. -/
/- TEXT:
ここで ``by`` を用いていないことに注目してください; ここでは明示的に証明項を与えているのです．それぞれ ``\<`` と ``\>`` で入力できる，左と右の角括弧を使うと，Leanは与えられたデータを現在のゴールに適した構成でまとめてくれます．初めからタクティクモードに入ることなくこの表記を使うこともできます:
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
-- QUOTE.

/- OMIT:
So now we know how to *prove* an exists statement.
But how do we *use* one?
If we know that there exists an object with a certain property,
we should be able to give a name to an arbitrary one
and reason about it.
For example, remember the predicates ``FnUb f a`` and ``FnLb f a``
from the last section,
which say that ``a`` is an upper bound or lower bound on ``f``,
respectively.
We can use the existential quantifier to say that "``f`` is bounded"
without specifying the bound:
OMIT. -/
/- TEXT:
これで存在についての命題を *証明をする* 方法がわかりました．しかしこのような命題はどのように *使う* のでしょうか？ある性質を持つ対象が存在することがわかっていれば，その対象の詳細がわからなくても名前を付けて推論することができます．例えば，前節で ``a`` が ``f`` の上界または下界であることをそれぞれ表していた ``FnUb f a`` と ``FnLb f a`` という述語を思い出してください．存在量化子を使えば具体的な上界・下界を指定せずに「 ``f`` は上界・下界を持つ」と言うことができます:
TEXT. -/
-- BOTH:
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
-- QUOTE.

/- OMIT:
We can use the theorem ``FnUb_add`` from the last section
to prove that if ``f`` and ``g`` have upper bounds,
then so does ``fun x ↦ f x + g x``.
OMIT. -/
/- TEXT:
前節の定理 ``fnUb_add`` を使って ``f`` と ``g`` が上界を持つなら ``fun x ↦ f x + g x`` も上界を持つことを証明できます．
TEXT. -/
-- BOTH:
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

-- QUOTE:
variable {f g : ℝ → ℝ}

-- EXAMPLES:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
-- QUOTE.

/- OMIT:
The ``rcases`` tactic unpacks the information
in the existential quantifier.
The annotations like ``⟨a, ubfa⟩``, written with the
same angle brackets as the anonymous constructors,
are known as *patterns*, and they describe the information
that we expect to find when we unpack the main argument.
Given the hypothesis ``ubf`` that there is an upper bound
for ``f``,
``rcases ubf with ⟨a, ubfa⟩`` adds a new variable ``a``
for an upper bound to the context,
together with the hypothesis ``ubfa`` that it has the given property.
The goal is left unchanged;
what *has* changed is that we can now use
the new object and the new hypothesis
to prove the goal.
This is a common method of reasoning in mathematics:
we unpack objects whose existence is asserted or implied
by some hypothesis, and then use it to establish the existence
of something else.

OMIT. -/
/- TEXT:
.. index:: cases, tactics ; cases

``rcases`` タクティクは存在量化子の情報を展開します．無名コンストラクタと同じ角括弧で書かれた ``⟨a, ubfa⟩`` のような構文は *パターン* と呼ばれ，メインの引数を展開した結果として期待される情報を記述します． ``f`` に上限があるという仮定 ``ubf`` が与えられたとき、 ``rcases ubf with ⟨a, ubfa⟩`` はコンテキストに上限を表す新しい変数 ``a`` を，それが与えられた性質を持つという仮定 ``ubfa`` とともに追加します．このときゴールは変更されません; 変更 *された* のは新しい対象と新しい仮定を使用してゴールを証明できるようになったことです．これは数学において一般的な推論の手法です: なにかしらの仮説から存在を主張、もしくは示唆されたときにその対象を展開し，それを使って他の何かの存在を証明するのです．

TEXT. -/
/- OMIT:
Try using this method to establish the following.
You might find it useful to turn some of the examples
from the last section into named theorems,
as we did with ``fn_ub_add``,
or you can insert the arguments directly
into the proofs.
OMIT. -/
/- TEXT:
この手法を用いて次を証明してみましょう． ``fn_ub_add`` の証明でやったように前節のいくつかの例を名前付きの定理にしたり，引数を証明に直接入れたりすると証明に役立つかもしれません．
TEXT. -/
-- QUOTE:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, lbfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (lbfa x) h

/- OMIT:
The "r" in ``rcases`` stands for "recursive," because it allows
us to use arbitrarily complex patterns to unpack nested data.
The ``rintro`` tactic
is a combination of ``intro`` and ``rcases``:
OMIT. -/
/- TEXT:
.. index:: rintro, tactics ; rintro, rcases, tactics ; rcases

``rcases`` の ``r`` は 「recursive（再帰的）」の略で，入れ子になっているデータを展開するために任意の複雑なパターンを使用することができます． ``rintro`` タクティクは ``intro`` と ``rcases`` を組み合わせたものです:
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- OMIT:
In fact, Lean also supports a pattern-matching fun
in expressions and proof terms:
OMIT. -/
/- TEXT:
実は，Leanは式と証明項中でのfunによるパターンマッチもサポートしています:
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

-- BOTH:
end

/- OMIT:
The task of unpacking information in a hypothesis is
so important that Lean and Mathlib provide a number of
ways to do it. For example, the ``obtain`` tactic provides suggestive syntax:
OMIT. -/
/- TEXT:
仮定から情報を取り出す作業はとても重要であるため，LeanとMathlibはこのための方法をいくつも提供しています．例えば ``obtain`` タクティクは直感的な記法を提供します:
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- OMIT:
Think of the first ``obtain`` instruction as matching the "contents" of ``ubf``
with the given pattern and assigning the components to the named variables.
``rcases`` and ``obtain`` are said to ``destruct`` their arguments, though
there is a small difference in that ``rcases`` clears ``ubf`` from the context
when it is done, whereas it is still present after ``obtain``.

OMIT. -/
/- TEXT:
1つ目の ``obtain`` 命令は与えられたパターンをもとに ``ubf`` の「中身」のパターンマッチを行い，その構成要素を名前のついた変数に代入すると考えてください． ``rcases`` と ``obtain`` はどちらも引数を ``destruct`` するといえますが， ``rcases`` は使用すると引数に渡した ``ubf`` がローカルコンテキストから消えてしまうのに対し， ``obtain`` ではそのまま残るという小さな違いがあります．

TEXT. -/
/- OMIT:
Lean also supports syntax that is similar to that used in other functional programming
languages:
OMIT. -/
/- TEXT:
Leanは他の関数型言語で使用されている構文と同様のものもサポートしています:
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- OMIT:
In the first example, if you put your cursor after ``cases ubf``,
you will see that the tactic produces a single goal, which Lean has tagged
``intro``. (The particular name chosen comes from the internal name for
the axiomatic primitive that builds a proof of an existential statement.)
The ``case`` tactic then names the components. The second example is similar,
except using ``next`` instead of ``case`` means that you can avoid mentioning
``intro``. The word ``match`` in the last two examples highlights that
what we are doing here is what computer scientists call "pattern matching."
Notice that the third proof begins by ``by``, after which the tactic version
of ``match`` expects a tactic proof on the right side of the arrow.
The last example is a proof term: there are no tactics in sight.

OMIT. -/
/- TEXT:
1つ目の例にて ``cases ubf`` の後ろにカーソルを置くと，このタクティクによって ``intro`` というタグを付けられた1つのゴールが生成されていることがわかるでしょう．（この ``intro`` という名前は存在命題を表すLeanの公理的プリミティブの内部的な名前に由来しています．）これに続く ``case`` タクティクがこのコンポーネントに名前を付けています．2つ目の例も似ていますが， ``case`` の代わりに ``next`` を使うことで， ``intro`` に言及することを避けることができます．最後の2つの例の ``match`` という単語はここで行っていることが計算機科学において「パターンマッチング」と呼ばれているものであることを強調しています．3つ目の証明は ``by`` で始まっていることに注目してください．タクティクバージョンの ``match`` の矢印の右側にはタクティクによる証明が来ることが期待されます．最後の例は証明項です: ここではタクティクは一つも見当たりません．

TEXT. -/
/- OMIT:
For the rest of this book, we will stick to ``rcases``, ``rintros``, and ``obtain``,
as the preferred ways of using an existential quantifier.
But it can't hurt to see the alternative syntax, especially if there is
a chance you will find yourself in the company of computer scientists.

OMIT. -/
/- TEXT:
本書ではこれ以降 ``rcases`` と ``rintro`` ， ``obtain`` を存在量化子を扱う好ましい方法として使います．しかし別の構文を見ておいても損はないでしょう．特に計算機科学者と一緒に作業をする可能性があるならなおさらです．

TEXT. -/
/- OMIT:
To illustrate one way that ``rcases`` can be used,
we prove an old mathematical chestnut:
if two integers ``x`` and ``y`` can each be written as
a sum of two squares,
then so can their product, ``x * y``.
In fact, the statement is true for any commutative
ring, not just the integers.
In the next example, ``rcases`` unpacks two existential
quantifiers at once.
We then provide the magic values needed to express ``x * y``
as a sum of squares as a list to the ``use`` statement,
and we use ``ring`` to verify that they work.
OMIT. -/
/- TEXT:
``rcases`` の使い方を例示するにあたって，数学においてすでに語り尽くされてきた事実を証明しましょう: もし2つの整数 ``x`` と ``y`` がそれぞれ2乗の和として表すことができる場合，その積 ``x * y`` も同様に表すことができます．実際にはこの命題は整数に限らず，任意の可換環に対しても成り立ちます．次の例で， ``rcases`` は2つの存在量化子を一度に展開しています．そして ``x * y`` を2乗の和として表現するために必要な具体的な値をリストとして ``use`` 文に与え， ``ring`` タクティクを使ってそれらの値が条件を満たすことを確認します．
TEXT. -/
section

-- QUOTE:
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

/- OMIT:
This proof doesn't provide much insight,
but here is one way to motivate it.
A *Gaussian integer* is a number of the form :math:`a + bi`
where :math:`a` and :math:`b` are integers and :math:`i = \sqrt{-1}`.
The *norm* of the Gaussian integer :math:`a + bi` is, by definition,
:math:`a^2 + b^2`.
So the norm of a Gaussian integer is a sum of squares,
and any sum of squares can be expressed in this way.
The theorem above reflects the fact that norm of a product of
Gaussian integers is the product of their norms:
if :math:`x` is the norm of :math:`a + bi` and
:math:`y` in the norm of :math:`c + di`,
then :math:`xy` is the norm of :math:`(a + bi) (c + di)`.
Our cryptic proof illustrates the fact that
the proof that is easiest to formalize isn't always
the most perspicuous one.
In :numref:`section_building_the_gaussian_integers`,
we will provide you with the means to define the Gaussian
integers and use them to provide an alternative proof.

OMIT. -/
/- TEXT:
この証明ではたいした洞察を得られませんでしたが，この事実に動機づけられる例が一つあります． *ガウス整数* とは :math:`a + bi` の形式で表される数で， :math:`a` と :math:`b` は整数で :math:`i = \sqrt{-1}` です．ガウス整数 :math:`a + bi` の *ノルム* は :math:`a^2 + b^2` で定義されます．したがってガウス整数のノルムは2乗の和で，どんな2乗の和も同じように表すことができるのでした．上記の定理はガウス整数の積のノルムがそれらのノルムの積であるという事実を反映します: もし :math:`x` が :math:`a + bi` のノルムで :math:`y` が :math:`c + di` のノルムであるならば， :math:`xy` は :math:`(a + bi) (c + di)` のノルムとなります．この不可解な証明は形式化するのが最も簡単な証明が最も明瞭なものになるとは限らないという事実を示しています． :numref:`section_building_the_gaussian_integers` ではガウス整数を定義し，それを用いて別の証明を行う方法を提供します．

TEXT. -/
/- OMIT:
The pattern of unpacking an equation inside an existential quantifier
and then using it to rewrite an expression in the goal
comes up often,
so much so that the ``rcases`` tactic provides
an abbreviation:
if you use the keyword ``rfl`` in place of a new identifier,
``rcases`` does the rewriting automatically (this trick doesn't work
with pattern-matching lambdas).
OMIT. -/
/- TEXT:
存在量化子中のパターンの展開とそれをゴールの式の書き換えに用いることは頻繁に行われるため， ``rcases`` タクティクは省略形を提供しています: ``rfl`` キーワードを新しい識別子の代わりに使うと， ``rcases`` が自動的に式を書き換えてくれます．（この技はラムダ抽象中のパターンマッチでは使うことができません．）
TEXT. -/
-- QUOTE:
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

end

/- OMIT:
As with the universal quantifier,
you can find existential quantifiers hidden all over
if you know how to spot them.
For example, divisibility is implicitly an "exists" statement.
OMIT. -/
/- TEXT:
全称量化子と同様，存在量化子も見分け方さえわかってしまえばあちこちに隠れていることがわかるでしょう．例えば整除関係は暗黙的な「存在」についての命題です．
TEXT. -/
-- BOTH:
section
variable {a b c : ℕ}

-- EXAMPLES:
-- QUOTE:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
-- QUOTE.

/- OMIT:
And once again, this provides a nice setting for using
``rcases`` with ``rfl``.
Try it out in the proof above.
It feels pretty good!

OMIT. -/
/- TEXT:
そして ``rcases`` を ``rfl`` と一緒に使うにあたって程よい設定も用意されています．上記の証明で試してみてください．なかなかいい感じですよ！

TEXT. -/
/- OMIT:
Then try proving the following:
OMIT. -/
/- TEXT:
そして以下の証明してみましょう:
TEXT. -/
-- QUOTE:
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

-- BOTH:
end

/- OMIT:
For another important example, a function :math:`f : \alpha \to \beta`
is said to be *surjective* if for every :math:`y` in the
codomain, :math:`\beta`,
there is an :math:`x` in the domain, :math:`\alpha`,
such that :math:`f(x) = y`.
Notice that this statement includes both a universal
and an existential quantifier, which explains
why the next example makes use of both ``intro`` and ``use``.
OMIT. -/
/- TEXT:
.. index:: surjective function

もう一つの重要な例として，関数 :math:`f : \alpha \to \beta` が *全射* であるとは終域 :math:`\beta` のすべての :math:`y` について， :math:`f(x) = y` を満たす始域 :math:`\alpha` にある :math:`x` が存在することです．この命題では全称量化子と存在量化子の両方を含むことに注目してください．これが次の例で ``intro`` と ``use`` の両方を用いている理由です．
TEXT. -/
-- BOTH:
section

open Function

-- EXAMPLES:
-- QUOTE:
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
-- QUOTE.

/- OMIT:
Try this example yourself using the theorem ``mul_div_cancel'``.:
OMIT. -/
/- TEXT:
この例を定理 ``mul_div_cancel'`` を用いて自力で証明してみましょう:
TEXT. -/
-- QUOTE:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel' _ h]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp [h] ; ring

/- OMIT:
At this point, it is worth mentioning that there is a tactic, ``field_simp``,
that will often clear denominators in a useful way.
It can be used in conjunction with the ``ring`` tactic.
OMIT. -/
/- TEXT:
.. index:: field_simp, tactic ; field_simp

この時点で ``field_simp`` というタクティクがあることに言及しておく価値があるでしょう．これは分数を整理するのに便利です．これは ``ring`` タクティクと組み合わせて使うことができます．
TEXT. -/
-- QUOTE:
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
-- QUOTE.

/- OMIT:
The next example uses a surjectivity hypothesis
by applying it to a suitable value.
Note that you can use ``rcases`` with any expression,
not just a hypothesis.
OMIT. -/
/- TEXT:
次の例は適切な値に全射な仮説を適用しています．ここで ``rcases`` が仮説だけでなくどんな式にでも使えることに注意してください．
TEXT. -/
-- QUOTE:
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
-- QUOTE.

-- BOTH:
end

/- OMIT:
See if you can use these methods to show that
the composition of surjective functions is surjective.
OMIT. -/
/- TEXT:
これらの方法を用いて，全射な関数同士の合成も全射になることを示せるかどうか見てみましょう．
TEXT. -/
-- BOTH:
section
open Function
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, rfl⟩
  rcases surjf y with ⟨x, rfl⟩
  use x

-- BOTH:
end

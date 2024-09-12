import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/- OMIT:
Induction and Recursion
-----------------------

OMIT. -/
/- TEXT:
.. _section_induction_and_recursion:

帰納法と再帰
-------------

TEXT. -/
/- OMIT:
The set of natural numbers :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`
is not only fundamentally important in its own right,
but also a plays a central role in the construction of new mathematical objects.
Lean's foundation allows us to declare *inductive types*,
which are types generated inductively by a given list of
*constructors*.
In Lean, the natural numbers are declared as follows.
OMIT. -/
/- TEXT:
自然数の集合 :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}` はその性質から数学の基礎において重要なだけでなく，新たな数学的対象の構成においても主要な役割を演じます．Leanの基礎では **帰納型** （inductive type）を宣言することができます．これは **コンストラクタ** （constructor）のリストによって帰納的に生成される型です．Leanでは自然数は次のように宣言されます．
OMIT: -/
namespace hidden

-- QUOTE:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- QUOTE.

end hidden

/- OMIT:
You can find this in the library by writing ``#check Nat`` and
then using ``ctrl-click`` on the identifier ``Nat``.
The command specifies that ``Nat`` is the datatype generated
freely and inductively by the two constructors ``zero : Nat`` and
``succ : Nat → Nat``.
Of course, the library introduces notation ``ℕ`` and ``0`` for
``nat`` and ``zero`` respectively. (Numerals are translated to binary
representations, but we don't have to worry about the details of that now.)

OMIT. -/
/- TEXT:
この型はライブラリ中のにて定義されています．その定義は ``#check Nat`` と書いてから，識別子 ``Nat`` を ``ctrl+クリック`` することで見つけることができます． ``inductive`` コマンドは ``Nat`` が2つのコンストラクタ ``zero : Nat`` と ``succ : Nat → Nat`` から自由かつ帰納的に生成されるデータ型であることを示しています．もちろん，ライブラリは ``nat`` と ``zero`` に対してそれぞれ ``ℕ`` と ``0`` という記法を導入しています．（数値は二進数表現に変換されますが，今はその詳細を気にする必要はありません．）

TEXT. -/
/- OMIT:
What "freely" means for the working mathematician is that the type
``Nat`` has an element ``zero`` and an injective successor function
``succ`` whose image does not include ``zero``.
OMIT. -/
/- TEXT:
ここで「自由」という言葉は現役の数学者にとって ``Nat`` 型が要素 ``zero`` と ``zero`` をその像に含まない単射な後続関数 ``succ`` を持つことを指します．
EXAMPLES: -/
-- QUOTE:
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h
-- QUOTE.

/- OMIT:
What the word "inductively" means for the working mathematician is that
the natural numbers comes with a principle of proof by induction
and a principle of definition by recursion.
This section will show you how to use these.

OMIT. -/
/- TEXT:
また現役の数学者にとって「帰納的」という言葉が意味するのは，自然数には帰納法による証明の原理と再帰による定義の原理が備わっているということです．この節ではこれらの使い方を紹介します．

TEXT. -/
/- OMIT:
Here is an example of a recursive definition of the factorial
function.
OMIT. -/
/- TEXT:
以下が再帰的な定義による階乗関数の例です．
BOTH: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- OMIT:
The syntax takes some getting used to.
Notice that there is no ``:=`` on the first line.
The next two lines provide the base case and inductive step
for a recursive definition.
These equations hold definitionally, but they can also
be used manually by giving the name ``fac`` to ``simp`` or ``rw``.
OMIT. -/
/- TEXT:
この構文には慣れが必要です．最初の行に ``:=`` が無いことに注目してください．そして次の2行は再帰的定義の基本ケースと帰納的なステップを展開しています．以下の等式は定義上成り立ちますが， ``fac`` を ``simp`` や ``rw`` に与えることで手動で使用することもできます．
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]
-- QUOTE.

/- OMIT:
The factorial function is actually already defined in Mathlib as
``Nat.factorial``. Once again, you can jump to it by typing
``#check Nat.factorial`` and using ``ctrl-click.``
For illustrative purposes, we will continue using ``fac`` in the examples.
The annotation ``@[simp]`` before the definition
of ``Nat.factorial`` specifies that
the defining equation should be added to the database of identities
that the simplifier uses by default.

OMIT. -/
/- TEXT:
この階乗関数はMathlibではすでに ``Nat.factorial`` として定義されています．ここでも再度 ``#check Nat.factorial`` と入力し， ``ctrl+クリック`` することでこの関数の定義にジャンプすることができます．本書では説明のため，例題では ``fac`` を引き続き使用します． ``Nat.factorial`` の定義の前にある ``@[simp]`` という注釈は， ``simp`` がデフォルトで使用する等式のデータベースにそこで定義した等式を追加することを指示します．

TEXT. -/
/- OMIT:
The principle of induction says that we can prove a general statement
about the natural numbers by proving that the statement holds of 0
and that whenever it holds of a natural number :math:`n`,
it also holds of :math:`n + 1`.
The line ``induction' n with n ih`` in the proof
below therefore results in two goals:
in the first we need to prove ``0 < fac 0``,
and in the second we have the added assumption ``ih : 0 < fac n``
and a required to prove ``0 < fac (n + 1)``.
The phrase ``with n ih`` serves to name the variable and
the assumption for the inductive hypothesis,
and you can choose whatever names you want for them.
OMIT. -/
/- TEXT:
帰納法の原理は，自然数に関する一般的な命題を証明するには，その命題が0について成り立ち，また自然数 :math:`n` について成り立つときはいつでも :math:`n + 1` についても成り立つことを証明すれば良いというものです．そのため，以下の証明の ``induction' n with n ih`` という行は2つのゴールを生み出します．1つ目は ``0 < fac 0`` を証明することであり，2つ目は ``ih : 0 < fac n`` という仮定から ``0 < fac (n + 1)`` の証明が求められます． ``with n ih`` というフレーズは帰納法で用いられる仮定の変数と仮定に名前をつけるためのもので，好きな名前をつけることができます．
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- OMIT:
The ``induction`` tactic is smart enough to include hypotheses
that depend on the induction variable as part of the
induction hypothesis.
Step through the next example to see what is going on.
OMIT. -/
/- TEXT:
``induction`` タクティクは賢いため，帰納法の変数に依存する仮定を帰納法の仮定の一部に含めることができます．これがどういうことなのか，次の例で見てみましょう．
EXAMPLES: -/
-- QUOTE:
theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right
-- QUOTE.

/- OMIT:
The following example provides a crude lower bound for the factorial
function.
It turns out to be easier to start with a proof by cases,
so that the remainder of the proof starts with the case
:math:`n = 1`.
See if you can complete the argument with a proof by induction using ``pow_succ``
or ``pow_succ'``.
OMIT. -/
/- TEXT:
次の例では階乗関数の粗い下界を示します．証明のはじめに場合分けをすると簡単になるため，証明の残りは :math:`n = 1` の場合から始まるようにします． ``pow_succ`` と ``pow_succ'`` を使いつつ，帰納法による証明で論証を完成してみましょう．
BOTH: -/
-- QUOTE:
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul _ ih
  repeat' apply Nat.succ_le_succ
  apply zero_le

-- BOTH:
-- QUOTE.
/- OMIT:
Induction is often used to prove identities involving finite sums and
products.
Mathlib defines the expressions ``Finset.sum s f`` where
``s : Finset α`` is a finite set of elements of the type ``α`` and
``f`` is a function defined on ``α``.
The codomain of ``f`` can be any type that supports a commutative,
associative addition operation with a zero element.
If you import ``Algebra.BigOperators.Basic`` and issue the command
``open BigOperators``, you can use the more suggestive notation
``∑ x in s, f x``. Of course, there is are an analogous operation and
notation for finite products.

OMIT. -/
/- TEXT:
有限の和や積を含む等式を証明するために帰納法がよく用いられます．Mathlibは ``Finset.sum s f`` という式を定義しています．ここで ``s : Finset α`` は ``α`` 型の要素の有限集合であり， ``f`` は ``α`` で定義される関数です． ``f`` の余域は零要素を持つ可換で結合的な加法をサポートする任意の型です． ``Algebra.BigOperators.Basic`` をインポートして ``open BigOperators`` コマンドを実行することで，より示唆的な表記である ``∑ x in s, f x`` を使うことができます．もちろん有限積についても同様の操作と表記法があります．

TEXT. -/
/- OMIT:
We will talk about the ``Finset`` type and the operations
it supports in the next section, and again in a later chapter.
For now, we will only make use
of ``Finset.range n``, which is the finite set of natural numbers
less than ``n``.
OMIT. -/
/- TEXT:
この ``Finset`` 型とそれがサポートする演算については次の節で説明します．現時点では ``n`` より小さい自然数の有限集合である ``Finset.range n`` のみ取り扱います．
BOTH: -/
section

-- QUOTE:
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

-- EXAMPLES:
#check Finset.sum s f
#check Finset.prod s f

-- BOTH:
open BigOperators
open Finset

-- EXAMPLES:
example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl
-- QUOTE.

/- OMIT:
The facts ``Finset.sum_range_zero`` and ``Finset.sum_range_succ``
provide a recursive description of summation up to :math:`n`,
and similarly for products.
OMIT. -/
/- TEXT:
``Finset.sum_range_zero`` と ``Finset.sum_range_succ`` は， :math:`n` までの総和を再帰的に記述するもので，積についても同様のものがあります．
EXAMPLES: -/
-- QUOTE:
example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n
-- QUOTE.

/- OMIT:
The first identity in each pair holds definitionally, which is to say,
you can replace the proofs by ``rfl``.

OMIT. -/
/- TEXT:
各ペアの1つ目の等式は定義上成り立ちます．つまり証明を ``rfl`` で置き換えることができます．

TEXT. -/
/- OMIT:
The following expresses the factorial function that we defined as a product.
OMIT. -/
/- TEXT:
以下は先程定義した階乗関数を積として表現したものになります．
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]
-- QUOTE.

/- OMIT:
The fact that we include ``mul_comm`` as a simplification rule deserves
comment.
It should seem dangerous to simplify with the identity ``x * y = y * x``,
which would ordinarily loop indefinitely.
Lean's simplifier is smart enough to recognize that, and applies the rule
only in the case where the resulting term has a smaller value in some
fixed but arbitrary ordering of the terms.
The following example shows that simplifying using the three rules
``mul_assoc``, ``mul_comm``, and ``mul_left_comm``
manages to identify products that are the same up to the
placement of parentheses and ordering of variables.
OMIT. -/
/- TEXT:
特筆すべきは単純化のルールとして ``mul_comm`` がふくまれていることです．等式 ``x * y = y * x`` を使って単純化しようとすると無限ループに陥ってしまうように思われるため，この等式で単純化するのは危険だと思われるでしょう．Leanの ``simp`` はその点を十分に認識しており，ある程度固定した上で任意の順序で項を並べたときに結果として得られる項の値が小さくなる場合にのみこの規則を適用するようにしています．次の例では ``mul_asso`` ， ``mul_comm`` ， ``mul_left_comm`` の3つのルールを使って簡約すると括弧の位置や変数の順序まで同じようにできることを示しています．
EXAMPLES: -/
-- QUOTE:
example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]
-- QUOTE.

/- OMIT:
Roughly, the rules work by pushing parentheses to the right
and then re-ordering the expressions on both sides until they
both follow the same canonical order. Simplifying with these
rules, and the corresponding rules for addition, is a handy trick.

OMIT. -/
/- TEXT:
大まかには，括弧を右に押し出し，両辺の式が同じ標準的な順序になるまで並べ替えることでこのルールは機能します．これらのルールとそれに対応する加法のルールを使って単純化するのは便利なテクニックです．

TEXT. -/
/- OMIT:
Returning to summation identities, we suggest stepping through the following proof
that the sum of the natural numbers up to and including :math:`n` is
:math:`n (n + 1) / 2`.
The first step of the proof clears the denominator.
This is generally useful when formalizing identities,
because calculations with division generally have side conditions.
(It is similarly useful to avoid using subtraction on the natural numbers when possible.)
OMIT. -/
/- TEXT:
和の等式の話に戻ると， :math:`n` までの自然数の和が :math:`n (n + 1) / 2` となることの証明は次のようになります．証明の最初のステップでは，まず分母を消去します．これは等式を形式化する際に一般的に便利です．なぜなら除算は一般的に副次的な条件を持つからです．（同様に可能な限り自然数に対して減算を使わないようにすることも有効です．）
EXAMPLES: -/
-- QUOTE:
theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
-- QUOTE.

/- OMIT:
We encourage you to prove the analogous identity for sums of squares,
and other identities you can find on the web.
OMIT. -/
/- TEXT:
ここで上記に似ている平方の和やググって出てくる様々な等式を証明することをお勧めします．
BOTH: -/
-- QUOTE:
theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 6, ← ih]
  ring
-- QUOTE.

-- BOTH:
end

/- OMIT:
In Lean's core library, addition and multiplication are themselves defined
using recursive definitions,
and their fundamental properties are established using induction.
If you like thinking about foundational topics like that,
you might enjoy working through proofs
of the commutativity and associativity of multiplication and addition
and the distributivity of multiplication over addition.
You can do this on a copy of the natural numbers
following the outline below.
Notice that we can use the ``induction`` tactic with ``MyNat``;
Lean is smart enough to know to
use the relevant induction principle (which is, of course,
the same as that for ``Nat``).

OMIT. -/
/- TEXT:
Leanのコアのライブラリでは，加法と乗法は再帰定義を使って定義されており，それらについての基本的な性質は帰納法を使って確立されています．もしこのような基礎的な話題に興味があるなら，乗法と加法の可換性と結合性，乗法と加法の分配性の証明に取り組むのも楽しいでしょう．これを自前定義の自然数を用いて行うには以下のような流れになります．ここで ``MyNat`` で ``induction`` を使うことができることに注意してください．Leanは賢いので関連する帰納法の原理（もちろん ``Nat`` の原理と同じです）が使えることを知っています．

TEXT. -/
/- OMIT:
We start you off with the commutativity of addition.
A good rule of thumb is that because addition and multiplication
are defined by recursion on the second argument,
it is generally advantageous to do proofs by induction on a variable
that occurs in that position.
It is a bit tricky to decide which variable to use in the proof
of associativity.

OMIT. -/
/- TEXT:
まずは加法の可換性から初めましょう．経験的には加法と乗法は第二引数に対する再帰によって定義されるので，その位置に現れる変数に対する帰納法によって証明を行うのが一般的に有利です．これに対し結合則の証明でどの変数で再帰するか決めるのは少し難しいです．

TEXT. -/
/- OMIT:
It can be confusing to write things without the usual notation
for zero, one, addition, and multiplication.
We will learn how to define such notation later.
Working in the namespace ``MyNat`` means that we can write
``zero`` and ``succ`` rather than ``MyNat.zero`` and ``MyNat.succ``,
and that these interpretations of the names take precedence over
others.
Outside the namespace, the full name of the ``add`` defined below,
for example, is ``MyNat.add``.

OMIT. -/
/- TEXT:
0，1，加法，乗法の通常の表記を使わずに証明を進めていくのは混乱を起こすことがあります．こういう場合に記法を定義するやり方がありますが，それは後ほど学びます．名前空間 ``MyNat`` で作業するということは， ``MyNat.zero`` や ``MyNat.succ`` ではなく， ``zero`` や ``succ`` と書くことができるということであり，これらの名前の解釈が他のものより優先されることを意味します．名前空間の外では，例えば以下で定義する ``add`` の完全な名前は ``MyNat.add`` となります．

TEXT. -/
/- OMIT:
If you find that you *really* enjoy this sort of thing, try defining
truncated subtraction and exponentiation and proving some of their
properties as well.
Remember that truncated subtraction cuts off at zero.
To define that, it is useful to define a predecessor function, ``pred``,
that subtracts one from any nonzero number and fixes zero.
The function ``pred`` can be defined by a simple instance of recursion.
OMIT. -/
/- TEXT:
もしこれらを考えることが本当に **楽しい** と感じたら，切り捨てる引き算と指数を定義し，それらの性質をいくつか証明してみましょう．切り捨て減算はゼロで切り捨てる計算方法です．これを定義するためには0ではない数から1を引き，0を固定する先行関数 ``pred`` を定義するのが便利です．関数 ``pred`` は単純な再帰のインスタンスで定義できます．
BOTH: -/
-- QUOTE:
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, ih]
  rfl

-- BOTH:
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, mul, mul, ih, add_assoc]

-- BOTH:
theorem zero_mul (n : MyNat) : mul zero n = zero := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, ih]
  rfl

-- BOTH:
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add]
  rfl

-- BOTH:
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rw [zero_mul]
    rfl
  rw [mul, ih, succ_mul]

-- BOTH:
end MyNat
-- QUOTE.

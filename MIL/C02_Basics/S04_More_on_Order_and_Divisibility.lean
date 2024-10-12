-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

/- OMIT:
More examples using apply and rw
--------------------------------

OMIT. -/
/- TEXT:
.. _more_on_order_and_divisibility:

applyとrwをさらに活用する
--------------------------

.. index:: min, max

TEXT. -/
/- OMIT:
The ``min`` function on the real numbers is uniquely characterized
by the following three facts:
OMIT. -/
/- TEXT:
実数上の関数 ``min`` は以下の3つの事実により一意に特徴付けられます:
TEXT. -/
-- BOTH:
section
variable (a b c d : ℝ)

-- QUOTE:
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- QUOTE.

/- OMIT:
Can you guess the names of the theorems that characterize
``max`` in a similar way?

OMIT. -/
/- TEXT:
これらから ``max`` 関数を同じように特徴づける定理の名称が想像つくでしょうか？

TEXT. -/
/- OMIT:
Notice that we have to apply ``min`` to a pair of arguments ``a`` and ``b``
by writing ``min a b`` rather than ``min (a, b)``.
Formally, ``min`` is a function of type ``ℝ → ℝ → ℝ``.
When we write a type like this with multiple arrows,
the convention is that the implicit parentheses associate
to the right, so the type is interpreted as ``ℝ → (ℝ → ℝ)``.
The net effect is that if ``a`` and ``b`` have type ``ℝ``
then ``min a`` has type ``ℝ → ℝ`` and
``min a b`` has type ``ℝ``, so ``min`` acts like a function
of two arguments, as we expect. Handling multiple
arguments in this way is known as *currying*,
after the logician Haskell Curry.

OMIT. -/
/- TEXT:
ここで ``min`` を引数 ``a`` と ``b`` のペアに適用するにあたり ``min (a, b)`` ではなく ``min a b`` と書かなければならない点に注意してください．形式的には ``min`` は ``ℝ → ℝ → ℝ`` 型の関数です．このように複数の矢印を用いた型を記述する場合，この矢印は慣例的に右結合として ``ℝ → (ℝ → ℝ)`` と解釈されます．この結果， ``a`` と ``b`` が ``ℝ`` 型の場合， ``min a`` は ``ℝ → ℝ`` 型となり， ``min a b`` は ``ℝ`` 型を持つため ``min`` は期待通り2引数の関数として振る舞います．このような方法で複数の引数を取り扱うことは，論理学者のHaskell Curryにちなんで **カリー化** （currying）として知られています．

TEXT. -/
/- OMIT:
The order of operations in Lean can also take some getting used to.
Function application binds tighter than infix operations, so the
expression ``min a b + c`` is interpreted as ``(min a b) + c``.
With time, these conventions will become second nature.

OMIT. -/
/- TEXT:
またLeanの演算子の優先順位についても慣れが必要です．関数適用は中置演算子より強く式と結びつくため， ``min a b + c`` という式は ``(min a b) + c`` と解釈されます．これらの慣例は時間が経てば自然と身につくでしょう．

TEXT. -/
/- OMIT:
Using the theorem ``le_antisymm``, we can show that two
real numbers are equal if each is less than or equal to the other.
Using this and the facts above,
we can show that ``min`` is commutative:
OMIT. -/
/- TEXT:
``le_antisymm`` を使用することで，2つの実数 ``a, b`` が等しいのは ``a ≤ b`` かつ ``a ≥ b`` の場合であることを示すことができます．これと上記の事実を使えば ``min`` が可換であることを示すことができます:
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
-- QUOTE.

/- OMIT:
Here we have used dots to separate proofs of
different goals.
Our usage is inconsistent:
at the outer level,
we use dots and indentation for both goals,
whereas for the nested proofs,
we use dots only until a single goal remains.
Both conventions are reasonable and useful.
We also use the ``show`` tactic to structure
the proof
and indicate what is being proved in each block.
The proof still works without the ``show`` commands,
but using them makes the proof easier to read and maintain.

OMIT. -/
/- TEXT:
.. index:: show, tactics ; show

ここでは異なるゴールの証明を区切るためにドットを用いています．ここでのドットの使い方は一貫していません:外側のレベルでは両方のゴールにドットとインデントを用いていますが，入れ子になった証明ではゴールが一つになったらドットは使用していません．どちらの書き方も合理的で有用です．また ``show`` タクティクを使って証明を構成し，各ブロックで何を証明したいかを明示的にしています． ``show`` コマンドを使わなくても証明は機能しますが，これにより証明が読みやすくなり，保守もしやすくなります．

TEXT. -/
/- OMIT:
It may bother you that the proof is repetitive.
To foreshadow skills you will learn later on,
we note that one way to avoid the repetition
is to state a local lemma and then use it:
OMIT. -/
/- TEXT:
この証明では同じようなことを繰り返していることが気になるかもしれません．あとで詳しく学びますが，繰り返しを避ける一つの方法として局所的な補題を示して利用する方法を記します:
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
-- QUOTE.

/- OMIT:
We will say more about the universal quantifier in
:numref:`implication_and_the_universal_quantifier`,
but suffice it to say here that the hypothesis
``h`` says that the desired inequality holds for
any ``x`` and ``y``,
and the ``intro`` tactic introduces an arbitrary
``x`` and ``y`` to establish the conclusion.
The first ``apply`` after ``le_antisymm`` implicitly
uses ``h a b``, whereas the second one uses ``h b a``.

OMIT. -/
/- TEXT:
全称量化子については :numref:`implication_and_the_universal_quantifier` で詳しく述べますが，今の時点では仮説 ``h`` は任意の ``x`` と ``y`` に対して目的の不等式が成り立っていて，``intro`` タクティクは任意の ``x`` と ``y`` を導入して結論を導いていると理解できていれば十分です． ``le_antisymm`` のあとの最初の ``apply`` は暗黙的に ``h a b`` を用いており，2つめでは ``h b a`` を使っています．

.. index:: repeat, tactics ; repeat

TEXT. -/
/- OMIT:
Another solution is to use the ``repeat`` tactic,
which applies a tactic (or a block) as many times
as it can.
OMIT. -/
/- TEXT:
繰り返しを避ける他の手段として ``repeat`` タクティクを用いる方法もあります．これはタクティク（や証明のブロック）をできるだけ繰り返し適用するタクティクです．
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
-- QUOTE.

/- OMIT:
We encourage you to prove the following as exercises.
You can use either of the tricks just described to shorten the first.
OMIT. -/
/- TEXT:
以下を演習問題として証明することをお勧めします。最初に説明した技法のいずれかを使って短縮することができます。
TEXT. -/
-- QUOTE:
-- BOTH:
example : max a b = max b a := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- BOTH:
example : min (min a b) c = min a (min b c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right
-- QUOTE.

/- OMIT:
Of course, you are welcome to prove the associativity of ``max`` as well.

OMIT. -/
/- TEXT:
もちろん， ``max`` 関数の結合性を証明してみるのも良いでしょう．

TEXT. -/
/- OMIT:
It is an interesting fact that ``min`` distributes over ``max``
the way that multiplication distributes over addition,
and vice-versa.
In other words, on the real numbers, we have the identity
``min a (max b c) = max (min a b) (min a c)``
as well as the corresponding version with ``max`` and ``min``
switched.
But in the next section we will see that this does *not* follow
from the transitivity and reflexivity of ``≤`` and
the characterizing properties of ``min`` and ``max`` enumerated above.
We need to use the fact that ``≤`` on the real numbers is a *total order*,
which is to say,
it satisfies ``∀ x y, x ≤ y ∨ y ≤ x``.
Here the disjunction symbol, ``∨``, represents "or".
In the first case, we have ``min x y = x``,
and in the second case, we have ``min x y = y``.
We will learn how to reason by cases in :numref:`disjunction`,
but for now we will stick to examples that don't require the case split.

OMIT. -/
/- TEXT:
乗法が加法に対して分配法則を満たすように ``min`` 関数が ``max`` に対して分配法則を満たし，その逆も成り立つというのは興味深い事実です．言い換えれば，実数上において ``min a (max b c) = max (min a b) (min a c)`` が成り立ち，この式の ``max`` と ``min`` を入れ替えた同様の式も成り立つということです．しかし次の節では， ``≤`` の推移性と反射性，そして上記で示した ``min`` と ``max`` を特徴付ける性質からこれが **成り立たない** ことを見ていきます．この性質を示すには実数上の関係 ``≤`` が **全順序** （total order）であること，つまり ``∀ x y, x ≤ y ∨ y ≤ x`` という性質が成り立つという事実を利用する必要があります．ここで記号 ``∨`` は選言記号で「または」を表します．最初のケースでは ``min x y = x`` となり，2番めのケースでは ``min x y = y`` となります．場合分けを使って証明する方法は :numref:`disjunction` で学びますが，現時点では場合分けをする必要のない例で説明します．

TEXT. -/
/- OMIT:
Here is one such example:
OMIT. -/
/- TEXT:
以下に一つ例を挙げましょう:
TEXT. -/
-- QUOTE:
-- BOTH:
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

-- BOTH:
example : min a b + c = min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]
-- QUOTE.

/- OMIT:
It is clear that ``aux`` provides one of the two inequalities
needed to prove the equality,
but applying it to suitable values yields the other direction
as well.
As a hint, you can use the theorem ``add_neg_cancel_right``
and the ``linarith`` tactic.

OMIT. -/
/- TEXT:
ここで等式を示すために必要な2つの不等式のうち ``aux`` がその片方を示しているのは明白ですが，適切な値に適用することでもう一方向の不等式も得られます．ヒント: 定理 ``add_neg_cancel_right`` と ``linarith`` タクティクが役に立つでしょう．

.. index:: absolute value

TEXT. -/
/- OMIT:
Lean's naming convention is made manifest
in the library's name for the triangle inequality:
OMIT. -/
/- TEXT:
Leanの命名規則はライブラリ中の三角不等式の名前にはっきりと現れています:
TEXT. -/
-- QUOTE:
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
-- QUOTE.

/- OMIT:
Use it to prove the following variant, using also ``add_sub_cancel_right``:
OMIT. -/
/- TEXT:
これを用いて以下の類似の定理を証明しましょう．ここでは ``add_sub_cancel_right`` を用います：
TEXT. -/
-- QUOTE:
-- BOTH:
example : |a| - |b| ≤ |a - b| :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]


-- alternatively
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

-- BOTH:
end
-- QUOTE.

/- OMIT:
See if you can do this in three lines or less.
You can use the theorem ``sub_add_cancel``.

.. index:: divisibility

OMIT. -/
/- TEXT:
この証明を3行以内にできるかどうか試してみましょう．この証明では ``sub_add_cancel`` を用いると良いでしょう．

.. index:: divisibility

TEXT. -/
/- OMIT:
Another important relation that we will make use of
in the sections to come is the divisibility relation
on the natural numbers, ``x ∣ y``.
Be careful: the divisibility symbol is *not* the
ordinary bar on your keyboard.
Rather, it is a unicode character obtained by
typing ``\|`` in VS Code.
By convention, Mathlib uses ``dvd``
to refer to it in theorem names.
OMIT. -/
/- TEXT:
本節で取り上げるもう一つの重要な関係として ``x ∣ y`` で表される自然数の整除関係があります．要注意: 整除記号はキーボードにある普通の縦棒 **ではありません** ．これはVSCodeでは ``\|`` で入力されるUnicode文字です．慣例としてMathlibでは定理名の中で整除関係を表すのに ``dvd`` を使用します．
TEXT. -/
-- BOTH:
section
variable (w x y z : ℕ)

-- QUOTE:
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left
-- QUOTE.

/- OMIT:
In the last example, the exponent is a natural
number, and applying ``dvd_mul_left``
forces Lean to expand the definition of ``x^2`` to
``x^1 * x``.
See if you can guess the names of the theorems
you need to prove the following:
OMIT. -/
/- TEXT:
最後の例では，指数が自然数であり ``dvd_mul_left`` を ``apply`` することでLeanに ``x^2`` の定義を ``x^1 * x`` に展開させています．次の例を証明するのに必要な定理名を推測してみましょう:
TEXT. -/
-- QUOTE:
-- BOTH:
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

-- BOTH:
end
-- QUOTE.

/- OMIT:
With respect to divisibility, the *greatest common divisor*,
``gcd``, and least common multiple, ``lcm``,
are analogous to ``min`` and ``max``.
Since every number divides ``0``,
``0`` is really the greatest element with respect to divisibility:
OMIT. -/
/- TEXT:
.. index:: gcd, lcm

整除について **最大公約数** （greatest common divisor） ``gcd`` と **最小公倍数** （least common multiple） ``lcm`` はそれぞれ ``min`` と ``max`` に対応しています．すべての数は ``0`` を割り切るため，実際 ``0`` は整除において最大の要素です:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
-- QUOTE.

/- OMIT:
See if you can guess the names of the theorems you will need to
prove the following:
OMIT. -/
/- TEXT:
次の例についても証明に必要な定理名を推測してみましょう:
TEXT. -/
-- QUOTE:
-- BOTH:
example : Nat.gcd m n = Nat.gcd n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
-- QUOTE.

-- BOTH:
end

/- OMIT:
Hint: you can use ``dvd_antisymm``, but if you do, Lean will
complain that the expression is ambiguous between the generic
theorem and the version ``Nat.dvd_antisymm``,
the one specifically for the natural numbers.
You can use ``_root_.dvd_antisymm`` to specify the generic one;
either one will work.
OMIT. -/
/- TEXT:
ヒント: ここでは ``dvd_antisymm`` を使うこともできますが，その場合Leanは一般的な定理と，自然数専用の ``Nat.dvd_antisymm`` とどちらを用いるのか曖昧であると文句を言ってきます．どちらでも証明できますが，もし一般的な定理のほうを用いたい場合は ``_root_.dvd_antisymm`` で指定可能です．
TEXT. -/

-- OMIT: fix this: protect `dvd_antisymm`.

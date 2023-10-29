-- BOTH:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

/- OMIT:
Using Theorems and Lemmas
-------------------------

OMIT. -/
/- TEXT:
.. _using_theorems_and_lemmas:

定理と補題を利用する
---------------------

.. index:: inequalities

TEXT. -/
/- OMIT:
Rewriting is great for proving equations,
but what about other sorts of theorems?
For example, how can we prove an inequality,
like the fact that :math:`a + e^b \le a + e^c` holds whenever :math:`b \le c`?
We have already seen that theorems can be applied to arguments and hypotheses,
and that the ``apply`` and ``exact`` tactics can be used to solve goals.
In this section, we will make good use of these tools.

OMIT. -/
/- TEXT:
書き換えは等式を証明するのには最適ですが，等式以外の定理についてはどうでしょうか？例えば， :math:`b \le c` であるときに :math:`a + e^b \le a + e^c` が成り立つというような不等式はどのように証明するのでしょうか？定理が何かしらの引数や仮説に適用でき， ``apply`` や ``exact`` タクティクを用いてゴールを解決するために使うことができることはこれまでに見てきました．このセクションでは，これらのツールをうまく使っていきましょう．

TEXT. -/
/- OMIT:
Consider the library theorems ``le_refl`` and ``le_trans``:
OMIT. -/
/- TEXT:
Mathlibにある定理 ``le_refl`` と ``le_trans`` について考えてみましょう．
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- QUOTE.

/- OMIT:
As we explain in more detail in  :numref:`implication_and_the_universal_quantifier`,
the implicit parentheses in the statement of ``le_trans``
associate to the right, so it should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``.
The library designers have set the arguments ``a``, ``b`` and ``c`` to ``le_trans`` implicit,
so that Lean will *not* let you provide them explicitly (unless you
really insist, as we will discuss later).
Rather, it expects to infer them from the context in which they are used.
For example, when hypotheses ``h : a ≤ b`` and  ``h' : b ≤ c``
are in the context,
all the following work:
OMIT. -/
/- TEXT:
詳しくは :numref:`implication_and_the_universal_quantifier` で説明しますが，命題 ``le_trans`` について ``→`` は右結合であるためこの命題は ``a ≤ b → (b ≤ c → a ≤ c)`` と解釈されます．ライブラリの設計者は ``le_trans`` の引数 ``a`` ， ``b`` ， ``c`` を暗黙に設定したため，Leanはこれらの引数を（このあと議論するように，実際に要求する場合を覗いて）明示的には利用者に提供 *しません* ．むしろこれらの引数が使用されている文脈から推測することを期待します．例えば，仮説 ``h : a ≤ b`` と ``h' : b ≤ c`` が文脈にある場合，これらは以下のように働きます:
TEXT. -/
section
-- QUOTE:
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
-- QUOTE.

end

/- OMIT:
The ``apply`` tactic takes a proof of a general statement or implication,
tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals.
If the given proof matches the goal exactly
(modulo *definitional* equality),
you can use the ``exact`` tactic instead of ``apply``.
So, all of these work:
OMIT. -/
/- TEXT:
.. index:: apply, tactics ; apply, exact, tactics ; exact

``apply`` タクティクは一般的な命題や含意の証明を受け取り，結論を現在のゴールにマッチさせようとし，もし仮定が残る場合はそれを新しいゴールとします．もし与えられた証明がゴールに正確に一致する場合（ *定義的に* 等しい変形が残っている場合も含みます），``apply``　の代わりに ``exact`` タクティクを使うことができます．これらのことから以下のすべての証明が機能します．
TEXT. -/
-- QUOTE:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
-- QUOTE.

/- OMIT:
In the first example, applying ``le_trans``
creates two goals,
and we use the dots to indicate where the proof of each begins.
The dots are optional, but they serve to *focus* the goal:
within the block introduced by the dot, only one goal is visible,
and it must be completed before the end of the block.
Here we end the first block by starting a new one with another dot.
We could just as well have decreased the indentation.
In the fourth example and in the last example,
we avoid going into tactic mode entirely:
``le_trans h₀ h₁`` and ``le_refl x`` are the proof terms we need.

OMIT. -/
/- TEXT:
最初の例では， ``le_trans`` を適用することで2つのゴールが作成され，それぞれの証明がどこから始まるかをピリオドで表しています．ここでピリオドは使用しなくても証明は通りますが，ピリオドを使用することでゴールに *焦点があてられます* :ピリオドが示すブロック内ではゴールは一つしかinfoviewに表示されず，かつこのゴールはブロックが終わるまでに完了しなければなりません．ここでは最初のブロックは次の行から始まる別のピリオドによって終了しています．この例に対し，インデントすることなく証明することも可能です．4つ目と最後の例では完全にタクティクモードを避けています: ``le_trans h₀ h₁`` と ``le_refl x`` がまさに証明に必要な項です．

TEXT. -/
/- OMIT:
Here are a few more library theorems:
OMIT. -/
/- TEXT:
ここでさらにいくつかライブラリの定理を紹介しましょう:
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- QUOTE.

/- OMIT:
Use them together with ``apply`` and ``exact`` to prove the following:
OMIT. -/
/- TEXT:
これらを ``apply`` と ``exact`` を用いることで以下を証明しましょう:
TEXT. -/
-- Try this.
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

/- OMIT:
In fact, Lean has a tactic that does this sort of thing automatically:
OMIT. -/
/- TEXT:
.. index:: linarith, tactics ; linarith

実際に，Leanにはこのようなことを自動的に行うタクティクがあります:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- QUOTE.

/- OMIT:
The ``linarith`` tactic is designed to handle *linear arithmetic*.
OMIT. -/
/- TEXT:
``linarith`` タクティクは *線形演算* を扱うように設計されています．
TEXT. -/
section

-- QUOTE:
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
-- QUOTE.

end

/- OMIT:
In addition to equations and inequalities in the context,
``linarith`` will use additional inequalities that you pass as arguments.
In the next example, ``exp_le_exp.mpr h'`` is a proof of
``exp b ≤ exp c``, as we will explain in a moment.
Notice that, in Lean, we write ``f x`` to denote the application
of a function ``f`` to the argument ``x``,
exactly the same way we write ``h x`` to denote the result of
applying a fact or theorem ``h`` to the argument ``x``.
Parentheses are only needed for compound arguments,
as in ``f (x + y)``. Without the parentheses, ``f x + y``
would be parsed as ``(f x) + y``.
OMIT. -/
/- TEXT:
文脈中にある等式と不等式に加えて， ``linarith`` は引数として渡した追加の不等式を使用します．次の例ではこのあとすぐ説明するように， ``exp_le_exp.mpr h'`` が ``exp b ≤ exp c`` の証明です．ここでLeanにおいて引数 ``x`` に関数 ``f`` を適用した結果を表すために ``f x`` と記載しますが，これは引数 ``x`` に事実や定理 ``h`` を適用した結果を表すために ``h x`` と書くのと全く同じです．他の一般的なプログラミング言語のように関数適用に括弧は不要ですが， ``f (x + y)`` のように複合的な引数の場合には必要となります．この場合括弧がないと， ``f x + y`` は ``(f x) + y`` と解釈されます．
TEXT. -/
-- QUOTE:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
-- QUOTE.

/- OMIT:
Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.
OMIT. -/
/- TEXT:
.. index:: exponential, logarithm

ここで実数上の不等式を立てるために有用なライブラリの定理をさらに紹介しましょう．
TEXT. -/
-- QUOTE:
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
-- QUOTE.

/- OMIT:
Some of the theorems, ``exp_le_exp``, ``exp_lt_exp``, and ``log_le_log``
use a *bi-implication*, which represents the
phrase "if and only if."
(You can type it in VS Code with ``\lr`` of ``\iff``).
We will discuss this connective in greater detail in the next chapter.
Such a theorem can be used with ``rw`` to rewrite a goal to
an equivalent one:
OMIT. -/
/- TEXT:
上記の定理の中で， ``exp_le_exp`` と ``exp_lt_exp`` ， ``log_le_log`` は必要十分条件を意味する *双方向の含意* を用いています．（VSCodeでは ``\lr`` か ``\iff`` で入力することができます）この接続詞については次の章で詳しく説明することとします．このような定理は ``rw`` と一緒に使うことで，ゴールをそれと等価なものに書き換えることができます:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
-- QUOTE.

/- OMIT:
In this section, however, we will use the fact that if ``h : A ↔ B``
is such an equivalence,
then ``h.mp`` establishes the forward direction, ``A → B``,
and ``h.mpr`` establishes the reverse direction, ``B → A``.
Here, ``mp`` stands for "modus ponens" and
``mpr`` stands for "modus ponens reverse."
You can also use ``h.1`` and ``h.2`` for ``h.mp`` and ``h.mpr``,
respectively, if you prefer.
Thus the following proof works:
OMIT. -/
/- TEXT:
しかし，本節では ``h : A ↔ B`` がこのような同値である場合， ``h.mp`` を順方向である ``A → B`` として，``h.mpr`` を逆方向である ``B → A`` として成立させているという事実の方を使っていきます．ここで ``mp`` は"modus ponens"を表し， ``mpr`` は"modus ponens reverse"を表しています．また ``h.mp`` と ``h.mpr`` はそれぞれ ``h.1`` と ``h.2`` を代わりに使うこともできます．以上から次の証明が成り立ちます:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-- QUOTE.

/- OMIT:
The first line, ``apply add_lt_add_of_lt_of_le``,
creates two goals,
and once again we use a dot to separate the
proof of the first from the proof of the second.

OMIT. -/
/- TEXT:
最初の行の ``apply add_lt_add_of_lt_of_le`` では2つのゴールが作られ，ここでもピリオドを使って1つ目と2つ目の証明を分けています．

.. index:: norm_num, tactics ; norm_num

TEXT. -/
/- OMIT:
Try the following examples on your own.
The example in the middle shows you that the ``norm_num``
tactic can be used to solve concrete numeric goals.
OMIT. -/
/- TEXT:
次の例は読者自身で試してみてください．真ん中の例では ``norm_num`` というタクティクが具体的な数値についてのゴールを解決するために使えることを示しています．
TEXT. -/
-- QUOTE:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  have h₁ : 0 < 1 + exp b := by sorry
  apply (log_le_log h₀ h₁).mpr
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  apply add_le_add_left h₀

-- an alternative using `linarith`.
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  have h₁ : 0 < 1 + exp b := by linarith [exp_pos b]
  apply (log_le_log h₀ h₁).mpr
  apply add_le_add_left (exp_le_exp.mpr h)

-- SOLUTION.
/- OMIT:
From these examples, it should be clear that being able to
find the library theorems you need constitutes an important
part of formalization.
There are a number of strategies you can use:

OMIT. -/
/- TEXT:
ここまで見てきた例題から，形式化において重要なことは読者がライブラリから必要な定理を見つけられるようになることであるのは明らかでしょう．これに当たって，取りうる手段はたくさんあります:

TEXT. -/
/- OMIT:
* You can browse Mathlib in its
  `GitHub repository <https://github.com/leanprover-community/mathlib4>`_.

OMIT. -/
/- TEXT:
* Mathlibの `GitHub repository <https://github.com/leanprover-community/mathlib4>`_ をブラウザで見ることができます．

TEXT. -/
/- OMIT:
* You can use the API documentation on the Mathlib
  `web pages <https://leanprover-community.github.io/mathlib4_docs/>`_.

OMIT. -/
/- TEXT:
* Mathlibの `web pages <https://leanprover-community.github.io/mathlib4_docs/>`_ にあるAPIのドキュメントから探すこともできます．

TEXT. -/
/- OMIT:
* You can rely on Mathlib naming conventions and Ctrl-space completion in
  the editor to guess a theorem name (or Cmd-space on a Mac keyboard).
  In Lean, a theorem named ``A_of_B_of_C`` establishes
  something of the form ``A`` from hypotheses of the form ``B`` and ``C``,
  where ``A``, ``B``, and ``C``
  approximate the way we might read the goals out loud.
  So a theorem establishing something like ``x + y ≤ ...`` will probably
  start with ``add_le``.
  Typing ``add_le`` and hitting Ctrl-space will give you some helpful choices.
  Note that hitting Ctrl-space twice displays more information about the available
  completions.

OMIT. -/
/- TEXT:
* Mathlibの定理はある程度命名規則が決まっているため，ある程度定理名を推理して入力した上でCtrl+スペースキー（MacではCmd+スペース）によってエディタで定理名を補完することも可能です．Leanでは， ``A_of_B_of_C`` という名前の定理は ``B`` と ``C`` という仮説から ``A`` という形の何かの証明に当てられ，そしてこの ``A`` ， ``B`` ， ``C`` はゴールを読み上げたときの文におおよそ近いことが多いです．つまり，例えば ``x + y ≤ ...`` というような形の定理はおそらく ``add_le`` で始まる可能性が高いのです．そこで ``add_le`` まで入力し，Ctrl+スペースを押せば有益な選択肢が表示されることでしょう．ここでCtrl+スペースを2回押すとさらに利用可能な補完についての詳細情報が表示されることも気にとどめてください．

TEXT. -/
/- OMIT:
* If you right-click on an existing theorem name in VS Code,
  the editor will show a menu with the option to
  jump to the file where the theorem is defined,
  and you can find similar theorems nearby.

OMIT. -/
/- TEXT:
* VSCode上で既存の定理名を右クリックして出てくるオプション中に，その定理が定義されているファイル中の位置に飛ぶ選択肢があるため，それを利用してその定理の近くにある類似の定理を探すことができます．

TEXT. -/
/- OMIT:
* You can use the ``apply?`` tactic,
  which tries to find the relevant theorem in the library.
OMIT. -/
/- TEXT:
* ``apply?`` タクティクを使うことでライブラリ中の関連する定理を探すことも可能です．
TEXT. -/
-- QUOTE:
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
-- QUOTE.

/- OMIT:
To try out ``apply?`` in this example,
delete the ``exact`` command and uncomment the previous line.
Using these tricks,
see if you can find what you need to do the
next example:
OMIT. -/
/- TEXT:
この例で ``exact`` の行を削除し，その前の行のコメントアウトを外して ``apply?`` の挙動を確認してみてください．この便利なツールを使って次の例でも必要な定理が見つかるかどうか試してみましょう:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  exact exp_le_exp.mpr h

-- alternatively:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  linarith [exp_le_exp.mpr h]

/- OMIT:
Using the same tricks, confirm that ``linarith`` instead of ``apply?``
can also finish the job.

OMIT. -/
/- TEXT:
同じ技法を使って， ``apply?`` の代わりに ``linarith`` を使って証明を終えることも可能です．

TEXT. -/
/- OMIT:
Here is another example of an inequality:
OMIT. -/
/- TEXT:
以下さらに別の不等式の例を挙げます:
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) :=
      add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

-- QUOTE.

/- OMIT:
Mathlib tends to put spaces around binary operations like ``*`` and ``^``,
but in this example, the more compressed format increases readability.
There are a number of things worth noticing.
First, an expression ``s ≥ t`` is definitionally equivalent to ``t ≤ s``.
In principle, this means one should be able to use them interchangeably.
But some of Lean's automation does not recognize the equivalence,
so Mathlib tends to favor ``≤`` over ``≥``.
Second, we have used the ``ring`` tactic extensively.
It is a real timesaver!
Finally, notice that in the second line of the
second ``calc`` proof,
instead of writing ``by exact add_le_add (le_refl _) h``,
we can simply write the proof term ``add_le_add (le_refl _) h``.

OMIT. -/
/- TEXT:
Mathlibでは ``*`` や ``^`` のような二項演算子の周りにはスペースを開ける傾向がありますが，ここではそこを詰めることで可読性を上げています．この例では注目すべき点がいくつもあります．まず， ``s ≥ t`` は定義上 ``t ≤ s`` と等価です．原理的にこの2つは互換性があるべきでしょう．しかし，Leanの自動証明の機構の中にはこの同値性を認識しない場合もあるため，Mathlibは ``≥`` よりも ``≤`` をより優先する傾向があります．第二に， ``ring`` タクティクをかなり多用しています．これはとても時間の節約になります！そして最後に，2番めの ``calc`` の証明の2行目で ``by exact add_le_add (le_refl _) h`` と書く代わりに，証明項 ``add_le_add (le_refl _) h`` をそのまま書けばよいことに注意してください．

TEXT. -/
/- OMIT:
In fact, the only cleverness in the proof above is figuring
out the hypothesis ``h``.
Once we have it, the second calculation involves only
linear arithmetic, and ``linarith`` can handle it:
OMIT. -/
/- TEXT:
実際，上記の証明で唯一ひらめきを要するのは仮説 ``h`` を見出すことだけです．それさえわかれば，2つ目の計算は線形演算だけで，これは ``linarith`` で処理できます:
TEXT. -/
-- QUOTE:
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
-- QUOTE.

/- OMIT:
How nice! We challenge you to use these ideas to prove the
following theorem. You can use the theorem ``abs_le'.mpr``.
OMIT. -/
/- TEXT:
なんて素晴らしいのでしょうか！これらのアイデアをもとに次の定理を証明してみてください．この定理では ``abs_le'.mpr`` を使うことができます．
TEXT. -/
-- QUOTE:
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

#check abs_le'.mpr
-- QUOTE.

-- SOLUTIONS:
theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff h]
    apply fact1
  rw [le_div_iff h]
  apply fact2

/- OMIT:
If you managed to solve this, congratulations!
You are well on your way to becoming a master formalizer.
OMIT. -/
/- TEXT:
これを自力で解けたのならおめでとうございます！あなたは形式化の達人への道を順調に歩めています．
TEXT. -/

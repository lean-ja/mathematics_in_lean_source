import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

/- OMIT:
Disjunction
-----------

OMIT. -/
/- TEXT:
.. _disjunction:

選言
-----

.. index:: left, right, tactics ; left, tactics ; right

TEXT. -/
/- OMIT:
The canonical way to prove a disjunction ``A ∨ B`` is to prove
``A`` or to prove ``B``.
The ``left`` tactic chooses ``A``,
and the ``right`` tactic chooses ``B``.
OMIT. -/
/- TEXT:
選言 ``A ∨ B`` を証明する標準的な方法は ``A`` か ``B`` のどちらかを証明することです． ``left`` タクティクは ``A`` を， ``right`` タクティクは ``B`` を選びます．
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {x y : ℝ}

-- EXAMPLES:
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]
-- QUOTE.

/- OMIT:
We cannot use an anonymous constructor to construct a proof
of an "or" because Lean would have to guess
which disjunct we are trying to prove.
When we write proof terms we can use
``Or.inl`` and ``Or.inr`` instead
to make the choice explicitly.
Here, ``inl`` is short for "introduction left" and
``inr`` is short for "introduction right."
OMIT. -/
/- TEXT:
「または」についての証明を組み立てるにあたって無名コンストラクタを使うことはできません．選言でどちらを証明したいのか，Leanが推測することはできないからです．選言の証明項を書く方法には，明示的に選択する以外にも ``Or.inl`` と ``Or.inr`` を使う方法があります．ここで ``inl`` は「introduction left」の略で， ``inr`` は「introduction right」の略です．
TEXT. -/
-- QUOTE:
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h
-- QUOTE.

/- OMIT:
It may seem strange to prove a disjunction by proving one side
or the other.
In practice, which case holds usually depends on a case distinction
that is implicit or explicit in the assumptions and the data.
The ``rcases`` tactic allows us to make use of a hypothesis
of the form ``A ∨ B``.
In contrast to the use of ``rcases`` with conjunction or an
existential quantifier,
here the ``rcases`` tactic produces *two* goals.
Both have the same conclusion, but in the first case,
``A`` is assumed to be true,
and in the second case,
``B`` is assumed to be true.
In other words, as the name suggests,
the ``rcases`` tactic carries out a proof by cases.
As usual, we can tell Lean what names to use for the hypotheses.
In the next example, we tell Lean
to use the name ``h`` on each branch.
OMIT. -/
/- TEXT:
選言を証明するために，どちらか片方だけを証明するというのは奇妙に思われるかもしれません．実際には，どちらのケースが成り立つかは通常，仮定とデータに暗黙的・明示的に含まれるケース分割に依存します． ``rcases`` タクティクは ``A ∨ B`` の形式の仮定を利用できるようにしてくれます．連言や存在量化子を使う場合の ``rcases`` の使用方法とは異なり，ここでは ``rcases`` は **2つの** ゴールを生成します．どちらのゴールも結論は同じですが，1つ目のケースでは ``A`` が真だと仮定され，2つ目のケースでは ``B`` が真だと仮定されます．つまり，名前の通り， ``rcases`` タクティクは場合分けによる証明を行ってくれます．いつものように，この仮定についてどのような名前を使うかをLeanに指示することができます．次の例では，各ブランチで ``h`` という名前を使っています．
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- OMIT:
Notice that the pattern changes from ``⟨h₀, h₁⟩`` in the case of
a conjunction to ``h₀ | h₁`` in the case of a disjunction.
Think of the first pattern as matching against data the contains
*both* an ``h₀`` and a ``h₁``, whereas second pattern, with the bar,
matches against data that contains *either* an ``h₀`` or ``h₁``.
In this case, because the two goals are separate, we have chosen
to use the same name, ``h``, in each case.

OMIT. -/
/- TEXT:
パターンが連言での ``⟨h₀, h₁⟩`` から選言では ``h₀ | h₁`` に変わっていることに注意してください．先に出した連言のパターンは ``h₀`` と ``h₁`` の **両方** を含むデータに対してのマッチングだったのに対して，2つ目の縦棒を用いたパターンは ``h₀`` か ``h₁`` の **どちらか** を含むデータに対してのマッチングであると考えてください．この場合，2つのゴールは別々になるため，両方で同じ名前 ``h`` を使用することにしています．

TEXT. -/
/- OMIT:
The absolute value function is defined in such a way
that we can immediately prove that
``x ≥ 0`` implies ``|x| = x``
(this is the theorem ``abs_of_nonneg``)
and ``x < 0`` implies ``|x| = -x`` (this is ``abs_of_neg``).
The expression ``le_or_gt 0 x`` establishes ``0 ≤ x ∨ x < 0``,
allowing us to split on those two cases.

OMIT. -/
/- TEXT:
絶対値関数に対して ``x ≥ 0`` ならば ``|x| = x`` （これが定理 ``abs_of_nonneg`` のことです）， ``x < 0`` ならば ``|x| = -x`` （こちらは ``abs_of_neg`` です）がそれぞれ成り立ち，証明は定義から直ちに導くことができます．式 ``le_or_gt 0 x`` は ``0 ≤ x ∨ x < 0`` の証明で，正負の場合分けを行うことができます．

TEXT. -/
/- OMIT:
Lean also supports the computer scientists' pattern-matching
syntax for disjunction. Now the ``cases`` tactic is more attractive,
because it allows us to name each ``case``, and name the hypothesis
that is introduced closer to where it is used.
OMIT. -/
/- TEXT:
Leanでは選言を計算機科学におけるパターンマッチ構文を使って扱うこともできます．この場合 ``cases`` タクティクはより魅力的です．なぜならそれぞれの ``case`` に名前をつけることができ，導入された仮定が使用される場所の近くで名前をつけることができるからです．
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- OMIT:
The names ``inl`` and ``inr`` are short for "intro left" and "intro right,"
respectively. Using ``case`` has the advantage that you can prove the
cases in either order; Lean uses the tag to find the relevant goal.
If you don't care about that, you can use ``next``, or ``match``,
or even a pattern-matching ``have``.
OMIT. -/
/- TEXT:
``inl`` と ``inr`` はそれぞれ 「intro left」と「intro right」の略です． ``case`` を用いると，任意の順番で証明ができるという利点があります．この場合，タグに一致するゴールが選択されます．これらの利点が必要でなければ， ``next`` や ``match`` ，あるいは ``have`` によるパターンマッチを使用することができます．
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h
-- QUOTE.

/- OMIT:
In the case of ``match``, we need to use the full names
``Or.inl`` and ``Or.inr`` of the canonical ways to prove a disjunction.
In this textbook, we will generally use ``rcases`` to split on the
cases of a disjunction.

OMIT. -/
/- TEXT:
``match`` の場合，選言を証明する正規の方法であるフルネーム ``Or.inl`` と ``Or.inr`` を使う必要があります．本書では，基本的に選言の場合分けには ``rcases`` を使うことにします．

TEXT. -/
/- OMIT:
Try proving the triangle inequality using the
first two theorems in the next snippet.
They are given the same names they have in Mathlib.
OMIT. -/
/- TEXT:
次のコードの最初の2つの定理を使って三角不等式を証明してみましょう．これらはMathlibにあるのと同じ名前が与えられています．
TEXT. -/
-- BOTH:
-- QUOTE:
namespace MyAbs

-- EXAMPLES:
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem le_abs_selfαα (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_selfαα (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_addαα (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

/- OMIT:
In case you enjoyed these (pun intended) and
you want more practice with disjunction,
try these.
OMIT. -/
/- TEXT:
場合分けによる証明を楽しめましたか？もっと練習をすることができます．以下を試してみてください．
TEXT. -/
-- QUOTE:
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem lt_absαα : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith
    · exact h'

theorem abs_ltαα : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    · intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

-- BOTH:
end MyAbs

end

/- OMIT:
You can also use ``rcases`` and ``rintro`` with nested disjunctions.
When these result in a genuine case split with multiple goals,
the patterns for each new goal are separated by a vertical bar.
OMIT. -/
/- TEXT:
``rcases`` と ``rintro`` は入れ子になった選言に対しても使うことができます．このケース分割の結果複数のゴールが作られる場合，それぞれの新しいゴールのパターンは縦棒で区切られます．
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt
-- QUOTE.

/- OMIT:
You can still nest patterns and use the ``rfl`` keyword
to substitute equations:
OMIT. -/
/- TEXT:
パターンをネストさせたり， ``rfl`` キーワードによって等式を代入したりすることも可能です:
TEXT. -/
-- QUOTE:
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right
-- QUOTE.

/- OMIT:
See if you can prove the following with a single (long) line.
Use ``rcases`` to unpack the hypotheses and split on cases,
and use a semicolon and ``linarith`` to solve each branch.
OMIT. -/
/- TEXT:
以下を（長い）1行で証明できるか試してみましょう． ``rcases`` を使って仮定を展開して場合分けを行い，セミコロンと ``linarith`` を用いて各分岐を解いてみましょう．
TEXT. -/
-- QUOTE:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

/- OMIT:
On the real numbers, an equation ``x * y = 0``
tells us that ``x = 0`` or ``y = 0``.
In Mathlib, this fact is known as ``eq_zero_or_eq_zero_of_mul_eq_zero``,
and it is another nice example of how a disjunction can arise.
See if you can use it to prove the following:
OMIT. -/
/- TEXT:
実数上において，等式 ``x * y = 0`` は ``x = 0`` か ``y = 0`` のどちらかを意味します．Mathlibにおいて，この事実は ``eq_zero_or_eq_zero_of_mul_eq_zero`` として知られており，どのように選言が生じるかを示す良い例です．これを使って次のことを証明してみましょう:
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

/- OMIT:
Remember that you can use the ``ring`` tactic to help
with calculations.

OMIT. -/
/- TEXT:
計算を助けるために ``ring`` タクティクを使うことができることを覚えておきましょう．

TEXT. -/
/- OMIT:
In an arbitrary ring :math:`R`, an element :math:`x` such
that :math:`x y = 0` for some nonzero :math:`y` is called
a *left zero divisor*,
an element :math:`x` such
that :math:`y x = 0` for some nonzero :math:`y` is called
a *right zero divisor*,
and an element that is either a left or right zero divisor
is called simply a *zero divisor*.
The theorem ``eq_zero_or_eq_zero_of_mul_eq_zero``
says that the real numbers have no nontrivial zero divisors.
A commutative ring with this property is called an *integral domain*.
Your proofs of the two theorems above should work equally well
in any integral domain:
OMIT. -/
/- TEXT:
任意の環 :math:`R` において，あるゼロではない要素 :math:`y` に対して :math:`x y = 0` を満たすような元 :math:`x` を **左零因子** （left zero divisor）と呼び，またあるゼロではない要素 :math:`y` に対して :math:`y x = 0` を満たすような元 :math:`x` を **右零因子** （right zero divisor）と呼び，左零因子または右零因子である要素を単に **零因子** （zero divisor）と呼びます．定理 ``eq_zero_or_eq_zero_of_mul_eq_zero`` は実数には0以外に零因子がないことを述べています．この性質を持つ可換環は **整域** （integral domain）と呼ばれます．上の2つの定理の証明はどのような整域でも同じようにうまくいくはずです:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

-- EXAMPLES:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

-- BOTH:
end

/- OMIT:
In fact, if you are careful, you can prove the first
theorem without using commutativity of multiplication.
In that case, it suffices to assume that ``R`` is
a ``Ring`` instead of an ``CommRing``.

OMIT. -/
/- TEXT:
実は注意深くやれば，乗法の可換性を用いずに最初の定理を証明することができます．その場合， ``R`` は ``CommRing`` ではなく ``Ring`` であると仮定すれば十分です．

.. index:: excluded middle

TEXT. -/
/- OMIT:
Sometimes in a proof we want to split on cases
depending on whether some statement is true or not.
For any proposition ``P``, we can use
``em P : P ∨ ¬ P``.
The name ``em`` is short for "excluded middle."
OMIT. -/
/- TEXT:
証明の中で，ある文が真かそうでないかによって場合分けを行いたいことがあります．任意の命題 ``P`` に対して， ``em P : P ∨ ¬ P`` で実現できます．この ``em`` という名前は「排中律(excluded middle)」の略です．
TEXT. -/
-- QUOTE:
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction
-- QUOTE.

/- OMIT:
Alternatively, you can use the ``by_cases`` tactic.

OMIT. -/
/- TEXT:
.. index:: by_cases, tactics ; by_cases

あるいは ``by_cases`` タクティクを使うこともできます．

TEXT. -/
-- QUOTE:
-- EXAMPLES:
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction
-- QUOTE.

/- OMIT:
Notice that the ``by_cases`` tactic lets you
specify a label for the hypothesis that is
introduced in each branch,
in this case, ``h' : P`` in one and ``h' : ¬ P``
in the other.
If you leave out the label,
Lean uses ``h`` by default.
Try proving the following equivalence,
using ``by_cases`` to establish one direction.
OMIT. -/
/- TEXT:
``by_cases`` タクティクでは各分岐で導入される仮定のラベルを指定できることに注意してください．この場合，1つは ``h' : P`` で，もう1つは ``h' : ¬ P`` です．ラベルを省略した場合，デフォルトで ``h`` という名前になります．以下の等価性を証明では，片方向で ``by_cases`` を使います．
TEXT. -/
-- QUOTE:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h

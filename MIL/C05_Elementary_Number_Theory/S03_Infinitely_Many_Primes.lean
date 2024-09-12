import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

/- OMIT:

Infinitely Many Primes
----------------------

OMIT. -/
/- TEXT:
.. _section_infinitely_many_primes:

無限に存在する素数
----------------------

TEXT. -/
/- OMIT:
Let us continue our exploration of induction and recursion with another
mathematical standard: a proof that there are infinitely many primes.
One way to formulate this is as the statement that
for every natural number
:math:`n`, there is a prime number greater than :math:`n`.
To prove this, let :math:`p` be any prime factor of :math:`n! + 1`.
If :math:`p` is less than or equal to :math:`n`, it divides :math:`n!`.
Since it also divides :math:`n! + 1`, it divides 1, a contradiction.
Hence :math:`p` is greater than :math:`n`.

OMIT. -/
/- TEXT:
帰納と再帰の探求を続けるにあたってもう一つの数学的な基本法則，すなわち素数が無限に存在することの証明を行いましょう．これの形式化された形として，すべての自然数 :math:`n` に対して :math:`n` より大きい素数が存在すると言うことができます．これを証明するために， :math:`p` を :math:`n! + 1` の任意の素因数とします．もし， :math:`p` が :math:`n` より小さければ， :math:`n!` も割ることができます．一方で :math:`n! + 1` も割るため， :math:`p` は1も割ることとなり，矛盾します．したがって :math:`p` は :math:`n` より大きいことになります．

TEXT. -/
/- OMIT:
To formalize that proof, we need to show that any number greater than or equal
to 2 has a prime factor.
To do that, we will need to show that any natural number that is
not equal to 0 or 1 is greater-than or equal to 2.
And this brings us to a quirky feature of formalization:
it is often trivial statements like this that are among the most
annoying to formalize.
Here we consider a few ways to do it.

OMIT. -/
/- TEXT:
この証明を形式化するには，2以上の数が素因数を持つことを示す必要があります．そのためには，0と1のどちらでもない自然数が2以上であることを証明する必要があります．そしてこの事実から形式化の風変わりな特徴が導かれます．この手の自明な命題が時として形式化にあたって最も厄介なのです．ここでは証明にあたっていくつかの方法を考えます．

TEXT. -/
/- OMIT:
To start with, we can use the ``cases`` tactic and the fact that the
successor function respects the ordering on the natural numbers.
OMIT. -/
/- TEXT:
まず初めに， ``cases`` タクティクと，後続関数が自然数の順序を保持するという事実を使うことができます．
BOTH: -/
-- QUOTE:
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le
-- QUOTE.

/- OMIT:
Another strategy is to use the tactic ``interval_cases``,
which automatically splits the goal into cases when
the variable in question is contained in an interval
of natural numbers or integers.
Remember that you can hover over it to see its documentation.
OMIT. -/
/- TEXT:
別の方法としては， ``interval_cases`` というタクティクを使う方法があります．これは問題の変数が自然数か整数の区間にふくまれる場合にゴールを自動的にケース分割してくれます．このタクティクにカーソルを合わせるとドキュメントを見ることができることを覚えておいてください．
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction
-- QUOTE.

/- OMIT:
Recall that the semicolon after ``interval_cases m`` means
that the next tactic is applied to each of the cases that it generates.
Yet another option is to use the tactic ``decide``, which tries
to find a decision procedure to solve the problem.
Lean knows that you can decide the truth value of a statement that
begins with a bounded quantifier ``∀ x, x < n → ...`` or ``∃ x, x < n ∧ ...``
by deciding each of the finitely many instances.
OMIT. -/
/- TEXT:
.. index:: decide, tactics ; decide

``interval_cases m`` の後ろのセミコロンは，その次に来るタクティクが分割された各ケースそれぞれに適用されることを意味します．さらに別の選択肢として ``decide`` というタクティクを使うことで，問題を解決するための決定手順を自動で見つけることもできます．Leanは束縛された量化子  ``∀ x, x < n → ...``  もしくは ``∃ x, x < n ∧ ...`` で始まる命題の真理値を，その命題を有限個生成してそれぞれについて決定することで求めることができることを知っています．
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide
-- QUOTE.

/- OMIT:
With the theorem ``two_le`` in hand, let's start by showing that every
natural number greater than two has a prime divisor.
Mathlib contains a function ``Nat.minFac`` that
returns the smallest prime divisor,
but for the sake of learning new parts of the library,
we'll avoid using it and prove the theorem directly.

OMIT. -/
/- TEXT:
定理 ``two_le`` 片手に2より大きい自然数にはすべて素因数があることを示すことから初めましょう．Mathlibには最小の素因数を帰す関数 ``Nat.minFac`` がありますが，ライブラリの新しい部分を学ぶために，この関数を使用せずに定理を直接証明することにしましょう．

TEXT. -/
/- OMIT:
Here, ordinary induction isn't enough.
We want to use *strong induction*, which allows us to prove
that every natural number :math:`n` has a property :math:`P`
by showing that for every number :math:`n`, if :math:`P` holds
of all values less than :math:`n`, it holds at :math:`n` as well.
In Lean, this principle is called ``Nat.strong_induction_on``,
and we can use the ``using`` keyword to tell the induction tactic
to use it.
Notice that when we do that, there is no base case; it is subsumed
by the general induction step.

OMIT. -/
/- TEXT:
これにあたっては普通の帰納法では不十分です．ここで必要なのはすべての自然数 :math:`n` が性質 :math:`P` を持つことを証明するために，すべての自然数 :math:`n` についてもし :math:`P` が :math:`n` より小さいすべての値で成り立つならば， :math:`n` でも成り立つことで示すという **強帰納法** （strong induction）です．Leanでは，この原理を ``Nat.strong_induction_on`` と呼び， ``with`` キーワードを使って帰納法のタクティクにこれを使うように指示することができます．この場合，ベースケースは存在せず，一般的な帰納法のステップにふくまれることに注意してください．

TEXT. -/
/- OMIT:
The argument is simply as follows. Assuming :math:`n ≥ 2`,
if :math:`n` is prime, we're done. If it isn't,
then by one of the characterizations of what it means to be a prime number,
it has a nontrivial factor, :math:`m`,
and we can apply the inductive hypothesis to that.
Step through the next proof to see how that plays out.
OMIT. -/
/- TEXT:
議論の流れは単純に以下のとおりです． :math:`n ≥ 2` を仮定し， :math:`n` が素数であればそれでおしまいです．もし素数でなければ，素数の特徴の1つである，素数の非自明な因数 :math:`m` を帰納法の仮説に適用することができます．次の証明を一行ずつ読めばこれがどのような役割を演じているかわかるでしょう．
BOTH: -/
-- QUOTE:
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
-- QUOTE.

/- OMIT:
We can now prove the following formulation of our theorem.
See if you can fill out the sketch.
You can use ``Nat.factorial_pos``, ``Nat.dvd_factorial``,
and ``Nat.dvd_sub'``.
OMIT. -/
/- TEXT:
これで本題の定理の形式化を証明することができます．以下のスケッチを埋めてみましょう．ここでは ``Nat.factorial_pos`` と ``Nat.dvd_factorial`` ， ``Nat.dvd_sub'`` が使えます．
BOTH: -/
-- QUOTE:
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_factorial
    apply pp.pos
    linarith
-- BOTH:
  have : p ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- OMIT:
Let's consider a variation of the proof above, where instead
of using the factorial function,
we suppose that we are given by a finite set
:math:`\{ p_1, \ldots, p_n \}` and we consider a prime factor of
:math:`\prod_{i = 1}^n p_i + 1`.
That prime factor has to be distinct from each
:math:`p_i`, showing that there is no finite set that contains
all the prime numbers.

OMIT. -/
/- TEXT:
上記の証明について別解を考えましょう．階乗関数を使う代わりに，有限集合 :math:`\{ p_1, \ldots, p_n \}` が与えられたとした時の :math:`\prod_{i = 1}^n p_i + 1` の素因数を考えることにします．この素因数は各 :math:`p_i` とは異なるものでなければならないため，すべての素数を含む有限集合は存在しないことがわかります．

TEXT. -/
/- OMIT:
Formalizing this argument requires us to reason about finite
sets. In Lean, for any type ``α``, the type ``Finset α``
represents finite sets of elements of type ``α``.
Reasoning about finite sets computationally requires having
a procedure to test equality on ``α``, which is why the snippet
below includes the assumption ``[DecidableEq α]``.
For concrete data types like ``ℕ``, ``ℤ``, and ``ℚ``,
the assumption is satisfied automatically. When reasoning about
the real numbers, it can be satisfied using classical logic
and abandoning the computational interpretation.

OMIT. -/
/- TEXT:
この議論を形式化するには，有限集合を推論できる必要があります．Leanでは，任意の型 ``α`` に対して ``Finset α`` 型で ``α`` 型の要素の有限集合を表します．有限集合の計算を推論するには， ``α`` 型についての同値性を検証する手順が必要です．これが以下のスニペットに ``[DecidableEq α]`` という仮定が含まれている理由です． ``ℕ`` や ``ℤ`` ， ``ℚ`` のような具体的なデータ型ではこの仮定は自動的に満たされます．実数について推論する際には古典論理によって仮定が成り立ち，計算的な解釈を放棄することができます．

TEXT. -/
/- OMIT:
We use the command ``open Finset`` to avail ourselves of shorter names
for the relevant theorems. Unlike the case with sets,
most equivalences involving finsets do not hold definitionally,
so they need to be expanded manually using equivalences like
``Finset.subset_iff``, ``Finset.mem_union``, ``Finset.mem_inter``,
and ``Finset.mem_sdiff``. The ``ext`` tactic can still be used
to show that two finite sets are equal by showing
that every element of one is an element of the other.
OMIT. -/
/- TEXT:
``open Finset`` コマンドを使うことで，関連する定理を短い名前で利用できるようにしています．集合の場合とは異なり，有限集合に関わる同値性はほとんどの場合定義的に成り立たないため， ``Finset.subset_iff`` や ``Finset.mem_union`` ， ``Finset.mem_inter`` ， ``Finset.mem_sdiff`` などの等価の条件を使って手動で展開する必要があります． ``ext`` タクティクは2つの有限集合が等しいことを片方の各元がすべてもう片方の元であることによって示すために使うことができます．
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end
-- QUOTE.

/- OMIT:
We have used a new trick: the ``tauto`` tactic (and a strengthened
version, ``tauto!``, which uses classical logic) can be used to
dispense with propositional tautologies. See if you can use
these methods to prove the two examples below.
OMIT. -/
/- TEXT:
ここで新しい技法を使いました． ``tauto`` タクティク（と古典論理を使う強化版の ``tauto!`` ）は命題の同語反復を省くために使うことができます．以下の2つの例を証明するためにこれらの手法が使えるか試してみましょう．
BOTH: -/
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

-- QUOTE:
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_inter, mem_union, mem_union, mem_union, mem_inter]
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

-- BOTH:
example : (r \ s) \ t = r \ (s ∪ t) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_sdiff, mem_sdiff, mem_sdiff, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto
-- QUOTE.
-- BOTH:

end

/- OMIT:
The theorem ``Finset.dvd_prod_of_mem`` tells us that if an
``n`` is an element of a finite set ``s``, then ``n`` divides
``∏ i in s, i``.
OMIT. -/
/- TEXT:
定理 ``Finset.dvd_prod_of_mem`` は，もし ``n`` が有限集合 ``s`` の元であれば， ``n`` は ``∏ i in s, i`` を割ることができることを教えてくれます．
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h
-- QUOTE.

/- OMIT:
We also need to know that the converse holds in the case where
``n`` is prime and ``s`` is a set of primes.
To show that, we need the following lemma, which you should
be able to prove using the theorem ``Nat.Prime.eq_one_or_self_of_dvd``.
OMIT. -/
/- TEXT:
また ``n`` が素数で ``s`` が素数の集合である場合は上記の逆も成り立つことも知っておく必要があります．これを示すには次の補題が必要です．この証明には定理 ``Nat.Prime.eq_one_or_self_of_dvd`` を使うことができます．
BOTH: -/
-- QUOTE:
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  cases prime_q.eq_one_or_self_of_dvd _ h
  · linarith [prime_p.two_le]
  assumption
-- QUOTE.
-- BOTH:

/- OMIT:
We can use this lemma to show that if a prime ``p`` divides a product of a finite
set of primes, then it is equal to one of them.
Mathlib provides a useful principle of induction on finite sets:
to show that a property holds of an arbitrary finite set ``s``,
show that it holds of the empty set, and show that it is preserved
when we add a single new element ``a ∉ s``.
The principle is known as ``Finset.induction_on``.
When we tell the induction tactic to use it, we can also specify the names
``a`` and ``s``, the name for the assumption ``a ∉ s`` in the inductive step,
and the name of the inductive hypothesis.
The expression ``Finset.insert a s`` denotes the union of ``s`` with the singleton ``a``.
The identities ``Finset.prod_empty`` and ``Finset.prod_insert`` then provide
the relevant rewrite rules for the product.
In the proof below, the first ``simp`` applies ``Finset.prod_empty``.
Step through the beginning of the proof to see the induction unfold,
and then finish it off.
OMIT. -/
/- TEXT:
この補題を使って素数 ``p`` が素数の有限集合の積を割り切る場合，そのうちの1つを割ることを示すことができます．Mathlibは有限集合の帰納法について便利な原理を提供しています．任意の有限集合 ``s`` の性質が成り立つことを示すには，空集合でその性質が成り立ち，新しい元 ``a ∉ s`` を1つ追加してもその性質が保たれることを示すことで出来るというものです．この原理は ``Finset.induction_on`` として知られています．これを使うように帰納法のタクティクに指示する際には， ``a`` と ``s`` の名前と帰納法のステップの仮定 ``a ∉ s`` の名前，帰納的仮説の名前を指定することもできます．式 ``Finset.insert a s`` は ``s`` と ``a`` の単集合の和を表します．恒等式 ``Finset.prod_empty`` と ``Finset.prod_insert`` は積に関連する書き換えルールです．以下の証明では最初の ``simp`` が ``Finset.prod_empty`` を適用しています．帰納法がどのように展開され，そして完成されるかを見るために証明の冒頭から順を追って確認してください．
BOTH: -/
-- QUOTE:
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rcases h₁ with h₁ | h₁
  · left
    exact prime_p.eq_of_dvd_of_prime h₀.1 h₁
  right
  exact ih h₀.2 h₁

-- BOTH:
-- QUOTE.
/- OMIT:
We need one last property of finite sets.
Given an element ``s : Set α`` and a predicate
``P`` on ``α``, in  :numref:`Chapter %s <sets_and_functions>`
we wrote ``{ x ∈ s | P x }`` for the set of
elements of ``s`` that satisfy ``P``.
Given ``s : Finset α``,
the analogous notion is written ``s.filter P``.
OMIT. -/
/- TEXT:
本題の証明を行うには有限集合についてあと一つの性質が必要です．ある元 ``s : Set α`` と ``α`` についての述語 ``P`` が与えられた時， :numref:`Chapter %s <sets_and_functions>` では ``P`` を満たす ``s`` の元の集合を ``{ x ∈ s | P x }`` と書いていました． ``s : Finset α`` の場合，同じような概念は ``s.filter P`` と書きます．
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter
-- QUOTE.

/- OMIT:
We now prove an alternative formulation of the statement that there are infinitely many
primes, namely, that given any ``s : Finset ℕ``, there is a prime ``p`` that is not
an element of ``s``.
Aiming for a contradiction, we assume that all the primes are in ``s``, and then
cut down to a set ``s'`` that contains all and only the primes.
Taking the product of that set, adding one, and finding a prime factor
of the result
leads to the contradiction we are looking for.
See if you can complete the sketch below.
You can use ``Finset.prod_pos`` in the proof of the first ``have``.
OMIT. -/
/- TEXT:
これで素数が無限にあることについての別の形式化を証明できます．すなわち，任意の ``s : Finset ℕ`` について，``s`` の元ではない素数 ``p`` が存在します．矛盾を導くために，すべての素数が ``s`` に存在することを仮定し，そこからすべての素数のみを含む集合 ``s'`` に絞り込みます．この集合の積を取り，1を加え，その結果の素因数を求めることで期待している矛盾が導かれます．下のスケッチを完成させましょう．最初の ``have`` の証明では ``Finset.prod_pos`` を使うことができます．
BOTH: -/
-- QUOTE:
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_prod_of_mem
    rw [mem_s']
    apply pp
-- BOTH:
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- OMIT:
We have thus seen two ways of saying that there are infinitely many primes:
saying that they are not bounded by any ``n``, and saying that they are
not contained in any finite set ``s``.
The two proofs below show that these formulations are equivalent.
In the second, in order to form ``s.filter Q``, we have to assume that there
is a procedure for deciding whether or not ``Q`` holds. Lean knows that there
is a procedure for ``Nat.Prime``. In general, if we use classical logic
by writing ``open Classical``,
we can dispense with the assumption.

OMIT. -/
/- TEXT:
さて，ここまでで素数が無限に存在するということについて2通りの言及の仕方を見てきました．一つは素数がどのような ``n`` にも束縛されないという言い方で，もう一つは素数がどのような有限集合 ``s`` にも含まれないという言い方です．以下の2つの証明はこれらの形式化が等価であることを示しています．2つ目では ``s.filter Q`` を形式化するために， ``Q`` が成り立つかどうかを決定する手順があると仮定しなければなりません．これについてLeanは ``Nat.Prime`` 用の手続きがあることを知っています．一般的に， ``open Classical`` と書いて古典論理を使うことで，この仮定を省くことができます．

TEXT. -/
/- OMIT:
In Mathlib, ``Finset.sup s f`` denotes the supremum of the values of ``f x`` as ``x``
ranges over ``s``, returning ``0`` in the case where ``s`` is empty and
the codomain of ``f`` is ``ℕ``. In the first proof, we use ``s.sup id``,
where ``id`` is the identity function, to refer to the maximum value in ``s``.
OMIT. -/
/- TEXT:
Mathlibでは， ``Finset.sup s f`` は ``x`` が ``s`` の範囲にある時の ``f x`` の上限を表します． ``s`` が空集合で ``f`` の余域が ``ℕ`` の場合は ``0`` を返します．最初の証明では ``s.sup id`` （ ``id`` は恒等関数です）を ``s`` の最大値を指すために使っています．
BOTH: -/
-- QUOTE:
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k
-- QUOTE.

/- OMIT:
A small variation on our second proof that there are infinitely many primes
shows that there are infinitely many primes congruent to 3 modulo 4.
The argument goes as follows.
First, notice that if the product of two numbers :math:`m` and :math:`n`
is equal to 3 modulo 4, then one of the two numbers is congruent to 3 modulo 4.
After all, both have to be odd, and if they are both congruent to 1 modulo 4,
so is their product.
We can use this observation to show that if some number
greater than 2 is congruent to 3 modulo 4,
then that number has a prime divisor that is also congruent to 3 modulo 4.

OMIT. -/
/- TEXT:
無限に多くの素数が存在するということの2つ目の証明については4を法とした3に合同な素数が無限に存在することを示す別バージョンが存在します．この事実の証明の流れは次のようになります．まず，2つの数 :math:`m` と :math:`n` の積が4を法として3に合同である場合，2つの数のどちらかが4を法として3に合同であることに気づきます．結局の所どちらも奇数でなければならず，もし両方共4を法として1に合同であればその積も同じとなるからです．この観察を使って2より大きいある数が4を法として3に合同であるならば，その数は4を法として3に合同である素因数を持つことを示すことができます．

TEXT. -/
/- OMIT:
Now suppose there are only finitely many prime numbers congruent to 3
modulo 4, say, :math:`p_1, \ldots, p_k`.
Without loss of generality, we can assume that :math:`p_1 = 3`.
Consider the product :math:`4 \prod_{i = 2}^k p_i + 3`.
It is easy to see that this is congruent to 3 modulo 4, so it has
a prime factor :math:`p` congruent to 3 modulo 4.
It can't be the case that :math:`p = 3`; since :math:`p`
divides :math:`4 \prod_{i = 2}^k p_i + 3`, if :math:`p`
were equal to 3 then it would also divide :math:`\prod_{i = 2}^k p_i`,
which implies that :math:`p` is equal to
one of the :math:`p_i` for :math:`i = 2, \ldots, k`;
and we have excluded 3 from this list.
So :math:`p` has to be one of the other elements :math:`p_i`.
But in that case, :math:`p` divides :math:`4 \prod_{i = 2}^k p_i`
and hence 3, which contradicts the fact that it is not 3.

OMIT. -/
/- TEXT:
ここで4を法として3に合同な素数が有限個だけあると仮定し， :math:`p_1, \ldots, p_k` と書くことにします．そして :math:`p_1 = 3` を仮定しても一般性を欠きません．ここで積 :math:`4 \prod_{i = 2}^k p_i + 3` を考えてみます．これが4を法として3に合同であることは簡単にわかるため，4を法として3に合同な素因数 :math:`p` を持つことになります．もし :math:`p` が3だとすると， :math:`p` は :math:`4 \prod_{i = 2}^k p_i + 3` を割り切れることになってしまうため， :math:`p=3` はありえません．また :math:`\prod_{i = 2}^k p_i` も割り切れることになり，これにより :math:`p` が :math:`i = 2, \ldots, k` の :math:`p_i` のどれかと等しいことを導いてしまうことからもこのリストから3を除外しています．従って :math:`p` は :math:`p_i` の他の元のどれかでなければなりません．しかしその場合， :math:`p` は :math:`4 \prod_{i = 2}^k p_i` を割るため，3が導かれますが，これは :math:`p` が3ではないとして事実に矛盾します．

TEXT. -/
/- OMIT:
In Lean, the notation ``n % m``, read "``n`` modulo ``m``,"
denotes the remainder of the division of ``n`` by ``m``.
OMIT. -/
/- TEXT:
Leanでは， ``n % m`` という表記は「 ``n`` modulo ``m`` 」と読み， ``n`` を ``m`` で割ったあまりを表します．
EXAMPLES: -/
-- QUOTE:
example : 27 % 4 = 3 := by norm_num
-- QUOTE.

/- OMIT:
We can then render the statement "``n`` is congruent to 3 modulo 4"
as ``n % 4 = 3``. The following example and theorems sum up
the facts about this function that we will need to use below.
The first named theorem is another illustration of reasoning by
a small number of cases.
In the second named theorem, remember that the semicolon means that
the subsequent tactic block is applied to all the goals created by the
preceding tactic.
OMIT. -/
/- TEXT:
「 ``n`` が4を法として3に合同である」という命題は ``n % 4 = 3`` と表すことができます．以下の例と定理はこの後で使うこの関数についての事実を要約したものです．1つ目の名前付きの定理は先程利用した小さい数についてのケース分割による推論の別の例です．2つ目の名前付きの定理において，セミコロンがそれに続くタクティクのブロックを，その前に実行したタクティクによって生み出されたすべてのゴールそれぞれに適用していることを覚えておいてください．
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

-- BOTH:
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
-- QUOTE.

/- OMIT:
We will also need the following fact, which says that if
``m`` is a nontrivial divisor of ``n``, then so is ``n / m``.
See if you can complete the proof using ``Nat.div_dvd_of_dvd``
and ``Nat.div_lt_self``.
OMIT. -/
/- TEXT:
また以下に示す ``m`` が ``n`` の自明ではない約数である場合， ``n / m`` もまた同様であるという事実も必要です． ``Nat.div_dvd_of_dvd`` と ``Nat.div_lt_self`` を使って証明を完成させてみましょう．
BOTH: -/
-- QUOTE:
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁
-- QUOTE.

-- BOTH:
/- OMIT:
Now put all the pieces together to prove that any
number congruent to 3 modulo 4 has a prime divisor with that
same property.
OMIT. -/
/- TEXT:
さて，これらすべてのピースを組み合わせて4を法として3に合同な数には同じ性質を持つ素因数があることを証明しましょう．
BOTH: -/
-- QUOTE:
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
/- EXAMPLES:
  . sorry
  . sorry
SOLUTIONS: -/
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

-- BOTH:
-- QUOTE.
/- OMIT:
We are in the home stretch. Given a set ``s`` of prime
numbers, we need to talk about the result of removing 3 from that
set, if it is present. The function ``Finset.erase`` handles that.
OMIT. -/
/- TEXT:
ここからが本番です．素数の集合 ``s`` が与えられたときに，その集合から3が存在する場合に3を取り除いたものについて語る必要があります．関数 ``Finset.erase`` がこれを実現します．
EXAMPLES: -/
-- QUOTE:
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
-- QUOTE.

/- OMIT:
We are now ready to prove that there are infinitely many primes
congruent to 3 modulo 4.
Fill in the missing parts below.
Our solution uses ``Nat.dvd_add_iff_left`` and ``Nat.dvd_sub'``
along the way.
OMIT. -/
/- TEXT:
これで4を法とした3に合同な素数が無限にあることを証明する準備ができました．以下の欠けている箇所を埋めましょう．本書で用意している解答では ``Nat.dvd_add_iff_left`` と ``Nat.dvd_sub'`` を途中で使っています．
BOTH: -/
-- QUOTE:
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [add_comm, Nat.add_mul_mod_self_left]
-- BOTH:
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [← hs p]
    exact ⟨pp, p4eq⟩
-- BOTH:
  have pne3 : p ≠ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro peq
    rw [peq, ← Nat.dvd_add_iff_left (dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro n
      simp [← hs n]
      tauto
    simp at this
-- BOTH:
  have : p ∣ 4 * ∏ i in erase s 3, i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_trans _ (dvd_mul_left _ _)
    apply dvd_prod_of_mem
    simp
    constructor <;> assumption
-- BOTH:
  have : p ∣ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  have : p = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply pp.eq_of_dvd_of_prime Nat.prime_three this
-- BOTH:
  contradiction
-- QUOTE.

/- OMIT:
If you managed to complete the proof, congratulations! This has been a serious
feat of formalization.
OMIT. -/
/- TEXT:
もしこの証明を完成させることができましたらおめでとうございます！これは形式化において重大な偉業です．
TEXT. -/
-- OMIT:
/-
Later:
o fibonacci numbers
o binomial coefficients

(The former is a good example of having more than one base case.)

TODO: mention ``local attribute`` at some point.
-/

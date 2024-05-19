.. _sets_and_functions:

集合と関数
==================

.. Sets and Functions
.. ==================

.. The vocabulary of sets, relations, and functions provides a uniform
.. language for carrying out constructions in all the branches of
.. mathematics.
.. Since functions and relations can be defined in terms of sets,
.. axiomatic set theory can be used as a foundation for mathematics.

集合，関係，関数の用語は，数学の全分野を構成するための統一的な言語を提供します．関数と関数は集合で定義できるので，数学の基礎として公理的集合論を利用することができます．

.. Lean's foundation is based instead on the primitive notion of a *type*,
.. and it includes ways of defining functions between types.
.. Every expression in Lean has a type:
.. there are natural numbers, real numbers, functions from reals to reals,
.. groups, vector spaces, and so on.
.. Some expressions *are* types,
.. which is to say,
.. their type is ``Type``.
.. Lean and Mathlib provide ways of defining new types,
.. and ways of defining objects of those types.

Leanの基礎では集合の代わりに *型* という原始的な概念に基づいており，型間の関数を定義する方法を含んでいます．Leanでのすべての式は型を持ちます: 例えば自然数，実数，実数から実数への関数，群，ベクトル空間などがあります．いくつかの式は型 *そのもの* であり，それらの型は ``Type`` です．LeanとMathlibは新しい型を定義する方法と，それらの型のオブジェクトを定義する方法を提供します．

.. Conceptually, you can think of a type as just a set of objects.
.. Requiring every object to have a type has some advantages.
.. For example, it makes it possible to overload notation like ``+``,
.. and it sometimes makes input less verbose
.. because Lean can infer a lot of information from
.. an object's type.
.. The type system also enables Lean to flag errors when you
.. apply a function to the wrong number of arguments,
.. or apply a function to arguments of the wrong type.

概念的には，型はオブジェクトの単なる集合と考えることができます．すべてのオブジェクトに型を要求することにはいくつかの利点があります．例えば， ``+`` のような記法をオーバーロードできるようになり，またLeanがオブジェクトの型から多くの情報を推測できることから入力が冗長にならないこともあります．また，型システムによって，間違った数の引数に関数を適用したり，間違った型の引数に関数を適用した場合にLeanがエラーを出すことができます．

.. Lean's library does define elementary set-theoretic notions.
.. In contrast to set theory,
.. in Lean a set is always a set of objects of some type,
.. such as a set of natural numbers or a set of functions
.. from real numbers to real numbers.
.. The distinction between types and sets takes some getting used to,
.. but this chapter will take you through the essentials.

Leanのライブラリは初等的な集合論的概念を定義しています．集合論とは対照的に，Leanでは集合は常にある型のオブジェクトの集合であり，例えば自然数の集合や実数から実数への関数の集合などです．型と集合の区別には慣れが必要ですが，この章ではその要点を説明します．

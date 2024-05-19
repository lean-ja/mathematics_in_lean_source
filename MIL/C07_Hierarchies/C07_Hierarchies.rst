.. _hierarchies:

階層構造
===========

.. Hierarchies
.. ===========

.. We have seen in :numref:`Chapter %s <structures>` how to define the class
.. of groups and build instances of this class, and then how to build an instance
.. of the commutative ring class. But of course there is a hierarchy here: a
.. commutative ring is in particular an additive group. In this chapter we
.. will study how to build such hierarchies. They appear in all branches
.. of mathematics but in this chapter the emphasis will be on algebraic examples.

:numref:`Chapter %s <structures>` では群のクラスを定義し，このクラスのインスタンスを構築する方法，そして可換環クラスのインスタンスを構築する方法について見てきました．しかしもちろんこのような構造間には階層があります: 特に可換環は加群です．この章では，このような階層の作り方を学んでいきます．このような階層は数学のあらゆる分野に現れますが，この章では代数的な例に重点を置きます．

.. It may seem premature to discuss how to build hierarchies before more discussions
.. about using existing hierarchies. But some understanding of the technology underlying
.. hierarchies is required to use them. So you should probably still read this chapter,
.. but without trying too hard to remember everything on your first read, then read
.. the following chapters and come back here for a second reading.

Leanにもうすでに定義されている階層構造の使い方を学ぶ前に，階層の作り方について議論するのは時期尚早と思われるかもしれません．しかし，階層を使用するためには，階層の基礎となる技術をある程度理解する必要があります．そのため，この章は読むべきではあります，が初見ですべてを覚えようと頑張りすぎず，次の章を読んでからもう一度ここに戻って読むとよいでしょう．

.. In this chapter, we will redefine (simpler versions of) many things that appear in Mathlib
.. so we will used indices to distinguish our version. For instance we will have ``Ring₁``
.. as our version of ``Ring``. Since we will gradually explain more powerful ways of formalizing
.. structures, those indices will sometimes grow beyond one.

この章では，Mathlibに登場する多くの階層を（簡易的に）再定義するので，添え字を用いてMathlibのものと区別します．例えば， ``Ring`` に対して，以下では ``Ring₁`` として定義します．構造の形式化について順を追って強力な方法を説明していくので，これらの添え字は1より大きくなることがあります．

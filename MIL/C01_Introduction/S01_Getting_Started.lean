/- OMIT:
Getting Started
---------------
OMIT. -/
/- TEXT:
本書の始め方
------------

TEXT. -/
/- OMIT:
The goal of this book is to teach you to formalize mathematics using the
Lean 4 interactive proof assistant.
It assumes that you know some mathematics, but it does not require much.
Although we will cover examples ranging from number theory
to measure theory and analysis,
we will focus on elementary aspects of those fields,
in the hopes that if they are not familiar to you,
you can pick them up as you go.
We also don't presuppose any background with formal methods.
Formalization can be seen as a kind of computer programming:
we will write mathematical definitions, theorems, and proofs in
a regimented language, like a programming language,
that Lean can understand.
In return, Lean provides feedback and information,
interprets expressions and guarantees that they are well-formed,
and ultimately certifies the correctness of our proofs.

OMIT. -/
/- TEXT:
本書の最終的な目標は，Lean4の対話的な証明アシスタントを用いた数学の定式化の方法を伝授することです．これにあたって読者にはある程度数学知識があることを前提にしますが，それほど多くは必要ではありません．本書では数論から測度論，解析学までの内容を取り上げますが，ここではこれらの分野の初歩的な側面のみに焦点をあてます．もし上記の中に馴染みのない分野があったとしても，順を追って本書を読み進めていくことで理解できることを期待しています．また，本書では形式手法の学習経験があることも前提としません．形式化は一種のコンピュータープログラミングと見なすことが出来ます:本書において数学の定義，定理，証明はLeanが理解できるようにプログラミング言語のような規則化された言語で記述します．こうすることによりLeanは与えられた式を解釈してその式が適格であることを保証し，そして最終的に「証明の正しさ」の証明をフィードバックとして提供します．

TEXT. -/
/- OMIT:
You can learn more about Lean from the
`Lean project page <https://leanprover.github.io>`_
and the
`Lean community web pages <https://leanprover-community.github.io/>`_.
This tutorial is based on Lean's large and ever-growing library, *Mathlib*.
We also strongly recommend joining the
`Lean Zulip online chat group <https://leanprover.zulipchat.com/>`_
if you haven't already.

OMIT. -/
/- TEXT:
Leanについての詳細な情報は `Lean project page <https://leanprover.github.io>`_ や `Lean community web pages <https://leanprover-community.github.io/>`_ で得られます．このチュートリアルはLeanの大規模で，今もなお成長し続けているライブラリである*Mathlib*に基づいています．またもしまだ参加していないのでしたら， `Lean Zulip online chat group <https://leanprover.zulipchat.com/>`_ に参加することを強く推奨します．そこはLeanの熱狂的なファンによる誰でも歓迎する活気に満ちたコミュニティで，喜んで読者の質問に答えたり精神的なサポートをしてくれるでしょう．

TEXT. -/
/- OMIT:
Although you can read a pdf or html version of this book online,
it designed to be read interactively,
running Lean from inside the VS Code editor.
To get started:

1. Install Lean 4 and VS Code following
   these `installation instructions <https://leanprover-community.github.io/get_started.html>`_.

2. Make sure you have `git <https://git-scm.com/>`_ installed.

3. Follow these `instructions <https://leanprover-community.github.io/install/project.html#working-on-an-existing-project>`_
   to fetch the ``mathematics_in_lean`` repository and open it up in VS Code.

4. Each section in this book has an associated Lean file with examples and exercises.
   You can find them in the folder ``MIL``, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy ``my_files`` or whatever you want and use it to create
   your own Lean files as well.

OMIT. -/
/- TEXT:
本書はPDF版もしくはHTML版をオンラインで読むことができるようになっていますが，同時にVSCode内でLeanを実行しながら対話的に読めるようにも設計されています．この方法は以下の手順で始められます:

1. Lean4とVSCodeを `installation instructions <https://leanprover-community.github.io/get_started.html>`_ に従ってインストールします．

2. `git <https://git-scm.com/>`_ がインストールされていることを確認してください．

3. `instructions <https://leanprover-community.github.io/install/project.html#working-on-an-existing-project>`_ に従って ``mathematics_in_lean`` リポジトリをフェッチしてVSCodeで開いてください．

4. 本書の各セクションには例題や練習問題を含むLeanファイルが対応付けられています．これらのファイルは ``MIL`` フォルダ内にチャプタごとで格納されています．本書ではこのフォルダをコピーし，そこで動作確認や練習を行うことを強くお勧めします．これによりオリジナルのファイルはそのまま残り，リポジトリの変更に伴う更新も容易になります．（詳細は下記を参照）読者はこのコピーに``my_files``等の名前をつけ、これを使って新たに独自のLeanファイルを追加することもできます．

TEXT. -/
/- OMIT:
At that point, you can open the textbook in a side panel in VS Code as follows:

1. Type ``ctrl-shift-P`` (``command-shift-P`` in macOS).

2. Type ``Lean 4: Open Documentation View`` in the bar that appears, and then
   press return. (You can press return to select it as soon as it is highlighted
   in the menu.)

3. In the window that opens, click on ``Open documentation of current project``.

OMIT. -/
/- TEXT:
この時点で，以下のようにVSCodeのサイドパネルで教科書を開くことが出来ます:

1. ``ctrl-shift-P`` (Macの場合は ``command-shift-P`` )を押下します．

2. 上記手順で現れたバーで ``Lean 4: Open Documentation View`` と打ち込み，エンターキーを押下します．（もしくはメニュー内で上記の文字列が選択されてハイライトされている場合はそのままエンターキーを押下することも可能です．）

3. これで開いたウィンドウで ``Open documentation of current project`` をクリックします．

TEXT. -/
/- OMIT:
Alternatively, you can run Lean and VS Code in the cloud,
using `Gitpod <https://gitpod.io/>`_.
You can find instructions as to how to do that on the Mathematics in Lean
`project page <https://github.com/leanprover-community/mathematics_in_lean>`_
on Github. We still recommend working in a copy of the `MIL` folder,
as described above.

OMIT. -/
/- TEXT:
また，LeanとVSCodeを `Gitpod <https://gitpod.io/>`_ を使ってクラウド上で実行することも可能です．Mathematics in Leanについてこの方法を行うにはGithub上の `project page <https://github.com/leanprover-community/mathematics_in_lean>`_ に手順があります．この場合も前述したとおり`MIL`フォルダの複製上で学習を行うことをお勧めします．

TEXT. -/
/- OMIT:
This textbook and the associated repository are still a work in progress.
You can update the repository by typing ``git pull``
followed by ``lake exe cache get`` inside the ``mathematics_in_lean`` folder.
(This assumes that you have not changed the contents of the ``MIL`` folder,
which is why we suggested making a copy.)

OMIT. -/
/- TEXT:
本書とこれに関連するリポジトリは現在も開発中です．リポジトリを更新するには ``mathematics_in_lean`` フォルダ内で ``git pull`` と打ち込み， ``lake exe cache get`` を実行します．（この手順は``MIL``フォルダ内のコンテンツを変更していないことを仮定しています．これがフォルダをコピーすることを推奨している理由です．）

TEXT. -/
/- OMIT:
We intend for you to work on the exercises in the ``MIL`` folder while reading the
textbook, which contains explanations, instructions, and hints.
The text will often include examples, like this one:
OMIT. -/
/- TEXT:
``MIL`` フォルダ内の練習問題は教科書中にある解説や指示，ヒントを読みながら取り組むことを想定しています．また本書ではしばしば次のような例を記載しています:
TEXT. -/
-- QUOTE:
#eval "Hello, World!"
-- QUOTE.

/- OMIT:
You should be able to find the corresponding example in the associated
Lean file.
If you click on the line, VS Code will show you Lean's feedback in
the ``Lean Goal`` window, and if you hover
your cursor over the ``#eval`` command VS Code will show you Lean's response
to this command in a pop-up window.
You are encouraged to edit the file and try examples of your own.

OMIT. -/
/- TEXT:
このような例を関連するLeanファイル中に見つけることができるでしょう．この行をクリックすると，VSCodeは ``Lean Goal`` ウィンドウ内にLeanによるフィードバックを表示し，また ``#eval`` コマンドにカーソルを合わせるとポップアップでこのコマンドに対するLeanの出力結果を表示します．試しにこのファイルを編集して挙動を確認することをお勧めします．

TEXT. -/
/- OMIT:
This book moreover provides lots of challenging exercises for you to try.
Don't rush past these!
Lean is about *doing* mathematics interactively, not just reading about it.
Working through the exercises is central to the experience.
You don't have to do all of them; when you feel comfortable that you have mastered
the relevant skills, feel free to move on.
You can always compare your solutions to the ones in the ``solutions``
folder associated with each section.
OMIT. -/
/- TEXT:
本書ではさらに挑戦し甲斐のある練習問題をたくさん掲載しています．しかし焦ってはいけません！Leanは数学を対話的に *実行する* ものであり，読むだけのものではありません．実際に練習をこなすことがLean学習における必要な経験の中心です．全ての練習問題をこなす必要はありません．もし関連するスキルが身に着いたと感じたら，遠慮なく次に進んでください．そして読者はいつでも自身の回答と各セクションに関連する ``solutions`` フォルダにある回答と比較することが出来ます．
TEXT. -/

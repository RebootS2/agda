module MultiplicationBinaryComp where

-- ---------------------------------------------------------------------------
-- 0. 証明に使うライブラリ読み込みと定義
-- ---------------------------------------------------------------------------
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- 正の二進数（先頭が必ず1になる二進数を構成する0, 1の並びから発想して定義）
data Pos : Set where
  one : Pos         -- 1
  _O  : Pos → Pos   -- 2n (末尾に0)
  _I  : Pos → Pos   -- 2n + 1 (末尾に1)

-- 二進数の定義（ゼロも含む定義）
data Bin : Set where
   zero : Bin
   pos  : Pos → Bin  -- Pos → Bin

-- 補助関数：二進数で自然数を網羅するため下一桁で場合分け
-- 足し算は使わず、場合分けで実装する。
-- seqB-Pos : Sequential Binary - Positive integers.
seq-BPos : Pos → Pos
seq-BPos one = (_O one)
seq-BPos (_O b) = _I b
seq-BPos (_I b) = _O (seq-BPos b)

-- 左シフト、すなわち2倍を定義
-- 二進数を与えると2倍を返す。
-- 足し算は使っていない。
x2Bin : Bin → Bin
x2Bin zero = zero
x2Bin (pos p) = pos (_O p)

-- 論理演算テーブル（XORとANDのビット演算回路みたいなもの）
-- 下一桁で場合分けをして、変換結果を返すテーブル
-- 有限であって、当然計算は終了する。
-- これはAgdaが保証してくれている。
_convRuleFin_ : Pos → Pos → Pos                          -- arrange token (2)
one    convRuleFin one    = _O one                       -- [1] c [1] = [10]
one    convRuleFin (_O y) = _I y                         -- [1] c [y0] = [y1]
one    convRuleFin (_I y) = _O (seq-BPos y)              -- [1] c [y1] = [[y next] 0]

(_O x) convRuleFin one    = _I x                         -- [x0] c [1] = [x1]
(_O x) convRuleFin (_O y) = _O (x convRuleFin y)         -- [x0] c [y0] = [[x] c [y] 0]
(_O x) convRuleFin (_I y) = _I (x convRuleFin y)         -- [x0] c [y1] = [[x] c [y] 1]

(_I x) convRuleFin one    = _O (seq-BPos x)              -- [x0] c [1] = [[x next] 0 ]
(_I x) convRuleFin (_O y) = _I (x convRuleFin y)                -- [x1] c [y0] = [[x] c [y] 1]
(_I x) convRuleFin (_I y) = _O (seq-BPos (x convRuleFin y))     -- [x1] c [y1] = [[[x] c [y]] next] 0]

-- 上記の論理演算テーブルでは場合分けが見えにくいため
-- 二進数の2項の演算に落とし込んだ演算Aを作ってみる。
-- CalAとした。
_CalA_ : Bin → Bin → Bin
zero   CalA y      = y
x      CalA zero   = x
pos x  CalA pos y  = pos (x convRuleFin y)

-- CalBを作ってみる。そろそろ乗算にできそう。
-- 構造的定義します。
_CalB_ : Bin → Bin → Bin
_ CalB zero = zero
zero CalB _ = zero
pos(x) CalB pos(one) = pos(x)
pos(x) CalB pos(_O y) = x2Bin(pos(x) CalB pos(y)) -- パターン1: 単なる左シフト
pos(x) CalB pos(_I y) = pos(x) CalA x2Bin(pos(x) CalB pos(y))  -- パターン2: シフト結果とCalAを借りた。

-- All Done!
-- 抜けなし。この関数は何でしょね。

-- ---------------------------------------------------------------------------
-- A. 自然数で検算（自然数の演算の定義はライブラリで済ます）
-- MultiplicationBinary.agdaで検証済み
-- ---------------------------------------------------------------------------
-- ---------------------------------------------------------------------------
-- B. 形式的に交換則を証明する
-- ---------------------------------------------------------------------------

-- 補題1：論理演算テーブル（convRuleFin）の交換法則
-- 「引数 x, y を入れ替えても結果が等しい」ことを、9通りのパターン全てで証明
convRuleFin-comm : (x y : Pos) → (x convRuleFin y) ≡ (y convRuleFin x)
convRuleFin-comm one one       = refl
convRuleFin-comm one (_O y)    = refl
convRuleFin-comm one (_I y)    = refl
convRuleFin-comm (_O x) one    = refl
convRuleFin-comm (_I x) one    = refl

-- 以下は、cong（関数の合同性： a ≡ b ならば f(a) ≡ f(b)）を利用
convRuleFin-comm (_O x) (_O y) = cong _O (convRuleFin-comm x y)
convRuleFin-comm (_O x) (_I y) = cong _I (convRuleFin-comm x y)
convRuleFin-comm (_I x) (_O y) = cong _I (convRuleFin-comm x y)
convRuleFin-comm (_I x) (_I y) = cong (λ k → _O (seq-BPos k)) (convRuleFin-comm x y)
-- 論理演算テーブルの交換則証明完

-- 1：CalAの交換法則
CalA-comm : (x y : Bin) → (x CalA y) ≡ (y CalA x)
CalA-comm zero zero       = refl
CalA-comm zero (pos y)    = refl
CalA-comm (pos x) zero    = refl
CalA-comm (pos x) (pos y) = cong pos (convRuleFin-comm x y)

-- 2：(x CalA y) CalA z ≡ x CalA (y CalA z) 結合則
-- 1補助左から：convRuleFin oneは、桁上がり（seq-BPos）と完全に等価
CRF-one-L : (x : Pos) → one convRuleFin x ≡ seq-BPos x
CRF-one-L one = refl
CRF-one-L (_O x) = refl
CRF-one-L (_I x) = refl
-- 1補助右から：convRuleFin oneは、桁上がり（seq-BPos）と完全に等価
CRF-one-R : (x : Pos) → x convRuleFin one ≡ seq-BPos x
CRF-one-R one = refl
CRF-one-R (_O x) = refl
CRF-one-R (_I x) = refl

-- 2補助：桁上がり（seq-BPos）の伝播
-- 「計算結果に桁上がりする」ことと、「左辺（または右辺）をあらかじめ桁上がりさせてから計算する」ことは等価
-- 左から
seq-BPos-conv-L : (x y : Pos) → seq-BPos (x convRuleFin y) ≡ (seq-BPos x) convRuleFin y
seq-BPos-conv-L one one       = refl
seq-BPos-conv-L one (_O y)    = cong _O (sym (CRF-one-L y))
seq-BPos-conv-L one (_I y)    = cong _I (sym (CRF-one-L y))
seq-BPos-conv-L (_O x) one    = refl
seq-BPos-conv-L (_O x) (_O y) = refl
seq-BPos-conv-L (_O x) (_I y) = refl
seq-BPos-conv-L (_I x) one    = refl
seq-BPos-conv-L (_I x) (_O y) = cong _O (seq-BPos-conv-L x y)
seq-BPos-conv-L (_I x) (_I y) = cong _I (seq-BPos-conv-L x y)
-- 右から
seq-BPos-conv-R : (x y : Pos) → seq-BPos (x convRuleFin y) ≡ x convRuleFin (seq-BPos y)
seq-BPos-conv-R one one       = refl
seq-BPos-conv-R one (_O y)    = refl
seq-BPos-conv-R one (_I y)    = refl
seq-BPos-conv-R (_O x) one    = cong _O (sym (CRF-one-R x))
seq-BPos-conv-R (_O x) (_O y) = refl
seq-BPos-conv-R (_O x) (_I y) = cong _O (seq-BPos-conv-R x y)
seq-BPos-conv-R (_I x) one    = cong _I (sym (CRF-one-R x))
seq-BPos-conv-R (_I x) (_O y) = refl
seq-BPos-conv-R (_I x) (_I y) = cong _I (seq-BPos-conv-R x y)

-- 変換テーブルの結合法則（{one, _O, _I} 3通りの3つの組み合わせ27パターンの網羅的検証）
convRuleFin-assoc : (x y z : Pos) → ((x convRuleFin y) convRuleFin z) ≡ (x convRuleFin (y convRuleFin z))
-- パターン1〜9：x が one の場合
convRuleFin-assoc one one one       = refl
convRuleFin-assoc one one (_O z)    = cong _O (CRF-one-L z)
convRuleFin-assoc one one (_I z)    = cong _I (CRF-one-L z)
convRuleFin-assoc one (_O y) one    = refl
convRuleFin-assoc one (_O y) (_O z) = refl
convRuleFin-assoc one (_O y) (_I z) = refl
convRuleFin-assoc one (_I y) one    = refl
convRuleFin-assoc one (_I y) (_O z) = cong _O (sym (seq-BPos-conv-L y z))
convRuleFin-assoc one (_I y) (_I z) = cong _I (sym (seq-BPos-conv-L y z))

-- パターン10〜18：x が (_O x) の場合
convRuleFin-assoc (_O x) one one       = cong _O (sym (CRF-one-R x))
convRuleFin-assoc (_O x) one (_O z)    = refl
convRuleFin-assoc (_O x) one (_I z)    = cong _O (seq-BPos-conv-R x z)
convRuleFin-assoc (_O x) (_O y) one    = refl
convRuleFin-assoc (_O x) (_O y) (_O z) = cong _O (convRuleFin-assoc x y z)
convRuleFin-assoc (_O x) (_O y) (_I z) = cong _I (convRuleFin-assoc x y z)
convRuleFin-assoc (_O x) (_I y) one    = cong _O (seq-BPos-conv-R x y)
convRuleFin-assoc (_O x) (_I y) (_O z) = cong _I (convRuleFin-assoc x y z)
convRuleFin-assoc (_O x) (_I y) (_I z) = cong _O (trans (cong seq-BPos (convRuleFin-assoc x y z)) (seq-BPos-conv-R x (y c z))) 
  where _c_ = _convRuleFin_

-- パターン19〜27：x が (_I x) の場合
convRuleFin-assoc (_I x) one one       = cong _I (sym (CRF-one-R x))
convRuleFin-assoc (_I x) one (_O z)    = cong _O (sym (seq-BPos-conv-L x z))
convRuleFin-assoc (_I x) one (_I z)    = cong _I (trans (sym (seq-BPos-conv-L x z)) (seq-BPos-conv-R x z))
convRuleFin-assoc (_I x) (_O y) one    = refl
convRuleFin-assoc (_I x) (_O y) (_O z) = cong _I (convRuleFin-assoc x y z)
convRuleFin-assoc (_I x) (_O y) (_I z) = cong (λ k → _O (seq-BPos k)) (convRuleFin-assoc x y z)
convRuleFin-assoc (_I x) (_I y) one    = cong _I (seq-BPos-conv-R x y)
convRuleFin-assoc (_I x) (_I y) (_O z) = cong _O (trans (sym (seq-BPos-conv-L (x c y) z)) (cong seq-BPos (convRuleFin-assoc x y z))) 
  where _c_ = _convRuleFin_
convRuleFin-assoc (_I x) (_I y) (_I z) = cong _I (trans (trans (sym (seq-BPos-conv-L (x c y) z)) (cong seq-BPos (convRuleFin-assoc x y z))) (seq-BPos-conv-R x (y c z)))
  where _c_ = _convRuleFin_
-- 変換テーブルの結合則の証明完了

-- 実質、掛け算になるCalBの左側から1を掛ける操作（単位元）の証明
CalB-id-left : (y : Pos) → pos one CalB pos y ≡ pos y
CalB-id-left one    = refl
CalB-id-left (_O y) = cong x2Bin (CalB-id-left y)
CalB-id-left (_I y) = cong (λ k → pos one CalA x2Bin k) (CalB-id-left y)
-- 証明完了

-- ===========================================================================
-- 加算の結合法則の証明（CalAは 加算）
-- ===========================================================================
-- 【定理】加算の結合法則
CalA-assoc : (x y z : Bin) → (x CalA y) CalA z ≡ x CalA (y CalA z)
CalA-assoc zero y z       = refl
CalA-assoc (pos x) zero z = refl
CalA-assoc (pos x) (pos y) zero = refl
CalA-assoc (pos x) (pos y) (pos z) = cong pos (convRuleFin-assoc x y z)
-- ===========================================================================
-- 左シフトと加算と分配法則の証明（CalAは 加算）
-- ===========================================================================
-- 【定理】左シフト（2倍）と加算の分配法則
-- （2x + 2y = 2(x + y) の証明
x2Bin-distrib : (x y : Bin) → x2Bin (x CalA y) ≡ (x2Bin x) CalA (x2Bin y)
x2Bin-distrib zero y = refl
x2Bin-distrib (pos x) zero = refl
x2Bin-distrib (pos x) (pos y) = refl

-- ===========================================================================
-- 乗算 0をかける 証明
-- ===========================================================================
-- 【定理】ゼロの性質（x * 0 = 0, 0 * x = 0）
-- 右から
CalB-zero-right : (x : Bin) → x CalB zero ≡ zero
CalB-zero-right zero    = refl
CalB-zero-right (pos x) = refl
-- 左から
CalB-zero-left : (y : Bin) → zero CalB y ≡ zero
CalB-zero-left zero    = refl
CalB-zero-left (pos y) = refl

-- ===========================================================================
-- （追加）加算 右から0を足す 証明　（agda回すのに必要だった。追加。）
-- ===========================================================================
-- 【追加定理】加算の右ゼロ（x + 0 = x）
CalA-zero-right : (x : Bin) → x CalA zero ≡ x
CalA-zero-right zero = refl
CalA-zero-right (pos x) = refl


-- ===========================================================================
-- 2進数ならではの分配法則のための4つの補助定理（Lemma）
-- ===========================================================================
-- 補助定理1： x + x = 2x の証明
-- 同じ数を足すと、左シフトした結果と完全に一致することの証明
convRuleFin-self : (x : Pos) → x convRuleFin x ≡ _O x
convRuleFin-self one    = refl
convRuleFin-self (_O x) = cong _O (convRuleFin-self x)
convRuleFin-self (_I x) = cong (λ k → _O (seq-BPos k)) (convRuleFin-self x)

CalA-self : (x : Pos) → pos x CalA pos x ≡ pos (_O x)
CalA-self x = cong pos (convRuleFin-self x)

-- 補助定理2：加算の左入れ替え（ a + (b + c) = b + (a + c) ）
-- 証明済み結合法則と交換法則を組み合わせて証明
CalA-left-comm : (a b c : Bin) → a CalA (b CalA c) ≡ b CalA (a CalA c)
CalA-left-comm a b c = 
  begin
    a CalA (b CalA c)
  ≡⟨ sym (CalA-assoc a b c) ⟩
    (a CalA b) CalA c
  ≡⟨ cong (λ k → k CalA c) (CalA-comm a b) ⟩
    (b CalA a) CalA c
  ≡⟨ CalA-assoc b a c ⟩
    b CalA (a CalA c)
  ∎

-- 補助定理3：結合の変更（ (x+x) + (y+z) = (x+y) + (x+z) ）
CalA-shuffle2 : (x y z : Bin) → (x CalA x) CalA (y CalA z) ≡ (x CalA y) CalA (x CalA z)
CalA-shuffle2 x y z = 
  begin
    (x CalA x) CalA (y CalA z)
  ≡⟨ CalA-assoc x x (y CalA z) ⟩
    x CalA (x CalA (y CalA z))
  ≡⟨ cong (λ k → x CalA k) (CalA-left-comm x y z) ⟩
    x CalA (y CalA (x CalA z))
  ≡⟨ sym (CalA-assoc x y (x CalA z)) ⟩
    (x CalA y) CalA (x CalA z)
  ∎

-- 1-4. 乗算と加算の分配法則
-- 補助定理4： x * (y + 1) = x * y + x の証明
CalB-succ : (x y : Pos) → pos x CalB pos (seq-BPos y) ≡ pos x CalA (pos x CalB pos y)
CalB-succ x one    = sym (CalA-self x)
CalB-succ x (_O y) = refl
CalB-succ x (_I y) = 
  begin
    x2Bin (pos x CalB pos (seq-BPos y))
  ≡⟨ cong x2Bin (CalB-succ x y) ⟩
    x2Bin (pos x CalA (pos x CalB pos y))
  ≡⟨ x2Bin-distrib (pos x) (pos x CalB pos y) ⟩
    pos (_O x) CalA x2Bin (pos x CalB pos y)
  ≡⟨ cong (λ k → k CalA x2Bin (pos x CalB pos y)) (sym (CalA-self x)) ⟩
    (pos x CalA pos x) CalA x2Bin (pos x CalB pos y)
  ≡⟨ CalA-assoc (pos x) (pos x) (x2Bin (pos x CalB pos y)) ⟩
    pos x CalA (pos x CalA x2Bin (pos x CalB pos y))
  ∎

-- ===========================================================================
-- 乗算と加算の分配法則の証明
-- ===========================================================================
-- yとzが{one, _O, _I}3通りの2つの組み合わせで9パターン
Pos-distrib : (x y z : Pos) → pos x CalB pos (y convRuleFin z) ≡ (pos x CalB pos y) CalA (pos x CalB pos z)

-- パターン1〜3：y が one の場合
Pos-distrib x one one = sym (CalA-self x)
Pos-distrib x one (_O z) = refl
Pos-distrib x one (_I z) = 
  begin
    x2Bin (pos x CalB pos (seq-BPos z))
  ≡⟨ cong x2Bin (CalB-succ x z) ⟩
    x2Bin (pos x CalA (pos x CalB pos z))       
  ≡⟨ x2Bin-distrib (pos x) (pos x CalB pos z) ⟩
    pos (_O x) CalA x2Bin (pos x CalB pos z)
  ≡⟨ cong (λ k → k CalA x2Bin (pos x CalB pos z)) (sym (CalA-self x)) ⟩
    (pos x CalA pos x) CalA x2Bin (pos x CalB pos z)
  ≡⟨ CalA-assoc (pos x) (pos x) (x2Bin (pos x CalB pos z)) ⟩
    pos x CalA (pos x CalA x2Bin (pos x CalB pos z))
  ∎

-- パターン4〜6：y が (_O y) の場合
Pos-distrib x (_O y) one = CalA-comm (pos x) (x2Bin (pos x CalB pos y))
Pos-distrib x (_O y) (_O z) = 
  begin
    x2Bin (pos x CalB pos (y convRuleFin z))
  ≡⟨ cong x2Bin (Pos-distrib x y z) ⟩
    x2Bin ((pos x CalB pos y) CalA (pos x CalB pos z))
  ≡⟨ x2Bin-distrib (pos x CalB pos y) (pos x CalB pos z) ⟩
    x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z)
  ∎
Pos-distrib x (_O y) (_I z) = 
  begin
    pos x CalA x2Bin (pos x CalB pos (y convRuleFin z))
  ≡⟨ cong (λ k → pos x CalA x2Bin k) (Pos-distrib x y z) ⟩
    pos x CalA x2Bin ((pos x CalB pos y) CalA (pos x CalB pos z))
  ≡⟨ cong (λ k → pos x CalA k) (x2Bin-distrib (pos x CalB pos y) (pos x CalB pos z)) ⟩
    pos x CalA (x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z))
  ≡⟨ CalA-left-comm (pos x) (x2Bin (pos x CalB pos y)) (x2Bin (pos x CalB pos z)) ⟩
    x2Bin (pos x CalB pos y) CalA (pos x CalA x2Bin (pos x CalB pos z))
  ∎

-- パターン7〜9：y が (_I y) の場合
Pos-distrib x (_I y) one = 
  begin
    x2Bin (pos x CalB pos (seq-BPos y))
  ≡⟨ cong x2Bin (CalB-succ x y) ⟩
    x2Bin (pos x CalA (pos x CalB pos y))      
  ≡⟨ x2Bin-distrib (pos x) (pos x CalB pos y) ⟩
    pos (_O x) CalA x2Bin (pos x CalB pos y)
  ≡⟨ cong (λ k → k CalA x2Bin (pos x CalB pos y)) (sym (CalA-self x)) ⟩
    (pos x CalA pos x) CalA x2Bin (pos x CalB pos y)
  ≡⟨ CalA-assoc (pos x) (pos x) (x2Bin (pos x CalB pos y)) ⟩
    pos x CalA (pos x CalA x2Bin (pos x CalB pos y))
  ≡⟨ CalA-comm (pos x) (pos x CalA x2Bin (pos x CalB pos y)) ⟩
    (pos x CalA x2Bin (pos x CalB pos y)) CalA pos x
  ∎
Pos-distrib x (_I y) (_O z) = 
  begin
    pos x CalA x2Bin (pos x CalB pos (y convRuleFin z))
  ≡⟨ cong (λ k → pos x CalA x2Bin k) (Pos-distrib x y z) ⟩
    pos x CalA x2Bin ((pos x CalB pos y) CalA (pos x CalB pos z))
  ≡⟨ cong (λ k → pos x CalA k) (x2Bin-distrib (pos x CalB pos y) (pos x CalB pos z)) ⟩
    pos x CalA (x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z))
  ≡⟨ sym (CalA-assoc (pos x) (x2Bin (pos x CalB pos y)) (x2Bin (pos x CalB pos z))) ⟩
    (pos x CalA x2Bin (pos x CalB pos y)) CalA x2Bin (pos x CalB pos z)
  ∎
Pos-distrib x (_I y) (_I z) = 
  begin
    x2Bin (pos x CalB pos (seq-BPos (y convRuleFin z)))
  ≡⟨ cong x2Bin (CalB-succ x (y convRuleFin z)) ⟩
    x2Bin (pos x CalA (pos x CalB pos (y convRuleFin z)))
  ≡⟨ x2Bin-distrib (pos x) (pos x CalB pos (y convRuleFin z)) ⟩
    pos (_O x) CalA x2Bin (pos x CalB pos (y convRuleFin z))
  ≡⟨ cong (λ k → pos (_O x) CalA x2Bin k) (Pos-distrib x y z) ⟩
    pos (_O x) CalA x2Bin ((pos x CalB pos y) CalA (pos x CalB pos z)) 
  ≡⟨ cong (λ k → pos (_O x) CalA k) (x2Bin-distrib (pos x CalB pos y) (pos x CalB pos z)) ⟩
    pos (_O x) CalA (x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z))
  ≡⟨ cong (λ k → k CalA (x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z))) (sym (CalA-self x)) ⟩
    (pos x CalA pos x) CalA (x2Bin (pos x CalB pos y) CalA x2Bin (pos x CalB pos z))
  ≡⟨ CalA-shuffle2 (pos x) (x2Bin (pos x CalB pos y)) (x2Bin (pos x CalB pos z)) ⟩
    (pos x CalA x2Bin (pos x CalB pos y)) CalA (pos x CalA x2Bin (pos x CalB pos z))
  ∎

-- ===========================================================================
-- 乗算の交換法則の証明の最終準備　補助定理の導入
-- ===========================================================================
-- 補助定理1: 奇数と偶数の加算の変形
-- pos (_I x) CalA pos (_O y) と pos (_I y) CalA pos (_O x) が等しい証明
CalA-cross : (x y : Pos) → pos (_I x) CalA pos (_O y) ≡ pos (_I y) CalA pos (_O x)
CalA-cross x y = cong (λ k → pos (_I k)) (convRuleFin-comm x y)

-- 補助定理2: 左シフトの左からの掛け算への分配 ((2x) * y = 2 * (x * y))
CalB-x2Bin-left : (x y : Pos) → pos (_O x) CalB pos y ≡ x2Bin (pos x CalB pos y)
CalB-x2Bin-left x one = refl
CalB-x2Bin-left x (_O y) = 
  begin
    x2Bin (pos (_O x) CalB pos y)
  ≡⟨ cong x2Bin (CalB-x2Bin-left x y) ⟩
    x2Bin (x2Bin (pos x CalB pos y))
  ∎
CalB-x2Bin-left x (_I y) = 
  begin
    pos (_O x) CalA x2Bin (pos (_O x) CalB pos y)
  ≡⟨ cong (λ k → pos (_O x) CalA x2Bin k) (CalB-x2Bin-left x y) ⟩
    pos (_O x) CalA x2Bin (x2Bin (pos x CalB pos y))
  ≡⟨ sym (x2Bin-distrib (pos x) (x2Bin (pos x CalB pos y))) ⟩
    x2Bin (pos x CalA x2Bin (pos x CalB pos y))
  ∎

-- 補助定理3: 奇数の左からの掛け算への分配 ((2x + 1) * y = y + 2 * (x * y))
CalB-add-left : (x y : Pos) → pos (_I x) CalB pos y ≡ pos y CalA x2Bin (pos x CalB pos y)
CalB-add-left x one = refl
CalB-add-left x (_O y) = 
  begin
    x2Bin (pos (_I x) CalB pos y)
  ≡⟨ cong x2Bin (CalB-add-left x y) ⟩
    x2Bin (pos y CalA x2Bin (pos x CalB pos y))
  ≡⟨ x2Bin-distrib (pos y) (x2Bin (pos x CalB pos y)) ⟩
    pos (_O y) CalA x2Bin (x2Bin (pos x CalB pos y))
  ∎
CalB-add-left x (_I y) = 
  begin
    pos (_I x) CalA x2Bin (pos (_I x) CalB pos y)
  ≡⟨ cong (λ k → pos (_I x) CalA x2Bin k) (CalB-add-left x y) ⟩
    pos (_I x) CalA x2Bin (pos y CalA x2Bin (pos x CalB pos y))
  ≡⟨ cong (λ k → pos (_I x) CalA k) (x2Bin-distrib (pos y) (x2Bin (pos x CalB pos y))) ⟩
    pos (_I x) CalA (pos (_O y) CalA x2Bin (x2Bin (pos x CalB pos y)))
  ≡⟨ sym (CalA-assoc (pos (_I x)) (pos (_O y)) (x2Bin (x2Bin (pos x CalB pos y)))) ⟩
    (pos (_I x) CalA pos (_O y)) CalA x2Bin (x2Bin (pos x CalB pos y))
  ≡⟨ cong (λ k → k CalA x2Bin (x2Bin (pos x CalB pos y))) (CalA-cross x y) ⟩
    (pos (_I y) CalA pos (_O x)) CalA x2Bin (x2Bin (pos x CalB pos y))
  ≡⟨ CalA-assoc (pos (_I y)) (pos (_O x)) (x2Bin (x2Bin (pos x CalB pos y))) ⟩
    pos (_I y) CalA (pos (_O x) CalA x2Bin (x2Bin (pos x CalB pos y)))
  ≡⟨ cong (λ k → pos (_I y) CalA k) (sym (x2Bin-distrib (pos x) (x2Bin (pos x CalB pos y)))) ⟩
    pos (_I y) CalA x2Bin (pos x CalA x2Bin (pos x CalB pos y))
  ∎

-- ===========================================================================
-- 乗算の交換法則　正の2進数から証明　 (x * y = y * x)　偶数と奇数に分けて証明する
-- ===========================================================================
Pos-mult-comm : (x y : Pos) → pos x CalB pos y ≡ pos y CalB pos x
Pos-mult-comm one y = CalB-id-left y
Pos-mult-comm (_O x) y = 
  begin
    pos (_O x) CalB pos y
  ≡⟨ CalB-x2Bin-left x y ⟩
    x2Bin (pos x CalB pos y)
  ≡⟨ cong x2Bin (Pos-mult-comm x y) ⟩
    x2Bin (pos y CalB pos x)
  ∎

Pos-mult-comm (_I x) y = 
  begin
    pos (_I x) CalB pos y
  ≡⟨ CalB-add-left x y ⟩
    pos y CalA x2Bin (pos x CalB pos y)
  ≡⟨ cong (λ k → pos y CalA x2Bin k) (Pos-mult-comm x y) ⟩
    pos y CalA x2Bin (pos y CalB pos x)
  ∎

-- 補助定理4 乗算と加算の分配法則： x * (y + z) = (x * y) + (x * z)
CalB-distrib : (x y z : Bin) → x CalB (y CalA z) ≡ (x CalB y) CalA (x CalB z)

CalB-distrib zero zero zero = refl
CalB-distrib zero zero (pos z) = refl
CalB-distrib zero (pos y) zero = refl
CalB-distrib zero (pos y) (pos z) = refl

CalB-distrib (pos x) zero zero = refl
CalB-distrib (pos x) zero (pos z) = refl

CalB-distrib (pos x) (pos y) zero = 
  begin
    pos x CalB (pos y CalA zero)
  ≡⟨ refl ⟩ 
    pos x CalB pos y
  ≡⟨ sym (CalA-zero-right (pos x CalB pos y)) ⟩
    (pos x CalB pos y) CalA zero
  ≡⟨ cong (λ k → (pos x CalB pos y) CalA k) (sym (CalB-zero-right (pos x))) ⟩
    (pos x CalB pos y) CalA (pos x CalB zero)
  ∎

-- 全てが正の二進数（pos）の場合を証明
CalB-distrib (pos x) (pos y) (pos z) = Pos-distrib x y z
-- 予め証明済みのPos-distrib x y zを使って証明完了

-- ===========================================================================
-- 2進数の乗算の交換法則　仕上げ　 (x * y = y * x)
-- ===========================================================================
-- 【交換則】乗算の交換法則： x * y = y * x
CalB-comm : (x y : Bin) → x CalB y ≡ y CalB x
CalB-comm zero zero = refl

-- x * 0 = 0 * x の証明
CalB-comm (pos x) zero = 
  begin
    pos x CalB zero
  ≡⟨ CalB-zero-right (pos x) ⟩
    zero
  ≡⟨ sym (CalB-zero-left (pos x)) ⟩
    zero CalB pos x
  ∎

-- 0 * y = y * 0 の証明
CalB-comm zero (pos y) = 
  begin
    zero CalB pos y
  ≡⟨ CalB-zero-left (pos y) ⟩
    zero
  ≡⟨ sym (CalB-zero-right (pos y)) ⟩
    pos y CalB zero
  ∎

-- 正の二進数同士の乗算の交換法則
CalB-comm (pos x) (pos y) = Pos-mult-comm x y
-- 予め証明済みのPos-mult-comm x yを使って証明完了

-- ====================================================================
-- 結論：かけ算を、累加を使わない実装を実現し、交換則を証明した。
-- ====================================================================
-- 本コードは、自然数のかけ算が「累加（Repeated Addition）でしか定義できない」
-- という主張に対する、構成的な反証です。
-- 
-- ペアノ自然数に基づく再帰的加算を使うことなく、二進木構造（Binary Tree）の
-- 帰納的データ型とそのパターンマッチのみを用いて乗算器を実装しました。
-- 本コードに対し、「結局は内部的に同数累加を行っているに過ぎない」という反論が
-- 来る事を見越して、計算機科学の観点から以下の特徴を述べておきます。
-- 
-- ・計算量（オーダー）の断絶
--   同数累加が O(M) のステップ数を要求するのに対し、本アルゴリズムは O(log2 M) の
--   再帰で完了するため、アルゴリズムの計算量クラスが根本から異なります。
-- 
-- ・構造的帰納法（Structural Induction）の違い
--   「1ずつ減らす」という分解単位を回避し、「右シフト（半分にする）」に相当する
--   二進木特有の構造的帰納法を採用することで、累加のロジックを完全排除しました。
-- 
-- ・ビット演算（ブール代数）への還元
--   自然数の足し算ではなく、2進数だからこそ行える直交的なパターンマッチ
--   （XORやAND回路に相当する演算）の組み合わせのみで実装しました。
-- 
-- さらに、2進数のかけ算の交換則を証明しました。
-- 証明の方針は、ペアノの乗算と基本的に同じですが、2進数ならではのシフト、加算に関する
-- 補題が異なります。
-- 場合分けが多いですが、自然数の掛け算と同じですからゴールは見えていて、
-- パターンさえ網羅すれば交換則を示せます。
-- 未知の計算CalAも、結合則、交換則、分配則があることを確認しながら、
-- 補題を立てて検証が完了しました。
-- 以上の結果から、二進数で構成したかけ算にも交換則があることを証明しました。
-- 自然数との一致は、toBin, fromBinを使って、任意の自然数で検証が可能です。
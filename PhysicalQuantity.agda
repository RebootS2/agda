module PhysicalQuantity where

-- ---------------------------------------------------------------------------
-- 0. 証明に使うライブラリ読み込みと定義
-- ---------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- 矛盾の定義
-- 命題を1つも持てない、空の型
-- 命題の存在余地なし。あり得ない＝矛盾を表現
data ⊥ : Set where
  -- 空。具体的な命題を持つ事は不可能

-- 否定の定義（A = A が成り立つなら、矛盾を返す）
¬_ : Set → Set
¬ A = A → ⊥

-- "そんなモノはない"と判断するための関数。
-- 矛盾⊥を渡せたら、どんな命題Aでも返す関数の定義。
-- () が何をするか、を敢えて実装していない＝ここに入る値はない、と言う関数。
-- 矛盾⊥を受ける関数は、現実に絶対に来ない想定なのでagdaは上記を通す仕様。

-- 何かの命題の代わりに()を書くと、
-- その命題が、矛盾以外の値を取り得るか？と型チェックが入る。
-- 矛盾以外の値が一つでも入り得るルートがある場合、敢えて省いた実装に引っかかってエラー発生。
-- 矛盾しかありえない事が保証されると、敢えて省いた実装は実行されずにコンパイルが通る。
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()  -- 型チェックで「可能なパターン」を網羅的にチェック。一つでもあればエラー。

-- ---------------------------------------------------------------------------
-- A. 数の演算 
-- ---------------------------------------------------------------------------
-- 1. 自然数, 演算の定義
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

{-# BUILTIN NATURAL ℕ #-} -- 0, 1, 2... 数字を使えるようにする

-- 2. 整数, 演算の定義
data ℤ : Set where
  +pos : ℕ → ℤ  -- +0, +1, +2, +3 ...　正の数を定義。0含める。
  -[1+_] : ℕ → ℤ  -- -1, -2, -3 ... 負の数を定義。-[1+ n ] で「-(n + 1)」を表す）

-- 整数の定義　確認 -1 ～ +2
+0 : ℤ
+0 = +pos zero
+1 : ℤ
+1 = +pos (suc zero)
+2 = +pos (suc 1)
-[1] : ℤ
-[1] = -[1+ zero ]

-- 符号反転の定義
negate : ℤ → ℤ
negate (+pos zero)    = +pos zero
negate (+pos (suc n)) = -[1+ n ]
negate (-[1+ n ])     = +pos (suc n)

-- 整数に自然数を1足す
succℤ : ℤ → ℤ
succℤ (+pos n)       = +pos (suc n)
succℤ (-[1+ zero ])  = +0
succℤ (-[1+ (suc n)]) = -[1+ n ]

-- 整数に自然数を1引く
predℤ : ℤ → ℤ
predℤ (+pos zero)    = -[1+ zero ]
predℤ (+pos (suc n)) = +pos n
predℤ (-[1+ n ])     = -[1+ suc n ]

-- 整数 + 自然数の定義
_ℤ+ℕ_ : ℤ → ℕ → ℤ
z ℤ+ℕ zero  = z
z ℤ+ℕ suc n = succℤ (z ℤ+ℕ n)

-- 整数 - 自然数の定義
_ℤ-ℕ_ : ℤ → ℕ → ℤ
z ℤ-ℕ zero  = z
z ℤ-ℕ suc n = predℤ (z ℤ-ℕ n)

-- 整数 + 整数の定義
_+ℤ_ : ℤ → ℤ → ℤ
z1 +ℤ +pos n2   = z1 ℤ+ℕ n2
z1 +ℤ -[1+ n2 ] = z1 ℤ-ℕ suc n2

-- 3. 交換則の証明
-- 自然数の足し算の交換則を証明
-- 補題1: 右辺が zero の場合の証明 (n + zero ≡ n)
+-zero : (n : ℕ) → n + zero ≡ n
+-zero zero = refl
+-zero (suc n) = cong suc (+-zero n)

-- 補題2: 右辺が suc の場合の証明 (n + suc m ≡ suc (n + m))
+-suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

-- 自然数の足し算の結合則を証明仕上げ
+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero b = sym (+-zero b)
+-comm (suc a) b = 
  begin
    suc (a + b)
  ≡⟨ cong suc (+-comm a b) ⟩
    suc (b + a)
  ≡⟨ sym (+-suc b a) ⟩
    b + suc a
  ∎

-- 自然数の掛け算の交換則を証明
-- 自然数の足し算の結合則
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

-- 補題3: 乗算の右辺が zero の場合の証明 (n * zero ≡ zero)
*-zero : (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) = *-zero n

-- 補題4: 乗算の右辺が suc の場合の証明 (n * suc m ≡ n + (n * m))
*-suc : (n m : ℕ) → n * suc m ≡ n + (n * m)
*-suc zero m = refl
*-suc (suc n) m =
  begin
    suc (m + (n * suc m))
  ≡⟨ cong (λ x → suc (m + x)) (*-suc n m) ⟩
    suc (m + (n + (n * m)))
  ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
    suc ((m + n) + (n * m))
  ≡⟨ cong (λ x → suc (x + (n * m))) (+-comm m n) ⟩
    suc ((n + m) + (n * m))
  ≡⟨ cong suc (+-assoc n m (n * m)) ⟩
    suc (n + (m + (n * m)))
  ∎

-- 自然数のかけ算の交換則を証明仕上げ
*-comm : (a b : ℕ) → a * b ≡ b * a
*-comm zero b = sym (*-zero b)
*-comm (suc a) b =
  begin
    b + (a * b)
  ≡⟨ cong (λ x → b + x) (*-comm a b) ⟩
    b + (b * a)
  ≡⟨ sym (*-suc b a) ⟩
    b * suc a
  ∎

-- ---------------------------------------------------------------------------
-- B. 物理量の定義
-- ---------------------------------------------------------------------------
-- 量の値は、数値と参照基準（単位）の組み合わせである。
-- JCGM 200:2012, International Vocabulary of Metrology – 
-- Basic and General Concepts and Associated Terms (VIM) 3rd edition, 1.1, 1.19, 1.20.

-- 物理単位の次元（今回はMass, Length, Time に限定。それぞれの指数を保持するレコード）
record Dimension : Set where
  constructor dim
  field
    mass   : ℤ
    length : ℤ
    time   : ℤ

-- 物理単位の乗算を定義
_⊗_ : Dimension → Dimension → Dimension
dim m1 l1 t1 ⊗ dim m2 l2 t2 = dim (m1 +ℤ m2) (l1 +ℤ l2) (t1 +ℤ t2)

-- SI基本単位の次元を定義
Dim:Mass : Dimension
Dim:Mass = dim +1 +0 +0

Dim:Length : Dimension
Dim:Length = dim +0 +1 +0

Dim:Time : Dimension
Dim:Time = dim +0 +0 +1

-- SI組立単位の次元を定義
Dim:Velocity : Dimension
Dim:Velocity = dim +0 +1 -[1]

Dim:Momentum : Dimension
Dim:Momentum = dim +1 +1 -[1]

Dim:Energy : Dimension
Dim:Energy = dim +1 +2 -[1+ 1 ]

-- 物理量（物理単位と大きさを持つ型）の定義
data Quantity : Dimension → Set where
  qu : (d : Dimension) → ℕ → Quantity d

-- 物理量を定義
-- 質量 2,5 (kg)
2kg : Quantity Dim:Mass
2kg = qu Dim:Mass 2
5kg : Quantity Dim:Mass
5kg = qu Dim:Mass 5

-- 速度 5,2 (m/s)
5m/s : Quantity Dim:Velocity
5m/s = qu Dim:Velocity 5
2m/s : Quantity Dim:Velocity
2m/s = qu Dim:Velocity 2

-- ---------------------------------------------------------------------------
-- C. 物理量の積
-- ---------------------------------------------------------------------------
-- 2つの物理量の掛け算
-- 物理単位の次元計算と、大きさとなる値を算出
_×_ : {d1 d2 : Dimension} → Quantity d1 → Quantity d2 → Quantity (d1 ⊗ d2)
qu d1 v1 × qu d2 v2 = qu (d1 ⊗ d2) (v1 * v2)

-- 1. 運動量を求める掛け算1 質量 x 速度 (p = m * v)
momentum-m*v : (m : Quantity Dim:Mass) → (v : Quantity Dim:Velocity) → Quantity Dim:Momentum
momentum-m*v m v = m × v

-- 2. 運動量を求める掛け算2 速度 x 質量 (p = v * m)
momentum-v*m : (v : Quantity Dim:Velocity) → (m : Quantity Dim:Mass) → Quantity Dim:Momentum
momentum-v*m v m = v × m

-- ---------------------------------------------------------------------------
-- D1. 運動量の算出にまつわる証明
-- ---------------------------------------------------------------------------
-- 【証明】運動量の単位は、入力する物理量である質量、速度の順番とは無関係
-- 運動量の単位の次元が、入力する物理量の次元を交換しても成り立つ事で証明。
dim-comm : Dim:Mass ⊗ Dim:Velocity ≡ Dim:Velocity ⊗ Dim:Mass
dim-comm = refl

-- 運動量を求める掛け算の交換則の証明。
-- 【確認】Case1 : 単位ごと交換　具体的な物理量を代入して証明
momentum-mv : 2kg × 5m/s ≡ 5m/s × 2kg
momentum-mv = refl

-- 【証明】Case1 : 運動量を求めるかけ算において、かける物理量の順番を交換しても、常に等しい
-- 物理量の積（次元、数値の演算）の性質から証明。
momentum-mv=vm : (m : Quantity Dim:Mass) → (v : Quantity Dim:Velocity) → (m × v) ≡ (v × m)
momentum-mv=vm (qu .Dim:Mass m) (qu .Dim:Velocity v) = cong (qu Dim:Momentum) (*-comm m v)
-- 質量 x 速度 でも、 速度 x 質量 でも、異なる式とは言えない事を証明した。
-- 2式は、シンタックスとして質量, 速度と、速度, 質量の順が異なるが
-- セマンティクス(運動量を求める事)は同一であることを示している。

-- 【確認】Case 2 : 単位を固定して、数値だけを交換　具体的な物理量を代入して証明
momentum-ab : 2kg × 5m/s ≡ 5kg × 2m/s
momentum-ab = refl

-- 【証明】Case2 : 運動量を求めるかけ算において、数値だけを交換しても、常に等しい
--  物理量の大きさの計算において、数値のかけ算の交換則から証明。
momentum-ab=ba : (a b : ℕ) → (qu Dim:Mass a) × (qu Dim:Velocity b) ≡ (qu Dim:Mass b) × (qu Dim:Velocity a)
momentum-ab=ba a b =
  begin
    (qu Dim:Mass a) × (qu Dim:Velocity b)
  ≡⟨ refl ⟩ -- 定義より qu Dim:Momentum (a * b) になる
    qu Dim:Momentum (a * b)
  ≡⟨ cong (qu Dim:Momentum) (*-comm a b) ⟩ -- 自然数の掛け算を交換
    qu Dim:Momentum (b * a)
  ≡⟨ refl ⟩ -- 上記は 定義で以下に置き換えられる。
    (qu Dim:Mass b) × (qu Dim:Velocity a)
  ∎
-- かける単位の順番を固定して、数値だけを入れ替えても、求まる運動量が変わらない事を証明した。

-- 次に、Case 2の両辺で、異なる物理状態の物体を扱っていることを手掛かりに調査する。
-- ---------------------------------------------------------------------------
-- D2. 運動量の算出における交換に伴う、物理状態の検証
-- ---------------------------------------------------------------------------

-- 両辺に入力されている物理量（質量、速度）が異なっている事の証明。
kgNEq : ¬ (2kg ≡ 5kg) -- 成り立たない事を
kgNEq ()  -- 証明済み
m/sNEq : ¬ (5m/s ≡ 2m/s) -- 成り立たない事を
m/sNEq () -- 証明済み

-- 物体が持つ速度、質量には、加速、増量の過程情報を持たない事を示す。
-- 物体を速度と質量を持つ型として定義
record Obj : Set where
  constructor q
  field
    m : Quantity Dim:Mass
    v : Quantity Dim:Velocity

-- 静止状態、質量ナシの状態を定義
-- 大きさ0の物理量を定義
0kg : Quantity Dim:Mass
0kg = qu Dim:Mass 0
0m/s : Quantity Dim:Velocity
0m/s = qu Dim:Velocity 0

objS : Obj
objS = q 0kg 0m/s

-- 物体に物理量を変化させる関数を定義
-- 加速操作
AccelateObj : (obj : Obj) → ℕ → Obj
AccelateObj obj a = q (Obj.m obj) (qu Dim:Velocity a)

-- 増量操作
WeightObj : (obj : Obj) → ℕ → Obj
WeightObj obj a = q (qu Dim:Mass a) (Obj.v obj)

-- 2kgの静止物体を 5m/sまで加速した物体を定義
Obj2kg : Obj
Obj2kg = q 2kg 0m/s
Obj2kg-5m/s : Obj
Obj2kg-5m/s = AccelateObj Obj2kg 5

-- 5m/sの速度で移動している質量0の物体に2kgの質量を追加した物体を定義
Obj5m/s : Obj
Obj5m/s = q 0kg 5m/s
Obj5m/s-2kg : Obj
Obj5m/s-2kg = WeightObj Obj5m/s 2

-- 【確認】2つの物体が、異なる過程を経ても、同じ物理量を持つケース
eqObj : Obj2kg-5m/s ≡ Obj5m/s-2kg
eqObj = refl

-- 異なるプロセスを経た物体が、異なる運動量を持ち得るかを確認した。

-- ある物理状態の物体を与えると、運動量を求める関数を定義。
-- 質量×速度、速度×質量で計算する2式をobj型を受け取る関数を作成
-- momentum-m*v m v = m × v
momentum-mvObj : (obj : Obj) → Quantity Dim:Momentum
momentum-mvObj obj = momentum-m*v (Obj.m obj) (Obj.v obj)
-- momentum-v*m v m = v × m
momentum-vmObj : (obj : Obj) → Quantity Dim:Momentum
momentum-vmObj obj = momentum-v*m (Obj.v obj) (Obj.m obj)

-- 両式が等しいことは既に証明済みだが、物体を使って確認。
-- 【確認】両辺は異なるプロセスの物体だが、どの式を使って運動量を求めても、同じ運動量を持つ
eqMomentum-mv : momentum-mvObj Obj2kg-5m/s ≡ momentum-mvObj Obj5m/s-2kg
eqMomentum-mv = refl
eqMomentum-vm : momentum-vmObj Obj2kg-5m/s ≡ momentum-vmObj Obj5m/s-2kg
eqMomentum-vm = refl
eqMomentum-x1 : momentum-mvObj Obj2kg-5m/s ≡ momentum-vmObj Obj5m/s-2kg
eqMomentum-x1 = refl
eqMomentum-x2 : momentum-vmObj Obj2kg-5m/s ≡ momentum-mvObj Obj5m/s-2kg
eqMomentum-x2 = refl
-- 加速、増量のプロセスによらず、運動量を求める式の種類によらず、
-- 同じ物理状態（質量、速度）を持っていれば同じ運動量が求まることを確認できた。

-- ---------------------------------------------------------------------------
-- E. 運動エネルギーに関する検証
-- ---------------------------------------------------------------------------
-- 物体から運動エネルギーの2倍を求める関数を定義
-- 割り算を省くため、運動エネルギーの2倍で評価する。
KEobj : (obj : Obj) → Quantity Dim:Energy
KEobj obj = ((Obj.m obj) × (Obj.v obj)) × (Obj.v obj)

-- 【確認】異なるプロセスを取っているが、同じ質量、速度を持つ物体のエネルギーが等しいかを確認
eqKE : KEobj Obj2kg-5m/s ≡ KEobj Obj5m/s-2kg
eqKE = refl
-- 加速、増量のプロセスは運動エネルギーには無関係であることを示せた。

-- ********************************************************************************
-- D1. D2. E. から、運動量、運動エネルギーは、質量、速度の組み合わせから決定され
-- 加速、増量プロセスは関与しない事を確認した。
-- ********************************************************************************

-- D1. Case 2から、単位を変えず数値だけ入れ替えても、運動量の交換則は成り立った。
-- 運動エネルギーで検証する。
-- 数値だけの入れ替えでは、異なる物体の状態量になるので、数値交換後の5kg, 2m/sの物体を定義する。
Obj5kg2m/s : Obj
Obj5kg2m/s = q 5kg 2m/s

-- 【確認】運動量は等しい
-- momentum-ab : 2kg × 5m/s ≡ 5kg × 2m/s
eqM : momentum-mvObj Obj5kg2m/s ≡ momentum-mvObj Obj5m/s-2kg
eqM = refl
-- 【確認】物理量（質量、速度）が異なる
not-eqObj : ¬ (Obj5kg2m/s ≡ Obj5m/s-2kg)
not-eqObj ()

-- 【確認】物理量（質量、速度）が異なると、運動エネルギーが異なる
not-eqKE : ¬ (KEobj Obj5kg2m/s ≡ KEobj Obj5m/s-2kg)
not-eqKE ()

-- 【念押しで再確認】
-- 加速、増量プロセスが異なっても、物理状態（質量、速度）が等しい異なる物体は、
-- 運動エネルギーは等しい
not-eqKE2 : KEobj Obj2kg-5m/s ≡ KEobj Obj5m/s-2kg
not-eqKE2 = refl

-- 【確認】数値だけ入れ替えたかけ順で運動量を求めるとき、扱っている物体の物理状態の対応を確認
X1 : (a b : ℕ) → (qu Dim:Mass a) × (qu Dim:Velocity b) ≡ (momentum-mvObj (q (qu Dim:Mass a) (qu Dim:Velocity b)))
X1 a b = refl
X2 : (a b : ℕ) → (qu Dim:Mass b) × (qu Dim:Velocity a) ≡ (momentum-mvObj (q (qu Dim:Mass b) (qu Dim:Velocity a)))
X2 a b = refl

-- 【証明】上記条件の2物体の物理状態が同じとは限らないことを示す
not-eqObjX12 : ¬ ((a b : ℕ) → (q (qu Dim:Mass a) (qu Dim:Velocity b)) ≡ (q (qu Dim:Mass b) (qu Dim:Velocity a)))
-- 反例を示して証明
not-eqObjX12 f = Ex(f 2 5)
  where
    Ex : ¬ ((q (qu Dim:Mass 2) (qu Dim:Velocity 5)) ≡ (q (qu Dim:Mass 5) (qu Dim:Velocity 2)))
    Ex ()

-- ---------------------------------------------------------------------------
-- X. 運動量のかけ順に関する結論
-- ---------------------------------------------------------------------------
-- 運動量、運動エネルギーは、加速、増量プロセスに依存せず、質量と速度から決まる

-- 数値を入れ替えるだけでは、両辺の物理状態が変わる（証明省いたが、物理量の大きさの数値が同じ時は例外）
-- 物理状態が異なる時、運動量と運動エネルギーが同時に保存されるとは限らない。
-- 以上の性質は、運動量を求める式に何を採用しても普遍的な性質。

-- 一方、単位でラベル付けされた物理量を交換した式では、
-- 両辺で同一の物理状態が保存されていることが保証されているため、必ず運動量と運動エネルギーは等しい。
-- 
-- 運動量を求めるかけ順のSyntaxは、物理状態を定義しない。
-- 運動量を求める掛け算のSemanticsは、質量と速度の2つの組み合わせから運動量を求める事である。
-- 運動量を求める掛け算のSenseは、具体的な実装に相当するがSemanticsに物理状態変化のプロセスは含められていない。
-- 運動量を求める元となっている物理状態を示すラベルとして機能しているのは、単位である。
-- 掛け順だけで、物体の物理状態を意味づけ、解釈する事はできない。

-- 運動量のかけ順が、物理量の変化プロセスの意味を持つ、と言う説は完全に否定される。
-- ※証明するまでもなく、運動量、運動エネルギーは状態量であり、過程によらない事が知られている。
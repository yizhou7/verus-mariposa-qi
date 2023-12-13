(set-option :print-success false)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.case_split 3)
(set-option :smt.arith.solver 2)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(set-info :comment "; done setting options")
(declare-sort T@U 0)
(declare-sort T@T 0)
(declare-fun real_pow (Real Real) Real)
(declare-fun UOrdering2 (T@U T@U) Bool)
(declare-fun UOrdering3 (T@T T@U T@U) Bool)
(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-fun $generated (T@U T@U T@U) T@U)
(declare-fun $generated@@0 (T@U T@U T@U Bool) T@U)
(declare-fun type (T@U) T@T)
(declare-fun $generated@@1 (T@U) Int)
(declare-fun $generated@@2 (T@U) Bool)
(declare-fun $generated@@3 (T@T) T@T)
(declare-fun $generated@@4 () T@T)
(declare-fun $generated@@5 (T@T T@T) T@T)
(declare-fun $generated@@6 () T@T)
(declare-fun $generated@@7 (T@T) T@T)
(declare-fun $generated@@8 () T@T)
(declare-fun $generated@@9 (T@U T@U) T@U)
(declare-fun $generated@@10 (T@U T@U) T@U)
(declare-fun $generated@@11 (T@T) Int)
(declare-fun $generated@@12 () T@T)
(declare-fun $generated@@13 () T@T)
(declare-fun $generated@@14 (Bool) T@U)
(declare-fun $generated@@15 (Int) T@U)
(declare-fun $generated@@16 (Real) T@U)
(declare-fun $generated@@17 (T@U) Real)
(declare-fun $generated@@18 (T@T) T@T)
(declare-fun $generated@@19 (T@T) T@T)
(declare-fun $generated@@20 (T@U T@U T@U) T@U)
(declare-fun $generated@@21 (T@U T@U T@U) T@U)
(declare-fun $generated@@22 (T@T T@T) T@T)
(declare-fun $generated@@23 (T@T) T@T)
(declare-fun $generated@@24 (T@T) T@T)
(declare-fun $generated@@25 (T@U T@U T@U T@U) T@U)
(declare-fun $generated@@131 (Int Int) Int)
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= ($generated@@11 $generated@@8) 0) (= ($generated@@11 $generated@@12) 1)) (= ($generated@@11 $generated@@13) 2)) (forall (($generated@@26 Bool)) (! (= ($generated@@2 ($generated@@14 $generated@@26)) $generated@@26) :pattern (($generated@@14 $generated@@26))))) (forall (($generated@@27 T@U)) (! (=> (= (type $generated@@27) $generated@@8) (= ($generated@@14 ($generated@@2 $generated@@27)) $generated@@27)) :pattern (($generated@@2 $generated@@27))))) (forall (($generated@@28 Bool)) (! (= (type ($generated@@14 $generated@@28)) $generated@@8) :pattern (($generated@@14 $generated@@28))))) (forall (($generated@@29 Int)) (! (= ($generated@@1 ($generated@@15 $generated@@29)) $generated@@29) :pattern (($generated@@15 $generated@@29))))) (forall (($generated@@30 T@U)) (! (=> (= (type $generated@@30) $generated@@12) (= ($generated@@15 ($generated@@1 $generated@@30)) $generated@@30)) :pattern (($generated@@1 $generated@@30))))) (forall (($generated@@31 Int)) (! (= (type ($generated@@15 $generated@@31)) $generated@@12) :pattern (($generated@@15 $generated@@31))))) (forall (($generated@@32 Real)) (! (= ($generated@@17 ($generated@@16 $generated@@32)) $generated@@32) :pattern (($generated@@16 $generated@@32))))) (forall (($generated@@33 T@U)) (! (=> (= (type $generated@@33) $generated@@13) (= ($generated@@16 ($generated@@17 $generated@@33)) $generated@@33)) :pattern (($generated@@17 $generated@@33))))) (forall (($generated@@34 Real)) (! (= (type ($generated@@16 $generated@@34)) $generated@@13) :pattern (($generated@@16 $generated@@34))))) (forall (($generated@@35 T@T) ($generated@@36 T@T)) (= ($generated@@11 ($generated@@5 $generated@@35 $generated@@36)) 3))) (forall (($generated@@37 T@T) ($generated@@38 T@T)) (! (= ($generated@@18 ($generated@@5 $generated@@37 $generated@@38)) $generated@@37) :pattern (($generated@@5 $generated@@37 $generated@@38))))) (forall (($generated@@39 T@T) ($generated@@40 T@T)) (! (= ($generated@@19 ($generated@@5 $generated@@39 $generated@@40)) $generated@@40) :pattern (($generated@@5 $generated@@39 $generated@@40))))) (forall (($generated@@41 T@U) ($generated@@42 T@U)) (! (let (($generated@@43 ($generated@@19 (type $generated@@41)))) (= (type ($generated@@10 $generated@@41 $generated@@42)) $generated@@43)) :pattern (($generated@@10 $generated@@41 $generated@@42))))) (forall (($generated@@44 T@U) ($generated@@45 T@U) ($generated@@46 T@U)) (! (let (($generated@@47 (type $generated@@46))) (let (($generated@@48 (type $generated@@45))) (= (type ($generated@@20 $generated@@44 $generated@@45 $generated@@46)) ($generated@@5 $generated@@48 $generated@@47)))) :pattern (($generated@@20 $generated@@44 $generated@@45 $generated@@46))))) (forall (($generated@@49 T@U) ($generated@@50 T@U) ($generated@@51 T@U)) (! (let (($generated@@52 ($generated@@19 (type $generated@@49)))) (=> (= (type $generated@@51) $generated@@52) (= ($generated@@10 ($generated@@20 $generated@@49 $generated@@50 $generated@@51) $generated@@50) $generated@@51))) :weight 0))) (and (forall (($generated@@53 T@U) ($generated@@54 T@U) ($generated@@55 T@U) ($generated@@56 T@U)) (! (or (= $generated@@55 $generated@@56) (= ($generated@@10 ($generated@@20 $generated@@54 $generated@@55 $generated@@53) $generated@@56) ($generated@@10 $generated@@54 $generated@@56))) :weight 0)) (forall (($generated@@57 T@U) ($generated@@58 T@U) ($generated@@59 T@U) ($generated@@60 T@U)) (! (or true (= ($generated@@10 ($generated@@20 $generated@@58 $generated@@59 $generated@@57) $generated@@60) ($generated@@10 $generated@@58 $generated@@60))) :weight 0)))) (forall (($generated@@61 T@T)) (= ($generated@@11 ($generated@@7 $generated@@61)) 4))) (forall (($generated@@62 T@T)) (! (= ($generated@@3 ($generated@@7 $generated@@62)) $generated@@62) :pattern (($generated@@7 $generated@@62))))) (forall (($generated@@63 T@U) ($generated@@64 T@U)) (! (let (($generated@@65 ($generated@@3 (type $generated@@64)))) (= (type ($generated@@9 $generated@@63 $generated@@64)) $generated@@65)) :pattern (($generated@@9 $generated@@63 $generated@@64))))) (= ($generated@@11 $generated@@6) 5)) (forall (($generated@@66 T@U) ($generated@@67 T@U) ($generated@@68 T@U)) (! (= (type ($generated@@21 $generated@@66 $generated@@67 $generated@@68)) $generated@@6) :pattern (($generated@@21 $generated@@66 $generated@@67 $generated@@68))))) (forall (($generated@@69 T@U) ($generated@@70 T@U) ($generated@@71 T@U)) (! (let (($generated@@72 ($generated@@3 (type $generated@@70)))) (=> (= (type $generated@@71) $generated@@72) (= ($generated@@9 ($generated@@21 $generated@@69 $generated@@70 $generated@@71) $generated@@70) $generated@@71))) :weight 0))) (and (forall (($generated@@73 T@U) ($generated@@74 T@U) ($generated@@75 T@U) ($generated@@76 T@U)) (! (or (= $generated@@75 $generated@@76) (= ($generated@@9 ($generated@@21 $generated@@74 $generated@@75 $generated@@73) $generated@@76) ($generated@@9 $generated@@74 $generated@@76))) :weight 0)) (forall (($generated@@77 T@U) ($generated@@78 T@U) ($generated@@79 T@U) ($generated@@80 T@U)) (! (or true (= ($generated@@9 ($generated@@21 $generated@@78 $generated@@79 $generated@@77) $generated@@80) ($generated@@9 $generated@@78 $generated@@80))) :weight 0)))) (= ($generated@@11 $generated@@4) 6)) (forall (($generated@@81 T@T) ($generated@@82 T@T)) (= ($generated@@11 ($generated@@22 $generated@@81 $generated@@82)) 7))) (forall (($generated@@83 T@T) ($generated@@84 T@T)) (! (= ($generated@@23 ($generated@@22 $generated@@83 $generated@@84)) $generated@@83) :pattern (($generated@@22 $generated@@83 $generated@@84))))) (forall (($generated@@85 T@T) ($generated@@86 T@T)) (! (= ($generated@@24 ($generated@@22 $generated@@85 $generated@@86)) $generated@@86) :pattern (($generated@@22 $generated@@85 $generated@@86))))) (forall (($generated@@87 T@U) ($generated@@88 T@U) ($generated@@89 T@U)) (! (let (($generated@@90 ($generated@@24 (type $generated@@87)))) (= (type ($generated $generated@@87 $generated@@88 $generated@@89)) $generated@@90)) :pattern (($generated $generated@@87 $generated@@88 $generated@@89))))) (forall (($generated@@91 T@U) ($generated@@92 T@U) ($generated@@93 T@U) ($generated@@94 T@U)) (! (let (($generated@@95 (type $generated@@94))) (let (($generated@@96 (type $generated@@92))) (= (type ($generated@@25 $generated@@91 $generated@@92 $generated@@93 $generated@@94)) ($generated@@22 $generated@@96 $generated@@95)))) :pattern (($generated@@25 $generated@@91 $generated@@92 $generated@@93 $generated@@94))))) (forall (($generated@@97 T@U) ($generated@@98 T@U) ($generated@@99 T@U) ($generated@@100 T@U)) (! (let (($generated@@101 ($generated@@24 (type $generated@@97)))) (=> (= (type $generated@@100) $generated@@101) (= ($generated ($generated@@25 $generated@@97 $generated@@98 $generated@@99 $generated@@100) $generated@@98 $generated@@99) $generated@@100))) :weight 0))) (and (and (forall (($generated@@102 T@U) ($generated@@103 T@U) ($generated@@104 T@U) ($generated@@105 T@U) ($generated@@106 T@U) ($generated@@107 T@U)) (! (or (= $generated@@104 $generated@@106) (= ($generated ($generated@@25 $generated@@103 $generated@@104 $generated@@105 $generated@@102) $generated@@106 $generated@@107) ($generated $generated@@103 $generated@@106 $generated@@107))) :weight 0)) (forall (($generated@@108 T@U) ($generated@@109 T@U) ($generated@@110 T@U) ($generated@@111 T@U) ($generated@@112 T@U) ($generated@@113 T@U)) (! (or (= $generated@@111 $generated@@113) (= ($generated ($generated@@25 $generated@@109 $generated@@110 $generated@@111 $generated@@108) $generated@@112 $generated@@113) ($generated $generated@@109 $generated@@112 $generated@@113))) :weight 0))) (forall (($generated@@114 T@U) ($generated@@115 T@U) ($generated@@116 T@U) ($generated@@117 T@U) ($generated@@118 T@U) ($generated@@119 T@U)) (! (or true (= ($generated ($generated@@25 $generated@@115 $generated@@116 $generated@@117 $generated@@114) $generated@@118 $generated@@119) ($generated $generated@@115 $generated@@118 $generated@@119))) :weight 0)))) (forall (($generated@@120 T@U) ($generated@@121 T@U) ($generated@@122 T@U) ($generated@@123 Bool)) (! (= (type ($generated@@0 $generated@@120 $generated@@121 $generated@@122 $generated@@123)) ($generated@@22 $generated@@4 $generated@@8)) :pattern (($generated@@0 $generated@@120 $generated@@121 $generated@@122 $generated@@123))))))
(assert (forall (($generated@@124 T@U) ($generated@@125 T@U) ($generated@@126 T@U) ($generated@@127 Bool) ($generated@@128 T@U) ($generated@@129 T@U)) (! (let (($generated@@130 ($generated@@3 (type $generated@@129)))) (=> (and (and (and (and (= (type $generated@@124) $generated@@4) (= (type $generated@@125) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@126) ($generated@@7 $generated@@8))) (= (type $generated@@128) $generated@@4)) (= (type $generated@@129) ($generated@@7 $generated@@130))) (= ($generated@@2 ($generated ($generated@@0 $generated@@124 $generated@@125 $generated@@126 $generated@@127) $generated@@128 $generated@@129)) (=> (and (not (= $generated@@128 $generated@@124)) ($generated@@2 ($generated@@9 ($generated@@10 $generated@@125 $generated@@128) $generated@@126))) $generated@@127)))) :pattern (($generated ($generated@@0 $generated@@124 $generated@@125 $generated@@126 $generated@@127) $generated@@128 $generated@@129)))))
(assert (forall (($generated@@132 Int) ($generated@@133 Int)) (! (= ($generated@@131 $generated@@132 $generated@@133) (* $generated@@132 $generated@@133)) :pattern (($generated@@131 $generated@@132 $generated@@133)))))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $generated@@134 () T@U)
(declare-fun $generated@@135 () T@U)
(declare-fun $generated@@136 () T@U)
(declare-fun $generated@@137 () T@U)
(declare-fun $generated@@138 () Int)
(declare-fun $generated@@139 () Int)
(declare-fun $generated@@140 () Int)
(declare-fun $generated@@141 () Int)
(declare-fun $generated@@142 () Int)
(declare-fun $generated@@143 () Int)
(declare-fun $generated@@144 (T@U) Bool)
(declare-fun $generated@@145 (T@U) Bool)
(declare-fun $generated@@146 () Int)
(assert (and (and (and (= (type $generated@@134) ($generated@@22 $generated@@4 $generated@@8)) (= (type $generated@@135) $generated@@4)) (= (type $generated@@136) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@137) ($generated@@7 $generated@@8))))
(assert (not (=> (= (ControlFlow 0 0) 3) (let (($generated@@147 (=> (and (and (= $generated@@134 ($generated@@0 $generated@@135 $generated@@136 $generated@@137 false)) (= $generated@@138 ($generated@@131 (- (- $generated@@139 ($generated@@131 $generated@@139 $generated@@140)) ($generated@@131 ($generated@@131 $generated@@139 $generated@@140) ($generated@@131 $generated@@140 $generated@@141))) (+ (+ $generated@@140 ($generated@@131 $generated@@142 $generated@@141)) (+ ($generated@@131 $generated@@139 $generated@@142) ($generated@@131 $generated@@140 $generated@@142)))))) (and (= $generated@@143 ($generated@@131 (- (- $generated@@139 ($generated@@131 $generated@@139 $generated@@140)) ($generated@@131 ($generated@@131 $generated@@140 $generated@@141) ($generated@@131 $generated@@139 $generated@@140))) (+ (+ $generated@@140 ($generated@@131 $generated@@142 $generated@@141)) (+ ($generated@@131 $generated@@139 $generated@@142) ($generated@@131 $generated@@140 $generated@@142))))) (= (ControlFlow 0 2) (- 0 1)))) (= $generated@@138 $generated@@143)))) (let (($generated@@148 (=> (and (and ($generated@@144 $generated@@136) ($generated@@145 $generated@@136)) (and (= 0 $generated@@146) (= (ControlFlow 0 3) 2))) $generated@@147))) $generated@@148)))))
(check-sat)

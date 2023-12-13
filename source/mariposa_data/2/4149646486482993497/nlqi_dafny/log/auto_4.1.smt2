(set-option :print-success false)
(set-option :auto_config false)
(set-option :type_check true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.delay_units true)
(set-option :smt.case_split 3)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
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
(declare-fun $generated@@134 (Int Int) Int)
(declare-fun $generated@@137 (Int Int) Int)
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= ($generated@@11 $generated@@8) 0) (= ($generated@@11 $generated@@12) 1)) (= ($generated@@11 $generated@@13) 2)) (forall (($generated@@26 Bool)) (! (= ($generated@@2 ($generated@@14 $generated@@26)) $generated@@26) :pattern (($generated@@14 $generated@@26))))) (forall (($generated@@27 T@U)) (! (=> (= (type $generated@@27) $generated@@8) (= ($generated@@14 ($generated@@2 $generated@@27)) $generated@@27)) :pattern (($generated@@2 $generated@@27))))) (forall (($generated@@28 Bool)) (! (= (type ($generated@@14 $generated@@28)) $generated@@8) :pattern (($generated@@14 $generated@@28))))) (forall (($generated@@29 Int)) (! (= ($generated@@1 ($generated@@15 $generated@@29)) $generated@@29) :pattern (($generated@@15 $generated@@29))))) (forall (($generated@@30 T@U)) (! (=> (= (type $generated@@30) $generated@@12) (= ($generated@@15 ($generated@@1 $generated@@30)) $generated@@30)) :pattern (($generated@@1 $generated@@30))))) (forall (($generated@@31 Int)) (! (= (type ($generated@@15 $generated@@31)) $generated@@12) :pattern (($generated@@15 $generated@@31))))) (forall (($generated@@32 Real)) (! (= ($generated@@17 ($generated@@16 $generated@@32)) $generated@@32) :pattern (($generated@@16 $generated@@32))))) (forall (($generated@@33 T@U)) (! (=> (= (type $generated@@33) $generated@@13) (= ($generated@@16 ($generated@@17 $generated@@33)) $generated@@33)) :pattern (($generated@@17 $generated@@33))))) (forall (($generated@@34 Real)) (! (= (type ($generated@@16 $generated@@34)) $generated@@13) :pattern (($generated@@16 $generated@@34))))) (forall (($generated@@35 T@T) ($generated@@36 T@T)) (= ($generated@@11 ($generated@@5 $generated@@35 $generated@@36)) 3))) (forall (($generated@@37 T@T) ($generated@@38 T@T)) (! (= ($generated@@18 ($generated@@5 $generated@@37 $generated@@38)) $generated@@37) :pattern (($generated@@5 $generated@@37 $generated@@38))))) (forall (($generated@@39 T@T) ($generated@@40 T@T)) (! (= ($generated@@19 ($generated@@5 $generated@@39 $generated@@40)) $generated@@40) :pattern (($generated@@5 $generated@@39 $generated@@40))))) (forall (($generated@@41 T@U) ($generated@@42 T@U)) (! (let (($generated@@43 ($generated@@19 (type $generated@@41)))) (= (type ($generated@@10 $generated@@41 $generated@@42)) $generated@@43)) :pattern (($generated@@10 $generated@@41 $generated@@42))))) (forall (($generated@@44 T@U) ($generated@@45 T@U) ($generated@@46 T@U)) (! (let (($generated@@47 (type $generated@@46))) (let (($generated@@48 (type $generated@@45))) (= (type ($generated@@20 $generated@@44 $generated@@45 $generated@@46)) ($generated@@5 $generated@@48 $generated@@47)))) :pattern (($generated@@20 $generated@@44 $generated@@45 $generated@@46))))) (forall (($generated@@49 T@U) ($generated@@50 T@U) ($generated@@51 T@U)) (! (let (($generated@@52 ($generated@@19 (type $generated@@49)))) (=> (= (type $generated@@51) $generated@@52) (= ($generated@@10 ($generated@@20 $generated@@49 $generated@@50 $generated@@51) $generated@@50) $generated@@51))) :weight 0))) (and (forall (($generated@@53 T@U) ($generated@@54 T@U) ($generated@@55 T@U) ($generated@@56 T@U)) (! (or (= $generated@@55 $generated@@56) (= ($generated@@10 ($generated@@20 $generated@@54 $generated@@55 $generated@@53) $generated@@56) ($generated@@10 $generated@@54 $generated@@56))) :weight 0)) (forall (($generated@@57 T@U) ($generated@@58 T@U) ($generated@@59 T@U) ($generated@@60 T@U)) (! (or true (= ($generated@@10 ($generated@@20 $generated@@58 $generated@@59 $generated@@57) $generated@@60) ($generated@@10 $generated@@58 $generated@@60))) :weight 0)))) (forall (($generated@@61 T@T)) (= ($generated@@11 ($generated@@7 $generated@@61)) 4))) (forall (($generated@@62 T@T)) (! (= ($generated@@3 ($generated@@7 $generated@@62)) $generated@@62) :pattern (($generated@@7 $generated@@62))))) (forall (($generated@@63 T@U) ($generated@@64 T@U)) (! (let (($generated@@65 ($generated@@3 (type $generated@@64)))) (= (type ($generated@@9 $generated@@63 $generated@@64)) $generated@@65)) :pattern (($generated@@9 $generated@@63 $generated@@64))))) (= ($generated@@11 $generated@@6) 5)) (forall (($generated@@66 T@U) ($generated@@67 T@U) ($generated@@68 T@U)) (! (= (type ($generated@@21 $generated@@66 $generated@@67 $generated@@68)) $generated@@6) :pattern (($generated@@21 $generated@@66 $generated@@67 $generated@@68))))) (forall (($generated@@69 T@U) ($generated@@70 T@U) ($generated@@71 T@U)) (! (let (($generated@@72 ($generated@@3 (type $generated@@70)))) (=> (= (type $generated@@71) $generated@@72) (= ($generated@@9 ($generated@@21 $generated@@69 $generated@@70 $generated@@71) $generated@@70) $generated@@71))) :weight 0))) (and (forall (($generated@@73 T@U) ($generated@@74 T@U) ($generated@@75 T@U) ($generated@@76 T@U)) (! (or (= $generated@@75 $generated@@76) (= ($generated@@9 ($generated@@21 $generated@@74 $generated@@75 $generated@@73) $generated@@76) ($generated@@9 $generated@@74 $generated@@76))) :weight 0)) (forall (($generated@@77 T@U) ($generated@@78 T@U) ($generated@@79 T@U) ($generated@@80 T@U)) (! (or true (= ($generated@@9 ($generated@@21 $generated@@78 $generated@@79 $generated@@77) $generated@@80) ($generated@@9 $generated@@78 $generated@@80))) :weight 0)))) (= ($generated@@11 $generated@@4) 6)) (forall (($generated@@81 T@T) ($generated@@82 T@T)) (= ($generated@@11 ($generated@@22 $generated@@81 $generated@@82)) 7))) (forall (($generated@@83 T@T) ($generated@@84 T@T)) (! (= ($generated@@23 ($generated@@22 $generated@@83 $generated@@84)) $generated@@83) :pattern (($generated@@22 $generated@@83 $generated@@84))))) (forall (($generated@@85 T@T) ($generated@@86 T@T)) (! (= ($generated@@24 ($generated@@22 $generated@@85 $generated@@86)) $generated@@86) :pattern (($generated@@22 $generated@@85 $generated@@86))))) (forall (($generated@@87 T@U) ($generated@@88 T@U) ($generated@@89 T@U)) (! (let (($generated@@90 ($generated@@24 (type $generated@@87)))) (= (type ($generated $generated@@87 $generated@@88 $generated@@89)) $generated@@90)) :pattern (($generated $generated@@87 $generated@@88 $generated@@89))))) (forall (($generated@@91 T@U) ($generated@@92 T@U) ($generated@@93 T@U) ($generated@@94 T@U)) (! (let (($generated@@95 (type $generated@@94))) (let (($generated@@96 (type $generated@@92))) (= (type ($generated@@25 $generated@@91 $generated@@92 $generated@@93 $generated@@94)) ($generated@@22 $generated@@96 $generated@@95)))) :pattern (($generated@@25 $generated@@91 $generated@@92 $generated@@93 $generated@@94))))) (forall (($generated@@97 T@U) ($generated@@98 T@U) ($generated@@99 T@U) ($generated@@100 T@U)) (! (let (($generated@@101 ($generated@@24 (type $generated@@97)))) (=> (= (type $generated@@100) $generated@@101) (= ($generated ($generated@@25 $generated@@97 $generated@@98 $generated@@99 $generated@@100) $generated@@98 $generated@@99) $generated@@100))) :weight 0))) (and (and (forall (($generated@@102 T@U) ($generated@@103 T@U) ($generated@@104 T@U) ($generated@@105 T@U) ($generated@@106 T@U) ($generated@@107 T@U)) (! (or (= $generated@@104 $generated@@106) (= ($generated ($generated@@25 $generated@@103 $generated@@104 $generated@@105 $generated@@102) $generated@@106 $generated@@107) ($generated $generated@@103 $generated@@106 $generated@@107))) :weight 0)) (forall (($generated@@108 T@U) ($generated@@109 T@U) ($generated@@110 T@U) ($generated@@111 T@U) ($generated@@112 T@U) ($generated@@113 T@U)) (! (or (= $generated@@111 $generated@@113) (= ($generated ($generated@@25 $generated@@109 $generated@@110 $generated@@111 $generated@@108) $generated@@112 $generated@@113) ($generated $generated@@109 $generated@@112 $generated@@113))) :weight 0))) (forall (($generated@@114 T@U) ($generated@@115 T@U) ($generated@@116 T@U) ($generated@@117 T@U) ($generated@@118 T@U) ($generated@@119 T@U)) (! (or true (= ($generated ($generated@@25 $generated@@115 $generated@@116 $generated@@117 $generated@@114) $generated@@118 $generated@@119) ($generated $generated@@115 $generated@@118 $generated@@119))) :weight 0)))) (forall (($generated@@120 T@U) ($generated@@121 T@U) ($generated@@122 T@U) ($generated@@123 Bool)) (! (= (type ($generated@@0 $generated@@120 $generated@@121 $generated@@122 $generated@@123)) ($generated@@22 $generated@@4 $generated@@8)) :pattern (($generated@@0 $generated@@120 $generated@@121 $generated@@122 $generated@@123))))))
(assert (forall (($generated@@124 T@U) ($generated@@125 T@U) ($generated@@126 T@U) ($generated@@127 Bool) ($generated@@128 T@U) ($generated@@129 T@U)) (! (let (($generated@@130 ($generated@@3 (type $generated@@129)))) (=> (and (and (and (and (= (type $generated@@124) $generated@@4) (= (type $generated@@125) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@126) ($generated@@7 $generated@@8))) (= (type $generated@@128) $generated@@4)) (= (type $generated@@129) ($generated@@7 $generated@@130))) (= ($generated@@2 ($generated ($generated@@0 $generated@@124 $generated@@125 $generated@@126 $generated@@127) $generated@@128 $generated@@129)) (=> (and (not (= $generated@@128 $generated@@124)) ($generated@@2 ($generated@@9 ($generated@@10 $generated@@125 $generated@@128) $generated@@126))) $generated@@127)))) :pattern (($generated ($generated@@0 $generated@@124 $generated@@125 $generated@@126 $generated@@127) $generated@@128 $generated@@129)))))
(assert (forall (($generated@@132 Int) ($generated@@133 Int)) (! (= ($generated@@131 $generated@@132 $generated@@133) (- $generated@@132 $generated@@133)) :pattern (($generated@@131 $generated@@132 $generated@@133)))))
(assert (forall (($generated@@135 Int) ($generated@@136 Int)) (! (= ($generated@@134 $generated@@135 $generated@@136) (+ $generated@@135 $generated@@136)) :pattern (($generated@@134 $generated@@135 $generated@@136)))))
(assert (forall (($generated@@138 Int) ($generated@@139 Int)) (! (= ($generated@@137 $generated@@138 $generated@@139) (* $generated@@138 $generated@@139)) :pattern (($generated@@137 $generated@@138 $generated@@139)))))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $generated@@140 (T@U) Bool)
(declare-fun $generated@@141 () T@U)
(declare-fun $generated@@142 (T@U) Bool)
(declare-fun $generated@@143 () T@U)
(declare-fun $generated@@144 () Int)
(declare-fun $generated@@145 () Int)
(declare-fun $generated@@146 () Int)
(declare-fun $generated@@147 () Int)
(declare-fun $generated@@148 () Int)
(declare-fun $generated@@149 () Int)
(declare-fun $generated@@150 () Int)
(declare-fun $generated@@151 () Int)
(declare-fun $generated@@152 () T@U)
(declare-fun $generated@@153 () Int)
(declare-fun $generated@@154 () Int)
(declare-fun $generated@@155 () Int)
(declare-fun $generated@@156 () Int)
(declare-fun $generated@@157 () T@U)
(declare-fun $generated@@158 () Int)
(declare-fun $generated@@159 () Int)
(declare-fun $generated@@160 () Int)
(declare-fun $generated@@161 () T@U)
(declare-fun $generated@@162 () T@U)
(declare-fun $generated@@163 () T@U)
(declare-fun $generated@@164 () T@U)
(declare-fun $generated@@165 () Int)
(declare-fun $generated@@166 () Int)
(declare-fun $generated@@167 () Int)
(declare-fun $generated@@168 () Int)
(assert (and (and (and (and (and (and (and (= (type $generated@@161) ($generated@@5 $generated@@4 $generated@@6)) (= (type $generated@@143) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@157) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@152) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@141) ($generated@@5 $generated@@4 $generated@@6))) (= (type $generated@@162) ($generated@@22 $generated@@4 $generated@@8))) (= (type $generated@@163) $generated@@4)) (= (type $generated@@164) ($generated@@7 $generated@@8))))
(assert (not (=> (= (ControlFlow 0 0) 14) (let (($generated@@169 true)) (let (($generated@@170 (=> (and (and (and (and ($generated@@140 $generated@@141) ($generated@@142 $generated@@141)) (forall (($generated@@171 Int) ($generated@@172 Int)) (! (=> true (= ($generated@@137 $generated@@171 $generated@@172) ($generated@@137 $generated@@172 $generated@@171))) :pattern (($generated@@137 $generated@@172 $generated@@171)) :pattern (($generated@@137 $generated@@171 $generated@@172))))) (and (and (forall (($generated@@173 Int) ($generated@@174 Int) ($generated@@175 Int)) (! (=> true (= ($generated@@137 $generated@@173 ($generated@@137 $generated@@174 $generated@@175)) ($generated@@137 ($generated@@137 $generated@@173 $generated@@174) $generated@@175))) :pattern (($generated@@137 ($generated@@137 $generated@@173 $generated@@174) $generated@@175)) :pattern (($generated@@137 $generated@@173 ($generated@@137 $generated@@174 $generated@@175))))) (forall (($generated@@176 Int) ($generated@@177 Int) ($generated@@178 Int)) (! (=> true (= ($generated@@137 $generated@@176 ($generated@@137 $generated@@177 $generated@@178)) ($generated@@137 ($generated@@137 $generated@@176 $generated@@177) $generated@@178))) :pattern (($generated@@137 ($generated@@137 $generated@@176 $generated@@177) $generated@@178)) :pattern (($generated@@137 $generated@@176 ($generated@@137 $generated@@177 $generated@@178)))))) (and (forall (($generated@@179 Int) ($generated@@180 Int) ($generated@@181 Int)) (! (=> true (= ($generated@@137 $generated@@179 ($generated@@134 $generated@@180 $generated@@181)) ($generated@@134 ($generated@@137 $generated@@179 $generated@@180) ($generated@@137 $generated@@179 $generated@@181)))) :pattern (($generated@@134 ($generated@@137 $generated@@179 $generated@@180) ($generated@@137 $generated@@179 $generated@@181))) :pattern (($generated@@137 $generated@@179 ($generated@@134 $generated@@180 $generated@@181))))) (forall (($generated@@182 Int) ($generated@@183 Int) ($generated@@184 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@182 $generated@@183) $generated@@184) ($generated@@134 ($generated@@137 $generated@@182 $generated@@184) ($generated@@137 $generated@@183 $generated@@184)))) :pattern (($generated@@134 ($generated@@137 $generated@@182 $generated@@184) ($generated@@137 $generated@@183 $generated@@184))) :pattern (($generated@@137 ($generated@@134 $generated@@182 $generated@@183) $generated@@184))))))) (and (and (and (forall (($generated@@185 Int) ($generated@@186 Int) ($generated@@187 Int)) (! (=> true (= ($generated@@137 $generated@@185 ($generated@@131 $generated@@186 $generated@@187)) ($generated@@131 ($generated@@137 $generated@@185 $generated@@186) ($generated@@137 $generated@@185 $generated@@187)))) :pattern (($generated@@131 ($generated@@137 $generated@@185 $generated@@186) ($generated@@137 $generated@@185 $generated@@187))) :pattern (($generated@@137 $generated@@185 ($generated@@131 $generated@@186 $generated@@187))))) (forall (($generated@@188 Int) ($generated@@189 Int) ($generated@@190 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@188 $generated@@189) $generated@@190) ($generated@@131 ($generated@@137 $generated@@188 $generated@@190) ($generated@@137 $generated@@189 $generated@@190)))) :pattern (($generated@@131 ($generated@@137 $generated@@188 $generated@@190) ($generated@@137 $generated@@189 $generated@@190))) :pattern (($generated@@137 ($generated@@131 $generated@@188 $generated@@189) $generated@@190))))) (and (forall (($generated@@191 Int) ($generated@@192 Int) ($generated@@193 Int)) (! (=> true (= ($generated@@137 $generated@@191 ($generated@@134 $generated@@192 $generated@@193)) ($generated@@134 ($generated@@137 $generated@@191 $generated@@192) ($generated@@137 $generated@@191 $generated@@193)))) :pattern (($generated@@134 ($generated@@137 $generated@@191 $generated@@192) ($generated@@137 $generated@@191 $generated@@193))) :pattern (($generated@@137 $generated@@191 ($generated@@134 $generated@@192 $generated@@193))))) (forall (($generated@@194 Int) ($generated@@195 Int) ($generated@@196 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@194 $generated@@195) $generated@@196) ($generated@@134 ($generated@@137 $generated@@194 $generated@@196) ($generated@@137 $generated@@195 $generated@@196)))) :pattern (($generated@@134 ($generated@@137 $generated@@194 $generated@@196) ($generated@@137 $generated@@195 $generated@@196))) :pattern (($generated@@137 ($generated@@134 $generated@@194 $generated@@195) $generated@@196)))))) (and (and (forall (($generated@@197 Int) ($generated@@198 Int) ($generated@@199 Int)) (! (=> true (= ($generated@@137 $generated@@197 ($generated@@131 $generated@@198 $generated@@199)) ($generated@@131 ($generated@@137 $generated@@197 $generated@@198) ($generated@@137 $generated@@197 $generated@@199)))) :pattern (($generated@@131 ($generated@@137 $generated@@197 $generated@@198) ($generated@@137 $generated@@197 $generated@@199))) :pattern (($generated@@137 $generated@@197 ($generated@@131 $generated@@198 $generated@@199))))) (forall (($generated@@200 Int) ($generated@@201 Int) ($generated@@202 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@200 $generated@@201) $generated@@202) ($generated@@131 ($generated@@137 $generated@@200 $generated@@202) ($generated@@137 $generated@@201 $generated@@202)))) :pattern (($generated@@131 ($generated@@137 $generated@@200 $generated@@202) ($generated@@137 $generated@@201 $generated@@202))) :pattern (($generated@@137 ($generated@@131 $generated@@200 $generated@@201) $generated@@202))))) (and (= $generated@@143 $generated@@141) (= (ControlFlow 0 8) (- 0 7)))))) (= $generated@@144 $generated@@145)))) (let (($generated@@203 (=> (= $generated@@146 $generated@@147) (=> (and (= $generated@@144 ($generated@@137 ($generated@@137 $generated@@148 $generated@@149) ($generated@@131 $generated@@150 $generated@@151))) (= $generated@@145 ($generated@@131 ($generated@@137 ($generated@@137 $generated@@148 $generated@@149) $generated@@150) ($generated@@137 ($generated@@137 $generated@@148 $generated@@149) $generated@@151)))) (and (=> (= (ControlFlow 0 10) 8) $generated@@170) (=> (= (ControlFlow 0 10) 9) $generated@@169)))))) (let (($generated@@204 (=> (and (and (and (and ($generated@@140 $generated@@152) ($generated@@142 $generated@@152)) (forall (($generated@@205 Int) ($generated@@206 Int)) (! (=> true (= ($generated@@137 $generated@@205 $generated@@206) ($generated@@137 $generated@@206 $generated@@205))) :pattern (($generated@@137 $generated@@206 $generated@@205)) :pattern (($generated@@137 $generated@@205 $generated@@206))))) (and (and (forall (($generated@@207 Int) ($generated@@208 Int) ($generated@@209 Int)) (! (=> true (= ($generated@@137 $generated@@207 ($generated@@137 $generated@@208 $generated@@209)) ($generated@@137 ($generated@@137 $generated@@207 $generated@@208) $generated@@209))) :pattern (($generated@@137 ($generated@@137 $generated@@207 $generated@@208) $generated@@209)) :pattern (($generated@@137 $generated@@207 ($generated@@137 $generated@@208 $generated@@209))))) (forall (($generated@@210 Int) ($generated@@211 Int) ($generated@@212 Int)) (! (=> true (= ($generated@@137 $generated@@210 ($generated@@137 $generated@@211 $generated@@212)) ($generated@@137 ($generated@@137 $generated@@210 $generated@@211) $generated@@212))) :pattern (($generated@@137 ($generated@@137 $generated@@210 $generated@@211) $generated@@212)) :pattern (($generated@@137 $generated@@210 ($generated@@137 $generated@@211 $generated@@212)))))) (and (forall (($generated@@213 Int) ($generated@@214 Int) ($generated@@215 Int)) (! (=> true (= ($generated@@137 $generated@@213 ($generated@@134 $generated@@214 $generated@@215)) ($generated@@134 ($generated@@137 $generated@@213 $generated@@214) ($generated@@137 $generated@@213 $generated@@215)))) :pattern (($generated@@134 ($generated@@137 $generated@@213 $generated@@214) ($generated@@137 $generated@@213 $generated@@215))) :pattern (($generated@@137 $generated@@213 ($generated@@134 $generated@@214 $generated@@215))))) (forall (($generated@@216 Int) ($generated@@217 Int) ($generated@@218 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@216 $generated@@217) $generated@@218) ($generated@@134 ($generated@@137 $generated@@216 $generated@@218) ($generated@@137 $generated@@217 $generated@@218)))) :pattern (($generated@@134 ($generated@@137 $generated@@216 $generated@@218) ($generated@@137 $generated@@217 $generated@@218))) :pattern (($generated@@137 ($generated@@134 $generated@@216 $generated@@217) $generated@@218))))))) (and (and (and (forall (($generated@@219 Int) ($generated@@220 Int) ($generated@@221 Int)) (! (=> true (= ($generated@@137 $generated@@219 ($generated@@131 $generated@@220 $generated@@221)) ($generated@@131 ($generated@@137 $generated@@219 $generated@@220) ($generated@@137 $generated@@219 $generated@@221)))) :pattern (($generated@@131 ($generated@@137 $generated@@219 $generated@@220) ($generated@@137 $generated@@219 $generated@@221))) :pattern (($generated@@137 $generated@@219 ($generated@@131 $generated@@220 $generated@@221))))) (forall (($generated@@222 Int) ($generated@@223 Int) ($generated@@224 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@222 $generated@@223) $generated@@224) ($generated@@131 ($generated@@137 $generated@@222 $generated@@224) ($generated@@137 $generated@@223 $generated@@224)))) :pattern (($generated@@131 ($generated@@137 $generated@@222 $generated@@224) ($generated@@137 $generated@@223 $generated@@224))) :pattern (($generated@@137 ($generated@@131 $generated@@222 $generated@@223) $generated@@224))))) (and (forall (($generated@@225 Int) ($generated@@226 Int) ($generated@@227 Int)) (! (=> true (= ($generated@@137 $generated@@225 ($generated@@134 $generated@@226 $generated@@227)) ($generated@@134 ($generated@@137 $generated@@225 $generated@@226) ($generated@@137 $generated@@225 $generated@@227)))) :pattern (($generated@@134 ($generated@@137 $generated@@225 $generated@@226) ($generated@@137 $generated@@225 $generated@@227))) :pattern (($generated@@137 $generated@@225 ($generated@@134 $generated@@226 $generated@@227))))) (forall (($generated@@228 Int) ($generated@@229 Int) ($generated@@230 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@228 $generated@@229) $generated@@230) ($generated@@134 ($generated@@137 $generated@@228 $generated@@230) ($generated@@137 $generated@@229 $generated@@230)))) :pattern (($generated@@134 ($generated@@137 $generated@@228 $generated@@230) ($generated@@137 $generated@@229 $generated@@230))) :pattern (($generated@@137 ($generated@@134 $generated@@228 $generated@@229) $generated@@230)))))) (and (and (forall (($generated@@231 Int) ($generated@@232 Int) ($generated@@233 Int)) (! (=> true (= ($generated@@137 $generated@@231 ($generated@@131 $generated@@232 $generated@@233)) ($generated@@131 ($generated@@137 $generated@@231 $generated@@232) ($generated@@137 $generated@@231 $generated@@233)))) :pattern (($generated@@131 ($generated@@137 $generated@@231 $generated@@232) ($generated@@137 $generated@@231 $generated@@233))) :pattern (($generated@@137 $generated@@231 ($generated@@131 $generated@@232 $generated@@233))))) (forall (($generated@@234 Int) ($generated@@235 Int) ($generated@@236 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@234 $generated@@235) $generated@@236) ($generated@@131 ($generated@@137 $generated@@234 $generated@@236) ($generated@@137 $generated@@235 $generated@@236)))) :pattern (($generated@@131 ($generated@@137 $generated@@234 $generated@@236) ($generated@@137 $generated@@235 $generated@@236))) :pattern (($generated@@137 ($generated@@131 $generated@@234 $generated@@235) $generated@@236))))) (and (= $generated@@143 $generated@@152) (= (ControlFlow 0 6) (- 0 5)))))) (= $generated@@146 $generated@@147)))) (let (($generated@@237 (=> (= $generated@@153 $generated@@154) (=> (and (= $generated@@146 ($generated@@137 $generated@@155 ($generated@@137 $generated@@156 88))) (= $generated@@147 ($generated@@137 ($generated@@137 $generated@@155 $generated@@156) 88))) (and (=> (= (ControlFlow 0 11) 6) $generated@@204) (=> (= (ControlFlow 0 11) 10) $generated@@203)))))) (let (($generated@@238 (=> (and (and (and (and ($generated@@140 $generated@@157) ($generated@@142 $generated@@157)) (forall (($generated@@239 Int) ($generated@@240 Int)) (! (=> true (= ($generated@@137 $generated@@239 $generated@@240) ($generated@@137 $generated@@240 $generated@@239))) :pattern (($generated@@137 $generated@@240 $generated@@239)) :pattern (($generated@@137 $generated@@239 $generated@@240))))) (and (and (forall (($generated@@241 Int) ($generated@@242 Int) ($generated@@243 Int)) (! (=> true (= ($generated@@137 $generated@@241 ($generated@@137 $generated@@242 $generated@@243)) ($generated@@137 ($generated@@137 $generated@@241 $generated@@242) $generated@@243))) :pattern (($generated@@137 ($generated@@137 $generated@@241 $generated@@242) $generated@@243)) :pattern (($generated@@137 $generated@@241 ($generated@@137 $generated@@242 $generated@@243))))) (forall (($generated@@244 Int) ($generated@@245 Int) ($generated@@246 Int)) (! (=> true (= ($generated@@137 $generated@@244 ($generated@@137 $generated@@245 $generated@@246)) ($generated@@137 ($generated@@137 $generated@@244 $generated@@245) $generated@@246))) :pattern (($generated@@137 ($generated@@137 $generated@@244 $generated@@245) $generated@@246)) :pattern (($generated@@137 $generated@@244 ($generated@@137 $generated@@245 $generated@@246)))))) (and (forall (($generated@@247 Int) ($generated@@248 Int) ($generated@@249 Int)) (! (=> true (= ($generated@@137 $generated@@247 ($generated@@134 $generated@@248 $generated@@249)) ($generated@@134 ($generated@@137 $generated@@247 $generated@@248) ($generated@@137 $generated@@247 $generated@@249)))) :pattern (($generated@@134 ($generated@@137 $generated@@247 $generated@@248) ($generated@@137 $generated@@247 $generated@@249))) :pattern (($generated@@137 $generated@@247 ($generated@@134 $generated@@248 $generated@@249))))) (forall (($generated@@250 Int) ($generated@@251 Int) ($generated@@252 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@250 $generated@@251) $generated@@252) ($generated@@134 ($generated@@137 $generated@@250 $generated@@252) ($generated@@137 $generated@@251 $generated@@252)))) :pattern (($generated@@134 ($generated@@137 $generated@@250 $generated@@252) ($generated@@137 $generated@@251 $generated@@252))) :pattern (($generated@@137 ($generated@@134 $generated@@250 $generated@@251) $generated@@252))))))) (and (and (and (forall (($generated@@253 Int) ($generated@@254 Int) ($generated@@255 Int)) (! (=> true (= ($generated@@137 $generated@@253 ($generated@@131 $generated@@254 $generated@@255)) ($generated@@131 ($generated@@137 $generated@@253 $generated@@254) ($generated@@137 $generated@@253 $generated@@255)))) :pattern (($generated@@131 ($generated@@137 $generated@@253 $generated@@254) ($generated@@137 $generated@@253 $generated@@255))) :pattern (($generated@@137 $generated@@253 ($generated@@131 $generated@@254 $generated@@255))))) (forall (($generated@@256 Int) ($generated@@257 Int) ($generated@@258 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@256 $generated@@257) $generated@@258) ($generated@@131 ($generated@@137 $generated@@256 $generated@@258) ($generated@@137 $generated@@257 $generated@@258)))) :pattern (($generated@@131 ($generated@@137 $generated@@256 $generated@@258) ($generated@@137 $generated@@257 $generated@@258))) :pattern (($generated@@137 ($generated@@131 $generated@@256 $generated@@257) $generated@@258))))) (and (forall (($generated@@259 Int) ($generated@@260 Int) ($generated@@261 Int)) (! (=> true (= ($generated@@137 $generated@@259 ($generated@@134 $generated@@260 $generated@@261)) ($generated@@134 ($generated@@137 $generated@@259 $generated@@260) ($generated@@137 $generated@@259 $generated@@261)))) :pattern (($generated@@134 ($generated@@137 $generated@@259 $generated@@260) ($generated@@137 $generated@@259 $generated@@261))) :pattern (($generated@@137 $generated@@259 ($generated@@134 $generated@@260 $generated@@261))))) (forall (($generated@@262 Int) ($generated@@263 Int) ($generated@@264 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@262 $generated@@263) $generated@@264) ($generated@@134 ($generated@@137 $generated@@262 $generated@@264) ($generated@@137 $generated@@263 $generated@@264)))) :pattern (($generated@@134 ($generated@@137 $generated@@262 $generated@@264) ($generated@@137 $generated@@263 $generated@@264))) :pattern (($generated@@137 ($generated@@134 $generated@@262 $generated@@263) $generated@@264)))))) (and (and (forall (($generated@@265 Int) ($generated@@266 Int) ($generated@@267 Int)) (! (=> true (= ($generated@@137 $generated@@265 ($generated@@131 $generated@@266 $generated@@267)) ($generated@@131 ($generated@@137 $generated@@265 $generated@@266) ($generated@@137 $generated@@265 $generated@@267)))) :pattern (($generated@@131 ($generated@@137 $generated@@265 $generated@@266) ($generated@@137 $generated@@265 $generated@@267))) :pattern (($generated@@137 $generated@@265 ($generated@@131 $generated@@266 $generated@@267))))) (forall (($generated@@268 Int) ($generated@@269 Int) ($generated@@270 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@268 $generated@@269) $generated@@270) ($generated@@131 ($generated@@137 $generated@@268 $generated@@270) ($generated@@137 $generated@@269 $generated@@270)))) :pattern (($generated@@131 ($generated@@137 $generated@@268 $generated@@270) ($generated@@137 $generated@@269 $generated@@270))) :pattern (($generated@@137 ($generated@@131 $generated@@268 $generated@@269) $generated@@270))))) (and (= $generated@@143 $generated@@157) (= (ControlFlow 0 4) (- 0 3)))))) (= $generated@@153 $generated@@154)))) (let (($generated@@271 (=> (= $generated@@158 $generated@@159) (=> (and (= $generated@@153 ($generated@@137 ($generated@@137 $generated@@160 $generated@@160) ($generated@@137 $generated@@160 $generated@@160))) (= $generated@@154 ($generated@@137 ($generated@@137 $generated@@160 $generated@@160) ($generated@@137 $generated@@160 $generated@@160)))) (and (=> (= (ControlFlow 0 12) 4) $generated@@238) (=> (= (ControlFlow 0 12) 11) $generated@@237)))))) (let (($generated@@272 (=> (and (and (and (and ($generated@@140 $generated@@161) ($generated@@142 $generated@@161)) (forall (($generated@@273 Int) ($generated@@274 Int)) (! (=> true (= ($generated@@137 $generated@@273 $generated@@274) ($generated@@137 $generated@@274 $generated@@273))) :pattern (($generated@@137 $generated@@274 $generated@@273)) :pattern (($generated@@137 $generated@@273 $generated@@274))))) (and (and (forall (($generated@@275 Int) ($generated@@276 Int) ($generated@@277 Int)) (! (=> true (= ($generated@@137 $generated@@275 ($generated@@137 $generated@@276 $generated@@277)) ($generated@@137 ($generated@@137 $generated@@275 $generated@@276) $generated@@277))) :pattern (($generated@@137 ($generated@@137 $generated@@275 $generated@@276) $generated@@277)) :pattern (($generated@@137 $generated@@275 ($generated@@137 $generated@@276 $generated@@277))))) (forall (($generated@@278 Int) ($generated@@279 Int) ($generated@@280 Int)) (! (=> true (= ($generated@@137 $generated@@278 ($generated@@137 $generated@@279 $generated@@280)) ($generated@@137 ($generated@@137 $generated@@278 $generated@@279) $generated@@280))) :pattern (($generated@@137 ($generated@@137 $generated@@278 $generated@@279) $generated@@280)) :pattern (($generated@@137 $generated@@278 ($generated@@137 $generated@@279 $generated@@280)))))) (and (forall (($generated@@281 Int) ($generated@@282 Int) ($generated@@283 Int)) (! (=> true (= ($generated@@137 $generated@@281 ($generated@@134 $generated@@282 $generated@@283)) ($generated@@134 ($generated@@137 $generated@@281 $generated@@282) ($generated@@137 $generated@@281 $generated@@283)))) :pattern (($generated@@134 ($generated@@137 $generated@@281 $generated@@282) ($generated@@137 $generated@@281 $generated@@283))) :pattern (($generated@@137 $generated@@281 ($generated@@134 $generated@@282 $generated@@283))))) (forall (($generated@@284 Int) ($generated@@285 Int) ($generated@@286 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@284 $generated@@285) $generated@@286) ($generated@@134 ($generated@@137 $generated@@284 $generated@@286) ($generated@@137 $generated@@285 $generated@@286)))) :pattern (($generated@@134 ($generated@@137 $generated@@284 $generated@@286) ($generated@@137 $generated@@285 $generated@@286))) :pattern (($generated@@137 ($generated@@134 $generated@@284 $generated@@285) $generated@@286))))))) (and (and (and (forall (($generated@@287 Int) ($generated@@288 Int) ($generated@@289 Int)) (! (=> true (= ($generated@@137 $generated@@287 ($generated@@131 $generated@@288 $generated@@289)) ($generated@@131 ($generated@@137 $generated@@287 $generated@@288) ($generated@@137 $generated@@287 $generated@@289)))) :pattern (($generated@@131 ($generated@@137 $generated@@287 $generated@@288) ($generated@@137 $generated@@287 $generated@@289))) :pattern (($generated@@137 $generated@@287 ($generated@@131 $generated@@288 $generated@@289))))) (forall (($generated@@290 Int) ($generated@@291 Int) ($generated@@292 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@290 $generated@@291) $generated@@292) ($generated@@131 ($generated@@137 $generated@@290 $generated@@292) ($generated@@137 $generated@@291 $generated@@292)))) :pattern (($generated@@131 ($generated@@137 $generated@@290 $generated@@292) ($generated@@137 $generated@@291 $generated@@292))) :pattern (($generated@@137 ($generated@@131 $generated@@290 $generated@@291) $generated@@292))))) (and (forall (($generated@@293 Int) ($generated@@294 Int) ($generated@@295 Int)) (! (=> true (= ($generated@@137 $generated@@293 ($generated@@134 $generated@@294 $generated@@295)) ($generated@@134 ($generated@@137 $generated@@293 $generated@@294) ($generated@@137 $generated@@293 $generated@@295)))) :pattern (($generated@@134 ($generated@@137 $generated@@293 $generated@@294) ($generated@@137 $generated@@293 $generated@@295))) :pattern (($generated@@137 $generated@@293 ($generated@@134 $generated@@294 $generated@@295))))) (forall (($generated@@296 Int) ($generated@@297 Int) ($generated@@298 Int)) (! (=> true (= ($generated@@137 ($generated@@134 $generated@@296 $generated@@297) $generated@@298) ($generated@@134 ($generated@@137 $generated@@296 $generated@@298) ($generated@@137 $generated@@297 $generated@@298)))) :pattern (($generated@@134 ($generated@@137 $generated@@296 $generated@@298) ($generated@@137 $generated@@297 $generated@@298))) :pattern (($generated@@137 ($generated@@134 $generated@@296 $generated@@297) $generated@@298)))))) (and (and (forall (($generated@@299 Int) ($generated@@300 Int) ($generated@@301 Int)) (! (=> true (= ($generated@@137 $generated@@299 ($generated@@131 $generated@@300 $generated@@301)) ($generated@@131 ($generated@@137 $generated@@299 $generated@@300) ($generated@@137 $generated@@299 $generated@@301)))) :pattern (($generated@@131 ($generated@@137 $generated@@299 $generated@@300) ($generated@@137 $generated@@299 $generated@@301))) :pattern (($generated@@137 $generated@@299 ($generated@@131 $generated@@300 $generated@@301))))) (forall (($generated@@302 Int) ($generated@@303 Int) ($generated@@304 Int)) (! (=> true (= ($generated@@137 ($generated@@131 $generated@@302 $generated@@303) $generated@@304) ($generated@@131 ($generated@@137 $generated@@302 $generated@@304) ($generated@@137 $generated@@303 $generated@@304)))) :pattern (($generated@@131 ($generated@@137 $generated@@302 $generated@@304) ($generated@@137 $generated@@303 $generated@@304))) :pattern (($generated@@137 ($generated@@131 $generated@@302 $generated@@303) $generated@@304))))) (and (= $generated@@143 $generated@@161) (= (ControlFlow 0 2) (- 0 1)))))) (= $generated@@158 $generated@@159)))) (let (($generated@@305 (=> (= $generated@@162 ($generated@@0 $generated@@163 $generated@@143 $generated@@164 false)) (=> (and (= $generated@@158 ($generated@@137 ($generated@@134 $generated@@165 $generated@@166) ($generated@@134 $generated@@167 $generated@@166))) (= $generated@@159 ($generated@@137 ($generated@@134 $generated@@167 $generated@@166) ($generated@@134 $generated@@165 $generated@@166)))) (and (=> (= (ControlFlow 0 13) 2) $generated@@272) (=> (= (ControlFlow 0 13) 12) $generated@@271)))))) (let (($generated@@306 (=> (and (and ($generated@@140 $generated@@143) ($generated@@142 $generated@@143)) (and (= 0 $generated@@168) (= (ControlFlow 0 14) 13))) $generated@@305))) $generated@@306)))))))))))))
(check-sat)

; benchmark generated from python API
(set-info :status unknown)
(declare-fun x_v0q0.i () Real)
(declare-fun x_v0q0.r () Real)
(declare-fun x_v0q1.i () Real)
(declare-fun x_v0q1.r () Real)
(declare-fun x_v0q2.i () Real)
(declare-fun x_v0q2.r () Real)
(declare-fun x_v0q3.i () Real)
(declare-fun x_v0q3.r () Real)
(declare-fun x_v1q0.i () Real)
(declare-fun x_v1q0.r () Real)
(declare-fun x_v1q1.i () Real)
(declare-fun x_v1q1.r () Real)
(declare-fun x_v1q2.i () Real)
(declare-fun x_v1q2.r () Real)
(declare-fun x_v1q3.i () Real)
(declare-fun x_v1q3.r () Real)
(declare-fun f (Int) Int)
(declare-fun x_v3q0.i () Real)
(declare-fun x_v3q0.r () Real)
(declare-fun x_v3q1.i () Real)
(declare-fun x_v3q1.r () Real)
(declare-fun x_v3q2.i () Real)
(declare-fun x_v3q2.r () Real)
(declare-fun x_v3q3.i () Real)
(declare-fun x_v3q3.r () Real)
(declare-fun x_v4q0.i () Real)
(declare-fun x_v4q0.r () Real)
(declare-fun x_v4q1.i () Real)
(declare-fun x_v4q1.r () Real)
(declare-fun x_v4q2.i () Real)
(declare-fun x_v4q2.r () Real)
(declare-fun x_v4q3.i () Real)
(declare-fun x_v4q3.r () Real)
(declare-fun x_v6q0.i () Real)
(declare-fun x_v6q0.r () Real)
(declare-fun x_v6q1.i () Real)
(declare-fun x_v6q1.r () Real)
(declare-fun x_v6q2.i () Real)
(declare-fun x_v6q2.r () Real)
(declare-fun x_v6q3.i () Real)
(declare-fun x_v6q3.r () Real)
(declare-fun x_v7q0.i () Real)
(declare-fun x_v7q0.r () Real)
(declare-fun x_v7q1.i () Real)
(declare-fun x_v7q1.r () Real)
(declare-fun x_v7q2.i () Real)
(declare-fun x_v7q2.r () Real)
(declare-fun x_v7q3.i () Real)
(declare-fun x_v7q3.r () Real)
(declare-fun Pr_x_v7_3 () Real)
(declare-fun Pr_x_v7_2 () Real)
(declare-fun Pr_x_v7_1 () Real)
(declare-fun Pr_x_v7_0 () Real)
(declare-fun Pr_x_v7_sum () Real)
(declare-fun meas_cert () Bool)
(declare-fun meas_x () Int)
(declare-fun x_v0c () Int)
(declare-fun grover_fixed_ret () Int)
(declare-fun a () Int)
(assert
 (and (= x_v0q0.r 1.0) (= 0.0 x_v0q0.i)))
(assert
 (and (= x_v0q1.r 0.0) (= 0.0 x_v0q1.i)))
(assert
 (and (= x_v0q2.r 0.0) (= 0.0 x_v0q2.i)))
(assert
 (and (= x_v0q3.r 0.0) (= 0.0 x_v0q3.i)))
(assert
 (let ((?x175 (* (/ 1.0 2.0) x_v0q3.i)))
 (let ((?x174 (* (/ 1.0 2.0) x_v0q2.i)))
 (let ((?x172 (* (/ 1.0 2.0) x_v0q1.i)))
 (let ((?x171 (* (/ 1.0 2.0) x_v0q0.i)))
 (let ((?x168 (* (/ 1.0 2.0) x_v0q3.r)))
 (let ((?x167 (* (/ 1.0 2.0) x_v0q2.r)))
 (let ((?x165 (* (/ 1.0 2.0) x_v0q1.r)))
 (let ((?x164 (* (/ 1.0 2.0) x_v0q0.r)))
 (and (= x_v1q0.r (+ ?x164 ?x165 ?x167 ?x168)) (= x_v1q0.i (+ ?x171 ?x172 ?x174 ?x175))))))))))))
(assert
 (let ((?x189 (* (- (/ 1.0 2.0)) x_v0q3.i)))
 (let ((?x174 (* (/ 1.0 2.0) x_v0q2.i)))
 (let ((?x187 (* (- (/ 1.0 2.0)) x_v0q1.i)))
 (let ((?x171 (* (/ 1.0 2.0) x_v0q0.i)))
 (let ((?x184 (* (- (/ 1.0 2.0)) x_v0q3.r)))
 (let ((?x167 (* (/ 1.0 2.0) x_v0q2.r)))
 (let ((?x182 (* (- (/ 1.0 2.0)) x_v0q1.r)))
 (let ((?x164 (* (/ 1.0 2.0) x_v0q0.r)))
 (and (= x_v1q1.r (+ ?x164 ?x182 ?x167 ?x184)) (= x_v1q1.i (+ ?x171 ?x187 ?x174 ?x189))))))))))))
(assert
 (let ((?x189 (* (- (/ 1.0 2.0)) x_v0q3.i)))
 (let ((?x195 (* (- (/ 1.0 2.0)) x_v0q2.i)))
 (let ((?x172 (* (/ 1.0 2.0) x_v0q1.i)))
 (let ((?x171 (* (/ 1.0 2.0) x_v0q0.i)))
 (let ((?x184 (* (- (/ 1.0 2.0)) x_v0q3.r)))
 (let ((?x173 (* (- (/ 1.0 2.0)) x_v0q2.r)))
 (let ((?x165 (* (/ 1.0 2.0) x_v0q1.r)))
 (let ((?x164 (* (/ 1.0 2.0) x_v0q0.r)))
 (and (= x_v1q2.r (+ ?x164 ?x165 ?x173 ?x184)) (= x_v1q2.i (+ ?x171 ?x172 ?x195 ?x189))))))))))))
(assert
 (let ((?x175 (* (/ 1.0 2.0) x_v0q3.i)))
 (let ((?x195 (* (- (/ 1.0 2.0)) x_v0q2.i)))
 (let ((?x187 (* (- (/ 1.0 2.0)) x_v0q1.i)))
 (let ((?x171 (* (/ 1.0 2.0) x_v0q0.i)))
 (let ((?x168 (* (/ 1.0 2.0) x_v0q3.r)))
 (let ((?x173 (* (- (/ 1.0 2.0)) x_v0q2.r)))
 (let ((?x182 (* (- (/ 1.0 2.0)) x_v0q1.r)))
 (let ((?x164 (* (/ 1.0 2.0) x_v0q0.r)))
 (and (= x_v1q3.r (+ ?x164 ?x182 ?x173 ?x168)) (= x_v1q3.i (+ ?x171 ?x187 ?x195 ?x175))))))))))))
(assert
 (let ((?x94 (+ 1.0 (* (- 2.0) (ite (= (f 0) 1) 1.0 0.0)))))
 (and (= x_v3q0.r (* x_v1q0.r ?x94)) (= x_v3q0.i (* x_v1q0.i ?x94)))))
(assert
 (let ((?x99 (+ 1.0 (* (- 2.0) (ite (= (f 1) 1) 1.0 0.0)))))
 (and (= x_v3q1.r (* x_v1q1.r ?x99)) (= x_v3q1.i (* x_v1q1.i ?x99)))))
(assert
 (let ((?x119 (+ 1.0 (* (- 2.0) (ite (= (f 2) 1) 1.0 0.0)))))
 (and (= x_v3q2.r (* x_v1q2.r ?x119)) (= x_v3q2.i (* x_v1q2.i ?x119)))))
(assert
 (let ((?x106 (+ 1.0 (* (- 2.0) (ite (= (f 3) 1) 1.0 0.0)))))
 (and (= x_v3q3.r (* x_v1q3.r ?x106)) (= x_v3q3.i (* x_v1q3.i ?x106)))))
(assert
 (let ((?x227 (* (/ 1.0 2.0) x_v3q3.i)))
 (let ((?x250 (* (/ 1.0 2.0) x_v3q2.i)))
 (let ((?x241 (* (/ 1.0 2.0) x_v3q1.i)))
 (let ((?x248 (* (/ 1.0 2.0) x_v3q0.i)))
 (let ((?x246 (* (/ 1.0 2.0) x_v3q3.r)))
 (let ((?x234 (* (/ 1.0 2.0) x_v3q2.r)))
 (let ((?x244 (* (/ 1.0 2.0) x_v3q1.r)))
 (let ((?x230 (* (/ 1.0 2.0) x_v3q0.r)))
 (and (= x_v4q0.r (+ ?x230 ?x244 ?x234 ?x246)) (= x_v4q0.i (+ ?x248 ?x241 ?x250 ?x227))))))))))))
(assert
 (let ((?x252 (* (- (/ 1.0 2.0)) x_v3q3.i)))
 (let ((?x250 (* (/ 1.0 2.0) x_v3q2.i)))
 (let ((?x249 (* (- (/ 1.0 2.0)) x_v3q1.i)))
 (let ((?x248 (* (/ 1.0 2.0) x_v3q0.i)))
 (let ((?x247 (* (- (/ 1.0 2.0)) x_v3q3.r)))
 (let ((?x234 (* (/ 1.0 2.0) x_v3q2.r)))
 (let ((?x235 (* (- (/ 1.0 2.0)) x_v3q1.r)))
 (let ((?x230 (* (/ 1.0 2.0) x_v3q0.r)))
 (and (= x_v4q1.r (+ ?x230 ?x235 ?x234 ?x247)) (= x_v4q1.i (+ ?x248 ?x249 ?x250 ?x252))))))))))))
(assert
 (let ((?x252 (* (- (/ 1.0 2.0)) x_v3q3.i)))
 (let ((?x278 (* (- (/ 1.0 2.0)) x_v3q2.i)))
 (let ((?x241 (* (/ 1.0 2.0) x_v3q1.i)))
 (let ((?x248 (* (/ 1.0 2.0) x_v3q0.i)))
 (let ((?x247 (* (- (/ 1.0 2.0)) x_v3q3.r)))
 (let ((?x233 (* (- (/ 1.0 2.0)) x_v3q2.r)))
 (let ((?x244 (* (/ 1.0 2.0) x_v3q1.r)))
 (let ((?x230 (* (/ 1.0 2.0) x_v3q0.r)))
 (and (= x_v4q2.r (+ ?x230 ?x244 ?x233 ?x247)) (= x_v4q2.i (+ ?x248 ?x241 ?x278 ?x252))))))))))))
(assert
 (let ((?x227 (* (/ 1.0 2.0) x_v3q3.i)))
 (let ((?x278 (* (- (/ 1.0 2.0)) x_v3q2.i)))
 (let ((?x249 (* (- (/ 1.0 2.0)) x_v3q1.i)))
 (let ((?x248 (* (/ 1.0 2.0) x_v3q0.i)))
 (let ((?x246 (* (/ 1.0 2.0) x_v3q3.r)))
 (let ((?x233 (* (- (/ 1.0 2.0)) x_v3q2.r)))
 (let ((?x235 (* (- (/ 1.0 2.0)) x_v3q1.r)))
 (let ((?x230 (* (/ 1.0 2.0) x_v3q0.r)))
 (and (= x_v4q3.r (+ ?x230 ?x235 ?x233 ?x246)) (= x_v4q3.i (+ ?x248 ?x249 ?x278 ?x227))))))))))))
(assert
 (and (= x_v6q0.r x_v4q0.r) (= x_v6q0.i x_v4q0.i)))
(assert
 (and (= x_v6q1.r (* (- 1.0) x_v4q1.r)) (= x_v6q1.i (* (- 1.0) x_v4q1.i))))
(assert
 (and (= x_v6q2.r (* (- 1.0) x_v4q2.r)) (= x_v6q2.i (* (- 1.0) x_v4q2.i))))
(assert
 (and (= x_v6q3.r (* (- 1.0) x_v4q3.r)) (= x_v6q3.i (* (- 1.0) x_v4q3.i))))
(assert
 (let ((?x328 (* (/ 1.0 2.0) x_v6q3.i)))
 (let ((?x327 (* (/ 1.0 2.0) x_v6q2.i)))
 (let ((?x325 (* (/ 1.0 2.0) x_v6q1.i)))
 (let ((?x324 (* (/ 1.0 2.0) x_v6q0.i)))
 (let ((?x321 (* (/ 1.0 2.0) x_v6q3.r)))
 (let ((?x320 (* (/ 1.0 2.0) x_v6q2.r)))
 (let ((?x318 (* (/ 1.0 2.0) x_v6q1.r)))
 (let ((?x317 (* (/ 1.0 2.0) x_v6q0.r)))
 (and (= x_v7q0.r (+ ?x317 ?x318 ?x320 ?x321)) (= x_v7q0.i (+ ?x324 ?x325 ?x327 ?x328))))))))))))
(assert
 (let ((?x340 (* (- (/ 1.0 2.0)) x_v6q3.i)))
 (let ((?x327 (* (/ 1.0 2.0) x_v6q2.i)))
 (let ((?x338 (* (- (/ 1.0 2.0)) x_v6q1.i)))
 (let ((?x324 (* (/ 1.0 2.0) x_v6q0.i)))
 (let ((?x335 (* (- (/ 1.0 2.0)) x_v6q3.r)))
 (let ((?x320 (* (/ 1.0 2.0) x_v6q2.r)))
 (let ((?x333 (* (- (/ 1.0 2.0)) x_v6q1.r)))
 (let ((?x317 (* (/ 1.0 2.0) x_v6q0.r)))
 (and (= x_v7q1.r (+ ?x317 ?x333 ?x320 ?x335)) (= x_v7q1.i (+ ?x324 ?x338 ?x327 ?x340))))))))))))
(assert
 (let ((?x340 (* (- (/ 1.0 2.0)) x_v6q3.i)))
 (let ((?x346 (* (- (/ 1.0 2.0)) x_v6q2.i)))
 (let ((?x325 (* (/ 1.0 2.0) x_v6q1.i)))
 (let ((?x324 (* (/ 1.0 2.0) x_v6q0.i)))
 (let ((?x335 (* (- (/ 1.0 2.0)) x_v6q3.r)))
 (let ((?x319 (* (- (/ 1.0 2.0)) x_v6q2.r)))
 (let ((?x318 (* (/ 1.0 2.0) x_v6q1.r)))
 (let ((?x317 (* (/ 1.0 2.0) x_v6q0.r)))
 (and (= x_v7q2.r (+ ?x317 ?x318 ?x319 ?x335)) (= x_v7q2.i (+ ?x324 ?x325 ?x346 ?x340))))))))))))
(assert
 (let ((?x328 (* (/ 1.0 2.0) x_v6q3.i)))
 (let ((?x346 (* (- (/ 1.0 2.0)) x_v6q2.i)))
 (let ((?x338 (* (- (/ 1.0 2.0)) x_v6q1.i)))
 (let ((?x324 (* (/ 1.0 2.0) x_v6q0.i)))
 (let ((?x321 (* (/ 1.0 2.0) x_v6q3.r)))
 (let ((?x319 (* (- (/ 1.0 2.0)) x_v6q2.r)))
 (let ((?x333 (* (- (/ 1.0 2.0)) x_v6q1.r)))
 (let ((?x317 (* (/ 1.0 2.0) x_v6q0.r)))
 (and (= x_v7q3.r (+ ?x317 ?x333 ?x319 ?x321)) (= x_v7q3.i (+ ?x324 ?x338 ?x346 ?x328))))))))))))
(assert
 (and (and (<= Pr_x_v7_0 1.0) (>= Pr_x_v7_0 0.0)) (and (<= Pr_x_v7_1 1.0) (>= Pr_x_v7_1 0.0)) (and (<= Pr_x_v7_2 1.0) (>= Pr_x_v7_2 0.0)) (and (<= Pr_x_v7_3 1.0) (>= Pr_x_v7_3 0.0))))
(assert
 (= Pr_x_v7_sum (+ Pr_x_v7_0 Pr_x_v7_1 Pr_x_v7_2 Pr_x_v7_3)))
(assert
 (= Pr_x_v7_sum 1.0))
(assert
 (= Pr_x_v7_0 (+ (+ (^ x_v7q0.r 2.0) (^ x_v7q0.i 2.0)))))
(assert
 (= Pr_x_v7_1 (+ (+ (^ x_v7q1.r 2.0) (^ x_v7q1.i 2.0)))))
(assert
 (= Pr_x_v7_2 (+ (+ (^ x_v7q2.r 2.0) (^ x_v7q2.i 2.0)))))
(assert
 (= Pr_x_v7_3 (+ (+ (^ x_v7q3.r 2.0) (^ x_v7q3.i 2.0)))))
(assert
 (let (($x213 (= Pr_x_v7_3 1.0)))
 (let (($x221 (= Pr_x_v7_2 1.0)))
 (let (($x212 (= Pr_x_v7_1 1.0)))
 (let (($x85 (= Pr_x_v7_0 1.0)))
 (let (($x215 (or $x85 $x212 $x221 $x213)))
 (let (($x226 (= meas_cert true)))
 (and (=> $x215 $x226) (=> $x226 $x215)))))))))
(assert
 (and (=> (= Pr_x_v7_0 1.0) (= meas_x 0)) (=> (= meas_x 0) (= Pr_x_v7_0 1.0))))
(assert
 (and (=> (= Pr_x_v7_1 1.0) (= meas_x 1)) (=> (= meas_x 1) (= Pr_x_v7_1 1.0))))
(assert
 (and (=> (= Pr_x_v7_2 1.0) (= meas_x 2)) (=> (= meas_x 2) (= Pr_x_v7_2 1.0))))
(assert
 (and (=> (= Pr_x_v7_3 1.0) (= meas_x 3)) (=> (= meas_x 3) (= Pr_x_v7_3 1.0))))
(assert
 (=> (= Pr_x_v7_0 0.0) (and (distinct meas_x 0) true)))
(assert
 (=> (= Pr_x_v7_1 0.0) (and (distinct meas_x 1) true)))
(assert
 (=> (= Pr_x_v7_2 0.0) (and (distinct meas_x 2) true)))
(assert
 (=> (= Pr_x_v7_3 0.0) (and (distinct meas_x 3) true)))
(assert
 true)
(assert
 (= x_v0c meas_x))
(assert
 (= grover_fixed_ret x_v0c))
(assert
 (and (or (= (f 0) 0) (= (f 0) 1)) (or (= (f 1) 0) (= (f 1) 1)) (or (= (f 2) 0) (= (f 2) 1)) (or (= (f 3) 0) (= (f 3) 1))))
(assert
 (and (>= grover_fixed_ret 0) (< grover_fixed_ret 4)))
(assert
 (and (>= a 0) (< a 4)))
(assert
 (= (f a) 1))
(assert
 (= (+ (f 0) (f 1) (f 2) (f 3)) 1))
(assert
 (not (and (= grover_fixed_ret a) meas_cert)))
(check-sat)

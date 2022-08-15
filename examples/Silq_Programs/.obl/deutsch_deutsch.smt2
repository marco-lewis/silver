; benchmark generated from python API
(set-info :status unknown)
(declare-fun x_v0q0.i () Real)
(declare-fun x_v0q0.r () Real)
(declare-fun x_v0q1.i () Real)
(declare-fun x_v0q1.r () Real)
(declare-fun x_v1q0.i () Real)
(declare-fun x_v1q0.r () Real)
(declare-fun x_v1q1.i () Real)
(declare-fun x_v1q1.r () Real)
(declare-fun f (Int) Int)
(declare-fun x_v2q0.i () Real)
(declare-fun x_v2q0.r () Real)
(declare-fun x_v2q1.i () Real)
(declare-fun x_v2q1.r () Real)
(declare-fun x_v3q0.i () Real)
(declare-fun x_v3q0.r () Real)
(declare-fun x_v3q1.i () Real)
(declare-fun x_v3q1.r () Real)
(declare-fun Pr_x_v3_1 () Real)
(declare-fun Pr_x_v3_0 () Real)
(declare-fun Pr_x_v3_sum () Real)
(declare-fun meas_cert () Bool)
(declare-fun meas_x () Int)
(declare-fun x_v0c () Int)
(declare-fun deutsch_ret () Int)
(assert
 (and (= x_v0q0.r 1.0) (= 0.0 x_v0q0.i)))
(assert
 (and (= x_v0q1.r 0.0) (= 0.0 x_v0q1.i)))
(assert
 (let (($x93 (= x_v1q0.i (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q0.i) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q1.i)))))
 (let (($x89 (= x_v1q0.r (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q0.r) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q1.r)))))
 (and $x89 $x93))))
(assert
 (let (($x107 (= x_v1q1.i (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q0.i) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 1) x_v0q1.i)))))
 (let (($x103 (= x_v1q1.r (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v0q0.r) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 1) x_v0q1.r)))))
 (and $x103 $x107))))
(assert
 (let ((?x55 (+ 1.0 (* (- 2.0) (ite (= (f 0) 1) 1.0 0.0)))))
 (and (= x_v2q0.r (* x_v1q0.r ?x55)) (= x_v2q0.i (* x_v1q0.i ?x55)))))
(assert
 (let ((?x46 (+ 1.0 (* (- 2.0) (ite (= (f 1) 1) 1.0 0.0)))))
 (and (= x_v2q1.r (* x_v1q1.r ?x46)) (= x_v2q1.i (* x_v1q1.i ?x46)))))
(assert
 (let (($x139 (= x_v3q0.i (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q0.i) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q1.i)))))
 (let (($x135 (= x_v3q0.r (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q0.r) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q1.r)))))
 (and $x135 $x139))))
(assert
 (let (($x153 (= x_v3q1.i (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q0.i) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 1) x_v2q1.i)))))
 (let (($x149 (= x_v3q1.r (+ (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 2) x_v2q0.r) (* (root-obj (+ (* 2 (^ x 2)) (- 1)) 1) x_v2q1.r)))))
 (and $x149 $x153))))
(assert
 (and (and (<= Pr_x_v3_0 1.0) (>= Pr_x_v3_0 0.0)) (and (<= Pr_x_v3_1 1.0) (>= Pr_x_v3_1 0.0))))
(assert
 (= Pr_x_v3_sum (+ Pr_x_v3_0 Pr_x_v3_1)))
(assert
 (= Pr_x_v3_sum 1.0))
(assert
 (= Pr_x_v3_0 (+ (+ (^ x_v3q0.r 2.0) (^ x_v3q0.i 2.0)))))
(assert
 (= Pr_x_v3_1 (+ (+ (^ x_v3q1.r 2.0) (^ x_v3q1.i 2.0)))))
(assert
 (let (($x113 (= Pr_x_v3_1 1.0)))
 (let (($x117 (= Pr_x_v3_0 1.0)))
 (let (($x114 (or $x117 $x113)))
 (let (($x141 (= meas_cert true)))
 (and (=> $x114 $x141) (=> $x141 $x114)))))))
(assert
 (and (=> (= Pr_x_v3_0 1.0) (= meas_x 0)) (=> (= meas_x 0) (= Pr_x_v3_0 1.0))))
(assert
 (and (=> (= Pr_x_v3_1 1.0) (= meas_x 1)) (=> (= meas_x 1) (= Pr_x_v3_1 1.0))))
(assert
 (= x_v0c meas_x))
(assert
 (= deutsch_ret x_v0c))
(check-sat)

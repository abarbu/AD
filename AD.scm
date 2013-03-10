(module AD
 ( ;; Lifted procedures
  + AD#+ - AD#- * AD#* / AD#/ = AD#= > AD#> < AD#< >= AD#>= <= AD#<=
  +-two --two *-two /-two =-two >-two <-two >=-two <=-two
  add1 sub1 signum
  exp log sin cos ;; TODO tan
  atan            ;; TODO acos asin
  expt sqrt
  ;; TODO quotient modulo remainder numerator denominator
  abs max min ;; TODO: gcd lcm
  positive? negative? odd? even? zero?
  real? exact? inexact?
  ;; TODO: floor ceiling truncate round
  inexact->exact exact->inexact
  finite?
  ;; Other procedures
  lift-real*real->real lift-real->real
  derivative-F gradient-F
  gradient-R derivative-R
  ;; low-level, dual&tape structs
  determine-fanout! reverse-phase! write-real
  )

(import (except scheme
                + - * / = > < >= <=
                exp log sin cos ;; tan
                atan ;; acos asin
                expt sqrt
                ;; quotient modulo remainder
                ;; numerator denominator
                abs max min ;; gcd lcm
                positive? negative? odd? even? zero?
                real? exact? inexact?
                ;; floor ceiling truncate round
                inexact->exact exact->inexact
                finite?)
        (except chicken add1 sub1 signum 
                finite? )
        (prefix scheme old-)
        (prefix chicken old-)
        define-structure
        foreign
        extras)

;; These cannot all be inlined, for example / and /-two mutually recurse
;; and sqrt recurses. As of 4.8.0.2 this causes the chicken
;; inliner to loop indefinitely.
;;   + - * / = > < <= >=
;;   sqrt exp log sin cos atan
(declare (inline +-two --two *-two /-two
                 =-two >-two <-two <=-two >=-two
                 zero? positive? negative? real?
                 exact? inexact? finite? odd? even?
                 abs max min add1 sub1 signum
                 inexact->exact exact->inexact))

(use traversal srfi-1)

(define (zero? x)
 (if (number? x)
     (old-zero? x)
     (old-zero? (primal* x))))

(define-structure dual-number epsilon primal perturbation)

(define-structure tape epsilon primal factors tapes fanout sensitivity)

(define *e* 0)

(define (<_e e1 e2) (old-< e1 e2))

(define (tape e primal factors tapes) (make-tape e primal factors tapes 0 0.0))

(define (primal* p)
 (cond ((dual-number? p) (primal* (dual-number-primal p)))
       ((tape? p) (primal* (tape-primal p)))
       (else p)))

(define (+ . xs)
 (if (null? xs)
     (old-+)
     (let loop ((xs (cdr xs)) (c (car xs)))
      (if (null? xs) c (loop (cdr xs) (+-two c (car xs)))))))

(define (- x . xs)
 (if (null? xs)
     (--two 0 x)
     (let loop ((xs xs) (c x))
      (if (null? xs) c (loop (cdr xs) (--two c (car xs)))))))

(define (* . xs)
 (if (null? xs)
     (old-*)
     (let loop ((xs (cdr xs)) (c (car xs)))
      (if (null? xs) c (loop (cdr xs) (*-two c (car xs)))))))

(define (/ x . xs)
 (if (null? xs)
     (/-two 1 x)
     (let loop ((xs xs) (c x))
      (if (null? xs) c (loop (cdr xs) (/-two c (car xs)))))))

(define (= . xs) (apply old-= (map primal* xs)))

(define (< . xs) (apply old-< (map primal* xs)))

(define (> . xs) (apply old-> (map primal* xs)))

(define (<= . xs) (apply old-<= (map primal* xs)))

(define (>= . xs) (apply old->= (map primal* xs)))

(define-syntax AD#+
 (syntax-rules ()
  ((_) 0)
  ((_ a) a)
  ((_ a b) (+-two a b))
  ((_ a b c ...) (+-two a (+ b c ...)))))

(define-syntax AD#-
 (syntax-rules ()
  ((_ a) (--two 0 a))
  ((_ a b) (--two a b))
  ((_ a b c ...) (--two a (- b c ...)))))

(define-syntax AD#*
 (syntax-rules ()
  ((_) 1)
  ((_ a) a)
  ((_ a b) (*-two a b))
  ((_ a b c ...) (*-two a (* b c ...)))))

(define-syntax AD#/
 (syntax-rules ()
  ((_ a) (/-two 1 a))
  ((_ a b) (/-two a b))
  ((_ a b c ...) (/-two a (/ b c ...)))))

(define-syntax AD#=
 (syntax-rules ()
  ((_ a b) (=-two a b))
  ((_ a b c ...) (and (= b c ...) (=-two a b)))))

(define-syntax AD#<
 (syntax-rules ()
  ((_ a b) (<-two a b))
  ((_ a b c ...) (and (< b c ...) (<-two a b)))))

(define-syntax AD#>
 (syntax-rules ()
  ((_ a b) (>-two a b))
  ((_ a b c ...) (and (> b c ...) (>-two a b)))))

(define-syntax AD#<=
 (syntax-rules ()
  ((_ a b) (<=-two a b))
  ((_ a b c ...) (and (<= b c ...) (<=-two a b)))))

(define-syntax AD#>=
 (syntax-rules ()
  ((_ a b) (>=-two a b))
  ((_ a b c ...) (and (>= b c ...) (>=-two a b)))))

;;;

(define (lift-real*real->real f df/dx1 df/dx2 x1 x2)
 (let loop ((x1 x1) (x2 x2))
  (cond
   ((dual-number? x1)
    (cond
     ((dual-number? x2)
      (cond ((<_e (dual-number-epsilon x1)
                  (dual-number-epsilon x2))
             (make-dual-number (dual-number-epsilon x2)
                               (loop x1 (dual-number-primal x2))
                               (* (df/dx2 x1 (dual-number-primal x2))
                                  (dual-number-perturbation x2))))
            ((<_e (dual-number-epsilon x2)
                  (dual-number-epsilon x1))
             (make-dual-number (dual-number-epsilon x1)
                               (loop (dual-number-primal x1) x2)
                               (* (df/dx1 (dual-number-primal x1) x2)
                                  (dual-number-perturbation x1))))
            (else
             (make-dual-number (dual-number-epsilon x1)
                               (loop (dual-number-primal x1)
                                     (dual-number-primal x2))
                               (+ (* (df/dx1 (dual-number-primal x1)
                                             (dual-number-primal x2))
                                     (dual-number-perturbation x1))
                                  (* (df/dx2 (dual-number-primal x1)
                                             (dual-number-primal x2))
                                     (dual-number-perturbation x2)))))))
     ((tape? x2)
      (if (<_e (dual-number-epsilon x1) (tape-epsilon x2))
          (tape (tape-epsilon x2)
                (loop x1 (tape-primal x2))
                (list (df/dx2 x1 (tape-primal x2)))
                (list x2))
          (make-dual-number (dual-number-epsilon x1)
                            (loop (dual-number-primal x1) x2)
                            (* (df/dx1 (dual-number-primal x1) x2)
                               (dual-number-perturbation x1)))))
     (else (make-dual-number (dual-number-epsilon x1)
                             (loop (dual-number-primal x1) x2)
                             (* (df/dx1 (dual-number-primal x1) x2)
                                (dual-number-perturbation x1))))))
   ((tape? x1)
    (cond ((dual-number? x2)
           (if (<_e (tape-epsilon x1) (dual-number-epsilon x2))
               (make-dual-number (dual-number-epsilon x2)
                                 (loop x1 (dual-number-primal x2))
                                 (* (df/dx2 x1 (dual-number-primal x2))
                                    (dual-number-perturbation x2)))
               (tape (tape-epsilon x1)
                     (loop (tape-primal x1) x2)
                     (list (df/dx1 (tape-primal x1) x2))
                     (list x1))))
          ((tape? x2)
           (cond ((<_e (tape-epsilon x1) (tape-epsilon x2))
                  (tape (tape-epsilon x2)
                        (loop x1 (tape-primal x2))
                        (list (df/dx2 x1 (tape-primal x2)))
                        (list x2)))
                 ((<_e (tape-epsilon x2) (tape-epsilon x1))
                  (tape (tape-epsilon x1)
                        (loop (tape-primal x1) x2)
                        (list (df/dx1 (tape-primal x1) x2))
                        (list x1)))
                 (else (tape (tape-epsilon x1)
                             (loop (tape-primal x1) (tape-primal x2))
                             (list (df/dx1 (tape-primal x1) (tape-primal x2))
                                   (df/dx2 (tape-primal x1) (tape-primal x2)))
                             (list x1 x2)))))
          (else (tape (tape-epsilon x1)
                      (loop (tape-primal x1) x2)
                      (list (df/dx1 (tape-primal x1) x2))
                      (list x1)))))
   (else (cond ((dual-number? x2)
                (make-dual-number (dual-number-epsilon x2)
                                  (loop x1 (dual-number-primal x2))
                                  (* (df/dx2 x1 (dual-number-primal x2))
                                     (dual-number-perturbation x2))))
               ((tape? x2)
                (tape (tape-epsilon x2)
                      (loop x1 (tape-primal x2))
                      (list (df/dx2 x1 (tape-primal x2)))
                      (list x2)))
               (else (f x1 x2)))))))

(define (lift-real->real f df/dx x)
 (let loop ((x x))
  (cond ((dual-number? x)
         (make-dual-number (dual-number-epsilon x)
                           (loop (dual-number-primal x))
                           (* (df/dx (dual-number-primal x))
                              (dual-number-perturbation x))))
        ((tape? x)
         (tape (tape-epsilon x)
               (loop (tape-primal x))
               (list (df/dx (tape-primal x)))
               (list x)))
        (else (f x)))))

(define (+-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-+ x1 x2)
     (lift-real*real->real
      old-+ (lambda (x1 x2) 1.0) (lambda (x1 x2) 1.0) x1 x2)))

(define (--two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-- x1 x2)
     (lift-real*real->real
      old-- (lambda (x1 x2) 1.0) (lambda (x1 x2) -1.0) x1 x2)))

(define (*-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-* x1 x2)
     (lift-real*real->real
      old-* (lambda (x1 x2) x2) (lambda (x1 x2) x1) x1 x2)))

(define (/-two x1 x2)
 (if (and (number? x1) (number? x2))
     ;; We pay a performance penalty because chicken is broken
     (if (= x2 0.0)
         (fp/ (exact->inexact x1) (exact->inexact x2))
         (old-/ x1 x2))
     (lift-real*real->real old-/
                           (lambda (x1 x2) (/ x2))
                           (lambda (x1 x2) (- (/ x1 (* x2 x2))))
                           x1
                           x2)))

(define (sqrt x)
 (lift-real->real old-sqrt (lambda (x) (/ (* 2.0 (sqrt x)))) x))

(define (exp x) (lift-real->real old-exp (lambda (x) (exp x)) x))

(define (log x) (lift-real->real old-log (lambda (x) (/ x)) x))

(define (expt x1 x2)
 (lift-real*real->real old-expt
                       (lambda (x1 x2) (* x2 (expt x1 (- x2 1))))
                       (lambda (x1 x2) (* (log x1) (expt x1 x2)))
                       x1
                       x2))

(define (sin x) (lift-real->real old-sin (lambda (x) (cos x)) x))

(define (cos x) (lift-real->real old-cos (lambda (x) (- (sin x))) x))

(define (atan . xs)
 (cond
  ((null? xs) (apply old-atan xs))
  ((null? (cdr xs)) (atan (first xs) 1))
  ((null? (cdr (cdr xs)))
   (lift-real*real->real old-atan
                         (lambda (x1 x2) (/ x2 (+ (* x1 x1) (* x2 x2))))
                         (lambda (x1 x2) (/ (- x1) (+ (* x1 x1) (* x2 x2))))
                         (car xs)
                         (cadr xs)))
  (else (apply old-atan xs))))

(define (=-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-= x1 x2)
     (let loop ((x1 x1) (x2 x2))
      (cond ((dual-number? x1) (loop (dual-number-primal x1) x2))
            ((tape? x1) (loop (tape-primal x1) x2))
            ((dual-number? x2) (loop x1 (dual-number-primal x2)))
            ((tape? x2) (loop x1 (tape-primal x2)))
            (else (old-= x1 x2))))))

(define (<-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-< x1 x2)
     (let loop ((x1 x1) (x2 x2))
      (cond ((dual-number? x1) (loop (dual-number-primal x1) x2))
            ((tape? x1) (loop (tape-primal x1) x2))
            ((dual-number? x2) (loop x1 (dual-number-primal x2)))
            ((tape? x2) (loop x1 (tape-primal x2)))
            (else (old-< x1 x2))))))

(define (>-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-> x1 x2)
     (let loop ((x1 x1) (x2 x2))
      (cond ((dual-number? x1) (loop (dual-number-primal x1) x2))
            ((tape? x1) (loop (tape-primal x1) x2))
            ((dual-number? x2) (loop x1 (dual-number-primal x2)))
            ((tape? x2) (loop x1 (tape-primal x2)))
            (else (old-> x1 x2))))))

(define (<=-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old-<= x1 x2)
     (let loop ((x1 x1) (x2 x2))
      (cond ((dual-number? x1) (loop (dual-number-primal x1) x2))
            ((tape? x1) (loop (tape-primal x1) x2))
            ((dual-number? x2) (loop x1 (dual-number-primal x2)))
            ((tape? x2) (loop x1 (tape-primal x2)))
            (else (old-<= x1 x2))))))

(define (>=-two x1 x2)
 (if (and (number? x1) (number? x2))
     (old->= x1 x2)
     (let loop ((x1 x1) (x2 x2))
      (cond ((dual-number? x1) (loop (dual-number-primal x1) x2))
            ((tape? x1) (loop (tape-primal x1) x2))
            ((dual-number? x2) (loop x1 (dual-number-primal x2)))
            ((tape? x2) (loop x1 (tape-primal x2)))
            (else (old->= x1 x2))))))

(define-syntax simple-lift
 (syntax-rules ()
  ((_ name old-name)
   (define (name x)
    (if (number? x)
        (old-name x)
        (old-name (primal* x)))))))

(simple-lift zero? old-zero?)
(simple-lift positive? old-positive?)
(simple-lift negative? old-negative?)
(simple-lift real? old-real?)
(simple-lift exact? old-exact?)
(simple-lift inexact? old-inexact?)
(simple-lift finite? old-finite?)
(simple-lift odd? old-odd?)
(simple-lift even? old-even?)

(define (abs x) (if (< x 0) (- x) x))
(define (max a b) (if (> a b) a b))
(define (min a b) (if (< a b) a b))

(define (add1 n) (+ n 1))
(define (sub1 n) (- n 1))
(define (signum x) (if (= x 0) 0 (if (< x 0) -1 1)))

(define (inexact->exact x) 
 (if (number? x)
     (old-inexact->exact x)
     (lift-real->real old-inexact->exact (lambda (x) x) x)))
(define (exact->inexact x) 
 (if (number? x)
     (old-exact->inexact x)
     (lift-real->real old-exact->inexact (lambda (x) x) x)))

(define (derivative-F f)
 (lambda (x)
  (set! *e* (+ *e* 1))
  (let* ((y (f (make-dual-number *e* x 1.0)))
	 (y-prime (if (or (not (dual-number? y))
			  (<_e (dual-number-epsilon y) *e*))
		      0.0
		      (dual-number-perturbation y))))
   (set! *e* (- *e* 1))
   y-prime)))

(define (replace-ith-vector x i xi)
 (map-n-vector
  (lambda (j) (if (= j i) xi (vector-ref x j))) (vector-length x)))

(define (gradient-F f)
 (lambda (x)
  (map-n-vector
   (lambda (i)
    ((derivative-F (lambda (xi) (f (replace-ith-vector x i xi))))
     (vector-ref x i)))
   (vector-length x))))

(define (determine-fanout! tape)
 (set-tape-fanout! tape (+ (tape-fanout tape) 1))
 (cond ((= (tape-fanout tape) 1)
	(for-each determine-fanout! (tape-tapes tape)))))

(define (reverse-phase! sensitivity tape)
 (set-tape-sensitivity! tape (+ (tape-sensitivity tape) sensitivity))
 (set-tape-fanout! tape (- (tape-fanout tape) 1))
 (cond ((zero? (tape-fanout tape))
	(let ((sensitivity (tape-sensitivity tape)))
	 (for-each (lambda (factor tape)
		    (reverse-phase! (* sensitivity factor) tape))
		   (tape-factors tape)
		   (tape-tapes tape))))))

(define (gradient-R f)
 (lambda (x)
  (set! *e* (+ *e* 1))
  (let* ((x (map-vector (lambda (xi) (tape *e* xi '() '())) x)) (y (f x)))
   (cond ((and (tape? y) (not (<_e (tape-epsilon y) *e*)))
	  (determine-fanout! y)
	  (reverse-phase! 1.0 y)))
   (set! *e* (- *e* 1))
   (map-vector tape-sensitivity x))))

(define (derivative-R f)
 (lambda (x)
  (vector-ref ((gradient-R (lambda (x) (f (vector-ref x 0)))) (vector x)) 0)))

(define (write-real x)
 (cond ((dual-number? x) (write-real (dual-number-primal x)) x)
       ((tape? x) (write-real (tape-primal x)) x)
       (else (write x) (newline) x)))

)

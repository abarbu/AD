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
  *e* <_e tape)

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
                inexact->exact exact->inexact)
        (except chicken add1 sub1 signum 
                finite? )
        (prefix scheme old-)
        (prefix chicken old-)
        define-structure
        foreign
        extras)

#>
/* argvector chicken starts with version 8 */
#if C_BINARY_VERSION >= 8
# define ARGVECTOR_CHICKEN
#endif

#define WORDS_PER_FLONUM C_SIZEOF_FLONUM
#define AD_a_i_divide(ptr, n, x, y)      AD_2_divide(ptr, x, y)

void barf(int code, char *loc, ...)
{
  C_char *msg;
  C_word err = C_intern2(C_heaptop, C_text("\003syserror-hook"));
  int c, i;
  va_list v;

  C_dbg_hook(C_SCHEME_UNDEFINED);

  C_temporary_stack = C_temporary_stack_bottom;
  err = C_u_i_car(err);

  switch(code) {
  case C_BAD_ARGUMENT_TYPE_ERROR:
    msg = C_text("bad argument type");
    c = 1;
    break;
  default:
    fprintf(stderr, "illegal internal error code");
    exit(1);
  }
  
#ifdef ARGVECTOR_CHICKEN
  {
    C_word *av = C_alloc(c + 4);

    av[ 0 ] = err;
    /* No continuation is passed: '##sys#error-hook' may not return: */
    av[ 1 ] = C_SCHEME_UNDEFINED;
    av[ 2 ] = C_fix(code);
    if(loc != NULL)
      av[ 3 ] = C_intern2(C_heaptop, loc);
    else {
      av[ 3 ] = C_SCHEME_FALSE;
    }

    av[ 3 ] = loc == NULL ? C_SCHEME_FALSE : C_intern2(C_heaptop, loc);

    va_start(v, loc);
    for(i = 0; i < c; ++i)
      av[ i + 4 ] = va_arg(v, C_word);
    va_end(v);

    C_do_apply(c + 4, av);
  }
#else
  C_save(C_fix(code));
  
  if(loc != NULL)
    C_save(C_intern2(C_heaptop, loc));
  else {
    C_save(C_SCHEME_FALSE);
  }
  
  va_start(v, loc);
  i = c;
   while(i--)
    C_save(va_arg(v, C_word));
  va_end(v);

  /* No continuation is passed: '##sys#error-hook' may not return: */
  C_do_apply(c + 2, err, C_SCHEME_UNDEFINED); 
#endif
}

C_regparm C_word C_fcall AD_2_divide(C_word **ptr, C_word x, C_word y)
{
  if(x & C_FIXNUM_BIT) {
    if(y & C_FIXNUM_BIT) {
      double fresult = (double)C_unfix(x) / (double)C_unfix(y);
      if(isfinite(fresult)) {
        C_word iresult = C_unfix(x) / C_unfix(y);
        if((double)iresult != fresult) return C_flonum(ptr, fresult);
        else return C_fix(iresult);
      } else {
        return C_flonum(ptr, fresult);
      }
    }
    else if(!C_immediatep(y) && C_block_header(y) == C_FLONUM_TAG) {
      return C_flonum(ptr, (double)C_unfix(x) / C_flonum_magnitude(y));
    }
    else barf(C_BAD_ARGUMENT_TYPE_ERROR, "/", y);
  }
  else if(!C_immediatep(x) && C_block_header(x) == C_FLONUM_TAG) {
    if(y & C_FIXNUM_BIT) {
      return C_flonum(ptr, C_flonum_magnitude(x) / (double)C_unfix(y));
    }
    else if(!C_immediatep(y) && C_block_header(y) == C_FLONUM_TAG) {
      return C_flonum(ptr, C_flonum_magnitude(x) / C_flonum_magnitude(y));
    }
    else barf(C_BAD_ARGUMENT_TYPE_ERROR, "/", y);
  }
  else barf(C_BAD_ARGUMENT_TYPE_ERROR, "/", x);

  abort(); /* should never get here */
}
<#

(use traversal srfi-1)

;; These cannot all be inlined, for example / and /-two mutually recurse
;; and sqrt recurses. As of 4.8.0.2 this causes the chicken
;; inliner to loop indefinitely.
;;   + - * / = > < <= >=
;;   sqrt exp log sin cos atan
(declare (inline +-two --two *-two
                 ;; /-two can't be inlined because of 
                 ;; 
                 =-two >-two <-two <=-two >=-two
                 zero? positive? negative? real?
                 exact? inexact? finite? odd? even?
                 abs max min add1 sub1 signum
                 inexact->exact exact->inexact))

(define-type AD-number (or number (struct tape) (struct dual-number)))

(: +-two (AD-number AD-number -> AD-number))
(: --two (AD-number AD-number -> AD-number))
(: *-two (AD-number AD-number -> AD-number))
(: /-two (AD-number AD-number -> AD-number))
(: =-two (AD-number AD-number -> boolean))
(: >-two (AD-number AD-number -> boolean))
(: <-two (AD-number AD-number -> boolean))
(: <=-two (AD-number AD-number -> boolean))
(: >=-two (AD-number AD-number -> boolean))
(: min (AD-number AD-number -> AD-number))
(: max (AD-number AD-number -> AD-number))
(: atan (AD-number AD-number -> AD-number))
(: expt (AD-number AD-number -> AD-number))

(: abs (AD-number -> AD-number))
(: add1 (AD-number -> AD-number))
(: sub1 (AD-number -> AD-number))
(: signum (AD-number -> number))
(: inexact->exact (AD-number -> AD-number))
(: exact->inexact (AD-number -> AD-number))
(: exp (AD-number -> AD-number))
(: log (AD-number -> AD-number))
(: sin (AD-number -> AD-number))
(: cos (AD-number -> AD-number))
(: sqrt (AD-number -> AD-number))

(: zero? (AD-number -> boolean))
(: positive? (AD-number -> boolean))
(: negative? (AD-number -> boolean))
(: real? (AD-number -> boolean))
(: exact? (AD-number -> boolean))
(: inexact? (AD-number -> boolean))
(: finite? (AD-number -> boolean))
(: odd? (AD-number -> boolean))
(: even? (AD-number -> boolean))

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
     (##core#inline_allocate ("AD_a_i_divide" 4) x1 x2)
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

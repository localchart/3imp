#!/usr/local/bin/gosh

;;;; check with gauche

(use gauche.process)
(use srfi-1)  ; for partition
(use srfi-13)  ; for string->list
(use file.util)
(use gauche.parseopt)

(define (test-suite run-proc title cases)
  (define (check subtitle sexp)
    (let ((res (run-proc sexp))
          (ans (eval sexp (interaction-environment))))
      (if (equal? res ans)
          `(#t ,subtitle ,res)
        `(#f ,subtitle ,res ,ans))))

  (let ((n (length cases)))
    (print #`"1..,n")
    (let ((results (map (lambda (c i)
                          (let ((subtitle (car c))
                                (sexp (cadr c)))
                            (let ((res (check subtitle sexp)))
                              (if (car res)
                                  (print #`"ok ,subtitle # ,i")
                                (begin
                                  (print #`"not ok ,subtitle # ,i")
                                  (display "# got:      ") (write (caddr res)) (newline)
                                  (display "# expected: ") (write (cadddr res)) (newline)))
                              res)))
                        cases
                        (iota n 1))))
      (receive (oks ngs) (partition car results)
               (null? ngs)))))

;;;; test suite

(define (run-test run-proc)
  (test-suite run-proc 'CHECK-ALL
 '(
;;;; BASIC
   (number
    123)
   (quote
    'abc)
   (string
    "hello")
;   (escaped-string
;    "hello\tgood-bye")
   (if-true
    (if #t 2 3))
   (if-false
    (if #f 2 3))
   (if-no-else
    (if 1 2))
   (simple-primitive-function-application
    (+ 1 2))
   (direct-lambda-application
    ((lambda (x) x) 123))
   (indirect-lambda-application
    ((lambda (f x) (f x)) (lambda (x) (* x x)) 111))
   (call/cc
    (call/cc (lambda (cc) (cc 1234) 567)))
   (set!
     ((lambda (x) (set! x 123) x) 100))
   (free-variable
    (((lambda (x) (lambda (y) (cons x y))) 10) 20))
   (begin
     (begin (+ 10 20) 30 (* 40 50)))
   (let
       (let ((a 10) (b 20)) (list a b)))
   (let*
       (let* ((x 10) (y (* x x))) (list x y)))
   (let1
     (let1 x 111 (* x x)))
   (named-let
    (let loop ((ls '(1 2 3)) (acc 0)) (if (null? ls) acc (loop (cdr  ls) (+ acc (car ls))))))
   (letrec
    (letrec ((ev? (lambda (x) (if (eq? x 0) #t (od? (- x 1)))))
             (od? (lambda (x) (if (eq? x 0) #f (ev? (- x 1))))))
            (ev? 10)))
   (cond-t
    (cond ((eq? 1 1) 'zero) (else 'other)))
   (cond-f
    (cond ((eq? 1 0) 'zero) (else 'other)))
   (cond=>
    (cond ((null? '()) => list)))
   (cond0
    (cond ((list 123))))
   (case
    (case 'abc ((hello) 'world) ((abc) 'def) (else 'other)))
   (when
    (when 1 2 3))
   (and
    (and 1 2 3))
   (or
    (or #f 2 3))
   (define
     (begin
       (define (sq x) (* x x))
       (sq 111)))
   (cons
    (cons 1 2))
   (car
    (car '(1 . 2)))
   (cdr
    (cdr '(1 . 2)))
   (null?
    (null? '()))
   (symbol?
    (symbol? 'abc))
   (pair?
    (pair? '(1 2)))
   (is-null-pair?
    (pair? '()))
   (set-car!
     (let1 c (cons 1 2) (set-car! c 'a) c))
   (set-cdr!
     (let1 c (cons 1 2) (set-cdr! c 'd) c))
;   (map
;    (map (lambda (x) (+ x 1)) '(10 20 30 40 50)))
   (apply
    (apply + 1 2 '(3 4 5)))
;;;; INNER
   ;; 内部define
   (internal-define
    (begin
      (define hoge 123)
      (begin hoge)))
   ;; 
   (simple-direct-invocation
    ((lambda (x) (* x x)) 111))
   ;; うまく動かないケース１：f が０じゃなくなるとDIRECT-INVOKE時に親フレームがあると思われてだめになる
   (non-toplevel-direct-invocation
    (let1 a 1
      (list
       (let1 x a
         x))))
   ;; うまく動かないケース２：スタックにいくつか積んである状態だと、RETURN-DIRECT時におかしくなる
   (inner-direct-invocation
    (list 10 ((lambda (x) x) 123) 30))
   ;; 再帰的なdirect-invocation時にフリー変数列挙の順序が変わってしまい結果が異なる
   (recursive-direct-invocation
    (let ((g 'hoge))
      (let loop ()
        (begin
          loop
          g))))
   ;; rest
   (rest-parameter-with-direct-invoke
    ((lambda (a . b) (list a b)) 10 20 30))
   ;; 内部でフリー変数を使う
   (inner-free-variable
    (begin
      (define compile
        (lambda (x e s next)
          ((lambda (G203)
             (apply (lambda (test then else)
                      ((lambda (thenc elsec)
                         (list test e s))
                       next
                       next))
                    (cdr x)))
           (car x))))
      (compile '(if x 2 3) '(()) 0 '(RETURN))))

;;;; LARGE
   (amb
    (begin
      (define fail
        (lambda () (error "no solution")))
      
      (define in-range
        (lambda (a b)
          (call/cc
           (lambda (cont)
             (enumerate a b cont)))))
      
      (define enumerate
        (lambda (a b cont)
          (if (> a b)
              (fail)
            (let ((save fail))
              (set! fail
                (lambda ()
                  (set! fail save)
                  (enumerate (+ a 1) b cont)))
              (cont a)))))
      
      (let* ((x (in-range 2 9))  ;let だと式の評価順が不定なので結果が異なる
             (y (in-range 2 9))
             (z (in-range 2 9)))
        (if (= (* x x)
               (+ (* y y) (* z z)))
            (list x y z)
          (fail)))))
   
   (fib
    (begin
      (define (fib n)
        (if (< n 2)
            n
          (+ (fib (- n 1))
             (fib (- n 2)))))
      (fib 10)))

   (Y-combinator
    (((lambda (f) 
        ((lambda (proc) (f (lambda (arg) ((proc proc) arg))))
         (lambda (proc) (f (lambda (arg) ((proc proc) arg))))))
      (lambda (self)
        (lambda (ls) 
          (if (null? ls) 0 (+ 1 (self (cdr ls))))))) 
     '(a b c d e)))

   ;;; Normal fib
   (fib
    (begin
     (define zero? (lambda (x) (= x 0)))
     (define add1 (lambda (x) (+ x 1)))
     (define sub1 (lambda (x) (- x 1)))
      
      (define add
       (lambda (x y)
         (if (zero? y)
             x
           (add (add1 x) (sub1 y)))))
      
      (define fib
        (lambda (x)
          (if (zero? x)
              1
            (if (zero? (sub1 x))
                1
              (add (fib (sub1 x))
                   (fib (sub1 (sub1 x))))))))
      
      (fib 10)))
   
   ;;;; CPS fib, create many closures
   (fib-CPS
    (begin
      (define zero? (lambda (x) (= x 0)))
      (define add1 (lambda (x) (+ x 1)))
      (define sub1 (lambda (x) (- x 1)))
      
      (define addk
        (lambda (x y k)
          (if (zero? y)
              (k x)
            (addk (add1 x) (sub1 y) k))))
      
      (define fibk
        (lambda (x k)
          (if (zero? x)
              (k 1)
            (if (zero? (sub1 x))
                (k 1)
              (fibk (sub1 x)
                    (lambda (a)
                      (fibk (sub1 (sub1 x))
                            (lambda (b)
                              (addk a b k)))))))))
      
      (fibk 10 (lambda (x) x))))
   
   ;;;; use clall/cc, create many continuations
   (fib-call/cc
    (begin
      (define zero? (lambda (x) (= x 0)))
      (define add1 (lambda (x) (+ x 1)))
      (define sub1 (lambda (x) (- x 1)))
      
      (define addc
        (lambda (x y c)
          (if (zero? y)
              (c x)
            (addc (add1 x) (sub1 y) c))))
      
      (define fibc
        (lambda (x c)
          (if (zero? x)
              (c 1)
            (if (zero? (sub1 x))
                (c 1)
              (addc (call/cc
                     (lambda (c)
                       (fibc (sub1 x) c)))
                    (call/cc
                     (lambda (c)
                       (fibc (sub1 (sub1 x)) c)))
                    c)))))
      
      (fibc 10 (lambda (x) x))))
   
   ;;; use assignment.
   (fib-assignment
    (begin
      (define zero? (lambda (x) (= x 0)))
      (define add1 (lambda (x) (+ x 1)))
      (define sub1 (lambda (x) (- x 1)))
      
      (define add!
        (lambda (x y)
          ((lambda (add!)
             (set! add!
               (lambda ()
                 (if (zero? y)
                     x
                   ((lambda ()
                      (set! x (add1 x))
                      (set! y (sub1 y))
                    (add!))))))
             (add!))
           '())))
      
      (define fib!
        (lambda (x)
          (if (zero? x)
              1
            (if (zero? (sub1 x))
                1
              (add! (fib! (sub1 x))
                    (fib! (sub1 (sub1 x))))))))
      
      (fib! 10)))
   
   )))


(define (exec-3imp sexp)
  (let* ((ss (write-to-string `(write ,sexp)))
         (proc (run-process `("gosh" "3imp.scm" "-e" ,ss) :output :pipe :error :pipe)))
    (guard (exc
            (else (process-kill proc) exc))
      (if (process-wait proc #f #t)
          (read (process-output proc))
        #f))))

(define (escape-shell-string str)
  (let1 conv (map (lambda (c)
                           (case c
                             ((#\\) "\\\\")
                             ((#\") "\\\"")
                             (else (string c))))
                  (string->list str))
    (apply string-append conv)))

(define (exec-mlisp sexp)
  (let1 cmd (string-append "sh eval-mlisp.sh \"(write "
                           (escape-shell-string (write-to-string sexp))
                           ")\" >.temp")
    (let1 exit-code (sys-system cmd)
      (if (= exit-code 0)
          (car (file->sexp-list ".temp"))
        (string-append "System execute error: exit code = "
                       (number->string exit-code))))))

(define (main args)
  (let-args (cdr args)
            ((mlisp?         "m|mlisp")
             . restargs)
    (let ((proc (cond (mlisp? exec-mlisp)
                      (else exec-3imp))))
      (run-test proc))))

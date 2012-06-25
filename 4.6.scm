
(load "./util.scm")

(define compile
  (lambda (x e s next)
    (cond
     ((symbol? x)
      (compile-refer x e
                     (if (set-member? x s)
                         (list 'INDIRECT next)
                       next)))
     ((pair? x)
      (record-case x
                   (quote (obj) (list 'CONSTANT obj next))
                   (lambda (vars body)
                     (let ((free (find-free body vars))
                           (sets (find-sets body vars)))
                       (collect-free free e
                                     (list 'CLOSE
                                           (length free)
                                           (make-boxes sets vars
                                                       (compile body
                                                                (cons vars free)
                                                                (set-union
                                                                 sets
                                                                 (set-intersect s free))
                                                                (list 'RETURN (length vars))))
                                           next))))
                   (if (test then else)
                       (let ((thenc (compile then e s next))
                             (elsec (compile else e s next)))
                         (compile test e s (list 'TEST thenc elsec))))
                   (set! (var x)
                         (compile-lookup var e
                                         (lambda (n)
                                           (compile x e s (list 'ASSIGN-LOCAL n next)))
                                         (lambda (n)
                                           (compile x e s (list 'ASSIGN-FREE n next)))))
                   (call/cc (x)
                            (let ((c (list 'CONTI
                                           (list 'ARGUMENT
                                                 (compile x e s
                                                          (if (tail? next)
                                                              (list 'SHIFT
                                                                    1
                                                                    (cadr next)
                                                                    '(APPLY))
                                                            '(APPLY)))))))
                              (if (tail? next)
                                  c
                                (list 'FRAME next c))))
                   (else
                    (recur loop ((args (cdr x))
                                 (c (compile (car x) e s
                                             (if (tail? next)
                                                 (list 'SHIFT
                                                       (length (cdr x))
                                                       (cadr next)
                                                       '(APPLY))
                                               '(APPLY)))))
                           (if (null? args)
                               (if (tail? next)
                                   c
                                 (list 'FRAME next c))
                             (loop (cdr args)
                               (compile (car args)
                                        e
                                        s
                                        (list 'ARGUMENT c))))))))
     (else (list 'CONSTANT x next)))))

(define find-free
  (lambda (x b)
    (cond
     ((symbol? x) (if (set-member? x b) '() (list x)))
     ((pair? x)
      (record-case x
                   (quote (obj) '())
                   (lambda (vars body)
                     (find-free body (set-union vars b)))
                   (if (test then else)
                       (set-union (find-free test b)
                                  (set-union (find-free then b)
                                             (find-free else b))))
                   (set! (var exp)
                         (set-union (if (set-member? var b) '() (list var))
                                    (find-free exp b)))
                   (call/cc (exp) (find-free exp b))
                   (else
                    (recur next ((x x))
                           (if (null? x)
                               '()
                             (set-union (find-free (car x) b)
                                        (next (cdr x))))))))
     (else '()))))

(define collect-free
  (lambda (vars e next)
    (if (null? vars)
        next
      (collect-free (cdr vars) e
                    (compile-refer (car vars) e
                                   (list 'ARGUMENT next))))))

(define find-sets
  (lambda (x v)
    (cond
     ((symbol? x) '())
     ((pair? x)
      (record-case x
                   (quote (obj) '())
                   (lambda (vars body)
                     (find-sets body (set-minus v vars)))
                   (if (test then else)
                       (set-union (find-sets test v)
                                  (set-union (find-sets then v)
                                             (find-sets else v))))
                   (set! (var x)
                         (set-union (if (set-member? var v) (list var) '())
                                    (find-sets x v)))
                   (call/cc (exp) (find-sets exp v))
                   (else
                    (recur next ((x x))
                           (if (null? x)
                               '()
                             (set-union (find-sets (car x) v)
                                        (next (cdr x))))))))
     (else '()))))

(define make-boxes
  (lambda (sets vars next)
    (recur f ((vars vars) (n 0))
           (if (null? vars)
               next
             (if (set-member? (car vars) sets)
                 (list 'BOX n (f (cdr vars) (+ n 1)))
               (f (cdr vars) (+ n 1)))))))

(define compile-refer
  (lambda (x e next)
    (compile-lookup x e
                    (lambda (n) (list 'REFER-LOCAL n next))
                    (lambda (n) (list 'REFER-FREE n next)))))

(define compile-lookup
  (lambda (x e return-local return-free)
    (recur nxtlocal ((locals (car e)) (n 0))
           (if (null? locals)
               (recur nxtfree ((free (cdr e)) (n 0))
                      (if (eq? (car free) x)
                          (return-free n)
                        (nxtfree (cdr free) (+ n 1))))
             (if (eq? (car locals) x)
                 (return-local n)
               (nxtlocal (cdr locals) (+ n 1)))))))

(define tail?
  (lambda (next)
    (eq? (car next) 'RETURN)))


;;;; runtime

(define *stack* (make-vector 1000))

(define push
  (lambda (x s)
    (vector-set! *stack* s x)
    (+ s 1)))

(define index
  (lambda (s i)
    (vector-ref *stack* (- (- s i) 1))))

(define index-set!
  (lambda (s i v)
    (vector-set! *stack* (- (- s i) 1) v)))


;;;; VM

(define VM
  (lambda (a x f c s)
    (dump-stack s)
    (print x)
    (record-case x
                 (HALT () a)
                 (REFER-LOCAL (n x)
                              (VM (index f n) x f c s))
                 (REFER-FREE (n x)
                             (VM (index-closure c n) x f c s))
                 (INDIRECT (x)
                           (VM (unbox a) x f c s))
                 (CONSTANT (obj x)
                           (VM obj x f c s))
                 (CLOSE (n body x)
                        (VM (closure body n s) x f c (- s n)))
                 (BOX (n x)
                      (index-set! s n (box (index s n)))
                      (VM a x f c s))
                 (TEST (then else)
                       (VM a (if a then else) f c s))
                 (ASSIGN-LOCAL (n x)
                               (set-box! (index f n) a)
                               (VM a x f c s))
                 (ASSIGN-FREE (n x)
                              (set-box! (index-closure c n) a)
                              (VM a x f c s))
                 (CONTI (x)
                        (VM (continuation s) x f c s))
                 (NUATE (stack x)
                        (VM a x f c (restore-stack stack)))
                 (FRAME (ret x)
                        (VM a x f c (push ret (push f (push c s)))))
                 (ARGUMENT (x)
                           (VM a x f c (push a s)))
                 (SHIFT (n m x)
                        (VM a x f c (shift-args n m s)))
                 (APPLY ()
                        (VM a (closure-body a) s a s))
                 (RETURN (n)
                         (let ((s (- s n)))
                           (VM a (index s 0) (index s 1) (index s 2) (- s 3)))))))

(define continuation
  (lambda (s)
    (closure
     (list 'REFER-LOCAL 0 (list 'NUATE (save-stack s) '(RETURN 0)))
     s
     s)))

(define closure
  (lambda (body n s)
    (let ((v (make-vector (+ n 1))))
      (vector-set! v 0 body)
      (recur f ((i 0))
             (unless (= i n)
               (vector-set! v (+ i 1) (index s i))
               (f (+ i 1))))
      v)))

(define closure-body
  (lambda (c)
    (vector-ref c 0)))

(define index-closure
  (lambda (c n)
    (vector-ref c (+ n 1))))

(define save-stack
  (lambda (s)
    (let ((v (make-vector s)))
      (recur copy ((i 0))
             (unless (= i s)
               (vector-set! v i (vector-ref *stack* i))
               (copy (+ i 1))))
      v)))

(define restore-stack
  (lambda (v)
    (let ((s (vector-length v)))
      (recur copy ((i 0))
             (unless (= i s)
               (vector-set! *stack* i (vector-ref v i))
               (copy (+ i 1))))
      s)))

(define box
  (lambda (x)
    (cons '=box= x)))

(define unbox
  (lambda (bx)
    (unless (eq? (car bx) '=box=)
      (error "is not box"))
    (cdr bx)))

(define set-box!
  (lambda (x v)
    (set-cdr! x v)))

(define shift-args
  (lambda (n m s)
    (recur nxtarg ((i (- n 1)))
           (unless (< i 0)
             (index-set! s (+ i m) (index s i))
             (nxtarg (- i 1))))
    (- s m)))


(define (dump-stack s)
  (write/ss (vector-copy *stack* 0 s))
  (newline))

;;;;

(define evaluate
  (lambda (x)
    (let1 code (compile x '() '() '(HALT))
      (VM '() code 0 '() 0))))


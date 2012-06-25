
(load "./util.scm")

(define extend
  (lambda (e r)
    (cons r e)))

(define compile
  (lambda (x e next)
    (cond ((symbol? x)
           (compile-lookup x e
                           (lambda (n m)
                             (list 'refer n m next))))
          ((pair? x)
           (record-case x
                        (quote (obj)
                               (list 'constant obj next))
                        (lambda (vars body)
                          (list 'close
                                (compile body
                                         (extend e vars)
                                         (list 'return))
                                next))
                        (if (test then else)
                            (let ((thenc (compile then e next))
                                  (elsec (compile else e next)))
                              (compile test e (list 'test thenc elsec))))
                        (else
                         (recur loop ((args (cdr x))
                                      (c (compile (car x) e '(apply))))
                                (if (null? args)
                                    (list 'frame next c)
                                  (loop (cdr args)
                                    (compile (car args)
                                             e
                                             (list 'argument c))))))))
          (else
           (list 'constant x next)))))

(define compile-lookup
  (lambda (var e return)
    (recur nxtrib ((e e) (rib 0))
           (if (null? e)
               (error "undefined" var)
             (recur nxtelt ((vars (car e)) (elt 0))
                    (cond
                     ((null? vars) (nxtrib (cdr e) (+ rib 1)))
                     ((eq? (car vars) var) (return rib elt))
                     (else (nxtelt (cdr vars) (+ elt 1)))))))))



;;;; runtime

(define stack (make-vector 1000))

(define push
  (lambda (x s)
    (vector-set! stack s x)
    (+ s 1)))

(define index
  (lambda (s i)
    (vector-ref stack (- (- s i) 1))))

(define index-set!
  (lambda (s i v)
    (vector-set! stack (- (- s i) 1) v)))


;;;; VM

(define VM
  (lambda (a x e r s)
    (record-case x
                 (halt () a)
                 (refer (n m x)
                        (VM (car (lookup n m e)) x e r s))
                 (constant (obj x)
                           (VM obj x e r s))
                 (close (body x)
                        (VM (closure body e) x e r s))
                 (test (then else)
                       (VM a (if a then else) e r s))
                 (assign (n m x)
                         (set-car! (lookup n m e) a)
                         (VM a x e r s))
                 (conti (x)
                        (VM (continuation s) x e r s))
                 (nuate (stack x)
                        (VM a x e r (restore-stack stack)))
                 (frame (ret x)
                        (VM a x e '() (push ret (push e (push r s)))))
                 (argument (x)
                           (VM a x e (cons a r) s))
                 (apply ()
                        (record a (body e)
                                (VM a body (extend e r) '() s)))
                 (return ()
                         (VM a (index s 0) (index s 1) (index s 2) (- s 3))))))

(define continuation
  (lambda (s)
    (closure
     (list 'refer 0 0 (list 'nuate (save-stack s) '(return)))
     '())))

(define closure
  (lambda (body e)
    (list body e)))

(define save-stack
  (lambda (s)
    (let ((v (make-vector s)))
      (recur copy ((i 0))
             (unless (= i s)
               (vector-set! v i (vector-ref stack i))
               (copy (+ i 1))))
      v)))

(define restore-stack
  (lambda (v)
    (let ((s (vector-length v)))
      (recur copy ((i 0))
             (unless (= i s)
               (vector-set! stack i (vector-ref v i))
               (copy (+ i 1))))
      s)))

(define lookup
  (lambda (n m e)
    (recur nxtrib ((e e) (rib n))
           (if (= rib 0)
               (recur nxtelt ((r (car e)) (elt m))
                      (if (= elt 0)
                          r
                        (nxtelt (cdr r) (- elt 1))))
             (nxtrib (cdr e) (- rib 1))))))

(define evaluate
  (lambda (x)
    (let1 code (compile x '() '(halt))
      (VM '() code '() '() 0))))


#!/usr/local/bin/gosh

(load "./util.scm")

(define extend
  (lambda (e r)
    (cons r e)))

(define compile
  (lambda (x e next)
    (cond
     ((symbol? x)
      (list 'refer (compile-lookup x e) next))
     ((pair? x)
      (record-case x
                   (quote (obj)
                          (list 'constant obj next))
                   (lambda (vars body)
                     (list 'close
                           (compile body (extend e vars) '(return))
                           next))
                   (if (test then else)
                       (let ((thenc (compile then e next))
                             (elsec (compile else e next)))
                         (compile test e (list 'test thenc elsec))))
                   (set! (var x)
                         (let ((access (compile-lookup var e)))
                           (compile x e (list 'assign access next))))
                   (call/cc (x)
                            (let ((c (list 'conti
                                           (list 'argument
                                                 (compile x e '(apply))))))
                              (if (tail? next)
                                  c
                                (list 'frame next c))))
                   (else
                    (recur loop ((args (cdr x))
                                 (c (compile (car x) e '(apply))))
                           (if (null? args)
                               (if (tail? next)
                                   c
                                 (list 'frame next c))
                             (loop (cdr args)
                                   (compile (car args)
                                            e
                                            (list 'argument c))))))))
     (else
      (list 'constant x next)))))

(define tail?
  (lambda (next)
    (eq? (car next) 'return)))


(define compile-lookup
  (lambda (var e)
    (recur nxtrib ((e e) (rib 0))
           (recur nxtelt ((vars (car e)) (elt 0))
                  (cond
                   ((null? vars) (nxtrib (cdr e) (+ rib 1)))
                   ((eq? (car vars) var) (cons rib elt))
                   (else (nxtelt (cdr vars) (+ elt 1))))))))

;;;;

(define VM
  (lambda (a x e r s)
    (record-case x
                 (halt () a)
                 (refer (var x)
                        (VM (car (lookup var e)) x e r s))
                 (constant (obj x)
                           (VM obj x e r s))
                 (close (body x)
                        (VM (closure body e) x e r s))
                 (test (then else)
                       (VM a (if a then else) e r s))
                 (assign (var x)
                         (set-car! (lookup var e) a)
                         (VM a x e r s))
                 (conti (x)
                        (VM (continuation s) x e r s))
                 (nuate (s var)
                        (VM (car (lookup var e)) '(return) e r s))
                 (frame (ret x)
                        (VM a x e '() (call-frame ret e r s)))
                 (argument (x)
                           (VM a x e (cons a r) s))
                 (apply ()
                        (record a (body e)
                                (VM a body (extend e r) '() s)))
                 (return ()
                         (record s (x e r s)
                                 (VM a x e r s)))
                 (else
                  (error "illegal opcode")))))

(define lookup
  (lambda (access e)
    (recur nxtrib ((e e) (rib (car access)))
           (if (= rib 0)
               (recur nxtelt ((r (car e)) (elt (cdr access)))
                      (if (= elt 0)
                          r
                        (nxtelt (cdr r) (- elt 1))))
             (nxtrib (cdr e) (- rib 1))))))

(define closure
  (lambda (body e)
    (list body e)))

(define continuation
  (lambda (s)
    (closure (list 'nuate s '(0 . 0)) '())))

(define call-frame
  (lambda (x e r s)
    (list x e r s)))

(define evaluate
  (lambda (x)
    (VM '() (compile x '() '(halt)) '() '() '())))

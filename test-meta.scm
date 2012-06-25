
(load "./util.scm")
(load "./macro2.scm")

(define-macro (define-constant sym val)
  `(define ,sym ,val))

(define-macro (defops . ls)
  (if #f
      ;; Use symbol for opcode
      `(begin
         ,@(map (lambda (sym)
                  `(define-constant ,sym ',sym))
                ls))
    ;; Use enum for opcode
    `(begin
       ,@(recur loop ((ls ls)
                      (i 0))
                (if (null? ls)
                    '()
                  `((define-constant ,(car ls) ,i)
                    ,@(loop (cdr ls) (+ i 1))))))))

(defops HALT
        LREF
        FREF
        GREF
        UNBOX
        CONST
        CLOSE
        BOX
        TEST
        LSET
        FSET
        GSET
        CONTI
        NUATE
        FRAME
        ARG
        SHIFT
        APPLY
        RET
        
        EXTEND
        SHRINK
        )


(define (compile x e s next)
  (cond
   ((symbol? x)
    (compile-refer x e
                   (if (set-member? x s)
                       (list* UNBOX next)
                     next)))
   ((pair? x)
    (record-case x
                 (quote (obj) (list* CONST obj next))
                 (lambda (vars . bodies)
                   (compile-lambda vars bodies e s next))
                 (if (test then . rest)
                     (let ((else (cond ((null? rest) #f)
                                       ((null? (cdr rest)) (car rest))
                                       (else (error "malformed if")))))
                       (let ((thenc (compile then e s next))
                             (elsec (compile else e s next)))
                         (compile test e s (list* TEST thenc elsec)))))
                 (set! (var x)
                       (compile-lookup var e
                                       (lambda (n)   (compile x e s (list* LSET n next)))
                                       (lambda (n)   (compile x e s (list* FSET n next)))
                                       (lambda (sym) (compile x e s (list* GSET sym next)))))
                 (call/cc (x)
                          (let ((c (list* CONTI (tail? next)
                                         (list* ARG
                                               (compile x e s
                                                        (if (tail? next)
                                                            (list* SHIFT
                                                                  1
                                                                  (list APPLY 1))
                                                          (list APPLY 1)))))))
                            (if (tail? next)
                                c
                              (list* FRAME c next))))
                 (begin bodies
                   (compile-lambda-bodies (car e) bodies (cdr e) s s next))
                 (else
                  (let ((func (car x))
                        (args (cdr x)))
                    (compile-apply func args e s next)))))
   (else (list* CONST x next))))

(define (compile-apply func args e s next)
  (if (direct-invoke? func)
      (compile-apply-direct func args e s next)
    (let ((argnum (length args)))
      (let ((c (compile func e s
                        (if (tail? next)
                            (list* SHIFT
                                  argnum
                                  (list APPLY argnum))
                          (list APPLY argnum)))))
        (let ((bc (compile-apply-args args c  e s)))
          (if (tail? next)
              bc
            (list* FRAME bc next)))))))

(define (compile-apply-args ap c e s)
  (recur loop ((ap ap)
               (c c))
         (if (null? ap)
             c
           (loop (cdr ap)
                 (compile (car ap) e s
                          (list* ARG c))))))

(define (direct-invoke? func)
  (and (pair? func)
       (eq? (car func) 'lambda)
       #f
       ))

(define (compile-apply-direct func args e s next)
  ;; 引数の個数チェック
  (define (check-argnum varnum args)
    (let ((argnum (length args))
          (minvarnum (car varnum))
          (maxvarnum (cdr varnum)))
      (cond ((< argnum (car varnum)) (error "too few argument(s):" argnum 'for minvarnum))
            ((and (>= maxvarnum 0)
                  (> argnum maxvarnum)) (error "too many arguments:" argnum 'for maxvarnum)))
      (if (< maxvarnum 0)
          ;; restパラメータあり
          (receive (must rest) (split-at args minvarnum)
            (if (null? rest)
                `(,@must '())
              `(,@must (list ,@rest))))
        args)))
  
  (let ((vars (cadr func))
        (bodies (cddr func)))
    (let* ((proper-vars (dotted->proper vars))
           (ext-vars (append proper-vars (car e))))
      (let ((free (cdr e))  ; 上のスコープの自由変数をそのまま引き継ぐ
            (sets (set-union s (find-setses bodies ext-vars)))
            (varnum (if (eq? vars proper-vars)
                        (cons (length vars) (length vars))
                      (cons (- (length proper-vars) 1)
                            -1))))
        (let ((args2 (check-argnum varnum args)))
          (if (null? proper-vars)
              ;; 変数なし(lambda () ...)：EXTEND～SHRINK 自体必要ない
              (compile-lambda-bodies (car e) bodies (cdr e) sets s
                                     next)
            (let ((c (list* EXTEND (length args2)
                           (make-boxes sets proper-vars
                                       (compile-lambda-bodies ext-vars bodies (cdr e) sets s
                                                              (cond ((tail? next) next)
                                                                    ((eq? (car next) SHRINK)
                                                                     (let ((argnum2 (cadr next))
                                                                           (nnext (cddr next)))
                                                                       (list* SHRINK
                                                                             (+ (length args2) argnum2)
                                                                             nnext)))
                                                                    (else
                                                                     (list* SHRINK (length args2)
                                                                           next))))))))
              (compile-apply-args args2 c e s))))))))

(define (compile-lambda vars bodies e s next)
  (let ((proper-vars (dotted->proper vars)))
    (let ((free (set-intersect (set-union (car e)
                                          (cdr e))
                               (find-frees bodies proper-vars)))
          (sets (find-setses bodies proper-vars))
          (varnum (if (eq? vars proper-vars)
                      (cons (length vars) (length vars))
                    (cons (- (length proper-vars) 1)
                          -1))))
      (collect-free free e
                    (list* CLOSE
                          varnum
                          (length free)
                          (make-boxes sets proper-vars
                                      (compile-lambda-bodies proper-vars bodies free sets s (list RET)))
                          next)))))

(define (compile-lambda-bodies vars bodies free sets s next)
  (let ((ee (cons vars free))
        (ss (set-union sets
                       (set-intersect s free))))
    (recur loop ((p bodies))
           (if (null? p)
               next
             (compile (car p) ee ss
                      (loop (cdr p)))))))

(define (find-frees xs b)
  (recur loop ((v '())
               (p xs))
         (if (null? p)
             v
           (loop (set-union v (find-free (car p) b))
                 (cdr p)))))

(define (find-free x b)
  (cond
   ((symbol? x) (if (set-member? x b) '() (list x)))
   ((pair? x)
    (record-case x
                 (lambda (vars . bodies)
                   (find-frees bodies (set-union (dotted->proper vars) b)))
                 (quote   all '())
                 (if      all (find-frees all b))
                 (set!    all (find-frees all b))
                 (call/cc all (find-frees all b))
                 (begin   all (find-frees all b))
                 (else        (find-frees x   b))))
   (else '())))

(define (collect-free vars e next)
  (if (null? vars)
      next
    (collect-free (cdr vars) e
                  (compile-refer (car vars) e
                                 (list* ARG next)))))

(define (find-setses xs v)
  (recur loop ((b '())
               (p xs))
         (if (null? p)
             b
           (loop (set-union b (find-sets (car p) v))
                 (cdr p)))))

(define (find-sets x v)
  (if (pair? x)
      (record-case x
                   (set! (var x)
                         (set-union (if (set-member? var v) (list var) '())
                                    (find-sets x v)))
                   (lambda (vars . bodies)
                     (find-setses bodies (set-minus v (dotted->proper vars))))
                   (quote   all '())
                   (if      all (find-setses all v))
                   (call/cc all (find-setses all v))
                   (begin   all (find-setses all v))
                   (else        (find-setses x   v)))
    '()))

(define (make-boxes sets vars next)
  (recur f ((vars vars) (n 0))
         (if (null? vars)
             next
           (if (set-member? (car vars) sets)
               (list* BOX n (f (cdr vars) (+ n 1)))
             (f (cdr vars) (+ n 1))))))

(define (compile-refer x e next)
  (compile-lookup x e
                  (lambda (n)   (list* LREF n next))
                  (lambda (n)   (list* FREF n next))
                  (lambda (sym) (list* GREF sym next))))

(define (find-index x ls)
  (let loop ((ls ls)
             (idx 0))
    (cond ((null? ls) #f)
          ((eq? (car ls) x) idx)
          (else (loop (cdr ls) (+ idx 1))))))

(define (compile-lookup x e return-local return-free return-global)
  (let ((locals (car e))
        (free   (cdr e)))
    (cond ((find-index x locals) => return-local)
          ((find-index x free) => return-free)
          (else (return-global x)))))

(define (tail? next)
  (eq? (car next) RET))



;;;;
;;; define special forms for macro expansion
;;; It is trivial, but needed

(define-special-form (quote x)
  `(quote ,x))

(define-special-form (lambda vars . bodies)
  `(lambda ,vars ,@(comp-macroexpand-1 bodies)))

(define-special-form (if test conseq . altern)
  `(if ,(comp-macroexpand-1 test)
       ,(comp-macroexpand-1 conseq)
     ,@(comp-macroexpand-1 altern)))

(define-special-form (set! var val)
  `(set! ,(comp-macroexpand-1 var)
     ,(comp-macroexpand-1 val)))

(define-special-form (quasiquote x)
  (transform-quasiquote x))

(define (transform-quasiquote x)
  (define (loop x)
    (cond ((not (pair? x)) `(quote (,x)))
          ((eq? (car x) 'unquote) `(list ,(cadr x)))
          ((eq? (car x) 'unquote-splicing) (cadr x))
          (else `(list (append ,@(map loop x))))))
  (let ((res (loop x)))
    (case (car res)
      ((list) (cadr res))
      ((quote) `(quote ,(caadr res)))
      (else (error "unexpected")))))

(define-special-form (define-macro name . f)
  (if (pair? name)
      `(define-macro ,(car name) (lambda ,(cdr name) ,@f))
    (begin
      (add-macro name 'MACRO (eval (car f)))
      `',name)))

;;;;
;; Define macros

(define-builtin-macro (begin . exps)
  `((lambda () ,@exps)))

(define-builtin-macro (define name . val)
  (if (pair? name)
      `(define ,(car name) (lambda ,(cdr name) ,@val))
    `(begin
       (set! ,name ,@val)
       ',name)))

(define-builtin-macro (let args . bodies)
  (if (pair? args)
      `((lambda ,(map car args)
          ,@bodies)
        ,@(map cadr args))
    ;; named let
    (if (symbol? args)
        ((lambda (name args bodies)
           `((lambda (,name)
               (set! ,name (lambda ,(map car args)
                             ,@bodies))
               (,name ,@(map cadr args)))
             '()))
         args (car bodies) (cdr bodies))
      (error "illegal let"))))

(define-builtin-macro (let1 var val . body)
  `((lambda (,var)
      ,@body)
    ,val))

(define-builtin-macro (let* args . body)
  (if (null? args)
      `(begin ,@body)
    (let1 a (car args)
      `(let1 ,(car a) ,(cadr a)
         (let* ,(cdr args) ,@body)))))

(define-builtin-macro (letrec parms . bodies)
  `((lambda ()
      ,@(map (lambda (e)
               `(define ,@e))
             parms)
      ,@bodies)))

(define-builtin-macro (cond . exps)
  (if (null? exps)
      #f
    (let1 clause (car exps)
      (if (not (pair? clause))
          (error "illegal cond exp" clause)
        (if (eq? (car clause) 'else)
            (if (null? (cdr exps))
                `(begin ,@(cdr clause))
              (error "syntax-error: 'else' clause followed by more clauses"))
          (let1 rest `(cond ,@(cdr exps))
            (if (null? (cdr clause))
                (let1 g (gensym)
                  `(let1 ,g ,(car clause)
                     (if ,g ,g
                       ,rest)))
              (if (eq? (cadr clause) '=>)
                  (let1 g (gensym)
                    `(let1 ,g ,(car clause)
                       (if ,g (,(caddr clause) ,g)
                         ,rest)))
                `(if ,(car clause)
                     (begin ,@(cdr clause))
                   ,rest)))))))))

(define-builtin-macro (case val . clauses)
  (let ((g (gensym)))
    `(let1 ,g ,val
       (cond
        ,@(let loop ((clauses clauses))
            (if (null? clauses)
                '()
              (let1 clause (car clauses)
                (cond ((not (pair? clause))
                       (error "illegal case exp" clause))
                      ((pair? (car clause))
                       `((,(let loop ((p (car clause)))
                             (cond ((not (pair? p)) #f)
                                   ((null? (cdr p)) `(eq? ,g ',(car p)))
                                   (else `(if (eq? ,g ',(car p))
                                              #t
                                            ,(loop (cdr p))))))
                          ,@(cdr clause))
                         ,@(loop (cdr clauses))))
                      ;; else
                      (else
                       `((else ,@(cdr clause))))))))))))

(define-builtin-macro (when c . exps)
  `(if ,c
       (begin ,@exps)
     #f))

(define-builtin-macro (unless c . exps)
  `(if ,c
       #f
     (begin ,@exps)))

(define-builtin-macro (and . exps)
  (cond ((null? exps) #t)
        ((null? (cdr exps)) (car exps))
        (else `(if ,(car exps)
                   (and ,@(cdr exps))
                 #f))))

(define-builtin-macro (or . exps)
  (cond ((null? exps) #f)
        ((null? (cdr exps)) (car exps))
        (else
         (let1 g (gensym)
           `(let1 ,g ,(car exps)
              (if ,g
                  ,g
                (or ,@(cdr exps))))))))

(define-builtin-macro (while pred . exps)
  (let ((g (gensym)))
    `(let ,g ()
       (when ,pred
         ,@exps
         (,g)))))

(define-builtin-macro (until pred . exps)
  (let ((g (gensym)))
    `(let ,g ()
       (unless ,pred
         ,@exps
         (,g)))))

(define-builtin-macro (load fn)
  (let ((sexps (file->sexp-list fn)))
    `(begin ,@sexps
       #t)))



(define (comp x s)
  (compile (comp-macroexpand-from-stack x s) '(()) '() (list RET)))


;;;;
(define (cadr x) (car (cdr x)))
(define (cddr x) (cdr (cdr x)))
(define (caddr x) (car (cddr x)))
(define (cdddr x) (cdr (cddr x)))

(define (list? ls)
  (cond ((null? ls) #t)
        ((pair? ls) (list? (cdr ls)))
        (else #f)))

(define (any f ls)
  (cond ((null? ls) #f)
        ((f (car ls)) #t)
        (else (any f (cdr ls)))))

(define (map f . args)
  (cond ((null? args) '())
        ((null? (cdr args))
         (let loop ((p (car args)))
           (if (null? p)
               '()
             (cons (f (car p))
                   (loop (cdr p))))))
        (else
         (let loop ((args args))
           (if (any null? args)
               '()
             (cons (apply f (map car args))
                   (loop (map cdr args))))))))

(define (map* f . args)
  (cond ((null? args) '())
        ((null? (cdr args))
         (let loop ((p (car args)))
           (cond ((pair? p)
                  (cons (f (car p))
                        (loop (cdr p))))
                 ((null? p) '())
                 (else (f p)))))
        (else
         (let loop ((args args))
           (if (any null? args)
               '()
             (cons (apply f (map* car args))
                   (loop (map* cdr args))))))))

(define (length ls)
  (if (pair? ls)
      (+ 1 (length (cdr ls)))
    0))

(define (list* . ls)
  (let loop ((ls ls))
    (if (pair? ls)
        (cond ((null? (cdr ls)) (car ls))
              (else (cons (car ls) (loop (cdr ls)))))
      ls)))

(define (reverse x)
  (let loop ((x x)
             (acc '()))
    (if (null? x)
        acc
      (loop (cdr x) (cons (car x) acc)))))

(define (reverse! x)
  (let loop ((x x)
             (acc '()))
    (if (null? x)
        acc
      (let1 d (cdr x)
        (set-cdr! x acc)
        (loop d x)))))

(define (file->sexp-list fn)
  (let ((f (open-input-file fn)))
    (if f
        (let loop ((acc '()))
          (let ((s (read f)))
            (if (eof-object? s)
                (reverse! acc)
              (loop (cons s acc)))))
      #f)))

(define macroexpand comp-macroexpand)
(define macroexpand-1 comp-macroexpand-1)


(define write/ss write)

(define (newline) (display "\n"))


(define (eval x)
  (run (comp x 0)))


#|
(define (repl)
  (display "type ':q' for quit\n")
  (let loop ()
    (display "> ") (flush)
    (let1 s (read)
      (if (or (eof-object? s)
              (eq? s ':q))
          (display "bye\n")
        (begin
          (write (eval s))
          (newline)
          (loop))))))


(define (main args)
  (if (null? args)
      (repl)
    (let loop ((p args))
      (if (null? p)
          '()
        (begin
          (let1 s (read-from-string (car p))
            (write/ss s) (newline)
            (let1 c (comp s 0)
              (write/ss c) (newline)
              (run c)
              (loop (cdr p)))))))))
|#

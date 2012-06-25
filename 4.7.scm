
(load "./util.scm")
(load "./macro.scm")
(use file.util)  ; file->sexp-list
(use srfi-1)  ; split-at

(define-macro (defops . ls)
  (if #t
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
        UNDEF
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
                     (let ((thenc (compile then e s next))
                           (elsec (cond ((null? rest)
                                         (compile-undef next))
                                        ((null? (cdr rest))
                                         (compile (car rest) e s next))
                                        (else (error "malformed if")))))
                       (compile test e s (list* TEST thenc elsec))))
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

(define (compile-undef next)
  (list* UNDEF next))

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
       ;#f
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
  (if (null? bodies)
      (compile-undef next)
    (let ((ee (cons vars free))
          (ss (set-union sets
                         (set-intersect s free))))
      (recur loop ((p bodies))
             (if (null? p)
                 next
               (compile (car p) ee ss
                        (loop (cdr p))))))))

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


;;;; runtime

(define *stack* (make-vector 1000))

(define (push x s)
  (vector-set! *stack* s x)
  (+ s 1))

(define (direct-index s)
  (vector-ref *stack* s))

(define (direct-index-set! s v)
  (vector-set! *stack* s v))

(define (index s i)
  (vector-ref *stack* (- (- s i) 2)))

(define (index-set! s i v)
  (vector-set! *stack* (- (- s i) 2) v))


;;;; VM

(define-macro (vrecord-case x . args)
  (let ((g1 (gensym))
        (g2 (gensym))
        (g3 (gensym)))
    `(let* ((,g1 ,x)
            (,g2 (car ,g1))
            (,g3 (cdr ,g1)))
       (cond
        ,@(map (lambda (e)
                (let ((key (car e))
                      (vars (cadr e))
                      (exprs (cddr e)))
                  (if (eq? key 'else)
                      e
                    `((eq? ,g2 ,key)
                      (record ,g3 ,vars ,@exprs)))))
              args)))))

(define *vm-trace-enable* #f)
(define (VM-trace flag)
  (set! *vm-trace-enable* flag))

(define (VM a x f c s)
  (when *vm-trace-enable*
    (write f) (write '/) (write s)
    (dump-stack s)
    (dump-opcode a x f c s))
  (vrecord-case x
                (HALT ()
;                      (unless (eq? s 0)
;                        (error "stack error"))
                      a)
                (LREF (n . x)
                      (VM (index f n) x f c s))
                (FREF (n . x)
                      (VM (index-closure c n) x f c s))
                (GREF (sym . x)
                      (VM (refer-global sym (lambda () (error "unbound variable:" sym))) x f c s))
                (UNBOX x
                       (VM (unbox a) x f c s))
                (CONST (obj . x)
                       (VM obj x f c s))
                (CLOSE (argnum n body . x)
                       (VM (closure argnum body n s) x f c (- s n)))
                (BOX (n . x)
                     (index-set! f n (box (index f n)))
                     (VM a x f c s))
                (TEST (then . else)
                      (VM a (if a then else) f c s))
                (LSET (n . x)
                      (set-box! (index f n) a)
                      (VM a x f c s))
                (FSET (n . x)
                      (set-box! (index-closure c n) a)
                      (VM a x f c s))
                (GSET (sym . x)
                      (assign-global! sym a)
                      (VM a x f c s))
                (CONTI (tail? . x)
                       (VM (continuation s tail?) x f c s))
                (NUATE (stack . x)
                       (VM a x f c (restore-stack stack)))
                (FRAME (x . ret)
                       (VM a x f c (push ret (push f (push c s)))))
                (ARG x
                     (VM a x f c (push a s)))
                (SHIFT (n . x)
                       (let ((m (index s (- n 1))))  ; 一つ前の呼び出しの引数の数
                         (VM a x f c (shift-args n m s))))
                (APPLY (argnum)
                       (do-apply argnum a s))
                (RET ()
                     (do-return a s))
                (EXTEND (argnum . x)
                        (expand-frame argnum f s)
                        (VM a x (+ f argnum) c s))
                (SHRINK (n . x)
                        (shrink-frame n f s)
                        (VM a x (- f n) c (- s n)))
                (UNDEF x
                       (VM (undefined) x f c s))
                (else
                 (error "unknown opcode" (car x)))))

(define (do-apply argnum a s)
  (let ((s (push argnum s)))
    (cond ((primitive-function? a)
           (let ((res (call-primitive-function a s argnum)))
             (do-return res s)))
          ((my-procedure? a)
           (let ((ss (check-argnum a argnum s)))
             (VM a (closure-body a) ss a ss)))
          (else
           (error "invalid application:" a)))))

(define (do-return a s)
  (let ((argnum (index s -1)))
    (let ((s (- s argnum)))
      (VM a (index s 0) (index s 1) (index s 2) (- s 4)))))

(define (copy-stack start end to)
  (if (> to start)
      ;; 後ろにずらす→後ろからコピー
      (recur copy1 ((s (- end 1))
                    (d (+ to (- end start) -1)))
             (if (>= s start)
                 (begin
                   (direct-index-set! d (direct-index s))
                   (copy1 (- s 1) (- d 1)))))
    ;; 前にコピー→前からコピー
    (recur copy2 ((s start)
                  (d to))
           (if (< s end)
               (begin
                 (direct-index-set! d (direct-index s))
                 (copy2 (+ s 1) (+ d 1)))))))

(define (expand-frame argnum f s)
  (let ((upper-argnum (index f -1)))
    (copy-stack f s (+ f argnum))  ; ローカルフレーム領域を空ける
    (copy-stack s (+ s argnum) (- f 1))  ; ローカルフレーム領域に移動
    (direct-index-set! (+ f argnum -1) (+ argnum upper-argnum))))  ; 引数の数を加算

(define (shrink-frame argnum f s)
  (let ((upper-argnum (index f -1)))
    (copy-stack f s (- f argnum))
    (direct-index-set! (- f argnum 1) (- upper-argnum argnum))))


(define (vm-apply s c . args)
  (define (push-args p s)
    (cond ((null? p) s)
          (else (push (car p)
                      (push-args (cdr p) s)))))
  (define (push-args2 p s)
    (cond ((null? p) s)
          ((null? (cdr p)) (push-args (car p) s))  ; applyの最後の引数：リスト
          (else (push (car p) (push-args2 (cdr p) s)))))
  (let* ((s2 (push `(,HALT) (push s (push '() s))))
         (ss (push-args2 args s2))
         (argnum (- ss s2)))
    (do-apply argnum c ss)))

(define (check-argnum c argnum s)
  (let ((varargnum (closure-argnum c)))
    (let ((minvarnum (car varargnum))
          (maxvarnum (cdr varargnum)))
      (cond ((< argnum minvarnum) (error "too few argument(s):" argnum 'for minvarnum))
            ((and (>= maxvarnum 0)
                  (> argnum maxvarnum)) (error "too many arguments:" argnum 'for maxvarnum)))
      (if (< maxvarnum 0)
          (set-rest-args argnum minvarnum s)
        s))))

(define (set-rest-args argnum minargnum s)
  (let ((ls (recur loop ((acc '())
                         (i (- argnum 1)))
                   (if (>= i minargnum)
                       (loop (cons (index s i) acc)
                         (- i 1))
                     acc))))
    (let ((ss (if (<= argnum minargnum)
                  (unshift-args minargnum s)
                (let ((d (- argnum minargnum 1)))
                  (if (> d 0)
                      (begin
                        (index-set! s -1 (+ minargnum 1))  ; 引数の数
                        (shift-args (+ minargnum 1)
                                    (- d 1)
                                    s))
                    s)))))
      (index-set! ss minargnum ls)
      ss)))

;;;; 可変長引数の関数呼び出し時にスタック上にrest引数用のバッファを作るため、スタックの要素をずらす
(define (unshift-args argnum s)
  ;; ひとつずらすだけでＯＫ
  (index-set! s -2 (+ (index s -1) 1))  ; 引数の数：+1してずらした位置に書く
  (recur loop ((i 0))
         (index-set! s (- i 1) (index s i))
         (when (< i argnum)
           (loop (+ 1 i))))
  (+ s 1))

(define (continuation s tail?)
  (let ((ss (if tail?
                s
              (push 0 s))))
    (closure
     '(1 . 1)  ; argnum
     (list* LREF 0
           (list* NUATE (save-stack ss)
                 (list RET)))
     0
     0)))

(define (closure argnum body n s)
  (let ((v (make-vector (+ n 2))))
    (vector-set! v 0 argnum)
    (vector-set! v 1 body)
    (recur f ((i 0))
           (unless (= i n)
             (vector-set! v (+ i 2) (index s (- i 1)))  ; CLOSE から closure が呼ばれるときは呼び出し引数の個数がスタックに積んでいないので、その分 -1
             (f (+ i 1))))
    v))

(define (closure-argnum c)
  (vector-ref c 0))

(define (closure-body c)
  (vector-ref c 1))

(define (index-closure c n)
  (vector-ref c (+ n 2)))

(define (save-stack s)
  (let ((v (make-vector s)))
    (recur copy ((i 0))
           (unless (= i s)
             (vector-set! v i (vector-ref *stack* i))
             (copy (+ i 1))))
    v))

(define (restore-stack v)
  (let ((s (vector-length v)))
    (recur copy ((i 0))
           (unless (= i s)
             (vector-set! *stack* i (vector-ref v i))
             (copy (+ i 1))))
    s))

(define (box x)
  (cons '=box= x))

(define (unbox bx)
  (unless (eq? (car bx) '=box=)
    (error "is not box" bx))
  (cdr bx))

(define (set-box! x v)
  (set-cdr! x v))

(define (shift-args n m s)
  (recur nxtarg ((i (- n 1)))
         (unless (< i 0)
           (index-set! s (+ i m) (index s (- i 1)))
           (nxtarg (- i 1))))
  (- s m 1))

;;; Global variable table

(define *global-variable-table* (make-hash-table))

(define (assign-global! sym val)
  (hash-table-put! *global-variable-table* sym val))

(define (refer-global sym no-exist)
  (if (hash-table-exists? *global-variable-table* sym)
      (hash-table-get *global-variable-table* sym)
    (no-exist)))

;;; Primitive function

(define-class <PrimFunc> ()
  ((name :init-keyword :name)
   (fn :init-keyword :fn)
   (minvarnum :init-keyword :minvarnum)
   (maxvarnum :init-keyword :maxvarnum)
   ))

(define (primitive-function? f)
  (is-a? f <PrimFunc>))

(define (call-primitive-function fn s argnum)
  (let ((minvarnum (slot-ref fn 'minvarnum))
        (maxvarnum (slot-ref fn 'maxvarnum)))
  (cond ((< argnum minvarnum)
         (error "Too few arguments" argnum 'for minvarnum '-- (slot-ref fn 'name)))
        ((and (> maxvarnum 0) (> argnum maxvarnum))
         (error "Too many arguments" argnum 'for maxvarnum '-- (slot-ref fn 'name)))
        (else ((slot-ref fn 'fn) s argnum)))))

(define (collect-args s argnum)
  (let loop ((i (- argnum 1))
             (acc '()))
    (if (>= i 0)
        (loop (- i 1) (cons (index s i) acc))
      acc)))

;;;;

(define (dump-stack s)
  (display "#[")
  (let loop ((i 0))
    (when (< i s)
      (my-write (vector-ref *stack* i))
      (when (< i (- s 1)) (display " "))
      (loop (+ 1 i))))
  (display "]\n"))

(define (dump-opcode a x f c s)
  (vrecord-case x
                (HALT () (my-write `(HALT)))
                (LREF (n . x) (my-write `(LREF ,n : ,(index f n))))
                (FREF (n . x) (my-write `(FREF ,n : ,(index-closure c n))))
                (GREF (sym . x) (my-write `(GREF ,sym : ,(refer-global sym error))))
                (UNBOX x (my-write `(UNBOX : ,(unbox a))))
                (CONST (obj . x) (my-write `(CONST ,obj)))
                (CLOSE (argnum n body . x) (my-write `(CLOSE ,argnum ,n)))
                (BOX (n . x) (my-write `(BOX ,n : ,(index f n))))
                (TEST (then . else) (my-write `(TEST : ,a)))
                (LSET (n . x) (my-write `(LSET ,n : ,a)))
                (FSET (n . x) (my-write `(FSET ,n : ,a)))
                (GSET (sym . x) (my-write `(GSET ,sym : ,a)))
                (CONTI (tail? . x) (my-write `(CONTI ,tail?)))
                (NUATE (stack . x) (my-write `(NUATE)))
                (FRAME (x . ret) (my-write `(FRAME)))
                (ARG x (my-write `(ARG)))
                (SHIFT (n . x) (my-write `(SHIFT ,n)))
                (APPLY (argnum) (my-write `(APPLY ,argnum)))
                (RET () (my-write `(RET)))
                (EXTEND (argnum . x) (my-write `(EXTEND ,argnum)))
                (SHRINK (n . x) (my-write `(SHRINK ,n)))
                (UNDEF x (my-write `(UNDEF)))
                (else
                 (error "unknown opcode" (car x))))
  (newline))

(define (dump-code code)
  (define (print-cell c indent)
    (display (make-string indent #\SPACE))
    (display "(")
    (recur loop ((p c))
           (if (null? p)
               (display ")")
             (let ((a (car p)))
               (if (pair? a)
                   (begin
                     (newline)
                     (print-cell a (+ indent 1))
                     (loop (cdr p)))
                 (begin
                   (unless (eq? p c)
                     (display " "))
                   (write a)
                   (loop (cdr p))))))))
  (print-cell code 0)
  (newline))

;;;;

(define (my-procedure? f)
  (or (vector? f)  ; closure?
      (primitive-function? f)))

(define (my-write s)
  (define (abbrev? s sym)
    (and (eq? (car s) sym)
         (not (null? (cdr s)))
         (null? (cddr s))))
  (cond ((primitive-function? s)
         (begin (display "#<subr:") (display (slot-ref s 'name)) (display ">")))
        ((my-procedure? s)
         (display "#<closure>"))
        ((pair? s)
         (cond ((abbrev? s 'quote) (display #\') (my-write (cadr s)))
               ((abbrev? s 'quasiquote) (display #\`) (my-write (cadr s)))
               (else
                (display "(")
                (let loop ((first #t)
                           (ls s))
                  (if (pair? ls)
                      (begin
                        (unless first (display " "))
                        (my-write (car ls))
                        (loop #f (cdr ls)))
                    (when (not (null? ls))
                      (display " . ")
                      (my-write ls))))
                (display ")"))))
        (else
         (write s))))

(define (comp x s)
  (compile (comp-macroexpand-from-stack x s) '(()) '() (list RET)))

(define (run code s)
  (let ((s2 (push `(,HALT) (push 0 (push '() s)))))  ; top stack frame
    (let ((ss (push 0 s2)))  ; argnum
      (VM '() code ss '() ss))))

(define (evaluate-from-stack sexp s)
  (run (comp sexp s) s))

(define (evaluate x)
  (evaluate-from-stack x 0))


(define (repl2 tty?)
  (when tty? (display "type ':q' for quit\n"))
  (recur recover ()
         (guard (exc
                 (else (if tty?
                           (begin
                            (print (condition-ref exc 'message))
                             (recover))
                         (raise exc))))
                (recur loop ()
                       (when tty? (display "> "))
                       (flush)
                       (let1 s (read)
                         (if (or (eof-object? s)
                                 (eq? s ':q))
                             (when tty? (print "bye"))
                           (begin
                             (my-write (evaluate s))
                             (newline)
                             (loop))))))))

(define (repl)
  (repl2 (sys-isatty (standard-input-port))))

(define-macro (assign-prim-fn! name argnum . rest)
  (define (gen-dispatcher fn minvarnum maxvarnum)
    (if (= minvarnum maxvarnum)
        `(lambda (s argnum)
           (,fn ,@(map (lambda (i) `(index s ,i))
                       (iota minvarnum))))
      `(lambda (s argnum)
         (apply ,fn (collect-args s argnum)))))
  
  (let ((minvarnum (if (number? argnum) argnum (car argnum)))
        (maxvarnum (cond ((number? argnum) argnum)
                         ((null? (cdr argnum)) -1)
                         (else (cadr argnum)))))
    (let ((fn (if (null? rest)
                  (gen-dispatcher name minvarnum maxvarnum)
                (car rest))))
      `(assign-global! ',name
                       (make <PrimFunc>
                             :name ',name
                             :fn ,fn
                             :minvarnum ,minvarnum
                             :maxvarnum ,maxvarnum)))))

(define (init-globals)
  (assign-prim-fn! cons 2)
  (assign-prim-fn! car 1)
  (assign-prim-fn! cdr 1)
  (assign-prim-fn! eq? 2)
  (assign-prim-fn! null? 1)
  (assign-prim-fn! symbol? 1)
  (assign-prim-fn! pair? 1)
  (assign-prim-fn! list? 1)
  (assign-prim-fn! set-car! 2)
  (assign-prim-fn! set-cdr! 2)
  (assign-prim-fn! not 1)
  (assign-prim-fn! + (0))
  (assign-prim-fn! - (1))
  (assign-prim-fn! * (0))
  (assign-prim-fn! / (1))
  (assign-prim-fn! = 2)
  (assign-prim-fn! < (2))
  (assign-prim-fn! > (2))
  (assign-prim-fn! <= (2))
  (assign-prim-fn! >= (2))
  (assign-prim-fn! write 1
                   (lambda (s argnum)
                     (my-write (index s 0))))
  (assign-prim-fn! write/ss 1)
  (assign-prim-fn! display 1)
  (assign-prim-fn! newline 0)
  (assign-prim-fn! flush 0)
  (assign-prim-fn! list (0))
  (assign-prim-fn! append (0))
  (assign-prim-fn! list* (0))
  (assign-prim-fn! list? 1)
  (assign-prim-fn! reverse 1)
  (assign-prim-fn! reverse! 1)
  (assign-prim-fn! read 0)
  (assign-prim-fn! read-from-string 1)
  (assign-prim-fn! file->sexp-list 1)
  (assign-prim-fn! eof-object? 1)
  (assign-prim-fn! map (2)
                   (lambda (s argnum)
                     (let ((fn (index s 0)))
                       (if (= argnum 2)
                           (let loop ((p (index s 1))
                                      (acc '()))
                             (if (null? p)
                                 (reverse! acc)
                               (loop (cdr p)
                                     (cons (vm-apply s fn (car p) '())
                                           acc))))
                         (let loop ((args (cdr (collect-args s argnum)))
                                    (acc '()))
                           (if (any null? args)
                               (reverse! acc)
                             (loop (map cdr args)
                                   (cons (vm-apply s fn (map car args))
                                         acc))))))))

  (assign-prim-fn! caar 1)
  (assign-prim-fn! cadr 1)
  (assign-prim-fn! cddr 1)
  (assign-prim-fn! caddr 1)
  (assign-prim-fn! cdddr 1)
  (assign-prim-fn! length 1)
  (assign-prim-fn! gensym 0)
  (assign-prim-fn! error (1))

  (assign-prim-fn! make-hash-table 0)
  (assign-prim-fn! hash-table-exists? 2)
  (assign-prim-fn! hash-table-put! 3)
  (assign-prim-fn! hash-table-get 2)
  (assign-prim-fn! hash-table-for-each 2
                   (lambda (s argnum)
                     (let ((ht (index s 0))
                           (proc (index s 1)))
                       (hash-table-for-each ht
                                            (lambda (k v)
                                              (vm-apply s proc k v '()))))))
  (assign-prim-fn! hash-table-keys 1)
  (assign-prim-fn! hash-table-values 1)
  (assign-prim-fn! hash-table-clear! 1)
  (assign-prim-fn! make-vector 0)
  (assign-prim-fn! vector-set! 3)
  (assign-prim-fn! vector-ref 2)
  (assign-prim-fn! VM-trace 1)

  (assign-prim-fn! apply (0)
                   (lambda (s argnum)
                     (let ((args (collect-args s argnum)))
                       (apply vm-apply s args))))
  (assign-prim-fn! vm-apply (1)
                   (lambda (s argnum)
                     (let ((args (collect-args s argnum)))
                       (apply vm-apply s args))))
  (assign-prim-fn! macroexpand 1
                   (lambda (s argnum)
                     (comp-macroexpand (index s 0))))
  (assign-prim-fn! eval 1
                   (lambda (s argnum)
                     (evaluate-from-stack (index s 0) s)))
  (assign-prim-fn! evaluate 1
                   (lambda (s argnum)
                     (evaluate-from-stack (index s 0) s)))
  (assign-prim-fn! compile 1
                   (lambda (s argnum)
                     (let ((sexp (index s 0)))
                       (comp sexp s))))
  (assign-prim-fn! run 1
                   (lambda (s argnum)
                     (let ((code (index s 0)))
                       (run code s))))
  
  (assign-prim-fn! any 2
                   (lambda (s argnum)
                     (let ((f (index s 0))
                           (p (index s 1)))
                       (any (lambda (x) (vm-apply s f (list x))) (car p)))))
  (assign-prim-fn! procedure? 1
                   (lambda (s argnum)
                     (my-procedure? (index s 0))))
  (assign-prim-fn! primitive-function? 1)
  
  (assign-prim-fn! macroexpand 1
                   (lambda (s argnum)
                     (comp-macroexpand-from-stack (index s 0) s)))
  (assign-prim-fn! macroexpand-1 1
                   (lambda (s argnum)
                     (comp-macroexpand-1-from-stack (index s 0) s)))
  (assign-prim-fn! disasm 1
                   (lambda (s argnum)
                     (let ((fn (index s 0)))
                       (if (and (not (primitive-function? fn))
                                (my-procedure? fn))
                           (closure-body fn)
                         #f))))
  )

(init-globals)

;;;;
;;; define special forms for macro expansion
;;; It is trivial, but needed

(define-special-form (quote . all)
  `(quote ,@all))

(define-special-form (lambda vars . bodies)
  (define (define? x) (and (pair? x) (eq? (car x) 'define)))
  (define (normalize-define exp)
    (let ((name (car exp))
          (bodies (cdr exp)))
      (if (pair? name)
          (normalize-define `(,(car name) (lambda ,(cdr name) ,@bodies)))
        exp)))
  (receive (internal-defines actual-bodies)
           (partition define? bodies)
    (let ((defines (map (lambda (x) (normalize-define (cdr x))) internal-defines)))
      (if (null? defines)
          `(lambda ,vars ,@(map comp-macroexpand-1 bodies))
        `(lambda ,vars
           ((lambda ,(map car defines)
              ,@(map (lambda (e)
                       `(set! ,(car e) ,(cadr e)))
                     defines)
              ,@actual-bodies)
            ,@(map (lambda (_) '()) defines)))))))

(define-special-form (if . all)
  `(if ,@(map comp-macroexpand-1 all)))

(define-special-form (set! . all)
  `(set! ,@(map comp-macroexpand-1 all)))

(define-special-form (quasiquote x)
  (transform-quasiquote x))

(define-special-form (define-macro name . f)
  (if (pair? name)
      `(define-macro ,(car name) (lambda ,(cdr name) ,@f))
    (begin
      (add-macro name 'MACRO (evaluate-from-stack (car f) %sp%))
      `',name)))

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

(define-special-form (begin . all)
  `(begin ,@(map comp-macroexpand-1 all)))

;;;;
;; Define macros

(define-builtin-macro (define name . val)
  (if (pair? name)
      `(define ,(car name) (lambda ,(cdr name) ,@val))
    `(begin
       (set! ,name ,@val)
       ',name)))

(define-builtin-macro (let args . bodies)
  (if (list? args)
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
      `(begin)
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
       (begin ,@exps)))

(define-builtin-macro (unless c . exps)
  `(if ,c
       (begin)
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

;;eof

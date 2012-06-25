
(define-macro (record args parm . exprs)
  `(apply (lambda ,parm
            ,@exprs)
          ,args))

(define-macro (record-case x . args)
  (let ((g1 (gensym)))
    `(let ((,g1 ,x))
       (case (car ,g1)
         ,@(map (lambda (e)
                  (let ((key (car e))
                        (vars (cadr e))
                        (exprs (cddr e)))
                    (if (eq? key 'else)
                        e
                      `((,key)
                        (record (cdr ,g1) ,vars ,@exprs)))))
                args)))))

(define-macro (recur . args)
  `(let ,@args))

;;; dotted pair -> proper list
(define (dotted->proper ls)
  (if (list? ls)
      ls
    (let loop ((p ls)
               (acc '()))
      (if (pair? p)
          (loop (cdr p)
                (cons (car p) acc))
        (reverse! (cons p acc))))))

;;;; set

(define set-member?
  (lambda (x s)
    (cond
     ((null? s) #f)
     ((eq? x (car s)) #t)
     (else (set-member? x (cdr s))))))

(define set-cons
  (lambda (x s)
    (if (set-member? x s)
        s
      (cons x s))))

(define set-union
  (lambda (s1 s2)
    (if (null? s1)
        s2
      (set-union (cdr s1) (set-cons (car s1) s2)))))

(define set-minus
  (lambda (s1 s2)
    (if (null? s1)
        '()
      (if (set-member? (car s1) s2)
          (set-minus (cdr s1) s2)
        (cons (car s1) (set-minus (cdr s1) s2))))))

(define set-intersect
  (lambda (s1 s2)
    (if (null? s1)
        '()
      (if (set-member? (car s1) s2)
          (cons (car s1) (set-intersect (cdr s1) s2))
        (set-intersect (cdr s1) s2)))))


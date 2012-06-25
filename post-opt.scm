#!/usr/local/bin/gosh

(use util.match)

(define first  car)
(define second cadr)
(define third  caddr)
(define fourth cadddr)

(define-macro (replace-rule code . ls)
  `(match ,code
          ,@(map (lambda (e)
                   (if (eq? (second e) '=>)
                       `((,@(first e)) (values ,(third e) ,(fourth e)))
                     e))
                 ls)
          (else (values #f code))))


;;;; 置き換えルール
(define (get-replace-rule code)
  (define (contain? sub lst)
    (cond ((null? lst) #f)
          ((eq? sub lst) #t)
          (else (contain? sub (cdr lst)))))
  (define (takeWhile sub lst)
    (let loop ((acc '())
               (lst lst))
      (if (or (null? lst)
              (eq? sub lst))
          (reverse! acc)
        (loop (cons (car lst) acc) (cdr lst)))))
  (define (end-with end lst)
    (cond ((null? lst) #f)
          ((equal? lst end) lst)
          (else (end-with end (cdr lst)))))
  
  (replace-rule code
;                (('GREF f 'APPLY n) => `(GREF-APPLY ,f ,n) '())
;                (('GREF f 'SHIFT m 'APPLY n) => `(GREF-SHIFT-APPLY ,f ,n) '())
;                (('SHIFT m 'APPLY n) => `(SHIFT-APPLY ,n) '())
;                (('CONST obj 'ARG . %rest) => `(CONST-ARG ,obj) %rest)
                (('CONST '#f 'TEST then . else) => else '())  ; 展開されたandの置き換え
                (('LREF 0 'TEST ('LREF 0 'SHRINK n 'TEST then . else1) . else2) => `(LREF 0 TEST (SHRINK ,n ,@then) ,@else2) '())
                (('FRAME proc 'TEST then . else)
                 (let ((c (end-with '(ARG GREF not APPLY 1) proc)))
                   (if c
                       (values `(,@(takeWhile c proc) TEST ,else ,@then) '())
                     (values #f code))))
                ))


(define optbl
  '((HALT ())
    (LREF (n . $x))
    (FREF (n . $x))
    (GREF (sym . $x))
    (UNBOX $x)
    (CONST (obj . $x))
    (CLOSE (argnum n $body . $x))
    (BOX (n . $x))
    (TEST ($then . $else))
    (LSET (n . $x))
    (FSET (n . $x))
    (GSET (sym . $x))
    (CONTI (tail$ . $x))
    (NUATE (stack . $x))
    (FRAME ($x . $ret))
    (ARG $x)
    (SHIFT (n . $x))
    (APPLY (argnum))
    (RET ())
    (EXTEND (argnum . $x))
    (SHRINK (n . $x))
    (UNDEF $x)
    ))

(define *h* (make-hash-table))

(dolist (e optbl)
  (let ((sym (car e))
        (args (cadr e)))
    (hash-table-put! *h* sym args)))

(define (next-ops code)
  (define (op? sym)
    (eq? (string-ref (symbol->string sym) 0)
         #\$))
  (define (check sym x f)
    (if (op? sym)
        (f x)
      (f #f)))
  (define (scons x xs)
    (if x (cons x xs) xs))
  
  (let* ((op (car code))
         (e (and (hash-table-exists? *h* op)
                 (hash-table-get *h* op))))
    (if e
        (reverse!
         (let loop ((p e)
                    (q (cdr code))
                    (acc '()))
           (cond ((pair? p)
                  (check (car p) (car q)
                         (lambda (x) (loop (cdr p) (cdr q) (scons x acc)))))
                 ((null? p) acc)
                 (else
                  (check p q
                         (lambda (x) (scons x acc)))))))
      '())))

(define (replace pair newpair)
  (set-car! pair (car newpair))
  (set-cdr! pair (cdr newpair)))

(define (optimize! code)
  (when (not (null? code))
    (receive (rep rest) (get-replace-rule code)
             (if rep
                 (begin
                   (replace code (cond ((null? rest) rep)
                                       (else (append rep (optimize! rest)))))
                   (optimize! code))
               (begin
                 (dolist (x (next-ops code))
                   (optimize! x))))))
  code)

(define (main args)
  (until (read) eof-object? => code
    (optimize! code)
    (write/ss code)
    (newline)))

;;;; macro

(define *macro-table* (make-hash-table))

(define (add-macro name type f)
  (hash-table-put! *macro-table* name (cons type f)))

(define-macro (define-special-form name . f)
  (if (pair? name)
      `(define-special-form ,(car name) (lambda (%sp% ,@(cdr name)) ,@f))
    `(add-macro ',name 'SF ,(car f))))

(define-macro (define-builtin-macro name . f)
  (if (pair? name)
      `(define-builtin-macro ,(car name) (lambda ,(cdr name) ,@f))
    `(add-macro ',name 'MACRO ,(evaluate (car f)))))

(define (macro? name)
  (and (hash-table-exists? *macro-table* name)
       (hash-table-get *macro-table* name)))

(define (all f . args)
  (let loop ((args args))
    (if (any null? args)
        #t
      (and (apply f (map car args))
           (loop (map cdr args))))))

(define (comp-macroexpand-1-from-stack x s)
  (if (pair? x)
      (let1 name (car x)
        (let ((trns
               (cond ((macro? name) => (lambda (c)
                                         (let ((type (car c))
                                               (f (cdr c)))
                                           (if (eq? type 'SF)
                                               (apply f s (cdr x))
                                             (vm-apply s f (cdr x))))))
                     (else (map (lambda (y)
                                  (comp-macroexpand-1-from-stack y s))
                                x)))))
          (if (and (pair? trns)
;                   (equal? x trns)  ; all ‚¾‚¯‚¾‚ÆA‚Ç‚¿‚ç‚©‚ª’Z‚¢ê‡‚É¬Œ÷‚µ‚Ä‚µ‚Ü‚¤ (all eq? '(1 2) '(1 2 3)) => #t
                   (all eq? x trns))
              x
            trns)))
    x))

(define (comp-macroexpand-from-stack x s)
  (let1 t (comp-macroexpand-1-from-stack x s)
    (if (eq? t x)
        x
      (comp-macroexpand-from-stack t s))))

(define (comp-macroexpand-1 x)
  (comp-macroexpand-1-from-stack x 0))

(define (comp-macroexpand x)
  (comp-macroexpand-from-stack x 0))

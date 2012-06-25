#!/usr/local/bin/gosh

(use file.util)
(use gauche.parseopt)
(require "./4.7")

(define (compile-file fn)
  (map (lambda (sexp)
         (comp sexp 0))
       (file->sexp-list fn)))

(define (run-code code)
  (dolist (x code)
    (run x 0)))

(define (dofile srcfn)
  (dolist (sexp (file->sexp-list srcfn))
    (evaluate sexp)))

(define (dostring str)
  (evaluate (read-from-string str)))

(define (write-compiled-code codes)
  (dolist (x codes)
    (write/ss x)
    (newline)))

(define (run-file srcfn)
  (run-code (file->sexp-list srcfn)))

(define (run-repl)
  (until (read) eof-object? => code
    (run code 0)))

(define (usage)
  (print "3imp scheme compiler.")
  (print "usage: 3imp [options] srcfn ...")
  (print "options:")
  (print "  -h,--help      disp help")
  (print "  -c,--compile   compile only")
  (print "  -r,--run       run compiled code")
  (print "  -e,--evaluate  evaluate string, write and exit")
  )

(define (main args)
  (let-args (cdr args)
            ((help?          "h|help")
             (compile-only?  "c|compile")
             (run?           "r|run")
             (estr           "e|evaluate=s")
             . restargs)
    (cond (help? (usage))
          (compile-only?
           (if estr
               (write-compiled-code (list (comp (read-from-string estr) 0)))
             (dolist (srcfn restargs)
               (let ((codes (compile-file srcfn)))
                 (write-compiled-code codes)))))
          (estr (dostring estr))
          ((null? restargs)
           (if run?
               (run-repl)
             (repl)))
          (else
           (let ((srcfn (car restargs))
                 (realargs (cdr restargs)))
             (cond (run? (run-file srcfn))
                   (else (dofile srcfn)))
             (let ((main (refer-global 'main (lambda () #f))))
               (when main
                 (vm-apply 0 main (list realargs))))))))
  0)

(use-modules (ice-9 match)
	     (oop goops)
	     (srfi srfi-26)
	     (djf fstruct)
	     )

(define (feval expr env)
  (if (pair? expr)
      (fapply (feval (car expr) env) expr env)
      (flookup expr env)))

(define-box <proc-env>)
					;(define-unit <lit-env> lit-env)
(define lit-env (make-box <proc-env> identity))
;(define-unit <lisp-base-env>)
(define lisp-base-env
  (make-box <proc-env>
	    (lambda (x)
	      (if (symbol? x)
		  (error "Unbound Variable:" x)
		  x))))

(define-generic flookup)
(define-method (flookup key (env <pair>))
  (if (equal? key (caar env))
      (cdar env)
      (flookup key (cdr env))))
(define-method (flookup key (env <null>))
  (error "Variable not found:" key))
(define-method (flookup key (env <proc-env>))
  ((unbox env) key))
;(define-method (flookup key (env <lit-env>)) key)

(define-generic fapply)
(define-method (fapply (f <procedure>) l env)
  (if (pair? l)
      (apply f (map (cut feval <> env) (cdr l)))
      f))
(define-method (fapply f l env) l)

(define-syntax procs->env
  (syntax-rules ()
    ((_) '())
    ((_ (key val) rest ...)
     `((key . ,val) . ,(procs->env rest ...)))
    ((_ f rest ...) (procs->env (f f) rest ...))))

(define r5rs-proc-env
  (procs->env  ; equivalence
              eqv? eq? equal?
	      ; numbers
	      number? complex? real? rational? integer? exact? inexact?
	      = < > <= >= zero? positive? negative? odd? even?
	      + - * quotient remainder modulo max min abs numerator denominator
	      gcd lcm floor ceiling truncate round rationalize expt
	      / exp log sin cos tan asin acos atan sqrt
	      make-rectangular make-polar real-part imag-part magnitude angle
	      exact->inexact inexact->exact
	      number->string string->number
	      ; booleans
	      not boolean?
	      ; pairs and lists
	      pair? cons car cdr set-car!
	      caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr
	      caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr cdaaar
	      cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr
	      null? list? list length append reverse list-tail list-ref
	      memq memv member assq assv assoc
	      ; symbols
              symbol? symbol->string string->symbol
	      ; characters
	      char? char=? char<? char>? char<=? char>=? char-ci=? char-ci<?
	      char-ci<=? char-ci>=? char-alphabetic? char-numeric?
	      char-whitespace? char-upper-case? char-lower-case? char->integer
	      integer->char char-upcase char-downcase
	      ; strings
	      string? make-string string string-length string-ref string-set!
	      string=? string>? string>? string<=? string>=? string-ci<?
	      string-ci>? string-ci<=? string-ci>=? substring string-append
	      string->list list->string string-copy string-fill!
	      ; vectors
	      vector? make-vector vector vector-length vector-ref vector-set!
	      vector->list list->vector vector-fill!
	      ; control features
	      procedure? apply map for-each force call-with-current-continuation
	      values call-with-values dynamic-wind
	      ; Eval
	      eval scheme-report-environment null-environment
	      interaction-environment
	      ; Ports
	      call-with-input-file call-with-output-file input-port?
	      output-port? current-input-port current-output-port
	      with-input-from-file with-output-to-file open-input-file
	      open-output-file close-input-port close-output-port
	      ; Input
	      read read-char peek-char eof-object? char-ready?
	      ; Output
	      write display newline write-char
	      ; System interface
	      load #;transcript-on #;transcript-off))

(define r5rs-base-env (append r5rs-proc-env lisp-base-env))

;(feval '(+ 2 2) `((+ . ,+) . ,lisp-base-env))
;(feval '(+ 2 2) lisp-base-env)
;(feval '(eval (list (string->symbol "+") 2 2) (scheme-report-environment 5)) r5rs-base-env)
;(feval '(+ 2 2) lit-env)

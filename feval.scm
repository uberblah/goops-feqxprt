(use-modules (ice-9 match)
	     (oop goops)
	     (srfi srfi-26)
	     (djf fstruct)
	     (srfi srfi-1)
	     )

(define (feval expr env)
  (if (pair? expr)
      (fapply (feval (car expr) env) expr env)
      (flookup expr env)))

(define-box <proc-env>)
					;(define-unit <lit-env> lit-env)
					;(define lit-env (make-box <proc-env> identity))
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
					;(define-method (fapply f l env) l)

(define-syntax procs->env
  (syntax-rules ()
    ((_) '())
    ((_ (key val) rest ...)
     (acons 'key val (procs->env rest ...)))
    ((_ f rest ...) (procs->env (f f) rest ...))))

(define r5rs-proc-env
  (procs->env ; equivalence
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
					; eval
   eval #;scheme-report-environment #;null-environment
   interaction-environment
					; ports
   call-with-input-file call-with-output-file input-port?
   output-port? current-input-port current-output-port
   with-input-from-file with-output-to-file open-input-file
   open-output-file close-input-port close-output-port
					; input
   read read-char peek-char eof-object? char-ready?
					; output
   write display newline write-char
					; system interface
   load #;transcript-on #;transcript-off))

(define r5rs-base-env (append r5rs-proc-env lisp-base-env))

(define-fstruct <fprocedure> code env)
(define-method (fapply (proc <fprocedure>) expr env)
  (match (fstruct->list proc)
    (((_ expr-arg env-arg body) inner-env)
     #;(feval (zip-args expr-args body) (acons env-arg env inner-env))
     (feval body (acons expr-arg expr (acons env-arg env inner-env))))))

(define quote-env
  (make-box <proc-env>
	    (lambda (x)
	      (make-fstruct <fprocedure>
			    '(flambda expr env expr)
			    lit-env))))

(define (make-closure args body env)
  (define (zip-args args in-expr env)
    (match (list args in-expr)
      (((aa . ad) (ea . ed)) (acons aa ea (zip-args ad ed env)))
      ((() ()) env)
      (((_ . _) _) (error "Too many arguments to closure"))
      ((() _) (error "Too few arguments to closure"))
      ((key val) (acons key val env))))
  (lambda x (feval body (zip-args args x env))))

(define (r5rs-valid-definition? expr)
  (match expr
    (('define (f . args) . _)
     (fold-right (lambda (x y) (and y (symbol? x))) #t args))
    (('define (? symbol? _) _) #t)
    (('begin . body) (every r5rs-valid-definition? body))
    (_ #f)))

(define (r5rs-definition? expr)
  (match expr
    (('define . _) #t)
    (('begin . body) (every r5rs-definition? body))
    (_ #f)))

(define (r5rs-transform-body body)
  (define (get-defs def prev-defs)
    (match def
      (('define (f . args) . body)
       `((,f (lambda ,args ,(r5rs-transform-body body))) . ,prev-defs))
      (('define var val) `((,var ,val) . ,prev-defs))
      (('begin . defs) (fold get-defs prev-defs defs))))
  (define (rec defs body)
    (match body
      ((a . b)
       (cond ((r5rs-valid-definition? a) (rec (get-defs a defs) b))
	     ((r5rs-definition? a) (error "Invalid R5RS definition:" a))
	     ((null? defs) `(begin . ,body))
	     (else `(letrec ,(reverse defs) (begin . ,body)))))))
  (rec '() body))

					; derived expressions: cond case and or let let* letrec begin do delay quasiquote
(define (syntax-rules-proc expr env body)
  (define (match-pattern pattern expr lits)
    (cond ((member pattern lits) (and (equal? expr lits) '()))
	  ((symbol? pattern) `((,pattern . ,expr)))
	  ((vector? pattern)
	   (and (vector? expr)
		(match-pattern (vector->list pattern)
			       (vector->list expr)
			       lits)))
	  ((not (pair? pattern))
	   (and (equal? expr pattern) '()))
	  (else
	   (match (list pattern expr)
	     (((p (? (cut eq? <> '...) pattern)) e) ; match bug?
	      (match-ellipsis p e lits))
	     (((pa . pb) (ea . eb))
	      (let ((a (match-pattern pa ea lits))
		    (b (match-pattern pb eb lits)))
		(and a b (append a b))))
	     (_ #f)))))
  (define (match-ellipsis p e lits)
    (define (transpose l) (apply map list l))
    (let ((m (map (cut match-pattern p <> lits) e)))
      (and (every identity m)
	   (let ((vars (map (lambda (x) (cons (car x) '...)) (car m)))
		 (vals (transpose (map (cut map cdr <>) m))))
	     (map cons vars vals)))))
  (match body
    ((_ lits . rules) (match-pattern (caar rules) expr lits))))

#|
(feval '(+ 2 2) `((+ . ,+) . ,lisp-base-env))
(feval '(+ 2 2) lisp-base-env) ; this is supposed to yield an error
(feval '(eval (list (string->symbol "+") 2 2) (scheme-report-environment 5)) r5rs-base-env)
(feval '(+ 2 2) quote-env)
((make-closure 'x '(apply + x) r5rs-base-env) 1 2 3 4 5)
(r5rs-transform-body '((begin (define a b)) (define (b) c) expr1 (expr2)))
(r5rs-transform-body '(expr))
(syntax-rules-proc '(1 2 3) 5 '(syntax-rules () ((_ (a b))) ()))
(syntax-rules-proc '(1 2 3) 5 '(syntax-rules () ((_ a ...) (list a ...))))
(syntax-rules-proc '(alist-alist 0 (1 2 3) (4 5 6) (7 8 9)) r5rs-base-env '(syntax-rules () ((_ beg (var val ...) ...) (list (list beg var val ...) ...))))

(define-syntax-rule (alist-alist beg (var val ...) ...) (list (list beg var val ...) ...))
(alist-alist 0 (1 2 3) (4 5 6) (7 8 9))

(feval `(,+ (2) (() 2)) quote-env)
|#

(include "feval.scm") ; TODO: Make modules
(use-modules (srfi srfi-1)
             (srfi srfi-26)
             (djf fstruct)
             (oop goops)
             (ice-9 match)
             ;(feval)
             )

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

#|
; halting work on syntax-rules, see notes/r5rs

(define (sr-ell-form form)
  (and (pair? form)
       (pair? (cdr form))
       (null? (cddr form))
       (equal? (cadr form) '...)))

(define (sr-check pattern template lits)
  (define (get-vars pattern)
    (cond
     ((member pattern lits) '())
     ((symbol? pattern) (list pattern))
     ((vector? pattern) (get-vars (vector->list pattern)))
     ((pair? pattern)
      (match pattern
	((a (? (cut equal? <> '...) _))
	 (map (cut cons <> '...) (get-vars a)))
	((a . b)
	 (append (get-vars a) (get-vars b)))))
     (else '())))
  (define (check-vars vars prev)
    (match vars
      (() #t)
      (((var . '...) . rest) (check-vars `(,var . ,rest) prev))
      ((var . rest) (and (not (member var rest))
			 (check-vars rest (cons var prev))))
      (_ #f)))
  (define (check-template template vvars evars ivars)
    (cond
     ((vector? template)
      (check-template (vector->list template) vvars evars ivars))
     ((sr-ell-form template) =>
      (cut check-template <> vvars
	   (map car (filter pair? evars))
	   (append (filter (negate pair?) evars) ivars)))
     ((pair? template)
      (and (check-template (car template) vvars evars ivars)
	   (check-template (cdr template) vvars evars ivars)))
     (else (or (member template vvars)
	       (member template evars)
	       (not (member template ivars))))))
  (let ((vars (get-vars pattern)))
    (cond ((not (check-vars vars '()))
	   (error "Duplicate variables in pattern" pattern))
	  ((check-template template
			   (filter (negate pair?) vars)
			   (filter pair? vars)
			   ivars))
	  (else (error "Incompatible ellipsis between pattern and template"
		       (cons pattern template))))))

(define (sr-matcher pattern lits)
  (define (ellipsis-matcher inner-pattern)
    (define (transpose l) (apply map list l))
    (define l (sr-matcher inner-pattern))
    (lambda (expr)
      (let ((m (map l expr)))
        (and (every identity m)
             (let ((vars (map (lambda (x) (cons (car x) '...)) m))
                   (vals (transpose (map cdr m))))
               (map cons vars vals))))))
  (cond
   ((member pattern lits) (const '()))
   ((symbol? pattern) (cut acons pattern <> '()))
   ((vector? pattern)
    (let ((l (sr-matcher (vector->list pattern) lits)))
      (lambda (x)
        (and (vector? x) (l (vector->list x))))))
   ((sr-ell-form pattern) => ellipsis-matcher)
   ((pair? pattern)
    (let ((la (sr-matcher (car pattern) lits))
	  (lb (sr-matcher (cdr pattern) lits)))
         (lambda (x)
           (let ((va (la (car x))) (vb (lb (cdr x))))
             (and va vb (append va vb))))))
   (else (lambda (x) (and (equal? x pattern) '())))))

(define (sr-expander template binds)
  (define (ell? x) (equal? x '...))
  (define (rec template vbinds ebinds einvalid)
    (cond
     ((symbol? template)
      (let ((a (assoc template vbinds)))
	(if a (cdr a) template)))
     ((vector? template)
      (list->vector (rec (vector->list template) vbinds ebinds)))
     ((sr-ell-form template)
      (rec template vbinds
	   (map (lambda (x) (cons (caar x) (cdr x)))
		(filter (compose pair? car) ebinds))
	   (append (filter (compose (negate pair?) car) ebinds)
		   vbinds)))
     ((pair? template)
      (cons (rec (car template) vbinds ebinds einvalid)
	    (rec (cdr template) vbinds ebinds einvalid)))))
  (rec template vbinds ebinds '()))
|#

; R5RS derived expressions: cond case and or let let* letrec begin do delay quasiquote

#|
(r5rs-transform-body '((begin (define a b)) (define (b) c) expr1 (expr2)))
(r5rs-transform-body '(expr))
(syntax-rules-proc '(1 2 3) 5 '(syntax-rules () ((_ (a b))) ()))
(syntax-rules-proc '(1 2 3) 5 '(syntax-rules () ((_ a ...) (list a ...))))
(syntax-rules-proc '(alist-alist 0 (1 2 3) (4 5 6) (7 8 9)) r5rs-base-env '(syntax-rules () ((_ beg (var val ...) ...) (list (list beg var val ...) ...))))

(define-syntax-rule (alist-alist beg (var val ...) ...) (list (list beg var val ...) ...))
(alist-alist 0 (1 2 3) (4 5 6) (7 8 9))
|#

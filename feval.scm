;(define-module (feval)) ; TODO

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

(define-generic fapply)
(define-method (fapply (f <procedure>) l env)
  (if (pair? l)
      (apply f (map (cut feval <> env) (cdr l)))
      f))

(define-syntax binds->env
  (syntax-rules ()
    ((_) '())
    ((_ (key val) rest ...)
     (acons 'key val (procs->env rest ...)))
    ((_ f rest ...) (procs->env (f f) rest ...))))

(define-fstruct <fprocedure> code env)
(define-method (fapply (proc <fprocedure>) expr env)
  (match (fstruct->list proc)
    (((_ expr-arg env-arg body) inner-env)
     (feval body (acons expr-arg expr (acons env-arg env inner-env))))))

(define lit-env (make-box <proc-env> identity))

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
(feval `(,+ (2) (() 2)) quote-env)
|#

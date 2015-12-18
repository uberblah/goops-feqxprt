(use-modules (ice-9 match)
	     (oop goops)
	     (srfi srfi-26)
	     )

(define (feval expr env)
  (define item
    (if (pair? expr)
	(feval (car expr) env)
	expr))
  (fapply (flookup item env) expr env))

(define-generic flookup)
(define-method (flookup key (env <list>))
  (if (symbol? key)
      (or (assoc-ref env key) (error "Key not in env:" key env))
      key))

(define-generic fapply)
(define-method (fapply (f <procedure>) l env)
  (if (pair? l)
      (apply f (map (cut feval <> env) (cdr l)))
      f))
(define-method (fapply f l env) l)

;(feval '(+ 2 2) `((+ . ,+)))

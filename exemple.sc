;;; examples of passing along threaded information.

;;; Try (collect-symbols '(if (x y 'a 'c zz) 'b 'c))
;;; Note that it commonizes the reference to c. 

(define-syntax with-values
  (syntax-rules ()
    ((_ P C) (call-with-values (lambda () P) C))))
(define collect-symbols
  (lambda (exp)
    (with-values (collect-symbols-help exp)
      (lambda (symbol-decls exp)
        (match symbol-decls
          (((,symbol-name . ,symbol-var) ...)
           `(let ((,symbol-var (quote ,symbol-name)) ...) ,exp)))))))
(define collect-symbols-help
  (lambda (exp)
    (let ((symbol-env '()))
      (match+ (symbol-env) exp
        (,x
          (guard (symbol? x))
          (values symbol-env x))
        ((quote ,x)
         (guard (symbol? x))
         (let ((pair/false (assq x symbol-env)))
           (if pair/false
               (values symbol-env (cdr pair/false))
               (let ((v (gensym)))
                 (values (cons (cons x v) symbol-env)
                         v)))))
        ((quote ,x)
         (values symbol-env `(quote ,x)))
        ((if ,[t] ,[c] ,[a])
         (values symbol-env `(if ,t ,c ,a)))
        ((,[op] ,[arg] ...)
         (values symbol-env `(,op ,arg ...)))))))

;;; the grammar for this one is just if-exprs and everything else

(define collect-leaves
  (lambda (exp acc)
    (match+ (acc) exp
      ((if ,[] ,[] ,[])
       acc)
      ((,[] ,[] ...)
       acc)
      (,x
        (cons x acc)))))

;; here's something that takes apart quoted stuff. 

(define destruct
  (lambda (datum)
    (match datum
      (() `'())
      ((,[X] . ,[Y])`(cons ,X ,Y))
      (#(,[X] ...) `(vector ,X ...))
      (,thing
        (guard (symbol? thing))
        `',thing)
      (,thing
        thing))))

;; examples using explicit Catas

(define sumsquares
  (lambda (ls)
    (define square 
      (lambda (x)
        (* x x)))
    (match ls 
      [(,[a*] ...) (apply + a*)]
      [,[square -> n] n])))

(define sumsquares
  (lambda (ls)
    (define square 
      (lambda (x)
        (* x x)))
    (let ([acc 0])
      (match+ (acc) ls 
        [(,[] ...) acc]
        [,[(lambda (acc x) (+ acc (square x))) ->] acc]))))

;;; The following uses explicit Catas to parse programs in the
;;; simple language defined by the grammar below

;;; <Prog> -> (program <Stmt>* <Expr>)
;;; <Stmt> -> (if <Expr> <Stmt> <Stmt>)
;;;         | (set! <var> <Expr>)
;;; <Expr> -> <var>
;;;         | <integer>
;;;         | (if <Expr> <Expr> <Expr>)
;;;         | (<Expr> <Expr*>)

(define parse
  (lambda (x)
    (define Prog
      (lambda (x)
        (match x
          [(program ,[Stmt -> s*] ... ,[Expr -> e])
           `(begin ,s* ... ,e)]
          [,other (error 'parse "invalid program ~s" other)])))
    (define Stmt
      (lambda (x)
        (match x
          [(if ,[Expr -> e] ,[Stmt -> s1] ,[Stmt -> s2])
           `(if ,e ,s1 ,s2)]
          [(set! ,v ,[Expr -> e])
           (guard (symbol? v))
           `(set! ,v ,e)]
          [,other (error 'parse "invalid statement ~s" other)])))
    (define Expr
      (lambda (x)
        (match x
          [,v (guard (symbol? v)) v]
          [,n (guard (integer? n)) n]
          [(if ,[e1] ,[e2] ,[e3])
           `(if ,e1 ,e2 ,e3)]
          [(,[rator] ,[rand*] ...) `(,rator ,rand* ...)]
          [,other (error 'parse "invalid expression ~s" other)])))
    (Prog x)))
;;; (parse '(program (set! x 3) (+ x 4)))) => (begin (set! x 3) (+ x 4))

;; CHANGELOG

;; [31 January 2010]
;; rkd replaced _ with k in the syntax-case patterns for match, match+,
;; etc., since in R6RS, _ is not a pattern variable.

;; [31 January 2010]
;; rkd renamed syntax-object->datum and datum->syntax-object to their
;; R6RS names syntax->datum and datum->syntax.  also replaced the
;; literal-identifier=? calls with free-identifier=? calls.

;; [3 February 2008]
;; rkd modified overloaded quasiquote to handle expressions followed
;; by more than one ellipsis.

;; [3 February 2008]
;; aziz modified mapper to quote the inserted empty lists

;; [3 March 2007]
;; aziz minor change to eagerly catch malformed clauses (e.g. a clause
;; that's not a list of 2 or more subforms).

;; [13 March 2002]
;; rkd added following change by Friedman and Ganz to the main source
;; code thread and fixed a couple of minor problems.

;; [9 March 2002]
;; Dan Friedman and Steve Ganz added the ability to use identical pattern
;; variables.  The patterns represented by the variables are compared
;; using the value of the parameter match-equality-test, which defaults
;; to equal?.
;;
;; > (match '(1 2 1 2 1)
;;     [(,a ,b ,a ,b ,a) (guard (number? a) (number? b)) (+ a b)])
;; 3
;; ;;
;; > (match '((1 2 3) 5 (1 2 3))
;;     [((,a ...) ,b (,a ...)) `(,a ... ,b)])
;; (1 2 3 5)
;; ;;
;; > (parameterize ([match-equality-test (lambda (x y) (equal? x (reverse y)))])
;;     (match '((1 2 3) (3 2 1))   
;;       [(,a ,a) 'yes]
;;       [,oops 'no]))
;; yes

;; [10 Jan 2002]
;; eh fixed bug that caused (match '((1 2 3 4)) (((,a ... ,d) . ,x) a)) to
;; blow up.  The bug was caused by a bug in the sexp-dispatch procedure
;; where a base value empty list was passed to an accumulator from inside
;; the recursion, instead of passing the old value of the accumulator.

;; [14 Jan 2001]
;; rkd added syntax checks to unquote pattern parsing to weed out invalid
;; patterns like ,#(a) and ,[(vector-ref d 1)].

;; [14 Jan 2001]
;; rkd added ,[Cata -> Id* ...] to allow specification of recursion
;; function.  ,[Id* ...] recurs to match; ,[Cata -> Id* ...] recurs
;; to Cata.

;; [14 Jan 2001]
;; rkd tightened up checks for ellipses and nested quasiquote; was comparing
;; symbolic names, which, as had been noted in the source, is a possible
;; hygiene bug.  Replaced error call in guard-body with syntax-error to
;; allow error to include source line/character information.

;; [13 Jan 2001]
;; rkd fixed match patterns of the form (stuff* ,[x] ... stuff+), which
;; had been recurring on subforms of each item rather than on the items
;; themselves.

;; [29 Feb 2000]
;; Fixed a case sensitivity bug.

;; [24 Feb 2000]
;; Matcher now handles vector patterns.  Quasiquote also handles
;; vector patterns, but does NOT do the csv6.2 optimization of
;; `#(a 1 ,(+ 3 4) x y) ==> (vector 'a 1 (+ 3 4) 'x 'y).
;; Also fixed bug in (P ... . P) matching code. 

;; [23 Feb 2000]
;; KSM fixed bug in unquote-splicing inside quasiquote.

;; [10 Feb 2000]
;; New forms match+ and trace-match+ thread arguments right-to-left.
;; The pattern (P ... . P) now works the way you might expect.
;; Infinite lists are now properly matched (and not matched).
;; Removed the @ pattern.
;; Internal: No longer converting into syntax-case. 

;; [6 Feb 2000]
;; Added expansion-time error message for referring to cata variable
;; in a guard.

;; [4 Feb 2000]
;; Fixed backquote so it can handle nested backquote (oops).
;; Double-backquoted elipses are neutralized just as double-backquoted
;; unquotes are.  So:
;;   `(a ,'(1 2 3) ... b)    =eval=> (a 1 2 3 b)
;;   ``(a ,'(1 2 3) ... b)   =eval=> `(a ,'(1 2 3) ... b)
;;   ``(a ,(,(1 2 3) ...) b) =eval=> `(a ,(1 2 3) b)
;; Added support for
;;   `((unquote-splicing x y z) b) =expand==> (append x y z (list 'b))

;; [1 Feb 2000]
;; Fixed a bug involving forgetting to quote stuff in the revised backquote.
;; Recognized unquote-splicing and signalled errors in the appropriate places.
;; Added support for deep elipses in backquote.
;; Rewrote backquote so it does the rebuilding directly instead of
;; expanding into Chez's backquote. 

;; [31 Jan 2000]
;; Kent Dybvig fixed template bug.

;; [31 Jan 2000]
;; Added the trace-match form, and made guards contain
;; an explicit and expression:
;;    (guard E ...) ==> (guard (and E ...))

;; [26 Jan 2000]
;; Inside the clauses of match expressions, the following
;; transformation is performed inside backquote expressions:
;;    ,v ...      ==> ,@v
;;    (,v ,w) ... ==> ,@(map list v w)
;;    etc.

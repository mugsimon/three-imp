(define-syntax rec
  (syntax-rules ()
    ((rec var exp)
     (let ((var '()))
       (set! var exp)))))

(define-syntax recur
  (syntax-rules ()
    ((recur f ((var init) ...) exp ...)
     ((rec f (lambda (var ...) exp ...))
      init ...))))

(define-syntax record
  (syntax-rules ()
    ((record (var ...) val exp ...)
     (apply (lambda (var ...) exp ...) val))))

(define-syntax record-case
  (syntax-rules ()
    ((record-case exp1
		  [key vars exp2 ...]
		  ...
		  [else exp3 ...])
     (let ((r exp1))
       (cond ((eq? (car r) 'key)
	      (record vars (cdr r) exp2 ...))
	     ...
	     (else exp3 ...))))))

(define extend
  (lambda (e r)
    (cons r e)))

(define functional
  (lambda (body e)
    (list body e)))

(define stack (make-vector 1000))

(define index ;; スタックのトップからi番目を参照 0ベース
  (lambda (s i)
    (vector-ref stack (- (- s i) 1))))

(define push 
  (lambda (x s) 
    (vector-set! stack s x) 
    (+ s 1)))

(define index-set!
  (lambda (s i v)
    (vector-set! stack (- (- s i) 1) v)))

(define find-link ;; n回静的リンクをたどる
  (lambda (n e)
    (if (= n 0)
        e
        (find-link (- n 1) (index e -1)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions for debug
(define c.scm:VM-debug
  (lambda (a x e s)
    (print "a:" a)
    (print "x:" x)
    (print "e:" e)
    (print "s:" s)
    (c.scm:stack-print s)
    (print "----------------------")))

(define c.scm:stack-print
  (lambda (s)
    (display "stack:")
    (display "[")
    (if (= s 0)
	(print "]")
	(let loop ((i (- s 1)))
	  (if (= i 0)
	      (print (vector-ref stack i) "]")
	      (begin (display (vector-ref stack i))
		     (display "][")
		     (loop (- i 1))))))))

(define c.scm:compile-debug
  (lambda (x e next)
    (print "x:" x)
    (print "e:" e)
    (print "next:" next)
    (print "-----------------")))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compile-lookup
  (lambda (var e return)
    (if (null? e)
	(c.scm:error "unbound variable" var)
	(recur nxtrib ([e e] [rib 0])
	       (if (null? e)
		   (c.scm:error "unbound variable" var)
		   (recur nxtelt ([vars (car e)] [elt 0])
			  (cond 
			   [(null? vars)	
			    (nxtrib (cdr e) (+ rib 1))]
			   [(eq? (car vars) var)
			    (return rib elt)] ;;(refer n m)
			   [else
			    (nxtelt (cdr vars) (+ elt 1))])))))))

(define (define-lookup var e x next)
  (cond ((not (eq? (car next) 'halt))
	 (c.scm:error "syntax-error"
		      "the form is only allowed in toplevel"
		      x))
	((null? e)
	 (extend-*groval-environment* var))
	(else
	 (recur nxtelt ([vars (car e)] [elt 0])
		(cond
		 [(null? vars)
		  (extend-*groval-environment* var)]
		 [(eq? (car vars) var)
		  #t]
		 [else
		  (nxtelt (cdr vars) (+ elt 1))])))))

(define (extend-*groval-environment* var)
  (set! *global-environment* (list (cons var (car *global-environment*))))
  (set! *stack-pointer* (+ *stack-pointer* 1)))

(define compile 
  (lambda (x e next)
    (when *debug-mode*
	  (c.scm:compile-debug x e next)) ;;debug
    (cond 
     [(symbol? x) 
      (compile-lookup x e 
		      (lambda (n m)
			(list 'refer n m next)))]
     [(pair? x)
      (record-case x 
		   [quote (obj)
			  (list 'constant obj next)]
		   [lambda (vars body)
		     (list 'close
			   (compile body 
				    (extend e vars)
				    (list 'return (+ (length vars) 1)))
			   next)]
		   [if (test then else)
		       (let ([thenc (compile then e next)]
			     [elsec (compile else e next)])
			 (compile test e (list 'test thenc elsec)))]
		   [set! (var x)
			 (compile-lookup var e
					 (lambda (n m) (compile x e (list 'assign n m next))))]
		   [define (var val)
		     (define-lookup var e x next)
		     (compile (list 'set! var val) *global-environment* next)]
		   [else
		    (recur loop ([args (cdr x)]
				 [c (compile (car x) e '(apply))])
			   (if (null? args)
			       (list 'frame next c)
			       (loop (cdr args)
				     (compile (car args)
					      e 
					      (list 'argument c)))))])]
     [else (list 'constant x next)])))

(define VM 
  (lambda (a x e s)
    (when *debug-mode*
	  (c.scm:VM-debug a x e s)) ;;debug code
    (record-case x
		 [halt ()
		       a]
		 [refer (n m x) ;;(index s i)
			;(print "refer") ;;debug
			;(print "s:" s "i:" (find-link n e)) ;;debug
			(VM (index (find-link n e) m) x e s)]
		 [constant (obj x)
			   ;(print "constant")
			   (VM obj x e s)]
		 [close (body x)
			;(print "close")
			(VM (functional body e) x e s)]
		 [test (then else)
		       ;(print "test")
		       (VM a (if a then else) e s)]
		 [assign (n m x)
					;(print "assign")
			 (index-set! (find-link n e) m a)
			 (VM a x e s)]
		 [frame (ret x)
			;(print "frame")
			(VM a x e (push ret (push e s)))]
		 [argument (x)
			   ;(print "argument")
			   (VM a x e (push a s))]
		 [apply ()
			;(print "apply")
			(VMapply a x e s)]
		 [return (n) ;;n=[args]+[static link]
			 ;(print "return")
			 (let ([s (- s n)])
			   (VM a (index s 0) (index s 1) (- s 2)))]
		 [else
		  (print "Unknown VM instruction")
		  a])))

(define (VMapply a x e s)
  (if (primitive? a)
      (let ((a (apply-primitive a s))
	    (x (make-return-instruction a)))
	(VM a x e s))      
      (record (body link) a
	      (VM a body s (push link s)))))

(define (primitive? a)
  (eq? (car a) 'primitive))

(define (apply-primitive a s)
  (let ((func (cadr a))
	(args (primitive-args s (caddr a))))
    (print "args:" args) ;;debug
    (apply func args)))

(define (primitive-args s n)
  (if (= n 0)
      '()
      (let loop ((args '())
		 (i (- n 1)))
	(if (= i 0)
	    (cons (index s i) args)
	    (loop (cons (index s i) args) (- i 1))))))

(define (VMinstruction? x)
  (memq (car x)
	'(halt refer constant close test assign frame argument apply return)))

(define (make-return-instruction a)
  (let ((n (caddr a)))
    (list 'return n)))

(define *top-level-continuation* #f)

(define c.scm:read-eval-print
  (lambda (cont)
    (set! *top-level-continuation* cont)
    (c.scm:prompt)
    (print (evaluate (read)))
    #t))

(define c.scm:prompt
  (lambda ()
    (display "c.scm> ")
    (flush)))

(define c.scm:error
  (lambda msg
    (display "C.SCM ERROR")
    (let loop ((msg msg))
      (if (null? msg)
	  (begin (newline)
		 (*top-level-continuation* #t))
	  (begin (display ": ")
		 (display (car msg))
		 (loop (cdr msg)))))))

(define *stack-pointer* 0)
(define *global-environment* '())
(define *debug-mode* #t)

(define initialize
  (lambda ()
    (set! *stack-pointer* 0)
    (set! *global-environment* '())
    (set! *global-environment*
	  (extend *global-environment* '(#;fact + - * = exit)))
    (for-each add-primitive (reverse (list #;(cons 'fact 1) (cons + 2) (cons - 2) (cons * 2) (cons = 2)
					   (cons c.scm:exit 0))))))

(define (add-primitive primitive-procedure)
  (let ((primitive-procedure
	 (make-primitive (car primitive-procedure)
			 (cdr primitive-procedure))))
    (set! *stack-pointer*
	  (push primitive-procedure
		*stack-pointer*))))

(define (make-primitive primitive-procedure n)
  (list 'primitive primitive-procedure n))

(define (c.scm:exit)
  (*top-level-continuation* #f))

(define c.scm
  (lambda ()
    (initialize)
    (let loop ()
      (if (call/cc c.scm:read-eval-print)
	  (loop)
	  (print "bye")))))

(define c.scm:read-eval-print
  (lambda (cont)
    (set! *top-level-continuation* cont)
    (c.scm:prompt)
    (print (evaluate (read)))
    #t))

(define evaluate
  (lambda (x)
    (VM '()
	(compile x *global-environment* '(halt))
	*stack-pointer*
	*stack-pointer*)))

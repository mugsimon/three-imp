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

(define compile-lookup
  (lambda (var e return)
    (recur nxtrib ([e e] [rib 0])
      (recur nxtelt ([vars (car e)] [elt 0])
        (cond 
          [(null? vars) (nxtrib (cdr e) (+ rib 1))]
          [(eq? (car vars) var) (return rib elt)]
[else (nxtelt (cdr vars) (+ elt 1))])))))

(define functional
  (lambda (body e)
    (list body e)))

(define compile 
  (lambda (x e next)
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

(define stack (make-vector 1000))

(define index ;; スタックのトップからi番目を参照
  (lambda (s i)
    (vector-ref stack (- (- s i) 1))))

(define push 
  (lambda (x s) 
    (vector-set! stack s x) 
    (+ s 1)))

(define index-set!
  (lambda (s i v)
    (vector-set! stack (- (- s i) 1) v)))

(define VM 
  (lambda (a x e s)
    (record-case x
		 [halt ()
		       a]
		 [refer (n m x)
			(VM (index (find-link n e) m) x e s)]
		 [constant (obj x)
			   (VM obj x e s)]
		 [close (body x)
			(VM (functional body e) x e s)]
		 [test (then else)
		       (VM a (if a then else) e s)]
		 [assign (n m x)
			 (index-set! (find-link n e) m a)
			 (VM a x e s)]
		 [frame (ret x)
			(VM a x e (push ret (push e s)))]
		 [argument (x)
			   (VM a x e (push a s))]
		 [apply ()
			(record (body link) a
				(VM a body s (push link s)))]
		 [return (n) ;;n=[args]+[static link]
			 (let ([s (- s n)])
			   (VM a (index s 0) (index s 1) (- s 2)))])))

(define find-link
  (lambda (n e)
    (if (= n 0)
        e
        (find-link (- n 1) (index e -1)))))

(define evaluate
  (lambda (x)
    (VM '() (compile x '() '(halt)) 0 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    (if (= s 0)
	(print)
	(let loop ((i (- s 1)))
	  (if (= i 0)
	      (print (vector-ref stack i))
	      (begin (display (vector-ref stack i))
		     (display " ")
		     (loop (- i 1))))))))

(define repl
  (lambda ()
    (call/cc
     (lambda (quit)
       (let loop ()
	 (display "stack-base> ")
	 (flush)
	 (let ((input (read)))
	   (if (eq? input 'exit)
	       (quit 'bye)
	       (begin (print (evaluate input))
		      (loop)))))))))

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

(define c.scm
  (lambda ()
    (let loop ()
      (if (call/cc c.scm:read-eval-print)
	  (loop)
	  (print "bye")))))

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
			  

(define compile-lookup
  (lambda (var e return)
    (if (null? e)
	(c.scm:error "Unbound variable" var)
	(recur nxtrib ([e e] [rib 0])
	       (if (null? e)
		   (c.scm:error "Unbound variable" var)
		   (recur nxtelt ([vars (car e)] [elt 0])
			  (cond 
			   [(null? vars)	
			    (nxtrib (cdr e) (+ rib 1))]
			   [(eq? (car vars) var)
			    (return rib elt)] ;;(refer n m)
			   [else
			    (nxtelt (cdr vars) (+ elt 1))])))))))

(define VM 
  (lambda (a x e s)
    (c.scm:VM-debug a x e s) ;;debug code
    (record-case x
		 [halt ()
		       (print "halt")
		       a]
		 [refer (n m x) ;;(index s i)
			(print "refer")
			(VM (index (find-link n e) m) x e s)]
		 [constant (obj x)
			   (print "constant")
			   (VM obj x e s)]
		 [close (body x)
			(print "close")
			(VM (functional body e) x e s)]
		 [test (then else)
		       (print "test")
		       (VM a (if a then else) e s)]
		 [assign (n m x)
			 (print "assign")
			 (index-set! (find-link n e) m a)
			 (VM a x e s)]
		 [frame (ret x)
			(print "frame")
			(VM a x e (push ret (push e s)))]
		 [argument (x)
			   (print "argument")
			   (VM a x e (push a s))]
		 [apply ()
			(print "apply")
			(record (body link) a
				(if (primitive? body)
				    (VM (apply-primitive link (primitive-args s (- s e 3)))
					(list 'return (length (primitive-args s (- s e 3))))
				        e
					s)
				    (VM a body s (push link s))))]
		 [return (n) ;;n=[args]+[static link]
			 (print "return")
			 (let ([s (- s n)])
			   (VM a (index s 0) (index s 1) (- s 2)))]
		 [else
		  (print "Unknown VM instruction")
		  a])))

(define c.scm:compile-debug
  (lambda (x e next)
    (print "x:" x)
    (print "e:" e)
    (print "next:" next)
    (print "-----------------")))

(define compile 
  (lambda (x e next)
    (c.scm:compile-debug x e next) ;;debug
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

(define *stack-pointer* 0)
(define *frame-pointer* 0)
(define *global-environment* '())

(define initialize
  (lambda ()
    (set! *stack-pointer* 0)
    (set! *global-environment* '())
    (let ((vars '(+)))
      (set! *global-environment* (extend *global-environment* vars))
      (for-each add-primitive vars))))

(define add-primitive
  (lambda (primitive-procedure)
    (set! *stack-pointer* (push (list 'primitive primitive-procedure) *stack-pointer*))))

(define (primitive? x)
  (eq? x 'primitive))

(define (primitive-args s i)
  (let loop ((args '())
	     (i (- i 1)))
    (if (zero? i)
	(cons (index s i) args)
	(loop (cons (index s i) args) (- i 1)))))

(define (apply-primitive body link)
  (let ((func (cadr body))
	(args (primitive-args link)))
    (apply func args)))

(define (apply-primitive func args)
  (let ((func (primitive-func func)))
    (print func)
    (print args)
    (apply func args)))

(define (primitive-func func)
  (case func
    ((+) +)))


    
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
    (VM '() (compile x *global-environment* '(halt)) *stack-pointer* *stack-pointer*)))

#|
(define compile-define-lookup
  (lambda (var e return)
    (if (null? e)
	(c.scm:error "c.scm:error - Unbound variable")
	(recur nxtrib ([e e] [rib 0])
	       (if (null? e)
		   (c.scm:error "c.scm:error - Unbound variable")
		   (recur nxtelt ([vars (car e)] [elt 0])
			  (cond 
			   [(null? vars)	
			    (nxtrib (cdr e) (+ rib 1))]
			   [(eq? (car vars) var)
			    (return rib elt)]
			   [else
			    (nxtelt (cdr vars) (+ elt 1))])))))))

|#

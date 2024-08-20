#lang racket/base

(require
 yosys/meta
 "../driver.rkt"
 "../circuit.rkt"
 "../spec.rkt"
 "../result.rkt"
 "../driver/interpreter.rkt"
 "checker.rkt"
 "hint.rkt"
 (only-in racket/class new send)
 (prefix-in @ (combine-in rosette/safe rosutil/addressable-struct rosutil/convenience))
 (only-in racket build-list))

(provide verify-timing)

(define (verify-timing
         spec
         circuit
         driver
         #:R R
         #:hints [hints (lambda (method c1 f1 f-out f2) (make-hintdb))]
         #:onlyA [only-methodA #f] ; method name or 'init or 'idle
         #:onlyB [only-methodB #f]
         #:override-args [override-args #f]
         #:override-f1 [override-f1 #f]
         #:override-c1 [override-c1 #f]
         #:without-crashes [without-crashes #f]
         #:without-yield [without-yield #f]
         #:verbose [verbose #f])
  (@gc-terms!)
  (define crash+por (crash+power-on-reset circuit)) ; so we can re-use it
  ; (when (or (not only-method) (equal? only-method 'invariant))
  ;   (when verbose (printf "verifying invariant...\n"))
  ;   (verify-invariant circuit verbose)
  ;   (when verbose (printf "  done!\n")))
  ; (when (or (not only-method) (equal? only-method 'init))
  ;   (when verbose (printf "verifying init...\n"))
  ;   (verify-init spec circuit crash+por R verbose)
  ;   (when verbose (printf "  done!\n")))
  ; (when (or (not only-method) (equal? only-method 'idle))
  ;   (when verbose (printf "verifying idle...\n"))
  ;   (verify-idle spec circuit driver R verbose)
  ;   (when verbose (printf "  done!\n")))
  (for ([methodA (spec-methods spec)])
    (when (or (not only-methodA) (equal? only-methodA (method-descriptor-name methodA)))
      (for ([methodB (spec-methods spec)])
        (when (or (not only-methodB) (equal? only-methodB (method-descriptor-name methodB)))
          (when verbose (printf "verifying methods ~a and ~a~a...\n"
            (method-descriptor-name methodA)
            (method-descriptor-name methodB)
            (if without-crashes " (without crashes)" "")))
          (verify-method spec circuit crash+por driver R methodA methodB override-args override-f1 override-c1 without-crashes without-yield hints verbose)
          (when verbose (printf "  done!\n"))
        )
      ))))

(define (verify-method spec circuit crash+por driver R methodA methodB override-args override-f1 override-c1 without-crashes without-yield hints verbose)
  ;; set up method and arguments
  (define method-nameA (method-descriptor-name methodA))
  (define method-nameB (method-descriptor-name methodB))
  (define spec-fnA (method-descriptor-method methodA))
  (define spec-fnB (method-descriptor-method methodB))
  (define args-A
    (or override-args
        (for/list ([arg (method-descriptor-args methodA)])
          (define type (argument-type arg))
          (if (list? type)
            (for/list ([el type]
                       [i (in-naturals)])
              (@fresh-symbolic (format "~a[~a]" (symbol->string (argument-name arg)) i) el))
            (@fresh-symbolic (argument-name arg) (argument-type arg)))))) 
  (define args-B
    (or override-args
        (for/list ([arg (method-descriptor-args methodB)])
          (define type (argument-type arg))
          (if (list? type)
            (for/list ([el type]
                       [i (in-naturals)])
              (@fresh-symbolic (format "~a[~a]" (symbol->string (argument-name arg)) i) el))
            (@fresh-symbolic (argument-name arg) (argument-type arg)))))) 
  ;; trng
  (define trng-words-state-A
    (build-list (spec-max-trng-words spec) (lambda (i) (@fresh-symbolic 'trng-word (@bitvector (spec-trng-word-length spec))))))
  (define trng-words-state-B
    (build-list (spec-max-trng-words spec) (lambda (i) (@fresh-symbolic 'trng-word (@bitvector (spec-trng-word-length spec))))))
  ; Both executions share valid state
  (define trng-valid-state
    (build-list (spec-max-trng-words spec) (lambda (i) (@fresh-symbolic 'trng-delay @integer?))))
  ; (define trng-valid-state
  ;   (build-list (spec-max-trng-words spec) (lambda (i) 0)))
  ;; spec
  (define f1-A (or override-f1 ((spec-new-symbolic spec))))
  (define f-result-A 
    (if (spec-random spec)
      (@check-no-asserts ((@apply spec-fnA args-A) (rstate f1-A trng-words-state-A)) #:discharge-asserts #t)
      (@check-no-asserts ((@apply spec-fnA args-A) f1-A) #:discharge-asserts #t)))
  (define f-out-A (result-value f-result-A))
  (define f-state-A (result-state f-result-A))
  (define f2-A 
    (if (spec-random spec)
      (rstate-spec (result-state f-result-A))
      (result-state f-result-A)
      ))
  (define f1-B (or override-f1 ((spec-new-symbolic spec))))
  (define f-result-B 
    (if (spec-random spec)
      (@check-no-asserts ((@apply spec-fnB args-B) (rstate f1-B trng-words-state-B)) #:discharge-asserts #t)
      (@check-no-asserts ((@apply spec-fnB args-B) f1-B) #:discharge-asserts #t)))
  (define f-out-B (result-value f-result-B))
  (define f-state-B (result-state f-result-B))
  (define f2-B 
    (if (spec-random spec)
      (rstate-spec (result-state f-result-B))
      (result-state f-result-B)
      ))
  ;; circuit
  (define m (circuit-meta circuit))
  (define inv (meta-invariant m))
  (define c1-A (@update-fields (or override-c1 ((meta-new-symbolic m)))
                             (cons
                              ;; reset is de-asserted
                              (cons (circuit-reset-input-name circuit)
                                    (not (circuit-reset-input-signal circuit)))
                              ;; other inputs are idle
                              (driver-idle driver))))
  (define c1-B (@update-fields (or override-c1 ((meta-new-symbolic m)))
                             (cons
                              ;; reset is de-asserted
                              (cons (circuit-reset-input-name circuit)
                                    (not (circuit-reset-input-signal circuit)))
                              ;; other inputs are idle
                              (driver-idle driver))))
  ;; make sure reset line is de-asserted
  (define driver-expr-A (cons method-nameA (map (lambda (arg) (list 'quote arg)) args-A)))
  (define initial-interpreter-state-A
    (make-interpreter driver-expr-A (driver-bindings driver) c1-A m trng-words-state-A trng-valid-state (spec-random spec) (spec-trng-word-length spec) (circuit-trng-word circuit) (circuit-trng-req circuit) (circuit-trng-valid circuit)))
  (define local-hints-A (hints (cons method-nameA args-A) c1-A f1-A f-out-A f2-A))
  (define precondition-A (@check-no-asserts (@&& (R f1-A c1-A) (inv c1-A))))
  (define driver-expr-B (cons method-nameB (map (lambda (arg) (list 'quote arg)) args-B)))
  (define initial-interpreter-state-B
    (make-interpreter driver-expr-B (driver-bindings driver) c1-B m trng-words-state-B trng-valid-state (spec-random spec) (spec-trng-word-length spec) (circuit-trng-word circuit) (circuit-trng-req circuit) (circuit-trng-valid circuit)))
  (define local-hints-B (hints (cons method-nameB args-B) c1-B f1-B f-out-B f2-B))
  (define precondition-B (@check-no-asserts (@&& (R f1-B c1-B) (inv c1-B))))
  (define exc (new checker%
                   [initial-state-A initial-interpreter-state-A]
                   [initial-state-B initial-interpreter-state-B]
                   [hint-db-A local-hints-A]
                   [hint-db-B local-hints-B]
                   [precondition-A precondition-A]
                   [precondition-B precondition-B]
                   [without-yield without-yield]))
  (when verbose (send exc debug!))
  ;; run
  (define finished (send exc run!))
  finished)

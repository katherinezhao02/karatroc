#lang rosette/safe

(require rosutil)
(provide (struct-out result) (struct-out rstate))

;; ideal functionality functions are curried, and have type
;; `args ... -> state -> result`
;;
;; For example, a lockbox's store op could be defined as
;; `(define ((store value) state) ...)`, returning a result
(struct result (value state)
  #:transparent)

(addressable-struct rstate (spec trng)) ;; If we have a trng, then result-state is a rstate.
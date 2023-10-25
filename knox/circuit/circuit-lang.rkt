#lang rosette/safe

(require
 (only-in rosutil/addressable-struct addressable-struct)
 "../result.rkt"
 "../circuit.rkt"
 (for-syntax racket/base racket/syntax syntax/parse))

(provide
 (except-out (all-from-out rosette/safe) struct #%module-begin)
 (rename-out [addressable-struct struct]
             [$#%module-begin #%module-begin])
 (all-from-out "../result.rkt"))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_
      #:circuit import-path
      #:reset reset-input-name reset-input-signal:boolean
      #:persistent [persistent-input ...]
      #:init-zeroed [init-zeroed-field ...]
      (~optional (~seq #:init-with-val [[val-init-field init-value] ...] ) #:defaults ([(val-init-field 1) null] [(init-value 1) null])) )
     #:with circuit (format-id stx "circuit")
     #:with metadata (format-id stx "metadata")
     #'(#%module-begin
        (require (only-in import-path metadata))
        (define circuit
          (make-circuit
           metadata
           'reset-input-name
           reset-input-signal
           (list 'persistent-input ...)
           (list 'init-zeroed-field ...)
           (list
            (cons 'val-init-field init-value) ...) ))
        (provide circuit))]
    [(_ body ...) ; fallback, useful in e.g. submodules (like a test module)
     #'(#%module-begin body ...)]))

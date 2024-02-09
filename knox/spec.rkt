#lang racket/base

(provide
 (struct-out argument)
 (struct-out method-descriptor)
 (except-out (struct-out spec) spec)
 (rename-out [spec make-spec]))

(struct argument (name type))

(struct method-descriptor (method name args))

(struct spec
  (init ; value
   new-symbolic ; callable that returns a symbolic value
   methods ; list of method-descriptor
   leak ; #f or method descriptor
   random ; if the hsm uses a trng
   max-trng-bits ; max number of random bits used in a method
   trng-has-valid ; if the trng has a valid bit
   )) 

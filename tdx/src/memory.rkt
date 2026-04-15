; Translation of memory.bpl to rosette

#lang rosette

;********************* Memory *********************

; Haven't quite figured out how I can do records/types yet but for now they are integers
(define dummy_physical_address 0)
(define dummy_linear_address 0)
(define abort_page 0)

; Struct definition for linear range register:
(define-struct lr_register (lbase lsize))

; Constructor and getter methods shown below, fortunatley racket takes care of this
; (define test_lr (make-lr_register 2000 3000)) 
; (displayln (lr_register-lbase test_lr))
; (displayln (lr_register-lsize test_lr))

(define page_table (hash
    dummy_linear_address dummy_physical_address))

; Example reference:
; (displayln (hash-ref page_table dummy_linear_address))

; Can add mappigns to the table with: 
; (hash-set page_table 20 2)
; Modifies page_table with the updated map: 
;(displayln page_table)


; All enclave memory is either EPC memory or non-EPC memory
; The bounds are arbitrary
(define EPC_HIGH 3000)
(define EPC_LOW 2000)

(define (is_epc_address physical_address)
    (and (<= EPC_LOW physical_address) (> EPC_HIGH physical_address)))

; Test cases as found in memory_test.bpl
(clear-vc!) 
(assert (is_epc_address 2500))
(assert (not (is_epc_address 1000)))

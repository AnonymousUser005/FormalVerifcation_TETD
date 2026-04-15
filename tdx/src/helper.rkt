;Defining helper functions 
#lang rosette

;Defining physical address as integer type
(define-symbolic physical_address integer?)
;(physical_address 4)
(integer? physical_address)

;Defining data as integer type
(define-symbolic data integer?)

;Defining memory registers as a hash fucntion
(define mem_reg (hash physical_address data))
(hash-set mem_reg  20 2)
(displayln mem_reg)


;Interrupts


;Exits

;Exceptions
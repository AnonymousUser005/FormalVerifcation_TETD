#lang rosette
;;; address types
(define hpaddr (bitvector 64))
(define gpaddr (bitvector 64))
(define gvaddr (bitvector 32)) ;;; Not sure
(define word (bitvector 32))

;; Constants and Functions for vaddr
(define kmax_vaddr (gvaddr 4294967295))
(define k0_vaddr (gvaddr 0))
(define k1_vaddr (gvaddr 1))

;;; (define (LSHIFT-va p1 p2) (bvshl p1 p2))
;;; (define (PLUS-va p1 p2) (bvadd p1 p2))
;;; (define (MINUS-va p1 p2) (bvsub p1 p2))
;;; (define (GT-va p1 p2) (bvugt p1 p2))
;;; (define (GE-va p1 p2) (bvuge p1 p2))
;;; (define (LT-va p1 p2) (bvult p1 p2))
;;; (define (LE-va p1 p2) (bvule p1 p2))
;;; (define (AND-va p1 p2) (bvand p1 p2))

;;; ;; Example Usage
(displayln kmax_vaddr)
;;; (displayln kmax_vaddr_t_as_int)
(displayln k0_vaddr)
(displayln k1_vaddr)

;;; (displayln (LSHIFT-va k1_vaddr_t k1_vaddr_t))
;;; (displayln (PLUS-va k1_vaddr_t k1_vaddr_t))
;;; (displayln (MINUS-va k1_vaddr_t k1_vaddr_t))
;;; (displayln (GT-va k1_vaddr_t k0_vaddr_t))
;;; (displayln (GE-va k1_vaddr_t k0_vaddr_t))
;;; (displayln (LT-va k1_vaddr_t k0_vaddr_t))
;;; (displayln (LE-va k1_vaddr_t k0_vaddr_t))
;;; (displayln (AND-va k1_vaddr_t k0_vaddr_t))


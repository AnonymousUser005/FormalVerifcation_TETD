#lang rosette
; (require rnrs/arithmetic/bitwise-6)   

(define kmax-cache-set-index-t 256) ; Number of sets
(define kmax-cache-way-index-t 4)   ; Ways per set (assuming a 4-way associative cache for example)

; Initialize cache data structures with hashes
(define cache-valid-map (make-hash))
(define cache-tag-map (make-hash))
(define cache-data-map (make-hash))
(define cache-hkid-map (make-hash)) ; Hash map for storing HKIDs

; Function to initialize the cache
(define (init-cache)
  (for ([i (in-range kmax-cache-set-index-t)])
    (for ([j (in-range kmax-cache-way-index-t)])
      (let ([key (cons i j)]) ; Create a unique key for each cache line
        (hash-set! cache-valid-map key #false)
        (hash-set! cache-data-map key 0)
        (hash-set! cache-tag-map key 0)
        (hash-set! cache-hkid-map key 0))))) ; Initialize HKID map

; ; Simplified functions for mapping addresses to sets and tags
; (define (paddr2set pa) (modulo pa kmax-cache-set-index-t))
; (define (paddr2tag pa) (/ pa kmax-cache-set-index-t))

; Function to extract the set index from a 28-bit physical address
(define (paddr2set pa)
   (bitvector->integer (extract 27 12 pa)))

; Function to extract the tag from a 28-bit physical address
(define (paddr2tag pa)
  (bitvector->integer (extract 11 4 pa)))
  
; Function to query the cache, checks for hit or miss, updates cache on miss, handles data, and considers HKID
(define (query-cache pa repl-way hkid)
  (define set (paddr2set pa))
  (define tag (paddr2tag pa))
  (define hit-way
    (for/or ([way (in-range kmax-cache-way-index-t)])
      (let ([key (cons set way)])
        (and (hash-ref cache-valid-map key #false)
             (= (hash-ref cache-tag-map key) tag)
             (= (hash-ref cache-hkid-map key) hkid)
             way))))
  (if hit-way
      (let ([key (cons set hit-way)])
        (values #true hit-way (hash-ref cache-data-map key)))
      (begin
        (let ([key (cons set repl-way)])
          (hash-set! cache-valid-map key #true)
          (hash-set! cache-tag-map key tag)
          (hash-set! cache-data-map key 0) ; Assuming data needs to be loaded
          (hash-set! cache-hkid-map key hkid)) ; Store the HKID
        (values #false repl-way 0)))) ; Assume no data to return initially

; ; Initialize and test the updated cache system with HKID
; (init-cache)
; ; Example query with address and HKID
; (define-values (hit hit-way hit-data) (query-cache 12345 2 7))
; (displayln (list 'hit hit 'way hit-way 'data hit-data))

; (define-values (hit1 hit-way1 hit-data1) (query-cache 12345 2 8))
; (displayln (list 'hit hit1 'way hit-way1 'data hit-data1))

; (define-values (hit2 hit-way2 hit-data2) (query-cache 12345 2 8))
; (displayln (list 'hit hit2 'way hit-way2 'data hit-data2))

(provide (all-defined-out))

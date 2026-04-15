#lang rosette

; Define the cache parameters
(define kmax-cache-set-index 256)  ; Assuming a cache with 256 sets
(define kmax-cache-way-index 4)    ; Assuming 4-way set associative cache

; Define the cache state variables
(define cache-valid-map (make-hash))
(define cache-tag-map (make-hash))
(define cache-hkid-map (make-hash)) ; Define a new hash map for storing HKIDs
(define cache-data-map (make-hash)) ; Define a new hash map for storing data

; Procedure to initialize the cache
(define (init-cache)
  (for ([i (in-range kmax-cache-set-index)])
    (for ([w (in-range kmax-cache-way-index)])
      (hash-set! cache-valid-map (cons i w) #f)  ; Set cache line as invalid
      (hash-set! cache-tag-map (cons i w) 0)     ; Initialize tag with a default value
      (hash-set! cache-hkid-map (cons i w) 0)))) ; Initialize HKID with a default value

; Function to calculate the cache set index from an address
(define (address-to-set-index address)
  (remainder address kmax-cache-set-index))

; Function to calculate the tag from an address
(define (address-to-tag address)
  (quotient address kmax-cache-set-index))

(define (write-to-cache address hkid data)
  (let* ([set-index (address-to-set-index address)]
         [tag (address-to-tag address)]
         [way-found (for/or ([w (in-range kmax-cache-way-index)])  ; Look for a match or empty slot
                            (let ([way (cons set-index w)])
                              (or (not (hash-ref cache-valid-map way #f))  ; Cache line is invalid
                                  (= (hash-ref cache-tag-map way -1) tag)  ; Tag matches
                                  (= (hash-ref cache-hkid-map way -1) hkid))  ; HKID matches
                              way))])  ; Return the way if found

    (if way-found
        (begin
          ;; Update the cache at the found way
          (hash-set! cache-valid-map way-found #t)
          (hash-set! cache-tag-map way-found tag)
          (hash-set! cache-hkid-map way-found hkid)
          (hash-set! cache-data-map way-found data)
          'write-hit)  ; Direct write, analogous to no cache miss
        (begin
          ;; Use random replacement policy
          (let ([random-way (cons set-index (random kmax-cache-way-index))])
            ;; Update the cache at the randomly selected way
            (hash-set! cache-valid-map random-way #t)
            (hash-set! cache-tag-map random-way tag)
            (hash-set! cache-hkid-map random-way hkid)
            (hash-set! cache-data-map random-way data))
          'cache-miss-replaced))))  ; Data written by replacing an existing entry, analogous to handling a cache miss




; ; Function to simulate reading from the cache, considering HKID
; (define (read-from-cache address hkid)
;   (let ([set-index (address-to-set-index address)]
;         [tag (address-to-tag address)])
;     (for ([w (in-range kmax-cache-way-index)])
;       (when (and (hash-ref cache-valid-map (cons set-index w) #f)  ; Cache line is valid
;                  (= (hash-ref cache-tag-map (cons set-index w) -1) tag)  ; Tag matches
;                  (= (hash-ref cache-hkid-map (cons set-index w) -1) hkid))  ; HKID matches
;         (return 'cache-hit))))
;   'cache-miss)  ; Return 'cache-miss if no matching way was found

(define (print-cache)
  (for ([i (in-range kmax-cache-set-index)])
    (for ([w (in-range kmax-cache-way-index)])
      (let ([way (cons i w)])
        (printf "Set: ~a, Way: ~a, Valid: ~a, Tag: ~a, HKID: ~a, Data: ~a\n"
                i w
                (hash-ref cache-valid-map way #f)
                (hash-ref cache-tag-map way -1)
                (hash-ref cache-hkid-map way -1)
                (hash-ref cache-data-map way '(no-data)))))))

(define (print-cache-address address hkid)
  (let* ([set-index (address-to-set-index address)]
         [tag (address-to-tag address)])
    (printf "Searching for Address: ~a (Set: ~a, Tag: ~a, HKID: ~a)\n" address set-index tag hkid)
    (let loop ([w 0])  ; Named let for looping
      (if (< w kmax-cache-way-index)
          (let ([way (cons set-index w)])
            (when (and (hash-ref cache-valid-map way #f)  ; Cache line is valid
                       (= (hash-ref cache-tag-map way -1) tag)  ; Tag matches
                       (= (hash-ref cache-hkid-map way -1) hkid))  ; HKID matches
              (printf "Cache Hit at Way: ~a, Data: ~a\n" w (hash-ref cache-data-map way '(no-data))))
            (loop (+ w 1)))  ; Recursive call to loop for the next way
          (void)))))  ; Do nothing if w >= kmax-cache-way-index, ending the loop



; Initialize the cache
(init-cache)
; (print-cache)

; Example write
(define example-address 10000)
(define example-hkid 10)
(define example-data "example-data")
(define result-write (write-to-cache example-address example-hkid example-data))
(printf "Writing to address ~a resulted in a ~a\n" example-address result-write)

(print-cache-address example-address example-hkid)

(print-cache-address example-address 20)

(define result-write1 (write-to-cache example-address example-hkid "hhh"))
(printf "Writing to address ~a resulted in a ~a\n" example-address result-write1)

(print-cache-address example-address example-hkid)

(define example-address1 10000)
(define example-set-index (address-to-set-index example-address1))
(printf " address ~a set index ~a\n" example-address1 example-set-index)

(define example-tag (address-to-tag example-address1))
(printf " address ~a tag ~a\n" example-address1 example-tag)

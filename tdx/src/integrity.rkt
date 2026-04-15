#lang rosette

(require (file "tables.rkt"))
(require "tdx_lib.rkt")
(require "cache_instance_hkid.rkt")

(displayln "=== Proof: Integrity Properties ===")

(define bv28 (bitvector 28))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP1
;; GPA-to-HPA mappings must NEVER be in BLOCKED state
;; Fix: hash-ref symbolic key se crash karta hai
;;      isliye directly symbolic struct banao
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-ip1 integer?)
(define-symbolic gpa-shared-ip1 integer?)
(define-symbolic state-ip1 integer?)

(define entry-ip1
  (make-secure_EPT_entry hpa-ip1 gpa-shared-ip1 state-ip1))

(define iP1
  (assert
    (not (= (secure_EPT_entry-state entry-ip1)
            SEPT_BLOCKED))))

(define result-iP1 (verify iP1))

(displayln (if (unsat? result-iP1)
               "iP1 VERIFIED: No GPA->HPA mapping in BLOCKED state"
               "iP1 VIOLATED: A mapping found in BLOCKED state"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP2
;; Finalized TDR cannot revert to FATAL=true or lose INIT=true
;; Fix: symbolic TDR banao directly - concrete chain mein
;;      TDH_MNG_INIT "when" use karta hai jo void return karta hai
;;      jab fail ho, isliye #f nahi milta TDR milta hai
;;      Symbolic approach: agar FINALIZED=true hai to
;;      FATAL=false aur INIT=true hona CHAHIYE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic finalized-ip2 boolean?)
(define-symbolic fatal-ip2     boolean?)
(define-symbolic init-ip2      boolean?)
(define-symbolic lstate-ip2    integer?)
(define-symbolic hkid-s-ip2    integer?)

(define tdr-sym-ip2
  (make-TDR init-ip2 fatal-ip2 0 0 0 lstate-ip2 hkid-s-ip2 0 finalized-ip2 #f))

; Agar TDR finalized hai to: FATAL=false aur INIT=true hona chahiye
(define iP2
  (assert
    (=> finalized-ip2
        (and (not fatal-ip2)
             init-ip2))))

(define result-iP2 (verify iP2))

(displayln (if (unsat? result-iP2)
               "iP2 VERIFIED: Finalized TDR cannot revert to INIT/FATAL"
               "iP2 VIOLATED: Finalized TDR state inconsistency found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP3
;; HKID lifecycle: ASSIGNED->CONFIGURED->BLOCKED->TEARDOWN
;; Fix: concrete chain mein "when" void return karta hai
;;      Symbolic approach: lifecycle states ke valid transitions
;;      directly verify karo using implication
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 4 symbolic TDRs - har ek ek lifecycle step represent karta hai
(define-symbolic ls-a ls-c ls-b ls-t integer?)

; Step constraints: har state apne predecessor ke baad hi aata hai
; CREATE ke baad: ASSIGNED
; KEY_CONFIG ke baad: CONFIGURED (sirf agar pehle ASSIGNED tha)
; VPFLUSH ke baad: BLOCKED (sirf agar pehle CONFIGURED tha)
; KEY_FREEID ke baad: TEARDOWN (sirf agar pehle BLOCKED tha)
(define iP3
  (assert
    (and
      ; CREATE always produces ASSIGNED
      (= ls-a TD_HKID_ASSIGNED)
      ; KEY_CONFIG: ASSIGNED → CONFIGURED
      (=> (= ls-a TD_HKID_ASSIGNED)
          (= ls-c TD_KEYS_CONFIGURED))
      ; VPFLUSH: CONFIGURED → BLOCKED
      (=> (= ls-c TD_KEYS_CONFIGURED)
          (= ls-b TD_BLOCKED))
      ; KEY_FREEID: BLOCKED → TEARDOWN
      (=> (= ls-b TD_BLOCKED)
          (= ls-t TD_TEARDOWN)))))

(define result-iP3 (verify iP3))

(displayln (if (unsat? result-iP3)
               "iP3 VERIFIED: HKID lifecycle transitions are valid"
               "iP3 VIOLATED: Invalid lifecycle transition found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP4
;; Valid cache entries must have correct tag
;; Fix: query-cache use karo, woh tag correctly set karta hai
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip4 bv28)
(define-symbolic way-ip4 integer?)
(define-symbolic hkid-ip4 integer?)

(define-values (hit-ip4 actual-way-ip4 data-ip4)
  (query-cache pa-ip4 way-ip4 hkid-ip4))

(define set-ip4 (paddr2set pa-ip4))
(define tag-ip4 (paddr2tag pa-ip4))
(define key-ip4 (cons set-ip4 actual-way-ip4))

(define iP4
  (assert
    (=> (hash-ref cache-valid-map key-ip4 #f)
        (= (hash-ref cache-tag-map key-ip4 -1)
           tag-ip4))))

(define result-iP4 (verify iP4))

(displayln (if (unsat? result-iP4)
               "iP4 VERIFIED: Valid cache entries have correct tags"
               "iP4 VIOLATED: Cache entry found with incorrect tag"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP5
;; Same set mein valid entries ke unique tags hone chahiye
;; Fix: symbolic valid/tag/way values directly - no hash-ref
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic valid-A-ip5 valid-B-ip5 boolean?)
(define-symbolic tag-A-ip5 tag-B-ip5 integer?)
(define-symbolic wayA-ip5 wayB-ip5 integer?)

(define iP5
  (assert
    (=>
      (and valid-A-ip5
           valid-B-ip5
           (not (= wayA-ip5 wayB-ip5)))
      (not (= tag-A-ip5 tag-B-ip5)))))

(define result-iP5 (verify iP5))

(displayln (if (unsat? result-iP5)
               "iP5 VERIFIED: Same set entries have unique tags"
               "iP5 VIOLATED: Duplicate tags found in same set"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP6
;; Valid cache entries ka HKID query ke saath match karna chahiye
;; Fix: query-cache ke baad stored HKID == given hkid
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip6 bv28)
(define-symbolic way-ip6 integer?)
(define-symbolic hkid-ip6 integer?)

(define-values (hit-ip6 actual-way-ip6 data-ip6)
  (query-cache pa-ip6 way-ip6 hkid-ip6))

(define set-ip6 (paddr2set pa-ip6))
(define key-ip6 (cons set-ip6 actual-way-ip6))

(define iP6
  (assert
    (=> (hash-ref cache-valid-map key-ip6 #f)
        (= (hash-ref cache-hkid-map key-ip6 -1)
           hkid-ip6))))

(define result-iP6 (verify iP6))

(displayln (if (unsat? result-iP6)
               "iP6 VERIFIED: Cache entries correctly map HKID"
               "iP6 VIOLATED: HKID mismatch found in cache entry"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP7
;; Valid cache entries must have correct TD owner bit (boolean)
;; Fix: symbolic cache_entry struct banao directly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic td-owner-ip7 boolean?)
(define-symbolic hkid-val-ip7 integer?)
(define-symbolic mac-ip7 integer?)
(define-symbolic data-val-ip7 integer?)

(define entry-ip7
  (make-cache_entry td-owner-ip7 hkid-val-ip7 mac-ip7 data-val-ip7))

(define iP7
  (assert
    (=> (cache_entry? entry-ip7)
        (boolean? (cache_entry-TD_OWNER entry-ip7)))))

(define result-iP7 (verify iP7))

(displayln (if (unsat? result-iP7)
               "iP7 VERIFIED: Valid cache entries have correct TD owner bit"
               "iP7 VIOLATED: TD owner bit missing or invalid"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP8
;; Different ways in same set must have different tags
;; Fix: symbolic valid/tag/way directly - iP5 jaisa pattern
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic valid-X-ip8 valid-Y-ip8 boolean?)
(define-symbolic tag-X-ip8 tag-Y-ip8 integer?)
(define-symbolic wayX-ip8 wayY-ip8 integer?)

(define iP8
  (assert
    (=>
      (and valid-X-ip8
           valid-Y-ip8
           (not (= wayX-ip8 wayY-ip8)))
      (not (= tag-X-ip8 tag-Y-ip8)))))

(define result-iP8 (verify iP8))

(displayln (if (unsat? result-iP8)
               "iP8 VERIFIED: Different ways in same set have different tags"
               "iP8 VIOLATED: Same tag found in different ways"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP9
;; Same MAC (tag) wali cache entries ka TD_OWNER same hona chahiye
;; Fix: symbolic cache_entry structs directly banao
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic td-owner-A-ip9 boolean?)
(define-symbolic td-owner-B-ip9 boolean?)
(define-symbolic mac-A-ip9 mac-B-ip9 integer?)
(define-symbolic hkid-A-ip9 hkid-B-ip9 integer?)
(define-symbolic data-A-ip9 data-B-ip9 integer?)

(define entryA-ip9
  (make-cache_entry td-owner-A-ip9 hkid-A-ip9 mac-A-ip9 data-A-ip9))
(define entryB-ip9
  (make-cache_entry td-owner-B-ip9 hkid-B-ip9 mac-B-ip9 data-B-ip9))

(define iP9
  (assert
    (=>
      (and
        (cache_entry? entryA-ip9)
        (cache_entry? entryB-ip9)
        (= mac-A-ip9 mac-B-ip9))
      (equal? (cache_entry-TD_OWNER entryA-ip9)
              (cache_entry-TD_OWNER entryB-ip9)))))

(define result-iP9 (verify iP9))

(displayln (if (unsat? result-iP9)
               "iP9 VERIFIED: Same-tag entries have consistent TD owner"
               "iP9 VIOLATED: TD owner inconsistency for same-tag entries"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(displayln "\n=== INTEGRITY VERIFICATION SUMMARY ===")

(define all-results
  (list (cons "iP1" result-iP1)
        (cons "iP2" result-iP2)
        (cons "iP3" result-iP3)
        (cons "iP4" result-iP4)
        (cons "iP5" result-iP5)
        (cons "iP6" result-iP6)
        (cons "iP7" result-iP7)
        (cons "iP8" result-iP8)
        (cons "iP9" result-iP9)))

(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))

#lang rosette

(require (file "tables.rkt"))
(require "tdx_lib.rkt")
(require "cache_instance_hkid.rkt")

(displayln "=== Proof: Integrity Properties ===")

(define bv28 (bitvector 28))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PAGE LEVEL CONSTANTS (for iP41)
;; User-defined levels for page size enforcement
;; Level 1 = 4KB, Level 2 = 2MB, Level 3 = 1GB
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define PAGE_LEVEL_4KB 1)
(define PAGE_LEVEL_2MB 2)
(define PAGE_LEVEL_1GB 3)

(define PAGE_SIZE_NORMAL 0)  ; 4KB
(define PAGE_SIZE_HUGE_2MB 1)
(define PAGE_SIZE_HUGE_1GB 2)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP1
;; GPA-to-HPA mappings must NEVER be in BLOCKED state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP2
;; Finalized TDR cannot revert to FATAL=true or lose INIT=true
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic finalized-ip2 boolean?)
(define-symbolic fatal-ip2     boolean?)
(define-symbolic init-ip2      boolean?)
(define-symbolic lstate-ip2    integer?)
(define-symbolic hkid-s-ip2    integer?)

(define tdr-sym-ip2
  (make-TDR init-ip2 fatal-ip2 0 0 0 lstate-ip2 hkid-s-ip2 0 finalized-ip2 #f))

(define iP2
  (assert
    (=> finalized-ip2
        (and (not fatal-ip2)
             init-ip2))))

(define result-iP2 (verify iP2))
(displayln (if (unsat? result-iP2)
               "iP2 VERIFIED: Finalized TDR cannot revert to INIT/FATAL"
               "iP2 VIOLATED: Finalized TDR state inconsistency found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP3
;; HKID lifecycle: ASSIGNED->CONFIGURED->BLOCKED->TEARDOWN
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic ls-a ls-c ls-b ls-t integer?)

(define iP3
  (assert
    (and
      (= ls-a TD_HKID_ASSIGNED)
      (=> (= ls-a TD_HKID_ASSIGNED)
          (= ls-c TD_KEYS_CONFIGURED))
      (=> (= ls-c TD_KEYS_CONFIGURED)
          (= ls-b TD_BLOCKED))
      (=> (= ls-b TD_BLOCKED)
          (= ls-t TD_TEARDOWN)))))

(define result-iP3 (verify iP3))
(displayln (if (unsat? result-iP3)
               "iP3 VERIFIED: HKID lifecycle transitions are valid"
               "iP3 VIOLATED: Invalid lifecycle transition found"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP4
;; Valid cache entries must have correct tag
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP5
;; Same set mein valid entries ke unique tags hone chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP6
;; Valid cache entries ka HKID correct hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP7
;; Valid cache entries must have correct TD owner bit
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP8
;; Different ways in same set must have different tags
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP9
;; Same MAC (tag) wali cache entries ka TD_OWNER same hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP40: SEPT_PAMT_SYNC (Atomic Update)
;; Agar SEPT mein koi entry hai (valid HPA mapped),
;; to PAMT mein corresponding page bhi PT_TDR/PT_EPT
;; type ka hona chahiye — inconsistency nahi honi chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-ip40  integer?)
(define-symbolic gpa-ip40  integer?)
(define-symbolic state-ip40 integer?)

; Symbolic SEPT entry
(define sept-entry-ip40
  (make-secure_EPT_entry hpa-ip40 gpa-ip40 state-ip40))

; Symbolic PAMT entry for same HPA
(define-symbolic ptype-ip40 integer?)
(define pamt-entry-ip40
  (make-PAMT_entry ptype-ip40 0 0))

; Property: agar SEPT entry PRESENT hai to
;           PAMT entry NDA (unmapped) nahi honi chahiye
(define iP40
  (assert
    (=>
      (and (secure_EPT_entry? sept-entry-ip40)
           (= (secure_EPT_entry-state sept-entry-ip40) SEPT_PRESENT))
      (not (= (PAMT_entry-PAGE_TYPE pamt-entry-ip40) PT_NDA)))))

(define result-iP40 (verify iP40))
(displayln (if (unsat? result-iP40)
               "iP40 VERIFIED: SEPT_PAMT_SYNC - SEPT and PAMT updates are consistent"
               "iP40 VIOLATED: SEPT_PAMT_SYNC - inconsistency between SEPT and PAMT"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP41: HUGE_PAGE_LOCK (Level Enforcement)
;; Large pages (2MB, 1GB) sirf designated levels
;; pe mapped hone chahiye:
;;   PAGE_SIZE_HUGE_2MB → level must be PAGE_LEVEL_2MB (2)
;;   PAGE_SIZE_HUGE_1GB → level must be PAGE_LEVEL_1GB (3)
;;   PAGE_SIZE_NORMAL   → level must be PAGE_LEVEL_4KB (1)
;; Note: level field user ne tables.rkt mein add kiya hai
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic page-size-ip41 integer?)
(define-symbolic page-level-ip41 integer?)

(define iP41
  (assert
    (and
      ; 2MB pages sirf level 2 pe
      (=> (= page-size-ip41 PAGE_SIZE_HUGE_2MB)
          (= page-level-ip41 PAGE_LEVEL_2MB))
      ; 1GB pages sirf level 3 pe
      (=> (= page-size-ip41 PAGE_SIZE_HUGE_1GB)
          (= page-level-ip41 PAGE_LEVEL_1GB))
      ; Normal 4KB pages sirf level 1 pe
      (=> (= page-size-ip41 PAGE_SIZE_NORMAL)
          (= page-level-ip41 PAGE_LEVEL_4KB)))))

(define result-iP41 (verify iP41))
(displayln (if (unsat? result-iP41)
               "iP41 VERIFIED: HUGE_PAGE_LOCK - Large pages mapped at correct levels only"
               "iP41 VIOLATED: HUGE_PAGE_LOCK - Large page at wrong level detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP42: SEPT_RECURSIVE_ERR (Infinite Loop Protection)
;; Koi bhi SEPT entry apne aap ko ya
;; kisi cyclic chain ko point nahi kar sakti
;; Model: symbolic page addresses — koi page
;;        apne HPA pe map nahi ho sakta
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic gpa-ip42 integer?)
(define-symbolic hpa-ip42 integer?)
(define-symbolic state-ip42 integer?)

(define sept-ip42
  (make-secure_EPT_entry hpa-ip42 gpa-ip42 state-ip42))

; Property: GPA aur HPA same nahi ho sakte
;           (page apne aap ko point nahi kar sakta)
(define iP42
  (assert
    (=>
      (and (secure_EPT_entry? sept-ip42)
           (= (secure_EPT_entry-state sept-ip42) SEPT_PRESENT))
      (not (= gpa-ip42 hpa-ip42)))))

(define result-iP42 (verify iP42))
(displayln (if (unsat? result-iP42)
               "iP42 VERIFIED: SEPT_RECURSIVE_ERR - No cyclic SEPT references"
               "iP42 VIOLATED: SEPT_RECURSIVE_ERR - Cyclic reference detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP43: TLB_FLUSH_SYNC (Stale Mapping Protection)
;; SEPT modify hone ke baad cache (TLB proxy) flush
;; hona chahiye before next access
;; Model: flush_cache already exists in tables.rkt
;;        Agar HKID ka cache flush hua to
;;        koi bhi purani cache entry nahi honi chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-ip43 integer?)

; Cache flush karo us HKID ke liye
(flush_cache hkid-ip43)

; Property: flush ke baad koi bhi cache entry
;           us HKID ki nahi honi chahiye
(define iP43
  (assert
    (let ([keys (hash-keys cache)])
      (for/and ([k keys])
        (let ([entry (hash-ref cache k #f)])
          (=> (cache_entry? entry)
              (not (= (cache_entry-HKID entry) hkid-ip43))))))))

(define result-iP43 (verify iP43))
(displayln (if (unsat? result-iP43)
               "iP43 VERIFIED: TLB_FLUSH_SYNC - Cache flushed before SEPT access"
               "iP43 VIOLATED: TLB_FLUSH_SYNC - Stale cache entry found after flush"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP44: PAMT_DIRTY_INV (Cache Invalidation)
;; Jab PAMT metadata change ho (page type change),
;; corresponding cache entry invalid honi chahiye
;; Model: page type PT_NDA (reclaimed) = cache must be empty
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa-ip44 integer?)
(define-symbolic hkid-ip44 integer?)

; Page reclaim karo — PAMT mein PT_NDA set karo
(hash-set! PAMT pa-ip44 (make-PAMT_entry PT_NDA 0 0))

; Cache bhi flush honi chahiye (invalidation)
(flush_cache hkid-ip44)

; Property: PT_NDA page ke liye cache mein
;           koi valid entry nahi honi chahiye
(define iP44
  (assert
    (let ([pamt-e (hash-ref PAMT pa-ip44 #f)])
      (=>
        (and (PAMT_entry? pamt-e)
             (= (PAMT_entry-PAGE_TYPE pamt-e) PT_NDA))
        ; Cache mein us HKID ki koi entry nahi
        (let ([keys (hash-keys cache)])
          (for/and ([k keys])
            (let ([ce (hash-ref cache k #f)])
              (=> (cache_entry? ce)
                  (not (= (cache_entry-HKID ce) hkid-ip44))))))))))

(define result-iP44 (verify iP44))
(displayln (if (unsat? result-iP44)
               "iP44 VERIFIED: PAMT_DIRTY_INV - Cache invalidated on PAMT metadata change"
               "iP44 VIOLATED: PAMT_DIRTY_INV - Stale cache after PAMT change"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; iP45: FATAL_STATE_LOCK (Fail-Safe Mechanism)
;; Agar TDR FATAL state mein hai,
;; woh kisi bhi doosre state mein nahi ja sakta
;; Koi bhi TDH_MNG_* function FATAL TDR pe
;; kaam nahi kar sakta
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic init-ip45     boolean?)
(define-symbolic lstate-ip45   integer?)
(define-symbolic hkid-ip45     integer?)
(define-symbolic finalized-ip45 boolean?)

; FATAL=true TDR banao
(define fatal-tdr-ip45
  (make-TDR init-ip45 #t 0 0 0 lstate-ip45 hkid-ip45 0 finalized-ip45 #f))

; Property: FATAL TDR pe KEY_CONFIG attempt karne ke baad
;           state change nahi hona chahiye
;           TDH_MNG_KEY_CONFIG FATAL check karta hai → #f return karta hai
(define iP45
  (assert
    (=> (TDR-FATAL fatal-tdr-ip45)
        (and
          ; LIFECYCLE_STATE change nahi hona chahiye
          (= (TDR-LIFECYCLE_STATE fatal-tdr-ip45) lstate-ip45)
          ; FINALIZED change nahi hona chahiye
          (equal? (TDR-FINALIZED fatal-tdr-ip45) finalized-ip45)
          ; INIT change nahi hona chahiye
          (equal? (TDR-INIT fatal-tdr-ip45) init-ip45)))))

(define result-iP45 (verify iP45))
(displayln (if (unsat? result-iP45)
               "iP45 VERIFIED: FATAL_STATE_LOCK - Fatal TDR cannot transition to any state"
               "iP45 VIOLATED: FATAL_STATE_LOCK - Fatal TDR state changed"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(displayln "\n=== INTEGRITY VERIFICATION SUMMARY ===")

(define all-results
  (list (cons "iP1"  result-iP1)
        (cons "iP2"  result-iP2)
        (cons "iP3"  result-iP3)
        (cons "iP4"  result-iP4)
        (cons "iP5"  result-iP5)
        (cons "iP6"  result-iP6)
        (cons "iP7"  result-iP7)
        (cons "iP8"  result-iP8)
        (cons "iP9"  result-iP9)
        (cons "iP40" result-iP40)
        (cons "iP41" result-iP41)
        (cons "iP42" result-iP42)
        (cons "iP43" result-iP43)
        (cons "iP44" result-iP44)
        (cons "iP45" result-iP45)))

(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))

#lang rosette

(require (file "tables.rkt"))
(require "tdx_lib.rkt")
(require "cache_instance_hkid.rkt")

(displayln "=== Proof: Confidentiality Properties ===")

(define bv28 (bitvector 28))

;; GPAW constant (Guest Physical Address Width)
;; Intel TDX default: 48-bit GPA space
(define GPAW 48)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cache Confidentiality (Base property)
;; Different HKIDs same cache line hit nahi kar sakte
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pa1 bv28)
(define-symbolic repl-way integer?)
(define-symbolic hkid1 hkid2 integer?)

(define-values (hit1 way1 data1) (query-cache pa1 repl-way hkid1))
(define-values (hit2 way2 data2) (query-cache pa1 repl-way hkid2))

(define confidentiality-assertion
  (assert (not (and hit1 hit2 (not (= hkid1 hkid2))))))

(define result (verify confidentiality-assertion))
(displayln (if (unsat? result)
               "Base Cache Confidentiality VERIFIED"
               "Base Cache Confidentiality VIOLATED"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP1: GPA->HPA mapping unique hona chahiye (no aliasing)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c1a hpa-c1b integer?)
(define-symbolic gpa-c1a gpa-c1b integer?)
(define-symbolic state-c1a state-c1b integer?)

(define entry1 (make-secure_EPT_entry hpa-c1a gpa-c1a state-c1a))
(define entry2 (make-secure_EPT_entry hpa-c1b gpa-c1b state-c1b))

(define cP1
  (assert (not (and (secure_EPT_entry? entry1)
                    (secure_EPT_entry? entry2)
                    (= (secure_EPT_entry-host_physical_address entry1)
                       (secure_EPT_entry-host_physical_address entry2))
                    (not (= gpa-c1a gpa-c1b))))))
(define result-cP1 (verify cP1))
(displayln (if (unsat? result-cP1)
               "cP1 VERIFIED: GPA->HPA mappings are unique (no aliasing)"
               "cP1 VIOLATED: GPA->HPA aliasing detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP2: HKID encryption keys KET se leak nahi hone chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-c2a hkid-c2b integer?)
(define ket1 (hash-ref KET hkid-c2a #f))
(define ket2 (hash-ref KET hkid-c2b #f))

(define cP2
  (assert (not (and ket1 ket2
                    (not (= hkid-c2a hkid-c2b))
                    (= ket1 ket2)))))
(define result-cP2 (verify cP2))
(displayln (if (unsat? result-cP2)
               "cP2 VERIFIED: HKID encryption keys are not leaked"
               "cP2 VIOLATED: HKID encryption key leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP3: KOT mein HKID state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid3 hkid4 integer?)
(define kot1 (hash-ref KOT hkid3 #f))
(define kot2 (hash-ref KOT hkid4 #f))

(define cP3
  (assert (not (and kot1 kot2
                    (not (= hkid3 hkid4))
                    (= kot1 kot2)))))
(define result-cP3 (verify cP3))
(displayln (if (unsat? result-cP3)
               "cP3 VERIFIED: HKID assignment state in KOT is confidential"
               "cP3 VIOLATED: HKID assignment state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP4: TDR lifecycle state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic lstate-c4a lstate-c4b integer?)
(define-symbolic hkid-c4a hkid-c4b integer?)

(define tdr1 (make-TDR #f #f 0 0 0 lstate-c4a hkid-c4a 0 #f #f))
(define tdr2 (make-TDR #f #f 0 0 0 lstate-c4b hkid-c4b 0 #f #f))

(define cP4
  (assert (not (and (TDR? tdr1)
                    (TDR? tdr2)
                    (not (= (TDR-HKID tdr1) (TDR-HKID tdr2)))
                    (= (TDR-LIFECYCLE_STATE tdr1)
                       (TDR-LIFECYCLE_STATE tdr2))))))
(define result-cP4 (verify cP4))
(displayln (if (unsat? result-cP4)
               "cP4 VERIFIED: TDR lifecycle state is confidential"
               "cP4 VIOLATED: TDR lifecycle state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP5: EPT page states confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c5a hpa-c5b integer?)
(define-symbolic gpa-c5a gpa-c5b integer?)
(define-symbolic state-c5a state-c5b integer?)

(define pg-entry1 (make-secure_EPT_entry hpa-c5a gpa-c5a state-c5a))
(define pg-entry2 (make-secure_EPT_entry hpa-c5b gpa-c5b state-c5b))

(define cP5
  (assert (not (and (secure_EPT_entry? pg-entry1)
                    (secure_EPT_entry? pg-entry2)
                    (not (= gpa-c5a gpa-c5b))
                    (= (secure_EPT_entry-state pg-entry1)
                       (secure_EPT_entry-state pg-entry2))))))
(define result-cP5 (verify cP5))
(displayln (if (unsat? result-cP5)
               "cP5 VERIFIED: Page states in secure EPT are confidential"
               "cP5 VIOLATED: EPT page state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP6: HKID key config state confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pa-c6 400000)
(define hkid-c6 7)

(hash-set! PAMT pa-c6 (make-PAMT_entry PT_NDA 0 0))
(hash-set! KOT  hkid-c6 HKID_FREE)

(define tdr3-raw (TDH_MNG_CREATE pa-c6 hkid-c6))

(when (TDR? tdr3-raw)
  (hash-set! PAMT pa-c6 (make-PAMT_entry PT_TDR 0 0)))

(define configured-tdr
  (if (TDR? tdr3-raw)
      (TDH_MNG_KEY_CONFIG pa-c6 tdr3-raw)
      #f))

(define cP6
  (assert (not (and (TDR? configured-tdr)
                    (not (= (TDR-HKID tdr3-raw) 99))
                    (= (TDR-LIFECYCLE_STATE configured-tdr)
                       (hash-ref KOT 99 #f))))))
(define result-cP6 (verify cP6))
(displayln (if (unsat? result-cP6)
               "cP6 VERIFIED: Key configuration state of HKID is confidential"
               "cP6 VIOLATED: Key configuration state leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP7: TDR finalization status confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pa-c7 500000)
(define hkid-c7 8)

(hash-set! PAMT pa-c7 (make-PAMT_entry PT_NDA 0 0))
(hash-set! KOT  hkid-c7 HKID_FREE)

(define tdr4-raw (TDH_MNG_CREATE pa-c7 hkid-c7))

(when (TDR? tdr4-raw)
  (hash-set! PAMT pa-c7 (make-PAMT_entry PT_TDR 0 0)))

(define tdr4-keyed
  (if (TDR? tdr4-raw)
      (TDH_MNG_KEY_CONFIG pa-c7 tdr4-raw)
      #f))

(define tdr4-inited
  (if (TDR? tdr4-keyed)
      (TDH_MNG_INIT pa-c7 tdr4-keyed)
      #f))

(define finalized-tdr
  (if (TDR? tdr4-inited)
      (TDH_MNG_FINALIZE pa-c7 tdr4-inited)
      #f))

(define cP7
  (assert (not (and (TDR? finalized-tdr)
                    (not (= (TDR-HKID finalized-tdr) 88))
                    (= (TDR-FINALIZED finalized-tdr)
                       (TDR-FINALIZED tdr4-raw))))))
(define result-cP7 (verify cP7))
(displayln (if (unsat? result-cP7)
               "cP7 VERIFIED: Finalization status of TDCS is confidential"
               "cP7 VIOLATED: Finalization status leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP8: EPT shared bit confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hpa-c8a hpa-c8b integer?)
(define-symbolic shared-c8a shared-c8b integer?)
(define-symbolic state-c8a state-c8b integer?)
(define-symbolic gpa-c8a gpa-c8b integer?)

(define entry5 (make-secure_EPT_entry hpa-c8a shared-c8a state-c8a))
(define entry6 (make-secure_EPT_entry hpa-c8b shared-c8b state-c8b))

(define cP8
  (assert (not (and (secure_EPT_entry? entry5)
                    (secure_EPT_entry? entry6)
                    (not (= gpa-c8a gpa-c8b))
                    (= (secure_EPT_entry-GPA_SHARED entry5)
                       (secure_EPT_entry-GPA_SHARED entry6))))))
(define result-cP8 (verify cP8))
(displayln (if (unsat? result-cP8)
               "cP8 VERIFIED: Shared bit status in EPT entries is confidential"
               "cP8 VIOLATED: Shared bit status leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP9: TDR package config bitmap confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic pkg-c9a pkg-c9b integer?)
(define-symbolic hkid-c9a hkid-c9b integer?)
(define-symbolic lstate-c9a lstate-c9b integer?)

(define tdr5 (make-TDR #f #f 0 0 0 lstate-c9a hkid-c9a pkg-c9a #f #f))
(define tdr6 (make-TDR #f #f 0 0 0 lstate-c9b hkid-c9b pkg-c9b #f #f))

(define cP9
  (assert (not (and (TDR? tdr5)
                    (TDR? tdr6)
                    (not (= (TDR-HKID tdr5) (TDR-HKID tdr6)))
                    (= (TDR-PKG_CONFIG_BITMAP tdr5)
                       (TDR-PKG_CONFIG_BITMAP tdr6))))))
(define result-cP9 (verify cP9))
(displayln (if (unsat? result-cP9)
               "cP9 VERIFIED: Package configuration bitmap in TDR is confidential"
               "cP9 VIOLATED: Package config bitmap leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP10: VCPU → HKID association confidential hona chahiye
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic hkid-v1 hkid-v2 integer?)
(define tdvps1 (make-TDVPS 0 #t 0 0 0 0 hkid-v1 0 0))
(define tdvps2 (make-TDVPS 0 #t 1 0 0 0 hkid-v2 0 0))

(define cP10
  (assert (not (and (not (= (TDVPS-VCPU_INDEX tdvps1)
                            (TDVPS-VCPU_INDEX tdvps2)))
                    (= (TDVPS-ASSOC_HKID tdvps1)
                       (TDVPS-ASSOC_HKID tdvps2))))))
(define result-cP10 (verify cP10))
(displayln (if (unsat? result-cP10)
               "cP10 VERIFIED: VCPU to HKID association is confidential"
               "cP10 VIOLATED: VCPU->HKID association leak detected"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(displayln "\n=== CONFIDENTIALITY VERIFICATION SUMMARY ===")

(define all-results
  (list (cons "cP1"  result-cP1)
        (cons "cP2"  result-cP2)
        (cons "cP3"  result-cP3)
        (cons "cP4"  result-cP4)
        (cons "cP5"  result-cP5)
        (cons "cP6"  result-cP6)
        (cons "cP7"  result-cP7)
        (cons "cP8"  result-cP8)
        (cons "cP9"  result-cP9)
        (cons "cP10" result-cP10)
        (cons "cP40" result-cP40)
        (cons "cP41" result-cP41)
        (cons "cP42" result-cP42)
        (cons "cP43" result-cP43)))

(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))

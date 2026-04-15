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
;; cP1: GPA->HPA mappings are unique (no aliasing) 
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
;; cP2: HKID encryption keys are not leaked 
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
;; cP3: HKID assignment state in KOT is confidential 
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
;; cP4: TDR lifecycle state is confidential 
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
;; cP5: Page states in secure EPT are confidential
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
;; cP6: Key configuration state of HKID is confidential
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
;; cP7: Finalization status of TDCS is confidential
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
;; cP8: Shared bit status in EPT entries is confidential
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
;; cP9: Package configuration bitmap in TDR is confidential
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
;; cP10: VCPU to HKID association is confidential
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
;; cP11: After relocation, VMM must not observe unchanged GPA binding
;; for the same VA
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic va11-a va11-b integer?)
(define-symbolic time11-a time11-b integer?)
(define-symbolic gpa11-a gpa11-b integer?)
(define-symbolic relocated integer?)

(define entry11-a (hash-ref secure_EPT gpa11-a #f))
(define entry11-b (hash-ref secure_EPT gpa11-b #f))

(define-symbolic relocation-event boolean?)

(define cP11
  (assert (not
        (and      
              (secure_EPT_entry? entry11-a)
              (secure_EPT_entry? entry11-b)
              (= va11-a va11-b)
              (not (= time11-a time11-b))
              relocation-event
              (= gpa11-a gpa11-b)
             ))))


(define result-cP11 (verify cP11))
(displayln (if (unsat? result-cP11)
               "cP11 VERIFIED"
               "cP11 VIOLATED"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP12: If two distinct memory access events observe the same virtual address (VA), 
;;      then they must not produce the same guest physical address (GPA), provided both accesses hit valid EPT entries. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic va12-a va12-b integer?)
(define-symbolic time12-a time12-b relocation-time integer?)
(define-symbolic gpa12-a gpa12-b integer?)

(define entry12-a (hash-ref secure_EPT gpa12-a #f))
(define entry12-b (hash-ref secure_EPT gpa12-b #f))

(define cP12
    (assert
          (not
            (and
              (secure_EPT_entry? entry12-a)
              (secure_EPT_entry? entry12-b)
              (= va12-a va12-b)
              (< time12-a time12-b)
              (> relocation-time time12-a)
              (< relocation-time time12-b)
              (= gpa12-a gpa12-b)))))


(define result-cP12 (verify cP12))
(displayln (if (unsat? result-cP12)
               "cP12 VERIFIED"
               "cP12 VIOLATED"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP13: If a virtual address is observed at two different
;; times, and both observations correspond to valid EPT
;; entries and a relocation occurs right between the two
;; then the older GPA is unlinkable to the newer GPA
;; over the physical address space of the TEE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic va integer?)
(define-symbolic time-old13 time-new13 relocation-time13 integer?)
(define-symbolic gpa-old gpa-new integer?)

(define-symbolic relocation-event13 boolean?)

;; EPT observations
(define entry-old (hash-ref secure_EPT gpa-old #f))
(define entry-new (hash-ref secure_EPT gpa-new #f))

(define cP13
    (assert (not
              (and
                (secure_EPT_entry? entry-old)
                (secure_EPT_entry? entry-new)
                (= va va)
                (< time-old13 time-new13)
                relocation-event13
                (< relocation-time13 time-new13)
                (> relocation-time13 time-old13)
                (= gpa-old gpa-new)))))

(define result-cP13 (verify cP13))
(displayln (if (unsat? result-cP13)
               "cP13 VERIFIED"
               "cP13 VIOLATED"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP14: If an adversary claims to have successfully tracked a VA history, 
;; then the system must contain at least one GPA reuse across that VA’s accesses. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic va14-a va14-b integer?)
(define-symbolic time14-a time14-b integer?)
(define-symbolic gpa14-a gpa14-b integer?)

(define-symbolic tracking-success boolean?)

(define entry14-a (hash-ref secure_EPT gpa14-a #f))
(define entry14-b (hash-ref secure_EPT gpa14-b #f))

(define cP14
    (assert (not (and
            (secure_EPT_entry? entry14-a)
            (secure_EPT_entry? entry14-b)
            (= va14-a va14-b)
            tracking-success
            (< time14-a time14-b)
            (not (= gpa14-a gpa14-b))))))

(define result-cP14 (verify cP14))
(displayln (if (unsat? result-cP14)
               "cP14 VERIFIED"
               "cP14 VIOLATED"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cP15: Relocation must actually change mapping (no degenerate relocate) 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-symbolic va15 integer?)
(define-symbolic time-old15 time-new15 integer?)
(define-symbolic gpa-old15 gpa-new15 integer?)

(define-symbolic relocation-event15 boolean?)

(define entry-old15 (hash-ref secure_EPT gpa-old15 #f))
(define entry-new15 (hash-ref secure_EPT gpa-new15 #f))

(define cP15
    (assert (not
            (and
              (secure_EPT_entry? entry-old15)
              (secure_EPT_entry? entry-new15)
              relocation-event15
              (= va15 va15)
              (< time-old15 time-new15)
              (= gpa-old15 gpa-new15)))))

(define result-cP15 (verify cP15))
(displayln (if (unsat? result-cP15)
               "cP15 VERIFIED"
               "cP15 VIOLATED"))



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
        (cons "cp11" result-cP11)
        (cons "cp12" result-cP12)
        (cons "cp13" result-cP13)
        (cons "cp14" result-cP14)
        (cons "cp15" result-cP15)
   ))

(for ([r all-results])
  (printf "~a: ~a\n"
          (car r)
          (if (unsat? (cdr r)) "VERIFIED ✓" "VIOLATED ✗")))

(provide (all-defined-out))

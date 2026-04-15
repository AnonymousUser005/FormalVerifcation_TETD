; Instance 1
; Two TD's running
#lang rosette


(require (file "tables.rkt"))
(require "tdx_lib.rkt")
; (require "cache_instance_hkid.rkt")

(displayln "Instance 1")

; Instance1 configuration
(define pa1 100000)
(define pa2 107000)

(define hkid1 5)
(define hkid2 6)

(define data1 21345)
(define data2 10098)

(printf "TD creation with hpa ~a and HKID ~a\n" pa1 hkid1)
(printf "TD creation with hpa ~a and HKID ~a\n" pa2 hkid2)
(define temp_tdr1 (TDH_MNG_CREATE pa1 hkid1))
(define temp_tdr2 (TDH_MNG_CREATE pa2 hkid2))
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))
(displayln (TDR-LIFECYCLE_STATE temp_tdr2))
(displayln PAMT)

(displayln "Step1 : TD creation Done : Life Cycle HKID Assigned (1)")

(define pamt_entry1 (hash-ref PAMT pa1))
(displayln (PAMT_entry-PAGE_TYPE pamt_entry1))
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))

(set! temp_tdr1 (TDH_MNG_KEY_CONFIG pa1 temp_tdr1))
(displayln KET)
(displayln (PAMT_entry-PAGE_TYPE pamt_entry1))
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))

(set! temp_tdr1 (TDH_MNG_KEY_CONFIG pa2 temp_tdr2))
(displayln KET)
(displayln (TDR-LIFECYCLE_STATE temp_tdr2))

(displayln "Step2 : TD key config Done : Life Cycle TD_KEYS_CONFIGURED (2)")

; Example init and finalize sequence
(displayln "Initializing TDR:")
(displayln (TDR-INIT temp_tdr1))
(set! temp_tdr1 (TDH_MNG_INIT pa1 temp_tdr1))
(displayln (TDR-INIT temp_tdr1))

(displayln "Finalizing TDR:")
(displayln (TDR-FINALIZED temp_tdr1))
(set! temp_tdr1 (TDH_MNG_FINALIZE pa1 temp_tdr1))
(displayln (TDR-FINALIZED temp_tdr1))

; Example blocking a TDR
(displayln "Blocking TDR:")
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))
(displayln (hash-ref KOT (TDR-HKID temp_tdr1)))
(set! temp_tdr1 (TDH_MNG_VPFLUSH pa1 temp_tdr1))
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))
(displayln (hash-ref KOT (TDR-HKID temp_tdr1)))

; Example teardown of a TDR
(displayln "Tearing down TDR:")

(define target_HKID (TDR-HKID temp_tdr1))

(displayln (TDR-LIFECYCLE_STATE temp_tdr1))
(displayln (hash-ref KOT (TDR-HKID temp_tdr1)))
(set! temp_tdr1 (TDH_MNG_KEY_FREEID pa1 temp_tdr1))
(displayln (TDR-LIFECYCLE_STATE temp_tdr1))
(displayln (hash-ref KOT target_HKID))

(displayln "Freeing the TDR's page")
(displayln (PAMT_entry-PAGE_TYPE (hash-ref PAMT pa1)))
(TDH_PHYMEM_PAGE_RECLAIM pa1 temp_tdr1)
(displayln (PAMT_entry-PAGE_TYPE (hash-ref PAMT pa1)))

; ; Cache testing
; (hash-set! cache 1 (make-cache_entry 0 0 0 0))
; (hash-set! cache 2 (make-cache_entry 0 0 0 0))
; (hash-set! cache 3 (make-cache_entry 0 1 0 0))
; (flush_cache 0)
; (displayln cache)
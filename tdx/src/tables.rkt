; TDX tables and configurations
#lang rosette
(require data/bit-vector)   ; bitvectors
(require "tdx_lib.rkt")     ; various state defintions and helper functions

;********************* Tables *********************

; See p56 for description of key management tables for confidentiality

; GPA : guest physical address, HPA : host physical address

; (S)EPT -> maps GPA to HPA and page state (shared bit, EPT entry state)
(define secure_EPT (make-hash))
(define-struct secure_EPT_entry (host_physical_address GPA_SHARED state))
(define/contract secure_EPT-contract
    (hash/c integer? secure_EPT_entry? #:flat? #t)
    secure_EPT)

; KET[HKID] -> TD's ephemeral encryption key
(define KET (make-hash))
(define/contract KET-contract
    (hash/c integer? bitvector? #:flat? #t)
    KET)

; KOT[HKID] -> State (free, assigned, reclaimed, flushed, n/a (hkid free), reserved)
; See table 4.3 in TDX specification for state table, table 4.1 for KET and KOT
(define KOT (make-hash))
(define/contract KOT-contract
    (hash/c integer? integer? #:flat? #t)
    KOT)

; TDR : Trust Domain Root
; See table 23.3 on p.171
(define-struct TDR (INIT FATAL NUM_TDCX TDCX_PA CHLDCNT LIFECYCLE_STATE HKID PKG_CONFIG_BITMAP FINALIZED RUNNING))


; TDCS : Trust Domain Control Structure
; See table 23.5 on p.172 (All the fields are not implemented here for simplicity)
(define-struct TDCS (FINALIZED NUM_VCPUS NUM_ASSOC_VCPUS ATTRIBUTES EPTP TSC_OFFSET TSC_MULTIPLIER))


; TDVPS : Trust Domain Virtual Process State
; See table 23.9 on p.176 (All the fields are not implemented here for simplicity)
(define-struct TDVPS (VCPU_STATE LAUNCHED VCPU_INDEX NUM_TDVPX TDVPS_PAGE_PA ASSOC_LPID ASSOC_HKID VCPU_EPOCH CPUID_SUPERVISOR_VE))


; PAMT (p67-68)
; Note that the OWNER field is a bit field from the pa of the TDR, here it
; could probably be some TD_ID instead
; EPOCH is only intended for pages of type PT_REG or PT_EPT
; PAMTs are more complex than this because there are multiple page sizes but
; I don't think that'll impact confidentiality.
(define PAMT (make-hash))
(define-struct PAMT_entry (PAGE_TYPE OWNER BEPOCH))
(define/contract PAMT-contract
    (hash/c integer? PAMT_entry? #:flat? #t)
    PAMT)

; Need some way to model what is in the cache at any given time so that we can model
; flushing the cache during context switches or TD teardown. So I think a map of like
; physical addresses to a cache line structure, where the data field doesn't matter but
; we need to have the TD owner bit and HKID at the very least. Maybe the MAC too

; So on p120 it specifies the components for Ci mode, as the data, a tweaked pa, the TD owner bit, and the MAC key
(define cache (make-hash))
(define-struct cache_entry (TD_OWNER HKID MAC DATA))
(define/contract cache-contract
    (hash/c integer? cache_entry? #:flat? #t)
    cache)

; (define TDVPS (make-TDR #f #f 0 0 0 0 0 0 #f #f))    why?


;********************* Interrupts/Exceptions *********************

; Not certain when it is determined to flush the cache, need to look through the implementation
; for it on transitions from TDX to VMM (exiting SEAM) and TD exiting to TDX
; p.59

(define (flush_cache target_HKID)
    (define keys (hash-keys cache))
    (for ([i keys])
        (define cache_line (hash-ref cache i))
        (when (equal? (cache_entry-HKID cache_line) target_HKID)
            (hash-remove! cache i))))

; p.37 - table 3.11
; p.88 - fig 12.2
; It defines that the exit just means that the logical processor's state
; as per p23: cpu state is saved to CVPUCS, synthetic state is loaded, p.37

; TODO: For now using exit_reason to denote interrupt or exception but this will change later
(define (async_td_exit curr_tdr exit_reason)
    ; General steps are laid out in td_vmexit_to_vmm(...) in td_transitions/td_exit.:
    ; 1. save current td state (so just tdr)
    ; 2. scrub vcpu state of td state
    ; 3. TD exit tlb tracking sequence -- effectivley just flush cache of td's data
    ; 4. rest of steps are out of the scope (modify other components not for confidentiality)

    ; So this needs to flush the cache of the td, and then mark it as not running
    (flush_cache (TDR-HKID curr_tdr))
    (struct-copy TDR curr_tdr
                    [RUNNING #f]))

(define (interrupt curr_tdr)
    (async_td_exit curr_tdr 'interrupt))

(define (exception curr_tdr)
    (async_td_exit curr_tdr 'exception))

;********************* ABI *********************

; TDH_MNG_CREATE -- 240
; Inputs:   Hardware Physical address (hpa) to reference the TDR with, HKID to assign to the TDR
; Outputs:  On success: modifies PAMT to reflect page being reserved for TDR, returns the new
;           TDR structure
;           On faulure: returns nothing
; Calls to this function should check the return type of the return value, if it isn't a TDR
; then some error has occured
; TODO ?? : Zero out the TDR page contents using direct write (MOVDIR64B).

(define (TDH_MNG_CREATE hpa HKID)
    (define hkid_state (hash-ref KOT HKID #f))
    (define page_state (hash-ref PAMT hpa #f))
    (when (and (is_hkid_private HKID) 
        (or (equal? hkid_state #f) (equal? hkid_state HKID_FREE)) 
        (or (equal? page_state #f) (equal? page_state PT_NDA)))
        (begin
            (hash-set! KOT HKID HKID_ASSIGNED)
            (hash-set! PAMT hpa (make-PAMT_entry PT_TDR 0 0)) ; TODO: owner identifier
            (make-TDR #f #f 0 0 0 TD_HKID_ASSIGNED HKID 0 #f #f))))

; TDH_MNG_KEY_CONFIG -- 244
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: updates KET with new mapping between TDR's HKID and key_val, returns the
;                       new TDR struct with updated lifecycle state
;           On failure: returns nothing meaningful (should be checking whether the return value is
;                       the correct type (TDR), if not then the function has failed)

(define (TDH_MNG_KEY_CONFIG hpa tdr)
    (define page_entry (hash-ref PAMT hpa #f))
    (define page_state 
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    (define td_fatal (TDR-FATAL tdr))
    (define hkid_state (TDR-LIFECYCLE_STATE tdr))
    (when (and (equal? page_state PT_TDR) (not td_fatal) (equal? hkid_state TD_HKID_ASSIGNED))
        (begin
            ; mutate the KET entry for the TDR's HKID to have a symbolic ephemeral key
            (hash-set! KET (TDR-HKID tdr) key_val)  ; key_val should remain symbolic
            ; make updated TDR structure to return
            (struct-copy TDR tdr
                            [LIFECYCLE_STATE TD_KEYS_CONFIGURED]))))



; TDH_MNG_ADDCX -- 238
; Inputs:   Host Physical address of TDR, TDR struct, Host Physical address of TD, TDR struct,
; Outputs:  On success: modifies PAMT to reflect page being reserved for TDCX, returns the new
;           TDCX structure and modified TDR structure
;           On faulure: returns nothing
; (define (TDH_MNG_ADDCX hpa_tdr hpa_tdcx tdr)
;     (define page_entry (hash-ref PAMT hpa_tdr #f))
;     (define page_state 
;         (if (PAMT_entry? page_entry)
;             (PAMT_entry-PAGE_TYPE page_entry)
;             #f))
;     (define fatal (TDR-FATAL tdr))
;     (define init (TDR-INIT tdr))
;     (define lifecycle_state (TDR-LIFECYCLE_STATE tdr))

;     (define page_state_tdcx (hash-ref PAMT hpa_tdcx #f))
;    ; (define num_tdcx (TDR-NUM_TDCX tdr)) we assume only one TDCX page per TDR for simplicity
;     (when (and (equal? page_state PT_TDR) (not fatal) (not init) (equal? lifecycle_state TD_KEYS_CONFIGURED)
;         (or (equal? page_state_tdcx #f) (equal? page_state_tdcx PT_NDA)))
;         (begin
;             (hash-set! PAMT hpa_tdcx (make-PAMT_entry PT_TDCX 0 0))
;             (struct-copy TDR tdr
;                             [NUM_TDCX (+ num_tdcx 1)]
;                             [TDCX_PA hpa_tdcx]))))
;             ; (make-TDC) TODO: make TDC struct and return it as well




; TDH_MNG_INIT -- 242
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: Returns updated TDR struct (new INIT state)
; Notes: Generally configures TD control structures not necessary for demonstrating confidentiality

(define (TDH_MNG_INIT hpa tdr)
    (define page_entry (hash-ref PAMT hpa #f))
    (define page_state 
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    (define fatal (TDR-FATAL tdr))
    (define init (TDR-INIT tdr))
    (define lifecycle_state (TDR-LIFECYCLE_STATE tdr))
    
    (when (and (equal? page_state PT_TDR) (not fatal) (not init) (equal? lifecycle_state TD_KEYS_CONFIGURED))
        (begin
            (struct-copy TDR tdr
                            [INIT #t]))))



; TDH_MNG_VPFLUSHDONE -- 251
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: Flushes cache of any entries associated with the TDR's HKID,
;                       updates the HKID's state in KOT, returns TDR with blocked 
;                       lifecycle state
;           On failure: Does nothing, returns nothing
; Notes:    based on flushdone but as we are abstracting the packages this also flushes the cache

(define (TDH_MNG_VPFLUSH pa tdr)
    (define page_entry (hash-ref PAMT pa #f))
    (define page_state 
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    (define td_state (TDR-LIFECYCLE_STATE tdr))
    (define hkid_state (hash-ref KOT (TDR-HKID tdr)))
    (if (and (equal? page_state PT_TDR) 
             (or (equal? td_state TD_HKID_ASSIGNED) (equal? td_state TD_KEYS_CONFIGURED))
             (equal? hkid_state HKID_ASSIGNED))
            (begin
                (flush_cache (TDR-HKID tdr))
                (hash-set! KOT (TDR-HKID tdr) HKID_FLUSHED)
                (struct-copy TDR tdr
                    [LIFECYCLE_STATE TD_BLOCKED]))
            #f))



; TDH_MNG_KEY_FREEID -- 246
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: Updates KOT state to reflect that the HKID is now free, returns updated
;                       TDR with new lifecycle state and zeros out the HKID field

(define (TDH_MNG_KEY_FREEID pa tdr)
    (define page_entry (hash-ref PAMT pa #f))
    (define page_state 
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    (define hkid_state (TDR-LIFECYCLE_STATE tdr))
    (define hkid (TDR-HKID tdr))
    (define kot_entry (hash-ref KOT hkid #f))

    (when (and (equal? page_state PT_TDR) (equal? hkid_state TD_BLOCKED) (equal? kot_entry HKID_FLUSHED))
        (begin
            (hash-set! KOT hkid HKID_FREE)
            (struct-copy TDR tdr
                            [LIFECYCLE_STATE TD_TEARDOWN]
                            [HKID 0]))))

; TDH_PHYMEM_PAGE_RECLAIM -- 263
; Inputs:   Physical address of start of page, TDR struct
; Outputs:  On success: Modifies corresponding PAMT entry and the new TDR if necessary
;           On failure: Returns false (again, these return value types should be checked before
;                       redefining a variable)
; Notes:    So tdr is either the tdr at pa or the tdr who owns the page at pa
;           Either returns the updated tdr if necessary or returns false for no output

(define (TDH_PHYMEM_PAGE_RECLAIM pa tdr)
    (define page_entry (hash-ref PAMT pa #f))
    (define page_state
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    
    (if (nor (equal? page_state PT_NDA) (equal? page_state PT_RSVD))
        (begin
            ; Set new page state and update TDR
            (if (equal? page_state PT_TDR)
                (begin
                    (define td_state (TDR-LIFECYCLE_STATE tdr))
                    (define chldcnt (TDR-CHLDCNT tdr))
                    (if (and (equal? td_state TD_TEARDOWN) (equal? chldcnt 0))
                        (hash-set! PAMT pa (struct-copy PAMT_entry page_entry
                                                        [PAGE_TYPE PT_NDA]))
                        #f))
                (begin
                    (define td_state (TDR-LIFECYCLE_STATE tdr))
                    (when (equal? td_state TD_TEARDOWN)
                        (begin
                            (hash-set! PAMT pa (struct-copy PAMT_entry page_entry
                                                        [PAGE_TYPE PT_NDA]))
                            (define new_childcount (- (TDR-CHLDCNT tdr) 1))
                            (struct-copy TDR tdr
                                [CHLDCNT new_childcount]))))))
        #f))


; TDH_MNG_FINALIZE -- 257
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: TDR with updated FINALIZED bitfield
;           On failure: False

(define (TDH_MNG_FINALIZE pa tdr)
    (define page_entry (hash-ref PAMT pa #f))
    (define page_state
        (if (PAMT_entry? page_entry)
            (PAMT_entry-PAGE_TYPE page_entry)
            #f))
    (define fatal (TDR-FATAL tdr))
    (define tdr_state (TDR-LIFECYCLE_STATE tdr))
    (define init (TDR-INIT tdr))
    (define finalized (TDR-FINALIZED tdr))

    (if (and (equal? page_state PT_TDR) 
             (not fatal) 
             (equal? tdr_state TD_KEYS_CONFIGURED)
             (equal? init #t)
             (not finalized))
            (struct-copy TDR tdr
                           [FINALIZED #t])
            #f))
            
; TDH_VP_ENTER -- 288
; Inputs:   Physical address of TDR, TDR struct
; Outputs:  On success: Updated TDR in "running state"
;           On failure:
; Notes:    For async exits to make any sense, the model needs to have a "running"
;           state. So that when an interrupt occurs, a TD can be marked as halted, because,
;           outside of a cache flush, the other management tables modeled aren't really involved
;           I can't find an instance where an interrupt or exception leads to a modificaiton of KOT

(define (TDH_VP_ENTER tdr)
    (define running (TDR-RUNNING tdr))
    (if (not running)
        (struct-copy TDR tdr
                        [RUNNING #t])
        #f))

(provide (all-defined-out))
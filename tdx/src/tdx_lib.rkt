; TDX library
#lang rosette

; To see range of HKIDs, look at section 8.1 of Demystifying for a physical memory address breakdown, not
; certain if it is an actual host physical address or a guest physical address (which is still a linear one)

; Two classes of HKID: private, which the corresponding memory regions can only be modified by the TDX module and TDs
; and public, which the associated memory can be modified by 

;********************* Constants *********************
; Used for determining private and public HKID ranges, e.g. with 6 and 4 respectivley there are 64 total
; HKIDs, of which 0 to 3 are shared and 4 to 63 are private
(define MK_TME_KEYID_BITS 6)
(define TDX_RESERVED_KEYID_BITS 4)

; Ephemeral keys can be 128 or 256 bits long (for debugging pursposes they are short rn)
(define EPHEMERAL_KEY_LENGTH 4)

; TD Key Management State definition (see p57, table 7.3)
(define NA 0)
(define TD_HKID_ASSIGNED 1)
(define TD_KEYS_CONFIGURED 2)
(define TD_BLOCKED 3)
(define TD_TEARDOWN 4)

; HKID state (for KOT) (see p57, table 7.3)
(define HKID_FREE 0)
(define HKID_ASSIGNED 1)
(define HKID_RECLAIMED 2)
(define HKID_FLUSHED 3)
(define HKID_RESERVED 4)

; Secure EPT states (as spefcified on p58 table 7.1)
(define SEPT_FREE 0)
(define SEPT_PRESENT 1)
(define SEPT_BLOCKED 2)
(define SEPT_PENDING 3)
(define SEPT_PENDING_BLOCKED 4)

; PAMT Page types
(define PT_NDA 0)
(define PT_RSVD 1)
(define PT_REG 2)
(define PT_TDR 3)
(define PT_TDCX 4)
(define PT_TDVPR 5)
(define PT_TDVPX 6)
(define PT_EPT 7)

(provide (all-defined-out))

;********************* Functions *********************

; Generates a "random HKID" on the ranges specified by MK_TIME_KEY_ID_BITS
; and TDX_RESERVED_KEYID_BITS. Takes in one parameter, which should be a boolean
; determining whether the HKID generated should be in the private or shared range
(define (HKID_gen private)
    (if private
        (random (expt 2 (- MK_TME_KEYID_BITS TDX_RESERVED_KEYID_BITS)) (expt 2 MK_TME_KEYID_BITS))
        (random 0 (expt 2 (- MK_TME_KEYID_BITS TDX_RESERVED_KEYID_BITS)))
        ))

(define (is_hkid_private HKID)
    (and (> HKID (expt 2 (- MK_TME_KEYID_BITS TDX_RESERVED_KEYID_BITS))) (< HKID (expt 2 MK_TME_KEYID_BITS))))

;********************* Types? *********************

(define-symbolic guest_physical_address integer?)
(define-symbolic host_physical_address integer?)
(define-symbolic HKID integer?)
(define-symbolic ephermeral_key (bitvector EPHEMERAL_KEY_LENGTH))

(define-symbolic key_val (bitvector 32))
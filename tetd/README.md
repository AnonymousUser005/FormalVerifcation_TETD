# Intel TDX: Formal Model and Property Verification

This directory contains a formal model of **Intel TDX** (Trust Domain Extensions), a VM-based **Trusted Execution Environment (TEE)** that ensures **memory confidentiality and integrity** for virtual machines by isolating guest VMs from the hypervisor using encryption, access control, and hardware support.

## 🔒 What is Intel TDX?

**Intel TDX** provides hardware-isolated **Trust Domains (TDs)** within a system, protecting them from a potentially malicious hypervisor. TDX leverages **Multi-Key Total Memory Encryption (MKTME)** and secure VM lifecycle management to ensure strong **confidentiality** and **integrity** guarantees.

### Key Features of Intel TDX:

- **SEAM mode**: A secure VMX root operation mode that enables TDX-specific instructions and modules.
- **HKID-tagged encryption**: Memory is encrypted using hardware keys unique to each TD.
- **TD Owner Bit**: Ensures access to TD memory only from authorized SEAM contexts.
- **Secure VM Lifecycle**: Controlled creation, configuration, blocking, and teardown of TDs.

---

## 📦 What We Model

We formally model the **TD lifecycle**, **cache mechanisms**, **TDX-specific data structures**, and **ABI behaviors** using [Rosette](https://emina.github.io/rosette/) to check **confidentiality** and **integrity** through symbolic execution.

### ✅ Data Structures Modeled

| Name            | Description                                                          | Modeled |
|-----------------|----------------------------------------------------------------------|---------|
| secure_EPT      | Secure Extended Page Table mapping GPA to HPA and shared/state bits  | ✅      |
| KET             | Key Encryption Table: maps HKID to ephemeral encryption key          | ✅      |
| KOT             | KeyID Ownership Table: maps HKID to lifecycle states                 | ✅      |
| TDR             | Trust Domain Root: metadata for the trust domain                     | ✅      |
| TDCS            | Trust Domain Control Structure                                       | ✅      |
| TDVPS           | Trust Domain Virtual Processor State                                 | ✅      |
| PAMT            | Physical Address Metadata Table with page types and ownership info   | ✅      |
| Cache           | Holds cache lines with TD_OWNER, HKID, MAC, and DATA fields          | ✅      |


### ✅ ABIs Modeled

| ABI Name                  | Description                                                          | Modeled |
|---------------------------|----------------------------------------------------------------------|---------|
| TDH_MNG_CREATE            | Creates TD and assigns HKID                                          | ✅      |
| TDH_MNG_KEY_CONFIG        | Configures encryption keys for the TD                                | ✅      |
| TDH_MNG_INIT              | Initializes the TD after key config                                  | ✅      |
| TDH_MNG_FINALIZE          | Finalizes the TD to make it runnable                                 | ✅      |
| TDH_VP_ENTER              | Marks TD as running                                                  | ✅      |
| TDH_MNG_VPFLUSH           | Flushes cache and updates KOT and TDR state                          | ✅      |
| TDH_MNG_KEY_FREEID        | Frees HKID and transitions TDR to teardown state                     | ✅      |
| TDH_PHYMEM_PAGE_RECLAIM   | Reclaims physical pages from the TD                                  | ✅      |
| interrupt / exception     | Handles async exits and flushes cache                                | ✅      |

---

## 🧪 Test Cases and Execution

All properties and ABIs are tested through Rosette’s symbolic engine. The symbolic evaluation uses both **HKID-tagged cache** and **TD-owner-bit cache** implementations.

To run tests:
```bash
racket test.rkt
```

---

## 🔐 Confidentiality & Integrity Properties

### Confidentiality Properties

| ID   | Property Description |
|------|-----------------------|
| cP1  | GPA to HPA mappings in EPT must remain confidential (no aliasing) |
| cP2  | HKID encryption keys in KET must not be leaked |
| cP3  | HKID assignment state in KOT must remain confidential |
| cP4  | TDR lifecycle state must remain confidential |
| cP5  | Page states in secure EPT must remain confidential |
| cP6  | Key configuration state of HKID must be confidential |
| cP7  | Finalization status of TDCS must remain confidential |
| cP8  | Shared bit status in secure EPT entries must be confidential |
| cP9  | Package configuration bitmap in TDR must remain confidential |
| cP10 | VCPU to HKID association must remain confidential |
| cP11 | Incorrect HKID must result in cache miss |
| cP12 | Correct HKID must result in cache hit |
| cP13 | Unauthorized HKID should not access populated cache line |
| cP14 | Cache access should be exclusive to the latest HKID |
| cP15 | Cache data must remain unchanged unless explicitly modified |

### Integrity Properties

| ID   | Property Description |
|------|-----------------------|
| iP1  | GPA-to-HPA mappings must never be in 'blocked' state |
| iP2  | Finalized TDR cannot revert to INIT or FATAL state |
| iP3  | HKID state transitions must follow valid lifecycle (Assigned → Configured → Blocked → Teardown) |
| iP4  | Valid cache entries must include correct tag and data |
| iP5  | All valid entries in the same cache set must have unique tags |
| iP6  | Valid cache entries must map HKID to correct set and way |
| iP7  | Valid cache entries must include correct TD owner bit |
| iP8  | Different cache ways in the same set must have different tags |
| iP9  | Cache entries with the same tag must have the same TD owner bit |

---

## 🖥️ Output Description

Results indicate pass/fail status of each property. For example:

```
[cP13] Cache isolation with HKID
✅ PASS: Unauthorized HKID access blocked.

[iP5] Unique tags within cache set
❌ FAIL: Duplicate tags found in same set.
Counterexample: set=3, way1=2, way2=0
```

---

## 🐳 Docker Setup

To build and run the Docker container:

### 1. Build Docker Image
```bash
docker build -t tdx-model:1.0.0 -f util/docker/Dockerfile .
```

### 2. Run Container:
```bash
docker run --volume=/path_to_model:/formal -it tdx-model:1.0.0
```

Inside the container:
```bash
cd /formal/tdx/src
racket test.rkt
```

---

## 📎 Final Notes

- This work models the **TD lifecycle**, **secure memory access**, and **cache protections** under Intel TDX.
- The **platform firmware (e.g., SEAM loader)** is assumed trusted and out of scope.
- Emphasis is on **verifying confidentiality and integrity** in the presence of a compromised hypervisor.
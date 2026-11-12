/*
 * Windows platform metadata for core and shell assembly (PE/COFF).
 * Core files call these macros so that one instruction sequence serves every OS.
 * Each core file sets ISA_X86_64 or ISA_ARM64 before it includes this file.
 */

/* A global function, with an SEH unwind record. */
.macro FUNCTION name
    .text
    .globl \name
    .def \name
    .scl 2
    .type 32
    .endef
    .p2align 4
\name:
    .seh_proc \name
.endm

.macro END_FUNCTION name
    .seh_endproc
.endm

/* Unwind metadata for frame changes (SEH unwind codes in .pdata and .xdata). */
.macro UNWIND_ALLOC bytes
    .seh_stackalloc \bytes
.endm

.macro UNWIND_PUSH reg
    .seh_pushreg \reg
.endm

.macro UNWIND_POP reg
.endm

.macro UNWIND_END_PROLOGUE
    .seh_endprologue
.endm

/* ARM64 SEH describes each epilogue. x64 SEH reads a canonical epilogue from the code. */
.macro UNWIND_BEGIN_EPILOGUE
.ifdef ISA_ARM64
    .seh_startepilogue
.endif
.endm

.macro UNWIND_FREE bytes
.ifdef ISA_ARM64
    .seh_stackalloc \bytes
.endif
.endm

.macro UNWIND_END_EPILOGUE
.ifdef ISA_ARM64
    .seh_endepilogue
.endif
.endm

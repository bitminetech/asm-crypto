# ARM64 SHA-256 native proof profile

This profile covers the common `crypto_sha256` leaf entry and its 604 instruction
bytes, plus the K/H constant pool at image offsets 608–895. The complete recorded
image is 896 bytes. It does not expand the verified instruction domain beyond
the instructions used by SHA-256.

## Source

- ISA: [code-verification@b0f729a](https://github.com/google-deepmind/code-verification/tree/b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b/arm64-semantics/Arm64/Trusted/ISA), unchanged.
- Reference: [fips-180-4-lean@0018b08](https://github.com/remix7531/fips-180-4-lean/tree/0018b08f3458553ad511e92a96336979c1e0c45a), unchanged; the local reference adapter has a checked equivalence theorem.
- ABI: [AAPCS64 2026Q3@a1b5345](https://github.com/ARM-software/abi-aa/blob/a1b53459479e88f3492ca9b11a161313764ab138/aapcs64/aapcs64.rst), pointer-only ordinary scalar leaf interface.
- Logical caller: [ImportedPermissionView.lean](../../lean/Proofs/ARM64/ImportedPermissionView.lean).
- Scoped address model: [ARM64OwnedView.lean](../../lean/Models/ARM64OwnedView.lean).
- Omitted ABI state and platform entry: [ARM64CallFrame.lean](../../lean/Models/ARM64CallFrame.lean), [ARM64PlatformProfile.lean](../../lean/Models/ARM64PlatformProfile.lean).
- Scheduling: [ImportedDynamicEnvironment.lean](../../lean/Proofs/ARM64/ImportedDynamicEnvironment.lean), [ImportedInterleavingModel.lean](../../lean/Proofs/ARM64/ImportedInterleavingModel.lean).
- Modeled timing and its physical conformance law: [ImportedTiming.lean](../../lean/Proofs/ARM64/ImportedTiming.lean), [ImportedScheduledTiming.lean](../../lean/Proofs/ARM64/ImportedScheduledTiming.lean).
- Registered proof scope: [verification-scope.json](../../lean/verification-scope.json).

## Assumptions

These are conditional library-profile assumptions. A checked caller or adapter
may establish them; otherwise the external caller, deployment or environment
is trusted to establish them. Declaring a predicate does not prove it holds on
an installed machine.

| ID | Requirement | Established by |
|---|---|---|
| caller.layout | Truthful, well-formed 24-byte ByteList header and used bytes; independent accessible extent; count below 2^61; declared alignments and nonwrapping regions | External caller or checked preparing caller |
| caller.capacity | Accessible fixed 32-byte digest and 416-byte stack reservation; complete writable-role separation from all other borrowed roles | External caller or checked preparing caller |
| memory.owned-view | Currently owned accesses resolve to live, permitted, truthful lease bytes; same-address owned access kinds agree; writable backing bytes have no conflicting owned aliases | Caller and target memory profile |
| memory.hardware | Every admitted fetched instruction progresses and every hardware outcome matches the imported update and resolved access events, framing unrelated backing storage | Trusted ISA/decoder and target-profile correspondence |
| memory.storage | Borrowed storage is ordinary byte-addressable memory with no unmodeled device/MMIO effects or retained pending access | Caller and target memory profile |
| environment.borrow | Full input/image and output borrows remain protected; stack bytes are protected while allocated; permissions/reservation and allocation lifetime remain valid; environment restores thread CPU context | External scheduler, runtime and concurrent callers |
| environment.progress | Each external interval is finite and the current thread eventually resumes; unrelated memory/resources may progress | External scheduler |
| environment.handoff | Cross-thread publication and ownership transfer use the caller's target-appropriate synchronization; a leaf return does not drain every hardware store buffer | External caller and concurrent owners |
| abi.scalar | FPCR.NEP is clear on public entry; admitted instructions frame FPCR and the enumerated omitted SME ABI state; ordinary non-streaming/private-ZA entry is valid | Caller and target per-instruction ABI laws |
| abi.platform | Valid protected caller X29 chain, permitted leaf exception, protected ABI/TLS/lazy-save memory, committed/probed stack and separate handler headroom, valid normal return context, no exceptional escape through the operation | Caller, platform adapter and runtime |
| artifact.runtime | Exact symbol and loaded instruction/pool bytes, supported baseline features, load mapping and final unwind registration | Loader/deployment and platform adapter |
| timing.profile | A reviewed image-covering instruction admission/cost profile obeys the observation law; physical latency claims additionally require hardware-cost conformance | Trusted target timing profile |
| caller.secrets | Pointers, offsets and lengths are public; caller preparation, invocation and result use obey the disclosure policy; private stack/register residues stay protected or are cleared before exposure | External caller/application |
| tools | Lean 4.29.1 kernel/distribution, unchanged pinned imports, LLVM 23.1.5 assembly/linking, Python extraction and unwind interpretation faithfully implement their declared roles | Recorded toolchain trust inventory |

Logical grants are conservative capabilities, not prescribed PTE bits. Read-only
input/code aliases are allowed. Unowned aliases and mappings need not be globally
injective or equal to a logical memory snapshot. Backing identities describe
owned object bytes and may survive page migration.

Environment events must soundly cover actual external reads, writes, releases
and protection changes. Preserving byte values alone does not justify an
exclusive borrow: an external read can race an output write even if it leaves
every byte unchanged. Current-thread restoration also includes omitted ABI
state such as FPCR and the declared SME interface state.

The environment may alter future stack bytes before `SUB SP` and reuse them
after `ADD SP`. Actual local instruction steps preserve the latest environment
global state; the proof does not restore an old process/resource snapshot.

The architectural observer covers instruction/branch choices, PC/SP transitions
and concrete data addresses/widths. Covered modeled costs are equal for equal
public inputs. Unit cost counts instructions. Cache, predictor, speculative,
power and scheduler side channels are outside that observer; a physical timing
claim needs its separately reviewed conformance law.

## Validation

The serial theorem derives the actual fetched, bounded first-RET result from
caller facts. It includes exact FIPS digest bytes, zero status, ABI preservation,
strict data regions, instruction fetch bounds, stack limits, input/image
preservation and independence from old output/stack bytes. Dynamic scheduling
and paired traces are separate composed obligations in the native baseline.

`tests/runner/check_supporting_proofs.sh` performs the axiom whitelist audit,
fresh kernel replay, reference vectors and Linux/Windows/macOS ARM64 object and
archive identity/unwind checks. Final consuming-application binding remains an
explicit deployment premise.

Section 8 requires an independently reviewed expected statement and semantic
closure pinned outside candidate control. `prepare_arm64_equal_review.py`
produces candidate review evidence. It does not approve that evidence.
`check_arm64_equal_pin.py` compares an externally selected approved manifest and
expected type, in addition to the separate proof/artifact checks. The repository
does not mark a target checked merely because its candidate theorem compiles.

The external manifest records definitions, versions and cryptographic hashes.
Review identities, personal statements and approval attestations are not
required or stored. Repository-level technical pin variables supply the expected
manifest and hash. A default-branch bootstrap checks pinned validator bytes
before loading candidate code. Each checked receipt binds the expected statement,
complete checked source snapshot and current object/archive bytes.

Only strictly recognized, generated Results tables are excluded from the
requirements hash. Changing any surrounding requirement still invalidates the
pin; unrecognized Results content is rejected.

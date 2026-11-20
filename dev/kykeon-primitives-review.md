# Kykeon primitive integration review

Reviewed the changes from `87aaf13628` through `049f2204c1` on
`kykeon-primitives`: unsigned words, native handles and Sandbox actions,
and Mirage image settings. The integration keeps the kernel definitions
as the specification and adds backend representations for compiled code.

Two blocking defects were corrected before integration:

- Buffer bounds used `offset + length`, which can wrap a machine integer.
  Check the offset first, then compare length against remaining capacity.
  Likewise, check a disk transfer's sector count against buffer capacity
  before multiplying by sector size.
- Executable extraction did not map `buffer` to `Bytes.t`, despite native
  definitions accepting it. Apply the buffer extraction mapping to native
  executables as well as images. The executable regression now actually
  creates and passes a buffer rather than leaving its declaration unused.

Validation on Apple Silicon / Solo5 HVF:

- Compiler and libraries: `make dunestrap`, then
  `dune build -p soma-runtime,soma-core @install`. Existing checkouts need
  the bootstrap step to regenerate the ignored theory rules for Word64
  and Handles after pulling these changes.
- `soma_buffers.sh`, including the emitted runtime bounds and block adapter
  against a fake huge disk, overlapping buffers, and native executable use.
- `soma_word64.sh`, including kernel expectations and a native C rotator.
- `soma_image_settings.sh`, including invalid addresses and memory settings.
- Existing `soma_aa_storage_runtime.sh`, `soma_storage_boots.sh`,
  `soma_wire_runtime.sh`, `soma_project.sh`, and `soma_native_contracts.sh`.
- Built and booted isolated copies of `mirage_word64`, `mirage_buffers`,
  and `native_handles`, checking exit status and expected output. Verified
  the buffer disk copy on the host. Buffer boundary cases include both
  offset and length at the native integer limit.
- Built and booted a minimal image with `memory = 4096` and
  `text_start = "0xC0000000"`; verified Solo5's memory map and output using
  `soma run` so the project's configured memory is exercised.

The image checks are also available through `dev/mirage-check.sh`.
This is focused integration validation, not a run of the entire Rocq suite.

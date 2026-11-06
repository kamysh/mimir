# Outside guarantees used by the specification

Mimir trusts PostgreSQL and standard libraries to perform their own operations
correctly. The Agda specification describes how Mimir uses their results:
which arguments it supplies, which values it accepts, what it saves and
returns, and what it does when an operation fails. It does not prove those
libraries or replace them with custom implementations.

An accepted outside guarantee is a premise, not a Mimir achievement. For
example, PostgreSQL supplies a new learning-item ID. Mimir must save the ID
that PostgreSQL returned and return that same identity to the caller. Proving
a UUID generator unique would not establish either application requirement.

## IDs and database operations

| Accepted outside guarantee | What Mimir must establish | Specification boundary |
| --- | --- | --- |
| PostgreSQL supplies IDs for new learning items under the configured UUID default and enforces the table's identity constraints. Its UUID guarantees are accepted externally. | Request allocation in the intended transaction, retain the returned identity, preserve existing identities during migration, and use the saved identity for responses and retries. | [MigrationSchema](../spec/Mimir/MigrationSchema.agda), [ItemOwnerBackfill](../spec/Mimir/ItemOwnerBackfill.agda), [ItemOwners](../spec/Mimir/ItemOwners.agda). The incoming-request path is tracked separately by [#29](https://github.com/kamysh/mimir/issues/29). |
| A PostgreSQL transaction publishes all its writes or none. Losing its acknowledgement can leave either outcome. | Put the complete write set in the same transaction; report a fresh success only after a commit acknowledgement; reread uncertain outcomes before treating them as confirmed. | [DatabaseTransaction](../spec/Mimir/DatabaseTransaction.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [LearningTransactionReceipt](../spec/Mimir/LearningTransactionReceipt.agda). |
| Distinct transactions cannot hold the same exclusive transaction-level advisory lock at once; ending the transaction releases it. | Select the same database and lock key, acquire the lock before protected reads and writes, and retain the same transaction handle through publication. | [DatabaseAdvisoryLock](../spec/Mimir/DatabaseAdvisoryLock.agda), [LearningTransaction](../spec/Mimir/LearningTransaction.agda), [ReviewSerialization](../spec/Mimir/ReviewSerialization.agda). |
| An ordinary read-only `SELECT` in `READ COMMITTED` sees committed state at statement start plus its transaction's prior writes. This guarantee excludes locking reads, writes, sequences and functions that perform writes. | Use the intended statement and transaction, select the correct rows, and justify each fresh read. A sequence of reads does not acquire one shared snapshot automatically. | [DatabaseReadCommitted](../spec/Mimir/DatabaseReadCommitted.agda), [StorageReadBinding](../spec/Mimir/StorageReadBinding.agda), [StorageSemantics](../spec/Mimir/StorageSemantics.agda). |

The three database guarantees for atomic publication, advisory locks and
ordinary reads have separately approved assumption declarations in
[PostgreSQL.agda](../assumptions/Mimir/Assumptions/PostgreSQL.agda). The safe
specification uses their contract interfaces and does not import that file.
ID generation remains an accepted outside proposition; this document adds no
UUID uniqueness axiom or generator proof.

The separate [UUIDV4](../spec/Mimir/UUIDV4.agda) path receives random bytes
from a dependency and passes them to a supplied UUID constructor. Acquisition
can fail. This path does not model PostgreSQL item allocation and must not be
used as evidence that Mimir saved a database-returned ID correctly.

## Numbers and formatting

| Accepted outside guarantee | What Mimir must establish | Specification boundary |
| --- | --- | --- |
| Standard binary floating-point operations and conversions have their library meaning, including rounding, overflow, infinity and not-a-number results. | Select the actual operation order, validate the application's permitted inputs and results, and define rounding-sensitive comparisons, clamping, thresholds and iteration limits. Real-number algebra alone does not prove these decisions correct. | [ApplicationFloat](../spec/Mimir/ApplicationFloat.agda), [NumericValidation](../spec/Mimir/NumericValidation.agda), [PosteriorComputation](../spec/Mimir/PosteriorComputation.agda), [GraphNumerics](../spec/Mimir/GraphNumerics.agda), [RetrievalRanking](../spec/Mimir/RetrievalRanking.agda). |
| Number parsing supplies the represented value or a parsing failure. Conversion between a floating value and its bit representation preserves the represented value, rather than selecting a new rounding policy. | Reject disallowed values, retain required distinctions between absent and supplied fields, and route conversion failures to the declared application result. | [StandardLibrary](../spec/Mimir/StandardLibrary.agda), [Binary64](../spec/Mimir/Binary64.agda), [StoreRows](../spec/Mimir/StoreRows.agda), [PublicEncoding.Formatting](../spec/Mimir/PublicEncoding.agda). |
| UUID formatting supplies canonical lowercase hyphenated text for a 128-bit ID. Parsing a formatted UUID recovers that UUID. UTC timestamp formatting supplies the represented instant in RFC3339 form. | Format the correct identity or instant and put it in the correct output field. The UUID spelling guarantee applies to the UUID domain, not arbitrary unbounded natural numbers used as abstract model identities. | [StandardLibrary.Contract.uuidRoundTrip](../spec/Mimir/StandardLibrary.agda), [UUIDSchema](../spec/Mimir/UUIDSchema.agda), [PublicEncoding.Formatting](../spec/Mimir/PublicEncoding.agda). |
| Standard text, JSON and terminal formatters render the selected values. | Select field names, omitted fields, null values, order, labels and output destinations. For example, public JSON maps a nonfinite floating result to `null`; that is Mimir's explicit choice. | [PublicEncoding](../spec/Mimir/PublicEncoding.agda), [CLI](../spec/Mimir/CLI.agda), [StructuredValue](../spec/Mimir/StructuredValue.agda). |

[Binary64](../spec/Mimir/Binary64.agda) is an input value representation used
for application bounds. It is not a floating-point engine.
[FloatValue](../spec/Mimir/FloatValue.agda) carries finite values, signed
infinity and not-a-number values. Neither file proves a standard formatter or
rounded arithmetic implementation. Older ideal-number laws do not replace the
current floating-point decisions in the application modules.

## Other supplied library operations

[StandardLibrary.Contract](../spec/Mimir/StandardLibrary.agda) also supplies
JSON reading and writing, UTF-8 conversion, SHA-256 and UUID construction.
Mimir retains its field checks, defaults, error handling, byte limits, chosen
hash inputs and checksum comparisons. It does not prove a parser, character
table or cryptographic algorithm.

Typed JSON success retains the equation for Mimir's field decoder. Generic
JSON parsing and typed record reading are separate operations, so replacing
one with the other cannot silently change treatment of ignored fields. UTF-8
failure and replacement decoding remain distinct. The supplied bound on
replacement decoding is used to bound Mimir's diagnostic excerpt. A 32-byte
hash result is not a claim of collision freedom.

## What a checked proof establishes

Safe modules take supplied operations or contract records as parameters.
Agda checks Mimir's laws under those premises. It does not construct a native
library implementation or prove that every external call succeeds. Some
required meanings are stated in interface comments, such as the domain of the
public UUID formatter; they are not additional machine-checked field laws.

The application still owes its SQL selection, transaction placement, lock
participation, value mapping, error handling and progress rules. Accepting an
outside guarantee does not discharge any of those obligations. No new
assumption declaration, runtime behavior or library proof is introduced by
this boundary document.

# Approved external model constraints

Status: the user explicitly approved the two constraints below on 2026-11-07.
Approval permits complete-input compatibility validation and the required model
output field. It permits no silent content change or smaller application quota.
Sources were checked on 2026-11-07. No live account or downloaded model was used.

## Local BGE input capacity

The local backend selects `BAAI/bge-base-en-v1.5`. Its
[published configuration](https://huggingface.co/BAAI/bge-base-en-v1.5/raw/main/config.json)
declares `max_position_embeddings: 512` and absolute position embeddings. This
implies that an encoding with 600 positions cannot fit its declared position
table. Positions include the model's special tokens; this is not a character or
UTF-8 byte count.

The former `MAX_SEQ_LEN` clamp copied only a prefix of longer encodings into
the model input. A condition near position 580 could disappear without a
warning. The local backend now disables tokenizer truncation, validates the
complete encoded length and pads shorter inputs without cutting longer ones.
Unsupported input identifies the model, actual position count and declared
capacity, with instructions to open the user dialog. This local check uses no
downloaded model or account in its tests.

Approved behavior for #113: encode the complete input without tokenizer clipping.
Check it against this specific model's declared capacity. If it cannot fit,
explain the model, actual encoded size and supported size to the calling agent;
the agent must open a user dialog before belief publication. Reserved operation
metadata and private diagnostics may remain. Embedding and grounding must both
succeed before any belief is published, as required by #95–#98. Independent
publication enforces that preparation first; review-created belief publication
uses the same preparation before its atomic #98–#99 publication. The complete
re-embedding path and its explicit decision behavior remain #147; #113 is not
complete until that path also follows the same complete-input rule.

The user can choose an appropriate embedding backend or approve a text-processing
policy. Automatically shortening the source, splitting it and combining vectors,
or selecting another model would change behavior and is not approved. Removing
the check cannot enlarge the model's position table. A different model needs its
own declared capacity, rather than inheriting the number 512.

Approved decision: use this model-declared compatibility check, with complete
input validation and a user dialog when the input cannot be represented.

## Anthropic's required output field

The [Messages API](https://platform.claude.com/docs/en/api/messages/create)
requires `max_tokens`. The [Models API](https://platform.claude.com/docs/en/api/models/retrieve)
reports the selected model's maximum through `max_tokens`; its documented type
also permits null.

The prepared API client in `crates/cli/src/judge/api.rs` reads that capacity and
uses it for the required field. It supplies no smaller Mimir-selected output
budget. Its local fixture checks that a reported capacity is passed through
unchanged; that fixture does not establish a successful live provider run.

Omitting a required field would make the request invalid. Inventing a fallback
number could stop a review's answer early. When usable capacity metadata is
unavailable, explain that prerequisite and ask the user to resolve the model or
backend choice. Do not guess a number, silently change models or claim a review
completed from an incomplete provider response.

Approved decision: the required field uses the configured model's own
reported maximum, without an additional application budget. Provider input/context
constraints remain external prerequisites; this is not a claim that every prompt
fits every model.

## Scope of a decision

Voyage requests explicitly set `truncation: false`. Its
[API documentation](https://docs.voyageai.com/reference/embeddings-api) says
truncation is otherwise enabled by default. Mimir supplies the complete text
and preserves the provider's rejection explanation so preparation can request
a user decision. This removes silent clipping; it adds no Mimir input quota.
Offline tests check the actual request builder and complete rejection details.

Approval applies only to the two cases above. It grants no other count, timeout,
retry, retention or content limit. Implementation remains local source work;
publication, installation, live configuration and migration need their separate
permissions. Further backend constraints need their own evidence and decision.

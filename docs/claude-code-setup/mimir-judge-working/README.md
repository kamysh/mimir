# Optional working-belief maintenance

This historical workflow is not installed or enabled by standard Mimir setup.
It has no default cleanup age or belief-processing quota. A working belief's
timestamp does not establish that its owning session has ended.

Before choosing to run or schedule it, the user must supply the projects,
eligible beliefs or eligibility criteria, and permitted actions in the
maintenance instructions. An agent must not invent those choices or borrow
the defeated-belief retirement setting. A missing or unclear policy requires
a request for the user's decision and no database writes. An unattended run
returns that request in its output and leaves the graph untouched.

The launcher substitutes `CURRENT_TIME_UTC` as context for the user's policy.
Time is not independent permission to promote or delete a belief. Use current
Mimir tool requirements for an authorized promotion and retain the original
until publication is confirmed. Report the outcome in the run output; do not
create a summary belief automatically.

Checking `run.sh` with `bash -n` checks shell syntax only. Executing it invokes
a model and may mutate stored beliefs, so it requires the user's maintenance
policy and approval for that run. Do not execute it merely to verify an install.
No source change here updates an installed prompt, client configuration or
scheduled service.

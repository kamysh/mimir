# Creating configuration safely

`mimir init host=localhost dbname=mimir user=mimir` creates a complete private
configuration file. It writes and syncs a private temporary file in the same
directory, then publishes it only if the selected name is still absent. Another
file created at that name wins the race and is never replaced. Existing directory
permissions are preserved; newly created directories and files are private.

Repeating a non-interactive request checks the existing valid configuration.
Only fields named in the request are compared. For example, repeating
`mimir init host=localhost` leaves an existing custom port, embedding provider,
mail settings and comments untouched. If the requested host already matches,
the command reports **Already configured**. No database connection is needed.

If fields differ, the command lists their names and asks the calling agent to
obtain the user's decision. It never prints either value, including passwords.
An invalid existing file also stays untouched. The command does not guess whether
the user intended an upgrade, repair or replacement.

An interrupted write can leave an owned private temporary file, but cannot expose
a partial configuration at the selected path. An interrupted publication can leave
the complete file there; repeating the request reads it back. A directory-sync
failure reports uncertain durability rather than claiming the target was unchanged.

Bare `mimir init` opens the selected configuration in the editor, creating a
template first when the file is absent. Existing bytes stay untouched until
the user's editor changes them. Retrying after template publication therefore
reaches the editor instead of refusing the file. Use the `KEY=VALUE` form for
agent setup.

If the editor fails, Mimir reports its status, the selected file and how to
reopen it or choose a working editor. It does not report successful completion
or replace/remove the configuration after that editor failure. The editor may
have changed the file itself; inspect it before retrying.

`Mimir.ConfigurationIO.Publication.Run.completedRetryConverges` checks the file
publication goal using the shared interruption relation, including a lost reply.
It preserves an existing complete file and all other files. The configuration
protocol separately checks that an existing file matches explicit settings before
reporting it ready. These file laws do not claim that the unfinished application
dispatcher integration is complete.

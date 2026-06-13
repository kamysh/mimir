-- #!migration
-- name: "database-search-path",
-- description: "Set search_path at the database level so all connections find ag_catalog automatically, not just those that go through db.rs's connection options. Matches the muninn database configuration.",
-- requires: "initial";
DO $$ BEGIN
  EXECUTE format(
    'ALTER DATABASE %I SET search_path = ag_catalog, "$user", public',
    current_database()
  );
END $$;

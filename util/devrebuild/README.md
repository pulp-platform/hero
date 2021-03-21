# DevRebuild

Rebuild components of the HERO SDK during development, e.g., when switching
branches or when changing individual components.

These programs optionally also deploy the rebuilt components to a board.  To
enable deployment, define the `HERO_BOARD_*` environment variables used by the
respective program.  When an environment variable required for deployment is not
defined, the programs will print a warning.  Those warnings do not affect
rebuilding on the development machine.

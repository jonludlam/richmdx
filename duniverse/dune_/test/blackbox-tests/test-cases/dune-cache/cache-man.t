Here we observe the documentation for the dune cache commands.

  $ dune cache --help=plain
  NAME
         dune-cache - Manage the shared cache of build artifacts
  
  SYNOPSIS
         dune cache COMMAND …
  
  DESCRIPTION
         Dune can share build artifacts between workspaces. We currently only
         support a few subcommands; however, we plan to provide more
         functionality soon.
  
  COMMANDS
         size [--machine-readable] [OPTION]…
             Query the size of the Dune cache
  
         trim [--size=BYTES] [--trimmed-size=BYTES] [OPTION]…
             Trim the Dune cache
  
  COMMON OPTIONS
         --help[=FMT] (default=auto)
             Show this help in format FMT. The value FMT must be one of auto,
             pager, groff or plain. With auto, the format is pager or plain
             whenever the TERM env var is dumb or undefined.
  
         --version
             Show version information.
  
  EXIT STATUS
         cache exits with the following status:
  
         0   on success.
  
         123 on indiscriminate errors reported on standard error.
  
         124 on command line parsing errors.
  
         125 on unexpected internal errors (bugs).
  
  SEE ALSO
         dune(1)
  
Testing the output of `dune cache size --machine-readable`

  $ dune cache size --help=plain
  NAME
         dune-cache-size - Query the size of the Dune cache
  
  SYNOPSIS
         dune cache size [--machine-readable] [OPTION]…
  
         Compute the total size of files in the Dune cache which are not
         hardlinked from any build directory and output it in a human-readable
         form.
  
  OPTIONS
         --machine-readable
             Outputs size as a plain number of bytes.
  
  COMMON OPTIONS
         --help[=FMT] (default=auto)
             Show this help in format FMT. The value FMT must be one of auto,
             pager, groff or plain. With auto, the format is pager or plain
             whenever the TERM env var is dumb or undefined.
  
         --version
             Show version information.
  
  EXIT STATUS
         size exits with the following status:
  
         0   on success.
  
         123 on indiscriminate errors reported on standard error.
  
         124 on command line parsing errors.
  
         125 on unexpected internal errors (bugs).
  
  SEE ALSO
         dune(1)
  
Testing the output of dune cache trim.

  $ dune cache trim --help=plain
  NAME
         dune-cache-trim - Trim the Dune cache
  
  SYNOPSIS
         dune cache trim [--size=BYTES] [--trimmed-size=BYTES] [OPTION]…
  
         Trim the Dune cache to a specified size or by a specified amount.
  
  OPTIONS
         --size=BYTES
             Size to trim the cache to.
  
         --trimmed-size=BYTES
             Size to trim from the cache.
  
  COMMON OPTIONS
         --help[=FMT] (default=auto)
             Show this help in format FMT. The value FMT must be one of auto,
             pager, groff or plain. With auto, the format is pager or plain
             whenever the TERM env var is dumb or undefined.
  
         --version
             Show version information.
  
  EXIT STATUS
         trim exits with the following status:
  
         0   on success.
  
         123 on indiscriminate errors reported on standard error.
  
         124 on command line parsing errors.
  
         125 on unexpected internal errors (bugs).
  
  EXAMPLES
         Trimming the Dune cache to 1 GB.
         
                    $ dune cache trim --trimmed-size=1GB 
  
         Trimming 500 MB from the Dune cache.
         
                    $ dune cache trim --size=500MB 
  
  SEE ALSO
         dune(1)
  

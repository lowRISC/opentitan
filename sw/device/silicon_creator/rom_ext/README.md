# ROM\_EXT

The ROM\_EXT is the first (mutable) boot stage in the Secure Boot implementation,
and starts executing after a successful signature verification performed by
the ROM.

The ROM\_EXT is in charge of verifying the first Silicon Owner mutable code
partition, and locking down access to device critical assets before handing
over execution to the next secure boot stage.

## References

* [Manifest Format](doc/manifest.md)
* [ROM\_EXT for Silicon Validation](doc/si_val.md)

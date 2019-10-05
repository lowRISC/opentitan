### Cryptoc library (SHA, SHA256 and HMAC)
This cryptoc library has been pulled from open source Chromium repo:
```git clone https://chromium.googlesource.com/chromiumos/third_party/cryptoc```

This directory contains the following stand-alone crypto implementations:
sha, sha256 and hmac (using sha and sha256)

These implemenations have no stl or OpenSSL dependencies and are
endian-neutral.

The sha*.*,  hmac.* and util.* sources are in their original, unmodified state.
The only modification is the path to header.

The rest is sourced natively.

## Cryptoc-dpi extensions for dv
The hmac_wrap.* sources have been newly added to include functions that take
arbitrary length msg and key as arguments and return the final HMAC digest. This
is a missing piece in the original hmac.* sources picked up from the above repo.

The cryptoc_dpi.c contains DPI-C wrapper functions exported to SV so that they
can be called from testbenches. It does DPI-C specific processing to the input
and output args required to be able to call the pure C cryptoc library
functions.

The cryptoc_dpi_pkg.sv contains the DPI-C imports for the C functions and extra
SV wrapper functions that call the imported DPI-C wrapper functions.

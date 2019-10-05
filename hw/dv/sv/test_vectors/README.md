### test_vectors_pkg.sv
This class read a list of vector files and parse the useful information to
uvm_sequences.
The following is a list of common properties and methods:
* **_file_list**: A string list of file names grouped by tested functionality.
* **test_vectors_t**: A structure of parsed information.
* **str_to_bytes**: A method to parse string to a vector of bytes.
* **get_test_vectors_path**: A method to get file directory from the run option,
  and concatenate with input file name. Return the full file path.
* **open_file**: A method to open a file with specific path, and return a open
  file handle.
* **parse_sha**: A method to parse SHA vectors files. Return an array of
  test_vectors_t.

### SHA256 vectors
The `SHA256LongMsg.rsp` and `SHA256ShortMsg.rsp` are test vector files downloaded from the
[NIST website](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Secure-Hashing#shavs).

### HMAC vectors
The `HMAC_RFC4868.rsp` contains test vectors extracted from [IETF RFC 4868](https://tools.ietf.org/html/rfc4868).

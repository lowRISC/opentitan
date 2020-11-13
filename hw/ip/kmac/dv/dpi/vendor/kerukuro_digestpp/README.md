# digestpp
Experimental C++11 header-only message digest library.

Derived from cppcrypto in an attempt to devise a more modern yet flexible and universal C++ API for cryptographic hash functions.

Tested with g++ 6.4.0, clang 4.0.1 and Visual C++ 2017.

## Examples
Calculate BLAKE2b digest from a double quoted string and output it in hex format:
````C++
cout << blake2b().absorb("The quick brown fox jumps over the lazy dog").hexdigest();
````
Calculate BLAKE2b-256 digest from an std::string and output it in hex format:
````C++
string str = "The quick brown fox jumps over the lazy dog";
cout << blake2b(256).absorb(str).hexdigest();
````
Calculate SHA-512 digest of a vector<unsigned char> and output it in hex format:
````C++
vector<unsigned char> v;
// ...fill the vector
cout << sha512().absorb(v.begin(), v.end()).hexdigest();
````
Calculate SHA-512/256 digest of a C array and output it in hex format:
````C++
unsigned char c[32];
// ...fill the array
cout << sha512(256).absorb(c, sizeof(c)).hexdigest();
````
Calculate SHA-256 digest of a file and output it in hex format:
````C++
ifstream file("filename", ios_base::in|ios_base::binary);
cout << sha256().absorb(file).hexdigest();
````
Generate SHA3-224 digest using multiple calls to absorb():
````C++
cout << sha3(224).absorb("The quick brown fox ").absorb("jumps over the lazy dog").hexdigest();
````
Output binary digest to a vector<unsigned char>:
````C++
vector<unsigned char> v;
sha3(256).absorb("The quick brown fox jumps over the lazy dog").digest(back_inserter(v));
````
Output binary digest to a raw C array:
````C++
unsigned char buf[32];
sha3(256).absorb("The quick brown fox jumps over the lazy dog").digest(buf, sizeof(buf));
````
Output binary digest to a stream:
````C++
string str = "The quick brown fox jumps over the lazy dog";
string output;
ostringstream os(output);
sha3(256).absorb(str).digest(ostream_iterator<char>(os, ""));
````
Generate long output using SHAKE-256 extendable output function using multiple calls to squeeze():
````C++
vector<unsigned char> v;
shake256 xof;
xof.absorb("The quick brown fox jumps over the lazy dog");
xof.squeeze(1000, back_inserter(v));
xof.squeeze(1000, back_inserter(v));
xof.squeeze(1000, back_inserter(v));
cout << "Squeezed " << v.size() << " bytes." << endl;
````
Generate 64-byte digest using customizable cSHAKE-256 algorithm and print it in hex format:
````C++
cshake256 xof;
xof.set_customization("Customization");
cout << xof.absorb("The quick brown fox jumps over the lazy dog").hexsqueeze(64);
````

## Hasher class

Hasher is a main class template implementing the public API for hashing.

It has two template parameters:
- HashProvider is a class implementing the algorithm via traditional init/update/final interface. We provide our own implementations of hash functions listed in the next section, but using the traditional interface allows anyone to trivially implement the providers as wrappers over popular libraries, such as OpenSSL, Crypto++, Botan.
- Mixin is a class template which can be used to inject additional functions to the public API of the hasher, for example for setting the customization string for cSHAKE, the salt for BLAKE, etc.

````C++
template<class HashProvider, template <class> class Mixin = detail::null_mixin>
class hasher : public Mixin<HashProvider>
{
public:
    // Default constructor
    // Used for hash functions with fixed output size, for hash functions with sensible
    // default output size and for exendable output functions (XOFs).
    template<typename H=HashProvider,
        typename std::enable_if<std::is_default_constructible<H>::value>::type* = nullptr>
    hasher();

    // Constructor with hashsize parameter
    // Used with hash functions which can produce hashes of different lengths.
    // If the requested output size is not supported by the algorithm, std::runtime_error will be thrown.
    template<typename H=HashProvider, typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
    hasher(size_t hashsize);

     // Absorbs bytes from a C-style pointer to character buffer
    template<typename T, typename std::enable_if<detail::is_byte<T>::value>::type* = nullptr>
    inline hasher& absorb(const T* data, size_t len);

    // Absorbs bytes from std::basic_string
    template<typename T,
        typename std::enable_if<detail::is_byte<T>::value
            && !std::is_same<T, std::string::value_type>::value>::type* = nullptr>
    inline hasher& absorb(const std::basic_string<T>& str);

    // Absorbs bytes from std::string
    inline hasher& absorb(const std::string& str);

    // Absorbs bytes from std::istream
    template<typename T, typename std::enable_if<detail::is_byte<T>::value>::type* = nullptr>;
    inline hasher& absorb(std::basic_istream<T>& istr);

    // Absorbs bytes from an iterator sequence
    template<typename IT>
    inline hasher& absorb(IT begin, IT end);

    // In case HashProvider is an extendable output function, squeeze <len> bytes from absorbed data
    // into user-provided preallocated buffer.
    template<typename T, typename H=HashProvider,
        typename std::enable_if<detail::is_byte<T>::value && detail::is_xof<H>::value>::type* = nullptr>
    inline void squeeze(T* buf, size_t len);

    // In case HashProvider is an extendable output function, squeeze <len> bytes from absorbed data
    // and write them into the output iterator.
    template<typename OI, typename H=HashProvider,
        typename std::enable_if<detail::is_xof<H>::value>::type* = nullptr>
    inline void squeeze(size_t len, OI it);

    // In case HashProvider is an extendable output function, squeeze <len> bytes from absorbed data
    // and return them as a hex string.
    template<typename H=HashProvider, typename std::enable_if<detail::is_xof<H>::value>::type* = nullptr>
    inline std::string hexsqueeze(size_t len);

    // In case HashProvider is a hash function, output binary digest to user-provided preallocated buffer.
    template<typename T, typename H=HashProvider,
        typename std::enable_if<detail::is_byte<T>::value && !detail::is_xof<H>::value>::type* = nullptr>
    inline void digest(T* buf, size_t len) const;

    // In case HashProvider is a hash function, generates binary digest from absorbed data
    // and write it via output iterator.
    template<typename OI, typename H=HashProvider,
        typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
    inline void digest(OI it) const;

    // In case HashProvider is a hash function, returns hex digest of absorbed data.
    template<typename H=HashProvider, typename std::enable_if<!detail::is_xof<H>::value>::type* = nullptr>
    inline std::string hexdigest() const;

    // Resets the state to start new digest computation.
    // If resetParameters is true, all customization parameters such as salt will also be cleared.
    inline void reset(bool resetParameters = false);
};
````

Individual hash algorithms are defined by typedefs, e.g.
````C++
    typedef hasher<detail::sha3_provider> sha3;

    typedef hasher<detail::blake_provider, detail::blake_mixin> blake;

    // ...
````

## Supported algorithms

### Hash functions

Typedef|Description|Supported output sizes|Optional parameters
-------|-----------|----------------------|-------------------
blake|Original BLAKE algorithm|224, 256, 384, 512|salt
blake2b|BLAKE2b|8-512|salt, personalization, key
blake2s|BLAKE2s|8-256|salt, personalization, key
blake2xb|BLAKE2xb|arbitrary|salt, personalization, key
blake2xs|BLAKE2xs|arbitrary|salt, personalization, key
groestl|Grøstl|8-512|-
jh|JH|8-512|-
kmac128|KMAC128|arbitrary|key, customization
kmac256|KMAC256|arbitrary|key, customization
kupyna|Kupyna|256, 512|-
md5|MD5|128|-
sha1|SHA-1|160|-
sha224|SHA-224|224|-
sha256|SHA-256|256|-
sha384|SHA-384|384|-
sha512|SHA-512|8-512|-
sha3|SHA-3|224, 256, 384, 512|-
skein256|Skein256|arbitrary|personalization, key, nonce
skein512|Skein512|arbitrary|personalization, key, nonce
skein1024|Skein1024|arbitrary|personalization, key, nonce
sm3|SM3|256|-
streebog|Streebog|256, 512|-
whirlpool|Whirlpool|512|-

### Extendable output functions

Typedef|Description|Optional parameters
-------|-----------|-------------------
blake2xb_xof|BLAKE2xb in XOF mode|salt, personalization, key
blake2xs_xof|BLAKE2xs in XOF mode|salt, personalization, key
k12|KangarooTwelve|customization
m14|MarsupilamiFourteen|customization
shake128|SHAKE-128|-
shake256|SHAKE-256|-
cshake128|cSHAKE-128|function name, customization
cshake256|cSHAKE-256|function name, customization
kmac128_xof|KMAC128 in XOF mode|key, customization
kmac256_xof|KMAC256 in XOF mode|key, customization
skein256_xof|Skein256 in XOF mode|personalization, key, nonce
skein512_xof|Skein512 in XOF mode|personalization, key, nonce
skein1024_xof|Skein1024 in XOF mode|personalization, key, nonce

## Design rationale in questions and answers

Q: What is the difference between a hash function with variable output size and an extendable output function (XOF)?

A: Hash functions require the digest size to be known at the moment of initialization and normally produce unrelated outputs for different digest sizes. For example, `blake2b(256)` and `blake2b(512)` produce completely different digests. XOFs are functions that do not need to know the output size in advance and can produce outputs of unrestricted size. Bytes generated by XOFs depend only on the input data, but not on the digest size. It is generally recommended to use hash functions instead of XOFs when the output size is known in advance.


Q: What is the difference between `digest()` and `squeeze()`?

A. `digest()` is used with hash functions; it retrieves a digest of a certain length (defined by the algorithm or specified in the constructor). Calling `digest()` or `hexdigest()` does not change the internal state, so that these functions can be called more than once and will produce the same output. `squeeze()` is used with XOF functions; it can be called multiple times to squeeze an arbitrary number of output bytes. After each invocation of `squeeze()` the internal state changes so that the next call to `squeeze()` will generate different (additional) output bytes.


Q: For hash functions with variable output size, why the output size is not a template parameter, e.g. `sha3<256>`?

A: While it may seem cool to make the output size a template parameter, in some usage scenarios the required digest size is not known at compile time. One simple example is Argon2 password hashing algorithm, which requires us to hash its state using BLAKE2b with dynamically calculated digest size. We can't just use the largest digest size and truncate the result, because most hash functions (unlike XOFs) produce completely different digests depending on the requested output size. Using a template parameter for the digest size would encumber implementation of such algorithms. Additionally, some hash functions support arbitrary output sizes which are not limited by the security level (examples of such functions are Skein, BLAKE2x, ParallelHash). Some functions are specifically designed to be usable both in hashing and in XOF modes, where the required output size is not known in advance even at runtime. Taking all this factors in consideration, specifying the output size at compile time does not seem like a good design.


Q: Why `hasher` does not support hashing non-byte types?

A: Cryptographic hash functions are always defined for a sequence of bytes. We support only those data types that can be unambiguosly converted to bytes (sequences of `char`, `signed char`, or `unsigned char`). Other data types should be converted to a sequence of bytes in non-ambiguous way before they can be hashed (eg wide strings could be encoded using UTF-8 or another encoding), which is beyond the scope of the library.


Q: Since the output size has to be provided to the constructor, why there are separate typedefs for `sha256` and `sha512` instead of one hasher with output size parameter: `sha2(256)` / `sha2(512)`?

A: SHA-2 family of hash functions is special because SHA-512 can produce output of any size up to 512 bits (SHA-512/t), e.g. `sha512(256)` will calculate SHA-512/256. The resulting hash is different from SHA-256, but has the same length. Thus SHA-512 is an independent hash function supporting variable output sizes. On the other hand, the 32-bit version of SHA-2 is only defined for 224-bit and 256-bit outputs, and they are widely known as SHA-224 and SHA-256. We decided to use different typedefs for SHA-224 and SHA-256 because requiring users to use `sha256(224)` for getting SHA-224 digests would be confusing. Internally all SHA-2 functions are implemented using one template class.


Q: Why there are separate typedefs for `skein256`, `skein512` and `skein1024` instead of one hasher with output size parameter: `skein(256)` / `skein(512)` / `skein(1024)`?

A: Skein256, Skein512 and Skein1024 are different algorithms. Each of them can produce digests of any size. The outputs are unrelated, e.g. `skein256(256)` != `skein512(256)` != `skein1024(256)`. Internally all Skein variants are implemented using one template class.


Q: Why there are so many typedefs for BLAKE2 hash function?

A: BLAKE2 has many variants that produce incompatible digests for the same output sizes. We support different variants via different typedef. For the 512-bit version, `blake2b` is the oldest algorithm which can produce digests of any size up to 512 bits. `blake2xb` can be used to produce larger digests but requires the output size to be known in advance; it can't be merged with `blake2b` because their output are different for the same digest sizes. `blake2xb_xof` can be used in XOF mode when the output size is not known in advance. Then there is a 256-bit version `blake2s` which supports all these variants as well. Internally all BLAKE2 variants are implemented using one template class.

## Known limitations

* Included providers are written in standard C++ and may be slower than SIMD optimized implementations.
* Only complete bytes are supported for input and output.
* Big endian systems are not supported.
* No attempts were made to make implementation of every algorithm constant time.

## Reference documentation

Reference documentation is here: https://kerukuro.github.io/digestpp/




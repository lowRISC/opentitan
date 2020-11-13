/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SHA2_HPP
#define DIGESTPP_ALGORITHM_SHA2_HPP

#include "../hasher.hpp"
#include "detail/sha2_provider.hpp"

namespace digestpp
{

/**
 * @brief SHA-512 hash function
 *
 * @hash
 *
 * @outputsize 8 - 512 bits
 *
 * @defaultsize 512 bits
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes),
 * or is not within the supported range
 *
 * @par Example:\n
 * @code // Output a SHA-512/256 digest of a string
 * digestpp::sha512 hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code dd9d67b371519c339ed8dbd25af90e976a1eeefd4ad3d889005e532fc5bef04d
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha2_provider<uint64_t>> sha512;

/**
 * @brief SHA-384 hash function
 *
 * @hash
 *
 * @outputsize 384 bits
 *
 * @defaultsize 384 bits
 *
 * @par Example:\n
 * @code // Output a SHA-384 digest of a string
 * digestpp::sha384 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code ca737f1014a48f4c0b6dd43cb177b0afd9e5169367544c494011e3317dbf9a509cb1e5dc1e85a941bbee3d7f2afbc9b1
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha2_provider<uint64_t, 384>> sha384;

/**
 * @brief SHA-256 hash function
 *
 * Note that this function is slower than SHA-512/256 on 64-bit systems.
 *
 * @hash
 *
 * @outputsize 256 bits
 *
 * @defaultsize 256 bits
 *
 * @par Example:\n
 * @code // Output a SHA-256 digest of a string
 * digestpp::sha256 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha2_provider<uint32_t, 256>> sha256;

/**
 * @brief SHA-224 hash function
 *
 * @hash
 *
 * @outputsize 224 bits
 *
 * @defaultsize 224 bits
 *
 * @par Example:\n
 * @code // Output a SHA-224 digest of a string
 * digestpp::sha224 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 730e109bd7a8a32b1cb9d9a09aa2325d2430587ddbc0c38bad911525
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha2_provider<uint32_t, 224>> sha224;


} // namespace digestpp

#endif
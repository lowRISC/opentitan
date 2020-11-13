/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SHA3_HPP
#define DIGESTPP_ALGORITHM_SHA3_HPP

#include "../hasher.hpp"
#include "detail/sha3_provider.hpp"

namespace digestpp
{

/**
 * @brief SHA-3 hash function
 *
 * @hash
 *
 * @outputsize 224 / 256 / 384 / 512 bits
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not supported
 *
 * @par Example:\n
 * @code // Output a 256-bit SHA-3 digest of a string
 * digestpp::sha3 hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 69070dda01975c8c120c3aada1b282394e7f032fa9cf32f4cb2259a0897dfc04
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sha3_provider> sha3;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_SHA3_HPP
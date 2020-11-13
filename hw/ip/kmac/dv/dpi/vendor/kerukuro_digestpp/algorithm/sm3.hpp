/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_SM3_HPP
#define DIGESTPP_ALGORITHM_SM3_HPP

#include "../hasher.hpp"
#include "detail/sm3_provider.hpp"

namespace digestpp
{

/**
 * @brief SM3 hash function
 *
 * @hash
 *
 * @outputsize 256 bits
 *
 * @defaultsize 256 bits
 *
 * @par Example:\n
 * @code // Output a SM3 digest of a string
 * digestpp::sm3 hasher;
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 5fdfe814b8573ca021983970fc79b2218c9570369b4859684e2e4c3fc76cb8ea
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::sm3_provider> sm3;

} // namespace digestpp

#endif
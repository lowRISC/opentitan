/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_KUPYNA_HPP
#define DIGESTPP_ALGORITHM_KUPYNA_HPP

#include "../hasher.hpp"
#include "detail/kupyna_provider.hpp"

namespace digestpp
{

/**
 * @brief Kupyna hash function
 *
 * @hash
 *
 * @outputsize 256 / 512 bits
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not supported
 *
 * @par Example:\n
 * @code // Output a 256-bit Kupyna digest of a string
 * digestpp::kupyna hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 996899f2d7422ceaf552475036b2dc120607eff538abf2b8dff471a98a4740c6
 * @endcode
 *
 * @sa hasher
 */

typedef hasher<detail::kupyna_provider> kupyna;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_KUPYNA_HPP
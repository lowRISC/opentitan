/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_JG_HPP
#define DIGESTPP_ALGORITHM_JG_HPP

#include "../hasher.hpp"
#include "detail/jh_provider.hpp"

namespace digestpp
{

/**
 * @brief JH hash function
 *
 * @hash
 *
 * @outputsize 8 - 512 bits
 *
 * @defaultsize none
 *
 * @throw std::runtime_error if the requested digest size is not divisible by 8 (full bytes),
 * or is not within the supported range
 *
 * @par Example:\n
 * @code // Output a 256-bit JH digest of a string
 * digestpp::jh hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 6a049fed5fc6874acfdc4a08b568a4f8cbac27de933496f031015b38961608a0
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::jh_provider> jh;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_JG_HPP
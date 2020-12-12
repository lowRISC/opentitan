/*
This code is written by kerukuro and released into public domain.
*/

#ifndef DIGESTPP_ALGORITHM_STREEBOG_HPP
#define DIGESTPP_ALGORITHM_STREEBOG_HPP

#include "../hasher.hpp"
#include "detail/streebog_provider.hpp"

namespace digestpp
{

/** @brief Streebog hash function
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
 * @code // Output a 256-bit Streebog digest of a string
 * digestpp::streebog hasher(256);
 * hasher.absorb("The quick brown fox jumps over the lazy dog");
 * std::cout << hasher.hexdigest() << '\n';
 * @endcode
 *
 * @par Example output:\n
 * @code 3e7dea7f2384b6c5a3d0e24aaa29c05e89ddd762145030ec22c71a6db8b2c1f4
 * @endcode
 *
 * @sa hasher
 */
typedef hasher<detail::streebog_provider> streebog;

} // namespace digestpp

#endif // DIGESTPP_ALGORITHM_STREEBOG_HPP